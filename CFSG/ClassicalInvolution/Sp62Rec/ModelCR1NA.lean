module

public import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1Basic
public import Certificates.Certificate550822

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open
  Matrix

section Checks

theorem centA0Check_holds : centA0Check () = true := Certificates.certificate550822.1

theorem normA0Check_holds : normA0Check () = true := Certificates.certificate550822.2.1

theorem wCheck_holds : wCheck () = true := Certificates.certificate550822.2.2.1

theorem stabWCheck_holds : stabWCheck () = true := Certificates.certificate550822.2.2.2.1

theorem centAlphaCheck_holds : centAlphaCheck () = true :=
  Certificates.certificate550822.2.2.2.2.1

theorem sylMeetCheck_holds : sylMeetCheck () = true :=
  Certificates.certificate550822.2.2.2.2.2.1

theorem orbCheck_holds : orbCheck () = true :=
  Certificates.certificate550822.2.2.2.2.2.2.1

theorem e8Check_holds : e8Check () = true :=
  Certificates.certificate550822.2.2.2.2.2.2.2.1

theorem sevenCheck_holds : sevenCheck () = true :=
  Certificates.certificate550822.2.2.2.2.2.2.2.2.1

theorem rhoMatCheck_holds : rhoMatCheck () = true :=
  Certificates.certificate550822.2.2.2.2.2.2.2.2.2.1

theorem rhoKerCheck_holds : rhoKerCheck () = true :=
  Certificates.certificate550822.2.2.2.2.2.2.2.2.2.2.1

theorem wCheck_spec :
    (∀ i < (enumA0 ()).elems.size, ∀ w ∈ wCodes, ((enumA0 ()).elems[i]!)[w]! = w) ∧
      ∀ v < 64, (∀ j < (gA0 ()).size, ((gA0 ())[j]!)[v]! = v) → v ∈ wCodes := by
  have h := wCheck_holds
  simp only [wCheck, Bool.and_eq_true, allLt_iff, List.all_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun v hv hfix => ?_⟩
  rcases h2 v hv with h | h
  · have ht : (allLt (gA0 ()).size fun j => decide (((gA0 ())[j]!)[v]! = v)) = true :=
      allLt_iff.mpr fun j hj => decide_eq_true (hfix j hj)
    rw [ht] at h
    cases h
  · exact h

end Checks

theorem code_lt_64 (g : StatedSp 3 (ZMod 2)) {n : ℕ} (hn : n < 64) : (code g)[n]! < 64 := by
  rw [code_get g hn]
  exact codeOf_lt _

theorem code_get_eq_iff (g : StatedSp 3 (ZMod 2)) {n : ℕ} (hn : n < 64) :
    (code g)[n]! = n ↔ spMat g *ᵥ vecOf n = vecOf n := by
  rw [mulVec_vecOf g hn]
  constructor
  · intro h
    rw [h]
  · intro h
    have := congrArg codeOf h
    rwa [codeOf_vecOf _ (code_lt_64 g hn), codeOf_vecOf _ hn] at this

theorem conj_mul_self {G : Type*} [Group G] {c x : G} (hx : x * x = 1) :
    c * x * c⁻¹ * (c * x * c⁻¹) = 1 := by
  rw [show c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ by group, hx, mul_one,
    mul_inv_cancel]

theorem toBlocks₁₁_mul' (M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (M * N).toBlocks₁₁ = M.toBlocks₁₁ * N.toBlocks₁₁ + M.toBlocks₁₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.mul_apply,
    Fintype.sum_sum_type]

theorem toBlocks₂₁_mul' (M N : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) :
    (M * N).toBlocks₂₁ = M.toBlocks₂₁ * N.toBlocks₁₁ + M.toBlocks₂₂ * N.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.toBlocks₂₁, Matrix.mul_apply,
    Fintype.sum_sum_type]

theorem toBlocks₁₁_eq_one_iff {B : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (hB : B.toBlocks₂₁ = 0) :
    B.toBlocks₁₁ = 1 ↔ ∀ j : Fin 3, B *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl j) 1 := by
  constructor
  · intro h j
    funext r
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
    rcases r with i | i
    · have := congrFun (congrFun h i) j
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply] at this
      rw [this, Matrix.one_apply, Pi.single_apply]
      simp only [Sum.inl.injEq]
    · have := congrFun (congrFun hB i) j
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
      rw [this, Pi.single_apply]
      simp
  · intro h
    ext i j
    have := congrFun (h j) (Sum.inl i)
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, this, Sum.inl.injEq, Matrix.one_apply]

theorem card_GL3 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

section Gen

theorem yamakiSp_inv (i : Fin 12) : (yamakiSp i)⁻¹ = yamakiSp i :=
  inv_eq_of_mul_eq_one_right (yamakiSp_mul_self i)

theorem spMat_yamakiSp_eq (i : Fin 12) : spMat (yamakiSp i) = yamakiMat i := rfl

theorem a0Gen_mem_A0 {j : ℕ} (hj : j < (gA0 ()).size) : a0Gen j ∈ A0 := by
  rw [A0_eq_closure]
  exact Subgroup.subset_closure ⟨j, hj, rfl⟩

theorem yword_alpha : yword [5] = alpha := by
  rw [yword_cons, yword_nil, mul_one]
  exact ysp_eq 5

theorem yword_rho28 : yword [3, 7] = rho28 := by
  rw [yword_cons, yword_cons, yword_nil, mul_one]
  exact congrArg₂ (· * ·) (ysp_eq 3) (ysp_eq 7)

theorem yword_flatten_replicate (w : List ℕ) (k : ℕ) :
    yword (List.replicate k w).flatten = yword w ^ k := by
  induction k with
  | zero => rw [List.replicate_zero, List.flatten_nil, yword_nil, pow_zero]
  | succ k ih => rw [List.replicate_succ, List.flatten_cons, yword_append, ih, pow_succ']

theorem commOK_gA0_of_commute {x : StatedSp 3 (ZMod 2)} (hx : ∀ a ∈ A0, x * a = a * x) :
    commOK (gA0 ()) (code x) = true := by
  simp only [commOK, allLt_iff, decide_eq_true_eq]
  intro j hj
  rw [gA0_get j hj, ← code_mul, ← code_mul, hx _ (a0Gen_mem_A0 hj)]

@[expose] def orbElems (x : List ℕ) (cs : List (List ℕ)) : List (StatedSp 3 (ZMod 2)) :=
  cs.map fun c => yword (conjWord c x)

theorem map_code_orbElems {x : List ℕ} {cs : List (List ℕ)} (hx : ∀ i ∈ x, i < 12)
    (hcs : ∀ c ∈ cs, ∀ i ∈ c, i < 12) : (orbElems x cs).map code = orbCodes x cs := by
  simp only [orbElems, orbCodes, List.map_map]
  exact List.map_congr_left fun c hc => code_yword (lt_of_mem_conjWord (hcs c hc) hx)

theorem orbN0_eq_of_closed {x : List ℕ} {cs : List (List ℕ)} (hx : ∀ i ∈ x, i < 12)
    (hcs : ∀ c ∈ cs, ∀ i ∈ c, i ∈ idxN0) (h0 : [] ∈ cs)
    (hcl : closedN0 (genA ()) (orbCodes x cs) = true) :
    orbN0 (yword x) = {y | y ∈ orbElems x cs} := by
  have hlt : ∀ c ∈ cs, ∀ i ∈ c, i < 12 := fun c hc i hi => (idxN0_spec (hcs c hc i hi)).1
  have hmap := map_code_orbElems hx hlt
  simp only [closedN0, List.all_eq_true, List.contains_iff_mem] at hcl
  have hgen : ∀ i : Fin 12, i.val ∈ idxN0 → ∀ y ∈ orbElems x cs,
      yamakiSp i * y * (yamakiSp i)⁻¹ ∈ orbElems x cs := by
    intro i hi y hy
    have hyc : code y ∈ orbCodes x cs := by
      rw [← hmap]
      exact List.mem_map_of_mem hy
    have h := hcl i.val hi (code y) hyc
    rw [← hmap] at h
    obtain ⟨z, hz, hze⟩ := List.mem_map.mp h
    have hzy : z = yamakiSp i * y * yamakiSp i :=
      code_injective (by rw [hze, code_mul, code_mul, code_yamakiSp])
    rw [yamakiSp_inv, ← hzy]
    exact hz
  have key : ∀ n ∈ N0, ∀ y ∈ orbElems x cs, n * y * n⁻¹ ∈ orbElems x cs := by
    intro n hn
    rw [N0] at hn
    induction hn using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := hg
      exact hgen i (mem_idxN0 hi)
    | inv_mem g hg =>
      obtain ⟨i, hi, rfl⟩ := hg
      rw [yamakiSp_inv]
      exact hgen i (mem_idxN0 hi)
    | one =>
      intro y hy
      rwa [one_mul, inv_one, mul_one]
    | mul a b _ _ ha hb =>
      intro y hy
      rw [show a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ by group]
      exact ha _ (hb y hy)
  ext y
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have hx0 : yword x ∈ orbElems x cs :=
      List.mem_map.mpr ⟨[], h0, by simp [conjWord]⟩
    exact key n hn _ hx0
  · intro hy
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
    exact ⟨yword c, yword_mem_N0 (hcs c hc), (yword_conjWord c x).symm⟩

theorem ncard_orbElems {x : List ℕ} {cs : List (List ℕ)} (hx : ∀ i ∈ x, i < 12)
    (hcs : ∀ c ∈ cs, ∀ i ∈ c, i < 12) (hnd : (orbCodes x cs).Nodup) :
    {y | y ∈ orbElems x cs}.ncard = cs.length := by
  classical
  have hnd' : (orbElems x cs).Nodup := by
    rw [← map_code_orbElems hx hcs] at hnd
    exact hnd.of_map _
  rw [show {y | y ∈ orbElems x cs} = ((orbElems x cs).toFinset : Set _) by ext; simp,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd', orbElems, List.length_map]

end Gen

section Normal

theorem conj_mem_A0 {i : Fin 12} (hi : i.val ∈ idxN0) {a : StatedSp 3 (ZMod 2)} (ha : a ∈ A0) :
    yamakiSp i * a * (yamakiSp i)⁻¹ ∈ A0 := by
  have h := normA0Check_holds
  simp only [normA0Check, List.all_eq_true, allLt_iff] at h
  rw [A0_eq_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    rw [mem_A0_iff_isSome, code_mul, code_mul, yamakiSp_inv, code_yamakiSp, ← gA0_get j hj]
    exact h i.val hi j hj
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact A0.one_mem
  | mul a b _ _ iha ihb =>
    rw [show yamakiSp i * (a * b) * (yamakiSp i)⁻¹ =
      yamakiSp i * a * (yamakiSp i)⁻¹ * (yamakiSp i * b * (yamakiSp i)⁻¹) by group]
    exact A0.mul_mem iha ihb
  | inv a _ ih =>
    rw [show yamakiSp i * a⁻¹ * (yamakiSp i)⁻¹ = (yamakiSp i * a * (yamakiSp i)⁻¹)⁻¹ by group]
    exact A0.inv_mem ih

theorem N0_le_normalizer : N0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) := by
  rw [N0, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i.val ∈ idxN0 := mem_idxN0 hi
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => conj_mem_A0 hi' hh, fun hh => ?_⟩
  have h2 := conj_mem_A0 hi' hh
  rwa [yamakiSp_inv, show yamakiSp i * (yamakiSp i * h * yamakiSp i) * yamakiSp i =
    yamakiSp i * yamakiSp i * h * (yamakiSp i * yamakiSp i) by group, yamakiSp_mul_self,
    one_mul, mul_one] at h2

theorem X0_le_normalizer : X0 ≤ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) :=
  X0_le_N0.trans N0_le_normalizer

theorem code_A0_fix {b : StatedSp 3 (ZMod 2)} (hb : b ∈ A0) {w : ℕ} (hw : w ∈ wCodes) :
    (code b)[w]! = w := by
  obtain ⟨k, hk, hke⟩ := exists_lt_of_mem_A0 hb
  rw [← hke]
  exact wCheck_spec.1 k hk w hw

theorem code_mem_wCodes_of_mem_normalizer {x : StatedSp 3 (ZMod 2)}
    (hxN : x ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2)))) {w : ℕ} (hw : w ∈ wCodes) :
    (code x)[w]! ∈ wCodes := by
  have hw64 : w < 64 := by
    revert w
    decide
  apply wCheck_spec.2 _ (code_lt_64 x hw64)
  intro j hj
  have hb : x⁻¹ * a0Gen j * x ∈ A0 := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) (a0Gen j)).mp
      (a0Gen_mem_A0 hj)
    rwa [inv_inv] at this
  have heq : a0Gen j * x = x * (x⁻¹ * a0Gen j * x) := by group
  rw [gA0_get j hj, ← compA_get _ _ hw64, ← code_mul, heq, code_mul, compA_get _ _ hw64,
    code_A0_fix hb hw]

end Normal

section Normalizer

theorem mem_A0_of_commute : ∀ x ∈ Hhat, (∀ a ∈ A0, x * a = a * x) → x ∈ A0 := by
  intro x hxH hx
  obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_Hhat_iff_isSome x).mp hxH)
  have h := centA0Check_holds
  simp only [centA0Check, allLt_iff, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h i hi with h1 | h1
  · rw [hie, commOK_gA0_of_commute hx] at h1
    cases h1
  · rw [hie] at h1
    exact (mem_A0_iff_isSome x).mpr h1

theorem mem_X0_of_mem_normalizer :
    ∀ x ∈ Hhat, x ∈ Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) → x ∈ X0 := by
  intro x hxH hxN
  obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_Hhat_iff_isSome x).mp hxH)
  have h := stabWCheck_holds
  simp only [stabWCheck, allLt_iff, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h i hi with h1 | h1
  · have ht : (wCodes.all fun w => wCodes.contains ((code x)[w]!)) = true :=
      List.all_eq_true.mpr fun w hw =>
        List.contains_iff_mem.mpr (code_mem_wCodes_of_mem_normalizer hxN hw)
    rw [hie, ht] at h1
    cases h1
  · rw [hie] at h1
    exact (mem_X0_iff_isSome x).mpr h1

theorem X0_eq_normalizer_inf_Hhat :
    X0 = Subgroup.normalizer (A0 : Set (StatedSp 3 (ZMod 2))) ⊓ Hhat :=
  le_antisymm (le_inf X0_le_normalizer X0_le_Hhat)
    fun x hx => mem_X0_of_mem_normalizer x hx.2 hx.1

end Normalizer

section CentAlpha

theorem mem_X0_of_commute_alpha : ∀ n ∈ N0, n * alpha = alpha * n → n ∈ X0 := by
  intro n hn hna
  obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_N0_iff_isSome n).mp hn)
  have h := centAlphaCheck_holds
  simp only [centAlphaCheck, allLt_iff, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  rcases h i hi with h1 | h1
  · exfalso
    apply h1
    rw [hie, ← code_alpha, ← code_mul, ← code_mul, hna]
  · rw [hie] at h1
    exact (mem_X0_iff_isSome n).mpr h1

theorem X0_eq_centralizer_inf_N0 :
    X0 = Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2))) ⊓ N0 :=
  le_antisymm (le_inf (X0_le_Hhat.trans Hhat_le_centralizer_alpha) X0_le_N0)
    fun x hx => mem_X0_of_commute_alpha x hx.2 (Subgroup.mem_centralizer_singleton_iff.mp hx.1)

end CentAlpha

section Sylow

theorem le_S0_of_normal {P : Subgroup (StatedSp 3 (ZMod 2))} (hPN : P ≤ N0)
    (hnorm : ∀ n ∈ N0, ∀ x ∈ P, n * x * n⁻¹ ∈ P) (hP : IsPGroup 2 P) : P ≤ S0 := by
  have hS : Nat.card (S0.subgroupOf N0) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S0_le_N0).toEquiv, card_S0]
  have hSp : IsPGroup 2 (S0.subgroupOf N0) := IsPGroup.of_card (n := 9) (by rw [hS]; norm_num)
  have hSi : (S0.subgroupOf N0).index = 21 := by
    have := Subgroup.card_mul_index (S0.subgroupOf N0)
    rw [hS, card_N0] at this
    omega
  have hSi' : ¬ 2 ∣ (S0.subgroupOf N0).index := by
    rw [hSi]
    decide
  haveI : (P.subgroupOf N0).Normal :=
    ⟨fun k hk g => by
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hnorm g g.2 k hk⟩
  have hPp : IsPGroup 2 (P.subgroupOf N0) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
  have hle := hPp.le_sylow_of_normal (hSp.toSylow hSi')
  intro x hx
  have hx' : (⟨x, hPN hx⟩ : ↥N0) ∈ P.subgroupOf N0 := hx
  exact (IsPGroup.mem_toSylow hSp hSi').mp (hle hx')

theorem le_A0_of_normal : ∀ P : Subgroup (StatedSp 3 (ZMod 2)), P ≤ N0 →
    (∀ n ∈ N0, ∀ x ∈ P, n * x * n⁻¹ ∈ P) → IsPGroup 2 P → P ≤ A0 := by
  intro P hPN hnorm hP
  have hS0 := le_S0_of_normal hPN hnorm hP
  have h := sylMeetCheck_holds
  simp only [sylMeetCheck, Bool.and_eq_true, allLt_iff, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨hw, h⟩ := h
  have hws : ∀ i ∈ sylMeetWord, i ∈ idxN0 := mem_of_wordsIn hw _ (by simp)
  have hlt : ∀ i ∈ sylMeetWord, i < 12 := fun i hi => (idxN0_spec (hws i hi)).1
  have hlt' : ∀ i ∈ sylMeetWord.reverse, i < 12 := fun i hi => hlt i (List.mem_reverse.mp hi)
  have hg : yword sylMeetWord ∈ N0 := yword_mem_N0 hws
  intro x hx
  have hgx : (yword sylMeetWord)⁻¹ * x * yword sylMeetWord ∈ S0 := by
    have := hnorm _ (N0.inv_mem hg) x hx
    rw [inv_inv] at this
    exact hS0 this
  obtain ⟨i, hi, hie⟩ := exists_lt_of_mem_S0 (hS0 hx)
  rcases h i hi with h1 | h1
  · have ht := (mem_S0_iff_isSome _).mp hgx
    rw [code_mul, code_mul, inv_yword, code_yword hlt', code_yword hlt, ← hie] at ht
    rw [ht] at h1
    cases h1
  · rw [hie] at h1
    exact (mem_A0_iff_isSome x).mpr h1

theorem le_A0_subgroupOf {K : Subgroup ↥N0} (hKn : K.Normal) (hKp : IsPGroup 2 K) :
    K ≤ A0.subgroupOf N0 := by
  have hPN : K.map N0.subtype ≤ N0 := Subgroup.map_subtype_le K
  have hPn : ∀ n ∈ N0, ∀ x ∈ K.map N0.subtype, n * x * n⁻¹ ∈ K.map N0.subtype := by
    intro n hn x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hc : (⟨n, hn⟩ : ↥N0) * k * (⟨n, hn⟩ : ↥N0)⁻¹ ∈ K := hKn.conj_mem k hk ⟨n, hn⟩
    have he : N0.subtype ((⟨n, hn⟩ : ↥N0) * k * (⟨n, hn⟩ : ↥N0)⁻¹) =
        n * N0.subtype k * n⁻¹ := by
      simp
    rw [← he]
    exact Subgroup.mem_map_of_mem _ hc
  have hle := le_A0_of_normal (K.map N0.subtype) hPN hPn (hKp.map N0.subtype)
  intro k hk
  exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem _ hk))

end Sylow

section NOrbits

theorem orbCheck_spec :
    (∀ c ∈ orbAlphaWords ++ orbPi12Words ++ orbPi3Words ++ orbRhoWords, ∀ i ∈ c, i ∈ idxN0) ∧
      (orbCodes [5] orbAlphaWords ++ orbCodes [4] orbPi12Words ++ orbCodes [5, 4] orbPi3Words ++
        orbCodes [3, 7] orbRhoWords).Nodup ∧
      closedN0 (genA ()) (orbCodes [5] orbAlphaWords) = true ∧
      closedN0 (genA ()) (orbCodes [4] orbPi12Words) = true ∧
      closedN0 (genA ()) (orbCodes [5, 4] orbPi3Words) = true ∧
      closedN0 (genA ()) (orbCodes [3, 7] orbRhoWords) = true ∧
      ∀ i < (enumA0 ()).elems.size, (enumA0 ()).elems[i]! = idA () ∨
        (enumA0 ()).elems[i]! ∈ orbCodes [5] orbAlphaWords ++ orbCodes [4] orbPi12Words ++
          orbCodes [5, 4] orbPi3Words ++ orbCodes [3, 7] orbRhoWords := by
  have h := orbCheck_holds
  simp only [orbCheck, Bool.and_eq_true, decide_eq_true_eq, allLt_iff, Bool.or_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨hw, hnd⟩, ha⟩, hb⟩, hc⟩, hd⟩, hcov⟩ := h
  exact ⟨mem_of_wordsIn hw, hnd, ha, hb, hc, hd, hcov⟩

theorem orbWords_spec {cs : List (List ℕ)}
    (hcs : cs = orbAlphaWords ∨ cs = orbPi12Words ∨ cs = orbPi3Words ∨ cs = orbRhoWords) :
    ∀ c ∈ cs, ∀ i ∈ c, i ∈ idxN0 := by
  intro c hc
  apply orbCheck_spec.1 c
  rcases hcs with rfl | rfl | rfl | rfl <;> simp [hc]

theorem orbWords_lt {cs : List (List ℕ)}
    (hcs : cs = orbAlphaWords ∨ cs = orbPi12Words ∨ cs = orbPi3Words ∨ cs = orbRhoWords) :
    ∀ c ∈ cs, ∀ i ∈ c, i < 12 :=
  fun c hc i hi => (idxN0_spec (orbWords_spec hcs c hc i hi)).1

theorem orbN0_alpha : orbN0 alpha = {y | y ∈ orbElems [5] orbAlphaWords} := by
  rw [← yword_alpha]
  exact orbN0_eq_of_closed (by decide) (orbWords_spec (Or.inl rfl)) (by decide)
    orbCheck_spec.2.2.1

theorem orbN0_pi12 : orbN0 pi12 = {y | y ∈ orbElems [4] orbPi12Words} := by
  rw [← yword_pi12]
  exact orbN0_eq_of_closed (by decide) (orbWords_spec (Or.inr (Or.inl rfl))) (by decide)
    orbCheck_spec.2.2.2.1

theorem orbN0_pi3 : orbN0 pi3 = {y | y ∈ orbElems [5, 4] orbPi3Words} := by
  rw [← yword_pi3]
  exact orbN0_eq_of_closed (by decide) (orbWords_spec (Or.inr (Or.inr (Or.inl rfl))))
    (by decide) orbCheck_spec.2.2.2.2.1

theorem orbN0_rho28 : orbN0 rho28 = {y | y ∈ orbElems [3, 7] orbRhoWords} := by
  rw [← yword_rho28]
  exact orbN0_eq_of_closed (by decide) (orbWords_spec (Or.inr (Or.inr (Or.inr rfl))))
    (by decide) orbCheck_spec.2.2.2.2.2.1

theorem orbCodes_nodup :
    (orbCodes [5] orbAlphaWords).Nodup ∧ (orbCodes [4] orbPi12Words).Nodup ∧
      (orbCodes [5, 4] orbPi3Words).Nodup ∧ (orbCodes [3, 7] orbRhoWords).Nodup := by
  obtain ⟨-, hnd, -⟩ := orbCheck_spec
  exact ⟨hnd.sublist ((List.sublist_append_left _ _).trans
      ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _))),
    hnd.sublist ((List.sublist_append_right _ _).trans
      ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _))),
    hnd.sublist ((List.sublist_append_right _ _).trans (List.sublist_append_left _ _)),
    hnd.sublist (List.sublist_append_right _ _)⟩

theorem ncard_orbN0 : (orbN0 alpha).ncard = 7 ∧ (orbN0 pi12).ncard = 7 ∧
    (orbN0 pi3).ncard = 21 ∧ (orbN0 rho28).ncard = 28 := by
  obtain ⟨h1, h2, h3, h4⟩ := orbCodes_nodup
  rw [orbN0_alpha, orbN0_pi12, orbN0_pi3, orbN0_rho28,
    ncard_orbElems (by decide) (orbWords_lt (Or.inl rfl)) h1,
    ncard_orbElems (by decide) (orbWords_lt (Or.inr (Or.inl rfl))) h2,
    ncard_orbElems (by decide) (orbWords_lt (Or.inr (Or.inr (Or.inl rfl)))) h3,
    ncard_orbElems (by decide) (orbWords_lt (Or.inr (Or.inr (Or.inr rfl)))) h4]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem card_closure_orbN0_pi12 : Nat.card (Subgroup.closure (orbN0 pi12)) = 8 := by
  have h := e8Check_holds
  simp only [e8Check, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, List.contains_iff_mem] at h
  obtain ⟨h1, hprod⟩ := h
  have hlt := orbWords_lt (Or.inr (Or.inl rfl))
  have hmap := map_code_orbElems (x := [4]) (by decide) hlt
  obtain ⟨S, hS⟩ : ∃ S : Set (StatedSp 3 (ZMod 2)),
      S = {y | y ∈ orbElems [4] orbPi12Words} := ⟨_, rfl⟩
  have hmemS : ∀ y, y ∈ S ↔ y ∈ orbElems [4] orbPi12Words := fun y => by rw [hS]; rfl
  rw [orbN0_pi12, ← hS]
  have hsq : ∀ y ∈ S, y * y = 1 := by
    intro y hy
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ((hmemS y).mp hy)
    rw [yword_conjWord, yword_pi12]
    exact conj_mul_self (yamakiSp_mul_self 4)
  have hcode : ∀ y ∈ S, code y ∈ orbCodes [4] orbPi12Words := by
    intro y hy
    rw [← hmap]
    exact List.mem_map_of_mem ((hmemS y).mp hy)
  have hmul : ∀ y ∈ S, ∀ z ∈ S, y * z = 1 ∨ y * z ∈ S := by
    intro y hy z hz
    rcases hprod _ (hcode y hy) _ (hcode z hz) with h | h
    · left
      apply code_injective
      rw [code_mul, h, code_one]
    · right
      rw [← code_mul, ← hmap] at h
      obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
      rw [hmemS, ← code_injective hwe]
      exact hw
  have h1S : (1 : StatedSp 3 (ZMod 2)) ∉ S := by
    intro h1m
    have hc := hcode 1 h1m
    rw [code_one] at hc
    rw [List.contains_iff_mem.mpr hc] at h1
    cases h1
  have hcl : (Subgroup.closure S : Set (StatedSp 3 (ZMod 2))) = insert 1 S := by
    apply Set.Subset.antisymm
    · intro g hg
      induction hg using Subgroup.closure_induction with
      | mem y hy => exact Or.inr hy
      | one => exact Or.inl rfl
      | mul a b _ _ ha hb =>
        rcases ha with rfl | ha
        · rwa [one_mul]
        rcases hb with rfl | hb
        · rw [mul_one]
          exact Or.inr ha
        rcases hmul a ha b hb with h | h
        · exact Or.inl h
        · exact Or.inr h
      | inv a _ ha =>
        rcases ha with rfl | ha
        · rw [inv_one]
          exact Or.inl rfl
        · rw [inv_eq_of_mul_eq_one_right (hsq a ha)]
          exact Or.inr ha
    · intro g hg
      rcases hg with rfl | hg
      · exact (Subgroup.closure S).one_mem
      · exact Subgroup.subset_closure hg
  have hncard : S.ncard = 7 := by
    rw [hS, ncard_orbElems (by decide) hlt orbCodes_nodup.2.1]
    rfl
  change Nat.card ↥(Subgroup.closure S : Set (StatedSp 3 (ZMod 2))) = 8
  rw [hcl, Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h1S (Set.toFinite _), hncard]

end NOrbits

section NOrbitsA0

theorem mem_orbN0_of_mem_A0 : ∀ a ∈ A0, a ≠ 1 →
    a ∈ orbN0 alpha ∨ a ∈ orbN0 pi12 ∨ a ∈ orbN0 pi3 ∨ a ∈ orbN0 rho28 := by
  intro a ha ha1
  obtain ⟨k, hk, hke⟩ := exists_lt_of_mem_A0 ha
  rcases orbCheck_spec.2.2.2.2.2.2 k hk with h | h
  · exact absurd (code_injective (by rw [code_one, ← hke, h])) ha1
  · rw [hke] at h
    have hmem : ∀ {x : List ℕ} {cs : List (List ℕ)}, (∀ i ∈ x, i < 12) →
        (∀ c ∈ cs, ∀ i ∈ c, i < 12) → code a ∈ orbCodes x cs → a ∈ orbElems x cs := by
      intro x cs hx hcs hc
      rw [← map_code_orbElems hx hcs] at hc
      obtain ⟨z, hz, hze⟩ := List.mem_map.mp hc
      rwa [← code_injective hze]
    rw [orbN0_alpha, orbN0_pi12, orbN0_pi3, orbN0_rho28]
    simp only [List.mem_append] at h
    simp only [Set.mem_setOf_eq]
    rcases h with ((h | h) | h) | h
    · exact Or.inl (hmem (by decide) (orbWords_lt (Or.inl rfl)) h)
    · exact Or.inr (Or.inl (hmem (by decide) (orbWords_lt (Or.inr (Or.inl rfl))) h))
    · exact Or.inr (Or.inr (Or.inl
        (hmem (by decide) (orbWords_lt (Or.inr (Or.inr (Or.inl rfl)))) h)))
    · exact Or.inr (Or.inr (Or.inr
        (hmem (by decide) (orbWords_lt (Or.inr (Or.inr (Or.inr rfl)))) h)))

theorem exists_fpf_seven : ∃ x ∈ N0, x ^ 7 = 1 ∧ x ≠ 1 ∧ ∀ a ∈ A0, a * x = x * a → a = 1 := by
  have h := sevenCheck_holds
  simp only [sevenCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    decide_eq_false_iff_not, allLt_iff, Bool.or_eq_true] at h
  obtain ⟨⟨⟨hw, h7⟩, h1⟩, hfix⟩ := h
  have hws : ∀ i ∈ sevenWord, i ∈ idxN0 := mem_of_wordsIn hw _ (by simp)
  have hlt : ∀ i ∈ sevenWord, i < 12 := fun i hi => (idxN0_spec (hws i hi)).1
  refine ⟨yword sevenWord, yword_mem_N0 hws, ?_, ?_, ?_⟩
  · apply code_injective
    rw [← yword_flatten_replicate, code_yword (by decide), code_one]
    exact h7
  · intro h
    apply h1
    rw [← code_yword hlt, h, code_one]
  · intro a ha hax
    obtain ⟨k, hk, hke⟩ := exists_lt_of_mem_A0 ha
    rcases hfix k hk with hf | hf
    · exfalso
      apply hf
      rw [hke, ← code_yword hlt, ← code_mul, ← code_mul, hax]
    · apply code_injective
      rw [← hke, hf, code_one]

end NOrbitsA0

section Rho

theorem rhoMatCheck_spec :
    rhoP * rhoPinv = 1 ∧ rhoPinv * rhoP = 1 ∧
      (∀ j : Fin 3, rhoP *ᵥ Pi.single (Sum.inl j) 1 = vecOf (![9, 20, 38] j)) ∧
      ∀ i : Fin 12, i.val ∈ idxN0 → (rhoPinv * yamakiMat i * rhoP).toBlocks₂₁ = 0 := by
  have h := rhoMatCheck_holds
  simp only [rhoMatCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun i hi => ?_⟩
  have h5 := h4 i (List.mem_finRange i)
  rw [show idxN0.contains i.val = true from List.contains_iff_mem.mpr hi] at h5
  simpa only [Bool.not_true, Bool.false_or, decide_eq_true_eq] using h5

@[expose] def rhoConj (g : StatedSp 3 (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  rhoPinv * spMat g * rhoP

theorem rhoConj_one : rhoConj 1 = 1 := by
  rw [rhoConj, map_one, Matrix.mul_one, rhoMatCheck_spec.2.1]

theorem rhoConj_mul (g h : StatedSp 3 (ZMod 2)) : rhoConj (g * h) = rhoConj g * rhoConj h := by
  simp only [rhoConj, map_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc rhoP rhoPinv, rhoMatCheck_spec.1, Matrix.one_mul]

theorem rhoConj_toBlocks₂₁ {n : StatedSp 3 (ZMod 2)} (hn : n ∈ N0) :
    (rhoConj n).toBlocks₂₁ = 0 := by
  rw [N0] at hn
  induction hn using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    rw [rhoConj, spMat_yamakiSp_eq]
    exact rhoMatCheck_spec.2.2.2 i (mem_idxN0 hi)
  | inv_mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    rw [yamakiSp_inv, rhoConj, spMat_yamakiSp_eq]
    exact rhoMatCheck_spec.2.2.2 i (mem_idxN0 hi)
  | one =>
    rw [rhoConj_one]
    ext i j
    simp [Matrix.toBlocks₂₁, Matrix.one_apply]
  | mul a b _ _ ha hb =>
    rw [rhoConj_mul, toBlocks₂₁_mul', ha, hb, Matrix.zero_mul, Matrix.mul_zero, add_zero]

@[expose] def rhoMatN0 : ↥N0 →* Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun n := (rhoConj n).toBlocks₁₁
  map_one' := by
    show (rhoConj ((1 : ↥N0) : StatedSp 3 (ZMod 2))).toBlocks₁₁ = 1
    rw [OneMemClass.coe_one, rhoConj_one]
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  map_mul' n m := by
    show (rhoConj ((n * m : ↥N0) : StatedSp 3 (ZMod 2))).toBlocks₁₁ =
      (rhoConj n).toBlocks₁₁ * (rhoConj m).toBlocks₁₁
    rw [Subgroup.coe_mul, rhoConj_mul, toBlocks₁₁_mul', rhoConj_toBlocks₂₁ m.2, Matrix.mul_zero,
      add_zero]

@[expose] def rhoN0 : ↥N0 →* GL (Fin 3) (ZMod 2) := rhoMatN0.toHomUnits

theorem rhoConj_fix_iff (n : StatedSp 3 (ZMod 2)) (j : Fin 3) :
    rhoConj n *ᵥ Pi.single (Sum.inl j) 1 = Pi.single (Sum.inl j) 1 ↔
      spMat n *ᵥ vecOf (![9, 20, 38] j) = vecOf (![9, 20, 38] j) := by
  obtain ⟨h1, h2, h3, -⟩ := rhoMatCheck_spec
  rw [← h3 j, rhoConj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have := congrArg (rhoP *ᵥ ·) h
    simp only [Matrix.mulVec_mulVec _ rhoP rhoPinv, h1, Matrix.one_mulVec] at this
    exact this
  · intro h
    rw [h, Matrix.mulVec_mulVec _ rhoPinv rhoP, h2, Matrix.one_mulVec]

theorem rhoN0_eq_one_iff (n : ↥N0) :
    rhoN0 n = 1 ↔
      ∀ j : Fin 3, (code (n : StatedSp 3 (ZMod 2)))[![9, 20, 38] j]! = ![9, 20, 38] j := by
  have hval : ((rhoN0 n : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (rhoConj n).toBlocks₁₁ := rfl
  rw [Units.ext_iff, hval, Units.val_one, toBlocks₁₁_eq_one_iff (rhoConj_toBlocks₂₁ n.2)]
  refine forall_congr' fun j => ?_
  rw [rhoConj_fix_iff, code_get_eq_iff _ (by fin_cases j <;> decide)]

theorem rhoN0_ker : rhoN0.ker = A0.subgroupOf N0 := by
  ext n
  rw [MonoidHom.mem_ker, rhoN0_eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨i, hi, hie⟩ := exists_lt_of_lookup ((mem_N0_iff_isSome _).mp n.2)
    have hk := rhoKerCheck_holds
    simp only [rhoKerCheck, allLt_iff, Bool.or_eq_true, Bool.not_eq_true'] at hk
    rcases hk i hi with h1 | h1
    · have ht : ([9, 20, 38] : List ℕ).all
          (fun w => decide ((code (n : StatedSp 3 (ZMod 2)))[w]! = w)) = true := by
        simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
          decide_eq_true_eq]
        exact ⟨h 0, h 1, h 2⟩
      rw [hie, ht] at h1
      cases h1
    · rw [hie] at h1
      exact (mem_A0_iff_isSome _).mpr h1
  · intro h j
    exact code_A0_fix h (by fin_cases j <;> decide)

theorem rhoN0_surjective : Function.Surjective rhoN0 := by
  rw [← MonoidHom.range_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [← Subgroup.index_ker, rhoN0_ker, card_GL3]
  have h1 : Nat.card (A0.subgroupOf N0) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe A0_le_N0).toEquiv, card_A0]
  have h2 := Subgroup.card_mul_index (A0.subgroupOf N0)
  rw [h1, card_N0] at h2
  omega

theorem exists_rho_N0 : ∃ ρ : ↥N0 →* GL (Fin 3) (ZMod 2),
    Function.Surjective ρ ∧ ρ.ker = A0.subgroupOf N0 :=
  ⟨rhoN0, rhoN0_surjective, rhoN0_ker⟩

end Rho

end CFSG.ClassicalInvolution.Sp62Rec

module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCAdaptModel
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCAdapted
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCGeneration

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.WeakCT (torusHom coe_torusHom)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n : ℕ} {a b : Fin n}

section Embedding

variable (K) in
@[expose] noncomputable def pairEmbed (hab : a ≠ b) : StatedSp 2 K →* StatedSp n K :=
  spEmbed (pairMap a b) (pairMap_injective hab)

theorem pairEmbed_injective (hab : a ≠ b) : Function.Injective (pairEmbed K hab) :=
  spEmbed_injective (pairMap_injective hab)

theorem range_pairEmbed (hab : a ≠ b) :
    (pairEmbed K hab).range = suppGroup (coords a ∪ coords b) := by
  rw [pairEmbed, range_spEmbed, range_pairMap]

theorem exists_ne_ne (hn : 3 ≤ n) (a b : Fin n) : ∃ c : Fin n, c ≠ a ∧ c ≠ b := by
  have : ∃ c : ℕ, c < 3 ∧ c ≠ a.val ∧ c ≠ b.val := by
    by_cases h0 : 0 ≠ a.val ∧ 0 ≠ b.val
    · exact ⟨0, by omega, h0.1, h0.2⟩
    · by_cases h1 : 1 ≠ a.val ∧ 1 ≠ b.val
      · exact ⟨1, by omega, h1.1, h1.2⟩
      · exact ⟨2, by omega, by omega, by omega⟩
  obtain ⟨c, hc, hca, hcb⟩ := this
  exact ⟨⟨c, by omega⟩, fun h => hca (by simpa using congrArg Fin.val h),
    fun h => hcb (by simpa using congrArg Fin.val h)⟩

theorem injective_comp_pairEmbed (hn : 3 ≤ n) (hab : a ≠ b) {Q : Type*} [Group Q]
    (ψ : StatedSp n K →* Q) (hψ : ψ.ker ≤ Subgroup.center (StatedSp n K)) :
    Function.Injective (ψ.comp (pairEmbed K hab)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne hn a b
  have hcen : pairEmbed K hab x ∈ Subgroup.center (StatedSp n K) := hψ hx
  have hsupp : pairEmbed K hab x ∈ suppGroup (coords a ∪ coords b) := by
    rw [← range_pairEmbed hab]
    exact ⟨x, rfl⟩
  have h1 : pairEmbed K hab x = 1 :=
    eq_one_of_mem_center_of_mem_suppGroup hcen hsupp (t := Sum.inl c) (by
      rintro (h | h)
      · rcases mem_coords.1 h with h | h
        · exact hca (Sum.inl_injective h)
        · exact Sum.inl_ne_inr h
      · rcases mem_coords.1 h with h | h
        · exact hcb (Sum.inl_injective h)
        · exact Sum.inl_ne_inr h)
  exact pairEmbed_injective hab (by rw [h1, map_one])

end Embedding

section PairPlanes

theorem mem_sup_stdPlane_iff (hab : a ≠ b) {v : Fin n ⊕ Fin n → K} :
    v ∈ stdPlane K n a ⊔ stdPlane K n b ↔ ∀ t ∉ coords a ∪ coords b, v t = 0 := by
  have hdisj : ∀ t, t ∈ coords a → t ∈ coords b → False := by
    intro t ha hb
    rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 hb with h | h
    · exact hab (Sum.inl_injective h)
    · exact Sum.inl_ne_inr h
    · exact Sum.inr_ne_inl h
    · exact hab (Sum.inr_injective h)
  constructor
  · intro hv t ht
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hv
    rw [Pi.add_apply, (mem_stdPlane_iff a).1 hx t (fun h => ht (Or.inl h)),
      (mem_stdPlane_iff b).1 hy t (fun h => ht (Or.inr h)), add_zero]
  · intro hv
    refine Submodule.mem_sup.2 ⟨fun t => if t ∈ coords a then v t else 0, ?_,
      fun t => if t ∈ coords b then v t else 0, ?_, ?_⟩
    · rw [mem_stdPlane_iff]
      intro t ht
      simp [ht]
    · rw [mem_stdPlane_iff]
      intro t ht
      simp [ht]
    · funext t
      by_cases ha : t ∈ coords a
      · have hb : t ∉ coords b := fun hb => hdisj t ha hb
        simp [ha, hb]
      · by_cases hb : t ∈ coords b
        · simp [ha, hb]
        · simp [ha, hb, hv t (by simp [ha, hb])]

theorem parClosed_union_coords (a b : Fin n) : ParClosed (coords a ∪ coords b) := by
  intro t ht
  rcases ht with ht | ht
  · exact Or.inl (parClosed_coords a t ht)
  · exact Or.inr (parClosed_coords b t ht)

theorem mulVec_mem_sup_stdPlane (hab : a ≠ b) {c : StatedSp n K}
    (hc : c ∈ suppGroup (coords a ∪ coords b)) {u : Fin n ⊕ Fin n → K}
    (hu : u ∈ stdPlane K n a ⊔ stdPlane K n b) :
    mat n K c *ᵥ u ∈ stdPlane K n a ⊔ stdPlane K n b := by
  rw [mem_sup_stdPlane_iff hab] at hu ⊢
  intro t ht
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : s ∈ coords a ∪ coords b
  · have h1 : mat n K c t s = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) t s :=
      hc t s (fun h => ht h.1)
    have hts : t ≠ s := fun h => ht (h ▸ hs)
    rw [h1, Matrix.one_apply_ne hts, zero_mul]
  · rw [hu s hs, mul_zero]

variable (K n) in
@[expose] def pairPlanes (a b : Fin n) : Set (Submodule K (Fin n ⊕ Fin n → K)) :=
  {P | IsHyperbolicPlane P ∧ P ≤ stdPlane K n a ⊔ stdPlane K n b}

variable (K n) in
@[expose] noncomputable def pairPlaneSubgroup (a b : Fin n) : Subgroup (StatedSp n K) :=
  ⨆ P : pairPlanes K n a b, planeGroup (P : Submodule K (Fin n ⊕ Fin n → K))

theorem planeGroup_le_suppGroup_pair (hab : a ≠ b) {P : Submodule K (Fin n ⊕ Fin n → K)}
    (hP : P ≤ stdPlane K n a ⊔ stdPlane K n b) :
    planeGroup P ≤ suppGroup (coords a ∪ coords b) := by
  rw [← fixing_supported_eq (parClosed_union_coords a b)]
  refine fixing_anti (fun v hv u hu => ?_)
  exact form_eq_zero_of_supp (parClosed_union_coords a b) hv
    (fun t ht => (mem_sup_stdPlane_iff hab).1 (hP hu) t ht)

theorem pairPlaneSubgroup_le (hab : a ≠ b) :
    pairPlaneSubgroup K n a b ≤ suppGroup (coords a ∪ coords b) :=
  iSup_le fun P => planeGroup_le_suppGroup_pair hab P.2.2

theorem map_mem_pairPlanes (hab : a ≠ b) {P : Submodule K (Fin n ⊕ Fin n → K)}
    (hP : P ∈ pairPlanes K n a b) {c : StatedSp n K} (hc : c ∈ suppGroup (coords a ∪ coords b)) :
    P.map (Matrix.mulVecLin (mat n K c)) ∈ pairPlanes K n a b := by
  obtain ⟨⟨u, w, huw, rfl⟩, hle⟩ := hP
  refine ⟨⟨mat n K c *ᵥ u, mat n K c *ᵥ w, ?_, ?_⟩, ?_⟩
  · rw [form_mulVec]
    exact huw
  · rw [Submodule.map_span]
    simp [Set.image_insert_eq]
  · rintro _ ⟨x, hx, rfl⟩
    exact mulVec_mem_sup_stdPlane hab hc (hle hx)

theorem conj_pairPlaneSubgroup_le (hab : a ≠ b) {c : StatedSp n K}
    (hc : c ∈ suppGroup (coords a ∪ coords b)) :
    (pairPlaneSubgroup K n a b).map (MulAut.conj c).toMonoidHom ≤ pairPlaneSubgroup K n a b := by
  rw [pairPlaneSubgroup, Subgroup.map_iSup]
  refine iSup_le fun P => ?_
  rw [← planeGroup_map_conj]
  exact le_iSup (fun Q : pairPlanes K n a b => planeGroup (Q : Submodule K (Fin n ⊕ Fin n → K)))
    ⟨_, map_mem_pairPlanes hab P.2 hc⟩

theorem longBlock_mem_pairPlaneSubgroup_left (A : SL(2, K)) :
    longBlock K n a A ∈ pairPlaneSubgroup K n a b := by
  have : planeGroup (stdPlane K n a) ≤ pairPlaneSubgroup K n a b :=
    le_iSup (fun Q : pairPlanes K n a b => planeGroup (Q : Submodule K (Fin n ⊕ Fin n → K)))
      ⟨_, isHyperbolicPlane_stdPlane a, le_sup_left⟩
  rw [planeGroup_stdPlane] at this
  exact this ⟨A, rfl⟩

theorem pairPlaneSubgroup_eq [Finite K] (h4 : 4 ≤ Nat.card K) (hab : a ≠ b) :
    pairPlaneSubgroup K n a b = suppGroup (coords a ∪ coords b) := by
  refine le_antisymm (pairPlaneSubgroup_le hab) ?_
  have hmem : ∀ g : StatedSp 2 K, pairEmbed K hab g ∈ suppGroup (coords a ∪ coords b) := fun g => by
    rw [← range_pairEmbed hab]
    exact ⟨g, rfl⟩
  have hnorm : ((pairPlaneSubgroup K n a b).comap (pairEmbed K hab)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_pairPlaneSubgroup_le hab (hmem g) ⟨_, hx, rfl⟩
  have hL : ∀ A : SL(2, K), pairEmbed K hab (longBlock K 2 0 A) ∈ pairPlaneSubgroup K n a b :=
    fun A => by
      rw [pairEmbed, spEmbed_longBlock]
      exact longBlock_mem_pairPlaneSubgroup_left A
  have hnc : ¬ (pairPlaneSubgroup K n a b).comap (pairEmbed K hab) ≤
      Subgroup.center (StatedSp 2 K) := by
    intro hle
    have hx : longBlock K 2 0 (mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two])) ∈
        (pairPlaneSubgroup K n a b).comap (pairEmbed K hab) := hL _
    exact noncomm_longBlock_transv (K := K) (n := 2) 0
      (Subgroup.mem_center_iff.1 (hle hx)
        (longBlock K 2 0 (mkSL !![1, 0; 1, 1] (by simp [Matrix.det_fin_two])))).symm
  have htop := eq_top_of_normal_of_not_le_center (by norm_num) h4 hnorm hnc
  intro g hg
  rw [← range_pairEmbed hab] at hg
  obtain ⟨y, rfl⟩ := hg
  have : y ∈ (pairPlaneSubgroup K n a b).comap (pairEmbed K hab) := by
    rw [htop]
    trivial
  exact this

end PairPlanes

section NonCommuting

theorem planeGroup_not_le_center (hn : 2 ≤ n) {P : Submodule K (Fin n ⊕ Fin n → K)}
    (hP : IsHyperbolicPlane P) : ¬ planeGroup P ≤ Subgroup.center (StatedSp n K) := by
  intro hle
  obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP (⟨0, by omega⟩ : Fin n)
  set A : SL(2, K) := mkSL !![1, 1; 0, 1] (by simp [Matrix.det_fin_two]) with hA
  have hmem : g * longBlock K n ⟨0, by omega⟩ A * g⁻¹ ∈ planeGroup P := by
    rw [hg]
    exact ⟨_, ⟨A, rfl⟩, by simp⟩
  have hcent : longBlock K n ⟨0, by omega⟩ A ∈ Subgroup.center (StatedSp n K) :=
    mem_center_of_conj_mem_center (hle hmem)
  have h1 : longBlock K n ⟨0, by omega⟩ A = 1 :=
    eq_one_of_mem_center_of_mem_suppGroup hcent (isSupp_longBlock _ A)
      (t := Sum.inl (⟨1, by omega⟩ : Fin n)) (by
        rintro (h | h)
        · have := Sum.inl_injective h
          simp at this
        · exact Sum.inl_ne_inr h)
  have h2 : A = 1 := longBlock_injective _ (by rw [h1, map_one])
  have h3 := congrArg (fun B : SL(2, K) => (B : Matrix (Fin 2) (Fin 2) K) 0 1) h2
  simp [hA, mkSL] at h3

theorem not_commutator_le_center_of_not_orth (h2 : (2 : K) ≠ 0)
    (hex : ∃ c : Kˣ, (c : K) ≠ ((c⁻¹ : Kˣ) : K)) (hn : 2 ≤ n)
    {P Q : Submodule K (Fin n ⊕ Fin n → K)} (hP : IsHyperbolicPlane P)
    (hQ : IsHyperbolicPlane Q) {u v : Fin n ⊕ Fin n → K} (hu : u ∈ P) (hv : v ∈ Q)
    (huv : form u v ≠ 0) :
    ¬ ⁅planeGroup P, planeGroup Q⁆ ≤ Subgroup.center (StatedSp n K) := by
  intro hc
  by_cases hne : planeGroup P = planeGroup Q
  · rw [hne] at hc
    exact planeGroup_not_le_center hn hQ ((planeGroup_le_commutator h2 hex hQ).trans hc)
  · exact huv (forall_form_eq_zero_of_commutator_mem_center h2 hex hP hQ hne hc u hu v hv)

theorem exists_pair_plane_not_commute (h2 : (2 : K) ≠ 0)
    (hex : ∃ c : Kˣ, (c : K) ≠ ((c⁻¹ : Kˣ) : K)) (hn : 2 ≤ n) (hab : a ≠ b) :
    ∃ H ∈ pairPlanes K n a b,
      ¬ ⁅planeGroup H, planeGroup (stdPlane K n a)⁆ ≤ Subgroup.center (StatedSp n K) ∧
      ¬ ⁅planeGroup H, planeGroup (stdPlane K n b)⁆ ≤ Subgroup.center (StatedSp n K) := by
  set u : Fin n ⊕ Fin n → K := Pi.single (Sum.inl a) 1 + Pi.single (Sum.inl b) 1 with hu
  set w : Fin n ⊕ Fin n → K :=
    (2 : K)⁻¹ • (Pi.single (Sum.inr a) 1 + Pi.single (Sum.inr b) 1) with hw
  have hfa : ∀ x y : Fin n, form (Pi.single (Sum.inl x) (1 : K) : Fin n ⊕ Fin n → K)
      (Pi.single (Sum.inr y) 1) = if x = y then 1 else 0 := by
    intro x y
    rw [form_single_right]
    simp [Pi.single_apply, eq_comm]
  have huw : form u w = 1 := by
    rw [hu, hw, form_smul_right, form_add_left, form_add_right, form_add_right, hfa, hfa, hfa, hfa]
    simp [hab, hab.symm]
    field_simp
    norm_num
  have hH : IsHyperbolicPlane (Submodule.span K {u, w}) := ⟨u, w, huw, rfl⟩
  have hmem_u : u ∈ Submodule.span K {u, w} := Submodule.subset_span (by simp)
  have hle : Submodule.span K {u, w} ≤ stdPlane K n a ⊔ stdPlane K n b := by
    rw [Submodule.span_le]
    intro x hx
    rw [SetLike.mem_coe, mem_sup_stdPlane_iff hab]
    intro t ht
    have h1 : t ≠ Sum.inl a := fun h => ht (Or.inl (h ▸ inl_mem_coords a))
    have h2' : t ≠ Sum.inr a := fun h => ht (Or.inl (h ▸ inr_mem_coords a))
    have h3 : t ≠ Sum.inl b := fun h => ht (Or.inr (h ▸ inl_mem_coords b))
    have h4 : t ≠ Sum.inr b := fun h => ht (Or.inr (h ▸ inr_mem_coords b))
    rcases hx with rfl | rfl
    · simp [hu, h1, h3]
    · simp [hw, h2', h4]
  refine ⟨_, ⟨hH, hle⟩, ?_, ?_⟩
  · refine not_commutator_le_center_of_not_orth h2 hex hn hH (isHyperbolicPlane_stdPlane a)
      hmem_u (v := Pi.single (Sum.inr a) 1) (Submodule.subset_span (by simp)) ?_
    rw [hu, form_add_left, hfa, hfa]
    simp [hab.symm]
  · refine not_commutator_le_center_of_not_orth h2 hex hn hH (isHyperbolicPlane_stdPlane b)
      hmem_u (v := Pi.single (Sum.inr b) 1) (Submodule.subset_span (by simp)) ?_
    rw [hu, form_add_left, hfa, hfa]
    simp [hab]

end NonCommuting

section RankTwo

theorem sup_eq_top_of_orth_planes {P Q : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hP : IsHyperbolicPlane P) (hQ : IsHyperbolicPlane Q)
    (horth : ∀ x ∈ P, ∀ y ∈ Q, form x y = 0) : P ⊔ Q = ⊤ := by
  obtain ⟨u0, w0, h0, rfl⟩ := hP
  obtain ⟨u1, w1, h1, rfl⟩ := hQ
  have hu0 : u0 ∈ Submodule.span K {u0, w0} := Submodule.subset_span (by simp)
  have hw0 : w0 ∈ Submodule.span K {u0, w0} := Submodule.subset_span (by simp)
  have hu1 : u1 ∈ Submodule.span K {u1, w1} := Submodule.subset_span (by simp)
  have hw1 : w1 ∈ Submodule.span K {u1, w1} := Submodule.subset_span (by simp)
  have hflip : ∀ x y : Fin 2 ⊕ Fin 2 → K, form x y = 0 → form y x = 0 := fun x y h => by
    rw [form_antisymm, h, neg_zero]
  have hframe : IsPlaneFrame ![u0, u1] ![w0, w1] :=
    { pair := fun k l => by
        fin_cases k <;> fin_cases l
        · simpa using h0
        · simpa using horth u0 hu0 w1 hw1
        · simpa using hflip _ _ (horth w0 hw0 u1 hu1)
        · simpa using h1
      uu := fun k l => by
        fin_cases k <;> fin_cases l
        · exact form_self _
        · simpa using horth u0 hu0 u1 hu1
        · simpa using hflip _ _ (horth u0 hu0 u1 hu1)
        · exact form_self _
      ww := fun k l => by
        fin_cases k <;> fin_cases l
        · exact form_self _
        · simpa using horth w0 hw0 w1 hw1
        · simpa using hflip _ _ (horth w0 hw0 w1 hw1)
        · exact form_self _ }
  have hspan : Submodule.span K (Set.range (Sum.elim ![u0, u1] ![w0, w1])) = ⊤ :=
    hframe.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp)
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  rcases s with k | k <;> fin_cases k
  · exact Submodule.mem_sup_left hu0
  · exact Submodule.mem_sup_right hu1
  · exact Submodule.mem_sup_left hw0
  · exact Submodule.mem_sup_right hw1

theorem false_of_orth_planes_rank_two {P Q H : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hP : IsHyperbolicPlane P) (hQ : IsHyperbolicPlane Q) (hH : IsHyperbolicPlane H)
    (hPQ : ∀ x ∈ P, ∀ y ∈ Q, form x y = 0) (hHP : ∀ x ∈ H, ∀ y ∈ P, form x y = 0)
    (hHQ : ∀ x ∈ H, ∀ y ∈ Q, form x y = 0) : False := by
  have htop := sup_eq_top_of_orth_planes hP hQ hPQ
  obtain ⟨h, h', hhh', rfl⟩ := hH
  have hmem : h ∈ Submodule.span K {h, h'} := Submodule.subset_span (by simp)
  have h1 : h' ∈ P ⊔ Q := by
    rw [htop]
    trivial
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 h1
  have h0 : form h h' = 0 := by
    rw [← hpq, form_add_right, hHP h hmem p hp, hHQ h hmem q hq, add_zero]
  rw [h0] at hhh'
  exact zero_ne_one hhh'

end RankTwo

section Central

theorem isPerfect_statedSp_of_four_le [Finite K] (h4 : 4 ≤ Nat.card K) :
    Group.IsPerfect (StatedSp n K) := by
  refine CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp n K (Or.inl ?_)
  have := Fintype.ofFinite K
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨s, hs⟩

theorem mem_center_of_forall_commutator_mem_center {G : Type*} [Group G]
    (hperf : Group.IsPerfect G) {w : G} (h : ∀ g : G, ⁅w, g⁆ ∈ Subgroup.center G) :
    w ∈ Subgroup.center G := by
  have key : ∀ a b : G, w * ⁅a, b⁆ = ⁅a, b⁆ * w := by
    intro a b
    have ha : w * a * w⁻¹ = a * ⁅w, a⁆ := by
      calc w * a * w⁻¹ = ⁅w, a⁆ * a := by simp only [commutatorElement_def]; group
        _ = a * ⁅w, a⁆ := (Subgroup.mem_center_iff.1 (h a) a).symm
    have hb : w * b * w⁻¹ = b * ⁅w, b⁆ := by
      calc w * b * w⁻¹ = ⁅w, b⁆ * b := by simp only [commutatorElement_def]; group
        _ = b * ⁅w, b⁆ := (Subgroup.mem_center_iff.1 (h b) b).symm
    have e : w * ⁅a, b⁆ * w⁻¹ = ⁅w * a * w⁻¹, w * b * w⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    have e2 : w * ⁅a, b⁆ * w⁻¹ = ⁅a, b⁆ := by
      rw [e, ha, hb, (commutator_mul_central (h b)).2, (commutator_mul_central (h a)).1]
    calc w * ⁅a, b⁆ = (w * ⁅a, b⁆ * w⁻¹) * w := by group
      _ = ⁅a, b⁆ * w := by rw [e2]
  have hle : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.centralizer {w} := by
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact key a b
  rw [← commutator_def, Group.isPerfect_def.1 hperf] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  have := Subgroup.mem_centralizer_iff.1 (hle (Subgroup.mem_top g)) w rfl
  exact this.symm

theorem neg_one_eq_torusHom : (-1 : SL(2, K)) = torusHom K (-1) := by
  apply Subtype.ext
  rw [coe_torusHom]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem planeTorusDiag_neg_one (x : Fin n ⊕ Fin n) {i j : Fin n} :
    planeTorusDiag i j (-1 : Kˣ) (-1) x = if x ∈ coords i ∪ coords j then -1 else 1 := by
  unfold planeTorusDiag
  by_cases h1 : x = Sum.inl i
  · simp [h1, inl_mem_coords]
  · by_cases h2 : x = Sum.inr i
    · simp [h2, inr_mem_coords]
    · by_cases h3 : x = Sum.inl j
      · simp [h3, inl_mem_coords]
      · by_cases h4 : x = Sum.inr j
        · simp [h4, inr_mem_coords]
        · have : x ∉ coords i ∪ coords j := by
            rintro (h | h)
            · rcases mem_coords.1 h with h | h
              · exact h1 h
              · exact h2 h
            · rcases mem_coords.1 h with h | h
              · exact h3 h
              · exact h4 h
          simp [h1, h2, h3, h4, this]

theorem commute_longInv_mul_longInv {i j : Fin n} (hij : i ≠ j) {g : StatedSp n K}
    (hg : g ∈ suppGroup (coords i ∪ coords j)) :
    Commute (longInv K n i * longInv K n j) g := by
  have e : longInv K n i * longInv K n j = planeTorusElt K i j (-1) (-1) := by
    simp only [longInv, planeTorusElt, neg_one_eq_torusHom]
  rw [e]
  refine (Commute.symm ((commute_planeTorusElt_iff hij (-1) (-1) g).2 fun r t => ?_))
  rw [planeTorusDiag_neg_one, planeTorusDiag_neg_one]
  by_cases hr : r ∈ coords i ∪ coords j
  · by_cases ht : t ∈ coords i ∪ coords j
    · simp [hr, ht]
    · have h0 : mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t :=
        hg r t (fun h => ht h.2)
      have hrt : r ≠ t := fun h => ht (h ▸ hr)
      simp [hr, ht, h0, Matrix.one_apply_ne hrt]
  · by_cases ht : t ∈ coords i ∪ coords j
    · have h0 : mat n K g r t = (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) r t :=
        hg r t (fun h => hr h.1)
      have hrt : r ≠ t := fun h => hr (h ▸ ht)
      simp [hr, ht, h0, Matrix.one_apply_ne hrt]
    · simp [hr, ht]

theorem not_forall_commutator_longInv_mul_mem_center [Finite K] (h2 : (2 : K) ≠ 0)
    (h4 : 4 ≤ Nat.card K) (hr : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) :
    ¬ ∀ g : StatedSp n K,
      ⁅longInv K n i * longInv K n j, g⁆ ∈ Subgroup.center (StatedSp n K) := by
  intro h
  have hw := mem_center_of_forall_commutator_mem_center (isPerfect_statedSp_of_four_le h4) h
  obtain ⟨c, hci, hcj⟩ := exists_ne_ne hr i j
  have hsupp : longInv K n i * longInv K n j ∈ suppGroup (coords i ∪ coords j) :=
    mul_mem (longInv_mem_suppGroup (Or.inl rfl)) (longInv_mem_suppGroup (Or.inr rfl))
  have h1 : longInv K n i * longInv K n j = 1 :=
    eq_one_of_mem_center_of_mem_suppGroup hw hsupp (t := Sum.inl c) (by
      rintro (h | h)
      · rcases mem_coords.1 h with h | h
        · exact hci (Sum.inl_injective h)
        · exact Sum.inl_ne_inr h
      · rcases mem_coords.1 h with h | h
        · exact hcj (Sum.inl_injective h)
        · exact Sum.inl_ne_inr h)
  have e : longInv K n i * longInv K n j = planeTorusElt K i j (-1) (-1) := by
    simp only [longInv, planeTorusElt, neg_one_eq_torusHom]
  have h3 := congrArg (fun x => mat n K x (Sum.inl i) (Sum.inl i)) (e.symm.trans h1)
  simp only [mat_planeTorusElt hij, map_one, Matrix.diagonal_apply_eq, Matrix.one_apply_eq,
    planeTorusDiag_inl_i] at h3
  apply h2
  have h5 : (-1 : K) = 1 := by simpa using h3
  linear_combination (-1 : K) * h5

theorem eq_two_of_central_image [Finite K] (h2 : (2 : K) ≠ 0) (h4 : 4 ≤ Nat.card K) {r : ℕ}
    (hr : 2 ≤ r) {N : Type*} [Group N] (ν : StatedSp r K →* N)
    (hν : ν.ker ≤ Subgroup.center (StatedSp r K)) (g : StatedSp r K) {k l : Fin r}
    (hkl : k ≠ l)
    (hc : ν (g * (longInv K r k * longInv K r l) * g⁻¹) ∈ Subgroup.center N) : r = 2 := by
  by_contra hne
  apply not_forall_commutator_longInv_mul_mem_center h2 h4 (by omega) hkl
  intro y
  have h1 : ν ⁅g * (longInv K r k * longInv K r l) * g⁻¹, g * y * g⁻¹⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 hc (ν (g * y * g⁻¹))).symm
  have h3 := hν h1
  have e : ⁅g * (longInv K r k * longInv K r l) * g⁻¹, g * y * g⁻¹⁆ =
      g * ⁅longInv K r k * longInv K r l, y⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e] at h3
  exact mem_center_of_conj_mem_center h3

end Central

section BlockPairs

variable {i j : Fin n}

theorem shortBlock_range_le_suppGroup (hij : i ≠ j) :
    (shortBlock K hij).range ≤ suppGroup (coords i ∪ coords j) :=
  le_sup_left.trans (shortBlock_sup_longBlock_eq_suppGroup hij).le

theorem longBlock_range_le_suppGroup_right (hij : i ≠ j) :
    (longBlock K n j).range ≤ suppGroup (coords i ∪ coords j) :=
  le_sup_right.trans (shortBlock_sup_longBlock_eq_suppGroup hij).le

theorem shortGroupNeg_le_suppGroup (hij : i ≠ j) :
    shortGroupNeg K hij ≤ suppGroup (coords i ∪ coords j) := by
  rintro _ ⟨x, hx, rfl⟩
  have hw : planeWeyl K n j ∈ suppGroup (coords i ∪ coords j) :=
    longBlock_range_le_suppGroup_right hij ⟨weylMat K, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact mul_mem (mul_mem hw (shortBlock_range_le_suppGroup hij hx)) (inv_mem hw)

theorem exists_symplecticBlockStandardPair_short_comp {Y : Type} [Group Y] (hij : i ≠ j)
    (φ : ↥(suppGroup (coords i ∪ coords j) : Subgroup (StatedSp n K)) →* Y)
    (hφ : Function.Injective φ) {S : Subgroup (StatedSp n K)}
    (hS : S = (shortBlock K hij).range ∨ S = shortGroupNeg K hij) :
    ∃ W, SymplecticBlockStandardPair K W
      (((longBlock K n j).range.subgroupOf (suppGroup (coords i ∪ coords j))).map φ)
      ((S.subgroupOf (suppGroup (coords i ∪ coords j))).map φ) := by
  have hL := longBlock_range_le_suppGroup_right (K := K) hij
  rcases hS with rfl | rfl
  · have h := symplecticBlockStandardPair_longShort (K := K) hij
    have h' := symplecticBlockStandardPair_subgroupOf
      (sup_le hL (shortBlock_range_le_suppGroup hij)) h
    exact ⟨_, symplecticBlockStandardPair_map h' φ hφ⟩
  · have h := symplecticBlockStandardPair_shortGroupNeg (K := K) hij
    have h' := symplecticBlockStandardPair_subgroupOf
      (sup_le hL (shortGroupNeg_le_suppGroup hij)) h
    exact ⟨_, symplecticBlockStandardPair_map h' φ hφ⟩

end BlockPairs

end CFSG.ClassicalInvolution.Models.SymplecticPairs

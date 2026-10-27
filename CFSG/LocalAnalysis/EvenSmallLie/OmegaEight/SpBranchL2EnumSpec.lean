module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Enum
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchIota
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchNfHom

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem sMul_zero_right {c : ℕ} (hc : c < 65536) :
    sMul c 0 = c := by
  have h := SModel.codeIso.map_mul (SModel.codeIso.g c) 1
  rw [mul_one, SModel.codeIso.f_one sMul_zero_zero, SModel.codeIso.f_g hc] at h
  exact h.symm

theorem t1Mul_lt {F : Array ℕ} {z c d : ℕ} (hc : c < 65536) (hd : d < 65536) :
    t1Mul F z c d = sMul c d := by
  unfold t1Mul extMul
  rw [ite_eq_left hc, ite_eq_left hd]

theorem t1Mul_x {F : Array ℕ} {z c : ℕ} (hc : c < 65536) :
    t1Mul F z c 65536 = sMul c 0 + 65536 := by
  unfold t1Mul extMul
  rw [ite_eq_left hc, ite_eq_right (lt_irrefl _), Nat.sub_self]

theorem t1Tree_ok (F : Array ℕ)
    (z : ℕ) : treeOK (t1Mul F z) t1Gens 131072 t1Par t1Pj t1Dep = true := by
  have hS := sCheck1_parts.2.2.2.2
  have hglt := sGens_lt
  unfold treeOK at hS ⊢
  rw [List.all_eq_true] at hS ⊢
  intro c hc
  have hcN := List.mem_range.1 hc
  have hlen : t1Gens.length = 10 := rfl
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
  by_cases hcS : c < 65536
  · have h := hS c (List.mem_range.2 hcS)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨⟨⟨hpj, hmul⟩, hpar⟩, hdep⟩
    · exact Or.inl h
    · right
      have hgD : t1Gens.getD (sTree.2.1[c]!) 0 = sGens.getD (sTree.2.1[c]!) 0 :=
        List.getD_append _ _ _ _ hpj
      have hgl : sGens.getD (sTree.2.1[c]!) 0 < 65536 := by
        rw [List.getD_eq_getElem _ _ hpj]
        exact hglt _ (List.getElem_mem hpj)
      have hpj9 : sTree.2.1[c]! < 9 := hpj
      simp only [t1Par, t1Pj, t1Dep, ite_eq_left hcS, ite_eq_left hpar]
      rw [hgD, t1Mul_lt hpar hgl]
      exact ⟨⟨⟨by omega, hmul⟩, by omega⟩, hdep⟩
  · right
    have hc' : c - 65536 < 65536 := by omega
    simp only [t1Par, t1Pj, t1Dep, ite_eq_right hcS, ite_eq_left hc']
    have hg9 : t1Gens.getD 9 0 = 65536 := rfl
    rw [hg9, t1Mul_x hc', sMul_zero_right hc']
    exact ⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩

theorem t1Vec_size (vS : Array ℕ) : (t1Vec vS).size = 131072 := Array.size_ofFn

theorem t1Vec_get (vS : Array ℕ) {c : ℕ} (hc : c < 131072) :
    (t1Vec vS)[c]! = if c < 65536 then vS[c]! else vS[c - 65536]! ^^^ 512 := by
  unfold t1Vec
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem sVec_lt {vS : Array ℕ} (hv : sVecOK vS = true) {c : ℕ} (hc : c < 65536) :
    vS[c]! < 512 := by
  unfold sVecOK at hv
  rw [Bool.and_eq_true, List.all_eq_true] at hv
  have h := hv.2 c (List.mem_range.2 hc)
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem t1Vec_lt {vS : Array ℕ} (hv : sVecOK vS = true) (c : ℕ) : (t1Vec vS)[c]! < 1024 := by
  by_cases hc : c < 131072
  · rw [t1Vec_get vS hc]
    split
    · rename_i hcS
      have := sVec_lt hv hcS
      omega
    · rename_i hcS
      have h := sVec_lt hv (by omega : c - 65536 < 65536)
      exact Nat.xor_lt_two_pow (n := 10) (by omega) (by norm_num)
  · rw [getElem!_neg _ c (by rw [t1Vec_size]; exact hc)]
    decide

theorem t1VecOK {vS : Array ℕ}
    (hv : sVecOK vS = true) :
    vecOK 131072 t1Par t1Pj (fun c => (t1Vec vS)[c]!) = true := by
  have hS := sCheck1_parts.2.2.2.2
  unfold treeOK at hS
  rw [List.all_eq_true] at hS
  have hv' := hv
  unfold sVecOK at hv'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    Bool.or_eq_true] at hv'
  obtain ⟨h0, hall⟩ := hv'
  unfold vecOK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true]
  refine ⟨by rw [t1Vec_get vS (c := 0) (by norm_num), ite_eq_left (by norm_num : (0 : ℕ) < 65536),
      h0],
    fun c hcN => ?_⟩
  by_cases hc0 : c = 0
  · exact Or.inl hc0
  right
  by_cases hcS : c < 65536
  · have h := (hall c hcS).2.resolve_left hc0
    have hT := hS c (List.mem_range.2 hcS)
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hT
    have hpar : sTree.1[c]! < 65536 := (hT.resolve_left hc0).1.2
    simp only [t1Par, t1Pj, ite_eq_left hcS]
    rw [t1Vec_get vS hcN, ite_eq_left hcS, t1Vec_get vS (by omega : sTree.1[c]! < 131072),
      ite_eq_left hpar]
    exact h
  · simp only [t1Par, t1Pj, ite_eq_right hcS]
    rw [t1Vec_get vS hcN, ite_eq_right hcS, t1Vec_get vS (by omega : c - 65536 < 131072),
      ite_eq_left (by omega : c - 65536 < 65536)]
    norm_num

theorem chiV_two_pow_mask (k v : ℕ) :
    ∀ n, chiV n (2 ^ k) v = (decide (k < n) && v.testBit k) := by
  intro n
  induction n with
  | zero => simp [chiV]
  | succ n ih =>
    rw [chiV_succ, ih, Nat.testBit_land, Nat.testBit_two_pow]
    by_cases hkn : k < n
    · have h1 : k < n + 1 := by omega
      have h2 : k ≠ n := by omega
      simp [hkn, h1, h2]
    · by_cases hk : k = n
      · subst hk
        simp
      · have h1 : ¬ k < n + 1 := by omega
        simp [hkn, h1, hk]

theorem chi512_t1Vec {vS : Array ℕ} (hv : sVecOK vS = true) {c : ℕ} (hc : c < 131072) :
    (!chiV 10 512 (t1Vec vS)[c]!) = decide (c < 65536) := by
  have h512 : (512 : ℕ) = 2 ^ 9 := by norm_num
  rw [h512, chiV_two_pow_mask, t1Vec_get vS hc]
  by_cases hcS : c < 65536
  · have hlt : vS[c]! < 2 ^ 9 := sVec_lt hv hcS
    rw [ite_eq_left hcS, Nat.testBit_lt_two_pow hlt]
    simp [hcS]
  · have hlt : vS[c - 65536]! < 2 ^ 9 := sVec_lt hv (by omega : c - 65536 < 65536)
    rw [ite_eq_right hcS, Nat.testBit_xor, Nat.testBit_lt_two_pow hlt, h512,
      Nat.testBit_two_pow_self]
    simp [hcS]

@[expose] def l2eTree (vS : Array ℕ) : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  (Array.ofFn (n := 131072) fun c => t1Par c.val, Array.ofFn (n := 131072) fun c => t1Pj c.val,
    Array.ofFn (n := 131072) fun c => t1Dep c.val, t1Vec vS)

@[expose] def l2eRelW (mul : ℕ → ℕ → ℕ) (vec : Array ℕ) (RW : List (ℕ × ℕ)) : Array (ℕ × ℕ) :=
  Array.ofFn (n := 1024) fun r => ((RW.find? fun p => s2Rel mul vec p.1 p.2 == r.val)).getD (0, 0)

theorem ofFn_get {α : Type*} [Inhabited α] {N : ℕ} (f : ℕ → α) {c : ℕ} (hc : c < N) :
    (Array.ofFn (n := N) fun i => f i.val)[c]! = f c := by
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_ofFn]

theorem s2CharOK_of {j : ℕ}
    {vS : Array ℕ} {RW : List (ℕ × ℕ)} {IV : List ℕ} (hv : sVecOK vS = true)
    (hc : l2eCharOK j (t1Vec vS) RW IV = true) :
    s2CharOK (t1Mul (s2F j) (s2Z j)) (l2eTree vS) (kInv (t1Mul (s2F j) (s2Z j)) 131072)
      (kOrd4 (t1Mul (s2F j) (s2Z j)) 131072)
      (s2RelV (t1Mul (s2F j) (s2Z j)) (l2eTree vS).2.2.2
        (l2eRelW (t1Mul (s2F j) (s2Z j)) (l2eTree vS).2.2.2 RW)) = true := by
  have hv4 : (l2eTree vS).2.2.2 = t1Vec vS := by simp only [l2eTree]
  rw [hv4]
  unfold l2eCharOK at hc
  dsimp only at hc
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨hRW, hIV⟩, hmask⟩ := hc
  have htree := t1Tree_ok (s2F j) (s2Z j)
  have hvec := t1VecOK hv
  unfold s2CharOK
  simp only [Bool.and_eq_true, l2eTree]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  ·
    unfold treeOK at htree ⊢
    rw [List.all_eq_true] at htree ⊢
    intro c hc
    have hcN := List.mem_range.1 hc
    have h := htree c hc
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    · exact Or.inl h
    · right
      simp only [ofFn_get t1Par hcN, ofFn_get t1Pj hcN, ofFn_get t1Dep hcN, ofFn_get t1Dep h3]
      exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  ·
    unfold vecOK at hvec ⊢
    simp only [Bool.and_eq_true, List.all_eq_true] at hvec ⊢
    refine ⟨hvec.1, fun c hc => ?_⟩
    have hcN := List.mem_range.1 hc
    have h := hvec.2 c hc
    simp only [ofFn_get t1Par hcN, ofFn_get t1Pj hcN]
    exact h
  ·
    rw [List.all_eq_true]
    intro b hb
    have h := hmask b hb
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, bne_iff_ne, ne_eq] at h ⊢
    rcases h with ((((h | h) | ⟨p, hp, hpb⟩) | h) | h)
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    ·
      refine Or.inl (Or.inl (Or.inr ⟨s2Rel (t1Mul (s2F j) (s2Z j)) (t1Vec vS) p.1 p.2, ?_, hpb⟩))
      have hp12 := hRW p hp
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hp12
      have hr : s2Rel (t1Mul (s2F j) (s2Z j)) (t1Vec vS) p.1 p.2 < 1024 := by
        unfold s2Rel
        exact Nat.xor_lt_two_pow (n := 10) (Nat.xor_lt_two_pow (n := 10) (t1Vec_lt hv _)
          (t1Vec_lt hv _)) (Nat.pow_lt_pow_right (by norm_num) hp12.2)
      have hfind : ∃ q, (RW.find? fun p' => s2Rel (t1Mul (s2F j) (s2Z j)) (t1Vec vS) p'.1 p'.2 ==
          s2Rel (t1Mul (s2F j) (s2Z j)) (t1Vec vS) p.1 p.2) = some q := by
        cases hq : RW.find? fun p' => s2Rel (t1Mul (s2F j) (s2Z j)) (t1Vec vS) p'.1 p'.2 ==
            s2Rel (t1Mul (s2F j) (s2Z j)) (t1Vec vS) p.1 p.2 with
        | none =>
          have := List.find?_eq_none.1 hq p hp
          simp at this
        | some q => exact ⟨q, rfl⟩
      obtain ⟨q, hq⟩ := hfind
      have hqm := List.mem_of_find?_eq_some hq
      have hqr := List.find?_some hq
      simp only [beq_iff_eq] at hqr
      have hW : (l2eRelW (t1Mul (s2F j) (s2Z j)) (t1Vec vS) RW)[s2Rel (t1Mul (s2F j) (s2Z j))
          (t1Vec vS) p.1 p.2]! = q := by
        unfold l2eRelW
        rw [ofFn_get (fun r => ((RW.find? fun p' => s2Rel (t1Mul (s2F j) (s2Z j)) (t1Vec vS) p'.1
          p'.2 == r)).getD (0, 0)) hr]
        rw [hq, Option.getD_some]
      have hq12 := hRW q hqm
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hq12
      simp only [s2RelV, List.mem_filter, List.mem_range, hW, decide_eq_true_eq, Bool.and_eq_true,
        beq_iff_eq]
      exact ⟨hr, ⟨hq12.1, hq12.2⟩, hqr⟩
    ·
      refine Or.inl (Or.inr ?_)
      rw [hIV, List.filter_map, List.length_map] at h
      exact h
    ·
      refine Or.inr ?_
      have e : (kOrd4 (t1Mul (s2F j) (s2Z j)) 131072).filter
          (fun c => !chiV 10 b (t1Vec vS)[c]!) =
          (List.range 131072).filter (fun c => !chiV 10 b (t1Vec vS)[c]! &&
            (t1Mul (s2F j) (s2Z j) c c != 0 && t1Mul (s2F j) (s2Z j) (t1Mul (s2F j) (s2Z j) c c)
              (t1Mul (s2F j) (s2Z j) c c) == 0)) := by
        unfold kOrd4
        rw [List.filter_filter]
      rw [e]
      exact h
  ·
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro c hc
    exact chi512_t1Vec hv hc

theorem s2IotaTab_get
    (mul : ℕ → ℕ → ℕ) (im : List ℕ) {c : ℕ} (hc : c < 65536) :
    (s2IotaTab mul im)[c]! = mul (wprodN mul 7 (fun l => im.getD l 0) (sAutData.nfE c))
      (wprodN mul 9 (fun i => im.getD (7 + i) 0) (sAutData.nfA c)) := by
  obtain ⟨he, ha, -⟩ := sCheck1_parts.2.1 c hc
  have he' : sAutData.nfE c < 128 := he
  have ha' : sAutData.nfA c < 512 := ha
  unfold s2IotaTab
  dsimp only
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_map]
  simp only [List.getElem_toArray, List.getElem_range]
  rw [ite_eq_left he', ite_eq_left ha', getElem!_pos _ _ (by simpa using he'),
    getElem!_pos _ _ (by simpa using ha'), Array.getElem_map, Array.getElem_map]
  simp only [List.getElem_toArray, List.getElem_range]

namespace CodeIso

variable {T : Type*} [Group T] {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T 131072 mul)

theorem g_cconj (h0 : mul 0 0 = 0) {inv : ℕ → ℕ}
    (hinv : ∀ c, c < 131072 → inv c < 131072 ∧ mul c (inv c) = 0) {a b : ℕ} (ha : a < 131072)
    (hb : b < 131072) : Φ.g (cconj mul inv a b) = Φ.g a * Φ.g b * (Φ.g a)⁻¹ := by
  have h := Φ.f_conj h0 hinv (Φ.g a) (Φ.g b)
  rw [Φ.f_g ha, Φ.f_g hb] at h
  rw [← h, Φ.g_f]

include Φ in
theorem mul_lt' {a b : ℕ} (ha : a < 131072) (hb : b < 131072) : mul a b < 131072 := by
  have h := Φ.lt (Φ.g a * Φ.g b)
  rwa [Φ.map_mul, Φ.f_g ha, Φ.f_g hb] at h

end CodeIso

theorem sMap_mul {T : Type*}
    [Group T] {W ρ φ : ℕ → T}
    (hφ : ∀ x, x < 65536 → φ x = W (sAutData.nfE x) * bitProd 9 ρ (sAutData.nfA x))
    (hW0 : W 0 = 1) (h2 : ∀ i, i < 9 → ρ i * ρ i = 1)
    (hc : ∀ i j, i < 9 → j < 9 → ρ i * ρ j = ρ j * ρ i)
    (hcb : ∀ l, l < 7 → ∀ i, i < 9 →
      φ (sPc.getD l 0) * ρ i * (φ (sPc.getD l 0))⁻¹ = bitProd 9 ρ (sAutData.cb l i))
    (hstep : ∀ e, e < 2 ^ 7 → ∀ l, l < 7 →
      φ (sMul (wprodN sMul 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0)) = W e * φ (sPc.getD l 0))
    (hK : ∀ g ∈ [128, 34816], a9K.co g < 512 ∧ a9K.lin (a9K.co g) = g)
    {x : ℕ} (hx : x < 65536) {g : ℕ} (hg : g ∈ sGens) : φ (sMul x g) = φ x * φ g := by
  have hnorm : ∀ x : SModel, KFacts.Mem SModel.codeIso sAutData.K x → ∀ y : SModel,
      KFacts.Mem SModel.codeIso sAutData.K (y * x * y⁻¹) := by
    intro x hx y
    have := sChar SModel.codeIso (MulAut.conj y) x hx
    rw [MulAut.conj_apply] at this
    exact this
  have hgen : (∃ l, l < sAutData.q ∧ g = sAutData.g l) ∨ sAutData.K.In g := by
    rcases List.mem_append.1 hg with hg | hg
    · left
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hg
      exact ⟨l, hl, (List.getD_eq_getElem _ _ hl).symm⟩
    · right
      exact ⟨(hK g hg).1, (hK g hg).2⟩
  exact (sAutFacts sMul_zero_zero).map_mul_gen SModel.codeIso rfl hnorm hφ hW0 h2 hc hcb hstep hx
    hgen

theorem iotaFacts_gen
    {T₁ : Subgroup G} {mul : ℕ → ℕ → ℕ} {inv : ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul)
    (h0 : mul 0 0 = 0) (hinv : ∀ c, c < 131072 → inv c < 131072 ∧ mul c (inv c) = 0)
    {im : List ℕ} {vec : Array ℕ} (him : ∀ c ∈ im, c < 131072)
    (hker : ∀ c, c < 65536 → c = 0 ∨ ¬ (s2IotaTab mul im)[c]! = 0)
    (hgens : ∀ g ∈ sGens, s2InSp vec (s2IotaTab mul im)[g]! = true)
    (hK : ∀ g ∈ [128, 34816], a9K.co g < 512 ∧ a9K.lin (a9K.co g) = g)
    (hρ : ∀ i, i < 9 → mul (im.getD (7 + i) 0) (im.getD (7 + i) 0) = 0 ∧
      ∀ i', i' < 9 → mul (im.getD (7 + i) 0) (im.getD (7 + i') 0) =
        mul (im.getD (7 + i') 0) (im.getD (7 + i) 0))
    (hcb : ∀ l, l < 7 → ∀ i, i < 9 →
      cconj mul inv (s2IotaTab mul im)[sPc.getD l 0]! (im.getD (7 + i) 0) =
        wprodN mul 9 (fun i => im.getD (7 + i) 0) (sAutData.cb l i))
    (hst : ∀ e, e < 128 → ∀ l, l < 7 →
      (s2IotaTab mul im)[sMul (wprodN sMul 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0)]! =
        mul (wprodN mul 7 (fun l => im.getD l 0) e) (s2IotaTab mul im)[sPc.getD l 0]!) :
    IotaFacts mul (s2IotaTab mul im) vec := by
  have hρlt : ∀ i, i < 9 → im.getD (7 + i) 0 < 131072 := by
    intro i hi
    by_cases h7 : 7 + i < im.length
    · rw [List.getD_eq_getElem _ _ h7]; exact him _ (List.getElem_mem h7)
    · rw [List.getD_eq_default _ _ (by omega)]; norm_num
  have hwlt : ∀ l, l < 7 → im.getD l 0 < 131072 := by
    intro l hl
    by_cases h7 : l < im.length
    · rw [List.getD_eq_getElem _ _ h7]; exact him _ (List.getElem_mem h7)
    · rw [List.getD_eq_default _ _ (by omega)]; norm_num
  have hIW : ∀ e, wprodN mul 7 (fun l => im.getD l 0) e < 131072 := fun e =>
    (Φ.g_wprodN h0 hwlt e).1
  have hIL : ∀ a, wprodN mul 9 (fun i => im.getD (7 + i) 0) a < 131072 := fun a =>
    (Φ.g_wprodN h0 hρlt a).1
  have hlt : ∀ c, c < 65536 → (s2IotaTab mul im)[c]! < 131072 := by
    intro c hc
    rw [s2IotaTab_get mul im hc]
    exact Φ.mul_lt' (hIW _) (hIL _)
  have hbp : ∀ a, bitProd 9 (fun i => Φ.g (im.getD (7 + i) 0)) a =
      Φ.g (wprodN mul 9 (fun i => im.getD (7 + i) 0) a) := fun a =>
    (Φ.g_wprodN h0 hρlt a).2.symm
  have hφ : ∀ x, x < 65536 → Φ.g (s2IotaTab mul im)[x]! =
      Φ.g (wprodN mul 7 (fun l => im.getD l 0) (sAutData.nfE x)) *
        bitProd 9 (fun i => Φ.g (im.getD (7 + i) 0)) (sAutData.nfA x) := by
    intro x hx
    rw [s2IotaTab_get mul im hx, hbp, Φ.g_mul (hIW _) (hIL _)]
  generalize s2IotaTab mul im = A at hlt hφ hker hgens hcb hst ⊢
  have hW0 : Φ.g (wprodN mul 7 (fun l => im.getD l 0) 0) = 1 := by
    rw [wprodN_zero, Φ.g_zero h0]
  have h2 : ∀ i, i < 9 → Φ.g (im.getD (7 + i) 0) * Φ.g (im.getD (7 + i) 0) = 1 := by
    intro i hi
    rw [← Φ.g_mul (hρlt i hi) (hρlt i hi), (hρ i hi).1, Φ.g_zero h0]
  have hcom : ∀ i i', i < 9 → i' < 9 → Φ.g (im.getD (7 + i) 0) * Φ.g (im.getD (7 + i') 0) =
      Φ.g (im.getD (7 + i') 0) * Φ.g (im.getD (7 + i) 0) := by
    intro i i' hi hi'
    rw [← Φ.g_mul (hρlt i hi) (hρlt i' hi'), ← Φ.g_mul (hρlt i' hi') (hρlt i hi),
      (hρ i hi).2 i' hi']
  have hgl : ∀ l, l < 7 → sPc.getD l 0 < 65536 := fun l hl => sCheck1_parts.1 l hl
  have hcb' : ∀ l, l < 7 → ∀ i, i < 9 →
      Φ.g A[sPc.getD l 0]! * Φ.g (im.getD (7 + i) 0) * (Φ.g A[sPc.getD l 0]!)⁻¹ =
          bitProd 9 (fun i => Φ.g (im.getD (7 + i) 0)) (sAutData.cb l i) := by
    intro l hl i hi
    rw [hbp, ← hcb l hl i hi, Φ.g_cconj h0 hinv (hlt _ (hgl l hl)) (hρlt i hi)]
  have hstep : ∀ e, e < 2 ^ 7 → ∀ l, l < 7 →
      Φ.g A[sMul (wprodN sMul 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0)]! =
        Φ.g (wprodN mul 7 (fun l => im.getD l 0) e) * Φ.g A[sPc.getD l 0]! := by
    intro e he l hl
    rw [hst e he l hl, Φ.g_mul (hIW _) (hlt _ (hgl l hl))]
  have hmul : ∀ c, c < 65536 → ∀ g ∈ sGens, Φ.g A[sMul c g]! = Φ.g A[c]! * Φ.g A[g]! := by
    intro c hc g hg
    obtain ⟨ιf, hιf⟩ : ∃ f : ℕ → ℕ, ∀ c, A[c]! = f c := ⟨_, fun _ => rfl⟩
    obtain ⟨Wf, hWf⟩ : ∃ f : ℕ → T₁, ∀ e, Φ.g (wprodN mul 7 (fun l => im.getD l 0) e) = f e :=
      ⟨_, fun _ => rfl⟩
    obtain ⟨ρf, hρf⟩ : ∃ f : ℕ → T₁, ∀ i, Φ.g (im.getD (7 + i) 0) = f i := ⟨_, fun _ => rfl⟩
    simp only [hιf, hWf, hρf] at hφ hW0 h2 hcom hcb' hstep ⊢
    exact sMap_mul (W := Wf) (ρ := ρf) (φ := fun c => Φ.g (ιf c)) hφ hW0 h2 hcom hcb' hstep hK
      hc hg
  refine ⟨?_, hlt, fun c hc h => ?_, hgens, fun c hc g hg => ?_⟩
  ·
    have h3 : (3 : ℕ) ∈ sGens := by decide
    have e := hmul 0 (by norm_num) 3 h3
    rw [sMul_zero_left (c := 3) (by norm_num)] at e
    have e2 : Φ.g A[0]! = 1 := mul_eq_right.1 e.symm
    rw [← Φ.f_g (hlt 0 (by norm_num)), e2, Φ.f_one h0]
  · rcases hker c hc with h' | h'
    · exact h'
    · exact absurd h h'
  · have e := hmul c hc g hg
    have hcg : sMul c g < 65536 := by
      have h' := SModel.codeIso.lt (SModel.codeIso.g c * SModel.codeIso.g g)
      rwa [SModel.codeIso.map_mul, SModel.codeIso.f_g hc, SModel.codeIso.f_g (sGens_lt g hg)]
        at h'
    rw [← Φ.f_g (hlt _ hcg), e, Φ.map_mul, Φ.f_g (hlt _ hc), Φ.f_g (hlt _ (sGens_lt g hg))]

theorem iotaFacts_of
    {T₁ : Subgroup G} {j : ℕ} (Φ : CodeIso T₁ 131072 (t1Mul (s2F j) (s2Z j)))
    (hinv : ∀ c, c < 131072 → t1Inv (s2F j) (s2Z j) c < 131072 ∧
      t1Mul (s2F j) (s2Z j) c (t1Inv (s2F j) (s2Z j) c) = 0)
    {vec : Array ℕ} (h : l2eIotaOK j vec = true) :
    IotaFacts (t1Mul (s2F j) (s2Z j)) (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))
      vec := by
  unfold l2eIotaOK at h
  dsimp only at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨him, -⟩, hker⟩, hgens⟩, hK⟩, hρ⟩, hcb⟩, hst⟩ := h
  exact iotaFacts_gen Φ (t1Mul_zero _ _) hinv him hker hgens hK hρ hcb hst

section Enum

variable {T₁ : Subgroup G} {j : ℕ}
  (Φ : CodeIso T₁ 131072 (t1Mul (s2F j) (s2Z j)))
  (hinv : invOK (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) 131072 = true)
  (hG₁ : Gen (t1Mul (s2F j) (s2Z j)) t1Gens 131072)

theorem l2eRec_entry {Rs : List (ℕ × List (ℕ × ℕ))} {r : ℕ}
    (hr : (Rs.any fun q => q.1 == r) = true) :
    ∃ q ∈ Rs, q.1 = r ∧ l2eRec Rs r = q.2.map Prod.fst := by
  have hs : (Rs.find? fun q => q.1 == r).isSome := by
    rw [List.find?_isSome]
    rw [List.any_eq_true] at hr
    exact hr
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hs
  have hq1 := List.find?_some hq
  rw [beq_iff_eq] at hq1
  refine ⟨q, List.mem_of_find?_eq_some hq, hq1, ?_⟩
  unfold l2eRec
  rw [hq, Option.map_some, Option.getD_some]

theorem l2eRec_any {Rs : List (ℕ × List (ℕ × ℕ))} {r c : ℕ} (hc : c ∈ l2eRec Rs r) :
    (Rs.any fun q => q.1 == r) = true := by
  unfold l2eRec at hc
  cases hq : Rs.find? fun q => q.1 == r with
  | none => rw [hq] at hc; simp at hc
  | some q =>
    have hq1 := List.find?_some hq
    rw [List.any_eq_true]
    exact ⟨q, List.mem_of_find?_eq_some hq, hq1⟩

include hinv hG₁ in
theorem l2eRec_spec {Rs : List (ℕ × List (ℕ × ℕ))} (hRs : l2eRecsOK j Rs = true) {r : ℕ}
    (hr : (Rs.any fun q => q.1 == r) = true) (x : T₁) :
    Φ.f x ∈ l2eRec Rs r ↔ x ∈ MulAction.orbit (ConjAct T₁) (Φ.g r) := by
  obtain ⟨q, hq, hq1, hrec⟩ := l2eRec_entry hr
  unfold l2eRecsOK at hRs
  rw [List.all_eq_true] at hRs
  have h := hRs q hq
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlt, hO⟩, hC⟩ := h
  have hO' := orbOK_of_M _ _ _ hO
  have hC' := orbClosed_of_M _ _ _ hC
  rw [← Φ.f_g hlt] at hO' hC'
  rw [hrec, ← hq1]
  exact (Φ.mem_orbit_iff (t1Mul_zero _ _) hinv t1Gens_lt hG₁ hO' hC' x).symm

include hinv hG₁ in
theorem l2eRec_conj {Rs : List (ℕ × List (ℕ × ℕ))} (hRs : l2eRecsOK j Rs = true) {r c : ℕ}
    (hc : c ∈ l2eRec Rs r) (hcN : c < 131072) (g : T₁) :
    Φ.f (g * Φ.g c * g⁻¹) ∈ l2eRec Rs r := by
  have hr := l2eRec_any hc
  have h1 := (l2eRec_spec Φ hinv hG₁ hRs hr (Φ.g c)).1 (by rw [Φ.f_g hcN]; exact hc)
  refine (l2eRec_spec Φ hinv hG₁ hRs hr _).2 ?_
  obtain ⟨g', hg'⟩ := mem_orbit_iff_conj.1 h1
  exact mem_orbit_iff_conj.2 ⟨g * g', by rw [← hg']; group⟩

include hinv hG₁ in
theorem cent_code {S : Subgroup G} {vec : Array ℕ} {C3 : List ℕ} {O3 : List (ℕ × ℕ)}
    (hcent : l2eCentOK j vec C3 O3 = true) {y : G}
    (hSp : ∀ g : T₁, y⁻¹ * g * y ∈ S ↔ s2InSp vec (Φ.f g) = true)
    (hιlt : ∀ g ∈ sGens, (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[g]! < 131072)
    (hgι : ∀ g ∈ sGens,
      y⁻¹ * (Φ.g (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[g]! : G) * y ∈ S)
    {c : T₁} (hc : ∀ g : T₁, y⁻¹ * g * y ∈ S → c * g = g * c) : Φ.f c = 0 ∨ Φ.f c = 24 := by
  have h0 := t1Mul_zero (s2F j) (s2Z j)
  unfold l2eCentOK at hcent
  dsimp only at hcent
  simp only [Bool.and_eq_true] at hcent
  obtain ⟨⟨⟨⟨⟨⟨h3, hO⟩, hCl⟩, hsort⟩, hcomm⟩, hlen⟩, hCS⟩ := hcent
  rw [List.all_eq_true] at hsort hcomm hCS
  rw [beq_iff_eq] at hlen
  have h3N : (3 : ℕ) < 131072 := by norm_num
  have hc3 : c * Φ.g 3 = Φ.g 3 * c := hc _ ((hSp _).2 (by rw [Φ.f_g h3N]; exact h3))
  have hO' := orbOK_of_M _ _ _ hO
  have hCl' := orbClosed_of_M _ _ _ hCl
  rw [← Φ.f_g h3N] at hO' hCl'
  have hnd : C3.Nodup := (List.isChain_iff_pairwise.1 (chain_of_zip_tail' fun p hp => by
    have := hsort p hp
    rwa [decide_eq_true_eq] at this)).imp ne_of_lt
  have hC : ∀ d ∈ C3, d < 131072 ∧
      t1Mul (s2F j) (s2Z j) d (Φ.f (Φ.g 3)) = t1Mul (s2F j) (s2Z j) (Φ.f (Φ.g 3)) d := by
    intro d hd
    have := hcomm d hd
    rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    rw [Φ.f_g h3N]
    exact this
  have hlen' : C3.length * (MulAction.orbit (ConjAct T₁) (Φ.g 3)).ncard = 131072 := by
    rw [Φ.ncard_eq h0 hinv t1Gens_lt hG₁ hO' hCl', hlen]
  have key := count_comm_eq Φ (Φ.g 3) hnd hC hlen' (fun d => d == Φ.f c)
  have hmemL : Φ.f c ∈ (List.range 131072).filter fun d => (fun d => d == Φ.f c) d &&
      t1Mul (s2F j) (s2Z j) d (Φ.f (Φ.g 3)) == t1Mul (s2F j) (s2Z j) (Φ.f (Φ.g 3)) d := by
    refine List.mem_filter.2 ⟨List.mem_range.2 (Φ.lt c), ?_⟩
    simp only [beq_self_eq_true, Bool.true_and, beq_iff_eq]
    rw [← Φ.map_mul, ← Φ.map_mul, hc3]
  have hpos : 0 < (C3.filter fun d => d == Φ.f c).length := by
    rw [← key]
    exact List.length_pos_of_mem hmemL
  obtain ⟨d, hd⟩ := List.exists_mem_of_length_pos hpos
  simp only [List.mem_filter, beq_iff_eq] at hd
  obtain ⟨hdC, rfl⟩ := hd
  have hall : (sGens.all fun g => t1Mul (s2F j) (s2Z j) (Φ.f c)
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[g]! ==
      t1Mul (s2F j) (s2Z j) (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))[g]!
        (Φ.f c)) = true := by
    simp only [List.all_eq_true, beq_iff_eq]
    intro g hg
    rw [← Φ.f_g (hιlt g hg), ← Φ.map_mul, ← Φ.map_mul, hc _ (hgι g hg)]
  have h := hCS (Φ.f c) hdC
  simp only [hall, Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq] at h
  exact h

include Φ hinv hG₁ in
theorem l2eActR_spec {Rs : List (ℕ × List (ℕ × ℕ))} (hRs : l2eRecsOK j Rs = true)
    (hcls : kClassOK (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens 131072
      (t1Cls (s2K j) (s2M j) (s2Z j)) = true) {k m w v : ℕ}
    (h : l2eActR j k m w v Rs = true) :
    (∀ r ∈ kRepsC (t1Cls (s2K j) (s2M j) (s2Z j)) 16, r ∈ l2Fix ∨
      ((recM (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens r).map Prod.fst).contains
        (s2B (t1Mul (s2F j) (s2Z j)) (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j []))
          (sFm k m) w r) = false) ∧
    (∀ g ∈ t1Gens, (chiS 131072)[s2B (t1Mul (s2F j) (s2Z j))
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) (sFm k m) w g]! =
        (chiS 131072)[g]!) ∧
    (chiS 131072)[v]! = false := by
  have h0 := t1Mul_zero (s2F j) (s2Z j)
  unfold l2eActR at h
  dsimp only at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true, List.all_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨h16, hchi⟩, hv⟩ := h
  refine ⟨fun r hr => ?_, fun g hg => beq_iff_eq.1 (hchi g hg), hv⟩
  have h1 := h16 r hr
  rw [Bool.or_eq_true, List.contains_iff_mem, Bool.and_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | ⟨hany, hB⟩
  · exact Or.inl h1
  right
  obtain ⟨-, hrecC, -⟩ := classOK_parts hcls
  obtain ⟨cr, hcr, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hrl, -, -, hO, -, -, -⟩ := hrecC cr (List.mem_of_mem_filter hcr)
  have hO2 : orbOK (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) 131072 (Φ.f (Φ.g cr.1))
      (recM (t1Mul (s2F j) (s2Z j)) (t1Inv (s2F j) (s2Z j)) t1Gens cr.1) = true := by
    rw [Φ.f_g hrl]
    exact hO
  rw [Bool.eq_false_iff]
  intro hc
  rw [List.contains_iff_mem] at hc
  obtain ⟨g, hg⟩ := Φ.exists_conj_of_orbOK h0 hinv hO2 hc
  have hz := (l2eRec_spec Φ hinv hG₁ hRs hany (g * Φ.g cr.1 * g⁻¹)).2
    (mem_orbit_iff_conj.2 ⟨g, rfl⟩)
  rw [hg] at hz
  exact Bool.false_ne_true (hB.symm.trans (List.contains_iff_mem.2 hz))

end Enum

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end

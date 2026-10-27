module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafBasic
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinNoQ16E4Sound

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord wordPerm wordPerm_mem getElem!_map'
  letters_of_all mapWord_rep)

theorem Q16Q16.of_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Injective f)
    {x y x' y' : G} (h : Q16Q16 (f x) (f y) (f x') (f y')) : Q16Q16 x y x' y' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨Q16Pair.of_map f hf h1, Q16Pair.of_map f hf h2,
    hf (by rw [map_pow, map_pow]; exact h3), hf (by rw [map_mul, map_mul]; exact h4),
    hf (by rw [map_mul, map_mul]; exact h5), hf (by rw [map_mul, map_mul]; exact h6),
    hf (by rw [map_mul, map_mul]; exact h7)⟩

theorem isPGroup_sup_of_q16Q16 {G : Type*} [Group G] {x y x' y' : G} (h : Q16Q16 x y x' y') :
    IsPGroup 2 ↥((Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊔
      (Subgroup.zpowers x' ⊔ Subgroup.zpowers y')) := by
  obtain ⟨h1, h2, -, hxx', hxy', hyx', hyy'⟩ := h
  have hA1 := isPGroup_sup_of_q16Pair h1
  have hA2 := isPGroup_sup_of_q16Pair h2
  set A₁ := Subgroup.zpowers x ⊔ Subgroup.zpowers y with hA₁
  have hc1 : A₁ ≤ Subgroup.centralizer ({x'} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hxx'
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hyx'
  have hc2 : A₁ ≤ Subgroup.centralizer ({y'} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hxy'
    · rw [Subgroup.mem_centralizer_singleton_iff]; exact hyy'
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ Subgroup.zpowers x' ⊔ Subgroup.zpowers y', a * b = b * a := by
    intro a ha
    have hb : Subgroup.zpowers x' ⊔ Subgroup.zpowers y' ≤ Subgroup.centralizer ({a} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hc1 ha)).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 (hc2 ha)).symm
    intro b hbm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hb hbm)).symm
  have hN : (Subgroup.zpowers x' ⊔ Subgroup.zpowers y') ≤ Subgroup.normalizer (A₁ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro b hb a ha
    rw [show b * a * b⁻¹ = a by rw [← hcomm a ha b hb, mul_assoc, mul_inv_cancel, mul_one]]
    exact ha
  exact hA1.to_sup_of_normal_left' hA2 hN

theorem noQ16Q16_of_sylow {G : Type*} [Group G] [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index) (h : NoQ16Q16 P) : NoQ16Q16 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x y x' y' hq
  obtain ⟨T, hT⟩ := (isPGroup_sup_of_q16Q16 hq).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hP.toSylow hidx) T
  have hmem : ∀ z : G, z ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y) ⊔
      (Subgroup.zpowers x' ⊔ Subgroup.zpowers y') → g⁻¹ * z * g ∈ P := by
    intro z hz
    have hzT : z ∈ (T : Subgroup G) := hT hz
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hzT
    obtain ⟨s, hs, hsz⟩ := hzT
    have hs' : s = g⁻¹ * z * g := by
      rw [← hsz]
      simp [MulAut.conj_apply, mul_assoc]
    rw [← hs']
    exact hs
  have hx := hmem x (Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers x)))
  have hy := hmem y (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
  have hx' := hmem x' (Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers x')))
  have hy' := hmem y' (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers y')))
  have hq' : Q16Q16 (g⁻¹ * x * g) (g⁻¹ * y * g) (g⁻¹ * x' * g) (g⁻¹ * y' * g) := by
    have := Q16Q16.map (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective hq
    simpa [MulAut.conj_apply, inv_inv] using this
  exact h ⟨_, hx⟩ ⟨_, hy⟩ ⟨_, hx'⟩ ⟨_, hy'⟩ (Q16Q16.of_map P.subtype Subtype.val_injective hq')

theorem noQ16Q16_of_sylow_card {G : Type*} [Group G] [Finite G] {A Q : Subgroup G} (hQA : Q ≤ A)
    {k m : ℕ} (hk : Nat.card Q = 2 ^ k) (hm : ¬ 2 ∣ m) (hcard : 2 ^ k * m = Nat.card A)
    (h : NoQ16Q16 Q) : NoQ16Q16 A := by
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hk
  let e : Q.subgroupOf A ≃* Q := Subgroup.subgroupOfEquivOfLe hQA
  have hP : IsPGroup 2 (Q.subgroupOf A) := hQ.of_equiv e.symm
  have hcardP : Nat.card (Q.subgroupOf A) = 2 ^ k := by rw [Nat.card_congr e.toEquiv, hk]
  have hidx : (Q.subgroupOf A).index = m := by
    have h1 := Subgroup.card_mul_index (Q.subgroupOf A)
    rw [hcardP, ← hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  exact noQ16Q16_of_sylow hP (by rw [hidx]; exact hm)
    (NoQ16Q16.of_injective e.toMonoidHom e.injective h)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

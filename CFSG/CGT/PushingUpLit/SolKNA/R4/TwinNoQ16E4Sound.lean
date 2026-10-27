module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.SmallQ3Q16
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord wordPerm wordPerm_mem getElem!_map'
  letters_of_all mapWord_rep)

theorem Q16Pair.of_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {x y : G} (h : Q16Pair (f x) (f y)) : Q16Pair x y := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun e => h1 (by rw [← map_pow, e, map_one]),
    hf (by rw [map_pow, map_one]; exact h2), hf (by rw [map_pow, map_pow]; exact h3), hf ?_⟩
  simpa only [map_mul, map_inv] using h4

theorem isPGroup_sup_of_q16Pair {G : Type*} [Group G] {x y : G} (h : Q16Pair x y) :
    IsPGroup 2 ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) := by
  obtain ⟨-, h8, hy2, hyx⟩ := h
  have hx : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card_dvd_pow (n := 3) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h8
  have hy : IsPGroup 2 ↥(Subgroup.zpowers y) := by
    refine IsPGroup.of_card_dvd_pow (n := 3) ?_
    rw [Nat.card_zpowers]
    refine orderOf_dvd_of_pow_eq_one ?_
    calc y ^ 8 = (y ^ 2) ^ 4 := by rw [← pow_mul]
      _ = (x ^ 4) ^ 4 := by rw [hy2]
      _ = (x ^ 8) ^ 2 := by rw [← pow_mul, ← pow_mul]
      _ = 1 := by rw [h8, one_pow]
  have hyx' : y⁻¹ * x * y = x⁻¹ := by
    have h' : y * x⁻¹ * y⁻¹ = x := by
      rw [show y * x⁻¹ * y⁻¹ = (y * x * y⁻¹)⁻¹ by group, hyx, inv_inv]
    calc y⁻¹ * x * y = y⁻¹ * (y * x⁻¹ * y⁻¹) * y := by rw [h']
      _ = x⁻¹ := by group
  have hyN : y ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨k, rfl⟩
      refine ⟨-k, ?_⟩
      rw [← conj_zpow, hyx, inv_zpow']
    · rintro ⟨k, hk⟩
      refine ⟨-k, ?_⟩
      have hg : g = y⁻¹ * (y * g * y⁻¹) * y := by group
      have hconj : (y⁻¹ * x * y) ^ k = y⁻¹ * x ^ k * y := by
        simpa only [inv_inv] using (conj_zpow (a := y⁻¹) (b := x) (i := k))
      rw [hg, ← hk, ← hconj, hyx', inv_zpow']
  exact hx.to_sup_of_normal_left' hy (Subgroup.zpowers_le.2 hyN)

theorem noQ16_of_sylow {G : Type*} [Group G] [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index) (h : NoQ16 P) : NoQ16 G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x y hxy
  obtain ⟨T, hT⟩ := (isPGroup_sup_of_q16Pair hxy).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hP.toSylow hidx) T
  have hmem : ∀ z : G, z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y → g⁻¹ * z * g ∈ P := by
    intro z hz
    have hzT : z ∈ (T : Subgroup G) := hT hz
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hzT
    obtain ⟨s, hs, hsz⟩ := hzT
    have hs' : s = g⁻¹ * z * g := by
      rw [← hsz]
      simp [MulAut.conj_apply, mul_assoc]
    rw [← hs']
    exact hs
  have hx := hmem x (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
  have hy := hmem y (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hq : Q16Pair (g⁻¹ * x * g) (g⁻¹ * y * g) := by
    have := Q16Pair.map (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective hxy
    simpa [MulAut.conj_apply, inv_inv] using this
  exact h ⟨_, hx⟩ ⟨_, hy⟩ (Q16Pair.of_map P.subtype Subtype.val_injective hq)

theorem noQ16_of_sylow_card {G : Type*} [Group G] [Finite G] {A Q : Subgroup G} (hQA : Q ≤ A)
    {k m : ℕ} (hk : Nat.card Q = 2 ^ k) (hm : ¬ 2 ∣ m) (hcard : 2 ^ k * m = Nat.card A)
    (h : NoQ16 Q) : NoQ16 A := by
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hk
  let e : Q.subgroupOf A ≃* Q := Subgroup.subgroupOfEquivOfLe hQA
  have hP : IsPGroup 2 (Q.subgroupOf A) := hQ.of_equiv e.symm
  have hcardP : Nat.card (Q.subgroupOf A) = 2 ^ k := by rw [Nat.card_congr e.toEquiv, hk]
  have hidx : (Q.subgroupOf A).index = m := by
    have h1 := Subgroup.card_mul_index (Q.subgroupOf A)
    rw [hcardP, ← hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  exact noQ16_of_sylow hP (by rw [hidx]; exact hm) (NoQ16.of_injective e.toMonoidHom e.injective h)

end CFSG.CGT.PushingUpLit.SolKNA.R4

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup
open scoped Pointwise

theorem exists_normalizer_lift {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) (Pb : Subgroup (X ⧸ N)) (P : Subgroup X) (hP2 : IsPGroup 2 P)
    (hPmap : P.map (QuotientGroup.mk' N) = Pb)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y)
    (kb : X ⧸ N) (hk : kb ∈ normalizer (Pb : Set (X ⧸ N))) :
    ∃ ν ∈ normalizer (P : Set X), QuotientGroup.mk' N ν = kb := by
  classical
  obtain ⟨k', hk'⟩ := QuotientGroup.mk'_surjective N kb
  let N₁ : Subgroup X := Pb.comap (QuotientGroup.mk' N)
  have hmemN₁ : ∀ x, x ∈ N₁ ↔ QuotientGroup.mk' N x ∈ Pb := fun x => Iff.rfl
  let Q : Subgroup X := P.map (MulAut.conj k').toMonoidHom
  have hPN₁ : P ≤ N₁ := fun x hx => by
    rw [hmemN₁, ← hPmap]; exact mem_map_of_mem _ hx
  have hQN₁ : Q ≤ N₁ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hmemN₁]
    have h1 : QuotientGroup.mk' N x ∈ Pb := by rw [← hPmap]; exact mem_map_of_mem _ hx
    have h2 := (Subgroup.mem_normalizer_iff.mp hk (QuotientGroup.mk' N x)).mp h1
    simpa [MulAut.conj_apply, map_mul, map_inv, hk'] using h2
  have hNN₁ : N ≤ N₁ := fun x hx => by
    rw [hmemN₁]
    have h1 : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]; exact Pb.one_mem
  have hcardP : Nat.card P = Nat.card Pb := by
    have hinj' : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := by
      intro x y hxy
      exact Subtype.ext (hinj x x.2 y y.2 hxy)
    have : ((QuotientGroup.mk' N).comp P.subtype).range = Pb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hPmap]
    rw [← this]
    exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
  have hcardN₁ : Nat.card N₁ = Nat.card N * Nat.card Pb := by
    let f : ↥N₁ →* X ⧸ N := (QuotientGroup.mk' N).comp N₁.subtype
    have hrange : f.range = Pb := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [Subgroup.map_comap_eq]
      simp [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]
    have hker : f.ker = N.subgroupOf N₁ := by
      ext ⟨x, hx⟩
      simp [f, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have h1 := Subgroup.card_ker_mul_card_range f
    rw [hrange, hker] at h1
    rw [← h1]
    congr 1
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNN₁).toEquiv
  have hcardQ : Nat.card Q = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj k').injective
  let P' : Subgroup ↥N₁ := P.subgroupOf N₁
  let Q' : Subgroup ↥N₁ := Q.subgroupOf N₁
  have hP'2 : IsPGroup 2 ↥P' := IsPGroup.of_equiv hP2 (Subgroup.subgroupOfEquivOfLe hPN₁).symm
  have hQ2 : IsPGroup 2 Q := hP2.map (MulAut.conj k').toMonoidHom
  have hQ'2 : IsPGroup 2 ↥Q' := IsPGroup.of_equiv hQ2 (Subgroup.subgroupOfEquivOfLe hQN₁).symm
  have hP'card : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN₁).toEquiv
  have hQ'card : Nat.card Q' = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN₁).toEquiv
  have hpos : 0 < Nat.card Pb := Nat.card_pos
  have hP'idx : P'.index = Nat.card N := by
    have h1 := Subgroup.card_mul_index P'
    rw [hP'card, hcardP, hcardN₁] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  have hQ'idx : Q'.index = Nat.card N := by
    have h1 := Subgroup.card_mul_index Q'
    rw [hQ'card, hcardQ, hcardP, hcardN₁] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  have hNodd : ¬ 2 ∣ Nat.card N := by
    intro h; exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)
  obtain ⟨n, hn⟩ := exists_conj_of_odd_index hP'2 hQ'2 (by rw [hP'idx]; exact hNodd)
    (by rw [hQ'idx]; exact hNodd)
  have hconj1 : ∀ y ∈ Q, ((n : X)⁻¹ * y * n) ∈ P := by
    intro y hy
    have := (hn ⟨y, hQN₁ hy⟩).mp (Subgroup.mem_subgroupOf.mpr hy)
    exact Subgroup.mem_subgroupOf.mp this
  have hconj2 : ∀ x ∈ P, (n : X) * x * (n : X)⁻¹ ∈ Q := by
    intro x hx
    have hxN₁ : (n : X) * x * (n : X)⁻¹ ∈ N₁ :=
      N₁.mul_mem (N₁.mul_mem n.2 (hPN₁ hx)) (N₁.inv_mem n.2)
    have := (hn ⟨(n : X) * x * (n : X)⁻¹, hxN₁⟩).mpr (by
      refine Subgroup.mem_subgroupOf.mpr ?_
      simpa [mul_assoc] using hx)
    exact Subgroup.mem_subgroupOf.mp this
  let ν₀ : X := (n : X)⁻¹ * k'
  have hν₀ : ν₀ ∈ normalizer (P : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hcalc : ν₀ * x * ν₀⁻¹ = (n : X)⁻¹ * (k' * x * k'⁻¹) * n := by simp [ν₀, mul_assoc]
    rw [hcalc]
    constructor
    · intro hx
      exact hconj1 _ ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · intro hx
      have h1 := hconj2 _ hx
      have h2 : k' * x * k'⁻¹ ∈ Q := by simpa [mul_assoc] using h1
      obtain ⟨y, hy, hyy⟩ := h2
      have : y = x := by simpa [MulAut.conj_apply] using hyy
      rw [← this]; exact hy
  have hnPb : QuotientGroup.mk' N (n : X) ∈ Pb := n.2
  rw [← hPmap] at hnPb
  obtain ⟨p, hpP, hp⟩ := Subgroup.mem_map.mp hnPb
  refine ⟨p * ν₀, Subgroup.mul_mem _ (Subgroup.le_normalizer hpP) hν₀, ?_⟩
  simp [ν₀, map_mul, map_inv, hp, hk']

theorem inj_mk_of_pgroup {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) {P : Subgroup X} (hP2 : IsPGroup 2 P) :
    ∀ x ∈ P, ∀ y ∈ P, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y := by
  intro x hx y hy hxy
  have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
  have h2 : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
  have := eq_one_of_pgroup_of_odd hP2 hN h2 h1
  exact inv_mul_eq_one.mp this

theorem lift_two_subgroup {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Odd (Nat.card N)) (Pb : Subgroup (X ⧸ N)) (hPb : IsPGroup 2 Pb) :
    ∃ P : Subgroup X, IsPGroup 2 P ∧ P.map (QuotientGroup.mk' N) = Pb ∧
      (∀ x ∈ P, ∀ y ∈ P, QuotientGroup.mk' N x = QuotientGroup.mk' N y → x = y) ∧
      ∀ kb ∈ normalizer (Pb : Set (X ⧸ N)), ∃ ν ∈ normalizer (P : Set X), QuotientGroup.mk' N ν = kb := by
  obtain ⟨P, hP2, hPmap⟩ := CFSG.GH74.Generic.exists_lift_twoSubgroup N Pb hPb
  have hinj := inj_mk_of_pgroup N hN hP2
  exact ⟨P, hP2, hPmap, hinj, fun kb hk => exists_normalizer_lift N hN Pb P hP2 hPmap hinj kb hk⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

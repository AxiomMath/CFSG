module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.ExtremalNotInM0
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

omit [Finite G] in
private theorem map_conj_inv_le_and_normal {h : G} {S Y : Subgroup G}
    (hYS : Y ≤ S.map (MulAut.conj h).toMonoidHom)
    (hYn : ∀ s ∈ S.map (MulAut.conj h).toMonoidHom, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) :
    (Y.map (MulAut.conj h⁻¹).toMonoidHom ≤ S) ∧
      (∀ s ∈ S, ∀ y ∈ Y.map (MulAut.conj h⁻¹).toMonoidHom,
        s * y * s⁻¹ ∈ Y.map (MulAut.conj h⁻¹).toMonoidHom) := by
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hYS hy
    have hEq : (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom s) = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [hEq]
  · intro s hs y hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hs' : (MulAut.conj h).toMonoidHom s ∈ S.map (MulAut.conj h).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hs
    have hc := hYn ((MulAut.conj h).toMonoidHom s) hs' y₀ hy₀
    refine ⟨(MulAut.conj h).toMonoidHom s * y₀ * ((MulAut.conj h).toMonoidHom s)⁻¹, hc, ?_⟩
    have hEq : (MulAut.conj h⁻¹).toMonoidHom
        ((MulAut.conj h).toMonoidHom s * y₀ * ((MulAut.conj h).toMonoidHom s)⁻¹)
        = s * (MulAut.conj h⁻¹).toMonoidHom y₀ * s⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [hEq]

theorem ThLocalIn.map_A_le_of_normal_map (W : ThLocalIn L S A B z) (h : G) {Y : Subgroup G}
    (hYS : Y ≤ S.map (MulAut.conj h).toMonoidHom)
    (hYn : ∀ s ∈ S.map (MulAut.conj h).toMonoidHom, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y)
    (hY : 16 ≤ Nat.card Y) : A.map (MulAut.conj h).toMonoidHom ≤ Y := by
  obtain ⟨hY'S, hY'n⟩ := map_conj_inv_le_and_normal hYS hYn
  have hY' : 16 ≤ Nat.card ↥(Y.map (MulAut.conj h⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective]
    exact hY
  have hA := W.A_le_of_normal hY'S hY'n hY'
  intro a ha
  obtain ⟨a₀, ha₀, rfl⟩ := ha
  obtain ⟨y, hy, hyeq⟩ := hA ha₀
  have hconj : (MulAut.conj h).toMonoidHom ((MulAut.conj h⁻¹).toMonoidHom y) = y := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [← hyeq, hconj]
  exact hy

omit [Finite G] in
private theorem mem_or_mul_mem_of_mem_sup_zpowers {X : Subgroup G} {u x : G} (hu2 : u ^ 2 = 1)
    (hcomm : ∀ a ∈ X, a * u = u * a) (hx : x ∈ X ⊔ zpowers u) : x ∈ X ∨ x * u ∈ X := by
  have hcomm' : ∀ a ∈ X, ∀ b ∈ zpowers u, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a u from hcomm a ha) k).eq
  obtain ⟨y, hy, r, hr, hxy⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcomm' hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  rcases zpow_eq_one_or_self hu2 k with h | h
  · left
    rw [h, mul_one] at hxy
    rwa [← hxy]
  · right
    rw [h] at hxy
    rw [← hxy, mul_assoc, ← sq, hu2, mul_one]
    exact hy

theorem ThCyc.conj_mem_omega1_of_mem_A (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) {T : Subgroup G} (hT : IsPGroup 2 T)
    (hTM : T ≤ normalizer (D : Set G)) (hDT : D ≤ T) {g : G} (hu : g⁻¹ * t * g ∈ T)
    (hSg : ∀ s ∈ S, g⁻¹ * s * g ∈ T) : ∀ a ∈ A, g⁻¹ * a * g ∈ omega1 D hD.comm := by
  classical
  intro a ha
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  let V : Subgroup G := omega1 D hD.comm
  let X : Subgroup G := V ⊓ centralizer ({g⁻¹ * t * g} : Set G)
  have hu2 : (g⁻¹ * t * g) ^ 2 = 1 := H.conj_sq g
  have huNV : g⁻¹ * t * g ∈ normalizer (V : Set G) :=
    ThCyc.normalizer_D_le_normalizer_omega1 hD (hTM hu)
  have hVcard : Nat.card V = 2 ^ 8 := H.card_omega1 W W2 hD hsq
  haveI hVele : IsElementaryAbelian 2 V :=
    IsElementaryAbelian.two_of_forall_mul_self
      (fun x hx y hy => H.omega1_comm W W2 hD hx hy)
      (fun x hx => by simpa [pow_two] using hx.2)
  have hVsq := CFSG.GroupTheory.card_le_card_inf_centralizer_sq (Y := V)
    (x := g⁻¹ * t * g) huNV (by rw [hu2]; exact Subgroup.one_mem _)
  have hX16 : 16 ≤ Nat.card X := by
    rw [hVcard] at hVsq
    dsimp only [X, V] at hVsq ⊢
    nlinarith
  obtain ⟨Y, hYle, hYleS', hYn, hYcard, -, -⟩ :=
    H.exists_elementary_normal_inf W W2 hD F hT hTM hDT hu hSg
  have hY16 : 16 ≤ Nat.card Y := by
    rw [hYcard]
    exact hX16
  have hA' : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ Y :=
    ThLocalIn.map_A_le_of_normal_map W (g⁻¹) hYleS' hYn hY16
  have haY : (MulAut.conj g⁻¹).toMonoidHom a ∈ Y :=
    hA' (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom ha)
  have haY' : g⁻¹ * a * g ∈ Y := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using haY
  have hxsup : g⁻¹ * a * g ∈ X ⊔ zpowers (g⁻¹ * t * g) :=
    (hYle.trans inf_le_left) haY'
  have hXcomm : ∀ x ∈ X, x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := by
    intro x hx
    dsimp only [X] at hx
    exact mem_centralizer_singleton_iff.1 hx.2
  rcases mem_or_mul_mem_of_mem_sup_zpowers hu2 hXcomm hxsup with hx | hx
  · dsimp only [X, V] at hx ⊢
    exact hx.1
  · exfalso
    have hxV : (g⁻¹ * a * g) * (g⁻¹ * t * g) ∈ omega1 D hD.comm := by
      dsimp only [X, V] at hx
      exact hx.1
    obtain ⟨v, hv, hva⟩ := H.thV_surj W W2 hD hsq a ha
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (H.omega1_mul_self W W2 hD hv)
    have hat : a * t = v * t * v := by
      rw [← hva]
      simp only [thV]
      group
    have hh : (v⁻¹ * g)⁻¹ * t * (v⁻¹ * g) =
        (g⁻¹ * a * g) * (g⁻¹ * t * g) := by
      calc (v⁻¹ * g)⁻¹ * t * (v⁻¹ * g)
          = g⁻¹ * (v * t * v⁻¹) * g := by group
        _ = g⁻¹ * (v * t * v) * g := by rw [hvi]
        _ = g⁻¹ * (a * t) * g := by rw [← hat]
        _ = (g⁻¹ * a * g) * (g⁻¹ * t * g) := by group
    refine H.conj_not_mem_omega1 hD F (v⁻¹ * g) ?_
    rw [hh]
    exact hxV

end CFSG.EvenSporadicStandard.ThStd

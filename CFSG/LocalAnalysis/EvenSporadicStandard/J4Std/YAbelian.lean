module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.YQuad
public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Interface

public section

namespace CFSG.EvenSporadicStandard.J4Std.YExists

open Subgroup

variable {G : Type} [Group G]

structure YFacts (L U : Subgroup G) (phi : G → G) (Y : Subgroup G) : Prop where
  U_le : U ≤ Y
  central : ∀ y ∈ Y, ∀ u ∈ U, y * u = u * y
  sq_mem : ∀ y ∈ Y, y * y ∈ U
  phi_mem : ∀ y ∈ Y, phi y ∈ U
  phi_mul : ∀ y ∈ Y, ∀ y' ∈ Y, phi (y * y') = phi y * phi y'
  phi_ker : ∀ y ∈ Y, phi y = 1 → y ∈ U
  phi_surj : ∀ u ∈ U, ∃ y ∈ Y, phi y = u
  phi_conj : ∀ h ∈ Hloc L U, ∀ y ∈ Y,
    h * y * h⁻¹ ∈ Y ∧ phi (h * y * h⁻¹) = h * phi y * h⁻¹

structure IsSect (U Y : Subgroup G) (phi η : G → G) : Prop where
  mem : ∀ u ∈ U, η u ∈ Y
  phi_eq : ∀ u ∈ U, phi (η u) = u

section Orbit

variable {L U : Subgroup G}

theorem hOrbit_symm {x y : G} (h : y ∈ hOrbit L U x) : x ∈ hOrbit L U y := by
  obtain ⟨g, hg, rfl⟩ := h
  exact ⟨g⁻¹, inv_mem hg, by group⟩

theorem hOrbit_trans {x y w : G} (h1 : y ∈ hOrbit L U x) (h2 : w ∈ hOrbit L U y) :
    w ∈ hOrbit L U x := by
  obtain ⟨g, hg, rfl⟩ := h1
  obtain ⟨g', hg', rfl⟩ := h2
  exact ⟨g' * g, mul_mem hg' hg, by group⟩

theorem ne_one_of_mem_hOrbit {x y : G} (hx : x ≠ 1) (h : y ∈ hOrbit L U x) : y ≠ 1 := by
  obtain ⟨g, hg, rfl⟩ := h
  intro h1
  apply hx
  have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [this, h1]
  group

theorem orbit_cover {T0 : Subgroup G} (hD : LocalData L U T0) {a d : G} (ha : a ∈ U) (hd : d ∈ U)
    (ha1 : a ≠ 1) (hd1 : d ≠ 1) (hda : d ∉ hOrbit L U a) {u : G} (hu : u ∈ U) (hu1 : u ≠ 1) :
    u ∈ hOrbit L U a ∨ u ∈ hOrbit L U d := by
  obtain ⟨a', b', -, -, -, -, -, hcov, -, -⟩ := hD.orbits
  have hnot : ∀ p, a ∈ hOrbit L U p → d ∈ hOrbit L U p → False := fun p h1 h2 =>
    hda (hOrbit_trans (hOrbit_symm h1) h2)
  rcases hcov u hu hu1 with huO | huO <;> rcases hcov a ha ha1 with haO | haO <;>
    rcases hcov d hd hd1 with hdO | hdO <;>
    first
    | exact Or.inl (hOrbit_trans (hOrbit_symm haO) huO)
    | exact Or.inr (hOrbit_trans (hOrbit_symm hdO) huO)
    | exact (hnot _ haO hdO).elim

end Orbit

section Sect

variable {L U T0 Y : Subgroup G} {phi η : G → G}

theorem sq_eq_of_phi_eq (hD : LocalData L U T0) (hF : YFacts L U phi Y) {y y' : G} (hy : y ∈ Y)
    (hy' : y' ∈ Y) (h : phi y = phi y') : y * y = y' * y' := by
  have ht : y⁻¹ * y' ∈ Y := Y.mul_mem (Y.inv_mem hy) hy'
  have hmul := hF.phi_mul y hy _ ht
  rw [mul_inv_cancel_left] at hmul
  have h1 : phi (y⁻¹ * y') = 1 := by
    have : phi y * phi (y⁻¹ * y') = phi y * 1 := by rw [← hmul, ← h, mul_one]
    exact mul_left_cancel this
  have htU : y⁻¹ * y' ∈ U := hF.phi_ker _ ht h1
  obtain ⟨t, ht', rfl⟩ : ∃ t ∈ U, y' = y * t := ⟨y⁻¹ * y', htU, by group⟩
  have hc := hF.central y hy t ht'
  calc y * y = y * y * (t * t) := by rw [hD.U_sq t ht', mul_one]
    _ = y * (y * t) * t := by group
    _ = y * (t * y) * t := by rw [hc]
    _ = (y * t) * (y * t) := by group

theorem sect_sq (hD : LocalData L U T0) (hF : YFacts L U phi Y) (hη : IsSect U Y phi η) {y : G}
    (hy : y ∈ Y) : η (phi y) * η (phi y) = y * y :=
  sq_eq_of_phi_eq hD hF (hη.mem _ (hF.phi_mem y hy)) hy (hη.phi_eq _ (hF.phi_mem y hy))

theorem sect_sq_fix (hD : LocalData L U T0) (hF : YFacts L U phi Y) (hη : IsSect U Y phi η)
    (hfix : FixData L U) {x : G} (hx : x ∈ U) (hx1 : x ≠ 1) :
    η x * η x = 1 ∨ η x * η x = x := by
  have hy := hη.mem x hx
  refine hfix x hx hx1 (η x * η x) (hF.sq_mem _ hy) (fun h hh hhx => ?_)
  obtain ⟨hhY, hphi⟩ := hF.phi_conj h hh (η x) hy
  rw [hη.phi_eq x hx, hhx] at hphi
  have hsq := sq_eq_of_phi_eq hD hF hhY hy (by rw [hphi, hη.phi_eq x hx])
  calc h * (η x * η x) * h⁻¹ = (h * η x * h⁻¹) * (h * η x * h⁻¹) := by group
    _ = η x * η x := hsq

theorem sect_sq_conj (hD : LocalData L U T0) (hF : YFacts L U phi Y) (hη : IsSect U Y phi η)
    {h x : G} (hh : h ∈ Hloc L U) (hx : x ∈ U) :
    η (h * x * h⁻¹) * η (h * x * h⁻¹) = h * (η x * η x) * h⁻¹ := by
  obtain ⟨hhY, hphi⟩ := hF.phi_conj h hh (η x) (hη.mem x hx)
  rw [hη.phi_eq x hx] at hphi
  have := sect_sq hD hF hη hhY
  rw [hphi] at this
  rw [this]
  group

theorem typ_iff_of_mem_hOrbit (hD : LocalData L U T0) (hF : YFacts L U phi Y)
    (hη : IsSect U Y phi η) {x x' : G} (hx : x ∈ U) (hx' : x' ∈ hOrbit L U x) :
    η x' * η x' = x' ↔ η x * η x = x := by
  obtain ⟨h, hh, rfl⟩ := hx'
  rw [sect_sq_conj hD hF hη hh hx]
  constructor
  · intro e
    have e' : h * (η x * η x) * h⁻¹ = h * x * h⁻¹ := e
    exact mul_left_cancel (mul_right_cancel e')
  · intro e
    rw [e]

theorem sect_poly3 (hD : LocalData L U T0) (hF : YFacts L U phi Y) (hη : IsSect U Y phi η)
    {x y w : G} (hx : x ∈ U) (hy : y ∈ U) (hw : w ∈ U) :
    η (x * y * w) * η (x * y * w) * (η (x * y) * η (x * y)) * (η (x * w) * η (x * w)) *
      (η (y * w) * η (y * w)) * (η x * η x) * (η y * η y) * (η w * η w) = 1 := by
  have hex := hη.mem x hx
  have hey := hη.mem y hy
  have hew := hη.mem w hw
  have pxy : phi (η x * η y) = x * y := by
    rw [hF.phi_mul _ hex _ hey, hη.phi_eq x hx, hη.phi_eq y hy]
  have pxw : phi (η x * η w) = x * w := by
    rw [hF.phi_mul _ hex _ hew, hη.phi_eq x hx, hη.phi_eq w hw]
  have pyw : phi (η y * η w) = y * w := by
    rw [hF.phi_mul _ hey _ hew, hη.phi_eq y hy, hη.phi_eq w hw]
  have pxyw : phi (η x * η y * η w) = x * y * w := by
    rw [hF.phi_mul _ (Y.mul_mem hex hey) _ hew, pxy, hη.phi_eq w hw]
  have e1 := sect_sq hD hF hη (Y.mul_mem (Y.mul_mem hex hey) hew)
  have e2 := sect_sq hD hF hη (Y.mul_mem hex hey)
  have e3 := sect_sq hD hF hη (Y.mul_mem hex hew)
  have e4 := sect_sq hD hF hη (Y.mul_mem hey hew)
  rw [pxyw] at e1
  rw [pxy] at e2
  rw [pxw] at e3
  rw [pyw] at e4
  rw [e1, e2, e3, e4]
  exact (⟨hF.U_le, hF.central, hD.U_sq, hF.sq_mem⟩ : CentralSq Y U).poly3 hex hey hew

end Sect

theorem Y_sq_dichotomy {L U T0 Y : Subgroup G} {phi : G → G} (hD : LocalData L U T0)
    (hF : YFacts L U phi Y) (hfix : FixData L U) (htriple : TripleData L U) :
    (∀ y ∈ Y, y * y = 1) ∨ ∀ y ∈ Y, y * y = phi y := by
  choose! η hηY hηphi using hF.phi_surj
  have hη : IsSect U Y phi η := ⟨hηY, hηphi⟩
  obtain ⟨a, ha, b, hb, c, hc, ha1, hab1, hbO, hcO, hbcO, habO, hacO, habcO⟩ := htriple
  have hb1 : b ≠ 1 := ne_one_of_mem_hOrbit ha1 hbO
  have hc1 : c ≠ 1 := ne_one_of_mem_hOrbit ha1 hcO
  have hbc1 : b * c ≠ 1 := ne_one_of_mem_hOrbit ha1 hbcO
  have hac1 : a * c ≠ 1 := ne_one_of_mem_hOrbit hab1 hacO
  have habc1 : a * b * c ≠ 1 := ne_one_of_mem_hOrbit hab1 habcO
  have hab : a * b ∈ U := U.mul_mem ha hb
  have key : η a * η a = a ↔ η (a * b) * η (a * b) = a * b :=
    typ_iff_of_triple hD.U_comm hD.U_sq (fun x => η x * η x)
      (fun x hx hx1 => sect_sq_fix hD hF hη hfix hx hx1)
      (fun x hx y hy w hw => sect_poly3 hD hF hη hx hy hw) ha hb hc ha1 hab1 hac1 habc1
      (typ_iff_of_mem_hOrbit hD hF hη ha hbO) (typ_iff_of_mem_hOrbit hD hF hη ha hcO)
      (typ_iff_of_mem_hOrbit hD hF hη ha hbcO) (typ_iff_of_mem_hOrbit hD hF hη hab hacO)
      (typ_iff_of_mem_hOrbit hD hF hη hab habcO) hb1 hc1 hbc1
  have hconst : ∀ x ∈ U, x ≠ 1 → (η x * η x = x ↔ η a * η a = a) := by
    intro x hx hx1
    rcases orbit_cover hD ha hab ha1 hab1 habO hx hx1 with hxO | hxO
    · exact typ_iff_of_mem_hOrbit hD hF hη ha hxO
    · exact (typ_iff_of_mem_hOrbit hD hF hη hab hxO).trans key.symm
  by_cases hT : η a * η a = a
  · right
    intro y hy
    by_cases hy1 : phi y = 1
    · rw [hy1]
      exact hD.U_sq y (hF.phi_ker y hy hy1)
    · exact (sect_sq hD hF hη hy).symm.trans ((hconst _ (hF.phi_mem y hy) hy1).2 hT)
  · left
    intro y hy
    by_cases hy1 : phi y = 1
    · exact hD.U_sq y (hF.phi_ker y hy hy1)
    · have hx := hF.phi_mem y hy
      rw [← sect_sq hD hF hη hy]
      rcases sect_sq_fix hD hF hη hfix hx hy1 with h | h
      · exact h
      · exact absurd ((hconst _ hx hy1).1 h) hT

theorem Y_abelian {L U T0 Y : Subgroup G} {phi : G → G} (hD : LocalData L U T0)
    (hF : YFacts L U phi Y) (hfix : FixData L U) (htriple : TripleData L U) :
    ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
  intro y hy y' hy'
  rcases Y_sq_dichotomy hD hF hfix htriple with hall | hall
  · have e1 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hall y hy)
    have e2 : y'⁻¹ = y' := inv_eq_of_mul_eq_one_right (hall y' hy')
    have e3 : (y * y')⁻¹ = y * y' := inv_eq_of_mul_eq_one_right (hall _ (Y.mul_mem hy hy'))
    calc y * y' = (y * y')⁻¹ := e3.symm
      _ = y' * y := by rw [mul_inv_rev, e1, e2]
  · have h1 := hall _ (Y.mul_mem hy hy')
    rw [hF.phi_mul y hy y' hy', ← hall y hy, ← hall y' hy'] at h1
    have h2 : y * (y' * y) * y' = y * (y * y') * y' := by
      calc y * (y' * y) * y' = y * y' * (y * y') := by group
        _ = y * y * (y' * y') := h1
        _ = y * (y * y') * y' := by group
    exact (mul_left_cancel (mul_right_cancel h2)).symm

end CFSG.EvenSporadicStandard.J4Std.YExists

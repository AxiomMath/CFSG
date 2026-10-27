module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 Subgroup

variable {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']

private lemma centEl_map_equiv (e : G ≃* G') (V : Subgroup G) (y : G) :
    centEl (V.map e.toMonoidHom) (e y) = (centEl V y).map e.toMonoidHom := by
  ext x
  simp only [centEl, Subgroup.mem_inf, Subgroup.mem_map_equiv,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxV, hx⟩
    exact ⟨hxV, by apply e.injective; rw [map_mul, map_mul, e.apply_symm_apply, hx]⟩
  · rintro ⟨hxV, hx⟩
    exact ⟨hxV, by rw [← e.apply_symm_apply x, ← map_mul, ← map_mul, hx]⟩

@[expose] noncomputable def G23Base.transport (e : G ≃* G') (b : G23Base G) : G23Base G' where
  L := b.L.map e.toMonoidHom
  normal := b.normal.map e.toMonoidHom e.surjective
  card_L := by rw [Subgroup.card_map_of_injective e.injective, b.card_L]
  card_G := by rw [Nat.card_congr e.toEquiv.symm, b.card_G]
  invol_conj := by
    intro u hu v hv
    obtain ⟨huL, hu2⟩ := hu
    obtain ⟨hvL, hv2⟩ := hv
    have huL' : e.symm u ∈ b.L := Subgroup.mem_map_equiv.mp huL
    have hvL' : e.symm v ∈ b.L := Subgroup.mem_map_equiv.mp hvL
    have hu2' : orderOf (e.symm u) = 2 := by
      rw [← MulEquiv.orderOf_eq e (e.symm u), e.apply_symm_apply]; exact hu2
    have hv2' : orderOf (e.symm v) = 2 := by
      rw [← MulEquiv.orderOf_eq e (e.symm v), e.apply_symm_apply]; exact hv2
    obtain ⟨l, hl, hvl⟩ := b.invol_conj (e.symm u) ⟨huL', hu2'⟩ (e.symm v) ⟨hvL', hv2'⟩
    refine ⟨e l, Subgroup.mem_map_of_mem e.toMonoidHom hl, ?_⟩
    rw [← e.apply_symm_apply v, ← e.apply_symm_apply u, hvl]
    simp [map_mul]
  card_cent := by
    intro u hu
    obtain ⟨huL, hu2⟩ := hu
    have huL' : e.symm u ∈ b.L := Subgroup.mem_map_equiv.mp huL
    have hu2' : orderOf (e.symm u) = 2 := by
      rw [← MulEquiv.orderOf_eq e (e.symm u), e.apply_symm_apply]; exact hu2
    rw [← e.apply_symm_apply u, centEl_map_equiv e b.L (e.symm u),
      Subgroup.card_map_of_injective e.injective]
    exact b.card_cent (e.symm u) ⟨huL', hu2'⟩
  cent_outer := by
    intro τ hτ hτ2
    have hτL : e.symm τ ∉ b.L := by
      intro h
      exact hτ (by simpa using Subgroup.mem_map_of_mem e.toMonoidHom h)
    have hτ2' : e.symm τ * e.symm τ = 1 := by
      apply e.injective
      rw [map_mul, e.apply_symm_apply, hτ2, map_one]
    obtain ⟨φ⟩ := b.cent_outer (e.symm τ) hτL hτ2'
    have heq : (centEl b.L (e.symm τ)).map e.toMonoidHom = centEl (b.L.map e.toMonoidHom) τ := by
      rw [← centEl_map_equiv e b.L (e.symm τ), e.apply_symm_apply]
    exact ⟨(MulEquiv.subgroupCongr heq).symm.trans
      ((MulEquiv.subgroupMap e (centEl b.L (e.symm τ))).symm.trans φ)⟩

@[expose] noncomputable def G23Model.transport (e : G ≃* G') (m : G23Model G) : G23Model G' where
  toG23Base := m.toG23Base.transport e
  ρ := m.ρ.comp e.symm.toMonoidHom
  inj := m.inj.comp e.symm.injective
  gX0 := e m.gX0
  gX1 := e m.gX1
  gY0 := e m.gY0
  gY1 := e m.gY1
  gS := e m.gS
  gX0_mem := Subgroup.mem_map_of_mem e.toMonoidHom m.gX0_mem
  gX1_mem := Subgroup.mem_map_of_mem e.toMonoidHom m.gX1_mem
  gY0_mem := Subgroup.mem_map_of_mem e.toMonoidHom m.gY0_mem
  gY1_mem := Subgroup.mem_map_of_mem e.toMonoidHom m.gY1_mem
  gS_not_mem := fun h => m.gS_not_mem ((Subgroup.mem_map_iff_mem e.injective).mp h)
  gS_sq := by rw [← map_mul, m.gS_sq, map_one]
  ρ_gX0 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
    exact m.ρ_gX0
  ρ_gX1 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
    exact m.ρ_gX1
  ρ_gY0 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
    exact m.ρ_gY0
  ρ_gY1 := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
    exact m.ρ_gY1
  ρ_gS := by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.symm_apply_apply]
    exact m.ρ_gS

theorem G23Model.transport_L (e : G ≃* G') (m : G23Model G) :
    (m.transport e).L = m.L.map e.toMonoidHom :=
  rfl

private lemma mulAut_congr_conj {Q N : Type} [Group Q] [Group N] (ε : Q ≃* N) (q : Q) :
    MulAut.congr ε (MulAut.conj q) = MulAut.conj (ε q) := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
    ε.apply_symm_apply]

private lemma mulAut_congr_symm_conj {Q N : Type} [Group Q] [Group N] (ε : Q ≃* N) (n : N) :
    (MulAut.congr ε).symm.toMonoidHom (MulAut.conj n) = MulAut.conj (ε.symm n) := by
  have h : MulAut.congr ε (MulAut.conj (ε.symm n)) = MulAut.conj n := by
    rw [mulAut_congr_conj, ε.apply_symm_apply]
  rw [← h, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem innerAut_map_congr {Q N : Type} [Group Q] [Group N] (ε : Q ≃* N) :
    (innerAut N).map (MulAut.congr ε).symm.toMonoidHom = innerAut Q := by
  ext α
  simp only [Subgroup.mem_map, innerAut, MonoidHom.mem_range]
  constructor
  · rintro ⟨β, ⟨n, rfl⟩, hβ⟩
    exact ⟨ε.symm n, by rw [← hβ, mulAut_congr_symm_conj]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨MulAut.conj (ε q), ⟨ε q, rfl⟩, by rw [mulAut_congr_symm_conj, ε.symm_apply_apply]⟩

end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

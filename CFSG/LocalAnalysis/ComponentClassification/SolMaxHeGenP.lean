module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxHeGenB

public section

namespace CFSG.ComponentClassification.SolMax.HeGen

open CFSG.Sporadic.HeldB Subgroup

theorem isCoatom_stabilizer_heP
    (ω : Fin 8330) : IsCoatom (MulAction.stabilizer heP ω) := by
  have := CFSG.Sporadic.He.isPreprimitive
  have hJ := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    CFSG.Sporadic.He.J (heBridgePerm ω)
  have hst : ∀ g : CFSG.Sporadic.He.J,
      g ∈ MulAction.stabilizer CFSG.Sporadic.He.J (heBridgePerm ω) ↔ heJToP g ω = ω := fun g => by
    rw [MulAction.mem_stabilizer_iff, heJToP_apply, Equiv.Perm.inv_eq_iff_eq]
  have hmem : ∀ g : CFSG.Sporadic.He.J, heJToP g ∈ heP := fun g =>
    heJToP_range ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩
  have hsurj : ∀ p ∈ heP, ∃ g, heJToP g = p := fun p hp =>
    MonoidHom.mem_range.1 (heJToP_range.symm ▸ hp)
  have hstP : ∀ p : heP, p ∈ MulAction.stabilizer heP ω ↔ (p : Equiv.Perm (Fin 8330)) ω = ω :=
    fun p => by rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Equiv.Perm.smul_def]
  refine ⟨fun htop => hJ.1 ?_, fun M hM => ?_⟩
  · rw [eq_top_iff]
    intro g _
    rw [hst]
    have h1 : (⟨heJToP g, hmem g⟩ : heP) ∈ MulAction.stabilizer heP ω := htop ▸ mem_top _
    exact (hstP _).1 h1
  · have hle : MulAction.stabilizer CFSG.Sporadic.He.J (heBridgePerm ω) ≤
        (M.map heP.subtype).comap heJToP := fun g hg => by
      rw [mem_comap]
      exact mem_map.2 ⟨⟨heJToP g, hmem g⟩, hM.le ((hstP _).2 ((hst g).1 hg)), rfl⟩
    have hne : MulAction.stabilizer CFSG.Sporadic.He.J (heBridgePerm ω) ≠
        (M.map heP.subtype).comap heJToP := by
      obtain ⟨p, hpM, hpS⟩ := IsConcreteLE.exists_of_lt hM
      obtain ⟨g, hg⟩ := hsurj p p.2
      intro h
      apply hpS
      have hgM : g ∈ (M.map heP.subtype).comap heJToP := by
        rw [mem_comap, hg]
        exact mem_map_of_mem _ hpM
      rw [← h, hst, hg] at hgM
      exact (hstP p).2 hgM
    have htop := hJ.2 _ (lt_of_le_of_ne hle hne)
    rw [eq_top_iff]
    intro p _
    obtain ⟨g, hg⟩ := hsurj p p.2
    have hg' : g ∈ (M.map heP.subtype).comap heJToP := htop ▸ mem_top g
    rw [mem_comap, hg] at hg'
    obtain ⟨q, hq, hqp⟩ := mem_map.1 hg'
    have : q = p := Subtype.ext hqp
    rwa [this] at hq

theorem heOuterD_le_heP :
    heOuterD ≤ heP :=
  heOuterD_le_C.trans (heOuterC_le_centralizer.trans inf_le_left)

theorem heOuterD_sup_normalizer :
    heOuterD ⊔ (heP ⊓ normalizer (heGenF0 : Set (Equiv.Perm (Fin 8330)))) = heP := by
  have hco := isCoatom_stabilizer_heP heGenOmega0
  set M := heOuterD ⊔ (heP ⊓ normalizer (heGenF0 : Set (Equiv.Perm (Fin 8330)))) with hM
  have hMP : M ≤ heP := sup_le heOuterD_le_heP inf_le_left
  have hstab : MulAction.stabilizer heP heGenOmega0 ≤ M.subgroupOf heP := by
    intro p hp
    rw [mem_subgroupOf]
    exact mem_sup_right
      (mem_inf.2 ⟨p.2, stab_le_normalizer p.2 (MulAction.mem_stabilizer_iff.1 hp)⟩)
  have hd2 : heOuterDGen 2 ∈ heOuterD := heOuterDGen_mem_D 2 (by norm_num)
  have hd : (⟨heOuterDGen 2, heOuterD_le_heP hd2⟩ : heP) ∈ M.subgroupOf heP :=
    mem_subgroupOf.2 (mem_sup_left hd2)
  have hdn : (⟨heOuterDGen 2, heOuterD_le_heP hd2⟩ : heP) ∉
      MulAction.stabilizer heP heGenOmega0 := by
    rw [MulAction.mem_stabilizer_iff]
    exact heGenD3_moves
  have htop : M.subgroupOf heP = ⊤ :=
    hco.2 _ (lt_of_le_of_ne hstab fun h => hdn (h ▸ hd))
  refine le_antisymm hMP fun p hp => ?_
  have : (⟨p, hp⟩ : heP) ∈ M.subgroupOf heP := htop ▸ mem_top _
  exact mem_subgroupOf.1 this

theorem heOuterD_sup_normalizer_conj
    {b : Equiv.Perm (Fin 8330)} (hb : b ∈ heOuterD) :
    heOuterD ⊔ (heP ⊓ normalizer ((heGenF0.map (MulAut.conj b).toMonoidHom :
      Subgroup (Equiv.Perm (Fin 8330))) : Set (Equiv.Perm (Fin 8330)))) = heP := by
  have hbP := heOuterD_le_heP hb
  refine le_antisymm (sup_le heOuterD_le_heP inf_le_left) ?_
  refine le_trans heOuterD_sup_normalizer.ge (sup_le le_sup_left fun p hp => ?_)
  obtain ⟨hpP, hpN⟩ := mem_inf.1 hp
  have hN : b * p * b⁻¹ ∈ normalizer ((heGenF0.map (MulAut.conj b).toMonoidHom :
      Subgroup (Equiv.Perm (Fin 8330))) : Set (Equiv.Perm (Fin 8330))) := by
    rw [← map_equiv_normalizer_eq]
    exact mem_map_of_mem _ hpN
  have hmem : b * p * b⁻¹ ∈ heOuterD ⊔ (heP ⊓ normalizer ((heGenF0.map
      (MulAut.conj b).toMonoidHom : Subgroup (Equiv.Perm (Fin 8330))) :
        Set (Equiv.Perm (Fin 8330)))) :=
    mem_sup_right (mem_inf.2 ⟨heP.mul_mem (heP.mul_mem hbP hpP) (heP.inv_mem hbP), hN⟩)
  have hb' : b ∈ heOuterD ⊔ (heP ⊓ normalizer ((heGenF0.map (MulAut.conj b).toMonoidHom :
      Subgroup (Equiv.Perm (Fin 8330))) : Set (Equiv.Perm (Fin 8330)))) := mem_sup_left hb
  have := mul_mem (mul_mem (inv_mem hb') hmem) hb'
  simpa [mul_assoc] using this

end CFSG.ComponentClassification.SolMax.HeGen

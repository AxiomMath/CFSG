module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Model.Unique
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.TableVIIProof.CentEquiv

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

section Cert


theorem exists_good_of_simple {H : Type} [Group H] {E : Subgroup H}
    (hE : TwoHS.IsF5Centralizer H E) {S : Subgroup H} [IsSimpleGroup ↥S] {t : ↥S}
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    (hY : IsNonsplitDoubleCoverOfS5 ↥(Subgroup.centralizer ({t} : Set ↥S))) :
    ∃ (S₁ : Subgroup (Equiv.Perm (Fin 1408))) (t₁ : Equiv.Perm (Fin 1408)),
      Good S₁ t₁ ∧ Nonempty (↥S ≃* ↥S₁) := by
  obtain ⟨Ψ, -⟩ := exists_mulEquiv_p1408_of_isF5Centralizer hE
  let ψ : H →* Equiv.Perm (Fin 1408) := P1408.subtype.comp Ψ.toMonoidHom
  have hψ : Function.Injective ψ := fun x y h => Ψ.injective (Subtype.ext h)
  let S₁ : Subgroup (Equiv.Perm (Fin 1408)) := S.map ψ
  let e : ↥S ≃* ↥S₁ := Subgroup.equivMapOfInjective S ψ hψ
  let t₁ : Equiv.Perm (Fin 1408) := (e t : Equiv.Perm (Fin 1408))
  refine ⟨S₁, t₁, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨e⟩⟩
  ·
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨s, -, rfl⟩
    exact (Ψ s).2
  ·
    exact e.symm.isSimpleGroup
  ·
    exact (e t).2
  ·
    change (e t : Equiv.Perm (Fin 1408)) * (e t : Equiv.Perm (Fin 1408)) = 1
    have h : e t * e t = 1 := by
      rw [← map_mul, show t * t = 1 from by rw [← pow_two]; exact ht2, map_one]
    simpa using congrArg Subtype.val h
  ·
    intro h
    apply ht1
    apply e.injective
    rw [map_one]
    exact Subtype.ext h
  ·
    obtain ⟨ec⟩ := Section3.tableVII_centralizer_mulEquiv e t
    have hcent : Subgroup.centralizer ({e t} : Set ↥S₁) =
        (Subgroup.centralizer ({t₁} : Set (Equiv.Perm (Fin 1408)))).subgroupOf S₁ := by
      ext u
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
        Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro h
        simpa using congrArg Subtype.val h
      · intro h
        apply Subtype.ext
        simpa using h
    have hcent' : ((Subgroup.centralizer ({t₁} : Set (Equiv.Perm (Fin 1408)))).subgroupOf
        S₁).map S₁.subtype = S₁ ⊓ Subgroup.centralizer ({t₁} : Set (Equiv.Perm (Fin 1408))) := by
      rw [Subgroup.subgroupOf_map_subtype, inf_comm]
    exact hY.of_mulEquiv (ec.trans ((MulEquiv.subgroupCongr hcent).trans
      ((Subgroup.equivMapOfInjective _ S₁.subtype S₁.subtype_injective).trans
        (MulEquiv.subgroupCongr hcent'))))

end Cert

theorem nonempty_mulEquiv_u0_of_eq_stab
    {S₁ : Subgroup (Equiv.Perm (Fin 1408))} {p : Fin 1408}
    (h : S₁ = P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p) :
    Nonempty (↥S₁ ≃* ↥u0) := by
  have hmap : (MulAction.stabilizer ↥P1408 p).map P1408.subtype =
      P1408 ⊓ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨g, hg, rfl⟩
      refine ⟨g.2, ?_⟩
      rw [MulAction.mem_stabilizer_iff] at hg
      change P1408.subtype g ∈ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p
      rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hg
    · rintro ⟨hxP, hxS⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxP⟩, ?_, rfl⟩
      rw [MulAction.mem_stabilizer_iff]
      change x ∈ MulAction.stabilizer (Equiv.Perm (Fin 1408)) p at hxS
      rw [MulAction.mem_stabilizer_iff] at hxS
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hxS
  have hmap' : (MulAction.stabilizer ↥P1408 p).map P1408.subtype = S₁ := hmap.trans h.symm
  have e1 : ↥S₁ ≃* ↥(MulAction.stabilizer ↥P1408 p) :=
    ((Subgroup.equivMapOfInjective (MulAction.stabilizer ↥P1408 p) P1408.subtype
      P1408.subtype_injective).trans (MulEquiv.subgroupCongr hmap')).symm
  haveI : MulAction.IsPretransitive ↥P1408 (Fin 1408) := isPretransitive_P1408
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := ↥P1408) p (0 : Fin 1408)
  have hu0 : MulAction.stabilizer ↥P1408 (0 : Fin 1408) = u0 := by
    ext g
    rw [MulAction.mem_stabilizer_iff, mem_u0]
  have e2 : ↥(MulAction.stabilizer ↥P1408 p) ≃* ↥u0 :=
    (MulAction.stabilizerEquivStabilizer (G := ↥P1408) (α := Fin 1408) hg.symm).trans
      (MulEquiv.subgroupCongr hu0)
  exact ⟨e1.trans e2⟩

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5

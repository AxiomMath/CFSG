module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFInduces

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

noncomputable def ffInducesHom {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) :
    ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q :=
  MonoidHom.mk'
    (fun s => Classical.choose
      (ff_exists_induces hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) e s.2))
    (fun s s' =>
      ff_induces_unique hQ (by omega) e
        (Classical.choose_spec (ff_exists_induces hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) e
          (Subgroup.mul_mem _ s.2 s'.2)))
        (inducesViaP_mul
          (Classical.choose_spec (ff_exists_induces hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) e s.2))
          (Classical.choose_spec (ff_exists_induces hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) e s'.2))))

theorem ffInducesHom_spec {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (s : ↥(Subgroup.normalizer (L : Set G))) :
    InducesViaP L (Subgroup.center ↥L) hQ e (s : G) (ffInducesHom hm e s) := by
  show InducesViaP L (Subgroup.center ↥L) hQ e (s : G)
    (Classical.choose (ff_exists_induces hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) e s.2))
  exact Classical.choose_spec (ff_exists_induces hQ (Or.inr ⟨hm.1, Or.inr hm.2⟩) e s.2)

theorem ffInducesHom_eq {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {s : G} {x : ProjSim Q}
    (h : InducesViaP L (Subgroup.center ↥L) hQ e s x) : ffInducesHom hm e ⟨s, h.1⟩ = x := by
  exact ff_induces_unique hQ (by omega) e (ffInducesHom_spec hm e ⟨s, h.1⟩) h

theorem ffInducesHom_eq_one_iff {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hL : commutator ↥L = ⊤)
    (s : ↥(Subgroup.normalizer (L : Set G))) :
    ffInducesHom hm e s = 1 ↔ (s : G) ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro h1
    have hspec := ffInducesHom_spec hm e s
    rw [h1] at hspec
    exact mem_centralizer_of_inducesViaP_one hL hspec
  · intro hc
    have hspec := inducesViaP_one_of_centralizer (hQ := hQ) (e := e) hc
    have heq : s = ⟨(s : G), hspec.1⟩ := Subtype.ext rfl
    rw [heq]
    exact ffInducesHom_eq hm e hspec

theorem ffInducesHom_of_mem {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L)
    (hl : (l : G) ∈ Subgroup.normalizer (L : Set G)) :
    ffInducesHom hm e ⟨l, hl⟩ =
      projOrthToProjSim Q ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) := by
  have hspec := inducesViaP_of_mem e l
  have heq : (⟨l, hl⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨(l : G), hspec.1⟩ := Subtype.ext rfl
  rw [heq]
  exact ffInducesHom_eq hm e hspec

theorem innerOn_iff_simInOmegaStar {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hL : commutator ↥L = ⊤) {s : G}
    (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    InnerOn L s ↔ SimInOmegaStar hQ (ffInducesHom hm e ⟨s, hs⟩) := by
  let Φ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q := ffInducesHom hm e
  let Ω₁ : Subgroup (ProjSim Q) := (omegaProj hQ).map (projOrthToProjSim Q)
  have hmemOmega : ∀ x : ProjSim Q, SimInOmegaStar hQ x ↔ x ∈ Ω₁ := fun _ => Iff.rfl
  constructor
  · intro hinner
    let S : Subgroup G := (Ω₁.comap Φ).map (Subgroup.normalizer (L : Set G)).subtype
    have hLle : L ≤ S := by
      intro l hl
      have hEq : Φ ⟨l, Subgroup.le_normalizer hl⟩ =
          projOrthToProjSim Q
            (((e (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) : omegaProj hQ) : ProjOrth Q)) :=
        ffInducesHom_of_mem hm e ⟨l, hl⟩ (Subgroup.le_normalizer hl)
      refine Subgroup.mem_map.mpr ⟨⟨l, Subgroup.le_normalizer hl⟩, ?_, rfl⟩
      show Φ ⟨l, Subgroup.le_normalizer hl⟩ ∈ Ω₁
      rw [hEq]
      exact Subgroup.mem_map.mpr
        ⟨((e (QuotientGroup.mk (⟨l, hl⟩ : ↥L)) : omegaProj hQ) : ProjOrth Q),
          (e (QuotientGroup.mk (⟨l, hl⟩ : ↥L))).2, rfl⟩
    have hCle : Subgroup.centralizer (L : Set G) ≤ S := by
      intro c hc
      have h1 : Φ ⟨c, Subgroup.centralizer_le_normalizer (L : Set G) hc⟩ = 1 :=
        (ffInducesHom_eq_one_iff hm e hL
          ⟨c, Subgroup.centralizer_le_normalizer (L : Set G) hc⟩).mpr hc
      refine Subgroup.mem_map.mpr
        ⟨⟨c, Subgroup.centralizer_le_normalizer (L : Set G) hc⟩, ?_, rfl⟩
      show Φ ⟨c, Subgroup.centralizer_le_normalizer (L : Set G) hc⟩ ∈ Ω₁
      rw [h1]
      exact Subgroup.mem_map.mpr ⟨1, (omegaProj hQ).one_mem, map_one (projOrthToProjSim Q)⟩
    have hsup : L ⊔ Subgroup.centralizer (L : Set G) ≤ S := sup_le hLle hCle
    have hsin : s ∈ S := hsup hinner
    obtain ⟨n, hn, hns⟩ := Subgroup.mem_map.mp hsin
    have hn' : Φ n = Φ ⟨s, hs⟩ := by
      congr 1
      exact Subtype.ext hns
    rw [Subgroup.mem_comap] at hn
    rw [hn'] at hn
    exact (hmemOmega (Φ ⟨s, hs⟩)).mpr hn
  · intro hsimp
    obtain ⟨y, hy, hyeq⟩ := (hmemOmega (Φ ⟨s, hs⟩)).mp hsimp
    let q : ↥L ⧸ Subgroup.center ↥L := e.symm ⟨y, hy⟩
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective q
    have hE : e (QuotientGroup.mk l) = ⟨y, hy⟩ := by
      rw [hl]
      exact e.apply_symm_apply ⟨y, hy⟩
    have hPhi : Φ ⟨l, Subgroup.le_normalizer l.2⟩ = Φ ⟨s, hs⟩ := by
      rw [ffInducesHom_of_mem hm e l (Subgroup.le_normalizer l.2)]
      have hy' : ((e (QuotientGroup.mk l) : omegaProj hQ) : ProjOrth Q) = y := by
        rw [hE]
      rw [hy', hyeq]
    have hmul : Φ (⟨l, Subgroup.le_normalizer l.2⟩⁻¹ * ⟨s, hs⟩) = 1 := by
      rw [map_mul, map_inv, hPhi, inv_mul_cancel]
    have hcent : ((⟨l, Subgroup.le_normalizer l.2⟩⁻¹ * ⟨s, hs⟩ :
        ↥(Subgroup.normalizer (L : Set G))) : G) ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hL _).mp hmul
    unfold InnerOn
    have hdecomp : s = (l : G) * ((l : G)⁻¹ * s) := by group
    rw [hdecomp]
    exact Subgroup.mul_mem_sup l.2 hcent

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionClass
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFusion
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionPerfect
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR7Split
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionB

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.OuterAutomorphisms

theorem two_lt_card_of_exists_mul_ne {G : Type*} [Group G] [Finite G]
    (h : ∃ a b : G, a * b ≠ b * a) : 2 < Nat.card G := by
  obtain ⟨a, b, hab⟩ := h
  by_contra hle
  rw [not_lt] at hle
  have hpos : 0 < Nat.card G := Nat.card_pos
  interval_cases hc : Nat.card G
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 hc).1
    exact hab (Subsingleton.elim _ _)
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : IsCyclic G := isCyclic_of_prime_card hc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    obtain ⟨m, rfl⟩ := hg a
    obtain ⟨n, rfl⟩ := hg b
    exact hab (zpow_mul_comm g m n)

section LemmaC


theorem exists_conj_eq_mul_twoCentral {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {K : Type} [Field K] (e : L ≃* adjointGroup .F4 K)
    (hZ : center (adjointGroup .F4 K) = ⊥)
    (hF1 : FactF1 K) (hF3p : FactF3Perfect K) (hF4b : FactF4b K) (hF7 : FactF7 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hC1 : OuterFusionTwoCentral L t) :
    ∃ g : G, ∃ z ∈ L, g⁻¹ * t * g = t * z ∧ z ≠ 1 ∧
      ∃ U : Sylow 2 L, ∀ u ∈ (U : Subgroup L), (u : G) * z = z * u := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  have hCN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have hZL : center L = ⊥ := center_eq_bot_congr e.symm hZ
  have hnot : ∀ g : G, g⁻¹ * t * g ∉ L :=
    conj_not_mem_of_forall_perfect hset hOut hZL (exists_perfect_le_of_mulEquiv e hF1 hF3p hF4b)
      htC ht
  by_cases hout : ∃ g : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) ∧
      g⁻¹ * t * g ∉ L ⊔ zpowers t
  · obtain ⟨g, hg1, hg2⟩ := hout
    exact hC1 g hg1 hg2
  · simp only [not_exists, not_and, not_not] at hout
    have : IsSimpleGroup G := hset.simple
    obtain ⟨x₀, hx₀, hgen, hlift⟩ :=
      exists_gen_of_mulAut hCN hLt hKt (exists_mulAut_normalForm_of_mulEquiv e hF7)
    exact exists_conj_eq_mul_of_forall_inner (two_lt_card_of_exists_mul_ne hset.nonab) ht hLt
      hCN hnot hout hx₀ hgen hlift

end LemmaC

section Main


theorem not_normal_map_oddCore_of_facts {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hset : StandardSetting G L) (hOut : Group.IsSolvable (Outer L))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hq : 4 ≤ Nat.card K)
    (e : L ≃* adjointGroup .F4 K) (hZ : center (adjointGroup .F4 K) = ⊥)
    (hOutD : Group.IsSolvable (Outer (C3Levi K)))
    (hF1 : FactF1 K) (hF2 : FactF2 K) (hF3 : FactF3 K) (hF3p : FactF3Perfect K)
    (hLS : FactLeviSimple K) (hF4b : FactF4b K) (hF5 : FactF5 K) (hF6 : FactF6 K)
    (hF7 : FactF7 K)
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hC1 : OuterFusionTwoCentral L t)
    {X : Subgroup G} (hXodd : Odd (Nat.card X))
    (hXJ : X ≤ ((rootSL2 K rootR).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((C3Levi K).map e.symm.toMonoidHom).map L.subtype)
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2) :
    ¬ ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hLt : L ≤ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC
  obtain ⟨g, z, hzL, hgz, hz1, hzU⟩ :=
    exists_conj_eq_mul_twoCentral hset hOut e hZ hF1 hF3p hF4b hF7 ht hKt hC1
  obtain ⟨κ, hκ1, P, hP, ⟨ePC⟩⟩ := exists_mulEquiv_le_centralizer_of_conj_eq_mul hset hOut e hF2
    hF3 hF3p hLS hF5 hF6 htC ht hXodd hXJ hzL hz1 ⟨_, hzU.choose_spec⟩ hgz
  have eD : C3Levi K ≃* D := by
    rw [hDe]
    exact ((C3Levi K).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).trans
      (((C3Levi K).map e.symm.toMonoidHom).equivMapOfInjective L.subtype L.subtype_injective)
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  have hXL : X ≤ L := hXJ.trans (map_subtype_le _)
  have htX : t ∈ centralizer (X : Set G) := centralizer_le hXL htC
  have hDX : D ≤ centralizer (X : Set G) := by
    rw [hDe]
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨_, ⟨j, hj, rfl⟩, rfl⟩ := hXJ hx
    have hd' : d ∈ centralizer ((rootSL2 K rootR : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) := by
      rw [rootSL2_rootR, centralizer_rootSL2R_eq_C3Levi hq]
      exact hd
    have hjd := mem_centralizer_iff.1 hd' j hj
    simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hjd]
  have hDq : CFSG.Open.IsQuasisimple D := hDe ▸ isQuasisimple_open_map_C3Levi e
  have hZD : center D = ⊥ := center_eq_bot_congr eD center_C3Levi_eq_bot
  have hOutD' : Group.IsSolvable (Outer D) :=
    (CFSG.LocalAnalysis.ComponentInitial.outer_isomorphism eD).2.1 hOutD
  have hyD : (e.symm (yRep K κ) : G) ∈ D := by
    rw [hDe]
    exact ⟨e.symm (yRep K κ), ⟨yRep K κ, yRep_mem_C3Levi κ, rfl⟩, rfl⟩
  have hy1 : (e.symm (yRep K κ) : G) ≠ 1 := by
    intro h
    apply hκ1
    have h' : e.symm (yRep K κ) = 1 := Subtype.ext h
    rw [← e.apply_symm_apply (yRep K κ), h', map_one]
  exact not_normal_map_oddCore_centralizer_of_mulEquiv htX ht hDX hDq hZD hOutD'
    (hDL.trans hLt) hsyl hyD hy1 (Or.inr rfl) hP ⟨ePC.trans eD⟩

end Main

end CFSG.SeitzReduction.F4Pilot

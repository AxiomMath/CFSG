module

public import CFSG.GF2Type.SmithTypeE.E8.QAOrbit
public import CFSG.GF2Type.SmithTypeE.E8.TransClauses
public import CFSG.GF2Type.SmithTypeE.E8.Clause4Count
public import CFSG.GF2Type.Smith1980Orth.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup QuadraticMap Module CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
  CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)

variable {G : Type} [Group G] [Finite G]

section Ext

variable
  [IsSimpleGroup G]

theorem exists_setting_data (I : Inputs10) {S : Setting G} (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) {k : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG)
    (hvz : k * S.z * k⁻¹ ≠ S.z) :
    ∃ (φ' : (S.conjBy k).Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2))
      (ψ' : (S.conjBy k).Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))),
      SmithE8Clauses123 (S.conjBy k) φ' ψ' ∧
      φ' ((S.conjBy k).cl S.z) = e7Y56 ∧
      QAg = (Lp (S.conjBy k) k⁻¹).map ψ'.toMonoidHom := by
  have hTw : (S.conjBy k).width = 28 := (S.width_conjBy k).trans hw
  have hTU : LieModel (S.conjBy k).Mbar .E7 0 2 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (S.mbarEquivConjBy k).symm hU
  have hz0 : k⁻¹ * (S.conjBy k).z * k⁻¹⁻¹ = S.z := by
    show k⁻¹ * (k * S.z * k⁻¹) * k⁻¹⁻¹ = S.z
    group
  have hzQv : k⁻¹ * S.z * k ∈ S.QG :=
    (SME.mem_Qa_iff S k S.z).mp (S.z_mem_Qa_of_mem_QG rfl hvQ hvz)
  have haQ : k⁻¹ * (S.conjBy k).z * k⁻¹⁻¹ ∈ (S.conjBy k).QG := by
    rw [hz0]
    exact (SME.mem_Qa_iff S k S.z).2 hzQv
  have hne : k⁻¹ * (S.conjBy k).z * k⁻¹⁻¹ ≠ (S.conjBy k).z := by
    rw [hz0]
    exact fun h => hvz h.symm
  obtain ⟨ψ', hψ'⟩ := exists_psi hTw hTU haQ hne
  obtain ⟨φ', hE', hφ'⟩ := exists_phi I hTw hTU haQ hne ψ' hψ'
  refine ⟨φ', ψ', IdBase.clauses123 I hTw hTU ⟨haQ, hne, hψ', hE', hφ'⟩, ?_, hψ'⟩
  rw [← hz0]
  exact hφ'

theorem card_orbit_conj_le (I : Inputs10) {S : Setting G} (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1) {k x : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG)
    (hvz : k * S.z * k⁻¹ ≠ S.z) (hxc : IsConj S.z x) (hxM : x ∈ S.M) (hxQ : x ∉ S.QG)
    (hxQv : k⁻¹ * x * k ∈ S.QG) :
    Nat.card (Set.range fun y : ↥(S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) =>
      (y : G) * x * (y : G)⁻¹) ≤ 2 * 2 ^ 11 := by
  classical
  obtain ⟨φ', ψ', hcl, hφz, hψ'⟩ := exists_setting_data I hw hU hvQ hvz
  have hz0 : k⁻¹ * (S.conjBy k).z * k⁻¹⁻¹ = S.z := by
    show k⁻¹ * (k * S.z * k⁻¹) * k⁻¹⁻¹ = S.z
    group
  have hzQv : k⁻¹ * S.z * k ∈ S.QG :=
    (SME.mem_Qa_iff S k S.z).mp (S.z_mem_Qa_of_mem_QG rfl hvQ hvz)
  have hzT : S.z ∈ (S.conjBy k).QG := (SME.mem_Qa_iff S k S.z).2 hzQv
  have hxT : x ∈ (S.conjBy k).QG := (SME.mem_Qa_iff S k x).2 hxQv
  have hQa : (S.conjBy k).Qa k⁻¹ = S.QG := by
    have h : ((S.conjBy k).conjBy k⁻¹).z = S.z := hz0
    exact Setting.QG_eq_of_z_eq ((S.conjBy k).conjBy k⁻¹) S h
  have hxTz : x ≠ (S.conjBy k).z := fun h => hxQ (h ▸ hvQ)
  have hxcT : IsConj (S.conjBy k).z x := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxc
    refine isConj_iff.mpr ⟨g * k⁻¹, ?_⟩
    rw [← hg]
    show g * k⁻¹ * (k * S.z * k⁻¹) * (g * k⁻¹)⁻¹ = g * S.z * g⁻¹
    group
  have hwt : φ' ((S.conjBy k).cl x) ∈ weightVec := hcl.2.1 x hxcT hxT hxTz
  have hnotcoll : φ' ((S.conjBy k).cl x) ∉ collSpace e7Y56 := by
    intro h
    have hh := (hcl.2.2.2 k⁻¹ x (by rw [hz0]; exact hzT) (by rw [hz0]; exact fun h => hvz h.symm)
      hxcT hxT hxTz).2
    have hz1 : φ' ((S.conjBy k).cl (k⁻¹ * (S.conjBy k).z * k⁻¹⁻¹)) = e7Y56 := by
      rw [hz0]
      exact hφz
    rw [hz1] at hh
    have := hh h
    rw [hQa] at this
    exact hxQ this
  have hcoll1 : ∀ u, u ∈ collSpace e7Y56 ↔ u ∈ W0 := by
    intro u
    have h := mem_collSpace_iff (1 : ↥(adjointGroup .E7 (ZMod 2))) u
    simp only [F.rep_one_apply, inv_one] at h
    exact h
  have hw0 : φ' ((S.conjBy k).cl x) ∉ W0 := fun h => hnotcoll ((hcoll1 _).2 h)
  have hff : F.ff e7Y56 (φ' ((S.conjBy k).cl x)) = 0 := by
    have h := isometry8 hcl.1 ((S.conjBy k).cl S.z) ((S.conjBy k).cl x)
    rw [hφz] at h
    rw [h]
    refine ((S.conjBy k).polar_cl_eq_zero_iff hzT hxT).2 ?_
    have := (S.mem_M_iff).1 hxM
    exact this.symm
  have hcardO := card_orbit_le hwt hw0 hff
  have hmaps : ∀ y : ↥(S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)),
      φ' ((S.conjBy k).cl ((y : G) * x * (y : G)⁻¹)) ∈ Set.range fun q : ↥QAg =>
        e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (φ' ((S.conjBy k).cl x)) := by
    intro y
    have hyM : (y : G) ∈ (S.conjBy k).M := y.2.2
    have hy0 : (y : G) ∈ (S.conjBy k).L0 k⁻¹ := by
      refine ⟨?_, hyM⟩
      rw [hQa]
      exact y.2.1
    have hmL : (⟨(S.conjBy k).ρ ⟨(y : G), hyM⟩, ⟨⟨(y : G), hyM⟩, rfl⟩⟩ : (S.conjBy k).Mbar) ∈
        Lp (S.conjBy k) k⁻¹ := by
      rw [Lp, Subgroup.mem_subgroupOf]
      exact (S.conjBy k).ρ_mem_Lbar hy0
    have hq : ψ' ⟨(S.conjBy k).ρ ⟨(y : G), hyM⟩, ⟨⟨(y : G), hyM⟩, rfl⟩⟩ ∈ QAg := by
      rw [hψ']
      exact Subgroup.mem_map_of_mem _ hmL
    refine ⟨⟨_, hq⟩, ?_⟩
    show e7Rep56 (ZMod 2) (ψ' ⟨(S.conjBy k).ρ ⟨(y : G), hyM⟩, ⟨⟨(y : G), hyM⟩, rfl⟩⟩)
      (φ' ((S.conjBy k).cl x)) = φ' ((S.conjBy k).cl ((y : G) * x * (y : G)⁻¹))
    rw [← hcl.1 ⟨(S.conjBy k).ρ ⟨(y : G), hyM⟩, ⟨⟨(y : G), hyM⟩, rfl⟩⟩ ((S.conjBy k).cl x)]
    congr 1
    exact (S.conjBy k).ρ_cl ⟨(y : G), hyM⟩ hxT
  set Orb : Set G := Set.range fun y : ↥(S.QG ⊓ centralizer ({k * S.z * k⁻¹} : Set G)) =>
    (y : G) * x * (y : G)⁻¹ with hOrb
  set O : Set (Fin e7Data.d →₀ ZMod 2) := Set.range fun q : ↥QAg =>
    e7Rep56 (ZMod 2) (q : ↥(adjointGroup .E7 (ZMod 2))) (φ' ((S.conjBy k).cl x)) with hO
  have hOrbfin : Orb.Finite := Set.toFinite _
  have hOfin : O.Finite := Set.toFinite _
  have hOrbT : ∀ u ∈ Orb, u ∈ (S.conjBy k).QG := by
    rintro _ ⟨y, rfl⟩
    exact (S.conjBy k).conj_mem_QG y.2.2 hxT
  have hfiber : ∀ a ∈ hOrbfin.toFinset.image (fun u => φ' ((S.conjBy k).cl u)),
      (hOrbfin.toFinset.filter fun u => φ' ((S.conjBy k).cl u) = a).card ≤ 2 := by
    intro a ha
    obtain ⟨u₀, hu₀, hu₀a⟩ := Finset.mem_image.1 ha
    have hu₀Q := hOrbT u₀ (hOrbfin.mem_toFinset.1 hu₀)
    refine (Finset.card_le_card (t := {u₀, u₀ * (S.conjBy k).z}) ?_).trans
      (Finset.card_le_two)
    intro u hu
    rw [Finset.mem_filter] at hu
    have huQ := hOrbT u (hOrbfin.mem_toFinset.1 hu.1)
    have hcl' : (S.conjBy k).cl u₀ = (S.conjBy k).cl u :=
      φ'.injective (hu₀a.trans hu.2.symm)
    rcases ((S.conjBy k).cl_eq_cl_iff hu₀Q huQ).1 hcl' with h | h
    · exact Finset.mem_insert.2 (Or.inl h)
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 h))
  have h1 := Finset.card_le_mul_card_image hOrbfin.toFinset 2 hfiber
  have h2 : (hOrbfin.toFinset.image fun u => φ' ((S.conjBy k).cl u)).card ≤ hOfin.toFinset.card := by
    refine Finset.card_le_card ?_
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨y, rfl⟩ := hOrbfin.mem_toFinset.1 hu
    exact hOfin.mem_toFinset.2 (hmaps y)
  have h3 : hOfin.toFinset.card = Nat.card O := (Nat.card_eq_card_finite_toFinset hOfin).symm
  have h4 : hOrbfin.toFinset.card = Nat.card Orb := (Nat.card_eq_card_finite_toFinset hOrbfin).symm
  rw [← h4]
  calc hOrbfin.toFinset.card
      ≤ 2 * (hOrbfin.toFinset.image fun u => φ' ((S.conjBy k).cl u)).card := h1
    _ ≤ 2 * hOfin.toFinset.card := Nat.mul_le_mul_left _ h2
    _ = 2 * Nat.card O := by rw [h3]
    _ ≤ 2 * 2 ^ 11 := Nat.mul_le_mul_left _ hcardO

theorem psi_involution {S : Setting G} (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))) {x : G}
    (hxM : x ∈ S.M) (hxc : IsConj S.z x) (hxQ : x ∉ S.QG) :
    ψ ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ * ψ ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ = 1 ∧
      ψ ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ ≠ 1 := by
  have hx2 : x ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxc
    rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hρxx : S.ρ ⟨x, hxM⟩ * S.ρ ⟨x, hxM⟩ = 1 := by
    rw [← map_mul]
    have : ((⟨x, hxM⟩ : S.M) * ⟨x, hxM⟩ : S.M) = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, hx2]; rfl)
    rw [this, map_one]
  refine ⟨?_, ?_⟩
  · rw [← map_mul]
    have : (⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ * ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ : S.Mbar) = 1 :=
      Subtype.ext hρxx
    rw [this, map_one]
  · intro h
    apply hxQ
    have h1 : (⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ : S.Mbar) = 1 :=
      ψ.injective (h.trans (map_one ψ).symm)
    have h2 : S.ρ ⟨x, hxM⟩ = 1 := congrArg Subtype.val h1
    exact (S.ρ_eq_one_iff ⟨x, hxM⟩).mp h2

theorem smithE8Clause4_of (I : Inputs10) {S : Setting G} (hw : S.width = 28)
    (hU : LieModel S.Mbar .E7 0 2 1)
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)} {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))}
    (hφ : SmithE8Clauses123 S φ ψ) : SmithE8Clause4 S ψ := by
  intro x hxM hxc hxQ
  obtain ⟨g, hg⟩ := isConj_iff.mp hxc
  have hxM' : g * S.z * g⁻¹ ∈ S.M := hg ▸ hxM
  have hxQ' : g * S.z * g⁻¹ ∉ S.QG := hg ▸ hxQ
  obtain ⟨v, hvc, hvQ, hvQa⟩ := smithE8E33_of_clauses hw hφ g hxM' hxQ'
  obtain ⟨k, hk⟩ := isConj_iff.mp hvc
  subst hk
  subst hg
  have hvQx' : g⁻¹ * (k * S.z * k⁻¹) * g ∈ S.QG := (SME.mem_Qa_iff S g _).mp hvQa
  have hvz : k * S.z * k⁻¹ ≠ S.z := by
    intro h
    apply SMF.conj_z_not_mem_QG S hxQ
    rw [← h]
    exact hvQx'
  have hvx : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹ := fun h => hxQ (h ▸ hvQ)
  have hxQv : k⁻¹ * (g * S.z * g⁻¹) * k ∈ S.QG := SME.mem_Qa_symm S hvQx' hvx
  have hn := card_orbit_conj_le I hw hU hvQ hvz hxc hxM hxQ hxQv
  have hchain := card_QG_le_of_orbit S hvQ hn
  set x' := g * S.z * g⁻¹ with hx'
  have hz : S.z ∈ (S.QG ⊓ centralizer ({x'} : Set G) : Subgroup G) :=
    ⟨S.z_mem_QG, mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm⟩
  have hclle : S.clSub (S.QG ⊓ centralizer ({x'} : Set G)) ≤ S.fixQt x' := by
    intro v hv
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp hv
    rw [S.cl_mem_fixQt_iff hxM hyQ]
    have hyc : y * x' = x' * y := mem_centralizer_singleton_iff.mp hy.2
    congr 1
    calc x' * y * x'⁻¹ = y * x' * x'⁻¹ := by rw [hyc]
      _ = y := by group
  have hcard2 : Nat.card (S.QG ⊓ centralizer ({x'} : Set G) : Subgroup G) =
      2 * 2 ^ finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({x'} : Set G))) := by
    have h1 := S.card_clPre (S.clSub (S.QG ⊓ centralizer ({x'} : Set G)))
    rw [S.clPre_clSub inf_le_left hz, S.card_submodule] at h1
    exact h1
  have hQ57 : Nat.card S.QG = 2 ^ 57 := by
    rw [S.card_QG_eq_card_Q, S.card_Q_eq, hw]
  have hd : 43 ≤ finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({x'} : Set G))) := by
    rw [hQ57, hcard2] at hchain
    have h2 : 2 ^ 57 ≤ 2 ^ (14 + finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({x'} : Set G)))) := by
      calc 2 ^ 57 ≤ 2 * (2 * 2 ^ 11) * (2 * 2 ^ finrank (ZMod 2)
            (S.clSub (S.QG ⊓ centralizer ({x'} : Set G)))) := hchain
        _ = 2 ^ (14 + finrank (ZMod 2) (S.clSub (S.QG ⊓ centralizer ({x'} : Set G)))) := by
          rw [pow_add]
          ring
    have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    omega
  have hd5 := CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_add_finrank_fixSpace
    (S.ρ ⟨x', hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt)
  rw [← S.fixQt_of_mem hxM, ← S.commQt_of_mem hxM, S.finrank_Qt_eq_two_mul_width, hw] at hd5
  have hfix : 43 ≤ finrank (ZMod 2) (S.fixQt x') := hd.trans (Submodule.finrank_mono hclle)
  have hdim : finrank (ZMod 2) (commSp (ψ ⟨S.ρ ⟨x', hxM⟩, ⟨⟨x', hxM⟩, rfl⟩⟩)) ≤ 13 := by
    rw [commSp_eq_map_commQt hφ.1 hxM, LinearEquiv.finrank_map_eq]
    omega
  obtain ⟨hinv1, hinv2⟩ := psi_involution ψ hxM hxc hxQ
  exact (involutionFacts8 _ hinv1 hinv2).root_of_le hdim

end Ext

end CFSG.GF2Type.SmithTypeE.E8

module

public import CFSG.GH74.GLS.C3.Layer1.PU3Rows
public import CFSG.GH74.GLS.C3.Layer1.PU3Basic
public import CFSG.GH74.Generic.BProg.B1.PilotS3
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockBasicAux
public import CFSG.GH74.Generic.BProg.B2.Thm2Comp

public section

namespace CFSG.GH74.Generic.BProg.B2.SDR

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B2
  CFSG.GH74.Uniqueness CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace SDRComp

omit [Finite G] in
theorem commutator_eq_self_of_isPCompIn {X K : Subgroup G} (hK : IsPCompIn 2 X K) : ⁅K, K⁆ = K := by
  have hp : Group.IsPerfect (K.subgroupOf X) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hK.2
  have hp' : Group.IsPerfect K := by
    have e := Subgroup.subgroupOfEquivOfLe hK.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.isPerfect_iff.mp hp'

omit [Finite G] in
theorem subgroupOf_le_sup_of_map_eq {K M : Subgroup G} {J : Subgroup ↥M}
    (hJ : J.map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) = barIn M K) :
    K.subgroupOf M ≤ J ⊔ pPrimeCore 2 ↥M := by
  intro y hy
  have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥M) y ∈ barIn M K := ⟨y, hy, rfl⟩
  rw [← hJ] at hmem
  obtain ⟨j, hj, hjy⟩ := hmem
  have hjo : j⁻¹ * y ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.1 hjy
  have e : y = j * (j⁻¹ * y) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hj hjo

end SDRComp

theorem isPCompIn_of_c1 {x : G} {K A M P Q H : Subgroup G} (hs : Stage2Setup G x K A M P Q) (hKM : K ≤ M)
    (hH : IsMinSubnormalIn K M H) (hc1 : barIn M H = barIn M K) :
    IsPCompIn 2 M H ∧ H = pPrimeCoreOf 2 H ⊔ K := by
  have hKH : K ≤ H := hH.1
  have hHM : H ≤ M := hH.2.1.1
  have hHsub : (H.subgroupOf M).IsSubnormal := hH.2.1.2
  have hHbar : (barIn M H).IsSubnormal :=
    Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hHsub
  have hKc : IsComponent (barIn M K) :=
    isComponent_barIn_of_isSubnormal hs hKM (hc1 ▸ hHbar)
  have hperf : ⁅K, K⁆ = K := SDRComp.commutator_eq_self_of_isPCompIn hs.pair.1.1.1.2.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable ↥(pPrimeCore 2 ↥M) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card)
  refine ⟨⟨hHM, barIn M K, hKc, hHsub, hc1, ?_⟩, ?_⟩
  · intro J hJlt hJsub hJmap
    have hle : K.subgroupOf M ≤ J ⊔ pPrimeCore 2 ↥M := SDRComp.subgroupOf_le_sup_of_map_eq hJmap
    have hKJ : K.subgroupOf M ≤ J :=
      CFSG.AGLEmbedding.le_of_perfect_of_le_sup_of_isSubnormal hJsub
        (PU3.commutator_subgroupOf_eq hKM hperf) hle
    set J' : Subgroup G := J.map M.subtype with hJ'
    have hJ'sub : J'.subgroupOf M = J := Subgroup.comap_map_eq_self_of_injective M.subtype_injective J
    have hKJ' : K ≤ J' := fun k hk => ⟨⟨k, hKM hk⟩, hKJ hk, rfl⟩
    have hJ'H : J' ≤ H := by
      rintro _ ⟨j, hj, rfl⟩
      exact hJlt.le hj
    have hEq : J' = H :=
      hH.2.2 J' hKJ' hJ'H ⟨Subgroup.map_subtype_le J, by rw [hJ'sub]; exact hJsub⟩
    have : J = H.subgroupOf M := by rw [← hJ'sub, hEq]
    exact hJlt.ne this
  · refine le_antisymm (fun h hh => ?_) (sup_le (TwoThin.pPrimeCoreOf_le H) hKH)
    have hhM : h ∈ M := hHM hh
    have hmem : QuotientGroup.mk' (pPrimeCore 2 ↥M) (⟨h, hhM⟩ : ↥M) ∈ barIn M H :=
      ⟨⟨h, hhM⟩, hh, rfl⟩
    rw [hc1] at hmem
    obtain ⟨k', hk', hkh⟩ := hmem
    have hko : k'⁻¹ * ⟨h, hhM⟩ ∈ pPrimeCore 2 ↥M := QuotientGroup.eq.1 hkh
    have hkK : (k' : G) ∈ K := hk'
    have hoM : (k' : G)⁻¹ * h ∈ pPrimeCoreOf 2 M := ⟨k'⁻¹ * ⟨h, hhM⟩, hko, by simp⟩
    have hoH : (k' : G)⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hKH hkK)) hh
    have hoO : (k' : G)⁻¹ * h ∈ pPrimeCoreOf 2 H := Th2.inf_le_pPrimeCoreOf hHM ⟨hoM, hoH⟩
    have e : h = (k' : G) * ((k' : G)⁻¹ * h) := by group
    have := Subgroup.mul_mem_sup hkK hoO
    rwa [← e, sup_comm] at this

theorem CMK_eq_CMbar {K M H : Subgroup G} (hKH : K ≤ H) (hcomp : IsPCompIn 2 M H)
    (hc1 : barIn M H = barIn M K) (hnorm : ∀ m ∈ M, ∀ l ∈ H, m * l * m⁻¹ ∈ H) :
    CMK M H = CMbar M K := by
  have hHM : H ≤ M := hcomp.1
  have hKM : K ≤ M := hKH.trans hHM
  have hOHM : pPrimeCoreOf 2 H ≤ pPrimeCoreOf 2 M := PU3.pPrimeCoreOf_le_of_comp hcomp
  apply le_antisymm
  · intro c hc
    obtain ⟨hcM, -, -, hcc⟩ := C3.Layer1.U1a.mem_CMK_iff.1 hc
    exact Th2.HY.mem_CMbar_of_comm hKM hcM (fun k hk => hOHM (hcc k (hKH hk)))
  · intro c hc
    have hcM : c ∈ M := hc.1
    refine C3.Layer1.U1a.mem_CMK_iff.2 ⟨hcM, C3.Layer1.U1a.mem_normalizer_of_norm hnorm hcM,
      C3.Layer1.U1a.mem_normalizer_pPrimeCoreOf hnorm hcM, fun h hh => ?_⟩
    have hcH : c ∈ CMbar M H := by
      rw [Thm2Comp.mem_CMbar_iff hHM ⟨c, hcM⟩]
      have := (Thm2Comp.mem_CMbar_iff hKM ⟨c, hcM⟩).1 hc
      simpa [SD.centBarK, hc1] using this
    have hO : ⁅h, c⁆ ∈ pPrimeCoreOf 2 M := hcH.2.2.2 h (Subgroup.mem_sup_left hh)
    have hHc : ⁅h, c⁆ ∈ H := by
      have h1 := hnorm c hcM h⁻¹ (H.inv_mem hh)
      have e : ⁅h, c⁆ = h * (c * h⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
      rw [e]; exact H.mul_mem hh h1
    rw [← PU3.inf_pPrimeCoreOf_eq hcomp]
    exact ⟨hHc, hO⟩

theorem kBar_data_of_shape3 {K H : Subgroup G} (hKH : K ≤ H) (hLeq : H = pPrimeCoreOf 2 H ⊔ K)
    (hq : IsQuasisimple (↥K ⧸ pPrimeCore 2 ↥K)) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) :
    IsSimpleGroup (kBar H) ∧ (∃ a b : kBar H, a * b ≠ b * a) ∧ 2 ≤ pRank 2 ↥H ∧
      Group.IsSolvable (Outer (kBar H)) := by
  obtain ⟨e⟩ := PU3.Rows.kBar_equiv hKH hLeq
  have hsK : IsSimpleGroup (kBar K) := B1.PilotS3.isSimpleGroup_of_qShape3 h3
  have hsH : IsSimpleGroup (kBar H) := e.isSimpleGroup
  have hOutK : Group.IsSolvable (Outer (kBar K)) := by
    obtain ⟨p, f, -, -, -, hL | hU⟩ := h3
    · exact CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable
        (stated_of_lieModel_PSL hL)
    · exact CFSG.ComponentClassification.CatalogueSchreierAssembly.classical_model_outer_solvable
        (stated_of_lieModel_PSU hU)
  have hnabK : ∃ a b : kBar K, a * b ≠ b * a := by
    obtain ⟨-, -, a', b', hab'⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    exact ⟨a, b, fun h => hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩
  have hnabH : ∃ a b : kBar H, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabK
    exact ⟨e.symm a, e.symm b, fun hc => hab (by simpa using congrArg e hc)⟩
  exact ⟨hsH, hnabH, PU3.Rows.two_le_pRank_of_kBar hsH hnabH,
    CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm⟩

end CFSG.GH74.Generic.BProg.B2.SDR

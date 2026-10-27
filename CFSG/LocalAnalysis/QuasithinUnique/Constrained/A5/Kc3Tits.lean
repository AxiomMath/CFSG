module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.LieType.BorelTits.Tits
public import Certificates.Certificate3950
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3CoverBase

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5

theorem not_isSolvable_alt5 :
    ¬ Group.IsSolvable ↥(alternatingGroup (Fin 5)) := by
  intro hs
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable.2 hs) a0' b0'
  have : (a0 * b0 : Equiv.Perm (Fin 5)) = b0 * a0 := congrArg Subtype.val hcomm
  revert this
  exact Certificates.certificate3950

theorem kc3ForS_tits
    : Kc3ForS Kc3Tits := by
  intro G _ _ K L S₀ T₀ hq hmod hZ hLK hD hperf hSL hS hT hST hTK hTS
  exfalso
  obtain ⟨V, Q, hVQ, hQL, hQ2, hLQ, hLV, α, hα, hαQ, β, hβ⟩ := hD
  have hBT := CFSG.LieType.BorelTits.holdsTits_of_reeTitsModel_tits hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVK : V ≤ K := hVQ.trans (hQL.trans hLK)
  set V' : Subgroup ↥K := V.subgroupOf K with hV'
  have hV'2 : IsPGroup 2 V' := by
    have : IsPGroup 2 ↥V := hQ2.to_le hVQ
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hVK).symm
  have hV'ne : V' ≠ ⊥ := by
    intro h
    apply d5_V_ne_bot β
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hVK hv⟩ : ↥K) ∈ V' := Subgroup.mem_subgroupOf.2 hv
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨S, P, hP, hN, -, -, hSP⟩ := hBT V' hV'ne hV'2
  have hS2 : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥K) ⊤ := by
    refine ⟨le_top, S.isPGroup', ?_⟩
    have h1 : ((S : Subgroup ↥K).subgroupOf ⊤).index = (S : Subgroup ↥K).index :=
      Subgroup.relIndex_top_right _
    rw [h1]
    exact S.not_dvd_index
  obtain ⟨H, N, -, hSH, hSN, -, -, hlat, hHs, hNs⟩ :=
    CFSG.QuasithinUnique.Setup.X6.titsSylowOvergroupLattice ↥K hmod (S : Subgroup ↥K) hS2
  have hPsolv : Group.IsSolvable ↥P := by
    rcases hlat P hSP with h | h | h | h
    · rw [h]
      have := S.isPGroup'.isNilpotent
      infer_instance
    · rw [h]; exact hHs
    · rw [h]; exact hNs
    · exact absurd h hP
  have hLP : L.subgroupOf K ≤ P := by
    refine le_trans ?_ hN
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have := Subgroup.mem_normalizer_iff.1 (hLV hl') (x : G)
    show (x : G) ∈ V ↔ ((l * x * l⁻¹ : ↥K) : G) ∈ V
    simpa using this
  have hLsolv : Group.IsSolvable ↥(L.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLP)
      (Subgroup.inclusion_injective _)
  have hLsolv' : Group.IsSolvable ↥L :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hLK).symm.toMonoidHom) (MulEquiv.injective _)
  exact not_isSolvable_alt5 (Group.isSolvable_of_surjective hα)

theorem kc3For_tits
    : Kc3For Kc3Tits := kc3For_of_simple isoInv_tits kc3ForS_tits

end CFSG.QuasithinUnique.A5

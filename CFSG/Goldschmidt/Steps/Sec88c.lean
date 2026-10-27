module

public import CFSG.Goldschmidt.Steps.G36Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec8Comp
import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.Goldschmidt.Steps.G36TypeIMain
import CFSG.Goldschmidt.Steps.G76L2
import CFSG.Walter.Bender1970.S3.FStar
import CFSG.Walter.Bender1970.S38.Basic
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open CFSG.ComponentClassification

variable {Q : Type} [Group Q] [Finite Q] {A : Subgroup Q}

theorem exists_isComponentOf
    (hO : goldschmidtOddCore Q = ⊥) (hS : IsSStarIn ⊤ A)
    (hK : ¬ normalClosureIn ⊤ A ≤ A) :
    ∃ L : Subgroup Q, GorensteinWalter.IsComponentOf L (normalClosureIn ⊤ A) := by
  by_contra hno
  push Not at hno
  obtain ⟨Z₂, hZA, -, hgen⟩ := G310.exists_gen hO hS
  refine hK ((hgen Z₂ le_rfl fun L hL => ?_).trans hZA)
  exfalso
  have hc := (CFSG.Adapters.isComponentOf_top_iff L).mp (G310.compFacts hO hS hL).comp
  exact hno L ⟨hL.1, Walter.isSubnormal_subgroupOf_of_le hL.1 le_top hc.2.1, hc.2.2⟩

theorem centralizer_le_normalizer
    (hS : IsSStarIn ⊤ A) (hA : IsElemAbelian 2 A)
    (h4 : Nat.card A = 4) {L : Subgroup Q}
    (hL : GorensteinWalter.IsComponentOf L (normalClosureIn ⊤ A)) :
    Subgroup.centralizer (A : Set Q) ≤ Subgroup.normalizer (L : Set Q) := by
  have hAL := le_of_isComponentOf G31 hS hA h4 hL
  have hLM := G73.isComponentOf_of_normalClosureIn hL
  have hnot := G73.not_inf_le_centralizer G31 hS hA hL
  intro c hc
  rw [← Walter.map_conj_eq_iff_mem_normalizer]
  by_contra hne
  have hLc := Walter.isComponentOf_map_conj hLM (Subgroup.le_normalizer (Subgroup.mem_top c))
  rcases Walter.isComponentOf_eq_or_commutator_eq_bot hLM hLc with h | h
  · exact hne h.symm
  · apply hnot
    have hLC : L.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer (L : Set Q) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
    rintro y ⟨hyA, -⟩
    refine hLC ⟨y, hAL hyA, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← Subgroup.mem_centralizer_iff.mp hc y hyA]
    group

theorem nonempty_psu34
    {L : Type} [Group L] [Finite L] {A₀ : Subgroup L} {T₀ : Sylow 2 L}
    (h : G36Hyp L A₀ T₀) (hI : IsGoldTypeI L) (h4 : Nat.card A₀ ≤ 4) :
    Nonempty (L ⧸ Subgroup.center L ≃* PSU3 2 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hKq := h.quasisimple
  have : IsSimpleGroup (L ⧸ Subgroup.center L) := hKq.2
  have hnab : ∃ x y : L ⧸ Subgroup.center L, x * y ≠ y * x :=
    Helpers.quasisimple_central_quotient_nonabelian L hKq
  have hZb : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ :=
    Helpers.center_eq_bot (L ⧸ Subgroup.center L) hnab
  have hI' : IsGoldTypeI (L ⧸ Subgroup.center L) := isGoldTypeI_quotient_center hZb hI
  obtain ⟨D, y, hB⟩ := exists_g36Borel G32 h hI
  have hZTb : Nat.card ((T₀ : Subgroup L).map π ⊓
      Subgroup.centralizer (((T₀ : Subgroup L).map π : Subgroup _) : Set _) :
        Subgroup (L ⧸ Subgroup.center L)) ≤ 4 := by
    rw [← hB.map_eq]
    exact (Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd A₀ π)).trans h4
  set Tb' : Sylow 2 (L ⧸ Subgroup.center L) := T₀.mapSurjective (QuotientGroup.mk'_surjective _)
    with hTb'
  have hTb'coe : (Tb' : Subgroup (L ⧸ Subgroup.center L)) = (T₀ : Subgroup L).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D', -, -, -, -, -, -, -, -, -, -, hPSL, -, hU, -, -, -, -, -⟩ :=
    G32 (L ⧸ Subgroup.center L) hI' Tb'
  rw [hTb'coe] at hPSL hU
  rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exfalso
    have hab := isMulCommutative_map_of_psl2 (T₀ := T₀) (by omega) e
    have hle : (T₀ : Subgroup L).map π ≤ (T₀ : Subgroup L).map π ⊓
        Subgroup.centralizer (((T₀ : Subgroup L).map π : Subgroup _) : Set _) :=
      fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz =>
        congrArg Subtype.val (hab.is_comm.comm ⟨z, hz⟩ ⟨x, hx⟩)⟩
    have h1 := (Subgroup.card_le_of_le hle).trans hZTb
    rw [(hPSL n hn ⟨e⟩).1] at h1
    have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · exfalso
    have h1 := (hB.sz n hn ⟨e⟩).1
    rw [hB.tb_eq] at h1
    rw [h1] at hZTb
    have : 2 ^ 3 ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have h1 := (hU n hn ⟨e⟩).1
    rw [h1] at hZTb
    have hn2 : n = 2 := by
      have : 2 ^ n ≤ 2 ^ 2 := by norm_num; exact hZTb
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
      omega
    subst hn2
    exact ⟨e⟩

theorem typeII_facts
    (hS : IsSStarIn ⊤ A) (hA : IsElemAbelian 2 A) (h4 : Nat.card A = 4)
    {L : Subgroup Q} (hL : GorensteinWalter.IsComponentOf L (normalClosureIn ⊤ A))
    {T₀ : Sylow 2 L} (h : G36Hyp L (A.subgroupOf L) T₀) (hII : IsGoldTypeII L) :
    A ⊓ Subgroup.centralizer (L : Set Q) = ⊥ ∧
      ∀ w ∈ Subgroup.centralizer (A : Set Q), IsPGroup 2 (Subgroup.zpowers w) →
        ∃ c ∈ A, c⁻¹ * w ∈ Subgroup.centralizer (L : Set Q) := by
  have hAL := le_of_isComponentOf G31 hS hA h4 hL
  have hAT : A.subgroupOf L = (T₀ : Subgroup L) := G76.eq_sylow_of_typeII h hII
  have hT₀ab : IsMulCommutative (T₀ : Subgroup L) := by
    have := hA.1
    rw [← hAT]
    exact Subgroup.comap_injective_isMulCommutative (H := A) L.subtype_injective
  refine ⟨?_, fun w hwA hw => ?_⟩
  · rw [eq_bot_iff]
    rintro c ⟨hcA, hcC⟩
    have hcZ : (⟨c, hAL hcA⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun g =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hcC g g.2)
    have h1 := eq_one_of_pow_two_of_odd (K := Subgroup.center L) hII.1 hcZ (k := 1)
      (Subtype.ext (by simpa using hA.2 c hcA))
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · obtain ⟨b, hb, hbw⟩ := G76.exists_acts_of_sylow h.quasisimple T₀ hT₀ab hw (fun p hp => by
        rw [← hAT] at hp
        exact (Subgroup.mem_centralizer_iff.mp hwA p (Subgroup.mem_subgroupOf.mp hp)).symm)
      (centralizer_le_normalizer hS hA h4 hL hwA)
    refine ⟨b, Subgroup.mem_subgroupOf.mp (hAT ▸ hb : b ∈ A.subgroupOf L),
      Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
    have := hbw k hk
    calc k * ((b : Q)⁻¹ * w) = (b : Q)⁻¹ * ((b : Q) * k * (b : Q)⁻¹) * w := by group
      _ = (b : Q)⁻¹ * (w * k * w⁻¹) * w := by rw [this]
      _ = (b : Q)⁻¹ * w * k := by group

end CFSG.Goldschmidt.Sec8

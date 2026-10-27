module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I137Transfer
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk)
open CFSG.LocalAnalysis.GLTheoremA (pQuotHom ker_pQuotHom chev_coe_normalizerMonoidHom
  nonempty_pQuot_equiv_map nonempty_pQuot_equiv_subgroupOf coprime_card_inf_ker_pQuotHom)

variable {G : Type} [Group G] [Finite G]

@[expose] def InnerOnMod (p : ℕ) {Y : Type} [Group Y] (L : Subgroup Y) (τ : MulAut Y) : Prop :=
  ∃ l ∈ L, ∀ y ∈ L, (l⁻¹ * y * l)⁻¹ * τ.symm y ∈ GLAPPrimeCoreOf p L

@[expose] noncomputable def imgK (K J : Subgroup G) : Subgroup (PQuot 3 K) :=
  (J.subgroupOf K).map (pQuotHom 3 K)

theorem isTypeWithCenter_of_pQuot_equiv {H : Type} [Group H] [Finite H] {X : Subgroup G} {Y : Subgroup H}
    (e : PQuot 3 X ≃* PQuot 3 Y)
    {Q : TauCeti.CFSGIndex → Prop} {z : ℕ} (h : S8.IsTypeWithCenter 3 X Q z) :
    S8.IsTypeWithCenter 3 Y Q z := by
  obtain ⟨hcat, hcard⟩ := h
  refine ⟨?_, ?_⟩
  · obtain ⟨i, hi, ⟨f⟩⟩ := hcat
    exact ⟨i, hi, ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).symm.trans f⟩⟩
  · rw [← hcard, ← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

theorem pQuot_equiv_imgK {K A : Subgroup G} (hAK : A ≤ K) :
    Nonempty (PQuot 3 A ≃* PQuot 3 (imgK K A)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : ¬ 3 ∣ Nat.card (pQuotHom 3 K).ker := by
    rw [ker_pQuotHom]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  obtain ⟨e₁⟩ := nonempty_pQuot_equiv_map Nat.prime_three hcop (A.subgroupOf K)
  obtain ⟨e₀⟩ := nonempty_pQuot_equiv_subgroupOf 3 hAK
  exact ⟨e₀.symm.trans e₁⟩

theorem barAut_symm_pQuotHom {K : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (K : Set G))
    (w : ↥K) :
    (barAut 3 K ⟨e, he⟩).symm (pQuotHom 3 K w) =
      pQuotHom 3 K (K.normalizerMonoidHom ⟨e⁻¹, Subgroup.inv_mem _ he⟩ w) := by
  rw [MulEquiv.symm_apply_eq]
  show (QuotientGroup.mk w : PQuot 3 K) =
    barAut 3 K ⟨e, he⟩ (QuotientGroup.mk (K.normalizerMonoidHom ⟨e⁻¹, Subgroup.inv_mem _ he⟩ w))
  rw [barAut_mk]
  congr 1
  apply Subtype.ext
  rw [chev_coe_normalizerMonoidHom, chev_coe_normalizerMonoidHom]
  dsimp only
  group

theorem mem_of_pQuot_mem_core {K J : Subgroup G} (hJK : J ≤ K) {z : G} (hz : z ∈ J)
    (hπ : (QuotientGroup.mk (⟨z, hJK hz⟩ : ↥K) : PQuot 3 K) ∈ GLAPPrimeCoreOf 3 (imgK K J)) :
    z ∈ GLAPPrimeCoreOf 3 J := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup ↥K := J.subgroupOf K with hA
  set ψ : ↥K →* PQuot 3 K := pQuotHom 3 K with hψ
  have hcop : Nat.Coprime 3 (Nat.card ↥(A ⊓ ψ.ker)) := coprime_card_inf_ker_pQuotHom Nat.prime_three K A
  obtain ⟨h, hh, hhz⟩ := CFSG.LocalAnalysis.GLTheoremA.I137Tr.mem_glaPPrimeCoreOf_iff.1 hπ
  have hmap := glaPPrimeCore_map_subgroupMap Nat.prime_three ψ A hcop
  have hh' : h ∈ Subgroup.map (ψ.subgroupMap A) (GLAPPrimeCore 3 ↥A) := by
    rw [hmap]
    exact hh
  obtain ⟨w, hw, hwh⟩ := Subgroup.mem_map.1 hh'
  set x : ↥A := ⟨⟨z, hJK hz⟩, Subgroup.mem_subgroupOf.2 hz⟩ with hx
  set u : ↥A := w⁻¹ * x with hu
  have hheq : h = (ψ.subgroupMap A) x := Subtype.ext hhz
  have hu_ker : u ∈ (ψ.subgroupMap A).ker := by
    have key : (ψ.subgroupMap A) w = (ψ.subgroupMap A) x := hwh.trans hheq
    rw [MonoidHom.mem_ker, hu, map_mul, map_inv, key, inv_mul_cancel]
  have hker_cop : Nat.Coprime 3 (Nat.card ↥(ψ.subgroupMap A).ker) := by
    have h1 : Nat.card ↥((ψ.subgroupMap A).ker.map A.subtype) = Nat.card ↥(ψ.subgroupMap A).ker :=
      Subgroup.card_map_of_injective A.subtype_injective
    have h2 : (ψ.subgroupMap A).ker.map A.subtype ≤ ψ.ker := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (ψ.subgroupMap A) y = 1 := hy
      have h3 : ((ψ.subgroupMap A y : ↥(Subgroup.map ψ A)) : PQuot 3 K) = 1 := by
        rw [hy']
        rfl
      exact h3
    have h3 : Nat.card ↥((ψ.subgroupMap A).ker.map A.subtype) ∣ Nat.card ↥ψ.ker :=
      Subgroup.card_dvd_of_le h2
    rw [← h1]
    refine Nat.Coprime.coprime_dvd_right h3 ?_
    rw [ker_pQuotHom]
    exact CFSG.pPrimeCore_coprime_card
  have hker_core : (ψ.subgroupMap A).ker ≤ GLAPPrimeCore 3 ↥A :=
    le_sSup ⟨inferInstance, hker_cop⟩
  have hxw : x ∈ GLAPPrimeCore 3 ↥A := by
    have hu' : u ∈ GLAPPrimeCore 3 ↥A := hker_core hu_ker
    have hx_eq : x = w * u := by rw [hu, mul_inv_cancel_left]
    rw [hx_eq]
    exact (GLAPPrimeCore 3 ↥A).mul_mem hw hu'
  have hzA : z ∈ GLAPPrimeCoreOf 3 J := by
    rw [← map_subtype_glaPPrimeCoreOf_subgroupOf 3 hJK]
    refine Subgroup.mem_map.2 ⟨x, ?_, rfl⟩
    exact CFSG.LocalAnalysis.GLTheoremA.I137Tr.mem_glaPPrimeCoreOf_iff.2 ⟨x, hxw, rfl⟩
  exact hzA

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end

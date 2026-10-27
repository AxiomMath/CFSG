module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxMain
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigDich

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup

variable {X : Type} [Group X]

theorem factorization_two_le_of_normalizer [Finite X] {Y K L : Subgroup X} (hKY : K ≤ Y)
    (hLY : L ≤ Y) (hY : Y ≤ normalizer ((GH74.GLS.pPrimeCoreOf 2 Y ⊔ K : Subgroup X) : Set X))
    (hgen : ∀ N : Subgroup X, K ≤ N → L ≤ normalizer (N : Set X) → L ≤ N) :
    (Nat.card L).factorization 2 ≤ (Nat.card K).factorization 2 := by
  set O := GH74.GLS.pPrimeCoreOf 2 Y with hOdef
  have hLN : L ≤ O ⊔ K := hgen _ le_sup_right (hLY.trans hY)
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, GH74.GLS.pPrimeCoreOf, card_map_of_injective Y.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hKO : K ≤ normalizer (O : Set X) := by
    intro k hk
    rw [mem_normalizer_iff_map_conj_eq]
    have hk' : (⟨k, hKY hk⟩ : ↥Y) ∈ normalizer ((pPrimeCore 2 ↥Y : Subgroup ↥Y) : Set ↥Y) := by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top _
    exact (mem_normalizer_iff_map_conj_eq.mp
      (mem_normalizer_map_subtype' hk'))
  have hcard := Sol78.card_sup_mul_card_inf' hKO
  have hpos : ∀ A : Subgroup X, Nat.card A ≠ 0 := fun A => Nat.card_pos.ne'
  have hinfodd : (Nat.card ↥(K ⊓ O)).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h2
    have h3 : Nat.card ↥(K ⊓ O) ∣ Nat.card O := card_dvd_of_le inf_le_right
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr (h2.trans h3))
  have hOz : (Nat.card O).factorization 2 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h2
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
  have h1 : (Nat.card ↥(K ⊔ O) * Nat.card ↥(K ⊓ O)).factorization 2 =
      (Nat.card K * Nat.card O).factorization 2 := by rw [hcard]
  rw [Nat.factorization_mul (hpos _) (hpos _), Nat.factorization_mul (hpos _) (hpos _)] at h1
  simp only [Finsupp.add_apply] at h1
  rw [hinfodd, hOz, add_zero, add_zero] at h1
  have h2 : (Nat.card L).factorization 2 ≤ (Nat.card ↥(K ⊔ O)).factorization 2 :=
    (Nat.factorization_le_iff_dvd (hpos _) (hpos _)).mpr
      (card_dvd_of_le (hLN.trans (sup_comm O K).le)) 2
  omega

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem fixedLayer_facts {u : X} (hu2 : IsPGroup 2 (zpowers u))
    (hut : u ∈ centralizer ({t} : Set X)) (huK : u ∈ UnbalancedLayer.coreActionKernel J) :
    GSLit.fixedLayer J (zpowers u) ≤ J ∧
      GSLit.fixedLayer J (zpowers u) ≤ centralizer ({u} : Set X) ∧
      FooteLit.IsTwoComponentIn (GSLit.fixedLayer J (zpowers u))
        (centralizer ((zpowers t ⊔ zpowers u : Subgroup X) : Set X)) ∧
      Nonempty (↥(GSLit.fixedLayer J (zpowers u)) ⧸ pPrimeCore 2 ↥(GSLit.fixedLayer J (zpowers u))
        ≃* alternatingGroup (Fin n)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({t} : Set X) with hC
  set Ju := GSLit.fixedLayer J (zpowers u) with hJu
  have hJC : J ≤ C := S.pair.1.2.1
  have hJpc : IsPComponent 2 (J.subgroupOf C) := S.pair.1.2.2.1
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJC).mp hJpc).2.2
  have hJsub : (J.subgroupOf C).IsSubnormal := hJpc.choose_spec.2.1
  have hE : zpowers u ≤ UnbalancedLayer.coreActionKernel J := zpowers_le.mpr huK
  have hEC : zpowers u ≤ C := zpowers_le.mpr hut
  have hle := GSLit.fixedLayer_le_inf J (zpowers u)
  have hJuJ : Ju ≤ J := hle.trans inf_le_left
  have hJuu : Ju ≤ centralizer ({u} : Set X) := by
    have h1 := hle.trans inf_le_right
    rwa [UnbalancedLayer.centralizer_zpowers_eq] at h1
  obtain ⟨hsup, hcore⟩ := GSLit.fixedLayer_sup_pPrimeCore hJq hE hu2
  have hpc := GSLit.fixedLayer_isPComponent hJC hJsub hEC hE hu2 hJq
  have hcen : centralizer ((zpowers t ⊔ zpowers u : Subgroup X) : Set X) =
      C ⊓ centralizer ((zpowers u : Subgroup X) : Set X) := by
    rw [centralizer_sup_zpowers, centralizer_zpowers_eq', UnbalancedLayer.centralizer_zpowers_eq]
  refine ⟨hJuJ, hJuu, ⟨?_, ?_⟩, ?_⟩
  · rw [hcen]
    exact hle.trans (inf_le_inf_right _ hJC)
  · rwa [hcen]
  set Y := Ju.subgroupOf J with hYdef
  have hY : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 ↥J)).comp Y.subtype) := by
    have h1 : Y ⊔ pPrimeCore 2 ↥J = ⊤ := by
      have h2 : (Ju ⊔ (pPrimeCore 2 ↥J).map J.subtype).subgroupOf J = ⊤ := by
        rw [hsup]
        exact subgroupOf_self J
      rwa [subgroupOf_sup hJuJ (map_subtype_le _), subgroupOf_map_subtype_self] at h2
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore 2 ↥J))) h1
    rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  obtain ⟨φ, -⟩ := UnbalancedGS.FixedPrimeLayer.exists_quotient_mulEquiv Y hY
  exact ⟨(Sol78.coreQuotCongr (subgroupOfEquivOfLe hJuJ)).symm.trans (φ.trans e)⟩

end Sig36

end CFSG.ComponentClassification.SolMax

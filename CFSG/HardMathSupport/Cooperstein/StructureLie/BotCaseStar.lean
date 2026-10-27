module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.HardMathSupport.Cooperstein.Proving
open scoped commutatorElement

section Abstract

variable {Y H : Type*} [Group Y] [Finite Y] [Group H]

theorem ker_le_of_hD (ψ : Y →* H) (K : Subgroup Y) [hKn : K.Normal]
    (hperf : commutator ↥K = ⊤) (h2 : ∀ y : Y, ∃ e : ℕ, y ^ 2 ^ e ∈ K)
    (hO : CFSG.pCore 2 Y = ⊥)
    (hD : ∀ d ∈ K, ψ d = 1 → d ∈ Subgroup.centralizer (K : Set Y)) : ψ.ker ≤ K := by
  have hKK : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp ⟨hperf⟩
  set C := Subgroup.centralizer (K : Set Y) with hC
  have hodd := Coordinator.StarAux.odd_card_centralizer K h2 hO
  have hNK : ⁅ψ.ker, K⁆ ≤ ψ.ker ⊓ K := Subgroup.commutator_le_inf _ _
  have hKz : ψ.ker ⊓ K ≤ C := fun d hd => hD d hd.2 hd.1
  have hbot : ⁅⁅ψ.ker, K⁆, K⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅ψ.ker, K⁆, K⁆ ≤ ⁅C, K⁆ := Subgroup.commutator_mono (hNK.trans hKz) le_rfl
      _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr le_rfl
  have hNC : ψ.ker ≤ C := Coordinator.StarAux.le_centralizer_of_commutator_commutator_eq_bot hKK hbot
  intro n hn
  have hnC := hNC hn
  have h1 : orderOf n ∣ Nat.card ↥C := by
    rw [← Subgroup.orderOf_mk n hnC]
    exact orderOf_dvd_natCard _
  have hodd' : Odd (orderOf n) := Odd.of_dvd_nat hodd h1
  obtain ⟨e, he⟩ := h2 n
  by_cases ho : orderOf n = 1
  · rw [orderOf_eq_one_iff.mp ho]; exact K.one_mem
  · have hlt : 1 < orderOf n := by
      have := orderOf_pos n
      omega
    have hcop : Nat.Coprime (2 ^ e) (orderOf n) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd')
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
    have : n = (n ^ 2 ^ e) ^ k := by
      rw [← pow_mul, ← pow_mod_orderOf, hk, pow_one]
    rw [this]
    exact K.pow_mem he k

end Abstract

section Star

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}
variable (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L) (hSL : S ≤ Subgroup.normalizer (L : Set G))

include hA hL hSL

theorem centralizer_le_sup_twoCore :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤ L ⊔ pCoreOf 2 (L ⊔ S) := by
  have hPV := sup_le_normalizer_blockV S L
  have hS2 : IsPGroup 2 S := hA.twoRadical.isPGroup
  have hLc : IsTwoPrimeComponent (L ⊔ S) L :=
    isTwoPrimeComponent_sup hL.toIsTwoPrimeComponent hA.twoRadical.1 hS2 hSL
  have hq := hLc.component.2.2
  let ρ' : ↥(L ⊔ S) →* ↥(autOn (L ⊔ S) (blockV S L)) :=
    (Setup.rho (blockV S L) (L ⊔ S) hPV).codRestrict _ fun l =>
      (Setup.range_rho hPV).le ⟨l, rfl⟩
  have hρ'1 : ∀ l : ↥(L ⊔ S), ρ' l = 1 ↔ (l : G) ∈ Subgroup.centralizer (blockV S L : Set G) := by
    intro l
    rw [← Setup.rho_eq_one_iff hPV l]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker : CFSG.pCore 2 ↥(L ⊔ S) ≤ ρ'.ker := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 (L ⊔ S) := mem_pCoreOf_iff.mpr ⟨x, hx, rfl⟩
    exact (hρ'1 x).mpr (AscTenThree.le_centralizer_omegaOneCenterOf_self _ hx')
  let ψ : ↥(L ⊔ S) ⧸ CFSG.pCore 2 ↥(L ⊔ S) →* ↥(autOn (L ⊔ S) (blockV S L)) :=
    QuotientGroup.lift _ ρ' hker
  have hnormL : (L.subgroupOf (L ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSL)
  have hKn : (barM (L ⊔ S) L).Normal :=
    hnormL.map (QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S))) (QuotientGroup.mk'_surjective _)
  have hcen := barM_inf_le_center_of_core_le hLc
    (le_sup_left.trans (le_normalizer_centralizer_blockV S L))
    (inf_le_right.trans (AscTenThree.le_centralizer_omegaOneCenterOf_self _))
    (not_le_centralizer_blockV hA hL hSL)
  have hK := ker_le_of_hD ψ (barM (L ⊔ S) L) hq.1
    (by
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨e, he⟩ := exists_pow_mem_sup_subgroupOf hS2 hSL y
      exact ⟨e, ⟨y ^ 2 ^ e, he, by simp⟩⟩)
    StarAux.pCore_quotient_pCore_eq_bot
    (by
      intro d hd hψd
      obtain ⟨y, hy, rfl⟩ := hd
      have hyC : (y : G) ∈ Subgroup.centralizer (blockV S L : Set G) :=
        (hρ'1 y).mp (by simpa [ψ] using hψd)
      obtain ⟨z, hz, hzy⟩ := hcen
        (show QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S)) y ∈
          barM (L ⊔ S) (L ⊓ Subgroup.centralizer (blockV S L : Set G)) from
        ⟨y, ⟨Subgroup.mem_subgroupOf.mp hy, hyC⟩, rfl⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := Subgroup.mem_center_iff.mp hz ⟨k, hk⟩
      rw [← hzy]
      have h' := congrArg Subtype.val this
      exact h')
  rintro c ⟨hcM, hcC⟩
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S)) (⟨c, hcM⟩ : ↥(L ⊔ S)) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact (hρ'1 ⟨c, hcM⟩).mpr hcC
  obtain ⟨l, hl, hlc⟩ := hK hmem
  have hq1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(L ⊔ S)) (l⁻¹ * ⟨c, hcM⟩) = 1 := by
    rw [map_mul, map_inv, hlc, inv_mul_cancel]
  have h1 := coe_mem_pCoreOf_two_of_mk_eq_one _ hq1
  have e : c = (l : G) * ((l⁻¹ * ⟨c, hcM⟩ : ↥(L ⊔ S)) : G) := by simp
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) h1

omit hSL in
theorem pCoreOf_le_pCoreOf_sup_bot : pCoreOf 2 X ≤ pCoreOf 2 (L ⊔ S) := by
  have hX : L ⊔ S ≤ X := sup_le hL.le hA.twoRadical.1
  have hQS : pCoreOf 2 X ≤ L ⊔ S := hA.twoCore_le.trans le_sup_right
  exact normal_pGroup_le_pCoreOf 2 _ _ hQS
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQS).mpr
        (hX.trans (localGroup_le_normalizer_pCoreOf 2 X)))
      (pCoreOf_isPGroup 2 X)

theorem inf_sup_centralizer_le (h0 : S ⊓ L ≤ pCoreOf 2 X) {x : G} (hxS : x ∈ S)
    (hx : x ∈ L ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G)) :
    x ∈ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) := by
  set Q := pCoreOf 2 (L ⊔ S) with hQ
  have hQS : Q ≤ S := twoCore_sup_le hA hL hSL
  have hQM : Q ≤ L ⊔ S := pCoreOf_le 2 _
  have hQC : Q ≤ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) :=
    le_inf hQM (AscTenThree.le_centralizer_omegaOneCenterOf_self _)
  have hMN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSL
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQM.trans hMN
  have hCN : (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) ≤
      Subgroup.normalizer (L : Set G) := inf_le_left.trans hMN
  set C := (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) with hC
  have hxC : x ∈ ((C ⊔ L : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right C L hCN] at hxC
  obtain ⟨c, hc, l, hl, rfl⟩ := hxC
  have hcQ : c ∈ ((Q ⊔ L : Subgroup G) : Set G) := by
    rw [sup_comm]; exact centralizer_le_sup_twoCore hA hL hSL hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Q L hQN] at hcQ
  obtain ⟨q, hq, l', hl', rfl⟩ := hcQ
  have hl'l : l' * l ∈ S ⊓ L := by
    refine ⟨?_, L.mul_mem hl' hl⟩
    have h1 := S.mul_mem (S.inv_mem (hQS hq)) hxS
    simpa [mul_assoc] using h1
  have hlQ : l' * l ∈ Q := pCoreOf_le_pCoreOf_sup_bot hA hL (h0 hl'l)
  have := Q.mul_mem hq hlQ
  have e : q * l' * l = q * (l' * l) := mul_assoc _ _ _
  show q * l' * l ∈ C
  rw [e]
  exact hQC this

end Star

end CFSG.HardMathSupport.Cooperstein.StructureLie

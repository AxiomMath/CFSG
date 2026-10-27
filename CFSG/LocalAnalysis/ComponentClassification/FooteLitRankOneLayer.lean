module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitStep

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_twoLayerIn {Y : Subgroup G} {g : G} (hg : g ∈ normalizer (Y : Set G)) :
    g ∈ normalizer ((twoLayerIn Y : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (pLayer ↥Y 2).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  rw [mem_normalizer_iff]
  intro x
  refine ⟨fun hx => Walter.conj_mem_map_of_characteristic hg hx, fun hx => ?_⟩
  have := Walter.conj_mem_map_of_characteristic (inv_mem hg) hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem le_twoLayerOf_of_isPComponent {a b : G} (ha : orderOf a = 2) (hab : a * b = b * a)
    {T : Subgroup G} (hTC : T ≤ centralizer ({b} : Set G) ⊓ centralizer ({a} : Set G))
    (hT : IsPComponent 2 (T.subgroupOf (centralizer ({b} : Set G) ⊓
      centralizer ({a} : Set G)))) : T ≤ twoLayerOf b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cb := centralizer ({b} : Set G) with hCb
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  set a' : Cb := ⟨a, haCb⟩
  have ha'2 : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena : centralizer ({a'} : Set Cb) = (Cb ⊓ centralizer ({a} : Set G)).subgroupOf Cb := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf]
    exact ⟨fun h => ⟨y.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)⟩,
      fun h => Subtype.ext (mem_centralizer_singleton_iff.mp h.2)⟩
  have hTCb : T ≤ Cb := hTC.trans inf_le_left
  have hK'C : T.subgroupOf Cb ≤ centralizer ({a'} : Set Cb) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hTC (mem_subgroupOf.mp hy))
  have hK'pc : IsPComponent 2 ((T.subgroupOf Cb).subgroupOf (centralizer ({a'} : Set Cb))) := by
    rw [hcena, isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two]
    exact hT
  have hle := le_pLayer_of_isPComponent_centralizer_singleton ha'2 hK'C hK'pc
  intro x hx
  exact ⟨⟨x, hTCb hx⟩, hle (show (⟨x, hTCb hx⟩ : Cb) ∈ T.subgroupOf Cb from hx), rfl⟩

theorem mem_normalizer_twoLayerOf {b g : G} (hg : g ∈ centralizer ({b} : Set G)) :
    g ∈ normalizer ((twoLayerOf b : Subgroup G) : Set G) :=
  mem_normalizer_twoLayerIn (le_normalizer hg)

theorem mem_twoLayerOf_of_mem_sup {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : a * b = b * a) {B₁ B₂ : Subgroup G} (hB₁ : IsTwoComponentAt a B₁)
    (hB₂ : IsTwoComponentAt a B₂) (hb₁ : b ∈ coreActionKernel B₁)
    (hb₂ : b ∈ coreActionKernel B₂) (haB : a ∈ B₁ ⊔ B₂) : a ∈ twoLayerOf b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ca := centralizer ({a} : Set G) with hCa
  set Cb := centralizer ({b} : Set G) with hCb
  set Oa := oddCoreOfCentralizer a with hOa
  have hbCa : b ∈ Ca := mem_centralizer_singleton_iff.mpr hab.symm
  have haCb : a ∈ Cb := mem_centralizer_singleton_iff.mpr hab
  have key : ∀ {B : Subgroup G}, IsTwoComponentAt a B → b ∈ coreActionKernel B →
      UnbalancedGS.gsFixedLayer B b ≤ twoLayerOf b ⊓ Cb ∧
        B ≤ UnbalancedGS.gsFixedLayer B b ⊔ Oa := by
    intro B hB hbB
    obtain ⟨-, hBa, hBpc⟩ := hB
    have hBq := isQuasisimple_quotient_of_isPComponent hBa hBpc
    have hBsub : (B.subgroupOf Ca).IsSubnormal := by
      obtain ⟨-, -, hs, -, -⟩ := id hBpc
      exact hs
    have hTpc := gsFixedLayer_isPComponent hBa hBsub hbCa hb hbB.1 hBq hbB.2
    have hTle : UnbalancedGS.gsFixedLayer B b ≤ B ⊓ Cb := UnbalancedGS.gsFixedLayer_le_inf B b
    have hTC : UnbalancedGS.gsFixedLayer B b ≤ Cb ⊓ Ca :=
      le_inf (hTle.trans inf_le_right) (hTle.trans (inf_le_left.trans hBa))
    have hTpc' : IsPComponent 2 ((UnbalancedGS.gsFixedLayer B b).subgroupOf (Cb ⊓ Ca)) := by
      rw [inf_comm]; exact hTpc
    refine ⟨le_inf (le_twoLayerOf_of_isPComponent ha hab hTC hTpc') (hTle.trans inf_le_right),
      ?_⟩
    have hsup := gsFixedLayer_sup_map_pPrimeCore hb hBq hbB.1 hbB.2
    have hOB : oddCoreIn B ≤ Oa := UGSChain.map_pPrimeCore_le_of_isPComponent hBa hBpc
    calc B = UnbalancedGS.gsFixedLayer B b ⊔ oddCoreIn B := hsup.symm
      _ ≤ UnbalancedGS.gsFixedLayer B b ⊔ Oa := sup_le_sup_left hOB _
  obtain ⟨hT₁, hB₁T⟩ := key hB₁ hb₁
  obtain ⟨hT₂, hB₂T⟩ := key hB₂ hb₂
  set T := UnbalancedGS.gsFixedLayer B₁ b ⊔ UnbalancedGS.gsFixedLayer B₂ b with hT
  have hTL : T ≤ twoLayerOf b ⊓ Cb := sup_le hT₁ hT₂
  have hTCa : T ≤ Ca := sup_le
    ((UnbalancedGS.gsFixedLayer_le_inf B₁ b).trans (inf_le_left.trans hB₁.2.1))
    ((UnbalancedGS.gsFixedLayer_le_inf B₂ b).trans (inf_le_left.trans hB₂.2.1))
  have haTO : a ∈ T ⊔ Oa := by
    have h1 : B₁ ⊔ B₂ ≤ T ⊔ Oa :=
      sup_le (hB₁T.trans (sup_le_sup_right le_sup_left _))
        (hB₂T.trans (sup_le_sup_right le_sup_right _))
    exact h1 haB
  have hTnorm : T ≤ normalizer ((Oa : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreOfCentralizer (hTCa hx)
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T Oa hTnorm] at haTO
  obtain ⟨x, hx, o, ho, hxo⟩ := haTO
  have hxCb : x ∈ Cb := (hTL hx).2
  have hoCb : o ∈ Cb := by
    have h1 : o = x⁻¹ * a := by rw [← hxo]; group
    rw [h1]
    exact mul_mem (inv_mem hxCb) haCb
  have hmem : a ∈ (Oa ⊓ Cb) ⊔ twoLayerOf b := by
    rw [← hxo]
    exact mul_mem (mem_sup_right (hTL hx).1) (mem_sup_left (mem_inf.mpr ⟨ho, hoCb⟩))
  have hodd : Odd (Nat.card ↥(Oa ⊓ Cb)) :=
    Odd.of_dvd_nat (odd_card_oddCoreOfCentralizer a) (card_dvd_of_le inf_le_left)
  exact mem_of_two_element_of_mem_sup (fun y hy => mem_normalizer_twoLayerOf (mem_inf.mp hy).2)
    (by rw [oddResidualIn_eq_bot_of_odd hodd]; exact bot_le) hmem ⟨1, by rw [ha, pow_one]⟩

theorem mem_gsFixedLayer_self {z a : G} {A : Subgroup G} (hA : IsTwoComponentAt z A)
    (haA : a ∈ A) (ha : orderOf a = 2) (haK : a ∈ coreActionKernel A) :
    a ∈ UnbalancedGS.gsFixedLayer A a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hAz, hApc⟩ := hA
  have hAq := isQuasisimple_quotient_of_isPComponent hAz hApc
  set T := UnbalancedGS.gsFixedLayer A a with hT
  set Ca := centralizer ({a} : Set G) with hCa
  have hsup : T ⊔ oddCoreIn A = A := gsFixedLayer_sup_map_pPrimeCore ha hAq haK.1 haK.2
  have hTle : T ≤ A ⊓ Ca := UnbalancedGS.gsFixedLayer_le_inf A a
  have hTnorm : T ≤ normalizer ((oddCoreIn A : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_oddCoreIn (le_normalizer ((hTle.trans inf_le_left) hx))
  have h1 : a ∈ T ⊔ oddCoreIn A := hsup.symm ▸ haA
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right T (oddCoreIn A) hTnorm] at h1
  obtain ⟨x, hx, o, ho, hxo⟩ := h1
  have hoCa : o ∈ Ca := by
    have e : o = x⁻¹ * a := by rw [← hxo]; group
    rw [e]
    exact mul_mem (inv_mem (hTle hx).2) (mem_centralizer_singleton_iff.mpr rfl)
  have hmem : a ∈ (oddCoreIn A ⊓ Ca) ⊔ T := by
    rw [← hxo]
    exact mul_mem (mem_sup_right hx) (mem_sup_left (mem_inf.mpr ⟨ho, hoCa⟩))
  have hodd : Odd (Nat.card ↥(oddCoreIn A ⊓ Ca)) :=
    Odd.of_dvd_nat (odd_card_oddCoreIn A) (card_dvd_of_le inf_le_left)
  have hN : oddCoreIn A ⊓ Ca ≤ normalizer ((T : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_twoLayerIn (le_normalizer (mem_inf.mpr
      ⟨map_subtype_le _ (mem_inf.mp hy).1, (mem_inf.mp hy).2⟩))
  exact mem_of_two_element_of_mem_sup hN
    (by rw [oddResidualIn_eq_bot_of_odd hodd]; exact bot_le) hmem ⟨1, by rw [ha, pow_one]⟩

theorem footeStep_cases_index_of_maximal (hLB : FooteLBalanceInput) {a b : G}
    {L : Subgroup G} (hmax : FootePointedMaximal a L) (hb : orderOf b = 2)
    (hab : a * b = b * a) (hne : a ≠ b) (hbL : b ∈ coreActionKernel L) :
    ∃ B : Subgroup G, IsTwoComponentAt b B ∧ FootePointedStep a L b B ∧
      Nonempty (L ⧸ Open.fusionZStar L ≃* B ⧸ Open.fusionZStar B) ∧
      ((conjugate B a = B ∧ footeFixed L b = B) ∨
        (conjugate B a ≠ B ∧ UnbalancedGS.gsFixedLayer L b =
          twoLayerIn ((B ⊔ conjugate B a) ⊓ centralizer ({a} : Set G)) ∧
          (pPrimeCore 2 (UnbalancedGS.gsFixedLayer L b)).index ≤ (pPrimeCore 2 B).index)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL := hmax.1
  obtain ⟨B, hBb, -, -, hcl, hcase⟩ := exists_footeStep hLB hL hb hab hne hbL
  have hstep : FootePointedStep a L b B := ⟨hL, hBb, hab, hne, hbL, hcl⟩
  obtain ⟨eLB⟩ := hmax.equiv_of_step hstep
  refine ⟨B, hBb, hstep, ⟨eLB⟩, ?_⟩
  obtain ⟨-, hLa, hLpc⟩ := hL
  have hLq := isQuasisimple_quotient_of_isPComponent hLa hLpc
  have hTL : UnbalancedGS.gsFixedLayer L b ≤ L :=
    (UnbalancedGS.gsFixedLayer_le_inf L b).trans inf_le_left
  rcases hcase with ⟨hBa, hBres, -⟩ | ⟨-, -, hiso⟩ | ⟨hBa, hT, hidx⟩
  · left
    refine ⟨hBa, le_antisymm ?_ ?_⟩
    · have h1 := (le_conjClosure (footeFixed L b) (twoLayerOf b)).trans hcl.le
      rwa [hBa, sup_idem] at h1
    · rw [hBres, footeFixed_eq_oddResidualIn]
      exact oddResidualIn_mono (sup_le_sup_right (UnbalancedGS.gsFixedLayer_le_inf L b) _)
  · exfalso
    obtain ⟨-, eT, -⟩ := restriction_quotient_mulEquiv hTL
      (gsFixedLayer_sup_map_pPrimeCore hb hLq hbL.1 hbL.2)
    obtain ⟨eZ⟩ := nonempty_fusionZStar_equiv_of_quotient_equiv eT
    exact hiso.false (eZ.trans eLB)
  · exact Or.inr ⟨hBa, hT, hidx⟩

end CFSG.ComponentClassification.FooteLit

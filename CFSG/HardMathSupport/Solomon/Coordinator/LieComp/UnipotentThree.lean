module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.Interface
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator

private theorem commute_zpowers_of_mem_fixSub_conj {S : Type} [Group S] {s c : S}
    (hc : c ∈ Lemma510Ns.fixSub (MulAut.conj s)) {h : S} (hh : h ∈ Subgroup.zpowers s) :
    c * h = h * c := by
  have hcs : Commute c s := by
    have := Lemma510Ns.mem_fixSub.1 hc
    rw [MulAut.conj_apply] at this
    show c * s = s * c
    calc c * s = (s * c * s⁻¹) * s := by rw [this]
      _ = s * c := by group
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  exact (hcs.zpow_right k).eq

private theorem fixSub_conj_le_normalizer_zpowers {S : Type} [Group S] (s : S) :
    Lemma510Ns.fixSub (MulAut.conj s) ≤ Subgroup.normalizer (Subgroup.zpowers s : Set S) := by
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hcomm : ∀ {x : S}, x ∈ Subgroup.zpowers s → c * x * c⁻¹ = x := fun {x} hx => by
    rw [commute_zpowers_of_mem_fixSub_conj hc hx]
    group
  constructor
  · intro hh
    rw [hcomm hh]
    exact hh
  · intro hh
    have e := hcomm hh
    have hy : h = c * h * c⁻¹ := by
      calc h = c⁻¹ * (c * h * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * h * c⁻¹) * c⁻¹) * c := by rw [e]
        _ = c * h * c⁻¹ := by group
    rw [hy]
    exact hh

private theorem conj_mem_fixSub_conj_of_mem_normalizer {S : Type} [Group S] {s n c : S}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers s : Set S))
    (hc : c ∈ Lemma510Ns.fixSub (MulAut.conj s)) :
    n * c * n⁻¹ ∈ Lemma510Ns.fixSub (MulAut.conj s) := by
  have ht : n⁻¹ * s * n ∈ Subgroup.zpowers s := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) s).1 (Subgroup.mem_zpowers s)
    simpa using this
  have hct := commute_zpowers_of_mem_fixSub_conj hc ht
  rw [Lemma510Ns.mem_fixSub, MulAut.conj_apply]
  generalize hT : n⁻¹ * s * n = t at ht hct
  have hs : s = n * t * n⁻¹ := by
    rw [← hT]
    group
  rw [hs]
  calc n * t * n⁻¹ * (n * c * n⁻¹) * (n * t * n⁻¹)⁻¹ = n * (t * c * t⁻¹) * n⁻¹ := by group
    _ = n * (c * t * t⁻¹) * n⁻¹ := by rw [← hct]
    _ = n * c * n⁻¹ := by group

private theorem gLAPPrimeCore_three_eq_bot_of_constrained {G : Type*} [Group G] [Finite G]
    (N : Subgroup G)
    (hcen : ∀ h ∈ N, (∀ r ∈ pCoreOf 3 N, h * r = r * h) → h ∈ pCoreOf 3 N) :
    GLAPPrimeCore 3 ↥N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  show CFSG.pPrimeCore 3 ↥N = ⊥
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro K hKn hKc
  have hBn : (CFSG.pCore 3 ↥N).Normal := CFSG.pCore_normal
  have hBp : IsPGroup 3 (CFSG.pCore 3 ↥N) := CFSG.pCore_isPGroup
  have hdisj : K ⊓ CFSG.pCore 3 ↥N = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    obtain ⟨n, hn⟩ := hBp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ hKc.symm
  rw [eq_bot_iff]
  intro k hk
  have hcomm : ∀ b ∈ CFSG.pCore 3 ↥N, k * b = b * k := by
    intro b hb
    have h1 : k * b * k⁻¹ * b⁻¹ ∈ K ⊓ CFSG.pCore 3 ↥N := by
      refine ⟨?_, ?_⟩
      · have h2 := hKn.conj_mem k⁻¹ (K.inv_mem hk) b
        have h3 : k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) := by group
        rw [h3]
        exact K.mul_mem hk h2
      · exact (CFSG.pCore 3 ↥N).mul_mem (hBn.conj_mem b hb k) ((CFSG.pCore 3 ↥N).inv_mem hb)
    rw [hdisj, Subgroup.mem_bot] at h1
    calc k * b = (k * b * k⁻¹ * b⁻¹) * (b * k) := by group
      _ = b * k := by rw [h1, one_mul]
  have hmem := hcen k k.2 (by
    rintro r ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hcomm b hb))
  obtain ⟨b, hb, hbk⟩ := hmem
  have hbk' : b = k := Subtype.ext hbk
  rw [hbk'] at hb
  have hkb : k ∈ K ⊓ CFSG.pCore 3 ↥N := ⟨hk, hb⟩
  rwa [hdisj] at hkb

private theorem conj_mem_pCoreOf_three {G : Type*} [Group G] (N : Subgroup G) {c q : G}
    (hc : c ∈ N) (hq : q ∈ pCoreOf 3 N) : c * q * c⁻¹ ∈ pCoreOf 3 N := by
  obtain ⟨b, hb, rfl⟩ := hq
  exact ⟨⟨c, hc⟩ * b * ⟨c, hc⟩⁻¹, CFSG.pCore_normal.conj_mem b hb ⟨c, hc⟩, rfl⟩

theorem noThreeComponents_of_conj (hQ : YS08.LieQ.LieQConstrainedInner 3) {S : Type} [Group S]
    [Finite S] (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hS : IsChevOfChar 3 S)
    {s : S} (hs1 : s ≠ 1) (hs3 : s ^ 3 = 1) : NoThreeComponents (MulAut.conj s) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro J hJ
  have hQ1 : Subgroup.zpowers s ≠ ⊥ := fun h => hs1 (Subgroup.zpowers_eq_bot.1 h)
  have hQ3 : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hs3 hs1]; norm_num)
  have hcen := hQ S hs hna hS (Subgroup.zpowers s) hQ1 hQ3
  set N : Subgroup S := Subgroup.normalizer (Subgroup.zpowers s : Set S)
  have hCN : Lemma510Ns.fixSub (MulAut.conj s) ≤ N := fixSub_conj_le_normalizer_zpowers s
  have hCnorm : ((Lemma510Ns.fixSub (MulAut.conj s)).subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCN]
    intro c n hc hn
    exact conj_mem_fixSub_conj_of_mem_normalizer hn hc
  have hsubN : IsSubnormal J N :=
    (hJ.2.1).trans (IsSubnormal.step hCN hCnorm (IsSubnormal.refl N))
  have hJN : J ≤ N := hsubN.le
  have hbotN : GLAPPrimeCore 3 ↥N = ⊥ := gLAPPrimeCore_three_eq_bot_of_constrained N hcen
  have hbotNof : GLAPPrimeCoreOf 3 N = ⊥ := by
    show (GLAPPrimeCore 3 ↥N).map N.subtype = ⊥
    rw [hbotN, Subgroup.map_bot]
  have hle := glaPPrimeCoreOf_le_of_isSubnormal 3 hsubN
  rw [hbotNof, le_bot_iff] at hle
  have hbotJ : GLAPPrimeCore 3 ↥J = ⊥ := by
    have h1 : (GLAPPrimeCore 3 ↥J).map J.subtype = ⊥ := hle
    rwa [Subgroup.map_eq_bot_iff, Subgroup.ker_subtype, le_bot_iff] at h1
  have hqJ : CFSG.Open.IsQuasisimple ↥J := by
    have hq := isQuasisimple_quotient_of_glaPComponent hJ
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hbotJ).trans QuotientGroup.quotientBot).symm hq
  have hcomp : CFSG.IsComponent (J.subgroupOf N) := by
    rw [CFSG.isComponent_iff_open]
    exact ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib hsubN.subgroupOf,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJN) hqJ⟩
  exact CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_le (C := N)
    (Q := pCoreOf 3 N) (p := 3) (Subgroup.map_subtype_le _)
    (CFSG.pCore_isPGroup.map N.subtype) (fun c hc q hq => conj_mem_pCoreOf_three N hc hq) hcen
    (J.subgroupOf N) hcomp

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

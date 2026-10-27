module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292LinUniDefs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1111b
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.CenterCyclic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open
open scoped commutatorElement

namespace I291Zero

section Generic

theorem quasisimple_nontrivial {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K) :
    Nontrivial K := by
  haveI : Nontrivial (K ⧸ Subgroup.center K) := hK.2.toNontrivial
  exact Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center K))

theorem normal_le_center_of_quasisimple {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (N : Subgroup K) [N.Normal] (hN : N ≠ ⊤) :
    N ≤ Subgroup.center K := by
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2
  have hNm : (N.map (QuotientGroup.mk' (Subgroup.center K))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center K))) with h | h
  · intro n hn
    have hmem : QuotientGroup.mk' (Subgroup.center K) n ∈
        N.map (QuotientGroup.mk' (Subgroup.center K)) :=
      Subgroup.mem_map_of_mem _ hn
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff n).1 hmem
  · exfalso
    apply hN
    have hdec : ∀ a : K, ∃ n ∈ N, ∃ c ∈ Subgroup.center K, a = n * c := by
      intro a
      have ha : QuotientGroup.mk' (Subgroup.center K) a ∈
          N.map (QuotientGroup.mk' (Subgroup.center K)) := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hna⟩ := Subgroup.mem_map.1 ha
      refine ⟨n, hn, n⁻¹ * a, ?_, by group⟩
      exact (QuotientGroup.eq (s := Subgroup.center K)).1 hna
    have hcomm : ∀ a b : K, ⁅a, b⁆ ∈ N := by
      intro a b
      obtain ⟨n₁, hn₁, c₁, hc₁, rfl⟩ := hdec a
      obtain ⟨n₂, hn₂, c₂, hc₂, rfl⟩ := hdec b
      have hc₁' : ∀ g : K, c₁ * g = g * c₁ := fun g => (Subgroup.mem_center_iff.1 hc₁ g).symm
      have hc₂' : ∀ g : K, c₂ * g = g * c₂ := fun g => (Subgroup.mem_center_iff.1 hc₂ g).symm
      have key : ⁅n₁ * c₁, n₂ * c₂⁆ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by
        rw [commutatorElement_def]
        calc n₁ * c₁ * (n₂ * c₂) * (n₁ * c₁)⁻¹ * (n₂ * c₂)⁻¹
            = n₁ * (c₁ * n₂) * c₂ * c₁⁻¹ * n₁⁻¹ * c₂⁻¹ * n₂⁻¹ := by group
          _ = n₁ * (n₂ * c₁) * c₂ * c₁⁻¹ * n₁⁻¹ * c₂⁻¹ * n₂⁻¹ := by rw [hc₁' n₂]
          _ = n₁ * n₂ * (c₁ * c₂ * c₁⁻¹) * n₁⁻¹ * c₂⁻¹ * n₂⁻¹ := by group
          _ = n₁ * n₂ * c₂ * n₁⁻¹ * c₂⁻¹ * n₂⁻¹ := by
            rw [← hc₂' c₁]; group
          _ = n₁ * n₂ * (c₂ * n₁⁻¹) * c₂⁻¹ * n₂⁻¹ := by group
          _ = n₁ * n₂ * (n₁⁻¹ * c₂) * c₂⁻¹ * n₂⁻¹ := by rw [hc₂' n₁⁻¹]
          _ = n₁ * n₂ * n₁⁻¹ * n₂⁻¹ := by group
      rw [key]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)
    have hcommN : _root_.commutator K ≤ N :=
      Subgroup.commutator_le.2 (fun a _ b _ => hcomm a b)
    have htop : (⊤ : Subgroup K) ≤ N :=
      calc (⊤ : Subgroup K) = _root_.commutator K := hK.1.symm
        _ ≤ N := hcommN
    exact top_le_iff.1 htop

theorem quasisimple_not_isPGroup {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hK : CFSG.Open.IsQuasisimple K) : ¬ IsPGroup p K := by
  intro hpg
  haveI := quasisimple_nontrivial hK
  haveI : Group.IsPerfect K := ⟨hK.1⟩
  exact Group.IsPerfect.not_isNilpotent K hpg.isNilpotent

theorem component_normal {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : CFSG.Open.IsComponentOf L ⊤)
    (huniq : ∀ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ → K = L) : L.Normal := by
  constructor
  intro n hn g
  have hconj : L.map (MulAut.conj g).toMonoidHom = L := by
    apply huniq
    refine ⟨le_top, ?_, ?_⟩
    · have h := CFSG.Open.IsSubnormal.map (MulAut.conj g).toMonoidHom hL.2.1
      rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h
    · exact (CFSG.Open.IsQuasisimple.congr
        (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective)).1 hL.2.2
  have hmem : g * n * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
  rwa [hconj] at hmem

theorem exists_conj_mem_of_isSylowOf {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {P : Subgroup Y} (hP : CFSG.ABGLocalTools.IsSylowOf p P ⊤) {H : Subgroup Y}
    (hH : IsPGroup p ↥H) : ∃ k : Y, ∀ h ∈ H, k⁻¹ * h * k ∈ P := by
  obtain ⟨Q, hHQ⟩ := hH.exists_le_sylow
  have hQ : CFSG.ABGLocalTools.IsSylowOf p (Q : Subgroup Y) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.2
      ⟨le_top, Q.isPGroup', by rw [Subgroup.relIndex_top_right]; exact Q.not_dvd_index⟩
  obtain ⟨k, -, hk⟩ := hP.exists_mem_conj hQ
  exact ⟨k, fun h hh => (hk h).1 (hHQ hh)⟩

theorem mem_zpowers_of_isCyclic {p : ℕ} {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsCyclic ↥S) {a b : G} (ha : a ∈ S) (hb : b ∈ S)
    (hao : Nat.card (Subgroup.zpowers a) = p) (hbo : Nat.card (Subgroup.zpowers b) = p) :
    a ∈ Subgroup.zpowers b := by
  haveI := hS
  have hza : Subgroup.zpowers a ≤ S := Subgroup.zpowers_le.2 ha
  have hzb : Subgroup.zpowers b ≤ S := Subgroup.zpowers_le.2 hb
  have heq : (Subgroup.zpowers a).subgroupOf S = (Subgroup.zpowers b).subgroupOf S := by
    rw [IsCyclic.subgroup_eq_iff_card_eq]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hza).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzb).toEquiv, hao, hbo]
  have hmem : (⟨a, ha⟩ : ↥S) ∈ (Subgroup.zpowers a).subgroupOf S :=
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers a)
  rw [heq, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem not_isCyclic_of_exponent {p : ℕ} {H : Type} [Group H] [Finite H] (hp : p.Prime)
    (hexp : ∀ h : H, h ^ p = 1) (hcard : Nat.card H = p ^ 2) : ¬ IsCyclic H := by
  intro hc
  have h1 : Monoid.exponent H = Nat.card H := IsCyclic.exponent_eq_card
  have h2 : Monoid.exponent H ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  rw [h1, hcard] at h2
  have h3 : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos h2
  have h4 := hp.two_le
  nlinarith

theorem centralizes_of_perfect {Y : Type} [Group Y] {L R : Subgroup Y} (hLn : L.Normal)
    (hRn : R.Normal) (hLq : _root_.commutator ↥L = ⊤)
    (hRL : ∀ g ∈ R, g ∈ L → ∀ h ∈ L, g * h = h * g) {r : Y} (hr : r ∈ R) {g : Y}
    (hg : g ∈ L) : r * g = g * r := by
  have hψR : ∀ a : Y, a ∈ L → r * a * r⁻¹ * a⁻¹ ∈ R := fun a _ => by
    have h1 : a * r⁻¹ * a⁻¹ ∈ R := hRn.conj_mem r⁻¹ (R.inv_mem hr) a
    have h2 : r * a * r⁻¹ * a⁻¹ = r * (a * r⁻¹ * a⁻¹) := by group
    rw [h2]
    exact R.mul_mem hr h1
  have hψL : ∀ a : Y, a ∈ L → r * a * r⁻¹ * a⁻¹ ∈ L := fun a ha => by
    have h1 : r * a * r⁻¹ ∈ L := hLn.conj_mem a ha r
    exact L.mul_mem h1 (L.inv_mem ha)
  have hψc : ∀ a : Y, a ∈ L → ∀ h ∈ L, (r * a * r⁻¹ * a⁻¹) * h = h * (r * a * r⁻¹ * a⁻¹) :=
    fun a ha h hh => hRL _ (hψR a ha) (hψL a ha) h hh
  let ψ : L →* Y := MonoidHom.mk' (fun a : L => r * (a : Y) * r⁻¹ * (a : Y)⁻¹) (by
    intro a b
    have ea : r * (a : Y) * r⁻¹ = (r * (a : Y) * r⁻¹ * (a : Y)⁻¹) * (a : Y) := by group
    have eb : r * (b : Y) * r⁻¹ = (r * (b : Y) * r⁻¹ * (b : Y)⁻¹) * (b : Y) := by group
    have hcb := hψc (b : Y) b.2 (a : Y) a.2
    show r * ((a : Y) * (b : Y)) * r⁻¹ * ((a : Y) * (b : Y))⁻¹ =
      (r * (a : Y) * r⁻¹ * (a : Y)⁻¹) * (r * (b : Y) * r⁻¹ * (b : Y)⁻¹)
    calc r * ((a : Y) * (b : Y)) * r⁻¹ * ((a : Y) * (b : Y))⁻¹
        = (r * (a : Y) * r⁻¹) * (r * (b : Y) * r⁻¹) * (b : Y)⁻¹ * (a : Y)⁻¹ := by group
      _ = ((r * (a : Y) * r⁻¹ * (a : Y)⁻¹) * (a : Y)) *
            ((r * (b : Y) * r⁻¹ * (b : Y)⁻¹) * (b : Y)) * (b : Y)⁻¹ * (a : Y)⁻¹ := by
          rw [← ea, ← eb]
      _ = (r * (a : Y) * r⁻¹ * (a : Y)⁻¹) *
            ((a : Y) * (r * (b : Y) * r⁻¹ * (b : Y)⁻¹)) * (a : Y)⁻¹ := by group
      _ = (r * (a : Y) * r⁻¹ * (a : Y)⁻¹) *
            ((r * (b : Y) * r⁻¹ * (b : Y)⁻¹) * (a : Y)) * (a : Y)⁻¹ := by rw [← hcb]
      _ = (r * (a : Y) * r⁻¹ * (a : Y)⁻¹) * (r * (b : Y) * r⁻¹ * (b : Y)⁻¹) := by group)
  have hker : _root_.commutator ↥L ≤ ψ.ker := by
    refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hψc (a : Y) a.2 (r * (b : Y) * r⁻¹ * (b : Y)⁻¹) (hψL (b : Y) b.2)
  have hg1 : ψ ⟨g, hg⟩ = 1 := by
    have htop : (⊤ : Subgroup ↥L) ≤ ψ.ker := by
      rw [← hLq]
      exact hker
    exact MonoidHom.mem_ker.1 (htop (Subgroup.mem_top _))
  have h3 : r * g * r⁻¹ * g⁻¹ = 1 := hg1
  calc r * g = (r * g * r⁻¹ * g⁻¹) * g * r := by group
    _ = g * r := by rw [h3]; group

end Generic

section Cfg

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}

theorem pCore_le_of_cfg (cfg : K62B.Cfg p P x z) : CFSG.pCore p Y ≤ P := by
  haveI : Fact p.Prime := ⟨cfg.prime⟩
  have hPn : IsPGroup p ↥(P ⊔ CFSG.pCore p Y) :=
    IsPGroup.to_sup_of_normal_right cfg.isPGroup CFSG.pCore_isPGroup
  have heq : P ⊔ CFSG.pCore p Y = P := cfg.sylow.eq_of_le le_sup_left le_top hPn
  exact (le_sup_right : CFSG.pCore p Y ≤ P ⊔ CFSG.pCore p Y).trans heq.le

theorem zpowers_conj_eq (cfg : K62B.Cfg p P x z) :
    ∀ g ∈ P, ∀ c ∈ Subgroup.zpowers z, g * c * g⁻¹ = c := by
  intro g hg c hc
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hcm : Commute g z := cfg.z_central g hg
  rw [(hcm.zpow_right n).eq, mul_inv_cancel_right]

theorem z_mem_normal (cfg : K62B.Cfg p P x z) {N : Subgroup Y} (hNn : N.Normal) (hN : N ≠ ⊥) :
    z ∈ N := by
  haveI : Fact p.Prime := ⟨cfg.prime⟩
  have hdvd : p ∣ Nat.card ↥N := by
    by_contra hnd
    have hcop : p.Coprime (Nat.card ↥N) := (Nat.Prime.coprime_iff_not_dvd cfg.prime).2 hnd
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_le_primeComplementCore
      p N hNn hcop
    rw [cfg.core, le_bot_iff] at hle
    exact hN hle
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hdvd
  have hgY : (g : Y) ∈ N := g.2
  have hgord : orderOf (g : Y) = p := by
    rw [Subgroup.orderOf_coe]
    exact hg
  have hgp : (g : Y) ^ p = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one _
  obtain ⟨k, hk⟩ := exists_conj_mem_of_isSylowOf cfg.sylow
    (CFSG.LocalAnalysis.RankFourTheoremC.isPGroup_zpowers_of_pow_prime_eq_one hgp)
  have hgP : k⁻¹ * (g : Y) * k ∈ P := hk _ (Subgroup.mem_zpowers _)
  have hgN : k⁻¹ * (g : Y) * k ∈ N := by
    have := hNn.conj_mem (g : Y) hgY k⁻¹
    simpa using this
  have hne : k⁻¹ * (g : Y) * k ≠ 1 := by
    intro h1
    have hg1 : (g : Y) = 1 := by
      have h2 : (g : Y) = k * (k⁻¹ * (g : Y) * k) * k⁻¹ := by group
      rw [h2, h1]
      group
    have hgone : orderOf (g : Y) = 1 := by rw [hg1, orderOf_one]
    rw [hgord] at hgone
    exact cfg.prime.one_lt.ne' hgone
  have hsub : N ⊓ P ≠ ⊥ := by
    intro h
    have hmem : k⁻¹ * (g : Y) * k ∈ N ⊓ P := Subgroup.mem_inf.2 ⟨hgN, hgP⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hne hmem
  have hz : z ∈ N ⊓ P := cfg.z_mem_of_normal inf_le_right (fun a ha b hb =>
    Subgroup.mem_inf.2 ⟨hNn.conj_mem (b : Y) (Subgroup.mem_inf.1 hb).1 a,
      P.mul_mem (P.mul_mem ha (Subgroup.mem_inf.1 hb).2) (P.inv_mem ha)⟩) hsub
  exact (Subgroup.mem_inf.1 hz).1


section Subgroups

theorem exists_subgroup_commutator_mem {Y : Type} [Group Y] {P C : Subgroup Y} (x : Y)
    (hC : ∀ g ∈ P, ∀ c ∈ C, g * c * g⁻¹ = c) :
    ∃ D : Subgroup Y, ∀ g, g ∈ D ↔ g ∈ P ∧ x * g * x⁻¹ * g⁻¹ ∈ C := by
  refine ⟨{ carrier := {g | g ∈ P ∧ x * g * x⁻¹ * g⁻¹ ∈ C}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro a b ⟨ha, hac⟩ ⟨hb, hbc⟩
    refine ⟨P.mul_mem ha hb, ?_⟩
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by group
    rw [e, hC a ha _ hbc]
    exact C.mul_mem hac hbc
  · exact ⟨P.one_mem, by simpa using C.one_mem⟩
  · rintro a ⟨ha, hac⟩
    refine ⟨P.inv_mem ha, ?_⟩
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = a⁻¹ * (x * a * x⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e, hC a⁻¹ (P.inv_mem ha) _ (C.inv_mem hac)]
    exact C.inv_mem hac

end Subgroups

end Cfg


end I291Zero

section Classification


namespace I291Zero

theorem plane_not_central {p : ℕ} {Y : Type} [Group Y] [Finite Y] (hp : p.Prime) (hp5 : 5 ≤ p)
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections Y) {V : Subgroup Y}
    (hV : CFSG.LocalAnalysis.GLTheoremB.IsPPlane p V) (hVL : V ≤ L)
    (hcent : ∀ v ∈ V, ∀ h ∈ L, h * v = v * h) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcatL : CFSG.Open.IsCatalogGroup (↥L ⧸ Subgroup.center ↥L) :=
    hcat.isCatalogGroup_center_quotient hL
  have hVc : V.subgroupOf L ≤ Subgroup.center ↥L := by
    intro w hw
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    exact hcent (w : Y) (Subgroup.mem_subgroupOf.1 hw) h h.2
  have hexp : ∀ w : ↥(V.subgroupOf L), w ^ p = 1 := by
    intro w
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.1.2 _ (Subgroup.mem_subgroupOf.1 w.2)
  have hVp : IsPGroup p ↥(V.subgroupOf L) := by
    intro w
    exact ⟨1, by rw [pow_one]; exact hexp w⟩
  have hcyc : IsCyclic ↥(V.subgroupOf L) :=
    CFSG.LocalAnalysis.RankFourTheoremC.kFactCenterCyclicGeFive_holds ↥L hL.2.2 hcatL p hp hp5
      (V.subgroupOf L) hVc hVp
  have hcard : Nat.card ↥(V.subgroupOf L) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv, hV.2]
  exact not_isCyclic_of_exponent hp hexp hcard hcyc

end I291Zero

theorem kd291LinUniZero_holds : KD291LinUniZero := by
  intro p Y _ _ P x z L hL
  obtain ⟨data, hLcomp, huniq, -⟩ := hL
  have cfg : K62B.Cfg p P x z := data.cfg
  haveI : Fact p.Prime := ⟨cfg.prime⟩
  have hp5 : 5 ≤ p := cfg.five_le
  have hp2 : p ≠ 2 := by omega
  have hLq : CFSG.Open.IsQuasisimple ↥L := hLcomp.2.2
  have hLn : L.Normal := I291Zero.component_normal hLcomp huniq
  have hLne : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).1 (I291Zero.quasisimple_nontrivial hLq)
  have hdvdL : p ∣ Nat.card ↥L := by
    by_contra hnd
    have hcop : p.Coprime (Nat.card ↥L) := (Nat.Prime.coprime_iff_not_dvd cfg.prime).2 hnd
    have hle := CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_le_primeComplementCore
      p L hLn hcop
    rw [cfg.core, le_bot_iff] at hle
    exact hLne hle
  by_cases hR : CFSG.pCore p Y = ⊥
  · refine ⟨?_, fun g hg _ => ?_⟩
    · rw [hR]
      exact isCyclic_of_subsingleton
    · rw [hR, Subgroup.mem_bot] at hg
      rw [hg]
      exact L.one_mem
  · have hRP : CFSG.pCore p Y ≤ P := I291Zero.pCore_le_of_cfg cfg
    have hRn : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
    have hzR : z ∈ CFSG.pCore p Y := I291Zero.z_mem_normal cfg CFSG.pCore_normal hR
    have hzL : z ∈ L := I291Zero.z_mem_normal cfg hLn hLne
    have hLnR : ¬ L ≤ CFSG.pCore p Y := by
      intro h
      apply I291Zero.quasisimple_not_isPGroup (p := p) hLq
      intro g
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := Y)) ⟨(g : Y), h g.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hRLc : ∀ g ∈ CFSG.pCore p Y, g ∈ L → ∀ h ∈ L, g * h = h * g := by
      intro g hg hgL h hh
      haveI : ((CFSG.pCore p Y).subgroupOf L).Normal := hRn.subgroupOf L
      have hNtop : (CFSG.pCore p Y).subgroupOf L ≠ ⊤ := by
        intro htop
        apply hLnR
        intro w hw
        have hwmem : (⟨w, hw⟩ : ↥L) ∈ (CFSG.pCore p Y).subgroupOf L := by
          rw [htop]
          exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.1 hwmem
      have hcen := I291Zero.normal_le_center_of_quasisimple hLq _ hNtop
      have hmem : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L :=
        hcen (Subgroup.mem_subgroupOf.2 hg)
      have hc := Subgroup.mem_center_iff.1 hmem ⟨h, hh⟩
      exact (congrArg Subtype.val hc).symm
    have hRcent : ∀ r ∈ CFSG.pCore p Y, ∀ g ∈ L, r * g = g * r := fun r hr g hg =>
      I291Zero.centralizes_of_perfect hLn hRn hLq.1 hRLc hr hg
    have hzcent : ∀ h ∈ L, h * z = z * h := fun h hh => (hRLc z hzR hzL h hh).symm
    have hRcyc : IsCyclic ↥(CFSG.pCore p Y) := by
      by_contra hRnc
      obtain ⟨U₂, hU₂R, hU₂pl, hU₂P⟩ :=
        CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1111b.input31_5_holds Y p cfg.prime hp2 P
          (CFSG.pCore p Y) cfg.isPGroup hRP (hRn.subgroupOf P) hRnc
      have hSn : ((L ⊓ P).subgroupOf P).Normal := by
        constructor
        intro n hn g
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact Subgroup.mem_inf.2 ⟨hLn.conj_mem _ (Subgroup.mem_inf.1 hn).1 g,
          P.mul_mem (P.mul_mem g.2 (Subgroup.mem_inf.1 hn).2) (P.inv_mem g.2)⟩
      have hSnc : ¬ IsCyclic ↥(L ⊓ P) := by
        intro hc
        obtain ⟨g₀, hg₀o, hg₀c⟩ :=
          CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
            hLq cfg.prime hp2 hdvdL
        have hg₀Y : orderOf (g₀ : Y) = p := by
          rw [Subgroup.orderOf_coe]
          exact hg₀o
        have hgp₀ : (g₀ : Y) ^ p = 1 := by
          rw [← hg₀Y]
          exact pow_orderOf_eq_one _
        obtain ⟨k, hk⟩ := I291Zero.exists_conj_mem_of_isSylowOf cfg.sylow
          (CFSG.LocalAnalysis.RankFourTheoremC.isPGroup_zpowers_of_pow_prime_eq_one hgp₀)
        set y : Y := k⁻¹ * (g₀ : Y) * k with hy
        have hyP : y ∈ P := hk _ (Subgroup.mem_zpowers _)
        have hyL : y ∈ L := by
          have := hLn.conj_mem (g₀ : Y) g₀.2 k⁻¹
          simpa [hy] using this
        have hyo : orderOf y = p := by
          have e : y = k⁻¹ * (g₀ : Y) * k⁻¹⁻¹ := by rw [hy, inv_inv]
          have hpow : y ^ p = 1 := by
            rw [e, conj_pow, hgp₀]
            group
          have hy1 : y ≠ 1 := by
            intro h1
            have h2 : (g₀ : Y) = 1 := by
              have h3 : (g₀ : Y) = k * (k⁻¹ * (g₀ : Y) * k) * k⁻¹ := by group
              rw [← hy, h1] at h3
              rw [h3]
              group
            have h4 : orderOf (g₀ : Y) = 1 := by rw [h2, orderOf_one]
            rw [hg₀Y] at h4
            exact cfg.prime.one_lt.ne' h4
          exact orderOf_eq_prime hpow hy1
        have hync : ¬ ∀ h ∈ L, h * y = y * h := by
          intro hcy
          apply hg₀c
          rw [Subgroup.mem_center_iff]
          intro h
          apply Subtype.ext
          have hh' : k⁻¹ * (h : Y) * k ∈ L := by
            simpa using hLn.conj_mem (h : Y) h.2 k⁻¹
          have hc' := hcy _ hh'
          have hg₀eq : (g₀ : Y) = k * y * k⁻¹ := by
            rw [hy]
            group
          show (h : Y) * (g₀ : Y) = (g₀ : Y) * (h : Y)
          rw [hg₀eq]
          calc (h : Y) * (k * y * k⁻¹) = k * ((k⁻¹ * (h : Y) * k) * y) * k⁻¹ := by group
            _ = k * (y * (k⁻¹ * (h : Y) * k)) * k⁻¹ := by rw [hc']
            _ = (k * y * k⁻¹) * (h : Y) := by group
        have hyS : y ∈ L ⊓ P := Subgroup.mem_inf.2 ⟨hyL, hyP⟩
        have hzS : z ∈ L ⊓ P := Subgroup.mem_inf.2 ⟨hzL, cfg.z_mem⟩
        have hyz : y ∈ Subgroup.zpowers z :=
          I291Zero.mem_zpowers_of_isCyclic hc hyS hzS
            (by rw [Nat.card_zpowers, hyo]) (by rw [Nat.card_zpowers, cfg.orderOf_z])
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hyz
        apply hync
        intro h hh
        rw [← hn]
        exact ((show Commute h z from hzcent h hh).zpow_right n).eq
      obtain ⟨U₁, hU₁S, hU₁pl, hU₁P⟩ :=
        CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1111b.input31_5_holds Y p cfg.prime hp2 P
          (L ⊓ P) cfg.isPGroup inf_le_right hSn hSnc
      have hU₁L : U₁ ≤ L := fun u hu => (Subgroup.mem_inf.1 (hU₁S hu)).1
      have hU₁P' : U₁ ≤ P := fun u hu => (Subgroup.mem_inf.1 (hU₁S hu)).2
      have hU₂P' : U₂ ≤ P := hU₂R.trans hRP
      have hnorm : ∀ V : Subgroup Y, P ≤ Subgroup.normalizer (V : Set Y) →
          ∀ g ∈ P, ∀ u ∈ V, g * u * g⁻¹ ∈ V := fun V hV g hg u hu =>
        (Subgroup.mem_normalizer_iff.1 (hV hg) u).1 hu
      have hcU₁ := cfg.comm_mem_zpowers hU₁P' (hnorm U₁ hU₁P) hU₁pl.2
      have hcU₂ := cfg.comm_mem_zpowers hU₂P' (hnorm U₂ hU₂P) hU₂pl.2
      obtain ⟨D, hD⟩ := I291Zero.exists_subgroup_commutator_mem x (I291Zero.zpowers_conj_eq cfg)
      have hU₁D : U₁ ≤ D := fun u hu => (hD u).2 ⟨hU₁P' hu, hcU₁ x cfg.x_mem u hu⟩
      have hU₂D : U₂ ≤ D := fun u hu => (hD u).2 ⟨hU₂P' hu, hcU₂ x cfg.x_mem u hu⟩
      have hcomm : ∀ a ∈ U₁, ∀ b ∈ U₂, a * b = b * a := fun a ha b hb =>
        (hRcent b (hU₂R hb) a (hU₁L ha)).symm
      have hFea := K62B.isElemAbelian_sup hU₁pl.1 hU₂pl.1 hcomm
      have hFcard : Nat.card ↥(U₁ ⊔ U₂) ≤ p ^ 2 :=
        cfg.card_le_sq_of_comm (sup_le hU₁P' hU₂P') hFea
          (fun e he => ((hD e).1 (sup_le hU₁D hU₂D he)).2)
      have hEq : U₁ = U₁ ⊔ U₂ :=
        Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hU₁pl.2]; exact hFcard)
      have hU₂U₁ : U₂ ≤ U₁ := by
        have h := (le_sup_right : U₂ ≤ U₁ ⊔ U₂)
        rw [← hEq] at h
        exact h
      exact I291Zero.plane_not_central cfg.prime hp5 hLcomp cfg.catalog hU₂pl (hU₂U₁.trans hU₁L)
        (fun v hv h hh => (hRLc v (hU₂R hv) (hU₁L (hU₂U₁ hv)) h hh).symm)
    refine ⟨hRcyc, fun g hg hgp => ?_⟩
    by_cases hg1 : g = 1
    · rw [hg1]
      exact L.one_mem
    have hgo : orderOf g = p := orderOf_eq_prime hgp hg1
    have hgz : g ∈ Subgroup.zpowers z :=
      I291Zero.mem_zpowers_of_isCyclic hRcyc hg hzR (by rw [Nat.card_zpowers, hgo])
        (by rw [Nat.card_zpowers, cfg.orderOf_z])
    exact (Subgroup.zpowers_le.2 hzL) hgz

end Classification

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

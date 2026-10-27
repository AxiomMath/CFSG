module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6PropSDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6QStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3FusionLines
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowLift
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VICore
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3A6VITools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem a6vi_exists_normalizer_conj {Q : Subgroup G} {x g : G}
    (hQsyl : IsSylowOf 3 Q (centralizer ({x} : Set G)))
    (hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hy : g * x * g⁻¹ ∈ Q) :
    ∃ n ∈ normalizer (Q : Set G), n * x * n⁻¹ = g * x * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q' : Subgroup G := Q.map (MulAut.conj g⁻¹).toMonoidHom with hQ'
  have hQ'mem : ∀ w : G, w ∈ Q' ↔ g * w * g⁻¹ ∈ Q := by
    intro w
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      have e : g * (g⁻¹ * q * g) * g⁻¹ = q := by group
      rw [e]
      exact hq
    · intro hw
      refine ⟨g * w * g⁻¹, hw, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
  have hQ'le : Q' ≤ centralizer ({x} : Set G) := by
    intro w hw
    rw [hQ'mem] at hw
    rw [mem_centralizer_singleton_iff]
    have h := hQab _ hw _ hy
    calc w * x = g⁻¹ * ((g * w * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * w * g⁻¹)) * g := by rw [h]
      _ = x * w := by group
  have hQ'syl : IsSylowOf 3 Q' (centralizer ({x} : Set G)) := by
    refine isSylowOf_of_card hQ'le ?_
    rw [hQ', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hQsyl.card_eq
  obtain ⟨k, hkC, hk⟩ := hQsyl.exists_mem_conj hQ'syl
  refine ⟨g * k, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro z
    have h1 := hk (k * z * k⁻¹)
    have e1 : k⁻¹ * (k * z * k⁻¹) * k = z := by group
    have e2 : g * (k * z * k⁻¹) * g⁻¹ = g * k * z * (g * k)⁻¹ := by group
    rw [e1, hQ'mem, e2] at h1
    exact h1.symm
  · have hkx : k * x * k⁻¹ = x := by rw [mem_centralizer_singleton_iff.mp hkC]; group
    calc g * k * x * (g * k)⁻¹ = g * (k * x * k⁻¹) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [hkx]

theorem a6vi_shape_of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hAct : KFactA6SylowAction) (hAut : A6AutData)
    (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G} (hM : IsCoreMaxLocal 3 P M)
    {x : G} (hgen : IsGenericPoint 3 P M x) {J : Subgroup G} (hJ : IsA6Normal M x J)
    (h34 : A6Prop34 3 P J x) : A6ShapeVI 3 P x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hnwc
  obtain ⟨hxP, hxLO, hQsyl, -⟩ := id hgen
  obtain ⟨-, hx1, hx3, -, -⟩ := id hxLO
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hQab, -, hfus⟩ := h34
  have hJC := hJ.le_centralizer
  have hxJ : x ∉ J := a6_x_not_mem_J hS hU0 hp hM hgen hJ
  obtain ⟨hTc, hTel, Z, hZc, hxZ, hTZ, hTZ0, hQTZ⟩ := a6_qstruct hS hU0 hA1 hAut hp hM hgen hJ
  set Q : Subgroup G := (P : Subgroup G) ⊓ centralizer ({x} : Set G) with hQ
  set T : Subgroup G := (P : Subgroup G) ⊓ J with hT
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hTQ : T ≤ Q := fun t ht => ⟨ht.1, hJC ht.2⟩
  have hxT : x ∉ T := fun h => hxJ h.2
  have hne1 : ∀ g : G, g * x * g⁻¹ ≠ 1 := fun g h => hx1 (by
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, h]; group)
  obtain ⟨g, hgQ, hgne⟩ : ∃ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q ∧
      (zpowers x).map (MulAut.conj g).toMonoidHom ≠ zpowers x := by
    by_contra hcon
    push Not at hcon
    exact hnwc hcon
  have hgJ := (hfus g hgQ).resolve_left hgne
  rw [a6vi_map_conj_zpowers] at hgQ hgJ
  have hyQ : g * x * g⁻¹ ∈ Q := zpowers_le.mp hgQ
  have hyT : g * x * g⁻¹ ∈ T := ⟨hyQ.1, zpowers_le.mp hgJ⟩
  obtain ⟨n, hnN, hnx⟩ := a6vi_exists_normalizer_conj hQsyl hQcomm hyQ
  have hZQ : Z ≤ Q := le_sup_right.trans hQTZ.symm.le
  have hZx : Z = zpowers x := by
    by_contra hne
    obtain ⟨w, hwZ, hw3⟩ :=
      a6vi_exists_cube_root hZc (hQsyl.isPGroup.to_le hZQ) hxZ hx1 hx3 hne
    have hwQ : n * w * n⁻¹ ∈ T ⊔ Z := by
      rw [← hQTZ]; exact (mem_normalizer_iff.mp hnN w).mp (hZQ hwZ)
    obtain ⟨t₀, ht₀, c₀, hc₀, hdec⟩ := u3l42_decomp hTZ hwQ
    have hy3 : g * x * g⁻¹ = c₀ ^ 3 := by
      rw [← hnx, ← hw3, ← conj_pow, hdec, Commute.mul_pow (hTZ t₀ ht₀ c₀ hc₀) 3,
        hTel.2 t₀ ht₀, one_mul]
    have hyTZ : g * x * g⁻¹ ∈ T ⊓ Z :=
      Subgroup.mem_inf.mpr ⟨hyT, by rw [hy3]; exact pow_mem hc₀ 3⟩
    rw [hTZ0] at hyTZ
    exact hne1 g (mem_bot.mp hyTZ)
  have hQeq : Q = T ⊔ zpowers x := by rw [← hZx]; exact hQTZ
  have hconjT : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ Q →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom ≤ T := fun g hg =>
    (hfus g hg).imp id fun hJ' => le_inf (hg.trans inf_le_left) hJ'
  have hTM : T ≤ M := inf_le_left.trans hPM
  have hLO : ∀ g : G, g * x * g⁻¹ ∈ T → IsLargeObstruction 3 M (g * x * g⁻¹) := fun g hg =>
    isLargeObstruction_conj_of_map_le hS hU0 hp hM hxP hxLO
      (by rw [a6vi_map_conj_zpowers]; exact zpowers_le.mpr hg.1)
  have hL33 : ∀ g₁ g₂ g₃ : G, g₁ * x * g₁⁻¹ ∈ T → g₂ * x * g₂⁻¹ ∈ T → g₃ * x * g₃⁻¹ ∈ T →
      zpowers (g₁ * x * g₁⁻¹) ≠ zpowers (g₂ * x * g₂⁻¹) →
      zpowers (g₁ * x * g₁⁻¹) ≠ zpowers (g₃ * x * g₃⁻¹) →
      zpowers (g₂ * x * g₂⁻¹) ≠ zpowers (g₃ * x * g₃⁻¹) → False :=
    fun g₁ g₂ g₃ h₁ h₂ h₃ h12 h13 h23 =>
      false_of_three_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hTM hTel
        hTc h₁ h₂ h₃ (hne1 g₁) (hne1 g₂) (hne1 g₃) h12 h13 h23 (hLO g₁ h₁) (hLO g₂ h₂)
        (hLO g₃ h₃)
  obtain ⟨n', hn'C, hn'N, hn'mv⟩ := a6_exists_moving hAct hgen hJ hyT (hne1 g)
  refine ⟨a6vi_core hxP hx1 hx3 hQsyl hQab hTel hTc hTQ hxT hQeq hconjT hL33 hnN
    (by rw [hnx]; exact hyT) hn'C hn'N (by rw [hnx]; exact hn'mv), ⟨hQab, ?_⟩, ?_⟩
  · intro q hq
    rw [hQeq] at hq
    have hxQ : x ∈ Q := ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩
    have hTx : ∀ t ∈ T, ∀ c ∈ zpowers x, t * c = c * t := fun t ht c hc =>
      hQcomm t (hTQ ht) c (zpowers_le.mpr hxQ hc)
    obtain ⟨t₀, ht₀, c₀, hc₀, rfl⟩ := u3l42_decomp hTx hq
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc₀
    rw [Commute.mul_pow (hTx t₀ ht₀ _ hc₀) 3, hTel.2 t₀ ht₀, one_mul, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3, one_zpow]
  · rw [hQeq, CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three T hx3 hxT
      (fun a ha => hQcomm a (hTQ ha) x ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩), hTc]
    norm_num

theorem GL83GenericPrimeThreeA6ShapeVI.of_kfacts (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD1 : TheoremD1 G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (K2 : StronglyEmbeddedCyclicOuterKFact) (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree)
    (hno : NoExcludedSection3 G) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore)
    (hE1 : KFactL28Three) (hE3 : KFactL28BorelCore) (hAct : KFactA6SylowAction)
    (hAut : A6AutData) : GL83GenericPrimeThreeA6ShapeVI G := by
  intro p hp P M hM hfail hIH x hgen hp3 J hJC hCJ hperf hlt hmin hnot Q _ ψ hψ hker hQ h34
  subst hp3
  exact a6vi_shape_of_kfacts hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hAct hAut hp hM
    hgen ⟨hJC, hCJ, hperf, hnot, hlt, hmin, Q, inferInstance, ψ, hψ, hker, hQ⟩ h34

end CFSG.LocalAnalysis.RankThreeTheoremC

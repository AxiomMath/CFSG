module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneSetup
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedTenFourteenThree
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.Quasithin CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def TwelveCase (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (b : G) (L : Subgroup G) : Prop :=
  AGL81CfgData 3 P M H Q K ∧ IsAltTwoP 3 K ∧ ¬ HasPrimeConstraint (G := H) 3 ∧
    3 ≤ Open.pRank 3 H ∧ TwelveB M H Q K b ∧ IsWeakSBlock M (pCoreOf 2 H) L ∧
    ∃ I₀ ∈ cZero (H ⊓ L), CFSG.ComponentClassification.AS76b.oUpperTwo I₀ ≤ hyp111Pre 3 H K

variable (G) in
@[expose] def AGL81TenThreeOTwoZ : Prop :=
  Setting G → ∀ (p : ℕ) (P : Sylow p G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)),
    AGL81CfgData p P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    ∀ I₀ ∈ cZero (H ⊓ L), IsSymThreeOrSUThreeTwo (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) →
    ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀,
      (∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) →
      x ∈ pCoreOf 2 (CFSG.ComponentClassification.AS76b.oUpperTwo I₀)

variable (G) in
@[expose] def AGL81TenFourteenThreeAt : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (b : G) (L : Subgroup G),
    TwelveCase P M H Q K b L → ¬ ⁅Subgroup.zpowers b, L⁆ ≤ pCoreOf 2 L

variable (G) in
@[expose] def AGL81TwelveNormalizes : Prop :=
  Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (b : G) (L : Subgroup G),
    TwelveCase P M H Q K b L → Subgroup.zpowers b ≤ Subgroup.normalizer (L : Set G)

theorem agl81TenFourteenThreeAt_of (h1014 : AGL81TenFourteenThreeCfg G)
    (h1031 : AGL81TenThreeOneAt G) : AGL81TenFourteenThreeAt G := by
  intro hS P M H Q K b L hc
  obtain ⟨hd, -, -, -, ⟨hbHM, -, hb3, hCb, hQb⟩, hL, I₀, hI₀, -⟩ := hc
  have hI₀' : IsCZeroMember (H ⊓ L) I₀ := hI₀
  have h3L : 3 ∣ Nat.card L := (h1031 hS 3 P M H Q K hd L hL I₀ hI₀).trans
    (Subgroup.card_dvd_of_le ((oUpperTwo_le_self I₀).trans (hI₀'.le.trans inf_le_right)))
  exact h1014 hS P M H Q K hd L hL h3L b hbHM.2 hb3 hCb ⟨Q, hQb, hd.base⟩

theorem commutator_mem_pCoreOf_of_not_mem_normalizer {M H L : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hL : IsTwoPrimeComponent M L) {b : G}
    (hbM : b ∈ M) (hbX : b ∈ d1PlusCore 3 H K) (hbL : b ∉ Subgroup.normalizer (L : Set G))
    {x : G} (hxL : x ∈ L) (hxK : x ∈ hyp111Pre 3 H K) {k : ℕ} (hxk : x ^ 3 ^ k = 1) :
    ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  set L' := L.map (MulAut.conj b).toMonoidHom with hL'def
  have hne : L ≠ L' := fun h => hbL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hL' : IsTwoPrimeComponent M L' := hL.map_conj hbM
  have hc1 := hL.commutator_le hL' hne
  have hc2 := hL'.commutator_le hL hne.symm
  have hjL' : b * x * b⁻¹ ∈ L' := ⟨x, hxL, by simp [MulAut.conj_apply]⟩
  have hcop : ∃ n : ℕ, Nat.Coprime (3 ^ k) n ∧ (x⁻¹ * (b * x * b⁻¹)) ^ n = 1 := by
    obtain ⟨x₀, hx₀, rfl⟩ := hxK
    obtain ⟨b₀, hb₀, rfl⟩ := hbX
    set N := primeComplementCore (G := H) 3 with hN
    set c₀ : H := x₀⁻¹ * (b₀ * x₀ * b₀⁻¹) with hc₀def
    have hc₀ : c₀ ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      have hcomm : QuotientGroup.mk' N x₀ * QuotientGroup.mk' N b₀ =
          QuotientGroup.mk' N b₀ * QuotientGroup.mk' N x₀ :=
        (Subgroup.mem_centralizer_iff.mp hb₀) _ hx₀
      rw [hc₀def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    refine ⟨orderOf c₀, ?_, ?_⟩
    · have hd : orderOf c₀ ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hc₀
      exact Nat.Coprime.pow_left k ((primeComplementCore_coprime (G := H) 3).coprime_dvd_right hd)
    · have h1 : (((x₀ : H) : G)⁻¹ * ((b₀ : G) * (x₀ : G) * (b₀ : G)⁻¹)) = (c₀ : G) := by
        simp [hc₀def]
      show (((x₀ : H) : G)⁻¹ * ((b₀ : G) * (x₀ : G) * (b₀ : G)⁻¹)) ^ orderOf c₀ = 1
      rw [h1, ← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
  obtain ⟨n, hn, hcn⟩ := hcop
  set q := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hq
  have hq1 : ∀ y : M, (y : G) ∈ pCoreOf 2 M → q y = 1 := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    exact (QuotientGroup.eq_one_iff y).mpr (this ▸ hz)
  have hq1' : ∀ y : M, q y = 1 → (y : G) ∈ pCoreOf 2 M := fun y hy =>
    ⟨y, (QuotientGroup.eq_one_iff y).mp hy, rfl⟩
  have hxM : x ∈ M := hL.le hxL
  have hjM : b * x * b⁻¹ ∈ M := hL'.le hjL'
  set x' : M := ⟨x, hxM⟩
  set j' : M := ⟨b * x * b⁻¹, hjM⟩
  have hxj : q x' * q j' = q j' * q x' := by
    have h := hq1 ⁅x', j'⁆ (hc1 (Subgroup.commutator_mem_commutator hxL hjL'))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  have hx3 : q x' ^ 3 ^ k = 1 := by
    rw [← map_pow, show x' ^ 3 ^ k = 1 from Subtype.ext hxk, map_one]
  have hj3 : q j' ^ 3 ^ k = 1 := by
    rw [← map_pow, show j' ^ 3 ^ k = 1 from Subtype.ext (by simp [j', conj_pow, hxk]), map_one]
  have hc3 : ((q x')⁻¹ * q j') ^ 3 ^ k = 1 := by
    rw [(Commute.inv_left (Commute.symm hxj).symm).mul_pow, inv_pow, hx3, hj3, inv_one, one_mul]
  have hcn' : ((q x')⁻¹ * q j') ^ n = 1 := by
    rw [← map_inv, ← map_mul, ← map_pow,
      show (x'⁻¹ * j') ^ n = 1 from Subtype.ext (by simpa using hcn), map_one]
  have hc1' : (q x')⁻¹ * q j' = 1 := by
    have h := (pow_gcd_eq_one (a := (q x')⁻¹ * q j')).mpr ⟨hc3, hcn'⟩
    rwa [Nat.Coprime.gcd_eq_one hn, pow_one] at h
  have hxj' : q x' = q j' := inv_mul_eq_one.mp hc1'
  intro l hl
  have hlM : l ∈ M := hL.le hl
  set l' : M := ⟨l, hlM⟩
  have hjl := hq1 ⁅j', l'⁆ (hc2 (Subgroup.commutator_mem_commutator hjL' hl))
  rw [map_commutatorElement, ← hxj', ← map_commutatorElement] at hjl
  have hxl : x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 M := hq1' _ hjl
  rw [← hL.inf_twoCore]
  exact ⟨L.mul_mem (L.mul_mem (L.mul_mem hxL hl) (L.inv_mem hxL)) (L.inv_mem hl), hxl⟩

theorem not_three_dvd_card_of_perfect {L I : Subgroup G} (hIL : I ≤ L) (hperf : ⁅I, I⁆ = I)
    (h : ∀ x ∈ I, (∃ k : ℕ, x ^ 3 ^ k = 1) → ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) :
    ¬ 3 ∣ Nat.card I := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 ↥I with hO
  set φ := QuotientGroup.mk' O with hφ
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 3 ↥I))
  set T' : Sylow 3 (↥I ⧸ O) := T.mapSurjective (QuotientGroup.mk'_surjective O) with hT'
  have hcomm : ∀ t ∈ (T : Subgroup ↥I), ∀ g : ↥I, φ t * φ g = φ g * φ t := by
    intro t ht g
    obtain ⟨k, hk⟩ := T.isPGroup' ⟨t, ht⟩
    have hk' : (t : G) ^ 3 ^ k = 1 := by
      have := congrArg (fun y : (T : Subgroup ↥I) => ((y : ↥I) : G)) hk
      simpa using this
    have hc := h t t.2 ⟨k, hk'⟩ g (hIL g.2)
    have hcI : ((⁅t, g⁆ : ↥I) : G) ∈ I ⊓ pCoreOf 2 L := ⟨(⁅t, g⁆ : ↥I).2, hc⟩
    obtain ⟨z, hz, hzx⟩ := inf_pCoreOf_le hIL hcI
    have hzt : z = ⁅t, g⁆ := Subtype.ext hzx
    have h1 : φ ⁅t, g⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (hzt ▸ hz)
    rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  have hcent : ∀ w : ↥I ⧸ O, ∀ s ∈ (T' : Subgroup (↥I ⧸ O)), s * w = w * s := by
    intro w s hs
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O w
    obtain ⟨t, ht, rfl⟩ := hs
    exact hcomm t ht g
  have hP : Subgroup.normalizer (T' : Subgroup (↥I ⧸ O)) ≤
      Subgroup.centralizer ((T' : Subgroup (↥I ⧸ O)) : Set (↥I ⧸ O)) :=
    fun w _ => Subgroup.mem_centralizer_iff.mpr fun s hs => hcent w s hs
  set τ := MonoidHom.transferSylow T' hP with hτ
  have hItop : ⁅(⊤ : Subgroup ↥I), (⊤ : Subgroup ↥I)⁆ = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
  have hWtop : ⁅(⊤ : Subgroup (↥I ⧸ O)), (⊤ : Subgroup (↥I ⧸ O))⁆ = ⊤ := by
    rw [← Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective O),
      ← Subgroup.map_commutator, hItop]
  have hker : τ.ker = ⊤ := by
    rw [eq_top_iff, ← hWtop, Subgroup.commutator_le]
    intro a _ c _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hcent (τ c) (τ a) (τ a).2)
  have hW := MonoidHom.not_dvd_card_ker_transferSylow T' hP
  rw [← hτ, hker, Subgroup.card_top] at hW
  intro h3
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact hW h
  · obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
    rw [hm] at h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega

theorem agl81TwelveNormalizes_of (h1031 : AGL81TenThreeOneAt G) (h2255 : AGL81TenThreeOTwoZ G) :
    AGL81TwelveNormalizes G := by
  intro hS P M H Q K b L hc
  obtain ⟨hd, -, -, -, ⟨hbHM, hbX, -, -, -⟩, hL, I₀, hI₀, hI₀K⟩ := hc
  have hI₀' : IsCZeroMember (H ⊓ L) I₀ := hI₀
  rw [Subgroup.zpowers_le]
  by_contra hbL
  have hI₀L : I₀ ≤ L := hI₀'.le.trans inf_le_right
  have h3 := h1031 hS 3 P M H Q K hd L hL I₀ hI₀
  have key : ∀ x ∈ CFSG.ComponentClassification.AS76b.oUpperTwo I₀, (∃ k : ℕ, x ^ 3 ^ k = 1) →
      ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := fun x hx ⟨k, hk⟩ =>
    commutator_mem_pCoreOf_of_not_mem_normalizer hL.toIsTwoPrimeComponent hbHM.2 hbX hbL
      (hI₀L (oUpperTwo_le_self I₀ hx)) (hI₀K hx) hk
  rcases hI₀'.shape with hperf | ⟨-, hsym⟩
  · refine not_three_dvd_card_of_perfect hI₀L hperf.perfect (fun x hx ⟨k, hk⟩ => key x ?_ ⟨k, hk⟩)
      (h3.trans (Subgroup.card_dvd_of_le (oUpperTwo_le_self I₀)))
    refine Subgroup.subset_closure ⟨hx, ?_⟩
    exact Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hk)
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hx' : orderOf (x : G) = 3 := by rwa [Subgroup.orderOf_coe]
    have hx3 : (x : G) ^ 3 ^ 1 = 1 := by rw [pow_one, ← hx', pow_orderOf_eq_one]
    have hO := h2255 hS 3 P M H Q K hd L hL I₀ hI₀ hsym x x.2 (key x x.2 ⟨1, hx3⟩)
    obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 _ ⟨(x : G), hO⟩
    have hdvd : orderOf (x : G) ∣ 2 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hm
    rw [hx'] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC

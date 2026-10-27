module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeDecomp

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

namespace Lemma33Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_core (p : ℕ) (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (GLAPPrimeCoreOf p L : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq] at hg ⊢
  rw [← glaPPrimeCoreOf_gLBConj, hg]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} {x : G} (hxp : x ^ p = 1) :
    IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨k, hk⟩ := (Subgroup.mem_zpowers_iff.1 g.2)
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]

theorem exists_mem_inf_centralizer {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxp : x ^ p = 1)
    (hx : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf p L) {l : G} (hl : l ∈ L) :
    ∃ y ∈ L ⊓ Subgroup.centralizer ({x} : Set G), y⁻¹ * l ∈ GLAPPrimeCoreOf p L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p L with hO
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  have hxle : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.zpowers_le).2 hxL
  set T : Set G := {z | l⁻¹ * z ∈ O} with hT
  have hTinv : ∀ b ∈ Subgroup.zpowers x, ∀ t ∈ T, b * t * b⁻¹ ∈ T := by
    intro b hb t ht
    have hbO : b ∈ Subgroup.normalizer (O : Set G) := normalizer_le_normalizer_core p L (hxle hb)
    have h1 : ⁅l⁻¹, b⁆ ∈ O := hx (Subgroup.commutator_mem_commutator (L.inv_mem hl) hb)
    have h2 : b * (l⁻¹ * t) * b⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 hbO _).1 ht
    have e : l⁻¹ * (b * t * b⁻¹) = ⁅l⁻¹, b⁆ * (b * (l⁻¹ * t) * b⁻¹) := by
      simp only [commutatorElement_def]; group
    show l⁻¹ * (b * t * b⁻¹) ∈ O
    rw [e]
    exact O.mul_mem h1 h2
  let _ : MulAction ↥(Subgroup.zpowers x) ↥T :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conjActionOn _ T hTinv
  have hcardT : Nat.card T = Nat.card O := by
    refine Nat.card_congr ⟨fun z => ⟨l⁻¹ * z.1, z.2⟩, fun n => ⟨l * n.1, by simp [hT]⟩, ?_, ?_⟩
    · intro z; ext; simp
    · intro n; ext; simp
  have hpg : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_pow_eq_one hxp
  have hmod := IsPGroup.card_modEq_card_fixedPoints hpg (α := ↥T)
  have hfix : (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥T).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne] at hmod
    have h0 : Nat.card (↥(∅ : Set ↥T)) = 0 := by simp
    rw [h0, hcardT] at hmod
    exact not_dvd_card_glaPPrimeCoreOf hp L ((Nat.modEq_zero_iff_dvd).1 hmod)
  obtain ⟨c, hc⟩ := hfix
  have hcx : x * (c : G) * x⁻¹ = c := by
    have := MulAction.mem_fixedPoints.1 hc ⟨x, Subgroup.mem_zpowers x⟩
    exact congrArg Subtype.val this
  have hcO : l⁻¹ * (c : G) ∈ O := c.2
  have hcL : (c : G) ∈ L := by
    have : (c : G) = l * (l⁻¹ * c) := by group
    rw [this]; exact L.mul_mem hl (hOL hcO)
  refine ⟨c, ⟨hcL, ?_⟩, ?_⟩
  · show (c : G) ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c : G) * x = (x * c * x⁻¹) * x := by rw [hcx]
      _ = x * c := by group
  · have := O.inv_mem hcO
    simpa using this

theorem not_commutator_inf_centralizer {p : ℕ} (hp : p.Prime) {L S : Subgroup G} {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxp : x ^ p = 1)
    (hx : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf p L)
    (hSx : x ∈ Subgroup.normalizer (S : Set G)) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hcop : Nat.Coprime p (Nat.card S)) (hS : ¬ ⁅L, S⁆ ≤ GLAPPrimeCoreOf p L) :
    ¬ ⁅L, S ⊓ Subgroup.centralizer ({x} : Set G)⁆ ≤ GLAPPrimeCoreOf p L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro hS1
  apply hS
  set O := GLAPPrimeCoreOf p L with hO
  set Q : Subgroup G := centralizerQuot L O with hQ
  have hmemQ : ∀ g, g ∈ Q ↔ g ∈ Subgroup.normalizer (L : Set G) ∧
      g ∈ Subgroup.normalizer (O : Set G) ∧ ∀ y ∈ L, y * g * y⁻¹ * g⁻¹ ∈ O := fun g => Iff.rfl
  have hcommO : ∀ y ∈ L, ∀ g ∈ Subgroup.normalizer (L : Set G),
      (∀ y' ∈ L, y' * g * y'⁻¹ * g⁻¹ ∈ O) → y * g * y⁻¹ * g⁻¹ ∈ O := fun y hy g _ h => h y hy
  have hQnorm : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ g ∈ Q, n * g * n⁻¹ ∈ Q := by
    intro n hn g hg
    obtain ⟨hgL, hgO, hg3⟩ := (hmemQ g).1 hg
    refine (hmemQ _).2 ⟨?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hgL) (Subgroup.inv_mem _ hn)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (normalizer_le_normalizer_core p L hn) hgO)
        (Subgroup.inv_mem _ (normalizer_le_normalizer_core p L hn))
    · intro y hy
      have hy' : n⁻¹ * y * n ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).1 hy
        simpa using this
      have h1 := hg3 _ hy'
      have h2 := (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_core p L hn) _).1 h1
      have e : n * (n⁻¹ * y * n * g * (n⁻¹ * y * n)⁻¹ * g⁻¹) * n⁻¹ =
          y * (n * g * n⁻¹) * y⁻¹ * (n * g * n⁻¹)⁻¹ := by group
      rw [e] at h2
      exact h2
  have hxQ : x ∈ Q := by
    refine (hmemQ x).2 ⟨hxL, normalizer_le_normalizer_core p L hxL, fun y hy => ?_⟩
    exact hx (Subgroup.commutator_mem_commutator hy (Subgroup.mem_zpowers x))
  have hzQ : Subgroup.zpowers x ≤ Q := (Subgroup.zpowers_le).2 hxQ
  have hSxle : Subgroup.zpowers x ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.zpowers_le).2 hSx
  have hS1Q : S ⊓ Subgroup.centralizer ({x} : Set G) ≤ Q := by
    intro s hs
    refine (hmemQ s).2 ⟨hSL hs.1, normalizer_le_normalizer_core p L (hSL hs.1), fun y hy => ?_⟩
    exact hS1 (Subgroup.commutator_mem_commutator hy hs)
  have hcommQ : ⁅S, Subgroup.zpowers x⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro s hs g hg
    have e : ⁅s, g⁆ = (s * g * s⁻¹) * g⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact Q.mul_mem (hQnorm s (hSL hs) g (hzQ hg)) (Q.inv_mem (hzQ hg))
  have hSle := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_sup_centralizer_commutator
    (p := p) (isPGroup_zpowers_of_pow_eq_one hxp) hSxle hcop
  have hSQ : S ≤ Q := by
    refine hSle.trans (sup_le ?_ hcommQ)
    refine le_trans ?_ hS1Q
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.2
      (Subgroup.mem_zpowers x)))
  rw [Subgroup.commutator_le]
  intro y hy s hs
  exact ((hmemQ s).1 (hSQ hs)).2.2 y hy

theorem isQuasisimple_barOf {p : ℕ} (hp : p.Prime) {Z L : Subgroup G}
    (hL : GLAPComponent p Z L) : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L) := by
  have h1 := glaPComponent_of_le hp hL le_rfl hL.1
  have h2 := h1.2.2.1.2.2
  change CFSG.Open.IsQuasisimple ↥(barX p L L) at h2
  rw [barX_self] at h2
  exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv Subgroup.topEquiv h2

theorem primeCore_inf_centralizer_le {p : ℕ} (hp : p.Prime) {L : Subgroup G} {x : G}
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxp : x ^ p = 1)
    (hx : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf p L) :
    GLAPPrimeCoreOf p (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤ GLAPPrimeCoreOf p L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Y := L ⊓ Subgroup.centralizer ({x} : Set G) with hY
  set P : Subgroup ↥L := GLAPPrimeCore p ↥L with hP
  let ψ : ↥L →* ↥L ⧸ P := QuotientGroup.mk' P
  have hYL : Y ≤ L := inf_le_left
  have hOYL : GLAPPrimeCoreOf p Y ≤ L := (Subgroup.map_subtype_le _).trans hYL
  set N : Subgroup ↥L := (GLAPPrimeCoreOf p Y).subgroupOf L with hN
  set N' : Subgroup (↥L ⧸ P) := N.map ψ with hN'
  have hbot : GLAPPrimeCore p (↥L ⧸ P) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hψeq : ∀ (y : G) (hy : y ∈ Y) (l : ↥L), y⁻¹ * (l : G) ∈ GLAPPrimeCoreOf p L →
      ψ l = ψ ⟨y, hYL hy⟩ := by
    intro y hy l hyl
    obtain ⟨q, hq, hqe⟩ := hyl
    have hqe' : q = ⟨y, hYL hy⟩⁻¹ * l := Subtype.ext (by simpa using hqe)
    exact ((QuotientGroup.eq).2 (hqe' ▸ hq)).symm
  have hnorm : N'.Normal := by
    constructor
    intro z hz g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective P g
    obtain ⟨n₀, hn₀, rfl⟩ := hz
    obtain ⟨y, hy, hyo⟩ := exists_mem_inf_centralizer hp hxL hxp hx l.2
    have hn₀' : (n₀ : G) ∈ GLAPPrimeCoreOf p Y := (Subgroup.mem_subgroupOf).1 hn₀
    have h1 : ψ l = ψ ⟨y, hYL hy⟩ := hψeq y hy l hyo
    refine ⟨⟨y, hYL hy⟩ * n₀ * ⟨y, hYL hy⟩⁻¹, ?_, ?_⟩
    · show ((⟨y, hYL hy⟩ * n₀ * ⟨y, hYL hy⟩⁻¹ : ↥L) : G) ∈ GLAPPrimeCoreOf p Y
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p Y hy) (n₀ : G)).1 hn₀'
      simpa using this
    · show ψ (⟨y, hYL hy⟩ * n₀ * ⟨y, hYL hy⟩⁻¹) = ψ l * ψ n₀ * (ψ l)⁻¹
      rw [h1, map_mul, map_mul, map_inv]
  have hcop : Nat.Coprime p (Nat.card N') := by
    have h1 : Nat.card N' ∣ Nat.card N := Subgroup.card_map_dvd N ψ
    have h2 : Nat.card N = Nat.card (GLAPPrimeCoreOf p Y) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOYL).toEquiv
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf hp Y (h2 ▸ hd.trans h1)
  have hle : N' ≤ GLAPPrimeCore p (↥L ⧸ P) := le_sSup ⟨hnorm, hcop⟩
  rw [hbot] at hle
  intro n hn
  have hnL : n ∈ L := hOYL hn
  have hmem : ψ ⟨n, hnL⟩ ∈ N' := ⟨⟨n, hnL⟩, (Subgroup.mem_subgroupOf).2 hn, rfl⟩
  have h1 := hle hmem
  rw [Subgroup.mem_bot] at h1
  have h2 : (⟨n, hnL⟩ : ↥L) ∈ P := (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨⟨n, hnL⟩, h2, rfl⟩

theorem exists_mul_of_component {p : ℕ} (hp : p.Prime) {Z L K : Subgroup G} {x : G}
    (hL : GLAPComponent p Z L)
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxp : x ^ p = 1)
    (hx : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf p L)
    (hK : GLAPComponent p (L ⊓ Subgroup.centralizer ({x} : Set G)) K) {l : G} (hl : l ∈ L) :
    ∃ k ∈ K, k⁻¹ * l ∈ GLAPPrimeCoreOf p L := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set Y := L ⊓ Subgroup.centralizer ({x} : Set G) with hY
  set P : Subgroup ↥L := GLAPPrimeCore p ↥L with hP
  let ψ : ↥L →* ↥L ⧸ P := QuotientGroup.mk' P
  have hYL : Y ≤ L := inf_le_left
  have hKY : K ≤ Y := hK.1
  have hKL : K ≤ L := hKY.trans hYL
  set K' : Subgroup ↥L := K.subgroupOf L with hK'
  set Y' : Subgroup ↥L := Y.subgroupOf L with hY'
  have hsurj : Y'.map ψ = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨l₁, rfl⟩ := QuotientGroup.mk'_surjective P g
    obtain ⟨y, hy, hyo⟩ := exists_mem_inf_centralizer hp hxL hxp hx l₁.2
    refine ⟨⟨y, hy.1⟩, (Subgroup.mem_subgroupOf).2 hy, ?_⟩
    obtain ⟨q, hq, hqe⟩ := hyo
    have hqe' : q = (⟨y, hy.1⟩ : ↥L)⁻¹ * l₁ := Subtype.ext (by simpa using hqe)
    exact ((QuotientGroup.eq).2 (hqe' ▸ hq))
  have hsnK' : IsSubnormal K' Y' := isSubnormal_comap' L.subtype hK.2.1
  have hsnM : IsSubnormal (K'.map ψ) ⊤ := by
    have := isSubnormal_map' ψ hsnK'
    rwa [hsurj] at this
  have hperfK : ⁅K', K'⁆ = K' := by
    rw [← subgroupOf_commutator hKL hKL, glaPComponent_perfect hK]
  have hperf : ⁅K'.map ψ, K'.map ψ⁆ = K'.map ψ := by
    rw [← Subgroup.map_commutator, hperfK]
  have : Group.IsPerfect (K'.map ψ) := Subgroup.isPerfect_iff.2 hperf
  have hQ := isQuasisimple_barOf hp hL
  rcases CFSG.ComponentClassification.Quasisimple.perfect_subnormal_eq_bot_or_eq_top hQ
    (K'.map ψ) hsnM with hbot | htop
  · exfalso
    have hKO : K ≤ GLAPPrimeCoreOf p Y := by
      intro k hk
      have h1 : ψ ⟨k, hKL hk⟩ = 1 := by
        have : ψ ⟨k, hKL hk⟩ ∈ K'.map ψ := ⟨⟨k, hKL hk⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact this
      have h2 : (⟨k, hKL hk⟩ : ↥L) ∈ P := (QuotientGroup.eq_one_iff _).1 h1
      have h3 : k ∈ GLAPPrimeCoreOf p L := ⟨⟨k, hKL hk⟩, h2, rfl⟩
      exact gLAPPrimeCoreOf_inf_le hp L (Subgroup.centralizer ({x} : Set G)) ⟨h3, hKY hk |>.2⟩
    have hbarbot : barX p Y K = ⊥ := by
      unfold barX
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      intro k hk
      obtain ⟨q, hq, hqe⟩ := hKO ((Subgroup.mem_subgroupOf).1 hk)
      have : q = k := Subtype.ext hqe
      exact this ▸ hq
    have hq := hK.2.2.1.2.2
    change CFSG.Open.IsQuasisimple ↥(barX p Y K) at hq
    have := CFSG.ComponentClassification.Quasisimple.nontrivial hq
    exact ((barX p Y K).nontrivial_iff_ne_bot.mp inferInstance) hbarbot
  · have hmem : ψ ⟨l, hl⟩ ∈ K'.map ψ := by rw [htop]; trivial
    obtain ⟨k', hk', hk'e⟩ := hmem
    refine ⟨(k' : G), (Subgroup.mem_subgroupOf).1 hk', ?_⟩
    have h1 : k'⁻¹ * (⟨l, hl⟩ : ↥L) ∈ P := (QuotientGroup.eq).1 hk'e
    exact ⟨k'⁻¹ * ⟨l, hl⟩, h1, by simp⟩

theorem commutator_le_of_component {p : ℕ} (hp : p.Prime) {Z L K S X : Subgroup G} {x : G}
    (hL : GLAPComponent p Z L)
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxp : x ^ p = 1)
    (hx : ⁅L, Subgroup.zpowers x⁆ ≤ GLAPPrimeCoreOf p L)
    (hK : GLAPComponent p (L ⊓ Subgroup.centralizer ({x} : Set G)) K)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hSx : S ≤ Subgroup.centralizer ({x} : Set G))
    (hX : L ⊓ Subgroup.centralizer ({x} : Set G) ≤ X)
    (hKS : ⁅K, S⁆ ≤ GLAPPrimeCoreOf p X) : ⁅L, S⁆ ≤ GLAPPrimeCoreOf p L := by
  classical
  set O := GLAPPrimeCoreOf p L with hO
  set Y := L ⊓ Subgroup.centralizer ({x} : Set G) with hY
  have hKY : K ≤ Y := hK.1
  have hLN : ∀ a ∈ L, ∀ o ∈ O, a * o * a⁻¹ ∈ O := fun a ha o ho =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p L ha) o).1 ho
  rw [Subgroup.commutator_le]
  intro l hl s hs
  obtain ⟨k, hk, hkn⟩ := exists_mul_of_component hp hL hxL hxp hx hK hl
  have hsN : s ∈ Subgroup.normalizer (O : Set G) := normalizer_le_normalizer_core p L (hSL hs)
  have hkL : k ∈ L := (hKY hk).1
  have hks : ⁅k, s⁆ ∈ O := by
    have h1 : ⁅k, s⁆ ∈ GLAPPrimeCoreOf p X :=
      hKS (Subgroup.commutator_mem_commutator hk hs)
    have h2 : ⁅k, s⁆ ∈ Y := by
      refine ⟨?_, ?_⟩
      · have h3 : s * k⁻¹ * s⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.1 (hSL hs) k⁻¹).1 (L.inv_mem hkL)
        have : ⁅k, s⁆ = k * (s * k⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
        rw [this]
        exact L.mul_mem hkL h3
      · have hkc := (hKY hk).2
        have hsc := hSx hs
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hkc hsc)
          (Subgroup.inv_mem _ hkc)) (Subgroup.inv_mem _ hsc)
    have h3 : ⁅k, s⁆ ∈ GLAPPrimeCoreOf p Y := by
      have := gLAPPrimeCoreOf_inf_le hp X Y ⟨h1, h2⟩
      rwa [inf_eq_right.2 hX] at this
    exact primeCore_inf_centralizer_le hp hxL hxp hx h3
  have hns : ⁅k⁻¹ * l, s⁆ ∈ O := by
    have : ⁅k⁻¹ * l, s⁆ = (k⁻¹ * l) * (s * (k⁻¹ * l)⁻¹ * s⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact O.mul_mem hkn ((Subgroup.mem_normalizer_iff.1 hsN _).1 (O.inv_mem hkn))
  have e : ⁅l, s⁆ = (k * ⁅k⁻¹ * l, s⁆ * k⁻¹) * ⁅k, s⁆ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact O.mul_mem (hLN k hkL _ hns) hks

theorem glaPComponent_of_isSubnormal {p : ℕ} (hp : p.Prime) {H M K : Subgroup G}
    (hK : GLAPComponent p H K) (hHM : H ≤ M) (hsnM : IsSubnormal K M) :
    GLAPComponent p M K := by
  obtain ⟨hKH, hsnH, hcomp, hmin⟩ := hK
  have hKM : K ≤ M := hKH.trans hHM
  refine ⟨hKM, hsnM, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := M) p hsnM
    rwa [barX_self] at this
  · have e : ↥(barX p H K) ≃* ↥(barX p M K) :=
      (quotEquivBarX hp hKH hsnH).symm.trans (quotEquivBarX hp hKM hsnM)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J hJ hJsn heq
    have hJL : J ≤ K := hJ.le
    have hcoreL : K ⊓ GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnM]
      exact glaPPrimeCoreOf_le_of_isSubnormal p hsnH
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn (hJL.trans hKH) hHM
    refine hmin J hJ hJsnH ?_
    show barX p H J = barX p H K
    refine le_antisymm (barX_mono p hJL) ?_
    refine barX_le_of_forall (hJL.trans hKH) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) (le_of_eq heq.symm) hk (hKM hk)
    exact ⟨j, hj, hcoreL ⟨K.mul_mem (K.inv_mem (hJL hj)) hk, hjk⟩⟩

theorem le_normalizer_of_input11_6' (i11 : Input11_6) {G : Type} [Group G] [Finite G]
    (hK : CFSG.Open.IsKProper G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {C B X L : Subgroup G}
    (hCtop : C ≠ ⊤) (hBC : B ≤ C) (hXC : X ≤ C) (hSC : IsSCp p ⊤ B)
    (hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C))
    (hX : Nat.Coprime p (Nat.card X))
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hL : GLAPComponent p C L) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  have hKC : CFSG.Open.IsKGroup ↥C := isKGroup_of_isKProper hK hCtop
  have hSC' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf hSC hBC
  have hcop : Nat.Coprime p (Nat.card (X.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]
    exact hX
  have hnorm : B.subgroupOf C ≤ Subgroup.normalizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.1 (hBX ((Subgroup.mem_subgroupOf).1 hb)) (x : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hmain := i11 ↥C hKC p hp hp2 (B.subgroupOf C) hSC' hrank (X.subgroupOf C) hcop hnorm
    (L.subgroupOf C) (glaPComponent_top hL)
  intro x hx
  have hxX : (⟨x, hXC hx⟩ : ↥C) ∈ X.subgroupOf C := (Subgroup.mem_subgroupOf).2 hx
  have hxn := Subgroup.mem_normalizer_iff.1 (hmain hxX)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := (hxn ⟨y, hL.1 hy⟩).1 ((Subgroup.mem_subgroupOf).2 hy)
    exact (Subgroup.mem_subgroupOf).1 (by simpa using h1)
  · intro hy
    have hyC : y ∈ C := by
      have : x * y * x⁻¹ ∈ C := hL.1 hy
      have := C.mul_mem (C.mul_mem (C.inv_mem (hXC hx)) this) (hXC hx)
      simpa [mul_assoc] using this
    have h1 := (hxn ⟨y, hyC⟩).2 ((Subgroup.mem_subgroupOf).2 (by simpa using hy))
    exact (Subgroup.mem_subgroupOf).1 h1

omit [Finite G] in
theorem commutator_iSup_le {p : ℕ} {X S : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ K ∈ 𝒞, K ≤ X) (h : ∀ K ∈ 𝒞, ⁅K, S⁆ ≤ GLAPPrimeCoreOf p X) :
    ⁅⨆ K ∈ 𝒞, K, S⁆ ≤ GLAPPrimeCoreOf p X := by
  set O := GLAPPrimeCoreOf p X with hO
  have hXO : ∀ a ∈ X, ∀ o ∈ O, a * o * a⁻¹ ∈ O := fun a ha o ho =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf p X ha) o).1 ho
  let P : Subgroup G :=
    { carrier := {a | a ∈ X ∧ ∀ s ∈ S, ⁅a, s⁆ ∈ O}
      one_mem' := ⟨X.one_mem, fun s _ => by simp⟩
      mul_mem' := by
        rintro a₁ a₂ ⟨ha₁, h₁⟩ ⟨ha₂, h₂⟩
        refine ⟨X.mul_mem ha₁ ha₂, fun s hs => ?_⟩
        have e : ⁅a₁ * a₂, s⁆ = (a₁ * ⁅a₂, s⁆ * a₁⁻¹) * ⁅a₁, s⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact O.mul_mem (hXO a₁ ha₁ _ (h₂ s hs)) (h₁ s hs)
      inv_mem' := by
        rintro a ⟨ha, h⟩
        refine ⟨X.inv_mem ha, fun s hs => ?_⟩
        have e : ⁅a⁻¹, s⁆ = a⁻¹ * (⁅a, s⁆)⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact hXO a⁻¹ (X.inv_mem ha) _ (O.inv_mem (h s hs)) }
  have hle : (⨆ K ∈ 𝒞, K) ≤ P := by
    refine iSup₂_le fun K hK k hk => ?_
    exact ⟨h𝒞 K hK hk, fun s hs => h K hK (Subgroup.commutator_mem_commutator hk hs)⟩
  rw [Subgroup.commutator_le]
  intro a ha s hs
  exact (hle ha).2 s hs

omit [Finite G] in
theorem commutator_gLBConj_le {p : ℕ} {K S : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (S : Set G)) (h : ⁅K, S⁆ ≤ GLAPPrimeCoreOf p K) :
    ⁅GLBConj e K, S⁆ ≤ GLAPPrimeCoreOf p (GLBConj e K) := by
  have h1 : GLBConj e ⁅K, S⁆ = ⁅GLBConj e K, GLBConj e S⁆ :=
    Subgroup.map_commutator K S (MulAut.conj e⁻¹).toMonoidHom
  rw [mem_normalizer_iff_gLBConj_eq.1 he] at h1
  rw [← h1, glaPPrimeCoreOf_gLBConj]
  exact gLBConj_mono e h

end Lemma33Ns

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.UniquenessMaximal Lemma33Ns

theorem lemma33_of_inputs (i11 : Input11_6) (i18 : Input18_3_4) : Lemma33 := by
  intro G _ _ m p hS B hB hsc b hb hb1 L hL hnb hBL x hx hx1 hxL
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have := hS.simple
  have hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv => elemAbelian_comm hB.1 hu hv
  have hxp : x ^ p = 1 := hB.1.2 x hx
  have hbp : b ^ p = 1 := hB.1.2 b hb
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  have hBCb : B ≤ Cb := fun b' hb' => Subgroup.mem_centralizer_singleton_iff.2 (hcomm b' hb' b hb)
  have hBCx : B ≤ Cx := fun b' hb' => Subgroup.mem_centralizer_singleton_iff.2 (hcomm b' hb' x hx)
  have hCxtop : Cx ≠ ⊤ := by
    intro htop
    have hcenter : x ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Cx := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_singleton_iff.1 this)
    have hcbot : Subgroup.center G = ⊥ := by
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · obtain ⟨a, c, hac⟩ := hS.nonabelian
        exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c : c ∈ Subgroup.center G) a)
          hac
    rw [hcbot, Subgroup.mem_bot] at hcenter
    exact hx1 hcenter
  have hxL' : x ∈ Subgroup.normalizer (L : Set G) := hBL hx
  unfold IsStronglyLocallyOneBalanced at hnb
  push Not at hnb
  obtain ⟨S, hSLC, hScop, hSB, hSnot⟩ := hnb
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := fun s hs => (hSLC hs).1
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := fun g hg => hSB ⟨hg, hBL hg⟩
  set S₁ := S ⊓ Cx with hS₁
  have hS₁N : B ≤ Subgroup.normalizer (S₁ : Set G) := by
    intro g hg
    have h1 := hBS hg
    have h2 : g ∈ Subgroup.normalizer (Cx : Set G) := Subgroup.le_normalizer (hBCx hg)
    rw [mem_normalizer_iff_gLBConj_eq] at h1 h2 ⊢
    rw [gLBConj_inf, h1, h2]
  have hS₁cop : Nat.Coprime p (Nat.card S₁) :=
    hScop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
  have hS₁nc : ¬ ⁅L, S₁⁆ ≤ GLAPPrimeCoreOf p L :=
    not_commutator_inf_centralizer hp hxL' hxp hxL (hBS hx) hSL hScop hSnot
  have hS₁L : S₁ ≤ Subgroup.normalizer (L : Set G) := inf_le_left.trans hSL
  have hS₁Cx : S₁ ≤ Cx := inf_le_right
  have hrank : GLATwoLocalRank p ↥Cx ≤ CFSG.Open.pRank p (B.subgroupOf Cx) := by
    refine (glaTwoLocalRank_subgroup_le hp.one_lt Cx).trans ?_
    rw [hS.rank_eq]
    refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl ((isSCp_subgroupOf hsc hBCx).2.1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBCx).toEquiv, hB.2.1, hS.rank_eq]
  have h11 : ∀ K' : Subgroup G, GLAPComponent p Cx K' → S₁ ≤ Subgroup.normalizer (K' : Set G) :=
    fun K' hK' => le_normalizer_of_input11_6' i11 hS.kProper hp hp2 hCxtop hBCx hS₁Cx hsc hrank
      hS₁cop hS₁N hK'
  unfold GLAPLayer
  refine sSup_le fun K hK => ?_
  have hK : GLAPComponent p (L ⊓ Cx) K := hK
  have hYW : IsSubnormal (L ⊓ Cx) (Cb ⊓ Cx) := isSubnormal_inf hL.2.1 Cx
  have hKW : GLAPComponent p (Cb ⊓ Cx) K :=
    glaPComponent_of_isSubnormal hp hK (inf_le_inf_right Cx hL.1) (isSubnormal_trans' hK.2.1 hYW)
  have hEB : Subgroup.zpowers b ≤ B := (Subgroup.zpowers_le).2 hb
  have hEel : IsElemAbelian p (Subgroup.zpowers b) := isElemAbelian_mono hB.1 hEB
  have hcentE : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) = Cb := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKW' : GLAPComponent p (Cx ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G))
      K := by
    rw [hcentE, inf_comm]
    exact hKW
  obtain ⟨𝒞, h𝒞comp, h𝒞sup, -, h𝒞trans⟩ :=
    i18 G Cx (isKGroup_of_isKProper hS.kProper hCxtop) p hp (Subgroup.zpowers b)
      (hEB.trans hBCx) hEel K hKW'
  have hKle : K ≤ ⨆ K' ∈ 𝒞, K' := by
    rw [h𝒞sup]
    exact le_iSup₂_of_le 1 (Subgroup.one_mem _) (le_of_eq (gLBConj_one K).symm)
  have hnon : ∀ K' ∈ 𝒞, ¬ ⁅K', S₁⁆ ≤ GLAPPrimeCoreOf p K' := by
    intro K₀ hK₀ hP
    have hall : ∀ K' ∈ 𝒞, ⁅K', S₁⁆ ≤ GLAPPrimeCoreOf p K' := by
      intro K' hK'
      obtain ⟨e, he, rfl⟩ := h𝒞trans K₀ hK₀ K' hK'
      exact commutator_gLBConj_le (hS₁N (hEB he)) hP
    have hX : ∀ K' ∈ 𝒞, ⁅K', S₁⁆ ≤ GLAPPrimeCoreOf p Cx := fun K' hK' =>
      (hall K' hK').trans (glaPPrimeCoreOf_le_of_isSubnormal p (h𝒞comp K' hK').2.1)
    have h1 := commutator_iSup_le (p := p) (X := Cx) (fun K' hK' => (h𝒞comp K' hK').1) hX
    have h2 : ⁅K, S₁⁆ ≤ GLAPPrimeCoreOf p Cx := (Subgroup.commutator_mono hKle le_rfl).trans h1
    exact hS₁nc (commutator_le_of_component hp hL hxL' hxp hxL hK hS₁L hS₁Cx inf_le_right h2)
  have hle : (⨆ K' ∈ 𝒞, K') ≤ lambdaOf p B x := by
    refine iSup₂_le fun K' hK' => ?_
    refine le_sSup ⟨h𝒞comp K' hK', fun hbal => hnon K' hK' ?_⟩
    exact hbal S₁ (le_inf (h11 K' (h𝒞comp K' hK')) hS₁Cx) hS₁cop (fun g hg => hS₁N hg.1)
  exact hKle.trans hle

end CFSG.HardMathSupport.Solomon.LocalBalance

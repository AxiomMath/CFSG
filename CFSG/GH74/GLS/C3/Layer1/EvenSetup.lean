module

public import CFSG.GH74.GLS.C3.Layer1.Split
public import CFSG.Timmesfeld.Final.Simple

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Blueprint
open scoped commutatorElement

@[expose] def EvenBCond {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup G) : Prop :=
  ∀ p f : ℕ, p.Prime → p ≠ 2 → LieModel ↥K .PSL 2 p f →
    4 ≤ pRank 2 ↥(centralizer ({x} : Set G)) ∧ ¬ IsCentralInvolution x ∧
      ((p ^ f = 5 ∧ HasElemAbelianSylowTwo (normalizer (K : Set G)) 4) ∨
        (p ^ f = 9 ∧ pRank 2 ↥(centralizer (K : Set G)) = 1))

@[expose] def EvenViolates {G : Type} [Group G] [Finite G] (x : G) (K : Subgroup G) : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ LieModel ↥K .PSL 2 p f ∧
      ¬ (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9 ∨ p ^ f = 17)) ∨ ¬ EvenBCond x K

structure EvenSel {G : Type} [Group G] [Finite G] (x : G) (K T Q : Subgroup G) : Prop where
  twoTerminal : IsTwoTerminal x K
  terminal : IsTerminalPair 2 x K
  isL2 : HasL2Model ↥K IsFM9
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  hQ : Q = T ⊓ CxK x K
  sylowQ : IsSylowOf 2 Q (centralizer (K : Set G))
  rankQ : 2 ≤ pRank 2 ↥Q
  sylowTM : IsSylowOf 2 T (normalizer (K : Set G))
  cent5 : ∀ u ∈ Q, (∀ t ∈ T, u * t = t * u) → orderOf u = 2 →
    IsSylowOf 2 T (centralizer ({u} : Set G))
  five : Nonempty (↥K ≃* alternatingGroup (Fin 5)) → T = (T ⊓ K) ⊔ Q → IsSylowOf 2 T ⊤
  violation : EvenViolates x K

@[expose] def B_even_select : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) → ∃ (x : G) (K T Q : Subgroup G), EvenSel x K T Q

@[expose] def B_even_std : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
    ∀ (x : G) (K T Q : Subgroup G), EvenSel x K T Q →
      IsStandardSubgroup K ∧ gammaK 2 Q 1 ≤ normalizer (K : Set G)

@[expose] def B_even_max : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → IsEvenType G →
    (¬ ∃ (x y : G) (K : Subgroup G), IsV2Triple x y K) →
    ∀ (x : G) (K T Q : Subgroup G), EvenSel x K T Q → IsStandardSubgroup K →
      gammaK 2 Q 1 ≤ normalizer (K : Set G) → IsCoatom (normalizer (K : Set G))

theorem isPComponent_two_of_normal' {X : Type*} [Group X] [Finite X] {L : Subgroup X}
    (hLn : L.Normal) (hL : IsQuasisimple L) (hZ : center L = ⊥) (h2 : 2 ∣ Nat.card L) :
    IsPComponent 2 L := by
  have hcore : L ⊓ pPrimeCore 2 X = ⊥ := by
    have hN : ((pPrimeCore 2 X).subgroupOf L).Normal := Subgroup.Normal.subgroupOf inferInstance L
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL hN with htop | hcen
    · exfalso
      have hle : L ≤ pPrimeCore 2 X := fun l hl => by
        have : (⟨l, hl⟩ : L) ∈ (pPrimeCore 2 X).subgroupOf L := htop ▸ Subgroup.mem_top _
        exact this
      have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop
        (h2.trans (Subgroup.card_dvd_of_le hle))
    · rw [hZ] at hcen
      rw [eq_bot_iff]
      rintro y ⟨hyL, hyO⟩
      have hy : (⟨y, hyL⟩ : L) ∈ (pPrimeCore 2 X).subgroupOf L := hyO
      have hy1 := hcen hy
      rw [Subgroup.mem_bot] at hy1 ⊢
      exact congrArg Subtype.val hy1
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hinj : ∀ a ∈ L, ∀ b ∈ L, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ pPrimeCore 2 X := QuotientGroup.eq.mp hab
    have h2 : a⁻¹ * b ∈ L ⊓ pPrimeCore 2 X := Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha) hb, h1⟩
    rw [hcore, Subgroup.mem_bot, inv_mul_eq_one] at h2
    exact h2
  refine ⟨L.map π, ⟨?_, ?_⟩, hLn.isSubnormal, rfl, ?_⟩
  · have hφ : Function.Injective (π.comp L.subtype) := fun a b hab =>
      Subtype.ext (hinj a a.2 b b.2 hab)
    have hr : (π.comp L.subtype).range = L.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MonoidHom.ofInjective hφ).trans (MulEquiv.subgroupCongr hr)) hL
  · exact (hLn.map π (QuotientGroup.mk'_surjective _)).isSubnormal
  · intro J hJL _ hJmap
    apply (lt_iff_le_not_ge.1 hJL).2
    intro l hl
    have hl' : π l ∈ J.map π := hJmap ▸ ⟨l, hl, rfl⟩
    obtain ⟨j, hj, hjl⟩ := hl'
    rw [← hinj j (hJL.le hj) l hl hjl]
    exact hj

theorem mem_centralizerSection_bot_iff' {G : Type*} [Group G] {K : Subgroup G} {c : G} :
    c ∈ centralizerSection K ⊥ ↔ ∀ k ∈ K, k * c = c * k := by
  refine ⟨fun ⟨_, _, hk⟩ k hk' => ?_, fun hc' => ?_⟩
  · have := hk k hk'
    rw [Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · have hfix : ∀ k' ∈ K, c * k' * c⁻¹ = k' := fun k' hk' => by
      rw [← hc' k' hk']; group
    have hfix' : ∀ k' ∈ K, c⁻¹ * k' * c = k' := fun k' hk' => by
      rw [mul_assoc, hc' k' hk', ← mul_assoc]; simp
    refine ⟨?_, ?_, fun k hk => ?_⟩
    · rw [mem_normalizer_iff]
      intro k
      refine ⟨fun hk => by rw [hfix k hk]; exact hk, fun hk' => ?_⟩
      have h1 := hfix' _ hk'
      have h2 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
      rw [h2] at h1
      rw [h1]; exact hk'
    · rw [mem_normalizer_iff]
      intro k
      simp [Subgroup.mem_bot]
    · rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hc' k hk)

section Sel

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q : Subgroup G}

namespace EvenSel

theorem K_simple
    (h : EvenSel x K T Q) : IsSimpleGroup ↥K := by
  obtain ⟨p, f, -, -, -, hL⟩ := h.isL2
  exact CFSG.Timmesfeld.isSimpleGroup_of_lieModel hL

theorem K_le_C (h : EvenSel x K T Q) : K ≤ centralizer ({x} : Set G) := h.terminal.2.1.1

theorem two_dvd_K (h : EvenSel x K T Q) : 2 ∣ Nat.card ↥K := h.terminal.2.2.1

theorem pPrimeCore_K
    (h : EvenSel x K T Q) : pPrimeCore 2 ↥K = ⊥ := by
  have := h.K_simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥K) with hb | ht
  · exact hb
  · exfalso
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥K)) := pPrimeCore_coprime_card
    have hcard : Nat.card (pPrimeCore 2 ↥K) = Nat.card ↥K := by
      rw [ht]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [hcard] at hcop
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop h.two_dvd_K

theorem pPrimeCoreOf_K
    (h : EvenSel x K T Q) : pPrimeCoreOf 2 K = ⊥ := by
  unfold pPrimeCoreOf
  rw [h.pPrimeCore_K, Subgroup.map_bot]

theorem CMK_eq
    (h : EvenSel x K T Q) : CMK (normalizer (K : Set G)) K = centralizer (K : Set G) := by
  ext c
  unfold CMK
  rw [h.pPrimeCoreOf_K]
  constructor
  · rintro ⟨-, hc⟩
    rw [mem_centralizer_iff]
    intro k hk
    exact mem_centralizerSection_bot_iff'.1 hc k hk
  · intro hc
    have hc' : ∀ k ∈ K, k * c = c * k := fun k hk => mem_centralizer_iff.1 hc k hk
    exact ⟨Subgroup.centralizer_le_normalizer _ hc, mem_centralizerSection_bot_iff'.2 hc'⟩

theorem isPCompIn_normalizer
    (h : EvenSel x K T Q) : IsPCompIn 2 (normalizer (K : Set G)) K := by
  have hKM : K ≤ normalizer (K : Set G) := Subgroup.le_normalizer
  refine ⟨hKM, ?_⟩
  have hKC : K ≤ centralizer ({x} : Set G) := h.K_le_C
  have hcomp : CFSG.IsComponent (K.subgroupOf (centralizer ({x} : Set G))) := h.terminal.2.1.2
  have hq : IsQuasisimple ↥(K.subgroupOf (normalizer (K : Set G))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hKC).trans (Subgroup.subgroupOfEquivOfLe hKM).symm) hcomp.1
  have hKs := h.K_simple
  have hKs' : IsSimpleGroup ↥(K.subgroupOf (normalizer (K : Set G))) :=
    (Subgroup.subgroupOfEquivOfLe hKM).isSimpleGroup
  have hZ : center ↥(K.subgroupOf (normalizer (K : Set G))) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center ↥(K.subgroupOf (normalizer (K : Set G)))) with hb | ht
    · exact hb
    · exfalso
      obtain ⟨-, -, a', b', hab'⟩ := hq
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
      apply hab'
      have : a ∈ center ↥(K.subgroupOf (normalizer (K : Set G))) := by rw [ht]; exact Subgroup.mem_top _
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 this b)]
  have h2 : 2 ∣ Nat.card ↥(K.subgroupOf (normalizer (K : Set G))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
    exact h.two_dvd_K
  exact isPComponent_two_of_normal'
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr le_rfl) hq hZ h2

end EvenSel

end Sel

theorem s_evenSetup_of_leaves
    (h1 : B_even_select) (h2 : B_even_std) (h3 : B_even_max) :
    S_evenSetup_rank4 := by
  intro G _ _ hG hE hV
  obtain ⟨x, K, T, Q, hs⟩ := h1 G hG hE hV
  obtain ⟨hstd, hgam⟩ := h2 G hG hE hV x K T Q hs
  have hmax := h3 G hG hE hV x K T Q hs hstd hgam
  refine ⟨x, K, K, normalizer (K : Set G), T, Q, ?_, ?_⟩
  · exact
    { twoTerminal := hs.twoTerminal
      maximal := hmax
      K_le_L := le_rfl
      L_normal := ⟨Subgroup.le_normalizer, fun m hm l hl => (mem_normalizer_iff.1 hm l).1 hl⟩
      L_comp := hs.isPCompIn_normalizer
      bar_eq := rfl
      sylowT := hs.sylowT
      hQ := hs.hQ
      sylowQ := by rw [hs.CMK_eq]; exact hs.sylowQ
      rankQ := hs.rankQ
      gamma := hgam
      sylowTM := hs.sylowTM
      cent5 := hs.cent5
      terminal_eq := fun _ => rfl }
  · exact
    { evenType := hE
      notRestricted := hG.notRE
      noV2 := hV
      isL2 := hs.isL2
      M_eq := rfl
      five := hs.five
      terminal := hs.terminal }

end CFSG.GH74.GLS

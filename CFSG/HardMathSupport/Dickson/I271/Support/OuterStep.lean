module

public import CFSG.HardMathSupport.Dickson.I271.Support.OuterRec
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineGen
public import CFSG.HardMathSupport.Dickson.I271.Support.OuterBasic

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

open scoped commutatorElement

section Step

variable {X : Type} [Group X] [Finite X]

theorem Chev204Hyp.quasi {p : ℕ} {K B : Subgroup X} (h : Chev204Hyp p K B) :
    CFSG.Open.IsQuasisimple ↥K :=
  i116e_isQuasisimple h.core h.comp

theorem Chev204Hyp.primeCore {p : ℕ} {K B : Subgroup X} (h : Chev204Hyp p K B) :
    GLAPPrimeCore p ↥K = ⊥ :=
  i271h_primeCore_eq_bot h.core h.comp

theorem Chev204Hyp.elem {p : ℕ} {K B : Subgroup X} (h : Chev204Hyp p K B) : IsElemAbelian p B :=
  h.scp.2.1

theorem Chev204Hyp.dvd {p : ℕ} {K B : Subgroup X} (h : Chev204Hyp p K B) : p ∣ Nat.card K :=
  i116e_dvd_card h.prime h.core h.comp

theorem Chev204Hyp.sc {p : ℕ} {K B : Subgroup X} (h : Chev204Hyp p K B) : IsSCp p (K ⊔ B) B :=
  ⟨le_sup_right, h.elem, fun E _ hEel hBE => h.scp.2.2 E le_top hEel hBE⟩

theorem not_mem_centralizer_of_faithful {K A : Subgroup X}
    (hAf : A ⊓ Subgroup.centralizer (K : Set X) = ⊥) {a : X} (ha : a ∈ A) (ha1 : a ≠ 1) :
    a ∉ Subgroup.centralizer (K : Set X) := fun h =>
  ha1 (by
    have : a ∈ A ⊓ Subgroup.centralizer (K : Set X) := ⟨ha, h⟩
    rw [hAf] at this
    exact Subgroup.mem_bot.1 this)

theorem chev204_inner {p : ℕ} (hDC : DefCharInnerCoreFree) (hKD : KDChevInner p)
    {K B A : Subgroup X} (hH : Chev204Hyp p K B) (hLie : I271LieType (· = p) K) (hAB : A ≤ B)
    (hAnc : ¬ IsCyclic ↥A) (hAf : A ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hAin : ∀ a ∈ A, ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)) :
    IsStronglyBalancedIn p B K := by
  have hp := hH.prime
  have hp2 := hH.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hAN : A ≤ Subgroup.normalizer (K : Set X) := hAB.trans hH.norm
  have hloc : IsCompLocallyBalanced p 1 A K :=
    isCompLocallyBalanced_of_inner hp hp2 hDC hH.quasi hH.primeCore hLie hAN hAin
  have hno : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      ¬ GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J := by
    intro a ha ha1 J hJ
    obtain ⟨k, hk, hc⟩ := hAin a ha
    exact no_component_of_inner hp hKD hH.quasi hH.chev (hH.elem.2 a (hAB ha))
      (not_mem_centralizer_of_faithful hAf ha ha1) hk hc hJ
  obtain ⟨a₀, ha₀A, ha₀1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hAnc
    haveI : Subsingleton ↥A :=
      ⟨fun x y => Subtype.ext ((hcon x x.2).trans (hcon y y.2).symm)⟩
    exact isCyclic_of_subsingleton
  exact engine_full ⟨hp, hp2, hH.quasi, hH.dvd, hH.norm, hH.elem, hH.sc, hAB, hAnc, hloc,
    fun a ha ha1 J hJ => (hno a ha ha1 J hJ).elim⟩
    ⟨a₀, ha₀A, ha₀1, fun w _ _ _ J hJ => (hno a₀ ha₀A ha₀1 J hJ).elim⟩

theorem mem_normalizer_inf_centralizer_of_comm {K : Subgroup X} {a w : X}
    (hw : w ∈ Subgroup.normalizer (K : Set X))
    (hc : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X)) :
    w ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) := by
  have key : ∀ {w : X}, w ∈ Subgroup.normalizer (K : Set X) →
      w * a * w⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X) →
        ∀ x ∈ K ⊓ Subgroup.centralizer ({a} : Set X),
          w * x * w⁻¹ ∈ K ⊓ Subgroup.centralizer ({a} : Set X) := by
    intro w hw hc x hx
    have hy : w * x * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hw x).1 hx.1
    refine ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    set c := w * a * w⁻¹ * a⁻¹ with hcdef
    have hca : c * a = w * a * w⁻¹ := by rw [hcdef]; group
    have hcy : (w * x * w⁻¹) * c = c * (w * x * w⁻¹) := Subgroup.mem_centralizer_iff.1 hc _ hy
    have h1 : (w * x * w⁻¹) * (w * a * w⁻¹) = (w * a * w⁻¹) * (w * x * w⁻¹) := by
      calc (w * x * w⁻¹) * (w * a * w⁻¹) = w * (x * a) * w⁻¹ := by group
        _ = w * (a * x) * w⁻¹ := by rw [hxa]
        _ = (w * a * w⁻¹) * (w * x * w⁻¹) := by group
    have h2 : (w * x * w⁻¹) * (c * a) = (c * a) * (w * x * w⁻¹) := by rw [hca]; exact h1
    have h3 : c * ((w * x * w⁻¹) * a) = c * (a * (w * x * w⁻¹)) := by
      calc c * ((w * x * w⁻¹) * a) = (c * (w * x * w⁻¹)) * a := by group
        _ = ((w * x * w⁻¹) * c) * a := by rw [hcy]
        _ = (w * x * w⁻¹) * (c * a) := by group
        _ = (c * a) * (w * x * w⁻¹) := h2
        _ = c * (a * (w * x * w⁻¹)) := by group
    exact mul_left_cancel h3
  have hwinv : w⁻¹ ∈ Subgroup.normalizer (K : Set X) := inv_mem hw
  have hcinv : w⁻¹ * a * w⁻¹⁻¹ * a⁻¹ ∈ Subgroup.centralizer (K : Set X) := by
    have h1 : w⁻¹ * (w * a * w⁻¹ * a⁻¹)⁻¹ * w⁻¹⁻¹ ∈ Subgroup.centralizer (K : Set X) :=
      conj_mem_centralizer hwinv (inv_mem hc)
    convert h1 using 1
    group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key hw hc x, fun hx => ?_⟩
  have := key hwinv hcinv _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_of_unique {p : ℕ} {K B J : Subgroup X} {a : X}
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hBel : IsElemAbelian p B) (haB : a ∈ B)
    (huniq : ∀ I J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) I →
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J → I = J)
    (hJ : GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J) :
    B ≤ Subgroup.normalizer (J : Set X) := by
  intro b hb
  have hbC : b ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({a} : Set X) : Subgroup X) : Set X) :=
    mem_normalizer_inf (hBK hb) (Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.2
        (CFSG.Open.IsElemAbelian.comm hBel hb haB)))
  have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ b
  rw [(mem_normalizer_iff_gLBConj_eq).1 hbC] at h1
  exact (mem_normalizer_iff_gLBConj_eq).2 (huniq _ J h1 hJ)

theorem chev204_outer {p : ℕ} (hDC : DefCharInnerCoreFree) (hOut : DefCharOuterCoreFree)
    (hK65 : KD65 p) (hKD : KDChevInner p) (hCent : ChevCentralizerStep)
    (ih : ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < Nat.card X →
      ∀ K' B' : Subgroup Y, Chev204Hyp p K' B' → ¬ ChevExc p K' B' → IsStronglyBalancedIn p B' K')
    {K B A : Subgroup X} (hH : Chev204Hyp p K B) (hLie : I271LieType (· = p) K)
    (hne : ¬ ChevExc p K B) (hAB : A ≤ B) (hAnc : ¬ IsCyclic ↥A)
    (hAf : A ⊓ Subgroup.centralizer (K : Set X) = ⊥) {a₁ : X} (ha₁ : a₁ ∈ A)
    (hout₁ : ¬ ∃ k ∈ K, k⁻¹ * a₁ ∈ Subgroup.centralizer (K : Set X)) :
    IsStronglyBalancedIn p B K := by
  have hp := hH.prime
  have hp2 := hH.odd
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center ↥K = ⊥ := center_eq_bot_of_outer hK65 hH (hAB ha₁) hout₁
  have hexc : ¬ (p = 3 ∧ IsLTwoTwentySeven (↥K ⧸ Subgroup.center ↥K)) := by
    rintro ⟨h3, hL⟩
    apply hne
    refine ⟨h3, Or.inl ⟨hL, fun hinn => ?_⟩⟩
    exact hout₁ (hinn a₁ ⟨hAB ha₁, hH.norm (hAB ha₁)⟩)
  have hloc : IsCompLocallyBalanced p 1 A K :=
    isCompLocallyBalanced_of_charp hp hp2 hDC hOut hH.quasi hH.primeCore hLie hexc
  have ha₁1 : a₁ ≠ 1 := by
    rintro rfl
    exact hout₁ ⟨1, K.one_mem, by simp⟩
  have hcomp : ∀ a ∈ A, a ≠ 1 → ∀ J : Subgroup X,
      GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
        B ≤ Subgroup.normalizer (J : Set X) ∧ IsStronglyLocallyOneBalanced p B a J := by
    intro a ha ha1 J hJ
    have haC : a ∉ Subgroup.centralizer (K : Set X) := not_mem_centralizer_of_faithful hAf ha ha1
    by_cases hin : ∃ k ∈ K, k⁻¹ * a ∈ Subgroup.centralizer (K : Set X)
    · exfalso
      obtain ⟨k, hk, hc⟩ := hin
      exact no_component_of_inner hp hKD hH.quasi hH.chev (hH.elem.2 a (hAB ha)) haC hk hc hJ
    · obtain ⟨huniq, htype⟩ := hCent X p K B hH hLie hZ a (hAB ha) ha1 hin
      have hBa : ∀ b ∈ B, a * b = b * a := fun b hb =>
        CFSG.Open.IsElemAbelian.comm hH.elem (hAB ha) hb
      have hBN : B ≤ Subgroup.normalizer (J : Set X) :=
        le_normalizer_of_unique hH.norm hH.elem (hAB ha) huniq hJ
      refine ⟨hBN, ?_⟩
      set C := Subgroup.centralizer ({a} : Set X) with hC
      have hBC : B ≤ C := fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hBa b hb).symm
      have hJC : GLAPComponent p C J := glaPComponent_centralizer hp hH.comp.2.1 hJ
      obtain ⟨hcoreC, hcompC, hSCC, hBNC⟩ := recursionData hp hJC hBC hBN hH.scp
      have hlt := card_bar_lt (centralizer_ne_top_of_not_mem haC) (GLAPPrimeCore p ↥C)
      obtain ⟨hchev, hnexc⟩ := htype J hJ
      have hbal := ih (↥C ⧸ GLAPPrimeCore p ↥C) hlt (barX p C J) (barX p C B)
        ⟨hp, hp2, hcoreC, hcompC, hSCC, hBNC, hchev⟩ hnexc
      exact stronglyLocallyOneBalanced_of_bar hp hJC.2.1 hBN hbal
  have hc : ∃ a ∈ A, a ≠ 1 ∧ ∀ w ∈ Subgroup.normalizer (K : Set X), Nat.Coprime p (orderOf w) →
      (∀ b ∈ B, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.centralizer (K : Set X)) →
        ∀ J : Subgroup X, GLAPComponent p (K ⊓ Subgroup.centralizer ({a} : Set X)) J →
          w ∈ Subgroup.normalizer (J : Set X) := by
    refine ⟨a₁, ha₁, ha₁1, fun w hw _ hwB J hJ => ?_⟩
    obtain ⟨huniq, -⟩ := hCent X p K B hH hLie hZ a₁ (hAB ha₁) ha₁1 hout₁
    have hwC := mem_normalizer_inf_centralizer_of_comm hw (hwB a₁ (hAB ha₁))
    have h1 := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hJ w
    rw [(mem_normalizer_iff_gLBConj_eq).1 hwC] at h1
    exact (mem_normalizer_iff_gLBConj_eq).2 (huniq _ J h1 hJ)
  exact engine_full ⟨hp, hp2, hH.quasi, hH.dvd, hH.norm, hH.elem, hH.sc, hAB, hAnc, hloc, hcomp⟩
    hc

end Step

end CFSG.HardMathSupport.Dickson.I271

module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigInvCore
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.Open CFSG.Goldschmidt.G3a
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem centralizer_le_normalizer_of_borelSetup {T : Sylow 2 X} {D : Subgroup X}
    (h : BorelSetup T D) {x : X} (hxT : x ∈ (T : Subgroup X)) (hx2 : orderOf x = 2) :
    (T : Subgroup X) ≤ centralizer ({x} : Set X) ∧
      centralizer ({x} : Set X) ≤ normalizer ((T : Subgroup X) : Set X) := by
  have hxZ : x ∈ sylowCenter (T : Subgroup X) :=
    h.inv x hxT (by rw [← hx2, pow_orderOf_eq_one])
  refine ⟨fun t ht => mem_centralizer_singleton_iff.mpr ((mem_sylowCenter.mp hxZ).2 t ht), ?_⟩
  intro g hg
  by_contra hgM
  have hodd := h.se.2.2 g hgM
  have hxM : x ∈ normalizer ((T : Subgroup X) : Set X) := le_normalizer hxT
  have hxc : x ∈ (normalizer ((T : Subgroup X) : Set X)).map (MulAut.conj g⁻¹).toMonoidHom := by
    refine ⟨x, hxM, ?_⟩
    have hc : g * x = x * g := mem_centralizer_singleton_iff.mp hg
    change g⁻¹ * x * g⁻¹⁻¹ = x
    rw [inv_inv, mul_assoc, ← hc, inv_mul_cancel_left]
  set I := normalizer ((T : Subgroup X) : Set X) ⊓
    (normalizer ((T : Subgroup X) : Set X)).map (MulAut.conj g⁻¹).toMonoidHom with hI
  have h1 := orderOf_dvd_natCard (⟨x, mem_inf.mpr ⟨hxM, hxc⟩⟩ : ↥I)
  have h0 : orderOf (⟨x, mem_inf.mpr ⟨hxM, hxc⟩⟩ : ↥I) = 2 :=
    (orderOf_injective _ I.subtype_injective _).symm.trans hx2
  rw [h0] at h1
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h1)

theorem involutionOddCore_eq_bot_of_borelSetup {T : Sylow 2 X} {D : Subgroup X}
    (h : BorelSetup T D) {x : X} (hxT : x ∈ (T : Subgroup X)) (hx2 : orderOf x = 2) :
    Assembly.Dichotomy.involutionOddCore x = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTC, hCN⟩ := centralizer_le_normalizer_of_borelSetup h hxT hx2
  set O := Assembly.Dichotomy.involutionOddCore x with hO
  have hOodd : Odd (Nat.card O) := by
    rw [hO, ClassicalInvolution.Balance.involutionOddCore_eq_oddCoreCentralizer]
    exact ClassicalInvolution.Balance.odd_card_oddCoreCentralizer _
  have hOC : O ≤ centralizer ({x} : Set X) := by
    rw [hO, ClassicalInvolution.Balance.involutionOddCore_eq_oddCoreCentralizer,
      ← CFSG.ClassicalInvolution.Balance.centralizer_zpowers_eq]
    exact ClassicalInvolution.Balance.oddCoreCentralizer_le_centralizer _
  have hOT : ∀ y ∈ O, y ∈ (T : Subgroup X) → y = 1 := by
    intro y hyO hyT
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨y, hyT⟩
    rw [Subgroup.orderOf_mk] at hn
    have hdvd : orderOf y ∣ Nat.card O := by
      have := orderOf_dvd_natCard (⟨y, hyO⟩ : O)
      rwa [Subgroup.orderOf_mk] at this
    have hodd : Odd (orderOf y) := hOodd.of_dvd_nat hdvd
    have hn0 : n = 0 := by
      by_contra hn0
      rw [hn] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hn0⟩)
    rw [hn0, pow_zero] at hn
    exact orderOf_eq_one_iff.mp hn
  rw [eq_bot_iff]
  intro o ho
  rw [mem_bot]
  have hoT : o ∈ centralizer ((T : Subgroup X) : Set X) := by
    rw [mem_centralizer_iff]
    intro t ht
    have hoN : o ∈ normalizer ((T : Subgroup X) : Set X) := hCN (hOC ho)
    have h1 : o * t * o⁻¹ * t⁻¹ ∈ O := by
      have := ClassicalInvolution.Balance.conj_mem_involutionOddCore (hTC ht) (inv_mem ho)
      have h2 := mul_mem ho this
      simpa [mul_assoc] using h2
    have h2 : o * t * o⁻¹ * t⁻¹ ∈ (T : Subgroup X) :=
      mul_mem ((mem_normalizer_iff.mp hoN t).mp ht) (inv_mem ht)
    have h3 := hOT _ h1 h2
    have : o * t = t * o := by
      calc o * t = (o * t * o⁻¹ * t⁻¹) * t * o := by group
        _ = t * o := by rw [h3, one_mul]
    exact this.symm
  exact hOT o ho (h.cent hoT)

theorem eq_one_of_odd_of_centralizes_sylow [IsSimpleGroup X] {T : Sylow 2 X} {D : Subgroup X}
    (h : BorelSetup T D) (β : MulAut X) (hβodd : Odd (orderOf β))
    (hβT : ∀ t ∈ (T : Subgroup X), β t = t) : β = 1 := by
  set r := orderOf β with hr
  have hβr : β ^ r = 1 := pow_orderOf_eq_one β
  obtain ⟨S₀, h₀⟩ := h.exists_ne_sylow
  have hβT' : β • T = T := Omega.smul_eq_of_mapsTo fun s hs => by rw [hβT s hs]; exact hs
  have hβS₀ : β • S₀ ≠ T := by
    intro hS
    apply h₀
    calc S₀ = β⁻¹ • (β • S₀) := (inv_smul_smul β S₀).symm
      _ = β⁻¹ • (β • T) := by rw [hS, hβT']
      _ = T := inv_smul_smul β T
  obtain ⟨r₀, hr₀, hr₀S⟩ := Omega.exists_smul_eq h.se h.card h₀ hβS₀
  have hpowS : ∀ j : ℕ, (β ^ j) • S₀ = r₀ ^ j • S₀ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, ih, Omega.smul_conj_smul, hβT _ ((T : Subgroup X).pow_mem hr₀ j),
        ← hr₀S, ← mul_smul, ← pow_succ]
  have h1 : r₀ ^ r • S₀ = S₀ := by rw [← hpowS r, hβr, one_smul]
  have h2 : r₀ ^ r = 1 := Omega.eq_one_of_mem_normalizer h.se h₀
    ((T : Subgroup X).pow_mem hr₀ r) (Sylow.smul_eq_iff_mem_normalizer.mp h1)
  have h3 : r₀ = 1 := BorelSetup.eq_one_of_pow_odd (T := T) hr₀ hβodd h2
  have hβS : β • S₀ = S₀ := by rw [← hr₀S, h3, one_smul]
  exact Omega.eq_one_of_centralizes h.se h.card h₀ β hβT' hβS hβT

theorem isInvolutionCoreFree_of_isBenderGroup
    (hX : fusionIsBenderGroup X) : IsInvolutionCoreFree X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup X :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hX
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨D₀, h₀⟩ := exists_borelSetup hX T₀
  have hZ : center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with hb | ht
    · exact hb
    · exfalso
      apply h₀.se.1
      rw [eq_top_iff]
      intro g _
      rw [mem_normalizer_iff]
      intro t
      have hg : g ∈ center X := ht ▸ mem_top g
      rw [← mem_center_iff.mp hg t, mul_inv_cancel_right]
  have hcase : ∀ x : X, x * x = 1 → x ≠ 1 →
      ∃ (T : Sylow 2 X) (D : Subgroup X), BorelSetup T D ∧ x ∈ (T : Subgroup X) ∧
        orderOf x = 2 := by
    intro x hx2 hx1
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
    have hxp : IsPGroup 2 (zpowers x) :=
      ClassicalInvolution.Balance.isPGroup_zpowers_of_mul_self_eq_one hx2
    obtain ⟨T, hT⟩ := hxp.exists_le_sylow
    obtain ⟨D, hD⟩ := exists_borelSetup hX T
    exact ⟨T, D, hD, hT (mem_zpowers x), hxo⟩
  refine isInvolutionCoreFree_of_rigid hZ (fun x hx2 => ?_) (fun x hx2 β hβ hβC => ?_)
  · by_cases hx1 : x = 1
    ·
      subst hx1
      set O := Assembly.Dichotomy.involutionOddCore (1 : X) with hO
      have hOn : O.Normal := by
        constructor
        intro y hy g
        exact ClassicalInvolution.Balance.conj_mem_involutionOddCore
          (mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])) hy
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal O with hb | ht
      · exact hb
      · exfalso
        have hOodd : Odd (Nat.card O) := by
          rw [hO, ClassicalInvolution.Balance.involutionOddCore_eq_oddCoreCentralizer]
          exact ClassicalInvolution.Balance.odd_card_oddCoreCentralizer _
        rw [ht, Subgroup.card_top] at hOodd
        have h4 := h₀.four
        have hdvd : Nat.card (sylowCenter (T₀ : Subgroup X)) ∣ Nat.card X :=
          Subgroup.card_subgroup_dvd_card _
        have heven : Even (Nat.card (sylowCenter (T₀ : Subgroup X))) := by
          have hp := (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter_le
            (T₀ : Subgroup X))
          obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp ((T₀.isPGroup').to_le hp))
          rw [hn] at h4 ⊢
          rcases n with _ | n
          · norm_num at h4
          · exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        exact (Nat.not_even_iff_odd.mpr (hOodd.of_dvd_nat hdvd)) heven
    · obtain ⟨T, D, hD, hxT, hxo⟩ := hcase x hx2 hx1
      exact involutionOddCore_eq_bot_of_borelSetup hD hxT hxo
  · by_cases hx1 : x = 1
    · subst hx1
      ext g
      exact hβC g (mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one]))
    · obtain ⟨T, D, hD, hxT, hxo⟩ := hcase x hx2 hx1
      have hTC := (centralizer_le_normalizer_of_borelSetup hD hxT hxo).1
      exact eq_one_of_odd_of_centralizes_sylow hD β hβ fun t ht => hβC t (hTC ht)

end CFSG.ComponentClassification.Sol76.Sig

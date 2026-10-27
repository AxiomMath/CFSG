module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoGroup
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitFooteM
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_fixed_mod_two_of_involutive {I : Type*} [Finite I] (σ : Equiv.Perm I)
    (hσ : Function.Involutive σ) :
    Nat.card {x : I // σ x = x} % 2 = Nat.card I % 2 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hcongruence := Equiv.Perm.card_fixedPoints_modEq
    (f := (fun x : I => σ x)) (p := 2) (n := 1) (by
      funext x
      exact hσ x)
  have heq : Fintype.card I % 2 = Fintype.card {x : I // σ x = x} % 2 := hcongruence
  simpa only [Nat.card_eq_fintype_card] using heq.symm

theorem exists_mul_mem_centralizer_of_odd {O : Subgroup G} (hO : Odd (Nat.card O)) {w d : G}
    (hw2 : w ^ 2 = 1) (hwO : w ∈ normalizer (O : Set G)) (hd : d⁻¹ * (w * d * w⁻¹) ∈ O) :
    ∃ o ∈ O, d * o ∈ centralizer ({w} : Set G) := by
  have hww : w * w = 1 := by rw [← sq]; exact hw2
  have hmem : ∀ o ∈ O, d⁻¹ * w * d * o * w⁻¹ ∈ O := by
    intro o ho
    have h1 : w * o * w⁻¹ ∈ O := (mem_normalizer_iff.mp hwO o).mp ho
    have h2 : d⁻¹ * w * d * o * w⁻¹ = (d⁻¹ * (w * d * w⁻¹)) * (w * o * w⁻¹) := by group
    rw [h2]
    exact mul_mem hd h1
  have hinv : ∀ o : G, d⁻¹ * w * d * (d⁻¹ * w * d * o * w⁻¹) * w⁻¹ = o := by
    intro o
    calc d⁻¹ * w * d * (d⁻¹ * w * d * o * w⁻¹) * w⁻¹
        = d⁻¹ * (w * w) * d * o * (w * w)⁻¹ := by group
      _ = o := by rw [hww]; group
  let σ : Equiv.Perm O :=
    { toFun := fun o => ⟨d⁻¹ * w * d * o * w⁻¹, hmem o o.2⟩
      invFun := fun o => ⟨d⁻¹ * w * d * o * w⁻¹, hmem o o.2⟩
      left_inv := fun o => Subtype.ext (hinv o)
      right_inv := fun o => Subtype.ext (hinv o) }
  have hσ : Function.Involutive σ := fun o => Subtype.ext (hinv o)
  have hmod := card_fixed_mod_two_of_involutive σ hσ
  have hpos : 0 < Nat.card {o : O // σ o = o} := by
    have := Nat.odd_iff.mp hO
    omega
  obtain ⟨⟨⟨o, ho⟩, hfix⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have hfix' : d⁻¹ * w * d * o * w⁻¹ = o := congrArg Subtype.val hfix
  refine ⟨o, ho, mem_centralizer_singleton_iff.mpr ?_⟩
  calc d * o * w = d * (d⁻¹ * w * d * o * w⁻¹) * w := by rw [hfix']
    _ = w * (d * o) * (w⁻¹ * w) := by group
    _ = w * (d * o) := by rw [inv_mul_cancel, mul_one]

theorem relIndex_eq_relIndex_inf_of_mul {A B N : Subgroup G} [(N.subgroupOf B).Normal]
    (hAB : A ≤ B) (hNB : N ≤ B) (hfac : ∀ b ∈ B, ∃ a ∈ A, ∃ n ∈ N, b = a * n) :
    A.relIndex B = (A ⊓ N).relIndex N := by
  set φ : A →* B ⧸ N.subgroupOf B :=
    (QuotientGroup.mk' (N.subgroupOf B)).comp (Subgroup.inclusion hAB) with hφdef
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨⟨b, hb⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, n, hn', rfl⟩ := hfac b hb
    refine ⟨⟨a, ha⟩, ?_⟩
    show (QuotientGroup.mk (⟨a, hAB ha⟩ : B)) = QuotientGroup.mk ⟨a * n, hb⟩
    rw [QuotientGroup.eq]
    show ((a⁻¹ * (a * n) : G)) ∈ N
    simpa using hn'
  have hker : φ.ker = (A ⊓ N).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk (⟨(x : G), hAB x.2⟩ : B) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hcard : Nat.card B * Nat.card (A ⊓ N : Subgroup G) = Nat.card A * Nat.card N := by
    have e := (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf B)
    have h3 : Nat.card φ.ker = Nat.card (A ⊓ N : Subgroup G) := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h4 : Nat.card (N.subgroupOf B) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
    rw [Nat.card_congr e, h3] at h1
    rw [h4] at h2
    rw [h2, h1]
    ring
  have h1 : Nat.card A * A.relIndex B = Nat.card B := by
    have := Subgroup.card_mul_index (A.subgroupOf B)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv] at this
  have h2 : Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N = Nat.card N := by
    have := Subgroup.card_mul_index ((A ⊓ N).subgroupOf N)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at this
  have hA : 0 < Nat.card A := Nat.card_pos
  have hD : 0 < Nat.card (A ⊓ N : Subgroup G) := Nat.card_pos
  have key : Nat.card A * Nat.card (A ⊓ N : Subgroup G) * A.relIndex B =
      Nat.card A * Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N := by
    calc Nat.card A * Nat.card (A ⊓ N : Subgroup G) * A.relIndex B
        = Nat.card (A ⊓ N : Subgroup G) * (Nat.card A * A.relIndex B) := by ring
      _ = Nat.card (A ⊓ N : Subgroup G) * Nat.card B := by rw [h1]
      _ = Nat.card A * Nat.card N := by rw [mul_comm]; exact hcard
      _ = Nat.card A * (Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N) := by rw [h2]
      _ = Nat.card A * Nat.card (A ⊓ N : Subgroup G) * (A ⊓ N).relIndex N := by ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hA hD) key

theorem exists_conj_le_centralizer_of_odd {O F : Subgroup G} (hO : Odd (Nat.card O))
    (hFO : F ≤ normalizer (O : Set G)) (hFp : IsPGroup 2 F) {w : G} (hw2 : w ^ 2 = 1)
    (hwO : w ∈ normalizer (O : Set G)) (hwF : ∀ f ∈ F, f⁻¹ * (w * f * w⁻¹) ∈ O) :
    ∃ k ∈ F ⊔ O, conjugate F k ≤ centralizer ({w} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := F ⊔ O with hD
  have hOD : O ≤ D := le_sup_right
  have hDmul : ∀ d ∈ D, ∃ f ∈ F, ∃ o ∈ O, f * o = d := by
    intro d hd
    have h1 : d ∈ ((F : Set G) * O) := by
      rw [← coe_mul_of_left_le_normalizer_right F O hFO]
      exact hd
    obtain ⟨f, hf, o, ho, hfo⟩ := Set.mem_mul.mp h1
    exact ⟨f, hf, o, ho, hfo⟩
  set X := D ⊓ centralizer ({w} : Set G) with hX
  have hXD : X ≤ D := inf_le_left
  have hcover : ∀ d ∈ D, ∃ x ∈ X, ∃ o ∈ O, d = x * o := by
    intro d hd
    obtain ⟨f, hf, o₀, ho₀, rfl⟩ := hDmul d hd
    have hd' : (f * o₀)⁻¹ * (w * (f * o₀) * w⁻¹) ∈ O := by
      have h1 : f⁻¹ * (w * f * w⁻¹) ∈ O := hwF f hf
      have h2 : w * o₀ * w⁻¹ ∈ O := (mem_normalizer_iff.mp hwO o₀).mp ho₀
      have h3 : (f * o₀)⁻¹ * (w * (f * o₀) * w⁻¹) =
          o₀⁻¹ * (f⁻¹ * (w * f * w⁻¹)) * (w * o₀ * w⁻¹) := by group
      rw [h3]
      exact mul_mem (mul_mem (inv_mem ho₀) h1) h2
    obtain ⟨o, ho, hdo⟩ := exists_mul_mem_centralizer_of_odd hO hw2 hwO hd'
    exact ⟨f * o₀ * o, mem_inf.mpr ⟨mul_mem hd (hOD ho), hdo⟩, o⁻¹, inv_mem ho, by group⟩
  have hDN : D ≤ normalizer (O : Set G) := sup_le hFO le_normalizer
  have : (O.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hOD).mpr hDN
  have hodd : ¬ 2 ∣ X.relIndex D := by
    rw [relIndex_eq_relIndex_inf_of_mul hXD hOD hcover]
    intro h2
    exact (Nat.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr
      (h2.trans (Subgroup.relIndex_dvd_card _ _)))
  obtain ⟨Q, hQ⟩ := exists_isSylowOf 2 X
  have hQD : IsSylowOf 2 Q D := by
    have hQ' := isSylowOf_iff.mp hQ
    refine isSylowOf_iff.mpr ⟨hQ'.1.trans hXD, hQ'.2.1, fun h2 => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex Q X D hQ'.1 hXD] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    exacts [hQ'.2.2 h, hodd h]
  obtain ⟨k, hkD, hk⟩ := exists_conj_le_of_isSylowOf hQD le_sup_left hFp
  exact ⟨k, hkD, (conjugate_le_of_forall hk).trans (hQ.le.trans inf_le_right)⟩

omit [Finite G] in
theorem inv_mul_conj_mem_oddCoreIn {M : Subgroup G} {f m : G} (hf : f ∈ coreActionKernel M)
    (hm : m ∈ M) : f⁻¹ * (m * f * m⁻¹) ∈ oddCoreIn M := by
  have h1 := (mem_coreActionKernel.mp hf).2 m⁻¹ (inv_mem hm)
  have h2 : f⁻¹ * (m * f * m⁻¹) = (m⁻¹⁻¹ * f⁻¹ * m⁻¹ * f)⁻¹ := by group
  rw [h2]
  exact inv_mem h1

theorem exists_card_eight_le_inf_centralizer (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    {M : Subgroup G} (hM : IsFooteM L M) {w : G} (hw : orderOf w = 2)
    (hwMC : w ∈ M ⊔ coreActionKernel M) :
    ∃ F : Subgroup G, F ≤ coreActionKernel M ⊓ centralizer ({w} : Set G) ∧
      (∀ x ∈ F, x ^ 2 = 1) ∧ Nat.card F = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hCdef
  set O := oddCoreIn M with hOdef
  have hOM : O ≤ M := map_subtype_le _
  have hOC : O ≤ C := GSThmB.oddCoreIn_le_coreActionKernel M
  have hCN : C ≤ normalizer (M : Set G) := fun c hc => (mem_coreActionKernel.mp hc).1
  have hMN : M ≤ normalizer (M : Set G) := le_normalizer
  have hNO : ∀ g ∈ normalizer (M : Set G), g ∈ normalizer (O : Set G) := fun g hg =>
    mem_normalizer_oddCoreIn hg
  have hw2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hwN : w ∈ normalizer (M : Set G) := sup_le hMN hCN hwMC
  obtain ⟨m, hm, c, hc, hmc⟩ : ∃ m ∈ M, ∃ c ∈ C, m * c = w := by
    have h1 : w ∈ ((M : Set G) * C) := by
      rw [← coe_mul_of_left_le_normalizer_right M C
        (hMN.trans (normalizer_le_normalizer_coreActionKernel M))]
      exact hwMC
    obtain ⟨m, hm, c, hc, hmc⟩ := Set.mem_mul.mp h1
    exact ⟨m, hm, c, hc, hmc⟩
  subst hmc
  have hc2 : c ^ 2 ∈ O := by
    have ho₁ : m⁻¹ * (c * m * c⁻¹) ∈ O := by
      have h1 := (mem_coreActionKernel.mp (inv_mem hc)).2 m hm
      have h2 : m⁻¹ * (c * m * c⁻¹) = m⁻¹ * c⁻¹⁻¹ * m * c⁻¹ := by group
      rw [h2]
      exact h1
    have h3 : c ^ 2 = (m * m * (m⁻¹ * (c * m * c⁻¹)))⁻¹ * ((m * c) * (m * c)) := by
      rw [sq]
      group
    have h4 : (m * c) * (m * c) = 1 := by rw [← sq]; exact hw2
    rw [h4, mul_one] at h3
    have hcM : c ^ 2 ∈ M := by
      rw [h3]
      exact inv_mem (mul_mem (mul_mem hm hm) (hOM ho₁))
    exact hM.inf_coreActionKernel_le h (mem_inf.mpr ⟨hcM, pow_mem hc 2⟩)
  obtain ⟨r, hr⟩ : ∃ r : ℕ, orderOf (c ^ 2) = 2 * r + 1 := by
    have hdvd : orderOf (c ^ 2) ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O hc2
    have hodd : Odd (orderOf (c ^ 2)) := (odd_card_oddCoreIn M).of_dvd_nat hdvd
    obtain ⟨r, hr⟩ := hodd
    exact ⟨r, hr⟩
  set c' := c ^ (2 * r + 1) with hc'def
  have hc'2 : c' ^ 2 = 1 := by
    rw [hc'def, ← pow_mul, show (2 * r + 1) * 2 = 2 * (2 * r + 1) by ring, pow_mul, ← hr,
      pow_orderOf_eq_one]
  have hc'C : c' ∈ C := pow_mem hc _
  have ho : c'⁻¹ * c ∈ O := by
    have h1 : c'⁻¹ * c = ((c ^ 2) ^ r)⁻¹ := by
      rw [hc'def, ← pow_mul]
      group
    rw [h1]
    exact inv_mem (pow_mem hc2 r)
  obtain ⟨F₀, hF₀C, hF₀c', hF₀2, hF₀8⟩ : ∃ F₀ : Subgroup G, F₀ ≤ C ∧
      (∀ f ∈ F₀, c' * f = f * c') ∧ (∀ x ∈ F₀, x ^ 2 = 1) ∧ Nat.card F₀ = 8 := by
    by_cases hc'1 : c' = 1
    · obtain ⟨E, hE2, hE8, hEC⟩ := hM.exists_card_eight h
      exact ⟨E, hEC, fun f _ => by rw [hc'1, one_mul, mul_one], hE2, hE8⟩
    · have hc'o : orderOf c' = 2 := orderOf_eq_prime hc'2 hc'1
      obtain ⟨F, hF, hF2, hF8⟩ := exists_card_eight_of_le_pRank (h47 G L h M hM c' hc'o hc'C)
      refine ⟨F, hF.trans inf_le_left, fun f hf => ?_, hF2, hF8⟩
      exact (mem_centralizer_singleton_iff.mp (hF hf).2).symm
  have hF₀p : IsPGroup 2 F₀ := IsPGroup.of_card (n := 3) (by rw [hF₀8]; norm_num)
  have hF₀O : F₀ ≤ normalizer (O : Set G) := fun f hf => hNO f (hCN (hF₀C hf))
  have hwF : ∀ f ∈ F₀, f⁻¹ * ((m * c) * f * (m * c)⁻¹) ∈ O := by
    intro f hf
    have hfO := hF₀O hf
    have hy : f⁻¹ * (c * f * c⁻¹) ∈ O := by
      set o := c'⁻¹ * c with hodef
      have hcc : c = c' * o := by rw [hodef]; group
      have h1 : f⁻¹ * o * f ∈ O := by
        have := (mem_normalizer_iff.mp (inv_mem hfO) o).mp ho
        simpa using this
      have hcomm : f⁻¹ * c' = c' * f⁻¹ := by
        have h2 := hF₀c' f hf
        calc f⁻¹ * c' = f⁻¹ * (c' * f) * f⁻¹ := by group
          _ = f⁻¹ * (f * c') * f⁻¹ := by rw [h2]
          _ = c' * f⁻¹ := by group
      have h3 : f⁻¹ * (c * f * c⁻¹) = c' * ((f⁻¹ * o * f) * o⁻¹) * c'⁻¹ := by
        rw [hcc]
        calc f⁻¹ * (c' * o * f * (c' * o)⁻¹) = (f⁻¹ * c') * o * f * o⁻¹ * c'⁻¹ := by group
          _ = (c' * f⁻¹) * o * f * o⁻¹ * c'⁻¹ := by rw [hcomm]
          _ = c' * ((f⁻¹ * o * f) * o⁻¹) * c'⁻¹ := by group
      rw [h3]
      exact (mem_normalizer_iff.mp (hNO c' (hCN hc'C)) _).mp (mul_mem h1 (inv_mem ho))
    have h4 := inv_mul_conj_mem_oddCoreIn (hF₀C hf) hm
    have h5 : m * (f⁻¹ * (c * f * c⁻¹)) * m⁻¹ ∈ O :=
      (mem_normalizer_iff.mp (hNO m (hMN hm)) _).mp hy
    have h6 : f⁻¹ * ((m * c) * f * (m * c)⁻¹) =
        (f⁻¹ * (m * f * m⁻¹)) * (m * (f⁻¹ * (c * f * c⁻¹)) * m⁻¹) := by group
    rw [h6]
    exact mul_mem h4 h5
  obtain ⟨k, hk, hkF⟩ := exists_conj_le_centralizer_of_odd (odd_card_oddCoreIn M) hF₀O hF₀p hw2
    (hNO _ hwN) hwF
  have hkC : k ∈ C := (sup_le hF₀C hOC) hk
  refine ⟨conjugate F₀ k, le_inf (fun x hx => ?_) hkF, sq_eq_one_of_mem_conjugate hF₀2 k,
    by rw [card_conjugate_eq_card, hF₀8]⟩
  rw [mem_conjugate_iff] at hx
  have h1 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
  rw [← h1]
  exact mul_mem (mul_mem (inv_mem hkC) (hF₀C hx)) hkC

end CFSG.ComponentClassification.FooteLit

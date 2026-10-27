module

public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.GH74.Generic.GKFCover
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract

public section

namespace CFSG.AGLEmbedding

open CFSG.RankThree.PerfectCover CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_lift_of_coprime_multiplier_index {S₀ E X : Type} [Group S₀] [Group E] [Group X]
    [Finite S₀] [Finite E] (hS₀ : Group.IsPerfect S₀) (hE : Group.IsPerfect E) (p₀ : S₀ →* X)
    (hp₀ : Function.Surjective p₀) (hk₀ : p₀.ker ≤ Subgroup.center S₀) (p : E →* X)
    (hp : Function.Surjective p) (hk : p.ker ≤ Subgroup.center E) {q : ℕ} (hq : q.Prime)
    (hEq : IsPGroup q p.ker) (m : ℕ) (hm : Nat.Coprime q m)
    (hcard : Nat.card (hopfMultiplier X) = Nat.card p₀.ker * m) :
    ∃ α : S₀ →* E, Function.Surjective α ∧ p.comp α = p₀ := by
  set h₀ := hopfLift p₀ hp₀ hk₀ with hh₀
  set h := hopfLift p hp hk with hh
  have h₀s : Function.Surjective h₀ := hopfLift_surjective p₀ hp₀ hk₀
  have hs : Function.Surjective h := hopfLift_surjective p hp hk
  have hcomp₀ : p₀.comp h₀ = hopfCoverMap X := comp_hopfLift p₀ hp₀ hk₀
  have hcomp : p.comp h = hopfCoverMap X := comp_hopfLift p hp hk
  have hmap₀ : (hopfMultiplier X).map h₀ = p₀.ker := map_hopfMultiplier_hopfLift p₀ hp₀ hk₀
  have hmap : (hopfMultiplier X).map h = p.ker := map_hopfMultiplier_hopfLift p hp hk
  have hker₀ : ∀ u ∈ h₀.ker, u ∈ hopfMultiplier X ∧ u ^ m = 1 := by
    let ψ : hopfMultiplier X →* p₀.ker :=
      (h₀.comp (hopfMultiplier X).subtype).codRestrict p₀.ker fun x => by
        rw [← hmap₀]
        exact ⟨x, x.2, rfl⟩
    have hψs : Function.Surjective ψ := by
      rintro ⟨c, hc⟩
      rw [← hmap₀] at hc
      obtain ⟨x, hx, rfl⟩ := hc
      exact ⟨⟨x, hx⟩, rfl⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hq.one_lt.ne' (Nat.coprime_zero_right q |>.1 hm)
    have hfin : Finite (hopfMultiplier X) := Nat.finite_of_card_ne_zero (by
      rw [hcard]
      exact (Nat.mul_pos Nat.card_pos (Nat.pos_of_ne_zero hm0)).ne')
    have hcardk : Nat.card ψ.ker * Nat.card p₀.ker = Nat.card (hopfMultiplier X) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).toEquiv] at h1
      rw [mul_comm]
      exact h1.symm
    have hkm : Nat.card ψ.ker = m := by
      have h2 : Nat.card ψ.ker * Nat.card p₀.ker = m * Nat.card p₀.ker := by
        rw [hcardk, hcard, mul_comm]
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
    intro u hu
    have hum : u ∈ hopfMultiplier X := by
      change hopfCoverMap X u = 1
      rw [← hcomp₀, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hu, map_one]
    refine ⟨hum, ?_⟩
    have hmem : (⟨u, hum⟩ : hopfMultiplier X) ∈ ψ.ker := Subtype.ext (MonoidHom.mem_ker.1 hu)
    have := orderOf_dvd_natCard (⟨⟨u, hum⟩, hmem⟩ : ψ.ker)
    rw [hkm] at this
    have h3 : (⟨⟨u, hum⟩, hmem⟩ : ψ.ker) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.1 this
    exact congrArg (fun z : ψ.ker => ((z : hopfMultiplier X) : HopfCover X)) h3
  have hle : h₀.ker ≤ h.ker := by
    intro u hu
    obtain ⟨hum, hum'⟩ := hker₀ u hu
    rw [MonoidHom.mem_ker]
    have hhu : h u ∈ p.ker := by
      rw [← hmap]
      exact ⟨u, hum, rfl⟩
    have hpow : (⟨h u, hhu⟩ : p.ker) ^ m = 1 := Subtype.ext (by
      change (h u) ^ m = 1
      rw [← map_pow, hum', map_one])
    obtain ⟨k, hkq⟩ := hEq ⟨h u, hhu⟩
    have hcop : Nat.Coprime (q ^ k) m := Nat.Coprime.pow_left _ hm
    have h1 : (⟨h u, hhu⟩ : p.ker) = 1 := by
      have := (pow_gcd_eq_one (a := (⟨h u, hhu⟩ : p.ker))).2 ⟨hkq, hpow⟩
      rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
    exact congrArg Subtype.val h1
  let α : S₀ →* E := (h₀.liftOfRightInverse (Function.surjInv h₀s)
    (Function.rightInverse_surjInv h₀s)) ⟨h, hle⟩
  have hα : ∀ u, α (h₀ u) = h u := fun u =>
    h₀.liftOfRightInverse_comp_apply (Function.surjInv h₀s) (Function.rightInverse_surjInv h₀s)
      ⟨h, hle⟩ u
  refine ⟨α, fun e => ?_, MonoidHom.ext fun x => ?_⟩
  · obtain ⟨u, rfl⟩ := hs e
    exact ⟨h₀ u, hα u⟩
  · obtain ⟨u, rfl⟩ := h₀s x
    rw [MonoidHom.comp_apply, hα, ← MonoidHom.comp_apply, hcomp, ← MonoidHom.comp_apply, hcomp₀]

section Quasisimple

variable {Y : Type} [Group Y]

theorem center_centerQuotient_eq_bot (hY : CFSG.Open.IsQuasisimple Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  have := hY.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (Y ⧸ Subgroup.center Y)) with h | h
  · exact h
  · exfalso
    have hle : commutator Y ≤ Subgroup.center Y := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff]
      have hab := Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top (QuotientGroup.mk a :
        Y ⧸ Subgroup.center Y)) (QuotientGroup.mk b)
      rw [commutatorElement_def, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, ← hab]
      group
    rw [hY.1] at hle
    have htop : Subgroup.center Y = ⊤ := top_le_iff.1 hle
    have : Subsingleton (Y ⧸ Subgroup.center Y) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (Y ⧸ Subgroup.center Y) this

theorem le_center_or_eq_top_of_normal_quasisimple (hY : CFSG.Open.IsQuasisimple Y) (N : Subgroup Y)
    [N.Normal] : N ≤ Subgroup.center Y ∨ N = ⊤ := by
  have := hY.2
  have hmk := QuotientGroup.mk'_surjective (Subgroup.center Y)
  have : (N.map (QuotientGroup.mk' (Subgroup.center Y))).Normal :=
    Subgroup.Normal.map inferInstance _ hmk
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Y))) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hdec : ∀ y : Y, ∃ n ∈ N, ∃ z ∈ Subgroup.center Y, y = n * z := by
      intro y
      obtain ⟨n, hn, hny⟩ := (h ▸ Subgroup.mem_top (QuotientGroup.mk' (Subgroup.center Y) y) :
        QuotientGroup.mk' _ y ∈ N.map (QuotientGroup.mk' (Subgroup.center Y)))
      refine ⟨n, hn, n⁻¹ * y, ?_, by group⟩
      rw [← QuotientGroup.eq]
      exact hny
    rw [eq_top_iff, ← hY.1, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdec a
    obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdec b
    rw [CFSG.AGLEmbedding.ParabPrime.commutatorElement_mul_central hz₁ hz₂, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hn₁ hn₂) (inv_mem hn₁)) (inv_mem hn₂)

end Quasisimple

section ThreeCover

variable {Y : Type} [Group Y]

@[expose] noncomputable def quotCenterOfLeCenter {O : Subgroup Y} [O.Normal]
    (hO : O ≤ Subgroup.center Y) : Y ⧸ O →* Y ⧸ Subgroup.center Y :=
  QuotientGroup.map O (Subgroup.center Y) (MonoidHom.id Y) hO

variable {O : Subgroup Y} [O.Normal] (hO : O ≤ Subgroup.center Y)

theorem quotCenterOfLeCenter_mk (y : Y) :
    quotCenterOfLeCenter hO (QuotientGroup.mk y) = QuotientGroup.mk y :=
  rfl

theorem quotCenterOfLeCenter_surjective : Function.Surjective (quotCenterOfLeCenter hO) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk y, rfl⟩

theorem quotCenterOfLeCenter_comp :
    (quotCenterOfLeCenter hO).comp (QuotientGroup.mk' O) = QuotientGroup.mk' (Subgroup.center Y) :=
  MonoidHom.ext fun _ => rfl

theorem mk_mem_ker_quotCenterOfLeCenter (y : Y) :
    (QuotientGroup.mk y : Y ⧸ O) ∈ (quotCenterOfLeCenter hO).ker ↔ y ∈ Subgroup.center Y := by
  rw [MonoidHom.mem_ker, quotCenterOfLeCenter_mk, QuotientGroup.eq_one_iff]

theorem ker_quotCenterOfLeCenter_le_center :
    (quotCenterOfLeCenter hO).ker ≤ Subgroup.center (Y ⧸ O) := by
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rw [mk_mem_ker_quotCenterOfLeCenter] at hx
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx w]

theorem isPGroup_ker_quotCenterOfLeCenter [Finite Y]
    (hO : primeComplementCore (G := Y) 3 ≤ Subgroup.center Y) :
    IsPGroup 3 (quotCenterOfLeCenter hO).ker := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy := (mk_mem_ker_quotCenterOfLeCenter hO y).1 hx
  set a := (orderOf y).factorization 3 with ha
  set y' := y ^ 3 ^ a with hy'
  have hy'c : y' ∈ Subgroup.center Y := Subgroup.pow_mem _ hy _
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers y')) := by
    rw [Nat.card_zpowers, hy', orderOf_pow' y (pow_ne_zero a (by norm_num)),
      Nat.gcd_eq_right (Nat.ordProj_dvd _ _)]
    exact Nat.coprime_ordCompl Nat.prime_three (orderOf_pos y).ne'
  have hnorm : (Subgroup.zpowers y').Normal := by
    refine ⟨fun z hz g => ?_⟩
    have hzc : z ∈ Subgroup.center Y := (Subgroup.zpowers_le.2 hy'c) hz
    rw [Subgroup.mem_center_iff.1 hzc g, mul_inv_cancel_right]
    exact hz
  have hle := normal_coprime_le_primeComplementCore 3 _ hnorm hcop
  refine ⟨a, Subtype.ext ?_⟩
  change (QuotientGroup.mk y : Y ⧸ primeComplementCore (G := Y) 3) ^ 3 ^ a = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hle (Subgroup.mem_zpowers y')

end ThreeCover

section Multiplier

open CFSG.Blueprint.Multiplier CFSG.Assembly.LowTwoRank

theorem card_hopfMultiplier_of_statedClassicalModel (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] {t : StatedLieTag} {n p f : ℕ} (hc : StatedClassicalModel X t n p f) :
    Nat.card (hopfMultiplier X) = (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨g⟩⟩ := hGA X t n p f ⟨hc.1, Or.inl hc⟩
  rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr g.toEquiv]
  simp only [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem coprime_three_card_hopfMultiplier_of_model_two (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] {t : StatedLieTag} {n : ℕ} (hc : StatedClassicalModel X t n 2 1)
    (ht : t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus) :
    Nat.Coprime 3 (Nat.card (hopfMultiplier X)) := by
  rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
  have hg : (genericOrders t n 2 1).1 * (genericOrders t n 2 1).2 ∣ 4 := by
    rcases ht with rfl | rfl | rfl | rfl <;> simp [genericOrders, Nat.gcd_dvd_left]
  have he : (exceptionalOrders t n 2 1).1 * (exceptionalOrders t n 2 1).2 ∣ 16 := by
    unfold exceptionalOrders
    split <;> first | omega | norm_num
  exact Nat.Coprime.coprime_dvd_right (Nat.mul_dvd_mul hg he) (by norm_num)

theorem card_hopfMultiplier_of_model_psu_two (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] {n : ℕ} (hc : StatedClassicalModel X .PSU n 2 1) :
    ∃ e : ℕ, e ∣ 16 ∧ Nat.card (hopfMultiplier X) = Nat.gcd n 3 * e := by
  refine ⟨(exceptionalOrders .PSU n 2 1).1 * (exceptionalOrders .PSU n 2 1).2, ?_, ?_⟩
  · unfold exceptionalOrders
    split <;> first | omega | norm_num
  · rw [card_hopfMultiplier_of_statedClassicalModel hGA hc]
    simp [genericOrders]

theorem ker_eq_bot_of_coprime_hopfMultiplier {E X : Type} [Group E] [Group X] [Finite E]
    (hE : Group.IsPerfect E) (p : E →* X) (hp : Function.Surjective p)
    (hk : p.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 p.ker)
    (hM : Nat.Coprime 3 (Nat.card (hopfMultiplier X))) : p.ker = ⊥ := by
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hE p hp hk
  obtain ⟨k, hk3⟩ := h3.exists_card_eq
  apply Subgroup.eq_bot_of_card_eq
  rw [hk3] at hdvd ⊢
  rcases k with _ | k
  · rfl
  · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero k)).trans hdvd)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hM)

end Multiplier

end CFSG.AGLEmbedding

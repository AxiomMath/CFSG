module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TwelveRanksLe

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.SectionRank.ClassicalEven

theorem exists_isElemAbelian_card_sq_of_gens {P : Type*} [Group P] [Finite P] {p : ℕ}
    [hp : Fact p.Prime] {x y : P} (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : Commute x y)
    (hx1 : x ≠ 1) (hy1 : ∀ n : ℕ, x ^ n ≠ y) :
    ∃ E : Subgroup P, IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ g ∈ E, ∃ n m : ℕ, g = x ^ n * y ^ m := by
  set B₀ : Subgroup P := ⊥
  have h₀ : ∀ b : B₀, B₀.subtype b = 1 := fun b => Subgroup.mem_bot.1 b.2
  have hc₀ : ∀ a b : B₀, a * b = b * a := fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])
  have hp₀ : ∀ a : B₀, a ^ p = 1 := fun a => Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [Subgroup.mem_bot.1 a.2, one_pow])
  have hcard₀ : Nat.card B₀ = p ^ 0 := by rw [pow_zero]; exact Subgroup.card_bot
  obtain ⟨F₁, hF₁, hc₁, hp₁, hcard₁, hr₁⟩ := CFSG.SectionRank.exists_extend hc₀ hp₀ hcard₀
    B₀.subtype Subtype.val_injective (y := x) hx (by
      rintro ⟨b, hb⟩
      exact hx1 (hb ▸ h₀ b))
    (fun b => by rw [h₀ b]; exact Commute.one_left x)
  have hr₁' : ∀ a, ∃ n : ℕ, F₁ a = x ^ n := fun a => by
    obtain ⟨b, n, hb⟩ := hr₁ a
    exact ⟨n, by rw [hb, h₀ b, one_mul]⟩
  obtain ⟨F₂, hF₂, hc₂, hp₂, hcard₂, hr₂⟩ := CFSG.SectionRank.exists_extend hc₁ hp₁ hcard₁ F₁
    hF₁ (y := y) hy
    (by
      rintro ⟨a, ha⟩
      obtain ⟨n, hn⟩ := hr₁' a
      exact hy1 n (hn ▸ ha))
    (fun a => by
      obtain ⟨n, hn⟩ := hr₁' a
      rw [hn]
      exact hxy.pow_left n)
  have hr₂' : ∀ a, ∃ n m : ℕ, F₂ a = x ^ n * y ^ m := fun a => by
    obtain ⟨b, m, hb⟩ := hr₂ a
    obtain ⟨n, hn⟩ := hr₁' b
    exact ⟨n, m, by rw [hb, hn]⟩
  refine ⟨F₂.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩, ?_, fun g hg => ?_⟩
  · obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : P) * b = b * a
    rw [← hu, ← hv, ← map_mul, ← map_mul, hc₂ u v]
  · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hg
    rw [← map_pow, hp₂ u, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hF₂).toEquiv, hcard₂]
  · obtain ⟨u, rfl⟩ := MonoidHom.mem_range.1 hg
    exact hr₂' u

theorem exists_isElemAbelian_card_nine_statedSU {K : Type} [Field K] [Finite K] {f n : ℕ}
    (hK : Nat.card K = (2 ^ f) ^ 2) (h3 : 3 ∣ 2 ^ f + 1) (hn : 4 ≤ n) :
    ∃ E : Subgroup (StatedSU n (2 ^ f) K), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      ∀ g ∈ E, (g : GL (Fin n) K) ∈ StatedScalars (Fin n) K → g = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq : 2 ^ f ≠ 0 := by positivity
  have hcard : Nat.card Kˣ = (2 ^ f + 1) * (2 ^ f - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  have h3K : 3 ∣ Nat.card Kˣ := by
    rw [hcard]
    exact h3.mul_right _
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 h3K
  have hζq : ζ ^ (2 ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact h3)
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hζ
    norm_num at hζ
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin n := ⟨2, by omega⟩ with hi₂
  set i₃ : Fin n := ⟨3, by omega⟩ with hi₃
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁]
  have h02 : i₀ ≠ i₂ := by simp [hi₀, hi₂]
  have h03 : i₀ ≠ i₃ := by simp [hi₀, hi₃]
  have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂]
  have h13 : i₁ ≠ i₃ := by simp [hi₁, hi₃]
  have h23 : i₂ ≠ i₃ := by simp [hi₂, hi₃]
  have hmem : ∀ j : Fin n, torusDiag (torusVec ζ j i₃) ∈ StatedSU n (2 ^ f) K := fun j =>
    torusDiag_mem_SU hq (prod_torusVec ζ j _) (by rw [torusVec_pow, hζq, torusVec_one])
  have hent {d d' : Fin n → Kˣ} (h : torusDiag d = (torusDiag d' : GL (Fin n) K)) (i : Fin n) :
      d i = d' i := congrFun (torusDiag_injective h) i
  have hζ3 : ζ ^ 3 = 1 := by
    have := pow_orderOf_eq_one ζ
    rwa [hζ] at this
  obtain ⟨x, hxe⟩ : ∃ x : StatedSU n (2 ^ f) K,
      (x : GL (Fin n) K) = torusDiag (torusVec ζ i₀ i₃) := ⟨⟨_, hmem i₀⟩, rfl⟩
  obtain ⟨y, hye⟩ : ∃ y : StatedSU n (2 ^ f) K,
      (y : GL (Fin n) K) = torusDiag (torusVec ζ i₁ i₃) := ⟨⟨_, hmem i₁⟩, rfl⟩
  have hxp : ∀ m : ℕ, ((x ^ m : StatedSU n (2 ^ f) K) : GL (Fin n) K) =
      torusDiag (torusVec (ζ ^ m) i₀ i₃) := fun m => by
    rw [SubgroupClass.coe_pow, hxe, ← map_pow, torusVec_pow]
  have hyp : ∀ m : ℕ, ((y ^ m : StatedSU n (2 ^ f) K) : GL (Fin n) K) =
      torusDiag (torusVec (ζ ^ m) i₁ i₃) := fun m => by
    rw [SubgroupClass.coe_pow, hye, ← map_pow, torusVec_pow]
  have hx3 : x ^ 3 = 1 :=
    Subtype.ext (by rw [hxp, hζ3, torusVec_one, map_one, OneMemClass.coe_one])
  have hy3 : y ^ 3 = 1 :=
    Subtype.ext (by rw [hyp, hζ3, torusVec_one, map_one, OneMemClass.coe_one])
  have hxy : Commute x y := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hxe, hye]
    exact ((Commute.all (torusVec ζ i₀ i₃) (torusVec ζ i₁ i₃)).map torusDiag).eq)
  have hx1 : x ≠ 1 := by
    intro h
    have h' := congrArg (fun g : StatedSU n (2 ^ f) K => (g : GL (Fin n) K)) h
    simp only [hxe, OneMemClass.coe_one] at h'
    have := hent (d' := 1) (h'.trans (map_one torusDiag).symm) i₀
    rw [torusVec_apply_left ζ h03, Pi.one_apply] at this
    exact hζ1 this
  have hy1 : ∀ m : ℕ, x ^ m ≠ y := by
    intro m h
    have h' := congrArg (fun g : StatedSU n (2 ^ f) K => (g : GL (Fin n) K)) h
    simp only [hxp, hye] at h'
    have := hent h' i₁
    rw [torusVec_apply_of_ne _ h01.symm h13, torusVec_apply_left _ h13] at this
    exact hζ1 this.symm
  obtain ⟨E, hE, hEcard, hEgen⟩ := exists_isElemAbelian_card_sq_of_gens hx3 hy3 hxy hx1 hy1
  refine ⟨E, hE, hEcard, fun g hg hgs => ?_⟩
  obtain ⟨a, b, rfl⟩ := hEgen g hg
  obtain ⟨c, hc⟩ := hgs
  rw [Subgroup.coe_mul, hxp, hyp, ← map_mul, scalar_eq_torusDiag] at hc
  have e0 := hent hc i₀
  have e1 := hent hc i₁
  have e2 := hent hc i₂
  simp only [Pi.mul_apply, torusVec_apply_left _ h03, torusVec_apply_of_ne _ h01 h03,
    torusVec_apply_of_ne _ h01.symm h13, torusVec_apply_left _ h13,
    torusVec_apply_of_ne _ h02.symm h23, torusVec_apply_of_ne _ h12.symm h23, mul_one,
    one_mul] at e0 e1 e2
  have hζa : ζ ^ a = 1 := e0.symm.trans e2
  have hζb : ζ ^ b = 1 := e1.symm.trans e2
  have hxa : x ^ a = 1 :=
    Subtype.ext (by rw [hxp, hζa, torusVec_one, map_one, OneMemClass.coe_one])
  have hyb : y ^ b = 1 :=
    Subtype.ext (by rw [hyp, hζb, torusVec_one, map_one, OneMemClass.coe_one])
  rw [hxa, hyb, mul_one]

end TwelveRanksLe

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.EmbedLam

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

@[expose] def LamLike2 (b : ℕ) (X : Type*) [Group X] : Prop :=
  Group.IsSolvable X ∧ ∀ P : Subgroup X, IsPGroup 2 P → (∀ x ∈ P, x * x = 1) ∧ Nat.card P ≤ b

theorem LamLike2.of_injective {b : ℕ} {X Y : Type*} [Group X] [Group Y] (h : LamLike2 b Y)
    {f : X →* Y} (hf : Function.Injective f) : LamLike2 b X := by
  obtain ⟨hs, hP⟩ := h
  refine ⟨Group.isSolvable_of_isSolvable_injective hf, fun P hP2 => ?_⟩
  obtain ⟨h1, h2⟩ := hP (P.map f) (hP2.map f)
  refine ⟨fun x hx => hf ?_, ?_⟩
  · have := h1 (f x) ⟨x, hx, rfl⟩
    rwa [← map_mul, ← map_one f] at this
  · rw [← Subgroup.card_map_of_injective hf]
    exact h2

@[expose] def InvolutionFixesNotLam2 (K : Type) [Group K] (b : ℕ) : Prop :=
  ∀ α : MulAut K, α ≠ 1 → α * α = 1 →
    ¬ LamLike2 b (↥(fixSubgroup α) × Multiplicative (ZMod 2)) ∧
      ((∃ k : K, α = MulAut.conj k) → ¬ LamLike2 b ↥(fixSubgroup α))

theorem NoFixedEmbeds.of_lamLike2 {K : Type} [Group K] {b : ℕ} {Λ : Type*} [Group Λ]
    (hK : InvolutionFixesNotLam2 K b) (hΛ : LamLike2 b Λ) : NoFixedEmbeds K Λ :=
  fun α h1 h2 =>
    ⟨fun ⟨_, hf⟩ => (hK α h1 h2).1 (hΛ.of_injective hf),
      fun hin ⟨_, hf⟩ => (hK α h1 h2).2 hin (hΛ.of_injective hf)⟩

section Lam

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G}

omit [Finite G] in
theorem sq_eq_one_of_isTwoElt (h2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    {c : G} (hc : c ∈ centralizer (L : Set G)) {k : ℕ} (hck : c ^ 2 ^ k = 1) : c * c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let c' : ↥(centralizer (L : Set G)) := ⟨c, hc⟩
  have hord : orderOf c' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hck))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hpg : IsPGroup 2 (Subgroup.zpowers c') := IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨S, hS⟩ := hpg.exists_le_sylow
  have hmem : c' ∈ (S : Subgroup ↥(centralizer (L : Set G))) := hS (Subgroup.mem_zpowers c')
  have hdvd : orderOf c' ∣ 2 := by
    have := Subgroup.orderOf_dvd_natCard (S : Subgroup ↥(centralizer (L : Set G))) hmem
    rwa [h2 S] at this
  have h2c : c' ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 hdvd
  have := congrArg Subtype.val h2c
  simpa [pow_two] using this

theorem lam_exp_two (h2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hA2 : ∀ A : Subgroup (autCentralizer L K), IsPGroup 2 A → ∀ x ∈ A, x * x = 1)
    (hin : ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) (hKL : K ≤ L)
    (hZ : Odd (Nat.card (center ↥L))) {P : Subgroup ↥(lam L K)} (hP2 : IsPGroup 2 P) :
    ∀ x ∈ P, x * x = 1 := by
  intro x hx
  let ψ : ↥P →* autCentralizer L K := (lamAction L K).comp P.subtype
  have hRp : IsPGroup 2 ψ.range := hP2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hψ : lamAction L K (x * x) = 1 := by
    have := hA2 ψ.range hRp (ψ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
    rw [← map_mul] at this
    exact this
  have hxx : ((x * x : ↥(lam L K)) : G) ∈ centralizer (L : Set G) :=
    mem_centralizer_of_lamAction_eq_one hψ
  obtain ⟨k, hk⟩ := hP2 ⟨x, hx⟩
  have hxk : (x : G) ^ 2 ^ k = 1 := by
    have := congrArg (fun z : ↥P => (((z : ↥(lam L K)) : G))) hk
    simpa using this
  have hyk : ((x : G) * x) ^ 2 ^ k = 1 := by
    rw [(Commute.refl (x : G)).mul_pow, hxk, one_mul]
  have hy2 : ((x : G) * x) * ((x : G) * x) = 1 := sq_eq_one_of_isTwoElt h2 hxx hyk
  obtain ⟨g, hg, c, hc, hgc⟩ := lam_factor hin hKL x.2
  have hcomm : (g : G) * c = c * g := mem_centralizer_iff.1 hc g hg.1
  have hy : (x : G) * x = (g * g) * (c * c) := by
    rw [hgc]
    calc g * c * (g * c) = g * (c * g) * c := by group
      _ = g * (g * c) * c := by rw [hcomm]
      _ = (g * g) * (c * c) := by group
  have hcc : c * c ∈ centralizer (L : Set G) := mul_mem hc hc
  have hg2C : (g : G) * g ∈ centralizer (L : Set G) := by
    have : (g : G) * g = ((x : G) * x) * (c * c)⁻¹ := by
      rw [hy]
      group
    rw [this]
    exact mul_mem hxx (inv_mem hcc)
  have hodd : Odd (orderOf ((g : G) * g)) :=
    odd_orderOf_of_mem_center hZ (mul_mem hg.1 hg.1) fun l hl => (mem_centralizer_iff.1 hg2C l hl)
  set r := orderOf ((g : G) * g) with hr
  have hgr : ((g : G) * g) ^ r = 1 := pow_orderOf_eq_one _
  have h1 : Commute (g : G) c := hcomm
  have hcg : Commute ((g : G) * g) (c * c) := (h1.mul_left h1).mul_right (h1.mul_left h1)
  have hy_r : ((x : G) * x) ^ r = (x : G) * x := by
    obtain ⟨j, hj⟩ := hodd
    rw [hj, pow_succ, pow_mul, sq, hy2, one_pow, one_mul]
  have hy_c : (x : G) * x = c ^ r * c ^ r := by
    calc (x : G) * x = ((x : G) * x) ^ r := hy_r.symm
      _ = ((g * g) * (c * c)) ^ r := by rw [hy]
      _ = (g * g) ^ r * (c * c) ^ r := hcg.mul_pow r
      _ = (c * c) ^ r := by rw [hgr, one_mul]
      _ = c ^ r * c ^ r := (Commute.refl c).mul_pow r
  have hc0 : c ^ r ∈ centralizer (L : Set G) := pow_mem hc r
  have h4 : (c ^ r) ^ 2 ^ 2 = 1 := by
    calc (c ^ r) ^ 2 ^ 2 = (c ^ r * c ^ r) * (c ^ r * c ^ r) := by
          rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
          group
      _ = ((x : G) * x) * ((x : G) * x) := by rw [hy_c]
      _ = 1 := hy2
  have hc02 : c ^ r * c ^ r = 1 := sq_eq_one_of_isTwoElt h2 hc0 h4
  exact Subtype.ext (hy_c.trans hc02)

theorem lam_isLamLike2 {e : ℕ} (h2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hAs : Group.IsSolvable (autCentralizer L K))
    (hA2 : ∀ A : Subgroup (autCentralizer L K), IsPGroup 2 A →
      (∀ x ∈ A, x * x = 1) ∧ Nat.card A ≤ e)
    (hin : ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g) (hKL : K ≤ L)
    (hZ : Odd (Nat.card (center ↥L))) : LamLike2 (2 * e) ↥(lam L K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : ∀ S : Sylow 2 (centralizer (L : Set G)), IsCyclic S := fun S =>
    isCyclic_of_prime_card (h2 S)
  refine ⟨lam_isSolvable hcyc hAs, fun P hP2 => ?_⟩
  have hexp : ∀ x ∈ P, x * x = 1 := lam_exp_two h2 (fun A hA => (hA2 A hA).1) hin hKL hZ hP2
  refine ⟨hexp, ?_⟩
  have he : ElemBound e (autCentralizer L K) := fun E hE _ =>
    (hA2 E (fun x => ⟨1, Subtype.ext (by simpa [pow_two] using hE x x.2)⟩)).2
  refine elemBound_lam_of_elem hcyc he P hexp fun x hx y hy => ?_
  have hxy : x * y * (x * y) = 1 := hexp _ (P.mul_mem hx hy)
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hexp x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hexp y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx', hy']

end Lam

end CFSG.EvenSporadicStandard.Induction

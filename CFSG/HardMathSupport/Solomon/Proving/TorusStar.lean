module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LpEpsTorus
public import CFSG.HardMathSupport.Solomon.Proving.TorusLift

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open Matrix CFSG.HardMathSupport.Timmesfeld.LocalTwo.Torus

@[expose] def starX {K : Type*} [Field K] {n r : ℕ} (ζ : Kˣ) (c : Fin n) (d : Fin r → Fin n)
    (k : Fin r) : GL (Fin n) K :=
  diagHom (tvec ζ c (d k))

@[expose] def starSw {K : Type*} [Field K] {n r : ℕ} (c : Fin n) (d : Fin r → Fin n) (k : Fin r) :
    GL (Fin n) K :=
  sgnSwap c (d k)

section Facts

variable {K : Type*} [Field K] {n r : ℕ} (ζ : Kˣ) (c : Fin n) (d : Fin r → Fin n)

theorem starX_comm (i j : Fin r) :
    Commute (starX ζ c d i : GL (Fin n) K) (starX ζ c d j) :=
  (Commute.all _ _).map diagHom

theorem starX_pow {p : ℕ} (hζ : ζ ^ p = 1) (k : Fin r) :
    (starX ζ c d k : GL (Fin n) K) ^ p = 1 := by
  rw [starX, ← map_pow, tvec_pow hζ, map_one]

theorem starSw_self (hcd : ∀ k, c ≠ d k) (k : Fin r) :
    (starSw c d k : GL (Fin n) K) * starX ζ c d k * (starSw c d k)⁻¹ = (starX ζ c d k)⁻¹ := by
  rw [starSw, starX, sgnSwap_conj_diag, tvec_comp_swap_self ζ (hcd k), map_inv]

theorem starSw_other (hd : Function.Injective d) (hcd : ∀ k, c ≠ d k) {j k : Fin r} (hjk : j ≠ k) :
    (starSw c d k : GL (Fin n) K) * starX ζ c d j * (starSw c d k)⁻¹ =
      (starX ζ c d k)⁻¹ * starX ζ c d j := by
  rw [starSw, starX, starX, sgnSwap_conj_diag,
    tvec_comp_swap_other ζ (hcd k) (hcd j) (hd.ne hjk.symm), map_mul, map_inv]

theorem closure_starX_diag {z : Fin n} (hzc : z ≠ c) (hzd : ∀ k, z ≠ d k) {g : GL (Fin n) K}
    (hg : g ∈ Subgroup.closure (Set.range (starX ζ c d))) :
    ∃ v : Fin n → Kˣ, g = diagHom v ∧ v z = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨_, rfl, tvec_apply_of_ne ζ hzc (hzd k)⟩
  | one => exact ⟨1, (map_one _).symm, rfl⟩
  | mul x y _ _ hx hy =>
    obtain ⟨v, rfl, hv⟩ := hx
    obtain ⟨w, rfl, hw⟩ := hy
    exact ⟨v * w, (map_mul _ _ _).symm, by simp [hv, hw]⟩
  | inv x _ hx =>
    obtain ⟨v, rfl, hv⟩ := hx
    exact ⟨v⁻¹, (map_inv _ _).symm, by simp [hv]⟩

theorem card_closure_starX [Finite K] {p : ℕ} [Fact p.Prime] (hζ : IsPrimitiveRoot ζ p)
    (hd : Function.Injective d) (hcd : ∀ k, c ≠ d k) :
    Nat.card (Subgroup.closure (Set.range (starX ζ c d)) : Subgroup (GL (Fin n) K)) = p ^ r := by
  classical
  set V : Fin r → (Fin n → Kˣ) := fun k => tvec ζ c (d k) with hV
  set U : Subgroup (Fin n → Kˣ) := Subgroup.closure (Set.range V) with hU
  have hmap : U.map (diagHom : (Fin n → Kˣ) →* GL (Fin n) K) =
      Subgroup.closure (Set.range (starX ζ c d)) := by
    rw [hU, MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hcard : Nat.card U = Nat.card (Subgroup.closure (Set.range (starX ζ c d)) :
      Subgroup (GL (Fin n) K)) := by
    rw [← hmap, Subgroup.card_map_of_injective diagHom_injective]
  rw [← hcard]
  have hVp : ∀ k, V k ^ p = 1 := fun k => tvec_pow hζ.pow_eq_one c (d k)
  have hev : ∀ (m : Fin r → ℕ) (k : Fin r), (∏ k', V k' ^ m k') (d k) = ζ⁻¹ ^ m k := by
    intro m k
    rw [Finset.prod_apply, Finset.prod_eq_single k]
    · simp [hV, Pi.pow_apply, tvec_apply_j]
    · intro k' _ hk'
      simp [hV, Pi.pow_apply, tvec_apply_of_ne ζ (hcd k).symm (hd.ne hk'.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  let Φ : (Fin r → ZMod p) → U := fun a =>
    ⟨∏ k, V k ^ (a k).val, Subgroup.prod_mem U fun k _ =>
      pow_mem (Subgroup.subset_closure (Set.mem_range_self k)) _⟩
  have hinj : Function.Injective Φ := by
    intro a b hab
    funext k
    have h1 := congrArg (fun u : U => (u : Fin n → Kˣ) (d k)) hab
    simp only [Φ] at h1
    rw [hev (fun k => (a k).val) k, hev (fun k => (b k).val) k] at h1
    have hζ' : IsPrimitiveRoot ζ⁻¹ p := hζ.inv
    have := hζ'.pow_inj (ZMod.val_lt (a k)) (ZMod.val_lt (b k)) h1
    exact ZMod.val_injective p this
  have haux : ∀ u ∈ U, ∃ a : Fin r → ZMod p, u = ∏ k, V k ^ (a k).val := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨Pi.single k 1, ?_⟩
      rw [Finset.prod_eq_single k]
      · simp [ZMod.val_one]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    | one => exact ⟨0, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hVp k), pow_add]
    | inv x _ hx =>
      obtain ⟨a, rfl⟩ := hx
      refine ⟨-a, ?_⟩
      rw [← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have h0 : V k ^ ((-a k).val + (a k).val) = 1 := by
        have hm : ((-a k).val + (a k).val) % p = 0 := by
          rw [← ZMod.val_add]
          exact (congrArg ZMod.val (neg_add_cancel (a k))).trans ZMod.val_zero
        rw [pow_eq_pow_mod _ (hVp k), hm, pow_zero]
      have h0' : V k ^ (a k).val * V k ^ (-a k).val = 1 := by
        rw [← pow_add, add_comm, h0]
      rw [Pi.neg_apply]
      exact inv_eq_of_mul_eq_one_right h0'
  have hsurj : Function.Surjective Φ := by
    rintro ⟨u, hu⟩
    obtain ⟨a, rfl⟩ := haux u hu
    exact ⟨a, rfl⟩
  rw [← Nat.card_eq_of_bijective Φ ⟨hinj, hsurj⟩]
  simp [Nat.card_eq_fintype_card]

end Facts

open Subgroup in
theorem exists_torusData_star {p n r : ℕ} [Fact p.Prime] {K : Type*} [Field K] [Finite K]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {M S : Type*} [Group M] [Group S]
    (ι : M →* GL (Fin n) K) (hι : Function.Injective ι) (π : M →* S)
    (hπ : ∀ g : M, π g = 1 → ∃ c : Kˣ, ι g = Matrix.GeneralLinearGroup.scalar (Fin n) c)
    (c z : Fin n) (d : Fin r → Fin n) (hd : Function.Injective d) (hcd : ∀ k, c ≠ d k)
    (hzc : z ≠ c) (hzd : ∀ k, z ≠ d k)
    (memX : ∀ k, starX ζ c d k ∈ ι.range) (memS : ∀ k, starSw c d k ∈ ι.range) :
    ∃ D : TorusData (Fin r) p S, Nat.card (Subgroup.closure (Set.range D.X)) = p ^ r ∧
      (∀ k, ∃ x : M, ι x = starX ζ c d k ∧ D.X k = π x) ∧
      (∀ k, ∃ s : M, ι s = starSw c d k ∧ D.Sw k = π s) := by
  classical
  choose x hx using fun k => MonoidHom.mem_range.1 (memX k)
  choose s hs using fun k => MonoidHom.mem_range.1 (memS k)
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hcomm : ∀ i j, Commute (x i) (x j) := fun i j => hι (by
    rw [map_mul, map_mul, hx, hx]; exact starX_comm ζ c d i j)
  have hpow : ∀ i, x i ^ p = 1 := fun i => hι (by
    rw [map_pow, hx, map_one]; exact starX_pow ζ c d hζp i)
  have hself : ∀ k, s k * x k * (s k)⁻¹ = (x k)⁻¹ := fun k => hι (by
    rw [map_mul, map_mul, map_inv, map_inv, hs, hx]; exact starSw_self ζ c d hcd k)
  have hother : ∀ j k, j ≠ k → s k * x j * (s k)⁻¹ = (x k)⁻¹ * x j := fun j k hjk => hι (by
    rw [map_mul, map_mul, map_inv, map_mul, map_inv, hs, hx, hx]
    exact starSw_other ζ c d hd hcd hjk)
  let D : TorusData (Fin r) p S :=
    { X := fun k => π (x k)
      Sw := fun k => π (s k)
      comm := fun i j => (hcomm i j).map π
      pow := fun i => by rw [← map_pow, hpow, map_one]
      sw_self := fun k => by rw [← map_mul, ← map_inv, ← map_mul, hself, map_inv]
      sw_other := fun j k hjk => by
        rw [← map_mul, ← map_inv, ← map_mul, hother j k hjk, map_mul, map_inv] }
  refine ⟨D, ?_, fun k => ⟨x k, hx k, rfl⟩, fun k => ⟨s k, hs k, rfl⟩⟩
  show Nat.card (closure (Set.range fun k => π (x k))) = p ^ r
  have hmapx : (closure (Set.range x)).map ι = closure (Set.range (starX ζ c d)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    have : (ι ∘ x) = starX ζ c d := funext hx
    rw [this]
  have hinj : ∀ g ∈ closure (Set.range x), π g = 1 → g = 1 := by
    intro g hg hπg
    obtain ⟨c', hc⟩ := hπ g hπg
    have hg' : ι g ∈ closure (Set.range (starX ζ c d)) := by
      rw [← hmapx]; exact Subgroup.mem_map_of_mem _ hg
    obtain ⟨v, hv, hvz⟩ := closure_starX_diag ζ c d hzc hzd hg'
    apply hι
    rw [map_one]
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) z z)
      (hc.symm.trans hv)
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, diagHom_apply,
      coe_diagGL, Matrix.diagonal_apply_eq] at h1
    have hc1 : c' = 1 := Units.ext (by rw [h1, hvz])
    rw [hc, hc1, map_one]
  have hcard1 : Nat.card (closure (Set.range x)) =
      Nat.card (closure (Set.range (starX ζ c d)) : Subgroup (GL (Fin n) K)) := by
    rw [← hmapx, Subgroup.card_map_of_injective hι]
  have hinj' : Function.Injective (π.domRestrict (closure (Set.range x))) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hinj g g.2 hg)
  have hmapπ : (closure (Set.range x)).map π = closure (Set.range fun k => π (x k)) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hcard2 : Nat.card (closure (Set.range fun k => π (x k))) =
      Nat.card (closure (Set.range x)) := by
    rw [← hmapπ, ← MonoidHom.domRestrict_range]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  rw [hcard2, hcard1]
  exact card_closure_starX ζ c d hζ hd hcd

end CFSG.HardMathSupport.Solomon.Proving

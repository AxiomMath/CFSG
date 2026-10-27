module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Dickson

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup Module

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]
variable {J : Type} [Group J]

theorem one_add_pow_sq_zero {R : Type*} [Ring R] (N : R) (hN : N * N = 0) (m : ℕ) :
    (1 + N) ^ m = 1 + (m : R) * N := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih]
    have h1 : N * ((m : R) * N) = 0 := by
      rw [← mul_assoc, (Nat.cast_commute m N).symm.eq, mul_assoc, hN, mul_zero]
    calc (1 + N) * (1 + (m : R) * N)
        = 1 + (m : R) * N + N + N * ((m : R) * N) := by noncomm_ring
      _ = 1 + ((m + 1 : ℕ) : R) * N := by rw [h1]; push_cast; noncomm_ring

def subRep (ρ : J →* Module.End (ZMod p) W) (S : Submodule (ZMod p) W)
    (hS : ∀ j, ∀ w ∈ S, ρ j w ∈ S) : J →* Module.End (ZMod p) S where
  toFun j := (ρ j).restrict (hS j)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

def quotRep (ρ : J →* Module.End (ZMod p) W) (S : Submodule (ZMod p) W)
    (hS : ∀ j, ∀ w ∈ S, ρ j w ∈ S) : J →* Module.End (ZMod p) (W ⧸ S) where
  toFun j := S.mapQ S (ρ j) (fun w hw => hS j w hw)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

section SubQuot

variable {ρ : J →* Module.End (ZMod p) W} {S : Submodule (ZMod p) W}
  {hS : ∀ j, ∀ w ∈ S, ρ j w ∈ S}

theorem repKer_le_sub : repKer ρ ≤ repKer (subRep ρ S hS) := by
  intro j hj
  rw [mem_repKer] at hj ⊢
  ext w
  simp [subRep, hj]

theorem repKer_le_quot : repKer ρ ≤ repKer (quotRep ρ S hS) := by
  intro j hj
  rw [mem_repKer] at hj ⊢
  ext w
  simp [quotRep, hj]

theorem sub_quad {x : J} (h : (ρ x - 1) * (ρ x - 1) = 0) :
    (subRep ρ S hS x - 1) * (subRep ρ S hS x - 1) = 0 := by
  ext w
  have := LinearMap.congr_fun h w
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
  simp only [subRep, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply, LinearMap.coe_restrict_apply, Submodule.coe_sub]
  simpa using this

theorem quot_quad {x : J} (h : (ρ x - 1) * (ρ x - 1) = 0) :
    (quotRep ρ S hS x - 1) * (quotRep ρ S hS x - 1) = 0 := by
  ext w
  have := LinearMap.congr_fun h w
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at this
  simp [quotRep, ← Submodule.Quotient.mk_sub]
  have h0 : (ρ x) ((ρ x) w - w) - ((ρ x) w - w) = 0 := by simpa using this
  rw [map_sub] at h0
  rw [h0]
  exact S.zero_mem

theorem pow_eq_one_of_sub_quot (j : J) (k : ℕ)
    (h1 : subRep ρ S hS j ^ (p ^ k) = 1) (h2 : quotRep ρ S hS j ^ (p ^ k) = 1) :
    ρ j ^ (p ^ (k + 1)) = 1 := by
  have h1' : subRep ρ S hS (j ^ (p ^ k)) = 1 := by rw [map_pow]; exact h1
  have h2' : quotRep ρ S hS (j ^ (p ^ k)) = 1 := by rw [map_pow]; exact h2
  set T : Module.End (ZMod p) W := ρ (j ^ (p ^ k)) with hT
  have hTS : ∀ s ∈ S, T s = s := by
    intro s hs
    have := LinearMap.congr_fun h1' ⟨s, hs⟩
    have h' := congrArg Subtype.val this
    simpa [subRep, hT] using h'
  have hTQ : ∀ w, T w - w ∈ S := by
    intro w
    have := LinearMap.congr_fun h2' (Submodule.Quotient.mk w)
    have h3 : (Submodule.Quotient.mk (T w) : W ⧸ S) = Submodule.Quotient.mk w := by
      simpa [quotRep, hT] using this
    exact (Submodule.Quotient.eq S).mp h3
  have hN : (T - 1) * (T - 1) = 0 := by
    ext w
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply]
    have h5 := hTS _ (hTQ w)
    rw [map_sub] at h5
    rw [map_sub, h5]
    abel
  have hpow : T ^ p = 1 := by
    have e : T = 1 + (T - 1) := by abel
    have h6 := one_add_pow_sq_zero (T - 1) hN p
    rw [← e] at h6
    rw [h6]
    have : ((p : ℕ) : Module.End (ZMod p) W) = 0 := by
      have := map_natCast (algebraMap (ZMod p) (Module.End (ZMod p) W)) p
      rw [← this, ZMod.natCast_self, map_zero]
    rw [this, zero_mul, add_zero]
  have hT' : ρ j ^ (p ^ k) = T := by rw [hT, map_pow]
  rw [pow_succ, pow_mul, hT']
  exact hpow

omit [Fact p.Prime] in
theorem pow_eq_one_of_le {M : Type*} [Monoid M] {x : M} {k₁ k : ℕ} (h : x ^ (p ^ k₁) = 1)
    (hk : k₁ ≤ k) : x ^ (p ^ k) = 1 := by
  obtain ⟨m, hm⟩ := Nat.pow_dvd_pow p hk
  rw [hm, pow_mul, h, one_pow]

theorem nonP_sub_or_quot (hnon : ∃ j : J, ∀ k : ℕ, ρ j ^ (p ^ k) ≠ 1) :
    (∃ j : J, ∀ k : ℕ, subRep ρ S hS j ^ (p ^ k) ≠ 1) ∨
      (∃ j : J, ∀ k : ℕ, quotRep ρ S hS j ^ (p ^ k) ≠ 1) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨j, hj⟩ := hnon
  obtain ⟨k1, hk1⟩ := hcon.1 j
  obtain ⟨k2, hk2⟩ := hcon.2 j
  exact hj (max k1 k2 + 1) (pow_eq_one_of_sub_quot j (max k1 k2)
    (pow_eq_one_of_le hk1 (le_max_left _ _)) (pow_eq_one_of_le hk2 (le_max_right _ _)))

end SubQuot

theorem invariant_of_gens [Finite J] {a b : J} (hgen : Subgroup.closure ({a, b} : Set J) = ⊤)
    (ρ : J →* Module.End (ZMod p) W) (S : Submodule (ZMod p) W)
    (ha : ∀ w ∈ S, ρ a w ∈ S) (hb : ∀ w ∈ S, ρ b w ∈ S) : ∀ j, ∀ w ∈ S, ρ j w ∈ S := by
  have hpow : ∀ (j : J), (∀ w ∈ S, ρ j w ∈ S) → ∀ m : ℕ, ∀ w ∈ S, ρ (j ^ m) w ∈ S := by
    intro j hj m
    induction m with
    | zero => intro w hw; simpa using hw
    | succ m ih =>
      intro w hw
      rw [pow_succ', map_mul]
      exact hj _ (ih w hw)
  let A : Subgroup J :=
    { carrier := {j | ∀ w ∈ S, ρ j w ∈ S}
      one_mem' := fun w hw => by simpa using hw
      mul_mem' := fun {x y} hx hy w hw => by
        rw [map_mul]; exact hx _ (hy w hw)
      inv_mem' := fun {x} hx => by
        have hn : 0 < orderOf x := orderOf_pos x
        have : x⁻¹ = x ^ (orderOf x - 1) := by
          refine inv_eq_of_mul_eq_one_right ?_
          rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
        show ∀ w ∈ S, ρ x⁻¹ w ∈ S
        rw [this]
        exact hpow x hx _ }
  have hle : Subgroup.closure ({a, b} : Set J) ≤ A := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb
  rw [hgen] at hle
  exact fun j => hle (Subgroup.mem_top j)

theorem rep_trivial_of_gens {a b : J} (hgen : Subgroup.closure ({a, b} : Set J) = ⊤)
    (ρ : J →* Module.End (ZMod p) W) (ha : ρ a = 1) (hb : ρ b = 1) : ∀ j, ρ j = 1 := by
  have hle : Subgroup.closure ({a, b} : Set J) ≤ repKer ρ := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact mem_repKer.mpr ha
    · exact mem_repKer.mpr hb
  rw [hgen] at hle
  exact fun j => mem_repKer.mp (hle (Subgroup.mem_top j))


theorem exists_sl2_quotient (hp2 : p ≠ 2) [Finite J] {a b : J}
    (hgen : Subgroup.closure ({a, b} : Set J) = ⊤) :
    ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module (ZMod p) W] [Finite W]
      (ρ : J →* Module.End (ZMod p) W), Module.finrank (ZMod p) W = n →
      (ρ a - 1) * (ρ a - 1) = 0 → (ρ b - 1) * (ρ b - 1) = 0 →
      (∃ j : J, ∀ k : ℕ, ρ j ^ (p ^ k) ≠ 1) → Sl2Quot p J (repKer ρ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W _ _ _ ρ hn hqa hqb hnon
    by_cases hirr : ∀ S : Submodule (ZMod p) W, (∀ j, ∀ w ∈ S, ρ j w ∈ S) → S = ⊥ ∨ S = ⊤
    · have hinv : ∀ (S : Submodule (ZMod p) W), (∀ w ∈ S, (ρ a - 1) w ∈ S) →
          (∀ w ∈ S, (ρ b - 1) w ∈ S) → ∀ j, ∀ w ∈ S, ρ j w ∈ S := by
        intro S hSa hSb
        refine invariant_of_gens hgen ρ S (fun w hw => ?_) (fun w hw => ?_)
        · have := S.add_mem hw (hSa w hw)
          simpa using this
        · have := S.add_mem hw (hSb w hw)
          simpa using this
      by_cases ha : ρ a = 1
      · by_cases hb : ρ b = 1
        · exfalso
          obtain ⟨j, hj⟩ := hnon
          exact hj 0 (by rw [pow_zero, pow_one]; exact rep_trivial_of_gens hgen ρ ha hb j)
        · refine sl2_of_irreducible hp2 b a (by rwa [Set.pair_comm]) ρ
            ⟨hqb, hqa, sub_ne_zero.mpr hb, fun S hSb hSa => hirr S (hinv S hSa hSb)⟩
      · exact sl2_of_irreducible hp2 a b hgen ρ
          ⟨hqa, hqb, sub_ne_zero.mpr ha, fun S hSa hSb => hirr S (hinv S hSa hSb)⟩
    · push Not at hirr
      obtain ⟨S, hS, hS1, hS2⟩ := hirr
      have hlt1 : Module.finrank (ZMod p) S < n :=
        hn ▸ Submodule.finrank_lt hS2
      have hlt2 : Module.finrank (ZMod p) (W ⧸ S) < n := by
        have h1 := Submodule.finrank_quotient_add_finrank S
        have h2 : 1 ≤ Module.finrank (ZMod p) S := Submodule.one_le_finrank_iff.mpr hS1
        omega
      have hQfin : Finite (W ⧸ S) :=
        Finite.of_surjective (Submodule.Quotient.mk (p := S)) (Submodule.Quotient.mk_surjective S)
      rcases nonP_sub_or_quot (ρ := ρ) (S := S) (hS := hS) hnon with hnS | hnQ
      · exact (ih _ hlt1 S (subRep ρ S hS) rfl (sub_quad hqa) (sub_quad hqb) hnS).mono
          repKer_le_sub
      · exact (ih _ hlt2 (W ⧸ S) (quotRep ρ S hS) rfl (quot_quad hqa) (quot_quad hqb) hnQ).mono
          repKer_le_quot

end CFSG.GH74.GLS.Stage2.Signalizer.L53

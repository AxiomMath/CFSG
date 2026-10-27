module

public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Tactic.Abel
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

structure Core0 (M : Type*) [AddCommGroup M] where
  ρ : Module.End ℤ M
  G : ℕ → AddSubgroup M
  n : ℕ
  y : M
  hn : 4 ≤ n
  G1 : G 1 = ⊤
  anti : ∀ j, 1 ≤ j → G (j + 1) ≤ G j
  card : ∀ j, 1 ≤ j → j ≤ n → Nat.card (G j) = 3 ^ (n - j)
  bot : ∀ j, n ≤ j → G j = ⊥
  hρ : ∀ j, 1 ≤ j → ∀ u ∈ G j, (ρ - 1) u ∈ G (j + 1)
  ker : ∀ u, (ρ - 1) u = 0 → u ∈ G (n - 1)
  nρ1 : ∀ w, (1 + ρ + ρ * ρ) ((ρ - 1) w) = 0
  nρ2 : (1 + ρ + ρ * ρ) y = 0
  hy : y ∉ G 2

structure Core (M : Type*) [AddCommGroup M] extends Core0 M where
  f : Module.End ℤ M
  hf : ∀ j, 1 ≤ j → ∀ u ∈ G j, (f - 1) u ∈ G (j + 1)
  comm : ρ * f = f * ρ
  nf : (1 + f + f * f) y = 0
  fx : ∀ u ∈ G (n - 2), f u = u

section

variable {M : Type*} [AddCommGroup M] [Finite M]

theorem exists_decomp_of_index_three {H₁ H₂ : AddSubgroup M} (hle : H₂ ≤ H₁)
    (hcard : Nat.card H₁ = 3 * Nat.card H₂) {z : M} (hz1 : z ∈ H₁) (hz2 : z ∉ H₂) :
    ∀ u ∈ H₁, ∃ k : ℤ, u - k • z ∈ H₂ := by
  set K : AddSubgroup M := H₂ ⊔ AddSubgroup.zmultiples z with hK
  have hKle : K ≤ H₁ := sup_le hle (AddSubgroup.zmultiples_le.mpr hz1)
  have hH₂K : H₂ ≤ K := le_sup_left
  have hd1 : Nat.card H₂ ∣ Nat.card K := AddSubgroup.card_dvd_of_le hH₂K
  have hd2 : Nat.card K ∣ Nat.card H₁ := AddSubgroup.card_dvd_of_le hKle
  have hpos : 0 < Nat.card H₂ := Nat.card_pos
  obtain ⟨t, ht⟩ := hd1
  rw [ht, hcard] at hd2
  have ht3 : t ∣ 3 := by
    have := Nat.dvd_of_mul_dvd_mul_left hpos (by simpa [mul_comm] using hd2 : Nat.card H₂ * t ∣
      Nat.card H₂ * 3)
    exact this
  have hKne : K ≠ H₂ := by
    intro h
    apply hz2
    rw [← h]
    exact AddSubgroup.mem_sup_right (AddSubgroup.mem_zmultiples z)
  have ht1 : t ≠ 1 := by
    intro h1
    apply hKne
    refine (AddSubgroup.eq_of_le_of_card_ge hH₂K ?_).symm
    rw [ht, h1]; simp
  have ht3' : t = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd t ht3 with h | h
    · exact absurd h ht1
    · exact h
  have hKH : K = H₁ := AddSubgroup.eq_of_le_of_card_ge hKle (by rw [ht, ht3', hcard, mul_comm])
  intro u hu
  rw [← hKH, hK, AddSubgroup.mem_sup] at hu
  obtain ⟨a, ha, b, hb, rfl⟩ := hu
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hb
  exact ⟨k, by simpa using ha⟩

end

namespace Core0

variable {M : Type*} [AddCommGroup M] [Finite M] (c : Core0 M)

theorem G_le {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) : c.G j ≤ c.G i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact (c.anti j (by omega)).trans ih

theorem pow_mem (T : Module.End ℤ M) (hT : ∀ j, 1 ≤ j → ∀ u ∈ c.G j, T u ∈ c.G (j + 1))
    (k : ℕ) : ∀ j, 1 ≤ j → ∀ u ∈ c.G j, (T ^ k) u ∈ c.G (j + k) := by
  induction k with
  | zero => intro j _ u hu; simpa using hu
  | succ k ih =>
    intro j hj u hu
    have h1 := ih j hj u hu
    have h2 := hT (j + k) (by omega) _ h1
    rw [pow_succ']
    simpa [add_assoc] using h2

theorem card_G_pred : Nat.card (c.G (c.n - 1)) = 3 := by
  have h := c.card (c.n - 1) (by have := c.hn; omega) (by omega)
  rw [h, show c.n - (c.n - 1) = 1 by have := c.hn; omega]; simp

theorem delta_onto {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ c.n - 1) :
    ∀ v ∈ c.G (j + 1), ∃ u ∈ c.G j, (c.ρ - 1) u = v := by
  let ψ : c.G j →+ M := (c.ρ - 1).toAddMonoidHom.comp (c.G j).subtype
  have hker : Nat.card ψ.ker ≤ 3 := by
    rw [← c.card_G_pred]
    refine Nat.card_le_card_of_injective
      (fun u => (⟨((u : c.G j) : M), c.ker _ ?_⟩ : c.G (c.n - 1))) ?_
    · have := u.2
      rw [AddMonoidHom.mem_ker] at this
      exact this
    · intro a b hab
      have := congrArg (fun z : c.G (c.n - 1) => (z : M)) hab
      exact Subtype.ext (Subtype.ext this)
  have hmul := AddSubgroup.card_ker_mul_card_range ψ
  have hGj := c.card j hj (by omega)
  have hGj1 := c.card (j + 1) (by omega) (by omega)
  have hle : ψ.range ≤ c.G (j + 1) := by
    rintro _ ⟨u, rfl⟩
    exact c.hρ j hj u u.2
  have hge : Nat.card (c.G (j + 1)) ≤ Nat.card ψ.range := by
    have h3 : 3 ^ (c.n - j) = 3 ^ (c.n - (j + 1)) * 3 := by
      rw [← pow_succ]; congr 1; omega
    rw [hGj1]
    by_contra hlt
    push Not at hlt
    have : Nat.card ψ.ker * Nat.card ψ.range < 3 * 3 ^ (c.n - (j + 1)) := by
      calc Nat.card ψ.ker * Nat.card ψ.range ≤ 3 * Nat.card ψ.range :=
            Nat.mul_le_mul_right _ hker
        _ < 3 * 3 ^ (c.n - (j + 1)) := by omega
    rw [hmul, hGj, h3] at this
    omega
  have heq := AddSubgroup.eq_of_le_of_card_ge hle hge
  intro v hv
  rw [← heq] at hv
  obtain ⟨u, hu⟩ := hv
  exact ⟨u, u.2, hu⟩

theorem decomp_M : ∀ u : M, ∃ k : ℤ, ∃ w : M, u = k • c.y + (c.ρ - 1) w := by
  have h1 := c.card 1 le_rfl (by have := c.hn; omega)
  have h2 := c.card 2 (by omega) (by have := c.hn; omega)
  have hcard : Nat.card (c.G 1) = 3 * Nat.card (c.G 2) := by
    rw [h1, h2, ← pow_succ']; congr 1; have := c.hn; omega
  have hy1 : c.y ∈ c.G 1 := by rw [c.G1]; trivial
  intro u
  have hu : u ∈ c.G 1 := by rw [c.G1]; trivial
  obtain ⟨k, hk⟩ := exists_decomp_of_index_three (c.anti 1 le_rfl) hcard hy1 c.hy u hu
  obtain ⟨w, -, hw⟩ := c.delta_onto (j := 1) le_rfl (by have := c.hn; omega) _ hk
  exact ⟨k, w, by rw [hw]; abel⟩

theorem N_rho_eq_zero : ∀ u : M, (1 + c.ρ + c.ρ * c.ρ) u = 0 := by
  intro u
  obtain ⟨k, w, rfl⟩ := c.decomp_M u
  rw [map_add, map_zsmul, c.nρ2, c.nρ1]; simp

theorem three_smul_mem : ∀ t : M, (3 : ℤ) • t ∈ c.G 3 := by
  intro t
  have hN := c.N_rho_eq_zero t
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at hN
  set s : M := -(t + c.ρ t) with hs
  have hρs : c.ρ s = t := by
    rw [hs, map_neg, map_add]
    linear_combination (norm := module) (-1 : ℤ) • hN
  have hN2 := c.N_rho_eq_zero s
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at hN2
  have hmem : (c.ρ - 1) ((c.ρ - 1) s) ∈ c.G 3 := by
    have := c.pow_mem (c.ρ - 1) c.hρ 2 1 le_rfl s (by rw [c.G1]; trivial)
    simpa [pow_two] using this
  have key : (3 : ℤ) • t = -((c.ρ - 1) ((c.ρ - 1) s)) := by
    rw [← hρs]
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    linear_combination (norm := module) hN2
  rw [key]
  exact AddSubgroup.neg_mem _ hmem

theorem G3_le_three : ∀ v ∈ c.G 3, ∃ t : M, v = (3 : ℤ) • t := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := c.delta_onto (j := 2) (by omega) (by have := c.hn; omega) v hv
  obtain ⟨w, -, rfl⟩ := c.delta_onto (j := 1) (by omega) (by have := c.hn; omega) u hu
  refine ⟨-(c.ρ w), ?_⟩
  have hN := c.N_rho_eq_zero w
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at hN
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  linear_combination (norm := module) hN

theorem shift2 (T : Module.End ℤ M) (hTρ : T * (c.ρ - 1) = (c.ρ - 1) * T)
    (hTy : T c.y ∈ c.G 3) :
    ∀ j, 1 ≤ j → ∀ u ∈ c.G j, T u ∈ c.G (j + 2) := by
  have hcom : ∀ k : ℕ, ∀ u : M, T (((c.ρ - 1) ^ k) u) = ((c.ρ - 1) ^ k) (T u) := by
    intro k u
    have : Commute T (c.ρ - 1) := hTρ
    have h2 := (this.pow_right k).eq
    exact congrArg (fun F : Module.End ℤ M => F u) h2
  have hrepr : ∀ j, 1 ≤ j → ∀ u ∈ c.G j, ∃ k : ℤ, ∃ w ∈ c.G (j + 1),
      u = k • ((c.ρ - 1) ^ (j - 1)) c.y + w := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      intro u hu
      obtain ⟨k, w, rfl⟩ := c.decomp_M u
      exact ⟨k, (c.ρ - 1) w, c.hρ 1 le_rfl w (by rw [c.G1]; trivial), by simp⟩
    | succ j hj ih =>
      intro u hu
      by_cases hjn : j ≤ c.n - 1
      · obtain ⟨u', hu', rfl⟩ := c.delta_onto hj hjn u hu
        obtain ⟨k, w, hw, rfl⟩ := ih u' hu'
        refine ⟨k, (c.ρ - 1) w, c.hρ (j + 1) (by omega) w hw, ?_⟩
        rw [map_add, map_zsmul]
        have : (j + 1 - 1) = (j - 1) + 1 := by omega
        rw [this, pow_succ']
        rfl
      · have : c.G (j + 1) = ⊥ := c.bot _ (by omega)
        rw [this] at hu
        have hu0 : u = 0 := by simpa using hu
        exact ⟨0, 0, AddSubgroup.zero_mem _, by simp [hu0]⟩
  have main : ∀ k : ℕ, ∀ j, 1 ≤ j → c.n ≤ j + k → ∀ u ∈ c.G j, T u ∈ c.G (j + 2) := by
    intro k
    induction k with
    | zero =>
      intro j hj hn u hu
      have : c.G j = ⊥ := c.bot j (by omega)
      rw [this] at hu
      have hu0 : u = 0 := by simpa using hu
      subst hu0; simp
    | succ k ih =>
      intro j hj hn u hu
      obtain ⟨a, w, hw, rfl⟩ := hrepr j hj u hu
      rw [map_add, map_zsmul, hcom]
      refine AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ ?_ _) ?_
      · have := c.pow_mem (c.ρ - 1) c.hρ (j - 1) 3 (by omega) _ hTy
        have e : 3 + (j - 1) = j + 2 := by omega
        rwa [e] at this
      · have := ih (j + 1) (by omega) (by omega) w hw
        exact c.G_le (i := j + 2) (j := j + 1 + 2) (by omega) (by omega) this
  intro j hj u hu
  exact main c.n j hj (by omega) u hu

@[expose] def triple (M : Type*) [AddCommGroup M] : M →+ M := AddMonoidHom.mk' (fun u => (3 : ℤ) • u)
  (fun _ _ => smul_add _ _ _)

@[simp] theorem triple_apply (M : Type*) [AddCommGroup M] (u : M) : triple M u = (3 : ℤ) • u := rfl

theorem range_triple : (triple M).range = c.G 3 := by
  ext v
  constructor
  · rintro ⟨t, rfl⟩
    exact c.three_smul_mem t
  · intro hv
    obtain ⟨t, rfl⟩ := c.G3_le_three v hv
    exact ⟨t, rfl⟩

include c in
theorem card_ker_triple : Nat.card (triple M).ker = 9 := by
  have h := AddSubgroup.card_ker_mul_card_range (triple M)
  rw [c.range_triple, c.card 3 (by omega) (by have := c.hn; omega)] at h
  have h1 : Nat.card M = 3 ^ (c.n - 1) := by
    have := c.card 1 le_rfl (by have := c.hn; omega)
    rw [c.G1] at this
    simpa using this
  rw [h1] at h
  have h2 : 3 ^ (c.n - 1) = 3 ^ (c.n - 3) * 9 := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add]; congr 1; have := c.hn; omega
  rw [h2] at h
  have hpos : 0 < 3 ^ (c.n - 3) := pow_pos (by norm_num) _
  exact Nat.eq_of_mul_eq_mul_right hpos (h.trans (mul_comm _ _))

end Core0

namespace Core

variable {M : Type*} [AddCommGroup M] [Finite M] (c : Core M)

theorem N_f_eq_zero : ∀ u : M, (1 + c.f + c.f * c.f) u = 0 := by
  set T : Module.End ℤ M := 1 + c.f + c.f * c.f with hT
  have hcomm : T * (c.ρ - 1) = (c.ρ - 1) * T := by
    have hc : Commute c.ρ c.f := c.comm
    have hρT : Commute c.ρ T := ((Commute.one_right _).add_right hc).add_right (hc.mul_right hc)
    exact ((hρT.sub_left (Commute.one_left _)).eq).symm
  have key : ∀ k : ℕ, ∀ u : M, T u ∈ c.G (k + 1) := by
    intro k
    induction k with
    | zero => intro u; rw [c.G1]; trivial
    | succ k ih =>
      intro u
      obtain ⟨a, w, rfl⟩ := c.decomp_M u
      have : T (a • c.y + (c.ρ - 1) w) = (c.ρ - 1) (T w) := by
        rw [map_add, map_zsmul, c.nf]
        have := congrArg (fun F : Module.End ℤ M => F w) hcomm
        simpa using this
      rw [this]
      exact c.hρ (k + 1) (by omega) _ (ih w)
  intro u
  have := key c.n u
  rw [c.bot (c.n + 1) (by omega)] at this
  simpa using this

include c in
theorem false_aux : False := by
  have hn := c.hn
  have hg_comm : (c.f - 1) * (c.ρ - 1) = (c.ρ - 1) * (c.f - 1) := by
    have hc : Commute c.ρ c.f := c.comm
    exact ((hc.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)).eq.symm
  have hgy : (c.f - 1) c.y ∈ c.G 3 := by
    by_contra hnot
    have hy1 : c.y ∈ c.G 1 := by rw [c.G1]; trivial
    have hgy2 : (c.f - 1) c.y ∈ c.G 2 := c.hf 1 le_rfl c.y hy1
    have hδy2 : (c.ρ - 1) c.y ∈ c.G 2 := c.hρ 1 le_rfl c.y hy1
    have hδy3 : (c.ρ - 1) c.y ∉ c.G 3 := by
      intro h3
      obtain ⟨u, hu, hδu⟩ := c.delta_onto (j := 2) (by omega) (by omega) _ h3
      have hker : (c.ρ - 1) (c.y - u) = 0 := by rw [map_sub, hδu]; simp
      have := c.G_le (i := 2) (j := c.n - 1) (by omega) (by omega) (c.ker _ hker)
      apply c.hy
      have h' := AddSubgroup.add_mem _ this hu
      simpa using h'
    have hcard : Nat.card (c.G 2) = 3 * Nat.card (c.G 3) := by
      rw [c.card 2 (by omega) (by omega), c.card 3 (by omega) (by omega), ← pow_succ']
      congr 1; omega
    obtain ⟨l, hl⟩ := exists_decomp_of_index_three (c.anti 2 (by omega)) hcard hδy2 hδy3 _ hgy2
    set T : Module.End ℤ M := c.f - 1 - l • (c.ρ - 1) with hT
    have hTρ : T * (c.ρ - 1) = (c.ρ - 1) * T := by
      have hc : Commute (c.f - 1) (c.ρ - 1) := hg_comm
      exact (hc.sub_left ((Commute.refl (c.ρ - 1)).smul_left l)).eq
    have hTy : T c.y ∈ c.G 3 := by
      have : T c.y = (c.f - 1) c.y - l • (c.ρ - 1) c.y := by simp [hT]
      rw [this]; exact hl
    have hshift := c.shift2 T hTρ hTy
    have hex : ∃ u ∈ c.G (c.n - 2), u ∉ c.G (c.n - 1) := by
      by_contra hno
      push Not at hno
      have hle : c.G (c.n - 2) ≤ c.G (c.n - 1) := fun u hu => hno u hu
      have hd := AddSubgroup.card_dvd_of_le hle
      rw [c.card (c.n - 2) (by omega) (by omega), c.card_G_pred] at hd
      have : (3 : ℕ) ^ (c.n - (c.n - 2)) = 9 := by
        rw [show c.n - (c.n - 2) = 2 by omega]; norm_num
      rw [this] at hd
      omega
    obtain ⟨u0, hu0, hu0n⟩ := hex
    have hδu0 : (c.ρ - 1) u0 ≠ 0 := fun h => hu0n (c.ker _ h)
    have hδmem : (c.ρ - 1) u0 ∈ c.G (c.n - 1) := by
      have := c.hρ (c.n - 2) (by omega) u0 hu0
      rwa [show c.n - 2 + 1 = c.n - 1 by omega] at this
    have hTu0 : T u0 = 0 := by
      have := hshift (c.n - 2) (by omega) u0 hu0
      rw [show c.n - 2 + 2 = c.n by omega, c.bot c.n le_rfl] at this
      simpa using this
    have hTu0' : T u0 = -(l • (c.ρ - 1) u0) := by
      have := c.fx u0 hu0
      simp [hT, this]
    have hl0 : l • (c.ρ - 1) u0 = 0 := by
      have := hTu0; rw [hTu0'] at this; simpa using this
    have h3 : (3 : ℕ) • (c.ρ - 1) u0 = 0 := by
      have : Nat.card (c.G (c.n - 1)) • (⟨(c.ρ - 1) u0, hδmem⟩ : c.G (c.n - 1)) = 0 :=
        card_nsmul_eq_zero'
      rw [c.card_G_pred] at this
      exact congrArg Subtype.val this
    have hord : addOrderOf ((c.ρ - 1) u0) = 3 := addOrderOf_eq_prime h3 hδu0
    have hdvd : ((3 : ℕ) : ℤ) ∣ l := by
      rw [← hord]
      exact (addOrderOf_dvd_iff_zsmul_eq_zero).mpr hl0
    obtain ⟨l', rfl⟩ := hdvd
    apply hnot
    have h3y : (3 : ℤ) • (c.ρ - 1) c.y ∈ c.G 3 := c.three_smul_mem _
    have h5 : l' • ((3 : ℤ) • (c.ρ - 1) c.y) ∈ c.G 3 := AddSubgroup.zsmul_mem _ h3y _
    have h4 := AddSubgroup.add_mem _ hl h5
    have e : (((3 : ℕ) : ℤ) * l') • (c.ρ - 1) c.y = l' • ((3 : ℤ) • (c.ρ - 1) c.y) := by
      rw [mul_comm, mul_smul]; norm_num
    rw [e] at h4
    simpa using h4
  have hshift := c.shift2 (c.f - 1) hg_comm hgy
  have hg3 : ∀ u : M, (c.f - 1) u ∈ c.G 3 := fun u => hshift 1 le_rfl u (by rw [c.G1]; trivial)
  have hg35 : ∀ u ∈ c.G 3, (c.f - 1) u ∈ c.G 5 := fun u hu => hshift 3 (by omega) u hu
  have h35 : ∀ t : M, (3 : ℤ) • t ∈ c.G 5 := by
    intro t
    have hN := c.N_f_eq_zero t
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at hN
    set s : M := -(t + c.f t) with hs
    have hfs : c.f s = t := by
      rw [hs, map_neg, map_add]
      linear_combination (norm := module) (-1 : ℤ) • hN
    have hN2 := c.N_f_eq_zero s
    simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at hN2
    have key : (3 : ℤ) • t = -((c.f - 1) ((c.f - 1) s)) := by
      rw [← hfs]
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
      linear_combination (norm := module) hN2
    rw [key]
    exact AddSubgroup.neg_mem _ (hg35 _ (hg3 s))
  have hle : c.G 3 ≤ c.G 5 := by
    intro v hv
    obtain ⟨t, rfl⟩ := c.G3_le_three v hv
    exact h35 t
  have hd := AddSubgroup.card_dvd_of_le hle
  rw [c.card 3 (by omega) (by omega)] at hd
  by_cases h5 : 5 ≤ c.n
  · rw [c.card 5 (by omega) h5] at hd
    have := Nat.le_of_dvd (pow_pos (by norm_num) _) hd
    have h2 : 3 ^ (c.n - 5) < 3 ^ (c.n - 3) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · rw [c.bot 5 (by omega)] at hd
    simp at hd
    omega

end Core

end CFSG.HardMathSupport.Lang.E6Descent

module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

private theorem parity_card_modEq {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {c : G} (hc : c ^ p = 1) (S : Subgroup G) (hS : ∀ x ∈ S, c * x * c⁻¹ ∈ S) :
    Nat.card S ≡ Nat.card {x : S // c * (x : G) = x * c} [MOD p] := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let f : Function.End S := fun x => ⟨c * x * c⁻¹, hS x x.2⟩
  have hpow : ∀ (n : ℕ) (x : S), (((f ^ n) x : S) : G) = c ^ n * x * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; show (x : G) = _; simp
    | succ n ih =>
      intro x
      have h1 : (f ^ (n + 1)) x = (f ^ n) (f x) := by
        rw [pow_succ]; rfl
      rw [h1, ih]
      show c ^ n * (c * (x : G) * c⁻¹) * (c ^ n)⁻¹ = c ^ (n + 1) * x * (c ^ (n + 1))⁻¹
      simp only [pow_succ, mul_inv_rev, mul_assoc]
  have hf : f ^ p ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    rw [hpow, pow_one, hc]
    show _ = (x : G)
    simp
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [Nat.card_eq_fintype_card]
  have h2 : Nat.card {x : S // c * (x : G) = x * c} = Fintype.card (Function.fixedPoints f) := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    show c * (x : G) = x * c ↔ f x = x
    rw [Subtype.ext_iff]
    show c * (x : G) = x * c ↔ c * x * c⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
  rw [h2]
  exact h

private theorem parity_comm {G : Type*} [Group G] {W : Subgroup G} (hW : IsElemAbelian 2 W)
    {x y : G} (hx : x ∈ W) (hy : y ∈ W) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hW hx hy

private theorem parity_conj_mem {G : Type*} [Group G] {W : Subgroup G} {c : G}
    (hcW : c ∈ normalizer (W : Set G)) {w : G} (hw : w ∈ W) : c * w * c⁻¹ ∈ W :=
  (mem_set_normalizer_iff.1 hcW w).1 hw

private theorem parity_ident {A : Type*} [Group A] (hcomm : ∀ x y : A, x * y = y * x)
    (hsq : ∀ x : A, x * x = 1) (x₀ x₁ x₂ x₃ x₄ x₅ x₆ : A) :
    (x₃ * x₅ * x₀ * (x₂ * x₄ * x₆)⁻¹) * ((x₂ * x₄ * x₆) * (x₁ * x₃ * x₅)⁻¹)⁻¹ = x₁ * x₀⁻¹ := by
  let _ : CommGroup A := { ‹Group A› with mul_comm := hcomm }
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  simp only [hinv]
  calc _ = x₀ * x₁ * (x₂ * x₂) * (x₃ * x₃) * (x₄ * x₄) * (x₅ * x₅) * (x₆ * x₆) := by ac_rfl
    _ = x₁ * x₀ := by simp [hsq, mul_comm]

private theorem parity_key {G : Type*} [Group G] {W : Subgroup G} {c : G}
    (hW : IsElemAbelian 2 W) (hcW : c ∈ normalizer (W : Set G)) (hc7 : c ^ 7 = 1) {w : G}
    (hw : w ∈ W) :
    ∃ v ∈ W, c * (c * v * c⁻¹ * v⁻¹) * c⁻¹ * (c * v * c⁻¹ * v⁻¹)⁻¹ = c * w * c⁻¹ * w⁻¹ := by
  set t : ℕ → G := fun k => c ^ k * w * (c ^ k)⁻¹ with ht
  have ht0 : t 0 = w := by simp [ht]
  have ht7 : t 7 = w := by simp [ht, hc7]
  have htS : ∀ k, c * t k * c⁻¹ = t (k + 1) := by
    intro k
    simp only [ht, pow_succ', mul_inv_rev, mul_assoc]
  have htW : ∀ k, t k ∈ W := by
    intro k
    induction k with
    | zero => rw [ht0]; exact hw
    | succ k ih => rw [← htS]; exact parity_conj_mem hcW ih
  refine ⟨t 1 * t 3 * t 5, mul_mem (mul_mem (htW 1) (htW 3)) (htW 5), ?_⟩
  have hv : c * (t 1 * t 3 * t 5) * c⁻¹ = t 2 * t 4 * t 6 := by
    rw [show c * (t 1 * t 3 * t 5) * c⁻¹ =
      (c * t 1 * c⁻¹) * (c * t 3 * c⁻¹) * (c * t 5 * c⁻¹) by group, htS, htS, htS]
  have hTv : c * (t 2 * t 4 * t 6) * c⁻¹ = t 3 * t 5 * t 7 := by
    rw [show c * (t 2 * t 4 * t 6) * c⁻¹ =
      (c * t 2 * c⁻¹) * (c * t 4 * c⁻¹) * (c * t 6 * c⁻¹) by group, htS, htS, htS]
  have h1 : c * ((t 2 * t 4 * t 6) * (t 1 * t 3 * t 5)⁻¹) * c⁻¹ =
      (t 3 * t 5 * t 7) * (t 2 * t 4 * t 6)⁻¹ := by
    rw [show c * ((t 2 * t 4 * t 6) * (t 1 * t 3 * t 5)⁻¹) * c⁻¹ =
      (c * (t 2 * t 4 * t 6) * c⁻¹) * (c * (t 1 * t 3 * t 5) * c⁻¹)⁻¹ by group, hTv, hv]
  have key : t 3 * t 5 * t 0 * (t 2 * t 4 * t 6)⁻¹ *
      (t 2 * t 4 * t 6 * (t 1 * t 3 * t 5)⁻¹)⁻¹ = t 1 * (t 0)⁻¹ :=
    congrArg Subtype.val (parity_ident (A := W) (fun x y => by
      have := hW.1
      exact Subtype.ext (setLike_mul_comm x.2 y.2)) (fun x => by
      apply Subtype.ext
      simpa [sq] using hW.2 x x.2) ⟨t 0, htW 0⟩ ⟨t 1, htW 1⟩ ⟨t 2, htW 2⟩ ⟨t 3, htW 3⟩
      ⟨t 4, htW 4⟩ ⟨t 5, htW 5⟩ ⟨t 6, htW 6⟩)
  rw [hv, h1, ht7]
  rw [ht0] at key
  have h01 : c * w * c⁻¹ = t 1 := by
    have := htS 0
    rwa [ht0] at this
  rw [h01]
  exact key

private theorem parity_exists_psi {G : Type*} [Group G] {W B : Subgroup G} {c : G}
    (hW : IsElemAbelian 2 W) (hcW : c ∈ normalizer (W : Set G)) (hBW : B ≤ W) :
    ∃ ψ : B →* G, ∀ u : B, ψ u = c * u * c⁻¹ * (u : G)⁻¹ := by
  refine ⟨{ toFun := fun u => c * u * c⁻¹ * (u : G)⁻¹, map_one' := by simp, map_mul' := ?_ },
    fun u => rfl⟩
  intro u v
  have hu : (u : G) ∈ W := hBW u.2
  have hv : (v : G) ∈ W := hBW v.2
  have h1 : (u : G)⁻¹ * (c * v * c⁻¹) = (c * v * c⁻¹) * (u : G)⁻¹ :=
    parity_comm hW (inv_mem hu) (parity_conj_mem hcW hv)
  have h2 : (v : G)⁻¹ * (u : G)⁻¹ = (u : G)⁻¹ * (v : G)⁻¹ :=
    parity_comm hW (inv_mem hv) (inv_mem hu)
  show c * ((u : G) * v) * c⁻¹ * ((u : G) * v)⁻¹ =
    (c * u * c⁻¹ * (u : G)⁻¹) * (c * v * c⁻¹ * (v : G)⁻¹)
  calc c * ((u : G) * v) * c⁻¹ * ((u : G) * v)⁻¹
      = (c * u * c⁻¹) * (c * v * c⁻¹) * ((v : G)⁻¹ * (u : G)⁻¹) := by group
    _ = (c * u * c⁻¹) * (c * v * c⁻¹) * ((u : G)⁻¹ * (v : G)⁻¹) := by rw [h2]
    _ = (c * u * c⁻¹) * ((c * v * c⁻¹) * (u : G)⁻¹) * (v : G)⁻¹ := by group
    _ = (c * u * c⁻¹) * ((u : G)⁻¹ * (c * v * c⁻¹)) * (v : G)⁻¹ := by rw [h1]
    _ = (c * u * c⁻¹ * (u : G)⁻¹) * (c * v * c⁻¹ * (v : G)⁻¹) := by group

private theorem parity_ker_eq {G : Type*} [Group G] [Finite G] {W A₀ B₀ : Subgroup G} {c : G}
    (hW : IsElemAbelian 2 W) (hc7 : c ^ 7 = 1) (hBW : B₀ ≤ W)
    (hA : ∀ a ∈ A₀, c * a = a * c) (hB : ∀ w ∈ W, c * w * c⁻¹ * w⁻¹ ∈ B₀)
    (hcard : A₀.relIndex B₀ = 8) (hnt : ∃ u ∈ B₀, c * u * c⁻¹ * u⁻¹ ∉ A₀)
    (ψ : B₀ →* G) (hψ : ∀ u : B₀, ψ u = c * u * c⁻¹ * (u : G)⁻¹) :
    ψ.ker = A₀.subgroupOf B₀ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker_iff : ∀ u : B₀, u ∈ ψ.ker ↔ c * (u : G) = u * c := by
    intro u
    rw [MonoidHom.mem_ker, hψ, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hS : ∀ x ∈ B₀, c * x * c⁻¹ ∈ B₀ := by
    intro x hx
    have := mul_mem (hB x (hBW hx)) hx
    simpa [mul_assoc] using this
  have hmod := parity_card_modEq hc7 B₀ hS
  have hc : Nat.card {x : B₀ // c * (x : G) = x * c} = Nat.card ψ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hker_iff x).symm)
  rw [hc, ← Subgroup.card_mul_index ψ.ker] at hmod
  have hB2 : IsPGroup 2 B₀ := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hW.2 x (hBW x.2)⟩
  obtain ⟨n, hn⟩ := (hB2.to_subgroup ψ.ker).exists_card_eq
  have hcop : Nat.gcd 7 (Nat.card ψ.ker) = 1 := by
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hk : ψ.ker.index ≡ 1 [MOD 7] := by
    apply Nat.ModEq.cancel_left_of_coprime hcop
    simpa using hmod
  have hA'K : A₀.subgroupOf B₀ ≤ ψ.ker := fun u hu => (hker_iff u).2 (hA u hu)
  have hidx : (A₀.subgroupOf B₀).index = 8 := hcard
  have hdvd : ψ.ker.index ∣ 8 := by
    have := Subgroup.index_dvd_of_le hA'K
    rwa [hidx] at this
  have hle : ψ.ker.index ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < ψ.ker.index := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hcases : ψ.ker.index = 1 ∨ ψ.ker.index = 8 := by
    unfold Nat.ModEq at hk
    omega
  rcases hcases with h1 | h8
  · exfalso
    have htop : ψ.ker = ⊤ := Subgroup.index_eq_one.1 h1
    obtain ⟨u, hu, hu'⟩ := hnt
    apply hu'
    have hmem : (⟨u, hu⟩ : B₀) ∈ ψ.ker := by rw [htop]; trivial
    have h := (hker_iff _).1 hmem
    have h2 : c * u * c⁻¹ * u⁻¹ = 1 := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]; exact h
    rw [h2]
    exact one_mem A₀
  · refine le_antisymm ?_ hA'K
    have h := Subgroup.relIndex_mul_index hA'K
    have hrel : (A₀.subgroupOf B₀).relIndex ψ.ker = 1 := by
      rw [h8, hidx] at h
      omega
    exact Subgroup.relIndex_eq_one.1 hrel

private theorem parity_card_mod_three {G : Type*} [Group G] [Finite G] {W : Subgroup G} {b : G}
    (hb3 : b ^ 3 = 1) (hfix : ∀ w ∈ W, b * w = w * b → w = 1) (E : Subgroup G) (hEW : E ≤ W)
    (hE : ∀ x ∈ E, b * x * b⁻¹ ∈ E) : Nat.card E ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := parity_card_modEq hb3 E hE
  have h1 : Nat.card {x : E // b * (x : G) = x * b} = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => ?_⟩, ⟨⟨1, one_mem E⟩, by simp⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [hfix x (hEW x.1.2) x.2, hfix y (hEW y.1.2) y.2]
  rwa [h1] at h

theorem parity_false_of_series {G : Type*} [Group G] [Finite G] {W A₀ B₀ : Subgroup G} {c b : G}
    (hW : IsElemAbelian 2 W) (hcW : c ∈ normalizer (W : Set G))
    (hbW : b ∈ normalizer (W : Set G)) (hc7 : c ^ 7 = 1) (hb3 : b ^ 3 = 1)
    (hcb : ∀ w ∈ W, c * (b * w * b⁻¹) * c⁻¹ = b * (c * w * c⁻¹) * b⁻¹)
    (hfix : ∀ w ∈ W, b * w = w * b → w = 1) (hAB : A₀ ≤ B₀) (hBW : B₀ ≤ W)
    (hA : ∀ a ∈ A₀, c * a = a * c) (hB : ∀ w ∈ W, c * w * c⁻¹ * w⁻¹ ∈ B₀)
    (hcard : A₀.relIndex B₀ = 8) (hnt : ∃ u ∈ B₀, c * u * c⁻¹ * u⁻¹ ∉ A₀) : False := by
  have _ := hAB
  obtain ⟨ψ, hψ⟩ := parity_exists_psi (B := B₀) hW hcW hBW
  have hker := parity_ker_eq hW hc7 hBW hA hB hcard hnt ψ hψ
  have hrange : Nat.card ψ.range = 8 := by
    rw [← Subgroup.index_ker, hker]
    exact hcard
  have hEW : ψ.range ≤ W := by
    rintro x ⟨u, rfl⟩
    rw [hψ]
    exact mul_mem (parity_conj_mem hcW (hBW u.2)) (inv_mem (hBW u.2))
  have hmem : ∀ w ∈ W, c * w * c⁻¹ * w⁻¹ ∈ ψ.range := by
    intro w hw
    obtain ⟨v, hv, hvw⟩ := parity_key hW hcW hc7 hw
    refine ⟨⟨c * v * c⁻¹ * v⁻¹, hB v hv⟩, ?_⟩
    rw [hψ]
    exact hvw
  have hstable : ∀ x ∈ ψ.range, b * x * b⁻¹ ∈ ψ.range := by
    rintro x ⟨u, rfl⟩
    have hu : (u : G) ∈ W := hBW u.2
    have h := hmem (b * u * b⁻¹) ((mem_set_normalizer_iff.1 hbW u).1 hu)
    rw [hψ]
    convert h using 1
    rw [hcb u hu]
    group
  have h3 := parity_card_mod_three hb3 hfix ψ.range hEW hstable
  rw [hrange] at h3
  exact absurd h3 (by decide)

end CFSG.LocalAnalysis.RankThreeTheoremC

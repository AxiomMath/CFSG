module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.FanoLemmas
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup

namespace Fano

variable {G : Type*} [Group G]

theorem fix_eq_one_of_four {K : Subgroup G} (hK : Nat.card K = 4) (φ : G ≃* G)
    (hφ3 : ∀ x, φ (φ (φ x)) = x) (hφK : ∀ x ∈ K, φ x ∈ K) (hmove : ∃ x ∈ K, φ x ≠ x)
    {c : G} (hc : c ∈ K) (hfix : φ c = c) : c = 1 := by
  by_contra hc1
  obtain ⟨x, hx, hxne⟩ := hmove
  have hφ1 : φ 1 = 1 := map_one φ
  have hinj := φ.injective
  have hx1 : x ≠ 1 := fun h => hxne (by rw [h, hφ1])
  have hφx1 : φ x ≠ 1 := fun h => hx1 (hinj (h.trans hφ1.symm))
  have hcx : c ≠ x := fun h => hxne (by rw [← h, hfix])
  have hcφx : c ≠ φ x := by
    intro h
    have h1 : φ x = φ c := by rw [hfix]; exact h.symm
    have h2 : x = c := hinj h1
    exact hxne (by rw [h2]; exact hfix)
  have hall := eq_of_four_distinct hK (one_mem K) hc hx (hφK x hx) (Ne.symm hc1)
    (Ne.symm hx1) (Ne.symm hφx1) hcx hcφx (Ne.symm hxne) (φ (φ x)) (hφK _ (hφK x hx))
  rcases hall with h | h | h | h
  · exact hφx1 (hinj (h.trans hφ1.symm))
  · exact hcφx (hinj (h.trans hfix.symm)).symm
  · exact hxne ((congrArg φ h).symm.trans (hφ3 x))
  · exact hxne (hinj h)

theorem eq_orbit_of_four {K : Subgroup G} (hK : Nat.card K = 4) (φ : G ≃* G)
    (hφ3 : ∀ x, φ (φ (φ x)) = x) (hφK : ∀ x ∈ K, φ x ∈ K) (hmove : ∃ x ∈ K, φ x ≠ x)
    {x : G} (hx : x ∈ K) (hx1 : x ≠ 1) {y : G} (hy : y ∈ K) (hy1 : y ≠ 1) :
    y = x ∨ y = φ x ∨ y = φ (φ x) := by
  have hinj := φ.injective
  have hφ1 : φ 1 = 1 := map_one φ
  have hfix : φ x ≠ x := fun h => hx1 (fix_eq_one_of_four hK φ hφ3 hφK hmove hx h)
  have hφx1 : φ x ≠ 1 := fun h => hx1 (hinj (h.trans hφ1.symm))
  have hφφx1 : φ (φ x) ≠ 1 := fun h => hφx1 (hinj (h.trans hφ1.symm))
  have hxφφ : x ≠ φ (φ x) := fun h => hfix ((congrArg φ h).trans (hφ3 x))
  have hφxφφ : φ x ≠ φ (φ x) := fun h => hfix (hinj h).symm
  have hall := eq_of_four_distinct hK (one_mem K) hx (hφK x hx) (hφK _ (hφK x hx))
    (Ne.symm hx1) (Ne.symm hφx1) (Ne.symm hφφx1) (Ne.symm hfix) hxφφ hφxφφ y hy
  rcases hall with h | h | h | h
  · exact absurd h hy1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem pred_of_invariant (E U U₁ : Subgroup G) (t u : G) (φ ψ : G ≃* G) (P : G → Prop)
    (hE8 : Nat.card E = 8) (hE2 : ∀ x ∈ E, x * x = 1)
    (hU : U ≤ E) (hU4 : Nat.card U = 4) (hU₁ : U₁ ≤ E) (hU₁4 : Nat.card U₁ = 4)
    (htE : t ∈ E) (htU : t ∉ U) (huU : u ∈ U) (huU₁ : u ∉ U₁)
    (hφ3 : ∀ x, φ (φ (φ x)) = x) (hφU : ∀ x ∈ U, φ x ∈ U) (hφt : φ t = t)
    (hφx : ∃ x ∈ U, φ x ≠ x)
    (hψ3 : ∀ x, ψ (ψ (ψ x)) = x) (hψU₁ : ∀ x ∈ U₁, ψ x ∈ U₁) (hψu : ψ u = u)
    (hψx : ∃ x ∈ U₁, ψ x ≠ x)
    (ht : P t) (hPφ : ∀ x, P x → P (φ x)) (hPψ : ∀ x, P x → P (ψ x)) :
    ∀ e ∈ E, e ≠ 1 → P e := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    mul_comm_of_mul_self_eq_one (hE2 x hx) (hE2 y hy) (hE2 _ (mul_mem hx hy))
  have hxU₁ : ∀ x ∈ E, x ∉ U₁ → u⁻¹ * x ∈ U₁ := fun x hx hx₁ =>
    inv_mul_mem_of_index_two hU₁ hE8 hU₁4 (hU huU) huU₁ hx hx₁
  have hψE : ∀ x ∈ E, ψ x ∈ E := by
    intro x hx
    by_cases hx₁ : x ∈ U₁
    · exact hU₁ (hψU₁ x hx₁)
    · have h1 := hxU₁ x hx hx₁
      have h2 : ψ x = u * ψ (u⁻¹ * x) := by
        rw [map_mul, map_inv, hψu]; group
      rw [h2]
      exact mul_mem (hU huU) (hU₁ (hψU₁ _ h1))
  have hfixψ : ∀ x ∈ E, ψ x = x → x ∈ U := by
    intro x hxE hx
    by_cases hx₁ : x ∈ U₁
    · rw [fix_eq_one_of_four hU₁4 ψ hψ3 hψU₁ hψx hx₁ hx]
      exact one_mem U
    · have h1 := hxU₁ x hxE hx₁
      have h2 : ψ (u⁻¹ * x) = u⁻¹ * x := by rw [map_mul, map_inv, hψu, hx]
      have h3 := fix_eq_one_of_four hU₁4 ψ hψ3 hψU₁ hψx h1 h2
      rw [← inv_mul_eq_one.mp h3]
      exact huU
  have ht1 : t ≠ 1 := fun h => htU (h ▸ one_mem U)
  obtain ⟨p, hp⟩ : ∃ p, ψ t = p := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, ψ p = q := ⟨_, rfl⟩
  have hqt : ψ q = t := by rw [← hq, ← hp]; exact hψ3 t
  have hpE : p ∈ E := hp ▸ hψE t htE
  have hqE : q ∈ E := hq ▸ hψE p hpE
  have hPp : P p := hp ▸ hPψ t ht
  have hPq : P q := hq ▸ hPψ p hPp
  have hpt : p ≠ t := fun h => htU (hfixψ t htE (hp.trans h))
  have hp1 : p ≠ 1 := fun h => ht1 (ψ.injective (hp.trans (h.trans (map_one ψ).symm)))
  have hq1 : q ≠ 1 := fun h => hp1 (ψ.injective (hq.trans (h.trans (map_one ψ).symm)))
  have hqt' : q ≠ t := fun h =>
    hpt ((hp.symm.trans (congrArg ψ h.symm)).trans hqt)
  have hN : t * p * q ∈ U := by
    apply hfixψ _ (mul_mem (mul_mem htE hpE) hqE)
    rw [map_mul, map_mul, hp, hq, hqt, mul_assoc t p q]
    exact (hcomm t htE (p * q) (mul_mem hpE hqE)).symm
  have hclaim : ∃ z w : G, P z ∧ P w ∧ z ∈ U ∧ z ≠ 1 ∧ w ∈ E ∧ w ∉ U ∧ w ≠ t := by
    by_cases hpU : p ∈ U <;> by_cases hqU : q ∈ U
    · exfalso
      apply htU
      have : t = (t * p * q) * q⁻¹ * p⁻¹ := by group
      rw [this]
      exact mul_mem (mul_mem hN (inv_mem hqU)) (inv_mem hpU)
    · exact ⟨p, q, hPp, hPq, hpU, hp1, hqE, hqU, hqt'⟩
    · exact ⟨q, p, hPq, hPp, hqU, hq1, hpE, hpU, hpt⟩
    · exfalso
      have ha := inv_mul_mem_of_index_two hU hE8 hU4 htE htU hpE hpU
      have hb := inv_mul_mem_of_index_two hU hE8 hU4 htE htU hqE hqU
      obtain ⟨a, hadef⟩ : ∃ a, a = t⁻¹ * p := ⟨_, rfl⟩
      obtain ⟨b, hbdef⟩ : ∃ b, b = t⁻¹ * q := ⟨_, rfl⟩
      rw [← hadef] at ha
      rw [← hbdef] at hb
      have hpa : p = t * a := by rw [hadef]; group
      have hqb : q = t * b := by rw [hbdef]; group
      have hmain : t * p * q = t * (a * b) := by
        rw [hpa, hqb]
        calc t * (t * a) * (t * b) = (t * t) * a * (t * b) := by group
          _ = a * (t * b) := by rw [hE2 t htE, one_mul]
          _ = (a * t) * b := by group
          _ = t * (a * b) := by rw [hcomm a (hU ha) t htE]; group
      rw [hmain] at hN
      apply htU
      have : t = (t * (a * b)) * (a * b)⁻¹ := by group
      rw [this]
      exact mul_mem hN (inv_mem (mul_mem ha hb))
  obtain ⟨z, w, hPz, hPw, hzU, hz1, hwE, hwU, hwt⟩ := hclaim
  intro e he he1
  by_cases heU : e ∈ U
  · rcases eq_orbit_of_four hU4 φ hφ3 hφU hφx hzU hz1 heU he1 with h | h | h
    · rw [h]; exact hPz
    · rw [h]; exact hPφ _ hPz
    · rw [h]; exact hPφ _ (hPφ _ hPz)
  · by_cases het : e = t
    · rw [het]; exact ht
    · have ha := inv_mul_mem_of_index_two hU hE8 hU4 htE htU hwE hwU
      have hb := inv_mul_mem_of_index_two hU hE8 hU4 htE htU he heU
      have ha1 : t⁻¹ * w ≠ 1 := fun h => hwt (inv_mul_eq_one.mp h).symm
      have hb1 : t⁻¹ * e ≠ 1 := fun h => het (inv_mul_eq_one.mp h).symm
      have hφmul : ∀ x, φ (t * x) = t * φ x := fun x => by rw [map_mul, hφt]
      have hew : e = t * (t⁻¹ * e) := by group
      have hww : w = t * (t⁻¹ * w) := by group
      rcases eq_orbit_of_four hU4 φ hφ3 hφU hφx ha ha1 hb hb1 with h | h | h
      · rw [hew, h, ← hww]; exact hPw
      · rw [hew, h, ← hφmul, ← hww]; exact hPφ _ hPw
      · rw [hew, h, ← hφmul, ← hφmul, ← hww]; exact hPφ _ (hPφ _ hPw)

end Fano

theorem fano_transitive {G : Type*} [Group G] (E U U₁ : Subgroup G) (t u r r₁ : G)
    (hE8 : Nat.card E = 8) (hE2 : ∀ x ∈ E, x * x = 1) (hU : U ≤ E) (hU4 : Nat.card U = 4)
    (hU₁ : U₁ ≤ E) (hU₁4 : Nat.card U₁ = 4) (htE : t ∈ E) (htU : t ∉ U) (huU : u ∈ U)
    (huU₁ : u ∉ U₁) (hrU : r ∈ normalizer (U : Set G)) (hrt : r * t = t * r)
    (hr3 : orderOf r = 3) (hrx : ∃ x ∈ U, r * x * r⁻¹ ≠ x)
    (hr₁U : r₁ ∈ normalizer (U₁ : Set G)) (hr₁u : r₁ * u = u * r₁)
    (hr₁3 : orderOf r₁ = 3) (hr₁x : ∃ x ∈ U₁, r₁ * x * r₁⁻¹ ≠ x) :
    ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
      ∃ y ∈ Subgroup.closure ({r, r₁} : Set G), y * e * y⁻¹ = e' := by
  have hr3' : r ^ 3 = 1 := hr3 ▸ pow_orderOf_eq_one r
  have hr₁3' : r₁ ^ 3 = 1 := hr₁3 ▸ pow_orderOf_eq_one r₁
  have hcube : ∀ (g x : G), g ^ 3 = 1 →
      g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
    intro g x hg
    have hg' : g * g * g = 1 := by rw [← pow_three']; exact hg
    calc g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * x * (g * g * g)⁻¹ := by group
      _ = x := by rw [hg']; simp
  have hcore := Fano.pred_of_invariant E U U₁ t u (MulAut.conj r) (MulAut.conj r₁)
    (fun x => ∃ y ∈ Subgroup.closure ({r, r₁} : Set G), y * t * y⁻¹ = x)
    hE8 hE2 hU hU4 hU₁ hU₁4 htE htU huU huU₁
    (fun x => by simpa only [MulAut.conj_apply] using hcube r x hr3')
    (fun x hx => by
      have := (Subgroup.mem_set_normalizer_iff.mp hrU x).mp hx
      simpa only [MulAut.conj_apply, SetLike.mem_coe] using this)
    (by simp only [MulAut.conj_apply]; rw [hrt]; group)
    (by simpa only [MulAut.conj_apply] using hrx)
    (fun x => by simpa only [MulAut.conj_apply] using hcube r₁ x hr₁3')
    (fun x hx => by
      have := (Subgroup.mem_set_normalizer_iff.mp hr₁U x).mp hx
      simpa only [MulAut.conj_apply, SetLike.mem_coe] using this)
    (by simp only [MulAut.conj_apply]; rw [hr₁u]; group)
    (by simpa only [MulAut.conj_apply] using hr₁x)
    ⟨1, one_mem _, by simp⟩
    (fun x ⟨y, hy, hyx⟩ => ⟨r * y, mul_mem (Subgroup.subset_closure (Set.mem_insert _ _)) hy, by
      rw [← hyx]; simp only [MulAut.conj_apply]; group⟩)
    (fun x ⟨y, hy, hyx⟩ => ⟨r₁ * y, mul_mem (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hy, by
      rw [← hyx]; simp only [MulAut.conj_apply]; group⟩)
  intro e he he1 e' he' he'1
  obtain ⟨y, hy, rfl⟩ := hcore e he he1
  obtain ⟨y', hy', rfl⟩ := hcore e' he' he'1
  exact ⟨y' * y⁻¹, mul_mem hy' (inv_mem hy), by group⟩

end CFSG.EvenSporadicStandard.RuStd.S2

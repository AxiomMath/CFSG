module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Glue1
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Ctx
public import CFSG.GH74.Uniqueness.SU.SU1Graph

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

section Quat

theorem quat_pow_eq_one {m : ℕ} [NeZero m] (hm : 2 ∣ m) (x : QuaternionGroup m) :
    x ^ (2 * m) = 1 := by
  cases x with
  | a i =>
    have h : orderOf (QuaternionGroup.a i : QuaternionGroup m) ∣ 2 * m := by
      rw [QuaternionGroup.orderOf_a]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
    exact orderOf_dvd_iff_pow_eq_one.1 h
  | xa i =>
    have h4 : orderOf (QuaternionGroup.xa i : QuaternionGroup m) = 4 := QuaternionGroup.orderOf_xa i
    have : 4 ∣ 2 * m := by
      obtain ⟨k, hk⟩ := hm
      exact ⟨k, by omega⟩
    exact orderOf_dvd_iff_pow_eq_one.1 (h4 ▸ this)

variable {G : Type} [Group G]

theorem P_exp_of_quat {Y : Subgroup G} {n : ℕ} (hY : IVK.IsQuaternionTwoGroup ↥Y n) :
    ∀ p ∈ Y, p ^ (Nat.card ↥Y / 2) = 1 := by
  obtain ⟨hn, ⟨e⟩⟩ := hY
  have hm2 : 2 ≤ 2 ^ (n - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hdvd : 2 ∣ 2 ^ (n - 2) := dvd_pow_self 2 (by omega)
  have hcard : Nat.card ↥Y = 4 * 2 ^ (n - 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  intro p hp
  have h1 : (⟨p, hp⟩ : ↥Y) ^ (2 * 2 ^ (n - 2)) = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact quat_pow_eq_one hdvd _
  have h2 : Nat.card ↥Y / 2 = 2 * 2 ^ (n - 2) := by omega
  rw [h2]
  simpa using congrArg Subtype.val h1

end Quat

section Rank

variable {G : Type} [Group G] [Finite G]

theorem nonempty_of_pos_sSup' {s : Set ℕ} (h : 0 < sSup s) : s.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne] at h
  simp at h

omit [Finite G] in
theorem pgroup_of_sq_one {E : Subgroup G} (hE : ∀ a ∈ E, a * a = 1) : IsPGroup 2 ↥E := by
  refine IsPGroup.iff_orderOf.2 (fun g => ?_)
  have hg : (g : ↥E) ^ 2 = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hE g g.2
  have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

theorem exists_elem_of_pRank {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H]
    (h : 1 ≤ pRank p H) : ∃ A : Subgroup H, IsElementaryAbelian p A ∧ Nat.card A = p ^ pRank p H := by
  have hne : {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian p A ∧ Nat.card A = p ^ r}.Nonempty :=
    nonempty_of_pos_sSup' (by unfold pRank at h; omega)
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian p A ∧ Nat.card A = p ^ r} :=
    ⟨Nat.card H, by
      rintro r ⟨B, -, hB⟩
      calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
        _ = Nat.card B := hB.symm
        _ ≤ Nat.card H := Subgroup.card_le_card_group B⟩
  exact Nat.sSup_mem hne hbdd

end Rank

namespace Std4r1

variable {G : Type} [Group G] [Finite G] {z : G} {S K F : Subgroup G}

theorem P_quat (h : Std4r1 G z S K F) (hq : II4_4_quat) :
    ∃ n, IVK.IsQuaternionTwoGroup ↥(S ⊓ K) n :=
  hq G h.simple z h.orderOf_z S K h.sylow h.comp_isPCompIn h.comp_pRank

theorem hasE8 (h : Std4r1 G z S K F) : R1.HasE8 S := by
  have hrank : 1 ≤ pRank 2 G := le_trans (by norm_num) h.rank
  obtain ⟨E₀, hE₀, hcard⟩ := exists_elem_of_pRank (by norm_num) hrank
  have hE₀2 : ∀ a ∈ E₀, a * a = 1 := by
    intro a ha
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E₀) a ha
    simpa [pow_two] using this
  have hE₀p : IsPGroup 2 ↥E₀ := pgroup_of_sq_one hE₀2
  obtain ⟨S₀, hS₀, hES₀⟩ := M.exists_syl2In_ge hE₀p (le_top : E₀ ≤ ⊤)
  obtain ⟨c, -, hc⟩ := h.S_top.exists_conj hS₀
  refine ⟨M.cj E₀ c⁻¹, ?_, ?_, ?_⟩
  · intro x hx
    have h1 : c⁻¹ * x * c ∈ E₀ := by
      have := M.mem_cj.1 hx
      simpa using this
    have h2 : c⁻¹ * x * c ∈ S₀ := hES₀ h1
    rw [hc] at h2
    have h3 := M.mem_cj.1 h2
    have e : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e] at h3
  · intro a ha
    have h1 : c⁻¹ * a * c ∈ E₀ := by
      have := M.mem_cj.1 ha
      simpa using this
    have h2 := hE₀2 _ h1
    calc a * a = c * ((c⁻¹ * a * c) * (c⁻¹ * a * c)) * c⁻¹ := by group
      _ = 1 := by rw [h2]; group
  · rw [M.cj_card, hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ pRank 2 G := Nat.pow_le_pow_right (by norm_num) h.rank

theorem cent_rank (h : Std4r1 G z S K F) {U : Subgroup G} (hUS : U ≤ S) (hU2 : ∀ a ∈ U, a * a = 1)
    (hU4 : Nat.card ↥U = 4) (hUn : ∀ s ∈ S, ∀ v ∈ U, s * v * s⁻¹ ∈ U) :
    ∃ E : Subgroup G, E ≤ S ∧ (∀ a ∈ E, a * a = 1) ∧ 8 ≤ Nat.card ↥E ∧
      ∀ e ∈ E, ∀ v ∈ U, e * v = v * e := by
  obtain ⟨E₁, hE₁S, hE₁2, hE₁8⟩ := h.hasE8
  have hel : ∀ {E : Subgroup G}, (∀ a ∈ E, a * a = 1) → Open.IsElemAbelian 2 E := by
    intro E hE
    refine ⟨⟨⟨fun a b => Subtype.ext (B.comm_of_forall_sq hE a.2 b.2)⟩⟩, fun x hx => ?_⟩
    simpa [pow_two] using hE x hx
  have hUel : Open.IsElemAbelian 2 U := hel hU2
  have hnormU : S ≤ normalizer (U : Set G) := fun s hs =>
    M.mem_normalizer_of_both (fun x hx => hUn s hs x hx) (fun x hx => by
      have := hUn s⁻¹ (S.inv_mem hs) x hx
      simpa using this)
  have hNE : CFSG.GH74.Uniqueness.SU.SU1.IsNormalEp2 2 S U :=
    ⟨hUS, hnormU, hUel, by rw [hU4]; norm_num⟩
  obtain ⟨-, -, hrank⟩ := CFSG.GH74.Uniqueness.SU.SU1.ig10_20_ii Nat.prime_two h.S_pgroup hNE
  have hbdd : ∀ H : Subgroup G, BddAbove
      {k : ℕ | ∃ E : Subgroup G, E ≤ H ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    intro H
    refine ⟨Nat.card G, ?_⟩
    rintro r ⟨B, -, -, hB⟩
    calc r ≤ 2 ^ r := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group B
  have hge : 3 ≤ Open.pRank 2 S := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (pgroup_of_sq_one hE₁2)
    have hk3 : 3 ≤ k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact le_trans hk3 (le_csSup (hbdd S) ⟨E₁, hE₁S, hel hE₁2, hk⟩)
  have hne : {k : ℕ | ∃ E : Subgroup G, E ≤ centralizer (U : Set G) ⊓ S ∧ Open.IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ k}.Nonempty :=
    nonempty_of_pos_sSup' (by unfold Open.pRank at hrank hge; omega)
  obtain ⟨E, hEle, hEel, hEcard⟩ := Nat.sSup_mem hne (hbdd _)
  refine ⟨E, fun x hx => (hEle hx).2, fun a ha => ?_, ?_, fun e he v hv => ?_⟩
  · simpa [pow_two] using hEel.2 a ha
  · have h1 : 2 ^ 3 ≤ 2 ^ (sSup {k : ℕ | ∃ E : Subgroup G, E ≤ centralizer (U : Set G) ⊓ S ∧
        Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}) :=
      Nat.pow_le_pow_right (by norm_num) (by unfold Open.pRank at hrank hge; omega)
    rw [hEcard]
    omega
  · exact (Subgroup.mem_centralizer_iff.1 (hEle he).1 v hv).symm

end Std4r1

end CFSG.GH74.GLS.Stage1.Thm3.Sec6

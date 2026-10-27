module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAAltPerm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltPerm
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltCore CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.KAAlt

section Core

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem core_card_bounds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : Perm α} (hy : y * y = 1)
    {P : Subgroup (Perm α)} (hPp : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hfix : ∀ x ∈ P, ∀ a, y a ≠ a → x a = a)
    (hcomm : ∀ e ∈ P, e * y = y * e)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P : Set (Perm α))) :
    3 ≤ Nat.card {a : α // y a = a} ∧ Nat.card {a : α // y a = a} ≤ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hyy : ∀ w, y (y w) = w := yy hy
  let Φ := {a : α // y a = a}
  let ι : Perm Φ →* Perm α := Equiv.Perm.ofSubtype
  have hι : Function.Injective ι := Equiv.Perm.ofSubtype_injective
  have hPι : P ≤ ι.range := by
    intro x hx
    have hyx : ∀ w, x (y w) = y (x w) := fun w => by
      have := congrArg (fun f : Perm α => f w) (hcomm x hx)
      simpa [Perm.mul_apply] using this
    have h1 : ∀ w, y (x w) = x w ↔ y w = w := by
      intro w
      rw [← hyx]
      exact ⟨fun h => x.injective h, fun h => by rw [h]⟩
    refine ⟨x.subtypePerm h1, Equiv.Perm.ofSubtype_subtypePerm h1 fun w hw => ?_⟩
    by_contra hyw
    exact hw (hfix x hx w hyw)
  let P' : Subgroup (Perm Φ) := P.comap ι
  have hmap : P'.map ι = P := Subgroup.map_comap_eq_self hPι
  have hP'p : IsPGroup p ↥P' := hPp.comap_of_injective ι hι
  have hP'1 : P' ≠ ⊥ := by
    intro h
    apply hP1
    rw [← hmap, h, Subgroup.map_bot]
  have hcommι : ∀ v' : Perm Φ, ι v' * y = y * ι v' := by
    intro v'
    ext w
    simp only [Perm.mul_apply]
    by_cases hw : y w = w
    · have h1 : ι v' w = ↑(v' ⟨w, hw⟩) := Equiv.Perm.ofSubtype_apply_of_mem v' hw
      rw [hw, h1]
      exact (v' ⟨w, hw⟩).2.symm
    · have h1 : ι v' w = w := Equiv.Perm.ofSubtype_apply_of_not_mem v' hw
      have h2 : ι v' (y w) = y w := by
        refine Equiv.Perm.ofSubtype_apply_of_not_mem v' ?_
        intro h
        apply hw
        rw [hyy] at h
        exact h.symm
      rw [h1, h2]
  have hDι : ∀ v' : Perm Φ, Odd (orderOf v') → v' ∈ normalizer (P' : Set (Perm Φ)) := by
    intro v' hv'
    have hv := hD (ι v') (by rw [orderOf_injective ι hι]; exact hv') (hcommι v')
    rw [Subgroup.mem_normalizer_iff] at hv ⊢
    intro h
    show ι h ∈ P ↔ ι (v' * h * v'⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact hv _
  have hoddP' : ∀ x ∈ P', Odd (orderOf x) := by
    intro x hx
    have := odd_orderOf_of_mem_pGroup hp hp2 hPp (show ι x ∈ P from hx)
    rwa [orderOf_injective ι hι] at this
  have h3 : Nat.card (Perm Φ) = (Nat.card Φ).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.card_eq_fintype_card]
  constructor
  · by_contra hlt
    push Not at hlt
    obtain ⟨j, hj⟩ := hP'p.exists_card_eq
    have h1 : Nat.card ↥P' ∣ Nat.card (Perm Φ) := Subgroup.card_subgroup_dvd_card P'
    have hle2 : Nat.card Φ ≤ 2 := by
      change Nat.card Φ < 3 at hlt
      omega
    have h2 : (Nat.card Φ).factorial ∣ 2 :=
      (Nat.factorial_dvd_factorial hle2).trans (by decide)
    have h4 : p ^ j ∣ 2 := by
      rw [← hj]
      exact h1.trans (h3 ▸ h2)
    have hcop : Nat.Coprime (p ^ j) 2 := by
      have : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 hp2
      exact Nat.Coprime.pow_left j this
    have h5 : p ^ j = 1 := Nat.Coprime.eq_one_of_dvd hcop h4
    apply hP'1
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hj, h5])
  · by_contra hlt
    push Not at hlt
    have hm : 5 ≤ Nat.card Φ := hlt
    have : Nontrivial Φ := by
      have : 1 < Nat.card Φ := by omega
      exact Finite.one_lt_card_iff_nontrivial.1 this
    have hAnorm : alternatingGroup Φ ≤ normalizer (P' : Set (Perm Φ)) := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro σ hσ
      exact hDι σ (by rw [hσ.orderOf]; exact (by decide : Odd 3))
    have hP'A : P' ≤ alternatingGroup Φ := fun x hx =>
      Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_odd' (hoddP' x hx))
    let N : Subgroup ↥(alternatingGroup Φ) := P'.subgroupOf (alternatingGroup Φ)
    have hN : N.Normal := by
      refine ⟨fun x hx g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      have := (Subgroup.mem_normalizer_iff.1 (hAnorm g.2) (x : Perm Φ)).1 hx
      simpa using this
    have hsimple : IsSimpleGroup ↥(alternatingGroup Φ) := alternatingGroup.isSimpleGroup hm
    rcases hsimple.eq_bot_or_eq_top_of_normal N with h | h
    · apply hP'1
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hP'A hx⟩ : ↥(alternatingGroup Φ)) ∈ N := Subgroup.mem_subgroupOf.2 hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · have hNp : IsPGroup p ↥N := hP'p.comap_of_injective (alternatingGroup Φ).subtype
        (alternatingGroup Φ).subtype_injective
      obtain ⟨j, hj⟩ := hNp.exists_card_eq
      have hcard : Nat.card ↥(alternatingGroup Φ) = p ^ j := by
        rw [← hj, h]
        exact (Nat.card_congr (Subgroup.topEquiv (G := ↥(alternatingGroup Φ))).toEquiv).symm
      have h2 := two_mul_nat_card_alternatingGroup (α := Φ)
      have h4 : 4 ∣ (Nat.card Φ).factorial := Nat.dvd_factorial (by norm_num) (by omega)
      have h5 : Even (Nat.card ↥(alternatingGroup Φ)) := by
        obtain ⟨t, ht⟩ := h4
        exact ⟨t, by omega⟩
      have h6 : Odd (p ^ j) := (hp.odd_of_ne_two hp2).pow
      rw [← hcard] at h6
      exact (Nat.not_even_iff_odd.2 h6) h5

theorem card_fix_bounds {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : Perm α} (hy : y * y = 1)
    {P : Subgroup (Perm α)} (hPp : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hcomm : ∀ e ∈ P, e * y = y * e)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P : Set (Perm α))) :
    3 ≤ Nat.card {a : α // y a = a} ∧ Nat.card {a : α // y a = a} ≤ 4 :=
  core_card_bounds hp hp2 hy hPp hP1 (fix_support hp hp2 hy hPp hcomm hD) hcomm hD

theorem sign_eq_one_of_seven (hc : Fintype.card α = 7) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {y : Perm α} (hy : y * y = 1) {P : Subgroup (Perm α)} (hPp : IsPGroup p ↥P) (hP1 : P ≠ ⊥)
    (hcomm : ∀ e ∈ P, e * y = y * e)
    (hD : ∀ v : Perm α, Odd (orderOf v) → v * y = y * v →
      v ∈ normalizer (P : Set (Perm α))) : Perm.sign y = 1 := by
  obtain ⟨h3, h4⟩ := card_fix_bounds hp hp2 hy hPp hP1 hcomm hD
  have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hy
  have hN : Nat.card {a : α // y a = a} = y.supportᶜ.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext a
    simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod : y.supportᶜ.card ≡ Fintype.card α [MOD 2] :=
    card_compl_support_modEq (p := 2) (n := 1) (σ := y) (by simpa using hy2)
  unfold Nat.ModEq at hmod
  rw [hc] at hmod
  have hN3 : Nat.card {a : α // y a = a} = 3 := by omega
  have hfp : Fintype.card (Function.fixedPoints y) = 3 := by
    rw [← hN3, Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun a => Iff.rfl)
  rw [sign_of_pow_two_eq_one hy2, hfp, hc]
  decide

end Core

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2

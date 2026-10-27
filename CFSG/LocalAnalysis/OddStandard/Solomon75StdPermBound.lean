module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdPermCycle
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS

theorem le_of_factorial_le_two_mul {f c : ℕ} (hf : 3 ≤ f) (h : f.factorial ≤ 2 * c.factorial) :
    f ≤ c := by
  by_contra hlt
  push Not at hlt
  have h1 : c.factorial ≤ (f - 1).factorial := Nat.factorial_le (by omega)
  have h2 : f.factorial = f * (f - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
  have h3 : 0 < (f - 1).factorial := Nat.factorial_pos _
  have h4 : 3 * (f - 1).factorial ≤ f * (f - 1).factorial := Nat.mul_le_mul_right _ hf
  omega

theorem card_le_factorial_of_ker_le {H A Q : Type*} [Group H] [Group A] [Finite Q]
    (θ : H →* A) (hθ : Function.Surjective θ) (Φ : H →* Perm Q) (hle : Φ.ker ≤ θ.ker) :
    Nat.card A ≤ (Nat.card Q).factorial := by
  have h1 : θ.ker.index = Nat.card A := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hθ, Subgroup.card_top]
  have h2 : Φ.ker.index = Nat.card Φ.range := Subgroup.index_ker Φ
  have h3 : Nat.card Φ.range ≤ (Nat.card Q).factorial := by
    rw [← Nat.card_perm]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have h4 : 0 < Φ.ker.index := by
    rw [h2]
    exact Nat.card_pos
  have h5 : θ.ker.index ≤ Φ.ker.index := Nat.le_of_dvd h4 (Subgroup.index_dvd_of_le hle)
  omega

theorem card_alternatingGroup_mul_two {β : Type*} [Fintype β] [DecidableEq β]
    (hβ : 2 ≤ Nat.card β) : Nat.card (alternatingGroup β) * 2 = (Nat.card β).factorial := by
  have : Nontrivial β := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  rw [mul_comm, two_mul_nat_card_alternatingGroup, Nat.card_perm]

theorem ker_le_or_ker_le_of_solvable_inf {H A : Type*} [Group H] [Group A] [IsSimpleGroup A]
    (hperf : commutator A = ⊤) (hnt : Nontrivial A) (θ : H →* A) (hθ : Function.Surjective θ)
    (N₁ N₂ : Subgroup H) [N₁.Normal] [N₂.Normal] (hs : Group.IsSolvable ↥(N₁ ⊓ N₂)) :
    N₁ ≤ θ.ker ∨ N₂ ≤ θ.ker := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have top_of : ∀ N : Subgroup H, N.Normal → ¬ N ≤ θ.ker → N.map θ = ⊤ := by
    intro N hN hN'
    have : (N.map θ).Normal := hN.map θ hθ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map θ) with h | h
    · exact absurd ((Subgroup.map_eq_bot_iff N).1 h) hN'
    · exact h
  have t1 := top_of N₁ inferInstance h1
  have t2 := top_of N₂ inferInstance h2
  have hc : (⁅N₁, N₂⁆).map θ = ⊤ := by
    rw [Subgroup.map_commutator, t1, t2]
    exact hperf
  have hle : (⁅N₁, N₂⁆).map θ ≤ (N₁ ⊓ N₂).map θ :=
    Subgroup.map_mono (Subgroup.commutator_le_inf N₁ N₂)
  rw [hc, top_le_iff] at hle
  let g : ↥(N₁ ⊓ N₂) →* A := θ.comp (N₁ ⊓ N₂).subtype
  have hg : Function.Surjective g := by
    intro a
    have : a ∈ (N₁ ⊓ N₂).map θ := by rw [hle]; exact Subgroup.mem_top a
    obtain ⟨x, hx, hxa⟩ := this
    exact ⟨⟨x, hx⟩, hxa⟩
  have : Group.IsSolvable ↥(N₁ ⊓ N₂) := hs
  have : Group.IsSolvable A := Group.isSolvable_of_surjective hg
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial A
  rw [hperf] at this
  exact lt_irrefl _ this

section DoubleCover

variable {D : Type} [Group D] {f : ℕ}

theorem normal_le_center_or_eq_top_of_doubleCover (hD : IsDoubleCoverOfAlt D f) (N : Subgroup D)
    [N.Normal] : N ≤ center D ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hD.1
  let q := QuotientGroup.mk' (center D)
  have hnormal : (N.map q).Normal := Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map q) with hbot | htop
  · left
    have hker : N ≤ q.ker := (Subgroup.map_eq_bot_iff N).1 hbot
    simpa only [q, QuotientGroup.ker_mk'] using hker
  · right
    have hsup : N ⊔ center D = ⊤ := by
      have hcomap := Subgroup.comap_map_eq q N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator D ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf.commutator_eq_top] at hderived
    exact top_unique hderived

theorem card_doubleCover (hf : 2 ≤ f) (hD : IsDoubleCoverOfAlt D f) :
    Nat.card D = f.factorial := by
  obtain ⟨-, hc, ⟨e⟩⟩ := hD
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center D)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  have h2 := card_alternatingGroup_mul_two (β := Fin f) (by simpa using hf)
  rw [Nat.card_eq_fintype_card (α := Fin f), Fintype.card_fin] at h2
  rw [h1, h2]

end DoubleCover

section Bounds

variable {N : Type*} [Fintype N] [DecidableEq N] {π : Perm N}

theorem exists_pow_two_apply_ne (hπ2 : π ^ 2 ≠ 1) : ∃ x, (π ^ 2) x ≠ x := by
  by_contra hcon
  push Not at hcon
  exact hπ2 (Equiv.ext hcon)

theorem four_mul_le_card_support_sq_of_doubleCover {f : ℕ} (hf : 5 ≤ f) {D : Type} [Group D]
    (hD : IsDoubleCoverOfAlt D f) (hπ : π ^ 4 = 1) (ι : D →* Perm N)
    (hι : ∀ d, ι d * π = π * ι d) {z : D} (hιz : ι z = π ^ 2) (hπ2 : π ^ 2 ≠ 1) :
    4 * f ≤ (π ^ 2).support.card := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_pow_two_apply_ne hπ2
  have hcard : Nat.card D = f.factorial := card_doubleCover (by omega) hD
  have hfin : Finite D := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (Nat.factorial_pos f).ne')
  have hne : (actT ι hι).ker ≠ ⊤ := by
    intro htop
    have hM : ⁅(⊤ : Subgroup D), ⊤⁆ ≤ (resT ι hι).ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact commute_resT_of_mem_ker_actT ι hι (htop ▸ Subgroup.mem_top a)
        (htop ▸ Subgroup.mem_top b)
    have hperf : ⁅(⊤ : Subgroup D), ⊤⁆ = ⊤ := hD.1.1.commutator_eq_top
    rw [hperf] at hM
    have hz1 : resT ι hι z = 1 := MonoidHom.mem_ker.1 (hM (Subgroup.mem_top z))
    have h2 := congrArg (fun e : Perm {x : N // (π ^ 2) x ≠ x} => (e ⟨x₀, hx₀⟩ : N)) hz1
    simp only [coe_resT_apply, hιz, Perm.coe_one, id_eq] at h2
    exact hx₀ h2
  have hle : (actT ι hι).ker ≤ center D :=
    (normal_le_center_or_eq_top_of_doubleCover hD _).resolve_right hne
  have hNT : Nat.card (actT ι hι).ker ≤ 2 := by
    calc Nat.card (actT ι hι).ker ≤ Nat.card (center D) := Subgroup.card_le_of_le hle
      _ = 2 := hD.2.1
  have hidx : (actT ι hι).ker.index ≤ (Nat.card (CycT π)).factorial := by
    rw [Subgroup.index_ker, ← Nat.card_perm]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have h1 : f.factorial ≤ 2 * (Nat.card (CycT π)).factorial := by
    calc f.factorial = Nat.card D := hcard.symm
      _ = (actT ι hι).ker.index * Nat.card (actT ι hι).ker :=
          (Subgroup.index_mul_card _).symm
      _ ≤ (Nat.card (CycT π)).factorial * 2 := Nat.mul_le_mul hidx hNT
      _ = 2 * (Nat.card (CycT π)).factorial := mul_comm _ _
  have h2 := le_of_factorial_le_two_mul (by omega) h1
  have h3 := four_mul_card_CycT_le hπ
  omega

theorem twelve_le_card_support_sq {D : Type*} [Group D]
    (hgen : Subgroup.closure {x : D | Odd (orderOf x)} = ⊤) (hπ : π ^ 4 = 1) (ι : D →* Perm N)
    (hι : ∀ d, ι d * π = π * ι d) {z : D} (hιz : ι z = π ^ 2) (hπ2 : π ^ 2 ≠ 1) :
    12 ≤ (π ^ 2).support.card := by
  classical
  obtain ⟨x₀, hx₀⟩ := exists_pow_two_apply_ne hπ2
  by_contra hlt
  push Not at hlt
  have hCT : Nat.card (CycT π) ≤ 2 := by
    have := four_mul_card_CycT_le hπ
    omega
  have hodd : ∀ x : D, Odd (orderOf x) → resT ι hι x = 1 := by
    intro x hx
    have hact : actT ι hι x = 1 := by
      have h1 : orderOf (actT ι hι x) ∣ orderOf x := orderOf_map_dvd _ _
      have h2 : orderOf (actT ι hι x) ∣ (Nat.card (CycT π)).factorial := by
        rw [← Nat.card_perm]
        exact _root_.orderOf_dvd_natCard _
      have h3 : (Nat.card (CycT π)).factorial ∣ 2 := by
        generalize Nat.card (CycT π) = c at hCT ⊢
        interval_cases c <;> decide
      have h4 : orderOf (actT ι hι x) ∣ 2 := h2.trans h3
      rcases (Nat.dvd_prime Nat.prime_two).1 h4 with h5 | h5
      · exact orderOf_eq_one_iff.1 h5
      · exfalso
        rw [h5] at h1
        obtain ⟨k, hk⟩ := h1
        obtain ⟨m, hm⟩ := hx
        omega
    have hker : x ∈ (actT ι hι).ker := hact
    have h1 : orderOf (resT ι hι x) ∣ orderOf x := orderOf_map_dvd _ _
    have h4 : orderOf (resT ι hι x) ∣ 4 :=
      orderOf_dvd_of_pow_eq_one (resT_pow_four_of_mem_ker_actT hπ ι hι hker)
    have hcop : Nat.Coprime 4 (orderOf x) := by
      have : Nat.Coprime 2 (orderOf x) := Nat.coprime_two_left.2 hx
      simpa using Nat.Coprime.pow_left 2 this
    have h5 : orderOf (resT ι hι x) ∣ Nat.gcd 4 (orderOf x) := Nat.dvd_gcd h4 h1
    rw [hcop] at h5
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)
  have hle : Subgroup.closure {x : D | Odd (orderOf x)} ≤ (resT ι hι).ker := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hodd x hx
  rw [hgen] at hle
  have hz1 : resT ι hι z = 1 := MonoidHom.mem_ker.1 (hle (Subgroup.mem_top z))
  have h2 := congrArg (fun e : Perm {x : N // (π ^ 2) x ≠ x} => (e ⟨x₀, hx₀⟩ : N)) hz1
  simp only [coe_resT_apply, hιz, Perm.coe_one, id_eq] at h2
  exact hx₀ h2

theorem card_le_max_of_surjective_alternating {β : Type*} [Fintype β] [DecidableEq β]
    (hβ : 5 ≤ Nat.card β) {H : Type*} [Group H] (θ : H →* alternatingGroup β)
    (hθ : Function.Surjective θ) (hπ : π ^ 4 = 1) (ι : H →* Perm N)
    (hι : ∀ h, ι h * π = π * ι h) (hker : Group.IsSolvable ι.ker) :
    Nat.card β ≤ max ((π ^ 2).support.card / 4) (Fintype.card N - (π ^ 2).support.card) := by
  classical
  have hsimple : IsSimpleGroup (alternatingGroup β) := alternatingGroup.isSimpleGroup hβ
  have hperf : commutator (alternatingGroup β) = ⊤ := commutator_alternatingGroup_eq_top hβ
  have hnt : Nontrivial (alternatingGroup β) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  have hs : Group.IsSolvable ↥((actT ι hι).ker ⊓ (actF ι hι).ker) := by
    let g : ↥((actT ι hι).ker ⊓ (actF ι hι).ker) →* Perm N :=
      ι.comp (Subgroup.subtype _)
    have hgker : Group.IsSolvable g.ker := by
      let e : g.ker →* ι.ker :=
        (((actT ι hι).ker ⊓ (actF ι hι).ker).subtype.comp g.ker.subtype).codRestrict ι.ker
          (fun x => x.2)
      refine Group.isSolvable_of_isSolvable_injective (f := e) ?_
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ι.ker => (x : H)) hab
    have hgrange : Group.IsSolvable g.range := by
      refine Group.isSolvable_of_comm ?_
      rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      apply Subtype.ext
      exact commute_of_cycHom_eq_one ι hι (ker_actT_inf_ker_actF_le ι hι x.2)
        (ker_actT_inf_ker_actF_le ι hι y.2)
    refine Group.isSolvable_of_ker_le_range g.ker.subtype g.rangeRestrict ?_
    rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype]
  have hcases := ker_le_or_ker_le_of_solvable_inf hperf hnt θ hθ (actT ι hι).ker
    (actF ι hι).ker hs
  have hfac := card_alternatingGroup_mul_two (β := β) (by omega)
  rcases hcases with h1 | h2
  · have h3 := card_le_factorial_of_ker_le θ hθ (actT ι hι) h1
    have h4 : (Nat.card β).factorial ≤ 2 * (Nat.card (CycT π)).factorial := by omega
    have h5 := le_of_factorial_le_two_mul (by omega) h4
    have h6 := four_mul_card_CycT_le hπ
    refine le_max_of_le_left ?_
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    omega
  · have h3 := card_le_factorial_of_ker_le θ hθ (actF ι hι) h2
    have h4 : (Nat.card β).factorial ≤ 2 * (Nat.card ↥(CycT π)ᶜ).factorial := by omega
    have h5 := le_of_factorial_le_two_mul (by omega) h4
    have h6 := card_CycF_le (π := π)
    exact le_max_of_le_right (h5.trans h6)

end Bounds

end CFSG.OddStandard.Solomon75

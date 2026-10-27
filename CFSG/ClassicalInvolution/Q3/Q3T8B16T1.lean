module

public import CFSG.ClassicalInvolution.Q3.Q3T8B16
public import CFSG.ClassicalInvolution.Q3.Q3PPFundPSL3
public import CFSG.ClassicalInvolution.Q3.Q3T6CoreSec
public import CFSG.ClassicalInvolution.Q3.Q3T8M11

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Uniform CFSG.Blueprint
open scoped MatrixGroups

section Transport

theorem dich_transport {S Y : Type} [Group S] [Group Y] (ψ : S →* Y)
    (hψ : Function.Bijective ψ) {R : Subgroup S}
    (h : ∀ ρ : MulAut S, ρ * ρ = 1 → (∀ r ∈ R, ρ r = r) →
      ∃ k ∈ R, k * k = 1 ∧ ρ = MulAut.conj k)
    {u : Y} (hu : IsUniqueInvolution (R.map ψ) u) (β : MulAut Y) (hβ2 : β * β = 1)
    (hβ : ∀ x ∈ R.map ψ, β x = x) : β = 1 ∨ β = MulAut.conj u := by
  let e : S ≃* Y := MulEquiv.ofBijective ψ hψ
  have he : ∀ x, e x = ψ x := fun x => rfl
  have h2 : MulAut.congr e.symm β * MulAut.congr e.symm β = 1 := by
    rw [← map_mul, hβ2, map_one]
  have hfix : ∀ r ∈ R, MulAut.congr e.symm β r = r := by
    intro r hr
    have h1 : β (ψ r) = ψ r := hβ _ (Subgroup.mem_map_of_mem ψ hr)
    have h3 : MulAut.congr e.symm β r = e.symm (β (e r)) := by
      simp [MulAut.congr_apply]
    rw [h3, he, h1, ← he, MulEquiv.symm_apply_apply]
  obtain ⟨k, hkR, hk2, hρ⟩ := h _ h2 hfix
  have hback : MulAut.congr e (MulAut.congr e.symm β) = β := by
    ext y
    simp [MulAut.congr_apply]
  have hβk : β = MulAut.conj (e k) := by
    rw [← hback, hρ, Q3PP.congr_conj]
  have hmem : e k ∈ R.map ψ := ⟨k, hkR, rfl⟩
  have hsq : e k * e k = 1 := by rw [← map_mul, hk2, map_one]
  rcases hu.unique (e k) hmem hsq with h1 | h1
  · left
    rw [hβk, h1, map_one]
  · right
    rw [hβk, h1]

end Transport

section Four

theorem exists_orderOf_four_of_card_24 {H : Type} [Group H] (hcard : Nat.card H = 24) {u : H}
    (hu : ∀ y : H, y * y = 1 → y = 1 ∨ y = u) : ∃ x : H, orderOf x = 4 := by
  classical
  have hfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 (n := 3)
    (by rw [hcard]; norm_num)
  by_contra hno
  push Not at hno
  have hP2 : ∀ x ∈ P, x = 1 ∨ x = u := by
    intro x hxP
    have hdvd : orderOf x ∣ 2 ^ 3 := by
      have := Subgroup.orderOf_dvd_natCard P hxP
      rwa [hP] at this
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    interval_cases i
    · left
      exact orderOf_eq_one_iff.mp (by simpa using hord)
    · apply hu
      have h2 : x ^ 2 = 1 := by
        rw [← orderOf_dvd_iff_pow_eq_one, hord]
        norm_num
      rw [← pow_two]
      exact h2
    · exact absurd (by simpa using hord) (hno x)
    · exfalso
      have h8 : orderOf (x ^ 2) = 4 := by
        rw [orderOf_pow_of_dvd (by norm_num) (by rw [hord]; norm_num), hord]
        norm_num
      exact hno _ h8
  let f : P → Bool := fun x => decide ((x : H) = 1)
  have hf : Function.Injective f := by
    intro x y hxy
    have hiff : ((x : H) = 1 ↔ (y : H) = 1) := by
      have h := hxy
      simp only [f, decide_eq_decide] at h
      exact h
    apply Subtype.ext
    by_cases hx1 : (x : H) = 1
    · rw [hx1, hiff.mp hx1]
    · have hy1 : (y : H) ≠ 1 := fun hy1 => hx1 (hiff.mpr hy1)
      rw [(hP2 x x.2).resolve_left hx1, (hP2 y y.2).resolve_left hy1]
  have hle := Nat.card_le_card_of_injective f hf
  rw [hP] at hle
  simp at hle

theorem exists_orderOf_four_of_unique_involution {Y : Type} [Group Y] {J : Subgroup Y} {u : Y}
    (hu : IsUniqueInvolution J u) (hcard : Nat.card J = 24) : ∃ x ∈ J, orderOf x = 4 := by
  obtain ⟨x, hx⟩ := exists_orderOf_four_of_card_24 (H := J) hcard (u := ⟨u, hu.mem⟩) (by
    intro y hy
    rcases hu.unique (y : Y) y.2 (congrArg Subtype.val hy) with h | h
    · left
      exact Subtype.ext h
    · right
      exact Subtype.ext h)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

end Four

section SL3

theorem sl3_involutory_fixes {g₀ : SL(3, GaloisField 3 1)} (ρ : MulAut SL(3, GaloisField 3 1))
    (hρ2 : ρ * ρ = 1)
    (hρR : ∀ r ∈ conjSub g₀ (Q3PP.rootSL2₃ (GaloisField 3 1)), ρ r = r) :
    ∃ k ∈ conjSub g₀ (Q3PP.rootSL2₃ (GaloisField 3 1)), k * k = 1 ∧ ρ = MulAut.conj k := by
  rcases Q3PP.eq_one_or_conj_of_fixes_conjSub Q3PP.natCard_gf3 Q3PP.outOne_sl3_gf3 hρ2 hρR with
    h | ⟨s, hs2, hs1, hsρ⟩
  · exact ⟨1, Subgroup.one_mem _, mul_one 1, by rw [h, map_one]⟩
  · have hcomm : ∀ r ∈ Q3PP.rootSL2₃ (GaloisField 3 1),
        (g₀⁻¹ * s * g₀) * r = r * (g₀⁻¹ * s * g₀) := by
      intro r hr
      have h1 := hρR _ (conj_mem_conjSub hr)
      rw [hsρ, MulAut.conj_apply] at h1
      have h2 : s * (g₀ * r * g₀⁻¹) = (g₀ * r * g₀⁻¹) * s := by
        calc s * (g₀ * r * g₀⁻¹) = s * (g₀ * r * g₀⁻¹) * s⁻¹ * s := by group
          _ = (g₀ * r * g₀⁻¹) * s := by rw [h1]
      calc g₀⁻¹ * s * g₀ * r = g₀⁻¹ * (s * (g₀ * r * g₀⁻¹)) * g₀ := by group
        _ = g₀⁻¹ * ((g₀ * r * g₀⁻¹) * s) * g₀ := by rw [h2]
        _ = r * (g₀⁻¹ * s * g₀) := by group
    have hsq : (g₀⁻¹ * s * g₀) * (g₀⁻¹ * s * g₀) = 1 := by
      calc (g₀⁻¹ * s * g₀) * (g₀⁻¹ * s * g₀) = g₀⁻¹ * (s * s) * g₀ := by group
        _ = 1 := by rw [hs2]; group
    rcases Q3PP.eq_one_or_rootInv_of_commutes hcomm hsq with ht | ht
    · exfalso
      apply hs1
      have e : s = g₀ * (g₀⁻¹ * s * g₀) * g₀⁻¹ := by group
      rw [e, ht]
      group
    · refine ⟨s, ?_, hs2, hsρ⟩
      rw [mem_conjSub_iff, ht]
      exact Q3PP.rootInv₃_mem

end SL3

section M11

theorem m11_involutory_fixes {R : Subgroup ↥NativeSporadic.M11}
    {s : ↥NativeSporadic.M11} (hsR : s ∈ R) (hs : orderOf s = 4)
    (ρ : MulAut ↥NativeSporadic.M11) (hρ2 : ρ * ρ = 1) (hρR : ∀ r ∈ R, ρ r = r) :
    ∃ k ∈ R, k * k = 1 ∧ ρ = MulAut.conj k := by
  obtain ⟨k, rfl⟩ := Q3NM.m11_aut_inner ρ
  have hZ : Subgroup.center ↥NativeSporadic.M11 = ⊥ := Q3.center_m11_eq_bot Q3.m11Facts
  have hkk : k * k = 1 := by
    have h1 : MulAut.conj (k * k) = 1 := by rw [map_mul]; exact hρ2
    exact (Q3PP.conj_eq_one_iff_of_center_eq_bot hZ _).mp h1
  have hsk : s * k = k * s := by
    have h1 := hρR s hsR
    rw [MulAut.conj_apply] at h1
    calc s * k = (k * s * k⁻¹) * k := by rw [h1]
      _ = k * s := by group
  have hk4 : k ^ 4 = 1 := by
    have hk2 : k ^ 2 = 1 := by rw [pow_two]; exact hkk
    calc k ^ 4 = (k ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hk2, one_pow]
  have hkz : k ∈ Subgroup.zpowers s := m11_mem_zpowers_of_commute hs hsk hk4
  exact ⟨k, Subgroup.zpowers_le.mpr hsR hkz, hkk, rfl⟩

end M11

section Main


theorem invol_dich_proved : InvolDichSect := by
  intro Y _ Φ D hcase J' hJ' u hu β hβ2 hβ
  have hsurj : Function.Surjective (D.hom 0) := Q3T6.lieSystemDataU_surjective_hom D 0
  obtain ⟨i', R', hR', hJR'⟩ := D.fundamental J' hJ'
  have hi' : i' = 0 := Subsingleton.elim _ _
  subst hi'
  rcases hcase with hc | hc
  ·
    obtain ⟨e, he, hft, hadm, hc'⟩ := hc
    have he1 : e = 1 := by
      rcases he with h | ⟨h, -⟩
      · exact h
      · exact absurd h (by decide)
    subst he1
    obtain ⟨R'', hR'', hRR⟩ := exists_map_castHom hc' (D.hom 0) hR'
    have hJ : J' = R''.map (castHom hc' (D.hom 0)) := by rw [hRR, hJR']
    have hsurj' : Function.Surjective (castHom hc' (D.hom 0)) := by
      rw [← MonoidHom.range_eq_top, range_castHom, MonoidHom.range_eq_top]
      exact hsurj
    have hker := castHom_ker_le_center hc' _ (D.ker_le_center 0)
    have hZ : Subgroup.center SL(3, GaloisField 3 1) = ⊥ :=
      Q3PP.center_sl3_eq_bot Q3PP.natCard_gf3
    have hinj : Function.Injective (castHom hc' (D.hom 0)) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      exact hker.trans hZ.le
    have hRl := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 2)
      (F := GaloisField 3 1) (by norm_num) hR''
    obtain ⟨g₀, hg₀⟩ := (CFSG.ClassicalInvolution.Models.mem_longRootSet_iff
      (show 2 ≤ 3 by norm_num)).mp hRl
    refine dich_transport (castHom hc' (D.hom 0)) ⟨hinj, hsurj'⟩ (R := R'') ?_
      (hJ ▸ hu) β hβ2 (hJ ▸ hβ)
    intro ρ hρ2 hρR
    rw [hg₀] at hρR ⊢
    exact sl3_involutory_fixes ρ hρ2 hρR
  ·
    obtain ⟨R'', hR'', hRR⟩ := exists_map_castHom hc (D.hom 0) hR'
    have hJ : J' = R''.map (castHom hc (D.hom 0)) := by rw [hRR, hJR']
    have hsurj' : Function.Surjective (castHom hc (D.hom 0)) := by
      rw [← MonoidHom.range_eq_top, range_castHom, MonoidHom.range_eq_top]
      exact hsurj
    have hsimple : IsSimpleGroup ↥NativeSporadic.M11 := (Q3.m11Facts).1
    have hinj : Function.Injective (castHom hc (D.hom 0)) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (castHom hc (D.hom 0)).ker with h | h
      · have hxk : x ∈ (castHom hc (D.hom 0)).ker := hx
        rw [h] at hxk
        exact Subgroup.mem_bot.mp hxk
      · exfalso
        have hu' := hu.mem
        rw [hJ] at hu'
        obtain ⟨r, -, hr⟩ := Subgroup.mem_map.mp hu'
        have hrk : r ∈ (castHom hc (D.hom 0)).ker := by rw [h]; exact Subgroup.mem_top r
        exact hu.ne_one (by rw [← hr]; exact hrk)
    obtain ⟨x, hxJ, hx4⟩ := exists_orderOf_four_of_unique_involution hu
      (D.card_eq (by norm_num) J' hJ')
    rw [hJ] at hxJ
    obtain ⟨s, hsR, rfl⟩ := Subgroup.mem_map.mp hxJ
    have hs4 : orderOf s = 4 := by rw [← orderOf_injective _ hinj s]; exact hx4
    exact dich_transport (castHom hc (D.hom 0)) ⟨hinj, hsurj'⟩ (R := R'')
      (fun ρ hρ2 hρR => m11_involutory_fixes hsR hs4 ρ hρ2 hρR) (hJ ▸ hu) β hβ2 (hJ ▸ hβ)

end Main

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

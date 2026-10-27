module

public import CFSG.CGT.PushingUpLit.BHS7.AltAssembly

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement
open Equiv Equiv.Perm

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ} {m : ℕ}

omit [Finite Γ] in
theorem exists_mul_of_mem_sup_of_commute {K E : Subgroup Γ}
    (hc : ∀ k ∈ K, ∀ e ∈ E, k * e = e * k) {x : Γ} (hx : x ∈ K ⊔ E) :
    ∃ k ∈ K, ∃ e ∈ E, x = k * e := by
  have hK : K ≤ Subgroup.centralizer (E : Set Γ) := fun k hk =>
    Subgroup.mem_centralizer_iff.mpr fun e he => (hc k hk e he).symm
  have hn : K ≤ Subgroup.normalizer (E : Set Γ) := hK.trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((K ⊔ E : Subgroup Γ) : Set Γ) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K E hn] at hx'
  obtain ⟨k, hk, e, he, rfl⟩ := hx'
  exact ⟨k, hk, e, he, rfl⟩

theorem omega_comm' (h : MinCex G T) {E E' : Subgroup Γ} (hE : E ∈ omegaSet G T)
    (hE' : E' ∈ omegaSet G T) (hne : E' ≠ E) : ∀ x ∈ E', ∀ y ∈ E, x * y = y * x := by
  intro x hx y hy
  have h1 : ⁅x, y⁆ ∈ (⁅E', E⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hx hy
  rw [omega_comm h hE hE' hne, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

omit [Finite Γ] in
theorem mem_normalizer_of_mem_normalizer_inf [Finite Γ] {E S : Subgroup Γ}
    (hS : IsSylowTwoOf S E) {e : Γ} (heE : e ∈ E)
    (hn : e ∈ Subgroup.normalizer ((Subgroup.normalizer (S : Set Γ) ⊓ E : Subgroup Γ) : Set Γ)) :
    e ∈ Subgroup.normalizer (S : Set Γ) := by
  set N : Subgroup Γ := Subgroup.normalizer (S : Set Γ) ⊓ E with hN
  have hSN : S ≤ N := fun s hs => ⟨Subgroup.le_normalizer hs, hS.1 hs⟩
  have hNE : N ≤ E := inf_le_right
  have hSN' : IsSylowTwoOf S N := B6.isSylowTwoOf_mono hS hSN hNE
  have hconjE : B6.conjSub e E = E := B6.conjSub_eq_self (Subgroup.le_normalizer heE)
  have hconjN : B6.conjSub e N = N := B6.conjSub_eq_self hn
  have hS'E : IsSylowTwoOf (B6.conjSub e S) E := by
    have := B6.isSylowTwoOf_conjSub hS e
    rwa [hconjE] at this
  have hS'N : IsSylowTwoOf (B6.conjSub e S) N := by
    refine B6.isSylowTwoOf_mono hS'E ?_ hNE
    have := (B6.conjSub e).monotone hSN
    rwa [hconjN] at this
  obtain ⟨g, hgN, hg⟩ := B6.isSylowTwoOf_exists_conj hSN' hS'N
  have h1 : B6.conjSub (g⁻¹ * e) S = S := by
    rw [B6.conjSub_mul, hg, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one]
  have h2 : B6.conjSub (g⁻¹ * e)⁻¹ S = S := by
    have h3 := congrArg (B6.conjSub (g⁻¹ * e)⁻¹) h1
    rw [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at h3
    exact h3.symm
  have hmem : g⁻¹ * e ∈ Subgroup.normalizer (S : Set Γ) :=
    B6.mem_normalizer_of_conjSub_le h1.le h2.le
  have hdecomp : e = g * (g⁻¹ * e) := by group
  rw [hdecomp]
  exact (Subgroup.normalizer (S : Set Γ)).mul_mem (Subgroup.mem_inf.mp hgN).1 hmem

theorem mem_cStarIn_of_normalizes (h : MinCex G T) (hms : OmegaMaxSwap G T) {E : Subgroup Γ}
    (hE : E ∈ omegaSet G T) (hA3 : ¬ IsNaturalAltModule ↥E 1) {e : Γ} (heE : e ∈ E)
    (hn : e ∈ Subgroup.normalizer ((cStarIn G T ⊓ E : Subgroup Γ) : Set Γ)) :
    e ∈ cStarIn G T := by
  classical
  have hEb : IsBTBlock G T E := omega_isBTBlock h hE
  have hS : IsSylowTwoOf (T ⊓ E) E :=
    isSylowTwoOf_inf_of_isSubnormal hE.2 (isSylowTwoOf_of_isSylowOf h.sylow)
  rcases hEb.type with ⟨n, hn2, hnat⟩ | ⟨m, hm, hmat⟩
  ·
    have hK := omega_cstar_sl h hE hn2 hnat
    rw [hK] at hn
    have h1 := mem_normalizer_of_mem_normalizer_inf hS heE hn
    have h2 : e ∈ cStarIn G T ⊓ E := by
      rw [hK]
      exact ⟨h1, heE⟩
    exact h2.1
  ·
    have hm2 : 2 ≤ m := by
      by_contra hlt
      apply hA3
      have : m = 1 := by omega
      subst this
      exact hmat
    obtain ⟨A⟩ := nonempty_altAct h.charTwo h.sylow hEb hm hmat
    have hk : A.k = m := by
      have h3 := hms E hE m hm2 hmat
      rw [A.card_baum] at h3
      exact Nat.pow_right_injective le_rfl h3
    obtain ⟨p₀, hp₀⟩ := A.exists_cStarIn_iff hm hk h hEb hS (omega_not_le_cStarIn h hE)
    have heH : e ∈ E ⊔ baum T := (le_sup_left : E ≤ E ⊔ baum T) heE
    have hfix : A.Φ ⟨e, heH⟩ p₀ = p₀ := by
      refine apply_p₀_of_normalizes_fix (by omega : 4 ≤ 2 * m + 1) fun c hc hcp => ?_
      obtain ⟨e', he'E, he'c⟩ := A.exists_of_alt c hc
      have he'H : (e' : Γ) ∈ E ⊔ baum T := e'.2
      have he'C : (e' : Γ) ∈ cStarIn G T := (hp₀ e').mpr (by rw [he'c]; exact hcp)
      have he'K : (e' : Γ) ∈ cStarIn G T ⊓ E := ⟨he'C, he'E⟩
      have hm1 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hn) e').mp he'K
      have hm2' : e⁻¹ * (e' : Γ) * e ∈ cStarIn G T ⊓ E := by simpa using hm1
      have hmH : e⁻¹ * (e' : Γ) * e ∈ E ⊔ baum T :=
        (E ⊔ baum T).mul_mem ((E ⊔ baum T).mul_mem ((E ⊔ baum T).inv_mem heH) he'H) heH
      have := (hp₀ ⟨_, hmH⟩).mp hm2'.1
      have e1 : (⟨e⁻¹ * (e' : Γ) * e, hmH⟩ : ↥(E ⊔ baum T)) =
          ⟨e, heH⟩⁻¹ * e' * ⟨e, heH⟩ := rfl
      rw [e1, map_mul, map_mul, map_inv, he'c] at this
      exact this
    exact (hp₀ ⟨e, heH⟩).mpr hfix

theorem mem_iSup_cStarIn_of_na (h : MinCex G T) (hms : OmegaMaxSwap G T)
    (s : Finset (Subgroup Γ))
    (hs : ∀ F ∈ s, F ∈ omegaSet G T ∧ ¬ IsNaturalAltModule ↥F 1) :
    ∀ x ∈ cStarIn G T, ∀ q ∈ (⨆ F ∈ s, F : Subgroup Γ), ∀ r : Γ,
      (∀ F ∈ s, ∀ f ∈ F, r * f = f * r) → x = q * r →
        q ∈ (⨆ F ∈ s, cStarIn G T ⊓ F : Subgroup Γ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x _ q hq r _ _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Subgroup.mem_bot] at hq ⊢
    exact hq
  | insert E s hEs ih =>
    intro x hx q hq r hr hxqr
    have hs' : ∀ F ∈ s, F ∈ omegaSet G T ∧ ¬ IsNaturalAltModule ↥F 1 := fun F hF =>
      hs F (Finset.mem_insert_of_mem hF)
    have hEΩ : E ∈ omegaSet G T := (hs E (Finset.mem_insert_self E s)).1
    have hEna : ¬ IsNaturalAltModule ↥E 1 := (hs E (Finset.mem_insert_self E s)).2
    have hcomm : ∀ F ∈ s, ∀ f ∈ F, ∀ e ∈ E, f * e = e * f := fun F hF f hf e he =>
      omega_comm' h hEΩ (hs' F hF).1 (fun hFE => hEs (hFE ▸ hF)) f hf e he
    have hQE : ∀ q' ∈ (⨆ F ∈ s, F : Subgroup Γ), ∀ e ∈ E, q' * e = e * q' := by
      intro q' hq' e he
      have hle : (⨆ F ∈ s, F : Subgroup Γ) ≤ Subgroup.centralizer (E : Set Γ) :=
        iSup₂_le fun F hF f hf => Subgroup.mem_centralizer_iff.mpr fun e he =>
          (hcomm F hF f hf e he).symm
      exact (Subgroup.mem_centralizer_iff.mp (hle hq') e he).symm
    rw [Finset.iSup_insert] at hq
    have hq2 : q ∈ (⨆ F ∈ s, F : Subgroup Γ) ⊔ E := by rwa [sup_comm]
    obtain ⟨q', hq', e, he, rfl⟩ := exists_mul_of_mem_sup_of_commute hQE hq2
    have hrE : ∀ f ∈ E, r * f = f * r := hr E (Finset.mem_insert_self E s)
    have hxz : ∀ z ∈ E, x * z * x⁻¹ = e * z * e⁻¹ := by
      intro z hz
      have h1 := hQE q' hq' z hz
      have h2 := hrE z hz
      rw [hxqr]
      calc q' * e * r * z * (q' * e * r)⁻¹ = q' * e * (r * z) * r⁻¹ * e⁻¹ * q'⁻¹ := by group
        _ = q' * e * (z * r) * r⁻¹ * e⁻¹ * q'⁻¹ := by rw [h2]
        _ = q' * (e * z * e⁻¹) * q'⁻¹ := by group
        _ = e * z * e⁻¹ := by
          have h3 := hQE q' hq' (e * z * e⁻¹) (E.mul_mem (E.mul_mem he hz) (E.inv_mem he))
          rw [h3]
          group
    have hxinv : x⁻¹ ∈ cStarIn G T := (cStarIn G T).inv_mem hx
    have hen : e ∈ Subgroup.normalizer ((cStarIn G T ⊓ E : Subgroup Γ) : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyE : y ∈ E := hy.2
        have h1 : e * y * e⁻¹ = x * y * x⁻¹ := (hxz y hyE).symm
        rw [h1]
        exact ⟨(cStarIn G T).mul_mem ((cStarIn G T).mul_mem hx hy.1) hxinv, by
          rw [← h1]
          exact E.mul_mem (E.mul_mem he hyE) (E.inv_mem he)⟩
      · intro hy
        have hyE : y ∈ E := by
          have := E.mul_mem (E.mul_mem (E.inv_mem he) hy.2) he
          simpa [mul_assoc] using this
        have h1 : e * y * e⁻¹ = x * y * x⁻¹ := (hxz y hyE).symm
        have h2 : y = x⁻¹ * (e * y * e⁻¹) * x := by
          rw [h1]
          group
        refine ⟨?_, hyE⟩
        rw [h2]
        exact (cStarIn G T).mul_mem ((cStarIn G T).mul_mem hxinv hy.1) hx
    have heC : e ∈ cStarIn G T := mem_cStarIn_of_normalizes h hms hEΩ hEna he hen
    have hx' : x * e⁻¹ = q' * r := by
      have h1 : e * r = r * e := (hrE e he).symm
      rw [hxqr]
      calc q' * e * r * e⁻¹ = q' * (e * r) * e⁻¹ := by group
        _ = q' * (r * e) * e⁻¹ := by rw [h1]
        _ = q' * r := by group
    have hr' : ∀ F ∈ s, ∀ f ∈ F, r * f = f * r := fun F hF f hf =>
      hr F (Finset.mem_insert_of_mem hF) f hf
    have hq'C := ih hs' (x * e⁻¹) ((cStarIn G T).mul_mem hx ((cStarIn G T).inv_mem heC)) q' hq' r
      hr' hx'
    rw [Finset.iSup_insert]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hq'C) (Subgroup.mem_sup_left ⟨heC, he⟩)

end CFSG.CGT.PushingUpLit.BHS7

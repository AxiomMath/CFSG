module

public import CFSG.GH74.GLS.C3.Layer1.P34T0Card

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.Quasithin MulAction
open scoped IsMulCommutative

theorem odd_prod_ne_one {A : Type*} [CommGroup A] {a b : A} (ha : a ≠ 1) (hb : b ≠ 1)
    (ha2 : a * a = 1) (hb2 : b * b = 1) {ι : Type*} [Fintype ι] (hcard : Odd (Fintype.card ι))
    (z : ι → A) (hz : ∀ i, z i = a ∨ z i = b) : ∏ i, z i ≠ 1 := by
  classical
  have ha2' : a ^ 2 = 1 := by rw [sq]; exact ha2
  have hb2' : b ^ 2 = 1 := by rw [sq]; exact hb2
  by_cases hab : a = b
  · have hall : ∀ i, z i = a := fun i => (hz i).elim id (fun h => h.trans hab.symm)
    rw [Finset.prod_congr rfl (fun i _ => hall i), Finset.prod_const, Finset.card_univ]
    obtain ⟨k, hk⟩ := hcard
    rw [hk, pow_succ, pow_mul, ha2', one_pow, one_mul]
    exact ha
  · have e : ∏ i, z i = ∏ i, (if z i = a then a else b) := by
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases h : z i = a
      · simp [h]
      · simp only [h, ite_false]; exact (hz i).resolve_left h
    rw [e, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun i => z i = a)
    rw [Finset.card_univ] at hsum
    set α := (Finset.univ.filter (fun i => z i = a)).card with hα
    set β := (Finset.univ.filter (fun i => ¬ z i = a)).card with hβ
    obtain ⟨k, hk⟩ := hcard
    have hpar : α % 2 = 0 ∧ β % 2 = 1 ∨ α % 2 = 1 ∧ β % 2 = 0 := by omega
    have hapow : ∀ m : ℕ, a ^ m = a ^ (m % 2) := fun m => by
      conv_lhs => rw [← Nat.mod_add_div m 2, pow_add, pow_mul, ha2', one_pow, mul_one]
    have hbpow : ∀ m : ℕ, b ^ m = b ^ (m % 2) := fun m => by
      conv_lhs => rw [← Nat.mod_add_div m 2, pow_add, pow_mul, hb2', one_pow, mul_one]
    rw [hapow α, hbpow β]
    rcases hpar with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; simpa using hb
    · rw [h1, h2]; simpa using ha

variable {X : Type} [Group X] [Finite X] {T P Q : Subgroup X} {x z f h : X}

theorem lemma35 (c : Cfg34 X T P Q x z f h) : Lemma35 T P Q f := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R : Subgroup X := P ⊔ Q with hR
  have hRle : R ≤ T := c.R_le
  have hnormal : (R.subgroupOf T).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using c.R_norm g g.2 n hn⟩
  have hcomm : IsMulCommutative (Qbar T R) := ⟨⟨fun a b => by
    induction a using QuotientGroup.induction_on with | H s => ?_
    induction b using QuotientGroup.induction_on with | H t => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := c.kf_abelian (t : X)⁻¹ (T.inv_mem t.2) (s : X)⁻¹ (T.inv_mem s.2)
    show ((s : X) * (t : X))⁻¹ * ((t : X) * (s : X)) ∈ R
    have e : ((s : X) * (t : X))⁻¹ * ((t : X) * (s : X)) =
        (t : X)⁻¹ * (s : X)⁻¹ * (t : X)⁻¹⁻¹ * (s : X)⁻¹⁻¹ := by group
    rw [e]; exact h1⟩⟩
  let τ : X →* Qbar T R := MonoidHom.transfer (phiQ T R)
  have hτ1 : ∀ y : X, τ y = 1 := by
    rcases c.X_simple.eq_bot_or_eq_top_of_normal τ.ker with hker | hker
    · exfalso
      obtain ⟨a, b, hab⟩ := c.X_nonab
      apply hab
      have h1 : τ (a * b) = τ (b * a) := by rw [map_mul, map_mul]; exact mul_comm _ _
      have h2 : (a * b)⁻¹ * (b * a) ∈ τ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, h1]; simp
      rw [hker, Subgroup.mem_bot] at h2
      calc a * b = a * b * ((a * b)⁻¹ * (b * a)) := by rw [h2, mul_one]
        _ = b * a := by group
    · intro y
      exact MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top y)
  have hb : ∀ (g : X) (k : ℕ), g⁻¹ * f ^ (2 * k) * g ∈ T → g⁻¹ * f ^ (2 * k) * g ∈ R := by
    intro g k _
    have : f ^ (2 * k) = 1 := by
      rw [pow_mul, sq, c.f_sq, one_pow]
    rw [this]
    have : g⁻¹ * 1 * g = 1 := by group
    rw [this]; exact R.one_mem
  have := Fintype.ofFinite (X ⧸ T)
  obtain ⟨D, hDC, hDp, hDsyl, hfD⟩ :=
    exists_sylow_centralizer (p := 2) (u := f) ⟨1, by simp [c.f_order]⟩
  have hτf : τ f = ∏ x : X ⧸ T, valF T R f x :=
    transfer_eq_prod_valF T R c.T_pgroup c.f_mem hb
  have hcommD : ∀ d : ↥D, (d : X) * f = f * d := fun d =>
    (Subgroup.mem_centralizer_iff.mp (hDC d.2) f (Set.mem_singleton f)).symm
  have h1 : ∏ x : X ⧸ T, valF T R f x = ∏ x : fixedPoints D (X ⧸ T), valF T R f x :=
    prod_eq_prod_fixedPoints hDp (valF T R f)
      (fun d x => valF_smul T R f d (hcommD d) x) (valF_pow T R f hb)
  have hcard : ¬ 2 ∣ Nat.card (fixedPoints D (X ⧸ T)) := by
    have hmod := hDp.card_modEq_card_fixedPoints (X ⧸ T)
    rw [← Nat.ModEq.dvd_iff hmod dvd_rfl, ← Subgroup.index_eq_card]
    exact c.T_index
  have hcard' : Odd (Fintype.card (fixedPoints D (X ⧸ T))) := by
    rw [Fintype.card_eq_nat_card, Nat.odd_iff]
    by_contra hne
    exact hcard (Nat.dvd_of_mod_eq_zero (by omega))
  have hex : ∃ xx : fixedPoints D (X ⧸ T), xx.1.out⁻¹ * f * xx.1.out ∈ R := by
    by_contra hnone
    push Not at hnone
    set a : Qbar T R := phiQ T R ⟨f, c.f_mem⟩ with ha
    set b : Qbar T R := phiQ T R ⟨h, c.h_mem⟩ with hb'
    have ha1 : a ≠ 1 := fun h1 => c.f_not_mem ((phiQ_eq_one_iff T R _).1 h1)
    have ha2 : a * a = 1 := by
      rw [ha, ← map_mul]
      have : (⟨f, c.f_mem⟩ * ⟨f, c.f_mem⟩ : ↥T) = 1 := Subtype.ext c.f_sq
      rw [this, map_one]
    have hb2 : b * b = 1 := by
      rw [hb', ← map_mul]
      have : (⟨h, c.h_mem⟩ * ⟨h, c.h_mem⟩ : ↥T) = 1 := Subtype.ext c.h_sq
      rw [this, map_one]
    have hy : ∀ xx : fixedPoints D (X ⧸ T), xx.1.out⁻¹ * f * xx.1.out ∈ T ∧
        IsExtremalIn 2 T (xx.1.out⁻¹ * f * xx.1.out) := fun xx =>
      extremal_of_fixed c.T_pgroup hDC hDsyl hfD xx.2
    have hval : ∀ xx : fixedPoints D (X ⧸ T),
        valF T R f xx.1 = phiQ T R ⟨xx.1.out⁻¹ * f * xx.1.out, (hy xx).1⟩ := by
      intro xx
      rw [valF_eq T R f xx.1 xx.1.out (QuotientGroup.out_eq' _)]
      simp only [(hy xx).1, ↓reduceDIte]
    have hcls : ∀ xx : fixedPoints D (X ⧸ T), valF T R f xx.1 = a ∨ valF T R f xx.1 = b := by
      intro xx
      rw [hval xx]
      have hy2 : (xx.1.out⁻¹ * f * xx.1.out) * (xx.1.out⁻¹ * f * xx.1.out) = 1 := by
        calc (xx.1.out⁻¹ * f * xx.1.out) * (xx.1.out⁻¹ * f * xx.1.out)
            = xx.1.out⁻¹ * (f * f) * xx.1.out := by group
          _ = 1 := by rw [c.f_sq]; group
      rcases c.kf_invol _ (hy xx).1 hy2 with hRf | ⟨r, hr, hrh⟩
      · left
        have hy' : xx.1.out⁻¹ * f * xx.1.out ∈ (((P ⊔ Q) ⊔ zpowers f : Subgroup X) : Set X) := hRf
        rw [c.coe_Rf] at hy'
        obtain ⟨r, hr, ff, hff, hrf⟩ := hy'
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hff
        have hrf' : r * f ^ k = xx.1.out⁻¹ * f * xx.1.out := hrf
        rcases zpow_involution_cases c.f_sq k with hk | hk
        · exfalso
          rw [hk, mul_one] at hrf'
          exact hnone xx (hrf' ▸ hr)
        · rw [hk] at hrf'
          have : (⟨xx.1.out⁻¹ * f * xx.1.out, (hy xx).1⟩ : ↥T) =
              ⟨r, hRle hr⟩ * ⟨f, c.f_mem⟩ := Subtype.ext hrf'.symm
          rw [this, map_mul, (phiQ_eq_one_iff T R _).2 hr, one_mul]
      · right
        have : (⟨xx.1.out⁻¹ * f * xx.1.out, (hy xx).1⟩ : ↥T) = ⟨r, hRle hr⟩ * ⟨h, c.h_mem⟩ :=
          Subtype.ext hrh
        rw [this, map_mul, (phiQ_eq_one_iff T R _).2 hr, one_mul]
    have hprod : ∏ xx : fixedPoints D (X ⧸ T), valF T R f xx.1 ≠ 1 := by
      rcases c.kf_h with hh | ⟨hhR, -⟩
      · have hb1 : b = 1 := by
          rw [hb']
          have : (⟨h, c.h_mem⟩ : ↥T) = 1 := Subtype.ext hh
          rw [this, map_one]
        have hall : ∀ xx : fixedPoints D (X ⧸ T), valF T R f xx.1 = a := by
          intro xx
          rcases hcls xx with h1 | h1
          · exact h1
          · exfalso
            have h2 : phiQ T R ⟨xx.1.out⁻¹ * f * xx.1.out, (hy xx).1⟩ = 1 :=
              (hval xx).symm.trans (h1.trans hb1)
            exact hnone xx ((phiQ_eq_one_iff T R _).1 h2)
        rw [Finset.prod_congr rfl (fun xx _ => hall xx), Finset.prod_const, Finset.card_univ]
        obtain ⟨k, hk⟩ := hcard'
        have ha2' : a ^ 2 = 1 := by rw [sq]; exact ha2
        rw [hk, pow_succ, pow_mul, ha2', one_pow, one_mul]
        exact ha1
      · have hb1 : b ≠ 1 := fun h1 =>
          hhR (mem_sup_left (show h ∈ P ⊔ Q from (phiQ_eq_one_iff T R _).1 h1))
        exact odd_prod_ne_one ha1 hb1 ha2 hb2 hcard' _ hcls
    exact hprod ((h1.symm.trans hτf.symm).trans (hτ1 f))
  obtain ⟨xx, hxx⟩ := hex
  have hext := (extremal_of_fixed c.T_pgroup hDC hDsyl hfD xx.2).2
  obtain ⟨c₀, hc₀, hcall⟩ := exists_iii c.T_pgroup hext
  have hconj : (xx.1.out * c₀)⁻¹ * f * (xx.1.out * c₀) = xx.1.out⁻¹ * f * xx.1.out := by
    have hcomm' : c₀ * (xx.1.out⁻¹ * f * xx.1.out) = (xx.1.out⁻¹ * f * xx.1.out) * c₀ :=
      mem_centralizer_singleton_iff.1 hc₀
    calc (xx.1.out * c₀)⁻¹ * f * (xx.1.out * c₀)
        = c₀⁻¹ * ((xx.1.out⁻¹ * f * xx.1.out) * c₀) := by group
      _ = c₀⁻¹ * (c₀ * (xx.1.out⁻¹ * f * xx.1.out)) := by rw [hcomm']
      _ = xx.1.out⁻¹ * f * xx.1.out := by group
  refine ⟨xx.1.out * c₀, ?_, ?_, ?_⟩
  · rw [hconj]; exact hxx
  · intro c' hc'T hc'f
    exact (hcall c' ⟨hc'T, mem_centralizer_singleton_iff.2 hc'f⟩).1
  · rw [hconj]; exact hext

end CFSG.GH74.GLS.C3.Layer1.P34

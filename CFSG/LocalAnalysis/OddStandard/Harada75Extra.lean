module

public import CFSG.LocalAnalysis.OddStandard.Harada75Rank
public import CFSG.LocalAnalysis.OddStandard.Harada75Conj
public import CFSG.LocalAnalysis.OddStandard.Harada75Count
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.OddStandard.Harada75

open Heis
open scoped commutatorElement

theorem cases_arith (g n u : ℕ) (hg : ∃ i ≤ 2, g = 2 ^ i) (hn : ∃ j ≤ 5, n = 2 ^ j)
    (h : g * n = 32 * u) :
    (g = 1 ∧ n = 32 ∧ u = 1) ∨ (g = 2 ∧ n = 16 ∧ u = 1) ∨ (g = 4 ∧ n = 8 ∧ u = 1) ∨
      (g = 2 ∧ n = 32 ∧ u = 2) ∨ (g = 4 ∧ n = 16 ∧ u = 2) ∨ (g = 4 ∧ n = 32 ∧ u = 4) := by
  obtain ⟨i, hi, rfl⟩ := hg
  obtain ⟨j, hj, rfl⟩ := hn
  interval_cases i <;> interval_cases j <;> omega

variable {S : Type} [Group S] {ι : Heis →* S}

theorem range_le_Vsub (ι : Heis →* S) : ι.range ≤ Vsub ι := by
  intro r hr
  exact Subgroup.mem_normalizer_iff.mpr fun h =>
    ⟨fun hh => ι.range.mul_mem (ι.range.mul_mem hr hh) (ι.range.inv_mem hr),
      fun hh => by
        have := ι.range.mul_mem (ι.range.mul_mem (ι.range.inv_mem hr) hh) hr
        simpa [mul_assoc] using this⟩

namespace Setup

variable (D : Setup ι)
include D

theorem card_range : Nat.card ι.range = 32 := by
  rw [← card_heis]
  exact (Nat.card_congr (MonoidHom.ofInjective D.inj).toEquiv).symm

theorem Zc_cent (c : ZMod 2) (s : S) : s * ι (Zc c) = ι (Zc c) * s := by
  rcases zmod2_cases c with rfl | rfl
  · rw [Zc_zero, map_one]; simp
  · rw [Zc_one]; exact D.z_cent s

@[expose] noncomputable def psiOn (T : Subgroup S) (hT : T ≤ Vsub ι) : T →* Isom :=
  D.psi.comp (Subgroup.inclusion hT)

theorem psiOn_apply (T : Subgroup S) (hT : T ≤ Vsub ι) (t : T) (w : W₀) :
    ((D.psiOn T hT t : Isom) : Equiv.Perm W₀) w = lin (D.phi ⟨t.1, hT t.2⟩) w := rfl

theorem card_sub_eq (T : Subgroup S) (hT : T ≤ Vsub ι) :
    Nat.card T = Nat.card (D.psiOn T hT).range * Nat.card ↥(T ⊓ ι.range) := by
  have h1 := Subgroup.card_ker_mul_card_range (D.psiOn T hT)
  have e : Nat.card (D.psiOn T hT).ker = Nat.card ↥(T ⊓ ι.range) := by
    refine Nat.card_congr
      { toFun := fun t => ⟨t.1.1, t.1.2, by
          have := t.2
          rw [MonoidHom.mem_ker] at this
          exact (D.psi_eq_one_iff ⟨t.1.1, hT t.1.2⟩).mp this⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, by
          rw [MonoidHom.mem_ker]
          exact (D.psi_eq_one_iff ⟨x.1, hT x.2.1⟩).mpr x.2.2⟩
        left_inv := fun t => rfl
        right_inv := fun x => rfl }
  rw [e] at h1
  rw [← h1, mul_comm]

theorem comm_phi (t : Vsub ι) (h : Heis) :
    t.1 * ι h * t.1⁻¹ * (ι h)⁻¹ = ι (D.phi t h * h⁻¹) := by
  rw [map_mul, map_inv, D.phi_spec]

theorem phi_w (t : Vsub ι) (h : Heis) : (D.phi t h).w = lin (D.phi t) h.w := by
  rw [phi_eq (D.phi t) (D.phi_z t) h]

theorem comm_phi_w (t : Vsub ι) (h : Heis) :
    (D.phi t h * h⁻¹).w = lin (D.phi t) h.w + h.w := by
  rw [Heis.mul_w, Heis.inv_w, D.phi_w]


theorem lin_phi_fix_of_comm (t : Vsub ι) (x : Heis) (c : ZMod 2)
    (h : t.1 * ι x * t.1⁻¹ = ι (Zc c * x)) : lin (D.phi t) x.w = x.w := by
  have h1 : D.phi t x = Zc c * x := D.inj (by rw [D.phi_spec, h])
  have h2 := D.phi_w t x
  rw [h1] at h2
  rw [← h2]
  simp [Zc]

theorem conj_comm_E (s : S) (h x : Heis) (hx : x ∈ E₀) :
    ∃ c : ZMod 2, (s * ι h * s⁻¹) * ι x * (s * ι h * s⁻¹)⁻¹ = ι (Zc c * x) := by
  obtain ⟨x'', hx'', e⟩ := D.E_norm s⁻¹ x hx
  simp only [inv_inv] at e
  refine ⟨b₀ h.w x''.w, ?_⟩
  have h1 : h * x'' * h⁻¹ = Zc (b₀ h.w x''.w) * x'' := by
    have := comm_formula h x''
    calc h * x'' * h⁻¹ = (h * x'' * h⁻¹ * x''⁻¹) * x'' := by group
      _ = Zc (b₀ h.w x''.w) * x'' := by rw [this]
  have h2 : ι x = s * ι x'' * s⁻¹ := by
    rw [← e]; group
  calc (s * ι h * s⁻¹) * ι x * (s * ι h * s⁻¹)⁻¹
      = s * (ι h * (s⁻¹ * ι x * s) * (ι h)⁻¹) * s⁻¹ := by group
    _ = s * (ι h * ι x'' * (ι h)⁻¹) * s⁻¹ := by rw [e]
    _ = s * ι (h * x'' * h⁻¹) * s⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = s * ι (Zc (b₀ h.w x''.w) * x'') * s⁻¹ := by rw [h1]
    _ = s * (ι (Zc (b₀ h.w x''.w)) * ι x'') * s⁻¹ := by rw [map_mul]
    _ = (s * ι (Zc (b₀ h.w x''.w)) * s⁻¹) * (s * ι x'' * s⁻¹) := by group
    _ = ι (Zc (b₀ h.w x''.w)) * ι x := by
        rw [← h2, show s * ι (Zc (b₀ h.w x''.w)) * s⁻¹ = ι (Zc (b₀ h.w x''.w)) by
          rw [D.Zc_cent _ s]; group]
    _ = ι (Zc (b₀ h.w x''.w) * x) := by rw [map_mul]

theorem conj_comm_conj (s : S) (h h' : Heis) :
    ∃ c : ZMod 2, (s * ι h * s⁻¹) * (s * ι h' * s⁻¹) * (s * ι h * s⁻¹)⁻¹ * (s * ι h' * s⁻¹)⁻¹ =
      ι (Zc c) := by
  refine ⟨b₀ h.w h'.w, ?_⟩
  have := congrArg ι (comm_formula h h')
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at this
  calc (s * ι h * s⁻¹) * (s * ι h' * s⁻¹) * (s * ι h * s⁻¹)⁻¹ * (s * ι h' * s⁻¹)⁻¹
      = s * (ι h * ι h' * (ι h)⁻¹ * (ι h')⁻¹) * s⁻¹ := by group
    _ = s * ι (Zc (b₀ h.w h'.w)) * s⁻¹ := by rw [this]
    _ = ι (Zc (b₀ h.w h'.w)) := by rw [D.Zc_cent _ s]; group


theorem Vsub_eq_top [Finite S] (hS : IsPGroup 2 S) : Vsub ι = ⊤ := by
  classical
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent S := hS.isNilpotent
  have hnc : NormalizerCondition S := Group.normalizerCondition_of_isNilpotent
  have hnot : Subgroup.normalizer ((Vsub ι : Subgroup S) : Set S) ≠ Vsub ι :=
    fun h => hne ((normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ h)
  obtain ⟨s, hsN, hsV⟩ : ∃ s ∈ Subgroup.normalizer ((Vsub ι : Subgroup S) : Set S),
      s ∉ Vsub ι := by
    by_contra hall
    push Not at hall
    exact hnot (le_antisymm (fun x hx => hall x hx) Subgroup.le_normalizer)
  let R' : Subgroup S := ι.range.map (MulAut.conj s).toMonoidHom
  have hmem : ∀ x : S, x ∈ R' ↔ ∃ h : Heis, s * ι h * s⁻¹ = x := by
    intro x
    constructor
    · rintro ⟨r, ⟨h, rfl⟩, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨ι h, ⟨h, rfl⟩, rfl⟩
  have hR'V : R' ≤ Vsub ι := by
    intro x hx
    obtain ⟨h, rfl⟩ := (hmem x).mp hx
    exact (Subgroup.mem_normalizer_iff.mp hsN _).mp (range_le_Vsub ι ⟨h, rfl⟩)
  have hR'card : Nat.card R' = 32 := by
    rw [Subgroup.card_map_of_injective (fun a b hab => (MulAut.conj s).injective hab),
      D.card_range]
  have hfix : ∀ τ : Vsub ι, τ.1 ∈ R' → ∀ w : W₀, w.2.2.1 = 0 → w.2.2.2 = 0 →
      lin (D.phi τ) w = w := by
    intro τ hτ w h1 h2
    obtain ⟨h, hh⟩ := (hmem τ.1).mp hτ
    have hx : (⟨w, 0⟩ : Heis) ∈ E₀ := ⟨h1, h2⟩
    obtain ⟨c, hc⟩ := D.conj_comm_E s h ⟨w, 0⟩ hx
    rw [hh] at hc
    exact D.lin_phi_fix_of_comm τ ⟨w, 0⟩ c hc
  have hex : ∃ t₀ ∈ R', t₀ ∉ ι.range := by
    by_contra hall
    push Not at hall
    have hle : R' ≤ ι.range := hall
    have heq : R' = ι.range :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hR'card, D.card_range])
    apply hsV
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · have : s * x * s⁻¹ ∈ R' := ⟨x, hx, rfl⟩
      rw [heq] at this
      exact range_le_Vsub ι hx |> fun _ => this
    · rw [← heq] at hx
      obtain ⟨h, hh⟩ := (hmem _).mp hx
      have : x = ι h := by
        have := hh
        calc x = s⁻¹ * (s * x * s⁻¹) * s := by group
          _ = s⁻¹ * (s * ι h * s⁻¹) * s := by rw [← hh]
          _ = ι h := by group
      rw [this]
      exact ⟨h, rfl⟩
  obtain ⟨t₀, ht₀R', ht₀R⟩ := hex
  let τ₀ : Vsub ι := ⟨t₀, hR'V ht₀R'⟩
  have hψ1 : D.psi τ₀ ≠ 1 := fun h => ht₀R ((D.psi_eq_one_iff τ₀).mp h)
  have hfixE : ∀ g : Isom, (∃ τ : Vsub ι, τ.1 ∈ R' ∧ D.psi τ = g) →
      cols (g : Equiv.Perm W₀) = idCols ∨ cols (g : Equiv.Perm W₀) = uCols := by
    rintro g ⟨τ, hτ, rfl⟩
    exact cols_of_fix_E (D.psi τ) (fun w h1 h2 => hfix τ hτ w h1 h2)
  have hcols : cols ((D.psi τ₀ : Isom) : Equiv.Perm W₀) = uCols := by
    rcases hfixE (D.psi τ₀) ⟨τ₀, ht₀R', rfl⟩ with h | h
    · exact absurd (eq_one_of_cols_id _ h) hψ1
    · exact h
  have hRR' : ∀ x ∈ ι.range, x ∈ R' → x ∈ E₀.map ι := by
    rintro x ⟨h, rfl⟩ hx'
    obtain ⟨h'', hh''⟩ := (hmem t₀).mp ht₀R'
    obtain ⟨h', hh'⟩ := (hmem (ι h)).mp hx'
    obtain ⟨c, hc⟩ := D.conj_comm_conj s h'' h'
    rw [hh'', hh'] at hc
    have hc' : t₀ * ι h * t₀⁻¹ = ι (Zc c * h) := by
      rw [map_mul]
      calc t₀ * ι h * t₀⁻¹ = (t₀ * ι h * t₀⁻¹ * (ι h)⁻¹) * ι h := by group
        _ = ι (Zc c) * ι h := by rw [hc]
    have hlin := D.lin_phi_fix_of_comm τ₀ h c hc'
    have := mem_E_of_fixed (D.psi τ₀) hcols h.w hlin
    exact ⟨h, this, rfl⟩
  have hcardR' := D.card_sub_eq R' hR'V
  have hΓ : Nat.card (D.psiOn R' hR'V).range ≤ 2 := by
    apply card_le_two_of_cols
    rintro g ⟨t, rfl⟩
    exact hfixE _ ⟨⟨t.1, hR'V t.2⟩, t.2, rfl⟩
  have hinf : Nat.card ↥(R' ⊓ ι.range) ≤ 8 := by
    have hle : R' ⊓ ι.range ≤ E₀.map ι := fun x hx => hRR' x hx.2 hx.1
    have h1 := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective D.inj, card_E₀] at h1
  have hmul := Nat.mul_le_mul hΓ hinf
  omega


omit D in
theorem comm_mem_U {T U : Subgroup S} (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) {x y : Heis}
    (hx : ι x ∈ T) (hy : ι y ∈ T) : ι (Zc (b₀ x.w y.w)) ∈ U := by
  have h1 := hcomm _ hx _ hy
  rw [commutatorElement_def] at h1
  have h2 := congrArg ι (comm_formula x y)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
  rw [← h2]
  exact h1

theorem phi_comm_mem_U {T U : Subgroup S} (hTV : T ≤ Vsub ι)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) (t : S) (ht : t ∈ T) {x : Heis} (hx : ι x ∈ T) :
    ι (D.phi ⟨t, hTV ht⟩ x * x⁻¹) ∈ U := by
  have h1 := hcomm t ht _ hx
  rw [commutatorElement_def] at h1
  rw [← D.comm_phi ⟨t, hTV ht⟩ x]
  exact h1


theorem U_big [Finite S] {T U : Subgroup S} (hTV : T ≤ Vsub ι)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) (hRT : ι.range ≤ T) (t : S) (ht : t ∈ T)
    (hψ : D.psi ⟨t, hTV ht⟩ ≠ 1) : 8 ≤ Nat.card U := by
  have hmemT : ∀ x : Heis, ι x ∈ T := fun x => hRT ⟨x, rfl⟩
  have hzU : ι z₀ ∈ U := by
    have := comm_mem_U (ι := ι) hcomm (x := ⟨e1, 0⟩) (y := ⟨f1, 0⟩) (hmemT _) (hmemT _)
    have hb : b₀ e1 f1 = 1 := by decide
    rw [hb] at this
    exact this
  have hZU : ∀ k : ZMod 2, ι (Zc k) ∈ U := by
    intro k
    rcases zmod2_cases k with rfl | rfl
    · rw [Zc_zero, map_one]; exact U.one_mem
    · rw [Zc_one]; exact hzU
  obtain ⟨τ, hτ⟩ : ∃ τ : Vsub ι, τ = ⟨t, hTV ht⟩ := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : W₀ → Heis, ∀ w, F w = D.phi τ ⟨w, 0⟩ * ⟨w, 0⟩⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have hFU : ∀ w, ι (F w) ∈ U := by
    intro w
    rw [hFdef, hτ]
    exact D.phi_comm_mem_U hTV hcomm t ht (hmemT _)
  have hFw : ∀ w, (F w).w = lin (D.phi τ) w + w := by
    intro w
    rw [hFdef]
    exact D.comm_phi_w τ ⟨w, 0⟩
  have hψ' : D.psi τ ≠ 1 := by rw [hτ]; exact hψ
  have hrank := rank_image (D.psi τ) hψ'
  obtain ⟨A, hA, hA4⟩ : ∃ A : Finset W₀, (∀ a ∈ A, ∃ w, (F w).w = a) ∧ 4 ≤ A.card := by
    refine ⟨Finset.univ.image (fun w : W₀ => ((D.psi τ : Isom) : Equiv.Perm W₀) w + w), ?_,
      hrank⟩
    intro a ha
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨w, by rw [hFw]; rfl⟩
  classical
  have hUH : 8 ≤ Nat.card (U.comap ι) := by
    have h1 := eight_le_card_of_cover F A hA hA4
      (Set.toFinset ((U.comap ι : Subgroup Heis) : Set Heis))
      (by
        intro w k
        rw [Set.mem_toFinset]
        show ι (Zc k * F w) ∈ U
        rw [map_mul]
        exact U.mul_mem (hZU k) (hFU w))
    rwa [Set.toFinset_card, ← Nat.card_eq_fintype_card] at h1
  have hle : Nat.card (U.comap ι) ≤ Nat.card U :=
    Nat.card_le_card_of_injective (fun x => ⟨ι x.1, x.2⟩) (by
      intro a b hab
      exact Subtype.ext (D.inj (congrArg Subtype.val hab)))
  omega


theorem card_comap (T : Subgroup S) : Nat.card (T.comap ι) = Nat.card ↥(T ⊓ ι.range) := by
  have h := Subgroup.map_comap_eq ι T
  have h2 : Nat.card ((T.comap ι).map ι) = Nat.card (T.comap ι) :=
    Subgroup.card_map_of_injective D.inj
  rw [← h2, h, inf_comm]

theorem hinj_one {x : Heis} (h : ι x = 1) : x = 1 := D.inj (by rw [h, map_one])

theorem caseA [Finite S] {T U : Subgroup S} (hTV : T ≤ Vsub ι) (hU : ∀ x ∈ U, x = 1)
    (hsq : ∀ x ∈ T, x ^ 2 ∈ U) (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U)
    (hn : Nat.card ↥(T ⊓ ι.range) = 8) : Nat.card (D.psiOn T hTV).range ≤ 2 := by
  have hmem : ∀ {x : Heis}, x ∈ T.comap ι ↔ ι x ∈ T := Iff.rfl
  have hNH : Nat.card (T.comap ι) = 8 := by rw [D.card_comap]; exact hn
  have hb : ∀ a ∈ T.comap ι, ∀ b ∈ T.comap ι, b₀ a.w b.w = 0 := by
    intro a ha b hb
    have h1 := comm_mem_U (ι := ι) hcomm (hmem.mp ha) (hmem.mp hb)
    exact (Zc_eq_one _).mp (D.hinj_one (hU _ h1))
  have hab : ∀ a ∈ T.comap ι, ∀ b ∈ T.comap ι, a * b = b * a := by
    intro a ha b hb'
    have h1 := comm_formula a b
    rw [hb a ha b hb', Zc_zero] at h1
    have h2 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h1
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h2]
  have hX4 := card_cImage_le_four (T.comap ι) hab
  have hZ2 := card_inf_Z₀_le (T.comap ι)
  have hprod := card_eq_cImage_mul (T.comap ι)
  rw [hNH] at hprod
  have hX : Nat.card (cImage (T.comap ι)) = 4 := by
    by_contra hne
    have h3 : Nat.card (cImage (T.comap ι)) ≤ 3 := by omega
    have := Nat.mul_le_mul h3 hZ2
    omega
  obtain ⟨u, hu, v, hv, hu0, hv0, huv⟩ := exists_two (cImage (T.comap ι)) (by omega)
  obtain ⟨a, ha, rfl⟩ := hu
  obtain ⟨b, hb', rfl⟩ := hv
  have hq : ∀ c ∈ T.comap ι, q₀ c.w = 0 := by
    intro c hc
    have h1 := hU _ (hsq _ (hmem.mp hc))
    rw [pow_two, ← map_mul] at h1
    have h2 := D.hinj_one h1
    rw [sq_formula] at h2
    exact (Zc_eq_one _).mp h2
  have hfix : ∀ g ∈ (D.psiOn T hTV).range, ∀ c ∈ T.comap ι,
      (g : Equiv.Perm W₀) c.w = c.w := by
    rintro g ⟨t, rfl⟩ c hc
    have h1 := D.phi_comm_mem_U hTV hcomm t.1 t.2 (hmem.mp hc)
    have h2 := D.hinj_one (hU _ h1)
    have h3 := congrArg Heis.w h2
    rw [D.comm_phi_w, Heis.one_w] at h3
    rw [D.psiOn_apply]
    exact eq_of_add_eq_zero_W₀ h3
  exact card_fix_plane_le (D.psiOn T hTV).range a.w b.w hu0 hv0 huv (hq a ha) (hq b hb')
    (hb a ha b hb') (fun g hg => ⟨hfix g hg a ha, hfix g hg b hb'⟩)


theorem caseC [Finite S] {T U : Subgroup S} (hTV : T ≤ Vsub ι)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) (hU2 : Nat.card U = 2)
    (hn : Nat.card ↥(T ⊓ ι.range) = 16) : Nat.card (D.psiOn T hTV).range ≤ 1 := by
  have hmem : ∀ {x : Heis}, x ∈ T.comap ι ↔ ι x ∈ T := Iff.rfl
  have hNH : Nat.card (T.comap ι) = 16 := by rw [D.card_comap]; exact hn
  obtain ⟨a, ha, b, hb, hnab⟩ : ∃ a ∈ T.comap ι, ∃ b ∈ T.comap ι, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have := card_le_eight_of_abelian (T.comap ι) hall
    omega
  have hc1 : b₀ a.w b.w = 1 := by
    rcases zmod2_cases (b₀ a.w b.w) with h | h
    · exfalso
      apply hnab
      have h1 := comm_formula a b
      rw [h, Zc_zero] at h1
      have h2 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h1
      calc a * b = a * b * a⁻¹ * a := by group
        _ = b * a := by rw [h2]
    · exact h
  have hzU : ι z₀ ∈ U := by
    have := comm_mem_U (ι := ι) hcomm (hmem.mp ha) (hmem.mp hb)
    rwa [hc1, Zc_one] at this
  have hzN : z₀ ∈ T.comap ι := by
    have h1 := comm_formula a b
    rw [hc1, Zc_one] at h1
    rw [← h1]
    exact (T.comap ι).mul_mem ((T.comap ι).mul_mem ((T.comap ι).mul_mem ha hb)
      ((T.comap ι).inv_mem ha)) ((T.comap ι).inv_mem hb)
  have hinter := card_inf_Z₀_of_mem (T.comap ι) hzN
  have hprod := card_eq_cImage_mul (T.comap ι)
  rw [hNH, hinter] at hprod
  have hX : Nat.card (cImage (T.comap ι)) = 8 := by omega
  have hzne : ι z₀ ≠ 1 := fun h => by
    have := D.hinj_one h
    exact absurd (congrArg Heis.k this) (by decide)
  have hUstruct : ∀ x ∈ U, x = 1 ∨ x = ι z₀ := by
    classical
    intro x hx
    by_contra hne
    push Not at hne
    have h3 := finset_card_le_subgroup ({1, ι z₀, x} : Finset S) U (by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact U.one_mem
      · exact hzU
      · exact hx)
    have h4 : ({1, ι z₀, x} : Finset S).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨1, ι z₀, x, hzne.symm, hne.1.symm, hne.2.symm, rfl⟩
    omega
  have hfix : ∀ g ∈ (D.psiOn T hTV).range, ∀ c ∈ T.comap ι,
      (g : Equiv.Perm W₀) c.w = c.w := by
    rintro g ⟨t, rfl⟩ c hc
    have h1 := D.phi_comm_mem_U hTV hcomm t.1 t.2 (hmem.mp hc)
    have h3 : (D.phi ⟨t.1, hTV t.2⟩ c * c⁻¹).w = 0 := by
      rcases hUstruct _ h1 with h | h
      · rw [D.hinj_one h]; rfl
      · have := D.inj h
        rw [this]; rfl
    rw [D.comm_phi_w] at h3
    rw [D.psiOn_apply]
    exact eq_of_add_eq_zero_W₀ h3
  obtain ⟨u, hu, v, hv, w, hw, hind⟩ := exists_indep (cImage (T.comap ι)) (by omega)
  obtain ⟨a', ha', rfl⟩ := hu
  obtain ⟨b', hb', rfl⟩ := hv
  obtain ⟨c', hc', rfl⟩ := hw
  exact card_fix_hyper_le (D.psiOn T hTV).range a'.w b'.w c'.w hind
    (fun g hg => ⟨hfix g hg a' ha', hfix g hg b' hb', hfix g hg c' hc'⟩)


theorem abelian_of_trivial {T U : Subgroup S} (hU : ∀ x ∈ U, x = 1)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) :
    ∀ a ∈ T.comap ι, ∀ b ∈ T.comap ι, a * b = b * a := by
  intro a ha b hb'
  have h1 := comm_mem_U (ι := ι) hcomm (x := a) (y := b) ha hb'
  have h0 := (Zc_eq_one _).mp (D.hinj_one (hU _ h1))
  have h2 := comm_formula a b
  rw [h0, Zc_zero] at h2
  have h3 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h2
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h3]

theorem range_le_of_card [Finite S] {T : Subgroup S} (hn : Nat.card ↥(T ⊓ ι.range) = 32) :
    ι.range ≤ T := by
  have hle : T ⊓ ι.range ≤ ι.range := inf_le_right
  have heq : T ⊓ ι.range = ι.range :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hn, D.card_range])
  intro x hx
  have : x ∈ T ⊓ ι.range := by rw [heq]; exact hx
  exact this.1

theorem exists_psi_ne_one {T : Subgroup S} (hTV : T ≤ Vsub ι)
    (h : 2 ≤ Nat.card (D.psiOn T hTV).range) :
    ∃ t : S, ∃ ht : t ∈ T, D.psi ⟨t, hTV ht⟩ ≠ 1 := by
  by_contra hall
  push Not at hall
  have hbot : (D.psiOn T hTV).range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro g ⟨t, rfl⟩
    exact hall t.1 t.2
  rw [hbot, Subgroup.card_bot] at h
  omega

theorem noE32_of_setup [Finite S] (hS : IsPGroup 2 S) : NoE32 S := by
  intro T U ⟨hUT, hsq, hcomm, hcard⟩
  have hV := D.Vsub_eq_top hS
  have hTV : T ≤ Vsub ι := by rw [hV]; exact le_top
  have hcard_sub := D.card_sub_eq T hTV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := hS.to_subgroup T
  have hΓ2 : IsPGroup 2 (D.psiOn T hTV).range :=
    hT2.of_surjective (D.psiOn T hTV).rangeRestrict (D.psiOn T hTV).rangeRestrict_surjective
  have hΓle := card_le_four_of_isPGroup _ hΓ2
  obtain ⟨i, hi⟩ := hΓ2.exists_card_eq
  have hi2 : i ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 3 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  have hN2 : IsPGroup 2 ↥(T ⊓ ι.range) := hS.to_subgroup _
  obtain ⟨j, hj⟩ := hN2.exists_card_eq
  have hNle : Nat.card ↥(T ⊓ ι.range) ≤ 32 := by
    have := Subgroup.card_le_of_le (inf_le_right : T ⊓ ι.range ≤ ι.range)
    rwa [D.card_range] at this
  have hj5 : j ≤ 5 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hlt
    omega
  have hmain : Nat.card (D.psiOn T hTV).range * Nat.card ↥(T ⊓ ι.range) =
      32 * Nat.card U := by rw [← hcard_sub, hcard]
  have hUtriv : Nat.card U = 1 → ∀ x ∈ U, x = 1 := by
    intro h x hx
    have := Subgroup.eq_bot_of_card_eq U h
    rw [this] at hx
    exact hx
  rcases cases_arith _ _ _ ⟨i, hi2, hi⟩ ⟨j, hj5, hj⟩ hmain with
    ⟨hg, hn, hu⟩ | ⟨hg, hn, hu⟩ | ⟨hg, hn, hu⟩ | ⟨hg, hn, hu⟩ | ⟨hg, hn, hu⟩ | ⟨hg, hn, hu⟩
  ·
    have hU1 := hUtriv hu
    have hab := D.abelian_of_trivial hU1 hcomm
    have := card_le_eight_of_abelian (T.comap ι) hab
    rw [D.card_comap, hn] at this
    omega
  · have hU1 := hUtriv hu
    have hab := D.abelian_of_trivial hU1 hcomm
    have := card_le_eight_of_abelian (T.comap ι) hab
    rw [D.card_comap, hn] at this
    omega
  · have hU1 := hUtriv hu
    have := D.caseA hTV hU1 hsq hcomm hn
    omega
  ·
    obtain ⟨t, ht, hψ⟩ := D.exists_psi_ne_one hTV (by omega)
    have := D.U_big hTV hcomm (D.range_le_of_card hn) t ht hψ
    omega
  · have := D.caseC hTV hcomm hu hn
    omega
  · obtain ⟨t, ht, hψ⟩ := D.exists_psi_ne_one hTV (by omega)
    have := D.U_big hTV hcomm (D.range_le_of_card hn) t ht hψ
    omega

end Setup

end CFSG.OddStandard.Harada75

module

public import CFSG.ClassicalInvolution.Asc77.AscC25V1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

namespace TP

open MulAction Subgroup




section Pairing

variable {X A : Type*} [Fintype X] [DecidableEq X] [CommGroup A]

theorem prod_eq_prod_fixed_of_involution (f : X → A) (hf2 : ∀ x, f x ^ 2 = 1) (σ : X → X)
    (hσσ : ∀ x, f x ≠ 1 → σ (σ x) = x) (hσf : ∀ x, f x ≠ 1 → f (σ x) = f x) :
    ∏ x, f x = ∏ x ∈ Finset.univ.filter (fun x => σ x = x), f x := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x => σ x = x)]
  have h1 : ∏ x ∈ Finset.univ.filter (fun x => ¬ σ x = x), f x = 1 := by
    refine Finset.prod_involution (fun x _ => if f x = 1 then x else σ x) ?_ ?_ ?_ ?_
    · intro x hx
      by_cases h : f x = 1
      · simp [h]
      · simp only [h, ite_false]
        rw [hσf x h, ← sq, hf2]
    · intro x hx hne
      by_cases h : f x = 1
      · exact absurd h hne
      · simpa [h] using (Finset.mem_filter.mp hx).2
    · intro x hx
      by_cases h : f x = 1
      · simpa [h] using hx
      · simp only [h, ite_false]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        rw [hσσ x h]
        exact fun hh => (Finset.mem_filter.mp hx).2 hh.symm
    · intro x hx
      by_cases h : f x = 1
      · simp [h]
      · simp only [h, ite_false]
        have h' : f (σ x) ≠ 1 := by rw [hσf x h]; exact h
        simp [h', hσσ x h]
  rw [h1, mul_one]

end Pairing




section Transfer

variable {G : Type} [Group G] {H : Subgroup G} {A : Type*} [CommGroup A]

open Classical in
noncomputable def extOne (ϕ : H →* A) (g : G) : A := if h : g ∈ H then ϕ ⟨g, h⟩ else 1

theorem extOne_of_mem (ϕ : H →* A) {g : G} (hg : g ∈ H) : extOne ϕ g = ϕ ⟨g, hg⟩ := by
  classical
  simp [extOne, hg]

theorem extOne_of_not_mem (ϕ : H →* A) {g : G} (hg : g ∉ H) : extOne ϕ g = 1 := by
  classical
  simp [extOne, hg]

theorem extOne_conj (ϕ : H →* A) (g : G) {h : G} (hh : h ∈ H) :
    extOne ϕ (h⁻¹ * g * h) = extOne ϕ g := by
  by_cases hg : g ∈ H
  · have hg' : h⁻¹ * g * h ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hh) hg) hh
    rw [extOne_of_mem ϕ hg', extOne_of_mem ϕ hg]
    have : (⟨h⁻¹ * g * h, hg'⟩ : H) = (⟨h, hh⟩ : H)⁻¹ * ⟨g, hg⟩ * ⟨h, hh⟩ := rfl
    rw [this, map_mul, map_mul, map_inv]
    calc (ϕ ⟨h, hh⟩)⁻¹ * ϕ ⟨g, hg⟩ * ϕ ⟨h, hh⟩
        = ϕ ⟨g, hg⟩ * ((ϕ ⟨h, hh⟩)⁻¹ * ϕ ⟨h, hh⟩) := by
          rw [mul_comm ((ϕ ⟨h, hh⟩)⁻¹), mul_assoc]
      _ = ϕ ⟨g, hg⟩ := by rw [inv_mul_cancel, mul_one]
  · have hg' : h⁻¹ * g * h ∉ H := by
      intro hmem
      apply hg
      have := H.mul_mem (H.mul_mem hh hmem) (H.inv_mem hh)
      simpa [mul_assoc] using this
    rw [extOne_of_not_mem ϕ hg', extOne_of_not_mem ϕ hg]

noncomputable def fv (ϕ : H →* A) (a : G) (x : G ⧸ H) : A := extOne ϕ (x.out⁻¹ * a * x.out)

theorem fv_eq (ϕ : H →* A) (a : G) (g : G) : fv ϕ a (g : G ⧸ H) = extOne ϕ (g⁻¹ * a * g) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  unfold fv
  rw [hh]
  have : (g * (h : G))⁻¹ * a * (g * (h : G)) = (h : G)⁻¹ * (g⁻¹ * a * g) * (h : G) := by group
  rw [this, extOne_conj ϕ _ h.2]

theorem fv_smul (ϕ : H →* A) {a y : G} (hya : y * a = a * y) (x : G ⧸ H) :
    fv ϕ a (y • x) = fv ϕ a x := by
  have hx : x = ((x.out : G) : G ⧸ H) := (QuotientGroup.out_eq' x).symm
  have h1 : y • x = (((y * x.out : G)) : G ⧸ H) := by
    conv_lhs => rw [hx]
    rfl
  rw [h1, fv_eq, fv]
  have : (y * x.out)⁻¹ * a * (y * x.out) = x.out⁻¹ * (y⁻¹ * a * y) * x.out := by group
  rw [this]
  have hya' : y⁻¹ * a * y = a := by
    calc y⁻¹ * a * y = y⁻¹ * (a * y) := by group
      _ = y⁻¹ * (y * a) := by rw [hya]
      _ = a := by group
  rw [hya']

theorem fv_sq (ϕ : H →* A) {a : G} (ha2 : a * a = 1) (x : G ⧸ H) : fv ϕ a x ^ 2 = 1 := by
  unfold fv
  by_cases hmem : x.out⁻¹ * a * x.out ∈ H
  · rw [extOne_of_mem ϕ hmem, ← map_pow]
    have : (⟨x.out⁻¹ * a * x.out, hmem⟩ : H) ^ 2 = 1 := by
      apply Subtype.ext
      show (x.out⁻¹ * a * x.out) ^ 2 = 1
      calc (x.out⁻¹ * a * x.out) ^ 2 = x.out⁻¹ * (a * a) * x.out := by rw [pow_two]; group
        _ = 1 := by rw [ha2]; group
    rw [this, map_one]
  · rw [extOne_of_not_mem ϕ hmem, one_pow]

theorem smul_mk_eq_iff {a : G} (ha2 : a * a = 1) (g : G) :
    a • ((g : G ⧸ H)) = (g : G ⧸ H) ↔ g⁻¹ * a * g ∈ H := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  show (((a * g : G)) : G ⧸ H) = (g : G ⧸ H) ↔ _
  rw [QuotientGroup.eq]
  have : (a * g)⁻¹ * g = g⁻¹ * a⁻¹ * g := by group
  rw [this, hai]

theorem smul_eq_self_iff {a : G} (ha2 : a * a = 1) (x : G ⧸ H) :
    a • x = x ↔ x.out⁻¹ * a * x.out ∈ H := by
  have := smul_mk_eq_iff (H := H) ha2 x.out
  rwa [QuotientGroup.out_eq'] at this

theorem fv_eq_one_of_not_fixed (ϕ : H →* A) {a : G} (ha2 : a * a = 1) {x : G ⧸ H}
    (hx : a • x ≠ x) : fv ϕ a x = 1 := by
  unfold fv
  apply extOne_of_not_mem
  intro hmem
  exact hx ((smul_eq_self_iff ha2 x).mpr hmem)

theorem transfer_eq_prod [Finite G] [H.FiniteIndex] (ϕ : H →* A) {a : G} (ha2 : a * a = 1)
    [Fintype (G ⧸ H)] : ϕ.transfer a = ∏ x : G ⧸ H, fv ϕ a x := by
  classical
  have : Fintype (Quotient (orbitRel (zpowers a) (G ⧸ H))) := Fintype.ofFinite _
  rw [ϕ.transfer_eq_prod_quotient_orbitRel_zpowers_quot a]
  rw [← Finset.prod_fiberwise Finset.univ
    (fun x : G ⧸ H => (Quotient.mk (orbitRel (zpowers a) (G ⧸ H)) x)) (fun x => fv ϕ a x)]
  refine Finset.prod_congr rfl fun q _ => ?_
  set y : G ⧸ H := q.out with hy
  have hyq : Quotient.mk (orbitRel (zpowers a) (G ⧸ H)) y = q := Quotient.out_eq q
  have hfib : ∀ x : G ⧸ H, Quotient.mk (orbitRel (zpowers a) (G ⧸ H)) x = q ↔
      x ∈ orbit (zpowers a) y := by
    intro x
    rw [← hyq, Quotient.eq]
    exact orbitRel_apply
  by_cases hfix : a • y = y
  · have hper : Function.minimalPeriod (a • ·) y = 1 :=
      Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hfix
    have hmem : y.out⁻¹ * a * y.out ∈ H := (smul_eq_self_iff ha2 y).mp hfix
    have hstab : ∀ m ∈ zpowers a, m • y = y := by
      intro m hm
      have : zpowers a ≤ stabilizer G y := (Subgroup.zpowers_le).mpr (by
        rw [mem_stabilizer_iff]; exact hfix)
      exact mem_stabilizer_iff.mp (this hm)
    have hsing : Finset.univ.filter (fun x : G ⧸ H =>
        Quotient.mk (orbitRel (zpowers a) (G ⧸ H)) x = q) = {y} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [hfib]
      constructor
      · rintro ⟨m, hm⟩
        rw [← hm]
        exact hstab m m.2
      · rintro rfl
        exact mem_orbit_self _
    rw [hsing, Finset.prod_singleton]
    have e : (⟨y.out⁻¹ * a ^ Function.minimalPeriod (a • ·) y * y.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H a y⟩ : H) = ⟨y.out⁻¹ * a * y.out, hmem⟩ :=
      Subtype.ext (by
        show y.out⁻¹ * a ^ Function.minimalPeriod (a • ·) y * y.out = y.out⁻¹ * a * y.out
        rw [hper, pow_one])
    rw [e]
    show _ = extOne ϕ (y.out⁻¹ * a * y.out)
    rw [extOne_of_mem ϕ hmem]
  · have hper : Function.minimalPeriod (a • ·) y ≠ 1 := fun h =>
      hfix (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h)
    have hdvd : Function.minimalPeriod (a • ·) y ∣ 2 := by
      apply Function.IsPeriodicPt.minimalPeriod_dvd
      show (fun x => a • x)^[2] y = y
      rw [smul_iterate]
      simp [pow_two, ha2]
    have h2 : Function.minimalPeriod (a • ·) y = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hper
      · exact h
    have e : (⟨y.out⁻¹ * a ^ Function.minimalPeriod (a • ·) y * y.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem H a y⟩ : H) = 1 := by
      apply Subtype.ext
      show y.out⁻¹ * a ^ Function.minimalPeriod (a • ·) y * y.out = 1
      rw [h2, pow_two, ha2]
      group
    rw [e, map_one]
    symm
    apply Finset.prod_eq_one
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hfib] at hx
    apply fv_eq_one_of_not_fixed ϕ ha2
    intro hxfix
    apply hfix
    have : y ∈ orbit (zpowers a) x := by
      have := (hfib x).mpr
      rcases hx with ⟨m, hm⟩
      refine ⟨m⁻¹, ?_⟩
      rw [← hm]
      show (m⁻¹ : zpowers a) • (m • y) = y
      rw [← mul_smul, inv_mul_cancel, one_smul]
    obtain ⟨m, hm⟩ := this
    have hstab : ∀ m ∈ zpowers a, m • x = x := by
      intro m hm
      have : zpowers a ≤ stabilizer G x := (Subgroup.zpowers_le).mpr (by
        rw [mem_stabilizer_iff]; exact hxfix)
      exact mem_stabilizer_iff.mp (this hm)
    have hmx : m • x = x := by
      rw [Subgroup.smul_def]
      exact hstab m m.2
    rw [← hm]
    show a • (m • x) = m • x
    rw [hmx, hxfix]

theorem apply_eq_one_of_unique_fixed [Finite G] [H.FiniteIndex] (ϕ : H →* A)
    (hG : ∀ ψ : G →* A, ψ = 1) {a y : G} (ha2 : a * a = 1) (haH : a ∈ H) (hya : y * a = a * y)
    (hy4 : y ^ 4 = 1) (hyH : y ∈ H)
    (hfix : ∀ g : G, y • (g : G ⧸ H) = (g : G ⧸ H) → (g : G ⧸ H) = ((1 : G) : G ⧸ H)) :
    ϕ ⟨a, haH⟩ = 1 := by
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hT : ϕ.transfer a = 1 := by
    have := hG ϕ.transfer
    exact congrArg (fun ψ => ψ a) this
  rw [transfer_eq_prod ϕ ha2] at hT
  have hy2a : y ^ 2 * a = a * y ^ 2 := (Commute.pow_left (show Commute y a from hya) 2).eq
  have h1 := prod_eq_prod_fixed_of_involution (fun x : G ⧸ H => fv ϕ a x) (fv_sq ϕ ha2)
    (fun x => (y ^ 2) • x)
    (fun x _ => by
      rw [← mul_smul, ← pow_add]
      have : y ^ (2 + 2) = 1 := by rw [show 2 + 2 = 4 from rfl]; exact hy4
      rw [this, one_smul])
    (fun x _ => fv_smul ϕ hy2a x)
  rw [hT] at h1
  rw [Finset.prod_filter] at h1
  set f₁ : G ⧸ H → A := fun x => if y ^ 2 • x = x then fv ϕ a x else 1 with hf₁
  have hf₁2 : ∀ x, f₁ x ^ 2 = 1 := by
    intro x
    by_cases hx : y ^ 2 • x = x
    · simp only [hf₁, hx, ite_true]
      exact fv_sq ϕ ha2 x
    · simp [hf₁, hx]
  have h2 := prod_eq_prod_fixed_of_involution f₁ hf₁2 (fun x => y • x)
    (fun x hx => by
      have hx' : y ^ 2 • x = x := by
        by_contra hne
        exact hx (by simp [hf₁, hne])
      rw [← mul_smul, ← pow_two]
      exact hx')
    (fun x hx => by
      have hx' : y ^ 2 • x = x := by
        by_contra hne
        exact hx (by simp [hf₁, hne])
      have hyx : y ^ 2 • (y • x) = y • x := by
        rw [← mul_smul, (Commute.self_pow y 2).eq.symm, mul_smul, hx']
      simp only [hf₁, hyx, hx', ite_true]
      exact fv_smul ϕ hya x)
  have h1' : ∏ x : G ⧸ H, f₁ x = 1 := by
    rw [← h1]
  rw [h1'] at h2
  have hfilt : Finset.univ.filter (fun x : G ⧸ H => y • x = x) = {((1 : G) : G ⧸ H)} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact hfix g hx
    · rintro rfl
      show (((y * 1 : G)) : G ⧸ H) = ((1 : G) : G ⧸ H)
      rw [mul_one, QuotientGroup.eq, mul_one]
      exact H.inv_mem hyH
  rw [hfilt, Finset.prod_singleton] at h2
  have h3 : f₁ ((1 : G) : G ⧸ H) = fv ϕ a ((1 : G) : G ⧸ H) := by
    have : y ^ 2 • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
      show (((y ^ 2 * 1 : G)) : G ⧸ H) = ((1 : G) : G ⧸ H)
      rw [mul_one, QuotientGroup.eq, mul_one]
      exact H.inv_mem (H.pow_mem hyH 2)
    simp [hf₁, this]
  rw [h3, fv_eq, inv_one, one_mul, mul_one, extOne_of_mem ϕ haH] at h2
  exact h2.symm

end Transfer


end TP

section Cent

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem hom_centralizer_apply_eq_one (hnc : ∃ x y : G, x * y ≠ y * x) {z a y : G}
    (ha2 : a * a = 1) (haz : a * z = z * a) (hya : y * a = a * y) (hyz : y * z = z * y)
    (hy4 : y ^ 4 = 1)
    (hnc4 : ∀ g : G, (g * z * g⁻¹) * y = y * (g * z * g⁻¹) → g * z * g⁻¹ = z)
    {A : Type*} [CommGroup A] (ϕ : Subgroup.centralizer ({z} : Set G) →* A) :
    ϕ ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr haz⟩ = 1 := by
  have hH : ∀ g : G, g ∈ Subgroup.centralizer ({z} : Set G) ↔ g * z = z * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff
  refine TP.apply_eq_one_of_unique_fixed ϕ (fun ψ => hom_eq_one_of_simple_of_commGroup hnc ψ) ha2
    _ hya hy4 ((hH y).mpr hyz) ?_
  intro g hg
  have h1 : (((y * g : G)) : G ⧸ Subgroup.centralizer ({z} : Set G)) =
      (g : G ⧸ Subgroup.centralizer ({z} : Set G)) := hg
  rw [QuotientGroup.eq] at h1
  have h2 : (g⁻¹ * y⁻¹ * g) * z = z * (g⁻¹ * y⁻¹ * g) := by
    have := (hH _).mp h1
    simpa [mul_assoc] using this
  have h3 : (g * z * g⁻¹) * y = y * (g * z * g⁻¹) := by
    have h4 : y⁻¹ * (g * z * g⁻¹) = (g * z * g⁻¹) * y⁻¹ := by
      calc y⁻¹ * (g * z * g⁻¹) = g * ((g⁻¹ * y⁻¹ * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y⁻¹ * g)) * g⁻¹ := by rw [h2]
        _ = (g * z * g⁻¹) * y⁻¹ := by group
    calc (g * z * g⁻¹) * y = y * (y⁻¹ * (g * z * g⁻¹)) * y := by group
      _ = y * ((g * z * g⁻¹) * y⁻¹) * y := by rw [h4]
      _ = y * (g * z * g⁻¹) := by group
  have h5 := hnc4 g h3
  have h6 : g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [hH]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h5]
  rw [QuotientGroup.eq, mul_one]
  exact (Subgroup.centralizer ({z} : Set G)).inv_mem h6

end Cent

end CFSG.ClassicalInvolution.Asc77.C25V

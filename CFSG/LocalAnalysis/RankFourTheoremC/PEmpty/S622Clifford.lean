module

public import CFSG.Open.LocalVocabulary
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open scoped commutatorElement

private theorem s622_pow_card_eq_one_of_no_fixed {Γ N : Type*} [Group Γ] [Finite Γ] [Group N]
    [MulDistribMulAction Γ N] (hcomm : ∀ a b : N, a * b = b * a) {R Z : Subgroup Γ}
    (hZR : ∀ g ∈ Z, ∀ r ∈ R, g * r * g⁻¹ ∈ R)
    (hfpf : ∀ g ∈ Z, g ≠ 1 → ∀ r ∈ R, g * r = r * g → r = 1)
    (hN : ∀ x : N, (∀ r ∈ R, r • x = x) → x = 1)
    (hZ : ∀ d : N, (∀ g ∈ Z, g • d = d) → d = 1) (x : N) : x ^ Nat.card R = 1 := by
  classical
  letI : CommGroup N := { ‹Group N› with mul_comm := hcomm }
  haveI : Fintype R := Fintype.ofFinite R
  haveI : Fintype Z := Fintype.ofFinite Z
  have hnormR : ∀ y : N, ∏ r : R, ((r : Γ) • y) = 1 := by
    intro y
    apply hN
    intro b hb
    rw [Finset.smul_prod']
    simp only [smul_smul]
    exact Fintype.prod_bijective (fun r : R => (⟨b, hb⟩ : R) * r) (Group.mulLeft_bijective _) _ _
      (fun r => rfl)
  have hnormZ : ∀ y : N, ∏ g : Z, ((g : Γ) • y) = 1 := by
    intro y
    apply hZ
    intro b hb
    rw [Finset.smul_prod']
    simp only [smul_smul]
    exact Fintype.prod_bijective (fun g : Z => (⟨b, hb⟩ : Z) * g) (Group.mulLeft_bijective _) _ _
      (fun g => rfl)
  have hconj : ∀ g : Z, g ≠ 1 → ∏ r : R, (((r : Γ) * g * (r : Γ)⁻¹) • x) = 1 := by
    intro g hg
    have hg1 : (g : Γ) ≠ 1 := fun h => hg (Subtype.ext h)
    let ψ : R → R := fun r => ⟨(r : Γ) * ((g : Γ) * (r : Γ)⁻¹ * (g : Γ)⁻¹),
      R.mul_mem r.2 (hZR g g.2 _ (R.inv_mem r.2))⟩
    have hψ : Function.Injective ψ := by
      intro r s hrs
      have h1 : (r : Γ) * ((g : Γ) * (r : Γ)⁻¹ * (g : Γ)⁻¹) =
          (s : Γ) * ((g : Γ) * (s : Γ)⁻¹ * (g : Γ)⁻¹) := congrArg Subtype.val hrs
      have hts : (s : Γ)⁻¹ * (r : Γ) ∈ R := R.mul_mem (R.inv_mem s.2) r.2
      have h2 : (g : Γ) * ((s : Γ)⁻¹ * (r : Γ)) = ((s : Γ)⁻¹ * (r : Γ)) * g := by
        have h3 : (r : Γ) * (g : Γ) * (r : Γ)⁻¹ = (s : Γ) * (g : Γ) * (s : Γ)⁻¹ := by
          have := congrArg (· * (g : Γ)) h1
          simpa [mul_assoc] using this
        calc (g : Γ) * ((s : Γ)⁻¹ * (r : Γ))
            = (s : Γ)⁻¹ * ((s : Γ) * (g : Γ) * (s : Γ)⁻¹) * (r : Γ) := by group
          _ = (s : Γ)⁻¹ * ((r : Γ) * (g : Γ) * (r : Γ)⁻¹) * (r : Γ) := by rw [h3]
          _ = ((s : Γ)⁻¹ * (r : Γ)) * g := by group
      have h4 := hfpf g g.2 hg1 _ hts h2
      exact Subtype.ext (inv_mul_eq_one.mp h4).symm
    have hψb : Function.Bijective ψ := Finite.injective_iff_bijective.mp hψ
    calc ∏ r : R, (((r : Γ) * g * (r : Γ)⁻¹) • x)
        = ∏ r : R, ((((ψ r : R) : Γ) * g) • x) := by
          refine Finset.prod_congr rfl fun r _ => ?_
          congr 1
          change (r : Γ) * (g : Γ) * (r : Γ)⁻¹ =
            ((r : Γ) * ((g : Γ) * (r : Γ)⁻¹ * (g : Γ)⁻¹)) * g
          group
      _ = ∏ r : R, (((r : Γ) * g) • x) :=
          hψb.prod_comp (fun r : R => (((r : Γ) * g) • x))
      _ = ∏ r : R, ((r : Γ) • ((g : Γ) • x)) := by
          refine Finset.prod_congr rfl fun r _ => ?_
          rw [mul_smul]
      _ = 1 := hnormR _
  have hid : ∏ r : R, ∏ g : Z, (((r : Γ) * g * (r : Γ)⁻¹) • x) = x ^ Nat.card R := by
    rw [Finset.prod_comm, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : Z))]
    have h1 : ∏ r : R, (((r : Γ) * ((1 : Z) : Γ) * (r : Γ)⁻¹) • x) = x ^ Nat.card R := by
      simp [Finset.prod_const, Nat.card_eq_fintype_card]
    rw [h1, Finset.prod_eq_one (fun g hg => hconj g (Finset.ne_of_mem_erase hg)), mul_one]
  rw [← hid]
  refine Finset.prod_eq_one fun r _ => ?_
  have h1 : ∏ g : Z, (((r : Γ) * g * (r : Γ)⁻¹) • x) =
      (r : Γ) • ∏ g : Z, ((g : Γ) • (((r : Γ)⁻¹) • x)) := by
    rw [Finset.smul_prod']
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [mul_smul, mul_smul]
  rw [h1, hnormZ, smul_one]

private theorem s622_exists_abelian_invariant {G : Type*} [Group G] {D : Subgroup G}
    (hD : Group.IsSolvable D) (hD1 : D ≠ ⊥) :
    ∃ N : Subgroup G, N ≤ D ∧ N ≠ ⊥ ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
      ∀ g ∈ normalizer (D : Set G), g ∈ normalizer (N : Set G) := by
  classical
  have hnt : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD1
  have hex : ∃ k, derivedSeries D k ≠ ⊥ ∧ derivedSeries D (k + 1) = ⊥ := by
    obtain ⟨n, hn⟩ := hD.solvable
    by_contra hcon
    have hall : ∀ k, derivedSeries D k ≠ ⊥ := by
      intro k
      induction k with
      | zero => rw [derivedSeries_zero]; exact top_ne_bot
      | succ k ih => exact fun h => hcon ⟨k, ih, h⟩
    exact hall n hn
  obtain ⟨k, hk1, hk2⟩ := hex
  refine ⟨(derivedSeries D k).map D.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h
    exact hk1 ((Subgroup.map_eq_bot_iff_of_injective (derivedSeries D k) D.subtype_injective).mp h)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 : ⁅a, b⁆ ∈ (⊥ : Subgroup D) := by
      rw [← hk2, derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator ha hb
    have h3 : a * b = b * a := commutatorElement_eq_one_iff_mul_comm.mp h1
    exact congrArg Subtype.val h3
  · have key : ∀ g ∈ normalizer (D : Set G), ∀ h ∈ (derivedSeries D k).map D.subtype,
        g * h * g⁻¹ ∈ (derivedSeries D k).map D.subtype := by
      intro g hg h hh
      obtain ⟨y, hy, rfl⟩ := hh
      let φ : D ≃* D := Subgroup.normalizerMonoidHom D ⟨g, hg⟩
      have hφ : φ y ∈ derivedSeries D k := by
        have hfix := (Subgroup.characteristic_iff_comap_eq.mp (derivedSeries_characteristic D k)) φ
        have : y ∈ (derivedSeries D k).comap φ.toMonoidHom := by rw [hfix]; exact hy
        exact this
      exact ⟨φ y, hφ, rfl⟩
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key g hg h, fun hgh => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ hgh
    simpa [mul_assoc] using this

private theorem s622_commute_of_mem_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {z : G} (hz : orderOf z = p) {g : G} (hg : g ∈ zpowers z) (hg1 : g ≠ 1)
    {r : G} (hr : g * r = r * g) : z * r = r * z := by
  have hord : orderOf g = p := by
    have h1 : orderOf g ∣ p := by
      rw [← hz]
      exact orderOf_dvd_of_mem_zpowers hg
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hg1
    · exact h
  have hle : zpowers g ≤ zpowers z := Subgroup.zpowers_le.mpr hg
  have hcard : Nat.card (zpowers z) ≤ Nat.card (zpowers g) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hz]
  have heq : zpowers g = zpowers z := Subgroup.eq_of_le_of_card_ge hle hcard
  have hzg : z ∈ zpowers g := heq ▸ Subgroup.mem_zpowers z
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzg
  rw [← hj]
  exact Commute.zpow_left (show Commute g r from hr) j

set_option linter.unusedVariables false in
theorem s622_exists_commuting_of_frobenius {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {D R : Subgroup G} {z : G} (hz : orderOf z = p)
    (hD : Odd (Nat.card D)) (hpD : ¬ p ∣ Nat.card D) (hD1 : D ≠ ⊥)
    (hRe : CFSG.Open.IsElemAbelian 2 R) (hzR : z ∈ normalizer (R : Set G))
    (hRD : R ≤ normalizer (D : Set G)) (hzD : z ∈ normalizer (D : Set G))
    (hfpf : ∀ r ∈ R, z * r = r * z → r = 1)
    (hC : ∀ d ∈ D, (∀ r ∈ R, r * d = d * r) → d = 1) :
    ∃ d ∈ D, d ≠ 1 ∧ z * d = d * z := by
  classical
  obtain ⟨N, hND, hN1, hNcomm, hNinv⟩ :=
    s622_exists_abelian_invariant (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hD) hD1
  set Γ : Subgroup G := normalizer (N : Set G) with hΓ
  have hRΓ : R ≤ Γ := fun r hr => hNinv r (hRD hr)
  have hzΓ : z ∈ Γ := hNinv z hzD
  have hZR : zpowers z ≤ normalizer (R : Set G) := Subgroup.zpowers_le.mpr hzR
  have hR2 : IsPGroup 2 R := fun g => ⟨1, Subtype.ext (by simpa using hRe.2 g g.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR2
  have hcardR : Nat.card (R.subgroupOf Γ) = 2 ^ a :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRΓ).toEquiv).trans ha
  by_contra hcon
  have hcom : ∀ d ∈ D, z * d = d * z → d = 1 := fun d hd h => by
    by_contra h1
    exact hcon ⟨d, hd, h1, h⟩
  have hmain := s622_pow_card_eq_one_of_no_fixed (Γ := ↥Γ) (N := ↥N)
    (fun x y => Subtype.ext (hNcomm x x.2 y y.2)) (R := R.subgroupOf Γ)
    (Z := (zpowers z).subgroupOf Γ) ?_ ?_ ?_ ?_
  · haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN1
    obtain ⟨x, hx⟩ := exists_ne (1 : N)
    apply hx
    have h1 := hmain x
    rw [hcardR] at h1
    have h2 : orderOf x ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one h1
    have h3 : Odd (orderOf x) :=
      Odd.of_dvd_nat (Odd.of_dvd_nat hD (Subgroup.card_dvd_of_le hND)) (orderOf_dvd_natCard x)
    have h4 : Nat.Coprime (orderOf x) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr h3)
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h4 h2)
  · intro g hg r hr
    rw [Subgroup.mem_subgroupOf] at hg hr ⊢
    have hgn : (g : G) ∈ normalizer (R : Set G) := hZR hg
    simpa using (Subgroup.mem_normalizer_iff.mp hgn (r : G)).mp hr
  · intro g hg hg1 r hr hgr
    rw [Subgroup.mem_subgroupOf] at hg hr
    have hg1' : (g : G) ≠ 1 := fun h => hg1 (Subtype.ext h)
    have h1 : z * (r : G) = (r : G) * z :=
      s622_commute_of_mem_zpowers hp hz hg hg1' (congrArg Subtype.val hgr)
    exact Subtype.ext (hfpf r hr h1)
  · intro x hx
    apply Subtype.ext
    apply hC x (hND x.2)
    intro r hr
    have h1 := hx ⟨r, hRΓ hr⟩ (by rw [Subgroup.mem_subgroupOf]; exact hr)
    have h2 : r * (x : G) * r⁻¹ = x := congrArg Subtype.val h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  · intro d hd
    have h1 := hd ⟨z, hzΓ⟩ (by rw [Subgroup.mem_subgroupOf]; exact Subgroup.mem_zpowers z)
    have h2 : z * (d : G) * z⁻¹ = d := congrArg Subtype.val h1
    exact Subtype.ext (hcom d (hND d.2) (mul_inv_eq_iff_eq_mul.mp h2))

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

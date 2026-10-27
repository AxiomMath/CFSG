module

public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.GrSLit.HeLay

open CFSG Subgroup CFSG.Quasithin
open scoped commutatorElement

variable {Y T : Type*} [Group Y] [Finite Y] [Group T] [Finite T]

omit [Finite Y] [Finite T] in
theorem commutator_eq_self_of_simple {D : Subgroup T} (hD : IsSimpleGroup ↥D)
    (hDnab : ∃ a b : ↥D, a * b ≠ b * a) : ⁅D, D⁆ = D := by
  have hc : commutator ↥D = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥D) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hDnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator ↥D := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  have h1 := map_commutator (⊤ : Subgroup ↥D) ⊤ D.subtype
  rw [← commutator_def, hc, ← MonoidHom.range_eq_map, range_subtype] at h1
  exact h1.symm

theorem commute_of_perfect_of_card_four {N K : Subgroup Y} [K.Normal] (hN : ⁅N, N⁆ = N)
    (hK : Nat.card K = 4) : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ = k := by
  classical
  let F : Subgroup (MulAut ↥K) := N.map (MulAut.conjNormal : Y →* MulAut ↥K)
  have : Group.IsPerfect ↥N := isPerfect_iff.mpr hN
  have hFp : Group.IsPerfect ↥F := Group.IsPerfect.map _
  have hFcard : Nat.card ↥F ∣ 24 := by
    have h1 : Nat.card ↥(F.map (MulAut.toPerm ↥K)) = Nat.card ↥F :=
      card_map_of_injective (fun a b h =>
        MulEquiv.ext fun x => congrArg (fun e : Equiv.Perm ↥K => e x) h)
    have h2 : Nat.card (Equiv.Perm ↥K) = 24 := by
      have : Fintype ↥K := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hK]
      rfl
    rw [← h1, ← h2]
    exact card_subgroup_dvd_card _
  have hsol : Group.IsSolvable ↥F := by
    refine LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have h1 : (Nat.card ↥F).primeFactors ⊆ (24 : ℕ).primeFactors :=
      Nat.primeFactors_mono hFcard (by norm_num)
    have h2 : (24 : ℕ).primeFactors.card = 2 := by
      rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors Nat.prime_two,
        Nat.Prime.primeFactors Nat.prime_three]
      rfl
    exact (Finset.card_le_card h1).trans h2.le
  have hFbot : F = ⊥ := by
    by_contra hne
    have : Nontrivial ↥F := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hsol
  intro n hn k hk
  have h1 : MulAut.conjNormal n ∈ F := mem_map_of_mem _ hn
  rw [hFbot, mem_bot] at h1
  have h2 := congrArg (fun e : MulAut ↥K => ((e ⟨k, hk⟩ : ↥K) : Y)) h1
  simpa [MulAut.conjNormal_apply] using h2

theorem exists_quasisimple_normal (ρ : Y →* T) {D : Subgroup T} (hD : IsSimpleGroup ↥D)
    (hDnab : ∃ a b : ↥D, a * b ≠ b * a) (hDle : D ≤ ρ.range)
    (hcomm : ⁅ρ.range, ρ.range⁆ ≤ D) (hker : Nat.card ρ.ker = 4) :
    ∃ N : Subgroup Y, N.Normal ∧ IsQuasisimple ↥N ∧ N.map ρ = D := by
  set N : Subgroup Y := perfectCore (⊤ : Subgroup Y) with hNdef
  have hNp : ⁅N, N⁆ = N := perfectCore_perfect ⊤
  have hNn : N.Normal := by
    have h := normalizer_le_normalizer_perfectCore (⊤ : Subgroup Y)
    rw [normalizer_eq_top_iff.mpr inferInstance] at h
    exact normalizer_eq_top_iff.mp (eq_top_iff.mpr h)
  have hDp := commutator_eq_self_of_simple hD hDnab
  have hρN : N.map ρ = D := by
    rw [hNdef, map_perfectCore, ← MonoidHom.range_eq_map]
    refine le_antisymm ?_ (le_perfectCore_of_perfect hDle hDp)
    exact (perfectCore_le_derivedSeriesOf _ 1).trans hcomm
  have hcen := commute_of_perfect_of_card_four (K := ρ.ker) hNp hker
  let ρN : ↥N →* ↥D := (ρ.comp N.subtype).codRestrict D (fun n => by
    rw [← hρN]
    exact mem_map_of_mem _ n.2)
  have hρNs : Function.Surjective ρN := by
    rintro ⟨d, hd⟩
    rw [← hρN] at hd
    obtain ⟨n, hn, rfl⟩ := hd
    exact ⟨⟨n, hn⟩, rfl⟩
  have hcD : center ↥D = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥D) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hDnab
      have hb : b ∈ center ↥D := by rw [h]; exact mem_top b
      exact hab ((mem_center_iff.mp hb) a)
  have hkerN : ρN.ker = center ↥N := by
    ext x
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro hx g
      have hxk : (x : Y) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hx
      have h1 := hcen g g.2 x hxk
      apply Subtype.ext
      simp only [coe_mul]
      calc (g : Y) * x = (g : Y) * x * (g : Y)⁻¹ * g := by group
        _ = x * g := by rw [h1]
    · intro hx
      have h1 : ρN x ∈ center ↥D := by
        rw [mem_center_iff]
        intro d
        obtain ⟨g, rfl⟩ := hρNs d
        rw [← map_mul, ← map_mul, hx g]
      rw [hcD, mem_bot] at h1
      exact h1
  let e : ↥N ⧸ center ↥N ≃* ↥D :=
    (QuotientGroup.quotientMulEquivOfEq hkerN.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρN hρNs)
  refine ⟨N, hNn, ⟨isPerfect_iff.mpr hNp, @MulEquiv.isSimpleGroup _ _ _ _ hD e, ?_⟩, hρN⟩
  obtain ⟨a, b, hab⟩ := hDnab
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h' := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'

omit [Finite T] in
theorem eq_of_isComponent (ρ : Y →* T) {D : Subgroup T} (hD : IsSimpleGroup ↥D)
    (hDnab : ∃ a b : ↥D, a * b ≠ b * a)
    (hcomm : ⁅ρ.range, ρ.range⁆ ≤ D) (hker : Nat.card ρ.ker = 4) {N J : Subgroup Y}
    (hN : IsComponent N) (hNρ : N.map ρ = D) (hJ : IsComponent J) : J = N := by
  rcases LocalCores.distinct_components_commute hJ hN with h | h
  · exact h
  exfalso
  have hJp : ⁅J, J⁆ = J := isPerfect_iff.mp hJ.1.1
  have hJC : ∀ x ∈ J, ∀ d ∈ D, ρ x * d = d * ρ x := by
    intro x hx d hd
    rw [← hNρ] at hd
    obtain ⟨n, hn, rfl⟩ := hd
    have h1 : ⁅x, n⁆ = 1 := by
      have := commutator_mem_commutator hx hn
      rwa [h, mem_bot] at this
    rw [← map_mul, ← map_mul, (commutatorElement_eq_one_iff_mul_comm.mp h1)]
  have hab : ∀ x ∈ J, ∀ y ∈ J, ρ x * ρ y = ρ y * ρ x := by
    intro x hx y hy
    have hc : ⁅ρ x, ρ y⁆ ∈ D := hcomm (commutator_mem_commutator ⟨x, rfl⟩ ⟨y, rfl⟩)
    have hcen : ∀ d ∈ D, ⁅ρ x, ρ y⁆ * d = d * ⁅ρ x, ρ y⁆ := by
      intro d hd
      have h1 := hJC x hx d hd
      have h2 := hJC y hy d hd
      have h3 := hJC x hx d⁻¹ (inv_mem hd)
      have h4 := hJC y hy d⁻¹ (inv_mem hd)
      rw [commutatorElement_def]
      have e1 : d * ρ x = ρ x * d := h1.symm
      have e2 : d * ρ y = ρ y * d := h2.symm
      calc ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ * d
          = ρ x * ρ y * (ρ x)⁻¹ * ((ρ y)⁻¹ * d) := by group
        _ = ρ x * ρ y * (ρ x)⁻¹ * (d * (ρ y)⁻¹) := by
          rw [show (ρ y)⁻¹ * d = d * (ρ y)⁻¹ by
            calc (ρ y)⁻¹ * d = (ρ y)⁻¹ * (d * ρ y) * (ρ y)⁻¹ := by group
              _ = (ρ y)⁻¹ * (ρ y * d) * (ρ y)⁻¹ := by rw [e2]
              _ = d * (ρ y)⁻¹ := by group]
        _ = ρ x * ρ y * ((ρ x)⁻¹ * d) * (ρ y)⁻¹ := by group
        _ = ρ x * ρ y * (d * (ρ x)⁻¹) * (ρ y)⁻¹ := by
          rw [show (ρ x)⁻¹ * d = d * (ρ x)⁻¹ by
            calc (ρ x)⁻¹ * d = (ρ x)⁻¹ * (d * ρ x) * (ρ x)⁻¹ := by group
              _ = (ρ x)⁻¹ * (ρ x * d) * (ρ x)⁻¹ := by rw [e1]
              _ = d * (ρ x)⁻¹ := by group]
        _ = ρ x * (ρ y * d) * (ρ x)⁻¹ * (ρ y)⁻¹ := by group
        _ = ρ x * (d * ρ y) * (ρ x)⁻¹ * (ρ y)⁻¹ := by rw [e2]
        _ = (ρ x * d) * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ := by group
        _ = (d * ρ x) * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹ := by rw [e1]
        _ = d * (ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹) := by group
    have hcD : center ↥D = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥D) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hDnab
        have hb : b ∈ center ↥D := by rw [h]; exact mem_top b
        exact hab ((mem_center_iff.mp hb) a)
    have hz : (⟨⁅ρ x, ρ y⁆, hc⟩ : ↥D) ∈ center ↥D := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (hcen g g.2).symm
    rw [hcD, mem_bot] at hz
    have hz' : ⁅ρ x, ρ y⁆ = 1 := congrArg Subtype.val hz
    exact commutatorElement_eq_one_iff_mul_comm.mp hz'
  have hJk : J ≤ ρ.ker := by
    intro x hx
    rw [← hJp] at hx
    have hle : ⁅J, J⁆ ≤ ρ.ker := by
      rw [commutator_le]
      intro a ha b hb
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab a ha b hb
    exact hle hx
  have hJab : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x := by
    have hcen4 := commute_of_perfect_of_card_four (K := ρ.ker) hJp hker
    intro x hx y hy
    have h1 := hcen4 x hx y (hJk hy)
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h1]
  have : Nontrivial ↥J := LocalCores.isQuasisimple_nontrivial hJ.1
  have hJbot : ⁅J, J⁆ = ⊥ := by
    rw [eq_bot_iff, commutator_le]
    intro a ha b hb
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hJab a ha b hb
  rw [hJp] at hJbot
  rw [hJbot] at this
  exact not_nontrivial_iff_subsingleton.mpr inferInstance this

end CFSG.ComponentClassification.GrSLit.HeLay

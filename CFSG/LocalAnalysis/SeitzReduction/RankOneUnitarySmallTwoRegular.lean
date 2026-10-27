module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoDegree
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoForm

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

theorem eq_one_or_eq_of_dvd {f k N : ℕ} (hf : 2 ≤ f)
    (hN : N = 1 + k * (((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))) (hdvd : N ∣ (2 ^ f) ^ 2) :
    N = 1 ∨ N = (2 ^ f) ^ 2 := by
  set q := 2 ^ f with hq
  set g := Nat.gcd 3 (q + 1) with hgdef
  set m := (q ^ 2 - 1) / g with hm
  have hq4 : 4 ≤ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQ : 16 ≤ q ^ 2 := by nlinarith
  have hg3 : g ∣ 3 := Nat.gcd_dvd_left 3 (q + 1)
  have hgq : g ∣ q ^ 2 - 1 := by
    rw [sq_sub_one_eq_sub_one_mul_add_one q (by omega)]
    exact Dvd.dvd.mul_left (Nat.gcd_dvd_right 3 (q + 1)) _
  have hgm : g * m = q ^ 2 - 1 := Nat.mul_div_cancel' hgq
  have hg : g = 1 ∨ g = 3 := (Nat.dvd_prime Nat.prime_three).mp hg3
  have hNle : N ≤ q ^ 2 := Nat.le_of_dvd (by positivity) hdvd
  have hm0 : 0 < m := by
    rcases hg with h1 | h1 <;> rw [h1] at hgm <;> omega
  have hkg : k ≤ g := by
    by_contra hk
    push Not at hk
    have : (g + 1) * m ≤ k * m := Nat.mul_le_mul_right m hk
    have e : (g + 1) * m = g * m + m := by ring
    omega
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show N ∣ 2 ^ (2 * f) by rw [pow_mul', ← hq]; exact hdvd)
  rcases hg with h1 | h1
  · rw [h1] at hkg hgm
    interval_cases k
    · left; omega
    · right; omega
  · rw [h1] at hkg hgm
    interval_cases k
    · left; omega
    · exfalso
      have h3 : ((2 ^ f) ^ 2 + 2) / 3 = 2 ^ j := by
        rw [← hq, ← hj, hN]
        omega
      exact (not_two_pow_or_of_degree hf).1 ⟨j, h3⟩
    · exfalso
      rcases j with _ | j
      · omega
      · have : 2 ^ (j + 1) % 2 = 0 := by rw [pow_succ, Nat.mul_mod_left]
        omega
    · right; omega

theorem card_orbit_dvd_of_normal {Ω : Type*} [Finite Ω] (H H₀ : Subgroup (Equiv.Perm Ω))
    (x₀ : Ω) (htrans : ∀ X, ∃ π ∈ H, π x₀ = X)
    (hn : ∀ π ∈ H, ∀ π₀ ∈ H₀, π * π₀ * π⁻¹ ∈ H₀) :
    Nat.card (MulAction.orbit H₀ x₀) ∣ Nat.card Ω := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have hsize : ∀ X : Ω, Nat.card (MulAction.orbit H₀ X) = Nat.card (MulAction.orbit H₀ x₀) := by
    intro X
    obtain ⟨π, hπ, rfl⟩ := htrans X
    refine Nat.card_congr
      { toFun := fun Y => ⟨π⁻¹ Y, ?_⟩
        invFun := fun Y => ⟨π Y, ?_⟩
        left_inv := fun Y => by simp
        right_inv := fun Y => by simp }
    · obtain ⟨⟨π₀, hπ₀⟩, hY⟩ := MulAction.mem_orbit_iff.mp Y.2
      refine MulAction.mem_orbit_iff.mpr ⟨⟨π⁻¹ * π₀ * π, ?_⟩, ?_⟩
      · have := hn π⁻¹ (inv_mem hπ) π₀ hπ₀
        rwa [inv_inv] at this
      · rw [← hY]
        show (π⁻¹ * π₀ * π) x₀ = π⁻¹ (π₀ (π x₀))
        simp [Equiv.Perm.mul_apply]
    · obtain ⟨⟨π₀, hπ₀⟩, hY⟩ := MulAction.mem_orbit_iff.mp Y.2
      refine MulAction.mem_orbit_iff.mpr ⟨⟨π * π₀ * π⁻¹, hn π hπ π₀ hπ₀⟩, ?_⟩
      rw [← hY]
      show (π * π₀ * π⁻¹) (π x₀) = π (π₀ x₀)
      simp [Equiv.Perm.mul_apply]
  let : Fintype (Quotient (MulAction.orbitRel H₀ Ω)) := Fintype.ofFinite _
  have e := Nat.card_congr (MulAction.selfEquivSigmaOrbits H₀ Ω)
  rw [Nat.card_sigma] at e
  rw [e, Finset.sum_congr rfl (fun ω _ => hsize ω.out), Finset.sum_const, smul_eq_mul]
  exact Dvd.intro_left _ rfl

namespace AffineCoords

variable {Ω : Type*} {E : Type*} [AddCommGroup E] (κ : Ω → E) (x₀ : Ω)

omit [AddCommGroup E] in
theorem perm_apply_inv (π : Equiv.Perm Ω) (X : Ω) : π (π⁻¹ X) = X := by
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

@[expose] def trans (hx₀ : κ x₀ = 0) (H : Subgroup (Equiv.Perm Ω)) : Subgroup (Equiv.Perm Ω) where
  carrier := {π | π ∈ H ∧ ∀ X, κ (π X) = κ X + κ (π x₀)}
  mul_mem' := by
    rintro π π' ⟨hπ, hπX⟩ ⟨hπ', hπ'X⟩
    refine ⟨mul_mem hπ hπ', fun X => ?_⟩
    simp only [Equiv.Perm.mul_apply]
    rw [hπX (π' X), hπ'X X, hπX (π' x₀)]
    abel
  one_mem' := ⟨one_mem H, fun X => by simp [hx₀]⟩
  inv_mem' := by
    rintro π ⟨hπ, hπX⟩
    refine ⟨inv_mem hπ, fun X => ?_⟩
    have h1 := hπX (π⁻¹ X)
    have h2 := hπX (π⁻¹ x₀)
    rw [perm_apply_inv] at h1 h2
    rw [hx₀] at h2
    have e1 : κ (π⁻¹ X) = κ X - κ (π x₀) := by rw [h1]; abel
    have e2 : κ (π⁻¹ x₀) = -κ (π x₀) := by
      rw [eq_neg_iff_add_eq_zero, h2]
    rw [e1, e2, sub_eq_add_neg]

variable {κ x₀}

theorem trans_normal {hx₀ : κ x₀ = 0} {H : Subgroup (Equiv.Perm Ω)}
    (haff : ∀ π ∈ H, ∃ φ : E →+ E, ∀ X, κ (π X) = φ (κ X) + κ (π x₀)) :
    ((trans κ x₀ hx₀ H).subgroupOf H).Normal := by
  constructor
  rintro ⟨π, hπH⟩ hπ ⟨h, hh⟩
  rw [mem_subgroupOf] at hπ ⊢
  obtain ⟨-, hπX⟩ := hπ
  obtain ⟨φ, hφ⟩ := haff h hh
  have key : ∀ X, κ ((h * π * h⁻¹) X) = κ X + φ (κ (π x₀)) := by
    intro X
    simp only [Equiv.Perm.mul_apply]
    rw [hφ, hπX, map_add]
    have h3 := hφ (h⁻¹ X)
    rw [perm_apply_inv] at h3
    rw [h3]
    show φ (κ (h⁻¹ X)) + φ (κ (π x₀)) + κ (h x₀) = φ (κ (h⁻¹ X)) + κ (h x₀) + φ (κ (π x₀))
    abel
  refine ⟨mul_mem (mul_mem hh hπH) (inv_mem hh), fun X => ?_⟩
  show κ ((h * π * h⁻¹) X) = κ X + κ ((h * π * h⁻¹) x₀)
  rw [key X, key x₀, hx₀, zero_add]

theorem trans_regular [DecidableEq E] {hx₀ : κ x₀ = 0} {H : Subgroup (Equiv.Perm Ω)}
    (hκ : Function.Injective κ)
    (hall : ∀ c : E, ∃ π ∈ trans κ x₀ hx₀ H, κ (π x₀) = c) (a b : Ω) :
    ∃! x : trans κ x₀ hx₀ H, (x : Equiv.Perm Ω) a = b := by
  obtain ⟨π, hπ, hπc⟩ := hall (κ b - κ a)
  have hπa : π a = b := hκ (by rw [hπ.2 a, hπc]; abel)
  refine ⟨⟨π, hπ⟩, hπa, fun ⟨π', hπ'⟩ hπ'a => ?_⟩
  have hc : κ (π' x₀) = κ (π x₀) := by
    have h1 := hπ'.2 a
    rw [hπ'a] at h1
    rw [hπc, h1]
    abel
  apply Subtype.ext
  ext X
  exact congrArg (fun f => f) (hκ (by rw [hπ'.2 X, hπ.2 X, hc]))

end AffineCoords

theorem hasRegularNormalSubgroup_of_affine {Ω : Type*} [Finite Ω] {E : Type*} [Field E]
    [Finite E] [CharP E 2] {σ : E →+* E} {f : ℕ} (hf : 2 ≤ f) (hσ : ∀ x, σ x = x ^ (2 ^ f))
    (hE : Nat.card E = (2 ^ f) ^ 2) (κ : Ω → E) (hκ : Function.Bijective κ) (x₀ : Ω)
    (hx₀ : κ x₀ = 0) (H : Subgroup (Equiv.Perm Ω)) (htrans : ∀ X, ∃ π ∈ H, π x₀ = X)
    (haff : ∀ π ∈ H, ∃ φ : E →+ E, Function.Injective φ ∧ ∀ X, κ (π X) = φ (κ X) + κ (π x₀))
    {μ : E} (hμord : orderOf μ = ((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1))
    {δ : Equiv.Perm Ω} (hδH : δ ∈ H) (hδ : ∀ X, κ (δ X) = μ * κ X)
    (H₀ : Subgroup (Equiv.Perm Ω)) (hH₀H : H₀ ≤ H) (hn : ∀ π ∈ H, ∀ π₀ ∈ H₀, π * π₀ * π⁻¹ ∈ H₀)
    (hform : ∀ π ∈ H₀, ∃ φ : E →+ E, (∀ X, κ (π X) = φ (κ X) + κ (π x₀)) ∧
      ∀ a b, TraceForm.form σ (φ a) (φ b) = TraceForm.form σ a b)
    {π₁ : Equiv.Perm Ω} (hπ₁ : π₁ ∈ H₀) (hπ₁1 : π₁ ≠ 1) :
    HasRegularNormalSubgroup H := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  have : Fintype E := Fintype.ofFinite E
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdvd : 2 ^ f - 1 ∣ orderOf μ := by
    rw [hμord]
    exact sub_one_dvd_div_gcd (2 ^ f) (by omega)
  have hμpos : orderOf μ ≠ 0 := by
    intro h0
    have h1 := hμord
    rw [h0] at h1
    have h2 : (2 ^ f) ^ 2 - 1 < Nat.gcd 3 (2 ^ f + 1) :=
      (Nat.div_eq_zero_iff_lt (Nat.gcd_pos_of_pos_left _ (by norm_num))).mp h1.symm
    have h3 : Nat.gcd 3 (2 ^ f + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have h4 : 2 ^ f ≤ (2 ^ f) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at hμpos
    exact hμpos (orderOf_eq_zero_iff'.mpr fun n hn h1 => by
      rw [zero_pow hn.ne'] at h1; exact zero_ne_one h1)
  have hF : Nat.card {x : E // σ x = x} = 2 ^ f :=
    LineCount.card_fixed_of_orderOf hσ (by omega) (orderOf_pow_orderOf_div hμpos hdvd)
  have hprim : IsPrimitiveRoot μ (orderOf μ) := IsPrimitiveRoot.orderOf μ
  have hEcard' : Nat.card E = 2 ^ (f * 2) := by rw [hE, pow_mul]
  have hcardΩ : Nat.card Ω = (2 ^ f) ^ 2 := by
    rw [← hE]
    exact Nat.card_congr (Equiv.ofBijective κ hκ)
  have hδx₀ : δ x₀ = x₀ := hκ.1 (by rw [hδ, hx₀, mul_zero])
  have haff' : ∀ π ∈ H, ∃ φ : E →+ E, ∀ X, κ (π X) = φ (κ X) + κ (π x₀) := fun π hπ => by
    obtain ⟨φ, -, hφ⟩ := haff π hπ
    exact ⟨φ, hφ⟩
  set Tr := AffineCoords.trans κ x₀ hx₀ H with hTr
  set V : Finset E := Finset.univ.filter fun c => ∃ π ∈ Tr, κ (π x₀) = c with hV
  have hV0 : (0 : E) ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ _, 1, one_mem _, by simp [hx₀]⟩
  have hVadd : ∀ a ∈ V, ∀ b ∈ V, a + b ∈ V := by
    intro a ha b hb
    obtain ⟨π, hπ, rfl⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨π', hπ', rfl⟩ := (Finset.mem_filter.mp hb).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, π * π', mul_mem hπ hπ', ?_⟩
    rw [Equiv.Perm.mul_apply, hπ.2, add_comm]
  have hVμ : ∀ a ∈ V, μ * a ∈ V := by
    intro a ha
    obtain ⟨π, hπ, rfl⟩ := (Finset.mem_filter.mp ha).2
    have hc := AffineCoords.trans_normal (hx₀ := hx₀) haff'
    have hmem := hc.conj_mem ⟨π, hπ.1⟩ (by rw [mem_subgroupOf]; exact hπ) ⟨δ, hδH⟩
    rw [mem_subgroupOf] at hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, δ * π * δ⁻¹, hmem, ?_⟩
    have hδinv : δ⁻¹ x₀ = x₀ := by
      conv_lhs => rw [← hδx₀]
      rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    simp only [Equiv.Perm.mul_apply]
    rw [hδinv, hδ]
  have hVcard := LineCount.card_erase_zero_of_isPrimitiveRoot hprim (Nat.pos_of_ne_zero hμpos) hVμ
  rw [Finset.card_erase_of_mem hV0] at hVcard
  obtain ⟨j, hj⟩ := LineCount.exists_card_eq_two_pow hEcard' hV0 hVadd
  have hVle : V.card ≤ (2 ^ f) ^ 2 := by
    rw [← hE, Nat.card_eq_fintype_card]
    exact Finset.card_le_univ V
  have hVdvd : V.card ∣ (2 ^ f) ^ 2 := by
    rw [hj, ← pow_mul]
    refine Nat.pow_dvd_pow 2 ?_
    have : 2 ^ j ≤ 2 ^ (f * 2) := by rw [← hj, pow_mul]; exact hVle
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have hVk : V.card = 1 + ((V.erase 0).image fun z => z ^ orderOf μ).card *
      (((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) := by
    have h1 : 1 ≤ V.card := Finset.card_pos.mpr ⟨0, hV0⟩
    rw [← hμord, ← hVcard]
    omega
  rcases eq_one_or_eq_of_dvd hf hVk hVdvd with hV1 | hVq
  swap
  ·
    have hVuniv : V = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hVq, ← hE, Nat.card_eq_fintype_card]
    refine ⟨Tr, fun π hπ => hπ.1, AffineCoords.trans_normal haff', fun a b => ?_⟩
    refine AffineCoords.trans_regular hκ.1 (fun c => ?_) a b
    have hcV : c ∈ V := by rw [hVuniv]; exact Finset.mem_univ c
    exact (Finset.mem_filter.mp hcV).2
  · exfalso
    have htriv : ∀ π ∈ Tr, π = 1 := by
      intro π hπ
      have hc : κ (π x₀) ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_univ _, π, hπ, rfl⟩
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hV1
      have h0 : κ (π x₀) = 0 := by
        rw [ha] at hc hV0
        rw [Finset.mem_singleton.mp hc, Finset.mem_singleton.mp hV0]
      ext X
      have h1 := hπ.2 X
      rw [h0, add_zero] at h1
      rw [Equiv.Perm.one_apply]
      exact hκ.1 h1
    set e := Equiv.ofBijective κ hκ with he
    let lin : Equiv.Perm Ω → E → E := fun π a => κ (π (e.symm a)) - κ (π x₀)
    have hlin : ∀ π, ∀ φ : E →+ E, (∀ X, κ (π X) = φ (κ X) + κ (π x₀)) → ∀ a, lin π a = φ a := by
      intro π φ hφ a
      have hea : κ (e.symm a) = a := e.apply_symm_apply a
      show κ (π (e.symm a)) - κ (π x₀) = φ a
      rw [hφ, hea]
      abel
    have hlinmul : ∀ π ∈ H, ∀ π' ∈ H, ∀ a, lin (π * π') a = lin π (lin π' a) := by
      intro π hπ π' hπ' a
      obtain ⟨φ, -, hφ⟩ := haff π hπ
      obtain ⟨φ', -, hφ'⟩ := haff π' hπ'
      have hφφ : ∀ X, κ ((π * π') X) = (φ.comp φ') (κ X) + κ ((π * π') x₀) := by
        intro X
        simp only [Equiv.Perm.mul_apply, AddMonoidHom.comp_apply]
        rw [hφ, hφ', hφ (π' x₀), hφ' x₀, hx₀, map_zero, zero_add, map_add]
        abel
      rw [hlin _ _ hφφ, hlin _ _ hφ, hlin _ _ hφ']
      rfl
    have hlinone : ∀ a, lin 1 a = a := by
      intro a
      have hea : κ (e.symm a) = a := e.apply_symm_apply a
      show κ ((1 : Equiv.Perm Ω) (e.symm a)) - κ ((1 : Equiv.Perm Ω) x₀) = a
      rw [Equiv.Perm.one_apply, Equiv.Perm.one_apply, hx₀, sub_zero, hea]
    have hlinbij : ∀ π ∈ H, Function.Bijective (lin π) := by
      intro π hπ
      obtain ⟨φ, hφi, hφ⟩ := haff π hπ
      have hinj : Function.Injective (lin π) := fun a b hab =>
        hφi (by rw [← hlin π φ hφ a, ← hlin π φ hφ b, hab])
      exact Finite.injective_iff_bijective.mp hinj
    have hlinid : ∀ π ∈ H, (∀ a, lin π a = a) → π = 1 := by
      intro π hπ hid
      apply htriv
      refine ⟨hπ, fun X => ?_⟩
      have h1 := hid (κ X)
      have hX : e.symm (κ X) = X := e.symm_apply_apply X
      change κ (π (e.symm (κ X))) - κ (π x₀) = κ X at h1
      rw [hX] at h1
      linear_combination h1
    have hOdvd : Nat.card (MulAction.orbit H₀ x₀) ∣ (2 ^ f) ^ 2 :=
      hcardΩ ▸ card_orbit_dvd_of_normal H H₀ x₀ htrans hn
    set SO : Finset E := (Finset.univ.filter fun X => X ∈ MulAction.orbit H₀ x₀).image κ with hSO
    have hSOcard : SO.card = Nat.card (MulAction.orbit H₀ x₀) := by
      rw [hSO, Finset.card_image_of_injective _ hκ.1, Nat.card_eq_fintype_card,
        Fintype.card_subtype]
    have hSO0 : (0 : E) ∈ SO := Finset.mem_image.mpr
      ⟨x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, MulAction.mem_orbit_self x₀⟩, hx₀⟩
    have hSOμ : ∀ c ∈ SO, μ * c ∈ SO := by
      intro c hc
      obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨⟨π₀, hπ₀⟩, rfl⟩ := MulAction.mem_orbit_iff.mp (Finset.mem_filter.mp hX).2
      refine Finset.mem_image.mpr ⟨δ (π₀ x₀), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        MulAction.mem_orbit_iff.mpr ⟨⟨δ * π₀ * δ⁻¹, hn δ hδH π₀ hπ₀⟩, ?_⟩⟩, hδ _⟩
      have hδinv : δ⁻¹ x₀ = x₀ := by
        conv_lhs => rw [← hδx₀]
        rw [← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
      show (δ * π₀ * δ⁻¹) x₀ = δ (π₀ x₀)
      simp only [Equiv.Perm.mul_apply, hδinv]
    have hSOk := LineCount.card_erase_zero_of_isPrimitiveRoot hprim (Nat.pos_of_ne_zero hμpos)
      hSOμ
    rw [Finset.card_erase_of_mem hSO0] at hSOk
    have hSOk' : SO.card = 1 + ((SO.erase 0).image fun z => z ^ orderOf μ).card *
        (((2 ^ f) ^ 2 - 1) / Nat.gcd 3 (2 ^ f + 1)) := by
      have h1 : 1 ≤ SO.card := Finset.card_pos.mpr ⟨0, hSO0⟩
      rw [← hμord, ← hSOk]
      omega
    rcases eq_one_or_eq_of_dvd hf hSOk' (hSOcard ▸ hOdvd) with hO1 | hOq
    ·
      have hfix : ∀ π₀ ∈ H₀, π₀ x₀ = x₀ := by
        intro π₀ hπ₀
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hO1
        have hmem : κ (π₀ x₀) ∈ SO := Finset.mem_image.mpr ⟨π₀ x₀, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, MulAction.mem_orbit_iff.mpr ⟨⟨π₀, hπ₀⟩, rfl⟩⟩, rfl⟩
        rw [ha] at hmem hSO0
        exact hκ.1 (by rw [Finset.mem_singleton.mp hmem, ← Finset.mem_singleton.mp hSO0, hx₀])
      apply hπ₁1
      ext X
      obtain ⟨π, hπ, rfl⟩ := htrans X
      have hconj : π⁻¹ * π₁ * π ∈ H₀ := by
        have := hn π⁻¹ (inv_mem hπ) π₁ hπ₁
        rwa [inv_inv] at this
      have h1 := hfix _ hconj
      simp only [Equiv.Perm.mul_apply] at h1
      rw [Equiv.Perm.one_apply]
      have h2 := congrArg π h1
      rwa [AffineCoords.perm_apply_inv] at h2
    ·
      have hdvdH₀ : 2 ^ (f * 2) ∣ Nat.card H₀ := by
        have h1 := MulAction.index_stabilizer H₀ x₀
        rw [← Nat.card_coe_set_eq, ← hSOcard, hOq, ← pow_mul] at h1
        rw [← h1]
        exact Subgroup.index_dvd_card _
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvdH₀
      let ρ : K →* Equiv.Perm E :=
        { toFun := fun g => Equiv.ofBijective (lin ((g : H₀) : Equiv.Perm Ω))
            (hlinbij _ (hH₀H (g : H₀).2))
          map_one' := by
            ext a
            show lin (((1 : K) : H₀) : Equiv.Perm Ω) a = a
            simp only [OneMemClass.coe_one]
            exact hlinone a
          map_mul' := fun g g' => by
            ext a
            show lin (((g * g' : K) : H₀) : Equiv.Perm Ω) a =
              lin ((g : H₀) : Equiv.Perm Ω) (lin ((g' : H₀) : Equiv.Perm Ω) a)
            simp only [MulMemClass.coe_mul]
            exact hlinmul _ (hH₀H (g : H₀).2) _ (hH₀H (g' : H₀).2) a }
      have hρ : ∀ (g : K) a, ρ g a = lin ((g : H₀) : Equiv.Perm Ω) a := fun g a => rfl
      have hρinj : Function.Injective ρ := by
        rw [injective_iff_map_eq_one]
        intro g hg
        have h1 : ((g : H₀) : Equiv.Perm Ω) = 1 :=
          hlinid _ (hH₀H (g : H₀).2) fun a => by rw [← hρ, hg, Equiv.Perm.one_apply]
        exact Subtype.ext (Subtype.ext h1)
      have hρadd : ∀ g a b, ρ g (a + b) = ρ g a + ρ g b := by
        intro g a b
        obtain ⟨φ, hφ, -⟩ := hform _ (g : H₀).2
        rw [hρ, hρ, hρ, hlin _ φ hφ, hlin _ φ hφ, hlin _ φ hφ, map_add]
      have hρform : ∀ g a b, TraceForm.form σ (ρ g a) (ρ g b) = TraceForm.form σ a b := by
        intro g a b
        obtain ⟨φ, hφ, hφf⟩ := hform _ (g : H₀).2
        rw [hρ, hρ, hlin _ φ hφ, hlin _ φ hφ, hφf]
      have hle := TraceForm.card_le_of_form hσ (by omega) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        hE hF (IsPGroup.of_card hK) ρ hρinj hρadd hρform
      rw [hK] at hle
      have h1 : 2 ^ f < 2 ^ (f * 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega

theorem U3RootCoords.commutator_coords {G : Type*} [Group G] {E : Type*} [Field E] [CharP E 2]
    {T₁ : Subgroup G} {σ : E →+* E} {u v : G → E} (hc : U3RootCoords T₁ σ u v) {y y' : G}
    (hy : y ∈ T₁) (hy' : y' ∈ T₁) :
    u (y * y' * y⁻¹ * y'⁻¹) = 0 ∧
      v (y * y' * y⁻¹ * y'⁻¹) = TraceForm.form σ (u y) (u y') := by
  have hcT : y * y' * y⁻¹ * y'⁻¹ ∈ T₁ :=
    mul_mem (mul_mem (mul_mem hy hy') (inv_mem hy)) (inv_mem hy')
  have hu : u (y * y' * y⁻¹ * y'⁻¹) = 0 := by
    rw [hc.mul_u _ (mul_mem (mul_mem hy hy') (inv_mem hy)) _ (inv_mem hy'),
      hc.mul_u _ (mul_mem hy hy') _ (inv_mem hy), hc.mul_u _ hy _ hy', hc.u_inv hy,
      hc.u_inv hy']
    ring
  refine ⟨hu, ?_⟩
  have e : y * y' = (y * y' * y⁻¹ * y'⁻¹) * (y' * y) := by group
  have h1 := congrArg v e
  rw [hc.mul_v _ hy _ hy', hc.mul_v _ hcT _ (mul_mem hy' hy), hc.mul_v _ hy' _ hy, hu,
    zero_mul, sub_zero] at h1
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  rw [TraceForm.form]
  linear_combination -h1 - (u y * σ (u y')) * h2

theorem commutator_mul_mul_eq_of_central_factors {G : Type*} [Group G] {a b c d : G}
    (hbc : b * c = c * b) (hbd : b * d = d * b) (hda : d * a = a * d) :
    a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = a * c * a⁻¹ * c⁻¹ := by
  have h1 : b * c * d * b⁻¹ = c * d := by
    calc b * c * d * b⁻¹ = c * (b * d) * b⁻¹ := by rw [hbc]; group
      _ = c * d := by rw [hbd]; group
  have h3 : d * a⁻¹ = a⁻¹ * d := by
    calc d * a⁻¹ = a⁻¹ * (a * d) * a⁻¹ := by group
      _ = a⁻¹ * (d * a) * a⁻¹ := by rw [hda]
      _ = a⁻¹ * d := by group
  have h2 : d * a⁻¹ * d⁻¹ = a⁻¹ := by
    calc d * a⁻¹ * d⁻¹ = a⁻¹ * d * d⁻¹ := by rw [h3]
      _ = a⁻¹ := by group
  calc a * b * (c * d) * (a * b)⁻¹ * (c * d)⁻¹ = a * (b * c * d * b⁻¹) * a⁻¹ * d⁻¹ * c⁻¹ := by
        group
    _ = a * c * (d * a⁻¹ * d⁻¹) * c⁻¹ := by rw [h1]; group
    _ = a * c * a⁻¹ * c⁻¹ := by rw [h2]

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

section Certificates

theorem hasRegularNormalSubgroup_of_ncard_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {R₂ : Subgroup G}
    (hR : U3R2 G L (szT₁ L T) R₂ t f) (hN : (u3Omega L T R₂ t).ncard = (2 ^ f) ^ 2) :
    HasRegularNormalSubgroup (u3OmegaAction L T R₂ t).range := by
  classical
  obtain ⟨E, hE, hEfin, hch, σ, hEcard, hσ, u, v, hc, hA₁u, d, hdL, hdT, μ, hμ0, hμord, hdμ⟩ :=
    h.exists_rootCoords_cartan_of_card_sylow hS2
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨κ, hκinj, hrep, hκ, haff⟩ := h.exists_kappa_of_card_sylow hS2 hR hc hA₁u
  obtain ⟨-, -, -, hNA, hNR₂, -⟩ := h.u3R2_canonical_of_card_sylow hS2 hR
  obtain ⟨-, -, -, hNR₁⟩ := h.char_of_card_sylow hS2 hR
  have hfin : (u3Omega L T R₂ t).Finite :=
    (Set.finite_range (u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁)).subset
      (h.u3Omega_subset_range_of_card_sylow hS2 hR)
  have : Finite (u3Omega L T R₂ t) := hfin.to_subtype
  have : Fintype (u3Omega L T R₂ t) := Fintype.ofFinite _
  have hcardΩ : Nat.card (u3Omega L T R₂ t) = (2 ^ f) ^ 2 := by rw [Nat.card_coe_set_eq, hN]
  have hκbij : Function.Bijective κ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hκinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardΩ, hEcard]
  set x₀ : u3Omega L T R₂ t := ⟨R₂ ⊔ zpowers t, sup_zpowers_mem_u3Omega L T R₂ t⟩ with hx₀
  have hκx₀ : κ x₀ = 0 := by
    rw [hκ x₀ 1 (one_mem _) (by rw [one_mul]), hc.u_one]
  have htrans : ∀ X, ∃ π ∈ (u3OmegaAction L T R₂ t).range, π x₀ = X := by
    intro X
    obtain ⟨y, hy, hyX⟩ := X.2
    refine ⟨u3OmegaAction L T R₂ t ⟨y, hy⟩, ⟨_, rfl⟩, Subtype.ext ?_⟩
    rw [u3OmegaAction_apply]
    exact hyX.symm
  have haffH : ∀ π ∈ (u3OmegaAction L T R₂ t).range, ∃ φ : E →+ E, Function.Injective φ ∧
      ∀ X, κ (π X) = φ (κ X) + κ (π x₀) := by
    rintro π ⟨y, rfl⟩
    obtain ⟨φ, hφi, -, c, hφc⟩ := haff y
    refine ⟨φ, hφi, fun X => ?_⟩
    rw [hφc X, hφc x₀, hκx₀, map_zero, zero_add]
  have hdt : d * t = t * d := mem_centralizer_iff.mp h.mem d hdL
  have hdA : d ∈ normalizer (szA L T t : Set G) := by
    have hdA₁ : d ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
      normalizer_le_normalizer_inf_centralizer (szT₁ L T) hdT
    have hdtN : d ∈ normalizer ((zpowers t : Subgroup G) : Set G) := by
      refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact ((Commute.zpow_right hdt k).eq).symm
    exact mem_normalizer_sup_of_mem_inf hdA₁ hdtN
  have hdY := hNA hdA
  have hδ : ∀ X, κ (u3OmegaAction L T R₂ t ⟨d, hdY⟩ X) = μ * κ X := by
    intro X
    obtain ⟨w, hw, hXw⟩ := hrep X
    have hdw : d * w * d⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hdT w).mp hw
    have hpt : ((u3OmegaAction L T R₂ t ⟨d, hdY⟩ X : u3Omega L T R₂ t) : Subgroup G) =
        R₂ ⊔ zpowers ((d * w * d⁻¹) * t) := by
      rw [u3OmegaAction_apply, hXw, map_conj_sup_zpowers (hNR₂ hdA)]
      have e : d * (w * t) * d⁻¹ = (d * w * d⁻¹) * t := by
        calc d * (w * t) * d⁻¹ = (d * w * d⁻¹) * (d * t * d⁻¹) := by group
          _ = (d * w * d⁻¹) * t := by rw [hdt, mul_inv_cancel_right]
      rw [e]
    rw [hκ _ _ hdw hpt, hdμ w hw, hκ X w hw hXw]
  have hYA₁ : ∀ y ∈ normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G),
      y ∈ normalizer (szA₁ (szT₁ L T) : Set G) := fun y hy =>
    h.normalizer_sup_le_normalizer_szA₁_of_card_sylow hS2 hR (mem_inf.mp (hNR₁ hy)).1
  set Y₀ := (centralizer (szA₁ (szT₁ L T) : Set G)).subgroupOf
    (normalizer ((szT₁ L T ⊔ R₂ ⊔ zpowers t : Subgroup G) : Set G)) with hY₀
  have hH₀H : Y₀.map (u3OmegaAction L T R₂ t) ≤ (u3OmegaAction L T R₂ t).range :=
    map_le_range _ _
  have hn : ∀ π ∈ (u3OmegaAction L T R₂ t).range, ∀ π₀ ∈ Y₀.map (u3OmegaAction L T R₂ t),
      π * π₀ * π⁻¹ ∈ Y₀.map (u3OmegaAction L T R₂ t) := by
    rintro π ⟨y, rfl⟩ π₀ ⟨y₀, hy₀, rfl⟩
    refine ⟨y * y₀ * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, hY₀, mem_subgroupOf] at hy₀ ⊢
    refine mem_centralizer_iff.mpr fun z hz => ?_
    have hz' : (y : G)⁻¹ * z * y ∈ szA₁ (szT₁ L T) :=
      (mem_normalizer_iff''.mp (hYA₁ y y.2) z).mp hz
    have hc1 := mem_centralizer_iff.mp hy₀ _ hz'
    show z * ((y : G) * y₀ * (y : G)⁻¹) = (y : G) * y₀ * (y : G)⁻¹ * z
    calc z * ((y : G) * y₀ * (y : G)⁻¹) = y * (((y : G)⁻¹ * z * y) * y₀) * (y : G)⁻¹ := by group
      _ = y * (y₀ * ((y : G)⁻¹ * z * y)) * (y : G)⁻¹ := by rw [hc1]
      _ = (y : G) * y₀ * (y : G)⁻¹ * z := by group
  have hform : ∀ π ∈ Y₀.map (u3OmegaAction L T R₂ t), ∃ φ : E →+ E,
      (∀ X, κ (π X) = φ (κ X) + κ (π x₀)) ∧
      ∀ a b, TraceForm.form σ (φ a) (φ b) = TraceForm.form σ a b := by
    rintro π ⟨y₀, hy₀, rfl⟩
    rw [SetLike.mem_coe, hY₀, mem_subgroupOf] at hy₀
    obtain ⟨φ, -, hφ, c, hφc⟩ := haff y₀
    refine ⟨φ, fun X => by rw [hφc X, hφc x₀, hκx₀, map_zero, zero_add], fun a b => ?_⟩
    obtain ⟨w, hw, rfl⟩ := hc.u_surj a
    obtain ⟨w', hw', rfl⟩ := hc.u_surj b
    have hyH := (mem_inf.mp (hNR₁ y₀.2)).1
    obtain ⟨w₁, hw₁, r₁, hr₁, he₁⟩ :=
      hR.mem_sup_iff.mp ((mem_normalizer_iff.mp hyH _).mp (mem_sup_left hw))
    obtain ⟨w₁', hw₁', r₁', hr₁', he₁'⟩ :=
      hR.mem_sup_iff.mp ((mem_normalizer_iff.mp hyH _).mp (mem_sup_left hw'))
    rw [← hφ w hw w₁ hw₁ r₁ hr₁ he₁.symm, ← hφ w' hw' w₁' hw₁' r₁' hr₁' he₁'.symm,
      ← (hc.commutator_coords hw hw').2, ← (hc.commutator_coords hw₁ hw₁').2]
    congr 1
    have hcT : w * w' * w⁻¹ * w'⁻¹ ∈ szT₁ L T :=
      mul_mem (mul_mem (mul_mem hw hw') (inv_mem hw)) (inv_mem hw')
    have hcA : w * w' * w⁻¹ * w'⁻¹ ∈ szA₁ (szT₁ L T) :=
      (hA₁u _ hcT).mpr (hc.commutator_coords hw hw').1
    have hfix : (y₀ : G) * (w * w' * w⁻¹ * w'⁻¹) * (y₀ : G)⁻¹ = w * w' * w⁻¹ * w'⁻¹ := by
      rw [← mem_centralizer_iff.mp hy₀ _ hcA, mul_inv_cancel_right]
    have hconj : (y₀ : G) * (w * w' * w⁻¹ * w'⁻¹) * (y₀ : G)⁻¹ =
        ((y₀ : G) * w * (y₀ : G)⁻¹) * ((y₀ : G) * w' * (y₀ : G)⁻¹) *
          ((y₀ : G) * w * (y₀ : G)⁻¹)⁻¹ * ((y₀ : G) * w' * (y₀ : G)⁻¹)⁻¹ := by group
    rw [← he₁, ← he₁', commutator_mul_mul_eq_of_central_factors (hR.commT₁ w₁' hw₁' r₁ hr₁).symm
      (hR.comm r₁ hr₁ r₁' hr₁') (hR.commT₁ w₁ hw₁ r₁' hr₁').symm, hfix] at hconj
    exact hconj.symm
  obtain ⟨E', hE', hE'fin, hch', σ', -, -, u', v', hc', hA₁u', k, hkA, hkT, s, hs1, hks⟩ :=
    h.exists_rootCoords_fpf_of_card_sylow hS2
  have hkY := hNA (centralizer_le_normalizer _ hkA)
  have hkA₁ : k ∈ centralizer (szA₁ (szT₁ L T) : Set G) :=
    centralizer_le (szA₁_le_szA L T t) hkA
  have hπ₁ : u3OmegaAction L T R₂ t ⟨k, hkY⟩ ∈ Y₀.map (u3OmegaAction L T R₂ t) :=
    ⟨⟨k, hkY⟩, by rw [SetLike.mem_coe, hY₀, mem_subgroupOf]; exact hkA₁, rfl⟩
  have hπ₁1 : u3OmegaAction L T R₂ t ⟨k, hkY⟩ ≠ 1 := by
    intro h1
    have : Nontrivial (u3Omega L T R₂ t) := by
      rw [← Finite.one_lt_card_iff_nontrivial, hcardΩ]
      have : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h.two_le
      nlinarith
    obtain ⟨X, hX⟩ := exists_ne x₀
    obtain ⟨w, hw, hXw⟩ := hrep X
    have hwA : w ∉ szA₁ (szT₁ L T) := by
      intro hwA
      apply hX
      apply Subtype.ext
      rw [hXw, hR.t_comm w hw, sup_zpowers_mul_eq (hR.le hwA)]
    have hkt : k * t = t * k := (mem_centralizer_iff.mp hkA t (mem_szA_right L T t)).symm
    have hkw : k * w * k⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hkT w).mp hw
    have hpt : ((u3OmegaAction L T R₂ t ⟨k, hkY⟩ X : u3Omega L T R₂ t) : Subgroup G) =
        R₂ ⊔ zpowers ((k * w * k⁻¹) * t) := by
      rw [u3OmegaAction_apply, hXw,
        map_conj_sup_zpowers (hNR₂ (centralizer_le_normalizer _ hkA))]
      have e : k * (w * t) * k⁻¹ = (k * w * k⁻¹) * t := by
        calc k * (w * t) * k⁻¹ = (k * w * k⁻¹) * (k * t * k⁻¹) := by group
          _ = (k * w * k⁻¹) * t := by rw [hkt, mul_inv_cancel_right]
      rw [e]
    have hkX : ((u3OmegaAction L T R₂ t ⟨k, hkY⟩ X : u3Omega L T R₂ t) : Subgroup G) =
        (X : Subgroup G) := by rw [h1]; rfl
    have h2 : u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁ (QuotientGroup.mk ⟨w, hw⟩) =
        u3OmegaPoint L T R₂ t hR.le h.mem_centralizer_szT₁
          (QuotientGroup.mk ⟨k * w * k⁻¹, hkw⟩) := by
      rw [u3OmegaPoint_mk, u3OmegaPoint_mk]
      exact (hXw.symm.trans hkX.symm).trans hpt
    have h3 := h.u3OmegaPoint_injective_of_card_sylow hS2 hR h2
    rw [QuotientGroup.eq, mem_subgroupOf] at h3
    have h3' : w⁻¹ * (k * w * k⁻¹) ∈ szA₁ (szT₁ L T) := by simpa using h3
    have h4 := (hA₁u' _ (mul_mem (inv_mem hw) hkw)).mp h3'
    rw [hc'.u_mul_inv hw hkw, hks w hw, sub_eq_zero] at h4
    have hu'w : u' w ≠ 0 := fun h0 => hwA ((hA₁u' w hw).mpr h0)
    exact hs1 (mul_right_cancel₀ hu'w (h4.trans (one_mul _).symm))
  exact hasRegularNormalSubgroup_of_affine h.two_le hσ hEcard κ hκbij x₀ hκx₀ _ htrans haffH
    hμord ⟨⟨d, hdY⟩, rfl⟩ hδ _ hH₀H hn hform hπ₁ hπ₁1

end Certificates

end U3Start

section Certificates

theorem u3OmegaOddRegularInput_holds : U3OmegaOddRegularInput :=
  fun _ _ _ _ _ _ _ _ h hS2 hR _ _ hN => h.hasRegularNormalSubgroup_of_ncard_of_card_sylow hS2 hR hN

end Certificates

end CFSG.SeitzReduction.RankOne

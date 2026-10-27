module

public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerStructure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.DesarguesianPlanes.RootModules
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

section Elementary

variable {G : Type} [Group G]

theorem card_centralizer_conj (g x : G) :
    Nat.card (Subgroup.centralizer ({g * x * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  have h : (Subgroup.centralizer ({x} : Set G)).map (conjHom g) =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, conjHom_apply]
    constructor
    · rintro ⟨z, hz, rfl⟩
      calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
        _ = g * (x * z) * g⁻¹ := by rw [hz]
        _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
    · intro hy
      refine ⟨g⁻¹ * y * g, ?_, by group⟩
      calc g⁻¹ * y * g * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hy]
        _ = x * (g⁻¹ * y * g) := by group
  rw [← h, card_map_conjHom]

theorem mem_normalizer_of_map_eq {H : Subgroup G} {t : G} (h : H.map (conjHom t) = H) :
    t ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      rw [conjHom_apply] at hyx
      have := congrArg (fun z => t⁻¹ * z * t) hyx
      simpa [mul_assoc] using this
    rw [← this]
    exact hy

@[expose] def Inverts (t : G) (H : Subgroup G) : Prop := ∀ x ∈ H, t * x * t⁻¹ = x⁻¹

theorem Inverts.map {t : G} {H : Subgroup G} (h : Inverts t H) (g : G) :
    Inverts (g * t * g⁻¹) (H.map (conjHom g)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [conjHom_apply, show g * t * g⁻¹ * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ =
    g * (t * x * t⁻¹) * g⁻¹ by group, h x hx]
  group

end Elementary

section Field

variable (F : Type) [Field F] [Finite F]

theorem coprime_ringChar_card_sub_one : Nat.Coprime (ringChar F) (Nat.card F - 1) := by
  have : Fintype F := Fintype.ofFinite F
  have hprime : (ringChar F).Prime := CharP.char_is_prime F _
  rw [Nat.Prime.coprime_iff_not_dvd hprime]
  intro hdvd
  have hcard : ringChar F ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact ringChar.dvd (FiniteField.cast_card_eq_zero F)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have : ringChar F ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hcard hdvd
  rw [Nat.sub_sub_self hpos] at this
  exact hprime.one_lt.ne' (Nat.dvd_one.mp this)

theorem exists_card_eq_ringChar_pow : ∃ f : ℕ, 0 < f ∧ Nat.card F = ringChar F ^ f := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F (ringChar F)
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

end Field

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)

omit [Finite F] in
theorem rootUp_neg (c : F) : rootUp φ (-c) = (rootUp φ c)⁻¹ := by
  have h := map_inv (upHom φ) (Multiplicative.ofAdd c)
  simp only [upHom_apply, toAdd_inv, toAdd_ofAdd] at h
  exact h

omit [Finite F] in
theorem rootLow_neg (c : F) : rootLow φ (-c) = (rootLow φ c)⁻¹ := by
  have h := map_inv (lowHom φ) (Multiplicative.ofAdd c)
  simp only [lowHom_apply, toAdd_inv, toAdd_ofAdd] at h
  exact h

omit [Finite F] in
theorem inverts_invJ₁_rootX₁ : Inverts (invJ₁ φ) (rootX₁ φ) := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp hx
  have h := diag_conj_rootUp φ 1 (-1) c
  rw [conjHom_apply] at h
  rw [invJ₁, h, ← rootUp_neg]
  congr 1
  simp

omit [Finite F] in
theorem inverts_invJ₁_rootX₂ : Inverts (invJ₁ φ) (rootX₂ φ) := by
  intro x hx
  obtain ⟨c, rfl⟩ := (mem_rootX₂ φ).mp hx
  have h := diag_conj_rootLow φ 1 (-1) c
  rw [conjHom_apply] at h
  rw [invJ₁, h, ← rootLow_neg]
  congr 1
  simp

section Setting

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

include hZ hZodd h2 in
theorem eq_one_of_isTorus_of_pow_eq_one {x : G} (hx : IsTorus φ x) {k : ℕ}
    (hxk : x ^ (ringChar F ^ k) = 1) : x = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨a, b, rfl⟩ := (isTorus_iff φ hZ hZodd h2 _).mp hx
  have hq := diag_pow_card_sub_one φ a b
  have hcop : Nat.Coprime (ringChar F ^ k) (Fintype.card F - 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact (coprime_ringChar_card_sub_one F).pow_left k
  have := pow_gcd_eq_one.mpr ⟨hxk, hq⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem inverts_invJ₂_rootX₁ : Inverts (invJ₂ φ) (rootX₁ φ) := by
  intro x hx
  have hc : J * x⁻¹ = x⁻¹ * J := commute_J_of_mem_rootX₁ ((rootX₁ φ).inv_mem hx)
  rw [invJ₂_eq φ hZ hZodd h2 hJ]
  calc J * invJ₁ φ * x * (J * invJ₁ φ)⁻¹ = J * (invJ₁ φ * x * (invJ₁ φ)⁻¹) * J⁻¹ := by group
    _ = J * x⁻¹ * J⁻¹ := by rw [inverts_invJ₁_rootX₁ φ x hx]
    _ = x⁻¹ := by rw [hc, mul_inv_cancel_right]

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem inverts_invJ₂_rootX₂ : Inverts (invJ₂ φ) (rootX₂ φ) := by
  intro x hx
  have hc : J * x⁻¹ = x⁻¹ * J := commute_J_of_mem_rootX₂ ((rootX₂ φ).inv_mem hx)
  rw [invJ₂_eq φ hZ hZodd h2 hJ]
  calc J * invJ₁ φ * x * (J * invJ₁ φ)⁻¹ = J * (invJ₁ φ * x * (invJ₁ φ)⁻¹) * J⁻¹ := by group
    _ = J * x⁻¹ * J⁻¹ := by rw [inverts_invJ₁_rootX₂ φ x hx]
    _ = x⁻¹ := by rw [hc, mul_inv_cancel_right]

section Y

variable {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

omit [Finite F] in
include hY₂ in
theorem conj_Y_sq_invJ₁ (hY₃ : Y⁻¹ * invJ₂ φ * Y = J) : (Y ^ 2)⁻¹ * invJ₁ φ * Y ^ 2 = J := by
  rw [show (Y ^ 2)⁻¹ * invJ₁ φ * Y ^ 2 = Y⁻¹ * (Y⁻¹ * invJ₁ φ * Y) * Y by
    simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc], hY₂, hY₃]

omit [Finite F] in
include hZ hZodd h2 hJ hY₁ hY₂ in
theorem inverts_J_rootSub_12 : Inverts J (rootSub φ Y 1 2) := by
  have h := (inverts_invJ₂_rootX₁ φ hZ hZodd h2 hJ).map Y⁻¹
  rwa [inv_inv, conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂] at h

omit [Finite F] in
include hZ hZodd h2 hJ hY₁ hY₂ in
theorem inverts_J_rootSub_21 : Inverts J (rootSub φ Y 2 1) := by
  have h := (inverts_invJ₂_rootX₂ φ hZ hZodd h2 hJ).map Y⁻¹
  rwa [inv_inv, conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂] at h

omit [Finite F] in
include hZ hZodd h2 hJ hY₁ hY₂ in
theorem inverts_J_rootSub_20 : Inverts J (rootSub φ Y 2 0) := by
  have h := (inverts_invJ₁_rootX₁ φ).map (Y ^ 2)⁻¹
  rwa [inv_inv, conj_Y_sq_invJ₁ φ hY₂ (conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂)] at h

omit [Finite F] in
include hZ hZodd h2 hJ hY₁ hY₂ in
theorem inverts_J_rootSub_02 : Inverts J (rootSub φ Y 0 2) := by
  have h := (inverts_invJ₁_rootX₂ φ).map (Y ^ 2)⁻¹
  rwa [inv_inv, conj_Y_sq_invJ₁ φ hY₂ (conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂)] at h

end Y

include φ hZ hZodd h2 in
theorem pow_ringChar_eq_one_of_pow_pow {g : G} (hg : J * g = g * J)
    (hgp : (g ^ ringChar F) ^ ringChar F = 1) : g ^ ringChar F = 1 := by
  set p := ringChar F
  set u := g ^ p with hu_def
  have hu : J * u = u * J := (Commute.pow_right hg p).eq
  by_contra hu1
  obtain ⟨h, hh, hhu⟩ := exists_conj_mem_rootX₁ φ hZ h2 hu hgp
  obtain ⟨c, hc⟩ := (mem_rootX₁ φ).mp hhu
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hu1
    rw [rootUp, upperGL_zero, map_one] at hc
    calc u = h⁻¹ * (h * u * h⁻¹) * h := by group
      _ = 1 := by rw [← hc]; group
  set g' := h * g * h⁻¹ with hg'_def
  have hg' : J * g' = g' * J := by
    have hhJ : Commute J h := hh
    have hgJ : Commute J g := hg
    exact ((hhJ.mul_right hgJ).mul_right hhJ.inv_right).eq
  have hg'p : g' ^ p = rootUp φ c := by
    rw [hg'_def, conj_pow, ← hu_def, hc]
  have hcomm : g' * rootUp φ c = rootUp φ c * g' := by
    rw [← hg'p]
    exact ((Commute.refl g').pow_right p).eq
  obtain ⟨a, b, hab⟩ := centralizer_rootUp φ hZ hZodd h2 hc0 hg' hcomm
  have hsc : Commute (linearCentralizerHom φ (Matrix.GeneralLinearGroup.scalar (Fin 2) a))
      (rootUp φ b) := by
    rw [rootUp, Commute, SemiconjBy, ← map_mul, ← map_mul,
      (commute_of_mem_scalars ⟨a, rfl⟩ (upperGL b)).eq]
  have hpow :
      g' ^ p = linearCentralizerHom φ (Matrix.GeneralLinearGroup.scalar (Fin 2) (a ^ p)) := by
    rw [hab, hsc.mul_pow, rootUp_pow_ringChar, mul_one, ← map_pow,
      ← map_pow (Matrix.GeneralLinearGroup.scalar (Fin 2))]
  rw [hg'p] at hpow
  have hmem := (linearCentralizerHom_eq_iff φ _ _).mp hpow
  have hsc' : upperGL c ∈ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F := by
    have h1 := hZ hmem
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin 2) (a ^ p) ∈
        CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F := ⟨_, rfl⟩
    have := (CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F).mul_mem h1 h3
    simpa using this
  exact hc0 ((upperGL_mem_scalars_iff c).mp hsc')

include φ hZ hZodd h2 in
theorem pow_ringChar_eq_one_of_commute {g : G} (hg : J * g = g * J) {k : ℕ}
    (hgk : g ^ (ringChar F ^ k) = 1) : g ^ ringChar F = 1 := by
  induction k generalizing g with
  | zero =>
    rw [pow_zero, pow_one] at hgk
    rw [hgk, one_pow]
  | succ k ih =>
    have hgp : J * g ^ ringChar F = g ^ ringChar F * J := (Commute.pow_right hg _).eq
    have h1 : (g ^ ringChar F) ^ (ringChar F ^ k) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hgk
    exact pow_ringChar_eq_one_of_pow_pow φ hZ hZodd h2 hg (ih hgp h1)

include φ hZ hZodd h2 hJ in
theorem normalizer_sylow_le_centralizer [Finite G] (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ Subgroup.centralizer {J}) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer {J} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({J} : Set G)
  obtain ⟨hJS, huniq⟩ := sylow_center_involution φ hZ hZodd h2 hJ (S.subtype hS)
  have hmemS : ∀ y : C, y ∈ S.subtype hS ↔ (y : G) ∈ (S : Subgroup G) := by
    intro y
    change y ∈ ((S.subtype hS : Sylow 2 C) : Subgroup C) ↔ _
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  have hJS' : J ∈ (S : Subgroup G) := (hmemS _).mp hJS
  have hJJ : J * J = 1 := J_mul_self hJ
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxS : n * J * n⁻¹ ∈ (S : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hn J).mp hJS'
  set x : S.subtype hS := ⟨⟨n * J * n⁻¹, hS hxS⟩, (hmemS _).mpr hxS⟩
  have hxc : x ∈ Subgroup.center (S.subtype hS) := by
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hy : ((y : C) : G) ∈ (S : Subgroup G) := (hmemS _).mp y.2
    have hny : n⁻¹ * (y : C) * n⁻¹⁻¹ ∈ (S : Subgroup G) :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) _).mp hy
    rw [inv_inv] at hny
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hS hny)
    change ((y : C) : G) * (n * J * n⁻¹) = n * J * n⁻¹ * ((y : C) : G)
    calc ((y : C) : G) * (n * J * n⁻¹) = n * ((n⁻¹ * (y : C) * n) * J) * n⁻¹ := by group
      _ = n * (J * (n⁻¹ * (y : C) * n)) * n⁻¹ := by rw [hcomm]
      _ = n * J * n⁻¹ * ((y : C) : G) := by group
  have hxx : x * x = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change n * J * n⁻¹ * (n * J * n⁻¹) = 1
    calc n * J * n⁻¹ * (n * J * n⁻¹) = n * (J * J) * n⁻¹ := by group
      _ = 1 := by rw [hJJ]; group
  rcases huniq x hxc hxx with h | h
  · exfalso
    have h1 : n * J * n⁻¹ = 1 := by
      have := congrArg (fun z : S.subtype hS => ((z : C) : G)) h
      exact this
    have hJ1 : J = 1 := by
      calc J = n⁻¹ * (n * J * n⁻¹) * n := by group
        _ = 1 := by rw [h1]; group
    rw [hJ1, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  · have h' : n * J * n⁻¹ = J := h
    calc n * J = n * J * n⁻¹ * n := by group
      _ = J * n := by rw [h']

omit [Finite F] in
include hZ h2 in
theorem J_ne_invJ₁ : J ≠ invJ₁ φ := by
  intro h
  have hx : rootUp φ 1 ∈ rootX₁ φ := (mem_rootX₁ φ).mpr ⟨1, rfl⟩
  have h1 : J * rootUp φ 1 * J⁻¹ = rootUp φ 1 := by
    rw [commute_J_of_mem_rootX₁ hx, mul_inv_cancel_right]
  have h1' : invJ₁ φ * rootUp φ 1 * (invJ₁ φ)⁻¹ = rootUp φ 1 := by
    rw [← h]
    exact h1
  rw [inverts_invJ₁_rootX₁ φ _ hx, ← rootUp_neg] at h1'
  have h3 := rootUp_injective φ hZ h1'
  apply h2
  linear_combination -h3

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem exists_Y [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∃ Y : G, Y⁻¹ * J * Y = invJ₁ φ ∧ Y⁻¹ * invJ₁ φ * Y = invJ₂ φ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hJJ : J * J = 1 := J_mul_self hJ
  have hJ1 : J ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hnotiso : ∃ g : G, (g * J * g⁻¹) * J = J * (g * J * g⁻¹) ∧ g * J * g⁻¹ ≠ J := by
    by_contra hcon
    push Not at hcon
    obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G J hJ1 hJJ hcon
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · have hcen : J ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have h := hN g
        rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at h
        calc g * J = g * J * g⁻¹ * g := by group
          _ = J * g := by rw [h]
      have hc : Subgroup.center G = ⊤ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
        · rw [h, Subgroup.mem_bot] at hcen
          exact absurd hcen hJ1
        · exact h
      obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ Subgroup.center G := by rw [hc]; exact Subgroup.mem_top a
      exact hab ((Subgroup.mem_center_iff.mp ha b).symm)
    · rw [htop, Subgroup.card_top] at hNodd
      have h2dvd : 2 ∣ Nat.card G := by
        rw [← hJ]
        exact orderOf_dvd_natCard J
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2dvd)
  obtain ⟨g, hgc, hgJ⟩ := hnotiso
  set x := g * J * g⁻¹ with hx_def
  have hxJ : J * x = x * J := hgc.symm
  have hx2 : x * x = 1 := by
    rw [hx_def]
    calc g * J * g⁻¹ * (g * J * g⁻¹) = g * (J * J) * g⁻¹ := by group
      _ = 1 := by rw [hJJ]; group
  have hx1 : x ≠ 1 := by
    intro h
    apply hJ1
    calc J = g⁻¹ * (g * J * g⁻¹) * g := by group
      _ = 1 := by rw [← hx_def, h]; group
  obtain ⟨h, -, hhx⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ hxJ hx2 hx1 hgJ
  set w := h⁻¹ * g with hw_def
  have hwJ : w * J * w⁻¹ = invJ₁ φ := by
    calc w * J * w⁻¹ = h⁻¹ * x * h := by rw [hw_def, hx_def]; group
      _ = invJ₁ φ := by rw [← hhx]; group
  have hJw : J = w⁻¹ * invJ₁ φ * w := by rw [← hwJ]; group
  have htJ : J * (w⁻¹ * J * w) = (w⁻¹ * J * w) * J := by
    have e1 : J * (w⁻¹ * J * w) = w⁻¹ * (invJ₁ φ * J) * w := by
      calc J * (w⁻¹ * J * w) = (w⁻¹ * invJ₁ φ * w) * (w⁻¹ * J * w) := by rw [← hJw]
        _ = w⁻¹ * (invJ₁ φ * J) * w := by group
    have e2 : (w⁻¹ * J * w) * J = w⁻¹ * (J * invJ₁ φ) * w := by
      calc (w⁻¹ * J * w) * J = (w⁻¹ * J * w) * (w⁻¹ * invJ₁ φ * w) := by rw [← hJw]
        _ = w⁻¹ * (J * invJ₁ φ) * w := by group
    rw [e1, e2, J_commute_invJ₁]
  have ht2 : (w⁻¹ * J * w) * (w⁻¹ * J * w) = 1 := by
    calc w⁻¹ * J * w * (w⁻¹ * J * w) = w⁻¹ * (J * J) * w := by group
      _ = 1 := by rw [hJJ]; group
  have ht1 : w⁻¹ * J * w ≠ 1 := by
    intro h'
    apply hJ1
    calc J = w * (w⁻¹ * J * w) * w⁻¹ := by group
      _ = 1 := by rw [h']; group
  have htne : w⁻¹ * J * w ≠ J := by
    intro h'
    apply J_ne_invJ₁ φ hZ h2
    rw [← hwJ]
    calc J = w * (w⁻¹ * J * w) * w⁻¹ := by group
      _ = w * J * w⁻¹ := by rw [h']
  obtain ⟨k, hk, hkt⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ htJ ht2 ht1 htne
  set y := w * k with hy_def
  have hyJ : y * J * y⁻¹ = invJ₁ φ := by
    calc y * J * y⁻¹ = w * (k * J * k⁻¹) * w⁻¹ := by rw [hy_def]; group
      _ = w * J * w⁻¹ := by rw [← hk, mul_inv_cancel_right]
      _ = invJ₁ φ := hwJ
  have hyJ₁ : y * invJ₁ φ * y⁻¹ = J := by
    calc y * invJ₁ φ * y⁻¹ = w * (k * invJ₁ φ * k⁻¹) * w⁻¹ := by rw [hy_def]; group
      _ = w * (w⁻¹ * J * w) * w⁻¹ := by rw [hkt]
      _ = J := by group
  refine ⟨(y * swapW φ)⁻¹, ?_, ?_⟩
  · rw [inv_inv]
    calc y * swapW φ * J * (y * swapW φ)⁻¹ = y * (swapW φ * J * (swapW φ)⁻¹) * y⁻¹ := by group
      _ = invJ₁ φ := by rw [swapW_conj_J, hyJ]
  · rw [inv_inv]
    have hJ₂ := invJ₂_eq φ hZ hZodd h2 hJ
    calc y * swapW φ * invJ₁ φ * (y * swapW φ)⁻¹ =
          y * (swapW φ * invJ₁ φ * (swapW φ)⁻¹) * y⁻¹ := by group
      _ = y * (J * invJ₁ φ) * y⁻¹ := by rw [swapW_conj_invJ₁, hJ₂]
      _ = (y * J * y⁻¹) * (y * invJ₁ φ * y⁻¹) := by group
      _ = invJ₂ φ := by rw [hyJ, hyJ₁, ← J_commute_invJ₁, hJ₂]

end Setting

end CFSG.BrauerLinearThree

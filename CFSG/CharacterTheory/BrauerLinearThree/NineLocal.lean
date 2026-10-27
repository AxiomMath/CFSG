module

public import CFSG.CharacterTheory.BrauerLinearThree.LayerOrder
public import CFSG.CharacterTheory.BrauerLinearThree.RootAnalysisCore
public import CFSG.CharacterTheory.Semidihedral.Principal.TwoLinearLocalBlocks
public import CFSG.Dihedral.PerfectDihedralFourgroupAction

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
@[expose] noncomputable def fourV : Subgroup G := Subgroup.closure {J, invJ₁ φ}

omit [Finite F] in
theorem J_mem_fourV : J ∈ fourV φ := Subgroup.subset_closure (Set.mem_insert _ _)

omit [Finite F] in
theorem invJ₁_mem_fourV : invJ₁ φ ∈ fourV φ :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem invJ₂_mem_fourV : invJ₂ φ ∈ fourV φ := by
  rw [invJ₂_eq φ hZ hZodd h2 hJ]
  exact Subgroup.mul_mem _ (J_mem_fourV φ) (invJ₁_mem_fourV φ)

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem mem_fourV {x : G} : x ∈ fourV φ ↔ x = 1 ∨ x = J ∨ x = invJ₁ φ ∨ x = invJ₂ φ := by
  constructor
  · intro hx
    have h := CFSG.Semidihedral.Principal.TwoLinearLocal.mem_closure_pair (J_commute_invJ₁ φ)
      (J_mul_self hJ) (invJ₁_mul_self φ) hx
    rwa [← invJ₂_eq φ hZ hZodd h2 hJ] at h
  · rintro (rfl | rfl | rfl | rfl)
    · exact (fourV φ).one_mem
    · exact J_mem_fourV φ
    · exact invJ₁_mem_fourV φ
    · exact invJ₂_mem_fourV φ hZ hZodd h2 hJ

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem mul_self_of_mem_fourV {x : G} (hx : x ∈ fourV φ) : x * x = 1 := by
  rcases (mem_fourV φ hZ hZodd h2 hJ).mp hx with rfl | rfl | rfl | rfl
  · exact one_mul 1
  · exact J_mul_self hJ
  · exact invJ₁_mul_self φ
  · exact invJ₂_mul_self φ hZ hZodd h2 hJ

omit [Finite F] in
include hZ h2 hJ in
theorem isKleinFour_fourV : IsKleinFour (fourV φ) := by
  refine CFSG.Wreathed.isKleinFour_closure_pair hJ (orderOf_invJ₁ φ hZ h2) (J_commute_invJ₁ φ) ?_
  rw [Subgroup.disjoint_def]
  intro x hxJ hx₁
  have hz : ∀ {g : G}, orderOf g = 2 → ∀ y ∈ Subgroup.zpowers g, y = 1 ∨ y = g := by
    intro g hg y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← zpow_mod_orderOf, hg]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      simp only [Nat.cast_ofNat, h, zpow_zero]
    · right
      simp only [Nat.cast_ofNat, h, zpow_one]
  rcases hz hJ x hxJ with h | h
  · exact h
  · rw [h] at hx₁
    rcases hz (orderOf_invJ₁ φ hZ h2) _ hx₁ with h' | h'
    · rw [h]; exact h'
    · exact absurd h' (J_ne_invJ₁ φ hZ h2)

omit [Finite F] in
theorem mem_centralizer_fourV {x : G} :
    x ∈ Subgroup.centralizer (fourV φ : Set G) ↔ IsTorus φ x := by
  rw [fourV, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨h J (Set.mem_insert _ _), h _ (Set.mem_insert_of_mem _ rfl)⟩
  · rintro ⟨h1, h2⟩ y hy
    rcases hy with hy | hy
    · rw [hy]; exact h1
    · rw [Set.mem_singleton_iff.mp hy]; exact h2

omit [Finite F] in
include hZ hZodd h2 in
theorem mem_centralizer_fourV_iff {x : G} :
    x ∈ Subgroup.centralizer (fourV φ : Set G) ↔
      ∃ a b : Fˣ, x = linearCentralizerHom φ (diagGL a b) := by
  rw [mem_centralizer_fourV, isTorus_iff φ hZ hZodd h2]

omit [Finite F] in
theorem centralizer_fourV_eq :
    Subgroup.centralizer (fourV φ : Set G) =
      Subgroup.centralizer ({J} : Set G) ⊓ Subgroup.centralizer ({invJ₁ φ} : Set G) := by
  ext x
  rw [mem_centralizer_fourV, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩

omit [Finite F] in
@[expose] noncomputable def oddTorus : Subgroup G :=
  ((linearCentralizerHom φ).comp ((diagHom : Fˣ × Fˣ →* GL (Fin 2) F).comp
    (powMonoidHom 2))).range

omit [Finite F] in
theorem mem_oddTorus {x : G} :
    x ∈ oddTorus φ ↔ ∃ a b : Fˣ, x = linearCentralizerHom φ (diagGL (a ^ 2) (b ^ 2)) := by
  rw [oddTorus, MonoidHom.mem_range]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨a, b, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩

omit [Finite F] in
theorem oddTorus_le_centralizer_fourV :
    oddTorus φ ≤ Subgroup.centralizer (fourV φ : Set G) := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := (mem_oddTorus φ).mp hx
  exact (mem_centralizer_fourV φ).mpr (isTorus_diag φ _ _)

include h2 in
theorem pow_half_eq_one_of_mem_oddTorus {x : G} (hx : x ∈ oddTorus φ) :
    x ^ ((Nat.card F - 1) / 2) = 1 := by
  obtain ⟨a, b, rfl⟩ := (mem_oddTorus φ).mp hx
  have hodd := odd_card_F h2
  have hq : 2 * ((Nat.card F - 1) / 2) = Nat.card F - 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hu : ∀ c : Fˣ, (c ^ 2) ^ ((Nat.card F - 1) / 2) = 1 := by
    intro c
    rw [← pow_mul, hq, ← Nat.card_units]
    exact pow_card_eq_one'
  rw [← map_pow, diagGL_pow, hu, hu, diagGL_one_one, map_one]

omit [Field F] [Finite F] in
theorem odd_half (hq : Nat.card F % 4 = 3) : Odd ((Nat.card F - 1) / 2) := by
  rw [Nat.odd_iff]
  omega

omit [Field F] [Finite F] in
theorem eq_one_of_sq_of_pow_half (hq : Nat.card F % 4 = 3) {x : G} (hx2 : x * x = 1)
    (hxm : x ^ ((Nat.card F - 1) / 2) = 1) : x = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨(show x ^ 2 = 1 by rw [sq, hx2]), hxm⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr (odd_half hq)), pow_one] at h

include h2 in
theorem odd_card_oddTorus [Finite G] (hq : Nat.card F % 4 = 3) : Odd (Nat.card (oddTorus φ)) := by
  by_contra hcon
  rw [Nat.not_odd_iff_even] at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hcon)
  have hx2 : (x : G) * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, sq] at this
    exact congrArg Subtype.val this
  have h1 := eq_one_of_sq_of_pow_half hq hx2 (pow_half_eq_one_of_mem_oddTorus φ h2 x.2)
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

include hZ hZodd h2 hJ in
theorem fourV_inf_oddTorus (hq : Nat.card F % 4 = 3) : fourV φ ⊓ oddTorus φ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxE⟩ := Subgroup.mem_inf.mp hx
  exact eq_one_of_sq_of_pow_half hq (mul_self_of_mem_fourV φ hZ hZodd h2 hJ hxV)
    (pow_half_eq_one_of_mem_oddTorus φ h2 hxE)

include h2 in
theorem exists_sign_mul_sq (hq : Nat.card F % 4 = 3) (a : Fˣ) :
    ∃ ε c : Fˣ, (ε = 1 ∨ ε = -1) ∧ a = ε * c ^ 2 := by
  set m := (Nat.card F - 1) / 2 with hm
  have hodd := odd_card_F h2
  have hq2 : 2 * m = Nat.card F - 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have ha : a ^ (2 * m) = 1 := by
    rw [hq2, ← Nat.card_units]
    exact pow_card_eq_one'
  have hε : a ^ m = 1 ∨ a ^ m = -1 := by
    have h : (a ^ m) * (a ^ m) = 1 := by rw [← pow_add, ← two_mul, ha]
    have h' : ((a ^ m : Fˣ) : F) * ((a ^ m : Fˣ) : F) = 1 := by
      rw [← Units.val_mul, h, Units.val_one]
    rcases mul_self_eq_one_iff.mp h' with h1 | h1
    · left
      exact Units.ext h1
    · right
      exact Units.ext (by rw [h1, Units.val_neg, Units.val_one])
  obtain ⟨k, hk⟩ := odd_half hq
  refine ⟨a ^ m, a ^ (k + 1), hε, ?_⟩
  have hsq : (a ^ m) * (a ^ m) = 1 := by rw [← pow_add, ← two_mul, ha]
  calc a = (a ^ m * a ^ m) * a := by rw [hsq, one_mul]
    _ = a ^ m * a ^ (m + 1) := by rw [pow_succ]; group
    _ = a ^ m * (a ^ (k + 1)) ^ 2 := by rw [← pow_mul]; congr 2; omega

include hZ hZodd h2 hJ in
theorem exists_mul_of_mem_centralizer_fourV (hq : Nat.card F % 4 = 3) {x : G}
    (hx : x ∈ Subgroup.centralizer (fourV φ : Set G)) :
    ∃ v ∈ fourV φ, ∃ e ∈ oddTorus φ, x = v * e := by
  obtain ⟨a, b, rfl⟩ := (mem_centralizer_fourV_iff φ hZ hZodd h2).mp hx
  obtain ⟨ε₁, c₁, hε₁, rfl⟩ := exists_sign_mul_sq h2 hq a
  obtain ⟨ε₂, c₂, hε₂, rfl⟩ := exists_sign_mul_sq h2 hq b
  refine ⟨linearCentralizerHom φ (diagGL ε₁ ε₂), ?_, linearCentralizerHom φ
    (diagGL (c₁ ^ 2) (c₂ ^ 2)), (mem_oddTorus φ).mpr ⟨c₁, c₂, rfl⟩, by
      rw [← map_mul, diagGL_mul]⟩
  rw [mem_fourV φ hZ hZodd h2 hJ]
  rcases hε₁ with rfl | rfl <;> rcases hε₂ with rfl | rfl
  · left
    rw [diagGL_one_one, map_one]
  · right; right; left
    rfl
  · right; right; right
    rfl
  · right; left
    rw [← neg_one_eq_diagGL]
    exact linearCentralizerHom_neg_one φ hZ hZodd h2 hJ

omit [Finite F] in
theorem centralizer_zpowers_eq (g : G) :
    Subgroup.centralizer (Subgroup.zpowers g : Set G) = Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

omit [Finite F] in
theorem mem_centralizer_zpowers_iff {g x : G} :
    x ∈ Subgroup.centralizer (Subgroup.zpowers g : Set G) ↔ g * x = x * g := by
  rw [centralizer_zpowers_eq, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem exists_conj_fourV [Finite G] (U : Subgroup G) (hU : IsKleinFour U) (hJU : J ∈ U)
    (hUC : U ≤ Subgroup.centralizer (Subgroup.zpowers J : Set G)) :
    ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers J : Set G),
      U.map (MulAut.conj c).toMonoidHom = fourV φ := by
  have : IsKleinFour U := hU
  obtain ⟨a, haU, haJ⟩ : ∃ a ∈ U, a ∉ Subgroup.zpowers J := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show U ≤ Subgroup.zpowers J from hcon)
    rw [IsKleinFour.card_four (G := U), Nat.card_zpowers, hJ] at hle
    omega
  have ha1 : a ≠ 1 := fun h => haJ (h ▸ Subgroup.one_mem _)
  have haJ' : a ≠ J := fun h => haJ (h ▸ Subgroup.mem_zpowers J)
  have ha2 : a * a = 1 := by
    have := IsKleinFour.mul_self (⟨a, haU⟩ : U)
    exact congrArg Subtype.val this
  have haC : J * a = a * J := (mem_centralizer_zpowers_iff.mp (hUC haU))
  obtain ⟨h, hhJ, hha⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ haC ha2 ha1 haJ'
  refine ⟨h⁻¹, mem_centralizer_zpowers_iff.mpr ?_, ?_⟩
  · calc J * h⁻¹ = h⁻¹ * (h * J) * h⁻¹ := by group
      _ = h⁻¹ * (J * h) * h⁻¹ := by rw [hhJ]
      _ = h⁻¹ * J := by group
  · have hle : fourV φ ≤ U.map (MulAut.conj h⁻¹).toMonoidHom := by
      rw [fourV, Subgroup.closure_le]
      intro y hy
      rcases hy with hy | hy
      · rw [hy]
        refine ⟨J, hJU, ?_⟩
        change h⁻¹ * J * h⁻¹⁻¹ = J
        rw [inv_inv, mul_assoc, hhJ, ← mul_assoc, inv_mul_cancel, one_mul]
      · rw [Set.mem_singleton_iff.mp hy]
        refine ⟨a, haU, ?_⟩
        change h⁻¹ * a * h⁻¹⁻¹ = invJ₁ φ
        rw [inv_inv, ← hha]
        group
    have hcard : Nat.card (U.map (MulAut.conj h⁻¹).toMonoidHom) = Nat.card (fourV φ) := by
      have : IsKleinFour (fourV φ) := isKleinFour_fourV φ hZ h2 hJ
      rw [Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective,
        IsKleinFour.card_four (G := U), IsKleinFour.card_four (G := fourV φ)]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem isConj_J_or_invJ₁ (y : Subgroup.centralizer (Subgroup.zpowers J : Set G))
    (hy : orderOf y = 2) :
    IsConj y ⟨J, CFSG.TwoRankLowerBound.Helpers.element_mem_centralizer_zpowers J⟩ ∨
      IsConj y ⟨invJ₁ φ, mem_centralizer_zpowers_iff.mpr (J_commute_invJ₁ φ)⟩ := by
  have hy2 : (y : G) * y = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy, sq] at this
    exact congrArg Subtype.val this
  have hy1 : (y : G) ≠ 1 := by
    intro h
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    exact absurd hy (by norm_num)
  by_cases hyJ : (y : G) = J
  · left
    have : y = ⟨J, CFSG.TwoRankLowerBound.Helpers.element_mem_centralizer_zpowers J⟩ :=
      Subtype.ext hyJ
    rw [this]
  · right
    obtain ⟨h, hhJ, hhy⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ
      (mem_centralizer_zpowers_iff.mp y.2) hy2 hy1 hyJ
    refine IsConj.symm (isConj_iff.mpr ⟨⟨h, mem_centralizer_zpowers_iff.mpr hhJ⟩, ?_⟩)
    exact Subtype.ext hhy

include φ hZ hZodd h2 hJ in
theorem isConj_J_of_involution [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {x : G} (hx : orderOf x = 2) : IsConj J x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Subgroup.centralizer ({J} : Set G)) := Finite.of_equiv _ φ.symm.toEquiv
  obtain ⟨Y, hY₁, -⟩ := exists_Y φ hZ hZodd h2 hJ hnonab
  obtain ⟨SC⟩ : Nonempty (Sylow 2 (Subgroup.centralizer ({J} : Set G))) := inferInstance
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_sylow_centralizer φ hZ hZodd h2 hJ _ SC rfl
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {J} := by
    rw [hS]
    exact Subgroup.map_subtype_le _
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨S', hS'⟩ := hxp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S'
  have hxS' : x ∈ (S' : Subgroup G) := hS' (Subgroup.mem_zpowers x)
  rw [← hg, mem_smul_sylow_iff] at hxS'
  obtain ⟨y, hyS, hyx⟩ := hxS'
  have hy_def : y = g⁻¹ * x * g := by rw [← hyx]; group
  have hyJ : J * y = y * J := (Subgroup.mem_centralizer_singleton_iff.mp (hSC hyS)).symm
  have hy2 : y * y = 1 := by
    have h : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    calc y * y = g⁻¹ * (x * x) * g := by rw [hy_def]; group
      _ = 1 := by rw [h]; group
  have hy1 : y ≠ 1 := by
    intro h
    have : x = 1 := by
      calc x = g * y * g⁻¹ := by rw [hy_def]; group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hJy : IsConj J y := by
    by_cases hyJ' : y = J
    · rw [hyJ']
    · obtain ⟨h, -, hhy⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ hyJ hy2 hy1 hyJ'
      refine isConj_iff.mpr ⟨h * Y⁻¹, ?_⟩
      rw [← hhy, ← hY₁]
      group
  exact hJy.trans (isConj_iff.mpr ⟨g, hyx⟩)

include φ hZ hZodd h2 hJ in
theorem isConj_of_involutions [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  (isConj_J_of_involution φ hZ hZodd h2 hJ hnonab hx).symm.trans
    (isConj_J_of_involution φ hZ hZodd h2 hJ hnonab hy)

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem mem_dV_or_swapW_mul_mem_dV {x : G} (hxJ : J * x = x * J)
    (hxM : x ∈ Subgroup.normalizer (fourV φ : Set G)) :
    x ∈ Subgroup.centralizer (fourV φ : Set G) ∨
      swapW φ * x ∈ Subgroup.centralizer (fourV φ : Set G) := by
  have hmem : x * invJ₁ φ * x⁻¹ ∈ fourV φ :=
    (Subgroup.mem_normalizer_iff.mp hxM _).mp (invJ₁_mem_fourV φ)
  have hJ₁' : orderOf (invJ₁ φ) = 2 := orderOf_invJ₁ φ hZ h2
  rcases (mem_fourV φ hZ hZodd h2 hJ).mp hmem with h | h | h | h
  · exfalso
    have : invJ₁ φ = 1 := by
      calc invJ₁ φ = x⁻¹ * (x * invJ₁ φ * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at hJ₁'
    exact absurd hJ₁' (by norm_num)
  · exfalso
    apply J_ne_invJ₁ φ hZ h2
    calc J = x⁻¹ * (x * J) := by group
      _ = x⁻¹ * (J * x) := by rw [hxJ]
      _ = x⁻¹ * (x * invJ₁ φ * x⁻¹) * x := by rw [h]; group
      _ = invJ₁ φ := by group
  · left
    rw [mem_centralizer_fourV]
    refine ⟨hxJ, ?_⟩
    calc invJ₁ φ * x = (x * invJ₁ φ * x⁻¹) * x := by rw [h]
      _ = x * invJ₁ φ := by group
  · right
    rw [mem_centralizer_fourV]
    have hW := swapW_conj_invJ₁ φ
    rw [swapW_inv] at hW
    refine ⟨?_, ?_⟩
    · have hWJ : J * swapW φ = swapW φ * J := linearCentralizerHom_commute φ _
      rw [← mul_assoc, hWJ, mul_assoc, hxJ, mul_assoc]
    ·
      have hW2 : swapW φ * invJ₂ φ * swapW φ = invJ₁ φ := by
        rw [← hW]
        calc swapW φ * (swapW φ * invJ₁ φ * swapW φ) * swapW φ =
            (swapW φ * swapW φ) * invJ₁ φ * (swapW φ * swapW φ) := by group
          _ = invJ₁ φ := by rw [swapW_mul_self]; group
      calc invJ₁ φ * (swapW φ * x) = swapW φ * invJ₂ φ * swapW φ * (swapW φ * x) := by
            rw [hW2]
        _ = swapW φ * (x * invJ₁ φ * x⁻¹) * (swapW φ * swapW φ) * x := by rw [h]; group
        _ = swapW φ * x * invJ₁ φ := by rw [swapW_mul_self]; group

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem swapW_mem_normalizer_fourV : swapW φ ∈ Subgroup.normalizer (fourV φ : Set G) := by
  have hW := swapW_conj_invJ₁ φ
  have hWJ := swapW_conj_J φ
  have hJ₂ : swapW φ * invJ₂ φ * (swapW φ)⁻¹ = invJ₁ φ := by
    rw [← hW, swapW_inv]
    calc swapW φ * (swapW φ * invJ₁ φ * swapW φ) * swapW φ =
        (swapW φ * swapW φ) * invJ₁ φ * (swapW φ * swapW φ) := by group
      _ = invJ₁ φ := by rw [swapW_mul_self]; group
  have hconj : ∀ x ∈ fourV φ, swapW φ * x * (swapW φ)⁻¹ ∈ fourV φ := by
    intro x hx
    rw [mem_fourV φ hZ hZodd h2 hJ] at hx ⊢
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · left; group
    · right; left; exact hWJ
    · right; right; right; exact hW
    · right; right; left; exact hJ₂
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj x, fun hx => ?_⟩
  have h := hconj _ hx
  rwa [swapW_inv, show swapW φ * (swapW φ * x * swapW φ) * swapW φ =
    (swapW φ * swapW φ) * x * (swapW φ * swapW φ) by group, swapW_mul_self, one_mul,
    mul_one] at h

omit [Finite F] in
include hZ hZodd h2 hJ in
theorem inv_mem_normalizer_fourV {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ)
    (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ) : Y⁻¹ ∈ Subgroup.normalizer (fourV φ : Set G) := by
  have hY₃ := conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂
  have hconj : ∀ x ∈ fourV φ, Y⁻¹ * x * Y ∈ fourV φ := by
    intro x hx
    rw [mem_fourV φ hZ hZodd h2 hJ] at hx ⊢
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · left; group
    · right; right; left; exact hY₁
    · right; right; right; exact hY₂
    · right; left; exact hY₃
  have hconj' : ∀ x ∈ fourV φ, Y * x * Y⁻¹ ∈ fourV φ := by
    intro x hx
    rw [mem_fourV φ hZ hZodd h2 hJ] at hx ⊢
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · left; group
    · right; right; right; exact conj_eq_of_inv_conj_eq hY₃
    · right; left; exact conj_eq_of_inv_conj_eq hY₁
    · right; right; left; exact conj_eq_of_inv_conj_eq hY₂
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => by rw [inv_inv]; exact hconj x hx, fun hx => ?_⟩
  have h := hconj' _ hx
  rwa [inv_inv, show Y * (Y⁻¹ * x * Y) * Y⁻¹ = x by group] at h

omit [Finite F] in
include φ hZ hZodd h2 hJ in
theorem normalizerMonoidHom_fourV_surjective [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    Function.Surjective (fourV φ).normalizerMonoidHom := by
  obtain ⟨Y, hY₁, hY₂⟩ := exists_Y φ hZ hZodd h2 hJ hnonab
  have : IsKleinFour (fourV φ) := isKleinFour_fourV φ hZ h2 hJ
  have hJ₂ := invJ₂_eq φ hZ hZodd h2 hJ
  have hJ1 : J ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  have hJ₁1 : invJ₁ φ ≠ 1 := by
    intro h
    have := orderOf_invJ₁ φ hZ h2
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  set a := (fourV φ).normalizerMonoidHom ⟨Y⁻¹, inv_mem_normalizer_fourV φ hZ hZodd h2 hJ hY₁ hY₂⟩
  set b := (fourV φ).normalizerMonoidHom ⟨swapW φ, swapW_mem_normalizer_fourV φ hZ hZodd h2 hJ⟩
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    have hJ' := congrArg (fun ψ : MulAut (fourV φ) => ((ψ ⟨J, J_mem_fourV φ⟩ : fourV φ) : G)) h
    simp only [MulAut.one_apply] at hJ'
    rw [sq, MulAut.mul_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.normalizerMonoidHom_apply_apply_coe] at hJ'
    have e1 : Y⁻¹ * J * Y⁻¹⁻¹ = invJ₁ φ := by rw [inv_inv]; exact hY₁
    simp only [e1] at hJ'
    rw [inv_inv, hY₂, hJ₂] at hJ'
    apply hJ₁1
    calc invJ₁ φ = J⁻¹ * (J * invJ₁ φ) := by group
      _ = 1 := by rw [hJ']; group
  have hb2 : b ^ 2 = 1 := by
    rw [sq, ← map_mul]
    have : (⟨swapW φ, swapW_mem_normalizer_fourV φ hZ hZodd h2 hJ⟩ *
        ⟨swapW φ, swapW_mem_normalizer_fourV φ hZ hZodd h2 hJ⟩ :
          Subgroup.normalizer (fourV φ : Set G)) = 1 :=
      Subtype.ext (swapW_mul_self φ)
    rw [this, map_one]
  have hb1 : b ≠ 1 := by
    intro h
    have h' := congrArg (fun ψ : MulAut (fourV φ) =>
      ((ψ ⟨invJ₁ φ, invJ₁_mem_fourV φ⟩ : fourV φ) : G)) h
    simp only [MulAut.one_apply] at h'
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, swapW_conj_invJ₁, hJ₂] at h'
    apply hJ1
    calc J = J * invJ₁ φ * (invJ₁ φ)⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hrange := CFSG.GorensteinWalter.kleinFourAut_subgroup_eq_top (fourV φ)
    (fourV φ).normalizerMonoidHom.range a b ⟨_, rfl⟩ ha2 ⟨_, rfl⟩ hb1 hb2
  exact MonoidHom.range_eq_top.mp hrange

end CFSG.BrauerLinearThree

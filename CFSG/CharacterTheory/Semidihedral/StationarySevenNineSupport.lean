module

public import CFSG.CharacterTheory.Semidihedral.Principal.FourGroupCosetDegreeBound
public import CFSG.CharacterTheory.Wreathed.WeightedCentralInvolutionSum
public import CFSG.CharacterTheory.Semidihedral.ActualSimpleLayerLocalPackage

public section

open scoped Pointwise

namespace CFSG.Semidihedral.StationarySevenNine

open CFSG.Open CFSG.Semidihedral CFSG.Semidihedral.ActualSimpleLayerLocalPackage
open CFSG.TwoRankLowerBound.Helpers

theorem fixed_core_card_index {G : Type} [Group G] [Finite G] (t s₀ : G) :
    Nat.card (((Subgroup.centralizer {s₀}).comap (C t).subtype).subgroupOf (N t)) =
        Nat.card ((N t).map (C t).subtype ⊓ Subgroup.centralizer ({s₀} : Set G) :
          Subgroup G) ∧
      (((Subgroup.centralizer {s₀}).comap (C t).subtype).subgroupOf (N t)).index =
        ((N t).map (C t).subtype ⊓ Subgroup.centralizer ({s₀} : Set G)).relIndex
          ((N t).map (C t).subtype) := by
  set CN := ((Subgroup.centralizer {s₀}).comap (C t).subtype).subgroupOf (N t) with hCN
  set Na := (N t).map (C t).subtype with hNa
  set A₀ := Na ⊓ Subgroup.centralizer ({s₀} : Set G) with hA₀
  have hinj : Function.Injective ((C t).subtype.comp (N t).subtype) :=
    (C t).subtype_injective.comp (N t).subtype_injective
  have hmap : CN.map ((C t).subtype.comp (N t).subtype) = A₀ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : C t), y.2, rfl⟩, hy⟩
    · rintro ⟨⟨c, hc, rfl⟩, hcs⟩
      exact ⟨⟨c, hc⟩, hcs, rfl⟩
  have hcard : Nat.card CN = Nat.card A₀ := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
  refine ⟨hcard, ?_⟩
  have h1 := Subgroup.card_mul_index CN
  have h2 := Subgroup.card_mul_index (A₀.subgroupOf Na)
  have h3 : Nat.card (A₀.subgroupOf Na) = Nat.card A₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A₀ ≤ Na)).toEquiv
  have h4 : Nat.card Na = Nat.card (N t) :=
    Subgroup.card_map_of_injective (C t).subtype_injective
  rw [h3, h4, ← hcard] at h2
  have hpos : 0 < Nat.card CN := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.trans h2.symm)

theorem mem_zpowers_of_unique_involution {G : Type*} [Group G] (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) {z : G} (hz : ∀ g ∈ Q, orderOf g = 2 → g = z) {u : G} (hu : u ∈ Q)
    (hu1 : u ≠ 1) : z ∈ Subgroup.zpowers u := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨u, hu⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hu1 hk
  have hv : orderOf (u ^ (orderOf u / 2)) = 2 :=
    orderOf_pow_orderOf_div (by rw [hk]; positivity) (by rw [hk]; exact dvd_pow_self 2 hk0)
  rw [← hz _ (Q.pow_mem hu _) hv]
  exact Subgroup.npow_mem_zpowers u _

theorem semidirectProduct_inl_bijective_of_subsingleton {K H : Type*} [Group K] [Group H]
    [Subsingleton H] (φ : H →* MulAut K) :
    Function.Bijective (SemidirectProduct.inl : K →* K ⋊[φ] H) :=
  ⟨SemidirectProduct.inl_injective, fun x =>
    ⟨x.left, SemidirectProduct.ext rfl (Subsingleton.elim _ _)⟩⟩

theorem exists_nonsquare_unit_of_odd_card (K : Type*) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) : ∃ a : Kˣ, ¬ IsSquare a := by
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K ≠ 2 := by
    intro h
    have h2 := (FiniteField.even_card_iff_char_two (F := K)).mp h
    rw [← Nat.card_eq_fintype_card] at h2
    exact Nat.not_even_iff_odd.mpr hK (Nat.even_iff.mpr h2)
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ha ⟨0, by simp⟩
  refine ⟨Units.mk0 a ha0, fun ⟨v, hv⟩ => ha ⟨v, ?_⟩⟩
  have h := congrArg Units.val hv
  simpa using h

theorem sum_norm_sq_le_card_centralizer {G : Type*} [Group G] [Fintype G]
    (basis : FiniteIrreducibleCharacterBasis G) (T : Finset basis.index) (g : G) :
    ∑ l ∈ T, ‖(basis.representation l).character g‖ ^ 2 ≤
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℝ) := by
  have h := CFSG.Wreathed.complete_complex_character_column_sum basis g g
  rw [CFSG.Wreathed.conjugatorCount_self] at h
  have hterm : ∀ l : basis.index, (basis.representation l).character g *
      starRingEnd ℂ ((basis.representation l).character g) =
        ((‖(basis.representation l).character g‖ ^ 2 : ℝ) : ℂ) := by
    intro l
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [hterm] at h
  have h' : (∑ l : basis.index, ‖(basis.representation l).character g‖ ^ 2 : ℝ) =
      Nat.card (Subgroup.centralizer ({g} : Set G)) := by
    exact_mod_cast h
  rw [← h']
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun l _ _ => sq_nonneg _)

open CFSG.Semidihedral.Principal.EigenCalculus in
theorem rational_prime_order_eigenspaces {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ G W) {z : G} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hz : z ^ ℓ = 1) {q : ℚ} (hq : ρ.character z = q) :
    ∃ d : ℕ, (∀ μ : ℂ, μ ^ ℓ = 1 → μ ≠ 1 →
        Module.finrank ℂ (Module.End.eigenspace (ρ z) μ) = d) ∧
      Module.finrank ℂ W = Module.finrank ℂ (Module.End.eigenspace (ρ z) 1) + (ℓ - 1) * d ∧
      ρ.character z = (Module.finrank ℂ (Module.End.eigenspace (ρ z) 1) : ℂ) - d := by
  classical
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have : NeZero ℓ := ⟨hℓ0⟩
  set ζ := Complex.exp (2 * Real.pi * Complex.I / ℓ) with hζdef
  have hζ : IsPrimitiveRoot ζ ℓ := Complex.isPrimitiveRoot_exp ℓ hℓ0
  have hf : ρ z ^ ℓ = 1 := by rw [← map_pow, hz, map_one]
  set E : Fin ℓ → ℕ := fun j =>
    Module.finrank ℂ (Module.End.eigenspace (ρ z) (ζ ^ (j : ℕ))) with hEdef
  have hsumz : ρ.character z = ∑ j : Fin ℓ, ((E j : ℤ) : ℂ) * ζ ^ (j : ℕ) := by
    have h := trace_mul_pow_eq_sum (Commute.one_right (ρ z)) hℓ0 hf hζ 1
    rw [one_mul, pow_one] at h
    change LinearMap.trace ℂ W (ρ z) = _
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_one, show (1 : Module.End ℂ W).restrict (mapsTo_eigenspace (Commute.one_right (ρ z))
      (ζ ^ (j : ℕ))) = 1 from by ext; rfl, LinearMap.trace_one, mul_comm]
    push_cast
    rfl
  have hequal : ∀ j k : Fin ℓ, (j : ℕ) ≠ 0 → (k : ℕ) ≠ 0 → E j = E k := by
    intro j k hj hk
    have h := CFSG.Semidihedral.Principal.CosetConstantEigenspaces.coeff_eq_of_sum_pow_rat hℓ hζ
      (fun j => (E j : ℤ)) (q := q) (by rw [← hq, hsumz]) j k hj hk
    exact_mod_cast h
  have hfin : Module.finrank ℂ W = ∑ j : Fin ℓ, E j := finrank_eq_sum hℓ0 hf hζ
  set j₀ : Fin ℓ := ⟨0, hℓ.pos⟩ with hj₀
  set j₁ : Fin ℓ := ⟨1, hℓ.one_lt⟩ with hj₁
  have hj₀0 : ((j₀ : Fin ℓ) : ℕ) = 0 := rfl
  have hE₀ : E j₀ = Module.finrank ℂ (Module.End.eigenspace (ρ z) 1) := by
    change Module.finrank ℂ (Module.End.eigenspace (ρ z) (ζ ^ 0)) = _
    rw [pow_zero]
  have hrest : ∀ j ∈ Finset.univ.erase j₀, E j = E j₁ := by
    intro j hj
    have hj0 : (j : ℕ) ≠ 0 := fun h0 => (Finset.mem_erase.mp hj).1 (Fin.ext h0)
    exact hequal j j₁ hj0 one_ne_zero
  have hcardE : (Finset.univ.erase j₀).card = ℓ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j₀), Finset.card_univ, Fintype.card_fin]
  refine ⟨E j₁, ?_, ?_, ?_⟩
  · intro μ hμ hμ1
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
    have hi0 : i ≠ 0 := fun h0 => hμ1 (by rw [h0, pow_zero])
    exact hequal ⟨i, hi⟩ j₁ hi0 one_ne_zero
  · rw [hfin, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀), hE₀, Finset.sum_congr rfl hrest,
      Finset.sum_const, hcardE, smul_eq_mul]
  ·
    have hgeom : ∑ j : Fin ℓ, ζ ^ (j : ℕ) = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ζ ^ i) ℓ]
      exact hζ.geom_sum_eq_zero hℓ.one_lt
    have hgeom' : ∑ j ∈ Finset.univ.erase j₀, ζ ^ (j : ℕ) = -1 := by
      have h : ζ ^ ((j₀ : Fin ℓ) : ℕ) + ∑ j ∈ Finset.univ.erase j₀, ζ ^ (j : ℕ) =
          ∑ j : Fin ℓ, ζ ^ (j : ℕ) :=
        Finset.add_sum_erase Finset.univ (fun j : Fin ℓ => ζ ^ (j : ℕ)) (Finset.mem_univ j₀)
      rw [hgeom, hj₀0, pow_zero] at h
      linear_combination h
    rw [hsumz, ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    have hterm : ∀ j ∈ Finset.univ.erase j₀, ((E j : ℤ) : ℂ) * ζ ^ (j : ℕ) =
        ((E j₁ : ℤ) : ℂ) * ζ ^ (j : ℕ) := by
      intro j hj
      rw [hrest j hj]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hgeom', hE₀, hj₀0, pow_zero, mul_one]
    push_cast
    ring

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_two {X : Type*} [Group X] {s a : X}
    (hs : orderOf s = 2) (ha : a ∈ Subgroup.zpowers s) : a = 1 ∨ a = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  rw [← zpow_mod_orderOf, hs]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show (k % ((2 : ℕ) : ℤ)) = 0 from h, zpow_zero]
  · right
    rw [show (k % ((2 : ℕ) : ℤ)) = 1 from h, zpow_one]

theorem le_normalizer_map_of_normal {X : Type*} [Group X] (C : Subgroup X) (K : Subgroup C)
    (hK : K.Normal) : C ≤ Subgroup.normalizer ((K.map C.subtype : Subgroup X) : Set X) := by
  have h := Subgroup.le_normalizer_map (H := K) C.subtype
  rw [Subgroup.normalizer_eq_top_iff.mpr hK, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  exact h

theorem central_product_of_index_two {X : Type*} [Group X] (Cc : Subgroup X)
    (Jc Nc Yc : Subgroup Cc) (hNn : Nc.Normal) (hJn : Jc.Normal) (hY : Yc = Jc ⊔ Nc)
    (hJN : Jc ⊓ Nc = ⊥) (hJcent : Jc ≤ Subgroup.centralizer (Nc : Set Cc))
    (hYindex : Yc.index = 2) (sc : Cc) (hs2 : orderOf sc = 2) (hsY : sc ∉ Yc)
    (hsN : ∀ y ∈ Nc, sc * y = y * sc) (hNcomm : ∀ a ∈ Nc, ∀ b ∈ Nc, a * b = b * a) :
    let JS := Jc.map Cc.subtype ⊔ Subgroup.zpowers (sc : X)
    let Na := Nc.map Cc.subtype
    JS ⊔ Na = Cc ∧ JS ⊓ Na = ⊥ ∧ (∀ x ∈ JS, ∀ y ∈ Na, Commute x y) ∧
      Nc ≤ Subgroup.center Cc ∧ JS ≤ Cc ∧
      Function.Bijective ((QuotientGroup.mk' Nc).comp ((JS.subgroupOf Cc).subtype)) := by
  intro JS Na
  have hJa : Jc.map Cc.subtype ≤ Cc := Subgroup.map_subtype_le _
  have hNa : Na ≤ Cc := Subgroup.map_subtype_le _
  have hsC : (sc : X) ∈ Cc := sc.2
  have hs2' : orderOf (sc : X) = 2 := by rw [Subgroup.orderOf_coe, hs2]
  have hJSC : JS ≤ Cc := sup_le hJa (Subgroup.zpowers_le.mpr hsC)
  have hJaN : Jc.map Cc.subtype ≤ Subgroup.centralizer (Na : Set X) := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp (hJcent hj) y hy)
  have hsN' : Subgroup.zpowers (sc : X) ≤ Subgroup.centralizer (Na : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hsN y hy).symm
  have hJSN : JS ≤ Subgroup.centralizer (Na : Set X) := sup_le hJaN hsN'
  have hNN : Na ≤ Subgroup.centralizer (Na : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hNcomm b hb a ha)
  have hYle : ∀ c : Cc, c ∈ Yc → (c : X) ∈ JS ⊔ Na := by
    intro c hc
    rw [hY] at hc
    have h : (c : X) ∈ (Jc ⊔ Nc).map Cc.subtype := ⟨c, hc, rfl⟩
    rw [Subgroup.map_sup] at h
    exact (sup_le_sup_right le_sup_left Na) h
  have hCle : Cc ≤ JS ⊔ Na := by
    intro c hc
    by_cases hcY : (⟨c, hc⟩ : Cc) ∈ Yc
    · exact hYle _ hcY
    · have hsinv : sc⁻¹ ∉ Yc := fun h => hsY (by simpa using Yc.inv_mem h)
      have hmem : sc⁻¹ * ⟨c, hc⟩ ∈ Yc :=
        (Subgroup.mul_mem_iff_of_index_two hYindex).mpr (iff_of_false hsinv hcY)
      have h2 : (sc : X) ∈ JS ⊔ Na :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
      have hc' : c = (sc : X) * ((sc⁻¹ * ⟨c, hc⟩ : Cc) : X) := by simp
      rw [hc']
      exact (JS ⊔ Na).mul_mem h2 (hYle _ hmem)
  have hsup : JS ⊔ Na = Cc := le_antisymm (sup_le hJSC hNa) hCle
  have hJSset : ((JS : Subgroup X) : Set X) =
      (Subgroup.zpowers (sc : X) : Set X) * (Jc.map Cc.subtype : Set X) := by
    rw [show JS = Subgroup.zpowers (sc : X) ⊔ Jc.map Cc.subtype from sup_comm _ _]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
      ((Subgroup.zpowers_le.mpr hsC).trans (le_normalizer_map_of_normal Cc Jc hJn))
  have hinf : JS ⊓ Na = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxJS, hxN⟩
    have hx : x ∈ (Subgroup.zpowers (sc : X) : Set X) * (Jc.map Cc.subtype : Set X) := by
      rw [← hJSset]
      exact hxJS
    obtain ⟨a, ha, _, ⟨j, hj, rfl⟩, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨y, hy, hyx⟩ := hxN
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two hs2' ha with rfl | rfl
    · rw [one_mul] at hyx
      have hyj : y = j := Subtype.ext hyx
      subst hyj
      have hmem : y ∈ Jc ⊓ Nc := ⟨hj, hy⟩
      rw [hJN] at hmem
      rw [Subgroup.mem_bot.mp hmem, one_mul]
      exact Subgroup.one_mem _
    · exfalso
      have hyx' : (y : X) = (sc : X) * (j : X) := hyx
      have hsc : sc = y * j⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hyx']
        group
      apply hsY
      rw [hsc, hY]
      exact (Jc ⊔ Nc).mul_mem (Subgroup.mem_sup_right hy) (Subgroup.mem_sup_left (Jc.inv_mem hj))
  have hcomm : ∀ x ∈ JS, ∀ y ∈ Na, Commute x y := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.mp (hJSN hx)) y hy).symm
  have hcenter : Nc ≤ Subgroup.center Cc := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro c
    have hcN : (c : X) ∈ Subgroup.centralizer (Na : Set X) := (sup_le hJSN hNN) (hCle c.2)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hcN (y : X) ⟨y, hy, rfl⟩).symm
  refine ⟨hsup, hinf, hcomm, hcenter, hJSC, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have hxJS : (((x : Cc) : X)) ∈ JS := x.2
    have hmem : (((x : Cc) : X)) ∈ JS ⊓ Na := ⟨hxJS, ⟨(x : Cc), hx, rfl⟩⟩
    rw [hinf] at hmem
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hmem))
  · intro w
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective Nc w
    have hcset : (c : X) ∈ ((JS ⊔ Na : Subgroup X) : Set X) := hCle c.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hJSC.trans (le_normalizer_map_of_normal Cc Nc hNn))] at hcset
    obtain ⟨a, ha, _, ⟨b, hb, rfl⟩, hab⟩ := Set.mem_mul.mp hcset
    refine ⟨⟨⟨a, hJSC ha⟩, ha⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have hc : c = ⟨a, hJSC ha⟩ * b := Subtype.ext hab.symm
    rw [hc]
    simpa using Nc.inv_mem hb

end CFSG.Semidihedral.StationarySevenNine

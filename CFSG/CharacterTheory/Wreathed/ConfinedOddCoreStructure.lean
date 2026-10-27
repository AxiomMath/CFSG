module

public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreSupport
public import CFSG.CharacterTheory.Wreathed.ConfinedOddCoreFrobenius

public section

open scoped Classical Pointwise commutatorElement

namespace CFSG.Wreathed.ConfinedOddCore

open CFSG.Wreathed.BaseFourCentralizerStructure CFSG.Wreathed.TorusSplitting

variable {G : Type} [Group G]

theorem mem_zpowers_of_pow_orderOf_eq_one {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {c a : A} (h : a ^ orderOf c = 1) : a ∈ Subgroup.zpowers c := by
  have hle : Subgroup.zpowers a ≤ Subgroup.zpowers c := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one h
  exact hle (Subgroup.mem_zpowers a)

theorem exists_prod_mulEquiv_of_commute (W A C : Subgroup G)
    (hcomm : ∀ g ∈ W, ∀ z ∈ A, g * z = z * g) (hWA : W ⊓ A = ⊥) (hsup : W ⊔ A = C) :
    ∃ μ : W × A ≃* C, ∀ z : W × A, (μ z : G) = z.1 * z.2 := by
  let μ0 : W × A →* G := W.subtype.noncommCoprod A.subtype fun g z => hcomm g g.2 z z.2
  have hrange : μ0.range = C := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      rw [← hsup]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left z.1.2) (Subgroup.mem_sup_right z.2.2)
    · rw [← hsup]
      apply sup_le
      · intro g hg
        refine ⟨(⟨g, hg⟩, 1), ?_⟩
        change g * ((1 : A) : G) = g
        simp
      · intro g hg
        refine ⟨(1, ⟨g, hg⟩), ?_⟩
        change ((1 : W) : G) * g = g
        simp
  have hinj : Function.Injective μ0 := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : (z.1 : G) * z.2 = 1 := hz
    have h2 : (z.1 : G) = (z.2 : G)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (z.1 : G) ∈ W ⊓ A := ⟨z.1.2, h2 ▸ A.inv_mem z.2.2⟩
    rw [hWA, Subgroup.mem_bot] at h3
    have h4 : (z.2 : G) = 1 := by
      rw [h3, one_mul] at h1
      exact h1
    exact Prod.ext (Subtype.ext h3) (Subtype.ext h4)
  let μ : W × A ≃* C := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact ⟨μ, fun z => rfl⟩

theorem conj_mem_oddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {g : G}
    (hg : g ∈ involutionCentralizer n S e) {r : G}
    (hr : r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) :
    g * r * g⁻¹ ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := by
  obtain ⟨r', hr', rfl⟩ := hr
  exact ⟨⟨g, hg⟩ * r' * (⟨g, hg⟩ : involutionCentralizer n S e)⁻¹,
    (inferInstance : (centralizerOddCore n S e).Normal).conj_mem r' hr' _, rfl⟩

theorem mem_normalizer_oddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) {g : G}
    (hg : g ∈ involutionCentralizer n S e) :
    g ∈ Subgroup.normalizer
      (((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype : Subgroup G) :
        Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_oddCore n S e hg
  · intro hh
    have h1 := conj_mem_oddCore n S e ((involutionCentralizer n S e).inv_mem hg) hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h1

theorem torusFixedCore_eq (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    torusFixedCore n S e = (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype ⊓
      Subgroup.centralizer {wreathModelHom S e (Original.x2 (2 ^ n))} := by
  ext g
  change g ∈ _ ⊓ Subgroup.centralizer (fourGroup n S e : Set G) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_inf, mem_centralizer_four_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hg, -, hgy⟩
    exact ⟨hg, hgy⟩
  · rintro ⟨hg, hgy⟩
    exact ⟨hg, Subgroup.map_subtype_le _ hg, hgy⟩

theorem oddCore_map_odd [Finite G] (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Odd (Nat.card ((centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)) := by
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact centralizerOddCore_card_odd n S e

theorem centralizer_le_of_conf (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    {r : G} (hr : r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hr1 : r ≠ 1) : Subgroup.centralizer {r} ≤ involutionCentralizer n S e :=
  (centralizer_singleton_le_normalizer_zpowers r).trans (hconf r hr hr1)

theorem fixed_core_malnormal [Finite G] (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    (hwA : ∀ z ∈ torusFixedCore n S e, wreathModelHom S e (Original.z (2 ^ n)) * z =
      z * wreathModelHom S e (Original.z (2 ^ n)))
    {a : G} (haodd : Odd (orderOf a))
    (hwa : (wreathModelHom S e (Original.z (2 ^ n)))⁻¹ * a *
      wreathModelHom S e (Original.z (2 ^ n)) = a⁻¹)
    (haN : a ∉ involutionCentralizer n S e) {u : G} (hu : u ∈ torusFixedCore n S e)
    (hau : a * u * a⁻¹ ∈ torusFixedCore n S e) : u = 1 := by
  set w := wreathModelHom S e (Original.z (2 ^ n)) with hwdef
  have hw2 : w * w = 1 := by
    rw [← sq, ← actual_orderOf_swap S e, pow_orderOf_eq_one]
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  have hwa' : w * a * w⁻¹ = a⁻¹ := by rw [hwinv]; nth_rewrite 1 [← hwinv]; exact hwa
  have hwu : w * u * w⁻¹ = u := by rw [hwA u hu, mul_inv_cancel_right]
  have hwv : w * (a * u * a⁻¹) * w⁻¹ = a * u * a⁻¹ := by rw [hwA _ hau, mul_inv_cancel_right]
  have h1 : a * u * a⁻¹ = a⁻¹ * u * a := by
    calc a * u * a⁻¹ = w * (a * u * a⁻¹) * w⁻¹ := hwv.symm
      _ = (w * a * w⁻¹) * (w * u * w⁻¹) * (w * a * w⁻¹)⁻¹ := by group
      _ = a⁻¹ * u * a := by rw [hwa', hwu, inv_inv]
  have h2 : Commute (a ^ 2) u := by
    rw [sq]
    change a * a * u = u * (a * a)
    calc a * a * u = a * (a * u * a⁻¹) * a := by group
      _ = a * (a⁻¹ * u * a) * a := by rw [h1]
      _ = u * (a * a) := by group
  have h3 : Commute a u := commute_of_sq_commute haodd h2
  by_contra hu1
  have huR : u ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype := hu.1
  apply haN
  exact centralizer_le_of_conf n S e hconf huR hu1
    (Subgroup.mem_centralizer_singleton_iff.mpr h3.eq)

theorem fixed_core_cyclic (W₀ A₀ C₀ : Subgroup G) (μ : W₀ × A₀ ≃* C₀)
    (hμ : ∀ z : W₀ × A₀, (μ z : G) = z.1 * z.2) [IsCyclic W₀] {a : G}
    (hconj : ∀ u ∈ A₀, a * u * a⁻¹ ∈ C₀) (hmal : ∀ u ∈ A₀, a * u * a⁻¹ ∈ A₀ → u = 1) :
    IsCyclic A₀ ∧ Nat.card A₀ ∣ Nat.card W₀ := by
  let κ : A₀ →* C₀ := ((MulAut.conj a).toMonoidHom.comp A₀.subtype).codRestrict C₀
    fun u => hconj u u.2
  let ψ : A₀ →* W₀ := (MonoidHom.fst W₀ A₀).comp (μ.symm.toMonoidHom.comp κ)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (μ.symm (κ u)).1 = 1 := hu
    have h2 : (κ u : G) = (μ.symm (κ u)).2 := by
      have h3 := hμ (μ.symm (κ u))
      rw [MulEquiv.apply_symm_apply, h1] at h3
      rw [h3]
      simp
    have h4 : a * (u : G) * a⁻¹ ∈ A₀ := by
      have h5 : (κ u : G) = a * (u : G) * a⁻¹ := rfl
      rw [← h5, h2]
      exact (μ.symm (κ u)).2.2
    exact Subtype.ext (hmal u u.2 h4)
  exact ⟨isCyclic_of_injective ψ hψ, Subgroup.card_dvd_of_injective ψ hψ⟩

theorem lift_commute_oddCore (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJR : J ⊓ centralizerOddCore n S e = ⊥) {g h : G}
    (hg : g ∈ J.map (involutionCentralizer n S e).subtype)
    (hh : h ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype) :
    g * h = h * g := by
  obtain ⟨g', hg', rfl⟩ := hg
  obtain ⟨h', hh', rfl⟩ := hh
  have hc : ⁅g', h'⁆ ∈ J ⊓ centralizerOddCore n S e :=
    Subgroup.commutator_le_inf J (centralizerOddCore n S e)
      (Subgroup.commutator_mem_commutator hg' hh')
  rw [hJR, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact congrArg Subtype.val hc

theorem x_mem_four (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom S e (Original.x (2 ^ n)) ∈ fourGroup n S e := by
  rw [x_eq_y_mul, y_eq]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem inverted_centralizer_trivial [Finite G] (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n))
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (W₀ : Subgroup G) (hW₀J : W₀ ≤ J.map (involutionCentralizer n S e).subtype)
    (hW₀A : W₀ ⊓ torusFixedCore n S e = ⊥)
    (hW₀Ac : ∀ g ∈ W₀, ∀ z ∈ torusFixedCore n S e, g * z = z * g)
    (μ : W₀ × torusFixedCore n S e ≃* torusCore n S e) (hμ : ∀ z, (μ z : G) = z.1 * z.2)
    [IsCyclic (torusFixedCore n S e)]
    {a : G} (haT : a ∈ Subgroup.normalizer (fourGroup n S e : Set G))
    (hacyc : ∀ v ∈ fourGroup n S e, v ≠ 1 → a * v * a⁻¹ ≠ v)
    {c : G} (hc : c ∈ torusFixedCore n S e) (hc1 : c ≠ 1)
    {v : G} (hv : v ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    (hvy : wreathModelHom S e (Original.x2 (2 ^ n)) * v *
      (wreathModelHom S e (Original.x2 (2 ^ n)))⁻¹ = v⁻¹) (hvc : v * c = c * v) : v = 1 := by
  set x := wreathModelHom S e (Original.x (2 ^ n)) with hxdef
  set y := wreathModelHom S e (Original.x2 (2 ^ n)) with hydef
  have hainv : a⁻¹ ∈ Subgroup.normalizer (fourGroup n S e : Set G) := Subgroup.inv_mem _ haT
  have hc' : a⁻¹ * c * a ∈ torusCore n S e := by
    have h1 := ambientOddCore_conj_mem _ (normalizer_le_normalizer_centralizer _ hainv)
      (torusFixedCore_le_torusCore n S e hc)
    rwa [inv_inv] at h1
  set z := μ.symm ⟨a⁻¹ * c * a, hc'⟩ with hzdef
  have hz : a⁻¹ * c * a = (z.1 : G) * z.2 := by
    rw [← hμ z, hzdef, MulEquiv.apply_symm_apply]
  have hcomm12 : Commute (z.1 : G) z.2 := hW₀Ac _ z.1.2 _ z.2.2
  have hk : (a⁻¹ * c * a) ^ orderOf c = 1 := by
    have h1 : (a⁻¹ * c * a⁻¹⁻¹) ^ orderOf c = a⁻¹ * c ^ orderOf c * a⁻¹⁻¹ := conj_pow
    rw [inv_inv] at h1
    rw [h1, pow_orderOf_eq_one, mul_one, inv_mul_cancel]
  have hpow : (z.1 : G) ^ orderOf c * (z.2 : G) ^ orderOf c = 1 := by
    rw [← hcomm12.mul_pow, ← hz, hk]
  have hz2 : (z.2 : G) ^ orderOf c = 1 := by
    have h1 : (z.1 : G) ^ orderOf c = ((z.2 : G) ^ orderOf c)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have h2 : (z.1 : G) ^ orderOf c ∈ W₀ ⊓ torusFixedCore n S e :=
      ⟨W₀.pow_mem z.1.2 _, h1 ▸ (torusFixedCore n S e).inv_mem
        ((torusFixedCore n S e).pow_mem z.2.2 _)⟩
    rw [hW₀A, Subgroup.mem_bot] at h2
    rw [h2, one_mul] at hpow
    exact hpow
  have hz2c : z.2 ∈ Subgroup.zpowers (⟨c, hc⟩ : torusFixedCore n S e) := by
    apply mem_zpowers_of_pow_orderOf_eq_one
    rw [Subgroup.orderOf_mk]
    exact Subtype.ext (by simpa using hz2)
  obtain ⟨j, hj⟩ := hz2c
  have hvz2 : v * z.2 = z.2 * v := by
    have h1 : (z.2 : G) = c ^ j := by rw [← hj]; simp
    rw [h1]
    exact ((Commute.zpow_right hvc j)).eq
  have hvz1 : v * z.1 = z.1 * v := (lift_commute_oddCore n S e J hJR (hW₀J z.1.2) hv).symm
  have hvconj : v * (a⁻¹ * c * a) = (a⁻¹ * c * a) * v := by
    rw [hz, ← mul_assoc, hvz1, mul_assoc, hvz2, ← mul_assoc]
  have hav : a * v * a⁻¹ ∈ Subgroup.centralizer {c} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * v * a⁻¹ * c = a * (v * (a⁻¹ * c * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * c * a) * v) * a⁻¹ := by rw [hvconj]
      _ = c * (a * v * a⁻¹) := by group
  have havN : a * v * a⁻¹ ∈ involutionCentralizer n S e :=
    centralizer_le_of_conf n S e hconf hc.1 hc1 hav
  have hxav : a * v * a⁻¹ * x = x * (a * v * a⁻¹) :=
    (mem_involutionCentralizer_iff n S e _).mp havN
  have hxT : x ∈ fourGroup n S e := x_mem_four n S e
  have hx1 : x ≠ 1 := by
    intro h
    have h1 := orderOf_x n hn S e
    rw [← hxdef, h, orderOf_one] at h1
    omega
  have hu : a⁻¹ * x * a ∈ fourGroup n S e := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hainv x).mp hxT
    rwa [inv_inv] at h1
  have hu1 : a⁻¹ * x * a ≠ 1 := by
    intro h
    apply hx1
    calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hux : a⁻¹ * x * a ≠ x := by
    intro h
    apply hacyc x hxT hx1
    calc a * x * a⁻¹ = a * (a⁻¹ * x * a) * a⁻¹ := by rw [h]
      _ = x := by group
  have hvN : v ∈ involutionCentralizer n S e := Subgroup.map_subtype_le _ hv
  have hxv : v * x = x * v := (mem_involutionCentralizer_iff n S e _).mp hvN
  have huv : (a⁻¹ * x * a) * v * (a⁻¹ * x * a)⁻¹ = v⁻¹ := by
    rcases eq_of_mem_four n hn S e hu with h | h | h | h
    · exact absurd h hu1
    · exact absurd h hux
    · rw [h]
      exact hvy
    · rw [h]
      calc y * x * v * (y * x)⁻¹ = y * (x * v * x⁻¹) * y⁻¹ := by group
        _ = y * v * y⁻¹ := by rw [← hxv, mul_inv_cancel_right]
        _ = v⁻¹ := hvy
  have huv' : (a⁻¹ * x * a) * v * (a⁻¹ * x * a)⁻¹ = v := by
    calc (a⁻¹ * x * a) * v * (a⁻¹ * x * a)⁻¹ = a⁻¹ * (x * (a * v * a⁻¹) * x⁻¹) * a := by group
      _ = a⁻¹ * (a * v * a⁻¹) * a := by rw [← hxav, mul_inv_cancel_right]
      _ = v := by group
  have hvv : v = v⁻¹ := huv'.symm.trans huv
  have hv2 : v ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 2 [hvv]
    exact mul_inv_cancel v
  exact eq_one_of_sq_eq_one (oddCore_map_odd n S e) hv hv2

theorem conj_mem_of_characteristic (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    {B : Subgroup G}
    (hBchar : (B.subgroupOf ((centralizerOddCore n S e).map
      (involutionCentralizer n S e).subtype)).Characteristic)
    (hBR : B ≤ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype)
    {k : G} (hk : k ∈ involutionCentralizer n S e) {v : G} (hv : v ∈ B) : k * v * k⁻¹ ∈ B := by
  set RG := (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype with hRG
  have hkinv : k⁻¹ ∈ involutionCentralizer n S e := (involutionCentralizer n S e).inv_mem hk
  let φ : RG ≃* RG :=
    { toFun := fun r => ⟨k⁻¹ * r * k⁻¹⁻¹, conj_mem_oddCore n S e hkinv r.2⟩
      invFun := fun r => ⟨k * r * k⁻¹, conj_mem_oddCore n S e hk r.2⟩
      left_inv := fun r => Subtype.ext (by simp only; group)
      right_inv := fun r => Subtype.ext (by simp only; group)
      map_mul' := fun r r' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hfix := hBchar.fixed φ
  have hmem : (⟨k * v * k⁻¹, conj_mem_oddCore n S e hk (hBR hv)⟩ : RG) ∈
      (B.subgroupOf RG).comap φ.toMonoidHom := by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    change k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ ∈ B
    rw [show k⁻¹ * (k * v * k⁻¹) * k⁻¹⁻¹ = v by group]
    exact hv
  rw [hfix] at hmem
  exact hmem

theorem confined_core_structure [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2) (hf : 1 ≤ f)
    (J : Subgroup (involutionCentralizer n S e)) [J.Normal]
    (hJR : J ⊓ centralizerOddCore n S e = ⊥)
    (hconf : ∀ r ∈ (centralizerOddCore n S e).map (involutionCentralizer n S e).subtype, r ≠ 1 →
      Subgroup.normalizer (Subgroup.zpowers r : Set G) ≤ involutionCentralizer n S e)
    (F : Type) [Field F] [Finite F] (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
    (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
    (ρ : centralizerFullQuotient n hn S e →*
      ComponentClassification.CatalogueSchreierLinearTwo.coordinateE F)
    (Ψ : CyclicCentralSL2Extension.SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
      (wreathModulus_even hn) Sigma hSigma ≃* centralizerOddCoreQuotient n S e)
    (hdata : ConditionalCompatibleModelData n hn S e p f F Sigma b hSigma ρ Ψ)
    (W₀ : Subgroup G)
    (hW₀mem : ∀ g, g ∈ W₀ ↔ g ∈ J.map (involutionCentralizer n S e).subtype ∧
      g * wreathModelHom S e (Original.x2 (2 ^ n)) = wreathModelHom S e (Original.x2 (2 ^ n)) * g ∧
      Odd (orderOf g))
    (hW₀C : W₀ ≤ torusCore n S e) (hW₀c : IsCyclic W₀)
    (hW₀A : W₀ ⊓ torusFixedCore n S e = ⊥)
    (hW₀Ac : ∀ g ∈ W₀, ∀ z ∈ torusFixedCore n S e, g * z = z * g)
    (hwA : ∀ z ∈ torusFixedCore n S e, wreathModelHom S e (Original.z (2 ^ n)) * z =
      z * wreathModelHom S e (Original.z (2 ^ n)))
    (hcard : ((2 ^ n : ℕ) : ℤ) * Nat.card W₀ =
      (Nat.card F : ℤ) - (if Nat.card F % 4 = 1 then 1 else -1))
    (hC₀ : torusCore n S e ≤ W₀ ⊔ torusFixedCore n S e) :
    let m := 2 ^ n
    let q := p ^ f
    let ε : ℤ := if q % 4 = 1 then 1 else -1
    let N := involutionCentralizer n S e
    let x : G := wreathModelHom S e (Original.x m)
    let y : G := wreathModelHom S e (Original.x2 m)
    let RG : Subgroup G := (centralizerOddCore n S e).map N.subtype
    let C₀ := torusCore n S e
    let A₀ := torusFixedCore n S e
    (∀ g, g ∈ A₀ ↔ g ∈ RG ∧ g * y = y * g) ∧
      W₀ ⊔ A₀ = C₀ ∧ W₀ ⊓ A₀ = ⊥ ∧ (∀ g ∈ W₀, ∀ z ∈ A₀, g * z = z * g) ∧
      (∃ μ : W₀ × A₀ ≃* C₀, ∀ z : W₀ × A₀, (μ z : G) = z.1 * z.2) ∧
      IsCyclic W₀ ∧ (m : ℤ) * Nat.card W₀ = q - ε ∧
      IsCyclic A₀ ∧ (Nat.card A₀ : ℤ) ∣ (q - ε) / m ∧
      ∃ B : Subgroup G, (∀ g, g ∈ B ↔ g ∈ RG ∧ y * g * y⁻¹ = g⁻¹) ∧ B ≤ RG ∧
        IsMulCommutative B ∧ (B.subgroupOf RG).Characteristic ∧ (B.subgroupOf RG).Normal ∧
        B ⊓ A₀ = ⊥ ∧ B ⊔ A₀ = RG ∧ (RG : Set G) = (B : Set G) * (A₀ : Set G) ∧
        B = ⁅RG, Subgroup.zpowers y⁆ ∧
        (∀ g ∈ N, orderOf g = 2 → g ≠ x →
          (∃ k ∈ N, k * y * k⁻¹ = g) ∧ ∀ v ∈ B, g * v * g⁻¹ = v⁻¹) ∧
        (A₀ ≠ ⊥ → (∀ a ∈ A₀, a ≠ 1 → RG ⊓ Subgroup.centralizer {a} = A₀) ∧
          (B ≠ ⊥ → ∀ a ∈ A₀, a ≠ 1 → ∀ v ∈ B, a * v * a⁻¹ = v → v = 1)) := by
  intro m q ε N x y RG C₀ A₀
  have hA₀eq : A₀ = RG ⊓ Subgroup.centralizer {y} := torusFixedCore_eq n S e
  have hA₀mem : ∀ g, g ∈ A₀ ↔ g ∈ RG ∧ g * y = y * g := by
    intro g
    rw [hA₀eq, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hA₀C₀ : A₀ ≤ C₀ := torusFixedCore_le_torusCore n S e
  have hsup : W₀ ⊔ A₀ = C₀ := le_antisymm (sup_le hW₀C hA₀C₀) hC₀
  obtain ⟨μ, hμ⟩ := exists_prod_mulEquiv_of_commute W₀ A₀ C₀ hW₀Ac hW₀A hsup
  obtain ⟨a, haT, haodd, hwa, hacyc⟩ := exists_inverted_cycling_element hnonab n hn S e
  have hx1 : x ≠ 1 := by
    intro h
    have h1 := orderOf_x n hn S e
    change orderOf x = 2 at h1
    rw [h, orderOf_one] at h1
    omega
  have haN : a ∉ N := by
    intro haN
    apply hacyc x (x_mem_four n S e) hx1
    have h1 := (mem_involutionCentralizer_iff n S e a).mp haN
    change a * x = x * a at h1
    rw [h1, mul_inv_cancel_right]
  have hconjA : ∀ u ∈ A₀, a * u * a⁻¹ ∈ C₀ := fun u hu =>
    ambientOddCore_conj_mem _ (normalizer_le_normalizer_centralizer _ haT) (hA₀C₀ hu)
  have hmal : ∀ u ∈ A₀, a * u * a⁻¹ ∈ A₀ → u = 1 := fun u hu hau =>
    fixed_core_malnormal n S e hconf hwA haodd hwa haN hu hau
  obtain ⟨hA₀cyc, hA₀dvd⟩ := fixed_core_cyclic W₀ A₀ C₀ μ hμ hconjA hmal
  have hP : ∀ c ∈ RG ⊓ Subgroup.centralizer {y}, c ≠ 1 → ∀ v ∈ RG, y * v * y⁻¹ = v⁻¹ →
      v * c = c * v → v = 1 := by
    intro c hc hc1 v hv hvy hvc
    rw [← hA₀eq] at hc
    exact inverted_centralizer_trivial n hn S e hconf J hJR W₀ (fun g hg => ((hW₀mem g).mp hg).1)
      hW₀A hW₀Ac μ hμ haT hacyc hc hc1 hv hvy hvc
  have hAcomm : ∀ a ∈ RG ⊓ Subgroup.centralizer {y}, ∀ b ∈ RG ⊓ Subgroup.centralizer {y},
      a * b = b * a := by
    rw [← hA₀eq]
    intro a ha b hb
    exact congrArg Subtype.val
      ((inferInstance : IsMulCommutative A₀).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨B, hBmem, hBR, hBcomm, hBnormal, hBchar, hBA, hBsup, hBset, hBcomm', hcases⟩ :=
    inverted_kernel_structure (oddCore_map_odd n S e) (orderOf_y n hn S e)
      (mem_normalizer_oddCore n S e (y_mem_involutionCentralizer n hn S e)) hAcomm hP
  rw [← hA₀eq] at hBA hBsup hBset hcases
  have hinv : ∀ g ∈ N, orderOf g = 2 → g ≠ x →
      (∃ k ∈ N, k * y * k⁻¹ = g) ∧ ∀ v ∈ B, g * v * g⁻¹ = v⁻¹ := by
    intro g hgN hg2 hgx
    have hg2' : orderOf (⟨g, hgN⟩ : N) = 2 := by rw [Subgroup.orderOf_mk]; exact hg2
    have hgx' : (⟨g, hgN⟩ : N) ≠ centralInvolution n S e := by
      intro h
      exact hgx (congrArg Subtype.val h)
    obtain ⟨k, hk⟩ := involution_isConj_y n hn S e p f hp hpodd hf F Sigma b hSigma ρ Ψ hdata
      ⟨g, hgN⟩ hg2' hgx'
    have hk' : (k : G) * y * (k : G)⁻¹ = g := congrArg Subtype.val hk
    refine ⟨⟨k, k.2, hk'⟩, fun v hv => ?_⟩
    have hv' : (k : G)⁻¹ * v * (k : G)⁻¹⁻¹ ∈ B :=
      conj_mem_of_characteristic n S e hBchar hBR ((involutionCentralizer n S e).inv_mem k.2) hv
    rw [inv_inv] at hv'
    have hyv := ((hBmem _).mp hv').2
    rw [← hk']
    calc (k : G) * y * (k : G)⁻¹ * v * ((k : G) * y * (k : G)⁻¹)⁻¹ =
        (k : G) * (y * ((k : G)⁻¹ * v * k) * y⁻¹) * (k : G)⁻¹ := by group
      _ = (k : G) * ((k : G)⁻¹ * v * k)⁻¹ * (k : G)⁻¹ := by rw [hyv]
      _ = v⁻¹ := by group
  have hFq : Nat.card F = q := hdata.card
  have hcard' : (m : ℤ) * Nat.card W₀ = q - ε := by
    rw [hFq] at hcard
    exact hcard
  have hdvd : (Nat.card A₀ : ℤ) ∣ (q - ε) / m := by
    rw [← hcard', Int.mul_ediv_cancel_left _ (by positivity)]
    exact Int.natCast_dvd_natCast.mpr hA₀dvd
  refine ⟨hA₀mem, hsup, hW₀A, hW₀Ac, ⟨μ, hμ⟩, hW₀c, hcard', hA₀cyc, hdvd, B, hBmem, hBR,
    hBcomm, hBchar, hBnormal, hBA, hBsup, hBset, hBcomm', hinv, fun hA0 => ?_⟩
  obtain ⟨h1, h2⟩ := hcases hA0
  exact ⟨h1, fun _ => h2⟩

end CFSG.Wreathed.ConfinedOddCore

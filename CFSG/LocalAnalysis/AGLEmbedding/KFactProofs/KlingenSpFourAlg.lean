module

public import CFSG.Open.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.AGLEmbedding.KlingenSpFour

open Matrix CFSG.Open
open scoped MatrixGroups

theorem card_eq_of_mem_iff_range {α G : Type*} [Group G] (K : Subgroup G) (f : α → G)
    (hf : Function.Injective f) (hK : ∀ g, g ∈ K ↔ ∃ a, g = f a) :
    Nat.card K = Nat.card α := by
  refine (Nat.card_eq_of_bijective (fun a : α => (⟨f a, (hK _).2 ⟨a, rfl⟩⟩ : K)) ⟨?_, ?_⟩).symm
  · intro a b hab
    exact hf (congrArg Subtype.val hab)
  · rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := (hK g).1 hg
    exact ⟨a, rfl⟩

structure HeisData (p : ℕ) (G : Type) [Group G] where
  e : ZMod p → ZMod p → ZMod p → G
  e_mul : ∀ s t u s' t' u', e s t u * e s' t' u' = e (s + s') (t + t') (u + u' - 2 * s' * t)
  e_inj : ∀ s t u s' t' u', e s t u = e s' t' u' → s = s' ∧ t = t' ∧ u = u'

namespace HeisData

section Basic

variable {p : ℕ} {G : Type} [Group G] (H : HeisData p G)

theorem e_congr {s s' t t' u u' : ZMod p} (hs : s = s') (ht : t = t') (hu : u = u') :
    H.e s t u = H.e s' t' u' := by
  subst hs ht hu
  rfl

theorem e_zero : H.e 0 0 0 = 1 := by
  have h : H.e 0 0 0 * H.e 0 0 0 = H.e 0 0 0 := by
    rw [H.e_mul]
    exact H.e_congr (by ring) (by ring) (by ring)
  exact mul_eq_left.1 h

theorem e_inv (s t u : ZMod p) : (H.e s t u)⁻¹ = H.e (-s) (-t) (-u - 2 * s * t) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [H.e_mul]
  exact (H.e_congr (by ring) (by ring) (by ring)).trans H.e_zero

theorem e_pow (s t u : ZMod p) (n : ℕ) :
    H.e s t u ^ n = H.e (n * s) (n * t) (n * u - n * (n - 1) * s * t) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact H.e_zero.symm.trans (H.e_congr (by simp) (by simp) (by simp))
  | succ n ih =>
    rw [pow_succ, ih, H.e_mul]
    exact H.e_congr (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)

theorem e_mul_D (s u s' u' : ZMod p) : H.e s 0 u * H.e s' 0 u' = H.e (s + s') 0 (u + u') := by
  rw [H.e_mul]
  exact H.e_congr rfl (by ring) (by ring)

theorem e_inv_D (s u : ZMod p) : (H.e s 0 u)⁻¹ = H.e (-s) 0 (-u) := by
  rw [H.e_inv]
  exact H.e_congr rfl (by ring) (by ring)

theorem e_mul_Z (u u' : ZMod p) : H.e 0 0 u * H.e 0 0 u' = H.e 0 0 (u + u') := by
  rw [H.e_mul]
  exact H.e_congr (by ring) (by ring) (by ring)

theorem e_inv_Z (u : ZMod p) : (H.e 0 0 u)⁻¹ = H.e 0 0 (-u) := by
  rw [H.e_inv]
  exact H.e_congr (by ring) (by ring) (by ring)

end Basic

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (H : HeisData p G)

@[expose] def E : Subgroup G where
  carrier := {g | ∃ s t u, g = H.e s t u}
  one_mem' := ⟨_, _, _, H.e_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, t, u, rfl⟩ ⟨s', t', u', rfl⟩
    exact ⟨_, _, _, H.e_mul s t u s' t' u'⟩
  inv_mem' := by
    rintro _ ⟨s, t, u, rfl⟩
    exact ⟨_, _, _, H.e_inv s t u⟩

@[expose] def D : Subgroup G where
  carrier := {g | ∃ s u, g = H.e s 0 u}
  one_mem' := ⟨_, _, H.e_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨s, u, rfl⟩ ⟨s', u', rfl⟩
    exact ⟨_, _, H.e_mul_D s u s' u'⟩
  inv_mem' := by
    rintro _ ⟨s, u, rfl⟩
    exact ⟨_, _, H.e_inv_D s u⟩

@[expose] def Z : Subgroup G where
  carrier := {g | ∃ u, g = H.e 0 0 u}
  one_mem' := ⟨_, H.e_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨u', rfl⟩
    exact ⟨_, H.e_mul_Z u u'⟩
  inv_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨_, H.e_inv_Z u⟩

omit [Fact p.Prime] in
theorem mem_E {g : G} : g ∈ H.E ↔ ∃ s t u, g = H.e s t u := Iff.rfl

theorem D_le_E : H.D ≤ H.E := by
  rintro _ ⟨s, u, rfl⟩
  exact ⟨s, 0, u, rfl⟩

theorem mem_center_E_iff (hp2 : p ≠ 2) (x : H.E) :
    x ∈ Subgroup.center H.E ↔ ∃ u, (x : G) = H.e 0 0 u := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  obtain ⟨x, s, t, u, rfl⟩ := x
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    have h1 : H.e 1 0 0 * H.e s t u = H.e s t u * H.e 1 0 0 :=
      congrArg Subtype.val (h ⟨H.e 1 0 0, 1, 0, 0, rfl⟩)
    have h3 : H.e 0 1 0 * H.e s t u = H.e s t u * H.e 0 1 0 :=
      congrArg Subtype.val (h ⟨H.e 0 1 0, 0, 1, 0, rfl⟩)
    rw [H.e_mul, H.e_mul] at h1 h3
    obtain ⟨-, -, h1⟩ := H.e_inj _ _ _ _ _ _ h1
    obtain ⟨-, -, h3⟩ := H.e_inj _ _ _ _ _ _ h3
    have ht : t = 0 :=
      (mul_eq_zero.1 (show (2 : ZMod p) * t = 0 by linear_combination h1)).resolve_left h2
    have hs : s = 0 :=
      (mul_eq_zero.1 (show (2 : ZMod p) * s = 0 by linear_combination -h3)).resolve_left h2
    subst hs ht
    exact ⟨u, rfl⟩
  · rintro ⟨u', hu'⟩ ⟨g, s', t', u'', rfl⟩
    have hu'' : H.e s t u = H.e 0 0 u' := hu'
    apply Subtype.ext
    show H.e s' t' u'' * H.e s t u = H.e s t u * H.e s' t' u''
    rw [hu'', H.e_mul, H.e_mul]
    exact H.e_congr (by ring) (by ring) (by ring)

omit [Fact p.Prime] in
theorem card_E : Nat.card H.E = p ^ 3 := by
  have hinj : Function.Injective (fun x : ZMod p × ZMod p × ZMod p => H.e x.1 x.2.1 x.2.2) := by
    rintro ⟨s, t, u⟩ ⟨s', t', u'⟩ h
    obtain ⟨rfl, rfl, rfl⟩ := H.e_inj _ _ _ _ _ _ h
    rfl
  rw [card_eq_of_mem_iff_range H.E _ hinj
    (fun g => ⟨fun ⟨s, t, u, h⟩ => ⟨(s, t, u), h⟩, fun ⟨⟨s, t, u⟩, h⟩ => ⟨s, t, u, h⟩⟩),
    Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring

omit [Fact p.Prime] in
theorem pow_eq_one_of_mem_E {x : G} (hx : x ∈ H.E) : x ^ p = 1 := by
  obtain ⟨s, t, u, rfl⟩ := hx
  rw [H.e_pow, ZMod.natCast_self]
  simp [H.e_zero]

theorem card_center_E (hp2 : p ≠ 2) : Nat.card (Subgroup.center H.E) = p := by
  have hinj : Function.Injective (fun u : ZMod p => H.e 0 0 u) := fun u u' h =>
    (H.e_inj _ _ _ _ _ _ h).2.2
  refine (Nat.card_eq_of_bijective (fun u : ZMod p =>
    (⟨⟨H.e 0 0 u, 0, 0, u, rfl⟩, (H.mem_center_E_iff hp2 _).2 ⟨u, rfl⟩⟩ :
      Subgroup.center H.E)) ⟨?_, ?_⟩).symm.trans (Nat.card_zmod p)
  · intro u u' h
    exact hinj (congrArg (fun x : Subgroup.center H.E => ((x : H.E) : G)) h)
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu⟩ := (H.mem_center_E_iff hp2 x).1 hx
    exact ⟨u, Subtype.ext (Subtype.ext hu.symm)⟩

theorem map_center_E (hp2 : p ≠ 2) : (Subgroup.center H.E).map H.E.subtype = H.Z := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (H.mem_center_E_iff hp2 x).1 hx
  · rintro ⟨u, rfl⟩
    exact ⟨⟨H.e 0 0 u, 0, 0, u, rfl⟩, (H.mem_center_E_iff hp2 _).2 ⟨u, rfl⟩, rfl⟩

theorem isElemAbelian_D : IsElemAbelian p H.D := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => H.pow_eq_one_of_mem_E (H.D_le_E hx)⟩
  obtain ⟨a, s, u, rfl⟩ := a
  obtain ⟨b, s', u', rfl⟩ := b
  show H.e s 0 u * H.e s' 0 u' = H.e s' 0 u' * H.e s 0 u
  rw [H.e_mul, H.e_mul]
  exact H.e_congr (by ring) (by ring) (by ring)

theorem card_D : Nat.card H.D = p ^ 2 := by
  have hinj : Function.Injective (fun x : ZMod p × ZMod p => H.e x.1 0 x.2) := by
    rintro ⟨s, u⟩ ⟨s', u'⟩ h
    obtain ⟨rfl, -, rfl⟩ := H.e_inj _ _ _ _ _ _ h
    rfl
  rw [card_eq_of_mem_iff_range H.D _ hinj
    (fun g => ⟨fun ⟨s, u, h⟩ => ⟨(s, u), h⟩, fun ⟨⟨s, u⟩, h⟩ => ⟨s, u, h⟩⟩),
    Nat.card_prod, Nat.card_zmod]
  ring

omit [Fact p.Prime] in
theorem exists_st (x : H.E) : ∃ st : ZMod p × ZMod p, ∃ u, (x : G) = H.e st.1 st.2 u := by
  obtain ⟨s, t, u, h⟩ := H.mem_E.mp x.2
  exact ⟨(s, t), u, h⟩

noncomputable def stE (x : H.E) : ZMod p × ZMod p := (H.exists_st x).choose

omit [Fact p.Prime] in
theorem stE_eq {x : H.E} {s t u : ZMod p} (hx : (x : G) = H.e s t u) : H.stE x = (s, t) := by
  obtain ⟨u', hu'⟩ := (H.exists_st x).choose_spec
  obtain ⟨h1, h2, -⟩ := H.e_inj _ _ _ _ _ _ (hu'.symm.trans hx)
  exact Prod.ext h1 h2

theorem stE_mul (x y : H.E) : H.stE (x * y) = H.stE x + H.stE y := by
  obtain ⟨s, t, u, hx⟩ := H.mem_E.mp x.2
  obtain ⟨s', t', u', hy⟩ := H.mem_E.mp y.2
  have hxy : ((x * y : H.E) : G) = H.e (s + s') (t + t') (u + u' - 2 * s' * t) := by
    rw [Subgroup.coe_mul, hx, hy, H.e_mul]
  rw [H.stE_eq hxy, H.stE_eq hx, H.stE_eq hy]
  rfl

noncomputable def coordHom : H.E →* Multiplicative (Fin 2 → ZMod p) :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd ![(H.stE x).2, -(H.stE x).1]) (by
    intro x y
    rw [H.stE_mul, ← ofAdd_add]
    congr 1
    ext i
    fin_cases i
    · rfl
    · exact neg_add _ _)

theorem coordHom_apply {x : H.E} {s t u : ZMod p} (hx : (x : G) = H.e s t u) :
    H.coordHom x = Multiplicative.ofAdd ![t, -s] := by
  change Multiplicative.ofAdd ![(H.stE x).2, -(H.stE x).1] = _
  rw [H.stE_eq hx]

theorem coordHom_surjective : Function.Surjective (H.coordHom) := by
  intro v
  refine ⟨⟨H.e (-(Multiplicative.toAdd v 1)) (Multiplicative.toAdd v 0) 0,
    H.mem_E.mpr ⟨_, _, _, rfl⟩⟩, ?_⟩
  rw [H.coordHom_apply (s := -(Multiplicative.toAdd v 1)) (t := Multiplicative.toAdd v 0)
    (u := 0) rfl]
  have hv : (![Multiplicative.toAdd v 0, -(-(Multiplicative.toAdd v 1))] : Fin 2 → ZMod p) =
      Multiplicative.toAdd v := by
    ext i
    fin_cases i
    · rfl
    · exact neg_neg _
  rw [hv]
  rfl

theorem ker_coordHom (hp2 : p ≠ 2) : H.coordHom.ker = Subgroup.center H.E := by
  ext x
  rw [MonoidHom.mem_ker, H.mem_center_E_iff hp2]
  obtain ⟨s, t, u, hx⟩ := H.mem_E.mp x.2
  rw [H.coordHom_apply hx]
  constructor
  · intro h
    have h' : (![t, -s] : Fin 2 → ZMod p) = 0 := h
    have ht : t = 0 := congrFun h' 0
    have hs : s = 0 := neg_eq_zero.mp (congrFun h' 1)
    exact ⟨u, by rw [hx, hs, ht]⟩
  · rintro ⟨u', hu'⟩
    obtain ⟨hs, ht, -⟩ := H.e_inj _ _ _ _ _ _ (hx.symm.trans hu')
    subst hs ht
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
    congr 1
    ext i
    fin_cases i
    · rfl
    · exact neg_zero

theorem hl_zero_aux {R : Type*} [CommRing R] (a b c d u : R) :
    a * 0 - b * 0 = 0 ∧ c * 0 - d * 0 = 0 ∧ u + 0 * 0 - 0 * 0 = u := by
  refine ⟨?_, ?_, ?_⟩ <;> ring

theorem mulVec_cons_neg {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) (s t : R) :
    g *ᵥ ![t, -s] = ![g 0 0 * t - g 0 1 * s, -(g 1 1 * s - g 1 0 * t)] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem exists_toGL_eq {a : GL (Fin 2) (ZMod p)} (ha : a ∈ CFSG.Open.StatedSL 2 (ZMod p)) :
    ∃ g : SL(2, ZMod p), Matrix.SpecialLinearGroup.toGL g = a := by
  have h : a ∈ CFSG.Assembly.LowTwoRank.StatedSL 2 (ZMod p) := ha
  rw [CFSG.Assembly.LowTwoRank.statedSL_eq_range_toGL] at h
  exact h

noncomputable def coordE (hp2 : p ≠ 2) :
    H.E ⧸ Subgroup.center H.E ≃* Multiplicative (Fin 2 → ZMod p) :=
  (QuotientGroup.quotientMulEquivOfEq (H.ker_coordHom hp2).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective H.coordHom H.coordHom_surjective)

theorem coordE_apply (hp2 : p ≠ 2) (s t u : ZMod p) :
    Multiplicative.toAdd (H.coordE hp2 (QuotientGroup.mk (⟨H.e s t u, s, t, u, rfl⟩ : H.E))) =
      ![t, -s] := by
  have h : H.coordE hp2 (QuotientGroup.mk (⟨H.e s t u, s, t, u, rfl⟩ : H.E)) =
      H.coordHom ⟨H.e s t u, H.mem_E.mpr ⟨s, t, u, rfl⟩⟩ := rfl
  rw [h, H.coordHom_apply (s := s) (t := t) (u := u) rfl]
  rfl

theorem l_range_le_centralizer (hp2 : p ≠ 2) (l : SL(2, ZMod p) →* G)
    (hl : ∀ (g : SL(2, ZMod p)) s t u, l g * H.e s t u * (l g)⁻¹ =
      H.e (g 1 1 * s - g 1 0 * t) (g 0 0 * t - g 0 1 * s)
        (u + s * t - (g 1 1 * s - g 1 0 * t) * (g 0 0 * t - g 0 1 * s))) :
    l.range ≤
      Subgroup.centralizer (((Subgroup.center H.E).map H.E.subtype : Subgroup G) : Set G) := by
  rw [H.map_center_E hp2]
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h := hl g 0 0 u
  have e12 := hl_zero_aux (g 1 1) (g 1 0) (g 0 0) (g 0 1) u
  rw [e12.1, e12.2.1, e12.2.2] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

theorem sl_action (hp2 : p ≠ 2) (l : SL(2, ZMod p) →* G)
    (hl : ∀ (g : SL(2, ZMod p)) s t u, l g * H.e s t u * (l g)⁻¹ =
      H.e (g 1 1 * s - g 1 0 * t) (g 0 0 * t - g 0 1 * s)
        (u + s * t - (g 1 1 * s - g 1 0 * t) * (g 0 0 * t - g 0 1 * s))) :
    CFSG.Open.StatedSL 2 (ZMod p) ≤ (l.range.subgroupOf (Subgroup.normalizer (H.E : Set G))).map
      (centerQuotientAction H.E (H.coordE hp2)) := by
  have hconj : ∀ (g : SL(2, ZMod p)) (x : G), x ∈ H.E → l g * x * (l g)⁻¹ ∈ H.E := by
    intro g x hx
    obtain ⟨s, t, u, rfl⟩ := H.mem_E.mp hx
    rw [hl g s t u]
    exact H.mem_E.mpr ⟨_, _, _, rfl⟩
  refine CFSG.AGLEmbedding.statedSL_le_map_centerQuotientAction H.E l.range (H.coordE hp2) ?_
  intro a ha
  obtain ⟨g, rfl⟩ := exists_toGL_eq ha
  refine ⟨l g, ⟨g, rfl⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj g x, fun hx => ?_⟩
    have h := hconj g⁻¹ _ hx
    have hx' : (l g)⁻¹ * (l g * x * (l g)⁻¹) * l g = x := by group
    rwa [map_inv, inv_inv, hx'] at h
  · intro u v huv
    obtain ⟨s, t, u₀, hu⟩ := H.mem_E.mp u.2
    have hu' : u = ⟨H.e s t u₀, H.mem_E.mpr ⟨s, t, u₀, rfl⟩⟩ := Subtype.ext hu
    have hv : (v : G) = H.e (g 1 1 * s - g 1 0 * t) (g 0 0 * t - g 0 1 * s)
        (u₀ + s * t - (g 1 1 * s - g 1 0 * t) * (g 0 0 * t - g 0 1 * s)) := by
      rw [huv, hu, hl]
    have hv' : v = ⟨H.e (g 1 1 * s - g 1 0 * t) (g 0 0 * t - g 0 1 * s)
        (u₀ + s * t - (g 1 1 * s - g 1 0 * t) * (g 0 0 * t - g 0 1 * s)),
          H.mem_E.mpr ⟨_, _, _, rfl⟩⟩ :=
      Subtype.ext hv
    rw [hu', hv', H.coordE_apply hp2, H.coordE_apply hp2]
    exact (mulVec_cons_neg (g : Matrix (Fin 2) (Fin 2) (ZMod p)) s t).symm

end HeisData

structure XData (p : ℕ) (G : Type) [Group G] where
  x : ZMod p → ZMod p → ZMod p → G
  x_mul : ∀ a b c a' b' c', x a b c * x a' b' c' = x (a + a') (b + b') (c + c')
  x_inj : ∀ a b c a' b' c', x a b c = x a' b' c' → a = a' ∧ b = b' ∧ c = c'

namespace XData
section Basic

variable {p : ℕ} {G : Type} [Group G] (X : XData p G)

theorem x_congr {a a' b b' c c' : ZMod p} (ha : a = a') (hb : b = b') (hc : c = c') :
    X.x a b c = X.x a' b' c' := by
  subst ha hb hc
  rfl

theorem x_zero : X.x 0 0 0 = 1 := by
  have h : X.x 0 0 0 * X.x 0 0 0 = X.x 0 0 0 := by
    rw [X.x_mul]
    exact X.x_congr (by ring) (by ring) (by ring)
  exact mul_eq_left.1 h

theorem x_inv (a b c : ZMod p) : (X.x a b c)⁻¹ = X.x (-a) (-b) (-c) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [X.x_mul]
  exact (X.x_congr (by ring) (by ring) (by ring)).trans X.x_zero

theorem x_pow (a b c : ZMod p) (n : ℕ) : X.x a b c ^ n = X.x (n * a) (n * b) (n * c) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact X.x_zero.symm.trans (X.x_congr (by simp) (by simp) (by simp))
  | succ n ih =>
    rw [pow_succ, ih, X.x_mul]
    exact X.x_congr (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)

end Basic

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] (X : XData p G)

@[expose] def U : Subgroup G where
  carrier := {g | ∃ a b c, g = X.x a b c}
  one_mem' := ⟨_, _, _, X.x_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
    exact ⟨_, _, _, X.x_mul a b c a' b' c'⟩
  inv_mem' := by
    rintro _ ⟨a, b, c, rfl⟩
    exact ⟨_, _, _, X.x_inv a b c⟩

omit [Fact p.Prime] in
theorem isElemAbelian_U : IsElemAbelian p X.U := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
  · obtain ⟨a, a₁, a₂, a₃, rfl⟩ := a
    obtain ⟨b, b₁, b₂, b₃, rfl⟩ := b
    show X.x a₁ a₂ a₃ * X.x b₁ b₂ b₃ = X.x b₁ b₂ b₃ * X.x a₁ a₂ a₃
    rw [X.x_mul, X.x_mul]
    exact X.x_congr (by ring) (by ring) (by ring)
  · obtain ⟨a, b, c, rfl⟩ := hg
    rw [X.x_pow, ZMod.natCast_self]
    simp [X.x_zero]

omit [Fact p.Prime] in
theorem card_U : Nat.card X.U = p ^ 3 := by
  have hinj : Function.Injective (fun v : ZMod p × ZMod p × ZMod p => X.x v.1 v.2.1 v.2.2) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    obtain ⟨rfl, rfl, rfl⟩ := X.x_inj _ _ _ _ _ _ h
    rfl
  rw [card_eq_of_mem_iff_range X.U _ hinj
    (fun g => ⟨fun ⟨a, b, c, h⟩ => ⟨(a, b, c), h⟩, fun ⟨⟨a, b, c⟩, h⟩ => ⟨a, b, c, h⟩⟩),
    Nat.card_prod, Nat.card_prod, Nat.card_zmod]
  ring
end XData

end CFSG.AGLEmbedding.KlingenSpFour

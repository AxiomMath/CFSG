module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Semidihedral.Principal

variable {G : Type*} [Group G]

@[expose] def conjugateLinearCharacter {D : Subgroup G} (n : Subgroup.normalizer (D : Set G))
    (ω : D →* ℂˣ) : D →* ℂˣ :=
  ω.comp (D.normalizerMonoidHom n⁻¹).toMonoidHom

@[expose] def conjugateLinearCharacters {D : Subgroup G} (H : Subgroup G) (ω : D →* ℂˣ) :
    Set (D →* ℂˣ) :=
  {χ | ∃ n : Subgroup.normalizer (D : Set G), (n : G) ∈ H ∧ χ = conjugateLinearCharacter n ω}

theorem coe_normalizerMonoidHom_apply {D : Subgroup G} (n : Subgroup.normalizer (D : Set G))
    (x : D) : ((D.normalizerMonoidHom n x : D) : G) = n * x * (n : G)⁻¹ := rfl

theorem inv_mul_mul_mem_of_mem_normalizer {D : Subgroup G}
    (n : Subgroup.normalizer (D : Set G)) (x : D) : (n : G)⁻¹ * x * n ∈ D := by
  have h := (Subgroup.mem_normalizer_iff.mp (n⁻¹).2 x).mp x.2
  simpa using h

theorem conjugateLinearCharacter_apply {D : Subgroup G} (n : Subgroup.normalizer (D : Set G))
    (ω : D →* ℂˣ) (x : D) :
    conjugateLinearCharacter n ω x =
      ω ⟨(n : G)⁻¹ * x * n, inv_mul_mul_mem_of_mem_normalizer n x⟩ := by
  change ω (D.normalizerMonoidHom n⁻¹ x) = _
  congr 1
  apply Subtype.ext
  rw [coe_normalizerMonoidHom_apply]
  simp

theorem conjugateLinearCharacter_one {D : Subgroup G} (ω : D →* ℂˣ) :
    conjugateLinearCharacter 1 ω = ω := by
  ext x
  rw [conjugateLinearCharacter_apply]
  congr 2
  apply Subtype.ext
  simp

theorem conjugateLinearCharacter_mul {D : Subgroup G} (n n' : Subgroup.normalizer (D : Set G))
    (ω : D →* ℂˣ) :
    conjugateLinearCharacter (n * n') ω =
      conjugateLinearCharacter n (conjugateLinearCharacter n' ω) := by
  ext x
  rw [conjugateLinearCharacter_apply, conjugateLinearCharacter_apply,
    conjugateLinearCharacter_apply]
  congr 2
  apply Subtype.ext
  simp [mul_assoc]

theorem conjugateLinearCharacter_of_mem {D : Subgroup G} (n : Subgroup.normalizer (D : Set G))
    (hn : (n : G) ∈ D) (ω : D →* ℂˣ) : conjugateLinearCharacter n ω = ω := by
  ext x
  rw [conjugateLinearCharacter_apply]
  have h : (⟨(n : G)⁻¹ * x * n, inv_mul_mul_mem_of_mem_normalizer n x⟩ : D) =
      ⟨n, hn⟩⁻¹ * x * ⟨n, hn⟩ := by
    apply Subtype.ext
    simp
  rw [h, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

theorem conjugateLinearCharacter_inv_cancel {D : Subgroup G}
    (n : Subgroup.normalizer (D : Set G)) (ω : D →* ℂˣ) :
    conjugateLinearCharacter n⁻¹ (conjugateLinearCharacter n ω) = ω := by
  rw [← conjugateLinearCharacter_mul, inv_mul_cancel, conjugateLinearCharacter_one]

theorem conjugateLinearCharacter_injective {D : Subgroup G} (n : Subgroup.normalizer (D : Set G)) :
    Function.Injective (conjugateLinearCharacter n : (D →* ℂˣ) → (D →* ℂˣ)) := fun ω ω' h => by
  rw [← conjugateLinearCharacter_inv_cancel n ω, h,
    conjugateLinearCharacter_inv_cancel]

theorem orderOf_inv_mul_mul (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
  simpa using h

theorem confined_odd_factor_gives_free_six_element_torus_character_orbit [Finite G]
    (S : Sylow 2 G) (t : G)
    (hZ : (S : Subgroup G) ⊓ Subgroup.centralizer (S : Set G) = Subgroup.zpowers t)
    (ht : orderOf t = 2) (V : Subgroup G) (hV : IsKleinFour V) (htV : t ∈ V)
    (C D M K : Subgroup G) (hC : C = Subgroup.centralizer {t})
    (hD : D = Subgroup.centralizer (V : Set G)) (hM : M = Subgroup.normalizer (V : Set G))
    (hK : K = M ⊓ C) (hsurj : Function.Surjective V.normalizerMonoidHom) (A W : Subgroup G)
    (hDVAW : ∃ e : (V × A × W) ≃* D, ∀ x : V × A × W, (e x : G) = x.1 * x.2.1 * x.2.2)
    (hAodd : Odd (Nat.card A)) (hWcyc : IsCyclic W) (hWodd : Odd (Nat.card W))
    (hW1 : 1 < Nat.card W) (hAK : (A.subgroupOf K).Normal) (hSA : ⁅(S : Subgroup G), A⁆ = ⊥)
    (hCA : Subgroup.centralizer (A : Set G) ≤ C)
    (hy : ∃ y ∈ K, y ∉ D ∧ ∀ d ∈ D, y * d * y⁻¹ * d ∈ V ⊔ A) :
    Subgroup.normalizer (A : Set G) ⊓ M = K ∧ M ≤ Subgroup.normalizer (D : Set G) ∧
    (∃ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A → ω x = 1) ∧
      ∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) ∧
    (∀ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A → ω x = 1) →
      (∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) →
      (∀ x : D, ω x = 1 ↔ (x : G) ∈ V ⊔ A) ∧
      (∀ n : Subgroup.normalizer (D : Set G), (n : G) ∈ M →
        (conjugateLinearCharacter n ω = ω ↔ (n : G) ∈ D)) ∧
      (conjugateLinearCharacters M ω).ncard = 6 ∧
      (∀ χ ∈ conjugateLinearCharacters M ω, (conjugateLinearCharacters K χ).ncard = 2) ∧
      ((conjugateLinearCharacters M ω).image (conjugateLinearCharacters K)).ncard = 3) ∧
    K.relIndex M = 3 ∧ D.relIndex K = 2 := by
  classical
  have hVcomm : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v := fun v hv v' hv' =>
    congrArg Subtype.val ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm ⟨v, hv⟩ ⟨v', hv'⟩)
  have hVD : V ≤ D := by
    intro v hv
    rw [hD, Subgroup.mem_centralizer_iff]
    intro v' hv'
    exact hVcomm v' hv' v hv
  have hDC : D ≤ C := by
    intro x hx
    rw [hD, Subgroup.mem_centralizer_iff] at hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hx g htV
  have hDM : D ≤ M := by
    rw [hD, hM]
    exact Subgroup.centralizer_le_normalizer _
  have hKM : K ≤ M := hK ▸ inf_le_left
  have hKC : K ≤ C := hK ▸ inf_le_right
  have hDK : D ≤ K := hK ▸ le_inf hDM hDC
  have hMN : M ≤ Subgroup.normalizer (D : Set G) := by
    intro m hm
    rw [hM, Subgroup.mem_normalizer_iff] at hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hD, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx v hv
      have hv' : m⁻¹ * v * m ∈ V :=
        (hm (m⁻¹ * v * m)).mpr (by rw [show m * (m⁻¹ * v * m) * m⁻¹ = v by group]; exact hv)
      have := hx _ hv'
      calc v * (m * x * m⁻¹) = m * ((m⁻¹ * v * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * v * m)) * m⁻¹ := by rw [this]
        _ = m * x * m⁻¹ * v := by group
    · intro hx v hv
      have hv' : m * v * m⁻¹ ∈ V := (hm v).mp hv
      have := hx _ hv'
      calc v * x = m⁻¹ * ((m * v * m⁻¹) * (m * x * m⁻¹)) * m := by group
        _ = m⁻¹ * ((m * x * m⁻¹) * (m * v * m⁻¹)) * m := by rw [this]
        _ = x * v := by group
  obtain ⟨e, he⟩ := hDVAW
  have hdecomp : ∀ x : D, (x : G) = ((e.symm x).1 : G) * (e.symm x).2.1 * (e.symm x).2.2 := by
    intro x
    rw [← he, MulEquiv.apply_symm_apply]
  have hAD : A ≤ D := fun a ha => by
    have h := (e (1, ⟨a, ha⟩, 1)).2
    rw [he] at h
    simpa using h
  have hWD : W ≤ D := fun w hw => by
    have h := (e (1, 1, ⟨w, hw⟩)).2
    rw [he] at h
    simpa using h
  have hsymmV : ∀ v : V, e.symm ⟨v, hVD v.2⟩ = (v, 1, 1) := by
    intro v
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [he]
    simp
  have hsymmA : ∀ a : A, e.symm ⟨a, hAD a.2⟩ = (1, a, 1) := by
    intro a
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [he]
    simp
  have hsymmW : ∀ w : W, e.symm ⟨w, hWD w.2⟩ = (1, 1, w) := by
    intro w
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [he]
    simp
  let πW : D →* W :=
    (MonoidHom.snd A W).comp ((MonoidHom.snd V (A × W)).comp e.symm.toMonoidHom)
  have hπW : ∀ x : D, πW x = (e.symm x).2.2 := fun x => rfl
  have hVA_iff : ∀ x : D, (x : G) ∈ V ⊔ A ↔ (e.symm x).2.2 = 1 := by
    intro x
    constructor
    · intro hx
      have hle : V ⊔ A ≤ (πW.ker).map D.subtype := by
        apply sup_le
        · intro v hv
          refine ⟨⟨v, hVD hv⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, hπW, hsymmV ⟨v, hv⟩]
        · intro a ha
          refine ⟨⟨a, hAD ha⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, MonoidHom.mem_ker, hπW, hsymmA ⟨a, ha⟩]
      obtain ⟨x', hx', hxx'⟩ := hle hx
      have : x' = x := Subtype.ext hxx'
      rw [← this]
      exact hx'
    · intro hx
      rw [hdecomp x, hx]
      simp only [OneMemClass.coe_one, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (e.symm x).1.2)
        (Subgroup.mem_sup_right (e.symm x).2.1.2)
  have hker : ∀ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A → ω x = 1) →
      (∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) →
      ∀ x : D, ω x = 1 ↔ (x : G) ∈ V ⊔ A := by
    intro ω hω1 hωW x
    refine ⟨fun h => ?_, hω1 x⟩
    have hsplit : x = e ((e.symm x).1, (e.symm x).2.1, 1) * e (1, 1, (e.symm x).2.2) := by
      rw [← map_mul]
      apply e.symm.injective
      rw [MulEquiv.symm_apply_apply]
      simp
    have h1 : ω (e ((e.symm x).1, (e.symm x).2.1, 1)) = 1 :=
      hω1 _ (by rw [hVA_iff, MulEquiv.symm_apply_apply])
    rw [hsplit, map_mul, h1, one_mul] at h
    have hw : ((e (1, 1, (e.symm x).2.2) : D) : G) = 1 := hωW _ (by rw [he]; simp) h
    rw [he] at hw
    simp only [OneMemClass.coe_one, one_mul] at hw
    rw [hVA_iff]
    exact Subtype.ext hw
  have hoddA : ∀ x : D, (x : G) ∈ V ⊔ A → Odd (orderOf (x : G)) → (x : G) ∈ A := by
    intro x hx hodd
    rw [hVA_iff] at hx
    have hxva : (x : G) = ((e.symm x).1 : G) * (e.symm x).2.1 := by
      rw [hdecomp x, hx]
      simp
    set v : V := (e.symm x).1
    set a : A := (e.symm x).2.1
    have hv2 : (v : G) ^ 2 = 1 := by
      rw [sq]
      exact congrArg Subtype.val (IsKleinFour.mul_self v)
    have hcomm : Commute (v : G) (a : G) := by
      have ha : (a : G) ∈ D := hAD a.2
      rw [hD, Subgroup.mem_centralizer_iff] at ha
      exact (ha v v.2)
    have ha1 : (a : G) ^ Nat.card A = 1 := by
      have := pow_card_eq_one' (x := a)
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := hAodd
    have hxA : (x : G) ^ Nat.card A = v := by
      rw [hxva, hcomm.mul_pow, ha1, mul_one, hk, pow_succ, pow_mul, hv2, one_pow, one_mul]
    have hvord : (v : G) ^ orderOf (x : G) = 1 := by
      rw [← hxA, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
    have hv1 : (v : G) = 1 := by
      have h1 := orderOf_dvd_of_pow_eq_one hvord
      have h2 := orderOf_dvd_of_pow_eq_one hv2
      have h3 : orderOf (v : G) ∣ Nat.gcd (orderOf (x : G)) 2 := Nat.dvd_gcd h1 h2
      rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_right.mpr hodd), Nat.dvd_one,
        orderOf_eq_one_iff] at h3
      exact h3
    rw [hxva, hv1, one_mul]
    exact a.2
  have hAK' : K ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_trans hAD hDK)).mp hAK
  have hNAC : ∀ m ∈ Subgroup.normalizer (A : Set G), m ∈ C := by
    intro m hm
    have hSs : ∀ x ∈ (S : Subgroup G), x * (m⁻¹ * t * m) = (m⁻¹ * t * m) * x := by
      intro x hx
      have hxA : x ∈ Subgroup.centralizer (A : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hSA) hx
      have hmx : m * x * m⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
        rw [Subgroup.mem_centralizer_iff] at hxA ⊢
        intro a ha
        have ha' : m⁻¹ * a * m ∈ A :=
          (Subgroup.mem_normalizer_iff.mp hm (m⁻¹ * a * m)).mpr (by group; exact ha)
        have := hxA _ ha'
        calc a * (m * x * m⁻¹) = m * ((m⁻¹ * a * m) * x) * m⁻¹ := by group
          _ = m * (x * (m⁻¹ * a * m)) * m⁻¹ := by rw [this]
          _ = m * x * m⁻¹ * a := by group
      have hmxC := hCA hmx
      rw [hC, Subgroup.mem_centralizer_iff] at hmxC
      have := hmxC t (Set.mem_singleton t)
      calc x * (m⁻¹ * t * m) = m⁻¹ * ((m * x * m⁻¹) * t) * m := by group
        _ = m⁻¹ * (t * (m * x * m⁻¹)) * m := by rw [this]
        _ = (m⁻¹ * t * m) * x := by group
    have hs2 : orderOf (m⁻¹ * t * m) = 2 := by rw [orderOf_inv_mul_mul, ht]
    have hP : IsPGroup 2 ((S : Subgroup G) ⊔ Subgroup.zpowers (m⁻¹ * t * m) : Subgroup G) := by
      apply IsPGroup.to_sup_of_normal_right' S.isPGroup'
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
      · intro x hx
        apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        exact ((Commute.zpow_left (hSs x hx).symm k)).eq
    have hsS : m⁻¹ * t * m ∈ (S : Subgroup G) := by
      have := S.is_maximal' hP le_sup_left
      rw [← this]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hsZ : m⁻¹ * t * m ∈ Subgroup.zpowers t := by
      rw [← hZ]
      exact ⟨hsS, Subgroup.mem_centralizer_iff.mpr fun x hx => hSs x hx⟩
    obtain ⟨k, hk, hkt⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hsZ)
    rw [ht, Finset.mem_range] at hk
    have hst : m⁻¹ * t * m = t := by
      interval_cases k
      · exfalso
        rw [pow_zero] at hkt
        have : t = 1 := by
          calc t = m * (m⁻¹ * t * m) * m⁻¹ := by group
            _ = 1 := by rw [← hkt]; group
        rw [this, orderOf_one] at ht
        omega
      · rw [pow_one] at hkt
        exact hkt.symm
    rw [hC, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc g * m = m * (m⁻¹ * g * m) := by group
      _ = m * g := by rw [hst]
  have hNMA : Subgroup.normalizer (A : Set G) ⊓ M = K := by
    apply le_antisymm
    · intro m hm
      rw [hK]
      exact ⟨hm.2, hNAC m hm.1⟩
    · exact le_inf hAK' hKM
  obtain ⟨y, hyK, hyD, hyinv⟩ := hy
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have hVcard : Nat.card V = 4 := IsKleinFour.card_four
  obtain ⟨u, huV, hu1, hut⟩ : ∃ u ∈ V, u ≠ 1 ∧ u ≠ t := by
    by_contra h
    push Not at h
    have hsub : (V : Set G) ⊆ {1, t} := fun v hv => by
      by_cases hv1 : v = 1
      · exact Or.inl hv1
      · exact Or.inr (h v hv hv1)
    have hle : Nat.card V ≤ 2 := by
      calc Nat.card V = (V : Set G).ncard := (Nat.card_coe_set_eq _)
        _ ≤ ({1, t} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ ({t} : Set G).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by rw [Set.ncard_singleton]
    omega
  have hneV : ∀ {a b : G} (ha : a ∈ V) (hb : b ∈ V), a ≠ b → (⟨a, ha⟩ : V) ≠ ⟨b, hb⟩ :=
    fun _ _ h h' => h (congrArg Subtype.val h')
  have hcases : ∀ v ∈ V, v = 1 ∨ v = t ∨ v = u ∨ v = t * u := by
    intro v hv
    by_cases h1 : v = 1
    · exact Or.inl h1
    by_cases h2 : v = t
    · exact Or.inr (Or.inl h2)
    by_cases h3 : v = u
    · exact Or.inr (Or.inr (Or.inl h3))
    refine Or.inr (Or.inr (Or.inr ?_))
    have := IsKleinFour.eq_mul_of_ne_all (x := (⟨t, htV⟩ : V)) (y := ⟨u, huV⟩)
      (z := ⟨v, hv⟩) (hneV htV V.one_mem ht1) (hneV huV V.one_mem hu1)
      (hneV htV huV (Ne.symm hut)) (hneV hv V.one_mem h1) (hneV hv htV h2) (hneV hv huV h3)
    exact congrArg Subtype.val this
  have hcentV : ∀ g : G, g * t * g⁻¹ = t → g * u * g⁻¹ = u → g ∈ D := by
    intro g hgt hgu
    have hgt' : t * g = g * t := by
      calc t * g = (g * t * g⁻¹) * g := by rw [hgt]
        _ = g * t := by group
    have hgu' : u * g = g * u := by
      calc u * g = (g * u * g⁻¹) * g := by rw [hgu]
        _ = g * u := by group
    rw [hD, Subgroup.mem_centralizer_iff]
    intro v hv
    rcases hcases v hv with rfl | rfl | rfl | rfl
    · simp
    · exact hgt'
    · exact hgu'
    · rw [mul_assoc, hgu', ← mul_assoc, hgt', mul_assoc]
  have hKt : ∀ k ∈ K, k * t * k⁻¹ = t := by
    intro k hk
    have h := hKC hk
    rw [hC, Subgroup.mem_centralizer_iff] at h
    rw [← h t (Set.mem_singleton t)]
    group
  have hKt' : ∀ k ∈ K, k⁻¹ * t * k = t := by
    intro k hk
    calc k⁻¹ * t * k = k⁻¹ * (k * t * k⁻¹) * k := by rw [hKt k hk]
      _ = t := by group
  have hKV : ∀ k ∈ K, ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
    intro k hk v hv
    have h := hKM hk
    rw [hM, Subgroup.mem_normalizer_iff] at h
    exact (h v).mp hv
  have hswap : ∀ k ∈ K, k ∉ D → k * u * k⁻¹ = t * u := by
    intro k hk hkD
    have hkuV := hKV k hk u huV
    have hne1 : k * u * k⁻¹ ≠ 1 := fun h => hu1 (by
      calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
        _ = 1 := by rw [h]; group)
    have hnet : k * u * k⁻¹ ≠ t := fun h => hut (by
      calc u = k⁻¹ * (k * u * k⁻¹) * k := by group
        _ = k⁻¹ * t * k := by rw [h]
        _ = t := hKt' k hk)
    have hneu : k * u * k⁻¹ ≠ u := fun h => hkD (hcentV k (hKt k hk) h)
    have := IsKleinFour.eq_mul_of_ne_all (x := (⟨t, htV⟩ : V)) (y := ⟨u, huV⟩)
      (z := ⟨k * u * k⁻¹, hkuV⟩) (hneV htV V.one_mem ht1) (hneV huV V.one_mem hu1)
      (hneV htV huV (Ne.symm hut)) (hneV hkuV V.one_mem hne1) (hneV hkuV htV hnet)
      (hneV hkuV huV hneu)
    exact congrArg Subtype.val this
  have hcoset : ∀ k ∈ K, ∀ k' ∈ K, k ∉ D → k' ∉ D → k⁻¹ * k' ∈ D := by
    intro k hk k' hk' hkD hk'D
    apply hcentV
    · calc k⁻¹ * k' * t * (k⁻¹ * k')⁻¹ = k⁻¹ * (k' * t * k'⁻¹) * k := by group
        _ = k⁻¹ * t * k := by rw [hKt k' hk']
        _ = t := hKt' k hk
    · calc k⁻¹ * k' * u * (k⁻¹ * k')⁻¹ = k⁻¹ * (k' * u * k'⁻¹) * k := by group
        _ = k⁻¹ * (t * u) * k := by rw [hswap k' hk' hk'D]
        _ = k⁻¹ * (k * u * k⁻¹) * k := by rw [hswap k hk hkD]
        _ = u := by group
  have hKD : D.relIndex K = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨y, hyK⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ D
    · have hby : (b : G) * y ∉ D := fun h => hyD (by simpa using D.mul_mem (D.inv_mem hb) h)
      simp [hb, hby]
    · have hby : (b : G) * y ∈ D := by
        have := hcoset (b : G)⁻¹ (K.inv_mem b.2) y hyK
          (fun h => hb (by simpa using D.inv_mem h)) hyD
        simpa using this
      simp [hb, hby]
  have hMK : K.relIndex M = 3 := by
    have h1 : K.relIndex M = (C.subgroupOf M).index := by
      rw [Subgroup.relIndex, hK, Subgroup.inf_subgroupOf_left]
    rw [h1]
    subst hM
    have hstab : C.subgroupOf (Subgroup.normalizer (V : Set G)) =
        MulAction.stabilizer (Subgroup.normalizer (V : Set G)) (⟨t, htV⟩ : V) := by
      ext n
      rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, hC,
        Subgroup.mem_centralizer_iff]
      constructor
      · intro h
        apply Subtype.ext
        change (n : G) * t * (n : G)⁻¹ = t
        rw [← h t (Set.mem_singleton t)]
        group
      · intro h g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        have h' : (n : G) * g * (n : G)⁻¹ = g := congrArg Subtype.val h
        calc g * n = ((n : G) * g * (n : G)⁻¹) * n := by rw [h']
          _ = n * g := by group
    rw [hstab, MulAction.index_stabilizer]
    have horbit : MulAction.orbit (Subgroup.normalizer (V : Set G)) (⟨t, htV⟩ : V) =
        {v : V | v ≠ 1} := by
      ext v
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨n, rfl⟩ h
        have h' := congrArg (fun z : V => n⁻¹ • z) h
        simp only [inv_smul_smul, smul_one] at h'
        exact ht1 (congrArg Subtype.val h')
      · intro hv
        have ht'1 : (⟨t, htV⟩ : V) ≠ 1 := hneV htV V.one_mem ht1
        let σ : V ≃* V := IsKleinFour.mulEquiv' (Equiv.swap ⟨t, htV⟩ v)
          (Equiv.swap_apply_of_ne_of_ne ht'1.symm hv.symm) IsKleinFour.exponent_two
        obtain ⟨n, hn⟩ := hsurj σ
        refine ⟨n, ?_⟩
        change V.normalizerMonoidHom n ⟨t, htV⟩ = v
        rw [hn]
        exact Equiv.swap_apply_left _ _
    rw [horbit]
    have : Fintype V := Fintype.ofFinite V
    rw [show {v : V | v ≠ 1} = ((Finset.univ : Finset V).erase 1 : Set V) by ext; simp,
      Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hVcard]
  have hMD : D.relIndex M = 6 := by
    rw [← Subgroup.relIndex_mul_relIndex D K M hDK hKM, hKD, hMK]
  have hWne : Nat.card W ≠ 0 := by omega
  have : NeZero (Nat.card W) := ⟨hWne⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : W →* ℂˣ, Function.Injective ζ := by
    have hcard : Nat.card W = Nat.card (rootsOfUnity (Nat.card W) ℂ) :=
      (Complex.card_rootsOfUnity _).symm
    let f := mulEquivOfCyclicCardEq hcard
    exact ⟨(rootsOfUnity (Nat.card W) ℂ).subtype.comp f.toMonoidHom,
      Subtype.val_injective.comp f.injective⟩
  have hπWW : ∀ x : D, ∀ hx : (x : G) ∈ W, πW x = ⟨x, hx⟩ := by
    intro x hx
    rw [hπW]
    exact congrArg (fun p : V × A × W => p.2.2) (hsymmW ⟨(x : G), hx⟩)
  have hexists : ∃ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A → ω x = 1) ∧
      ∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1 := by
    refine ⟨ζ.comp πW, fun x hx => ?_, fun x hx h => ?_⟩
    · rw [MonoidHom.comp_apply, hπW, (hVA_iff x).mp hx, map_one]
    · rw [MonoidHom.comp_apply, hπWW x hx] at h
      exact congrArg Subtype.val (hζ (h.trans (map_one ζ).symm))
  have hyN : y ∈ Subgroup.normalizer (D : Set G) := hMN (hKM hyK)
  obtain ⟨w, hw1⟩ : ∃ w : W, w ≠ 1 := by
    have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp hW1
    exact exists_ne 1
  have hstabω : ∀ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A → ω x = 1) →
      (∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) →
      ∀ n : Subgroup.normalizer (D : Set G), (n : G) ∈ M →
        (conjugateLinearCharacter n ω = ω ↔ (n : G) ∈ D) := by
    intro ω hω1 hωW n hnM
    refine ⟨fun h => ?_, fun h => conjugateLinearCharacter_of_mem n h ω⟩
    have hVA : ∀ x : D, (x : G) ∈ V ⊔ A → (n : G)⁻¹ * x * n ∈ V ⊔ A := by
      intro x hx
      have h1 : conjugateLinearCharacter n ω x = 1 := by rw [h]; exact hω1 x hx
      rw [conjugateLinearCharacter_apply] at h1
      exact (hker ω hω1 hωW _).mp h1
    have hA' : ∀ a ∈ A, (n : G)⁻¹ * a * n ∈ A := by
      intro a ha
      have hx := hVA ⟨a, hAD ha⟩ (Subgroup.mem_sup_right ha)
      refine hoddA ⟨(n : G)⁻¹ * a * n, inv_mul_mul_mem_of_mem_normalizer n ⟨a, hAD ha⟩⟩ hx ?_
      change Odd (orderOf ((n : G)⁻¹ * a * n))
      rw [orderOf_inv_mul_mul]
      exact Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A ha)
    have hnA : (n : G) ∈ Subgroup.normalizer (A : Set G) := by
      have hle : A.map (MulAut.conj (n : G)⁻¹).toMonoidHom ≤ A := by
        rintro _ ⟨a, ha, rfl⟩
        simpa using hA' a ha
      have heq : A.map (MulAut.conj (n : G)⁻¹).toMonoidHom = A :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Subgroup.card_map_of_injective (MulAut.conj _).injective])
      rw [Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        rw [← heq] at hg
        obtain ⟨a, ha, rfl⟩ := hg
        simpa [mul_assoc] using ha
      · intro hg
        have := hA' _ hg
        simpa [mul_assoc] using this
    have hnK : (n : G) ∈ K := hNMA ▸ ⟨hnA, hnM⟩
    by_contra hnD
    have hyn : y⁻¹ * n ∈ D := hcoset y hyK n hnK hyD hnD
    have hconj : conjugateLinearCharacter n ω = conjugateLinearCharacter ⟨y, hyN⟩ ω := by
      have hsplit : n = ⟨y, hyN⟩ * ⟨y⁻¹ * n, hMN (hDM hyn)⟩ := Subtype.ext (by simp)
      rw [hsplit, conjugateLinearCharacter_mul,
        conjugateLinearCharacter_of_mem ⟨y⁻¹ * n, hMN (hDM hyn)⟩ hyn]
    have hyω : ∀ x : D, conjugateLinearCharacter ⟨y, hyN⟩ ω x = (ω x)⁻¹ := by
      intro x
      rw [conjugateLinearCharacter_apply]
      have hd := hyinv _ (inv_mul_mul_mem_of_mem_normalizer ⟨y, hyN⟩ x)
      have hxd : (x : G) * (y⁻¹ * x * y) ∈ V ⊔ A := by
        simpa [mul_assoc] using hd
      have h1 := hω1 (x * ⟨y⁻¹ * x * y, inv_mul_mul_mem_of_mem_normalizer ⟨y, hyN⟩ x⟩) hxd
      rw [map_mul] at h1
      exact eq_inv_of_mul_eq_one_right h1
    have hww : ω ⟨w, hWD w.2⟩ = (ω ⟨w, hWD w.2⟩)⁻¹ := by
      rw [← hyω, ← hconj, h]
    have hw2 : ω (⟨w, hWD w.2⟩ * ⟨w, hWD w.2⟩) = 1 := by
      rw [map_mul]
      nth_rewrite 2 [hww]
      exact mul_inv_cancel _
    have hw2' := hωW _ (W.mul_mem w.2 w.2) hw2
    have hwsq : w ^ 2 = 1 := Subtype.ext (by rw [sq]; exact hw2')
    have h1 := orderOf_dvd_of_pow_eq_one hwsq
    have h2 := orderOf_dvd_natCard w
    have h3 : orderOf w ∣ Nat.gcd 2 (Nat.card W) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hWodd), Nat.dvd_one,
      orderOf_eq_one_iff] at h3
    exact hw1 h3
  let actM : MulAction M (D →* ℂˣ) :=
    { smul := fun m χ => conjugateLinearCharacter ⟨m, hMN m.2⟩ χ
      one_smul := fun χ => conjugateLinearCharacter_one χ
      mul_smul := fun m m' χ =>
        conjugateLinearCharacter_mul (D := D) ⟨(m : G), hMN m.2⟩ ⟨(m' : G), hMN m'.2⟩ χ }
  let actK : MulAction K (D →* ℂˣ) :=
    { smul := fun k χ => conjugateLinearCharacter ⟨k, hMN (hKM k.2)⟩ χ
      one_smul := fun χ => conjugateLinearCharacter_one χ
      mul_smul := fun k k' χ =>
        conjugateLinearCharacter_mul (D := D) ⟨(k : G), hMN (hKM k.2)⟩
          ⟨(k' : G), hMN (hKM k'.2)⟩ χ }
  have horbM : ∀ χ : D →* ℂˣ, MulAction.orbit M χ = conjugateLinearCharacters M χ := by
    intro χ
    ext χ'
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨⟨m, hMN m.2⟩, m.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have horbK : ∀ χ : D →* ℂˣ, MulAction.orbit K χ = conjugateLinearCharacters K χ := by
    intro χ
    ext χ'
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨k, hMN (hKM k.2)⟩, k.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, rfl⟩
  have hstabM : ∀ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A → ω x = 1) →
      (∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) →
      MulAction.stabilizer M ω = D.subgroupOf M := by
    intro ω hω1 hωW
    ext m
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    exact hstabω ω hω1 hωW ⟨m, hMN m.2⟩ m.2
  have hstabK : ∀ ω : D →* ℂˣ, (∀ x : D, (x : G) ∈ V ⊔ A → ω x = 1) →
      (∀ x : D, (x : G) ∈ W → ω x = 1 → (x : G) = 1) →
      ∀ χ ∈ conjugateLinearCharacters M ω, MulAction.stabilizer K χ = D.subgroupOf K := by
    intro ω hω1 hωW χ hχ
    obtain ⟨n₀, hn₀M, rfl⟩ := hχ
    ext k
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    change conjugateLinearCharacter (D := D) ⟨(k : G), hMN (hKM k.2)⟩
        (conjugateLinearCharacter n₀ ω) =
      conjugateLinearCharacter n₀ ω ↔ (k : G) ∈ D
    have key : conjugateLinearCharacter (D := D) ⟨(k : G), hMN (hKM k.2)⟩
          (conjugateLinearCharacter n₀ ω) =
        conjugateLinearCharacter n₀ ω ↔
        conjugateLinearCharacter (n₀⁻¹ * ⟨(k : G), hMN (hKM k.2)⟩ * n₀) ω = ω := by
      rw [mul_assoc, conjugateLinearCharacter_mul, conjugateLinearCharacter_mul]
      constructor
      · intro h
        rw [h, conjugateLinearCharacter_inv_cancel]
      · intro h
        apply conjugateLinearCharacter_injective n₀⁻¹
        rw [h, conjugateLinearCharacter_inv_cancel]
    rw [key, hstabω ω hω1 hωW _ (by
      change (n₀ : G)⁻¹ * k * n₀ ∈ M
      exact M.mul_mem (M.mul_mem (M.inv_mem hn₀M) (hKM k.2)) hn₀M)]
    change (n₀ : G)⁻¹ * k * n₀ ∈ D ↔ (k : G) ∈ D
    have hn := Subgroup.mem_normalizer_iff.mp (n₀⁻¹).2 (k : G)
    simp only [Subgroup.coe_inv, inv_inv] at hn
    exact hn.symm
  refine ⟨hNMA, hMN, hexists, fun ω hω1 hωW => ⟨hker ω hω1 hωW, hstabω ω hω1 hωW, ?_, ?_, ?_⟩,
    hMK, hKD⟩
  · rw [← horbM, ← MulAction.index_stabilizer, hstabM ω hω1 hωW]
    exact hMD
  · intro χ hχ
    rw [← horbK, ← MulAction.index_stabilizer, hstabK ω hω1 hωW χ hχ]
    exact hKD
  · have hOcard : (conjugateLinearCharacters M ω).ncard = 6 := by
      rw [← horbM, ← MulAction.index_stabilizer, hstabM ω hω1 hωW]
      exact hMD
    have hOfin : (conjugateLinearCharacters M ω).Finite := Set.finite_of_ncard_ne_zero (by omega)
    have hsub : ∀ χ ∈ conjugateLinearCharacters M ω,
        conjugateLinearCharacters K χ ⊆ conjugateLinearCharacters M ω := by
      rintro χ ⟨n₀, hn₀, rfl⟩ χ' ⟨k, hk, rfl⟩
      exact ⟨k * n₀, M.mul_mem (hKM hk) hn₀, (conjugateLinearCharacter_mul k n₀ ω).symm⟩
    have hKcard : ∀ χ ∈ conjugateLinearCharacters M ω,
        (conjugateLinearCharacters K χ).ncard = 2 := by
      intro χ hχ
      rw [← horbK, ← MulAction.index_stabilizer, hstabK ω hω1 hωW χ hχ]
      exact hKD
    have hiff : ∀ χ χ' : D →* ℂˣ, conjugateLinearCharacters K χ = conjugateLinearCharacters K χ' ↔
        χ ∈ conjugateLinearCharacters K χ' := by
      intro χ χ'
      rw [← horbK, ← horbK]
      exact MulAction.orbit_eq_iff
    have hcount := Finset.card_eq_sum_card_image (conjugateLinearCharacters K) hOfin.toFinset
    have hfib : ∀ P ∈ hOfin.toFinset.image (conjugateLinearCharacters K),
        (hOfin.toFinset.filter fun χ => conjugateLinearCharacters K χ = P).card = 2 := by
      intro P hP
      obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.mp hP
      rw [Set.Finite.mem_toFinset] at hχ₀
      have hfin₀ : (conjugateLinearCharacters K χ₀).Finite := hOfin.subset (hsub χ₀ hχ₀)
      have hfilter : hOfin.toFinset.filter
          (fun χ => conjugateLinearCharacters K χ = conjugateLinearCharacters K χ₀) =
            hfin₀.toFinset := by
        ext χ
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
        rw [hiff]
        exact ⟨fun h => h.2, fun h => ⟨hsub χ₀ hχ₀ h, h⟩⟩
      rw [hfilter, ← Set.ncard_eq_toFinset_card _ hfin₀]
      exact hKcard χ₀ hχ₀
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
      ← Set.ncard_eq_toFinset_card _ hOfin, hOcard] at hcount
    have himage : (conjugateLinearCharacters M ω).image (conjugateLinearCharacters K) =
        ↑(hOfin.toFinset.image (conjugateLinearCharacters K)) := by
      rw [Finset.coe_image, Set.Finite.coe_toFinset]
    rw [himage, Set.ncard_coe_finset]
    omega

end CFSG.Semidihedral.Principal

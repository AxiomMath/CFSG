module

public import CFSG.LocalAnalysis.EvenBN.U5.Prelim
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.SL2Modules
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.NaturalModule CFSG.LocalAnalysis.ComponentInitial.EvenLinearTwoModule
open CFSG.ABGLocalTools (IsSylowOf)
open scoped IsMulCommutative

variable {G : Type*} [Group G] {k : Type*} [Field k]

namespace Prelim

theorem centralizer_sup_eq (P P' : Subgroup G) :
    centralizer ((P ⊔ P' : Subgroup G) : Set G) =
      centralizer (P : Set G) ⊓ centralizer (P' : Set G) := by
  refine le_antisymm (le_inf (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
    (centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right))) fun c hc => ?_
  have hle : P ⊔ P' ≤ centralizer ({c} : Set G) :=
    sup_le (fun p hp => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc.1 p hp))
      (fun p hp => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc.2 p hp))
  exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hle hx)

theorem inf_centralizer_map_conj {V P : Subgroup G} {x : G} (hx : x ∈ normalizer (V : Set G)) :
    V ⊓ centralizer ((P.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) =
      (V ⊓ centralizer (P : Set G)).map (MulAut.conj x).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨hzV, hz⟩
    refine ⟨x⁻¹ * z * x, ⟨conj_mem_of_mem_normalizer hx hzV, mem_centralizer_iff.mpr
      fun p hp => ?_⟩, by simp [MulAut.conj_apply]; group⟩
    have h1 := mem_centralizer_iff.mp hz (x * p * x⁻¹) ⟨p, hp, rfl⟩
    calc p * (x⁻¹ * z * x) = x⁻¹ * ((x * p * x⁻¹) * z) * x := by group
      _ = x⁻¹ * (z * (x * p * x⁻¹)) * x := by rw [h1]
      _ = x⁻¹ * z * x * p := by group
  · rintro ⟨w, ⟨hwV, hw⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.mp hx w).mp hwV, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    have h1 := mem_centralizer_iff.mp hw p hp
    change x * p * x⁻¹ * (x * w * x⁻¹) = x * w * x⁻¹ * (x * p * x⁻¹)
    calc x * p * x⁻¹ * (x * w * x⁻¹) = x * (p * w) * x⁻¹ := by group
      _ = x * (w * p) * x⁻¹ := by rw [h1]
      _ = x * w * x⁻¹ * (x * p * x⁻¹) := by group

theorem card_map_conj (H : Subgroup G) (x : G) :
    Nat.card (H.map (MulAut.conj x).toMonoidHom) = Nat.card H :=
  card_map_of_injective (MulAut.conj x).injective

theorem map_conj_self {X : Subgroup G} {x : G} (hx : x ∈ X) :
    X.map (MulAut.conj x).toMonoidHom = X := by
  ext z
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact X.mul_mem (X.mul_mem hx hw) (X.inv_mem hx)
  · intro hz
    exact ⟨x⁻¹ * z * x, X.mul_mem (X.mul_mem (X.inv_mem hx) hz) hx, by group⟩

theorem map_conj_map_conj (P : Subgroup G) (x y : G) :
    (P.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      P.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem map_conj_eq_of_le_centralizer {P : Subgroup G} {y : G}
    (hy : y ∈ centralizer (P : Set G)) : P.map (MulAut.conj y).toMonoidHom = P := by
  ext z
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← mem_centralizer_iff.mp hy w hw, mul_inv_cancel_right]
    exact hw
  · intro hz
    exact ⟨z, hz, by rw [← mem_centralizer_iff.mp hy z hz, mul_inv_cancel_right]⟩

theorem le_normalizer_inf_centralizer {V P Y : Subgroup G} (hYV : Y ≤ normalizer (V : Set G))
    (hYP : Y ≤ centralizer (P : Set G)) :
    Y ≤ normalizer ((V ⊓ centralizer (P : Set G) : Subgroup G) : Set G) := fun _ hy =>
  inf_normalizer_le_normalizer_inf ⟨hYV hy,
    normalizer_le_normalizer_centralizer P (centralizer_le_normalizer _ (hYP hy))⟩

section Action

variable {X : Subgroup G}

@[expose] def slAction (φ : X ≃* SpecialLinearGroup (Fin 2) k) {N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) : SpecialLinearGroup (Fin 2) k →* MulAut N :=
  (SL2MinimalFaithful.conjAction hXN).comp φ.symm.toMonoidHom

theorem slAction_apply (φ : X ≃* SpecialLinearGroup (Fin 2) k) {N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) (g : SpecialLinearGroup (Fin 2) k) (n : N) :
    (slAction φ hXN g n : G) = (φ.symm g : G) * n * (φ.symm g : G)⁻¹ :=
  rfl

theorem le_centralizer_of_slAction_eq_one (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    {N : Subgroup G} (hXN : X ≤ normalizer (N : Set G)) (h : slAction φ hXN = 1) :
    X ≤ centralizer (N : Set G) := by
  intro x hx
  rw [mem_centralizer_iff]
  intro n hn
  have h1 := congrArg (fun f : SpecialLinearGroup (Fin 2) k →* MulAut N =>
    ((f (φ ⟨x, hx⟩) ⟨n, hn⟩ : N) : G)) h
  simp only [slAction_apply, MulEquiv.symm_apply_apply, MonoidHom.one_apply,
    MulAut.one_apply] at h1
  calc n * x = x * n * x⁻¹ * x := by rw [h1]
    _ = x * n := by group

variable [Finite G] [Finite k] {m : ℕ}

theorem le_centralizer_of_card_lt (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (φ : X ≃* SpecialLinearGroup (Fin 2) k) {A : Subgroup G} (hXA : X ≤ normalizer (A : Set G))
    (hA : IsPGroup 2 A) (hcard : Nat.card A < 2 ^ (2 * m)) : X ≤ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hA
  rw [hd] at hcard
  have hlt : d < 2 * m := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hcard
  refine le_centralizer_of_slAction_eq_one φ hXA ?_
  by_contra hne
  have := U4.two_mul_le_of_ne_one hk hm hm3 hd (slAction φ hXA) hne
  omega

theorem le_centralizer_of_card_lt_mul (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (φ : X ≃* SpecialLinearGroup (Fin 2) k) {A B : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA : IsPGroup 2 A) (hBA : B ≤ A)
    (hXA : X ≤ normalizer (A : Set G)) (hBX : B ≤ centralizer (X : Set G))
    (hcard : Nat.card A < 2 ^ (2 * m) * Nat.card B) : X ≤ centralizer (A : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (hAc a a.2 b b.2)⟩⟩
  set ρ := slAction φ hXA
  set B' := B.subgroupOf A
  have : B'.Normal := normal_of_isMulCommutative B'
  have hfix : ∀ g, ∀ b ∈ B', ρ g b = b := by
    intro g b hb
    apply Subtype.ext
    rw [slAction_apply]
    have := mem_centralizer_iff.mp (hBX (mem_subgroupOf.mp hb)) _ (φ.symm g).2
    rw [this, mul_inv_cancel_right]
  have hmap : ∀ g, B'.map (ρ g : A →* A) = B' := by
    intro g
    ext b
    constructor
    · rintro ⟨b', hb', rfl⟩
      change ρ g b' ∈ B'
      rw [hfix g b' hb']
      exact hb'
    · intro hb
      exact ⟨b, hb, hfix g b hb⟩
  set ρbar := SL2MinimalFaithful.quotientAction ρ B' hmap
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (hA.to_quotient B')
  have hcardB : Nat.card B' = Nat.card B := Nat.card_congr (subgroupOfEquivOfLe hBA).toEquiv
  have hlt : e < 2 * m := by
    have h1 := card_eq_card_quotient_mul_card_subgroup B'
    rw [he, hcardB] at h1
    rw [h1] at hcard
    have hpos : 0 < Nat.card B := Nat.card_pos
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (Nat.lt_of_mul_lt_mul_right hcard)
  have hbar : ρbar = 1 := by
    by_contra hne
    have := U4.two_mul_le_of_ne_one hk hm hm3 he ρbar hne
    omega
  have hδ : ∀ g (v : A), v⁻¹ * ρ g v ∈ actionFixed ρ ⊤ := by
    intro g v h _
    have h1 : ρbar g (v : A ⧸ B') = (v : A ⧸ B') := by rw [hbar]; rfl
    rw [SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq] at h1
    have h2 : v⁻¹ * ρ g v ∈ B' := by
      have := B'.inv_mem h1
      rwa [_root_.mul_inv_rev, inv_inv] at this
    exact hfix h _ h2
  exact le_centralizer_of_slAction_eq_one φ hXA
    (U4.eq_one_of_forall_inv_mul_apply_mem (U4.exists_finset_card_four hk hm) ρ hδ)

end Action

section Sylow

variable {X : Subgroup G}

@[expose] def ofSL (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    (S : Subgroup (SpecialLinearGroup (Fin 2) k)) : Subgroup G :=
  (S.map φ.symm.toMonoidHom).map X.subtype

theorem ofSL_le (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    (S : Subgroup (SpecialLinearGroup (Fin 2) k)) : ofSL φ S ≤ X :=
  map_subtype_le _

theorem coe_mem_ofSL_iff (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    {S : Subgroup (SpecialLinearGroup (Fin 2) k)} (x : X) : (x : G) ∈ ofSL φ S ↔ φ x ∈ S := by
  constructor
  · rintro ⟨y, ⟨s, hs, rfl⟩, hsx⟩
    have hx : (φ.symm s : X) = x := Subtype.ext hsx
    rw [← hx]
    simpa using hs
  · intro hx
    exact ⟨φ.symm (φ x), ⟨φ x, hx, rfl⟩, by simp⟩

theorem ofSL_top (φ : X ≃* SpecialLinearGroup (Fin 2) k) : ofSL φ ⊤ = X := by
  rw [ofSL, map_top_of_surjective _ φ.symm.surjective, ← MonoidHom.range_eq_map, range_subtype]

theorem ofSL_sup (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    (S T : Subgroup (SpecialLinearGroup (Fin 2) k)) : ofSL φ (S ⊔ T) = ofSL φ S ⊔ ofSL φ T := by
  simp only [ofSL, Subgroup.map_sup]

theorem card_ofSL (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    (S : Subgroup (SpecialLinearGroup (Fin 2) k)) : Nat.card (ofSL φ S) = Nat.card S := by
  rw [ofSL, card_map_of_injective X.subtype_injective,
    card_map_of_injective (f := φ.symm.toMonoidHom) φ.symm.injective]

theorem ofSL_map_conj (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    (S : Subgroup (SpecialLinearGroup (Fin 2) k)) (y : X) :
    ofSL φ (S.map (MulAut.conj (φ y)).toMonoidHom) =
      (ofSL φ S).map (MulAut.conj (y : G)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
    refine ⟨((φ.symm s : X) : G), ⟨_, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, subtype_apply, map_mul, map_inv,
      MulEquiv.symm_apply_apply]
  · rintro ⟨_, ⟨_, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
    refine ⟨φ.symm (φ y * s * (φ y)⁻¹), ⟨φ y * s * (φ y)⁻¹, ⟨s, hs, rfl⟩, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, subtype_apply, map_mul, map_inv,
      MulEquiv.symm_apply_apply]

theorem map_subgroupOf_ofSL (φ : X ≃* SpecialLinearGroup (Fin 2) k)
    (S : Subgroup (SpecialLinearGroup (Fin 2) k)) :
    ((ofSL φ S).subgroupOf X).map φ.toMonoidHom = S := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (coe_mem_ofSL_iff φ x).mp (mem_subgroupOf.mp hx)
  · intro hg
    exact ⟨φ.symm g, mem_subgroupOf.mpr ((coe_mem_ofSL_iff φ _).mpr (by simpa using hg)),
      by simp⟩

variable [Finite G]

theorem isSylowOf_ofSL_upperUnipotent [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    (φ : X ≃* SpecialLinearGroup (Fin 2) k) : IsSylowOf 2 (ofSL φ (upperUnipotent k)) X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (ofSL φ (upperUnipotent k)) = 2 ^ m := by
    rw [card_ofSL, card_upperUnipotent, hk]
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨ofSL_le φ _, IsPGroup.of_card hcard, ?_⟩
  have h1 := relIndex_mul_card (ofSL φ (upperUnipotent k)) X
  rw [inf_eq_left.mpr (ofSL_le φ _), hcard, Nat.card_congr φ.toEquiv,
    SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk] at h1
  have h2 : (ofSL φ (upperUnipotent k)).relIndex X = (2 ^ m) ^ 2 - 1 := by
    have hpos : 0 < 2 ^ m := by positivity
    rw [mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  rw [h2]
  have hodd : Odd ((2 ^ m) ^ 2 - 1) := by
    have h4 : 4 ≤ (2 ^ m) ^ 2 := by
      calc 4 = (2 ^ 1) ^ 2 := by norm_num
        _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) hm) 2
    have heven : Even ((2 ^ m) ^ 2) := by
      rw [← pow_mul]
      exact (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨r, hr⟩ := heven
    exact ⟨r - 1, by omega⟩
  exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem exists_conj_of_isSylowOf {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (hP : IsSylowOf p P K) (hP' : IsSylowOf p P' K) :
    ∃ x ∈ K, P' = P.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨Q, rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hP'
  obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq K Q Q'
  refine ⟨x, x.2, ?_⟩
  ext z
  rw [Sylow.coe_subgroup_smul]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_smul_pointwise_iff_exists] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    exact ⟨s, ⟨s, hs, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨x * s * x⁻¹, ?_, by simp [MulAut.conj_apply]⟩
    rw [SetLike.mem_coe, mem_smul_pointwise_iff_exists]
    exact ⟨s, hs, by simp [MulAut.smul_def, MulAut.conj_apply]⟩

theorem mul_upperElt_eq_of_eq_zero {g : SpecialLinearGroup (Fin 2) k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) (t : k) :
    g * upperElt k t =
      upperElt k ((g : Matrix (Fin 2) (Fin 2) k) 0 0 * t * (g : Matrix (Fin 2) (Fin 2) k) 0 0) *
        g := by
  have hdet := g.2
  rw [Matrix.det_fin_two, hg, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_upperElt, Matrix.mul_apply, Fin.sum_univ_two, hg]
  linear_combination (-((g : Matrix (Fin 2) (Fin 2) k) 0 0 * t)) * hdet

theorem map_conj_upperUnipotent_of_eq_zero [Finite k] {g : SpecialLinearGroup (Fin 2) k}
    (hg : (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    (upperUnipotent k).map (MulAut.conj g).toMonoidHom = upperUnipotent k := by
  have hle : (upperUnipotent k).map (MulAut.conj g).toMonoidHom ≤ upperUnipotent k := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).1 hu
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_upperElt_eq_of_eq_zero hg,
      mul_inv_cancel_right]
    exact (mem_upperUnipotent_iff k).2 ⟨_, rfl⟩
  exact eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge

theorem sup_eq_of_isSylowOf_ne [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    (φ : X ≃* SpecialLinearGroup (Fin 2) k) {P P' : Subgroup G} (hP : IsSylowOf 2 P X)
    (hP' : IsSylowOf 2 P' X) (hne : P ≠ P') : P ⊔ P' = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := ofSL φ (upperUnipotent k)
  have hR := isSylowOf_ofSL_upperUnipotent hk hm φ
  obtain ⟨x, hx, rfl⟩ := exists_conj_of_isSylowOf hR hP
  obtain ⟨x', hx', rfl⟩ := exists_conj_of_isSylowOf hR hP'
  set y : X := ⟨x⁻¹ * x', X.mul_mem (X.inv_mem hx) hx'⟩
  have hxy : x * (y : G) = x' := by simp [y]
  have hR' : R.map (MulAut.conj x').toMonoidHom =
      (R.map (MulAut.conj (y : G)).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [map_conj_map_conj, hxy]
  have hRy : R.map (MulAut.conj (y : G)).toMonoidHom =
      ofSL φ ((upperUnipotent k).map (MulAut.conj (φ y)).toMonoidHom) :=
    (ofSL_map_conj φ _ y).symm
  by_cases h10 : ((φ y : SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0
  · exfalso
    apply hne
    rw [hR', hRy, map_conj_upperUnipotent_of_eq_zero h10]
  · rw [hR', hRy, ← Subgroup.map_sup, ← ofSL_sup, upperUnipotent_sup_map_conj_eq_top h10,
      ofSL_top]
    exact map_conj_self hx

theorem card_of_isSylowOf [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    (φ : X ≃* SpecialLinearGroup (Fin 2) k) {P : Subgroup G} (hP : IsSylowOf 2 P X) :
    Nat.card P = 2 ^ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, -, rfl⟩ := exists_conj_of_isSylowOf (isSylowOf_ofSL_upperUnipotent hk hm φ) hP
  rw [card_map_conj, card_ofSL, card_upperUnipotent, hk]

theorem inf_inf_centralizer_eq [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    (φ : X ≃* SpecialLinearGroup (Fin 2) k) (V : Subgroup G) {P P' : Subgroup G}
    (hP : IsSylowOf 2 P X) (hP' : IsSylowOf 2 P' X) (hne : P ≠ P') :
    (V ⊓ centralizer (P : Set G)) ⊓ (V ⊓ centralizer (P' : Set G)) =
      V ⊓ centralizer (X : Set G) := by
  rw [← sup_eq_of_isSylowOf_ne hk hm φ hP hP' hne, centralizer_sup_eq]
  ext z
  simp only [mem_inf]
  tauto

end Sylow

section Natural

variable [Finite G] [Finite k] {m : ℕ} {X : Subgroup G}

open scoped commutatorElement in
theorem exists_isNaturalModule (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    (φ : X ≃* SpecialLinearGroup (Fin 2) k) {N : Subgroup G} (hN : IsElementaryAbelian 2 N)
    (hXN : X ≤ normalizer (N : Set G)) (hcard : Nat.card N = 2 ^ (2 * m))
    (hfix : N ⊓ centralizer (X : Set G) = ⊥) {S : Subgroup G} (hS : IsSylowOf 2 S X)
    (hNS : Nat.card (N ⊓ centralizer (S : Set G) : Subgroup G) = 2 ^ m) :
    ∃ θ : (Fin 2 → k) → G, IsNaturalModule φ θ ∧ Set.range θ = (N : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := U4.charP_two_of_card hk
  have : IsElementaryAbelian 2 N := hN
  set R := ofSL φ (upperUnipotent k) with hRdef
  obtain ⟨x, hx, rfl⟩ := exists_conj_of_isSylowOf (isSylowOf_ofSL_upperUnipotent hk hm φ) hS
  have hNR : Nat.card (N ⊓ centralizer (R : Set G) : Subgroup G) = 2 ^ m := by
    rw [← hNS, inf_centralizer_map_conj (hXN hx), card_map_conj]
  set ρ := slAction φ hXN
  have hD : actionFixed ρ ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvX : (v : G) ∈ N ⊓ centralizer (X : Set G) := by
      refine ⟨v.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h1 := congrArg Subtype.val (hv (φ ⟨y, hy⟩) (mem_top _))
      rw [slAction_apply, MulEquiv.symm_apply_apply] at h1
      calc y * (v : G) = y * v * y⁻¹ * y := by group
        _ = v * y := by rw [h1]
    rw [hfix, mem_bot] at hvX
    exact (mem_bot).mpr (Subtype.ext hvX)
  have hfixB : ∀ v : N, v ∈ actionFixed ρ (upperUnipotent k) ↔
      (v : G) ∈ centralizer (R : Set G) := by
    intro v
    constructor
    · intro hv
      refine mem_centralizer_iff.mpr ?_
      rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have h1 := congrArg Subtype.val (hv b hb)
      rw [slAction_apply] at h1
      change (φ.symm b : G) * v = v * (φ.symm b : G)
      calc (φ.symm b : G) * v = (φ.symm b : G) * v * (φ.symm b : G)⁻¹ * (φ.symm b : G) := by
            group
        _ = v * (φ.symm b : G) := by rw [h1]
    · intro hv b hb
      apply Subtype.ext
      have hbR : ((φ.symm b : X) : G) ∈ R := ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have h1 := mem_centralizer_iff.mp hv _ hbR
      rw [slAction_apply, h1, mul_inv_cancel_right]
  have hcardB : Nat.card (actionFixed ρ (upperUnipotent k)) = 2 ^ m := by
    rw [← hNR]
    have hmap : (actionFixed ρ (upperUnipotent k)).map N.subtype =
        N ⊓ centralizer (R : Set G) := by
      ext z
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.2, (hfixB v).mp hv⟩
      · rintro ⟨hzN, hzR⟩
        exact ⟨⟨z, hzN⟩, (hfixB ⟨z, hzN⟩).mpr hzR, rfl⟩
    rw [← hmap, card_map_of_injective N.subtype_injective]
  have hc := isComplement'_map_weylElt hD (by rw [hcardB, hcard, ← pow_add, two_mul])
  have hquad : ∀ n ∈ N, ∀ a ∈ R, ∀ a' ∈ R, Commute a' ⁅a, n⁆ := by
    intro n hn a ha a' ha'
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := (mem_upperUnipotent_iff k).1 hb
    set v : N := ⟨n, hn⟩
    set w : N := ρ (upperElt k t) v * v⁻¹ with hw
    have hwG : (w : G) = ⁅((φ.symm (upperElt k t) : X) : G), n⁆ := by
      rw [hw, coe_mul, slAction_apply, coe_inv, commutatorElement_def]
    have hwfix : w ∈ actionFixed ρ (upperUnipotent k) := by
      by_cases ht : t = 0
      · have : w = 1 := by
          rw [hw, ht, upperElt_zero, map_one, MulAut.one_apply, mul_inv_cancel]
        rw [this]
        exact one_mem _
      refine mem_of_upperElt_apply_eq hD hc ht ?_
      have hb2 : ρ (upperElt k t) (ρ (upperElt k t) v) = v := by
        rw [← MulAut.mul_apply, ← map_mul, upperElt_mul_self, map_one, MulAut.one_apply]
      rw [hw, map_mul, map_inv, hb2]
      have hinv : ∀ u : N, u⁻¹ = u := fun u =>
        Subtype.ext (inv_eq_self_of_mem hN u.2)
      rw [hinv, hinv, mul_comm]
    change Commute a' ⁅((φ.symm (upperElt k t) : X) : G), n⁆
    rw [← hwG]
    exact (mem_centralizer_iff.mp ((hfixB w).mp hwfix) a' ha')
  obtain ⟨w₀, hw₀, hw₀1⟩ : ∃ w₀ ∈ N ⊓ centralizer (R : Set G), w₀ ≠ 1 := by
    have h1 : 1 < Nat.card (N ⊓ centralizer (R : Set G) : Subgroup G) := by
      rw [hNR]
      exact Nat.one_lt_two_pow (by omega)
    have : Nontrivial (N ⊓ centralizer (R : Set G) : Subgroup G) :=
      Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨⟨w, hw⟩, hw1⟩ := exists_ne (1 : (N ⊓ centralizer (R : Set G) : Subgroup G))
    exact ⟨w, hw, fun h => hw1 (Subtype.ext h)⟩
  obtain ⟨θ, hθ, hrange, -⟩ := exists_natural_of_quadratic_conj φ (A := R)
    (map_subgroupOf_ofSL φ _) (fun n hn n' hn' => mul_comm_of_mem hN hn hn')
    (fun y hy n hn => (mem_normalizer_iff.mp (hXN hy) n).mp hn)
    (fun n hn hcomm => by
      have hnX : n ∈ N ⊓ centralizer (X : Set G) :=
        ⟨hn, mem_centralizer_iff.mpr fun y hy => (hcomm y hy).eq⟩
      rwa [hfix, mem_bot] at hnX)
    hquad hw₀.1 (fun a ha => mem_centralizer_iff.mp hw₀.2 a ha) hw₀1
  refine ⟨θ, hθ, ?_⟩
  have hsub : Set.range θ ⊆ (N : Set G) := by
    rw [hrange]
    refine (closure_le N).mpr ?_
    rintro _ ⟨y, rfl⟩
    exact (mem_normalizer_iff.mp (hXN y.2) w₀).mp hw₀.1
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hθ.card_range, hk, ← pow_mul, mul_comm]
  exact (congrArg Nat.card (SetLike.coe_sort_coe N)).trans hcard |>.le

end Natural

theorem card_inf_centralizer_eq_mul [Finite G] {V A A' S : Subgroup G}
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hsup : A ⊔ A' = V) (hinf : A ⊓ A' = ⊥)
    (hSA : S ≤ normalizer (A : Set G)) (hSA' : S ≤ normalizer (A' : Set G)) :
    Nat.card (V ⊓ centralizer (S : Set G) : Subgroup G) =
      Nat.card (A ⊓ centralizer (S : Set G) : Subgroup G) *
        Nat.card (A' ⊓ centralizer (S : Set G) : Subgroup G) := by
  have hAV : A ≤ V := hsup ▸ le_sup_left
  have hA'V : A' ≤ V := hsup ▸ le_sup_right
  have hcAA' : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := fun a ha b hb => hVc a (hAV ha) b (hA'V hb)
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A A' hcAA').2
  have hZ : V ⊓ centralizer (S : Set G) =
      (A ⊓ centralizer (S : Set G)) ⊔ (A' ⊓ centralizer (S : Set G)) := by
    refine le_antisymm (fun z hz => ?_)
      (sup_le (inf_le_inf_right _ hAV) (inf_le_inf_right _ hA'V))
    have hz' : z ∈ ((A ⊔ A' : Subgroup G) : Set G) := hsup.symm ▸ hz.1
    rw [hset] at hz'
    obtain ⟨a, ha, a', ha', rfl⟩ := hz'
    have haS : a ∈ centralizer (S : Set G) := by
      refine mem_centralizer_iff.mpr fun s hs => ?_
      have hzs := mem_centralizer_iff.mp hz.2 s hs
      have h1 : s * a * s⁻¹ ∈ A := (mem_normalizer_iff.mp (hSA hs) a).mp ha
      have h2 : s * a' * s⁻¹ ∈ A' := (mem_normalizer_iff.mp (hSA' hs) a').mp ha'
      have h3 : (s * a * s⁻¹) * (s * a' * s⁻¹) = a * a' := by
        calc (s * a * s⁻¹) * (s * a' * s⁻¹) = s * (a * a') * s⁻¹ := by group
          _ = a * a' := by rw [hzs, mul_inv_cancel_right]
      have h4 : a⁻¹ * (s * a * s⁻¹) = a' * (s * a' * s⁻¹)⁻¹ := by
        have hc := hVc _ (hAV h1) _ (hA'V h2)
        calc a⁻¹ * (s * a * s⁻¹) = a⁻¹ * ((s * a * s⁻¹) * (s * a' * s⁻¹)) *
              (s * a' * s⁻¹)⁻¹ := by group
          _ = a⁻¹ * (a * a') * (s * a' * s⁻¹)⁻¹ := by rw [h3]
          _ = a' * (s * a' * s⁻¹)⁻¹ := by group
      have h5 : a⁻¹ * (s * a * s⁻¹) ∈ A ⊓ A' :=
        ⟨A.mul_mem (A.inv_mem ha) h1, h4 ▸ A'.mul_mem ha' (A'.inv_mem h2)⟩
      rw [hinf, mem_bot] at h5
      have h6 : s * a * s⁻¹ = a := (inv_mul_eq_one.mp h5).symm
      calc s * a = s * a * s⁻¹ * s := by group
        _ = a * s := by rw [h6]
    have ha'S : a' ∈ centralizer (S : Set G) := by
      have := mul_mem (inv_mem haS) hz.2
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mem_sup_left ⟨ha, haS⟩) (mem_sup_right ⟨ha', ha'S⟩)
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (A ⊓ centralizer (S : Set G))
    (A' ⊓ centralizer (S : Set G)) fun a ha b hb => hcAA' a ha.1 b hb.1).1
  have hbot : (A ⊓ centralizer (S : Set G)) ⊓ (A' ⊓ centralizer (S : Set G)) = ⊥ :=
    eq_bot_iff.mpr fun z hz => hinf ▸ (⟨hz.1.1, hz.2.1⟩ : z ∈ A ⊓ A')
  rw [hbot, card_bot, mul_one] at hc
  rw [hZ, hc]

structure PairSetting (m : ℕ) (V X Y : Subgroup G) : Prop where
  elem : IsElementaryAbelian 2 V
  card : Nat.card V = 2 ^ (4 * m)
  normX : X ≤ normalizer (V : Set G)
  normY : Y ≤ normalizer (V : Set G)
  comm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x
  fixed : V ⊓ centralizer (X : Set G) ⊓ centralizer (Y : Set G) = ⊥

namespace PairSetting

variable {m : ℕ} {V X Y : Subgroup G} (h : PairSetting m V X Y)
include h

theorem symm : PairSetting m V Y X where
  elem := h.elem
  card := h.card
  normX := h.normY
  normY := h.normX
  comm := fun y hy x hx => (h.comm x hx y hy).symm
  fixed := by rw [inf_right_comm]; exact h.fixed

theorem le_centralizer : Y ≤ centralizer (X : Set G) := fun y hy =>
  mem_centralizer_iff.mpr fun x hx => h.comm x hx y hy

theorem isPGroup : IsPGroup 2 V := @IsElementaryAbelian.isPGroup 2 V _ h.elem

theorem isPGroup_of_le {A : Subgroup G} (hA : A ≤ V) : IsPGroup 2 A := h.isPGroup.to_le hA

theorem comm_of_le {A : Subgroup G} (hA : A ≤ V) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a :=
  fun _ ha _ hb => mul_comm_of_mem h.elem (hA ha) (hA hb)

theorem elem_of_le {A : Subgroup G} (hA : A ≤ V) : IsElementaryAbelian 2 A where
  toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (h.comm_of_le hA a a.2 b b.2)⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => Subtype.ext (by
    simpa using @CFSG.elemPow_eq_one_of_isElementaryAbelian 2 G _ V h.elem a (hA a.2))

theorem le_normalizer_right {P : Subgroup G} (hP : P ≤ X) :
    Y ≤ normalizer ((V ⊓ centralizer (P : Set G) : Subgroup G) : Set G) :=
  le_normalizer_inf_centralizer h.normY (h.le_centralizer.trans (centralizer_le hP))

theorem ne_bot (hm : 1 ≤ m) : V ≠ ⊥ := by
  intro hV
  have h1 := h.card
  rw [hV, card_bot] at h1
  have : 2 ≤ 2 ^ (4 * m) := Nat.le_self_pow (by omega) 2
  omega

variable [Finite G]

theorem inf_centralizer_ne_bot (hm : 1 ≤ m) {P : Subgroup G} (hPX : P ≤ X)
    (hP : IsPGroup 2 P) : V ⊓ centralizer (P : Set G) ≠ ⊥ :=
  inf_centralizer_ne_bot_of_pow_mem h.isPGroup (h.ne_bot hm) (hPX.trans h.normX) fun y hy => by
    obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
    refine ⟨k, ?_⟩
    have : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [this]
    exact one_mem _

variable [Finite k]

theorem card_inf_inf_centralizer_eq {P P' : Subgroup G} (hP : IsSylowOf 2 P X)
    (hP' : IsSylowOf 2 P' X) {S : Subgroup G} (hS : S ≤ Y) :
    Nat.card (V ⊓ centralizer (P' : Set G) ⊓ centralizer (S : Set G) : Subgroup G) =
      Nat.card (V ⊓ centralizer (P : Set G) ⊓ centralizer (S : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, rfl⟩ := exists_conj_of_isSylowOf hP hP'
  have hxS : S.map (MulAut.conj x).toMonoidHom = S := map_conj_eq_of_le_centralizer
    (mem_centralizer_iff.mpr fun s hs => (h.comm x hx s (hS hs)).symm)
  rw [inf_assoc, inf_assoc, ← centralizer_sup_eq, ← centralizer_sup_eq, ← hxS, ← Subgroup.map_sup,
    inf_centralizer_map_conj (h.normX hx), card_map_conj, hxS]

theorem card_inf_centralizer_eq {P P' : Subgroup G} (hP : IsSylowOf 2 P X)
    (hP' : IsSylowOf 2 P' X) :
    Nat.card (V ⊓ centralizer (P' : Set G) : Subgroup G) =
      Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, rfl⟩ := exists_conj_of_isSylowOf hP hP'
  rw [inf_centralizer_map_conj (h.normX hx), card_map_conj]

theorem inf_centralizer_eq_bot (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (φX : X ≃* SpecialLinearGroup (Fin 2) k) (φY : Y ≃* SpecialLinearGroup (Fin 2) k)
    {P Q : Subgroup G} (hP : IsSylowOf 2 P X) (hQ : IsSylowOf 2 Q Y)
    (hU : Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ (2 * m))
    (hW : Nat.card (V ⊓ centralizer (Q : Set G) : Subgroup G) = 2 ^ (2 * m)) :
    V ⊓ centralizer (X : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := U4.charP_two_of_card hk
  by_contra hD
  set D := V ⊓ centralizer (X : Set G) with hDdef
  set U := V ⊓ centralizer (P : Set G) with hUdef
  set W := V ⊓ centralizer (Q : Set G) with hWdef
  have hYD : Y ≤ normalizer (D : Set G) := le_normalizer_inf_centralizer h.normY h.le_centralizer
  have hDQ : D ⊓ centralizer (Q : Set G) ≠ ⊥ := inf_centralizer_ne_bot_of_pow_mem
    (h.isPGroup_of_le inf_le_left) hD (hQ.le.trans hYD) fun y hy => by
      obtain ⟨j, hj⟩ := hQ.isPGroup ⟨y, hy⟩
      refine ⟨j, ?_⟩
      rw [show y ^ 2 ^ j = 1 from congrArg Subtype.val hj]
      exact one_mem _
  have hXW : X ≤ normalizer (W : Set G) := h.symm.le_normalizer_right hQ.le
  have hWX1 : 1 < Nat.card (W ⊓ centralizer (X : Set G) : Subgroup G) := by
    have hle : D ⊓ centralizer (Q : Set G) ≤ W ⊓ centralizer (X : Set G) := fun z hz =>
      ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩
    have h1 := (one_lt_card_iff_ne_bot _).mpr hDQ
    exact h1.trans_le (card_le_of_le hle)
  have hWX : X ≤ centralizer (W : Set G) := le_centralizer_of_card_lt_mul hk hm hm3 φX
    (h.comm_of_le inf_le_left) (h.isPGroup_of_le inf_le_left) inf_le_left hXW inf_le_right
    (by rw [hW]; exact lt_mul_of_one_lt_right (by positivity) hWX1)
  have hWD : W ≤ D := fun w hw => ⟨hw.1, mem_centralizer_iff.mpr fun x hx =>
    (mem_centralizer_iff.mp (hWX hx) w hw).symm⟩
  have hDU : D ≤ U := inf_le_inf_left V (centralizer_le hP.le)
  have hWU : W = U := eq_of_le_of_card_ge (hWD.trans hDU) (by rw [hU, hW])
  have hYUn : Y ≤ normalizer (U : Set G) := h.le_normalizer_right hP.le
  have hYU : Y ≤ centralizer (U : Set G) := by
    refine le_centralizer_of_slAction_eq_one φY hYUn ?_
    have hsimple := U4.isSimpleGroup_specialLinearGroup (U4.exists_finset_card_four hk hm)
    rcases hsimple.eq_bot_or_eq_top_of_normal (slAction φY hYUn).ker with hbot | htop
    · exfalso
      have hQ1 : Q ≠ ⊥ := by
        rw [← one_lt_card_iff_ne_bot, card_of_isSylowOf hk (by omega) φY hQ]
        exact Nat.one_lt_two_pow (by omega)
      obtain ⟨⟨q, hq⟩, hq1⟩ := (ne_bot_iff_exists_ne_one).mp hQ1
      have hker : φY ⟨q, hQ.le hq⟩ ∈ (slAction φY hYUn).ker := by
        rw [MonoidHom.mem_ker]
        ext u
        rw [slAction_apply, MulEquiv.symm_apply_apply, MulAut.one_apply]
        have hu : (u : G) ∈ W := hWU.ge u.2
        change q * u * q⁻¹ = u
        rw [mem_centralizer_iff.mp hu.2 q hq, mul_inv_cancel_right]
      rw [hbot, mem_bot] at hker
      have : (⟨q, hQ.le hq⟩ : Y) = 1 := φY.injective (hker.trans (map_one φY).symm)
      have hq' : q = 1 := congrArg Subtype.val this
      exact hq1 (Subtype.ext hq')
    · exact MonoidHom.ker_eq_top_iff.mp htop
  apply h.inf_centralizer_ne_bot (by omega) hP.le hP.isPGroup
  rw [eq_bot_iff, ← h.fixed]
  intro u hu
  exact ⟨hWD (hWU.ge hu), mem_centralizer_iff.mpr fun y hy =>
    (mem_centralizer_iff.mp (hYU hy) u hu).symm⟩

theorem card_eq_of_card_le (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (φX : X ≃* SpecialLinearGroup (Fin 2) k) (φY : Y ≃* SpecialLinearGroup (Fin 2) k)
    {P Q : Subgroup G} (hP : IsSylowOf 2 P X) (hQ : IsSylowOf 2 Q Y)
    (hUW : Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) =
      Nat.card (V ⊓ centralizer (Q : Set G) : Subgroup G))
    (hle : Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) ≤ 2 ^ (2 * m)) :
    Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ (2 * m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm hle (not_lt.mp fun hlt => ?_)
  set U := V ⊓ centralizer (P : Set G)
  set W := V ⊓ centralizer (Q : Set G)
  have hYU : Y ≤ centralizer (U : Set G) := le_centralizer_of_card_lt hk hm hm3 φY
    (h.le_normalizer_right hP.le) (h.isPGroup_of_le inf_le_left) hlt
  have hXW : X ≤ centralizer (W : Set G) := le_centralizer_of_card_lt hk hm hm3 φX
    (h.symm.le_normalizer_right hQ.le) (h.isPGroup_of_le inf_le_left) (hUW ▸ hlt)
  have hUW' : U ≤ W := fun u hu => ⟨hu.1, mem_centralizer_iff.mpr fun q hq =>
    (mem_centralizer_iff.mp (hYU (hQ.le hq)) u hu).symm⟩
  have hUeq : U = W := eq_of_le_of_card_ge hUW' hUW.ge
  apply h.inf_centralizer_ne_bot (by omega) hP.le hP.isPGroup
  rw [eq_bot_iff, ← h.fixed]
  intro u hu
  refine ⟨⟨hu.1, mem_centralizer_iff.mpr fun x hx => ?_⟩, mem_centralizer_iff.mpr fun y hy =>
    (mem_centralizer_iff.mp (hYU hy) u hu).symm⟩
  exact (mem_centralizer_iff.mp (hXW hx) u (hUeq.le hu)).symm

theorem inf_centralizer_ne_bot_of_lt (hk : Nat.card k = 2 ^ m) (hm : 1 ≤ m)
    (φX : X ≃* SpecialLinearGroup (Fin 2) k) {P P' : Subgroup G} (hP : IsSylowOf 2 P X)
    (hP' : IsSylowOf 2 P' X) (hPP : P ≠ P')
    (hU : 2 ^ (2 * m) < Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G)) :
    V ⊓ centralizer (X : Set G) ≠ ⊥ := by
  rw [← inf_inf_centralizer_eq hk hm φX V hP hP' hPP]
  intro hbot
  set U := V ⊓ centralizer (P : Set G)
  set U' := V ⊓ centralizer (P' : Set G)
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U U' fun a ha b hb =>
    mul_comm_of_mem h.elem ha.1 hb.1).1
  rw [hbot, card_bot, mul_one, h.card_inf_centralizer_eq hP hP'] at hc
  have hle : Nat.card (U ⊔ U' : Subgroup G) ≤ Nat.card V :=
    card_le_of_le (sup_le inf_le_left inf_le_left)
  rw [hc, h.card] at hle
  have h4 : 2 ^ (4 * m) = 2 ^ (2 * m) * 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
  rw [h4] at hle
  exact absurd hle (not_le.mpr (Nat.mul_lt_mul'' hU hU))

theorem card_inf_centralizer_eq_of_ne_bot (hk : Nat.card k = 2 ^ m) (hm : 2 ≤ m) (hm3 : m ≠ 3)
    (φX : X ≃* SpecialLinearGroup (Fin 2) k) (φY : Y ≃* SpecialLinearGroup (Fin 2) k)
    (hX : V ⊓ centralizer (X : Set G) ≠ ⊥) (hY : V ⊓ centralizer (Y : Set G) ≠ ⊥) :
    Nat.card (V ⊓ centralizer (X : Set G) : Subgroup G) = 2 ^ (2 * m) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := V ⊓ centralizer (X : Set G)
  rcases lt_trichotomy (Nat.card D) (2 ^ (2 * m)) with hlt | heq | hgt
  · exfalso
    have hYD : Y ≤ centralizer (D : Set G) := le_centralizer_of_card_lt hk hm hm3 φY
      (le_normalizer_inf_centralizer h.normY h.le_centralizer) (h.isPGroup_of_le inf_le_left)
      hlt
    apply hX
    rw [eq_bot_iff, ← h.fixed]
    intro d hd
    exact ⟨hd, mem_centralizer_iff.mpr fun y hy => (mem_centralizer_iff.mp (hYD hy) d hd).symm⟩
  · exact heq
  · exfalso
    have hXV : X ≤ centralizer (V : Set G) := le_centralizer_of_card_lt_mul hk hm hm3 φX
      (h.comm_of_le le_rfl) h.isPGroup inf_le_left h.normX inf_le_right (by
        rw [h.card, show 4 * m = 2 * m + 2 * m by ring, pow_add]
        exact Nat.mul_lt_mul_of_pos_left hgt (by positivity))
    apply hY
    rw [eq_bot_iff, ← h.fixed]
    intro v hv
    exact ⟨⟨hv.1, mem_centralizer_iff.mpr fun x hx =>
      (mem_centralizer_iff.mp (hXV hx) v hv.1).symm⟩, hv.2⟩

end PairSetting

theorem isSylowOf_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P K : Subgroup G}
    (hP : IsSylowOf p P K) {x : G} (hx : x ∈ K) :
    IsSylowOf p (P.map (MulAut.conj x).toMonoidHom) K := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  obtain ⟨hle, hp, hdvd⟩ := hP
  have hle' : P.map (MulAut.conj x).toMonoidHom ≤ K := by
    rw [← map_conj_self hx]
    exact map_mono hle
  refine ⟨hle', hp.map _, ?_⟩
  have h1 := relIndex_mul_card P K
  have h2 := relIndex_mul_card (P.map (MulAut.conj x).toMonoidHom) K
  rw [inf_eq_left.mpr hle] at h1
  rw [inf_eq_left.mpr hle', card_map_conj, ← h1] at h2
  rwa [Nat.eq_of_mul_eq_mul_right Nat.card_pos h2]

end Prelim

open Prelim in
theorem sl2_pair_module_small [Finite G] [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) (hm3 : m ≠ 3) {V X Y : Subgroup G} (hV : IsElementaryAbelian 2 V)
    (hVcard : Nat.card V = 2 ^ (4 * m)) (φX : X ≃* SpecialLinearGroup (Fin 2) k)
    (φY : Y ≃* SpecialLinearGroup (Fin 2) k) (hXV : X ≤ normalizer (V : Set G))
    (hYV : Y ≤ normalizer (V : Set G)) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hfix : V ⊓ centralizer (X : Set G) ⊓ centralizer (Y : Set G) = ⊥)
    {P P' Q Q' : Subgroup G} (hP : IsSylowOf 2 P X) (hP' : IsSylowOf 2 P' X) (hPP : P ≠ P')
    (hQ : IsSylowOf 2 Q Y) (hQ' : IsSylowOf 2 Q' Y) (hQQ : Q ≠ Q')
    (hUW : Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) =
      Nat.card (V ⊓ centralizer (Q : Set G) : Subgroup G))
    (hle : Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) ≤ 2 ^ (2 * m)) :
    Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ (2 * m) ∧
      (V ⊓ centralizer (P : Set G)) ⊔ (V ⊓ centralizer (P' : Set G)) = V ∧
      (V ⊓ centralizer (P : Set G)) ⊓ (V ⊓ centralizer (P' : Set G)) = ⊥ ∧
      (V ⊓ centralizer (Q : Set G)) ⊔ (V ⊓ centralizer (Q' : Set G)) = V ∧
      (V ⊓ centralizer (Q : Set G)) ⊓ (V ⊓ centralizer (Q' : Set G)) = ⊥ ∧
      (∃ θ : (Fin 2 → k) → G, IsNaturalModule φX θ ∧
        Set.range θ = ((V ⊓ centralizer (Q : Set G) : Subgroup G) : Set G)) ∧
      (∃ θ : (Fin 2 → k) → G, IsNaturalModule φX θ ∧
        Set.range θ = ((V ⊓ centralizer (Q' : Set G) : Subgroup G) : Set G)) ∧
      (∃ θ : (Fin 2 → k) → G, IsNaturalModule φY θ ∧
        Set.range θ = ((V ⊓ centralizer (P : Set G) : Subgroup G) : Set G)) ∧
      ∃ θ : (Fin 2 → k) → G, IsNaturalModule φY θ ∧
        Set.range θ = ((V ⊓ centralizer (P' : Set G) : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : PairSetting m V X Y := ⟨hV, hVcard, hXV, hYV, hXY, hfix⟩
  have hm1 : 1 ≤ m := by omega
  set U := V ⊓ centralizer (P : Set G)
  set U' := V ⊓ centralizer (P' : Set G)
  set W := V ⊓ centralizer (Q : Set G)
  set W' := V ⊓ centralizer (Q' : Set G)
  have hU := h.card_eq_of_card_le hk hm hm3 φX φY hP hQ hUW hle
  have hW : Nat.card W = 2 ^ (2 * m) := hUW ▸ hU
  have hX0 := h.inf_centralizer_eq_bot hk hm hm3 φX φY hP hQ hU hW
  have hY0 := h.symm.inf_centralizer_eq_bot hk hm hm3 φY φX hQ hP hW hU
  have hU' : Nat.card U' = 2 ^ (2 * m) := (h.card_inf_centralizer_eq hP hP').trans hU
  have hW' : Nat.card W' = 2 ^ (2 * m) := (h.symm.card_inf_centralizer_eq hQ hQ').trans hW
  have hUU : U ⊓ U' = ⊥ := (inf_inf_centralizer_eq hk hm1 φX V hP hP' hPP).trans hX0
  have hWW : W ⊓ W' = ⊥ := (inf_inf_centralizer_eq hk hm1 φY V hQ hQ' hQQ).trans hY0
  have h4 : 2 ^ (4 * m) = 2 ^ (2 * m) * 2 ^ (2 * m) := by rw [← pow_add]; ring_nf
  have hsup : ∀ {A A' : Subgroup G}, A ≤ V → A' ≤ V → A ⊓ A' = ⊥ →
      Nat.card A = 2 ^ (2 * m) → Nat.card A' = 2 ^ (2 * m) → A ⊔ A' = V := by
    intro A A' hA hA' hAA hcA hcA'
    have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A A' fun a ha b hb =>
      mul_comm_of_mem hV (hA ha) (hA' hb)).1
    rw [hAA, card_bot, mul_one, hcA, hcA', ← h4, ← hVcard] at hc
    exact eq_of_le_of_card_ge (sup_le hA hA') hc.ge
  have hUU' : U ⊔ U' = V := hsup inf_le_left inf_le_left hUU hU hU'
  have hWW' : W ⊔ W' = V := hsup inf_le_left inf_le_left hWW hW hW'
  have hsq : ∀ {a : ℕ}, a * a = 2 ^ (2 * m) → a = 2 ^ m := by
    intro a ha
    rw [← sq, pow_mul'] at ha
    exact Nat.pow_left_injective two_ne_zero ha
  have hQU : Q ≤ normalizer (U : Set G) := hQ.le.trans (h.le_normalizer_right hP.le)
  have hQU' : Q ≤ normalizer (U' : Set G) := hQ.le.trans (h.le_normalizer_right hP'.le)
  have hPW : P ≤ normalizer (W : Set G) := hP.le.trans (h.symm.le_normalizer_right hQ.le)
  have hPW' : P ≤ normalizer (W' : Set G) := hP.le.trans (h.symm.le_normalizer_right hQ'.le)
  have hcQ : Nat.card W = Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) *
      Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) := by
    have := card_inf_centralizer_eq_mul (h.comm_of_le le_rfl) hUU' hUU hQU hQU'
    rw [h.card_inf_inf_centralizer_eq hP hP' hQ.le] at this
    exact this
  have hUQ : Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = 2 ^ m :=
    hsq (hcQ.symm.trans hW)
  have hU'Q : Nat.card (U' ⊓ centralizer (Q : Set G) : Subgroup G) = 2 ^ m :=
    (h.card_inf_inf_centralizer_eq hP hP' hQ.le).trans hUQ
  have hcP : Nat.card U = Nat.card (W ⊓ centralizer (P : Set G) : Subgroup G) *
      Nat.card (W ⊓ centralizer (P : Set G) : Subgroup G) := by
    have := card_inf_centralizer_eq_mul (h.comm_of_le le_rfl) hWW' hWW hPW hPW'
    rw [h.symm.card_inf_inf_centralizer_eq hQ hQ' hP.le] at this
    exact this
  have hWP : Nat.card (W ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ m :=
    hsq (hcP.symm.trans hU)
  have hW'P : Nat.card (W' ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ m :=
    (h.symm.card_inf_inf_centralizer_eq hQ hQ' hP.le).trans hWP
  have hfixX : ∀ {A : Subgroup G}, A ≤ V → A ⊓ centralizer (X : Set G) = ⊥ := fun hA =>
    eq_bot_iff.mpr ((inf_le_inf_right _ hA).trans hX0.le)
  have hfixY : ∀ {A : Subgroup G}, A ≤ V → A ⊓ centralizer (Y : Set G) = ⊥ := fun hA =>
    eq_bot_iff.mpr ((inf_le_inf_right _ hA).trans hY0.le)
  exact ⟨hU, hUU', hUU, hWW', hWW,
    exists_isNaturalModule hk hm1 φX (h.elem_of_le inf_le_left)
      (h.symm.le_normalizer_right hQ.le) hW (hfixX inf_le_left) hP hWP,
    exists_isNaturalModule hk hm1 φX (h.elem_of_le inf_le_left)
      (h.symm.le_normalizer_right hQ'.le) hW' (hfixX inf_le_left) hP hW'P,
    exists_isNaturalModule hk hm1 φY (h.elem_of_le inf_le_left)
      (h.le_normalizer_right hP.le) hU (hfixY inf_le_left) hQ hUQ,
    exists_isNaturalModule hk hm1 φY (h.elem_of_le inf_le_left)
      (h.le_normalizer_right hP'.le) hU' (hfixY inf_le_left) hQ hU'Q⟩

open Prelim in
theorem sl2_pair_module_large [Finite G] [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) (hm3 : m ≠ 3) {V X Y : Subgroup G} (hV : IsElementaryAbelian 2 V)
    (hVcard : Nat.card V = 2 ^ (4 * m)) (φX : X ≃* SpecialLinearGroup (Fin 2) k)
    (φY : Y ≃* SpecialLinearGroup (Fin 2) k) (hXV : X ≤ normalizer (V : Set G))
    (hYV : Y ≤ normalizer (V : Set G)) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hfix : V ⊓ centralizer (X : Set G) ⊓ centralizer (Y : Set G) = ⊥)
    {P P' Q Q' : Subgroup G} (hP : IsSylowOf 2 P X) (hP' : IsSylowOf 2 P' X) (hPP : P ≠ P')
    (hQ : IsSylowOf 2 Q Y) (hQ' : IsSylowOf 2 Q' Y) (hQQ : Q ≠ Q')
    (hU : 2 ^ (2 * m) < Nat.card (V ⊓ centralizer (P : Set G) : Subgroup G))
    (hW : 2 ^ (2 * m) < Nat.card (V ⊓ centralizer (Q : Set G) : Subgroup G)) :
    V ⊓ centralizer (X : Set G) = (V ⊓ centralizer (P : Set G)) ⊓ (V ⊓ centralizer (P' : Set G)) ∧
      V ⊓ centralizer (Y : Set G) =
        (V ⊓ centralizer (Q : Set G)) ⊓ (V ⊓ centralizer (Q' : Set G)) ∧
      (V ⊓ centralizer (X : Set G)) ⊔ (V ⊓ centralizer (Y : Set G)) = V ∧
      (V ⊓ centralizer (X : Set G)) ⊓ (V ⊓ centralizer (Y : Set G)) = ⊥ ∧
      Nat.card (V ⊓ centralizer (X : Set G) : Subgroup G) = 2 ^ (2 * m) ∧
      Nat.card (V ⊓ centralizer (Y : Set G) : Subgroup G) = 2 ^ (2 * m) := by
  have h : PairSetting m V X Y := ⟨hV, hVcard, hXV, hYV, hXY, hfix⟩
  have hm1 : 1 ≤ m := by omega
  have hX1 := h.inf_centralizer_ne_bot_of_lt hk hm1 φX hP hP' hPP hU
  have hY1 := h.symm.inf_centralizer_ne_bot_of_lt hk hm1 φY hQ hQ' hQQ hW
  have hXc := h.card_inf_centralizer_eq_of_ne_bot hk hm hm3 φX φY hX1 hY1
  have hYc := h.symm.card_inf_centralizer_eq_of_ne_bot hk hm hm3 φY φX hY1 hX1
  have hinf : (V ⊓ centralizer (X : Set G)) ⊓ (V ⊓ centralizer (Y : Set G)) = ⊥ := by
    rw [← hfix]
    ext z
    simp only [mem_inf]
    tauto
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (V ⊓ centralizer (X : Set G))
    (V ⊓ centralizer (Y : Set G)) fun a ha b hb => mul_comm_of_mem hV ha.1 hb.1).1
  rw [hinf, card_bot, mul_one, hXc, hYc, ← pow_add, show 2 * m + 2 * m = 4 * m by ring,
    ← hVcard] at hc
  exact ⟨(inf_inf_centralizer_eq hk hm1 φX V hP hP' hPP).symm,
    (inf_inf_centralizer_eq hk hm1 φY V hQ hQ' hQQ).symm,
    eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) hc.ge, hinf, hXc, hYc⟩

end CFSG.LocalAnalysis.EvenBN.U5

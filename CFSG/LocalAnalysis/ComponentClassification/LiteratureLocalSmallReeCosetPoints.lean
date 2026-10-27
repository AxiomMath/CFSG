module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Walter.Ree.Model.Cells

public noncomputable section

namespace CFSG.ComponentClassification.LiteratureLocal.SmallRee

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.Walter.Ree.Model

variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

omit [CharP K ReeTag.G2.prime] in
theorem pow_two_mul_sub_one_ne_one (hK : Nat.card K = 3 ^ (2 * a + 1)) {s : Kˣ} (hs : s ≠ 1) :
    s ^ (2 * 3 ^ a - 1) ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  intro h
  apply hs
  apply hbij.1
  simp only [one_pow]
  exact h

omit [CharP K ReeTag.G2.prime] in
theorem pow_three_pow_ne_one (hK : Nat.card K = 3 ^ (2 * a + 1)) {s : Kˣ} (hs : s ≠ 1) :
    (s : K) ^ 3 ^ a ≠ 1 := by
  obtain ⟨-, ρ, -, hρ, -⟩ := small_Ree_field_power_identities a K hK
  intro h
  apply hs
  apply Units.ext
  apply ρ.injective
  rw [hρ, hρ, h, Units.val_one, one_pow]

omit [CharP K ReeTag.G2.prime] in
theorem zpow_one_sub_ne_one (hK : Nat.card K = 3 ^ (2 * a + 1)) {s : Kˣ} (hs1 : s ≠ 1)
    (hs2 : s ≠ -1) : s ^ (1 - (3 ^ a : ℤ)) ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hgcd, -⟩ := small_Ree_field_power_identities a K hK
  intro h
  have hθ : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
  have h1 : s ^ (3 ^ a - 1) = 1 := by
    have e : (1 - (3 ^ a : ℤ)) = -((3 ^ a - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hθ]
      push_cast
      ring
    rw [e, zpow_neg, zpow_natCast, inv_eq_one] at h
    exact h
  have hq : s ^ (3 ^ (2 * a + 1) - 1) = 1 := by
    have h0 : s ^ Nat.card Kˣ = 1 := pow_card_eq_one'
    rwa [Nat.card_units, hK] at h0
  have h2 : orderOf s ∣ 2 := by
    rw [← hgcd]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hq)
  have h3 : s ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h2
  have h4 : ((s : K) - 1) * ((s : K) + 1) = 0 := by
    have : (s : K) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h3, Units.val_one]
    linear_combination this
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact hs1 (Units.ext (by rw [Units.val_one]; linear_combination h5))
  · exact hs2 (Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination h5))

theorem eq_zero_of_smallReeH_conj_eq (hK : Nat.card K = 3 ^ (2 * a + 1)) {s : Kˣ} (hs1 : s ≠ 1)
    (hs2 : s ≠ -1) {v b c : K}
    (h : smallReeH a K s * smallReeU a K v b c * (smallReeH a K s)⁻¹ = smallReeU a K v b c) :
    v = 0 ∧ b = 0 ∧ c = 0 := by
  have h' := ReeTag.smallReeTorusElt_conj_smallReeCoord (a := a) hK s v b c
  have h'' : smallReeU a K (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * v)
      (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b) ((s : K) ^ 3 ^ a * c) =
        smallReeU a K v b c := h'.symm.trans h
  obtain ⟨hv, hb, hc⟩ := smallReeU_inj h''
  have e1 : (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) - 1) ≠ 0 := by
    intro e
    apply pow_two_mul_sub_one_ne_one hK hs1
    exact Units.ext (by rw [Units.val_one]; linear_combination e)
  have e2 : (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) - 1) ≠ 0 := by
    intro e
    apply zpow_one_sub_ne_one hK hs1 hs2
    exact Units.ext (by rw [Units.val_one]; linear_combination e)
  have e3 : ((s : K) ^ 3 ^ a - 1) ≠ 0 := by
    intro e
    exact pow_three_pow_ne_one hK hs1 (by linear_combination e)
  refine ⟨?_, ?_, ?_⟩
  · have : (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) - 1) * v = 0 := by linear_combination hv
    exact (mul_eq_zero.1 this).resolve_left e1
  · have : (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) - 1) * b = 0 := by linear_combination hb
    exact (mul_eq_zero.1 this).resolve_left e2
  · have : ((s : K) ^ 3 ^ a - 1) * c = 0 := by linear_combination hc
    exact (mul_eq_zero.1 this).resolve_left e3

variable (hK : Nat.card K = 3 ^ (2 * a + 1)) {w₀ : WeylGroup ReeTag.G2.tag}
  (hw₀ : ∀ w, (coxeterSystem ReeTag.G2.tag).length w ≤ (coxeterSystem ReeTag.G2.tag).length w₀)

variable (a K) in
@[expose] def longestIn : ReeTag.G2.reeGamma K a :=
  ⟨canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀, ReeTag.canonicalRep_longest_mem_reeGamma hw₀⟩

variable (a K) in
@[expose] def basePt : ReeTag.G2.reeGamma K a ⧸
    (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) :=
  QuotientGroup.mk 1

variable (a K) in
@[expose] def oppPt : ReeTag.G2.reeGamma K a ⧸
    (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) :=
  QuotientGroup.mk (longestIn a K hw₀)

include hK hw₀

theorem eq_basePt_of_smul_eq {u : ReeTag.G2.reeGamma K a}
    (hu : (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a) (hu1 : u ≠ 1)
    {ω : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)}
    (h : u • ω = ω) : ω = basePt a K := by
  obtain ⟨-, -, -, -, -, -, hreg, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  by_contra hω
  obtain ⟨v, -, huniq⟩ := hreg ω ω hω hω
  have h1 := huniq ⟨u, hu⟩ h
  have h2 := huniq 1 (one_smul _ _)
  exact hu1 (congrArg Subtype.val (h1.trans h2.symm))

omit hK in
theorem smul_oppPt_of_mem_torus {h : ReeTag.G2.reeGamma K a}
    (hh : (h : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a) :
    h • oppPt a K hw₀ = oppPt a K hw₀ := by
  rw [oppPt, MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hT : (h : ModGL ReeTag.G2.tag K)⁻¹ ∈ torusGroup ReeTag.G2.tag K :=
    inv_mem (Subgroup.mem_inf.1 hh).1
  have e : ((h • longestIn a K hw₀ : ReeTag.G2.reeGamma K a)⁻¹ * longestIn a K hw₀ :
      ReeTag.G2.reeGamma K a) = (longestIn a K hw₀)⁻¹ * h⁻¹ * longestIn a K hw₀ := by
    rw [smul_eq_mul]
    group
  rw [e]
  show (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹ * (h : ModGL ReeTag.G2.tag K)⁻¹ *
    canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∈ _
  rw [canonicalRep_inv_conj hw₀ hT, inv_inv]
  exact ReeTag.reeFixedTorus_le_reeFixedBorel hh

theorem exists_smul_oppPt {ω : ReeTag.G2.reeGamma K a ⧸
    (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)} (hω : ω ≠ basePt a K) :
    ∃ u : ReeTag.G2.reeGamma K a,
      (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a ∧ u • oppPt a K hw₀ = ω := by
  obtain ⟨hn, -, -, -, hbij, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  obtain ⟨u, -, hu⟩ := hbij.2.2 (show ω ∈ {ω | ω ≠ QuotientGroup.mk 1} from hω)
  exact ⟨u, u.2, hu⟩

theorem eq_of_smul_oppPt_eq {u u' : ReeTag.G2.reeGamma K a}
    (hu : (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a)
    (hu' : (u' : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a)
    (h : u • oppPt a K hw₀ = u' • oppPt a K hw₀) : u = u' := by
  obtain ⟨hn, -, -, -, hbij, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  have := hbij.injOn (Set.mem_univ (⟨u, hu⟩ :
    (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)))
    (Set.mem_univ (⟨u', hu'⟩ :
      (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a))) h
  exact congrArg Subtype.val this

theorem smul_oppPt_ne_basePt {u : ReeTag.G2.reeGamma K a}
    (hu : (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a) :
    u • oppPt a K hw₀ ≠ basePt a K := by
  obtain ⟨hn, -, -, -, hbij, -⟩ := small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
  exact hbij.1 (Set.mem_univ (⟨u, hu⟩ :
    (ReeTag.G2.reeFixedPosUnipotent K a).subgroupOf (ReeTag.G2.reeGamma K a)))

omit hK in
theorem torus_smul_smul_oppPt {h u : ReeTag.G2.reeGamma K a}
    (hh : (h : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a) :
    h • (u • oppPt a K hw₀) = (h * u * h⁻¹) • oppPt a K hw₀ := by
  rw [mul_smul, mul_smul, smul_oppPt_of_mem_torus hw₀ (h := h⁻¹)
    (show ((h⁻¹ : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈ _ from inv_mem hh)]

theorem torus_smul_smul_oppPt_eq_iff {h u : ReeTag.G2.reeGamma K a}
    (hh : (h : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a)
    (hu : (u : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedPosUnipotent K a) :
    h • (u • oppPt a K hw₀) = u • oppPt a K hw₀ ↔ h * u * h⁻¹ = u := by
  rw [torus_smul_smul_oppPt hw₀ hh]
  constructor
  · intro e
    refine eq_of_smul_oppPt_eq hK hw₀ ?_ hu e
    have := (Subgroup.mem_normalizer_iff.mp
      (ReeTag.reeFixedTorus_le_normalizer_reeFixedPosUnipotent hh) u).mp hu
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  · intro e
    rw [e]

omit hw₀ in
@[expose] def midIn (b : K) : ReeTag.G2.reeGamma K a :=
  ⟨smallReeU a K 0 b 0, ReeTag.reeFixedPosUnipotent_le_reeGamma (smallReeU_mem hK 0 b 0)⟩

omit hw₀ in
theorem midIn_val (b : K) :
    ((midIn hK b : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) = smallReeU a K 0 b 0 := by
  rw [midIn]

omit hw₀ in
theorem midIn_mem (b : K) :
    ((midIn hK b : ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K) ∈
      ReeTag.G2.reeFixedPosUnipotent K a :=
  smallReeU_mem hK 0 b 0

omit hK hw₀ in
theorem smul_basePt_of_mem_borel {g : ReeTag.G2.reeGamma K a}
    (hg : (g : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a) :
    g • basePt a K = basePt a K := by
  rw [basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  simpa using inv_mem hg

omit hK hw₀ in
theorem mem_borel_of_smul_basePt {g : ReeTag.G2.reeGamma K a} (hg : g • basePt a K = basePt a K) :
    (g : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedBorel K a := by
  rw [basePt, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hg
  simpa using inv_mem hg

theorem eq_basePt_or_eq_oppPt_of_torus_smul {s : Kˣ} (hs1 : s ≠ 1) (hs2 : s ≠ -1)
    {h : ReeTag.G2.reeGamma K a} (hh : (h : ModGL ReeTag.G2.tag K) = smallReeH a K s)
    {ω : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)} (hω : h • ω = ω) :
    ω = basePt a K ∨ ω = oppPt a K hw₀ := by
  by_cases h0 : ω = basePt a K
  · exact Or.inl h0
  right
  obtain ⟨u, hu, rfl⟩ := exists_smul_oppPt hK hw₀ h0
  have hhT : (h : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a := hh ▸ smallReeH_mem hK s
  have hc := (torus_smul_smul_oppPt_eq_iff hK hw₀ hhT hu).1 hω
  obtain ⟨v, b, c, hvbc⟩ := exists_smallReeU_eq hK hu
  have hc' : smallReeH a K s * smallReeU a K v b c * (smallReeH a K s)⁻¹ =
      smallReeU a K v b c := by
    have h1 := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [hh, ← hvbc] at h1
    exact h1
  obtain ⟨rfl, rfl, rfl⟩ := eq_zero_of_smallReeH_conj_eq hK hs1 hs2 hc'
  have hu1 : u = 1 := Subtype.ext (by
    rw [← hvbc, OneMemClass.coe_one]
    exact smallReeCoord_zero)
  rw [hu1, one_smul]

theorem torusInv_smul_eq_iff {t : ReeTag.G2.reeGamma K a}
    (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1))
    (ω : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a)) :
    t • ω = ω ↔ ω = basePt a K ∨ ∃ b : K, ω = midIn hK b • oppPt a K hw₀ := by
  have htT : (t : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a :=
    ht ▸ smallReeH_mem hK (-1)
  constructor
  · intro hω
    by_cases h0 : ω = basePt a K
    · exact Or.inl h0
    right
    obtain ⟨u, hu, rfl⟩ := exists_smul_oppPt hK hw₀ h0
    have hc := (torus_smul_smul_oppPt_eq_iff hK hw₀ htT hu).1 hω
    obtain ⟨v, b, c, hvbc⟩ := exists_smallReeU_eq hK hu
    have hc' : smallReeU a K v b c * smallReeH a K (-1) =
        smallReeH a K (-1) * smallReeU a K v b c := by
      have h1 := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [ht, ← hvbc] at h1
      calc smallReeU a K v b c * smallReeH a K (-1) =
            smallReeH a K (-1) * smallReeU a K v b c * (smallReeH a K (-1))⁻¹ *
              smallReeH a K (-1) := by rw [h1]
        _ = _ := by group
    obtain ⟨rfl, rfl⟩ := (smallReeU_commute_iff hK v b c).1 hc'
    exact ⟨b, by rw [show u = midIn hK b from Subtype.ext hvbc.symm]⟩
  · rintro (rfl | ⟨b, rfl⟩)
    · exact smul_basePt_of_mem_borel (ReeTag.reeFixedTorus_le_reeFixedBorel htT)
    · refine (torus_smul_smul_oppPt_eq_iff hK hw₀ htT (midIn_mem hK b)).2 ?_
      have hcomm := (smallReeU_commute_iff (a := a) hK 0 b 0).2 ⟨rfl, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, midIn, ht]
      rw [← hcomm]
      group

theorem ncard_fixed_torusInv {t : ReeTag.G2.reeGamma K a}
    (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1)) :
    {ω : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) | t • ω = ω}.ncard =
      3 ^ (2 * a + 1) + 1 := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  have hset : {ω : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a) | t • ω = ω} =
      insert (basePt a K) (Set.range fun b : K => midIn hK b • oppPt a K hw₀) := by
    ext ω
    change t • ω = ω ↔ _
    rw [torusInv_smul_eq_iff hK hw₀ ht, Set.mem_insert_iff, Set.mem_range]
    constructor
    · rintro (h | ⟨b, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨b, h.symm⟩
    · rintro (h | ⟨b, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨b, h.symm⟩
  have hinj : Function.Injective fun b : K => midIn hK b • oppPt a K hw₀ := by
    intro b b' h
    have h1 := eq_of_smul_oppPt_eq hK hw₀ (midIn_mem hK b) (midIn_mem hK b') h
    have h2 : smallReeU a K 0 b 0 = smallReeU a K 0 b' 0 := by
      rw [← midIn_val hK, ← midIn_val hK, h1]
    exact (smallReeU_inj h2).2.1
  have hnot : basePt a K ∉ Set.range fun b : K => midIn hK b • oppPt a K hw₀ := by
    rintro ⟨b, hb⟩
    exact smul_oppPt_ne_basePt hK hw₀ (midIn_mem hK b) hb
  rw [hset, Set.ncard_insert_of_notMem hnot (Set.toFinite _), Set.ncard_range_of_injective hinj,
    hK]

theorem eq_one_or_eq_of_forall_fixed {t : ReeTag.G2.reeGamma K a}
    (ht : (t : ModGL ReeTag.G2.tag K) = smallReeH a K (-1)) {g : ReeTag.G2.reeGamma K a}
    (hg : ∀ ω : ReeTag.G2.reeGamma K a ⧸
      (ReeTag.G2.reeFixedBorel K a).subgroupOf (ReeTag.G2.reeGamma K a),
        t • ω = ω → g • ω = ω) : g = 1 ∨ g = t := by
  have hξ := hg (basePt a K) ((torusInv_smul_eq_iff hK hw₀ ht _).2 (Or.inl rfl))
  have hη := hg (oppPt a K hw₀) ((torusInv_smul_eq_iff hK hw₀ ht _).2
    (Or.inr ⟨0, by rw [show midIn hK (0 : K) = 1 from Subtype.ext smallReeCoord_zero,
      one_smul]⟩))
  have hgB := mem_borel_of_smul_basePt hξ
  have hgB' : (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹ * (g : ModGL ReeTag.G2.tag K) *
      canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ ∈ ReeTag.G2.reeFixedBorel K a := by
    rw [oppPt, MulAction.Quotient.smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hη
    have h1 := inv_mem hη
    have e : ((((g • longestIn a K hw₀ : ReeTag.G2.reeGamma K a)⁻¹ * longestIn a K hw₀ :
        ReeTag.G2.reeGamma K a) : ModGL ReeTag.G2.tag K))⁻¹ =
        (canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀)⁻¹ * (g : ModGL ReeTag.G2.tag K) *
          canonicalRep (coxeterSystem ReeTag.G2.tag) K w₀ := by
      simp only [smul_eq_mul, Subgroup.coe_mul, Subgroup.coe_inv, longestIn]
      group
    rw [e] at h1
    exact h1
  have hgH : (g : ModGL ReeTag.G2.tag K) ∈ ReeTag.G2.reeFixedTorus K a := by
    rw [← ReeTag.reeFixedBorel_inf_map_conj (K := K) (a := a) hw₀]
    refine Subgroup.mem_inf.2 ⟨hgB, ⟨_, hgB', ?_⟩⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨s, hs⟩ := exists_smallReeH_eq hgH
  have hfix := hg (midIn hK 1 • oppPt a K hw₀) ((torusInv_smul_eq_iff hK hw₀ ht _).2
    (Or.inr ⟨1, rfl⟩))
  have hc := (torus_smul_smul_oppPt_eq_iff hK hw₀ hgH (midIn_mem hK 1)).1 hfix
  have hc' : smallReeH a K s * smallReeU a K 0 1 0 * (smallReeH a K s)⁻¹ =
      smallReeU a K 0 1 0 := by
    have h1 := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, midIn] at h1
    rw [← hs] at h1
    exact h1
  have h2 := ReeTag.smallReeTorusElt_conj_smallReeCoord (a := a) hK s 0 1 0
  have h3 : smallReeU a K (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * 0)
      (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * 1) ((s : K) ^ 3 ^ a * 0) = smallReeU a K 0 1 0 :=
    h2.symm.trans hc'
  have h4 := (smallReeU_inj h3).2.1
  rw [mul_one] at h4
  have h5 : s ^ (1 - (3 ^ a : ℤ)) = 1 := Units.ext (by rw [h4, Units.val_one])
  by_cases hs1 : s = 1
  · left
    apply Subtype.ext
    rw [← hs, hs1, OneMemClass.coe_one]
    exact smallReeH_one
  by_cases hs2 : s = -1
  · right
    apply Subtype.ext
    rw [← hs, hs2, ht]
  exact absurd h5 (zpow_one_sub_ne_one hK hs1 hs2)

end CFSG.ComponentClassification.LiteratureLocal.SmallRee

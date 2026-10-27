module

public import CFSG.LieType.Ree.SmallReeCoordinateProduct
public import CFSG.LieType.Ree.SmallReeTorusAction
public import CFSG.LieType.Ree.SmallReeFrattiniTorusNormalizer
public import CFSG.LieType.Ree.ReeGenericPerfect

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial CFSG.OrderReductions.FrattiniAutomorphisms
open scoped commutatorElement

namespace ReeTag

section Conj

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

variable (t K a) in
@[expose] def reeFixedTorusConj :
    t.reeFixedTorus K a →* MulAut (t.reeFixedPosUnipotent K a) where
  toFun g := ((MulAut.conj (g : ModGL t.tag K)).subgroupMap (t.reeFixedPosUnipotent K a)).trans
    (MulEquiv.subgroupCongr (map_conj_eq_of_mem_normalizer
      (reeFixedTorus_le_normalizer_reeFixedPosUnipotent g.2)))
  map_one' := MulEquiv.ext fun x => Subtype.ext (by
    change ((1 : t.reeFixedTorus K a) : ModGL t.tag K) * x *
      ((1 : t.reeFixedTorus K a) : ModGL t.tag K)⁻¹ = x
    simp)
  map_mul' g h := MulEquiv.ext fun x => Subtype.ext (by
    change ((g * h : t.reeFixedTorus K a) : ModGL t.tag K) * x *
        ((g * h : t.reeFixedTorus K a) : ModGL t.tag K)⁻¹ =
      (g : ModGL t.tag K) * ((h : ModGL t.tag K) * x * (h : ModGL t.tag K)⁻¹) *
        (g : ModGL t.tag K)⁻¹
    simp only [Subgroup.coe_mul, mul_inv_rev, mul_assoc])

theorem coe_reeFixedTorusConj
    (g : t.reeFixedTorus K a) (x : t.reeFixedPosUnipotent K a) :
    ((t.reeFixedTorusConj K a g x : t.reeFixedPosUnipotent K a) : ModGL t.tag K) =
      g * x * (g : ModGL t.tag K)⁻¹ :=
  rfl

end Conj

section Subgroups

variable {a : ℕ} {K : Type} [Field K] [CharP K G2.prime]

theorem smallReeSigma_add (x y : K) :
    smallReeSigma a (x + y) = smallReeSigma a x + smallReeSigma a y := by
  have : CharP K 3 := ‹CharP K G2.prime›
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [smallReeSigma, ← pow_succ']
  rw [add_pow_char_pow]

theorem smallReeCoord_zero_mul
    (b c d e : K) :
    smallReeCoord a K 0 b c * smallReeCoord a K 0 d e = smallReeCoord a K 0 (b + d) (c + e) := by
  have h3 := smallRee_three_eq_zero (K := K)
  simp only [smallReeCoord_eq_smallReeP]
  rw [smallReeP_mul h3]
  simp only [smallReeSigma_zero, smallReeSigma_add]
  congr 1 <;> ring

variable (a K) in
@[expose] def smallReeU1 :
    Subgroup (ModGL G2.tag K) where
  carrier := {g | ∃ b c : K, g = smallReeCoord a K 0 b c}
  mul_mem' := by
    rintro _ _ ⟨b, c, rfl⟩ ⟨d, e, rfl⟩
    exact ⟨b + d, c + e, smallReeCoord_zero_mul b c d e⟩
  one_mem' := ⟨0, 0, smallReeCoord_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨b, c, rfl⟩
    refine ⟨-b, -c, inv_eq_of_mul_eq_one_right ?_⟩
    exact (smallReeCoord_zero_mul b c (-b) (-c)).trans (by
      rw [add_neg_cancel, add_neg_cancel]
      exact smallReeCoord_zero)

variable (a K) in
@[expose] def smallReeZ1 :
    Subgroup (ModGL G2.tag K) where
  carrier := {g | ∃ c : K, g = smallReeCoord a K 0 0 c}
  mul_mem' := by
    rintro _ _ ⟨c, rfl⟩ ⟨e, rfl⟩
    exact ⟨c + e, (smallReeCoord_zero_mul 0 c 0 e).trans (by rw [add_zero])⟩
  one_mem' := ⟨0, smallReeCoord_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨c, rfl⟩
    refine ⟨-c, inv_eq_of_mul_eq_one_right ?_⟩
    exact (smallReeCoord_zero_mul 0 c 0 (-c)).trans (by
      rw [add_zero, add_neg_cancel]
      exact smallReeCoord_zero)

end Subgroups

section Coordinates

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}

theorem smallReeCoord_mem_reeFixedPosUnipotent
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (t b c : K) :
    (smallReeCoord a K t b c : ModGL G2.tag K) ∈ G2.reeFixedPosUnipotent K a :=
  Subgroup.mem_inf.2 ⟨smallReeCoord_mem_posUnipotent a K t b c,
    mem_reeGamma_of_fixed (smallReeCoord_mem_adjointGroup t b c)
      (finiteReeAut_smallReeCoord hK t b c)⟩

@[expose] def smallReeCoordU
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (t b c : K) :
    G2.reeFixedPosUnipotent K a :=
  ⟨smallReeCoord a K t b c, smallReeCoord_mem_reeFixedPosUnipotent hK t b c⟩

variable (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

theorem coe_smallReeCoordU
    (t b c : K) :
    ((smallReeCoordU hK t b c : G2.reeFixedPosUnipotent K a) : ModGL G2.tag K) =
      smallReeCoord a K t b c :=
  rfl

theorem smallReeCoordU_mul
    (t b c s d e : K) :
    smallReeCoordU hK t b c * smallReeCoordU hK s d e = smallReeCoordU hK (t + s)
      (b + d + smallReeSigma a t * s) (c + e - b * s + smallReeSigma a t * s ^ 2) :=
  Subtype.ext (smallReeCoord_mul hK t b c s d e)

theorem smallReeCoordU_zero_mul
    (b c d e : K) :
    smallReeCoordU hK 0 b c * smallReeCoordU hK 0 d e = smallReeCoordU hK 0 (b + d) (c + e) :=
  Subtype.ext (smallReeCoord_zero_mul b c d e)

theorem smallReeCoordU_zero :
    smallReeCoordU hK 0 0 0 = 1 :=
  Subtype.ext smallReeCoord_zero

theorem smallReeCoordU_injective
    {t b c t' b' c' : K}
    (h : smallReeCoordU hK t b c = smallReeCoordU hK t' b' c') : t = t' ∧ b = b' ∧ c = c' := by
  have h1 := congrArg Subtype.val h
  rw [coe_smallReeCoordU, coe_smallReeCoordU] at h1
  have h' := (bijOn_smallReeCoord hK).2.1 (Set.mem_univ (t, b, c)) (Set.mem_univ (t', b', c')) h1
  simpa only [Prod.mk.injEq] using h'

theorem exists_smallReeCoordU_eq
    (x : G2.reeFixedPosUnipotent K a) :
    ∃ t b c, smallReeCoordU hK t b c = x := by
  obtain ⟨⟨t, b, c⟩, -, h⟩ := (bijOn_smallReeCoord hK).2.2 x.2
  exact ⟨t, b, c, Subtype.ext h⟩

theorem mem_smallReeU1_iff
    (t b c : K) :
    (smallReeCoord a K t b c : ModGL G2.tag K) ∈ smallReeU1 a K ↔ t = 0 := by
  constructor
  · rintro ⟨b', c', h⟩
    exact (smallReeCoordU_injective hK (t := t) (b := b) (c := c) (t' := 0) (b' := b') (c' := c')
      (Subtype.ext h)).1
  · rintro rfl
    exact ⟨b, c, rfl⟩

theorem mem_smallReeZ1_iff
    (t b c : K) :
    (smallReeCoord a K t b c : ModGL G2.tag K) ∈ smallReeZ1 a K ↔ t = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨c', h⟩
    obtain ⟨h1, h2, -⟩ := smallReeCoordU_injective hK (t := t) (b := b) (c := c) (t' := 0)
      (b' := 0) (c' := c') (Subtype.ext h)
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨c, rfl⟩

@[expose] def smallReeCoordEquiv
    : K × K × K ≃ G2.reeFixedPosUnipotent K a :=
  Equiv.ofBijective (fun p => smallReeCoordU hK p.1 p.2.1 p.2.2)
    ⟨fun p p' h => by
      obtain ⟨h1, h2, h3⟩ := smallReeCoordU_injective hK h
      exact Prod.ext h1 (Prod.ext h2 h3),
     fun x => by
      obtain ⟨t, b, c, h⟩ := exists_smallReeCoordU_eq hK x
      exact ⟨(t, b, c), h⟩⟩

theorem smallReeCoordEquiv_symm_apply
    (t b c : K) :
    (smallReeCoordEquiv hK).symm (smallReeCoordU hK t b c) = (t, b, c) :=
  (smallReeCoordEquiv hK).symm_apply_eq.2 rfl

@[expose] def smallReePi
    : G2.reeFixedPosUnipotent K a →* Multiplicative K where
  toFun x := Multiplicative.ofAdd ((smallReeCoordEquiv hK).symm x).1
  map_one' := by
    rw [← smallReeCoordU_zero hK, smallReeCoordEquiv_symm_apply]
    rfl
  map_mul' x y := by
    obtain ⟨t, b, c, rfl⟩ := exists_smallReeCoordU_eq hK x
    obtain ⟨s, d, e, rfl⟩ := exists_smallReeCoordU_eq hK y
    rw [smallReeCoordU_mul, smallReeCoordEquiv_symm_apply, smallReeCoordEquiv_symm_apply,
      smallReeCoordEquiv_symm_apply]
    rfl

theorem smallReePi_apply
    (t b c : K) :
    smallReePi hK (smallReeCoordU hK t b c) = Multiplicative.ofAdd t := by
  change Multiplicative.ofAdd ((smallReeCoordEquiv hK).symm (smallReeCoordU hK t b c)).1 = _
  rw [smallReeCoordEquiv_symm_apply]

theorem smallReePi_surjective
    : Function.Surjective (smallReePi hK) := fun y =>
  ⟨smallReeCoordU hK y.toAdd 0 0, by rw [smallReePi_apply]; rfl⟩

theorem ker_smallReePi :
    (smallReePi hK).ker = (smallReeU1 a K).subgroupOf (G2.reeFixedPosUnipotent K a) := by
  ext x
  obtain ⟨t, b, c, rfl⟩ := exists_smallReeCoordU_eq hK x
  rw [MonoidHom.mem_ker, smallReePi_apply, Subgroup.mem_subgroupOf]
  change _ ↔ (smallReeCoord a K t b c : ModGL G2.tag K) ∈ smallReeU1 a K
  rw [mem_smallReeU1_iff hK]
  exact ⟨fun h => by simpa using h, fun h => by rw [h]; rfl⟩

theorem center_reeFixedPosUnipotent :
    Subgroup.center (G2.reeFixedPosUnipotent K a) =
      (smallReeZ1 a K).subgroupOf (G2.reeFixedPosUnipotent K a) := by
  ext x
  obtain ⟨t, b, c, rfl⟩ := exists_smallReeCoordU_eq hK x
  rw [Subgroup.mem_center_iff, Subgroup.mem_subgroupOf]
  change _ ↔ (smallReeCoord a K t b c : ModGL G2.tag K) ∈ smallReeZ1 a K
  rw [mem_smallReeZ1_iff hK]
  constructor
  · intro h
    have h1 := h (smallReeCoordU hK 0 1 0)
    rw [smallReeCoordU_mul, smallReeCoordU_mul] at h1
    obtain ⟨-, -, e1⟩ := smallReeCoordU_injective hK h1
    rw [smallReeSigma_zero] at e1
    have ht : t = 0 := by linear_combination -e1
    subst ht
    have h2 := h (smallReeCoordU hK 1 0 0)
    rw [smallReeCoordU_mul, smallReeCoordU_mul] at h2
    obtain ⟨-, -, e2⟩ := smallReeCoordU_injective hK h2
    rw [smallReeSigma_zero] at e2
    exact ⟨rfl, by linear_combination e2⟩
  · rintro ⟨rfl, rfl⟩ g
    obtain ⟨s, d, e, rfl⟩ := exists_smallReeCoordU_eq hK g
    rw [smallReeCoordU_mul, smallReeCoordU_mul, smallReeSigma_zero]
    congr 1 <;> ring

theorem card_smallReeU1
    : Nat.card (smallReeU1 a K) = (3 ^ (2 * a + 1)) ^ 2 := by
  have hbij : Function.Bijective fun p : K × K =>
      (⟨smallReeCoord a K 0 p.1 p.2, p.1, p.2, rfl⟩ : smallReeU1 a K) := by
    refine ⟨fun p p' h => ?_, fun x => ?_⟩
    · have h0 : smallReeCoordU hK 0 p.1 p.2 = smallReeCoordU hK 0 p'.1 p'.2 := by
        refine Subtype.ext ?_
        rw [coe_smallReeCoordU, coe_smallReeCoordU]
        have h2 := congrArg Subtype.val h
        dsimp only at h2
        exact h2
      obtain ⟨-, h1, h2⟩ := smallReeCoordU_injective hK h0
      exact Prod.ext h1 h2
    · obtain ⟨b, c, hx⟩ := x.2
      exact ⟨(b, c), Subtype.ext hx.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hK, sq]

theorem card_smallReeZ1
    : Nat.card (smallReeZ1 a K) = 3 ^ (2 * a + 1) := by
  have hbij : Function.Bijective fun c : K =>
      (⟨smallReeCoord a K 0 0 c, c, rfl⟩ : smallReeZ1 a K) := by
    refine ⟨fun c c' h => ?_, fun x => ?_⟩
    · have h0 : smallReeCoordU hK 0 0 c = smallReeCoordU hK 0 0 c' := by
        refine Subtype.ext ?_
        rw [coe_smallReeCoordU, coe_smallReeCoordU]
        have h2 := congrArg Subtype.val h
        dsimp only at h2
        exact h2
      exact (smallReeCoordU_injective hK h0).2.2
    · obtain ⟨c, hx⟩ := x.2
      exact ⟨c, Subtype.ext hx.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hK]

omit [Finite K] hK in
theorem smallReeCoord_zero_comm
    (b c d e : K) :
    smallReeCoord a K 0 b c * smallReeCoord a K 0 d e =
      smallReeCoord a K 0 d e * smallReeCoord a K 0 b c := by
  rw [smallReeCoord_zero_mul, smallReeCoord_zero_mul, add_comm b, add_comm c]

omit [Finite K] hK in
theorem smallReeCoord_zero_pow_three
    (b c : K) : smallReeCoord a K 0 b c ^ 3 = 1 := by
  have h3 := smallRee_three_eq_zero (K := K)
  rw [pow_three', smallReeCoord_zero_mul, smallReeCoord_zero_mul, ← smallReeCoord_zero]
  congr 1
  · linear_combination b * h3
  · linear_combination c * h3

omit [Finite K] hK in
theorem isElementaryAbelian_smallReeU1
    : CFSG.IsElementaryAbelian 3 (smallReeU1 a K) := by
  have hcomm : ∀ x y : smallReeU1 a K, x * y = y * x := by
    rintro ⟨_, b, c, rfl⟩ ⟨_, d, e, rfl⟩
    exact Subtype.ext (smallReeCoord_zero_comm b c d e)
  have hpow : ∀ x : smallReeU1 a K, x ^ 3 = 1 := by
    rintro ⟨_, b, c, rfl⟩
    exact Subtype.ext (smallReeCoord_zero_pow_three b c)
  exact { toIsMulCommutative := ⟨⟨hcomm⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow }

end Coordinates

theorem mulAut_apply_mem_commutator {G : Type*} [Group G] (φ : MulAut G) {x : G}
    (hx : x ∈ commutator G) : φ x ∈ commutator G := by
  have h := (inferInstance : (commutator G).Characteristic).fixed φ
  exact Subgroup.mem_comap.1 ((Subgroup.ext_iff.1 h x).2 hx)

section Commutator

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
variable (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

theorem commutatorElement_smallReeCoordU
    (c : K) :
    ⁅smallReeCoordU hK 1 0 0, smallReeCoordU hK 0 c 0⁆ = smallReeCoordU hK 0 0 c := by
  have key : smallReeCoordU hK 1 0 0 * smallReeCoordU hK 0 c 0 =
      smallReeCoordU hK 0 0 c * (smallReeCoordU hK 0 c 0 * smallReeCoordU hK 1 0 0) := by
    rw [smallReeCoordU_mul, smallReeCoordU_mul, smallReeCoordU_mul, smallReeSigma_zero]
    congr 1 <;> simp [smallReeSigma]
  rw [commutatorElement_def, key]
  group

theorem smallReeCoordU_zero_zero_mem_commutator
    (c : K) :
    smallReeCoordU hK 0 0 c ∈ commutator (G2.reeFixedPosUnipotent K a) := by
  rw [← commutatorElement_smallReeCoordU hK]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

@[expose] def smallReeCommMid :
    AddSubgroup K where
  carrier := {b | ∃ c, smallReeCoordU hK 0 b c ∈ commutator (G2.reeFixedPosUnipotent K a)}
  add_mem' := by
    rintro b b' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [← smallReeCoordU_zero_mul]; exact mul_mem hc hc'⟩
  zero_mem' := ⟨0, by rw [smallReeCoordU_zero]; exact one_mem _⟩
  neg_mem' := by
    rintro b ⟨c, hc⟩
    refine ⟨-c, ?_⟩
    have h : smallReeCoordU hK 0 (-b) (-c) = (smallReeCoordU hK 0 b c)⁻¹ :=
      (inv_eq_of_mul_eq_one_right (by
        rw [smallReeCoordU_zero_mul, add_neg_cancel, add_neg_cancel, smallReeCoordU_zero])).symm
    rw [h]
    exact inv_mem hc

theorem smul_mem_smallReeCommMid
    (s : Kˣ) {b : K} (hb : b ∈ smallReeCommMid hK) :
    ((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b ∈ smallReeCommMid hK := by
  obtain ⟨c, hc⟩ := hb
  have hφ : G2.reeFixedTorusConj K a ⟨smallReeTorusElt a K s, smallReeTorusElt_mem hK s⟩
      (smallReeCoordU hK 0 b c) = smallReeCoordU hK 0
        (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * b) ((s : K) ^ 3 ^ a * c) := by
    have h1 := smallReeTorusElt_conj_smallReeCoord hK s 0 b c
    rw [mul_zero] at h1
    exact Subtype.ext h1
  refine ⟨(s : K) ^ 3 ^ a * c, ?_⟩
  rw [← hφ]
  exact mulAut_apply_mem_commutator _ hc

theorem sub_smallReeSigma_mem_smallReeCommMid
    (s : K) :
    s - smallReeSigma a s ∈ smallReeCommMid hK := by
  set g := smallReeCoordU hK 1 0 0
  set h := smallReeCoordU hK s 0 0
  have hx : ⁅g, h⁆ ∈ commutator (G2.reeFixedPosUnipotent K a) :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  obtain ⟨β₀, β, γ, hβ⟩ := exists_smallReeCoordU_eq hK ⁅g, h⁆
  have key : g * h = ⁅g, h⁆ * (h * g) := by
    rw [commutatorElement_def]
    group
  rw [← hβ] at key
  simp only [g, h, smallReeCoordU_mul] at key
  obtain ⟨e0, e1, -⟩ := smallReeCoordU_injective hK key
  have hβ₀ : β₀ = 0 := by linear_combination -e0
  subst hβ₀
  have h1 : smallReeSigma a (1 : K) = 1 := one_pow _
  rw [smallReeSigma_zero, h1] at e1
  refine ⟨γ, ?_⟩
  rw [show s - smallReeSigma a s = β by linear_combination e1, hβ]
  exact hx

theorem commutator_reeFixedPosUnipotent
    (ha : 1 ≤ a) :
    commutator (G2.reeFixedPosUnipotent K a) =
      (smallReeU1 a K).subgroupOf (G2.reeFixedPosUnipotent K a) := by
  obtain ⟨-, ρ, σ, -, hσ, -, -, -, hσ1, -, -, -, hcard⟩ := small_Ree_field_power_identities a K hK
  refine le_antisymm ?_ fun x hx => ?_
  · rw [← ker_smallReePi hK]
    exact Abelianization.commutator_subset_ker _
  ·
    have hM : smallReeCommMid hK = ⊤ := by
      obtain ⟨s₀, hs₀⟩ : ∃ s₀ : K, σ s₀ ≠ s₀ := by
        by_contra hne
        push Not at hne
        exact hσ1 ha (RingEquiv.ext hne)
      set b₀ := s₀ - smallReeSigma a s₀
      have hb₀ : b₀ ≠ 0 := fun h => hs₀ (by rw [hσ]; exact (sub_eq_zero.1 h).symm)
      have hb₀M : b₀ ∈ smallReeCommMid hK := sub_smallReeSigma_mem_smallReeCommMid hK s₀
      have hinj : Function.Injective fun μ : Kˣ => (μ : K) * b₀ := fun μ ν h =>
        Units.ext (mul_right_cancel₀ hb₀ h)
      set T : Set K := (fun μ : Kˣ => (μ : K) * b₀) ''
        Set.range fun s : Kˣ => s ^ (1 - (3 ^ a : ℤ))
      have hT : T.ncard = (3 ^ (2 * a + 1) - 1) / 2 := by
        rw [Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq, hcard]
      have hTM : insert 0 T ⊆ (smallReeCommMid hK : Set K) := by
        rintro y (rfl | ⟨μ, ⟨s, rfl⟩, rfl⟩)
        · exact (smallReeCommMid hK).zero_mem
        · exact smul_mem_smallReeCommMid hK s hb₀M
      have h0T : (0 : K) ∉ T := by
        rintro ⟨μ, -, h⟩
        exact mul_ne_zero μ.ne_zero hb₀ h
      have hle := Set.ncard_le_ncard hTM (Set.toFinite _)
      rw [Set.ncard_insert_of_notMem h0T (Set.toFinite _), hT, ← Nat.card_coe_set_eq] at hle
      have hdvd : Nat.card (smallReeCommMid hK) ∣ 3 ^ (2 * a + 1) :=
        hK ▸ AddSubgroup.card_addSubgroup_dvd_card _
      obtain ⟨j, hj, hMj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      have hj' : j = 2 * a + 1 := by
        by_contra hne
        have hj2 : j ≤ 2 * a := by omega
        have h1 : 3 ^ j ≤ 3 ^ (2 * a) := Nat.pow_le_pow_right (by norm_num) hj2
        have h2 : 3 ^ (2 * a + 1) = 3 * 3 ^ (2 * a) := by ring
        change (3 ^ (2 * a + 1) - 1) / 2 + 1 ≤ Nat.card (smallReeCommMid hK) at hle
        rw [hMj] at hle
        omega
      exact (AddSubgroup.card_eq_iff_eq_top _).1 (by rw [hMj, hj', hK])
    obtain ⟨t, b, c, rfl⟩ := exists_smallReeCoordU_eq hK x
    rw [Subgroup.mem_subgroupOf] at hx
    change (smallReeCoord a K t b c : ModGL G2.tag K) ∈ smallReeU1 a K at hx
    rw [mem_smallReeU1_iff hK] at hx
    subst hx
    obtain ⟨c', hc'⟩ : b ∈ smallReeCommMid hK := by rw [hM]; exact AddSubgroup.mem_top b
    have h1 := mul_mem hc' (smallReeCoordU_zero_zero_mem_commutator hK (c - c'))
    rwa [smallReeCoordU_zero_mul, add_zero, add_sub_cancel] at h1

end Commutator

section Frattini

variable {K : Type} [Field K] [Finite K] [CharP K G2.prime] {a : ℕ}
variable (hK : Nat.card K = 3 ^ (2 * a + 1))
include hK

theorem isPGroup_reeFixedPosUnipotent
    : IsPGroup 3 (G2.reeFixedPosUnipotent K a) :=
  IsPGroup.of_card (n := 3 * (2 * a + 1))
    (by rw [(small_Ree_positive_fixed_coordinates a K hK).2, ← pow_mul, mul_comm])

theorem frattini_reeFixedPosUnipotent
    (ha : 1 ≤ a) :
    frattini (G2.reeFixedPosUnipotent K a) =
      (smallReeU1 a K).subgroupOf (G2.reeFixedPosUnipotent K a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP := isPGroup_reeFixedPosUnipotent hK
  have : Finite (G2.reeFixedPosUnipotent K a) := Nat.finite_of_card_ne_zero (by
    rw [(small_Ree_positive_fixed_coordinates a K hK).2]; positivity)
  obtain ⟨-, hcomm, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hP
  refine le_antisymm (fun x hx => ?_) ?_
  ·
    rw [← ker_smallReePi hK, MonoidHom.mem_ker]
    by_contra hne
    set t := (smallReePi hK x).toAdd with htdef
    have ht : t ≠ 0 := fun h => hne (by rw [← ofAdd_toAdd (smallReePi hK x), ← htdef, h]; rfl)
    have : CharP K 3 := ‹CharP K G2.prime›
    let : Algebra (ZMod 3) K := ZMod.algebra K 3
    obtain ⟨l, hl⟩ : ∃ l : Module.Dual (ZMod 3) K, l t ≠ 0 := by
      by_contra h
      push Not at h
      exact ht ((Module.forall_dual_apply_eq_zero_iff (ZMod 3) t).1 h)
    let φ : G2.reeFixedPosUnipotent K a →* Multiplicative (ZMod 3) :=
      (AddMonoidHom.toMultiplicative l.toAddMonoidHom).comp (smallReePi hK)
    have hφ : Function.Surjective φ := by
      intro y
      obtain ⟨z, hz⟩ := smallReePi_surjective hK
        (Multiplicative.ofAdd (((l t)⁻¹ * y.toAdd) • t))
      refine ⟨z, ?_⟩
      change Multiplicative.ofAdd (l (smallReePi hK z).toAdd) = y
      rw [hz, toAdd_ofAdd, map_smul, smul_eq_mul, mul_right_comm, inv_mul_cancel₀ hl, one_mul]
      rfl
    have hidx : φ.ker.index = 3 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hφ, Subgroup.card_top]
      exact Nat.card_zmod 3
    have hprime : φ.ker.index.Prime := by
      rw [hidx]
      exact Nat.prime_three
    have hcoatom : IsCoatom φ.ker := Subgroup.isCoatom_of_index_prime hprime
    have hxk := frattini_le_coatom hcoatom hx
    rw [MonoidHom.mem_ker] at hxk
    change Multiplicative.ofAdd (l (smallReePi hK x).toAdd) = 1 at hxk
    exact hl (by rw [htdef]; exact hxk)
  ·
    rw [← commutator_reeFixedPosUnipotent hK ha]
    refine Subgroup.commutator_le.2 fun g _ h _ => ?_
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.is_comm.comm _ _

end Frattini

end ReeTag

theorem small_Ree_positive_Frattini_quotient
    (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) :
    IsPGroup 3 (ReeTag.G2.reeFixedPosUnipotent K a) ∧
    Nat.card (ReeTag.G2.reeFixedPosUnipotent K a) = (3 ^ (2 * a + 1)) ^ 3 ∧
    CFSG.IsElementaryAbelian 3 (ReeTag.smallReeU1 a K) ∧
    Nat.card (ReeTag.smallReeU1 a K) = (3 ^ (2 * a + 1)) ^ 2 ∧
    Subgroup.center (ReeTag.G2.reeFixedPosUnipotent K a) =
      (ReeTag.smallReeZ1 a K).subgroupOf (ReeTag.G2.reeFixedPosUnipotent K a) ∧
    Nat.card (ReeTag.smallReeZ1 a K) = 3 ^ (2 * a + 1) ∧
    commutator (ReeTag.G2.reeFixedPosUnipotent K a) =
      (ReeTag.smallReeU1 a K).subgroupOf (ReeTag.G2.reeFixedPosUnipotent K a) ∧
    frattini (ReeTag.G2.reeFixedPosUnipotent K a) =
      (ReeTag.smallReeU1 a K).subgroupOf (ReeTag.G2.reeFixedPosUnipotent K a) ∧
    ∃ π : ReeTag.G2.reeFixedPosUnipotent K a →* Multiplicative K,
      (∀ (t b c : K) (h : smallReeCoord a K t b c ∈ ReeTag.G2.reeFixedPosUnipotent K a),
        π ⟨smallReeCoord a K t b c, h⟩ = Multiplicative.ofAdd t) ∧
      Function.Surjective π ∧
      π.ker = (ReeTag.smallReeU1 a K).subgroupOf (ReeTag.G2.reeFixedPosUnipotent K a) ∧
      ∃ e : Additive (ReeTag.G2.reeFixedPosUnipotent K a ⧸
          frattini (ReeTag.G2.reeFixedPosUnipotent K a)) ≃+ K,
        (∀ x : ReeTag.G2.reeFixedPosUnipotent K a,
          e (Additive.ofMul (x : ReeTag.G2.reeFixedPosUnipotent K a ⧸
            frattini (ReeTag.G2.reeFixedPosUnipotent K a))) = (π x).toAdd) ∧
        (ReeTag.G2.reeFixedTorusConj K a).range.map (frattiniScalarRep e) =
          scalarAddAut K := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbij, -⟩ := small_Ree_field_power_identities a K hK
  set U := ReeTag.G2.reeFixedPosUnipotent K a
  set π := ReeTag.smallReePi hK
  have hΦ : frattini U = π.ker := by
    rw [ReeTag.ker_smallReePi hK, ReeTag.frattini_reeFixedPosUnipotent hK ha]
  set e : Additive (U ⧸ frattini U) ≃+ K := MulEquiv.toAdditiveLeft
    ((QuotientGroup.quotientMulEquivOfEq hΦ).trans
      (QuotientGroup.quotientKerEquivOfSurjective π (ReeTag.smallReePi_surjective hK)))
  have he : ∀ x : U, e (Additive.ofMul (x : U ⧸ frattini U)) = (π x).toAdd := fun x => rfl
  refine ⟨ReeTag.isPGroup_reeFixedPosUnipotent hK, (small_Ree_positive_fixed_coordinates a K hK).2,
    ReeTag.isElementaryAbelian_smallReeU1, ReeTag.card_smallReeU1 hK,
    ReeTag.center_reeFixedPosUnipotent hK, ReeTag.card_smallReeZ1 hK,
    ReeTag.commutator_reeFixedPosUnipotent hK ha, ReeTag.frattini_reeFixedPosUnipotent hK ha, π,
    fun t b c h => ReeTag.smallReePi_apply hK t b c, ReeTag.smallReePi_surjective hK,
    ReeTag.ker_smallReePi hK, e, he, ?_⟩
  have hact : ∀ (s : Kˣ) (y : K),
      (frattiniScalarRep e (ReeTag.G2.reeFixedTorusConj K a
        ⟨smallReeTorusElt a K s, ReeTag.smallReeTorusElt_mem hK s⟩)).toAdd y =
        ((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * y := by
    intro s y
    have hy : e.symm y = Additive.ofMul ((ReeTag.smallReeCoordU hK y 0 0 : U) : U ⧸ frattini U) :=
      e.symm_apply_eq.2 (by rw [he, ReeTag.smallReePi_apply]; rfl)
    rw [frattiniScalarRep_apply, hy, toMul_ofMul]
    change e (Additive.ofMul (quotientEquivalence (frattini U) _
      (QuotientGroup.mk' (frattini U) _))) = _
    rw [quotientEquivalence_apply, QuotientGroup.mk'_apply, he]
    have hconj : (ReeTag.G2.reeFixedTorusConj K a
        ⟨smallReeTorusElt a K s, ReeTag.smallReeTorusElt_mem hK s⟩)
          (ReeTag.smallReeCoordU hK y 0 0) =
        ReeTag.smallReeCoordU hK (((s ^ (2 * 3 ^ a - 1) : Kˣ) : K) * y)
          (((s ^ (1 - (3 ^ a : ℤ)) : Kˣ) : K) * 0) ((s : K) ^ 3 ^ a * 0) := by
      refine Subtype.ext ?_
      rw [ReeTag.coe_reeFixedTorusConj]
      exact ReeTag.smallReeTorusElt_conj_smallReeCoord hK s y 0 0
    rw [hconj, ReeTag.smallReePi_apply]
    rfl
  ext f
  constructor
  · rintro ⟨α, ⟨g, rfl⟩, rfl⟩
    obtain ⟨s, hs⟩ := ReeTag.exists_smallReeTorusElt_eq g.2
    have hg : g = ⟨smallReeTorusElt a K s, ReeTag.smallReeTorusElt_mem hK s⟩ :=
      Subtype.ext hs.symm
    exact ⟨s ^ (2 * 3 ^ a - 1), fun y => by rw [hg, hact]⟩
  · rintro ⟨c, hc⟩
    obtain ⟨s, rfl⟩ := hbij.2 c
    refine ⟨ReeTag.G2.reeFixedTorusConj K a
      ⟨smallReeTorusElt a K s, ReeTag.smallReeTorusElt_mem hK s⟩, ⟨_, rfl⟩, ?_⟩
    change Multiplicative.ofAdd _ = f
    refine (congrArg Multiplicative.ofAdd (AddEquiv.ext fun y => ?_)).trans (ofAdd_toAdd f)
    rw [hc y]
    exact hact s y

end CFSG.LieType.Ree

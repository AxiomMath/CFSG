module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Sub
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSec31TwoAux
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3A75D4Cover

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup CFSG.LieType.HighestRoot
open scoped MatrixGroups commutatorElement

namespace F3D4

theorem sl2_center_cases {K : Type} [Field K] {z : SL(2, K)} (hz : z ∈ center SL(2, K)) :
    z = 1 ∨ z = -1 := by
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  have h2 : r * r = 1 := by rw [← sq]; exact hr
  rcases mul_self_eq_one_iff.mp h2 with h | h
  · left
    apply Subtype.ext
    rw [← hrz, h, map_one, Matrix.SpecialLinearGroup.coe_one]
  · right
    apply Subtype.ext
    rw [← hrz, h, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]

@[expose] def slTwoEquivZModThree {K : Type} [Field K] [Fintype K] (hK : Fintype.card K = 3) :
    SL(2, K) ≃* SL(2, ZMod 3) :=
  { toFun := Matrix.SpecialLinearGroup.map
      (ZMod.ringEquivOfPrime K Nat.prime_three hK).symm.toRingHom
    invFun := Matrix.SpecialLinearGroup.map (ZMod.ringEquivOfPrime K Nat.prime_three hK).toRingHom
    left_inv := fun g => by ext i j; simp
    right_inv := fun g => by ext i j; simp
    map_mul' := map_mul _ }

theorem isQuasisimple_sl2 {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) :
    IsQuasisimple SL(2, K) :=
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isQuasisimple_special_linear_two h4

theorem sl23_exists_pair : ∃ a b : SL23, a ^ 2 = -1 ∧ b ^ 2 = -1 ∧ (b⁻¹ * a) ^ 2 = -1 := by
  decide +kernel

theorem sl23_pow_four_mul : ∀ a b : SL23, a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

@[expose] def sl23Q8 : Subgroup SL23 where
  carrier := {g | g ^ 4 = 1}
  mul_mem' := fun {a b} ha hb => sl23_pow_four_mul a b ha hb
  one_mem' := one_pow 4
  inv_mem' := fun {a} ha => by
    change a⁻¹ ^ 4 = 1
    rw [inv_pow, show a ^ 4 = 1 from ha, inv_one]

instance sl23Q8_normal : sl23Q8.Normal :=
  ⟨fun n hn g => by
    change (g * n * g⁻¹) ^ 4 = 1
    rw [conj_pow, show n ^ 4 = 1 from hn, mul_one, mul_inv_cancel]⟩

theorem not_isSolvable_of_isPerfect {G : Type*} [Group G] [Nontrivial G]
    (hG : Group.IsPerfect G) : ¬ Group.IsSolvable G := by
  intro hs
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := G)
  rw [Group.isPerfect_def.mp hG] at h
  exact lt_irrefl _ h

variable {Q : Type} [Group Q] [Finite Q] {L M : Subgroup Q} {t : Q}

omit [Finite Q] in
theorem normalizer_le_normalizer_map {D : Subgroup ↥L} [D.Characteristic] :
    normalizer (L : Set Q) ≤ normalizer ((D.map L.subtype : Subgroup Q) : Set Q) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact conj_mem_map_of_characteristic hg
  · intro hy
    have h1 := conj_mem_map_of_characteristic (inv_mem hg) hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h1

variable {S : Type} [Group S]

omit [Finite Q] in
theorem conj_coe_eq {c : Cover S ↥L} {m : Q} (hmN : m ∈ normalizer (L : Set Q)) {α : MulAut S}
    (hα : ∀ g, c.θ (α g) = L.normalizerMonoidHom ⟨m, hmN⟩ (c.θ g)) (g : S) :
    m * ((c.θ g : ↥L) : Q) * m⁻¹ = ((c.θ (α g) : ↥L) : Q) := by
  rw [hα]
  rfl

omit [Finite Q] in
theorem commutatorElement_coe_eq {c : Cover S ↥L} {m : Q} (hmN : m ∈ normalizer (L : Set Q))
    {α : MulAut S} (hα : ∀ g, c.θ (α g) = L.normalizerMonoidHom ⟨m, hmN⟩ (c.θ g)) (u : S) :
    ⁅((c.θ u : ↥L) : Q), m⁆ = ((c.θ (u * (α u)⁻¹) : ↥L) : Q) := by
  have h2 := conj_coe_eq hmN hα u⁻¹
  rw [map_inv c.θ u, Subgroup.coe_inv, map_inv α u] at h2
  calc ⁅((c.θ u : ↥L) : Q), m⁆ = ((c.θ u : ↥L) : Q) * (m * ((c.θ u : ↥L) : Q)⁻¹ * m⁻¹) := by
        rw [commutatorElement_def]; group
    _ = ((c.θ (u * (α u)⁻¹) : ↥L) : Q) := by rw [h2, map_mul, Subgroup.coe_mul]

theorem false_of_ker_trivial (htL : t ∈ L) (hM : IsSolvableTwoComponentIn M (centralizer {t}))
    (hMN : M ≤ normalizer (L : Set Q)) (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3))
    {c : Cover S ↥L} (hinj : ∀ z ∈ center S, c.θ z = 1 → z = 1)
    (hZ2 : ∀ z ∈ center S, z * z = 1) {m : Q} (hm : m ∈ M) (hmo : Odd (orderOf m))
    {α : MulAut S} (hα : ∀ g, c.θ (α g) = L.normalizerMonoidHom ⟨m, hMN hm⟩ (c.θ g))
    {z₀ : S} (hz₀ : z₀ ∈ center S) (hαz : α z₀ ≠ z₀) (hαz2 : α (α z₀) ≠ z₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθinj : Function.Injective c.θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    exact hinj g (c.ker_le hg) hg
  set A := normalizer (L : Set Q) ⊓ centralizer ({t} : Set Q) with hA
  have hMA : M ≤ A := le_inf hMN hM.1
  have hMs : (M.subgroupOf A).IsSubnormal := F3L226.isSubnormal_subgroupOf_mono inf_le_right hM.2.1
  set U := (center ↥L).map L.subtype with hU
  have hUA : U ≤ A := by
    rintro _ ⟨z, hz, rfl⟩
    refine mem_inf.mpr ⟨le_normalizer z.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := mem_center_iff.mp hz ⟨t, htL⟩
    exact (congrArg Subtype.val h1).symm
  have hAU : A ≤ normalizer (U : Set Q) := inf_le_left.trans normalizer_le_normalizer_map
  have hcenL : ∀ y ∈ center ↥L, ∃ z ∈ center S, c.θ z = y := by
    intro y hy
    obtain ⟨z, rfl⟩ := c.surj y
    refine ⟨z, mem_center_iff.mpr fun g => hθinj ?_, rfl⟩
    rw [map_mul, map_mul]
    exact mem_center_iff.mp hy (c.θ g)
  have hU2 : IsPGroup 2 U := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    obtain ⟨z, hz, rfl⟩ := hcenL y hy
    refine ⟨1, Subtype.ext ?_⟩
    show ((c.θ z : ↥L) : Q) ^ 2 ^ 1 = 1
    rw [pow_one, sq, ← Subgroup.coe_mul, ← map_mul, hZ2 z hz, map_one, Subgroup.coe_one]
  have hcomm := F3L225.commutator_zpowers_le_of_isSubnormal hMA hMs hUA hAU hU2 hm hmo
  have hθcen : ∀ z ∈ center S, ((c.θ z : ↥L) : Q) ∈ U := fun z hz =>
    ⟨c.θ z, mem_center_iff.mpr fun g => by
      obtain ⟨g', rfl⟩ := c.surj g
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz g'], rfl⟩
  have hw : ∀ z ∈ center S, α z ≠ z → ⁅((c.θ z : ↥L) : Q), m⁆ ∈ M ∧
      ⁅((c.θ z : ↥L) : Q), m⁆ ∈ U ∧ orderOf ⁅((c.θ z : ↥L) : Q), m⁆ = 2 := by
    intro z hz hαz'
    have h1 := hcomm (commutator_mem_commutator (hθcen z hz) (mem_zpowers m))
    refine ⟨(mem_inf.mp h1).1, (mem_inf.mp h1).2, ?_⟩
    rw [commutatorElement_coe_eq (hMN hm) hα z]
    have hzα : z * (α z)⁻¹ ∈ center S := mul_mem hz (inv_mem (Cover.mem_center_map α hz))
    apply orderOf_eq_prime
    · rw [sq, ← Subgroup.coe_mul, ← map_mul, hZ2 _ hzα, map_one, Subgroup.coe_one]
    · intro h
      have h2 : c.θ (z * (α z)⁻¹) = 1 := Subtype.ext h
      have h3 := hθinj (h2.trans (map_one c.θ).symm)
      apply hαz'
      calc α z = (z * (α z)⁻¹)⁻¹ * z := by group
        _ = z := by rw [h3, inv_one, one_mul]
  obtain ⟨hw1M, hw1U, hw1⟩ := hw z₀ hz₀ hαz
  have hz₁ : α z₀ ∈ center S := Cover.mem_center_map α hz₀
  have hαz' : α (α z₀) ≠ α z₀ := fun h => hαz (α.injective h)
  obtain ⟨hw2M, hw2U, hw2⟩ := hw (α z₀) hz₁ hαz'
  obtain ⟨k, hk⟩ := hU2 ⟨_, mul_mem hw1U hw2U⟩
  have hk' : (⁅((c.θ z₀ : ↥L) : Q), m⁆ * ⁅((c.θ (α z₀) : ↥L) : Q), m⁆) ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
  have heq := eq_of_involutions e hw1M hw2M hw1 hw2 hk'
  rw [commutatorElement_coe_eq (hMN hm) hα, commutatorElement_coe_eq (hMN hm) hα] at heq
  have h4 := hθinj (Subtype.ext heq)
  apply hαz2
  have hi1 : (α z₀)⁻¹ = α z₀ := inv_eq_of_mul_eq_one_right (hZ2 _ hz₁)
  have hz₂ : α (α z₀) ∈ center S := Cover.mem_center_map α hz₁
  have hi2 : (α (α z₀))⁻¹ = α (α z₀) := inv_eq_of_mul_eq_one_right (hZ2 _ hz₂)
  rw [hi1, hi2] at h4
  have h5 := mem_center_iff.mp hz₁ (α (α z₀))
  rw [← h5] at h4
  exact (mul_right_cancel h4).symm

omit [Finite Q] in
theorem eq_of_comp_eq {P X : Type*} [Group P] [Group X] (hperf : Group.IsPerfect P)
    {θ : S →* X} (hker : θ.ker ≤ center S) {f g : P →* S} (h : ∀ p, θ (f p) = θ (g p)) :
    f = g := by
  have hd : ∀ p, (g p)⁻¹ * f p ∈ center S := fun p => hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel])
  let d : P →* ↥(center S) :=
    { toFun := fun p => ⟨(g p)⁻¹ * f p, hd p⟩
      map_one' := by
        apply Subtype.ext
        show (g 1)⁻¹ * f 1 = 1
        rw [map_one, map_one, inv_one, one_mul]
      map_mul' := fun a b => by
        apply Subtype.ext
        show (g (a * b))⁻¹ * f (a * b) = (g a)⁻¹ * f a * ((g b)⁻¹ * f b)
        have hc := mem_center_iff.mp (hd a)
        rw [map_mul, map_mul, mul_inv_rev]
        calc (g b)⁻¹ * (g a)⁻¹ * (f a * f b) = (g b)⁻¹ * ((g a)⁻¹ * f a) * f b := by group
          _ = (g a)⁻¹ * f a * (g b)⁻¹ * f b := by rw [← hc ((g b)⁻¹)]
          _ = (g a)⁻¹ * f a * ((g b)⁻¹ * f b) := by group }
  have hcomm : commutator P ≤ d.ker := Abelianization.commutator_subset_ker d
  ext p
  have hp : p ∈ d.ker := hcomm (by rw [Group.isPerfect_def.mp hperf]; exact mem_top p)
  have h1 : (g p)⁻¹ * f p = 1 := congrArg Subtype.val hp
  calc f p = g p * ((g p)⁻¹ * f p) := by group
    _ = g p := by rw [h1, mul_one]

theorem false_of_component {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) (htL : t ∈ L)
    (hM : IsSolvableTwoComponentIn M (centralizer {t})) (hMN : M ≤ normalizer (L : Set Q))
    {c : Cover S ↥L} {x : S} (hx : c.θ x = ⟨t, htL⟩) {m : Q} (hm : m ∈ M) {α : MulAut S}
    (hα : ∀ g, c.θ (α g) = L.normalizerMonoidHom ⟨m, hMN hm⟩ (c.θ g)) (hαx : α x = x)
    {J : Subgroup S} (hJx : J ≤ centralizer ({x} : Set S))
    (hJs : (J.subgroupOf (centralizer ({x} : Set S))).IsSubnormal) (eJ : ↥J ≃* SL(2, K))
    {z : S} (hz : z ∈ center S) (hxz : x * z ∈ J) (hxZ : x ∉ center S) (hαz : α z ≠ z) :
    False := by
  have hJq : IsQuasisimple ↥J := LocalCores.isQuasisimple_of_mulEquiv eJ.symm (isQuasisimple_sl2 h4)
  set θ' : S →* Q := L.subtype.comp c.θ with hθ'
  set A := normalizer (L : Set Q) ⊓ centralizer ({t} : Set Q) with hA
  have hMA : M ≤ A := le_inf hMN hM.1
  have hMs : (M.subgroupOf A).IsSubnormal := F3L226.isSubnormal_subgroupOf_mono inf_le_right hM.2.1
  have hXs := isSubnormal_map_of_centralizer htL c.surj c.ker_le hx hJx hJs
  have hxzc : (⟨x * z, hxz⟩ : ↥J) ∈ center ↥J := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : S) * (x * z) = x * z * g
    have h1 : (g : S) * x = x * g := mem_centralizer_singleton_iff.mp (hJx g.2)
    have h2 := mem_center_iff.mp hz (g : S)
    calc (g : S) * (x * z) = (g * x) * z := by group
      _ = x * (g * z) := by rw [h1]; group
      _ = x * z * g := by rw [h2]; group
  have hxz1 : x * z ≠ 1 := fun h => hxZ (by
    have h1 : x = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact inv_mem hz)
  have hexz : eJ ⟨x * z, hxz⟩ = -1 := by
    have h1 : eJ ⟨x * z, hxz⟩ ∈ center SL(2, K) := (mem_center_mulEquiv_iff eJ _).mpr hxzc
    rcases sl2_center_cases h1 with h | h
    · exact absurd (congrArg Subtype.val ((map_eq_one_iff eJ eJ.injective).mp h)) hxz1
    · exact h
  have hinjJ : Function.Injective (θ'.comp J.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro j hj
    have h1 : c.θ (j : S) = 1 := Subtype.ext hj
    have hjZ : (j : S) ∈ center S := c.ker_le h1
    have hjc : j ∈ center ↥J := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp hjZ (g : S))
    rcases sl2_center_cases ((mem_center_mulEquiv_iff eJ _).mpr hjc) with h | h
    · exact (map_eq_one_iff eJ eJ.injective).mp h
    · exfalso
      have h2 : j = ⟨x * z, hxz⟩ := eJ.injective (h.trans hexz.symm)
      have h3 : x * z ∈ center S := by
        have h4 : (j : S) = x * z := congrArg Subtype.val h2
        rw [← h4]
        exact hjZ
      apply hxZ
      have h5 : x = (x * z) * z⁻¹ := by group
      rw [h5]
      exact mul_mem h3 (inv_mem hz)
  have hJA : J.map θ' ≤ A := by
    rintro _ ⟨j, hj, rfl⟩
    refine mem_inf.mpr ⟨le_normalizer (c.θ j).2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : j * x = x * j := mem_centralizer_singleton_iff.mp (hJx hj)
    have h2 := congrArg (fun g => ((c.θ g : ↥L) : Q)) h1
    simp only [map_mul, Subgroup.coe_mul, hx] at h2
    exact h2
  have hrange : (θ'.comp J.subtype).range = J.map θ' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eX : ↥((J.map θ').subgroupOf A) ≃* ↥J :=
    ((Subgroup.subgroupOfEquivOfLe hJA).trans (MulEquiv.subgroupCongr hrange.symm)).trans
      (MonoidHom.ofInjective hinjJ).symm
  have hXq : IsQuasisimple ↥((J.map θ').subgroupOf A) :=
    LocalCores.isQuasisimple_of_mulEquiv eX.symm hJq
  have hXc : GorensteinWalter.IsComponentOf ((J.map θ').subgroupOf A) ⊤ :=
    ⟨le_top, hXs.subgroupOf, F3L221.gwIsQuasisimple hXq⟩
  have hmemX : ∀ (j : S) (hj : j ∈ J), (⟨θ' j, hJA ⟨j, hj, rfl⟩⟩ : ↥A) ∈
      (J.map θ').subgroupOf A :=
    fun j hj => ⟨j, hj, rfl⟩
  rcases GorensteinWalter.component_le_or_commutator_eq_bot hXc hMs with hle | hcomm
  ·
    have hMsol : Group.IsSolvable ↥M := F3L221.isSolvable_of_isSolvableTwoComponentIn hM
    have hJM : ∀ j : ↥J, θ' j ∈ M := fun j => hle (hmemX j j.2)
    let ψ : ↥J →* ↥M :=
      { toFun := fun j => ⟨θ' j, hJM j⟩
        map_one' := Subtype.ext (by
          show θ' ((1 : ↥J) : S) = 1
          rw [OneMemClass.coe_one, map_one])
        map_mul' := fun a b => Subtype.ext (by
          show θ' ((a * b : ↥J) : S) = θ' a * θ' b
          rw [Subgroup.coe_mul, map_mul]) }
    have hψ : Function.Injective ψ := fun a b h => hinjJ (by
      have h1 := congrArg Subtype.val h
      exact h1)
    have hJsol : Group.IsSolvable ↥J := Group.isSolvable_of_isSolvable_injective hψ
    have : Nontrivial ↥J := LocalCores.isQuasisimple_nontrivial hJq
    exact not_isSolvable_of_isPerfect hJq.1 hJsol
  ·
    have hjm : ∀ j ∈ J, θ' j * m = m * θ' j := by
      intro j hj
      have h2 := commutator_mem_commutator (hmemX j hj)
        (show (⟨m, hMA hm⟩ : ↥A) ∈ M.subgroupOf A from hm)
      rw [hcomm, mem_bot] at h2
      exact congrArg Subtype.val ((commutatorElement_eq_one_iff_mul_comm).mp h2)
    have hfix := eq_of_comp_eq hJq.1 c.ker_le (f := α.toMonoidHom.comp J.subtype)
      (g := J.subtype) (fun j => by
        apply Subtype.ext
        show ((c.θ (α j) : ↥L) : Q) = ((c.θ j : ↥L) : Q)
        rw [← conj_coe_eq (hMN hm) hα]
        have h1 := hjm j j.2
        calc m * ((c.θ j : ↥L) : Q) * m⁻¹ = (m * θ' j) * m⁻¹ := rfl
          _ = θ' j := by rw [← h1, mul_inv_cancel_right]
          _ = ((c.θ j : ↥L) : Q) := rfl)
    have h3 : α (x * z) = x * z := DFunLike.congr_fun hfix ⟨x * z, hxz⟩
    rw [map_mul, hαx] at h3
    exact hαz (mul_left_cancel h3)

theorem false_of_sl23 (htL : t ∈ L) (hM : IsSolvableTwoComponentIn M (centralizer {t}))
    (hMN : M ≤ normalizer (L : Set Q)) (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* SL(2, ZMod 3))
    {c : Cover S ↥L} (hker : center S ≤ c.θ.ker) {x : S} (hx : c.θ x = ⟨t, htL⟩)
    {m : Q} (hm : m ∈ M) (hmo : Odd (orderOf m)) {α : MulAut S}
    (hα : ∀ g, c.θ (α g) = L.normalizerMonoidHom ⟨m, hMN hm⟩ (c.θ g)) (hαx : α x = x)
    {J₁ J₂ : Subgroup S} (hJx : J₁ ≤ centralizer ({x} : Set S))
    (hJs : (J₁.subgroupOf (centralizer ({x} : Set S))).IsSubnormal) (eJ : ↥J₁ ≃* SL23)
    {z : S} (hz : z ∈ center S) (hxz : x * z ∈ J₁) (hxZ : x ∉ center S)
    (hJ12 : J₁.map α.toMonoidHom = J₂) (hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set θ' : S →* Q := L.subtype.comp c.θ with hθ'
  set A := normalizer (L : Set Q) ⊓ centralizer ({t} : Set Q) with hA
  have hMA : M ≤ A := le_inf hMN hM.1
  have hMs : (M.subgroupOf A).IsSubnormal := F3L226.isSubnormal_subgroupOf_mono inf_le_right hM.2.1
  set U := (CFSG.pCore 2 ↥A).map A.subtype with hU
  have hUA : U ≤ A := map_subtype_le _
  have hAU : A ≤ normalizer (U : Set Q) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨a, ha⟩ * u * ⟨a, ha⟩⁻¹, (CFSG.pCore_normal (p := 2) (G := ↥A)).conj_mem u hu _, rfl⟩
    · rintro ⟨u, hu, hy⟩
      refine ⟨⟨a, ha⟩⁻¹ * u * ⟨a, ha⟩⁻¹⁻¹,
        (CFSG.pCore_normal (p := 2) (G := ↥A)).conj_mem u hu _, ?_⟩
      show a⁻¹ * (u : Q) * a⁻¹⁻¹ = y
      rw [show (u : Q) = a * y * a⁻¹ from hy]
      group
  have hU2 : IsPGroup 2 U := (CFSG.pCore_isPGroup).map _
  have hcommU := F3L225.commutator_zpowers_le_of_isSubnormal hMA hMs hUA hAU hU2 hm hmo
  have hJA : J₁.map θ' ≤ A := by
    rintro _ ⟨j, hj, rfl⟩
    refine mem_inf.mpr ⟨le_normalizer (c.θ j).2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : j * x = x * j := mem_centralizer_singleton_iff.mp (hJx hj)
    have h2 := congrArg (fun g => ((c.θ g : ↥L) : Q)) h1
    simp only [map_mul, Subgroup.coe_mul, hx] at h2
    exact h2
  set Q₁ := (sl23Q8.comap eJ.toMonoidHom).map J₁.subtype with hQ₁
  have hQJ : Q₁ ≤ J₁ := map_subtype_le _
  have hQn : (Q₁.subgroupOf J₁).Normal := by
    rw [hQ₁, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective J₁.subtype_injective]
    exact Subgroup.Normal.comap sl23Q8_normal eJ.toMonoidHom
  have hQs : (Q₁.subgroupOf (centralizer ({x} : Set S))).IsSubnormal :=
    GroupTheory.isSubnormal_subgroupOf_trans hQJ hJx hQn.isSubnormal hJs
  have hQ2 : IsPGroup 2 ↥(Q₁.map θ') := by
    rintro ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩⟩
    refine ⟨2, Subtype.ext ?_⟩
    show θ' (j : S) ^ 2 ^ 2 = 1
    have h1 : eJ (j ^ 4) = 1 := by rw [map_pow]; exact hj
    have h2 : j ^ 4 = 1 := (map_eq_one_iff eJ eJ.injective).mp h1
    rw [← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num, ← Subgroup.coe_pow, h2,
      OneMemClass.coe_one, map_one]
  have hQU : Q₁.map θ' ≤ U := by
    have h1 := isSubnormal_map_of_centralizer htL c.surj c.ker_le hx (hQJ.trans hJx) hQs
    have hQA : Q₁.map θ' ≤ A := (map_mono hQJ).trans hJA
    have h2 : IsPGroup 2 ↥((Q₁.map θ').subgroupOf A) :=
      hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQA).symm
    have h3 := le_pCore_of_isSubnormal h1 h2
    intro y hy
    exact ⟨⟨y, hQA hy⟩, h3 hy, rfl⟩
  have hxzc : (⟨x * z, hxz⟩ : ↥J₁) ∈ center ↥J₁ := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : S) * (x * z) = x * z * g
    have h1 : (g : S) * x = x * g := mem_centralizer_singleton_iff.mp (hJx g.2)
    have h2 := mem_center_iff.mp hz (g : S)
    calc (g : S) * (x * z) = (g * x) * z := by group
      _ = x * (g * z) := by rw [h1]; group
      _ = x * z * g := by rw [h2]; group
  have hxz1 : x * z ≠ 1 := fun h => hxZ (by
    have h1 : x = z⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [h1]
    exact inv_mem hz)
  have hexz : eJ ⟨x * z, hxz⟩ = -1 := by
    have h1 : eJ ⟨x * z, hxz⟩ ∈ center SL23 := (mem_center_mulEquiv_iff eJ _).mpr hxzc
    rcases sl2_center_cases h1 with h | h
    · exact absurd (congrArg Subtype.val ((map_eq_one_iff eJ eJ.injective).mp h)) hxz1
    · exact h
  have hsq : ∀ u : ↥J₁, eJ u ^ 2 = -1 → (u : S) * u = x * z := by
    intro u hu
    have h1 : eJ (u * u) = eJ ⟨x * z, hxz⟩ := by rw [map_mul, ← sq, hu, hexz]
    have h2 := congrArg Subtype.val (eJ.injective h1)
    simpa only [Subgroup.coe_mul] using h2
  have hαJ : ∀ u : ↥J₁, α (u : S) ∈ J₂ := by
    intro u
    have h1 : α (u : S) ∈ J₁.map α.toMonoidHom := ⟨(u : S), u.2, rfl⟩
    rwa [hJ12] at h1
  have hcen : ∀ v : ↥J₁, (v : S) * (α v)⁻¹ ∈ center S → eJ v ^ 2 = 1 := by
    intro v hv
    have hvc : v ∈ center ↥J₁ := by
      rw [mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : S) * v = v * g
      have h1 := mem_center_iff.mp hv (g : S)
      have h2 : (g : S) * α v = α v * g := hcomm g g.2 (α v) (hαJ v)
      calc (g : S) * v = (g : S) * (((v : S) * (α v)⁻¹) * α v) := by group
        _ = ((v : S) * (α v)⁻¹) * ((g : S) * α v) := by rw [← mul_assoc, h1, mul_assoc]
        _ = ((v : S) * (α v)⁻¹) * (α v * g) := by rw [h2]
        _ = v * g := by group
    rcases sl2_center_cases ((mem_center_mulEquiv_iff eJ _).mpr hvc) with h | h
    · rw [h, one_pow]
    · rw [h]
      exact neg_one_sq
  have hw : ∀ u : ↥J₁, (u : S) ∈ Q₁ → eJ u ^ 2 = -1 →
      ⁅((c.θ (u : S) : ↥L) : Q), m⁆ ∈ M ∧ ⁅((c.θ (u : S) : ↥L) : Q), m⁆ ∈ U ∧
        orderOf ⁅((c.θ (u : S) : ↥L) : Q), m⁆ = 2 := by
    intro u huQ hu
    have hθu : ((c.θ (u : S) : ↥L) : Q) ∈ U := hQU ⟨(u : S), huQ, rfl⟩
    have h1 := hcommU (commutator_mem_commutator hθu (mem_zpowers m))
    refine ⟨(mem_inf.mp h1).1, (mem_inf.mp h1).2, ?_⟩
    rw [commutatorElement_coe_eq (hMN hm) hα]
    have hc : Commute (u : S) (α u) := hcomm u u.2 (α u) (hαJ u)
    have hc' : (u : S) * (α u)⁻¹ = (α u)⁻¹ * u := hc.inv_right.eq
    have hbb : α (u : S) * α u = x * α z := by rw [← map_mul, hsq u hu, map_mul, hαx]
    have hzz : z * (α z)⁻¹ ∈ center S := mul_mem hz (inv_mem (Cover.mem_center_map α hz))
    have hsq' : ((u : S) * (α u)⁻¹) * ((u : S) * (α u)⁻¹) = z * (α z)⁻¹ := by
      calc ((u : S) * (α u)⁻¹) * ((u : S) * (α u)⁻¹) = (u : S) * ((α u)⁻¹ * u) * (α u)⁻¹ := by
            group
        _ = (u : S) * ((u : S) * (α u)⁻¹) * (α u)⁻¹ := by rw [← hc']
        _ = ((u : S) * u) * (α (u : S) * α u)⁻¹ := by group
        _ = x * (z * (α z)⁻¹) * x⁻¹ := by rw [hsq u hu, hbb]; group
        _ = z * (α z)⁻¹ := by rw [mem_center_iff.mp hzz x, mul_inv_cancel_right]
    apply orderOf_eq_prime
    · rw [sq, ← Subgroup.coe_mul, ← map_mul, hsq', show c.θ (z * (α z)⁻¹) = 1 from hker hzz,
        OneMemClass.coe_one]
    · intro h
      have h2 : c.θ ((u : S) * (α u)⁻¹) = 1 := Subtype.ext h
      have h3 := hcen u (c.ker_le h2)
      rw [hu] at h3
      exact absurd h3 (by decide)
  obtain ⟨a₀, b₀, ha₀, hb₀, hab₀⟩ := sl23_exists_pair
  have hQ8 : ∀ g : SL23, g ^ 2 = -1 → (eJ.symm g : S) ∈ Q₁ := by
    intro g hg
    refine ⟨eJ.symm g, ?_, rfl⟩
    show eJ.toMonoidHom (eJ.symm g) ^ 4 = 1
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, show (4 : ℕ) = 2 * 2 by norm_num,
      pow_mul, hg]
    exact neg_one_sq
  have hu₁ : eJ (eJ.symm a₀) ^ 2 = -1 := by rw [MulEquiv.apply_symm_apply]; exact ha₀
  have hu₂ : eJ (eJ.symm b₀) ^ 2 = -1 := by rw [MulEquiv.apply_symm_apply]; exact hb₀
  obtain ⟨hw1M, hw1U, hw1⟩ := hw (eJ.symm a₀) (hQ8 a₀ ha₀) hu₁
  obtain ⟨hw2M, hw2U, hw2⟩ := hw (eJ.symm b₀) (hQ8 b₀ hb₀) hu₂
  obtain ⟨k, hk⟩ := hU2 ⟨_, mul_mem hw1U hw2U⟩
  have hk' : (⁅((c.θ (eJ.symm a₀ : S) : ↥L) : Q), m⁆ *
      ⁅((c.θ (eJ.symm b₀ : S) : ↥L) : Q), m⁆) ^ 2 ^ k = 1 := by
    have h1 := congrArg Subtype.val hk
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using h1
  have heq := eq_of_involutions e hw1M hw2M hw1 hw2 hk'
  rw [commutatorElement_coe_eq (hMN hm) hα, commutatorElement_coe_eq (hMN hm) hα] at heq
  have h1 : c.θ ((eJ.symm a₀ : S) * (α (eJ.symm a₀ : S))⁻¹) =
      c.θ ((eJ.symm b₀ : S) * (α (eJ.symm b₀ : S))⁻¹) := Subtype.ext heq
  set u₁ := eJ.symm a₀ with hu₁def
  set u₂ := eJ.symm b₀ with hu₂def
  have h2 : ((u₂ : S) * (α u₂)⁻¹)⁻¹ * ((u₁ : S) * (α u₁)⁻¹) ∈ center S :=
    c.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel])
  have hv : ((u₂⁻¹ * u₁ : ↥J₁) : S) * (α (u₂⁻¹ * u₁ : ↥J₁))⁻¹ ∈ center S := by
    have h3 : ((u₂⁻¹ * u₁ : ↥J₁) : S) * (α (u₂⁻¹ * u₁ : ↥J₁))⁻¹ =
        (α (u₂ : S))⁻¹ * ((((u₂ : S) * (α u₂)⁻¹)⁻¹ * ((u₁ : S) * (α u₁)⁻¹)) * α (u₂ : S)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
      group
    rw [h3, ← mem_center_iff.mp h2 (α (u₂ : S)), inv_mul_cancel_left]
    exact h2
  have h4 := hcen (u₂⁻¹ * u₁) hv
  rw [map_mul, map_inv, hu₂def, hu₁def, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    hab₀] at h4
  exact absurd h4 (by decide)

end F3D4

end CFSG.ComponentClassification.HarrisLit.T1

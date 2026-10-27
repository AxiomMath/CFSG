module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIXi
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoExcHypIIE6SL2
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed

public section

namespace CFSG.ComponentClassification.RankTwoExcHypII

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.RankTwoHypIIY

section Pullback

variable {C : Type*} [Group C]

theorem exists_pullback_of_witness (hZ : center C = ⊥) {ξ : MulAut C}
    {E₀ : Subgroup (MulAut C)} (hab : IsElemAbelian 2 E₀) (hne : E₀ ≠ ⊥)
    (hX : E₀ ≤ OuterAutomorphisms.inner C) (hξ : E₀ ≤ centralizer {ξ})
    (hN : OuterAutomorphisms.inner C ⊓ centralizer {ξ} ≤ normalizer (E₀ : Set (MulAut C)))
    (hcl : ∀ x ∈ E₀, x ≠ 1 → ∀ w ∈ OuterAutomorphisms.inner C ⊓ centralizer {x},
      w * ξ * w⁻¹ * ξ⁻¹ ∈ E₀) :
    ∃ E₁ : Subgroup C, E₁ ≠ ⊥ ∧ (∀ a ∈ E₁, ∀ b ∈ E₁, a * b = b * a) ∧
      (∀ a ∈ E₁, a ^ 2 = 1) ∧ (∀ a ∈ E₁, ξ a = a) ∧
      (∀ c : C, ξ c = c → ∀ a ∈ E₁, c * a * c⁻¹ ∈ E₁) ∧
      ∀ x ∈ E₁, x ≠ 1 → ∀ w : C, w * x = x * w → w * (ξ w)⁻¹ ∈ E₁ := by
  have hinj := conj_injective_of_center_eq_bot hZ
  have hcξ : ∀ g : C, MulAut.conj g ∈ centralizer {ξ} ↔ ξ g = g := by
    intro g
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply hinj
      rw [conj_apply_eq_mul_conj_mul_inv, ← h, mul_inv_cancel_right]
    · intro h
      have e := conj_apply_eq_mul_conj_mul_inv ξ g
      rw [h] at e
      have := congrArg (· * ξ) e
      simpa [mul_assoc] using this
  refine ⟨E₀.comap (MulAut.conj : C →* MulAut C), fun hbot => hne ?_, fun a ha b hb => hinj ?_,
    fun a ha => hinj ?_, fun a ha => (hcξ a).1 (hξ ha), fun c hc a ha => ?_,
    fun x hx hx1 w hw => ?_⟩
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨g, rfl⟩ := hX hy
    have : g ∈ E₀.comap (MulAut.conj : C →* MulAut C) := hy
    rw [hbot, mem_bot] at this
    rw [this, map_one]
    exact one_mem _
  · rw [map_mul, map_mul]
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
  · rw [map_pow, hab.2 _ ha, map_one]
  · have hcN := hN ⟨⟨c, rfl⟩, (hcξ c).2 hc⟩
    change MulAut.conj (c * a * c⁻¹) ∈ E₀
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp hcN _).mp ha
  · have hx1' : MulAut.conj x ≠ 1 := fun h => hx1 (hinj (h.trans (map_one _).symm))
    have hw' : MulAut.conj w ∈ OuterAutomorphisms.inner C ⊓ centralizer {MulAut.conj x} :=
      ⟨⟨w, rfl⟩, mem_centralizer_singleton_iff.mpr (by rw [← map_mul, ← map_mul, hw])⟩
    have h := hcl _ hx hx1' _ hw'
    change MulAut.conj (w * (ξ w)⁻¹) ∈ E₀
    have e : MulAut.conj (w * (ξ w)⁻¹) =
        MulAut.conj w * ξ * (MulAut.conj w)⁻¹ * ξ⁻¹ := by
      rw [map_mul, map_inv, conj_apply_eq_mul_conj_mul_inv]
      group
    rw [e]
    exact h

end Pullback

variable {k : Type} [Field k]

theorem diagramMap_conj_e6Alpha
    (h2 : (2 : k) = 0) (s j : Bool) (c : k) :
    diagramMap TwistTag.E6 k *
        pinnedX TwistTag.E6.tag k (if s then -e6Alpha j else e6Alpha j) c *
        (diagramMap TwistTag.E6 k)⁻¹ =
      pinnedX TwistTag.E6.tag k (if s then -e6Alpha (!j) else e6Alpha (!j)) c := by
  have hρ : permLattice TwistTag.E6.perm (if s then -e6Alpha j else e6Alpha j) =
      (if s then -e6Alpha (!j) else e6Alpha (!j)) := by
    revert s j
    decide
  have hα : IsRoot TwistTag.E6.tag (if s then -e6Alpha j else e6Alpha j) := by
    cases s
    · exact isRoot_e6Alpha j
    · exact isRoot_neg_iff.2 (isRoot_e6Alpha j)
  rw [E6GraphRadical.diagramMap_conj_pinnedX_of_two h2 hα, hρ]

theorem commute_e6Alpha_theta
    (s : Bool) (j : Bool) (c b : k) :
    Commute (pinnedX TwistTag.E6.tag k (if s then -e6Alpha j else e6Alpha j) c)
      (pinnedX TwistTag.E6.tag k e6HighestRoot b) := by
  have key : ∀ s j : Bool, (if s then -e6Alpha j else e6Alpha j) ≠ e6HighestRoot ∧
      (if s then -e6Alpha j else e6Alpha j) ≠ -e6HighestRoot ∧
      e6RootB ((if s then -e6Alpha j else e6Alpha j) + e6HighestRoot) = false := by decide
  obtain ⟨h1, h2, h3⟩ := key s j
  have hα : IsRoot TwistTag.E6.tag (if s then -e6Alpha j else e6Alpha j) := by
    cases s
    · exact isRoot_e6Alpha j
    · exact isRoot_neg_iff.2 (isRoot_e6Alpha j)
  refine (simply_laced_root_commutator_unit TwistTag.E6.tag (.inr (.inl rfl)) hα
    isRoot_e6HighestRoot h1 h2).2 (fun hr => ?_) k _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _
    (mem_rootSubgroup.2 ⟨b, rfl⟩)
  rw [isRoot_iff_e6RootB, h3] at hr
  exact Bool.false_ne_true hr

theorem commute_e6Alpha_pair
    (s : Bool) (c d : k) :
    Commute (pinnedX TwistTag.E6.tag k (if s then -e6Alpha false else e6Alpha false) c)
      (pinnedX TwistTag.E6.tag k (if s then -e6Alpha true else e6Alpha true) d) := by
  obtain ⟨hne, hne', hnr⟩ := e6Alpha_facts s s
  have hα : IsRoot TwistTag.E6.tag (if s then -e6Alpha false else e6Alpha false) := by
    cases s
    · exact isRoot_e6Alpha false
    · exact isRoot_neg_iff.2 (isRoot_e6Alpha false)
  have hβ : IsRoot TwistTag.E6.tag (if s then -e6Alpha true else e6Alpha true) := by
    cases s
    · exact isRoot_e6Alpha true
    · exact isRoot_neg_iff.2 (isRoot_e6Alpha true)
  exact (simply_laced_root_commutator_unit TwistTag.E6.tag (.inr (.inl rfl)) hα hβ hne hne').2
    hnr k _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem diagramMap_conj_e6Alpha'
    (h2 : (2 : k) = 0) (c : k) :
    diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6Alpha false) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6Alpha true) c ∧
      diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (e6Alpha true) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (e6Alpha false) c ∧
      diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (-e6Alpha false) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (-e6Alpha true) c ∧
      diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (-e6Alpha true) c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k (-e6Alpha false) c :=
  ⟨diagramMap_conj_e6Alpha h2 false false c, diagramMap_conj_e6Alpha h2 false true c,
    diagramMap_conj_e6Alpha h2 true false c, diagramMap_conj_e6Alpha h2 true true c⟩

theorem commute_e6Alpha_theta'
    (j : Bool) (c b : k) :
    Commute (pinnedX TwistTag.E6.tag k (e6Alpha j) c) (pinnedX TwistTag.E6.tag k e6HighestRoot b) ∧
      Commute (pinnedX TwistTag.E6.tag k (-e6Alpha j) c)
        (pinnedX TwistTag.E6.tag k e6HighestRoot b) :=
  ⟨commute_e6Alpha_theta false j c b, commute_e6Alpha_theta true j c b⟩

theorem commute_e6Alpha_pair'
    (c d : k) :
    Commute (pinnedX TwistTag.E6.tag k (e6Alpha false) c)
        (pinnedX TwistTag.E6.tag k (e6Alpha true) d) ∧
      Commute (pinnedX TwistTag.E6.tag k (-e6Alpha false) c)
        (pinnedX TwistTag.E6.tag k (-e6Alpha true) d) :=
  ⟨commute_e6Alpha_pair false c d, commute_e6Alpha_pair true c d⟩

theorem permLattice_e6Alpha :
    permLattice TwistTag.E6.perm (e6Alpha false) = e6Alpha true ∧
      permLattice TwistTag.E6.perm (e6Alpha true) = e6Alpha false ∧
      permLattice TwistTag.E6.perm (-e6Alpha false) = -e6Alpha true ∧
      permLattice TwistTag.E6.perm (-e6Alpha true) = -e6Alpha false := by
  decide

theorem conj_theta_diagramMap_pair
    (h2 : (2 : k) = 0) (d d' : k) :
    pinnedX TwistTag.E6.tag k e6HighestRoot 1 * (diagramMap TwistTag.E6 k *
        (pinnedX TwistTag.E6.tag k (e6Alpha false) d *
          pinnedX TwistTag.E6.tag k (e6Alpha true) d') * (diagramMap TwistTag.E6 k)⁻¹) *
        (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹ =
      pinnedX TwistTag.E6.tag k (e6Alpha true) d *
        pinnedX TwistTag.E6.tag k (e6Alpha false) d' := by
  have e : ∀ a b : ModGL TwistTag.E6.tag k, diagramMap TwistTag.E6 k * (a * b) *
      (diagramMap TwistTag.E6 k)⁻¹ = diagramMap TwistTag.E6 k * a * (diagramMap TwistTag.E6 k)⁻¹ *
        (diagramMap TwistTag.E6 k * b * (diagramMap TwistTag.E6 k)⁻¹) := fun a b => by group
  have hc := (commute_e6Alpha_theta' true d 1).1.mul_left (commute_e6Alpha_theta' false d' 1).1
  rw [e, (diagramMap_conj_e6Alpha' h2 d).1, (diagramMap_conj_e6Alpha' h2 d').2.1, ← hc.eq,
    mul_inv_cancel_right]

theorem conj_theta_diagramMap_negPair
    (h2 : (2 : k) = 0) :
    pinnedX TwistTag.E6.tag k e6HighestRoot 1 * (diagramMap TwistTag.E6 k *
        (pinnedX TwistTag.E6.tag k (-e6Alpha false) 1 *
          pinnedX TwistTag.E6.tag k (-e6Alpha true) 1) * (diagramMap TwistTag.E6 k)⁻¹) *
        (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹ =
      pinnedX TwistTag.E6.tag k (-e6Alpha false) 1 *
        pinnedX TwistTag.E6.tag k (-e6Alpha true) 1 := by
  have e : ∀ a b : ModGL TwistTag.E6.tag k, diagramMap TwistTag.E6 k * (a * b) *
      (diagramMap TwistTag.E6 k)⁻¹ = diagramMap TwistTag.E6 k * a * (diagramMap TwistTag.E6 k)⁻¹ *
        (diagramMap TwistTag.E6 k * b * (diagramMap TwistTag.E6 k)⁻¹) := fun a b => by group
  obtain ⟨-, -, h3, h4⟩ := diagramMap_conj_e6Alpha' h2 (1 : k)
  have hc := ((commute_e6Alpha_theta' false (1 : k) 1).2).mul_left
    ((commute_e6Alpha_theta' true (1 : k) 1).2)
  rw [e, h3, h4, ← (commute_e6Alpha_pair' (1 : k) 1).2.eq, ← hc.eq, mul_inv_cancel_right]

theorem e6Alpha_pair_mul_inv
    [CharP k 2] (d d' : k) :
    pinnedX TwistTag.E6.tag k (e6Alpha false) d * pinnedX TwistTag.E6.tag k (e6Alpha true) d' *
        (pinnedX TwistTag.E6.tag k (e6Alpha true) d *
          pinnedX TwistTag.E6.tag k (e6Alpha false) d')⁻¹ =
      pinnedX TwistTag.E6.tag k (e6Alpha false) (d + d') *
        pinnedX TwistTag.E6.tag k (e6Alpha true) (d + d') := by
  have h6 : pinnedX TwistTag.E6.tag k (e6Alpha true) d' *
      pinnedX TwistTag.E6.tag k (e6Alpha true) d = pinnedX TwistTag.E6.tag k (e6Alpha true) d *
        pinnedX TwistTag.E6.tag k (e6Alpha true) d' := by
    rw [← pinnedX_add, ← pinnedX_add, add_comm]
  rw [mul_inv_rev, pinnedX_neg, pinnedX_neg, CharTwo.neg_eq d', CharTwo.neg_eq d, pinnedX_add,
    pinnedX_add]
  calc pinnedX TwistTag.E6.tag k (e6Alpha false) d * pinnedX TwistTag.E6.tag k (e6Alpha true) d' *
        (pinnedX TwistTag.E6.tag k (e6Alpha false) d' *
          pinnedX TwistTag.E6.tag k (e6Alpha true) d) =
      pinnedX TwistTag.E6.tag k (e6Alpha false) d *
        (pinnedX TwistTag.E6.tag k (e6Alpha true) d' *
          pinnedX TwistTag.E6.tag k (e6Alpha false) d') *
        pinnedX TwistTag.E6.tag k (e6Alpha true) d := by simp only [mul_assoc]
    _ = pinnedX TwistTag.E6.tag k (e6Alpha false) d *
        (pinnedX TwistTag.E6.tag k (e6Alpha false) d' *
          pinnedX TwistTag.E6.tag k (e6Alpha true) d') *
        pinnedX TwistTag.E6.tag k (e6Alpha true) d := by
      rw [(commute_e6Alpha_pair' d' d').1.eq]
    _ = pinnedX TwistTag.E6.tag k (e6Alpha false) d *
        pinnedX TwistTag.E6.tag k (e6Alpha false) d' *
        (pinnedX TwistTag.E6.tag k (e6Alpha true) d' *
          pinnedX TwistTag.E6.tag k (e6Alpha true) d) := by simp only [mul_assoc]
    _ = _ := by rw [h6]

theorem secondGraphWitness_of
    [Finite k] [CharP k 2] {C : Subgroup (ModGL TwistTag.E6.tag k)} (hZ : center C = ⊥)
    {ξ : MulAut C}
    (hξ : ∀ g : C, (ξ g : ModGL TwistTag.E6.tag k) = pinnedX TwistTag.E6.tag k e6HighestRoot 1 *
      (diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) *
        (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹)
    (hS : ∀ E₁ : Subgroup C, E₁ ≠ ⊥ → (∀ a ∈ E₁, a ^ 2 = 1) → (∀ a ∈ E₁, ξ a = a) →
      (∀ c : C, ξ c = c → ∀ a ∈ E₁, c * a * c⁻¹ ∈ E₁) →
      ∃ a ∈ E₁, a ≠ 1 ∧ (a : ModGL TwistTag.E6.tag k) ∈ posUnipotent TwistTag.E6.tag k ∧
        ∀ i, (a : ModGL TwistTag.E6.tag k) * e6Test k i = e6Test k i * a)
    {d d' : k} (hd : d + d' ≠ 0)
    (hw : pinnedX TwistTag.E6.tag k (e6Alpha false) d *
      pinnedX TwistTag.E6.tag k (e6Alpha true) d' ∈ C)
    (hy : pinnedX TwistTag.E6.tag k (-e6Alpha false) 1 *
      pinnedX TwistTag.E6.tag k (-e6Alpha true) 1 ∈ C) :
    SecondGraphWitness ξ := by
  intro E₀ hab hne hX hξ₀ hN hcl
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨E₁, hE₁ne, hE₁c, hE₁2, hE₁ξ, hE₁n, hE₁w⟩ :=
    exists_pullback_of_witness hZ hab hne hX hξ₀ hN hcl
  obtain ⟨a, haE, ha1, haU, hT⟩ := hS E₁ hE₁ne hE₁2 hE₁ξ hE₁n
  have h8 := mem_heightSeries_eight_of_commute haU hT
  obtain ⟨w, hw'⟩ : ∃ w : C, (w : ModGL TwistTag.E6.tag k) =
      pinnedX TwistTag.E6.tag k (e6Alpha false) d * pinnedX TwistTag.E6.tag k (e6Alpha true) d' :=
    ⟨⟨_, hw⟩, rfl⟩
  have hwa : w * a = a * w := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hw']
    exact ((commute_e6Alpha_of_mem h8 false d).mul_right
      (commute_e6Alpha_of_mem h8 true d')).eq.symm)
  have hz := hE₁w a haE ha1 w hwa
  obtain ⟨y, hy'⟩ : ∃ y : C, (y : ModGL TwistTag.E6.tag k) =
      pinnedX TwistTag.E6.tag k (-e6Alpha false) 1 * pinnedX TwistTag.E6.tag k (-e6Alpha true) 1 :=
    ⟨⟨_, hy⟩, rfl⟩
  have hyz := hE₁n y (Subtype.ext (by rw [hξ, hy', conj_theta_diagramMap_negPair h2])) _ hz
  have hcomm := congrArg Subtype.val (hE₁c _ hz _ hyz)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcomm
  rw [hξ, hw', conj_theta_diagramMap_pair h2, e6Alpha_pair_mul_inv, hy'] at hcomm
  exact e6Alpha_pair_not_commute hd hcomm

theorem exists_commute_tests_of_le
    [Finite k] [CharP k 2] {E₂ : Subgroup (ModGL TwistTag.E6.tag k)}
    (hJ : E₂ ≤ twistedFixedGroup TwistTag.E6 k (RingHom.id k)) (hne : E₂ ≠ ⊥)
    (h2 : ∀ a ∈ E₂, a ^ 2 = 1)
    (hn : ∀ s ∈ graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k), ∀ a ∈ E₂,
      s * a * s⁻¹ ∈ E₂) :
    ∃ a ∈ E₂, a ≠ 1 ∧ a ∈ posUnipotent TwistTag.E6.tag k ∧
      ∀ i, a * e6Test k i = e6Test k i * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.E6.tag k) := finite_modGL
  have h2' : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [e6_twistedFixedGroup_id_eq_graphFixedRootGroup k] at hJ
  have hP := isPGroup_graphFixedPosUnipotent_subgroupOf (K := k) (t := TwistTag.E6)
    (σ := RingHom.id k) 2
  have hI := not_dvd_index_graphFixedPosUnipotent (K := k) (t := TwistTag.E6)
    (σ := RingHom.id k) 2 Function.surjective_id
  have hE₂ : IsPGroup 2 (E₂.subgroupOf (graphFixedRootGroup TwistTag.E6 k (RingHom.id k))) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact h2 _ (Subgroup.mem_subgroupOf.1 x.2)
  have hnorm : (graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)).subgroupOf
      (graphFixedRootGroup TwistTag.E6 k (RingHom.id k)) ≤
      normalizer ((E₂.subgroupOf (graphFixedRootGroup TwistTag.E6 k (RingHom.id k)) :
        Subgroup _) : Set _) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact Subgroup.mem_subgroupOf.2
        (hn _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy))
    · intro hy
      have h := hn _ (inv_mem (Subgroup.mem_subgroupOf.1 hx)) _ (Subgroup.mem_subgroupOf.1 hy)
      have e : ((x : ModGL TwistTag.E6.tag k))⁻¹ *
          ((x * y * x⁻¹ : graphFixedRootGroup TwistTag.E6 k (RingHom.id k)) :
            ModGL TwistTag.E6.tag k) * ((x : ModGL TwistTag.E6.tag k))⁻¹⁻¹ = y := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rw [e] at h
      exact Subgroup.mem_subgroupOf.2 h
  have hsup := hE₂.to_sup_of_normal_left' (hP.toSylow hI).isPGroup' hnorm
  have hle := sup_eq_right.mp ((hP.toSylow hI).is_maximal' hsup le_sup_right)
  have hES : E₂ ≤ graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k) := by
    intro g hg
    have hmem : (⟨g, hJ hg⟩ : graphFixedRootGroup TwistTag.E6 k (RingHom.id k)) ∈
        E₂.subgroupOf (graphFixedRootGroup TwistTag.E6 k (RingHom.id k)) :=
      Subgroup.mem_subgroupOf.2 hg
    exact Subgroup.mem_subgroupOf.1 (hle hmem)
  have hSp : IsPGroup 2 (graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)) :=
    (isPGroup_posUnipotent 2 TwistTag.E6.tag).to_le inf_le_left
  have : Group.IsNilpotent (graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)) :=
    hSp.isNilpotent
  have hE₃ : (E₂.subgroupOf (graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k))).Normal :=
    ⟨fun n hn' g => Subgroup.mem_subgroupOf.2 (hn _ g.2 _ (Subgroup.mem_subgroupOf.1 hn'))⟩
  have hE₃ne : E₂.subgroupOf (graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro a ha
    have hm : (⟨a, hES ha⟩ : graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)) ∈
        E₂.subgroupOf (graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)) :=
      Subgroup.mem_subgroupOf.2 ha
    rw [hbot, mem_bot] at hm
    have hm' := congrArg Subtype.val hm
    exact mem_bot.2 hm'
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hE₃ne)
  refine ⟨_, Subgroup.mem_subgroupOf.1 x.2.1, fun h => hx1 (Subtype.ext (Subtype.ext h)),
    (x : graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)).2.1, fun i => ?_⟩
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.1 x.2.2
    ⟨e6Test k i, Subgroup.mem_inf.2 ⟨e6Test_mem_posUnipotent i,
      e6Test_mem_twistedFixedGroup h2' i⟩⟩)).symm

theorem map_baseChangeGL_posUnipotent_le
    {K : Type} [Field K] (f : k →+* K) (τ : Tag) :
    (posUnipotent τ k).map (baseChangeGL f) ≤ posUnipotent τ K := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  change baseChangeGL f (pinnedX τ k α c) ∈ posUnipotent τ K
  rw [baseChangeGL_pinnedX]
  exact pinnedX_mem_rootSpan hα (f c)

theorem baseChangeGL_e6Test
    {K : Type} [Field K] (f : k →+* K) (i : Fin TwistTag.E6.tag.rank) :
    baseChangeGL f (e6Test k i) = e6Test K i := by
  unfold e6Test
  split_ifs <;> simp only [map_mul, baseChangeGL_pinnedX, map_one]

theorem exists_commute_tests_of_baseChange
    {K : Type} [Field K] [Algebra k K] [Finite k] [CharP k 2] [CharP K 2]
    {C : Subgroup (ModGL TwistTag.E6.tag K)} (hCa : C ≤ adjointGroup TwistTag.E6.tag K)
    (hι : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)) ≤
      C)
    (hJ : ∀ g ∈ C, diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹ = g →
      g ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map (baseChangeGL (algebraMap k K)))
    {ξ : MulAut C}
    (hξ : ∀ g : C, (ξ g : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
      (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹)
    {E₁ : Subgroup C} (hne : E₁ ≠ ⊥) (h2 : ∀ a ∈ E₁, a ^ 2 = 1) (hfix : ∀ a ∈ E₁, ξ a = a)
    (hn : ∀ c : C, ξ c = c → ∀ a ∈ E₁, c * a * c⁻¹ ∈ E₁) :
    ∃ a ∈ E₁, a ≠ 1 ∧ (a : ModGL TwistTag.E6.tag K) ∈ posUnipotent TwistTag.E6.tag K ∧
      ∀ i, (a : ModGL TwistTag.E6.tag K) * e6Test K i = e6Test K i * a := by
  have hK2 : ringChar K = 2 := ringChar.eq K 2
  have hinj := baseChangeGL_injective (τ := TwistTag.E6.tag) (algebraMap k K)
  have hE₁ι : ∀ a ∈ E₁, ∃ g ∈ twistedFixedGroup TwistTag.E6 k (RingHom.id k),
      baseChangeGL (algebraMap k K) g = a := by
    intro a ha
    have h := hξ a
    rw [hfix a ha] at h
    exact Subgroup.mem_map.1
      (hJ _ a.2 (E6SecondGraphFixed.diagramMap_conj_eq_of_conj hK2 (hCa a.2) h.symm))
  have hSC : ∀ s ∈ graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k),
      baseChangeGL (algebraMap k K) s ∈ C := fun s hs => hι (Subgroup.mem_map_of_mem _ hs.2)
  have hSξ : ∀ s (hs : s ∈ graphFixedPosUnipotent TwistTag.E6 k (RingHom.id k)),
      ξ ⟨_, hSC s hs⟩ = ⟨_, hSC s hs⟩ := by
    intro s hs
    apply Subtype.ext
    rw [hξ]
    have hsU : baseChangeGL (algebraMap k K) s ∈ posUnipotent TwistTag.E6.tag K :=
      map_baseChangeGL_posUnipotent_le _ _ (Subgroup.mem_map_of_mem _ hs.1)
    have hPs : diagramMap TwistTag.E6 K * baseChangeGL (algebraMap k K) s =
        baseChangeGL (algebraMap k K) s * diagramMap TwistTag.E6 K := by
      have := congrArg (baseChangeGL (algebraMap k K)) (mem_twistedFixedGroup_id_iff.1 hs.2).2
      rwa [map_mul, map_mul, baseChangeGL_diagramMap] at this
    change pinnedX TwistTag.E6.tag K e6HighestRoot 1 * (diagramMap TwistTag.E6 K *
      baseChangeGL (algebraMap k K) s * (diagramMap TwistTag.E6 K)⁻¹) *
        (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ = baseChangeGL (algebraMap k K) s
    rw [mul_inv_eq_of_eq_mul hPs, ← (commute_e6HighestRoot_of_mem_posUnipotent K hsU 1).eq,
      mul_inv_cancel_right]
  obtain ⟨a₀, ha₀, ha₀1, ha₀U, hT⟩ := exists_commute_tests_of_le
    (E₂ := (E₁.map C.subtype).comap (baseChangeGL (algebraMap k K)))
    (fun g hg => by
      obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hg)
      obtain ⟨g', hg', hg'a⟩ := hE₁ι a ha
      rwa [hinj (hg'a.trans hag)] at hg')
    (fun hbot => hne (by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨g, -, hga⟩ := hE₁ι a ha
      have hg : g ∈ (E₁.map C.subtype).comap (baseChangeGL (algebraMap k K)) :=
        Subgroup.mem_comap.2 (hga ▸ Subgroup.mem_map_of_mem _ ha)
      rw [hbot, mem_bot] at hg
      rw [hg, map_one] at hga
      exact mem_bot.2 (Subtype.ext hga.symm)))
    (fun g hg => by
      obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hg)
      apply hinj
      rw [map_pow, map_one, ← hag, ← map_pow, h2 a ha, map_one])
    (fun s hs g hg => by
      obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hg)
      refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨_, hn _ (hSξ s hs) a ha, ?_⟩)
      rw [map_mul, map_mul, map_inv, hag, map_mul, map_mul, map_inv]
      rfl)
  obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 ha₀)
  refine ⟨a, ha, fun h => ha₀1 (hinj ?_), ?_, fun i => ?_⟩
  · rw [map_one, ← hag, h, map_one]
  · change C.subtype a ∈ _
    rw [hag]
    exact map_baseChangeGL_posUnipotent_le _ _ (Subgroup.mem_map_of_mem _ ha₀U)
  · change C.subtype a * _ = _ * C.subtype a
    rw [hag, ← baseChangeGL_e6Test (algebraMap k K), ← map_mul, ← map_mul, hT i]

@[expose] noncomputable def e6Xi
    (k : Type) [Field k]
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k) :
    MulAut (adjointGroup TwistTag.E6.tag k) :=
  MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag k) * diagramConjAut TwistTag.E6 k

theorem coe_e6Xi
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
    (g : adjointGroup TwistTag.E6.tag k) :
    ((e6Xi k ht g : adjointGroup TwistTag.E6.tag k) : ModGL TwistTag.E6.tag k) =
      pinnedX TwistTag.E6.tag k e6HighestRoot 1 *
        (diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) *
          (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹ := by
  rw [e6Xi, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, coe_diagramConjAut]

theorem secondGraphWitness_E6
    {f : ℕ} (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k) :
    SecondGraphWitness (e6Xi k ht) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two hf hk
  have hι : ∀ H : Subgroup (ModGL TwistTag.E6.tag k), H.map (baseChangeGL (algebraMap k k)) = H :=
    fun H => by rw [Algebra.algebraMap_self, map_baseChangeGL_id]
  have hιC : (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
      (baseChangeGL (algebraMap k k)) ≤ adjointGroup TwistTag.E6.tag k := by
    rw [hι]
    exact inf_le_left
  have hJ : ∀ g ∈ adjointGroup TwistTag.E6.tag k,
      diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹ = g →
        g ∈ (twistedFixedGroup TwistTag.E6 k (RingHom.id k)).map
          (baseChangeGL (algebraMap k k)) := fun g hg hP => by
    rw [hι]
    exact mem_twistedFixedGroup_id_iff.2 ⟨hg, mul_inv_eq_iff_eq_mul.1 hP⟩
  exact secondGraphWitness_of center_adjointGroup_eq_bot (coe_e6Xi ht)
    (fun E₁ hne h2 hfix hn =>
      exists_commute_tests_of_baseChange le_rfl hιC hJ (coe_e6Xi ht) hne h2 hfix hn)
    (d := 1) (d' := 0) (by rw [add_zero]; exact one_ne_zero)
    (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
    (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))

end CFSG.ComponentClassification.RankTwoExcHypII

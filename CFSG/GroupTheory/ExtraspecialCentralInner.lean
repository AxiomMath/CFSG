module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.FixedCosetCommutator
import CFSG.Foundations.MaxCardThompson
import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralAutomorphismInner

public section

namespace CFSG.GroupTheory

open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialOddQuotientAutFaithfulness
  (quotientHom quotientHom_mk)
open CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialTwoCentralAutomorphismInner
  (exists_inner)
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutator_eq_inf_centralizer_of_isExtraspecial {Q : Subgroup G}
    (hQ : CFSG.IsExtraspecialPGroup 2 ↥Q) :
    ⁅Q, Q⁆ = Q ⊓ Subgroup.centralizer (Q : Set G) := by
  rw [← Q.map_subtype_commutator, hQ.2.1]
  exact CFSG.center_map_subtype_eq_inf_centralizer Q

private lemma commutatorElement_mem_centralizer_of_commute_normalizer {Q : Subgroup G}
    {a l : G} (ha : ∀ q ∈ Q, a * q = q * a)
    (hl : l ∈ Subgroup.normalizer (Q : Set G)) :
    ⁅a, l⁆ ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hq' : l⁻¹ * q * l ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (Q : Set G)).inv_mem hl) q).mp hq
  have hqa : Commute q a := (ha q hq).symm
  have hqh : Commute q (l * a * l⁻¹) := by
    rw [commute_iff_eq]
    calc q * (l * a * l⁻¹) = l * ((l⁻¹ * q * l) * a) * l⁻¹ := by group
      _ = l * (a * (l⁻¹ * q * l)) * l⁻¹ := by rw [ha _ hq']
      _ = (l * a * l⁻¹) * q := by group
  rw [commutatorElement_def,
    show a * l * a⁻¹ * l⁻¹ = a * (l * a * l⁻¹)⁻¹ by group]
  exact (hqa.mul_right hqh.inv_right).eq

private theorem commutator_le_centralizer_of_mem_inf_centralizer {L Q : Subgroup G} {a : G}
    (hZL : ∀ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G), ∀ l ∈ L, z * l = l * z)
    (hmemZ : ∀ l ∈ L, ⁅a, l⁆ ∈ Q ⊓ Subgroup.centralizer (Q : Set G)) :
    ⁅L, L⁆ ≤ Subgroup.centralizer ({a} : Set G) := by
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  let ℓ : L →* Z :=
    { toFun := fun l => ⟨⁅a, (l : G)⁆, hmemZ l l.2⟩
      map_one' := Subtype.ext (by
        change ⁅a, ((1 : L) : G)⁆ = 1
        rw [Subgroup.coe_one, commutatorElement_one_right])
      map_mul' := fun l m => Subtype.ext (by
        change ⁅a, ((l : G) * (m : G))⁆ = ⁅a, (l : G)⁆ * ⁅a, (m : G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hz : ⁅a, (m : G)⁆ ∈ Z := hmemZ m m.2
        have hc := hZL _ hz l l.2
        calc ⁅a, (l : G)⁆ * (l : G) * ⁅a, (m : G)⁆ * (l : G)⁻¹
            = ⁅a, (l : G)⁆ * ((l : G) * ⁅a, (m : G)⁆) * (l : G)⁻¹ := by group
          _ = ⁅a, (l : G)⁆ * (⁅a, (m : G)⁆ * (l : G)) * (l : G)⁻¹ := by rw [hc]
          _ = ⁅a, (l : G)⁆ * ⁅a, (m : G)⁆ := by group) }
  have hcommL : ∀ l ∈ L, ∀ m ∈ L, ⁅a, ⁅l, m⁆⁆ = 1 := by
    intro l hl m hm
    have h1 : ℓ ⟨⁅l, m⁆, Subgroup.commutator_le_of_le (le_refl L) (le_refl L)
        (Subgroup.commutator_mem_commutator hl hm)⟩ =
        ⁅ℓ ⟨l, hl⟩, ℓ ⟨m, hm⟩⁆ :=
      map_commutatorElement ℓ (g₁ := ⟨l, hl⟩) (g₂ := ⟨m, hm⟩)
    have h2 : ⁅ℓ ⟨l, hl⟩, ℓ ⟨m, hm⟩⁆ = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_one]
      exact commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 (hmemZ m hm).2 (ℓ ⟨l, hl⟩ : G) (hmemZ l hl).1)
    have h3 := congrArg Subtype.val (h1.trans h2)
    exact h3
  rw [Subgroup.commutator_le]
  intro l hl m hm
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst h
  exact commutatorElement_eq_one_iff_mul_comm.1 (hcommL l hl m hm)

private theorem mem_of_mem_B_of_centralizer_of_action_on_E₁ {B E₁ L Q T : Subgroup G} {a : G}
    (hZL : ∀ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G), ∀ l ∈ L, z * l = l * z)
    (hTL : T ≤ L)
    (hZT : T ⊓ Subgroup.centralizer (T : Set G) ≤ Q ⊓ Subgroup.centralizer (Q : Set G))
    (hQB : Q ≤ B)
    (hT3 : ∀ x ∈ B, (∀ t ∈ T, x * t = t * x) →
      ∃ z ∈ T ⊓ Subgroup.centralizer (T : Set G), ∀ y ∈ E₁, x * y * x⁻¹ = z * y * z⁻¹)
    (hcore : ∀ x ∈ B, (∀ y ∈ E₁, x * y = y * x) → (∀ y ∈ L, x * y = y * x) → x = 1)
    (haB : a ∈ B) (haL : ∀ l ∈ L, a * l = l * a) :
    a ∈ Q := by
  obtain ⟨z, hzT, hzE⟩ := hT3 a haB (fun t ht => haL t (hTL ht))
  have hzZ : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZT hzT
  have hzQ : z ∈ Q := hzZ.1
  have hzL : ∀ l ∈ L, z * l = l * z := fun l hl => hZL z hzZ l hl
  have hx0B : z⁻¹ * a ∈ B := B.mul_mem (B.inv_mem (hQB hzQ)) haB
  have hx0E : ∀ y ∈ E₁, (z⁻¹ * a) * y = y * (z⁻¹ * a) := by
    intro y hy
    have h := hzE y hy
    calc (z⁻¹ * a) * y = z⁻¹ * (a * y * a⁻¹) * a := by group
      _ = z⁻¹ * (z * y * z⁻¹) * a := by rw [h]
      _ = y * (z⁻¹ * a) := by group
  have hx0L : ∀ l ∈ L, (z⁻¹ * a) * l = l * (z⁻¹ * a) := by
    intro l hl
    have h1 : Commute z l := hzL l hl
    have h2 : Commute a l := haL l hl
    calc (z⁻¹ * a) * l = z⁻¹ * (a * l) := by group
      _ = z⁻¹ * (l * a) := by rw [h2.eq]
      _ = (z⁻¹ * l) * a := by group
      _ = (l * z⁻¹) * a := by rw [h1.inv_left.eq]
      _ = l * (z⁻¹ * a) := by group
  have hx0 : z⁻¹ * a = 1 := hcore (z⁻¹ * a) hx0B hx0E hx0L
  have haz : a = z := by
    calc a = z * (z⁻¹ * a) := by group
      _ = z * 1 := by rw [hx0]
      _ = z := by rw [mul_one]
  rw [haz]
  exact hzQ

theorem mem_of_commutatorElement_mem_of_isExtraspecial [Finite G]
    {B E₁ L Q T : Subgroup G} {c : G}
    (hQ : CFSG.IsExtraspecialPGroup 2 ↥Q) (hLQ : L ≤ Subgroup.normalizer (Q : Set G))
    (hirr : ∀ W : Subgroup G, Q ⊓ Subgroup.centralizer (Q : Set G) ≤ W → W ≤ Q →
      L ≤ Subgroup.normalizer (W : Set G) →
        W = Q ⊓ Subgroup.centralizer (Q : Set G) ∨ W = Q)
    (hperf : L ≤ ⁅L, L⁆ ⊔ Q)
    (hZL : ∀ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G), ∀ l ∈ L, z * l = l * z)
    (hTL : T ≤ L)
    (hZT : T ⊓ Subgroup.centralizer (T : Set G) ≤ Q ⊓ Subgroup.centralizer (Q : Set G))
    (hQB : Q ≤ B)
    (hT3 : ∀ x ∈ B, (∀ t ∈ T, x * t = t * x) →
      ∃ z ∈ T ⊓ Subgroup.centralizer (T : Set G), ∀ y ∈ E₁, x * y * x⁻¹ = z * y * z⁻¹)
    (hcore : ∀ x ∈ B, (∀ y ∈ E₁, x * y = y * x) → (∀ y ∈ L, x * y = y * x) → x = 1)
    (hc2 : ∃ m : ℕ, c ^ 2 ^ m = 1) (hcB : c ∈ B)
    (hcQ : c ∈ Subgroup.normalizer (Q : Set G)) (hcL : ∀ l ∈ L, ⁅c, l⁆ ∈ Q) : c ∈ Q := by
  let Z : Subgroup G := Q ⊓ Subgroup.centralizer (Q : Set G)
  have hZdef : Z = Q ⊓ Subgroup.centralizer (Q : Set G) := rfl
  have hcomm : ⁅Q, Q⁆ = Z := by
    rw [hZdef]
    exact commutator_eq_inf_centralizer_of_isExtraspecial hQ
  have hNC : Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _)
  have hNZ : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    intro x hx
    rw [hZdef]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hx, hNC hx⟩
  have hLZ : L ≤ Subgroup.normalizer (Z : Set G) := hLQ.trans hNZ
  have hcZ : c ∈ Subgroup.normalizer (Z : Set G) := hNZ hcQ
  have hcq : ∀ q ∈ Q, ⁅c, q⁆ ∈ Z := by
    intro q hq
    rw [hZdef]
    exact commutatorElement_mem_of_irreducible (K₀ := Z) hQ.1 inf_le_left hcomm.le hLQ hLZ
      hirr hc2 hcQ hcZ hcL q hq
  obtain ⟨w, hwQ, hw⟩ : ∃ w ∈ Q, ∀ q ∈ Q, c * q * c⁻¹ = w * q * w⁻¹ := by
    have hα : quotientHom ↥Q (Q.normalizerMonoidHom ⟨c, hcQ⟩) = 1 := by
      ext x
      induction x using QuotientGroup.induction_on with
      | H q =>
        rw [quotientHom_mk, MulAut.one_apply, QuotientGroup.eq,
          ← Subgroup.mem_map_iff_mem Q.subtype_injective,
          CFSG.center_map_subtype_eq_inf_centralizer]
        convert hcq _ (Q.inv_mem q.2) using 1
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
          Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def]
        group
    obtain ⟨x, hx⟩ := exists_inner hQ _ hα
    refine ⟨x, x.2, fun q hq => ?_⟩
    simpa using congrArg Subtype.val (DFunLike.congr_fun hx ⟨q, hq⟩)
  set a : G := w⁻¹ * c with ha
  have ha_comm : ∀ q ∈ Q, a * q = q * a := by
    intro q hq
    rw [ha]
    calc w⁻¹ * c * q = w⁻¹ * (c * q * c⁻¹) * c := by group
      _ = w⁻¹ * (w * q * w⁻¹) * c := by rw [hw q hq]
      _ = q * (w⁻¹ * c) := by group
  have hmemQ : ∀ l ∈ L, ⁅a, l⁆ ∈ Q := by
    intro l hl
    have hform : ⁅a, l⁆ = w⁻¹ * ⁅c, l⁆ * (l * w * l⁻¹) := by
      rw [ha]
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact Q.mul_mem (Q.mul_mem (Q.inv_mem hwQ) (hcL l hl))
      ((Subgroup.mem_normalizer_iff.1 (hLQ hl) w).mp hwQ)
  have hcent : ∀ l ∈ L, ⁅a, l⁆ ∈ Subgroup.centralizer (Q : Set G) :=
    fun l hl => commutatorElement_mem_centralizer_of_commute_normalizer ha_comm (hLQ hl)
  have hmemZ : ∀ l ∈ L, ⁅a, l⁆ ∈ Z := by
    intro l hl
    rw [hZdef]
    exact ⟨hmemQ l hl, hcent l hl⟩
  have hLL : ⁅L, L⁆ ≤ Subgroup.centralizer ({a} : Set G) :=
    commutator_le_centralizer_of_mem_inf_centralizer hZL hmemZ
  have hQcent : Q ≤ Subgroup.centralizer ({a} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact ha_comm q hq
  have hLcent : L ≤ Subgroup.centralizer ({a} : Set G) := hperf.trans (sup_le hLL hQcent)
  have haL : ∀ l ∈ L, a * l = l * a := fun l hl =>
    Subgroup.mem_centralizer_iff.1 (hLcent hl) a (Set.mem_singleton a)
  have haB : a ∈ B := by
    rw [ha]
    exact B.mul_mem (B.inv_mem (hQB hwQ)) hcB
  have haQ : a ∈ Q :=
    mem_of_mem_B_of_centralizer_of_action_on_E₁ hZL hTL hZT hQB hT3 hcore haB haL
  rw [show c = w * a by rw [ha]; group]
  exact Q.mul_mem hwQ haQ

end CFSG.GroupTheory

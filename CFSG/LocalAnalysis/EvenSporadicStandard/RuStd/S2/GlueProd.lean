module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueCen

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

abbrev CenL (L : Subgroup G) {a : G} (ha : a ∈ L) : Type :=
  ↥(centralizer ({(⟨a, ha⟩ : L)} : Set L))

theorem t_mem_cen (hc : Config G L t) {a : G} (ha : a ∈ L) :
    t ∈ centralizer ({a} : Set G) :=
  mem_centralizer_singleton_iff.2 (hc.comm a ha).symm

@[expose] def tCen (hc : Config G L t) {a : G} (ha : a ∈ L) : CenG a := ⟨t, t_mem_cen hc ha⟩

abbrev CenT (hc : Config G L t) {a : G} (ha : a ∈ L) : Type :=
  ↥(centralizer ({tCen hc ha} : Set (CenG a)))

theorem zpowers_comm_t {z : G} (hz : z ∈ zpowers t) : z * t = t * z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  exact (Commute.zpow_left (Commute.refl t) k).eq

theorem mul_mem_cenG (hc : Config G L t) {a : G} (ha : a ∈ L) (m : CenL L ha)
    (z : ↥(zpowers t)) : ((m : L) : G) * (z : G) ∈ centralizer ({a} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  have h1 : ((m : L) : G) * a = a * ((m : L) : G) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.1 m.2)
  have h2 : (z : G) * a = a * (z : G) := (comm_zpowers hc ha z.2).symm
  calc ((m : L) : G) * (z : G) * a = ((m : L) : G) * ((z : G) * a) := mul_assoc _ _ _
    _ = ((m : L) : G) * (a * (z : G)) := by rw [h2]
    _ = (((m : L) : G) * a) * (z : G) := (mul_assoc _ _ _).symm
    _ = (a * ((m : L) : G)) * (z : G) := by rw [h1]
    _ = a * (((m : L) : G) * (z : G)) := mul_assoc _ _ _

theorem mul_comm_t (hc : Config G L t) (m : L) (z : ↥(zpowers t)) :
    (m : G) * (z : G) * t = t * ((m : G) * (z : G)) := by
  have h1 : (m : G) * t = t * (m : G) := hc.comm m m.2
  have h2 : (z : G) * t = t * (z : G) := zpowers_comm_t z.2
  calc (m : G) * (z : G) * t = (m : G) * ((z : G) * t) := mul_assoc _ _ _
    _ = (m : G) * (t * (z : G)) := by rw [h2]
    _ = ((m : G) * t) * (z : G) := (mul_assoc _ _ _).symm
    _ = (t * (m : G)) * (z : G) := by rw [h1]
    _ = t * ((m : G) * (z : G)) := mul_assoc _ _ _

@[expose] noncomputable def cenMul (hc : Config G L t) {a : G} (ha : a ∈ L) :
    CenL L ha × ↥(zpowers t) →* CenT hc ha where
  toFun p := ⟨⟨((p.1 : L) : G) * (p.2 : G), mul_mem_cenG hc ha p.1 p.2⟩,
    mem_centralizer_singleton_iff.2 (Subtype.ext (mul_comm_t hc _ _))⟩
  map_one' := Subtype.ext (Subtype.ext (by simp))
  map_mul' p q := by
    refine Subtype.ext (Subtype.ext ?_)
    have h : ((p.2 : ↥(zpowers t)) : G) * (((q.1 : CenL L ha) : L) : G) =
        (((q.1 : CenL L ha) : L) : G) * ((p.2 : ↥(zpowers t)) : G) :=
      (comm_zpowers hc (q.1 : L).2 p.2.2).symm
    show (((p.1 * q.1 : CenL L ha) : L) : G) * ((p.2 * q.2 : ↥(zpowers t)) : G) =
      (((p.1 : L) : G) * (p.2 : G)) * ((((q.1 : L) : G)) * (q.2 : G))
    calc (((p.1 * q.1 : CenL L ha) : L) : G) * ((p.2 * q.2 : ↥(zpowers t)) : G)
        = ((p.1 : L) : G) * (((q.1 : L) : G) * ((p.2 : G) * (q.2 : G))) := by
          simp only [mul_assoc, Subgroup.coe_mul]
      _ = ((p.1 : L) : G) * ((p.2 : G) * ((q.1 : L) : G)) * (q.2 : G) := by
          rw [h]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]

theorem cenMul_apply (hc : Config G L t) {a : G} (ha : a ∈ L) (p : CenL L ha × ↥(zpowers t)) :
    (((cenMul hc ha p : CenT hc ha) : CenG a) : G) = ((p.1 : L) : G) * (p.2 : G) := rfl

theorem cenMul_injective (hc : Config G L t) {a : G} (ha : a ∈ L) :
    Function.Injective (cenMul hc ha) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨m, z⟩ h
  have h1 : ((m : L) : G) * (z : G) = 1 := by
    have := congrArg (fun x : CenT hc ha => (((x : CenG a) : G))) h
    simpa [cenMul_apply] using this
  have hz : (z : G) = ((m : L) : G)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hz1 : (z : G) = 1 :=
    Subgroup.disjoint_def.1 hc.disjoint (by rw [hz]; exact inv_mem (m : L).2) z.2
  have hm1 : ((m : L) : G) = 1 := by rw [hz1, mul_one] at h1; exact h1
  refine Prod.ext (Subtype.ext (Subtype.ext hm1)) (Subtype.ext hz1)

theorem cenMul_surjective (hc : Config G L t) {a : G} (ha : a ∈ L) :
    Function.Surjective (cenMul hc ha) := by
  rintro ⟨⟨x, hxa⟩, hxt⟩
  have hxt' : x * t = t * x := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hxt)
  have hxa' : x * a = a * x := mem_centralizer_singleton_iff.1 hxa
  rcases hc.mem_cases (mem_centralizer_singleton_iff.2 hxt') with hxL | ⟨l, hl, rfl⟩
  · refine ⟨(⟨⟨x, hxL⟩, mem_centralizer_singleton_iff.2 (Subtype.ext hxa')⟩, 1), ?_⟩
    exact Subtype.ext (Subtype.ext (by simp [cenMul_apply]))
  · have hla : l * a = a * l := by
      apply mul_left_cancel (a := t)
      calc t * (l * a) = (t * l) * a := (mul_assoc _ _ _).symm
        _ = a * (t * l) := hxa'
        _ = (a * t) * l := (mul_assoc _ _ _).symm
        _ = (t * a) * l := by rw [hc.comm a ha]
        _ = t * (a * l) := mul_assoc _ _ _
    refine ⟨(⟨⟨l, hl⟩, mem_centralizer_singleton_iff.2 (Subtype.ext hla)⟩,
      ⟨t, mem_zpowers t⟩), ?_⟩
    exact Subtype.ext (Subtype.ext (by simp [cenMul_apply, hc.comm l hl]))

theorem cenMul_bijective (hc : Config G L t) {a : G} (ha : a ∈ L) :
    Function.Bijective (cenMul hc ha) :=
  ⟨cenMul_injective hc ha, cenMul_surjective hc ha⟩

@[expose] noncomputable def cenEquiv (hc : Config G L t) {a : G} (ha : a ∈ L) :
    CenT hc ha ≃* CenL L ha × ↥(zpowers t) :=
  (MulEquiv.ofBijective (cenMul hc ha) (cenMul_bijective hc ha)).symm

theorem cenEquiv_symm_apply (hc : Config G L t) {a : G} (ha : a ∈ L)
    (p : CenL L ha × ↥(zpowers t)) : (cenEquiv hc ha).symm p = cenMul hc ha p := rfl

theorem cenMul_cenEquiv (hc : Config G L t) {a : G} (ha : a ∈ L) (x : CenT hc ha) :
    cenMul hc ha (cenEquiv hc ha x) = x := by
  rw [← cenEquiv_symm_apply, MulEquiv.symm_apply_apply]

theorem card_cenT (hc : Config G L t) {a : G} (ha : a ∈ L) :
    Nat.card (CenT hc ha) = 2 * Nat.card (CenL L ha) := by
  rw [Nat.card_congr (cenEquiv hc ha).toEquiv, Nat.card_prod, Nat.card_zpowers, hc.orderOf_z,
    mul_comm]

noncomputable def zpowersEquivZMod {t : G} (ht : orderOf t = 2) :
    ↥(zpowers t) ≃* Multiplicative (ZMod 2) := by
  have hc : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers, ht]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (zmodCyclicMulEquiv (inferInstance : IsCyclic (zpowers t))).symm.trans
    (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hc).toAddEquiv)

end CFSG.EvenSporadicStandard.RuStd.S2.Glue

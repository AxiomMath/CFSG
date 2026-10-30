module

public import CFSG.GF2Type.CenterFour.CaseAOneClass
public import CFSG.GF2Type.CenterFour.BasicIndex

public section

namespace CFSG.GF2Type.CenterFour

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {n : ℕ}

private theorem orderOf_conj' (z g : G) : orderOf (g⁻¹ * z * g) = orderOf z := by
  have h3 := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulEquiv.injective _) z
  simpa [MulAut.conj_apply] using h3

private theorem involution_of_mem {z : G} {n : ℕ} (hC : Config z n) {b : G}
    (hb : Fused z b) : b ^ 2 = 1 ∧ b ≠ 1 := by
  obtain ⟨g, rfl⟩ := hb
  have hord : orderOf (g⁻¹ * z * g) = 2 := by
    rw [orderOf_conj', hC.orderOf_eq]
  refine ⟨?_, ?_⟩
  · rw [← hord]
    exact pow_orderOf_eq_one _
  · intro h
    rw [h, orderOf_one] at hord
    norm_num at hord

private theorem not_mem_center_of_fused {z : G} {n : ℕ} (hC : Config z n) {b : G}
    (hb : Fused z b) (hb1 : b ≠ z) : b ∉ centerAt z := by
  intro hmem
  apply hb1
  obtain ⟨g, rfl⟩ := hb
  apply hC.eq_of_mem_center hmem
  rw [orderOf_conj', hC.orderOf_eq]

private theorem mul_z_mem_F {z : G} {n : ℕ} (hC : Config z n) {b : G}
    (hb : Fused z b) (hbQ : b ∈ coreAt z) (hb1 : b ≠ z) :
    Fused z (b * z) ∧ b * z ∈ coreAt z ∧ b * z ≠ z := by
  obtain ⟨hb2, hbne1⟩ := involution_of_mem hC hb
  have hbZ := not_mem_center_of_fused hC hb hb1
  refine ⟨?_, (coreAt z).mul_mem hbQ hC.mem_core, ?_⟩
  · obtain ⟨q, hq, hqe⟩ := hC.exists_conj_eq_mul hbQ hb2 hbZ
    obtain ⟨g, hg⟩ := hb
    exact ⟨g * q, by rw [← hqe, ← hg]; group⟩
  · intro h
    apply hbne1
    have hb' : b * z * z⁻¹ = z * z⁻¹ := by rw [h]
    simpa using hb'

private def FSet (G : Type) [Group G] (z : G) : Set G :=
  {w : G | Fused z w ∧ w ∈ coreAt z ∧ w ≠ z}

private theorem mem_FSet {z w : G} : w ∈ FSet G z ↔ Fused z w ∧ w ∈ coreAt z ∧ w ≠ z :=
  Iff.rfl

private noncomputable def idxG (G : Type) [Group G] [Finite G] (g : G) : ℕ :=
  (Finite.equivFin G g : ℕ)

private theorem idxG_injective (G : Type) [Group G] [Finite G] :
    Function.Injective (idxG G) := by
  intro a b h
  exact (Finite.equivFin G).injective (Fin.ext h)

private def PairSet (G : Type) [Group G] [Finite G] (z : G) : Set G :=
  {t : G | t ∈ FSet G z ∧ idxG G t < idxG G (t * z)}

private theorem mem_PairSet {z t : G} :
    t ∈ PairSet G z ↔ (Fused z t ∧ t ∈ coreAt z ∧ t ≠ z) ∧ idxG G t < idxG G (t * z) :=
  Iff.rfl

private theorem z_mul_z {z : G} {n : ℕ} (hC : Config z n) (w : G) : w * z * z = w := by
  have hz2 : z ^ 2 = 1 := by
    rw [← hC.orderOf_eq]
    exact pow_orderOf_eq_one z
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  rw [mul_assoc, hzz, mul_one]

private theorem FSet_subset_pairSet {z : G} {n : ℕ} (hC : Config z n) :
    FSet G z ⊆ PairSet G z ∪ (fun t => t * z) '' PairSet G z := by
  intro b hb
  rw [mem_FSet] at hb
  obtain ⟨hbz_F, hbzQ, hbzne⟩ := mul_z_mem_F hC hb.1 hb.2.1 hb.2.2
  have hbF : b ∈ FSet G z := mem_FSet.2 hb
  have hbzF : b * z ∈ FSet G z := mem_FSet.2 ⟨hbz_F, hbzQ, hbzne⟩
  have hne : idxG G b ≠ idxG G (b * z) := by
    intro h
    have h1 : b * z = b * 1 := by
      rw [mul_one]
      exact (idxG_injective G h).symm
    have hz1 : z = 1 := mul_left_cancel h1
    have h2 := hC.orderOf_eq
    rw [hz1, orderOf_one] at h2
    norm_num at h2
  rcases lt_or_gt_of_ne hne with h | h
  · exact Set.mem_union_left _ (mem_PairSet.2 ⟨mem_FSet.1 hbF, h⟩)
  · refine Set.mem_union_right _ ⟨b * z, mem_PairSet.2 ⟨mem_FSet.1 hbzF, ?_⟩, z_mul_z hC b⟩
    rw [z_mul_z hC b]
    exact h

private theorem CaseA.exists_partner {z : G} {n : ℕ} (hC : Config z n) (hA : CaseA z) {a x b : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a)
    (hb : Fused z b) (hbQ : b ∈ coreAt z) (hbz : b ≠ z) :
    ∃ c, Fused z c ∧ c ∈ coreAt z ∧ c ≠ z ∧ b * c ≠ c * b := by
  by_contra hcon
  push Not at hcon
  have hba : b * a = a * b := hcon a ha haQ haz
  have hbx : b * x = x * b := hcon x hx hxQ hxz
  exact hax (CaseA.commute_of_commute hC hA hb hbQ hbz ha haQ hx hxQ hba hbx)

private theorem CaseA.eq_or_eq_mul_of_comm {z : G} {n : ℕ} (hC : Config z n) (hA : CaseA z)
    {a x b c : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a)
    (hb : Fused z b) (hbQ : b ∈ coreAt z) (hbz : b ≠ z)
    (hc : Fused z c) (hcQ : c ∈ coreAt z) (hcz : c ≠ z) (hbc : b * c = c * b) :
    c = b ∨ c = b * z := by
  obtain ⟨x', hx', hx'Q, hx'z, hnc⟩ :=
    CaseA.exists_partner hC hA ha haQ haz hx hxQ hxz hax hb hbQ hbz
  exact CaseA.eq_or_eq_mul_of_commute hC hA hb hbQ hbz hx' hx'Q hx'z hnc hc hcQ hcz hbc

private theorem PairSet_noncomm {z : G} {n : ℕ} (hC : Config z n) (hA : CaseA z) {a x : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a)
    {t t' : G} (ht : t ∈ PairSet G z) (ht' : t' ∈ PairSet G z) (hne : t ≠ t') :
    t * t' ≠ t' * t := by
  intro hcomm
  rw [mem_PairSet] at ht ht'
  have hc := CaseA.eq_or_eq_mul_of_comm hC hA ha haQ haz hx hxQ hxz hax
    ht.1.1 ht.1.2.1 ht.1.2.2 ht'.1.1 ht'.1.2.1 ht'.1.2.2 hcomm
  rcases hc with h | h
  · exact hne h.symm
  · have h1 := ht'.2
    rw [h, z_mul_z hC] at h1
    have h2 := ht.2
    omega

private theorem PairSet_comm_eq {z : G} {n : ℕ} (hC : Config z n) (hA : CaseA z) {a x : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a)
    {t t' : G} (ht : t ∈ PairSet G z) (ht' : t' ∈ PairSet G z) (hne : t ≠ t') :
    ⁅t, t'⁆ = z := by
  have htQ := (mem_PairSet.1 ht).1.2.1
  have ht'Q := (mem_PairSet.1 ht').1.2.1
  rcases hC.comm_eq t htQ t' ht'Q with h1 | h1
  · exact absurd (commutatorElement_eq_one_iff_mul_comm.1 h1)
      (PairSet_noncomm hC hA ha haQ haz hx hxQ hxz hax ht ht' hne)
  · exact h1

private theorem PairSet_ncard_le {z : G} {n : ℕ} (hC : Config z n) (hA : CaseA z) {a x : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a) :
    (PairSet G z).ncard ≤ 2 * n + 1 := by
  have key := hC.card_pairwise_le (Nat.card (PairSet G z))
    (fun i => ((Finite.equivFin (PairSet G z)).symm i : G))
    (fun i => (mem_PairSet.1 ((Finite.equivFin (PairSet G z)).symm i).2).1.2.1)
    (fun i j hij => by
      have hne : ((Finite.equivFin (PairSet G z)).symm i : G) ≠
          ((Finite.equivFin (PairSet G z)).symm j : G) := by
        intro h
        apply hij
        apply (Finite.equivFin (PairSet G z)).symm.injective
        exact Subtype.ext h
      exact PairSet_comm_eq hC hA ha haQ haz hx hxQ hxz hax
        ((Finite.equivFin (PairSet G z)).symm i).2 ((Finite.equivFin (PairSet G z)).symm j).2 hne)
  rw [Nat.card_coe_set_eq] at key
  exact key

theorem CaseA.ncard_le (hC : Config z n) (hA : CaseA z) {a x : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a) :
    Set.ncard {w : G | Fused z w ∧ w ∈ coreAt z ∧ w ≠ z} ≤ 4 * n + 2 := by
  change (FSet G z).ncard ≤ 4 * n + 2
  have h1 := Set.ncard_le_ncard (FSet_subset_pairSet hC)
  have h2 := Set.ncard_union_le (PairSet G z) ((fun t => t * z) '' PairSet G z)
  have h3 : ((fun t => t * z) '' PairSet G z).ncard ≤ (PairSet G z).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have h4 := PairSet_ncard_le hC hA ha haQ haz hx hxQ hxz hax
  omega

private theorem isElemAbelian_two_of_sq {G : Type} [Group G] (U : Subgroup G)
    (h : ∀ u ∈ U, u ^ 2 = 1) : CFSG.Open.IsElemAbelian 2 U := by
  refine ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩
  · show (u : G) * v = v * u
    have huu : (u : G) * u = 1 := by rw [← sq]; exact h u.1 u.2
    have hvv : (v : G) * v = 1 := by rw [← sq]; exact h v.1 v.2
    have huv : ((u : G) * v) * ((u : G) * v) = 1 := by
      rw [← sq]; exact h _ (U.mul_mem u.2 v.2)
    have hui : (u : G)⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    have hvi : (v : G)⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
    calc (u : G) * v = ((u : G) * v)⁻¹ := eq_inv_of_mul_eq_one_left huv
      _ = (v : G)⁻¹ * (u : G)⁻¹ := mul_inv_rev _ _
      _ = v * u := by rw [hui, hvi]
  · exact h u hu

private theorem card_inter_centralizer_le {a x : G} {n : ℕ} (hCa : Config a n) (P : Subgroup G)
    (hP : P ≤ coreAt a) (hax : a * x ≠ x * a) :
    Nat.card (P ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 ^ n := by
  have hsq : ∀ u ∈ (P ⊓ centralizer ({x} : Set G) : Subgroup G), u ^ 2 = 1 := by
    intro u hu
    rw [Subgroup.mem_inf] at hu
    have huQ : u ∈ coreAt a := hP hu.1
    have hux : Commute u x := Subgroup.mem_centralizer_singleton_iff.1 hu.2
    rcases hCa.sq_eq u huQ with h | h
    · exact h
    · exfalso
      apply hax
      have hc : Commute (u ^ 2) x := hux.pow_left 2
      rw [h] at hc
      exact hc.eq
  have hdisj : (P ⊓ centralizer ({x} : Set G) : Subgroup G) ⊓ centerAt a = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_inf, Subgroup.mem_inf] at hy
    rw [Subgroup.mem_bot]
    by_contra hy1
    have hord : orderOf y = 2 := orderOf_eq_prime (hsq y (Subgroup.mem_inf.2 hy.1)) hy1
    have hya : y = a := hCa.eq_of_mem_center hy.2 hord
    apply hax
    have hyx : Commute y x := Subgroup.mem_centralizer_singleton_iff.1 hy.1.2
    rw [← hya]
    exact hyx.eq
  exact hCa.card_elem_le_of_disjoint _ (inf_le_left.trans hP)
    (isElemAbelian_two_of_sq _ hsq) hdisj

private theorem card_centralizer_core {a z : G} {n : ℕ} (hCa : Config a n)
    (hzQ : z ∈ coreAt a) (hzZ : z ∉ centerAt a) :
    Nat.card (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G) = 2 ^ (2 * n + 1) := by
  have h1 := hCa.card_centralizer_mul_two hzQ hzZ
  rw [hCa.card_core] at h1
  have h2 : (2 : ℕ) ^ (2 * n + 2) = 2 ^ (2 * n + 1) * 2 := by ring
  omega

private theorem conj_eq_of_comm {p x w : G} (hpw : p * w = w * p) (h : p * x * p⁻¹ = w) :
    x = w := by
  calc x = p⁻¹ * (p * x * p⁻¹) * p := by group
    _ = p⁻¹ * (w * p) := by rw [h, mul_assoc]
    _ = p⁻¹ * (p * w) := by rw [hpw]
    _ = w := by group

private theorem conj_mem_FSet {z : G} {n : ℕ} (hC : Config z n) {p x : G}
    (hp : p ∈ centralizer ({z} : Set G)) (hx : x ∈ FSet G z) : p * x * p⁻¹ ∈ FSet G z := by
  rw [mem_FSet] at hx ⊢
  obtain ⟨⟨k, hk⟩, hxQ, hxz⟩ := hx
  have hpz : p * z = z * p := Subgroup.mem_centralizer_singleton_iff.1 hp
  refine ⟨⟨k * p⁻¹, ?_⟩, hC.conj_mem_core hp hxQ, ?_⟩
  · calc (k * p⁻¹)⁻¹ * z * (k * p⁻¹) = p * (k⁻¹ * z * k) * p⁻¹ := by group
      _ = p * x * p⁻¹ := by rw [hk]
  · intro h
    apply hxz
    exact conj_eq_of_comm hpz h

private theorem z_mem_core_base {z : G} {n : ℕ} (hC : Config z n) {g a : G}
    (hg : g⁻¹ * z * g = a) (haQ : a ∈ coreAt z) : z ∈ coreAt a := by
  have hCa : Config a n := by
    rw [← hg]
    exact hC.conj g
  have hcz : CFSG.conjugate (centerAt z) g ≤ centralizer ({z} : Set G) :=
    (hC.center_le_iff g).2 (by rw [hg]; exact haQ)
  have hcz' : centerAt a ≤ centralizer ({z} : Set G) := by
    rw [← hg, centerAt_conj z g]
    exact hcz
  have hzc : z ∈ centralizer (centerAt a : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.1 (hcz' hh)
  have hgz : g * a * g⁻¹ = z := by
    rw [← hg]
    group
  have e : (g⁻¹)⁻¹ * a * g⁻¹ = z := by
    rw [inv_inv]
    exact hgz
  have key := hCa.mem_core_of_centralizes g⁻¹ (by rw [e]; exact hzc)
  rwa [e] at key

private theorem z_not_mem_center_base {z a : G} {n : ℕ} (hC : Config z n) {g : G}
    (hg : g⁻¹ * z * g = a) (haz : a ≠ z) : z ∉ centerAt a := by
  have hCa : Config a n := by
    rw [← hg]
    exact hC.conj g
  intro hz
  exact haz (hCa.eq_of_mem_center hz hC.orderOf_eq).symm

private theorem conj_ne_base {z a x : G} {n : ℕ} (hC : Config z n) (hCa : Config a n)
    (ha : Fused z a) (haQ : a ∈ coreAt z) (hax : a * x ≠ x * a) {p : G}
    (hpa : p ∈ coreAt a) (hpz : p ∈ centralizer ({z} : Set G)) :
    p * x * p⁻¹ ≠ a ∧ p * x * p⁻¹ ≠ a * z := by
  have hpa' : p * a = a * p :=
    Subgroup.mem_centralizer_singleton_iff.1 (hCa.core_le_centralizer hpa)
  have hpz' : p * z = z * p := Subgroup.mem_centralizer_singleton_iff.1 hpz
  have haa : a * a = 1 := by
    rw [← sq]
    exact (involution_of_mem hC ha).1
  have hazc : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.1 (hC.core_le_centralizer haQ)
  constructor
  · intro h
    have hxa : x = a := conj_eq_of_comm hpa' h
    apply hax
    rw [hxa]
  · intro h
    have hpaz : p * (a * z) = a * z * p := by
      calc p * (a * z) = (p * a) * z := (mul_assoc _ _ _).symm
        _ = (a * p) * z := by rw [hpa']
        _ = a * (p * z) := mul_assoc _ _ _
        _ = a * (z * p) := by rw [hpz']
        _ = a * z * p := (mul_assoc _ _ _).symm
    have hxaz : x = a * z := conj_eq_of_comm hpaz h
    apply hax
    rw [hxaz]
    have h1 : a * (a * z) = z := by rw [← mul_assoc, haa, one_mul]
    have h2 : a * z * a = z := by
      calc a * z * a = z * a * a := by rw [hazc]
        _ = z * (a * a) := mul_assoc _ _ _
        _ = z := by rw [haa, mul_one]
    rw [h1, h2]

@[instance_reducible] private def conjActP (P : Subgroup G) : MulAction P G where
  smul p y := (p : G) * y * (p : G)⁻¹
  one_smul y := by
    show ((1 : P) : G) * y * ((1 : P) : G)⁻¹ = y
    simp
  mul_smul p q y := by
    show ((p * q : P) : G) * y * ((p * q : P) : G)⁻¹ =
      (p : G) * ((q : G) * y * (q : G)⁻¹) * (p : G)⁻¹
    simp [mul_assoc]

private theorem card_eq_orbit_mul_stab (P : Subgroup G) (x : G) :
    Nat.card P = Set.ncard {w : G | ∃ p ∈ P, p * x * p⁻¹ = w} *
      Nat.card (P ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  letI := conjActP P
  have hidx := MulAction.index_stabilizer P x
  have hmul := (MulAction.stabilizer P x).index_mul_card
  have horb : MulAction.orbit P x = {w : G | ∃ p ∈ P, p * x * p⁻¹ = w} := by
    ext w
    constructor
    · rintro ⟨⟨p, hp⟩, rfl⟩
      exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  have hstab : MulAction.stabilizer P x = (P ⊓ centralizer ({x} : Set G)).subgroupOf P := by
    ext p
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    show (p : G) * x * (p : G)⁻¹ = x ↔ ((p : G) ∈ P ∧ (p : G) * x = x * (p : G))
    rw [mul_inv_eq_iff_eq_mul]
    exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
  rw [hidx, horb, hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hmul
  exact hmul.symm

private theorem orbit_mem_F {z a x : G} {n : ℕ} (hC : Config z n) (hCa : Config a n)
    (ha : Fused z a) (haQ : a ∈ coreAt z) (hax : a * x ≠ x * a) (hxF : x ∈ FSet G z) {p : G}
    (hp : p ∈ coreAt a ⊓ centralizer ({z} : Set G)) :
    p * x * p⁻¹ ∈ FSet G z ∧ p * x * p⁻¹ ≠ a ∧ p * x * p⁻¹ ≠ a * z := by
  obtain ⟨hpa, hpz⟩ := Subgroup.mem_inf.1 hp
  obtain ⟨hne1, hne2⟩ := conj_ne_base hC hCa ha haQ hax hpa hpz
  exact ⟨conj_mem_FSet hC hpz hxF, hne1, hne2⟩

private theorem four_mul_lt_pow {n : ℕ} (hn : 3 ≤ n) : 4 * n < 2 ^ (n + 1) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

theorem CaseA.ncard_ge (hC : Config z n) (hA : CaseA z) {a x : G}
    (ha : Fused z a) (haQ : a ∈ coreAt z) (haz : a ≠ z)
    (hx : Fused z x) (hxQ : x ∈ coreAt z) (hxz : x ≠ z) (hax : a * x ≠ x * a) :
    2 ^ (n + 1) + 2 ≤ Set.ncard {w : G | Fused z w ∧ w ∈ coreAt z ∧ w ≠ z} := by
  obtain ⟨g, hg⟩ := id ha
  have hCa : Config a n := by
    rw [← hg]
    exact hC.conj g
  have hzQa : z ∈ coreAt a := z_mem_core_base hC hg haQ
  have hzZa : z ∉ centerAt a := z_not_mem_center_base hC hg haz
  have hxF : x ∈ FSet G z := mem_FSet.2 ⟨hx, hxQ, hxz⟩
  have hsplit := card_eq_orbit_mul_stab (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G) x
  rw [card_centralizer_core hCa hzQa hzZa] at hsplit
  have hbound := card_inter_centralizer_le hCa
    (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G) inf_le_left hax
  have hord : 2 ^ (n + 1) ≤ Set.ncard {w : G |
      ∃ p ∈ (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G), p * x * p⁻¹ = w} := by
    have key : 2 ^ (n + 1) * 2 ^ n ≤
        Set.ncard {w : G |
          ∃ p ∈ (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G), p * x * p⁻¹ = w} * 2 ^ n := by
      have h2 : 2 ^ (n + 1) * 2 ^ n = 2 ^ (2 * n + 1) := by ring
      rw [h2, hsplit]
      exact Nat.mul_le_mul le_rfl hbound
    exact Nat.le_of_mul_le_mul_right key (by positivity)
  have hane : a ≠ a * z := by
    intro h
    have h1 : a * 1 = a * z := by
      rw [mul_one]
      exact h
    have hz1 : z = 1 := (mul_left_cancel h1).symm
    have h2 := hC.orderOf_eq
    rw [hz1, orderOf_one] at h2
    norm_num at h2
  have hdisj : Disjoint
      {w : G | ∃ p ∈ (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G), p * x * p⁻¹ = w}
      ({a, a * z} : Set G) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    obtain ⟨p, hp, rfl⟩ := hw
    have h := orbit_mem_F hC hCa ha haQ hax hxF hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    rcases hw' with h' | h'
    · exact h.2.1 h'
    · exact h.2.2 h'
  have hsub : {w : G | ∃ p ∈ (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G), p * x * p⁻¹ = w}
      ∪ ({a, a * z} : Set G) ⊆ {w : G | Fused z w ∧ w ∈ coreAt z ∧ w ≠ z} := by
    intro w hw
    rcases hw with ⟨p, hp, rfl⟩ | hw
    · exact mem_FSet.1 (orbit_mem_F hC hCa ha haQ hax hxF hp).1
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with h | h
      · rw [h]
        exact ⟨ha, haQ, haz⟩
      · rw [h]
        exact mul_z_mem_F hC ha haQ haz
  have hcard : Set.ncard ({w : G | ∃ p ∈ (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G),
      p * x * p⁻¹ = w} ∪ ({a, a * z} : Set G)) =
      Set.ncard {w : G | ∃ p ∈ (coreAt a ⊓ centralizer ({z} : Set G) : Subgroup G),
        p * x * p⁻¹ = w} + 2 := by
    rw [Set.ncard_union_eq hdisj, Set.ncard_pair hane]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem CaseA.false (hC : Config z n) (hA : CaseA z) : False := by
  obtain ⟨a, x, ha, haQ, haz, hx, hxQ, hxz, hax⟩ := CaseA.exists_not_commute hC hA
  have h1 := CaseA.ncard_le hC hA ha haQ haz hx hxQ hxz hax
  have h2 := CaseA.ncard_ge hC hA ha haQ haz hx hxQ hxz hax
  have h3 := four_mul_lt_pow hC.three_le
  omega

end CFSG.GF2Type.CenterFour

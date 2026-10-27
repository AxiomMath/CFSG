module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenS
public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenD

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
open scoped commutatorElement

section Centre

variable {V : Type} [CommGroup V] [Finite V] {G T Y L : Subgroup (MulAut V)}

theorem Emb5Layer.central_eq_one_of_two (cfg : Emb5Cfg G T Y) (h : Emb5Layer G Y L)
    {z : MulAut V} (hzL : z ∈ L) (hzc : ∀ l ∈ L, l * z = z * l) {k : ℕ} (hz : z ^ 2 ^ k = 1) :
    z = 1 := by
  have hLG := h.le
  have hnorm : (L.subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mpr fun g hg =>
      normalizer_of_forall_conj h.normal hg
  have hcomp : CFSG.IsComponent (L.subgroupOf G) :=
    ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLG).symm h.quasi,
      hnorm.isSubnormal⟩
  have hzG : z ∈ G := hLG hzL
  have h1 := eq_one_of_central_two (noNormalTwo_of_pCore cfg.o2) hcomp
    (z := (⟨z, hzG⟩ : ↥G)) (Subgroup.mem_subgroupOf.mpr hzL)
    (fun l hl => Subtype.ext (hzc l (Subgroup.mem_subgroupOf.mp hl))) (k := k)
    (Subtype.ext (by simpa using hz))
  exact congrArg Subtype.val h1

end Centre

section Quot

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}

@[expose] def NoCentralTwo (L : Subgroup (MulAut V)) : Prop :=
  ∀ z : ↥L, z ∈ Subgroup.center ↥L → ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1

theorem lpi_surjective : Function.Surjective (lpi L) := QuotientGroup.mk'_surjective _

theorem lpi_eq_one_iff {x : ↥L} : lpi L x = 1 ↔ x ∈ Subgroup.center ↥L :=
  QuotientGroup.eq_one_iff x

theorem lpi_eq_iff {x y : ↥L} : lpi L x = lpi L y ↔ x⁻¹ * y ∈ Subgroup.center ↥L :=
  QuotientGroup.eq

theorem NoCentralTwo.orderOf_odd (h : NoCentralTwo L) [Finite ↥L] {z : ↥L}
    (hz : z ∈ Subgroup.center ↥L) : Odd (orderOf z) := by
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf z) (orderOf_pos z).ne'
  have hw : (z ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one z
  have hwc : z ^ m ∈ Subgroup.center ↥L := Subgroup.pow_mem _ hz m
  have hw1 : z ^ m = 1 := h _ hwc a hw
  have hdvd : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hw1
  rw [hord] at hdvd
  have hmpos : 0 < m := hm.pos
  have h2 : 2 ^ a * m ∣ 1 * m := by simpa using hdvd
  have h3 : 2 ^ a ∣ 1 := Nat.dvd_of_mul_dvd_mul_right hmpos h2
  have h4 : 2 ^ a = 1 := Nat.dvd_one.mp h3
  rw [hord, h4, one_mul]
  exact hm

theorem NoCentralTwo.unique (h : NoCentralTwo L) {s s' : ↥L} (hs : s * s = 1) (hs' : s' * s' = 1)
    (hss' : lpi L s = lpi L s') : s = s' := by
  have hz : s⁻¹ * s' ∈ Subgroup.center ↥L := lpi_eq_iff.mp hss'
  set z : ↥L := s⁻¹ * s' with hzdef
  have hs'eq : s' = s * z := by rw [hzdef]; group
  have hzc : ∀ g : ↥L, g * z = z * g := Subgroup.mem_center_iff.mp hz
  have hzz : z ^ 2 ^ 1 = 1 := by
    have h1 : s * z * (s * z) = 1 := by rw [← hs'eq]; exact hs'
    have h2 : s * z * (s * z) = s * s * (z * z) := by
      calc s * z * (s * z) = s * (z * s) * z := by group
        _ = s * (s * z) * z := by rw [← hzc s]
        _ = s * s * (z * z) := by group
    rw [h2, hs, one_mul] at h1
    simpa [pow_two] using h1
  have hz1 : z = 1 := h z hz 1 hzz
  rw [hs'eq, hz1, mul_one]

theorem NoCentralTwo.exists_lift (h : NoCentralTwo L) [Finite ↥L] {u : LQ L} (hu : u * u = 1) :
    ∃ s : ↥L, s * s = 1 ∧ lpi L s = u := by
  obtain ⟨x, rfl⟩ := lpi_surjective (L := L) u
  set z : ↥L := x * x with hzdef
  have hz : z ∈ Subgroup.center ↥L := by
    rw [← lpi_eq_one_iff, hzdef, map_mul]
    exact hu
  have hodd := h.orderOf_odd hz
  set m := orderOf z with hm
  refine ⟨x ^ m, ?_, ?_⟩
  · have : x ^ m * x ^ m = z ^ m := by
      rw [hzdef, ← pow_add, ← two_mul, pow_mul, pow_two]
    rw [this, hm]
    exact pow_orderOf_eq_one z
  · obtain ⟨j, hj⟩ := hodd
    have hu2 : lpi L x ^ 2 = 1 := by rw [pow_two]; exact hu
    rw [map_pow, hj, pow_succ, pow_mul, hu2, one_pow, one_mul]

theorem NoCentralTwo.comm_of (h : NoCentralTwo L) {s x : ↥L} (hs : s * s = 1)
    (hx : lpi L x * lpi L s = lpi L s * lpi L x) : x * s = s * x := by
  have h1 : (x * s * x⁻¹) * (x * s * x⁻¹) = 1 := by
    calc x * s * x⁻¹ * (x * s * x⁻¹) = x * (s * s) * x⁻¹ := by group
      _ = 1 := by rw [hs]; group
  have h2 : lpi L (x * s * x⁻¹) = lpi L s := by
    rw [map_mul, map_mul, map_inv, hx, mul_assoc, mul_inv_cancel, mul_one]
  have h3 := h.unique h1 hs h2
  calc x * s = x * s * x⁻¹ * x := by group
    _ = s * x := by rw [h3]

omit [CommGroup V] in
theorem commutator_mul_central_left {Γ : Type*} [Group Γ] {x y z : Γ}
    (hz : ∀ g : Γ, g * z = z * g) : ⁅x * z, y⁆ = ⁅x, y⁆ := by
  have h : z * y * z⁻¹ = y := by rw [← hz y]; group
  simp only [commutatorElement_def]
  calc x * z * y * (x * z)⁻¹ * y⁻¹ = x * (z * y * z⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

omit [CommGroup V] in
theorem commutator_mul_central_right {Γ : Type*} [Group Γ] {x y z : Γ}
    (hz : ∀ g : Γ, g * z = z * g) : ⁅x, y * z⁆ = ⁅x, y⁆ := by
  have h : z * x⁻¹ * z⁻¹ = x⁻¹ := by rw [← hz x⁻¹]; group
  simp only [commutatorElement_def]
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * (z * x⁻¹ * z⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [h]

theorem le_of_tilde_eq_top (hperf : Group.IsPerfect ↥L) {B : Subgroup (MulAut V)}
    (h : tilde (L := L) B = ⊤) : L ≤ B := by
  set B' : Subgroup ↥L := B.subgroupOf L with hB'
  have hz : ∀ x : ↥L, ∃ b ∈ B', ∃ z ∈ Subgroup.center ↥L, x = b * z := by
    intro x
    have hx : lpi L x ∈ tilde (L := L) B := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨b, hb, hbx⟩ := hx
    refine ⟨b, hb, b⁻¹ * x, lpi_eq_iff.mp hbx, ?_⟩
    group
  have hcomm : ∀ x y : ↥L, ⁅x, y⁆ ∈ B' := by
    intro x y
    obtain ⟨b₁, hb₁, z₁, hz₁, rfl⟩ := hz x
    obtain ⟨b₂, hb₂, z₂, hz₂, rfl⟩ := hz y
    rw [commutator_mul_central_left (Subgroup.mem_center_iff.mp hz₁),
      commutator_mul_central_right (Subgroup.mem_center_iff.mp hz₂)]
    rw [commutatorElement_def]
    exact B'.mul_mem (B'.mul_mem (B'.mul_mem hb₁ hb₂) (B'.inv_mem hb₁)) (B'.inv_mem hb₂)
  have hle : (⊤ : Subgroup ↥L) ≤ B' := by
    have h1 : commutator ↥L = ⊤ := Group.isPerfect_def.mp hperf
    rw [← h1]
    exact Subgroup.commutator_le.mpr fun x _ y _ => hcomm x y
  intro l hl
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top ⟨l, hl⟩))

end Quot

section Conj

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)}

@[expose] def conjL (hn : ∀ g ∈ G, ∀ x ∈ L, g * x * g⁻¹ ∈ L) {g : MulAut V} (hg : g ∈ G) :
    ↥L ≃* ↥L where
  toFun x := ⟨g * x * g⁻¹, hn g hg x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by simpa using hn g⁻¹ (G.inv_mem hg) x x.2⟩
  left_inv x := Subtype.ext (by simp only; group)
  right_inv x := Subtype.ext (by simp only; group)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjL_apply (hn : ∀ g ∈ G, ∀ x ∈ L, g * x * g⁻¹ ∈ L) {g : MulAut V} (hg : g ∈ G)
    (x : ↥L) : ((conjL hn hg x : ↥L) : MulAut V) = g * x * g⁻¹ := rfl

@[expose] def conjQ (hn : ∀ g ∈ G, ∀ x ∈ L, g * x * g⁻¹ ∈ L) {g : MulAut V} (hg : g ∈ G) :
    LQ L ≃* LQ L :=
  QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjL hn hg)
    (map_center_eq_of_mulEquiv _)

theorem conjQ_lpi (hn : ∀ g ∈ G, ∀ x ∈ L, g * x * g⁻¹ ∈ L) {g : MulAut V} (hg : g ∈ G)
    (x : ↥L) : conjQ hn hg (lpi L x) = lpi L (conjL hn hg x) := rfl

theorem conjQ_conjQ (hn : ∀ g ∈ G, ∀ x ∈ L, g * x * g⁻¹ ∈ L) {g : MulAut V} (hg : g ∈ G)
    (hg2 : g * g = 1) (s : LQ L) : conjQ hn hg (conjQ hn hg s) = s := by
  obtain ⟨x, rfl⟩ := lpi_surjective (L := L) s
  rw [conjQ_lpi, conjQ_lpi]
  congr 1
  apply Subtype.ext
  show g * (g * (x : MulAut V) * g⁻¹) * g⁻¹ = x
  calc g * (g * (x : MulAut V) * g⁻¹) * g⁻¹ = (g * g) * x * (g * g)⁻¹ := by group
    _ = x := by rw [hg2]; group

end Conj

end CFSG.CGT.PushingUpLit.CGT6

module

public import CFSG.GH74.Generic.Lifting
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.Front.Transfer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic

section Conj

variable {G : Type} [Group G]

theorem isConj_of_odd_order_mul {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hodd : Odd (orderOf (a * b))) : IsConj a b := by
  obtain ⟨m, hm⟩ := hodd
  set n := a * b with hn
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  set s := n ^ (m + 1) with hs
  have hs2 : s * s = n := by
    rw [hs, ← pow_add, show m + 1 + (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, ← hm,
      pow_orderOf_eq_one, one_mul]
  have han : a * n * a⁻¹ = n⁻¹ := by
    rw [hn, hainv, mul_inv_rev, hbinv, hainv]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have has : a * s * a⁻¹ = s⁻¹ := by
    have h1 : (MulAut.conj a : MulAut G) n = n⁻¹ := han
    have h2 : (MulAut.conj a : MulAut G) s = s⁻¹ := by
      rw [hs, map_pow, h1, inv_pow]
    exact h2
  refine isConj_iff.2 ⟨s⁻¹, ?_⟩
  have h3 : s⁻¹ * a * s = s⁻¹ * (a * s * a⁻¹) * a := by group
  rw [inv_inv, h3, has]
  calc s⁻¹ * s⁻¹ * a = (s * s)⁻¹ * a := by group
    _ = n⁻¹ * a := by rw [hs2]
    _ = b := by
      rw [hn, mul_inv_rev, hbinv, hainv]
      calc b * a * a = b * (a * a) := by group
        _ = b := by rw [ha, mul_one]

variable [Finite G]

theorem isConj_of_barOf_eq {x : G} {a b : G} (ha : a ∈ centralizer ({x} : Set G))
    (hb : b ∈ centralizer ({x} : Set G)) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (h : barOf ha = barOf hb) : IsConj a b := by
  refine isConj_of_odd_order_mul ha2 hb2 ?_
  have hker : proj x ((⟨a, ha⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨b, hb⟩) = 1 := by
    rw [map_mul, map_inv]
    have h' : proj x ⟨a, ha⟩ = proj x ⟨b, hb⟩ := h
    rw [h', inv_mul_cancel]
  have hodd := proj_odd x _ hker
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have e : (((⟨a, ha⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨b, hb⟩ :
      ↥(centralizer ({x} : Set G))) : G) = a * b := by
    simp [hainv]
  rw [← e, Subgroup.orderOf_coe]
  exact hodd

end Conj

section Lift

variable {G : Type} [Group G] [Finite G]

theorem closure_comm_of_comm {C : Type*} [Group C] (s : Set C)
    (hsc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ g ∈ Subgroup.closure s, ∀ h ∈ Subgroup.closure s, g * h = h * g := by
  have h1 : ∀ g ∈ Subgroup.closure s, ∀ b ∈ s, b * g = g * b := by
    intro g hg
    have : Subgroup.closure s ≤ Subgroup.centralizer (s : Set C) := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hsc b hb a ha)
    have hg' := this hg
    rw [Subgroup.mem_centralizer_iff] at hg'
    intro b hb
    exact hg' b hb
  intro g hg h hh
  have : Subgroup.closure s ≤ Subgroup.centralizer ({g} : Set C) := by
    rw [Subgroup.closure_le]
    intro b hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact h1 g hg b hb
  have := this hh
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

theorem closure_sq_of_comm {C : Type*} [Group C] (s : Set C) (hs2 : ∀ a ∈ s, a * a = 1)
    (hsc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) : ∀ g ∈ Subgroup.closure s, g * g = 1 := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem a ha => exact hs2 a ha
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab := closure_comm_of_comm s hsc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha =>
    calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      _ = 1 := by rw [iha, inv_one]

theorem exists_frame_lift {x : G} (hx : orderOf x = 2) (w : Fin 4 → CentralizerBar x)
    (hw2 : ∀ i, w i * w i = 1)
    (hwc : ∀ i j, w i * w j = w j * w i) (hprod : w 0 * w 1 * w 2 * w 3 = xbar x) :
    ∃ (u : Fin 4 → G) (hu : ∀ i, u i ∈ centralizer ({x} : Set G)),
      (∀ i, u i * u i = 1 ∧ barOf (hu i) = w i) ∧ (∀ i j, u i * u j = u j * u i) ∧
        u 0 * u 1 * u 2 * u 3 = x := by
  classical
  set X : Subgroup G := centralizer ({x} : Set G) with hX
  set s : Set (CentralizerBar x) := Set.range w with hs
  have hs2 : ∀ a ∈ s, a * a = 1 := by
    rintro _ ⟨i, rfl⟩
    exact hw2 i
  have hsc : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hwc i j
  set Pb : Subgroup (CentralizerBar x) := Subgroup.closure s with hPb
  have hPbp : IsPGroup 2 Pb := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    have := closure_sq_of_comm s hs2 hsc g g.2
    change (g : CentralizerBar x) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    exact this
  obtain ⟨P, hP2, hPmap⟩ := exists_lift_twoSubgroup (pPrimeCore 2 ↥X) Pb hPbp
  have hwP : ∀ i, w i ∈ P.map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) := fun i => by
    rw [hPmap]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  choose p hpP hpw using hwP
  have hinj : ∀ a ∈ P, ∀ b ∈ P, proj x a = proj x b → a = b := fun a ha b hb h =>
    lift_twoSubgroup_injOn hP2 ha hb h
  have hpx : ∀ i, proj x (p i) = w i := hpw
  have hsq : ∀ i, p i * p i = 1 := fun i => by
    apply hinj _ (P.mul_mem (hpP i) (hpP i)) _ P.one_mem
    rw [map_mul, hpx, hw2, map_one]
  have hcomm : ∀ i j, p i * p j = p j * p i := fun i j => by
    apply hinj _ (P.mul_mem (hpP i) (hpP j)) _ (P.mul_mem (hpP j) (hpP i))
    rw [map_mul, map_mul, hpx, hpx, hwc]
  refine ⟨fun i => ((p i : ↥X) : G), fun i => (p i).2, fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact congrArg Subtype.val (hsq i)
  · exact hpx i
  · intro i j
    exact congrArg Subtype.val (hcomm i j)
  ·
    set q : ↥X := p 0 * p 1 * p 2 * p 3 with hq
    have hqP : q ∈ P := P.mul_mem (P.mul_mem (P.mul_mem (hpP 0) (hpP 1)) (hpP 2)) (hpP 3)
    have hqx : proj x q = proj x (xH x) := by
      rw [hq, map_mul, map_mul, map_mul, hpx, hpx, hpx, hpx, hprod]
      rfl
    have hxx : xH x * xH x = 1 := xH_mul_self hx
    have hq2 : q * q = 1 := by
      apply hinj _ (P.mul_mem hqP hqP) _ P.one_mem
      rw [map_mul, hqx, ← map_mul, hxx, map_one]
    have hn : (xH x)⁻¹ * q ∈ pPrimeCore 2 ↥X := (QuotientGroup.eq).1 hqx.symm
    have hcq : q * (xH x)⁻¹ = (xH x)⁻¹ * q := (Commute.inv_right (xH_central x q))
    have hn2 : ((xH x)⁻¹ * q) * ((xH x)⁻¹ * q) = 1 := by
      calc ((xH x)⁻¹ * q) * ((xH x)⁻¹ * q) = (xH x)⁻¹ * (q * (xH x)⁻¹) * q := by group
        _ = (xH x)⁻¹ * ((xH x)⁻¹ * q) * q := by rw [hcq]
        _ = (xH x * xH x)⁻¹ * (q * q) := by group
        _ = 1 := by rw [hxx, hq2]; group
    have hP' : IsPGroup 2 (Subgroup.zpowers ((xH x)⁻¹ * q)) :=
      isPGroup_zpowers_of_pow_two_pow_eq_one (n := 1) (by simpa [pow_two] using hn2)
    have h1 := eq_one_of_isPGroup_of_mem_pPrimeCore hP' (Subgroup.mem_zpowers _) hn
    have : q = xH x := by
      have := congrArg (fun z => xH x * z) h1
      simpa using this
    have h4 := congrArg Subtype.val this
    exact h4

end Lift

end CFSG.GH74.Generic.S1

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscBSCModel
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem commute_of_comm_mem_zpowers [Finite G] {A : Subgroup G} {z : G} (hA : Odd (Nat.card A))
    (hz2 : z * z = 1) (hz : ∀ a ∈ A, z * a = a * z) {p : G}
    (hmem : ∀ a ∈ A, ⁅p, a⁆ ∈ Subgroup.zpowers z) : ∀ a ∈ A, p * a = a * p := by
  have hcen : ∀ c ∈ Subgroup.zpowers z, ∀ a ∈ A, a * c = c * a := by
    intro c hc a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact (Commute.zpow_left (show Commute z a from hz a ha) k).symm.eq
  have hsq : ∀ c ∈ Subgroup.zpowers z, c ^ 2 = 1 := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    have h2z : z ^ 2 = 1 := by rw [sq]; exact hz2
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2z, one_zpow]
  intro a ha
  let f : A →* G :=
    { toFun := fun x => ⁅p, (x : G)⁆
      map_one' := by simp
      map_mul' := fun x y => by
        have hc : (x : G) * ⁅p, (y : G)⁆ * (x : G)⁻¹ = ⁅p, (y : G)⁆ := by
          rw [hcen _ (hmem y y.2) x x.2, mul_inv_cancel_right]
        show ⁅p, (x : G) * (y : G)⁆ = ⁅p, (x : G)⁆ * ⁅p, (y : G)⁆
        calc ⁅p, (x : G) * (y : G)⁆
            = ⁅p, (x : G)⁆ * ((x : G) * ⁅p, (y : G)⁆ * (x : G)⁻¹) := by
              simp only [commutatorElement_def]
              group
          _ = ⁅p, (x : G)⁆ * ⁅p, (y : G)⁆ := by rw [hc] }
  set x : A := ⟨a, ha⟩ with hx
  have hfx : f x = ⁅p, a⁆ := rfl
  have hdvd2 : orderOf (f x) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hfx]
    exact hsq _ (hmem a ha)
  have hdvdA : orderOf (f x) ∣ Nat.card A :=
    (orderOf_map_dvd f x).trans (orderOf_dvd_natCard x)
  have hcop : Nat.Coprime (orderOf (f x)) 2 :=
    Nat.Coprime.coprime_dvd_left hdvdA hA.coprime_two_right
  have hone : orderOf (f x) = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd2
  have hfx1 : f x = 1 := orderOf_eq_one_iff.mp hone
  rw [hfx] at hfx1
  exact commutatorElement_eq_one_iff_mul_comm.mp hfx1

theorem odd_natCard_of_isPGroup_three [Finite G] {A : Subgroup G} (hA : IsPGroup 3 ↥A) :
    Odd (Nat.card A) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn]
  exact Odd.pow (by decide)

@[expose] def Model1520 (X : Subgroup G) (t : G) : Prop :=
  ∀ A : Subgroup G, IsPGroup 3 ↥A → A ≤ Subgroup.normalizer (X : Set G) →
    A ≤ Subgroup.centralizer ((X ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) : Set G) →
    A ≤ Subgroup.centralizer (X : Set G)

theorem le_centralizer_of_transport217 [Finite G] {X N A : Subgroup G} {z t : G}
    (hz2 : z * z = 1) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hAz : A ≤ Subgroup.centralizer ({z} : Set G)) (hAN : A ≤ N)
    (hNn : Subgroup.centralizer ({t, z} : Set G) ≤ Subgroup.normalizer (N : Set G))
    (hXz : X ≤ Subgroup.centralizer ({z} : Set G)) (hNX : N ⊓ X ≤ Subgroup.zpowers z)
    (hA3 : IsPGroup 3 ↥A) (h1520 : Model1520 X t) : A ≤ Subgroup.centralizer (X : Set G) := by
  refine h1520 A hA3 hAX ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have hpX : p ∈ X := (Subgroup.mem_inf.mp hp).1
  have hpt : p ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hp).2
  have hpz : p ∈ Subgroup.centralizer ({z} : Set G) := hXz hpX
  have hpn : p ∈ Subgroup.normalizer (N : Set G) := by
    apply hNn
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mp hpt |>.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mp hpz |>.symm
  have hmem : ∀ a ∈ A, ⁅p, a⁆ ∈ Subgroup.zpowers z := by
    intro a ha
    apply hNX
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h1 : p * a * p⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hpn a).mp (hAN ha)
      have h2 : ⁅p, a⁆ = (p * a * p⁻¹) * a⁻¹ := by
        rw [commutatorElement_def]
      rw [h2]
      exact N.mul_mem h1 (N.inv_mem (hAN ha))
    · have h1 : a * p⁻¹ * a⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hAX ha) p⁻¹).mp (X.inv_mem hpX)
      have h2 : ⁅p, a⁆ = p * (a * p⁻¹ * a⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact X.mul_mem hpX h1
  have := commute_of_comm_mem_zpowers (odd_natCard_of_isPGroup_three hA3) hz2
    (fun a ha => (Subgroup.mem_centralizer_singleton_iff.mp (hAz ha)).symm) hmem a ha
  exact this

theorem isSubnormal_of_centralizer_inf {C X L : Subgroup G}
    (hCX : C ≤ Subgroup.normalizer (X : Set G))
    (h1 : IsSubnormal L (C ⊓ Subgroup.centralizer (X : Set G))) : IsSubnormal L C := by
  have hCX' : ∀ c ∈ C, ∀ x ∈ X, c * x * c⁻¹ ∈ X := fun c hc x hx =>
    (Subgroup.mem_normalizer_iff.mp (hCX hc) x).mp hx
  set N : Subgroup G := C ⊓ Subgroup.centralizer (X : Set G) with hN
  have hNC : N ≤ C := inf_le_left
  have hnorm : (N.subgroupOf C).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine Subgroup.mem_inf.mpr ⟨by
      simpa using C.mul_mem (C.mul_mem c.2 (Subgroup.mem_inf.mp hn).1) (C.inv_mem c.2), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcx := hCX' ((c⁻¹ : C) : G) (C.inv_mem c.2) x hx
    have hth := (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hn).2) _ hcx
    set cg : G := (c : G) with hcg
    set ng : G := (n : G) with hng
    have hth' : ng * (cg⁻¹ * x * cg) = (cg⁻¹ * x * cg) * ng := by
      simpa [hcg, hng, mul_assoc] using hth.symm
    show x * (cg * ng * cg⁻¹) = (cg * ng * cg⁻¹) * x
    calc x * (cg * ng * cg⁻¹) = cg * ((cg⁻¹ * x * cg) * ng) * cg⁻¹ := by group
      _ = cg * (ng * (cg⁻¹ * x * cg)) * cg⁻¹ := by rw [hth']
      _ = (cg * ng * cg⁻¹) * x := by group
  exact CFSG.ClassicalInvolution.isSubnormal_trans h1
    (IsSubnormal.step hNC hnorm (IsSubnormal.refl C))

theorem mem_normalizer_of_forall_commute {L : Subgroup G} {y : G} (hy : ∀ x ∈ L, x * y = y * x) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : y * h * y⁻¹ = h := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hy h hh).symm
    rw [this]
    exact hh
  · intro hh
    have hw := hy _ hh
    have e : y * h = y * (y * h * y⁻¹) := by
      calc y * h = (y * h * y⁻¹) * y := by group
        _ = y * (y * h * y⁻¹) := hw
    have e' : h = y * h * y⁻¹ := mul_left_cancel e
    rw [e']
    exact hh

structure Lift217Side (X K L A : Subgroup G) (z : G) : Prop where
  involution : IsUniqueInvolution K z
  centralizes : K ≤ Subgroup.centralizer (X : Set G)
  le : K ≤ L
  normal : (K.subgroupOf L).Normal
  quotient : Nonempty (↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, ZMod 3))
  le_A : A ≤ L
  threeGroup : IsPGroup 3 ↥A
  sup_eq : L = K ⊔ A

namespace Lift217Side

variable {X K L A : Subgroup G} {z : G}

theorem le_centralizer (h : Lift217Side X K L A z) :
    L ≤ Subgroup.centralizer ({z} : Set G) := by
  intro l hl
  have hz := h.involution
  have hzL : z ∈ L := h.le hz.mem
  have hmem := h.normal.conj_mem ⟨z, hzL⟩ (by rw [Subgroup.mem_subgroupOf]; exact hz.mem)
    ⟨l, hl⟩
  rw [Subgroup.mem_subgroupOf] at hmem
  have hmem' : l * z * l⁻¹ ∈ K := by simpa using hmem
  have hsq : (l * z * l⁻¹) * (l * z * l⁻¹) = 1 := by
    calc (l * z * l⁻¹) * (l * z * l⁻¹) = l * (z * z) * l⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  rcases hz.unique _ hmem' hsq with h1 | h1
  · exfalso
    apply hz.ne_one
    have := congrArg (fun w => l⁻¹ * w * l) h1
    simpa [mul_assoc] using this
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp h1)

end Lift217Side

theorem mem_normalizer_of_conjSub_eq {c : G} {N : Subgroup G} (h : conjSub c N = N) :
    c ∈ Subgroup.normalizer (N : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := conj_mem_conjSub (n := c) hx
    rwa [h] at this
  · intro hx
    rw [← h, mem_conjSub_iff] at hx
    simpa [mul_assoc] using hx

theorem conjSub_injective (c : G) {P Q : Subgroup G} (h : conjSub c P = conjSub c Q) : P = Q := by
  ext x
  have := Subgroup.ext_iff.mp h (c * x * c⁻¹)
  rw [mem_conjSub_iff, mem_conjSub_iff] at this
  simpa [mul_assoc] using this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

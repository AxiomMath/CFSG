module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
import CFSG.GroupTheory.KleinFourAutomorphism
import TauCeti.GroupTheory.QuotientGroup.MulAut

public section

namespace CFSG.GroupTheory

open Subgroup QuaternionGroup

variable {G : Type*} [Group G]

theorem mul_self_eq_of_not_mem_centerIn_of_pow_three [Finite G] {N : Subgroup G} {z σ : G}
    (hidx : Nat.card N = 4 * Nat.card (centerIn N))
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1) (hz : z ∈ centerIn N)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hσN : ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) (hσZ : ∀ x ∈ centerIn N, σ * x = x * σ)
    (hσ3 : ∀ n ∈ N, σ ^ 3 * n * (σ ^ 3)⁻¹ * n⁻¹ ∈ centerIn N)
    (hσ : ∃ n ∈ N, σ * n * σ⁻¹ * n⁻¹ ∉ centerIn N) :
    ∀ x ∈ N, x ∉ centerIn N → x * x = z := by
  classical
  set Z : Subgroup G := centerIn N with hZdef
  have hZN : Z ≤ N := by
    rw [hZdef]
    exact inf_le_left
  have hZ2' : ∀ u ∈ Z, u * u = 1 := by
    intro u hu
    exact hZ2 u (by simpa [hZdef] using hu)
  have hz' : z ∈ Z := by simpa [hZdef] using hz
  have hσZ' : ∀ u ∈ Z, σ * u = u * σ := by
    intro u hu
    exact hσZ u (by simpa [hZdef] using hu)
  have hσ3' : ∀ n ∈ N, σ ^ 3 * n * (σ ^ 3)⁻¹ * n⁻¹ ∈ Z := by
    intro n hn
    rw [hZdef]
    exact hσ3 n hn
  have hσ' : ∃ n ∈ N, σ * n * σ⁻¹ * n⁻¹ ∉ Z := by
    obtain ⟨n, hn, h⟩ := hσ
    exact ⟨n, hn, by simpa [hZdef] using h⟩
  have hσNinv : ∀ n ∈ N, σ⁻¹ * n * σ ∈ N := by
    let f : ↥N →* ↥N :=
      { toFun := fun n => ⟨σ * (n : G) * σ⁻¹, hσN n n.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by
          simp only [Subgroup.coe_mul]
          group) }
    have hf_inj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h : σ * (a : G) * σ⁻¹ = σ * (b : G) * σ⁻¹ := congrArg Subtype.val hab
      calc (a : G) = σ⁻¹ * (σ * (a : G) * σ⁻¹) * σ := by group
        _ = σ⁻¹ * (σ * (b : G) * σ⁻¹) * σ := by rw [h]
        _ = (b : G) := by group
    have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
    intro n hn
    obtain ⟨m, hm⟩ := hf_surj ⟨n, hn⟩
    have hval : σ * (m : G) * σ⁻¹ = n := congrArg Subtype.val hm
    rw [show σ⁻¹ * n * σ = (m : G) by
      calc σ⁻¹ * n * σ = σ⁻¹ * (σ * (m : G) * σ⁻¹) * σ := by rw [hval]
        _ = (m : G) := by group]
    exact m.2
  have hσnorm : σ ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hσN n hn
    · intro hn
      have h := hσNinv (σ * n * σ⁻¹) hn
      have h' : σ⁻¹ * (σ * n * σ⁻¹) * σ = n := by group
      rwa [h'] at h
  have hx2mem : ∀ x ∈ N, x * x ∈ Z := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨N.mul_mem hx hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hconj : x * (x * y * x⁻¹ * y⁻¹) * x⁻¹ = x * y * x⁻¹ * y⁻¹ := by
      rcases hcomm x hx y hy with hd | hd
      · rw [hd]
        group
      · rw [hd]
        have hxz : x * z = z * x := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz').2 x hx
        rw [hxz]
        group
    have hsq : (x * x) * y * (x * x)⁻¹ * y⁻¹ = 1 := by
      calc (x * x) * y * (x * x)⁻¹ * y⁻¹
          = (x * (x * y * x⁻¹ * y⁻¹) * x⁻¹) * (x * y * x⁻¹ * y⁻¹) := by group
        _ = (x * y * x⁻¹ * y⁻¹) * (x * y * x⁻¹ * y⁻¹) := by rw [hconj]
        _ = 1 := by
            rcases hcomm x hx y hy with hd | hd
            · rw [hd]
              group
            · rw [hd]
              simpa using hZ2' z hz'
    have h1 : (x * x) * y * (x * x)⁻¹ = y := by
      calc (x * x) * y * (x * x)⁻¹
          = ((x * x) * y * (x * x)⁻¹ * y⁻¹) * y := by group
        _ = 1 * y := by rw [hsq]
        _ = y := one_mul y
    calc y * (x * x) = ((x * x) * y * (x * x)⁻¹) * (x * x) := by rw [h1]
      _ = (x * x) * y := by group
  have hqconj : ∀ n ∈ N, (σ * n * σ⁻¹) * (σ * n * σ⁻¹) = n * n := by
    intro n hn
    have hn2 : n * n ∈ Z := hx2mem n hn
    have hσn2 : σ * (n * n) * σ⁻¹ = n * n := by
      have hcommσ : σ * (n * n) = (n * n) * σ := hσZ' (n * n) hn2
      calc σ * (n * n) * σ⁻¹ = ((n * n) * σ) * σ⁻¹ := by rw [hcommσ]
        _ = n * n := by group
    calc (σ * n * σ⁻¹) * (σ * n * σ⁻¹) = σ * (n * n) * σ⁻¹ := by group
      _ = n * n := hσn2
  let Z' : Subgroup ↥N := Z.subgroupOf N
  have hZ'center : Z' = Subgroup.center ↥N := by
    ext n
    constructor
    · intro hn
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hn).2 (m : G) m.2
    · intro hn
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨n.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h := Subgroup.mem_center_iff.mp hn ⟨g, hg⟩
      exact congrArg Subtype.val h
  have hZ'char : Z'.Characteristic := by
    rw [hZ'center]
    exact Subgroup.centerCharacteristic
  have hZ'normal : Z'.Normal := Subgroup.normal_of_characteristic Z'
  let Q := ↥N ⧸ Z'
  let sN : ↥(Subgroup.normalizer (N : Set G)) := ⟨σ, hσnorm⟩
  let gN : MulAut ↥N := Subgroup.normalizerMonoidHom N sN
  have hgN_apply : ∀ n : ↥N, ((gN n : ↥N) : G) = σ * (n : G) * σ⁻¹ :=
    fun n => Subgroup.normalizerMonoidHom_apply_apply_coe N sN n
  let aQ : MulAut Q := MulAut.mapQuotient Z' gN
  have haQ_mk : ∀ n : ↥N, aQ (QuotientGroup.mk n : Q) = (QuotientGroup.mk (gN n) : Q) :=
    fun n => MulAut.mapQuotient_mk Z' gN n
  have hgN3 : gN ^ 3 = Subgroup.normalizerMonoidHom N
      ⟨σ ^ 3, Subgroup.pow_mem (Subgroup.normalizer (N : Set G)) hσnorm 3⟩ := by
    have hsN3 : sN ^ 3 = ⟨σ ^ 3, Subgroup.pow_mem (Subgroup.normalizer (N : Set G)) hσnorm 3⟩ :=
      Subtype.ext rfl
    calc gN ^ 3 = Subgroup.normalizerMonoidHom N (sN ^ 3) := by
          rw [show gN = Subgroup.normalizerMonoidHom N sN from rfl, map_pow]
      _ = Subgroup.normalizerMonoidHom N
            ⟨σ ^ 3, Subgroup.pow_mem (Subgroup.normalizer (N : Set G)) hσnorm 3⟩ := by rw [hsN3]
  have hgN3_apply : ∀ n : ↥N,
      (((gN ^ 3) n : ↥N) : G) = σ ^ 3 * (n : G) * (σ ^ 3)⁻¹ := by
    intro n
    rw [hgN3]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe N
      ⟨σ ^ 3, Subgroup.pow_mem (Subgroup.normalizer (N : Set G)) hσnorm 3⟩ n
  have haQ3 : aQ ^ 3 = 1 := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H n =>
      rw [show aQ ^ 3 = MulAut.mapQuotient Z' (gN ^ 3) from by
        rw [show aQ = MulAut.mapQuotient Z' gN from rfl, map_pow]]
      rw [MulAut.mapQuotient_mk, MulAut.one_apply]
      apply QuotientGroup.eq_iff_div_mem.mpr
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hcoe : ((((gN ^ 3) n) / n : ↥N) : G) =
          σ ^ 3 * (n : G) * (σ ^ 3)⁻¹ * (n : G)⁻¹ := by
        rw [Subgroup.coe_div, hgN3_apply, div_eq_mul_inv]
      rw [hcoe]
      exact hσ3' n n.2
  have haQ_ne : aQ ≠ 1 := by
    obtain ⟨n0, hn0, hn0Z⟩ := hσ'
    intro h
    let n : ↥N := ⟨n0, hn0⟩
    have h1 : aQ (QuotientGroup.mk n : Q) = (QuotientGroup.mk n : Q) := by
      rw [h, MulAut.one_apply]
    rw [haQ_mk] at h1
    have h2 : (gN n) / n ∈ Z' := QuotientGroup.eq_iff_div_mem.mp h1
    have h3 : ((gN n : ↥N) : G) / n0 = σ * n0 * σ⁻¹ * n0⁻¹ := by
      rw [hgN_apply, div_eq_mul_inv]
    have h4 : σ * n0 * σ⁻¹ * n0⁻¹ ∈ Z := by
      have h := Subgroup.mem_subgroupOf.mp h2
      rw [Subgroup.coe_div, h3] at h
      exact h
    exact hn0Z h4
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have horder : orderOf aQ = 3 := orderOf_eq_prime haQ3 haQ_ne
  have hcardZ' : Nat.card Z' = Nat.card (centerIn N) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : centerIn N ≤ N)).toEquiv
  have hZ'pos : 0 < Nat.card Z' := by
    have : Nonempty ↥Z' := ⟨⟨1, Subgroup.one_mem Z'⟩⟩
    exact Nat.card_pos
  have hcardN : Nat.card ↥N = 4 * Nat.card Z' := by
    rw [hidx, ← hcardZ']
  have hQcard : Nat.card Q = 4 := by
    have hQmul : Nat.card ↥N = Nat.card Q * Nat.card Z' :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
    have hEq : 4 * Nat.card Z' = Nat.card Q * Nat.card Z' := by
      rw [← hcardN, hQmul]
    exact Nat.eq_of_mul_eq_mul_right hZ'pos hEq.symm
  have hsq : ∀ a : Q, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H n =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (hx2mem n n.2)
  have hExpDvd : Monoid.exponent Q ∣ 2 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro a
    rw [pow_two]
    exact hsq a
  have hExpNe : Monoid.exponent Q ≠ 1 := by
    intro h1
    have : Subsingleton Q := Monoid.exp_eq_one_iff.mp h1
    have hle : Nat.card Q ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  have hExp : Monoid.exponent Q = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hExpDvd with h | h
    · exact absurd h hExpNe
    · exact h
  have : IsKleinFour Q := IsKleinFour.mk hQcard hExp
  intro x hx hxZ
  let y : G := σ * x * σ⁻¹
  have hyN : y ∈ N := hσN x hx
  let w : G := σ * y * σ⁻¹
  have hwN : w ∈ N := hσN y hyN
  have hq_x_y : x * x = y * y := by
    dsimp [y]
    exact (hqconj x hx).symm
  have hq_y_w : y * y = w * w := by
    dsimp [w]
    exact (hqconj y hyN).symm
  have hq_x_w : x * x = w * w := hq_x_y.trans hq_y_w
  let xN : ↥N := ⟨x, hx⟩
  let yN : ↥N := ⟨y, hyN⟩
  let wN : ↥N := ⟨w, hwN⟩
  have hxbar_ne : (QuotientGroup.mk xN : Q) ≠ 1 := by
    intro h
    exact hxZ (by simpa using Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff xN).mp h))
  have hyZ : y ∉ Z := by
    intro hyZ'
    have hσy : σ * y = y * σ := hσZ' y hyZ'
    have hx_eq : x = y := by
      calc x = σ⁻¹ * y * σ := by
            dsimp [y]
            group
        _ = y := by
            calc σ⁻¹ * y * σ = σ⁻¹ * (y * σ) := by group
              _ = σ⁻¹ * (σ * y) := by rw [← hσy]
              _ = y := by group
    exact hxZ (by simpa [hx_eq] using hyZ')
  have hybar_ne : (QuotientGroup.mk yN : Q) ≠ 1 := by
    intro h
    exact hyZ (by simpa using Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff yN).mp h))
  have haQ_x : aQ (QuotientGroup.mk xN : Q) = QuotientGroup.mk yN := by
    have hg : gN xN = yN := by
      apply Subtype.ext
      rw [hgN_apply]
    rw [haQ_mk, hg]
  have haQ_y : aQ (QuotientGroup.mk yN : Q) = QuotientGroup.mk wN := by
    have hg : gN yN = wN := by
      apply Subtype.ext
      rw [hgN_apply]
    rw [haQ_mk, hg]
  have haQ2_x : aQ (aQ (QuotientGroup.mk xN : Q)) = QuotientGroup.mk wN := by
    rw [haQ_x, haQ_y]
  obtain ⟨hax_ne, -, -, hcover⟩ :=
    CFSG.kleinFour_order_three_cycle Q aQ horder (QuotientGroup.mk xN : Q) hxbar_ne
  have hxy_ne : (QuotientGroup.mk yN : Q) ≠ QuotientGroup.mk xN := by
    intro h
    exact hax_ne (haQ_x.trans h)
  have hprod_ne1 : (QuotientGroup.mk xN : Q) * (QuotientGroup.mk yN : Q) ≠ 1 := by
    intro h
    have hx2 : (QuotientGroup.mk xN : Q) * (QuotientGroup.mk xN : Q) = 1 :=
      IsKleinFour.mul_self _
    have hy_eq : (QuotientGroup.mk yN : Q) = QuotientGroup.mk xN :=
      mul_left_cancel (by rw [h, hx2])
    exact hxy_ne hy_eq
  have hprod_nex : (QuotientGroup.mk xN : Q) * (QuotientGroup.mk yN : Q) ≠
      QuotientGroup.mk xN := by
    intro h
    have h1 : (QuotientGroup.mk xN : Q) * (QuotientGroup.mk yN : Q) =
        (QuotientGroup.mk xN : Q) * 1 := by rw [h, mul_one]
    exact hybar_ne (mul_left_cancel h1)
  have hprod_ney : (QuotientGroup.mk xN : Q) * (QuotientGroup.mk yN : Q) ≠
      QuotientGroup.mk yN := by
    intro h
    have h1 : (QuotientGroup.mk xN : Q) * (QuotientGroup.mk yN : Q) =
        1 * (QuotientGroup.mk yN : Q) := by rw [h, one_mul]
    exact hxbar_ne (mul_right_cancel h1)
  have hprod : (QuotientGroup.mk xN : Q) * (QuotientGroup.mk yN : Q) =
      QuotientGroup.mk wN := by
    rcases hcover _ hprod_ne1 with h | h | h
    · exact absurd h hprod_nex
    · exact absurd (h.trans haQ_x) hprod_ney
    · exact h.trans haQ2_x
  have hprod_xy : (QuotientGroup.mk (xN * yN) : Q) = QuotientGroup.mk wN := by
    rw [QuotientGroup.mk_mul, hprod]
  have hcoset : (xN * yN) / wN ∈ Z' :=
    QuotientGroup.eq_iff_div_mem.mp hprod_xy
  have hdivZ : (x * y) / w ∈ Z := by
    have h := Subgroup.mem_subgroupOf.mp hcoset
    simpa [Subgroup.coe_div, Subgroup.coe_mul] using h
  have hx_central : ∀ (_ : x * y = y * x), x ∈ Z := by
    intro hxy
    refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hcomm_mul : ∀ (a u : G), a ∈ N → u ∈ Z → x * a = a * x →
        x * (u * a) = (u * a) * x := by
      intro a u ha hu hax
      have hux : u * x = x * u :=
        (Subgroup.mem_centralizer_iff.mp hu.2 x hx).symm
      calc x * (u * a) = (x * u) * a := by group
        _ = (u * x) * a := by rw [← hux]
        _ = u * (x * a) := by group
        _ = u * (a * x) := by rw [hax]
        _ = (u * a) * x := by group
    have hxxy : x * (x * y) = (x * y) * x := by
      calc x * (x * y) = x * (y * x) := by rw [hxy]
        _ = (x * y) * x := by group
    by_cases hnZ : n ∈ Z
    · exact (Subgroup.mem_centralizer_iff.mp hnZ.2 x hx).symm
    · have hnbar_ne : (QuotientGroup.mk (⟨n, hn⟩ : ↥N) : Q) ≠ 1 := by
        intro h
        have hmem : (⟨n, hn⟩ : ↥N) ∈ Z' :=
          (QuotientGroup.eq_one_iff (N := Z') (⟨n, hn⟩ : ↥N)).mp h
        exact hnZ (by simpa using Subgroup.mem_subgroupOf.mp hmem)
      rcases hcover _ hnbar_ne with hcov | hcov | hcov
      · let u : G := n / x
        have huZ' : (⟨n, hn⟩ : ↥N) / xN ∈ Z' := QuotientGroup.eq_iff_div_mem.mp hcov
        have huZ : u ∈ Z := by
          have h := Subgroup.mem_subgroupOf.mp huZ'
          simpa [u, Subgroup.coe_div] using h
        have hn_eq : n = u * x := by
          dsimp [u]
          rw [div_mul_cancel]
        rw [hn_eq]
        exact (hcomm_mul x u hx huZ rfl).symm
      · let u : G := n / y
        have hcov' : (QuotientGroup.mk (⟨n, hn⟩ : ↥N) : Q) = QuotientGroup.mk yN :=
          hcov.trans haQ_x
        have huZ' : (⟨n, hn⟩ : ↥N) / yN ∈ Z' := QuotientGroup.eq_iff_div_mem.mp hcov'
        have huZ : u ∈ Z := by
          have h := Subgroup.mem_subgroupOf.mp huZ'
          simpa [u, Subgroup.coe_div] using h
        have hn_eq : n = u * y := by
          dsimp [u]
          rw [div_mul_cancel]
        rw [hn_eq]
        exact (hcomm_mul y u hyN huZ hxy).symm
      · let u : G := n / (x * y)
        have hcov' : (QuotientGroup.mk (⟨n, hn⟩ : ↥N) : Q) = QuotientGroup.mk (xN * yN) :=
          (hcov.trans haQ2_x).trans hprod_xy.symm
        have huZ' : (⟨n, hn⟩ : ↥N) / (xN * yN) ∈ Z' :=
          QuotientGroup.eq_iff_div_mem.mp hcov'
        have huZ : u ∈ Z := by
          have h := Subgroup.mem_subgroupOf.mp huZ'
          simpa [u, Subgroup.coe_div, Subgroup.coe_mul] using h
        have hn_eq : n = u * (x * y) := by
          dsimp [u]
          rw [div_mul_cancel]
        rw [hn_eq]
        exact (hcomm_mul (x * y) u (N.mul_mem hx hyN) huZ hxxy).symm
  have hq_xy_w : (x * y) * (x * y) = w * w := by
    set u : G := (x * y) / w with hu_def
    have huZ : u ∈ Z := by simpa [hu_def] using hdivZ
    have huw : u * w = w * u :=
      (Subgroup.mem_centralizer_iff.mp huZ.2 w hwN).symm
    have hxy : x * y = u * w := by rw [hu_def, div_mul_cancel]
    calc (x * y) * (x * y) = (u * w) * (u * w) := by rw [hxy]
      _ = (u * u) * (w * w) := by
          calc (u * w) * (u * w) = u * (w * u) * w := by group
            _ = u * (u * w) * w := by rw [← huw]
            _ = (u * u) * (w * w) := by group
      _ = w * w := by rw [hZ2' u huZ, one_mul]
  have hd_ne_one : x⁻¹ * y * x * y⁻¹ ≠ 1 := by
    intro hd1
    have hyx : y * x = x * y := by
      have h1 : x⁻¹ * y * x = y := by
        have h := congrArg (fun t => t * y) hd1
        simpa [mul_assoc] using h
      calc y * x = x * (x⁻¹ * y * x) := by group
        _ = x * y := by rw [h1]
    exact hxZ (hx_central hyx.symm)
  have hd_z : x⁻¹ * y * x * y⁻¹ = z := by
    rcases hcomm x⁻¹ (N.inv_mem hx) y hyN with h | h
    · exact absurd (by simpa using h) hd_ne_one
    · simpa using h
  have hq_xy_z : (x * y) * (x * y) = z := by
    have hformula : (x * y) * (x * y) = (x * x) * (x⁻¹ * y * x * y⁻¹) * (y * y) := by
      group
    have hcommzx : z * (x * x) = (x * x) * z :=
      (Subgroup.mem_centralizer_iff.mp hz'.2 (x * x) (N.mul_mem hx hx)).symm
    rw [hformula, hd_z, ← hq_x_y]
    calc (x * x) * z * (x * x) = (x * x) * (z * (x * x)) := by group
      _ = (x * x) * ((x * x) * z) := by rw [hcommzx]
      _ = ((x * x) * (x * x)) * z := by group
      _ = z := by rw [hZ2' (x * x) (hx2mem x hx), one_mul]
  exact (hq_x_w.trans hq_xy_w.symm).trans hq_xy_z

theorem forall_commute_of_pow_three_eq_one {N : Subgroup G} {σ : G}
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1) (hσ3 : σ ^ 3 = 1)
    (hσZ : ∀ x ∈ centerIn N, σ * x = x * σ)
    (hσ : ∀ n ∈ N, σ * n * σ⁻¹ * n⁻¹ ∈ centerIn N) :
    ∀ n ∈ N, σ * n = n * σ := by
  intro n hn
  set c : G := σ * n * σ⁻¹ * n⁻¹ with hc_def
  have hcZ : c ∈ centerIn N := hσ n hn
  have hcσ : c * σ = σ * c := (hσZ c hcZ).symm
  have hcn : σ * n * σ⁻¹ = c * n := by
    rw [hc_def]
    group
  have hσc : σ * c * σ⁻¹ = c := by
    calc σ * c * σ⁻¹ = (σ * c) * σ⁻¹ := by group
      _ = (c * σ) * σ⁻¹ := by rw [← hcσ]
      _ = c := by group
  have hσ2 : σ ^ 2 * n * (σ ^ 2)⁻¹ = n := by
    rw [pow_two]
    calc (σ * σ) * n * (σ * σ)⁻¹
        = σ * (σ * n * σ⁻¹) * σ⁻¹ := by group
      _ = σ * (c * n) * σ⁻¹ := by rw [hcn]
      _ = (σ * c * σ⁻¹) * (σ * n * σ⁻¹) := by group
      _ = c * (c * n) := by rw [hσc, hcn]
      _ = (c * c) * n := by group
      _ = n := by rw [hZ2 c hcZ, one_mul]
  have hσ3n : σ ^ 3 * n * (σ ^ 3)⁻¹ = c * n := by
    rw [pow_three]
    calc σ * (σ * σ) * n * (σ * (σ * σ))⁻¹
        = σ * (σ ^ 2 * n * (σ ^ 2)⁻¹) * σ⁻¹ := by
          rw [pow_two]
          group
      _ = σ * n * σ⁻¹ := by rw [hσ2]
      _ = c * n := hcn
  have hn_eq : n = c * n := by
    rw [← hσ3n, hσ3]
    group
  have hc1 : c = 1 := by
    have h : n * n⁻¹ = (c * n) * n⁻¹ := congrArg (fun t => t * n⁻¹) hn_eq
    simpa [mul_assoc] using h.symm
  have hconj : σ * n * σ⁻¹ = n := by
    rw [hcn, hc1, one_mul]
  calc σ * n = (σ * n * σ⁻¹) * σ := by group
    _ = n * σ := by rw [hconj]

theorem forall_commute_or_mul_self_eq_of_pow_three_eq_one [Finite G] {N : Subgroup G} {z σ : G}
    (hidx : Nat.card N = 4 * Nat.card (centerIn N))
    (hZ2 : ∀ x ∈ centerIn N, x * x = 1) (hz : z ∈ centerIn N)
    (hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hσN : ∀ n ∈ N, σ * n * σ⁻¹ ∈ N) (hσ3 : σ ^ 3 = 1)
    (hσZ : ∀ x ∈ centerIn N, σ * x = x * σ) :
    (∀ n ∈ N, σ * n = n * σ) ∨ ∀ x ∈ N, x ∉ centerIn N → x * x = z := by
  by_cases h : ∃ n ∈ N, σ * n * σ⁻¹ * n⁻¹ ∉ centerIn N
  · right
    apply mul_self_eq_of_not_mem_centerIn_of_pow_three hidx hZ2 hz hcomm hσN hσZ
    · intro n hn
      simp [hσ3]
    · exact h
  · left
    push Not at h
    exact forall_commute_of_pow_three_eq_one hZ2 hσ3 hσZ h

theorem quaternionGroup_two_eq_one_or_eq_a_two_of_mul_self (x : QuaternionGroup 2)
    (hx : x * x = 1) : x = 1 ∨ x = a 2 := by
  revert x
  decide

theorem not_elementaryAbelian_of_card_eq_sixteen_of_quaternion_quotient [Finite G]
    {T N Z : Subgroup G} (π : ↥T →* QuaternionGroup 2) (hker : ∀ g : ↥T, π g = 1 → (g : G) ∈ N)
    (hZ : Nat.card Z ≤ 4) (hN2 : ∀ x ∈ N, x * x = 1 → x ∈ Z)
    (F : Subgroup G) (hFT : F ≤ T) (hF : Nat.card F = 16) :
    ¬ ((∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1) := by
  rintro ⟨-, hFsq⟩
  let φ : ↥F →* QuaternionGroup 2 := π.comp (Subgroup.inclusion hFT)
  have hφ_sq : ∀ x : ↥φ.range, (x : QuaternionGroup 2) * x = 1 := by
    intro x
    obtain ⟨y, hy⟩ := x.2
    have hy2 : y * y = 1 := by
      apply Subtype.ext
      simpa using hFsq (y : G) y.2
    calc (x : QuaternionGroup 2) * x = φ y * φ y := by rw [← hy]
      _ = φ (y * y) := (map_mul φ y y).symm
      _ = 1 := by rw [hy2, map_one]
  have hrange : Nat.card φ.range ≤ 2 := by
    let f : ↥φ.range → Bool := fun x => if (x : QuaternionGroup 2) = 1 then false else true
    have hf_inj : Function.Injective f := by
      intro a b hab
      have hiff : ((a : QuaternionGroup 2) = 1) ↔ ((b : QuaternionGroup 2) = 1) := by
        simpa [f] using hab
      by_cases ha1 : (a : QuaternionGroup 2) = 1
      · exact Subtype.ext (ha1.trans ((hiff.mp ha1).symm))
      · have hb1 : ¬ (b : QuaternionGroup 2) = 1 := fun hb => ha1 (hiff.mpr hb)
        have ha2 : (a : QuaternionGroup 2) = QuaternionGroup.a 2 := by
          rcases quaternionGroup_two_eq_one_or_eq_a_two_of_mul_self (a : QuaternionGroup 2)
            (hφ_sq a) with h | h
          · exact absurd h ha1
          · exact h
        have hb2 : (b : QuaternionGroup 2) = QuaternionGroup.a 2 := by
          rcases quaternionGroup_two_eq_one_or_eq_a_two_of_mul_self (b : QuaternionGroup 2)
            (hφ_sq b) with h | h
          · exact absurd h hb1
          · exact h
        exact Subtype.ext (ha2.trans hb2.symm)
    have hcardBool : Nat.card Bool = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    calc Nat.card φ.range ≤ Nat.card Bool := Nat.card_le_card_of_injective f hf_inj
      _ = 2 := hcardBool
  have hker : Nat.card ↥φ.ker ≤ Nat.card Z := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥φ.ker => (⟨((x : ↥F) : G), ?_⟩ : ↥Z)) ?_
    · have hxN : ((x : ↥F) : G) ∈ N := by
        refine hker ⟨((x : ↥F) : G), hFT x.1.2⟩ ?_
        have hx1 : φ x = 1 := MonoidHom.mem_ker.mp x.2
        exact hx1
      exact hN2 ((x : ↥F) : G) hxN (hFsq ((x : ↥F) : G) x.1.2)
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥Z => (z : G)) hab
  have hcard := Subgroup.card_ker_mul_card_range φ
  rw [hF] at hcard
  have hmul : Nat.card ↥φ.ker * Nat.card ↥φ.range ≤ 4 * 2 :=
    Nat.mul_le_mul (hker.trans hZ) hrange
  omega

end CFSG.GroupTheory

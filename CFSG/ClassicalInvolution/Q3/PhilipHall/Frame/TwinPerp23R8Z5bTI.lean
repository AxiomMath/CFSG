module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLCen
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Z5b

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section TI

variable {Y : Type} [Group Y] [Finite Y]

theorem conjSub_eq_of_mem_centralizer {E : Subgroup Y} (hZ : Subgroup.center Y = ⊥)
    (hgen : ∀ x : Y, E.map (MulAut.conj x).toMonoidHom ≠ E →
      E ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤)
    {x v : Y} (hv : v ≠ 1) (hvE : v ∈ Subgroup.centralizer (E : Set Y))
    (hvx : v ∈ Subgroup.centralizer ((conjSub x E : Subgroup Y) : Set Y)) : conjSub x E = E := by
  by_contra hne
  have htop : E ⊔ conjSub x E = ⊤ := hgen x hne
  have hle : E ⊔ conjSub x E ≤ Subgroup.centralizer ({v} : Set Y) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hvE) y hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp hvx) y hy)
  apply hv
  have hc : v ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ Subgroup.centralizer ({v} : Set Y) := hle (htop ▸ Subgroup.mem_top y)
    exact Subgroup.mem_centralizer_singleton_iff.mp hy
  rw [hZ] at hc
  exact hc

theorem conjSub_eq_of_centralizer {E : Subgroup Y} (hZ : Subgroup.center Y = ⊥)
    (hgen : ∀ x : Y, E.map (MulAut.conj x).toMonoidHom ≠ E →
      E ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤)
    {w x : Y} (hw : w ≠ 1) (hwE : w ∈ Subgroup.centralizer (E : Set Y))
    (hx : x ∈ Subgroup.centralizer ({w} : Set Y)) : conjSub x E = E := by
  refine conjSub_eq_of_mem_centralizer hZ hgen hw hwE ?_
  rw [← Asc77.Thompson.conjSub_centralizer_conjSub]
  have hxw : x * w * x⁻¹ = w := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hx]
    group
  have h := conj_mem_conjSub (n := x) hwE
  rwa [hxw] at h

theorem eq_one_of_mem_oddCoreOf {E : Subgroup Y} {w : Y} (hw : w ∈ oddCoreOf E) (hw2 : w * w = 1) :
    w = 1 := by
  have hdvd : orderOf w ∣ Nat.card ↥(oddCoreOf E) := Subgroup.orderOf_dvd_natCard _ hw
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    rw [h] at hdvd
    exact (Nat.not_even_iff_odd.mpr (oddCoreOf_odd_natCard E)) (even_iff_two_dvd.mpr hdvd)

theorem conj_eq_of_conjSub_eq {E : Subgroup Y} {e x : Y} (hE : LemL.OmegaOneCenter E e) (heE : e ∈ E)
    (hEc : E ≤ Subgroup.centralizer ({e} : Set Y)) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hx : conjSub x E = E) : x * e * x⁻¹ = e := by
  set z := x * e * x⁻¹ with hzdef
  have hzE : z ∈ E := by
    rw [← hx]
    exact conj_mem_conjSub heE
  have hzc : ∀ y ∈ E, z * y = y * z := by
    intro y hy
    have hy' : x⁻¹ * y * x ∈ E := by
      have h : y ∈ conjSub x E := hx.symm ▸ hy
      exact mem_conjSub_iff.mp h
    have hcomm : x⁻¹ * y * x * e = e * (x⁻¹ * y * x) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hEc hy')
    calc z * y = x * (e * (x⁻¹ * y * x)) * x⁻¹ := by rw [hzdef]; group
      _ = x * (x⁻¹ * y * x * e) * x⁻¹ := by rw [hcomm]
      _ = y * z := by rw [hzdef]; group
  have hz2 : z * z = 1 := by
    rw [hzdef]
    calc x * e * x⁻¹ * (x * e * x⁻¹) = x * (e * e) * x⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have hcomm' : ∀ y ∈ E, z * y * z⁻¹ * y⁻¹ ∈ oddCoreOf E := by
    intro y hy
    have h1 : z * y * z⁻¹ * y⁻¹ = 1 := by rw [hzc y hy]; group
    rw [h1]
    exact (oddCoreOf E).one_mem
  have hsq : z * z ∈ oddCoreOf E := by
    rw [hz2]
    exact (oddCoreOf E).one_mem
  rcases hE z hzE hcomm' hsq with hzO | hzO
  · exfalso
    have hz1 : z = 1 := eq_one_of_mem_oddCoreOf hzO hz2
    apply he1
    have h : e = x⁻¹ * z * x := by rw [hzdef]; group
    rw [h, hz1]
    group
  · have hze : z * e = e * z := hzc e heE
    have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    have hez : e⁻¹ * z = 1 := by
      refine eq_one_of_mem_oddCoreOf hzO ?_
      rw [heinv]
      calc e * z * (e * z) = e * (z * e) * z := by group
        _ = e * (e * z) * z := by rw [hze]
        _ = (e * e) * (z * z) := by group
        _ = 1 := by rw [he2, hz2, one_mul]
    exact (inv_mul_eq_one.mp hez).symm

theorem centralizer_le_of_mem_centralizer {E : Subgroup Y} {e : Y} (hZ : Subgroup.center Y = ⊥)
    (hgen : ∀ x : Y, E.map (MulAut.conj x).toMonoidHom ≠ E →
      E ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤)
    (hE : LemL.OmegaOneCenter E e) (heE : e ∈ E) (hEc : E ≤ Subgroup.centralizer ({e} : Set Y))
    (he2 : e * e = 1) (he1 : e ≠ 1) {w : Y} (hw : w ≠ 1)
    (hwE : w ∈ Subgroup.centralizer (E : Set Y)) :
    Subgroup.centralizer ({w} : Set Y) ≤ Subgroup.centralizer ({e} : Set Y) := by
  intro x hx
  have h := conj_eq_of_conjSub_eq hE heE hEc he2 he1 (conjSub_eq_of_centralizer hZ hgen hw hwE hx)
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  calc x * e = x * e * x⁻¹ * x := by group
    _ = e * x := by rw [h]

theorem gamma1_le_centralizer {E : Subgroup Y} {e : Y} (hZ : Subgroup.center Y = ⊥)
    (hgen : ∀ x : Y, E.map (MulAut.conj x).toMonoidHom ≠ E →
      E ⊔ E.map (MulAut.conj x).toMonoidHom = ⊤)
    (hE : LemL.OmegaOneCenter E e) (heE : e ∈ E) (hEc : E ≤ Subgroup.centralizer ({e} : Set Y))
    (he2 : e * e = 1) (he1 : e ≠ 1) {U : Subgroup Y} (hU : U ≤ Subgroup.centralizer (E : Set Y))
    (X : Subgroup Y) : gamma1 U X ≤ Subgroup.centralizer ({e} : Set Y) := by
  unfold gamma1
  exact iSup₂_le fun w hw => iSup_le fun hw1 =>
    inf_le_right.trans (centralizer_le_of_mem_centralizer hZ hgen hE heE hEc he2 he1 hw1 (hU hw))

end TI

section Cfg

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem rLayer_le_centralizer (f : Y) : rLayer (Om R) f ≤ Subgroup.centralizer ({f} : Set Y) := by
  unfold rLayer
  exact iSup₂_le fun _ _ => iSup_le fun hR => hR

theorem p23_gamma1_le_centralizer (hc : P23Cfg n Y R S t K' W u e g)
    (hgen : ∀ x : Y, (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom ≠ rLayer (Om R) e →
      rLayer (Om R) e ⊔ (rLayer (Om R) e).map (MulAut.conj x).toMonoidHom = ⊤)
    (hE : LemL.OmegaOneCenter (rLayer (Om R) e) e) {U : Subgroup Y}
    (hU : U ≤ Subgroup.centralizer ((rLayer (Om R) e : Subgroup Y) : Set Y)) (X : Subgroup Y) :
    gamma1 U X ≤ Subgroup.centralizer ({e} : Set Y) :=
  gamma1_le_centralizer
    (InductionBridge.center_eq_bot_of_fstar_simple hc.std.perp.core.simple hc.std.perp.core.nonab) hgen hE
    (p23_e_mem_rLayer hc) (rLayer_le_centralizer e) hc.data.he2 hc.data.he1 hU X

end Cfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Z5b

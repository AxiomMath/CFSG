module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67InnerTools
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {Y : Type} [Group Y]

theorem isElementaryAbelian_subgroupOf {M : Type*} [Group M] {r : ℕ} {V B : Subgroup M}
    (hVB : V ≤ B) (hVe : IsElementaryAbelian r V) : IsElementaryAbelian r (V.subgroupOf B) :=
  isElementaryAbelian_of_injective' (p := r)
    (Subgroup.subgroupOfEquivOfLe hVB).toMonoidHom (Subgroup.subgroupOfEquivOfLe hVB).injective

theorem conj_range_normal : ((MulAut.conj : Y →* MulAut Y).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  refine ⟨g y, ?_⟩
  ext x
  simp [MulAut.conj_apply]

def planeOverGroup (Y : Type) [Group Y] (V Z : Subgroup (MulAut Y)) : Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range ⊔ (Z ⊔ V)

theorem conj_range_le_planeOverGroup (V Z : Subgroup (MulAut Y)) :
    (MulAut.conj : Y →* MulAut Y).range ≤ planeOverGroup Y V Z := le_sup_left

theorem V_le_planeOverGroup (V Z : Subgroup (MulAut Y)) : V ≤ planeOverGroup Y V Z :=
  le_sup_right.trans' (le_sup_right (a := Z))

theorem Z_le_planeOverGroup (V Z : Subgroup (MulAut Y)) : Z ≤ planeOverGroup Y V Z :=
  le_sup_right.trans' (le_sup_left (b := V))

theorem planeOverGroup_inf_centralizer_le_normalizer (hcen : Subgroup.center Y = ⊥) {r : ℕ}
    {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : Y →* MulAut Y).range) {a : MulAut Y} (haV : a ∈ V)
    (ha1 : a ≠ 1) :
    planeOverGroup Y V Z ⊓ Subgroup.centralizer ({a} : Set (MulAut Y)) ≤
      Subgroup.normalizer (Z : Set (MulAut Y)) := by
  obtain ⟨-, -, hVe, -, -, -, -, -, hcomm⟩ := h2
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    mulAut_conj_injective_of_center_bot hcen
  have : ((MulAut.conj : Y →* MulAut Y).range).Normal := conj_range_normal
  rintro b ⟨hbB, hbc⟩
  obtain ⟨i, hi, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hbB
  have hVcomm : ∀ v ∈ V, a * v = v * a := fun v hv =>
    congrArg Subtype.val (hVe.is_comm.comm (⟨a, haV⟩ : V) (⟨v, hv⟩ : V))
  have hconjV : ∀ v ∈ V, ∀ z ∈ Z, v * z * v⁻¹ = z := fun v hv z hz => by
    rw [hcomm v hv z hz]; group
  have hZc : Z ≤ Subgroup.centralizer ({a} : Set (MulAut Y)) := fun z hz => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm a haV z hz).symm
  have hVc : V ≤ Subgroup.centralizer ({a} : Set (MulAut Y)) := fun v hv => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hVcomm v hv).symm
  have hwc : w ∈ Subgroup.centralizer ({a} : Set (MulAut Y)) := (sup_le hZc hVc) hw
  have hZn : Z ≤ Subgroup.normalizer (Z : Set (MulAut Y)) := Subgroup.le_normalizer
  have hVn : V ≤ Subgroup.normalizer (Z : Set (MulAut Y)) := fun v hv => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hz
      rw [hconjV v hv h hz]
      exact hz
    · intro hz
      have h1 := hconjV v⁻¹ (V.inv_mem hv) _ hz
      have e : v⁻¹ * (v * h * v⁻¹) * v⁻¹⁻¹ = h := by group
      rw [e] at h1
      rw [h1]
      exact hz
  have hwn : w ∈ Subgroup.normalizer (Z : Set (MulAut Y)) := (sup_le hZn hVn) hw
  have hic : i ∈ Subgroup.centralizer ({a} : Set (MulAut Y)) := by
    have hbc' : i * w * a = a * (i * w) := Subgroup.mem_centralizer_singleton_iff.1 hbc
    have hwc' : w * a = a * w := Subgroup.mem_centralizer_singleton_iff.1 hwc
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : i * a * w = a * i * w := by
      calc i * a * w = i * (a * w) := by group
        _ = i * (w * a) := by rw [hwc']
        _ = i * w * a := by group
        _ = a * (i * w) := hbc'
        _ = a * i * w := by group
    exact mul_right_cancel h1
  obtain ⟨y, rfl⟩ := hi
  obtain ⟨x, rfl⟩ := hinn a haV
  have hyx : y ∈ fixSub (MulAut.conj x) := by
    have hic' : MulAut.conj y * MulAut.conj x = MulAut.conj x * MulAut.conj y :=
      Subgroup.mem_centralizer_singleton_iff.1 hic
    have h1 : MulAut.conj (x * y) = MulAut.conj (y * x) := by rw [map_mul, map_mul, hic']
    have h2 := hinj h1
    rw [mem_fixSub, MulAut.conj_apply]
    calc x * y * x⁻¹ = y * x * x⁻¹ := by rw [h2]
      _ = y := by group
  exact Subgroup.mul_mem _ (h3 _ haV ha1 y hyx) hwn

theorem Z_le_inSubgroup_theta [Finite Y] (hcen : Subgroup.center Y = ⊥) {r : ℕ}
    {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : Y →* MulAut Y).range) {a : MulAut Y} (haV : a ∈ V)
    (ha1 : a ≠ 1) :
    Z ≤ inSubgroup (aschbacherSolvableCore r)
      (planeOverGroup Y V Z ⊓ Subgroup.centralizer ({a} : Set (MulAut Y))) := by
  have hnorm := planeOverGroup_inf_centralizer_le_normalizer hcen h2 h3 hinn haV ha1
  obtain ⟨hr, -, -, -, hZab, -, hZcop, -, hcomm⟩ := h2
  set H : Subgroup (MulAut Y) :=
    planeOverGroup Y V Z ⊓ Subgroup.centralizer ({a} : Set (MulAut Y)) with hH
  have hZH : Z ≤ H := fun z hz => Subgroup.mem_inf.2 ⟨Z_le_planeOverGroup V Z hz,
    Subgroup.mem_centralizer_singleton_iff.2 (hcomm a haV z hz).symm⟩
  have : Finite H := inferInstance
  have hN : (Z.subgroupOf H).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hxZ : (x : MulAut Y) ∈ Z := Subgroup.mem_subgroupOf.1 hx
    have := (Subgroup.mem_normalizer_iff.1 (hnorm g.2) (x : MulAut Y)).1 hxZ
    exact Subgroup.mem_subgroupOf.2 (by simpa using this)
  have hsolv : Group.IsSolvable (Z.subgroupOf H) := by
    have : IsMulCommutative (Z.subgroupOf H) := ⟨⟨fun x y => by
      apply Subtype.ext
      apply Subtype.ext
      exact hZab _ (Subgroup.mem_subgroupOf.1 x.2) _ (Subgroup.mem_subgroupOf.1 y.2)⟩⟩
    infer_instance
  have hndvd : ¬ r ∣ Nat.card (Z.subgroupOf H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]
    intro h
    have h1 := Nat.Coprime.eq_one_of_dvd hZcop.symm h
    exact hr.one_lt.ne' h1
  have hle := (solvable_prime_complement_core_characterization hr).2.2.2.1 _ hN hsolv hndvd
  rw [inSubgroup]
  intro z hz
  exact ⟨⟨z, hZH hz⟩, hle (Subgroup.mem_subgroupOf.2 hz), rfl⟩

theorem Z_le_autThetaT [Finite Y] (hcen : Subgroup.center Y = ⊥) {r : ℕ}
    {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : Y →* MulAut Y).range) :
    Z ≤ autThetaT r (planeOverGroup Y V Z) V := by
  simp only [autThetaT]
  refine le_iInf fun a => le_iInf fun haV => le_iInf fun ha1 => ?_
  exact Z_le_inSubgroup_theta hcen h2 h3 hinn haV ha1

theorem false_of_autThetaT_eq_bot [Finite Y] (hcen : Subgroup.center Y = ⊥) {r : ℕ}
    {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hbot : autThetaT r (planeOverGroup Y V Z) V = ⊥) : False := by
  have hle := Z_le_autThetaT hcen h2 h3 hinn
  rw [hbot] at hle
  obtain ⟨-, -, -, -, -, -, -, hZbot, -⟩ := h2
  exact hZbot (le_bot_iff.1 hle)

theorem false_of_thetaT_eq_bot [Finite Y] (hcen : Subgroup.center Y = ⊥) {r : ℕ}
    {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z)
    (hinn : ∀ v ∈ V, v ∈ (MulAut.conj : Y →* MulAut Y).range)
    (hbot : thetaT r (V.subgroupOf (planeOverGroup Y V Z)) = ⊥) : False := by
  set B := planeOverGroup Y V Z with hB
  have hr : r.Prime := h2.1
  have hZ : Z.subgroupOf B ≤ thetaT r (V.subgroupOf B) := by
    simp only [thetaT]
    refine le_iInf fun a => le_iInf fun haV => le_iInf fun ha1 => ?_
    have haV' : (a : MulAut Y) ∈ V := Subgroup.mem_subgroupOf.1 haV
    have ha1' : (a : MulAut Y) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have h1 := Z_le_inSubgroup_theta hcen h2 h3 hinn haV' ha1'
    rw [← map_subtype_theta_centralizer hr B a] at h1
    intro z hz
    have hz' : (z : MulAut Y) ∈ Z := Subgroup.mem_subgroupOf.1 hz
    obtain ⟨y, hy, hyz⟩ := h1 hz'
    have : y = z := Subtype.ext hyz
    exact this ▸ hy
  rw [hbot] at hZ
  obtain ⟨-, -, -, -, -, -, -, hZbot, -⟩ := h2
  apply hZbot
  rw [eq_bot_iff]
  intro z hz
  have h1 : (⟨z, Z_le_planeOverGroup V Z hz⟩ : B) ∈ Z.subgroupOf B := Subgroup.mem_subgroupOf.2 hz
  have h2 := hZ h1
  rw [Subgroup.mem_bot] at h2 ⊢
  exact congrArg Subtype.val h2

end CFSG.GH74.GLS.Stage2.Bender.Thm1

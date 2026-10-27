module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX4
public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigX1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Gen

variable {G : Type} [Group G] [Finite G] {Q : Subgroup G} {r : ℕ}
  (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))

theorem mul_centralizes_of_conj_zeta (hr : 4 ≤ r) {t u : G}
    (ht : ∀ q ∈ Q, t * q * t⁻¹ = QSub.zeta e * q * (QSub.zeta e)⁻¹)
    (hu : ∀ q ∈ Q, u * q * u⁻¹ = QSub.zeta e * q * (QSub.zeta e)⁻¹) :
    ∀ q ∈ Q, (t * u) * q = q * (t * u) := by
  intro q hq
  have hζ : QSub.zeta e ∈ Q := QSub.zeta_mem e
  have hq' : QSub.zeta e * q * (QSub.zeta e)⁻¹ ∈ Q := Q.mul_mem (Q.mul_mem hζ hq) (Q.inv_mem hζ)
  have h1 := ht _ hq'
  have hz2 : QSub.zeta e * QSub.zeta e = quatInvolution r e := QSub.zeta_mul_self e hr
  have hzq : quatInvolution r e * q = q * quatInvolution r e :=
    (quatInvolution_comm hr e hq).symm
  have hrhs : QSub.zeta e * (QSub.zeta e * q * (QSub.zeta e)⁻¹) * (QSub.zeta e)⁻¹ = q := by
    have h2 : QSub.zeta e * (QSub.zeta e * q * (QSub.zeta e)⁻¹) * (QSub.zeta e)⁻¹ =
        (QSub.zeta e * QSub.zeta e) * q * (QSub.zeta e * QSub.zeta e)⁻¹ := by group
    rw [h2, hz2, hzq, mul_inv_cancel_right]
  rw [hrhs, ← hu q hq] at h1
  have h3 : t * u * q = (t * (u * q * u⁻¹) * t⁻¹) * (t * u) := by group
  rw [h3, h1]

end Gen

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.ne_tu_of_mem_cls (hs : Z2SetR r n R S t J u R₀ T₀ P) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y} (hy : IsUniqueInvolution L y) :
    y ≠ t * u := by
  intro h
  obtain ⟨c, rfl⟩ := hL
  have hc : y = c * t * c⁻¹ := hy.eq (hs.large.datum.isUniqueInvolution_core.conj c)
  apply hs.tu_not_conj c⁻¹
  rw [← h, hc]
  group

theorem false_of_Ry_cent_t (hr : 4 ≤ r)
    {L V : Subgroup Y} (hV : IsSylow2In V (L ⊓ Subgroup.centralizer ({t} : Set Y)))
    {Ry : Subgroup Y} (hRy : IsSylow2In Ry L) (hVc : Nat.card ↥V = 2 ^ (r - 1))
    (hRyc : Nat.card ↥Ry = 2 ^ r) (hRyt : ∀ q ∈ Ry, t * q * t⁻¹ = q) : False := by
  have hRyle : Ry ≤ L ⊓ Subgroup.centralizer ({t} : Set Y) := le_inf hRy.1 fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hRyt q hq)).symm
  have hle := hV.natCard_le hRy.2.1 hRyle
  rw [hVc, hRyc] at hle
  have hlt : 2 ^ (r - 1) < 2 ^ r := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem Z2SetR.false_of_Ry_cent_a (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y} (hyL : IsUniqueInvolution L y)
    (hyP : y ∈ (P : Subgroup Y)) (hyt : y ≠ t) {V : Subgroup Y}
    (hV : IsSylow2In V (L ⊓ Subgroup.centralizer ({t} : Set Y))) (hVc : Nat.card ↥V = 2 ^ (r - 1))
    {Ry : Subgroup Y} (hRy : IsSylow2In Ry L) (hRyc : Nat.card ↥Ry = 2 ^ r)
    (hRya : ∀ q ∈ Ry, (t * u) * q = q * (t * u)) : False := by
  have hW4 : 2 < Nat.card ↥Ry := by
    rw [hRyc]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hyE := hs.mem_E_of_two_lt_card hr h1 hL hyL hyP hRy.2.1 hRy.1
    (fun q hq => Subgroup.mem_centralizer_singleton_iff.mpr (hRya q hq).symm) hW4
  have hVlt : Nat.card ↥V < 2 ^ r := by
    rw [hVc]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hyu : y ≠ u := hs.ne_u_of_natCard_lt hr hL hyL hV hVlt
  rcases mem_closure_pair_cases hs.t2 hs.u2 hs.tu_comm hyE with h | h | h | h
  · exact hyL.ne_one h
  · exact hyt h
  · exact hyu h
  · exact hs.ne_tu_of_mem_cls hL hyL h

theorem Z2SetR.false_of_Ry_cent_u (hs : Z2SetR r n R S t J u R₀ T₀ P) (hr : 4 ≤ r)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) {y : Y}
    (hyL : IsUniqueInvolution L y) (hyu : y ≠ u) {Ry : Subgroup Y} (hRy : IsSylow2In Ry L)
    (e : ↥Ry ≃* QuaternionGroup (2 ^ (r - 2)))
    (hRyu : ∀ q ∈ Ry, u * q * u⁻¹ = q) (htζ : t * QSub.zeta e = QSub.zeta e * t)
    (htR : ∀ q ∈ Ry, t * q * t⁻¹ = QSub.zeta e * q * (QSub.zeta e)⁻¹) : False := by
  have hRyuC : Ry ≤ Subgroup.centralizer ({u} : Set Y) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc q * u = (u * q * u⁻¹) * u := by rw [hRyu q hq]
        _ = u * q := by group)
  have hLJ : L ≠ J := by
    rintro rfl
    exact hyu (hyL.eq hs.hu)
  have hLn := hs.mem_omegaNbr_J_of_isSylow2In hL hLJ hRy hRyuC
  have hRyΛ : Ry ≤ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    hs.le_linkLayerAt_of_le hLn hRy.2.1 hRy.1 hRyuC
  have hζR : QSub.zeta e ∈ Ry := QSub.zeta_mem e
  have hcΛ : (QSub.zeta e)⁻¹ * t ∈ linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hRyΛ hζR)) hs.t_mem_linkLayerAt
  have hcR : ∀ q ∈ Ry, ((QSub.zeta e)⁻¹ * t) * q = q * ((QSub.zeta e)⁻¹ * t) := by
    intro q hq
    calc (QSub.zeta e)⁻¹ * t * q = (QSub.zeta e)⁻¹ * (t * q * t⁻¹) * t := by group
      _ = (QSub.zeta e)⁻¹ * (QSub.zeta e * q * (QSub.zeta e)⁻¹) * t := by rw [htR q hq]
      _ = q * ((QSub.zeta e)⁻¹ * t) := by group
  have hζ2 : QSub.zeta e ^ 2 = quatInvolution r e := by
    rw [pow_two]
    exact QSub.zeta_mul_self e hr
  have hz2 : quatInvolution r e ^ 2 = 1 := by
    rw [pow_two]
    exact quatInvolution_sq hr e
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    exact hs.t2
  have hζ4 : QSub.zeta e ^ 4 = 1 := by
    calc QSub.zeta e ^ 4 = (QSub.zeta e ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [hζ2, hz2]
  have hcom : Commute (QSub.zeta e)⁻¹ t :=
    Commute.inv_left (show Commute (QSub.zeta e) t from htζ.symm)
  have hc2 : ∃ k : ℕ, ((QSub.zeta e)⁻¹ * t) ^ 2 ^ k = 1 := by
    refine ⟨2, ?_⟩
    calc ((QSub.zeta e)⁻¹ * t) ^ 2 ^ 2 = ((QSub.zeta e)⁻¹ * t) ^ 4 := by norm_num
      _ = ((QSub.zeta e)⁻¹) ^ 4 * t ^ 4 := hcom.mul_pow 4
      _ = 1 := by
        rw [inv_pow, hζ4, inv_one, one_mul, show t ^ 4 = (t ^ 2) ^ 2 by rw [← pow_mul], ht2,
          one_pow]
  rcases cent_a_two_of_concl hr hRyΛ hRy.2.1 e (hs.centAConcl_u hr) hcΛ hcR hc2 with h | h
  ·
    have hζt : QSub.zeta e = t := inv_mul_eq_one.mp h
    apply quatInvolution_ne_one hr e
    rw [← QSub.zeta_mul_self e hr, hζt]
    exact hs.t2
  ·
    have htz : t = QSub.zeta e * quatInvolution r e := by
      rw [← h]
      group
    have hcomm : QSub.zeta e * quatInvolution r e = quatInvolution r e * QSub.zeta e :=
      quatInvolution_comm hr e hζR
    have h1 := hs.t2
    rw [htz] at h1
    have h2 : (QSub.zeta e * quatInvolution r e) * (QSub.zeta e * quatInvolution r e) =
        (QSub.zeta e * QSub.zeta e) * (quatInvolution r e * quatInvolution r e) := by
      calc (QSub.zeta e * quatInvolution r e) * (QSub.zeta e * quatInvolution r e) =
          QSub.zeta e * (quatInvolution r e * QSub.zeta e) * quatInvolution r e := by group
        _ = QSub.zeta e * (QSub.zeta e * quatInvolution r e) * quatInvolution r e := by
          rw [← hcomm]
        _ = (QSub.zeta e * QSub.zeta e) * (quatInvolution r e * quatInvolution r e) := by group
    rw [h2, quatInvolution_sq hr e, mul_one, QSub.zeta_mul_self e hr] at h1
    exact quatInvolution_ne_one hr e h1

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

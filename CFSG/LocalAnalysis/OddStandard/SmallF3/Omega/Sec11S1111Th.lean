module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S105S
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111V4

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

@[expose] def secTheta (t z : G) (R : Subgroup G) : Set G :=
  {s | s ∈ R ∧ ∃ h ∈ centralizer ({z} : Set G), s = h⁻¹ * t * h}

theorem sec11_R_le_H [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) :
    R ≤ centralizer ({z} : Set G) :=
  hctx.sylowR.1.trans (sec11_normalizer_Q_le_centralizer_z hp hctx.toSec10Ctx)

theorem sec11_t_mem_R [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : t ∈ R :=
  (Subgroup.mem_inf.mp (sec11_t_mem_D hp hctx)).2

theorem sec11_z_mem_R [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : z ∈ R :=
  (Subgroup.mem_inf.mp (sec11_z_mem_D hp hctx)).2

theorem sec11_closure_Theta_le_R (t z : G) (R : Subgroup G) :
    Subgroup.closure (secTheta t z R) ≤ R := by
  rw [Subgroup.closure_le]
  intro s hs
  simp only [secTheta, Set.mem_setOf_eq] at hs
  exact hs.1

theorem sec11_t_mem_Theta [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R) : t ∈ secTheta t z R := by
  refine ⟨sec11_t_mem_R hp hctx, 1, Subgroup.one_mem _, ?_⟩
  simp

theorem sec11_tz_mem_Theta [Finite G] (hp : Asc82Pre11) (h111N : Asc82Lemma111N) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : t * z ∈ secTheta t z R := by
  have hclass : t * z ∈ conjClassIn T t := by
    rw [(h111N G t L S z K1 K2 T R hctx).2.1]
    simp
  obtain ⟨τ, hτT, hτ⟩ := hclass
  refine ⟨R.mul_mem (sec11_t_mem_R hp hctx) (sec11_z_mem_R hp hctx), τ⁻¹, ?_, ?_⟩
  · exact sec11_R_le_H hp hctx (R.inv_mem (hctx.T_le hτT))
  · rw [inv_inv]
    exact hτ

theorem sec11_z_mem_closure_Theta [Finite G] (hp : Asc82Pre11) (h111N : Asc82Lemma111N) {t : G}
    {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) : z ∈ Subgroup.closure (secTheta t z R) := by
  have ht2 : t * t = 1 := (sec10D_basic hp.basic hctx.toSec10Ctx).1
  have hz : z = t * (t * z) := by rw [← mul_assoc, ht2, one_mul]
  have hmem : t * (t * z) ∈ Subgroup.closure (secTheta t z R) :=
    Subgroup.mul_mem _
      (Subgroup.subset_closure (sec11_t_mem_Theta hp hctx))
      (Subgroup.subset_closure (sec11_tz_mem_Theta hp h111N hctx))
  exact (congrArg (fun y => y ∈ Subgroup.closure (secTheta t z R)) hz.symm).mp hmem

theorem sec11_Theta_conj {t z : G} {R : Subgroup G} (hRH : R ≤ centralizer ({z} : Set G)) :
    ∀ s ∈ secTheta t z R, ∀ u ∈ Subgroup.closure (secTheta t z R),
      u * s * u⁻¹ ∈ secTheta t z R := by
  intro s hs u hu
  simp only [secTheta, Set.mem_setOf_eq] at hs
  obtain ⟨hsR, h, hhH, rfl⟩ := hs
  have huR : u ∈ R := sec11_closure_Theta_le_R t z R hu
  have huH : u ∈ centralizer ({z} : Set G) := hRH huR
  refine ⟨R.mul_mem (R.mul_mem huR hsR) (R.inv_mem huR), h * u⁻¹, ?_, ?_⟩
  · exact (centralizer ({z} : Set G)).mul_mem hhH ((centralizer ({z} : Set G)).inv_mem huH)
  · group

theorem sec11_Theta_order [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 : Subgroup G}
    (hctx : Sec10Ctx G t L S z K1 K2) (R : Subgroup G) :
    ∀ s ∈ secTheta t z R, orderOf s = 2 := by
  intro s hs
  simp only [secTheta, Set.mem_setOf_eq] at hs
  obtain ⟨-, h, -, rfl⟩ := hs
  have h1 : orderOf ((MulAut.conj h⁻¹) t) = orderOf t := MulEquiv.orderOf_eq _ _
  have h2 : (MulAut.conj h⁻¹) t = h⁻¹ * t * h := by rw [MulAut.conj_apply, inv_inv]
  rw [← h2, h1]
  exact hctx.involution

theorem sec11_Theta_not_z [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) (R : Subgroup G) :
    z ∉ secTheta t z R := by
  intro hz
  simp only [secTheta, Set.mem_setOf_eq] at hz
  obtain ⟨-, h, -, heq⟩ := hz
  have ht : t = h * z * h⁻¹ := by
    rw [heq]
    group
  exact sec10_not_conj_z hp.s3.l37 hctx h⁻¹ (by rw [inv_inv]; exact ht.symm)

theorem sec11_isDih2_card {P : Subgroup G} (h : IsDih2 P) : Nat.card ↥P = 4 ∨ 8 ≤ Nat.card ↥P := by
  obtain ⟨m, hm1, ⟨e⟩⟩ := h
  have hcard : Nat.card ↥P = 2 * 2 ^ m := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rcases eq_or_lt_of_le hm1 with hm | hm
  · left
    rw [hcard, ← hm]
    norm_num
  · right
    rw [hcard]
    have h4 : 4 ≤ 2 ^ m := by
      have h := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hm
      norm_num at h
      exact h
    calc 8 = 2 * 4 := by norm_num
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 h4

theorem sec11_strClosed_of_card_four [Finite G] (hp : Asc82Pre11) (h111N : Asc82Lemma111N)
    {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hcard : Nat.card ↥(Subgroup.closure (secTheta t z R)) = 4) : IsStrClosedModZ t z R := by
  obtain ⟨ht2, hz2, ht1, hz1, hne, htz⟩ := sec10D_basic hp.basic hctx.toSec10Ctx
  intro h hhH hmem
  have htD : t ∈ Subgroup.closure (secTheta t z R) :=
    Subgroup.subset_closure (sec11_t_mem_Theta hp hctx)
  have hzD : z ∈ Subgroup.closure (secTheta t z R) :=
    sec11_z_mem_closure_Theta hp h111N hctx
  have hVle : zpowers t ⊔ zpowers z ≤ Subgroup.closure (secTheta t z R) :=
    sup_le (Subgroup.zpowers_le.mpr htD) (Subgroup.zpowers_le.mpr hzD)
  have hVcard : Nat.card ↥(zpowers t ⊔ zpowers z) = 4 :=
    sec11_V4_card ht2 hz2 htz ht1 hz1 hne
  have hVeq : zpowers t ⊔ zpowers z = Subgroup.closure (secTheta t z R) :=
    Subgroup.eq_of_le_of_card_ge hVle (le_of_eq (hcard.trans hVcard.symm))
  have hsup : R ⊔ zpowers z = R :=
    sup_eq_left.mpr (Subgroup.zpowers_le.mpr (sec11_z_mem_R hp hctx))
  have hmemR : h⁻¹ * t * h ∈ R := by
    have h' := hmem
    rwa [hsup] at h'
  have hTh : h⁻¹ * t * h ∈ secTheta t z R := ⟨hmemR, h, hhH, rfl⟩
  have hmemD : h⁻¹ * t * h ∈ Subgroup.closure (secTheta t z R) := Subgroup.subset_closure hTh
  rw [← hVeq] at hmemD
  rcases (sec11_V4_mem ht2 hz2 htz).mp hmemD with h1 | ht | hz | htz'
  · exfalso
    have ht_eq1 : t = 1 := by
      calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
        _ = h * 1 * h⁻¹ := by rw [h1]
        _ = 1 := by group
    exact ht1 ht_eq1
  · exact Or.inl ht
  · exfalso
    exact sec11_Theta_not_z hp hctx.toSec10Ctx R
      ⟨(congrArg (fun y => y ∈ R) hz).mp hmemR, h, hhH, hz.symm⟩
  · exact Or.inr htz'

end CFSG.OddStandard.SmallF3.Omega

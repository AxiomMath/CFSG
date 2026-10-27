module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109Da
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10TCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers2

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure T11Hyp [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 T R : Subgroup G) (h : G) :
    Prop where
  pre : Asc82Pre11
  ctx : Sec11Ctx G t L S z K1 K2 T R
  cent : h ∈ centralizer ({z} : Set G)
  mem : h⁻¹ * t * h ∈ S
  type : InducesTypeSome L (h⁻¹ * t * h) 5 1 2 1

variable [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G} {h : G}

theorem t11_cent_le_norm (hp : Asc82Pre11) (hctx : Sec10Ctx G t L S z K1 K2) :
    centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
  fun c hc => sec4_mem_normalizer hp.s3.l36 hctx.toSec10Z.toSec10Setting.toSec3SettingLB c hc

theorem t11_le_cent (hctx : Sec10Ctx G t L S z K1 K2) : L ≤ centralizer ({t} : Set G) :=
  hctx.component.le

private theorem t11_isPGroup_zpowers {a : G} (ha : a * a = 1) : IsPGroup 2 (zpowers a) := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])

theorem t11_invol_eq (hp : Asc82Pre11) (hctx : Sec10Ctx G t L S z K1 K2) {e : G}
    (heL : e ∈ centralizer (L : Set G)) (het : e * t = t * e) (he2 : e * e = 1) (he1 : e ≠ 1) :
    e = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heC : e ∈ centralizer ({t} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr het
  obtain ⟨c, hc, hcS⟩ := exists_conj_le_of_isSylow2Of hctx.sylow (t11_isPGroup_zpowers he2)
    (Subgroup.zpowers_le.mpr heC)
  have h1 : c * e * c⁻¹ ∈ S := hcS e (Subgroup.mem_zpowers e)
  have h2 : c * e * c⁻¹ ∈ centralizer (L : Set G) :=
    kl_centralizer_conj (t11_cent_le_norm hp hctx hc) heL
  have h3 : orderOf (c * e * c⁻¹) = 2 := by
    have e1 : c * e * c⁻¹ = (MulAut.conj c) e := by simp [MulAut.conj_apply]
    rw [e1, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact he2) he1
  have h4 := sec10T_invol_cent_eq hp.r10.l102 hp.basic hctx h1 h2 h3
  have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  calc e = c⁻¹ * (c * e * c⁻¹) * c := by group
    _ = c⁻¹ * t * c := by rw [h4]
    _ = c⁻¹ * (c * t) := by rw [mul_assoc, hct]
    _ = t := by group

theorem t11_conj_z (H : T11Hyp t L S z K1 K2 T R h) : h⁻¹ * z * h = z := by
  have e : h * z = z * h := Subgroup.mem_centralizer_singleton_iff.mp H.cent
  calc h⁻¹ * z * h = h⁻¹ * (z * h) := by group
    _ = h⁻¹ * (h * z) := by rw [e]
    _ = z := by group

theorem t11_ctx' (H : T11Hyp t L S z K1 K2 T R h) :
    Sec10Ctx G (h⁻¹ * t * h) (CFSG.conjugate L h) (CFSG.conjugate S h) z (CFSG.conjugate K1 h)
      (CFSG.conjugate K2 h) := by
  have h1 := H.ctx.toSec10Ctx.conjugate h
  rwa [t11_conj_z H] at h1

theorem t11_s_comm_t (H : T11Hyp t L S z K1 K2 T R h) :
    h⁻¹ * t * h * t = t * (h⁻¹ * t * h) :=
  Subgroup.mem_centralizer_singleton_iff.mp (H.ctx.sylow.1 H.mem)

theorem t11_s_sq (H : T11Hyp t L S z K1 K2 T R h) : h⁻¹ * t * h * (h⁻¹ * t * h) = 1 := by
  obtain ⟨ht2, -⟩ := sec10D_basic H.pre.basic H.ctx.toSec10Ctx
  calc h⁻¹ * t * h * (h⁻¹ * t * h) = h⁻¹ * (t * t) * h := by group
    _ = 1 := by rw [ht2]; group

theorem t11_s_ne_one (H : T11Hyp t L S z K1 K2 T R h) : h⁻¹ * t * h ≠ 1 := by
  obtain ⟨-, -, ht1, -⟩ := sec10D_basic H.pre.basic H.ctx.toSec10Ctx
  intro e
  apply ht1
  calc t = h * (h⁻¹ * t * h) * h⁻¹ := by group
    _ = 1 := by rw [e]; group

theorem t11_s_norm (H : T11Hyp t L S z K1 K2 T R h) : h⁻¹ * t * h ∈ normalizer (L : Set G) :=
  (H.pre.basic G t L S z H.ctx.toSec10Ctx.toSec10Z).2.2.2.2.1 H.mem

theorem t11_s_not_inner (H : T11Hyp t L S z K1 K2 T R h) :
    h⁻¹ * t * h ∉ L ⊔ centralizer (L : Set G) := by
  have hpsp := (H.pre.basic G t L S z H.ctx.toSec10Ctx.toSec10Z).1
  have hss : h⁻¹ * t * h * (h⁻¹ * t * h) ∈ centralizer (L : Set G) := by
    rw [t11_s_sq H]
    exact Subgroup.one_mem _
  exact (H.pre.facts.factsC.ty G L hpsp _ (t11_s_norm H) hss).2 (Or.inl H.type)

theorem t11_s_ne_t (H : T11Hyp t L S z K1 K2 T R h) :
    h⁻¹ * t * h ≠ t ∧ h⁻¹ * t * h ≠ t * z := by
  have htC := (H.pre.basic G t L S z H.ctx.toSec10Ctx.toSec10Z).2.1
  have hzL : z ∈ L := IsI4PlusIn.mem H.ctx.toSec10Ctx.toSec10Z.pocket
  have hn := t11_s_not_inner H
  refine ⟨fun e => hn ?_, fun e => hn ?_⟩
  · rw [e]
    exact Subgroup.mem_sup_right htC
  · rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right htC) (Subgroup.mem_sup_left hzL)

theorem t11_psp' (H : T11Hyp t L S z K1 K2 T R h) : IsPSp43 (CFSG.conjugate L h) :=
  (H.pre.basic _ _ _ _ _ (t11_ctx' H).toSec10Z).1

theorem t11_norm' (H : T11Hyp t L S z K1 K2 T R h) :
    centralizer ({h⁻¹ * t * h} : Set G) ≤ normalizer ((CFSG.conjugate L h : Subgroup G) : Set G) :=
  t11_cent_le_norm H.pre (t11_ctx' H)

theorem t11_le_cent' (H : T11Hyp t L S z K1 K2 T R h) :
    CFSG.conjugate L h ≤ centralizer ({h⁻¹ * t * h} : Set G) :=
  t11_le_cent (t11_ctx' H)

theorem t11_invol_eq' (H : T11Hyp t L S z K1 K2 T R h) {e : G}
    (heL : e ∈ centralizer ((CFSG.conjugate L h : Subgroup G) : Set G))
    (hes : e * (h⁻¹ * t * h) = h⁻¹ * t * h * e) (he2 : e * e = 1) (he1 : e ≠ 1) :
    e = h⁻¹ * t * h :=
  t11_invol_eq H.pre (t11_ctx' H) heL hes he2 he1

theorem t11_z_i4p' (H : T11Hyp t L S z K1 K2 T R h) : IsI4PlusIn (CFSG.conjugate L h) z :=
  (t11_ctx' H).toSec10Z.pocket

end CFSG.OddStandard.SmallF3.Omega

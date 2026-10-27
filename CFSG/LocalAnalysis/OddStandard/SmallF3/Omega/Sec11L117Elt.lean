module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Fact
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L117Qg
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S118D2PA

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec11_twoCoreIn_map (φ : G ≃* G) (H H' : Subgroup G)
    (h : H.map φ.toMonoidHom = H') :
    twoCoreIn H' = (twoCoreIn H).map φ.toMonoidHom := by
  have key := CFSG.pCore_map_iso 2 ((MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr h))
  unfold twoCoreIn CFSG.inSubgroup
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem sec11_twoCoreIn_conj {K K' : Subgroup G} {a : G}
    (hK : CFSG.conjugate K a = K') {x : G} (hx : x ∈ twoCoreIn K) :
    a⁻¹ * x * a ∈ twoCoreIn K' := by
  have h : K.map (MulAut.conj a⁻¹).toMonoidHom = K' := hK
  rw [sec11_twoCoreIn_map (MulAut.conj a⁻¹) K K' h]
  refine Subgroup.mem_map.mpr ⟨x, hx, ?_⟩
  simp [MulAut.conj_apply]

private theorem sec11_conjugate_swap {K K' : Subgroup G} {a : G} (haa : a * a = 1)
    (h : CFSG.conjugate K a = K') : CFSG.conjugate K' a = K := by
  rw [← h]
  unfold CFSG.conjugate
  rw [Subgroup.map_map]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hid : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hainv,
      inv_inv, MonoidHom.id_apply]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [haa]; group
  rw [hid, Subgroup.map_id]

theorem sec11_a_T [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} {a x : G} (hax : Sec11Ax G t L S z K1 K2 T R a x) :
    a ∈ T ∧ a * a = 1 := by
  obtain ⟨hAS, -, -⟩ := sec126_isElemAb2_secA hp hax.toSec11Ctx.toSec10Z
  obtain ⟨-, haa, -⟩ := sec11d2_a_facts hp hax
  exact ⟨hax.toSec11Ctx.S_le (hAS hax.a_mem), haa⟩

theorem sec11_a_swap [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 T R : Subgroup G} {a x : G} (hax : Sec11Ax G t L S z K1 K2 T R a x) :
    (∀ q ∈ twoCoreIn K1, a * q * a⁻¹ ∈ twoCoreIn K2) ∧
      (∀ q ∈ twoCoreIn K2, a * q * a⁻¹ ∈ twoCoreIn K1) := by
  obtain ⟨-, haa, -⟩ := sec11d2_a_facts hp hax
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have hsw : CFSG.conjugate K1 a⁻¹ = K2 := by rw [hainv]; exact hax.swap
    have h := sec11_twoCoreIn_conj hsw hq
    simpa only [inv_inv] using h
  · have hsw : CFSG.conjugate K2 a⁻¹ = K1 := by
      rw [hainv]; exact sec11_conjugate_swap haa hax.swap
    have h := sec11_twoCoreIn_conj hsw hq
    simpa only [inv_inv] using h

theorem sec11_x_sq [Finite G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T R : Subgroup G}
    {a x : G} (hax : Sec11Ax G t L S z K1 K2 T R a x) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [hax.x_inv, pow_two] at h
  exact h

theorem sec11_x_C [Finite G] (hp : Asc82Pre11) (r : Asc82Res11a) {t : G} {L S : Subgroup G}
    {z : G} {K1 K2 T R : Subgroup G} {a x : G} (hax : Sec11Ax G t L S z K1 K2 T R a x) :
    ∀ c ∈ secCTQ K1 K2 T, x * c * x⁻¹ * c⁻¹ ∈ zpowers z := by
  intro c hc
  by_cases hC : secCTQ K1 K2 T = zpowers t ⊔ zpowers z
  · rw [hC] at hc
    have htY : t ∈ sec11Qg z x (⊤ : Subgroup G) := by
      obtain ⟨-, -, htz, -, -⟩ := sec11_invols hax.toSec11Ctx.toSec10Ctx
      refine ⟨trivial, htz, ?_⟩
      have hmem : x * t * x⁻¹ ∈ conjClassIn T t := ⟨x, hax.x_mem, rfl⟩
      have hclass := (r.l111N G t L S z K1 K2 T R hax.toSec11Ctx).2.1
      rw [hclass] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h
      · rw [h, mul_inv_cancel]
        exact (zpowers z).one_mem
      · rw [h]
        have hz_eq : (t * z) * t⁻¹ = z := by rw [htz]; group
        rw [hz_eq]
        exact Subgroup.mem_zpowers z
    have hzY : z ∈ sec11Qg z x (⊤ : Subgroup G) :=
      sec11_z_mem_Qg (Q := ⊤) trivial
        (sec11_T_cent_z hp hax.toSec11Ctx x hax.x_mem)
    have hsup : zpowers t ⊔ zpowers z ≤ sec11Qg z x (⊤ : Subgroup G) :=
      sup_le (Subgroup.zpowers_le.mpr htY) (Subgroup.zpowers_le.mpr hzY)
    have hcY := hsup hc
    rw [mem_sec11Qg_iff] at hcY
    exact hcY.2.2
  · have hcomm := hax.x_comm hC c hc
    have hone : x * c * x⁻¹ * c⁻¹ = 1 := by rw [hcomm]; group
    rw [hone]
    exact (zpowers z).one_mem

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LargeExtraspecial.S14Seven
public import CFSG.LargeExtraspecial.S6TwoD

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.Open CFSG.LargeExtraspecial.S4
open CFSG.RankThree.OrthogonalInvolutions

theorem eq_smul_id_of_commute_isometryGroup {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {β : LinearMap.BilinForm (ZMod 2) V} (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    {φ : V →ₗ[ZMod 2] V}
    (hcomm : ∀ e ∈ TauCeti.BilinForm.isometryGroup β, ∀ v, φ (e v) = e (φ v)) :
    ∃ c : ZMod 2, φ = c • (1 : Module.End (ZMod 2) V) := by
  refine LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent fun a => ?_
  by_cases ha : a = 0
  · rw [ha]
    exact fun h => h.ne_zero 0 rfl
  obtain ⟨x, hx⟩ : ∃ x, β x a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (hnd.2 a fun x => hcon x)
  have hx1 : β x a = 1 := by
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (β x a) with h | h
    · exact absurd h hx
    · exact h
  have h1 := hcomm _ (spTransvection_mem_isometryGroup hβ a) x
  rw [spTransvection_apply, spTransvection_apply, map_add, map_smul, hx1, one_smul,
    add_left_cancel_iff] at h1
  rw [LinearIndependent.pair_iff]
  intro h
  have := h (β (φ x) a) (-1) (by rw [h1, neg_one_smul, add_neg_cancel])
  exact absurd this.2 (by decide)

theorem apply_sub_mem_of_finrank_eq_succ {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {X Y : Submodule (ZMod 2) V} (hXY : X ≤ Y)
    (hdim : finrank (ZMod 2) Y = finrank (ZMod 2) X + 1) {e : V ≃ₗ[ZMod 2] V}
    (hX : ∀ v ∈ X, e v ∈ X) (hY : ∀ v ∈ Y, e v ∈ Y) {y : V} (hy : y ∈ Y) : e y - y ∈ X := by
  by_cases hyX : y ∈ X
  · exact X.sub_mem (hX y hyX) hyX
  have hlt : X < X ⊔ (ZMod 2) ∙ y := lt_of_le_of_ne le_sup_left fun h =>
    hyX (by rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
  have hle : X ⊔ (ZMod 2) ∙ y ≤ Y :=
    sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hy)
  have hspan : X ⊔ (ZMod 2) ∙ y = Y := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hmap : X.map e.toLinearMap = X :=
    Submodule.eq_of_le_of_finrank_eq (fun _ ⟨v, hv, hve⟩ => hve ▸ hX v hv)
      (LinearEquiv.finrank_map_eq e X)
  have hey : e y ∈ X ⊔ (ZMod 2) ∙ y := hspan ▸ hY y hy
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hey
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
  · exfalso
    rw [zero_smul, add_zero] at huw
    rw [← hmap] at hu
    obtain ⟨v, hv, hve⟩ := hu
    have : y = v := e.injective (by rw [← huw, ← hve]; rfl)
    exact hyX (this ▸ hv)
  · rw [← huw, one_smul, add_sub_cancel_right]
    exact hu

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem fix_Vt_of_commute (H : Hyp4 S g) {t x : S.O} (hx : ∀ r ∈ Rbar S g t, x * r = r * x)
    {v : S.Qt} (hv : v ∈ Vt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have hgen : ∀ h : S.M, t ∈ S.Lbar ((h : G) * g) →
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) =
        S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    intro h hth
    have hmem : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹)) ∈
        fixSub S (S.Lbar ((h : G) * g)) := by
      rw [mem_fixSub]
      intro s hs
      have hcs := (mem_fixSub S).mp (cl_mem_fixSub H h) s hs
      rw [← coe_mul_apply, ← hx s (Lbar_mul_le_Rbar hth hs), coe_mul_apply, hcs]
    refine eq_cl_of_mem_fixSub H h hmem fun h0 => cl_conj_ne_zero H h ?_
    exact (LinearEquiv.map_eq_zero_iff _).mp h0
  have hle : Vt S g t ≤ fixSpace (x : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [Vt, Submodule.span_le]
    rintro _ ⟨h, hth, rfl⟩
    exact mem_fixSpace.mpr (hgen h hth)
  exact mem_fixSpace.mp (hle hv)

theorem apply_sub_mem_Vt_of_fix_Wt {t x : S.O}
    (hfix : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) (q : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q ∈ Vt S g t := by
  set P := LinearMap.BilinForm.orthogonal S.q.polarBilin (Wt S g t) with hP
  have hVP : Vt S g t ≤ P := fun v hv => LinearMap.BilinForm.mem_orthogonal_iff.mpr
    fun w hw => by
      rw [polarBilin_apply_apply, polar_comm]
      exact mem_Wt.mp hw v hv
  have hdim : finrank (ZMod 2) P = finrank (ZMod 2) (Vt S g t) := by
    have h1 := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate (Wt S g t)
    have h2 := finrank_Wt (S := S) (g := g) (t := t)
    have h3 := Submodule.finrank_le (Wt S g t)
    rw [hP]
    omega
  have hPV : P = Vt S g t := (Submodule.eq_of_le_of_finrank_eq hVP hdim.symm).symm
  rw [← hPV, hP, LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  rw [polarBilin_apply_apply, polar_sub_right, sub_eq_zero]
  conv_lhs => rw [← hfix w hw]
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2]

theorem eq_bot_of_le_span_pair (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (h3 : 3 ≤ finrank (ZMod 2) (Vt S g t)) {b : S.Qt} {I : Submodule (ZMod 2) S.Qt}
    (hI : I ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ⊔ (ZMod 2) ∙ b)
    (hR : ∀ r ∈ Rbar S g t, ∀ u ∈ I, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ I) : I = ⊥ := by
  by_contra hne
  have ha : S.cl (g * S.z * g⁻¹) ∈ I :=
    S6.cl_mem_of_Lbar_invariant H (fun l hl v hv => hR l (Lbar_le_Rbar ht hl) v hv) hne
  have hV : Vt S g t ≤ I := by
    rw [Vt_eq_span_orbit H ht, Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    exact hR r hr _ ha
  have hle1 : ∀ v : S.Qt, finrank (ZMod 2) ((ZMod 2) ∙ v) ≤ 1 := fun v => by
    by_cases hv : v = 0
    · rw [hv, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton hv]
  have hs := Submodule.finrank_sup_add_finrank_inf_eq ((ZMod 2) ∙ S.cl (g * S.z * g⁻¹))
    ((ZMod 2) ∙ b)
  have := Submodule.finrank_mono (hV.trans hI)
  have := hle1 (S.cl (g * S.z * g⁻¹))
  have := hle1 b
  omega

theorem eq_zero_of_fix_Rbar (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) {h : S.M}
    (hh : S.ρ h ∈ Rbar S g t) (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g) {u : S.Qt}
    (hu : ∀ r ∈ Rbar S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) : u = 0 := by
  have hth := S6.mem_Lbar_of_pair H ht hh
  have ha : u ∈ fixSub S (S.Lbar g) := (mem_fixSub S).mpr fun l hl => hu l (Lbar_le_Rbar ht hl)
  have hb' : u ∈ fixSub S (S.Lbar ((h : G) * g)) :=
    (mem_fixSub S).mpr fun l hl => hu l (Lbar_mul_le_Rbar hth hl)
  rw [H.fixSub_eq, mem_span_cl_iff] at ha
  rw [fixSub_Lbar_mul H h, mem_span_cl_iff] at hb'
  rcases ha with h0 | rfl
  · exact h0
  rcases hb' with h0 | e
  · exact h0
  exfalso
  apply S6.cl_b_not_mem H hb
  rw [← e]
  exact S6.cl_mem_clSub_self H.conj_mem

theorem sub_mem_fixSub_of_commute {t x : S.O} (hx : ∀ r ∈ Rbar S g t, x * r = r * x)
    {K : Subgroup S.O} (hK : K ≤ Rbar S g t) {X : Submodule (ZMod 2) S.Qt}
    (hX : ∀ v ∈ X, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) {w : S.Qt}
    (hw : ∀ l ∈ K, (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ X) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ fixSub S K := by
  rw [mem_fixSub]
  intro l hl
  have hd := hX _ (hw l hl)
  rw [map_sub, ← coe_mul_apply, ← hx l (hK hl), coe_mul_apply]
  have e : (l : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ((l : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w) := by abel
  rw [e, map_add, hd]
  abel

theorem fix_Wt_of_commute_omega (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hΩ : OmegaCase H C ht ht1 hVQ) {x : S.O} (hx : ∀ r ∈ Rbar S g t, x * r = r * x)
    {w : S.Qt} (hw : w ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  have hV : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
    fix_Vt_of_commute H hx hv
  obtain ⟨h, hh, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  have hPI := S6.pairInt_of_radBound H C ht ht1 hVQ (S6.radBound_of_omegaCase H C ht ht1 hVQ hΩ)
  have hth := S6.mem_Lbar_of_pair H ht hh
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    omega
  set ψ : S.Qt →ₗ[ZMod 2] S.Qt := (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id with hψ
  have hψa : ∀ v, ψ v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := fun v => rfl
  have hI : (Wt S g t).map ψ ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ⊔
      (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [← S6.sup_eq_Wt H C ht ht1 hVQ hh hb (S6.pairInt_ab hh hb hPI), Submodule.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      rw [hψa]
      have := sub_mem_fixSub_of_commute hx (Lbar_le_Rbar ht) hV
        ((S6.forall_apply_sub_mem_Vt_iff_a H hNo C ht ht1 hVQ hh hb hPI hv.2).mpr
          (Submodule.mem_sup_left hv))
      rwa [H.fixSub_eq] at this
    · rintro _ ⟨v, hv, rfl⟩
      rw [hψa]
      have := sub_mem_fixSub_of_commute hx (fun l hl => Lbar_mul_le_Rbar hth hl) hV
        ((S6.forall_apply_sub_mem_Vt_iff_b H hNo C ht ht1 hVQ hh hb hPI hv.2).mpr
          (Submodule.mem_sup_left hv))
      rwa [fixSub_Lbar_mul H h] at this
  have hIR : ∀ r ∈ Rbar S g t, ∀ u ∈ (Wt S g t).map ψ,
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ (Wt S g t).map ψ := by
    rintro r hr _ ⟨v, hv, rfl⟩
    refine ⟨(r : S.Qt ≃ₗ[ZMod 2] S.Qt) v, apply_mem_Wt H hr hv, ?_⟩
    rw [hψa, hψa, map_sub, ← coe_mul_apply, ← coe_mul_apply, hx r hr]
  have hI0 := eq_bot_of_le_span_pair H ht h3 hI hIR
  have hmem : ψ w ∈ (Wt S g t).map ψ := ⟨w, hw, rfl⟩
  rw [hI0, Submodule.mem_bot, hψa, sub_eq_zero] at hmem
  exact hmem

theorem fix_Wt_of_commute_sp (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hSp : SpCase H C ht ht1 hVQ) {x : S.O} (hx : ∀ r ∈ Rbar S g t, x * r = r * x)
    {w : S.Qt} (hw : w ∈ Wt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  have hV : ∀ v ∈ Vt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := fun v hv =>
    fix_Vt_of_commute H hx hv
  obtain ⟨h, hh, hb⟩ := S6.exists_pair H C ht ht1 hVQ
  have hth := S6.mem_Lbar_of_pair H ht hh
  have h3 : 3 ≤ finrank (ZMod 2) (Vt S g t) := by
    have := four_le_finrank_Vt H C ht ht1 hVQ hNo
    omega
  obtain ⟨h1R, hb1⟩ := S6.pair_one (t := t) hb
  have hab : g * S.z * g⁻¹ ≠ (h : G) * g * S.z * ((h : G) * g)⁻¹ := fun e =>
    hb (e ▸ S.conj_z_mem_Qa g)
  have hba : ((1 : S.M) : G) * g * S.z * (((1 : S.M) : G) * g)⁻¹ ∉ S.Qa ((h : G) * g) := by
    simpa using fun hmem => hb (S.mem_Qa_symm hab hmem)
  set ψ : S.Qt →ₗ[ZMod 2] S.Qt := (x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id with hψ
  have hψa : ∀ v, ψ v = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v := fun v => rfl
  have hψr : ∀ r ∈ Rbar S g t, ∀ v,
      ψ ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = (r : S.Qt ≃ₗ[ZMod 2] S.Qt) (ψ v) := by
    intro r hr v
    rw [hψa, hψa, map_sub, ← coe_mul_apply, ← coe_mul_apply, hx r hr]
  have hstep : ∀ {X Y : Submodule (ZMod 2) S.Qt}, (∀ v ∈ X, ψ v = 0) →
      (∀ r ∈ Rbar S g t, ∀ y ∈ Y, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y ∈ X) →
      ∀ y ∈ Y, ψ y = 0 := by
    intro X Y hX hXY y hy
    refine eq_zero_of_fix_Rbar H ht hh hb fun r hr => ?_
    rw [← hψr r hr]
    have e : (r : S.Qt ≃ₗ[ZMod 2] S.Qt) y = y + ((r : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) := by abel
    rw [e, map_add, hX _ (hXY r hr y hy), add_zero]
  have hV1 : ∀ v ∈ S6.Vone S g t g ((h : G) * g), ψ v = 0 :=
    hstep (fun v hv => by rw [hψa, hV v hv, sub_self]) fun r hr y hy =>
      apply_sub_mem_of_finrank_eq_succ (S6.Vt_le_Vone _ _)
        (S6.finrank_Vone_eq' hCE H hNo C ht ht1 hVQ hSp hh hb)
        (fun u hu => apply_mem_Vt_of_mem_Rbar H.conj_mem hr hu)
        (fun u hu => S6.apply_mem_Vone hCE H hNo C ht ht1 hVQ hSp hh hb hr hu) hy
  have hV1' : ∀ v ∈ S6.Vone S g t g ((h : G) * g), (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v :=
    fun v hv => by have := hV1 v hv; rwa [hψa, sub_eq_zero] at this
  have hW1 := S6.Wone_eq_sup hCE H hNo C ht ht1 hVQ hSp hh hb
  have hI : (S6.Wone S g t g ((h : G) * g)).map ψ ≤ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ⊔
      (ZMod 2) ∙ S.cl ((h : G) * g * S.z * ((h : G) * g)⁻¹) := by
    rw [← hW1, Submodule.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      have hvW : v ∈ S6.Wone S g t g ((h : G) * g) := hW1 ▸ Submodule.mem_sup_left hv
      have key := S6.forall_apply_sub_mem_Vone_iff hCE H hNo C ht ht1 hVQ hSp hh hb h1R hh hb1 hvW
      simp only [OneMemClass.coe_one, one_mul] at key
      rw [hψa]
      have := sub_mem_fixSub_of_commute hx (Lbar_le_Rbar ht) hV1'
        (key.mpr (Submodule.mem_sup_left ⟨hv.1, hvW⟩))
      rwa [H.fixSub_eq] at this
    · rintro _ ⟨v, hv, rfl⟩
      have hvW : v ∈ S6.Wone S g t g ((h : G) * g) := hW1 ▸ Submodule.mem_sup_right hv
      have key := S6.forall_apply_sub_mem_Vone_iff hCE H hNo C ht ht1 hVQ hSp hh hb hh h1R hba hvW
      rw [hψa]
      have := sub_mem_fixSub_of_commute hx (fun l hl => Lbar_mul_le_Rbar hth hl) hV1'
        (key.mpr (Submodule.mem_sup_left ⟨hv.1, hvW⟩))
      rwa [fixSub_Lbar_mul H h] at this
  have hIR : ∀ r ∈ Rbar S g t, ∀ u ∈ (S6.Wone S g t g ((h : G) * g)).map ψ,
      (r : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ (S6.Wone S g t g ((h : G) * g)).map ψ := by
    rintro r hr _ ⟨v, hv, rfl⟩
    exact ⟨(r : S.Qt ≃ₗ[ZMod 2] S.Qt) v,
      S6.apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hr hv, hψr r hr v⟩
  have hI0 := eq_bot_of_le_span_pair H ht h3 hI hIR
  have hW1z : ∀ v ∈ S6.Wone S g t g ((h : G) * g), ψ v = 0 := fun v hv => by
    have hmem : ψ v ∈ (S6.Wone S g t g ((h : G) * g)).map ψ := ⟨v, hv, rfl⟩
    rwa [hI0, Submodule.mem_bot] at hmem
  have hz := hstep hW1z (fun r hr y hy =>
    apply_sub_mem_of_finrank_eq_succ (S6.Wone_le_Wt _ _)
      (S6.finrank_Wone_eq hCE H hNo C ht ht1 hVQ hSp hh hb).symm
      (fun u hu => S6.apply_mem_Wone hCE H hNo C ht ht1 hVQ hSp hh hb hr hu)
      (fun u hu => apply_mem_Wt H hr hu) hy) w hw
  rwa [hψa, sub_eq_zero] at hz

theorem eq_smul_of_commute_RmodN (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ)
    (h4 : 4 ≤ finrank (ZMod 2) (Vt S g t)) {φ : Vt S g t →ₗ[ZMod 2] Vt S g t}
    (hφ : ∀ e ∈ RmodN S g t, ∀ v, φ (e v) = e (φ v)) :
    ∃ c : ZMod 2, φ = c • LinearMap.id := by
  rcases hcase with hΩ | hSp
  · obtain ⟨Q, hQ, -, hX, -, -⟩ := hΩ.exists_form
    exact S2.timmesfeld_2_4_omegaGroup hQ h4 fun e he v => hφ e (by rw [hX]; exact he) v
  · exact eq_smul_id_of_commute_isometryGroup (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) fun e he v => hφ e (by rw [hSp.eq_sp]; exact he) v

theorem mem_zpowers_of_commute (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g)
    (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hcase : OmegaCase H C ht ht1 hVQ ∨ SpCase H C ht ht1 hVQ)
    {x : S.O} (hx : ∀ r ∈ Rbar S g t, x * r = r * x) : x ∈ zpowers t := by
  have hW : ∀ w ∈ Wt S g t, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := fun w hw =>
    hcase.elim (fun hΩ => fix_Wt_of_commute_omega H hNo C ht ht1 hVQ hΩ hx hw)
      (fun hSp => fix_Wt_of_commute_sp hCE H hNo C ht ht1 hVQ hSp hx hw)
  set f : S.Qt →ₗ[ZMod 2] Vt S g t := LinearMap.codRestrict (Vt S g t)
    ((x : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - LinearMap.id) (apply_sub_mem_Vt_of_fix_Wt hW)
    with hfdef
  have hf : ∀ q, (f q : S.Qt) = (x : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q := fun q => rfl
  have hfW : Wt S g t ≤ LinearMap.ker f := fun w hw => by
    rw [LinearMap.mem_ker]
    exact Subtype.ext (by rw [hf, hW w hw, sub_self]; rfl)
  set φ : Vt S g t →ₗ[ZMod 2] Vt S g t :=
    ((Wt S g t).liftQ f hfW).comp (chi H C ht ht1 hVQ).symm.toLinearMap with hφdef
  have hφχ : ∀ q, φ (chi H C ht ht1 hVQ (Submodule.Quotient.mk q)) = f q := fun q => by
    rw [hφdef, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      Submodule.liftQ_apply]
  have hcomm : ∀ e ∈ RmodN S g t, ∀ v, φ (e v) = e (φ v) := by
    intro e he v
    rw [← range_resV H.conj_mem t] at he
    obtain ⟨r, rfl⟩ := he
    obtain ⟨q', hq'⟩ := (chi H C ht ht1 hVQ).surjective v
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ q'
    rw [← hq', ← chi_equivariant H C ht ht1 hVQ r q, hφχ, hφχ]
    apply Subtype.ext
    rw [hf, coe_resV_apply, hf, map_sub, ← coe_mul_apply, ← coe_mul_apply, hx r r.2]
  have h4 : 4 ≤ finrank (ZMod 2) (Vt S g t) := four_le_finrank_Vt H C ht ht1 hVQ hNo
  obtain ⟨c, hc⟩ := eq_smul_of_commute_RmodN H C ht ht1 hVQ hcase h4 hcomm
  have key : ∀ q, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q = c • ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) q - q) := by
    intro q
    have h1 := congrArg (fun ψ : Vt S g t →ₗ[ZMod 2] Vt S g t =>
      ((ψ (chi H C ht ht1 hVQ (Submodule.Quotient.mk q)) : Vt S g t) : S.Qt)) hc
    simp only [hφχ, hf, LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul,
      coe_chi_apply_mk] at h1
    exact h1
  rcases CFSG.RankThree.Literature.FSmith.zmod2_cases c with rfl | rfl
  · have hx1 : x = 1 := Subtype.ext (LinearEquiv.ext fun q => by
      have := key q
      rwa [zero_smul, sub_eq_zero] at this)
    rw [hx1]
    exact one_mem _
  · have hxt : x = t := Subtype.ext (LinearEquiv.ext fun q => by
      have := key q
      rwa [one_smul, sub_left_inj] at this)
    rw [hxt]
    exact mem_zpowers t

theorem centRbarStmt (hCE : CentralExtInput.{0}) : CentRbarStmt := by
  intro G _ _ _ S g t c hSt hocc _ x _ hx
  obtain ⟨H, C, ht, ht1, hVQ, hcase, -⟩ := case_of_occurs hocc
  have hNo : NoA2 S g := fun α h1 h2 h3 =>
    hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩
  exact mem_zpowers_of_commute hCE H hNo C ht ht1 hVQ hcase hx

theorem claim14_7 (hCE : CentralExtInput.{0}) : Claim14_7 :=
  claim14_7_of hCE (centRbarStmt hCE)

end CFSG.LargeExtraspecial.S14

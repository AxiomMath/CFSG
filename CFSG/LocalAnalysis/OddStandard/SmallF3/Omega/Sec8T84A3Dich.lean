module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Tr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Act
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
  {B K L1 : Subgroup G}

open Classical in
@[expose] noncomputable def qt (t : G) (B L1 : Subgroup G) (b : ↥B) : ↥B :=
  if hb : ∃ l ∈ L1, tauFn t l = (b : G) ∧ l * l ∈ B then
    ⟨hb.choose * hb.choose, hb.choose_spec.2.2⟩ else 1

theorem qt_eq (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) {l : G}
    (hl : l ∈ L1) {b : ↥B} (hb : tauFn t l = (b : G)) : ((qt t B L1 b : ↥B) : G) = l * l := by
  have hex : ∃ l' ∈ L1, tauFn t l' = (b : G) ∧ l' * l' ∈ B :=
    ⟨l, hl, hb, h.K_data.sq_le l (h.le hl)⟩
  unfold qt
  rw [dif_pos hex]
  exact sq_eq_of_tau_eq hctx h hex.choose_spec.1 hl (hex.choose_spec.2.1.trans hb.symm)

theorem qt_one (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) :
    qt t B L1 1 = 1 := by
  apply Subtype.ext
  have h1 := qt_eq hctx h (l := 1) L1.one_mem (b := 1) (by simp [tauFn])
  simpa using h1

theorem qt_quad (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1)
    (x y z' : ↥B) :
    qt t B L1 (x * y * z') * qt t B L1 x * qt t B L1 y * qt t B L1 z' =
      qt t B L1 (x * y) * qt t B L1 (x * z') * qt t B L1 (y * z') := by
  obtain ⟨a, ha, hax⟩ := tau_exists hctx h x.2
  obtain ⟨b, hb, hby⟩ := tau_exists hctx h y.2
  obtain ⟨c, hc, hcz⟩ := tau_exists hctx h z'.2
  have hab : tauFn t (a * b) = ((x * y : ↥B) : G) := by
    rw [tau_mul_L1 h ha hb, hax, hby]; rfl
  have hac : tauFn t (a * c) = ((x * z' : ↥B) : G) := by
    rw [tau_mul_L1 h ha hc, hax, hcz]; rfl
  have hbc : tauFn t (b * c) = ((y * z' : ↥B) : G) := by
    rw [tau_mul_L1 h hb hc, hby, hcz]; rfl
  have habc : tauFn t (a * b * c) = ((x * y * z' : ↥B) : G) := by
    rw [tau_mul_L1 h (L1.mul_mem ha hb) hc, tau_mul_L1 h ha hb, hax, hby, hcz]; rfl
  have key := (cl2_of h.K_data).sq_cube (h.le ha) (h.le hb) (h.le hc)
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [qt_eq hctx h (L1.mul_mem (L1.mul_mem ha hb) hc) habc, qt_eq hctx h ha hax,
    qt_eq hctx h hb hby, qt_eq hctx h hc hcz, qt_eq hctx h (L1.mul_mem ha hb) hab,
    qt_eq hctx h (L1.mul_mem ha hc) hac, qt_eq hctx h (L1.mul_mem hb hc) hbc]
  simpa only [mul_assoc] using key

theorem isOm6M_ctx (hctx : Sec8Ctx G t L S z g B) : IsOm6M L :=
  ⟨hctx.toSec3SettingLB.component.isQuasisimple, hctx.omega6m⟩

theorem aut_B_of (F : Sec8T84Base) (hctx : Sec8Ctx G t L S z g B) :
    Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) ∧
      (∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 →
        ∃ n ∈ L ⊓ normalizer (B : Set G), n * b * n⁻¹ = b') ∧
      L ⊓ centralizer (B : Set G) = B ⊔ centerIn L := by
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLt : L ≤ centralizer ({t} : Set G) := hS.component.le
  have hNmem : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer F.h36 hS
  have hP : IsSylow2Of (S ⊓ L) L := sec4_isSylow2Of_inf hLt hNmem hctx.sylow
  have hBle : B ≤ S ⊓ L := by rw [inf_comm]; exact hctx.B_le
  exact F.hM.aut_B G L (isOm6M_ctx hctx) (S ⊓ L) hP B hBle hctx.B_e16

theorem qt_equiv (F : Sec8T84Base) (hctx : Sec8Ctx G t L S z g B)
    (h : Sec8T84L1 G t L S z g B K L1) {α : MulAut ↥B} (hα : α ∈ autIn L B) (x : ↥B) :
    qt t B L1 (α x) = α (qt t B L1 x) := by
  unfold autIn at hα
  obtain ⟨m, hmL, rfl⟩ := Subgroup.mem_map.mp hα
  have hmL' : (m : G) ∈ L := Subgroup.mem_subgroupOf.mp hmL
  obtain ⟨hmN, hmc⟩ := sec8t84a1_L_norm_le hctx ⟨hmL', m.2⟩
  have hnt : (m : G) * t = t * (m : G) := Subgroup.mem_centralizer_singleton_iff.mp hmc
  let n : ↥(Nsub8 t B) := ⟨(m : G), hmN⟩
  obtain ⟨l0, hlx⟩ : ∃ l0 : ↥L1, tauFn t (l0 : G) = (x : G) := by
    obtain ⟨l, hl, hlx⟩ := tau_exists hctx h x.2
    exact ⟨⟨l, hl⟩, hlx⟩
  have h1 : tauFn t ((RedAct.redHom (setup hctx h) n l0 : ↥L1) : G) =
      ((B.normalizerMonoidHom m x : ↥B) : G) := by
    rw [tauFn_rho F.h8A hctx h n hnt l0, hlx]
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe B m x).symm
  have hl' : ((RedAct.redHom (setup hctx h) n l0 : ↥L1) : G) ∈ L1 :=
    (RedAct.redHom (setup hctx h) n l0).2
  apply Subtype.ext
  rw [qt_eq hctx h hl' h1, rho_sq hctx h n m.2 l0,
    Subgroup.normalizerMonoidHom_apply_apply_coe, qt_eq hctx h l0.2 hlx]

theorem dich (F : Sec8T84Base) (hQ : Sec8T84FactQuad) (hctx : Sec8Ctx G t L S z g B)
    (h : Sec8T84L1 G t L S z g B K L1) :
    (∀ l ∈ L1, l * l = 1) ∨ (∀ l ∈ L1, l * l = tauFn t l) := by
  have hb : ∀ l ∈ L1, tauFn t l ∈ B := fun l hl =>
    (cl2_of h.K_data).tau_mem (t_mem_K h.K_data) (h.le hl)
  rcases hQ G B hctx.B_e16 (autIn L B) (aut_B_of F hctx).1 (qt t B L1) (qt_one hctx h)
      (fun _ hα x => qt_equiv F hctx h hα x) (qt_quad hctx h) with h1 | h1
  · left
    intro l hl
    have h2 := qt_eq hctx h hl (b := ⟨tauFn t l, hb l hl⟩) rfl
    have h3 := congrFun h1 ⟨tauFn t l, hb l hl⟩
    rw [h3] at h2
    simpa using h2.symm
  · right
    intro l hl
    have h2 := qt_eq hctx h hl (b := ⟨tauFn t l, hb l hl⟩) rfl
    have h3 := congrFun h1 ⟨tauFn t l, hb l hl⟩
    rw [h3] at h2
    exact h2.symm

end A3

end CFSG.OddStandard.SmallF3.Omega

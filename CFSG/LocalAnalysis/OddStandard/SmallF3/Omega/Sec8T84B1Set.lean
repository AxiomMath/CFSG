module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A1Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Red

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace B89

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}

theorem t_sq (hctx : Sec8Ctx G t L S z g B) : t * t = 1 := by
  rw [← pow_two, ← hctx.toSec3SettingLB.involution, pow_orderOf_eq_one]

theorem t_inv (hctx : Sec8Ctx G t L S z g B) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (t_sq hctx)

theorem B_le_E (hE : Sec8E G t L S z g B E) : B ≤ E := by
  rw [← hE.cent_t]
  exact inf_le_left

theorem B_le_Ct (hE : Sec8E G t L S z g B E) : B ≤ centralizer ({t} : Set G) := by
  rw [← hE.cent_t]
  exact inf_le_right

theorem E_comm (hE : Sec8E G t L S z g B E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm hE.elem.1 ha hb

theorem t_mem_X (hE : Sec8E G t L S z g B E) : t ∈ normalizer (E : Set G) := by
  have ht2 := t_sq hE.ctx
  have htinv := t_inv hE.ctx
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · exact hE.t_norm e
  · intro he
    have h2 := hE.t_norm (t * e * t⁻¹) he
    have h3 : t * (t * e * t⁻¹) * t⁻¹ = e := by
      rw [htinv]
      calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
        _ = e := by rw [ht2]; group
    rwa [h3] at h2

theorem mem_N_of_comm {x : G} (hxt : x * t = t * x) (hxB : x ∈ normalizer (B : Set G)) :
    x ∈ Nsub8 t B := by
  rw [Nsub8]
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have ht : (↑(MulAut.conj x) : G →* G) t = t := by
    change (MulAut.conj x) t = t
    rw [MulAut.conj_apply, hxt]
    group
  have hBmap : B.map (↑(MulAut.conj x) : G →* G) = B :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hxB
  rw [Asub8, Subgroup.map_sup, MonoidHom.map_zpowers, ht, hBmap]

theorem XCt_le_NB (hE : Sec8E G t L S z g B E) :
    normalizer (E : Set G) ⊓ centralizer ({t} : Set G) ≤ normalizer (B : Set G) := by
  have key : ∀ x ∈ normalizer (E : Set G) ⊓ centralizer ({t} : Set G), ∀ b ∈ B,
      x * b * x⁻¹ ∈ B := by
    intro x hx b hb
    obtain ⟨hxX, hxt⟩ := Subgroup.mem_inf.mp hx
    have hb' : b ∈ E ⊓ centralizer ({t} : Set G) := by rw [hE.cent_t]; exact hb
    have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxt
    have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp hb'.2
    have hxinv : x⁻¹ * t = t * x⁻¹ := by
      calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hxt']
        _ = t * x⁻¹ := by group
    rw [← hE.cent_t]
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hxX b).mp hb'.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (x * b * x⁻¹) * t = x * b * (x⁻¹ * t) := by group
      _ = x * b * (t * x⁻¹) := by rw [hxinv]
      _ = x * (b * t) * x⁻¹ := by group
      _ = x * (t * b) * x⁻¹ := by rw [hbt]
      _ = (x * t) * b * x⁻¹ := by group
      _ = (t * x) * b * x⁻¹ := by rw [hxt']
      _ = t * (x * b * x⁻¹) := by group
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨fun hb => key x hx b hb, fun hb => ?_⟩
  have h := key x⁻¹ (inv_mem hx) (x * b * x⁻¹) hb
  simpa [mul_assoc] using h

theorem XCt_le_N (hE : Sec8E G t L S z g B E) :
    normalizer (E : Set G) ⊓ centralizer ({t} : Set G) ≤ Nsub8 t B := fun x hx =>
  mem_N_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hx.2) (XCt_le_NB hE hx)

theorem t_mem_N : t ∈ Nsub8 t B :=
  sec8t84a1_A_le_N sec8t84a1_t_mem_A

theorem setupE (hE : Sec8E G t L S z g B E) :
    RedAct.Setup (Nsub8 t B) (oddCoreIn (Nsub8 t B)) E where
  O_le := (oddCoreIn_normal (Nsub8 t B)).1
  V_le := hE.le_N
  O_norm := fun n hn o ho => sec8t84a1_O_norm n hn o ho
  inf := RedAct.inf_of_card_two_pow (k := 8) hE.elem.2 sec8t84a1_O_odd
  inv := by
    intro n hn v hv
    have hMN : E ⊔ oddCoreIn (Nsub8 t B) ≤ Nsub8 t B :=
      sup_le hE.le_N (oddCoreIn_normal (Nsub8 t B)).1
    have hMn : Nsub8 t B ≤ normalizer ((E ⊔ oddCoreIn (Nsub8 t B) : Subgroup G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mp hE.normal
    exact (Subgroup.mem_normalizer_iff.mp (hMn hn) v).mp (Subgroup.mem_sup_left hv)

open Classical in
@[expose] noncomputable def rhoG (hE : Sec8E G t L S z g B E) (n : G) : MulAut ↥E :=
  if h : n ∈ Nsub8 t B then RedAct.redHom (setupE hE) ⟨n, h⟩ else 1

theorem rhoG_eq (hE : Sec8E G t L S z g B E) {n : G} (hn : n ∈ Nsub8 t B) :
    rhoG hE n = RedAct.redHom (setupE hE) ⟨n, hn⟩ :=
  dif_pos hn

theorem rhoG_one (hE : Sec8E G t L S z g B E) : rhoG hE 1 = 1 := by
  rw [rhoG_eq hE (one_mem _)]
  exact map_one _

theorem rhoG_mul (hE : Sec8E G t L S z g B E) {m n : G} (hm : m ∈ Nsub8 t B)
    (hn : n ∈ Nsub8 t B) : rhoG hE (m * n) = rhoG hE m * rhoG hE n := by
  rw [rhoG_eq hE hm, rhoG_eq hE hn, rhoG_eq hE ((Nsub8 t B).mul_mem hm hn)]
  exact map_mul (RedAct.redHom (setupE hE)) ⟨m, hm⟩ ⟨n, hn⟩

theorem rhoG_inv (hE : Sec8E G t L S z g B E) {n : G} (hn : n ∈ Nsub8 t B) :
    rhoG hE n⁻¹ = (rhoG hE n)⁻¹ := by
  rw [rhoG_eq hE hn, rhoG_eq hE ((Nsub8 t B).inv_mem hn)]
  exact map_inv (RedAct.redHom (setupE hE)) ⟨n, hn⟩

theorem rhoG_pow (hE : Sec8E G t L S z g B E) {n : G} (hn : n ∈ Nsub8 t B) (k : ℕ) :
    rhoG hE (n ^ k) = rhoG hE n ^ k := by
  rw [rhoG_eq hE hn, rhoG_eq hE ((Nsub8 t B).pow_mem hn k)]
  exact map_pow (RedAct.redHom (setupE hE)) ⟨n, hn⟩ k

theorem rhoG_conj (hE : Sec8E G t L S z g B E) {m n : G} (hm : m ∈ Nsub8 t B)
    (hn : n ∈ Nsub8 t B) :
    rhoG hE (m * n * m⁻¹) = rhoG hE m * rhoG hE n * (rhoG hE m)⁻¹ := by
  rw [rhoG_mul hE ((Nsub8 t B).mul_mem hm hn) ((Nsub8 t B).inv_mem hm), rhoG_mul hE hm hn,
    rhoG_inv hE hm]

theorem rhoG_apply_X (hE : Sec8E G t L S z g B E) {n : G} (hn : n ∈ Nsub8 t B)
    (hnX : n ∈ normalizer (E : Set G)) (e : ↥E) :
    ((rhoG hE n e : ↥E) : G) = n * e * n⁻¹ := by
  rw [rhoG_eq hE hn]
  exact RedAct.redHom_of_mem_normalizer (setupE hE) ⟨n, hn⟩ hnX e

theorem rhoG_of_mem_E (hE : Sec8E G t L S z g B E) {n : G} (hn : n ∈ E) : rhoG hE n = 1 := by
  have hnN : n ∈ Nsub8 t B := hE.le_N hn
  rw [rhoG_eq hE hnN]
  ext v
  have h := RedAct.redHom_of_mem_V (setupE hE) ⟨n, hnN⟩ hn v
  have h2 : n * (v : G) * n⁻¹ = v := by
    rw [E_comm hE hn v.2]
    group
  rw [MulAut.one_apply]
  exact h.trans h2

theorem rhoG_of_mem_O (hE : Sec8E G t L S z g B E) {n : G}
    (hn : n ∈ oddCoreIn (Nsub8 t B)) : rhoG hE n = 1 := by
  have hnN : n ∈ Nsub8 t B := (oddCoreIn_normal (Nsub8 t B)).1 hn
  rw [rhoG_eq hE hnN]
  exact RedAct.redHom_of_mem_O (setupE hE) ⟨n, hnN⟩ hn

theorem rhoG_B (hE : Sec8E G t L S z g B E) (h8B : Asc82Lemma8B) {n : G}
    (hn : n ∈ Nsub8 t B) (b : ↥E) (hb : (b : G) ∈ B) :
    ((rhoG hE n b : ↥E) : G) = n * b * n⁻¹ := by
  have hmem : n * (b : G) * n⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (sec8t84a1_N_le_normalizer h8B hE.ctx hn) b).mp hb
  have h := RedAct.redHom_eq_of (setupE hE) ⟨n, hn⟩ b
    ⟨n * (b : G) * n⁻¹, B_le_E hE hmem⟩ (o := 1) (oddCoreIn (Nsub8 t B)).one_mem
    (by simp)
  rw [rhoG_eq hE hn, h]

theorem rhoG_t_apply (hE : Sec8E G t L S z g B E) (e : ↥E) :
    ((rhoG hE t e : ↥E) : G) = t * e * t⁻¹ :=
  rhoG_apply_X hE t_mem_N (t_mem_X hE) e

theorem rhoG_t_mul_self (hE : Sec8E G t L S z g B E) : rhoG hE t * rhoG hE t = 1 := by
  rw [← rhoG_mul hE t_mem_N t_mem_N, t_sq hE.ctx, rhoG_one]

theorem rhoG_t_fix_iff (hE : Sec8E G t L S z g B E) (e : ↥E) :
    rhoG hE t e = e ↔ (e : G) ∈ B := by
  rw [show (e : G) ∈ B ↔ (e : G) ∈ E ⊓ centralizer ({t} : Set G) from by rw [hE.cent_t]]
  constructor
  · intro h
    have h1 : t * (e : G) * t⁻¹ = e := by
      rw [← rhoG_t_apply hE e, h]
    refine Subgroup.mem_inf.mpr ⟨e.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (e : G) * t = (t * e * t⁻¹) * t := by rw [h1]
      _ = t * e := by group
  · intro h
    have hc : (e : G) * t = t * e :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp h).2
    apply Subtype.ext
    rw [rhoG_t_apply]
    calc t * (e : G) * t⁻¹ = (e * t) * t⁻¹ := by rw [hc]
      _ = e := by group

theorem rhoG_t_onto (hE : Sec8E G t L S z g B E) :
    ∀ b ∈ B, ∃ e : ↥E, (e : G) * ((rhoG hE t e : ↥E) : G)⁻¹ = b := by
  intro b hb
  obtain ⟨e, he, hbe⟩ := hE.comm_onto b hb
  refine ⟨⟨e, he⟩, ?_⟩
  rw [rhoG_t_apply, ← hbe]
  group

theorem rhoG_t_ne_one (hE : Sec8E G t L S z g B E) : rhoG hE t ≠ 1 := by
  intro h1
  have hle : E ≤ B := fun e he => (rhoG_t_fix_iff hE ⟨e, he⟩).mp (by rw [h1]; rfl)
  have h2 := Subgroup.card_le_of_le hle
  rw [hE.elem.2, hE.ctx.B_e16.2] at h2
  norm_num at h2

end B89

end CFSG.OddStandard.SmallF3.Omega

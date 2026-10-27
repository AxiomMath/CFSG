
module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneKillCoord
public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneSylowOffenderBase

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

open Subgroup

namespace KillData

variable {G : Type*} [Group G] {u : Bool} {Jh E : Subgroup G} {cV cE : G → ℕ} {z l₁ l₂ : G}
  (h : KillData u Jh E cV cE z l₁ l₂)

@[expose] noncomputable def liftV (v : ℕ) : G :=
  if hv : v < 64 then Classical.choose (h.cV_surj v hv) else 1

@[expose] noncomputable def liftE (x : ℕ) : G :=
  if hx : x < 512 then Classical.choose (h.cE_surj x hx) else 1

include h

theorem liftV_mem (v : ℕ) : h.liftV v ∈ Jh := by
  unfold liftV; split
  · exact (Classical.choose_spec (h.cV_surj _ ‹_›)).1
  · exact one_mem _

theorem cV_liftV {v : ℕ} (hv : v < 64) : cV (h.liftV v) = v := by
  unfold liftV; rw [dite_eq_left hv]
  exact (Classical.choose_spec (h.cV_surj _ hv)).2

theorem liftE_mem (x : ℕ) : h.liftE x ∈ E := by
  unfold liftE; split
  · exact (Classical.choose_spec (h.cE_surj _ ‹_›)).1
  · exact one_mem _

theorem cE_liftE {x : ℕ} (hx : x < 512) : cE (h.liftE x) = x := by
  unfold liftE; rw [dite_eq_left hx]
  exact (Classical.choose_spec (h.cE_surj _ hx)).2

@[expose] noncomputable def actV (g : G) (v : ℕ) : ℕ := cV (g * h.liftV v * g⁻¹)

@[expose] noncomputable def actE (g : G) (x : ℕ) : ℕ := cE (g * h.liftE x * g⁻¹)

section Act

variable {g : G} (hg : g ∈ normalizer (Jh : Set G))
include hg

theorem cV_conj {j : G} (hj : j ∈ Jh) : cV (g * j * g⁻¹) = h.actV g (cV j) := by
  have hℓ := h.liftV_mem (cV j)
  have he : (h.liftV (cV j))⁻¹ * j ∈ E := h.mem_E_of_cV_eq hℓ hj (h.cV_liftV (h.cV_lt j hj))
  have e1 : g * j * g⁻¹ = (g * h.liftV (cV j) * g⁻¹) * (g * ((h.liftV (cV j))⁻¹ * j) * g⁻¹) := by
    group
  rw [e1, h.cV_mul _ (conj_mem_Jh hg hℓ) _ (conj_mem_Jh hg (h.E_le he)),
    (h.cV_eq_zero _ (conj_mem_Jh hg (h.E_le he))).2 (h.conj_mem_E hg he), Nat.xor_zero]
  rfl

omit hg in
theorem cE_conj {e : G} (he : e ∈ E) : cE (g * e * g⁻¹) = h.actE g (cE e) := by
  have hℓ := h.liftE_mem (cE e)
  have e2 : h.liftE (cE e) = e := h.cE_injOn hℓ he (h.cE_liftE (h.cE_lt e he))
  unfold actE
  rw [e2]

theorem actV_lt (v : ℕ) : h.actV g v < 64 :=
  h.cV_lt _ (conj_mem_Jh hg (h.liftV_mem v))

theorem actE_lt (x : ℕ) : h.actE g x < 512 :=
  h.cE_lt _ (h.conj_mem_E hg (h.liftE_mem x))

theorem actV_xor {v w : ℕ} (hv : v < 64) (hw : w < 64) :
    h.actV g (v ^^^ w) = h.actV g v ^^^ h.actV g w := by
  have hm := mul_mem (h.liftV_mem v) (h.liftV_mem w)
  have e : h.actV g (v ^^^ w) = cV (g * (h.liftV v * h.liftV w) * g⁻¹) := by
    rw [h.cV_conj hg hm, h.cV_mul _ (h.liftV_mem v) _ (h.liftV_mem w), h.cV_liftV hv,
      h.cV_liftV hw]
  rw [e, show g * (h.liftV v * h.liftV w) * g⁻¹ = (g * h.liftV v * g⁻¹) * (g * h.liftV w * g⁻¹)
    by group, h.cV_mul _ (conj_mem_Jh hg (h.liftV_mem v)) _ (conj_mem_Jh hg (h.liftV_mem w))]
  rfl

theorem actE_xor {x y : ℕ} (hx : x < 512) (hy : y < 512) :
    h.actE g (x ^^^ y) = h.actE g x ^^^ h.actE g y := by
  have hm := mul_mem (h.liftE_mem x) (h.liftE_mem y)
  have e : h.actE g (x ^^^ y) = cE (g * (h.liftE x * h.liftE y) * g⁻¹) := by
    rw [h.cE_conj hm, h.cE_mul _ (h.liftE_mem x) _ (h.liftE_mem y), h.cE_liftE hx,
      h.cE_liftE hy]
  rw [e, show g * (h.liftE x * h.liftE y) * g⁻¹ = (g * h.liftE x * g⁻¹) * (g * h.liftE y * g⁻¹)
    by group, h.cE_mul _ (h.conj_mem_E hg (h.liftE_mem x)) _ (h.conj_mem_E hg (h.liftE_mem y))]
  rfl

theorem q_actV {v : ℕ} (hv : v < 64) : qOf u (h.actV g v) = h.actE g (qOf u v) := by
  have hℓ := h.liftV_mem v
  have hc := conj_mem_Jh hg hℓ
  calc qOf u (h.actV g v) = cE ((g * h.liftV v * g⁻¹) * (g * h.liftV v * g⁻¹)) :=
        (h.sq _ hc).2.symm
    _ = cE (g * (h.liftV v * h.liftV v) * g⁻¹) := by congr 1; group
    _ = h.actE g (cE (h.liftV v * h.liftV v)) := h.cE_conj (h.sq _ hℓ).1
    _ = h.actE g (qOf u v) := by rw [(h.sq _ hℓ).2, h.cV_liftV hv]

omit hg in
theorem actV_mul {g' : G} (hg : g ∈ normalizer (Jh : Set G)) (hg' : g' ∈ normalizer (Jh : Set G))
    (v : ℕ) : h.actV (g * g') v = h.actV g (h.actV g' v) := by
  rw [show h.actV g' v = cV (g' * h.liftV v * g'⁻¹) from rfl,
    ← h.cV_conj hg (conj_mem_Jh hg' (h.liftV_mem v))]
  unfold actV
  congr 1
  group

omit hg in
theorem actE_mul {g' : G} (hg' : g' ∈ normalizer (Jh : Set G)) (x : ℕ) :
    h.actE (g * g') x = h.actE g (h.actE g' x) := by
  rw [show h.actE g' x = cE (g' * h.liftE x * g'⁻¹) from rfl,
    ← h.cE_conj (h.conj_mem_E hg' (h.liftE_mem x))]
  unfold actE
  congr 1
  group

omit hg in
theorem actV_one {v : ℕ} (hv : v < 64) : h.actV 1 v = v := by
  unfold actV; rw [one_mul, inv_one, mul_one, h.cV_liftV hv]

omit hg in
theorem actE_one {x : ℕ} (hx : x < 512) : h.actE 1 x = x := by
  unfold actE; rw [one_mul, inv_one, mul_one, h.cE_liftE hx]

end Act

@[expose] noncomputable def permV (g : normalizer (Jh : Set G)) : Equiv.Perm (Fin 64) where
  toFun v := ⟨h.actV g v, h.actV_lt g.2 v⟩
  invFun v := ⟨h.actV (g⁻¹ : normalizer (Jh : Set G)) v, h.actV_lt (inv_mem g.2) v⟩
  left_inv v := Fin.ext (by
    show h.actV ((g⁻¹ : normalizer (Jh : Set G)) : G) (h.actV g v) = v
    rw [Subgroup.coe_inv, ← h.actV_mul (inv_mem g.2) g.2, inv_mul_cancel, h.actV_one v.2])
  right_inv v := Fin.ext (by
    show h.actV (g : G) (h.actV ((g⁻¹ : normalizer (Jh : Set G)) : G) v) = v
    rw [Subgroup.coe_inv, ← h.actV_mul g.2 (inv_mem g.2), mul_inv_cancel, h.actV_one v.2])

@[expose] noncomputable def permE (g : normalizer (Jh : Set G)) : Equiv.Perm (Fin 512) where
  toFun x := ⟨h.actE g x, h.actE_lt g.2 x⟩
  invFun x := ⟨h.actE (g⁻¹ : normalizer (Jh : Set G)) x, h.actE_lt (inv_mem g.2) x⟩
  left_inv x := Fin.ext (by
    show h.actE ((g⁻¹ : normalizer (Jh : Set G)) : G) (h.actE g x) = x
    rw [Subgroup.coe_inv, ← h.actE_mul g.2, inv_mul_cancel, h.actE_one x.2])
  right_inv x := Fin.ext (by
    show h.actE (g : G) (h.actE ((g⁻¹ : normalizer (Jh : Set G)) : G) x) = x
    rw [Subgroup.coe_inv, ← h.actE_mul (inv_mem g.2), mul_inv_cancel, h.actE_one x.2])

@[expose] noncomputable def ρV : normalizer (Jh : Set G) →* Equiv.Perm (Fin 64) where
  toFun := h.permV
  map_one' := Equiv.ext fun v => Fin.ext (h.actV_one v.2)
  map_mul' g g' := Equiv.ext fun v => Fin.ext (h.actV_mul g.2 g'.2 v)

@[expose] noncomputable def ρE : normalizer (Jh : Set G) →* Equiv.Perm (Fin 512) where
  toFun := h.permE
  map_one' := Equiv.ext fun x => Fin.ext (h.actE_one x.2)
  map_mul' _ g' := Equiv.ext fun x => Fin.ext (h.actE_mul g'.2 x)

theorem ρV_apply (g : normalizer (Jh : Set G)) (v : Fin 64) : (h.ρV g v).val = h.actV g v := rfl

theorem ρE_apply (g : normalizer (Jh : Set G)) (x : Fin 512) : (h.ρE g x).val = h.actE g x := rfl

theorem ρV_mem_Gq (g : normalizer (Jh : Set G)) : h.ρV g ∈ Gq u := by
  refine ⟨fun v w => Fin.ext ?_, h.ρE g, fun x y => Fin.ext ?_, fun v => Fin.ext ?_⟩
  · exact h.actV_xor g.2 v.2 w.2
  · exact h.actE_xor g.2 x.2 y.2
  · exact h.q_actV g.2 v.2

theorem cV_conj' (g : normalizer (Jh : Set G)) {j : G} (hj : j ∈ Jh) :
    cV ((g : G) * j * (g : G)⁻¹) = (h.ρV g ⟨cV j, h.cV_lt j hj⟩).val :=
  h.cV_conj g.2 hj

theorem eAct_ρV (g : normalizer (Jh : Set G)) (x : Fin 512) :
    eAct u (h.ρV g) x = (h.ρE g x).val :=
  (eAct_unique (h.ρV_mem_Gq g) (τ := h.ρE g) (fun a b => Fin.ext (h.actE_xor g.2 a.2 b.2))
    (fun v => Fin.ext (h.q_actV g.2 v.2)) x).symm

theorem card_E : Nat.card E = 512 := by
  have hbij : Function.Bijective (fun e : E => (⟨cE e, h.cE_lt e e.2⟩ : Fin 512)) := by
    refine ⟨fun e e' he => Subtype.ext (h.cE_injOn e.2 e'.2 (congrArg Fin.val he)), fun x => ?_⟩
    obtain ⟨e, he, hx⟩ := h.cE_surj x x.2
    exact ⟨⟨e, he⟩, Fin.ext hx⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_of_le {H : Subgroup G} (hEH : E ≤ H) (hHJ : H ≤ Jh) :
    Nat.card H = Nat.card {v : Fin 64 // ∃ x ∈ H, cV x = v} * 512 := by
  classical
  let ℓ : ℕ → G := fun v => if hv : ∃ x ∈ H, cV x = v then Classical.choose hv else 1
  have hℓ : ∀ x ∈ H, ℓ (cV x) ∈ H ∧ cV (ℓ (cV x)) = cV x := by
    intro x hx
    have hv : ∃ y ∈ H, cV y = cV x := ⟨x, hx, rfl⟩
    simp only [ℓ, dite_eq_left hv]
    exact Classical.choose_spec hv
  have hℓ' : ∀ v : {v : Fin 64 // ∃ x ∈ H, cV x = v}, ℓ v.1 ∈ H ∧ cV (ℓ v.1) = v.1 := by
    intro v
    obtain ⟨x, hx, hxv⟩ := v.2
    rw [← hxv]
    exact hℓ x hx
  have hE : ∀ x ∈ H, (ℓ (cV x))⁻¹ * x ∈ E := fun x hx =>
    h.mem_E_of_cV_eq (hHJ (hℓ x hx).1) (hHJ hx) (hℓ x hx).2
  let e : H ≃ {v : Fin 64 // ∃ x ∈ H, cV x = v} × E :=
    { toFun := fun x => (⟨⟨cV x, h.cV_lt x (hHJ x.2)⟩, x, x.2, rfl⟩, ⟨_, hE x x.2⟩)
      invFun := fun p => ⟨ℓ p.1.1 * p.2, mul_mem (hℓ' p.1).1 (hEH p.2.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun p => by
        have hcv : cV (ℓ p.1.1 * p.2) = p.1.1 := by
          rw [h.cV_mul _ (hHJ (hℓ' p.1).1) _ (h.E_le p.2.2), (hℓ' p.1).2,
            (h.cV_eq_zero _ (h.E_le p.2.2)).2 p.2.2, Nat.xor_zero]
        refine Prod.ext (Subtype.ext (Fin.ext hcv)) (Subtype.ext ?_)
        simp only
        rw [hcv]
        group }
  rw [Nat.card_congr e, Nat.card_prod, h.card_E]

theorem card_Jh : Nat.card Jh = 2 ^ 15 := by
  rw [h.card_of_le h.E_le le_rfl]
  have : Nat.card {v : Fin 64 // ∃ x ∈ Jh, cV x = v} = 64 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv fun v => by
      obtain ⟨x, hx, hv⟩ := h.cV_surj v v.2
      exact ⟨x, hx, hv⟩), Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [this]
  norm_num

end KillData

end CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne

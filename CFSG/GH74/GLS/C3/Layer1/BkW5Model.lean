module

public import CFSG.GH74.GLS.C3.Layer1.BkW5Nprime
public import CFSG.GH74.GLS.C3.Layer2.L5C15

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk.W5


open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
open scoped commutatorElement
open CFSG.GH74.GLS.C3.Layer1.Back

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}
  {h : IsAConfigW 5 x K T Q S a}

namespace Coord

section Iota

variable (c : Coord h)

@[expose] noncomputable def iotaT : ↥T5 →* G where
  toFun t := (exists_T_rco c t.2).choose
  map_one' := by
    have h1 : (exists_T_rco c (1 : ↥T5).2).choose ∈ T := (exists_T_rco c (1 : ↥T5).2).choose_spec.1
    refine rco_inj c h1 T.one_mem ?_
    rw [(exists_T_rco c (1 : ↥T5).2).choose_spec.2, rco_one]
    rfl
  map_mul' s t := by
    have hs := (exists_T_rco c s.2).choose_spec
    have ht := (exists_T_rco c t.2).choose_spec
    have hst := (exists_T_rco c (s * t).2).choose_spec
    refine rco_inj c hst.1 (T.mul_mem hs.1 ht.1) ?_
    rw [hst.2, rco_T_mul c hs.1 ht.1, hs.2, ht.2]
    rfl

theorem iotaT_mem_T (t : ↥T5) : c.iotaT t ∈ T :=
  (exists_T_rco c t.2).choose_spec.1

theorem iotaT_mem_C (t : ↥T5) :
    c.iotaT t ∈ centralizer ({x} : Set G) :=
  h.T_le_C (c.iotaT_mem_T t)

theorem rco_iotaT (t : ↥T5) : c.rco (c.iotaT t) = (t : Amb 5) :=
  (exists_T_rco c t.2).choose_spec.2

theorem iotaT_injective : Function.Injective c.iotaT := by
  intro s t hst
  apply Subtype.ext
  have := congrArg c.rco hst
  rwa [c.rco_iotaT, c.rco_iotaT] at this

theorem iotaT_elT
    (i : Fin 16) : c.iotaT (elT i) = c.liftEl i := by
  apply rco_inj c (c.iotaT_mem_T _) (c.liftEl_mem_T i)
  rw [c.rco_iotaT, c.rco_liftEl]
  rfl

theorem iotaT_x0 :
    c.iotaT x0T5 = x := by
  apply rco_inj c (c.iotaT_mem_T _) h.x_mem_T
  rw [c.rco_iotaT, x_co (c := c)]
  rfl

theorem iotaT_conj {g : Amb 5} (hg : g ∈ Fgrp 5) {t s : ↥T5}
    (hts : g * (t : Amb 5) * g⁻¹ = (s : Amb 5)) : IsConj (c.iotaT t) (c.iotaT s) := by
  obtain ⟨g', hg'⟩ := c.co_surj ⟨g, hg⟩
  have hg'C : (g' : G) ∈ centralizer ({x} : Set G) := g'.2
  have hco : c.rco (g' : G) = g := by
    rw [rco_of_mem c hg'C]
    have : (⟨(g' : G), hg'C⟩ : ↥(centralizer ({x} : Set G))) = g' := rfl
    rw [this, hg']
  set u : G := (g' : G) * c.iotaT t * (g' : G)⁻¹ with hu
  have huC : u ∈ centralizer ({x} : Set G) :=
    mul_mem (mul_mem hg'C (c.iotaT_mem_C t)) (inv_mem hg'C)
  have hruu : c.rco u = (s : Amb 5) := by
    rw [hu, rco_mul c (mul_mem hg'C (c.iotaT_mem_C t)) (inv_mem hg'C),
      rco_mul c hg'C (c.iotaT_mem_C t), rco_inv c hg'C, hco, c.rco_iotaT]
    exact hts
  have hsC := c.iotaT_mem_C s
  have hW : (⟨(c.iotaT s)⁻¹ * u, mul_mem (inv_mem hsC) huC⟩ : ↥(centralizer ({x} : Set G))) ∈
      Wc x := by
    rw [← c.co_ker]
    have e : (⟨(c.iotaT s)⁻¹ * u, mul_mem (inv_mem hsC) huC⟩ : ↥(centralizer ({x} : Set G))) =
        (⟨c.iotaT s, hsC⟩ : ↥(centralizer ({x} : Set G)))⁻¹ * ⟨u, huC⟩ := rfl
    rw [e, map_mul, map_inv]
    have h1 : c.co ⟨u, huC⟩ = c.co ⟨c.iotaT s, hsC⟩ := by
      apply Subtype.ext
      have h2 := rco_of_mem c huC
      have h3 := rco_of_mem c hsC
      rw [← h2, ← h3, hruu, c.rco_iotaT]
    rw [h1, inv_mul_cancel]
  have hsuW : (c.iotaT s)⁻¹ * u ∈ pPrimeCoreOf 2 (centralizer ({x} : Set G)) := mem_Wc.1 hW
  have hT2 : IsPGroup 2 ↥T := h.sylowT.isPGroup
  have hcjT : IsPGroup 2 ↥(Th2.cj (g' : G) T) := hT2.map (MulAut.conj (g' : G)).toMonoidHom
  have huB : u ∈ Th2.cj (g' : G) T := ⟨c.iotaT t, c.iotaT_mem_T t, by simp [hu, MulAut.conj_apply]⟩
  obtain ⟨k, hk⟩ := exists_conj_of_coset (C := centralizer ({x} : Set G))
    (W := pPrimeCoreOf 2 (centralizer ({x} : Set G)))
    (fun c' hc' w hw => W_norm hc' hw) (W_odd x) hsC (c.iotaT_mem_T s) hT2 huB hcjT hsuW
  rw [isConj_iff]
  refine ⟨k * (g' : G), ?_⟩
  rw [← hk, hu]
  group

end Iota

end Coord

namespace Coord

section Model

@[expose] noncomputable def rhoS1
    (c : Coord h) {S₁ : Subgroup G} (hN : S₁ ≤ c.N) : ↥S₁ →* Perm (Fin 16) :=
  c.rhoG.comp (Subgroup.inclusion hN)

@[expose] noncomputable def iotaS1 (c : Coord h) {S₁ : Subgroup G}
    (hT : T ≤ S₁) : ↥T5 →* ↥S₁ where
  toFun t := ⟨c.iotaT t, hT (c.iotaT_mem_T t)⟩
  map_one' := Subtype.ext (map_one c.iotaT)
  map_mul' s t := Subtype.ext (map_mul c.iotaT s t)

theorem iotaS1_injective (c : Coord h) {S₁ : Subgroup G}
    (hT : T ≤ S₁) : Function.Injective (c.iotaS1 hT) := fun s t hst => by
  have h2 := congrArg Subtype.val hst
  exact c.iotaT_injective h2

structure ModelIso
    (c : Coord h) {S₁ : Subgroup G} (hS : c.S1Data S₁)
    (M : Subgroup (Perm (Fin 16))) (Tr : Fin 16 → Perm (Fin 16)) (yy : Perm (Fin 16)) where
  ψ : ↥S₁ ≃* ↥M
  spec : ∀ t, ((ψ (c.iotaS1 hS.hT t) : ↥M) : Perm (Fin 16)) = emb48 Tr yy t

variable
  {c : Coord h} {S₁ : Subgroup G} {hS : c.S1Data S₁}
  {M : Subgroup (Perm (Fin 16))} {Tr : Fin 16 → Perm (Fin 16)} {yy : Perm (Fin 16)}

theorem ModelIso.liftEl (Ψ : c.ModelIso hS M Tr yy) (i : Fin 16) :
    ((Ψ.ψ ⟨c.liftEl i, R_le_S1 hS (c.liftEl_mem i)⟩ : ↥M) : Perm (Fin 16)) = Tr i := by
  have h1 := Ψ.spec (elT i)
  have h2 : c.iotaS1 hS.hT (elT i) = ⟨c.liftEl i, R_le_S1 hS (c.liftEl_mem i)⟩ :=
    Subtype.ext (c.iotaT_elT i)
  rw [h2] at h1
  rw [h1]
  exact Glue.emb48_el16 Tr yy i

theorem ModelIso.conj (Ψ : c.ModelIso hS M Tr yy) {s : G} (hs : s ∈ S₁) (i : Fin 16) :
    ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16)) * Tr i * ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16))⁻¹ =
      Tr (c.rhoG ⟨s, hS.hN hs⟩ i) := by
  have e1 : (⟨s, hs⟩ : ↥S₁) * ⟨c.liftEl i, R_le_S1 hS (c.liftEl_mem i)⟩ *
      (⟨s, hs⟩ : ↥S₁)⁻¹ =
      ⟨c.liftEl (c.rhoG ⟨s, hS.hN hs⟩ i), R_le_S1 hS (c.liftEl_mem _)⟩ :=
    Subtype.ext (by simp [rhoG_spec])
  have h2 := congrArg (fun y : ↥S₁ => ((Ψ.ψ y : ↥M) : Perm (Fin 16))) e1
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [Ψ.liftEl, Ψ.liftEl] at h2
  exact h2

theorem ModelIso.mem_R (Ψ : c.ModelIso hS M Tr yy) {s : G} (hs : s ∈ S₁) :
    s ∈ c.lift Rm ↔ ∃ i, ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16)) = Tr i := by
  constructor
  · intro hR
    refine ⟨idx16 (c.rco s), ?_⟩
    have h3 : (⟨s, hs⟩ : ↥S₁) = ⟨c.liftEl (idx16 (c.rco s)),
        R_le_S1 hS (c.liftEl_mem _)⟩ := Subtype.ext (exists_liftEl c hR)
    rw [h3]
    exact Ψ.liftEl _
  · rintro ⟨i, hi⟩
    have h4 : Ψ.ψ ⟨s, hs⟩ = Ψ.ψ ⟨c.liftEl i, R_le_S1 hS (c.liftEl_mem i)⟩ :=
      Subtype.ext (by rw [hi, Ψ.liftEl])
    have h5 : s = c.liftEl i := congrArg Subtype.val (Ψ.ψ.injective h4)
    rw [h5]
    exact c.liftEl_mem i

theorem ModelIso.rhoF_eq (Ψ : c.ModelIso hS M Tr yy) (hTr : Function.Injective Tr)
    {s : G} (hs : s ∈ S₁) (i : Fin 16) :
    rhoF Tr ((Ψ.ψ ⟨s, hs⟩ : ↥M) : Perm (Fin 16)) i = c.rhoG ⟨s, hS.hN hs⟩ i :=
  Glue.rhoF_eq hTr (Ψ.conj hs i)

end Model

end Coord

end CFSG.GH74.GLS.C3.Layer1.Bk.W5

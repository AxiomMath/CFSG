module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Recog

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

structure Sec {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (C : StdCfg T M H S L) where
  hTC : blockTC T S L = ⊥
  s : Equiv.Perm (Fin 5) →* ↥H
  hs : ∀ σ, C.D.π (s σ) = σ

theorem exists_sec
    {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}
    (C : StdCfg T M H S L) (hTC : blockTC T S L = ⊥) : Nonempty (Sec C) := by
  obtain ⟨s, hs⟩ := C.exists_section_H hTC
  exact ⟨⟨hTC, s, hs⟩⟩

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] noncomputable def iV (C : StdCfg T M H S L) (w : evenWeight 5) : ↥H :=
  C.iotaH (Multiplicative.ofAdd w)

theorem iV_add (C : StdCfg T M H S L) (w w' : evenWeight 5) :
    C.iV (w + w') = C.iV w * C.iV w' := by
  simp [iV]

theorem iV_zero (C : StdCfg T M H S L) : C.iV 0 = 1 := by simp [iV]

theorem iV_inj (C : StdCfg T M H S L) (hTC : blockTC T S L = ⊥) {w w' : evenWeight 5}
    (h : C.iV w = C.iV w') : w = w' :=
  Multiplicative.ofAdd.injective ((C.deltaExt hTC).inj h)

theorem iV_coe (C : StdCfg T M H S L) (w : evenWeight 5) :
    ((C.iV w : ↥H) : G) = ((C.D.β.symm (Multiplicative.ofAdd w) : ↥(blockU L)) : G) := rfl

theorem iV_mem_U (C : StdCfg T M H S L) (w : evenWeight 5) : ((C.iV w : ↥H) : G) ∈ blockU L :=
  (C.D.β.symm (Multiplicative.ofAdd w)).2

theorem pi_iV (C : StdCfg T M H S L) (hTC : blockTC T S L = ⊥) (w : evenWeight 5) :
    C.D.π (C.iV w) = 1 := (C.deltaExt hTC).ι_ker w

theorem conj_iV (C : StdCfg T M H S L) (hTC : blockTC T S L = ⊥) (h : ↥H) (w : evenWeight 5) :
    h * C.iV w * h⁻¹ = C.iV (vact (C.D.π h) w) := (C.deltaExt hTC).conj h w

theorem exists_iV (C : StdCfg T M H S L) (hTC : blockTC T S L = ⊥) {h : ↥H}
    (hh : C.D.π h = 1) : ∃ w, C.iV w = h := (C.deltaExt hTC).ker h hh

theorem iV_self (C : StdCfg T M H S L) (w : evenWeight 5) : C.iV w * C.iV w = 1 := by
  rw [← iV_add, Delta_add_self, iV_zero]

theorem iV_comm (C : StdCfg T M H S L) (w w' : evenWeight 5) : C.iV w * C.iV w' = C.iV w' * C.iV w := by
  rw [← iV_add, ← iV_add, add_comm]

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

@[expose] noncomputable def emb (w : evenWeight 5) (σ : Equiv.Perm (Fin 5)) : ↥H :=
  C.iV w * X.s σ

theorem pi_emb (w : evenWeight 5) (σ : Equiv.Perm (Fin 5)) : C.D.π (X.emb w σ) = σ := by
  rw [emb, map_mul, C.pi_iV X.hTC, X.hs, one_mul]

theorem emb_mul (w w' : evenWeight 5) (σ σ' : Equiv.Perm (Fin 5)) :
    X.emb w σ * X.emb w' σ' = X.emb (w + vact σ w') (σ * σ') := by
  have h := C.conj_iV X.hTC (X.s σ) w'
  rw [X.hs] at h
  calc X.emb w σ * X.emb w' σ' = C.iV w * (X.s σ * C.iV w' * (X.s σ)⁻¹) * (X.s σ * X.s σ') := by
        simp only [emb]; group
    _ = C.iV w * C.iV (vact σ w') * X.s (σ * σ') := by rw [h, map_mul]
    _ = X.emb (w + vact σ w') (σ * σ') := by rw [emb, C.iV_add]

theorem emb_zero_one : X.emb 0 1 = 1 := by
  rw [emb, C.iV_zero, map_one, one_mul]

theorem emb_inj {w w' : evenWeight 5} {σ σ' : Equiv.Perm (Fin 5)}
    (h : X.emb w σ = X.emb w' σ') : w = w' ∧ σ = σ' := by
  have hσ : σ = σ' := by
    have := congrArg C.D.π h
    rwa [X.pi_emb, X.pi_emb] at this
  subst hσ
  refine ⟨?_, rfl⟩
  have : C.iV w = C.iV w' := by
    have h' : C.iV w * X.s σ = C.iV w' * X.s σ := h
    exact mul_right_cancel h'
  exact C.iV_inj X.hTC this

theorem exists_emb (h : ↥H) : ∃ w, h = X.emb w (C.D.π h) := by
  have hker : C.D.π (h * (X.s (C.D.π h))⁻¹) = 1 := by
    rw [map_mul, map_inv, X.hs, mul_inv_cancel]
  obtain ⟨w, hw⟩ := C.exists_iV X.hTC hker
  refine ⟨w, ?_⟩
  rw [emb, hw]
  group

@[expose] noncomputable def cw (h : ↥H) : evenWeight 5 := Classical.choose (X.exists_emb h)

theorem cw_spec (h : ↥H) : h = X.emb (X.cw h) (C.D.π h) := Classical.choose_spec (X.exists_emb h)

theorem cw_emb (w : evenWeight 5) (σ : Equiv.Perm (Fin 5)) : X.cw (X.emb w σ) = w := by
  have h := X.cw_spec (X.emb w σ)
  rw [X.pi_emb] at h
  exact (X.emb_inj h.symm).1

theorem emb_inv (w : evenWeight 5) (σ : Equiv.Perm (Fin 5)) :
    (X.emb w σ)⁻¹ = X.emb (vact σ⁻¹ w) σ⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [emb_mul, ← vact_mul, mul_inv_cancel, vact_one, Delta_add_self, emb_zero_one]

end Sec

end CFSG.QuasithinUnique.A5

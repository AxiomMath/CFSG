module

public import CFSG.LocalAnalysis.EvenBN.U4.RootQ1Orbit

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

@[expose] noncomputable def rootElt (hS : Setting h L η t Q T) (a : K) : G :=
  ((η.symm ⟨miyamotoXGL h a 0 0 0, hS.rootA_le_SU ⟨a, rfl⟩⟩ : L) : G)

theorem rootElt_mem_PG (hS : Setting h L η t Q T) (a : K) :
    hS.rootElt a ∈ miyamotoPG h L η := by
  have : CharP K 2 := h.charP
  exact (symm_mem_miyamotoPull_iff h L η).2
    ((miyamotoA2_le_P h) ((miyamotoRootA_le_A2 h) ⟨a, rfl⟩))

theorem rootElt_add (hS : Setting h L η t Q T) (a b : K) :
    hS.rootElt (a + b) = hS.rootElt a * hS.rootElt b := by
  have : CharP K 2 := h.charP
  simp only [rootElt]
  rw [← L.coe_mul, ← map_mul]
  congr 3
  change miyamotoXGL h (a + b) 0 0 0 = miyamotoXGL h a 0 0 0 * miyamotoXGL h b 0 0 0
  rw [miyamotoXGL_mul h (map_zero _), miyamotoXGL_inj]
  simp

theorem rootElt_zero (hS : Setting h L η t Q T) : hS.rootElt 0 = 1 := by
  have := hS.rootElt_add 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := hS.rootElt 0) (by rw [mul_one, ← this])

theorem rootElt_mul_self (hS : Setting h L η t Q T) (a : K) :
    hS.rootElt a * hS.rootElt a = 1 := by
  have : CharP K 2 := h.charP
  rw [← hS.rootElt_add, CharTwo.add_self_eq_zero, hS.rootElt_zero]

theorem rootElt_inv (hS : Setting h L η t Q T) (a : K) : (hS.rootElt a)⁻¹ = hS.rootElt a :=
  inv_eq_of_mul_eq_one_right (hS.rootElt_mul_self a)

theorem rootElt_mem_P1 (hS : Setting h L η t Q T) (a : K) :
    hS.rootElt a ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η :=
  mem_sup_right (hS.rootElt_mem_PG a)

theorem rootElt_mem_F1_iff (hS : Setting h L η t Q T) {a : K} :
    hS.rootElt a ∈ miyamotoF1G h L η t ↔ a = 0 := by
  have : CharP K 2 := h.charP
  constructor
  · intro ha
    have hA : hS.rootElt a ∈ miyamotoA1G h L η := by
      rw [← hS.F1_inf_PG]
      exact mem_inf.2 ⟨ha, hS.rootElt_mem_PG a⟩
    have := (symm_mem_miyamotoPull_iff h L η).1 hA
    exact ((miyamotoXGL_mem_A1 h).1 this).1
  · rintro rfl
    rw [hS.rootElt_zero]
    exact one_mem _

@[expose] noncomputable def torusElt (_hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) : G :=
  ((η.symm ⟨miyamotoIHom h p,
    miyamotoI_le_gramSU h ((miyamotoIHom_mem_miyamotoI_iff h p).2 hp)⟩ : L) : G)

theorem torusElt_mem_IG (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) : hS.torusElt p hp ∈ miyamotoIG h L η :=
  (symm_mem_miyamotoPull_iff h L η).2 ((miyamotoIHom_mem_miyamotoI_iff h p).2 hp)

theorem torusElt_conj_rootElt (hS : Setting h L η t Q T) (p : Kˣ × Kˣ)
    (hp : miyamotoIParam h p = 1) (a : K) :
    (hS.torusElt p hp)⁻¹ * hS.rootElt a * hS.torusElt p hp =
      hS.rootElt (miyamotoWeightA p * a) := by
  simp only [torusElt, rootElt]
  rw [← L.coe_inv, ← L.coe_mul, ← L.coe_mul, ← map_inv, ← map_mul, ← map_mul]
  congr 3
  apply Subtype.ext
  simp only [coe_mul, coe_inv]
  exact miyamotoIHom_conj_rootA h p a

theorem exists_rootElt_mul_inv_mem_F1 (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    ∃ b, x * (hS.rootElt b)⁻¹ ∈ miyamotoF1G h L η t := by
  have : CharP K 2 := h.charP
  obtain ⟨f₀, hf₀, p, hp, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' hS.PG_le_normalizer_F1 hx
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hp
  set a := ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0 with ha
  refine ⟨a, ?_⟩
  have hxA : miyamotoXGL h a 0 0 0 ∈ miyamotoP h :=
    (miyamotoA2_le_P h) ((miyamotoRootA_le_A2 h) ⟨a, rfl⟩)
  have hA : (g : GL (Fin 4) K) * (miyamotoXGL h a 0 0 0)⁻¹ ∈ miyamotoA1 h := by
    refine (mem_miyamotoA1_iff_one_zero h (mul_mem hg (inv_mem hxA))).2 ?_
    rw [miyamotoP_one_zero_mul h hg (inv_mem hxA), miyamotoP_one_zero_inv h hxA,
      coe_miyamotoXGL, miyamotoX_one_zero, ← ha, CharTwo.add_self_eq_zero]
  have hAG : ((η.symm g : L) : G) * (hS.rootElt a)⁻¹ ∈ miyamotoA1G h L η := by
    have := (symm_mem_miyamotoPull_iff h L η
      (g := g * ⟨miyamotoXGL h a 0 0 0, hS.rootA_le_SU ⟨a, rfl⟩⟩⁻¹)).2 (by
        simpa only [coe_mul, coe_inv] using hA)
    simpa only [map_mul, map_inv, L.coe_mul, L.coe_inv, rootElt] using this
  rw [mul_assoc]
  exact mul_mem hf₀ (hS.A1_le_F1 hAG)

theorem eq_of_rootElt_mul_inv_mem_F1 (hS : Setting h L η t Q T) {x : G} {b b' : K}
    (hb : x * (hS.rootElt b)⁻¹ ∈ miyamotoF1G h L η t)
    (hb' : x * (hS.rootElt b')⁻¹ ∈ miyamotoF1G h L η t) : b = b' := by
  have : CharP K 2 := h.charP
  have h1 := mul_mem (inv_mem hb) hb'
  rw [show (x * (hS.rootElt b)⁻¹)⁻¹ * (x * (hS.rootElt b')⁻¹) =
      hS.rootElt b * (hS.rootElt b')⁻¹ by group, hS.rootElt_inv, ← hS.rootElt_add,
    hS.rootElt_mem_F1_iff] at h1
  calc b = b + (b + b') := by rw [h1, add_zero]
    _ = b' := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

open Classical in
noncomputable def coordP1 (hS : Setting h L η t Q T) (x : G) : K :=
  if hx : ∃ b, x * (hS.rootElt b)⁻¹ ∈ miyamotoF1G h L η t then hx.choose else 0

theorem coordP1_spec (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    x * (hS.rootElt (hS.coordP1 x))⁻¹ ∈ miyamotoF1G h L η t := by
  have hex := hS.exists_rootElt_mul_inv_mem_F1 hx
  rw [coordP1, dite_eq_left hex]
  exact hex.choose_spec

theorem coordP1_eq (hS : Setting h L η t Q T) {x : G} {b : K}
    (hb : x * (hS.rootElt b)⁻¹ ∈ miyamotoF1G h L η t) : hS.coordP1 x = b := by
  have hex : ∃ b, x * (hS.rootElt b)⁻¹ ∈ miyamotoF1G h L η t := ⟨b, hb⟩
  rw [coordP1, dite_eq_left hex]
  exact hS.eq_of_rootElt_mul_inv_mem_F1 hex.choose_spec hb

theorem coordP1_rootElt (hS : Setting h L η t Q T) (a : K) : hS.coordP1 (hS.rootElt a) = a :=
  hS.coordP1_eq (by rw [mul_inv_cancel]; exact one_mem _)

theorem coordP1_mul (hS : Setting h L η t Q T) {x y : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η)
    (hy : y ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    hS.coordP1 (x * y) = hS.coordP1 x + hS.coordP1 y := by
  refine hS.coordP1_eq ?_
  have h1 := hS.coordP1_spec hx
  have h2 := hS.coordP1_spec hy
  have h3 : hS.rootElt (hS.coordP1 x) * (y * (hS.rootElt (hS.coordP1 y))⁻¹) *
      (hS.rootElt (hS.coordP1 x))⁻¹ ∈ miyamotoF1G h L η t :=
    (mem_normalizer_iff.1 (hS.PG_le_normalizer_F1 (hS.rootElt_mem_PG _)) _).1 h2
  rw [hS.rootElt_add]
  have e : x * y * (hS.rootElt (hS.coordP1 x) * hS.rootElt (hS.coordP1 y))⁻¹ =
      (x * (hS.rootElt (hS.coordP1 x))⁻¹) * (hS.rootElt (hS.coordP1 x) *
        (y * (hS.rootElt (hS.coordP1 y))⁻¹) * (hS.rootElt (hS.coordP1 x))⁻¹) := by
    group
  rw [e]
  exact mul_mem h1 h3

theorem coordP1_eq_zero_iff (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    hS.coordP1 x = 0 ↔ x ∈ miyamotoF1G h L η t := by
  constructor
  · intro h0
    have := hS.coordP1_spec hx
    rwa [h0, hS.rootElt_zero, inv_one, mul_one] at this
  · intro hxF
    exact hS.coordP1_eq (by rw [hS.rootElt_zero, inv_one, mul_one]; exact hxF)

theorem coordP1_of_mem_F1 (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoF1G h L η t) :
    hS.coordP1 x = 0 :=
  (hS.coordP1_eq_zero_iff (mem_sup_left hx)).2 hx

theorem normalizer_Q1_le_normalizer_P1 (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) ≤
      normalizer ((miyamotoF1G h L η t ⊔ miyamotoPG h L η : Subgroup G) : Set G) :=
  hS.orbit_shape.2

theorem conj_mem_P1 (hS : Setting h L η t Q T) {g x : G}
    (hg : g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))
    (hx : x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η) :
    g * x * g⁻¹ ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η :=
  (mem_normalizer_iff.1 (hS.normalizer_Q1_le_normalizer_P1 hg) x).1 hx

@[expose] noncomputable def conjAct (hS : Setting h L η t Q T) :
    normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G) →* AddMonoid.End K where
  toFun g :=
    { toFun := fun a => hS.coordP1 ((g : G) * hS.rootElt a * (g : G)⁻¹)
      map_zero' := by
        show hS.coordP1 ((g : G) * hS.rootElt 0 * (g : G)⁻¹) = 0
        rw [hS.rootElt_zero, mul_one, mul_inv_cancel]
        exact hS.coordP1_of_mem_F1 (one_mem _)
      map_add' := fun a b => by
        show hS.coordP1 ((g : G) * hS.rootElt (a + b) * (g : G)⁻¹) =
          hS.coordP1 ((g : G) * hS.rootElt a * (g : G)⁻¹) +
            hS.coordP1 ((g : G) * hS.rootElt b * (g : G)⁻¹)
        rw [hS.rootElt_add, show (g : G) * (hS.rootElt a * hS.rootElt b) * (g : G)⁻¹ =
          ((g : G) * hS.rootElt a * (g : G)⁻¹) * ((g : G) * hS.rootElt b * (g : G)⁻¹) by group]
        exact hS.coordP1_mul (hS.conj_mem_P1 g.2 (hS.rootElt_mem_P1 a))
          (hS.conj_mem_P1 g.2 (hS.rootElt_mem_P1 b)) }
  map_one' := by
    ext a
    change hS.coordP1 (1 * hS.rootElt a * 1⁻¹) = a
    rw [one_mul, inv_one, mul_one, hS.coordP1_rootElt]
  map_mul' g g' := by
    ext a
    change hS.coordP1 ((g * g' : G) * hS.rootElt a * (g * g' : G)⁻¹) =
      hS.coordP1 ((g : G) * hS.rootElt (hS.coordP1 ((g' : G) * hS.rootElt a * (g' : G)⁻¹)) *
        (g : G)⁻¹)
    set y := (g' : G) * hS.rootElt a * (g' : G)⁻¹ with hy
    have hyP := hS.conj_mem_P1 g'.2 (hS.rootElt_mem_P1 a)
    have hf := hS.coordP1_spec hyP
    have hgF : (g : G) * (y * (hS.rootElt (hS.coordP1 y))⁻¹) * (g : G)⁻¹ ∈
        miyamotoF1G h L η t :=
      (mem_normalizer_iff.1 (hS.normalizer_Q1_le_normalizer_F1 g.2) _).1 hf
    have e : ((g * g' : G)) * hS.rootElt a * (g * g' : G)⁻¹ =
        ((g : G) * (y * (hS.rootElt (hS.coordP1 y))⁻¹) * (g : G)⁻¹) *
          ((g : G) * hS.rootElt (hS.coordP1 y) * (g : G)⁻¹) := by
      rw [hy]
      group
    rw [e, hS.coordP1_mul (mem_sup_left hgF)
      (hS.conj_mem_P1 g.2 (hS.rootElt_mem_P1 _)), hS.coordP1_of_mem_F1 hgF, zero_add]

theorem conjAct_apply (hS : Setting h L η t Q T)
    (g : normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) (a : K) :
    hS.conjAct g a = hS.coordP1 ((g : G) * hS.rootElt a * (g : G)⁻¹) :=
  rfl

theorem conjAct_eq_one_iff (hS : Setting h L η t Q T)
    (g : normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :
    hS.conjAct g = 1 ↔ ∀ x ∈ miyamotoF1G h L η t ⊔ miyamotoPG h L η,
      (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ miyamotoF1G h L η t := by
  constructor
  · intro h1 x hx
    have hxs := hS.coordP1_spec hx
    have h2 : hS.coordP1 ((g : G) * hS.rootElt (hS.coordP1 x) * (g : G)⁻¹) = hS.coordP1 x := by
      rw [← conjAct_apply, h1]
      rfl
    have h3 := hS.coordP1_spec (hS.conj_mem_P1 g.2 (hS.rootElt_mem_P1 (hS.coordP1 x)))
    rw [h2] at h3
    set s := hS.rootElt (hS.coordP1 x) with hs
    have hgf : (g : G) * (x * s⁻¹) * (g : G)⁻¹ ∈ miyamotoF1G h L η t :=
      (mem_normalizer_iff.1 (hS.normalizer_Q1_le_normalizer_F1 g.2) _).1 hxs
    have e : (g : G) * x * (g : G)⁻¹ * x⁻¹ =
        ((g : G) * (x * s⁻¹) * (g : G)⁻¹) * ((g : G) * s * (g : G)⁻¹ * s⁻¹) * (x * s⁻¹)⁻¹ := by
      group
    rw [e]
    exact mul_mem (mul_mem hgf h3) (inv_mem hxs)
  · intro h1
    ext a
    change hS.coordP1 ((g : G) * hS.rootElt a * (g : G)⁻¹) = a
    exact hS.coordP1_eq (h1 _ (hS.rootElt_mem_P1 a))


end Setting

end CFSG.LocalAnalysis.EvenBN.U4

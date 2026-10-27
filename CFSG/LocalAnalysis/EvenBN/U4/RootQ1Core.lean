module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.AutSection
public import CFSG.LocalAnalysis.EvenBN.U4.RootQ1Orbit

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_sup mem_normalizer_inf)

section Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem glAut_miyamotoIHom (φ : K ≃+* K) (p : Kˣ × Kˣ) :
    glAut φ (miyamotoIHom h p) =
      miyamotoIHom h (Units.map (φ : K →* K) p.1, Units.map (φ : K →* K) p.2) := by
  apply Units.ext
  rw [coe_glAut]
  simp only [miyamotoIHom, MonoidHom.coe_mk, OneHom.coe_mk, coe_miyamotoDiag]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, map_bar_comm h φ, Units.coe_map, map_inv₀]

theorem miyamotoIParam_mk_inv (u : Kˣ) : miyamotoIParam h (u, u⁻¹) = 1 := by
  apply Units.ext
  simp only [miyamotoIParam, MonoidHom.mul_apply, MonoidHom.coe_fst, MonoidHom.coe_snd,
    MonoidHom.inv_apply, MonoidHom.coe_comp, Function.comp_apply, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    Units.val_one]
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hbu : h.bar (u : K) ≠ 0 := (map_ne_zero _).2 hu
  rw [map_inv₀]
  field_simp

theorem miyamotoIHom_comm (p p' : Kˣ × Kˣ) :
    miyamotoIHom h p * miyamotoIHom h p' = miyamotoIHom h p' * miyamotoIHom h p := by
  rw [← map_mul, ← map_mul, mul_comm]

theorem eq_refl_of_conj_mul_inv_mem_P [CharP K 2] {s : GL (Fin 4) K}
    (hs : s ∈ gramSU h (miyamotoJ4 K)) {φ : K ≃+* K}
    (hP : ∀ g ∈ miyamotoP h, s * glAut φ g * s⁻¹ ∈ miyamotoP h)
    (hI : ∀ p : Kˣ × Kˣ, miyamotoIParam h p = 1 →
      s * glAut φ (miyamotoIHom h p) * s⁻¹ * (miyamotoIHom h p)⁻¹ ∈ miyamotoP h) :
    φ = RingEquiv.refl K := by
  have := h.finite
  have hsN : s ∈ normalizer (miyamotoP h : Set (GL (Fin 4) K)) := by
    refine mem_normalizer_fintype fun g hg => ?_
    have := hP _ (glAut_mem_P h φ⁻¹ hg)
    rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at this
  have hsPI : s ∈ miyamotoP h ⊔ miyamotoI h := by
    rw [← normalizer_miyamotoP h]
    exact mem_inf.2 ⟨hs, hsN⟩
  obtain ⟨p₀, hp₀, d₀, hd₀, rfl⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer' (miyamotoI_le_normalizer_unipotent h false false) hsPI
  obtain ⟨q₀, -, rfl⟩ := hd₀
  refine RingEquiv.ext fun x => ?_
  by_cases hx : x = 0
  · rw [hx, map_zero]
    rfl
  set u : Kˣ := Units.mk0 x hx with hu
  set D := miyamotoIHom h (u, u⁻¹) with hD
  set D' := miyamotoIHom h (Units.map (φ : K →* K) u, (Units.map (φ : K →* K) u)⁻¹) with hD'
  have hφD : glAut φ D = D' := by
    rw [hD, glAut_miyamotoIHom, hD', map_inv]
  have hD'I : D' ∈ miyamotoI h := ⟨_, miyamotoIParam_mk_inv h _, rfl⟩
  have hDI : D ∈ miyamotoI h := ⟨_, miyamotoIParam_mk_inv h _, rfl⟩
  have h1 := hI (u, u⁻¹) (miyamotoIParam_mk_inv h u)
  rw [← hD, hφD] at h1
  have hcomm : miyamotoIHom h q₀ * D' = D' * miyamotoIHom h q₀ := miyamotoIHom_comm h _ _
  have e1 : p₀ * miyamotoIHom h q₀ * D' * (p₀ * miyamotoIHom h q₀)⁻¹ * D⁻¹ =
      p₀ * D' * p₀⁻¹ * D⁻¹ := by
    rw [mul_assoc p₀, hcomm]
    group
  rw [e1] at h1
  have h2 : D' * p₀⁻¹ * D'⁻¹ ∈ miyamotoP h :=
    (mem_normalizer_iff.1 (miyamotoI_le_normalizer_unipotent h false false hD'I) _).1
      (inv_mem hp₀)
  have h3 : D' * D⁻¹ ∈ miyamotoP h := by
    have := mul_mem (inv_mem (mul_mem hp₀ h2)) h1
    rwa [show (p₀ * (D' * p₀⁻¹ * D'⁻¹))⁻¹ * (p₀ * D' * p₀⁻¹ * D⁻¹) = D' * D⁻¹ by group] at this
  have h4 : D' * D⁻¹ ∈ miyamotoI h := mul_mem hD'I (inv_mem hDI)
  have h5 : D' * D⁻¹ = 1 := by
    have := mem_inf.2 ⟨h3, h4⟩
    rwa [miyamotoP_inf_I h, mem_bot] at this
  have h6 : D' = D := mul_inv_eq_one.1 h5
  have e00 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) h6
  simpa [hD, hD', hu, miyamotoIHom, miyamotoDiag] using e00

end Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem fieldFactor_eq_one_of_commutator (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hxP : x ∈ normalizer (miyamotoPG h L η : Set G))
    (hxI : ∀ i ∈ miyamotoIG h L η, x * i * x⁻¹ * i⁻¹ ∈ miyamotoPG h L η) :
    hS.fieldFactor ⟨x, hxC⟩ = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨s, hs⟩ := hS.exists_act_eq ⟨x, hxC⟩
  have hact : ∀ g : gramSU h (miyamotoJ4 K),
      ((hS.act ⟨x, hxC⟩ g : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
        (s : GL (Fin 4) K) * glAut (hS.fieldFactor ⟨x, hxC⟩) (g : GL (Fin 4) K) *
          (s : GL (Fin 4) K)⁻¹ := fun g => by
    rw [hs, MulAut.mul_apply, MulAut.conj_apply, coe_mul, coe_mul, coe_inv,
      coe_miyamotoFieldAut_apply]
  refine eq_refl_of_conj_mul_inv_mem_P h s.2 (fun g hg => ?_) (fun p hp => ?_)
  · have hgS : g ∈ gramSU h (miyamotoJ4 K) := miyamotoUnipotent_le_SU h false false hg
    have h1 : x * ((η.symm ⟨g, hgS⟩ : L) : G) * x⁻¹ ∈ miyamotoPG h L η :=
      (mem_normalizer_iff.1 hxP _).1 ((symm_mem_miyamotoPull_iff h L η).2 hg)
    rw [← hS.coe_symm_act_apply ⟨x, hxC⟩, symm_mem_miyamotoPull_iff, hact] at h1
    exact h1
  · have hpI := (miyamotoIHom_mem_miyamotoI_iff h p).2 hp
    have hD : miyamotoIHom h p ∈ gramSU h (miyamotoJ4 K) := miyamotoI_le_gramSU h hpI
    have h1 := hxI _ ((symm_mem_miyamotoPull_iff h L η (g := ⟨_, hD⟩)).2 hpI)
    rw [← hS.coe_symm_act_apply ⟨x, hxC⟩, ← L.coe_inv, ← map_inv, ← L.coe_mul, ← map_mul,
      symm_mem_miyamotoPull_iff, coe_mul, coe_inv, hact] at h1
    exact h1

theorem le_Q_of_isPGroup (hS : Setting h L η t Q T) {X : Subgroup G}
    (hXC : X ≤ centralizer ({t} : Set G)) (hXQ : X ≤ normalizer (Q : Set G))
    (hX2 : IsPGroup 2 X) (hTX : T ≤ normalizer (X : Set G))
    (hIX : miyamotoIG h L η ≤ normalizer (X : Set G)) : X ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have hXT : X ≤ T := by
    have h2 : IsPGroup 2 (X ⊔ T : Subgroup G) := hX2.to_sup_of_normal_left' hS.isPGroup_T hTX
    have heq := hS.T_sylow.eq_of_le le_sup_right (sup_le hXC hS.T_le) h2
    exact heq ▸ le_sup_left
  intro x hx
  have hxT := hXT hx
  have hxC := hXC hx
  have hxP : x ∈ normalizer (miyamotoPG h L η : Set G) := by
    rw [← hS.Q_inf_L]
    exact mem_normalizer_inf (hXQ hx) (hS.centralizer_le_normalizer hxC)
  have hxI : ∀ i ∈ miyamotoIG h L η, x * i * x⁻¹ * i⁻¹ ∈ miyamotoPG h L η := by
    intro i hi
    have hiL : i ∈ L := miyamotoPull_le h L η _ hi
    have h1 : x * i * x⁻¹ * i⁻¹ ∈ X := by
      have := (mem_normalizer_iff.1 (hIX hi) x⁻¹).1 (inv_mem hx)
      rw [show x * i * x⁻¹ * i⁻¹ = x * (i * x⁻¹ * i⁻¹) by group]
      exact mul_mem hx this
    have h2 : x * i * x⁻¹ * i⁻¹ ∈ L :=
      mul_mem ((mem_normalizer_iff.1 (hS.centralizer_le_normalizer hxC) i).1 hiL) (inv_mem hiL)
    rw [← hS.T_inf_L]
    exact mem_inf.2 ⟨hXT h1, h2⟩
  obtain ⟨l, hl, c, hc, hlc⟩ :=
    (hS.fieldFactor_eq_one_iff ⟨x, hxC⟩).1 (hS.fieldFactor_eq_one_of_commutator hxC hxP hxI)
  rw [hS.kernel_eq_zpowers'] at hc
  have hct : c ∈ T := (zpowers_le.2 hS.t_mem_T) hc
  have hlP : l ∈ miyamotoPG h L η := by
    rw [← hS.T_inf_L]
    refine mem_inf.2 ⟨?_, hl⟩
    have : l = x * c⁻¹ := by
      change x = l * c at hlc
      rw [hlc, mul_inv_cancel_right]
    rw [this]
    exact mul_mem hxT (inv_mem hct)
  change x = l * c at hlc
  rw [hlc, hS.Q_eq]
  exact mul_mem (mem_sup_left hlP) (mem_sup_right hc)

theorem mem_sup_I1_of_commutator_mem_F1 (hS : Setting h L η t Q T) {g : G}
    (hg : g ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G))
    (hc : ∀ x ∈ miyamotoF1G h L η t ⊔ Q, g * x * g⁻¹ * x⁻¹ ∈ miyamotoF1G h L η t) :
    g ∈ (miyamotoF1G h L η t ⊔ Q) ⊔ miyamotoI1G h L η := by
  have : CharP K 2 := h.charP
  have hgF := hS.normalizer_Q1_le_normalizer_F1 hg
  have htF := hS.t_mem_normalizer_F1
  have hgt : (g * t)⁻¹ * (t * g) ∈ miyamotoF1G h L η t := by
    have h1 := hc t (mem_sup_right hS.t_mem_Q)
    have h2 := (mem_normalizer_iff.1 (inv_mem hgF) _).1 h1
    have h3 := (mem_normalizer_iff.1 (inv_mem htF) _).1 h2
    have h4 := inv_mem h3
    rwa [show (t⁻¹ * (g⁻¹ * (g * t * g⁻¹ * t⁻¹) * g⁻¹⁻¹) * t⁻¹⁻¹)⁻¹ = (g * t)⁻¹ * (t * g) by
      group] at h4
  have hgB := hS.mem_normalizer_B1_of_crossed_mem_F1 hgF hgt
  obtain ⟨c, hcQC, d, hd, rfl⟩ := hS.exists_mul_of_mem_normalizer_Q1_inf_B1 hg hgB
  obtain ⟨hcQ, hcC⟩ := mem_inf.1 hcQC
  have hDQ : miyamotoD1 h L η t ≤ miyamotoF1G h L η t ⊔ Q := by
    rw [← hS.F1_sup_zpowers]
    exact sup_le le_sup_left (zpowers_le.2 (mem_sup_right hS.t_mem_Q))
  have hdQ := hDQ hd
  have hcB : c ∈ normalizer (miyamotoB1 h L η t : Set G) := by
    have := mul_mem hgB (inv_mem (hS.D1_le_normalizer_B1 hd))
    rwa [mul_inv_cancel_right] at this
  have hcA := hS.normalizer_B1_le_normalizer_A1 hcB
  obtain ⟨-, hcomm⟩ := hS.Q1_mod_F1
  have hcF : ∀ x ∈ miyamotoF1G h L η t ⊔ Q, c * x * c⁻¹ * x⁻¹ ∈ miyamotoF1G h L η t := by
    intro x hx
    have hx' : d⁻¹ * x * d ∈ miyamotoF1G h L η t ⊔ Q := mul_mem (mul_mem (inv_mem hdQ) hx) hdQ
    have h1 := hc _ hx'
    have h2 : d⁻¹ * x * d * x⁻¹ ∈ miyamotoF1G h L η t := by
      have := hcomm d⁻¹ (inv_mem hdQ) x hx
      rwa [commutatorElement_def, inv_inv] at this
    have := mul_mem h1 h2
    rwa [show c * d * (d⁻¹ * x * d) * (c * d)⁻¹ * (d⁻¹ * x * d)⁻¹ * (d⁻¹ * x * d * x⁻¹) =
      c * x * c⁻¹ * x⁻¹ by group] at this
  have hstab : ∀ g' : gramSU h (miyamotoJ4 K),
      ((hS.act ⟨c, hcC⟩ g' : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) ∈ miyamotoA1 h ↔
        (g' : GL (Fin 4) K) ∈ miyamotoA1 h := by
    intro g'
    rw [← symm_mem_miyamotoPull_iff h L η, hS.coe_symm_act_apply,
      ← symm_mem_miyamotoPull_iff h L η (g := g')]
    exact (mem_normalizer_iff.1 hcA _).symm
  have hfix : ∀ g' : gramSU h (miyamotoJ4 K), (g' : GL (Fin 4) K) ∈ miyamotoP h →
      (g' : GL (Fin 4) K)⁻¹ * (hS.act ⟨c, hcC⟩ g' : GL (Fin 4) K) ∈ miyamotoA1 h := by
    intro g' hg'
    set p := ((η.symm g' : L) : G) with hp
    have hpP : p ∈ miyamotoPG h L η := (symm_mem_miyamotoPull_iff h L η).2 hg'
    have hpQ1 : p ∈ miyamotoF1G h L η t ⊔ Q := mem_sup_right (hS.P_le_Q hpP)
    have h1 := hcF p hpQ1
    have h2 : c * p * c⁻¹ * p⁻¹ ∈ T := by
      have hcp : c * p * c⁻¹ ∈ Q := (mem_normalizer_iff.1 hcQ p).1 (hS.P_le_Q hpP)
      exact mul_mem (hS.Q_le_T hcp) (inv_mem (hS.P_le_T hpP))
    have h3 : c * p * c⁻¹ * p⁻¹ ∈ miyamotoA1G h L η := by
      rw [← hS.F1_inf_T]
      exact mem_inf.2 ⟨h1, h2⟩
    have h4 : p⁻¹ * (c * p * c⁻¹) ∈ miyamotoA1G h L η := by
      have := (mem_normalizer_iff.1 (hS.PG_le_normalizer_A1 (inv_mem hpP)) _).1 h3
      rwa [show p⁻¹ * (c * p * c⁻¹ * p⁻¹) * p⁻¹⁻¹ = p⁻¹ * (c * p * c⁻¹) by group] at this
    rw [← hS.coe_symm_act_apply ⟨c, hcC⟩, hp, ← L.coe_inv, ← map_inv, ← L.coe_mul,
      ← map_mul, symm_mem_miyamotoPull_iff, coe_mul, coe_inv] at h4
    exact h4
  obtain ⟨s, ⟨p, hpP, i, hiI, hs⟩, hα⟩ :=
    (stabilizes_A1_and_fixes_mod_A1_iff h (hS.act ⟨c, hcC⟩)).1 ⟨hstab, hfix⟩
  rw [act_apply] at hα
  obtain ⟨z, hzL, hcz⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ s hα
  change c = ((η.symm s : L) : G) * z at hcz
  have hsC : ((η.symm s : L) : G) ∈ centralizer ({t} : Set G) :=
    hS.L_le_centralizer (η.symm s).2
  have hzt : z ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    refine ⟨hzL, ?_⟩
    have := mul_mem (inv_mem hsC) hcC
    rwa [hcz, inv_mul_cancel_left] at this
  have hpS : p ∈ gramSU h (miyamotoJ4 K) := miyamotoUnipotent_le_SU h false false hpP
  have hiS : i ∈ gramSU h (miyamotoJ4 K) := miyamotoI1_le_SU h hiI
  have hspi : s = ⟨p, hpS⟩ * ⟨i, hiS⟩ := Subtype.ext hs
  have hsG : ((η.symm s : L) : G) = ((η.symm ⟨p, hpS⟩ : L) : G) * ((η.symm ⟨i, hiS⟩ : L) : G) := by
    rw [hspi, map_mul, L.coe_mul]
  have hp' : ((η.symm ⟨p, hpS⟩ : L) : G) ∈ miyamotoPG h L η :=
    (symm_mem_miyamotoPull_iff h L η).2 hpP
  have hi' : ((η.symm ⟨i, hiS⟩ : L) : G) ∈ miyamotoI1G h L η :=
    (symm_mem_miyamotoPull_iff h L η).2 hiI
  rw [hcz, hsG]
  have hzQ : z ∈ miyamotoF1G h L η t ⊔ Q := mem_sup_right ((zpowers_le.2 hS.t_mem_Q) hzt)
  have hpQ : ((η.symm ⟨p, hpS⟩ : L) : G) ∈ miyamotoF1G h L η t ⊔ Q :=
    mem_sup_right (hS.P_le_Q hp')
  exact mul_mem (mul_mem (mul_mem (mem_sup_left hpQ) (mem_sup_right hi')) (mem_sup_left hzQ))
    (mem_sup_left hdQ)

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

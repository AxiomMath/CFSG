module

public import CFSG.LocalAnalysis.EvenBN.U4.RootF1Abelian

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (exists_mem_inf_centralizer_mul_of_coprime
  card_sup_mul_card_inf_eq mem_normalizer_inf mem_normalizer_sup)
open scoped commutatorElement

section ModelU

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem conj_miyamotoIHom_mem_rootA (p : Kˣ × Kˣ) {y : GL (Fin 4) K}
    (hy : y ∈ miyamotoRootA h) :
    (miyamotoIHom h p)⁻¹ * y * miyamotoIHom h p ∈ miyamotoRootA h := by
  obtain ⟨a, rfl⟩ := hy
  rw [miyamotoIHom_conj_rootA]
  exact ⟨_, rfl⟩

theorem miyamotoI_le_normalizer_rootA :
    miyamotoI h ≤ normalizer (miyamotoRootA h : Set (GL (Fin 4) K)) := by
  rintro _ ⟨p, -, rfl⟩
  exact miyamotoIHom_mem_normalizer h (fun p _ hy => conj_miyamotoIHom_mem_rootA h p hy) p

end ModelU

@[expose] noncomputable def miyamotoFG {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  miyamotoEG h L η Q ⊔
    (miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G))

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem F_le_F1 (hS : Setting h L η t Q T) : miyamotoFG h L η t Q ≤ miyamotoF1G h L η t :=
  sup_le hS.E_le_F1 inf_le_left

theorem E_le_F (_hS : Setting h L η t Q T) : miyamotoEG h L η Q ≤ miyamotoFG h L η t Q :=
  le_sup_left

theorem exists_mul_of_mem_F (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoFG h L η t Q) :
    ∃ e ∈ miyamotoEG h L η Q, ∃ y ∈ miyamotoF1G h L η t ⊓
      centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G), x = e * y :=
  exists_mul_of_mem_sup_of_commute (fun _ he _ hy => hS.F1_comm (hS.E_le_F1 he) (mem_inf.1 hy).1)
    hx

theorem A1G_inf_centralizer_I1r2 (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) =
      miyamotoPull h L η (miyamotoRootC h) := by
  have : CharP K 2 := h.charP
  obtain ⟨-, hr2, -, -, -⟩ := hS.le_SU_facts
  rw [← miyamotoPull_inf_centralizer h L η _ hr2, miyamotoA1_inf_centralizer_I1r2 h hS.two_le]

theorem exists_mul_of_mem_Z2 (hS : Setting h L η t Q T) {z : G}
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) :
    ∃ z₀ ∈ miyamotoZG h L η, ∃ c ∈ miyamotoPull h L η (miyamotoRootC h), z = z₀ * c := by
  have : CharP K 2 := h.charP
  exact exists_mul_of_mem_miyamotoPull h L η
    ((miyamotoZ_le_P h).trans (miyamotoUnipotent_le_SU h false false)) (hS.rootC_le_SU)
    (miyamotoZ_mul_rootC h) hz

theorem rootC_le_Z2 (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootC h) ≤ miyamotoPull h L η (miyamotoZ2 h) := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η (miyamotoRootC_le_Z2 h)

theorem Z2_le_A1 (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoZ2 h) ≤ miyamotoA1G h L η := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η (miyamotoZ2_le_A1 h)

theorem ZP_le_Z2 (_hS : Setting h L η t Q T) :
    miyamotoZG h L η ≤ miyamotoPull h L η (miyamotoZ2 h) := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η (miyamotoZ_le_Z2 h)

theorem rootC_le_Yc (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootC h) ≤
      miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) := by
  rw [← hS.A1G_inf_centralizer_I1r2]
  exact fun c hc => ⟨hS.A1_le_F1 hc.1, hc.2⟩

theorem Z2_le_F (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoZ2 h) ≤ miyamotoFG h L η t Q := by
  intro z hz
  obtain ⟨z₀, hz₀, c, hc, rfl⟩ := hS.exists_mul_of_mem_Z2 hz
  exact mul_mem (mem_sup_left (hS.ZP_le_E hz₀)) (mem_sup_right (hS.rootC_le_Yc hc))

theorem crossed_mem_Z2_of_mem_F (hS : Setting h L η t Q T) {x : G}
    (hx : x ∈ miyamotoFG h L η t Q) : x⁻¹ * t * x * t ∈ miyamotoPull h L η (miyamotoZ2 h) := by
  obtain ⟨e, he, y, hy, rfl⟩ := hS.exists_mul_of_mem_F hx
  rw [hS.crossed_mul_D1 (hS.F1_le_D1 (hS.E_le_F1 he)) (hS.F1_le_D1 hy.1)]
  refine mul_mem (hS.ZP_le_Z2 (hS.sec3_3.2.2.2.2.2.1 e he)) (hS.rootC_le_Z2 ?_)
  rw [← hS.A1G_inf_centralizer_I1r2]
  exact ⟨hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 hy.1),
    hS.crossed_mem_centralizer hS.tori_le_IG.2.1 hy.2⟩

theorem exists_F_crossed_eq (hS : Setting h L η t Q T) {z : G}
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) :
    ∃ x ∈ miyamotoFG h L η t Q, x⁻¹ * t * x * t = z := by
  obtain ⟨z₀, hz₀, c, hc, rfl⟩ := hS.exists_mul_of_mem_Z2 hz
  obtain ⟨e, he, hez⟩ := hS.exists_E_crossed_eq hz₀
  have hcA : c ∈ miyamotoA1G h L η ⊓
      centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) := by
    rw [hS.A1G_inf_centralizer_I1r2]
    exact hc
  obtain ⟨y, hy, hyJ, hyc⟩ := hS.exists_F1_centralizer_crossed_eq hS.tori_le_IG.2.1 hcA.1 hcA.2
  refine ⟨e * y, mul_mem (mem_sup_left he) (mem_sup_right ⟨hy, hyJ⟩), ?_⟩
  rw [hS.crossed_mul_D1 (hS.F1_le_D1 (hS.E_le_F1 he)) (hS.F1_le_D1 hy), hez, hyc]

theorem mem_E_sup_A1_of_crossed_mem_ZP (hS : Setting h L η t Q T) {w : G}
    (hw : w ∈ miyamotoF1G h L η t) (hδ : w⁻¹ * t * w * t ∈ miyamotoZG h L η) :
    ∃ e ∈ miyamotoEG h L η Q, ∃ a ∈ miyamotoA1G h L η, w = e * a := by
  obtain ⟨e, he, hew⟩ := hS.exists_E_crossed_eq hδ
  have heF := hS.E_le_F1 he
  refine ⟨e, he, e⁻¹ * w, (hS.crossed_eq_one_iff_F1 (mul_mem (inv_mem heF) hw)).1 ?_, by group⟩
  rw [hS.crossed_mul_D1 (inv_mem (hS.F1_le_D1 heF)) (hS.F1_le_D1 hw),
    hS.crossed_inv_D1 (hS.F1_le_D1 heF), hew, inv_mul_cancel]

theorem commutator_Z2_P_mem_ZP (_hS : Setting h L η t Q T) {z p : G}
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) (hp : p ∈ miyamotoPG h L η) :
    ⁅z, p⁆ ∈ miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hz
  obtain ⟨k, hk, rfl⟩ := (mem_miyamotoPull h L η).1 hp
  have := ((mem_Z2_iff_commutator_mem h).1 hg).2 _ hk
  have e : ⁅((η.symm g : L) : G), ((η.symm k : L) : G)⁆ = ((η.symm ⁅g, k⁆ : L) : G) := by
    simp only [commutatorElement_def, map_mul, map_inv, coe_mul, coe_inv]
  rw [e]
  exact (symm_mem_miyamotoPull_iff h L η).2 (by
    simp only [commutatorElement_def, coe_mul, coe_inv] at this ⊢
    exact this)

theorem PG_le_normalizer_A1 (_hS : Setting h L η t Q T) :
    miyamotoPG h L η ≤ normalizer (miyamotoA1G h L η : Set G) := by
  have : CharP K 2 := h.charP
  intro x hx
  have : x ∈ L ⊓ normalizer (miyamotoA1G h L η : Set G) := by
    rw [← miyamotoPull_inf_normalizer h L η (miyamotoUnipotent_le_SU h true false)]
    exact miyamotoPull_mono h L η (le_inf (miyamotoUnipotent_le_SU h false false)
      (le_normalizer.trans (normalizer_P_le_normalizer_A1 h))) hx
  exact this.2

theorem PG_le_C (hS : Setting h L η t Q T) : miyamotoPG h L η ≤ centralizer ({t} : Set G) :=
  (miyamotoPull_le h L η _).trans hS.L_le_centralizer

theorem PG_le_normalizer_B1 (hS : Setting h L η t Q T) :
    miyamotoPG h L η ≤ normalizer (miyamotoB1 h L η t : Set G) := fun _ hx =>
  mem_normalizer_sup (mem_normalizer_zpowers_of_comm (mem_centralizer_singleton_iff.1
    (hS.PG_le_C hx))) (hS.PG_le_normalizer_A1 hx)

theorem PG_le_normalizer_F1 (hS : Setting h L η t Q T) :
    miyamotoPG h L η ≤ normalizer (miyamotoF1G h L η t : Set G) :=
  hS.PG_le_normalizer_B1.trans hS.normalizer_B1_le_normalizer_F1

theorem commutator_F_P_mem (hS : Setting h L η t Q T) {x p : G}
    (hx : x ∈ miyamotoFG h L η t Q) (hp : p ∈ miyamotoPG h L η) :
    ∃ e ∈ miyamotoEG h L η Q, ∃ a ∈ miyamotoA1G h L η, x * p * x⁻¹ * p⁻¹ = e * a := by
  have hxF := hS.F_le_F1 hx
  have hpF := hS.PG_le_normalizer_F1 hp
  have hpt : p * t = t * p := mem_centralizer_singleton_iff.1 (hS.PG_le_C hp)
  have hy : p * x⁻¹ * p⁻¹ ∈ miyamotoF1G h L η t := (mem_normalizer_iff.1 hpF _).1 (inv_mem hxF)
  have hw : x * p * x⁻¹ * p⁻¹ ∈ miyamotoF1G h L η t := by
    rw [show x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹) by group]
    exact mul_mem hxF hy
  refine hS.mem_E_sup_A1_of_crossed_mem_ZP hw ?_
  have hxD := hS.F1_le_D1 hxF
  rw [show x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹) by group,
    hS.crossed_mul_D1 hxD (hS.F1_le_D1 hy),
    CFSG.EvenSmallLie.UnitarySix.YamadaD.crossed_conj (x := x⁻¹) hpt, hS.crossed_inv_D1 hxD]
  have := hS.commutator_Z2_P_mem_ZP (hS.crossed_mem_Z2_of_mem_F hx) hp
  rw [commutatorElement_def] at this
  rwa [← mul_assoc, ← mul_assoc]

theorem E_inf_PG (hS : Setting h L η t Q T) :
    miyamotoEG h L η Q ⊓ miyamotoPG h L η = miyamotoZG h L η := by
  have : CharP K 2 := h.charP
  refine le_antisymm (fun e he => (hS.crossed_eq_one_iff_E he.1).1 ?_)
    (le_inf hS.ZP_le_E (miyamotoPull_mono h L η (miyamotoZ_le_P h)))
  have het : e * t = t * e := mem_centralizer_singleton_iff.1 (hS.PG_le_C he.2)
  rw [mul_assoc e⁻¹, ← het, inv_mul_cancel_left, hS.t_mul_t]

theorem E_comm_PG (hS : Setting h L η t Q T) {e p : G} (he : e ∈ miyamotoEG h L η Q)
    (hp : p ∈ miyamotoPG h L η) : e * p = p * e :=
  (mem_centralizer_iff.1 (hS.E_le_centralizer_P he) p hp).symm

theorem A2G_le_PG (_hS : Setting h L η t Q T) : miyamotoA2G h L η ≤ miyamotoPG h L η := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η (miyamotoA2_le_P h)

theorem A1G_le_PG (_hS : Setting h L η t Q T) : miyamotoA1G h L η ≤ miyamotoPG h L η :=
  miyamotoPull_mono h L η (miyamotoA1_le_P h)

theorem card_E_sup_A2 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) = (2 ^ f) ^ 6 := by
  have : CharP K 2 := h.charP
  have hinf : miyamotoEG h L η Q ⊓ miyamotoA2G h L η = miyamotoZG h L η := by
    refine le_antisymm (fun e he => ?_) (le_inf hS.ZP_le_E (miyamotoPull_mono h L η
      ((miyamotoZ_le_Z2 h).trans (miyamotoZ2_le_A2 h))))
    rw [← hS.E_inf_PG]
    exact ⟨he.1, hS.A2G_le_PG he.2⟩
  have hN : miyamotoA2G h L η ≤ normalizer (miyamotoEG h L η Q : Set G) := fun a ha =>
    mem_normalizer_fintype fun e he => by
      rw [← hS.E_comm_PG he (hS.A2G_le_PG ha), mul_inv_cancel_right]
      exact he
  have key := card_sup_mul_card_inf_eq hN
  rw [hinf, hS.card_E, card_miyamotoA2G, hS.card_ZP] at key
  have : Nat.card (miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) * 2 ^ f =
      (2 ^ f) ^ 6 * 2 ^ f := by rw [key]; ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) this

theorem conj_EA2_eq (hS : Setting h L η t Q T) {x : G} (hx : x ∈ miyamotoFG h L η t Q) :
    x ∈ normalizer ((miyamotoEG h L η Q ⊔ miyamotoA2G h L η : Subgroup G) : Set G) := by
  have : CharP K 2 := h.charP
  set EA := miyamotoEG h L η Q ⊔ miyamotoA2G h L η with hEA
  set W := EA.map (MulAut.conj x).toMonoidHom with hW
  have hxF := hS.F_le_F1 hx
  have hconjE : ∀ e ∈ miyamotoEG h L η Q, x * e * x⁻¹ ∈ miyamotoEG h L η Q :=
    fun e he => hS.conj_mem_E_of_mem_F1 hxF he
  have hEW : miyamotoEG h L η Q ≤ W := fun e he => by
    refine ⟨x⁻¹ * e * x, mem_sup_left ?_, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group⟩
    have := hS.conj_mem_E_of_mem_F1 (inv_mem hxF) he
    rwa [inv_inv] at this
  have hEAcomm : ∀ e ∈ miyamotoEG h L η Q, ∀ a ∈ miyamotoA2G h L η, e * a = a * e :=
    fun e he a ha => hS.E_comm_PG he (hS.A2G_le_PG ha)
  have hWEP : ∀ w ∈ W, ∃ e ∈ miyamotoEG h L η Q, ∃ p ∈ miyamotoPG h L η, w = e * p := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute hEAcomm hy
    obtain ⟨e', he', a', ha', hea⟩ := hS.commutator_F_P_mem hx (hS.A2G_le_PG ha)
    refine ⟨(x * e * x⁻¹) * e', mul_mem (hconjE e he) he', a' * a,
      mul_mem (hS.A1G_le_PG ha') (hS.A2G_le_PG ha), ?_⟩
    have e1 : x * a * x⁻¹ = e' * a' * a := by rw [← hea]; group
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    calc x * (e * a) * x⁻¹ = (x * e * x⁻¹) * (x * a * x⁻¹) := by group
      _ = (x * e * x⁻¹) * e' * (a' * a) := by rw [e1]; group
  set X := W ⊓ miyamotoPG h L η with hX
  have hWsq : ∀ w ∈ W, w * w ∈ miyamotoEG h L η Q := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute hEAcomm hy
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    have ha2 : a * a ∈ miyamotoZG h L η := hS.A2_mod_Z.1 a ha
    have e1 : x * (e * a) * x⁻¹ * (x * (e * a) * x⁻¹) = x * (e * e * (a * a)) * x⁻¹ := by
      have hea := hEAcomm e he a ha
      calc x * (e * a) * x⁻¹ * (x * (e * a) * x⁻¹) = x * (e * (a * e) * a) * x⁻¹ := by group
        _ = x * (e * (e * a) * a) * x⁻¹ := by rw [← hea]
        _ = x * (e * e * (a * a)) * x⁻¹ := by group
    rw [e1]
    exact hconjE _ (mul_mem (mul_mem he he) (hS.ZP_le_E ha2))
  have hWcomm : ∀ w ∈ W, ∀ w' ∈ W, ⁅w, w'⁆ ∈ miyamotoEG h L η Q := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    obtain ⟨e, he, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_commute hEAcomm hy
    obtain ⟨e', he', a', ha', rfl⟩ := exists_mul_of_mem_sup_of_commute hEAcomm hy'
    simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    have hc : ⁅e * a, e' * a'⁆ = ⁅a, a'⁆ := by
      have hee : e * e' = e' * e := hS.F1_comm (hS.E_le_F1 he) (hS.E_le_F1 he')
      have h1 := hEAcomm e he a' ha'
      have h2 := hEAcomm e' he' a ha
      have h3 := hEAcomm e he a ha
      have h4 := hEAcomm e' he' a' ha'
      rw [commutatorElement_def, commutatorElement_def]
      calc e * a * (e' * a') * (e * a)⁻¹ * (e' * a')⁻¹
          = e * (a * e') * a' * a⁻¹ * e⁻¹ * a'⁻¹ * e'⁻¹ := by group
        _ = e * e' * a * a' * a⁻¹ * e⁻¹ * a'⁻¹ * e'⁻¹ := by rw [← h2]; group
        _ = e * e' * (a * a' * a⁻¹ * (e⁻¹ * a'⁻¹)) * e'⁻¹ := by group
        _ = e * e' * (a * a' * a⁻¹ * (a'⁻¹ * e⁻¹)) * e'⁻¹ := by
            rw [show e⁻¹ * a'⁻¹ = a'⁻¹ * e⁻¹ by
              rw [← mul_inv_rev, ← mul_inv_rev, h1]]
        _ = e * e' * (a * a' * a⁻¹ * a'⁻¹) * e⁻¹ * e'⁻¹ := by group
        _ = (a * a' * a⁻¹ * a'⁻¹) * (e * e') * e⁻¹ * e'⁻¹ := by
            have hz : (a * a' * a⁻¹ * a'⁻¹) ∈ miyamotoZG h L η := by
              have := hS.A2_mod_Z.2 a ha a' ha'
              rwa [commutatorElement_def] at this
            have hzE : (e * e') * (a * a' * a⁻¹ * a'⁻¹) = (a * a' * a⁻¹ * a'⁻¹) * (e * e') :=
              hS.F1_comm (mul_mem (hS.E_le_F1 he) (hS.E_le_F1 he'))
                (hS.E_le_F1 (hS.ZP_le_E hz))
            rw [hzE]
        _ = a * a' * a⁻¹ * a'⁻¹ := by rw [hee]; group
    have e1 : ⁅x * (e * a) * x⁻¹, x * (e' * a') * x⁻¹⁆ = x * ⁅e * a, e' * a'⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, hc]
    exact hconjE _ (hS.ZP_le_E (hS.A2_mod_Z.2 a ha a' ha'))
  have hXsq : ∀ y ∈ X, y * y ∈ miyamotoZG h L η := fun y hy => by
    rw [← hS.E_inf_PG]
    exact ⟨hWsq y (mem_inf.1 hy).1, mul_mem (mem_inf.1 hy).2 (mem_inf.1 hy).2⟩
  have hXcomm : ∀ y ∈ X, ∀ y' ∈ X, ⁅y, y'⁆ ∈ miyamotoZG h L η := fun y hy y' hy' => by
    rw [← hS.E_inf_PG]
    obtain ⟨hy1, hy2⟩ := mem_inf.1 hy
    obtain ⟨hy1', hy2'⟩ := mem_inf.1 hy'
    refine mem_inf.2 ⟨hWcomm y hy1 y' hy1', ?_⟩
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hy2 hy2') (inv_mem hy2)) (inv_mem hy2')
  have hWsup : W = miyamotoEG h L η Q ⊔ X := by
    refine le_antisymm (fun w hw => ?_) (sup_le hEW inf_le_left)
    obtain ⟨e, he, p, hp, rfl⟩ := hWEP w hw
    have hpW : p ∈ W := by
      have := mul_mem (inv_mem (hEW he)) hw
      rwa [inv_mul_cancel_left] at this
    exact mul_mem (mem_sup_left he) (mem_sup_right ⟨hpW, hp⟩)
  have hcardW : Nat.card W = (2 ^ f) ^ 6 := by
    rw [hW, Subgroup.card_map_of_injective (MulAut.conj x).injective, hEA, hS.card_E_sup_A2]
  have hXN : X ≤ normalizer (miyamotoEG h L η Q : Set G) := fun y hy =>
    mem_normalizer_fintype fun e he => by
      rw [← hS.E_comm_PG he hy.2, mul_inv_cancel_right]
      exact he
  have hEX : miyamotoEG h L η Q ⊓ X = miyamotoZG h L η := by
    refine le_antisymm (fun e he => ?_) fun z hz => ⟨hS.ZP_le_E hz, hEW (hS.ZP_le_E hz),
      miyamotoPull_mono h L η (miyamotoZ_le_P h) hz⟩
    rw [← hS.E_inf_PG]
    exact ⟨(mem_inf.1 he).1, (mem_inf.1 (mem_inf.1 he).2).2⟩
  have key := card_sup_mul_card_inf_eq hXN
  rw [← hWsup, hcardW, hEX, hS.card_E, hS.card_ZP] at key
  have hcardX : Nat.card X = (2 ^ f) ^ 5 := by
    have : (2 ^ f) ^ 2 * Nat.card X = (2 ^ f) ^ 2 * (2 ^ f) ^ 5 := by rw [← key]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) this
  have hXA := (hS.card_le_and_eq_A2G_of_mod_Z inf_le_right hXsq hXcomm).2 hcardX.ge
  have hfin : W = EA := by
    rw [hWsup, hX, hXA, hEA]
  rw [mem_normalizer_iff_map_conj_eq]
  exact hfin

theorem commutator_F_A2_mem_EZ2 (hS : Setting h L η t Q T) {x a : G}
    (hx : x ∈ miyamotoFG h L η t Q) (ha : a ∈ miyamotoA2G h L η) :
    ∃ e ∈ miyamotoEG h L η Q, ∃ z ∈ miyamotoPull h L η (miyamotoZ2 h),
      x * a * x⁻¹ * a⁻¹ = e * z := by
  have : CharP K 2 := h.charP
  have hxF := hS.F_le_F1 hx
  have hxa : x * a * x⁻¹ ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η :=
    (mem_normalizer_iff.1 (hS.conj_EA2_eq hx) a).1 (mem_sup_right ha)
  have hc : x * a * x⁻¹ * a⁻¹ ∈ miyamotoEG h L η Q ⊔ miyamotoA2G h L η :=
    mul_mem hxa (inv_mem (mem_sup_right ha))
  obtain ⟨e, he, a', ha', hea⟩ := exists_mul_of_mem_sup_of_commute
    (fun e he a ha => hS.E_comm_PG he (hS.A2G_le_PG ha)) hc
  have hcF : x * a * x⁻¹ * a⁻¹ ∈ miyamotoF1G h L η t := by
    rw [show x * a * x⁻¹ * a⁻¹ = x * (a * x⁻¹ * a⁻¹) by group]
    exact mul_mem hxF ((mem_normalizer_iff.1 (hS.PG_le_normalizer_F1 (hS.A2G_le_PG ha)) _).1
      (inv_mem hxF))
  have ha'F : a' ∈ miyamotoF1G h L η t := by
    have := mul_mem (inv_mem (hS.E_le_F1 he)) hcF
    rwa [hea, inv_mul_cancel_left] at this
  have ha'A : a' ∈ miyamotoA1G h L η := by
    rw [← hS.F1_inf_B1]
    refine ⟨ha'F, ?_⟩
    rw [← hS.D1_inf_C]
    exact ⟨hS.F1_le_D1 ha'F, hS.PG_le_C (hS.A2G_le_PG ha')⟩
  refine ⟨e, he, a', ?_, hea⟩
  rw [← miyamotoA1G_inf_miyamotoA2G]
  exact ⟨ha'A, ha'⟩

theorem rootA_le_SU (_hS : Setting h L η t Q T) : miyamotoRootA h ≤ gramSU h (miyamotoJ4 K) := by
  have : CharP K 2 := h.charP
  exact (miyamotoRootA_le_A2 h).trans ((miyamotoA2_le_P h).trans
    (miyamotoUnipotent_le_SU h false false))

theorem rootA_le_A2G (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootA h) ≤ miyamotoA2G h L η := by
  have : CharP K 2 := h.charP
  exact miyamotoPull_mono h L η (miyamotoRootA_le_A2 h)

theorem IG_le_normalizer_rootA (hS : Setting h L η t Q T) :
    miyamotoIG h L η ≤ normalizer (miyamotoPull h L η (miyamotoRootA h) : Set G) := by
  have : CharP K 2 := h.charP
  intro x hx
  have : x ∈ L ⊓ normalizer (miyamotoPull h L η (miyamotoRootA h) : Set G) := by
    rw [← miyamotoPull_inf_normalizer h L η hS.rootA_le_SU]
    exact miyamotoPull_mono h L η (le_inf (miyamotoI_le_gramSU h)
      (miyamotoI_le_normalizer_rootA h)) hx
  exact this.2

theorem exists_I1r2_fpf_rootA (hS : Setting h L η t Q T) :
    ∃ j ∈ miyamotoPull h L η (miyamotoI1r2 h), ∀ u ∈ miyamotoPull h L η (miyamotoRootA h),
      j * u * j⁻¹ = u → u = 1 := by
  have : CharP K 2 := h.charP
  obtain ⟨s, hs, hs2⟩ := exists_fixed_unit_sq_ne_one h hS.two_le
  have hDI : miyamotoIHom h (s, s⁻¹) ∈ miyamotoI1r2 h := (mem_miyamotoI1r2 h).2 ⟨s, hs, rfl⟩
  have hDS : miyamotoIHom h (s, s⁻¹) ∈ gramSU h (miyamotoJ4 K) :=
    hS.le_SU_facts.2.1 hDI
  refine ⟨_, (symm_mem_miyamotoPull_iff h L η (g := ⟨_, hDS⟩)).2 hDI, fun u hu e => ?_⟩
  obtain ⟨g, ⟨a, hga⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hu
  have e' : (⟨_, hDS⟩ : gramSU h (miyamotoJ4 K)) * g * (⟨_, hDS⟩)⁻¹ = g := by
    apply η.symm.injective
    apply Subtype.ext
    simpa only [map_mul, map_inv, coe_mul, coe_inv] using e
  have e2 : (miyamotoIHom h (s, s⁻¹))⁻¹ * (g : GL (Fin 4) K) * miyamotoIHom h (s, s⁻¹) = g := by
    have := congrArg Subtype.val e'
    simp only [coe_mul, coe_inv] at this
    calc (miyamotoIHom h (s, s⁻¹))⁻¹ * (g : GL (Fin 4) K) * miyamotoIHom h (s, s⁻¹) =
        (miyamotoIHom h (s, s⁻¹))⁻¹ * (miyamotoIHom h (s, s⁻¹) * g *
          (miyamotoIHom h (s, s⁻¹))⁻¹) * miyamotoIHom h (s, s⁻¹) := by rw [this]
      _ = g := by group
  rw [hga, miyamotoIHom_conj_rootA, miyamotoXGL_inj] at e2
  have ha : a = 0 := by
    refine eq_zero_of_mul_eq_self ?_ e2.1
    simp only [coe_miyamotoWeightA, Units.val_inv_eq_inv_val, inv_inv]
    rwa [← sq]
  have : g = 1 := Subtype.ext (by rw [hga, ha, miyamotoXGL_zero, OneMemClass.coe_one])
  rw [this, map_one, OneMemClass.coe_one]

theorem rootC_le_centralizer_I1r2 (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootC h) ≤
      centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G) := fun c hc => by
  rw [← hS.A1G_inf_centralizer_I1r2] at hc
  exact hc.2

theorem mul_mem_F1_of_E_Z2 (hS : Setting h L η t Q T) {e z : G} (he : e ∈ miyamotoEG h L η Q)
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) : e * z ∈ miyamotoF1G h L η t :=
  mul_mem (hS.E_le_F1 he) (hS.A1_le_F1 (hS.Z2_le_A1 hz))

theorem conj_P_E_Z2_mem_E (hS : Setting h L η t Q T) {p e z : G}
    (hp : p ∈ miyamotoPG h L η) (he : e ∈ miyamotoEG h L η Q)
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) :
    p * (e * z) * p⁻¹ * (e * z)⁻¹ ∈ miyamotoEG h L η Q := by
  have hpe : p * e = e * p := (hS.E_comm_PG he hp).symm
  have hc : ⁅p, z⁆ ∈ miyamotoZG h L η := by
    have := inv_mem (hS.commutator_Z2_P_mem_ZP hz hp)
    rwa [commutatorElement_inv] at this
  rw [commutatorElement_def] at hc
  have hzE : p * z * p⁻¹ * z⁻¹ ∈ miyamotoEG h L η Q := hS.ZP_le_E hc
  have e1 : p * (e * z) * p⁻¹ * (e * z)⁻¹ = e * (p * z * p⁻¹ * z⁻¹) * e⁻¹ := by
    calc p * (e * z) * p⁻¹ * (e * z)⁻¹ = (p * e) * z * p⁻¹ * z⁻¹ * e⁻¹ := by group
      _ = (e * p) * z * p⁻¹ * z⁻¹ * e⁻¹ := by rw [hpe]
      _ = e * (p * z * p⁻¹ * z⁻¹) * e⁻¹ := by group
  rw [e1]
  exact mul_mem (mul_mem he hzE) (inv_mem he)

theorem conj_I1r2_E_Z2_mem_E (hS : Setting h L η t Q T) {j e z : G}
    (hj : j ∈ miyamotoPull h L η (miyamotoI1r2 h)) (he : e ∈ miyamotoEG h L η Q)
    (hz : z ∈ miyamotoPull h L η (miyamotoZ2 h)) :
    j * (e * z) * j⁻¹ * (e * z)⁻¹ ∈ miyamotoEG h L η Q := by
  have hjI : j ∈ miyamotoIG h L η := hS.tori_le_IG.2.1 hj
  obtain ⟨z₀, hz₀, c, hc, rfl⟩ := hS.exists_mul_of_mem_Z2 hz
  have hjc : j * c = c * j :=
    mem_centralizer_iff.1 (hS.rootC_le_centralizer_I1r2 hc) j hj
  have hje : j * e * j⁻¹ ∈ miyamotoEG h L η Q :=
    (mem_normalizer_iff.1 (hS.IG_le_normalizer_E hjI) e).1 he
  have hjz : j * z₀ * j⁻¹ ∈ miyamotoZG h L η :=
    (mem_normalizer_iff.1 (hS.H_le_normalizer_ZP (hS.IG_le_H hjI)) z₀).1 hz₀
  have hcF : c ∈ miyamotoF1G h L η t := hS.A1_le_F1 (hS.Z2_le_A1 (hS.rootC_le_Z2 hc))
  set x := (j * e * j⁻¹) * (j * z₀ * j⁻¹) * z₀⁻¹ * e⁻¹ with hx
  have hxE : x ∈ miyamotoEG h L η Q :=
    mul_mem (mul_mem (mul_mem hje (hS.ZP_le_E hjz)) (inv_mem (hS.ZP_le_E hz₀))) (inv_mem he)
  have hxF : x ∈ miyamotoF1G h L η t := hS.E_le_F1 hxE
  have e1 : j * (e * (z₀ * c)) * j⁻¹ * (e * (z₀ * c))⁻¹ = c * x * c⁻¹ := by
    calc j * (e * (z₀ * c)) * j⁻¹ * (e * (z₀ * c))⁻¹
        = (j * e * j⁻¹) * (j * z₀ * j⁻¹) * (j * c) * j⁻¹ * c⁻¹ * z₀⁻¹ * e⁻¹ := by group
      _ = (j * e * j⁻¹) * (j * z₀ * j⁻¹) * (c * j) * j⁻¹ * c⁻¹ * z₀⁻¹ * e⁻¹ := by rw [hjc]
      _ = (j * e * j⁻¹) * (j * z₀ * j⁻¹) * c * c⁻¹ * z₀⁻¹ * e⁻¹ := by group
      _ = c * x * c⁻¹ := by
          rw [hx, show c * ((j * e * j⁻¹) * (j * z₀ * j⁻¹) * z₀⁻¹ * e⁻¹) * c⁻¹ =
            (j * e * j⁻¹) * (j * z₀ * j⁻¹) * z₀⁻¹ * e⁻¹ by
              rw [hS.F1_comm hcF hxF, mul_inv_cancel_right]]
          group
  rw [e1, hS.F1_comm hcF hxF, mul_inv_cancel_right]
  exact hxE

theorem commutator_Yc_rootA_mem_E (hS : Setting h L η t Q T) {y u : G}
    (hy : y ∈ miyamotoF1G h L η t ⊓ centralizer (miyamotoPull h L η (miyamotoI1r2 h) : Set G))
    (hu : u ∈ miyamotoPull h L η (miyamotoRootA h)) :
    y * u * y⁻¹ * u⁻¹ ∈ miyamotoEG h L η Q := by
  have : CharP K 2 := h.charP
  obtain ⟨hyF, hyJ⟩ := mem_inf.1 hy
  have hyFG : y ∈ miyamotoFG h L η t Q := mem_sup_right hy
  have hUP : miyamotoPull h L η (miyamotoRootA h) ≤ miyamotoPG h L η :=
    hS.rootA_le_A2G.trans hS.A2G_le_PG
  have hφ : ∀ v ∈ miyamotoPull h L η (miyamotoRootA h), ∃ e ∈ miyamotoEG h L η Q,
      ∃ z ∈ miyamotoPull h L η (miyamotoZ2 h), y * v * y⁻¹ * v⁻¹ = e * z := fun v hv =>
    hS.commutator_F_A2_mem_EZ2 hyFG (hS.rootA_le_A2G hv)
  have hφF : ∀ v ∈ miyamotoPull h L η (miyamotoRootA h),
      y * v * y⁻¹ * v⁻¹ ∈ miyamotoF1G h L η t := fun v hv => by
    obtain ⟨e, he, z, hz, hez⟩ := hφ v hv
    rw [hez]
    exact hS.mul_mem_F1_of_E_Z2 he hz
  have hA : ∀ p ∈ miyamotoPG h L η, ∀ v ∈ miyamotoPull h L η (miyamotoRootA h),
      p * (y * v * y⁻¹ * v⁻¹) * p⁻¹ * (y * v * y⁻¹ * v⁻¹)⁻¹ ∈ miyamotoEG h L η Q := by
    intro p hp v hv
    obtain ⟨e, he, z, hz, hez⟩ := hφ v hv
    rw [hez]
    exact hS.conj_P_E_Z2_mem_E hp he hz
  obtain ⟨j, hj, hfpf⟩ := hS.exists_I1r2_fpf_rootA
  have hjI : j ∈ miyamotoIG h L η := hS.tori_le_IG.2.1 hj
  have hjU := hS.IG_le_normalizer_rootA hjI
  obtain ⟨v, hv, rfl⟩ := exists_conj_mul_inv_eq hjU hfpf hu
  set φ : G → G := fun w => y * w * y⁻¹ * w⁻¹ with hφdef
  have hav : j * v * j⁻¹ ∈ miyamotoPull h L η (miyamotoRootA h) := (mem_normalizer_iff.1 hjU v).1 hv
  have hbv : v⁻¹ ∈ miyamotoPull h L η (miyamotoRootA h) := inv_mem hv
  have hjy : j * y = y * j := (mem_centralizer_iff.1 hyJ j hj)
  have hφj : φ (j * v * j⁻¹) = j * φ v * j⁻¹ := by
    simp only [hφdef]
    calc y * (j * v * j⁻¹) * y⁻¹ * (j * v * j⁻¹)⁻¹ = (y * j) * v * j⁻¹ * y⁻¹ * j * v⁻¹ * j⁻¹ := by
          group
      _ = (j * y) * v * (y * j)⁻¹ * j * v⁻¹ * j⁻¹ := by rw [hjy]; group
      _ = j * (y * v * y⁻¹ * v⁻¹) * j⁻¹ := by rw [← hjy]; group
  have X2 : φ (j * v * j⁻¹) * (φ v)⁻¹ ∈ miyamotoEG h L η Q := by
    rw [hφj]
    obtain ⟨e, he, z, hz, hez⟩ := hφ v hv
    simp only [hφdef]
    rw [hez]
    exact hS.conj_I1r2_E_Z2_mem_E hj he hz
  have X1 : (j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹ * (φ v⁻¹)⁻¹ ∈ miyamotoEG h L η Q :=
    hA _ (hUP hav) _ hbv
  have X3 : φ v⁻¹ * φ v ∈ miyamotoEG h L η Q := by
    have h1 := hA v (hUP hv) v⁻¹ hbv
    have e1 : v * φ v⁻¹ * v⁻¹ = (φ v)⁻¹ := by
      simp only [hφdef]
      group
    rw [e1] at h1
    have := inv_mem h1
    simp only [mul_inv_rev, inv_inv] at this
    simp only [hφdef, inv_inv]
    convert this using 1
  have hcocycle : φ (j * v * j⁻¹ * v⁻¹) =
      φ (j * v * j⁻¹) * ((j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹) := by
    simp only [hφdef]
    group
  have hF_a := hφF _ hav
  have hF_b := hφF _ hbv
  have hF_v := hφF _ hv
  have hF_c : (j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹ ∈ miyamotoF1G h L η t :=
    (mem_normalizer_iff.1 (hS.PG_le_normalizer_F1 (hUP hav)) _).1 hF_b
  change φ (j * v * j⁻¹ * v⁻¹) ∈ miyamotoEG h L η Q
  rw [hcocycle]
  have key : φ (j * v * j⁻¹) * ((j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹) =
      (φ (j * v * j⁻¹) * (φ v)⁻¹) *
        ((j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹ * (φ v⁻¹)⁻¹) * (φ v⁻¹ * φ v) := by
    have c1 := hS.F1_comm hF_v hF_b
    have c2 := hS.F1_comm (inv_mem hF_v) hF_c
    have c3 := hS.F1_comm hF_v hF_c
    calc φ (j * v * j⁻¹) * ((j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹)
        = φ (j * v * j⁻¹) * (φ v)⁻¹ * (φ v * ((j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹)) := by
          group
      _ = φ (j * v * j⁻¹) * (φ v)⁻¹ * (((j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹) * φ v) := by
          rw [c3]
      _ = (φ (j * v * j⁻¹) * (φ v)⁻¹) *
          ((j * v * j⁻¹) * φ v⁻¹ * (j * v * j⁻¹)⁻¹ * (φ v⁻¹)⁻¹) * (φ v⁻¹ * φ v) := by group
  rw [key]
  exact mul_mem (mul_mem X2 X1) X3

theorem commutator_F_A2_mem_E (hS : Setting h L η t Q T) {x a : G}
    (hx : x ∈ miyamotoFG h L η t Q) (ha : a ∈ miyamotoA2G h L η) :
    x * a * x⁻¹ * a⁻¹ ∈ miyamotoEG h L η Q := by
  have : CharP K 2 := h.charP
  obtain ⟨e, he, y, hy, rfl⟩ := hS.exists_mul_of_mem_F hx
  obtain ⟨z, hz, u, hu, rfl⟩ := exists_mul_of_mem_miyamotoPull h L η
    ((miyamotoZ2_le_A1 h).trans ((miyamotoA1_le_P h).trans (miyamotoUnipotent_le_SU h false false)))
    hS.rootA_le_SU (miyamotoZ2_mul_rootA h) ha
  have hyF := (mem_inf.1 hy).1
  have hzF : z ∈ miyamotoF1G h L η t := hS.A1_le_F1 (hS.Z2_le_A1 hz)
  have hzP := hS.A1G_le_PG (hS.Z2_le_A1 hz)
  have huP := hS.rootA_le_A2G.trans hS.A2G_le_PG hu
  have hc := hS.commutator_Yc_rootA_mem_E (Q := Q) hy hu
  have heF := hS.E_le_F1 he
  have hez : e * z = z * e := hS.E_comm_PG he hzP
  have heu : e * u = u * e := hS.E_comm_PG he huP
  have hyz : y * z = z * y := hS.F1_comm hyF hzF
  have hcz : (y * u * y⁻¹ * u⁻¹) * z = z * (y * u * y⁻¹ * u⁻¹) :=
    hS.F1_comm (hS.E_le_F1 hc) hzF
  have hey : e * y = y * e := hS.F1_comm heF hyF
  have hce : (y * u * y⁻¹ * u⁻¹) * e = e * (y * u * y⁻¹ * u⁻¹) :=
    hS.F1_comm (hS.E_le_F1 hc) heF
  have e1 : e * y * (z * u) * (e * y)⁻¹ * (z * u)⁻¹ = y * u * y⁻¹ * u⁻¹ := by
    calc e * y * (z * u) * (e * y)⁻¹ * (z * u)⁻¹
        = e * (y * z) * u * y⁻¹ * e⁻¹ * u⁻¹ * z⁻¹ := by group
      _ = e * (z * y) * u * y⁻¹ * e⁻¹ * u⁻¹ * z⁻¹ := by rw [hyz]
      _ = (e * z) * (y * u * y⁻¹ * u⁻¹) * (u * e⁻¹ * u⁻¹) * z⁻¹ := by group
      _ = (e * z) * (y * u * y⁻¹ * u⁻¹) * e⁻¹ * z⁻¹ := by
          rw [show u * e⁻¹ * u⁻¹ = e⁻¹ by
            rw [← (Commute.inv_left heu).eq, mul_inv_cancel_right]]
      _ = (z * e) * (y * u * y⁻¹ * u⁻¹) * e⁻¹ * z⁻¹ := by rw [hez]
      _ = z * (e * (y * u * y⁻¹ * u⁻¹) * e⁻¹) * z⁻¹ := by group
      _ = z * (y * u * y⁻¹ * u⁻¹) * z⁻¹ := by rw [← hce, mul_inv_cancel_right]
      _ = y * u * y⁻¹ * u⁻¹ := by rw [← hcz, mul_inv_cancel_right]
  rw [e1]
  exact hc

end Setting

end CFSG.LocalAnalysis.EvenBN.U4

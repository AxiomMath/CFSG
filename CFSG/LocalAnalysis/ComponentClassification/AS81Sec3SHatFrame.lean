module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatZ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

namespace Sec3Coord

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

@[expose] def piF (i : Fin 6) : Fin 6 := ![1, 0, 3, 2, 5, 4] i

theorem piF_piF (i : Fin 6) : piF (piF i) = i := by
  fin_cases i <;> rfl

@[expose] def qplus (y : Fin 6 → ZMod 2) : ZMod 2 :=
  y 0 ^ 2 + y 0 * y 1 + y 1 ^ 2 + y 2 * y 3 + y 4 ^ 2 + y 4 * y 5 + y 5 ^ 2

structure IsFrame (q : QuadraticForm (ZMod 2) V) (b : Fin 6 → V) : Prop where
  polar_eq : ∀ i j, polar q (b i) (b j) = if i = piF j then 1 else 0
  q_eq : ∀ i, q (b i) = ![1, 1, 0, 0, 1, 1] i

@[expose] noncomputable def vec (b : Fin 6 → V) : (Fin 6 → ZMod 2) →ₗ[ZMod 2] V :=
  Fintype.linearCombination (ZMod 2) b

theorem vec_apply (b : Fin 6 → V) (y : Fin 6 → ZMod 2) : vec b y = ∑ i, y i • b i :=
  Fintype.linearCombination_apply _ _ _

@[expose] noncomputable def coord (q : QuadraticForm (ZMod 2) V) (b : Fin 6 → V) :
    V →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.pi fun i => (polarBilin q).flip (b (piF i))

theorem coord_apply (b : Fin 6 → V) (v : V) (i : Fin 6) :
    coord q b v i = polar q v (b (piF i)) := rfl

variable {b : Fin 6 → V}

theorem polar_vec_left {w : V} (h : ∀ i, polar q (b i) w = 0) (y : Fin 6 → ZMod 2) :
    polar q (vec b y) w = 0 := by
  have e : polar q (vec b y) w = (polarBilin q).flip w (vec b y) := rfl
  rw [e, vec_apply, map_sum]
  simp only [map_smul, LinearMap.flip_apply, polarBilin_apply_apply, h, smul_zero,
    Finset.sum_const_zero]

theorem polar_vec (hb : IsFrame q b) (y : Fin 6 → ZMod 2) (j : Fin 6) :
    polar q (vec b y) (b j) = y (piF j) := by
  have e : polar q (vec b y) (b j) = (polarBilin q).flip (b j) (vec b y) := rfl
  rw [e, vec_apply, map_sum]
  simp only [map_smul, LinearMap.flip_apply, polarBilin_apply_apply, hb.polar_eq, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem coord_vec (hb : IsFrame q b) (y : Fin 6 → ZMod 2) : coord q b (vec b y) = y := by
  funext i
  rw [coord_apply, polar_vec hb, piF_piF]

theorem q_vec (hb : IsFrame q b) (y : Fin 6 → ZMod 2) : q (vec b y) = qplus y := by
  have hp := hb.polar_eq
  have hq := hb.q_eq
  rw [vec_apply, Fin.sum_univ_six]
  simp only [map_add_eq, polar_add_left, QuadraticMap.map_smul, polar_smul_left,
    polar_smul_right, hp, hq, smul_eq_mul]
  simp [piF]
  unfold qplus
  ring

theorem polar_sub_vec (hb : IsFrame q b) (v : V) (j : Fin 6) :
    polar q (v - vec b (coord q b v)) (b j) = 0 := by
  rw [polar_sub_left, polar_vec hb, coord_apply, piF_piF, sub_self]

theorem polar_sub_vec_vec (hb : IsFrame q b) (v : V) (y : Fin 6 → ZMod 2) :
    polar q (v - vec b (coord q b v)) (vec b y) = 0 := by
  rw [polar_comm]
  exact polar_vec_left (fun i => by rw [polar_comm]; exact polar_sub_vec hb v i) y

theorem map_eq (hb : IsFrame q b) (v : V) :
    q v = q (v - vec b (coord q b v)) + qplus (coord q b v) := by
  conv_lhs => rw [← sub_add_cancel v (vec b (coord q b v))]
  rw [map_add_eq, q_vec hb, polar_sub_vec_vec hb, add_zero]

@[expose] noncomputable def gamLin (q : QuadraticForm (ZMod 2) V) (b : Fin 6 → V)
    (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) : V →ₗ[ZMod 2] V :=
  LinearMap.id + vec b ∘ₗ g ∘ₗ coord q b - vec b ∘ₗ coord q b

theorem gamLin_apply (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) (v : V) :
    gamLin q b g v = v + vec b (g (coord q b v)) - vec b (coord q b v) := rfl

theorem coord_gamLin (hb : IsFrame q b) (g : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (v : V) : coord q b (gamLin q b g v) = g (coord q b v) := by
  rw [gamLin_apply, map_sub, map_add, coord_vec hb, coord_vec hb]
  abel

theorem gamLin_comp (hb : IsFrame q b) (g h : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) :
    gamLin q b g ∘ₗ gamLin q b h = gamLin q b (g ∘ₗ h) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, gamLin_apply g, coord_gamLin hb, gamLin_apply, gamLin_apply,
    LinearMap.comp_apply]
  abel

theorem gamLin_id : gamLin q b LinearMap.id = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [gamLin_apply, LinearMap.id_apply, add_sub_cancel_right, LinearMap.id_apply]

@[expose] noncomputable def gamEquiv (hb : IsFrame q b)
    (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofLinearMap (gamLin q b g) (gamLin q b g.symm)
    (by rw [gamLin_comp hb, LinearEquiv.comp_symm, gamLin_id])
    (by rw [gamLin_comp hb, LinearEquiv.symm_comp, gamLin_id])

theorem gamEquiv_apply (hb : IsFrame q b) (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (v : V) : gamEquiv hb g v = v + vec b (g (coord q b v)) - vec b (coord q b v) := rfl

theorem coord_gamEquiv (hb : IsFrame q b) (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (v : V) : coord q b (gamEquiv hb g v) = g (coord q b v) :=
  coord_gamLin hb g v

@[expose] noncomputable def gam (hb : IsFrame q b) :
    ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) →* (V ≃ₗ[ZMod 2] V) where
  toFun := gamEquiv hb
  map_one' := LinearEquiv.ext fun v => by
    change v + vec b (coord q b v) - vec b (coord q b v) = v
    rw [add_sub_cancel_right]
  map_mul' g h := LinearEquiv.ext fun v => by
    rw [LinearEquiv.mul_apply, gamEquiv_apply, gamEquiv_apply, coord_gamEquiv hb,
      gamEquiv_apply hb h, LinearEquiv.mul_apply]
    abel

theorem gam_apply (hb : IsFrame q b) (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (v : V) : gam hb g v = v + vec b (g (coord q b v)) - vec b (coord q b v) := rfl

theorem coord_gam (hb : IsFrame q b) (g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (v : V) : coord q b (gam hb g v) = g (coord q b v) :=
  coord_gamLin hb g v

theorem gam_apply_of_eq (hb : IsFrame q b) {g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    {v : V} (h : g (coord q b v) = coord q b v) : gam hb g v = v := by
  rw [gam_apply, h, add_sub_cancel_right]

theorem gam_mem_orthogonalGroup (hb : IsFrame q b)
    {g : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)} (hg : ∀ y, qplus (g y) = qplus y) :
    gam hb g ∈ TauCeti.QuadraticMap.orthogonalGroup q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  have e : gam hb g v = (v - vec b (coord q b v)) + vec b (g (coord q b v)) := by
    rw [gam_apply]
    abel
  rw [e, map_add_eq, q_vec hb, polar_sub_vec_vec hb, add_zero, hg, ← map_eq hb]

variable [FiniteDimensional (ZMod 2) V]

theorem map_eq_qplus (hb : IsFrame q b) (hdim : finrank (ZMod 2) V = 8) {a a₁ : V}
    (ha : q a = 0) (haa₁ : polar q a a₁ = 1) (hab : ∀ i, polar q a (b i) = 0)
    (ha₁b : ∀ i, polar q a₁ (b i) = 0) {v : V} (hv : polar q a v = 0) :
    q v = qplus (coord q b v) := by
  let E : ((ZMod 2 × ZMod 2) × (Fin 6 → ZMod 2)) →ₗ[ZMod 2] V :=
    ((LinearMap.fst _ _ _).smulRight a + (LinearMap.snd _ _ _).smulRight a₁) ∘ₗ
      LinearMap.fst _ _ _ + vec b ∘ₗ LinearMap.snd _ _ _
  have hE : ∀ c : (ZMod 2 × ZMod 2) × (Fin 6 → ZMod 2),
      E c = c.1.1 • a + c.1.2 • a₁ + vec b c.2 := fun _ => rfl
  have hbv : ∀ (w : V), (∀ i, polar q w (b i) = 0) → ∀ y, polar q (vec b y) w = 0 :=
    fun w hw y => polar_vec_left (fun i => by rw [polar_comm]; exact hw i) y
  have ha₁a : polar q a₁ a = 1 := by rw [polar_comm]; exact haa₁
  have hcoord : ∀ c, coord q b (E c) = c.2 := by
    intro c
    funext i
    rw [hE, map_add, map_add, map_smul, map_smul, coord_vec hb]
    simp only [Pi.add_apply, Pi.smul_apply, coord_apply, hab, ha₁b, smul_zero, zero_add]
  have hpa₁ : ∀ c, polar q (E c) a₁ = c.1.1 := by
    intro c
    rw [hE, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, haa₁,
      polar_self_eq_zero, hbv a₁ ha₁b]
    simp
  have hpa : ∀ c, polar q (E c) a = c.1.2 := by
    intro c
    rw [hE, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, ha₁a,
      polar_self_eq_zero, hbv a hab]
    simp
  have hinj : Function.Injective E := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have h1 := hpa₁ c
    have h2 := hpa c
    have h3 := hcoord c
    rw [hc, polar_zero_left] at h1 h2
    rw [hc, map_zero] at h3
    obtain ⟨⟨α, β⟩, y⟩ := c
    simp only at h1 h2 h3
    subst h1 h2 h3
    exact Submodule.zero_mem _
  have hsurj : Function.Surjective E := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj
    rw [hdim]
    simp [Module.finrank_prod]
  obtain ⟨c, rfl⟩ := hsurj v
  have hβ : c.1.2 = 0 := by rw [← hpa c, polar_comm]; exact hv
  rw [hcoord, hE, hβ, zero_smul, add_zero, map_add_eq,
    CFSG.LargeExtraspecial.OrthoF2.map_smul_zmod2, ha, mul_zero, zero_add, q_vec hb,
    polar_smul_left, polar_comm, hbv a hab, smul_zero, add_zero]

end Sec3Coord

namespace Sec38Hyp

open CFSG.LargeExtraspecial.S2 (perp mem_perp)
open CFSG.GroupTheory.WeirSylow (IsPlusType)

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem not_isPlusType_W' : ¬ IsPlusType (H.xsub.q.comp (H.xsub.clSub Q).subtype) := by
  intro hplus
  have : Finite (H.xsub.clSub Q ≃ₗ[ZMod 2] H.xsub.clSub Q) :=
    Finite.of_injective (fun e : H.xsub.clSub Q ≃ₗ[ZMod 2] H.xsub.clSub Q =>
      (e : H.xsub.clSub Q → H.xsub.clSub Q)) DFunLike.coe_injective
  have hdim : finrank (ZMod 2) (H.xsub.clSub Q) = 2 * (2 + 1) := H.finrank_W'
  have : Nontrivial (H.xsub.clSub Q) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [H.finrank_W']; norm_num)
  have hprod : ∏ i ∈ Finset.Icc 1 2, (((Nat.card (ZMod 2) : ℤ) ^ 2) ^ i - 1) = 45 := by
    rw [Nat.card_zmod]
    decide
  have h := CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type (K := ZMod 2)
    H.W'_nondegenerate hdim (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  rw [hprod, Nat.card_zmod] at h
  have h1 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (H.xsub.q.comp (H.xsub.clSub Q).subtype)) : ℤ) = 40320 := by rw [h]; norm_num
  have hidx := relIndex_omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate
  have hmul := Subgroup.relIndex_mul_card
    (omegaGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype) H.W'_nondegenerate)
    (TauCeti.QuadraticMap.orthogonalGroup (H.xsub.q.comp (H.xsub.clSub Q).subtype))
  rw [hidx, inf_of_le_left (omegaGroup_le _ _)] at hmul
  have hle := Subgroup.card_le_of_le H.range_resB₀.le
  rw [H.card_range_resB₀] at hle
  omega

variable {z₂ : G}

theorem exists_frame (hZQ : Zs ≤ Q) (hz₂ : z₂ ∈ Zs) (hz₂z : z₂ ∉ zpowers z) :
    ∃ b : Fin 6 → H.xsub.Qt, Sec3Coord.IsFrame H.xsub.q b ∧
      (∀ i, polar H.xsub.q (H.xsub.cl z₂) (b i) = 0) ∧
      (∀ v, polar H.xsub.q (H.xsub.cl z₂) v = 0 →
        H.xsub.q v = Sec3Coord.qplus (Sec3Coord.coord H.xsub.q b v)) ∧
      b 0 ∈ H.xsub.clSub Q₀ ∧ b 1 ∈ H.xsub.clSub Q₀ ∧
      H.ρG ⟨x, H.x_mem_N⟩ (b 0) = b 1 ∧ H.ρG ⟨x, H.x_mem_N⟩ (b 1) = b 0 + b 1 ∧
      ∀ i : Fin 6, 2 ≤ i.val → b i ∈ H.xsub.clSub Q := by
  have hq := H.xsub.q_nondegenerate
  set a := H.xsub.cl z₂ with ha
  have ha0 : a ≠ 0 := H.cl_ne_zero hZQ hz₂ hz₂z
  have hqa : H.xsub.q a = 0 := H.q_cl_eq_zero hZQ hz₂
  have haW' : a ∈ H.xsub.clSub Q := H.xsub.cl_mem_clSub (hZQ hz₂) (H.Q_le (hZQ hz₂))
  have hW'perp : H.xsub.clSub Q ≤ perp H.xsub.q (H.xsub.clSub Q₀) := fun v hv =>
    mem_perp.mpr fun u hu => H.polar_W₀_W' hu hv
  have hperp : perp H.xsub.q (H.xsub.clSub Q₀) = H.xsub.clSub Q := by
    refine (Submodule.eq_of_le_of_finrank_eq hW'perp ?_).symm
    rw [H.finrank_W']
    change 6 = finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (polarBilin H.xsub.q)
      (H.xsub.clSub Q₀))
    rw [LinearMap.BilinForm.finrank_orthogonal hq, H.finrank_Qt, H.finrank_W₀]
  have hW₀ : H.xsub.clSub Q₀ ⊓ perp H.xsub.q (H.xsub.clSub Q₀) = ⊥ := by
    rw [hperp]
    exact H.W₀_inf_W'
  have haP : a ∈ perp H.xsub.q (H.xsub.clSub Q₀) := hperp ▸ haW'
  obtain ⟨a₁, ha₁P, hqa₁, haa₁⟩ :=
    CFSG.LargeExtraspecial.S2.exists_hyperbolic_partner hq hW₀ haP ha0 hqa
  set W₄ := perp H.xsub.q (H.xsub.clSub Q₀ ⊔ Submodule.span (ZMod 2) {a, a₁}) with hW₄
  have hF4 := CFSG.LargeExtraspecial.S2.sup_span_pair_inf_perp_eq_bot hW₀ haP ha₁P haa₁
  have hdim4 : finrank (ZMod 2) W₄ = 4 := by
    have h : finrank (ZMod 2) W₄ + 2 = finrank (ZMod 2) (perp H.xsub.q (H.xsub.clSub Q₀)) :=
      CFSG.LargeExtraspecial.S2.finrank_perp_sup_span_pair hq hW₀ haP ha₁P haa₁
    rw [hperp, H.finrank_W'] at h
    omega
  have hW₄W' : W₄ ≤ H.xsub.clSub Q := hperp ▸ CFSG.LargeExtraspecial.S2.perp_sup_span_pair_le
  have hW₄nd : (H.xsub.q.comp W₄.subtype).polarBilin.Nondegenerate :=
    polarBilin_restrict_nondegenerate hq (CFSG.LargeExtraspecial.S2.sup_perp_eq_top hF4)
      (fun v hv w hw => (mem_perp.mp hw) v hv)
  have hW₄a : ∀ w ∈ W₄, polar H.xsub.q a w = 0 := fun w hw =>
    (mem_perp.mp hw) a (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hW₄a₁ : ∀ w ∈ W₄, polar H.xsub.q a₁ w = 0 := fun w hw =>
    (mem_perp.mp hw) a₁ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hW₄W₀ : ∀ w ∈ W₄, ∀ u ∈ H.xsub.clSub Q₀, polar H.xsub.q u w = 0 := fun w hw u hu =>
    (mem_perp.mp hw) u (Submodule.mem_sup_left hu)
  have hW₄np : ¬ IsPlusType (H.xsub.q.comp W₄.subtype) := by
    rintro ⟨T, hT, hTq⟩
    apply H.not_isPlusType_W'
    set T' : Submodule (ZMod 2) H.xsub.Qt := T.map W₄.subtype with hT'
    have hT'W₄ : T' ≤ W₄ := by
      rintro _ ⟨t, -, rfl⟩
      exact t.2
    have hT'fin : finrank (ZMod 2) T' = 2 := by
      rw [hT', Submodule.finrank_map_subtype_eq]
      omega
    have hinf : T' ⊓ (ZMod 2) ∙ a = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hvT, hva⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hva
      have h1 := hW₄a₁ _ (hT'W₄ hvT)
      rw [polar_smul_right, polar_comm, haa₁, smul_eq_mul, mul_one] at h1
      rw [h1, zero_smul]
      exact Submodule.zero_mem _
    have hfin3 : finrank (ZMod 2) ↥(T' ⊔ (ZMod 2) ∙ a) = 3 := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq T' ((ZMod 2) ∙ a)
      rw [hinf, finrank_bot, add_zero, hT'fin, finrank_span_singleton ha0] at h
      omega
    have hle : T' ⊔ (ZMod 2) ∙ a ≤ H.xsub.clSub Q :=
      sup_le (hT'W₄.trans hW₄W') ((Submodule.span_singleton_le_iff_mem _ _).mpr haW')
    refine ⟨(T' ⊔ (ZMod 2) ∙ a).comap (H.xsub.clSub Q).subtype, ?_, ?_⟩
    · rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq, hfin3, H.finrank_W']
    · intro v hv
      have hv' : (v : H.xsub.Qt) ∈ T' ⊔ (ZMod 2) ∙ a := hv
      obtain ⟨t, ht, s, hs, hts⟩ := Submodule.mem_sup.mp hv'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
      obtain ⟨t₀, ht₀, rfl⟩ := ht
      change H.xsub.q (v : H.xsub.Qt) = 0
      have h1 : H.xsub.q (t₀ : H.xsub.Qt) = 0 := hTq t₀ ht₀
      have h2 : polar H.xsub.q (t₀ : H.xsub.Qt) (c • a) = 0 := by
        rw [polar_smul_right, polar_comm, hW₄a _ t₀.2, smul_zero]
      rw [← hts, Submodule.subtype_apply, map_add_eq, h1, h2,
        CFSG.LargeExtraspecial.OrthoF2.map_smul_zmod2, hqa, mul_zero, zero_add, add_zero]
  obtain ⟨e₄⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType hW₄nd (n := 2)
    (by norm_num) (by rw [hdim4]) hW₄np (b := (1 : ZMod 2)) (c := 1) (by decide)
  set Qm := CFSG.LieType.Universal.Spin.quadMinus 2 (ZMod 2) 1 1 with hQm
  set f : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) → H.xsub.Qt :=
    fun k => ((e₄.symm (Pi.single k 1) : W₄) : H.xsub.Qt) with hf
  have hfW₄ : ∀ k, f k ∈ W₄ := fun k => (e₄.symm _).2
  have hqe : ∀ u, H.xsub.q ((e₄.symm u : W₄) : H.xsub.Qt) = Qm u := fun u => e₄.symm.map_app u
  have hpe : ∀ u v, polar H.xsub.q ((e₄.symm u : W₄) : H.xsub.Qt) ((e₄.symm v : W₄) : H.xsub.Qt) =
      polar Qm u v := by
    intro u v
    simp only [polar]
    rw [← Submodule.coe_add, ← map_add, hqe, hqe, hqe]
  have k0 : Fin (2 - 1) := ⟨0, by norm_num⟩
  have hf01 : polar H.xsub.q (f (.inl k0)) (f (.inr (.inl k0))) = 1 := by
    rw [hf, hpe, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl]
    simp
  have hf02 : polar H.xsub.q (f (.inl k0)) (f (.inr (.inr 0))) = 0 := by
    rw [hf, hpe, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero]
    simp
  have hf03 : polar H.xsub.q (f (.inl k0)) (f (.inr (.inr 1))) = 0 := by
    rw [hf, hpe, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one]
    simp
  have hf12 : polar H.xsub.q (f (.inr (.inl k0))) (f (.inr (.inr 0))) = 0 := by
    rw [hf, hpe, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_zero]
    simp
  have hf13 : polar H.xsub.q (f (.inr (.inl k0))) (f (.inr (.inr 1))) = 0 := by
    rw [hf, hpe, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one]
    simp
  have hf23 : polar H.xsub.q (f (.inr (.inr 0))) (f (.inr (.inr 1))) = 1 := by
    rw [hf, hpe, CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inr_one]
    simp
  have hqf0 : H.xsub.q (f (.inl k0)) = 0 := by
    rw [hf, hqe, CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp
  have hqf1 : H.xsub.q (f (.inr (.inl k0))) = 0 := by
    rw [hf, hqe, CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp
  have hqf2 : H.xsub.q (f (.inr (.inr 0))) = 1 := by
    rw [hf, hqe, CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp
  have hqf3 : H.xsub.q (f (.inr (.inr 1))) = 1 := by
    rw [hf, hqe, CFSG.LieType.Universal.Spin.quadMinus_apply]
    simp
  obtain ⟨a₀, ha₀, hne⟩ := H.ρx_W₀
  set ρx := H.ρG ⟨x, H.x_mem_N⟩ with hρx
  set w := H.xsub.cl a₀ with hw
  have hρO : ρx ∈ TauCeti.QuadraticMap.orthogonalGroup H.xsub.q := (H.xsub.ρ ⟨x, H.x_mem_N⟩).2
  have hρW₀ : ∀ v ∈ H.xsub.clSub Q₀, ρx v ∈ H.xsub.clSub Q₀ := by
    intro v hv
    rw [← H.mem_glStab.mp (H.ρG_mem_glStab (n := ⟨x, H.x_mem_N⟩) H.q0.x_Q₀)]
    exact Submodule.mem_map_of_mem hv
  have hwW₀ : w ∈ H.xsub.clSub Q₀ := H.xsub.cl_mem_clSub ha₀ (H.Q₀_le ha₀)
  have huW₀ : ρx w ∈ H.xsub.clSub Q₀ := hρW₀ w hwW₀
  have hu'W₀ : ρx (ρx w) ∈ H.xsub.clSub Q₀ := hρW₀ _ huW₀
  have hq1 : ∀ v ∈ H.xsub.clSub Q₀, v ≠ 0 → H.xsub.q v = 1 := fun v hv hv0 =>
    CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_one_of_ne_zero fun h => hv0 (H.W₀_aniso hv h)
  have hw0 : w ≠ 0 := by
    intro h
    apply hne
    rw [h, map_zero]
  have hqw : H.xsub.q w = 1 := hq1 w hwW₀ hw0
  have hqu : H.xsub.q (ρx w) = 1 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hρO, hqw]
  have hqu' : H.xsub.q (ρx (ρx w)) = 1 := by
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hρO, hqu]
  have hwu : polar H.xsub.q w (ρx w) = 1 := by
    have hs0 : w + ρx w ≠ 0 := by
      intro h
      apply hne
      have h' := eq_neg_of_add_eq_zero_right h
      rwa [ZModModule.neg_eq_self] at h'
    have h1 := hq1 _ (Submodule.add_mem _ hwW₀ huW₀) hs0
    rw [map_add_eq, hqw, hqu, show (1 : ZMod 2) + 1 = 0 by decide, zero_add] at h1
    exact h1
  have hρ3 : ρx (ρx (ρx w)) = w := by
    have h := H.ρx_pow_three
    rw [← hρx] at h
    have e : (ρx ^ 3) w = ρx (ρx (ρx w)) := by
      rw [pow_succ, pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [← e, h]
    rfl
  have huu' : polar H.xsub.q (ρx w) (ρx (ρx w)) = 1 := by
    rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hρO, hwu]
  have hwu' : polar H.xsub.q w (ρx (ρx w)) = 1 := by
    have h : polar H.xsub.q (ρx (ρx w)) (ρx (ρx (ρx w))) = 1 := by
      rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hρO, huu']
    rw [hρ3] at h
    rw [polar_comm]
    exact h
  have hρu : ρx (ρx w) = w + ρx w := by
    have hs : w + ρx w + ρx (ρx w) ∈ H.xsub.clSub Q₀ :=
      Submodule.add_mem _ (Submodule.add_mem _ hwW₀ huW₀) hu'W₀
    have hqs : H.xsub.q (w + ρx w + ρx (ρx w)) = 0 := by
      rw [map_add_eq, map_add_eq, polar_add_left, hqw, hqu, hqu', hwu, hwu', huu']
      decide
    have h0 := H.W₀_aniso hs hqs
    have h' := eq_neg_of_add_eq_zero_right h0
    rwa [ZModModule.neg_eq_self] at h'
  set b : Fin 6 → H.xsub.Qt := ![w, ρx w, f (.inl k0), f (.inr (.inl k0)), f (.inr (.inr 0)),
    f (.inr (.inr 1))] with hbdef
  have hwf : ∀ k, polar H.xsub.q w (f k) = 0 := fun k => hW₄W₀ _ (hfW₄ k) w hwW₀
  have huf : ∀ k, polar H.xsub.q (ρx w) (f k) = 0 := fun k => hW₄W₀ _ (hfW₄ k) _ huW₀
  have hfw : ∀ k, polar H.xsub.q (f k) w = 0 := fun k => by rw [polar_comm]; exact hwf k
  have hfu : ∀ k, polar H.xsub.q (f k) (ρx w) = 0 := fun k => by rw [polar_comm]; exact huf k
  have huw : polar H.xsub.q (ρx w) w = 1 := by rw [polar_comm]; exact hwu
  have hf10 : polar H.xsub.q (f (.inr (.inl k0))) (f (.inl k0)) = 1 := by
    rw [polar_comm]; exact hf01
  have hf20 : polar H.xsub.q (f (.inr (.inr 0))) (f (.inl k0)) = 0 := by
    rw [polar_comm]; exact hf02
  have hf30 : polar H.xsub.q (f (.inr (.inr 1))) (f (.inl k0)) = 0 := by
    rw [polar_comm]; exact hf03
  have hf21 : polar H.xsub.q (f (.inr (.inr 0))) (f (.inr (.inl k0))) = 0 := by
    rw [polar_comm]; exact hf12
  have hf31 : polar H.xsub.q (f (.inr (.inr 1))) (f (.inr (.inl k0))) = 0 := by
    rw [polar_comm]; exact hf13
  have hf32 : polar H.xsub.q (f (.inr (.inr 1))) (f (.inr (.inr 0))) = 1 := by
    rw [polar_comm]; exact hf23
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hb : Sec3Coord.IsFrame H.xsub.q b := by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hbdef, Sec3Coord.piF, h2, hwu, huw, hwf, huf, hfw, hfu, hf01,
          hf02, hf03, hf12, hf13, hf23, hf10, hf20, hf30, hf21, hf31, hf32]
    · intro i
      fin_cases i <;> simp [hbdef, hqw, hqu, hqf0, hqf1, hqf2, hqf3]
  have haw : polar H.xsub.q a w = 0 := by rw [polar_comm]; exact H.polar_W₀_W' hwW₀ haW'
  have hau : polar H.xsub.q a (ρx w) = 0 := by rw [polar_comm]; exact H.polar_W₀_W' huW₀ haW'
  have ha₁w : polar H.xsub.q a₁ w = 0 := by rw [polar_comm]; exact (mem_perp.mp ha₁P) w hwW₀
  have ha₁u : polar H.xsub.q a₁ (ρx w) = 0 := by
    rw [polar_comm]; exact (mem_perp.mp ha₁P) _ huW₀
  have hab : ∀ i, polar H.xsub.q a (b i) = 0 := by
    intro i
    fin_cases i <;> simp [hbdef, haw, hau, hW₄a _ (hfW₄ _)]
  have ha₁b : ∀ i, polar H.xsub.q a₁ (b i) = 0 := by
    intro i
    fin_cases i <;> simp [hbdef, ha₁w, ha₁u, hW₄a₁ _ (hfW₄ _)]
  refine ⟨b, hb, hab, fun v hv => Sec3Coord.map_eq_qplus hb H.finrank_Qt hqa haa₁ hab ha₁b hv,
    hwW₀, huW₀, rfl, hρu, ?_⟩
  intro i hi
  fin_cases i <;> simp at hi ⊢ <;> exact hW₄W' (hfW₄ _)

end Sec38Hyp

end CFSG.ComponentClassification.AS81

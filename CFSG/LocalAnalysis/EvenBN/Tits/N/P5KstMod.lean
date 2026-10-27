module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstSetup
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstComb

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N.P4 Equiv

variable {Γ : Type*} [Group Γ] [Finite Γ] {U K : Subgroup Γ} {x v t : Γ}

namespace KSetup

@[expose] noncomputable def eqv (h : KSetup U K x v t) : ↥(cls K t) ≃ Fin 6 := Finite.equivFinOfCardEq h.card_cls

@[expose] noncomputable def dd (h : KSetup U K x v t) (i : Fin 6) : Γ := ((h.eqv.symm i : ↥(cls K t)) : Γ)

theorem dd_mem_cls (h : KSetup U K x v t) (i : Fin 6) : h.dd i ∈ cls K t := (h.eqv.symm i).2

theorem dd_injective (h : KSetup U K x v t) : Function.Injective h.dd := fun i j hij =>
  h.eqv.symm.injective (Subtype.ext hij)

theorem exists_dd (h : KSetup U K x v t) {c : Γ} (hc : c ∈ cls K t) : ∃ i, h.dd i = c :=
  ⟨h.eqv ⟨c, hc⟩, by simp [dd]⟩

theorem t_mem_U0 : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)

theorem cls_le_U0 (h : KSetup U K x v t) {d : Γ} (hd : d ∈ cls K t) : d ∈ U ⊔ zpowers t := by
  obtain ⟨u, hu, rfl⟩ := h.cls_subset hd
  exact mul_mem t_mem_U0 (mem_sup_left hu)

theorem dd_mem_U0 (h : KSetup U K x v t) (i : Fin 6) : h.dd i ∈ U ⊔ zpowers t :=
  h.cls_le_U0 (h.dd_mem_cls i)

theorem U0_comm (h : KSetup U K x v t) {a b : Γ} (ha : a ∈ U ⊔ zpowers t) (hb : b ∈ U ⊔ zpowers t) :
    a * b = b * a :=
  h.U0_data.1.comm ha hb

theorem U0_sq (h : KSetup U K x v t) {a : Γ} (ha : a ∈ U ⊔ zpowers t) : a * a = 1 :=
  h.U0_data.1.mul_self_eq_one ha

theorem U_le_K (h : KSetup U K x v t) : U ≤ K :=
  (IsF20.U_le_Pgrp U x v).trans (le_sup_right.trans h.hCK)

theorem U0_le_K (h : KSetup U K x v t) : U ⊔ zpowers t ≤ K :=
  sup_le h.U_le_K (le_sup_left.trans h.hCK)

theorem dd_eqv (h : KSetup U K x v t) {c : Γ} (hc : c ∈ cls K t) : h.dd (h.eqv ⟨c, hc⟩) = c := by
  simp [dd]

theorem eqv_dd (h : KSetup U K x v t) (i : Fin 6) : h.eqv ⟨h.dd i, h.dd_mem_cls i⟩ = i := by
  simp [dd]

@[expose] noncomputable def permOf (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K) : Perm (Fin 6) where
  toFun i := h.eqv ⟨k * h.dd i * k⁻¹, h.conj_mem_cls hk (h.dd_mem_cls i)⟩
  invFun i := h.eqv ⟨k⁻¹ * h.dd i * k⁻¹⁻¹, h.conj_mem_cls (inv_mem hk) (h.dd_mem_cls i)⟩
  left_inv i := by
    have : k⁻¹ * (k * h.dd i * k⁻¹) * k⁻¹⁻¹ = h.dd i := by group
    simp only [dd_eqv, this]
    exact h.eqv_dd i
  right_inv i := by
    have : k * (k⁻¹ * h.dd i * k⁻¹⁻¹) * k⁻¹ = h.dd i := by group
    simp only [dd_eqv, this]
    exact h.eqv_dd i

theorem dd_permOf (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K) (i : Fin 6) :
    h.dd (h.permOf hk i) = k * h.dd i * k⁻¹ := by
  simp only [permOf, Equiv.coe_fn_mk]
  exact h.dd_eqv _

@[expose] noncomputable def rho (h : KSetup U K x v t) : ↥K →* Perm (Fin 6) where
  toFun k := h.permOf k.2
  map_one' := by
    refine Equiv.ext fun i => ?_
    apply h.dd_injective
    simp [dd_permOf]
  map_mul' k₁ k₂ := by
    refine Equiv.ext fun i => ?_
    apply h.dd_injective
    simp only [Perm.coe_mul, Function.comp_apply, dd_permOf, Subgroup.coe_mul, mul_inv_rev]
    group

theorem dd_rho (h : KSetup U K x v t) (k : ↥K) (i : Fin 6) :
    h.dd (h.rho k i) = (k : Γ) * h.dd i * (k : Γ)⁻¹ := h.dd_permOf k.2 i

theorem rho_eq_one_iff (h : KSetup U K x v t) (k : ↥K) :
    h.rho k = 1 ↔ (k : Γ) ∈ U ⊔ zpowers t := by
  constructor
  · intro hk
    refine h.kernel_cls k.2 fun d hd => ?_
    obtain ⟨i, rfl⟩ := h.exists_dd hd
    have := h.dd_rho k i
    rw [hk] at this
    simpa using this.symm
  · intro hk
    refine Equiv.ext fun i => ?_
    apply h.dd_injective
    rw [h.dd_rho]
    have hc := h.U0_comm hk (h.dd_mem_U0 i)
    simp [hc]

@[expose] noncomputable def base (h : KSetup U K x v t) : Fin 6 := h.eqv ⟨t, h.t_mem_cls⟩

theorem dd_base (h : KSetup U K x v t) : h.dd h.base = t := h.dd_eqv h.t_mem_cls

theorem rho_base (h : KSetup U K x v t) {g : Γ} (hg : g ∈ K) (hgt : g * t = t * g) :
    h.rho ⟨g, hg⟩ h.base = h.base := by
  apply h.dd_injective
  rw [h.dd_rho, h.dd_base]
  show g * t * g⁻¹ = t
  rw [hgt]
  group

theorem v_mem_K (h : KSetup U K x v t) : v ∈ K :=
  (le_sup_right.trans h.hCK) (mem_sup_right (mem_sup_right (mem_zpowers v)))

theorem card_range_rho (h : KSetup U K x v t) : Nat.card h.rho.range = 120 := by
  have hker : h.rho.ker = (U ⊔ zpowers t).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, h.rho_eq_one_iff, mem_subgroupOf]
  have h1 := Subgroup.card_ker_mul_card_range h.rho
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.U0_le_K).toEquiv, h.U0_data.2,
    h.card_K] at h1
  omega

theorem sixData (h : KSetup U K x v t) :
    SixData h.rho.range h.base (h.rho ⟨x, h.x_mem_K⟩) (h.rho ⟨v, h.v_mem_K⟩) := by
  refine ⟨Fintype.card_fin 6, h.card_range_rho, ?_, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    obtain ⟨k, hk, hkω⟩ := (h.dd_mem_cls ω : ∃ k ∈ K, h.dd ω = k * t * k⁻¹)
    refine ⟨h.rho ⟨k, hk⟩, ⟨_, rfl⟩, ?_⟩
    apply h.dd_injective
    rw [h.dd_rho, h.dd_base, hkω]
  · exact h.rho_base h.x_mem_K h.htx.symm
  · exact h.rho_base h.v_mem_K h.htv.symm
  · rw [← map_pow]
    have : (⟨x, h.x_mem_K⟩ : ↥K) ^ 5 = 1 := Subtype.ext (by simpa using h.hF.x5)
    rw [this, map_one]
  · intro ω hω hfix
    obtain ⟨k, hk, hkω⟩ := (h.dd_mem_cls ω : ∃ k ∈ K, h.dd ω = k * t * k⁻¹)
    obtain ⟨u, hu, hω'⟩ := h.cls_subset (h.dd_mem_cls ω)
    have h1 : x * h.dd ω * x⁻¹ = h.dd ω := by
      have := h.dd_rho ⟨x, h.x_mem_K⟩ ω
      rw [hfix] at this
      exact this.symm
    rw [hω'] at h1
    have h2 : x * (t * u) * x⁻¹ = t * (x * u * x⁻¹) := by
      have := h.htx
      calc x * (t * u) * x⁻¹ = (x * t) * u * x⁻¹ := by group
        _ = (t * x) * u * x⁻¹ := by rw [h.htx.symm]
        _ = t * (x * u * x⁻¹) := by group
    rw [h2] at h1
    have h3 : x * u * x⁻¹ = u := mul_left_cancel h1
    have h4 : u = 1 := h.hF.fpf u hu h3
    apply hω
    apply h.dd_injective
    rw [hω', h4, h.dd_base]
    simp
  · rw [← map_pow]
    have : (⟨v, h.v_mem_K⟩ : ↥K) ^ 4 = 1 := Subtype.ext (by simpa using h.hF.v4)
    rw [this, map_one]
  · intro hb
    rw [← map_pow] at hb
    have := (h.rho_eq_one_iff _).1 hb
    exact h.v_sq_not_mem (by simpa using this)
  · rcases h.hF.vx with hvx | hvx
    · left
      have : (⟨v, h.v_mem_K⟩ * ⟨x, h.x_mem_K⟩ * ⟨v, h.v_mem_K⟩⁻¹ : ↥K) = ⟨x, h.x_mem_K⟩ ^ 2 :=
        Subtype.ext (by simpa using hvx)
      rw [← map_inv, ← map_mul, ← map_mul, this, map_pow]
    · right
      have : (⟨v, h.v_mem_K⟩ * ⟨x, h.x_mem_K⟩ * ⟨v, h.v_mem_K⟩⁻¹ : ↥K) = ⟨x, h.x_mem_K⟩ ^ 3 :=
        Subtype.ext (by simpa using hvx)
      rw [← map_inv, ← map_mul, ← map_mul, this, map_pow]

@[expose, instance_reducible] noncomputable def commA (h : KSetup U K x v t) : CommGroup ↥(U ⊔ zpowers t) :=
  { (inferInstance : Group ↥(U ⊔ zpowers t)) with
    mul_comm := fun a b => Subtype.ext (h.U0_comm a.2 b.2) }

@[expose] noncomputable def ddA (h : KSetup U K x v t) (i : Fin 6) : ↥(U ⊔ zpowers t) :=
  ⟨h.dd i, h.dd_mem_U0 i⟩

theorem ddA_sq (h : KSetup U K x v t) (i : Fin 6) : h.ddA i ^ 2 = 1 := by
  apply Subtype.ext
  show h.dd i ^ 2 = 1
  rw [pow_two]
  exact h.U0_sq (h.dd_mem_U0 i)

@[expose] noncomputable def ev (h : KSetup U K x v t) (f : Fin 6 → ZMod 2) : ↥(U ⊔ zpowers t) :=
  letI := h.commA
  ∏ i, h.ddA i ^ (f i).val

theorem ev_add (h : KSetup U K x v t) (f g : Fin 6 → ZMod 2) :
    h.ev (f + g) = h.ev f * h.ev g := by
  letI := h.commA
  have key : ∀ i, h.ddA i ^ ((f + g) i).val = h.ddA i ^ (f i).val * h.ddA i ^ (g i).val := by
    intro i
    rw [Pi.add_apply, ZMod.val_add, ← pow_add, pow_eq_pow_mod ((f i).val + (g i).val) (h.ddA_sq i)]
  calc h.ev (f + g) = ∏ i, (h.ddA i ^ (f i).val * h.ddA i ^ (g i).val) :=
        Finset.prod_congr rfl (fun i _ => key i)
    _ = (∏ i, h.ddA i ^ (f i).val) * ∏ i, h.ddA i ^ (g i).val := Finset.prod_mul_distrib

theorem ev_zero (h : KSetup U K x v t) : h.ev 0 = 1 := by
  letI := h.commA
  unfold ev
  exact Finset.prod_eq_one fun i _ => by simp <;> rfl

theorem ev_single (h : KSetup U K x v t) (j : Fin 6) : h.ev (Pi.single j 1) = h.ddA j := by
  letI := h.commA
  unfold ev
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb] <;> rfl
  · intro hj
    exact absurd (Finset.mem_univ j) hj

@[expose] noncomputable def cA (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K) : ↥(U ⊔ zpowers t) →* ↥(U ⊔ zpowers t) where
  toFun a := ⟨k * a * k⁻¹, (mem_normalizer_iff.1 (h.hKN hk) a).1 a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem cA_ddA (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K) (i : Fin 6) :
    h.cA hk (h.ddA i) = h.ddA (h.permOf hk i) := by
  apply Subtype.ext
  show k * h.dd i * k⁻¹ = h.dd (h.permOf hk i)
  rw [h.dd_permOf]

theorem cA_ev (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K) (f : Fin 6 → ZMod 2) :
    h.cA hk (h.ev f) = h.ev (fun j => f ((h.permOf hk).symm j)) := by
  letI := h.commA
  unfold ev
  rw [map_prod]
  refine Fintype.prod_equiv (h.permOf hk) _ _ fun i => ?_
  rw [map_pow, h.cA_ddA hk i]
  simp

@[expose] def tA (h : KSetup U K x v t) : ↥(U ⊔ zpowers t) := ⟨t, t_mem_U0⟩

theorem t_mul_dd_mem_U (h : KSetup U K x v t) (i : Fin 6) : t * h.dd i ∈ U := by
  obtain ⟨u, hu, hd⟩ := h.cls_subset (h.dd_mem_cls i)
  rw [hd, ← mul_assoc, h.htt, one_mul]
  exact hu

@[expose] noncomputable def uA (h : KSetup U K x v t) (i : Fin 6) : ↥(U ⊔ zpowers t) :=
  ⟨t * h.dd i, mul_mem t_mem_U0 (h.dd_mem_U0 i)⟩

theorem ddA_eq (h : KSetup U K x v t) (i : Fin 6) : h.ddA i = h.tA * h.uA i := by
  apply Subtype.ext
  show h.dd i = t * (t * h.dd i)
  rw [← mul_assoc, h.htt, one_mul]

theorem ev_mem_U_iff (h : KSetup U K x v t) (f : Fin 6 → ZMod 2) :
    ((h.ev f : ↥(U ⊔ zpowers t)) : Γ) ∈ U ↔ ∑ i, f i = 0 := by
  letI := h.commA
  have hev : h.ev f = h.tA ^ (∑ i, (f i).val) * ∏ i, h.uA i ^ (f i).val := by
    unfold ev
    calc ∏ i, h.ddA i ^ (f i).val = ∏ i, (h.tA ^ (f i).val * h.uA i ^ (f i).val) :=
          Finset.prod_congr rfl (fun i _ => (congrArg (· ^ (f i).val) (h.ddA_eq i)).trans
            (mul_pow _ _ _))
      _ = (∏ i, h.tA ^ (f i).val) * ∏ i, h.uA i ^ (f i).val := Finset.prod_mul_distrib
      _ = h.tA ^ (∑ i, (f i).val) * ∏ i, h.uA i ^ (f i).val :=
          congrArg (fun a => a * ∏ i, h.uA i ^ (f i).val)
            (Finset.prod_pow_eq_pow_sum Finset.univ (fun i => (f i).val) h.tA)
  have hw : ((∏ i, h.uA i ^ (f i).val : ↥(U ⊔ zpowers t)) : Γ) ∈ U := by
    refine Finset.prod_induction (fun i => h.uA i ^ (f i).val) (fun a => (a : Γ) ∈ U) ?_ ?_ ?_
    · intro a b ha hb
      exact mul_mem ha hb
    · exact one_mem U
    · intro i _
      exact pow_mem (h.t_mul_dd_mem_U i) _
  have hcoe : ((h.ev f : ↥(U ⊔ zpowers t)) : Γ) =
      t ^ (∑ i, (f i).val) * ((∏ i, h.uA i ^ (f i).val : ↥(U ⊔ zpowers t)) : Γ) := by
    rw [hev]
    rfl
  rw [hcoe, mul_mem_cancel_right hw]
  have hsum : (∑ i, f i) = (((∑ i, (f i).val : ℕ)) : ZMod 2) := by
    push_cast
    simp [ZMod.natCast_zmod_val]
  rw [hsum, ZMod.natCast_eq_zero_iff]
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact h.htt
  rcases Nat.even_or_odd' (∑ i, (f i).val) with ⟨m, hm | hm⟩
  · rw [hm, pow_mul, ht2, one_pow]
    simp only [one_mem, true_iff]
    exact ⟨m, by ring⟩
  · rw [hm, pow_succ, pow_mul, ht2, one_pow, one_mul]
    simp only [h.htnU, false_iff]
    intro hd
    obtain ⟨c, hc⟩ := hd
    omega

theorem ev_mul_self (h : KSetup U K x v t) (f : Fin 6 → ZMod 2) : h.ev f * h.ev f = 1 := by
  rw [← h.ev_add]
  have h2 : f + f = 0 := by
    funext i
    have : ∀ a : ZMod 2, a + a = 0 := by decide
    exact this (f i)
  rw [h2, h.ev_zero]

theorem ev_surj (h : KSetup U K x v t) {a : Γ} (ha : a ∈ U ⊔ zpowers t) :
    ∃ f, ((h.ev f : ↥(U ⊔ zpowers t)) : Γ) = a := by
  let Rg : Subgroup Γ :=
    { carrier := {c | ∃ f, ((h.ev f : ↥(U ⊔ zpowers t)) : Γ) = c}
      mul_mem' := by
        rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
        exact ⟨f + g, by rw [h.ev_add]; rfl⟩
      one_mem' := ⟨0, by rw [h.ev_zero]; rfl⟩
      inv_mem' := by
        rintro _ ⟨f, rfl⟩
        refine ⟨f, ?_⟩
        have h2 : ((h.ev f : ↥(U ⊔ zpowers t)) : Γ) * ((h.ev f : ↥(U ⊔ zpowers t)) : Γ) = 1 :=
          congrArg Subtype.val (h.ev_mul_self f)
        exact (inv_eq_of_mul_eq_one_right h2).symm }
  have hcls : Subgroup.closure (cls K t) ≤ Rg := by
    rw [Subgroup.closure_le]
    intro d hd
    obtain ⟨i, rfl⟩ := h.exists_dd hd
    exact ⟨Pi.single i 1, by rw [h.ev_single]; rfl⟩
  rw [← h.closure_cls] at ha
  exact hcls ha

theorem ev_ones (h : KSetup U K x v t) : h.ev 1 = 1 := by
  have hx : x ∈ K := h.x_mem_K
  have h1 : h.cA hx (h.ev 1) = h.ev 1 := h.cA_ev hx 1
  have h2 : ((h.ev 1 : ↥(U ⊔ zpowers t)) : Γ) ∈ U := by
    rw [h.ev_mem_U_iff]
    decide
  have h3 : x * ((h.ev 1 : ↥(U ⊔ zpowers t)) : Γ) * x⁻¹ = ((h.ev 1 : ↥(U ⊔ zpowers t)) : Γ) :=
    congrArg Subtype.val h1
  exact Subtype.ext (h.hF.fpf _ h2 h3)

@[expose] noncomputable def evHom (h : KSetup U K x v t) :
    (Fin 6 → ZMod 2) →+ Additive ↥(U ⊔ zpowers t) :=
  AddMonoidHom.mk' (fun f => Additive.ofMul (h.ev f)) (fun f g => by
    rw [h.ev_add]
    rfl)

theorem evHom_surjective (h : KSetup U K x v t) : Function.Surjective h.evHom := by
  intro y
  obtain ⟨a, rfl⟩ : ∃ a : ↥(U ⊔ zpowers t), Additive.ofMul a = y := ⟨Additive.toMul y, rfl⟩
  obtain ⟨f, hf⟩ := h.ev_surj a.2
  exact ⟨f, congrArg Additive.ofMul (Subtype.ext hf)⟩

theorem card_ker_evHom (h : KSetup U K x v t) : Nat.card h.evHom.ker = 2 := by
  have h1 := AddSubgroup.card_ker_mul_card_of_surjective h.evHom_surjective
  have h2 : Nat.card (Additive ↥(U ⊔ zpowers t)) = 32 := by
    rw [Nat.card_congr (Additive.toMul : Additive ↥(U ⊔ zpowers t) ≃ ↥(U ⊔ zpowers t))]
    exact h.U0_data.2
  have h3 : Nat.card (Fin 6 → ZMod 2) = 64 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_fun]
  rw [h2, h3] at h1
  omega

theorem ev_eq_one_iff (h : KSetup U K x v t) (f : Fin 6 → ZMod 2) :
    h.ev f = 1 ↔ f = 0 ∨ f = 1 := by
  constructor
  · intro hf
    have hmem : f ∈ h.evHom.ker := by
      rw [AddMonoidHom.mem_ker]
      exact congrArg Additive.ofMul hf
    have hones : (1 : Fin 6 → ZMod 2) ∈ h.evHom.ker := by
      rw [AddMonoidHom.mem_ker]
      exact congrArg Additive.ofMul h.ev_ones
    have hne : (1 : Fin 6 → ZMod 2) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    have hcard := h.card_ker_evHom
    rw [Nat.card_eq_two_iff' (⟨0, zero_mem _⟩ : h.evHom.ker)] at hcard
    obtain ⟨y, hy, huniq⟩ := hcard
    by_cases hf0 : f = 0
    · exact Or.inl hf0
    · right
      have e1 : (⟨f, hmem⟩ : h.evHom.ker) = y := huniq _ (by simpa [Subtype.ext_iff] using hf0)
      have e2 : (⟨1, hones⟩ : h.evHom.ker) = y := huniq _ (by simpa [Subtype.ext_iff] using hne)
      exact congrArg Subtype.val (e1.trans e2.symm)
  · rintro (rfl | rfl)
    · exact h.ev_zero
    · exact h.ev_ones

theorem ev_eq_iff (h : KSetup U K x v t) (f g : Fin 6 → ZMod 2) :
    h.ev f = h.ev g ↔ g = f ∨ g = f + 1 := by
  have key : h.ev g = h.ev f * h.ev (g - f) := by
    rw [← h.ev_add]
    congr 1
    funext i
    exact (add_sub_cancel (f i) (g i)).symm
  have hsub : ∀ a b : ZMod 2, (a - b = 0 ↔ a = b) := fun a b => sub_eq_zero
  constructor
  · intro hfg
    have h1 : h.ev (g - f) = 1 := by
      rw [key] at hfg
      exact (mul_eq_left.1 hfg.symm)
    rcases (h.ev_eq_one_iff _).1 h1 with h2 | h2
    · left
      exact sub_eq_zero.1 h2
    · right
      exact sub_eq_iff_eq_add'.1 h2
  · rintro (rfl | rfl)
    · rfl
    · rw [h.ev_add, h.ev_ones, mul_one]

@[expose] noncomputable def evG (h : KSetup U K x v t) (f : Fin 6 → ZMod 2) : Γ :=
  ((h.ev f : ↥(U ⊔ zpowers t)) : Γ)

theorem evG_mem (h : KSetup U K x v t) (f : Fin 6 → ZMod 2) : h.evG f ∈ U ⊔ zpowers t :=
  (h.ev f).2

theorem evG_add (h : KSetup U K x v t) (f g : Fin 6 → ZMod 2) :
    h.evG (f + g) = h.evG f * h.evG g := by
  unfold evG
  rw [h.ev_add]
  rfl

theorem evG_mem_U_iff (h : KSetup U K x v t) (f : Fin 6 → ZMod 2) :
    h.evG f ∈ U ↔ ∑ i, f i = 0 := h.ev_mem_U_iff f

theorem evG_surj (h : KSetup U K x v t) {a : Γ} (ha : a ∈ U ⊔ zpowers t) : ∃ f, h.evG f = a :=
  h.ev_surj ha

theorem evG_eq_iff (h : KSetup U K x v t) (f g : Fin 6 → ZMod 2) :
    h.evG f = h.evG g ↔ g = f ∨ g = f + 1 := by
  rw [← h.ev_eq_iff]
  exact ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩

theorem conj_evG (h : KSetup U K x v t) {k : Γ} (hk : k ∈ K) (f : Fin 6 → ZMod 2) :
    k * h.evG f * k⁻¹ = h.evG (fun j => f ((h.permOf hk).symm j)) :=
  congrArg Subtype.val (h.cA_ev hk f)

theorem fix_iff (h : KSetup U K x v t) {y : Γ} (hy : y ∈ K) (f : Fin 6 → ZMod 2) :
    y * h.evG f * y⁻¹ = h.evG f ↔ f ∈ FixVec (h.permOf hy) := by
  rw [h.conj_evG hy, eq_comm, h.evG_eq_iff]
  unfold FixVec
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem FixVec_add_one {σ : Perm (Fin 6)} {f : Fin 6 → ZMod 2} (hf : f ∈ FixVec σ) :
    f + 1 ∈ FixVec σ := by
  unfold FixVec at hf ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  rcases hf with hf | hf
  · left
    funext i
    have := congrFun hf i
    simp only [Pi.add_apply, Pi.one_apply] at this ⊢
    rw [this]
  · right
    funext i
    have := congrFun hf i
    simp only [Pi.add_apply, Pi.one_apply] at this ⊢
    rw [this]

theorem EvenVec_add_one {f : Fin 6 → ZMod 2} (hf : f ∈ EvenVec) : f + 1 ∈ EvenVec := by
  unfold EvenVec at hf ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, Finset.sum_add_distrib] at hf ⊢
  rw [hf]
  decide

theorem card_image_evG [DecidableEq Γ] (h : KSetup U K x v t) (S : Finset (Fin 6 → ZMod 2))
    (hS : ∀ f ∈ S, f + 1 ∈ S) : (S.image h.evG).card * 2 = S.card := by
  rw [Finset.card_eq_sum_card_image h.evG S]
  rw [Finset.sum_const_nat (m := 2) ?_]
  intro a ha
  obtain ⟨f₀, hf₀, rfl⟩ := Finset.mem_image.1 ha
  have hne : f₀ ≠ f₀ + 1 := by
    intro heq
    have := congrFun heq 0
    simp at this
  have hfib : S.filter (fun f => h.evG f = h.evG f₀) = {f₀, f₀ + 1} := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hf⟩
      exact (h.evG_eq_iff f₀ f).1 hf.symm
    · rintro (rfl | rfl)
      · exact ⟨hf₀, rfl⟩
      · exact ⟨hS _ hf₀, ((h.evG_eq_iff f₀ _).2 (Or.inr rfl)).symm⟩
  rw [hfib, Finset.card_pair hne]

theorem card_of_image_set [DecidableEq Γ] (h : KSetup U K x v t) (C : Subgroup Γ) (S : Finset (Fin 6 → ZMod 2))
    (hS : ∀ f ∈ S, f + 1 ∈ S) (hC : (C : Set Γ) = ↑(S.image h.evG)) :
    Nat.card C * 2 = S.card := by
  have h1 : Nat.card C = (S.image h.evG).card := by
    rw [← Set.ncard_coe_finset, ← hC]
    exact Nat.card_coe_set_eq _
  rw [h1]
  exact h.card_image_evG S hS

theorem centralizer_U0_eq [DecidableEq Γ] (h : KSetup U K x v t) {y : Γ} (hy : y ∈ K) :
    (((U ⊔ zpowers t) ⊓ centralizer ({y} : Set Γ) : Subgroup Γ) : Set Γ) =
      ↑((FixVec (h.permOf hy)).image h.evG) := by
  ext a
  simp only [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff, Finset.coe_image,
    Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨ha, hac⟩
    obtain ⟨f, rfl⟩ := h.evG_surj ha
    refine ⟨f, (h.fix_iff hy f).1 ?_, rfl⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact hac.symm
  · rintro ⟨f, hf, rfl⟩
    refine ⟨h.evG_mem f, ?_⟩
    have := (h.fix_iff hy f).2 hf
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm

theorem centralizer_U_eq [DecidableEq Γ] (h : KSetup U K x v t) {y : Γ} (hy : y ∈ K) :
    ((U ⊓ centralizer ({y} : Set Γ) : Subgroup Γ) : Set Γ) =
      ↑((FixVec (h.permOf hy) ∩ EvenVec).image h.evG) := by
  ext a
  simp only [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff, Finset.coe_image,
    Set.mem_image, Finset.mem_coe, Finset.mem_inter]
  constructor
  · rintro ⟨ha, hac⟩
    obtain ⟨f, rfl⟩ := h.evG_surj (mem_sup_left ha)
    refine ⟨f, ⟨(h.fix_iff hy f).1 ?_, ?_⟩, rfl⟩
    · rw [mul_inv_eq_iff_eq_mul]
      exact hac.symm
    · unfold EvenVec
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h.evG_mem_U_iff f).1 ha
  · rintro ⟨f, ⟨hf, hev⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · unfold EvenVec at hev
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hev
      exact (h.evG_mem_U_iff f).2 hev
    · have := (h.fix_iff hy f).2 hf
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm

theorem centralizer_U0_inter_eq [DecidableEq Γ] (h : KSetup U K x v t) {y y' : Γ} (hy : y ∈ K)
    (hy' : y' ∈ K) :
    (((U ⊔ zpowers t) ⊓ centralizer ({y} : Set Γ) ⊓ centralizer ({y'} : Set Γ) : Subgroup Γ) :
        Set Γ) = ↑((FixVec (h.permOf hy) ∩ FixVec (h.permOf hy')).image h.evG) := by
  ext a
  simp only [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff, Finset.coe_image,
    Set.mem_image, Finset.mem_coe, Finset.mem_inter]
  constructor
  · rintro ⟨⟨ha, hac⟩, hac'⟩
    obtain ⟨f, rfl⟩ := h.evG_surj ha
    refine ⟨f, ⟨(h.fix_iff hy f).1 ?_, (h.fix_iff hy' f).1 ?_⟩, rfl⟩
    · rw [mul_inv_eq_iff_eq_mul]
      exact hac.symm
    · rw [mul_inv_eq_iff_eq_mul]
      exact hac'.symm
  · rintro ⟨f, ⟨hf, hf'⟩, rfl⟩
    refine ⟨⟨h.evG_mem f, ?_⟩, ?_⟩
    · have := (h.fix_iff hy f).2 hf
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · have := (h.fix_iff hy' f).2 hf'
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm

theorem card_centralizer_U0 [DecidableEq Γ] (h : KSetup U K x v t) {y : Γ} (hy : y ∈ K)
    (hσ : h.permOf hy * h.permOf hy = 1)
    (hf : fixCount (h.permOf hy) = 0 ∨ fixCount (h.permOf hy) = 2) :
    Nat.card ↥((U ⊔ zpowers t) ⊓ centralizer ({y} : Set Γ)) = 8 := by
  have h1 := h.card_of_image_set _ _ (fun f hf => FixVec_add_one hf) (h.centralizer_U0_eq hy)
  have h2 := card_fixVec (h.permOf hy) hσ hf
  omega

theorem card_centralizer_U [DecidableEq Γ] (h : KSetup U K x v t) {y : Γ} (hy : y ∈ K)
    (hσ : h.permOf hy * h.permOf hy = 1)
    (hf : fixCount (h.permOf hy) = 0 ∨ fixCount (h.permOf hy) = 2) :
    Nat.card ↥(U ⊓ centralizer ({y} : Set Γ)) = 4 := by
  have h1 := h.card_of_image_set _ _
    (fun f hf => by
      rw [Finset.mem_inter] at hf ⊢
      exact ⟨FixVec_add_one hf.1, EvenVec_add_one hf.2⟩) (h.centralizer_U_eq hy)
  have h2 := card_fixVec_even (h.permOf hy) hσ hf
  omega

theorem card_centralizer_U0_inter_le [DecidableEq Γ] (h : KSetup U K x v t) {y y' : Γ}
    (hy : y ∈ K) (hy' : y' ∈ K) (hσ : h.permOf hy * h.permOf hy = 1)
    (hσ' : h.permOf hy' * h.permOf hy' = 1)
    (hc : h.permOf hy * h.permOf hy' = h.permOf hy' * h.permOf hy)
    (hne : h.permOf hy ≠ h.permOf hy') (hne1 : h.permOf hy ≠ 1) (hne1' : h.permOf hy' ≠ 1)
    (hf : fixCount (h.permOf hy) = 0 ∨ fixCount (h.permOf hy) = 2)
    (hf' : fixCount (h.permOf hy') = 0 ∨ fixCount (h.permOf hy') = 2)
    (hff : fixCount (h.permOf hy * h.permOf hy') = 0 ∨ fixCount (h.permOf hy * h.permOf hy') = 2) :
    Nat.card ↥((U ⊔ zpowers t) ⊓ centralizer ({y} : Set Γ) ⊓ centralizer ({y'} : Set Γ)) ≤ 4 := by
  have h1 := h.card_of_image_set _ _
    (fun f hf => by
      rw [Finset.mem_inter] at hf ⊢
      exact ⟨FixVec_add_one hf.1, FixVec_add_one hf.2⟩) (h.centralizer_U0_inter_eq hy hy')
  have h2 := card_fixVec_inter hσ hσ' hc hne hne1 hne1' hf hf' hff
  omega

theorem exists_pair (h : KSetup U K x v t) {a : Γ} (ha : a ∈ U) (ha1 : a ≠ 1) :
    ∃ p q : Fin 6, p ≠ q ∧ a = h.dd p * h.dd q := by
  obtain ⟨f, rfl⟩ := h.evG_surj (mem_sup_left ha)
  have hev : ∑ i, f i = 0 := (h.evG_mem_U_iff f).1 ha
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact ha1 (congrArg Subtype.val h.ev_zero)
  have hf1 : f ≠ 1 := by
    rintro rfl
    exact ha1 (congrArg Subtype.val h.ev_ones)
  obtain ⟨p, q, hpq, hpq'⟩ := even_pair f hev hf0 hf1
  refine ⟨p, q, hpq, ?_⟩
  have key : h.evG (Pi.single p 1 + Pi.single q 1) = h.dd p * h.dd q := by
    rw [h.evG_add]
    unfold evG
    rw [h.ev_single, h.ev_single]
    rfl
  rcases hpq' with e | e
  · rw [e, key]
  · rw [← key, ← e, h.evG_add]
    have : h.evG 1 = 1 := congrArg Subtype.val h.ev_ones
    rw [this, mul_one]

end KSetup

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

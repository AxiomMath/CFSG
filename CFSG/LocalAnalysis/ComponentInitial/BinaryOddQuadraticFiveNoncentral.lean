module

public import CFSG.LocalAnalysis.ComponentInitial.BinaryOddQuadraticFiveSplitting
public import Mathlib.FieldTheory.Finiteness

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace OddQuadraticFive

open BinarySymplecticTransvection
open scoped commutatorElement

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {D : Type} [Group D] {B : Subgroup D}
  {θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2)} {b : LinearMap.BilinForm (ZMod 2) E}
  {Q : QuadraticForm (ZMod 2) E}

theorem eq_of_forall_basis (hnd : b.Nondegenerate) (e : Module.Basis (Fin 4) (ZMod 2) E)
    {u u' : E} (h : ∀ i, b (e i) u = b (e i) u') : u = u' := by
  rw [← sub_eq_zero]
  refine hnd.2 _ fun x => ?_
  rw [← e.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, map_sub, h, sub_self, smul_zero]

theorem exists_dual_vector (hnd : b.Nondegenerate) [Finite E] (hcardE : Nat.card E = 16)
    (e : Module.Basis (Fin 4) (ZMod 2) E) (β : Fin 4 → ZMod 2) : ∃ u, ∀ i, b (e i) u = β i := by
  have hinj : Function.Injective fun u : E => fun i => b (e i) u := fun u u' h =>
    eq_of_forall_basis hnd e fun i => congrFun h i
  have hbij := hinj.bijective_of_nat_card_le (by
    rw [hcardE, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num)
  obtain ⟨u, hu⟩ := hbij.2 β
  exact ⟨u, fun i => congrFun hu i⟩

namespace Labels

variable (L : Labels θ b 1)

theorem comm_bv_subA (u : E) (s : ZMod 2) (d : D) :
    (bv θ ((u, s), 0))⁻¹ * d⁻¹ * bv θ ((u, s), 0) * d =
      bv θ (b (L.lab d).1 u • rV, 0) := by
  rw [L.comm_bv]
  simp

theorem subI_le_commutator (hb : b.IsAlt) (hnd : b.Nondegenerate) (hsurj : ∀ a, ∃ d, L.lab d = a)
    {C : Subgroup D} (hAC : subA θ ≤ C) (hidx : ∀ d, d ∈ C ∨ d * zz θ ∈ C) {w : E}
    (hw : w ≠ 0) : subI θ ≤ ⁅C, C⁆ := by
  rintro _ ⟨c, rfl⟩
  rcases zmod_two_cases c with rfl | rfl
  · rw [zero_smul, Prod.mk_zero_zero, bv_zero]
    exact one_mem _
  · obtain ⟨c₁, hc₁, hl⟩ := L.exists_mem_lab hb hsurj hidx (w, 0)
    obtain ⟨u, hu⟩ := exists_apply_eq_one hnd hw
    have hx : bv θ ((u, 0), 0) ∈ C := hAC ⟨_, rfl⟩
    have h := L.comm_bv_subA u 0 c₁
    rw [hl, symm_apply hb, hu] at h
    rw [← h, show (bv θ ((u, 0), 0))⁻¹ * c₁⁻¹ * bv θ ((u, 0), 0) * c₁ =
      ⁅(bv θ ((u, 0), 0))⁻¹, c₁⁻¹⁆ by rw [commutatorElement_def, inv_inv, inv_inv]]
    exact Subgroup.commutator_mem_commutator (inv_mem hx) (inv_mem hc₁)

theorem sq_mem_subI (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) {C : Subgroup D} (hidx : ∀ d, d ∈ C ∨ d * zz θ ∈ C)
    (hω : ∀ c ∈ C, ∀ c' ∈ C, om θ c c' = 0) {c : D} (hc : c ∈ C) : c ^ 2 ∈ subI θ := by
  obtain ⟨v, hv⟩ := L.sq_mem_subA hb hfaith c
  have hcen : ∀ c' ∈ C, c'⁻¹ * c ^ 2 * c' = c ^ 2 := by
    intro c' hc'
    have hw : c⁻¹ * c'⁻¹ * c * c' ∈ subI θ :=
      mem_subI_of_mem_subA (L.comm_mem_subA hb hfaith c c') (hω c hc c' hc')
    have e : (c ^ 2)⁻¹ * c'⁻¹ * c ^ 2 * c' =
        c⁻¹ * (c⁻¹ * c'⁻¹ * c * c') * c * (c⁻¹ * c'⁻¹ * c * c') := by
      rw [sq]
      group
    have hconj : c⁻¹ * (c⁻¹ * c'⁻¹ * c * c') * c = c⁻¹ * c'⁻¹ * c * c' := by
      rw [mul_assoc, ← L.commute_of_mem_subI hw c, ← mul_assoc, inv_mul_cancel, one_mul]
    have e1 : (c ^ 2)⁻¹ * c'⁻¹ * c ^ 2 * c' = 1 := by
      rw [e, hconj, ← sq, sq_eq_one_of_mem θ (subA_le θ (subI_le_subA θ hw))]
    calc c'⁻¹ * c ^ 2 * c' = c ^ 2 * ((c ^ 2)⁻¹ * c'⁻¹ * c ^ 2 * c') := by group
      _ = c ^ 2 := by rw [e1, mul_one]
  have hv1 : v.1 = 0 := by
    refine hnd.2 _ fun w => ?_
    obtain ⟨c', hc', hl⟩ := L.exists_mem_lab hb hsurj hidx (w, 0)
    have h := hcen c' hc'
    rw [← hv, L.conj_bv, hl] at h
    have h2 := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.2) (bv_injective θ h)
    simpa [rV] using h2
  rw [← hv]
  exact mem_subI_of_mem_subA ⟨v, rfl⟩ (by rw [cB_bv]; exact hv1)

theorem mem_closure_of_mem (hb : b.IsAlt) {C : Subgroup D} {ξ : D}
    (hCF : ∀ c ∈ C, (L.lab c).1 = 0 → c ∈ subA θ ∨ ξ⁻¹ * c ∈ subA θ)
    (e : Module.Basis (Fin 4) (ZMod 2) E) (c : Fin 4 → D) (hcC : ∀ i, c i ∈ C)
    (hcl : ∀ i, (L.lab (c i)).1 = e i) {g : D} (hg : g ∈ C) :
    g ∈ Subgroup.closure (subA θ ∪ {ξ} ∪ Set.range c : Set D) := by
  have hpow : ∀ (x : D) (k : ZMod 2), (L.lab (x ^ k.val)).1 = k • (L.lab x).1 := by
    intro x k
    rcases zmod_two_cases k with rfl | rfl
    · rw [ZMod.val_zero, pow_zero, L.lab_one, zero_smul]
      rfl
    · rw [ZMod.val_one, pow_one, one_smul]
  set n := e.repr (L.lab g).1 with hn
  set P := c 0 ^ (n 0).val * c 1 ^ (n 1).val * c 2 ^ (n 2).val * c 3 ^ (n 3).val with hP
  have hPl : (L.lab P).1 = (L.lab g).1 := by
    rw [hP, L.lab_mul_fst hb, L.lab_mul_fst hb, L.lab_mul_fst hb, hpow, hpow, hpow, hpow, hcl,
      hcl, hcl, hcl]
    conv_rhs => rw [← e.sum_repr (L.lab g).1, Fin.sum_univ_four]
  have hcl' : ∀ i, c i ∈ Subgroup.closure (subA θ ∪ {ξ} ∪ Set.range c : Set D) := fun i =>
    Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hPcl : P ∈ Subgroup.closure (subA θ ∪ {ξ} ∪ Set.range c : Set D) :=
    mul_mem (mul_mem (mul_mem (pow_mem (hcl' 0) _) (pow_mem (hcl' 1) _)) (pow_mem (hcl' 2) _))
      (pow_mem (hcl' 3) _)
  have hPC : P ∈ C :=
    mul_mem (mul_mem (mul_mem (pow_mem (hcC 0) _) (pow_mem (hcC 1) _)) (pow_mem (hcC 2) _))
      (pow_mem (hcC 3) _)
  have hh : (L.lab (P⁻¹ * g)).1 = 0 := by
    rw [L.lab_mul_fst hb, L.lab_inv_fst hb, hPl, add_self_eq_zero_zmod_two]
  have hg' : g = P * (P⁻¹ * g) := by group
  rw [hg']
  refine mul_mem hPcl ?_
  rcases hCF _ (mul_mem (inv_mem hPC) hg) hh with h | h
  · exact Subgroup.subset_closure (Or.inl (Or.inl h))
  · have e' : P⁻¹ * g = ξ * (ξ⁻¹ * (P⁻¹ * g)) := by group
    rw [e']
    exact mul_mem (Subgroup.subset_closure (Or.inl (Or.inr rfl)))
      (Subgroup.subset_closure (Or.inl (Or.inl h)))


theorem center_props (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (hsurj : ∀ a, ∃ d, L.lab d = a) [Finite E] (hcardE : Nat.card E = 16)
    (e : Module.Basis (Fin 4) (ZMod 2) E) {C : Subgroup D} {ξ : D} (hAC : subA θ ≤ C)
    (hidx : ∀ d, d ∈ C ∨ d * zz θ ∈ C) (hω : ∀ c ∈ C, ∀ c' ∈ C, om θ c c' = 0) (hξC : ξ ∈ C)
    (hξl : L.lab ξ = rV) (hCF : ∀ c ∈ C, (L.lab c).1 = 0 → c ∈ subA θ ∨ ξ⁻¹ * c ∈ subA θ) :
    Nat.card (Subgroup.center C) = 4 ∧
      C ⊓ L.subF hb = subA θ ⊔ (Subgroup.center C).map C.subtype ∧
      ∀ x ∈ C ⊓ L.subF hb, ∀ y ∈ C ⊓ L.subF hb, x * y = y * x := by
  classical
  have hξF : ξ ∈ L.subF hb := by
    rw [mem_subF, hξl]
    rfl
  choose c hcC hcl using fun i : Fin 4 => L.exists_mem_lab hb hsurj hidx (e i, 0)
  have hcl1 : ∀ i, (L.lab (c i)).1 = e i := fun i => by rw [hcl]
  choose β hβ using fun i : Fin 4 =>
    mem_subI_of_mem_subA (L.comm_mem_subA hb hfaith ξ (c i)) (hω ξ hξC (c i) (hcC i))
  obtain ⟨u₀, hu₀⟩ := exists_dual_vector hnd hcardE e β
  have hξpow : ∀ t : ZMod 2, ξ ^ t.val ∈ C ∧ ξ ^ t.val ∈ L.subF hb ∧
      (L.lab (ξ ^ t.val)).2 = t ∧
      ∀ i, (ξ ^ t.val)⁻¹ * (c i)⁻¹ * ξ ^ t.val * c i = bv θ ((t * β i) • rV, 0) := by
    intro t
    rcases zmod_two_cases t with rfl | rfl
    · refine ⟨by simp, by simp, by rw [ZMod.val_zero, pow_zero, L.lab_one]; rfl, fun i => ?_⟩
      rw [ZMod.val_zero, pow_zero, zero_mul, zero_smul, Prod.mk_zero_zero, bv_zero]
      group
    · refine ⟨by rw [ZMod.val_one, pow_one]; exact hξC, by rw [ZMod.val_one, pow_one]; exact hξF,
        by rw [ZMod.val_one, pow_one, hξl]; rfl, fun i => ?_⟩
      rw [ZMod.val_one, pow_one, one_mul, hβ]
  have hcomm : ∀ (t s : ZMod 2) (v : E) (i : Fin 4),
      (ξ ^ t.val * bv θ ((v, s), 0))⁻¹ * (c i)⁻¹ * (ξ ^ t.val * bv θ ((v, s), 0)) * c i =
        bv θ ((t * β i + b (e i) v) • rV, 0) := by
    intro t s v i
    have e₁ : (ξ ^ t.val * bv θ ((v, s), 0))⁻¹ * (c i)⁻¹ * (ξ ^ t.val * bv θ ((v, s), 0)) * c i =
        (bv θ ((v, s), 0))⁻¹ * ((ξ ^ t.val)⁻¹ * (c i)⁻¹ * ξ ^ t.val * c i) * bv θ ((v, s), 0) *
          ((bv θ ((v, s), 0))⁻¹ * (c i)⁻¹ * bv θ ((v, s), 0) * c i) := by group
    have hI : bv θ ((t * β i) • rV, 0) ∈ subI θ := ⟨_, rfl⟩
    have hwx : (bv θ ((v, s), 0))⁻¹ * bv θ ((t * β i) • rV, 0) * bv θ ((v, s), 0) =
        bv θ ((t * β i) • rV, 0) := by
      rw [mul_assoc, ← L.commute_of_mem_subI hI, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e₁, (hξpow t).2.2.2 i, hwx, L.comm_bv_subA, hcl1, ← bv_add, Prod.mk_add_mk, add_zero,
      ← add_smul]
  have hdecomp : ∀ g ∈ C, (L.lab g).1 = 0 →
      ∃ (t s : ZMod 2) (v : E), g = ξ ^ t.val * bv θ ((v, s), 0) := by
    intro g hg hg1
    rcases hCF g hg hg1 with h | h
    · obtain ⟨w, hw⟩ := h
      exact ⟨0, w.2, w.1, by rw [ZMod.val_zero, pow_zero, one_mul, Prod.mk.eta, hw]⟩
    · obtain ⟨w, hw⟩ := h
      refine ⟨1, w.2, w.1, ?_⟩
      rw [ZMod.val_one, pow_one, Prod.mk.eta, hw]
      group
  have hcenF : ∀ g ∈ C, (∀ g' ∈ C, g * g' = g' * g) → (L.lab g).1 = 0 := by
    intro g hg hcen
    refine hnd.1 _ fun u => ?_
    have h := hcen _ (hAC ⟨((u, 0) : E × ZMod 2), rfl⟩)
    have h2 := L.comm_bv_subA u 0 g
    have h3 : (bv θ ((u, 0), 0))⁻¹ * g⁻¹ * bv θ ((u, 0), 0) * g = 1 := by
      rw [mul_assoc, ← h]
      group
    rw [h3, ← bv_zero θ] at h2
    have := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.2) (bv_injective θ h2)
    simpa [rV] using this.symm
  have hgens : ∀ (t s : ZMod 2) (v : E), (∀ i, t * β i + b (e i) v = 0) →
      ∀ g' ∈ C, (ξ ^ t.val * bv θ ((v, s), 0)) * g' = g' * (ξ ^ t.val * bv θ ((v, s), 0)) := by
    intro t s v hv g' hg'
    set g := ξ ^ t.val * bv θ ((v, s), 0) with hg
    have hgF : g ∈ L.subF hb := mul_mem (hξpow t).2.1 (L.subA_le_subF hb ⟨_, rfl⟩)
    have hle : Subgroup.closure (subA θ ∪ {ξ} ∪ Set.range c : Set D) ≤
        Subgroup.centralizer {g} := by
      rw [Subgroup.closure_le]
      rintro x ((hx | hx) | ⟨i, rfl⟩) _ rfl
      · exact (L.commute_of_mem_subF hb hgF hx)
      · rw [Set.mem_singleton_iff.1 hx]
        have h1 : ξ * ξ ^ t.val = ξ ^ t.val * ξ := (Commute.self_pow ξ _).eq
        have h2 := L.commute_of_mem_subF hb hξF (show bv θ ((v, s), 0) ∈ subA θ from ⟨_, rfl⟩)
        show g * ξ = ξ * g
        rw [hg, mul_assoc, ← h2, ← mul_assoc, ← h1, mul_assoc]
      · have h := hcomm t s v i
        rw [← hg, hv, zero_smul, Prod.mk_zero_zero, bv_zero] at h
        have : c i * g = g * c i := by
          calc c i * g = c i * g * (g⁻¹ * (c i)⁻¹ * g * c i) := by rw [h, mul_one]
            _ = g * c i := by group
        exact this.symm
    exact (hle (L.mem_closure_of_mem hb hCF e c hcC hcl1 hg') g rfl)
  have hcrit : ∀ (t s : ZMod 2) (v : E), (∀ g' ∈ C,
      (ξ ^ t.val * bv θ ((v, s), 0)) * g' = g' * (ξ ^ t.val * bv θ ((v, s), 0))) ↔ v = t • u₀ := by
    intro t s v
    have hb' : ∀ i, b (e i) (t • u₀) = t * β i := fun i => by rw [map_smul, smul_eq_mul, hu₀]
    constructor
    · intro hcen
      refine eq_of_forall_basis hnd e fun i => ?_
      have h := hcomm t s v i
      have h1 : (ξ ^ t.val * bv θ ((v, s), 0))⁻¹ * (c i)⁻¹ * (ξ ^ t.val * bv θ ((v, s), 0)) *
          c i = 1 := by
        rw [mul_assoc, hcen _ (hcC i)]
        group
      rw [h1, ← bv_zero θ] at h
      have h2 := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.2) (bv_injective θ h)
      simp only [Prod.snd_zero, Prod.fst_zero, Prod.smul_snd, rV, smul_eq_mul, mul_one] at h2
      rw [hb']
      exact (eq_of_add_eq_zero_zmod2 h2.symm).symm
    · rintro rfl
      exact hgens t s _ fun i => by rw [hb', add_self_eq_zero_zmod_two]
  have hmemC : ∀ t s : ZMod 2, ξ ^ t.val * bv θ ((t • u₀, s), 0) ∈ C := fun t s =>
    mul_mem (hξpow t).1 (hAC ⟨_, rfl⟩)
  have hmemZ : ∀ t s : ZMod 2,
      (⟨_, hmemC t s⟩ : C) ∈ Subgroup.center C := fun t s =>
    Subgroup.mem_center_iff.2 fun g' =>
      Subtype.ext ((hcrit t s _).2 rfl g' g'.2).symm
  set f : ZMod 2 × ZMod 2 → Subgroup.center C := fun p => ⟨⟨_, hmemC p.1 p.2⟩, hmemZ p.1 p.2⟩
    with hf
  have hfinj : Function.Injective f := by
    rintro ⟨t, s⟩ ⟨t', s'⟩ h
    have h' : ξ ^ t.val * bv θ ((t • u₀, s), 0) = ξ ^ t'.val * bv θ ((t' • u₀, s'), 0) :=
      congrArg (fun x : Subgroup.center C => ((x : C) : D)) h
    have ht : t = t' := by
      have := congrArg (fun x => (L.lab x).2) h'
      simp only [L.lab_mul_bv hb, (hξpow t).2.2.1, (hξpow t').2.2.1] at this
      exact this
    subst ht
    rw [mul_right_inj] at h'
    have := congrArg (fun x : (E × ZMod 2) × ZMod 2 => x.1.2) (bv_injective θ h')
    simp only at this
    rw [this]
  have hfsurj : Function.Surjective f := by
    rintro ⟨⟨g, hg⟩, hgZ⟩
    have hcen : ∀ g' ∈ C, g * g' = g' * g := fun g' hg' =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.1 hgZ ⟨g', hg'⟩)).symm
    obtain ⟨t, s, v, rfl⟩ := hdecomp g hg (hcenF g hg hcen)
    have hv := (hcrit t s v).1 hcen
    subst hv
    exact ⟨(t, s), rfl⟩
  have hcard : Nat.card (Subgroup.center C) = 4 := by
    rw [← Nat.card_eq_of_bijective f ⟨hfinj, hfsurj⟩, Nat.card_prod, Nat.card_zmod]
  have hab : ∀ x ∈ C ⊓ L.subF hb, ∀ y ∈ C ⊓ L.subF hb, x * y = y * x := by
    intro x hx y hy
    rcases hCF x hx.1 hx.2 with hxA | hxA
    · exact (L.commute_of_mem_subF hb hy.2 hxA).symm
    rcases hCF y hy.1 hy.2 with hyA | hyA
    · exact L.commute_of_mem_subF hb hx.2 hyA
    have hx' : x = ξ * (ξ⁻¹ * x) := by group
    have hy' : y = ξ * (ξ⁻¹ * y) := by group
    have c1 : Commute ξ (ξ⁻¹ * x) := L.commute_of_mem_subF hb hξF hxA
    have c2 : Commute ξ (ξ⁻¹ * y) := L.commute_of_mem_subF hb hξF hyA
    have c3 : Commute (ξ⁻¹ * x) (ξ⁻¹ * y) :=
      B_comm θ (subA_le θ hxA) (subA_le θ hyA)
    rw [hx', hy']
    exact ((Commute.refl ξ).mul_right c2 |>.mul_left (c1.symm.mul_right c3)).eq
  refine ⟨hcard, le_antisymm (fun g hg => ?_) (sup_le (le_inf hAC (L.subA_le_subF hb)) ?_), hab⟩
  · rcases hCF g hg.1 hg.2 with h | h
    · exact Subgroup.mem_sup_left h
    · have e₁ : g = (ξ * bv θ (((1 : ZMod 2) • u₀, 0), 0)) *
          ((bv θ (((1 : ZMod 2) • u₀, 0), 0))⁻¹ * (ξ⁻¹ * g)) := by group
      rw [e₁]
      refine mul_mem (Subgroup.mem_sup_right ⟨f (1, 0), ?_, ?_⟩)
        (Subgroup.mem_sup_left (mul_mem (inv_mem ⟨_, rfl⟩) h))
      · exact (f (1, 0)).2
      · change ξ ^ (1 : ZMod 2).val * bv θ (((1 : ZMod 2) • u₀, 0), 0) = _
        rw [ZMod.val_one, pow_one]
  · rintro _ ⟨g, hgZ, rfl⟩
    have hcen : ∀ g' ∈ C, (g : D) * g' = g' * g := fun g' hg' =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.1 hgZ ⟨g', hg'⟩)).symm
    exact ⟨g.2, (L.mem_subF hb).2 (hcenF g g.2 hcen)⟩

end Labels

end OddQuadraticFive


open OddQuadraticFive

theorem binary_odd_quadratic_five_noncentral_action_normal_index_two_subgroup
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (hE : Module.finrank (ZMod 2) E = 4) (b : LinearMap.BilinForm (ZMod 2) E) (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (Q : QuadraticForm (ZMod 2) E) (hQ : QuadraticMap.polarBilin Q = b)
    {D : Type} [Group D] [Finite D] (B : Subgroup D) [B.Normal]
    (θ : B ≃* Multiplicative ((E × ZMod 2) × ZMod 2))
    (hconj : ∀ d : D, ∃ a : E × ZMod 2, ∀ v : E × ZMod 2,
      d⁻¹ * bv θ (v, 1) * d = bv θ (v + a + b a.1 v.1 • rV, 1))
    (hsurj : ∀ a : E × ZMod 2, ∃ d : D, ∀ v : E × ZMod 2,
      d⁻¹ * bv θ (v, 1) * d = bv θ (v + a + b a.1 v.1 • rV, 1))
    (hfaith : ∀ d : D, (∀ v, d⁻¹ * bv θ (v, 1) * d = bv θ (v, 1)) → d ∈ B)
    (act : bilinIsometryGroup b →* MulAut D)
    (hact : ∀ s v ε, act s (bv θ (v, ε)) = bv θ (hV hQ s v, ε)) :
    Nat.card D = 2048 ∧ commutator D = subA θ ∧
      Subgroup.closure {x : D | ∃ y : D, y ^ 2 = x} = subA θ ∧
    ∃ F : Subgroup D, (∀ d, d ∈ F ↔ ∃ x ∈ subI θ, d⁻¹ * zz θ * d = zz θ * x) ∧
      F.Normal ∧ (∀ s, ∀ d ∈ F, act s d ∈ F) ∧ Nat.card F = 128 ∧
      (Subgroup.center F).map F.subtype = subA θ ∧ ⁅F, F⁆ = subI θ ∧
      Subgroup.closure {x : D | ∃ y ∈ F, y ^ 2 = x} = subI θ ∧
    ∃ C : Subgroup D, C.Normal ∧ (∀ s, ∀ c ∈ C, act s c ∈ C) ∧ Nat.card C = 1024 ∧
      Subgroup.zpowers (zz θ) ⊔ C = ⊤ ∧ B ⊓ C = subA θ ∧ ⁅C, C⁆ = subI θ ∧
      Subgroup.closure {x : D | ∃ y ∈ C, y ^ 2 = x} = subI θ ∧
      Nat.card (Subgroup.center C) = 4 ∧
      C ⊓ F = subA θ ⊔ (Subgroup.center C).map C.subtype ∧
      ∀ x ∈ C ⊓ F, ∀ y ∈ C ⊓ F, x * y = y * x := by
  have : Finite E := Module.finite_of_finite (ZMod 2)
  have hcardE : Nat.card E = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), hE, Nat.card_zmod]
    norm_num
  have hE4 : 4 < Nat.card E := by
    rw [hcardE]
    norm_num
  let e : Module.Basis (Fin 4) (ZMod 2) E := Module.finBasisOfFinrankEq (ZMod 2) E hE
  choose lab hlab using hconj
  let L : Labels θ b 1 := ⟨lab, fun d v => by rw [hlab d v, one_mul]⟩
  have hsurj' : ∀ a, ∃ d, L.lab d = a := by
    intro a
    obtain ⟨d, hd⟩ := hsurj a
    refine ⟨d, ?_⟩
    have h := (L.conj_zz d).symm.trans (hd 0)
    simp only [zero_add, Prod.fst_zero, map_zero, zero_smul, add_zero] at h
    exact congrArg Prod.fst (bv_injective θ h)
  have hcard := L.natCard_D hb hQ hfaith hsurj' hcardE
  have hcomm := L.commutator_eq hb hfaith hsurj'
  obtain ⟨hFn, hFS, hFc, hFZ, hFc', hFsq⟩ := L.subF_props hQ act hact hb hnd hfaith hsurj' hcardE
  obtain ⟨C, a, ξ, hAC, hz, hidx, hCS, hω, -, hξC, hξl, hCF⟩ :=
    L.exists_index_two hQ act hact hb hnd hfaith hsurj' hE4 e
  obtain ⟨hCc, hCtop, hBC⟩ := index_two_props hAC hz hidx hcard
  have hCI : subI θ ≤ ⁅C, C⁆ := L.subI_le_commutator hb hnd hsurj' hAC hidx (e.ne_zero 0)
  have hCcomm : ⁅C, C⁆ = subI θ := le_antisymm (L.commutator_le_subI hb hfaith hω) hCI
  have hCsq : Subgroup.closure {x : D | ∃ y ∈ C, y ^ 2 = x} = subI θ := by
    refine le_antisymm ((Subgroup.closure_le _).2 ?_) (hCI.trans (commutator_le_closure_sq C))
    rintro _ ⟨y, hy, rfl⟩
    exact L.sq_mem_subI hb hnd hfaith hsurj' hidx hω hy
  obtain ⟨hZ, hCF', hab⟩ := L.center_props hb hnd hfaith hsurj' hcardE e hAC hidx hω hξC hξl hCF
  exact ⟨hcard, hcomm, L.closure_sq_eq hb hfaith hsurj', L.subF hb,
    fun d => L.mem_subF_iff_conj hb, hFn, hFS, hFc, hFZ, hFc', hFsq, C,
    normal_of_commutator_le (hcomm.le.trans hAC), hCS, hCc, hCtop, hBC, hCcomm, hCsq, hZ, hCF',
    hab⟩

end CFSG.LocalAnalysis.ComponentInitial

module

public import CFSG.CGT.Foote82.T66.CitedCaseII
public import CFSG.CGT.Foote82.T66.CertProofsH1OmegaMinusSix
import CFSG.CGT.Foote82.T66.FaithfulBasic
import CFSG.Quasithin.Background.G11Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel Matrix

namespace CaseIISplitAux

abbrev N6 : Type := Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 2

abbrev act (x : ↥(omegaMinusTwo 2)) (v : N6) : N6 :=
  ((x : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) :
    Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ v

def pf (x y : N6) : ZMod 2 :=
  x (.inl 0) * y (.inr (.inl 0)) + x (.inr (.inl 0)) * y (.inl 0) +
    x (.inl 1) * y (.inr (.inl 1)) + x (.inr (.inl 1)) * y (.inl 1) +
    x (.inr (.inr 0)) * y (.inr (.inr 1)) + x (.inr (.inr 1)) * y (.inr (.inr 0))

theorem q6_add (x y : N6) :
    OmegaSix.q6 (x + y) = OmegaSix.q6 x + OmegaSix.q6 y + pf x y := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [OmegaSix.q6, pf, Pi.add_apply]
  linear_combination
    (x (.inr (.inr 0)) * y (.inr (.inr 0)) + x (.inr (.inr 1)) * y (.inr (.inr 1))) * h2

theorem pf_add_left (x x' y : N6) : pf (x + x') y = pf x y + pf x' y := by
  simp only [pf, Pi.add_apply]
  ring

theorem pf_add_right (x y y' : N6) : pf x (y + y') = pf x y + pf x y' := by
  simp only [pf, Pi.add_apply]
  ring

theorem pf_sub_right (x y y' : N6) : pf x (y - y') = pf x y - pf x y' := by
  simp only [pf, Pi.sub_apply]
  ring

theorem pf_zero_left (y : N6) : pf 0 y = 0 := by
  simp [pf]

theorem pf_mulVec {g : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)}
    (hg : g ∈ orthogonalMinus 2 (ZMod 2) 1 1) (x y : N6) :
    pf ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ x)
      ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ y) = pf x y := by
  have h := q6_add ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ x)
    ((g : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)) *ᵥ y)
  rw [← mulVec_add, OmegaSix.q6_mulVec_of_mem hg, OmegaSix.q6_mulVec_of_mem hg,
    OmegaSix.q6_mulVec_of_mem hg, q6_add] at h
  exact (add_left_cancel h).symm

theorem pf_act (x : ↥(omegaMinusTwo 2)) (v w : N6) : pf (act x v) w = pf v (act x⁻¹ w) := by
  have hx := OmegaSix.omegaMinusTwo_le_orthogonalMinus x.2
  have e : w = act x (act x⁻¹ w) := by
    rw [act, act, mulVec_mulVec, Subgroup.coe_inv, Units.mul_inv, one_mulVec]
  conv_lhs => rw [e]
  exact pf_mulVec hx v _

@[expose] def bv (i : Fin 2 ⊕ Fin 2 ⊕ Fin 2) : N6 := fun j => if i = j then 1 else 0

theorem bv_eq (i : Fin 2 ⊕ Fin 2 ⊕ Fin 2) : bv i = fun j => if i = j then 1 else 0 := rfl

theorem exists_pf_eq (ξ : N6 →+ ZMod 2) : ∃ y : N6, ∀ x, ξ x = pf x y := by
  refine ⟨OmegaSix.vec6 (ξ (bv (.inr (.inl 0)))) (ξ (bv (.inr (.inl 1)))) (ξ (bv (.inl 0)))
    (ξ (bv (.inl 1))) (ξ (bv (.inr (.inr 1)))) (ξ (bv (.inr (.inr 0)))), fun x => ?_⟩
  have h := LinearMap.pi_apply_eq_sum_univ (ξ.toZModLinearMap 2) x
  rw [AddMonoidHom.coe_toZModLinearMap] at h
  rw [h]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_two, smul_eq_mul, pf, OmegaSix.vec6,
    Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, bv_eq]
  ring

theorem eq_of_pf_eq {z z' : N6} (h : ∀ x, pf x z = pf x z') : z = z' := by
  funext j
  rcases j with k | k | k <;> fin_cases k
  · simpa [pf, bv] using h (bv (.inr (.inl 0)))
  · simpa [pf, bv] using h (bv (.inr (.inl 1)))
  · simpa [pf, bv] using h (bv (.inl 0))
  · simpa [pf, bv] using h (bv (.inl 1))
  · simpa [pf, bv] using h (bv (.inr (.inr 1)))
  · simpa [pf, bv] using h (bv (.inr (.inr 0)))

theorem exists_pf_of_ker {A : Type*} [AddCommGroup A] (β : A →+ N6)
    (hβ : Function.Surjective β) (θ : A →+ ZMod 2) (hθ : β.ker ≤ θ.ker) :
    ∃ y : N6, ∀ a, θ a = pf (β a) y := by
  obtain ⟨y, hy⟩ := exists_pf_eq (β.liftOfRightInverse (Function.surjInv hβ)
    (Function.rightInverse_surjInv hβ) ⟨θ, hθ⟩)
  exact ⟨y, fun a => by rw [← hy, AddMonoidHom.liftOfRightInverse_comp_apply]⟩

theorem relators_sum (p q : ZMod 2)
    (h : ∀ w ∈ OmegaSix.relators, (w.map fun i => if i = 0 then p else q).sum = 0) :
    p = 0 ∧ q = 0 := by
  revert p q
  decide

theorem omega_addHom_eq_zero
    (τ : ↥(omegaMinusTwo 2) → ZMod 2) (hτ : ∀ x y, τ (x * y) = τ x + τ y)
    (x : ↥(omegaMinusTwo 2)) : τ x = 0 := by
  have h1 : τ 1 = 0 := by
    have h := hτ 1 1
    rw [one_mul] at h
    exact left_eq_add.mp h
  have hprod : ∀ l : List ↥(omegaMinusTwo 2), τ l.prod = (l.map τ).sum := by
    intro l
    induction l with
    | nil => rw [List.prod_nil, h1, List.map_nil, List.sum_nil]
    | cons y l ih => rw [List.prod_cons, hτ, ih, List.map_cons, List.sum_cons]
  have hgen : ∀ i, τ (OmegaSix.gen6 i) =
      if i = 0 then τ (OmegaSix.gen6 0) else τ (OmegaSix.gen6 1) := by
    intro i
    by_cases hi : i = 0
    · subst hi
      rfl
    · rw [if_neg hi]
      simp only [OmegaSix.gen6, if_neg hi, one_ne_zero, if_false]
  obtain ⟨hp, hq⟩ := relators_sum (τ (OmegaSix.gen6 0)) (τ (OmegaSix.gen6 1)) fun w hw => by
    have h := congrArg τ (OmegaSix.relators_spec w hw).2
    rw [hprod, List.map_map, h1] at h
    rw [← h]
    congr 1
    exact List.map_congr_left fun i _ => (hgen i).symm
  have hx : x ∈ Subgroup.closure (OmegaSix.gen6 '' Set.Iio 2) := by
    rw [OmegaSix.closure_gen6]
    exact Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨i, -, rfl⟩ := hy
    rw [hgen i]
    split_ifs
    · exact hp
    · exact hq
  | one => exact h1
  | mul y z _ _ hy hz => rw [hτ, hy, hz, add_zero]
  | inv y _ hy =>
    have h := hτ y y⁻¹
    rw [mul_inv_cancel, h1, hy, zero_add] at h
    exact h.symm

theorem addHom_eq_zero_of_equiv {X : Type*} [Group X]
    (φ : X ≃* ↥(omegaMinusTwo 2)) (τ : X → ZMod 2) (hτ : ∀ x y, τ (x * y) = τ x + τ y)
    (x : X) : τ x = 0 := by
  have h := omega_addHom_eq_zero (fun z => τ (φ.symm z)) (fun z z' => by rw [map_mul, hτ]) (φ x)
  simpa using h

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem eq_zero_of_forall_sub {H : Subgroup (GLV V)} (f : ↥(commSpace H ⊤) →+ ZMod 2)
    (hf : ∀ u : ↥(commSpace H ⊤), (∃ h ∈ H, ∃ v : V, (u : V) = h v - v) → f u = 0)
    (u : ↥(commSpace H ⊤)) : f u = 0 := by
  have hle : commSpace H ⊤ ≤ (LinearMap.ker (f.toZModLinearMap 2)).map (commSpace H ⊤).subtype :=
    commSpace_le_iff.2 fun h hh v _ =>
      ⟨⟨h v - v, sub_mem_commSpace hh Submodule.mem_top⟩, hf _ ⟨h, hh, v, rfl⟩, rfl⟩
  obtain ⟨u', hu', he⟩ := hle u.2
  have e : u' = u := Subtype.ext he
  rw [← e]
  exact hu'

end CaseIISplitAux

open CaseIISplitAux

theorem caseIISplit_holds :
    CaseIISplit := by
  intro V _ _ _ H φ β hβ hker hequiv
  have hkerpt : ∀ w : ↥(commSpace H ⊤), β w = 0 ↔ (w : V) ∈ fixedSpace H :=
    L13Aux.ker_iff_of_eq hker
  have hinv : Invariant H (commSpace H ⊤) := L13Aux.invariant_commSpace_top H
  have hsub : ∀ h ∈ H, ∀ v : V, h v - v ∈ commSpace H ⊤ :=
    fun h hh v => sub_mem_commSpace hh Submodule.mem_top
  have hβh : ∀ (h : ↥H) (u : ↥(commSpace H ⊤)),
      β ⟨(h : GLV V) u, hinv h h.2 u u.2⟩ = act (φ h) (β u) :=
    fun h u => hequiv h u _ rfl
  have hdisj : ∀ c ∈ commSpace H ⊤, c ∈ fixedSpace H → c = 0 := by
    intro c hcU hcF
    refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) c).mp fun μ => ?_
    have hy : ∀ h : ↥H, ∃ y : N6, ∀ u : ↥(commSpace H ⊤),
        μ ((h : GLV V) u - u) = pf (β u) y := by
      intro h
      let θ : ↥(commSpace H ⊤) →+ ZMod 2 :=
        ((μ.comp (((h : GLV V) : V →ₗ[ZMod 2] V) - LinearMap.id)).comp
          (commSpace H ⊤).subtype).toAddMonoidHom
      have hθ : ∀ u : ↥(commSpace H ⊤), θ u = μ ((h : GLV V) u - u) := fun u => rfl
      obtain ⟨y, hy⟩ := exists_pf_of_ker β hβ θ fun w hw => by
        have hw' : (w : V) ∈ fixedSpace H := (hkerpt w).1 hw
        rw [AddMonoidHom.mem_ker, hθ, hw' h h.2, sub_self, map_zero]
      exact ⟨y, fun u => (hθ u).symm.trans (hy u)⟩
    choose y hy using hy
    have hcoc : ∀ g h : ↥H, y (g * h) = act (φ h)⁻¹ (y g) + y h := by
      intro g h
      apply eq_of_pf_eq
      intro x
      obtain ⟨u, rfl⟩ := hβ x
      have e1 : ((g * h : ↥H) : GLV V) u - u =
          ((g : GLV V) ((h : GLV V) u) - (h : GLV V) u) + ((h : GLV V) u - u) := by
        simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
        abel
      have h2 : μ ((g : GLV V) ((h : GLV V) u) - (h : GLV V) u) =
          pf (β ⟨(h : GLV V) u, hinv h h.2 u u.2⟩) (y g) := hy g ⟨_, hinv h h.2 u u.2⟩
      rw [← hy (g * h) u, e1, map_add, h2, hy h u, hβh h u, pf_add_right, pf_act]
    obtain ⟨a, ha⟩ := h1OmegaMinusSix_holds (fun x => y (φ.symm x⁻¹)) fun x x' => by
      show y (φ.symm (x * x')⁻¹) = y (φ.symm x⁻¹) + act x (y (φ.symm x'⁻¹))
      rw [_root_.mul_inv_rev, map_mul, hcoc, MulEquiv.apply_symm_apply, inv_inv, add_comm]
    have hya : ∀ h : ↥H, y h = act (φ h)⁻¹ a - a := by
      intro h
      have h1 : y (φ.symm ((φ h)⁻¹)⁻¹) = act (φ h)⁻¹ a - a := ha (φ h)⁻¹
      rwa [inv_inv, MulEquiv.symm_apply_apply] at h1
    let M : ↥(commSpace H ⊤) →+ ZMod 2 :=
      AddMonoidHom.mk' (fun u => μ u - pf (β u) a) fun u u' => by
        rw [Submodule.coe_add, map_add, map_add, pf_add_left]
        ring
    have hM : ∀ u : ↥(commSpace H ⊤), M u = μ u - pf (β u) a := fun u => rfl
    have hMinv : ∀ (h : ↥H) (u : ↥(commSpace H ⊤)), M ⟨(h : GLV V) u, hinv h h.2 u u.2⟩ = M u := by
      intro h u
      have h1 : μ ((h : GLV V) u) - μ u = pf (β u) (y h) := by
        rw [← map_sub]
        exact hy h u
      rw [hya h, pf_sub_right, ← pf_act, ← hβh h u] at h1
      rw [hM, hM]
      linear_combination h1
    have hM0 : ∀ u : ↥(commSpace H ⊤), (∃ h ∈ H, ∃ v : V, (u : V) = h v - v) → M u = 0 := by
      rintro u ⟨h, hh, v, huv⟩
      have hu : u = ⟨h v - v, sub_mem_commSpace hh Submodule.mem_top⟩ := Subtype.ext huv
      rw [hu]
      refine addHom_eq_zero_of_equiv φ
        (fun k : ↥H => M ⟨(k : GLV V) v - v, sub_mem_commSpace k.2 Submodule.mem_top⟩)
        (fun g k => ?_) ⟨h, hh⟩
      have e : (⟨((g * k : ↥H) : GLV V) v - v, sub_mem_commSpace (g * k).2 Submodule.mem_top⟩ :
          ↥(commSpace H ⊤)) =
          ⟨(g : GLV V) ((k : GLV V) v - v),
              hinv g g.2 _ (sub_mem_commSpace k.2 Submodule.mem_top)⟩ +
            ⟨(g : GLV V) v - v, sub_mem_commSpace g.2 Submodule.mem_top⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, LinearEquiv.mul_apply, Submodule.coe_add, map_sub]
        abel
      show M ⟨((g * k : ↥H) : GLV V) v - v, _⟩ = M ⟨(g : GLV V) v - v, _⟩ + M ⟨(k : GLV V) v - v, _⟩
      rw [e, map_add, hMinv g ⟨_, sub_mem_commSpace k.2 Submodule.mem_top⟩, add_comm]
    have hMc := eq_zero_of_forall_sub M hM0 ⟨c, hcU⟩
    have hβc : β ⟨c, hcU⟩ = 0 := (hkerpt ⟨c, hcU⟩).2 hcF
    rw [hM, hβc, pf_zero_left, sub_zero] at hMc
    exact hMc
  have hcod : ∀ v : V, ∃ u ∈ commSpace H ⊤, v - u ∈ fixedSpace H := by
    intro v
    have hact : ∀ (ℓ : ↥H) (w w' : ↥(commSpace H ⊤)), (w' : V) = (ℓ : GLV V) w →
        β w' = act (φ.toMonoidHom ℓ) (β w) := fun ℓ w w' h => hequiv ℓ w w' h
    obtain ⟨a, ha⟩ := h1OmegaMinusSix_holds (fun x => L13Aux.cocy β v (φ.symm x)) fun x x' => by
      show L13Aux.cocy β v (φ.symm (x * x')) =
        L13Aux.cocy β v (φ.symm x) + act x (L13Aux.cocy β v (φ.symm x'))
      rw [map_mul, L13Aux.cocy_mul φ.toMonoidHom β act hact v]
      simp only [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    obtain ⟨u, hu, hY⟩ := L13Aux.exists_sub_mem_of_cobound φ.toMonoidHom β act hact hkerpt hβ v ⊤
      a fun ℓ _ => by
        have h1 : L13Aux.cocy β v (φ.symm (φ ℓ)) = act (φ ℓ) a - a := ha (φ ℓ)
        rw [MulEquiv.symm_apply_apply] at h1
        exact h1
    refine ⟨u, hu, fun k hk => ?_⟩
    have h0 := hdisj _ (hsub k hk (v - u)) (hY ⟨k, hk⟩ (Subgroup.mem_top _))
    exact sub_eq_zero.mp h0
  refine ⟨Submodule.disjoint_def.mpr hdisj, codisjoint_iff.mpr ?_⟩
  rw [Submodule.eq_top_iff']
  intro v
  obtain ⟨u, hu, hvu⟩ := hcod v
  exact Submodule.mem_sup.mpr ⟨u, hu, v - u, hvu, by abel⟩

end CFSG.CGT.Foote82

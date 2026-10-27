module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ARemXB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AL47A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

@[expose] def ctxYt (t tau x₁ x₂ : G) : Subgroup G :=
  closure {t, (x₁ * x₂) ^ 2, x₁ ^ 2, tau * (x₁ * x₂)}

private lemma y_mem_baseGrp (x₁ x₂ : G) : x₁ ^ 2 ∈ baseGrp x₁ x₂ := by
  rw [baseGrp]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2

private lemma z_mem_baseGrp (x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ baseGrp x₁ x₂ := by
  rw [baseGrp]
  exact Subgroup.pow_mem _
    (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) 2

private lemma x1x2_mem_baseGrp (x₁ x₂ : G) : x₁ * x₂ ∈ baseGrp x₁ x₂ :=
  Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private lemma x1x2_mem_m12Grp (x₁ x₂ lam tau : G) : x₁ * x₂ ∈ m12Grp x₁ x₂ lam tau :=
  Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

private lemma baseGrp_le_wreathGrp (x₁ x₂ lam : G) : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
  rw [baseGrp, wreathGrp]
  refine Subgroup.closure_mono ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
  rcases ha with rfl | rfl <;> simp

private lemma wreathGrp_le_S (h : Ctx t L S x₁ x₂ lam rho tau) : wreathGrp x₁ x₂ lam ≤ S :=
  h.inf_eq ▸ inf_le_left

private lemma baseGrp_le_S (h : Ctx t L S x₁ x₂ lam rho tau) : baseGrp x₁ x₂ ≤ S :=
  (baseGrp_le_wreathGrp x₁ x₂ lam).trans (wreathGrp_le_S h)

private lemma t_mem_ctxX (t tau x₁ x₂ : G) : t ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]
  exact Subgroup.subset_closure (by simp)

private lemma t_mem_ctxE (t x₁ x₂ : G) : t ∈ ctxE t x₁ x₂ := by
  rw [ctxE]
  exact Subgroup.subset_closure (by simp)

private lemma y_mem_ctxE (t x₁ x₂ : G) : x₁ ^ 2 ∈ ctxE t x₁ x₂ := by
  rw [ctxE]
  exact Subgroup.subset_closure (by simp)

private lemma z_mem_ctxE (t x₁ x₂ : G) : (x₁ * x₂) ^ 2 ∈ ctxE t x₁ x₂ := by
  rw [ctxE]
  exact Subgroup.subset_closure (by simp)

private lemma t_commute_tau (h : Ctx t L S x₁ x₂ lam rho tau) : Commute t tau :=
  (mem_invCent_iff.mp (h.le_invCent h.tau_mem)).symm

private lemma commute_t_of_mem_S (h : Ctx t L S x₁ x₂ lam rho tau) {g : G} (hg : g ∈ S) :
    Commute t g :=
  (mem_invCent_iff.mp (h.le_invCent hg)).symm

private lemma x1x2_mem_S (h : Ctx t L S x₁ x₂ lam rho tau) : x₁ * x₂ ∈ S :=
  m12Grp_le_S h (x1x2_mem_m12Grp x₁ x₂ lam tau)

private lemma tau_mem_ctxX (t tau x₁ x₂ : G) : tau ∈ ctxX t tau x₁ x₂ := by
  rw [ctxX]
  exact Subgroup.subset_closure (by simp)

private lemma commute_y_tau (h : Ctx t L S x₁ x₂ lam rho tau) : Commute (x₁ ^ 2) tau :=
  show x₁ ^ 2 * tau = tau * x₁ ^ 2 from (tau_commute_y h).symm

private lemma commute_z_tau (h : Ctx t L S x₁ x₂ lam rho tau) :
    Commute ((x₁ * x₂) ^ 2) tau :=
  show (x₁ * x₂) ^ 2 * tau = tau * (x₁ * x₂) ^ 2 from (tau_commute_z h).symm

private lemma baseGrp_commute (h : Ctx t L S x₁ x₂ lam rho tau) {a b : G}
    (ha : a ∈ baseGrp x₁ x₂) (hb : b ∈ baseGrp x₁ x₂) : Commute a b := by
  haveI : IsMulCommutative (baseGrp x₁ x₂) := (h.wreath.baseGrp_eq).1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : baseGrp x₁ x₂) ⟨b, hb⟩)

private lemma tau_conj_x1x2_of (h : Ctx t L S x₁ x₂ lam rho tau) :
    tau * (x₁ * x₂) * tau⁻¹ = (x₁ * x₂)⁻¹ := by
  have hcomm_inv : x₁⁻¹ * x₂⁻¹ = (x₁ * x₂)⁻¹ := by
    have := congrArg Inv.inv h.wreath.comm.symm
    simpa [mul_inv_rev] using this
  calc tau * (x₁ * x₂) * tau⁻¹
      = (tau * x₁ * tau⁻¹) * (tau * x₂ * tau⁻¹) := by group
    _ = x₁⁻¹ * x₂⁻¹ := by rw [h.tau_x₁, h.tau_x₂]
    _ = (x₁ * x₂)⁻¹ := hcomm_inv

private lemma x1x2_tau_sq (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    (tau * (x₁ * x₂)) * (tau * (x₁ * x₂)) = 1 := by
  have hconj := tau_conj_x1x2_of h
  have hτ2 : tau * tau = 1 := by rw [← pow_two]; exact h44
  calc (tau * (x₁ * x₂)) * (tau * (x₁ * x₂))
      = (tau * (x₁ * x₂) * tau⁻¹) * (tau * tau) * (x₁ * x₂) := by group
    _ = (x₁ * x₂)⁻¹ * 1 * (x₁ * x₂) := by rw [hconj, hτ2]
    _ = 1 := by group

private lemma mem_zpowers_eq_one_or_eq {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro a b (rfl | rfl) (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        rintro a (rfl | rfl)
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

private lemma closure_gen_eq_ctxX (t tau x₁ x₂ : G) :
    closure ({t, (x₁ * x₂) ^ 2, x₁ ^ 2, tau} : Set G) = ctxX t tau x₁ x₂ := by
  rw [ctxX]
  congr 1
  ext g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem isE16In_ctxX (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    IsE16In S (ctxX t tau x₁ x₂) := by
  obtain ⟨hea, hcard⟩ := ctxX_elemAbelian_of h h44
  refine ⟨?_, hea, hcard⟩
  rw [ctxX]
  refine (Subgroup.closure_le (K := S)).mpr ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg1 | hg2 | hg3 | hg4
  · rw [hg1, h.S_eq]
    exact Subgroup.mem_sup_left h.hyp.mem_twoCore
  · rw [hg2]
    exact h.tau_mem
  · rw [hg3]
    exact baseGrp_le_S h (y_mem_baseGrp x₁ x₂)
  · rw [hg4]
    exact baseGrp_le_S h (z_mem_baseGrp x₁ x₂)

theorem normalIn_ctxX (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) : NormalIn (ctxX t tau x₁ x₂) S := by
  have hXleS : ctxX t tau x₁ x₂ ≤ S := (isE16In_ctxX h h44).1
  have hN : S ≤ normalizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) := by
    have hnorm := normalizer_X_of h h43 h44
    have hm12H : m12Grp x₁ x₂ lam tau ≤ invCent t := (m12Grp_le_S h).trans h.le_invCent
    have hm12W : m12Grp x₁ x₂ lam tau ≤ ctxW t x₁ x₂ ⊔ closure {tau, rho, lam} := by
      rw [m12Grp]
      refine (Subgroup.closure_le (K := ctxW t x₁ x₂ ⊔ closure {tau, rho, lam})).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure (by simp)))
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure (by simp))
    have hm12ctxM : m12Grp x₁ x₂ lam tau ≤ ctxM t tau x₁ x₂ := by
      have : m12Grp x₁ x₂ lam tau ≤ invCent t ⊓ ctxM t tau x₁ x₂ := by
        rw [hnorm]
        exact hm12W
      exact this.trans inf_le_right
    have hzp : zpowers t ≤ normalizer ((ctxX t tau x₁ x₂ : Subgroup G) : Set G) :=
      (Subgroup.zpowers_le.mpr (t_mem_ctxX t tau x₁ x₂)).trans
        (Subgroup.le_normalizer (H := ctxX t tau x₁ x₂))
    rw [(S_eq_prod_of h h43 h44).1]
    exact sup_le hzp (by simpa only [ctxM] using hm12ctxM)
  refine ⟨hXleS, ?_⟩
  intro g hg k hk
  have hgN := hN hg
  rw [Subgroup.mem_set_normalizer_iff] at hgN
  exact (hgN k).mp hk

theorem ctxX_ne_ctxYt (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) :
    ctxX t tau x₁ x₂ ≠ ctxYt t tau x₁ x₂ := by
  intro heq
  have hw : tau * (x₁ * x₂) ∈ ctxYt t tau x₁ x₂ := by
    rw [ctxYt]
    exact Subgroup.subset_closure (by simp)
  rw [← heq] at hw
  have htau : tau ∈ ctxX t tau x₁ x₂ := tau_mem_ctxX t tau x₁ x₂
  have hxy : x₁ * x₂ ∈ ctxX t tau x₁ x₂ := by
    have h := Subgroup.mul_mem (ctxX t tau x₁ x₂) (Subgroup.inv_mem _ htau) hw
    rwa [inv_mul_cancel_left] at h
  have hsq : (x₁ * x₂) ^ 2 = 1 := (ctxX_elemAbelian_of h h44).1.2 (x₁ * x₂) hxy
  exact (z_mul_self_ne_one h.toCtx0).2 hsq

theorem mem_ctxYt_cases (h : Ctx t L S x₁ x₂ lam rho tau) (h44 : tau ^ 2 = 1) {g : G}
    (hg : g ∈ ctxYt t tau x₁ x₂) :
    g ∈ ctxE t x₁ x₂ ∨ ∃ a ∈ ctxE t x₁ x₂, g = tau * (x₁ * x₂) * a := by
  let w : G := tau * (x₁ * x₂)
  have hw_sq : w * w = 1 := x1x2_tau_sq h h44
  have hYeq : ctxYt t tau x₁ x₂ = ctxE t x₁ x₂ ⊔ zpowers w := by
    apply le_antisymm
    · rw [ctxYt]
      refine (Subgroup.closure_le (K := ctxE t x₁ x₂ ⊔ zpowers w)).mpr ?_
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with ha1 | ha2 | ha3 | ha4
      · rw [ha1]; exact Subgroup.mem_sup_left (t_mem_ctxE t x₁ x₂)
      · rw [ha2]; exact Subgroup.mem_sup_left (z_mem_ctxE t x₁ x₂)
      · rw [ha3]; exact Subgroup.mem_sup_left (y_mem_ctxE t x₁ x₂)
      · rw [ha4]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    · refine sup_le ?_ ?_
      · rw [ctxE]
        refine (Subgroup.closure_le (K := ctxYt t tau x₁ x₂)).mpr ?_
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with ha1 | ha2 | ha3
        · rw [ha1, ctxYt]; exact Subgroup.subset_closure (by simp)
        · rw [ha2, ctxYt]; exact Subgroup.subset_closure (by simp)
        · rw [ha3, ctxYt]; exact Subgroup.subset_closure (by simp)
      · rw [Subgroup.zpowers_le, ctxYt]
        exact Subgroup.subset_closure (by simp [w])
  have hcommE : ∀ a ∈ ctxE t x₁ x₂, Commute a w := by
    intro a ha
    rw [ctxE] at ha
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with hx1 | hx2 | hx3
        · rw [hx1]
          exact (t_commute_tau h).mul_right (commute_t_of_mem_S h (x1x2_mem_S h))
        · rw [hx2]
          exact (commute_y_tau h).mul_right
            (baseGrp_commute h (y_mem_baseGrp x₁ x₂) (x1x2_mem_baseGrp x₁ x₂))
        · rw [hx3]
          exact (commute_z_tau h).mul_right
            (baseGrp_commute h (z_mem_baseGrp x₁ x₂) (x1x2_mem_baseGrp x₁ x₂))
    | one => exact Commute.one_left w
    | mul x y _ _ ihx ihy => exact ihx.mul_left ihy
    | inv x _ ihx => exact ihx.inv_left
  have hcomm : ∀ a ∈ ctxE t x₁ x₂, ∀ b ∈ zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (hcommE a ha).zpow_right k |>.eq
  rw [hYeq] at hg
  obtain ⟨a, ha, b, hb, hgab⟩ := (mem_sup_iff_of_commute hcomm).mp hg
  rcases mem_zpowers_eq_one_or_eq hw_sq hb with hb1 | hbw
  · left
    rw [hgab, hb1, mul_one]
    exact ha
  · right
    refine ⟨a, ha, ?_⟩
    rw [hgab, hbw]
    exact hcomm a ha w (Subgroup.mem_zpowers w)

theorem conj_ctxX_cases (h : Ctx t L S x₁ x₂ lam rho tau) (h43 : twoCore t = zpowers t)
    (h44 : tau ^ 2 = 1) {α : G} (hα : α ∈ normalizer (S : Set G)) :
    (∀ x : G, x ∈ ctxX t tau x₁ x₂ ↔ α * x * α⁻¹ ∈ ctxX t tau x₁ x₂) ∨
    (∀ x : G, x ∈ ctxX t tau x₁ x₂ ↔ α * x * α⁻¹ ∈ ctxYt t tau x₁ x₂) := by
  have hXnormal : NormalIn (ctxX t tau x₁ x₂) S := normalIn_ctxX h h43 h44
  let X' : Subgroup G := (ctxX t tau x₁ x₂).map (MulAut.conj α).toMonoidHom
  have hX'leS : X' ≤ S := by
    intro y hy
    dsimp only [X'] at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxS : x ∈ S := (isE16In_ctxX h h44).1 hx
    have hmem := (Subgroup.mem_set_normalizer_iff.mp hα x).mp hxS
    show (MulAut.conj α) x ∈ S
    rw [MulAut.conj_apply]
    exact hmem
  have hX'ea : CFSG.Open.IsElemAbelian 2 X' := by
    dsimp only [X']
    exact (ctxX_elemAbelian_of h h44).1.map (MulAut.conj α).toMonoidHom
  have hX'card : Nat.card X' = 16 := by
    dsimp only [X']
    rw [Subgroup.card_map_of_injective (K := ctxX t tau x₁ x₂)
      (f := (MulAut.conj α).toMonoidHom) (MulAut.conj α).injective,
      (ctxX_elemAbelian_of h h44).2]
  have hX'normal : NormalIn X' S := by
    refine ⟨hX'leS, ?_⟩
    intro g hg k hk
    dsimp only [X'] at hk ⊢
    rw [Subgroup.mem_map] at hk
    obtain ⟨x, hx, rfl⟩ := hk
    refine Subgroup.mem_map.mpr
      ⟨(MulAut.conj α).symm g * x * ((MulAut.conj α).symm g)⁻¹, ?_, ?_⟩
    · have hgS : (MulAut.conj α).symm g ∈ S := by
        have := (Subgroup.mem_set_normalizer_iff''.mp hα g).mp hg
        rw [MulAut.conj_symm_apply]
        exact this
      exact hXnormal.2 _ hgS x hx
    · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hcases := lemma4_7b_of h h43 h44 X' ⟨hX'leS, hX'ea, hX'card⟩ hX'normal
  have hmem : ∀ x : G, (MulAut.conj α) x ∈ X' ↔ x ∈ ctxX t tau x₁ x₂ := by
    intro x
    dsimp only [X']
    rw [Subgroup.mem_map_equiv (f := MulAut.conj α) (K := ctxX t tau x₁ x₂)]
    rw [MulEquiv.symm_apply_apply]
  rcases hcases with hcase | hcase
  · left
    rw [closure_gen_eq_ctxX] at hcase
    intro x
    constructor
    · intro hx
      have h := (hmem x).mpr hx
      rw [hcase] at h
      simpa only [MulAut.conj_apply] using h
    · intro hx
      have h2 : (MulAut.conj α) x ∈ X' := by
        rw [hcase]
        simpa only [MulAut.conj_apply] using hx
      exact (hmem x).mp h2
  · right
    change X' = ctxYt t tau x₁ x₂ at hcase
    intro x
    constructor
    · intro hx
      have h := (hmem x).mpr hx
      rw [hcase] at h
      simpa only [MulAut.conj_apply] using h
    · intro hx
      have h2 : (MulAut.conj α) x ∈ X' := by
        rw [hcase]
        simpa only [MulAut.conj_apply] using hx
      exact (hmem x).mp h2

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

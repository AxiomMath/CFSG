module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EDefs
public import CFSG.GH74.GLS.IVK.L2.BorelMatrices
public import CFSG.GH74.GLS.IVK.L2.BorelSylow
public import CFSG.Adapters.SpecialLinearPerfect

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter CFSG.PSL2Table
  CFSG.GH74.GLS.IVK.L2Borel
open scoped MatrixGroups

theorem l46e_mk_unip_inj {F : Type} [Field F] {s t : F} (h : mk (unip s) = mk (unip t)) : s = t := by
  rw [mk_eq_mk_iff] at h
  rcases h with h | h
  · have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simpa using h01.symm
  · have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
    have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h
    simp only [coe_unip, neg_apply_SL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one] at h00 h01
    have h2 : (2 : F) = 0 := by linear_combination h00
    linear_combination (-1 : F) * h01 + s * h2

theorem l46e_psl2FieldAut_mk_unip {F : Type} [Field F] (σ : F ≃+* F) (t : F) :
    psl2FieldAut F σ (mk (unip t)) = mk (unip (σ t)) := by
  show psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center _) (unip t)) = _
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unip]

theorem l46e_aut_fix_unipotent {F : Type} [Field F] [Finite F] (α : MulAut (PSL2 F))
    (hα : ∀ x ∈ unipotent F, α x = x) : ∃ s : F, α = MulAut.conj (mk (unip s)) := by
  obtain ⟨γ, hγ⟩ := semilinearAction_surjective F α
  have hαeq : ∀ x, α x = pglAction F γ.left (psl2FieldAut F γ.right x) := by
    intro x
    rw [← hγ, ← SemidirectProduct.inl_left_mul_inr_right γ, map_mul, semilinearAction_inl,
      semilinearAction_inr]
    simp
  have h1 : γ.left * Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip (1 : F))) =
      Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip (1 : F))) * γ.left := by
    have h := hα (mk (unip 1)) (mk_unip_mem_unipotent 1)
    rw [hαeq] at h
    have h2 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
    rw [toPGL_pglAction, l46e_psl2FieldAut_mk_unip, map_one] at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2
  obtain ⟨s, hs⟩ := exists_eq_toPGL_of_commute one_ne_zero h1
  have hconj : pglAction F γ.left = MulAut.conj (mk (unip s)) := by
    rw [hs, pglAction_toPGL]
  have hσ : γ.right = 1 := by
    apply RingEquiv.ext
    intro t
    have h := hα (mk (unip t)) (mk_unip_mem_unipotent t)
    rw [hαeq, hconj, l46e_psl2FieldAut_mk_unip, MulAut.conj_apply,
      unipotent_mul_comm (mk_unip_mem_unipotent s) (mk_unip_mem_unipotent _),
      mul_inv_cancel_right] at h
    exact l46e_mk_unip_inj h
  refine ⟨s, ?_⟩
  ext x
  rw [hαeq, hconj, hσ]
  simp

theorem l46e_aut_fix_sylow {F : Type} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ n) (W : Sylow p (PSL2 F)) (α : MulAut (PSL2 F))
    (hα : ∀ x ∈ (W : Subgroup (PSL2 F)), α x = x) :
    ∃ w ∈ (W : Subgroup (PSL2 F)), α = MulAut.conj w := by
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hF W
  have hmem : ∀ x ∈ unipotent F, c * x * c⁻¹ ∈ (W : Subgroup (PSL2 F)) := by
    intro x hx
    rw [hc]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  obtain ⟨s, hs⟩ := l46e_aut_fix_unipotent (MulAut.conj c⁻¹ * α * MulAut.conj c) (by
    intro x hx
    have h1 := hα _ (hmem x hx)
    simp only [MulAut.mul_apply, MulAut.conj_apply, h1]
    group)
  refine ⟨c * mk (unip s) * c⁻¹, ?_, ?_⟩
  · rw [hc]
    exact ⟨mk (unip s), mk_unip_mem_unipotent s, by simp [MulAut.conj_apply]⟩
  · ext x
    have h := congrArg (fun β : MulAut (PSL2 F) => β (c⁻¹ * x * c)) hs
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h ⊢
    have h2 : α x = c * (mk (unip s) * (c⁻¹ * x * c) * (mk (unip s))⁻¹) * c⁻¹ := by
      rw [← h]
      group
    rw [h2]
    group

theorem l46e_aut_eq_one_of_perfect {G : Type*} [Group G] [Group.IsPerfect G] (θ : MulAut G)
    (h : ∀ k : G, (θ k)⁻¹ * k ∈ Subgroup.center G) : θ = 1 := by
  let f : G →* Subgroup.center G :=
    { toFun := fun k => ⟨(θ k)⁻¹ * k, h k⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        have hc := Subgroup.mem_center_iff.1 (h a) (θ b)⁻¹
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        calc (θ b)⁻¹ * (θ a)⁻¹ * (a * b) = (θ b)⁻¹ * ((θ a)⁻¹ * a) * b := by group
          _ = ((θ a)⁻¹ * a) * (θ b)⁻¹ * b := by rw [hc]
          _ = ((θ a)⁻¹ * a) * ((θ b)⁻¹ * b) := by group }
  have hker : f.ker = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := G)]
    exact Abelianization.commutator_subset_ker f
  ext k
  have hk : f k = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top k)
  have hk' : (θ k)⁻¹ * k = 1 := congrArg Subtype.val hk
  simpa using inv_mul_eq_one.1 hk'

theorem l46e_sl2_aut_one {F : Type} [Field F] [Finite F] {p n : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p ^ n) (h4 : 4 ≤ Nat.card F)
    (W : Sylow p (Matrix.SpecialLinearGroup (Fin 2) F))
    (θ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F))
    (hθ : ∀ x ∈ (W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), θ x = x)
    (hord : Nat.Coprime (orderOf θ) p) : θ = 1 := by
  classical
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
  have hZ : (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)).map θ.toMonoidHom =
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    have hc : ∀ ϕ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F),
        ∀ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F),
        ϕ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      intro ϕ z hz
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨g', rfl⟩ := ϕ.surjective g
      rw [← map_mul, ← map_mul, hz g']
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hc θ z hz
    · intro hx
      exact ⟨θ⁻¹ x, hc θ⁻¹ x hx, by simp⟩
  let θb : PSL2 F ≃* PSL2 F :=
    QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) θ hZ
  have hθb : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F,
      θb (QuotientGroup.mk k) = QuotientGroup.mk (θ k) := fun k =>
    QuotientGroup.congr_mk _ _ _ _ k
  let π : Matrix.SpecialLinearGroup (Fin 2) F →* PSL2 F :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let Wb : Sylow p (PSL2 F) := Sylow.mapSurjective hπ W
  have hWb : (Wb : Subgroup (PSL2 F)) = (W : Subgroup _).map π := Sylow.coe_mapSurjective hπ W
  have hWbfix : ∀ x ∈ (Wb : Subgroup (PSL2 F)), θb x = x := by
    intro x hx
    rw [hWb] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    show θb (QuotientGroup.mk w) = QuotientGroup.mk w
    rw [hθb, hθ w hw]
  obtain ⟨wb, hwb, hθwb⟩ := l46e_aut_fix_sylow hF Wb θb hWbfix
  rw [hWb] at hwb
  obtain ⟨w, hw, rfl⟩ := hwb
  have hconj : ∀ k : Matrix.SpecialLinearGroup (Fin 2) F,
      π (θ k) = π w * π k * (π w)⁻¹ := by
    intro k
    have h1 := hθb k
    rw [hθwb, MulAut.conj_apply] at h1
    exact h1.symm
  let θ₂ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.conj w⁻¹ * θ
  have hθ₂ : θ₂ = 1 := by
    apply l46e_aut_eq_one_of_perfect
    intro k
    have e1 : θ₂ k = w⁻¹ * θ k * w := by
      simp [θ₂]
    have h1 : π (θ₂ k) = π k := by
      rw [e1, map_mul, map_mul, map_inv, hconj k]
      group
    exact QuotientGroup.eq.1 h1
  have hθw : θ = MulAut.conj w := by
    have h1 : θ = (MulAut.conj w⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hθ₂
    rw [h1, ← map_inv, inv_inv]
  obtain ⟨k, hk⟩ := (W.isPGroup').exists_orderOf_dvd_pow (⟨w, hw⟩ : ↥(W : Subgroup _))
  have h2 : orderOf θ ∣ p ^ k := by
    rw [hθw]
    refine (orderOf_map_dvd MulAut.conj w).trans ?_
    rw [← Subgroup.orderOf_mk w hw]
    exact hk
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hord.pow_right k) h2)

theorem autFactB : AutFactB := by
  classical
  intro Y _ _ p X hp hC y hy hcop
  obtain ⟨n, hn, ⟨F, _, _, hFcard, ⟨φ⟩⟩, Q, hQ⟩ := hC
  have : Fact p.Prime := ⟨hp⟩
  have hnormal : (ncl X).Normal := Subgroup.normalClosure_normal
  let ψ : ↥(ncl X) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm
  let θ : MulAut ↥(ncl X) := MulAut.conjNormal y
  let θ₁ : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr ψ θ
  let W : Sylow p (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Sylow.mapSurjective (f := ψ.toMonoidHom) ψ.surjective Q
  have hW : (W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) =
      (Q : Subgroup ↥(ncl X)).map ψ.toMonoidHom := Sylow.coe_mapSurjective _ Q
  have hθq : ∀ q ∈ (Q : Subgroup ↥(ncl X)), θ q = q := by
    intro q hq
    have hqX : (q : Y) ∈ X := by
      have h0 : (q : Y) ∈ Subgroup.map (ncl X).subtype (Q : Subgroup ↥(ncl X)) := ⟨q, hq, rfl⟩
      rw [hQ] at h0
      exact h0
    apply Subtype.ext
    have h1 := Subgroup.mem_centralizer_iff.1 hy (q : Y) hqX
    show y * (q : Y) * y⁻¹ = q
    rw [← h1]
    group
  have hfix : ∀ x ∈ (W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)), θ₁ x = x := by
    intro x hx
    rw [hW] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    show ψ (θ (ψ.symm (ψ q))) = ψ q
    rw [ψ.symm_apply_apply, hθq q hq]
  have hord : Nat.Coprime (orderOf θ₁) p := by
    have h1 : orderOf θ₁ = orderOf θ :=
      orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective θ
    have h2 : orderOf θ ∣ orderOf y := orderOf_map_dvd (MulAut.conjNormal : Y →* MulAut ↥(ncl X)) y
    rw [h1]
    exact Nat.Coprime.coprime_dvd_left h2 hcop
  have h4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    omega
  have hθ₁ : θ₁ = 1 :=
    l46e_sl2_aut_one hFcard h4 W θ₁ hfix hord
  have hθ : θ = 1 := by
    apply (MulAut.congr ψ).injective
    rw [map_one]
    exact hθ₁
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hθ ⟨g, hg⟩)
  have h2 : y * g * y⁻¹ = g := h1
  calc g * y = (y * g * y⁻¹) * y := by rw [h2]
    _ = y * g := by group

end CFSG.GH74.GLS.Stage2.Signalizer.L46E

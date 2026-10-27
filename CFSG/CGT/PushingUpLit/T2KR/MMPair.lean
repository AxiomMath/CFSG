module

public import CFSG.CGT.PushingUpLit.T2KR.MMEquiv

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall
open scoped commutatorElement LinearAlgebra.Projectivization

theorem fix_of_rel {F : Type} [Field F] {σ : F ≃+* F} {μ δ s s₀ : F} (hμ : μ ≠ 0) (hs₀ : s₀ ≠ 0)
    (h : σ s * μ = s * δ) (h₀ : σ s₀ * μ = s₀ * δ) : σ (s / s₀) = s / s₀ := by
  have hσs₀ : σ s₀ ≠ 0 := fun h0 => hs₀ (σ.injective (by rw [h0, map_zero]))
  rw [map_div₀, div_eq_div_iff hσs₀ hs₀]
  have : (σ s * s₀ - s * σ s₀) * μ = 0 := by linear_combination s₀ * h - s * h₀
  have := (mul_eq_zero.1 this).resolve_right hμ
  linear_combination this

theorem unip_commute_rel {F : Type} [Field F] {σ : F ≃+* F} (B : Equiv.Perm (Fin 2 → F))
    (hadd : ∀ w w', B (w + w') = B w + B w') (hB : IsSemilinearWith B σ) {s : F}
    (hcomm : B * slPerm F (CFSG.SL2MinimalFaithful.unipotent s) =
      slPerm F (CFSG.SL2MinimalFaithful.unipotent s) * B) :
    s * B ![1, 0] 1 = 0 ∧ σ s * B ![1, 0] 0 = s * B ![0, 1] 1 := by
  have h0 := congrArg (fun p : Equiv.Perm (Fin 2 → F) => p ![1, 0]) hcomm
  have h1 := congrArg (fun p : Equiv.Perm (Fin 2 → F) => p ![0, 1]) hcomm
  simp only [Equiv.Perm.mul_apply, slPerm_apply, smul_unipotent_vec] at h0 h1
  have e0 : (![(![1, 0] : Fin 2 → F) 0 + s * (![1, 0] : Fin 2 → F) 1, (![1, 0] : Fin 2 → F) 1] :
      Fin 2 → F) = ![1, 0] := by simp
  have e1 : (![(![0, 1] : Fin 2 → F) 0 + s * (![0, 1] : Fin 2 → F) 1, (![0, 1] : Fin 2 → F) 1] :
      Fin 2 → F) = ![0, 1] + s • ![1, 0] := by
    ext i; fin_cases i <;> simp
  rw [e0] at h0
  rw [e1, hadd, hB] at h1
  have h0' := congrFun h0 0
  have h1' := congrFun h1 0
  simp at h0' h1'
  refine ⟨?_, ?_⟩
  · rcases h0' with h | h <;> simp [h]
  · linear_combination h1'

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem twist_semilinear (x₀ : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) (m : ↥M) :
    IsSemilinearWith ((H.twist x₀).actHom m) (H.chi m) := by
  rw [H.twist_actHom]
  have h1 : IsSemilinearWith (slPerm (Fq n) x₀⁻¹) (1 : Fq n ≃+* Fq n) := by
    rw [slPerm_eq_semilinPerm]
    exact semilinPerm_isSemilinear _ _
  have h2 : IsSemilinearWith (slPerm (Fq n) x₀) (1 : Fq n ≃+* Fq n) := by
    rw [slPerm_eq_semilinPerm]
    exact semilinPerm_isSemilinear _ _
  have := (h1.mul (H.isSemilinear_chi m)).mul h2
  simpa using this

include H in
theorem relIndex_sq_le_card_of_commute (X : Subgroup G) (hX : X ≤ L ⊔ QM L M)
    (hX2 : ∀ x ∈ X, x * x = 1) {b : ↥M} (hb : b * b = 1) (hχ : H.chi b ≠ 1)
    (hbX : ∀ x ∈ X, (b : G) * x = x * (b : G)) :
    (X ⊓ QM L M).relIndex X ^ 2 ≤ Nat.card (Fq n) := by
  classical
  obtain ⟨p, hp⟩ := H.exists_root_point X hX hX2
  obtain ⟨x₀, rfl⟩ := exists_smul_pt0 p
  have hρ' : ∀ x (hx : x ∈ X), (H.twist x₀).rho ⟨x, hX hx⟩ ∈
      rootGrp (pt0 : ℙ (Fq n) (Fin 2 → Fq n)) := by
    intro x hx
    rw [H.twist_rho]
    exact mem_rootGrp_smul_iff.1 (hp ⟨⟨x, hx⟩, rfl⟩)
  have hS : ∀ x (hx : x ∈ X), ∃ s : Fq n,
      (H.twist x₀).rho ⟨x, hX hx⟩ = CFSG.SL2MinimalFaithful.unipotent s := by
    intro x hx
    have := hρ' x hx
    rw [rootGrp_pt0] at this
    obtain ⟨t, ht⟩ := this
    exact ⟨Multiplicative.toAdd t, ht.symm⟩
  have hcomm : ∀ x (hx : x ∈ X), (H.twist x₀).actHom b * slPerm (Fq n) ((H.twist x₀).rho ⟨x, hX hx⟩) =
      slPerm (Fq n) ((H.twist x₀).rho ⟨x, hX hx⟩) * (H.twist x₀).actHom b := by
    intro x hx
    rw [(H.twist x₀).slPerm_rho, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hbX x hx)
  have hBσ := H.twist_semilinear x₀ b
  have hBadd := (H.twist x₀).actHom_add b
  have hσσ := H.chi_involution hb
  rw [(H.twist x₀).relIndex_eq_card_range X hX]
  have hq : 1 ≤ Nat.card (Fq n) := Nat.card_pos
  by_cases htriv : ∀ x (hx : x ∈ X), (H.twist x₀).rho ⟨x, hX hx⟩ = 1
  · have : ((H.twist x₀).rhoOn X hX).range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, rfl⟩
      exact htriv x x.2
    rw [this, Subgroup.card_bot]
    simpa using hq
  · push Not at htriv
    obtain ⟨x₁, hx₁, hne⟩ := htriv
    obtain ⟨s₀, hs₀⟩ := hS x₁ hx₁
    have hs₀ne : s₀ ≠ 0 := fun h => hne (by rw [hs₀, h, CFSG.SL2MinimalFaithful.unipotent_zero])
    obtain ⟨a₀, b₀⟩ := unip_commute_rel ((H.twist x₀).actHom b) hBadd hBσ (s := s₀)
      (by rw [← hs₀]; exact hcomm x₁ hx₁)
    have hv1 : (H.twist x₀).actHom b ![1, 0] 1 = 0 := (mul_eq_zero.1 a₀).resolve_left hs₀ne
    have hμ : (H.twist x₀).actHom b ![1, 0] 0 ≠ 0 := by
      intro h0
      have hz : (H.twist x₀).actHom b ![1, 0] = 0 := by
        funext i
        fin_cases i
        · exact h0
        · exact hv1
      have : (![1, 0] : Fin 2 → Fq n) = 0 :=
        ((H.twist x₀).actHom b).injective (hz.trans hBσ.map_zero.symm)
      have := congrFun this 0
      simp at this
    have hr : ∀ r : ↥((H.twist x₀).rhoOn X hX).range, ∃ s : Fq n,
        (r : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) = CFSG.SL2MinimalFaithful.unipotent s ∧
          H.chi b s * (H.twist x₀).actHom b ![1, 0] 0 =
            s * (H.twist x₀).actHom b ![0, 1] 1 := by
      rintro ⟨_, ⟨x, rfl⟩⟩
      obtain ⟨s, hs⟩ := hS x x.2
      refine ⟨s, hs, ?_⟩
      exact (unip_commute_rel ((H.twist x₀).actHom b) hBadd hBσ (s := s)
        (by rw [← hs]; exact hcomm x x.2)).2
    let f : ↥((H.twist x₀).rhoOn X hX).range → {t : Fq n // 1 * H.chi b t = t} := fun r =>
      ⟨Classical.choose (hr r) / s₀, by
        rw [one_mul]
        exact fix_of_rel hμ hs₀ne (Classical.choose_spec (hr r)).2 b₀⟩
    have hf : Function.Injective f := by
      intro r r' h
      have h1 : Classical.choose (hr r) / s₀ = Classical.choose (hr r') / s₀ :=
        congrArg Subtype.val h
      have h2 : Classical.choose (hr r) = Classical.choose (hr r') :=
        (div_left_inj' hs₀ne).1 h1
      apply Subtype.ext
      rw [(Classical.choose_spec (hr r)).1, (Classical.choose_spec (hr r')).1, h2]
    have hcard := Nat.card_le_card_of_injective f hf
    have hFix := card_fixed_twisted (H.chi b) hχ hσσ 1 (by rw [map_one, mul_one])
    calc Nat.card ((H.twist x₀).rhoOn X hX).range ^ 2
        ≤ Nat.card {t : Fq n // 1 * H.chi b t = t} ^ 2 := Nat.pow_le_pow_left hcard 2
      _ = Nat.card (Fq n) := hFix

include H in
theorem theta_one : H.theta (1 : ↥(QM L M)) = 0 := by
  have := (H.vco_mul 1 1).2
  rw [mul_one] at this
  linear_combination -this

include H in
theorem card_CV_pair_le {b : ↥M} (hb : b * b = 1) (hχ : H.chi b ≠ 1) {e : G}
    (he : e ∈ L ⊔ QM L M) (he2 : e * e = 1) (heQ : e ∉ QM L M)
    (hbe : (b : G) * e = e * (b : G)) :
    Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({(b : G), e} : Set G)) ^ 2 ≤ Nat.card (Fq n) := by
  classical
  have hz2 : ∀ x ∈ Subgroup.zpowers e, x * x = 1 := by
    rintro _ ⟨k, rfl⟩
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, he2, one_zpow]
  obtain ⟨p, hp⟩ := H.exists_root_point (Subgroup.zpowers e)
    ((Subgroup.zpowers_le).2 he) hz2
  have hρe : H.rho ⟨e, he⟩ ∈ rootGrp p := hp ⟨⟨e, Subgroup.mem_zpowers e⟩, rfl⟩
  have hρe1 : H.rho ⟨e, he⟩ ≠ 1 := fun h => heQ ((H.rho_eq_one_iff ⟨e, he⟩).1 h)
  have hfixe : ∀ w, H.actHom ⟨e, H.LQ_le he⟩ w = w ↔ w ∈ p.submodule := H.fixed_iff hρe hρe1
  have hbeM : b * (⟨e, H.LQ_le he⟩ : ↥M) = ⟨e, H.LQ_le he⟩ * b := Subtype.ext hbe
  have hBe : ∀ w, H.actHom b (H.actHom ⟨e, H.LQ_le he⟩ w) = H.actHom ⟨e, H.LQ_le he⟩ (H.actHom b w) := by
    intro w
    have := congrArg (fun m : ↥M => H.actHom m w) hbeM
    simpa using this
  have hBmem : ∀ w ∈ p.submodule, H.actHom b w ∈ p.submodule := by
    intro w hw
    refine (hfixe _).1 ?_
    rw [← hBe, (hfixe w).2 hw]
  let β : ↥p.submodule →+ ↥p.submodule :=
    AddMonoidHom.mk' (fun w => ⟨H.actHom b w, hBmem w w.2⟩)
      (fun w w' => Subtype.ext (H.actHom_add b w w'))
  have hβ : ∀ (c : Fq n) (w : ↥p.submodule), β (c • w) = H.chi b c • β w :=
    fun c w => Subtype.ext (H.isSemilinear_chi b c w)
  have hββ : ∀ w, β (β w) = w := fun w => Subtype.ext (by
    have := congrArg (fun q : Equiv.Perm (Fin 2 → Fq n) => q (w : Fin 2 → Fq n)) (show H.actHom b * H.actHom b = 1 by
      rw [← map_mul, hb, map_one])
    exact this)
  have hdesc := card_eq_sq_card_fixed (W := ↥p.submodule) (H.chi b) hχ (H.chi_involution hb) β hβ hββ
  rw [Nat.card_congr (Equiv.refl _) |>.trans (card_submodule_line p)] at hdesc
  have hinj : Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({(b : G), e} : Set G)) ≤
      Nat.card {w : ↥p.submodule // β w = w} := by
    have hmem : ∀ u : ↥(blockU L ⊓ Subgroup.centralizer ({(b : G), e} : Set G)),
        H.D.ψe u.1 ∈ p.submodule ∧ H.actHom b (H.D.ψe u.1) = H.D.ψe u.1 := by
      intro u
      have hue : e * u.1 = u.1 * e :=
        Subgroup.mem_centralizer_iff.1 u.2.2 e (by simp)
      have hub : (b : G) * u.1 = u.1 * (b : G) :=
        Subgroup.mem_centralizer_iff.1 u.2.2 (b : G) (by simp)
      refine ⟨(hfixe _).1 ?_, ?_⟩
      · rw [H.actHom_apply, H.act_vec _ u.2.1]
        congr 1
        calc e * u.1 * e⁻¹ = (u.1 * e) * e⁻¹ := by rw [hue]
          _ = u.1 := by group
      · rw [H.actHom_apply, H.act_vec _ u.2.1]
        congr 1
        calc (b : G) * u.1 * (b : G)⁻¹ = (u.1 * (b : G)) * (b : G)⁻¹ := by rw [hub]
          _ = u.1 := by group
    refine Nat.card_le_card_of_injective (fun u => ⟨⟨H.D.ψe u.1, (hmem u).1⟩, Subtype.ext (hmem u).2⟩) ?_
    intro u u' h
    apply Subtype.ext
    exact H.ψe_injOn u.2.1 u'.2.1 (congrArg (fun z : {w : ↥p.submodule // β w = w} => (z.1 : Fin 2 → Fq n)) h)
  calc Nat.card ↥(blockU L ⊓ Subgroup.centralizer ({(b : G), e} : Set G)) ^ 2
      ≤ Nat.card {w : ↥p.submodule // β w = w} ^ 2 := Nat.pow_le_pow_left hinj 2
    _ = Nat.card (Fq n) := hdesc.symm

include H in
theorem card_centralizer_QM_pair_le {b : ↥M} (hb : b * b = 1) (hχ : H.chi b ≠ 1) {e : G}
    (he : e ∈ L ⊔ QM L M) (he2 : e * e = 1) (heQ : e ∉ QM L M)
    (hbe : (b : G) * e = e * (b : G)) :
    Nat.card ↥(QM L M ⊓ Subgroup.centralizer ({(b : G), e} : Set G)) ≤ Nat.card (Fq n) := by
  classical
  set S : Set G := {(b : G), e} with hS
  set C : Subgroup G := QM L M ⊓ Subgroup.centralizer S with hC
  let θC : ↥C →* Multiplicative (Fq n) :=
    { toFun := fun u => Multiplicative.ofAdd (H.theta ⟨u.1, u.2.1⟩)
      map_one' := by
        show Multiplicative.ofAdd (H.theta ⟨1, _⟩) = 1
        rw [← ofAdd_zero]
        exact congrArg Multiplicative.ofAdd H.theta_one
      map_mul' := fun u u' => by
        show Multiplicative.ofAdd (H.theta ⟨u.1 * u'.1, _⟩) = _
        rw [← ofAdd_add]
        exact congrArg Multiplicative.ofAdd (H.vco_mul ⟨u.1, u.2.1⟩ ⟨u'.1, u'.2.1⟩).2 }
  have hθ : ∀ u : ↥C, θC u = Multiplicative.ofAdd (H.theta ⟨u.1, u.2.1⟩) := fun u => rfl
  have h1 := Subgroup.card_mul_index θC.ker
  rw [Subgroup.index_ker] at h1
  have hker : Nat.card θC.ker ≤ Nat.card ↥(blockU L ⊓ Subgroup.centralizer S) := by
    refine Nat.card_le_card_of_injective (fun u => ⟨u.1.1, ?_, u.1.2.2⟩) ?_
    · have hu := u.2
      rw [MonoidHom.mem_ker, hθ] at hu
      have : H.theta ⟨u.1.1, u.1.2.1⟩ = 0 := by
        have := congrArg Multiplicative.toAdd hu
        simpa using this
      exact (H.theta_eq_zero_iff ⟨u.1.1, u.1.2.1⟩).1 this
    · intro u u' h
      have h' := congrArg (fun z : ↥(blockU L ⊓ Subgroup.centralizer S) => (z : G)) h
      exact Subtype.ext (Subtype.ext h')
  have hc := H.cc_involution hb
  have hrange : Nat.card θC.range ≤ Nat.card {x : Fq n // H.cc b * H.chi b x = x} := by
    refine Nat.card_le_card_of_injective (fun r => ⟨Multiplicative.toAdd r.1, ?_⟩) ?_
    · obtain ⟨u, hu⟩ := r.2
      rw [← hu, hθ, toAdd_ofAdd]
      have hbu : (b : G) * u.1 * (b : G)⁻¹ = u.1 := by
        have := Subgroup.mem_centralizer_iff.1 u.2.2 (b : G) (by simp [hS])
        calc (b : G) * u.1 * (b : G)⁻¹ = (u.1 * (b : G)) * (b : G)⁻¹ := by rw [this]
          _ = u.1 := by group
      have hmu : (b : G) * u.1 * (b : G)⁻¹ ∈ QM L M := by rw [hbu]; exact u.2.1
      have := H.theta_conj b ⟨u.1, u.2.1⟩ hmu
      have e : (⟨(b : G) * u.1 * (b : G)⁻¹, hmu⟩ : ↥(QM L M)) = ⟨u.1, u.2.1⟩ := Subtype.ext hbu
      rw [e] at this
      exact this.symm
    · intro r r' h
      have h' := congrArg (fun z : {x : Fq n // H.cc b * H.chi b x = x} => z.1) h
      exact Subtype.ext (Multiplicative.toAdd.injective h')
  have hFixc := card_fixed_twisted (H.chi b) hχ (H.chi_involution hb) (H.cc b) hc
  have hV := H.card_CV_pair_le hb hχ he he2 heQ hbe
  have hmul : Nat.card θC.ker * Nat.card θC.range ≤
      Nat.card ↥(blockU L ⊓ Subgroup.centralizer S) * Nat.card {x : Fq n // H.cc b * H.chi b x = x} :=
    Nat.mul_le_mul hker hrange
  rw [h1] at hmul
  by_contra hlt
  push Not at hlt
  have h2 : Nat.card (Fq n) < Nat.card ↥(blockU L ⊓ Subgroup.centralizer S) *
      Nat.card {x : Fq n // H.cc b * H.chi b x = x} := hlt.trans_le hmul
  have h3 : Nat.card (Fq n) * Nat.card (Fq n) <
      (Nat.card ↥(blockU L ⊓ Subgroup.centralizer S) *
        Nat.card {x : Fq n // H.cc b * H.chi b x = x}) ^ 2 := by
    nlinarith
  rw [mul_pow] at h3
  have h4 : Nat.card ↥(blockU L ⊓ Subgroup.centralizer S) ^ 2 *
      Nat.card {x : Fq n // H.cc b * H.chi b x = x} ^ 2 ≤ Nat.card (Fq n) * Nat.card (Fq n) := by
    rw [hFixc]
    exact Nat.mul_le_mul_right _ hV
  omega

end MData

end CFSG.CGT.PushingUpLit.T2KR

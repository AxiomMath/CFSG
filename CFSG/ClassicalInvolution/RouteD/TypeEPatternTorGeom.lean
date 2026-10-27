module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthPairs

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv)
open scoped commutatorElement MatrixGroups

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_hypPair_perp_frames (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 11 ≤ Module.finrank K V) (F₁ F₂ : Models.OrthogonalPairs.Frame Q)
    (h : F₂.span ≤ F₁.perp) :
    ∃ P : HypPair Q, P.e ∈ F₁.perp ∧ P.f ∈ F₁.perp ∧ P.e ∈ F₂.perp ∧ P.f ∈ F₂.perp := by
  have hnd : PolarNondegOn Q (F₁.perp ⊓ F₂.perp) := by
    intro x hx hxW
    apply eq_zero_of_polar_eq_zero hQ
    intro y
    have hy : y ∈ F₁.span ⊔ F₁.perp := by
      rw [F₁.isCompl_span_perp.sup_eq_top]
      trivial
    obtain ⟨u, hu, y', hy', rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right]
    have h1 : polar Q x u = 0 := by
      obtain ⟨Y, rfl⟩ := hu
      exact (Frame.mem_perp_iff_forall_incl F₁).mp (Submodule.mem_inf.mp hx).1 Y
    have hv : F₂.incl (F₂.coords y') ∈ F₁.perp := h ⟨F₂.coords y', rfl⟩
    have hw : y' - F₂.incl (F₂.coords y') ∈ F₁.perp ⊓ F₂.perp := by
      refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hy' hv, ?_⟩
      rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
    have h2 : polar Q x (F₂.incl (F₂.coords y')) = 0 :=
      (Frame.mem_perp_iff_forall_incl F₂).mp (Submodule.mem_inf.mp hx).2 _
    have h3 : polar Q x (y' - F₂.incl (F₂.coords y')) = 0 := hxW _ hw
    rw [polar_sub_right] at h3
    rw [h1, zero_add]
    linear_combination h3 + h2
  have hd1 := ModelFacts.finrank_perp_add_four F₁
  have hd2 := ModelFacts.finrank_perp_add_four F₂
  have hdimC : 3 ≤ Module.finrank K ↥(F₁.perp ⊓ F₂.perp) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq F₁.perp F₂.perp
    have h2 : Module.finrank K ↥(F₁.perp ⊔ F₂.perp) ≤ Module.finrank K V := Submodule.finrank_le _
    omega
  have hnd' : (polarBilin (Q.restrict (F₁.perp ⊓ F₂.perp))).Nondegenerate :=
    nondegenerate_polarBilin_restrict hnd
  obtain ⟨v, hv0, hvQ⟩ := ModelFacts.exists_isotropic_of_finrank_ge_three hodd
    (Q.restrict (F₁.perp ⊓ F₂.perp)) hnd' hdimC
  have hQe : Q (v : V) = 0 := by simpa using hvQ
  have hve : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨y, hy, hey⟩ := hnd.exists_polar_ne_zero v.2 hve
  have h1 : polar Q (v : V) ((polar Q (v : V) y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hey]
  let P : HypPair Q := HypPair.ofPolarEqOne hQe h1
  have hPe : P.e ∈ F₁.perp ⊓ F₂.perp := v.2
  have hPf : P.f ∈ F₁.perp ⊓ F₂.perp :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ v.2)
  exact ⟨P, (Submodule.mem_inf.mp hPe).1, (Submodule.mem_inf.mp hPf).1,
    (Submodule.mem_inf.mp hPe).2, (Submodule.mem_inf.mp hPf).2⟩

omit [Finite K] [FiniteDimensional K V] in
theorem mem_perp_frame_iff (F : Models.OrthogonalPairs.Frame Q) {x : V} :
    x ∈ F.perp ↔ polar Q x F.e₁ = 0 ∧ polar Q x F.f₁ = 0 ∧ polar Q x F.e₂ = 0 ∧
      polar Q x F.f₂ = 0 := by
  rw [Frame.mem_perp_iff, Frame.coords_apply]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp at h00 h01 h10 h11
    exact ⟨h11, h00, h10, h01⟩
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3, h4]

omit [FiniteDimensional K V] in
theorem span_le_perp_of_orth (hodd : Odd (Nat.card K)) {F₁ F₂ : Models.OrthogonalPairs.Frame Q}
    (h : ∀ x ∈ negSpace (F₁.La (-1)), ∀ y ∈ negSpace (F₂.La (-1)), polar Q x y = 0) :
    F₂.span ≤ F₁.perp := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  intro x hx
  obtain ⟨Y, rfl⟩ := hx
  rw [Frame.mem_perp_iff_forall_incl]
  intro X
  rw [polar_comm]
  exact h _ (by rw [negSpace_La_neg_one h2]; exact ⟨X, rfl⟩) _
    (by rw [negSpace_La_neg_one h2]; exact ⟨Y, rfl⟩)

theorem exists_adjPerp_model (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 11 ≤ Module.finrank K V) {S A : Subgroup (V ≃ₗ[K] V)} {iS iA : V ≃ₗ[K] V}
    (hS : IsFundamental Q S iS) (hA : IsFundamental Q A iA)
    (horth : ∀ x ∈ negSpace iS, ∀ y ∈ negSpace iA, polar Q x y = 0) :
    ∃ N : Subgroup (V ≃ₗ[K] V), (∃ iN, IsFundamental Q N iN) ∧
      (∃ W, LinearBlockStandardPair K W S N) ∧ Commutes N A := by
  obtain ⟨FS, rfl, rfl⟩ := hS
  obtain ⟨FA, rfl, rfl⟩ := hA
  have hspan : FA.span ≤ FS.perp := span_le_perp_of_orth hodd horth
  have hspan' : FS.span ≤ FA.perp :=
    span_le_perp_of_orth hodd (fun x hx y hy => by rw [polar_comm]; exact horth y hy x hx)
  obtain ⟨c, hce1, hcf1, hce2, hcf2⟩ := exists_hypPair_perp_frames hodd hQ hdim FS FA hspan
  obtain ⟨a1, a2, a3, a4⟩ := (mem_perp_frame_iff FS).mp hce1
  obtain ⟨b1, b2, b3, b4⟩ := (mem_perp_frame_iff FS).mp hcf1
  let T : Triple Q := ⟨FS.P, FS.P', c, FS.orth,
    ⟨by rw [polar_comm]; exact a1, by rw [polar_comm]; exact b1, by rw [polar_comm]; exact a2,
      by rw [polar_comm]; exact b2⟩,
    ⟨by rw [polar_comm]; exact a3, by rw [polar_comm]; exact b3, by rw [polar_comm]; exact a4,
      by rw [polar_comm]; exact b4⟩⟩
  obtain ⟨θ, hθinj, -, hB12, hB23⟩ := T.exists_theta (L₁ := FS.La.range)
    (L₂ := T.frame12.La.range) (Or.inl rfl) (Or.inl rfl)
  refine ⟨T.frame12.La.range, ⟨_, IsFundamental.of_frame _⟩, ⟨θ.range, θ, 1, rfl, ?_,
    Or.inl ⟨?_, ?_⟩⟩, ?_⟩
  · intro x hx
    have : x = 1 := hθinj (by rw [MonoidHom.mem_ker.mp hx, map_one])
    rw [this]
    exact Subgroup.one_mem _
  · have e : (MulAut.conj (1 : SL(3, K))⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [e, Subgroup.map_id]
    exact hB12
  · have e : (MulAut.conj (1 : SL(3, K))⁻¹).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [e, Subgroup.map_id]
    exact hB23
  · have hG : ∀ y ∈ T.frame12.span, y ∈ FA.perp := by
      rintro _ ⟨X, rfl⟩
      rw [Frame.incl_apply]
      exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ (hspan' FS.e₂_mem_span))
        (Submodule.smul_mem _ _ (hspan' FS.f₂_mem_span))) (Submodule.smul_mem _ _ hce2))
        (Submodule.smul_mem _ _ hcf2)
    have horth' : ∀ X Y, polar Q (FA.incl X) (T.frame12.incl Y) = 0 := fun X Y => by
      rw [polar_comm]
      exact (Frame.mem_perp_iff_forall_incl FA).mp (hG _ ⟨Y, rfl⟩) X
    have hc : Commutes FA.La.range T.frame12.La.range := by
      rintro _ ⟨A', rfl⟩ _ ⟨B, rfl⟩
      exact Frame.La_comm_of_orth horth' A' B
    exact commutes_symm hc

end Geometry

section Predicate

variable {KY : Type} [Group KY]

@[expose] def AdjPerp (F : Type) [Field F] (Z : Subgroup KY) (𝓕 : Set (Subgroup KY)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ModelAdj Z A B → ∀ S ∈ 𝓕, Commutes S A → Commutes S B →
    ∃ N ∈ 𝓕, (∃ W, LinearBlockStandardPair F W S N) ∧ Commutes N A

end Predicate

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem adjPerp_model (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 11 ≤ Module.finrank K V) : AdjPerp K (scalars K V) (fundSet Q) := by
  rintro A ⟨iA, hA⟩ B ⟨iB, hB⟩ hAB S ⟨iS, hS⟩ hSA hSB
  have horth := orth_of_cross hodd (by omega : 9 ≤ Module.finrank K V) hA hB hS hAB.1 hAB.2.1
    (ModelInvComm.of_adj hAB).symm' (commutes_symm hSA) (commutes_symm hSB)
  obtain ⟨N, hN, hlin, hc⟩ := exists_adjPerp_model hodd hQ hdim hS hA
    (fun x hx y hy => by rw [polar_comm]; exact horth y hy x hx)
  exact ⟨N, hN, hlin, hc⟩

end Model

section Transfer

variable {F : Type} [Field F] {KY X : Type} [Group KY] [Group X] {π : KY →* X}
  {𝓕 : Set (Subgroup KY)} {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem CentralQuot.adjPerp {p : ℕ} [Fact p.Prime] [CharP F p] [Finite F] (h4 : 4 ≤ Nat.card F)
    [Finite KY] (hC : ¬ p ∣ Nat.card (Subgroup.center KY)) (h : CentralQuot π 𝓕 𝓕' Z')
    (hG : AdjPerp F Z' 𝓕') : AdjPerp F (Subgroup.center KY) 𝓕 := by
  intro A hA B hB hAB S hS hSA hSB
  obtain ⟨N', hN', ⟨W, hW⟩, hc⟩ := hG (A.map π) (h.map_mem A hA) (B.map π) (h.map_mem B hB)
    (h.modelAdj hA hB hAB) (S.map π) (h.map_mem S hS) ((h.commutes_iff hS).mpr hSA)
    ((h.commutes_iff hS).mpr hSB)
  obtain ⟨N, hN, rfl⟩ := h.surj N' hN'
  exact ⟨N, hN, exists_lin_of_map h4 hC π h.ker_le (h.perf S hS) (h.perf N hN) ⟨W, hW⟩,
    (h.commutes_iff hN).mp hc⟩

end Transfer

section Plus

variable {p f m : ℕ} [Fact p.Prime]

theorem adjPerp_plusDatum (hp2 : p ≠ 2) (hm : 6 ≤ m) (hm3 : 3 ≤ m) (hq : 5 ≤ p ^ f) :
    AdjPerp (GaloisField p f) (Subgroup.center (spinGroup (quadPlus m (GaloisField p f))))
      (fundamentalSubgroups .POmegaPlus (plusDatum m (GaloisField p f) hm3)) := by
  obtain ⟨hf, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hK]
    omega
  have hdim : 11 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hG := adjPerp_model (Q := quadPlus m (GaloisField p f)) hodd
    (nondegenerate_polarBilin_quadPlus m (GaloisField p f)) hdim
  have : NeZero m := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus m (GaloisField p f))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  exact (centralQuot_plus hp2 (by omega) hm3 hq).adjPerp h4 (not_dvd_card_center_plus hp2 hm3) hG

theorem adjPerp_plus (hp2 : p ≠ 2) (hm : 6 ≤ m) (hq : 5 ≤ p ^ f) :
    AdjPerp (GaloisField p f) (Subgroup.center (modelUniv .POmegaPlus m p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus m p f Fact.out).D) := by
  have e := RouteD.modelUniv_POmegaPlus_eq (p := p) (f := f) (by omega : 3 ≤ m)
  rw [e]
  exact adjPerp_plusDatum hp2 hm (by omega) hq

end Plus

end CFSG.ClassicalInvolution.RouteD.Gaps

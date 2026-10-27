module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93ResSL2

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

open Subgroup Module CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification CFSG.GH74.GLS.IVK.Proofs2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.CatalogueBUnitaryB
open scoped MatrixGroups

theorem ivk93res_psu_embedding {p f : ℕ} {K : Type} [Field K] (hud : UnitaryFieldData p f K)
    {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1) :
    ∃ φ : StatedProj (StatedSU (2 * r + ε) (p ^ f) K) →* sesqProjUnitary hud (hypForm hud r ε),
      Function.Injective φ ∧ φ.range = projSpecial hud (hypForm hud r ε) := by
  classical
  have : Fact p.Prime := ⟨hud.prime⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  set θ := (hypPSUEquivStatedProj hud hR (by omega)).symm
  set ι : hypPSU hud r ε →* sesqProjUnitary hud (hypForm hud r ε) :=
    (projSpecial hud (hypForm hud r ε)).subtype.comp (hypModelEquiv hud).toMonoidHom with hιdef
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv hud).injective
  set φ := ι.comp θ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := hι.comp θ.injective
  refine ⟨φ, hφ, ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact (hypModelEquiv hud (θ y)).2
  · intro hz
    obtain ⟨w, hw⟩ := (hypModelEquiv hud).surjective ⟨z, hz⟩
    refine ⟨θ.symm w, ?_⟩
    rw [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      hιdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hw]
    rfl

section Paired

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

theorem ivk93res_structure_paired (h : UnitaryFieldData p f E) (hp : p ≠ 2) [FiniteDimensional E V]
    (hn : 2 ≤ finrank E V) {B : V →ₛₗ[h.bar] V →ₗ[E] E} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {A : sesqUnitaryGroup B} (hA : orderOf (QuotientGroup.mk A : sesqProjUnitary h B) = 2)
    (hnorm : ∀ l : E, unitaryOp A * unitaryOp A = (l ^ 2) • (1 : Module.End E V) → h.norm l = -1) :
    ∃ P : Submodule E V, P ≠ ⊥ ∧ 2 * finrank E P = finrank E V ∧
      Nonempty (centralizer ({A} : Set (sesqUnitaryGroup B)) ≃* LinearMap.GeneralLinearGroup E P) := by
  obtain ⟨l, -, hl2, hN, hP, -, -, -, hpaired, -⟩ :=
    projective_unitary_involution_centralizer_matrix_structure h hp hn hB hBl hA
  have hnl : h.norm l = -1 := hnorm l hl2
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP E p := h.charP
  rcases hN with hN | hN
  · exfalso
    rw [hnl] at hN
    exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq E p]; exact hp) hN
  · obtain ⟨-, -, -, h2m, -, -, eC, -⟩ := hpaired hN
    exact ⟨_, hP, h2m, ⟨eC⟩⟩

theorem ivk93res_sl2_of_gl [Finite E] {P : Submodule E V} [FiniteDimensional E V] {G : Type}
    [Group G] (hP : finrank E P = 2) (eC : G ≃* LinearMap.GeneralLinearGroup E P) :
    ∃ ψ₀ : SL(2, E) →* G, Function.Injective ψ₀ := by
  let eGL := eC.trans ((LinearMap.GeneralLinearGroup.generalLinearEquiv E P).trans
    (CatalogueBAlternatingIsometry.basisMatrixEquiv (Module.finBasis E P)))
  obtain ⟨m, hm, ⟨e⟩⟩ : ∃ m : ℕ, m = 2 ∧ Nonempty (G ≃* GL (Fin m) E) :=
    ⟨_, hP, ⟨eGL⟩⟩
  subst hm
  refine ⟨e.symm.toMonoidHom.comp Matrix.SpecialLinearGroup.toGL, ?_⟩
  intro a b hab
  have h1 : Matrix.SpecialLinearGroup.toGL a = Matrix.SpecialLinearGroup.toGL b :=
    e.symm.injective hab
  exact Subtype.ext (congrArg (fun u : GL (Fin 2) E => (u : Matrix (Fin 2) (Fin 2) E)) h1)

end Paired

theorem ivk93res_sl2_uni {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1) :
    Ivk93ResSL2 (StatedProj (StatedSU (2 * 2 + 0) (p ^ f) K)) (p ^ f) := by
  classical
  have hud : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have hcharK : CharP K p := hud.charP
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hm⟩ : ∃ m, p ^ f = 4 * m + 1 := ⟨p ^ f / 4, by omega⟩
  have hsqK : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
    have : (p ^ f) ^ 2 % 4 = 1 := by rw [Nat.pow_mod, hq]
    omega
  obtain ⟨ι, hι⟩ := hsqK
  have hι0 : ι ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hι
    exact (neg_ne_zero.2 one_ne_zero) hι
  have hι4 : ι ^ 4 = 1 := by
    calc ι ^ 4 = (ι * ι) * (ι * ι) := by ring
      _ = 1 := by rw [← hι]; norm_num
  have hbar : hud.bar ι = ι := by
    rw [hud.bar_apply, hm, pow_succ, pow_mul, hι4, one_pow, one_mul]
  have hne1 : ι * ι ≠ 1 := by
    rw [← hι]
    exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq K p]; exact hp2)
  let a : Fin 2 → Kˣ := fun _ => Units.mk0 ι hι0
  let d : Fin 0 → Kˣ := fun k => k.elim0
  have hd : ∀ k : Fin 0, hud.norm (d k : K) = 1 := fun k => k.elim0
  have hratio : torusRatio hud a d = 1 := by
    simp [torusRatio, a, hbar, hι0]
  obtain ⟨gT, -, hgT⟩ := torusMat_mem_hypSU (r := 2) (ε := 0) hud a hd hratio
  let B := hypForm hud 2 0
  let A' : sesqUnitaryGroup B := ((hypSpecialHom hud gT : CatalogueBUnitaryB.unitarySpecial B) : sesqUnitaryGroup B)
  have hA'sp : A' ∈ CatalogueBUnitaryB.unitarySpecial B := (hypSpecialHom hud gT).2
  have hop : ∀ v : HypIndex 2 0 → K, unitaryOp A' v =
      (Matrix.diagonal (torusEntries hud a d)).mulVec v := by
    intro v
    rw [← hgT]
    exact toLin_hyp_apply (gT : GL (HypIndex 2 0) K) v
  have hent : ∀ (v : HypIndex 2 0 → K) x, unitaryOp A' v x = torusEntries hud a d x * v x := by
    intro v x
    rw [hop, Matrix.mulVec_diagonal]
  have hsqA : unitaryOp A' * unitaryOp A' = (-1 : K) • (1 : Module.End K (HypIndex 2 0 → K)) := by
    refine LinearMap.ext fun v => funext fun x => ?_
    rw [Module.End.mul_apply, hent, hent]
    rcases x with i | k | i
    · simp only [torusEntries, a, Units.val_mk0, LinearMap.smul_apply, Module.End.one_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← hι]
    · exact k.elim0
    · simp only [torusEntries, a, Units.val_mk0, hbar, LinearMap.smul_apply, Module.End.one_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ← mul_inv, ← hι]
      simp
  let aD : sesqProjUnitary hud B := QuotientGroup.mk A'
  have haD2 : aD ^ 2 = 1 := by
    show (QuotientGroup.mk A' : sesqProjUnitary hud B) ^ 2 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine ⟨-1, by simp [UnitaryFieldData.norm], ?_⟩
    change unitaryOp A' * unitaryOp A' = _
    rw [hsqA]
  have haD1 : aD ≠ 1 := by
    intro h1
    obtain ⟨c, -, hc⟩ := (QuotientGroup.eq_one_iff A').1 h1
    have h2 := congrArg (fun φ : Module.End K (HypIndex 2 0 → K) =>
      φ (Pi.single (Sum.inl 0) 1) (Sum.inl 0)) hc
    have h3 := congrArg (fun φ : Module.End K (HypIndex 2 0 → K) =>
      φ (Pi.single (Sum.inr (Sum.inr 0)) 1) (Sum.inr (Sum.inr 0))) hc
    simp only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply] at h2 h3
    change unitaryOp A' (Pi.single (Sum.inl 0) 1) (Sum.inl 0) = _ at h2
    change unitaryOp A' (Pi.single (Sum.inr (Sum.inr 0)) 1) (Sum.inr (Sum.inr 0)) = _ at h3
    rw [hent] at h2 h3
    simp [torusEntries, a, hbar] at h2 h3
    have h4 : ι⁻¹ = ι := h3.trans h2.symm
    apply hne1
    calc ι * ι = ι * ι⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel₀ hι0
  have haD : orderOf aD = 2 := orderOf_eq_prime haD2 haD1
  have hn4 : finrank K (HypIndex 2 0 → K) = 4 := by
    simp
  have hnorm : ∀ l : K, unitaryOp A' * unitaryOp A' = (l ^ 2) • (1 : Module.End K (HypIndex 2 0 → K)) →
      hud.norm l = -1 := by
    intro l hl
    have h1 := congrArg (fun φ : Module.End K (HypIndex 2 0 → K) =>
      φ (Pi.single (Sum.inl 0) 1) (Sum.inl 0)) (hl.symm.trans hsqA)
    simp only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply] at h1
    simp at h1
    rw [UnitaryFieldData.norm, hud.bar_apply, hm]
    calc l * l ^ (4 * m + 1) = (l ^ 2) ^ (2 * m + 1) := by ring
      _ = -1 := by rw [h1]; exact Odd.neg_one_pow ⟨m, rfl⟩
  obtain ⟨P, -, h2m, ⟨eC⟩⟩ := ivk93res_structure_paired hud hp2 (V := HypIndex 2 0 → K)
    (by omega) (hypForm_isSymm hud) (hypForm_separatingLeft hud) haD hnorm
  have hP2 : finrank K P = 2 := by omega
  obtain ⟨ψ₀, hψ₀inj⟩ := ivk93res_sl2_of_gl hP2 eC
  let ψ₁ : SL(2, K) →* sesqUnitaryGroup B := (Subgroup.centralizer {A'}).subtype.comp ψ₀
  have hψ₁c : ∀ g, ψ₁ g * A' = A' * ψ₁ g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (ψ₀ g).2
  have hψ₁inj : Function.Injective ψ₁ := Subtype.val_injective.comp hψ₀inj
  have hK4 : 4 ≤ Nat.card K := by
    have h5 : 5 ≤ p ^ f := by
      have := hp.two_le
      have h1 : 2 ≤ p ^ f := this.trans (Nat.le_self_pow (by omega) p)
      omega
    rw [hK]
    nlinarith
  have hQ : CFSG.IsQuasisimple SL(2, K) := GHInv.isQuasisimple_sl2 hK4
  have hperf : commutator SL(2, K) = ⊤ := hQ.1.commutator_eq_top
  have hdet : ∀ g, ψ₁ g ∈ CatalogueBUnitaryB.unitarySpecial B := by
    let δ : SL(2, K) →* Kˣ :=
      (Units.map (LinearMap.det : Module.End K (HypIndex 2 0 → K) →* K)).comp
        ((sesqUnitaryGroup B).subtype.comp ψ₁)
    have hker : commutator SL(2, K) ≤ δ.ker := Abelianization.commutator_subset_ker δ
    intro g
    have hg : g ∈ δ.ker := hker (hperf ▸ Subgroup.mem_top g)
    rw [CatalogueBUnitaryB.mem_unitarySpecial]
    have h1 : δ g = 1 := hg
    exact congrArg (fun u : Kˣ => (u : K)) h1
  let ψD : SL(2, K) →* sesqProjUnitary hud B :=
    (QuotientGroup.mk' (sesqNormOneScalars hud B)).comp ψ₁
  have hψDsp : ∀ g, ψD g ∈ projSpecial hud B := fun g => Subgroup.mem_map_of_mem _ (hdet g)
  have haDsp : aD ∈ projSpecial hud B := Subgroup.mem_map_of_mem _ hA'sp
  have hψDc : ∀ g, ψD g * aD = aD * ψD g := by
    intro g
    show (QuotientGroup.mk (ψ₁ g) : sesqProjUnitary hud B) * QuotientGroup.mk A' =
      QuotientGroup.mk A' * QuotientGroup.mk (ψ₁ g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hψ₁c g]
  have hψD1 : ψD ≠ 1 := by
    intro h1
    have hsc : ∀ g, ψ₁ g ∈ sesqNormOneScalars hud B := by
      intro g
      have h2 : ψD g = 1 := by rw [h1]; rfl
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hcomm : ∀ g g', ψ₁ g * ψ₁ g' = ψ₁ g' * ψ₁ g := fun g g' =>
      mem_sesqNormOneScalars_commute (hsc g) (ψ₁ g')
    have hker : commutator SL(2, K) ≤ ψ₁.ker := by
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm a b)
    let g₀ : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hg₀ : ψ₁ g₀ = 1 := hker (hperf ▸ Subgroup.mem_top g₀)
    have h5 : g₀ = 1 := hψ₁inj (hg₀.trans (map_one ψ₁).symm)
    have h6 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 1) h5
    simp [g₀] at h6
  obtain ⟨φ, hφinj, hφrange⟩ := ivk93res_psu_embedding hud (r := 2) (ε := 0) (by norm_num)
    (by norm_num)
  have hmemR : ∀ x ∈ projSpecial hud B, x ∈ φ.range := fun x hx => hφrange ▸ hx
  let yR : ↥φ.range := ⟨aD, hmemR _ haDsp⟩
  let ψR : SL(2, K) →* ↥φ.range := ψD.codRestrict φ.range (fun g => hmemR _ (hψDsp g))
  have hR : Ivk93ResSL2 ↥φ.range (p ^ f) := by
    refine ⟨yR, K, inferInstance, inferInstance, ψR, ?_, hK, fun h1 => hψD1 ?_, fun g => ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact haD
    · ext g
      exact congrArg (fun φ' : SL(2, K) →* ↥φ.range => ((φ' g : ↥φ.range) : sesqProjUnitary hud B)) h1
    · exact Subtype.ext (hψDc g)
  exact hR.of_equiv (MonoidHom.ofInjective hφinj).symm

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93Adapt

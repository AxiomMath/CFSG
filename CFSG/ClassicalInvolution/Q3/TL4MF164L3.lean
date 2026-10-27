module

public import CFSG.ClassicalInvolution.Q3.TL4MF164Fr
public import CFSG.ClassicalInvolution.Q3.TL4MF164M11

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint Matrix
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem blk_eq_blockSL {K : Type} [Field K] (B : SL(2, K)) :
    GH74.GLS.IVK.Proofs2.Lemma41aL3.blk (SpecialLinearGroup.toGL B) =
      SpecialLinearGroup.toGL (WeakCT.blockSL K 3 2 0 (by omega) B) := by
  apply Units.ext
  rw [GH74.GLS.IVK.Proofs2.Lemma41aL3.coe_blk, SpecialLinearGroup.coe_GL_coe_matrix,
    SpecialLinearGroup.coe_GL_coe_matrix, WeakCT.coe_blockSL_three_zero,
    GH74.GLS.IVK.Proofs2.Lemma41aL3.blkMat, B.2]
  simp

theorem exists_sl2_of_frame {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) {π : (⊤ : Subgroup (GL (Fin 2) K)) →* X} (hk : CubeKer π) {z s : X}
    (hz : z ≠ 1) (hπ1 : π ⟨-1, Subgroup.mem_top _⟩ = z) (hsz : s * s = z)
    (hsr : s ∈ π.range) :
    ∃ B : SL(2, K), π ⟨SpecialLinearGroup.toGL B, Subgroup.mem_top _⟩ = s := by
  obtain ⟨A, rfl⟩ := hsr
  have hns : ∀ c : Kˣ, (A : GL (Fin 2) K) ≠ GeneralLinearGroup.scalar (Fin 2) c := by
    intro c hc
    have hc2 : c * c = 1 := by
      have h1 : c ^ 2 = 1 := by
        have hcard : Nat.card Kˣ = 2 := by rw [Nat.card_units, hK]
        rw [← hcard]
        exact pow_card_eq_one'
      rwa [sq] at h1
    apply hz
    rw [← hsz, ← map_mul]
    have hA2 : A * A = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, hc, ← map_mul, hc2, map_one, Subgroup.coe_one])
    rw [hA2, map_one]
  obtain ⟨B, hB, hBA⟩ := mem_map_slPart_of_sq hk (N1 := ⟨-1, Subgroup.mem_top _⟩) rfl
    (by rw [hπ1]; exact hsz) hns
  refine ⟨Q5L3.slPartTopEquiv ⟨B, hB⟩, ?_⟩
  rw [← hBA]
  exact congrArg π (Subtype.ext (Units.ext rfl))

theorem map_blockSL {R S : Type} [Field R] [Field S] (κ : R ≃+* S) (B : SL(2, R)) :
    SpecialLinearGroup.map κ.toRingHom (WeakCT.blockSL R 3 2 0 (by omega) B) =
      WeakCT.blockSL S 3 2 0 (by omega) (SpecialLinearGroup.map κ.toRingHom B) := by
  ext i j
  rw [SpecialLinearGroup.map_apply_coe, WeakCT.coe_blockSL_three_zero,
    WeakCT.coe_blockSL_three_zero]
  fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.map_apply_coe]

theorem map_map_symm {R S : Type} [Field R] [Field S] (κ : R ≃+* S) {n : ℕ} (x : SL(n, S)) :
    SpecialLinearGroup.map κ.toRingHom (SpecialLinearGroup.map κ.symm.toRingHom x) = x := by
  ext i j
  simp [SpecialLinearGroup.map_apply_coe]

theorem map_symm_map {R S : Type} [Field R] [Field S] (κ : R ≃+* S) {n : ℕ} (x : SL(n, R)) :
    SpecialLinearGroup.map κ.symm.toRingHom (SpecialLinearGroup.map κ.toRingHom x) = x := by
  ext i j
  simp [SpecialLinearGroup.map_apply_coe]

theorem exists_sl3_conj {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3) (Q : GL (Fin 3) K)
    (B : SL(2, K)) : ∃ g : SL(3, K), Q5L3.blkP Q (SpecialLinearGroup.toGL B) =
      g * WeakCT.blockSL K 3 2 0 (by omega) B * g⁻¹ := by
  have := Fintype.ofFinite K
  set d := GeneralLinearGroup.det Q with hd
  have hd3 : d ^ 3 = d := by
    have h := FiniteField.pow_card (d : K)
    rw [← Nat.card_eq_fintype_card, hK] at h
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h])
  set Q' : GL (Fin 3) K := Q * GeneralLinearGroup.scalar (Fin 3) d⁻¹ with hQ'
  have hdet : (Q' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hQ', map_mul, GeneralLinearGroup.det_scalar,
      Fintype.card_fin, inv_pow, hd3, ← hd, mul_inv_cancel, Units.val_one]
  let g : SL(3, K) := ⟨Q', hdet⟩
  refine ⟨g, SpecialLinearGroup.toGL_injective ?_⟩
  have hg : SpecialLinearGroup.toGL g = Q' := Units.ext rfl
  rw [Q5L3.toGL_blkP, blk_eq_blockSL, map_mul, map_mul, map_inv, hg, hQ']
  set x := SpecialLinearGroup.toGL (WeakCT.blockSL K 3 2 0 (by omega) B)
  have hc := Q5L3.scalar_mul_comm₃ d⁻¹ x
  calc Q * x * Q⁻¹ = Q * (GeneralLinearGroup.scalar (Fin 3) d⁻¹ * x *
        (GeneralLinearGroup.scalar (Fin 3) d⁻¹)⁻¹) * Q⁻¹ := by rw [hc]; group
    _ = _ := by group

theorem gamma_sq_of_l3_three {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 3) (e₀ : X ≃* projectiveSL 3 K) (Q : GL (Fin 3) K) (B : SL(2, K)) {s : X}
    (hs : e₀.symm (proj 3 K (Q5L3.blkP Q (SpecialLinearGroup.toGL B))) = s)
    (hs4 : orderOf s = 4) {γ : MulAut X} (hγs : γ s = s) (hγ4 : γ ^ 4 = 1) :
    γ ^ 2 = 1 ∨ γ ^ 2 = MulAut.conj (s ^ 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite K
  have hGF : Nat.card (GaloisField 3 1) = 3 := by rw [GaloisField.card 3 1 one_ne_zero]; rfl
  have := Fintype.ofFinite (GaloisField 3 1)
  let κ : GaloisField 3 1 ≃+* K := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hGF, hK])
  obtain ⟨g', hg'⟩ := exists_sl3_conj hK Q B
  let ψ : SL(3, GaloisField 3 1) →* X :=
    e₀.symm.toMonoidHom.comp ((proj 3 K).comp (SpecialLinearGroup.map κ.toRingHom))
  have hψ : ∀ x, ψ x = e₀.symm (proj 3 K (SpecialLinearGroup.map κ.toRingHom x)) := fun _ => rfl
  set g := SpecialLinearGroup.map κ.symm.toRingHom g' with hg
  set B₀ := SpecialLinearGroup.map κ.symm.toRingHom B with hB₀
  set s₀ := g * WeakCT.blockSL (GaloisField 3 1) 3 2 0 (by omega) B₀ * g⁻¹ with hs₀def
  have h1 : SpecialLinearGroup.map κ.toRingHom s₀ =
      g' * WeakCT.blockSL K 3 2 0 (by omega) B * g'⁻¹ := by
    rw [hs₀def, map_mul, map_mul, map_inv, hg, map_map_symm, map_blockSL, hB₀, map_map_symm]
  have hψs₀ : ψ s₀ = s := by rw [hψ, h1, ← hg', hs]
  have hker : ψ.ker ≤ Subgroup.center SL(3, GaloisField 3 1) := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ, MulEquiv.map_eq_one_iff, proj_eq_one_iff] at hx
    have hc := scalars_le_center 3 K hx
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    have h1 := hc (SpecialLinearGroup.map κ.toRingHom y)
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg (SpecialLinearGroup.map κ.symm.toRingHom) h1
    rwa [map_symm_map, map_symm_map] at h2
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨w, hw⟩ := proj_surjective 3 K (e₀ y)
    refine ⟨SpecialLinearGroup.map κ.symm.toRingHom w, ?_⟩
    rw [hψ, map_map_symm, hw, MulEquiv.symm_apply_apply]
  have h23 : 2 ≤ 3 := by omega
  set Rf : Subgroup SL(3, GaloisField 3 1) :=
    (Models.rootSL2 (GaloisField 3 1) h23).map (MulAut.conj g).toMonoidHom with hRfdef
  have hRf : Rf ∈ Generic.fundamentalSubgroups .PSL (Generic.modelUniv .PSL 3 3 1 Fact.out).D :=
    RouteD.longRootSet_subset_fundamentalSubgroups_psl (m := 2) h23
      ((Models.mem_longRootSet_iff h23).2 ⟨g, rfl⟩)
  have hs₀ : s₀ ∈ Rf := ⟨_, ⟨B₀, rfl⟩, by rw [hs₀def]; rfl⟩
  have hord : orderOf (ψ s₀) = 2 ^ (1 + 1) := by rw [hψs₀, hs4]; norm_num
  have hγ' : γ (ψ s₀) = ψ s₀ := by rw [hψs₀, hγs]
  have h := Asc77.s26_aut164L 3 1 ⟨Nat.prime_three, le_rfl, by decide⟩ (by norm_num) X ψ hker
    hsurj Rf hRf s₀ hs₀ 1 le_rfl hord γ hγ' hγ4
  have h2 : (ψ s₀) ^ 2 = s ^ 2 := by rw [hψs₀]
  rcases h with h | h
  · left
    simpa using h
  · right
    rw [pow_one] at h
    rw [h]
    exact congrArg MulAut.conj h2

theorem model164L3_proved : Model164L3 := by
  intro X _ _ R S z hm _ _ p f hp hp2 hL U hUR hUc hU4 β γ hγU hβ hβ2
  by_cases h3 : p ^ f = 3
  swap
  · exact (false_of_l3_ne_three hm.datum hp hp2 hL h3).elim
  obtain ⟨K, _, _, hK, ⟨e₀⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  rw [h3] at hK
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  let e : ↥(⊤ : Subgroup X) ≃* projectiveSL 3 K := Subgroup.topEquiv.trans e₀
  obtain ⟨Q, π, hrange, hk, hπ1, hπ⟩ :=
    Q5L3.exists_frame hodd e (Subgroup.mem_top z) hm.datum.order
  obtain ⟨s, hs'⟩ := hUc.exists_generator
  have hs4 : orderOf (s : X) = 4 := orderOf_gen_eq_four hs' hU4
  have hsz : (s : X) ^ 2 = z := sq_eq_of_cyclic_four hm.datum hUR hs4
  have hz1 : z ≠ 1 := fun h => by
    have h2 := hm.datum.order
    rw [h, orderOf_one] at h2
    omega
  have hsr : (s : X) ∈ π.range := by
    rw [hrange]
    refine ⟨Subgroup.mem_top _, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hsz, sq, mul_assoc]
  obtain ⟨B, hB⟩ := exists_sl2_of_frame hK hk hz1 hπ1 (by rw [← sq]; exact hsz) hsr
  have hγ4 : γ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, ← hβ, hβ2]
  have hsB : e₀.symm (proj 3 K (Q5L3.blkP Q (SpecialLinearGroup.toGL B))) = s := by
    rw [← hB, hπ]
    rfl
  rcases gamma_sq_of_l3_three hK e₀ Q B hsB hs4 (hγU s s.2) hγ4 with h | h
  · left
    rw [hβ, ← sq, h]
  · right
    rw [hβ, ← sq, h, hsz]

end CFSG.ClassicalInvolution.Q3.TL4.MF164

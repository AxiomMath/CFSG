module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z9
public import CFSG.ClassicalInvolution.RouteD.TriageSU4Layer
public import CFSG.ClassicalInvolution.Asc77.AscT7Y1
public import CFSG.ClassicalInvolution.Asc77.AscT7Z1
public import CFSG.ClassicalInvolution.Asc77.AscT7Z5
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedDDischarge

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.TwistedPairs
  CFSG.ClassicalInvolution.RouteD.SU4Pattern
open CFSG.ClassicalInvolution.Phan (Su blockEmb blockMat blockMat_one)
open CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalGroups.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr)
open CFSG.LieType.Universal.Spin.Twisted (fact_shortField)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


section Torus

variable {K₄ : Type} [Field K₄] [Finite K₄] [CharP K₄ p]

theorem su4TorusElt_comm_blockEmb_two (l : K₄) (hl : unitaryInvolution K₄ p f l * l = 1)
    (A : Su K₄ p f 2) :
    blockEmb K₄ p f 4 2 2 (by omega) A * su4TorusElt K₄ p f l hl =
      su4TorusElt K₄ p f l hl * blockEmb K₄ p f 4 2 2 (by omega) A := by
  apply suMat_injective
  have h1 : ∀ X : Matrix (Fin 2) (Fin 2) K₄, blockMat 4 2 X = BD 1 X := fun X => by
    unfold BD
    rw [blockMat_one, one_mul]
  rw [suMat_mul, suMat_mul, suMat_su4TorusElt, suMat_blockEmb, h1, BD_mul, BD_mul]
  simp

end Torus

theorem eSide3 [IsSimpleGroup G] (hq3 : p ^ f % 4 = 3) (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hex : ExactMembers Ω) (hOE : classicalInvolutionOddCore ↥(exactLayer Ω e) = ⊥)
    (hE : LayerOrthType p f Ω e 6 false) {z₁ : G} (hz₁2 : z₁ * z₁ = 1) (hz₁e : z₁ * e = e * z₁)
    (θ : SL(2, GaloisField p f) →* G) (hθ : θ.range = conjSub g K)
    (hθτ : ∀ s, z₁ * θ s * z₁⁻¹ = θ (diagConj2 (-1) 1 s))
    (hclaim : ∀ a : G, a * u = u * a → (∀ x ∈ conjSub g K, a * x = x * a) →
      (∀ x ∈ conjSub g K', a * x = x * a) → a * z₁ = z₁ * a) :
    ∃ K₃ : Subgroup G, (∃ V, TwistedB2BlockPair (minusCoeffs_irr p f) V (conjSub g K) K₃) ∧
      K₃ ≤ Subgroup.centralizer ({z₁} : Set G) ∧ K₃ ≤ ⁅K₃, K₃⁆ ∧ K₃ ≤ exactLayer Ω e ∧
      exactLayer Ω e ≤ conjSub g K ⊔ K₃ ∧ conjSub g K ≤ exactLayer Ω e ∧
      conjSub g K' ≤ exactLayer Ω e := by
  classical
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hcls := hst.hyp.classical
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R₂, R₂', a₂, b₂, v', hJt, hJ't, -⟩ := T7L.exists_uFrame hs hd
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    T7K.exists_decomp hs hd
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) :=
    T7Y.le_centralizer_e hs hd hα hKΩ hs.hz hR hRN
  have hK'e : K' ≤ Subgroup.centralizer ({e} : Set G) :=
    T7Y.le_centralizer_e hs hd hα hK'Ω hzK' hR' hR'N
  have hJΩ : conjSub g K ∈ Ω := hst.hyp.conjInvariant g K hKΩ
  have hJ'Ω : conjSub g K' ∈ Ω := hst.hyp.conjInvariant g K' hK'Ω
  have hJe := T7Z.conjSub_le_centralizer_e hd hKe
  have hJ'e := T7Z.conjSub_le_centralizer_e hd hK'e
  have hKΦ : K ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hKΩ, hKe⟩
  have hK'Φ : K' ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hK'Ω, hK'e⟩
  have hJΦ : conjSub g K ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hJΩ, hJe⟩
  have hJ'Φ : conjSub g K' ∈ exactFamily Ω e := centMembers_subset_exactFamily hcls ⟨hJ'Ω, hJ'e⟩
  have hJu : conjSub g K ≤ Subgroup.centralizer ({u} : Set G) :=
    ((tqMembers_eq_centMembers_of_exact (c := u) hex) ▸ hJt).2
  have htJ : IsUniqueInvolution (conjSub g K) (u * e) := hd.hgt ▸ hs.hz.conj g
  have htJ' : IsUniqueInvolution (conjSub g K') (u * e) := hd.hgt ▸ hzK'.conj g
  have hexeq : ∀ L ∈ Ω, Nonempty (↥L ≃* SL(2, GaloisField p f)) := by
    intro L hL
    obtain ⟨zL, hzL⟩ := hcls L hL
    exact hzL.nonempty_equiv_sl2 (hex L hL)
  have hJJ' : conjSub g K ≠ conjSub g K' := fun h => hs.hne ((conjSub_inj g).mp h).symm
  have hKle : K ≤ omegaGen (exactFamily Ω e) := le_omegaGen hKΦ
  have hK'le : K' ≤ omegaGen (exactFamily Ω e) := le_omegaGen hK'Φ
  have hue : u ∈ omegaGen (exactFamily Ω e) := sup_le hKle hK'le hd.hu
  obtain ⟨t', n', ht', D, hcard, i', hit, hir⟩ := T7Z.exists_omegaLie_of_layerOrth hOE hE
  have htn : t' = .PSU ∧ n' = 4 := by
    rcases ht' with h | h | h | h | h | h <;> simp_all
  have hie : D.exp i' = f := by
    rcases D.exp_eq i' with h | ⟨h, -⟩
    · exact h
    · exact absurd (hit.symm.trans h) (by rw [htn.1]; decide)
  obtain ⟨P⟩ := T7Z.nonempty_modelLayer_of_omegaLie D hcard i' (hit.trans htn.1)
    (hir.trans htn.2) hie
  have h2 : (2 : GaloisField p f) ≠ 0 := ModelFacts.two_ne_zero_galoisField f hp2
  have hadm : StatedLieAdmissible .PSU 4 p f :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf0, by norm_num, fun h => by
      have := congrArg Prod.fst h
      simp at this⟩
  have hK : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 :=
    ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq
  have hF4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [GaloisField.card p f hf0]
    omega
  have : NeZero f := ⟨hf0⟩
  have : NeZero (2 * f) := ⟨by omega⟩
  obtain ⟨φ, hφ⟩ := RouteD.psu_model_equiv hp2 hadm
  obtain ⟨RJ, hRJ, hJR⟩ := P.fund _ hJΦ
  obtain ⟨RJ', hRJ', hJ'R⟩ := P.fund _ hJ'Φ
  have hi₁ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ hJR (hexeq _ hJΩ)
  have hi₂ := P.injOn_fund hp2 hadm (by trivial) (by decide) (by decide) hRJ' hJ'R
    (hexeq _ hJ'Ω)
  have hne : RJ ≠ RJ' := by
    intro h
    apply hJJ'
    rw [hJR, hJ'R, h]
  obtain ⟨x, hxRJ, hψx⟩ : ∃ x ∈ RJ, P.ψ x = u * e := by
    have : u * e ∈ RJ.map P.ψ := hJR ▸ htJ.mem
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx, hxe⟩
  obtain ⟨x', hx'RJ', hψx'⟩ : ∃ x' ∈ RJ', P.ψ x' = u * e := by
    have : u * e ∈ RJ'.map P.ψ := hJ'R ▸ htJ'.mem
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨x, hx, hxe⟩
  have hx2 : x * x = 1 := hi₁ _ (RJ.mul_mem hxRJ hxRJ) (by rw [map_mul, hψx, htJ.sq])
  have hx'2 : x' * x' = 1 := hi₂ _ (RJ'.mul_mem hx'RJ' hx'RJ') (by rw [map_mul, hψx', htJ'.sq])
  have hx1 : x ≠ 1 := fun h => htJ.ne_one (by rw [← hψx, h, map_one])
  have hx'1 : x' ≠ 1 := fun h => htJ'.ne_one (by rw [← hψx', h, map_one])
  have hc : x' * x⁻¹ ∈ Subgroup.center (modelUniv .PSU 4 p f Fact.out).K :=
    P.ker_le (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψx, hψx', mul_inv_cancel])
  have hR₁ : RJ.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by norm_num : 2 ≤ 4) := (hφ RJ).mp hRJ
  have hR₁' : RJ'.map φ.toMonoidHom ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p)
      (f := f) (by norm_num : 2 ≤ 4) := (hφ RJ').mp hRJ'
  have hne₁ : RJ.map φ.toMonoidHom ≠ RJ'.map φ.toMonoidHom := fun h =>
    hne (Subgroup.map_injective φ.injective h)
  have hc₁ : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    rw [← map_inv, ← map_mul]
    exact (MulEquivClass.apply_mem_center_iff φ).2 hc
  obtain ⟨g₁, hRg, hR'g, -⟩ := ModelFacts.Orth15.OuterU4.twin_std_u hK hp2 hR₁ hR₁' hne₁
    ⟨x, hxRJ, rfl⟩ (by rw [← map_mul, hx2, map_one]) (fun h => hx1 (φ.injective
      (h.trans (map_one φ).symm))) ⟨x', hx'RJ', rfl⟩ (by rw [← map_mul, hx'2, map_one])
    (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc₁
  set ψ₁ : Su (GaloisField p (2 * f)) p f 4 →* G :=
    (P.ψ.comp φ.symm.toMonoidHom).comp (MulAut.conj g₁).toMonoidHom with hψ₁
  have hker₀ : (P.ψ.comp φ.symm.toMonoidHom).ker ≤
      Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    intro y hy
    have h1 : φ.symm y ∈ P.ψ.ker := hy
    have h2' := (MulEquivClass.apply_mem_center_iff φ).2 (P.ker_le h1)
    rw [MulEquiv.apply_symm_apply] at h2'
    exact h2'
  have hker : ψ₁.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) :=
    ker_comp_mulEquiv_le_center hker₀ (MulAut.conj g₁)
  have hrange : ψ₁.range = exactLayer Ω e := by
    rw [T7Z.exactLayer_eq_omegaGen, ← P.range_eq]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨φ.symm (g₁ * x * g₁⁻¹), rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨g₁⁻¹ * φ x * g₁, ?_⟩
      show P.ψ (φ.symm (g₁ * (g₁⁻¹ * φ x * g₁) * g₁⁻¹)) = P.ψ x
      have : g₁ * (g₁⁻¹ * φ x * g₁) * g₁⁻¹ = φ x := by group
      rw [this, MulEquiv.symm_apply_apply]
  have hmapφ : ∀ L : Subgroup (modelUniv .PSU 4 p f Fact.out).K,
      (L.map φ.toMonoidHom).map (P.ψ.comp φ.symm.toMonoidHom) = L.map P.ψ := by
    intro L
    rw [Subgroup.map_map]
    congr 1
    ext y
    simp
  have hJ0 : (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ = conjSub g K := by
    rw [hJR, ← hmapφ RJ, hRg]
    exact (Subgroup.map_map _ _ _).symm
  have hJ'0 : (blockEmb (GaloisField p (2 * f)) p f 4 2 2 (by norm_num)).range.map ψ₁ =
      conjSub g K' := by
    rw [hJ'R, ← hmapφ RJ', hR'g]
    exact (Subgroup.map_map _ _ _).symm
  have hu : u ∈ ψ₁.range := by
    rw [hrange, T7Z.exactLayer_eq_omegaGen]
    exact hue
  obtain ⟨y, hy⟩ := hu
  obtain ⟨l, hl, hl4⟩ := exists_norm_one_pow_four hK hq
  set T := su4TorusElt (GaloisField p (2 * f)) p f l hl with hT
  have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf0
  have hcardk : Nat.card (fixedSubfield (GaloisField p (2 * f)) p f) = p ^ f :=
    card_fixedSubfield hK
  obtain ⟨ε⟩ : Nonempty (GaloisField p f ≃+* fixedSubfield (GaloisField p (2 * f)) p f) := by
    have := Fintype.ofFinite (GaloisField p f)
    have := Fintype.ofFinite (fixedSubfield (GaloisField p (2 * f)) p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF, hcardk])⟩
  have hperf : Group.IsPerfect SL(2, GaloisField p f) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ hF4
  have hyR : ∀ A : Su (GaloisField p (2 * f)) p f 2,
      y * blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by norm_num) A =
        blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by norm_num) A * y := by
    obtain ⟨ν, hνinj, hνrange, -⟩ := exists_natChart hK hp2 ε
    have key := hom_eq_of_central_ker_perfect (G := SL(2, GaloisField p f)) hker
      ((MulAut.conj y).toMonoidHom.comp ν) ν (fun s => by
        have hmem : ψ₁ (ν s) ∈ conjSub g K := by
          rw [← hJ0]
          exact ⟨ν s, by rw [← hνrange]; exact ⟨s, rfl⟩, rfl⟩
        have hcomm : u * ψ₁ (ν s) = ψ₁ (ν s) * u :=
          (Subgroup.mem_centralizer_singleton_iff.mp (hJu hmem)).symm
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
          map_inv, hy, hcomm]
        group)
    intro A
    have hA : blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by norm_num) A ∈ ν.range := by
      rw [hνrange]
      exact ⟨A, rfl⟩
    obtain ⟨s, hs⟩ := hA
    have h3 := DFunLike.congr_fun key s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h3
    rw [← hs]
    calc y * ν s = (y * ν s * y⁻¹) * y := by group
      _ = ν s * y := by rw [h3]
  have hau : ψ₁ T * u = u * ψ₁ T := by
    rw [← hy, ← map_mul, ← map_mul, su4TorusElt_comm_of_comm_block hK hp2 hq l hl y hyR]
  have hcJ : ∀ x ∈ conjSub g K, ψ₁ T * x = x * ψ₁ T := by
    intro x hx
    rw [← hJ0] at hx
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
    rw [← map_mul, ← map_mul, ← su4TorusElt_comm_blockEmb l hl A]
  have hcJ' : ∀ x ∈ conjSub g K', ψ₁ T * x = x * ψ₁ T := by
    intro x hx
    rw [← hJ'0] at hx
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
    rw [← map_mul, ← map_mul, ← su4TorusElt_comm_blockEmb_two l hl A]
  have hza : ψ₁ T * z₁ = z₁ * ψ₁ T := hclaim _ hau hcJ hcJ'
  have hz₁inv : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁2
  have hz₁c : z₁ ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hz₁e
  have hτ : ∀ x : G, (MulAut.conj z₁) ((MulAut.conj z₁) x) = x := by
    intro x
    simp only [MulAut.conj_apply, hz₁inv]
    calc z₁ * (z₁ * x * z₁) * z₁ = (z₁ * z₁) * x * (z₁ * z₁) := by group
      _ = x := by rw [hz₁2]; simp
  have hstab : ∀ x, (MulAut.conj z₁) (ψ₁ x) ∈ ψ₁.range := by
    intro x
    have h1 := conjSub_exactLayer hst.hyp.conjInvariant hz₁c
    have h2' : z₁ * ψ₁ x * z₁⁻¹ ∈ conjSub z₁ (exactLayer Ω e) :=
      conj_mem_conjSub (by rw [← hrange]; exact ⟨x, rfl⟩)
    rw [h1, ← hrange] at h2'
    exact h2'
  have hθ' : θ.range = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ :=
    hθ.trans hJ0.symm
  have hθτ' : ∀ s, (MulAut.conj z₁) (θ s) = θ (diagConj2 (-1) 1 s) := fun s => hθτ s
  have hT' : (MulAut.conj z₁) (ψ₁ T) = ψ₁ T := by
    simp only [MulAut.conj_apply]
    rw [← hza]
    group
  have hlin : LinearLift ψ₁ (MulAut.conj z₁) :=
    linearLift_of_torus_fixed hK hp2 hq ε ψ₁ hker (MulAut.conj z₁) hτ hstab θ hθ' (-1) hθτ' l hl
      hl4 hT'
  have hg6 := RouteD.spinMinus6Generated_galois (p := p) (f := f) hp2
  have := fact_shortField (minusCoeffs_irr p f)
  obtain ⟨S, W₃, hpair, hRS, hfix⟩ := exists_fixed_shortPair_linear hp2 hq hq3 hg6 ψ₁ hker
    (MulAut.conj z₁) hτ
    (R := rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4))
    ⟨_, isLongRootSU2_standard (by norm_num : 2 ≤ 4)⟩ θ hθ' hθτ' hlin
  have hpair' : TwistedB2BlockPair (minusCoeffs_irr p f) W₃ (conjSub g K) (S.map ψ₁) := by
    rw [← hJ0]
    exact hpair
  refine ⟨S.map ψ₁, ⟨_, hpair'⟩, ?_, (RouteD.twistedB2BlockPair_perfect hF4 hpair').2, ?_, ?_, ?_,
    ?_⟩
  · rintro _ ⟨y₀, hy₀, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := hfix y₀ hy₀
    simp only [MulAut.conj_apply] at h
    calc ψ₁ y₀ * z₁ = (z₁ * ψ₁ y₀ * z₁⁻¹) * z₁ := by rw [h]
      _ = z₁ * ψ₁ y₀ := by group
  · rw [← hrange]
    exact Subgroup.map_le_range ψ₁ S
  · rw [← hrange, MonoidHom.range_eq_map, ← hRS, Subgroup.map_sup, hJ0]
  · rw [T7Z.exactLayer_eq_omegaGen]
    exact le_omegaGen hJΦ
  · rw [T7Z.exactLayer_eq_omegaGen]
    exact le_omegaGen hJ'Φ

end CHN

end CFSG.ClassicalInvolution.Asc77

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAGen2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL4Def
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL5Def
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSL
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
  CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped MatrixGroups commutatorElement

section Generic

variable {G Y : Type} [Group G] [Group Y]

theorem ka_orth_le_fixSub (π : G →* Y) (φ : G →* G) {α : MulAut Y}
    (hφ : ∀ g, α (π g) = π (φ g)) {S : Subgroup G} (hfix : ∀ g ∈ S, φ g = g) :
    S.map π ≤ fixSub α := by
  rintro _ ⟨g, hg, rfl⟩
  rw [mem_fixSub, hφ, hfix g hg]

theorem ka_orth_perfect_map (π : G →* Y) {S : Subgroup G} (hperf : ⁅S, S⁆ = S) :
    ⁅S.map π, S.map π⁆ = S.map π := by
  rw [← Subgroup.map_commutator, hperf]

theorem ka_orth_mem_normalizer_map (π : G →* Y) {T N : Subgroup G}
    (hN : ∀ h ∈ T, ∀ g ∈ N, h * g * h⁻¹ ∈ N) {h : G} (hh : h ∈ T) :
    π h ∈ normalizer ((N.map π : Subgroup Y) : Set Y) := by
  have key : ∀ k ∈ T, ∀ y ∈ N.map π, π k * y * (π k)⁻¹ ∈ N.map π := by
    intro k hk
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨k * g * k⁻¹, hN k hk g hg, by simp only [map_mul, map_inv]⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key h hh y, fun hy => ?_⟩
  have h1 := key h⁻¹ (T.inv_mem hh) _ hy
  have h2 : π h⁻¹ * (π h * y * (π h)⁻¹) * (π h⁻¹)⁻¹ = y := by
    rw [map_inv]
    group
  rw [h2] at h1
  exact h1

theorem ka_orth_normalizes (π : G →* Y) (hπ : Function.Surjective π) (φ : G →* G) {α : MulAut Y}
    (hφ : ∀ g, α (π g) = π (φ g)) {S : Subgroup G}
    (hnorm : ∀ h : G, π (φ h) = π h → ∀ g ∈ S, h * g * h⁻¹ ∈ S) :
    ∀ x ∈ fixSub α, x ∈ normalizer ((S.map π : Subgroup Y) : Set Y) := by
  intro x hx
  obtain ⟨h, rfl⟩ := hπ x
  have hfix : π (φ h) = π h := by
    rw [← hφ]
    exact mem_fixSub.1 hx
  exact ka_orth_mem_normalizer_map π (T := MonoidHom.eqLocus (π.comp φ) π) (N := S)
    (fun k hk g hg => hnorm k hk g hg) hfix

theorem ka_orth_central_of_components [Finite Y] (π : G →* Y) {S : Subgroup G} {m : ℕ}
    (Fq : Fin m → Subgroup G) (hq : ∀ i, IsQuasisimple (Fq i)) (hle : ∀ i, Fq i ≤ S)
    (hsup : S ≤ ⨆ i, Fq i) (hFn : ∀ i, ∀ h ∈ S, ∀ g ∈ Fq i, h * g * h⁻¹ ∈ Fq i)
    {p : ℕ} (hp : p.Prime) (M : Subgroup Y) (hML : M ≤ S.map π) (hMp : IsPGroup p ↥M)
    (hMn : ∀ l ∈ S.map π, l ∈ normalizer (M : Set Y)) :
    ∀ x ∈ M, ∀ l ∈ S.map π, x * l = l * x := by
  have hcomp : ∀ i, ∀ x ∈ M, ∀ l ∈ (Fq i).map π, x * l = l * x := by
    intro i
    have hrange : (π.comp (Fq i).subtype).range = (Fq i).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have hperf : ⁅(Fq i).map π, (Fq i).map π⁆ = (Fq i).map π := by
      rw [← Subgroup.map_commutator,
        CFSG.ComponentClassification.Burgoyne.PSL.commutator_eq_self_of_isQuasisimple (hq i)]
    have hcen := ka_central_of_quasisimple_image (π.comp (Fq i).subtype) (hq i) hp
    rw [hrange] at hcen
    refine ka_centralizes_of_perfect ((Fq i).map π) M hperf
      (fun l hl => hMn l (Subgroup.map_mono (hle i) hl)) (fun x hx => ?_) hMp
      (fun M' hM'le hM'p hM'n => hcen M' hM'le hM'p hM'n)
    obtain ⟨h, hh, rfl⟩ := hML hx
    exact ka_orth_mem_normalizer_map π (hFn i) hh
  have hsub : S.map π ≤ Subgroup.centralizer (M : Set Y) := by
    calc S.map π ≤ (⨆ i, Fq i).map π := Subgroup.map_mono hsup
      _ = ⨆ i, (Fq i).map π := Subgroup.map_iSup _ _
      _ ≤ Subgroup.centralizer (M : Set Y) := iSup_le fun i l hl => by
          rw [Subgroup.mem_centralizer_iff]
          exact fun x hx => hcomp i x hx l hl
  intro x hx l hl
  exact Subgroup.mem_centralizer_iff.1 (hsub hl) x hx

theorem ka_orth_all_of_components [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (π : G →* Y) (hπ : Function.Surjective π) (φ : G →* G) {α : MulAut Y}
    (hφ : ∀ g, α (π g) = π (φ g)) {S : Subgroup G} (hfix : ∀ g ∈ S, φ g = g)
    (hnorm : ∀ h : G, π (φ h) = π h → ∀ g ∈ S, h * g * h⁻¹ ∈ S) (hperf : ⁅S, S⁆ = S) {m : ℕ}
    (Fq : Fin m → Subgroup G) (hq : ∀ i, IsQuasisimple (Fq i)) (hle : ∀ i, Fq i ≤ S)
    (hsup : S ≤ ⨆ i, Fq i) (hFn : ∀ i, ∀ h ∈ S, ∀ g ∈ Fq i, h * g * h⁻¹ ∈ Fq i)
    (hrig : KARigidComm α (S.map π)) : KAAll α :=
  ka_all_of_normal_comm hinj (S.map π) (ka_orth_le_fixSub π φ hφ hfix)
    (ka_orth_perfect_map π hperf) (ka_orth_normalizes π hπ φ hφ hnorm)
    (fun _ hp _ M hML hMp hMn => ka_orth_central_of_components π Fq hq hle hsup hFn hp M hML hMp
      hMn) hrig

end Generic

theorem ka_all_of_orth_nf {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hK : ringChar F ≠ 2) {w : Fin n → F} (hw : OrthNF w)
    (hdata : OrthComponentData n F (diagGL hw.1)) :
    KAAll (conjAut n F (diagGL hw.1)⁻¹ * dualAut n F) := by
  have : Fintype F := Fintype.ofFinite F
  set R := diagGL hw.1
  set A := R⁻¹
  have hAR : A⁻¹ = R := inv_inv R
  set I := CatalogueBGraphForm.isometryGroup n F R
  set Ω := ⁅I, I⁆
  obtain ⟨hperf, m, Lc, hsup, hL⟩ := hdata
  set ΩS := Ω.comap SpecialLinearGroup.toGL
  have hmapΩ : ΩS.map SpecialLinearGroup.toGL = Ω := map_comap_toGL_of_le_commutator le_rfl
  have hF1 : ∀ g ∈ ΩS, graphLift A g = g := by
    intro g hg
    rw [graphLift_eq_iff, hAR]
    exact commutator_le_self I hg
  have hF2 : ∀ h : SpecialLinearGroup (Fin n) F, h⁻¹ * graphLift A h ∈ scalars n F →
      ∀ g ∈ ΩS, h * g * h⁻¹ ∈ ΩS := by
    intro h hh g hg
    obtain ⟨z, hz⟩ := graphLiftGL_toGL_of_scalar hh
    change SpecialLinearGroup.toGL (h * g * h⁻¹) ∈ Ω
    rw [map_mul, map_mul, map_inv]
    have hg' : SpecialLinearGroup.toGL g ∈ ⁅CatalogueBGraphForm.isometryGroup n F A⁻¹,
        CatalogueBGraphForm.isometryGroup n F A⁻¹⁆ := by rw [hAR]; exact hg
    have := conj_mem_commutator_isometryGroup hz hg'
    rwa [hAR] at this
  have hperfS : ⁅ΩS, ΩS⁆ = ΩS := by
    apply Subgroup.map_injective SpecialLinearGroup.toGL_injective
    rw [map_commutator, hmapΩ, hperf]
  have hFq : ∀ i, IsQuasisimple ((Lc i).comap SpecialLinearGroup.toGL) := by
    intro i
    obtain ⟨hq, hLΩ, -⟩ := hL i
    set Fi := (Lc i).comap SpecialLinearGroup.toGL
    have hmap : Fi.map SpecialLinearGroup.toGL = Lc i := map_comap_toGL_of_le_commutator hLΩ
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((Fi.equivMapOfInjective _ SpecialLinearGroup.toGL_injective).trans
        (MulEquiv.subgroupCongr hmap)).symm hq
  have hFle : ∀ i, (Lc i).comap SpecialLinearGroup.toGL ≤ ΩS := fun i => comap_mono (hL i).2.1
  have hFn : ∀ i, ∀ h ∈ ΩS, ∀ g ∈ (Lc i).comap SpecialLinearGroup.toGL,
      h * g * h⁻¹ ∈ (Lc i).comap SpecialLinearGroup.toGL := by
    intro i h hh g hg
    change SpecialLinearGroup.toGL (h * g * h⁻¹) ∈ Lc i
    rw [map_mul, map_mul, map_inv]
    exact (hL i).2.2 _ hh _ hg
  have hΩsup : ΩS ≤ ⨆ i, (Lc i).comap SpecialLinearGroup.toGL := by
    have h1 : (⨆ i, (Lc i).comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL = Ω := by
      rw [Subgroup.map_iSup]
      exact (iSup_congr fun i => map_comap_toGL_of_le_commutator (hL i).2.1).trans hsup
    intro g hg
    have hmem : SpecialLinearGroup.toGL g ∈
        (⨆ i, (Lc i).comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL := by
      rw [h1]
      exact hg
    obtain ⟨g', hg', hgg'⟩ := hmem
    rwa [SpecialLinearGroup.toGL_injective hgg'] at hg'
  have hinj := CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (k := F) (n := n) hn
  refine ka_orth_all_of_components hinj (proj n F) (proj_surjective n F) (graphLift A)
    (fun g => conjAut_mul_dualAut_proj A g) hF1
    (fun h hh => hF2 h (proj_eq_proj_iff.1 hh.symm)) hperfS
    (fun i => (Lc i).comap SpecialLinearGroup.toGL) hFq hFle hΩsup hFn ?_
  intro p hp hp2 e hpg hc hfixL
  have hodd : Odd (orderOf e) := ka_odd_of_mem_pGroup hp hp2 hpg (Subgroup.mem_zpowers e)
  obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hfix : ∀ g ∈ ΩS, (conjAut n F D * fieldAut n F τ) (proj n F g) = proj n F g :=
    fun g hg => hfixL _ ⟨g, hg, rfl⟩
  have hex : ∀ G ∈ Ω, (D : Matrix (Fin n) (Fin n) F) * (G : Matrix (Fin n) (Fin n) F).map τ *
      ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = G := by
    intro G hG
    set g : SpecialLinearGroup (Fin n) F := ⟨(G : Matrix (Fin n) (Fin n) F),
      det_eq_one_of_mem_commutator hG⟩
    have hg : g ∈ ΩS := by
      change SpecialLinearGroup.toGL g ∈ Ω
      have : SpecialLinearGroup.toGL g = G := Units.ext rfl
      rw [this]
      exact hG
    have h := slConj_map_eq_of_commutator_eq hperfS hfix hg
    have := congrArg (fun x : SpecialLinearGroup (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) h
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at this
    exact this
  exact orth_centralizer hK hn hw hodd hc hex

theorem ka_orth_congr_eq {Y : Type} [Group Y] (e β : MulAut Y) :
    MulAut.congr e β = e * β * e⁻¹ := by
  ext y
  simp [MulAut.congr_apply]

theorem ka_all_of_orth {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F]
    (hK : ringChar F ≠ 2) (A : GL (Fin n) F) (hA : (A : Matrix (Fin n) (Fin n) F)ᵀ = A)
    (hdata : ∀ (w : Fin n → F) (hw : OrthNF w),
      (∃ P : GL (Fin n) F, (P : Matrix (Fin n) (Fin n) F)ᵀ *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * P = Matrix.diagonal w) →
      OrthComponentData n F (diagGL hw.1)) :
    KAAll (conjAut n F A * dualAut n F) := by
  have hR := inv_transpose_of_transpose_eq A hA
  obtain ⟨P, w, hw, hP⟩ := exists_orth_normal_form hK hn A⁻¹ hR
  set H := P⁻¹ with hH
  have hHA : H * A * GeneralLinearGroup.inverseTranspose H⁻¹ = (diagGL hw.1)⁻¹ := by
    have hT : CatalogueBGraphForm.glTranspose n F P * A⁻¹ * P = diagGL hw.1 := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix, coe_diagGL]
      exact hP
    have hT' : CatalogueBGraphForm.glTranspose n F P =
        (GeneralLinearGroup.inverseTranspose P)⁻¹ := rfl
    rw [← hT, hT', hH, inv_inv]
    group
  have key := ka_all_of_orth_nf hn hK hw (hdata w hw ⟨P, hP⟩)
  have hconj : conjAut n F H * (conjAut n F A * dualAut n F) * (conjAut n F H)⁻¹ =
      conjAut n F (diagGL hw.1)⁻¹ * dualAut n F := by
    rw [conjAut_mul_conjAut_dualAut_mul_inv, hHA]
  have h1 := KAAll.of_mulEquiv (conjAut n F H⁻¹) key
  have h2 : MulAut.congr (conjAut n F H⁻¹) (conjAut n F (diagGL hw.1)⁻¹ * dualAut n F) =
      conjAut n F A * dualAut n F := by
    rw [ka_orth_congr_eq, ← hconj, map_inv]
    group
  rwa [h2] at h1

theorem kaL4GOrth_thm : KAL4GOrth := by
  intro F _ _ hK h5 A hA
  refine ka_all_of_orth (n := 4) (by norm_num) hK A hA fun w hw _ => ?_
  have hRsym : ((diagGL hw.1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = diagGL hw.1 := by
    rw [coe_diagGL, diagonal_transpose]
  exact orthComponentData hK (by norm_num) _ hRsym fun h => by omega

theorem kaL5GOrth_thm : KAL5GOrth := by
  intro F _ _ hK A hA
  refine ka_all_of_orth (n := 5) (by norm_num) hK A hA fun w hw _ => ?_
  have hRsym : ((diagGL hw.1 : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)ᵀ = diagGL hw.1 := by
    rw [coe_diagGL, diagonal_transpose]
  exact orthComponentData hK (by norm_num) _ hRsym fun h => by omega

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

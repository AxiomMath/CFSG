module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLOrthCore
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLGraph

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.PSL

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open scoped MatrixGroups commutatorElement

variable {n : ℕ} {K : Type} [Field K]

@[expose] def graphLiftGL (A : GL (Fin n) K) : GL (Fin n) K →* GL (Fin n) K :=
  (MulAut.conj A).toMonoidHom.comp GeneralLinearGroup.inverseTranspose.toMonoidHom

theorem toGL_graphLift' (A : GL (Fin n) K) (g : SpecialLinearGroup (Fin n) K) :
    SpecialLinearGroup.toGL (graphLift A g) = graphLiftGL A (SpecialLinearGroup.toGL g) :=
  toGL_graphLift A g

theorem graphLiftGL_eq_iff (A X : GL (Fin n) K) :
    graphLiftGL A X = X ↔ X ∈ CatalogueBGraphForm.isometryGroup n K A⁻¹ := by
  change A * GeneralLinearGroup.inverseTranspose X * A⁻¹ = X ↔
    CatalogueBGraphForm.glTranspose n K X * A⁻¹ * X = A⁻¹
  have hT : CatalogueBGraphForm.glTranspose n K X =
      (GeneralLinearGroup.inverseTranspose X)⁻¹ := rfl
  rw [hT]
  set Y := GeneralLinearGroup.inverseTranspose X
  constructor
  · intro h
    rw [← h]
    group
  · intro h
    calc A * Y * A⁻¹ = A * Y * (Y⁻¹ * A⁻¹ * X) := by rw [h]
      _ = X := by group

theorem conj_mem_isometryGroup_of_scalar {A H : GL (Fin n) K} {z : Kˣ}
    (hH : graphLiftGL A H = H * GeneralLinearGroup.scalar (Fin n) z) {X : GL (Fin n) K}
    (hX : X ∈ CatalogueBGraphForm.isometryGroup n K A⁻¹) :
    H * X * H⁻¹ ∈ CatalogueBGraphForm.isometryGroup n K A⁻¹ := by
  rw [← graphLiftGL_eq_iff] at hX ⊢
  have hz : ∀ Y : GL (Fin n) K, GeneralLinearGroup.scalar (Fin n) z * Y =
      Y * GeneralLinearGroup.scalar (Fin n) z := fun Y => by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  rw [map_mul, map_mul, map_inv, hH, hX]
  calc H * GeneralLinearGroup.scalar (Fin n) z * X * (H * GeneralLinearGroup.scalar (Fin n) z)⁻¹
      = H * (GeneralLinearGroup.scalar (Fin n) z * X) *
        (GeneralLinearGroup.scalar (Fin n) z)⁻¹ * H⁻¹ := by group
    _ = H * X * H⁻¹ := by rw [hz]; group

theorem conj_mem_commutator_isometryGroup {A H : GL (Fin n) K} {z : Kˣ}
    (hH : graphLiftGL A H = H * GeneralLinearGroup.scalar (Fin n) z) {X : GL (Fin n) K}
    (hX : X ∈ ⁅CatalogueBGraphForm.isometryGroup n K A⁻¹,
      CatalogueBGraphForm.isometryGroup n K A⁻¹⁆) :
    H * X * H⁻¹ ∈ ⁅CatalogueBGraphForm.isometryGroup n K A⁻¹,
      CatalogueBGraphForm.isometryGroup n K A⁻¹⁆ := by
  set I := CatalogueBGraphForm.isometryGroup n K A⁻¹
  have hle : I.map (MulAut.conj H).toMonoidHom ≤ I := by
    rintro _ ⟨Y, hY, rfl⟩
    exact conj_mem_isometryGroup_of_scalar hH hY
  have h1 : (⁅I, I⁆).map (MulAut.conj H).toMonoidHom ≤ ⁅I, I⁆ := by
    rw [map_commutator]
    exact commutator_mono hle hle
  exact h1 ⟨X, hX, rfl⟩

theorem graphLiftGL_toGL_of_scalar {A : GL (Fin n) K} {h : SpecialLinearGroup (Fin n) K}
    (hh : h⁻¹ * graphLift A h ∈ scalars n K) :
    ∃ z : Kˣ, graphLiftGL A (SpecialLinearGroup.toGL h) =
      SpecialLinearGroup.toGL h * GeneralLinearGroup.scalar (Fin n) z := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hh
  refine ⟨c, ?_⟩
  rw [← toGL_graphLift']
  have hφ : graphLift A h = h * (h⁻¹ * graphLift A h) := by rw [mul_inv_cancel_left]
  rw [hφ, map_mul]
  congr 1
  apply Units.ext
  change ((h⁻¹ * graphLift A h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
  rw [hc]
  rfl

theorem det_eq_one_of_mem_commutator {I : Subgroup (GL (Fin n) K)} {X : GL (Fin n) K}
    (hX : X ∈ ⁅I, I⁆) : (X : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hle : ⁅I, I⁆ ≤ (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    refine le_trans (commutator_mono le_top le_top) ?_
    rw [← commutator_def]
    exact Abelianization.commutator_subset_ker _
  have h1 := hle hX
  rw [MonoidHom.mem_ker, Units.ext_iff, GeneralLinearGroup.val_det_apply, Units.val_one] at h1
  exact h1

theorem map_comap_toGL_of_le_commutator {I L : Subgroup (GL (Fin n) K)} (hL : L ≤ ⁅I, I⁆) :
    (L.comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL = L := by
  refine map_comap_eq_self fun X hX => ?_
  exact ⟨⟨(X : Matrix (Fin n) (Fin n) K), det_eq_one_of_mem_commutator (hL hX)⟩, Units.ext rfl⟩

variable (n K) in
@[expose] def OrthComponentData (R : GL (Fin n) K) : Prop :=
  ⁅⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆,
      ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆⁆ =
    ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆ ∧
  ∃ (m : ℕ) (L : Fin m → Subgroup (GL (Fin n) K)),
    (⨆ i, L i) = ⁅CatalogueBGraphForm.isometryGroup n K R,
      CatalogueBGraphForm.isometryGroup n K R⁆ ∧
    ∀ i, IsQuasisimple (L i) ∧
      L i ≤ ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆ ∧
      ∀ x ∈ ⁅CatalogueBGraphForm.isometryGroup n K R, CatalogueBGraphForm.isometryGroup n K R⁆,
        ∀ l ∈ L i, x * l * x⁻¹ ∈ L i

theorem orth_oddCoreIn_eq_bot_of_data [Finite K] (hK : ringChar K ≠ 2) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)))
    {B : Subgroup (MulAut (projectiveSL n K))}
    (hB : (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range ≤ B)
    {w : Fin n → K} (hw : OrthNF w) (hdata : OrthComponentData n K (diagGL hw.1)) :
    oddCoreIn B (conjAut n K (diagGL hw.1)⁻¹ * dualAut n K) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  set R := diagGL hw.1 with hR
  set A := R⁻¹ with hA
  have hAR : A⁻¹ = R := inv_inv R
  set I := CatalogueBGraphForm.isometryGroup n K R with hI
  set Ω := ⁅I, I⁆ with hΩ
  obtain ⟨hperf, m, L, hsup, hL⟩ := hdata
  set ΩS := Ω.comap SpecialLinearGroup.toGL with hΩS
  have hmapΩ : ΩS.map SpecialLinearGroup.toGL = Ω := map_comap_toGL_of_le_commutator le_rfl
  have hF1 : ∀ g ∈ ΩS, graphLift A g = g := by
    intro g hg
    rw [graphLift_eq_iff, hAR]
    exact commutator_le_self I hg
  have hF2 : ∀ h : SpecialLinearGroup (Fin n) K, h⁻¹ * graphLift A h ∈ scalars n K →
      ∀ g ∈ ΩS, h * g * h⁻¹ ∈ ΩS := by
    intro h hh g hg
    obtain ⟨z, hz⟩ := graphLiftGL_toGL_of_scalar hh
    change SpecialLinearGroup.toGL (h * g * h⁻¹) ∈ Ω
    rw [map_mul, map_mul, map_inv]
    have hg' : SpecialLinearGroup.toGL g ∈ ⁅CatalogueBGraphForm.isometryGroup n K A⁻¹,
        CatalogueBGraphForm.isometryGroup n K A⁻¹⁆ := by rw [hAR]; exact hg
    have := conj_mem_commutator_isometryGroup hz hg'
    rwa [hAR] at this
  obtain ⟨hle, hsub⟩ := isSubnormal_map_fixed hinj hB (graphLift A) (conjAut_mul_dualAut_proj A)
    hF1 hF2
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have hfixL : ∀ i, ∀ g ∈ (L i).comap SpecialLinearGroup.toGL, y (proj n K g) = proj n K g := by
    intro i g hg
    obtain ⟨hq, hLΩ, hLn⟩ := hL i
    set F := (L i).comap SpecialLinearGroup.toGL with hF
    have hFΩ : F ≤ ΩS := comap_mono hLΩ
    have hFq : IsQuasisimple F := by
      have hmap : F.map SpecialLinearGroup.toGL = L i := map_comap_toGL_of_le_commutator hLΩ
      exact LocalCores.isQuasisimple_of_mulEquiv ((F.equivMapOfInjective _
        SpecialLinearGroup.toGL_injective).trans (MulEquiv.subgroupCongr hmap)).symm hq
    have hFimq : IsQuasisimple (F.map (conjProj n K)) := by
      refine LocalCores.isQuasisimple_map hFq _ fun hker => ?_
      have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
        intro a ha b hb
        have ha' : a ∈ scalars n K := by
          have h1 : conjProj n K a = 1 := hker ha
          exact proj_eq_one_iff.1 (hinj (by rw [map_one]; exact h1))
        exact (mem_center_iff.1 (scalars_le_center n K ha') b).symm
      have : Nontrivial F := LocalCores.isQuasisimple_nontrivial hFq
      have hcomm : commutator F = ⊥ := by
        rw [eq_bot_iff, _root_.commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext (hFab a a.2 b b.2)
      have hperfF := hFq.1.commutator_eq_top
      rw [hcomm] at hperfF
      exact bot_ne_top hperfF
    have hFsub : ((F.map (conjProj n K)).subgroupOf
        (B ⊓ centralizer ({conjAut n K A * dualAut n K} : Set _))).IsSubnormal := by
      refine isSubnormal_subgroupOf_of_normalizes (map_mono hFΩ) ?_ hsub
      rintro _ ⟨h, hh, rfl⟩ _ ⟨g', hg', rfl⟩
      refine ⟨h * g' * h⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      change SpecialLinearGroup.toGL (h * g' * h⁻¹) ∈ L i
      rw [map_mul, map_mul, map_inv]
      exact hLn _ hh _ hg'
    exact apply_proj_eq_of_commute hinj (commute_of_mem_pPrimeCore ((map_mono hFΩ).trans hle)
      hFimq hFsub (even_card_of_isQuasisimple hFimq) hy ⟨g, hg, rfl⟩)
  have hΩsup : ΩS ≤ ⨆ i, (L i).comap SpecialLinearGroup.toGL := by
    have h1 : (⨆ i, (L i).comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL = Ω := by
      rw [Subgroup.map_iSup]
      exact (iSup_congr fun i => map_comap_toGL_of_le_commutator (hL i).2.1).trans hsup
    intro g hg
    have hmem : SpecialLinearGroup.toGL g ∈
        (⨆ i, (L i).comap SpecialLinearGroup.toGL).map SpecialLinearGroup.toGL := by
      rw [h1]
      exact hg
    obtain ⟨g', hg', hgg'⟩ := hmem
    rwa [SpecialLinearGroup.toGL_injective hgg'] at hg'
  have hfix : ∀ g ∈ ΩS, y (proj n K g) = proj n K g := by
    have hsubgrp : (⨆ i, (L i).comap SpecialLinearGroup.toGL) ≤
        MonoidHom.eqLocus (y.toMonoidHom.comp (proj n K)) (proj n K) :=
      iSup_le fun i g hg => hfixL i g hg
    exact fun g hg => hsubgrp (hΩsup hg)
  obtain ⟨D, τ, rfl⟩ := exists_semilinear_of_odd hn hodd
  have hperfS : ⁅ΩS, ΩS⁆ = ΩS := by
    apply Subgroup.map_injective SpecialLinearGroup.toGL_injective
    rw [map_commutator, hmapΩ, hperf]
  have hex : ∀ G ∈ Ω, (D : Matrix (Fin n) (Fin n) K) * (G : Matrix (Fin n) (Fin n) K).map τ *
      ((D⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = G := by
    intro G hG
    set g : SpecialLinearGroup (Fin n) K := ⟨(G : Matrix (Fin n) (Fin n) K),
      det_eq_one_of_mem_commutator hG⟩
    have hg : g ∈ ΩS := by
      change SpecialLinearGroup.toGL g ∈ Ω
      have : SpecialLinearGroup.toGL g = G := Units.ext rfl
      rw [this]
      exact hG
    have h := slConj_map_eq_of_commutator_eq hperfS hfix hg
    have := congrArg (fun x : SpecialLinearGroup (Fin n) K => (x : Matrix (Fin n) (Fin n) K)) h
    simp only [CatalogueBHigherLinearAction.slConjugation_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at this
    exact this
  exact orth_centralizer hK hn hw hodd (commute_of_mem_oddCoreIn hy) hex

end CFSG.ComponentClassification.Burgoyne.PSL

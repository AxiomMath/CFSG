module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutUnitary
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.FinalTheorem
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def CentralizerInnerAt (S : Subgroup G) : Prop :=
  ∀ α : MulAut G, (∀ s ∈ S, α s = s) → ∃ t ∈ S, α = MulAut.conj t

open AutTransport in
theorem CentralizerInnerAt.map_mulEquiv {G' : Type*} [Group G'] {S : Subgroup G}
    (h : CentralizerInnerAt S) (e : G ≃* G') : CentralizerInnerAt (S.map e.toMonoidHom) := by
  intro α' hα'
  set α := (MulAut.congr e).symm α' with hαdef
  have hα'eq : α' = MulAut.congr e α := by rw [hαdef, MulEquiv.apply_symm_apply]
  have happ : ∀ g, α g = e.symm (α' (e g)) := fun g => congr_symm_apply' e α' g
  have hα : ∀ s ∈ S, α s = s := by
    intro s hs
    rw [happ, hα' _ ((mem_map_iff e).mpr hs), MulEquiv.symm_apply_apply]
  obtain ⟨t, ht, hαt⟩ := h α hα
  exact ⟨e t, (mem_map_iff e).mpr ht, by rw [hα'eq, hαt, congr_conj]⟩

theorem centralizerInnerAt_of_one_sylow [Finite G] (R : Sylow 2 G)
    (h : CentralizerInnerAt (R : Subgroup G)) (T : Sylow 2 G) :
    CentralizerInnerAt (T : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  have hT : (T : Subgroup G) = (R : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.map_mulEquiv (MulAut.conj g)

theorem centralizerInnerAt_of_mulEquiv [Finite G] {G' : Type*} [Group G'] (e : G ≃* G')
    (hG' : ∀ T : Sylow 2 G', CentralizerInnerAt (T : Subgroup G')) (T : Sylow 2 G) :
    CentralizerInnerAt (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (hG' (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map_mulEquiv e.symm
  have h' : CentralizerInnerAt (((T : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom) := h
  rw [Subgroup.map_map] at h'
  convert h'
  ext x
  simp

theorem mul_comm_of_centralizerInnerAt {S : Subgroup G} (h : CentralizerInnerAt S)
    {α β : MulAut G} (hα : ∀ s ∈ S, α s = s) (hβ : ∀ s ∈ S, β s = s) : α * β = β * α := by
  obtain ⟨t, ht, rfl⟩ := h α hα
  obtain ⟨t', ht', rfl⟩ := h β hβ
  have htt' : t * t' = t' * t := by
    have h1 := hα t' ht'
    rw [MulAut.conj_apply] at h1
    calc t * t' = t * t' * t⁻¹ * t := by group
      _ = t' * t := by rw [h1]
  rw [← map_mul, ← map_mul, htt']

open scoped MatrixGroups in
theorem centralizerInnerAt_psl2 {f : ℕ} (hf : 2 ≤ f) [Finite PSL(2, GaloisField 2 f)]
    (T : Sylow 2 PSL(2, GaloisField 2 f)) :
    CentralizerInnerAt (T : Subgroup PSL(2, GaloisField 2 f)) := by
  intro α hα
  have hB := CFSG.Milestones.ctgms_bender_1971_even_rank_one_model_and_strong_embedding_input_1 f hf
  obtain ⟨hSE, -, hZcard, hTcard⟩ := benderBorel_sylowCenter hB T
  have : IsSimpleGroup PSL(2, GaloisField 2 f) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
      (Or.inl ⟨f, hf, ⟨MulEquiv.refl _⟩⟩)
  have hcard : Nat.card (Sylow 2 PSL(2, GaloisField 2 f)) =
      Nat.card (T : Subgroup PSL(2, GaloisField 2 f)) + 1 := by
    rw [CFSG.Walter.psl2_even_card_sylow (by omega), hTcard, pow_one]
  have hab := le_sylowCenter_of_card (T := (T : Subgroup PSL(2, GaloisField 2 f)))
    (by rw [hZcard, hTcard, pow_one])
  exact Omega.exists_eq_conj_of_abelian hSE hcard
    (fun x hx y hy => (mem_sylowCenter.mp (hab hy)).2 x hx) α hα

open scoped MatrixGroups in
theorem centralizerInnerAt_of_mulEquiv_psl2 {X : Type*} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (e : X ≃* PSL(2, GaloisField 2 f)) (T : Sylow 2 X) :
    CentralizerInnerAt (T : Subgroup X) := by
  have : Finite PSL(2, GaloisField 2 f) := Finite.of_surjective e e.surjective
  exact centralizerInnerAt_of_mulEquiv e (centralizerInnerAt_psl2 hf) T

namespace SuzukiAut

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII

variable (m : ℕ)

theorem centralizerInnerAt_rootSub (hm : 0 < m) [Finite (SuzukiMatrixGroup m)]
    (S : Sylow 2 (SuzukiMatrixGroup m)) (hS : (S : Subgroup (SuzukiMatrixGroup m)) = rootSub m) :
    CentralizerInnerAt (S : Subgroup (SuzukiMatrixGroup m)) := by
  intro α hα
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow m hm
  obtain ⟨hSE, -, -, -⟩ := benderBorel_sylowCenter (bender_suzukiMatrixGroup_borel m hm) S
  have : IsSimpleGroup (SuzukiMatrixGroup m) := isSimpleGroup_suzukiMatrixGroup m hm
  have hHN : torusSub m ≤ Subgroup.normalizer (((S : Subgroup (SuzukiMatrixGroup m))) : Set _) := by
    rw [hS]
    exact torusSub_le_normalizer m
  rw [← hS] at hNR hcard
  have hS₁ : weyl m • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer m
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  have hHN₁ : torusSub m ≤
      Subgroup.normalizer
        ((((weyl m • S : Sylow 2 _)) : Subgroup (SuzukiMatrixGroup m)) : Set _) := by
    intro h hh
    obtain ⟨x, rfl⟩ := (mem_torusSub m hm).mp hh
    rw [Omega.mem_normalizer_conj_smul_iff, weyl_inv_conj_torus]
    exact hHN (torus_mem m x⁻¹)
  have hαS : α • S = S := Omega.smul_eq_of_mapsTo fun s hs => by rw [hα s hs]; exact hs
  obtain ⟨r, hr, hrS₁⟩ := Omega.exists_conj_adjust hSE hcard hS₁ α hαS
  set α' := (MulAut.conj r)⁻¹ * α with hα'
  have happ : ∀ g, α' g = r⁻¹ * α g * r := fun g => by
    rw [hα', MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  have hα'S : α' • S = S := by
    rw [hα', mul_smul, hαS, inv_smul_eq_iff, Omega.conj_smul_self hr]
  have hα'R : ∀ s ∈ rootSub m, α' s ∈ rootSub m := by
    intro s hs
    rw [← hS] at hs ⊢
    exact InvInner.apply_mem_of_smul_eq hα'S hs
  have hα'Z : ∀ b : BinaryGaloisField (2 * m + 1), α' (root m 0 b) = root m 0 b := by
    intro b
    have hZ : root m 0 b ∈ sylowCenter (S : Subgroup (SuzukiMatrixGroup m)) := by
      rw [hS]
      exact (mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩
    rw [happ, hα _ (sylowCenter_le _ hZ), mul_assoc, ← (mem_sylowCenter.mp hZ).2 r hr,
      inv_mul_cancel_left]
  have hα'H : ∀ x : (BinaryGaloisField (2 * m + 1))ˣ, ∃ x', α' (torus m x) = torus m x' := by
    intro x
    have h1 := Omega.mem_normalizer_smul (α := α') (hHN (torus_mem m x))
    have h2 := Omega.mem_normalizer_smul (α := α') (hHN₁ (torus_mem m x))
    rw [hα'S] at h1
    rw [hrS₁] at h2
    exact (mem_torusSub m hm).mp
      (Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2)
  have hcentral := centralizes_root m hm α' hα'R hα'Z hα'H
  have hone := Omega.eq_one_of_centralizes hSE hcard hS₁ α' hα'S hrS₁ (fun s hs => by
    rw [hS] at hs
    obtain ⟨a, b, rfl⟩ := (mem_rootSub m).mp hs
    exact hcentral a b)
  rw [hα', inv_mul_eq_one] at hone
  exact ⟨r, hr, hone.symm⟩

end SuzukiAut

open SuzukiAut CFSG.BenderSuzuki.MatrixGroups in
theorem centralizerInnerAt_of_mulEquiv_sz {X : Type*} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* Sz a) (T : Sylow 2 X) : CentralizerInnerAt (T : Subgroup X) := by
  let e'' : X ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e'' e''.surjective
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub a (by omega)
  exact centralizerInnerAt_of_mulEquiv e''
    (centralizerInnerAt_of_one_sylow S (centralizerInnerAt_rootSub a (by omega) S hS)) T

namespace UnitaryAut

open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem centralizerInnerAt_root (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hKcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hS : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryCoverRoot J hJ) :
    CentralizerInnerAt (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  classical
  intro α hα
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  have : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2 ^ f) (by omega) hKcard hfixed
  set U := hermitianUnipotentPSU J hJ with hUdef
  have hU : Function.Injective U := CFSG.BenderSuzuki.Background.hermitianUnipotentPSU_injective J hJ
  have hconjU : ∀ (k : Kˣ) (z : hermitianUnipotentCoord J),
      hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹ =
        U (hermitianTorusAction J k z) := unitaryCoverTorus_conj_root J hJ
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow J f hf hKcard hfixed hJ
  obtain ⟨hSE, -, -, -⟩ :=
    benderBorel_sylowCenter (bender_projectiveSpecialUnitary_borel J f hf hKcard hfixed hJ) S
  have hHN : unitaryCoverTorus J hJ ≤
      Subgroup.normalizer (((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) : Set _) := by
    rw [hS]
    exact unitaryCoverTorus_le_normalizer J hJ
  rw [← hS] at hNR hcard
  have hS₁ : hermitianWeylPSU J hJ • S ≠ S := by
    intro h
    apply weyl_not_mem_normalizer J (2 ^ f) hKcard hfixed hJ
    rw [← hS]
    exact (Sylow.smul_eq_iff_mem_normalizer).mp h
  have hHN₁ : unitaryCoverTorus J hJ ≤ Subgroup.normalizer
      ((((hermitianWeylPSU J hJ • S : Sylow 2 _)) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    rintro _ ⟨k, rfl⟩
    rw [Omega.mem_normalizer_conj_smul_iff]
    have h := weyl_conj_torus J hJ (Units.map J.conj.toMonoidHom k)⁻¹
    have hk : (Units.map J.conj.toMonoidHom (Units.map J.conj.toMonoidHom k)⁻¹)⁻¹ = k := by
      ext
      simp [J.conj_involutive (k : K)]
    rw [hk] at h
    have h2 : (hermitianWeylPSU J hJ)⁻¹ * hermitianTorusPSU J hJ k * hermitianWeylPSU J hJ =
        hermitianTorusPSU J hJ (Units.map J.conj.toMonoidHom k)⁻¹ := by
      rw [← h]
      group
    rw [h2]
    exact hHN ⟨_, rfl⟩
  have hRS : ∀ z, U z ∈ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := fun z => by
    rw [hS]
    exact ⟨z, rfl⟩
  have hαS : α • S = S := Omega.smul_eq_of_mapsTo fun s hs => by rw [hα s hs]; exact hs
  obtain ⟨r, hr, hrS₁⟩ := Omega.exists_conj_adjust hSE hcard hS₁ α hαS
  set α' := (MulAut.conj r)⁻¹ * α with hα'
  have hαα' : α = MulAut.conj r * α' := by rw [hα', mul_inv_cancel_left]
  have happ : ∀ g, α' g = r⁻¹ * α g * r := fun g => by
    rw [hα', MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  have hα'S : α' • S = S := by
    rw [hα', mul_smul, hαS, inv_smul_eq_iff, Omega.conj_smul_self hr]
  have hα'H : ∀ k : Kˣ, ∃ k' : Kˣ, α' (hermitianTorusPSU J hJ k) = hermitianTorusPSU J hJ k' := by
    intro k
    have h1 := Omega.mem_normalizer_smul (α := α') (hHN ⟨k, rfl⟩)
    have h2 := Omega.mem_normalizer_smul (α := α') (hHN₁ ⟨k, rfl⟩)
    rw [hα'S] at h1
    rw [hrS₁] at h2
    obtain ⟨k', hk'⟩ := Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2
    exact ⟨k', hk'.symm⟩
  obtain ⟨c, rfl⟩ : ∃ c, U c = r := by
    have h := hr
    rw [hS] at h
    exact h
  let ψ : hermitianUnipotentCoord J →* hermitianUnipotentCoord J :=
    (MulAut.conj c⁻¹).toMonoidHom
  have hψ : ∀ z, ψ z = c⁻¹ * z * c := fun z => by
    change MulAut.conj c⁻¹ z = c⁻¹ * z * c
    rw [MulAut.conj_apply, inv_inv]
  have hψU : ∀ z, U (ψ z) = α' (U z) := by
    intro z
    rw [happ, hα _ (hRS z), hψ, ← map_inv, ← map_mul, ← map_mul]
  have hψinj : Function.Injective ψ := fun z z' h => by
    rw [hψ, hψ] at h
    simpa using h
  have hψcen : ∀ z : hermitianUnipotentCoord J, z.1.1 = 0 → ψ z = z := by
    intro z hz
    rw [hψ, mul_assoc, ← (UnitaryCoord.mul_comm_iff J z c).mpr (by
      rw [hz, map_zero, mul_zero, zero_mul]), inv_mul_cancel_left]
  have hψtor : ∀ k : Kˣ, ∃ k' : Kˣ,
      ∀ z, ψ (hermitianTorusAction J k z) = hermitianTorusAction J k' (ψ z) := by
    intro k
    obtain ⟨k', hk'⟩ := hα'H k
    refine ⟨k', fun z => hU ?_⟩
    calc U (ψ (hermitianTorusAction J k z)) = α' (U (hermitianTorusAction J k z)) := hψU _
      _ = α' (hermitianTorusPSU J hJ k * U z * (hermitianTorusPSU J hJ k)⁻¹) := by
          rw [hconjU]
      _ = α' (hermitianTorusPSU J hJ k) * α' (U z) * (α' (hermitianTorusPSU J hJ k))⁻¹ := by
          rw [map_mul, map_mul, mulAut_apply_inv]
      _ = hermitianTorusPSU J hJ k' * U (ψ z) * (hermitianTorusPSU J hJ k')⁻¹ := by
          rw [hk', hψU]
      _ = U (hermitianTorusAction J k' (ψ z)) := hconjU k' (ψ z)
  obtain ⟨lam, -, hform⟩ := UnitaryCoordAut.coordAut_form J (2 ^ f) hKcard hfixed hq4 hJ ψ
    hψinj hψcen hψtor
  have hψfst : ∀ z, (ψ z).1.1 = z.1.1 := fun z => by
    rw [hψ]
    exact UnitaryCoord.inv_mul_mul_fst J c z
  have hsurj := unitaryCoverFirstCoord_surjective J (2 ^ f) hKcard hfixed hJ
  obtain ⟨z₁, hz₁⟩ := hsurj (Multiplicative.ofAdd 1)
  have hz₁1 : z₁.1.1 = 1 := congrArg Multiplicative.toAdd hz₁
  have hid : ∀ z, ψ z = z := by
    rcases hform with hid | hconj
    · have hlam : lam = 1 := by
        have h := (hid z₁).1
        rw [hψfst, hz₁1, mul_one] at h
        exact h.symm
      intro z
      apply Subtype.ext
      apply Prod.ext
      · exact hψfst z
      · exact (hid z).2
    · exfalso
      have hlam : lam = 1 := by
        have h := (hconj z₁).1
        rw [hψfst, hz₁1, map_one, mul_one] at h
        exact h.symm
      have hall : ∀ a : K, J.conj a = a := by
        intro a
        obtain ⟨z, hz⟩ := hsurj (Multiplicative.ofAdd a)
        have hz1 : z.1.1 = a := congrArg Multiplicative.toAdd hz
        have h := (hconj z).1
        rw [hψfst, hlam, one_mul, hz1] at h
        exact h.symm
      have h1 : Nat.card {x : K // J.conj x = x} = Nat.card K :=
        Nat.card_congr (Equiv.subtypeUnivEquiv hall)
      rw [hfixed, hKcard] at h1
      have h2 : 2 ^ f * 1 < 2 ^ f * 2 ^ f := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      rw [sq] at h1
      omega
  have hone := Omega.eq_one_of_centralizes hSE hcard hS₁ α' hα'S hrS₁ (fun s hs => by
    rw [hS] at hs
    obtain ⟨z, rfl⟩ := hs
    rw [← hψU, hid])
  exact ⟨U c, hRS c, by rw [hαα', hone, mul_one]⟩

end UnitaryAut

open UnitaryAut CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups in
theorem centralizerInnerAt_of_mulEquiv_psu3 {X : Type*} [Group X] [Finite X] {f : ℕ}
    (hf : 2 ≤ f) (e : X ≃* PSU3 2 f) (T : Sylow 2 X) : CentralizerInnerAt (T : Subgroup X) := by
  let k := GaloisField 2 f
  let K := FiniteField.Extension k 2 2
  let J := binaryQuadraticHermitian f (by omega)
  let : CharP K 2 := CharP.of_ringHom_of_ne_zero (algebraMap k K) 2 (by norm_num)
  have hKcard : Nat.card K = (2 ^ f) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 f (by omega)]
  have hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f :=
    quadraticBinaryFrobenius_fixed_card f (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  let e₁ := (projectiveSpecialUnitary_equiv_PSU3Model J f hf hJ hKcard hfixed).some
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e₂ : ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3 2 f :=
    e₁.trans (MulEquiv.subgroupCongr hmodel)
  let e₃ : X ≃* ProjectiveSpecialUnitaryMatrixGroup J := e.trans e₂.symm
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  obtain ⟨S, hS⟩ := exists_sylow_eq_root J f hf hKcard hfixed hJ
  exact centralizerInnerAt_of_mulEquiv e₃
    (centralizerInnerAt_of_one_sylow S (centralizerInnerAt_root J f hf hKcard hfixed hJ S hS)) T

theorem centralizerInnerAt_of_isBenderGroup {X : Type*} [Group X] [Finite X]
    (hX : fusionIsBenderGroup X) (T : Sylow 2 X) : CentralizerInnerAt (T : Subgroup X) := by
  rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · exact centralizerInnerAt_of_mulEquiv_psl2 hf e T
  · exact centralizerInnerAt_of_mulEquiv_psu3 hf e T
  · exact centralizerInnerAt_of_mulEquiv_sz ha e T

end Bender

theorem glaubermanBenderPerfect :
    ∀ (X : Type) [Group X] [Finite X], CFSG.BenderSuzuki.IsSimpleBenderGroup X →
      ∀ (S : Sylow 2 X) (K : Subgroup (MulAut X)), Group.IsPerfect K →
        (∀ α ∈ K, ∀ s ∈ (S : Subgroup X), α s = s) → K = ⊥ := by
  intro X _ _ hB S K hK hfix
  have hCI := Bender.centralizerInnerAt_of_isBenderGroup
    (CFSG.Open.fusionIsBenderGroup_of_isSimpleBenderGroup hB) S
  by_contra hne
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  have hcomm : IsMulCommutative K := ⟨⟨fun a b => Subtype.ext
    (Bender.mul_comm_of_centralizerInnerAt hCI (hfix a a.2) (hfix b b.2))⟩⟩
  exact Group.IsPerfect.not_isMulCommutative K hcomm

end CFSG.ComponentClassification.AschbacherToolkit

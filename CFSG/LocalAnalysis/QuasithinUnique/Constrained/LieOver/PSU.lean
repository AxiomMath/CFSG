module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadicalNode

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open Matrix
open scoped Pointwise

@[expose] def PSUCover : Prop :=
  ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (r ε : ℕ), 2 ≤ r → ε ≤ 1 →
    (2 * r + ε, 2 ^ f) ≠ (4, 2) →
    ∀ A : Subgroup (hypPSU h r ε), A ≠ ⊤ → hypProjUnitriangular h r ε ≤ A →
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ r ∧ A ≤ projIsoStabilizer h r ε (hypFlag h r ε d)

@[expose] def PSU42SylowFacts : Prop :=
  ∀ (K : Type) [Field K] (h : UnitaryFieldData 2 1 K),
    SylowFacts (hypPSU h 2 0) (hypProjUnitriangular h 2 0)

theorem le_isPGroup_map {G G' : Type} [Group G] [Group G'] (e : G →* G') {H : Subgroup G}
    (hH : IsPGroup 2 H) : IsPGroup 2 (H.map e) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨k, hk⟩ := hH ⟨y, hy⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : y ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, h1, map_one]

theorem le_charTwo_of_normal {G : Type} [Group G] [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    (hN2 : IsPGroup 2 N) (hNn : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N)
    (hcent : ∀ x ∈ H, (∀ n ∈ N, x * n = n * x) → x ∈ N) : CharTwo H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (N.subgroupOf H).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hNn (g : G) g.2 (a : G) ha
  have hNO : N ≤ pCoreOf 2 H := CFSG.LieType.BorelTits.le_pCoreOf 2 hNH hnorm hN2
  rintro x ⟨hxH, hxC⟩
  apply hNO
  apply hcent x hxH
  intro n hn
  exact (Subgroup.mem_centralizer_iff.mp hxC n (hNO hn)).symm

theorem le_charTwo_map {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] (e : G ≃* G')
    {H : Subgroup G} (hH : CharTwo H) : CharTwo (H.map e.toMonoidHom) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 (pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hOH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hOn : ∀ y ∈ H, ∀ o ∈ pCoreOf 2 H, y * o * y⁻¹ ∈ pCoreOf 2 H := fun y hy o ho =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hy) o).mp ho
  refine le_charTwo_of_normal (N := (pCoreOf 2 H).map e.toMonoidHom)
    (Subgroup.map_mono hOH) (le_isPGroup_map _ hO2) ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨o, ho, rfl⟩
    refine ⟨y * o * y⁻¹, hOn y hy o ho, ?_⟩
    simp
  · rintro _ ⟨y, hy, rfl⟩ hc
    have hyC : y ∈ Subgroup.centralizer ((pCoreOf 2 H : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro o ho
      have hmem : e.toMonoidHom o ∈ (pCoreOf 2 H).map e.toMonoidHom := ⟨o, ho, rfl⟩
      have h1 := hc _ hmem
      apply e.injective
      simpa using h1.symm
    exact ⟨y, hH ⟨hy, hyC⟩, rfl⟩

section Flag

abbrev leC (K : Type) [Field K] (r ε : ℕ) : GL (Fin (2 * r + ε)) K := 1

abbrev leM (K : Type) [Field K] (r ε : ℕ) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K :=
  (leC K r ε : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)

theorem le_leM_eq {K : Type} [Field K] (r ε : ℕ) : leM K r ε = 1 := by
  simp [leM, leC]

theorem le_isPrimeFormGram {K : Type} [Field K] (r ε : ℕ) : IsPrimeFormGram (leC K r ε) where
  symm := by simp [leC]
  prime i j := by
    simp only [leC, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem le_gramHyp {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R) :
    IsGramHypTransport h (leM K r ε) R := by
  unfold IsGramHypTransport
  rw [le_leM_eq, Matrix.mul_one]
  exact hR

theorem le_mul_gramHypEquiv {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (s : gramSU h (leM K r ε)) :
    R * (((gramHypEquiv h (leM K r ε) (le_gramHyp h hR) s : hypSU h r ε) :
        GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      ((s : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) * R := by
  have hc := coe_gramHypEquiv (le_gramHyp h hR) s
  have hI : R * gramHypInv h (leM K r ε) R = 1 := by
    unfold gramHypInv
    rw [le_leM_eq, Matrix.mul_one]
    exact mul_transportInv hR
  rw [hc, ← Matrix.mul_assoc R, ← Matrix.mul_assoc R, hI, Matrix.one_mul]

theorem le_stab_iff {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (F : Submodule K (HypIndex r ε → K)) (s : gramSU h (leM K r ε)) :
    (∀ v ∈ transportSubspace h hR F,
        ((s : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈
          transportSubspace h hR F) ↔
      ∀ v ∈ F, (((gramHypEquiv h (leM K r ε) (le_gramHyp h hR) s : hypSU h r ε) :
        GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ F := by
  have hKI := le_mul_gramHypEquiv h hR s
  set gm := (((gramHypEquiv h (leM K r ε) (le_gramHyp h hR) s : hypSU h r ε) :
      GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) with hgm
  set sm := ((s : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    with hsm
  have hmap : ∀ v, sm *ᵥ (R *ᵥ v) = R *ᵥ (gm *ᵥ v) := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, hKI]
  have hinj : ∀ x y, R *ᵥ x = R *ᵥ y → x = y := fun x y hxy => by
    have h1 : transportInv h R *ᵥ (R *ᵥ x) = transportInv h R *ᵥ (R *ᵥ y) := by rw [hxy]
    rwa [mulVec_mulVec, mulVec_mulVec, transportInv_mul hR, one_mulVec, one_mulVec] at h1
  rw [transportSubspace_apply]
  constructor
  · intro hs v hv
    obtain ⟨u, hu, hue⟩ := Submodule.mem_map.mp
      (hs (mulVecLin R v) (Submodule.mem_map_of_mem hv))
    have hue' : R *ᵥ u = sm *ᵥ (R *ᵥ v) := hue
    rw [hmap] at hue'
    rw [← hinj u (gm *ᵥ v) hue']
    exact hu
  · intro hF w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hw
    show sm *ᵥ (R *ᵥ v) ∈ F.map (mulVecLin R)
    rw [hmap]
    exact Submodule.mem_map_of_mem (hF v hv)

theorem le_mem_isoStabilizer_iff {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K)
    {r ε : ℕ} (g : hypSU h r ε) (F : Submodule K (HypIndex r ε → K)) :
    g ∈ isoStabilizer h r ε F ↔
      ∀ v ∈ F, ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ∈ F := by
  have hfin : Finite K := h.finite
  rw [mem_isoStabilizer, Subgroup.smul_def, smul_eq_map]
  constructor
  · intro hg v hv
    rw [← hg]
    exact Submodule.mem_map_of_mem hv
  · intro hF
    apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      exact hF v hv
    · intro x hx
      have hinj : Function.Injective fun v : HypIndex r ε → K =>
          ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v := by
        intro a b hab
        have h1 := congrArg (fun u => ((g⁻¹ : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ u) hab
        simpa [mulVec_mulVec, ← Units.val_mul] using h1
      have hgx : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
          (((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x) ∈ F := by
        rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
        exact hx
      have hmem := (mem_iff_of_mapsTo_of_finite hinj (S := (F : Set (HypIndex r ε → K))) hF _).mp
        hgx
      refine Submodule.mem_map.mpr ⟨_, hmem, ?_⟩
      show ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        (((g⁻¹ : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ x) = x
      rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem le_gramForm_one_eq {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) (n : ℕ)
    (x y : Fin n → K) :
    gramForm h (1 : Matrix (Fin n) (Fin n) K) x y = CFSG.LinearGroups.stdHermForm h n x y := by
  simp [gramForm, CFSG.LinearGroups.stdHermForm, dotProduct, Matrix.one_mulVec]

theorem le_transport_isotropic {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K)
    {r ε : ℕ} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (F : Submodule K (HypIndex r ε → K))
    (hF : ∀ x ∈ F, ∀ y ∈ F, hypForm h r ε x y = 0) :
    ∀ v ∈ transportSubspace h hR F, ∀ w ∈ transportSubspace h hR F,
      gramForm h (leM K r ε) v w = 0 := by
  intro v hv w hw
  rw [transportSubspace_apply] at hv hw
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hv
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hw
  rw [show leM K r ε = 1 from le_leM_eq r ε, le_gramForm_one_eq]
  exact (stdHermForm_transport hR x y).trans (hF x hx y hy)

theorem le_transport_ne_bot {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K)
    {r ε : ℕ} {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K} (hR : IsHypTransport h R)
    (F : Submodule K (HypIndex r ε → K)) (hF : F ≠ ⊥) :
    transportSubspace h hR F ≠ ⊥ := fun h0 =>
  hF ((transportSubspace h hR).injective (by rw [h0, OrderIso.map_bot]))

end Flag

section Conj

variable {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}

theorem le_conj_eq (a : gramSU h (leM K r ε)) :
    primeFormConjHom h (leM K r ε) (gramSUToUnitary h (leM K r ε) a) =
      MulAut.conj (QuotientGroup.mk a : primeFormP h (leM K r ε)) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

theorem le_conj_inj (hn : 3 ≤ 2 * r + ε) (a b : gramSU h (leM K r ε))
    (hab : MulAut.conj (QuotientGroup.mk a : primeFormP h (leM K r ε)) =
      MulAut.conj (QuotientGroup.mk b : primeFormP h (leM K r ε))) :
    (QuotientGroup.mk a : primeFormP h (leM K r ε)) = QuotientGroup.mk b := by
  have hC : IsPrimeFormGram (leC K r ε) := le_isPrimeFormGram r ε
  have hA1 : primeFormConjHom h (leM K r ε)
      ((gramSUToUnitary h (leM K r ε) a)⁻¹ * gramSUToUnitary h (leM K r ε) b) = 1 := by
    rw [map_mul, map_inv, le_conj_eq, le_conj_eq, hab, inv_mul_cancel]
  have hA2 := (primeFormConjHom_eq_psi h hC _).symm.trans hA1
  obtain ⟨-, c, hc, hcA⟩ := (primeFormPsi_eq_one_iff h hC hn _).mp hA2
  have hu : ((a⁻¹ * b : gramSU h (leM K r ε)) : GL (Fin (2 * r + ε)) K) =
      (((gramSUToUnitary h (leM K r ε) a)⁻¹ * gramSUToUnitary h (leM K r ε) b :
        primeFormUnitary h (leM K r ε)) : GL (Fin (2 * r + ε)) K) := rfl
  have hscal : ((a⁻¹ * b : gramSU h (leM K r ε)) : GL (Fin (2 * r + ε)) K) =
      GeneralLinearGroup.scalar (Fin (2 * r + ε)) c := by
    rw [hu]
    exact hcA
  have hdet := (((mem_gramSU_iff_unitary h).mp (a⁻¹ * b).2)).2
  have hcn : c ^ (2 * r + ε) = 1 := by
    apply Units.ext
    rw [hscal, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal] at hdet
    simpa [Finset.prod_const] using hdet
  have hmem : a⁻¹ * b ∈ normOneScalars h (gramSU h (leM K r ε)) (2 * r + ε) :=
    ⟨c, hc, hcn, hscal⟩
  exact QuotientGroup.eq.mpr hmem

end Conj

section Main

theorem le_orth_invariant {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    (A : GL (Fin (2 * r + ε)) K) (hA : A ∈ primeFormUnitary h (leM K r ε))
    (W : Submodule K (Fin (2 * r + ε) → K))
    (hW : ∀ v ∈ W, (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈ W) :
    ∀ v ∈ W.orthogonalBilin (gramForm h (leM K r ε)),
      (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v ∈
        W.orthogonalBilin (gramForm h (leM K r ε)) := by
  have hfin : Finite K := h.finite
  have hiso := (gramForm_isometry_iff h _ _).mpr (mem_primeFormUnitary.mp hA)
  have hinj : Function.Injective fun v : Fin (2 * r + ε) → K =>
      (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ v := by
    intro a b hab
    have h1 := congrArg (fun u => ((A⁻¹ : GL (Fin (2 * r + ε)) K) :
      Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ u) hab
    simpa [mulVec_mulVec, ← Units.val_mul] using h1
  have hAA : ∀ u : Fin (2 * r + ε) → K,
      (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ
        (((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ u) =
        u := by
    intro u
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hAinv : ∀ w ∈ W,
      ((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ w ∈ W := by
    intro w hw
    exact (mem_iff_of_mapsTo_of_finite hinj (S := (W : Set (Fin (2 * r + ε) → K))) hW
      (((A⁻¹ : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ w)).mp
      (by
        show _ ∈ (W : Set (Fin (2 * r + ε) → K))
        rw [hAA]
        exact hw)
  intro v hv
  change ∀ x ∈ W, gramForm h (leM K r ε) x ((A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
    *ᵥ v) = 0
  have hv' : ∀ x ∈ W, gramForm h (leM K r ε) x v = 0 := hv
  intro n hn
  rw [← hAA n, hiso]
  exact hv' _ (hAinv n hn)

theorem le_normal_radical {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    (W : Submodule K (Fin (2 * r + ε) → K)) (hn : 3 ≤ 2 * r + ε) (s : gramSU h (leM K r ε))
    (hs : ∀ v ∈ W, ((s : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
      *ᵥ v ∈ W)
    (g : isotropicRadical h (leM K r ε) W) :
    ∃ g' : isotropicRadical h (leM K r ε) W,
      (QuotientGroup.mk (g' : gramSU h (leM K r ε)) : primeFormP h (leM K r ε)) =
        QuotientGroup.mk (s * (g : gramSU h (leM K r ε)) * s⁻¹) := by
  have hC : IsPrimeFormGram (leC K r ε) := le_isPrimeFormGram r ε
  have hA : ((gramSUToUnitary h (leM K r ε) s : primeFormUnitary h (leM K r ε)) :
      GL (Fin (2 * r + ε)) K) ∈ primeFormUnitary h (leM K r ε) :=
    (gramSUToUnitary h (leM K r ε) s).2
  have hTL := le_orth_invariant h _ hA W hs
  have hnA := psi_mem_normalizer_radicalImage_of_mapsTo h hC
    (gramSUToUnitary h (leM K r ε) s) 1 hs hTL
  rw [← primeFormConjHom_eq_psi h hC] at hnA
  have hβ : radicalConjHom h (leM K r ε) W g ∈ radicalImage h (leM K r ε) W := ⟨g, rfl⟩
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.mp ((Subgroup.mem_normalizer_iff.mp hnA _).mp hβ)
  have e1 : MulAut.conj (QuotientGroup.mk (g' : gramSU h (leM K r ε)) :
      primeFormP h (leM K r ε)) = MulAut.conj (QuotientGroup.mk
        (s * (g : gramSU h (leM K r ε)) * s⁻¹) : primeFormP h (leM K r ε)) := by
    simp only [radicalConjHom_apply, le_conj_eq] at hg'
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
    exact hg'
  exact ⟨g', le_conj_inj h hn _ _ e1⟩

theorem le_centralizer_radical {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 2 f K) {r ε : ℕ}
    (W : Submodule K (Fin (2 * r + ε) → K)) (hn : 3 ≤ 2 * r + ε) (hW0 : W ≠ ⊥)
    (hWiso : ∀ v ∈ W, ∀ w ∈ W, gramForm h (leM K r ε) v w = 0) (s : gramSU h (leM K r ε))
    (hx : ∀ g : isotropicRadical h (leM K r ε) W,
      (QuotientGroup.mk s : primeFormP h (leM K r ε)) *
          (QuotientGroup.mk (g : gramSU h (leM K r ε)) : primeFormP h (leM K r ε)) =
        (QuotientGroup.mk (g : gramSU h (leM K r ε)) : primeFormP h (leM K r ε)) *
          QuotientGroup.mk s) :
    ∃ g' : isotropicRadical h (leM K r ε) W,
      (QuotientGroup.mk (g' : gramSU h (leM K r ε)) : primeFormP h (leM K r ε)) =
        QuotientGroup.mk s := by
  have hC : IsPrimeFormGram (leC K r ε) := le_isPrimeFormGram r ε
  have hcomm : MulAut.conj (QuotientGroup.mk s : primeFormP h (leM K r ε)) ∈
      Subgroup.centralizer ((radicalImage h (leM K r ε) W :
        Subgroup (MulAut (primeFormP h (leM K r ε)))) :
        Set (MulAut (primeFormP h (leM K r ε)))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro β hβ
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hβ
    have h1 := congrArg (fun y => MulAut.conj y) (hx g)
    simp only [map_mul] at h1
    rw [radicalConjHom_apply, le_conj_eq]
    exact h1.symm
  have hD : MulAut.conj (QuotientGroup.mk s : primeFormP h (leM K r ε)) ∈
      primeFormD h (leM K r ε) := by
    rw [← le_conj_eq h s]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hmem := Subgroup.mem_inf.mpr ⟨hcomm, hD⟩
  rw [centralizer_inf_primeFormD h hC hWiso hn hW0] at hmem
  obtain ⟨β, -, hβ⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp β.2
  have hβ' : (β : MulAut (primeFormP h (leM K r ε))) =
      MulAut.conj (QuotientGroup.mk s : primeFormP h (leM K r ε)) := hβ
  have e : MulAut.conj (QuotientGroup.mk (g : gramSU h (leM K r ε)) :
      primeFormP h (leM K r ε)) = MulAut.conj (QuotientGroup.mk s : primeFormP h (leM K r ε)) := by
    rw [← hβ', ← hg, radicalConjHom_apply, le_conj_eq]
  exact ⟨g, le_conj_inj h hn _ _ e⟩

theorem psuFlagCharTwo_holds :
    ∀ (f : ℕ) (K : Type) [Field K] (h : UnitaryFieldData 2 f K) (r ε d : ℕ), 2 ≤ r → ε ≤ 1 →
      1 ≤ d → d ≤ r → CharTwo (projIsoStabilizer h r ε (hypFlag h r ε d)) := by
  intro f K _ h r ε d hr hε hd hdn
  haveI : Finite K := h.finite
  have hn : 3 ≤ 2 * r + ε := by omega
  have hq : ¬(2 * r + ε = 3 ∧ 2 ^ f = 2) := fun hx => by omega
  have hC : IsPrimeFormGram (leC K r ε) := le_isPrimeFormGram r ε
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  have hFpos : hypFlag h r ε d = posFlag r ε K d := hypFlag_eq_posFlag h hε (by omega)
  have hFiso : ∀ x ∈ hypFlag h r ε d, ∀ y ∈ hypFlag h r ε d, hypForm h r ε x y = 0 := by
    rw [hFpos]
    exact posFlag_isotropic h hdn
  have hFne : hypFlag h r ε d ≠ ⊥ := by
    intro h0
    have h1 := finrank_posFlag (K := K) (r := r) (ε := ε) hdn
    rw [← hFpos, h0, finrank_bot] at h1
    omega
  set F := hypFlag h r ε d with hFdef
  set W0 := transportSubspace h hR F with hW0def
  have hW0ne : W0 ≠ ⊥ := le_transport_ne_bot h hR F hFne
  have hWiso := le_transport_isotropic h hR F hFiso
  have hR0 : IsPGroup 2 (isotropicRadical h (leM K r ε) W0) :=
    (even_unitary_isotropic_radical_centralizer h hC hn hq W0 hW0ne hWiso).1
  haveI : Finite (primeFormP h (leM K r ε)) := inferInstance
  haveI : Finite (hypPSU h r ε) := inferInstance
  have hcomap : ∀ g : hypSU h r ε, hypProj h r ε g ∈ projIsoStabilizer h r ε F ↔
      g ∈ isoStabilizer h r ε F := fun g => by
    rw [← comap_projIsoStabilizer (W := F)]
    exact Subgroup.mem_comap.symm
  set Θ := gramHypProjEquiv h (leM K r ε) (le_gramHyp h hR) with hΘ
  set Hc : Subgroup (primeFormP h (leM K r ε)) :=
    (projIsoStabilizer h r ε F).comap Θ.toMonoidHom with hHc
  have hmemHc : ∀ s : gramSU h (leM K r ε),
      (QuotientGroup.mk s : primeFormP h (leM K r ε)) ∈ Hc ↔
        ∀ v ∈ W0, ((s : GL (Fin (2 * r + ε)) K) : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
          *ᵥ v ∈ W0 := by
    intro s
    rw [hHc, Subgroup.mem_comap]
    change Θ (QuotientGroup.mk s) ∈ projIsoStabilizer h r ε F ↔ _
    rw [hΘ, gramHypProjEquiv_mk]
    exact (hcomap (gramHypEquiv h (leM K r ε) (le_gramHyp h hR) s)).trans
      ((le_mem_isoStabilizer_iff h _ F).trans (le_stab_iff h hR F s).symm)
  set mkR : isotropicRadical h (leM K r ε) W0 →* primeFormP h (leM K r ε) :=
    (QuotientGroup.mk' (normOneScalars h (gramSU h (leM K r ε)) (2 * r + ε))).comp
      (isotropicRadical h (leM K r ε) W0).subtype with hmkR
  set N : Subgroup (primeFormP h (leM K r ε)) := mkR.range with hN
  have hN2 : IsPGroup 2 N := by
    rintro ⟨z, hz⟩
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hz
    obtain ⟨k, hk⟩ := hR0 g
    refine ⟨k, Subtype.ext ?_⟩
    show mkR g ^ 2 ^ k = 1
    rw [← map_pow, hk, map_one]
  have hNH : N ≤ Hc := by
    intro x hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
    change (QuotientGroup.mk (g : gramSU h (leM K r ε)) : primeFormP h (leM K r ε)) ∈ Hc
    refine (hmemHc _).mpr fun v hv => ?_
    rw [(mem_isotropicRadical.mp g.2).1 v hv]
    exact hv
  have hnorm : ∀ x ∈ Hc, ∀ y ∈ N, x * y * x⁻¹ ∈ N := by
    intro x hx y hy
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨g', hg'⟩ := le_normal_radical h W0 hn s ((hmemHc s).mp hx) g
    refine MonoidHom.mem_range.mpr ⟨g', ?_⟩
    show (QuotientGroup.mk (g' : gramSU h (leM K r ε)) : primeFormP h (leM K r ε)) = _
    rw [hg', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    try rfl
  have hcent : ∀ x ∈ Hc, (∀ n ∈ N, x * n = n * x) → x ∈ N := by
    intro x _ hx
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨g', hg'⟩ := le_centralizer_radical h W0 hn hW0ne hWiso s
      (fun g => hx (mkR g) ⟨g, rfl⟩)
    exact MonoidHom.mem_range.mpr ⟨g', hg'⟩
  have hCH : CharTwo Hc :=
    le_charTwo_of_normal hNH hN2 (fun x hx y hy => hnorm x hx y hy)
      (fun x hx hc => hcent x hx hc)
  have hT := le_charTwo_map Θ hCH
  have hmap : Hc.map Θ.toMonoidHom = projIsoStabilizer h r ε F := by
    rw [hHc]
    exact Subgroup.map_comap_eq_self_of_surjective Θ.surjective _
  rw [hmap] at hT
  exact hT

end Main

theorem le_sylowFacts_generic {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (r ε : ℕ) (hr : 2 ≤ r) (hε : ε ≤ 1)
    (hcov : ∀ A : Subgroup (hypPSU h r ε), A ≠ ⊤ → hypProjUnitriangular h r ε ≤ A →
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ r ∧ A ≤ projIsoStabilizer h r ε (hypFlag h r ε d))
    (hchar : ∀ d : ℕ, 1 ≤ d → d ≤ r → CharTwo (projIsoStabilizer h r ε (hypFlag h r ε d)))
    (hsimp : IsSimpleGroup (hypPSU h r ε)) :
    SylowFacts (hypPSU h r ε) (hypProjUnitriangular h r ε) := by
  haveI : Finite K := h.finite
  haveI : Finite (hypPSU h r ε) := inferInstance
  haveI := hsimp
  have hr1 : 1 ≤ r := by omega
  obtain ⟨hcard, -, -, ⟨e, -⟩, ⟨P0, hP0⟩, -⟩ :=
    unitary_order_and_Sylow h (r := r) (ε := ε) hr1 hε
  have hU0 : IsSylowTwoOf (hypProjUnitriangular h r ε) ⊤ := by
    rw [← hP0]
    exact CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P0
  have hU1 : hypProjUnitriangular h r ε ≠ ⊥ := by
    intro hbot
    have hc : Nat.card (hypProjUnitriangular h r ε) =
        (2 ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) := by
      rw [← Nat.card_congr e.toEquiv]
      exact hcard
    rw [hbot, Subgroup.card_bot] at hc
    have hf : 1 ≤ f := h.one_le
    have h2f : 2 ≤ 2 ^ f := Nat.le_self_pow (by omega) 2
    have hm : 4 * 3 ≤ (2 * r + ε) * (2 * r + ε - 1) := Nat.mul_le_mul (by omega) (by omega)
    have hN : 0 < (2 * r + ε) * (2 * r + ε - 1) / 2 := Nat.div_pos (by omega) (by norm_num)
    have hpow : 2 ≤ (2 ^ f) ^ ((2 * r + ε) * (2 * r + ε - 1) / 2) :=
      le_trans h2f (Nat.le_self_pow (by omega) (2 ^ f))
    omega
  have hco : ∀ d : ℕ, 1 ≤ d → d ≤ r →
      projIsoStabilizer h r ε (hypFlag h r ε d) ⋖ ⊤ := fun d hd hdn =>
    (isCoatom_projIsoStabilizer_hypFlag h hr1 hε hd hdn).covBy_top
  have hUP : ∀ d : ℕ, 1 ≤ d → d ≤ r →
      hypProjUnitriangular h r ε ≤ projIsoStabilizer h r ε (hypFlag h r ε d) := fun d hd hdn =>
    (Subgroup.map_mono (hypUnitriangular_le_hypBorel h (r := r) (ε := ε))).trans
      (hypProjBorel_le_projIsoStabilizer h hd hdn (ε := ε))
  have hX : pCoreOf 2 (⊤ : Subgroup (hypPSU h r ε)) = ⊥ :=
    pCoreOf_top_eq_bot_of_simple hU0 (hUP 1 le_rfl hr1) (hco 1 le_rfl hr1).lt.ne
  have hne : projIsoStabilizer h r ε (hypFlag h r ε 1) ≠
      projIsoStabilizer h r ε (hypFlag h r ε 2) := by
    intro heq
    obtain ⟨c, hc, hc0⟩ := exists_mem_traceZero_ne_zero' h
    have h1 := congrArg (Subgroup.comap (hypProj h r ε)) heq
    rw [comap_projIsoStabilizer, comap_projIsoStabilizer] at h1
    have hI1 : ({1} : Set ℕ) ⊆ Set.Icc 1 r := fun i hi => by
      rw [Set.mem_singleton_iff.mp hi]
      exact ⟨le_rfl, hr1⟩
    have hI2 : ({2} : Set ℕ) ⊆ Set.Icc 1 r := fun i hi => by
      rw [Set.mem_singleton_iff.mp hi]
      exact ⟨by norm_num, hr⟩
    have hmem : uWeylRep ε h ⟨1, by omega⟩ c hc ∈ flagStabilizer h r ε {1} :=
      (uWeylRep_mem_flagStabilizer_iff h hε hc hc0 hI1 ⟨1, by omega⟩).mpr (by simp)
    rw [flagStabilizer_singleton h 1] at hmem
    rw [h1, ← flagStabilizer_singleton h 2] at hmem
    exact (uWeylRep_mem_flagStabilizer_iff h hε hc hc0 hI2 ⟨1, by omega⟩).mp hmem (by simp)
  refine (ParabolicData.of_coatoms
    (Ps := (fun d : ℕ => projIsoStabilizer h r ε (hypFlag h r ε d)) '' {d | 1 ≤ d ∧ d ≤ r})
    hU0 hU1 hX ?_ ?_ ?_ ?_).sylowFacts
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact ⟨hco d hd hdn, hUP d hd hdn⟩
  · exact ⟨projIsoStabilizer h r ε (hypFlag h r ε 1), ⟨1, ⟨le_rfl, hr1⟩, rfl⟩,
      projIsoStabilizer h r ε (hypFlag h r ε 2), ⟨2, ⟨by norm_num, hr⟩, rfl⟩, hne⟩
  · intro A hUA hA
    obtain ⟨d, hd, hdn, hAd⟩ := hcov A hA hUA
    exact ⟨projIsoStabilizer h r ε (hypFlag h r ε d), ⟨d, ⟨hd, hdn⟩, rfl⟩, hAd⟩
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact hchar d hd hdn

theorem asLieTwoPSUGe4_of_gaps (hA : PSUCover) (hC : PSU42SylowFacts) :
    AsLieTwoPSUGe4 := by
  intro n f X _ _ hn hS hadm hmod
  have hmc : StatedClassicalModel X .PSU n 2 f := hmod.statedClassicalModel (by decide)
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hmc
  obtain ⟨r, ε, rfl, hε⟩ : ∃ r ε : ℕ, n = 2 * r + ε ∧ ε ≤ 1 :=
    ⟨n / 2, n % 2, by omega, by omega⟩
  have hU : UnitaryFieldData 2 f K :=
    ⟨Nat.prime_two, hadm.2.1, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) hU
  have hn1 : 1 ≤ 2 * r + ε := by omega
  have hr : 2 ≤ r := by omega
  let eH : X ≃* hypPSU hU r ε := e.trans (hypPSUEquivStatedProj hU hR hn1).symm
  have hsimp : IsSimpleGroup (hypPSU hU r ε) := eH.symm.isSimpleGroup
  have hFacts : SylowFacts (hypPSU hU r ε) (hypProjUnitriangular hU r ε) := by
    by_cases hex : (2 * r + ε, 2 ^ f) = (4, 2)
    · obtain ⟨h4, h2⟩ := Prod.mk.inj hex
      have hf1 : f = 1 := Nat.pow_right_injective (le_refl 2) (h2.trans (pow_one 2).symm)
      have hr2 : r = 2 := by omega
      have hε0 : ε = 0 := by omega
      subst hr2 hε0 hf1
      exact hC K hU
    · exact le_sylowFacts_generic hU r ε hr hε (hA f K hU r ε hr hε hex)
        (fun d hd hdn => psuFlagCharTwo_holds f K hU r ε d hr hε hd hdn) hsimp
  have hall : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → SylowFacts X T := fun T hT =>
    SylowFacts.of_mulEquiv_isSylow eH hFacts hT
  exact ⟨overgroups_of_forall_sylowFacts hall, oddAut_of_forall_sylowFacts hall⟩

end CFSG.Quasithin.LieOver

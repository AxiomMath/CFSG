module

public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Diagonal
public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoSt0E
public import CFSG.LocalAnalysis.WeakClosure81.ElevenFourBAltGp
public import CFSG.GF2Type.Smith1979.WidthFourKP.Swap.Interface

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Swap

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S5
  CFSG.Open Subgroup Module
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.PartOne.KCOrthogonal
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G} {D : S5.SwapData S g}

structure StabData (W : SwapW4 D) where
  Q : QuadraticForm (ZMod 2) (Vt S g D.t)
  hQ : Q.polarBilin.Nondegenerate
  hR : RmodN S g D.t = omegaGroup Q hQ
  hmin : ∀ U : Submodule (ZMod 2) (Vt S g D.t), finrank (ZMod 2) U = 2 →
    ∃ u ∈ U, Q u ≠ 0
  v : Vt S g D.t
  hv : Q v = 1
  CX : Subgroup S.O
  hCX : ∀ m : S.O, m ∈ CX ↔ m ∈ D.Xhat ∧
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v
  K : Subgroup S.O
  hK : ∀ m : S.O, m ∈ K ↔ m ∈ D.Z ⊔ D.W ∧
    (m : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v

theorem SwapW4.herm_stab_facts (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts) :
    Nat.card A.CX = 6 ∧
    (∀ u : Vt S g D.t,
      (∀ c ∈ A.CX, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) → u = 0 ∨ u = A.v) ∧
    (∀ ξ ∈ D.Xhat, (∀ c ∈ A.CX, ξ * c = c * ξ) → ξ = 1) ∧
    (∀ ξ ∈ D.Xhat, (∀ c ∈ A.CX, ξ * c * ξ⁻¹ ∈ A.CX) → ξ ∈ A.CX) := by
  obtain ⟨E, hField, hAlg, P', ψ, φ, hcardE, hψQ, hψρ⟩ :=
    SwapW4.exists_herm D W A.Q A.hQ A.hR A.hmin
  letI := hField
  letI := hAlg
  let X : hermFourSpace P'.σ := ψ A.v
  have hX1 : hermFourForm P' X = 1 := by
    rw [hψQ, A.hv]
  obtain ⟨hcard, hfix, hcen, hnormS⟩ := @hHS E hField hAlg P' hcardE X hX1
  let SX : Subgroup (SL(2, E)) :=
    { carrier := {h | hermFourRho P' h X = X}
      one_mem' := by
        show hermFourRho P' 1 X = X
        rw [map_one]
        rfl
      mul_mem' := by
        intro a b ha hb
        show hermFourRho P' (a * b) X = X
        rw [map_mul]
        show (hermFourRho P' a) ((hermFourRho P' b) X) = X
        rw [hb, ha]
      inv_mem' := by
        intro a ha
        show hermFourRho P' a⁻¹ X = X
        rw [map_inv]
        have h := congrArg (fun Y => (hermFourRho P' a)⁻¹ Y) ha
        simpa using h.symm }
  have hCXle : A.CX ≤ D.Xhat := fun m hm => ((A.hCX m).mp hm).1
  have hmem_iff (ξ : D.Xhat) :
      (ξ : S.O) ∈ A.CX ↔ hermFourRho P' (φ ξ) X = X := by
    rw [A.hCX (ξ : S.O)]
    constructor
    · rintro ⟨-, hv⟩
      have hres : resV W.H.conj_mem D.t ⟨ξ, W.F.XR ξ.2⟩ A.v = A.v := by
        apply Subtype.ext
        rw [S4.coe_resV_apply]
        exact hv
      have h := hψρ ξ A.v
      rw [hres] at h
      exact h.symm
    · intro h
      refine ⟨ξ.2, ?_⟩
      have hres : resV W.H.conj_mem D.t ⟨ξ, W.F.XR ξ.2⟩ A.v = A.v := by
        apply ψ.injective
        rw [hψρ ξ A.v]
        exact h
      have h' := congrArg (fun x : Vt S g D.t => (x : S.Qt)) hres
      rwa [S4.coe_resV_apply] at h'
  let eCX : A.CX ≃ SX :=
    { toFun := fun c => ⟨φ ⟨c.1, hCXle c.2⟩, (hmem_iff ⟨c.1, hCXle c.2⟩).mp c.2⟩
      invFun := fun h => ⟨((φ.symm h.1 : D.Xhat) : S.O), by
        refine (hmem_iff (φ.symm h.1)).mpr ?_
        rw [MulEquiv.apply_symm_apply]
        exact h.2⟩
      left_inv := fun c => by
        apply Subtype.ext
        show ((φ.symm (φ ⟨c.1, hCXle c.2⟩) : D.Xhat) : S.O) = c.1
        rw [MulEquiv.symm_apply_apply]
      right_inv := fun h => by
        apply Subtype.ext
        show φ (φ.symm h.1) = h.1
        rw [MulEquiv.apply_symm_apply] }
  have hcardCX : Nat.card A.CX = 6 := by
    rw [Nat.card_congr eCX]
    exact hcard
  refine ⟨hcardCX, ?_, ?_, ?_⟩
  ·
    intro u hu
    let Y : hermFourSpace P'.σ := ψ u
    have hY : ∀ h : SL(2, E), hermFourRho P' h X = X → hermFourRho P' h Y = Y := by
      intro h hh
      let c : A.CX := eCX.symm ⟨h, hh⟩
      let cX : D.Xhat := ⟨c.1, hCXle c.2⟩
      have hφc : φ cX = h :=
        congrArg Subtype.val (eCX.apply_symm_apply ⟨h, hh⟩)
      have hres : resV W.H.conj_mem D.t ⟨cX, W.F.XR cX.2⟩ u = u := by
        apply Subtype.ext
        rw [S4.coe_resV_apply]
        exact hu c c.2
      have h := hψρ cX u
      rw [hres, hφc] at h
      exact h.symm
    rcases hfix Y hY with h0 | hX
    · left
      apply ψ.injective
      rw [map_zero ψ]
      exact h0
    · right
      exact ψ.injective hX
  ·
    intro ξ hξX hcomm
    have hφ : φ ⟨ξ, hξX⟩ = 1 := by
      apply hcen (φ ⟨ξ, hξX⟩)
      intro h hh
      let c : A.CX := eCX.symm ⟨h, hh⟩
      let cX : D.Xhat := ⟨c.1, hCXle c.2⟩
      have hφc : φ cX = h :=
        congrArg Subtype.val (eCX.apply_symm_apply ⟨h, hh⟩)
      have hccomm : (⟨ξ, hξX⟩ : D.Xhat) * cX = cX * ⟨ξ, hξX⟩ := by
        apply Subtype.ext
        exact hcomm c c.2
      have hmap : φ ⟨ξ, hξX⟩ * φ cX = φ cX * φ ⟨ξ, hξX⟩ := by
        rw [← map_mul, ← map_mul, hccomm]
      rw [hφc] at hmap
      exact hmap
    have h1 : (⟨ξ, hξX⟩ : D.Xhat) = 1 := by
      apply φ.injective
      simpa using hφ
    exact congrArg Subtype.val h1
  ·
    intro ξ hξX hnormK
    have hφ : hermFourRho P' (φ ⟨ξ, hξX⟩) X = X := by
      apply hnormS (φ ⟨ξ, hξX⟩)
      intro h hh
      let c : A.CX := eCX.symm ⟨h, hh⟩
      let cX : D.Xhat := ⟨c.1, hCXle c.2⟩
      have hφc : φ cX = h :=
        congrArg Subtype.val (eCX.apply_symm_apply ⟨h, hh⟩)
      have hconj : (((⟨ξ, hξX⟩ : D.Xhat) * cX * ⟨ξ, hξX⟩⁻¹ : D.Xhat) : S.O) ∈ A.CX := by
        simpa using hnormK c c.2
      have hmap := (hmem_iff (⟨ξ, hξX⟩ * cX * ⟨ξ, hξX⟩⁻¹)).mp hconj
      rw [show φ (⟨ξ, hξX⟩ * cX * ⟨ξ, hξX⟩⁻¹) =
          φ ⟨ξ, hξX⟩ * h * (φ ⟨ξ, hξX⟩)⁻¹ by
        rw [map_mul, map_mul, map_inv, hφc]] at hmap
      exact hmap
    exact (hmem_iff ⟨ξ, hξX⟩).mpr hφ

theorem SwapW4.card_CX (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts) :
    Nat.card A.CX = 6 :=
  (SwapW4.herm_stab_facts W A hHS).1

theorem SwapW4.fix_CX (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts) :
    ∀ u : Vt S g D.t,
      (∀ c ∈ A.CX, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) → u = 0 ∨ u = A.v :=
  (SwapW4.herm_stab_facts W A hHS).2.1

theorem SwapW4.centralizer_CX (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts) :
    ∀ ξ ∈ D.Xhat, (∀ c ∈ A.CX, ξ * c = c * ξ) → ξ = 1 :=
  (SwapW4.herm_stab_facts W A hHS).2.2.1

theorem SwapW4.normalizer_CX (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts) :
    ∀ ξ ∈ D.Xhat, (∀ c ∈ A.CX, ξ * c * ξ⁻¹ ∈ A.CX) → ξ ∈ A.CX :=
  (SwapW4.herm_stab_facts W A hHS).2.2.2

section Goursat

theorem SwapW4.Xhat_le_E2 (W : SwapW4 D) : D.Xhat ≤ D.Z ⊔ D.W :=
  (D.Xhat_le_sup_inf W.H).trans inf_le_left

theorem SwapW4.CX_le_K (W : SwapW4 D) (A : StabData W) : A.CX ≤ A.K := by
  intro m hm
  rw [A.hK m]
  exact ⟨SwapW4.Xhat_le_E2 W ((A.hCX m).mp hm).1, ((A.hCX m).mp hm).2⟩

theorem SwapW4.t_fixes_v (W : SwapW4 D) (A : StabData W) :
    (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) (A.v : S.Qt) = A.v := by
  have hv : (A.v : S.Qt) ∈ fixSpace (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [W.hFix]
    exact A.v.2
  exact mem_fixSpace.mp hv

theorem SwapW4.conj_mem_E2 (W : SwapW4 D) {e : S.O} (he : e ∈ D.Z ⊔ D.W) :
    D.t * e * D.t⁻¹ ∈ D.Z ⊔ D.W := by
  have hWmap : D.W.map (MulAut.conj D.t).toMonoidHom = D.Z := by
    have hcomp : (MulAut.conj D.t).toMonoidHom.comp (MulAut.conj D.t).toMonoidHom =
        MonoidHom.id S.O :=
      MonoidHom.ext fun x => D.involutive W.H x
    calc D.W.map (MulAut.conj D.t).toMonoidHom
        = (D.Z.map (MulAut.conj D.t).toMonoidHom).map (MulAut.conj D.t).toMonoidHom := by
          rw [S5.SwapData.W]
      _ = D.Z.map ((MulAut.conj D.t).toMonoidHom.comp (MulAut.conj D.t).toMonoidHom) := by
          rw [Subgroup.map_map]
      _ = D.Z.map (MonoidHom.id S.O) := by rw [hcomp]
      _ = D.Z := Subgroup.map_id D.Z
  have hmap : (D.Z ⊔ D.W : Subgroup S.O).map (MulAut.conj D.t).toMonoidHom =
      D.Z ⊔ D.W := by
    rw [Subgroup.map_sup, hWmap, S5.SwapData.W, sup_comm]
  exact hmap ▸ Subgroup.mem_map.mpr ⟨e, he, rfl⟩

theorem SwapW4.t_normalizes_K (W : SwapW4 D) (A : StabData W) {k : S.O}
    (hk : k ∈ A.K) : D.t * k * D.t⁻¹ ∈ A.K := by
  rw [A.hK]
  refine ⟨SwapW4.conj_mem_E2 W ((A.hK k).mp hk).1, ?_⟩
  have hkv : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) A.v = A.v := ((A.hK k).mp hk).2
  have htv := SwapW4.t_fixes_v W A
  have htt : (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 := by
    have h := congrArg (fun x : S.O => (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) (D.t_mul_t W.H)
    simpa [Subgroup.coe_mul] using h
  have htinv : (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ = (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
    inv_eq_of_mul_eq_one_right htt
  have hcoe : ((D.t * k * D.t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (k : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  calc ((D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (k : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹) A.v
      = (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((k : S.Qt ≃ₗ[ZMod 2] S.Qt)
            ((D.t : S.Qt ≃ₗ[ZMod 2] S.Qt)⁻¹ A.v)) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    _ = (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) A.v) := by
        rw [htinv, htv]
    _ = (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) A.v := by rw [hkv]
    _ = A.v := htv

theorem SwapW4.conj_K_inf_Z (W : SwapW4 D) (A : StabData W) :
    (A.K ⊓ D.Z).map (MulAut.conj D.t).toMonoidHom = A.K ⊓ D.W := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj D.t).injective]
  have hKmap : A.K.map (MulAut.conj D.t).toMonoidHom = A.K := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨k, hk, rfl⟩
      exact SwapW4.t_normalizes_K W A hk
    · intro k hk
      refine ⟨D.t * k * D.t⁻¹, SwapW4.t_normalizes_K W A hk, ?_⟩
      show D.t * (D.t * k * D.t⁻¹) * D.t⁻¹ = k
      calc D.t * (D.t * k * D.t⁻¹) * D.t⁻¹
          = (D.t * D.t) * k * (D.t⁻¹ * D.t⁻¹) := by group
        _ = k := by rw [D.t_mul_t W.H, D.t_inv W.H, D.t_mul_t W.H]; group
  rw [hKmap, S5.SwapData.W]

theorem SwapW4.card_K_inf_Z_eq (W : SwapW4 D) (A : StabData W) :
    Nat.card ↥(A.K ⊓ D.Z) = Nat.card ↥(A.K ⊓ D.W) := by
  rw [← SwapW4.conj_K_inf_Z W A]
  exact (Subgroup.card_map_of_injective (MulAut.conj D.t).injective).symm

theorem SwapW4.chi_mem_CX (W : SwapW4 D) (A : StabData W) {k : S.O}
    (hk : k ∈ A.K ⊓ D.Z) : D.chi ⟨k, hk.2⟩ ∈ A.CX := by
  rw [A.hCX]
  refine ⟨D.chi_mem_Xhat _, ?_⟩
  have hkK : k ∈ A.K := hk.1
  have htkK : D.t * k * D.t⁻¹ ∈ A.K := SwapW4.t_normalizes_K W A hkK
  have hkv : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) A.v = A.v := ((A.hK k).mp hkK).2
  have htkv : ((D.t * k * D.t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) A.v = A.v :=
    ((A.hK _).mp htkK).2
  rw [S5.SwapData.chi_apply]
  have hcoe : ((k * (D.t * k * D.t⁻¹) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        ((D.t * k * D.t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [Subgroup.coe_mul]
  rw [hcoe]
  calc ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) *
        ((D.t * k * D.t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) A.v
      = (k : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((D.t * k * D.t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) A.v) := by
        rw [LinearEquiv.mul_apply]
    _ = (k : S.Qt ≃ₗ[ZMod 2] S.Qt) A.v := by rw [htkv]
    _ = A.v := hkv

theorem SwapW4.card_K_inf_Z_dvd_six (W : SwapW4 D) (A : StabData W)
    (hHS : HermStabFacts) : Nat.card ↥(A.K ⊓ D.Z) ∣ 6 := by
  have hmap : ((A.K ⊓ D.Z).subgroupOf D.Z).map D.chi ≤ A.CX := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : (k : S.O) ∈ A.K ⊓ D.Z := (Subgroup.mem_subgroupOf).mp hk
    exact SwapW4.chi_mem_CX W A (k := (k : S.O)) hk'
  have hcard : Nat.card ↥(((A.K ⊓ D.Z).subgroupOf D.Z).map D.chi) =
      Nat.card ↥(A.K ⊓ D.Z) := by
    rw [Subgroup.card_map_of_injective (SwapW4.chi_injective D W)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← hcard]
  have := Subgroup.card_dvd_of_le hmap
  rwa [SwapW4.card_CX W A hHS] at this

@[expose] noncomputable def SwapW4.piZFun (W : SwapW4 D) (e : (D.Z ⊔ D.W : Subgroup S.O)) : D.Z :=
  (SwapW4.decomp D W e.2).choose.1

theorem SwapW4.piZFun_eq (W : SwapW4 D) {e : (D.Z ⊔ D.W : Subgroup S.O)} {z z2 : D.Z}
    (he : (e : S.O) = (z : S.O) * (D.t * (z2 : S.O) * D.t⁻¹)) :
    SwapW4.piZFun W e = z := by
  have hspec := Classical.choose_spec (SwapW4.decomp D W e.2)
  have hpair : (z, z2) = Classical.choose (SwapW4.decomp D W e.2) :=
    hspec.2 (z, z2) he
  change (Classical.choose (SwapW4.decomp D W e.2)).1 = z
  rw [← hpair]

theorem SwapW4.piZFun_eq_one_iff (W : SwapW4 D) {e : (D.Z ⊔ D.W : Subgroup S.O)} :
    SwapW4.piZFun W e = 1 ↔ (e : S.O) ∈ D.W := by
  constructor
  · intro h
    have hspec := Classical.choose_spec (SwapW4.decomp D W e.2)
    have hpi : SwapW4.piZFun W e = (Classical.choose (SwapW4.decomp D W e.2)).1 := rfl
    have hp1 : (Classical.choose (SwapW4.decomp D W e.2)).1 = 1 := by rw [← hpi, h]
    have he : (e : S.O) = D.t * ((Classical.choose (SwapW4.decomp D W e.2)).2 : S.O) * D.t⁻¹ := by
      calc (e : S.O)
          = ((Classical.choose (SwapW4.decomp D W e.2)).1 : S.O) *
              (D.t * ((Classical.choose (SwapW4.decomp D W e.2)).2 : S.O) * D.t⁻¹) := hspec.1
        _ = ((1 : D.Z) : S.O) *
              (D.t * ((Classical.choose (SwapW4.decomp D W e.2)).2 : S.O) * D.t⁻¹) := by rw [hp1]
        _ = D.t * ((Classical.choose (SwapW4.decomp D W e.2)).2 : S.O) * D.t⁻¹ := by
            rw [show ((1 : D.Z) : S.O) = 1 from rfl, one_mul]
    rw [he]
    exact D.conj_mem_W (Classical.choose (SwapW4.decomp D W e.2)).2.2
  · intro hW
    obtain ⟨z, hzZ, hz⟩ := Subgroup.mem_map.mp hW
    let zD : D.Z := ⟨z, hzZ⟩
    have hz' : (e : S.O) = ((1 : D.Z) : S.O) * (D.t * (zD : S.O) * D.t⁻¹) := by
      rw [← hz]
      change D.t * (z : S.O) * D.t⁻¹ = ((1 : D.Z) : S.O) * (D.t * (z : S.O) * D.t⁻¹)
      rw [show ((1 : D.Z) : S.O) = 1 from rfl, one_mul]
    have hpair : ((1 : D.Z), zD) = Classical.choose (SwapW4.decomp D W e.2) :=
      (Classical.choose_spec (SwapW4.decomp D W e.2)).2 (1, zD) hz'
    change (Classical.choose (SwapW4.decomp D W e.2)).1 = 1
    rw [← hpair]

@[expose] noncomputable def SwapW4.piZ (W : SwapW4 D) : (D.Z ⊔ D.W : Subgroup S.O) →* D.Z where
  toFun := SwapW4.piZFun W
  map_one' := by
    change SwapW4.piZFun W 1 = 1
    exact (SwapW4.piZFun_eq_one_iff W).mpr D.W.one_mem
  map_mul' e f := by
    obtain ⟨p, hp, huniq⟩ := SwapW4.decomp D W e.2
    obtain ⟨q, hq, huniq'⟩ := SwapW4.decomp D W f.2
    have hpi_e : SwapW4.piZFun W e = p.1 := SwapW4.piZFun_eq W hp
    have hpi_f : SwapW4.piZFun W f = q.1 := SwapW4.piZFun_eq W hq
    have hprod : ((e * f : (D.Z ⊔ D.W : Subgroup S.O)) : S.O) =
        ((p.1 * q.1 : D.Z) : S.O) *
          (D.t * ((p.2 * q.2 : D.Z) : S.O) * D.t⁻¹) := by
      rw [Subgroup.coe_mul, hp, hq]
      have hcomm : (D.t * (p.2 : S.O) * D.t⁻¹) * (q.1 : S.O) =
          (q.1 : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹) :=
        D.mul_comm_of_mem_W (D.conj_mem_W p.2.2) q.1.2
      calc (p.1 : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹) *
            ((q.1 : S.O) * (D.t * (q.2 : S.O) * D.t⁻¹))
          = (p.1 : S.O) * ((D.t * (p.2 : S.O) * D.t⁻¹) * (q.1 : S.O)) *
              (D.t * (q.2 : S.O) * D.t⁻¹) := by group
        _ = (p.1 : S.O) * ((q.1 : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹)) *
              (D.t * (q.2 : S.O) * D.t⁻¹) := by rw [hcomm]
        _ = ((p.1 * q.1 : D.Z) : S.O) *
              (D.t * ((p.2 * q.2 : D.Z) : S.O) * D.t⁻¹) := by
            rw [Subgroup.coe_mul, Subgroup.coe_mul]
            group
    change SwapW4.piZFun W (e * f) = SwapW4.piZFun W e * SwapW4.piZFun W f
    rw [hpi_e, hpi_f, SwapW4.piZFun_eq W hprod]

theorem SwapW4.card_range_le_of_ne_top (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts)
    (πK : A.K →* D.Z)
    (hπK_norm : ∀ k : A.K, (πK k : S.O) ∈
      Subgroup.normalizer ((A.K ⊓ D.Z : Subgroup S.O) : Set S.O))
    (hcard_ker : Nat.card ↥πK.ker = Nat.card ↥(A.K ⊓ D.W))
    (hcardK : Nat.card ↥A.K = Nat.card ↥πK.range * Nat.card ↥πK.ker)
    (h60 : 60 ≤ Nat.card ↥A.K) (hne : πK.range ≠ ⊤) :
    Nat.card ↥πK.range ≤ 6 ∧ Nat.card ↥(A.K ⊓ D.Z) = 6 := by
  haveI : IsSimpleGroup D.Z := SwapW4.isSimpleGroup_Z D W
  have hle12 : Nat.card ↥πK.range ≤ 12 :=
    CFSG.LocalAnalysis.WeakClosure81.b114_ElevenFourBAltGp_card_le_twelve_of_ne_top
      (SwapW4.card_Z D W) hne
  have hK1ge : 5 ≤ Nat.card ↥(A.K ⊓ D.Z) := by
    have h1 : Nat.card ↥πK.ker = Nat.card ↥(A.K ⊓ D.Z) := by
      rw [hcard_ker, ← SwapW4.card_K_inf_Z_eq W A]
    have h2 : 60 ≤ Nat.card ↥πK.range * Nat.card ↥(A.K ⊓ D.Z) := by
      calc 60 ≤ Nat.card A.K := h60
        _ = Nat.card ↥πK.range * Nat.card ↥πK.ker := hcardK
        _ = Nat.card ↥πK.range * Nat.card ↥(A.K ⊓ D.Z) := by rw [h1]
    have h3 : 60 ≤ 12 * Nat.card ↥(A.K ⊓ D.Z) :=
      h2.trans (Nat.mul_le_mul_right _ hle12)
    have h4 : 5 * 12 ≤ Nat.card ↥(A.K ⊓ D.Z) * 12 := by
      calc 5 * 12 = 60 := by norm_num
        _ ≤ 12 * Nat.card ↥(A.K ⊓ D.Z) := h3
        _ = Nat.card ↥(A.K ⊓ D.Z) * 12 := by ring
    exact Nat.le_of_mul_le_mul_right h4 (by norm_num)
  have hdvd := SwapW4.card_K_inf_Z_dvd_six W A hHS
  have hle6 : Nat.card ↥(A.K ⊓ D.Z) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hK1card : Nat.card ↥(A.K ⊓ D.Z) = 6 := by
    rcases Nat.eq_or_lt_of_le hK1ge with h5 | h5
    · exfalso
      rw [← h5] at hdvd
      norm_num at hdvd
    · exact Nat.le_antisymm hle6 (Nat.succ_le_of_lt h5)
  have hχK1_le : ((A.K ⊓ D.Z).subgroupOf D.Z).map D.chi ≤ A.CX := by
    rintro _ ⟨y, hy, rfl⟩
    exact SwapW4.chi_mem_CX W A (k := (y : S.O))
      ((Subgroup.mem_subgroupOf).mp hy)
  have hχK1_card : Nat.card ↥(((A.K ⊓ D.Z).subgroupOf D.Z).map D.chi) = 6 := by
    have h1 : Nat.card ↥(((A.K ⊓ D.Z).subgroupOf D.Z).map D.chi) =
        Nat.card ↥((A.K ⊓ D.Z).subgroupOf D.Z) :=
      Subgroup.card_map_of_injective (SwapW4.chi_injective D W)
    have h2 : Nat.card ↥((A.K ⊓ D.Z).subgroupOf D.Z) =
        Nat.card ↥(A.K ⊓ D.Z) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    exact h1.trans (h2.trans hK1card)
  have hχK1_eq : ((A.K ⊓ D.Z).subgroupOf D.Z).map D.chi = A.CX := by
    apply eq_of_le_of_card_ge hχK1_le
    rw [hχK1_card, SwapW4.card_CX W A hHS]
  have hχrange_le : (πK.range).map D.chi ≤ A.CX := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨k, hk, rfl⟩ := MonoidHom.mem_range.mp hz
    refine SwapW4.normalizer_CX W A hHS (D.chi (πK k)) (D.chi_mem_Xhat (πK k)) ?_
    intro c hc
    have hc' : c ∈ ((A.K ⊓ D.Z).subgroupOf D.Z).map D.chi := hχK1_eq ▸ hc
    rcases Subgroup.mem_map.mp hc' with ⟨y, hy, hc_eq⟩
    have hy' : (y : S.O) ∈ A.K ⊓ D.Z := (Subgroup.mem_subgroupOf).mp hy
    have hzy : (((πK k * y * (πK k)⁻¹ : D.Z) : S.O)) ∈ A.K ⊓ D.Z := by
      have h := (Subgroup.mem_normalizer_iff.mp (hπK_norm k)) (y : S.O)
      simpa using h.mp hy'
    have hχzy : D.chi (πK k * y * (πK k)⁻¹) ∈ A.CX :=
      SwapW4.chi_mem_CX W A (k := ((πK k * y * (πK k)⁻¹ : D.Z) : S.O)) hzy
    have hchi_eq : D.chi (πK k) * c * (D.chi (πK k))⁻¹ =
        D.chi (πK k * y * (πK k)⁻¹) := by
      rw [← hc_eq]
      simp only [map_mul, map_inv]
    rwa [hchi_eq]
  refine ⟨?_, hK1card⟩
  have hcardmap : Nat.card ↥((πK.range).map D.chi) = Nat.card ↥πK.range :=
    Subgroup.card_map_of_injective (SwapW4.chi_injective D W)
  have hle : Nat.card ↥((πK.range).map D.chi) ≤ Nat.card ↥A.CX := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥((πK.range).map D.chi) => (⟨x.1, hχrange_le x.2⟩ : A.CX)) ?_
    intro a b hab
    exact Subtype.ext (congrArg (fun z : A.CX => (z : S.O)) hab)
  rw [← hcardmap]
  exact hle.trans (by rw [SwapW4.card_CX W A hHS])

structure GoursatFacts (W : SwapW4 D) (A : StabData W) : Prop where
  K_inf_Z : A.K ⊓ D.Z = ⊥
  K_inf_W : A.K ⊓ D.W = ⊥
  card_K : Nat.card ↥A.K = 60
  isSimpleGroup_K : IsSimpleGroup A.K
  not_commutative : ∃ a b : A.K, a * b ≠ b * a

theorem SwapW4.goursat_aux (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts)
    (h60 : 60 ≤ Nat.card ↥A.K) (πK : A.K →* D.Z)
    (hker : πK.ker = (A.K ⊓ D.W).subgroupOf A.K)
    (hcard_ker : Nat.card ↥πK.ker = Nat.card ↥(A.K ⊓ D.W))
    (hcardK : Nat.card ↥A.K = Nat.card ↥πK.range * Nat.card ↥πK.ker)
    (hπK_norm : ∀ k : A.K, (πK k : S.O) ∈
      Subgroup.normalizer ((A.K ⊓ D.Z : Subgroup S.O) : Set S.O))
    (htop : πK.range = ⊤) : GoursatFacts W A := by
  haveI : IsSimpleGroup D.Z := SwapW4.isSimpleGroup_Z D W
  have hZleNorm : D.Z ≤ Subgroup.normalizer ((A.K ⊓ D.Z : Subgroup S.O) : Set S.O) := by
    intro z hz
    have hzrange : (⟨z, hz⟩ : D.Z) ∈ πK.range := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hzrange
    have hk' : (πK k : S.O) = z := congrArg Subtype.val hk
    rw [← hk']
    exact hπK_norm k
  have hK1normal : ((A.K ⊓ D.Z).subgroupOf D.Z).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hZleNorm
  have hK1bot : A.K ⊓ D.Z = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((A.K ⊓ D.Z).subgroupOf D.Z) with hbot | htop'
    · rw [eq_bot_iff]
      intro x hx
      have hxZ : x ∈ D.Z := hx.2
      have hxsub : (⟨x, hxZ⟩ : D.Z) ∈ (A.K ⊓ D.Z).subgroupOf D.Z := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      rw [hbot] at hxsub
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxsub)
    · have hK1top : D.Z ≤ A.K ⊓ D.Z := (Subgroup.subgroupOf_eq_top.mp htop')
      have hK1eq : A.K ⊓ D.Z = D.Z := le_antisymm inf_le_right hK1top
      have hcard60 : Nat.card ↥(A.K ⊓ D.Z) = 60 := by rw [hK1eq, SwapW4.card_Z D W]
      have hdvd := SwapW4.card_K_inf_Z_dvd_six W A hHS
      rw [hcard60] at hdvd
      have hle6 : 60 ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      omega
  have hKinfWbot : A.K ⊓ D.W = ⊥ := by
    rw [← SwapW4.conj_K_inf_Z W A, hK1bot, Subgroup.map_bot]
  have hcardK60 : Nat.card ↥A.K = 60 := by
    rw [hcardK, hcard_ker, ← SwapW4.card_K_inf_Z_eq W A, hK1bot]
    rw [Subgroup.card_bot, mul_one, htop, Subgroup.card_top, SwapW4.card_Z D W]
  have hkerbot : πK.ker = ⊥ := by
    rw [hker, hKinfWbot]
    simp
  have hinj : Function.Injective πK := (MonoidHom.ker_eq_bot_iff πK).mp hkerbot
  have hsurj : Function.Surjective πK := by
    intro z
    have hz : z ∈ πK.range := by rw [htop]; exact Subgroup.mem_top z
    exact MonoidHom.mem_range.mp hz
  let eK : A.K ≃* D.Z := MulEquiv.ofBijective πK ⟨hinj, hsurj⟩
  have hKsimple : IsSimpleGroup A.K := MulEquiv.isSimpleGroup eK
  have hnabZ : ∃ a b : D.Z, a * b ≠ b * a := by
    haveI : Group.IsPerfect D.Z := ⟨D.isQuasisimple_Z.1⟩
    haveI : Nontrivial D.Z :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [SwapW4.card_Z D W]; norm_num)
    have hnc := Group.IsPerfect.not_isMulCommutative D.Z
    rw [isMulCommutative_iff] at hnc
    push Not at hnc
    exact hnc
  have hnabK : ∃ a b : A.K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnabZ
    refine ⟨eK.symm a, eK.symm b, ?_⟩
    intro h
    apply hab
    have := congrArg eK h
    simpa using this
  exact ⟨hK1bot, hKinfWbot, hcardK60, hKsimple, hnabK⟩
theorem SwapW4.goursat_facts (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts)
    (h60 : 60 ≤ Nat.card ↥A.K) : GoursatFacts W A := by
  haveI : IsSimpleGroup D.Z := SwapW4.isSimpleGroup_Z D W
  let E2 : Subgroup S.O := D.Z ⊔ D.W
  have hKE2 : A.K ≤ E2 := fun k hk => ((A.hK k).mp hk).1
  let πK : A.K →* D.Z := (SwapW4.piZ W).comp (Subgroup.inclusion hKE2)
  have hker : πK.ker = (A.K ⊓ D.W).subgroupOf A.K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro h
      refine ⟨k.2, ?_⟩
      change SwapW4.piZFun W (Subgroup.inclusion hKE2 k) = 1 at h
      rwa [SwapW4.piZFun_eq_one_iff, Subgroup.coe_inclusion] at h
    · rintro ⟨-, hw⟩
      change SwapW4.piZFun W (Subgroup.inclusion hKE2 k) = 1
      rwa [SwapW4.piZFun_eq_one_iff, Subgroup.coe_inclusion]
  have hcard_ker : Nat.card ↥πK.ker = Nat.card ↥(A.K ⊓ D.W) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hcardK : Nat.card ↥A.K = Nat.card ↥πK.range * Nat.card ↥πK.ker := by
    calc Nat.card ↥A.K = Nat.card (A.K ⧸ πK.ker) * Nat.card ↥πK.ker :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup πK.ker
      _ = Nat.card ↥πK.range * Nat.card ↥πK.ker := by
          rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange πK).toEquiv]
  have hπK_norm : ∀ k : A.K, (πK k : S.O) ∈
      Subgroup.normalizer ((A.K ⊓ D.Z : Subgroup S.O) : Set S.O) := by
    intro k
    rw [Subgroup.mem_normalizer_iff_map_conj_eq (G := S.O) (H := A.K ⊓ D.Z)
      (g := (πK k : S.O))]
    have hle : (A.K ⊓ D.Z).map (MulAut.conj ((πK k : S.O))).toMonoidHom ≤ A.K ⊓ D.Z := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨p, hp, huniq⟩ := SwapW4.decomp D W (Subgroup.inclusion hKE2 k).2
      have hpi : πK k = p.1 := SwapW4.piZFun_eq W hp
      have hp' : (k : S.O) = (p.1 : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹) := by
        rw [← Subgroup.coe_inclusion hKE2 k]
        exact hp
      have hcomm : (D.t * (p.2 : S.O) * D.t⁻¹) * (y : S.O) =
          (y : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹) :=
        D.mul_comm_of_mem_W (D.conj_mem_W p.2.2) hy.2
      have hconj_eq : (πK k : S.O) * (y : S.O) * (πK k : S.O)⁻¹ =
          (k : S.O) * (y : S.O) * (k : S.O)⁻¹ := by
        rw [hpi, hp']
        calc (p.1 : S.O) * (y : S.O) * (p.1 : S.O)⁻¹
            = (p.1 : S.O) *
                ((D.t * (p.2 : S.O) * D.t⁻¹) * (y : S.O) *
                  (D.t * (p.2 : S.O) * D.t⁻¹)⁻¹) * (p.1 : S.O)⁻¹ := by
              rw [show (D.t * (p.2 : S.O) * D.t⁻¹) * (y : S.O) *
                    (D.t * (p.2 : S.O) * D.t⁻¹)⁻¹ = (y : S.O) by
                  rw [hcomm]; group]

          _ = ((p.1 : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹)) * (y : S.O) *
                ((p.1 : S.O) * (D.t * (p.2 : S.O) * D.t⁻¹))⁻¹ := by group
      change (πK k : S.O) * (y : S.O) * (πK k : S.O)⁻¹ ∈ A.K ⊓ D.Z
      refine ⟨?_, ?_⟩
      · rw [hconj_eq]
        exact A.K.mul_mem (A.K.mul_mem k.2 hy.1) (A.K.inv_mem k.2)
      · exact D.Z.mul_mem (D.Z.mul_mem (πK k).2 hy.2) (D.Z.inv_mem (πK k).2)
    refine eq_of_le_of_card_ge hle ?_
    have hmapcard : Nat.card ↥((A.K ⊓ D.Z).map
        (MulAut.conj ((πK k : S.O))).toMonoidHom) = Nat.card ↥(A.K ⊓ D.Z) :=
      Subgroup.card_map_of_injective (f := (MulAut.conj ((πK k : S.O))).toMonoidHom)
        (MulAut.conj ((πK k : S.O))).injective
    change Nat.card ↥(A.K ⊓ D.Z) ≤
      Nat.card ↥((A.K ⊓ D.Z).map (MulAut.conj ((πK k : S.O))).toMonoidHom)
    rw [hmapcard]
  have htop : πK.range = ⊤ := by
    by_contra hne
    obtain ⟨hcard_range_le, hK1card⟩ :=
      SwapW4.card_range_le_of_ne_top W A hHS πK hπK_norm hcard_ker hcardK h60 hne
    have hcardK_le : Nat.card ↥A.K ≤ 36 := by
      have hker' : Nat.card ↥πK.ker = Nat.card ↥(A.K ⊓ D.Z) :=
        hcard_ker.trans (SwapW4.card_K_inf_Z_eq W A).symm
      have h1 : Nat.card ↥A.K = Nat.card ↥πK.range * Nat.card ↥(A.K ⊓ D.Z) :=
        hcardK.trans (congrArg (fun x => Nat.card ↥πK.range * x) hker')
      exact h1.le.trans ((Nat.mul_le_mul hcard_range_le hK1card.le).trans (by norm_num))
    omega
  exact SwapW4.goursat_aux W A hHS h60 πK hker hcard_ker hcardK hπK_norm htop

theorem SwapW4.card_K (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts)
    (h60 : 60 ≤ Nat.card ↥A.K) : Nat.card ↥A.K = 60 :=
  (SwapW4.goursat_facts W A hHS h60).card_K

theorem SwapW4.isSimpleGroup_K (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts)
    (h60 : 60 ≤ Nat.card ↥A.K) : IsSimpleGroup A.K :=
  (SwapW4.goursat_facts W A hHS h60).isSimpleGroup_K

theorem SwapW4.isQuasisimple_K (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts)
    (h60 : 60 ≤ Nat.card ↥A.K) : CFSG.Open.IsQuasisimple A.K := by
  haveI : IsSimpleGroup A.K := (SwapW4.goursat_facts W A hHS h60).isSimpleGroup_K
  exact CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.isQuasisimple_open_of_simple
    (SwapW4.goursat_facts W A hHS h60).not_commutative

theorem SwapW4.eq_one_of_mem_Lbar_of_commute (W : SwapW4 D) (A : StabData W)
    (hHS : HermStabFacts) (h60 : 60 ≤ Nat.card ↥A.K) :
    ∀ ℓ ∈ S.Lbar g, (∀ k ∈ A.K, ℓ * k = k * ℓ) → ℓ = 1 := by
  intro ℓ hℓ hcomm
  have hcommL : ∀ a ∈ Subgroup.zpowers D.t, ∀ b ∈ (SwapW4.P D W).map D.chi,
      a * b = b * a := by
    intro a ha b hb
    refine S4.Lbar_comm S W.H.conj_mem ?_ ?_
    · exact zpowers_le.mpr D.mem_Lbar ha
    · have h := hb
      rw [SwapW4.P_map_chi D W] at h
      exact h.1
  have hℓ' : ℓ ∈ Subgroup.zpowers D.t ⊔ (SwapW4.P D W).map D.chi := by
    rwa [← SwapW4.Lbar_eq D W]
  obtain ⟨n, hn, b, hb, hnb⟩ := (GL83.CompFam.mem_sup_of_commute hcommL).mp hℓ'
  have hbX : b ∈ D.Xhat := by
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hb
    exact D.chi_mem_Xhat z
  have hbCX : ∀ c ∈ A.CX, b * c = c * b := by
    intro c hc
    have hcK : c ∈ A.K := SwapW4.CX_le_K W A hc
    have hcX : c ∈ D.Xhat := ((A.hCX c).mp hc).1
    have hct : Commute c D.t :=
      Subgroup.mem_centralizer_singleton_iff.mp (D.Xhat_le_centralizer W.H hcX)
    have hnc : n * c = c * n := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      exact (hct.zpow_right k).eq.symm
    have hℓc : ℓ * c = c * ℓ := hcomm c hcK
    rw [← hnb] at hℓc
    calc b * c = n⁻¹ * (n * b) * c := by group
      _ = n⁻¹ * ((n * b) * c) := by group
      _ = n⁻¹ * (c * (n * b)) := by rw [hℓc]
      _ = n⁻¹ * (c * n) * b := by group
      _ = n⁻¹ * (n * c) * b := by rw [hnc]
      _ = c * b := by group
  have hb1 : b = 1 := SwapW4.centralizer_CX W A hHS b hbX hbCX
  have hℓn : ℓ = n := by rw [← hnb, hb1, mul_one]
  have htz : n = 1 ∨ n = D.t := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have ht2 : D.t * D.t = 1 := D.t_mul_t W.H
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
        pow_two, ht2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast,
        pow_two, ht2, one_zpow, one_mul, zpow_one]
  rcases htz with h1 | ht
  · rw [hℓn, h1]
  · exfalso
    rw [hℓn, ht] at hcomm
    have hKE2 : A.K ≤ D.Z ⊔ D.W := fun k hk => ((A.hK k).mp hk).1
    have hKleX : A.K ≤ D.Xhat := by
      intro k hk
      have hkE : k ∈ D.Z ⊔ D.W := hKE2 hk
      have hkt : k ∈ Subgroup.centralizer ({D.t} : Set S.O) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact hcomm k hk
      have hmem : k ∈ (D.Z ⊔ D.W) ⊓ Subgroup.centralizer ({D.t} : Set S.O) :=
        Subgroup.mem_inf.mpr ⟨hkE, hkt⟩
      rwa [SwapW4.E2_inf_centralizer D W] at hmem
    have hKleCX : A.K ≤ A.CX := by
      intro k hk
      rw [A.hCX k]
      exact ⟨hKleX hk, ((A.hK k).mp hk).2⟩
    have hcard : Nat.card ↥A.K ≤ Nat.card ↥A.CX := Subgroup.card_le_of_le hKleCX
    rw [SwapW4.card_CX W A hHS] at hcard
    omega

theorem SwapW4.le_closure_pow_five (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts)
    (h60 : 60 ≤ Nat.card ↥A.K) :
    A.K ≤ Subgroup.closure {k : S.O | k ∈ A.K ∧ k ^ 5 = 1} := by
  haveI : IsSimpleGroup A.K := SwapW4.isSimpleGroup_K W A hHS h60
  have hcardK : Nat.card ↥A.K = 60 := SwapW4.card_K W A hHS h60
  let T : Set S.O := {k | k ∈ A.K ∧ k ^ 5 = 1}
  let H : Subgroup S.O := Subgroup.closure T
  have hTle : T ⊆ A.K := fun x hx => hx.1
  have hHle : H ≤ A.K := (Subgroup.closure_le A.K).mpr hTle
  have hTconj : ∀ k ∈ A.K, ∀ x ∈ T, k * x * k⁻¹ ∈ T := by
    intro k hk x hx
    refine ⟨A.K.mul_mem (A.K.mul_mem hk hx.1) (A.K.inv_mem hk), ?_⟩
    rw [show k * x * k⁻¹ = (MulAut.conj k) x by rw [MulAut.conj_apply]]
    rw [← map_pow, hx.2, map_one]
  have hHconj : ∀ k ∈ A.K, ∀ x ∈ H, k * x * k⁻¹ ∈ H := by
    intro k hk x hx
    refine Subgroup.closure_induction (k := T) ?_ ?_ ?_ ?_ hx
    · intro y hy
      exact Subgroup.subset_closure (hTconj k hk y hy)
    · simp
    · intro a b ha_mem hb_mem ha hb
      rw [show k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) by group]
      exact H.mul_mem ha hb
    · intro a ha_mem ha
      rw [show k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ by group]
      exact H.inv_mem ha
  have hHnormal : (H.subgroupOf A.K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hHle]
    intro h k hh hk
    exact hHconj k hk h hh
  have hHne : H ≠ ⊥ := by
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := A.K) 5 (by rw [hcardK]; norm_num)
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hxord
      omega
    have hxT : (x : S.O) ∈ T := by
      refine ⟨x.2, ?_⟩
      have h : x ^ 5 = 1 := by
        rw [← hxord]
        exact pow_orderOf_eq_one x
      exact congrArg (fun y : A.K => (y : S.O)) h
    intro hbot
    have hxH : (x : S.O) ∈ H := Subgroup.subset_closure hxT
    rw [hbot] at hxH
    have hx1' : (x : S.O) = 1 := Subgroup.mem_bot.mp hxH
    exact hx1 (Subtype.ext hx1')
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.subgroupOf A.K) with hbot | htop
  · exfalso
    apply hHne
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ A.K := hHle hx
    have hxsub : (⟨x, hxK⟩ : A.K) ∈ H.subgroupOf A.K := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    rw [hbot] at hxsub
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hxsub)
  · exact Subgroup.subgroupOf_eq_top.mp htop

theorem SwapW4.finrank_le_two (W : SwapW4 D) (A : StabData W) (hHS : HermStabFacts) :
    ∀ C : Submodule (ZMod 2) S.Qt,
      (∀ u ∈ C, ∀ k ∈ A.K, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) →
      finrank (ZMod 2) C ≤ 2 := by
  intro C hC
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  let t : S.Qt ≃ₗ[ZMod 2] S.Qt := D.t
  let C' : Submodule (ZMod 2) S.Qt := C ⊔ C.map t.toLinearMap
  have htt : t * t = 1 := by
    have h := congrArg (fun x : S.O => (x : S.Qt ≃ₗ[ZMod 2] S.Qt)) (D.t_mul_t W.H)
    simpa [t, Subgroup.coe_mul] using h
  have hC't : ∀ u ∈ C', t u ∈ C' := by
    intro u hu
    rcases Submodule.mem_sup.mp hu with ⟨a, ha, b, hb, rfl⟩
    rcases Submodule.mem_map.mp hb with ⟨c, hc, rfl⟩
    rw [map_add]
    change t a + t (t c) ∈ C'
    rw [show t (t c) = c by
      rw [← LinearEquiv.mul_apply, htt]
      rfl]
    exact Submodule.mem_sup.mpr ⟨c, hc, t a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩, add_comm _ _⟩
  have hC'K : ∀ u ∈ C', ∀ k ∈ A.K, (k : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    intro u hu k hk
    rcases Submodule.mem_sup.mp hu with ⟨a, ha, b, hb, rfl⟩
    rcases Submodule.mem_map.mp hb with ⟨c, hc, rfl⟩
    rw [map_add]
    have hka : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) a = a := hC a ha k hk
    have htk : D.t * k * D.t⁻¹ ∈ A.K := SwapW4.t_normalizes_K W A hk
    have hkt : ((D.t * k * D.t⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c := hC c hc _ htk
    have htt' : ∀ v : S.Qt, t (t v) = v := fun v => by
      rw [← LinearEquiv.mul_apply, htt]
      rfl
    have htc : (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (t c) = t c := by
      have h2 : (D.t : S.Qt ≃ₗ[ZMod 2] S.Qt)
          ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) ((D.t : S.Qt ≃ₗ[ZMod 2] S.Qt) c)) = c := by
        have hcoe : ((D.t * k * D.t : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) c = c := by
          have h1 : D.t * k * D.t = D.t * k * D.t⁻¹ := by rw [D.t_inv W.H]
          rw [h1]
          exact hkt
        simpa [Subgroup.coe_mul, LinearEquiv.mul_apply] using hcoe
      calc (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (t c)
          = t (t ((k : S.Qt ≃ₗ[ZMod 2] S.Qt) (t c))) := (htt' _).symm
        _ = t c := by rw [h2]
    change (k : S.Qt ≃ₗ[ZMod 2] S.Qt) a +
      (k : S.Qt ≃ₗ[ZMod 2] S.Qt) (t c) = a + t c
    rw [hka, htc]
  have hinf_le_span : C' ⊓ fixSpace t ≤ Submodule.span (ZMod 2) {(A.v : S.Qt)} := by
    intro u hu
    have huC' : u ∈ C' := hu.1
    have huV : u ∈ Vt S g D.t := by
      rw [← W.hFix]
      exact hu.2
    have hfixCX : ∀ c ∈ A.CX, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u :=
      fun c hc => hC'K u huC' c (SwapW4.CX_le_K W A hc)
    rcases SwapW4.fix_CX W A hHS ⟨u, huV⟩ hfixCX with h0 | hv
    · rw [show u = 0 from congrArg Subtype.val h0]
      exact Submodule.zero_mem _
    · rw [show u = (A.v : S.Qt) from congrArg Subtype.val hv]
      exact Submodule.subset_span rfl
  have hinf_le_one : finrank (ZMod 2) ↥(C' ⊓ fixSpace t) ≤ 1 := by
    have hv0 : (A.v : S.Qt) ≠ 0 := by
      intro h
      have h' : A.v = 0 := Subtype.ext h
      have h0 : A.Q A.v = 0 := by rw [h']; exact map_zero A.Q
      rw [A.hv] at h0
      exact one_ne_zero h0
    calc finrank (ZMod 2) ↥(C' ⊓ fixSpace t)
        ≤ finrank (ZMod 2) (Submodule.span (ZMod 2) {(A.v : S.Qt)}) :=
          Submodule.finrank_mono hinf_le_span
      _ = 1 := finrank_span_singleton hv0
  have hdim := CFSG.LargeExtraspecial.S2.finrank_le_two_mul_inf_fixSpace (M := S.Qt) htt
    (W := C') hC't
  have hCC' : finrank (ZMod 2) C ≤ finrank (ZMod 2) C' :=
    Submodule.finrank_mono (le_sup_left : C ≤ C')
  omega

end Goursat

end CFSG.GF2Type.Smith1979.W4Swap

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvField

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace SuzukiAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

variable (m : ℕ)

theorem centralizes_center_of_involutive (hm : 0 < m) (α : MulAut (SuzukiMatrixGroup m))
    (hαα : ∀ g, α (α g) = g) (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m)
    (hH : ∀ x : (BinaryGaloisField (2 * m + 1))ˣ, ∃ x', α (torus m x) = torus m x') :
    ∀ b : BinaryGaloisField (2 * m + 1), α (root m 0 b) = root m 0 b := by
  classical
  have hrm := root_mul m hm
  have hex : ∀ a b : BinaryGaloisField (2 * m + 1),
      ∃ c d : BinaryGaloisField (2 * m + 1), α (root m a b) = root m c d :=
    fun a b => (mem_rootSub m).mp (hR _ (root_mem m a b))
  choose L M hLM using hex
  have hZ : ∀ z ∈ sylowCenter (rootSub m), α z ∈ sylowCenter (rootSub m) := by
    intro z hz
    rw [mem_sylowCenter] at hz ⊢
    refine ⟨hR z hz.1, fun t ht => ?_⟩
    have ht' : α t ∈ rootSub m := hR t ht
    calc t * α z = α (α t) * α z := by rw [hαα]
      _ = α (α t * z) := (map_mul α _ _).symm
      _ = α (z * α t) := by rw [hz.2 (α t) ht']
      _ = α z * t := by rw [map_mul, hαα]
  have hcen : ∀ b : BinaryGaloisField (2 * m + 1), L 0 b = 0 := by
    intro b
    have h := hZ _ ((mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩)
    rw [hLM] at h
    obtain ⟨b', hb'⟩ := (mem_sylowCenter_rootSub m hm).mp h
    exact (root_injective m hb').1
  have hprod : ∀ a b a' b' : BinaryGaloisField (2 * m + 1),
      L (a + a') (b + b' + a * tits m a') = L a b + L a' b' ∧
        M (a + a') (b + b' + a * tits m a') = M a b + M a' b' + L a b * tits m (L a' b') := by
    intro a b a' b'
    have h := map_mul α (root m a b) (root m a' b')
    rw [hrm, hLM, hLM, hLM, hrm] at h
    exact root_injective m h
  have hL : ∀ a b : BinaryGaloisField (2 * m + 1), L a b = L a 0 := by
    intro a b
    have h := (hprod a 0 0 b).1
    simp only [add_zero, zero_add, map_zero, mul_zero] at h
    rw [h, hcen b, add_zero]
  have hM : ∀ a b : BinaryGaloisField (2 * m + 1), M a b = M a 0 + M 0 b := by
    intro a b
    have h := (hprod a 0 0 b).2
    simp only [add_zero, zero_add, map_zero, mul_zero] at h
    rw [h, hcen b, map_zero, mul_zero, add_zero]
  have hLadd : ∀ a a' : BinaryGaloisField (2 * m + 1), L (a + a') 0 = L a 0 + L a' 0 := by
    intro a a'
    have h := (hprod a 0 a' 0).1
    rw [hL] at h
    exact h
  have hLL : ∀ a : BinaryGaloisField (2 * m + 1), L (L a 0) 0 = a := by
    intro a
    have h := hαα (root m a 0)
    rw [hLM, hLM] at h
    have h1 := (root_injective m h).1
    rwa [hL] at h1
  choose θ hθ using hH
  have htor : ∀ (x : (BinaryGaloisField (2 * m + 1))ˣ) (a b : BinaryGaloisField (2 * m + 1)),
      (θ x : BinaryGaloisField (2 * m + 1)) * L a b =
          L ((x : BinaryGaloisField (2 * m + 1)) * a)
            ((x : BinaryGaloisField (2 * m + 1)) *
              tits m (x : BinaryGaloisField (2 * m + 1)) * b) ∧
        (θ x : BinaryGaloisField (2 * m + 1)) * tits m (θ x : BinaryGaloisField (2 * m + 1)) *
            M a b =
          M ((x : BinaryGaloisField (2 * m + 1)) * a)
            ((x : BinaryGaloisField (2 * m + 1)) *
              tits m (x : BinaryGaloisField (2 * m + 1)) * b) := by
    intro x a b
    have h := congrArg α (torus_conj_root m a b x)
    rw [map_mul, map_mul, map_inv, hθ, hLM, hLM, torus_conj_root] at h
    exact root_injective m h
  have hLzero : ∀ a : BinaryGaloisField (2 * m + 1), L a 0 = 0 → a = 0 := by
    intro a ha
    rw [← hLL a, ha, hcen 0]
  obtain ⟨lam, hlamdef⟩ : ∃ lam, L 1 0 = lam := ⟨_, rfl⟩
  have hlam0 : lam ≠ 0 := fun h => one_ne_zero (hLzero 1 (hlamdef.trans h))
  set φ : BinaryGaloisField (2 * m + 1) → BinaryGaloisField (2 * m + 1) :=
    fun a => L a 0 * lam⁻¹ with hφdef
  have hLφ : ∀ a, L a 0 = φ a * lam := fun a => by
    simp only [hφdef]
    field_simp
  have hφ1 : φ 1 = 1 := by
    simp only [hφdef, hlamdef]
    exact mul_inv_cancel₀ hlam0
  have hφ0 : φ 0 = 0 := by simp only [hφdef, hcen 0, zero_mul]
  have hφadd : ∀ a a', φ (a + a') = φ a + φ a' := by
    intro a a'
    simp only [hφdef, hLadd]
    ring
  have hφmul : ∀ x a, φ (x * a) = φ x * φ a := by
    intro x a
    by_cases hx : x = 0
    · rw [hx, zero_mul, hφ0, zero_mul]
    · have h1 := (htor (Units.mk0 x hx) a 0).1
      have h2 := (htor (Units.mk0 x hx) 1 0).1
      simp only [Units.val_mk0, mul_one, mul_zero, hlamdef] at h1 h2
      simp only [hφdef]
      rw [← h1, ← h2]
      field_simp
  let φr : BinaryGaloisField (2 * m + 1) →+* BinaryGaloisField (2 * m + 1) :=
    { toFun := φ
      map_one' := hφ1
      map_mul' := hφmul
      map_zero' := hφ0
      map_add' := hφadd }
  have hlamφ : lam * φ lam = 1 := by
    have h := hLL 1
    rw [hlamdef, hLφ] at h
    linear_combination h
  have hφφ' : ∀ a, φr (φr a) = a := by
    intro a
    have h := hLL a
    rw [hLφ, hLφ, hφmul] at h
    change φ (φ a) = a
    calc φ (φ a) = φ (φ a) * (lam * φ lam) := by rw [hlamφ, mul_one]
      _ = a := by linear_combination h
  have hKcard : Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
    simpa [BinaryGaloisField] using GaloisField.card 2 (2 * m + 1) (by omega)
  have hφid : ∀ a, φ a = a := InvField.apply_eq_self_of_odd hKcard φr hφφ'
  have hlam1 : lam = 1 := by
    have h := hlamφ
    rw [hφid] at h
    exact CharTwo.sq_injective (show lam ^ 2 = 1 ^ 2 by rw [sq, h, one_pow])
  have hLid : ∀ a, L a 0 = a := fun a => by rw [hLφ, hφid, hlam1, mul_one]
  have hθid : ∀ x : (BinaryGaloisField (2 * m + 1))ˣ,
      (θ x : BinaryGaloisField (2 * m + 1)) = x := by
    intro x
    have h := (htor x 1 0).1
    simp only [mul_one, mul_zero] at h
    rw [hLid, hLid, mul_one] at h
    exact h
  have hN0 : M 0 0 = 0 := by
    have h := map_one α
    rw [← root_zero_zero m, hLM] at h
    exact (root_injective m h).2
  have hNsc : ∀ (x : (BinaryGaloisField (2 * m + 1))ˣ) (b : BinaryGaloisField (2 * m + 1)),
      M 0 ((x : BinaryGaloisField (2 * m + 1)) * tits m (x : BinaryGaloisField (2 * m + 1)) * b) =
        (x : BinaryGaloisField (2 * m + 1)) * tits m (x : BinaryGaloisField (2 * m + 1)) *
          M 0 b := by
    intro x b
    have h := (htor x 0 b).2
    rw [hθid, mul_zero] at h
    exact h.symm
  have hsurj : ∀ b : BinaryGaloisField (2 * m + 1), b ≠ 0 →
      ∃ x : (BinaryGaloisField (2 * m + 1))ˣ,
        (x : BinaryGaloisField (2 * m + 1)) * tits m (x : BinaryGaloisField (2 * m + 1)) = b := by
    intro b hb
    let g : (BinaryGaloisField (2 * m + 1))ˣ → (BinaryGaloisField (2 * m + 1))ˣ := fun x =>
      Units.mk0 ((x : BinaryGaloisField (2 * m + 1)) * tits m (x : BinaryGaloisField (2 * m + 1)))
        (mul_ne_zero (Units.ne_zero x) ((map_ne_zero (tits m)).mpr (Units.ne_zero x)))
    have hg : Function.Injective g := by
      intro x y h
      apply Units.ext
      have h' := congrArg (fun u : (BinaryGaloisField (2 * m + 1))ˣ =>
        (u : BinaryGaloisField (2 * m + 1))) h
      exact eq_of_mul_tits_eq m (Units.ne_zero y) h'
    obtain ⟨x, hx⟩ := (Finite.injective_iff_surjective.mp hg) (Units.mk0 b hb)
    exact ⟨x, congrArg (fun u : (BinaryGaloisField (2 * m + 1))ˣ =>
      (u : BinaryGaloisField (2 * m + 1))) hx⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, M 0 1 = ν := ⟨_, rfl⟩
  have hNlin : ∀ b, M 0 b = b * ν := by
    intro b
    by_cases hb : b = 0
    · rw [hb, hN0, zero_mul]
    · obtain ⟨x, hx⟩ := hsurj b hb
      have h := hNsc x 1
      rw [mul_one, hx, hνdef] at h
      exact h
  have hcomm : ∀ a a' : BinaryGaloisField (2 * m + 1),
      M 0 (a * tits m a') - M 0 (a' * tits m a) = a * tits m a' - a' * tits m a := by
    intro a a'
    have h1 := (hprod a 0 a' 0).2
    have h2 := (hprod a' 0 a 0).2
    rw [hM, hLid, hLid] at h1
    rw [hM, hLid, hLid, add_comm a' a] at h2
    simp only [zero_add] at h1 h2
    linear_combination h1 - h2
  obtain ⟨u, hu⟩ := exists_tits_ne m hm
  have hν1 : ν = 1 := by
    have h := hcomm 1 u
    rw [hNlin, hNlin, map_one, one_mul, mul_one] at h
    have h2 : (tits m u - u) * (ν - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hu
    · exact sub_eq_zero.mp h3
  intro b
  rw [hLM, hcen, hNlin, hν1, mul_one]

theorem invDichotomyAt_rootSub (hm : 0 < m) [Finite (SuzukiMatrixGroup m)]
    (S : Sylow 2 (SuzukiMatrixGroup m)) (hS : (S : Subgroup (SuzukiMatrixGroup m)) = rootSub m) :
    InvDichotomyAt (S : Subgroup (SuzukiMatrixGroup m)) := by
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
  apply invDichotomyAt_of_twisted hSE hcard hS₁
  intro α' hα'α' hα'S hα'S₁ _ _ _
  left
  have hα'R : ∀ s ∈ rootSub m, α' s ∈ rootSub m := by
    intro s hs
    rw [← hS] at hs ⊢
    exact InvInner.apply_mem_of_smul_eq hα'S hs
  have hα'H : ∀ x : (BinaryGaloisField (2 * m + 1))ˣ, ∃ x', α' (torus m x) = torus m x' := by
    intro x
    have h1 := Omega.mem_normalizer_smul (α := α') (hHN (torus_mem m x))
    have h2 := Omega.mem_normalizer_smul (α := α') (hHN₁ (torus_mem m x))
    rw [hα'S] at h1
    rw [hα'S₁] at h2
    exact (mem_torusSub m hm).mp
      (Omega.mem_of_mem_normalizer_of_mem_normalizer hSE hS₁ hNR hHN₁ h1 h2)
  have hcentral := centralizes_root m hm α' hα'R
    (centralizes_center_of_involutive m hm α' hα'α' hα'R hα'H) hα'H
  intro s hs
  rw [hS] at hs
  obtain ⟨a, b, rfl⟩ := (mem_rootSub m).mp hs
  exact hcentral a b

end SuzukiAut

open SuzukiAut CFSG.Open CFSG.BenderSuzuki.MatrixGroups in
theorem invDichotomyAt_of_mulEquiv_sz {X : Type*} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* Sz a) (T : Sylow 2 X) : InvDichotomyAt (T : Subgroup X) := by
  let e'' : X ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e'' e''.surjective
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub a (by omega)
  exact invDichotomyAt_of_mulEquiv e''
    (invDichotomyAt_of_one_sylow S (invDichotomyAt_rootSub a (by omega) S hS)) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzukiModel
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

namespace SuzukiAut

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

variable (m : ℕ)

theorem eq_of_mul_tits_eq {u v : BinaryGaloisField (2 * m + 1)} (hv : v ≠ 0)
    (h : u * tits m u = v * tits m v) : u = v := by
  set w := u / v with hw
  have hwu : u = w * v := by rw [hw, div_mul_cancel₀ u hv]
  have htv : tits m v ≠ 0 := (map_ne_zero (tits m)).mpr hv
  have hw1 : w * tits m w = 1 := by
    rw [hwu, map_mul] at h
    have h2 : (w * tits m w) * (v * tits m v) = 1 * (v * tits m v) := by
      rw [one_mul]
      linear_combination h
    exact mul_right_cancel₀ (mul_ne_zero hv htv) h2
  have hw0 : w ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hw1
    exact zero_ne_one hw1
  have htw : tits m w = w⁻¹ := eq_inv_of_mul_eq_one_right hw1
  have hsq : w ^ 2 = w := by
    rw [← tits_tits, htw, map_inv₀, htw, inv_inv]
  have hw1' : w = 1 := by
    have h3 : w * (w - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hsq, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hw0
    · exact sub_eq_zero.mp h
  rw [hwu, hw1', one_mul]

theorem eq_zero_or_eq_of_tits_comm {a a' : BinaryGaloisField (2 * m + 1)} (ha : a ≠ 0)
    (h : a' * tits m a = a * tits m a') : a' = 0 ∨ a' = a := by
  set u := a' / a with hu
  have hua : a' = u * a := by rw [hu, div_mul_cancel₀ a' ha]
  have hta : tits m a ≠ 0 := (map_ne_zero (tits m)).mpr ha
  have h1 : tits m u = u := by
    rw [hua, map_mul] at h
    have h2 : (tits m u - u) * (a * tits m a) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (mul_ne_zero ha hta)
  have hsq : u ^ 2 = u := by rw [← tits_tits, h1, h1]
  have h3 : u * (u - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hsq, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · left
    rw [hua, h4, zero_mul]
  · right
    rw [hua, sub_eq_zero.mp h4, one_mul]

theorem exists_tits_ne (hm : 0 < m) : ∃ u : BinaryGaloisField (2 * m + 1), tits m u ≠ u := by
  by_contra hcon
  push Not at hcon
  have h2 : ∀ u : BinaryGaloisField (2 * m + 1), u ^ 2 = u := fun u => by
    rw [← tits_tits, hcon, hcon]
  have hsub : (Set.univ : Set (BinaryGaloisField (2 * m + 1))) ⊆ {0, 1} := by
    intro u _
    have h3 : u * (u - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h2 u, sub_self]
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  have hcard : Nat.card (BinaryGaloisField (2 * m + 1)) ≤ 2 := by
    calc Nat.card (BinaryGaloisField (2 * m + 1))
        = (Set.univ : Set (BinaryGaloisField (2 * m + 1))).ncard := (Set.ncard_univ _).symm
      _ ≤ ({0, 1} : Set (BinaryGaloisField (2 * m + 1))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ ({1} : Set (BinaryGaloisField (2 * m + 1))).ncard + 1 := Set.ncard_insert_le 0 {1}
      _ = 2 := by rw [Set.ncard_singleton]
  have hKcard : Nat.card (BinaryGaloisField (2 * m + 1)) = 2 ^ (2 * m + 1) := by
    simpa [BinaryGaloisField] using GaloisField.card 2 (2 * m + 1) (by omega)
  rw [hKcard] at hcard
  have : 2 ^ 1 < 2 ^ (2 * m + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem root_comm_iff (hm : 0 < m) (a b a' b' : BinaryGaloisField (2 * m + 1)) :
    root m a' b' * root m a b = root m a b * root m a' b' ↔ a' * tits m a = a * tits m a' := by
  rw [root_mul m hm, root_mul m hm]
  constructor
  · intro h
    have h2 := (root_injective m h).2
    linear_combination h2
  · intro h
    rw [add_comm a' a, h]
    congr 1
    ring

theorem centralizes_root (hm : 0 < m) (α : MulAut (SuzukiMatrixGroup m))
    (hR : ∀ r ∈ rootSub m, α r ∈ rootSub m)
    (hZ : ∀ b : BinaryGaloisField (2 * m + 1), α (root m 0 b) = root m 0 b)
    (hH : ∀ x : (BinaryGaloisField (2 * m + 1))ˣ, ∃ x', α (torus m x) = torus m x') :
    ∀ a b : BinaryGaloisField (2 * m + 1), α (root m a b) = root m a b := by
  classical
  have hrm := root_mul m hm
  have hex : ∀ a b : BinaryGaloisField (2 * m + 1),
      ∃ c d : BinaryGaloisField (2 * m + 1), α (root m a b) = root m c d :=
    fun a b => (mem_rootSub m).mp (hR _ (root_mem m a b))
  choose L M hLM using hex
  have hprod : ∀ a b a' b' : BinaryGaloisField (2 * m + 1),
      L (a + a') (b + b' + a * tits m a') = L a b + L a' b' ∧
        M (a + a') (b + b' + a * tits m a') = M a b + M a' b' + L a b * tits m (L a' b') := by
    intro a b a' b'
    have h := map_mul α (root m a b) (root m a' b')
    rw [hrm, hLM, hLM, hLM, hrm] at h
    exact root_injective m h
  have hcen : ∀ b : BinaryGaloisField (2 * m + 1), L 0 b = 0 ∧ M 0 b = b := by
    intro b
    have h := hZ b
    rw [hLM] at h
    exact root_injective m h
  have hL : ∀ a b : BinaryGaloisField (2 * m + 1), L a b = L a 0 := by
    intro a b
    have h := (hprod a 0 0 b).1
    simp only [add_zero, zero_add, map_zero, mul_zero] at h
    rw [h, (hcen b).1, add_zero]
  have hM : ∀ a b : BinaryGaloisField (2 * m + 1), M a b = M a 0 + b := by
    intro a b
    have h := (hprod a 0 0 b).2
    simp only [add_zero, zero_add, map_zero, mul_zero] at h
    rw [h, (hcen b).2, (hcen b).1, map_zero, mul_zero, add_zero]
  choose θ hθ using hH
  have htor : ∀ (x : (BinaryGaloisField (2 * m + 1))ˣ) (a b : BinaryGaloisField (2 * m + 1)),
      (θ x : BinaryGaloisField (2 * m + 1)) * L a 0 =
          L ((x : BinaryGaloisField (2 * m + 1)) * a) 0 ∧
        (θ x : BinaryGaloisField (2 * m + 1)) * tits m (θ x : BinaryGaloisField (2 * m + 1)) *
            (M a 0 + b) =
          M ((x : BinaryGaloisField (2 * m + 1)) * a) 0 +
            (x : BinaryGaloisField (2 * m + 1)) *
              tits m (x : BinaryGaloisField (2 * m + 1)) * b := by
    intro x a b
    have h := congrArg α (torus_conj_root m a b x)
    rw [map_mul, map_mul, map_inv, hθ, hLM, hLM, torus_conj_root] at h
    have h2 := root_injective m h
    rw [hL a b, hM a b, hL ((x : BinaryGaloisField (2 * m + 1)) * a),
      hM ((x : BinaryGaloisField (2 * m + 1)) * a)] at h2
    exact h2
  have hθx : ∀ x : (BinaryGaloisField (2 * m + 1))ˣ, (θ x : BinaryGaloisField (2 * m + 1)) = x := by
    intro x
    have h1 := (htor x 0 1).2
    simp only [mul_zero, (hcen 0).2, zero_add, mul_one] at h1
    exact eq_of_mul_tits_eq m (Units.ne_zero _) h1
  have hℓ : ∀ (x : (BinaryGaloisField (2 * m + 1))ˣ) (a : BinaryGaloisField (2 * m + 1)),
      L ((x : BinaryGaloisField (2 * m + 1)) * a) 0 =
        (x : BinaryGaloisField (2 * m + 1)) * L a 0 := by
    intro x a
    rw [← (htor x a 0).1, hθx]
  have hγ : ∀ (x : (BinaryGaloisField (2 * m + 1))ˣ) (a : BinaryGaloisField (2 * m + 1)),
      M ((x : BinaryGaloisField (2 * m + 1)) * a) 0 =
        (x : BinaryGaloisField (2 * m + 1)) *
          tits m (x : BinaryGaloisField (2 * m + 1)) * M a 0 := by
    intro x a
    have h := (htor x a 0).2
    simp only [hθx, add_zero, mul_zero] at h
    exact h.symm
  set lam := L 1 0 with hlam
  have hℓlam : ∀ a : BinaryGaloisField (2 * m + 1), L a 0 = a * lam := by
    intro a
    by_cases ha : a = 0
    · rw [ha, (hcen 0).1, zero_mul]
    · have := hℓ (Units.mk0 a ha) 1
      simpa only [Units.val_mk0, mul_one] using this
  have hγrel : ∀ a a' : BinaryGaloisField (2 * m + 1),
      M (a + a') 0 + a * tits m a' = M a 0 + M a' 0 + L a 0 * tits m (L a' 0) := by
    intro a a'
    have h := (hprod a 0 a' 0).2
    rw [hM (a + a'), zero_add, zero_add] at h
    exact h
  obtain ⟨u, hu⟩ := exists_tits_ne m hm
  have hlam1 : lam * tits m lam = 1 := by
    have h1 := hγrel 1 u
    have h2 := hγrel u 1
    rw [add_comm u 1] at h2
    simp only [hℓlam, map_one, map_mul, one_mul, mul_one] at h1 h2
    have h3 : (tits m u - u) * (1 - lam * tits m lam) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) hu
    · exact (sub_eq_zero.mp h4).symm
  have hlam_ne : lam ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at hlam1
    exact zero_ne_one hlam1
  have hlam_one : lam = 1 := by
    have : lam * tits m lam = 1 * tits m 1 := by rw [hlam1, map_one, one_mul]
    exact eq_of_mul_tits_eq m one_ne_zero this
  have hγadd : ∀ a a' : BinaryGaloisField (2 * m + 1), M (a + a') 0 = M a 0 + M a' 0 := by
    intro a a'
    have h := hγrel a a'
    rw [hℓlam, hℓlam, hlam_one, mul_one, mul_one] at h
    linear_combination h
  set c := M 1 0 with hc
  have hγc : ∀ a : BinaryGaloisField (2 * m + 1), a ≠ 0 → M a 0 = a * tits m a * c := by
    intro a ha
    have := hγ (Units.mk0 a ha) 1
    simpa only [Units.val_mk0, mul_one] using this
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (map_zero _)
  have hu1 : (1 : BinaryGaloisField (2 * m + 1)) + u ≠ 0 := by
    intro h
    have hu' : u = 1 := by
      have := CharTwo.add_eq_zero.mp h
      exact this.symm
    rw [hu', map_one] at hu
    exact hu rfl
  have hc0 : c = 0 := by
    have h := hγadd 1 u
    rw [hγc _ hu1, hγc _ one_ne_zero, hγc _ hu0, map_add, map_one] at h
    have h2 : (tits m u + u) * c = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h4 | h4
    · exfalso
      apply hu
      have := CharTwo.add_eq_zero.mp h4
      exact this
    · exact h4
  have hγ0 : ∀ a : BinaryGaloisField (2 * m + 1), M a 0 = 0 := by
    intro a
    by_cases ha : a = 0
    · rw [ha, (hcen 0).2]
    · rw [hγc a ha, hc0, mul_zero]
  intro a b
  rw [hLM, hL, hM, hℓlam, hlam_one, mul_one, hγ0, zero_add]

noncomputable def suzukiEquiv (a : ℕ) : SuzukiMatrixGroup a ≃* Sz a :=
  (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a).symm).trans
    (MulEquiv.subgroupCongr (by
      simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, Sz,
        CFSG.Open.SzGenerators]))

theorem isSimpleGroup_suzukiMatrixGroup (hm : 0 < m) [Finite (SuzukiMatrixGroup m)] :
    IsSimpleGroup (SuzukiMatrixGroup m) :=
  CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup
    (Or.inr (Or.inr ⟨m, hm, ⟨suzukiEquiv m⟩⟩))

theorem weyl_inv_conj_torus (x : (BinaryGaloisField (2 * m + 1))ˣ) :
    (weyl m)⁻¹ * torus m x * weyl m = torus m x⁻¹ := by
  have h := weyl_conj_torus m x⁻¹
  rw [inv_inv] at h
  rw [← h]
  group

theorem autControlAt_rootSub (hm : 0 < m) [Finite (SuzukiMatrixGroup m)] :
    AutControlAt (rootSub m) := by
  intro α hn hz _ hout
  exfalso
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub m hm
  obtain ⟨hNR, hcard⟩ := normalizer_and_card_sylow m hm
  obtain ⟨hSE, -, -, -⟩ := benderBorel_sylowCenter (bender_suzukiMatrixGroup_borel m hm) S
  have : IsSimpleGroup (SuzukiMatrixGroup m) := isSimpleGroup_suzukiMatrixGroup m hm
  have hHN : torusSub m ≤ Subgroup.normalizer (((S : Subgroup (SuzukiMatrixGroup m))) : Set _) := by
    rw [hS]
    exact torusSub_le_normalizer m
  rw [← hS] at hn hz hNR hcard
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
  have hαS : α • S = S := Omega.smul_eq_of_mapsTo hn
  obtain ⟨r, hr, hrS₁⟩ := Omega.exists_conj_adjust hSE hcard hS₁ α hαS
  set α' := (MulAut.conj r)⁻¹ * α with hα'
  have happ : ∀ g, α' g = r⁻¹ * α g * r := fun g => by
    rw [hα', MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
  have hα'S : α' • S = S := by
    rw [hα', mul_smul, hαS, inv_smul_eq_iff, Omega.conj_smul_self hr]
  have hα'R : ∀ s ∈ rootSub m, α' s ∈ rootSub m := by
    intro s hs
    rw [← hS] at hs ⊢
    rw [happ]
    have h1 := (S : Subgroup (SuzukiMatrixGroup m)).inv_mem hr
    exact (S : Subgroup (SuzukiMatrixGroup m)).mul_mem
      ((S : Subgroup (SuzukiMatrixGroup m)).mul_mem h1 (hn s hs)) hr
  have hα'Z : ∀ b : BinaryGaloisField (2 * m + 1), α' (root m 0 b) = root m 0 b := by
    intro b
    have hZ : root m 0 b ∈ sylowCenter (S : Subgroup (SuzukiMatrixGroup m)) := by
      rw [hS]
      exact (mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩
    rw [happ, hz _ hZ, mul_assoc, ← (mem_sylowCenter.mp hZ).2 r hr, inv_mul_cancel_left]
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
  exact hout r (hS ▸ hr) hone.symm

theorem centPairAt_rootSub (hm : 0 < m) : CentPairAt (rootSub m) := by
  intro s hs hsZ
  obtain ⟨a, b, rfl⟩ := (mem_rootSub m).mp hs
  have ha : a ≠ 0 := by
    rintro rfl
    exact hsZ ((mem_sylowCenter_rootSub m hm).mpr ⟨b, rfl⟩)
  obtain ⟨u, hu⟩ := exists_tits_ne m hm
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hu (map_zero _)
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hu (map_one _)
  let x : (BinaryGaloisField (2 * m + 1))ˣ := Units.mk0 u hu0
  refine ⟨(torus m x)⁻¹, Subgroup.inv_mem _ (torusSub_le_normalizer m (torus_mem m x)), ?_⟩
  intro t ht hc₁ hc₂
  obtain ⟨a', b', rfl⟩ := (mem_rootSub m).mp ht
  rw [inv_inv, torus_conj_root] at hc₂
  have e1 := (root_comm_iff m hm a b a' b').mp hc₁
  have e2 := (root_comm_iff m hm _ _ a' b').mp hc₂
  rcases eq_zero_or_eq_of_tits_comm m ha e1 with h0 | h1
  · exact (mem_sylowCenter_rootSub m hm).mpr ⟨b', by rw [h0]⟩
  · exfalso
    have hxa : (x : BinaryGaloisField (2 * m + 1)) * a ≠ 0 := mul_ne_zero (Units.ne_zero x) ha
    rcases eq_zero_or_eq_of_tits_comm m hxa e2 with h0' | h1'
    · exact ha (h1 ▸ h0')
    · apply hu1
      have h2 : (x : BinaryGaloisField (2 * m + 1)) * a = 1 * a := by rw [← h1', h1, one_mul]
      exact mul_right_cancel₀ ha h2

theorem autControlAt_suzukiMatrixGroup (hm : 0 < m) [Finite (SuzukiMatrixGroup m)]
    (T : Sylow 2 (SuzukiMatrixGroup m)) : AutControlAt (T : Subgroup (SuzukiMatrixGroup m)) := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub m hm
  exact autControlAt_of_one_sylow S (hS ▸ autControlAt_rootSub m hm) T

theorem centPairAt_suzukiMatrixGroup (hm : 0 < m) [Finite (SuzukiMatrixGroup m)]
    (T : Sylow 2 (SuzukiMatrixGroup m)) : CentPairAt (T : Subgroup (SuzukiMatrixGroup m)) := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub m hm
  exact centPairAt_of_one_sylow S (hS ▸ centPairAt_rootSub m hm) T

end SuzukiAut

open SuzukiAut CFSG.Open CFSG.BenderSuzuki.MatrixGroups in
theorem autControlAt_of_mulEquiv_sz {X : Type*} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* Sz a) (T : Sylow 2 X) : AutControlAt (T : Subgroup X) := by
  let e'' : X ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e'' e''.surjective
  exact autControlAt_of_mulEquiv e'' (autControlAt_suzukiMatrixGroup a (by omega)) T

open SuzukiAut CFSG.Open CFSG.BenderSuzuki.MatrixGroups in
theorem centPairAt_of_mulEquiv_sz {X : Type*} [Group X] [Finite X] {a : ℕ} (ha : 1 ≤ a)
    (e : X ≃* Sz a) (T : Sylow 2 X) : CentPairAt (T : Subgroup X) := by
  let e'' : X ≃* SuzukiMatrixGroup a := e.trans (suzukiEquiv a).symm
  have : Finite (SuzukiMatrixGroup a) := Finite.of_surjective e'' e''.surjective
  exact centPairAt_of_mulEquiv e'' (centPairAt_suzukiMatrixGroup a (by omega)) T

end Bender

end CFSG.ComponentClassification.AschbacherToolkit

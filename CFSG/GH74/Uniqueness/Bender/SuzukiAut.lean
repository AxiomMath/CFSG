module

public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.GH74.Uniqueness.Bender.CentralizesCenter
public import CFSG.GH74.Uniqueness.Bender.Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzuki

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Transport

variable {G : Type*} [Group G]

@[expose] def CentralizingInner (S : Subgroup G) : Prop :=
  ∀ α : MulAut G, (∀ s ∈ S, α s ∈ S) → (∀ z ∈ rootCenter S, α z = z) →
    ∃ s ∈ S, α = MulAut.conj s

open CFSG.ComponentClassification.AschbacherToolkit.Bender.AutTransport in
theorem CentralizingInner.map_mulEquiv {G' : Type*} [Group G'] {S : Subgroup G}
    (h : CentralizingInner S) (e : G ≃* G') : CentralizingInner (S.map e.toMonoidHom) := by
  intro α' hn hz
  set α := (MulAut.congr e).symm α' with hαdef
  have hα' : α' = MulAut.congr e α := by rw [hαdef, MulEquiv.apply_symm_apply]
  have happ : ∀ g, α g = e.symm (α' (e g)) := fun g => congr_symm_apply' e α' g
  have hn' : ∀ s ∈ S, α s ∈ S := by
    intro s hs
    rw [happ, ← mem_map_iff' e]
    exact hn _ ((mem_map_iff e).mpr hs)
  have hz' : ∀ z ∈ rootCenter S, α z = z := by
    intro z hz₀
    rw [happ, hz _ ((mem_sylowCenter_map e).mpr hz₀), MulEquiv.symm_apply_apply]
  obtain ⟨s, hs, hαs⟩ := h α hn' hz'
  exact ⟨e s, (mem_map_iff e).mpr hs, by rw [hα', hαs, congr_conj]⟩

theorem CentralizingInner.of_one_sylow [Finite G] (R : Sylow 2 G)
    (h : CentralizingInner (R : Subgroup G)) (T : Sylow 2 G) :
    CentralizingInner (T : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  have hT : (T : Subgroup G) = (R : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.map_mulEquiv (MulAut.conj g)

theorem CentralizingInner.of_mulEquiv [Finite G] {G' : Type*} [Group G'] (e : G ≃* G')
    (hG' : ∀ T : Sylow 2 G', CentralizingInner (T : Subgroup G')) (T : Sylow 2 G) :
    CentralizingInner (T : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (hG' (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map_mulEquiv e.symm
  have h' : CentralizingInner (((T : Subgroup G).map e.toMonoidHom).map e.symm.toMonoidHom) := h
  rw [Subgroup.map_map] at h'
  convert h'
  ext x
  simp

end Transport

section SuzukiMatrix

open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut
open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.BenderSuzuki.PFAppendixIII

variable (m : ℕ)

theorem centralizingInner_rootSub (hm : 0 < m) [Finite (SuzukiMatrixGroup m)] :
    CentralizingInner (rootSub m) := by
  intro α hn hz
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
  exact ⟨r, hS ▸ hr, hone.symm⟩

theorem centralizingInner_suzukiMatrixGroup (hm : 0 < m) [Finite (SuzukiMatrixGroup m)]
    (T : Sylow 2 (SuzukiMatrixGroup m)) : CentralizingInner (T : Subgroup (SuzukiMatrixGroup m)) := by
  obtain ⟨S, hS⟩ := exists_sylow_eq_rootSub m hm
  exact CentralizingInner.of_one_sylow S (hS ▸ centralizingInner_rootSub m hm) T

end SuzukiMatrix

section BenderTypeLevel

variable {K : Type*} [Group K] [Finite K]

theorem BenderType.centralizingInner_suzuki {n e : ℕ} (h : BenderType K n 2 e)
    (Q : Sylow 2 K) : CentralizingInner (Q : Subgroup K) := by
  cases h with
  | suzuki a ha e₁ =>
    let e₂ : K ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
      e₁.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a))
    have : Finite (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) :=
      Finite.of_equiv K e₂.toEquiv
    exact CentralizingInner.of_mulEquiv e₂ (centralizingInner_suzukiMatrixGroup a (by omega)) Q

theorem BenderType.exists_eq_conj_of_centralizes_center_suzuki
    {n e : ℕ}
    (h : BenderType K n 2 e) (Q : Sylow 2 K) (σ : MulAut K)
    (hσ : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z) :
    ∃ r ∈ (Q : Subgroup K), σ = MulAut.conj r :=
  h.centralizingInner_suzuki Q σ (h.mem_of_centralizes_rootCenter Q σ hσ) hσ

theorem BenderType.aut_eq_conj_cartan_suzuki
    {K : Type} [Group K] [Finite K] {n : ℕ}
    (h : BenderType K n 2 1) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d) :
    ∃ d₀ ∈ cartan (Q : Subgroup K) t, ∀ k, σ k = d₀ * k * d₀⁻¹ := by
  have hc := h.benderCore Q ht htQ
  obtain ⟨z₀, hz₀, hz₀1⟩ := hc.exists_involution
  have hσz₀ : σ z₀ ∈ rootCenter (Q : Subgroup K) ∧ σ z₀ ≠ 1 := by
    refine ⟨hc.mem_rootCenter_of_mul_self (hσQ z₀ (rootCenter_le _ hz₀)) ?_, ?_⟩
    · rw [← map_mul, hc.center_sq z₀ hz₀, map_one]
    · intro h1
      apply hz₀1
      apply σ.injective
      rw [h1, map_one]
  obtain ⟨d, hd, hdσ⟩ := hc.exists_cartan_conj hz₀ hz₀1 hσz₀.1 hσz₀.2
  have hZ : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = d⁻¹ * z * d := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]; simp
    · obtain ⟨e, he, hez⟩ := hc.exists_cartan_conj hz₀ hz₀1 hz hz1
      have hσe : σ e = e := hσD e he
      have hσe' : σ e⁻¹ = e⁻¹ := hσD e⁻¹ ((cartan _ t).inv_mem he)
      calc σ z = σ (e⁻¹ * z₀ * e) := by rw [hez]
        _ = e⁻¹ * σ z₀ * e := by rw [map_mul, map_mul, hσe, hσe']
        _ = e⁻¹ * (d⁻¹ * z₀ * d) * e := by rw [hdσ]
        _ = d⁻¹ * (e⁻¹ * z₀ * e) * d := by
          have hc2 : e⁻¹ * d⁻¹ = d⁻¹ * e⁻¹ :=
            hc.cartan_comm ((cartan _ t).inv_mem he) ((cartan _ t).inv_mem hd)
          have hc3 : d * e = e * d := hc.cartan_comm hd he
          calc e⁻¹ * (d⁻¹ * z₀ * d) * e = (e⁻¹ * d⁻¹) * z₀ * (d * e) := by group
            _ = (d⁻¹ * e⁻¹) * z₀ * (e * d) := by rw [hc2, hc3]
            _ = d⁻¹ * (e⁻¹ * z₀ * e) * d := by group
        _ = d⁻¹ * z * d := by rw [hez]
  set σ'' : MulAut K := MulAut.conj d * σ with hσ''
  have hσ''app : ∀ k, σ'' k = d * σ k * d⁻¹ := fun k => by
    simp [hσ'', MulAut.conj_apply]
  have hdB : d ∈ borel (Q : Subgroup K) := cartan_le_borel _ t hd
  have hσ''Q : ∀ x ∈ (Q : Subgroup K), σ'' x ∈ (Q : Subgroup K) := by
    intro x hx
    rw [hσ''app]
    have hσx := hσQ x hx
    exact ((Subgroup.mem_normalizer_iff.mp hdB) (σ x)).mp hσx
  have hcen : ∀ z ∈ rootCenter (Q : Subgroup K), σ'' z = z := by
    intro z hz
    rw [hσ''app, hZ z hz]
    group
  obtain ⟨r, hr, hσr⟩ := h.exists_eq_conj_of_centralizes_center_suzuki Q σ'' hcen
  have hDfix : ∀ d' ∈ cartan (Q : Subgroup K) t, σ'' d' = d' := by
    intro d' hd'
    rw [hσ''app, hσD d' hd']
    have := hc.cartan_comm hd hd'
    calc d * d' * d⁻¹ = d' * d * d⁻¹ := by rw [this]
      _ = d' := by group
  have hDr : ∀ d' ∈ cartan (Q : Subgroup K) t, d' * r = r * d' := by
    intro d' hd'
    have h2 : σ'' d' = r * d' * r⁻¹ := by rw [hσr]; rfl
    rw [hDfix d' hd'] at h2
    calc d' * r = (r * d' * r⁻¹) * r := by rw [← h2]
      _ = r * d' := by group
  have hr1 : r = 1 := by
    by_contra hr1
    have hRD := h.suzuki_rootData Q
    have hQcard : Nat.card (Q : Subgroup K) = 2 ^ n + (2 ^ n - 1) * 2 ^ n := by
      rw [hc.card_eq]
      have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      zify [h4]
      ring
    obtain ⟨z, hz, hz1, hDz⟩ : ∃ z ∈ rootCenter (Q : Subgroup K), z ≠ 1 ∧
        ∀ d' ∈ cartan (Q : Subgroup K) t, d' * z = z * d' := by
      by_cases hr2 : r * r = 1
      · exact ⟨r, hc.mem_rootCenter_of_mul_self hr hr2, hr1, hDr⟩
      · have hr2' : r ^ 2 ≠ 1 := by rwa [sq]
        have hsq := sq_sq_eq_one_of_rootData hRD hQcard ⟨r, hr⟩ (fun h1 => hr2' (by
          have := congrArg Subtype.val h1
          simpa using this))
        have hrr : (r * r) * (r * r) = 1 := by
          have := congrArg Subtype.val hsq
          simpa [sq, mul_assoc] using this
        refine ⟨r * r, hc.mem_rootCenter_of_mul_self
          ((Q : Subgroup K).mul_mem hr hr) hrr, hr2, fun d' hd' => ?_⟩
        calc d' * (r * r) = (d' * r) * r := by group
          _ = (r * d') * r := by rw [hDr d' hd']
          _ = r * (d' * r) := by group
          _ = r * (r * d') := by rw [hDr d' hd']
          _ = (r * r) * d' := by group
    have hDle : cartan (Q : Subgroup K) t ≤ centralizer ({z} : Set K) := by
      intro d' hd'
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact (hDz d' hd').symm
    have hbot : cartan (Q : Subgroup K) t = ⊥ := by
      have := hc.cartan_inf_centralizer_eq hz hz1
      rw [hc.fixCartan_eq_bot, inf_eq_left.mpr hDle] at this
      exact this
    have hcard := hc.card_cartan
    rw [hbot, Subgroup.card_bot] at hcard
    have hn2 := h.two_le.2
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hσ''one : σ'' = 1 := by rw [hσr, hr1, map_one]
  refine ⟨d⁻¹, (cartan _ t).inv_mem hd, fun k => ?_⟩
  have hk : σ'' k = k := by rw [hσ''one]; rfl
  calc σ k = d⁻¹ * (d * σ k * d⁻¹) * d := by group
    _ = d⁻¹ * σ'' k * d := by rw [hσ''app k]
    _ = d⁻¹ * k * d := by rw [hk]
    _ = d⁻¹ * k * d⁻¹⁻¹ := by rw [inv_inv]

end BenderTypeLevel

section Combined

theorem BenderType.exists_eq_conj_of_centralizes_center_of_ne_three
    {K : Type} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) (hi : i ≠ 3) (Q : Sylow 2 K) (σ : MulAut K)
    (hσ : ∀ z ∈ rootCenter (Q : Subgroup K), σ z = z) :
    ∃ r ∈ (Q : Subgroup K), σ = MulAut.conj r := by
  rcases h.cases' with ⟨hi1, he1, -⟩ | ⟨hi2, -, -⟩ | ⟨hi3, -, -⟩
  · subst hi1
    obtain ⟨t, hc⟩ := h.exists_benderCore Q
    have hQZ : rootCenter (Q : Subgroup K) = (Q : Subgroup K) :=
      Subgroup.eq_of_le_of_card_ge (rootCenter_le _) (by rw [hc.card_eq, hc.card_center, pow_one])
    obtain ⟨r, hr, hσr⟩ := h.lemma_3_6_a Q σ (fun x hx => hσ x (by rw [hQZ]; exact hx))
    exact ⟨r, rootCenter_le _ hr, MulEquiv.ext fun k => hσr k⟩
  · subst hi2
    exact h.exists_eq_conj_of_centralizes_center_suzuki Q σ hσ
  · exact absurd hi3 hi

end Combined

end CFSG.GH74.Uniqueness.Bender

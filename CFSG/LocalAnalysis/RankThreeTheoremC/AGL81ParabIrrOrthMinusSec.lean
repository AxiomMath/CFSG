module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrOrthMinusIso
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabIrrGeneric

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
  CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr

section Scalar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Sup T : Submodule K V}

theorem scalarMod_unique {g : V → V} {a a' : K} (h : ScalarMod Sup T g a)
    (h' : ScalarMod Sup T g a') {v₀ : V} (hv₀ : v₀ ∈ Sup) (hv₀T : v₀ ∉ T) : a = a' := by
  by_contra hne
  apply hv₀T
  have h1 := T.sub_mem (h' v₀ hv₀) (h v₀ hv₀)
  have h2 : (a - a') • v₀ ∈ T := by
    have e : (g v₀ - a' • v₀) - (g v₀ - a • v₀) = (a - a') • v₀ := by
      rw [sub_smul]
      abel
    rwa [e] at h1
  have h3 := T.smul_mem (a - a')⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul] at h3

variable {G : Type*} [Group G] (ρ : G →* (V ≃ₗ[K] V)) {v₀ : V} (hv₀ : v₀ ∈ Sup) (hv₀T : v₀ ∉ T)
  (hT : ∀ x w, ρ x w ∈ T ↔ w ∈ T) (hsc : ∀ x, ∃ a : K, ScalarMod Sup T (ρ x) a)

include hv₀ hv₀T hT in
theorem choose_scalarMod_ne_zero (x : G) : Classical.choose (hsc x) ≠ 0 := by
  intro h0
  have h := Classical.choose_spec (hsc x) v₀ hv₀
  rw [h0, zero_smul, sub_zero] at h
  exact hv₀T ((hT x v₀).1 h)

@[expose] noncomputable def secChar : G →* Kˣ :=
  MonoidHom.mk' (fun x => Units.mk0 (Classical.choose (hsc x))
      (choose_scalarMod_ne_zero ρ hv₀ hv₀T hT hsc x)) fun x y => by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul]
    have h1 : ∀ a, ScalarMod Sup T (ρ (x * y)) a → ScalarMod Sup T (ρ x * ρ y) a := fun a h => by
      rwa [map_mul] at h
    have h2 : ScalarMod Sup T (ρ x * ρ y) (Classical.choose (hsc x) * Classical.choose (hsc y)) :=
      ScalarMod.mul (Classical.choose_spec (hsc x)) (Classical.choose_spec (hsc y))
        (fun w hw => (hT x w).2 hw)
    exact scalarMod_unique (h1 _ (Classical.choose_spec (hsc (x * y)))) h2 hv₀ hv₀T

theorem scalarMod_secChar (x : G) :
    ScalarMod Sup T (ρ x) ((secChar ρ hv₀ hv₀T hT hsc x : Kˣ) : K) :=
  Classical.choose_spec (hsc x)

end Scalar

section Conj

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Sup T : Submodule K V}
  {F : V ≃+ V} {σ : K ≃+* K} {hF : ∀ (c : K) (v : V), F (c • v) = σ c • F v}

theorem scalarMod_semilinConj (hS : ∀ v, F v ∈ Sup ↔ v ∈ Sup) (hT : ∀ v, F v ∈ T ↔ v ∈ T)
    {g : V ≃ₗ[K] V} {a : K} (h : ScalarMod Sup T g a) :
    ScalarMod Sup T (semilinConj F σ hF g) (σ a) := by
  intro v hv
  rw [semilinConj_apply]
  have hw : F.symm v ∈ Sup := (hS _).1 (by rwa [AddEquiv.apply_symm_apply])
  have h1 := (hT _).2 (h _ hw)
  rw [map_sub, hF, AddEquiv.apply_symm_apply] at h1
  exact h1

end Conj

section Res

variable {K : Type} [Field K] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

@[expose] def TrivRes {t : ℕ} (ht : t ≤ r) (g : 𝕍 ≃ₗ[K] 𝕍) : Prop :=
  ∀ v : 𝕍, IsResPerp ht v → g v - v ∈ tailFlag K (Fin 2 → K) r t

theorem trivRes_semilinConj {t : ℕ} (ht : t ≤ r) {F : 𝕍 ≃+ 𝕍} {σ : K ≃+* K}
    {hF : ∀ (c : K) (v : 𝕍), F (c • v) = σ c • F v}
    (hp : ∀ v, IsResPerp ht (F v) ↔ IsResPerp ht v)
    (hT : ∀ v, F v ∈ tailFlag K (Fin 2 → K) r t ↔ v ∈ tailFlag K (Fin 2 → K) r t)
    {g : 𝕍 ≃ₗ[K] 𝕍} (h : TrivRes ht g) : TrivRes ht (semilinConj F σ hF g) := by
  intro v hv
  rw [semilinConj_apply]
  have hw : IsResPerp ht (F.symm v) := (hp _).1 (by rwa [AddEquiv.apply_symm_apply])
  have h1 := (hT _).2 (h _ hw)
  rw [map_sub, AddEquiv.apply_symm_apply] at h1
  exact h1

theorem exists_mem_flag_not_mem (hd : OrthCuts r d) (l : Fin s) :
    ∃ v ∈ tailFlag K (Fin 2 → K) r (d l.succ), v ∉ tailFlag K (Fin 2 → K) r (d l.castSucc) := by
  have h1 := hd.mono (Fin.castSucc_lt_succ (i := l))
  have h2 : d l.succ ≤ r := (hd.mono.monotone (Fin.le_last l.succ)).trans hd.last
  refine ⟨hypVec K (Fin 2 → K) (.inl (⟨d l.castSucc, by omega⟩ : Fin r)),
    orthHypVec_mem_tailFlag (a := d l.succ) (j := ⟨d l.castSucc, by omega⟩) h1, fun hmem => ?_⟩
  have h3 := orth_fst_inl_eq_zero_of_mem_tailFlag hmem (u := ⟨d l.castSucc, by omega⟩) le_rfl
  simp [hypVec] at h3

end Res

theorem forall_eq_one_of_irred_cyclic {A : Type} [Group A] [Finite A] {N B : Subgroup A}
    (hcyc : ¬ IsCyclic ↥B) (hN : IrredOn N B) (hNB : N ≤ Subgroup.normalizer (B : Set A))
    {G : Type*} [Group G] (θ : ↥B →* G) (hθc : IsCyclic ↥θ.range)
    (hθ : ∀ n ∈ N, ∀ b : ↥B, θ b = 1 → ∀ hb : n * (b : A) * n⁻¹ ∈ B, θ ⟨_, hb⟩ = 1) :
    ∀ b, θ b = 1 := by
  set V : Subgroup A := θ.ker.map B.subtype with hV
  have hVB : V ≤ B := by
    rintro _ ⟨b, -, rfl⟩
    exact b.2
  have hNV : N ≤ Subgroup.normalizer (V : Set A) := by
    intro n hn
    haveI : Finite ↥V := inferInstance
    refine Subgroup.mem_normalizer_fintype fun v hv => ?_
    obtain ⟨b, hb, rfl⟩ := hv
    have hnb : n * (b : A) * n⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.1 (hNB hn) b).1 b.2
    exact ⟨⟨_, hnb⟩, hθ n hn b hb hnb, rfl⟩
  haveI := hθc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := θ.range)
  obtain ⟨c, hc⟩ := g.2
  have hBle : B ≤ V ⊔ Subgroup.zpowers (c : A) := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨θ ⟨a, ha⟩, ⟨a, ha⟩, rfl⟩)
    have hk' : θ (c ^ k) = θ ⟨a, ha⟩ := by
      rw [map_zpow, hc]
      exact congrArg Subtype.val hk
    have hker : (⟨a, ha⟩ * (c ^ k)⁻¹ : ↥B) ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hk', mul_inv_cancel]
    have h1 : ((⟨a, ha⟩ * (c ^ k)⁻¹ : ↥B) : A) ∈ V := ⟨_, hker, rfl⟩
    have hmem : ((⟨a, ha⟩ * (c ^ k)⁻¹ : ↥B) : A) * (c : A) ^ k ∈ V ⊔ Subgroup.zpowers (c : A) :=
      Subgroup.mul_mem _ (le_sup_left (b := Subgroup.zpowers (c : A)) h1)
        (le_sup_right (a := V) (Subgroup.zpow_mem_zpowers (c : A) k))
    simpa using hmem
  have hVeq := eq_of_le_sup_zpowers hcyc hN hVB hNV c.2 hBle
  intro b
  have hb : (b : A) ∈ V := by
    rw [hVeq]
    exact b.2
  obtain ⟨b', hb', hbe⟩ := hb
  rwa [show b' = b from Subtype.ext hbe] at hb'

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.OrthMinus

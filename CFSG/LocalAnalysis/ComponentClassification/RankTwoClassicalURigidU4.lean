module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalURigidDx4

public section

namespace CFSG.ComponentClassification.RankTwoClassical.URigid

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

variable {K : Type} [Field K] [CharP K 2] [Finite K] {f : ℕ} (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G] [Finite G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedSU (2 + 2) (2 ^ f) K)}

theorem rigidCore_unitary_four (hf : 2 ≤ f) (hker : θ.ker = center ↥A)
    (hθ : Function.Surjective θ) (hodd : Odd (Nat.card (center ↥A))) {p : G} (hpA : p ∈ A)
    (hp2 : p ^ 2 = 1) {c : K} (hc0 : c ≠ 0) (hc : h.bar c = c)
    {Mp : StatedSU (2 + 2) (2 ^ f) K}
    (hMp : ((Mp : GL (Fin (2 + 2)) K) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) =
      blk 1 (1 + c • vecMulVec (uw₀ (K := K) (le_refl 2)) (uw₀ (le_refl 2))))
    (hθp : θ ⟨p, hpA⟩ = uProj K (2 + 2) f Mp) :
    RigidCore A p (liftSub θ (uBarT K f) ⊔ uLeviW θ) := by
  have hK := h.card_eq_sq
  obtain ⟨s, hs⟩ := exists_add_bar_eq h (map_one h.bar)
  have hR := isHypTransport_uFrame h (le_refl 2) hs
  have hθp' : θ ⟨p, hpA⟩ = psiU h hR ⟨tz h hc, tz_mem_stabE h hc⟩ := by
    rw [hθp, psiU_apply]
    congr 1
    exact Subtype.ext (Units.ext (hMp.trans (tmat_tz h (le_refl 2) hs hc).symm))
  obtain ⟨Θ, hΘs, hΘ⟩ := exists_theta_stabE h hR hf (le_refl 2) hθ hker hodd hpA hp2 hc hc0
    hθp'
  have hXA := perfectCore_inf_le A p
  have hWperf : ⁅uLeviW θ, uLeviW θ⁆ = uLeviW θ :=
    commutator_levLift hker hθ (commutator_uBarW hK hf)
  have hpL : θ ⟨p, hpA⟩ ∈ uBarL K 2 f := by
    rw [hθp]
    obtain ⟨S, hS⟩ := mem_range_uL_of h (g := Mp) hMp
    exact ⟨S, by simp only [MonoidHom.comp_apply]; rw [hS]⟩
  have hWp : uLeviW θ ≤ centralizer ({p} : Set G) :=
    levLift_le_centralizer hker hpA fun u hu => (uBarW_commute_uBarL hu hpL).symm
  have hWX : uLeviW θ ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect (le_inf levLift_le hWp) hWperf
  have hWstd : ((uLeviW θ).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      stdW h :=
    map_theta_eq_stdW h (le_refl 2) hs hXA hΘ hWX (fun w hw => theta_mem_of_mem_levLift hw)
      (fun u hu => exists_mem_levLift hθ (commutator_uBarW hK hf) hu)
  have hstdperf : ⁅stdW (ε := 2) h, stdW (ε := 2) h⁆ = stdW (ε := 2) h := by
    rw [← hWstd, ← Subgroup.map_commutator, perfect_subgroupOf hWX hWperf]
  have hDW := liftSub_uBarT_le_centralizer hker hWperf
  have hDp := liftSub_uBarT_le_centralizer_p hker hodd hpA hp2 hpL
  have hc1 : h.bar 1 = 1 := map_one h.bar
  obtain ⟨t₁, ht₁⟩ : ∃ t : stabE (ε := 2) h, t = ⟨tz h hc1, tz_mem_stabE h hc1⟩ := ⟨_, rfl⟩
  have hNt : ∀ S : StatedSU 2 (2 ^ f) K, (S : GL (Fin 2) K).val = 1 + onesM →
      uProj K (2 + 2) f (uL K 2 f S) = psiU h hR t₁ := by
    intro S hS
    have hSt : uL K 2 f S = hypTransport h hR (tz h hc1) := by
      apply Subtype.ext
      apply Units.ext
      rw [coe_uL, hS]
      refine Eq.trans ?_ (tmat_tz h (le_refl 2) hs hc1).symm
      rw [one_smul, vecMulVec_uw₀_two]
    rw [ht₁]
    exact (congrArg (uProj K (2 + 2) f) hSt).trans rfl
  have htT : t₁ ∈ tvSub h := by
    have hts : smat h t₁ = 1 + Matrix.single hE hF 1 := by
      rw [ht₁, smat, coe_tz, one_smul]
    refine ⟨?_, ?_⟩
    · rw [ht₁]
      exact (mem_ker_zBlockHom h _).mpr (eich_mem_eichSub h (valid_zero h hc1))
    · funext k
      simp [avec, hts, one_apply]
  intro x hXx hYN hYC
  have hWxX : rightConjugate (uLeviW θ) x ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    (Subgroup.map_mono hWX).trans hXx.le
  have hWxA : rightConjugate (uLeviW θ) x ≤ A := hWxX.trans hXA
  have hWxperf : ⁅rightConjugate (uLeviW θ) x, rightConjugate (uLeviW θ) x⁆ =
      rightConjugate (uLeviW θ) x := by
    rw [rightConjugate, ← Subgroup.map_commutator, hWperf]
  obtain ⟨β, hβ⟩ := exists_beta_conjAut h hs hΘ hker hodd hΘs hXx
  have hDx : ∀ a ∈ liftSub θ (uBarT K f),
      x⁻¹ * a * x ∈ rightConjugate (liftSub θ (uBarT K f) ⊔ uLeviW θ) x := fun a ha =>
    ⟨a, mem_sup_left ha, by simp⟩
  obtain ⟨ζ, hζ, hζ1⟩ := exists_norm_one_ne_one hK
  obtain ⟨c₀, -, hc₀⟩ := exists_rootsOfUnity_ne_one hζ hζ1
  obtain ⟨d', hd'⟩ := hθ (uProj K (2 + 2) f (torusU K f c₀))
  have hdD : (d' : G) ∈ liftSub θ (uBarT K f) := mem_liftSub.mpr ⟨d'.2, by
    show θ d' ∈ uBarT K f
    rw [hd']
    exact ⟨c₀, rfl⟩⟩
  obtain ⟨α₀, hα₀, -⟩ := exists_alpha_tconj h hs hΘ hβ d'.2 (hDp hdD) hd' (hYN (hDx _ hdD))
    (hYC (hDx _ hdD)) hθ hker hΘs
  have hδW := tconj_fix_map_stdW h hs hΘ hβ d'.2 (hDp hdD) hd' (hYN (hDx _ hdD))
    (hYC (hDx _ hdD)) hWX hWstd fun w hw => (mem_centralizer_iff.mp (hDW hdD) w hw).symm
  set δ : MulAut (stabE (ε := 2) h) := (β.symm.trans (tconj h (le_refl 2) hs c₀)).trans β
  have hδapp : ∀ g, δ g = β (tconj h (le_refl 2) hs c₀ (β.symm g)) := fun g => rfl
  have hαδ : ∀ g, psiU h hR (δ g) = α₀ (psiU h hR g) := fun g => by
    rw [hδapp]
    exact hα₀ g
  have hδW' : ∀ g ∈ (stdW h).map β.toMonoidHom, δ g = g := fun g hg => by
    rw [hδapp]
    exact hδW g hg
  have hfix := fixfree_conj h hf (le_refl 2) β (tconj h (le_refl 2) hs c₀)
    fun y _ hy => tconj_fixfree h (le_refl 2) hs hc₀ y hy
  have hfix' : ∀ y ∈ (zBlockHom (ε := 2) h).ker, avec h (δ y) = avec h y → avec h y = 0 :=
    fun y hy hy' => hfix y hy (by rwa [hδapp] at hy')
  obtain ⟨g₀, hg₀⟩ := exists_map_stdW_eq_conj_two h hf hstdperf β hR hαδ hδW' hfix'
  have hθW := map_theta_rightConjugate_eq h hs hΘ hWX hWstd
    (fun u hu => exists_mem_levLift hθ (commutator_uBarW hK hf) hu) hXx hβ hg₀
  obtain ⟨y₀, hy₀⟩ : ∃ y, y = psiU h hR g₀ := ⟨_, rfl⟩
  rw [← hy₀] at hθW
  have hy₀t : y₀ * psiU h hR t₁ * y₀⁻¹ = psiU h hR t₁ := by
    have e : g₀ * t₁ * g₀⁻¹ = t₁ :=
      mul_inv_eq_iff_eq_mul.mpr (commute_of_avec_eq_zero h htT.1 htT.2 g₀).symm
    rw [hy₀, ← map_inv, ← map_mul, ← map_mul, e]
  have hDL : ∀ a ∈ liftSub θ (uBarT K f),
      ∀ l ∈ levLift θ ((uBarL K 2 f).map (MulAut.conj y₀).toMonoidHom),
        x⁻¹ * a * x * l = l * (x⁻¹ * a * x) := by
    intro a ha l hl
    obtain ⟨haA, c', hc'⟩ := mem_liftSub.mp ha
    obtain ⟨α, hαψ, γ, hγ, hαγ⟩ := exists_alpha_tconj h hs hΘ hβ haA (hDp ha) (c := c')
      hc'.symm (hYN (hDx a ha)) (hYC (hDx a ha)) hθ hker hΘs
    refine conj_commute_of_levLift h hf hker hθ hodd ha hγ hαγ ?_ ?_ hl
    ·
      rw [← hθW]
      rintro _ ⟨w', hw', rfl⟩
      rw [hαγ]
      congr 1
      apply Subtype.ext
      rw [hγ]
      obtain ⟨w, hw, hww⟩ := Subgroup.mem_subgroupOf.mp hw'
      have hww' : (w' : G) = x⁻¹ * w * x := by simpa using hww.symm
      rw [hww']
      have h1 : a * w = w * a := (mem_centralizer_iff.mp (hDW ha) w hw).symm
      calc x⁻¹ * a * x * (x⁻¹ * w * x) * (x⁻¹ * a * x)⁻¹ = x⁻¹ * (a * w) * a⁻¹ * x := by group
        _ = x⁻¹ * (w * a) * a⁻¹ * x := by rw [h1]
        _ = x⁻¹ * w * x := by group
    ·
      intro S hS
      rw [hNt S hS]
      refine ⟨hy₀t, ?_⟩
      rw [← hαψ]
      congr 1
      have h1 : β.symm t₁ ∈ tvSub h := by
        rw [← map_tvSub h hf (le_refl 2) β.symm]
        exact ⟨t₁, htT, rfl⟩
      rw [tconj_of_mem_tvSub h (le_refl 2) hs c' h1, MulEquiv.apply_symm_apply]
  have hL'C : levLift θ ((uBarL K 2 f).map (MulAut.conj y₀).toMonoidHom) ≤
      A ⊓ centralizer (rightConjugate (liftSub θ (uBarT K f) ⊔ uLeviW θ) x : Set G) := by
    intro l hl
    refine Subgroup.mem_inf.mpr ⟨levLift_le hl, ?_⟩
    have hYl : rightConjugate (liftSub θ (uBarT K f) ⊔ uLeviW θ) x ≤
        centralizer ({l} : Set G) := by
      rw [rightConjugate, Subgroup.map_le_iff_le_comap]
      refine sup_le (fun a ha => ?_) (fun w hw => ?_)
      · change (MulAut.conj x⁻¹) a ∈ centralizer ({l} : Set G)
        rw [mem_centralizer_singleton_iff, MulAut.conj_apply, inv_inv]
        exact hDL a ha l hl
      · change (MulAut.conj x⁻¹) w ∈ centralizer ({l} : Set G)
        rw [mem_centralizer_singleton_iff, MulAut.conj_apply, inv_inv]
        exact conj_commute_of_levLift_W hker hWxA hWxperf hθW hl hw
    rw [mem_centralizer_iff]
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hYl hz)
  have hLbperf : ⁅(uBarL K 2 f).map (MulAut.conj y₀).toMonoidHom,
      (uBarL K 2 f).map (MulAut.conj y₀).toMonoidHom⁆ =
        (uBarL K 2 f).map (MulAut.conj y₀).toMonoidHom := by
    rw [← Subgroup.map_commutator, commutator_uBarL hK hf (le_refl 2)]
  refine noNormalTwo_of_map_theta hker hodd inf_le_left ?_
  refine noNormalTwo_of_conj h hf y₀ ?_ ?_
  · intro u hu
    obtain ⟨l, hl, hlu⟩ := exists_mem_levLift hθ hLbperf hu
    exact ⟨⟨l, levLift_le hl⟩, hL'C hl, hlu⟩
  · rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff, ← hθW]
    rintro _ ⟨w, hw, rfl⟩
    have hwY : (w : G) ∈ rightConjugate (liftSub θ (uBarT K f) ⊔ uLeviW θ) x :=
      Subgroup.map_mono le_sup_right hw
    have h1 := mem_centralizer_iff.mp (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).2 _
      hwY
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext h1)

end CFSG.ComponentClassification.RankTwoClassical.URigid

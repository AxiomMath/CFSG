module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.Q3T7M02
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Transport217

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Uniform

namespace TwinThmE

section Lift

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def E189Concl (Λ : Set (Subgroup Y)) (K : Subgroup Y) (z t : Y) : Prop :=
  (∃ K'' ∈ twinSet Λ K, K'' ≠ K ∧ ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ K ∧
      IsSylow2In R₂ K'' ∧ Commutes R₁ R₂ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₂ ∧ u ≠ 1 ∧
        u * u = 1 ∧ x * u * x⁻¹ = z * t) ∨
  (∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧
      ∃ R₁ R₂ : Subgroup Y, IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧
        Commutes R₁ R₂ ∧ ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w)

variable {Λ : Set (Subgroup Y)}

theorem twin_of_lift (hΩ : HypOmegaGen Λ) (h2 : ∀ J ∈ Λ, IsPGroup 2 J) (hex : ExactSylow Λ)
    {K M M' : Subgroup Y} (hK : K ∈ Λ) (hM : M ∈ liftFam Λ) (hM' : M' ∈ liftFam Λ) (hKM : K ≤ M)
    (hne : M' ≠ M) {z : Y} (hzM : IsUniqueInvolution M z) (hzM' : IsUniqueInvolution M' z) :
    ∃ K₂ ∈ Λ, K₂ ≤ M' ∧ K₂ ∈ twinSet Λ K ∧ K₂ ≠ K ∧ IsSylow2In K M ∧ IsSylow2In K₂ M' := by
  obtain ⟨K₂, hK₂, hK₂M'⟩ := exists_core_of_mem_liftFam hM'
  obtain ⟨u, hu⟩ := (hΩ.omega1 K hK).1
  obtain ⟨u₂, hu₂⟩ := (hΩ.omega1 K₂ hK₂).1
  have hKz : IsUniqueInvolution K z := isUniqueInvolution_of_le_liftFam hu hKM hzM
  have hK₂z : IsUniqueInvolution K₂ z := isUniqueInvolution_of_le_liftFam hu₂ hK₂M' hzM'
  refine ⟨K₂, hK₂, hK₂M', ⟨hK₂, z, hKz, hK₂z⟩, ?_, isSylow2In_of_le_liftFam hΩ hK (h2 K hK) hM hKM,
    isSylow2In_of_le_liftFam hΩ hK₂ (h2 K₂ hK₂) hM' hK₂M'⟩
  intro hKK
  apply hne
  exact liftFam_eq_of_le hΩ hM' hM hK₂ hK₂M' (hKK ▸ hKM)

theorem E189Concl.of_lift (hΩ : HypOmegaGen Λ) (h2 : ∀ J ∈ Λ, IsPGroup 2 J) (hex : ExactSylow Λ)
    {K Kl : Subgroup Y} (hK : K ∈ Λ) (hKl : Kl ∈ liftFam Λ) (hKKl : K ≤ Kl) {z t : Y}
    (hz : IsUniqueInvolution K z) (h : E189Concl (liftFam Λ) Kl z t) : E189Concl Λ K z t := by
  have hzKl : IsUniqueInvolution Kl z := isUniqueInvolution_liftFam_of_le hKl hz hKKl
  rcases h with ⟨K'', hK''tw, hne, R₁, R₂, hR₁, hR₂, hc, u, x, hu, hu1, hu2, hux⟩ |
    ⟨x, M', hM'tw, hne, R₁, R₂, hR₁, hR₂, hc, hall⟩
  · have hK''tw' := hK''tw
    obtain ⟨-, z', hz'Kl, hz'K''⟩ := hK''tw'
    have hz'z : z' = z := hz'Kl.eq hzKl
    subst hz'z
    obtain ⟨K₂, hK₂, hK₂K'', htw, hneK, hSK, hSK₂⟩ := twin_of_lift hΩ h2 hex hK hKl hK''tw.1 hKKl
      hne hzKl hz'K''
    have hR₁K : R₁ = K := hex Kl hKl _ _ hR₁ hSK
    have hR₂K : R₂ = K₂ := hex K'' hK''tw.1 _ _ hR₂ hSK₂
    refine Or.inl ⟨K₂, htw, hneK, K, K₂,
      ⟨le_rfl, h2 K hK, fun V hV _ hle => le_antisymm hV hle⟩,
      ⟨le_rfl, h2 K₂ hK₂, fun V hV _ hle => le_antisymm hV hle⟩, ?_, u, x, ?_, hu1, hu2, hux⟩
    · rw [← hR₁K, ← hR₂K]; exact hc
    · rw [← hR₁K, ← hR₂K]; exact hu
  · have hM'tw' := hM'tw
    obtain ⟨-, z', hz'x, hz'M'⟩ := hM'tw'
    have hxK : conjSub x K ∈ Λ := hΩ.conjInvariant x K hK
    have hxKl : conjSub x Kl ∈ liftFam Λ := conjInvariant_liftFam hΩ.conjInvariant x Kl hKl
    have hxKKl : conjSub x K ≤ conjSub x Kl := conjSub_mono hKKl
    have hzx : IsUniqueInvolution (conjSub x Kl) z' := hz'x
    obtain ⟨K₂, hK₂, hK₂M', htw, hneK, hSK, hSK₂⟩ := twin_of_lift hΩ h2 hex hxK hxKl hM'tw.1 hxKKl
      hne hzx hz'M'
    have hR₁K : R₁ = conjSub x K := hex _ hxKl _ _ hR₁ hSK
    have hR₂K : R₂ = K₂ := hex M' hM'tw.1 _ _ hR₂ hSK₂
    refine Or.inr ⟨x, K₂, htw, hneK, conjSub x K, K₂,
      ⟨le_rfl, h2 _ hxK, fun V hV _ hle => le_antisymm hV hle⟩,
      ⟨le_rfl, h2 K₂ hK₂, fun V hV _ hle => le_antisymm hV hle⟩, ?_, ?_⟩
    · rw [← hR₁K, ← hR₂K]; exact hc
    · rw [← hR₁K, ← hR₂K]; exact hall

end Lift

section NoExit

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem e189_bar_noExit {n : ℕ} (hE : Q3T8.Asc77.E189Sect) (hcit : CIT3Below n)
    (hih : Uniform.IH8T 3 1 n)
    (hP : TL4.TightBelowRPlus 3 n) (hlt : Nat.card Y < n) (hS : TwinDisc.Q8Section Y Λ)
    (hno : TwinDisc.NoExit Y Λ) {K J : Subgroup Y} (hK : K ∈ Λ) (hJ : J ∈ Λ) {z t : Y}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt : z * t = t * z)
    (hne : conjSub t K ≠ K) : E189Concl Λ K z t := by
  obtain ⟨h2, hl, hex⟩ := TwinDisc.lifts_of_noExit hP hlt hS hno
  have hΩ : HypOmegaGen Λ := hS.hyp
  have hΛl : Q3T8.Generic.CITBelowU n :=
    (Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit
  have hHM : Q3T7M.HM (liftFam Λ) := hypOmegaModU_liftFam hΩ.conjInvariant
  have hgen : (⨆ L ∈ liftFam Λ, L) = ⊤ := by
    apply top_le_iff.mp
    rw [← hS.gen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨M, u, hM⟩ := hl L hL
    exact hM.le_sat.trans (le_iSup₂ (f := fun (L : Subgroup Y) (_ : L ∈ liftFam Λ) => L) _
      (satU_mem_liftFam hL hM))
  have hAΛ := ExactSylow.aEmpty_liftFam hΩ h2 hl hex hS.aEmpty
  obtain ⟨LK, uK, hLK⟩ := hl K hK
  obtain ⟨LJ, uJ, hLJ⟩ := hl J hJ
  have hKl := satU_mem_liftFam hK hLK
  have hJl := satU_mem_liftFam hJ hLJ
  have hzKl : IsUniqueInvolution (satU (.sl2 3 1) LK uK) z :=
    isUniqueInvolution_liftFam_of_le hKl hz hLK.le_sat
  have htJl : IsUniqueInvolution (satU (.sl2 3 1) LJ uJ) t :=
    isUniqueInvolution_liftFam_of_le hJl ht hLJ.le_sat
  have hnel : conjSub t (satU (.sl2 3 1) LK uK) ≠ satU (.sl2 3 1) LK uK := by
    intro h
    apply hne
    have hn : t ∈ Subgroup.normalizer ((satU (.sl2 3 1) LK uK : Subgroup Y) : Set Y) :=
      mem_normalizer_of_conjSub_eq h
    rw [ExactSylow.normalizer_eq hΩ h2 hex hKl hK hLK.le_sat] at hn
    exact conjSub_eq_of_mem_normalizer hn
  have hconcl := hE n hΛl hih Y hlt (liftFam Λ) hHM hgen hAΛ _ hKl _ hJl z t hzKl htJl hzt hnel
  exact E189Concl.of_lift hΩ h2 hex hK hKl hLK.le_sat hz hconcl
end NoExit

end TwinThmE

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

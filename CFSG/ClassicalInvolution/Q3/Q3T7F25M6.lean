module

public import CFSG.ClassicalInvolution.Q3.Q3T7F25M4
public import CFSG.ClassicalInvolution.Asc77.AscT7TZStar
public import CFSG.ClassicalInvolution.Asc77.AscT7TFix

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false
namespace CFSG.ClassicalInvolution.T7F25

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

@[expose] def C25_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ A : Subgroup G, IsElemAbelian2 A 2 → z ∈ A →
      (∀ a ∈ A, a * t = t * a) → ∃ a ∈ A, a ≠ 1 ∧ z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))

@[expose] def C25_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ A : Subgroup G, z ∈ A → A ≤ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), conjSub s A = A) →
      (∀ a ∈ A, a ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({a} : Set G))) → A = Subgroup.zpowers z
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7G2
open CFSG.ClassicalInvolution.Asc77.T7G2
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W :
    Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}
section Swap
variable (hyp : Asc77.Hyp25 Ω K K' W S R R' z t u₁ u₂)
include hyp
theorem not_normalizes_of_nonfused {t'' g : G} (hg : g * z * g⁻¹ = t'') (hne : z ≠ t'')
    (hnf : ¬ ∃ y : G, y * z * y⁻¹ = t'' * z) : conjSub z (conjSub g K) ≠ conjSub g K := by
  intro hN
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hW₀ : W ∈ WSet Ω := hyp.hW
  have hE4 := hyp.hE4
  have hJt : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have htJ : IsUniqueInvolution (conjSub g K) t'' := by
    have := hz.conj g
    rwa [hg] at this
  have hz2 : z * z = 1 := hz.sq
  have hzN : z ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) :=
    mem_normalizer_iff_conjSub_eq.mpr hN
  obtain ⟨Rt, hRtsyl, hRtinv⟩ := T3.exists_sylow_normalized (T7ER.isPGroup_zpowers_of_sq hz2)
    (Subgroup.zpowers_le.mpr hzN)
  have hRtmem : Rt ∈ RSet Ω := mem_RSet_of_isSylow2In hJt hRtsyl
  have hRtq : IsQuatSub Rt := hΩ.isQuatSub_of_mem_RSet hRtmem
  have htRt : t'' ∈ Rt := T7C.mem_of_isSylow2In hΩ hJt hRtsyl htJ
  have hzRt : IsUniqueInvolution Rt t'' :=
    ⟨htRt, htJ.ne_one, htJ.sq, fun y hy hy2 => htJ.unique y (hRtsyl.1 hy) hy2⟩
  have hsRt : conjSub z Rt = Rt := hRtinv _ (Subgroup.mem_zpowers _)
  have hbR : ∀ r ∈ Rt, z * r * z⁻¹ ∈ Rt := fun r hr => by
    have := conj_mem_conjSub (n := z) hr
    rwa [hsRt] at this
  have hfixt : ∀ r ∈ Rt, orderOf r = 4 → z * r * z⁻¹ ≠ r := by
    intro r hr hr4 h
    have := T7ER.not_commute_of_conj hs hW₀ hE4 hJt htJ (y := 1) (by simpa using hne)
      (hRtsyl.1 hr) hr4
    apply this
    simp only [one_mul, inv_one, mul_one]
    have h1 := congrArg (fun w => w * z) h
    simpa [mul_assoc] using h1
  obtain ⟨ρ, hρ, hρs⟩ := T7ER.exists_conj_eq_mul_inv hRtq hzRt hz2 hbR hfixt
  apply hnf
  refine ⟨ρ⁻¹, ?_⟩
  calc ρ⁻¹ * z * ρ⁻¹⁻¹ = ρ⁻¹ * z * ρ := by rw [inv_inv]
    _ = ρ⁻¹ * (z * ρ * z⁻¹) * z := by group
    _ = ρ⁻¹ * (ρ * t'') * z := by rw [hρs]
    _ = t'' * z := by group
end Swap
end T7G2
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G]
theorem c25_3_proved : C25_3 := by
  intro G _ _ Ω K K' W S R R' z t u₁ u₂ hyp A hA hzA hAt
  by_contra hcon
  push Not at hcon
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  obtain ⟨htS, htz, g, hg⟩ := hyp.ht
  have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hK
  have htJ : IsUniqueInvolution (conjSub g K) t := by
    have := hz.conj g
    rwa [hg] at this
  have hA2 : IsPGroup 2 A := IsPGroup.of_card (n := 2) hA.1
  have hAC : A ≤ Subgroup.centralizer ({t} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAt a ha)
  obtain ⟨V, hV, hAV⟩ := IsSylow2In.exists_ge hA2 hAC
  have hΓ : gamma1 A (V ⊓ ⨆ L ∈ twinSet Ω (conjSub g K), L) ≤
      Subgroup.centralizer ({z} : Set G) := by
    unfold gamma1
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    intro y hy
    obtain ⟨⟨hyV, -⟩, hyw⟩ := (Subgroup.mem_inf.mp hy) |>.imp Subgroup.mem_inf.mp id
    have hzV : z ∈ V := hAV hzA
    have hTV : Subgroup.closure ({y, z} : Set G) ≤ V := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hyV
      · exact hzV
    have hT2 : IsPGroup 2 (Subgroup.closure ({y, z} : Set G)) := hV.2.1.to_le hTV
    have hTw : Subgroup.closure ({y, z} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hyw
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_sq_eq_one hA.2 hzA hw)
    have hzT : z ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hyT : y ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    exact le_centralizer_of_mem_zStarOf (hcon w hw hw1) hzT hTw hT2 hyT
  obtain ⟨x, hxJ, hx4, hxz⟩ := hst.nine3 (conjSub g K) hJ t htJ V hV A hAV
    hA z hzA hz.ne_one hΓ
  refine T7ER.not_commute_of_conj hs hyp.hW hyp.hE4 hJ htJ (y := 1) ?_ hxJ hx4 ?_
  · simpa using htz.symm
  · simpa using hxz.symm
end T7T
end Asc77
end
section
set_option linter.unusedSectionVars false
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7T
open CFSG.ClassicalInvolution.Asc77.T7T
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}

theorem twin_sq (hs : Hyp23Setting Ω K K' z) {x : G} (hx : x * z * x⁻¹ = z) :
    conjSub (x * x) K = K := by
  have hΩ : HypOmegaMod Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hKx : conjSub x K = K ∨ conjSub x K = K' := by
    have hmem : conjSub x K ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant x K hK, z, hz, by simpa [hx] using hz.conj x⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  have hK'x : conjSub x K' = K ∨ conjSub x K' = K' := by
    have hmem : conjSub x K' ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant x K' hs.hK'.1, z, hz, by simpa [hx] using hz'.conj x⟩
    rw [hs.twinSet_eq] at hmem
    exact hmem
  rw [conjSub_mul]
  rcases hKx with h | h
  · rw [h, h]
  · rw [h]
    rcases hK'x with h' | h'
    · exact h'
    · exfalso
      exact hs.hne (conjSub_injective x (h.trans h'.symm)).symm
theorem c25_5_proved : C25_5 := by
  intro G _ _ Ω K K' W S R R' z t u₁ u₂ hyp A hzA hAS hAnorm hZ
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hz : IsUniqueInvolution K z := hs.hz
  have hz2 : z * z = 1 := hz.sq
  have hz1 : z ≠ 1 := hz.ne_one
  obtain ⟨t', ht'S, ht'2, ⟨g, hg⟩, ht'R, hnf⟩ := T7G2.exists_swap_nonfused hyp
  have hRS : R ≤ (S : Subgroup G) := hyp.hR.2.2
  have hRne : R ≠ R' := T7ER.ne_of_hyp25 hyp
  have hzt' : z ≠ t' := by
    intro h
    apply hRne
    have h1 : conjSub t' R = R := by
      rw [← h]
      exact T7F2.conjSub_eq_of_centralizes fun r hr => hyp.hzS r (hRS hr)
    rw [← ht'R, h1]
  have hyp' : Hyp25 Ω K K' W S R R' z t' u₁ u₂ := { hyp with ht := ⟨ht'S, hzt'.symm, g, hg⟩ }
  have hnosq : ∀ b ∈ A ⊓ Subgroup.centralizer ({t'} : Set G), b * b ≠ z := by
    intro b hb hbb
    have hbt : b * t' = t' * b := Subgroup.mem_centralizer_singleton_iff.mp hb.2
    have hx : (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = z := by
      calc (g⁻¹ * b * g) * z * (g⁻¹ * b * g)⁻¹ = g⁻¹ * b * (g * z * g⁻¹) * b⁻¹ * g := by group
        _ = g⁻¹ * b * t' * b⁻¹ * g := by rw [hg]
        _ = g⁻¹ * (b * t' * b⁻¹) * g := by group
        _ = g⁻¹ * t' * g := by rw [hbt]; group
        _ = z := by rw [← hg]; group
    have h1 := twin_sq hs hx
    have h2 : conjSub (b * b) (conjSub g K) = conjSub g K := by
      calc conjSub (b * b) (conjSub g K) = conjSub ((b * b) * g) K := (conjSub_mul (b * b) g K).symm
        _ = conjSub (g * ((g⁻¹ * b * g) * (g⁻¹ * b * g))) K := by congr 1; group
        _ = conjSub g (conjSub ((g⁻¹ * b * g) * (g⁻¹ * b * g)) K) := by rw [conjSub_mul]
        _ = conjSub g K := by rw [h1]
    rw [hbb] at h2
    exact T7G2.not_normalizes_of_nonfused hyp hg hzt' hnf h2
  have hinv : ∀ c ∈ A ⊓ Subgroup.centralizer ({t'} : Set G), c * c = 1 → c ≠ 1 → c ≠ z → False := by
    intro c hc hc2 hc1 hcz
    have hcA : c ∈ A := hc.1
    have hcz' : c * z = z * c := hyp.hzS c (hAS hcA)
    have h4 := T7A.isElemAbelian2_closure_pair hc2 hz2 hc1 hz1 hcz hcz'
    have hle : Subgroup.closure ({c, z} : Set G) ≤ A := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hcA
      · exact hzA
    have hlet : Subgroup.closure ({c, z} : Set G) ≤ Subgroup.centralizer ({t'} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hc.2
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS t' ht'S).symm
    obtain ⟨a, hacl, ha1, haz⟩ := c25_3_proved G Ω K K' W S R R' z t' u₁ u₂
      hyp' _ h4 (Subgroup.subset_closure (by simp)) fun a ha =>
        Subgroup.mem_centralizer_singleton_iff.mp (hlet ha)
    exact haz (hZ a (hle hacl) ha1)
  have hB2 : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer ({t'} : Set G)) :=
    S.isPGroup'.to_le (inf_le_left.trans hAS)
  have hBz := eq_one_or_eq_of_isPGroup hB2 hnosq hinv
  by_contra hne
  have hbig : ∃ a ∈ A, a ≠ 1 ∧ a ≠ z := by
    by_contra hall
    push Not at hall
    apply hne
    apply le_antisymm
    · intro a ha
      by_cases h1 : a = 1
      · rw [h1]; exact one_mem _
      · rw [hall a ha h1]; exact Subgroup.mem_zpowers z
    · exact Subgroup.zpowers_le.mpr hzA
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht'2
  have htA : ∀ a ∈ A, t' * a * t'⁻¹ ∈ A := fun a ha => by
    have := conj_mem_conjSub (n := t') ha
    rwa [hAnorm t' ht'S] at this
  have htz : t' * z * t'⁻¹ = z := by
    rw [hyp.hzS t' ht'S]; group
  have hfix : ∀ a ∈ A, t' * a * t'⁻¹ = a → a = 1 ∨ a = z := fun a ha h => by
    refine hBz a ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : t' * a = a * t' := by
      calc t' * a = (t' * a * t'⁻¹) * t' := by group
        _ = a * t' := by rw [h]
    exact h1.symm
  obtain ⟨a, haA, ha1, haz, hcon⟩ := exists_conj_eq_mul_of_isPGroup (S.isPGroup'.to_le hAS) hzA
    hz2 hz1 (fun a ha => (hyp.hzS a (hAS ha)).symm) ht'2 htA htz hfix hbig
  apply hnf
  refine ⟨a⁻¹ * g, ?_⟩
  have h1 : t' * a = a * z * t' := by
    calc t' * a = (t' * a * t'⁻¹) * t' := by group
      _ = a * z * t' := by rw [hcon]
  calc a⁻¹ * g * z * (a⁻¹ * g)⁻¹ = a⁻¹ * (g * z * g⁻¹) * a := by group
    _ = a⁻¹ * t' * a := by rw [hg]
    _ = a⁻¹ * (t' * a) := by group
    _ = a⁻¹ * (a * z * t') := by rw [h1]
    _ = z * t' := by group
    _ = t' * z := (hyp.hzS t' ht'S).symm
end T7T
end Asc77
end
end CFSG.ClassicalInvolution.T7F25

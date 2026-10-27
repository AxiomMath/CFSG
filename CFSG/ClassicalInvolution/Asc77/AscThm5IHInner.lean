module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHSplit
public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha
public import CFSG.ClassicalInvolution.Balance.Q27D4Parts
public import CFSG.Assembly.BalancedOddCoreCompletion
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHRed

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Q27
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Abstract

variable {S Y : Type} [Group S] [Group Y] [Finite Y]

theorem thm5IH_odd_core_centralizes {ε : S →* Y} (hε : Function.Injective ε)
    (hnorm : ε.range.Normal) (hO : InvolutionOddCoreTrivial S) {x : S} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) {d : Y} (hd : d ∈ involutionOddCore (ε x)) {y : S}
    (hy : y ∈ Subgroup.centralizer ({x} : Set S)) : d * ε y = ε y * d := by
  classical
  set O : Subgroup Y := involutionOddCore (ε x) with hOdef
  have hcentS : ∀ s ∈ Subgroup.centralizer ({x} : Set S),
      ε s ∈ Subgroup.centralizer ({ε x} : Set Y) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff] at hs ⊢
    rw [← map_mul, ← map_mul, hs]
  set N : Subgroup S := O.comap ε with hN
  have hNle : N ≤ Subgroup.centralizer ({x} : Set S) := by
    intro n hn
    have h1 : ε n ∈ Subgroup.centralizer ({ε x} : Set Y) :=
      CFSG.ClassicalInvolution.Balance.involutionOddCore_le_centralizer (ε x) hn
    rw [Subgroup.mem_centralizer_singleton_iff] at h1 ⊢
    apply hε
    rw [map_mul, map_mul]
    exact h1
  have hNconj : ∀ c ∈ Subgroup.centralizer ({x} : Set S), ∀ n ∈ N, c * n * c⁻¹ ∈ N := by
    intro c hc n hn
    show ε (c * n * c⁻¹) ∈ O
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_involutionOddCore (hcentS c hc) hn
  have hNodd : Odd (Nat.card N) := by
    have h1 : Nat.card (N.map ε) = Nat.card N := Subgroup.card_map_of_injective hε
    have h2 : N.map ε ≤ O := Subgroup.map_comap_le ε O
    rw [← h1]
    exact (CFSG.Assembly.Dichotomy.odd_card_involutionOddCore (ε x)).of_dvd_nat
      (Subgroup.card_dvd_of_le h2)
  have hNbot : N = ⊥ := hO x hx2 hx1 N hNle hNconj hNodd
  set w : Y := d * ε y * d⁻¹ * (ε y)⁻¹ with hw
  have hwO : w ∈ O := by
    have h1 : ε y * d⁻¹ * (ε y)⁻¹ ∈ O :=
      conj_mem_involutionOddCore (hcentS y hy) (O.inv_mem hd)
    have e : w = d * (ε y * d⁻¹ * (ε y)⁻¹) := by rw [hw]; group
    rw [e]
    exact O.mul_mem hd h1
  have hwR : w ∈ ε.range := by
    have h1 : d * ε y * d⁻¹ ∈ ε.range := hnorm.conj_mem (ε y) ⟨y, rfl⟩ d
    exact ε.range.mul_mem h1 (ε.range.inv_mem ⟨y, rfl⟩)
  obtain ⟨s, hs⟩ := hwR
  have hsN : s ∈ N := by
    show ε s ∈ O
    rw [hs]
    exact hwO
  rw [hNbot, Subgroup.mem_bot] at hsN
  have hw1 : w = 1 := by rw [← hs, hsN, map_one]
  have h2 : d * ε y * d⁻¹ = ε y := by
    have := congrArg (fun u => u * ε y) hw1
    simpa [hw, mul_assoc] using this
  calc d * ε y = d * ε y * d⁻¹ * d := by group
    _ = ε y * d := by rw [h2]

theorem thm5IH_alphaOf_eq_bot_of_inner {ε : S →* Y} (hε : Function.Injective ε)
    (hnorm : ε.range.Normal) (hcent : ∀ y : Y, (∀ s : S, y * ε s = ε s * y) → y = 1)
    (hO : InvolutionOddCoreTrivial S) (hG : InvolutionCentralizersGenerate S)
    {F : Subgroup Y} (hF4 : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1) (hFr : F ≤ ε.range) :
    alphaOf F = ⊥ := by
  classical
  rw [alphaOf_eq_bot_iff]
  have hFcomm := thm5IH_comm_of_sq hF2
  have hpre2 : ∀ x : S, ε x ∈ F → x * x = 1 := fun x hx => hε (by
    rw [map_mul, map_one]
    exact hF2 _ hx)
  refine ⟨fun a ha ha1 => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := hFr ha
    have hx2 : x * x = 1 := hpre2 x ha
    have hx1 : x ≠ 1 := fun h => ha1 (by rw [h, map_one])
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro d hd b hb
    obtain ⟨y, rfl⟩ := hFr hb
    have hy : y ∈ Subgroup.centralizer ({x} : Set S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hε
      rw [map_mul, map_mul]
      exact (hFcomm _ ha _ hb).symm
    have h := thm5IH_odd_core_centralizes hε hnorm hO hx2 hx1 hd hy
    rw [Subgroup.mem_bot, commutatorElement_def, h]
    group
  · change deltaCore F = ⊥
    obtain ⟨f₁, hf₁F, hf₁1, -⟩ := thm5IH_exists_ne hF4 1 1
    obtain ⟨f₂, hf₂F, hf₂1, hf₂₁⟩ := thm5IH_exists_ne hF4 1 f₁
    obtain ⟨x₁, rfl⟩ := hFr hf₁F
    obtain ⟨x₂, rfl⟩ := hFr hf₂F
    have hx₁2 : x₁ * x₁ = 1 := hpre2 x₁ hf₁F
    have hx₂2 : x₂ * x₂ = 1 := hpre2 x₂ hf₂F
    have hx₁1 : x₁ ≠ 1 := fun h => hf₁1 (by rw [h, map_one])
    have hx₂1 : x₂ ≠ 1 := fun h => hf₂1 (by rw [h, map_one])
    have hx₁₂ : x₁ ≠ x₂ := fun h => hf₂₁ (by rw [h])
    have hcomm : x₁ * x₂ = x₂ * x₁ := by
      apply hε
      rw [map_mul, map_mul]
      exact hFcomm _ hf₁F _ hf₂F
    have hf₃F : ε x₁ * ε x₂ ∈ F := F.mul_mem hf₁F hf₂F
    have hf₃1 : ε x₁ * ε x₂ ≠ 1 := by
      intro h
      apply hf₂₁
      rw [eq_inv_of_mul_eq_one_right h]
      exact inv_eq_of_mul_eq_one_right (hF2 _ hf₁F)
    have hx₃F : ε (x₁ * x₂) ∈ F := by rw [map_mul]; exact hf₃F
    have hx₃2 : x₁ * x₂ * (x₁ * x₂) = 1 := hpre2 _ hx₃F
    have hx₃1 : x₁ * x₂ ≠ 1 := fun h => hf₃1 (by rw [← map_mul, h, map_one])
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_bot]
    set T : Subgroup S := (Subgroup.centralizer ({d} : Set Y)).comap ε with hT
    have hTc : ∀ x : S, x * x = 1 → x ≠ 1 → d ∈ involutionOddCore (ε x) →
        Subgroup.centralizer ({x} : Set S) ≤ T := by
      intro x hx2 hx1 hdx y hy
      show ε y ∈ Subgroup.centralizer ({d} : Set Y)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (thm5IH_odd_core_centralizes hε hnorm hO hx2 hx1 hdx hy).symm
    have hd₁ : d ∈ involutionOddCore (ε x₁) := mem_deltaCore_iff.mp hd _ hf₁F hf₁1
    have hd₂ : d ∈ involutionOddCore (ε x₂) := mem_deltaCore_iff.mp hd _ hf₂F hf₂1
    have hd₃ : d ∈ involutionOddCore (ε (x₁ * x₂)) := by
      rw [map_mul]
      exact mem_deltaCore_iff.mp hd _ hf₃F hf₃1
    have hle : Subgroup.centralizer ({x₁} : Set S) ⊔ Subgroup.centralizer ({x₂} : Set S) ⊔
        Subgroup.centralizer ({x₁ * x₂} : Set S) ≤ T :=
      sup_le (sup_le (hTc x₁ hx₁2 hx₁1 hd₁) (hTc x₂ hx₂2 hx₂1 hd₂))
        (hTc _ hx₃2 hx₃1 hd₃)
    rw [hG x₁ x₂ hx₁2 hx₂2 hx₁1 hx₂1 hx₁₂ hcomm] at hle
    refine hcent d fun s => ?_
    have hs : s ∈ T := hle (Subgroup.mem_top s)
    have h1 : ε s ∈ Subgroup.centralizer ({d} : Set Y) := hs
    rw [Subgroup.mem_centralizer_singleton_iff] at h1
    exact h1.symm

end Abstract


section Induced

variable {H : Type} [Group H]

theorem thm5IH_inducedImage_eq_range {L A : Subgroup H}
    (hAN : A ≤ Subgroup.normalizer (L : Set H)) :
    inducedImage L A = ((toInducedAutOn L).comp (Subgroup.inclusion hAN)).range := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨⟨b, hAN b.2⟩, b.2, rfl⟩

theorem thm5IH_card_inducedImage {L A : Subgroup H} (hAN : A ≤ Subgroup.normalizer (L : Set H))
    (hA4 : Nat.card A = 4) (hfaith : ∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ L, a * x = x * a) :
    Nat.card (inducedImage L A) = 4 := by
  set πA : ↥A →* ↥(inducedAutOn L) := (toInducedAutOn L).comp (Subgroup.inclusion hAN) with hπA
  have hinj : Function.Injective πA := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hc := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (hAN b.2) hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    exact hfaith b b.2 (fun h => hb1 (Subtype.ext h)) fun x hx => hc x hx
  rw [thm5IH_inducedImage_eq_range hAN, ← hA4]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem thm5IH_alphaOf_inducedImage_eq_bot {S : Type} [Group S] [Finite S] [Group.IsPerfect S]
    [Finite H] (ψ : S →* H) (hker : ψ.ker ≤ Subgroup.center S) (hZ : Subgroup.center S = ⊥)
    (hO : InvolutionOddCoreTrivial S) (hG : InvolutionCentralizersGenerate S) {A : Subgroup H}
    (hA4 : Nat.card A = 4) (hA2 : ∀ a ∈ A, a * a = 1) (hAL : A ≤ ψ.range)
    (hfaith : ∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ ψ.range, a * x = x * a) :
    alphaOf (inducedImage ψ.range A) = ⊥ := by
  obtain ⟨hcen, hnorm, hcent⟩ := FrameVertex.innerHom_spec ψ hker
  have hε : Function.Injective (FrameVertex.innerHom ψ) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    have h1 := hcen g (MonoidHom.mem_ker.mp hg)
    rw [hZ] at h1
    exact h1
  have hAN : A ≤ Subgroup.normalizer (ψ.range : Set H) := fun a ha =>
    Subgroup.le_normalizer (hAL ha)
  refine thm5IH_alphaOf_eq_bot_of_inner hε hnorm
    (fun y hy => hcent y fun _ hx => by obtain ⟨s, rfl⟩ := hx; exact hy s) hO hG
    (thm5IH_card_inducedImage hAN hA4 hfaith) ?_ ?_
  · intro f hf
    rw [thm5IH_inducedImage_eq_range hAN] at hf
    obtain ⟨b, rfl⟩ := hf
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hA2 b b.2)
    rw [this, map_one]
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨s, hs⟩ := hAL (Subgroup.mem_subgroupOf.mp hm)
    refine ⟨s, ?_⟩
    rw [FrameVertex.innerHom_apply]
    congr 1
    exact Subtype.ext hs

end Induced

section Model

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_of_model {t : StatedLieTag} {k e : ℕ} (P : Prop → Prop)
    (hfacts : p ≠ 2 → 5 ≤ p ^ f → IsFundTag t → StatedLieAdmissible t k p e →
      (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
        Group.IsPerfect (modelUniv t k p e Fact.out).K ∧
        Subgroup.center (modelUniv t k p e Fact.out).K = ⊥ ∧
        InvolutionOddCoreTrivial (modelUniv t k p e Fact.out).K ∧
        InvolutionCentralizersGenerate (modelUniv t k p e Fact.out).K) :
    T5BaseAt p f t k e P := by
  intro hp2 hq hfund hadm hef H _ _ ψ hker R _ R' _ _ _ _ _ z _ _ A hA hAKJ _ hfaith
  obtain ⟨hperf, hZ, hO, hG⟩ := hfacts hp2 hq hfund hadm hef
  have := hperf
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have : Finite (modelUniv t k p e Fact.out).K := Finite.of_injective ψ hψinj
  have hAL : A ≤ ψ.range :=
    hAKJ.trans (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R'))
  exact thm5IH_alphaOf_inducedImage_eq_bot ψ hker hZ hO hG (by simpa using hA.1) hA.2 hAL hfaith

end Model

end CFSG.ClassicalInvolution.Asc77

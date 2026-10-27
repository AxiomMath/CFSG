module

public import CFSG.ClassicalInvolution.Asc77.AscC5O9H
public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal
public import CFSG.ClassicalInvolution.Asc77.AscC5O6
public import CFSG.ClassicalInvolution.Asc77.AscC5O7

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Swaps

variable {τ σ : G}

theorem false_of_comm [IsSimpleGroup G] (hM : ModelFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ)
    (hT1 : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈
      hBig D.ctx.hyp.std.setting.stand.hyp.conjInvariant z a τ σ D.τC D.σC) : False := by
  have C := D.ctx
  have haS : a ∈ (S : Subgroup G) := C.haA.1
  have hne := CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal S hT1 haS
    (D.a_not_mem_hBig hM) (by rw [pow_two]; exact C.ha2) (fun g hg => by
      have hgS : g⁻¹ * a * g ∈ (S : Subgroup G) :=
        hg a ⟨haS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      exact D.extremal_mem_hBig hM (C.hyp.hzS _ hgS))
  apply hne
  obtain ⟨t', hT⟩ := T7T.exists_hyp25T C.hyp
  obtain ⟨x, -, y, -, hxy⟩ := hT.hqR.exists_not_commute
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with
    h | h
  · exact (hxy ((isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)) x y)).elim
  · exact h

end Swaps

namespace Ctx

theorem exists_conj_mem_S [IsSimpleGroup G] (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {w : G}
    (hwa : w * a = a * w) (hwz : w * z = z * w) (hw2 : IsPGroup 2 (Subgroup.zpowers w)) :
    ∃ g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :
        Subgroup G) : Set G), g⁻¹ * w * g ∈ (S : Subgroup G) := by
  set A₀ := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hA₀
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (A₀ : Set G) := fun s hs =>
    mem_normalizer_of_conjSub_eq (T7T.conjSub_centralizer_of_hyp C.hyp hs)
  have hSsyl : IsSylow2In (S : Subgroup G) (Subgroup.normalizer (A₀ : Set G)) :=
    ⟨hSN, S.isPGroup', fun V' _ hV' hle => S.is_maximal' hV' hle⟩
  have hfixA : ∀ h ∈ A₀, w * h * w⁻¹ = h := by
    intro h hh
    rcases C.hA0 h hh with e | e | e | e <;> rw [e]
    · group
    · rw [hwa]; group
    · rw [hwz]; group
    · calc w * (a * z) * w⁻¹ = (w * a) * z * w⁻¹ := by group
        _ = a * (w * z) * w⁻¹ := by rw [hwa]; group
        _ = a * z := by rw [hwz]; group
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (A₀ : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_,
      fun hh => ?_⟩)
    · rw [hfixA h hh]; exact hh
    · have e1 := hfixA _ hh
      have e2 : h = w * h * w⁻¹ := by
        calc h = w⁻¹ * (w * h * w⁻¹) * w := by group
          _ = w⁻¹ * (w * (w * h * w⁻¹) * w⁻¹) * w := by rw [e1]
          _ = w * h * w⁻¹ := by group
      rw [e2]; exact hh
  obtain ⟨V, hV, hVle⟩ := IsSylow2In.exists_ge hw2 hwN
  obtain ⟨g, hg, hVeq⟩ := IsSylow2Of.exists_conj (show IsSylow2Of _ _ from hSsyl)
    (show IsSylow2Of _ _ from hV)
  refine ⟨g, hg, ?_⟩
  have h := hVle (Subgroup.mem_zpowers w)
  rw [hVeq] at h
  exact mem_conjSubgroup_iff.mp h

theorem mk_swaps [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) {τ σ hτ hσ : G}
    (hhτX : hτ ∈ exactLayer Ω (a * z)) (hhτ : hτ * z * hτ⁻¹ = τ) (hτz : τ * z = z * τ)
    (hτK : conjSub τ K = K') (hτn : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ τ)
    (haτ : ¬ ∃ g : G, g * z * g⁻¹ = a * τ) (hhσX : hσ ∈ exactLayer Ω a)
    (hhσ : hσ * z * hσ⁻¹ = σ) (hσz : σ * z = z * σ)
    (hσn : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ σ)
    (haσ : ¬ ∃ g : G, g * z * g⁻¹ = (a * z) * σ) :
    Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ := by
  obtain ⟨hzY, -, -, -, -, -⟩ := C.om5
  obtain ⟨hzY', -, -, -, -, -⟩ := C.swap.om5
  have hτX : τ ∈ exactLayer Ω (a * z) := by
    rw [← hhτ]; exact mul_mem (mul_mem hhτX hzY') (inv_mem hhτX)
  have hσX : σ ∈ exactLayer Ω a := by
    rw [← hhσ]; exact mul_mem (mul_mem hhσX hzY) (inv_mem hhσX)
  have hτaz : τ * (a * z) = (a * z) * τ :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω (a * z) hτX)
  have hτa : τ * a = a * τ := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right C.hz2
    calc τ * a = τ * (a * z) * z⁻¹ := by group
      _ = (a * z) * τ * z⁻¹ := by rw [hτaz]
      _ = (a * z) * (τ * z) := by rw [hzi]; group
      _ = (a * z) * (z * τ) := by rw [hτz]
      _ = a * τ := by rw [← mul_assoc, C.mul_z_mul_z]
  have hσa : σ * a = a * σ :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω a hσX)
  exact ⟨C, ⟨hτ, hhτ⟩, hτa, hτz, hτn, haτ, hτX, hτK, ⟨hσ, hhσ⟩, hσa, hσz, hσn, haσ, hσX,
    C.swap.interchange hM hhτX hhτ hτz hτK⟩

theorem exists_swaps [IsSimpleGroup G] (hM : ModelFacts p f)
    (C : Ctx p f Ω K K' W S R R' z t u₁ u₂ a) :
    (∃ τ σ : G, Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ ∧ τ ∈ (S : Subgroup G)) ∨
      ∃ τ σ : G, Swaps p f Ω K K' W S R R' z t u₁ u₂ (a * z) τ σ ∧ τ ∈ (S : Subgroup G) := by
  classical
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hz2 := C.hz2
  have hazz := C.mul_z_mul_z
  obtain ⟨t₀, ⟨h₀, hh₀X, hh₀⟩, ht₀z, -, ht₀K, -, ht₀n⟩ := C.swap.refSwap hM
  obtain ⟨s₀, ⟨k₀, hk₀X, hk₀⟩, hs₀z, -, hs₀K, -, hs₀n⟩ := C.refSwap hM
  have has₀ := C.not_conj_az_swap hM hk₀X hk₀ hs₀z hs₀K
  have hat₀ := C.swap.not_conj_az_swap hM hh₀X hh₀ ht₀z ht₀K
  rw [hazz] at hat₀
  have ht₀n' : ∀ h : G, h * a = a * h → h * z * h⁻¹ ≠ t₀ := by
    intro h hh hhz
    apply ht₀n h hhz
    rw [hazz]; exact hh
  have hs₀n' : ∀ h : G, h * (a * z) = (a * z) * h → h * z * h⁻¹ ≠ s₀ :=
    fun h hh hhz => hs₀n h hhz hh
  obtain ⟨hzY, -, -, -, -, -⟩ := C.om5
  obtain ⟨hzY', -, -, -, -, -⟩ := C.swap.om5
  have ht₀X : t₀ ∈ exactLayer Ω (a * z) := by
    rw [← hh₀]; exact mul_mem (mul_mem hh₀X hzY') (inv_mem hh₀X)
  have ht₀az : t₀ * (a * z) = (a * z) * t₀ :=
    Subgroup.mem_centralizer_singleton_iff.mp (exactLayer_le_centralizer Ω (a * z) ht₀X)
  have ht₀a : t₀ * a = a * t₀ := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    calc t₀ * a = t₀ * (a * z) * z⁻¹ := by group
      _ = (a * z) * t₀ * z⁻¹ := by rw [ht₀az]
      _ = (a * z) * (t₀ * z) := by rw [hzi]; group
      _ = (a * z) * (z * t₀) := by rw [ht₀z]
      _ = a * t₀ := by rw [← mul_assoc, hazz]
  have ht₀2 : t₀ * t₀ = 1 := by
    rw [← hh₀]
    calc h₀ * z * h₀⁻¹ * (h₀ * z * h₀⁻¹) = h₀ * (z * z) * h₀⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨g, hg, hgS⟩ := C.exists_conj_mem_S ht₀a ht₀z (isPGroup_zpowers_of_sq_eq_one ht₀2)
  have hgi := Subgroup.inv_mem _ hg
  have hgz : g⁻¹ * z * g = z := by
    have := C.norm_fix_z hgi
    rwa [inv_inv] at this
  set t₁ := g⁻¹ * t₀ * g with ht₁
  have ht₁z : t₁ * z = z * t₁ := by
    calc t₁ * z = g⁻¹ * (t₀ * (g * z * g⁻¹)) * g := by rw [ht₁]; group
      _ = g⁻¹ * (t₀ * z) * g := by
          rw [show g * z * g⁻¹ = z by
            calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
              _ = z := by group]
      _ = g⁻¹ * (z * t₀) * g := by rw [ht₀z]
      _ = (g⁻¹ * z * g) * t₁ := by rw [ht₁]; group
      _ = z * t₁ := by rw [hgz]
  have hgzc : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = g * (g⁻¹ * z * g) * g⁻¹ := by rw [hgz]
      _ = z := by group
  have ht₁K : conjSub t₁ K = K' := by
    have ht₀K' : conjSub t₀ K' = K := by
      rw [← ht₀K, ← conjSub_mul, ht₀2, conjSub_one]
    rw [ht₁, conjSub_mul, conjSub_mul]
    rcases C25Y.conjSub_pair_of_central hs hgzc with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, ht₀K, ← e2, ← conjSub_mul, inv_mul_cancel, conjSub_one, e2]
    · rw [e1, ht₀K', ← e2, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have hpull : ∀ (b w : G), (∀ h : G, h * b = b * h → h * z * h⁻¹ ≠ w) →
      ∀ h : G, h * (g⁻¹ * b * g) = (g⁻¹ * b * g) * h → h * z * h⁻¹ ≠ g⁻¹ * w * g := by
    intro b w hn h hh hhz
    apply hn (g * h * g⁻¹)
    · calc g * h * g⁻¹ * b = g * (h * (g⁻¹ * b * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * b * g) * h) * g⁻¹ := by rw [hh]
        _ = b * (g * h * g⁻¹) := by group
    · calc g * h * g⁻¹ * z * (g * h * g⁻¹)⁻¹ = g * (h * (g⁻¹ * z * g) * h⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [hgz, hhz]
        _ = w := by group
  have hpullG : ∀ b : G, (¬ ∃ g' : G, g' * z * g'⁻¹ = b * t₀) →
      ¬ ∃ g' : G, g' * z * g'⁻¹ = (g⁻¹ * b * g) * t₁ := by
    rintro b hn ⟨g', hg'⟩
    apply hn ⟨g * g', ?_⟩
    calc g * g' * z * (g * g')⁻¹ = g * (g' * z * g'⁻¹) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * t₁) * g⁻¹ := by rw [hg']
      _ = b * t₀ := by rw [ht₁]; group
  have hh₁ : (g⁻¹ * h₀ * g) * z * (g⁻¹ * h₀ * g)⁻¹ = t₁ := by
    calc (g⁻¹ * h₀ * g) * z * (g⁻¹ * h₀ * g)⁻¹ = g⁻¹ * (h₀ * (g * z * g⁻¹) * h₀⁻¹) * g := by group
      _ = t₁ := by rw [hgzc, hh₀, ht₁]
  have hconjX : ∀ c : G, g⁻¹ * h₀ * g ∈ exactLayer Ω (g⁻¹ * c * g) ↔
      h₀ ∈ exactLayer Ω c := by
    intro c
    have e := exactLayer_conj hΩ.conjInvariant g⁻¹ c
    rw [inv_inv] at e
    rw [e, mem_conjSub_iff, inv_inv]
    constructor <;> intro h <;> simpa [mul_assoc] using h
  rcases C.norm_a_cases hgi with hga | hga <;> rw [inv_inv] at hga
  ·
    left
    have hgaz : g⁻¹ * (a * z) * g = a * z := by
      calc g⁻¹ * (a * z) * g = (g⁻¹ * a * g) * (g⁻¹ * z * g) := by group
        _ = a * z := by rw [hga, hgz]
    have hX1 : g⁻¹ * h₀ * g ∈ exactLayer Ω (a * z) := by
      rw [← hgaz]; exact (hconjX (a * z)).mpr hh₀X
    refine ⟨t₁, s₀, C.mk_swaps hM hX1 hh₁ ht₁z ht₁K ?_ ?_ hk₀X hk₀ hs₀z hs₀n' has₀, hgS⟩
    · have := hpull a t₀ ht₀n'
      rwa [hga] at this
    · have := hpullG a hat₀
      rwa [hga] at this
  ·
    right
    have hgaz : g⁻¹ * (a * z) * g = a * z * z := by
      calc g⁻¹ * (a * z) * g = (g⁻¹ * a * g) * (g⁻¹ * z * g) := by group
        _ = a * z * z := by rw [hga, hgz]
    have hX1 : g⁻¹ * h₀ * g ∈ exactLayer Ω (a * z * z) := by
      rw [← hgaz]; exact (hconjX (a * z)).mpr hh₀X
    refine ⟨t₁, t₀, C.swap.mk_swaps hM hX1 hh₁ ht₁z ht₁K ?_ ?_ hh₀X hh₀ ht₀z ?_ ?_, hgS⟩
    · have := hpull a t₀ ht₀n'
      rwa [hga] at this
    · have := hpullG a hat₀
      rwa [hga] at this
    · intro h hh hhz
      apply ht₀n' h _ hhz
      rw [hazz] at hh; exact hh
    · rw [hazz]; exact hat₀

end Ctx

end CFSG.ClassicalInvolution.Asc77.C5O

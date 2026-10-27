module

public import CFSG.ClassicalInvolution.Asc77.AscT7TC15
public import CFSG.ClassicalInvolution.Asc77.AscT7HC4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15SExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open scoped commutatorElement

structure TwinSect0 {X : Type} [Group X] (Φ : Set (Subgroup X)) (A A' : Subgroup X)
    (z a₀ b₀ : X) : Prop where
  hA : A ∈ Φ
  hA' : A' ∈ Φ
  ne : A ≠ A'
  hzA : IsUniqueInvolution A z
  hzA' : IsUniqueInvolution A' z
  ha₀ : a₀ ∈ A
  hb₀ : b₀ ∈ A'
  ha₀sq : a₀ * a₀ = z
  hb₀sq : b₀ * b₀ = z
  nbA : ∀ M ∈ Φ, M ∈ omegaNbr Φ A → M = A'
  nbA' : ∀ M ∈ Φ, M ∈ omegaNbr Φ A' → M = A

namespace C25X

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G}


theorem sq_eq_of_orderOf_four {K : Subgroup G} {z u : G} (hz : IsUniqueInvolution K z) (hu : u ∈ K)
    (h4 : orderOf u = 4) : u * u = z := by
  have h2 : (u * u) * (u * u) = 1 := by
    have := pow_orderOf_eq_one u
    rw [h4] at this
    calc (u * u) * (u * u) = u ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have h1 : u * u ≠ 1 := by
    intro h
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [h4] at this
    omega
  exact (hz.unique _ (K.mul_mem hu hu) h2).resolve_left h1

theorem layer_a_frame {S : Sylow 2 G} {R R' : Subgroup G} {t u₁ u₂ : G}
    (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) {a : G} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (haR : ∀ x ∈ R, a * x = x * a) (haR' : ∀ x ∈ R', a * x = x * a) :
    ∃ (hzY : z ∈ exactLayer Ω a) (hu₁Y : u₁ ∈ exactLayer Ω a) (hu₂Y : u₂ ∈ exactLayer Ω a),
      K ∈ tqMembers Ω a ∧ K' ∈ tqMembers Ω a ∧
      GenSection p f (oddQuotientFamily (exactPair Ω a)) ∧
      Nat.card (↥(exactLayer Ω a) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω a)) < Nat.card G ∧
      TwinSect0 (oddQuotientFamily (exactPair Ω a)) (T7H.exactImg Ω a K) (T7H.exactImg Ω a K')
        (T7H.toBar Ω a z hzY) (T7H.toBar Ω a u₁ hu₁Y) (T7H.toBar Ω a u₂ hu₂Y) := by
  classical
  obtain ⟨t', h⟩ := T7T.exists_hyp25T hyp
  have hs : Hyp23Setting p f Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK : IsUniqueInvolution K z := hs.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hcpg : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_eq_one ha2
  have hRsyl : IsSylow2In R K := h.hRsyl
  have hR'syl : IsSylow2In R' K' := h.hR'syl
  have hRc : R ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haR x hx).symm
  have hR'c : R' ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (haR' x hx).symm
  have hK₂ : K ∈ tqMembers Ω a :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcpg).mpr ⟨hKΩ, R, hRsyl, hRc⟩
  have hK₂' : K' ∈ tqMembers Ω a :=
    (mem_tqMembers_iff_exists_sylow hp hq hΩ hcpg).mpr ⟨hK'Ω, R', hR'syl, hR'c⟩
  have hS₂ : IsSylow2In R (exactCore a K) :=
    (isSylow2In_exactCore_iff hΩ hcpg hKΩ hK₂.2).mpr ⟨hRsyl, hRc⟩
  have hS₂' : IsSylow2In R' (exactCore a K') :=
    (isSylow2In_exactCore_iff hΩ hcpg hK'Ω hK₂'.2).mpr ⟨hR'syl, hR'c⟩
  have hu₁R : u₁ ∈ R := hyp.hu₁.1
  have hu₂R' : u₂ ∈ R' := hyp.hu₂.1
  have hu₁sq : u₁ * u₁ = z := sq_eq_of_orderOf_four hzK (hRsyl.1 hu₁R) hyp.hu₁.2.1
  have hu₂sq : u₂ * u₂ = z := sq_eq_of_orderOf_four hzK' (hR'syl.1 hu₂R') hyp.hu₂.2.1
  set Y := exactLayer Ω a with hY
  set N₀ := classicalInvolutionOddCore ↥Y with hN₀
  have hN₀odd : Odd (Nat.card N₀) := CFSG.ComponentClassification.OddCore.odd_card ↥Y
  have hΛ : HypOmegaMod p f (exactPair Ω a) := hypOmegaMod_exactPair hp hq hΩ hcpg
  have hΦ : HypOmegaMod p f (oddQuotientFamily (exactPair Ω a)) :=
    oddQuotHyp p f hp hq ↥Y (exactPair Ω a) hΛ N₀ hN₀odd
  have hzc : z ∈ exactCore a K := (T7H.isUniqueInvolution_exactCore hp hΩ hcpg hK₂ hzK).mem
  have hzY : z ∈ Y := exactCore_le_exactLayer hK₂ hzc
  have hu₁c : u₁ ∈ exactCore a K := hS₂.1 hu₁R
  have hu₂c : u₂ ∈ exactCore a K' := hS₂'.1 hu₂R'
  have hu₁Y : u₁ ∈ Y := exactCore_le_exactLayer hK₂ hu₁c
  have hu₂Y : u₂ ∈ Y := exactCore_le_exactLayer hK₂' hu₂c
  have hperp' : KPerp Ω K' = {K', K} := by rw [hs.perp_of_twin hs.hK', Set.pair_comm]
  have hA : T7H.exactImg Ω a K ∈ oddQuotientFamily (exactPair Ω a) := T7H.exactImg_mem hK₂
  have hA' : T7H.exactImg Ω a K' ∈ oddQuotientFamily (exactPair Ω a) := T7H.exactImg_mem hK₂'
  have hzA := T7H.exactImg_isUnique hp hΩ hcpg hK₂ hzK hzY
  have hzA' := T7H.exactImg_isUnique hp hΩ hcpg hK₂' hzK' hzY
  have hne : T7H.exactImg Ω a K ≠ T7H.exactImg Ω a K' := by
    refine map_ne_of_commutes_sylow (N := N₀) hp hΦ hN₀odd
      (M₁ := (exactCore a K).subgroupOf Y) (M₂ := (exactCore a K').subgroupOf Y)
      (V₁ := R.subgroupOf Y) (V₂ := R'.subgroupOf Y)
      ⟨_, exactCore_mem_exactFamily hK₂, exactCore_le_exactLayer hK₂, rfl⟩
      (hS₂.subgroupOf (exactCore_le_exactLayer hK₂))
      (hS₂'.subgroupOf (exactCore_le_exactLayer hK₂')) ?_
    intro x hx y hy
    exact Subtype.ext (h.hcomm x (Subgroup.mem_subgroupOf.mp hx) y (Subgroup.mem_subgroupOf.mp hy))
  have hnbA : ∀ M ∈ oddQuotientFamily (exactPair Ω a),
      M ∈ omegaNbr (oddQuotientFamily (exactPair Ω a)) (T7H.exactImg Ω a K) →
        M = T7H.exactImg Ω a K' := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hM
    exact T7H.exactImg_nbr_eq hp hq hΩ hcpg hK₂ hs.perp hJ hMn
  have hnbA' : ∀ M ∈ oddQuotientFamily (exactPair Ω a),
      M ∈ omegaNbr (oddQuotientFamily (exactPair Ω a)) (T7H.exactImg Ω a K') →
        M = T7H.exactImg Ω a K := by
    intro M hM hMn
    obtain ⟨J, hJ, rfl⟩ := T7H.exists_exactImg_of_mem hM
    exact T7H.exactImg_nbr_eq hp hq hΩ hcpg hK₂' hperp' hJ hMn
  have hgen : omegaGen (oddQuotientFamily (exactPair Ω a)) = ⊤ :=
    omegaGen_quotFamily_eq_top (exactPair Ω a) N₀
      (omegaGen_restrictFamily_eq_top (exactFamily Ω a) Y (exactLayer_eq_iSup Ω a).symm)
  have hAΩ : ∀ M ∈ Ω, AEmpty Ω M := hst.aEmpty
  have hAΛ : ∀ L ∈ exactPair Ω a, AEmpty (exactPair Ω a) L := by
    have h0 := aEmpty_exactPair hp hq hΩ hAΩ hcpg
    have e0 : centralizingMembers (exactFamily Ω a) {a} = exactFamily Ω a :=
      centMembers_exactFamily Ω a
    rw [e0] at h0
    exact h0
  have hAΦ : ∀ L ∈ oddQuotientFamily (exactPair Ω a),
      AEmpty (oddQuotientFamily (exactPair Ω a)) L :=
    aEmpty_quotFamily hp hq hΛ hΦ hN₀odd hAΛ
  have hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    obtain ⟨z₀, hz₀⟩ := hΩ.classical K hKΩ
    obtain ⟨x, -, y, -, hxy⟩ := ih8_exists_noncomm hz₀
    have hacen : a ∈ Subgroup.center G := hsub (Set.mem_singleton a)
    exact ha1 (T7B.eq_one_of_central ⟨x, y, hxy⟩
      (fun g' => Subgroup.mem_center_iff.mp hacen g'))
  have hlt : Nat.card (↥Y ⧸ N₀) < Nat.card G := by
    have h1 : Nat.card (↥Y ⧸ N₀) ≤ Nat.card ↥Y :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card N₀)
    have h2 : Nat.card ↥Y < Nat.card G := card_exactLayer_lt hnc
    omega
  have haB : T7H.toBar Ω a u₁ hu₁Y ∈ T7H.exactImg Ω a K := T7H.mem_exactImg hu₁c hu₁Y
  have hbB : T7H.toBar Ω a u₂ hu₂Y ∈ T7H.exactImg Ω a K' := T7H.mem_exactImg hu₂c hu₂Y
  have haBsq : T7H.toBar Ω a u₁ hu₁Y * T7H.toBar Ω a u₁ hu₁Y = T7H.toBar Ω a z hzY := by
    have h1 : (⟨u₁, hu₁Y⟩ : ↥Y) * ⟨u₁, hu₁Y⟩ = ⟨z, hzY⟩ := Subtype.ext hu₁sq
    unfold T7H.toBar
    rw [← map_mul, h1]
  have hbBsq : T7H.toBar Ω a u₂ hu₂Y * T7H.toBar Ω a u₂ hu₂Y = T7H.toBar Ω a z hzY := by
    have h1 : (⟨u₂, hu₂Y⟩ : ↥Y) * ⟨u₂, hu₂Y⟩ = ⟨z, hzY⟩ := Subtype.ext hu₂sq
    unfold T7H.toBar
    rw [← map_mul, h1]
  exact ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂',
    ⟨hΦ, CFSG.ComponentClassification.OddCore.quotient_corefree ↥Y, hgen, hAΦ⟩, hlt,
    ⟨hA, hA', hne, hzA, hzA', haB, hbB, haBsq, hbBsq, hnbA, hnbA'⟩⟩

end C25X

end CFSG.ClassicalInvolution.Asc77

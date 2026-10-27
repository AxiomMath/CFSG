module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.ThreePairStrong

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

theorem D2AlmostSimple.eq_top_of_card_outer_eq_one (h : D2AlmostSimple p X R A X₀ K)
    (hout : Nat.card (Outer K) = 1) : K = ⊤ := by
  have : K.Normal := h.normal
  rw [eq_top_iff]
  intro x _
  let ψ : X →* Outer K := (QuotientGroup.mk' (inner K)).comp (MulAut.conjNormal (H := K))
  have hψ : ψ x = 1 := by
    have : Subsingleton (Outer K) := (Nat.card_eq_one_iff_unique.mp hout).1
    exact Subsingleton.elim _ _
  obtain ⟨c, hc⟩ := (QuotientGroup.eq_one_iff _).mp hψ
  have hcent : (c : X)⁻¹ * x ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hc ⟨y, hy⟩)
    rw [MulAut.conjNormal_apply] at h1
    change (c : X) * y * (c : X)⁻¹ = x * y * x⁻¹ at h1
    calc y * ((c : X)⁻¹ * x) = (c : X)⁻¹ * ((c : X) * y * (c : X)⁻¹) * x := by group
      _ = (c : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (c : X)⁻¹ * x * y := by group
  rw [h.centralizer_eq_bot, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  exact hcent ▸ c.2

theorem primeComplementCore_normalizer_eq_bot [Fact p.Prime] {A : Subgroup X} (hA : IsPGroup p A)
    (hC : Subgroup.centralizer (A : Set X) ≤ A) :
    primeComplementCore (G := Subgroup.normalizer (A : Set X)) p = ⊥ := by
  set N := Subgroup.normalizer (A : Set X)
  set W := (primeComplementCore (G := N) p).map N.subtype with hWdef
  have hWsub : W.subgroupOf N = primeComplementCore (G := N) p :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
  have hWN : W ≤ N := Subgroup.map_subtype_le _
  have hNW : N ≤ Subgroup.normalizer (W : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWN).mp (by rw [hWsub]; infer_instance)
  have hcop : p.Coprime (Nat.card W) := by
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact primeComplementCore_coprime p
  have hAW : A ⊓ W = ⊥ := inf_eq_bot_of_isPGroup Fact.out hA hcop
  have hAN : A ≤ N := Subgroup.le_normalizer
  have hWC : W ≤ Subgroup.centralizer (A : Set X) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hcomm : w * a * w⁻¹ * a⁻¹ ∈ A ⊓ W := by
      refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp (hWN hw) a).mp ha) (A.inv_mem ha), ?_⟩
      have h1 : a * w⁻¹ * a⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hNW (hAN ha)) w⁻¹).mp (W.inv_mem hw)
      have h2 : w * (a * w⁻¹ * a⁻¹) ∈ W := W.mul_mem hw h1
      simpa [mul_assoc] using h2
    rw [hAW, Subgroup.mem_bot] at hcomm
    have : w * a = a * w := by
      calc w * a = (w * a * w⁻¹ * a⁻¹) * a * w := by group
        _ = a * w := by rw [hcomm, one_mul]
    exact this.symm
  have hW : W = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ A ⊓ W := ⟨hC (hWC hw), hw⟩
    rwa [hAW] at this
  exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp hW

theorem D2AlmostSimple.eq_normalizer_of_card_outer_eq_one {i : TauCeti.CFSGIndex} {X : Type}
    [Group X] [Finite X] {R : Sylow p X} {A X₀ K : Subgroup X}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) →
      Nat.card (Outer L) = 1 ∧ ∀ S : Sylow p L, Nat.card (S : Subgroup L) = p ^ 2 ∧
        Subgroup.centralizer ((S : Subgroup L) : Set L) ≤ S ∧
        ∀ Y : Subgroup L, Subgroup.normalizer ((S : Subgroup L) : Set L) ≤ Y →
          Y = Subgroup.normalizer ((S : Subgroup L) : Set L) ∨ Y = ⊤)
    (hK : D2AlmostSimple p X R A X₀ K) (e : K ≃* i.Group) :
    X₀ = Subgroup.normalizer ((R : Subgroup X) : Set X) ∧
      Subgroup.centralizer ((R : Subgroup X) : Set X) ≤ R ∧ Nat.card (R : Subgroup X) = p ^ 2 := by
  have hKtop := hK.eq_top_of_card_outer_eq_one (h K ⟨e⟩).1
  have eX : X ≃* i.Group :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hKtop.symm)).trans e
  obtain ⟨hcard, hC, hmax⟩ := (h X ⟨eX⟩).2 R
  have hRA : (R : Subgroup X) = A :=
    (Subgroup.eq_of_le_of_card_ge hK.A_le (by rw [hcard, hK.card_A])).symm
  have hAne : A ≠ ⊥ := by
    intro hA
    have hc := hK.card_A
    rw [hA, Subgroup.card_bot] at hc
    have := Nat.one_lt_pow two_ne_zero hK.prime.one_lt
    omega
  have hNX₀ : Subgroup.normalizer (A : Set X) ≤ X₀ := hK.normalizer_le_of_le_A A le_rfl hAne
  rw [← hRA] at hNX₀
  refine ⟨?_, hC, hcard⟩
  rcases hmax X₀ hNX₀ with hX | hX
  · exact hX
  · exact absurd (hX ▸ le_top) hK.not_le

theorem d2PairAt_of_maximal {i : TauCeti.CFSGIndex} {p : ℕ}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) →
      Nat.card (Outer L) = 1 ∧ ∀ S : Sylow p L, Nat.card (S : Subgroup L) = p ^ 2 ∧
        Subgroup.centralizer ((S : Subgroup L) : Set L) ≤ S ∧
        ∀ Y : Subgroup L, Subgroup.normalizer ((S : Subgroup L) : Set L) ≤ Y →
          Y = Subgroup.normalizer ((S : Subgroup L) : Set L) ∨ Y = ⊤) :
    D2PairAt i fun q => q = p := by
  intro X _ _ q hq R A X₀ K hK ⟨e⟩
  subst hq
  have : Fact q.Prime := ⟨hK.prime⟩
  obtain ⟨hX₀, hC, -⟩ := hK.eq_normalizer_of_card_outer_eq_one h e
  subst hX₀
  exact primeComplementCore_normalizer_eq_bot R.isPGroup' hC

theorem d2SolvableAt_of_maximal {i : TauCeti.CFSGIndex}
    (h : ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* i.Group) →
      Nat.card (Outer L) = 1 ∧ ∀ S : Sylow 3 L, Nat.card (S : Subgroup L) = 3 ^ 2 ∧
        Subgroup.centralizer ((S : Subgroup L) : Set L) ≤ S ∧
        ∀ Y : Subgroup L, Subgroup.normalizer ((S : Subgroup L) : Set L) ≤ Y →
          Y = Subgroup.normalizer ((S : Subgroup L) : Set L) ∨ Y = ⊤) :
    D2SolvableAt i fun q => q = 3 := by
  intro X _ _ q hq R A X₀ K hK ⟨e⟩
  subst hq
  obtain ⟨hX₀, hC, hcard⟩ := hK.eq_normalizer_of_card_outer_eq_one h e
  rw [hX₀]
  exact isSolvable_normalizer_of_card_eq_nine_of_le hcard hC

@[expose] def KFactM11Three : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic .M11).Group) →
    Nat.card (Outer L) = 1 ∧ ∀ S : Sylow 3 L, Nat.card (S : Subgroup L) = 3 ^ 2 ∧
      Subgroup.centralizer ((S : Subgroup L) : Set L) ≤ S ∧
      ∀ Y : Subgroup L, Subgroup.normalizer ((S : Subgroup L) : Set L) ≤ Y →
        Y = Subgroup.normalizer ((S : Subgroup L) : Set L) ∨ Y = ⊤

theorem d2IndexCaseAt_m11_three (hKF : KFactM11Three) (h84 : Asc81bEightFour)
    (hD2 : D1NoXBlock) (hS : D2PairStrongThree) :
    D2IndexCaseAt (.sporadic .M11) fun p => p = 3 :=
  d2IndexCaseAt_three_of_pairStrong (d2PairAt_of_maximal hKF) (d2SolvableAt_of_maximal hKF) h84
    hD2 hS

end CFSG.AGLEmbeddingD2

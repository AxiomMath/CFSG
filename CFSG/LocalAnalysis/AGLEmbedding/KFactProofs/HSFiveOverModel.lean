module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.OverGood
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.RankThree.Native CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint

theorem exists_model_conj {X G : Type*} [Group X] [Finite X] [Group G] [Finite G]
    (ι : X →* G) (hι : Function.Injective ι) {B R₀ : Subgroup G} (hB : ι.range = B)
    (hR₀B : R₀ ≤ B) (hR₀ : Nat.card R₀ = 5 ^ (Nat.card B).factorization 5) (R : Sylow 5 X)
    {X₀ : Subgroup X} (hNX : Subgroup.normalizer ((R : Subgroup X) : Set X) ≤ X₀)
    (hX₀top : X₀ ≠ ⊤) (hX₀N : X₀ ≠ Subgroup.normalizer ((R : Subgroup X) : Set X)) :
    ∃ X₂ : Subgroup G, B ⊓ Subgroup.normalizer (R₀ : Set G) ≤ X₂ ∧ X₂ ≤ B ∧
      X₂ ≠ B ⊓ Subgroup.normalizer (R₀ : Set G) ∧ X₂ ≠ B ∧
      (OverGood R₀ X₂ → OverGood (R : Subgroup X) X₀) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set R₁ := (R : Subgroup X).map ι with hR₁def
  have hR₁B : R₁ ≤ B := by
    rw [← hB]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hcardX : Nat.card X = Nat.card B := by
    rw [← hB]
    exact Nat.card_congr (MonoidHom.ofInjective hι).toEquiv
  have hR₁ : Nat.card R₁ = 5 ^ (Nat.card B).factorization 5 := by
    rw [hR₁def, Subgroup.card_map_of_injective hι, ← hcardX]
    exact R.card_eq_multiplicity
  obtain ⟨c, hcB, hc⟩ := exists_conj_eq_of_card_eq hR₁B hR₀B hR₁ hR₀
  set X₁ := X₀.map ι with hX₁def
  have hX₁B : X₁ ≤ B := by
    rw [← hB]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  set X₂ := X₁.map (MulAut.conj c⁻¹).toMonoidHom with hX₂def
  have hconjB : ∀ g : G, g ∈ B → ∀ y ∈ B, g * y * g⁻¹ ∈ B := fun g hg y hy =>
    B.mul_mem (B.mul_mem hg hy) (B.inv_mem hg)
  have hR : R₁.comap ι = (R : Subgroup X) := Subgroup.comap_map_eq_self_of_injective hι _
  have hX₀ : X₁.comap ι = X₀ := Subgroup.comap_map_eq_self_of_injective hι _
  have hNR : (Subgroup.normalizer (R₁ : Set G)).comap ι =
      Subgroup.normalizer ((R : Subgroup X) : Set X) := by
    have h := Subgroup.comap_normalizer_eq_of_le_range (f := ι) (H := R₁) (by rw [hB]; exact hR₁B)
    rw [h, hR]
  have hNconj : (B ⊓ Subgroup.normalizer (R₀ : Set G)).map (MulAut.conj c).toMonoidHom =
      B ⊓ Subgroup.normalizer (R₁ : Set G) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj c).injective, Subgroup.map_equiv_normalizer_eq,
      ← hc]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hconjB c hcB z hz
    · intro hy
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · have := hconjB c⁻¹ (B.inv_mem hcB) y hy
        simpa using this
      · show c * (c⁻¹ * y * c) * c⁻¹ = y
        group
  have hX₂X₁ : X₂.map (MulAut.conj c).toMonoidHom = X₁ := by
    rw [hX₂def, Subgroup.map_map]
    convert Subgroup.map_id X₁ using 2
    ext y
    show c * (c⁻¹ * y * c⁻¹⁻¹) * c⁻¹ = y
    group
  have hBcomap : B.comap ι = ⊤ := by
    rw [← hB]
    exact eq_top_iff.mpr fun x _ => ⟨x, rfl⟩
  have hBconj : B.map (MulAut.conj c).toMonoidHom = B := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hconjB c hcB y hy
    · intro y hy
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · have := hconjB c⁻¹ (B.inv_mem hcB) y hy
        simpa using this
      · show c * (c⁻¹ * y * c) * c⁻¹ = y
        group
  refine ⟨X₂, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro n hn
    have h1 : c * n * c⁻¹ ∈ B ⊓ Subgroup.normalizer (R₁ : Set G) := by
      rw [← hNconj]
      exact ⟨n, hn, rfl⟩
    obtain ⟨x, hx⟩ : c * n * c⁻¹ ∈ ι.range := hB ▸ h1.1
    have hxN : x ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) := by
      rw [← hNR]
      show ι x ∈ Subgroup.normalizer (R₁ : Set G)
      rw [hx]
      exact h1.2
    refine ⟨ι x, ⟨x, hNX hxN, rfl⟩, ?_⟩
    show c⁻¹ * ι x * c⁻¹⁻¹ = n
    rw [hx]
    group
  ·
    rintro _ ⟨y, hy, rfl⟩
    exact hconjB c⁻¹ (B.inv_mem hcB) y (hX₁B hy)
  ·
    intro h
    apply hX₀N
    rw [← hX₀, ← hX₂X₁, h, hNconj, Subgroup.comap_inf, ← hNR, hBcomap, top_inf_eq]
  ·
    intro h
    apply hX₀top
    rw [← hX₀, ← hX₂X₁, h, hBconj, hBcomap]
  · intro hG
    have h1 := hG.map_equiv (MulAut.conj c)
    rw [← hc, hX₂X₁] at h1
    have h2 := h1.comap_of_injective ι hι (hB.symm ▸ hX₁B)
    rwa [hR, hX₀] at h2

theorem centralizer_eq_bot_of_perfect {X : Type*} [Group X] {R U : Subgroup X}
    (hRU : R ≤ U) (hR : R ≠ ⊥) (hCR : Subgroup.centralizer (R : Set X) ≤ R) (hUU : ⁅U, U⁆ = U)
    (hUs : ∀ W : Subgroup X, W ≤ U → U ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ W = U) :
    Subgroup.centralizer (U : Set X) = ⊥ := by
  have hCU : Subgroup.centralizer (U : Set X) ≤ U :=
    (Subgroup.centralizer_le hRU).trans (hCR.trans hRU)
  have hfix : ∀ u ∈ U, ∀ g ∈ Subgroup.centralizer (U : Set X), u * g * u⁻¹ = g := by
    intro u hu g hg
    rw [Subgroup.mem_centralizer_iff] at hg
    rw [hg u hu]
    group
  have hnorm : U ≤ Subgroup.normalizer ((Subgroup.centralizer (U : Set X)) : Set X) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      rw [hfix u hu g hg]
      exact hg
    · intro hg
      have h1 := hfix u⁻¹ (U.inv_mem hu) _ hg
      rw [show u⁻¹ * (u * g * u⁻¹) * u⁻¹⁻¹ = g by group] at h1
      rw [h1]
      exact hg
  rcases hUs _ hCU hnorm with h | h
  · exact h
  · exfalso
    have hab : ⁅U, U⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have hb' : b ∈ Subgroup.centralizer (U : Set X) := by rw [h]; exact hb
      rw [Subgroup.mem_centralizer_iff] at hb'
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hb' a ha
    apply hR
    rw [eq_bot_iff]
    calc R ≤ U := hRU
      _ = ⁅U, U⁆ := hUU.symm
      _ = ⊥ := hab

theorem kFactHSFiveOver_of_model
    (hR₀P : hsOR0 ≤ hs100P) (hR₀ : Nat.card hsOR0 = 5 ^ 3)
    (hA1 : ∀ Y : Subgroup (Equiv.Perm (Fin 100)),
      hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y → Y ≤ hs100R →
        Y = hs100R ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∨ Y = hs100R)
    (hA2 : ∀ Y : Subgroup (Equiv.Perm (Fin 100)),
      hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ≤ Y → Y ≤ hs100P →
        Y = hs100P ⊓ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∨ Y = hsOUA2 ∨
          Y = hsOUB2 ∨ Y = hs100P)
    (hGA : OverGood hsOR0 hsOUA2) (hGB : OverGood hsOR0 hsOUB2) : KFactHSFiveOver := by
  intro X _ _ K hKn hC ⟨e⟩ R X₀ hNX hX₀top hX₀N
  have : K.Normal := hKn
  obtain ⟨eC⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  let θ : K ≃* hs100P := (e.trans eC.symm).trans hs100Equiv
  have hmodel := CFSG.RankThree.PartOne.hs_autModel
  have hinj := hmodel.embed_injective K θ hC
  set ι := hmodel.embed K θ with hι
  have hPB : hs100P ≤ ι.range := fun y hy =>
    ⟨(θ.symm ⟨y, hy⟩ : K), by rw [hι, hmodel.embed_coe, MulEquiv.apply_symm_apply]⟩
  have hBR : ι.range ≤ hs100R := by
    rintro _ ⟨x, rfl⟩
    exact hmodel.embed_mem K θ x
  have hcard2 : Nat.card hs100R = 2 * Nat.card hs100P := by
    rw [card_hs100R, card_hs100P]
  have hfP : (Nat.card hs100P).factorization 5 = 3 := factorization_card_hs100P_five
  have hfR : (Nat.card hs100R).factorization 5 = 3 := by
    rw [card_hs100R]
    exact factorization_eq_of_pow_dvd Nat.prime_five (k := 3) (by norm_num) (by norm_num)
      (by norm_num)
  rcases eq_or_eq_of_index_two hPB hBR hcard2 with hB | hB
  ·
    obtain ⟨X₂, hNX₂, hX₂B, hX₂N, hX₂top, hgood⟩ := exists_model_conj ι hinj hB hR₀P
      (by rw [hR₀, hfP]) R hNX hX₀top hX₀N
    have hG : OverGood hsOR0 X₂ := by
      rcases hA2 X₂ hNX₂ hX₂B with h | h | h | h
      · exact absurd h hX₂N
      · exact h ▸ hGA
      · exact h ▸ hGB
      · exact absurd h hX₂top
    obtain ⟨U, hUX, hXN, hUU, hRU, hUs, hUp, hUo, hE⟩ := hgood hG
    refine ⟨?_, U, hUX, hXN, hUU, hRU, hUs, hUp, ?_, hUo, hE⟩
    ·
      have hK : K.map ι = hs100P := by
        apply le_antisymm
        · rintro _ ⟨k, hk, rfl⟩
          have : ι k = θ ⟨k, hk⟩ := hmodel.embed_coe K θ ⟨k, hk⟩
          rw [this]
          exact (θ ⟨k, hk⟩).2
        · intro y hy
          refine ⟨(θ.symm ⟨y, hy⟩ : K), (θ.symm ⟨y, hy⟩).2, ?_⟩
          rw [hmodel.embed_coe, MulEquiv.apply_symm_apply]
      have htop : (⊤ : Subgroup X).map ι = K.map ι := by
        rw [hK, ← hB, MonoidHom.range_eq_map]
      exact (Subgroup.map_injective hinj htop).symm
    ·
      let eX : X ≃* hs100P :=
        (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hB)
      have hloc := heisLocalEq_hsP eX R
      refine centralizer_eq_bot_of_perfect hRU ?_ hloc.2.1 hUU hUs
      intro hbot
      have h1 := hloc.1
      rw [hbot, Subgroup.card_bot] at h1
      norm_num at h1
  ·
    exfalso
    obtain ⟨X₂, hNX₂, hX₂B, hX₂N, hX₂top, -⟩ := exists_model_conj ι hinj hB
      (hR₀P.trans (hPB.trans hBR))
      (by rw [hR₀, hfR]) R hNX hX₀top hX₀N
    rcases hA1 X₂ hNX₂ hX₂B with h | h
    · exact hX₂N h
    · exact hX₂top h

theorem wordVal_hsOAB_mem (w : List ℤ) : CFSG.AGLEmbedding.FusD2.wordVal hsOAB w ∈ hs100P :=
  CFSG.AGLEmbedding.FusD2.wordVal_mem hsOAB hs100P (by
    intro g hg
    simp only [hsOAB, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)) w

theorem hsOR0_le_hs100P : hsOR0 ≤ hs100P := by
  rw [hsOR0, Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · exact wordVal_hsOAB_mem _
  · exact wordVal_hsOAB_mem _

end CFSG.AGLEmbeddingD2

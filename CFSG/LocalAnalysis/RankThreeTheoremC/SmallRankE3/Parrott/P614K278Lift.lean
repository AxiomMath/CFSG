module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmThree

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

variable {A : Type} [Group A] [Finite A]

theorem exists_perfect_normal {X : Subgroup A} {L : Subgroup (P64Asm.XBar 3 X)} [L.Normal]
    (hLp : ⁅L, L⁆ = L) :
    ∃ K₀ : Subgroup X, K₀.Normal ∧ K₀.map (P64Asm.XBar.mk 3 X) = L ∧ ⁅K₀, K₀⁆ = K₀ := by
  have hπ : Function.Surjective (P64Asm.XBar.mk 3 X) := QuotientGroup.mk'_surjective _
  obtain ⟨K₀, -, ⟨hKn, hKL⟩, hKmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun N : Subgroup X => N.Normal ∧ N.map (P64Asm.XBar.mk 3 X) = L)
    (L.comap (P64Asm.XBar.mk 3 X)) ⟨inferInstance, map_comap_eq_self_of_surjective hπ L⟩
  haveI := hKn
  refine ⟨K₀, hKn, hKL, le_antisymm (commutator_le_left K₀ K₀) ?_⟩
  exact hKmin ⟨inferInstance, by rw [map_commutator, hKL, hLp]⟩ (commutator_le_left K₀ K₀)

theorem exists_lift {X : Subgroup A} {L : Subgroup (P64Asm.XBar 3 X)} [L.Normal]
    (hLs : IsSimpleGroup L) (hLp : ⁅L, L⁆ = L) (h3 : 3 ∣ Nat.card L) :
    ∃ K : Subgroup A, K ≤ X ∧ X ≤ normalizer (K : Set A) ∧ ⁅K, K⁆ = K ∧
      K ⊓ rankThreePrimeCore 3 X < K ∧
      (∀ N : Subgroup A, N ≤ K → (N.subgroupOf K).Normal → K ⊓ rankThreePrimeCore 3 X ≤ N →
        N = K ⊓ rankThreePrimeCore 3 X ∨ N = K) ∧
      (K.subgroupOf X).map (P64Asm.XBar.mk 3 X) = L ∧ Nonempty (Kbar K ≃* L) := by
  obtain ⟨K₀, hKn, hKL, hKp⟩ := exists_perfect_normal hLp
  set π := P64Asm.XBar.mk 3 X with hπ
  set O := rankThreePrimeCore 3 X with hOdef
  have hO : O = (primeComplementCore (G := X) 3).map X.subtype :=
    rankThreePrimeCore_eq_map_primeComplementCore 3 X
  have hker : π.ker = primeComplementCore (G := X) 3 := QuotientGroup.ker_mk' _
  set K := K₀.map X.subtype with hKdef
  have hKX : K ≤ X := map_subtype_le K₀
  have hKsub : K.subgroupOf X = K₀ := comap_map_eq_self_of_injective X.subtype_injective K₀
  have hLne : L ≠ ⊥ := (nontrivial_iff_ne_bot L).mp inferInstance
  have hval : ∀ k : K, π (inclusion hKX k) ∈ L := by
    intro k
    rw [← hKL]
    refine ⟨inclusion hKX k, ?_, rfl⟩
    have := k.2
    rw [← hKsub]
    exact this
  set ψ : K →* L := (π.comp (inclusion hKX)).codRestrict L hval with hψ
  have hψs : Function.Surjective ψ := by
    rintro ⟨l, hl⟩
    rw [← hKL] at hl
    obtain ⟨k, hk, rfl⟩ := hl
    refine ⟨⟨k, ⟨k, hk, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    rfl
  have hψker : ∀ k : K, k ∈ ψ.ker ↔ (k : A) ∈ O := by
    intro k
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : π (inclusion hKX k) = 1 := congrArg Subtype.val h1
      have h3 : inclusion hKX k ∈ primeComplementCore (G := X) 3 := by
        rw [← hker]
        exact h2
      rw [hO]
      exact ⟨_, h3, rfl⟩
    · intro h1
      rw [hO] at h1
      obtain ⟨o, ho, hoe⟩ := h1
      apply Subtype.ext
      show π (inclusion hKX k) = 1
      have : inclusion hKX k = o := Subtype.ext hoe.symm
      rw [this, ← MonoidHom.mem_ker, hker]
      exact ho
  have hψker' : ψ.ker = (K ⊓ O).subgroupOf K := by
    ext k
    rw [hψker, mem_subgroupOf, mem_inf]
    exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩
  have hcop : Nat.Coprime 3 (Nat.card ψ.ker) := by
    have h1 : Nat.card ψ.ker = Nat.card (K ⊓ O : Subgroup A) := by
      rw [hψker']
      exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
    have h2 : Nat.card O = Nat.card (primeComplementCore (G := X) 3) := by
      rw [hO, card_map_of_injective X.subtype_injective]
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (h2 ▸ card_dvd_of_le inf_le_right)
      (primeComplementCore_coprime 3)
  have hcore : CFSG.pPrimeCore 3 K = ψ.ker := by
    apply le_antisymm
    · have hmap := ((primeComplementCore_normal (G := K) 3).map ψ hψs).eq_bot_or_eq_top
      rcases hmap with h | h
      · exact (Subgroup.map_eq_bot_iff _).mp h
      · exfalso
        have h1 : Nat.card L ∣ Nat.card (primeComplementCore (G := K) 3) := by
          have := card_map_dvd (primeComplementCore (G := K) 3) ψ
          rw [h, card_top] at this
          exact this
        have h2 := Nat.Coprime.coprime_dvd_right h1 (primeComplementCore_coprime (G := K) 3)
        rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_eq_right h3] at h2
        norm_num at h2
    · exact normal_coprime_le_primeComplementCore 3 ψ.ker inferInstance hcop
  refine ⟨K, hKX, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    have hxN : (⟨x, hx⟩ : X) ∈ normalizer (K₀ : Set X) := by
      rw [normalizer_eq_top_iff.mpr hKn]
      exact mem_top _
    exact le_normalizer_map X.subtype ⟨⟨x, hx⟩, hxN, rfl⟩
  ·
    rw [hKdef, ← map_commutator, hKp]
  ·
    refine lt_of_le_of_ne inf_le_left fun h => hLne ?_
    have hKO : K₀ ≤ primeComplementCore (G := X) 3 := by
      intro k hk
      have h1 : (k : A) ∈ K ⊓ O := by
        rw [h]
        exact ⟨k, hk, rfl⟩
      rw [hO] at h1
      obtain ⟨o, ho, hoe⟩ := h1.2
      rwa [← Subtype.ext hoe]
    rw [← hKL]
    exact (Subgroup.map_eq_bot_iff _).mpr (hker.symm ▸ hKO)
  ·
    intro N hNK hNn hON
    have hkerN : ψ.ker ≤ N.subgroupOf K := by
      rw [hψker']
      intro k hk
      exact hON hk
    rcases (hNn.map ψ hψs).eq_bot_or_eq_top with h | h
    · left
      have h1 : N.subgroupOf K = (K ⊓ O).subgroupOf K := by
        rw [← hψker']
        exact le_antisymm ((Subgroup.map_eq_bot_iff _).mp h) hkerN
      rw [subgroupOf_inj, inf_eq_left.mpr hNK, inf_eq_left.mpr (inf_le_left : K ⊓ O ≤ K)] at h1
      exact h1
    · right
      have h1 : N.subgroupOf K = ⊤ := by
        have := comap_map_eq ψ (N.subgroupOf K)
        rw [h, comap_top, sup_eq_left.mpr hkerN] at this
        exact this.symm
      rw [subgroupOf_eq_top] at h1
      exact le_antisymm hNK h1
  ·
    rw [hKsub, hKL]
  ·
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

theorem le_sup_of_map_sup_eq_top {X Y K : Subgroup A}
    (h : (Y.subgroupOf X).map (P64Asm.XBar.mk 3 X) ⊔ (K.subgroupOf X).map (P64Asm.XBar.mk 3 X) =
      ⊤) :
    X ≤ (Y ⊔ K) ⊔ rankThreePrimeCore 3 X := by
  intro x hx
  have hmem : P64Asm.XBar.mk 3 X ⟨x, hx⟩ ∈
      (Y.subgroupOf X ⊔ K.subgroupOf X).map (P64Asm.XBar.mk 3 X) := by
    rw [Subgroup.map_sup, h]
    exact mem_top _
  obtain ⟨w, hw, hwx⟩ := hmem
  have ho : w⁻¹ * ⟨x, hx⟩ ∈ primeComplementCore (G := X) 3 := by
    rw [← QuotientGroup.eq_one_iff]
    change P64Asm.XBar.mk 3 X (w⁻¹ * ⟨x, hx⟩) = 1
    rw [map_mul, map_inv, hwx, inv_mul_cancel]
  have hwYK : (w : A) ∈ Y ⊔ K := by
    have hle : (Y.subgroupOf X ⊔ K.subgroupOf X).map X.subtype ≤ Y ⊔ K := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact hy
      · rintro _ ⟨k, hk, rfl⟩
        exact hk
    exact hle ⟨w, hw, rfl⟩
  have hoO : ((w⁻¹ * ⟨x, hx⟩ : X) : A) ∈ rankThreePrimeCore 3 X := by
    rw [rankThreePrimeCore_eq_map_primeComplementCore]
    exact ⟨_, ho, rfl⟩
  have e : x = (w : A) * ((w⁻¹ * ⟨x, hx⟩ : X) : A) := by simp
  rw [e]
  exact mul_mem_sup hwYK hoO

theorem relIndex_eq_card_map {X S : Subgroup A} (hSX : S ≤ X) :
    (rankThreePrimeCore 3 X).relIndex S =
      Nat.card ((S.subgroupOf X).map (P64Asm.XBar.mk 3 X)) := by
  have hS : (S.subgroupOf X).map X.subtype = S := map_subgroupOf_eq_of_le hSX
  rw [rankThreePrimeCore_eq_map_primeComplementCore]
  conv_lhs => rw [← hS]
  rw [relIndex_map_map_of_injective _ _ X.subtype_injective, ← relIndex_ker,
    QuotientGroup.ker_mk']

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K278

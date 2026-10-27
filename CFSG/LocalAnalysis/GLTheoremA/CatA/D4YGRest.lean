module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YGIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YFAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YERest
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
public import CFSG.RankThree.PartOne.KFOUT3.Galois
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.D4Y

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.D4T CFSG.StandardType CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

section Transport

variable {K : Type} [Group K] {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]

theorem inf_inner_card_eq (Φ : K ≃* Om8 K₀) (A : Subgroup (MulAut K)) :
    Nat.card ↥(A.map (MulAut.congr Φ).toMonoidHom ⊓ Inn (Om8 K₀)) = Nat.card ↥(A ⊓ innerAut K) := by
  have h : (A.map (MulAut.congr Φ).toMonoidHom ⊓ Inn (Om8 K₀)) = (A ⊓ innerAut K).map
      (MulAut.congr Φ).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.congr Φ).injective, ← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr Φ]
    rfl
  rw [h, Subgroup.card_map_of_injective (MulAut.congr Φ).injective]

theorem not_mem_sup_of_notCentral (Φ : K ≃* Om8 K₀) (hcomm : ∀ σ τ : K₀ ≃+* K₀, σ * τ = τ * σ)
    {α : MulAut K} (h : ∃ γ : MulAut K, γ * α * γ⁻¹ * α⁻¹ ∉ innerAut K) :
    MulAut.congr Φ α ∉ Inn (Om8 K₀) ⊔ (AutOm.fieldAutP (K := K₀) 4).range := by
  intro hmem
  obtain ⟨γ, hγ⟩ := h
  apply hγ
  have h1 := D4YF.commutator_mem_inner_of_mem_sup hcomm hmem (MulAut.congr Φ γ)
  rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr Φ] at h1
  obtain ⟨x, hx, hxe⟩ := h1
  have : x = γ * α * γ⁻¹ * α⁻¹ := by
    apply (MulAut.congr Φ).injective
    change (MulAut.congr Φ) x = _ at hxe
    rw [hxe]
    simp only [map_mul, map_inv]
  exact this ▸ hx

theorem inf_inner_le_nine (Φ : K ≃* Om8 K₀) (hcomm : ∀ σ τ : K₀ ≃+* K₀, σ * τ = τ * σ)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian 3 A) {α : MulAut K} (hαA : α ∈ A)
    (h : ∃ γ : MulAut K, γ * α * γ⁻¹ * α⁻¹ ∉ innerAut K) :
    Nat.card ↥(A ⊓ innerAut K) ≤ 9 := by
  have hA' := CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map (MulAut.congr Φ).toMonoidHom hA
  have hαA' : MulAut.congr Φ α ∈ A.map (MulAut.congr Φ).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hαA
  have := NbrGraphD4.card_inf_inner_le_nine hA' hαA' (not_mem_sup_of_notCentral Φ hcomm h)
  rwa [inf_inner_card_eq] at this

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem inf_inner_le_three_odd (Φ : K ≃* Om8 K₀) {n : ℕ} (hn1 : 1 ≤ n) (hK₀ : Nat.card K₀ = 2 ^ n)
    (hn : Odd n) {A : Subgroup (MulAut K)} (hA : IsElemAbelian 3 A) {α : MulAut K} (hαA : α ∈ A)
    (h : ∃ γ : MulAut K, γ * α * γ⁻¹ * α⁻¹ ∉ innerAut K) {S : Subgroup (MulAut K)}
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hAS : A ≤ Subgroup.normalizer (S : Set (MulAut K))) :
    Nat.card ↥(A ⊓ innerAut K) ≤ 3 := by
  haveI : IsCyclic (K₀ ≃+* K₀) := CFSG.RankThree.PartOne.KFOUT3.isCyclic_aut hn1 hK₀
  have hcomm : ∀ σ τ : K₀ ≃+* K₀, σ * τ = τ * σ := fun σ τ =>
    (IsCyclic.commGroup (α := K₀ ≃+* K₀)).mul_comm σ τ
  obtain ⟨-, -, -, hGalc⟩ := CFSG.RankThree.PartOne.KFOUT3.exists_frobenius hn1 hK₀
  have hGal : Odd (Nat.card (K₀ ≃+* K₀)) := by rw [hGalc]; exact hn
  have hQ3 : Nat.card K₀ % 3 = 2 := by rw [hK₀]; exact two_pow_mod_three_of_odd hn
  have hA' := CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map (MulAut.congr Φ).toMonoidHom hA
  have hαA' : MulAut.congr Φ α ∈ A.map (MulAut.congr Φ).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hαA
  have := D4YF.card_inf_inner_le_three hQ3 hGal hcomm hA' hαA'
    (not_mem_sup_of_notCentral Φ hcomm h) (S := S.map (MulAut.congr Φ).toMonoidHom)
    (hS2.map _) (fun hb => hS1 ((Subgroup.map_eq_bot_iff_of_injective S (MulAut.congr Φ).injective).1 hb))
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ (hAS hy)))
  rwa [inf_inner_card_eq] at this

end Transport

section Bbar

variable {H : Type} [Group H] [Finite H]

@[expose] def Bbar (K B : Subgroup H) : Subgroup (MulAut ↥K) :=
  (B.subgroupOf (Subgroup.normalizer (K : Set H))).map (conjHom K)

theorem card_subgroupOf_of_le' {N Y : Subgroup H} (hY : Y ≤ N) :
    Nat.card (Y.subgroupOf N) = Nat.card Y :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv

theorem card_B_eq {K B : Subgroup H} (hBK : B ≤ Subgroup.normalizer (K : Set H)) :
    Nat.card B = Nat.card (Bo K B) * Nat.card (Bbar K B) := by
  classical
  set N : Subgroup H := Subgroup.normalizer (K : Set H) with hN
  set ρ : ↥N →* MulAut ↥K := conjHom K with hρ
  set B' : Subgroup ↥N := B.subgroupOf N with hB'
  have hBo_le : Bo K B ≤ B := inf_le_left
  have hρcoe : ∀ (b : ↥N) (k : ↥K), ((ρ b k : ↥K) : H) = (b : H) * k * (b : H)⁻¹ := fun b k => rfl
  have hker : ρ.ker ⊓ B' = (Bo K B).subgroupOf N := by
    ext b
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, hB', Bo, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun k hk => ?_⟩
      have h3 := congrArg (fun σ : MulAut ↥K => ((σ ⟨k, hk⟩ : ↥K) : H)) h1
      simp only [hρcoe, MulAut.one_apply] at h3
      calc k * (b : H) = (b : H) * k * (b : H)⁻¹ * (b : H) := by rw [h3]
        _ = (b : H) * k := by group
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      ext ⟨k, hk⟩
      simp only [hρcoe, MulAut.one_apply]
      have := h1 k hk
      calc (b : H) * k * (b : H)⁻¹ = (k * (b : H)) * (b : H)⁻¹ := by rw [← this]
        _ = k := by group
  have h1 := Subgroup.relIndex_mul_card (H := ρ.ker) (K := B')
  rw [Subgroup.relIndex_ker, hker, card_subgroupOf_of_le' (hBo_le.trans hBK),
    card_subgroupOf_of_le' hBK] at h1
  rw [← h1, mul_comm]
  rfl

end Bbar

section Rest2

variable {H : Type} [Group H]

@[expose] def D4Unhandled2 (K B : Subgroup H) : Prop :=
  3 * Nat.card ↥(Bbar K B ⊓ innerAut ↥K) < Nat.card ↥(Bbar K B)

end Rest2

@[expose] def D4BigCoreRest2 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K B : Subgroup H),
    catalogIs ↥K isD4any → ¬ catalogIs ↥K S9.isD4two →
    (∀ k ∈ K, (∀ y ∈ K, y * k = k * y) → k = 1) → IsElemAbelian 3 B →
    B ≤ Subgroup.normalizer (K : Set H) →
    (∃ b ∈ B, ∃ hb : b ∈ Subgroup.normalizer (K : Set H), NotCentralOut (conjAut K b hb)) →
    D4RankCase K B → D4Unhandled2 K B → False

theorem d4BigCoreRest_of_rest2 (h : D4BigCoreRest2) : D4BigCoreRest := by
  classical
  intro H _ _ K B hK hn hKc hB hBK hout hcase hU
  refine h H K B hK hn hKc hB hBK hout hcase ?_
  set N : Subgroup H := Subgroup.normalizer (K : Set H) with hN
  set ρ : ↥N →* MulAut ↥K := conjHom K with hρ
  have hB'el : IsElemAbelian 3 (B.subgroupOf N) := hB.comap N.subtype_injective
  have hAel : IsElemAbelian 3 (Bbar K B) :=
    CFSG.LocalAnalysis.GLTheoremA.S9.l94t_isElemAbelian_map ρ hB'el
  obtain ⟨b, hb, hbN, hnc⟩ := hout
  have hαA : conjAut K b hbN ∈ Bbar K B :=
    Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 hb : (⟨b, hbN⟩ : ↥N) ∈ B.subgroupOf N)
  have hBopos : 0 < Nat.card (Bo K B) := Nat.card_pos
  have hcard := card_B_eq hBK
  rcases hU with h27 | ⟨h9, ⟨n', hn'2, hodd', hKn'⟩, T, hT2, hTne, hBT, hTK, hTnc⟩
  · obtain ⟨n, hn2, hKn⟩ := exists_isD4pow2 hK hn
    obtain ⟨K₀, _, _, _, hK₀, ⟨Φ⟩⟩ := exists_om8_of_isD4pow2 hn2 hKn
    haveI : IsCyclic (K₀ ≃+* K₀) := CFSG.RankThree.PartOne.KFOUT3.isCyclic_aut (by omega) hK₀
    have hcomm : ∀ σ τ : K₀ ≃+* K₀, σ * τ = τ * σ := fun σ τ =>
      (IsCyclic.commGroup (α := K₀ ≃+* K₀)).mul_comm σ τ
    have h9' := inf_inner_le_nine Φ hcomm hAel hαA hnc
    show 3 * Nat.card ↥(Bbar K B ⊓ innerAut ↥K) < Nat.card ↥(Bbar K B)
    rw [hcard] at h27
    by_contra hge
    push Not at hge
    nlinarith
  · by_contra hcon
    have hcon' : Nat.card ↥(Bbar K B) ≤ 3 * Nat.card ↥(Bbar K B ⊓ innerAut ↥K) := not_lt.1 hcon
    obtain ⟨K₀, _, _, _, hK₀, ⟨Φ⟩⟩ := exists_om8_of_isD4pow2 hn'2 hKn'
    set T' : Subgroup ↥N := T.subgroupOf N with hT'
    set Th : Subgroup (MulAut ↥K) := T'.map ρ with hTh
    have hT'2 : IsPGroup 2 T' := hT2.comap_subtype
    have hTh2 : IsPGroup 2 Th := hT'2.map ρ
    have hρcoe : ∀ (b : ↥N) (k : ↥K), ((ρ b k : ↥K) : H) = (b : H) * k * (b : H)⁻¹ := fun b k => rfl
    have hThne : Th ≠ ⊥ := by
      intro hbot
      obtain ⟨t, ht, htk⟩ := (SetLike.not_le_iff_exists.1 hTnc)
      obtain ⟨k, hk, hkt⟩ : ∃ k ∈ K, k * t ≠ t * k := by
        by_contra hh
        push Not at hh
        exact htk (Subgroup.mem_centralizer_iff.2 hh)
      have hmem : ρ ⟨t, hTK ht⟩ ∈ Th := Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.2 ht)
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hkt
      have h3 := congrArg (fun σ : MulAut ↥K => ((σ ⟨k, hk⟩ : ↥K) : H)) hmem
      simp only [hρcoe, MulAut.one_apply] at h3
      calc k * t = (t * k * t⁻¹) * t := by rw [h3]
        _ = t * k := by group
    have hBT' : B.subgroupOf N ≤ Subgroup.normalizer (T' : Set ↥N) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have h1 := Subgroup.mem_normalizer_iff.1 (hBT (Subgroup.mem_subgroupOf.1 hb)) (y : H)
      simp only [hT', Subgroup.mem_subgroupOf, SetLike.mem_coe, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1 ⊢
      exact h1
    have hnorm : Bbar K B ≤ Subgroup.normalizer (Th : Set (MulAut ↥K)) := fun σ hσ => by
      obtain ⟨b, hb, rfl⟩ := hσ
      exact Subgroup.le_normalizer_map ρ (Subgroup.mem_map_of_mem _ (hBT' hb))
    have h3 := inf_inner_le_three_odd Φ (by omega) hK₀ hodd' hAel hαA hnc hTh2 hThne hnorm
    rw [hcard] at h9
    have hBb : Nat.card ↥(Bbar K B) ≤ 9 := by omega
    nlinarith

end CFSG.LocalAnalysis.GLTheoremA.D4Y

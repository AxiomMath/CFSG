module

public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRecognizePieces
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotRows

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open scoped MatrixGroups

section Centre

variable {F : Type} [Field F]

theorem odd_card_units_of_card_eq_two_pow {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) :
    Odd (Nat.card Fˣ) := by
  rw [Nat.card_units, hF]
  obtain ⟨r, rfl⟩ : ∃ r, f = r + 1 := ⟨f - 1, by omega⟩
  refine ⟨2 ^ r - 1, ?_⟩
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [pow_succ]
  omega

theorem odd_card_center_specialLinear {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 ≤ f) (N : ℕ) :
    Odd (Nat.card (center SL(N, F))) := by
  rw [Nat.card_congr (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity
    (n := Fin N) (R := F)).toEquiv]
  exact Odd.of_dvd_nat (odd_card_units_of_card_eq_two_pow hF hf)
    (Subgroup.card_subgroup_dvd_card _)

theorem odd_card_center_of_surjective_specialLinear {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hf : 1 ≤ f) {m : ℕ} (hm : 2 ≤ m) {Y : Type*} [Group Y] {ψ : SL(m + 1, F) →* Y}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center SL(m + 1, F)) :
    Odd (Nat.card (center Y)) := by
  rw [CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F hm) hψ hker]
  exact Odd.of_dvd_nat (odd_card_center_specialLinear hF hf (m + 1)) ((center SL(m + 1, F)).card_map_dvd ψ)

end Centre

section Cover

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

@[expose] def SpGlobalCoverType (e : L ≃* StatedSp n K) (f : ℕ) (κ : Sp2mKind) : Prop :=
  CFSG.IsQuasisimple (spGlobal e) ∧ Odd (Nat.card (center (spGlobal e))) ∧
    Sp2mKindType (spGlobal e ⧸ center (spGlobal e)) n f κ

end Cover

@[expose] def SpKindCoverInput (κ : Sp2mKind) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (n f : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ n → Nat.card K = 2 ^ f →
    2 ≤ f → ∀ (e : L ≃* StatedSp n K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∀ k : Fin n, RootKindSp e t f k κ) → SpGlobalCoverType e f κ

section WeakCT

variable {G : Type} [Group G]

theorem exists_weakCT_of_subgroups {F : Type} [Field F] [Finite F] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (hf : 2 ≤ f) {r : ℕ} (hr : 3 ≤ r) {U : Fin r → Subgroup G}
    {G₀ : Subgroup G}
    (hcomm : ∀ i j : Fin r, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin r, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hgen : ⨆ i, U i = G₀) :
    ∃ ψ : SL(r + 1, F) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(r + 1, F) ∧
      CFSG.IsQuasisimple G₀ ∧ Odd (Nat.card (center G₀)) ∧
      LieModel (G₀ ⧸ center G₀) .PSL (r + 1) 2 f := by
  have hle : ∀ i, U i ≤ G₀ := fun i => hgen ▸ le_iSup U i
  have hUmap : ∀ i, ((U i).subgroupOf G₀).map G₀.subtype = U i := fun i => by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr (hle i)]
  have hcomm' : ∀ i j : Fin r, (i : ℕ) + 1 < j → ∀ x ∈ (U i).subgroupOf G₀,
      ∀ y ∈ (U j).subgroupOf G₀, x * y = y * x := by
    intro i j hij x hx y hy
    exact Subtype.ext (hcomm i j hij _ (mem_subgroupOf.1 hx) _ (mem_subgroupOf.1 hy))
  have hpair' : ∀ i j : Fin r, (j : ℕ) = i + 1 →
      ∃ W, LinearBlockStandardPair F W ((U i).subgroupOf G₀) ((U j).subgroupOf G₀) := by
    intro i j hj
    obtain ⟨W, θ, c, -, hker, hcase⟩ := hpair i j hj
    have htop : (B12 F).map (MulAut.conj c⁻¹).toMonoidHom ⊔
        (B23 F).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
      rw [← Subgroup.map_sup, CFSG.ClassicalInvolution.WeakCT.B12_sup_B23,
        ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 (MulAut.conj c⁻¹).surjective
    have hrange : θ.range = U i ⊔ U j := by
      rw [MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, sup_comm]
    have hθG₀ : ∀ A, θ A ∈ G₀ := fun A =>
      sup_le (hle i) (hle j) (hrange ▸ (⟨A, rfl⟩ : θ A ∈ θ.range))
    let θ' : SL(3, F) →* G₀ := θ.codRestrict G₀ hθG₀
    have hθ' : ∀ H : Subgroup SL(3, F), (H.map θ').map G₀.subtype = H.map θ := fun H => by
      rw [map_map]
      rfl
    refine ⟨θ'.range, θ', c, rfl, ?_, ?_⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hker
    · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine Or.inl ⟨?_, ?_⟩
        · apply map_injective G₀.subtype_injective
          rw [hθ', h1, hUmap]
        · apply map_injective G₀.subtype_injective
          rw [hθ', h2, hUmap]
      · refine Or.inr ⟨?_, ?_⟩
        · apply map_injective G₀.subtype_injective
          rw [hθ', h1, hUmap]
        · apply map_injective G₀.subtype_injective
          rw [hθ', h2, hUmap]
  have hgen' : ⨆ i, (U i).subgroupOf G₀ = ⊤ := by
    apply map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp only [hUmap]
    exact hgen
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨ψ, hsurj, hker, hqs, hmodel⟩ :=
    CFSG.ClassicalInvolution.WeakCT.weakCT_recognition_of_pairs F 2 f Nat.prime_two hF hq hr
      hcomm' hpair' hgen'
  exact ⟨ψ, hsurj, hker, hqs,
    odd_card_center_of_surjective_specialLinear hF (by omega) (by omega) hsurj hker, hmodel⟩

end WeakCT

section Nodes

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}

@[expose] def SpLinearNodeSystem (e : L ≃* StatedSp n K) (f r : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (U : Fin r → Subgroup G), Nat.card F = 2 ^ f ∧
    (∀ (j : Fin n) (i i' : Fin r), (i : ℕ) = j → (i' : ℕ) + j + 1 = r →
      pieceCore e ({j} : Finset (Fin n)) = U i ⊔ U i') ∧
    (∀ i j : Fin r, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x) ∧
    (∀ i j : Fin r, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F W (U i) (U j))

theorem iSup_nodes_eq_spGlobal {e : L ≃* StatedSp n K} {r : ℕ} (hnr : n ≤ r) (hrn : r ≤ 2 * n)
    {U : Fin r → Subgroup G}
    (hpiece : ∀ (j : Fin n) (i i' : Fin r), (i : ℕ) = j → (i' : ℕ) + j + 1 = r →
      pieceCore e ({j} : Finset (Fin n)) = U i ⊔ U i') :
    ⨆ i, U i = spGlobal e := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    by_cases hi : (i : ℕ) < n
    · have h1 := hpiece ⟨i, hi⟩ i ⟨r - 1 - i, by omega⟩ rfl (by simp; omega)
      exact le_sup_left.trans (h1.symm.le.trans (le_iSup (fun j : Fin n =>
        pieceCore e ({j} : Finset (Fin n))) ⟨i, hi⟩))
    · have h1 := hpiece ⟨r - 1 - i, by omega⟩ ⟨r - 1 - i, by omega⟩ i rfl (by simp; omega)
      exact le_sup_right.trans (h1.symm.le.trans (le_iSup (fun j : Fin n =>
        pieceCore e ({j} : Finset (Fin n))) ⟨r - 1 - i, by omega⟩))
  · refine iSup_le fun j => ?_
    rw [hpiece j ⟨j, by omega⟩ ⟨r - 1 - j, by omega⟩ rfl (by simp; omega)]
    exact sup_le (le_iSup U _) (le_iSup U _)

theorem spGlobalCoverType_of_nodeSystem {e : L ≃* StatedSp n K} {f : ℕ} (hf : 2 ≤ f)
    (hn : 2 ≤ n) {κ : Sp2mKind} {r : ℕ}
    (hκr : (κ = .linearEven ∧ r + 1 = 2 * n) ∨ (κ = .linearOdd ∧ r = 2 * n))
    (h : SpLinearNodeSystem e f r) : SpGlobalCoverType e f κ := by
  obtain ⟨F, _, _, U, hF, hpiece, hcomm, hpair⟩ := h
  have hnr : n ≤ r := by rcases hκr with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hrn : r ≤ 2 * n := by rcases hκr with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hr3 : 3 ≤ r := by rcases hκr with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨-, -, -, hqs, hodd, hmodel⟩ :=
    exists_weakCT_of_subgroups hF hf hr3 hcomm hpair (iSup_nodes_eq_spGlobal hnr hrn hpiece)
  refine ⟨hqs, hodd, ?_⟩
  rcases hκr with ⟨rfl, h⟩ | ⟨rfl, rfl⟩
  · change LieModel _ .PSL (2 * n) 2 f
    rw [← h]
    exact hmodel
  · exact hmodel

end Nodes

end CFSG.SeitzReduction.SymplecticPilot

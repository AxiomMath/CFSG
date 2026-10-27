module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614ExtDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJSetup
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64

open CFSG.Open Subgroup CFSG.Quasithin CFSG.HardMathSupport.Solomon
open CFSG.LocalAnalysis.RankThreeTheoremC

variable {A : Type} [Group A] [Finite A]

theorem pCoreOf_le_of_maxInv {B X S : Subgroup A} (hS : IsMaxTwoInvariantIn B X S)
    (hBX : B ≤ X) : pCoreOf 2 X ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hSX, hS2, hBS⟩, hmax⟩ := hS
  have hXO := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hinv : IsTwoInvariantIn B X (S ⊔ pCoreOf 2 X) :=
    ⟨sup_le hSX (CFSG.LieType.BorelTits.pCoreOf_le 2 X),
      IsPGroup.to_sup_of_normal_right' hS2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
        (hSX.trans hXO),
      B2F.le_normalizer_sup hBS (hBX.trans hXO)⟩
  rw [← hmax _ hinv le_sup_left]
  exact le_sup_right

theorem eq_or_eq_of_relIndex_le_two {O H S : Subgroup A} (hOH : O ≤ H) (hHS : H ≤ S)
    (h2 : O.relIndex S ≤ 2) : H = O ∨ H = S := by
  have h := relIndex_mul_relIndex O H S hOH hHS
  haveI : O.IsFiniteRelIndex H := isFiniteRelIndex_of_finiteIndex
  haveI : H.IsFiniteRelIndex S := isFiniteRelIndex_of_finiteIndex
  have h1 : O.relIndex H ≠ 0 := relIndex_ne_zero
  have h2' : H.relIndex S ≠ 0 := relIndex_ne_zero
  rcases (show O.relIndex H = 1 ∨ H.relIndex S = 1 by
    rcases Nat.lt_or_ge (O.relIndex H) 2 with h3 | h3
    · left; omega
    · right
      have : 2 * H.relIndex S ≤ O.relIndex H * H.relIndex S := Nat.mul_le_mul_right _ h3
      omega) with h4 | h4
  · left
    exact le_antisymm (relIndex_eq_one.mp h4) hOH
  · right
    exact le_antisymm hHS (relIndex_eq_one.mp h4)

section Module

theorem isElemAbelian_omegaOneCenterOf (O : Subgroup A) :
    IsElemAbelian 2 (omegaOneCenterOf O) :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ.zj_isElemAbelian_omegaOneCenter O

theorem le_normalizer_omegaOneCenterOf {X O : Subgroup A} (hXO : X ≤ normalizer (O : Set A)) :
    X ≤ normalizer (omegaOneCenterOf O : Set A) := by
  intro g hg
  rw [B2F.mem_normalizer_iff_cjSub_eq]
  have hO : cjSub g O = O := B2F.mem_normalizer_iff_cjSub_eq.mp (hXO hg)
  unfold cjSub at hO ⊢
  rw [omegaOneCenterOf_map_mulEquiv, hO]

theorem le_centralizer_omegaOneCenterOf (O : Subgroup A) :
    O ≤ centralizer (omegaOneCenterOf O : Set A) := by
  intro o ho
  rw [mem_centralizer_iff]
  intro v hv
  have hv' :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ.zj_omegaOneCenter_le_centerOf O hv
  exact (mem_centralizer_iff.mp hv'.2 o ho).symm

theorem omegaOneCenterOf_le_omegaOneCenterOf {S O X : Subgroup A} (hOS : O ≤ S) (hSX : S ≤ X)
    (hcent : X ⊓ centralizer (O : Set A) ≤ O) :
    omegaOneCenterOf S ≤ omegaOneCenterOf O := by
  refine (closure_le _).mpr fun x hx => ?_
  obtain ⟨⟨hxS, hxC⟩, hx2⟩ := hx
  have hxCO : x ∈ centralizer (O : Set A) :=
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_iff.mp hxC h (hOS hh)
  have hxO : x ∈ O := hcent ⟨hSX hxS, hxCO⟩
  exact subset_closure ⟨⟨hxO, hxCO⟩, hx2⟩

theorem le_omegaOneCenterOf {S V : Subgroup A} (hVS : V ≤ S) (hV : IsElemAbelian 2 V)
    (hSC : S ≤ centralizer (V : Set A)) : V ≤ omegaOneCenterOf S := by
  intro v hv
  refine subset_closure ⟨⟨hVS hv, ?_⟩, hV.2 v hv⟩
  exact mem_centralizer_iff.mpr fun s hs => (mem_centralizer_iff.mp (hSC hs) v hv).symm

end Module

theorem exists_offender {S O X K : Subgroup A} (hOS : O ≤ S)
    (hXO : X ≤ normalizer (O : Set A)) (hKX : K ≤ X)
    (hK : ¬ K ≤ normalizer (thompsonJ S : Set A)) :
    ∃ A₀ : Subgroup A, IsMaxElemAbelian S A₀ ∧ ¬ A₀ ≤ O := by
  by_contra h
  push Not at h
  apply hK
  have hJO : thompsonJ S ≤ O := iSup₂_le fun A₀ hA₀ => h A₀ hA₀
  have hJ : thompsonJ S = thompsonJ O := thompsonJ_eq_of_le hJO hOS
  intro g hg
  rw [B2F.mem_normalizer_iff_cjSub_eq, hJ]
  exact cjSub_thompsonJ (hXO (hKX hg))

section Transvection

@[expose] def commMap {W : Type} [CommGroup W] (τ : MulAut W) : W →* W where
  toFun v := τ v * v⁻¹
  map_one' := by simp
  map_mul' v w := by
    rw [map_mul, mul_inv_rev]
    simp only [mul_assoc, mul_comm, mul_left_comm]

theorem commMap_apply {W : Type} [CommGroup W] (τ : MulAut W) (v : W) :
    commMap τ v = τ v * v⁻¹ := rfl

theorem closure_range_eq {W : Type} [CommGroup W] (τ : MulAut W) :
    closure (Set.range fun v : W => τ v * v⁻¹) = (commMap τ).range := by
  show closure (Set.range (commMap τ)) = _
  rw [← MonoidHom.coe_range]
  exact closure_eq _

theorem card_commV_le_two {S A₀ W : Subgroup A} (hA₀ : IsMaxElemAbelian S A₀) {a : A}
    (haA : a ∈ A₀) (hW : IsElemAbelian 2 W) (hWS : W ≤ S) (haN : a ∈ normalizer (W : Set A))
    (hidx : (A₀ ⊓ centralizer (W : Set A)).relIndex A₀ ≤ 2) :
    Nat.card (closure (Set.range fun v : IntMod W hW => convI hW ⟨a, haN⟩ v * v⁻¹)) ≤ 2 := by
  rw [closure_range_eq]
  set δ := commMap (convI hW ⟨a, haN⟩)
  set A₁ := A₀ ⊓ centralizer (W : Set A) with hA₁
  have hcomm : ∀ x ∈ W, ∀ y ∈ A₁, x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.mp hy.2 x hx
  have hA₁e : IsElemAbelian 2 A₁ := B2F.isElemAbelian_mono inf_le_left hA₀.2.1
  have hsup : IsElemAbelian 2 (W ⊔ A₁) := B2F.isElemAbelian_sup_of_commute hW hA₁e hcomm
  have hle : Nat.card ↥(W ⊔ A₁) ≤ Nat.card A₀ :=
    hA₀.2.2 _ (sup_le hWS (inf_le_left.trans hA₀.1)) hsup
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  have hA₀A₁ : Nat.card A₀ ≤ 2 * Nat.card A₁ := by
    have h := relIndex_mul_card A₁ A₀
    rw [inf_of_le_left inf_le_left] at h
    rw [← h]
    exact Nat.mul_le_mul_right _ hidx
  have hWA : Nat.card ↥(W ⊓ A₁) ≤ Nat.card ↥(W ⊓ A₀) :=
    card_le_of_le (inf_le_inf_left W inf_le_left)
  have hker : Nat.card ↥(W ⊓ A₀) ≤ Nat.card δ.ker := by
    let f : ↥(W ⊓ A₀) → δ.ker := fun x => ⟨IntMod.mk hW ⟨x.1, x.2.1⟩, by
      rw [MonoidHom.mem_ker, commMap_apply, mul_inv_eq_one]
      apply IntMod.val_injective
      rw [convI_apply_val]
      change a * x.1 * a⁻¹ = x.1
      rw [B2F.isElemAbelian_comm hA₀.2.1 haA x.2.2, mul_inv_cancel_right]⟩
    refine Nat.card_le_card_of_injective f fun x y hxy => ?_
    have := congrArg (fun z : δ.ker => IntMod.val (z : IntMod W hW)) hxy
    exact Subtype.ext this
  have hpos1 : 0 < Nat.card A₁ := Nat.card_pos
  have hpos2 : 0 < Nat.card δ.ker := Nat.card_pos
  have h1 : Nat.card W * Nat.card A₁ ≤ (2 * Nat.card ↥(W ⊓ A₁)) * Nat.card A₁ := by
    calc Nat.card W * Nat.card A₁ = Nat.card ↥(W ⊔ A₁) * Nat.card ↥(W ⊓ A₁) := hcard.symm
      _ ≤ Nat.card A₀ * Nat.card ↥(W ⊓ A₁) := Nat.mul_le_mul_right _ hle
      _ ≤ (2 * Nat.card A₁) * Nat.card ↥(W ⊓ A₁) := Nat.mul_le_mul_right _ hA₀A₁
      _ = (2 * Nat.card ↥(W ⊓ A₁)) * Nat.card A₁ := by ring
  have h2 : Nat.card W ≤ 2 * Nat.card ↥(W ⊓ A₁) := Nat.le_of_mul_le_mul_right h1 hpos1
  have h3 := Subgroup.card_ker_mul_card_range δ
  have hW' : Nat.card (IntMod W hW) = Nat.card W := rfl
  rw [hW'] at h3
  have h4 : Nat.card δ.ker * Nat.card δ.range ≤ Nat.card δ.ker * 2 := by
    rw [h3]
    omega
  exact Nat.le_of_mul_le_mul_left h4 hpos2

theorem isTransvection_convI {W : Subgroup A} (hW : IsElemAbelian 2 W) {a : A}
    (haN : a ∈ normalizer (W : Set A)) (haC : a ∉ centralizer (W : Set A))
    (hle : Nat.card (closure (Set.range fun v : IntMod W hW => convI hW ⟨a, haN⟩ v * v⁻¹)) ≤
      2) :
    UniquenessMaximal.IsTransvection (convI hW ⟨a, haN⟩) := by
  have hne : convI hW ⟨a, haN⟩ ≠ 1 := fun h => haC ((convI_eq_one_iff hW _).mp h)
  refine ⟨hne, le_antisymm hle ?_⟩
  by_contra hlt
  push Not at hlt
  have hpos : 0 < Nat.card (closure (Set.range fun v : IntMod W hW =>
      convI hW ⟨a, haN⟩ v * v⁻¹)) := Nat.card_pos
  have h1 : Nat.card (closure (Set.range fun v : IntMod W hW =>
      convI hW ⟨a, haN⟩ v * v⁻¹)) = 1 := by omega
  rw [card_eq_one] at h1
  apply hne
  ext v
  have h2 : convI hW ⟨a, haN⟩ v * v⁻¹ ∈
      closure (Set.range fun v : IntMod W hW => convI hW ⟨a, haN⟩ v * v⁻¹) :=
    subset_closure ⟨v, rfl⟩
  rw [h1, mem_bot] at h2
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h2

end Transvection

theorem le_normalizer_of_conj {H U : Subgroup A} (h : ∀ g ∈ H, ∀ u ∈ U, g * u * g⁻¹ ∈ U) :
    H ≤ normalizer (U : Set A) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro u
  refine ⟨h g hg u, fun hu => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hu
  simpa [mul_assoc] using this

theorem le_normalizer_of_index_two {K O S : Subgroup A} {a : A} (hOS : O ≤ S)
    (hidx : O.relIndex S ≤ 2) (haS : a ∈ S) (haO : a ∉ O) (hKO : K ≤ normalizer (O : Set A))
    (hka : ∀ k ∈ K, k * a * k⁻¹ * a⁻¹ ∈ O) : K ≤ normalizer (S : Set A) := by
  haveI : O.IsFiniteRelIndex S := isFiniteRelIndex_of_finiteIndex
  have h2 : O.relIndex S = 2 := by
    have h0 : O.relIndex S ≠ 0 := relIndex_ne_zero
    have h1 : O.relIndex S ≠ 1 := fun h => haO (relIndex_eq_one.mp h haS)
    omega
  obtain ⟨b, hbS, hb⟩ := relIndex_eq_two_iff.mp h2
  have hab : a * b ∈ O := by
    rcases hb a haS with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h haO
  have hcoset : ∀ s ∈ S, s ∈ O ∨ s * a⁻¹ ∈ O := by
    intro s hs
    rcases hb s hs with ⟨h, -⟩ | ⟨h, -⟩
    · right
      have : s * a⁻¹ = (s * b) * (a * b)⁻¹ := by group
      rw [this]
      exact O.mul_mem h (O.inv_mem hab)
    · exact Or.inl h
  refine le_normalizer_of_conj fun k hk s hs => ?_
  rcases hcoset s hs with h | h
  · exact hOS ((mem_normalizer_iff.mp (hKO hk) s).mp h)
  · have e : k * s * k⁻¹ = (k * (s * a⁻¹) * k⁻¹) * (k * a * k⁻¹ * a⁻¹) * a := by group
    rw [e]
    exact S.mul_mem (hOS (O.mul_mem ((mem_normalizer_iff.mp (hKO hk) _).mp h) (hka k hk))) haS

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K64

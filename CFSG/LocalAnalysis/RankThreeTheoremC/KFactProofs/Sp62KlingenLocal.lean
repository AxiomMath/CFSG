module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Sp62Transport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalInSitu
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalTransport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A9LocalEmbed
public import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62AutElemRank
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameScan

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.Quasithin CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.PreuniquenessRankFour.Helpers

theorem eq_bot_of_inf_B0_eq_bot
    {W : Subgroup H6} (hWN : W ≤ N0) (hW : N0 ≤ Subgroup.normalizer (W : Set H6))
    (h : W ⊓ B0 = ⊥) : W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  have hcomm : ∀ b ∈ B0, w * b = b * w := by
    intro b hb
    have h1 : w * (b * w⁻¹ * b⁻¹) ∈ W :=
      mul_mem hw ((Subgroup.mem_normalizer_iff.1 (hW (B0_le_N0 hb)) w⁻¹).1 (inv_mem hw))
    have h2 : w * b * w⁻¹ * b⁻¹ ∈ B0 := by
      have := (Subgroup.mem_normalizer_iff.1 (N0_le_normalizer_B0 (hWN hw)) b).1 hb
      exact mul_mem this (inv_mem hb)
    have h3 : w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) := by group
    have h4 : w * b * w⁻¹ * b⁻¹ ∈ W ⊓ B0 := Subgroup.mem_inf.2 ⟨h3 ▸ h1, h2⟩
    rw [h, Subgroup.mem_bot] at h4
    exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h4)
  have hwB : w ∈ B0 := by
    refine centralizer_N0_le (Subgroup.mem_inf.2 ⟨hWN hw, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hcomm b hb).symm
  have : w ∈ W ⊓ B0 := Subgroup.mem_inf.2 ⟨hw, hwB⟩
  rwa [h] at this

theorem primeCore_N0
    {W : Subgroup H6} (hWN : W ≤ N0) (hW : N0 ≤ Subgroup.normalizer (W : Set H6))
    (hc : Nat.Coprime 3 (Nat.card W)) : W = ⊥ := by
  refine eq_bot_of_inf_B0_eq_bot hWN hW ?_
  have h1 : Nat.card (W ⊓ B0 : Subgroup H6) ∣ Nat.card W := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card (W ⊓ B0 : Subgroup H6) ∣ 3 ^ 3 :=
    card_B0 ▸ Subgroup.card_dvd_of_le inf_le_right
  have h3 : Nat.card (W ⊓ B0 : Subgroup H6) ∣ Nat.gcd (3 ^ 3) (Nat.card W) := Nat.dvd_gcd h2 h1
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left 3 hc)] at h3
  exact (Subgroup.card_eq_one).1 (Nat.dvd_one.1 h3)

theorem normal_dichotomy_N0
    {W : Subgroup H6} (hWN : W ≤ N0) (hW : N0 ≤ Subgroup.normalizer (W : Set H6)) :
    W = ⊥ ∨ B0 ≤ W := by
  by_cases h : W ⊓ B0 = ⊥
  · exact Or.inl (eq_bot_of_inf_B0_eq_bot hWN hW h)
  · right
    obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    exact irr_B0 W hW (Subgroup.mem_inf.1 w.2).1 (Subgroup.mem_inf.1 w.2).2
      (fun h' => hw1 (Subtype.ext h'))

theorem solvable_N0 :
    Group.IsSolvable N0 := by
  haveI : (B0.subgroupOf N0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer B0_le_N0).2 N0_le_normalizer_B0
  haveI : Group.IsSolvable B0 :=
    Group.isSolvable_of_comm fun a b => B0_elemAbelian.1.is_comm.comm a b
  haveI : Group.IsSolvable (B0.subgroupOf N0) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe B0_le_N0).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe B0_le_N0).injective
  haveI : Group.IsSolvable (N0 ⧸ B0.subgroupOf N0) := by
    refine CFSG.GroupTheory.groups_order_below_sixty_solvable ?_
    have h := Subgroup.card_mul_index (B0.subgroupOf N0)
    have hc : Nat.card (B0.subgroupOf N0) = Nat.card B0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe B0_le_N0).toEquiv
    rw [hc, card_B0, card_N0] at h
    have : (B0.subgroupOf N0).index = 48 := by
      have h' : (B0.subgroupOf N0).index * 27 = 48 * 27 := by
        rw [show 3 ^ 3 = 27 by norm_num] at h
        omega
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
    show (B0.subgroupOf N0).index < 60
    omega
  exact Group.isSolvable_of_subgroup_quotient (B0.subgroupOf N0)

theorem pRank_H6_le : CFSG.Open.pRank 3 (⊤ : Subgroup H6) ≤ 3 := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  rintro k ⟨E, -, hE, hk⟩
  have h := card_le_of_isElemAbelian_H6 hE
  rw [hk] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem a9InSitu_N0 :
    A9InSitu T0 B0 N0 where
  le_normalizer := N0_le_normalizer_B0
  primeCore := fun _ hWN hW hc => primeCore_N0 hWN hW hc
  normal_dichotomy := fun _ hWN hW => normal_dichotomy_N0 hWN hW
  centralizer_le := centralizer_N0_le
  pcore_le := fun _ hWN hW hp => pcore_N0_le _ hWN hW hp
  solvable := solvable_N0
  pRank_le := pRank_H6_le

theorem a3pInSitu_N0 :
    A3pInSitu 3 T0 B0 N0 where
  primeCore := fun _ hWN hW hc => primeCore_N0 hWN hW hc
  normal_dichotomy := fun _ hWN hW => normal_dichotomy_N0 hWN hW
  centralizer_le := fun x hx => B0_le_T0 (centralizer_N0_le hx)

theorem a3pInSitu_W0 :
    A3pInSitu 3 T0 B0 W0 where
  primeCore := fun W hWW hWN hc => by
    rcases dichotomy_W0 W hWW hWN with h | h
    · exact h
    · exfalso
      have h1 : 3 ∣ Nat.card V0 := by rw [card_V0]; norm_num
      have h2 := h1.trans (Subgroup.card_dvd_of_le h)
      have h3 := Nat.dvd_gcd (dvd_refl 3) h2
      rw [hc.gcd_eq_one] at h3
      omega
  normal_dichotomy := fun W hWW hWN =>
    (dichotomy_W0 W hWW hWN).imp_right fun h => B0_le_T0.trans (T0_le_V0.trans h)
  centralizer_le := fun x hx => B0_le_T0 (centralizer_B0_le (Subgroup.mem_inf.1 hx).2)

theorem sp62_map_ne_top {X Y : Type} [Group X] [Group Y] (f : X ≃* Y) {A : Subgroup X}
    (h : A ≠ ⊤) : A.map f.toMonoidHom ≠ ⊤ := by
  intro htop
  apply h
  apply Subgroup.map_injective (show Function.Injective f.toMonoidHom from f.injective)
  rw [htop, Subgroup.map_top_of_surjective _ f.surjective]

theorem N0_le_map_of_weakCore
    {Y : Type} [Group Y] [Finite Y] (Ψ : Y ≃* H6)
    {T : Sylow 3 Y} (hT : (T : Subgroup Y).map Ψ.toMonoidHom = T0) {Y₀ : Subgroup Y}
    (hW : GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀) : N0 ≤ Y₀.map Ψ.toMonoidHom := by
  have hmapsymm : ∀ A : Subgroup H6,
      (A.map Ψ.symm.toMonoidHom).map Ψ.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    ext x
    simp
  have hmap : ∀ A : Subgroup Y,
      (A.map Ψ.toMonoidHom).map Ψ.symm.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    ext x
    simp
  have hrank : 3 ≤ CFSG.Open.pRank 3 B0 :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl B0_elemAbelian card_B0
  have hN : Subgroup.normalizer (B0 : Set H6) ≤ GLBWeakCore 3 T0 :=
    normalizer_le_weakCore_of_commutative_overgroup 3 Nat.prime_three B0_le_T0 le_rfl
      B0_elemAbelian.1 (by omega) hrank
  have hcore : GLBWeakCore 3 T0 ≤ Y₀.map Ψ.toMonoidHom := by
    have h1 := map_glbWeakCore_le Nat.prime_three Ψ.symm.toMonoidHom Ψ.symm.injective T0
    rw [show T0.map Ψ.symm.toMonoidHom = (T : Subgroup Y) by rw [← hT, hmap]] at h1
    have h2 := Subgroup.map_mono (f := Ψ.toMonoidHom) (h1.trans hW)
    rwa [hmapsymm] at h2
  rw [← normalizer_B0_eq]
  exact hN.trans hcore

theorem map_eq_B0 {Y : Type}
    [Group Y] (Ψ : Y ≃* H6) {T B : Subgroup Y} (hT : T.map Ψ.toMonoidHom = T0) (hBT : B ≤ T)
    (hBe : IsElemAbelian 3 B) (hBc : Nat.card B = 3 ^ 3) : B.map Ψ.toMonoidHom = B0 :=
  eq_B0_of_elemAbelian (hT ▸ Subgroup.map_mono hBT) (elementary_abelian_map 3 hBe _)
    (by rw [Subgroup.card_map_of_injective Ψ.injective, hBc])

theorem kFactKlingenLocal_inSitu_sp62 :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (d : TauCeti.ValidLieTypeIndex),
      (p = 3 ∧ IsSpSixTwoIndex d) → ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y),
      K.Normal → Nonempty (K ≃* CatGroup d) →
      Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow p Y) (B Y₀ : Subgroup Y),
        B ≤ T → IsElemAbelian p B → Nat.card B = p ^ 3 →
        GLBWeakCore p (T : Subgroup Y) ≤ Y₀ → Y₀ ≠ ⊤ → A3pInSitu p (T : Subgroup Y) B Y₀ := by
  intro p _ hp2 d ⟨hp3, hd⟩ Y _ _ K hKn ⟨e⟩ hC T B Y₀ hBT hBe hBc hW hY₀
  subst hp3
  obtain ⟨Ψ, hT⟩ := exists_equiv_H6_sylow K d hd e hC T
  have hBΨ := map_eq_B0 Ψ hT hBT hBe hBc
  have hN := N0_le_map_of_weakCore Ψ hT hW
  rcases eq_N0_or_W0 hN (sp62_map_ne_top Ψ hY₀) with h | h
  · exact sp62_a3pInSitu_of_map Ψ.toMonoidHom Ψ.injective hT hBΨ h a3pInSitu_N0
  · exact sp62_a3pInSitu_of_map Ψ.toMonoidHom Ψ.injective hT hBΨ h a3pInSitu_W0

theorem kFactKlingenThreeLocal_sp62 :
    ∀ (d : TauCeti.ValidLieTypeIndex), IsSpSixTwoIndex d → ∀ (Y : Type) [Group Y] [Finite Y]
      [Fact (Nat.Prime 3)] (K : Subgroup Y), K.Normal → Nonempty (K ≃* CatGroup d) →
      Subgroup.centralizer (K : Set Y) = ⊥ → ∀ (T : Sylow 3 Y) (B Y₀ : Subgroup Y),
        B ≤ T → IsElemAbelian 3 B → Nat.card B = 3 ^ 3 → GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ →
        Y₀ ≠ ⊤ → HasKlingenData 3 T Y₀ →
        A9InSitu (T : Subgroup Y) B Y₀ ∧ Nat.card (T : Subgroup Y) = 3 ^ 4 ∧
          Nat.card (centerOf (T : Subgroup Y)) = 3 := by
  intro d hd Y _ _ _ K hKn ⟨e⟩ hC T B Y₀ hBT hBe hBc hW hY₀ hKl
  obtain ⟨Ψ, hT⟩ := exists_equiv_H6_sylow K d hd e hC T
  have hBΨ := map_eq_B0 Ψ hT hBT hBe hBc
  have hN := N0_le_map_of_weakCore Ψ hT hW
  have hK' : HasKlingenData 3 T0S (Y₀.map Ψ.toMonoidHom) :=
    hasKlingenData_of_mulEquiv Ψ (T := T) (T' := T0S) (by rw [coe_T0S, hT]) hKl
  rcases eq_N0_or_W0 hN (sp62_map_ne_top Ψ hY₀) with h | h
  · refine ⟨A9InSitu.of_map Ψ.toMonoidHom Ψ.injective hBΨ h a9InSitu_N0, ?_, ?_⟩
    · have h1 := card_T0
      rw [← hT, Subgroup.card_map_of_injective Ψ.injective] at h1
      exact h1
    · have hZ : (centerOf (T : Subgroup Y)).map Ψ.toMonoidHom =
          T0 ⊓ Subgroup.centralizer (T0 : Set H6) := by
        unfold centerOf
        rw [Subgroup.map_inf _ _ _ Ψ.injective, sp62_map_centralizer Ψ (T : Subgroup Y), hT]
      have h1 := card_inf_centralizer_T0
      rw [← hZ, Subgroup.card_map_of_injective Ψ.injective] at h1
      exact h1
  · exfalso
    rw [h] at hK'
    exact not_hasKlingenData_W0 hK'

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

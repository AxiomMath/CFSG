module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltSwaps
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModPow

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
  {g : ↥L →* alternatingGroup (Fin n)}

theorem swap_mul_swap_inv_eq {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (swap a b * swap b c)⁻¹ = swap b a * swap a c := by
  rw [mul_inv_rev, swap_inv, swap_inv, swap_mul_swap_swap_eq hab hbc hac]

namespace GNAltModData

variable (S : GNAltModData T L g)

theorem swapPair_eq_or_disjoint {a b a₀ b₀ : Fin n} (hab : a ≠ b)
    (hab₀ : a₀ ≠ b₀) (hsQ : swap a b ∈ S.Q) (hs₀Q : swap a₀ b₀ ∈ S.Q) :
    (a₀ ≠ a ∧ a₀ ≠ b ∧ b₀ ≠ a ∧ b₀ ≠ b) ∨ (a = a₀ ∧ b = b₀) ∨ (a = b₀ ∧ b = a₀) := by
  by_cases h1 : a₀ = a
  · subst h1
    have := S.eq_of_swap_mem_Q hab₀ hab hs₀Q hsQ
    exact Or.inr (Or.inl ⟨rfl, this.symm⟩)
  by_cases h2 : a₀ = b
  · subst h2
    have := S.eq_of_swap_mem_Q hab₀ hab.symm hs₀Q (by rwa [swap_comm])
    exact Or.inr (Or.inr ⟨this.symm, rfl⟩)
  by_cases h3 : b₀ = a
  · subst h3
    have := S.eq_of_swap_mem_Q hab₀.symm hab (by rwa [swap_comm]) hsQ
    exact Or.inr (Or.inr ⟨rfl, this.symm⟩)
  by_cases h4 : b₀ = b
  · subst h4
    have := S.eq_of_swap_mem_Q hab₀.symm hab.symm (by rwa [swap_comm]) (by rwa [swap_comm])
    exact Or.inr (Or.inl ⟨this.symm, rfl⟩)
  exact Or.inl ⟨h1, h2, h3, h4⟩

theorem three_element_transfer (hX : GNSetting X T) (hL : IsComponentOf L ⊤) (hn : 4 ≤ n)
    {c₀ : Fin n} (hc₀ : ∀ q ∈ S.Q, q c₀ = c₀)
    {a₀ b₀ : Fin n} (hab₀ : a₀ ≠ b₀) (hs₀ : swap a₀ b₀ ∈ S.J) {ℓ₀ : ↥L}
    (hgℓ₀ : (g ℓ₀ : Perm (Fin n)) = swap a₀ b₀ * swap b₀ c₀)
    {H : Subgroup (X ⧸ gnC T)}
    (hH : ∀ m ∈ Subgroup.normalizer (baum T : Set X), ∀ c ∈ H,
      toStar T m * c * (toStar T m)⁻¹ ∈ H)
    (h₀ : (ℓ₀ : X ⧸ gnC T) ∈ H) :
    ∀ a b : Fin n, a ≠ b → swap a b ∈ S.J → ∀ ℓ : ↥L,
      (g ℓ : Perm (Fin n)) = swap a b * swap b c₀ → (ℓ : X ⧸ gnC T) ∈ H := by
  classical
  intro a b hab hs ℓ hgℓ
  obtain ⟨hca₀, hcb₀⟩ := S.fixed_ne hab₀ hc₀ hs₀
  obtain ⟨hca, hcb⟩ := S.fixed_ne hab hc₀ hs
  have hs₀Q : swap a₀ b₀ ∈ S.Q := S.J_le_Q hs₀
  have hsQ : swap a b ∈ S.Q := S.J_le_Q hs
  rcases S.swapPair_eq_or_disjoint hab hab₀ hsQ hs₀Q with hdisj | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨ha₀a, ha₀b, hb₀a, hb₀b⟩ := hdisj
    have hγA : swap a₀ a * swap b₀ b ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap ha₀a, sign_swap hb₀b]
      decide
    obtain ⟨l, hl, hρl⟩ := S.exists_lift_of_mem_alternatingGroup hγA
    have hconj := S.swap_conj_mem_Q hab₀ hab ha₀a ha₀b hb₀a hb₀b hs₀Q hsQ
    have hJQ : ∀ j ∈ S.J, S.ρ ⟨l, Subgroup.le_normalizer hl⟩ * j *
        (S.ρ ⟨l, Subgroup.le_normalizer hl⟩)⁻¹ ∈ S.Q := by
      rw [hρl]
      exact S.conj_J_le_Q hconj
    obtain ⟨m, hm, hml⟩ := S.exists_mem_normalizer_baum_of_conj_J_le_Q hX hL hn hl hJQ
    have hxa : S.ρ ⟨l, Subgroup.le_normalizer hl⟩ a₀ = a := by
      rw [hρl, Perm.mul_apply, swap_apply_of_ne_of_ne hab₀ ha₀b, swap_apply_left]
    have hxb : S.ρ ⟨l, Subgroup.le_normalizer hl⟩ b₀ = b := by
      rw [hρl, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne ha₀b.symm hab.symm]
    have hxc : S.ρ ⟨l, Subgroup.le_normalizer hl⟩ c₀ = c₀ := by
      rw [hρl, Perm.mul_apply, swap_apply_of_ne_of_ne hcb₀ hcb, swap_apply_of_ne_of_ne hca₀ hca]
    have hxl : toStar T l * (ℓ₀ : X ⧸ gnC T) * (toStar T l)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hl ℓ₀.2) (L.inv_mem hl)
    have := S.conj_threeElement (x := ⟨l, Subgroup.le_normalizer hl⟩) hxc hxa hxb hgℓ₀ hgℓ hxl
    rw [← this, ← hml]
    exact hH m hm _ h₀
  · rw [h1, h2] at hgℓ
    have : ℓ = ℓ₀ := S.g_bij.1 (Subtype.ext (hgℓ.trans hgℓ₀.symm))
    rw [this]
    exact h₀
  · rw [h1, h2] at hgℓ
    have hinv : (g ℓ : Perm (Fin n)) = ((g ℓ₀)⁻¹ : alternatingGroup (Fin n)) := by
      rw [hgℓ, Subgroup.coe_inv, hgℓ₀]
      exact (swap_mul_swap_inv_eq hab₀ (Ne.symm hcb₀) (Ne.symm hca₀)).symm
    have : ℓ = ℓ₀⁻¹ := S.g_bij.1 (by rw [map_inv]; exact Subtype.ext hinv)
    rw [this]
    exact H.inv_mem h₀

include S in
theorem le_centralizer_or_normalizer (hX : GNSetting X T) (hL : IsComponentOf L ⊤)
    {T₁ T₂ : Subgroup X} (hP : IsC118Pair T T₁ T₂) (hn : 5 ≤ n) (hodd : Odd n)
    (hblock : ∀ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H → IsBlock2 H Kb →
      IsAltType Kb 3 → ¬ Kb ≤ gnC T → gnImg T Kb ≤ L → False) :
    L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      L ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
  classical
  obtain ⟨c₀, hc₀, -⟩ := S.existsUnique_fixed hodd
  have hall : S.JAllSwaps := S.jAllSwaps_of_gnSetting hX hL
  obtain ⟨T', ⟨s₀, hs₀⟩, hT's, -, hT'J⟩ := S.J_swaps
  have hs₀J : s₀ ∈ S.J := by
    have hJ : S.J = Subgroup.closure T' := hT'J
    rw [hJ]
    exact Subgroup.subset_closure hs₀
  obtain ⟨a₀, b₀, hab₀, rfl⟩ := hT's s₀ hs₀
  obtain ⟨hca, hcb⟩ := S.fixed_ne hab₀ hc₀ hs₀J
  have hτ : swap a₀ b₀ * swap b₀ c₀ ∈ alternatingGroup (Fin n) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab₀, sign_swap hcb.symm]
    decide
  obtain ⟨ℓ₀, hℓ₀⟩ := S.g_bij.2 ⟨swap a₀ b₀ * swap b₀ c₀, hτ⟩
  have hgℓ₀ : (g ℓ₀ : Perm (Fin n)) = swap a₀ b₀ * swap b₀ c₀ := congrArg Subtype.val hℓ₀
  obtain ⟨C, hCB, hCc, hCΩ, hT₁C, hmain⟩ := S.outcome_of_swap_sharp hX hP
  have hout := hmain hab₀ hc₀ hs₀J hgℓ₀
  obtain ⟨-, h1Z, h1ch, -, h2B, h2ch, -⟩ := id hP
  rcases hout with h | h | ⟨H, Kb, hH, hblk, hA3, hnC, himg⟩
  · left
    have hLH : L ≤ gnImg T (Subgroup.centralizer ((C ⊓ gnV T : Subgroup X) : Set X)) :=
      S.le_of_threeElements hn hall hc₀
        (S.three_element_transfer hX hL (by omega) hc₀ hab₀ hs₀J hgℓ₀
          (H := gnImg T (Subgroup.centralizer ((C ⊓ gnV T : Subgroup X) : Set X)))
          (fun m hm c hc => conj_mem_gnImg_centralizer
            (normalizer_baum_le_normalizer_inf_gnV hCB hCc hm) hc) h)
    exact hLH.trans (gnImg_centralizer_le_of_le hT₁C)
  · right
    exact S.le_of_threeElements hn hall hc₀
        (S.three_element_transfer hX hL (by omega) hc₀ hab₀ hs₀J hgℓ₀
          (H := gnImg T (Subgroup.normalizer (T₂ : Set X)))
          (fun m hm c hc => conj_mem_gnImg_normalizer
            (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2ch hm) hc) h)
  · exact (hblock H Kb hH hblk hA3 hnC (himg ▸ Subgroup.zpowers_le.2 ℓ₀.2)).elim

end GNAltModData

theorem false_of_gnYComponent_odd (hX : GNSetting X T) {T₁ T₂ : Subgroup X}
    (hP : IsC118Pair T T₁ T₂) {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ L) {n : ℕ}
    (hn9 : 9 ≤ n) (hodd : Odd n) (e : ↥L ≃* alternatingGroup (Fin n))
    (hlayer : GNNaturalOnLayer T L n)
    (hM2 : gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (hblock : ∀ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H → IsBlock2 H Kb →
      IsAltType Kb 3 → ¬ Kb ≤ gnC T → gnImg T Kb ≤ L → False) : False := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  obtain ⟨g, ⟨S⟩⟩ := exists_gnAltModData_of_layer hX hY.1 hJ hM2 hn9 hodd e hlayer
  rcases S.le_centralizer_or_normalizer hX hY.1 hP (by omega) hodd hblock with h | h
  · exact hY.2.1 h
  · exact hY.2.2 h

theorem altOddCoverRest_of_inputs (hlayer : GNLayerHolds) (hM2 : GNBaumNormalizes)
    (hBL : GNBlockLift) : AltOddCoverRest := by
  intro X _ _ T hX _ T₁ T₂ hP Ls hY n hn hodd _ he
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  have hn9 : 9 ≤ n := by omega
  have hZ : Subgroup.center ↥Ls = ⊥ :=
    altOddCentreTrivial ↥Ls hY.1.2.2 (not_two_dvd_card_center hX hY.1) n hn9 he
  let e : ↥Ls ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans he.some
  have hl := hlayer X T hX Ls hY.1 hJ n hn9 hodd ⟨e⟩
  exact false_of_gnYComponent_odd hX hP hY hn9 hodd e hl
    (hM2 X T hX Ls hY.1 hJ n hn9 hodd ⟨e⟩)
    (hBL X T hX Ls hY.1 hJ n hn9 hodd ⟨e⟩ hl)

theorem altEven_of_inputs (hlayer : GNLayerHolds) (hM2 : GNBaumNormalizes) (hBL : GNBlockLift) :
    GNInputRed.AltEven :=
  altEven_of_altOddCover
    (altOddCover_of_split (altOddCoverPow_of_inputs hlayer hM2 hBL)
      (altOddCoverRest_of_inputs hlayer hM2 hBL))

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15


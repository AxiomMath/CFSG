module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltModPair
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.Quasithin.EmptyFaithful.S1412

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.RankThree.PartTwo
open Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)} {n : ℕ}
  {g : ↥L →* alternatingGroup (Fin n)}

@[expose] def GNNaturalOnLayer (T : Subgroup X) (L : Subgroup (X ⧸ gnC T)) (n : ℕ) : Prop :=
  ∃ (g : ↥L →* alternatingGroup (Fin n)) (W : Subgroup X)
    (π : ↥⁅W, gnPre T L⁆ →* Multiplicative (altHeart n)),
    Function.Surjective g ∧ W ≤ gnV T ∧ omegaOneCenterOf T ≤ W ∧
    (∀ k ∈ gnPre T L, ∀ w ∈ W, k * w * k⁻¹ ∈ W) ∧
    (∀ u : ↥⁅W, gnPre T L⁆, π u = 1 → ∀ k ∈ gnPre T L, (k : X) * u * (k : X)⁻¹ = u) ∧
    (∀ (l : X) (hl : toStar T l ∈ L) (u u' : ↥⁅W, gnPre T L⁆),
      (u' : X) = l * u * l⁻¹ → ∀ x : evenWeight n,
        Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π u') = (QuotientAddGroup.mk (evenWeightPerm
          (g ⟨toStar T l, hl⟩ : Equiv.Perm (Fin n)) x) : altHeart n)) ∧
    ⁅gnV T, gnPre T L⁆ = ⁅W, gnPre T L⁆

theorem exists_gnAltModData_of_layer (hX : GNSetting X T) {L : Subgroup (X ⧸ gnC T)}
    (hL : IsComponentOf L ⊤) (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (hM2 : gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    {n : ℕ} (hn9 : 9 ≤ n) (hodd : Odd n) (e : ↥L ≃* alternatingGroup (Fin n))
    (hlayer : GNNaturalOnLayer T L n) :
    ∃ g : ↥L →* alternatingGroup (Fin n), Nonempty (GNAltModData T L g) := by
  obtain ⟨g, W, π, hg, hWV, -, hWK, hπk, hπi, hVW⟩ := hlayer
  exact ⟨g, nonempty_gnAltModData hX hL hJ hM2 hn9 hodd e g hg W hWV hWK π hπk hπi hVW⟩

theorem GNAltModData.le_centralizer_or_normalizer_of_two_pow_succ (S : GNAltModData T L g)
    (hX : GNSetting X T) {T₁ T₂ : Subgroup X} (hP : IsC118Pair T T₁ T₂) {m : ℕ} (hm : 2 ≤ m)
    (hn : n = 2 ^ m + 1)
    (hblock : ∀ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H → IsBlock2 H Kb →
      IsAltType Kb 3 → ¬ Kb ≤ gnC T → gnImg T Kb ≤ L → False) :
    L ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      L ≤ gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
  subst hn
  classical
  have hodd : Odd (2 ^ m + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hn5 : 5 ≤ 2 ^ m + 1 := by
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨c₀, hc₀, -⟩ := S.existsUnique_fixed hodd
  have hall : S.JAllSwaps := S.jAllSwaps_of_two_pow_succ (by omega) rfl
  obtain ⟨T', ⟨s₀, hs₀⟩, hT's, -, hT'J⟩ := S.J_swaps
  have hs₀J : s₀ ∈ S.J := by
    have hJ : S.J = Subgroup.closure T' := hT'J
    rw [hJ]
    exact Subgroup.subset_closure hs₀
  obtain ⟨a₀, b₀, hab₀, rfl⟩ := hT's s₀ hs₀
  obtain ⟨hca, hcb⟩ := S.fixed_ne hab₀ hc₀ hs₀J
  have hτ : swap a₀ b₀ * swap b₀ c₀ ∈ alternatingGroup (Fin (2 ^ m + 1)) := by
    rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hab₀, sign_swap hcb.symm]
    decide
  obtain ⟨ℓ₀, hℓ₀⟩ := S.g_bij.2 ⟨swap a₀ b₀ * swap b₀ c₀, hτ⟩
  have hgℓ₀ : (g ℓ₀ : Perm (Fin (2 ^ m + 1))) = swap a₀ b₀ * swap b₀ c₀ :=
    congrArg Subtype.val hℓ₀
  have hout := S.outcome_of_swap hX hP hab₀ hc₀ hs₀J hgℓ₀
  obtain ⟨-, h1Z, h1ch, -, h2B, h2ch, -⟩ := id hP
  have hT₁T : T₁ ≤ T := h1Z.trans (C1GN.omegaOneCenterOf_le_self T)
  have hT₁ : ∀ x ∈ T, x ∈ Subgroup.normalizer (T₁ : Set X) := fun x hx =>
    normalizer_le_normalizer_of_characteristic_subgroupOf hT₁T h1ch (Subgroup.le_normalizer hx)
  have hT₂ : ∀ x ∈ T, x ∈ Subgroup.normalizer (T₂ : Set X) := fun x hx =>
    normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2ch
      (normalizer_le_normalizer_of_characteristic_subgroupOf inf_le_left (C1GN.characteristic_baum T)
        (Subgroup.le_normalizer hx))
  have hconj : ∀ a b : Fin (2 ^ m + 1), a ≠ b → swap a b ∈ S.J → ∀ ℓ : ↥L,
      (g ℓ : Perm (Fin (2 ^ m + 1))) = swap a b * swap b c₀ →
      ∃ x ∈ T, toStar T x * (ℓ₀ : X ⧸ gnC T) * (toStar T x)⁻¹ = (ℓ : X ⧸ gnC T) := by
    intro a b hab hs ℓ hℓ
    obtain ⟨t, htQ, hta, htb⟩ := exists_apply_swap_eq_of_sylowTwo_two_pow_succ (by omega)
      S.sylow.1 S.sylow.2 hab₀ hab (S.J_le_Q hs₀J) (S.J_le_Q hs)
    obtain ⟨x, hx, rfl⟩ := htQ
    have hxT : (x : X) ∈ T := (Subgroup.mem_subgroupOf.1 hx).1
    have hxc : S.ρ x c₀ = c₀ := hc₀ _ ⟨x, hx, rfl⟩
    have hxl : toStar T x * (ℓ₀ : X ⧸ gnC T) * (toStar T x)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (mem_normalizer_gnPre_iff.1 x.2) ℓ₀).1 ℓ₀.2
    exact ⟨x, hxT, S.conj_threeElement hxc hta htb hgℓ₀ hℓ hxl⟩
  rcases hout with h | h | ⟨H, Kb, hH, hblk, hA3, hnC, himg⟩
  · left
    refine S.le_of_threeElements hn5 hall hc₀ fun a b hab hs ℓ hℓ => ?_
    obtain ⟨x, hxT, hxe⟩ := hconj a b hab hs ℓ hℓ
    rw [← hxe]
    exact conj_mem_gnImg_centralizer (hT₁ x hxT) h
  · right
    refine S.le_of_threeElements hn5 hall hc₀ fun a b hab hs ℓ hℓ => ?_
    obtain ⟨x, hxT, hxe⟩ := hconj a b hab hs ℓ hℓ
    rw [← hxe]
    exact conj_mem_gnImg_normalizer (hT₂ x hxT) h
  · exact (hblock H Kb hH hblk hA3 hnC (himg ▸ Subgroup.zpowers_le.2 ℓ₀.2)).elim

theorem GNAltModData.false_of_two_pow_succ (S : GNAltModData T L g) (hX : GNSetting X T)
    {T₁ T₂ : Subgroup X} (hP : IsC118Pair T T₁ T₂) (hY : GNYComponent T T₁ T₂ L) {m : ℕ}
    (hm : 2 ≤ m) (hn : n = 2 ^ m + 1)
    (hblock : ∀ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H → IsBlock2 H Kb →
      IsAltType Kb 3 → ¬ Kb ≤ gnC T → gnImg T Kb ≤ L → False) : False := by
  rcases S.le_centralizer_or_normalizer_of_two_pow_succ hX hP hm hn hblock with h | h
  · exact hY.2.1 h
  · exact hY.2.2 h

theorem false_of_gnYComponent_two_pow_succ (hX : GNSetting X T) {T₁ T₂ : Subgroup X}
    (hP : IsC118Pair T T₁ T₂) {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ L) {m : ℕ}
    (hm : 3 ≤ m) (e : ↥L ≃* alternatingGroup (Fin (2 ^ m + 1)))
    (hlayer : GNNaturalOnLayer T L (2 ^ m + 1))
    (hM2 : gnImg T (baum T) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)))
    (hblock : ∀ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H → IsBlock2 H Kb →
      IsAltType Kb 3 → ¬ Kb ≤ gnC T → gnImg T Kb ≤ L → False) : False := by
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := id hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  have hn9 : 9 ≤ 2 ^ m + 1 := by
    have : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hodd : Odd (2 ^ m + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  obtain ⟨g, ⟨S⟩⟩ := exists_gnAltModData_of_layer hX hY.1 hJ hM2 hn9 hodd e hlayer
  exact S.false_of_two_pow_succ hX hP hY (by omega) rfl hblock

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

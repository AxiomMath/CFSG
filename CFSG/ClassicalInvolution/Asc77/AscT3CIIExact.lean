module

public import CFSG.ClassicalInvolution.Asc77.AscT3CIISetup

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Exact

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem exists_equiv_sl2_of_exact (hΩ : HypOmegaMod p f Ω) (hex : ExactMembers Ω) {L : Subgroup G}
    (hL : L ∈ Ω) : Nonempty (L ≃* SL(2, GaloisField p f)) := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  exact hz.nonempty_equiv_sl2 (hex L hL)

omit [Finite G] in
theorem odd_natCard_galoisField (hp : p ≠ 2) (hq : 5 ≤ p ^ f) :
    Odd (Nat.card (GaloisField p f)) := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  rw [GaloisField.card p f hf]
  rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
  · exact absurd h hp
  · exact h.pow

theorem commute_of_twin_exact (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hex : ExactMembers Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω) (hK' : K' ∈ Ω)
    (hne : K' ≠ K) (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) :
    ∀ k ∈ K, ∀ k' ∈ K', k * k' = k' * k := by
  have h1 := Sec6Gen.comm_le_oddCore_of_twin (hypOmegaGen_of_mod hp hq hΩ) hK hK' hne.symm hz hz'
  rw [oddCoreOf_eq_bot_of_exact hex hK, bot_inf_eq, le_bot_iff] at h1
  intro k hk k' hk'
  have h2 : ⁅k, k'⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hk hk'
  rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

end Exact

section Graph

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem aviol_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} {zK zJ : G}
    (h : AViol Ω K J zK zJ) (g : G) :
    AViol Ω (conjSub g K) (conjSub g J) (g * zK * g⁻¹) (g * zJ * g⁻¹) where
  star := omegaStarNbr_conj hΩ h.star g
  not_nbr := fun hn => h.not_nbr (by
    have := omegaNbr_conj hΩ hn g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this)
  hzK := h.hzK.conj g
  hzJ := h.hzJ.conj g
  no_conj := by
    intro g' hg' hcon
    rw [← conjSub_pairNormalizers', mem_conjSub_iff] at hg'
    apply h.no_conj (g⁻¹ * g' * g) hg'
    rw [conjSub_mul, conjSub_mul, hcon, conjSub_inv_conjSub]

theorem aGraphAdj_conj' (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : aGraphAdj Ω K J) (g : G) :
    aGraphAdj Ω (conjSub g K) (conjSub g J) := by
  obtain ⟨hJ, h | h | ⟨ht, hne⟩⟩ := h
  · obtain ⟨zK, zJ, hv⟩ := h
    exact ⟨hΩ g J hJ, Or.inl ⟨_, _, aviol_conj hΩ hv g⟩⟩
  · obtain ⟨zK, zJ, hv⟩ := h
    exact ⟨hΩ g J hJ, Or.inr (Or.inl ⟨_, _, aviol_conj hΩ hv g⟩)⟩
  · exact ⟨hΩ g J hJ, Or.inr (Or.inr ⟨twinSet_conj hΩ ht g, fun e => hne ((conjSub_inj g).mp e)⟩)⟩

end Graph

section Symm

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem aviol_symm (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {K J : Subgroup G}
    {zK zJ : G} (hK : K ∈ Ω) (h : AViol Ω K J zK zJ) : AViol Ω J K zJ zK where
  star := omegaStarNbr_symm (l6_2 p f) hp hq hΩ hK h.mem h.star
  not_nbr := fun hn => h.not_nbr (omegaNbr_symm (l6_2 p f) hp hq hΩ h.mem hK hn)
  hzK := h.hzJ
  hzJ := h.hzK
  no_conj := by
    intro g hg hcon
    have hg' : g ∈ pairNormalizers K J zK zJ := by
      unfold pairNormalizers at hg ⊢
      rw [Set.pair_comm, sup_comm]
      exact hg
    apply h.no_conj g⁻¹ ((pairNormalizers K J zK zJ).inv_mem hg')
    rw [← hcon, conjSub_inv_conjSub]

theorem t_mem_sup_of_aviol (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K₁ K₂ J₂ : Subgroup G} {z t₂ : G} (hK₁ : K₁ ∈ Ω) (h : AViol Ω K₁ J₂ z t₂)
    (htw : twinSet Ω K₁ = {K₁, K₂}) : t₂ ∈ K₁ ⊔ K₂ := by
  obtain ⟨v, Ks, hVU, hVJ, -, hKs, htw', hvv⟩ := exists_hexagon_data hp hq hΩ hK₁ h.mem h.hzK
    h.hzJ h.star h.not_nbr h.no_conj
  have hKsK₂ : Ks = K₂ := by
    have hm : Ks ∈ twinSet Ω K₁ := by rw [htw']; exact Or.inr rfl
    rw [htw] at hm
    rcases hm with h1 | h1
    · exact absurd h1 hKs
    · exact h1
  subst hKsK₂
  have hV2 : IsPGroup 2 (Subgroup.zpowers v) := hΩ.isPGroup_of_mem_USet hp hVU
  obtain ⟨-, -, -, -, -, -, hVc, -, h4V⟩ := hΩ.exists_data_of_mem_USet hp hVU
  have htV : t₂ ∈ Subgroup.zpowers v := mem_of_isPGroup h.hzJ hVJ hV2 (by omega)
  obtain ⟨w, hw, hww⟩ := exists_sq_eq_of_cyclic h.hzJ hVJ hVc hV2 h4V
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hww, ← (Commute.refl v).mul_zpow]
  exact Subgroup.zpow_mem _ hvv k

end Symm

end CFSG.ClassicalInvolution.Asc77.T3CII

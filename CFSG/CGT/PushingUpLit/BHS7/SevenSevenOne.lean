module

public import CFSG.CGT.PushingUpLit.BHS7.SubnormalJ
public import CFSG.CGT.PushingUpLit.BHS6.SixTwelve
public import CFSG.CGT.PushingUpLit.BHS7.BlockV
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem conjSub_injective (g : Γ) {X Y : Subgroup Γ} (h : A1b.conjSub g X = A1b.conjSub g Y) :
    X = Y := by
  have := congrArg (A1b.conjSub g⁻¹) h
  rwa [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one, ← A1b.conjSub_mul, inv_mul_cancel,
    A1b.conjSub_one] at this

variable [Finite Γ]

theorem blocks_commute_of_subnormal {G T₁ T₂ U K K' : Subgroup Γ} (hU : CharTwo U)
    (hK : IsBTBlock G T₁ K) (hK' : IsBTBlock G T₂ K') (hKs : IsSubnormal K U)
    (hK's : IsSubnormal K' U) (hne : K ≠ K') : ⁅K, K'⁆ = ⊥ := by
  have hKU : K ≤ U := A3.subnormal_le hKs
  have hK'U : K' ≤ U := A3.subnormal_le hK's
  have hKs' := isSubnormal_subgroupOf_of_open hKs
  have hK's' := isSubnormal_subgroupOf_of_open hK's
  have hKchar : CharTwo K := CharTwo.of_isSubnormal hU hKU hKs'
  have hK'char : CharTwo K' := CharTwo.of_isSubnormal hU hK'U hK's'
  have hKX : InClassX ↥K := Glue.inClassX_of_isBTBlock hK hKchar
  have hK'X : InClassX ↥K' := Glue.inClassX_of_isBTBlock hK' hK'char
  exact distinct_blocks_commute_of_isBlockOfInX
    (EscapingLocal.isCharacteristicP_of_charTwo hU) ⟨hKU, hKs', hKX⟩ ⟨hK'U, hK's', hK'X⟩ hne

theorem baum_le_normalizer_of_subnormal_sub {G T T₀ U K : Subgroup Γ} (hG : CharTwo G)
    (hT : IsSylowOf 2 T G) (hT₀ : IsSylowOf 2 T₀ G) (hK : IsBTBlock G T₀ K) (hU : CharTwo U)
    (hBU : baum T ≤ U) (hsub : IsSubnormal K U) : baum T ≤ Subgroup.normalizer (K : Set Γ) := by
  have hJU : thompsonJ T ≤ U := (B6.thompsonJ_le_baum T).trans hBU
  have hJ : thompsonJ T ≤ Subgroup.normalizer (K : Set Γ) :=
    thompsonJ_le_normalizer_of_subnormal_sub hG hT₀ hK hsub hT hJU
  obtain ⟨w, hwW, hwK, hwJ⟩ := exists_fixed_noncentral hG hT₀ hK hT hJ
  intro b hb
  have hbT : b ∈ T := hb.1
  have hbG : b ∈ G := hT.1 hbT
  have hbU : b ∈ U := hBU hb
  have hwb : w * b = b * w := Subgroup.mem_centralizer_iff.mp hb.2 w hwJ
  have hK'sub : IsSubnormal (A1b.conjSub b K) U := isSubnormal_conjSub hbU hsub
  have hK'b : IsBTBlock G (A1b.conjSub b T₀) (A1b.conjSub b K) := by
    have := isBTBlock_conj b hK
    rwa [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hbG)] at this
  by_cases hKK : A1b.conjSub b K = K
  · exact BHS.mem_normalizer_of_conjSub_eq hKK
  · exfalso
    have hcomm : ⁅K, A1b.conjSub b K⁆ = ⊥ :=
      blocks_commute_of_subnormal hU hK hK'b hsub hK'sub (Ne.symm hKK)
    have hwK' : w ∈ A1b.conjSub b K := by
      rw [A1b.mem_conjSub_iff]
      have : b⁻¹ * w * b = w := by
        calc b⁻¹ * w * b = b⁻¹ * (w * b) := by group
          _ = b⁻¹ * (b * w) := by rw [hwb]
          _ = w := by group
      rw [this]
      exact CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K hwW
    apply hwK
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := Subgroup.commutator_mem_commutator hk hwK'
    rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this

theorem sigma_mem_bStarT {G T E U K : Subgroup Γ} (h : MinCex G T) (hE : E ∈ bStarT G T)
    (hUG : U < G) (hBU : baum T ≤ U) (hEU : E ≤ U)
    (hKconj : ∃ g ∈ G, K = A1b.conjSub g E) (hsub : IsSubnormal K U) : K ∈ bStarT G T := by
  obtain ⟨g, hg, rfl⟩ := hKconj
  have hT : IsSylowTwoOf T G := h.sylow
  have hTS : IsSylowOf 2 T G := h.sylow
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  have hUC : ¬ U ≤ cStarIn G T := fun hl => hE.2 (hEU.trans hl)
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBU
  obtain ⟨hUchar, -, -⟩ := seven_three h hT ⟨hUG, hBU, hUC⟩ hS
  have hTg : IsSylowTwoOf (A1b.conjSub g T) G := isSylowTwoOf_conjSub_of_mem hT hg
  have hTgS : IsSylowOf 2 (A1b.conjSub g T) G := hTg
  have hKb : IsBTBlock G (A1b.conjSub g T) (A1b.conjSub g E) := by
    have := isBTBlock_conj g hE.1.2
    rwa [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at this
  have hKmax : A1b.conjSub g E ∈ btBlocksMax G T := conjSub_mem_btBlocksMax hE.1.1 hg
  have hBN : baum T ≤ Subgroup.normalizer ((A1b.conjSub g E : Subgroup Γ) : Set Γ) :=
    baum_le_normalizer_of_subnormal_sub h.charTwo hTS hTgS hKb hUchar hBU hsub
  obtain ⟨n, hn, hnB⟩ := exists_conj_baum_of_le_of_le (N := G ⊓ Subgroup.normalizer
      ((A1b.conjSub g E : Subgroup Γ) : Set Γ)) hT hTg inf_le_left
    (le_inf ((inf_le_left : baum T ≤ T).trans hT.1) hBN)
    (le_inf ((inf_le_left : baum (A1b.conjSub g T) ≤ _).trans hTg.1)
      (baum_le_normalizer_of_isBTBlock hKb))
  have hnG : n ∈ G := hn.1
  have hnK : n ∈ Subgroup.normalizer ((A1b.conjSub g E : Subgroup Γ) : Set Γ) := hn.2
  have hnKeq : A1b.conjSub n (A1b.conjSub g E) = A1b.conjSub g E :=
    BHS.conjSub_eq_of_mem_normalizer hnK
  have hcomm : ⁅A1b.conjSub g E, baum T⁆ = A1b.conjSub g E := by
    have h1 : ⁅A1b.conjSub g E, baum (A1b.conjSub g T)⁆ = A1b.conjSub g E := hKb.commutator
    rw [hnB] at h1
    have h3 : ⁅A1b.conjSub n (A1b.conjSub g E), A1b.conjSub n (baum T)⁆ =
        A1b.conjSub n (A1b.conjSub g E) := by rw [hnKeq]; exact h1
    rw [commutator_conjSub] at h3
    exact conjSub_injective n h3
  have hKC : ¬ A1b.conjSub g E ≤ cStarIn G T := by
    intro hKC
    have hT''S : IsSylowTwoOf (A1b.conjSub n⁻¹ (A1b.conjSub g T)) G :=
      isSylowTwoOf_conjSub_of_mem hTg (G.inv_mem hnG)
    have hbT'' : baum (A1b.conjSub n⁻¹ (A1b.conjSub g T)) = baum T := by
      rw [baum_conjSub, hnB, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
    have hcs : cStarIn G (A1b.conjSub n⁻¹ (A1b.conjSub g T)) = cStarIn G T :=
      cStarIn_eq_of_baum_eq hT hT''S hbT'' hb0
    have h1 : cStarIn G (A1b.conjSub n⁻¹ (A1b.conjSub g T)) =
        A1b.conjSub n⁻¹ (A1b.conjSub g (cStarIn G T)) := by
      have e1 := cStarIn_conjSub n⁻¹ G (A1b.conjSub g T)
      rw [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer (G.inv_mem hnG))] at e1
      have e2 := cStarIn_conjSub g G T
      rw [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg)] at e2
      rw [e1, e2]
    rw [← hcs, h1] at hKC
    have h2 := A1b.conjSub_mono n hKC
    rw [hnKeq, ← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at h2
    have h3 := A1b.conjSub_mono g⁻¹ h2
    rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one, ← A1b.conjSub_mul, inv_mul_cancel,
      A1b.conjSub_one] at h3
    exact hE.2 h3
  have hKT : IsBTBlock G T (A1b.conjSub g E) :=
    { le := hKb.le
      residual := hKb.residual
      commutator := hcomm
      perfect := hKb.perfect
      elemAbelian := hKb.elemAbelian
      nonCentral := by
        intro h0
        apply hKC
        refine le_trans (le_inf hKb.le ?_) (centralizer_le_cStarIn G T)
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        have h1 : ⁅e, z⁆ ∈ (⁅A1b.conjSub g E, omegaOneCenterOf T⁆ : Subgroup Γ) :=
          Subgroup.commutator_mem_commutator he hz
        rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
      type := hKb.type }
  exact ⟨⟨hKmax, hKT⟩, hKC⟩

end CFSG.CGT.PushingUpLit.BHS7

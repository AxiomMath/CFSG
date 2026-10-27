module

public import CFSG.CGT.PushingUpLit.BHS7.SevenSevenOne
public import CFSG.CGT.PushingUpLit.BHS7.Pending
public import CFSG.CGT.PushingUpLit.BHS7.ClaimA

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def sigmaSet (G E U : Subgroup Γ) : Set (Subgroup Γ) :=
  {K | (∃ g ∈ G, K = A1b.conjSub g E) ∧ IsSubnormal K U}

@[expose] def sigmaJoin (G E U : Subgroup Γ) : Subgroup Γ := ⨆ K ∈ sigmaSet G E U, K

theorem sigmaSet_le {G E U K : Subgroup Γ} (hK : K ∈ sigmaSet G E U) : K ≤ U :=
  A3.subnormal_le hK.2

theorem le_sigmaJoin {G E U K : Subgroup Γ} (hK : K ∈ sigmaSet G E U) : K ≤ sigmaJoin G E U :=
  le_iSup₂_of_le (f := fun (K' : Subgroup Γ) (_ : K' ∈ sigmaSet G E U) => K') K hK le_rfl

theorem sigmaJoin_le {G E U : Subgroup Γ} : sigmaJoin G E U ≤ U :=
  iSup₂_le fun _ hK => sigmaSet_le hK

theorem mem_sigmaSet_self {G E U : Subgroup Γ} (hsub : IsSubnormal E U) :
    E ∈ sigmaSet G E U :=
  ⟨⟨1, G.one_mem, (A1b.conjSub_one E).symm⟩, hsub⟩

theorem sigmaSet_conj {G E U K : Subgroup Γ} (hUG : U ≤ G) (hK : K ∈ sigmaSet G E U) {u : Γ}
    (hu : u ∈ U) : A1b.conjSub u K ∈ sigmaSet G E U := by
  obtain ⟨⟨g, hg, rfl⟩, hsub⟩ := hK
  refine ⟨⟨u * g, G.mul_mem (hUG hu) hg, (A1b.conjSub_mul u g E).symm⟩, isSubnormal_conjSub hu hsub⟩

theorem mem_normalizer_sigmaJoin {G E U : Subgroup Γ} {y : Γ}
    (hy : ∀ K ∈ sigmaSet G E U, A1b.conjSub y K ∈ sigmaSet G E U)
    (hy' : ∀ K ∈ sigmaSet G E U, A1b.conjSub y⁻¹ K ∈ sigmaSet G E U) :
    y ∈ Subgroup.normalizer ((sigmaJoin G E U : Subgroup Γ) : Set Γ) := by
  have key : ∀ z : Γ, (∀ K ∈ sigmaSet G E U, A1b.conjSub z K ∈ sigmaSet G E U) →
      A1b.conjSub z (sigmaJoin G E U) ≤ sigmaJoin G E U := by
    intro z hz
    unfold sigmaJoin
    rw [conjSub_iSup]
    refine iSup_le fun K => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hK => ?_
    exact le_iSup₂_of_le (f := fun (K' : Subgroup Γ) (_ : K' ∈ sigmaSet G E U) => K')
      (A1b.conjSub z K) (hz K hK) le_rfl
  exact mem_normalizer_of_conjSub_le (key y hy) (key y⁻¹ hy')

theorem sigmaJoin_le_normalizer {G E U : Subgroup Γ}
    (h : ∀ K ∈ sigmaSet G E U, K ≤ Subgroup.normalizer (E : Set Γ)) :
    sigmaJoin G E U ≤ Subgroup.normalizer (E : Set Γ) :=
  iSup₂_le fun K hK => h K hK

variable [Finite Γ]

section Frame

variable {G T E : Subgroup Γ}

theorem sup_baum_le_normalizer (h : MinCex G T) (hE : E ∈ bStarT G T) :
    E ⊔ baum T ≤ G ⊓ Subgroup.normalizer (E : Set Γ) :=
  sup_le (le_inf hE.1.2.le Subgroup.le_normalizer)
    (le_inf ((inf_le_left : baum T ≤ T).trans h.sylow.1)
      (baum_le_normalizer_of_isBTBlock hE.1.2))

omit [Finite Γ] in
theorem normalizer_inf_lt (h4 : Seven4 G T) (hE : E ∈ bStarT G T) :
    G ⊓ Subgroup.normalizer (E : Set Γ) < G := by
  refine lt_of_le_of_ne inf_le_left fun hEq => ?_
  have hGN : G ≤ Subgroup.normalizer (E : Set Γ) := fun g hg => by
    have : g ∈ G ⊓ Subgroup.normalizer (E : Set Γ) := hEq.symm ▸ hg
    exact this.2
  refine h4 E ⟨1, G.one_mem, ?_⟩ (isSubnormal_of_le_of_le_normalizer hE.1.2.le hGN)
  rwa [A1b.conjSub_one]

theorem charTwo_of_proper (h : MinCex G T) (hE : E ∈ bStarT G T) {U : Subgroup Γ} (hUG : U < G)
    (hXU : E ⊔ baum T ≤ U) : CharTwo U := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hBU : baum T ≤ U := le_sup_right.trans hXU
  have hUC : ¬ U ≤ cStarIn G T := fun hl => hE.2 ((le_sup_left.trans hXU).trans hl)
  obtain ⟨S, hS, -⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBU
  exact (seven_three h hT ⟨hUG, hBU, hUC⟩ hS).1

theorem sigma_comm (h : MinCex G T) (hE : E ∈ bStarT G T) {U : Subgroup Γ} (hUG : U < G)
    (hXU : E ⊔ baum T ≤ U) {K K' : Subgroup Γ} (hK : K ∈ sigmaSet G E U)
    (hK' : K' ∈ sigmaSet G E U) (hne : K ≠ K') : ⁅K, K'⁆ = ⊥ := by
  obtain ⟨⟨g, hg, rfl⟩, hKs⟩ := hK
  obtain ⟨⟨g', hg', rfl⟩, hK's⟩ := hK'
  have hb : ∀ g₀ ∈ G, IsBTBlock G (A1b.conjSub g₀ T) (A1b.conjSub g₀ E) := fun g₀ hg₀ => by
    have := isBTBlock_conj g₀ hE.1.2
    rwa [BHS.conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hg₀)] at this
  exact blocks_commute_of_subnormal (charTwo_of_proper h hE hUG hXU) (hb g hg) (hb g' hg') hKs
    hK's hne

theorem sigma_le_normalizer (h : MinCex G T) (hE : E ∈ bStarT G T) {U : Subgroup Γ} (hUG : U < G)
    (hXU : E ⊔ baum T ≤ U) {K : Subgroup Γ} (hK : K ∈ sigmaSet G E U) :
    K ≤ Subgroup.normalizer (E : Set Γ) := by
  by_cases hKE : K = E
  · subst hKE
    exact Subgroup.le_normalizer
  · have hE' : E ∈ sigmaSet G E U := mem_sigmaSet_self (claim_A h hE hUG (le_sup_right.trans hXU)
      (le_sup_left.trans hXU))
    have hc : ⁅K, E⁆ = ⊥ := sigma_comm h hE hUG hXU hK hE' hKE
    have : K ≤ Subgroup.centralizer (E : Set Γ) := fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        have h1 : ⁅x, y⁆ ∈ (⁅K, E⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hx hy
        rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1.symm
    exact this.trans (Subgroup.centralizer_le_normalizer _)

theorem sigma_eq_of_maximal (h : MinCex G T) (h4 : Seven4 G T) (hE : E ∈ bStarT G T)
    {L : Subgroup Γ} (hL : IsMaximalSubgroup G L) (hXL : E ⊔ baum T ≤ L) :
    G ⊓ Subgroup.normalizer ((sigmaJoin G E L : Subgroup Γ) : Set Γ) = L ∧
      G ⊓ Subgroup.normalizer (E : Set Γ) ≤ L ∧
      sigmaSet G E L = sigmaSet G E (G ⊓ Subgroup.normalizer (E : Set Γ)) := by
  set Y : Subgroup Γ := G ⊓ Subgroup.normalizer (E : Set Γ) with hYdef
  have hYG : Y < G := normalizer_inf_lt h4 hE
  have hXY : E ⊔ baum T ≤ Y := sup_baum_le_normalizer h hE
  have hBL : baum T ≤ L := le_sup_right.trans hXL
  have hEL : E ≤ L := le_sup_left.trans hXL
  have hBY : baum T ≤ Y := le_sup_right.trans hXY
  have hEY : E ≤ Y := le_sup_left.trans hXY
  have hEsig : E ∈ sigmaSet G E L := mem_sigmaSet_self (claim_A h hE hL.1 hBL hEL)
  have hLle : L ≤ G ⊓ Subgroup.normalizer ((sigmaJoin G E L : Subgroup Γ) : Set Γ) := by
    refine le_inf hL.1.le fun l hl => mem_normalizer_sigmaJoin (fun K hK => ?_) (fun K hK => ?_)
    · exact sigmaSet_conj hL.1.le hK hl
    · exact sigmaSet_conj hL.1.le hK (L.inv_mem hl)
  have hlt : G ⊓ Subgroup.normalizer ((sigmaJoin G E L : Subgroup Γ) : Set Γ) < G := by
    refine lt_of_le_of_ne inf_le_left fun hEq => ?_
    have hGN : G ≤ Subgroup.normalizer ((sigmaJoin G E L : Subgroup Γ) : Set Γ) := fun g hg =>
      (hEq.symm ▸ hg : g ∈ G ⊓ Subgroup.normalizer ((sigmaJoin G E L : Subgroup Γ) : Set Γ)).2
    have hEN : sigmaJoin G E L ≤ Subgroup.normalizer (E : Set Γ) :=
      sigmaJoin_le_normalizer fun K hK => sigma_le_normalizer h hE hL.1 hXL hK
    have hsubE : IsSubnormal E (sigmaJoin G E L) :=
      isSubnormal_of_le_of_le_normalizer (le_sigmaJoin hEsig) hEN
    have hsubN : IsSubnormal (sigmaJoin G E L) G :=
      isSubnormal_of_le_of_le_normalizer (sigmaJoin_le.trans hL.1.le) hGN
    exact h4 E ⟨1, G.one_mem, by rwa [A1b.conjSub_one]⟩ (A3.subnormal_trans hsubE hsubN)
  have hNL : G ⊓ Subgroup.normalizer ((sigmaJoin G E L : Subgroup Γ) : Set Γ) = L :=
    hL.2 _ hLle hlt
  have hb : ∀ K ∈ sigmaSet G E L, K ∈ sigmaSet G E Y := fun K hK =>
    ⟨hK.1, claim_A h (sigma_mem_bStarT h hE hL.1 hBL hEL hK.1 hK.2) hYG hBY
      (le_inf ((sigmaSet_le hK).trans hL.1.le) (sigma_le_normalizer h hE hL.1 hXL hK))⟩
  have hc : ∀ K ∈ sigmaSet G E Y, K ≤ L := by
    intro K hK
    by_cases hKL : K ∈ sigmaSet G E L
    · exact sigmaSet_le hKL
    · have hNK : sigmaJoin G E L ≤ Subgroup.centralizer (K : Set Γ) := by
        refine iSup₂_le fun K' hK' x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        have hne : K ≠ K' := fun hEq => hKL (hEq ▸ hK')
        have hcomm : ⁅K, K'⁆ = ⊥ := sigma_comm h hE hYG hXY hK (hb K' hK') hne
        have h1 : ⁅y, x⁆ ∈ (⁅K, K'⁆ : Subgroup Γ) := Subgroup.commutator_mem_commutator hy hx
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      have hKc : K ≤ Subgroup.centralizer ((sigmaJoin G E L : Subgroup Γ) : Set Γ) := by
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        exact (Subgroup.mem_centralizer_iff.mp (hNK hn) k hk).symm
      have hKN := hKc.trans (Subgroup.centralizer_le_normalizer _)
      rw [← hNL]
      exact fun k hk => ⟨(sigmaSet_le hK hk).1, hKN hk⟩
  have hd : ∀ K ∈ sigmaSet G E Y, K ∈ sigmaSet G E L := fun K hK =>
    ⟨hK.1, claim_A h (sigma_mem_bStarT h hE hYG hBY hEY hK.1 hK.2) hL.1 hBL (hc K hK)⟩
  have hsig : sigmaSet G E L = sigmaSet G E Y := Set.ext fun K => ⟨hb K, hd K⟩
  have hYL : Y ≤ L := by
    intro y hy
    rw [← hNL]
    refine ⟨hy.1, mem_normalizer_sigmaJoin (fun K hK => ?_) (fun K hK => ?_)⟩
    · exact hd _ (sigmaSet_conj hYG.le (hb K hK) hy)
    · exact hd _ (sigmaSet_conj hYG.le (hb K hK) (Y.inv_mem hy))
  exact ⟨hNL, hYL, hsig⟩

theorem exists_maximalSubgroup_ge {G Y : Subgroup Γ} (hYG : Y < G) :
    ∃ L : Subgroup Γ, IsMaximalSubgroup G L ∧ Y ≤ L := by
  have hne : {K : Subgroup Γ | Y ≤ K ∧ K < G}.Nonempty := ⟨Y, le_rfl, hYG⟩
  obtain ⟨L, ⟨hYL, hLG⟩, hmax⟩ := Set.exists_max_image {K : Subgroup Γ | Y ≤ K ∧ K < G}
    (fun K => Nat.card K) (Set.toFinite _) hne
  refine ⟨L, ⟨hLG, fun K hLK hKG => ?_⟩, hYL⟩
  have hcard : Nat.card K ≤ Nat.card L := hmax K ⟨hYL.trans hLK, hKG⟩
  exact (Subgroup.eq_of_le_of_card_ge hLK hcard).symm

theorem seven_seven_of_seven_four (h : MinCex G T) (h4 : Seven4 G T) : Seven7 G T := by
  intro E hE
  have hYG : G ⊓ Subgroup.normalizer (E : Set Γ) < G := normalizer_inf_lt h4 hE
  have hXY : E ⊔ baum T ≤ G ⊓ Subgroup.normalizer (E : Set Γ) := sup_baum_le_normalizer h hE
  obtain ⟨L, hL, hYL⟩ := exists_maximalSubgroup_ge hYG
  have hXL : E ⊔ baum T ≤ L := hXY.trans hYL
  refine ⟨L, hL, hXL, claim_A h hE hL.1 (le_sup_right.trans hXL) (le_sup_left.trans hXL),
    fun H' hH' hXH' => ?_⟩
  obtain ⟨hNH', -, hsigH'⟩ := sigma_eq_of_maximal h h4 hE hH' hXH'
  obtain ⟨hNL, -, hsigL⟩ := sigma_eq_of_maximal h h4 hE hL hXL
  have hjoin : sigmaJoin G E H' = sigmaJoin G E L := by
    unfold sigmaJoin
    rw [hsigH', hsigL]
  rw [← hNH', ← hNL, hjoin]

end Frame

end CFSG.CGT.PushingUpLit.BHS7

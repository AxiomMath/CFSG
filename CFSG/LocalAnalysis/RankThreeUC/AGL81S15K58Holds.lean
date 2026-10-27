module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K58Lift
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K58A6Lat
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dRed
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Aux
public import CFSG.LargeExtraspecial.S5Syl
public import CFSG.LargeExtraspecial.S5Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K58Proof

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
  CFSG.LargeExtraspecial.S5

section Z

variable {X : Type} [Group X] {T : Subgroup X}

theorem omegaOneCenterOf_subset (L : Subgroup X) :
    ((omegaOneCenterOf T : Subgroup X) : Set X) ⊆
      ((gnV T ⊓ Subgroup.centralizer
        ((T ⊓ Subgroup.normalizer (L : Set X) : Subgroup X) : Set X) : Subgroup X) : Set X) := by
  intro x hx
  refine ⟨Subgroup.subset_normalClosure hx, ?_⟩
  exact Subgroup.centralizer_le (inf_le_left : T ⊓ Subgroup.normalizer (L : Set X) ≤ T)
    (CFSG.Quasithin.A4.centerOf_le_centralizer _
      (CFSG.Quasithin.A4.omegaOneCenterOf_le_centerOf _ hx))

end Z

section Core

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem exists_minOver_fixing [Finite X] (hT : IsSylowTwoOf T ⊤) {Ls : Subgroup (X ⧸ gnC T)}
    (hL : IsSubnormal Ls ⊤) [Group.IsPerfect ↥Ls] {n : ℕ}
    (hW : Nat.card (SecW (gnRep hV) Ls) = n + 1) (hlat : SylLat ↥Ls n) :
    IsSylowTwoOf (T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls) Ls ∧
      ∃ P : Subgroup (X ⧸ gnC T), IsMinOverBorel Ls (T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls) P ∧
        ∀ w : Additive (IntMod (gnV T) hV),
          (∀ s ∈ T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls, gnRep hV s w = w) →
            ∀ p ∈ P, gnRep hV p w = w := by
  have hT' : IsSylowTwoIn T ⊤ := hT
  have hTmap : IsSylowTwoIn (T.map (QuotientGroup.mk' (gnC T))) ⊤ := by
    have := hT'.map (QuotientGroup.mk' (gnC T))
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
  have hS₀ : IsSylowTwoOf (T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls) Ls :=
    hTmap.inf_of_isSubnormal hL
  have hS := isSylowTwoOf_subgroupOf_top hS₀
  obtain ⟨A, B, hAB⟩ := hlat _ hS
  obtain ⟨w₀, -, hfixS, hstab⟩ := fixed_eq_pair_of_lattice (secW (gnRep hV) Ls) hW
    (secW_fixed_eq_zero (gnRep hV) Ls) hS.2.1 hAB.lt_index hAB.lattice hAB.index_A hAB.index_B
    hAB.normalizer_A hAB.normalizer_B
  obtain ⟨P', hSP, hmin, hP'⟩ : ∃ P' : Subgroup ↥Ls,
      (T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls).subgroupOf Ls ≤ P' ∧
        IsMinOverBorel ⊤ ((T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls).subgroupOf Ls) P' ∧
        ∀ p ∈ P', secW (gnRep hV) Ls p w₀ = w₀ := by
    rcases hstab with h | h
    · exact ⟨A, hAB.le_A, hAB.isMinOverBorel_left, fun p hp => (h p).2 hp⟩
    · exact ⟨B, hAB.le_B, hAB.isMinOverBorel_right, fun p hp => (h p).2 hp⟩
  refine ⟨hS₀, P'.map Ls.subtype, K1525d_of_core_aux_minOver hS₀.1 hmin, ?_⟩
  rintro w hw _ ⟨p, hp, rfl⟩
  refine fixes_of_fixes_secW (gnRep hV) Ls hSP hS₀.2.2 (fun m hm q hq => ?_)
    (fun s hs => hw s (Subgroup.mem_subgroupOf.mp hs)) p hp
  rcases hfixS m hm with rfl | rfl
  · exact map_zero _
  · exact hP' q hq

theorem comap_le_centralizer {Ls P : Subgroup (X ⧸ gnC T)}
    (hP : ∀ w : Additive (IntMod (gnV T) hV),
      (∀ s ∈ T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls, gnRep hV s w = w) →
        ∀ p ∈ P, gnRep hV p w = w) :
    P.comap (toStar T) ≤ Subgroup.centralizer ((gnV T ⊓ Subgroup.centralizer
      ((T ⊓ Subgroup.normalizer ((Ls.comap (toStar T) : Subgroup X) : Set X) : Subgroup X) :
        Set X) : Subgroup X) : Set X) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  rintro y ⟨hyV, hyC⟩
  obtain ⟨w, rfl⟩ := exists_elt hV hyV
  have hw : ∀ s ∈ T.map (QuotientGroup.mk' (gnC T)) ⊓ Ls, gnRep hV s w = w := by
    rintro _ ⟨⟨t, ht, rfl⟩, htL⟩
    apply elt_injective hV
    have htN : t ∈ T ⊓ Subgroup.normalizer ((Ls.comap (toStar T) : Subgroup X) : Set X) :=
      ⟨ht, Subgroup.le_normalizer (Subgroup.mem_comap.mpr htL)⟩
    have hc : t * elt hV w = elt hV w * t := Subgroup.mem_centralizer_iff.mp hyC t htN
    show elt hV (gnRep hV (QuotientGroup.mk t) w) = elt hV w
    rw [elt_gnRep, hc, mul_inv_cancel_right]
  have h1 : elt hV (gnRep hV (QuotientGroup.mk x) w) = elt hV w := congrArg (elt hV) (hP w hw _ hx)
  rw [elt_gnRep] at h1
  calc elt hV w * x = x * elt hV w * x⁻¹ * x := by rw [h1]
    _ = x * elt hV w := by group

end Core

end K58Proof

section Main

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
  CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542


theorem K58_holds : K58 := by
  intro X _ _ T hX Ls hL hJ _ _ h6
  have hC : CharTwo (⊤ : Subgroup X) := hX.charTwo
  have hT2 : IsPGroup 2 T := hX.sylow.isPGroup
  have hQT : pCoreOf 2 (⊤ : Subgroup X) ≤ T :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow
  have hV := isElemAbelian_gnV_of_le hC hQT
  letI : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  obtain ⟨n, hW, hlat⟩ : ∃ n, Nat.card (K58Proof.SecW (gnRep hV) Ls) = n + 1 ∧
      K58Proof.SylLat ↥Ls n := by
    rcases h6 with h6 | hU
    · obtain ⟨eL⟩ := h6
      obtain ⟨hHI, hrel⟩ := a6_clause T hC hQT Ls hL hJ eL
      exact ⟨15, by rw [K58Proof.card_secW_gnRep hV Ls hHI hrel]; norm_num,
        K58Proof.sylLat_of_alt6 eL⟩
    · obtain ⟨hHI, hrel⟩ := agl81FiveThreeU33_proved X T hX.kGroup hC hT2 hQT Ls hL hJ hU
      exact ⟨63, by rw [K58Proof.card_secW_gnRep hV Ls hHI hrel]; norm_num,
        K58Proof.sylLat_of_isUThreeThree hU⟩
  haveI : Group.IsPerfect ↥Ls := ⟨hL.2.2.1⟩
  obtain ⟨hS₀, P, hmin, hfix⟩ := K58Proof.exists_minOver_fixing hV hX.sylow hL.2.1 hW hlat
  have hcent := (pElementSubgroup_le (p := 2) _).trans (K58Proof.comap_le_centralizer hV hfix)
  exact ⟨_, P, hS₀, hmin, hcent,
    hcent.trans (Subgroup.centralizer_le (K58Proof.omegaOneCenterOf_subset _))⟩

end Main

end CFSG.LocalAnalysis.RankThreeUC.S15

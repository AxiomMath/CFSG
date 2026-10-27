module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3322C

public section
namespace CFSG.Quasithin.H13.L3322

open Equiv Equiv.Perm
open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique hiding evenWeight
open CFSG.Quasithin.H13.A7 (IsCoordAct vec natLam)
open CFSG.Quasithin.SteinbergCB (permAct7 evenWeight sevenP)
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

section Comp

variable {ψ : ↥⁅vPlus L T, L⁆ ≃* Multiplicative (evenWeight 7)}

theorem thetaOf_centralizer_le_F4
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h14 : Stmt3_3_14_F4)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat) (h38' : A38ForSQTK) (hF : A318Facts)
    (hC27 : ASC27Statement_F4 G) (hI1 : A7.Insp1236) (hI2 : A7.InspSL2NoA6)
    (h : Hyp331 G T M L D) (hc : Coord322 T L ψ) {e : ↥⁅vPlus L T, L⁆}
    (he : vec ψ e = A7.vecSix) (heZ : (e : G) ∈ quasithinOmegaOneCenter T) {c : G}
    (hcZ : c ∈ quasithinOmegaOneCenter T) (hcL : c ∈ Subgroup.centralizer (L : Set G)) :
    thetaOf (Subgroup.centralizer ({c * (e : G)} : Set G)) ≤ lTheta L e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  set z := c * (e : G) with hzdef
  set Gz := Subgroup.centralizer ({z} : Set G) with hGz
  set Mz := M ⊓ Gz with hMzdef
  set Lθ := lTheta L (e : G) with hLθdef
  set R := pCoreOf 2 (L ⊔ T) with hRdef
  have he1 : (e : G) ≠ 1 := by
    intro h1
    have h2 : e = 1 := Subtype.ext h1
    rw [h2, A7.vec_one] at he
    exact absurd he (by decide)
  have hzZ : z ∈ quasithinOmegaOneCenter T := Subgroup.mul_mem _ hcZ heZ
  have hz1 : z ≠ 1 := by
    intro h1
    have hec : (e : G) = c⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine he1 (congrArg Subtype.val (eq_one_of_centralizer hc e fun l hl => ?_))
    rw [hec]
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.inv_mem _ hcL) l hl
  have hz2 : orderOf z = 2 := orderOf_eq_prime (sq_eq_one_of_mem_omegaOneCenter T hzZ) hz1
  have hTz : T ≤ Gz := fun t ht => Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 (L246C127.le_centralizer_omegaOneCenter T ht) z hzZ).symm
  have hLθeq : lTheta L z = Lθ := lTheta_mul_eq hcL _
  have hLθz : Lθ ≤ Gz := hLθeq ▸ lTheta_le_centralizer L z
  have hLθL : Lθ ≤ L := lTheta_le L _
  have hLθMz : Lθ ≤ Mz := le_inf (hLθL.trans h.LM) hLθz
  have hMz : Mz ≤ Subgroup.normalizer (Lθ : Set G) := by
    rw [← hLθeq]
    intro m hm
    have h1 : m ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :
        Set G) := CFSG.Quasithin.A4.mem_normalizer_inf (hMN hm.1) (Subgroup.le_normalizer hm.2)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 ⊢
    rw [← oTwoUpper_map, h1]
  have hTLθ : T ≤ Subgroup.normalizer (Lθ : Set G) := T_le_normalizer_lTheta hTL heZ
  have hR : pCoreOf 2 (Lθ ⊔ T) = R := pCoreOf_lTheta_sup h7 h hML hTL hc he heZ
  have hR1 : R ≠ ⊥ := by
    intro hb
    have heR : (e : G) ∈ R :=
      ((Hyp331.vPlus_reduced h.toSetup331).1 (L3317.commV_le_vPlus h e.2)).1
    rw [hb, Subgroup.mem_bot] at heR
    exact he1 heR
  have hH2 : pCoreOf 2 Gz ≠ ⊥ := by
    have hle : Subgroup.zpowers z ≤ pCoreOf 2 Gz := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 rfl)) ?_
        (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2, pow_one]))
      rw [A7.normalizer_zpowers_eq_centralizer' hz2]
    intro hbot
    apply hz1
    have := hle (Subgroup.mem_zpowers z)
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨hLθF, hLθq, hA6⟩ := lTheta_mem_lFamily h hTL hc he heZ
  have hLθO : Lθ = oTwoUpper Lθ := eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hLθF)
  have hC23 : HypC23 Gz R Mz :=
    hypC23_centralizer h5 h hML hzZ hH2 hLθO hLθL hLθz hMz hR hR1
  have hLocal : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke).1
  have hSylH : QuasithinUnique.IsSylowTwoOf T Gz := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hTz
  obtain ⟨K, ⟨hK, hLθK⟩, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_4_existsUnique hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h39 hH2 hSylH hLθz hLθF
  have hKn := QuasithinUnique.Vol2Native.lemma_1_2_4_normal hLocal
    QuasithinUnique.Vol2Native.a37ForSQTKCat_proved h38 hH2 hSylH hLθF hLθK hK hTLθ
  have hKH : K ≤ Gz := le_of_mem_cComp hK
  have hTK : T ≤ Subgroup.normalizer (K : Set G) :=
    hTz.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).1 hKn)
  have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
    obtain ⟨hcases, -, -⟩ := QuasithinUnique.Vol2Native.lemma_1_2_1_four_core hLocal
      QuasithinUnique.Vol2Native.a36CoreForSQTKCat_proved hH2 hK
    rcases hcases with hc' | h34
    · obtain ⟨eK⟩ := modO2_mulEquiv hK
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hc'.1
    · exfalso
      obtain ⟨e6⟩ := hA6
      refine A7.not_case34_of_le hI2 hK hLθK (g := e6.toMonoidHom.comp
        ((QuotientGroup.mk' _).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥Lθ)))) ?_ h34
      exact e6.surjective.comp ((QuotientGroup.mk'_surjective _).comp
        (QuotientGroup.mk'_surjective _))
  have hHchar : QuasithinUnique.CharTwo Gz := by
    obtain ⟨Ts, hTs⟩ : ∃ Ts : Sylow 2 G, (Ts : Subgroup G) = T :=
      ⟨_, IsPGroup.toSylow_coe h.sylow.1 h.sylow.2⟩
    exact h.qtke.2.1 _ (A7.isTwoLocal_centralizer' hz2) ⟨Ts, hTs ▸ hTz⟩
  have hKchar : QuasithinUnique.CharTwo K :=
    A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hHchar
  have hLθK' : Lθ = K := by
    by_contra hne
    have hlt : Lθ < K := lt_of_le_of_ne hLθK hne
    have hKMz : ¬ K ≤ Mz := by
      intro hKMz
      have hn : (Lθ.subgroupOf K).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLθK).2 (hKMz.trans hMz)
      exact hK.2.2.2 _ hlt hLθF.1 (perfect_of_mem_cComp hLθF)
        (IsSubnormal.step hLθK hn (subnormal_of_mem_cComp hK))
    have hRT : R ≤ T := QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
    have hRK : R ≤ Subgroup.normalizer (K : Set G) := hRT.trans hTK
    have hconcl : C27Concl Gz R Mz K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) :=
      hC27 _ _ _ K _ hC23 hK hKq hKchar hKMz hRK rfl
    exact hI1 G _ _ _ K _ T Lθ hC23 hK hKq hKchar hKMz hRK rfl hconcl hSylH hRT hTK
      (le_inf hLθK hLθMz) hTLθ hLθq hA6
  rw [← hLθK'] at hK hKn
  exact A7.thetaOf_le_of_A6 hF h38' h.qtke h.simple h.nonabelian hH2 hK hKn hLθq hA6

end Comp

end CFSG.Quasithin.H13.L3322

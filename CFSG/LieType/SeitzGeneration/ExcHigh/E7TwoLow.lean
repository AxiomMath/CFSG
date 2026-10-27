module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E7Two
public import CFSG.LieType.SeitzGeneration.ExcHigh.E7SylowFive
public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwoLow
public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameCyclic

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

section S1
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge TauCeti CFSG.AGLEmbeddingD2
  CFSG.LieType.SeitzGeneration
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups


noncomputable abbrev e7D6Chain (K : Type) [Field K] (k : Fin 6) :
    Subgroup (adjointGroup .E7 K) :=
  rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k)

theorem exists_e7D6_family_param (K : Type) [Field K] [Finite K] :
    ∃ ρ : Fin 6 → SL(2, K) →* adjointGroup .E7 K,
      (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = e7D6Chain K k) ∧
      (∀ i j : Fin 6, i ≠ j → ¬ edgeD 6 i j → ¬ edgeD 6 j i →
        ∀ u ∈ e7D6Chain K i, ∀ v ∈ e7D6Chain K j, u * v = v * u) ∧
      (∀ i j : Fin 6, edgeD 6 i j → ∃ ψ : SL(3, K) →* adjointGroup .E7 K,
        ψ.comp (ClassicalInvolution.WeakCT.blk K 0) = ρ i ∧
          ψ.comp (ClassicalInvolution.WeakCT.blk K 1) = ρ j) ∧
      ∀ (k : Fin 6) c, ρ k (tv 0 1 c) = xPar (rootOperatorFamily .E7) (Pi.single (e7D6Node k) 1) c ∧
        ρ k (tv 1 0 c) = xPar (rootOperatorFamily .E7) (-Pi.single (e7D6Node k) 1) c := by
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  refine ⟨fun k => ρF (e7D6Node k), fun k => ⟨hρFi _, hρFr _⟩, fun i j hij h1 h2 => ?_,
    fun i j h => ?_, fun k c => hρFv _ c⟩
  · obtain ⟨hne, hc1, hc2⟩ := e7D6_nadj i j hij h1 h2
    exact commutes_rankOne_of_cartan_eq_zero hE rfl hne hc1 hc2
  · obtain ⟨hne, hc1, hc2, l, hl⟩ := e7D6_adj i j h
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl hne hc1 hc2 hl
    exact ⟨emb, sl3_comp_blk hv (hρFv _) (hρFv _)⟩

theorem exists_psi_D6_param (K : Type) [Field K] [Finite K] (hn3 : 3 ≤ 6) :
    ∃ Ψ : spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 6 K)) ∧
      Ψ.range = e7D6Group K ∧
      (∀ k, (CurtisTits.rankOne (Spin.plusDatum 6 K hn3).rootGroup k).map Ψ = e7D6Chain K k) ∧
      ∀ k : Fin 6, Ψ (Spin.weylD K hn3 k) = Chevalley.weylElement .E7 K (e7D6Node k) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hadm : StatedLieAdmissible .POmegaPlus 6 (ringChar K) m := ⟨hℓ, m.pos, by norm_num⟩
  obtain ⟨ρ, hρ, hcomm, hψ, hparam⟩ := exists_e7D6_family_param K
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.plusDatum 6 K hn3).isFiniteType
    (Dv := (Spin.plusDatum 6 K hn3).divisible) rfl
  have hE := Steinberg.SpinPlus.chevalleyExtras hn3 O Steinberg.SpinPlus.commC
    (Steinberg.SpinPlus.commutatorFormula hn3 O)
  obtain ⟨x', hD, hx'⟩ := exists_simplyLacedLevis hE rfl
    (fun α _ β _ _ _ => Steinberg.SpinPlus.commC_natAbs α β (1, 1)) LevisSpin.edgeD_asymm
    (fun _ _ h => LevisSpin.cartanD_of_edgeD h)
    (fun _ _ hij h1 h2 => LevisSpin.cartanD_of_not_edgeD hij h1 h2)
    (fun _ _ h => LevisSpin.edgeD_neighbour hn3 h)
    (Spin.plusDatum_steinbergExtras hn3).torus_iSupIndep
    (fun (k : Fin 6) => by
      have h := (Steinberg.SpinPlus.isCTGroupDatum (K := K) hn3).sq_mem k
      rw [← weylElement_spinPlus hn3 k] at h
      exact h)
  obtain ⟨Ψ, hker, hrange, hu, hv, hrank⟩ := weakCT_param
    (CurtisTits.curtisTitsConclusion_spinPlus hadm hK hn3) (leviConePresented_spinPlus K hn3) hD
    (⟨0, by omega⟩ : Fin 6) (U := e7D6Chain K) hcomm hρ hψ
  have hU1 : ∀ k c, Ψ (Steinberg.SpinPlus.x 6 K hn3 (sroot k) c) = ρ k (tv 0 1 c) := fun k c =>
    (congrArg Ψ (hx' k c).1.symm).trans (hu k c)
  have hU2 : ∀ k c, Ψ (Steinberg.SpinPlus.x 6 K hn3 (-sroot k) c) = ρ k (tv 1 0 c) := fun k c =>
    (congrArg Ψ (hx' k c).2.symm).trans (hv k c)
  refine ⟨Ψ, hker, hrange, hrank, fun k => ?_⟩
  rw [← weylElement_spinPlus hn3 k, weylElement_eq_xPar (rootOperatorFamily .E7) (e7D6Node k)]
  simp only [Steinberg.weylElement, Units.val_one, inv_one, map_mul]
  change Ψ (Steinberg.SpinPlus.x 6 K hn3 (sroot k) 1) *
    Ψ (Steinberg.SpinPlus.x 6 K hn3 (-sroot k) (-1)) *
      Ψ (Steinberg.SpinPlus.x 6 K hn3 (sroot k) 1) = _
  rw [hU1, hU2, (hparam k 1).1, (hparam k (-1)).2]

@[expose] def ι6 : Fin 3 × Bool ≃ Fin 6 where
  toFun p := ⟨2 * p.1.val + (if p.2 then 1 else 0), by
    have := p.1.isLt
    split_ifs <;> omega⟩
  invFun j := (⟨j.val / 2, by omega⟩, decide (j.val % 2 = 1))
  left_inv := by decide
  right_inv := by decide

section Identification

variable {K : Type} [Field K] (hn3 : 3 ≤ 6)
  {Ψ : spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K}

theorem map_longSL2_eq_chain_e7
    (hrank : ∀ k, (CurtisTits.rankOne (Spin.plusDatum 6 K hn3).rootGroup k).map Ψ = e7D6Chain K k)
    {k i j : Fin 6} (hij : i ≠ j) (s t : Bool)
    (hγ : toStdD 6 (Pi.single k 1) = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    ((Spin.plusFrame 6 K hn3).longSL2 hij s t).range.map Ψ = e7D6Chain K k := by
  have h := CFSG.ClassicalInvolution.RouteD.Gaps.rootGroup_sup_eq_longSL2_range (K := K) hn3 hij
    s t hγ
  rw [← h]
  exact hrank k

theorem map_longSL2_le_of_word_e7
    (hrank : ∀ k, (CurtisTits.rankOne (Spin.plusDatum 6 K hn3).rootGroup k).map Ψ = e7D6Chain K k)
    (hweyl : ∀ k : Fin 6,
      Ψ (Spin.weylD K hn3 k) = Chevalley.weylElement .E7 K (e7D6Node k))
    (ω : List (Fin 6)) (k₀ : Fin 6) {i j : Fin 6} (hij : i ≠ j) (s t : Bool)
    (hγ : ω.foldr (fun a e => stdReflD 6 a e) (toStdD 6 (Pi.single k₀ 1)) =
      Pi.single i (boolSign s) + Pi.single j (boolSign t))
    {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : wordReflect .E7 (ω.map e7D6Node) (Pi.single (e7D6Node k₀) 1) = β) :
    ((Spin.plusFrame 6 K hn3).longSL2 hij s t).range.map Ψ ≤ rootPairE7 K β := by
  have hΦ := RootSystem.isCTRootSystem (isFiniteType_cartanD 6) (∅ : Set (Fin 6))
  set w := (RootSystem.coxeterMatrix (isFiniteType_cartanD 6)).toCoxeterSystem.wordProd ω with hw
  set γ : Fin 6 → ℤ := RootSystem.weylAction (isFiniteType_cartanD 6) w (Pi.single k₀ 1) with hγdef
  have hγ' : toStdD 6 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
    rw [hγdef, hw, toStdD_weylAction_wordProd, hγ]
  have hsingle : (Pi.single k₀ 1 : Fin 6 → ℤ) ∈ RootSystem.roots (isFiniteType_cartanD 6) ∅ :=
    hΦ.single_mem k₀
  have hneg : (-Pi.single k₀ 1 : Fin 6 → ℤ) ∈ RootSystem.roots (isFiniteType_cartanD 6) ∅ := by
    have := hΦ.smul_mem ((RootSystem.coxeterMatrix (isFiniteType_cartanD 6)).toCoxeterSystem.simple
      k₀) _ (hΦ.single_mem k₀)
    rwa [hΦ.simple_single] at this
  have hrg := CFSG.ClassicalInvolution.RouteD.Gaps.rootGroup_sup_eq_longSL2_range (K := K) hn3 hij
    s t hγ'
  have hle : ((Spin.plusFrame 6 K hn3).longSL2 hij s t).range ≤
      (CurtisTits.rankOne (Spin.plusDatum 6 K hn3).rootGroup k₀).map
        (MulAut.conj ((ω.map (Spin.weylD K hn3)).prod)).toMonoidHom := by
    rw [← hrg]
    refine sup_le ?_ ?_
    · exact (spin_rootGroup_wordProd_le (K := K) hn3 ω hsingle).trans
        (Subgroup.map_mono le_sup_left)
    · have h2 := spin_rootGroup_wordProd_le (K := K) hn3 ω hneg
      rw [hw, map_neg] at *
      exact h2.trans (Subgroup.map_mono le_sup_right)
  have hΨz : Ψ ((ω.map (Spin.weylD K hn3)).prod) = weylWordElt .E7 K (ω.map e7D6Node) := by
    rw [map_list_prod, List.map_map, weylWordElt, List.map_map]
    congr 1
    exact List.map_congr_left fun k _ => hweyl k
  calc ((Spin.plusFrame 6 K hn3).longSL2 hij s t).range.map Ψ
      ≤ ((CurtisTits.rankOne (Spin.plusDatum 6 K hn3).rootGroup k₀).map
          (MulAut.conj ((ω.map (Spin.weylD K hn3)).prod)).toMonoidHom).map Ψ :=
        Subgroup.map_mono hle
    _ = ((CurtisTits.rankOne (Spin.plusDatum 6 K hn3).rootGroup k₀).map Ψ).map
          (MulAut.conj (Ψ ((ω.map (Spin.weylD K hn3)).prod))).toMonoidHom :=
        map_conj_map Ψ _ _
    _ = (rootPairE7 K (Pi.single (e7D6Node k₀) 1)).map
          (MulAut.conj (weylWordElt .E7 K (ω.map e7D6Node))).toMonoidHom := by
        rw [hrank k₀, hΨz]
        rfl
    _ = rootPairE7 K β := by
        rw [← hβ]
        exact map_conj_weylWordElt_rootPair (K := K) (ω.map e7D6Node) (isRoot_single _ _)

theorem e7D6Chain_le_frame_of_simple {k : Fin 6} {i : Fin 7}
    (h : frameE7Root i = Pi.single (e7D6Node k) 1) : e7D6Chain K k ≤ e7FrameGroup K := by
  have e : e7D6Chain K k = rootPairE7 K (Pi.single (e7D6Node k) 1) := rfl
  rw [e, ← h]
  exact le_iSup (fun i => rootPairE7 K (frameE7Root i)) i

theorem map_spinFrameGroup_le_e7
    (hrank : ∀ k, (CurtisTits.rankOne (Spin.plusDatum 6 K hn3).rootGroup k).map Ψ = e7D6Chain K k)
    (hweyl : ∀ k : Fin 6,
      Ψ (Spin.weylD K hn3 k) = Chevalley.weylElement .E7 K (e7D6Node k)) :
    (spinFrameGroup 6 K hn3 ι6).map Ψ ≤ e7FrameGroup K := by
  unfold spinFrameGroup
  rw [Subgroup.map_iSup]
  refine iSup_le fun a => ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · fin_cases a
    ·
      refine (map_longSL2_le_of_word_e7 hn3 hrank hweyl [1, 0, 2, 1, 3, 2, 4, 3] 5
        (ne_of_pairing ι6 _) true true (by decide +kernel) (β := frameE7Root 1)
        (by decide)).trans (le_iSup (fun i => rootPairE7 K (frameE7Root i)) 1)
    ·
      refine (map_longSL2_le_of_word_e7 hn3 hrank hweyl [3, 2, 4, 3] 5
        (ne_of_pairing ι6 _) true true (by decide +kernel) (β := frameE7Root 2)
        (by decide)).trans (le_iSup (fun i => rootPairE7 K (frameE7Root i)) 2)
    ·
      rw [map_longSL2_eq_chain_e7 hn3 hrank (k := 5) (ne_of_pairing ι6 _) true true
        (by decide +kernel)]
      exact e7D6Chain_le_frame_of_simple (i := 6) (by decide)
  · fin_cases a
    ·
      rw [map_longSL2_eq_chain_e7 hn3 hrank (k := 0) (ne_of_pairing ι6 _) true false
        (by decide +kernel)]
      exact e7D6Chain_le_frame_of_simple (i := 3) (by decide)
    ·
      rw [map_longSL2_eq_chain_e7 hn3 hrank (k := 2) (ne_of_pairing ι6 _) true false
        (by decide +kernel)]
      exact e7D6Chain_le_frame_of_simple (i := 4) (by decide)
    ·
      rw [map_longSL2_eq_chain_e7 hn3 hrank (k := 4) (ne_of_pairing ι6 _) true false
        (by decide +kernel)]
      exact e7D6Chain_le_frame_of_simple (i := 5) (by decide)

end Identification

end S1

section S2
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge TauCeti CFSG.AGLEmbeddingD2
  CFSG.LieType.SeitzGeneration
open scoped MatrixGroups


section Product

variable {K : Type} [Field K]

theorem commute_rootPairE7_theta_of_mem_e7D6Group {x y : adjointGroup .E7 K}
    (hx : x ∈ rootPairE7 K e7Theta) (hy : y ∈ e7D6Group K) : Commute x y := by
  have hcentr : e7D6Group K ≤
      Subgroup.centralizer (rootPairE7 K e7Theta : Set (adjointGroup .E7 K)) := by
    refine iSup_le fun k => ?_
    intro y hy x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7Theta_orth k
    exact commutes_rootPair_of_noG2 (K := K) noG2_E7 isRoot_e7Theta (isRoot_single _ _)
      h1 h2 h3 h4 h5 x hx y hy
  exact Subgroup.mem_centralizer_iff.1 (hcentr hy) x hx

theorem rootPairE7_theta_le_e7FrameGroup : rootPairE7 K e7Theta ≤ e7FrameGroup K := by
  have e : frameE7Root 0 = e7Theta := by decide
  have h : rootPairE7 K (frameE7Root 0) ≤ e7FrameGroup K :=
    le_iSup (fun i => rootPairE7 K (frameE7Root i)) 0
  rwa [e] at h

end Product

end S2

section Group
open scoped MatrixGroups
open CFSG.HardMathSupport.Lang.AnisoF4

theorem not_dvd_card_ker_noncommCoprod {K S G : Type*} [Field K] [Finite K] [Group S] [Finite S]
    [Group G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (ρ : SL(2, K) →* G)
    (hρi : Function.Injective ρ) (Ψ : S →* G)
    (hcomm : ∀ (a : SL(2, K)) (t : S), Commute (ρ a) (Ψ t))
    (hker : Ψ.ker ≤ Subgroup.center S) (hcen : ¬ p ∣ Nat.card (Subgroup.center S)) :
    ¬ p ∣ Nat.card (MonoidHom.noncommCoprod ρ Ψ hcomm).ker := by
  intro hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
  obtain ⟨⟨a, s⟩, hxk⟩ := x
  have hxk' : ρ a * Ψ s = 1 := hxk
  have hxp : (a, s) ^ p = 1 := by
    have := pow_orderOf_eq_one (⟨(a, s), hxk⟩ : (MonoidHom.noncommCoprod ρ Ψ hcomm).ker)
    rw [hx] at this
    exact congrArg Subtype.val this
  have hap : a ^ p = 1 := congrArg Prod.fst hxp
  have hsp : s ^ p = 1 := congrArg Prod.snd hxp
  have hacent : a ∈ Subgroup.center SL(2, K) := by
    rw [Subgroup.mem_center_iff]
    intro b
    have h1 : ρ a = (Ψ s)⁻¹ := eq_inv_of_mul_eq_one_left hxk'
    have h2 : Commute (ρ b) (ρ a) := by
      rw [h1]
      exact (hcomm b s).inv_right
    apply hρi
    rw [map_mul, map_mul]
    exact h2.eq
  obtain ⟨r, hr, hra⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hacent
  simp only [Fintype.card_fin] at hr
  have ha2 : a * a = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, ← hra, ← map_mul, ← pow_two, hr, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  have ha1 : a = 1 := by
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2
      (by omega)
    have hd2 : orderOf a ∣ Nat.gcd 2 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rwa [pow_two])) (orderOf_dvd_of_pow_eq_one hap)
    rw [hcop] at hd2
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd2)
  have hΨs : Ψ s = 1 := by
    rw [ha1, map_one, one_mul] at hxk'
    exact hxk'
  have hs1 : s = 1 :=
    eq_one_of_pow_eq_one_of_not_dvd hcen (hker (MonoidHom.mem_ker.2 hΨs)) hsp
  have hx1 : (⟨(a, s), hxk⟩ : (MonoidHom.noncommCoprod ρ Ψ hcomm).ker) = 1 :=
    Subtype.ext (Prod.ext ha1 hs1)
  rw [hx1, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

theorem map_conj_eq_of_commute {G : Type*} [Group G] (V : Subgroup G) (x : G)
    (h : ∀ v ∈ V, Commute x v) : V.map (MulAut.conj x).toMonoidHom = V := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(h v hv).eq, mul_inv_cancel_right]
    exact hv
  · intro hz
    refine ⟨z, hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(h z hz).eq, mul_inv_cancel_right]

theorem map_conj_mul {G : Type*} [Group G] (V : Subgroup G) (x y : G) :
    V.map (MulAut.conj (x * y)).toMonoidHom =
      (V.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext z
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply, mul_inv_rev]
  group

end Group

section Group2

theorem card_map_le {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H) (E : Subgroup G) :
    Nat.card (E.map f) ≤ Nat.card E := by
  have hs : Function.Surjective (fun x : E => (⟨f x, ⟨x, x.2, rfl⟩⟩ : E.map f)) := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact Nat.card_le_card_of_surjective _ hs

theorem card_le_card_map_prod {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (F : Subgroup (A × B)) :
    Nat.card F ≤ Nat.card (F.map (MonoidHom.fst A B)) * Nat.card (F.map (MonoidHom.snd A B)) := by
  have hinj : Function.Injective (fun x : F =>
      ((⟨x.1.1, ⟨x, x.2, rfl⟩⟩ : F.map (MonoidHom.fst A B)),
        (⟨x.1.2, ⟨x, x.2, rfl⟩⟩ : F.map (MonoidHom.snd A B)))) := by
    intro x y h
    have h1 := congrArg (fun z => (z.1 : A)) h
    have h2 := congrArg (fun z => (z.2 : B)) h
    exact Subtype.ext (Prod.ext h1 h2)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

end Group2

section S3
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge TauCeti CFSG.AGLEmbeddingD2
  CFSG.LieType.SeitzGeneration
open scoped MatrixGroups


section Main

variable {K : Type} [Field K] [Finite K]

theorem e7_conj_into_frame_five (hodd : Odd (Nat.card K)) (hpq : 5 ∣ Nat.card K + 1)
    (E₀ : Subgroup (adjointGroup .E7 K)) (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (hE₀c : Nat.card E₀ = 5 ^ 2) (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hp5p : (5 : ℕ).Prime := Nat.prime_five
  have hord := orderOf_eq_two_of_dvd_add_one hp5p (by norm_num) hpq
  have hpK : ¬ 5 ∣ Nat.card K := not_dvd_card_of_dvd_add_one hp5p hpq
  have hpq1 := not_dvd_pred_of_dvd_add_one hp5p (by norm_num) hpq
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hℓ, hm⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hm
  have hpl : 5 ≠ ringChar K := by
    intro h
    apply hpK
    rw [hK, ← h]
    exact dvd_pow_self 5 m.ne_zero
  have hpK0 : ((5 : ℕ) : K) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp5p hpK
  have hn3 : 3 ≤ 6 := by norm_num
  obtain ⟨Ψ, hker, hrange, hrank, hweyl⟩ := exists_psi_D6_param K hn3
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K) isRoot_e7Theta
  have hcomm : ∀ (a : SL(2, K)) (t : spinGroup (Spin.quadPlus 6 K)), Commute (ρ a) (Ψ t) :=
    fun a t => commute_rootPairE7_theta_of_mem_e7D6Group (hρr ▸ ⟨a, rfl⟩) (hrange ▸ ⟨t, rfl⟩)
  haveI : Nonempty (Fin 6 ⊕ Fin 6) := ⟨Sum.inl 0⟩
  haveI : Finite (spinGroup (Spin.quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcen5 := not_dvd_card_center_spinPlus (K := K) hn3 (p := 5) (by norm_num) hpq1
  let ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K :=
    MonoidHom.noncommCoprod ρ Ψ hcomm
  have hψker : ¬ 5 ∣ Nat.card ψ.ker :=
    not_dvd_card_ker_noncommCoprod (by norm_num) ρ hρi Ψ hcomm hker hcen5
  obtain ⟨g, hg⟩ := exists_conj_le_range_of_sylow_E7_five hpq ψ hψker E₀ hE₀p
  set E := E₀.map (MulAut.conj g).toMonoidHom with hE
  have hEp : ∀ x ∈ E, x ^ 5 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [conj_pow, hE₀p y hy]
    group
  have hEc : Nat.card E = 5 ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    let _ : CommGroup E := IsPGroup.commGroupOfCardEqPrimeSq hEc
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hE_le : E ≤ ψ.range := hg
  set ψ' : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* ψ.range := ψ.rangeRestrict with hψ'
  have hψ'surj : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  have hψ'ker : ψ'.ker = ψ.ker := ψ.ker_rangeRestrict
  set E1 : Subgroup ψ.range := E.subgroupOf ψ.range with hE1def
  have hE1 : IsElemAbelian 5 E1 :=
    ⟨IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subtype.ext (hEcomm a.1.1 a.2 b.1.1 b.2)),
     fun x hx => Subtype.ext (hEp x hx)⟩
  obtain ⟨E', hmapE', hdisE', hE'ea⟩ :=
    exists_lift_elemAbelian_of_coprime_ker ψ' hψ'surj (hψ'ker ▸ hψker) hE1
  have hcardE1 : Nat.card E1 = 5 ^ 2 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE_le).toEquiv
  have hcardE' : Nat.card E' = 5 ^ 2 := by
    rw [← card_map_eq_of_disjoint_ker ψ' hdisE', hmapE', hcardE1]
  have hlift : ∀ ε ∈ E, ∃ e ∈ E', ψ e = ε := by
    intro ε hε
    have : (⟨ε, hE_le hε⟩ : ψ.range) ∈ E1 := hε
    rw [← hmapE'] at this
    obtain ⟨e, he, hee⟩ := this
    exact ⟨e, he, congrArg Subtype.val hee⟩
  set E₁ : Subgroup SL(2, K) := E'.map (MonoidHom.fst _ _) with hE₁def
  set E₂ : Subgroup (spinGroup (Spin.quadPlus 6 K)) := E'.map (MonoidHom.snd _ _) with hE₂def
  have hE₁ea : IsElemAbelian 5 E₁ := hE'ea.map _
  have hE₂ea : IsElemAbelian 5 E₂ := hE'ea.map _
  have hcard₁ : Nat.card E₁ ≤ 5 := card_le_of_isElemAbelian_specialLinear_two hpK0 hE₁ea
  have hE₂card : Nat.card E₂ = 5 ∨ Nat.card E₂ = 5 ^ 2 := by
    have hpg : IsPGroup 5 E₂ := fun x => ⟨1, Subtype.ext (by simpa using hE₂ea.2 x x.2)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hpg
    have hle2 : Nat.card E₂ ≤ 5 ^ 2 := hcardE' ▸ card_map_le _ E'
    have hge : 5 ^ 2 ≤ 5 * Nat.card E₂ := by
      have := card_le_card_map_prod E'
      rw [hcardE'] at this
      exact this.trans (Nat.mul_le_mul_right _ hcard₁)
    rw [hn] at hle2 hge ⊢
    have hn2 : n ≤ 2 := by
      by_contra h
      have : 5 ^ 3 ≤ 5 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hn1 : 1 ≤ n := by
      by_contra h
      have : n = 0 := by omega
      subst this
      norm_num at hge
    interval_cases n
    · left; norm_num
    · right; rfl
  have hNS : ∀ T : Submodule K (Fin 6 ⊕ Fin 6 → K),
      (∀ e ∈ E₂, ∀ v ∈ T, spinAction (Spin.quadPlus 6 K) e v ∈ T) →
      (∀ v ∈ T, Spin.quadPlus 6 K v = 0) → T = ⊥ := by
    intro T hTi hTs
    by_contra hT0
    obtain ⟨U, hU0, hUp, hUn⟩ :=
      exists_rGroup_normalized_of_invariant_singular hodd hn3 E₂ T hT0 hTs hTi
    haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
    have hr2 : ringChar K ≠ 2 := by
      intro h2
      have : Even (Nat.card K) := by
        rw [hK, h2]
        exact (Nat.even_pow.mpr ⟨even_two, m.ne_zero⟩)
      exact (Nat.not_even_iff_odd.mpr hodd) this
    have hrq1 : ¬ ringChar K ∣ Nat.card K - 1 := by
      intro hd
      have hq1 : 1 ≤ Nat.card K := Nat.card_pos
      have h1 : ringChar K ∣ Nat.card K := by
        rw [hK]
        exact dvd_pow_self _ m.ne_zero
      have h2 : ringChar K ∣ Nat.card K - (Nat.card K - 1) := Nat.dvd_sub h1 hd
      have e : Nat.card K - (Nat.card K - 1) = 1 := by omega
      rw [e] at h2
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
    have hcenr := not_dvd_card_center_spinPlus (K := K) hn3 hr2 hrq1
    have hV0 := map_ne_bot_of_central_kernel Ψ hker hcenr hU0 hUp
    apply hN
    refine normalizesRGroup_of_map_conj g ⟨U.map Ψ, hV0, hUp.map Ψ, ?_⟩
    rintro ε hε
    obtain ⟨⟨a, s⟩, he, rfl⟩ := hlift ε hε
    have hs : s ∈ E₂ := ⟨(a, s), he, rfl⟩
    have hψe : ψ (a, s) = ρ a * Ψ s := rfl
    rw [hψe, map_conj_mul, ← map_conj_map Ψ s U, hUn s hs]
    exact map_conj_eq_of_commute _ _ (by
      rintro _ ⟨u, -, rfl⟩
      exact hcomm a u)
  have hfr : ∃ x : spinGroup (Spin.quadPlus 6 K), ∀ e ∈ E₂,
      x * e * x⁻¹ ∈ spinFrameGroup 6 K hn3 ι6 := by
    rcases hE₂card with h5 | h25
    ·
      haveI : Nontrivial E₂ := Finite.one_lt_card_iff_nontrivial.mp (by rw [h5]; norm_num)
      obtain ⟨b', hb'⟩ := exists_ne (1 : E₂)
      set b : spinGroup (Spin.quadPlus 6 K) := (b' : spinGroup (Spin.quadPlus 6 K)) with hbdef
      have hbE : b ∈ E₂ := b'.2
      have hb5 : b ^ 5 = 1 := hE₂ea.2 b hbE
      have hb1 : b ≠ 1 := fun h => hb' (Subtype.ext h)
      have hord5 : orderOf b = 5 := orderOf_eq_prime hb5 hb1
      have hzp : Subgroup.zpowers b = E₂ := by
        refine Subgroup.eq_of_le_of_card_ge ?_ ?_
        · rw [Subgroup.zpowers_le]
          exact hbE
        · rw [Nat.card_zpowers, hord5, h5]
      have hmem : ∀ e ∈ E₂, ∃ i : ℕ, b ^ i = e := fun e he => by
        rw [← hzp] at he
        exact (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr he)
      have hNSb : ∀ T : Submodule K (Fin 6 ⊕ Fin 6 → K),
          (∀ v ∈ T, spinAction (Spin.quadPlus 6 K) b v ∈ T) →
          (∀ v ∈ T, Spin.quadPlus 6 K v = 0) → T = ⊥ := by
        intro T hTb hTs
        refine hNS T (fun e he v hv => ?_) hTs
        obtain ⟨i, rfl⟩ := hmem e he
        rw [map_pow]
        exact OrthBlk.pow_apply_mem hTb i v hv
      obtain ⟨x, hx⟩ := exists_spin_conj_frameGroup_cyclic hodd hn3 (k := 3) (by norm_num) ι6
        hp5p (by norm_num) hpl hord b hb5 hNSb
      refine ⟨x, fun e he => ?_⟩
      obtain ⟨i, rfl⟩ := hmem e he
      rw [← conj_pow]
      exact pow_mem hx i
    · exact exists_spin_conj_frameGroup hodd hn3 (k := 3) (by norm_num) ι6 hp5p (by norm_num)
        hpl hord E₂ hE₂ea.2 h25 hNS
  obtain ⟨x, hx⟩ := hfr
  refine ⟨Ψ x * g, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨⟨a, s⟩, he, hee⟩ := hlift (g * z * g⁻¹) ⟨z, hz, rfl⟩
  have hs : s ∈ E₂ := ⟨(a, s), he, rfl⟩
  have h1 : Ψ (x * s * x⁻¹) ∈ e7FrameGroup K :=
    map_spinFrameGroup_le_e7 hn3 hrank hweyl ⟨_, hx s hs, rfl⟩
  have h2 : ρ a ∈ e7FrameGroup K := rootPairE7_theta_le_e7FrameGroup (hρr ▸ ⟨a, rfl⟩)
  have hee' : ρ a * Ψ s = g * z * g⁻¹ := hee
  have key : (Ψ x * g) * z * (Ψ x * g)⁻¹ = ρ a * Ψ (x * s * x⁻¹) := by
    have h3 : (Ψ x * g) * z * (Ψ x * g)⁻¹ = Ψ x * (g * z * g⁻¹) * (Ψ x)⁻¹ := by group
    rw [h3, ← hee', map_mul, map_mul, map_inv]
    have hc : Ψ x * ρ a = ρ a * Ψ x := (hcomm a x).symm.eq
    calc Ψ x * (ρ a * Ψ s) * (Ψ x)⁻¹ = (Ψ x * ρ a) * Ψ s * (Ψ x)⁻¹ := by group
      _ = ρ a * (Ψ x * Ψ s * (Ψ x)⁻¹) := by rw [hc]; group
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [key]
  exact (e7FrameGroup K).mul_mem h2 h1

end Main

end S3

section S4
open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
  CFSG.ComponentClassification.CatLeafProof CFSG.HardMathSupport.Lang.AnisoE8
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld.LevisExtras
  CFSG.ClassicalInvolution.ModelFacts CoxeterSystem CFSG.LieType.Universal.Spin
  CFSG.StandardType.TableBExcTwo CFSG.HardMathSupport.Lang.AnisoF4 CFSG.Open
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.TauCetiBridge TauCeti CFSG.AGLEmbeddingD2
  CFSG.LieType.SeitzGeneration
open scoped MatrixGroups


section Glue

@[expose] def E7TwoSylowFive : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 5 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
        ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K

@[expose] def E7TwoSylowFiveEven : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Even (Nat.card K) → 5 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ 5 = 1) → Nat.card E₀ = 5 ^ 2 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
        ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K

@[expose] def E7TwoSylowSeven : Prop :=
  ∀ (K : Type) [Field K] [Finite K], 7 ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ 7 = 1) → Nat.card E₀ = 7 ^ 2 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
        ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K

theorem e7TwoSylowFive_of_odd (K : Type) [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (hpq : 5 ∣ Nat.card K + 1) (E₀ : Subgroup (adjointGroup .E7 K))
    (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1) (hE₀c : Nat.card E₀ = 5 ^ 2)
    (hN : ¬ NormalizesRGroup (ringChar K) E₀) :
    ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K :=
  e7_conj_into_frame_five hodd hpq E₀ hE₀p hE₀c hN

theorem e7TwoSylowFive_of_even (h : E7TwoSylowFiveEven) : E7TwoSylowFive := by
  intro K _ _ hpq E₀ hE₀p hE₀c hN
  rcases Nat.even_or_odd (Nat.card K) with he | ho
  · exact h K he hpq E₀ hE₀p hE₀c hN
  · exact e7TwoSylowFive_of_odd K ho hpq E₀ hE₀p hE₀c hN

theorem e7TwoSylowLow_of_five_seven (h5 : E7TwoSylowFive) (h7 : E7TwoSylowSeven) :
    E7TwoSylowLow := by
  intro K _ _ p hpF hp5 hlt hpq E₀ hE₀p hE₀c hN
  have hp : p.Prime := hpF.out
  have h57 : p = 5 ∨ p = 7 := by
    interval_cases p <;> first | omega | (exfalso; revert hp; norm_num)
  rcases h57 with rfl | rfl
  · exact h5 K hpq E₀ hE₀p hE₀c hN
  · exact h7 K hpq E₀ hE₀p hE₀c hN

theorem seitzExcHighE7Two_of_even_seven (h5 : E7TwoSylowFiveEven) (h7 : E7TwoSylowSeven) :
    SeitzExcHighE7Two :=
  seitzExcHighE7Two_of_sylow_low (e7TwoSylowLow_of_five_seven (e7TwoSylowFive_of_even h5) h7)

end Glue

end S4

end CFSG.LieType.SeitzGeneration.ExcHigh

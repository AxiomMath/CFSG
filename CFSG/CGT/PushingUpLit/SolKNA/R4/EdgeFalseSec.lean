module

public import CFSG.ClassicalInvolution.Q3.TL4SecOrbit
public import CFSG.ClassicalInvolution.Q3.TL4Conn26YS
public import CFSG.ClassicalInvolution.Q3.TL4SecIdFam
public import CFSG.ClassicalInvolution.Q3.TL4LinkE2Hyp
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinD2Leaves2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinReduce

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Disconnected (DConnected dAdj DEdgeless)

section Orbits

variable {n r : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem adj_of_not_conjR (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {M N : Subgroup X}
    (hM : M ∈ Φ) (hN : N ∈ Φ) (hnc : ¬ ∃ g ∈ omegaGen Φ, conjSub g M = N) :
    N ∈ Φ ∧ dAdj Φ M N := by
  have hne : N ≠ M := fun e => hnc ⟨1, (omegaGen Φ).one_mem, by rw [conjSub_one, e]⟩
  exact ⟨hN, Or.inl (mem_omegaNbr_of_commutes hN hne
    (Vtx.commutes_of_not_conj h4 h hO hn hM hN hnc))⟩

theorem dConnected_of_not_conjR (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {K L : Subgroup X}
    (hK : K ∈ Φ) (hL : L ∈ Φ) (hKL : ¬ ∃ g ∈ omegaGen Φ, conjSub g K = L) : DConnected Φ := by
  intro M hM N hN
  have adj := fun {A B : Subgroup X} (hA : A ∈ Φ) (hB : B ∈ Φ)
    (hnc : ¬ ∃ g ∈ omegaGen Φ, conjSub g A = B) => adj_of_not_conjR h4 h hO hn hA hB hnc
  by_cases hMN : ∃ g ∈ omegaGen Φ, conjSub g M = N
  · by_cases hMK : ∃ g ∈ omegaGen Φ, conjSub g M = K
    · have hML : ¬ ∃ g ∈ omegaGen Φ, conjSub g M = L := fun hML =>
        hKL (omegaConj_trans (omegaConj_symm hMK) hML)
      have hLN : ¬ ∃ g ∈ omegaGen Φ, conjSub g L = N := fun hLN =>
        hML (omegaConj_trans hMN (omegaConj_symm hLN))
      exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (adj hM hL hML))
        (adj hL hN hLN)
    · have hKN : ¬ ∃ g ∈ omegaGen Φ, conjSub g K = N := fun hKN =>
        hMK (omegaConj_trans hMN (omegaConj_symm hKN))
      exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (adj hM hK hMK))
        (adj hK hN hKN)
  · exact Relation.ReflTransGen.single (adj hM hN hMN)

theorem omegaTransitive_of_not_dstarConnectedR (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {K : Subgroup X}
    (hK : K ∈ Φ) (hc : ¬ T3.DStarConnected Φ) : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L :=
  fun _ hL => by_contra fun hnc =>
    hc (dstarConnected_of_dConnected h.hyp (dConnected_of_not_conjR h4 h hO hn hK hL hnc))

end Orbits

section Datum

variable {n r : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem nonempty_sylow_equivR (h : TypeRFam r Φ) {K : Subgroup X} (hK : K ∈ Φ)
    (S : Sylow 2 ↥K) : Nonempty (↥(S : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2))) := by
  obtain ⟨e⟩ := h.quat K hK _ (isSylow2In_map_subtype K S)
  exact ⟨((S : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans e⟩

theorem tightDatum_of_memR (hr : 3 ≤ r) (h : TypeRFam r Φ) {K : Subgroup X} (hK : K ∈ Φ)
    {z : X} (hz : IsUniqueInvolution K z) (S : Sylow 2 ↥K) : TightDatum K S z where
  quat := ⟨r, hr, nonempty_sylow_equivR h hK S⟩
  mem := T3.mem_of_isPGroup hz (Subgroup.map_subtype_le _) (S.isPGroup'.map _)
    (le_trans (by norm_num) (Sec6Gen.eight_le_of_mem_RSet h.hyp
      (mem_RSet_of_isSylow2In hK (isSylow2In_map_subtype K S))))
  order := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  cent := h.le_centralizer hK hz
  normal := (Subgroup.normal_subgroupOf_iff_le_normalizer (h.le_centralizer hK hz)).mpr
    (h.tight K hK z hz)
  twoGroup := h.twoGroup K hK

theorem exists_datumR_of_omegaTransitive (hr : 3 ≤ r) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤) {K : Subgroup X}
    (hK : K ∈ Φ) (htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L) {z : X}
    (hz : IsUniqueInvolution K z) :
    ∃ S : Sylow 2 ↥K, TightDatum K S z ∧ TightClsR r X K S z ∧
      CoreAssembly.conjClass (tightCore K) = Φ := by
  have htr' : ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := fun L hL => by
    obtain ⟨g, -, hg⟩ := htr L hL
    exact ⟨g, hg⟩
  have hcore : tightCore K = K := h.closure_twoElts hK
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  refine ⟨S, tightDatum_of_memR hr h hK hz S, ⟨nonempty_sylow_equivR h hK S, ?_, hO⟩, ?_⟩
  · show (⨆ g : X, conjSub g (tightCore K)) = ⊤
    rw [hcore, eq_top_iff, ← hgen]
    refine iSup₂_le fun L hL => ?_
    obtain ⟨g, rfl⟩ := htr' L hL
    exact le_iSup (fun g : X => conjSub g K) g
  · rw [hcore]
    ext L
    constructor
    · rintro ⟨g, rfl⟩
      exact h.hyp.conjInvariant g K hK
    · intro hL
      exact htr' L hL

theorem tightClsR_orbGrp (hr : 3 ≤ r) (h4 : Thm4RBelow r n) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n) {K : Subgroup X}
    (hK : K ∈ Φ) {z : X} (hz : IsUniqueInvolution K z) :
    ∃ S' : Sylow 2 ↥(K.subgroupOf (Vtx.orbGrp Φ K)),
      TightDatum (K.subgroupOf (Vtx.orbGrp Φ K)) S' ⟨z, Vtx.le_orbGrp K hz.mem⟩ ∧
        TightClsR r ↥(Vtx.orbGrp Φ K) (K.subgroupOf (Vtx.orbGrp Φ K)) S'
          ⟨z, Vtx.le_orbGrp K hz.mem⟩ := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥K))
  have hd := tightDatum_of_memR hr h hK hz S
  have hcl := h.hyp.conjInvariant
  have hKX : K ≤ Vtx.orbGrp Φ K := Vtx.le_orbGrp K
  obtain ⟨S', hd', ⟨e⟩⟩ :=
    hd.restrict (H := Vtx.orbGrp Φ K) ((Subgroup.map_subtype_le _).trans hKX)
  refine ⟨S', hd', ⟨e.trans (nonempty_sylow_equivR h hK S).some⟩, ?_, ?_⟩
  · have hcore : tightCore (K.subgroupOf (Vtx.orbGrp Φ K)) = K.subgroupOf (Vtx.orbGrp Φ K) := by
      rw [tightCore_subgroupOf ((tightCore_le K).trans hKX)]
      congr 1
      exact h.closure_twoElts hK
    show (⨆ g : ↥(Vtx.orbGrp Φ K), conjSub g (tightCore (K.subgroupOf (Vtx.orbGrp Φ K)))) = ⊤
    rw [hcore]
    apply Subgroup.map_injective (Vtx.orbGrp Φ K).subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : ∀ g : ↥(Vtx.orbGrp Φ K), (conjSub g (K.subgroupOf (Vtx.orbGrp Φ K))).map
        (Vtx.orbGrp Φ K).subtype = conjSub (g : X) K := by
      intro g
      rw [conjSub_subgroupOf, Subgroup.map_subgroupOf_eq_of_le]
      exact Vtx.conjSub_le_orbGrp K ⟨g, Vtx.orbGrp_le hcl hK g.2⟩
    simp_rw [e2]
    exact (Vtx.orbGrp_eq_iSup hcl hK (Vtx.commute_conj_of_not_conj h4 h hO hn hK)).symm
  · exact oddCore_eq_bot_of_isSubnormal (Vtx.isSubnormal_orbGrp hcl hK) hO

end Datum

section DStar

variable {n r : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem dstarConnected_of_inO2_four_le (hr : 4 ≤ r) (h : TypeRFam r Φ)
    (hO : classicalInvolutionOddCore X = ⊥) (hA : ∀ L ∈ Φ, AEmpty Φ L)
    (hin : ∀ L ∈ Φ, ∀ u : X, IsUniqueInvolution L u →
      ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 Q ∧ u ∈ Q) :
    T3.DStarConnected Φ := by
  have h2 : ∀ L ∈ Φ, IsPGroup 2 L := fun L hL => by
    obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
    obtain ⟨Q, hQn, hQ2, huQ⟩ := hin L hL u hu
    exact LinkE2.isPGroup_of_inO2_typeR h hO hL hu hQn hQ2 huQ
  have h8 : ∀ L ∈ Φ, Nat.card L = 2 ^ r := fun L hL => by
    obtain ⟨e⟩ := h.quat L hL L (AlphaFr.E2A.isSylow2In_self (h2 L hL))
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    rw [Nat.add_sub_cancel, pow_add]
    ring
  intro K hK J hJ
  show Relation.ReflTransGen (dstarAdj Φ) K J
  by_cases hJK : J = K
  · rw [hJK]
  · obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
    exact Relation.ReflTransGen.single ⟨hJ, Or.inl
      (mem_omegaStarNbr_of_normalizes h.hyp h2 h8 hA hO hin hK hJ hJK hz
        (mem_normalizer_of_four_le hr h.hyp h2 h8 hin hJ hK hz))⟩

section Cit3


theorem inO2_of_edge_four_le (hr : 4 ≤ r) (hB : TightBelowR r n) (hNo : NoQ16E4)
    {Y : Type} [Group Y] [Finite Y] (hn : Nat.card Y < n) {R : Subgroup Y} {S : Sylow 2 R}
    {t : Y} (hd : TightDatum R S t) (hc : TightClsR r Y R S t) (hne : ¬ TightEdgeless R) :
    TightInO2 t := by
  have hex := (hB Y hn R S t hd hc).resolve_right (not_goodThreeElement_of_four_le hr hd hc.1)
  rcases hex with h2 | ⟨he, -⟩ | ⟨he, -⟩ | ⟨Q, hQ, f, hfs, hf2, -, hm⟩
  · exact h2
  · exact absurd he hne
  · exact absurd he hne
  · exact tightInO2_of_twinE4' hr hNo (PhilipHall.QuaternionBridge.TightDatum.toQ8TwinDatum hd)
      hc.1 ⟨Q, hQ, f, hfs, hf2, hm⟩

theorem inO2_of_omegaTransitive_four_le (hr : 4 ≤ r) (hB : TightBelowR r n) (hNo : NoQ16E4)
    (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore X = ⊥) (hn : Nat.card X < n)
    (hgen : omegaGen Φ = ⊤) {K : Subgroup X} (hK : K ∈ Φ)
    (htr : ∀ L ∈ Φ, ∃ g ∈ omegaGen Φ, conjSub g K = L) (hedge : ¬ DEdgeless Φ) {z : X}
    (hz : IsUniqueInvolution K z) : TightInO2 z := by
  obtain ⟨S, hd, hc, hfam⟩ := exists_datumR_of_omegaTransitive (by omega) h hO hgen hK htr hz
  refine inO2_of_edge_four_le hr hB hNo hn hd hc ?_
  unfold TightEdgeless
  rw [hfam]
  exact hedge

theorem dstarConnected_of_edge_four_le (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (hNo : NoQ16E4) (h : TypeRFam r Φ) (hO : classicalInvolutionOddCore X = ⊥)
    (hn : Nat.card X < n) (hgen : omegaGen Φ = ⊤) (hA : ∀ L ∈ Φ, AEmpty Φ L)
    (hedge : ¬ DEdgeless Φ) : T3.DStarConnected Φ := by
  by_contra hc
  have hex : ∃ K ∈ Φ, ∃ J ∈ Φ, dAdj Φ K J := by
    by_contra hno
    push Not at hno
    exact hedge hno
  obtain ⟨K, hK, -⟩ := hex
  have htr := omegaTransitive_of_not_dstarConnectedR h4 h hO hn hK hc
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hK
  obtain ⟨P, hPn, hP2, hzP⟩ := inO2_of_omegaTransitive_four_le hr hB hNo h hO hn hgen hK htr
    hedge hz
  refine hc (dstarConnected_of_inO2_four_le hr h hO hA fun L hL u hu => ?_)
  obtain ⟨g, -, rfl⟩ := htr L hL
  refine ⟨P, hPn, hP2, ?_⟩
  rw [← (hz.conj g).eq hu]
  exact hPn.conj_mem z hzP g

theorem tightSecTriangleR_of_four_le (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (hNo : NoQ16E4) : TightSecTriangleR r n := by
  intro X _ _ hn Φ h hO hgen hA B hBΦ _ hadj
  exact dstarConnected_of_edge_four_le hr h4 hB hNo h hO hn hgen hA fun he =>
    he (B 0) (hBΦ 0) (B 1) (hBΦ 1) (Or.inl (hadj 0 1 (by decide)))

theorem tightE4SecGenR_of_four_le (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (hNo : NoQ16E4) : TightE4SecGenR r n := by
  intro X _ _ hn Φ h hO hgen hA hnc A hA' B' hB'
  exfalso
  exact hnc (dstarConnected_of_edge_four_le hr h4 hB hNo h hO hn hgen hA fun he =>
    he A hA' B' hB'.1 (Or.inl hB'))

theorem tightSecNoRootR_of_four_le (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (hNo : NoQ16E4) : TightSecNoRootR r n := by
  intro X _ _ hn Φ h hO hgen hA hnc A hA' B' hB'
  exfalso
  exact hnc (dstarConnected_of_edge_four_le hr h4 hB hNo h hO hn hgen hA fun he =>
    he A hA' B' hB'.1 (Or.inl hB'))

theorem tightSecExactR_of_four_le (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (hNo : NoQ16E4) : TightSecExactR r n := by
  intro X _ _ hn Φ h hO hgen _ L hL M hM ⟨g, hg⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution h.hyp hL
  obtain ⟨S', hd, hc⟩ := tightClsR_orbGrp (by omega) h4 h hO hn hL hz
  have hne := not_tightEdgeless_orbGrp h4 h hO hn hL hM
    (by rw [hgen]; exact Subgroup.mem_top g) hg
  have hlt : Nat.card ↥(Vtx.orbGrp Φ L) < n :=
    lt_of_le_of_lt (Subgroup.card_le_card_group _) hn
  have h2 := isPGroup_of_inO2 hd hc.2.2 (inO2_of_edge_four_le hr hB hNo hlt hd hc hne)
  exact oddCore_eq_bot_of_isPGroup
    (h2.of_equiv (Subgroup.subgroupOfEquivOfLe (Vtx.le_orbGrp L)))

theorem tightLambdaCommR_of_four_le (hr : 4 ≤ r) (h4 : Thm4RBelow r n) (hB : TightBelowR r n)
    (hNo : NoQ16E4) : TightLambdaCommR r n :=
  tightLambdaCommR_of_exact (tightSecExactR_of_four_le hr h4 hB hNo) h4

end Cit3

end DStar

end CFSG.CGT.PushingUpLit.SolKNA.R4

module

public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAEQ
public import CFSG.ClassicalInvolution.Q3.TL4Conn278ANMu
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Quot
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Tri
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DEdgeless)

variable {H : Type} [Group H] [Finite H] {Φ : Set (Subgroup H)}

theorem z2_eq_of_ne_one : ∀ x y : Multiplicative (ZMod 2), x ≠ 1 → y ≠ 1 → x = y := by decide

theorem exists_commuting_sylow_pair_gen (hΦ : HypOmegaGen Φ) {K J : Subgroup H} (hK : K ∈ Φ)
    (hJ : J ∈ omegaNbr Φ K) :
    ∃ (R T : Subgroup H) (S : Sylow 2 H), IsSylow2In R K ∧ IsSylow2In T J ∧
      R ≤ (S : Subgroup H) ∧ T ≤ (S : Subgroup H) ∧ Commutes R T := by
  obtain ⟨hJΦ, hne, T, hT, hTJ, hTN⟩ := hJ
  have hTsyl : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΦ hJΦ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := exists_sylow_normalized hTsyl.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set H) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTsyl.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  have hRS : R ≤ (S : Subgroup H) := le_sup_right.trans hS
  have hTS : T ≤ (S : Subgroup H) := le_sup_left.trans hS
  have hRT : R ≠ T := by
    intro e
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΦ hT
    exact hne (Sec6Gen.eq_of_le_of_le hΦ hJΦ hK hTsyl.2.1 (by omega) hTJ (e ▸ hRK.1))
  exact ⟨R, T, S, hRK, hTsyl, hRS, hTS,
    Q3CP.l67Gen H Φ hΦ S R (mem_RSet_of_isSylow2In hK hRK) T hT hRS hTS hRT⟩

theorem dEdgeless_of_muIsoZ2_gen (hP : Q3CL.PartIHypG Φ) {W' : Subgroup H}
    (hW' : W' ∈ WSet Φ) (hZ : MuIsoZ2 Φ W') : DEdgeless Φ := by
  have hΦ : HypOmegaGen Φ := hP.hyp
  have key : ∀ K ∈ Φ, ∀ J ∈ omegaNbr Φ K, False := by
    intro K hK J hJ
    obtain ⟨R, T, S, hRsyl, hTsyl, hRS, hTS, -⟩ := exists_commuting_sylow_pair_gen hΦ hK hJ
    obtain ⟨g, hgW, hgS, hgN⟩ := exists_conjSub_wset_le hΦ.conjInvariant hW' S
    have hRD : R ∈ DSet Φ (conjSub g W') := ⟨mem_RSet_of_isSylow2In hK hRsyl, fun x hx =>
      mem_normalizer_iff_conjSub_eq.mpr (hgN x (hRS hx))⟩
    have hTD : T ∈ DSet Φ (conjSub g W') := ⟨mem_RSet_of_isSylow2In hJ.1 hTsyl, fun x hx =>
      mem_normalizer_iff_conjSub_eq.mpr (hgN x (hTS hx))⟩
    have c := Q3CL.T8.ctxOf hP hgW
    obtain ⟨r₀, hr₀, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΦ hgW hRD
    obtain ⟨t₀, ht₀, ht₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D hΦ hgW hTD
    let ρ : Rep Φ (conjSub g W') := ⟨K, R, r₀, hK, hRD, hRsyl, hr₀, hr₀W⟩
    let σ : Rep Φ (conjSub g W') := ⟨J, T, t₀, hJ.1, hTD, hTsyl, ht₀, ht₀W⟩
    have hne : T8.repElt ρ ≠ T8.repElt σ := fun e =>
      hJ.2.1 ((repElt_eq_iff_gen c ρ σ).mp e).symm
    obtain ⟨φ⟩ := hZ
    let e2 := (muGroupConjEquivGen hΦ g W').symm.trans φ
    have h1 : e2 (T8.repElt ρ) ≠ 1 := fun h =>
      muDelta_ne_one hgW (T8.repElt_mem ρ) (e2.injective (by rw [h, map_one]))
    have h2 : e2 (T8.repElt σ) ≠ 1 := fun h =>
      muDelta_ne_one hgW (T8.repElt_mem σ) (e2.injective (by rw [h, map_one]))
    exact hne (e2.injective (z2_eq_of_ne_one _ _ h1 h2))
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact key K hK J h
  · exact key J hJ K h

theorem muIsoZ2_of_unique_member_gen (hP : Q3CL.PartIHypG Φ) {W : Subgroup H}
    (hW : W ∈ WSet Φ) {J₀ : Subgroup H} (hJ₀ : J₀ ∈ Φ) (h : ∀ ρ : Rep Φ W, ρ.K = J₀) :
    MuIsoZ2 Φ W := by
  obtain ⟨-, ρ₀, -⟩ := Q3T6.Mu.exists_rep hP hW hJ₀
  have c := Q3CL.T8.ctxOf hP hW
  have hall : ∀ d ∈ muDelta Φ W, d = T8.repElt ρ₀ := by
    intro d hd
    obtain ⟨ρ, rfl⟩ := T8.exists_rep_of_mem_muDelta hd
    exact (repElt_eq_iff_gen c ρ ρ₀).mpr (by rw [h ρ, h ρ₀])
  have h2 : T8.repElt ρ₀ * T8.repElt ρ₀ = 1 :=
    Q3T8.Asc77.Thompson.muDelta_mul_self hP.hyp hW (T8.repElt_mem _)
  have h1 : T8.repElt ρ₀ ≠ 1 := muDelta_ne_one hW (T8.repElt_mem _)
  refine MuTab.nonempty_mulEquiv_z2 h2 h1 ?_
  rw [eq_top_iff, ← closure_muDelta_eq_top Φ W]
  refine (Subgroup.closure_le _).mpr fun d hd => ?_
  rw [hall d hd]
  exact Subgroup.subset_closure rfl

theorem eq_image_of_mem_USet_le_sylow_gen {Λ : Set (Subgroup H)} (hΛ : HypOmegaGen Λ)
    (hΦ : HypOmegaGen (oddQuotientFamily Λ)) (S : Sylow 2 H) (J₀ : Subgroup H)
    (hK1 : ∀ L ∈ Λ, 2 < Nat.card ↥(L ⊓ (S : Subgroup H)) → L = J₀)
    {M : Subgroup (H ⧸ classicalInvolutionOddCore H)} (hM : M ∈ oddQuotientFamily Λ)
    {Ub : Subgroup (H ⧸ classicalInvolutionOddCore H)}
    (hUb : Ub ∈ USet (oddQuotientFamily Λ)) (hUbM : Ub ≤ M)
    (hUbS : Ub ≤ (S : Subgroup H).map (QuotientGroup.mk' (classicalInvolutionOddCore H))) :
    M = J₀.map (QuotientGroup.mk' (classicalInvolutionOddCore H)) := by
  set N := classicalInvolutionOddCore H with hNdef
  have hN : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card H
  obtain ⟨J, hJ, rfl⟩ := hM
  obtain ⟨U, hU, hUJ, hUmap⟩ := Q3T7.exists_lift_USet3 hΦ hN hJ hUb hUbM
  have hUSN : U ≤ (S : Subgroup H) ⊔ N := by
    intro u hu
    have h1 : QuotientGroup.mk' N u ∈ (S : Subgroup H).map (QuotientGroup.mk' N) :=
      hUbS (hUmap ▸ Subgroup.mem_map_of_mem _ hu)
    have h2 : u ∈ Subgroup.comap (QuotientGroup.mk' N) ((S : Subgroup H).map
        (QuotientGroup.mk' N)) := h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hU2 : IsPGroup 2 U := Sec6Gen.isPGroup_of_mem_USet hΛ hU
  obtain ⟨n, hn, hUn⟩ := exists_conj_le_of_le_sup hN hU2 hUSN
  have hJ' : conjSub n J ∈ Λ := hΛ.conjInvariant _ J hJ
  have hU4 : 4 ≤ Nat.card U := by
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΛ hU
    exact h4
  have hle : conjSub n U ≤ conjSub n J ⊓ (S : Subgroup H) := le_inf (conjSub_mono hUJ) hUn
  have hcard : 2 < Nat.card ↥(conjSub n J ⊓ (S : Subgroup H)) := by
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card ↥(conjSub n U) = Nat.card ↥U :=
      Subgroup.card_map_of_injective (MulAut.conj n).injective
    omega
  have hJeq : conjSub n J = J₀ := hK1 _ hJ' hcard
  have hJn : J = conjSub n⁻¹ J₀ := by
    rw [← hJeq, conjSub_inv_conjSub]
  have hnN : QuotientGroup.mk' N n⁻¹ = 1 := (QuotientGroup.eq_one_iff _).mpr (N.inv_mem hn)
  rw [hJn, AscQuot.map_conjSub, hnN, conjSub_one]

theorem exists_muIsoZ2_of_sylow_gen {Λ : Set (Subgroup H)} (hΛ : HypOmegaGen Λ)
    (hP : Q3CL.PartIHypG (oddQuotientFamily Λ)) (S : Sylow 2 H) {J₀ : Subgroup H}
    (hJ₀ : J₀ ∈ Λ) (hK1 : ∀ L ∈ Λ, 2 < Nat.card ↥(L ⊓ (S : Subgroup H)) → L = J₀) :
    ∃ W' ∈ WSet (oddQuotientFamily Λ), MuIsoZ2 (oddQuotientFamily Λ) W' := by
  have hΦ : HypOmegaGen (oddQuotientFamily Λ) := hP.hyp
  set N := classicalInvolutionOddCore H with hNdef
  set π := QuotientGroup.mk' N with hπ
  set S' : Sylow 2 (H ⧸ N) := Sylow.mapSurjective (QuotientGroup.mk'_surjective N) S with hS'def
  have hS' : (S' : Subgroup (H ⧸ N)) = (S : Subgroup H).map π := Sylow.coe_mapSurjective _ _
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΦ S'
  have hηG : η ∈ etaG (oddQuotientFamily Λ) := ⟨S', hη, hinv⟩
  set W' : Subgroup (H ⧸ N) := ⨆ U ∈ η, U with hW'def
  have hW' : W' ∈ WSet (oddQuotientFamily Λ) := ⟨η, hηG, rfl⟩
  refine ⟨W', hW', ?_⟩
  refine muIsoZ2_of_unique_member_gen hP hW' (J₀ := J₀.map π) ⟨J₀, hJ₀, rfl⟩ fun ρ => ?_
  have hW2 : IsPGroup 2 W' := isPGroup_of_mem_WSet hW'
  have hR2 : IsPGroup 2 ρ.R := ρ.hRK.2.1
  have hRN : ρ.R ≤ Subgroup.normalizer (W' : Set (H ⧸ N)) := ρ.hR.2
  have hRW : IsPGroup 2 ↥(ρ.R ⊔ W') := hR2.to_sup_of_normal_right' hW2 hRN
  obtain ⟨S'', hS''⟩ := hRW.exists_le_sylow
  have hηS'' : ∀ V ∈ η, V ≤ (S'' : Subgroup (H ⧸ N)) := fun V hV =>
    (le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV).trans (le_sup_right.trans hS'')
  have hcard : 2 < Nat.card ↥(ρ.K ⊓ (S'' : Subgroup (H ⧸ N))) := by
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΦ ρ.hR.1
    have h1 := Subgroup.card_le_of_le (le_inf ρ.hRK.1 (le_sup_left.trans hS''))
    omega
  have h611 := Sec6Gen.l6_11Gen (H ⧸ N) (oddQuotientFamily Λ) hΦ S'' η hηG hηS'' ρ.K ρ.hK
    hcard
  have hV := hη.1 h611
  exact eq_image_of_mem_USet_le_sylow_gen hΛ hΦ S J₀ hK1 ρ.hK hV.1 inf_le_left (hS' ▸ hV.2)

theorem exists_rep_of_involution_mem_gen {W : Subgroup H} (c : Q3CL.Thompson.Ctx Φ W)
    (hcl : Q3CL.ClassicalClause Φ) {J : Subgroup H} (hJ : J ∈ Φ) {t : H}
    (ht : IsUniqueInvolution J t) (htW : t ∈ W) : ∃ ρ : Rep Φ W, ρ.K = J := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet c.hW
  have hWC : W ≤ Subgroup.centralizer ({t} : Set H) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (c.comm_W w hw t htW)
  obtain ⟨T, hT, hWT⟩ := IsSylow2In.exists_ge hW2 hWC
  have hR : IsSylow2In (T ⊓ J) J :=
    AscP1Nine3.isSylow2In_inf_of_isSubnormal hT (hcl.isSubnormal_of_uniqueInvolution hJ ht)
  obtain ⟨S, hTS⟩ := hT.2.1.exists_le_sylow
  have hRD : T ⊓ J ∈ DSet Φ W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow c.hΩ c.hW (hWT.trans hTS) (mem_RSet_of_isSylow2In hJ hR)
      (inf_le_left.trans hTS)
  obtain ⟨r₀, hr₀, hr₀W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D c.hΩ c.hW hRD
  exact ⟨⟨J, T ⊓ J, r₀, hJ, hRD, hR, hr₀, hr₀W⟩, rfl⟩

end CFSG.ClassicalInvolution.Q3.TL4

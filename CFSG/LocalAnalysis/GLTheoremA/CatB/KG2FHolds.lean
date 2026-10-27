module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KG2F
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I91T4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Holds
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Catalog.Realization

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KG2F

namespace Holds

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open scoped commutatorElement


theorem finite_card_of_isG2n_two {T : Type} [Group T] (hT : catalogIs T (isG2n 2)) :
    Finite T ∧ Nat.card T = 251596800 := by
  obtain ⟨-, ⟨e⟩⟩ := T266.G2Holds.g2_adjoint_equiv hT
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := GaloisField 2 2)
  rw [hK] at h
  have hord : CFSG.Open.ordG2 4 = 251596800 := by
    unfold CFSG.Open.ordG2
    norm_num
  haveI : Finite (ModGL .G2 (GaloisField 2 2)) := inferInstance
  refine ⟨Finite.of_equiv _ e.toEquiv, ?_⟩
  rw [← Nat.card_congr e.toEquiv, h, hord]

theorem commutator_eq_top_of_isG2n_two {T : Type} [Group T] (hT : catalogIs T (isG2n 2)) :
    commutator T = ⊤ := by
  obtain ⟨-, ⟨e⟩⟩ := T266.G2Holds.g2_adjoint_equiv hT
  have hK : 3 ≤ Nat.card (GaloisField 2 2) := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h := CFSG.TauCetiBridge.Even.commutator_adjointGroup_eq_of_three_le .G2 (GaloisField 2 2) hK
  have hA : commutator ↥(adjointGroup .G2 (GaloisField 2 2)) = ⊤ := by
    apply Subgroup.map_injective (adjointGroup .G2 (GaloisField 2 2)).subtype_injective
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, h]
  have hmap : (commutator ↥(adjointGroup .G2 (GaloisField 2 2))).map e.toMonoidHom = commutator T := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [← hmap, hA, Subgroup.map_top_of_surjective _ e.surjective]

theorem catalogIs_isG2n_of_markedModel {S : Type} [Group S] {m : ℕ} (hm : 2 ≤ m)
    (h : MarkedModel ⟨.G2, 0, m⟩ S) : catalogIs S (isG2n m) := by
  have hL : CFSG.Blueprint.LieModel S .G2 0 2 m := h
  rcases hL with ⟨hc, -⟩ | ⟨-, -, hE⟩ | ⟨-, hr, -⟩ | ⟨-, ht, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hE
    let q : TauCeti.PrimePower := ⟨2, m, Nat.prime_two, by omega⟩
    have hq : q.card = 2 ^ m := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
      refine (TauCeti.LieTypeIndex.valid_iff _).2 ⟨?_, ?_⟩
      · rw [TauCeti.LieTypeIndex.inStandardRange_iff]
        show 3 ≤ q.card
        rw [hq]
        calc 3 ≤ 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      · simp [TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    obtain ⟨b⟩ := CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv rfl K (by rw [hK, hq])
    exact ⟨.lie ⟨_, hv⟩, ⟨rfl, rfl⟩, ⟨e.trans b⟩⟩
  · exact absurd hr (by decide)
  · exact absurd ht (by decide)

end Holds

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.GLTheoremA.CatB.KG2F.Holds
open scoped commutatorElement


theorem g2FieldLayerS_holds : G2FieldLayerS := by
  intro S _ hS β hM J hJC hJsn T _ hT hφ
  obtain ⟨φ, hφs⟩ := hφ
  obtain ⟨hTfin, hTcard⟩ := finite_card_of_isG2n_two hT
  have hTperf := commutator_eq_top_of_isG2n_two hT
  haveI : Nontrivial T := by
    rw [← Finite.one_lt_card_iff_nontrivial, hTcard]
    norm_num
  have h := FP.canon_marking_and_labelAll_simple'
    (P' := fun lab R _ I F => (¬ (lab.tag = .triD4 ∧ (3 : ℕ) = 3) → FR.SubfieldBody 3 lab R I F) ∧
      RawInnBody 3 R I F)
    (fun lab hlab => by
      have h1 : CAll lab (LargeEvenSimpleGuard fun R _ I F =>
          ¬ (lab.tag = .triD4 ∧ (3 : ℕ) = 3) → FR.SubfieldBody 3 lab R I F) := by
        by_cases h3 : lab.tag = .triD4 ∧ (3 : ℕ) = 3
        · exact (canonRawInnAny (p := 3) (by norm_num) hlab).mono fun R _ I F _ _ _ h => absurd h3 h
        · exact (FR.canonSubfield Nat.prime_three (by norm_num) hlab h3).mono
            fun R _ I F h' hs hna _ => h' hs hna
      exact (h1.and (canonRawInn' Nat.prime_three (by norm_num) hlab)).mono
        fun R _ I F ⟨ha, hb⟩ hs hna => ⟨ha hs hna, hb hs hna⟩) hM
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, ⟨hP, hSub, hRI⟩, hMM⟩ :=
    Canonical.largeEvenMarking_exists_markedModel h
  obtain ⟨hne, f, hf, u, hu, hord, hind⟩ := hP
  have h3 : ¬ (lab.tag = .triD4 ∧ (3 : ℕ) = 3) := by
    rintro ⟨ht, -⟩
    rcases hne with h0 | h0
    · exact h0 ht
    · exact h0 rfl
  obtain ⟨hpn, D, hD, hdat⟩ := hSub h3 f hf hord
  obtain ⟨hmul, hinv, hconj, hFI⟩ := hRI
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h0
    · exact h0
    · exfalso
      have hc : commutator S = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top x) y)
      have htop := hM.1
      rw [hc] at htop
      haveI : Nontrivial S := IsSimpleGroup.toNontrivial
      exact bot_ne_top htop
  set θ' : S ≃* R :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans θ with hθ'
  have hθ'mk : ∀ s : S, θ' s = θ (QuotientGroup.mk s) := fun s => rfl
  have hβ : ∀ s : S, (u * f * u⁻¹) (θ' s) = θ' (β s) := by
    intro s
    rw [hθ'mk, hθ'mk]
    exact hind s (β s) rfl
  have hcongr : MulAut.congr θ' β = u * f * u⁻¹ := by
    ext x
    have := hβ (θ'.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [this]
    simp [MulAut.congr_apply]
  haveI hRfin : Finite R := (CFSG.LieType.Catalog.lieModel_finite_simple R _ _ _ _ hMM).1
  haveI : Finite S := Finite.of_equiv _ θ'.symm.toEquiv
  have hDu : FR.SubfieldGrp (u * f * u⁻¹) (D.map (u : R ≃* R).toMonoidHom) :=
    FR.subfieldGrp_map (u : R ≃* R) (fun x => by simp) hD
  have hDS : FR.SubfieldGrp β ((D.map (u : R ≃* R).toMonoidHom).map θ'.symm.toMonoidHom) := by
    refine FR.subfieldGrp_map θ'.symm (f := u * f * u⁻¹) (fun x => ?_) hDu
    have := hβ (θ'.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [this, MulEquiv.symm_apply_apply]
  set DS : Subgroup S := (D.map (u : R ≃* R).toMonoidHom).map θ'.symm.toMonoidHom with hDSdef
  let eD : ↥DS ≃* ↥D :=
    (FR.equivMapEquiv θ'.symm _).symm.trans (FR.equivMapEquiv (u : R ≃* R) D).symm
  obtain ⟨hDSC, hDScomm, -⟩ := hDS
  set c : Subgroup ↥J := commutator ↥J with hc
  set J₁ : Subgroup S := c.map J.subtype with hJ₁
  have hJ₁comm : J₁ = ⁅J, J⁆ := by
    rw [hJ₁, hc, commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hJ₁J : J₁ ≤ J := by
    rw [hJ₁]
    exact Subgroup.map_subtype_le c
  have hJ₁D : J₁ ≤ DS := by
    rw [hJ₁comm]
    exact (Subgroup.commutator_mono hJC hJC).trans hDScomm
  let eJ₁ : ↥c ≃* ↥J₁ := c.equivMapOfInjective J.subtype J.subtype_injective
  let ψ : ↥J₁ →* T := (φ.comp c.subtype).comp eJ₁.symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    have hrange : (φ.comp c.subtype).range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hc, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hφs, ← commutator_def, hTperf]
    intro t
    have ht : t ∈ (φ.comp c.subtype).range := by rw [hrange]; trivial
    obtain ⟨x, hx⟩ := ht
    refine ⟨eJ₁ x, ?_⟩
    show (φ.comp c.subtype) (eJ₁.symm (eJ₁ x)) = t
    rw [MulEquiv.symm_apply_apply]
    exact hx
  have hJ₁ne : J₁ ≠ ⊥ := by
    intro h0
    obtain ⟨t, ht⟩ := exists_ne (1 : T)
    obtain ⟨x, rfl⟩ := hψ t
    apply ht
    have hx : x = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall J₁).1 h0 x x.2)
    rw [hx, map_one]
  have hTle : Nat.card T ≤ Nat.card J₁ := Nat.card_le_card_of_surjective ψ hψ
  have hJ₁sn : CFSG.Open.IsSubnormal J₁ (FP.fixSub β) := by
    refine CFSG.Open.IsSubnormal.step hJ₁J ?_ hJsn
    have hsub : J₁.subgroupOf J = c := Subgroup.comap_map_eq_self_of_injective J.subtype_injective c
    rw [hsub, hc]
    infer_instance
  rcases hdat with hdat | hexc
  · by_cases hΛ : LargeEvenInLambda2 ⟨lab.tag, lab.rank, lab.n / 3⟩
    ·
      have hG : lab.tag ≠ .G2der := by
        intro hg
        obtain ⟨t, r, n⟩ := lab
        dsimp only at hg hpn hlab
        subst hg
        have hn1 : n = 1 := hlab.2.2
        rw [hn1] at hpn
        exact absurd hpn (by norm_num)
      have hnaJ₁ : ∃ x y : ↥J₁, x * y ≠ y * x := by
        by_contra hcon
        push Not at hcon
        have hTc : commutator T = ⊥ := by
          rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro a _
          rw [Subgroup.mem_centralizer_iff]
          intro b _
          obtain ⟨x, rfl⟩ := hψ a
          obtain ⟨y, rfl⟩ := hψ b
          rw [← map_mul, ← map_mul, hcon y x]
        rw [hTperf] at hTc
        exact bot_ne_top hTc.symm
      have hnaD : ∃ x y : ↥D, x * y ≠ y * x := by
        obtain ⟨x, y, hxy⟩ := hnaJ₁
        refine ⟨eD (Subgroup.inclusion hJ₁D x), eD (Subgroup.inclusion hJ₁D y), fun h => hxy ?_⟩
        apply Subgroup.inclusion_injective hJ₁D
        apply eD.injective
        rw [map_mul, map_mul, map_mul, map_mul]
        exact h
      obtain ⟨hDs, hDM⟩ := I91T.simple_of_datum hΛ hG hnaD hdat
      haveI : IsSimpleGroup ↥D := hDs
      haveI : IsSimpleGroup ↥DS := eD.isSimpleGroup
      have hsn : CFSG.Open.IsSubnormal J₁ DS := by
        have := GL83.PiGen.isSubnormal_inf_right hJ₁sn DS
        rwa [inf_eq_left.2 hJ₁D, inf_eq_right.2 hDSC] at this
      have hJ₁DS : J₁ = DS := (GL83.PiGen.eq_bot_or_eq_of_isSubnormal hsn rfl).resolve_left hJ₁ne
      let ψD : ↥DS →* T := ψ.comp (MulEquiv.subgroupCongr hJ₁DS).symm.toMonoidHom
      have hψD : Function.Surjective ψD := hψ.comp (MulEquiv.surjective _)
      have hψDinj : Function.Injective ψD := by
        rw [← MonoidHom.ker_eq_bot_iff]
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψD.ker with h0 | h0
        · exact h0
        · exfalso
          obtain ⟨t, ht⟩ := exists_ne (1 : T)
          obtain ⟨x, rfl⟩ := hψD t
          exact ht ((h0 ▸ Subgroup.mem_top x : x ∈ ψD.ker))
      let eDT : ↥D ≃* T := eD.symm.trans (MulEquiv.ofBijective ψD ⟨hψDinj, hψD⟩)
      have hTM : MarkedModel ⟨lab.tag, lab.rank, lab.n / 3⟩ T := MarkedModel.of_mulEquiv eDT hDM
      obtain ⟨-, hTG⟩ := HG2Inn.markedModel_g2_of_catalog hT
      have hlab' := HG2Inn.label_eq_g2 hΛ hTM hTG
      obtain ⟨t, r, m⟩ := lab
      simp only [LargeEvenLabel.mk.injEq] at hlab'
      obtain ⟨rfl, rfl, hm⟩ := hlab'
      have hm6 : m = 6 := by
        obtain ⟨k, hk⟩ := hpn
        subst hk
        omega
      subst hm6
      exact catalogIs_isG2n_of_markedModel (by norm_num) (MarkedModel.of_mulEquiv θ'.symm hMM)
    ·
      exfalso
      have hsmall := I91T.smallDatumOrder_holds 3 lab ↥D Nat.prime_three hlab hpn hΛ hdat
      have h1 : Nat.card J₁ ≤ Nat.card DS := Subgroup.card_le_of_le hJ₁D
      have h2 : Nat.card DS = Nat.card D := Nat.card_congr eD.toEquiv
      omega
  · rcases hexc with ⟨-, -, hsol⟩ | ⟨htag, hn⟩
    ·
      exfalso
      haveI := hsol
      haveI : Group.IsSolvable ↥DS :=
        Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective
      haveI : Group.IsSolvable ↥J₁ :=
        Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJ₁D)
      haveI : Group.IsSolvable T := Group.isSolvable_of_surjective hψ
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial T).ne hTperf
    ·
      exfalso
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hf3 : f ^ 3 = 1 := hord ▸ pow_orderOf_eq_one f
      have hnotI : u * f * u⁻¹ ∉ I := FP.not_mem_of_conj_field hmul hinv hu (hFI f hf hord)
      have hβ3 : β ^ 3 = 1 := by
        apply (MulAut.congr θ').injective
        rw [map_pow, hcongr, conj_pow, hf3, mul_one, mul_inv_cancel, map_one]
      have hβ1 : β ≠ 1 := by
        intro h1
        apply hnotI
        rw [← hcongr, h1, map_one, ← map_one (MulAut.conj : R →* MulAut R)]
        exact hconj 1
      have hβord : orderOf β = 3 := orderOf_eq_prime hβ3 hβ1
      have hβi : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
        intro hin
        apply hnotI
        obtain ⟨s, hs⟩ := (FQ.congr_mem_range_conj θ' β).2 hin
        rw [← hcongr, ← hs]
        exact hconj s
      obtain ⟨t, r, n⟩ := lab
      dsimp only at htag hn
      subst htag
      subst hn
      have hSM : MarkedModel ⟨.twF4, r, 3⟩ S := MarkedModel.of_mulEquiv θ'.symm hMM
      have hL : LieModel S .twistedF4 0 2 3 := hSM
      obtain ⟨-, -, a, hfa, K, _, _, hK, ⟨e0⟩⟩ := hL.reeTitsModel (by simp [reeTitsTags])
      have ha : 1 ≤ a := by omega
      have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
      obtain ⟨-, b₀, hb, k, _, _, _, hk, ⟨eF⟩⟩ :=
        FR.Res.ree_fix_equiv ha hK' Nat.prime_three (by norm_num) e0 β hβord hβi
      have hb0 : b₀ = 0 := by omega
      subst hb0
      have hk' : Nat.card k = 2 ^ (2 * 0 + 1) := by simpa using hk
      have hΓcard : Nat.card ↥(ReeTag.F4.reeGamma k 0) = 35942400 := by
        have := (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
          0 k hk').1
        rw [this]
        norm_num
      have hC : Nat.card (FP.fixSub β) = 35942400 := by rw [Nat.card_congr eF.toEquiv, hΓcard]
      have h1 : Nat.card J₁ ≤ Nat.card (FP.fixSub β) := Subgroup.card_le_of_le (hJ₁J.trans hJC)
      omega

end CFSG.LocalAnalysis.GLTheoremA.CatB.KG2F

end

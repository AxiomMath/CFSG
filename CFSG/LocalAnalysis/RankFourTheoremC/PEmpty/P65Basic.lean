module

import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
import CFSG.RankThree.PartOne.K1327.Trick
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank65Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fusion
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Plane

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem p65_le_of_plane_centralizers_le {p : ℕ} (hp : p.Prime) {U V M : Subgroup G}
    (hU : IsElemAbelian p U) (hUc : Nat.card U = p ^ 2) (hUV : U ≤ normalizer (V : Set G))
    (hV : ¬ p ∣ Nat.card V) (hC : ∀ u ∈ U, u ≠ 1 → centralizer ({u} : Set G) ≤ M) : V ≤ M := by
  have hgen := CFSG.RankThree.PartOne.K1327.le_iSup_centralizers hp hU hUc hUV hV
  refine hgen.trans (iSup_le fun b => ?_)
  exact inf_le_right.trans (hC b.val.val b.val.property fun h => b.property (Subtype.ext h))

theorem p65_exists_max {C : Subgroup G → Prop} (hne : ∃ F, C F) :
    ∃ F, C F ∧ ∀ F', C F' → Nat.card F' ≤ Nat.card F := by
  obtain ⟨F, hF, hmin⟩ := (measure (fun F : Subgroup G => Nat.card G - Nat.card F)).wf.has_min
    {F | C F} hne
  refine ⟨F, hF, fun F' hF' => ?_⟩
  have h1 : ¬ Nat.card G - Nat.card F' < Nat.card G - Nat.card F := hmin F' hF'
  have h2 := Subgroup.card_le_card_group F
  have h3 := Subgroup.card_le_card_group F'
  omega

private theorem p65_exists_commutative {M B F : Subgroup G} [Group.IsSolvable F]
    (hF1 : F ≠ ⊥) (hBF : B ≤ normalizer (F : Set G)) (hFnot : ¬ normalizer (F : Set G) ≤ M) :
    ∃ K : Subgroup G, K ≤ F ∧ K ≠ ⊥ ∧ B ≤ normalizer (K : Set G) ∧
      ¬ normalizer (K : Set G) ≤ M ∧ IsMulCommutative K := by
  obtain ⟨K, ⟨hKF, hK1, hBK, hKnot⟩, hmin⟩ :=
    (measure (fun K : Subgroup G => Nat.card K)).wf.has_min
      {K : Subgroup G | K ≤ F ∧ K ≠ ⊥ ∧ B ≤ normalizer (K : Set G) ∧
        ¬ normalizer (K : Set G) ≤ M} ⟨F, le_rfl, hF1, hBF, hFnot⟩
  refine ⟨K, hKF, hK1, hBK, hKnot, ?_⟩
  have : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKF)
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hK1
  refine (commutator_eq_bot_iff ↥K).1 ?_
  by_contra hne
  have hlt : _root_.commutator ↥K < ⊤ := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K
  have hN : normalizer (K : Set G) ≤
      normalizer (((_root_.commutator ↥K).map K.subtype : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (_root_.commutator ↥K)
  have hne' : (_root_.commutator ↥K).map K.subtype ≠ ⊥ := by
    rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]
  refine hmin _ ⟨(Subgroup.map_subtype_le _).trans hKF, hne', hBK.trans hN,
    fun hle => hKnot (hN.trans hle)⟩ ?_
  show Nat.card ((_root_.commutator ↥K).map K.subtype) < Nat.card K
  rw [Subgroup.card_subtype]
  calc Nat.card (_root_.commutator ↥K) < Nat.card (⊤ : Subgroup ↥K) :=
        Subgroup.card_lt_of_lt hlt
    _ = Nat.card K := Subgroup.card_top

theorem p65_exists_f_counterexample {p : ℕ} {M B F : Subgroup G}
    (hF1 : F ≠ ⊥) (hodd : Odd (Nat.card F)) (hcop : Nat.Coprime p (Nat.card F))
    (hBF : B ≤ normalizer (F : Set G)) (hFnot : ¬ normalizer (F : Set G) ≤ M) :
    ∃ f : ℕ, f.Prime ∧ f ≠ 2 ∧ f ≠ p ∧ ∃ F₁ : Subgroup G, IsPGroup f F₁ ∧ F₁ ≤ F ∧ F₁ ≠ ⊥ ∧
      B ≤ normalizer (F₁ : Set G) ∧ ¬ normalizer (F₁ : Set G) ≤ M := by
  have : Group.IsSolvable ↥F := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨K, hKF, hK1, hBK, hKnot, hcomm⟩ := p65_exists_commutative (M := M) hF1 hBF hFnot
  obtain ⟨f, hf, hfK⟩ := Nat.exists_prime_and_dvd
    (show Nat.card K ≠ 1 from fun h1 => hK1 (Subgroup.eq_bot_of_card_eq K h1))
  have : Fact f.Prime := ⟨hf⟩
  have hfF : f ∣ Nat.card F := hfK.trans (Subgroup.card_dvd_of_le hKF)
  have hf2 : f ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hfF)
  have hfp : f ≠ p := by
    rintro rfl
    exact hf.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hfF)
  obtain ⟨S⟩ : Nonempty (Sylow f ↥K) := inferInstance
  have : IsMulCommutative ↥K := hcomm
  have hSc : (S : Subgroup ↥K).Characteristic := Sylow.characteristic_of_normal S inferInstance
  have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (S : Subgroup ↥K)
  have hS1 : (S : Subgroup ↥K) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (S : Subgroup ↥K) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [S.card_eq_multiplicity] at h1
    have hk : 0 < (Nat.card ↥K).factorization f :=
      hf.factorization_pos_of_dvd Nat.card_pos.ne' hfK
    exact (Nat.one_lt_pow hk.ne' hf.one_lt).ne' h1
  refine ⟨f, hf, hf2, hfp, (S : Subgroup ↥K).map K.subtype, S.isPGroup'.map K.subtype,
    (Subgroup.map_subtype_le _).trans hKF, ?_, hBK.trans hN, fun hle => hKnot (hN.trans hle)⟩
  rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective]

theorem p65_fusionIsSylowIn_conj {f : ℕ} {S O : Subgroup G}
    (hS : fusionIsSylowIn f S O) {h : G} (hh : h ∈ normalizer (O : Set G)) :
    fusionIsSylowIn f (S.map (MulAut.conj h).toMonoidHom) O := by
  obtain ⟨hSO, hSp, hmax⟩ := hS
  refine ⟨?_, hSp.map _, fun P hPO hPp hTP => ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_iff.mp hh s).mp (hSO hs)
  · have hh' : h⁻¹ ∈ normalizer (O : Set G) := inv_mem hh
    have h1 : S ≤ P.map (MulAut.conj h⁻¹).toMonoidHom := fun s hs =>
      ⟨h * s * h⁻¹, hTP ⟨s, hs, rfl⟩, by simp [mul_assoc]⟩
    have h2 : P.map (MulAut.conj h⁻¹).toMonoidHom ≤ O := by
      rintro _ ⟨p, hp, rfl⟩
      exact (mem_normalizer_iff.mp hh' p).mp (hPO hp)
    have h3 := hmax _ h2 (hPp.map _) h1
    refine le_antisymm (fun x hx => ?_) hTP
    have hx' : h⁻¹ * x * h ∈ S := by
      rw [← h3]
      exact ⟨x, hx, by simp⟩
    exact ⟨h⁻¹ * x * h, hx', by simp [MulAut.conj_apply, mul_assoc]⟩

theorem p65_mem_normalizer_of_map_eq {S : Subgroup G} {c h : G}
    (hTc : S.map (MulAut.conj h).toMonoidHom = S.map (MulAut.conj c).toMonoidHom) :
    c⁻¹ * h ∈ normalizer (S : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hx1 : h * x * h⁻¹ ∈ S.map (MulAut.conj c).toMonoidHom := by
      rw [← hTc]
      exact ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := hx1
    have hsx' : c * s * c⁻¹ = h * x * h⁻¹ := hsx
    have : c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = s := by
      calc c⁻¹ * h * x * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * x * h⁻¹) * c := by group
        _ = c⁻¹ * (c * s * c⁻¹) * c := by rw [hsx']
        _ = s := by group
    rw [this]
    exact hs
  · intro hx
    have hx1 : h * x * h⁻¹ ∈ S.map (MulAut.conj c).toMonoidHom :=
      ⟨c⁻¹ * h * x * (c⁻¹ * h)⁻¹, hx, by
        show c * (c⁻¹ * h * x * (c⁻¹ * h)⁻¹) * c⁻¹ = h * x * h⁻¹
        group⟩
    rw [← hTc] at hx1
    obtain ⟨s, hs, hsx⟩ := hx1
    have hsx' : h * s * h⁻¹ = h * x * h⁻¹ := hsx
    have : s = x := mul_left_cancel (mul_right_cancel hsx')
    rwa [← this]

theorem p65_le_of_normalizer_le {M H O S : Subgroup G} {p f : ℕ} (hp : p.Prime)
    (hf : f.Prime) (hOp : ¬ p ∣ Nat.card O) (hHO : H ≤ normalizer (O : Set G)) (hOM : O ≤ M)
    (hS : fusionIsSylowIn f S O) (hSM : normalizer (S : Set G) ≤ M) : H ≤ M := by
  intro h hh
  have hT := p65_fusionIsSylowIn_conj hS (hHO hh)
  have hbot : IsPGroup p (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨c, hc, hTc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows
    hp hf hbot hOp bot_le hS hT bot_le bot_le
  have hn := p65_mem_normalizer_of_map_eq hTc
  have := M.mul_mem (hOM (mem_inf.mp hc).1) (hSM hn)
  simpa using this

theorem p65_normalizer_le_of_enlarged {M B F E : Subgroup G} {p f : ℕ} (hp : p.Prime)
    (hf : f.Prime) (hB : IsPGroup p B)
    (hmax : ∀ F' : Subgroup G, F' ≤ M → IsPGroup f F' → F' ≠ ⊥ → B ≤ normalizer (F' : Set G) →
      Nat.card F < Nat.card F' → normalizer (F' : Set G) ≤ M)
    (hBF : B ≤ normalizer (F : Set G))
    (hOM : rankThreePrimeCore p (normalizer (F : Set G)) ≤ M) (hFE : F < E) (hE : IsPGroup f E)
    (hBE : B ≤ normalizer (E : Set G))
    (hEO : E ≤ rankThreePrimeCore p (normalizer (F : Set G))) :
    normalizer (F : Set G) ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hHO, hOp⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p (normalizer (F : Set G))
  have hOp' : ¬ p ∣ Nat.card (rankThreePrimeCore p (normalizer (F : Set G))) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp hOp
  obtain ⟨S, hSsyl, hES, hBS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    hp hf hB hOp' (hBF.trans hHO) hEO hE hBE
  have hS1 : S ≠ ⊥ := bot_lt_iff_ne_bot.mp ((bot_le.trans_lt hFE).trans_le hES)
  have hcard : Nat.card F < Nat.card S :=
    (Subgroup.card_lt_of_lt hFE).trans_le (Subgroup.card_le_of_le hES)
  have hN : normalizer (S : Set G) ≤ M := hmax S (hSsyl.1.trans hOM) hSsyl.2.1 hS1 hBS hcard
  exact p65_le_of_normalizer_le hp hf hOp' hHO hOM hSsyl hN

theorem p65_primeCore_le_of_rank_three {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}
    (hS : Situation G p P M) (hx : Point P M x) (hz : Central P z) {H Q : Subgroup G}
    (hQH : Q ≤ H) (hQ : IsPGroup p Q) (hQidx : ¬ p ∣ (Q.subgroupOf H).index)
    (hrank : 3 ≤ Open.pRank p H) (hBQ : zpowers x ⊔ zpowers z ≤ Q) :
    rankThreePrimeCore p H ≤ M := by
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨-, hHO, hOp⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p H
  have hpl := plane_of_central hS hx hz
  have hBP : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) := hpl.isIsolatedPlane.1
  have hQM : Q ≤ M := le_of_plane_le hS hBP (centralizer_plane_le hS hz) hQ hBQ
  have hQrk : 3 ≤ Open.pRank p Q := by
    rw [CFSG.LocalAnalysis.RankThreeTheoremC.pRank_eq_of_sylow hprime hQH hQ hQidx]
    exact hrank
  obtain ⟨E, hEQ, hEa, hEc⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hprime hQrk
  have hE3 : 3 ≤ Open.pRank p E :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_pRank_of_isElemAbelian hprime le_rfl hEa hEc
  obtain ⟨U, hUE, hUa, hUc⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank
    hprime (k := 2) (by omega : 2 ≤ Open.pRank p E)
  refine p65_le_of_plane_centralizers_le hprime hUa hUc ?_
    ((Nat.Prime.coprime_iff_not_dvd hprime).1 hOp) fun u hu hu1 => ?_
  · exact hUE.trans (hEQ.trans (hQH.trans hHO))
  · have huE : u ∈ E := hUE hu
    have huM : u ∈ M := hQM (hEQ huE)
    refine hS.centralizer_le_of_pRank huM ?_ ?_
    · have hup : u ^ p = 1 := hUa.2 u hu
      exact orderOf_eq_prime hup hu1
    · refine le_trans hE3 (CFSG.SectionRank.pRank_mono hprime.one_lt (le_inf (hEQ.trans hQM) ?_))
      intro e he
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hEa.1.is_comm.comm ⟨e, he⟩ ⟨u, huE⟩)

theorem p65_d1Local_of_le {p : ℕ} {P : Sylow p G} {M : Subgroup G} (hS : Situation G p P M)
    {f : ℕ} (hf : f.Prime) (hf2 : f ≠ 2) (h4 : 4 ≤ Open.pRank f M) {Fh : Subgroup G}
    (hFhM : Fh ≤ M) (hFh : IsPGroup f Fh) (h3 : 3 ≤ Open.pRank f Fh) (F₀ : Sylow f G)
    (hle : Fh ≤ (F₀ : Subgroup G)) :
    CFSG.AGLEmbedding.D1Local f F₀ M ∧ GLBCore f 2 (F₀ : Subgroup G) ≤ M := by
  have hM2 : IsTwoLocal M := hS.loc.maxLocal.1
  have hdvd : f ∣ Nat.card G :=
    ((dvd_card_of_one_le_pRank hf (by omega)).trans (Subgroup.card_dvd_of_le hFhM |>.trans
      (Subgroup.card_subgroup_dvd_card M))) |> fun h => h
  have hrank : 4 ≤ GLBTwoLocalRank f G :=
    h4.trans (le_csSup (CFSG.PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove f hf)
      ⟨M, hM2, rfl⟩)
  have hbeta : f ∈ GLBBetaFour G := ⟨hf, hf2, hdvd, hrank⟩
  obtain ⟨Y, hY, hWY⟩ := (hS.toGlobal.d1Global.pre f hbeta).2 F₀
  obtain ⟨M', hYM', hM'⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_maximal_twoLocal hY
  have hD' : CFSG.AGLEmbedding.D1Local f F₀ M' := ⟨hbeta, hM', hWY.trans hYM'⟩
  have hcore' : GLBCore f 2 (F₀ : Subgroup G) ≤ M' := hS.toGlobal.fullCore f F₀ M' hD'
  obtain ⟨E, hEFh, hEa, hEc⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.exists_isElemAbelian_of_le_pRank hf h3
  have hE3 : 3 ≤ Open.pRank f E :=
    CFSG.LocalAnalysis.RankThreeTheoremC.le_pRank_of_isElemAbelian hf le_rfl hEa hEc
  have hEM' : E ≤ M' :=
    le_normalizer.trans ((CFSG.AGLEmbeddingD2.normalizer_le_glbCore f 2 (hEFh.trans hle)
      (by omega)).trans hcore')
  have hMM' : M ≤ M' := hS.toGlobal.d1 f hbeta F₀ M' hM' hD'.core M hM2 (by
    refine le_trans hE3 (CFSG.SectionRank.pRank_mono hf.one_lt (le_inf (hEFh.trans hFhM) hEM')))
  have hMeq : M' = M := hS.loc.maxLocal.2 M' hM'.1 hMM'
  subst hMeq
  exact ⟨hD', hcore'⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SylNormTriv
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineSpAut
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
public import CFSG.ClassicalGroups.Symplectic.ProjectivePerfect
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.AGLEmbedding.ParabHub

open CFSG.LieType.Universal CFSG.LieType.Steinberg

variable {K Y : Type*} [Group K] [Finite K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y}

theorem BorelQuotient.normalizer_eq_of_one (h : BorelQuotient D n H π 1) (T : Sylow 2 Y) :
    Subgroup.normalizer ((T : Subgroup Y) : Set Y) = T := by
  haveI : Finite Y := Finite.of_surjective π h.surj
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' 1 :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hN := hQ.normalizer_map_posUnipotent
  have hHbot : (⨆ i, H i) = ⊥ := by
    refine le_antisymm (iSup_le fun i => ?_) bot_le
    intro g hg
    simpa using hQ.torus_pow i g hg
  have hB : borel D H = posUnipotent D := by
    rw [CFSG.LieType.Steinberg.borel, hHbot, bot_sup_eq]
  rw [hB] at hN
  rw [← hT] at hN
  exact hN

end CFSG.AGLEmbedding.ParabHub

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem normalizer_sylow_statedProj_statedSp {r : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) (T : Sylow 2 (StatedProj (StatedSp r F))) :
    normalizer ((T : Subgroup (StatedProj (StatedSp r F))) : Set (StatedProj (StatedSp r F))) =
      T := by
  haveI : CharP F 2 := by
    letI : Fintype F := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card, hF]; norm_num)
  have hQ := CFSG.AGLEmbedding.ParabHub.borelQuotient_sp (n := r) (F := F)
    (Y := StatedProj (StatedSp r F)) (MulEquiv.refl _)
  have hM : Nat.card F - 1 = 1 := by omega
  rw [hM] at hQ
  exact hQ.normalizer_eq_of_one T

theorem mulAut_eq_one_of_mulEquiv_statedProj_statedSp {r : ℕ} (hr : 3 ≤ r) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 2) {X : Type} [Group X] (e : X ≃* StatedProj (StatedSp r F))
    (α : MulAut X) (hα : Odd (orderOf α)) {S : Subgroup X} (hS : IsPGroup 2 S)
    (hSi : ¬ 2 ∣ S.index) (hαS : S.map α.toMonoidHom = S) : α = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (StatedProj (StatedSp r F)) :=
    CFSG.ClassicalGroups.Symplectic.finite_statedProj_statedSp r F
  haveI : Finite X := Finite.of_surjective e.symm.toMonoidHom e.symm.surjective
  let α' : MulAut (StatedProj (StatedSp r F)) := e.symm.trans (α.trans e)
  obtain ⟨g', hg'⟩ :=
    CFSG.SeitzReduction.SporadicRefine.allInner_statedProjSp_of_card_two (r := r) (K := F) hr hF α'
  let g : X := e.symm g'
  have hαconj : α = MulAut.conj g := by
    have h1 : ∀ x, α x = e.symm (g' * e x * g'⁻¹) := by
      intro x
      apply e.injective
      calc e (α x) = α' (e x) := by simp [α', MulEquiv.trans_apply]
        _ = (MulAut.conj g') (e x) :=
          congrArg (fun σ : MulAut (StatedProj (StatedSp r F)) => σ (e x)) hg'
        _ = g' * e x * g'⁻¹ := by rw [MulAut.conj_apply]
        _ = e (e.symm (g' * e x * g'⁻¹)) := by rw [MulEquiv.apply_symm_apply]
    ext x
    rw [h1 x, MulAut.conj_apply]
    simp [g]
  have hSconj : S.map (MulAut.conj g).toMonoidHom = S := by
    rw [← hαconj]
    exact hαS
  have hgN : g ∈ Subgroup.normalizer (S : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 hSconj
  have hTidx : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    have hdvd : (S.map e.toMonoidHom).index ∣ S.index :=
      Subgroup.index_map_dvd (H := S) (f := e.toMonoidHom) e.surjective
    exact fun h2 => hSi (h2.trans hdvd)
  have hnormT : Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set _) =
      S.map e.toMonoidHom :=
    normalizer_sylow_statedProj_statedSp (r := r) (F := F) hF
      ((hS.map e.toMonoidHom).toSylow hTidx)
  have hnormX : Subgroup.normalizer (S : Set X) = S := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_equiv_normalizer_eq]
    exact hnormT
  have hgS : g ∈ S := by
    rwa [hnormX] at hgN
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf (p := 2) (G := S)).1 hS ⟨g, hgS⟩
  have hjg : orderOf g = 2 ^ j :=
    (Subgroup.orderOf_coe (⟨g, hgS⟩ : S)).trans hj
  have hdvd : orderOf α ∣ orderOf g := by
    rw [hαconj]
    exact orderOf_map_dvd (MulAut.conj : X →* MulAut X) g
  rw [hjg] at hdvd
  have hcop : Nat.Coprime (orderOf α) (2 ^ j) :=
    (Nat.coprime_two_right.mpr hα).pow_right j
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem kFactSylNormTrivSp : KFactSylNormTrivSp := by
  intro A _ _ P b hP hb
  by_contra hW
  obtain ⟨k, d, ⟨q, hq2, hd⟩, ⟨e⟩⟩ := hP
  obtain ⟨α, hαord, -, ⟨S, -, hSisP, hSrel, hSfix⟩, w, hw, hαw⟩ :=
    exists_mulAut_of_sylAct e hb hW
  obtain ⟨d0, hdv⟩ := d
  have hd0 : d0 = .B k q := hd
  subst hd0
  have hrange := ((TauCeti.LieTypeIndex.inStandardRange_iff (.B k q)).1
    ((TauCeti.LieTypeIndex.valid_iff (.B k q)).1 hdv).1)
  have hkne : k ≠ 2 := fun hk => hrange.2 ⟨hk, hq2⟩
  have hk3 : 3 ≤ k := by omega
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hq2, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h q.prime_p.ne_one
    · exact h
  have he1 : q.exponent = 1 := by
    have h1 : q.p ^ q.exponent = 2 := by
      rw [← TauCeti.PrimePower.card_def, hq2]
    rw [hp2] at h1
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by rw [h1, pow_one]
    exact Nat.pow_right_injective (le_refl 2) h2
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even k q hdv hp2 hk3
    (G := (TauCeti.CFSGIndex.lie ⟨.B k q, hdv⟩).Group) (MulEquiv.refl _)
  obtain ⟨-, F, hF, hFfin, hcard, ⟨f⟩⟩ := hmodel
  have hF2 : Nat.card F = 2 := by
    rw [hcard, hp2, he1, pow_one]
  have hFsimple : IsSimpleGroup (StatedProj (StatedSp k F)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F k (by omega)
      (Or.inr (Or.inr ⟨hF2, hk3⟩))
  have hFperf : Group.IsPerfect (StatedProj (StatedSp k F)) :=
    CFSG.ClassicalGroups.Symplectic.symplectic_projective_perfect k F
      (Or.inr (Or.inr ⟨hF2, hk3⟩))
  haveI : IsSimpleGroup (StatedProj (StatedSp k F)) := hFsimple
  haveI : Group.IsPerfect (StatedProj (StatedSp k F)) := hFperf
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie ⟨.B k q, hdv⟩).Group :=
    MulEquiv.isSimpleGroup f
  have hncSp : ∃ a b : StatedProj (StatedSp k F), a * b ≠ b * a := by
    have h := Group.IsPerfect.not_isMulCommutative (StatedProj (StatedSp k F))
    rw [isMulCommutative_iff] at h
    push Not at h
    exact h
  have hncQ : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.B k q, hdv⟩).Group, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hncSp
    exact ⟨f.symm a, f.symm b, fun h => hab (by simpa using congrArg f h)⟩
  obtain ⟨hQquasi, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hncQ
  have hquasiTop : CFSG.IsQuasisimple (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨.B k q, hdv⟩).Group) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQquasi
  have htop : wSup (TauCeti.CFSGIndex.lie ⟨.B k q, hdv⟩).Group = ⊤ := by
    refine le_antisymm le_top ?_
    exact le_wSup_of_normal_of_isQuasisimple (N := ⊤) inferInstance hquasiTop
  have hSi : ¬ 2 ∣ S.index := by
    rw [htop, Subgroup.relIndex_top_right] at hSrel
    exact hSrel
  unfold SylAct at hb
  have hαodd : Odd (orderOf α) := hb.1.of_dvd_nat hαord
  have hα1 : α = 1 :=
    mulAut_eq_one_of_mulEquiv_statedProj_statedSp hk3 hF2 f α hαodd hSisP hSi hSfix
  exact hαw (by rw [hα1]; rfl)

theorem kFactSylNormTriv : KFactSylNormTriv :=
  kFactSylNormTriv_of_sp kFactSylNormTrivSp

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

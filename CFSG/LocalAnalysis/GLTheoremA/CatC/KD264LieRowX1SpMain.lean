module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpGroup
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1SpForm
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1Lin
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273d2
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSpRank
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

open CFSG.Open

theorem isQuasisimple_alt6 : CFSG.Open.IsQuasisimple (alternatingGroup (Fin 6)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  have hcen : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hperf : commutator (alternatingGroup (Fin 6)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  refine ⟨hperf, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans
    (QuotientGroup.quotientBot (G := alternatingGroup (Fin 6)))).isSimpleGroup

theorem exists_noncomm_of_not_mulCommutative {G : Type*} [Group G] (h : ¬ IsMulCommutative G) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  exact h ⟨⟨fun a b => hc a b⟩⟩

theorem kd264X1SpPart_holds : KD264X1SpPart := by
  intro d n q hd inst
  obtain ⟨dd, hv⟩ := d
  dsimp only at hd
  subst hd
  unfold KD264X1At
  intro h1 h2 h3 h4 h5 h6
  unfold KD264X1Concl
  intro A hA hrank
  have hq : q.card = 2 := by simpa [ov2Idx, fieldSize] using h4
  have hvalid := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hvalid.1
  have hn3 : n ≠ 2 := fun h => hr.2 ⟨h, hq⟩
  have hn2 : 2 ≤ n := hr.1
  have hn3' : n ≠ 3 := by
    rintro rfl
    apply h2
    show CFSG.Yardstones.Md0ec50421ce4.k2Lie 3 (TauCeti.LieTypeIndex.B 3 q)
    exact ⟨rfl, hq⟩
  have hn4 : 4 ≤ n := by omega
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 := by
      rw [← hq, TauCeti.PrimePower.card_def]
      exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.1 q.exponent_pos)
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
  have he1 : q.exponent = 1 := by
    have h2e : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def, hq]
    rw [hp2] at h2e
    exact Nat.pow_right_injective (le_refl 2) (show 2 ^ q.exponent = 2 ^ 1 by simpa using h2e)
  obtain ⟨ψ0⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d.nonempty_typeBGroupEquiv_spTwo
    (n := n) (by omega) q hv hp2 he1
  let ψ : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group ≃*
      ↥(CFSG.Open.StatedSp n (ZMod 2)) := ψ0
  obtain ⟨ιs⟩ := exists_stdIso n
  let ι := ψ.trans ιs
  have hinn : ∀ β : MulAut (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group,
      ∃ g : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group, β = MulAut.conj g := by
    intro β
    obtain ⟨g, hg⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273d.all_inner_spTwo
      (n := n) (by omega) (MulAut.congr ψ β)
    refine ⟨ψ.symm g, ?_⟩
    have hβ : β = MulAut.congr ψ.symm (MulAut.congr ψ β) := by
      ext x
      simp [MulAut.congr_apply]
    rw [hβ, hg, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]
  let instV : @Module (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) _ AddCommGroup.toAddCommMonoid :=
    Pi.module _ _ _
  have hfd : FiniteDimensional (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) := Module.Finite.pi
  have hcen : ∀ s : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group,
      MulAut.conj s = 1 → s = 1 := by
    intro s hs
    have hst : ∀ t, s * t = t * s := by
      intro t
      have h := congrArg (fun φ : MulAut _ => φ t) hs
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h
    have hz : ψ s ∈ Subgroup.center ↥(CFSG.Open.StatedSp n (ZMod 2)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨t, rfl⟩ := ψ.surjective g
      rw [← map_mul, ← map_mul, hst t]
    haveI : NeZero n := ⟨by omega⟩
    rw [CFSG.StandardType.AutPSp.center_eq_bot] at hz
    exact ψ.injective ((Subgroup.mem_bot.1 hz).trans (map_one ψ).symm)
  have hinj : Function.Injective (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    exact hcen s hs
  have hpS : n ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group) := by
    have h1 := CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp (K := ZMod 2)
      (n := n) (r := 3) (by norm_num) (by rw [Nat.card_zmod]; norm_num)
    have h2 := pRank_map_mulEquiv 3 ψ (⊤ : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group)
    have htop : Subgroup.map (ψ : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →*
        ↥(CFSG.Open.StatedSp n (ZMod 2))) ⊤ = ⊤ :=
      Subgroup.map_top_of_surjective _ ψ.surjective
    rw [htop] at h2
    rw [← h2]
    exact h1
  let E : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group :=
    A.comap (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _)
  have hEA : E.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _) = A := by
    ext a
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro ha
      obtain ⟨g, rfl⟩ := hinn a
      exact ⟨g, ha, rfl⟩
  have hEel : IsElemAbelian 3 E :=
    isElemAbelian_of_map_injective _ hinj (by rw [hEA]; exact hA)
  have hEcard : Nat.card E = Nat.card A := by
    have h := Subgroup.card_map_of_injective (K := E)
      (f := (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _)) hinj
    rw [hEA] at h
    exact h.symm
  obtain ⟨kA, hkA⟩ := Gen.card_eq_three_pow' hA
  have hpA : CFSG.Open.pRank 3 A = kA := pRank_eq_of_card Nat.prime_three hA hkA
  obtain ⟨ιs⟩ := exists_stdIso n
  let ι := ψ.trans ιs
  let E' : Subgroup ↥(TauCeti.BilinForm.isometryGroup (stdForm n)) := E.map ι.toMonoidHom
  have hE'el : IsElemAbelian 3 E' := isElemAbelian_map_hom 3 _ hEel
  haveI : Fintype E' := Fintype.ofFinite _
  have hE'card : Nat.card E' = 3 ^ kA := by
    rw [Subgroup.card_map_of_injective (f := ι.toMonoidHom) ι.injective, hEcard, hkA]
  let EΓ : Subgroup ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) :=
    E'.map (TauCeti.BilinForm.isometryGroup (stdForm n)).subtype
  haveI : Fintype EΓ := Fintype.ofFinite _
  have hEΓel : IsElemAbelian 3 EΓ := isElemAbelian_map_hom 3 _ hE'el
  have hEΓcard : Fintype.card EΓ = 3 ^ kA := by
    rw [← Nat.card_eq_fintype_card, Subgroup.card_map_of_injective Subtype.val_injective, hE'card]
  have hGL := card_le_three_pow_half EΓ hEΓel
  have hfin : Module.finrank (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) / 2 = n := by
    rw [stdForm_finrank]
    omega
  have hkn : kA ≤ n := by
    rw [hfin, hEΓcard] at hGL
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hGL
  have hkn' : n ≤ kA := le_trans hpS (le_trans hrank hpA.le)
  have hkeq : kA = n := le_antisymm hkn hkn'
  have hE'card' : Fintype.card E' = 3 ^ n := by
    rw [← Nat.card_eq_fintype_card, hE'card, hkeq]
  obtain ⟨F', hF'E, hF'el, hF'rank, L', hL'sub, hL'iso⟩ :=
    sp_core_G (stdForm n) (stdForm_isAlt n) (stdForm_nondeg n) n hn4 (stdForm_finrank n) E'
      hE'el hE'card'
  obtain ⟨χ0⟩ := hL'iso
  let FS : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group :=
    F'.map (ι.symm.toMonoidHom)
  have hFSE : FS ≤ E := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.1 (hF'E ht)
    have : ι.symm t = u := by
      rw [← hut]
      simp
    rw [show ι.symm.toMonoidHom t = u from this]
    exact hu
  have hFA : FS.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _) ≤ A := by
    calc FS.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _)
        ≤ E.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _) :=
          Subgroup.map_mono hFSE
      _ = A := hEA
  have hFel : IsElemAbelian 3 (FS.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _)) :=
    isElemAbelian_map_hom 3 _ (isElemAbelian_map_hom 3 _ hF'el)
  have hFS2 : 2 ≤ CFSG.Open.pRank 3 FS := by
    have h := pRank_map_mulEquiv 3 ι.symm F'
    show 2 ≤ CFSG.Open.pRank 3 (F'.map ι.symm.toMonoidHom)
    rw [show F'.map ι.symm.toMonoidHom = F'.map (ι.symm : _ →* _) from rfl, h]
    exact hF'rank
  have hFrank : 2 ≤ CFSG.Open.pRank 3 (FS.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _)) :=
    Gen.two_le_pRank_map_injective _ hinj hFS2
  have hmin : min 2 (CFSG.Open.pRank 3 A - 1) ≤ CFSG.Open.pRank 3
      (FS.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _)) :=
    (min_le_left _ _).trans hFrank
  let LS : Subgroup (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group :=
    L'.map ι.symm.toMonoidHom
  have hLsub : CFSG.Open.IsSubnormal LS (Subgroup.centralizer (FS : Set _)) := by
    have h := CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map ι.symm hL'sub
    rw [centralizer_map_mulEquiv ι.symm F'] at h
    exact h
  let χ : ↥LS ≃* alternatingGroup (Fin 6) :=
    (MulEquiv.subgroupMap ι.symm L').symm.trans χ0
  have hq : CFSG.Open.IsQuasisimple ↥LS :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv χ.symm isQuasisimple_alt6
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI hsimpL : IsSimpleGroup ↥LS := χ.isSimpleGroup
  have hnc6 : ¬ IsMulCommutative (alternatingGroup (Fin 6)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simp
  obtain ⟨a6, b6, hab6⟩ := exists_noncomm_of_not_mulCommutative hnc6
  have hncL : ∃ a b : ↥LS, a * b ≠ b * a :=
    ⟨χ.symm a6, χ.symm b6, fun h => hab6 (by
      have := congrArg χ h
      simpa using this)⟩
  have hcenL : Subgroup.center ↥LS = ⊥ := center_eq_bot_of_simple_nonabelian hncL
  have h360 : Nat.card ↥LS = 360 := by
    rw [Nat.card_congr χ.toEquiv]
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin 6)
    have h3 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_perm]
      simp [Nat.factorial]
    rw [h3] at h2
    omega
  have hd : 3 ∣ Nat.card (↥LS ⧸ Subgroup.center ↥LS) := by
    rw [hcenL, Nat.card_congr (QuotientGroup.quotientBot (G := ↥LS)).toEquiv, h360]
    norm_num
  have hGood : CFSG.Open.IsSubnormal LS (⨅ g ∈ FS.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _), CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup g) := by
    rw [iInf_fixSubgroup_conj]
    exact hLsub
  exact ⟨FS.map (MulAut.conj : (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.B n q, hv⟩).Group →* _),
    hFA, hFel, hmin, isGood_of_subnormal_quasisimple Nat.prime_three hGood hq hd⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1Sp

end

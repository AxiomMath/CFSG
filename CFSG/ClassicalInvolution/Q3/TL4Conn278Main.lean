module

public import CFSG.ClassicalInvolution.Q3.TL4Conn278Lift
public import CFSG.ClassicalInvolution.Q3.TL4Conn278Alpha
public import CFSG.ClassicalInvolution.Q3.TL4ConnThm8
public import CFSG.ClassicalInvolution.Asc77.AscT8Y4

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)
open CFSG.ClassicalInvolution.Q3.Q3CL.T8R.Loc (Std8Core)

section Norm

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

omit [Finite G] in
theorem layerY_conjSub_eq (hΩ : ConjInvariant Ω) {c : G}
    (hc : c ∈ Subgroup.centralizer ({x} : Set G)) : conjSub c (layerY Ω x) = layerY Ω x := by
  have key : ∀ d ∈ Subgroup.centralizer ({x} : Set G),
      conjSub d (layerY Ω x) ≤ layerY Ω x := by
    intro d hd
    unfold layerY
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_layerY (conjSub_mem_coreFam hΩ hC hd)
  refine le_antisymm (key c hc) ?_
  have h := conjSub_mono (n := c) (key c⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hc))
  rwa [conjSub_conjSub_inv] at h

theorem oddCoreOf_layerY_le (hΩ : ConjInvariant Ω) :
    oddCoreOf (layerY Ω x) ≤ oddCoreOf (Subgroup.centralizer ({x} : Set G)) :=
  oddCoreOf_le_oddCoreOf_of_normalized layerY_le_centralizer
    (fun _ hc => layerY_conjSub_eq hΩ hc)

theorem oddCoreOf_layerY_le_of_good_pair (hΩ : ConjInvariant Ω) {u v : G} {J : Subgroup G}
    (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (hne : u ≠ v) (hux : u ∈ Subgroup.centralizer ({x} : Set G))
    (hvx : v ∈ Subgroup.centralizer ({x} : Set G))
    (hgu : Subgroup.centralizer ({u} : Set G) ≤ J) (hgv : Subgroup.centralizer ({v} : Set G) ≤ J)
    (hguv : Subgroup.centralizer ({u * v} : Set G) ≤ J) : oddCoreOf (layerY Ω x) ≤ J := by
  refine CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le
    (E := Subgroup.closure ({u, v} : Set G))
    ⟨⟨fun a b => Subtype.ext (closure_pair_mul_comm huv a.2 b.2)⟩⟩
    (fun w hw => closure_pair_sq hu hv huv hw) (four_le_natCard_closure_pair hu hu1 hv1 hne)
    (fun w hw => mem_normalizer_oddCore_of_mem_normalizer
      (mem_normalizer_iff_conjSub_eq.mpr (layerY_conjSub_eq hΩ ?_)))
    (oddCoreOf_odd_natCard _) (fun e he he1 => inf_le_right.trans ?_)
  · have hcl : Subgroup.closure ({u, v} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact hux
      · exact hvx
    exact hcl hw
  · rcases mem_closure_pair_involutions hu hv huv he with h | h | h | h
    · exact absurd h he1
    · rw [h]; exact hgu
    · rw [h]; exact hgv
    · rw [h]; exact hguv

end Norm

section Good

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem repElt_omegaStar_gen (c : Q3CL.Thompson.Ctx Ω W) (ρ σ : Rep Ω W) (hne : ρ.K ≠ σ.K) :
    σ.K ∈ omegaStarNbr Ω ρ.K :=
  (Q3CL.Thompson.mem_omegaStarNbr_of_inf_W c.hΩ c.hW ρ.hK σ.hK hne ρ.hR σ.hR ρ.hRK σ.hRK).1

theorem mem_dComp_of_rep_gen (hs : Std8Core Ω K J S R T W z t)
    (hcomp : dComp Ω K = dstarComp Ω K) (ρ : Rep Ω W) : ρ.K ∈ dComp Ω K := by
  have hc := Q3CL.T8.ctxOf (Q3CL.T8R.Loc.partIHyp_of_std8 hs) hs.hW.1
  rw [hcomp]
  by_cases h : K = ρ.K
  · rw [← h]
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      ⟨ρ.hK, Or.inl (repElt_omegaStar_gen hc (Q3CL.T8R.Loc.stdRepK hs) ρ h)⟩

theorem exists_good_pair_of_nonabelian_gen (hs : Std8Core Ω K J S R T W z t)
    (hcomp : dComp Ω K = dstarComp Ω K)
    (hab : ¬ ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) :
    ∃ u v : G, u * u = 1 ∧ v * v = 1 ∧ u ≠ 1 ∧ v ≠ 1 ∧ u * v = v * u ∧ u ≠ v ∧
      u ∈ Subgroup.centralizer ({z * t} : Set G) ∧ v ∈ Subgroup.centralizer ({z * t} : Set G) ∧
      Subgroup.centralizer ({u} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({v} : Set G) ≤ sigmaNorm Ω K ∧
      Subgroup.centralizer ({u * v} : Set G) ≤ sigmaNorm Ω K := by
  have hP := Q3CL.T8R.Loc.partIHyp_of_std8 hs
  have hc := Q3CL.T8.ctxOf hP hs.hW.1
  have hΩ : HypOmegaGen Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    noTwins_of_mem hΩ.conjInvariant hs.stand.trans hs.noTwins hM
  obtain ⟨d, hd, e, he, hde⟩ := exists_noncomm_of_not_abelian hab
  obtain ⟨ρ, rfl⟩ := T8.exists_rep_of_mem_muDelta hd
  obtain ⟨σ, rfl⟩ := T8.exists_rep_of_mem_muDelta he
  have hKne : ρ.K ≠ σ.K := fun h => hde (by rw [(repElt_eq_iff_gen hc ρ σ).mpr h])
  have hnonbr : σ.K ∉ omegaNbr Ω ρ.K := fun h =>
    hde ((repElt_commute_iff_gen hc ρ σ hKne).mpr h)
  have hstar : σ.K ∈ omegaStarNbr Ω ρ.K := repElt_omegaStar_gen hc ρ σ hKne
  obtain ⟨zρ, hzρ⟩ := Sec6Gen.exists_uniqueInvolution hΩ ρ.hK
  obtain ⟨zσ, hzσ⟩ := Sec6Gen.exists_uniqueInvolution hΩ σ.hK
  have hzρW : zρ ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 ρ.hK ρ.hR ρ.hRK hzρ).2
  have hzσW : zσ ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 σ.hK σ.hR σ.hRK hzσ).2
  have hzW : z ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 hK
    (Q3CL.T8R.Loc.stdRepK hs).hR (Q3CL.T8R.Loc.stdRepK hs).hRK hs.hz).2
  have htW : t ∈ W := (Q3CL.Thompson.uniqueInvolution_mem_W hΩ hs.hW.1 hs.hJ.1
    (Q3CL.T8R.Loc.stdRepJ hs).hR (Q3CL.T8R.Loc.stdRepJ hs).hRK hs.ht).2
  have haW : z * t ∈ W := W.mul_mem hzW htW
  have hcomm : zρ * zσ = zσ * zρ := hc.comm_W _ hzρW _ hzσW
  have hzne : zσ ≠ zρ := by
    intro h
    have hj : IsUniqueInvolution σ.K zρ := by rw [← h]; exact hzσ
    exact hKne (hnt _ ρ.hK _ ⟨σ.hK, zρ, hzρ, hj⟩).symm
  have hmρ := mem_dComp_of_rep_gen hs hcomp ρ
  have hmσ := mem_dComp_of_rep_gen hs hcomp σ
  have hKρ : ρ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmρ)
  have hKσ : σ.K ≤ sigmaNorm Ω K :=
    Subgroup.le_normalizer.trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmσ)
  have hg1 : Subgroup.centralizer ({zρ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant ρ.hK (hnt _ ρ.hK) hzρ).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmρ)
  have hg2 : Subgroup.centralizer ({zσ} : Set G) ≤ sigmaNorm Ω K :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant σ.hK (hnt _ σ.hK) hzσ).trans
      (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hK hmσ)
  obtain ⟨c, hcmem, hcz⟩ := exists_conj_mul_of_aEmpty (hs.stand.aEmpty ρ.K ρ.hK) hstar hnonbr
    hzρ hzσ hcomm hzne
  have hcN : c ∈ sigmaNorm Ω K := (sup_le hKρ hKσ) hcmem
  have hg3 : Subgroup.centralizer ({zρ * zσ} : Set G) ≤ sigmaNorm Ω K := by
    refine centralizer_le_of_conj hcN ?_
    have : c⁻¹ * (zρ * zσ) * c = zρ := by rw [← hcz]; group
    rw [this]
    exact hg1
  exact ⟨zρ, zσ, hzρ.sq, hzσ.sq, hzρ.ne_one, hzσ.ne_one, hcomm, Ne.symm hzne,
    Subgroup.mem_centralizer_singleton_iff.mpr (hc.comm_W _ hzρW _ haW),
    Subgroup.mem_centralizer_singleton_iff.mpr (hc.comm_W _ hzσW _ haW), hg1, hg2, hg3⟩

end Good


section TwoGroup

variable {G : Type} [Group G] [Finite G]

theorem twoGroup_of_le {L M : Subgroup G} (hLM : L ≤ M)
    (h2 : IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M)) :
    IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) := by
  intro cb
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective cb
  have hcM : (c : G) ∈ M := hLM c.2
  obtain ⟨k, hk⟩ := h2 (QuotientGroup.mk (⟨c, hcM⟩ : ↥M))
  refine ⟨k, ?_⟩
  have h1 : (⟨c, hcM⟩ : ↥M) ^ 2 ^ k ∈ classicalInvolutionOddCore ↥M := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  have h2' : (c : G) ^ 2 ^ k ∈ oddCoreOf M :=
    mem_oddCoreOf_iff.mpr ⟨M.pow_mem hcM _, by simpa using h1⟩
  have h3 : (c : G) ^ 2 ^ k ∈ oddCoreOf L := inf_oddCoreOf_le hLM ⟨L.pow_mem c.2 _, h2'⟩
  obtain ⟨hmem, h4⟩ := mem_oddCoreOf_iff.mp h3
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  have e : c ^ 2 ^ k = ⟨(c : G) ^ 2 ^ k, hmem⟩ := Subtype.ext (Subgroup.coe_pow _ c _)
  rw [e]
  exact h4

omit [Finite G] in
theorem twoGroup_conjSub {L : Subgroup G} (h2 : IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L))
    (g : G) : IsPGroup 2 (↥(conjSub g L) ⧸ classicalInvolutionOddCore ↥(conjSub g L)) := by
  let e : ↥L ≃* ↥(conjSub g L) :=
    L.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact h2.of_equiv (QuotientGroup.congr _ _ e
    (CFSG.ComponentClassification.OddCore.equiv_invariant e))

end TwoGroup

section Triangle

theorem triFrame_le_centralizer_mul {G : Type} [Group G] {Ω : Set (Subgroup G)}
    {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {P : Fin 3 → Subgroup G}
    (hF : TriFrame Ω M x P) (j : Fin 3) : P j ≤ Subgroup.centralizer ({x 0 * x 1} : Set G) := by
  intro p hp
  have h0 := Subgroup.mem_centralizer_singleton_iff.mp (hF.cent j 0 hp)
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hF.cent j 1 hp)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc p * (x 0 * x 1) = (p * x 0) * x 1 := by group
    _ = (x 0 * p) * x 1 := by rw [h0]
    _ = x 0 * (p * x 1) := by group
    _ = x 0 * (x 1 * p) := by rw [h1]
    _ = x 0 * x 1 * p := by group

theorem xMem_of_triFrame {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    (hΩ : HypOmegaGen Ω) (hnt : ∀ L ∈ Ω, ∀ L' ∈ twinSet Ω L, L' = L)
    {M : Fin 3 → Subgroup G} {x : Fin 3 → G} {P : Fin 3 → Subgroup G}
    (hF : TriFrame Ω M x P) (i : Fin 3) : XMem Ω (x 0 * x 1) (M i) := by
  have hc0 := triFrame_comm_gen hF hΩ i 0
  have hc1 := triFrame_comm_gen hF hΩ i 1
  refine ⟨hF.mem i, centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i)
    (hnt _ (hF.mem i)) (hF.inv i) ?_, P i, hF.syl i, fun p hp =>
      Subgroup.mem_centralizer_singleton_iff.mp (triFrame_le_centralizer_mul hF i hp)⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc x 0 * x 1 * x i = x 0 * (x 1 * x i) := by group
    _ = x 0 * (x i * x 1) := by rw [hc1]
    _ = (x 0 * x i) * x 1 := by group
    _ = (x i * x 0) * x 1 := by rw [hc0]
    _ = x i * (x 0 * x 1) := by group

end Triangle

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem TightLargeHypR.typeRFam (hL : TightLargeHypR r n Y Rd Sd z) :
    TypeRFam r (CoreAssembly.conjClass (tightCore Rd)) := by
  have hΩ := hL.datum.hypOmegaGen
  have hnt : ∀ L ∈ CoreAssembly.conjClass (tightCore Rd),
      ∀ L' ∈ twinSet (CoreAssembly.conjClass (tightCore Rd)) L, L' = L := by
    intro L hL'
    refine noTwins_of_mem hΩ.conjInvariant (fun _ h => h) ?_ hL'
    rw [hL.datum.twinSet_eq]
    exact fun K' hK' => hK'
  refine ⟨hΩ, hL.datum.classicalClause, ?_, ?_, ?_, hnt⟩
  · rintro _ ⟨g, rfl⟩
    exact twoGroup_conjSub (twoGroup_of_le (tightCore_le Rd) hL.datum.twoGroup) g
  · rintro _ ⟨g, rfl⟩ P hP
    have hP' : IsSylow2In (conjSub g⁻¹ P) (tightCore Rd) := by
      have := hP.conj g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have hS'R := isSylow2In_map_sylow Rd Sd
    have hS'K : ((Sd : Subgroup Rd).map Rd.subtype) ≤ tightCore Rd := fun s hs =>
      Subgroup.subset_closure ⟨hS'R.1 hs, hS'R.2.1.to_le (Subgroup.zpowers_le.mpr hs)⟩
    have hS'K0 : IsSylow2In ((Sd : Subgroup Rd).map Rd.subtype) (tightCore Rd) :=
      ⟨hS'K, hS'R.2.1, fun V hV hV2 hle => hS'R.2.2 V (hV.trans (tightCore_le Rd)) hV2 hle⟩
    obtain ⟨k, -, hk⟩ := Thompson.exists_conj_of_isSylow2In hP' hS'K0
    obtain ⟨eS⟩ := hL.cls.1
    have hk' : conjSub (k * g⁻¹) P = (Sd : Subgroup Rd).map Rd.subtype := by
      rw [conjSub_mul, hk]
    exact ⟨((P.equivMapOfInjective (MulAut.conj (k * g⁻¹)).toMonoidHom
      (MulAut.conj (k * g⁻¹)).injective).trans (MulEquiv.subgroupCongr hk')).trans
      (((Sd : Subgroup Rd).equivMapOfInjective Rd.subtype Rd.subtype_injective).symm.trans eS)⟩
  · intro L hL' w hw
    exact centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hL' (hnt L hL') hw

variable {J : Subgroup Y} {S : Sylow 2 Y} {R T W : Subgroup Y} {t : Y}

theorem TightStd8R.xMem_K (hs : TightStd8R r n Rd Sd z J S R T W t) :
    XMem (CoreAssembly.conjClass (tightCore Rd)) (z * t) (tightCore Rd) := by
  have hzt := Q3CL.T8.mul_comm_of_mem_omegaNbr hs.hyp hs.hz hs.hJ hs.ht
  refine ⟨hs.mem, hs.large.datum.le_normalizer_core ?_, R,
    Q3CL.T3.isSylow2In_of_mem_RSet_of_le hs.hyp hs.mem hs.hR.1 hs.hR.2.1, fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mp (Q3CL.T8R.Loc.le_centralizer_mul hs.toStd8Core hr)⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc z * t * z = z * (t * z) := by group
    _ = z * (z * t) := by rw [hzt]

theorem TightStd8R.exists_not_comm (hs : TightStd8R r n Rd Sd z J S R T W t) :
    ∃ g : Y, g * (z * t) ≠ (z * t) * g := by
  by_contra hcon
  push Not at hcon
  have hmem : z * t ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr fun g => hcon g
  rw [hs.large.center, Subgroup.mem_bot] at hmem
  exact mul_ne_one_of_ne hs.hz.sq (ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht) hmem

theorem TightStd8R.natCard_secQuot_lt (hs : TightStd8R r n Rd Sd z J S R T W t) :
    Nat.card (SecQuot (CoreAssembly.conjClass (tightCore Rd)) (z * t)) < n :=
  hs.large.card ▸ TL4.natCard_secQuot_lt hs.exists_not_comm

theorem TightStd8R.dstarConnected_secFam (hTri : TightSecTriangleR r n)
    (hs : TightStd8R r n Rd Sd z J S R T W t)
    (hE4 : ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W)
    (hab : ∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
      ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x) :
    T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)) := by
  set Ω := CoreAssembly.conjClass (tightCore Rd) with hΩdef
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen Ω := hs.hyp
  obtain ⟨K', R', z', hF⟩ := exists_triFrame_of_abelian hs.toStd8Core hE4 hab
  have hX : ∀ i, XMem Ω (z * t) (![tightCore Rd, J, K'] i) :=
    xMem_of_triFrame hΩ h.noTwins hF
  have hne : ∀ i j, i ≠ j → secImg Ω (z * t) (![tightCore Rd, J, K'] i) ≠
      secImg Ω (z * t) (![tightCore Rd, J, K'] j) := fun i j hij =>
    secImg_ne h (hX i) (hX j) (hF.inv i) (hF.inv j) (triFrame_comm_gen hF hΩ i j)
      (hF.x_ne h.noTwins hij)
  have hadj : ∀ i j, i ≠ j → secImg Ω (z * t) (![tightCore Rd, J, K'] j) ∈
      omegaNbr (secFam Ω (z * t)) (secImg Ω (z * t) (![tightCore Rd, J, K'] i)) := by
    intro i j hij
    have hPN : (![R, T, R'] j) ≤ Subgroup.normalizer ((![tightCore Rd, J, K'] i : Subgroup Y) :
        Set Y) :=
      (hF.cent j i).trans (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant (hF.mem i)
        (h.noTwins _ (hF.mem i)) (hF.inv i))
    exact secImg_mem_omegaNbr (hX i) (hX j) (hF.syl j) (triFrame_le_centralizer_mul hF j) hPN
      (hne i j hij)
  refine hTri (SecQuot Ω (z * t)) hs.natCard_secQuot_lt (secFam Ω (z * t)) h.secFam
    secQuot_oddCore_eq_bot omegaGen_secFam (aEmpty_secFam h)
    (fun i => secImg Ω (z * t) (![tightCore Rd, J, K'] i)) (fun i => secImg_mem (hX i)) ?_ hadj
  intro i j hij
  by_contra hne'
  exact hne i j hne' hij


@[expose] def TightC27_YsmallR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Rd : Subgroup Y) (Sd : Sylow 2 Rd) (z : Y) (J : Subgroup Y)
    (S : Sylow 2 Y) (R T W : Subgroup Y) (t : Y), TightStd8R r n Rd Sd z J S R T W t →
      ¬ DConnected (CoreAssembly.conjClass (tightCore Rd)) →
        ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W →
          (¬ ∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
            ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x) →
            ¬ T3.DStarConnected (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t)) →
              layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t) ≤
                sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd)

theorem TightStd8R.oddCoreOf_layerY_le_of_zt (hs : TightStd8R r n Rd Sd z J S R T W t)
    {K' : Subgroup Y} (hK' : K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    (hz' : IsUniqueInvolution K' (z * t)) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t)) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hs.hz hs.hJ hs.ht
  have hne : z ≠ t := ne_of_mem_omegaNbr hs.noTwins hs.hJ hs.hz hs.ht
  have hzC : z ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * (z * t) = z * (t * z) := by rw [hzt]
      _ = z * t * z := by group
  have htC : t ∈ Subgroup.centralizer ({z * t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t * (z * t) = (t * z) * t := by group
      _ = (z * t) * t := by rw [hzt]
  have hgt : Subgroup.centralizer ({t} : Set Y) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hs.hJ.1 (h.noTwins J hs.hJ.1)
      hs.ht).trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hs.mem
        (mem_dComp_of_mem_omegaNbr hs.hJ))
  have hgzt : Subgroup.centralizer ({z * t} : Set Y) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) :=
    (centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hK'.1 (h.noTwins K' hK'.1)
      hz').trans (normalizer_le_sigmaNorm_of_mem hΩ.conjInvariant hs.mem
        (mem_dComp_of_mem_omegaNbr hK'))
  exact oddCoreOf_layerY_le_of_good_pair hΩ.conjInvariant hs.hz.sq hs.ht.sq hzt hs.hz.ne_one
    hs.ht.ne_one hne hzC htC hs.centralizer_le_sigmaNorm hgt hgzt

theorem tightC27_8nE4R_of (h2 : TightC27_2R r n) (h4 : TightC27_4R r n)
    (hTri : TightSecTriangleR r n) (hT4 : Thm4RBelow r n) (hH : TightHyp51TriR r n)
    (hN : TightAlphaNormR r n) (hYs : TightC27_YsmallR r n) : TightC27_8nE4R r n := by
  intro Y _ _ Rd Sd z J S R T W t hs hdisc hE4
  have h := TightLargeHypR.typeRFam hs.large
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore Rd)) := hs.hyp
  have hcomp := h2 Y Rd Sd z J S R T W t hs hdisc
  have hK := hs.xMem_K
  have hY : layerY (CoreAssembly.conjClass (tightCore Rd)) (z * t) ≤
      sigmaNorm (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) := by
    by_cases hab : ∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
        ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x
    · refine layerY_le_sigmaNorm_of_conn h hK hcomp (hs.dstarConnected_secFam hTri hE4 hab) ?_
      by_cases hE8 : ∀ K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd),
          K' ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) J → ∀ z' : Y,
            IsUniqueInvolution K' z' → z' ≠ z * t
      · exact (oddCoreOf_layerY_le hΩ.conjInvariant).trans
          (hs.oddCoreOf_centralizer_le_sigmaNorm h4 hH hN hdisc hE4 hab hE8)
      · push Not at hE8
        obtain ⟨K', hK', -, z', hz', hzt⟩ := hE8
        rw [hzt] at hz'
        exact hs.oddCoreOf_layerY_le_of_zt hK' hz'
    · by_cases hconn : T3.DStarConnected
          (secFam (CoreAssembly.conjClass (tightCore Rd)) (z * t))
      · obtain ⟨u, v, hu, hv, hu1, hv1, huv, hne, hux, hvx, hgu, hgv, hguv⟩ :=
          exists_good_pair_of_nonabelian_gen hs.toStd8Core hcomp hab
        exact layerY_le_sigmaNorm_of_conn h hK hcomp hconn
          (oddCoreOf_layerY_le_of_good_pair hΩ.conjInvariant hu hv huv hu1 hv1 hne hux hvx hgu
            hgv hguv)
      · exact hYs Y Rd Sd z J S R T W t hs hdisc hE4 hab hconn
  exact centralizer_le_sigmaNorm_of_layerY_le h hT4 hs.natCard_secQuot_lt hK hcomp hY


theorem tightConnLeafR'_of_residuals₂ (h26_2 : TightC26_2R r n) (h26_13 : TightC26_13R r n)
    (hmin : TightC27_4MR r n) (hB : TightBenderEndR) (hE4 : TightF26E4R r n)
    (hTri : TightSecTriangleR r n) (hT4 : Thm4RBelow r n) (hH : TightHyp51TriR r n)
    (hN : TightAlphaNormR r n) (hYs : TightC27_YsmallR r n) : TightConnLeafR' r n :=
  have h2 := tightC27_2R_of h26_2 h26_13
  have h4 := tightC27_4R_of h2 (tightC27_4aR_of_min h2 hmin) hB
  tightConnLeafR'_of_steps h4 (tightC27_8R_of hE4 (tightC27_8nE4R_of h2 h4 hTri hT4 hH hN hYs))

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.ClassicalInvolution.Q3.Q3TWBHt
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uE
public import CFSG.ClassicalInvolution.Q3.Q3T7Q22H51uD

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement


section Frame

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' J : Subgroup G}
  {z u t c : G}

theorem u_not_mem_closure3 (hΩ : Q3T7M.HM Ω) (hd : Q3T8.Asc77.TwinFrameData Ω K K' z u J t) :
    u ∉ Subgroup.closure ({z, t} : Set G) := by
  intro hu
  have hzt : z * t = t * z := hd.comm_zt hΩ
  have hz2 : z * z = 1 := hd.hz.sq
  have ht2 : t * t = 1 := hd.ht.sq
  have hnt := hd.t_not_mem_closure hΩ
  have hzcl : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hucl : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  rcases ChainFrame.mem_closure_four hz2 ht2 hzt hu with h | h | h | h
  · exact hd.hu1 h
  · exact hd.huz h
  · exact hnt (h ▸ hucl)
  · apply hnt
    have : t = z * u := by
      rw [h, ← mul_assoc, hz2, one_mul]
    rw [this]
    exact Subgroup.mul_mem _ hzcl hucl

theorem ucoset_facts3 (hΩ : Q3T7M.HM Ω) (hd : Q3T8.Asc77.TwinFrameData Ω K K' z u J t)
    (hc : UCoset z u t c) :
    c ∈ Subgroup.closure ({z, u, t} : Set G) ∧ c ≠ 1 ∧ t ≠ c ∧ z ≠ c ∧ z * t ≠ c ∧
      ∃ w : G, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) ∧ c = u * w ∧ u = c * w := by
  have hzt : z * t = t * z := hd.comm_zt hΩ
  have hz2 : z * z = 1 := hd.hz.sq
  have ht2 : t * t = 1 := hd.ht.sq
  have hnu := u_not_mem_closure3 hΩ hd
  obtain ⟨w, hw, hcw, huw⟩ : ∃ w : G, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) ∧ c = u * w ∧
      u = c * w := by
    rcases hc with hc | hc | hc | hc
    · exact ⟨1, Or.inl rfl, by rw [hc, mul_one], by rw [hc, mul_one]⟩
    · refine ⟨z, Or.inr (Or.inl rfl), hc, ?_⟩
      rw [hc, mul_assoc, hz2, mul_one]
    · refine ⟨t, Or.inr (Or.inr (Or.inl rfl)), hc, ?_⟩
      rw [hc, mul_assoc, ht2, mul_one]
    · refine ⟨t * z, Or.inr (Or.inr (Or.inr rfl)), by rw [hc, mul_assoc], ?_⟩
      have h1 : (t * z) * (t * z) = 1 := mul_involution_of_commute ht2 hz2 hzt.symm
      rw [hc]
      calc u = u * ((t * z) * (t * z)) := by rw [h1, mul_one]
        _ = u * t * z * (t * z) := by group
  have hz' : z ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have ht' : t ∈ Subgroup.closure ({z, t} : Set G) := Subgroup.subset_closure (by simp)
  have hncl : c ∉ Subgroup.closure ({z, t} : Set G) := by
    intro hcl
    apply hnu
    have hwcl : w ∈ Subgroup.closure ({z, t} : Set G) := by
      rcases hw with hw | hw | hw | hw <;> rw [hw]
      · exact Subgroup.one_mem _
      · exact hz'
      · exact ht'
      · exact Subgroup.mul_mem _ ht' hz'
    rw [huw]
    exact Subgroup.mul_mem _ hcl hwcl
  exact ⟨hc.mem_closure, fun h => hncl (h ▸ Subgroup.one_mem _), fun h => hncl (h ▸ ht'),
    fun h => hncl (h ▸ hz'), fun h => hncl (h ▸ Subgroup.mul_mem _ hz' ht'), w, hw, hcw, huw⟩

theorem exists_twin_J3 (hΩ : Q3T7M.HM Ω) (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g K = M)
    (hd : Q3T8.Asc77.TwinFrameData Ω K K' z u J t) :
    ∃ J' : Subgroup G, J' ∈ twinSet Ω J ∧ J' ≠ J := by
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  obtain ⟨g, hg⟩ := htrans J hd.hJ.1
  have h1 := hzK'.conj g
  have h2 : IsUniqueInvolution J (g * z * g⁻¹) := by
    have := hd.hz.conj g
    rwa [hg] at this
  have hgz : g * z * g⁻¹ = t := h2.eq hd.ht ▸ rfl
  refine ⟨conjSub g K', ⟨hΩ.conjInvariant g K' hK'Ω, t, hd.ht, ?_⟩, ?_⟩
  · rwa [hgz] at h1
  · intro h
    apply hd.hne
    rw [← hg] at h
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem sylow_le_trivialOnQuot3 (hΩ : Q3T7M.HM Ω) {N M V : Subgroup G} {w : G} (hN : N ∈ Ω)
    (hM : M ∈ Ω) (hw : IsUniqueInvolution N w) (hMt : IsUniqueInvolution M t) (hwt : w ≠ t)
    (hV : IsSylow2In V N) (hVt : ∀ r ∈ V, r * t = t * r) : V ≤ trivialOnQuot M := by
  have hMN : M ≠ N := by
    rintro rfl
    exact hwt (hw.eq hMt)
  exact le_trivialOnQuot_of_commutator_le (Q3CL.Thompson.comm_le_oddCore_of_isSylow2In
    Sec6Gen.l6_2Gen hΩ.toGen hM hN hMN hMt hw hV fun r hr =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hVt r hr))

theorem commute_of_trivialOnQuot_of_fix3 {L S : Subgroup G} (hS : IsSylow2In S L) {a : G}
    (ha : a ∈ trivialOnQuot L) (hfix : conjSub a S = S) : ∀ r ∈ S, r * a = a * r := by
  intro r hr
  have h1 : a * r * a⁻¹ ∈ S := by
    have := conj_mem_conjSub (n := a) hr
    rwa [hfix] at this
  have h2 : a * r * a⁻¹ * r⁻¹ ∈ S := S.mul_mem h1 (S.inv_mem hr)
  have h3 : a * r * a⁻¹ * r⁻¹ ∈ Balance.oddCoreIn L := by
    have := ha.2 r (hS.1 hr)
    rwa [commutatorElement_def] at this
  have h4 : IsPGroup 2 (Subgroup.zpowers (a * r * a⁻¹ * r⁻¹)) :=
    hS.2.1.to_le (Subgroup.zpowers_le.mpr h2)
  have h5 : a * r * a⁻¹ * r⁻¹ = 1 :=
    eq_one_of_isPGroup_of_mem_odd (Balance.odd_card_oddCoreIn L) h3 h4
  have h6 : a * r * a⁻¹ = r := by
    have := congrArg (fun w => w * r) h5
    simpa using this
  calc r * a = a * r * a⁻¹ * a := by rw [h6]
    _ = a * r := by group

theorem omega4_exactCore3' (hΩ : Q3T7M.HM Ω) {c : G} (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K₀ J₀ : Subgroup G} (hK₀ : K₀ ∈ tqMembers3 Ω c) (hJ₀ : J₀ ∈ tqMembers3 Ω c)
    (hKJ : K₀ ≠ J₀) :
    padicValNat 2 (Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀)) ≤ 1 ∧
      (padicValNat 2 (Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀)) = 1 →
        ⁅exactCore3 c K₀, exactCore3 c J₀⁆ ≤
          oddCoreOf (exactCore3 c K₀) ⊓ oddCoreOf (exactCore3 c J₀)) := by
  obtain ⟨h1, h2⟩ := hΩ.omega4 K₀ hK₀.1 J₀ hJ₀.1 hKJ
  obtain ⟨zK, hzK⟩ := hΩ.classical K₀ hK₀.1
  obtain ⟨zJ, hzJ⟩ := hΩ.classical J₀ hJ₀.1
  have hK3 : IsClassicalMember3 K₀ zK := hzK.toQ3 (by norm_num)
  have hJ3 : IsClassicalMember3 J₀ zJ := hzJ.toQ3 (by norm_num)
  have hdvd : Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀) ∣ Nat.card ↥(K₀ ⊓ J₀) :=
    Subgroup.card_dvd_of_le (inf_le_inf (exactCore3_le_left c K₀) (exactCore3_le_left c J₀))
  have hle : padicValNat 2 (Nat.card ↥(exactCore3 c K₀ ⊓ exactCore3 c J₀)) ≤
      padicValNat 2 (Nat.card ↥(K₀ ⊓ J₀)) :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mp (dvd_trans pow_padicValNat_dvd hdvd)
  refine ⟨hle.trans h1, fun h => ?_⟩
  have hv : padicValNat 2 (Nat.card ↥(K₀ ⊓ J₀)) = 1 := le_antisymm h1 (h ▸ hle)
  have hcomm := h2 hv
  have hoK : oddCoreOf (exactCore3 c K₀) = exactCore3 c K₀ ⊓ oddCoreOf K₀ :=
    oddCoreIn_exactCore3 hK3 hc2 hK₀.2
  have hoJ : oddCoreOf (exactCore3 c J₀) = exactCore3 c J₀ ⊓ oddCoreOf J₀ :=
    oddCoreIn_exactCore3 hJ3 hc2 hJ₀.2
  rw [hoK, hoJ]
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  have hab : ⁅a, b⁆ ∈ ⁅K₀, J₀⁆ :=
    Subgroup.commutator_mem_commutator (exactCore3_le_left c K₀ ha) (exactCore3_le_left c J₀ hb)
  have ho := hcomm hab
  have hac : a ∈ Subgroup.centralizer ({c} : Set G) := exactCore3_le_centralizer c K₀ ha
  have hbc : b ∈ Subgroup.centralizer ({c} : Set G) := exactCore3_le_centralizer c J₀ hb
  have hcc : ⁅a, b⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
    have h1 : ⁅a, b⁆ = a * b * a⁻¹ * b⁻¹ := rfl
    rw [h1]
    exact (Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem
        ((Subgroup.centralizer ({c} : Set G)).mul_mem hac hbc)
        ((Subgroup.centralizer ({c} : Set G)).inv_mem hac))
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hbc)
  exact ⟨⟨⟨(Subgroup.map_subtype_le _) ho.1, hcc⟩, ho.1⟩,
    ⟨⟨(Subgroup.map_subtype_le _) ho.2, hcc⟩, ho.2⟩⟩

end Frame

section Hyp51

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}
  {K K' J : Subgroup G} {z u t c : G}

theorem hyp51At_u_of3 (hrows : TwinOuterAlphaAll3)
    (hs : Q3T8.Asc77.TwinFrameSettingNA Ω K K' J z u t) (hf : Q3T8.Asc77.FuzzyEdges3 Ω)
    (hc : UCoset z u t c) : Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  classical
  have hΩ : Q3T7M.HM Ω := hs.hyp
  have hd := hs.frame
  have hΩ3 : InClass3 Ω := Q3T8.Asc77.inClass3_of_twinFrameSetting hs
  have hBelow3 : CIT3Below (Nat.card G) :=
    (Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hs.below
  have hKΩ : K ∈ Ω := hd.mem
  have hK'Ω : K' ∈ Ω := hd.hK'.1
  have hzK : IsUniqueInvolution K z := hd.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hd.hz hd.hK'
  have hJΩ : J ∈ Ω := hd.hJ.1
  have hJt : IsUniqueInvolution J t := hd.ht
  have hJK : J ∈ omegaNbr Ω K := hd.hJ.2 K (mem_twinSet_self hKΩ hzK)
  have hJK' : J ∈ omegaNbr Ω K' := hd.hJ.2 K' hd.hK'
  have hKJ : K ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hKΩ hJΩ hJK
  have hK'J : K' ∈ omegaNbr Ω J := Q3CL.T3.omegaNbr_symm (Q3T8.Asc77.l6_2) hΩ hK'Ω hJΩ hJK'
  have htK : t ∈ trivialOnQuot K :=
    mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (hf J hJΩ K hKJ t hd.ht)
  have htK' : t ∈ trivialOnQuot K' :=
    mem_trivialOnQuot_iff_actsTrivOnQuot.mpr (hf J hJΩ K' hK'J t hd.ht)
  have hBab : IsElemAbelian 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    Q3T8.Asc77.twinFrame_isElemAbelian hΩ hd
  have hzB : z ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have huB : u ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  have htB : t ∈ Subgroup.closure ({z, u, t} : Set G) := Subgroup.subset_closure (by simp)
  obtain ⟨hcB, hc1, htc, hzc, hztc, w, hw, hcw, huw⟩ := ucoset_facts3 hΩ hd hc
  have hz1 : z ≠ 1 := hzK.ne_one
  have ht1 : t ≠ 1 := hJt.ne_one
  have hzt1 : z * t ≠ 1 := fun h =>
    hd.t_ne_z ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hzK.sq))
  have hcc : c * c = 1 := Lemma52Proof.mul_self_eq_one_of_mem hBab hcB
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hcc
  have hnab : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨V, hV, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
    have hVR : V ∈ RSet Ω := mem_RSet_of_isSylow2In hKΩ hV
    obtain ⟨x, -, y, -, hxy⟩ := (hΩ.isQuatSub_of_mem_RSet hVR).exists_not_commute
    exact ⟨x, y, hxy⟩
  have hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := Balance.not_subset_center_of_ne_one hnab hc1
  obtain ⟨R, R', hRsyl, hR'syl, hRR', hRt, hR't, x, hx, y, hy, hx2, hy2, hxy⟩ :=
    Q3T8.Asc77.exists_sylow_frame3 hΩ hd htK htK'
  have hzt_ne : z ≠ t := hd.t_ne_z.symm
  have hxM : ∀ M ∈ Ω, IsUniqueInvolution M t → x ∈ trivialOnQuot M := fun M hM hMt =>
    sylow_le_trivialOnQuot3 hΩ hKΩ hM hzK hMt hzt_ne hRsyl hRt hx
  have hyM : ∀ M ∈ Ω, IsUniqueInvolution M t → y ∈ trivialOnQuot M := fun M hM hMt =>
    sylow_le_trivialOnQuot3 hΩ hK'Ω hM hzK' hMt hzt_ne hR'syl hR't hy
  have hzM : ∀ M ∈ Ω, IsUniqueInvolution M t → z ∈ trivialOnQuot M := fun M hM hMt => by
    rw [← hx2]
    exact Subgroup.mul_mem _ (hxM M hM hMt) (hxM M hM hMt)
  have huM : ∀ M ∈ Ω, IsUniqueInvolution M t → u ∈ trivialOnQuot M := fun M hM hMt => by
    rw [← hxy]
    exact Subgroup.mul_mem _ (hxM M hM hMt) (hyM M hM hMt)
  have htM : ∀ M ∈ Ω, IsUniqueInvolution M t → t ∈ trivialOnQuot M := fun M _ hMt =>
    Q3T8.Asc77.mem_trivialOnQuot_of_isUniqueInvolution hMt
  have hcM : ∀ M ∈ Ω, IsUniqueInvolution M t → c ∈ trivialOnQuot M := fun M hM hMt => by
    rcases hc with hc | hc | hc | hc <;> rw [hc]
    · exact huM M hM hMt
    · exact Subgroup.mul_mem _ (huM M hM hMt) (hzM M hM hMt)
    · exact Subgroup.mul_mem _ (huM M hM hMt) (htM M hM hMt)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (huM M hM hMt) (htM M hM hMt))
        (hzM M hM hMt)
  have hxz : x * z = z * x := (hzK.commute_of_mem (hRsyl.1 hx)).symm
  have hxt : x * t = t * x := hRt x hx
  have hxy_c : x * y = y * x := hRR' x hx y hy
  have hxu : x * u = u * x := by
    rw [← hxy]
    calc x * (x * y) = x * (y * x) := by rw [hxy_c]
      _ = (x * y) * x := by group
  have hxB : Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hg with hg | hg | hg <;> rw [hg]
    · exact hxz.symm
    · exact hxu.symm
    · exact hxt.symm
  have hxc : x * c = c * x := (Subgroup.mem_centralizer_singleton_iff.mp (hxB hcB)).symm
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxc
  obtain ⟨J', hJ'tw, hJ'ne⟩ := exists_twin_J3 hΩ hs.trans hd
  have hJ'Ω : J' ∈ Ω := hJ'tw.1
  have hJ't : IsUniqueInvolution J' t := by
    obtain ⟨t', hJt', hJ't'⟩ := hJ'tw.2
    have : t' = t := hJt'.eq hJt
    rwa [this] at hJ't'
  have hcJ : IsClassicalMember3 J t :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hJΩ hJt).toQ3 (by norm_num)
  have hcJ' : IsClassicalMember3 J' t :=
    (Q3T8.Asc77.isClassicalMember_of_twin hΩ hJ'Ω hJ't).toQ3 (by norm_num)
  have hMJ : J ∈ tqMembers3 Ω c := ⟨hJΩ, hcM J hJΩ hJt⟩
  have hMJ' : J' ∈ tqMembers3 Ω c := ⟨hJ'Ω, hcM J' hJ'Ω hJ't⟩
  have hΦ : SecData3 c (exactFamily3 Ω c) := secData3_exactFamily hΩ3 hc2 ⟨J, hMJ⟩
  have hMΦ : exactCore3 c J ∈ exactFamily3 Ω c := exactCore3_mem_exactFamily3 hMJ
  have hM'Φ : exactCore3 c J' ∈ exactFamily3 Ω c := exactCore3_mem_exactFamily3 hMJ'
  have htU : IsUniqueInvolution (exactCore3 c J) t :=
    Q3T6D.isUniqueInvolution_of_le' hJt (mem_exactCore3 hcJ hc2 hMJ.2) (exactCore3_le_left c J)
  have htU' : IsUniqueInvolution (exactCore3 c J') t :=
    Q3T6D.isUniqueInvolution_of_le' hJ't (mem_exactCore3 hcJ' hc2 hMJ'.2) (exactCore3_le_left c J')
  have hA2 : IsPGroup 2 (Subgroup.closure ({z, u, t} : Set G)) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 _ hBab
  have hBN : ∀ M ∈ Ω, IsUniqueInvolution M t →
      Subgroup.closure ({z, u, t} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
    intro M hM hMt
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact (hzM M hM hMt).1
    · exact (huM M hM hMt).1
    · exact (htM M hM hMt).1
  obtain ⟨S, S', hSsyl, hS'syl, hSS', hSfix, hS'fix, -⟩ :=
    Q3T8.Asc77.exists_twinSylow_normalized3 hΩ hJΩ hJt hJ'tw hJ'ne hA2 (hBN J hJΩ hJt)
      (hBN J' hJ'Ω hJ't)
  have hcS : ∀ r ∈ S, r * c = c * r :=
    commute_of_trivialOnQuot_of_fix3 hSsyl (hcM J hJΩ hJt) (hSfix c hcB)
  have hcS' : ∀ r ∈ S', r * c = c * r :=
    commute_of_trivialOnQuot_of_fix3 hS'syl (hcM J' hJ'Ω hJ't) (hS'fix c hcB)
  have hSC : S ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcS r hr)
  have hS'C : S' ≤ Subgroup.centralizer ({c} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcS' r hr)
  have hSM : S ≤ exactCore3 c J := le_inf hSsyl.1 hSC
  have hS'M' : S' ≤ exactCore3 c J' := le_inf hS'syl.1 hS'C
  have h8 : 8 ≤ Nat.card S := (Q3T7P25.natCard_isSylow2In_member hΩ hJΩ hSsyl).ge
  have hS'8 : Nat.card S' = 8 := Q3T7P25.natCard_isSylow2In_member hΩ hJ'Ω hS'syl
  have hω4 := omega4_exactCore3' hΩ hc2 hMJ hMJ' hJ'ne.symm
  have hv1 : padicValNat 2 (Nat.card ↥(exactCore3 c J ⊓ exactCore3 c J')) = 1 :=
    padicValNat_inf_eq_one3 (mem_exactCore3 hcJ hc2 hMJ.2) (mem_exactCore3 hcJ' hc2 hMJ'.2)
      hJt.sq ht1 hω4.1
  have hxJ : x ∈ trivialOnQuot (exactCore3 c J) :=
    mem_trivialOnQuot_exactCore3 hcJ hc2 hMJ.2 (hxM J hJΩ hJt) hxC
  have hxJ' : x ∈ trivialOnQuot (exactCore3 c J') :=
    mem_trivialOnQuot_exactCore3 hcJ' hc2 hMJ'.2 (hxM J' hJ'Ω hJ't) hxC
  have hztcl : ∀ w : G, (w = 1 ∨ w = z ∨ w = t ∨ w = t * z) →
      w ∈ Subgroup.closure ({z, t, c} : Set G) := by
    have hz' : z ∈ Subgroup.closure ({z, t, c} : Set G) := Subgroup.subset_closure (by simp)
    have ht' : t ∈ Subgroup.closure ({z, t, c} : Set G) := Subgroup.subset_closure (by simp)
    intro w hw
    rcases hw with hw | hw | hw | hw <;> rw [hw]
    · exact Subgroup.one_mem _
    · exact hz'
    · exact ht'
    · exact Subgroup.mul_mem _ ht' hz'
  have hBeq : Subgroup.closure ({z, u, t} : Set G) = Subgroup.closure ({z, t, c} : Set G) := by
    apply le_antisymm
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg <;> rw [hg]
      · exact Subgroup.subset_closure (by simp)
      · rw [huw]
        exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (hztcl w hw)
      · exact Subgroup.subset_closure (by simp)
    · refine (Subgroup.closure_le _).mpr ?_
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg <;> rw [hg]
      · exact hzB
      · exact htB
      · exact hcB
  have hα : ∀ (ι : Type) (D : LieSystemData3 ι
      (↥(centralizingLayer (exactFamily3 Ω c) {c}) ⧸
        classicalInvolutionOddCore ↥(centralizingLayer (exactFamily3 Ω c) {c}))
      (oddQuotientFamily (restrictFamily (centralizingMembers (exactFamily3 Ω c) {c})
        (centralizingLayer (exactFamily3 Ω c) {c})))) (j : ι),
      modOdd c (exactCore3 c J) ≤ secComp hΦ D j →
        MovedByAll (Subgroup.closure ({z, u, t} : Set G)) c (secComp hΦ D j) →
          CFSG.IsComponent (secComp hΦ D j) →
            alphaOf (inducedImage (secComp hΦ D j)
              (modOdd c (Subgroup.closure ({z, u, t} : Set G)))) = ⊥ := by
    intro ι D j hMj hmov hLc
    have hne : modOdd c (exactCore3 c J) ≠ modOdd c (exactCore3 c J') := by
      intro heq
      have hSR : S' ≤ S := le_of_modOdd_eq_of_commutes3 hΦ D hMΦ hM'Φ heq hSM hS'M'
        hSsyl.2.1 hS'syl.2.1 hSS' h8
      have hSle : S' ≤ exactCore3 c J ⊓ exactCore3 c J' := le_inf (hSR.trans hSM) hS'M'
      have hdvd : 2 ^ 3 ∣ Nat.card ↥(exactCore3 c J ⊓ exactCore3 c J') := by
        have := Subgroup.card_dvd_of_le hSle
        rw [hS'8] at this
        simpa using this
      have hpos : Nat.card ↥(exactCore3 c J ⊓ exactCore3 c J') ≠ 0 := Nat.card_pos.ne'
      have h3 := (padicValNat_dvd_iff_le (p := 2) hpos).mp hdvd
      omega
    have hcomm : ∀ a ∈ modOdd c (exactCore3 c J), ∀ b ∈ modOdd c (exactCore3 c J'),
        a * b = b * a := by
      rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      have hk' : (k : G) ∈ exactCore3 c J := Subgroup.mem_subgroupOf.mp hk
      have hl' : (l : G) ∈ exactCore3 c J' := Subgroup.mem_subgroupOf.mp hl
      have h4 := hω4.2 hv1 (Subgroup.commutator_mem_commutator hk' hl')
      exact oddQuotMk_comm_of_commutator_mem3 hΦ D hMΦ k.2 l.2 h4.1
    have hcommM : ∀ a ∈ modOdd c (exactCore3 c J),
        oddQuotMk c ⟨x, hxC⟩ * a = a * oddQuotMk c ⟨x, hxC⟩ := by
      rintro _ ⟨k, hk, rfl⟩
      exact oddQuotMk_comm_of_commutator_mem3 hΦ D hMΦ hxC k.2
        (hxJ.2 k (Subgroup.mem_subgroupOf.mp hk))
    have hcommM' : ∀ a ∈ modOdd c (exactCore3 c J'),
        oddQuotMk c ⟨x, hxC⟩ * a = a * oddQuotMk c ⟨x, hxC⟩ := by
      rintro _ ⟨k, hk, rfl⟩
      exact oddQuotMk_comm_of_commutator_mem3 hΦ D hM'Φ hxC k.2
        (hxJ'.2 k (Subgroup.mem_subgroupOf.mp hk))
    exact alpha_of_twinOuter3 hrows hΦ D hBab hcB hc1 hzB htB hz1 ht1 hzc htc hztc hzt1 hBeq hMΦ
      hM'Φ htU htU' hne hcomm hxC hx2 hxt hcommM hcommM' hMj hmov hLc
  exact hyp51At_of_witness_alpha3 hBelow3 hΦ hnc hMΦ
    (isSectionMember3_exactCore3 hcJ hc2 hMJ.2) hBab hcB hc1 htB htc hα

theorem twinFrameHyp51uC_of_rows3 (hrows : TwinOuterAlphaAll3) :
    Q3T8.Asc77.TwinFrameHyp51uC := by
  intro G _ _ _ Ω K K' J z u t hs hf
  exact ⟨hyp51At_u_of3 hrows hs hf (Or.inl rfl),
    hyp51At_u_of3 hrows hs hf (Or.inr (Or.inl rfl)),
    hyp51At_u_of3 hrows hs hf (Or.inr (Or.inr (Or.inl rfl))),
    hyp51At_u_of3 hrows hs hf (Or.inr (Or.inr (Or.inr rfl)))⟩

end Hyp51

end CFSG.ClassicalInvolution.Q3.Q3T7

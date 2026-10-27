module

public import CFSG.CGT.Stroth76.TFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

variable {G : Type*} [Group G] [Finite G] (K : Config G)

theorem mem_normalizer_of_conj_ev {g : G} (hg : g * g = 1) {f : Co → Co}
    (hf : ∀ v, g⁻¹ * K.ev v * g = K.ev (f v)) : g ∈ Subgroup.normalizer (K.A : Set G) := by
  have hinv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hmem : ∀ a ∈ K.A, g * a * g⁻¹ ∈ K.A := by
    intro a ha
    obtain ⟨v, rfl⟩ := K.exists_ev ha
    rw [show g * K.ev v * g⁻¹ = g⁻¹ * K.ev v * g by rw [hinv], hf]
    exact K.ev_mem _
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨hmem a, fun ha => ?_⟩
  have := hmem _ ha
  rwa [show g * (g * a * g⁻¹) * g⁻¹ = a by rw [hinv, ← mul_assoc, ← mul_assoc, hg, one_mul,
    mul_assoc, hg, mul_one]] at this

theorem Tsub_le_normalizer_A : Tsub K ≤ Subgroup.normalizer (K.A : Set G) := by
  refine sup_le Subgroup.le_normalizer ((Subgroup.closure_le _).2 ?_)
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact mem_normalizer_of_conj_ev K (uv_mul_self K) K.conj_uv_ev
  · exact mem_normalizer_of_conj_ev K (t_mul_self K) K.conj_t_ev
  · exact mem_normalizer_of_conj_ev K (u_mul_self K) K.conj_u_ev

theorem exists_T_conj_of_normalizer_A
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) {n : G}
    (hn : n ∈ Subgroup.normalizer (K.A : Set G)) :
    ∃ s ∈ Tsub K, s⁻¹ * K.w * s = n⁻¹ * K.w * n := by
  have hmem : n⁻¹ * K.w * n ∈ K.A := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) K.w).1 K.w_mem
    simpa using this
  obtain ⟨v, hv⟩ := K.exists_ev hmem
  have hconj : IsConj K.w (K.ev v) := by
    rw [hv, isConj_iff]
    exact ⟨n⁻¹, by group⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [K.ev_zero] at hv
    apply w_ne_one K
    have h := congrArg (fun z => n * z * n⁻¹) hv
    simp only [mul_one, mul_inv_cancel] at h
    rw [h]
    group
  have hv2 : 2 • v = 0 := by
    rw [← K.ev_eq_one_iff, K.ev_nsmul, hv]
    simp [pow_two, mul_assoc, ← mul_assoc K.w, ← pow_two K.w, K.hw]
  have hE : ∀ e ∈ ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G), e ∈
      Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G) :=
    fun e he => Subgroup.subset_closure he
  have hbad : ∀ e ∈ Subgroup.closure ({K.x ^ 2, K.y ^ 2, K.uv, K.t} : Set G), K.ev v = e →
      False := by
    intro e he hve
    refine hAnn1 (hconj.trans ?_)
    rw [hve]
    exact hfusE e he (by rw [← hve, Ne, K.ev_eq_one_iff]; exact hv0)
  rcases co_two_nsmul v hv2 hv0 with h | h | h | h | h | h | h <;> subst h
  · exact (hbad _ (hE _ (by simp)) (ev_020 K)).elim
  · exact (hbad _ (hE _ (by simp)) (ev_002 K)).elim
  · exact (hbad _ (Subgroup.mul_mem _ (hE _ (by simp)) (hE _ (by simp))) (ev_022 K)).elim
  · exact ⟨1, Subgroup.one_mem _, by rw [← hv, K.ev_w]; group⟩
  · exact ⟨K.t, Subgroup.mem_sup_right (t_mem_D K), by rw [conj_t_w, hv]⟩
  · exact ⟨K.uv * K.t, Subgroup.mul_mem _ (Subgroup.mem_sup_right (uv_mem_D K))
      (Subgroup.mem_sup_right (t_mem_D K)), by rw [conj_uvt_w, hv]⟩
  · exact ⟨K.uv, Subgroup.mem_sup_right (uv_mem_D K), by rw [conj_uv_w, hv]⟩

section Sylow

variable [Fact (Nat.Prime 2)]

theorem card_map_conj (m : G) (R : Subgroup G) :
    Nat.card (R.map (MulAut.conj m).toMonoidHom) = Nat.card R :=
  Subgroup.card_map_of_injective (MulAut.conj m).injective

theorem eq_Qsub_of_le
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) (hTS : Tsub K = S)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQw : Q ≤ Subgroup.centralizer {K.w})
    (hQQ : Qsub K ≤ Q) : Q = Qsub K := by
  by_contra hne
  have hlt : Qsub K < Q := lt_of_le_of_ne hQQ (Ne.symm hne)
  set R := Q ⊓ Subgroup.normalizer (Qsub K : Set G) with hRdef
  have hRgt : Qsub K < R := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hQ hlt
  have hRp : IsPGroup 2 R := hQ.to_le inf_le_left
  have hRN : R ≤ Subgroup.normalizer (K.A : Set G) := fun g hg =>
    mem_normalizer_A_of_mem_normalizer_Q K hg.2
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K.A : Set G) :=
    hTS ▸ Tsub_le_normalizer_A K
  obtain ⟨c, hcN, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (Subgroup.normalizer (K.A : Set G)) S hSN R hRN hRp
  obtain ⟨s, hsT, hs⟩ := exists_T_conj_of_normalizer_A K hfusE hAnn1 (Subgroup.inv_mem _ hcN)
  rw [inv_inv] at hs
  have hle : R.map (MulAut.conj (s * c)).toMonoidHom ≤ Qsub K := by
    rintro _ ⟨r, hr, rfl⟩
    have hcr : c * r * c⁻¹ ∈ Tsub K := by
      rw [hTS]
      exact hc ⟨r, hr, rfl⟩
    have hT : s * c * r * (s * c)⁻¹ ∈ Tsub K := by
      have := (Tsub K).mul_mem ((Tsub K).mul_mem hsT hcr) ((Tsub K).inv_mem hsT)
      rwa [show s * (c * r * c⁻¹) * s⁻¹ = s * c * r * (s * c)⁻¹ by group] at this
    have he : (MulAut.conj (s * c)).toMonoidHom r = s * c * r * (s * c)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [he]
    refine mem_Q_of_comm_w K hT ?_
    have hrw : r * K.w = K.w * r := Subgroup.mem_centralizer_singleton_iff.1 (hQw hr.1)
    have hw : s * c * K.w * (s * c)⁻¹ = K.w := by
      calc s * c * K.w * (s * c)⁻¹ = s * (c * K.w * c⁻¹) * s⁻¹ := by group
        _ = s * (s⁻¹ * K.w * s) * s⁻¹ := by rw [hs]
        _ = K.w := by group
    show s * c * r * (s * c)⁻¹ * K.w = K.w * (s * c * r * (s * c)⁻¹)
    calc s * c * r * (s * c)⁻¹ * K.w
        = s * c * r * (s * c)⁻¹ * (s * c * K.w * (s * c)⁻¹) := by rw [hw]
      _ = s * c * (r * K.w) * (s * c)⁻¹ := by group
      _ = s * c * (K.w * r) * (s * c)⁻¹ := by rw [hrw]
      _ = s * c * K.w * (s * c)⁻¹ * (s * c * r * (s * c)⁻¹) := by group
      _ = K.w * (s * c * r * (s * c)⁻¹) := by rw [hw]
  have h1 : Nat.card R ≤ Nat.card (Qsub K) := by
    rw [← card_map_conj (s * c) R]
    exact Subgroup.card_le_of_le hle
  have h2 : Nat.card (Qsub K) < Nat.card R := Subgroup.card_lt_of_lt hRgt
  omega

theorem card_le_of_le_centralizer_w
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) (hTS : Tsub K = S)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQw : Q ≤ Subgroup.centralizer {K.w}) :
    Nat.card Q ≤ 2 ^ 6 := by
  set C := Subgroup.centralizer ({K.w} : Set G)
  have hQC : IsPGroup 2 (Qsub K) :=
    (IsPGroup.of_card (card_Qsub K))
  obtain ⟨P, hP⟩ := (hQC.of_equiv (Subgroup.subgroupOfEquivOfLe (Qsub_le_centralizer_w K)).symm
    |>.exists_le_sylow)
  have hPeq : (P : Subgroup C).map C.subtype = Qsub K := by
    refine eq_Qsub_of_le K hfusE hAnn1 S hTS (P.2.map C.subtype) ?_ ?_
    · rintro _ ⟨g, -, rfl⟩
      exact g.2
    · intro q hq
      exact ⟨⟨q, Qsub_le_centralizer_w K hq⟩, hP hq, rfl⟩
  have hQ' : IsPGroup 2 (Q.subgroupOf C) := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQw).symm
  obtain ⟨P', hP'⟩ := hQ'.exists_le_sylow
  have hcard : Nat.card P' = 2 ^ 6 := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P, ← card_Qsub K, ← hPeq,
      Subgroup.card_map_of_injective C.subtype_injective]
  calc Nat.card Q = Nat.card (Q.subgroupOf C) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQw)).symm
    _ ≤ Nat.card P' := Subgroup.card_le_of_le hP'
    _ = 2 ^ 6 := hcard

end Sylow

theorem comm_ne_w {g h : G} (hg : g ∈ Tsub K) (hh : h ∈ Tsub K) : g⁻¹ * h⁻¹ * g * h ≠ K.w := by
  obtain ⟨p, rfl⟩ := exists_tElt K hg
  obtain ⟨q, rfl⟩ := exists_tElt K hh
  rw [← tElt_tinv, ← tElt_tinv, ← tElt_mul, ← tElt_mul, ← tElt_mul, ← tElt_w]
  intro he
  have := congrArg wpar (tElt_injective K he)
  simp only [wpar_tmul, wpar_tinv] at this
  revert this
  generalize wpar p = a
  generalize wpar q = b
  revert a b
  decide

@[expose] def Mcent : Subgroup G := Tsub K ⊓ Subgroup.centralizer {K.x * K.y * K.uv}

theorem card_Mcent : Nat.card (Mcent K) = 2 ^ 6 := by
  rw [← card_isCc, ← Nat.card_eq_fintype_card]
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun p : {p // IsCc p} => (⟨tElt K p, Subgroup.mem_inf.2 ⟨tElt_mem K p,
      Subgroup.mem_centralizer_singleton_iff.2 ((isCc_iff K p).1 p.2)⟩⟩ : Mcent K))
    ⟨?_, ?_⟩)
  · intro p q h
    exact Subtype.ext (tElt_injective K (congrArg Subtype.val h))
  · rintro ⟨g, hg⟩
    obtain ⟨hgT, hgc⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨p, rfl⟩ := exists_tElt K hgT
    exact ⟨⟨p, (isCc_iff K p).2 (Subgroup.mem_centralizer_singleton_iff.1 hgc)⟩, rfl⟩

theorem u_mem_Mcent : K.u ∈ Mcent K := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_sup_right (u_mem_D K),
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  rw [← tElt_gen_u]
  exact (isCc_iff K _).1 isCc_u

theorem tx_mem_Mcent : K.t * K.x ∈ Mcent K := by
  have htx : K.t * K.x = tElt K (tmul (0, (0, 1, 0)) ((0, 1, 0), 0)) := by
    rw [tElt_mul, tElt_gen_t, tElt_x]
  rw [htx]
  exact Subgroup.mem_inf.2 ⟨tElt_mem K _,
    Subgroup.mem_centralizer_singleton_iff.2 ((isCc_iff K _).1 isCc_tx)⟩

section Sylow

variable [Fact (Nat.Prime 2)]

theorem exists_conj_eq_Qsub
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) (hTS : Tsub K = S)
    {M : Subgroup G} (hMw : M ≤ Subgroup.centralizer {K.w}) (hM : Nat.card M = 2 ^ 6) :
    ∃ k ∈ Subgroup.centralizer ({K.w} : Set G), ∀ m ∈ M, k⁻¹ * m * k ∈ Qsub K := by
  set C := Subgroup.centralizer ({K.w} : Set G)
  have hQw := Qsub_le_centralizer_w K
  have hsyl : ∀ {N : Subgroup G}, N ≤ C → Nat.card N = 2 ^ 6 →
      ∃ P : Sylow 2 C, (P : Subgroup C) = N.subgroupOf C := by
    intro N hNC hN
    have hNp : IsPGroup 2 (N.subgroupOf C) := by
      refine IsPGroup.of_card (n := 6) ?_
      rw [← hN]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC)
    obtain ⟨P, hP⟩ := hNp.exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    have h1 := card_le_of_le_centralizer_w K hfusE hAnn1 S hTS (P.2.map C.subtype) (by
      rintro _ ⟨g, -, rfl⟩
      exact g.2)
    rw [Subgroup.card_map_of_injective C.subtype_injective] at h1
    calc Nat.card (P : Subgroup C) ≤ 2 ^ 6 := h1
      _ = Nat.card (N.subgroupOf C) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, hN]
  obtain ⟨P, hP⟩ := hsyl hQw (card_Qsub K)
  obtain ⟨P', hP'⟩ := hsyl hMw hM
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq C P' P
  refine ⟨(k : G)⁻¹, C.inv_mem k.2, fun m hm => ?_⟩
  have hmP' : (⟨m, hMw hm⟩ : C) ∈ (P' : Subgroup C) := by
    rw [hP']
    exact hm
  have hmem : MulAut.conj k (⟨m, hMw hm⟩ : C) ∈ (P : Subgroup C) := by
    rw [← hk, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmP'
  rw [hP] at hmem
  have : (k : G) * m * (k : G)⁻¹ ∈ Qsub K := hmem
  rwa [inv_inv]

end Sylow



section Main

variable [Fact (Nat.Prime 2)]

theorem not_isConj_w_xyuv
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) (hTS : Tsub K = S) :
    ¬ IsConj K.w (K.x * K.y * K.uv) := by
  intro hconj
  obtain ⟨h, hh⟩ := isConj_iff.1 hconj.symm
  set M := (Mcent K).map (MulAut.conj h).toMonoidHom
  have hMw : M ≤ Subgroup.centralizer {K.w} := by
    rintro _ ⟨m, hm, rfl⟩
    have hmc : m * (K.x * K.y * K.uv) = K.x * K.y * K.uv * m :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hm).2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hh]
    calc h * m * h⁻¹ * (h * (K.x * K.y * K.uv) * h⁻¹)
        = h * (m * (K.x * K.y * K.uv)) * h⁻¹ := by group
      _ = h * (K.x * K.y * K.uv * m) * h⁻¹ := by rw [hmc]
      _ = h * (K.x * K.y * K.uv) * h⁻¹ * (h * m * h⁻¹) := by group
  have hMcard : Nat.card M = 2 ^ 6 := by rw [card_map_conj, card_Mcent]
  obtain ⟨k, hk, hkM⟩ := exists_conj_eq_Qsub K hfusE hAnn1 S hTS hMw hMcard
  have hq1 := hkM _ ⟨K.u, u_mem_Mcent K, rfl⟩
  have hq2 := hkM _ ⟨K.t * K.x, tx_mem_Mcent K, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hq1 hq2
  apply comm_ne_w K (Qsub_le_Tsub K hq1) (Qsub_le_Tsub K hq2)
  have hkw : k⁻¹ * K.w * k = K.w := by
    rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.1 hk, ← mul_assoc, inv_mul_cancel,
      one_mul]
  calc (k⁻¹ * (h * K.u * h⁻¹) * k)⁻¹ * (k⁻¹ * (h * (K.t * K.x) * h⁻¹) * k)⁻¹ *
        (k⁻¹ * (h * K.u * h⁻¹) * k) * (k⁻¹ * (h * (K.t * K.x) * h⁻¹) * k)
      = k⁻¹ * (h * (K.u⁻¹ * (K.t * K.x)⁻¹ * K.u * (K.t * K.x)) * h⁻¹) * k := by group
    _ = k⁻¹ * (h * (K.x * K.y * K.uv) * h⁻¹) * k := by rw [comm_u_tx]
    _ = k⁻¹ * K.w * k := by rw [hh]
    _ = K.w := hkw

end Main

theorem arch76Lemma4 [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {u' : G} (hu' : u' = K.u ∨ u' = K.w * K.u)
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hfusW : ∀ g ∈ Subgroup.closure {K.x, K.y, K.uv, K.t, u'}, orderOf g = 2 →
      IsConj g ((K.x * K.y) ^ 2) ∨ IsConj g (K.x * K.y * K.uv))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G)
    (hTS : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ S) :
    K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≠ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hT
  change Tsub K = S at hT
  have hW : Subgroup.closure ({K.x, K.y, K.uv, K.t, u'} : Set G) ≤ Tsub K ∧
      Nat.card (Subgroup.closure ({K.x, K.y, K.uv, K.t, u'} : Set G)) = 2 ^ 7 ∧
      K.w ∉ Subgroup.closure ({K.x, K.y, K.uv, K.t, u'} : Set G) := by
    rcases hu' with rfl | rfl
    · rw [closure_u_eq]
      exact ⟨U0sub_le_Tsub K, by rw [U0sub, card_tSub, card_isU0c], w_not_mem_U0sub K⟩
    · rw [closure_wu_eq]
      exact ⟨Usub_le_Tsub K, by rw [Usub, card_tSub, card_isUc], w_not_mem_Usub K⟩
  obtain ⟨hWT, hWcard, hwW⟩ := hW
  have hTp : IsPGroup 2 (Tsub K) := hT ▸ S.isPGroup'
  have hTidx : ¬ 2 ∣ (Tsub K).index := hT ▸ S.not_dvd_index
  have hWidx : (Subgroup.closure ({K.x, K.y, K.uv, K.t, u'} : Set G)).relIndex (Tsub K) = 2 := by
    have h := Subgroup.relIndex_mul_card
      (H := Subgroup.closure ({K.x, K.y, K.uv, K.t, u'} : Set G)) (K := Tsub K)
    rw [inf_of_le_left hWT, hWcard, card_Tsub] at h
    omega
  have hwT : K.w ∈ Tsub K := Subgroup.mem_sup_left K.w_mem
  obtain ⟨g, hg⟩ := CFSG.EvenSporadicStandard.exists_conj_mem_complement hnonab hTp hTidx hWT
    hWidx hwT hwW (orderOf_w K)
  have hord : orderOf (g⁻¹ * K.w * g) = 2 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective K.w
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
    rw [this, orderOf_w]
  have hwg : IsConj K.w (g⁻¹ * K.w * g) := isConj_iff.2 ⟨g⁻¹, by group⟩
  rcases hfusW _ hg hord with h1 | h2
  · exact hAnn1 (hwg.trans h1)
  · exact not_isConj_w_xyuv K hfusE hAnn1 S hT (hwg.trans h2)

end CFSG.CGT.Stroth76

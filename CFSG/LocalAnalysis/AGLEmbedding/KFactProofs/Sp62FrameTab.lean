module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalGroups
public import Certificates.Certificate9452

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp62Local

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.Quasithin.H13 CFSG.KGroups.Sp6 CFSG.Quasithin.G2U CFSG.Open

theorem Rep.inv_of_genB {g : H6} {t : List ℕ} (hg : Rep g t) (ht : genB t = true) :
    Rep g⁻¹ (invC t) := by
  have h := rep_elt_inv ht
  have h2 : elt t = g := (rep_elt (genB_isoB ht)).eq hg
  rwa [h2] at h

theorem Rep.pow {g : H6} {t : List ℕ} (hg : Rep g t) (k : ℕ) : Rep (g ^ k) (powC t k) := by
  induction k with
  | zero => simpa [powC] using Rep.one
  | succ k ih =>
    rw [pow_succ']
    exact hg.mul ih

theorem Rep.conj {g x : H6} {c t : List ℕ} (hg : Rep g c) (hc : genB c = true) (hx : Rep x t) :
    Rep (g * x * g⁻¹) (conjC c t) := by
  unfold conjC
  rw [mul_assoc]
  exact hg.mul (hx.mul (hg.inv_of_genB hc))

theorem Rep.commutator {x n : H6} {a b : List ℕ} (hx : Rep x a) (ha : genB a = true)
    (hn : Rep n b) (hb : genB b = true) : Rep (x * (n * (x⁻¹ * n⁻¹))) (commC a b) :=
  hx.mul (hn.mul ((hx.inv_of_genB ha).mul (hn.inv_of_genB hb)))

theorem genB_cW1 : genB cW1 = true :=
  (tabCheck_spec tabCheck_T).2.2.2.2 cW1 (by simp [gensT])

theorem genB_cW2 : genB cW2 = true :=
  (tabCheck_spec tabCheck_T).2.2.2.2 cW2 (by simp [gensT])

theorem genB_cSg : genB cSg = true :=
  (tabCheck_spec tabCheck_T).2.2.2.2 cSg (by simp [gensT])

theorem mem_normalizer_zpowers {g x : H6} (h : g * x * g⁻¹ ∈ Subgroup.zpowers x) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup H6) : Set H6) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ h k

theorem sp62_frame_tables :
    chkN () = true ∧ chkTT () = true ∧ chkS0 () = true ∧ chkWordsX () = true ∧
      chkDCWords () = true :=
  Certificates.certificate9452

@[expose] def N0 : Subgroup H6 := Hgen gensN

theorem tabCheck_N : tabCheck gensN 1296 propN = true :=
  sp62_frame_tables.1

theorem N0_spec :
    propN0 (tabOf gensN 1296) = true ∧ propN1 (tabOf gensN 1296) = true ∧
      propN2 (tabOf gensN 1296) = true ∧ propN3 (tabOf gensN 1296) = true ∧
      propN4 (tabOf gensN 1296) = true := by
  simpa only [propN, Bool.and_eq_true, and_assoc] using (tabCheck_spec tabCheck_N).2.2.2.1

theorem card_N0 : Nat.card N0 = 1296 :=
  (tabCheck_spec tabCheck_N).2.2.1

theorem T0_le_N0 : T0 ≤ N0 := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, by simp only [gensT, gensN, List.mem_cons] at hc ⊢; tauto, rfl⟩

theorem B0_le_N0 : B0 ≤ N0 := by
  refine Subgroup.closure_mono ?_
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨c, by simp only [gensB, gensN, List.mem_cons] at hc ⊢; tauto, rfl⟩

theorem N0_le_normalizer_B0 :
    N0 ≤ Subgroup.normalizer (B0 : Set H6) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, rfl⟩
  exact elt_mem_normalizer_B0 hc

theorem exists_rep_genB_N0 {x : H6} (hx : x ∈ N0) :
    ∃ t ∈ tabOf gensN 1296, Rep x t ∧ genB t = true := by
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_N hx
  exact ⟨t, ht, hrep, by simpa using forall_of_allCheck N0_spec.1 t ht⟩

theorem exists_mem_N0_of_mem_tab {t : List ℕ}
    (ht : t ∈ tabOf gensN 1296) : ∃ g ∈ N0, Rep g t ∧ genB t = true := by
  obtain ⟨g, hg, hrep⟩ := (tabCheck_spec tabCheck_N).2.1 t ht
  exact ⟨g, hg, hrep, by simpa using forall_of_allCheck N0_spec.1 t ht⟩

theorem genB_of_mem_tabB {t : List ℕ}
    (ht : t ∈ tabOf gensB 27) : genB t = true := by
  have h := N0_spec.2.2.1
  simp only [propN2, Bool.and_eq_true] at h
  simpa using forall_of_allCheck h.1.1.1.1 t ht

theorem centralizer_N0_le :
    N0 ⊓ Subgroup.centralizer (B0 : Set H6) ≤ B0 := by
  rintro x ⟨hxN, hxC⟩
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_N hxN
  have hcomm := commB_gens_of_centralizes (tabCheck_spec tabCheck_B).2.2.2.2 hrep hxC
  have h1 := N0_spec.2.1
  simp only [propN1] at h1
  have h := forall_of_allCheck h1 t ht
  rw [hcomm] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact mem_Hgen_of_rep tabCheck_B (inTab_iff.1 h) hrep

theorem elt_cIo_mem_N0 : elt cIo ∈ N0 := elt_mem_Hgen (c := cIo) (by simp [gensN])

theorem genB_cIo : genB cIo = true :=
  (tabCheck_spec tabCheck_N).2.2.2.2 cIo (by simp [gensN])

theorem genB_cTau : genB cTau = true :=
  (tabCheck_spec tabCheck_N).2.2.2.2 cTau (by simp [gensN])

theorem genB_and_mem_of_inTab {c : List ℕ}
    (h : inTab (tabOf gensN 1296) c = true) : genB c = true ∧ elt c ∈ N0 := by
  obtain ⟨g, hg, hrep, hgen⟩ := exists_mem_N0_of_mem_tab (inTab_iff.1 h)
  exact ⟨hgen, ((rep_elt (genB_isoB hgen)).eq hrep).symm ▸ hg⟩

theorem cIo1_cIo2_cTau12 :
    (genB cIo1 = true ∧ elt cIo1 ∈ N0) ∧ (genB cIo2 = true ∧ elt cIo2 ∈ N0) ∧
      (genB cTau12 = true ∧ elt cTau12 ∈ N0) := by
  have h := N0_spec.2.2.2.2
  simp only [propN4, List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h
  exact ⟨genB_and_mem_of_inTab h.1, genB_and_mem_of_inTab h.2.1, genB_and_mem_of_inTab h.2.2⟩

theorem irr_B0 (W : Subgroup H6)
    (hW : N0 ≤ Subgroup.normalizer (W : Set H6)) {w : H6} (hwW : w ∈ W) (hwB : w ∈ B0)
    (hw1 : w ≠ 1) : B0 ≤ W := by
  have hnorm : ∀ {u : H6}, u ∈ N0 → ∀ x ∈ W, u * x * u⁻¹ ∈ W := fun hu x hx =>
    (Subgroup.mem_normalizer_iff.1 (hW hu) x).1 hx
  obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_B hwB
  have hgt : genB t = true := genB_of_mem_tabB ht
  have ht1 : t ≠ oneC := fun h => hw1 (hrep.eq_one_iff.2 h)
  have hirr := N0_spec.2.2.1
  simp only [propN2, Bool.and_eq_true] at hirr
  obtain ⟨⟨⟨⟨-, hirr⟩, hs0⟩, hs1⟩, hs2⟩ := hirr
  have hirrt : irrOK t = true := by
    have := forall_of_allCheck hirr t ht
    simpa [ht1] using this
  have hσN : elt cSg ∈ N0 := T0_le_N0 (elt_mem_Hgen (c := cSg) (by simp [gensT]))
  have hσrep : Rep (elt cSg) cSg := rep_elt (genB_isoB genB_cSg)
  have h0 : Rep (elt cW0) cW0 := rep_elt (genB_isoB genB_cW0)
  have h1 : Rep (elt cW1) cW1 := rep_elt (genB_isoB genB_cW1)
  have h2 : Rep (elt cW2) cW2 := rep_elt (genB_isoB genB_cW2)
  have hs0' : elt cSg * elt cW0 * (elt cSg)⁻¹ = elt cW1 :=
    ((hσrep.conj genB_cSg h0).eq_iff h1).2 (beq_iff_eq.1 hs0)
  have hs1' : elt cSg * elt cW1 * (elt cSg)⁻¹ = elt cW2 :=
    ((hσrep.conj genB_cSg h1).eq_iff h2).2 (beq_iff_eq.1 hs1)
  have hs2' : elt cSg * elt cW2 * (elt cSg)⁻¹ = elt cW0 :=
    ((hσrep.conj genB_cSg h2).eq_iff h0).2 (beq_iff_eq.1 hs2)
  have hall : elt cW0 ∈ W ∨ elt cW1 ∈ W ∨ elt cW2 ∈ W → B0 ≤ W := by
    intro h
    have h01 : elt cW0 ∈ W → elt cW1 ∈ W := fun h => hs0' ▸ hnorm hσN _ h
    have h12 : elt cW1 ∈ W → elt cW2 ∈ W := fun h => hs1' ▸ hnorm hσN _ h
    have h20 : elt cW2 ∈ W → elt cW0 ∈ W := fun h => hs2' ▸ hnorm hσN _ h
    have hA : elt cW0 ∈ W ∧ elt cW1 ∈ W ∧ elt cW2 ∈ W := by
      rcases h with h | h | h
      · exact ⟨h, h01 h, h12 (h01 h)⟩
      · exact ⟨h20 (h12 h), h, h12 h⟩
      · exact ⟨h20 h, h01 (h20 h), h⟩
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    simp only [gensB, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    exacts [hA.1, hA.2.1, hA.2.2]
  have hmain : ∀ (u om : List ℕ), genB u = true → genB om = true → elt u ∈ N0 →
      (mulC t (conjC u (invC t)) = om ∨ mulC t (conjC u (invC t)) = invC om) → elt om ∈ W := by
    intro u om hu hom huN hv
    have hmem : w * (elt u * w⁻¹ * (elt u)⁻¹) ∈ W :=
      mul_mem hwW (hnorm huN _ (inv_mem hwW))
    have hrepv : Rep (w * (elt u * w⁻¹ * (elt u)⁻¹)) (mulC t (conjC u (invC t))) :=
      hrep.mul ((rep_elt (genB_isoB hu)).conj hu (hrep.inv_of_genB hgt))
    rcases hv with hv | hv
    · rw [hv] at hrepv
      rwa [hrepv.eq (rep_elt (genB_isoB hom))] at hmem
    · rw [hv] at hrepv
      rw [hrepv.eq (rep_elt_inv hom)] at hmem
      simpa using hmem
  simp only [irrOK, List.any_eq_true, List.mem_cons, List.not_mem_nil, or_false,
    Bool.or_eq_true, beq_iff_eq] at hirrt
  obtain ⟨⟨u, om⟩, hp, hv⟩ := hirrt
  obtain ⟨⟨hIo1, hIo1N⟩, ⟨hIo2, hIo2N⟩, -⟩ := cIo1_cIo2_cTau12
  rcases hp with hp | hp | hp
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact hall (Or.inl (hmain _ _ genB_cIo genB_cW0 elt_cIo_mem_N0 hv))
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact hall (Or.inr (Or.inl (hmain _ _ hIo1 genB_cW1 hIo1N hv)))
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    exact hall (Or.inr (Or.inr (hmain _ _ hIo2 genB_cW2 hIo2N hv)))

theorem pow_81_of_isPGroup (W : Subgroup H6) (hWN : W ≤ N0)
    (hp : IsPGroup 3 W) : ∀ w ∈ W, w ^ 81 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro w hw
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hp
  have hdvd : Nat.card W ∣ 1296 := card_N0 ▸ Subgroup.card_dvd_of_le hWN
  have hn4 : n ≤ 4 := by
    by_contra hn5
    push Not at hn5
    have h5 : 3 ^ 5 ∣ 3 ^ n := pow_dvd_pow 3 hn5
    rw [← hn] at h5
    have := h5.trans hdvd
    norm_num at this
  obtain ⟨k, hk⟩ : Nat.card W ∣ 81 := by
    rw [hn]
    exact (pow_dvd_pow 3 hn4)
  have h1 : (⟨w, hw⟩ : W) ^ Nat.card W = 1 := pow_card_eq_one'
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
  rw [hk, pow_mul, h2, one_pow]

theorem pcore_N0_le
    (W : Subgroup H6) (hWN : W ≤ N0) (hW : N0 ≤ Subgroup.normalizer (W : Set H6))
    (hp : IsPGroup 3 W) : W ≤ B0 := by
  have h81 := pow_81_of_isPGroup W hWN hp
  intro x hx
  obtain ⟨t, ht, hrep, hgt⟩ := exists_rep_genB_N0 (hWN hx)
  by_cases hB : inTab (tabOf gensB 27) t = true
  · exact mem_Hgen_of_rep tabCheck_B (inTab_iff.1 hB) hrep
  · exfalso
    have h3 := N0_spec.2.2.2.1
    simp only [propN3] at h3
    have h := forall_of_allCheck h3 t ht
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Array.any_eq_true'] at h
    rcases h with (h | h) | ⟨n, hn, h⟩
    · exact hB h
    · exact h ((hrep.pow 81).eq_one_iff.1 (h81 x hx))
    · obtain ⟨n', hn'N, hnrep, hgn⟩ := exists_mem_N0_of_mem_tab hn
      have hc : x * (n' * (x⁻¹ * n'⁻¹)) ∈ W := by
        refine mul_mem hx ?_
        have := (Subgroup.mem_normalizer_iff.1 (hW hn'N) x⁻¹).1 (inv_mem hx)
        simpa [mul_assoc] using this
      have hrc := hrep.commutator hgt hnrep hgn
      exact h (((hrc.pow 81).eq_one_iff).1 (h81 _ hc))

theorem tabCheck_TT : tabCheck gensT 81 propTT = true :=
  sp62_frame_tables.2.1

theorem TT_spec :
    allCheck genB (tabOf gensT 81) = true ∧
    allCheck (fun c => inZ c || (tabOf gensT 81).all fun t =>
      !(commB c t) || inTab (tabOf gensB 27) t) (tabOf gensB 27) = true ∧
    allCheck (fun x => powC x 9 == oneC) (tabOf gensT 81) = true ∧
    allCheck (fun x => powC x 3 == oneC || (tabOf gensT 81).any fun t =>
      !((List.range 9).any fun k => conjC t x == powC x k)) (tabOf gensT 81) = true ∧
    (!(inTab (tabOf gensB 27) cSg)) = true ∧ gensT.all (commB cZ) = true ∧
    allCheck (fun x => !(gensB.all (commB x)) || inTab (tabOf gensB 27) x)
      (tabOf gensT 81) = true := by
  have h := (tabCheck_spec tabCheck_TT).2.2.2.1
  simpa only [propTT, Bool.and_eq_true, and_assoc] using h

theorem mem_B0_of_comm {c : H6}
    (hc : c ∈ B0) (hcz : c ∉ Subgroup.zpowers z0) {t : H6} (ht : t ∈ T0) (hct : c * t = t * c) :
    t ∈ B0 := by
  obtain ⟨tc, htc, hrc⟩ := Hgen_rep tabCheck_B hc
  obtain ⟨tt, htt, hrt⟩ := Hgen_rep tabCheck_T ht
  have h := forall_of_allCheck TT_spec.2.1 tc htc
  have hinZ : inZ tc = false := by
    by_contra h'
    exact hcz (mem_zpowers_z0 hrc (by simpa using h'))
  simp only [hinZ, Bool.false_or, Array.all_eq_true'] at h
  have h3 := h tt htt
  have hcomm : commB tc tt = true := beq_iff_eq.2 ((hrc.comm_iff hrt).1 hct)
  simp only [hcomm, Bool.not_true, Bool.false_or] at h3
  exact mem_Hgen_of_rep tabCheck_B (inTab_iff.1 h3) hrt

theorem nine_le_card_inf_B0 {J : Subgroup H6} (hJ : J ≤ T0)
    (hc : Nat.card J = 3 ^ 3) : 9 ≤ Nat.card (J ⊓ B0 : Subgroup H6) := by
  have h1 := Subgroup.relIndex_mul_card (H := J) (K := T0)
  rw [inf_of_le_left hJ, hc, card_T0] at h1
  have h2 := Subgroup.relIndex_mul_card (H := B0) (K := T0)
  rw [inf_of_le_left B0_le_T0, card_B0, card_T0] at h2
  have h3 := Subgroup.relIndex_inf_le (H := J) (K := B0) (L := T0)
  have h4 := Subgroup.relIndex_mul_card (H := J ⊓ B0) (K := T0)
  rw [inf_of_le_left (inf_le_left.trans hJ), card_T0] at h4
  have hj : J.relIndex T0 = 3 := by omega
  have hb : B0.relIndex T0 = 3 := by omega
  rw [hj, hb] at h3
  by_contra hlt
  push Not at hlt
  have : (J ⊓ B0).relIndex T0 * Nat.card (J ⊓ B0 : Subgroup H6) ≤ 9 * 8 :=
    Nat.mul_le_mul h3 (by omega)
  omega

theorem eq_B0_of_elemAbelian
    {J : Subgroup H6} (hJT : J ≤ T0) (hJe : IsElemAbelian 3 J) (hJc : Nat.card J = 3 ^ 3) :
    J = B0 := by
  by_contra hne
  have hnle : ¬ J ≤ B0 := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hJc, card_B0]))
  obtain ⟨x, hxJ, hxB⟩ := Set.not_subset.1 hnle
  have h9 := nine_le_card_inf_B0 hJT hJc
  have hle : J ⊓ B0 ≤ Subgroup.zpowers z0 := by
    intro f hf
    by_contra hfz
    apply hxB
    refine mem_B0_of_comm hf.2 hfz (hJT hxJ) ?_
    exact congrArg Subtype.val (hJe.1.is_comm.comm ⟨f, hf.1⟩ ⟨x, hxJ⟩)
  have h3 := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, orderOf_z0] at h3
  omega

theorem z0_mem_T0 : z0 ∈ T0 := E0_le_T0 z0_mem_E0

theorem inf_centralizer_T0 :
    T0 ⊓ Subgroup.centralizer (T0 : Set H6) = Subgroup.zpowers z0 := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.1 hx
    by_contra hxz
    have hσ : elt cSg ∈ T0 := elt_mem_Hgen (c := cSg) (by simp [gensT])
    have hxB : x ∈ B0 := by
      refine centralizer_N0_le (Subgroup.mem_inf.2 ⟨T0_le_N0 hxT, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact Subgroup.mem_centralizer_iff.1 hxC b (B0_le_T0 hb)
    have hσB := mem_B0_of_comm hxB hxz hσ (Subgroup.mem_centralizer_iff.1 hxC _ hσ).symm
    obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_B hσB
    have hteq : t = cSg := (hrep.eq_iff (rep_elt (genB_isoB genB_cSg))).1 rfl
    have := TT_spec.2.2.2.2.1
    simp only [Bool.not_eq_true'] at this
    rw [← hteq] at this
    exact absurd (inTab_iff.2 ht) (by simp [this])
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨z0_mem_T0, ?_⟩
    have hc := comm_Hgen_of_gens rep_z0 (tabCheck_spec tabCheck_T).2.2.2.2
      (fun c hc => by simpa using List.all_eq_true.1 TT_spec.2.2.2.2.2.1 c hc)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hc h hh).symm

theorem card_inf_centralizer_T0 :
    Nat.card (T0 ⊓ Subgroup.centralizer (T0 : Set H6) : Subgroup H6) = 3 := by
  rw [inf_centralizer_T0, Nat.card_zpowers, orderOf_z0]

@[expose] def S0 : Subgroup H6 := Hgen gensS0

theorem tabCheck_S0 : tabCheck gensS0 432 propS0 = true :=
  sp62_frame_tables.2.2.1

theorem card_S0 : Nat.card S0 = 432 :=
  (tabCheck_spec tabCheck_S0).2.2.1

theorem S0_spec :
    gensS0.all (fun g => inTab (tabOf gensN 1296) g &&
      (conjC g cW0 == cW0 || conjC g cW0 == mulC cW0 cW0)) = true ∧
    (!(conjC cSg cW0 == cW0 || conjC cSg cW0 == mulC cW0 cW0)) = true := by
  have h := (tabCheck_spec tabCheck_S0).2.2.2.1
  simpa only [propS0, Bool.and_eq_true] using h

theorem S0_le_N0 : S0 ≤ N0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, rfl⟩
  have h := List.all_eq_true.1 S0_spec.1 c hc
  simp only [Bool.and_eq_true] at h
  exact (genB_and_mem_of_inTab h.1).2

theorem S0_le_normalizer :
    S0 ≤ Subgroup.normalizer ((Subgroup.zpowers (elt cW0) : Subgroup H6) : Set H6) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, hc, rfl⟩
  have h := List.all_eq_true.1 S0_spec.1 c hc
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hgc, -⟩ := genB_and_mem_of_inTab h1
  have h0 : Rep (elt cW0) cW0 := rep_elt (genB_isoB genB_cW0)
  have hcj := (rep_elt (genB_isoB hgc)).conj hgc h0
  apply mem_normalizer_zpowers
  rcases h2 with h2 | h2
  · rw [h2] at hcj
    rw [hcj.eq h0]
    exact Subgroup.mem_zpowers _
  · rw [h2] at hcj
    rw [hcj.eq (h0.mul h0), ← sq]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) 2

theorem sigma_not_mem_normalizer :
    elt cSg ∉ Subgroup.normalizer ((Subgroup.zpowers (elt cW0) : Subgroup H6) : Set H6) := by
  intro hσ
  have h := S0_spec.2
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at h
  have h0 : Rep (elt cW0) cW0 := rep_elt (genB_isoB genB_cW0)
  have hσrep : Rep (elt cSg) cSg := rep_elt (genB_isoB genB_cSg)
  have hcj := hσrep.conj genB_cSg h0
  have hmem : elt cSg * elt cW0 * (elt cSg)⁻¹ ∈ Subgroup.zpowers (elt cW0) :=
    (Subgroup.mem_normalizer_iff.1 hσ (elt cW0)).1 (Subgroup.mem_zpowers _)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have h3 : elt cW0 ^ 3 = 1 := pow_three_elt (g := cW0) (by simp)
  rcases zpow_cases_of_pow_three h3 k with h4 | h4 | h4
  ·
    rw [h4] at hk
    have hω : elt cW0 = 1 := by
      have := congrArg (fun y => (elt cSg)⁻¹ * y * elt cSg) hk
      simpa [mul_assoc] using this.symm
    exact absurd (h0.eq_one_iff.1 hω) (by decide)
  · rw [h4] at hk
    exact h.1 ((hcj.eq_iff h0).1 hk.symm)
  · rw [h4] at hk
    have hsq : (elt cW0)⁻¹ = elt cW0 * elt cW0 :=
      inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact h3)
    rw [hsq] at hk
    exact h.2 ((hcj.eq_iff (h0.mul h0)).1 hk.symm)

theorem relIndex_normalizer_zpowers_N0 :
    (Subgroup.normalizer ((Subgroup.zpowers (elt cW0) : Subgroup H6) : Set H6)).relIndex N0 =
      3 := by
  set Nb := Subgroup.normalizer ((Subgroup.zpowers (elt cW0) : Subgroup H6) : Set H6) with hNb
  have hS : S0 ≤ Nb ⊓ N0 := le_inf S0_le_normalizer S0_le_N0
  have h1 := Subgroup.relIndex_mul_card (H := S0) (K := N0)
  rw [inf_of_le_left S0_le_N0, card_S0, card_N0] at h1
  have h2 : S0.relIndex N0 = 3 := by
    have h1' : S0.relIndex N0 * 432 = 3 * 432 := by rw [h1]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1'
  have h3 := Subgroup.relIndex_mul_relIndex S0 (Nb ⊓ N0) N0 hS inf_le_right
  rw [h2, Subgroup.inf_relIndex_right] at h3
  have hd : Nb.relIndex N0 ∣ 3 := Dvd.intro_left _ h3
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
  · exfalso
    rw [Subgroup.relIndex_eq_one] at h
    exact sigma_not_mem_normalizer (h (T0_le_N0 (elt_mem_Hgen (c := cSg) (by simp [gensT]))))
  · exact h

theorem genB_cGD : genB cGD = true :=
  (tabCheck_spec tabCheck_WD).2.2.2.2 cGD (by simp [gensWD])

theorem exists_rep_evalWordC {L : List (List ℕ)} (hL : ∀ c ∈ L, genB c = true) {X : Subgroup H6}
    (hX : ∀ c ∈ L, elt c ∈ X) (w : List (ℕ × Bool)) : ∃ g ∈ X, Rep g (evalWordC L w) := by
  induction w with
  | nil => exact ⟨1, one_mem _, Rep.one⟩
  | cons l w ih =>
    obtain ⟨g, hgX, hg⟩ := ih
    have hc : genB (L.getD l.1 oneC) = true ∧ elt (L.getD l.1 oneC) ∈ X := by
      rw [List.getD_eq_getElem?_getD]
      cases hl : L[l.1]? with
      | none =>
        exact ⟨genB_oneC, by rw [Option.getD_none, ← one_eq_elt_oneC]; exact one_mem _⟩
      | some c =>
        have hcL := List.mem_of_getElem? hl
        exact ⟨hL c hcL, hX c hcL⟩
    show ∃ g' ∈ X, Rep g' (mulC (letterL L l) (evalWordC L w))
    unfold letterL
    split_ifs
    · exact ⟨elt (L.getD l.1 oneC) * g, mul_mem hc.2 hgX,
        (rep_elt (genB_isoB hc.1)).mul hg⟩
    · exact ⟨(elt (L.getD l.1 oneC))⁻¹ * g, mul_mem (inv_mem hc.2) hgX,
        (rep_elt_inv hc.1).mul hg⟩

theorem elt_mem_of_evalWordC {L : List (List ℕ)} (hL : ∀ c ∈ L, genB c = true)
    {X : Subgroup H6} (hX : ∀ c ∈ L, elt c ∈ X) {w : List (ℕ × Bool)} {c : List ℕ}
    (hc : genB c = true) (hw : evalWordC L w = c) : elt c ∈ X := by
  obtain ⟨g, hgX, hg⟩ := exists_rep_evalWordC hL hX w
  rw [hw] at hg
  rw [(rep_elt (genB_isoB hc)).eq hg]
  exact hgX

theorem wordsX_spec :
    (∀ c ∈ gensX, genB c = true) ∧ (∀ c ∈ [cIo1, cTau12], commB cW0 c = true) ∧
      evalWordC gensX wordTau = cTau ∧ evalWordC gensX wordIo = cIo ∧
      evalWordC gensX wordGD = cGD ∧
      ∀ p ∈ dcPairs, genB p.1 = true := by
  have hw := sp62_frame_tables.2.2.2.1
  simp only [chkWordsX, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨hg, hcomm⟩, ht⟩, hi⟩, hd⟩, hdc⟩ := hw
  exact ⟨hg, hcomm, ht, hi, hd, fun p hp => (hdc p hp).1⟩

theorem cIo1_cTau12_mem_centralizer :
    elt cIo1 ∈ Subgroup.centralizer ({elt cW0} : Set H6) ∧
      elt cTau12 ∈ Subgroup.centralizer ({elt cW0} : Set H6) := by
  obtain ⟨⟨hg1, -⟩, -, ⟨hg2, -⟩⟩ := cIo1_cIo2_cTau12
  have hc := wordsX_spec.2.1
  have key : ∀ c, genB c = true → commB cW0 c = true →
      elt c ∈ Subgroup.centralizer ({elt cW0} : Set H6) := by
    intro c hgc hcc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (((rep_elt (genB_isoB genB_cW0)).comm_iff (rep_elt (genB_isoB hgc))).2
      (beq_iff_eq.1 hcc)).symm
  exact ⟨key _ hg1 (hc _ (by simp)), key _ hg2 (hc _ (by simp))⟩

theorem mem_of_gensX
    {X : Subgroup H6} (h : ∀ c ∈ gensX, elt c ∈ X) :
    elt cTau ∈ X ∧ elt cIo ∈ X ∧ elt cGD ∈ X := by
  obtain ⟨hL, -, ht, hi, hd, -⟩ := wordsX_spec
  exact ⟨elt_mem_of_evalWordC hL h genB_cTau ht, elt_mem_of_evalWordC hL h genB_cIo hi,
    elt_mem_of_evalWordC hL h genB_cGD hd⟩

theorem gD_mem_of_rep
    {X : Subgroup H6} (hN : N0 ≤ X) {r : List ℕ}
    (hr : r ∈ dcPairs.map Prod.fst) (hrX : elt r ∈ X) : elt cGD ∈ X := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  have hw := sp62_frame_tables.2.2.2.2
  simp only [chkDCWords, beq_iff_eq, List.all_eq_true] at hw
  have hgp : genB p.1 = true := wordsX_spec.2.2.2.2.2 p hp
  have hL : ∀ c ∈ gensN ++ [p.1], genB c = true := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact (tabCheck_spec tabCheck_N).2.2.2.2 c hc
    · rw [List.mem_singleton.1 hc]
      exact hgp
  have hX : ∀ c ∈ gensN ++ [p.1], elt c ∈ X := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact hN (elt_mem_Hgen hc)
    · rw [List.mem_singleton.1 hc]
      exact hrX
  exact elt_mem_of_evalWordC hL hX genB_cGD (hw p hp)

end CFSG.AGLEmbedding.KFactProofs.Sp62Local

module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Params
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.RedGroup
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.RedNum
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Bookkeeping
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OffenderDataOuter
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OuterTransvection
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcOrder
public import CFSG.Adapters.TauCetiExceptional.EvenB1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.QuasithinUnique.Setup CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  TauCeti CFSG.Open


theorem perm_zero_ne : exactPerm .E6 1 (⟨0, by decide⟩ : N6) ≠ ⟨0, by decide⟩ := by decide

theorem perm_five_ne : exactPerm .E6 1 (⟨5, by decide⟩ : N6) ≠ ⟨5, by decide⟩ := by decide

theorem perm_one_fix : exactPerm .E6 1 (⟨1, by decide⟩ : N6) = ⟨1, by decide⟩ := by decide

theorem exactPerm_cases (ε : Fin (exactE .E6)) : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
  obtain ⟨ev, hev⟩ := ε
  have : ev < 2 := hev
  show ev = 0 ∨ ev = 1
  omega

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem noIrrFFOffender_E6_of_interfaces
    (h27 : E6Surv27) (h78 : E6Surv78) (hinn : E6InnerOfSqOne)
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid) (hq : q.p = 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  have hcard := e6CardBound_holds
  have hout := e6OutBound_holds
  classical
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel hquad
  by_contra hcon
  have hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hcon
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_E6 q hv hq (MulEquiv.refl _)
  obtain ⟨n, hnq⟩ : ∃ n, n = q.exponent := ⟨_, rfl⟩
  have hn : 1 ≤ n := hnq ▸ q.exponent_pos
  have hK2 : Nat.card K = 2 ^ n := by rw [hK, hq, hnq]
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK2
  let eS : ↥L ⧸ Subgroup.center ↥L ≃* ↥(adjointGroup .E6 K) :=
    e.trans (e0.trans (CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.adjointQuotientEquiv .E6 K))
  have hLfin : Finite ↥L := inferInstance
  have hGfin : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid
  let f : ↥L →* ↥(adjointGroup .E6 K) :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Surjective f := eS.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker ≤ Subgroup.center ↥L := by
    intro x hx
    have h0 : eS (QuotientGroup.mk x) = 1 := hx
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = 1 :=
      eS.injective (h0.trans (map_one eS).symm)
    exact (QuotientGroup.eq_one_iff x).1 h1
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.1 hql.1
  obtain ⟨π, hπs, hπf⟩ := exists_hat (Isogeny.e6IsogenyT K) f hf hfk hperf
    (fun E' _ _ p hp hc =>
      CFSG.StandardType.LayerCycExc.e6_minGroup_exists_section hK2 E' p hp hc)
    (Isogeny.e6IsogenyT_surjective (k := K))
  let D : HatData K ↥L := ⟨f, hf, hfk, hperf, π, hπs, hπf⟩
  have hDf : ∀ x, D.f x = eS (QuotientGroup.mk x) := fun _ => rfl
  have hLnt : Nontrivial ↥L := by
    haveI := hql.2.1
    exact (QuotientGroup.mk'_surjective (Subgroup.center ↥L)).nontrivial
  obtain ⟨δ, m, k, _, _, _, ιK, ρ, hδ, hm, hρirr, hρinj, hιKinj, hWcard, hent, -, hfixS, Bf,
    hBf1, hBf2, hBf3⟩ :=
    CurtisExc.offender_periodic_data_outer hW hql.1 hirr hEN hE hel hquad hoff
      (MulEquiv.refl ↥L) hn hK2
  letI : Algebra K k := ιK.toAlgebra
  have hρ : IsSimpleRep ρ := (SL2Modules.isIrreducible_iff ρ).1 hρirr
  have hρ' : IsSimpleRep (ρ.comp π) := simpleRep_comp π hπs hρ
  obtain ⟨y, χ, J, ht⟩ := e6_exists_isCoverType hρ'
  have hδper : ∀ (i : N6) (u : Kˣ),
      χ (e6Data_valid.hm K i u) ^ (2 ^ δ) = χ (e6Data_valid.hm K i u) :=
    fun i u => chi_pow_of_entries_cover δ hρ' (fun s i j => hent (π s) i j) ht i u
  have hnper : ∀ (i : N6) (u : Kˣ),
      χ (e6Data_valid.hm K i u) ^ (2 ^ n) = χ (e6Data_valid.hm K i u) :=
    fun i u => chi_hm_pow_card hρ' ht hK2 i u
  have hnt : ∃ (x : ↥(e6Data_valid.minGroup K)) (v : Fin m → k), (ρ.comp π) x v ≠ v := by
    obtain ⟨s, hs⟩ := exists_ne (1 : ↥L)
    obtain ⟨x, rfl⟩ := hπs s
    refine ⟨x, ?_⟩
    by_contra hcon'
    push Not at hcon'
    apply hs
    apply hρinj
    rw [map_one]
    exact LinearMap.ext fun v => hcon' v
  have hg1 : 1 ≤ Nat.gcd δ n := Nat.gcd_pos_of_pos_left _ hδ
  have hbound := e6_typeBound hn hK2 k m (ρ.comp π) y χ J (Nat.gcd δ n) hρ' hnt ht hg1
    (Nat.gcd_dvd_right δ n) (fun i t => pow_two_pow_gcd _ δ n (hδper i t) (hnper i t))
  obtain ⟨hb1, hb2⟩ := hbound
  obtain ⟨hGlt, hG2⟩ := hcard K n hn hK2
  have hLle : Nat.card ↥L ≤ Nat.card ↥(e6Data_valid.minGroup K) :=
    Nat.card_le_card_of_surjective π hπs
  have hLc : Nat.card (Subgroup.center ↥L) * Nat.card ↥(adjointGroup .E6 K) = Nat.card ↥L := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
    rw [this, mul_comm]
    congr 1
    exact (Nat.card_congr eS.toEquiv).symm
  have hZS : Nat.card (Subgroup.center ↥L) * Nat.card ↥(adjointGroup .E6 K) ≤
      Nat.card ↥(e6Data_valid.minGroup K) := hLc ▸ hLle
  have hgn : Nat.gcd δ n ∣ n := Nat.gcd_dvd_right δ n
  have hgδ : Nat.gcd δ n ∣ δ := Nat.gcd_dvd_left δ n
  have hWδ : Nat.card W = 2 ^ (δ * m) := hWcard
  have hwindow : ((n / Nat.gcd δ n = 1 ∧ 79 ≤ m) ∨ (2 ≤ n / Nat.gcd δ n ∧
      78 * (n / Nat.gcd δ n) + 2 ≤ m)) → False := by
    intro hh
    obtain ⟨hw1, hw2⟩ := window_numerics hn hδ hgn hgδ hg1 hh
    by_cases hn1 : n = 1
    · have h79 := hw1 hn1
      have hK1 : Nat.card K = 2 := by rw [hK2, hn1]; rfl
      have hOut2 := fun B hc hs => (hout K B hc hs).2 hK1
      have hlt : 2 * (Nat.card (Subgroup.center ↥L) * Nat.card ↥(adjointGroup .E6 K)) <
          Nat.card W := by
        rw [hWδ]
        have := (hG2 hn1)
        calc 2 * (Nat.card (Subgroup.center ↥L) * Nat.card ↥(adjointGroup .E6 K))
            ≤ 2 * Nat.card ↥(e6Data_valid.minGroup K) := Nat.mul_le_mul_left _ hZS
          _ < 2 ^ 79 := this
          _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) h79
      exact absurd (exclusion_of_card_lt_of_outer hW hql hirr hEN hE hel eS (k := 2) hOut2 hlt)
        hcon
    · have hn2 : 2 ≤ n := by omega
      have h78n := hw2 hn2
      have hOut4 := fun B hc hs => (hout K B hc hs).1
      have hlt : 4 * (Nat.card (Subgroup.center ↥L) * Nat.card ↥(adjointGroup .E6 K)) <
          Nat.card W := by
        rw [hWδ]
        calc 4 * (Nat.card (Subgroup.center ↥L) * Nat.card ↥(adjointGroup .E6 K))
            ≤ 4 * Nat.card ↥(e6Data_valid.minGroup K) := Nat.mul_le_mul_left _ hZS
          _ < 4 * 2 ^ (78 * n) := by omega
          _ = 2 ^ (78 * n + 2) := by rw [pow_add]; ring
          _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) h78n
      exact absurd (exclusion_of_card_lt_of_outer hW hql hirr hEN hE hel eS (k := 4) hOut4 hlt)
        hcon
  have hpos : 0 < n / Nat.gcd δ n := Nat.div_pos (Nat.le_of_dvd (by omega) hgn) hg1
  by_cases ht1 : n / Nat.gcd δ n = 1
  swap
  · exact hwindow (Or.inr ⟨by omega, hb2 (by omega)⟩)
  rcases hb1 ht1 with ⟨s, b0, hs, hb0, hJ, hχv⟩ | h79
  swap
  · exact hwindow (Or.inl ⟨ht1, h79⟩)
  have hgeqn : Nat.gcd δ n = n := by
    have h1 : n = Nat.gcd δ n * (n / Nat.gcd δ n) := (Nat.mul_div_cancel' hgn).symm
    rw [ht1, mul_one] at h1
    exact h1.symm
  have hnδ : n ≤ δ := Nat.le_of_dvd hδ (hgeqn ▸ hgδ)
  obtain ⟨Θ, -, hΘrel, hΘker, -, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  have hpar : ∀ (b : MulAut W) (hb : b ∈ E), ∃ ε : Fin (exactE .E6),
      Θ (psiAut L eS (hEN hb)) = (1, Multiplicative.ofAdd ((ε : ℕ) : ZMod (exactE .E6))) ∧
      (¬ s = (⟨1, by decide⟩ : N6) → (ε : ℕ) = 0) := by
    intro b hb
    obtain ⟨hBu, hBρ⟩ := hBf1 b hb
    obtain ⟨g, a, σ, ε, hαe, h1, h2⟩ :=
      outer_params hK2 eS D hDf hρ ht (hEN hb) (Bf b) hBu hBρ
    have hεs : ¬ s = (⟨1, by decide⟩ : N6) → (ε : ℕ) = 0 := by
      intro hs1
      rcases exactPerm_cases ε with h0 | h0
      · exact h0
      · exfalso
        have hh := h2 s
        rw [h0, hJ] at hh
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, not_true_eq_false,
          false_iff, Decidable.not_not] at hh
        rcases hs with rfl | rfl | h
        · exact perm_zero_ne hh
        · exact perm_five_ne hh
        · exact hs1 h
    have hperm : exactPerm .E6 ε s = s := by
      rcases exactPerm_cases ε with h0 | h0
      · rw [h0, exactPerm_zero]; rfl
      · rw [h0]
        by_cases hs1 : s = (⟨1, by decide⟩ : N6)
        · rw [hs1]; exact perm_one_fix
        · exact absurd (hεs hs1) (by omega)
    have hσ : σ = 1 := by
      refine RingEquiv.ext fun c => ?_
      by_cases hc : c = 0
      · rw [hc, map_zero]; rfl
      · have := h1 s (Units.mk0 c hc)
        rw [hperm, hχv s, hχv s] at this
        simp only [ite_true] at this
        have h3 := frob_pow_injective b0 this
        have h4 : ((sU σ (Units.mk0 c hc) : Kˣ) : K) = c := hιKinj h3
        exact h4
    refine ⟨ε, ?_, hεs⟩
    rw [hΘrel _ g a σ ε (expr_of_eq hαe), hσ]
  let lam : ↥E →* RingAut K × Multiplicative (ZMod (exactE .E6)) :=
    Θ.comp (psiHom L eS hEN)
  have hlam : ∀ (b : MulAut W) (hb : b ∈ E), lam ⟨b, hb⟩ = Θ (psiAut L eS (hEN hb)) :=
    fun _ _ => rfl
  let K0 : Subgroup ↥E := lam.ker
  have hK0L : ∀ b : ↥E, b ∈ K0 → (b : MulAut W) ∈ L := fun b hb =>
    mem_of_theta_one hW hql.1 hirr hEN hel eS Θ hΘker hinn b.2 hb
  let jL : ↥K0 →* ↥L :=
    { toFun := fun b => ⟨(b.1 : MulAut W), hK0L b.1 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hjL : Function.Injective jL := by
    intro a b h
    have := congrArg (fun z : ↥L => (z : MulAut W)) h
    exact Subtype.ext (Subtype.ext this)
  have hE0card : Nat.card ↥jL.range = Nat.card ↥K0 :=
    (Nat.card_congr (MonoidHom.ofInjective hjL).toEquiv).symm
  have hZsq : ∀ x ∈ jL.range, x ^ 2 = 1 := by
    rintro x ⟨b, rfl⟩
    rw [← map_pow]
    have : b ^ 2 = 1 := Subtype.ext (Subtype.ext (by simpa using hel.2 _ b.1.2))
    rw [this, map_one]
  have hT : ((K0.map E.subtype : Subgroup (MulAut W)) : Set (MulAut W)) ⊆ (E : Set (MulAut W)) := by
    rintro a ⟨b', _, rfl⟩
    exact b'.2
  have hfixE0 : Nat.card {w : W // ∀ a ∈ ((K0.map E.subtype : Subgroup (MulAut W)) :
      Set (MulAut W)), a w = w} = 2 ^ (δ * Module.finrank k ↥(fixSub ρ jL.range)) := by
    have hsub : (⨅ a ∈ ((K0.map E.subtype : Subgroup (MulAut W)) : Set (MulAut W)),
        LinearMap.ker (Bf a - 1) : Submodule k (Fin m → k)) = fixSub ρ jL.range := by
      ext v
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero, mem_fixSub]
      constructor
      · intro h g hg
        obtain ⟨b, rfl⟩ := hg
        have := h b.1.1 ⟨b.1, b.2, rfl⟩
        rw [hBf2 b.1.1 b.1.2 (jL b) rfl] at this
        exact this
      · intro h a ha
        obtain ⟨b', hb', rfl⟩ := ha
        have := h (jL ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩
        rw [← hBf2 b'.1 b'.2 (jL ⟨b', hb'⟩) rfl] at this
        exact this
    rw [hBf3 _ hT, hsub]
  have hfixle : Nat.card ↥(fixV E) ≤ Nat.card {w : W // ∀ a ∈ ((K0.map E.subtype :
      Subgroup (MulAut W)) : Set (MulAut W)), a w = w} :=
    Nat.card_le_card_of_injective (fun w => ⟨w.1, fun a ha => w.2 a (hT ha)⟩)
      (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
  have hlam_fst : ∀ x : ↥E, (lam x).1 = 1 := by
    intro x
    obtain ⟨ε, h1, -⟩ := hpar x.1 x.2
    show (Θ (psiAut L eS (hEN x.2))).1 = 1
    rw [h1]
  have hidx : Nat.card ↥E ≤ 2 * Nat.card ↥K0 := by
    have h1 := Subgroup.card_mul_index K0
    have h2 : K0.index = Nat.card ↥lam.range := Subgroup.index_ker lam
    have h3 : Nat.card ↥lam.range ≤ 2 := by
      have hinj : Function.Injective (fun x : ↥lam.range => x.1.2) := by
        intro x y hxy
        obtain ⟨x1, hx1⟩ := x.2
        obtain ⟨y1, hy1⟩ := y.2
        refine Subtype.ext (Prod.ext ?_ hxy)
        rw [← hx1, ← hy1, hlam_fst, hlam_fst]
      have : Finite (Multiplicative (ZMod (exactE .E6))) :=
        Finite.of_equiv (ZMod 2) Multiplicative.ofAdd
      have := Nat.card_le_card_of_injective _ hinj
      refine this.trans (le_of_eq ?_)
      show Nat.card (Multiplicative (ZMod 2)) = 2
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h2] at h1
    calc Nat.card ↥E = Nat.card ↥K0 * Nat.card ↥lam.range := h1.symm
      _ ≤ Nat.card ↥K0 * 2 := Nat.mul_le_mul le_rfl h3
      _ = 2 * Nat.card ↥K0 := mul_comm _ _
  have hEne1 : Nat.card ↥E ≠ 1 := fun h => hE (Subgroup.card_eq_one.1 h)
  have hWpos : 0 < Nat.card W := Nat.card_pos
  by_cases hs1 : s = (⟨1, by decide⟩ : N6)
  swap
  ·
    have hs0 : s = (⟨0, by decide⟩ : N6) ∨ s = (⟨5, by decide⟩ : N6) := by
      rcases hs with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hs1
    have hK0 : K0 = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨ε, h1, h2⟩ := hpar x.1 x.2
      show lam x = 1
      rw [hlam, h1, h2 hs1]
      simp
    have hEK : Nat.card ↥E = Nat.card ↥K0 := by rw [hK0, Subgroup.card_top]
    have hE0ne : jL.range ≠ ⊥ := by
      intro h
      apply hEne1
      rw [hEK, ← hE0card, h, Subgroup.card_bot]
    obtain ⟨A, hAbot, hAsq, hAcard, hAfix⟩ := lift_fix π hπs D.hodd ρ jL.range hZsq
    have hA0 : A ≠ ⊥ := fun h => hE0ne (hAbot.1 h)
    obtain ⟨hm27, hAb⟩ := h27 K n hn hK2 k m (ρ.comp π) y χ J s b0 hρ' ht hs0 hb0 hJ hχv
    have hAb' := hAb A hAsq hA0
    rw [hAfix, hK2, hAcard] at hAb'
    have hoff' : 2 ^ (δ * 27) ≤ Nat.card ↥jL.range *
        2 ^ (δ * Module.finrank k ↥(fixSub ρ jL.range)) := by
      calc 2 ^ (δ * 27) = Nat.card W := by rw [hWδ, hm27]
        _ ≤ Nat.card ↥E * Nat.card ↥(fixV E) := hoff
        _ ≤ Nat.card ↥jL.range * 2 ^ (δ * Module.finrank k ↥(fixSub ρ jL.range)) := by
          rw [hEK, ← hE0card, ← hfixE0]
          exact Nat.mul_le_mul le_rfl hfixle
    exact surv27_contra hnδ (hAcard ▸ hAb') hoff'
  ·
    subst hs1
    obtain ⟨hm78, hAb⟩ := h78 K n hn hK2 k m (ρ.comp π) y χ J b0 hρ' ht hb0 hJ hχv
    have hW78 : Nat.card W = 2 ^ (δ * 78) := by rw [hWδ, hm78]
    by_cases hE0 : jL.range = ⊥
    ·
      have hK01 : Nat.card ↥K0 = 1 := by rw [← hE0card, hE0, Subgroup.card_bot]
      have hE2 : Nat.card ↥E ≤ 2 := by have := hidx; omega
      obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
      have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
      have hbb : b * b = 1 := by rw [← pow_two]; exact hel.2 b hb
      have hCbne : ∃ w : W, b w ≠ w := by
        by_contra h
        push Not at h
        exact hb1' (MulEquiv.ext fun w => h w)
      have hCb : fixV (Subgroup.zpowers b) ≠ ⊤ := by
        intro h
        obtain ⟨w, hw⟩ := hCbne
        have : w ∈ fixV (Subgroup.zpowers b) := by rw [h]; trivial
        exact hw (this b (Subgroup.mem_zpowers b))
      have hidxCb := Subgroup.card_mul_index (fixV (Subgroup.zpowers b))
      have hidx2 : 2 ≤ (fixV (Subgroup.zpowers b)).index := by
        have h1 : (fixV (Subgroup.zpowers b)).index ≠ 1 := fun h => hCb (Subgroup.index_eq_one.1 h)
        have h2 : (fixV (Subgroup.zpowers b)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have hfixVE : Nat.card ↥(fixV E) ≤ Nat.card ↥(fixV (Subgroup.zpowers b)) :=
        Subgroup.card_le_of_le fun w hw y hy => hw y ((Subgroup.zpowers_le.2 hb) hy)
      have hCbpos : 0 < Nat.card ↥(fixV (Subgroup.zpowers b)) := Nat.card_pos
      have hW2 : Nat.card W ≤ 2 * Nat.card ↥(fixV (Subgroup.zpowers b)) :=
        hoff.trans (Nat.mul_le_mul hE2 hfixVE)
      have hidx2' : (fixV (Subgroup.zpowers b)).index = 2 := by
        by_contra hne
        have h3 : 3 ≤ (fixV (Subgroup.zpowers b)).index := by omega
        have : Nat.card ↥(fixV (Subgroup.zpowers b)) * 3 ≤ Nat.card W := by
          rw [← hidxCb]; exact Nat.mul_le_mul le_rfl h3
        omega
      have hbtv : Nat.card W = 2 * Nat.card {w : W // b w = w} := by
        rw [card_fix_zpowers b, ← hidxCb, hidx2', mul_comm]
      have hTb : (({b} : Set (MulAut W))) ⊆ (E : Set (MulAut W)) := by simpa using hb
      have hcb := hBf3 {b} hTb
      have hcb' : Nat.card {w : W // b w = w} = 2 ^ (δ * Module.finrank k
          ↥(⨅ a ∈ ({b} : Set (MulAut W)), LinearMap.ker (Bf a - 1))) := by
        rw [← hcb]
        exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by simp)
      have hfb_le : Module.finrank k ↥(⨅ a ∈ ({b} : Set (MulAut W)), LinearMap.ker (Bf a - 1)) ≤
          m := by
        have := Submodule.finrank_le (R := k)
          (⨅ a ∈ ({b} : Set (MulAut W)), LinearMap.ker (Bf a - 1))
        rwa [Module.finrank_fin_fun] at this
      have hfb77 : Module.finrank k ↥(⨅ a ∈ ({b} : Set (MulAut W)),
          LinearMap.ker (Bf a - 1)) ≤ 77 := by
        by_contra hcon77
        have h78' : Module.finrank k ↥(⨅ a ∈ ({b} : Set (MulAut W)),
            LinearMap.ker (Bf a - 1)) = 78 := by omega
        rw [h78', ← hW78] at hcb'
        omega
      have hδ1 : δ = 1 := by
        refine surv78_single hδ hfb77 ?_
        rw [← hW78, hbtv, hcb']
      subst hδ1
      have hn1 : n = 1 := by omega
      have hK1 : Nat.card K = 2 := by rw [hK2, hn1]; rfl
      have hinv : ∀ x ∈ L, x ≠ 1 → x * x = 1 →
          2 ^ 5 * Nat.card {w : W // x w = w} ≤ Nat.card W := by
        intro x hxL hx1 hxx
        let x' : ↥L := ⟨x, hxL⟩
        have hx'1 : x' ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
        have hx'sq : x' ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hxx)
        have hZsq' : ∀ y ∈ Subgroup.zpowers x', y ^ 2 = 1 := by
          rintro y ⟨j, rfl⟩
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx'sq, one_zpow]
        obtain ⟨A', hAbot', hAsq', hAcard', hAfix'⟩ :=
          lift_fix π hπs D.hodd ρ (Subgroup.zpowers x') hZsq'
        have hA0' : A' ≠ ⊥ := by
          intro h
          have h1 := hAbot'.1 h
          have hmem : x' ∈ Subgroup.zpowers x' := Subgroup.mem_zpowers x'
          rw [h1] at hmem
          exact hx'1 (Subgroup.mem_bot.1 hmem)
        obtain ⟨hAf', -⟩ := hAb A' hAsq' hA0'
        rw [hAfix'] at hAf'
        have hcnt := hfixS (Subgroup.zpowers x')
        have e1 : ((Subgroup.zpowers x').map (MulEquiv.refl ↥L).toMonoidHom).map L.subtype =
            Subgroup.zpowers x := by
          rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
          rfl
        rw [e1, ← card_fix_zpowers] at hcnt
        rw [hcnt, hW78, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      obtain ⟨hod, hd1, hd2⟩ := CurtisExc.no_outer_transvection hW hirr (hEN hb) hbb hbtv hinv
        (d := 1 * 78) hW78
      have hN : ((Subgroup.centralizer {b}).subgroupOf L).index = 79 := by
        obtain ⟨r, hr⟩ := hod
        omega
      have h79L : 79 ∣ Nat.card ↥L := hN ▸ Subgroup.index_dvd_card _
      have h79G : 79 ∣ Nat.card ↥(e6Data_valid.minGroup K) :=
        h79L.trans (card_dvd_of_surj π hπs)
      rw [card_minGroup_E6 (K := K), CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E6,
        hK1] at h79G
      norm_num [ordE6] at h79G
    · obtain ⟨A, hAbot, hAsq, hAcard, hAfix⟩ := lift_fix π hπs D.hodd ρ jL.range hZsq
      have hA0 : A ≠ ⊥ := fun h => hE0 (hAbot.1 h)
      obtain ⟨hAf, hAc⟩ := hAb A hAsq hA0
      rw [hAfix] at hAf
      have ha : Nat.card ↥jL.range ≤ (2 ^ n) ^ 16 := by
        rw [← hAcard, ← hK2]; exact hAc
      have hoff' : 2 ^ (δ * 78) ≤ 2 * Nat.card ↥jL.range *
          2 ^ (δ * Module.finrank k ↥(fixSub ρ jL.range)) := by
        calc 2 ^ (δ * 78) = Nat.card W := hW78.symm
          _ ≤ Nat.card ↥E * Nat.card ↥(fixV E) := hoff
          _ ≤ (2 * Nat.card ↥K0) * 2 ^ (δ * Module.finrank k ↥(fixSub ρ jL.range)) := by
            rw [← hfixE0]
            exact Nat.mul_le_mul hidx hfixle
          _ = 2 * Nat.card ↥jL.range * 2 ^ (δ * Module.finrank k ↥(fixSub ρ jL.range)) := by
            rw [hE0card]
      exact surv78_contra hnδ hδ hAf ha hoff'

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

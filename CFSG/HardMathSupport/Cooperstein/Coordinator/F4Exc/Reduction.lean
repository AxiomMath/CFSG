module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSection
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.ReductionArith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.OffenderDataFix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Twist
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OuterBound
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.OffenderBound
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8Arith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.GenPeriodic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc.Survivor
public import CFSG.Monster.B.TwoA.Base.ElemAut

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.Blueprint CFSG.Blueprint.Chevalley TauCeti
  CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.Open
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev

section Glue

variable {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {G : Type} [Group G]

@[expose] def phiOfF (ι : G ≃* ↥L) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) : MulAut G :=
  ι.trans ((X1.conjAut L hb).trans ι.symm)

theorem phiOfF_apply (ι : G ≃* ↥L) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (x : G) :
    phiOfF ι hb x = ι.symm (X1.conjAut L hb (ι x)) := rfl

theorem psiAut_eq_phiOfF (eS : ↥L ⧸ Subgroup.center ↥L ≃* G) (ι : G ≃* ↥L)
    (hι : ∀ l, ι.symm l = eS (QuotientGroup.mk l)) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) : psiAut L eS hb = phiOfF ι hb := by
  refine MulEquiv.ext fun x => ?_
  have hx' : eS (QuotientGroup.mk (ι x)) = x := by rw [← hι]; exact MulEquiv.symm_apply_apply ι x
  rw [phiOfF_apply, hι]
  calc psiAut L eS hb x = psiAut L eS hb (eS (QuotientGroup.mk (ι x))) := by rw [hx']
    _ = _ := psiAut_mk eS hb (ι x)

theorem phiOfF_sq (ι : G ≃* ↥L) {b : MulAut W}
    (hb : b ∈ Subgroup.normalizer (L : Set (MulAut W))) (hb2 : b * b = 1) :
    phiOfF ι hb * phiOfF ι hb = 1 := by
  refine MulEquiv.ext fun x => ?_
  show phiOfF ι hb (phiOfF ι hb x) = x
  rw [phiOfF_apply, phiOfF_apply, MulEquiv.apply_symm_apply]
  have : ι.symm (X1.conjAut L hb (X1.conjAut L hb (ι x))) = x := by
    have h : X1.conjAut L hb (X1.conjAut L hb (ι x)) = ι x := by
      apply Subtype.ext
      rw [X1.coe_conjAut, X1.coe_conjAut]
      calc b * (b * (ι x : MulAut W) * b⁻¹) * b⁻¹ = (b * b) * (ι x : MulAut W) * (b * b)⁻¹ := by
            group
        _ = (ι x : MulAut W) := by rw [hb2]; group
    rw [h, MulEquiv.symm_apply_apply]
  exact this

end Glue

section Chi


variable {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem chi_dC_powF {ρ : Representation k (adjointGroup τ K) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (i : Fin τ.rank) (t : Kˣ) (N : ℕ) :
    χ (dC τ K i (t ^ N)) = χ (dC τ K i t) ^ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  induction N with
  | zero => rw [pow_zero, dC_one, pow_zero]; exact hμ.chi_one
  | succ N ih =>
    rw [pow_succ, dC_mul, hμ.chi_mul (dC_mem_H i _) (dC_mem_H i _), ih, pow_succ]

theorem chi_dC_pow_cardF {ρ : Representation k (adjointGroup τ K) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) {n : ℕ} (hK : Nat.card K = 2 ^ n) (i : Fin τ.rank)
    (t : Kˣ) : χ (dC τ K i t) ^ (2 ^ n) = χ (dC τ K i t) := by
  have h1 : t ^ (2 ^ n - 1) = 1 := by
    have := pow_card_eq_one' (G := Kˣ) (x := t)
    rwa [Nat.card_units, hK] at this
  have h2 : χ (dC τ K i t) ^ (2 ^ n - 1) = 1 := by
    rw [← chi_dC_powF hρ ht, h1, dC_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
    exact hμ.chi_one
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  calc χ (dC τ K i t) ^ (2 ^ n) = χ (dC τ K i t) ^ (2 ^ n - 1) * χ (dC τ K i t) := by
        rw [← pow_succ]; congr 1; omega
    _ = χ (dC τ K i t) := by rw [h2, one_mul]

end Chi

section Main


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem noIrrFFOffender_F4 (q : PrimePower) (hv : (LieTypeIndex.F4 q).Valid) (hq : q.p = 2) :
    NoIrrFFOffender (CFSGIndex.lie ⟨.F4 q, hv⟩).Group := by
  classical
  intro W _ _ hW L E hql hirr ⟨e⟩ hEN hE hel hquad
  by_contra hcon
  have hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E) := not_lt.1 hcon
  obtain ⟨K, _, _, hK, ⟨e0⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
    CFSG.TauCetiBridge.Even.untwistedBridgeEven_F4 q hv hq (MulEquiv.refl _)
  obtain ⟨n, hnq⟩ : ∃ n, n = q.exponent := ⟨_, rfl⟩
  have hn : 1 ≤ n := hnq ▸ q.exponent_pos
  have hK2 : Nat.card K = 2 ^ n := by rw [hK, hq, hnq]
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK2
  have hZ : Subgroup.center ↥L = ⊥ :=
    center_eq_bot_of_F4 hql (odd_card_center_of_isIrrOn hW hirr) hn hK2 (e.trans e0)
  let eS : ↥L ⧸ Subgroup.center ↥L ≃* adjointGroup .F4 K :=
    e.trans (e0.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv .F4 K))
  let f : ↥L →* adjointGroup .F4 K :=
    eS.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hf : Function.Bijective f := by
    refine ⟨fun x y hxy => ?_, eS.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    have h1 : (QuotientGroup.mk x : ↥L ⧸ Subgroup.center ↥L) = QuotientGroup.mk y :=
      eS.injective hxy
    rw [QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact h1
  let ι : adjointGroup .F4 K ≃* ↥L := (MulEquiv.ofBijective f hf).symm
  have hι : ∀ l, ι.symm l = eS (QuotientGroup.mk l) := fun l => rfl
  have hnt : Nontrivial (adjointGroup .F4 K) :=
    ⟨⟨xC .F4 K (f4n 0) 1, 1, xC_ne_one (f4n 0) 1⟩⟩
  obtain ⟨δ, m, k, _, _, _, ιK, ρ, hδ, hm, hρirr, hρinj, hιKinj, hWcard, hent, hext, hfix⟩ :=
    offender_periodic_data_fix hW hql.1 hirr hEN hE hel hquad hoff ι hn hK2
  letI : Algebra K k := ιK.toAlgebra
  have hρ : IsSimpleRep ρ := (SL2Modules.isIrreducible_iff ρ).1 hρirr
  obtain ⟨y, χ, J, ht⟩ := exists_isChevType (hw := FFExc.exists_weyl_neg_F4') (p := 2) hρ
  have hδper : ∀ (i : Fin Tag.F4.rank) (t : Kˣ), χ (dC .F4 K i t) ^ (2 ^ δ) = χ (dC .F4 K i t) :=
    fun i t => chi_pow_of_entries δ hρ hent ht _ (dC_mem_H i t)
  have hnper := fun (i : Fin Tag.F4.rank) (t : Kˣ) => chi_dC_pow_cardF hρ ht hK2 i t
  have hbound := f4TypeBound hn hK2 k m ρ y χ J
  have hG : Nat.card (adjointGroup .F4 K) < 2 ^ (52 * n) := by
    rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK2]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have := ordF4_lt h2
    rwa [← pow_mul, mul_comm] at this
  obtain ⟨-, hnf0, ⟨Θ0, hΘrel0, -, hΘker0⟩, hinv0, -, -, -⟩ :=
    CFSG.LieType.Chevalley.even_F4_exact_automorphism_normal_form (f := n) hn K hK2
  let Θ : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * n)) := Θ0
  have hnf : ∀ α : MulAut (adjointGroup .F4 K), ∃! gk : adjointGroup .F4 K × Fin (2 * n),
      α = MulAut.conj gk.1 * FFExc.phiF4 K ^ (gk.2 : ℕ) := hnf0
  have hΘrel : ∀ (α : MulAut (adjointGroup .F4 K)) (g : adjointGroup .F4 K) (k : ℕ),
      α = MulAut.conj g * FFExc.phiF4 K ^ k → Θ α = Multiplicative.ofAdd (k : ZMod (2 * n)) :=
    hΘrel0
  have hΘker : Θ.ker = (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    hΘker0
  have hinv : ∀ (α : MulAut (adjointGroup .F4 K)) (g : adjointGroup .F4 K) (k : ℕ), k < 2 * n →
      α = MulAut.conj g * FFExc.phiF4 K ^ k → α ^ 2 = 1 → k = 0 ∨ k = n := hinv0
  have hg1 : 1 ≤ Nat.gcd δ n := Nat.gcd_pos_of_pos_left _ hδ
  have hper : ∀ (i : Fin Tag.F4.rank) (t : Kˣ),
      χ (dC .F4 K i t) ^ (2 ^ Nat.gcd δ n) = χ (dC .F4 K i t) :=
    fun i t => pow_two_pow_gcd _ δ n (hδper i t) (hnper i t)
  have hboundg := hbound (Nat.gcd δ n) hρ hρinj ht hg1 (Nat.gcd_dvd_right δ n) hper
  by_cases hout : ∃ (a : MulAut W) (ha : a ∈ E), Θ (phiOfF ι (hEN ha)) ≠ 1
  ·
    obtain ⟨a, ha, hΘ1⟩ := hout
    have hφ2 := phiOfF_sq ι (hEN ha) (by rw [← pow_two]; exact hel.2 a ha)
    obtain ⟨⟨g, kk⟩, hgk, -⟩ := hnf (phiOfF ι (hEN ha))
    have hk : (kk : ℕ) = 0 ∨ (kk : ℕ) = n :=
      hinv (phiOfF ι (hEN ha)) g (kk : ℕ) kk.2 hgk (by rw [pow_two]; exact hφ2)
    have hkn : (kk : ℕ) = n := by
      rcases hk with h | h
      · exfalso
        apply hΘ1
        rw [hΘrel _ g (kk : ℕ) hgk, h]
        simp
      · exact h
    obtain ⟨B, hBu, hB⟩ := hext a ha
    rcases hboundg with hdim | ⟨-, hS⟩
    · have hnum := nonsurv_numerics hg1 (Nat.gcd_dvd_right δ n) (Nat.gcd_dvd_left δ n) hδ hdim
      have hOut : ∀ B : Subgroup (MulAut (adjointGroup .F4 K)),
          (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
          Nat.card B ≤ 2 * Nat.card ↥(B ⊓ (MulAut.conj : adjointGroup .F4 K →* MulAut _).range) := by
        intro B _ hBsq
        rw [← hΘker]
        refine card_le_two_mul_of_theta Θ B ?_
        intro b hb b' hb' h1 h1'
        have key : ∀ b ∈ B, Θ b ≠ 1 → Θ b = Multiplicative.ofAdd (n : ZMod (2 * n)) := by
          intro b hb hb1
          obtain ⟨⟨g', k'⟩, hgk', -⟩ := hnf b
          have hk' : (k' : ℕ) = 0 ∨ (k' : ℕ) = n :=
            hinv b g' (k' : ℕ) k'.2 hgk' (by rw [pow_two]; exact hBsq b hb)
          rcases hk' with h | h
          · exfalso; apply hb1; rw [hΘrel b g' (k' : ℕ) hgk', h]; simp
          · rw [hΘrel b g' (k' : ℕ) hgk', h]
        exact (key b hb h1).trans (key b' hb' h1').symm
      have hlt : 2 * (Nat.card (Subgroup.center ↥L) * Nat.card (adjointGroup .F4 K)) < Nat.card W := by
        rw [hZ, Subgroup.card_bot, one_mul, hWcard]
        calc 2 * Nat.card (adjointGroup .F4 K) < 2 * 2 ^ (52 * n) := by omega
          _ = 2 ^ (52 * n + 1) := by rw [pow_succ]; ring
          _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) hnum
      exact absurd (exclusion_of_card_lt_of_outer hW hql hirr hEN hE hel eS (k := 2) hOut hlt) hcon
    ·
      refine survivor_no_twist hn hK2 hρ ht hS B hBu g (fun s => ?_)
      have h1 := hB s
      rw [← phiOfF_apply ι (hEN ha) s, hgk, hkn] at h1
      exact h1
  ·
    push Not at hout
    have hEL : E ≤ L := by
      intro a ha
      have h1 : phiOfF ι (hEN ha) ∈ Θ.ker := hout a ha
      rw [hΘker] at h1
      obtain ⟨s, hs⟩ := h1
      refine mem_of_psiAut_inner hW hql.1 hirr hEN hel eS ha s fun x => ?_
      rw [psiAut_eq_phiOfF eS ι hι, ← hs, MulAut.conj_apply]
    rcases hboundg with hdim | ⟨ht1, hS⟩
    · have hnum := nonsurv_numerics hg1 (Nat.gcd_dvd_right δ n) (Nat.gcd_dvd_left δ n) hδ hdim
      have hlt : Nat.card ↥(L ⊔ E) < Nat.card W := by
        rw [sup_eq_left.2 hEL, hWcard]
        calc Nat.card ↥L = Nat.card (adjointGroup .F4 K) := Nat.card_congr ι.symm.toEquiv
          _ < 2 ^ (52 * n) := hG
          _ ≤ 2 ^ (δ * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact absurd (card_mul_card_fixV_lt_of_card_sup_lt hW hql hirr hEN hE hel hlt) hcon
    ·
      have hgn : Nat.gcd δ n = n := by
        have h := Nat.div_mul_cancel (Nat.gcd_dvd_right δ n)
        rw [ht1, one_mul] at h
        exact h
      have hnδ : n ≤ δ := by
        have : n ∣ δ := by rw [← hgn]; exact Nat.gcd_dvd_left δ n
        exact Nat.le_of_dvd hδ this
      set A : Subgroup (adjointGroup .F4 K) := (E.subgroupOf L).map ι.symm.toMonoidHom with hA
      have hAι : A.map ι.toMonoidHom = E.subgroupOf L := by
        rw [hA, Subgroup.map_map]
        have : ι.toMonoidHom.comp ι.symm.toMonoidHom = MonoidHom.id _ := by
          ext x; simp
        rw [this, Subgroup.map_id]
      have hAE : (A.map ι.toMonoidHom).map L.subtype = E := by
        rw [hAι, Subgroup.subgroupOf_map_subtype]
        exact inf_eq_left.2 hEL
      have hAcard : Nat.card A = Nat.card E := by
        rw [hA, Subgroup.card_map_of_injective ι.symm.injective]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
      have hAne : A ≠ ⊥ := by
        intro h0
        apply hE
        rw [← hAE, h0]
        simp
      have hAel : ∀ a ∈ A, a ^ 2 = 1 := by
        intro a ha
        have h1 : ((ι a : ↥L) : MulAut W) ∈ E := by
          have : ((ι a : ↥L) : MulAut W) ∈ (A.map ι.toMonoidHom).map L.subtype :=
            ⟨ι a, ⟨a, ha, rfl⟩, rfl⟩
          rwa [hAE] at this
        have h2 := hel.2 _ h1
        apply ι.injective
        rw [map_pow, map_one]
        apply Subtype.ext
        simpa [pow_two] using h2
      obtain ⟨hm26, hbd⟩ := survivor_fixed_bound hρ ht hS A hAne hAel
      have hfixA := hfix A
      rw [hAE] at hfixA
      set fd := Module.finrank k (fixSub ρ A) with hfd
      rw [hAcard, hK2] at hbd
      have hbd2 : Nat.card E * 2 ^ (n * fd) ≤ 2 ^ (25 * n) := by
        calc Nat.card E * 2 ^ (n * fd) = Nat.card E * (2 ^ n) ^ fd := by rw [pow_mul]
          _ ≤ (2 ^ n) ^ 25 := hbd
          _ = 2 ^ (25 * n) := by rw [← pow_mul, mul_comm]
      rw [hfixA, hWcard, hm26] at hoff
      have hEpos : 0 < Nat.card E := Nat.card_pos
      have hfd25 : fd ≤ 25 := by
        by_contra h
        push Not at h
        have : 2 ^ (25 * n) < 2 ^ (n * fd) :=
          Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
        have h2 : 2 ^ (n * fd) ≤ Nat.card E * 2 ^ (n * fd) := Nat.le_mul_of_pos_left _ hEpos
        omega
      have key : 2 ^ (δ * 26 + n * fd) ≤ 2 ^ (25 * n + δ * fd) := by
        calc 2 ^ (δ * 26 + n * fd) = 2 ^ (δ * 26) * 2 ^ (n * fd) := pow_add _ _ _
          _ ≤ (Nat.card E * 2 ^ (δ * fd)) * 2 ^ (n * fd) := Nat.mul_le_mul_right _ hoff
          _ = (Nat.card E * 2 ^ (n * fd)) * 2 ^ (δ * fd) := by ring
          _ ≤ 2 ^ (25 * n) * 2 ^ (δ * fd) := Nat.mul_le_mul_right _ hbd2
          _ = 2 ^ (25 * n + δ * fd) := (pow_add _ _ _).symm
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 key
      nlinarith

end Main

end CFSG.HardMathSupport.Cooperstein.Coordinator.F4Exc

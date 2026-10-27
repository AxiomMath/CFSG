module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCHeOut
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCHeUniq

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem exists_conj_of_inverts_odd {t w : X} (htw : t * w * t⁻¹ = w⁻¹)
    (hw : Odd (orderOf w)) : ∃ o : X, o * t * o⁻¹ = w * t := by
  obtain ⟨k, hk⟩ := hw
  refine ⟨w ^ (k + 1), ?_⟩
  have h1 : t * w ^ (k + 1) * t⁻¹ = (w ^ (k + 1))⁻¹ := by
    have h2 := map_pow (MulAut.conj t) w (k + 1)
    rw [MulAut.conj_apply, MulAut.conj_apply, htw, inv_pow] at h2
    exact h2
  have h3 : t * (w ^ (k + 1))⁻¹ * t⁻¹ = w ^ (k + 1) := by
    calc t * (w ^ (k + 1))⁻¹ * t⁻¹ = (t * w ^ (k + 1) * t⁻¹)⁻¹ := by group
      _ = w ^ (k + 1) := by rw [h1, inv_inv]
  calc w ^ (k + 1) * t * (w ^ (k + 1))⁻¹ = w ^ (k + 1) * (t * (w ^ (k + 1))⁻¹ * t⁻¹) * t := by
        group
    _ = w ^ (k + 1 + (k + 1)) * t := by rw [h3, ← pow_add]
    _ = w ^ (2 * k + 1) * w * t := by rw [show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ]
    _ = w * t := by rw [← hk, pow_orderOf_eq_one, one_mul]

omit [Finite X] in
theorem exists_conj_of_odd_mul {a t g w : X} (haa : a * a = 1) (htt : t * t = 1)
    (hg : g * a * g⁻¹ = w * t) (hw : Odd (orderOf w)) : ∃ g' : X, g' * a * g'⁻¹ = t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hv2 : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [haa, mul_one, mul_inv_cancel]
  have hvinv : (g * a * g⁻¹)⁻¹ = g * a * g⁻¹ := inv_eq_of_mul_eq_one_right hv2
  have hwv : w = g * a * g⁻¹ * t := by
    calc w = w * t * t⁻¹ := by group
      _ = g * a * g⁻¹ * t := by rw [← hg, htinv]
  have htw : t * w * t⁻¹ = w⁻¹ := by
    calc t * w * t⁻¹ = t * (g * a * g⁻¹) * (t * t) := by rw [hwv, htinv]; group
      _ = t⁻¹ * (g * a * g⁻¹)⁻¹ := by rw [htt, mul_one, htinv, hvinv]
      _ = w⁻¹ := by rw [hwv]; group
  obtain ⟨o, ho⟩ := exists_conj_of_inverts_odd htw hw
  refine ⟨o⁻¹ * g, ?_⟩
  calc o⁻¹ * g * a * (o⁻¹ * g)⁻¹ = o⁻¹ * (g * a * g⁻¹) * o := by group
    _ = o⁻¹ * (o * t * o⁻¹) * o := by rw [hg, ho]
    _ = t := by group

omit [Finite X] in
theorem center_eq_bot_of_held {Q : Type*} [Group Q]
    (θ₀ : Q ≃* Blueprint.NativeSporadic.He) : center Q = ⊥ := by
  have hs : IsSimpleGroup Q := @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He θ₀
  rcases hs.eq_bot_or_eq_top_of_normal (center Q) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative Q := ⟨⟨fun x y => mem_center_iff.mp (h ▸ mem_top y) x⟩⟩
    have hp := Group.is_simple_iff_prime_card.mp hs
    rw [Nat.card_congr θ₀.toEquiv, Sporadic.He.card_He] at hp
    norm_num at hp

omit [Finite X] in
theorem oddQuotConj_of_mem {M : Subgroup X} {m : X} (hm : m ∈ M) :
    oddQuotConj M ⟨m, Subgroup.le_normalizer hm⟩ =
      MulAut.conj ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [oddQuotConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1

omit [Finite X] in
theorem center_eq_bot_of_equiv {Q R : Type*} [Group Q] [Group R] (e : Q ≃* R)
    (hR : center R = ⊥) : center Q = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  have h1 : e c ∈ center R := by
    rw [mem_center_iff]
    intro g
    obtain ⟨q, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hc q]
  rw [hR, mem_bot, map_eq_one_iff e e.injective] at h1
  exact mem_bot.mpr h1

omit [Finite X] in
theorem mem_oddIn_of_oddQuotConj_eq_one {M : Subgroup X}
    (hZ : center (↥M ⧸ pPrimeCore 2 ↥M) = ⊥) {m : X} (hm : m ∈ M)
    (h1 : oddQuotConj M ⟨m, Subgroup.le_normalizer hm⟩ = 1) :
    m ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  rw [oddQuotConj_of_mem hm] at h1
  have hc : ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
    rw [mem_center_iff]
    intro q
    have h2 := congrArg (fun f : MulAut (↥M ⧸ pPrimeCore 2 ↥M) => f q) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc q * ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) =
        ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) * q *
          ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M)⁻¹ *
          ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := by rw [h2]
      _ = ((⟨m, hm⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) * q := by group
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hc
  exact ⟨⟨m, hm⟩, hc, rfl⟩

theorem Config.mem_gsFixedLayer {a : X} {J E : Subgroup X} (h : Config a J E) {b : X}
    (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel J) {z : X} (hzJ : z ∈ J)
    (hz2 : orderOf z = 2) (hzb : z * b = b * z) : z ∈ gsFixedLayer J b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ h.le_centralizer).mp
      h.isPComponent).2.2
  have hb2 : IsPGroup 2 (zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb, pow_one])
  rw [← GSLit.fixedLayer_zpowers, GSLit.fixedLayer_eq_closure hJq (zpowers_le.mpr hbK) hb2]
  refine subset_closure ⟨mem_inf.mpr ⟨hzJ, mem_centralizer_iff.mpr fun g hg => ?_⟩,
    1, by rw [hz2, pow_one]⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  exact ((show Commute z b from hzb).symm.zpow_left n).eq

open CFSG.Sporadic.HeldB in
theorem held_outer_conj
    {S : Type} [Group S] (θ₀ : S ≃* Blueprint.NativeSporadic.He) {α α' : MulAut S}
    (hα : orderOf α = 2) (hout : α ∉ (MulAut.conj : S →* MulAut S).range)
    (hα' : orderOf α' = 2) (hout' : α' ∉ (MulAut.conj : S →* MulAut S).range) :
    ∃ s : S, α' = MulAut.conj s * α * (MulAut.conj s)⁻¹ := by
  obtain ⟨hbij, -, -, -, -, -⟩ := ctbh_full_automorphism_permutation_model
  obtain ⟨-, hcls, -⟩ := ctbh_outer_involution_class_exhaustion
  set θ : S ≃* heP := θ₀.trans heEquivP with hθ
  have hcls' : ∀ w : heAutGroup, (w : Equiv.Perm (Fin 8330)) ∉ heP →
      orderOf (w : Equiv.Perm (Fin 8330)) = 2 →
      ∃ g ∈ heP, (w : Equiv.Perm (Fin 8330)) = g * heAutU * g⁻¹ := by
    intro w hwP hw2
    have hmem : (w : Equiv.Perm (Fin 8330)) ∈ {z : Equiv.Perm (Fin 8330) |
        z ∈ heAutGroup ∧ z ∉ heP ∧ orderOf z = 2} := ⟨w.2, hwP, hw2⟩
    rw [hcls] at hmem
    exact hmem
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq hbij (MulAut.congr θ α)
    (by rw [orderOf_congr, hα]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨x', hx', hx'P, hx'2⟩ := exists_heConjR_eq hbij (MulAut.congr θ α')
    (by rw [orderOf_congr, hα']) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := hcls' x hxP hx2
  obtain ⟨g', hg', hx'g⟩ := hcls' x' hx'P hx'2
  have hhP : g' * g⁻¹ ∈ heP := heP.mul_mem hg' (heP.inv_mem hg)
  set h : heP := ⟨g' * g⁻¹, hhP⟩ with hh
  set hR : heAutGroup := ⟨g' * g⁻¹, heP_le_heAutGroup hhP⟩ with hhR
  have hx'x : x' = hR * x * hR⁻¹ := by
    apply Subtype.ext
    simp only [hhR, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx'g, hxg]
    group
  have hRc : heConjR hR = MulAut.conj h := by
    refine MulEquiv.ext fun p => Subtype.ext ?_
    rw [heConjR_apply, MulAut.conj_apply]
    rfl
  refine ⟨θ.symm h, ?_⟩
  apply (MulAut.congr θ).injective
  rw [map_mul, map_mul, map_inv, congr_conj, MulEquiv.apply_symm_apply, ← hx, ← hx', hx'x,
    map_mul, map_mul, map_inv, hRc]

theorem Config.held_fusion
    (hTB : GSLit.ThompsonBurgoyneInput) (hSA : SolAltLit.SolomonAlternatingOddInput)
    (hS : SchreierFor Blueprint.Catalog) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (h : Config a J E)
    {b y : X} {M : Subgroup X} (hb : orderOf b = 2) (hbK : b ∈ coreActionKernel J)
    (hab : a * b = b * a) (hUM : GSUnbalancingTriple b y M) (hMa : conjugate M a = M)
    (hTM : gsFixedLayer J b ≤ M) (hHe : GrSLit.IsHeldType (M ⧸ Open.fusionZStar M)) {z : X}
    (hzJ : z ∈ J) (hz2 : orderOf z = 2) (hzb : z * b = b * z) :
    ∃ g : X, g * a * g⁻¹ = a * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbN, hbc⟩ := mem_coreActionKernel.mp hbK
  obtain ⟨-, -, -, hMb, hMc, -, -⟩ := gsUnbalancingTriple_iff.mp hUM
  have ha := h.orderOf_eq
  have hJa := h.le_centralizer
  have hJ := h.isPComponent
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hza : z * a = a * z := mem_centralizer_singleton_iff.mp (hJa hzJ)
  have hbZ : b ∉ center X := GSLit.not_mem_center_of_orderOf_eq_two hnonab hb
  obtain ⟨θ₀⟩ := held_equiv_of_unbalancing hTB hSA hnonab hK hz hU hUM hHe
  have hMsup : M ⊔ conjugate M a = M := by rw [hMa, sup_idem]
  have hW : GrSLit.GSWeakCorr a J b M :=
    ⟨ha, hb, hab, hJa, hJ, hMb, hMc, hbN, hbc, by rw [hMsup]; exact hTM⟩
  obtain ⟨hTN, hTpc, ⟨φ⟩⟩ := GrSLit.gsFixedLayer_isPComponent_of_gsWeakCorr hS hK hW hbZ
  rw [hMsup] at hTN hTpc
  obtain ⟨e7⟩ := h.equiv
  have hT7 : Nonempty (↥(gsFixedLayer J b) ⧸ pPrimeCore 2 ↥(gsFixedLayer J b) ≃*
      alternatingGroup (Fin 7)) := ⟨φ.trans e7⟩
  have haN : a ∈ normalizer (M : Set X) := mem_normalizer_of_conjugate_eq hMa
  have hout := not_mem_conj_range_of_fixed_alternating GrSLit.HeldFix.isL34Type_of_isPComponent_centralizer_heA0
    GrSLit.HeldFix.not_isPComponent_centralizer_heT1P ⟨θ₀⟩ haN haa hTN hTpc
    (nonempty_fusionZStar_equiv_alternating hT7)
  have hzM : z ∈ M := hTM (h.mem_gsFixedLayer hb hbK hzJ hz2 hzb)
  set σ := oddQuotConj M with hσ
  set A : ↥(normalizer (M : Set X)) := ⟨a, haN⟩ with hA
  set Z : ↥(normalizer (M : Set X)) := ⟨z, Subgroup.le_normalizer hzM⟩ with hZ
  have hσZ : σ Z = MulAut.conj ((⟨z, hzM⟩ : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := oddQuotConj_of_mem hzM
  have hout' : σ (A * Z) ∉
      (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut (↥M ⧸ pPrimeCore 2 ↥M)).range := by
    intro hmem
    apply hout
    have h1 : σ A = σ (A * Z) * (σ Z)⁻¹ := by rw [map_mul, mul_inv_cancel_right]
    rw [h1]
    exact mul_mem hmem (inv_mem ⟨_, hσZ.symm⟩)
  have ht2 : a * z * (a * z) = 1 := by
    calc a * z * (a * z) = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [hza]
      _ = a * a * (z * z) := by group
      _ = 1 := by rw [haa, hzz, one_mul]
  have hord : ∀ N : ↥(normalizer (M : Set X)), N * N = 1 →
      σ N ∉ (MulAut.conj : (↥M ⧸ pPrimeCore 2 ↥M) →* MulAut (↥M ⧸ pPrimeCore 2 ↥M)).range →
      orderOf (σ N) = 2 := fun N hN hNo =>
    orderOf_eq_prime (by rw [pow_two, ← map_mul, hN, map_one]) fun h1 =>
      hNo ⟨1, by rw [map_one, h1]⟩
  obtain ⟨s, hs⟩ := held_outer_conj θ₀ (hord A (Subtype.ext haa) hout) hout
    (hord (A * Z) (Subtype.ext ht2) hout') hout'
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective s
  set Mm : ↥(normalizer (M : Set X)) := ⟨m, Subgroup.le_normalizer m.2⟩ with hMm
  have hσm : σ Mm = MulAut.conj ((m : ↥M) : ↥M ⧸ pPrimeCore 2 ↥M) := oddQuotConj_of_mem m.2
  have hσW : σ (Mm * A * Mm⁻¹ * (A * Z)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσm, ← hs, mul_inv_cancel]
  set w : X := (m : X) * a * (m : X)⁻¹ * (a * z)⁻¹ with hw
  have hWc : ((Mm * A * Mm⁻¹ * (A * Z)⁻¹ : ↥(normalizer (M : Set X))) : X) = w := rfl
  have hwM : w ∈ M := by
    have h1 : a * ((m : X)⁻¹ * z⁻¹) * a⁻¹ ∈ M :=
      (mem_normalizer_iff.mp haN _).mp (mul_mem (inv_mem m.2) (inv_mem hzM))
    rw [show w = m * (a * ((m : X)⁻¹ * z⁻¹) * a⁻¹) by rw [hw]; group]
    exact mul_mem m.2 h1
  have hσW' : oddQuotConj M ⟨w, Subgroup.le_normalizer hwM⟩ = 1 := by
    have h1 : (⟨w, Subgroup.le_normalizer hwM⟩ : ↥(normalizer (M : Set X))) =
        Mm * A * Mm⁻¹ * (A * Z)⁻¹ := Subtype.ext hWc.symm
    rw [h1]
    exact hσW
  have hwO := mem_oddIn_of_oddQuotConj_eq_one (center_eq_bot_of_held θ₀) hwM hσW'
  have hwodd : Odd (orderOf w) := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hwO
    rw [card_map_of_injective M.subtype_injective] at h1
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h1
  exact exists_conj_of_odd_mul (g := (m : X)) haa ht2 (by rw [hw]; group) hwodd

end CFSG.ComponentClassification.GSThmB.CorC

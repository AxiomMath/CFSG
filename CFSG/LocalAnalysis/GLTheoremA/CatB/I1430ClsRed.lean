module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1430Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ClsRed
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge sporOrd SporadicOrdersTable)
open CFSG.LocalAnalysis.GLTheoremA.H1420.ClsRed (isPGroup_zpowers_three card_alt_ne)
open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA.AltDown

@[expose] def I1430SporS : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (s : TauCeti.SporadicName),
    Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    ∀ β : MulAut S, β ^ 3 = 1 → β ≠ 1 → ∀ J : Subgroup S,
      GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
      catalogIs (PSimple 3 J) isA6 → Nat.card (Subgroup.center (PQuot 3 J)) = 1 →
      s = .J3 ∨ s = .ONan ∨ s = .Suz

@[expose] def I1430ONCover : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ : Subgroup Q) (y : Q), I1430Model K I₀ y →
    catalogIs (↥K ⧸ Subgroup.center ↥K) (sporIs .ONan) → Nat.card (Subgroup.center ↥K) = 1

@[expose] def I1430ClsLie : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (K I₀ : Subgroup Q) (y : Q), I1430Model K I₀ y →
    ∀ d : TauCeti.ValidLieTypeIndex,
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group) →
      catalogIs (↥K ⧸ Subgroup.center ↥K) I1430Out ∧
      (catalogIs (↥K ⧸ Subgroup.center ↥K) (sporIs .ONan) → Nat.card (Subgroup.center ↥K) = 1) ∧
      (catalogIs (↥K ⧸ Subgroup.center ↥K) isSp48 →
        ¬ ∃ g ∈ K, ∀ k ∈ K, y⁻¹ * k * y = g * k * g⁻¹)

theorem kdAltDown_mod (n p : ℕ) (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (alternatingGroup (Fin n))) (hα : α ^ p = 1) (hα1 : α ≠ 1)
    (I : Subgroup (alternatingGroup (Fin n))) (hI : GLAPComponent p (fixSubgroup α) I) :
    ∃ m : ℕ, max 5 p ≤ m ∧ m + p ≤ n ∧ p ∣ n - m ∧
      Nonempty (PSimple p I ≃* alternatingGroup (Fin m)) := by
  obtain ⟨x, hx1, hxp, rfl⟩ := exists_conj_of_alt hn hp hp2 hα hα1
  have hσp : (x : Perm (Fin n)) ^ p = 1 := by simpa using congrArg Subtype.val hxp
  have hσ1 : (x : Perm (Fin n)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hIF := le_range_ofSubtype_of_glaPComponent hp hp2 hxp hI
  obtain ⟨m, hm⟩ : ∃ m, ((x : Perm (Fin n)).support)ᶜ.card = m := ⟨_, rfl⟩
  have hcompl : m = n - ((x : Perm (Fin n)).support).card := by
    have h := Finset.card_compl ((x : Perm (Fin n)).support)
    rw [Fintype.card_fin, hm] at h
    exact h
  have hmn : m + p ≤ n := by
    have h1 := le_card_support_of_pow_eq_one hp hσp hσ1
    have h2 : ((x : Perm (Fin n)).support).card ≤ n := by
      simpa using Finset.card_le_univ ((x : Perm (Fin n)).support)
    omega
  have hdvd : p ∣ n - m := by
    haveI : Fact p.Prime := ⟨hp⟩
    have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one hσp
    have hsum := Equiv.Perm.sum_cycleType (x : Perm (Fin n))
    rw [hct, Multiset.sum_replicate, smul_eq_mul] at hsum
    have h2 : ((x : Perm (Fin n)).support).card ≤ n := by
      simpa using Finset.card_le_univ ((x : Perm (Fin n)).support)
    have : n - m = ((x : Perm (Fin n)).support).card := by omega
    rw [this, ← hsum]
    exact Dvd.intro_left _ rfl
  obtain ⟨e⟩ := nonempty_range_ofSubtype_equiv ((x : Perm (Fin n)).support)ᶜ m hm
  have hIdvd : Nat.card I ∣ m.factorial := by
    have h1 := Subgroup.card_dvd_of_le hIF
    rw [Nat.card_congr e.toEquiv] at h1
    exact h1.trans (by simpa using natCard_alternatingGroup_dvd_factorial (Fin m))
  haveI : Nontrivial ↥I := nontrivial_of_glaPComponent hp hI
  have hm5 : 5 ≤ m := by
    by_contra hlt
    haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hI)
    exact false_of_isPerfect_of_card_dvd_twentyFour
      (hIdvd.trans (factorial_dvd_twentyFour (not_le.1 hlt)))
  have hmp : p ≤ m := by
    by_contra hlt
    refine not_coprime_card_of_glaPComponent hp hI ?_
    have hpm : ¬ p ∣ m.factorial := fun h => hlt ((Nat.Prime.dvd_factorial hp).1 h)
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).coprime_dvd_right hIdvd
  have hm5' : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm5
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hm5'
  haveI : IsSimpleGroup ↥(alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range :=
    e.isSimpleGroup
  have hFC : (alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range ≤
      fixSubgroup (MulAut.conj x) := fun k hk =>
    mem_fixSubgroup_conj.2 (Subtype.ext (commute_of_mem_range_ofSubtype_compl hk).eq)
  have hIeq := eq_of_isSubnormal_of_isSimpleGroup (glaPComponent_of_le hp hI hIF hFC).2.1
    ((Subgroup.nontrivial_iff_ne_bot I).1 inferInstance)
  exact ⟨m, max_le hm5 hmp, hmn, hdvd, nonempty_pSimple_equiv hp hI
    (alternatingGroup.center_eq_bot (by omega)) ((MulEquiv.subgroupCongr hIeq).trans e)⟩

variable {Q : Type} [Group Q] [Finite Q]

theorem core_eq_bot {K I₀ : Subgroup Q} {y : Q} (hM : I1430Model K I₀ y) :
    GLAPPrimeCore 3 ↥K = ⊥ := by
  obtain ⟨-, hq, hZ, -, -, -, hI, -, -⟩ := hM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  have hne : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
    intro htop
    apply not_coprime_card_of_glaPComponent Nat.prime_three hI
    have hIK : I₀ ≤ K := hI.1.trans inf_le_left
    have h1 : Nat.card I₀ ∣ Nat.card K := Subgroup.card_dvd_of_le hIK
    have h2 : Nat.card (GLAPPrimeCore 3 ↥K) = Nat.card K := by
      rw [htop, Subgroup.card_top]
    rw [h2] at hcop
    exact hcop.coprime_dvd_right h1
  have hle := le_center_of_normal_of_isQuasisimple hq (GLAPPrimeCore.normal 3 ↥K) hne
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨n, hn⟩ := hZ z (hle hz)
  have h1 : orderOf z ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h2 : Nat.Coprime 3 (orderOf z) := by
    have : orderOf (⟨z, hz⟩ : GLAPPrimeCore 3 ↥K) ∣ Nat.card (GLAPPrimeCore 3 ↥K) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at this
    exact hcop.coprime_dvd_right this
  have h3 : orderOf z = 1 := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
    rw [hk] at h2 ⊢
    rcases k with _ | k
    · rfl
    · exact absurd h2 (by rw [Nat.coprime_pow_right_iff (by omega)]; norm_num)
  exact orderOf_eq_one_iff.1 h3

@[expose] noncomputable def pQuotEquiv {K I₀ : Subgroup Q} {y : Q} (hM : I1430Model K I₀ y) :
    PQuot 3 K ≃* ↥K :=
  (QuotientGroup.quotientMulEquivOfEq (core_eq_bot hM)).trans QuotientGroup.quotientBot

@[expose] noncomputable def pSimpleEquiv {K I₀ : Subgroup Q} {y : Q} (hM : I1430Model K I₀ y) :
    PSimple 3 K ≃* (↥K ⧸ Subgroup.center ↥K) :=
  QuotientGroup.congr _ _ (pQuotEquiv hM) (Subgroup.map_center_eq (pQuotEquiv hM))

theorem isQuasisimple_pQuot {K I₀ : Subgroup Q} {y : Q} (hM : I1430Model K I₀ y) :
    CFSG.Open.IsQuasisimple (PQuot 3 K) :=
  CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (pQuotEquiv hM).symm hM.2.1

theorem not_centMod {K I₀ : Subgroup Q} {y : Q} (hM : I1430Model K I₀ y) : ¬ CentMod 3 K y := by
  intro hCM
  apply hM.2.2.2.2.2.1
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := ((centMod_iff.1 hCM).2 k hk)
  have hb : GLAPPrimeCoreOf 3 K = ⊥ := by
    unfold GLAPPrimeCoreOf
    rw [core_eq_bot hM, Subgroup.map_bot]
  rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  first
    | exact h
    | exact h.symm

theorem chevAut_ne_one {K I₀ : Subgroup Q} {y : Q} (hM : I1430Model K I₀ y) :
    chevAut 3 K ⟨y, hM.2.2.2.1⟩ ≠ 1 := fun h =>
  not_centMod hM ((H1420.ClsRed.chevAut_eq_one_iff' (isQuasisimple_pQuot hM) hM.2.2.2.1).1 h)

theorem center_card_chevTransfer {K I₀ : Subgroup Q} {y : Q} (hM : I1430Model K I₀ y)
    (hZ : Nat.card (Subgroup.center (PQuot 3 I₀)) = 1) :
    Nat.card (Subgroup.center (PQuot 3 (chevTransfer 3 K I₀))) = 1 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  obtain ⟨-, -, -, hyN, hy3, -, hI, -, -⟩ := hM
  have hyp := isPGroup_zpowers_three hy3
  have hJ := glaPComponent_chevTransfer hp hyN hyp hI
  obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hI
  have hIK : I₀ ≤ K := hI.1.trans inf_le_left
  obtain ⟨g₀⟩ := nonempty_pQuot_equiv_subgroupOf 3 hIK
  set A := I₀.subgroupOf K
  set f := (chevQuotHom 3 K).subgroupMap A
  have hf : Function.Surjective f := (chevQuotHom 3 K).subgroupMap_surjective A
  have hsurj := pQuotMapOfSurjective_surjective hp f hf
  have hdvd : Nat.card (PQuot 3 (chevTransfer 3 K I₀)) ∣ Nat.card (PQuot 3 I₀) := by
    have h1 : Nat.card (↥(A.map (chevQuotHom 3 K)) ⧸ GLAPPrimeCore 3 ↥(A.map (chevQuotHom 3 K))) ∣
        Nat.card (↥A ⧸ GLAPPrimeCore 3 ↥A) :=
      Subgroup.card_dvd_of_surjective hsurj
    have h2 : Nat.card (PQuot 3 I₀) = Nat.card (↥A ⧸ GLAPPrimeCore 3 ↥A) := by
      first
        | exact (Nat.card_congr g₀.toEquiv)
        | exact (Nat.card_congr g₀.toEquiv).symm
    rw [h2]
    exact h1
  have hcI := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot 3 I₀))
  rw [hZ, mul_one] at hcI
  have hcJ := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (PQuot 3 (chevTransfer 3 K I₀)))
  have hS : Nat.card (PSimple 3 I₀) = Nat.card (PSimple 3 (chevTransfer 3 K I₀)) :=
    Nat.card_congr g.toEquiv
  have hpos : 0 < Nat.card (PSimple 3 (chevTransfer 3 K I₀)) := Nat.card_pos
  have hI0 : 0 < Nat.card (PQuot 3 I₀) := Nat.card_pos
  have hle := Nat.le_of_dvd hI0 hdvd
  have e1 : Nat.card (PQuot 3 I₀) = Nat.card (PSimple 3 I₀) := hcI
  have e2 : Nat.card (PQuot 3 (chevTransfer 3 K I₀)) =
      Nat.card (PSimple 3 (chevTransfer 3 K I₀)) *
        Nat.card (Subgroup.center (PQuot 3 (chevTransfer 3 K I₀))) := hcJ
  rw [e2, e1, hS] at hle
  have h3 : Nat.card (Subgroup.center (PQuot 3 (chevTransfer 3 K I₀))) ≤ 1 :=
    Nat.le_of_mul_le_mul_left (by rw [mul_one]; exact hle) hpos
  have h4 : 0 < Nat.card (Subgroup.center (PQuot 3 (chevTransfer 3 K I₀))) := Nat.card_pos
  omega

theorem card_a6 (hB : LieOrderBridge) {T : Type} [Group T] [Finite T] (h : catalogIs T isA6) :
    Nat.card T = 360 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  rcases hi with hi | hi
  · cases i with
    | alternating n hn =>
      have h6 : n = 6 := hi
      subst h6
      rw [Nat.card_congr f.toEquiv]
      show Nat.card (alternatingGroup (Fin 6)) = 360
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    | _ => exact False.elim hi
  · cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A n q =>
        rcases n with _ | _ | n
        · exact False.elim hi
        · have hq : q.card = 9 := hi
          rw [hB ⟨_, hv⟩ T ⟨f⟩]
          show orderA 1 q.card = 360
          rw [hq]
          decide
        · exact False.elim hi
      | _ => exact False.elim hi
    | _ => exact False.elim hi

theorem card_sp48 (hB : LieOrderBridge) {T : Type} [Group T] [Finite T] (h : catalogIs T isSp48) :
    Nat.card T = 1056706560 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | B n q =>
      rcases n with _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 8 := hi
        rw [hB ⟨_, hv⟩ T ⟨f⟩]
        show orderBC 2 q.card = 1056706560
        rw [hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

theorem card_on (hOrd : SporadicOrdersTable) {T : Type} [Group T] (h : catalogIs T (sporIs .ONan)) :
    Nat.card T = 460815505920 := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  have hi' : i = .sporadic .ONan := hi
  subst hi'
  rw [Nat.card_congr f.toEquiv, hOrd]
  decide

theorem i1430Cls_of_parts (hB : LieOrderBridge) (hOrd : SporadicOrdersTable) (hSpor : I1430SporS)
    (hON : I1430ONCover) (hLie : I1430ClsLie) : I1430Cls := by
  intro Q _ _ K I₀ y hM
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hcatK := hM.2.2.2.2.2.2.2.2
  obtain ⟨i, ⟨e⟩⟩ := hcatK
  have hcard : ∀ {P : TauCeti.CFSGIndex → Prop}, catalogIs (↥K ⧸ Subgroup.center ↥K) P →
      Nat.card (↥K ⧸ Subgroup.center ↥K) = Nat.card i.Group := fun _ => Nat.card_congr e.toEquiv
  cases i with
  | lie d => exact hLie Q K I₀ y hM d ⟨e⟩
  | cyclic r hr =>
    exfalso
    obtain ⟨a', b', hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hM.2.1
    apply hab
    apply e.injective
    simp only [map_mul]
    exact mul_comm _ _
  | alternating n hn =>
    have hcAn : Nat.card (↥K ⧸ Subgroup.center ↥K) = n.factorial / 2 := by
      rw [Nat.card_congr e.toEquiv]
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      show Nat.card (alternatingGroup (Fin n)) = _
      rw [nat_card_alternatingGroup, Nat.card_fin]
    have hcAn' : ∀ N k : ℕ, k.factorial < 2 * N → 2 * N < (k + 1).factorial →
        Nat.card (↥K ⧸ Subgroup.center ↥K) ≠ N := by
      intro N k h1 h2 h
      rw [Nat.card_congr e.toEquiv] at h
      exact card_alt_ne k hn h1 h2 h
    refine ⟨?_, fun h => absurd (card_on hOrd h) (hcAn' _ 14 (by decide) (by decide)),
      fun h => absurd (card_sp48 hB h) (hcAn' _ 12 (by decide) (by decide))⟩
    obtain ⟨-, -, -, hyN, hy3, -, hI, hIt, -⟩ := id hM
    have hyp := isPGroup_zpowers_three hy3
    have hα1 := chevAut_ne_one hM
    have e' : PSimple 3 K ≃* alternatingGroup (Fin n) := (pSimpleEquiv hM).trans e
    have hI' := glaPComponent_chevTransfer hp hyN hyp hI
    have hα : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
    obtain ⟨hβI, ⟨e₁⟩⟩ := chevQ_transport hp e' hI'
    have hβ : MulAut.congr e' (chevAut 3 K ⟨y, hyN⟩) ^ 3 = 1 := by
      rw [← map_pow, hα, map_one]
    have hβ1 : MulAut.congr e' (chevAut 3 K ⟨y, hyN⟩) ≠ 1 := fun h =>
      hα1 ((MulAut.congr e').injective (h.trans (map_one _).symm))
    obtain ⟨m, hm, hmn, h3, ⟨f⟩⟩ := kdAltDown_mod n 3 hn hp (by norm_num) _ hβ hβ1 _ hβI
    obtain ⟨g₁⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hI
    have hm6 : m = 6 := by
      have h1 := card_a6 hB hIt.1
      rw [Nat.card_congr (g₁.trans (e₁.trans f)).toEquiv] at h1
      haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [nat_card_alternatingGroup, Nat.card_fin] at h1
      rcases (show m = 5 ∨ m = 6 ∨ 7 ≤ m by omega) with rfl | rfl | h7
      · norm_num [Nat.factorial] at h1
      · rfl
      · exfalso
        have h2 := Nat.div_le_div_right (c := 2) (Nat.factorial_le h7)
        rw [h1] at h2
        norm_num [Nat.factorial] at h2
    subst hm6
    rcases (show n = 9 ∨ 12 ≤ n by omega) with rfl | h12
    · refine ⟨_, ?_, ⟨e⟩⟩
      exact Or.inl (Or.inl rfl)
    · refine ⟨_, ?_, ⟨e⟩⟩
      exact Or.inr (Or.inl ⟨n, h12, rfl⟩)
  | sporadic s =>
    have hcS : Nat.card (↥K ⧸ Subgroup.center ↥K) = sporOrd s := by
      rw [Nat.card_congr e.toEquiv, hOrd]
    obtain ⟨-, -, -, hyN, hy3, -, hI, hIt, -⟩ := id hM
    have hyp := isPGroup_zpowers_three hy3
    have hα1 := chevAut_ne_one hM
    obtain ⟨g⟩ := nonempty_pSimple_equiv_chevTransfer hp hyN hyp hI
    have hJ := glaPComponent_chevTransfer hp hyN hyp hI
    have hJT : catalogIs (PSimple 3 (chevTransfer 3 K I₀)) isA6 := by
      obtain ⟨i, hi, ⟨f⟩⟩ := hIt.1
      exact ⟨i, hi, ⟨g.symm.trans f⟩⟩
    have hJZ := center_card_chevTransfer hM hIt.2
    have hs := hSpor (PSimple 3 K) s ⟨(pSimpleEquiv hM).trans e⟩ (chevAut 3 K ⟨y, hyN⟩)
      (chevAut_pow_eq_one 3 K hyN hy3) hα1 (chevTransfer 3 K I₀) hJ hJT hJZ
    refine ⟨?_, fun h => hON Q K I₀ y hM h, fun h => ?_⟩
    · rcases hs with rfl | rfl | rfl
      · refine ⟨_, ?_, ⟨e⟩⟩
        exact Or.inl (Or.inr (Or.inl rfl))
      · refine ⟨_, ?_, ⟨e⟩⟩
        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · refine ⟨_, ?_, ⟨e⟩⟩
        exact Or.inr (Or.inr (Or.inl rfl))
    · exfalso
      have h1 := card_sp48 hB h
      rw [hcS] at h1
      rcases hs with rfl | rfl | rfl <;> revert h1 <;> decide

end CFSG.LocalAnalysis.GLTheoremA.S8.L84.ClsRed

end

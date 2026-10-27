module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcMove

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
open CFSG.Timmesfeld.ExceptionalOrders (zpowMatrix zpowMatrix_apply zpowMatrix_zpowMatrix zpowMatrix_one)
open scoped commutatorElement Matrix

variable {τ : Tag}

@[expose] def WeakFrame (τ : Tag) (F : Type) [Field F] [Finite F] (w : WeylGroup τ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (D : LangDatum τ L),
    (∀ c, Fr c = c ^ Nat.card F) ∧ ((Nat.card F : ℕ) : L) = 0 ∧ D.Φ = Units.map (entrywiseHom Fr) ∧
    D.n = canonicalRep (coxeterSystem τ) L w ∧ Nonempty (adjointGroup τ F ≃* D.Γ)

theorem weakFrame_exact (hτ : τ = .G2 ∨ τ = .F4) (F : Type) [Field F] [Finite F]
    (w : WeylGroup τ) (hperf : commutator ↥(adjointGroup τ F) = ⊤) : WeakFrame τ F w := by
  haveI : Finite (ModGL τ F) := finite_modGL
  obtain ⟨L, _, _, _, D, Fr, hFr, hD, hDq, hDn, hK0, hd⟩ :=
    exists_exact_frame (K := F) hτ (p := 5) w hperf
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hι : Function.Injective ((baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  exact ⟨L, inferInstance, inferInstance, Fr, D, hFr, hK0, hD, hDn, ⟨hd.mulEquiv hι⟩⟩

theorem weakFrame_untw {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) (F : Type) [Field F]
    [Finite F] (w : WeylGroup τ) (hperf : commutator ↥(adjointGroup τ F) = ⊤) :
    WeakFrame τ F w := by
  haveI : Finite (ModGL τ F) := finite_modGL
  obtain ⟨L, _, _, _, D, Fr, hFr, hD, hDq, hDn, hK0, hd⟩ :=
    exists_untw_frame d hτ F (p := 5) (by norm_num) (by norm_num) w hperf
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  have hι : Function.Injective ((baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  exact ⟨L, inferInstance, inferInstance, Fr, D, hFr, hK0, hD, hDn, ⟨hd.mulEquiv hι⟩⟩

section Engine

variable {F : Type} [Field F] [Finite F] {L : Type} [Field L] [IsAlgClosed L]

theorem rootDiagUnit_mul_inv (a b : Fin τ.rank → Lˣ) :
    rootDiagUnit τ (fun i => a i * (b i)⁻¹) = rootDiagUnit τ a * (rootDiagUnit τ b)⁻¹ := by
  have : (fun i => a i * (b i)⁻¹) = a * b⁻¹ := rfl
  rw [this]
  change rootDiagUnitHom τ L (a * b⁻¹) = rootDiagUnitHom τ L a * (rootDiagUnitHom τ L b)⁻¹
  rw [map_mul, map_inv]

theorem wcOn_noncomm_of_frame (D : LangDatum τ L) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ Nat.card F) (hΦ : D.Φ = Units.map (entrywiseHom Fr))
    {w : WeylGroup τ} (hn : D.n = canonicalRep (coxeterSystem τ) L w)
    (e : adjointGroup τ F ≃* D.Γ) {p : ℕ} [Fact p.Prime]
    {X Y s : WeylGroup τ} (hX : X ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hY : Y ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)))
    (hs : s ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ))) (hv : ⁅X, Y⁆ ^ p = 1)
    {β : Fin τ.rank → Lˣ} (hβT : rootDiagUnit τ β ∈ D.torus)
    (hβp : rootDiagUnit τ β ^ p = 1)
    (hnc : weylTuple ⁅X, Y⁆ (fun i => weylTuple s β i * (β i)⁻¹) ≠
      fun i => weylTuple s β i * (β i)⁻¹) : WCOn p (adjointGroup τ F) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite (ModGL τ F) := finite_modGL
  haveI hfin : Finite D.Γ := Finite.of_equiv _ e.toEquiv
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨yX, hyX⟩ := exists_nfix_lift D hq hFr hn hX
  obtain ⟨yY, hyY⟩ := exists_nfix_lift D hq hFr hn hY
  obtain ⟨ys, hys⟩ := exists_nfix_lift D hq hFr hn hs
  have hM : ∀ y : NFix D.n Fr, (y : ModGL τ L) ∈ D.model := fun y => NFix_le_model D hΦ y.2
  have hTD : D.torus = twistedTorusOf D.n (Units.map (entrywiseHom Fr)) :=
    torus_eq_twistedTorus D hΦ
  set c : NFix D.n Fr := ⁅yX, yY⁆ with hc
  have hcΓ : (c : ModGL τ L) ∈ D.Γ := commutator_mem_Γ D (hM yX) (hM yY)
  set c' : D.Γ := ⟨(c : ModGL τ L), hcΓ⟩ with hc'
  obtain ⟨a, m, hm, hcm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c').ne' p hp.ne_one
  obtain ⟨m', hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm hp.one_lt
  set y' : D.Γ := c' ^ (m * m') with hy'
  have hy'p : y' ^ p ^ a = 1 := by
    rw [hy', ← pow_mul, show m * m' * p ^ a = (p ^ a * m) * m' by ring, pow_mul, ← hcm,
      pow_orderOf_eq_one, one_pow]
  have hycoe : (y' : ModGL τ L) = (c : ModGL τ L) ^ (m * m') := by
    rw [hy']
    rfl
  have hyN : (y' : ModGL τ L) ∈ NFix D.n Fr := by
    rw [hycoe]
    exact Subgroup.pow_mem _ c.2 _
  have hyN' : (y' : ModGL τ L)⁻¹ ∈ NFix D.n Fr := (NFix D.n Fr).inv_mem hyN
  have hweyl : NFixToWeyl D.n Fr ⟨(y' : ModGL τ L), hyN⟩ = ⁅X, Y⁆ := by
    have h1 : (⟨(y' : ModGL τ L), hyN⟩ : NFix D.n Fr) = c ^ (m * m') := Subtype.ext hycoe
    rw [h1, map_pow, hc, map_commutatorElement, hyX, hyY]
    have h2 : m * m' = p * (m * m' / p) + 1 := by
      have := Nat.div_add_mod (m * m') p
      omega
    rw [h2, pow_succ, pow_mul, hv, one_pow, one_mul]
  have hTc : IsMulCommutative ↥(D.torus.subgroupOf D.Γ) :=
    IsMulCommutative.of_comm fun a b => Subtype.ext (Subtype.ext
      (torusGroup_mul_comm (Subgroup.mem_subgroupOf.1 a.2).1 (Subgroup.mem_subgroupOf.1 b.2).1))
  set E : Subgroup D.Γ := torsionSubgroup (D.torus.subgroupOf D.Γ) hTc p with hE
  have hEp : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using g.2.2)⟩
  have hconj : ∀ z : D.Γ, (z : ModGL τ L) ∈ NFix D.n Fr → ∀ h ∈ E, z * h * z⁻¹ ∈ E := by
    intro z hz h hh
    obtain ⟨hhT, hhp⟩ := hh
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf] at hhT ⊢
      rw [hTD] at hhT ⊢
      exact NFix_conj_mem_twistedTorusOf hz hhT
    · rw [conj_pow, hhp]
      simp
  have hynorm : y' ∈ Subgroup.normalizer (E : Set D.Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj y' hyN h, fun hh => ?_⟩
    have := hconj y'⁻¹ hyN' _ hh
    simpa [mul_assoc] using this
  have hznorm : Subgroup.zpowers y' ≤ Subgroup.normalizer (E : Set D.Γ) :=
    Subgroup.zpowers_le.2 hynorm
  have hzp : IsPGroup p (Subgroup.zpowers y') := by
    refine IsPGroup.of_card_dvd_pow (n := a) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hy'p
  have hQ : IsPGroup p (Subgroup.zpowers y' ⊔ E : Subgroup D.Γ) :=
    hzp.to_sup_of_normal_right' hEp hznorm
  set t : ModGL τ L := rootDiagUnit τ β with ht
  have htM : t ∈ D.model := D.torus_le_model hβT
  have hxΓ : ⁅(ys : ModGL τ L), t⁆ ∈ D.Γ := commutator_mem_Γ D (hM ys) htM
  have hconjt : (ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹ ∈ D.torus := by
    rw [hTD] at hβT ⊢
    exact NFix_conj_mem_twistedTorusOf ys.2 hβT
  have hxT : ⁅(ys : ModGL τ L), t⁆ ∈ D.torus := by
    rw [commutatorElement_def]
    have h1 : (ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹ * t⁻¹ ∈ D.torus :=
      D.torus.mul_mem hconjt (D.torus.inv_mem hβT)
    simpa [mul_assoc] using h1
  have hxp : ⁅(ys : ModGL τ L), t⁆ ^ p = 1 := by
    have hcomm : (ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹ * t⁻¹ =
        t⁻¹ * ((ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹) := by
      have := torusGroup_mul_comm hconjt.1 (D.torus.inv_mem hβT).1
      exact this
    rw [commutatorElement_def, show (ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹ * t⁻¹ =
      ((ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹) * t⁻¹ by rfl]
    rw [Commute.mul_pow (show Commute ((ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹) t⁻¹ from hcomm),
      conj_pow, hβp, inv_pow, hβp]
    simp
  set x' : D.Γ := ⟨⁅(ys : ModGL τ L), t⁆, hxΓ⟩ with hx'
  have hx'E : x' ∈ E := by
    refine ⟨Subgroup.mem_subgroupOf.2 hxT, Subtype.ext ?_⟩
    simpa [hx'] using hxp
  have hnoncomm : x' * y' ≠ y' * x' := by
    intro hxy
    have hxy' : (y' : ModGL τ L) * (x' : ModGL τ L) * (y' : ModGL τ L)⁻¹ = (x' : ModGL τ L) := by
      have := congrArg Subtype.val hxy
      simp only [Subgroup.coe_mul] at this
      rw [← this]
      group
    let γ : Fin τ.rank → Lˣ := fun i => weylTuple s β i * (β i)⁻¹
    have hconjd : (ys : ModGL τ L) * t * (ys : ModGL τ L)⁻¹ = rootDiagUnit τ (weylTuple s β) := by
      have := NFix_conj_rootDiagUnit ys β
      rw [hys] at this
      exact this
    have hxγ : (x' : ModGL τ L) = rootDiagUnit τ γ := by
      rw [hx', show ((⟨⁅(ys : ModGL τ L), t⁆, hxΓ⟩ : D.Γ) : ModGL τ L) = ⁅(ys : ModGL τ L), t⁆ from rfl,
        commutatorElement_def, show γ = fun i => weylTuple s β i * (β i)⁻¹ from rfl,
        rootDiagUnit_mul_inv, hconjd]
    rw [hxγ, show (y' : ModGL τ L) = ((⟨(y' : ModGL τ L), hyN⟩ : NFix D.n Fr) : ModGL τ L) from rfl,
      NFix_conj_rootDiagUnit, hweyl] at hxy'
    exact hnc (rootDiagUnit_injective hxy')
  have hWC : WCOn p D.Γ :=
    WCOn.of_noncomm_pSubgroup hQ (Subgroup.mem_sup_right hx'E)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y')) hnoncomm
  exact WCOn.of_mulEquiv e hWC

end Engine

section Numeric

variable {F : Type} [Field F] [Finite F] {L : Type} [Field L] [IsAlgClosed L]

theorem exists_unit_orderOf_prime_of_not_dvd {p q : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q)
    (hq0 : ((q : ℕ) : L) = 0) : ∃ ζ : Lˣ, orderOf ζ = p := by
  have hpL : ((p : ℕ) : L) ≠ 0 := by
    intro h0
    haveI : CharP L p := (CharP.charP_iff_prime_eq_zero hp).2 h0
    exact hpq ((CharP.cast_eq_zero_iff L p q).1 hq0)
  haveI : NeZero ((p : ℕ) : L) := ⟨hpL⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  set ζu : Lˣ := (hζ.isUnit hp.ne_zero).unit with hζu
  have hζu' : IsPrimitiveRoot ζu p :=
    IsPrimitiveRoot.coe_units_iff.1 (by simpa [hζu] using hζ)
  exact ⟨ζu, hζu'.eq_orderOf.symm⟩

theorem rootDiagUnit_pow_eq (β : Fin τ.rank → Lˣ) (n : ℕ) :
    rootDiagUnit τ β ^ n = rootDiagUnit τ (fun i => β i ^ n) :=
  (map_pow (rootDiagUnitHom τ L) β n).symm

theorem mem_twistedTorus_of_coord {w : WeylGroup τ} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {β : Fin τ.rank → Lˣ}
    (h : weylTuple w (fun i => β i ^ q) = β) :
    rootDiagUnit τ β ∈
      twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) := by
  rw [mem_twistedTorusOf_iff_negPhi]
  refine ⟨rootDiagUnit_mem_torusGroup β, ?_⟩
  rw [negPhi_rootDiagUnit_gen_pow Fr w hFr β, h]

theorem noncomm_coord {p : ℕ} {ζ : Lˣ} (hζ : orderOf ζ = p) (vec : Fin τ.rank → ℤ)
    (j : Fin τ.rank) (s v : WeylGroup τ)
    (hj : ¬ (p : ℤ) ∣ ∑ i, vec i * ((weylMat s⁻¹ - 1) * (weylMat v⁻¹ - 1)) i j) :
    weylTuple v (fun i => weylTuple s (fun i => ζ ^ vec i) i * (ζ ^ vec i)⁻¹) ≠
      fun i => weylTuple s (fun i => ζ ^ vec i) i * (ζ ^ vec i)⁻¹ := by
  intro hfix
  set β : Fin τ.rank → Lˣ := fun i => ζ ^ vec i with hβ
  set S : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := weylMat s⁻¹ with hS
  set V : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := weylMat v⁻¹ with hV
  have hγ : (fun i => weylTuple s β i * (β i)⁻¹) = zpowMatrix (S - 1) β := by
    rw [zpowMatrix_sub, zpowMatrix_one, weylTuple_eq_zpowMatrix]
    rfl
  rw [hγ, weylTuple_eq_zpowMatrix, zpowMatrix_zpowMatrix] at hfix
  have h1 : zpowMatrix ((S - 1) * (V - 1)) β = 1 := by
    have h2 : zpowMatrix ((S - 1) * V - (S - 1) * 1) β = 1 := by
      rw [zpowMatrix_sub, hfix, mul_one, mul_inv_cancel]
    rwa [← mul_sub] at h2
  have h3 := congrFun h1 j
  rw [zpowMatrix_apply] at h3
  simp only [hβ, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum] at h3
  have h4 : (p : ℤ) ∣ ∑ i, vec i * ((S - 1) * (V - 1)) i j := by
    rw [← hζ]
    exact orderOf_dvd_iff_zpow_eq_one.2 h3
  exact hj h4

end Numeric

section Split

variable {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem mem_centralizer_one' {G : Type*} [Group G] (a : G) :
    a ∈ Subgroup.centralizer ({1} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    simp

theorem mem_centralizer_of_neg {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (a : WeylGroup τ) : a ∈ Subgroup.centralizer ({w} : Set (WeylGroup τ)) :=
  Subgroup.mem_centralizer_iff.2 fun g hg => by
    rw [Set.mem_singleton_iff.1 hg]
    exact weylGroup_mul_comm_of_neg hw a

theorem WeakFrame.wcOn_noncomm_one (hF : WeakFrame τ F 1) (hpq : ¬ p ∣ Nat.card F)
    (hd : p ∣ Nat.card F - 1) {X Y s : WeylGroup τ} (hv : ⁅X, Y⁆ ^ p = 1)
    (vec : Fin τ.rank → ℤ) (j : Fin τ.rank)
    (hj : ¬ (p : ℤ) ∣ ∑ i, vec i * ((weylMat s⁻¹ - 1) * (weylMat ⁅X, Y⁆⁻¹ - 1)) i j) :
    WCOn p (adjointGroup τ F) := by
  obtain ⟨L, _, _, Fr, D, hFr, hK0, hΦ, hn, ⟨e⟩⟩ := hF
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_prime_of_not_dvd (L := L) Fact.out hpq hK0
  have hζq : ζ ^ (Nat.card F - 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hd)
  have hq2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have hζq' : ζ ^ Nat.card F = ζ := by
    calc ζ ^ Nat.card F = ζ ^ ((Nat.card F - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ Nat.card F)]
      _ = ζ := by rw [pow_succ, hζq, one_mul]
  have hβq : weylTuple (1 : WeylGroup τ) (fun i => (ζ ^ vec i) ^ Nat.card F) =
      fun i => ζ ^ vec i := by
    rw [weylTuple_one]
    funext i
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζq']
  have hβT : rootDiagUnit τ (fun i => ζ ^ vec i) ∈ D.torus := by
    rw [torus_eq_twistedTorus D hΦ, hn]
    exact mem_twistedTorus_of_coord hFr hβq
  have hβp : rootDiagUnit τ (fun i => ζ ^ vec i) ^ p = 1 := by
    rw [rootDiagUnit_pow_eq]
    have : (fun i => (ζ ^ vec i) ^ p) = fun _ => (1 : Lˣ) := by
      funext i
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζ, pow_orderOf_eq_one,
        one_zpow]
    rw [this]
    exact rootDiagUnit_one
  exact wcOn_noncomm_of_frame D hFr hΦ hn e (mem_centralizer_one' _) (mem_centralizer_one' _)
    (mem_centralizer_one' _) hv hβT hβp (noncomm_coord hζ vec j s ⁅X, Y⁆ hj)

theorem WeakFrame.wcOn_noncomm_neg {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (hF : WeakFrame τ F w) (hpq : ¬ p ∣ Nat.card F) (hd : p ∣ Nat.card F + 1)
    {X Y s : WeylGroup τ} (hv : ⁅X, Y⁆ ^ p = 1) (vec : Fin τ.rank → ℤ) (j : Fin τ.rank)
    (hj : ¬ (p : ℤ) ∣ ∑ i, vec i * ((weylMat s⁻¹ - 1) * (weylMat ⁅X, Y⁆⁻¹ - 1)) i j) :
    WCOn p (adjointGroup τ F) := by
  obtain ⟨L, _, _, Fr, D, hFr, hK0, hΦ, hn, ⟨e⟩⟩ := hF
  obtain ⟨ζ, hζ⟩ := exists_unit_orderOf_prime_of_not_dvd (L := L) Fact.out hpq hK0
  have hζq : ζ ^ (Nat.card F + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hd)
  have hβq : weylTuple w (fun i => (ζ ^ vec i) ^ Nat.card F) = fun i => ζ ^ vec i := by
    rw [weylTuple_eq_inv hw]
    funext i
    refine inv_eq_of_mul_eq_one_right ?_
    calc (ζ ^ vec i) ^ Nat.card F * ζ ^ vec i = ζ ^ (vec i * ((Nat.card F + 1 : ℕ) : ℤ)) := by
          rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
          congr 1
          push_cast
          ring
      _ = (ζ ^ (Nat.card F + 1)) ^ vec i := by rw [mul_comm, zpow_mul, zpow_natCast]
      _ = 1 := by rw [hζq, one_zpow]
  have hβT : rootDiagUnit τ (fun i => ζ ^ vec i) ∈ D.torus := by
    rw [torus_eq_twistedTorus D hΦ, hn]
    exact mem_twistedTorus_of_coord hFr hβq
  have hβp : rootDiagUnit τ (fun i => ζ ^ vec i) ^ p = 1 := by
    rw [rootDiagUnit_pow_eq]
    have : (fun i => (ζ ^ vec i) ^ p) = fun _ => (1 : Lˣ) := by
      funext i
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζ, pow_orderOf_eq_one,
        one_zpow]
    rw [this]
    exact rootDiagUnit_one
  exact wcOn_noncomm_of_frame D hFr hΦ hn e (mem_centralizer_of_neg hw _)
    (mem_centralizer_of_neg hw _) (mem_centralizer_of_neg hw _) hv hβT hβp
    (noncomm_coord hζ vec j s ⁅X, Y⁆ hj)

end Split


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

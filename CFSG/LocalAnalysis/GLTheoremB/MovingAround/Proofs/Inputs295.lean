module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsMisc8
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2FamSpor
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSimple
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR1Basic
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import Certificates.Certificate8137
public import Certificates.Certificate8138
public import Certificates.Certificate8140
public import Certificates.Certificate8141

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295

open CFSG.Open
open CFSG.HardMathSupport.Timmesfeld.Coordinator (SporadicOuterLeTwo)
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (SporadicBridges)
open CFSG.HardMathSupport.Solomon.Coordinator (SporadicOrdersTable sporOrd)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_le)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
  (isPSolvable_of_mulEquiv)

section Generic

variable {S : Type} [Group S] [Finite S]

@[expose] def Excl295At (x : S) : Prop :=
  (∃ P : Subgroup S, P ≤ Subgroup.centralizer ({x} : Set S) ∧ IsPGroup 3 ↥P ∧
      3 ^ 5 ≤ Nat.card P) ∨
    4 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer ({x} : Set S)) ∨
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.centralizer ({x} : Set S))

variable (S) in
@[expose] def No295 : Prop :=
  4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup S) → ∀ x : S, orderOf x = 3 → Excl295At x

theorem map_centralizer_singleton {T : Type} [Group T] (e : S ≃* T) (x : S) :
    (Subgroup.centralizer ({x} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set T) := by
  ext y
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    simpa using congrArg e hz
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa using hy

theorem Excl295At.of_equiv {T : Type} [Group T] [Finite T] (e : S ≃* T) {x : S}
    (h : Excl295At (e x)) : Excl295At x := by
  have hmap := map_centralizer_singleton e x
  have hback : (Subgroup.centralizer ({e x} : Set T)).map e.symm.toMonoidHom =
      Subgroup.centralizer ({x} : Set S) := by
    rw [← hmap, Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by ext; simp
    rw [this, Subgroup.map_id]
  rcases h with ⟨P, hP, hPp, hPc⟩ | hr | hs
  · refine Or.inl ⟨P.map e.symm.toMonoidHom, ?_, hPp.map _, ?_⟩
    · rw [← hback]
      exact Subgroup.map_mono hP
    · rwa [Subgroup.card_map_of_injective e.symm.injective]
  · refine Or.inr (Or.inl ?_)
    have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) e.symm.toMonoidHom
      e.symm.injective (Subgroup.centralizer ({e x} : Set T))
    rw [hback] at h1
    omega
  · refine Or.inr (Or.inr fun hsolv => hs ?_)
    exact isPSolvable_of_mulEquiv ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)) hsolv

theorem Excl295At.of_isConj {x y : S} (hxy : IsConj x y) (h : Excl295At y) : Excl295At x := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hxy
  refine Excl295At.of_equiv (MulAut.conj c) ?_
  rwa [MulAut.conj_apply, hc]

theorem Excl295At.of_centralizer_eq {x y : S}
    (hc : Subgroup.centralizer ({x} : Set S) = Subgroup.centralizer ({y} : Set S))
    (h : Excl295At x) : Excl295At y := by
  unfold Excl295At at h ⊢
  rwa [← hc]

theorem No295.of_equiv {T : Type} [Group T] [Finite T] (e : S ≃* T) (h : No295 T) : No295 S := by
  intro hrk x hx
  have hrk' : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup T) := by
    rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
  exact Excl295At.of_equiv e (h hrk' (e x) (by rw [MulEquiv.orderOf_eq, hx]))

theorem excl295At_of_le {x : S} {J : Subgroup S} (hJ : J ≤ Subgroup.centralizer ({x} : Set S))
    (h : 3 ^ 5 ∣ Nat.card J) : Excl295At x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 h
  refine Or.inl ⟨P.map J.subtype, (Subgroup.map_subtype_le P).trans hJ,
    (IsPGroup.of_card hP).map _, ?_⟩
  rw [Subgroup.card_map_of_injective J.subtype_injective, hP]

theorem excl295At_of_card_dvd {x : S}
    (h : 3 ^ 5 ∣ Nat.card (Subgroup.centralizer ({x} : Set S))) : Excl295At x :=
  excl295At_of_le le_rfl h

theorem excl295At_of_simple {x : S} {T : Subgroup S}
    (hT : T ≤ Subgroup.centralizer ({x} : Set S)) (hs : IsSimpleGroup ↥T)
    (hnc : ¬ IsMulCommutative ↥T) (h3 : 3 ∣ Nat.card T) : Excl295At x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact Or.inr (Or.inr fun hsolv =>
    CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.not_isPSolvable_three_of_simple hs hnc h3
      (isPSolvable_of_le hsolv hT))

theorem excl295At_of_elem {x : S} {E : Subgroup S} (hE : E ≤ Subgroup.centralizer ({x} : Set S))
    (hEa : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 4) : Excl295At x :=
  Or.inr (Or.inl (CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hE hEa hc))

theorem centralizer_pow_two_eq {x : S} (hx : x ^ 3 = 1) :
    Subgroup.centralizer ({x ^ 2} : Set S) = Subgroup.centralizer ({x} : Set S) := by
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  have hx4 : (x ^ 2) ^ 2 = x := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hx, one_mul]
  constructor
  · intro h
    have h2 : Commute g ((x ^ 2) ^ 2) := (show Commute g (x ^ 2) from h).pow_right 2
    rw [hx4] at h2
    exact h2
  · intro h
    exact (show Commute g x from h).pow_right 2

theorem Excl295At.of_conj_pow {x y : S} (hx : x ^ 3 = 1) {e : ℕ} (he : e = 1 ∨ e = 2)
    (hy : IsConj y (x ^ e)) (h : Excl295At x) : Excl295At y := by
  refine Excl295At.of_isConj hy ?_
  rcases he with rfl | rfl
  · rwa [pow_one]
  · exact Excl295At.of_centralizer_eq (centralizer_pow_two_eq hx).symm h

theorem excl295At_of_ambient {G : Type} [Group G] {P : Subgroup G} [Finite ↥P] {x : G}
    (hx : x ∈ P) {J : Subgroup G} (hJ : J ≤ Subgroup.centralizer ({x} : Set G) ⊓ P)
    (h : 3 ^ 5 ∣ Nat.card J) : Excl295At (⟨x, hx⟩ : ↥P) := by
  refine excl295At_of_le (J := J.subgroupOf P) (fun j hj => ?_) ?_
  · rw [Subgroup.mem_subgroupOf] at hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hJ hj).1)
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hJ.trans inf_le_right)).toEquiv]

theorem exists_noncomm_of_isSimpleGroup {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hc : ¬ (Nat.card T).Prime) : ∃ a b : T, a * b ≠ b * a := by
  by_contra h
  push Not at h
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := h }
  exact hc IsSimpleGroup.prime_card

theorem excl295At_of_ambient_simple {G : Type} [Group G] {P : Subgroup G} [Finite ↥P] {x : G}
    (hx : x ∈ P) {J : Subgroup G} (hJ : J ≤ Subgroup.centralizer ({x} : Set G) ⊓ P)
    (hs : IsSimpleGroup ↥J) (hnc : ∃ a b : ↥J, a * b ≠ b * a) (h3 : 3 ∣ Nat.card J) :
    Excl295At (⟨x, hx⟩ : ↥P) := by
  have e : ↥(J.subgroupOf P) ≃* ↥J := Subgroup.subgroupOfEquivOfLe (hJ.trans inf_le_right)
  refine excl295At_of_simple (T := J.subgroupOf P) (fun j hj => ?_)
    (haveI := hs; e.isSimpleGroup) ?_ ?_
  · rw [Subgroup.mem_subgroupOf] at hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hJ hj).1)
  · rintro ⟨hc⟩
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hc.comm _ _
  · rwa [Nat.card_congr e.toEquiv]

theorem pRank_le_three_of_not_dvd (h : ¬ 3 ^ 4 ∣ Nat.card S) :
    CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.SectionRank.pRank_le (p := 3) (by norm_num) fun E _ hE => ?_
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  rw [hk]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hlt
  exact h ((pow_dvd_pow 3 (by omega)).trans (hk ▸ Subgroup.card_subgroup_dvd_card E))

theorem Excl295At.map_equiv {T : Type} [Group T] [Finite T] (e : S ≃* T) {x : S}
    (h : Excl295At x) : Excl295At (e x) :=
  Excl295At.of_equiv e.symm (by rwa [MulEquiv.symm_apply_apply])

theorem Excl295At.of_subgroup {H : Subgroup S} {x : S} (hx : x ∈ H)
    (h : Excl295At (⟨x, hx⟩ : ↥H)) : Excl295At x := by
  have hle : (Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H)).map H.subtype ≤
      Subgroup.centralizer ({x} : Set S) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact congrArg Subtype.val hy
  rcases h with ⟨P, hP, hPp, hPc⟩ | hr | hs
  · refine Or.inl ⟨P.map H.subtype, (Subgroup.map_mono hP).trans hle, hPp.map _, ?_⟩
    rwa [Subgroup.card_map_of_injective H.subtype_injective]
  · refine Or.inr (Or.inl (hr.trans ((CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num)
      H.subtype H.subtype_injective _).trans (CFSG.SectionRank.pRank_mono (by norm_num) hle))))
  · refine Or.inr (Or.inr fun hsolv => hs ?_)
    exact isPSolvable_of_mulEquiv (Subgroup.equivMapOfInjective _ H.subtype
      H.subtype_injective).symm (isPSolvable_of_le hsolv hle)

theorem Excl295At.of_injective {H : Type} [Group H] [Finite H] (f : H →* S)
    (hf : Function.Injective f) {y : H} (h : Excl295At y) : Excl295At (f y) := by
  have h1 := Excl295At.map_equiv (MonoidHom.ofInjective hf) h
  have he : MonoidHom.ofInjective hf y = ⟨f y, y, rfl⟩ :=
    Subtype.ext (MonoidHom.ofInjective_apply hf)
  rw [he] at h1
  exact Excl295At.of_subgroup _ h1

theorem card_centralizer_eq_of_isConj {x y : S} (h : IsConj x y) :
    Nat.card (Subgroup.centralizer ({x} : Set S)) =
      Nat.card (Subgroup.centralizer ({y} : Set S)) := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have hm := map_centralizer_singleton (MulAut.conj c) x
  rw [MulAut.conj_apply, hc] at hm
  rw [← hm, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem excl295At_of_mem_elem {x : S} {A : Subgroup S} (hx : x ∈ A) (hA : IsElemAbelian 3 A)
    (hc : Nat.card A = 3 ^ 4) : Excl295At x := by
  refine excl295At_of_elem (fun a ha => ?_) hA hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hA.1.is_comm.comm (⟨a, ha⟩ : ↥A) ⟨x, hx⟩)

theorem excl295At_of_mem_comm {x : S} {A : Subgroup S} (hx : x ∈ A)
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (h : 3 ^ 5 ∣ Nat.card A) : Excl295At x := by
  refine excl295At_of_le (fun a ha => ?_) h
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hA a ha x hx

variable (S) in
@[expose] def AllExcl295 : Prop := ∀ x : S, orderOf x = 3 → Excl295At x

theorem No295.of_all (h : AllExcl295 S) : No295 S := fun _ => h

theorem no295_of_pRank_le (h : CFSG.Open.pRank 3 (⊤ : Subgroup S) ≤ 3) : No295 S :=
  fun h4 => by omega

theorem no295_of_not_dvd_five (h : ¬ 3 ^ 5 ∣ Nat.card S) : No295 S := by
  intro hrk x hx
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
    (⊤ : Subgroup S)
  have hd : 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup S) ∣ Nat.card S :=
    hEc ▸ Subgroup.card_subgroup_dvd_card E
  have hr : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 4 := by
    by_contra hne
    exact h ((pow_dvd_pow 3 (by omega)).trans hd)
  have hfac : (Nat.card S).factorization 3 = 4 := by
    have hS0 : Nat.card S ≠ 0 := Nat.card_pos.ne'
    have h1 := (Nat.prime_three.pow_dvd_iff_le_factorization hS0).1 (hr ▸ hd)
    have h2 : ¬ 5 ≤ (Nat.card S).factorization 3 :=
      fun h5 => h ((Nat.prime_three.pow_dvd_iff_le_factorization hS0).2 h5)
    omega
  let P₁ : Sylow 3 S := Sylow.ofCard E (by rw [hEc, hr, hfac])
  have hxp : IsPGroup 3 (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  have hxQ : x ∈ (Q : Subgroup S) := hQ (Subgroup.mem_zpowers x)
  let f : ↥(Q : Subgroup S) ≃* ↥(P₁ : Subgroup S) := Sylow.equiv Q P₁
  have hP₁ : ∀ a b : ↥(P₁ : Subgroup S), a * b = b * a := fun a b =>
    hE.1.is_comm.comm (⟨a, a.2⟩ : E) ⟨b, b.2⟩
  have hQa : IsElemAbelian 3 (Q : Subgroup S) := by
    refine ⟨⟨⟨fun a b => f.injective ?_⟩⟩, fun q hq => ?_⟩
    · rw [map_mul, map_mul, hP₁]
    · have h1 : f ⟨q, hq⟩ ^ 3 = 1 := Subtype.ext (hE.2 _ (f ⟨q, hq⟩).2)
      rw [← map_pow, map_eq_one_iff f f.injective] at h1
      exact congrArg Subtype.val h1
  have hQc : Nat.card (Q : Subgroup S) = 3 ^ 4 := by
    rw [Nat.card_congr f.toEquiv]
    change Nat.card E = 3 ^ 4
    rw [hEc, hr]
  refine excl295At_of_elem (fun q hq => ?_) hQa hQc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hQa.1.is_comm.comm (⟨q, hq⟩ : ↥(Q : Subgroup S)) ⟨x, hxQ⟩)

end Generic

section Reduction

@[expose] def No295Spor (s : TauCeti.SporadicName) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    No295 S

theorem isElemAbelian_comap {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {p : ℕ} {E : Subgroup H} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun y hy => hf (by rw [map_pow, hE.2 _ hy, map_one])⟩
  have := congrArg Subtype.val (hE.1.is_comm.comm (⟨f a, a.2⟩ : E) ⟨f b, b.2⟩)
  simpa using this

theorem input29_5'Spor_of (hout : SporadicOuterLeTwo) (h : ∀ s, No295Spor s) :
    InputsMisc8.Input29_5'Spor := by
  intro X _ _ L hLn hq _ hC s ⟨e⟩ _ hrk x hx hC4 hrk3 hsolv
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hLn
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine hC z fun l hl => ?_
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨l, hl⟩).symm
  let e₀ : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  let eL : ↥L ≃* (TauCeti.CFSGIndex.sporadic s).Group := e₀.trans e
  haveI : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hq.2
  haveI : IsSimpleGroup ↥L := e₀.isSimpleGroup
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.center ↥L = ⊤ :=
      eq_top_iff.2 fun z _ => Subgroup.mem_center_iff.2 fun g => hall g z
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥L
    apply hab
    have ha : a ∈ Subgroup.center ↥L := htop ▸ Subgroup.mem_top a
    have hb : b ∈ Subgroup.center ↥L := htop ▸ Subgroup.mem_top b
    rw [hZ, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hOut : Nat.card (Outer ↥L) ≤ 2 := hout ↥L inferInstance hnab s ⟨eL⟩
  set ψ : X →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp MulAut.conjNormal with hψ
  have hker : ∀ y : X, ψ y = 1 → y ∈ L := by
    intro y hy
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨l, hl⟩ := hy
    have hc : ∀ m ∈ L, ((l : X)⁻¹ * y) * m = m * ((l : X)⁻¹ * y) := by
      intro m hm
      have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨m, hm⟩ : ↥L) : X)) hl
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc (l : X)⁻¹ * y * m = (l : X)⁻¹ * (y * m * y⁻¹) * y := by group
        _ = (l : X)⁻¹ * ((l : X) * m * (l : X)⁻¹) * y := by rw [h1]
        _ = m * ((l : X)⁻¹ * y) := by group
    have h1 := hC _ hc
    have : y = l := by
      rw [inv_mul_eq_one] at h1
      exact h1.symm
    rw [this]
    exact l.2
  haveI : Finite (Outer ↥L) := by
    haveI : Finite (MulAut ↥L) := MulEquiv.finite_left
    infer_instance
  have h3L : ∀ y : X, y ^ 3 = 1 → y ∈ L := by
    intro y hy
    apply hker
    have h1 : orderOf (ψ y) ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hy, map_one])
    have h2 : orderOf (ψ y) ∣ Nat.card (Outer ↥L) := orderOf_dvd_natCard (ψ y)
    have hpos : 0 < Nat.card (Outer ↥L) := Nat.card_pos
    have h3 : orderOf (ψ y) ∣ Nat.gcd 3 (Nat.card (Outer ↥L)) := Nat.dvd_gcd h1 h2
    have hg : Nat.gcd 3 (Nat.card (Outer ↥L)) = 1 := by
      interval_cases (Nat.card (Outer ↥L)) <;> norm_num
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxL : x ∈ L := h3L x hx3
  set x' : ↥L := ⟨x, hxL⟩ with hx'
  have hox : orderOf x' = 3 := by
    rw [← hx, hx']
    exact (Subgroup.orderOf_coe (⟨x, hxL⟩ : ↥L)).symm
  have hrkL : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (⊤ : Subgroup X)
    have hEL : E ≤ L := fun y hy => h3L y (hE.2 y hy)
    have hcard : Nat.card (E.comap L.subtype) = Nat.card E := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, Subgroup.map_comap_eq,
        Subgroup.range_subtype, inf_of_le_right hEL]
    exact hrk.trans (CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top
      (isElemAbelian_comap L.subtype_injective hE) (hcard.trans hEc))
  have hCle : (Subgroup.centralizer ({x'} : Set ↥L)).map L.subtype ≤
      Subgroup.centralizer ({x} : Set X) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact congrArg Subtype.val hy
  rcases h s ↥L ⟨eL⟩ hrkL x' hox with ⟨P, hP, hPp, hPc⟩ | hr | hs
  · have h1 := hC4 (P.map L.subtype) ((Subgroup.map_mono hP).trans hCle) (hPp.map _)
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    omega
  · have h1 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) L.subtype
      L.subtype_injective (Subgroup.centralizer ({x'} : Set ↥L))
    have h2 := CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) hCle
    omega
  · apply hs
    exact isPSolvable_of_mulEquiv (Subgroup.equivMapOfInjective _ L.subtype
      L.subtype_injective).symm (isPSolvable_of_le hsolv hCle)

theorem no295Spor_of_carrier (hbr : SporadicBridges) (s : TauCeti.SporadicName)
    (h : ∀ [Finite (CFSG.Blueprint.NativeSporadic.Carrier s)],
      No295 (CFSG.Blueprint.NativeSporadic.Carrier s)) : No295Spor s := by
  intro S _ _ ⟨e⟩
  obtain ⟨b⟩ := hbr s
  let f : S ≃* CFSG.Blueprint.NativeSporadic.Carrier s := e.trans b.symm
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) := Finite.of_equiv S f.toEquiv
  exact No295.of_equiv f h

theorem no295Spor_of_sporOrd (hord : SporadicOrdersTable) {s : TauCeti.SporadicName}
    (h : ¬ 3 ^ 4 ∣ sporOrd s) : No295Spor s := by
  intro S _ _ ⟨e⟩
  refine no295_of_pRank_le (pRank_le_three_of_not_dvd ?_)
  rwa [Nat.card_congr e.toEquiv, hord s]

theorem no295Spor_of_sporOrd_five (hord : SporadicOrdersTable) {s : TauCeti.SporadicName}
    (h : ¬ 3 ^ 5 ∣ sporOrd s) : No295Spor s := by
  intro S _ _ ⟨e⟩
  refine no295_of_not_dvd_five ?_
  rwa [Nat.card_congr e.toEquiv, hord s]

end Reduction

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs295

module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29Defs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools
open scoped commutatorElement

namespace S3Sec29D4

section Generic

open CFSG.SignalizerFunctor.Helpers

variable {GroupType ImageType : Type} [Group GroupType] [Group ImageType]

theorem map_inf_centralizer_eq' (φ : GroupType →* ImageType) (hker : Odd (Nat.card φ.ker))
    (actor target : Subgroup GroupType) (hact : IsPGroup 2 actor)
    (hnorm : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    (target ⊓ Subgroup.centralizer (actor : Set GroupType)).map φ =
      target.map φ ⊓ Subgroup.centralizer (actor.map φ : Set ImageType) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _action := conjugationAction actor target hnorm
  apply le_antisymm
  · rintro imageElement ⟨element, member, rfl⟩
    refine ⟨⟨element, member.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro imageActor ⟨actorElement, actor_member, rfl⟩
    simpa only [map_mul] using congrArg φ
      (Subgroup.mem_centralizer_iff.mp member.2 actorElement actor_member)
  · intro imageElement member
    obtain ⟨element, element_member, image_eq⟩ := member.1
    let restricted := φ.domRestrict target
    let fibre : SubMulAction actor target :=
      ⟨{representative | restricted representative = imageElement}, by
        intro actorElement representative representative_member
        change φ (actorElement.val * representative.val * actorElement.val⁻¹) = imageElement
        rw [map_mul, map_mul, map_inv]
        change φ actorElement.val * restricted representative * (φ actorElement.val)⁻¹ =
          imageElement
        rw [representative_member]
        have commutes := Subgroup.mem_centralizer_iff.mp member.2
          (φ actorElement.val) (Subgroup.mem_map_of_mem φ actorElement.property)
        rw [commutes, mul_assoc, mul_inv_cancel, mul_one]⟩
    have fibre_card : Nat.card fibre = Nat.card restricted.ker := by
      have fibre_eq : {representative : target | restricted representative = imageElement} =
          restricted ⁻¹' {restricted (⟨element, element_member⟩ : target)} := by
        ext representative
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        change (restricted representative = imageElement) ↔ restricted representative = φ element
        rw [image_eq]
      exact (Nat.card_congr (Set.equivOfEq fibre_eq)).trans
        (Nat.card_congr (restricted.fiberEquivKer (⟨element, element_member⟩ : target)))
    have hkerdvd : Nat.card restricted.ker ∣ Nat.card φ.ker := by
      let ι : restricted.ker →* φ.ker :=
        { toFun := fun x => ⟨x.1.1, MonoidHom.mem_ker.mp x.2⟩
          map_one' := rfl
          map_mul' := fun x y => rfl }
      refine Subgroup.card_dvd_of_injective ι fun x y hxy => ?_
      have h1 := congrArg (fun z : ↥φ.ker => (z : GroupType)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have not_divides : ¬ 2 ∣ Nat.card fibre := by
      rw [fibre_card]
      exact Nat.prime_two.coprime_iff_not_dvd.mp
        ((Nat.coprime_two_left.mpr hker).of_dvd_right hkerdvd)
    obtain ⟨representative, fixed⟩ :=
      hact.nonempty_fixed_point_of_prime_not_dvd_card fibre not_divides
    refine ⟨representative.val.val, ⟨representative.val.property, ?_⟩, representative.property⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement actor_member
    have equality := congrArg (fun fixedElement : fibre => fixedElement.val.val)
      (fixed (⟨actorElement, actor_member⟩ : actor))
    change actorElement * representative.val.val * actorElement⁻¹ = representative.val.val
      at equality
    exact mul_inv_eq_iff_eq_mul.mp equality

theorem exists_isPGroup_map_eq_of_map_le' {A B : Type*} [Group A] [Group B] [Finite A] {p : ℕ}
    [Fact p.Prime] (φ : A →* B) {H : Subgroup A} {Q : Subgroup B} (hQ : IsPGroup p Q)
    (hQH : Q ≤ H.map φ) {E : Subgroup A} (hE : IsPGroup p E) (hEH : E ≤ H) (hEQ : E.map φ ≤ Q) :
    ∃ P : Subgroup A, E ≤ P ∧ P ≤ H ∧ IsPGroup p P ∧ P.map φ = Q := by
  set W := H ⊓ Q.comap φ
  let ψ : W →* Q := (φ.comp W.subtype).codRestrict Q fun w => w.2.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨a, ha, rfl⟩ := hQH hq
    exact ⟨⟨a, ha, hq⟩, rfl⟩
  have hEW : E ≤ W := le_inf hEH fun e he => hEQ ⟨e, he, rfl⟩
  obtain ⟨T, hT⟩ := (hE.comap_of_injective W.subtype W.subtype_injective).exists_le_sylow
  have htop : ((T.mapSurjective hψ : Sylow p Q) : Subgroup Q) = ⊤ :=
    ((T.mapSurjective hψ).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  refine ⟨(T : Subgroup W).map W.subtype, fun e he => ⟨⟨e, hEW he⟩,
    hT (Subgroup.mem_comap.mpr he : (⟨e, hEW he⟩ : W) ∈ E.comap W.subtype), rfl⟩,
    (Subgroup.map_subtype_le _).trans inf_le_left, T.isPGroup'.map _, le_antisymm ?_ ?_⟩
  · rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
    exact w.2.2
  · intro q hq
    obtain ⟨w, hw, hwq⟩ : (⟨q, hq⟩ : Q) ∈ (T : Subgroup W).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    exact ⟨w, ⟨w, hw, rfl⟩, congrArg Subtype.val hwq⟩

end Generic

section GLevel

open CFSG.GH74.Generic.S45

variable {G : Type} [Group G] [Finite G] {y : G}

omit [Finite G] in
theorem piC_conj {g a : G} (hg : g ∈ centralizer ({y} : Set G)) (ha : a ∈ centralizer ({y} : Set G)) :
    piC y (g * a * g⁻¹) = piC y g * piC y a * (piC y g)⁻¹ := by
  rw [piC_mul y (mul_mem hg ha) (inv_mem hg), piC_mul y hg ha, piC_inv y hg]

theorem piC_eq_one_odd {a : G} (ha : a ∈ centralizer ({y} : Set G)) (h1 : piC y a = 1) :
    Odd (orderOf a) := by
  rw [piC_of_mem y ha] at h1
  have := proj_odd y ⟨a, ha⟩ h1
  rwa [Subgroup.orderOf_mk] at this

theorem eq_of_piC_eq {P : Subgroup G} (hPC : P ≤ centralizer ({y} : Set G)) (hP : IsPGroup 2 ↥P)
    {a b : G} (ha : a ∈ P) (hb : b ∈ P) (h : piC y a = piC y b) : a = b := by
  have haC := hPC ha
  have hbC := hPC hb
  have h1 : piC y (a⁻¹ * b) = 1 := by
    rw [piC_mul y (inv_mem haC) hbC, piC_inv y haC, h, inv_mul_cancel]
  have hodd := piC_eq_one_odd (mul_mem (inv_mem haC) hbC) h1
  obtain ⟨k, hk⟩ := hP ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb⟩
  have hdvd : orderOf (a⁻¹ * b) ∣ 2 ^ k := by
    have := orderOf_dvd_of_pow_eq_one hk
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hone : orderOf (a⁻¹ * b) = 1 := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · rw [hi, h0, pow_zero]
    · exfalso
      rw [hi] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' (by omega)).mpr even_two)
  have := orderOf_eq_one_iff.1 hone
  calc a = a * (a⁻¹ * b) := by rw [this, mul_one]
    _ = b := by group

theorem mem_of_piC_mem {X : Subgroup G} (hy2 : y * y = 1)
    (h : piC y y ∈ S3.imgBar y X) : y ∈ X := by
  obtain ⟨p, hpX, hp⟩ := S3.mem_imgBar.1 h
  have hyC : y ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  set q : G := (p : G) with hq
  have hqC : q ∈ centralizer ({y} : Set G) := p.2
  have hpy : piC y q = piC y y := by rw [piC_of_mem y hqC]; exact hp
  set o : G := q⁻¹ * y with ho
  have hoC : o ∈ centralizer ({y} : Set G) := mul_mem (inv_mem hqC) hyC
  have ho1 : piC y o = 1 := by rw [piC_mul y (inv_mem hqC) hyC, piC_inv y hqC, hpy, inv_mul_cancel]
  have hodd := piC_eq_one_odd hoC ho1
  have hqy : q * y = y * q := Subgroup.mem_centralizer_singleton_iff.1 hqC
  have hcomm : Commute q o := by
    show q * (q⁻¹ * y) = (q⁻¹ * y) * q
    calc q * (q⁻¹ * y) = y := by group
      _ = q⁻¹ * (q * y) := by group
      _ = q⁻¹ * (y * q) := by rw [hqy]
      _ = (q⁻¹ * y) * q := by group
  have hyqo : y = q * o := by rw [ho]; group
  obtain ⟨m, hm⟩ := hodd
  have hpow : y ^ (2 * m + 1) = y := by
    rw [pow_succ, pow_mul, pow_two, hy2, one_pow, one_mul]
  have hopow : o ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one o
  have : y = q ^ (2 * m + 1) := by
    calc y = y ^ (2 * m + 1) := hpow.symm
      _ = (q * o) ^ (2 * m + 1) := by rw [← hyqo]
      _ = q ^ (2 * m + 1) * o ^ (2 * m + 1) := hcomm.mul_pow _
      _ = q ^ (2 * m + 1) := by rw [hopow, mul_one]
  rw [this]
  exact X.pow_mem hpX _

theorem centralizer_zpowers_eq {M : Type*} [Group M] (a : M) :
    centralizer ((zpowers a : Subgroup M) : Set M) = centralizer ({a} : Set M) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem imgBar_inf_centralizer {T : Subgroup G} {u : G}
    (huC : u ∈ centralizer ({y} : Set G)) (hu2 : u * u = 1) (huT : u ∈ normalizer (T : Set G)) :
    S3.imgBar y (T ⊓ centralizer ({u} : Set G)) =
      S3.imgBar y T ⊓ centralizer ({piC y u} : Set (CentralizerBar y)) := by
  set C := centralizer ({y} : Set G) with hC
  set uC : ↥C := ⟨u, huC⟩ with huCdef
  have hker : Odd (Nat.card (proj y).ker) := by
    have : (proj y).ker = pPrimeCore 2 ↥C := QuotientGroup.ker_mk' _
    rw [this]
    exact TwoThin.odd_card_pPrimeCore ↥C
  have huu : uC ^ 2 = 1 := by apply Subtype.ext; simp [pow_two, huCdef, hu2]
  have hact : IsPGroup 2 ↥(zpowers uC) := by
    have hdvd : orderOf uC ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by simpa using huu)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hnorm : zpowers uC ≤ normalizer ((T.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro t
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 huT t
  have key := map_inf_centralizer_eq' (proj y) hker (zpowers uC) (T.subgroupOf C) hact hnorm
  have hL : (T ⊓ centralizer ({u} : Set G)).subgroupOf C =
      T.subgroupOf C ⊓ centralizer ((zpowers uC : Subgroup ↥C) : Set ↥C) := by
    rw [centralizer_zpowers_eq]
    ext t
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Subtype.ext h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, congrArg Subtype.val h2⟩
  have hR : (zpowers uC).map (proj y) = zpowers (piC y u) := by
    rw [MonoidHom.map_zpowers, piC_of_mem y huC]
  show ((T ⊓ centralizer ({u} : Set G)).subgroupOf C).map (proj y) =
    (T.subgroupOf C).map (proj y) ⊓ centralizer ({piC y u} : Set (CentralizerBar y))
  rw [hL, key, hR, centralizer_zpowers_eq]

theorem exists_derivedSeries_succ_eq (H : Type*) [Group H] [Finite H] :
    ∃ n, derivedSeries H (n + 1) = derivedSeries H n := by
  by_contra hne
  push Not at hne
  have key : ∀ n, Nat.card ↥(derivedSeries H n) + n ≤ Nat.card H := by
    intro n
    induction n with
    | zero =>
        simp only [derivedSeries_zero, add_zero]
        exact Subgroup.card_le_of_le le_top |>.trans (by rw [Subgroup.card_top])
    | succ n ih =>
        have hle : derivedSeries H (n + 1) ≤ derivedSeries H n := by
          rw [derivedSeries_succ]; exact Subgroup.commutator_le_left _ _
        have hlt : Nat.card ↥(derivedSeries H (n + 1)) < Nat.card ↥(derivedSeries H n) :=
          Subgroup.card_lt_of_lt (lt_of_le_of_ne hle (hne n))
        omega
  have h1 := key (Nat.card H)
  have h2 : 0 < Nat.card ↥(derivedSeries H (Nat.card H)) := Nat.card_pos
  omega

theorem exists_perfect_le {X : Subgroup G} {Δ : Subgroup (CentralizerBar y)} (hΔ : Δ ≤ S3.imgBar y X) (hp : ⁅Δ, Δ⁆ = Δ) :
    ∃ P : Subgroup G, P ≤ X ∧ ⁅P, P⁆ = P ∧ Δ ≤ S3.imgBar y P := by
  have hind : ∀ m, Δ ≤ S3.imgBar y ((derivedSeries ↥X m).map X.subtype) := by
    intro m
    induction m with
    | zero =>
        rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact hΔ
    | succ m ih =>
        rw [← hp, Subgroup.commutator_le]
        intro a ha b hb
        obtain ⟨a', ha'D, rfl⟩ := S3.mem_imgBar.1 (ih ha)
        obtain ⟨b', hb'D, rfl⟩ := S3.mem_imgBar.1 (ih hb)
        refine S3.mem_imgBar.2 ⟨⁅a', b'⁆, ?_, by rw [map_commutatorElement]⟩
        obtain ⟨a'', ha'', ha''e⟩ := ha'D
        obtain ⟨b'', hb'', hb''e⟩ := hb'D
        refine ⟨⁅a'', b''⁆, ?_, ?_⟩
        · rw [derivedSeries_succ]
          exact Subgroup.commutator_mem_commutator ha'' hb''
        · rw [map_commutatorElement, ha''e, hb''e]
          exact (map_commutatorElement (centralizer ({y} : Set G)).subtype a' b').symm
  obtain ⟨n, hn⟩ := exists_derivedSeries_succ_eq ↥X
  refine ⟨(derivedSeries ↥X n).map X.subtype, Subgroup.map_subtype_le _, ?_, hind n⟩
  rw [← Subgroup.map_commutator, ← derivedSeries_succ, hn]

theorem le_perfectCoreOf {P X : Subgroup G} (hPX : P ≤ X) (hP : ⁅P, P⁆ = P) :
    P ≤ perfectCoreOf X := by
  have hind : ∀ m, P ≤ (derivedSeries ↥X m).map X.subtype := by
    intro m
    induction m with
    | zero =>
        rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact hPX
    | succ m ih =>
        rw [derivedSeries_succ, Subgroup.map_commutator, ← hP]
        exact Subgroup.commutator_mono ih ih
  intro x hx
  refine ⟨⟨x, hPX hx⟩, Subgroup.mem_iInf.2 fun m => ?_, rfl⟩
  obtain ⟨d, hd, hde⟩ := hind m hx
  have : d = ⟨x, hPX hx⟩ := Subtype.ext hde
  rwa [this] at hd

theorem mem_perfectCoreOf_of_img {X : Subgroup G} {Δ : Subgroup (CentralizerBar y)} (hΔ : Δ ≤ S3.imgBar y X) (hp : ⁅Δ, Δ⁆ = Δ)
    (hyΔ : piC y y ∈ Δ) (hy2 : y * y = 1) : y ∈ perfectCoreOf X := by
  obtain ⟨P, hPX, hPp, hΔP⟩ := exists_perfect_le hΔ hp
  exact le_perfectCoreOf hPX hPp (mem_of_piC_mem hy2 (hΔP hyΔ))

theorem exists_lift_central {J S : Subgroup G} (hJC : J ≤ centralizer ({y} : Set G))
    (hS : IsSylowOf 2 S J) {zb : CentralizerBar y} (hzb : zb ∈ S3.imgBar y J) (hz2 : zb * zb = 1)
    (hzc : ∀ c ∈ S3.imgBar y J, c * zb = zb * c) : ∃ z ∈ S, piC y z = zb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({y} : Set G) with hC
  have hQ : IsPGroup 2 ↥(zpowers zb) := by
    have hdvd : orderOf zb ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hz2)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hQH : zpowers zb ≤ (J.subgroupOf C).map (proj y) := by
    rw [Subgroup.zpowers_le]; exact hzb
  obtain ⟨P', -, hP'H, hP'2, hP'Q⟩ := exists_isPGroup_map_eq_of_map_le' (proj y) hQ hQH
    (IsPGroup.of_bot) bot_le (by simp)
  obtain ⟨p', hp'P, hp'e⟩ : zb ∈ P'.map (proj y) := by rw [hP'Q]; exact Subgroup.mem_zpowers zb
  set P : Subgroup G := P'.map C.subtype with hPdef
  have hPJ : P ≤ J := by
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hP'H hq)
  have hP2 : IsPGroup 2 ↥P := hP'2.map C.subtype
  obtain ⟨k, hkJ, hk⟩ := C3.Layer1.Back.exists_mem_conjugate_le_of_isSylowOf hS hPJ hP2
  have hkC : k ∈ C := hJC hkJ
  have hpC : (p' : G) ∈ C := p'.2
  refine ⟨k⁻¹ * p' * k, hk (C3.Layer1.Back.mem_conjugate_iff'.2 ?_), ?_⟩
  · show k * (k⁻¹ * (p' : G) * k) * k⁻¹ ∈ P
    rw [show k * (k⁻¹ * (p' : G) * k) * k⁻¹ = p' by group]
    exact ⟨p', hp'P, rfl⟩
  · have hpz : piC y (p' : G) = zb := by rw [piC_of_mem y hpC]; exact hp'e
    have hkz : piC y k * zb = zb * piC y k :=
      hzc _ (S3.mem_imgBar.2 ⟨⟨k, hkC⟩, hkJ, (piC_of_mem y hkC).symm⟩)
    rw [piC_mul y (mul_mem (inv_mem hkC) hpC) hkC, piC_mul y (inv_mem hkC) hpC, piC_inv y hkC, hpz]
    calc (piC y k)⁻¹ * zb * piC y k = (piC y k)⁻¹ * (zb * piC y k) := by group
      _ = (piC y k)⁻¹ * (piC y k * zb) := by rw [hkz]
      _ = zb := by group

theorem exists_D8_lift {T : Subgroup G} {u : G}
    (huC : u ∈ centralizer ({y} : Set G)) (hu2 : u * u = 1) (huT : u ∈ normalizer (T : Set G))
    (hyT : y ∈ T) {a w : CentralizerBar y} (ha : a ∈ S3.imgBar y T) (hw : w ∈ S3.imgBar y T)
    (hau : a * piC y u = piC y u * a) (hwu : w * piC y u = piC y u * w) (haa : a * a = piC y y)
    (hww : w * w = 1) (hwa : w * a * w⁻¹ = a⁻¹) (hy2 : y * y = 1) :
    ∃ a' w' : G, a' ∈ T ⊓ centralizer ({u} : Set G) ∧ w' ∈ T ⊓ centralizer ({u} : Set G) ∧
      a' * a' = y ∧ w' * w' = 1 ∧ w' * a' * w'⁻¹ = a'⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({y} : Set G) with hC
  set T₂ := T ⊓ centralizer ({u} : Set G) with hT₂
  have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hyT₂ : y ∈ T₂ := Subgroup.mem_inf.2 ⟨hyT, Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_singleton_iff.1 huC).symm⟩
  have himg := imgBar_inf_centralizer huC hu2 huT
  have ha2 : a ∈ S3.imgBar y T₂ := by
    rw [himg]; exact Subgroup.mem_inf.2 ⟨ha, Subgroup.mem_centralizer_singleton_iff.2 hau⟩
  have hw2 : w ∈ S3.imgBar y T₂ := by
    rw [himg]; exact Subgroup.mem_inf.2 ⟨hw, Subgroup.mem_centralizer_singleton_iff.2 hwu⟩
  have hapow : a ^ 4 = 1 := by
    calc a ^ 4 = (a * a) * (a * a) := by simp [pow_succ, mul_assoc]
      _ = piC y (y * y) := by rw [haa, piC_mul y hyC hyC]
      _ = 1 := by rw [hy2, piC_one]
  have hA : IsPGroup 2 ↥(zpowers a) := by
    have hdvd : orderOf a ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hapow)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hW : IsPGroup 2 ↥(zpowers w) := by
    have hdvd : orderOf w ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hww)
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hfwd : ∀ c ∈ zpowers a, w * c * w⁻¹ ∈ zpowers a := by
    intro c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    rw [← conj_zpow, hwa]
    exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)) k
  have hWA : zpowers w ≤ normalizer ((zpowers a : Subgroup (CentralizerBar y)) : Set (CentralizerBar y)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨hfwd c, fun hc => ?_⟩
    have h1 := hfwd _ hc
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rwa [show w * (w * c * w⁻¹) * w⁻¹ = (w * w) * c * (w⁻¹ * w⁻¹) by group, hww, hwi, hww,
      one_mul, mul_one] at h1
  have hD : IsPGroup 2 ↥(zpowers w ⊔ zpowers a) := hW.to_sup_of_normal_right' hA hWA
  have hDH : zpowers w ⊔ zpowers a ≤ (T₂.subgroupOf C).map (proj y) := by
    refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le]
    · exact hw2
    · exact ha2
  set yC : ↥C := ⟨y, hyC⟩ with hyCdef
  have hE : IsPGroup 2 ↥(zpowers yC) := by
    have hdvd : orderOf yC ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by
      apply Subtype.ext; simp [pow_two, hyCdef, hy2])
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have hEH : zpowers yC ≤ T₂.subgroupOf C := by
    rw [Subgroup.zpowers_le]; exact Subgroup.mem_subgroupOf.2 hyT₂
  have hEQ : (zpowers yC).map (proj y) ≤ zpowers w ⊔ zpowers a := by
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    refine Subgroup.mem_sup_right ?_
    have : proj y yC = a ^ 2 := by rw [← piC_of_mem y hyC, pow_two, haa]
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers a) 2
  obtain ⟨P', hEP', hP'H, hP'2, hP'D⟩ := exists_isPGroup_map_eq_of_map_le' (proj y) hD hDH hE hEH hEQ
  obtain ⟨a₀, ha₀P, ha₀e⟩ : a ∈ P'.map (proj y) := by
    rw [hP'D]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
  obtain ⟨w₀, hw₀P, hw₀e⟩ : w ∈ P'.map (proj y) := by
    rw [hP'D]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  set P : Subgroup G := P'.map C.subtype with hPdef
  have hPC : P ≤ C := Subgroup.map_subtype_le _
  have hP2 : IsPGroup 2 ↥P := hP'2.map C.subtype
  have hPT₂ : P ≤ T₂ := by
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hP'H hq)
  have ha₀ : (a₀ : G) ∈ P := ⟨a₀, ha₀P, rfl⟩
  have hw₀ : (w₀ : G) ∈ P := ⟨w₀, hw₀P, rfl⟩
  have hyP : y ∈ P := ⟨yC, hEP' (Subgroup.mem_zpowers yC), rfl⟩
  have hpa : piC y (a₀ : G) = a := by rw [piC_of_mem y a₀.2]; exact ha₀e
  have hpw : piC y (w₀ : G) = w := by rw [piC_of_mem y w₀.2]; exact hw₀e
  refine ⟨a₀, w₀, hPT₂ ha₀, hPT₂ hw₀, ?_, ?_, ?_⟩
  · refine eq_of_piC_eq hPC hP2 (mul_mem ha₀ ha₀) hyP ?_
    rw [piC_mul y a₀.2 a₀.2, hpa, haa]
  · refine eq_of_piC_eq hPC hP2 (mul_mem hw₀ hw₀) (one_mem _) ?_
    rw [piC_mul y w₀.2 w₀.2, hpw, hww, piC_one]
  · refine eq_of_piC_eq hPC hP2 (mul_mem (mul_mem hw₀ ha₀) (inv_mem hw₀)) (inv_mem ha₀) ?_
    rw [piC_mul y (mul_mem w₀.2 a₀.2) (inv_mem w₀.2), piC_mul y w₀.2 a₀.2, piC_inv y w₀.2,
      piC_inv y a₀.2, hpa, hpw, hwa]

end GLevel

end S3Sec29D4

end CFSG.GH74.Generic.BProg.B3

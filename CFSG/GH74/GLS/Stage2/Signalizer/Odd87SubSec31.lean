module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SubSecLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Stmt
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GrpLift
import CFSG.GH74.Orders.LieType

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer

section Aux

private theorem isPGroup_two_zpowers {M : Type*} [Group M] {x : M} (hx : x * x = 1) :
    IsPGroup 2 ↥(zpowers x) := by
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hx
  rintro ⟨g, hg⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, ?_⟩
  apply Subtype.ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]

private theorem isPGroup_two_sup_zpowers {M : Type*} [Group M] {x y : M} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) : IsPGroup 2 ↥(zpowers x ⊔ zpowers y) := by
  refine (isPGroup_two_zpowers hx).to_sup_of_normal_right' (isPGroup_two_zpowers hy) ?_
  rw [Subgroup.zpowers_le]
  refine Subgroup.centralizer_le_normalizer ((zpowers y : Subgroup M) : Set M) ?_
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨n, rfl⟩
  exact (Commute.zpow_left (show Commute y x from hxy.symm) n).eq

private theorem center_eq_bot_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : center X = ⊥) : center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    simpa using Subgroup.mem_center_iff.mp hy (e g)
  rw [h, Subgroup.mem_bot] at hx
  rw [hx, map_one]
  exact one_mem _

private theorem center_eq_bot_of_a7_or_l2 {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 X Odd) : center X = ⊥ := by
  rcases h with ⟨⟨e⟩⟩ | ⟨F₀, _, _, -, ⟨e⟩⟩
  · refine center_eq_bot_of_equiv e.symm (alternatingGroup.center_eq_bot ?_)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  · exact center_eq_bot_of_equiv (e.trans (IVK.L2.equivPSL F₀)).symm
      (CFSG.GorensteinWalter.psl2_center_eq_bot F₀)

private theorem eq_of_isCyclic_of_sq {R : Type*} [Group R] [Finite R] [IsCyclic R] {a b : R}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite R
  by_contra hab
  have hmem : ∀ x : R, x * x = 1 → x ∈ Finset.univ.filter fun x : R => x ^ 2 = 1 := fun x hx =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ x, by rw [pow_two, hx]⟩
  have h3 : 2 < (Finset.univ.filter fun x : R => x ^ 2 = 1).card := by
    rw [Finset.two_lt_card]
    exact ⟨1, hmem 1 (mul_one 1), a, hmem a ha, b, hmem b hb, ha1.symm, hb1.symm, hab⟩
  have := IsCyclic.card_pow_eq_one_le (α := R) (n := 2) (by norm_num)
  omega

private theorem quat_eq_a_of_orderOf_eq_two {N : ℕ} [NeZero N] {q : QuaternionGroup N}
    (hq : orderOf q = 2) : q = QuaternionGroup.a (N : ZMod (2 * N)) := by
  cases q with
  | xa i =>
      have hfour := QuaternionGroup.orderOf_xa i
      omega
  | a i =>
      have hi_ne : i ≠ 0 := by
        intro hi
        subst i
        rw [QuaternionGroup.a_zero, orderOf_one] at hq
        omega
      have hpow := pow_orderOf_eq_one (QuaternionGroup.a i)
      rw [hq] at hpow
      rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def,
        QuaternionGroup.a.injEq] at hpow
      have hcast : ((2 * i.val : ℕ) : ZMod (2 * N)) = 0 := by
        calc
          (↑(2 * i.val) : ZMod (2 * N)) =
              2 * (↑i.val : ZMod (2 * N)) := by norm_num
          _ = i + i := by rw [ZMod.natCast_zmod_val]; noncomm_ring
          _ = 0 := hpow
      have hdvd2 : 2 * N ∣ 2 * i.val :=
        (ZMod.natCast_eq_zero_iff (2 * i.val) (2 * N)).mp hcast
      have hdvd : N ∣ i.val :=
        Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd2
      have hval_ne : i.val ≠ 0 := by
        simpa [ZMod.val_eq_zero] using hi_ne
      have hval : i.val = N :=
        Nat.eq_of_dvd_of_lt_two_mul hval_ne hdvd (ZMod.val_lt i)
      rw [← ZMod.natCast_zmod_val i, hval]

private theorem eq_of_isQuat_of_sq {R : Type} [Group R] (hR : IsQuat R) {a b : R}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨n, -, ⟨e⟩⟩ := hR
  have hord : ∀ x : R, x * x = 1 → x ≠ 1 → orderOf (e x) = 2 := by
    intro x hx hx1
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, hx, map_one]
    · intro h
      exact hx1 (e.injective (by rw [h, map_one]))
  apply e.injective
  rw [quat_eq_a_of_orderOf_eq_two (hord a ha ha1), quat_eq_a_of_orderOf_eq_two (hord b hb hb1)]

end Aux

section M11

private theorem exists_orderOf_eleven : ∃ x : ↥NativeSporadic.M11, orderOf x = 11 := by
  let a : Equiv.Perm (Fin 11) :=
    List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]
  let b : Equiv.Perm (Fin 11) := List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]
  have ha : a ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hb : b ∈ NativeSporadic.M11 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hx : (a * b) ^ 3 ∈ NativeSporadic.M11 := pow_mem (mul_mem ha hb) 3
  refine ⟨⟨(a * b) ^ 3, hx⟩, ?_⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have h1 : ((a * b) ^ 3) ^ 11 = 1 := by
    ext i
    revert i
    decide +kernel
  have h2 : ((a * b) ^ 3) ≠ 1 := by
    intro h
    have := congrArg (fun f : Equiv.Perm (Fin 11) => f 0) h
    revert this
    decide +kernel
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime h1 h2

private theorem card_dvd_of_isSporadic_M11 {X : Type} [Group X]
    (hX : NativeSporadic.IsSporadic X .M11) :
    Nat.card X ∣ Nat.factorial 11 ∧ 11 ∣ Nat.card X := by
  obtain ⟨e⟩ := hX
  have hcard : Nat.card X = Nat.card ↥NativeSporadic.M11 := Nat.card_congr e.toEquiv
  rw [hcard]
  refine ⟨?_, ?_⟩
  · have h := Subgroup.card_subgroup_dvd_card NativeSporadic.M11
    rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 11)), Fintype.card_perm,
      Fintype.card_fin] at h
  · obtain ⟨x, hx⟩ := exists_orderOf_eleven
    have := orderOf_dvd_natCard x
    rwa [hx] at this

private theorem ordA_two (q : ℕ) :
    CFSG.Open.ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold CFSG.Open.ordA
  rw [Finset.prod_Icc_succ_top (by norm_num), Finset.Icc_self, Finset.prod_singleton]

private theorem not_psl3_card {q : ℕ} (hq2 : 2 ≤ q) (hodd : Odd q ∨ q = 4)
    (hdvd : CFSG.Open.ordA 2 q ∣ Nat.factorial 11) (h11 : 11 ∣ CFSG.Open.ordA 2 q) :
    False := by
  by_cases hbig : 13 ≤ q
  · rw [ordA_two] at hdvd
    have hd3 : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
    have hq1 : Nat.gcd 3 (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
    have h2 : q - 1 ∣ q ^ 2 - 1 := by
      simpa using Nat.sub_dvd_pow_sub_pow q 1 2
    have hdiv : Nat.gcd 3 (q - 1) ∣ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Dvd.dvd.mul_left (Dvd.dvd.mul_right (hq1.trans h2) _) _
    have hN := Nat.le_of_dvd (Nat.factorial_pos 11) hdvd
    have hmul := Nat.div_mul_cancel hdiv
    have hle : q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) * Nat.gcd 3 (q - 1) ≤
        Nat.factorial 11 * 3 := Nat.mul_le_mul hN hd3
    rw [hmul] at hle
    have h1 : 13 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hbig 3
    have h2' : 13 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left hbig 2) 1
    have h3' : 13 ^ 3 - 1 ≤ q ^ 3 - 1 := Nat.sub_le_sub_right h1 1
    have := Nat.mul_le_mul h1 (Nat.mul_le_mul h2' h3')
    have hf : Nat.factorial 11 = 39916800 := by decide
    rw [hf] at hle
    norm_num at this hle
    omega
  · rw [not_le] at hbig
    interval_cases q
    · exact absurd hodd (by decide)
    · revert hdvd h11; rw [ordA_two]; decide
    · revert hdvd h11; rw [ordA_two]; decide
    · revert hdvd h11; rw [ordA_two]; decide
    · exact absurd hodd (by decide)
    · revert hdvd h11; rw [ordA_two]; decide
    · exact absurd hodd (by decide)
    · revert hdvd h11; rw [ordA_two]; decide
    · exact absurd hodd (by decide)
    · revert hdvd h11; rw [ordA_two]; decide
    · exact absurd hodd (by decide)

private theorem lieModel_psl_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n p f : ℕ} (hn : n ≠ 0) (h : LieModel Y .PSL n p f) : LieModel X .PSL n p f := by
  obtain ⟨hadm, K, hK, hKf, hc, ⟨e'⟩⟩ := CFSG.GH74.statedClassicalModel_of_lieModel hn h
  exact Or.inl ⟨by decide, hadm, K, hK, hKf, hc, ⟨e.trans e'⟩⟩

end M11

section Sec31Core
variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G} {B : Type}
  [Group B] [Finite B]

theorem sec31_core_hom (hL : Lemma31Narrow) (hctx : Stage2Ctx G z k S) {H₀ : Subgroup G}
    (hH₀ : H₀ ≠ ⊤) (π : ↥H₀ →* B) (hπ : Function.Surjective π) (hodd : Odd (Nat.card π.ker))
    {J : Subgroup B} (hJ : IsComponent J) {W : Subgroup B} (hW2 : IsPGroup 2 ↥W)
    (hWJ : W ≤ centralizer (J : Set B)) (hW1 : W ≠ ⊥) :
    ∃ (Jt R : Subgroup G) (ρ : ↥R →* B), IsPCompIn 2 H₀ Jt ∧ (Jt.subgroupOf H₀).map π = J ∧
      Nonempty (Hat Jt ≃* Hat J) ∧ Lemma31NarrowConcl z H₀ Jt R ∧ Function.Injective ρ ∧
        W ≤ ρ.range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Jt, hJt, himg, hHat, hcent⟩ := exists_pcomp_lift π hπ hodd hJ
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(W.comap π)) := inferInstance
  have hP : ((P : Subgroup ↥(W.comap π)).map (W.comap π).subtype).map π = W :=
    map_sylow_comap_eq π hπ W hW2 P
  set W' : Subgroup ↥H₀ := (P : Subgroup ↥(W.comap π)).map (W.comap π).subtype
  have hW'2 : IsPGroup 2 ↥W' := P.isPGroup'.map _
  set C : Subgroup G := H₀ ⊓ centralizerSection Jt (pPrimeCoreOf 2 Jt)
  have hW'mem : ∀ x ∈ W', π x ∈ W := fun x hx => hP ▸ Subgroup.mem_map_of_mem π hx
  have hW'C : W'.map H₀.subtype ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, hcent x (hWJ (hW'mem x hx))⟩
  have hW'C2 : IsPGroup 2 ↥((W'.map H₀.subtype).subgroupOf C) :=
    (hW'2.map H₀.subtype).of_equiv (Subgroup.subgroupOfEquivOfLe hW'C).symm
  obtain ⟨Q, hQ⟩ := hW'C2.exists_le_sylow
  set R : Subgroup G := (Q : Subgroup ↥C).map C.subtype
  have hRC : R ≤ C := Subgroup.map_subtype_le _
  have hRH₀ : R ≤ H₀ := hRC.trans inf_le_left
  have hWR : W'.map H₀.subtype ≤ R := by
    intro g hg
    have hgC := hW'C hg
    exact ⟨⟨g, hgC⟩, hQ (show (⟨g, hgC⟩ : ↥C) ∈ (W'.map H₀.subtype).subgroupOf C from hg), rfl⟩
  have hR2 : IsPGroup 2 ↥R := Q.isPGroup'.map _
  let ρ : ↥R →* B := π.comp (Subgroup.inclusion hRH₀)
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    have hbot := isPGroup_two_inf_eq_bot_of_odd (R.subgroupOf H₀) π.ker
      (hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRH₀).symm) hodd
    have hmem : (Subgroup.inclusion hRH₀ r : ↥H₀) ∈ R.subgroupOf H₀ ⊓ π.ker := ⟨r.2, hr⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subgroup.inclusion_injective hRH₀ (by rw [hmem, map_one]))
  have hWρ : W ≤ ρ.range := by
    intro w hw
    rw [← hP] at hw
    obtain ⟨x, hx, rfl⟩ := hw
    exact ⟨⟨x, hWR ⟨x, hx, rfl⟩⟩, rfl⟩
  have hRne : R ≠ ⊥ := by
    intro hRb
    apply hW1
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨r, rfl⟩ := hWρ hw
    have hr : r = 1 := Subtype.ext (by simpa [hRb] using r.2)
    rw [hr, map_one]
    exact one_mem _
  exact ⟨Jt, R, ρ, hJt, himg, hHat, hL G z k S hctx H₀ Jt R hH₀ hJt ⟨Q, rfl⟩ hRne, hρinj, hWρ⟩

end Sec31Core

section Transport
variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}

theorem sec31_unique_inv (hL : Lemma31Narrow) (hctx : Stage2Ctx G z k S) {B : Type} [Group B]
    [Finite B] {b : B} (hB : SecOfG G z B b) {J : Subgroup B} (hJ : IsComponent J)
    (hZ : center (Hat J) ≠ ⊥) {u v : B} (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huJ : u ∈ centralizer (J : Set B)) (hvJ : v ∈ centralizer (J : Set B))
    (huv : u * v = v * u) : u = v := by
  obtain ⟨H₀, π, hH₀, hπ, hodd, -⟩ := SecOfG.exists_hom hB
  have hW2 : IsPGroup 2 ↥(zpowers u ⊔ zpowers v) := isPGroup_two_sup_zpowers hu hv huv
  have huW : u ∈ zpowers u ⊔ zpowers v := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hvW : v ∈ zpowers u ⊔ zpowers v := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have hWJ : zpowers u ⊔ zpowers v ≤ centralizer (J : Set B) :=
    sup_le (Subgroup.zpowers_le.mpr huJ) (Subgroup.zpowers_le.mpr hvJ)
  have hW1 : zpowers u ⊔ zpowers v ≠ ⊥ := fun h => hu1 (by simpa [h] using huW)
  obtain ⟨Jt, R, ρ, -, -, ⟨e⟩, hconcl, hρinj, hWρ⟩ :=
    sec31_core_hom hL hctx hH₀ π hπ hodd hJ hW2 hWJ hW1
  obtain ⟨r₁, hr₁⟩ := hWρ huW
  obtain ⟨r₂, hr₂⟩ := hWρ hvW
  have hsq : ∀ (r : ↥R) (x : B), ρ r = x → x * x = 1 → r * r = 1 := fun r x hr hx =>
    hρinj (by rw [map_mul, hr, hx, map_one])
  have hne : ∀ (r : ↥R) (x : B), ρ r = x → x ≠ 1 → r ≠ 1 := fun r x hr hx h =>
    hx (by rw [← hr, h, map_one])
  obtain ⟨hR, hdih, -, -⟩ := hconcl
  have hrr : r₁ = r₂ := by
    rcases hR with hc | hq | hd
    · exact eq_of_isCyclic_of_sq (hsq r₁ u hr₁ hu) (hsq r₂ v hr₂ hv) (hne r₁ u hr₁ hu1)
        (hne r₂ v hr₂ hv1)
    · exact eq_of_isQuat_of_sq hq (hsq r₁ u hr₁ hu) (hsq r₂ v hr₂ hv) (hne r₁ u hr₁ hu1)
        (hne r₂ v hr₂ hv1)
    · exact absurd (center_eq_bot_of_equiv e (center_eq_bot_of_a7_or_l2 (hdih hd))) hZ
  rw [← hr₁, ← hr₂, hrr]

theorem sec31_f (hL : Lemma31Narrow) (hctx : Stage2Ctx G z k S) {B : Type} [Group B] [Finite B]
    {b : B} (hB : SecOfG G z B b) {J : Subgroup B} (hJ : IsComponent J) {p n : ℕ}
    (hp : p.Prime) (hn : 1 ≤ n) (hodd : Odd (p ^ n) ∨ p ^ n = 4)
    (hL3 : LieModel (Hat J) .PSL 3 p n) {c : B} (hc : orderOf c = 2)
    (hcJ : c ∈ centralizer (J : Set B)) : False := by
  obtain ⟨H₀, π, hH₀, hπ, hodd', -⟩ := SecOfG.exists_hom hB
  have hc2 : c * c = 1 := by
    rw [← pow_two]
    exact hc ▸ pow_orderOf_eq_one c
  have hW2 : IsPGroup 2 ↥(zpowers c) := isPGroup_two_zpowers hc2
  have hWJ : zpowers c ≤ centralizer (J : Set B) := Subgroup.zpowers_le.mpr hcJ
  have hW1 : zpowers c ≠ ⊥ := by
    intro h
    have hcm : c ∈ zpowers c := Subgroup.mem_zpowers c
    rw [h, Subgroup.mem_bot] at hcm
    rw [hcm, orderOf_one] at hc
    omega
  obtain ⟨Jt, R, ρ, -, -, ⟨e⟩, hconcl, -, -⟩ :=
    sec31_core_hom hL hctx hH₀ π hπ hodd' hJ hW2 hWJ hW1
  have hL3t : LieModel (Hat Jt) .PSL 3 p n := lieModel_psl_of_mulEquiv e (by norm_num) hL3
  obtain ⟨-, -, -, hfclause⟩ := hconcl
  have hf := hfclause (Or.inr ⟨p, n, hp, hn, hodd, Or.inl hL3t⟩)
  have hcard : Nat.card (Hat Jt) = CFSG.Open.ordA 2 (p ^ n) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.GH74.card_of_lieModel_PSL (by norm_num) hL3
  obtain ⟨hd, h11⟩ := card_dvd_of_isSporadic_M11 hf.1
  rw [hcard] at hd h11
  exact not_psl3_card (hp.two_le.trans (Nat.le_self_pow (by omega) p)) hodd hd h11

end Transport

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

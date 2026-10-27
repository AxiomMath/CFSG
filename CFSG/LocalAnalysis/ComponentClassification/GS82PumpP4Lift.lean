module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Inputs
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import CFSG.GH74.Generic.GKFCover
public import CFSG.Assembly.OrderReductions.LinearOrders

public section

namespace CFSG.ComponentClassification.GS82PumpInputs.P4

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
open scoped MatrixGroups commutatorElement

theorem eq_one_of_pow_two_pow_eq_one {G : Type*} [Group G] {H : Subgroup G}
    (hH : Odd (Nat.card H)) {x : G} (hx : x ∈ H) (k : ℕ) (hxk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have h2 : orderOf x ∣ Nat.card H := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card H) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hH)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem card_comap_of_surjective {G G' : Type*} [Group G] [Group G'] [Finite G]
    (f : G →* G') (hf : Function.Surjective f) (H : Subgroup G') :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  let g : ↥(H.comap f) →* ↥H := (f.comp (H.comap f).subtype).codRestrict H fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hgk : Nat.card g.ker = Nat.card f.ker := by
    have hle : f.ker ≤ H.comap f := fun x hx => by
      rw [mem_comap, MonoidHom.mem_ker.mp hx]
      exact one_mem H
    have : g.ker = f.ker.subgroupOf (H.comap f) := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [RankThree.PerfectCover.card_eq_card_mul_card_ker g hg, hgk, mul_comm]

theorem ordProj_two_pow (a : ℕ) : ordProj[2] (2 ^ a) = 2 ^ a := by
  rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem ordProj_two_mul_odd {a m : ℕ} (ha : a ≠ 0) (hm : Odd m) :
    ordProj[2] (a * m) = ordProj[2] a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  rw [Nat.factorization_mul ha hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
      (even_iff_two_dvd.mpr h)), add_zero]

theorem ordProj_two_pow_mul_odd {a m : ℕ} (hm : Odd m) : ordProj[2] (2 ^ a * m) = 2 ^ a := by
  rw [ordProj_two_mul_odd (pow_ne_zero a two_ne_zero) hm, ordProj_two_pow]

theorem map_perfectResidual_of_isPerfect {Y : Type} [Group Y] [Finite Y] {H : Subgroup Y}
    (hH : Group.IsPerfect ↥H) : (perfectResidual ↥H).map H.subtype = H := by
  have htop : Group.IsPerfect ↥(⊤ : Subgroup ↥H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := ↥H)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := ↥H)).symm.surjective
  have h1 : perfectResidual ↥H = ⊤ :=
    top_unique (RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual ⊤ htop)
  rw [h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem exists_perfect_map_eq {S Y : Type} [Group S] [Group Y] [Finite S] [Finite Y]
    (π : S →* Y) (hπ : Function.Surjective π) {L : Subgroup Y} (hL : Group.IsPerfect ↥L) :
    ∃ P : Subgroup S, Group.IsPerfect ↥P ∧ P.map π = L := by
  set T := L.comap π with hT
  set f : ↥T →* Y := π.comp T.subtype with hf
  have hr : f.range = L := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hT,
      Subgroup.map_comap_eq_self_of_surjective hπ]
  have hrp : Group.IsPerfect ↥f.range := by
    rw [hr]
    exact hL
  have : Group.IsPerfect ↥(perfectResidual ↥T) :=
    (perfect_residual_characterization (G := ↥T)).2.2.1
  refine ⟨(perfectResidual ↥T).map T.subtype, Group.IsPerfect.map T.subtype, ?_⟩
  rw [Subgroup.map_map, ← hf, (perfect_residual_transport f).1,
    map_perfectResidual_of_isPerfect hrp, hr]

theorem odd_exceptionalOrders_PSL {m p f : ℕ} (hp2 : p ≠ 2) :
    Odd ((exceptionalOrders .PSL m p f).1 * (exceptionalOrders .PSL m p f).2) := by
  have h : Odd (exceptionalOrders .PSL m p f).1 ∧ Odd (exceptionalOrders .PSL m p f).2 := by
    unfold exceptionalOrders
    split <;> simp_all
    all_goals decide
  exact h.1.mul h.2

theorem card_hopfMultiplier_psl_two
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    ∃ e : ℕ, Odd e ∧
      Nat.card (RankThree.PerfectCover.hopfMultiplier (StatedProj (StatedSL 2 F))) = 2 * e := by
  have := Fintype.ofFinite F
  obtain ⟨p, hchar⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  obtain ⟨f, hp, hcardF⟩ := FiniteField.card F p
  have hcard : Nat.card F = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hcardF]
  have hq : Odd (p ^ (f : ℕ)) := hcard ▸ hodd
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hq) ((Nat.even_pow' f.ne_zero).mpr even_two)
  have hadm : StatedLieAdmissible .PSL 2 p f :=
    ⟨hp, f.pos, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
      fun h => by simp only [Prod.mk.injEq] at h; omega⟩
  obtain ⟨-, ⟨eM⟩⟩ := LieType.Steinberg.CentralExt.GriessClassical.psl_row
    (X := StatedProj (StatedSL 2 F))
    ⟨hadm, F, inferInstance, inferInstance, hcard, ⟨MulEquiv.refl _⟩⟩
  have hgen : genericOrders .PSL 2 p f = (2, 1) := by
    have h1 : Nat.gcd 2 (p ^ (f : ℕ) - 1) = 2 := by
      obtain ⟨k, hk⟩ := hq
      exact Nat.gcd_eq_left ⟨k, by omega⟩
    exact Prod.ext h1 rfl
  refine ⟨(exceptionalOrders .PSL 2 p f).1 * (exceptionalOrders .PSL 2 p f).2,
    odd_exceptionalOrders_PSL hp2, ?_⟩
  rw [← Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr eM.toEquiv, Nat.card_prod]
  unfold generic exceptional
  rw [hgen]
  simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]

theorem odd_card_ker_of_sl2
    {P : Type} [Group P] [Finite P] (hP : Group.IsPerfect P)
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hOSL : pPrimeCore 2 SL(2, F) = ⊥) (θ : P →* SL(2, F)) (hθ : Function.Surjective θ)
    (hcomm : ∀ k ∈ θ.ker, ∀ g : P, ⁅k, g⁆ ∈ pPrimeCore 2 P) : Odd (Nat.card θ.ker) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 P with hOdef
  have hOle : O ≤ θ.ker := by
    have h1 : O.map θ ≤ pPrimeCore 2 SL(2, F) := map_pPrimeCore_le θ hθ
    rw [hOSL, Subgroup.map_le_iff_le_comap, MonoidHom.comap_bot] at h1
    exact h1
  let θ' : P ⧸ O →* SL(2, F) := QuotientGroup.lift O θ hOle
  have hθ'mk : ∀ g : P, θ' (QuotientGroup.mk g) = θ g := fun g => rfl
  have hθ' : Function.Surjective θ' := by
    intro s
    obtain ⟨g, rfl⟩ := hθ s
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hker' : θ'.ker ≤ center (P ⧸ O) := by
    intro x hx
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hk : k ∈ θ.ker := by
      rw [MonoidHom.mem_ker, ← hθ'mk]
      exact hx
    rw [mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 := hcomm k hk g
    have h2 : (QuotientGroup.mk ⁅k, g⁆ : P ⧸ O) = 1 := (QuotientGroup.eq_one_iff _).mpr h1
    rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      at h2
    exact h2.symm
  have hP' : Group.IsPerfect (P ⧸ O) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
  set eSL := specialLinearGroupEquivStatedSL 2 F with heSL
  set q : P ⧸ O →* StatedProj (StatedSL 2 F) :=
    (QuotientGroup.mk' ((StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F))).comp
      (eSL.toMonoidHom.comp θ') with hqdef
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective _).comp (eSL.surjective.comp hθ')
  have hqk : q.ker = (center SL(2, F)).comap θ' := by
    ext x
    rw [MonoidHom.mem_ker, mem_comap]
    change QuotientGroup.mk (eSL (θ' x)) = (1 : StatedProj (StatedSL 2 F)) ↔ _
    rw [QuotientGroup.eq_one_iff, ← map_center_eq_statedScalars 2 F]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact (eSL.injective hyx) ▸ hy
    · exact fun h => ⟨θ' x, h, rfl⟩
  have hqker : q.ker ≤ center (P ⧸ O) := by
    rw [hqk, LocalCores.comap_center_eq_of_perfect hP' θ' hθ' hker']
  have hdvd := GH74.Generic.card_ker_dvd_hopfMultiplier hP' q hq hqker
  obtain ⟨e, he, hM⟩ := card_hopfMultiplier_psl_two hodd h5
  have hZ : Nat.card (center SL(2, F)) = 2 := by
    rw [OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num)]
    obtain ⟨k, hk⟩ := hodd
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  have hqcard : Nat.card q.ker = Nat.card θ'.ker * 2 := by
    rw [hqk, card_comap_of_surjective θ' hθ', hZ]
  rw [hqcard, hM, mul_comm] at hdvd
  have hθ'odd : Odd (Nat.card θ'.ker) :=
    Odd.of_dvd_nat he (Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd)
  have hθk : θ.ker = θ'.ker.comap (QuotientGroup.mk' O) := by
    ext g
    rw [MonoidHom.mem_ker, mem_comap, MonoidHom.mem_ker, QuotientGroup.mk'_apply, hθ'mk]
  rw [hθk, card_comap_of_surjective _ (QuotientGroup.mk'_surjective O), QuotientGroup.ker_mk']
  exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).mul hθ'odd

theorem exists_involution_lift
    {E A : Type} [Group E] [Group A] [Finite E] [Finite A]
    (ρ : E →* A) (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center E)
    {q₀ : ℕ} (hq₀ : Odd q₀) (h5 : 5 ≤ q₀) (hA : HarrisLit.IsSLTwoOver q₀ (A ⧸ pPrimeCore 2 A))
    {c : A} (hc : c ∈ center A) (hcc : c * c = 1) :
    ∃ t : E, t * t = 1 ∧ ρ t = c := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, hFq, ⟨eA⟩⟩ := hA
  set OA := pPrimeCore 2 A with hOA
  have hOAodd : Odd (Nat.card OA) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  let θA : A →* SL(2, F) := eA.toMonoidHom.comp (QuotientGroup.mk' OA)
  have hθA : Function.Surjective θA := eA.surjective.comp (QuotientGroup.mk'_surjective OA)
  have hθAker : ∀ a : A, θA a = 1 ↔ a ∈ OA := by
    intro a
    change eA (QuotientGroup.mk a) = 1 ↔ _
    rw [map_eq_one_iff eA eA.injective, QuotientGroup.eq_one_iff]
  have hFodd : Odd (Nat.card F) := by rw [Nat.card_eq_fintype_card, hFq]; exact hq₀
  have hF5 : 5 ≤ Nat.card F := by rw [Nat.card_eq_fintype_card, hFq]; exact h5
  have hOSL : pPrimeCore 2 SL(2, F) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 eA, CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.map_bot]
  set θ : E →* SL(2, F) := θA.comp ρ with hθdef
  have hθ : Function.Surjective θ := hθA.comp hρ
  have hSL : Group.IsPerfect SL(2, F) := LinearGroups.special_linear_dimension_two_perfect
    (LieType.Steinberg.CentralExt.SL2Closed.exists_four_of_five_le hF5)
  have htop : Group.IsPerfect ↥(⊤ : Subgroup SL(2, F)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := SL(2, F))).symm.toMonoidHom)
      (Subgroup.topEquiv (G := SL(2, F))).symm.surjective
  obtain ⟨P, hP, hPm⟩ := exists_perfect_map_eq θ hθ htop
  set θP : ↥P →* SL(2, F) := θ.comp P.subtype with hθPdef
  have hθP : Function.Surjective θP := by
    intro s
    have hs : s ∈ P.map θ := by rw [hPm]; exact mem_top s
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨⟨x, hx⟩, rfl⟩
  have h2c : ∀ x : ↥P, θP x = 1 → ∀ k : ℕ, x ^ 2 ^ k = 1 → x ∈ center ↥P := by
    intro x hx k hxk
    have h1 : ρ (x : E) ∈ OA := (hθAker _).mp hx
    have h2 : ρ (x : E) ^ 2 ^ k = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, hxk, Subgroup.coe_one, map_one]
    have h3 : ρ (x : E) = 1 := eq_one_of_pow_two_pow_eq_one hOAodd h1 k h2
    have h4 : (x : E) ∈ center E := hker (MonoidHom.mem_ker.mpr h3)
    exact mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp h4 g)
  have hcomm : ∀ k ∈ θP.ker, ∀ g : ↥P, ⁅k, g⁆ ∈ pPrimeCore 2 ↥P := by
    set D := θP.ker with hDdef
    obtain ⟨T⟩ : Nonempty (Sylow 2 ↥D) := inferInstance
    have hT2 : ∀ x ∈ (T : Subgroup ↥D), ((x : ↥P)) ∈ center ↥P := by
      intro x hx
      obtain ⟨k, hk⟩ := T.isPGroup' ⟨x, hx⟩
      have hk' : (x : ↥P) ^ 2 ^ k = 1 := by
        have := congrArg (fun y : ↥(T : Subgroup ↥D) => ((y : ↥D) : ↥P)) hk
        simpa using this
      exact h2c _ x.2 k hk'
    have hTc : (T : Subgroup ↥D) ≤ center ↥D := fun x hx =>
      mem_center_iff.mpr fun g => Subtype.ext (mem_center_iff.mp (hT2 x hx) g)
    have hNC : normalizer ((T : Subgroup ↥D) : Set ↥D) ≤
        centralizer ((T : Subgroup ↥D) : Set ↥D) := by
      intro g _
      rw [mem_centralizer_iff]
      intro x hx
      exact (mem_center_iff.mp (hTc hx) g).symm
    have hcompl := MonoidHom.ker_transferSylow_isComplement' T hNC
    have hNO : (MonoidHom.transferSylow T hNC).ker ≤ pPrimeCore 2 ↥D :=
      le_sSup ⟨MonoidHom.normal_ker _, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
        (MonoidHom.not_dvd_card_ker_transferSylow T hNC)⟩
    have hDO : (pPrimeCore 2 ↥D).map D.subtype ≤ pPrimeCore 2 ↥P := by
      rw [ABGLocalTools.pPrimeCore_map_subtype_eq_inf (MonoidHom.normal_ker θP)]
      exact inf_le_right
    intro k hk g
    obtain ⟨⟨o, t⟩, hot⟩ := hcompl.2 ⟨k, hk⟩
    set o' : ↥P := ((o : ↥D) : ↥P) with ho'
    set t' : ↥P := ((t : ↥D) : ↥P) with ht'
    have hkot : k = o' * t' := by
      have := congrArg Subtype.val hot
      simpa using this.symm
    have ho : o' ∈ pPrimeCore 2 ↥P := hDO ⟨o, hNO o.2, rfl⟩
    have ht : t' * g = g * t' := (mem_center_iff.mp (hT2 t t.2) g).symm
    have hcomm_t : ⁅o' * t', g⁆ = o' * (g * o'⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]
      calc o' * t' * g * (o' * t')⁻¹ * g⁻¹ = o' * (t' * g) * t'⁻¹ * o'⁻¹ * g⁻¹ := by group
        _ = o' * (g * t') * t'⁻¹ * o'⁻¹ * g⁻¹ := by rw [ht]
        _ = o' * (g * o'⁻¹ * g⁻¹) := by group
    rw [hkot, hcomm_t]
    exact mul_mem ho ((pPrimeCore_normal (p := 2) (G := ↥P)).conj_mem _ (inv_mem ho) g)
  have hodd := odd_card_ker_of_sl2 hP hFodd hF5 hOSL θP hθP hcomm
  obtain ⟨s, hs⟩ := hθP (θA c)
  set m := Nat.card θP.ker with hm
  have hss : s * s ∈ θP.ker := by
    rw [MonoidHom.mem_ker, map_mul, hs, ← map_mul, hcc, map_one]
  have hsm : (s * s) ^ m = 1 := by
    have h1 : (⟨s * s, hss⟩ : θP.ker) ^ m = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
    exact h2
  have hw : θA c * θA c = 1 := by rw [← map_mul, hcc, map_one]
  set t : E := ((s ^ m : ↥P) : E) with ht
  have htt : t * t = 1 := by
    rw [ht, ← Subgroup.coe_mul, ← pow_add, ← two_mul, pow_mul, sq, hsm]
    rfl
  refine ⟨t, htt, ?_⟩
  have hθt : θA (ρ t) = θA c := by
    change θP (s ^ m) = θA c
    rw [map_pow, hs]
    obtain ⟨j, hj⟩ := hodd
    rw [hj, pow_succ, pow_mul, sq, hw, one_pow, one_mul]
  have h1 : ρ t * c⁻¹ ∈ OA := by
    rw [← hθAker, map_mul, map_inv, hθt, mul_inv_cancel]
  have h2 : (ρ t * c⁻¹) ^ 2 ^ 1 = 1 := by
    have hρt : ρ t * ρ t = 1 := by rw [← map_mul, htt, map_one]
    rw [pow_one, (Commute.inv_right (mem_center_iff.mp hc (ρ t))).mul_pow, sq, sq, hρt,
      ← mul_inv_rev, hcc, inv_one, one_mul]
  exact mul_inv_eq_one.mp (eq_one_of_pow_two_pow_eq_one hOAodd h1 1 h2)

theorem card_center_eq_ordProj_of_cover {S₀ Y : Type} [Group S₀] [Group Y] [Finite S₀]
    [Finite Y] (π : S₀ →* Y) (hπ : Function.Surjective π) {N₀ : Subgroup S₀}
    (hN : ∀ g, g ∈ N₀ ↔ π g ∈ center Y)
    (hinv : ∀ x ∈ N₀, ∀ y ∈ N₀, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y)
    (h2 : IsPGroup 2 ↥(center Y)) {t : S₀} (htt : t * t = 1) (htZ : π t ∈ center Y)
    (ht1 : π t ≠ 1) : Nat.card ↥(center Y) = ordProj[2] (Nat.card N₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkN : π.ker ≤ N₀ := fun k hk => (hN k).mpr (by
    rw [MonoidHom.mem_ker.mp hk]
    exact one_mem _)
  have htN : t ∈ N₀ := (hN t).mpr htZ
  have ht1' : t ≠ 1 := fun h => ht1 (by rw [h, map_one])
  have hodd : ¬ 2 ∣ Nat.card π.ker := by
    intro h2k
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 h2k
    have hkk : (k : S₀) * k = 1 := by
      have h1 := pow_orderOf_eq_one k
      rw [hk, pow_two] at h1
      exact congrArg Subtype.val h1
    have hk1 : (k : S₀) ≠ 1 := by
      intro h
      have h' : k = 1 := Subtype.ext h
      rw [h', orderOf_one] at hk
      exact absurd hk (by norm_num)
    have hkt := hinv _ (hkN k.2) t htN hkk htt hk1 ht1'
    exact ht1 (by rw [← hkt]; exact MonoidHom.mem_ker.mp k.2)
  let ρ : ↥N₀ →* ↥(center Y) :=
    (π.comp N₀.subtype).codRestrict (center Y) fun x => (hN x).mp x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := hπ y
    exact ⟨⟨g, (hN g).mpr hy⟩, rfl⟩
  have hρk : Nat.card ρ.ker = Nat.card π.ker := by
    have : ρ.ker = π.ker.subgroupOf N₀ := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkN).toEquiv
  obtain ⟨a, ha⟩ := h2.exists_card_eq
  rw [RankThree.PerfectCover.card_eq_card_mul_card_ker ρ hρ, hρk, ha,
    ordProj_two_pow_mul_odd (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))]

end CFSG.ComponentClassification.GS82PumpInputs.P4

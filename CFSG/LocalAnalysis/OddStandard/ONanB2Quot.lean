module

public import CFSG.LocalAnalysis.OddStandard.ONanB2D8
public import CFSG.Alternating.Multipliers.Small
public import CFSG.LieType.Steinberg.CentralExt.PSLSmall
public import CFSG.LieType.Steinberg.CentralExt.MultiplierCongr
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.OddStandard.ONanRec.B2

open Subgroup CFSG.GorensteinWalter

section Quotient

variable {Y : Type} [Group Y]

theorem eq_one_of_sq_of_odd {R : Subgroup Y} (hRodd : Odd (Nat.card R)) {r : Y} (hr : r ∈ R)
    (h2 : r * r = 1) : r = 1 := by
  have hord : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  have hodd : orderOf r ∣ Nat.card R := by
    rw [← Subgroup.orderOf_mk r hr]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 2 (Nat.card R) := Nat.coprime_two_left.2 hRodd
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hord hodd)

theorem centD8_quotient (R : Subgroup Y) [R.Normal] (hRc : R ≤ center Y)
    (hRodd : Odd (Nat.card R))
    (hS : ∀ j : Y, orderOf j = 2 → ∃ S : Subgroup Y, Nonempty (S ≃* DihedralGroup 4) ∧
      centralizer ({j} : Set Y) = R ⊔ S) :
    CentD8 (Y ⧸ R) := by
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  set m := Nat.card R with hm
  obtain ⟨k, hk⟩ := hRodd
  have hy2 : y * y ∈ R := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hx]
    exact pow_orderOf_eq_one _
  set j := y ^ m with hj
  have hjbar : (QuotientGroup.mk j : Y ⧸ R) = QuotientGroup.mk y := by
    rw [hj, QuotientGroup.mk_pow, hk, pow_succ, pow_mul]
    have h2 : (QuotientGroup.mk y : Y ⧸ R) ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one _
    rw [h2, one_pow, one_mul]
  have hj2 : j * j = 1 := by
    have h1 : (y * y) ^ m = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := R) (x := ⟨y * y, hy2⟩))
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      exact this
    rw [hj, ← pow_add, ← two_mul, pow_mul, ← h1, pow_two]
  have hj1 : j ≠ 1 := by
    intro h1
    have : (QuotientGroup.mk y : Y ⧸ R) = 1 := by rw [← hjbar, h1, QuotientGroup.mk_one]
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hjo : orderOf j = 2 := orderOf_eq_two_iff.2 ⟨hj2, hj1⟩
  obtain ⟨S, ⟨e⟩, hC⟩ := hS j hjo
  have hCbar : centralizer ({(QuotientGroup.mk y : Y ⧸ R)} : Set (Y ⧸ R)) =
      (centralizer ({j} : Set Y)).map (QuotientGroup.mk' R) := by
    rw [← hjbar]
    apply le_antisymm
    · intro xb hxb
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
      refine ⟨x, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rw [mem_centralizer_singleton_iff] at hxb
      have hr : j⁻¹ * (x * j * x⁻¹) ∈ R := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          show (QuotientGroup.mk x : Y ⧸ R) * QuotientGroup.mk j = QuotientGroup.mk j *
            QuotientGroup.mk x from hxb]
        group
      set r := j⁻¹ * (x * j * x⁻¹) with hrdef
      have hrc : ∀ g : Y, g * r = r * g := fun g => Subgroup.mem_center_iff.1 (hRc hr) g
      have hxj : x * j * x⁻¹ = j * r := by rw [hrdef]; group
      have hr2 : r * r = 1 := by
        have h1 : x * j * x⁻¹ * (x * j * x⁻¹) = 1 := by
          calc x * j * x⁻¹ * (x * j * x⁻¹) = x * (j * j) * x⁻¹ := by group
            _ = 1 := by rw [hj2]; group
        rw [hxj] at h1
        calc r * r = j * j * (r * r) := by rw [hj2, one_mul]
          _ = j * (j * r) * r := by group
          _ = j * (r * j) * r := by rw [hrc j]
          _ = j * r * (j * r) := by group
          _ = 1 := h1
      have hr1 : r = 1 := eq_one_of_sq_of_odd ⟨k, hk⟩ hr hr2
      rw [hr1, mul_one] at hxj
      calc x * j = x * j * x⁻¹ * x := by group
        _ = j * x := by rw [hxj]
    · rintro _ ⟨x, hx', rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx'
      rw [mem_centralizer_singleton_iff]
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx']
  have hSR : S ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro s ⟨hsS, hsR⟩
    have h8 : orderOf s ∣ 8 := by
      have := orderOf_dvd_natCard (⟨s, hsS⟩ : S)
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at this
      rw [← Subgroup.orderOf_mk s hsS]
      exact this
    have hodd : orderOf s ∣ Nat.card R := by
      rw [← Subgroup.orderOf_mk s hsR]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime 8 (Nat.card R) :=
      Nat.Coprime.pow_left 3 (Nat.coprime_two_left.2 ⟨k, hk⟩)
    exact mem_bot.2 (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h8 hodd))
  have hmap : (centralizer ({j} : Set Y)).map (QuotientGroup.mk' R) = S.map (QuotientGroup.mk' R) := by
    rw [hC, Subgroup.map_sup]
    have hR : R.map (QuotientGroup.mk' R) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨r, hr, rfl⟩
      rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hr
    rw [hR, bot_sup_eq]
  let f : S →* Y ⧸ R := (QuotientGroup.mk' R).comp S.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hsR : (s : Y) ∈ R := by
      have : (QuotientGroup.mk' R) (s : Y) = 1 := hs
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have := hSR.le ⟨s.2, hsR⟩
    exact Subtype.ext (mem_bot.1 this)
  have hrange : f.range = S.map (QuotientGroup.mk' R) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr (hCbar.trans (hmap.trans hrange.symm))).trans
    ((MonoidHom.ofInjective hf).symm.trans e)⟩

end Quotient

section Split

open CFSG.RankThree.PerfectCover CFSG.LieType.Steinberg.CentralExt
open scoped commutatorElement

theorem card_hopfMultiplier_congr {X X' : Type} [Group X] [Group X'] (e : X ≃* X') :
    Nat.card (hopfMultiplier X) = Nat.card (hopfMultiplier X') :=
  Nat.card_congr ((hopfMultiplierEquivGriess X).symm.trans
    ((griessHopfMultiplierCongr e).trans (hopfMultiplierEquivGriess X'))).toEquiv

theorem isPerfect_card_hopfMultiplier_dvd_six
    {X : Type} [Group X] (K : Type) [Field K] [Finite K] (hq : Nat.card K = 7 ∨ Nat.card K = 9)
    (e : X ≃* PSL2 K) :
    Group.IsPerfect X ∧ Nat.card (hopfMultiplier X) ∣ 6 := by
  have : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = Nat.card K := Fintype.card_eq_nat_card
  rcases hq with h7 | h9
  · obtain ⟨hc, ⟨m⟩⟩ := SLClosed.psl_two_hopfMultiplier_of_mulEquiv (k := K)
      (by rw [hK, h7]; norm_num) (by rw [hK, h7]; norm_num) e.symm
    refine ⟨Group.isPerfect_def.mpr hc, ?_⟩
    rw [← Nat.card_congr (hopfMultiplierEquivGriess X).toEquiv, Nat.card_congr m.toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hK, h7]
    norm_num
  · obtain ⟨e6⟩ := CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      K (by rw [hK, h9])
    have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    refine ⟨Group.IsPerfect.ofSurjective (f := (e.trans e6).symm.toMonoidHom)
      (e.trans e6).symm.surjective, ?_⟩
    rw [card_hopfMultiplier_congr (e.trans e6),
      CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six.2]

theorem commutatorElement_mul_mem_center' {Y : Type} [Group Y] {a b z w : Y}
    (hz : z ∈ center Y) (hw : w ∈ center Y) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  have hzw : z * w * z⁻¹ = w := by rw [← hz' w]; group
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by rw [← hz' b]
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by rw [hzw]; group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [← hw' a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

section Central

variable {Y X : Type} [Group Y] [Group X] [Group.IsPerfect X] {Z : Subgroup Y}
  {π : Y →* X} (hπ : Function.Surjective π) (hker : π.ker ≤ Z)

include hπ in
theorem map_commutator_eq_top : (commutator Y).map π = ⊤ := by
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ,
    ← commutator_def, Group.IsPerfect.commutator_eq_top]

include hπ hker in
theorem exists_commutator_mul (y : Y) : ∃ e ∈ commutator Y, ∃ z ∈ Z, y = e * z := by
  have hy : π y ∈ (commutator Y).map π := (map_commutator_eq_top hπ).symm ▸ mem_top _
  obtain ⟨e, he, hey⟩ := hy
  refine ⟨e, he, e⁻¹ * y, hker ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hey, inv_mul_cancel]

include hπ hker in
theorem isPerfect_commutator (hZ : Z ≤ center Y) : Group.IsPerfect (commutator Y) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  set E := commutator Y with hE
  calc E = ⁅(⊤ : Subgroup Y), ⊤⁆ := commutator_def Y
    _ ≤ ⁅E, E⁆ := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨e₁, he₁, z₁, hz₁, rfl⟩ := exists_commutator_mul hπ hker a
      obtain ⟨e₂, he₂, z₂, hz₂, rfl⟩ := exists_commutator_mul hπ hker b
      rw [commutatorElement_mul_mem_center' (hZ hz₁) (hZ hz₂)]
      exact Subgroup.commutator_mem_commutator he₁ he₂

include hπ in
theorem surjective_comp_commutator : Function.Surjective (π.comp (commutator Y).subtype) := by
  intro x
  have hx : x ∈ (commutator Y).map π := (map_commutator_eq_top hπ).symm ▸ mem_top _
  obtain ⟨e, he, rfl⟩ := hx
  exact ⟨⟨e, he⟩, rfl⟩

omit [Group.IsPerfect X] in
include hker in
theorem ker_comp_commutator_le_center (hZ : Z ≤ center Y) :
    (π.comp (commutator Y).subtype).ker ≤ center (commutator Y) := by
  intro k hk
  have hk' : (k : Y) ∈ center Y := hZ (hker hk)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext ((Subgroup.mem_center_iff.1 hk') g)

include hπ hker in
theorem card_ker_dvd_hopfMultiplier (hZ : Z ≤ center Y) :
    Nat.card (π.comp (commutator Y).subtype).ker ∣ Nat.card (hopfMultiplier X) := by
  have := isPerfect_commutator hπ hker hZ
  exact Subgroup.card_dvd_of_surjective (hopfMultiplierToKer_surjective _
    (surjective_comp_commutator hπ) (ker_comp_commutator_le_center hker hZ))

end Central

variable {G : Type} [Group G]

theorem conj_mem_centralizer {R : Subgroup G} {g : G} (hg : g ∈ normalizer (R : Set G))
    {c : G} (hc : c ∈ centralizer (R : Set G)) : g * c * g⁻¹ ∈ centralizer (R : Set G) := by
  rw [mem_centralizer_iff]
  intro r hr
  have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := (mem_normalizer_iff.1 (inv_mem hg) r).1 hr
  have h := mem_centralizer_iff.1 hc _ hr'
  calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * r := by group

theorem conj_mem_commutator_centralizer {R : Subgroup G} {g : G}
    (hg : g ∈ normalizer (R : Set G)) {c : G}
    (hc : c ∈ ⁅centralizer (R : Set G), centralizer (R : Set G)⁆) :
    g * c * g⁻¹ ∈ ⁅centralizer (R : Set G), centralizer (R : Set G)⁆ := by
  have hle : (centralizer (R : Set G)).map (MulAut.conj g).toMonoidHom ≤
      centralizer (R : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_centralizer hg hx
  have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hc
  rw [Subgroup.map_commutator] at h
  exact Subgroup.commutator_mono hle hle h

theorem exists_complement
    [Finite G]
    (R : Subgroup G) (hR9 : Nat.card R = 9) (T : Subgroup G)
    (hT : T ≤ normalizer (R : Set G))
    (hirr : ∀ A : Subgroup G, A ≤ R → Nat.card A = 3 → ∃ t ∈ T, ∃ a ∈ A, t * a * t⁻¹ ∉ A)
    (K : Type) [Field K] [Finite K] (hq : Nat.card K = 7 ∨ Nat.card K = 9)
    (π : centralizer (R : Set G) →* PSL2 K) (hπ : Function.Surjective π)
    (hker : π.ker = R.subgroupOf (centralizer (R : Set G))) :
    centralizer (R : Set G) = R ⊔ ⁅centralizer (R : Set G), centralizer (R : Set G)⁆ ∧
      R ⊓ ⁅centralizer (R : Set G), centralizer (R : Set G)⁆ = ⊥ ∧
      Nonempty (↥⁅centralizer (R : Set G), centralizer (R : Set G)⁆ ≃* PSL2 K) := by
  revert π
  set C := centralizer (R : Set G) with hC
  intro π hπ hker
  obtain ⟨hperfK, hdvd⟩ := isPerfect_card_hopfMultiplier_dvd_six (X := PSL2 K) K hq
    (MulEquiv.refl _)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRC : R ≤ C := by
    intro a ha
    rw [hC, mem_centralizer_iff]
    intro b hb
    have := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := R)
      (by rw [hR9]; norm_num)).is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩
    exact congrArg Subtype.val this
  have hZ : R.subgroupOf C ≤ center C := by
    intro r hr
    rw [mem_subgroupOf] at hr
    rw [Subgroup.mem_center_iff]
    intro c
    exact Subtype.ext (mem_centralizer_iff.1 c.2 _ hr).symm
  set E := commutator C with hE
  set q := π.comp E.subtype with hqdef
  have hLE : E.map C.subtype = ⁅C, C⁆ := Subgroup.map_subtype_commutator C
  set A : Subgroup G := (q.ker.map E.subtype).map C.subtype with hA
  have hAeq : A = R ⊓ ⁅C, C⁆ := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · have h1 : ((k : C)) ∈ π.ker := hk
        rw [hker, mem_subgroupOf] at h1
        exact h1
      · rw [← hLE]
        exact ⟨k, k.2, rfl⟩
    · rintro a ⟨haR, haL⟩
      rw [← hLE] at haL
      obtain ⟨y, hy, rfl⟩ := haL
      refine ⟨y, ⟨⟨y, hy⟩, ?_, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      show π y = 1
      rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
      exact haR
  have hcardA : Nat.card A = Nat.card q.ker := by
    rw [hA, Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.card_map_of_injective E.subtype_injective]
  have hA6 : Nat.card A ∣ 6 := by
    rw [hcardA]
    exact (card_ker_dvd_hopfMultiplier hπ hker.le hZ).trans hdvd
  have hA9 : Nat.card A ∣ 9 := by
    rw [← hR9]
    exact Subgroup.card_dvd_of_le (by rw [hAeq]; exact inf_le_left)
  have hA3 : Nat.card A ∣ 3 := by
    have := Nat.dvd_gcd hA6 hA9
    norm_num at this
    exact this
  have hAbot : A = ⊥ := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hA3 with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      obtain ⟨t, ht, a, ha, hta⟩ := hirr A (by rw [hAeq]; exact inf_le_left) h3
      apply hta
      rw [hAeq] at ha ⊢
      exact ⟨(mem_normalizer_iff.1 (hT ht) a).1 ha.1,
        conj_mem_commutator_centralizer (hT ht) ha.2⟩
  have hqinj : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have : ((k : C) : G) ∈ A := ⟨k, ⟨k, hk, rfl⟩, rfl⟩
    rw [hAbot, mem_bot] at this
    exact mem_bot.2 (Subtype.ext (Subtype.ext this))
  refine ⟨le_antisymm ?_ (sup_le hRC (Subgroup.commutator_le_self C)), by rw [← hAeq]; exact hAbot,
    ?_⟩
  · intro c hc
    obtain ⟨e, he, z, hz, hcz⟩ := exists_commutator_mul hπ hker.le ⟨c, hc⟩
    have hc' : c = (e : G) * (z : G) := congrArg Subtype.val hcz
    rw [hc', sup_comm]
    exact mul_mem_sup (by rw [← hLE]; exact ⟨e, he, rfl⟩) (mem_subgroupOf.1 hz)
  · exact ⟨(MulEquiv.subgroupCongr hLE).symm.trans
      ((Subgroup.equivMapOfInjective E C.subtype C.subtype_injective).symm.trans
        (MulEquiv.ofBijective q ⟨hqinj, surjective_comp_commutator hπ⟩))⟩

end Split

end CFSG.OddStandard.ONanRec.B2

module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Suz
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Suz
public import CFSG.Sporadic.SuzOddCore.SmallModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Sporadic.SuzOddCore
open scoped commutatorElement

namespace Sec3

section General

variable {H : Type} [Group H]

theorem conj_eq_of_mul_inv_mem_zpowers {x z b : H} (hx : orderOf x = 3) (hz : z * z = 1)
    (hxz : x * z = z * x) (h : b * z * b⁻¹ * z⁻¹ ∈ zpowers x) : b * z * b⁻¹ = z := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  set u := x ^ k with hu
  have hbz : b * z * b⁻¹ = u * z := by rw [hk]; group
  have huz : u * z = z * u := ((Commute.zpow_left (hxz : Commute x z) k)).eq
  have hu2 : u * u = 1 := by
    have h1 : (b * z * b⁻¹) * (b * z * b⁻¹) = 1 := by
      rw [show (b * z * b⁻¹) * (b * z * b⁻¹) = b * (z * z) * b⁻¹ by group, hz]
      group
    rw [hbz, show u * z * (u * z) = u * u * (z * z) by
      rw [show u * z * (u * z) = u * (z * u) * z by group, ← huz]; group, hz, mul_one] at h1
    exact h1
  have hu3 : u ^ 3 = 1 := by
    rw [hu, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hu1 : u = 1 := by
    rw [pow_succ, pow_two, hu2, one_mul] at hu3
    exact hu3
  rw [hbz, hu1, one_mul]

theorem isQ8Cube_map_iff {H' : Type} [Group H'] [Finite H] [Finite H'] (f : H →* H')
    (hf : Function.Injective f) {X : Subgroup H} : IsQ8Cube (X.map f) ↔ IsQ8Cube X := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  constructor
  · rintro ⟨hX, hc, hU⟩
    refine ⟨LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv e.symm hX, ?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv, hc]
    · rintro ⟨U, hUX, hUe, hU16⟩
      exact hU ⟨U.map f, map_mono hUX, isElemAbelian_map f hUe,
        by rw [card_map_of_injective hf, hU16]⟩
  · rintro ⟨hX, hc, hU⟩
    refine ⟨LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv e hX, ?_, ?_⟩
    · rw [← Nat.card_congr e.toEquiv, hc]
    · rintro ⟨U, hUX, hUe, hU16⟩
      have hUr : U ≤ f.range := hUX.trans (map_le_range f X)
      refine hU ⟨U.comap f, fun a ha => ?_, ?_, ?_⟩
      · obtain ⟨b, hb, hba⟩ := hUX ha
        rwa [← hf hba]
      · refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun a ha => hf ?_⟩
        · have := hUe.1.1.1 ⟨f a, a.2⟩ ⟨f b, b.2⟩
          simpa using congrArg Subtype.val this
        · rw [map_pow, map_one]
          exact hUe.2 _ ha
      · have h1 := Subgroup.card_map_of_injective (K := U.comap f) hf
        rw [map_comap_eq_self hUr] at h1
        rw [← h1, hU16]

theorem le_of_isPGroup_of_sup_eq_top {D N L : Subgroup H} [Finite H] [N.Normal]
    (hDN : D ⊔ N = ⊤) (hND : N ⊓ D = ⊥) (hNc : N ≤ center H) (hNo : Odd (Nat.card N))
    (hL : IsPGroup 2 L) : L ≤ D := by
  intro l hl
  obtain ⟨d, hd, n, hn, rfl⟩ := mem_sup_of_normal_right.mp (hDN ▸ mem_top l : l ∈ D ⊔ N)
  obtain ⟨m, hm⟩ := hL ⟨d * n, hl⟩
  have hm' : (d * n) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hdn : Commute d n := mem_center_iff.mp (hNc hn) d
  rw [hdn.mul_pow] at hm'
  have hnD : n ^ 2 ^ m ∈ N ⊓ D := by
    refine mem_inf.mpr ⟨pow_mem hn _, ?_⟩
    rw [eq_inv_of_mul_eq_one_right hm']
    exact inv_mem (pow_mem hd _)
  rw [hND, mem_bot] at hnD
  have hn1 : n = 1 := by
    have h1 : orderOf n ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hnD
    have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
    have hcop : Nat.Coprime (2 ^ m) (Nat.card N) :=
      Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hNo)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  rw [hn1, mul_one]
  exact hd

theorem mem_normalizer_map_subtype {K : Subgroup H} {L : Subgroup ↥K} (hL : L.Normal) {k : H}
    (hk : k ∈ K) : k ∈ normalizer (L.map K.subtype : Set H) := by
  rw [mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨k, hk⟩ * l * ⟨k, hk⟩⁻¹, hL.conj_mem l hl _, rfl⟩
  · rintro ⟨l, hl, hlg⟩
    have hlg' : (l : H) = k * g * k⁻¹ := hlg
    have hgK : g = (⟨k, hk⟩⁻¹ * l * ⟨k, hk⟩⁻¹⁻¹ : ↥K) := by
      simp only [coe_mul, coe_inv, inv_inv]
      rw [hlg']
      group
    exact ⟨_, hL.conj_mem l hl _, hgK.symm⟩

theorem mem_normalizer_of_normal {L : Subgroup H} (hL : L.Normal) (h : H) :
    h ∈ normalizer (L : Set H) := by
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => hL.conj_mem g hg h, fun hg => ?_⟩
  have := hL.conj_mem _ hg h⁻¹
  rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at this

end General

section Lift

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G}

theorem exists_lift_eq_Q (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y)
    {C : Type} [Group C] [Finite C] {Q₁ : Subgroup C} (hQ₁ : IsQ8Cube Q₁) (hQ₁n : Q₁.Normal)
    (hCcard : Nat.card C = 3317760)
    {K : Subgroup G} (hK : K = sec3B A₁ x ⊓ centralizer ({z} : Set G)) {π : ↥K →* C}
    (hπs : Function.Surjective π) (hπk : ∀ k, π k = 1 ↔ (k : G) ∈ zpowers x) :
    ∃ L : Subgroup ↥K, IsPGroup 2 L ∧ L.Normal ∧ (∀ l ∈ L, π l ∈ Q₁) ∧
      (∀ a : ↥K, π a ∈ Q₁ → ∃ l ∈ L, ∃ n ∈ π.ker, a = l * n) ∧ L.map K.subtype = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzT : z ∈ T := by
    have h := mem_zpowers z
    rw [← hS.T_center] at h
    exact (mem_inf.mp h).1
  have hzc : z ∈ centralizer (T : Set G) := by
    have h := mem_zpowers z
    rw [← hS.T_center] at h
    exact (mem_inf.mp h).2
  have hTK : T ≤ K := fun t ht => hK ▸ mem_inf.mpr ⟨hS.T_le ht,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hzc t ht)⟩
  have hKB : K ≤ sec3B A₁ x := hK ▸ inf_le_left
  have hzB : z ∈ sec3B A₁ x := hS.T_le hzT
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by rw [hS.B_center]; exact mem_zpowers x
  have hxB : x ∈ sec3B A₁ x := (mem_inf.mp hxZ).1
  have hxc : ∀ b ∈ sec3B A₁ x, b * x = x * b := fun b hb =>
    mem_centralizer_iff.mp (mem_inf.mp hxZ).2 b hb
  have hxK : x ∈ K := hK ▸ mem_inf.mpr ⟨hxB, mem_centralizer_singleton_iff.mpr (hxc z hzB).symm⟩
  have hx3 : orderOf x = 3 := hS.setting.order_x
  have hz2 : orderOf z = 2 := by
    have h1 := hS.q8.1.2.2.2
    rw [← card_centerIn, hS.Q_center, Nat.card_zpowers] at h1
    exact h1
  set N := π.ker with hNdef
  have hNx : ∀ k : ↥K, k ∈ N ↔ (k : G) ∈ zpowers x := fun k => MonoidHom.mem_ker.trans (hπk k)
  have hN3 : Nat.card N = 3 := by
    have hNeq : N = (zpowers x).subgroupOf K := by
      ext k
      rw [hNx, mem_subgroupOf]
    rw [hNeq, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hxK)).toEquiv, Nat.card_zpowers,
      hx3]
  have hNo : Odd (Nat.card N) := by rw [hN3]; decide
  have hNc : N ≤ center ↥K := by
    intro n hn
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp ((hNx n).mp hn)
    change (k : G) * (n : G) = (n : G) * (k : G)
    rw [← hj]
    exact ((Commute.zpow_right (hxc k (hKB k.2) : Commute (k : G) x) j)).eq
  set θ := QuotientGroup.quotientKerEquivOfSurjective π hπs with hθdef
  have hθ : ∀ k : ↥K, θ (QuotientGroup.mk' N k) = π k := fun k => rfl
  set Qb : Subgroup (↥K ⧸ N) := Q₁.map θ.symm.toMonoidHom with hQbdef
  have hQb8 : IsQ8Cube Qb := (isQ8Cube_map_iff θ.symm.toMonoidHom θ.symm.injective).mpr hQ₁
  have hQb2 : IsPGroup 2 Qb := hQb8.1.1
  have hQbn : Qb.Normal := hQ₁n.map θ.symm.toMonoidHom θ.symm.surjective
  have hmemQb : ∀ k : ↥K, QuotientGroup.mk' N k ∈ Qb ↔ π k ∈ Q₁ := fun k => by
    rw [hQbdef, mem_map_equiv, MulEquiv.symm_symm, hθ]
  set L := twoLift N Qb with hLdef
  have hL2 : IsPGroup 2 L := isPGroup_twoLift hNc hNo hQb2
  have hLn : L.Normal := ⟨fun l hl k => (mem_normalizer_iff.mp (mem_normalizer_twoLift hNc hNo
    hQb2 (mem_normalizer_of_normal hQbn _)) l).mp hl⟩
  have hLQ : ∀ l ∈ L, π l ∈ Q₁ := fun l hl =>
    (hmemQb l).mp (mk_mem_of_mem_twoLift hNc hNo hQb2 hl)
  have hQL : ∀ a : ↥K, π a ∈ Q₁ → ∃ l ∈ L, ∃ n ∈ N, a = l * n := by
    intro a ha
    have ha' : QuotientGroup.mk' N a ∈ Qb := (hmemQb a).mpr ha
    obtain ⟨l, hl, hla⟩ := exists_mem_twoLift hNc hNo hQb2 ha'
    refine ⟨l, hl, l⁻¹ * a, QuotientGroup.eq.mp hla, by group⟩
  set Q' := L.map K.subtype with hQ'def
  have hQ'8 : IsQ8Cube Q' := isQ8Cube_twoLift hNc hNo hQb8
  have hKQ' : K ≤ normalizer (Q' : Set G) := fun k hk => mem_normalizer_map_subtype hLn hk
  have hcardK : Nat.card K = 2 ^ 13 * 1215 := by
    have h := card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top.mpr hπs, card_top, hCcard, ← hNdef, hN3] at h
    rw [← h]
    norm_num
  have hTsyl : IsSylowOf 2 T K := by
    refine isSylowOf_of_card hTK ?_
    rw [hS.T_card, hcardK, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hQ'T : Q' ≤ T := by
    have h2 : IsPGroup 2 ↥(Q' ⊔ T) := (hL2.map K.subtype).to_sup_of_normal_left' hS.T_two
      (hTK.trans hKQ')
    have h := hTsyl.eq_of_le le_sup_right (sup_le (map_subtype_le L) hTK) h2
    exact le_sup_left.trans h.le
  have hyK : y ∈ K := by
    refine hK ▸ mem_inf.mpr ⟨(mem_inf.mp hS.y_mem).1, mem_centralizer_singleton_iff.mpr ?_⟩
    have h := Sec2.mem_normalizer_centerIn hS.y_Q
    rw [hS.Q_center] at h
    have h1 := Sec2.conj_eq_of_mem_normalizer_zpowers hz2 h
    calc y * z = y * z * y⁻¹ * y := by group
      _ = z * y := by rw [h1]
  exact ⟨L, hL2, hLn, hLQ, hQL, hS.Q_unique Q' hQ'8 hQ'T (hKQ' hyK)⟩

theorem sec3B0_of_hom
    (hts : SuzB0.noTS3 = true) (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y)
    {C : Type} [Group C] [Finite C] {Q₁ : Subgroup C}
    {ρ : C →* ((Fin 6 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))} (hQ₁ : IsQ8Cube Q₁)
    (hQ₁n : Q₁.Normal) (hρr : ρ.range = timmesfeldOmega qMinus) (hρk : ρ.ker = Q₁)
    (hCp : commutator C = ⊤) (hCcard : Nat.card C = 3317760)
    {K : Subgroup G} (hK : K = sec3B A₁ x ⊓ centralizer ({z} : Set G)) {π : ↥K →* C}
    (hπs : Function.Surjective π) (hπk : ∀ k, π k = 1 ↔ (k : G) ∈ zpowers x) :
    Q ≤ B₀ ∧ B₀ ≤ normalizer (Q : Set G) ∧
      ∃ φ : ↥B₀ →* ↥(timmesfeldOmega qMinus), Function.Surjective φ ∧ φ.ker = Q.subgroupOf B₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzT : z ∈ T := by
    have h := mem_zpowers z
    rw [← hS.T_center] at h
    exact (mem_inf.mp h).1
  have hKB : K ≤ sec3B A₁ x := hK ▸ inf_le_left
  have hzB : z ∈ sec3B A₁ x := hS.T_le hzT
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by rw [hS.B_center]; exact mem_zpowers x
  have hxB : x ∈ sec3B A₁ x := (mem_inf.mp hxZ).1
  have hxc : ∀ b ∈ sec3B A₁ x, b * x = x * b := fun b hb =>
    mem_centralizer_iff.mp (mem_inf.mp hxZ).2 b hb
  have hxK : x ∈ K := hK ▸ mem_inf.mpr ⟨hxB, mem_centralizer_singleton_iff.mpr (hxc z hzB).symm⟩
  have hx3 : orderOf x = 3 := hS.setting.order_x
  set N := π.ker with hNdef
  have hNx : ∀ k : ↥K, k ∈ N ↔ (k : G) ∈ zpowers x := fun k => MonoidHom.mem_ker.trans (hπk k)
  have hN3 : Nat.card N = 3 := by
    have hNeq : N = (zpowers x).subgroupOf K := by
      ext k
      rw [hNx, mem_subgroupOf]
    rw [hNeq, Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hxK)).toEquiv, Nat.card_zpowers,
      hx3]
  have hNo : Odd (Nat.card N) := by rw [hN3]; decide
  have hNc : N ≤ center ↥K := by
    intro n hn
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp ((hNx n).mp hn)
    change (k : G) * (n : G) = (n : G) * (k : G)
    rw [← hj]
    exact ((Commute.zpow_right (hxc k (hKB k.2) : Commute (k : G) x) j)).eq
  obtain ⟨L, hL2, hLn, hLQ, hQL, hQ'Q⟩ := exists_lift_eq_Q hS hQ₁ hQ₁n hCcard hK hπs hπk
  have hKQ : K ≤ normalizer (Q : Set G) := fun k hk => by
    rw [← hQ'Q]
    exact mem_normalizer_map_subtype hLn hk
  have hρmem : ∀ c, ρ c ∈ timmesfeldOmega qMinus := fun c => hρr ▸ ⟨c, rfl⟩
  set ρ' := ρ.codRestrict (timmesfeldOmega qMinus) hρmem with hρ'def
  have hρ's : Function.Surjective ρ' := by
    rintro ⟨ω, hω⟩
    rw [← hρr] at hω
    obtain ⟨c, rfl⟩ := hω
    exact ⟨c, rfl⟩
  have hρ'k : ∀ c, ρ' c = 1 ↔ c ∈ Q₁ := fun c => by
    rw [← hρk, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  set φ₀ := ρ'.comp π with hφ₀def
  have hφ₀s : Function.Surjective φ₀ := hρ's.comp hπs
  have hφ₀k : ∀ k, φ₀ k = 1 ↔ π k ∈ Q₁ := fun k => hρ'k (π k)
  set D := commutator ↥K with hDdef
  have hmap : D.map π = (⊤ : Subgroup ↥K).map π := by
    rw [hDdef, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hπs, ← _root_.commutator_def, hCp]
  have hDN : D ⊔ N = ⊤ := by
    have h := map_eq_map_iff.mp hmap
    rwa [top_sup_eq] at h
  have hND : N ⊓ D = ⊥ := by
    by_contra hne
    have hNle : N ≤ D := by
      have hdvd : Nat.card ↥(N ⊓ D) ∣ 3 := hN3 ▸ card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd ((card_eq_one).mp h1) hne
      · have := eq_of_le_of_card_ge (inf_le_left : N ⊓ D ≤ N) (by rw [h3, hN3])
        rw [← this]
        exact inf_le_right
    have hDtop : D = ⊤ := by rw [← hDN, sup_eq_left.mpr hNle]
    have hEp : commutator (↥K ⧸ L) = ⊤ := by
      have h1 := map_commutator (⊤ : Subgroup ↥K) ⊤ (QuotientGroup.mk' L)
      rw [← _root_.commutator_def, ← hDdef, hDtop, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective L)] at h1
      rw [_root_.commutator_def]
      exact h1.symm
    have : Group.IsPerfect (↥K ⧸ L) := Group.isPerfect_def.mpr hEp
    have hLφ : L ≤ φ₀.ker := fun l hl => (hφ₀k l).mpr (hLQ l hl)
    set p := QuotientGroup.lift L φ₀ hLφ with hpdef
    have hps : Function.Surjective p := QuotientGroup.lift_surjective_of_surjective L φ₀ hφ₀s hLφ
    have hpC : p.ker ≤ center (↥K ⧸ L) := by
      intro e he
      induction e using QuotientGroup.induction_on with
      | H a =>
        have ha : π a ∈ Q₁ := (hφ₀k a).mp he
        obtain ⟨l, hl, n, hn, rfl⟩ := hQL a ha
        rw [mem_center_iff]
        intro w
        induction w using QuotientGroup.induction_on with
        | H b =>
          have hl1 : (QuotientGroup.mk l : ↥K ⧸ L) = 1 := (QuotientGroup.eq_one_iff l).mpr hl
          rw [QuotientGroup.mk_mul, hl1, one_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
            mem_center_iff.mp (hNc hn) b]
    have hNp : N.map (QuotientGroup.mk' L) ≤ p.ker := by
      rintro _ ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker]
      change φ₀ n = 1
      rw [hφ₀k, MonoidHom.mem_ker.mp hn]
      exact Q₁.one_mem
    have hNcard : Nat.card (N.map (QuotientGroup.mk' L)) = 3 := by
      have hinj : Function.Injective ((QuotientGroup.mk' L).comp N.subtype) := by
        intro a b hab
        have h1 : (a : ↥K)⁻¹ * b ∈ L := QuotientGroup.eq.mp hab
        have h2 : (a : ↥K)⁻¹ * b ∈ L ⊓ N := mem_inf.mpr ⟨h1, N.mul_mem (N.inv_mem a.2) b.2⟩
        rw [AS81.inf_eq_bot_of_isPGroup hL2 hNo, mem_bot, inv_mul_eq_one] at h2
        exact Subtype.ext h2
      have h1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      rwa [MonoidHom.range_comp, range_subtype, hN3, eq_comm] at h1
    have h3 : 3 ∣ Nat.card p.ker := hNcard ▸ card_dvd_of_le hNp
    have h2 := SuzB0.card_ker_dvd_two hts p hps hpC
    have := Nat.le_of_dvd (by norm_num) (h3.trans h2)
    omega
  have hLD : L ≤ D := le_of_isPGroup_of_sup_eq_top hDN hND hNc hNo hL2
  have hB₀D : B₀ = D.map K.subtype := by
    rw [hS.B₀_eq, ← hK, hDdef, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      range_subtype]
  have hB₀K : B₀ ≤ K := hB₀D ▸ map_subtype_le D
  refine ⟨?_, hB₀K.trans hKQ, ?_⟩
  · rw [← hQ'Q, hB₀D]
    exact map_mono hLD
  · refine ⟨φ₀.comp (inclusion hB₀K), ?_, ?_⟩
    · intro ω
      obtain ⟨c, rfl⟩ := hρ's ω
      have hc : c ∈ D.map π := by
        rw [hmap, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπs]
        exact mem_top c
      obtain ⟨d, hd, rfl⟩ := hc
      exact ⟨⟨(d : G), hB₀D ▸ mem_map_of_mem K.subtype hd⟩, rfl⟩
    · ext b
      rw [MonoidHom.mem_ker, mem_subgroupOf, ← hQ'Q]
      constructor
      · intro hb
        have hbQ := (hφ₀k (inclusion hB₀K b)).mp hb
        obtain ⟨l, hl, n, hn, hln⟩ := hQL _ hbQ
        have hbD : inclusion hB₀K b ∈ D := by
          have h : (b : G) ∈ D.map K.subtype := hB₀D ▸ b.2
          obtain ⟨d, hd, hdb⟩ := h
          have : inclusion hB₀K b = d := Subtype.ext hdb.symm
          rw [this]
          exact hd
        have hnD : n ∈ N ⊓ D := by
          refine mem_inf.mpr ⟨hn, ?_⟩
          have : n = l⁻¹ * inclusion hB₀K b := by rw [hln]; group
          rw [this]
          exact D.mul_mem (D.inv_mem (hLD hl)) hbD
        rw [hND, mem_bot] at hnD
        rw [hnD, mul_one] at hln
        exact ⟨l, hl, (congrArg Subtype.val hln).symm⟩
      · rintro ⟨l, hl, hlb⟩
        have : inclusion hB₀K b = l := Subtype.ext hlb.symm
        change φ₀ (inclusion hB₀K b) = 1
        rw [this, hφ₀k]
        exact hLQ l hl

theorem exists_hom_invE
    (hS : Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y)
    (e₀ : ↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x) ≃* CFSG.Blueprint.NativeSporadic.Carrier .Suz) :
    ∃ c ∈ suzT, ∃ π : ↥(sec3B A₁ x ⊓ centralizer ({z} : Set G)) →* ↥(invE 1),
      Function.Surjective π ∧ (∀ k, π k = 1 ↔ (k : G) ∈ zpowers x) ∧
      ∀ k, (π k : Equiv.Perm (Fin 1782)) = c⁻¹ * (suzEquivM (e₀ (QuotientGroup.mk
        (inclusion (inf_le_left : sec3B A₁ x ⊓ centralizer ({z} : Set G) ≤ sec3B A₁ x) k))) :
          Equiv.Perm (Fin 1782)) * c := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzT : z ∈ T := by
    have h := mem_zpowers z
    rw [← hS.T_center] at h
    exact (mem_inf.mp h).1
  have hzc : z ∈ centralizer (T : Set G) := by
    have h := mem_zpowers z
    rw [← hS.T_center] at h
    exact (mem_inf.mp h).2
  have hzB : z ∈ sec3B A₁ x := hS.T_le hzT
  have hxZ : x ∈ centerIn (sec3B A₁ x) := by rw [hS.B_center]; exact mem_zpowers x
  have hxc : ∀ b ∈ sec3B A₁ x, b * x = x * b := fun b hb =>
    mem_centralizer_iff.mp (mem_inf.mp hxZ).2 b hb
  have hx3 : orderOf x = 3 := hS.setting.order_x
  have hz2 : orderOf z = 2 := by
    have h1 := hS.q8.1.2.2.2
    rw [← card_centerIn, hS.Q_center, Nat.card_zpowers] at h1
    exact h1
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  set e : ↥(sec3B A₁ x) ⧸ center ↥(sec3B A₁ x) ≃* ↥suzM := e₀.trans suzEquivM with hedef
  set π₀ : ↥(sec3B A₁ x) →* Equiv.Perm (Fin 1782) :=
    suzM.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' _)) with hπ₀def
  have hπ₀M : ∀ b, π₀ b ∈ suzM := fun b => (e _).2
  have hπ₀s : ∀ m ∈ suzM, ∃ b, π₀ b = m := by
    intro m hm
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (center ↥(sec3B A₁ x)) (e.symm ⟨m, hm⟩)
    refine ⟨b, ?_⟩
    change ((e (QuotientGroup.mk' _ b) : ↥suzM) : Equiv.Perm (Fin 1782)) = m
    rw [hb, MulEquiv.apply_symm_apply]
  have hcen : ∀ b : ↥(sec3B A₁ x), b ∈ center ↥(sec3B A₁ x) ↔ (b : G) ∈ zpowers x := by
    intro b
    rw [← hS.B_center, ← map_center_eq_centerIn]
    exact ⟨fun h => ⟨b, h, rfl⟩, fun ⟨c, hc, hcb⟩ => (Subtype.ext hcb : c = b) ▸ hc⟩
  have hπ₀k : ∀ b, π₀ b = 1 ↔ (b : G) ∈ zpowers x := by
    intro b
    rw [← hcen, ← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h1 : e (QuotientGroup.mk' _ b) = 1 := Subtype.ext h
      rwa [map_eq_one_iff e e.injective] at h1
    · intro h
      change ((e (QuotientGroup.mk' _ b) : ↥suzM) : Equiv.Perm (Fin 1782)) = 1
      rw [QuotientGroup.mk'_apply, h, map_one]
      rfl
  have hcard3 : Nat.card ↥(center ↥(sec3B A₁ x)) = 3 := by
    rw [← card_centerIn, hS.B_center, Nat.card_zpowers, hx3]
  have hodd : Odd (Nat.card ↥(center ↥(sec3B A₁ x))) := by rw [hcard3]; decide
  set z' : ↥(sec3B A₁ x) := ⟨z, hzB⟩ with hz'
  have hzbar2 : orderOf (π₀ z') = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two]
      have : z' * z' = 1 := Subtype.ext hzz
      rw [this, map_one]
    · intro h
      have h1 := (hπ₀k z').mp h
      have h2 := orderOf_dvd_of_mem_zpowers h1
      change orderOf z ∣ orderOf x at h2
      rw [hz2, hx3] at h2
      exact absurd h2 (by norm_num)
  have hT2 : IsPGroup 2 (T.subgroupOf (sec3B A₁ x)) := hS.T_two.comap_subtype
  have hTcard : Nat.card ((T.subgroupOf (sec3B A₁ x)).map π₀) = 2 ^ 13 := by
    have h1 : (T.subgroupOf (sec3B A₁ x)).map π₀ =
        ((T.subgroupOf (sec3B A₁ x)).map (QuotientGroup.mk' _)).map
          (suzM.subtype.comp e.toMonoidHom) := by
      rw [map_map]
      rfl
    have hinj : Function.Injective (suzM.subtype.comp e.toMonoidHom) := fun a b h =>
      e.injective (Subtype.ext h)
    rw [h1, card_map_of_injective hinj,
      AS81.card_map_mk'_of_le hT2 hodd le_rfl,
      Nat.card_congr (subgroupOfEquivOfLe hS.T_le).toEquiv, hS.T_card]
  have hTle : (T.subgroupOf (sec3B A₁ x)).map π₀ ≤
      suzM ⊓ centralizer ({π₀ z'} : Set (Equiv.Perm (Fin 1782))) := by
    rintro _ ⟨t, ht, rfl⟩
    refine mem_inf.mpr ⟨hπ₀M t, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_iff.mp hzc _ (mem_subgroupOf.mp ht))
  have hdvd : 2 ^ 13 ∣ Nat.card (suzM ⊓ centralizer ({π₀ z'} : Set (Equiv.Perm (Fin 1782))) :
      Subgroup (Equiv.Perm (Fin 1782))) := hTcard ▸ card_dvd_of_le hTle
  obtain ⟨c, hc, hct⟩ := suzM_involution_class (hπ₀M z') hzbar2
  have hcz : c * suzInv 1 * c⁻¹ = π₀ z' := by
    rcases hct with h0 | h1
    · exfalso
      rw [← h0, card_inf_centralizer_conj_of_mem_normalizer
        (suz_le_normalizer le_rfl suzM_le_suzT hc), card_suzM_inf_centralizer (by norm_num)]
        at hdvd
      exact absurd hdvd (by decide)
    · exact h1
  have hKB : sec3B A₁ x ⊓ centralizer ({z} : Set G) ≤ sec3B A₁ x := inf_le_left
  set π' : ↥(sec3B A₁ x ⊓ centralizer ({z} : Set G)) →* Equiv.Perm (Fin 1782) :=
    (MulAut.conj c⁻¹).toMonoidHom.comp (π₀.comp (inclusion hKB)) with hπ'def
  have hπ' : ∀ k, π' k = c⁻¹ * π₀ (inclusion hKB k) * c := fun k => by
    simp [hπ'def]
  have hcomm : ∀ m : Equiv.Perm (Fin 1782), m * π₀ z' = π₀ z' * m →
      (c⁻¹ * m * c) * suzInv 1 = suzInv 1 * (c⁻¹ * m * c) := by
    intro m hm
    have ht : suzInv 1 = c⁻¹ * π₀ z' * c := by rw [← hcz]; group
    rw [ht]
    calc c⁻¹ * m * c * (c⁻¹ * π₀ z' * c) = c⁻¹ * (m * π₀ z') * c := by group
      _ = c⁻¹ * (π₀ z' * m) * c := by rw [hm]
      _ = c⁻¹ * π₀ z' * c * (c⁻¹ * m * c) := by group
  have hmem : ∀ k, π' k ∈ invE 1 := by
    intro k
    rw [invE_eq_centM (by norm_num), hπ' k]
    refine ⟨mem_centralizer_singleton_iff.mpr (hcomm _ ?_), ?_⟩
    · rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp k.2).2)
    · have := (suzM_conj_iff (suzT.inv_mem hc) (π₀ (inclusion hKB k))).mp (hπ₀M _)
      rwa [inv_inv] at this
  refine ⟨c, hc, π'.codRestrict (invE 1) hmem, ?_, ?_, fun k => hπ' k⟩
  ·
    intro ⟨m, hm⟩
    rw [invE_eq_centM (by norm_num)] at hm
    obtain ⟨hmc, hmM⟩ := mem_inf.mp hm
    obtain ⟨b, hb⟩ := hπ₀s (c * m * c⁻¹) ((suzM_conj_iff hc m).mp hmM)
    have hbz : π₀ b * π₀ z' = π₀ z' * π₀ b := by
      rw [hb, ← hcz]
      have h1 := mem_centralizer_singleton_iff.mp hmc
      calc c * m * c⁻¹ * (c * suzInv 1 * c⁻¹) = c * (m * suzInv 1) * c⁻¹ := by group
        _ = c * (suzInv 1 * m) * c⁻¹ := by rw [h1]
        _ = c * suzInv 1 * c⁻¹ * (c * m * c⁻¹) := by group
    have hbz' : (b : G) * z * (b : G)⁻¹ = z := by
      refine conj_eq_of_mul_inv_mem_zpowers hx3 hzz (hxc z hzB).symm ?_
      have h1 : π₀ (b * z' * b⁻¹ * z'⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hbz]
        group
      exact (hπ₀k _).mp h1
    have hbK : (b : G) ∈ sec3B A₁ x ⊓ centralizer ({z} : Set G) := by
      refine mem_inf.mpr ⟨b.2, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (b : G) * z = (b : G) * z * (b : G)⁻¹ * b := by group
        _ = z * b := by rw [hbz']
    refine ⟨⟨b, hbK⟩, Subtype.ext ?_⟩
    change π' ⟨b, hbK⟩ = m
    rw [hπ' ⟨b, hbK⟩, show inclusion hKB ⟨(b : G), hbK⟩ = b from rfl, hb]
    group
  · intro k
    rw [show (k : G) = ((inclusion hKB k : ↥(sec3B A₁ x)) : G) from rfl, ← hπ₀k]
    constructor
    · intro h
      have h1 : π' k = 1 := congrArg Subtype.val h
      rw [hπ' k] at h1
      have h2 : π₀ (inclusion hKB k) = c * 1 * c⁻¹ := by rw [← h1]; group
      rw [h2]
      group
    · intro h
      apply Subtype.ext
      change π' k = 1
      rw [hπ' k, h]
      group

end Lift

end Sec3

theorem sec3B0_proof :
    ∀ (G : Type) [Group G] [Finite G] (A A₁ R : Subgroup G) (g : G) (E F : Subgroup G) (x : G)
      (Zs P T Q B₀ : Subgroup G) (z y : G), Sec3Suz G A A₁ R g E F x Zs P T Q B₀ z y →
        Q ≤ B₀ ∧ B₀ ≤ normalizer (Q : Set G) ∧
        ∃ φ : ↥B₀ →* ↥(timmesfeldOmega qMinus), Function.Surjective φ ∧ φ.ker = Q.subgroupOf B₀ := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y hS
  obtain ⟨e₀⟩ := hS.B_suz
  obtain ⟨-, -, π, hπs, hπk, -⟩ := Sec3.exists_hom_invE hS e₀
  obtain ⟨Q₁, ρ, hQ₁8, hQ₁C, hCN, hρr, hρk, hCp⟩ := SuzB0.suzB0_model
  refine Sec3.sec3B0_of_hom SuzB0.b0_parts.2.2.2.2.2.2 hS (Q₁ := Q₁.subgroupOf (invE 1)) ?_ ?_
    hρr hρk hCp ?_ rfl hπs hπk
  · rw [← Sec3.isQ8Cube_map_iff (invE 1).subtype (invE 1).subtype_injective, subgroupOf_map_subtype,
      inf_eq_left.mpr hQ₁C]
    exact hQ₁8
  · exact ⟨fun a ha c => mem_subgroupOf.mpr
      ((mem_normalizer_iff.mp (hCN c.2) a).mp (mem_subgroupOf.mp ha))⟩
  · rw [card_invE (by norm_num)]
    rfl

end CFSG.ComponentClassification.AS81

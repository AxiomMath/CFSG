module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs96
public import CFSG.LargeExtraspecial.Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Subgroup CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

theorem card_ker_comp_subtype_dvd {H M : Type*} [Group H] [Finite H] [Group M] (π : H →* M)
    (A : Subgroup H) : Nat.card (π.comp A.subtype).ker ∣ Nat.card π.ker := by
  set K := (π.comp A.subtype).ker with hK
  have h1 : K.map A.subtype ≤ π.ker := by
    rintro _ ⟨k, hk, rfl⟩
    exact hk
  have h2 : Nat.card (K.map A.subtype) = Nat.card K :=
    Subgroup.card_map_of_injective A.subtype_injective
  rw [← h2]
  exact Subgroup.card_dvd_of_le h1

theorem injective_comp_subtype {H M : Type*} [Group H] [Finite H] [Group M] {p : ℕ}
    (hp : p.Prime) (π : H →* M) (hker : ¬ p ∣ Nat.card π.ker) {W : Subgroup H}
    (hW : IsPGroup p W) : Function.Injective (π.comp W.subtype) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  set K := (π.comp W.subtype).ker with hK
  have hKp : IsPGroup p K := hW.to_subgroup K
  have hKdvd : Nat.card K ∣ Nat.card π.ker := card_ker_comp_subtype_dvd π W
  obtain ⟨n, hn⟩ := hKp.exists_card_eq
  by_contra hne
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hn
    exact (Subgroup.card_eq_one).1 hn
  apply hker
  refine (dvd_pow_self p hn0).trans ?_
  rw [← hn]
  exact hKdvd

theorem exists_pSubgroup_lift {H M : Type*} [Group H] [Finite H] [Group M] {p : ℕ}
    (hp : p.Prime) (π : H →* M) (hker : ¬ p ∣ Nat.card π.ker) {E : Subgroup M}
    (hE : IsPGroup p E) (hEπ : E ≤ π.range) :
    ∃ W : Subgroup H, IsPGroup p W ∧ W.map π = E ∧ Function.Injective (π.comp W.subtype) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let P : Subgroup H := E.comap π
  let f : ↥P →* ↥E := π.subgroupComap E
  have hf : Function.Surjective f := by
    intro e
    obtain ⟨h, hh⟩ := hEπ e.2
    exact ⟨⟨h, by simp [P, Subgroup.mem_comap, hh]⟩, Subtype.ext hh⟩
  haveI : Finite E := Finite.of_surjective f hf
  have htop : IsPGroup p (⊤ : Subgroup ↥E) := hE.of_equiv Subgroup.topEquiv.symm
  obtain ⟨R⟩ : Nonempty (Sylow p ↥E) := inferInstance
  have hR : (R : Subgroup ↥E) = ⊤ := (R.3 htop le_top).symm
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hf p R
  have hQf : (Q : Subgroup ↥P).map f = ⊤ := by
    have := congrArg (fun S : Sylow p ↥E => (S : Subgroup ↥E)) hQ
    simpa [Sylow.coe_mapSurjective, hR] using this
  have hW : IsPGroup p ((Q : Subgroup ↥P).map P.subtype) := Q.2.map P.subtype
  have hmap : ((Q : Subgroup ↥P).map P.subtype).map π = E := by
    have h1 : ((Q : Subgroup ↥P).map P.subtype).map π =
        ((Q : Subgroup ↥P).map f).map E.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hQf, Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨(Q : Subgroup ↥P).map P.subtype, hW, hmap, injective_comp_subtype hp π hker hW⟩

theorem card_eq_of_injective_comp_subtype {H M : Type*} [Group H] [Group M] (π : H →* M)
    {W : Subgroup H} (hinj : Function.Injective (π.comp W.subtype)) :
    Nat.card W = Nat.card (W.map π) := by
  have hrange : (π.comp W.subtype).range = W.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv

@[expose] noncomputable def mulEquivMap {H M : Type*} [Group H] [Group M] (π : H →* M)
    {W : Subgroup H} (hinj : Function.Injective (π.comp W.subtype)) : W ≃* W.map π :=
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]))

theorem mulEquivMap_apply {H M : Type*} [Group H] [Group M] (π : H →* M) {W : Subgroup H}
    (hinj : Function.Injective (π.comp W.subtype)) (w : W) :
    ((mulEquivMap π hinj w : W.map π) : M) = π w := rfl

theorem isElemAbelian_of_injective_comp_subtype {H M : Type*} [Group H] [Group M] {p : ℕ}
    (π : H →* M) {W : Subgroup H} (hinj : Function.Injective (π.comp W.subtype))
    (h : IsElemAbelian p (W.map π)) : IsElemAbelian p W := by
  have := h.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply hinj
    show π (a * b) = π (b * a)
    rw [map_mul, map_mul]
    exact congrArg Subtype.val
      (show (⟨π a, Subgroup.mem_map_of_mem π a.2⟩ : W.map π) * ⟨π b, Subgroup.mem_map_of_mem π b.2⟩ =
        ⟨π b, Subgroup.mem_map_of_mem π b.2⟩ * ⟨π a, Subgroup.mem_map_of_mem π a.2⟩ from
        mul_comm' _ _)
  · have h1 : (π x) ^ p = 1 := h.2 (π x) (Subgroup.mem_map_of_mem π hx)
    have h2 : (⟨x ^ p, W.pow_mem hx p⟩ : W) = 1 := by
      apply hinj
      show π (x ^ p) = π 1
      rw [map_pow, h1, map_one]
    exact congrArg Subtype.val h2

theorem isElemAbelian_range {A M : Type*} [CommGroup A] [Group M] {p : ℕ} (φ : A →* M)
    (hp : ∀ a : A, a ^ p = 1) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : M) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [← map_pow, hp a, map_one]

theorem card_range_eq_of_injective {A M : Type*} [Group A] [Group M] (φ : A →* M)
    (hφ : Function.Injective φ) : Nat.card φ.range = Nat.card A :=
  (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm

theorem mem_normalizer_zpowers_of_commute {M : Type*} [Group M] {y s : M} (h : Commute y s) :
    y ∈ Subgroup.normalizer (Subgroup.zpowers s : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : y * s ^ k = s ^ k * y := (Commute.zpow_right h k).eq
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) k
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hc : y * s ^ k = s ^ k * y := (Commute.zpow_right h k).eq
    have h1 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    rw [← hk] at h1
    have h2 : y⁻¹ * s ^ k * y = s ^ k := by
      calc y⁻¹ * s ^ k * y = y⁻¹ * (s ^ k * y) := by rw [mul_assoc]
        _ = y⁻¹ * (y * s ^ k) := by rw [hc]
        _ = s ^ k := by group
    rw [h2] at h1
    rw [← h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) k

theorem isPGroup_zpowers_of_pow_eq_one {H : Type*} [Group H] {q : ℕ} {z : H} (hz : z ^ q = 1) :
    IsPGroup q (Subgroup.zpowers z) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.2
  rw [pow_one, Subgroup.coe_pow, ← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hz, one_zpow]
  rfl

theorem exists_mem_centralizer_lift {H M : Type*} [Group H] [Finite H] [Group M] {q : ℕ}
    (hq : q.Prime) (π : H →* M) (hker : ¬ q ∣ Nat.card π.ker) {z : H} (hz : z ^ q = 1) {m : M}
    (hm : m ∈ π.range) (hc : m * π z = π z * m) :
    ∃ h : H, h * z = z * h ∧ π h = m := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨h₀, hh₀⟩ := hm
  let P : Subgroup H := Subgroup.zpowers z
  have hP : IsPGroup q P := isPGroup_zpowers_of_pow_eq_one hz
  have hcomm : ∀ g ∈ P, π g * m = m * π g := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [map_zpow]
    exact ((Commute.zpow_right (show Commute m (π z) from hc) k).eq).symm
  let α := {x : H // π x = m}
  have hmem : ∀ (g : H), g ∈ P → ∀ x : α, π (g * x.1 * g⁻¹) = m := by
    intro g hg x
    rw [map_mul, map_mul, map_inv, x.2, hcomm g hg, mul_assoc, mul_inv_cancel, mul_one]
  letI act : MulAction P α :=
    { smul := fun g x => ⟨(g : H) * x.1 * (g : H)⁻¹, hmem g g.2 x⟩
      one_smul := fun x => Subtype.ext (show ((1 : P) : H) * x.1 * ((1 : P) : H)⁻¹ = x.1 by simp)
      mul_smul := fun g h x => Subtype.ext (show ((g * h : P) : H) * x.1 * ((g * h : P) : H)⁻¹ =
          (g : H) * ((h : H) * x.1 * (h : H)⁻¹) * (g : H)⁻¹ by
        simp only [Subgroup.coe_mul]
        group) }
  have hcard : ¬ q ∣ Nat.card α := by
    have : Nat.card α = Nat.card π.ker := by
      refine Nat.card_congr
        { toFun := fun x => ⟨h₀⁻¹ * x.1, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hh₀, x.2, inv_mul_cancel]⟩
          invFun := fun k => ⟨h₀ * k.1, by rw [map_mul, k.2 |> MonoidHom.mem_ker.1, mul_one, hh₀]⟩
          left_inv := fun x => Subtype.ext (by simp)
          right_inv := fun k => Subtype.ext (by simp) }
    rw [this]
    exact hker
  obtain ⟨x, hx⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α hcard
  have hxz : x.1 * z = z * x.1 := by
    have h := congrArg Subtype.val (hx ⟨z, Subgroup.mem_zpowers z⟩)
    change z * x.1 * z⁻¹ = x.1 at h
    calc x.1 * z = (z * x.1 * z⁻¹) * z := by rw [h]
      _ = z * x.1 := by group
  exact ⟨x.1, hxz, x.2⟩

theorem exists_pSubgroup_lift_centralizer {H M : Type*} [Group H] [Finite H] [Group M] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (π : H →* M) (hkp : ¬ p ∣ Nat.card π.ker)
    (hkq : ¬ q ∣ Nat.card π.ker) {z : H} (hz : z ^ q = 1) {E : Subgroup M} (hE : IsPGroup p E)
    (hEπ : E ≤ π.range) (hEc : E ≤ Subgroup.centralizer {π z}) :
    ∃ W : Subgroup H, IsPGroup p W ∧ W ≤ Subgroup.centralizer {z} ∧ W.map π = E ∧
      Function.Injective (π.comp W.subtype) := by
  let A : Subgroup H := E.comap π ⊓ Subgroup.centralizer {z}
  let πA : ↥A →* M := π.comp A.subtype
  have hEA : E ≤ πA.range := by
    intro e he
    obtain ⟨h₀, hh₀⟩ := hEπ he
    have hcm : e * π z = π z * e := by
      have := hEc he
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    obtain ⟨h, hhz, hhe⟩ := exists_mem_centralizer_lift hq π hkq hz ⟨h₀, hh₀⟩ hcm
    have hA : h ∈ A := Subgroup.mem_inf.2 ⟨by rw [Subgroup.mem_comap, hhe]; exact he,
      Subgroup.mem_centralizer_singleton_iff.2 hhz⟩
    exact ⟨⟨h, hA⟩, hhe⟩
  have hkA : ¬ p ∣ Nat.card πA.ker := fun h => hkp (h.trans (card_ker_comp_subtype_dvd π A))
  obtain ⟨W', hW'p, hW'map, -⟩ := exists_pSubgroup_lift hp πA hkA hE hEA
  have hWp : IsPGroup p (W'.map A.subtype) := hW'p.map A.subtype
  refine ⟨W'.map A.subtype, hWp, ?_, ?_, injective_comp_subtype hp π hkp hWp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact (Subgroup.mem_inf.1 w.2).2
  · rw [Subgroup.map_map]
    exact hW'map

theorem exists_pow_lift {H M : Type*} [Group H] [Finite H] [Group M] {q : ℕ} (hq : q.Prime)
    (π : H →* M) (hkq : ¬ q ∣ Nat.card π.ker) {s : M} (hs : s ∈ π.range) (hsq : s ^ q = 1) :
    ∃ z : H, z ^ q = 1 ∧ π z = s := by
  obtain ⟨W, hWp, hWmap, hWinj⟩ := exists_pSubgroup_lift hq π hkq
    (isPGroup_zpowers_of_pow_eq_one hsq) (Subgroup.zpowers_le.2 hs)
  have hsW : s ∈ W.map π := hWmap ▸ Subgroup.mem_zpowers s
  obtain ⟨z, hzW, hzs⟩ := hsW
  refine ⟨z, ?_, hzs⟩
  have h1 : π (z ^ q) = π 1 := by rw [map_pow, hzs, hsq, map_one]
  have h2 : (⟨z ^ q, W.pow_mem hzW q⟩ : W) = 1 := hWinj (by
    simpa [MonoidHom.comp_apply] using h1)
  exact congrArg Subtype.val h2

theorem map_subtype_isElemAbelian_card {G : Type*} [Group G] {J : Subgroup G} {M : Type*}
    [Group M] (π : ↥J →* M) {p : ℕ} {E : Subgroup M} {W : Subgroup ↥J}
    (hWmap : W.map π = E) (hWinj : Function.Injective (π.comp W.subtype))
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (W.map J.subtype) ∧ Nat.card (W.map J.subtype) = Nat.card E := by
  refine ⟨CFSG.SectionRank.isElemAbelian_map
    (isElemAbelian_of_injective_comp_subtype π hWinj (hWmap ▸ hE)) J.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective J.subtype_injective,
    card_eq_of_injective_comp_subtype π hWinj, hWmap]

theorem lift_extraspecial_four {G : Type} [Group G] [Finite G] {J : Subgroup G} {M : Type*}
    [Group M] (π : ↥J →* M) (hk : ¬ 2 ∣ Nat.card π.ker) {Tb Ub : Subgroup M} {n : ℕ}
    (hTr : Tb ≤ π.range) (hT : CFSG.IsExtraspecialPGroup 2 ↥Tb)
    (hTc : Nat.card Tb = 2 ^ (2 * n + 1)) (hUT : Ub ≤ Tb) (hUe : IsElemAbelian 2 Ub)
    (hUc : Nat.card Ub = 4) (hUz : Ub ⊓ (Tb ⊓ Subgroup.centralizer (Tb : Set M)) = ⊥) :
    ∃ T : Subgroup G, T ≤ J ∧ IsExtraspecialTwo T n ∧ ∃ U : Subgroup G, U ≤ T ∧
      IsElemAbelian 2 U ∧ Nat.card U = 4 ∧
        U ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) = ⊥ := by
  obtain ⟨W, hWp, hWmap, hWinj⟩ := exists_pSubgroup_lift Nat.prime_two π hk hT.1 hTr
  let eWT : W ≃* Tb := (mulEquivMap π hWinj).trans (MulEquiv.subgroupCongr hWmap)
  let eTW : (W.map J.subtype) ≃* W := (W.equivMapOfInjective J.subtype J.subtype_injective).symm
  have hext : CFSG.IsExtraspecialPGroup 2 ↥(W.map J.subtype) :=
    CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv (eWT.symm.trans eTW.symm) hT
  refine ⟨W.map J.subtype, Subgroup.map_subtype_le _, ⟨hext, ?_⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective J.subtype_injective, card_eq_of_injective_comp_subtype π hWinj,
      hWmap, hTc]
  let Ut : Subgroup ↥J := Ub.comap π ⊓ W
  have hUtW : Ut ≤ W := inf_le_right
  have hUtmap : Ut.map π = Ub := by
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hu).1
    · intro u hu
      have : u ∈ W.map π := hWmap ▸ hUT hu
      obtain ⟨w, hw, rfl⟩ := this
      exact ⟨w, Subgroup.mem_inf.2 ⟨hu, hw⟩, rfl⟩
  have hUtinj : Function.Injective (π.comp Ut.subtype) := by
    intro a b hab
    have : (⟨a.1, hUtW a.2⟩ : W) = ⟨b.1, hUtW b.2⟩ := hWinj hab
    exact Subtype.ext (Subtype.mk.inj this)
  obtain ⟨hUel, hUcard⟩ := map_subtype_isElemAbelian_card π hUtmap hUtinj hUe
  refine ⟨Ut.map J.subtype, Subgroup.map_mono hUtW, hUel, hUcard.trans hUc, ?_⟩
  rw [eq_bot_iff]
  rintro x ⟨hxU, hxT, hxC⟩
  obtain ⟨w, hwU, rfl⟩ := hxU
  have hwW : w ∈ W := hUtW hwU
  have hcomm : ∀ w' ∈ W, w' * w = w * w' := by
    intro w' hw'
    have := Subgroup.mem_centralizer_iff.1 hxC (J.subtype w') ⟨w', hw', rfl⟩
    exact Subtype.ext this
  have hπw : π w ∈ Ub ⊓ (Tb ⊓ Subgroup.centralizer (Tb : Set M)) := by
    refine Subgroup.mem_inf.2 ⟨hUtmap ▸ Subgroup.mem_map_of_mem π hwU, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · exact hWmap ▸ Subgroup.mem_map_of_mem π hwW
    · rw [Subgroup.mem_centralizer_iff]
      rintro t ht
      have : t ∈ W.map π := hWmap ▸ ht
      obtain ⟨w', hw', rfl⟩ := this
      rw [← map_mul, ← map_mul, hcomm w' hw']
  rw [hUz, Subgroup.mem_bot] at hπw
  have : (⟨w, hUtW hwU⟩ : W) = 1 := hWinj (by simpa using hπw.trans (map_one π).symm)
  have hw1 : w = 1 := congrArg Subtype.val this
  rw [hw1]
  exact Subgroup.one_mem _


theorem mem_sup_zpowers_iff {M : Type*} [Group M] {K : Subgroup M} {y : M}
    (hc : K ≤ Subgroup.centralizer ({y} : Set M)) {x : M} :
    x ∈ K ⊔ Subgroup.zpowers y ↔ ∃ k ∈ K, ∃ z ∈ Subgroup.zpowers y, x = k * z := by
  have hzK : ∀ z ∈ Subgroup.zpowers y, ∀ k ∈ K, z * k = k * z := by
    intro z hz k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have := Subgroup.mem_centralizer_singleton_iff.1 (hc hk)
    exact ((Commute.zpow_left (Commute.symm (show Commute k y from this)) n).symm).eq.symm
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, one_mem _, (mul_one x).symm⟩
      · exact ⟨1, one_mem _, x, hx, (one_mul x).symm⟩
    · exact ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
    · rintro a b _ _ ⟨k, hk, z, hz, rfl⟩ ⟨k', hk', z', hz', rfl⟩
      refine ⟨k * k', mul_mem hk hk', z * z', mul_mem hz hz', ?_⟩
      calc k * z * (k' * z') = k * (z * k') * z' := by group
        _ = k * (k' * z) * z' := by rw [hzK z hz k' hk']
        _ = k * k' * (z * z') := by group
    · rintro a _ ⟨k, hk, z, hz, rfl⟩
      refine ⟨k⁻¹, inv_mem hk, z⁻¹, inv_mem hz, ?_⟩
      calc (k * z)⁻¹ = z⁻¹ * k⁻¹ := by group
        _ = k⁻¹ * z⁻¹ := by
          have := hzK z⁻¹ (inv_mem hz) k⁻¹ (inv_mem hk)
          exact this
  · rintro ⟨k, hk, z, hz, rfl⟩
    exact mul_mem (mem_sup_left hk) (mem_sup_right hz)


theorem kb_conj_mem {M : Type*} [Group M] {Kb : Subgroup M} {yb : M}
    (hKc : Kb ≤ Subgroup.centralizer ({yb} : Set M)) :
    ∀ p ∈ Kb ⊔ Subgroup.zpowers yb, ∀ k ∈ Kb, p * k * p⁻¹ ∈ Kb := by
  intro p hp k hk
  obtain ⟨k₀, hk₀, z, hz, rfl⟩ := (mem_sup_zpowers_iff hKc).1 hp
  have hzk : z * k = k * z := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKc hk)
    exact ((Commute.zpow_left (Commute.symm (show Commute k yb from this)) n).symm).eq.symm
  have : k₀ * z * k * (k₀ * z)⁻¹ = k₀ * k * k₀⁻¹ := by
    calc k₀ * z * k * (k₀ * z)⁻¹ = k₀ * (z * k) * z⁻¹ * k₀⁻¹ := by group
      _ = k₀ * (k * z) * z⁻¹ * k₀⁻¹ := by rw [hzk]
      _ = k₀ * k * k₀⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hk₀ hk) (inv_mem hk₀)

theorem center_eq_bot_of_simple {K : Type*} [Group K] [IsSimpleGroup K] (hn : ¬ IsMulCommutative K) :
    Subgroup.center K = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center K) with h | h
  · exact h
  · exfalso
    apply hn
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : a ∈ Subgroup.center K := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

theorem normal_threePrime_eq_bot {M : Type*} [Group M] [Finite M] {Kb : Subgroup M} {yb : M}
    {N : Subgroup M} (hy3 : yb ^ 3 = 1) (hKs : IsSimpleGroup ↥Kb) (hKn : ¬ IsMulCommutative ↥Kb)
    (hK3 : 3 ∣ Nat.card Kb) (hKc : Kb ≤ Subgroup.centralizer ({yb} : Set M))
    (hNP : N ≤ Kb ⊔ Subgroup.zpowers yb)
    (hNn : ∀ p ∈ Kb ⊔ Subgroup.zpowers yb, ∀ n ∈ N, p * n * p⁻¹ ∈ N)
    (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  have hKnorm := kb_conj_mem hKc
  have hKP : Kb ≤ Kb ⊔ Subgroup.zpowers yb := le_sup_left
  have hNK : ∀ k ∈ Kb, k ∈ N → k = 1 := by
    have hnorm : (N.subgroupOf Kb).Normal := by
      refine ⟨fun a ha b => ?_⟩
      have ha' : (a : M) ∈ N := ha
      have := hNn (b : M) (hKP b.2) (a : M) ha'
      exact (show ((b * a * b⁻¹ : ↥Kb) : M) ∈ N from by simpa using this)
    rcases hnorm.eq_bot_or_eq_top with h | h
    · intro k hk hkN
      have : (⟨k, hk⟩ : ↥Kb) ∈ N.subgroupOf Kb := hkN
      rw [h, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hKN : Kb ≤ N := by
        intro k hk
        have : (⟨k, hk⟩ : ↥Kb) ∈ N.subgroupOf Kb := by rw [h]; exact Subgroup.mem_top _
        exact this
      exact hN3 (hK3.trans (Subgroup.card_dvd_of_le hKN))
  rw [eq_bot_iff]
  intro n hn
  have hnP := hNP hn
  have hcomm : ∀ k ∈ Kb, n * k = k * n := by
    intro k hk
    have h1 : n * k * n⁻¹ * k⁻¹ ∈ N := by
      have := hNn k (hKP hk) n⁻¹ (inv_mem hn)
      have h2 : n * (k * n⁻¹ * k⁻¹) ∈ N := mul_mem hn this
      simpa [mul_assoc] using h2
    have h2 : n * k * n⁻¹ * k⁻¹ ∈ Kb :=
      mul_mem (hKnorm n hnP k hk) (inv_mem hk)
    have := hNK _ h2 h1
    calc n * k = n * k * n⁻¹ * k⁻¹ * k * n := by group
      _ = k * n := by rw [this]; group
  obtain ⟨k₀, hk₀, z, hz, rfl⟩ := (mem_sup_zpowers_iff hKc).1 hnP
  have hzk : ∀ k ∈ Kb, z * k = k * z := by
    intro k hk
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have := Subgroup.mem_centralizer_singleton_iff.1 (hKc hk)
    exact ((Commute.zpow_left (Commute.symm (show Commute k yb from this)) m).symm).eq.symm
  have hk₀c : (⟨k₀, hk₀⟩ : ↥Kb) ∈ Subgroup.center ↥Kb := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have h1 := hcomm k k.2
    have h2 : k₀ * z * (k : M) = (k : M) * (k₀ * z) := h1
    have h3 : k₀ * (k : M) * z = (k : M) * k₀ * z := by
      calc k₀ * (k : M) * z = k₀ * ((k : M) * z) := by group
        _ = k₀ * (z * (k : M)) := by rw [hzk k k.2]
        _ = k₀ * z * (k : M) := by group
        _ = (k : M) * (k₀ * z) := h2
        _ = (k : M) * k₀ * z := by group
    have := mul_right_cancel h3
    exact this.symm
  have hk₀1 : k₀ = 1 := by
    rw [center_eq_bot_of_simple hKn] at hk₀c
    exact congrArg Subtype.val (Subgroup.mem_bot.1 hk₀c)
  rw [hk₀1, one_mul] at hn ⊢
  have hz3 : z ^ 3 = 1 := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  by_contra hz1
  have hz1' : z ≠ 1 := fun h => hz1 (by rw [h]; exact Subgroup.one_mem _)
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1'
  apply hN3
  have := orderOf_dvd_natCard (⟨z, hn⟩ : ↥N)
  rwa [Subgroup.orderOf_mk, hord] at this


open scoped commutatorElement in
theorem isQuasisimple_of_simple_nonabelian {K : Type*} [Group K] [IsSimpleGroup K]
    (hn : ¬ IsMulCommutative K) : CFSG.Open.IsQuasisimple K := by
  refine ⟨?_, ?_⟩
  · rcases Subgroup.Normal.eq_bot_or_eq_top (commutator K) with h | h
    · exfalso
      apply hn
      refine ⟨⟨fun a b => ?_⟩⟩
      have : ⁅a, b⁆ ∈ commutator K := by
        rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at this
      exact (commutatorElement_eq_one_iff_mul_comm.1 this)
    · exact h
  · have e : K ⧸ Subgroup.center K ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_simple hn)).trans
        QuotientGroup.quotientBot
    exact e.isSimpleGroup



section Simple

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def toSimple (p : ℕ) (J : Subgroup G) : ↥J →* PSimple p J :=
  (QuotientGroup.mk' (Subgroup.center (PQuot p J))).comp (QuotientGroup.mk' (GLAPPrimeCore p ↥J))

theorem toSimple_surjective (p : ℕ) (J : Subgroup G) : Function.Surjective (toSimple p J) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem card_ker_toSimple (p : ℕ) (J : Subgroup G) :
    Nat.card (toSimple p J).ker =
      Nat.card (GLAPPrimeCore p ↥J) * Nat.card (Subgroup.center (PQuot p J)) := by
  have h1 : Nat.card (toSimple p J).ker =
      Nat.card (QuotientGroup.mk ⁻¹' (Subgroup.center (PQuot p J) : Set (PQuot p J)) :
        Set ↥J) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    show toSimple p J x = 1 ↔ _
    change (QuotientGroup.mk (QuotientGroup.mk x) : PSimple p J) = 1 ↔
      (QuotientGroup.mk x : PQuot p J) ∈ (Subgroup.center (PQuot p J) : Set (PQuot p J))
    rw [QuotientGroup.eq_one_iff]
    rfl
  rw [h1, QuotientGroup.card_preimage_mk]
  rfl

theorem exists_hom_of_simple_equiv {p : ℕ} {J : Subgroup G} {M : Type*} [Group M]
    (e : PSimple p J ≃* M) :
    ∃ π : ↥J →* M, Function.Surjective π ∧
      Nat.card π.ker = Nat.card (GLAPPrimeCoreOf p J) * Nat.card (Subgroup.center (PQuot p J)) := by
  refine ⟨e.toMonoidHom.comp (toSimple p J), e.surjective.comp (toSimple_surjective p J), ?_⟩
  have h1 : (e.toMonoidHom.comp (toSimple p J)).ker = (toSimple p J).ker :=
    MonoidHom.ker_comp_of_injective (toSimple p J) e.toMonoidHom e.injective
  rw [h1, card_ker_toSimple]
  congr 1
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective J.subtype_injective]

theorem exists_hom_ker_eq_of_center_bot {p : ℕ} {J : Subgroup G} {M : Type*} [Group M]
    (e : PSimple p J ≃* M) (hZ : Subgroup.center (PQuot p J) = ⊥) :
    ∃ π : ↥J →* M, Function.Surjective π ∧ π.ker = GLAPPrimeCore p ↥J := by
  refine ⟨e.toMonoidHom.comp (toSimple p J), e.surjective.comp (toSimple_surjective p J), ?_⟩
  rw [MonoidHom.ker_comp_of_injective (toSimple p J) e.toMonoidHom e.injective]
  ext x
  rw [MonoidHom.mem_ker]
  change (QuotientGroup.mk (QuotientGroup.mk x : PQuot p J) : PSimple p J) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff]

theorem odd_card_ker (J : Subgroup G) {k : ℕ}
    (hk : k = Nat.card (GLAPPrimeCoreOf 3 J) * Nat.card (Subgroup.center (PQuot 3 J)))
    (hO : Odd (Nat.card (GLAPPrimeCoreOf 3 J))) : ¬ 2 ∣ k := by
  have hZ : IsPGroup 3 (Subgroup.center (PQuot 3 J)) :=
    CFSG.LocalAnalysis.GLTheoremA.I2611.isPGroup_center_pQuot' Nat.prime_three J
  obtain ⟨n, hn⟩ := hZ.exists_card_eq
  have hodd : Odd (Nat.card (Subgroup.center (PQuot 3 J))) := by
    rw [hn]
    exact Odd.pow (by decide)
  rw [hk, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact hO.mul hodd

theorem not_three_dvd_card_ker (J : Subgroup G) {k : ℕ}
    (hk : k = Nat.card (GLAPPrimeCoreOf 3 J) * Nat.card (Subgroup.center (PQuot 3 J)))
    (hZ : Subgroup.center (PQuot 3 J) = ⊥) : ¬ 3 ∣ k := by
  rw [hk, hZ, Subgroup.card_bot, mul_one]
  exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three J

end Simple

end CFSG.LocalAnalysis.GLTheoremA.CatB

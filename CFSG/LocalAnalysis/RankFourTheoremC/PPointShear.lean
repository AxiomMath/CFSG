module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma33
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem zpowers_inf_zpowers_eq_bot {p : ℕ} (hp : p.Prime) {x c : G} (hxp : orderOf x = p)
    (hcp : orderOf c = p) (hcx : c ∉ zpowers x) : zpowers x ⊓ zpowers c = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  by_contra hg1
  have hgx : g ∈ zpowers x := hg.1
  have hgc : g ∈ zpowers c := hg.2
  have hgp : orderOf g = p := by
    have h1 : orderOf g ∣ p := by
      rw [← hxp]
      exact orderOf_dvd_of_mem_zpowers hgx
    exact (Nat.dvd_prime hp).mp h1 |>.resolve_left fun h => hg1 (orderOf_eq_one_iff.mp h)
  have hzc : zpowers g = zpowers c := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hgc) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, hgp, hcp])
  exact hcx (zpowers_le.mpr hgx (hzc ▸ mem_zpowers c))

omit [Finite G] in
theorem pow_mul_mul_pow_inv_eq {x c e : G} (hec : e * c = c * e) (hex : e * x * e⁻¹ = c * x)
    (j : ℕ) : e ^ j * x * (e ^ j)⁻¹ = c ^ j * x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcj : e * c ^ j * e⁻¹ = c ^ j := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (Commute.pow_right (show Commute e c from hec) j).eq
    calc e ^ (j + 1) * x * (e ^ (j + 1))⁻¹
        = e * (e ^ j * x * (e ^ j)⁻¹) * e⁻¹ := by rw [pow_succ', mul_inv_rev]; group
      _ = e * (c ^ j * x) * e⁻¹ := by rw [ih]
      _ = (e * c ^ j * e⁻¹) * (e * x * e⁻¹) := by group
      _ = c ^ (j + 1) * x := by rw [hcj, hex, pow_succ]; group

omit [Finite G] in
theorem inf_centralizer_ne_bot_of_normalizes [Finite G] {p : ℕ} [Fact p.Prime] {P W : Subgroup G}
    (hP : IsPGroup p P) (hWP : W ≤ P) (hnorm : P ≤ normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h
    apply hW
    rw [← map_subgroupOf_eq_of_le hWP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ W ⊓ centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h, mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

namespace IsPPoint

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem false_of_sheared [Fact p.Prime] (hp2 : p ≠ 2) (h243 : GL83ComponentPCoreTrivial)
    (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut) (hS : D1Global G)
    (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {c e : G} (hcP : c ∈ (P : Subgroup G)) (hc1 : c ≠ 1) (hcp : c ^ p = 1)
    (hcx : c * x = x * c) (hcz : c ∉ zpowers x) (hec : e * c = c * e)
    (hex : e * x * e⁻¹ = c * x) : False := by
  classical
  have hp : p.Prime := Fact.out
  have hxo : orderOf x = p := h.elem.2.1
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have hxQ : x ∈ (P : Subgroup G) ⊓ C := ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hcQ : c ∈ (P : Subgroup G) ⊓ C := ⟨hcP, mem_centralizer_singleton_iff.2 hcx⟩
  have hinf : zpowers x ⊓ zpowers c = ⊥ := zpowers_inf_zpowers_eq_bot hp hxo hco hcz
  have hxz : x ∉ zpowers c := by
    intro hxc
    have : x ∈ zpowers x ⊓ zpowers c := ⟨mem_zpowers x, hxc⟩
    rw [hinf, mem_bot] at this
    rw [this, orderOf_one] at hxo
    exact hp.one_lt.ne hxo
  set D : Subgroup G := zpowers x ⊔ zpowers c with hD
  have hDQ : D ≤ (P : Subgroup G) ⊓ C := sup_le (zpowers_le.mpr hxQ) (zpowers_le.mpr hcQ)
  have hDel : IsElemAbelian p D := by
    refine CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_sup_of_commuting p
      (isElemAbelian_zpowers hxp) (isElemAbelian_zpowers hcp) ?_
    rw [zpowers_le]
    refine mem_centralizer_iff.mpr fun b hb => ?_
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_left (show Commute c x from hcx) k).eq
  have hDcard : Nat.card D = p ^ 2 := by
    have hcomm : ∀ a ∈ zpowers x, a * c = c * a := fun a ha => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute x c from hcx.symm) k).eq
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers x) hcp hcz hcomm,
      Nat.card_zpowers, hxo]
    ring
  set ℓ : ℕ → Subgroup G := fun j => zpowers (c ^ j * x) with hℓ
  have hcxj : ∀ j : ℕ, c ^ j * x = x * c ^ j := fun j =>
    (Commute.pow_left (show Commute c x from hcx) j).eq
  have hord : ∀ j : ℕ, orderOf (c ^ j * x) = p := by
    intro j
    have h1 : (c ^ j * x) ^ p = 1 := by
      rw [(Commute.pow_left (show Commute c x from hcx) j).mul_pow, ← pow_mul, mul_comm,
        pow_mul, hcp, one_pow, one_mul, hxp]
    refine orderOf_eq_prime h1 fun h1' => ?_
    have : x ∈ zpowers c := by
      have hx : x = (c ^ j)⁻¹ := eq_inv_of_mul_eq_one_right h1'
      rw [hx]
      exact inv_mem (pow_mem (mem_zpowers c) j)
    exact hxz this
  have hℓinj : Set.InjOn ℓ ↑(Finset.range p) := by
    intro j hj j' hj' hjj'
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    have hmem : c ^ j' * x ∈ zpowers (c ^ j * x) := by
      rw [show zpowers (c ^ j * x) = ℓ j from rfl, hjj']
      exact mem_zpowers _
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hmem
    have hcomm : Commute (c ^ j) x := Commute.pow_left (show Commute c x from hcx) j
    have hm' : c ^ ((j : ℤ) * m) * x ^ m = c ^ j' * x := by
      have h1 : (c ^ j * x) ^ m = (c ^ j) ^ m * x ^ m := hcomm.mul_zpow m
      have h2 : (c ^ j) ^ m = c ^ ((j : ℤ) * m) := by rw [zpow_mul, zpow_natCast]
      rw [← h2, ← h1, hm]
    have hkey : x ^ (m - 1) = c ^ ((j' : ℤ) - (j : ℤ) * m) := by
      have h3 : x ^ m = (c ^ ((j : ℤ) * m))⁻¹ * (c ^ j' * x) := by
        rw [← hm']; group
      calc x ^ (m - 1) = x ^ m * x⁻¹ := by rw [zpow_sub, zpow_one]
        _ = (c ^ ((j : ℤ) * m))⁻¹ * c ^ j' := by rw [h3]; group
        _ = c ^ ((j' : ℤ) - (j : ℤ) * m) := by
          rw [← zpow_natCast, ← zpow_neg, ← zpow_add]; congr 1; ring
    have hxm : x ^ (m - 1) ∈ zpowers x ⊓ zpowers c :=
      ⟨zpow_mem (mem_zpowers x) _, hkey ▸ zpow_mem (mem_zpowers c) _⟩
    rw [hinf, mem_bot] at hxm
    have hd1 : (p : ℤ) ∣ m - 1 := (orderOf_dvd_iff_zpow_eq_one.mpr hxm |> fun h => by
      rwa [hxo] at h)
    have hd2 : (p : ℤ) ∣ (j' : ℤ) - (j : ℤ) * m := by
      have : c ^ ((j' : ℤ) - (j : ℤ) * m) = 1 := by rw [← hkey]; exact hxm
      have := orderOf_dvd_iff_zpow_eq_one.mpr this
      rwa [hco] at this
    have hd3 : (p : ℤ) ∣ (j' : ℤ) - (j : ℤ) := by
      have : (j' : ℤ) - (j : ℤ) = ((j' : ℤ) - (j : ℤ) * m) + (j : ℤ) * (m - 1) := by ring
      rw [this]
      exact dvd_add hd2 (dvd_mul_of_dvd_right hd1 _)
    have habs : |(j' : ℤ) - (j : ℤ)| < (p : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd3 habs
    omega
  set S : Finset (Subgroup G) := (Finset.range p).image ℓ with hSdef
  have hScard : S.card = p := by
    rw [hSdef, Finset.card_image_of_injOn hℓinj, Finset.card_range]
  refine h.not_exists_conj_lines hp2 h243 h244 hsig hS hD1 hFC hloc hDQ hDel hDcard
    ⟨S, hScard, fun L hL => ?_⟩
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hL
  refine ⟨zpowers_le.mpr (D.mul_mem (pow_mem (mem_sup_right (mem_zpowers c)) j)
    (mem_sup_left (mem_zpowers x))), ?_, e ^ j, ?_⟩
  · rw [hℓ]
    simp only [Nat.card_zpowers, hord]
  · rw [MonoidHom.map_zpowers]
    change zpowers (c ^ j * x) = zpowers ((e ^ j) * x * (e ^ j)⁻¹)
    rw [pow_mul_mul_pow_inv_eq hec hex j]

theorem le_centralizer_of_isElemAbelian [Fact p.Prime] (hp2 : p ≠ 2)
    (h243 : GL83ComponentPCoreTrivial) (h244 : GL83NongenerationList) (hsig : GL83SignalizerAut)
    (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local p P M)
    (h : IsPPoint p P M x) {E : Subgroup G} (hEP : E ≤ (P : Subgroup G)) (hE : IsElemAbelian p E)
    (hxE : x ∈ normalizer (E : Set G)) : E ≤ centralizer ({x} : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  have hxo : orderOf x = p := h.elem.2.1
  have hxp : x ^ p = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  by_contra hnot
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg (Subtype.val : E → G) (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hxinv : x⁻¹ ∈ normalizer (E : Set G) := inv_mem hxE
  have hconj : ∀ a ∈ E, x * a * x⁻¹ ∈ E := fun a ha => (mem_normalizer_iff.mp hxE a).mp ha
  have hconj' : ∀ a ∈ E, x⁻¹ * a * x ∈ E := fun a ha => by
    have := (mem_normalizer_iff.mp hxinv a).mp ha
    simpa using this
  let φ : E →* E := MonoidHom.mk' (fun a => ⟨x * a * x⁻¹ * (a : G)⁻¹,
    E.mul_mem (hconj a a.2) (E.inv_mem a.2)⟩) (by
    intro a b
    apply Subtype.ext
    have h1 : x * (a : G) * x⁻¹ ∈ E := hconj a a.2
    have h2 : x * (b : G) * x⁻¹ * (b : G)⁻¹ ∈ E := E.mul_mem (hconj b b.2) (E.inv_mem b.2)
    have h3 := hcomm _ (E.inv_mem a.2) _ h2
    change x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹ =
      (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹)
    calc x * ((a : G) * b) * x⁻¹ * ((a : G) * b)⁻¹
        = (x * (a : G) * x⁻¹) * ((x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
      _ = (x * (a : G) * x⁻¹) * ((a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹)) := by rw [← h3]
      _ = _ := by group)
  set V : Subgroup G := φ.range.map E.subtype with hV
  have hVE : V ≤ E := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hVmem : ∀ v, v ∈ V ↔ ∃ a ∈ E, v = x * a * x⁻¹ * a⁻¹ := by
    intro v
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨φ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hnot
    intro a ha
    rw [mem_centralizer_singleton_iff]
    have : x * a * x⁻¹ * a⁻¹ ∈ V := (hVmem _).mpr ⟨a, ha, rfl⟩
    rw [hbot, mem_bot] at this
    have h1 : x * a = a * x := by
      calc x * a = (x * a * x⁻¹ * a⁻¹) * (a * x) := by group
        _ = a * x := by rw [this, one_mul]
    exact h1.symm
  have hVx : ∀ v ∈ V, x * v * x⁻¹ ∈ V := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (hVmem v).mp hv
    refine (hVmem _).mpr ⟨x * a * x⁻¹, hconj a ha, by group⟩
  have hVx' : ∀ v ∈ V, x⁻¹ * v * x ∈ V := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (hVmem v).mp hv
    refine (hVmem _).mpr ⟨x⁻¹ * a * x, hconj' a ha, by group⟩
  have hxN : x ∈ normalizer (V : Set G) := by
    rw [mem_normalizer_iff]
    intro v
    exact ⟨hVx v, fun hv => by
      have := hVx' _ hv
      rwa [show x⁻¹ * (x * v * x⁻¹) * x = v by group] at this⟩
  set W : Subgroup G := V ⊔ zpowers x with hW
  have hxW : x ∈ W := mem_sup_right (mem_zpowers x)
  have hWP : W ≤ (P : Subgroup G) := sup_le (hVE.trans hEP) (zpowers_le.mpr h.mem)
  have hWN : W ≤ normalizer (V : Set G) := sup_le le_normalizer (zpowers_le.mpr hxN)
  have hWp : IsPGroup p W := P.isPGroup'.to_le hWP
  obtain ⟨⟨c, hcV, hcW⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (inf_centralizer_ne_bot_of_normalizes hWp (le_sup_left : V ≤ W) hWN hVne)
  have hc1' : c ≠ 1 := fun h1 => hc1 (Subtype.ext h1)
  obtain ⟨a, haE, hca⟩ := (hVmem c).mp hcV
  have hcE : c ∈ E := hVE hcV
  have hcp : c ^ p = 1 := hE.2 c hcE
  have hcx : c * x = x * c := (mem_centralizer_iff.mp hcW x hxW).symm
  have hco : orderOf c = p := orderOf_eq_prime hcp hc1'
  have hcz : c ∉ zpowers x := by
    intro hcx'
    have hzc : zpowers c = zpowers x := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hcx')
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hco, hxo])
    have hxE' : x ∈ E := zpowers_le.mpr hcE (hzc ▸ mem_zpowers x)
    apply hnot
    intro b hb
    rw [mem_centralizer_singleton_iff]
    exact (hcomm _ hxE' _ hb).symm
  have hax : x * a * x⁻¹ = c * a := by rw [hca]; group
  have hec : a⁻¹ * c = c * a⁻¹ := by
    have := hcomm _ (E.inv_mem haE) _ hcE
    exact this
  have hex : a⁻¹ * x * (a⁻¹)⁻¹ = c * x := by
    calc a⁻¹ * x * (a⁻¹)⁻¹ = a⁻¹ * (x * a * x⁻¹) * x := by group
      _ = a⁻¹ * (c * a) * x := by rw [hax]
      _ = (a⁻¹ * c) * a * x := by group
      _ = c * (a⁻¹ * a) * x := by rw [hec]; group
      _ = c * x := by group
  exact h.false_of_sheared hp2 h243 h244 hsig hS hD1 hFC hloc (hEP hcE) hc1' hcp hcx hcz hec hex

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC

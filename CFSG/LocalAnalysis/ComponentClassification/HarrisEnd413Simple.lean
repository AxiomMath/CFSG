module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBasic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndRank
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndInputs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecImg

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.HarrisEnd

open CFSG Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_finset_closure_eq_of_map {H : Type} [Group H] {ι : H →* G}
    (hι : Function.Injective ι) {P : Subgroup H} {s : Finset G}
    (hs : closure (s : Set G) = P.map ι) :
    ∃ s' : Finset H, s'.card ≤ s.card ∧ closure (s' : Set H) = P := by
  classical
  refine ⟨s.preimage ι hι.injOn, Finset.card_le_card_of_injOn ι
    (fun a ha => Finset.mem_preimage.mp ha) hι.injOn, ?_⟩
  apply map_injective hι
  rw [MonoidHom.map_closure, Finset.coe_preimage, ← hs]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    have hxP : x ∈ P.map ι := hs ▸ subset_closure hx
    obtain ⟨y, -, rfl⟩ := hxP
    exact ⟨y, hx, rfl⟩

omit [Finite G] in
theorem sectionalTwoRankLE_of_map {E : Subgroup G} {Y : Subgroup ↥E} {n : ℕ}
    (h : ∀ P : Subgroup G, P ≤ Y.map E.subtype → IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ n ∧ closure (s : Set G) = P) :
    GH74.SectionalTwoRankLE ↥Y n := by
  intro P hP
  let ι : ↥Y →* G := E.subtype.comp Y.subtype
  have hι : Function.Injective ι := E.subtype_injective.comp Y.subtype_injective
  have hle : P.map ι ≤ Y.map E.subtype := by
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, y.2, rfl⟩
  have hPp : IsPGroup 2 (P.map ι) := hP.map ι
  obtain ⟨s, hsn, hsc⟩ := h _ hle hPp
  obtain ⟨s', hs'n, hs'c⟩ := exists_finset_closure_eq_of_map hι hsc
  exact ⟨s', hs'n.trans hsn, hs'c⟩

omit [Finite G] in
theorem zpowers_le_normalizer_of_comm {P : Subgroup G} {x : G}
    (hx : ∀ y ∈ P, x * y = y * x) : zpowers x ≤ normalizer (P : Set G) := by
  refine (zpowers_le).mpr ?_
  refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
  exact (hx y hy).symm

omit [Finite G] in
theorem exists_mul_zpow_of_mem_sup {P : Subgroup G} {x g : G} (hx : ∀ y ∈ P, x * y = y * x)
    (hg : g ∈ P ⊔ zpowers x) : ∃ y ∈ P, ∃ k : ℤ, g = y * x ^ k := by
  have hg' : g ∈ ((P : Set G) * (zpowers x : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left P _ (zpowers_le_normalizer_of_comm hx)]
    exact hg
  obtain ⟨y, hy, _, ⟨k, rfl⟩, rfl⟩ := hg'
  exact ⟨y, hy, k, rfl⟩

theorem exists_closure_eq_of_sup_zpowers {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hxP : x ∉ P) (hx : ∀ y ∈ P, y * x = x * y) {n : ℕ}
    {s : Finset G} (hs : s.card ≤ n) (hsc : closure (s : Set G) = P ⊔ zpowers x) :
    ∃ s' : Finset G, s'.card ≤ n - 1 ∧ closure (s' : Set G) = P := by
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hdisj : P ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g ⟨hgP, hgx⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hgx
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · rw [zpow_mul, show x ^ (2 : ℤ) = 1 by exact_mod_cast hx2, one_zpow]
      exact one_mem _
    · exfalso
      rw [zpow_add, zpow_mul, show x ^ (2 : ℤ) = 1 by exact_mod_cast hx2, one_zpow, one_mul,
        zpow_one] at hgP
      exact hxP hgP
  refine exists_closure_eq_of_sup hP (fun a ha => ?_) (fun a ha b hb => ?_) (fun y hy a ha => ?_)
    hdisj (k := 1) (by rw [Nat.card_zpowers, hord, pow_one]) hs hsc
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow_self x i j).eq
  · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    exact (Commute.zpow_right (show Commute y x from hx y hy) k).eq

section Simple

variable [IsSimpleGroup ↥(layer G)]


omit [Finite G] in
theorem centralizer_inf_layer_eq_bot {K : Subgroup G} (hKE : K ≤ layer G)
    (hK : ∃ a b : K, a * b ≠ b * a) :
    centralizer (layer G : Set G) ⊓ layer G = ⊥ := by
  have hn : ((centralizer (layer G : Set G)).subgroupOf (layer G)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * n * (g : G)⁻¹ = n := by
      rw [mem_centralizer_iff.mp hn g g.2]
      group
    simpa [h1] using hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((centralizer (layer G : Set G)).subgroupOf (layer G)) with h | h
  · rw [← inf_subgroupOf_left, subgroupOf_eq_bot, disjoint_iff, inf_comm, ← inf_assoc,
      inf_idem] at h
    rw [inf_comm]
    exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hK
    apply hab
    have hb : (⟨b, hKE b.2⟩ : ↥(layer G)) ∈ (centralizer (layer G : Set G)).subgroupOf (layer G) :=
      h ▸ mem_top _
    rw [mem_subgroupOf] at hb
    exact Subtype.ext (mem_centralizer_iff.mp hb a (hKE a.2))

omit [IsSimpleGroup ↥(layer G)] in
theorem layerIn_fixedPoints_conjOn (tb : G) :
    GSThmB.layerIn (fixedPoints (conjOn (layer G) tb)) =
      (GSThmB.layerIn (layer G ⊓ centralizer {tb})).subgroupOf (layer G) := by
  rw [fixedPoints_conjOn_eq, ← inf_subgroupOf_left]
  exact GSThmB.B5a.layerIn_subgroupOf inf_le_left

omit [Finite G] [IsSimpleGroup ↥(layer G)] in
theorem layerIn_le_layer (tb : G) :
    GSThmB.layerIn (layer G ⊓ centralizer {tb}) ≤ layer G :=
  (map_subtype_le _).trans inf_le_left

omit [Finite G] [IsSimpleGroup ↥(layer G)] in
theorem isPGroup_sup_zpowers {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx2 : x ^ 2 = 1)
    (hx : ∀ y ∈ P, x * y = y * x) : IsPGroup 2 ↥(P ⊔ zpowers x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g
  obtain ⟨y, hy, k, hg⟩ := exists_mul_zpow_of_mem_sup hx g.2
  obtain ⟨n, hn⟩ := hP ⟨y, hy⟩
  refine ⟨n + 1, Subtype.ext ?_⟩
  have hc : Commute y (x ^ k) := (show Commute y x from (hx y hy).symm).zpow_right k
  have hyn : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hxk : (x ^ k) ^ 2 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx2, one_zpow]
  rw [Subgroup.coe_pow, hg, hc.mul_pow, pow_succ, pow_mul, hyn, one_pow, one_mul, pow_mul',
    hxk, one_pow, Subgroup.coe_one]

theorem list_of_simple (hin : Harris36SimpleInput) {tb bb : G} (htb2 : tb ^ 2 = 1)
    (htbC : tb ∉ centralizer (layer G : Set G)) (hbb : bb ∈ center G) (hbb2 : bb ^ 2 = 1)
    (hbb1 : bb ≠ 1) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h16 : 16 ∣ p ^ (2 * m) - 1) (hF : IsOfType (HarrisF p) ↥(layer G))
    (h47 : ∀ k : ℕ, 1 ≤ k → ¬ Blueprint.LieModel ↥(layer G) .PSL 4 p k ∧
      ¬ Blueprint.LieModel ↥(layer G) .PSU 4 p k)
    (hK : Blueprint.LieModel ↥(GSThmB.layerIn (layer G ⊓ centralizer {tb})) .PSL 2 p m)
    (hr : ∀ P : Subgroup G, P ≤ centralizer {tb} → IsPGroup 2 P →
      ∃ s : Finset G, s.card ≤ 4 ∧ closure (s : Set G) = P) :
    conjOn (layer G) tb ∉ innAut ↥(layer G) ∧
      (Nonempty (↥(layer G) ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (↥(layer G) ≃* Blueprint.NativeSporadic.J3) ∨
        Blueprint.LieModel ↥(layer G) .PSL 3 2 2 ∨ Blueprint.LieModel ↥(layer G) .PSL 3 p m ∨
        Blueprint.LieModel ↥(layer G) .PSU 3 p m ∨
        Blueprint.LieModel ↥(layer G) .PSL 2 p (2 * m)) := by
  set E := layer G with hEdef
  set τ := conjOn E tb with hτdef
  have hKE := layerIn_le_layer (G := G) tb
  have hKnab := nonabelian_of_lieModel_psl2 hK
  have hEnab : ∃ a b : ↥E, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hKnab
    refine ⟨⟨a, hKE a.2⟩, ⟨b, hKE b.2⟩, fun h => hab (Subtype.ext ?_)⟩
    have := congrArg Subtype.val h
    simpa using this
  have hCE := centralizer_inf_layer_eq_bot hKE hKnab
  have hbbC : bb ∈ centralizer (E : Set G) :=
    mem_centralizer_iff.mpr fun h _ => mem_center_iff.mp hbb h
  have hbbE : bb ∉ E := fun h => hbb1 (by
    have : bb ∈ centralizer (E : Set G) ⊓ E := ⟨hbbC, h⟩
    rwa [hCE, mem_bot] at this)
  have hτ1 : τ ≠ 1 := fun h => htbC (conjOn_eq_one_iff.mp h)
  have hτ2 : τ ^ 2 = 1 := by rw [hτdef, ← map_pow, htb2, map_one]
  have hτord : orderOf τ = 2 := orderOf_eq_prime hτ2 hτ1
  have hKτ : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m := by
    rw [hτdef, layerIn_fixedPoints_conjOn]
    exact lieModel_psl2_of_mulEquiv (subgroupOfEquivOfLe hKE) hK
  have hfix : (fixedPoints τ).map E.subtype = E ⊓ centralizer {tb} := map_fixedPoints_conjOn tb
  have hbbP : ∀ P : Subgroup G, P ≤ E ⊓ centralizer {tb} → ∀ y ∈ P, bb * y = y * bb :=
    fun P _ y _ => (mem_center_iff.mp hbb y).symm
  have hr3 : GH74.SectionalTwoRankLE ↥(fixedPoints τ) 3 := by
    refine sectionalTwoRankLE_of_map fun P hP hP2 => ?_
    rw [hfix] at hP
    have hsup : P ⊔ zpowers bb ≤ centralizer {tb} := by
      refine sup_le (hP.trans inf_le_right) (zpowers_le.mpr ?_)
      exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hbb tb).symm
    obtain ⟨s, hs, hsc⟩ := hr _ hsup (isPGroup_sup_zpowers hP2 hbb2 (hbbP P hP))
    exact exists_closure_eq_of_sup_zpowers hP2 hbb2 hbb1 (fun h => hbbE ((hP.trans inf_le_left) h))
      (fun y hy => (hbbP P hP y hy).symm) hs hsc
  have hYnab : ∃ a b : ↥E, a * b ≠ b * a := hEnab
  have hin' := hin ↥E hYnab p m hp hp2 hm h16 hF h47 τ hτord hKτ
  have hout : τ ∉ innAut ↥E := hin'.1 hr3
  refine ⟨hout, hin'.2 hout ?_⟩
  refine sectionalTwoRankLE_of_map fun P hP hP2 => ?_
  rw [hfix] at hP
  have htb1 : tb ≠ 1 := fun h => htbC (h ▸ one_mem _)
  have hP1 := isPGroup_sup_zpowers hP2 hbb2 (hbbP P hP)
  have htbP1 : ∀ y ∈ P ⊔ zpowers bb, tb * y = y * tb := by
    intro y hy
    obtain ⟨y', hy', k, rfl⟩ := exists_mul_zpow_of_mem_sup (hbbP P hP) hy
    have h1 : tb * y' = y' * tb := (mem_centralizer_singleton_iff.mp (hP hy').2).symm
    have h2 : Commute tb (bb ^ k) :=
      Commute.zpow_right (show Commute tb bb from mem_center_iff.mp hbb tb) k
    rw [← mul_assoc, h1, mul_assoc, h2.eq, ← mul_assoc]
  have htbnot : tb ∉ P ⊔ zpowers bb := by
    intro h
    obtain ⟨y, hy, k, hyk⟩ := exists_mul_zpow_of_mem_sup (hbbP P hP) h
    apply hout
    refine conjOn_mem_innAut_iff.mpr ⟨y, (hP.trans inf_le_left) hy, ?_⟩
    rw [hyk, show y * bb ^ k * y⁻¹ = bb ^ k by
      rw [mul_assoc, (Commute.zpow_left (show Commute bb y⁻¹ from
        (mem_center_iff.mp hbb y⁻¹).symm) k).eq, ← mul_assoc, mul_inv_cancel, one_mul]]
    exact zpow_mem hbbC k
  have hsup : P ⊔ zpowers bb ⊔ zpowers tb ≤ centralizer {tb} := by
    refine sup_le (sup_le (hP.trans inf_le_right) (zpowers_le.mpr ?_)) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hbb tb).symm
    · exact mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨s, hs, hsc⟩ := hr _ hsup (isPGroup_sup_zpowers hP1 htb2 htbP1)
  obtain ⟨s₁, hs₁, hs₁c⟩ := exists_closure_eq_of_sup_zpowers hP1 htb2 htb1 htbnot
    (fun y hy => (htbP1 y hy).symm) hs hsc
  obtain ⟨s₂, hs₂, hs₂c⟩ := exists_closure_eq_of_sup_zpowers hP2 hbb2 hbb1
    (fun h => hbbE ((hP.trans inf_le_left) h)) (fun y hy => (hbbP P hP y hy).symm) hs₁ hs₁c
  exact ⟨s₂, by omega, hs₂c⟩

omit [Finite G] [IsSimpleGroup ↥(layer G)] in
theorem conj_mem_centralizer_layer {c : G} (hc : c ∈ Subgroup.centralizer (layer G : Set G))
    (g : G) : g * c * g⁻¹ ∈ Subgroup.centralizer (layer G : Set G) := by
  refine mem_centralizer_iff.mpr fun h hh => ?_
  have hh' : g⁻¹ * h * g ∈ layer G := by
    have := (inferInstance : (layer G).Normal).conj_mem h hh g⁻¹
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.mp hc _ hh'
  calc h * (g * c * g⁻¹) = g * ((g⁻¹ * h * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [e]
    _ = g * c * g⁻¹ * h := by group

omit [Finite G] in
theorem exists_mul_of_conjOn_mem_innAut {K : Subgroup G} (hKE : K ≤ layer G)
    (hK : ∃ a b : K, a * b ≠ b * a) {tb g : G} (hg : g ∈ centralizer {tb})
    (hin : conjOn (layer G) g ∈ innAut ↥(layer G)) :
    ∃ c ∈ Subgroup.centralizer (layer G : Set G) ⊓ Subgroup.centralizer {tb},
      ∃ n ∈ layer G ⊓ Subgroup.centralizer {tb}, g = c * n := by
  obtain ⟨n, hnE, hc⟩ := conjOn_mem_innAut_iff.mp hin
  have hCE := centralizer_inf_layer_eq_bot hKE hK
  have hgt : tb * g * tb⁻¹ = g := by
    rw [← mem_centralizer_singleton_iff.mp hg]
    group
  have hc' := conj_mem_centralizer_layer hc tb
  have hn' : tb * n * tb⁻¹ ∈ layer G := (inferInstance : (layer G).Normal).conj_mem n hnE tb
  have key : (tb * (g * n⁻¹) * tb⁻¹)⁻¹ * (g * n⁻¹) = (tb * n * tb⁻¹) * n⁻¹ := by
    calc (tb * (g * n⁻¹) * tb⁻¹)⁻¹ * (g * n⁻¹)
        = tb * n * tb⁻¹ * ((tb * g * tb⁻¹)⁻¹ * g) * n⁻¹ := by group
      _ = (tb * n * tb⁻¹) * n⁻¹ := by rw [hgt]; group
  have hmem : (tb * n * tb⁻¹) * n⁻¹ ∈ Subgroup.centralizer (layer G : Set G) ⊓ layer G := by
    refine Subgroup.mem_inf.mpr ⟨?_, mul_mem hn' (inv_mem hnE)⟩
    rw [← key]
    exact mul_mem (inv_mem hc') hc
  rw [hCE, mem_bot, mul_inv_eq_one] at hmem
  have hnt : n ∈ Subgroup.centralizer ({tb} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc n * tb = (tb * n * tb⁻¹) * tb := by rw [hmem]
      _ = tb * n := by group
  have hct : g * n⁻¹ ∈ Subgroup.centralizer ({tb} : Set G) := mul_mem hg (inv_mem hnt)
  exact ⟨g * n⁻¹, ⟨hc, hct⟩, n, ⟨hnE, hnt⟩, by group⟩

omit [IsSimpleGroup ↥(layer G)] in
theorem orderOf_ne_of_hasDihedralSylowTwo {K : Type} [Group K] [Finite K]
    (hK : GorensteinWalter.HasDihedralSylowTwo K) (k : K) :
    orderOf k ≠ 2 ^ (Nat.card K).factorization 2 := by
  intro hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 K := Sylow.ofCard (zpowers k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨m, hm, ⟨e⟩⟩ := hK P
  have hcyc : IsCyclic (P : Subgroup K) := by
    change IsCyclic (zpowers k)
    infer_instance
  have : IsCyclic (DihedralGroup (2 ^ m)) := isCyclic_of_surjective e.toMonoidHom e.surjective
  exact DihedralGroup.not_isCyclic (by
    intro h
    have := Nat.one_lt_two_pow (n := m) (by omega)
    omega) this

theorem not_J3 {tb bb : G} (htb2 : tb ^ 2 = 1)
    (hbb : bb ∈ center G) (hbb2 : bb ^ 2 = 1)
    (hQt : centralizer (layer G : Set G) ⊓ centralizer {tb} = zpowers bb)
    (hKnab : ∃ a b : ↥(GSThmB.layerIn (layer G ⊓ centralizer {tb})), a * b ≠ b * a)
    (hall : ∀ φ : MulAut ↥(layer G),
      φ ∈ innAut ↥(layer G) ∨ φ * conjOn (layer G) tb ∈ innAut ↥(layer G))
    (hKeq : layer G ⊓ centralizer {tb} = GSThmB.layerIn (layer G ⊓ centralizer {tb}))
    (hKd : GorensteinWalter.HasDihedralSylowTwo ↥(GSThmB.layerIn (layer G ⊓ centralizer {tb})))
    {d : G} (hd : d ∈ centralizer {tb}) {e : ℕ} (he : 2 ≤ e) (hde : orderOf d = 2 ^ e)
    (hK2 : 2 ^ e =
      2 ^ (Nat.card ↥(GSThmB.layerIn (layer G ⊓ centralizer {tb}))).factorization 2) :
    False := by
  set E := layer G with hEdef
  set K := GSThmB.layerIn (layer G ⊓ centralizer {tb}) with hKdef
  set τ := conjOn E tb with hτdef
  have hKE : K ≤ E := layerIn_le_layer tb
  have hdec : ∀ g ∈ centralizer ({tb} : Set G), conjOn E g ∈ innAut ↥E →
      ∃ c ∈ zpowers bb, ∃ n ∈ K, g = c * n := by
    intro g hg hgin
    obtain ⟨c, hc, n, hn, rfl⟩ := exists_mul_of_conjOn_mem_innAut hKE hKnab hg hgin
    rw [hQt] at hc
    rw [hKeq] at hn
    exact ⟨c, hc, n, hn, rfl⟩
  have hbbc : ∀ c ∈ zpowers bb, ∀ x : G, c * x = x * c := by
    intro c hc x
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact (Commute.zpow_left (show Commute bb x from (mem_center_iff.mp hbb x).symm) k).eq
  have hc2 : ∀ c ∈ zpowers bb, c ^ 2 = 1 := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hbb2, one_zpow]
  obtain ⟨n, hnK, hsq⟩ : ∃ n ∈ K, d ^ 2 = n ^ 2 := by
    rcases hall (conjOn E d) with h | h
    · obtain ⟨c, hc, n, hn, rfl⟩ := hdec d hd h
      refine ⟨n, hn, ?_⟩
      rw [(show Commute c n from hbbc c hc n).mul_pow, hc2 c hc, one_mul]
    · rw [hτdef, ← map_mul] at h
      have hdt : d * tb ∈ centralizer ({tb} : Set G) :=
        mul_mem hd (mem_centralizer_singleton_iff.mpr rfl)
      obtain ⟨c, hc, n, hn, hdn⟩ := hdec (d * tb) hdt h
      refine ⟨n, hn, ?_⟩
      have htn : tb * n = n * tb :=
        (mem_centralizer_singleton_iff.mp ((hKeq ▸ hn : n ∈ E ⊓ centralizer {tb}).2)).symm
      have hd' : d = c * n * tb := by
        calc d = d * tb * tb := by rw [mul_assoc, ← sq, htb2, mul_one]
          _ = c * n * tb := by rw [hdn]
      rw [hd', sq, sq]
      calc c * n * tb * (c * n * tb) = c * c * (n * (tb * n) * tb) := by
            rw [show c * n * tb * (c * n * tb) = c * (n * (tb * c) * n * tb) by group,
              ← hbbc c hc tb, show c * (n * (c * tb) * n * tb) = c * ((n * c) * tb * n * tb) by
                group, ← hbbc c hc n]
            group
        _ = n * n := by
            rw [htn, ← sq c, hc2 c hc, one_mul,
              show n * (n * tb) * tb = n * n * (tb * tb) by group, ← sq tb, htb2, mul_one]
  have hnord : orderOf n = 2 ^ e := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
    have hd1 : d ^ 2 ^ (e' + 1) ≠ 1 := by
      intro h
      have := orderOf_dvd_of_pow_eq_one h
      rw [hde] at this
      have := Nat.le_of_dvd (by positivity) this
      have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (show e' + 1 < e' + 2 by omega)
      omega
    have hd2 : d ^ 2 ^ (e' + 2) = 1 := by rw [← hde]; exact pow_orderOf_eq_one d
    have hpow : ∀ j : ℕ, d ^ (2 * j) = n ^ (2 * j) := fun j => by rw [pow_mul, hsq, ← pow_mul]
    refine orderOf_eq_prime_pow (p := 2) ?_ ?_
    · rw [show 2 ^ (e' + 1) = 2 * 2 ^ e' by ring, ← hpow, ← show 2 ^ (e' + 1) = 2 * 2 ^ e' by ring]
      exact hd1
    · rw [show 2 ^ (e' + 2) = 2 * 2 ^ (e' + 1) by ring, ← hpow,
        ← show 2 ^ (e' + 2) = 2 * 2 ^ (e' + 1) by ring]
      exact hd2
  apply orderOf_ne_of_hasDihedralSylowTwo hKd ⟨n, hnK⟩
  rw [Subgroup.orderOf_mk, hnord, hK2]

end Simple

end CFSG.ComponentClassification.HarrisLit.HarrisEnd

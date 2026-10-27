module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporBigOvergroup
import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporMemoir
import CFSG.GroupTheory.PCentralElement
import CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.GroupTheory.ConjTransport
import CFSG.Mathlib.GroupTheory.SylowConj

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporBig

private lemma conj_mem_of_mem_normalizer {G : Type*} [Group G] {V : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G)) {v : G} (hv : v ∈ V) : s * v * s⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp hs v).mp hv

private lemma conj_conj_eq_self {G : Type*} [Group G] {s v : G} (hs2 : s ^ 2 = 1) :
    s * (s * v * s⁻¹) * s⁻¹ = v := by
  have hs : s * s = 1 := by simpa [pow_two] using hs2
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  rw [hs']
  calc s * (s * v * s) * s = (s * s) * v * (s * s) := by group
    _ = v := by rw [hs]; group

private noncomputable def conjHom {G : Type*} [Group G] {V : Subgroup G} (s : G)
    (hs : s ∈ Subgroup.normalizer (V : Set G)) : V →* V :=
  { toFun := fun v => ⟨s * (v : G) * s⁻¹, conj_mem_of_mem_normalizer hs v.2⟩
    map_one' := by ext; simp
    map_mul' := fun x y => by
      ext
      simp only [Subgroup.coe_mul]
      group }

private noncomputable def diffHom {G : Type*} [Group G] {V : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G))
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) : V →* V :=
  { toFun := fun v => ⟨(v : G) * (s * (v : G) * s⁻¹)⁻¹,
      V.mul_mem v.2 (V.inv_mem (conj_mem_of_mem_normalizer hs v.2))⟩
    map_one' := by ext; simp
    map_mul' := fun x y => by
      ext
      simp only [Subgroup.coe_mul]
      have hxy : s * ((x : G) * (y : G)) * s⁻¹ = (s * (x : G) * s⁻¹) * (s * (y : G) * s⁻¹) := by
        group
      rw [hxy, mul_inv_rev]
      have hcy : (y : G) * (s * (y : G) * s⁻¹)⁻¹ = (s * (y : G) * s⁻¹)⁻¹ * (y : G) :=
        hVab y y.2 ((s * (y : G) * s⁻¹)⁻¹)
          (V.inv_mem (conj_mem_of_mem_normalizer hs y.2))
      have hcyx : (y : G) * (s * (x : G) * s⁻¹)⁻¹ =
          (s * (x : G) * s⁻¹)⁻¹ * (y : G) :=
        hVab y y.2 ((s * (x : G) * s⁻¹)⁻¹)
          (V.inv_mem (conj_mem_of_mem_normalizer hs x.2))
      have hcx : (s * (x : G) * s⁻¹)⁻¹ * (s * (y : G) * s⁻¹)⁻¹ =
          (s * (y : G) * s⁻¹)⁻¹ * (s * (x : G) * s⁻¹)⁻¹ :=
        hVab ((s * (x : G) * s⁻¹)⁻¹)
          (V.inv_mem (conj_mem_of_mem_normalizer hs x.2))
          ((s * (y : G) * s⁻¹)⁻¹)
          (V.inv_mem (conj_mem_of_mem_normalizer hs y.2))
      calc (x : G) * (y : G) * ((s * (y : G) * s⁻¹)⁻¹ * (s * (x : G) * s⁻¹)⁻¹)
          = (x : G) * (y : G) * (s * (y : G) * s⁻¹)⁻¹ * (s * (x : G) * s⁻¹)⁻¹ := by group
        _ = (x : G) * ((y : G) * (s * (y : G) * s⁻¹)⁻¹) * (s * (x : G) * s⁻¹)⁻¹ := by group
        _ = (x : G) * ((s * (y : G) * s⁻¹)⁻¹ * (y : G)) * (s * (x : G) * s⁻¹)⁻¹ := by rw [hcy]
        _ = (x : G) * (s * (y : G) * s⁻¹)⁻¹ * ((y : G) * (s * (x : G) * s⁻¹)⁻¹) := by group
        _ = (x : G) * (s * (y : G) * s⁻¹)⁻¹ * ((s * (x : G) * s⁻¹)⁻¹ * (y : G)) := by rw [hcyx]
        _ = (x : G) * ((s * (y : G) * s⁻¹)⁻¹ * (s * (x : G) * s⁻¹)⁻¹) * (y : G) := by group
        _ = (x : G) * ((s * (x : G) * s⁻¹)⁻¹ * (s * (y : G) * s⁻¹)⁻¹) * (y : G) := by rw [hcx]
        _ = (x : G) * (s * (x : G) * s⁻¹)⁻¹ * ((s * (y : G) * s⁻¹)⁻¹ * (y : G)) := by group
        _ = (x : G) * (s * (x : G) * s⁻¹)⁻¹ * ((y : G) * (s * (y : G) * s⁻¹)⁻¹) := by rw [hcy]
        _ = ((x : G) * (s * (x : G) * s⁻¹)⁻¹) * ((y : G) * (s * (y : G) * s⁻¹)⁻¹) := by group }

private lemma diffHom_eq_one_iff {G : Type*} [Group G] {V : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G))
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hs2 : s ^ 2 = 1) {v : V} :
    diffHom hs hVab v = 1 ↔ (v : G) = s * (v : G) * s⁻¹ := by
  constructor
  · intro h
    have hv : (v : G) * (s * (v : G) * s⁻¹)⁻¹ = 1 := by
      simpa only [diffHom, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one,
        Subgroup.coe_one] using congrArg Subtype.val h
    rw [mul_inv_eq_one] at hv
    exact hv
  · intro h
    apply Subtype.ext
    simp only [diffHom, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one,
      Subgroup.coe_one]
    rw [← h, mul_inv_cancel]

private lemma conj_diffHom_eq_inv {G : Type*} [Group G] {V : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (V : Set G))
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hs2 : s ^ 2 = 1) (u : V) :
    conjHom s hs (diffHom hs hVab u) = (diffHom hs hVab u)⁻¹ := by
  apply Subtype.ext
  simp only [conjHom, diffHom, MonoidHom.coe_mk, OneHom.coe_mk]
  have hinner : s * (s * (u : G) * s⁻¹) * s⁻¹ = (u : G) := conj_conj_eq_self hs2
  calc s * ((u : G) * (s * (u : G) * s⁻¹)⁻¹) * s⁻¹
      = (s * (u : G) * s⁻¹) * (s * (s * (u : G) * s⁻¹) * s⁻¹)⁻¹ := by group
    _ = (s * (u : G) * s⁻¹) * ((u : G))⁻¹ := by rw [hinner]
    _ = ((u : G) * (s * (u : G) * s⁻¹)⁻¹)⁻¹ := by group

private lemma ker_or_range_large {p i j : ℕ} [Fact p.Prime] {K R : ℕ}
    (hK : K = p ^ i) (hR : R = p ^ j) (hij : i + j = 3) :
    p ^ 2 ≤ K ∨ p ^ 2 ≤ R := by
  rw [hK, hR]
  by_contra h
  push Not at h
  have hi2 : i ≤ 1 := by
    by_contra hi2
    exact (not_le.mpr h.1)
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : 2 ≤ i))
  have hj2 : j ≤ 1 := by
    by_contra hj2
    exact (not_le.mpr h.2)
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega : 2 ≤ j))
  omega

private lemma exists_large_fixed_or_anti {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {V : Subgroup G} (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVcard : Nat.card V = p ^ 3) {s : G} (hs : s ∈ Subgroup.normalizer (V : Set G))
    (hs2 : s ^ 2 = 1) :
    ∃ S : Subgroup V, p ^ 2 ≤ Nat.card S ∧
      ((∀ v : V, v ∈ S → s * (v : G) * s⁻¹ = (v : G)) ∨
        (∀ v : V, v ∈ S → s * (v : G) * s⁻¹ = ((v : G)⁻¹))) := by
  classical
  let c : V →* V := conjHom s hs
  have hc : ∀ v : V, c (c v) = v := by
    intro v
    apply Subtype.ext
    simp only [c, conjHom]
    exact conj_conj_eq_self hs2
  have hcdiff : ∀ u : V, c (diffHom hs hVab u) = (diffHom hs hVab u)⁻¹ :=
    conj_diffHom_eq_inv hs hVab hs2
  let φ : V →* V := diffHom hs hVab
  have hcardprod : Nat.card φ.ker * Nat.card φ.range = Nat.card V := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have h2 : Nat.card (V ⧸ φ.ker) = Nat.card φ.range := by
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
    rw [h2, mul_comm] at h1
    exact h1.symm
  have htop : Nat.card (⊤ : Subgroup V) = Nat.card V := Subgroup.card_top
  have hkerdvd : Nat.card φ.ker ∣ p ^ 3 := by
    rw [← hVcard]
    simpa [htop] using Subgroup.card_dvd_of_le (le_top : φ.ker ≤ ⊤)
  have hrangedvd : Nat.card φ.range ∣ p ^ 3 := by
    rw [← hVcard]
    simpa [htop] using Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)
  obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hkerdvd
  obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hrangedvd
  have hij : i + j = 3 := by
    have h : p ^ i * p ^ j = p ^ 3 := by
      rw [← hi, ← hj, hcardprod, hVcard]
    rw [← pow_add] at h
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h
  have hlarge : p ^ 2 ≤ Nat.card φ.ker ∨ p ^ 2 ≤ Nat.card φ.range :=
    ker_or_range_large hi hj hij
  rcases hlarge with hk | hr
  · refine ⟨φ.ker, hk, Or.inl ?_⟩
    intro v hv
    have hvg : (v : G) = s * (v : G) * s⁻¹ :=
      (diffHom_eq_one_iff hs hVab hs2).mp (MonoidHom.mem_ker.mp hv)
    exact hvg.symm
  · refine ⟨φ.range, hr, Or.inr ?_⟩
    rintro v ⟨u, rfl⟩
    have hcv : c (φ u) = (φ u)⁻¹ := hcdiff u
    exact congrArg Subtype.val hcv

private lemma inf_ne_bot_of_large {V : Type*} [Group V] [Finite V] [IsMulCommutative V]
    {p : ℕ} [Fact p.Prime] (hV : Nat.card V = p ^ 3) {A B : Subgroup V}
    (hA : p ^ 2 ≤ Nat.card A) (hB : p ^ 2 ≤ Nat.card B) : A ⊓ B ≠ ⊥ := by
  intro hbot
  have hdisj : Disjoint A B := disjoint_iff.mpr hbot
  haveI : A.Normal := Subgroup.normal_of_isMulCommutative A
  have hnormal : B ≤ Subgroup.normalizer (A : Set V) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hcard :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer (G := V) A B hnormal hdisj
  have hle : Nat.card (A ⊔ B : Subgroup V) ≤ Nat.card V := Subgroup.card_le_card_group _
  rw [hcard] at hle
  have h4 : p ^ 4 ≤ Nat.card A * Nat.card B := by
    calc p ^ 4 = p ^ 2 * p ^ 2 := by ring
      _ ≤ Nat.card A * Nat.card B := Nat.mul_le_mul hA hB
  have h34 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num : 3 < 4)
  have : p ^ 3 < p ^ 3 := lt_of_lt_of_le h34 (h4.trans (hle.trans_eq hV))
  exact lt_irrefl _ this

private lemma conj_eq_or_inv {G : Type*} [Group G] {a t v : G}
    (htv : t * v * t⁻¹ = v ∨ t * v * t⁻¹ = v⁻¹)
    (hatv : (a * t) * v * (a * t)⁻¹ = v ∨ (a * t) * v * (a * t)⁻¹ = v⁻¹) :
    a * v * a⁻¹ = v ∨ a * v * a⁻¹ = v⁻¹ := by
  have hat : (a * t) * v * (a * t)⁻¹ = a * (t * v * t⁻¹) * a⁻¹ := by group
  rcases htv with h | h <;> rcases hatv with h' | h'
  · exact Or.inl (by rwa [hat, h] at h')
  · exact Or.inr (by rwa [hat, h] at h')
  · refine Or.inr ?_
    rw [hat, h] at h'
    simpa [mul_assoc] using congrArg Inv.inv h'
  · refine Or.inl ?_
    rw [hat, h] at h'
    simpa [mul_assoc] using congrArg Inv.inv h'

private lemma conj_eq_self_of_conj_eq_inv_of_odd {G : Type*} [Group G] {a v : G}
    (hodd : Odd (orderOf a)) (h : a * v * a⁻¹ = v⁻¹) : a * v * a⁻¹ = v := by
  have h2 : a ^ 2 * v * (a ^ 2)⁻¹ = v := by
    calc a ^ 2 * v * (a ^ 2)⁻¹ = a * (a * v * a⁻¹) * a⁻¹ := by
          rw [pow_two]; group
      _ = a * v⁻¹ * a⁻¹ := by rw [h]
      _ = (a * v * a⁻¹)⁻¹ := by group
      _ = (v⁻¹)⁻¹ := by rw [h]
      _ = v := inv_inv v
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one a) hodd 1
  rw [pow_one, pow_mul] at hm
  have h2c : a ^ 2 ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a ^ 2 * v = (a ^ 2 * v * (a ^ 2)⁻¹) * a ^ 2 := by group
      _ = v * a ^ 2 := by rw [h2]
  have hac : a ∈ Subgroup.centralizer ({v} : Set G) := by
    rw [hm]
    exact Subgroup.pow_mem _ h2c m
  rw [Subgroup.mem_centralizer_singleton_iff] at hac
  rw [hac]; group


theorem false_of_inverted_of_card_eq_cube {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {V : Subgroup G} (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hV : Nat.card V = p ^ 3) {a t : G} (ha : a ∈ Subgroup.normalizer (V : Set G))
    (ht : t ∈ Subgroup.normalizer (V : Set G)) (hfix : ∀ v ∈ V, a * v * a⁻¹ = v → v = 1)
    (hodd : Odd (orderOf a)) (ht2 : t ^ 2 = 1) (hinv : t * a * t⁻¹ = a⁻¹) : False := by
  classical
  haveI : IsMulCommutative V := ⟨⟨fun x y => Subtype.ext (hVab x x.2 y y.2)⟩⟩
  have hat : a * t ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff] at ha ht ⊢
    intro v
    rw [show a * t * v * (a * t)⁻¹ = a * (t * v * t⁻¹) * a⁻¹ by group]
    exact (ht v).trans (ha (t * v * t⁻¹))
  have hat2 : (a * t) ^ 2 = 1 := by
    calc (a * t) ^ 2 = a * (t * a * t⁻¹) * (t * t) := by rw [pow_two]; group
      _ = a * a⁻¹ * (t * t) := by rw [hinv]
      _ = 1 := by rw [mul_inv_cancel, ← pow_two, ht2]; group
  obtain ⟨S, hScard, hS⟩ := exists_large_fixed_or_anti hVab hV ht ht2
  obtain ⟨T, hTcard, hT⟩ := exists_large_fixed_or_anti hVab hV hat hat2
  have hinf : S ⊓ T ≠ ⊥ := inf_ne_bot_of_large hV hScard hTcard
  obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  let w : V := (v : V)
  have hwS : w ∈ S := (Subgroup.mem_inf.mp v.2).1
  have hwT : w ∈ T := (Subgroup.mem_inf.mp v.2).2
  have hwne : w ≠ 1 := fun h => hv1 (Subtype.ext h)
  have htv : t * (w : G) * t⁻¹ = (w : G) ∨ t * (w : G) * t⁻¹ = ((w : G)⁻¹) := by
    rcases hS with h | h
    · exact Or.inl (h w hwS)
    · exact Or.inr (h w hwS)
  have hatv : (a * t) * (w : G) * (a * t)⁻¹ = (w : G) ∨
      (a * t) * (w : G) * (a * t)⁻¹ = ((w : G)⁻¹) := by
    rcases hT with h | h
    · exact Or.inl (h w hwT)
    · exact Or.inr (h w hwT)
  rcases conj_eq_or_inv htv hatv with h | h
  · exact hwne (Subtype.ext (hfix (w : G) w.2 h))
  · exact hwne (Subtype.ext (hfix (w : G) w.2 (conj_eq_self_of_conj_eq_inv_of_odd hodd h)))


variable {L : Type} [Group L] [Finite L] {p d : ℕ} {Y : Subgroup L}

private lemma min_normal_of_normal_pGroup (h : SporOvergroupData L p d Y)
    {R : Subgroup L} (hRp : IsPGroup p R) (hRY : R ≤ Y)
    (hRn : (R.subgroupOf Y).Normal) (hR : R ≠ ⊥) :
    ∃ M : Subgroup ↥Y, M.Normal ∧ M ≠ ⊥ ∧ M ≤ R.subgroupOf Y ∧
      IsElementaryAbelian p M ∧ ∀ K : Subgroup ↥Y, K.Normal → K ≤ M → K = ⊥ ∨ K = M := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hRsub_ne_bot : R.subgroupOf Y ≠ ⊥ := by
    intro hbot
    have hmap := congrArg (Subgroup.map Y.subtype) hbot
    rw [Subgroup.map_subgroupOf_eq_of_le hRY, Subgroup.map_bot] at hmap
    exact hR hmap
  obtain ⟨M, hMnorm, hMle, hMne, hMmin⟩ :=
    CFSG.exists_minimal_normal_le (R.subgroupOf Y) hRn hRsub_ne_bot
  have hRsubp : IsPGroup p (R.subgroupOf Y) := hRp.comap_subtype
  have hMp : IsPGroup p M := hRsubp.to_le hMle
  have hMmin' : ∀ K : Subgroup ↥Y, K.Normal → K ≤ M → K = ⊥ ∨ K = M := by
    intro K hKn hKle
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · exact Or.inr (hMmin K hKn hKle hKbot)
  have hMelem : IsElementaryAbelian p M :=
    CFSG.isElementaryAbelian_of_minimalNormal hMnorm hMp hMne hMmin'
  exact ⟨M, hMnorm, hMne, hMle, hMelem, hMmin'⟩

private lemma sylow_subgroupOf_le_of_data (h : SporOvergroupData L p d Y)
    (Q : Sylow p L) (hQle : (Q : Subgroup L) ≤ Y) :
    ∃ QY : Sylow p Y, (QY : Subgroup Y) = (Q : Subgroup L).subgroupOf Y := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p (Q : Subgroup L) Y := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hQle, Q.isPGroup', ?_⟩
    exact fun hdvd => Q.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hQle))
  exact hQsyl.exists_sylow_eq_subgroupOf

private lemma map_normal_pSubgroup_le_sylow (h : SporOvergroupData L p d Y)
    {M : Subgroup ↥Y} (hMnorm : M.Normal) (hMp : IsPGroup p M)
    {Q : Sylow p L} (hQle : (Q : Subgroup L) ≤ Y) :
    M.map Y.subtype ≤ (Q : Subgroup L) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨QY, hQY⟩ := sylow_subgroupOf_le_of_data h Q hQle
  have hMleQY : M ≤ (QY : Subgroup Y) := IsPGroup.le_sylow_of_normal hMp QY
  have hMleQsub : M ≤ (Q : Subgroup L).subgroupOf Y := by
    rwa [hQY] at hMleQY
  calc M.map Y.subtype ≤ ((Q : Subgroup L).subgroupOf Y).map Y.subtype :=
        Subgroup.map_mono hMleQsub
    _ = (Q : Subgroup L) ⊓ Y := Subgroup.subgroupOf_map_subtype _ _
    _ = (Q : Subgroup L) := inf_eq_left.mpr hQle

private lemma centralizer_card_dvd_of_mem_map {M : Subgroup ↥Y} {z : L}
    (hz : z ∈ M.map Y.subtype) :
    Nat.card (Subgroup.centralizer (M : Set ↥Y)) ∣
      Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  classical
  have hmap_le : (Subgroup.centralizer (M : Set ↥Y)).map Y.subtype ≤
      Subgroup.centralizer ({z} : Set L) := by
    rintro x ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨m, hmM, hmz⟩ := Subgroup.mem_map.mp hz
    have hyc := Subgroup.mem_centralizer_iff.mp hy m hmM
    have hcomm : ((y : ↥Y) : L) * (m : L) = (m : L) * ((y : ↥Y) : L) := by
      exact (congrArg (fun t : ↥Y => (t : L)) hyc).symm
    change Y.subtype y * Y.subtype m = Y.subtype m * Y.subtype y at hcomm
    rw [hmz] at hcomm
    exact hcomm
  have hcard_eq : Nat.card ((Subgroup.centralizer (M : Set ↥Y)).map Y.subtype) =
      Nat.card (Subgroup.centralizer (M : Set ↥Y)) :=
    Subgroup.card_map_of_injective Y.subtype_injective
  rw [← hcard_eq]
  exact Subgroup.card_dvd_of_le hmap_le


private lemma exists_elem_abelian_map_of_normal_pGroup (h : SporOvergroupData L p d Y)
    {R : Subgroup L} (hRp : IsPGroup p R) (hRY : R ≤ Y) (hRn : (R.subgroupOf Y).Normal)
    (hR : R ≠ ⊥) :
    ∃ (M : Subgroup ↥Y) (V : Subgroup L) (k : ℕ), M.Normal ∧ M ≠ ⊥ ∧ M ≤ R.subgroupOf Y ∧
      IsElementaryAbelian p M ∧ V = M.map Y.subtype ∧ V ≤ Y ∧ (V.subgroupOf Y).Normal ∧
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ v ∈ V, v ^ p = 1) ∧
      Nat.card V = p ^ k ∧ 1 ≤ k ∧ k ≤ 3 := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨M, hMnorm, hMne, hMle, hMelem, hMmin⟩ :=
    min_normal_of_normal_pGroup h hRp hRY hRn hR
  haveI hMinst : IsElementaryAbelian p M := hMelem
  let V : Subgroup L := M.map Y.subtype
  have hVle : V ≤ Y := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    exact m.2
  have hVsub : (V.subgroupOf Y).Normal := by
    have hVsub_eq : V.subgroupOf Y = M := by
      refine Subgroup.map_subtype_inj.mp ?_
      calc (V.subgroupOf Y).map Y.subtype = V ⊓ Y := Subgroup.subgroupOf_map_subtype V Y
        _ = V := inf_eq_left.mpr hVle
        _ = M.map Y.subtype := rfl
    rw [hVsub_eq]
    exact hMnorm
  have hVele : IsElementaryAbelian p V := IsElementaryAbelian.map_subtype
  haveI hVinst : IsElementaryAbelian p V := hVele
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
    intro x hx y hy
    have h := hVele.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg (fun t : ↥V => (t : L)) h
  have hVp : ∀ v ∈ V, v ^ p = 1 := fun v hv =>
    elemPow_eq_one_of_isElementaryAbelian v hv
  have hVpGroup : IsPGroup p V := IsElementaryAbelian.isPGroup p V
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hVpGroup
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hMne
    refine Subgroup.map_subtype_inj.mp ?_
    simpa [V] using hbot
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    have hVcard : Nat.card V = 1 := by rw [hk, hk0', pow_zero]
    haveI hnt : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
    exact not_subsingleton V (Nat.card_eq_one_iff_unique.mp hVcard).1
  have hk3 : k ≤ 3 := by
    have hVopen : CFSG.Open.IsElemAbelian p V := ⟨hVele.toIsMulCommutative, hVp⟩
    have h1 : k ≤ CFSG.Open.pRank p (⊤ : Subgroup L) :=
      CFSG.SectionRank.le_pRank h.prime.one_lt (le_top : V ≤ ⊤) hVopen hk
    exact h1.trans h.rank_le
  exact ⟨M, V, k, hMnorm, hMne, hMle, hMelem, rfl, hVle, hVsub, hVab, hVp, hk, hk1, hk3⟩

private lemma exists_central_elem_of_normal_pGroup (h : SporOvergroupData L p d Y)
    {V : Subgroup L} {Q : Sylow p L}
    (hVQ : V ≤ (Q : Subgroup L)) (hQle : (Q : Subgroup L) ≤ Y)
    (hVle : V ≤ Y) (hVsub : (V.subgroupOf Y).Normal)
    (hVp : ∀ v ∈ V, v ^ p = 1) (hVne : V ≠ ⊥) :
    ∃ z : L, z ∈ V ∧ orderOf z = p ∧
      p ^ (Nat.card L).factorization p ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hVQsub_ne : V.subgroupOf (Q : Subgroup L) ≠ ⊥ := by
    intro hbot
    apply hVne
    have h := congrArg (Subgroup.map (Q : Subgroup L).subtype) hbot
    rwa [Subgroup.map_subgroupOf_eq_of_le hVQ, Subgroup.map_bot] at h
  have hVQsub_norm : (V.subgroupOf (Q : Subgroup L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVQ]
    have hYnorm : Y ≤ Subgroup.normalizer (V : Set L) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVle).mp hVsub
    exact hQle.trans hYnorm
  haveI hVQsub_inst : (V.subgroupOf (Q : Subgroup L)).Normal := hVQsub_norm
  have hinter : V.subgroupOf (Q : Subgroup L) ⊓ Subgroup.center ↥(Q : Subgroup L) ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      Q.isPGroup' (V.subgroupOf (Q : Subgroup L)) hVQsub_ne
  obtain ⟨zQ, hzQne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinter
  let z : L := (Q : Subgroup L).subtype zQ.1
  have hzV : z ∈ V := by
    have hmem : zQ.1 ∈ V.subgroupOf (Q : Subgroup L) := (Subgroup.mem_inf.mp zQ.2).1
    exact Subgroup.mem_subgroupOf.mp hmem
  have hzCenter : zQ.1 ∈ Subgroup.center ↥(Q : Subgroup L) := (Subgroup.mem_inf.mp zQ.2).2
  have hz_pow : z ^ p = 1 := hVp z hzV
  have hz_ne : z ≠ 1 := by
    intro hz1
    apply hzQne
    have h : (Q : Subgroup L).subtype zQ.1 = (Q : Subgroup L).subtype 1 := by
      simpa [z] using hz1
    exact Subtype.ext ((Q : Subgroup L).subtype_injective h)
  have hz_order : orderOf z = p := by
    have hdvd : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hz_pow
    rcases h.prime.eq_one_or_self_of_dvd (orderOf z) hdvd with h1 | hp
    · exact absurd (orderOf_eq_one_iff.mp h1) hz_ne
    · exact hp
  have hQ_cent : (Q : Subgroup L) ≤ Subgroup.centralizer ({z} : Set L) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcenter := Subgroup.mem_center_iff.mp hzCenter ⟨q, hq⟩
    simpa [z] using congrArg (Q : Subgroup L).subtype hcenter
  have hdvd : p ^ (Nat.card L).factorization p ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    have hcardQ : Nat.card (Q : Subgroup L) = p ^ (Nat.card L).factorization p :=
      Sylow.card_eq_multiplicity Q
    rw [← hcardQ]
    exact Subgroup.card_dvd_of_le hQ_cent
  exact ⟨z, hzV, hz_order, hdvd⟩

private lemma card_dvd_card_centralizer_mul_card_mulAut {X : Type*} [Group X] [Finite X]
    (N : Subgroup X) [hN : N.Normal] :
    Nat.card X ∣ Nat.card (Subgroup.centralizer (N : Set X)) * Nat.card (MulAut N) := by
  have hcard : Nat.card (Subgroup.normalizer (N : Set X)) = Nat.card X := by
    rw [Subgroup.normalizer_eq_top N, Subgroup.card_top]
  rw [← hcard, ← CFSG.GH74.Generic.S45.card_range_normalizerMonoidHom_mul N,
    mul_comm (Nat.card (Subgroup.centralizer (N : Set X)))]
  exact mul_dvd_mul_right (Subgroup.card_subgroup_dvd_card _) _

theorem exists_elem_central_of_normal_pGroup (h : SporOvergroupData L p d Y) {R : Subgroup L}
    (hRp : IsPGroup p R) (hRY : R ≤ Y) (hRn : (R.subgroupOf Y).Normal) (hR : R ≠ ⊥) :
    ∃ (V : Subgroup L) (k : ℕ) (z : L), V ≤ Y ∧ (V.subgroupOf Y).Normal ∧
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧ (∀ v ∈ V, v ^ p = 1) ∧ Nat.card V = p ^ k ∧
      1 ≤ k ∧ k ≤ 3 ∧ z ∈ V ∧ orderOf z = p ∧
      p ^ (Nat.card L).factorization p ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) ∧
      Nat.card Y ∣ (∏ i : Fin k, (p ^ k - p ^ (i : ℕ))) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨M, V, k, hMnorm, hMne, hMle, hMelem, hVeq, hVle, hVsub, hVab, hVp, hk, hk1, hk3⟩ :=
    exists_elem_abelian_map_of_normal_pGroup h hRp hRY hRn hR
  haveI hMinst : IsElementaryAbelian p M := hMelem
  obtain ⟨Q, hQle⟩ := exists_sylow_le_of_data h
  have hMp : IsPGroup p M := IsElementaryAbelian.isPGroup p M
  have hVQ : V ≤ (Q : Subgroup L) := by
    rw [hVeq]
    exact map_normal_pSubgroup_le_sylow h hMnorm hMp hQle
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hMne
    refine Subgroup.map_subtype_inj.mp ?_
    rw [hVeq] at hbot
    rw [Subgroup.map_bot]
    exact hbot
  obtain ⟨z, hzV, hz_order, hzdvd⟩ :=
    exists_central_elem_of_normal_pGroup h hVQ hQle hVle hVsub hVp hVne
  have hzMap : z ∈ M.map Y.subtype := by
    rw [← hVeq]
    exact hzV
  have hMcard : Nat.card M = p ^ k := by
    rw [← Subgroup.card_map_of_injective (K := M) Y.subtype_injective, ← hVeq]
    exact hk
  haveI hMnorm_inst : M.Normal := hMnorm
  have hYdvd : Nat.card ↥Y ∣
      Nat.card (Subgroup.centralizer (M : Set ↥Y)) * Nat.card (MulAut M) :=
    card_dvd_card_centralizer_mul_card_mulAut M
  have hAutdvd : Nat.card (MulAut M) ∣ ∏ i : Fin k, (p ^ k - p ^ (i : ℕ)) :=
    CFSG.LinearAlgebra.CoprimeActions.BinarySmallAutomorphismOddRank.card_mulAut_dvd_GL
      (E := ↥M) (n := k) hMcard
  have hCentdvd : Nat.card (Subgroup.centralizer (M : Set ↥Y)) ∣
      Nat.card (Subgroup.centralizer ({z} : Set L)) :=
    centralizer_card_dvd_of_mem_map hzMap
  refine ⟨V, k, z, hVle, hVsub, hVab, hVp, hk, hk1, hk3, hzV, hz_order, hzdvd, ?_⟩
  have hstep : Nat.card (Subgroup.centralizer (M : Set ↥Y)) * Nat.card (MulAut M) ∣
      (∏ i : Fin k, (p ^ k - p ^ (i : ℕ))) * Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    rw [mul_comm]
    exact mul_dvd_mul hAutdvd hCentdvd
  exact dvd_trans hYdvd hstep

theorem op_eq_bot_of_data (h : SporOvergroupData L p d Y)
    (hC : ∀ z : L, orderOf z = p →
      p ^ (Nat.card L).factorization p ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ^ (Nat.card L).factorization d ∣ (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2) *
        Nat.card (Subgroup.centralizer ({z} : Set L))) :
    ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥ := by
  intro R hRp hRY hRn
  by_contra hR
  obtain ⟨V, k, z, hVle, hVsub, hVab, hVp, hk, hk1, hk3, hzV, hz_order, hzdvd, hYdvd⟩ :=
    exists_elem_central_of_normal_pGroup h hRp hRY hRn hR
  have hdvdY : d ^ (Nat.card L).factorization d ∣ Nat.card Y :=
    (pow_factorization_dvd_card_of_data h).2
  have hdvdPk : d ^ (Nat.card L).factorization d ∣
      (∏ i : Fin k, (p ^ k - p ^ (i : ℕ))) * Nat.card (Subgroup.centralizer ({z} : Set L)) :=
    hdvdY.trans hYdvd
  have hprod_dvd : (∏ i : Fin k, (p ^ k - p ^ (i : ℕ))) ∣
      (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2) := by
    interval_cases k
    · simp only [Fin.prod_univ_one, pow_one, pow_zero]
      have h1 : p - 1 ∣ p ^ 3 - 1 := by
        simpa using Nat.sub_dvd_pow_sub_pow p 1 3
      have h2 : p - 1 ∣ (p ^ 3 - 1) * (p ^ 3 - p) := h1.trans (dvd_mul_right _ _)
      exact h2.trans (dvd_mul_right _ _)
    · simp only [Fin.prod_univ_two, pow_one, pow_zero]
      have h1 : p ^ 2 - 1 ∣ p ^ 3 - p := by
        refine ⟨p, ?_⟩
        rw [Nat.sub_mul]
        have hp3 : p ^ 3 = p ^ 2 * p := by ring
        rw [hp3, one_mul]
      have h2 : p ^ 2 - p ∣ p ^ 3 - p ^ 2 := by
        refine ⟨p, ?_⟩
        rw [Nat.sub_mul]
        have hp3 : p ^ 3 = p ^ 2 * p := by ring
        have hp2 : p * p = p ^ 2 := by ring
        rw [hp3, hp2]
      have h3 : (p ^ 2 - 1) * (p ^ 2 - p) ∣ (p ^ 3 - p) * (p ^ 3 - p ^ 2) :=
        Nat.mul_dvd_mul h1 h2
      simpa [mul_assoc] using h3.trans (dvd_mul_left _ _)
    · simp [Fin.prod_univ_three]
  have hdvdP3 : d ^ (Nat.card L).factorization d ∣
      (p ^ 3 - 1) * (p ^ 3 - p) * (p ^ 3 - p ^ 2) *
        Nat.card (Subgroup.centralizer ({z} : Set L)) := by
    refine dvd_trans hdvdPk ?_
    exact Nat.mul_dvd_mul hprod_dvd (dvd_refl _)
  exact hC z hz_order hzdvd hdvdP3

private lemma inverting_conj_core (h : SporOvergroupData L p d Y)
    {a t : L} (ha : orderOf a = d) (ht2 : t ^ 2 = 1) (hinv : t * a * t⁻¹ = a⁻¹) :
    ∃ a' t' : L, orderOf a' = d ∧ t' ^ 2 = 1 ∧ t' * a' * t'⁻¹ = a'⁻¹ ∧
      a' ∈ Y ∧ t' ∈ Y := by
  obtain ⟨D, hDsyl, hDne, hnorm⟩ := h.sylowD
  haveI : Fact d.Prime := ⟨h.d_prime⟩
  have hDcard : Nat.card D = d ^ (Nat.card (⊤ : Subgroup L)).factorization d := hDsyl.card_eq
  have hza : IsPGroup d (Subgroup.zpowers a) :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, ha, pow_one]⟩
  obtain ⟨g, -, hg⟩ := IsPGroup.exists_mem_conj_mem_of_card_eq (G := L) (p := d)
    (P := ⊤) (Q := D) (R := Subgroup.zpowers a) le_top hDcard le_top hza
  have hga : g⁻¹ * a * g ∈ D := hg a (Subgroup.mem_zpowers a)
  let a' := g⁻¹ * a * g
  let t' := g⁻¹ * t * g
  let φ : L ≃* L := MulAut.conj (g⁻¹)
  have hφa : φ a = a' := by
    dsimp [a', φ]
    group
  have hφt : φ t = t' := by
    dsimp [t', φ]
    group
  have ha'_order : orderOf a' = d := by
    rw [← hφa, ← ha]
    exact φ.orderOf_eq a
  have ha'_ne : a' ≠ 1 := by
    intro h1
    have h2 : orderOf a' = 1 := by rw [h1]; exact orderOf_one
    rw [ha'_order] at h2; exact h.d_prime.ne_one h2
  have ha'_D : a' ∈ D := hga
  have ht'2 : t' ^ 2 = 1 := by
    rw [← hφt, ← map_pow, ht2, map_one]
  have hinv'_eq : t' * a' * t'⁻¹ = a'⁻¹ := by
    rw [← hφt, ← hφa, ← map_inv, ← map_mul, ← map_mul, hinv, map_inv]
  have ha'_Y : a' ∈ Y := by
    have hle : Subgroup.zpowers a' ≤ D := Subgroup.zpowers_le.mpr ha'_D
    have hne : Subgroup.zpowers a' ≠ ⊥ := by
      simpa [Subgroup.zpowers_eq_bot] using ha'_ne
    exact hnorm (Subgroup.zpowers a') hle hne
      (Subgroup.le_normalizer (Subgroup.mem_zpowers a'))
  have ht'_Y : t' ∈ Y := by
    have hle : Subgroup.zpowers a' ≤ D := Subgroup.zpowers_le.mpr ha'_D
    have hne : Subgroup.zpowers a' ≠ ⊥ := by
      simpa [Subgroup.zpowers_eq_bot] using ha'_ne
    have hmem : t' ∈ Subgroup.normalizer ((Subgroup.zpowers a') : Set L) := by
      rw [CFSG.GroupTheory.mem_normalizer_zpowers_iff]
      rw [hinv'_eq]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a')
    exact hnorm (Subgroup.zpowers a') hle hne hmem
  exact ⟨a', t', ha'_order, ht'2, hinv'_eq, ha'_Y, ht'_Y⟩

private lemma false_of_inverting_rank_three (h : SporOvergroupData L p d Y)
    {V : Subgroup L} (hVle : V ≤ Y) (hVsub : (V.subgroupOf Y).Normal)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x)
    (hVp : ∀ v ∈ V, v ^ p = 1) (hVcard : Nat.card V = p ^ 3)
    (hinv : ∃ a t : L, orderOf a = d ∧ t ^ 2 = 1 ∧ t * a * t⁻¹ = a⁻¹)
    (hCd : ∀ v : L, orderOf v = p → ¬ d ∣ Nat.card (Subgroup.centralizer ({v} : Set L))) :
    False := by
  obtain ⟨a, t, ha, ht2, hinv_eq⟩ := hinv
  obtain ⟨a', t', ha'_order, ht'2, hinv'_eq, ha'_Y, ht'_Y⟩ :=
    inverting_conj_core h ha ht2 hinv_eq
  have hYleV : Y ≤ Subgroup.normalizer (V : Set L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVle).mp hVsub
  have ha'_N : a' ∈ Subgroup.normalizer (V : Set L) := hYleV ha'_Y
  have ht'_N : t' ∈ Subgroup.normalizer (V : Set L) := hYleV ht'_Y
  have hodd : Odd (orderOf a') := by
    rw [ha'_order]
    exact h.d_prime.odd_of_ne_two h.d_ne_two
  have hfix : ∀ v ∈ V, a' * v * a'⁻¹ = v → v = 1 := by
    intro v hv hfix_eq
    by_contra hvne
    have hv_order : orderOf v = p := by
      have hvdvd : orderOf v ∣ p := orderOf_dvd_iff_pow_eq_one.mpr (hVp v hv)
      rcases h.prime.eq_one_or_self_of_dvd (orderOf v) hvdvd with h1 | hp
      · exact absurd (orderOf_eq_one_iff.mp h1) hvne
      · exact hp
    have hcomm : a' * v = v * a' := mul_inv_eq_iff_eq_mul.mp hfix_eq
    have hcent : a' ∈ Subgroup.centralizer ({v} : Set L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm
    have hdvd_cent : d ∣ Nat.card (Subgroup.centralizer ({v} : Set L)) := by
      have hdvd_order : d ∣ orderOf a' := by rw [ha'_order]
      exact hdvd_order.trans (Subgroup.orderOf_dvd_natCard _ hcent)
    exact hCd v hv_order hdvd_cent
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact false_of_inverted_of_card_eq_cube hVab hVcard ha'_N ht'_N hfix hodd ht'2 hinv'_eq

theorem op_eq_bot_of_data_of_inverting (h : SporOvergroupData L p d Y)
    (hC2 : ∀ z : L, orderOf z = p →
      p ^ (Nat.card L).factorization p ∣ Nat.card (Subgroup.centralizer ({z} : Set L)) →
      ¬ d ^ (Nat.card L).factorization d ∣ (p ^ 2 - 1) * (p ^ 2 - p) *
        Nat.card (Subgroup.centralizer ({z} : Set L)))
    (hCd : ∀ v : L, orderOf v = p → ¬ d ∣ Nat.card (Subgroup.centralizer ({v} : Set L)))
    (hinv : ∃ a t : L, orderOf a = d ∧ t ^ 2 = 1 ∧ t * a * t⁻¹ = a⁻¹) :
    ∀ R : Subgroup L, IsPGroup p R → R ≤ Y → (R.subgroupOf Y).Normal → R = ⊥ := by
  intro R hRp hRY hRn
  by_contra hR
  obtain ⟨V, k, z, hVle, hVsub, hVab, hVp, hk, hk1, hk3, hzV, hz_order, hzdvd, hYdvd⟩ :=
    exists_elem_central_of_normal_pGroup h hRp hRY hRn hR
  have hdvdPk : d ^ (Nat.card L).factorization d ∣
      (∏ i : Fin k, (p ^ k - p ^ (i : ℕ))) * Nat.card (Subgroup.centralizer ({z} : Set L)) :=
    (pow_factorization_dvd_card_of_data h).2.trans hYdvd
  by_cases hk3' : k = 3
  · have hVcard : Nat.card V = p ^ 3 := by rw [hk, hk3']
    exact false_of_inverting_rank_three h hVle hVsub hVab hVp hVcard hinv hCd
  · have hk2 : k ≤ 2 := by omega
    have hprod_dvd : (∏ i : Fin k, (p ^ k - p ^ (i : ℕ))) ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
      interval_cases k
      · simp only [Fin.prod_univ_one, Fin.val_zero, pow_one, pow_zero]
        have h1 : p - 1 ∣ p ^ 2 - 1 := by
          simpa using Nat.sub_dvd_pow_sub_pow p 1 2
        exact h1.trans (dvd_mul_right _ _)
      · simp only [Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_one, pow_zero]
        exact dvd_refl _
    have hdvdP2 : d ^ (Nat.card L).factorization d ∣
        (p ^ 2 - 1) * (p ^ 2 - p) * Nat.card (Subgroup.centralizer ({z} : Set L)) := by
      refine dvd_trans hdvdPk ?_
      exact Nat.mul_dvd_mul hprod_dvd (dvd_refl _)
    exact hC2 z hz_order hzdvd hdvdP2

end CFSG.LocalAnalysis.AGL81I.Section3.SporBig

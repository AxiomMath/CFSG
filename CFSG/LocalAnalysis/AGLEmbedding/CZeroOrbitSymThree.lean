module

public import CFSG.LocalAnalysis.AGLEmbedding.CZeroOrbitLines
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.AS76bDefs

public section

namespace CFSG.AGLEmbedding.CZeroOrbit

open CFSG.Open Subgroup
open scoped Pointwise
open CFSG.ComponentClassification.AS76b (oUpperTwo)

variable {Y : Type} [Group Y] [Finite Y]

private def c3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private def s3 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

private theorem perm3_facts :
    c3 ^ 3 = 1 ∧ c3 ≠ 1 ∧ s3 ^ 2 = 1 ∧ s3 * c3 * s3⁻¹ = c3⁻¹ ∧
      (∀ x : Equiv.Perm (Fin 3), x ^ 3 = 1 → x = 1 ∨ x = c3 ∨ x = c3 ^ 2) ∧
      ∀ x : Equiv.Perm (Fin 3), x ^ 3 = 1 ∨ (x * s3⁻¹) ^ 3 = 1 := by
  decide

private theorem dvd_three_of_dvd_six {n : ℕ} (h6 : n ∣ 6) (hn : Odd n) : n ∣ 3 := by
  have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  interval_cases n <;> simp_all <;> contradiction

theorem symThree_data {T : Subgroup Y} (hT : IsSubnormal T ⊤)
    (hS : Nonempty (↥T ≃* Equiv.Perm (Fin 3))) :
    ∃ a t : Y, a ∈ T ∧ t ∈ T ∧ a ^ 3 = 1 ∧ a ≠ 1 ∧ t ^ 2 = 1 ∧ t * a * t⁻¹ = a⁻¹ ∧
      oUpperTwo T = zpowers a ∧ IsSubnormal (zpowers a) ⊤ ∧
      zpowers a ≤ pCoreOf 3 (⊤ : Subgroup Y) ∧
      (∀ d ∈ pCoreOf 3 (⊤ : Subgroup Y), d * t * d⁻¹ * t⁻¹ ∈ zpowers a) ∧
      (∀ x ∈ T, x ∈ zpowers a ∨ x * t⁻¹ ∈ zpowers a) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := hS
  obtain ⟨hc3, hc1, hs2, hsc, hcases, hsplit⟩ := perm3_facts
  set a : Y := ((e.symm c3 : ↥T) : Y) with ha
  set t : Y := ((e.symm s3 : ↥T) : Y) with ht
  have haT : a ∈ T := (e.symm c3).2
  have htT : t ∈ T := (e.symm s3).2
  have ha3 : a ^ 3 = 1 := by
    rw [ha, ← Subgroup.coe_pow, ← map_pow, hc3, map_one, Subgroup.coe_one]
  have ha1 : a ≠ 1 := by
    intro h
    apply hc1
    have : e.symm c3 = 1 := Subtype.ext h
    simpa using congrArg e this
  have ht2 : t ^ 2 = 1 := by
    rw [ht, ← Subgroup.coe_pow, ← map_pow, hs2, map_one, Subgroup.coe_one]
  have hta : t * a * t⁻¹ = a⁻¹ := by
    have := congrArg (fun g => ((e.symm g : ↥T) : Y)) hsc
    simpa [ha, ht] using this
  have hcube : ∀ x ∈ T, x ^ 3 = 1 → x ∈ zpowers a := by
    intro x hx hx3
    have h3 : e ⟨x, hx⟩ ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : ↥T) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    have hxe : (⟨x, hx⟩ : ↥T) = e.symm (e ⟨x, hx⟩) := (e.symm_apply_apply _).symm
    rcases hcases _ h3 with h | h | h
    · rw [h, map_one] at hxe
      have : x = 1 := congrArg Subtype.val hxe
      rw [this]
      exact one_mem _
    · rw [h] at hxe
      have : x = a := congrArg Subtype.val hxe
      rw [this]
      exact mem_zpowers a
    · rw [h, map_pow] at hxe
      have : x = a ^ 2 := by simpa [ha] using congrArg Subtype.val hxe
      rw [this]
      exact pow_mem (mem_zpowers a) 2
  have hcard : Nat.card ↥T = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hodd : ∀ x ∈ T, Odd (orderOf x) → x ^ 3 = 1 := by
    intro x hx hxo
    have h6 : orderOf x ∣ 6 := by
      rw [← hcard, ← Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_three_of_dvd_six h6 hxo)
  have h3el : ∀ x ∈ T, (∃ k : ℕ, x ^ (3 ^ k) = 1) → x ∈ zpowers a := by
    rintro x hx ⟨k, hk⟩
    refine hcube x hx (hodd x hx ?_)
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hk)
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hO2 : oUpperTwo T = zpowers a := by
    apply le_antisymm
    · exact (closure_le _).mpr fun x hx => hcube x hx.1 (hodd x hx.1 hx.2)
    · rw [zpowers_le]
      exact subset_closure ⟨haT, by rw [hoa]; decide⟩
  set D : Subgroup Y := pCoreOf 3 (⊤ : Subgroup Y) with hDdef
  have hD3 : IsPGroup 3 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 ⊤
  have hDN : ∀ g : Y, g ∈ normalizer (D : Set Y) := fun g =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 ⊤ (le_normalizer (mem_top g))
  have hDn : ∀ g d : Y, d ∈ D → g * d * g⁻¹ ∈ D := fun g d hd =>
    (mem_normalizer_iff.mp (hDN g) d).mp hd
  have hAn : ((zpowers a).subgroupOf T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    have hconj : (g : Y) * a * (g : Y)⁻¹ ∈ zpowers a := by
      refine hcube _ (T.mul_mem (T.mul_mem g.2 haT) (T.inv_mem g.2)) ?_
      rw [conj_pow, ha3, mul_one, mul_inv_cancel]
    have : ((g * n * g⁻¹ : ↥T) : Y) = ((g : Y) * a * (g : Y)⁻¹) ^ k := by
      rw [conj_zpow, hk]
      simp
    rw [this]
    exact zpow_mem hconj k
  have hA3 : IsPGroup 3 (zpowers a) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (a ^ k) ^ 3 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
  have hasn : IsSubnormal (zpowers a) ⊤ := IsSubnormal.step (zpowers_le.mpr haT) hAn hT
  have hAD : zpowers a ≤ D := SubnormalCommute.le_pCoreOf_of_isSubnormal hasn hA3
  have h2t : IsPGroup 2 (zpowers t) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    change (t ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hD2 : ¬ 2 ∣ Nat.card D := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hD3
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    omega
  have hE := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 2
    Nat.prime_two (zpowers t) D h2t hD2 (fun g _ => hDN g)
  have hET := SubnormalCommute.commutator_zpowers_le_of_isSubnormal hT hE htT le_top
  have hcomm : ∀ d ∈ D, d * t * d⁻¹ * t⁻¹ ∈ zpowers a := by
    intro d hd
    have hmem : d * t * d⁻¹ * t⁻¹ ∈ D := by
      have := D.mul_mem hd (hDn t d⁻¹ (D.inv_mem hd))
      simpa [mul_assoc] using this
    refine h3el _ (hET ?_) ?_
    · have := commutator_mem_commutator hd (mem_zpowers t)
      rwa [commutatorElement_def] at this
    · obtain ⟨k, hk⟩ := hD3 ⟨_, hmem⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hsplitT : ∀ x ∈ T, x ∈ zpowers a ∨ x * t⁻¹ ∈ zpowers a := by
    intro x hx
    rcases hsplit (e ⟨x, hx⟩) with h | h
    · left
      refine hcube x hx ?_
      have : e (⟨x, hx⟩ ^ 3) = e 1 := by rw [map_pow, h, map_one]
      simpa using congrArg Subtype.val (e.injective this)
    · right
      refine hcube _ (T.mul_mem hx (T.inv_mem htT)) ?_
      have hst : e.symm s3 = ⟨t, htT⟩ := rfl
      have : e ((⟨x, hx⟩ * (⟨t, htT⟩ : ↥T)⁻¹) ^ 3) = e 1 := by
        rw [map_pow, map_mul, map_inv, ← hst, MulEquiv.apply_symm_apply, h, map_one]
      simpa using congrArg Subtype.val (e.injective this)
  exact ⟨a, t, haT, htT, ha3, ha1, ht2, hta, hO2, hasn, hAD, hcomm, hsplitT⟩

private theorem exists_nat_of_mem_zpowers {G : Type*} [Group G] [Finite G] {x y : G}
    (h : y ∈ zpowers x) : ∃ n : ℕ, y = x ^ n := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf] at h
  simp only [Finset.mem_image, Finset.mem_range] at h
  obtain ⟨n, -, hn⟩ := h
  exact ⟨n, hn.symm⟩

private theorem exists_lt_three_of_mem_zpowers {G : Type*} [Group G] [Finite G] {a x : G}
    (ha3 : a ^ 3 = 1) (h : x ∈ zpowers a) : ∃ n : ℕ, n < 3 ∧ x = a ^ n := by
  obtain ⟨n, rfl⟩ := exists_nat_of_mem_zpowers h
  refine ⟨n % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, ha3, one_pow, one_mul]

private theorem isPGroup_zpowers {G : Type*} [Group G] [Finite G] {p k : ℕ} [Fact p.Prime]
    {g : G} (hg : g ^ p ^ k = 1) : IsPGroup p (zpowers g) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 (orderOf_dvd_of_pow_eq_one hg)
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem false_of_symThree_orbit {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (σ : MulAut Y)
    (hσ : σ ^ p ^ k = 1) {A : Subgroup Y} (hA : IsSubnormal A ⊤)
    (hS : Nonempty (↥A ≃* Equiv.Perm (Fin 3)))
    (hmove : (oUpperTwo A).map σ.toMonoidHom ≠ oUpperTwo A)
    (hrk : ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E ≤ 27) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, t, haA, htA, ha3, ha1, ht2, hta, hO2, hasn, haD, hcomm, hsplit⟩ :=
    symThree_data hA hS
  set D : Subgroup Y := pCoreOf 3 (⊤ : Subgroup Y) with hDdef
  have hD3 : IsPGroup 3 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 ⊤
  have hDnorm : D.Normal := ⟨fun n hn g => (mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 3 ⊤ (le_normalizer (mem_top g))) n).mp
      hn⟩
  have hDinv : ∀ g : MulAut Y, ∀ d ∈ D, g d ∈ D := by
    intro g d hd
    have hN : (D.map g.toMonoidHom).Normal := hDnorm.map _ g.surjective
    have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 (le_top : D.map g.toMonoidHom ≤ ⊤)
      (fun y _ => (normalizer_eq_top_iff.mpr hN).ge (mem_top y)) (hD3.map g.toMonoidHom)
    exact hle ⟨d, hd, rfl⟩
  have hAsn : ∀ i : ℕ, IsSubnormal (A.map (σ ^ i).toMonoidHom) ⊤ := by
    intro i
    have := hA.map (σ ^ i).toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ (σ ^ i).surjective] at this
  have hAS : ∀ i : ℕ, Nonempty (↥(A.map (σ ^ i).toMonoidHom) ≃* Equiv.Perm (Fin 3)) := fun i =>
    ⟨(A.equivMapOfInjective _ (σ ^ i).injective).symm.trans hS.some⟩
  have hai3 : ∀ i : ℕ, ((σ ^ i) a) ^ 3 = 1 := fun i => by rw [← map_pow, ha3, map_one]
  have haiD : ∀ i : ℕ, (σ ^ i) a ∈ D := fun i => hDinv _ _ (haD (mem_zpowers a))
  have hcommij : ∀ i j : ℕ, (σ ^ i) a * (σ ^ j) a = (σ ^ j) a * (σ ^ i) a := by
    intro i j
    have hB3 : IsPGroup 3 (zpowers ((σ ^ j) a)) := isPGroup_zpowers (k := 1) (by simpa using hai3 j)
    have hBs : IsSubnormal (zpowers ((σ ^ j) a)) ⊤ := by
      have := hasn.map (σ ^ j).toMonoidHom
      rwa [MonoidHom.map_zpowers, Subgroup.map_top_of_surjective _ (σ ^ j).surjective] at this
    have hx : (σ ^ i) a ∈ oUpperTwo (A.map (σ ^ i).toMonoidHom) := by
      rw [← SUPair.map_oUpperTwo, hO2]
      exact ⟨a, mem_zpowers a, rfl⟩
    exact (SubnormalCommute.commute_oUpperTwo_of_symThree (hAsn i) (hAS i) hB3 hBs _ hx _
      (mem_zpowers _)).symm
  have hcommi : ∀ i : ℕ, ∀ d ∈ D, d * (σ ^ i) t * d⁻¹ * ((σ ^ i) t)⁻¹ ∈ zpowers ((σ ^ i) a) := by
    intro i d hd
    have hd' : (σ ^ i).symm d ∈ D := hDinv _ _ hd
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hcomm _ hd')
    refine mem_zpowers_iff.mpr ⟨m, ?_⟩
    have := congrArg (σ ^ i) hm
    simpa [map_mul, map_inv, map_zpow] using this
  set gens : Set Y := Set.range fun i : ℕ => (σ ^ i) a with hgens
  set F : Subgroup Y := closure gens with hFdef
  have hpair : gens.Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    exact hcommij i j
  have hFc : IsMulCommutative F := Subgroup.isMulCommutative_closure hpair
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hF3 : ∀ x ∈ F, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hai3 i
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy => rw [(Commute.mul_pow (hFcomm x hx y hy) 3), ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hFE : IsElemAbelian 3 F := ⟨hFc, hF3⟩
  have hFD : F ≤ D := (closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact haiD i)
  have haF : a ∈ F := subset_closure ⟨0, by simp⟩
  have haiF : ∀ i : ℕ, (σ ^ i) a ∈ F := fun i => subset_closure ⟨i, rfl⟩
  have hFσ : ∀ n : ℕ, F.map (σ ^ n).toMonoidHom = F := by
    intro n
    have hle : F.map (σ ^ n).toMonoidHom ≤ F := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      have : (σ ^ n).toMonoidHom ((σ ^ i) a) = (σ ^ (n + i)) a := by
        rw [pow_add, MulAut.mul_apply]
        rfl
      rw [this]
      exact haiF _
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (σ ^ n).injective])
  have hFcard : ∃ r : ℕ, r ≤ 3 ∧ Nat.card F = 3 ^ r := by
    obtain ⟨r, hr⟩ := (hD3.to_le hFD).exists_card_eq
    refine ⟨r, ?_, hr⟩
    have h27 := hrk F hFE
    rw [hr] at h27
    by_contra h
    have : 3 ^ 4 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨r, hr3, hFr⟩ := hFcard
  set σF : MulAut ↥F := restrictAut σ F (by simpa using hFσ 1) with hσFdef
  have hσFpow : ∀ n : ℕ, ∀ x : ↥F, ((σF ^ n) x : Y) = (σ ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, MulAut.mul_apply, hσFdef, restrictAut_apply]
  have hσF : σF ^ p ^ k = 1 := by
    ext x
    rw [hσFpow, hσ]
    rfl
  have hσa : σ a ≠ a := by
    intro h
    apply hmove
    rw [hO2, MonoidHom.map_zpowers]
    change zpowers (σ a) = zpowers a
    rw [h]
  set G₁ : Subgroup (MulAut ↥F) := zpowers σF with hG₁
  have hG₁p : IsPGroup p G₁ := isPGroup_zpowers hσF
  set C : Subgroup ↥F :=
    { carrier := {x | σF x = x}
      mul_mem' := fun {x y} hx hy => by
        change σF (x * y) = x * y
        rw [map_mul, show σF x = x from hx, show σF y = y from hy]
      one_mem' := map_one σF
      inv_mem' := fun {x} hx => by
        change σF x⁻¹ = x⁻¹
        rw [map_inv, show σF x = x from hx] } with hCdef
  have hfix : MulAction.fixedPoints ↥G₁ ↥F = (C : Set ↥F) := by
    ext x
    constructor
    · intro hx
      exact hx ⟨σF, mem_zpowers σF⟩
    · intro hx g
      obtain ⟨n, hn⟩ := exists_nat_of_mem_zpowers g.2
      change (g : MulAut ↥F) x = x
      rw [hn]
      clear hn
      induction n with
      | zero => rfl
      | succ n ih => rw [pow_succ, MulAut.mul_apply, show σF x = x from hx, ih]
  have hmod := hG₁p.card_modEq_card_fixedPoints ↥F
  rw [hfix] at hmod
  obtain ⟨s, hs⟩ : ∃ s : ℕ, Nat.card C = 3 ^ s := by
    have hdvd : Nat.card C ∣ 3 ^ r := hFr ▸ Subgroup.card_subgroup_dvd_card C
    obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact ⟨s, hs⟩
  have hsr : s < r := by
    have hsle : s ≤ r := by
      have hle : Nat.card C ≤ Nat.card ↥F := Subgroup.card_le_card_group C
      rw [hs, hFr] at hle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    rcases hsle.lt_or_eq with h | h
    · exact h
    · exfalso
      have htop : C = ⊤ := Subgroup.eq_top_of_card_eq C (by rw [hs, hFr, h])
      have : σF ⟨a, haF⟩ = ⟨a, haF⟩ := by
        have : (⟨a, haF⟩ : ↥F) ∈ C := htop ▸ mem_top _
        exact this
      exact hσa (congrArg Subtype.val this)
  rw [SetLike.coe_sort_coe, hs, hFr] at hmod
  have hdvd : p ∣ 3 ^ r - 3 ^ s :=
    (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right (by norm_num) hsr.le)).mp hmod.symm
  have hkey : p = 13 ∧ r = 3 ∧ s = 0 := by
    have hp2 := hp.two_le
    interval_cases r <;> interval_cases s <;> norm_num at hdvd <;>
      (have := Nat.le_of_dvd (by norm_num) hdvd; interval_cases p <;> revert hp hdvd <;> norm_num)
  obtain ⟨rfl, rfl, rfl⟩ := hkey
  have hCbot : ∀ x : ↥F, σF x = x → x = 1 := by
    intro x hx
    have hC1 : Nat.card C = 1 := by rw [hs, pow_zero]
    have := (Subgroup.card_eq_one.mp hC1)
    have hxC : x ∈ C := hx
    rw [this] at hxC
    exact hxC
  have hF3' : ∀ x : ↥F, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hF3 x x.2)
  have hcommF : ∀ x y : ↥F, x * y = y * x := fun x y => Subtype.ext (hFcomm x x.2 y y.2)
  have hFcard : Nat.card ↥F = 27 := by rw [hFr]; norm_num
  have hΛ : Nat.card ↥(lines ↥F) = 13 := by
    have h := two_mul_card_lines_add_one hF3'
    have e : ↥(lines ↥F) ≃ {ℓ : Subgroup ↥F // Nat.card ℓ = 3} :=
      Equiv.subtypeEquivRight fun _ => mem_lines
    rw [Nat.card_congr e]
    omega
  have hσFapp : ∀ x : ↥F, (σF x : Y) = σ x := fun x => rfl
  have hnofix : ∀ ℓ : ↥(lines ↥F), σF • (ℓ : Subgroup ↥F) ≠ ℓ := by
    intro ℓ hℓ
    have h3 : Nat.card (ℓ : Subgroup ↥F) = 3 := mem_lines.mp ℓ.2
    obtain ⟨x, hxℓ, hx1⟩ : ∃ x ∈ (ℓ : Subgroup ↥F), x ≠ 1 := by
      by_contra h
      push Not at h
      have : (ℓ : Subgroup ↥F) = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
      rw [this, Subgroup.card_bot] at h3
      norm_num at h3
    have hox : orderOf x = 3 := orderOf_eq_prime (hF3' x) hx1
    have hℓx : (ℓ : Subgroup ↥F) = zpowers x := by
      symm
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hxℓ) ?_
      rw [h3, Nat.card_zpowers, hox]
    have hσx : σF x ∈ zpowers x := by
      rw [← hℓx]
      have := Subgroup.smul_mem_pointwise_smul x σF _ hxℓ
      rwa [hℓ, MulAut.smul_def] at this
    obtain ⟨n, hn3, hn⟩ := exists_lt_three_of_mem_zpowers (hF3' x) hσx
    interval_cases n
    · apply hx1
      rw [pow_zero] at hn
      exact σF.injective (by rw [hn, map_one])
    · exact hx1 (hCbot x (by rw [hn, pow_one]))
    · have h2 : (σF ^ 2) x = x := by
        rw [pow_two, MulAut.mul_apply, hn, map_pow, hn, ← pow_mul,
          show 2 * 2 = 3 + 1 from rfl, pow_succ, hF3', one_mul]
      have hcop : Nat.Coprime 2 (orderOf σF) :=
        (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 13)).coprime_dvd_right
          (orderOf_dvd_of_pow_eq_one hσF)
      obtain ⟨c, hc⟩ := exists_pow_eq_self_of_coprime hcop
      have hall : ∀ m : ℕ, ((σF ^ 2) ^ m) x = x := by
        intro m
        induction m with
        | zero => rfl
        | succ m ih => rw [pow_succ, MulAut.mul_apply, h2, ih]
      exact hx1 (hCbot x (by rw [← hc]; exact hall c))
  set N : Subgroup Y := normalizer (F : Set Y) with hNdef
  have htinv : ∀ i : ℕ, ((σ ^ i) t)⁻¹ = (σ ^ i) t := by
    intro i
    rw [← map_inv]
    congr 1
    rw [inv_eq_iff_mul_eq_one, ← sq, ht2]
  have htconj : ∀ i : ℕ, ∀ x ∈ F, (σ ^ i) t * x * ((σ ^ i) t)⁻¹ ∈ F := by
    intro i x hx
    have h := hcommi i x⁻¹ (D.inv_mem (hFD hx))
    rw [inv_inv] at h
    have hmem : x⁻¹ * (σ ^ i) t * x * ((σ ^ i) t)⁻¹ ∈ F := zpowers_le.mpr (haiF i) h
    have e : (σ ^ i) t * x * ((σ ^ i) t)⁻¹ = x * (x⁻¹ * (σ ^ i) t * x * ((σ ^ i) t)⁻¹) := by group
    rw [e]
    exact F.mul_mem hx hmem
  have htiN : ∀ i : ℕ, (σ ^ i) t ∈ N := by
    intro i
    rw [hNdef, mem_normalizer_iff]
    intro h
    refine ⟨htconj i h, fun hh => ?_⟩
    have := htconj i _ hh
    have e : h = (σ ^ i) t * ((σ ^ i) t * h * ((σ ^ i) t)⁻¹) * ((σ ^ i) t)⁻¹ := by
      nth_rewrite 2 [← htinv i]
      nth_rewrite 3 [htinv i]
      group
    rw [e]
    exact this
  set ρ : ↥N →* MulAut ↥F := conjRestrict F with hρdef
  have hρF : ∀ y (hy : y ∈ N), y ∈ F → ρ ⟨y, hy⟩ = 1 := by
    intro y hy hyF
    ext x
    change y * x * y⁻¹ = x
    rw [hFcomm y hyF x x.2, mul_inv_cancel_right]
  set τ : ℕ → MulAut ↥F := fun i => ρ ⟨(σ ^ i) t, htiN i⟩ with hτdef
  have hτ2 : ∀ i : ℕ, τ i ^ 2 = 1 := by
    intro i
    change ρ ⟨(σ ^ i) t, htiN i⟩ ^ 2 = 1
    rw [← map_pow]
    have : (⟨(σ ^ i) t, htiN i⟩ : ↥N) ^ 2 = 1 :=
      Subtype.ext (by change ((σ ^ i) t) ^ 2 = 1; rw [← map_pow, ht2, map_one])
    rw [this, map_one]
  have hmapz : ∀ (i : ℕ) (y : Y), y ∈ zpowers a → (σ ^ i) y ∈ zpowers ((σ ^ i) a) := by
    intro i y hy
    have h : (σ ^ i).toMonoidHom y ∈ zpowers ((σ ^ i).toMonoidHom a) := by
      rw [← MonoidHom.map_zpowers]
      exact ⟨y, hy, rfl⟩
    exact h
  have hAiN : ∀ i : ℕ, A.map (σ ^ i).toMonoidHom ≤ N := by
    rintro i _ ⟨y, hy, rfl⟩
    rcases hsplit y hy with h | h
    · exact le_normalizer (zpowers_le.mpr (haiF i) (hmapz i y h))
    · have hm := hmapz i _ h
      have e : (σ ^ i).toMonoidHom y = (σ ^ i) (y * t⁻¹) * (σ ^ i) t := by
        change (σ ^ i) y = _
        rw [map_mul, map_inv, inv_mul_cancel_right]
      rw [e]
      exact N.mul_mem (le_normalizer (zpowers_le.mpr (haiF i) hm)) (htiN i)
  have himg : ∀ i : ℕ, ((A.map (σ ^ i).toMonoidHom).subgroupOf N).map ρ ≤ zpowers (τ i) := by
    rintro i _ ⟨⟨x, hxN⟩, hxA, rfl⟩
    have hxA' : x ∈ A.map (σ ^ i).toMonoidHom := mem_subgroupOf.mp hxA
    obtain ⟨y, hy, rfl⟩ := hxA'
    rcases hsplit y hy with h | h
    · rw [hρF _ hxN (zpowers_le.mpr (haiF i) (hmapz i y h))]
      exact one_mem _
    · have hyF : (σ ^ i) (y * t⁻¹) ∈ F := zpowers_le.mpr (haiF i) (hmapz i _ h)
      have e : (⟨(σ ^ i).toMonoidHom y, hxN⟩ : ↥N) =
          ⟨(σ ^ i) (y * t⁻¹), le_normalizer hyF⟩ * ⟨(σ ^ i) t, htiN i⟩ := by
        apply Subtype.ext
        change (σ ^ i) y = (σ ^ i) (y * t⁻¹) * (σ ^ i) t
        rw [map_mul, map_inv, inv_mul_cancel_right]
      rw [e, map_mul, hρF _ _ hyF, one_mul]
      exact mem_zpowers _
  have himg2 : ∀ i : ℕ, IsPGroup 2 (((A.map (σ ^ i).toMonoidHom).subgroupOf N).map ρ) :=
    fun i => (isPGroup_zpowers (k := 1) (by simpa using hτ2 i)).to_le (himg i)
  have himgsn : ∀ i : ℕ,
      IsSubnormal (((A.map (σ ^ i).toMonoidHom).subgroupOf N).map ρ) ρ.range := by
    intro i
    have h1 := (hAsn i).inf_of_le (le_top : N ≤ ⊤)
    rw [inf_of_le_left (hAiN i)] at h1
    have h2 := h1.comap N.subtype
    have h2' : IsSubnormal ((A.map (σ ^ i).toMonoidHom).subgroupOf N) ⊤ := by
      have e : N.comap N.subtype = ⊤ := Subgroup.subgroupOf_self N
      rw [e] at h2
      exact h2
    have h3 := h2'.map ρ
    rwa [← MonoidHom.range_eq_map] at h3
  have hτT : ∀ i : ℕ, τ i ∈ pCoreOf 2 ρ.range := by
    intro i
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle := SubnormalCommute.le_pCoreOf_of_isSubnormal (himgsn i) (himg2 i)
    exact hle ⟨⟨(σ ^ i) t, htiN i⟩, mem_subgroupOf.mpr ⟨t, htA, rfl⟩, rfl⟩
  set T : Subgroup (MulAut ↥F) := closure (Set.range τ) with hTdef
  have hT2 : IsPGroup 2 T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ρ.range).to_le
      ((closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hτT i))
  have hσinv : ∀ x : ↥F, ((σF⁻¹ x : ↥F) : Y) = σ⁻¹ x := by
    intro x
    have h : σ ((σF⁻¹ x : ↥F) : Y) = x := by
      rw [← hσFapp]
      exact congrArg Subtype.val (MulAut.apply_inv_self _ σF x)
    rw [← h, MulAut.inv_apply_self]
  have hστ : ∀ i : ℕ, σF * τ i * σF⁻¹ = τ (i + 1) := by
    intro i
    ext x
    change σ ((σ ^ i) t * ((σF⁻¹ x : ↥F) : Y) * ((σ ^ i) t)⁻¹) =
      (σ ^ (i + 1)) t * x * ((σ ^ (i + 1)) t)⁻¹
    rw [hσinv, map_mul, map_mul, map_inv, MulAut.apply_inv_self, pow_succ', MulAut.mul_apply]
  have hσN : σF ∈ normalizer (T : Set (MulAut ↥F)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    have hle : T.map (MulAut.conj σF).toMonoidHom ≤ T := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      change σF * τ i * σF⁻¹ ∈ T
      rw [hστ]
      exact subset_closure ⟨i + 1, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj σF).injective])
  have hG₁N : G₁ ≤ normalizer (T : Set (MulAut ↥F)) := zpowers_le.mpr hσN
  obtain ⟨ℓ₁, hℓ₁⟩ := hT2.nonempty_fixed_point_of_prime_not_dvd_card ↥(lines ↥F)
    (by rw [hΛ]; norm_num)
  obtain ⟨n, hn⟩ := hG₁p.card_orbit ℓ₁
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    have hmem : (⟨σF, mem_zpowers σF⟩ : ↥G₁) • ℓ₁ ∈ MulAction.orbit ↥G₁ ℓ₁ :=
      MulAction.mem_orbit _ _
    have hself : ℓ₁ ∈ MulAction.orbit ↥G₁ ℓ₁ := MulAction.mem_orbit_self _
    obtain ⟨u, hu⟩ := Nat.card_eq_one_iff_exists.mp hn
    have heq : (⟨σF, mem_zpowers σF⟩ : ↥G₁) • ℓ₁ = ℓ₁ :=
      congrArg Subtype.val ((hu ⟨_, hmem⟩).trans (hu ⟨_, hself⟩).symm)
    apply hnofix ℓ₁
    have := congrArg Subtype.val heq
    change ((σF • ℓ₁ : ↥(lines ↥F)) : Subgroup ↥F) = ℓ₁ at this
    rwa [SubMulAction.val_smul] at this
  have horbit : MulAction.orbit ↥G₁ ℓ₁ = Set.univ := by
    rw [Set.eq_univ_iff_ncard, hΛ, ← Nat.card_coe_set_eq, hn]
    have hle : 13 ^ n ≤ 13 := by
      rw [← hn, ← hΛ, Nat.card_coe_set_eq]
      exact Set.ncard_le_card _
    have h1 : 13 ^ 1 ≤ 13 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn0)
    have h2 : n ≤ 1 := by
      by_contra h
      have : 13 ^ 2 ≤ 13 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : n = 1 := by omega
    rw [this, pow_one]
  have hallfix : ∀ ℓ : ↥(lines ↥F), ∀ τ' ∈ T, τ' • (ℓ : Subgroup ↥F) = ℓ := by
    intro ℓ τ' hτ'
    have hℓ : ℓ ∈ MulAction.orbit ↥G₁ ℓ₁ := horbit ▸ Set.mem_univ ℓ
    obtain ⟨g, rfl⟩ := hℓ
    have hconjT : (g : MulAut ↥F)⁻¹ * τ' * g ∈ T := by
      have h := (mem_normalizer_iff.mp (hG₁N (inv_mem g.2)) τ').mp hτ'
      simpa using h
    have hfix1 := congrArg Subtype.val (hℓ₁ ⟨_, hconjT⟩)
    change ((((g : MulAut ↥F)⁻¹ * τ' * g) • ℓ₁ : ↥(lines ↥F)) : Subgroup ↥F) = ℓ₁ at hfix1
    rw [SubMulAction.val_smul] at hfix1
    change τ' • (((g : MulAut ↥F) • ℓ₁ : ↥(lines ↥F)) : Subgroup ↥F) =
      (((g : MulAut ↥F) • ℓ₁ : ↥(lines ↥F)) : Subgroup ↥F)
    rw [SubMulAction.val_smul, smul_smul]
    calc (τ' * (g : MulAut ↥F)) • (ℓ₁ : Subgroup ↥F)
        = (g : MulAut ↥F) • (((g : MulAut ↥F)⁻¹ * τ' * g) • (ℓ₁ : Subgroup ↥F)) := by
          rw [smul_smul]
          congr 1
          group
      _ = (g : MulAut ↥F) • (ℓ₁ : Subgroup ↥F) := by rw [hfix1]
  set a' : ↥F := ⟨a, haF⟩ with ha'
  have ha'3 : a' ^ 3 = 1 := hF3' a'
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have hτ0 : ∀ x : ↥F, ((τ 0 x : ↥F) : Y) = t * x * t⁻¹ := fun x => by
    change (σ ^ 0) t * x * ((σ ^ 0) t)⁻¹ = t * x * t⁻¹
    rw [pow_zero]
    rfl
  have hτa : τ 0 a' = a'⁻¹ := Subtype.ext (by rw [hτ0]; exact hta)
  have hτF : ∀ x : ↥F, ∃ m : ℤ, τ 0 x = x * a' ^ m := by
    intro x
    have h := hcomm (x : Y)⁻¹ (D.inv_mem (hFD x.2))
    rw [inv_inv] at h
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp h
    refine ⟨m, Subtype.ext ?_⟩
    rw [hτ0, Subgroup.coe_mul, Subgroup.coe_zpow, hm]
    group
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ↥F, c₀ ∉ zpowers a' := by
    by_contra h
    push Not at h
    have htop : (⊤ : Subgroup ↥F) ≤ zpowers a' := fun x _ => h x
    have := Subgroup.card_le_of_le htop
    rw [Subgroup.card_top, hFcard, Nat.card_zpowers, orderOf_eq_prime ha'3 ha'1] at this
    norm_num at this
  obtain ⟨m, hm⟩ := hτF c₀
  set c : ↥F := c₀ * a' ^ (2 * m) with hc
  have ha'pow : ∀ j : ℤ, a' ^ (3 * j) = 1 := fun j => by rw [zpow_mul, zpow_ofNat, ha'3, one_zpow]
  have hτc : τ 0 c = c := by
    rw [hc, map_mul, map_zpow, hm, hτa, inv_zpow', mul_assoc, ← zpow_add]
    congr 1
    have : m + -(2 * m) = 2 * m + 3 * (-m) := by ring
    rw [this, zpow_add, ha'pow, mul_one]
  have hcz : c ∉ zpowers a' := by
    intro h
    apply hc₀
    have : c₀ = c * a' ^ (-(2 * m)) := by rw [hc, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero,
      mul_one]
    rw [this]
    exact mul_mem h (zpow_mem (mem_zpowers a') _)
  set x : ↥F := a' * c with hx
  have hx1 : x ≠ 1 := by
    intro h
    apply hcz
    have : c = a'⁻¹ := by rw [eq_inv_iff_mul_eq_one, hcommF, ← hx, h]
    rw [this]
    exact inv_mem (mem_zpowers a')
  have hxℓ : zpowers x ∈ lines ↥F := by
    rw [mem_lines, Nat.card_zpowers]
    exact orderOf_eq_prime (hF3' x) hx1
  have hfixℓ := hallfix ⟨zpowers x, hxℓ⟩ (τ 0) (subset_closure ⟨0, rfl⟩)
  have hmemx : τ 0 x ∈ zpowers x := by
    have := Subgroup.smul_mem_pointwise_smul x (τ 0) _ (mem_zpowers x)
    change τ 0 • x ∈ τ 0 • zpowers x at this
    rwa [hfixℓ, MulAut.smul_def] at this
  have hτx : τ 0 x = a'⁻¹ * c := by rw [hx, map_mul, hτa, hτc]
  obtain ⟨j, hj3, hj⟩ := exists_lt_three_of_mem_zpowers (hF3' x) hmemx
  rw [hτx] at hj
  interval_cases j
  · apply hcz
    rw [pow_zero, inv_mul_eq_one] at hj
    rw [← hj]
    exact mem_zpowers a'
  · apply ha'1
    rw [pow_one, hx, mul_left_inj] at hj
    have h2 : a' ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← hj]; exact inv_mul_cancel a'
    calc a' = a' ^ 3 * (a' ^ 2)⁻¹ := by group
      _ = 1 := by rw [ha'3, h2]; group
  · apply hcz
    have hsq : (a' * c) ^ 2 = a' ^ 2 * c ^ 2 := (Commute.mul_pow (hcommF a' c) 2)
    rw [hx, hsq] at hj
    have hc1 : c = 1 := by
      have e1 : c = a' * (a'⁻¹ * c) := by group
      rw [hj] at e1
      have e2 : a' * (a' ^ 2 * c ^ 2) = a' ^ 3 * c ^ 2 := by group
      rw [e2, ha'3, one_mul] at e1
      calc c = c ^ 2 * c⁻¹ := by group
        _ = 1 := by rw [← e1]; group
    rw [hc1]
    exact one_mem _

end CFSG.AGLEmbedding.CZeroOrbit

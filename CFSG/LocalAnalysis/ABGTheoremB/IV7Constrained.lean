module

public import CFSG.LocalAnalysis.ABGTheoremB.IV7Data
import CFSG.LocalAnalysis.ABGTheoremB.IV2
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStabilityReduction
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.Gorenstein.MaxCardThompson
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public noncomputable section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools CFSG.ABGQGroups
open scoped Pointwise commutatorElement

universe u

section General

variable {G : Type u} [Group G]

private theorem mem_normalizer_of_conj_mem [Finite G] {K : Subgroup G} {x : G}
    (h : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨k, hk, rfl⟩
    exact h k hk
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

private theorem normalizer_le_normalizer_map_of_characteristic [Finite G] {Y : Subgroup G}
    (A : Subgroup Y) [hA : A.Characteristic] :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer ((A.map Y.subtype : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_of_conj_mem
  rintro _ ⟨a, ha, rfl⟩
  have hfix := hA.fixed (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩)
  have hmem : a ∈ Subgroup.comap (Subgroup.normalizerMonoidHom Y ⟨g, hg⟩).toMonoidHom A := by
    rw [hfix]
    exact ha
  refine ⟨_, hmem, ?_⟩
  change (((Subgroup.normalizerMonoidHom Y ⟨g, hg⟩) a : Y) : G) = g * a * g⁻¹
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]

private theorem normalizer_le_normalizer_of_characteristic [Finite G] {P Q : Subgroup G}
    (hQP : Q ≤ P) (hQ : (Q.subgroupOf P).Characteristic) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  have := normalizer_le_normalizer_map_of_characteristic (Y := P) (Q.subgroupOf P)
  rwa [Subgroup.map_subgroupOf_eq_of_le hQP] at this

private theorem isSylowOf_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {Z X : Subgroup G}
    (hZ : IsSylowOf p Z X) {k : G} (hk : k ∈ Subgroup.normalizer (X : Set G)) :
    IsSylowOf p (Z.map (MulAut.conj k).toMonoidHom) X := by
  apply isSylowOf_of_card
  · rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hk z).mp (hZ.le hz)
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, hZ.card_eq]

private theorem exists_mem_inv_mul_mem_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {Z X : Subgroup G} (hZ : IsSylowOf p Z X) {k : G}
    (hk : k ∈ Subgroup.normalizer (X : Set G)) :
    ∃ x ∈ X, x⁻¹ * k ∈ Subgroup.normalizer (Z : Set G) := by
  obtain ⟨x, hx, hconj⟩ := hZ.exists_mem_conj (isSylowOf_map_conj hZ hk)
  refine ⟨x, hx, mem_normalizer_of_conj_mem fun z hz => ?_⟩
  have h2 := (hconj (k * z * k⁻¹)).mp ⟨z, hz, rfl⟩
  have e : x⁻¹ * k * z * (x⁻¹ * k)⁻¹ = x⁻¹ * (k * z * k⁻¹) * x := by group
  rw [e]
  exact h2

private theorem mem_normalizer_of_isSylowOf_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {Z X : Subgroup G} (hZ : IsSylowOf p Z X) (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    {k : G} (hk : k ∈ Subgroup.normalizer (X : Set G)) :
    k ∈ Subgroup.normalizer (Z : Set G) := by
  obtain ⟨x, hx, hn⟩ := exists_mem_inv_mul_mem_normalizer hZ hk
  have e : k = x * (x⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ (hXZ hx) hn

private theorem inf_eq_bot_of_coprime [Finite G] {p : ℕ} [Fact p.Prime] {E Q : Subgroup G}
    (hE : Nat.Coprime p (Nat.card E)) (hQ : IsPGroup p Q) : E ⊓ Q = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  apply (Subgroup.disjoint_of_coprime_natCard _).eq_bot
  rw [hk]
  exact (Nat.Coprime.pow_left k hE).symm

private theorem isSylowOf_sup_of_coprime_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime]
    {E Q : Subgroup G} (hE : Nat.Coprime p (Nat.card E)) (hQ : IsPGroup p Q)
    (hQE : Q ≤ Subgroup.normalizer (E : Set G)) : IsSylowOf p Q (E ⊔ Q) := by
  have hcard := card_sup_mul_card_inf_of_le_normalizer hQE
  rw [inf_eq_bot_of_coprime hE hQ, Subgroup.card_bot, mul_one] at hcard
  rw [isSylowOf_iff]
  refine ⟨le_sup_right, hQ, ?_⟩
  have h1 := Subgroup.relIndex_mul_card Q (E ⊔ Q)
  rw [inf_eq_left.mpr le_sup_right, hcard] at h1
  have h2 : Q.relIndex (E ⊔ Q) = Nat.card E := Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  rw [h2]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hE

private theorem commute_of_inf_eq_bot {K A B : Subgroup G}
    (hA : K ≤ Subgroup.normalizer (A : Set G)) (hB : K ≤ Subgroup.normalizer (B : Set G))
    (hAB : A ⊓ B = ⊥) {a b : G} (ha : a ∈ A) (haK : a ∈ K) (hb : b ∈ B) (hbK : b ∈ K) :
    a * b = b * a := by
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have h := (Subgroup.mem_normalizer_iff.mp (hA hbK) a⁻¹).mp (A.inv_mem ha)
    have := A.mul_mem ha h
    simpa [mul_assoc] using this
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ B :=
    B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hB haK) b).mp hb) (B.inv_mem hb)
  have h3 : a * b * a⁻¹ * b⁻¹ = 1 := by
    have h : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨h1, h2⟩
    rw [hAB] at h
    exact h
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h3, one_mul]

private theorem inv_pow_mul_pow_mem {L : Subgroup G} {x l : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hl : l ∈ L) (n : ℕ) :
    (x ^ n)⁻¹ * (x * l) ^ n ∈ L := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hx' : x⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hx' _).mp ih
    have e : (x ^ (n + 1))⁻¹ * (x * l) ^ (n + 1) =
        x⁻¹ * ((x ^ n)⁻¹ * (x * l) ^ n) * x⁻¹⁻¹ * l := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact L.mul_mem h1 hl

private theorem mem_of_pow_mem_of_pow_mem {H : Subgroup G} {y : G} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : y ^ a ∈ H) (hb : y ^ b ∈ H) : y ∈ H := by
  have h := Int.gcd_eq_gcd_ab (a : ℤ) (b : ℤ)
  rw [Int.gcd_natCast_natCast, hab.gcd_eq_one, Nat.cast_one] at h
  have e : y = (y ^ a) ^ (Int.gcdA a b) * (y ^ b) ^ (Int.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast y b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact H.mul_mem (H.zpow_mem ha _) (H.zpow_mem hb _)

private theorem pow_eq_self_of_sq_eq_one {y : G} (hy : y ^ 2 = 1) {n : ℕ} (hn : Odd n) :
    y ^ n = y := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, hy, one_pow, one_mul]

private theorem pow_eq_one_of_sq_eq_one {y : G} (hy : y ^ 2 = 1) {n : ℕ} (hn : Even n) :
    y ^ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, hy, one_pow]

private theorem exists_fixed_mem_coset [Finite G] {D H : Subgroup G} (hD : IsPGroup 2 D)
    (hH : Odd (Nat.card H)) {v : G}
    (hinv : ∀ d ∈ D, ∀ l ∈ H, v⁻¹ * (d * (v * l) * d⁻¹) ∈ H) :
    ∃ l ∈ H, ∀ d ∈ D, d * (v * l) * d⁻¹ = v * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction D H :=
    { smul := fun d l => ⟨v⁻¹ * ((d : G) * (v * l) * (d : G)⁻¹), hinv d d.2 l l.2⟩
      one_smul := fun l => Subtype.ext (by
        change v⁻¹ * ((1 : G) * (v * l) * (1 : G)⁻¹) = l
        group)
      mul_smul := fun d₁ d₂ l => Subtype.ext (by
        change v⁻¹ * (((d₁ : G) * d₂) * (v * l) * ((d₁ : G) * d₂)⁻¹) =
          v⁻¹ * ((d₁ : G) * (v * (v⁻¹ * ((d₂ : G) * (v * l) * (d₂ : G)⁻¹))) * (d₁ : G)⁻¹)
        group) }
  obtain ⟨l, hl⟩ := hD.nonempty_fixed_point_of_prime_not_dvd_card H hH.not_two_dvd_nat
  refine ⟨l, l.2, fun d hd => ?_⟩
  have h : v⁻¹ * (d * (v * l) * d⁻¹) = l := congrArg Subtype.val (hl ⟨d, hd⟩)
  calc d * (v * l) * d⁻¹ = v * (v⁻¹ * (d * (v * l) * d⁻¹)) := by group
    _ = v * l := by rw [h]

private theorem commutator_le_self (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

@[expose] def omegaPow (p m : ℕ) (P : Subgroup G) : Subgroup G :=
  Subgroup.closure {u | u ∈ P ∧ u ^ p ^ m = 1}

theorem omegaPow_le (p m : ℕ) (P : Subgroup G) : omegaPow p m P ≤ P := by
  rw [omegaPow, Subgroup.closure_le]
  exact fun u hu => hu.1

theorem mem_omegaPow {p m : ℕ} {P : Subgroup G} {u : G} (hu : u ∈ P) (hum : u ^ p ^ m = 1) :
    u ∈ omegaPow p m P :=
  Subgroup.subset_closure ⟨hu, hum⟩

theorem normalizer_le_normalizer_omegaPow [Finite G] (p m : ℕ) (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (omegaPow p m P : Set G) := by
  intro g hg
  apply mem_normalizer_of_conj_mem
  intro u hu
  have hle : (omegaPow p m P).map (MulAut.conj g).toMonoidHom ≤ omegaPow p m P := by
    rw [omegaPow, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, ⟨hyP, hy⟩, rfl⟩
    apply Subgroup.subset_closure
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hyP, ?_⟩
    change (g * y * g⁻¹) ^ p ^ m = 1
    rw [conj_pow, hy, mul_one, mul_inv_cancel]
  exact hle ⟨u, hu, rfl⟩

theorem omegaPow_subgroupOf_characteristic (p m : ℕ) (P : Subgroup G) :
    ((omegaPow p m P).subgroupOf P).Characteristic := by
  have hmap : omegaPow p m P = (Subgroup.closure {u : P | u ^ p ^ m = 1}).map P.subtype := by
    rw [MonoidHom.map_closure, omegaPow]
    congr 1
    ext u
    constructor
    · rintro ⟨hu, hum⟩
      exact ⟨⟨u, hu⟩, Subtype.ext (by simpa using hum), rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v.2, by simpa using congrArg Subtype.val (show v ^ p ^ m = 1 from hv)⟩
  rw [hmap, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective P.subtype_injective,
    Subgroup.characteristic_iff_map_le]
  intro φ
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨v, hv, rfl⟩
  apply Subgroup.subset_closure
  change (φ v) ^ p ^ m = 1
  rw [← map_pow, show v ^ p ^ m = 1 from hv, map_one]

theorem commutator_omegaPow_subgroupOf_characteristic (p m : ℕ) (P : Subgroup G) :
    (⁅omegaPow p m P, omegaPow p m P⁆.subgroupOf P).Characteristic := by
  have : (omegaPow p m P).subgroupOf P |>.Characteristic :=
    omegaPow_subgroupOf_characteristic p m P
  have heq : ⁅omegaPow p m P, omegaPow p m P⁆ =
      (⁅(omegaPow p m P).subgroupOf P, (omegaPow p m P).subgroupOf P⁆).map P.subtype := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (omegaPow_le p m P)]
  rw [heq, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

theorem omegaPow_eq_of_le {p m : ℕ} {P P₁ : Subgroup G} (hP₁ : P₁ ≤ P)
    (h : ∀ u ∈ P, u ^ p ^ m = 1 → u ∈ P₁) : omegaPow p m P = omegaPow p m P₁ := by
  rw [omegaPow, omegaPow]
  congr 1
  ext u
  exact ⟨fun hu => ⟨h u hu.1 hu.2, hu.2⟩, fun hu => ⟨hP₁ hu.1, hu.2⟩⟩

private theorem normalizer_le_normalizer_commutator [Finite G] (Ω : Subgroup G) :
    Subgroup.normalizer (Ω : Set G) ≤ Subgroup.normalizer ((⁅Ω, Ω⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  rw [Subgroup.map_commutator, hg]

theorem pow_eq_one_of_mem_omegaPow {p m : ℕ} {P : Subgroup G}
    (hab : ∀ a ∈ omegaPow p m P, ∀ b ∈ omegaPow p m P, a * b = b * a) {u : G}
    (hu : u ∈ omegaPow p m P) : u ^ p ^ m = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow _
  | mul x y hx hy ihx ihy =>
    rw [(show Commute x y from hab x hx y hy).mul_pow, ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

section CyclicQuotient

variable {N L : Subgroup G}

private theorem isCyclic_quotient_of_generator [(L.subgroupOf N).Normal]
    (hnorm : N ≤ Subgroup.normalizer (L : Set G))
    (hcyc : ∃ g ∈ N, ∀ n ∈ N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ L) :
    IsCyclic (N ⧸ L.subgroupOf N) := by
  obtain ⟨g, hg, hgen⟩ := hcyc
  refine ⟨⟨QuotientGroup.mk' (L.subgroupOf N) ⟨g, hg⟩, fun y => ?_⟩⟩
  obtain ⟨⟨n, hn⟩, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨k, hk⟩ := hgen n hn
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← map_zpow, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have hgk : g ^ k ∈ N := N.zpow_mem hg k
  have h1 := (Subgroup.mem_normalizer_iff.mp (hnorm (N.inv_mem hgk)) _).mp hk
  have e : (g ^ k)⁻¹ * (n * (g ^ k)⁻¹) * (g ^ k)⁻¹⁻¹ = (g ^ k)⁻¹ * n := by group
  rw [e] at h1
  simpa using h1

private theorem commutator_mem_of_cyclic (hLN : L ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (L : Set G))
    (hcyc : ∃ g ∈ N, ∀ n ∈ N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ L) {a b : G} (ha : a ∈ N)
    (hb : b ∈ N) : a * b * a⁻¹ * b⁻¹ ∈ L := by
  have : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hnorm
  have hcy := isCyclic_quotient_of_generator hnorm hcyc
  have hcomm := hcy.isMulCommutative
  have h := hcomm.is_comm.comm (QuotientGroup.mk' (L.subgroupOf N) ⟨a, ha⟩)
    (QuotientGroup.mk' (L.subgroupOf N) ⟨b, hb⟩)
  rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  have h2 : (a * b)⁻¹ * (b * a) ∈ L := by simpa using h
  have h3 := (Subgroup.mem_normalizer_iff.mp (hnorm (N.mul_mem ha hb)) _).mp (L.inv_mem h2)
  have e2 : a * b * ((a * b)⁻¹ * (b * a))⁻¹ * (a * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by group
  rw [e2] at h3
  exact h3

private theorem exists_pow_inv_mul_mem_of_cyclic (hLN : L ≤ N)
    (hnorm : N ≤ Subgroup.normalizer (L : Set G))
    (hcyc : ∃ g ∈ N, ∀ n ∈ N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ L) [Finite G] {r : ℕ} [hr : Fact r.Prime]
    {a b : G} (ha : a ∈ N) (haL : a ∉ L) (har : ∃ j : ℕ, a ^ r ^ j ∈ L) (hb : b ∈ N)
    (hbr : b ^ r ∈ L) : ∃ k : ℕ, (a ^ k)⁻¹ * b ∈ L := by
  have : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hnorm
  have hcy := isCyclic_quotient_of_generator hnorm hcyc
  set π := QuotientGroup.mk' (L.subgroupOf N) with hπ
  have hmem : ∀ (y : G) (hy : y ∈ N), π ⟨y, hy⟩ = 1 ↔ y ∈ L := by
    intro y hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set A := π ⟨a, ha⟩ with hA
  set B := π ⟨b, hb⟩ with hB
  have hA1 : A ≠ 1 := fun h => haL ((hmem a ha).mp h)
  obtain ⟨j, hj⟩ := har
  have hAj : A ^ r ^ j = 1 := by
    rw [hA, ← map_pow]
    exact (hmem _ (N.pow_mem ha _)).mpr hj
  have hBr : B ^ r = 1 := by
    rw [hB, ← map_pow]
    exact (hmem _ (N.pow_mem hb _)).mpr hbr
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hr.out).mp (orderOf_dvd_of_pow_eq_one hAj)
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hA1 (orderOf_eq_one_iff.mp (by simpa using hi))
  have hc : orderOf (A ^ r ^ (i - 1)) = r := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hr.out.ne_zero) (by
      rw [hi]; exact pow_dvd_pow r (Nat.sub_le i 1)), hi]
    rw [show i = (i - 1) + 1 by omega, pow_succ, Nat.add_sub_cancel,
      Nat.mul_div_cancel_left _ (pow_pos hr.out.pos _)]
  have hBc : B ∈ Subgroup.zpowers (A ^ r ^ (i - 1)) := by
    by_cases hB1 : B = 1
    · rw [hB1]
      exact one_mem _
    have hBo : orderOf B = r := orderOf_eq_prime hBr hB1
    have heq : Subgroup.zpowers B = Subgroup.zpowers (A ^ r ^ (i - 1)) :=
      IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hBo, hc])
    rw [← heq]
    exact Subgroup.mem_zpowers B
  have hBA : B ∈ Subgroup.zpowers A :=
    (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers A) _)) hBc
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := A)).mpr hBA
  refine ⟨k, ?_⟩
  have h1 : π (⟨a, ha⟩ ^ k) = π ⟨b, hb⟩ := by
    rw [map_pow]
    exact hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at h1
  simpa using h1

end CyclicQuotient

section Cores

variable {p : ℕ} {K : Subgroup G}

private theorem pPrimeCoreIn_le_pPrimePCoreIn : pPrimeCoreIn p K ≤ pPrimePCoreIn p K :=
  Subgroup.map_mono pPrimeCore_le_Op_p'p

private theorem coprime_card_pPrimeCoreIn [Finite G] [Fact p.Prime] :
    Nat.Coprime p (Nat.card (pPrimeCoreIn p K)) := by
  rw [pPrimeCoreIn, Subgroup.card_map_of_injective K.subtype_injective]
  exact pPrimeCore_coprime_card

private theorem le_normalizer_pPrimeCoreIn :
    K ≤ Subgroup.normalizer (pPrimeCoreIn p K : Set G) :=
  le_normalizer_map_subtype K (CFSG.pPrimeCore p K)

private theorem le_normalizer_pPrimePCoreIn :
    K ≤ Subgroup.normalizer (pPrimePCoreIn p K : Set G) :=
  le_normalizer_map_subtype K (CFSG.Op_p'p p K)

private theorem exists_pow_mem_pPrimeCoreIn {y : G} (hy : y ∈ pPrimePCoreIn p K) :
    ∃ k : ℕ, y ^ p ^ k ∈ pPrimeCoreIn p K := by
  obtain ⟨y', hy', rfl⟩ := hy
  obtain ⟨k, hk⟩ := exists_pow_mem_pPrimeCore_of_mem_Op_p'p hy'
  exact ⟨k, ⟨_, hk, by simp⟩⟩

private theorem le_pPrimePCoreIn_of_normal {X : Subgroup G} (hXK : X ≤ K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G))
    (hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ pPrimeCoreIn p K) : X ≤ pPrimePCoreIn p K := by
  have hn : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  have hle : X.subgroupOf K ≤ CFSG.Op_p'p p K := by
    apply le_Op_p'p_of_normal hn
    intro x hx
    obtain ⟨k, z, hz, hzx⟩ := hpow x hx
    refine ⟨k, ?_⟩
    have : z = x ^ p ^ k := Subtype.ext (by simpa using hzx)
    rw [← this]
    exact hz
  intro x hx
  exact ⟨⟨x, hXK hx⟩, hle hx, rfl⟩

private theorem sup_eq_pPrimePCoreIn_iff [Finite G] [Fact p.Prime] {Q : Subgroup G}
    (hQ : IsPGroup p Q) (hQK : Q ≤ K) :
    pPrimeCoreIn p K ⊔ Q = pPrimePCoreIn p K ↔ IsSylowOf p Q (pPrimePCoreIn p K) := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  have h := sup_eq_Op_p'p_iff_isSylowOf (H := K) hQ'
  have hsyl : IsSylowOf p (Q.subgroupOf K) (CFSG.Op_p'p p K) ↔
      IsSylowOf p Q (pPrimePCoreIn p K) := by
    rw [← isSylowOf_map_subtype_iff K, Subgroup.map_subgroupOf_eq_of_le hQK]
    rfl
  rw [← hsyl, ← h]
  constructor
  · intro heq
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hQK]
    exact heq
  · intro heq
    rw [pPrimeCoreIn, pPrimePCoreIn, ← heq, Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hQK]

private theorem le_pPrimeCoreIn_of_normal {X : Subgroup G} (hXK : X ≤ K)
    (hKX : K ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X)) :
    X ≤ pPrimeCoreIn p K := by
  have hn : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  have hc : Nat.Coprime p (Nat.card (X.subgroupOf K)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv]
  have hle : X.subgroupOf K ≤ CFSG.pPrimeCore p K := le_sSup ⟨hn, hc⟩
  intro x hx
  exact ⟨⟨x, hXK hx⟩, hle hx, rfl⟩

end Cores

private theorem solvableRadical_characteristic (H : Type*) [Group H] [Finite H] :
    (CFSG.solvableRadical H).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  apply le_sSup
  refine ⟨(solvableRadical_normal).map φ.toMonoidHom φ.surjective, ?_⟩
  have : Group.IsSolvable (CFSG.solvableRadical H) := solvableRadical_isSolvable
  let e := (CFSG.solvableRadical H).equivMapOfInjective φ.toMonoidHom φ.injective
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private theorem solvRadIn_le_solvRadIn [Finite G] {L N : Subgroup G} (hLN : L ≤ N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) : solvRadIn L ≤ solvRadIn N := by
  have : (CFSG.solvableRadical L).Characteristic := solvableRadical_characteristic L
  have hXN : solvRadIn L ≤ N := (solvRadIn_le L).trans hLN
  have hn : ((solvRadIn L).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr
      (hNL.trans (normalizer_le_normalizer_map_of_characteristic _))
  have hsolv : Group.IsSolvable ((solvRadIn L).subgroupOf N) := by
    have : Group.IsSolvable (CFSG.solvableRadical L) := solvableRadical_isSolvable
    let e : CFSG.solvableRadical L ≃* (solvRadIn L).subgroupOf N :=
      ((CFSG.solvableRadical L).equivMapOfInjective L.subtype L.subtype_injective).trans
        (Subgroup.subgroupOfEquivOfLe hXN).symm
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hle : (solvRadIn L).subgroupOf N ≤ CFSG.solvableRadical N := le_sSup ⟨hn, hsolv⟩
  intro x hx
  exact ⟨⟨x, hXN hx⟩, hle hx, rfl⟩

private theorem thompsonCenter_subgroupOf_map [Finite G] {Y P : Subgroup G} (hPY : P ≤ Y) :
    (thompsonCenter (G := Y) (P.subgroupOf Y)).map Y.subtype = thompsonCenter (G := G) P :=
  by
  rw [CFSG.map_thompsonCenter_of_injective Y.subtype _
    (Y.subtype_injective.comp (Subgroup.subtype_injective _)), Subgroup.map_subgroupOf_eq_of_le hPY]

private theorem thompsonCenter_subgroupOf_characteristic [Finite G] (P : Subgroup G) :
    ((thompsonCenter (G := G) P).subgroupOf P).Characteristic := by
  rw [← thompsonCenter_top_map_subtype (G := G) P, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective,
    Subgroup.characteristic_iff_map_le]
  intro φ
  rw [thompsonCenter_top_map_mulEquiv φ]

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

@[expose] def IV7K (P : Subgroup G) : Subgroup G :=
  (σ.C ⊓ σ.L ⊓ Subgroup.normalizer ((P ⊓ σ.L : Subgroup G) : Set G)) ⊔ P

private theorem L_le_N' (hσ : σ.IsValid) : σ.L ≤ σ.N :=
  sup_le hσ.L₀_le_N (σ.S_le_N hσ)

omit [Finite G] in
private theorem D_le_L' : σ.D ≤ σ.L :=
  σ.D_le_S.trans le_sup_right

private theorem x₂_mem_D' (hσ : σ.IsValid) : σ.x₂ ∈ σ.D :=
  σ.T_le_D hσ σ.x₂_mem_T

omit [Finite G] in
private theorem isPGroup_two_D : IsPGroup 2 σ.D :=
  σ.S.isPGroup'.to_le σ.D_le_S

private theorem odd_card_of_isPGroup' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup p X) : Odd (Nat.card X) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

omit [Finite G] in
private theorem ON_ne_bot {r : ℕ} (hr : r.Prime) (hdvd : r ∣ Nat.card σ.ON) : σ.ON ≠ ⊥ := by
  intro h
  rw [h, Subgroup.card_bot] at hdvd
  exact hr.one_lt.ne' (Nat.dvd_one.mp hdvd)

private theorem isQGroup_N (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ Nat.card σ.ON) : IsQGroup σ.N := by
  have hcov : (σ.L₀ : Set G) ⊆ (σ.N : Set G) * (σ.ON : Set G) := by
    intro l hl
    exact ⟨l, hσ.L₀_le_N hl, 1, σ.ON.one_mem, mul_one l⟩
  exact (hII.cover_qgroup σ.N (σ.T_le_N hσ) (σ.ON_ne_bot hr hdvd) hcov).1.1

private theorem not_dvd_relIndex_inf_ON (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {X : Subgroup G} (hXS : X ≤ solvRadIn σ.N)
    (hXON : X ≤ Subgroup.normalizer (σ.ON : Set G)) : ¬ r ∣ (X ⊓ σ.ON).relIndex X := by
  set Z : Subgroup G := centerOf (σ.S : Subgroup G) with hZdef
  have hZON : Z ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON
  rw [Subgroup.inf_relIndex_left, ← relIndex_sup_right_of_le_normalizer hXON]
  have hdvd : σ.ON.relIndex (X ⊔ σ.ON) ∣ σ.ON.relIndex (Z ⊔ σ.ON) := by
    have hXZ : X ⊔ σ.ON ≤ Z ⊔ σ.ON := by
      rw [sup_le_iff]
      refine ⟨?_, le_sup_right⟩
      have := hXS
      rwa [hII.N_solvRad, sup_comm] at this
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hXZ)
  rw [relIndex_sup_right_of_le_normalizer hZON] at hdvd
  have hZ2 : IsPGroup 2 Z := σ.S.isPGroup'.to_le inf_le_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ2
  intro hrd
  have h1 : r ∣ 2 ^ k := hk ▸ hrd.trans (hdvd.trans (Subgroup.relIndex_dvd_card _ _))
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))

private theorem exists_two_pow_mem_ON (hσ : σ.IsValid) (hII : σ.NStructure) {y : G}
    (hy : y ∈ solvRadIn σ.N) : ∃ a : ℕ, y ^ 2 ^ a ∈ σ.ON := by
  have hZON : centerOf (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON
  rw [hII.N_solvRad, sup_comm] at hy
  have hy' : y ∈ ((centerOf (σ.S : Subgroup G) ⊔ σ.ON : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZON] at hy'
  obtain ⟨z, hz, o, ho, rfl⟩ := hy'
  obtain ⟨a, ha⟩ := (σ.S.isPGroup'.to_le
    (inf_le_left : centerOf (σ.S : Subgroup G) ≤ σ.S)) ⟨z, hz⟩
  have ha' : z ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  refine ⟨a, ?_⟩
  have h := inv_pow_mul_pow_mem (hZON hz) ho (2 ^ a)
  rwa [ha', inv_one, one_mul] at h

private theorem mem_ON_of_mem_solvRadIn (hσ : σ.IsValid) (hII : σ.NStructure) {y : G}
    (hy : y ∈ solvRadIn σ.N) (hodd : Odd (orderOf y)) : y ∈ σ.ON := by
  obtain ⟨a, ha⟩ := σ.exists_two_pow_mem_ON hσ hII hy
  have h1 : y ^ orderOf y ∈ σ.ON := by
    rw [pow_orderOf_eq_one]
    exact one_mem _
  exact mem_of_pow_mem_of_pow_mem
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)) ha h1

private theorem isSylowOf_pPrimePCoreIn_N_of_inf (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hc : σ.Constrained r) {X : Subgroup G}
    (hX : IsSylowOf r X (pPrimePCoreIn r σ.N ⊓ σ.ON)) : IsSylowOf r X (pPrimePCoreIn r σ.N) := by
  have : Fact r.Prime := ⟨hr⟩
  have hOS : pPrimePCoreIn r σ.N ≤ solvRadIn σ.N := Subgroup.map_mono hc.1
  have hON : pPrimePCoreIn r σ.N ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (Subgroup.map_subtype_le _).trans σ.N_le_normalizer_ON
  rw [isSylowOf_iff] at hX ⊢
  refine ⟨hX.1.trans inf_le_left, hX.2.1, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex X (pPrimePCoreIn r σ.N ⊓ σ.ON) _ hX.1 inf_le_left]
  exact hr.not_dvd_mul hX.2.2 (σ.not_dvd_relIndex_inf_ON hσ hII hr hr2 hOS hON)

theorem exists_sylow_pPrimePCoreIn_N (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hc : σ.Constrained r) {Q : Subgroup G} (hQN : Q ≤ σ.N)
    (hQ : IsPGroup r Q) (hDQ : σ.D ≤ Subgroup.normalizer (Q : Set G)) :
    ∃ Rs : Subgroup G, IsSylowOf r Rs (pPrimePCoreIn r σ.N) ∧
      σ.D ≤ Subgroup.normalizer (Rs : Set G) ∧ Q ≤ Subgroup.normalizer (Rs : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  set O : Subgroup G := pPrimePCoreIn r σ.N with hOdef
  set Y₀ : Subgroup G := O ⊓ σ.ON with hY₀def
  have hNO : σ.N ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimePCoreIn
  have hNY₀ : σ.N ≤ Subgroup.normalizer (Y₀ : Set G) :=
    (le_inf hNO σ.N_le_normalizer_ON).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQY₀ : Q ≤ Subgroup.normalizer (Y₀ : Set G) := hQN.trans hNY₀
  have hDY₀ : σ.D ≤ Subgroup.normalizer (Y₀ : Set G) := (σ.D_le_N hσ).trans hNY₀
  have hY₀odd : Odd (Nat.card Y₀) :=
    σ.odd_card_ON.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hQodd : Odd (Nat.card Q) := odd_card_of_isPGroup' hr hr2 hQ
  set M : Subgroup G := Y₀ ⊔ Q with hMdef
  have hModd : Odd (Nat.card M) := odd_card_sup_of_le_normalizer_of_odd hQY₀ hY₀odd hQodd
  have hDM : σ.D ≤ Subgroup.normalizer (M : Set G) :=
    (le_inf hDY₀ hDQ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨R₁, hR₁, hQR₁, hDR₁⟩ := exists_isSylowOf_normalized_ge_of_odd hr σ.isPGroup_two_D
    hDM hModd le_sup_right hQ hDQ
  have hMY₀ : M ≤ Subgroup.normalizer (Y₀ : Set G) := sup_le Subgroup.le_normalizer hQY₀
  have hRs : IsSylowOf r (R₁ ⊓ Y₀) Y₀ := hR₁.inf_of_le_normalizer le_sup_left hMY₀
  refine ⟨R₁ ⊓ Y₀, σ.isSylowOf_pPrimePCoreIn_N_of_inf hσ hII hr hr2 hc hRs, ?_, ?_⟩
  · exact (le_inf hDR₁ hDY₀).trans Subgroup.inf_normalizer_le_normalizer_inf
  · exact (le_inf (hQR₁.trans Subgroup.le_normalizer) hQY₀).trans
      Subgroup.inf_normalizer_le_normalizer_inf

theorem lemmaIV71 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : σ.HypIV7 r)
    (hc : σ.Constrained r) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    {Q : Subgroup G} (hQ1 : Q ≠ ⊥) (hQP : Q ≤ P) (hQchar : (Q.subgroupOf P).Characteristic)
    (hcov : ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      (Subgroup.normalizer (Q : Set G) : Set G) * ((σ.C ⊓ solvRadIn σ.L : Subgroup G) : Set G)) :
    ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R ∧ d.Nstar = σ.N ∧ d.Q = Q := by
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hQN : Q ≤ σ.N := hQP.trans (hP.le.trans σ.C_le_N)
  have hDQ : σ.D ≤ Subgroup.normalizer (Q : Set G) :=
    hPD.trans (normalizer_le_normalizer_of_characteristic hQP hQchar)
  obtain ⟨Rs, hRs, hRsD, hRsQ⟩ := σ.exists_sylow_pPrimePCoreIn_N hσ hII hr.prime hr2 hc hQN
    (hP.isPGroup.to_le hQP) hDQ
  have hCN : σ.C ⊓ σ.N = σ.C := inf_eq_left.mpr σ.C_le_N
  refine ⟨{
      P := P
      P_sylow := hP
      P_D := hPD
      R := R
      R_sylow := hR
      R_D := hRD
      R_P := hRP
      Q := Q
      Q_ne_bot := hQ1
      Q_le := hQP
      Q_characteristic := hQchar
      Nstar := σ.N
      Nstar_qgroup := σ.isQGroup_N hσ hII hr.prime hr.dvd_ON
      Nstar_constrained := hc
      Nstar_covers := ?_
      D_le_Nstar := σ.D_le_N hσ
      Q_le_Nstar := hQN
      Cstar_covers := ?_
      Rstar := Rs
      Rstar_sylow := hRs
      Rstar_D := hRsD
      Rstar_Q := hRsQ
      centralizer_le := ?_
      cases := Or.inl (by rw [hCN]) }, rfl, rfl, rfl, rfl⟩
  · intro l hl
    exact ⟨l, σ.L_le_N' hσ hl, 1, σ.ON.one_mem, mul_one l⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hcov hg
    have haC : a ∈ σ.C := by
      have e : a = a * b * b⁻¹ := by group
      rw [e]
      exact σ.C.mul_mem hg.1 (σ.C.inv_mem hb.1)
    exact ⟨a, ⟨⟨haC, σ.C_le_N haC⟩, ha⟩, b, hb, rfl⟩
  · rw [hCN]
    refine inf_le_inf_left _ ?_
    exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)).trans
      (Subgroup.centralizer_le_normalizer _)

omit [Finite G] in
private theorem mul_pow_mem_ON {a b : G} (ha : a ∈ σ.N) (hb : b ∈ σ.N)
    (hab : a * b * a⁻¹ * b⁻¹ ∈ σ.ON) {n : ℕ} (han : a ^ n ∈ σ.ON) (hbn : b ^ n ∈ σ.ON) :
    (a * b) ^ n ∈ σ.ON := by
  have : (σ.ON.subgroupOf σ.N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer σ.ON_le_N).mpr σ.N_le_normalizer_ON
  set π := QuotientGroup.mk' (σ.ON.subgroupOf σ.N) with hπ
  have hπ1 : ∀ (y : G) (hy : y ∈ σ.N), π ⟨y, hy⟩ = 1 ↔ y ∈ σ.ON := by
    intro y hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := by
    have h := (hπ1 _ (σ.N.mul_mem (σ.N.mul_mem (σ.N.mul_mem ha hb) (σ.N.inv_mem ha))
      (σ.N.inv_mem hb))).mpr hab
    have e : (⟨a * b * a⁻¹ * b⁻¹, σ.N.mul_mem (σ.N.mul_mem (σ.N.mul_mem ha hb)
        (σ.N.inv_mem ha)) (σ.N.inv_mem hb)⟩ : σ.N) =
        ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h
    change π ⟨a, ha⟩ * π ⟨b, hb⟩ = π ⟨b, hb⟩ * π ⟨a, ha⟩
    calc π ⟨a, ha⟩ * π ⟨b, hb⟩ = π ⟨a, ha⟩ * π ⟨b, hb⟩ * (π ⟨a, ha⟩)⁻¹ * (π ⟨b, hb⟩)⁻¹ *
          (π ⟨b, hb⟩ * π ⟨a, ha⟩) := by group
      _ = π ⟨b, hb⟩ * π ⟨a, ha⟩ := by rw [h, one_mul]
  have h1 : π (⟨a, ha⟩ ^ n) = 1 := (hπ1 _ (σ.N.pow_mem ha n)).mpr han
  have h2 : π (⟨b, hb⟩ ^ n) = 1 := (hπ1 _ (σ.N.pow_mem hb n)).mpr hbn
  rw [map_pow] at h1 h2
  apply (hπ1 _ (σ.N.pow_mem (σ.N.mul_mem ha hb) n)).mp
  change π ((⟨a, ha⟩ * ⟨b, hb⟩) ^ n) = 1
  rw [map_pow, map_mul, hcomm.mul_pow, h1, h2, one_mul]

section K

variable {r : ℕ} {P : Subgroup G}

omit [Finite G] in
private theorem le_IV7K : P ≤ σ.IV7K P :=
  le_sup_right

omit [Finite G] in
private theorem IV7K_le_C (hPC : P ≤ σ.C) : σ.IV7K P ≤ σ.C :=
  sup_le (inf_le_left.trans inf_le_left) hPC

omit [Finite G] in
private theorem le_normalizer_L_of_le_C (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (hPC : P ≤ σ.C) : P ≤ Subgroup.normalizer (σ.L : Set G) :=
  (hPC.trans σ.C_le_N).trans h_L_normal

omit [Finite G] in
private theorem IV7K_le_normalizer_inf_L (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (hPC : P ≤ σ.C) : σ.IV7K P ≤ Subgroup.normalizer ((P ⊓ σ.L : Subgroup G) : Set G) :=
  sup_le inf_le_right ((le_inf Subgroup.le_normalizer
    (σ.le_normalizer_L_of_le_C h_L_normal hPC)).trans Subgroup.inf_normalizer_le_normalizer_inf)

private theorem isSylowOf_IV7K [Fact r.Prime] (hP : IsSylowOf r P σ.C) :
    IsSylowOf r P (σ.IV7K P) :=
  hP.of_le σ.le_IV7K (σ.IV7K_le_C hP.le)

private theorem isSylowOf_inf_L [Fact r.Prime]
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G)) (hP : IsSylowOf r P σ.C) :
    IsSylowOf r (P ⊓ σ.L) (σ.C ⊓ σ.L) := by
  have hCL : σ.C ≤ Subgroup.normalizer ((σ.C ⊓ σ.L : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (σ.C_le_N.trans h_L_normal)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have h := hP.inf_of_le_normalizer inf_le_left hCL
  rwa [← inf_assoc, inf_eq_left.mpr hP.le] at h

theorem lemmaIV72 {r : ℕ} (hr : r.Prime) {P : Subgroup G} (hP : IsSylowOf r P σ.C)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_II42 : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L) :
    σ.IV7K P ≤ σ.C ∧ ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      (σ.IV7K P : Set G) * ((σ.C ⊓ solvRadIn σ.L : Subgroup G) : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  refine ⟨σ.IV7K_le_C hP.le, ?_⟩
  set CL : Subgroup G := σ.C ⊓ σ.L with hCLdef
  set PL : Subgroup G := P ⊓ σ.L with hPLdef
  set SL : Subgroup G := σ.C ⊓ solvRadIn σ.L with hSLdef
  have hPL : IsSylowOf r PL CL := σ.isSylowOf_inf_L h_L_normal hP
  have : (CFSG.solvableRadical σ.L).Normal := solvableRadical_normal
  have hLS : σ.L ≤ Subgroup.normalizer (solvRadIn σ.L : Set G) :=
    le_normalizer_map_subtype σ.L (CFSG.solvableRadical σ.L)
  have hSLnorm : CL ≤ Subgroup.normalizer (SL : Set G) :=
    (le_inf (inf_le_left.trans Subgroup.le_normalizer) (inf_le_right.trans hLS)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hSLCL : SL ≤ CL := inf_le_inf_left _ (solvRadIn_le σ.L)
  have hK₁CL : SL ⊔ PL ≤ CL := sup_le hSLCL hPL.le
  have hK₁norm : CL ≤ Subgroup.normalizer ((SL ⊔ PL : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    intro k hk
    have hc : g * k * g⁻¹ * k⁻¹ ∈ SL := by
      refine ⟨σ.C.mul_mem (σ.C.mul_mem (σ.C.mul_mem hg.1 (hK₁CL hk).1) (σ.C.inv_mem hg.1))
        (σ.C.inv_mem (hK₁CL hk).1), h_II42 ?_⟩
      exact Subgroup.commutator_mem_commutator hg (hK₁CL hk)
    have e : g * k * g⁻¹ = g * k * g⁻¹ * k⁻¹ * k := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) hk
  have hPLK₁ : IsSylowOf r PL (SL ⊔ PL) := hPL.of_le le_sup_right hK₁CL
  intro x hx
  obtain ⟨y, hy, hn⟩ := exists_mem_inv_mul_mem_normalizer hPLK₁ (hK₁norm hx)
  have hyCL : y ∈ CL := hK₁CL hy
  rw [sup_comm] at hy
  have hy' : y ∈ ((PL ⊔ SL : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hPL.le.trans hSLnorm)] at hy'
  obtain ⟨p, hp, s, hs, rfl⟩ := hy'
  set n := (p * s)⁻¹ * x with hndef
  have hnCL : n ∈ CL := CL.mul_mem (CL.inv_mem hyCL) hx
  have hnK : n ∈ σ.IV7K P := Subgroup.mem_sup_left ⟨hnCL, hn⟩
  have hpK : p ∈ σ.IV7K P := σ.le_IV7K (inf_le_left (b := σ.L) hp)
  refine ⟨p * n, (σ.IV7K P).mul_mem hpK hnK, n⁻¹ * s * n, ?_, ?_⟩
  · have h1 := (Subgroup.mem_normalizer_iff.mp (hSLnorm (CL.inv_mem hnCL)) s).mp hs
    simpa using h1
  · rw [hndef]
    group

omit [Finite G] in
private theorem le_oddCoreIn_C [Fact r.Prime] (hr2 : r ≠ 2) (hP : IsSylowOf r P σ.C)
    (h_C : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C) : P ≤ oddCoreIn σ.C := by
  intro c hc
  apply h_C c (hP.le hc)
  obtain ⟨n, hn⟩ := hP.isPGroup ⟨c, hc⟩
  have h1 : orderOf c ∣ r ^ n := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hn)
  exact ((Fact.out : r.Prime).eq_two_or_odd'.resolve_left hr2).pow.of_dvd_nat h1

private theorem centerOf_S_le_IV7K (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (hσ : σ.IsValid) (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) :
    centerOf (σ.S : Subgroup G) ≤ σ.IV7K P := by
  intro z hz
  have hzT : z ∈ Subgroup.centralizer (σ.T : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (σ.T_le_S hσ)) hz.2
  have hzD : z ∈ σ.D := ⟨hz.1, Subgroup.centralizer_le_normalizer _ hzT⟩
  have hzL : z ∈ σ.L := Subgroup.mem_sup_right hz.1
  refine Subgroup.mem_sup_left ⟨⟨hzT, hzL⟩, ?_⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hPD hzD, ((σ.D_le_N hσ).trans h_L_normal) hzD⟩

theorem lemmaIV72_iii (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {P : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G))
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_C : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C)
    (h_II42 : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L)
    (h_II42iii : ∀ u ∈ oddCoreIn σ.C, (∃ n : ℕ, u ^ r ^ n = 1) → u ∉ σ.L →
      ∃ w ∈ oddCoreIn σ.C ⊓ σ.L, Nat.Coprime (orderOf w) r ∧ u * w * u⁻¹ * w⁻¹ ∉ σ.ON) :
    pCoreIn r (σ.IV7K P) = P ⊓ σ.L := by
  have : Fact r.Prime := ⟨hr⟩
  have h_II42i : ⁅oddCoreIn σ.C ⊓ σ.L, oddCoreIn σ.C ⊓ σ.L⁆ ≤ σ.ON := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hab : ⁅a, b⁆ ∈ oddCoreIn σ.C := by
      rw [commutatorElement_def]
      exact (oddCoreIn σ.C).mul_mem ((oddCoreIn σ.C).mul_mem ((oddCoreIn σ.C).mul_mem ha.1 hb.1)
        ((oddCoreIn σ.C).inv_mem ha.1)) ((oddCoreIn σ.C).inv_mem hb.1)
    refine σ.mem_ON_of_mem_solvRadIn hσ hII.toNStructure
      (solvRadIn_le_solvRadIn (σ.L_le_N' hσ) h_L_normal (h_II42 ?_))
      ((odd_card_oddCoreIn σ.C).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hab))
    exact Subgroup.commutator_mem_commutator ⟨oddCoreIn_le σ.C ha.1, ha.2⟩
      ⟨oddCoreIn_le σ.C hb.1, hb.2⟩
  set K : Subgroup G := σ.IV7K P with hKdef
  set O : Subgroup G := pCoreIn r K with hOdef
  set PL : Subgroup G := P ⊓ σ.L with hPLdef
  have hPK : IsSylowOf r P K := σ.isSylowOf_IV7K hP
  have hKC : K ≤ σ.C := σ.IV7K_le_C hP.le
  have hKN : K ≤ σ.N := hKC.trans σ.C_le_N
  have hKPL : K ≤ Subgroup.normalizer (PL : Set G) := σ.IV7K_le_normalizer_inf_L h_L_normal hP.le
  have hOK : O ≤ K := pCoreIn_le r K
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_map_subtype K (CFSG.pCore r K)
  have hOp : IsPGroup r O := CFSG.pCore_isPGroup.map K.subtype
  have hPLO : PL ≤ O := by
    have hn : (PL.subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hPK.le)).mpr hKPL
    have hle : PL.subgroupOf K ≤ CFSG.pCore r K :=
      le_sSup ⟨hn, (hP.isPGroup.to_le inf_le_left).comap_subtype⟩
    intro x hx
    exact ⟨⟨x, (inf_le_left.trans hPK.le) hx⟩, hle hx, rfl⟩
  have hOP : O ≤ P := by
    have h := hPK.eq_of_le le_sup_right (sup_le hOK hPK.le)
      (IsPGroup.to_sup_of_normal_left' hOp hP.isPGroup (hPK.le.trans hKO))
    rw [← h]
    exact le_sup_left
  refine le_antisymm (le_inf hOP ?_) hPLO
  intro u hu
  by_contra huL
  have huP : u ∈ P := hOP hu
  have huN : u ∈ σ.N := hKN (hOK hu)
  have huC : u ∈ oddCoreIn σ.C := σ.le_oddCoreIn_C hr2 hP h_C huP
  obtain ⟨j, hj⟩ := hP.isPGroup ⟨u, huP⟩
  have hj' : u ^ r ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨w, hwW, hwr, hwu⟩ := h_II42iii u huC ⟨j, hj'⟩ huL
  apply hwu
  have hwN : w ∈ σ.N := σ.C_le_N (oddCoreIn_le σ.C hwW.1)
  have hZON : centerOf (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON
  obtain ⟨k₀, hk₀, o₀, ho₀, hwk⟩ : ∃ k₀ ∈ K, ∃ o₀ ∈ σ.ON, k₀ * o₀ = w := by
    obtain ⟨k, hk, c, hc, rfl⟩ := (σ.lemmaIV72 hr hP h_L_normal h_II42).2
      ⟨oddCoreIn_le σ.C hwW.1, hwW.2⟩
    have hcS : c ∈ solvRadIn σ.N := solvRadIn_le_solvRadIn (σ.L_le_N' hσ) h_L_normal hc.2
    rw [hII.N_solvRad, sup_comm] at hcS
    have hcS' : c ∈ ((centerOf (σ.S : Subgroup G) ⊔ σ.ON : Subgroup G) : Set G) := hcS
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZON] at hcS'
    obtain ⟨z, hz, o, ho, rfl⟩ := hcS'
    exact ⟨k * z, K.mul_mem hk (σ.centerOf_S_le_IV7K h_L_normal hσ hPD hz), o, ho,
      by simp [mul_assoc]⟩
  set a : G := u * (k₀ * u⁻¹ * k₀⁻¹) with hadef
  have haO : a ∈ O :=
    O.mul_mem hu ((Subgroup.mem_normalizer_iff.mp (hKO hk₀) _).mp (O.inv_mem hu))
  have hk₀N : k₀ ∈ σ.N := hKN hk₀
  have hrest : a⁻¹ * (u * w * u⁻¹ * w⁻¹) ∈ σ.ON := by
    have h1 : u * o₀ * u⁻¹ ∈ σ.ON :=
      (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON huN) _).mp ho₀
    have h2 := (Subgroup.mem_normalizer_iff.mp (σ.N_le_normalizer_ON hk₀N) _).mp
      (σ.ON.mul_mem h1 (σ.ON.inv_mem ho₀))
    have e : a⁻¹ * (u * w * u⁻¹ * w⁻¹) = k₀ * (u * o₀ * u⁻¹ * o₀⁻¹) * k₀⁻¹ := by
      rw [hadef, ← hwk]
      group
    rw [e]
    exact h2
  obtain ⟨i, hi⟩ := hOp ⟨a, haO⟩
  have hi' : a ^ r ^ i = 1 := by simpa using congrArg Subtype.val hi
  have hpow1 : (u * w * u⁻¹ * w⁻¹) ^ r ^ i ∈ σ.ON := by
    have e : u * w * u⁻¹ * w⁻¹ = a * (a⁻¹ * (u * w * u⁻¹ * w⁻¹)) := by group
    have h := inv_pow_mul_pow_mem (σ.N_le_normalizer_ON (hKN (hOK haO))) hrest (r ^ i)
    rwa [hi', inv_one, one_mul, ← e] at h
  have huw : u * w * u⁻¹ ∈ oddCoreIn σ.C ⊓ σ.L := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreIn σ.C (hP.le huP)) w).mp
      hwW.1, (Subgroup.mem_normalizer_iff.mp (h_L_normal huN) w).mp hwW.2⟩
  have hpow2 : (u * w * u⁻¹ * w⁻¹) ^ orderOf w ∈ σ.ON := by
    have hcomm : u * w * u⁻¹ * w⁻¹ * (u * w * u⁻¹)⁻¹ * w⁻¹⁻¹ ∈ σ.ON := by
      apply h_II42i
      have h := Subgroup.commutator_mem_commutator huw ((oddCoreIn σ.C ⊓ σ.L).inv_mem hwW)
      rwa [commutatorElement_def] at h
    have h1 : (u * w * u⁻¹) ^ orderOf w ∈ σ.ON := by
      rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
      exact one_mem _
    have h2 : w⁻¹ ^ orderOf w ∈ σ.ON := by
      rw [inv_pow, pow_orderOf_eq_one, inv_one]
      exact one_mem _
    have huwN : u * w * u⁻¹ ∈ σ.N := σ.N.mul_mem (σ.N.mul_mem huN hwN) (σ.N.inv_mem huN)
    have h := σ.mul_pow_mem_ON huwN (σ.N.inv_mem hwN) hcomm h1 h2
    simpa [mul_assoc] using h
  exact mem_of_pow_mem_of_pow_mem (Nat.Coprime.pow_right i hwr) hpow2 hpow1

omit [Finite G] in
private theorem exists_pow_not_mem_pow_mem {L : Subgroup G} {a : G} (haL : a ∉ L) {j : ℕ}
    (hj : a ^ r ^ j ∈ L) : ∃ i, 1 ≤ i ∧ i ≤ j ∧ a ^ r ^ (i - 1) ∉ L ∧ a ^ r ^ i ∈ L := by
  classical
  have hex : ∃ i, a ^ r ^ i ∈ L := ⟨j, hj⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex hj, Nat.find_min hex ?_, Nat.find_spec hex⟩
  · by_contra h0
    have h := Nat.find_spec hex
    rw [show Nat.find hex = 0 by omega, pow_zero, pow_one] at h
    exact haL h
  · by_contra h0
    have h := Nat.find_spec hex
    rw [show Nat.find hex = 0 by omega, pow_zero, pow_one] at h
    exact haL h

omit [Finite G] in
private theorem inf_L_le_pPrimePCoreIn (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (hP : IsSylowOf r P σ.C) : P ⊓ σ.L ≤ pPrimePCoreIn r (σ.IV7K P) := by
  refine le_pPrimePCoreIn_of_normal (inf_le_left.trans σ.le_IV7K)
    (σ.IV7K_le_normalizer_inf_L h_L_normal hP.le) fun x hx => ?_
  obtain ⟨k, hk⟩ := (hP.isPGroup.to_le (inf_le_left : P ⊓ σ.L ≤ P)) ⟨x, hx⟩
  refine ⟨k, ?_⟩
  have : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact one_mem _

private theorem exists_mem_pPrimePCoreIn_not_mem_L (hr : r.Prime)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G)) (hP : IsSylowOf r P σ.C)
    (hU' : pPrimeCoreIn r (σ.IV7K P) ⊔ (P ⊓ σ.L) ≠ pPrimePCoreIn r (σ.IV7K P)) :
    ∃ a ∈ P, a ∈ pPrimePCoreIn r (σ.IV7K P) ∧ a ∉ σ.L := by
  have : Fact r.Prime := ⟨hr⟩
  by_contra hcon
  push Not at hcon
  have hPK := σ.isSylowOf_IV7K hP
  have hM : IsSylowOf r (P ⊓ pPrimePCoreIn r (σ.IV7K P)) (pPrimePCoreIn r (σ.IV7K P)) :=
    hPK.inf_of_le_normalizer (pPrimePCoreIn_le r _) le_normalizer_pPrimePCoreIn
  have heq : P ⊓ pPrimePCoreIn r (σ.IV7K P) = P ⊓ σ.L :=
    le_antisymm (fun a ha => ⟨ha.1, hcon a ha.1 ha.2⟩)
      (le_inf inf_le_left (σ.inf_L_le_pPrimePCoreIn h_L_normal hP))
  rw [heq] at hM
  exact hU' ((sup_eq_pPrimePCoreIn_iff (hP.isPGroup.to_le inf_le_left)
    (inf_le_left.trans σ.le_IV7K)).mpr hM)

omit [Finite G] in
private theorem pow_mem_L_of_minimal (hr : r.Prime) {v : G}
    (hvmin : ∀ w ∈ P, w ∉ σ.L → w ^ r ∈ σ.L → orderOf v ≤ orderOf w) {m : ℕ}
    (hvm : orderOf v = r ^ m) {u : G} (huP : u ∈ P) (hu : u ^ r ^ m = 1) : u ^ r ∈ σ.L := by
  by_cases huL : u ∈ σ.L
  · exact σ.L.pow_mem huL r
  have hum : u ^ r ^ m ∈ σ.L := by
    rw [hu]
    exact one_mem _
  obtain ⟨i, hi1, him, hi, hi'⟩ := exists_pow_not_mem_pow_mem huL hum
  by_cases hi2 : i = 1
  · rw [hi2, pow_one] at hi'
    exact hi'
  exfalso
  have hwr : (u ^ r ^ (i - 1)) ^ r ∈ σ.L := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hi1]
    exact hi'
  have h1 := hvmin _ (P.pow_mem huP _) hi hwr
  have h2 : orderOf (u ^ r ^ (i - 1)) ∣ r ^ (m - (i - 1)) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (by omega), hu]
  have h3 := Nat.le_of_dvd (pow_pos hr.pos _) h2
  have h4 : r ^ (m - (i - 1)) < r ^ m := Nat.pow_lt_pow_right hr.one_lt (by omega)
  omega

private theorem mem_sup_zpowers_of_pow_mem (hr : r.Prime)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_II33 : ∃ g ∈ σ.N, ∀ n ∈ σ.N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ σ.L) (hσ : σ.IsValid)
    (hP : IsSylowOf r P σ.C) {v w : G} (hvP : v ∈ P) (hvL : v ∉ σ.L) (hwP : w ∈ P)
    (hwr : w ^ r ∈ σ.L) : w ∈ (P ⊓ σ.L) ⊔ Subgroup.zpowers v := by
  have : Fact r.Prime := ⟨hr⟩
  have hPN : P ≤ σ.N := hP.le.trans σ.C_le_N
  obtain ⟨j, hj⟩ := hP.isPGroup ⟨v, hvP⟩
  have hj' : v ^ r ^ j ∈ σ.L := by
    have : v ^ r ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [this]
    exact one_mem _
  obtain ⟨k, hk⟩ := exists_pow_inv_mul_mem_of_cyclic (σ.L_le_N' hσ) h_L_normal h_II33 (hPN hvP)
    hvL ⟨j, hj'⟩ (hPN hwP) hwr
  have e : w = v ^ k * ((v ^ k)⁻¹ * w) := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers v) k)
    ⟨P.mul_mem (P.inv_mem (P.pow_mem hvP k)) hwP, hk⟩

theorem exists_minimal_order_not_mem_L (hr : r.Prime)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G)) (hP : IsSylowOf r P σ.C)
    (hU' : pPrimeCoreIn r (σ.IV7K P) ⊔ (P ⊓ σ.L) ≠ pPrimePCoreIn r (σ.IV7K P)) :
    ∃ v ∈ P, v ∉ σ.L ∧ v ^ r ∈ σ.L ∧
      ∀ w ∈ P, w ∉ σ.L → w ^ r ∈ σ.L → orderOf v ≤ orderOf w := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a, haP, -, haL⟩ := σ.exists_mem_pPrimePCoreIn_not_mem_L hr h_L_normal hP hU'
  obtain ⟨j, hj⟩ := hP.isPGroup ⟨a, haP⟩
  have hj' : a ^ r ^ j ∈ σ.L := by
    have : a ^ r ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [this]
    exact one_mem _
  obtain ⟨i, hi1, -, hi, hi'⟩ := exists_pow_not_mem_pow_mem haL hj'
  have hex : ∃ n, ∃ w ∈ P, w ∉ σ.L ∧ w ^ r ∈ σ.L ∧ orderOf w = n := by
    refine ⟨_, a ^ r ^ (i - 1), P.pow_mem haP _, hi, ?_, rfl⟩
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hi1]
    exact hi'
  obtain ⟨v, hvP, hvL, hvr, hvo⟩ := Nat.find_spec hex
  refine ⟨v, hvP, hvL, hvr, fun w hwP hwL hwr => ?_⟩
  rw [hvo]
  exact Nat.find_min' hex ⟨w, hwP, hwL, hwr, rfl⟩

private theorem inf_L_ne_bot (hr : σ.HypIV7 r)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G)) (hP : IsSylowOf r P σ.C) :
    P ⊓ σ.L ≠ ⊥ := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hcard := (σ.isSylowOf_inf_L h_L_normal hP).card_eq
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have h0 : (Nat.card (σ.C ⊓ σ.L : Subgroup G)).factorization r = 0 := by
    by_contra h
    have := Nat.one_lt_pow h hr.prime.one_lt
    omega
  have h1 := (hr.prime.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hr.dvd_CL
  omega

private theorem hasAbelianSylowTwo_of_odd {H : Type*} [Group H] [Finite H]
    (hH : Odd (Nat.card H)) : CFSG.BenderSuzuki.HasAbelianSylow 2 H := by
  have hodd : Odd (Nat.card (⊤ : Subgroup H)) := by rwa [Subgroup.card_top]
  have : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  exact CFSG.BenderSuzuki.hasAbelianSylowTwo_of_odd_normal_quotient_isMulCommutative ⊤ hodd
    ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩

theorem IV7K_le_normalizer_thompsonCenter (hr : σ.HypIV7 r) (hP : IsSylowOf r P σ.C)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_C : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C)
    (hU : pPrimeCoreIn r (σ.IV7K P) ⊔ (P ⊓ σ.L) = pPrimePCoreIn r (σ.IV7K P)) :
    σ.IV7K P ≤ Subgroup.normalizer (thompsonCenter (G := G) P : Set G) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  set K : Subgroup G := σ.IV7K P with hKdef
  set E : Subgroup G := pPrimeCoreIn r K with hEdef
  set PL : Subgroup G := P ⊓ σ.L with hPLdef
  set Z : Subgroup G := thompsonCenter (G := G) P with hZdef
  have hPK : IsSylowOf r P K := σ.isSylowOf_IV7K hP
  have hKC : K ≤ σ.C := σ.IV7K_le_C hP.le
  have hKPL : K ≤ Subgroup.normalizer (PL : Set G) := σ.IV7K_le_normalizer_inf_L h_L_normal hP.le
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := le_normalizer_pPrimeCoreIn
  have hEK : E ≤ K := pPrimeCoreIn_le r K
  have hEc : Nat.Coprime r (Nat.card E) := coprime_card_pPrimeCoreIn
  have hZP : Z ≤ P := thompsonCenter_le_self P
  have hZp : IsPGroup r Z := hP.isPGroup.to_le hZP
  have hZK : Z ≤ K := hZP.trans hPK.le
  have hPLp : IsPGroup r PL := hP.isPGroup.to_le inf_le_left
  set Y₁ : Subgroup G := K ⊓ oddCoreIn σ.C with hY₁def
  have hY₁odd : Odd (Nat.card Y₁) :=
    (odd_card_oddCoreIn σ.C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hKY₁ : K ≤ Subgroup.normalizer (Y₁ : Set G) :=
    (le_inf Subgroup.le_normalizer (hKC.trans (le_normalizer_oddCoreIn σ.C))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPY₁ : P ≤ Y₁ := le_inf hPK.le (σ.le_oddCoreIn_C hr2 hP h_C)
  have hPY₁syl : IsSylowOf r P Y₁ := hPK.of_le hPY₁ inf_le_left
  obtain ⟨S, hS⟩ := hPY₁syl.exists_sylow_eq_subgroupOf
  have hsolv : Group.IsSolvable Y₁ := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hY₁odd
  have hcore : CFSG.pCore r Y₁ ≠ ⊥ := by
    have hn : (PL.subgroupOf Y₁).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hPY₁)).mpr
        ((inf_le_left : Y₁ ≤ K).trans hKPL)
    have hle : PL.subgroupOf Y₁ ≤ CFSG.pCore r Y₁ := le_sSup ⟨hn, hPLp.comap_subtype⟩
    intro hbot
    rw [hbot, le_bot_iff] at hle
    apply σ.inf_L_ne_bot hr h_L_normal hP
    rw [← hPLdef, ← Subgroup.map_subgroupOf_eq_of_le (show PL ≤ Y₁ from inf_le_left.trans hPY₁),
      hle, Subgroup.map_bot]
  have hZJ := CFSG.G_theorem_8_2_11 (G := Y₁) r hr2 hcore
    (isPConstrained_iff_pConstrainedGroup.mp (isPConstrained_of_isSolvable hsolv))
    (CFSG.BenderSuzuki.pStableGroup'_of_solvable_abelianSylowTwo hsolv
      (hasAbelianSylowTwo_of_odd hY₁odd) (hr.prime.eq_two_or_odd'.resolve_left hr2)) S
  rw [hS] at hZJ
  set E₁ : Subgroup G := (CFSG.pPrimeCore r Y₁).map Y₁.subtype with hE₁def
  have hY₁ZE₁ : Y₁ ≤ Subgroup.normalizer ((Z ⊔ E₁ : Subgroup G) : Set G) := by
    have h := le_normalizer_map_subtype Y₁ (thompsonCenter (G := Y₁) (P.subgroupOf Y₁) ⊔
      CFSG.pPrimeCore r Y₁)
    rwa [Subgroup.map_sup, thompsonCenter_subgroupOf_map hPY₁] at h
  have hE₁E : E₁ ≤ E := by
    apply le_pPrimeCoreIn_of_normal ((Subgroup.map_subtype_le _).trans inf_le_left)
      (hKY₁.trans (normalizer_le_normalizer_map_of_characteristic _))
    rw [Subgroup.card_map_of_injective Y₁.subtype_injective]
    exact pPrimeCore_coprime_card
  have hKEZ : K ≤ Subgroup.normalizer ((E ⊔ Z : Subgroup G) : Set G) := by
    have heq : E ⊔ Z = E ⊔ (Z ⊔ E₁) := by
      rw [sup_comm Z E₁, ← sup_assoc, sup_eq_left.mpr hE₁E]
    intro k hk
    obtain ⟨y, hy, hn⟩ := exists_mem_inv_mul_mem_normalizer hPY₁syl (hKY₁ hk)
    have hyK : y ∈ K := (inf_le_left : Y₁ ≤ K) hy
    have h1 : y ∈ Subgroup.normalizer ((E ⊔ Z : Subgroup G) : Set G) := by
      rw [heq]
      exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hKE hyK, hY₁ZE₁ hy⟩
    have h2 : y⁻¹ * k ∈ Subgroup.normalizer ((E ⊔ Z : Subgroup G) : Set G) :=
      normalizer_inf_normalizer_le_normalizer_sup _ _
        ⟨hKE (K.mul_mem (K.inv_mem hyK) hk), normalizer_le_normalizer_thompsonCenter P hn⟩
    have e : k = y * (y⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 h2
  have hZE : Z ≤ Subgroup.normalizer (E : Set G) := hZK.trans hKE
  have hZM : Z ≤ pPrimePCoreIn r K := by
    refine le_sup_right.trans (le_pPrimePCoreIn_of_normal (sup_le hEK hZK) hKEZ ?_)
    intro x hx
    have hx' : x ∈ ((Z ⊔ E : Subgroup G) : Set G) := by rw [sup_comm]; exact hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZE] at hx'
    obtain ⟨z, hz, e, he, rfl⟩ := hx'
    obtain ⟨k, hk⟩ := hZp ⟨z, hz⟩
    refine ⟨k, ?_⟩
    have hzk : z ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h := inv_pow_mul_pow_mem (hZE hz) he (r ^ k)
    rwa [hzk, inv_one, one_mul] at h
  rw [← hU] at hZM
  have hPLsyl : IsSylowOf r PL (E ⊔ PL) :=
    isSylowOf_sup_of_coprime_of_le_normalizer hEc hPLp (inf_le_left.trans (hPK.le.trans hKE))
  have hZPL : Z ≤ PL := by
    have h := hPLsyl.eq_of_le le_sup_right (sup_le hZM le_sup_right)
      (IsPGroup.to_sup_of_normal_right' hZp hPLp (hZK.trans hKPL))
    rw [← h]
    exact le_sup_left
  have hEZ : E ≤ Subgroup.normalizer (Z : Set G) := by
    intro e he
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (commute_of_inf_eq_bot hKE hKPL (inf_eq_bot_of_coprime hEc hPLp) he (hEK he)
      (hZPL hz) (hZK hz)).symm
  intro k hk
  exact mem_normalizer_of_isSylowOf_of_le_normalizer
    (isSylowOf_sup_of_coprime_of_le_normalizer hEc hZp hZE) (sup_le hEZ Subgroup.le_normalizer)
    (hKEZ hk)

theorem IV7K_le_normalizer_commutator_omegaPow (hσ : σ.IsValid) (hr : r.Prime)
    (hP : IsSylowOf r P σ.C)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_II33 : ∃ g ∈ σ.N, ∀ n ∈ σ.N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ σ.L)
    (hU' : pPrimeCoreIn r (σ.IV7K P) ⊔ (P ⊓ σ.L) ≠ pPrimePCoreIn r (σ.IV7K P)) {v : G}
    (hvP : v ∈ P) (hvL : v ∉ σ.L) (hvr : v ^ r ∈ σ.L)
    (hvmin : ∀ w ∈ P, w ∉ σ.L → w ^ r ∈ σ.L → orderOf v ≤ orderOf w) {m : ℕ}
    (hvm : orderOf v = r ^ m) :
    σ.IV7K P ≤ Subgroup.normalizer ((⁅omegaPow r m P, omegaPow r m P⁆ : Subgroup G) : Set G) ∧
      ⁅omegaPow r m P, omegaPow r m P⁆ ≤ P ⊓ σ.L := by
  have : Fact r.Prime := ⟨hr⟩
  set K : Subgroup G := σ.IV7K P with hKdef
  set E : Subgroup G := pPrimeCoreIn r K with hEdef
  set M : Subgroup G := pPrimePCoreIn r K with hMdef
  set PL : Subgroup G := P ⊓ σ.L with hPLdef
  set Ω : Subgroup G := omegaPow r m P with hΩdef
  have hPK : IsSylowOf r P K := σ.isSylowOf_IV7K hP
  have hKPL : K ≤ Subgroup.normalizer (PL : Set G) := σ.IV7K_le_normalizer_inf_L h_L_normal hP.le
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := le_normalizer_pPrimeCoreIn
  have hKM : K ≤ Subgroup.normalizer (M : Set G) := le_normalizer_pPrimePCoreIn
  have hEK : E ≤ K := pPrimeCoreIn_le r K
  have hMK : M ≤ K := pPrimePCoreIn_le r K
  have hEc : Nat.Coprime r (Nat.card E) := coprime_card_pPrimeCoreIn
  have hPN : P ≤ σ.N := hP.le.trans σ.C_le_N
  have hPLp : IsPGroup r PL := hP.isPGroup.to_le inf_le_left
  have hPLM : PL ≤ M := σ.inf_L_le_pPrimePCoreIn h_L_normal hP
  obtain ⟨a, haP, haM, haL⟩ := σ.exists_mem_pPrimePCoreIn_not_mem_L hr h_L_normal hP hU'
  have hM_of : ∀ w ∈ P, w ^ r ∈ σ.L → w ∈ M := fun w hwP hwr =>
    (sup_le hPLM (Subgroup.zpowers_le.mpr haM))
      (σ.mem_sup_zpowers_of_pow_mem hr h_L_normal h_II33 hσ hP haP haL hwP hwr)
  set P₁ : Subgroup G := PL ⊔ Subgroup.zpowers v with hP₁def
  have hvPL : Subgroup.zpowers v ≤ Subgroup.normalizer (PL : Set G) :=
    Subgroup.zpowers_le.mpr (hKPL (hPK.le hvP))
  have hP₁P : P₁ ≤ P := sup_le inf_le_left (Subgroup.zpowers_le.mpr hvP)
  have hP₁K : P₁ ≤ K := hP₁P.trans hPK.le
  have hP₁M : P₁ ≤ M := sup_le hPLM (Subgroup.zpowers_le.mpr (hM_of v hvP hvr))
  have hP₁p : IsPGroup r P₁ := hP.isPGroup.to_le hP₁P
  have hP₁E : P₁ ≤ Subgroup.normalizer (E : Set G) := hP₁K.trans hKE
  have hmemP₁ : ∀ w ∈ P, w ∈ P₁ ↔ w ^ r ∈ σ.L := by
    intro w hwP
    constructor
    · intro hw
      have hw' : w ∈ ((Subgroup.zpowers v ⊔ PL : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hw
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hvPL] at hw'
      obtain ⟨x, hx, l, hl, rfl⟩ := hw'
      obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hx)
      have h1 := inv_pow_mul_pow_mem (h_L_normal (hPN (P.pow_mem hvP k))) hl.2 r
      have h2 : (v ^ k) ^ r ∈ σ.L := by
        rw [← pow_mul, mul_comm, pow_mul]
        exact σ.L.pow_mem hvr k
      have h3 := σ.L.mul_mem h2 h1
      rwa [mul_inv_cancel_left] at h3
    · intro hwr
      exact σ.mem_sup_zpowers_of_pow_mem hr h_L_normal h_II33 hσ hP hvP hvL hwP hwr
  have hPU : ∀ x ∈ P, x ∈ E ⊔ PL → x ∈ σ.L := by
    intro x hxP hxU
    have hxU' : x ∈ ((PL ⊔ E : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hxU
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_left.trans (hPK.le.trans hKE))] at hxU'
    obtain ⟨l, hl, e, he, rfl⟩ := hxU'
    have heP : e ∈ P := by
      have h : e = l⁻¹ * (l * e) := by group
      rw [h]
      exact P.mul_mem (P.inv_mem hl.1) hxP
    have he1 : e = 1 := by
      have h : e ∈ E ⊓ P := ⟨he, heP⟩
      rw [inf_eq_bot_of_coprime hEc hP.isPGroup] at h
      exact h
    simpa [he1] using hl.2
  have hU'K : K ≤ Subgroup.normalizer ((E ⊔ PL : Subgroup G) : Set G) :=
    (le_inf hKE hKPL).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hMchar : ∀ y ∈ M, y ∈ E ⊔ P₁ ↔ y ^ r ∈ E ⊔ PL := by
    intro y hyM
    constructor
    · intro hy
      have hy' : y ∈ ((P₁ ⊔ E : Subgroup G) : Set G) := by
        rw [sup_comm]
        exact hy
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hP₁E] at hy'
      obtain ⟨p, hp, e, he, rfl⟩ := hy'
      have h1 := inv_pow_mul_pow_mem (hP₁E hp) he r
      have h2 : p ^ r ∈ PL := ⟨P.pow_mem (hP₁P hp) r, (hmemP₁ p (hP₁P hp)).mp hp⟩
      have h3 := (E ⊔ PL).mul_mem (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left h1)
      rwa [mul_inv_cancel_left] at h3
    · intro hyr
      have hPMsyl : IsSylowOf r (P ⊓ M) M := hPK.inf_of_le_normalizer hMK hKM
      have hEPM : E ⊔ (P ⊓ M) = M := (sup_eq_pPrimePCoreIn_iff
        (hP.isPGroup.to_le inf_le_left) (inf_le_left.trans hPK.le)).mpr hPMsyl
      have hy' : y ∈ (((P ⊓ M) ⊔ E : Subgroup G) : Set G) := by
        rw [sup_comm, hEPM]
        exact hyM
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (inf_le_left.trans (hPK.le.trans hKE))] at hy'
      obtain ⟨p, hp, e, he, rfl⟩ := hy'
      have h1 := inv_pow_mul_pow_mem (hKE (hPK.le hp.1)) he r
      have h2 : p ^ r ∈ E ⊔ PL := by
        have h := (E ⊔ PL).mul_mem hyr ((E ⊔ PL).inv_mem (Subgroup.mem_sup_left h1))
        have e1 : (p * e) ^ r * ((p ^ r)⁻¹ * (p * e) ^ r)⁻¹ = p ^ r := by group
        rwa [e1] at h
      have hpP₁ : p ∈ P₁ := (hmemP₁ p hp.1).mpr (hPU _ (P.pow_mem hp.1 r) h2)
      rw [sup_comm]
      exact Subgroup.mul_mem_sup hpP₁ he
  have hKEP₁ : K ≤ Subgroup.normalizer ((E ⊔ P₁ : Subgroup G) : Set G) := by
    intro k hk
    apply mem_normalizer_of_conj_mem
    intro y hy
    have hyM : y ∈ M := sup_le pPrimeCoreIn_le_pPrimePCoreIn hP₁M hy
    have hkyM : k * y * k⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hKM hk) y).mp hyM
    rw [hMchar _ hkyM, conj_pow]
    exact (Subgroup.mem_normalizer_iff.mp (hU'K hk) _).mp ((hMchar y hyM).mp hy)
  have hP₁syl : IsSylowOf r P₁ (E ⊔ P₁) :=
    isSylowOf_sup_of_coprime_of_le_normalizer hEc hP₁p hP₁E
  have hΩeq : Ω = omegaPow r m P₁ := omegaPow_eq_of_le hP₁P fun u huP hu =>
    (hmemP₁ u huP).mpr (σ.pow_mem_L_of_minimal hr hvmin hvm huP hu)
  have hNP₁Q : Subgroup.normalizer (P₁ : Set G) ≤
      Subgroup.normalizer ((⁅Ω, Ω⁆ : Subgroup G) : Set G) := by
    have h1 := normalizer_le_normalizer_omegaPow r m P₁
    rw [← hΩeq] at h1
    exact h1.trans (normalizer_le_normalizer_commutator Ω)
  have hQPL : ⁅Ω, Ω⁆ ≤ PL := by
    have hΩP : Ω ≤ P := omegaPow_le r m P
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [commutatorElement_def]
    exact ⟨P.mul_mem (P.mul_mem (P.mul_mem (hΩP hg₁) (hΩP hg₂)) (P.inv_mem (hΩP hg₁)))
      (P.inv_mem (hΩP hg₂)), commutator_mem_of_cyclic (σ.L_le_N' hσ) h_L_normal h_II33
      (hPN (hΩP hg₁)) (hPN (hΩP hg₂))⟩
  have hEQ : E ≤ Subgroup.normalizer ((⁅Ω, Ω⁆ : Subgroup G) : Set G) := by
    intro e he
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (commute_of_inf_eq_bot hKE hKPL (inf_eq_bot_of_coprime hEc hPLp) he (hEK he)
      (hQPL hz) (hPK.le (hQPL hz).1)).symm
  refine ⟨fun k hk => ?_, hQPL⟩
  obtain ⟨y, hy, hn⟩ := exists_mem_inv_mul_mem_normalizer hP₁syl (hKEP₁ hk)
  have hyQ := (sup_le hEQ (Subgroup.le_normalizer.trans hNP₁Q)) hy
  have e : k = y * (y⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem _ hyQ (hNP₁Q hn)

private theorem covers_of_IV7K_le_normalizer (hr : r.Prime) (hP : IsSylowOf r P σ.C)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_II42 : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L) {Q : Subgroup G}
    (hQ : σ.IV7K P ≤ Subgroup.normalizer (Q : Set G)) :
    ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆ (Subgroup.normalizer (Q : Set G) : Set G) *
      ((σ.C ⊓ solvRadIn σ.L : Subgroup G) : Set G) :=
  (σ.lemmaIV72 hr hP h_L_normal h_II42).2.trans
    (Set.mul_subset_mul_right (SetLike.coe_subset_coe.mpr hQ))

theorem lemmaIV73 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r)
    (hc : σ.Constrained r) {R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_C : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C)
    (h_II42 : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L)
    (hU : pPrimeCoreIn r (σ.IV7K P) ⊔ (P ⊓ σ.L) = pPrimePCoreIn r (σ.IV7K P)) :
    ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R ∧ d.Nstar = σ.N ∧ d.Q = thompsonCenter (G := G) P := by
  have : Fact r.Prime := ⟨hr.prime⟩
  have hPne : P ≠ ⊥ := fun h => σ.inf_L_ne_bot hr h_L_normal hP (by rw [h, bot_inf_eq])
  exact σ.lemmaIV71 hσ hII hr hc hP hPD hR hRD hRP
    (section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hP.isPGroup hPne)
    (thompsonCenter_le_self P) (thompsonCenter_subgroupOf_characteristic P)
    (σ.covers_of_IV7K_le_normalizer hr.prime hP h_L_normal h_II42
      (σ.IV7K_le_normalizer_thompsonCenter hr hP h_L_normal h_C hU))

theorem lemmaIV74 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r)
    (hc : σ.Constrained r) {R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_II33 : ∃ g ∈ σ.N, ∀ n ∈ σ.N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ σ.L)
    (h_II42 : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L)
    (hU' : pPrimeCoreIn r (σ.IV7K P) ⊔ (P ⊓ σ.L) ≠ pPrimePCoreIn r (σ.IV7K P)) {v : G}
    (hvP : v ∈ P) (hvL : v ∉ σ.L) (hvr : v ^ r ∈ σ.L)
    (hvmin : ∀ w ∈ P, w ∉ σ.L → w ^ r ∈ σ.L → orderOf v ≤ orderOf w) {m : ℕ}
    (hvm : orderOf v = r ^ m)
    (hnonab : ¬ ∀ a ∈ omegaPow r m P, ∀ b ∈ omegaPow r m P, a * b = b * a) :
    ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R ∧ d.Nstar = σ.N ∧
      d.Q = ⁅omegaPow r m P, omegaPow r m P⁆ := by
  have hQ1 : ⁅omegaPow r m P, omegaPow r m P⁆ ≠ ⊥ := by
    intro hbot
    apply hnonab
    intro a ha b hb
    have h := Subgroup.commutator_mem_commutator ha hb
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
    exact h
  exact σ.lemmaIV71 hσ hII hr hc hP hPD hR hRD hRP hQ1
    ((commutator_le_self _).trans (omegaPow_le r m P))
    (commutator_omegaPow_subgroupOf_characteristic r m P)
    (σ.covers_of_IV7K_le_normalizer hr.prime hP h_L_normal h_II42
      (σ.IV7K_le_normalizer_commutator_omegaPow hσ hr.prime hP h_L_normal h_II33 hU' hvP hvL
        hvr hvmin hvm).1)

private theorem exists_sylow_ON_of_frobenius (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hc : σ.Constrained r)
    (h75 : ∀ {X Y K : Subgroup G}, Y ≤ K → K ≤ X →
      X ≤ Subgroup.normalizer (Y : Set G) → X ≤ Subgroup.normalizer (K : Set G) →
      Odd (Nat.card Y) → ∀ {p r : ℕ}, p.Prime → r.Prime → p ≠ 2 → r ≠ 2 → p ≠ r →
      Y.relIndex X = 2 * p * r → Y.relIndex K = r → ∀ {t u : G}, t ∈ X → u ∈ X →
      orderOf t = 2 → (∃ n : ℕ, u ^ p ^ n = 1) → t * u = u * t →
      (∀ k : ℕ, (t * u) ^ k ∈ Y ↔ 2 * p ∣ k) →
      (∀ g ∈ Subgroup.zpowers (t * u), g ∉ Y → ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ Y → k ∈ Y) →
      (∀ R : Subgroup G, IsSylowOf p R Y → X ⊓ Subgroup.centralizer (R : Set G) ≤ Y) →
      ∃ R : Subgroup G, IsSylowOf p R Y ∧ t * u ∈ Subgroup.normalizer (R : Set G) ∧
        ∃ z ∈ R, z * t = t * z ∧ z ^ p = 1 ∧ z * u ≠ u * z)
    {v : G} (hvN : v ∈ σ.N) (hvx₂ : σ.x₂ * v = v * σ.x₂) {m : ℕ} (hvm : v ^ r ^ m = 1)
    (hvON : v ∉ σ.ON) (hvr : v ^ r ∈ σ.ON) {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsr : s ≠ r)
    {K₀ : Subgroup G} (hONK₀ : σ.ON ≤ K₀) (hK₀N : K₀ ≤ σ.N) (hK₀idx : σ.ON.relIndex K₀ = s)
    (hvK₀ : v ∈ Subgroup.normalizer (K₀ : Set G))
    (hinv : ∀ k ∈ K₀, σ.x₂ * k * σ.x₂⁻¹ * k ∈ σ.ON)
    (hfpf : ∀ k ∈ K₀, v * k * v⁻¹ * k⁻¹ ∈ σ.ON → k ∈ σ.ON) :
    ∃ R₀ : Subgroup G, IsSylowOf r R₀ σ.ON ∧ σ.x₂ * v ∈ Subgroup.normalizer (R₀ : Set G) ∧
      ∃ z ∈ R₀, z * σ.x₂ = σ.x₂ * z ∧ z ^ r = 1 ∧ z * v ≠ v * z := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact s.Prime := ⟨hs⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hONN : σ.ON ≤ σ.N := σ.ON_le_N
  have : (σ.ON.subgroupOf σ.N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hONN).mpr σ.N_le_normalizer_ON
  set π := QuotientGroup.mk' (σ.ON.subgroupOf σ.N) with hπ
  have hπ1 : ∀ (y : G) (hy : y ∈ σ.N), π ⟨y, hy⟩ = 1 ↔ y ∈ σ.ON := by
    intro y hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hπmul : ∀ (a b : G) (ha : a ∈ σ.N) (hb : b ∈ σ.N),
      π ⟨a * b, σ.N.mul_mem ha hb⟩ = π ⟨a, ha⟩ * π ⟨b, hb⟩ := by
    intro a b ha hb
    rw [← map_mul]
    rfl
  have hπinv : ∀ (a : G) (ha : a ∈ σ.N), π ⟨a⁻¹, σ.N.inv_mem ha⟩ = (π ⟨a, ha⟩)⁻¹ := by
    intro a ha
    rw [← map_inv]
    rfl
  have hπpow : ∀ (a : G) (ha : a ∈ σ.N) (n : ℕ), π ⟨a ^ n, σ.N.pow_mem ha n⟩ = (π ⟨a, ha⟩) ^ n := by
    intro a ha n
    rw [← map_pow]
    rfl
  have hπcomm : ∀ (a b : G) (ha : a ∈ σ.N) (hb : b ∈ σ.N),
      a * b * a⁻¹ * b⁻¹ ∈ σ.ON ↔ Commute (π ⟨a, ha⟩) (π ⟨b, hb⟩) := by
    intro a b ha hb
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ σ.N :=
      σ.N.mul_mem (σ.N.mul_mem (σ.N.mul_mem ha hb) (σ.N.inv_mem ha)) (σ.N.inv_mem hb)
    rw [← hπ1 _ hmem]
    have e : π ⟨a * b * a⁻¹ * b⁻¹, hmem⟩ =
        π ⟨a, ha⟩ * π ⟨b, hb⟩ * (π ⟨a, ha⟩)⁻¹ * (π ⟨b, hb⟩)⁻¹ := by
      rw [← hπinv a ha, ← hπinv b hb, ← hπmul _ _ ha hb, ← hπmul _ _ _ (σ.N.inv_mem ha),
        ← hπmul _ _ _ (σ.N.inv_mem hb)]
    rw [e]
    constructor
    · intro h
      change π ⟨a, ha⟩ * π ⟨b, hb⟩ = π ⟨b, hb⟩ * π ⟨a, ha⟩
      calc π ⟨a, ha⟩ * π ⟨b, hb⟩ = π ⟨a, ha⟩ * π ⟨b, hb⟩ * (π ⟨a, ha⟩)⁻¹ * (π ⟨b, hb⟩)⁻¹ *
            (π ⟨b, hb⟩ * π ⟨a, ha⟩) := by group
        _ = π ⟨b, hb⟩ * π ⟨a, ha⟩ := by rw [h, one_mul]
    · intro h
      rw [h.eq]
      group
  have hx₂N : σ.x₂ ∈ σ.N := σ.x₂_mem_N hσ
  have hx₂ON : σ.x₂ ∉ σ.ON := by
    intro h
    have h1 := Subgroup.orderOf_dvd_natCard _ h
    rw [hσ.x₂_order] at h1
    exact σ.two_not_dvd_card_ON h1
  have hx₂sq : σ.x₂ ^ 2 = 1 := by
    rw [← hσ.x₂_order]
    exact pow_orderOf_eq_one _
  have ht1 : π ⟨σ.x₂, hx₂N⟩ ≠ 1 := fun h => hx₂ON ((hπ1 _ _).mp h)
  have ht2 : π ⟨σ.x₂, hx₂N⟩ ^ 2 = 1 := by
    rw [← hπpow _ hx₂N, hπ1]
    rw [hx₂sq]
    exact one_mem _
  have hto : orderOf (π ⟨σ.x₂, hx₂N⟩) = 2 := orderOf_eq_prime ht2 ht1
  have hu1 : π ⟨v, hvN⟩ ≠ 1 := fun h => hvON ((hπ1 _ _).mp h)
  have hur : π ⟨v, hvN⟩ ^ r = 1 := by
    rw [← hπpow _ hvN, hπ1]
    exact hvr
  have huo : orderOf (π ⟨v, hvN⟩) = r := orderOf_eq_prime hur hu1
  have htu : Commute (π ⟨σ.x₂, hx₂N⟩) (π ⟨v, hvN⟩) := by
    change π ⟨σ.x₂, hx₂N⟩ * π ⟨v, hvN⟩ = π ⟨v, hvN⟩ * π ⟨σ.x₂, hx₂N⟩
    rw [← hπmul _ _ hx₂N hvN, ← hπmul _ _ hvN hx₂N]
    congr 1
    exact Subtype.ext hvx₂
  have h2r : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
  have htuo : orderOf (π ⟨σ.x₂, hx₂N⟩ * π ⟨v, hvN⟩) = 2 * r := by
    rw [htu.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hto, huo]; exact h2r), hto, huo]
  set g₀ : G := σ.x₂ * v with hg₀def
  have hg₀N : g₀ ∈ σ.N := σ.N.mul_mem hx₂N hvN
  have hπg₀ : π ⟨g₀, hg₀N⟩ = π ⟨σ.x₂, hx₂N⟩ * π ⟨v, hvN⟩ := hπmul _ _ hx₂N hvN
  have hord : ∀ k : ℕ, g₀ ^ k ∈ σ.ON ↔ 2 * r ∣ k := by
    intro k
    rw [← hπ1 _ (σ.N.pow_mem hg₀N k), hπpow _ hg₀N, hπg₀, ← htuo, orderOf_dvd_iff_pow_eq_one]
  have hcomm_pow : Commute σ.x₂ v := hvx₂
  have hg₀pow : ∀ n : ℕ, g₀ ^ n = σ.x₂ ^ n * v ^ n := fun n => hcomm_pow.mul_pow n
  have hK₀norm : (σ.ON.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hONK₀).mpr (hK₀N.trans σ.N_le_normalizer_ON)
  have hK₀pow : ∀ k ∈ K₀, k ^ s ∈ σ.ON := by
    intro k hk
    have h := Subgroup.pow_index_mem (σ.ON.subgroupOf K₀) (⟨k, hk⟩ : K₀)
    rw [show (σ.ON.subgroupOf K₀).index = s from hK₀idx, Subgroup.mem_subgroupOf] at h
    simpa using h
  have hK₀comm : ∀ k ∈ K₀, ∀ k' ∈ K₀, k * k' * k⁻¹ * k'⁻¹ ∈ σ.ON := by
    intro k hk k' hk'
    have hcard : Nat.card (K₀ ⧸ σ.ON.subgroupOf K₀) = s := by
      rw [← Subgroup.index_eq_card]
      exact hK₀idx
    have hcyc : IsCyclic (K₀ ⧸ σ.ON.subgroupOf K₀) := isCyclic_of_prime_card hcard
    have h := hcyc.isMulCommutative.is_comm.comm (QuotientGroup.mk' (σ.ON.subgroupOf K₀) ⟨k, hk⟩)
      (QuotientGroup.mk' (σ.ON.subgroupOf K₀) ⟨k', hk'⟩)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
    have h2 : (k * k')⁻¹ * (k' * k) ∈ σ.ON := by simpa using h
    have h3 := (Subgroup.mem_normalizer_iff.mp
      (σ.N_le_normalizer_ON (σ.N.mul_mem (hK₀N hk) (hK₀N hk'))) _).mp (σ.ON.inv_mem h2)
    have e : k * k' * ((k * k')⁻¹ * (k' * k))⁻¹ * (k * k')⁻¹ = k * k' * k⁻¹ * k'⁻¹ := by group
    rwa [e] at h3
  have hK₀ne : ∃ k ∈ K₀, k ∉ σ.ON := by
    by_contra hcon
    push Not at hcon
    have h1 : σ.ON.relIndex K₀ = 1 := Subgroup.relIndex_eq_one.mpr hcon
    rw [hK₀idx] at h1
    exact hs.one_lt.ne' h1
  have hx₂K₀ : σ.x₂ ∈ Subgroup.normalizer (K₀ : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro k hk
    have e : σ.x₂ * k * σ.x₂⁻¹ = σ.x₂ * k * σ.x₂⁻¹ * k * k⁻¹ := by group
    rw [e]
    exact K₀.mul_mem (hONK₀ (hinv k hk)) (K₀.inv_mem hk)
  have hg₀K₀ : g₀ ∈ Subgroup.normalizer (K₀ : Set G) := Subgroup.mul_mem _ hx₂K₀ hvK₀
  have hZK₀ : Subgroup.zpowers g₀ ≤ Subgroup.normalizer (K₀ : Set G) :=
    Subgroup.zpowers_le.mpr hg₀K₀
  set X : Subgroup G := K₀ ⊔ Subgroup.zpowers g₀ with hXdef
  have hXN : X ≤ σ.N := sup_le hK₀N (Subgroup.zpowers_le.mpr hg₀N)
  have hrm_odd : Odd (r ^ m) := (hr.eq_two_or_odd'.resolve_left hr2).pow
  have hx₂X : σ.x₂ ∈ X := by
    have e : g₀ ^ r ^ m = σ.x₂ := by
      rw [hg₀pow, hvm, mul_one, pow_eq_self_of_sq_eq_one hx₂sq hrm_odd]
    rw [← e]
    exact Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers g₀) _)
  have hvX : v ∈ X := by
    have e : g₀ ^ (r ^ m + 1) = v := by
      rw [hg₀pow, pow_eq_one_of_sq_eq_one hx₂sq hrm_odd.add_one, one_mul, pow_succ, hvm, one_mul]
    rw [← e]
    exact Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers g₀) _)
  have hfpf' : ∀ g ∈ Subgroup.zpowers g₀, g ∉ σ.ON → ∀ k ∈ K₀,
      g * k * g⁻¹ * k⁻¹ ∈ σ.ON → k ∈ σ.ON := by
    intro g hg hgON k hk hgk
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg)
    have hkN : k ∈ σ.N := hK₀N hk
    have hc1 := (hπcomm _ _ (σ.N.pow_mem hg₀N n) hkN).mp hgk
    rw [hπpow _ hg₀N, hπg₀, htu.mul_pow] at hc1
    by_contra hkON
    have hk1 : π ⟨k, hkN⟩ ≠ 1 := fun h => hkON ((hπ1 _ _).mp h)
    rcases Nat.even_or_odd n with hn | hn
    · rw [pow_eq_one_of_sq_eq_one ht2 hn, one_mul] at hc1
      have hrn : ¬ r ∣ n := by
        intro hrn
        apply hgON
        rw [hord]
        exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd h2r (even_iff_two_dvd.mp hn) hrn)
      have hgcd : n.gcd (orderOf (π ⟨v, hvN⟩)) = 1 := by
        rw [huo, Nat.gcd_comm]
        exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hr).mpr hrn)).symm
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_pow_iff.mpr hgcd)
      have hc2 : Commute (π ⟨v, hvN⟩) (π ⟨k, hkN⟩) := by
        rw [← hz]
        exact hc1.zpow_left z
      exact hkON (hfpf k hk ((hπcomm _ _ hvN hkN).mpr hc2))
    · have hc2 : Commute (π ⟨σ.x₂, hx₂N⟩) (π ⟨k, hkN⟩) := by
        have h := hc1.pow_left r
        rw [(htu.pow_pow n n).mul_pow r, ← pow_mul, ← pow_mul, mul_comm n r,
          pow_mul (π ⟨v, hvN⟩), hur, one_pow, mul_one,
          pow_eq_self_of_sq_eq_one ht2 ((hr.eq_two_or_odd'.resolve_left hr2).mul hn)] at h
        exact h
      have hinv' : π ⟨σ.x₂, hx₂N⟩ * π ⟨k, hkN⟩ * (π ⟨σ.x₂, hx₂N⟩)⁻¹ * π ⟨k, hkN⟩ = 1 := by
        rw [← hπinv _ hx₂N, ← hπmul _ _ hx₂N hkN, ← hπmul _ _ _ (σ.N.inv_mem hx₂N),
          ← hπmul _ _ _ hkN, hπ1]
        exact hinv k hk
      rw [hc2.eq, mul_inv_cancel_right] at hinv'
      have hk2 : π ⟨k, hkN⟩ ^ 2 = 1 := by rw [sq]; exact hinv'
      have hks : π ⟨k, hkN⟩ ^ s = 1 := by
        rw [← hπpow _ hkN, hπ1]
        exact hK₀pow k hk
      have h2s : Nat.Coprime 2 s := (Nat.coprime_primes Nat.prime_two hs).mpr (Ne.symm hs2)
      apply hk1
      apply orderOf_eq_one_iff.mp
      exact Nat.eq_one_of_dvd_coprimes h2s (orderOf_dvd_of_pow_eq_one hk2)
        (orderOf_dvd_of_pow_eq_one hks)
  have h2s : Nat.Coprime 2 s := (Nat.coprime_primes Nat.prime_two hs).mpr (Ne.symm hs2)
  have hXK : X ≤ Subgroup.normalizer (K₀ : Set G) := sup_le Subgroup.le_normalizer hZK₀
  have : (CFSG.solvableRadical σ.N).Normal := solvableRadical_normal
  have hNS : σ.N ≤ Subgroup.normalizer (solvRadIn σ.N : Set G) :=
    le_normalizer_map_subtype σ.N (CFSG.solvableRadical σ.N)
  have hKS : ∀ y ∈ K₀, y ∈ solvRadIn σ.N → y ∈ σ.ON := by
    intro y hyK hyS
    obtain ⟨a, ha⟩ := σ.exists_two_pow_mem_ON hσ hII.toNStructure hyS
    exact mem_of_pow_mem_of_pow_mem (Nat.Coprime.pow_left a h2s) ha (hK₀pow y hyK)
  have hb' : ∀ R : Subgroup G, IsSylowOf r R σ.ON →
      X ⊓ Subgroup.centralizer (R : Set G) ≤ σ.ON := by
    intro R hR w hw
    have hwN : w ∈ σ.N := hXN hw.1
    have hwS : w ∈ solvRadIn σ.N :=
      σ.centralizer_le_solvRad_of_constrained hσ hII.toNStructure hr hr2 hR hc ⟨hwN, hw.2⟩
    have hwK : ∀ (k : G) (hk : k ∈ K₀), Commute (π ⟨w, hwN⟩) (π ⟨k, hK₀N hk⟩) := by
      intro k hk
      apply (hπcomm _ _ hwN (hK₀N hk)).mp
      apply hKS
      · exact K₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXK hw.1) k).mp hk) (K₀.inv_mem hk)
      · have h1 : k * w⁻¹ * k⁻¹ ∈ solvRadIn σ.N :=
          (Subgroup.mem_normalizer_iff.mp (hNS (hK₀N hk)) _).mp
            ((solvRadIn σ.N).inv_mem hwS)
        have e : w * k * w⁻¹ * k⁻¹ = w * (k * w⁻¹ * k⁻¹) := by group
        rw [e]
        exact (solvRadIn σ.N).mul_mem hwS h1
    have hw' : w ∈ ((Subgroup.zpowers g₀ ⊔ K₀ : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hw.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZK₀] at hw'
    obtain ⟨g, hg, k₁, hk₁, hgk⟩ := hw'
    have hgN : g ∈ σ.N := hXN (Subgroup.mem_sup_right hg)
    have hk₁N : k₁ ∈ σ.N := hK₀N hk₁
    have hgK : ∀ k ∈ K₀, g * k * g⁻¹ * k⁻¹ ∈ σ.ON := by
      intro k hk
      apply (hπcomm _ _ hgN (hK₀N hk)).mpr
      have e : π ⟨g, hgN⟩ = π ⟨w, hwN⟩ * (π ⟨k₁, hk₁N⟩)⁻¹ := by
        rw [← hπinv _ hk₁N, ← hπmul _ _ hwN (σ.N.inv_mem hk₁N)]
        congr 1
        apply Subtype.ext
        change g = w * k₁⁻¹
        rw [← hgk]
        group
      rw [e]
      exact (hwK k hk).mul_left
        ((hπcomm _ _ hk₁N (hK₀N hk)).mp (hK₀comm k₁ hk₁ k hk)).inv_left
    have hgON : g ∈ σ.ON := by
      by_contra hgON
      obtain ⟨k, hk, hkON⟩ := hK₀ne
      exact hkON (hfpf' g hg hgON k hk (hgK k hk))
    apply hKS w _ hwS
    rw [← hgk]
    exact K₀.mul_mem (hONK₀ hgON) hk₁
  have hidx : σ.ON.relIndex X = 2 * r * s := by
    have hrs : Nat.Coprime r s := (Nat.coprime_primes hr hs).mpr (Ne.symm hsr)
    have h2rs : Nat.Coprime (2 * r) s := Nat.coprime_mul_iff_left.mpr ⟨h2s, hrs⟩
    rw [← Subgroup.relIndex_mul_relIndex σ.ON K₀ X hONK₀ le_sup_left, hK₀idx]
    have hX' : X = Subgroup.zpowers g₀ ⊔ K₀ := sup_comm _ _
    rw [hX', relIndex_sup_right_of_le_normalizer hZK₀]
    have hn : 2 * r ∣ orderOf g₀ :=
      (hord _).mp (by rw [pow_orderOf_eq_one]; exact one_mem _)
    have hinf : K₀ ⊓ Subgroup.zpowers g₀ = Subgroup.zpowers (g₀ ^ (2 * r)) := by
      apply le_antisymm
      · rintro y ⟨hyK, hyZ⟩
        obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hyZ)
        have h1 : g₀ ^ (j * s) ∈ σ.ON := by
          rw [pow_mul]
          exact hK₀pow _ hyK
        obtain ⟨c, rfl⟩ := h2rs.dvd_of_dvd_mul_right ((hord _).mp h1)
        rw [pow_mul g₀ (2 * r) c]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      · rw [Subgroup.zpowers_le]
        exact ⟨hONK₀ ((hord _).mpr dvd_rfl), Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
    have h1 := Subgroup.relIndex_mul_card K₀ (Subgroup.zpowers g₀)
    rw [hinf, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_pow_of_dvd (Nat.mul_ne_zero two_ne_zero hr.ne_zero) hn] at h1
    have hpos : 0 < orderOf g₀ / (2 * r) :=
      Nat.div_pos (Nat.le_of_dvd (orderOf_pos g₀) hn) (Nat.mul_pos two_pos hr.pos)
    have h4 : K₀.relIndex (Subgroup.zpowers g₀) = 2 * r := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [h1]
      exact (Nat.mul_div_cancel' hn).symm
    rw [h4]
    ring
  exact h75 hONK₀ le_sup_left (hXN.trans σ.N_le_normalizer_ON) hXK σ.odd_card_ON hr hs hr2 hs2
    (Ne.symm hsr) hidx hK₀idx hx₂X hvX hσ.x₂_order ⟨m, hvm⟩ hvx₂ hord hfpf' hb'

theorem lemmaIV76 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hr : σ.HypIV7 r)
    (hc : σ.Constrained r) (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G))
    (h75 : ∀ {X Y K : Subgroup G}, Y ≤ K → K ≤ X →
      X ≤ Subgroup.normalizer (Y : Set G) → X ≤ Subgroup.normalizer (K : Set G) →
      Odd (Nat.card Y) → ∀ {p r : ℕ}, p.Prime → r.Prime → p ≠ 2 → r ≠ 2 → p ≠ r →
      Y.relIndex X = 2 * p * r → Y.relIndex K = r → ∀ {t u : G}, t ∈ X → u ∈ X →
      orderOf t = 2 → (∃ n : ℕ, u ^ p ^ n = 1) → t * u = u * t →
      (∀ k : ℕ, (t * u) ^ k ∈ Y ↔ 2 * p ∣ k) →
      (∀ g ∈ Subgroup.zpowers (t * u), g ∉ Y → ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ Y → k ∈ Y) →
      (∀ R : Subgroup G, IsSylowOf p R Y → X ⊓ Subgroup.centralizer (R : Set G) ≤ Y) →
      ∃ R : Subgroup G, IsSylowOf p R Y ∧ t * u ∈ Subgroup.normalizer (R : Set G) ∧
        ∃ z ∈ R, z * t = t * z ∧ z ^ p = 1 ∧ z * u ≠ u * z)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_II43iii : ∀ y ∈ σ.L, y ∈ Subgroup.centralizer (σ.D : Set G) → Odd (orderOf y) →
      y ∈ σ.ON)
    (h_II43 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ w ∈ Subgroup.centralizer (σ.D : Set G),
      (∃ n : ℕ, w ^ p ^ n = 1) → w ∉ σ.L → w ^ p ∈ σ.ON → ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ p ∧
        ∃ K₀ : Subgroup G, σ.ON ≤ K₀ ∧ K₀ ≤ σ.N ∧ σ.ON.relIndex K₀ = s ∧
          w ∈ Subgroup.normalizer (K₀ : Set G) ∧ (∀ k ∈ K₀, σ.x₂ * k * σ.x₂⁻¹ * k ∈ σ.ON) ∧
          ∀ k ∈ K₀, w * k * w⁻¹ * k⁻¹ ∈ σ.ON → k ∈ σ.ON)
    {v : G} (hvP : v ∈ P) (hvL : v ∉ σ.L) (hvr : v ^ r ∈ σ.L) {m : ℕ}
    (hvm : orderOf v = r ^ m) :
    ¬ ∀ a ∈ omegaPow r m P, ∀ b ∈ omegaPow r m P, a * b = b * a := by
  intro hab
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  set Ω : Subgroup G := omegaPow r m P with hΩdef
  have hPN : P ≤ σ.N := hP.le.trans σ.C_le_N
  have hΩP : Ω ≤ P := omegaPow_le r m P
  have hvm' : v ^ r ^ m = 1 := by
    rw [← hvm]
    exact pow_orderOf_eq_one v
  have hvΩ : v ∈ Ω := mem_omegaPow hvP hvm'
  have hm1 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hvm
    exact hvL (hvm ▸ one_mem _)
  have hDΩ : σ.D ≤ Subgroup.normalizer (Ω : Set G) :=
    hPD.trans (normalizer_le_normalizer_omegaPow r m P)
  have hΩLodd : Odd (Nat.card (Ω ⊓ σ.L : Subgroup G)) :=
    odd_card_of_isPGroup' hr.prime hr2 (hP.isPGroup.to_le (inf_le_left.trans hΩP))
  obtain ⟨l₀, hl₀, hfix⟩ := exists_fixed_mem_coset σ.isPGroup_two_D hΩLodd (v := v) (by
    intro d hd l hl
    refine ⟨?_, ?_⟩
    · exact Ω.mul_mem (Ω.inv_mem hvΩ)
        ((Subgroup.mem_normalizer_iff.mp (hDΩ hd) _).mp (Ω.mul_mem hvΩ hl.1))
    · have hdL : d ∈ σ.L := σ.D_le_L' hd
      have h1 : v⁻¹ * d * v⁻¹⁻¹ ∈ σ.L :=
        (Subgroup.mem_normalizer_iff.mp (h_L_normal (σ.N.inv_mem (hPN hvP))) d).mp hdL
      have e : v⁻¹ * (d * (v * l) * d⁻¹) = (v⁻¹ * d * v⁻¹⁻¹) * l * d⁻¹ := by group
      rw [e]
      exact σ.L.mul_mem (σ.L.mul_mem h1 hl.2) (σ.L.inv_mem hdL))
  set v₁ : G := v * l₀ with hv₁def
  have hv₁Ω : v₁ ∈ Ω := Ω.mul_mem hvΩ hl₀.1
  have hv₁P : v₁ ∈ P := hΩP hv₁Ω
  have hv₁N : v₁ ∈ σ.N := hPN hv₁P
  have hv₁L : v₁ ∉ σ.L := by
    intro h
    apply hvL
    have e : v = v₁ * l₀⁻¹ := by rw [hv₁def]; group
    rw [e]
    exact σ.L.mul_mem h (σ.L.inv_mem hl₀.2)
  have hv₁D : v₁ ∈ Subgroup.centralizer (σ.D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have h := hfix d hd
    calc d * v₁ = d * v₁ * d⁻¹ * d := by group
      _ = v₁ * d := by rw [h]
  have hv₁m : v₁ ^ r ^ m = 1 := pow_eq_one_of_mem_omegaPow hab hv₁Ω
  have hv₁rL : v₁ ^ r ∈ σ.L := by
    have h := σ.L.mul_mem (σ.L.pow_mem hvr 1)
      (inv_pow_mul_pow_mem (h_L_normal (hPN hvP)) hl₀.2 r)
    rwa [pow_one, mul_inv_cancel_left] at h
  have hv₁rON : v₁ ^ r ∈ σ.ON := by
    refine h_II43iii _ hv₁rL (Subgroup.pow_mem _ hv₁D r) ?_
    have h1 : orderOf (v₁ ^ r) ∣ r ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← pow_mul, mul_comm, pow_mul, hv₁m, one_pow]
    exact (hr.prime.eq_two_or_odd'.resolve_left hr2).pow.of_dvd_nat h1
  have hONL : σ.ON ≤ σ.L := hσ.ON_le_L₀.trans le_sup_left
  have hv₁ON : v₁ ∉ σ.ON := fun h => hv₁L (hONL h)
  obtain ⟨s, hs, hs2, hsr, K₀, hONK₀, hK₀N, hK₀idx, hv₁K₀, hinvK, hfpfK⟩ :=
    h_II43 r hr.prime hr2 v₁ hv₁D ⟨m, hv₁m⟩ hv₁L hv₁rON
  have hx₂D : σ.x₂ ∈ σ.D := σ.x₂_mem_D' hσ
  have hv₁x₂ : σ.x₂ * v₁ = v₁ * σ.x₂ := Subgroup.mem_centralizer_iff.mp hv₁D σ.x₂ hx₂D
  obtain ⟨R₀, hR₀, hg₀R₀, z, hzR₀, hzx₂, hzr, hzv⟩ :=
    σ.exists_sylow_ON_of_frobenius hσ hII hr.prime hr2 hc h75 hv₁N hv₁x₂ hv₁m hv₁ON hv₁rON hs
      hs2 hsr hONK₀ hK₀N hK₀idx hv₁K₀ hinvK hfpfK
  have hx₂sq : σ.x₂ ^ 2 = 1 := by
    rw [← hσ.x₂_order]
    exact pow_orderOf_eq_one _
  have hrm_odd : Odd (r ^ m) := (hr.prime.eq_two_or_odd'.resolve_left hr2).pow
  have hv₁R₀ : v₁ ∈ Subgroup.normalizer (R₀ : Set G) := by
    have e : (σ.x₂ * v₁) ^ (r ^ m + 1) = v₁ := by
      rw [(show Commute σ.x₂ v₁ from hv₁x₂).mul_pow,
        pow_eq_one_of_sq_eq_one hx₂sq hrm_odd.add_one, one_mul, pow_succ, hv₁m, one_mul]
    rw [← e]
    exact Subgroup.pow_mem _ hg₀R₀ _
  have hzON : z ∈ σ.ON := hR₀.le hzR₀
  have hzC : z ∈ σ.C := by
    change z ∈ Subgroup.centralizer ((Subgroup.closure {σ.x, σ.x₂} : Subgroup G) : Set G)
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl
    · exact ((σ.mem_N_iff z).mp (σ.ON_le_N hzON)).symm
    · exact hzx₂.symm
  have hv₁p : IsPGroup r (Subgroup.zpowers v₁) := hP.isPGroup.to_le (Subgroup.zpowers_le.mpr hv₁P)
  have hRV : IsPGroup r (R₀ ⊔ Subgroup.zpowers v₁ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hR₀.isPGroup hv₁p (Subgroup.zpowers_le.mpr hv₁R₀)
  set W : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers v₁ with hWdef
  have hWRV : W ≤ R₀ ⊔ Subgroup.zpowers v₁ :=
    sup_le_sup_right (Subgroup.zpowers_le.mpr hzR₀) _
  have hWC : W ≤ σ.C := sup_le (Subgroup.zpowers_le.mpr hzC)
    (Subgroup.zpowers_le.mpr (hP.le hv₁P))
  have hWp : IsPGroup r (W.subgroupOf σ.C) := (hRV.to_le hWRV).comap_subtype
  obtain ⟨S', hS'⟩ := hWp.exists_le_sylow
  have hPs : IsSylowOf r ((S' : Subgroup σ.C).map σ.C.subtype) σ.C := ⟨S', rfl⟩
  have hWPs : W ≤ (S' : Subgroup σ.C).map σ.C.subtype := by
    intro w hw
    exact ⟨⟨w, hWC hw⟩, hS' hw, rfl⟩
  obtain ⟨c, -, hconj⟩ := hP.exists_mem_conj hPs
  have hconjΩ : ∀ y ∈ W, y ^ r ^ m = 1 → c⁻¹ * y * c ∈ Ω := by
    intro y hy hym
    refine mem_omegaPow ((hconj y).mp (hWPs hy)) ?_
    have e : c⁻¹ * y * c = c⁻¹ * y * c⁻¹⁻¹ := by rw [inv_inv]
    rw [e, conj_pow, hym, mul_one, mul_inv_cancel]
  have hzm : z ^ r ^ m = 1 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm1
    rw [hk, pow_succ', pow_mul, hzr, one_pow]
  have h1 := hab _ (hconjΩ z (Subgroup.mem_sup_left (Subgroup.mem_zpowers z)) hzm) _
    (hconjΩ v₁ (Subgroup.mem_sup_right (Subgroup.mem_zpowers v₁)) hv₁m)
  apply hzv
  have e1 : c⁻¹ * z * c * (c⁻¹ * v₁ * c) = c⁻¹ * (z * v₁) * c := by group
  have e2 : c⁻¹ * v₁ * c * (c⁻¹ * z * c) = c⁻¹ * (v₁ * z) * c := by group
  rw [e1, e2] at h1
  exact mul_left_cancel (mul_right_cancel h1)

end K

theorem exists_IV7Data_of_constrained (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) (hc : σ.Constrained r) {P R : Subgroup G} (hP : IsSylowOf r P σ.C)
    (hPD : σ.D ≤ Subgroup.normalizer (P : Set G)) (hR : IsSylowOf r R σ.ON)
    (hRD : σ.D ≤ Subgroup.normalizer (R : Set G)) (hRP : P ≤ Subgroup.normalizer (R : Set G))
    (h75 : ∀ {X Y K : Subgroup G}, Y ≤ K → K ≤ X →
      X ≤ Subgroup.normalizer (Y : Set G) → X ≤ Subgroup.normalizer (K : Set G) →
      Odd (Nat.card Y) → ∀ {p r : ℕ}, p.Prime → r.Prime → p ≠ 2 → r ≠ 2 → p ≠ r →
      Y.relIndex X = 2 * p * r → Y.relIndex K = r → ∀ {t u : G}, t ∈ X → u ∈ X →
      orderOf t = 2 → (∃ n : ℕ, u ^ p ^ n = 1) → t * u = u * t →
      (∀ k : ℕ, (t * u) ^ k ∈ Y ↔ 2 * p ∣ k) →
      (∀ g ∈ Subgroup.zpowers (t * u), g ∉ Y → ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ Y → k ∈ Y) →
      (∀ R : Subgroup G, IsSylowOf p R Y → X ⊓ Subgroup.centralizer (R : Set G) ≤ Y) →
      ∃ R : Subgroup G, IsSylowOf p R Y ∧ t * u ∈ Subgroup.normalizer (R : Set G) ∧
        ∃ z ∈ R, z * t = t * z ∧ z ^ p = 1 ∧ z * u ≠ u * z)
    (h_L_normal : σ.N ≤ Subgroup.normalizer (σ.L : Set G))
    (h_C : ∀ c ∈ σ.C, Odd (orderOf c) → c ∈ oddCoreIn σ.C)
    (h_II33 : ∃ g ∈ σ.N, ∀ n ∈ σ.N, ∃ k : ℤ, n * (g ^ k)⁻¹ ∈ σ.L)
    (h_II42 : ⁅σ.C ⊓ σ.L, σ.C ⊓ σ.L⁆ ≤ solvRadIn σ.L)
    (h_II43iii : ∀ y ∈ σ.L, y ∈ Subgroup.centralizer (σ.D : Set G) → Odd (orderOf y) →
      y ∈ σ.ON)
    (h_II43 : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ w ∈ Subgroup.centralizer (σ.D : Set G),
      (∃ n : ℕ, w ^ p ^ n = 1) → w ∉ σ.L → w ^ p ∈ σ.ON → ∃ s : ℕ, s.Prime ∧ s ≠ 2 ∧ s ≠ p ∧
        ∃ K₀ : Subgroup G, σ.ON ≤ K₀ ∧ K₀ ≤ σ.N ∧ σ.ON.relIndex K₀ = s ∧
          w ∈ Subgroup.normalizer (K₀ : Set G) ∧ (∀ k ∈ K₀, σ.x₂ * k * σ.x₂⁻¹ * k ∈ σ.ON) ∧
          ∀ k ∈ K₀, w * k * w⁻¹ * k⁻¹ ∈ σ.ON → k ∈ σ.ON) :
    ∃ d : σ.IV7Data r, d.P = P ∧ d.R = R ∧ d.Nstar = σ.N := by
  by_cases hU : pPrimeCoreIn r (σ.IV7K P) ⊔ (P ⊓ σ.L) = pPrimePCoreIn r (σ.IV7K P)
  · obtain ⟨d, hdP, hdR, hdN, -⟩ :=
      σ.lemmaIV73 hσ hII hr hc hP hPD hR hRD hRP h_L_normal h_C h_II42 hU
    exact ⟨d, hdP, hdR, hdN⟩
  · have : Fact r.Prime := ⟨hr.prime⟩
    obtain ⟨v, hvP, hvL, hvr, hvmin⟩ := σ.exists_minimal_order_not_mem_L hr.prime h_L_normal hP hU
    obtain ⟨m, hvm⟩ := (IsPGroup.iff_orderOf.mp hP.isPGroup) ⟨v, hvP⟩
    rw [Subgroup.orderOf_mk] at hvm
    obtain ⟨d, hdP, hdR, hdN, -⟩ := σ.lemmaIV74 hσ hII hr hc hP hPD hR hRD hRP h_L_normal
      h_II33 h_II42 hU hvP hvL hvr hvmin hvm
      (σ.lemmaIV76 hσ hII hr hc hP hPD h75 h_L_normal h_II43iii h_II43 hvP hvL hvr hvm)
    exact ⟨d, hdP, hdR, hdN⟩

end Setting

end CFSG.ABGTheoremB

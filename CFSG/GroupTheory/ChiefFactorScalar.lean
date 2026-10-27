module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityModule
public import TauCeti.RingTheory.ZMod.Torsion

public section

open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

private noncomputable def normalizerConjHom (M : Subgroup G) {c : G}
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) : M →* M :=
  (Subgroup.normalizerMonoidHom M ⟨c, hcM⟩).toMonoidHom

private noncomputable def conjMem (M : Subgroup G) {c : G}
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (x : M) : M :=
  ⟨c * (x : G) * c⁻¹, (Subgroup.mem_normalizer_iff.mp hcM (x : G)).mp x.2⟩

private lemma normalizerConjHom_apply_coe (M : Subgroup G) {c : G}
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (x : M) :
    ((normalizerConjHom M hcM x : M) : G) = c * (x : G) * c⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe M ⟨c, hcM⟩ x

private lemma normalizerConjHom_eq_conjMem (M : Subgroup G) {c : G}
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (x : M) :
    normalizerConjHom M hcM x = conjMem M hcM x :=
  Subtype.ext (normalizerConjHom_apply_coe M hcM x)

private noncomputable def quotientHom (N M : Subgroup G) [(N.subgroupOf M).Normal] :
    M →* (M ⧸ N.subgroupOf M) :=
  QuotientGroup.mk' (N.subgroupOf M)

private noncomputable def chiefScalarHom (N M : Subgroup G) (c : G) (w : ℕ)
    (hcM : c ∈ Subgroup.normalizer (M : Set G))
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] :
    M →* (M ⧸ N.subgroupOf M) :=
  (quotientHom N M).comp (normalizerConjHom M hcM) *
    (((powMonoidHom w).comp (quotientHom N M))⁻¹)

private lemma chiefScalarHom_apply (N M : Subgroup G) (c : G) (w : ℕ)
    (hcM : c ∈ Subgroup.normalizer (M : Set G))
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] (x : M) :
    chiefScalarHom N M c w hcM x =
      QuotientGroup.mk' (N.subgroupOf M) (conjMem M hcM x) *
        (QuotientGroup.mk' (N.subgroupOf M) x ^ w)⁻¹ := by
  simp [chiefScalarHom, quotientHom, normalizerConjHom_eq_conjMem, MonoidHom.mul_apply]

private lemma chiefScalarHom_eq_one_iff (N M : Subgroup G) (c : G) (w : ℕ)
    (hcM : c ∈ Subgroup.normalizer (M : Set G))
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] (x : M) :
    chiefScalarHom N M c w hcM x = 1 ↔
      c * (x : G) * c⁻¹ * ((x : G) ^ w)⁻¹ ∈ N := by
  have h1 : QuotientGroup.mk' (N.subgroupOf M) (conjMem M hcM x) *
      (QuotientGroup.mk' (N.subgroupOf M) x ^ w)⁻¹ =
      QuotientGroup.mk' (N.subgroupOf M) (conjMem M hcM x * (x ^ w)⁻¹) := by
    rw [← map_pow, ← map_inv, ← map_mul]
  rw [chiefScalarHom_apply, h1]
  change (QuotientGroup.mk (conjMem M hcM x * (x ^ w)⁻¹) : M ⧸ N.subgroupOf M) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simp [conjMem]

private noncomputable def chiefScalarSubgroup (N M : Subgroup G) (c : G) (w : ℕ)
    (hcM : c ∈ Subgroup.normalizer (M : Set G))
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] : Subgroup G :=
  (chiefScalarHom N M c w hcM).ker.map M.subtype

private lemma mem_chiefScalarSubgroup (N M : Subgroup G) (c : G) (w : ℕ)
    (hcM : c ∈ Subgroup.normalizer (M : Set G))
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] (x : M) :
    (x : G) ∈ chiefScalarSubgroup N M c w hcM ↔
      c * (x : G) * c⁻¹ * ((x : G) ^ w)⁻¹ ∈ N := by
  rw [chiefScalarSubgroup]
  change M.subtype x ∈ (chiefScalarHom N M c w hcM).ker.map M.subtype ↔ _
  rw [Subgroup.mem_map_iff_mem M.subtype_injective, MonoidHom.mem_ker,
    chiefScalarHom_eq_one_iff]

private noncomputable def powChiefSubgroup (N M : Subgroup G) (r : ℕ)
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] : Subgroup G :=
  ((powMonoidHom r).comp (quotientHom N M)).ker.map M.subtype

private lemma mem_powChiefSubgroup (N M : Subgroup G) (r : ℕ)
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] (x : M) :
    (x : G) ∈ powChiefSubgroup N M r ↔ (x : G) ^ r ∈ N := by
  rw [powChiefSubgroup]
  change M.subtype x ∈ (((powMonoidHom r).comp (quotientHom N M)).ker.map M.subtype) ↔ _
  rw [Subgroup.mem_map_iff_mem M.subtype_injective, MonoidHom.mem_ker,
    MonoidHom.comp_apply, powMonoidHom_apply, ← map_pow]
  change (QuotientGroup.mk (x ^ r) : M ⧸ N.subgroupOf M) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simp

private lemma conj_mem_normal_of_commutator_le {P M N : Subgroup G} (hMP : M ≤ P)
    (hNM : N ≤ M) (hPM : ⁅M, P⁆ ≤ N) {x : G} (hx : x ∈ M) {y : G} (hy : y ∈ N) :
    x * y * x⁻¹ ∈ N := by
  have h := hPM (Subgroup.commutator_mem_commutator hx (hMP (hNM hy)))
  have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
    simp only [commutatorElement_def]
    group
  rw [hxy]
  exact N.mul_mem h hy

private lemma le_normalizer_of_between {P M N : Subgroup G} (hMP : M ≤ P)
    (hPM : ⁅M, P⁆ ≤ N) {K : Subgroup G} (hNK : N ≤ K) (hKM : K ≤ M) :
    P ≤ Subgroup.normalizer (K : Set G) := by
  have hforward : ∀ y ∈ P, ∀ z ∈ K, y * z * y⁻¹ ∈ K := by
    intro y hy z hz
    have hcomm' : ⁅z, y⁆ ∈ N := (Subgroup.commutator_le.mp hPM) z (hKM hz) y hy
    have hcomm : ⁅y, z⁆ ∈ N := by
      rw [← commutatorElement_inv]
      exact N.inv_mem hcomm'
    have hyz : y * z * y⁻¹ = ⁅y, z⁆ * z := by
      simp only [commutatorElement_def]
      group
    rw [hyz]
    exact K.mul_mem (hNK hcomm) hz
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro k
  exact ⟨hforward x hx k, fun hk => by
    have h := hforward x⁻¹ (P.inv_mem hx) (x * k * x⁻¹) hk
    have heq : x⁻¹ * (x * k * x⁻¹) * (x⁻¹)⁻¹ = k := by group
    rwa [heq] at h⟩

private lemma powChiefSubgroup_normalizer {Y N M : Subgroup G} {r : ℕ}
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)]
    (hYM : Y ≤ Subgroup.normalizer (M : Set G))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) :
    Y ≤ Subgroup.normalizer (powChiefSubgroup N M r : Set G) := by
  have hKM : powChiefSubgroup N M r ≤ M := Subgroup.map_subtype_le _
  have hforward : ∀ y ∈ Y, ∀ k ∈ powChiefSubgroup N M r,
      y * k * y⁻¹ ∈ powChiefSubgroup N M r := by
    intro y hy k hk
    have hkM : k ∈ M := hKM hk
    have hkr : (⟨k, hkM⟩ : M) ^ r ∈ N.subgroupOf M :=
      (mem_powChiefSubgroup N M r ⟨k, hkM⟩).mp hk
    have hkr' : k ^ r ∈ N := by
      have := Subgroup.mem_subgroupOf.mp hkr
      simpa using this
    have hkyM : y * k * y⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hYM hy) k).mp hkM
    refine (mem_powChiefSubgroup N M r ⟨y * k * y⁻¹, hkyM⟩).mpr ?_
    have hpow : (y * k * y⁻¹) ^ r = y * k ^ r * y⁻¹ := conj_pow
    rw [hpow]
    exact (Subgroup.mem_normalizer_iff.mp (hYN hy) (k ^ r)).mp hkr'
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro k
  exact ⟨hforward y hy k, fun hk => by
    have h := hforward y⁻¹ (Y.inv_mem hy) (y * k * y⁻¹) hk
    have heq : y⁻¹ * (y * k * y⁻¹) * (y⁻¹)⁻¹ = k := by group
    rwa [heq] at h⟩

private lemma exists_mem_powChiefSubgroup_not_mem {P M N : Subgroup G} {r : ℕ}
    [Fact r.Prime] [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)]
    [Finite M] (hP : IsPGroup r P) (hMP : M ≤ P) (hPM : ⁅M, P⁆ ≤ N)
    (hNM : N < M) :
    ∃ m : G, m ∈ powChiefSubgroup N M r ∧ m ∉ N := by
  have hNMle : N ≤ M := hNM.le
  haveI : Nontrivial (M ⧸ N.subgroupOf M) := by
    rw [QuotientGroup.nontrivial_iff]
    intro htop
    refine (ne_of_lt hNM) (le_antisymm hNMle ?_)
    intro m hm
    have hmem : (⟨m, hm⟩ : M) ∈ N.subgroupOf M := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have hQp : IsPGroup r (M ⧸ N.subgroupOf M) :=
    (hP.to_le hMP).to_quotient (N.subgroupOf M)
  have hdvd : r ∣ Nat.card (M ⧸ N.subgroupOf M) := by
    rcases hQp.card_eq_or_dvd with h | h
    · rw [Nat.card_eq_one_iff_unique] at h
      exact absurd h.1 (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial _›)
    · exact h
  obtain ⟨x, hxord⟩ : ∃ x : M ⧸ N.subgroupOf M, orderOf x = r :=
    exists_prime_orderOf_dvd_card' (G := M ⧸ N.subgroupOf M) r hdvd
  have hx1 : x ≠ 1 := by
    intro hx
    rw [hx, orderOf_one] at hxord
    exact (Fact.out : r.Prime).ne_one hxord.symm
  have hxpow : x ^ r = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (s := N.subgroupOf M) x
  have hmK : (m : G) ∈ powChiefSubgroup N M r := by
    refine (mem_powChiefSubgroup N M r m).mpr ?_
    have h1 : QuotientGroup.mk' (N.subgroupOf M) ((m : M) ^ r) = 1 := by
      rw [map_pow]
      change (QuotientGroup.mk (m : M) : M ⧸ N.subgroupOf M) ^ r = 1
      rw [hm, hxpow]
    have h2 : (m : M) ^ r ∈ N.subgroupOf M :=
      (QuotientGroup.eq_one_iff (N := N.subgroupOf M) (x := (m : M) ^ r)).mp h1
    exact Subgroup.mem_subgroupOf.mp h2
  have hmN : (m : G) ∉ N := by
    intro h
    have hm1 : QuotientGroup.mk' (N.subgroupOf M) (m : M) = 1 :=
      (QuotientGroup.eq_one_iff (N := N.subgroupOf M) (x := (m : M))).mpr
        (Subgroup.mem_subgroupOf.mpr h)
    have hm1' : (QuotientGroup.mk (m : M) : M ⧸ N.subgroupOf M) = 1 := by
      simpa [QuotientGroup.mk'_apply] using hm1
    rw [hm] at hm1'
    exact hx1 hm1'
  exact ⟨m, hmK, hmN⟩

private lemma powChiefSubgroup_ne {P M N : Subgroup G} {r : ℕ} [Fact r.Prime]
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] [Finite M]
    (hP : IsPGroup r P) (hMP : M ≤ P) (hPM : ⁅M, P⁆ ≤ N) (hNM : N < M) :
    powChiefSubgroup N M r ≠ N := by
  intro hEq
  obtain ⟨m, hmK, hmN⟩ := exists_mem_powChiefSubgroup_not_mem hP hMP hPM hNM
  exact hmN (hEq ▸ hmK)

theorem isChiefFactorUnder_of_commutator_le {G : Type*} [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] {P Y N M : Subgroup G} (hP : IsPGroup r P) (hNM : N < M) (hMP : M ≤ P)
    (hPM : ⁅M, P⁆ ≤ N) (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (hYM : Y ≤ Subgroup.normalizer (M : Set G))
    (hmin : ∀ K : Subgroup G, N ≤ K → K ≤ M → P ⊔ Y ≤ Subgroup.normalizer (K : Set G) →
      K = N ∨ K = M) :
    CFSG.ABGLocalTools.IsChiefFactorUnder r Y M N := by
  classical
  have hNMle : N ≤ M := hNM.le
  have hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N := fun x hx y hy =>
    hPM (Subgroup.commutator_mem_commutator hx (hMP hy))
  have hcommM : _root_.commutator ↥M ≤ N.subgroupOf M := by
    change ⁅(⊤ : Subgroup ↥M), ⊤⁆ ≤ N.subgroupOf M
    rw [Subgroup.commutator_le]
    intro x _ y _
    have h := hcomm (x : G) x.2 (y : G) y.2
    rw [Subgroup.mem_subgroupOf]
    change ⁅(x : G), (y : G)⁆ ∈ N
    exact h
  haveI hNnorm : (N.subgroupOf M).Normal := Subgroup.Normal.of_commutator_le (↥M) hcommM
  haveI hQcomm : IsMulCommutative (M ⧸ N.subgroupOf M) := by
    refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
    change ⁅(⊤ : Subgroup ↥M), ⊤⁆ ≤ N.subgroupOf M
    rw [Subgroup.commutator_le]
    intro x _ y _
    have h := hcomm (x : G) x.2 (y : G) y.2
    rw [Subgroup.mem_subgroupOf]
    change ⁅(x : G), (y : G)⁆ ∈ N
    exact h
  have hexp : ∀ m ∈ M, m ^ r ∈ N := by
    have hNK : N ≤ powChiefSubgroup N M r := by
      intro n hn
      have hnM : n ∈ M := hNMle hn
      exact (mem_powChiefSubgroup N M r ⟨n, hnM⟩).mpr (N.pow_mem hn r)
    have hKM : powChiefSubgroup N M r ≤ M := Subgroup.map_subtype_le _
    have hPK : P ≤ Subgroup.normalizer (powChiefSubgroup N M r : Set G) :=
      le_normalizer_of_between hMP hPM hNK hKM
    have hYK : Y ≤ Subgroup.normalizer (powChiefSubgroup N M r : Set G) :=
      powChiefSubgroup_normalizer hYM hYN
    have hKne : powChiefSubgroup N M r ≠ N := powChiefSubgroup_ne hP hMP hPM hNM
    rcases hmin (powChiefSubgroup N M r) hNK hKM (sup_le hPK hYK) with hKN | hKM'
    · exact absurd hKN hKne
    · intro m hm
      exact (mem_powChiefSubgroup N M r ⟨m, hm⟩).mp (by rw [hKM']; exact hm)
  refine ⟨hNM, hYM, hYN, ?_, ?_, hexp, ?_⟩
  · intro x hx y hy
    exact conj_mem_normal_of_commutator_le hMP hNMle hPM hx hy
  · intro x hx y hy
    exact hcomm x hx y hy
  · intro X hNX hXM hYX
    exact hmin X hNX hXM (sup_le (le_normalizer_of_between hMP hPM hNX hXM) hYX)


private lemma le_normalizer_chiefScalarSubgroup {N M Y : Subgroup G} {c : G} {w : ℕ}
    (hYM : Y ≤ Subgroup.normalizer (M : Set G))
    (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (hcM : c ∈ Subgroup.normalizer (M : Set G))
    (hcY : Y ≤ Subgroup.centralizer ({c} : Set G))
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)] :
    Y ≤ Subgroup.normalizer (chiefScalarSubgroup N M c w hcM : Set G) := by
  have hforward : ∀ y ∈ Y, ∀ k ∈ chiefScalarSubgroup N M c w hcM,
      y * k * y⁻¹ ∈ chiefScalarSubgroup N M c w hcM := by
    intro y hy k hk
    have hkM : k ∈ M := Subgroup.map_subtype_le _ hk
    have hkcond : c * k * c⁻¹ * (k ^ w)⁻¹ ∈ N :=
      (mem_chiefScalarSubgroup N M c w hcM ⟨k, hkM⟩).mp hk
    have hkyM : y * k * y⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hYM hy) k).mp hkM
    refine (mem_chiefScalarSubgroup N M c w hcM ⟨y * k * y⁻¹, hkyM⟩).mpr ?_
    have hcy : c * y = y * c :=
      (Subgroup.mem_centralizer_iff.mp (hcY hy)) c (by simp)
    have h1 : c * (y * k * y⁻¹) * c⁻¹ = y * (c * k * c⁻¹) * y⁻¹ := by
      calc
        c * (y * k * y⁻¹) * c⁻¹ = (c * y) * k * (c * y)⁻¹ := by group
        _ = (y * c) * k * (y * c)⁻¹ := by rw [hcy]
        _ = y * (c * k * c⁻¹) * y⁻¹ := by group
    have h2 : (y * k * y⁻¹) ^ w = y * k ^ w * y⁻¹ := conj_pow
    have hcond : y * (c * k * c⁻¹ * (k ^ w)⁻¹) * y⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hYN hy) _).mp hkcond
    rw [h1, h2]
    have heq : y * (c * k * c⁻¹) * y⁻¹ * (y * k ^ w * y⁻¹)⁻¹ =
        y * (c * k * c⁻¹ * (k ^ w)⁻¹) * y⁻¹ := by group
    rw [heq]
    exact hcond
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro k
  exact ⟨hforward y hy k, fun hk => by
    have h := hforward y⁻¹ (Y.inv_mem hy) (y * k * y⁻¹) hk
    have heq : y⁻¹ * (y * k * y⁻¹) * (y⁻¹)⁻¹ = k := by group
    rwa [heq] at h⟩

theorem trivial_or_fixedPointFree_of_isChiefFactorUnder {G : Type*} [Group G]
    {r : ℕ} {Y N M : Subgroup G} (hchief : CFSG.ABGLocalTools.IsChiefFactorUnder r Y M N)
    {c : G} (hcY : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (hcN : c ∈ Subgroup.normalizer (N : Set G)) :
    (∀ m ∈ M, c * m * c⁻¹ * m⁻¹ ∈ N) ∨ (∀ m ∈ M, c * m * c⁻¹ * m⁻¹ ∈ N → m ∈ N) := by
  classical
  have hNM : N ≤ M := hchief.1.le
  haveI hNnorm : (N.subgroupOf M).Normal := hchief.normal
  haveI hQcomm : IsMulCommutative (M ⧸ N.subgroupOf M) := by
    refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
    change ⁅(⊤ : Subgroup ↥M), ⊤⁆ ≤ N.subgroupOf M
    rw [Subgroup.commutator_le]
    intro x _ y _
    have h := hchief.2.2.2.2.1 (x : G) x.2 (y : G) y.2
    rw [Subgroup.mem_subgroupOf]
    change ⁅(x : G), (y : G)⁆ ∈ N
    exact h
  let K := chiefScalarSubgroup N M c 1 hcM
  have hNK : N ≤ K := by
    intro n hn
    have hnM : n ∈ M := hNM hn
    refine (mem_chiefScalarSubgroup N M c 1 hcM ⟨n, hnM⟩).mpr ?_
    rw [pow_one]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp hcN n).mp hn) (N.inv_mem hn)
  have hKM : K ≤ M := Subgroup.map_subtype_le _
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_chiefScalarSubgroup hchief.2.1 hchief.2.2.1 hcM hcY
  rcases hchief.2.2.2.2.2.2 K hNK hKM hYK with hKN | hKM'
  · right
    intro m hmM hmcond
    have hmK : m ∈ K := by
      refine (mem_chiefScalarSubgroup N M c 1 hcM ⟨m, hmM⟩).mpr ?_
      simpa using hmcond
    rw [hKN] at hmK
    exact hmK
  · left
    intro m hmM
    have hmK : m ∈ K := by rw [hKM']; exact hmM
    have := (mem_chiefScalarSubgroup N M c 1 hcM ⟨m, hmM⟩).mp hmK
    simpa using this



private lemma end_pow_three_sub_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (α : V →ₗ[K] V) (hα3 : α ^ 3 = 1) {ω : K} (hω3 : ω ^ 3 = 1)
    (hωsum : 1 + ω + ω ^ 2 = 0) :
    (α - 1) * (α - ω • 1) * (α - ω ^ 2 • 1) = 0 := by
  have hfac : (Polynomial.X - Polynomial.C (1 : K)) * (Polynomial.X - Polynomial.C ω) *
      (Polynomial.X - Polynomial.C (ω ^ 2)) = Polynomial.X ^ 3 - 1 := by
    have hsum' : (1 : Polynomial K) + Polynomial.C ω + Polynomial.C (ω ^ 2) = 0 := by
      simpa using congrArg (Polynomial.C (R := K)) hωsum
    have hprod' : Polynomial.C ω * Polynomial.C (ω ^ 2) = (1 : Polynomial K) := by
      rw [← map_mul, show ω * ω ^ 2 = ω ^ 3 by ring, hω3, map_one]
    have h : (Polynomial.X - Polynomial.C (1 : K)) * (Polynomial.X - Polynomial.C ω) *
        (Polynomial.X - Polynomial.C (ω ^ 2)) =
        Polynomial.X ^ 3 - 1 +
          (1 + Polynomial.C ω + Polynomial.C (ω ^ 2)) *
            (Polynomial.X - Polynomial.X ^ 2) +
          (Polynomial.C ω * Polynomial.C (ω ^ 2) - 1) * (Polynomial.X - 1) := by
      simp only [Polynomial.C_1, mul_one]
      ring
    rw [hsum', hprod'] at h
    simpa using h
  have hsq : (ω • (1 : V →ₗ[K] V)) ^ 2 = ω ^ 2 • (1 : V →ₗ[K] V) := by
    rw [← Algebra.algebraMap_eq_smul_one (R := K) (A := V →ₗ[K] V) (r := ω),
      ← Algebra.algebraMap_eq_smul_one (R := K) (A := V →ₗ[K] V) (r := ω ^ 2), ← map_pow]
  have h := congrArg (Polynomial.aeval α) hfac
  simpa [hα3, hsq, map_mul, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one] using h



private lemma exists_cube_root_of_mod_three {r : ℕ} [Fact r.Prime] (hr : r % 3 = 1) :
    ∃ ζ : ZMod r, ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ 1 + ζ + ζ ^ 2 = 0 := by
  haveI : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  have h3dvd : 3 ∣ r - 1 := by omega
  obtain ⟨ζ, hζ⟩ := TauCeti.ZMod.exists_isPrimitiveRoot_of_dvd_sub_one
    (Fact.out : r.Prime) h3dvd
  refine ⟨ζ, hζ.pow_eq_one, hζ.ne_one (by norm_num), ?_⟩
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have hζne : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hfac : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
    have h : ζ ^ 3 - 1 = 0 := by rw [hζ3]; ring
    rwa [show (ζ - 1) * (ζ ^ 2 + ζ + 1) = ζ ^ 3 - 1 by ring]
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h (sub_ne_zero.mpr hζne)
  · linear_combination h

private lemma ker_scalar_eq_bot {r : ℕ} [Fact r.Prime] {N M : Subgroup G} {c : G} {w : ℕ}
    [(N.subgroupOf M).Normal] [IsMulCommutative (M ⧸ N.subgroupOf M)]
    [IsElementaryAbelian r (M ⧸ N.subgroupOf M)]
    (hcM : c ∈ Subgroup.normalizer (M : Set G))
    (hKN : chiefScalarSubgroup N M c w hcM = N)
    (α : Additive (M ⧸ N.subgroupOf M) →ₗ[ZMod r]
      Additive (M ⧸ N.subgroupOf M))
    (hαq : ∀ x : M, α (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (conjMem M hcM x))) :
    LinearMap.ker (α - (w : ZMod r) • 1) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  obtain ⟨x, rfl⟩ := CFSG.ABGLocalTools.exists_ofMul_mk (W₁ := M) (W₂ := N) v
  have h1 : α (Additive.ofMul (QuotientGroup.mk x)) =
      (w : ZMod r) • (Additive.ofMul (QuotientGroup.mk x) :
        Additive (M ⧸ N.subgroupOf M)) := by
    simpa [sub_eq_zero] using hv
  rw [hαq x] at h1
  have hw' : ((w : ℕ) : ZMod r) •
      (Additive.ofMul (QuotientGroup.mk x) : Additive (M ⧸ N.subgroupOf M)) =
      Additive.ofMul (QuotientGroup.mk ((x : M) ^ w)) := by
    rw [Nat.cast_smul_eq_nsmul, ← ofMul_pow]
    congr 1
  rw [hw'] at h1
  have h2 : QuotientGroup.mk (conjMem M hcM x) =
      QuotientGroup.mk ((x : M) ^ w) := Additive.ofMul.injective h1
  have hhom : chiefScalarHom N M c w hcM x = 1 := by
    rw [chiefScalarHom_apply]
    have h2' : QuotientGroup.mk' (N.subgroupOf M) (conjMem M hcM x) =
        (QuotientGroup.mk' (N.subgroupOf M) x) ^ w := by
      rw [← map_pow]
      simpa [QuotientGroup.mk'_apply] using h2
    rw [h2']
    exact mul_inv_cancel _
  have hcond := (chiefScalarHom_eq_one_iff N M c w hcM x).mp hhom
  have hxK : (x : G) ∈ chiefScalarSubgroup N M c w hcM :=
    (mem_chiefScalarSubgroup N M c w hcM x).mpr hcond
  rw [hKN] at hxK
  have hxN : x ∈ N.subgroupOf M := Subgroup.mem_subgroupOf.mpr hxK
  have hx1 : QuotientGroup.mk x = 1 :=
    (QuotientGroup.eq_one_iff (N := N.subgroupOf M) x).mpr hxN
  rw [hx1]
  rfl

private lemma false_of_three_kernels {r : ℕ} [Fact r.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] (α : V →ₗ[ZMod r] V) (hα3 : α ^ 3 = 1)
    {ζ : ZMod r} (hζ3 : ζ ^ 3 = 1) (hζsum : 1 + ζ + ζ ^ 2 = 0)
    (hker1 : LinearMap.ker (α - (1 : V →ₗ[ZMod r] V)) = ⊥)
    (hkerw1 : LinearMap.ker (α - ζ • (1 : V →ₗ[ZMod r] V)) = ⊥)
    (hkerw2 : LinearMap.ker (α - ζ ^ 2 • (1 : V →ₗ[ZMod r] V)) = ⊥)
    {a : V} (ha : a ≠ (0 : V)) : False := by
  have hinj1 : Function.Injective (α - (1 : V →ₗ[ZMod r] V)) :=
    LinearMap.ker_eq_bot.mp hker1
  have hinjw1 : Function.Injective (α - ζ • (1 : V →ₗ[ZMod r] V)) :=
    LinearMap.ker_eq_bot.mp hkerw1
  have hinjw2 : Function.Injective (α - ζ ^ 2 • (1 : V →ₗ[ZMod r] V)) :=
    LinearMap.ker_eq_bot.mp hkerw2
  have hprod := end_pow_three_sub_one α hα3 hζ3 hζsum
  let b : V := (α - ζ ^ 2 • (1 : V →ₗ[ZMod r] V)) a
  let u : V := (α - ζ • (1 : V →ₗ[ZMod r] V)) b
  have hb : b ≠ (0 : V) := fun hb0 => ha (hinjw2 (by simpa [b] using hb0))
  have hu : u ≠ (0 : V) := fun hu0 => hb (hinjw1 (by simpa [u] using hu0))
  have hzu : (α - (1 : V →ₗ[ZMod r] V)) u = (0 : V) := by
    have h := congrArg (fun f : V →ₗ[ZMod r] V => f a) hprod
    simpa [u, b] using h
  have hzu0 : u = (0 : V) := by
    apply hinj1
    simpa using hzu
  exact hu hzu0

private lemma exists_ne_zero_quotient {N M : Subgroup G} [(N.subgroupOf M).Normal]
    (hNM : N < M) :
    ∃ a : Additive (M ⧸ N.subgroupOf M), a ≠ (0 : Additive (M ⧸ N.subgroupOf M)) := by
  obtain ⟨m₀, hm₀M, hm₀N⟩ := Set.exists_of_ssubset hNM
  refine ⟨Additive.ofMul (QuotientGroup.mk (⟨m₀, hm₀M⟩ : M)), ?_⟩
  intro h
  have h' : Additive.ofMul (QuotientGroup.mk (⟨m₀, hm₀M⟩ : M)) =
      (0 : Additive (M ⧸ N.subgroupOf M)) := h
  have h1 : QuotientGroup.mk (⟨m₀, hm₀M⟩ : M) = 1 :=
    (ofMul_eq_zero (x := QuotientGroup.mk (⟨m₀, hm₀M⟩ : M))).mp h'
  exact hm₀N (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff (N := N.subgroupOf M) _).mp h1))

private lemma false_of_all_scalarK_eq {G : Type*} [Group G] {r : ℕ} [Fact r.Prime]
    {Y N M : Subgroup G} [(N.subgroupOf M).Normal]
    [IsMulCommutative (M ⧸ N.subgroupOf M)]
    (hchief : CFSG.ABGLocalTools.IsChiefFactorUnder r Y M N) {c : G}
    (hc3 : c ^ 3 = 1) (hcM : c ∈ Subgroup.normalizer (M : Set G))
    (hcN : c ∈ Subgroup.normalizer (N : Set G)) {ζ : ZMod r} (hζ3 : ζ ^ 3 = 1)
    (hζsum : 1 + ζ + ζ ^ 2 = 0)
    (h1N : chiefScalarSubgroup N M c 1 hcM = N)
    (hw1N : chiefScalarSubgroup N M c ζ.val hcM = N)
    (hw2N : chiefScalarSubgroup N M c (ζ ^ 2).val hcM = N) : False := by
  classical
  haveI hEA : IsElementaryAbelian r (M ⧸ N.subgroupOf M) := hchief.isElementaryAbelian
  let Q := M ⧸ N.subgroupOf M
  let V := Additive Q
  have hMnorm : Subgroup.zpowers c ≤ Subgroup.normalizer (M : Set G) :=
    Subgroup.zpowers_le.mpr hcM
  have hNnormz : Subgroup.zpowers c ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr hcN
  let cz : Subgroup.zpowers c := ⟨c, Subgroup.mem_zpowers c⟩
  let α : V →ₗ[ZMod r] V := (CFSG.ABGLocalTools.chiefRep (p := r) hMnorm hNnormz cz).val
  have hcz3 : cz ^ 3 = 1 := by
    apply Subtype.ext
    simpa [cz] using hc3
  have hα3 : α ^ 3 = 1 := by
    have h1 : (CFSG.ABGLocalTools.chiefRep (p := r) hMnorm hNnormz cz) ^ 3 = 1 := by
      rw [← map_pow, hcz3, map_one]
    have h2 := congrArg (fun u : LinearMap.GeneralLinearGroup (ZMod r) V =>
      (u : V →ₗ[ZMod r] V)) h1
    simpa [α] using h2
  have hαq : ∀ x : M, α (Additive.ofMul (QuotientGroup.mk x)) =
      Additive.ofMul (QuotientGroup.mk (conjMem M hcM x)) := by
    intro x
    dsimp only [α]
    rw [CFSG.ABGLocalTools.chiefRep_apply_mk]
    congr 1
  have hker1 : LinearMap.ker (α - (1 : V →ₗ[ZMod r] V)) = ⊥ := by
    have h := ker_scalar_eq_bot (r := r) hcM h1N α hαq
    simpa using h
  have hkerw1 : LinearMap.ker (α - ζ • (1 : V →ₗ[ZMod r] V)) = ⊥ := by
    have h := ker_scalar_eq_bot (r := r) hcM hw1N α hαq
    rwa [ZMod.natCast_zmod_val] at h
  have hkerw2 : LinearMap.ker (α - ζ ^ 2 • (1 : V →ₗ[ZMod r] V)) = ⊥ := by
    have h := ker_scalar_eq_bot (r := r) hcM hw2N α hαq
    rwa [ZMod.natCast_zmod_val] at h
  obtain ⟨a, ha⟩ := exists_ne_zero_quotient hchief.1
  exact false_of_three_kernels α hα3 hζ3 hζsum hker1 hkerw1 hkerw2 ha

theorem exists_pow_of_isChiefFactorUnder {G : Type*} [Group G] {r : ℕ}
    [Fact r.Prime] (hr : r % 3 = 1) {Y N M : Subgroup G}
    (hchief : CFSG.ABGLocalTools.IsChiefFactorUnder r Y M N) {c : G} (hc3 : c ^ 3 = 1)
    (hcY : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hcM : c ∈ Subgroup.normalizer (M : Set G)) (hcN : c ∈ Subgroup.normalizer (N : Set G)) :
    ∃ w : ℕ, ∀ m ∈ M, c * m * c⁻¹ * (m ^ w)⁻¹ ∈ N := by
  classical
  have hNM : N ≤ M := hchief.1.le
  haveI hNnorm : (N.subgroupOf M).Normal := hchief.normal
  haveI hQcomm : IsMulCommutative (M ⧸ N.subgroupOf M) := by
    refine Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr ?_
    change ⁅(⊤ : Subgroup ↥M), ⊤⁆ ≤ N.subgroupOf M
    rw [Subgroup.commutator_le]
    intro x _ y _
    have h := hchief.2.2.2.2.1 (x : G) x.2 (y : G) y.2
    rw [Subgroup.mem_subgroupOf]
    change ⁅(x : G), (y : G)⁆ ∈ N
    exact h
  obtain ⟨ζ, hζ3, _, hζsum⟩ := exists_cube_root_of_mod_three hr
  let K : ℕ → Subgroup G := fun w => chiefScalarSubgroup N M c w hcM
  have hKmem : ∀ (w : ℕ) (m : M), (m : G) ∈ K w ↔
      c * (m : G) * c⁻¹ * ((m : G) ^ w)⁻¹ ∈ N := fun w m =>
    mem_chiefScalarSubgroup N M c w hcM m
  have hNK : ∀ w, N ≤ K w := by
    intro w n hn
    have hnM : n ∈ M := hNM hn
    refine (hKmem w ⟨n, hnM⟩).mpr ?_
    have h1 : c * n * c⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hcN n).mp hn
    have h2 : (n ^ w)⁻¹ ∈ N := N.inv_mem (N.pow_mem hn w)
    simpa using N.mul_mem h1 h2
  have hKM : ∀ w, K w ≤ M := fun w => Subgroup.map_subtype_le _
  have hYK : ∀ w, Y ≤ Subgroup.normalizer (K w : Set G) := fun w =>
    le_normalizer_chiefScalarSubgroup hchief.2.1 hchief.2.2.1 hcM hcY
  have hKcase : ∀ w, K w = N ∨ K w = M := fun w =>
    hchief.2.2.2.2.2.2 (K w) (hNK w) (hKM w) (hYK w)
  have hOfEq : ∀ w, K w = M → ∃ w' : ℕ, ∀ m ∈ M, c * m * c⁻¹ * (m ^ w')⁻¹ ∈ N := by
    intro w hw
    refine ⟨w, fun m hm => ?_⟩
    exact (hKmem w ⟨m, hm⟩).mp (by rw [hw]; exact hm)
  by_cases h1M : K 1 = M
  · exact hOfEq 1 h1M
  by_cases hw1M : K ζ.val = M
  · exact hOfEq ζ.val hw1M
  by_cases hw2M : K (ζ ^ 2).val = M
  · exact hOfEq (ζ ^ 2).val hw2M
  have h1N : K 1 = N := (hKcase 1).resolve_right h1M
  have hw1N : K ζ.val = N := (hKcase ζ.val).resolve_right hw1M
  have hw2N : K (ζ ^ 2).val = N := (hKcase (ζ ^ 2).val).resolve_right hw2M
  exact False.elim (false_of_all_scalarK_eq hchief hc3 hcM hcN hζ3 hζsum h1N hw1N hw2N)

end CFSG.GroupTheory

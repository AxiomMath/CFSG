module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
import CFSG.FeitThompson.Local.PrimeCubeTorsionCentralizerCyclic
import CFSG.FeitThompson.Local.NormalPlaneElementCentralizerIndex
import CFSG.FeitThompson.Local.PrimeCubeOddScalarObstruction

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open scoped commutatorElement Pointwise

variable {p : ℕ} {R : Type*} [Group R]

theorem eq_bot_of_commutator_top_eq [Group.IsNilpotent R] {M : Subgroup R}
    (hM : ⁅(⊤ : Subgroup R), M⁆ = M) : M = ⊥ := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent R›
  have key : ∀ k, M ≤ (⊤ : Subgroup R).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        calc M = ⁅M, (⊤ : Subgroup R)⁆ := by rw [← Subgroup.commutator_comm]; exact hM.symm
          _ ≤ ⁅(⊤ : Subgroup R).lowerCentralSeries k, ⊤⁆ := Subgroup.commutator_mono ih le_rfl
  exact le_bot_iff.mp (hn ▸ key n)

theorem card_commutator_top_lt [Finite R] [Group.IsNilpotent R] {M : Subgroup R} [M.Normal]
    (hM : M ≠ ⊥) : Nat.card ↥⁅(⊤ : Subgroup R), M⁆ < Nat.card ↥M :=
  lt_of_not_ge fun h => hM (eq_bot_of_commutator_top_eq
    (Subgroup.eq_of_le_of_card_ge (Subgroup.commutator_le_right _ _) h))

theorem le_center_of_card_dvd_prime [Finite R] [Group.IsNilpotent R] {M : Subgroup R} [M.Normal]
    (hp : p.Prime) (hM : Nat.card ↥M ∣ p) : M ≤ center R := by
  have hbot : ⁅(⊤ : Subgroup R), M⁆ = ⊥ := by
    rcases eq_or_ne M ⊥ with h | h
    · simp [h]
    · have hlt := card_commutator_top_lt (M := M) h
      have hdvd : Nat.card ↥⁅(⊤ : Subgroup R), M⁆ ∣ p :=
        (Subgroup.card_dvd_of_le (Subgroup.commutator_le_right _ _)).trans hM
      have hMp : Nat.card ↥M ≤ p := Nat.le_of_dvd hp.pos hM
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact Subgroup.card_eq_one.mp h1
      · omega
  exact Subgroup.centralizer_eq_top_iff_subset.mp
    (top_le_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot))

def commutatorHom {Z : Subgroup R} (hZc : Z ≤ center R) {t : R}
    (ht : ∀ r : R, ⁅r, t⁆ ∈ Z) : R →* R :=
  MonoidHom.mk' (fun r => ⁅r, t⁆) fun r s =>
    commutatorElement_mul_left_of_mem_center (hZc (ht r)) (hZc (ht s))

@[simp]
theorem commutatorHom_apply {Z : Subgroup R} (hZc : Z ≤ center R) {t : R}
    (ht : ∀ r : R, ⁅r, t⁆ ∈ Z) (r : R) : commutatorHom hZc ht r = ⁅r, t⁆ := (rfl)

theorem ker_commutatorHom {Z : Subgroup R} (hZc : Z ≤ center R) {t : R}
    (ht : ∀ r : R, ⁅r, t⁆ ∈ Z) : (commutatorHom hZc ht).ker = centralizer {t} := by
  ext r
  rw [MonoidHom.mem_ker, commutatorHom_apply, commutatorElement_eq_one_iff_commute,
    mem_centralizer_singleton_iff]
  exact Iff.rfl

theorem index_centralizer_singleton_dvd {Z : Subgroup R} (hZc : Z ≤ center R) {t : R}
    (ht : ∀ r : R, ⁅r, t⁆ ∈ Z) : (centralizer {t}).index ∣ Nat.card Z := by
  rw [← ker_commutatorHom hZc ht, Subgroup.index_ker]
  exact Subgroup.card_dvd_of_le (by rintro _ ⟨r, rfl⟩; exact ht r)

theorem zpowers_sup_eq_of_card_eq_prime_sq [Finite R] (hp : p.Prime) {T Z : Subgroup R}
    (hT : Nat.card T = p ^ 2) (hZT : Z ≤ T) (hZ : Nat.card Z = p) {t : R} (htT : t ∈ T)
    (htZ : t ∉ Z) : zpowers t ⊔ Z = T := by
  set S : Subgroup R := zpowers t ⊔ Z with hS
  have hST : S ≤ T := sup_le (zpowers_le.mpr htT) hZT
  have hZS : Z ≤ S := le_sup_right
  have hne : Z ≠ S := fun h => htZ (h ▸ (le_sup_left : zpowers t ≤ S) (Subgroup.mem_zpowers t))
  obtain ⟨j, hj2, hjc⟩ := (Nat.dvd_prime_pow hp).mp (hT ▸ Subgroup.card_dvd_of_le hST)
  have h1j : 1 ≤ j := by
    have hd : p ^ 1 ∣ p ^ j := by rw [pow_one, ← hjc]; exact hZ ▸ Subgroup.card_dvd_of_le hZS
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd
  have hj1 : j ≠ 1 := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge hZS (by rw [hjc, h, pow_one, hZ]))
  have hj : j = 2 := by omega
  exact Subgroup.eq_of_le_of_card_ge hST (by rw [hT, hjc, hj])

theorem centralizer_eq_centralizer_singleton {T Z : Subgroup R} (hZc : Z ≤ center R) {t : R}
    (hTt : zpowers t ⊔ Z = T) : centralizer (T : Set R) = centralizer {t} := by
  have htT : t ∈ T := hTt ▸ (le_sup_left : zpowers t ≤ _) (Subgroup.mem_zpowers t)
  refine le_antisymm (centralizer_le (by simpa using htT)) ?_
  have hcl : Subgroup.closure ({t} ∪ (Z : Set R)) = T := by
    rw [Subgroup.closure_union, ← zpowers_eq_closure, Subgroup.closure_eq, hTt]
  rw [← hcl, Subgroup.centralizer_closure]
  refine fun r hr => mem_centralizer_iff.mpr ?_
  rintro g (hg | hg)
  · rw [Set.mem_singleton_iff] at hg
    exact hg ▸ (mem_centralizer_singleton_iff.mp hr).symm
  · exact (Subgroup.mem_center_iff.mp (hZc hg) r).symm

theorem map_subgroupOf_subtype {B : Subgroup R} (X : Subgroup R) :
    (X.subgroupOf B).map B.subtype = B ⊓ X := by
  rw [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.subtype_range]

theorem card_subgroupOf {B T : Subgroup R} (hTB : T ≤ B) :
    Nat.card ↥(T.subgroupOf B) = Nat.card T :=
  Nat.card_congr (subgroupOfEquivOfLe hTB).toEquiv

theorem inf_center_omega1_le_map_center (p : ℕ) (R : Type*) [Group R] :
    center R ⊓ omega1 p R ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype := by
  rw [← inf_centralizer_omega1_eq_map_center]
  exact le_inf inf_le_right (inf_le_left.trans (center_le_centralizer _))

theorem map_center_omega1_eq_commutator (hp : p.Prime)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R)) :
    (center ↥(omega1 p R)).map (omega1 p R).subtype = ⁅omega1 p R, omega1 p R⁆ := by
  rw [← commutator_eq_center_of_card_eq_prime_cube hp hB hnab, commutator_def, map_commutator,
    ← MonoidHom.range_eq_map, Subgroup.subtype_range]

theorem map_center_le_commutator_top_omega1 (hp : p.Prime)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R)) :
    (center ↥(omega1 p R)).map (omega1 p R).subtype ≤ ⁅(⊤ : Subgroup R), omega1 p R⁆ := by
  rw [map_center_omega1_eq_commutator hp hB hnab]
  exact Subgroup.commutator_mono le_top le_rfl

theorem map_center_omega1_le_center [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R)) :
    (center ↥(omega1 p R)).map (omega1 p R).subtype ≤ center R := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  rw [map_center_omega1_eq_commutator hp hB hnab]
  refine le_center_of_card_dvd_prime hp ?_
  rw [← map_center_omega1_eq_commutator hp hB hnab, card_map_center_omega1 hp hB hnab]

instance commutator_top_omega1_characteristic :
    (⁅(⊤ : Subgroup R), omega1 p R⁆).Characteristic :=
  Subgroup.commutator_characteristic _ _

theorem card_commutator_top_omega1 [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    Nat.card ↥⁅(⊤ : Subgroup R), omega1 p R⁆ = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  have hTB : ⁅(⊤ : Subgroup R), omega1 p R⁆ ≤ omega1 p R := Subgroup.commutator_le_right _ _
  have hZT := map_center_le_commutator_top_omega1 hp hB hnab
  have hZcard : Nat.card ↥((center ↥(omega1 p R)).map (omega1 p R).subtype) = p :=
    card_map_center_omega1 hp hB hnab
  have hdvdZ : p ∣ Nat.card ↥⁅(⊤ : Subgroup R), omega1 p R⁆ := by
    have h := Subgroup.card_dvd_of_le hZT; rwa [hZcard] at h
  have hdvd3 : Nat.card ↥⁅(⊤ : Subgroup R), omega1 p R⁆ ∣ p ^ 3 := by
    have h := Subgroup.card_dvd_of_le hTB; rwa [hB] at h
  obtain ⟨k, hk3, hkc⟩ := (Nat.dvd_prime_pow hp).mp hdvd3
  have h1k : 1 ≤ k := by
    have hd : p ^ 1 ∣ p ^ k := by rw [pow_one, ← hkc]; exact hdvdZ
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hd
  have hk1 : k ≠ 1 := fun h =>
    hZ (le_of_eq (Subgroup.eq_of_le_of_card_ge hZT (by rw [hkc, h, pow_one, hZcard])).symm)
  have hkne3 : k ≠ 3 := by
    intro h
    have hTeq : ⁅(⊤ : Subgroup R), omega1 p R⁆ = omega1 p R :=
      Subgroup.eq_of_le_of_card_ge hTB (by rw [hkc, h, hB])
    have hbot := eq_bot_of_commutator_top_eq hTeq
    rw [hbot] at hnab
    exact hnab inferInstance
  have hk2 : k = 2 := by omega
  rw [hkc, hk2]

theorem nonempty_mulEquiv_commutator_top_omega1 [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hexp : ∀ b ∈ omega1 p R, b ^ p = 1)
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    Nonempty (↥⁅(⊤ : Subgroup R), omega1 p R⁆ ≃* (Fin 2 → Multiplicative (ZMod p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hTcard : Nat.card ↥⁅(⊤ : Subgroup R), omega1 p R⁆ = p ^ 2 :=
    card_commutator_top_omega1 hp hR hB hnab hZ
  have hcomm : IsMulCommutative ↥⁅(⊤ : Subgroup R), omega1 p R⁆ :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hTcard
  let _ : CommGroup ↥⁅(⊤ : Subgroup R), omega1 p R⁆ := IsMulCommutative.instCommGroup
  refine nonempty_mulEquiv_pi_of_exponent hp (fun x => Subtype.ext ?_) hTcard
  simpa using hexp _ (Subgroup.commutator_le_right _ _ x.2)

theorem two_mem_elementaryAbelianRanks_commutator_top_omega1 [Finite R] (hp : p.Prime)
    (hR : IsPGroup p R) (hB : Nat.card ↥(omega1 p R) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(omega1 p R)) (hexp : ∀ b ∈ omega1 p R, b ^ p = 1)
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    2 ∈ elementaryAbelianRanks p ↥⁅(⊤ : Subgroup R), omega1 p R⁆ :=
  mem_elementaryAbelianRanks.mpr
    ⟨⊤, ⟨(topEquiv (G := ↥⁅(⊤ : Subgroup R), omega1 p R⁆)).trans
      (nonempty_mulEquiv_commutator_top_omega1 hp hR hB hnab hexp hZ).some⟩⟩

theorem commutator_top_commutator_top_omega1_le [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    ⁅(⊤ : Subgroup R), ⁅(⊤ : Subgroup R), omega1 p R⁆⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent R := hR.isNilpotent
  set T : Subgroup R := ⁅(⊤ : Subgroup R), omega1 p R⁆ with hTdef
  have hTcard : Nat.card T = p ^ 2 := card_commutator_top_omega1 hp hR hB hnab hZ
  have hTne : T ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hTcard
    exact absurd hTcard.symm (by simpa using hp.one_lt.ne')
  have hlt : Nat.card ↥⁅(⊤ : Subgroup R), T⁆ < Nat.card T := card_commutator_top_lt hTne
  have hdvd : Nat.card ↥⁅(⊤ : Subgroup R), T⁆ ∣ p ^ 2 := by
    have h := Subgroup.card_dvd_of_le (Subgroup.commutator_le_right (⊤ : Subgroup R) T)
    rwa [hTcard] at h
  obtain ⟨j, hj2, hjc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have hj : j = 2 := by omega
    rw [hjc, hj, ← hTcard] at hlt
    omega
  have hdvdp : Nat.card ↥⁅(⊤ : Subgroup R), T⁆ ∣ p := by
    rw [hjc]; interval_cases j <;> simp
  refine le_trans (le_inf (le_center_of_card_dvd_prime hp hdvdp) ?_)
    (inf_center_omega1_le_map_center p R)
  exact le_trans (Subgroup.commutator_le_right _ _) (Subgroup.commutator_le_right _ _)

theorem inf_centralizer_commutator_top_omega1 [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    omega1 p R ⊓ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R)
      = ⁅(⊤ : Subgroup R), omega1 p R⁆ := by
  set T : Subgroup R := ⁅(⊤ : Subgroup R), omega1 p R⁆ with hTdef
  have hTB : T ≤ omega1 p R := Subgroup.commutator_le_right _ _
  have hTcard : Nat.card T = p ^ 2 := card_commutator_top_omega1 hp hR hB hnab hZ
  have h := centralizer_eq_self_of_card_eq_prime_sq (T := T.subgroupOf (omega1 p R)) hp hB hnab
    (by rw [card_subgroupOf hTB, hTcard])
  rw [centralizer_subgroupOf hTB] at h
  have h2 := congrArg (fun X : Subgroup ↥(omega1 p R) => X.map (omega1 p R).subtype) h
  simpa only [map_subgroupOf_subtype, inf_left_idem, inf_eq_right.mpr hTB] using h2

theorem centralizer_omega1_le_centralizer_commutator (p : ℕ) (R : Type*) [Group R] :
    centralizer (omega1 p R : Set R)
      ≤ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) :=
  centralizer_le (by exact_mod_cast Subgroup.commutator_le_right (⊤ : Subgroup R) (omega1 p R))

theorem index_centralizer_commutator_top_omega1 [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    (centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R)).index = p := by
  have : Fact p.Prime := ⟨hp⟩
  set Z : Subgroup R := (center ↥(omega1 p R)).map (omega1 p R).subtype with hZdef
  set T : Subgroup R := ⁅(⊤ : Subgroup R), omega1 p R⁆ with hTdef
  have hZcard : Nat.card Z = p := card_map_center_omega1 hp hB hnab
  have hZc : Z ≤ center R := map_center_omega1_le_center hp hR hB hnab
  have hZT : Z ≤ T := map_center_le_commutator_top_omega1 hp hB hnab
  have hTcard : Nat.card T = p ^ 2 := card_commutator_top_omega1 hp hR hB hnab hZ
  obtain ⟨t, htT, htZ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hZT fun h => hZ (h ▸ le_rfl))
  have hTt : zpowers t ⊔ Z = T := zpowers_sup_eq_of_card_eq_prime_sq hp hTcard hZT hZcard htT htZ
  have hcomm : ∀ r : R, ⁅r, t⁆ ∈ Z := fun r =>
    commutator_top_commutator_top_omega1_le hp hR hB hnab hZ
      (Subgroup.commutator_mem_commutator (mem_top r) htT)
  have hdvd : (centralizer (T : Set R)).index ∣ p := by
    rw [centralizer_eq_centralizer_singleton hZc hTt, ← hZcard]
    exact index_centralizer_singleton_dvd hZc hcomm
  rcases (Nat.dvd_prime hp).mp hdvd with h | h
  · exact absurd (le_trans (le_inf (Subgroup.centralizer_eq_top_iff_subset.mp
      (Subgroup.index_eq_one.mp h)) (Subgroup.commutator_le_right _ _))
      (inf_center_omega1_le_map_center p R)) hZ
  · exact h

theorem sup_centralizer_commutator_top_omega1 [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    omega1 p R ⊔ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) = ⊤ := by
  set T : Subgroup R := ⁅(⊤ : Subgroup R), omega1 p R⁆ with hTdef
  set D : Subgroup R := centralizer (T : Set R) with hDdef
  have hDindex : D.index = p := index_centralizer_commutator_top_omega1 hp hR hB hnab hZ
  have hTcard : Nat.card T = p ^ 2 := card_commutator_top_omega1 hp hR hB hnab hZ
  have hBD : ¬ omega1 p R ≤ D := by
    intro hle
    have h := inf_centralizer_commutator_top_omega1 hp hR hB hnab hZ
    rw [inf_eq_left.mpr hle] at h
    rw [h, hTcard] at hB
    exact absurd (Nat.pow_right_injective hp.two_le hB) (by omega)
  have h1 : D.relIndex (omega1 p R ⊔ D) * (omega1 p R ⊔ D).index = D.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have h2 : D.relIndex (omega1 p R ⊔ D) ≠ 1 := fun hh =>
    hBD (le_trans le_sup_left (Subgroup.relIndex_eq_one.mp hh))
  rw [hDindex] at h1
  rcases (Nat.dvd_prime hp).mp ⟨_, h1.symm⟩ with h | h
  · exact absurd h h2
  · rw [h] at h1
    exact Subgroup.index_eq_one.mp (Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h1, mul_one]))

theorem mul_centralizer_commutator_eq_univ [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    (omega1 p R : Set R)
        * (centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) : Set R)
      = Set.univ := by
  rw [← Subgroup.mul_normal, sup_centralizer_commutator_top_omega1 hp hR hB hnab hZ]
  simp

theorem prime_cube_noncentral_plane [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hexp : ∀ b ∈ omega1 p R, b ^ p = 1)
    (hZ : ¬ ⁅(⊤ : Subgroup R), omega1 p R⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    (⁅(⊤ : Subgroup R), omega1 p R⁆).Characteristic ∧
      Nat.card ↥⁅(⊤ : Subgroup R), omega1 p R⁆ = p ^ 2 ∧
      Nonempty (↥⁅(⊤ : Subgroup R), omega1 p R⁆ ≃* (Fin 2 → Multiplicative (ZMod p))) ∧
      (center ↥(omega1 p R)).map (omega1 p R).subtype ≤ ⁅(⊤ : Subgroup R), omega1 p R⁆ ∧
      ⁅(⊤ : Subgroup R), ⁅(⊤ : Subgroup R), omega1 p R⁆⁆
        ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype ∧
      (centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R)).index = p ∧
      omega1 p R ⊓ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R)
        = ⁅(⊤ : Subgroup R), omega1 p R⁆ ∧
      centralizer (omega1 p R : Set R)
        ≤ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) ∧
      omega1 p R ⊔ centralizer ((⁅(⊤ : Subgroup R), omega1 p R⁆ : Subgroup R) : Set R) = ⊤ :=
  ⟨commutator_top_omega1_characteristic, card_commutator_top_omega1 hp hR hB hnab hZ,
    nonempty_mulEquiv_commutator_top_omega1 hp hR hB hnab hexp hZ,
    map_center_le_commutator_top_omega1 hp hB hnab,
    commutator_top_commutator_top_omega1_le hp hR hB hnab hZ,
    index_centralizer_commutator_top_omega1 hp hR hB hnab hZ,
    inf_centralizer_commutator_top_omega1 hp hR hB hnab hZ,
    centralizer_omega1_le_centralizer_commutator p R,
    sup_centralizer_commutator_top_omega1 hp hR hB hnab hZ⟩

end

end CFSG.FeitThompson

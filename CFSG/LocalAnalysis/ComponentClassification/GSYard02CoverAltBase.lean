
module

public import CFSG.Alternating.Multipliers.Main
public import CFSG.RankThree.PerfectCover.HopfCentralCovers
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.LocalAnalysis.ComponentClassification.GSYard02Basic
public import Certificates.Data.CFSGNative.GSYard02Spin
public import CFSG.Sporadic.Schreier.J4SSylowBase

@[expose] public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02.CoverAltGroup

def treeAux {G : Type*} [Mul G] [One G] (gs : List G) : List G → List (ℕ × ℕ) → List G
  | acc, [] => acc
  | acc, (p, g) :: tr => treeAux gs (acc ++ [gs.getD g 1 * acc.getD p 1]) tr

def treeTab {G : Type*} [Mul G] [One G] (gs : List G) (tr : List (ℕ × ℕ)) : List G :=
  treeAux gs [1] tr

private theorem getD_mem_of {α : Type*} [One α] {P : α → Prop} (h1 : P 1) :
    ∀ (l : List α) (n : ℕ), (∀ y ∈ l, P y) → P (l.getD n 1)
  | [], _, _ => h1
  | x :: _, 0, h => by
    rw [List.getD_cons_zero]
    exact h x (List.mem_cons.mpr (Or.inl rfl))
  | _ :: xs, n + 1, h => by
    rw [List.getD_cons_succ]
    exact getD_mem_of h1 xs n fun y hy => h y (List.mem_cons.mpr (Or.inr hy))

private theorem treeAux_mem_of_mem {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ)) :
    ∀ (acc : List G) (y : G), y ∈ acc → y ∈ treeAux gs acc tr := by
  induction tr with
  | nil => intro acc y hy; exact hy
  | cons pg tr ih =>
    intro acc y hy
    obtain ⟨p, g⟩ := pg
    show y ∈ treeAux gs (acc ++ [gs.getD g 1 * acc.getD p 1]) tr
    exact ih _ y (List.mem_append.mpr (Or.inl hy))

private theorem treeAux_mem_closure {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ)) :
    ∀ (acc : List G), (∀ y ∈ acc, y ∈ Subgroup.closure {g | g ∈ gs}) →
      ∀ y ∈ treeAux gs acc tr, y ∈ Subgroup.closure {g | g ∈ gs} := by
  induction tr with
  | nil => intro acc h y hy; exact h y hy
  | cons pg tr ih =>
    intro acc h
    obtain ⟨p, g⟩ := pg
    show ∀ y ∈ treeAux gs (acc ++ [gs.getD g 1 * acc.getD p 1]) tr,
      y ∈ Subgroup.closure {g | g ∈ gs}
    apply ih
    intro y hy
    rcases List.mem_append.mp hy with hy' | hy'
    · exact h y hy'
    · rw [List.mem_singleton.mp hy']
      have hgen : ∀ z ∈ gs, z ∈ Subgroup.closure {g | g ∈ gs} := fun z hz =>
        Subgroup.subset_closure (show z ∈ {g | g ∈ gs} from hz)
      exact mul_mem
        (getD_mem_of (P := fun z => z ∈ Subgroup.closure {g | g ∈ gs}) (one_mem _) gs g hgen)
        (getD_mem_of (P := fun z => z ∈ Subgroup.closure {g | g ∈ gs}) (one_mem _) acc p h)

private theorem one_mem_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ)) :
    (1 : G) ∈ treeTab gs tr :=
  treeAux_mem_of_mem gs tr [1] 1 (List.mem_singleton.mpr rfl)

private theorem closure_le_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ))
    (hinv : ∀ g ∈ gs, g⁻¹ ∈ gs)
    (hcl : ∀ x ∈ treeTab gs tr, ∀ g ∈ gs, g * x ∈ treeTab gs tr) (x : G)
    (hx : x ∈ Subgroup.closure {g | g ∈ gs}) : x ∈ treeTab gs tr := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact one_mem_treeTab gs tr
  | mul_left g hg y _ ih => exact hcl y ih g hg
  | inv_mul_cancel g hg y _ ih => exact hcl y ih g⁻¹ (hinv g hg)

theorem mem_closure_iff_mem_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ))
    (hinv : ∀ g ∈ gs, g⁻¹ ∈ gs) (hnd : (treeTab gs tr).Nodup)
    (hcl : ∀ x ∈ treeTab gs tr, ∀ g ∈ gs, g * x ∈ treeTab gs tr) (x : G) :
    x ∈ Subgroup.closure {g | g ∈ gs} ↔ x ∈ treeTab gs tr :=
  ⟨closure_le_treeTab gs tr hinv hcl x, fun hx =>
    treeAux_mem_closure gs tr [1] (fun y hy => by
      rw [List.mem_singleton.mp hy]
      exact one_mem _) x hx⟩

theorem card_closure_eq_length_treeTab {G : Type*} [Group G] (gs : List G) (tr : List (ℕ × ℕ))
    (hinv : ∀ g ∈ gs, g⁻¹ ∈ gs) (hnd : (treeTab gs tr).Nodup)
    (hcl : ∀ x ∈ treeTab gs tr, ∀ g ∈ gs, g * x ∈ treeTab gs tr) :
    Nat.card (Subgroup.closure {g | g ∈ gs}) = (treeTab gs tr).length := by
  classical
  have hset : ((Subgroup.closure {g | g ∈ gs} : Subgroup G) : Set G) =
      ↑(treeTab gs tr).toFinset := by
    ext y
    simp only [SetLike.mem_coe, List.coe_toFinset, Set.mem_setOf_eq]
    exact mem_closure_iff_mem_treeTab gs tr hinv hnd hcl y
  have h1 : Nat.card (Subgroup.closure {g | g ∈ gs}) =
      ((Subgroup.closure {g | g ∈ gs} : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

private def pairTree : List (ℕ × ℕ) := [(0, 0), (0, 1), (2, 0)]

theorem isKleinFour_closure_pair {G : Type*} [Group G] {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    IsKleinFour (Subgroup.closure {a, b}) ∧ Nat.card (Subgroup.closure {a, b}) = 4 := by
  have hA : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hB : b * (a * b) = a := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]
  have hba : b * a = a * b := hab.symm
  have hab1 : a * b ≠ 1 := fun h => hne (mul_left_cancel (h.trans ha.symm)).symm
  have h1a : (1 : G) ≠ a := fun h => ha1 h.symm
  have h1b : (1 : G) ≠ b := fun h => hb1 h.symm
  have h1ab : (1 : G) ≠ a * b := fun h => hab1 h.symm
  have haab : a ≠ a * b := fun h => hb1 (mul_left_cancel ((mul_one a).trans h)).symm
  have hbab : b ≠ a * b := fun h => ha1 (mul_right_cancel ((one_mul b).trans h)).symm
  have hinv : ∀ g ∈ [a, b], g⁻¹ ∈ [a, b] := by
    intro g hg
    rcases List.mem_cons.mp hg with h | h
    · rw [h, inv_eq_of_mul_eq_one_right ha]
      simp
    · rw [List.mem_singleton.mp h, inv_eq_of_mul_eq_one_right hb]
      simp
  have hL : treeTab [a, b] pairTree = [1, a, b, a * b] := by
    simp [pairTree, treeTab, treeAux]
  have hnd : (treeTab [a, b] pairTree).Nodup := by
    rw [hL]
    simp [h1a, h1b, h1ab, ha1, hb1, hne, hne.symm, hab1, haab, hbab]
  have hcl : ∀ x ∈ treeTab [a, b] pairTree, ∀ g ∈ [a, b],
      g * x ∈ treeTab [a, b] pairTree := by
    rw [hL]
    intro x hx g hg
    simp at hx hg
    rcases hx with h | h | h | h <;> rcases hg with h' | h' <;> rw [h, h'] <;>
      simp [hA, hB, hba, ha, hb]
  have hset : ({g | g ∈ [a, b]} : Set G) = {a, b} := by
    ext g
    simp
  have hcardT := card_closure_eq_length_treeTab [a, b] pairTree hinv hnd hcl
  rw [hset, hL] at hcardT
  have h4 : Nat.card (Subgroup.closure ({a, b} : Set G)) = 4 := hcardT.trans (by simp)
  have hmem : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    intro x hx
    rw [← hset] at hx
    have hx' := (mem_closure_iff_mem_treeTab [a, b] pairTree hinv hnd hcl x).mp hx
    rw [hL] at hx'
    simpa using hx'
  have h2 : ∀ x ∈ Subgroup.closure ({a, b} : Set G), x ^ 2 = 1 := by
    intro x hx
    rcases hmem x hx with h | h | h | h
    · rw [h]
      exact one_pow 2
    · rw [h, sq]
      exact ha
    · rw [h, sq]
      exact hb
    · rw [h, sq, mul_assoc, hB]
      exact ha
  exact ⟨FooteLit.isKleinFour_of_card_eq_four h4 h2, h4⟩

theorem exists_pair_of_isKleinFour {G : Type*} [Group G] (Y : Subgroup G) (hY : IsKleinFour Y) :
    ∃ a b : G, a ∈ Y ∧ b ∈ Y ∧ a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      Y = Subgroup.closure {a, b} := by
  have hY2 : ∀ x ∈ Y, x ^ 2 = 1 := fun x hx => FooteLit.sq_eq_one_of_isKleinFour hY hx
  have hsq : ∀ x ∈ Y, x * x = 1 := fun x hx => by
    have h := hY2 x hx
    rwa [sq] at h
  have hcomm : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
    FooteLit.commute_of_sq_eq_one hY2 hx hy
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hY.card_four]; norm_num)
  have hYcard : (Y : Set G).ncard = 4 :=
    (Nat.card_coe_set_eq (Y : Set G)).symm.trans hY.card_four
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ Y, a ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Y : Set G) ⊆ ({1} : Set G) := fun x hx =>
      Set.mem_singleton_iff.mpr (hcon x hx)
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_singleton, hYcard] at h1
    omega
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ Y, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push_neg at hcon
    have hsub : (Y : Set G) ⊆ ({1, a} : Set G) := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [Set.mem_insert_iff]
        exact Or.inl hx1
      · rw [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inr (hcon x hx hx1)
    have h1 := Set.ncard_le_ncard hsub
    rw [Set.ncard_pair (show (1 : G) ≠ a from fun h => ha1 h.symm), hYcard] at h1
    omega
  have hbb : b * b = 1 := hsq b hb
  have hab : a * b = b * a := hcomm a ha b hb
  have hne : a ≠ b := fun h => hba h.symm
  have hcl := (isKleinFour_closure_pair (hsq a ha) hbb hab ha1 hb1 hne).2
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Y := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · rw [h]
      exact ha
    · rw [Set.mem_singleton_iff.mp h]
      exact hb
  have hEq : Subgroup.closure ({a, b} : Set G) = Y :=
    Subgroup.eq_of_le_of_card_ge hle (hY.card_four.trans hcl.symm).le
  exact ⟨a, b, ha, hb, hsq a ha, hbb, hab, ha1, hb1, hne, hEq.symm⟩

theorem sylow_two_of_card {G : Type*} [Group G] [Finite G] (S : Subgroup G) {k : ℕ}
    (hS : Nat.card S = 2 ^ k) (hodd : ¬ 2 ∣ S.index) : Nonempty (Sylow 2 G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨(IsPGroup.of_card hS).toSylow hodd⟩

end CFSG.ComponentClassification.Sol76.Sig.GSYard02.CoverAltGroup

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard02

open CFSG Subgroup CFSG.Alternating.Multipliers.Spin
open SpinNative (Wd Q4 invW wordsOK)
open CFSG.Alternating.Multipliers CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.Sol76.Sig.GSYard02.CoverAltGroup
open scoped commutatorElement

section Model

variable {m : ℕ}

theorem exists_negE (hm : 2 ≤ m) : ∃ x : E (m + 2), ((x : H (m + 2)) : monomial (m + 2)) = negOne := by
  set p₀ : Fin (m + 2) := ⟨0, by omega⟩
  set p₁ : Fin (m + 2) := ⟨1, by omega⟩
  set p₂ : Fin (m + 2) := ⟨2, by omega⟩
  set p₃ : Fin (m + 2) := ⟨3, by omega⟩
  have h01 : p₀ ≠ p₁ := by simp [p₀, p₁]
  have h02 : p₀ ≠ p₂ := by simp [p₀, p₂, Fin.ext_iff]
  have h03 : p₀ ≠ p₃ := by simp [p₀, p₃, Fin.ext_iff]
  have h12 : p₁ ≠ p₂ := by simp [p₁, p₂, Fin.ext_iff]
  have h13 : p₁ ≠ p₃ := by simp [p₁, p₃, Fin.ext_iff]
  have h23 : p₂ ≠ p₃ := by simp [p₂, p₃, Fin.ext_iff]
  set x : H (m + 2) := ⟨dd h01 h23, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  set y : H (m + 2) := ⟨dd h02 h13, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩
  exact ⟨⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩,
    commutator_dd h01 h02 h03 h12 h13 h23⟩

noncomputable def negE (hm : 2 ≤ m) : E (m + 2) := (exists_negE (m := m) hm).choose

theorem coe_negE (hm : 2 ≤ m) :
    ((negE hm : H (m + 2)) : monomial (m + 2)) = negOne :=
  (exists_negE (m := m) hm).choose_spec

theorem psi_negE (hm : 2 ≤ m) : psi (negE hm) = 1 := by
  apply Subtype.ext
  change perm ((negE hm : H (m + 2)) : monomial (m + 2)) = 1
  rw [coe_negE, perm_negOne]

theorem negE_ne_one (hm : 2 ≤ m) : negE hm ≠ 1 := by
  intro h
  have := coe_negE (m := m) hm
  rw [h] at this
  exact negOne_ne_one (by rw [← this]; rfl)

end Model

section Model2

variable {m : ℕ}

theorem card_ker_psi_le (hm : 6 ≤ m) :
    Finite (psi (m := m)).ker ∧ Nat.card (psi (m := m)).ker ≤ 2 := by
  have hK : (psi (m := m)).ker ≤ center (E (m + 2)) := ker_psi_le_center
  have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
  have hperf : Group.IsPerfect (E (m + 2)) := E_isPerfect (by omega)
  have hAperf : Group.IsPerfect (alternatingGroup (Fin (m + 2))) :=
    ⟨commutator_alternatingGroup_eq_top (by simp; omega)⟩
  haveI : Finite (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    CFSG.RankThree.PerfectCover.finite_hopfMultiplier hAperf
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift (psi (m := m)) hψ hK
  have hcardM : Nat.card (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_hopfMultiplier_alternatingGroup (by omega)
  let g : RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2))) →
      (psi (m := m)).ker := fun x =>
    ⟨RankThree.PerfectCover.hopfLift (psi (m := m)) hψ hK x.1, by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ x.2⟩
  have hg : Function.Surjective g := by
    intro y
    have hy : (y : E (m + 2)) ∈ (RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin (m + 2)))).map
        (RankThree.PerfectCover.hopfLift (psi (m := m)) hψ hK) := by
      rw [hmap]; exact y.2
    obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩
  haveI : Finite (psi (m := m)).ker := Finite.of_surjective g hg
  refine ⟨inferInstance, ?_⟩
  have := Nat.card_le_card_of_surjective g hg
  omega

theorem card_ker_psi (hm : 6 ≤ m) : Nat.card (psi (m := m)).ker = 2 := by
  obtain ⟨hfin, hle⟩ := card_ker_psi_le hm
  haveI := hfin
  have hne : (psi (m := m)).ker ≠ ⊥ := by
    intro h
    have hmem : negE (m := m) (by omega) ∈ (psi (m := m)).ker := by
      rw [MonoidHom.mem_ker]; exact psi_negE _
    rw [h, Subgroup.mem_bot] at hmem
    exact negE_ne_one _ hmem
  have h1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  omega

theorem negOne_mul_negOne : (negOne : monomial (m + 2)) * negOne = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp [negOne]

theorem negE_sq (hm : 2 ≤ m) : negE (m := m) hm * negE (m := m) hm = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_one]
  rw [coe_negE]
  exact negOne_mul_negOne

theorem ker_psi_eq (hm : 6 ≤ m) (x : E (m + 2)) (hx : psi x = 1) :
    x = 1 ∨ x = negE (m := m) (by omega) := by
  obtain ⟨hfin, _⟩ := card_ker_psi_le hm
  haveI := hfin
  set g := negE (m := m) (by omega) with hg
  have hle : Subgroup.closure {g} ≤ (psi (m := m)).ker := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact MonoidHom.mem_ker.mpr (psi_negE _)
  have hgsq : g ^ 2 = 1 := by rw [sq]; exact negE_sq _
  have hgne : g ≠ 1 := negE_ne_one _
  have hord : orderOf g = 2 := orderOf_eq_prime hgsq hgne
  have hcl : Nat.card (Subgroup.closure {g}) = 2 := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, hord]
  have hkeq : (psi (m := m)).ker = Subgroup.closure {g} := by
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    exact le_of_eq (by rw [card_ker_psi hm, hcl])
  have hxmem : x ∈ Subgroup.closure {g} := by rw [← hkeq]; exact MonoidHom.mem_ker.mpr hx
  obtain ⟨k, hk⟩ := Subgroup.mem_closure_singleton.mp hxmem
  rw [← hk]
  have hmod : g ^ k = g ^ (k % (2 : ℤ)) := by
    rw [← zpow_mod_orderOf g k, hord]; simp
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left; rw [hmod, h0, zpow_zero]
  · right; rw [hmod, h1, zpow_one]

end Model2

section Model3

variable {m : ℕ}

theorem center_E_eq (hm : 6 ≤ m) : center (E (m + 2)) = (psi (m := m)).ker := by
  apply le_antisymm
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
    have hc : psi z ∈ center (alternatingGroup (Fin (m + 2))) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hψ g
      have h := congrArg psi ((Subgroup.mem_center_iff.mp hz) y)
      simp only [map_mul] at h
      exact h
    rw [alternatingGroup.center_eq_bot (by simp; omega)] at hc
    simpa using hc
  · exact ker_psi_le_center

theorem finite_E (hm : 6 ≤ m) : Finite (E (m + 2)) := by
  obtain ⟨hfin, _⟩ := card_ker_psi_le hm
  haveI := hfin
  have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
  have e := QuotientGroup.quotientKerEquivOfSurjective (psi (m := m)) hψ
  haveI : Finite (E (m + 2) ⧸ (psi (m := m)).ker) := Finite.of_equiv _ e.toEquiv.symm
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := (psi (m := m)).ker)).symm

theorem alternatingGroup_nonabelian {n : ℕ} (hn : 4 ≤ n) :
    ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have : IsMulCommutative (alternatingGroup (Fin n)) := ⟨⟨fun a b => hcon a b⟩⟩
  have h := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin n)).mp this
  simp at h
  omega

noncomputable def quotCenter_iso (hm : 6 ≤ m) :
    E (m + 2) ⧸ center (E (m + 2)) ≃* alternatingGroup (Fin (m + 2)) :=
  (QuotientGroup.quotientMulEquivOfEq (center_E_eq hm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective (psi (m := m)) (psi_surjective (by omega)))

theorem isQuasisimple_E (hm : 6 ≤ m) : IsQuasisimple (E (m + 2)) := by
  refine ⟨E_isPerfect (m := m) (by omega), ?_⟩
  have hA : IsSimpleGroup (alternatingGroup (Fin (m + 2))) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  haveI := hA
  obtain ⟨a₀, b₀, hab₀⟩ := alternatingGroup_nonabelian (n := m + 2) (by omega)
  haveI : Nontrivial (alternatingGroup (Fin (m + 2))) :=
    ⟨⟨a₀, b₀, fun h => hab₀ (by rw [h])⟩⟩
  have e := quotCenter_iso hm
  haveI : Nontrivial (E (m + 2) ⧸ center (E (m + 2))) := e.toEquiv.nontrivial
  refine ⟨IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom e.symm.surjective, ?_⟩
  exact ⟨e.symm a₀, e.symm b₀, fun h => hab₀ (by have := congrArg e h; simpa using this)⟩

theorem card_center_E (hm : 6 ≤ m) : Nat.card (center (E (m + 2))) = 2 := by
  rw [center_E_eq hm]
  exact card_ker_psi hm

theorem card_E (hm : 6 ≤ m) : Nat.card (E (m + 2)) = (m + 2).factorial := by
  haveI := finite_E hm
  have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
  have e := QuotientGroup.quotientKerEquivOfSurjective (psi (m := m)) hψ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (psi (m := m)).ker,
    Nat.card_congr e.toEquiv, card_ker_psi hm]
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin (m + 2))
  have h3 : Nat.card (Equiv.Perm (Fin (m + 2))) = (m + 2).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  omega

theorem quotCenter_E (hm : 6 ≤ m) :
    Nonempty (E (m + 2) ⧸ center (E (m + 2)) ≃* alternatingGroup (Fin (m + 2))) :=
  ⟨quotCenter_iso hm⟩

end Model3

namespace SpinM

def Mdd {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (q : Q4) :
    Matrix (Fin N) (Fin N) ℚ :=
  if q.1 = q.2.1 ∨ q.2.2.1 = q.2.2.2 then 1
  else (1 / 2 : ℚ) • ((Γ q.1 - Γ q.2.1) * (Γ q.2.2.1 - Γ q.2.2.2))

def Mw {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (w : Wd) :
    Matrix (Fin N) (Fin N) ℚ :=
  (w.map (Mdd Γ)).prod

def Mcomm {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (p : Wd × Wd) :
    Matrix (Fin N) (Fin N) ℚ :=
  Mw Γ p.1 * Mw Γ p.2 * Mw Γ (invW p.1) * Mw Γ (invW p.2)

def gensM {N : ℕ} (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (ps : List (Wd × Wd)) :
    List (Matrix (Fin N) (Fin N) ℚ) :=
  ps.map (Mcomm Γ) ++ ps.map fun p => Mcomm Γ (p.2, p.1)

end SpinM

section Bridge

open SpinNative (Mat ent ofF oneM zeroM addM subM smulM mulM prodM gensM closedB
  pairsS10 treeS10)

variable {N : ℕ}

def toMat (A : Mat N) : Matrix (Fin N) (Fin N) ℚ := Matrix.of fun i j => ent A i j

def Gm (Γ : ℕ → Mat N) : ℕ → Matrix (Fin N) (Fin N) ℚ := fun k => toMat (Γ k)

def klTab (Γ : ℕ → Mat N) : List (Matrix (Fin N) (Fin N) ℚ) :=
  CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) pairsS10) treeS10

theorem ent_ofF (f : Fin N → Fin N → ℚ) (i j : Fin N) : ent (ofF f) i j = f i j := by
  simp [ent, ofF]

theorem toMat_ofF (f : Fin N → Fin N → ℚ) : toMat (ofF f) = Matrix.of f := by
  ext i j
  simp [toMat, ent_ofF]

theorem get_eq_getElem' {α : Type*} {n : ℕ} (v : Vector α n) (i : Fin n) :
    v.get i = v[i.val]'i.isLt := rfl

theorem toMat_injective : Function.Injective (toMat (N := N)) := by
  intro A B h
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have h' := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
  simpa [toMat, ent, get_eq_getElem'] using h'

theorem toMat_oneM : toMat (oneM N) = 1 := by
  ext i j
  simp [oneM, toMat_ofF, Matrix.one_apply]

theorem toMat_zeroM : toMat (zeroM N) = 0 := by
  ext i j
  simp [zeroM, toMat_ofF, ent_ofF]

theorem toMat_addM (A B : Mat N) : toMat (addM A B) = toMat A + toMat B := by
  ext i j
  simp [addM, toMat_ofF, toMat, ent_ofF]

theorem toMat_subM (A B : Mat N) : toMat (subM A B) = toMat A - toMat B := by
  ext i j
  simp [subM, toMat_ofF, toMat, ent_ofF]

theorem toMat_smulM (c : ℚ) (A : Mat N) : toMat (smulM c A) = c • toMat A := by
  ext i j
  simp [smulM, toMat_ofF, toMat, ent_ofF]

theorem foldl_skip (f g : Fin N → ℚ) (ks : List (Fin N)) (acc : ℚ) :
    ks.foldl (fun acc k => if f k = 0 then acc else acc + f k * g k) acc =
      acc + (ks.map fun k => f k * g k).sum := by
  induction ks generalizing acc with
  | nil => simp
  | cons k ks ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]
    split_ifs with h
    · simp [h]
    · rw [add_assoc]

theorem toMat_mulM (A B : Mat N) : toMat (mulM A B) = toMat A * toMat B := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_def]
  simp only [toMat, Matrix.of_apply, mulM, ent_ofF]
  rw [foldl_skip, zero_add]

theorem toMat_prodM : ∀ L : List (Mat N), toMat (prodM L) = (L.map toMat).prod
  | [] => by simp [prodM, toMat_oneM]
  | A :: As => by simp [prodM, toMat_mulM, toMat_prodM As]

theorem toMat_Mdd (G : ℕ → Mat N) (q : Q4) :
    toMat (SpinNative.Mdd G q) = SpinM.Mdd (Gm G) q := by
  unfold SpinNative.Mdd SpinM.Mdd Gm
  split_ifs
  · exact toMat_oneM
  · simp [toMat_smulM, toMat_mulM, toMat_subM]

theorem toMat_Mw (G : ℕ → Mat N) (w : Wd) :
    toMat (SpinNative.Mw G w) = SpinM.Mw (Gm G) w := by
  unfold SpinNative.Mw SpinM.Mw
  rw [toMat_prodM, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact toMat_Mdd G q

theorem toMat_Mcomm (G : ℕ → Mat N) (p : Wd × Wd) :
    toMat (SpinNative.Mcomm G p) = SpinM.Mcomm (Gm G) p := by
  simp [SpinNative.Mcomm, SpinM.Mcomm, toMat_mulM, toMat_Mw]

theorem toMat_gensM (G : ℕ → Mat N) (ps : List (Wd × Wd)) :
    (gensM G ps).map toMat = SpinM.gensM (Gm G) ps := by
  simp [gensM, SpinM.gensM, SpinNative.gensM, List.map_append, List.map_map, toMat_Mcomm,
    Function.comp_def]

theorem toMat_getD (L : List (Mat N)) (i : ℕ) :
    toMat (L.getD i (oneM N)) = (L.map toMat).getD i 1 := by
  by_cases h : i < L.length
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h, toMat_oneM]

theorem toMat_treeAux (gs : List (Mat N)) (tr : List (ℕ × ℕ)) :
    ∀ acc : List (Mat N), (SpinNative.treeAux gs acc tr).map toMat =
      CoverAltGroup.treeAux (gs.map toMat) (acc.map toMat) tr := by
  induction tr with
  | nil => intro acc; simp [SpinNative.treeAux, CoverAltGroup.treeAux]
  | cons pg tr ih =>
    intro acc
    obtain ⟨p, g⟩ := pg
    simp only [SpinNative.treeAux, CoverAltGroup.treeAux]
    rw [ih]
    congr 1
    rw [List.map_append, List.map_cons, List.map_nil, toMat_mulM, toMat_getD, toMat_getD]

theorem toMat_treeTab (gs : List (Mat N)) (tr : List (ℕ × ℕ)) :
    (SpinNative.treeTab gs tr).map toMat = CoverAltGroup.treeTab (gs.map toMat) tr := by
  unfold SpinNative.treeTab CoverAltGroup.treeTab
  rw [toMat_treeAux]
  simp [toMat_oneM]

theorem treeTab_gensM_map (Γ : ℕ → Mat N) (ps : List (Wd × Wd)) (tr : List (ℕ × ℕ)) :
    (SpinNative.treeTab (gensM Γ ps) tr).map toMat =
      CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) ps) tr := by
  rw [toMat_treeTab, toMat_gensM]

theorem klTab_eq (Γ : ℕ → Mat N) :
    klTab Γ = (SpinNative.treeTab (gensM Γ pairsS10) treeS10).map toMat := by
  unfold klTab
  rw [treeTab_gensM_map]

theorem tab_getD_eq (Γ : ℕ → Mat N) (i : ℕ) :
    toMat ((SpinNative.treeTab (gensM Γ pairsS10) treeS10).getD i (oneM N)) =
      (klTab Γ).getD i 1 := by
  rw [toMat_getD, klTab_eq]

theorem toMat_mul_eq_iff (a b : Mat N) :
    toMat a * toMat b = toMat b * toMat a ↔ mulM a b = mulM b a := by
  constructor
  · intro h
    apply toMat_injective
    rw [toMat_mulM, toMat_mulM]
    exact h
  · intro h
    rw [← toMat_mulM, ← toMat_mulM, h]

theorem toMat_ne_one (a : Mat N) : toMat a ≠ 1 ↔ a ≠ oneM N :=
  ⟨fun h e => h (by rw [e, toMat_oneM]), fun h e => h (toMat_injective (by rw [e, toMat_oneM]))⟩

theorem toMat_ne_iff (a b : Mat N) : toMat a ≠ toMat b ↔ a ≠ b :=
  ⟨fun h e => h (by rw [e]), fun h e => h (toMat_injective e)⟩

theorem toMat_sq_iff (d : Mat N) :
    (toMat d * toMat d = 1 ∧ toMat d ≠ 1) ↔ (mulM d d = oneM N ∧ d ≠ oneM N) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨toMat_injective ?_, fun h => h2 ?_⟩
    · rw [toMat_mulM, toMat_oneM]; exact h1
    · rw [h, toMat_oneM]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun h => h2 (toMat_injective ?_)⟩
    · rw [← toMat_mulM, h1, toMat_oneM]
    · rw [h, toMat_oneM]

theorem closedB_spec_M {T gs : List (Mat N)} (h : closedB T gs = true) :
    (T.map toMat).Nodup ∧ ∀ x ∈ T.map toMat, ∀ g ∈ gs.map toMat, g * x ∈ T.map toMat := by
  simp only [closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hnd, hcl⟩ := h
  refine ⟨List.Nodup.map toMat_injective hnd, ?_⟩
  intro x hx g hg
  obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  rw [← toMat_mulM]
  exact List.mem_map_of_mem (hcl x' hx' g' hg')

end Bridge

section Clifford

variable {N : ℕ}

def GammaRel (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, Γ i * Γ j + Γ j * Γ i = if i = j then (2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ) else 0

theorem gamRelB_spec {n : ℕ} {Γ : ℕ → SpinNative.Mat N} (h : SpinNative.gamRelB Γ n = true) :
    GammaRel (Gm Γ) n := by
  intro i hi j hj
  simp only [SpinNative.gamRelB, List.all_eq_true, decide_eq_true_eq, List.mem_range] at h
  have h3 := congrArg toMat (h i hi j hj)
  rw [toMat_addM, toMat_mulM, toMat_mulM] at h3
  simp only [Gm]
  split_ifs at h3 ⊢
  · rw [toMat_smulM, toMat_oneM] at h3; exact h3
  · rw [toMat_zeroM] at h3; exact h3

def gammaLin (Γ : ℕ → Matrix (Fin N) (Fin N) ℚ) (n : ℕ) :
    (Fin n → ℚ) →ₗ[ℚ] Matrix (Fin N) (Fin N) ℚ where
  toFun x := ∑ i : Fin n, x i • Γ i.val
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

theorem sumSq_apply' (n : ℕ) (x : Fin n → ℚ) : sumSq n x = ∑ i, x i * x i := by
  simp [sumSq, QuadraticMap.weightedSumSquares_apply]

theorem gammaLin_mul_self {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n)
    (x : Fin n → ℚ) :
    gammaLin Γ n x * gammaLin Γ n x = algebraMap ℚ (Matrix (Fin N) (Fin N) ℚ) (∑ i : Fin n, x i * x i) := by
  have hrel : ∀ i j : Fin n, Γ i.val * Γ j.val + Γ j.val * Γ i.val =
      if i = j then (2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ) else 0 := by
    intro i j
    have := h i.val i.isLt j.val j.isLt
    simpa [Fin.val_inj] using this
  set S := ∑ i : Fin n, ∑ j : Fin n, (x i * x j) • (Γ i.val * Γ j.val) with hSdef
  set T := ∑ i : Fin n, ∑ j : Fin n, (x i * x j) • (Γ j.val * Γ i.val) with hTdef
  have hAA : gammaLin Γ n x * gammaLin Γ n x = S := by
    simp only [gammaLin, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul_sum, hSdef]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm]
  have hsym : S = T := by
    rw [hSdef, hTdef, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (x j) (x i)]
  have hST : S + T = (∑ i : Fin n, x i * x i) • ((2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ)) := by
    rw [hSdef, hTdef, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ j : Fin n, (x i * x j) • (Γ i.val * Γ j.val) + (x i * x j) • (Γ j.val * Γ i.val) =
        if i = j then (x i * x i) • ((2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ)) else 0 := by
      intro j
      rw [← smul_add, hrel i j]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_ite_eq]
    simp
  have hsum2 : (2 : ℚ) • S = (2 : ℚ) • algebraMap ℚ (Matrix (Fin N) (Fin N) ℚ) (∑ i : Fin n, x i * x i) := by
    rw [(two_smul ℚ S).trans (congrArg (S + ·) hsym), hST, Algebra.algebraMap_eq_smul_one, smul_comm]
  rw [hAA]
  exact smul_right_injective (Matrix (Fin N) (Fin N) ℚ) two_ne_zero hsum2

def cliffHom {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) :
    CliffordAlgebra (CFSG.Alternating.Multipliers.Spin.sumSq n) →ₐ[ℚ] Matrix (Fin N) (Fin N) ℚ :=
  CliffordAlgebra.lift (CFSG.Alternating.Multipliers.Spin.sumSq n)
    ⟨gammaLin Γ n, fun x => by rw [sumSq_apply']; exact gammaLin_mul_self h x⟩

theorem cliffHom_v {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) (i : Fin n) :
    cliffHom h (CFSG.Alternating.Multipliers.Spin.v n i) = Γ i.val := by
  unfold cliffHom CFSG.Alternating.Multipliers.Spin.v
  rw [CliffordAlgebra.lift_ι_apply]
  simp [gammaLin, Pi.single_apply]

theorem cliffHom_algebraMap {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) (c : ℚ) :
    cliffHom h (algebraMap ℚ (CliffordAlgebra (CFSG.Alternating.Multipliers.Spin.sumSq n)) c) =
      c • (1 : Matrix (Fin N) (Fin N) ℚ) := by
  rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]

end Clifford

section Rep

variable {N : ℕ}

def thetaH {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) :
    H n →* (Matrix (Fin N) (Fin N) ℚ)ˣ :=
  (Units.map (cliffHom h).toMonoidHom).comp ((monomial n).subtype.comp (H n).subtype)

def thetaE {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) :
    E n →* (Matrix (Fin N) (Fin N) ℚ)ˣ :=
  (thetaH h).comp (E n).subtype

end Rep

section Injective

variable {N : ℕ} {m : ℕ}

theorem thetaE_val {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ} (h : GammaRel Γ n) (x : E n) :
    ((thetaE h x : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) =
      cliffHom h ((((x : H n) : monomial n) : (Cl n)ˣ) : Cl n) := rfl

theorem comm_mul_central_left {G : Type*} [Group G] {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : z * b = b * z := (Subgroup.mem_center_iff.mp hz b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_central_right {G : Type*} [Group G] {a b z : G} (hz : z ∈ Subgroup.center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h : z * a⁻¹ = a⁻¹ * z := (Subgroup.mem_center_iff.mp hz a⁻¹).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_central {G : Type*} [Group G] {n₁ n₂ k₁ k₂ : G} (hk₁ : k₁ ∈ Subgroup.center G)
    (hk₂ : k₂ ∈ Subgroup.center G) : ⁅n₁ * k₁, n₂ * k₂⁆ = ⁅n₁, n₂⁆ := by
  rw [comm_mul_central_left hk₁, comm_mul_central_right hk₂]

theorem thetaE_injective (hm : 6 ≤ m) {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} (h : GammaRel Γ (m + 2))
    (hN : 0 < N) : Function.Injective (thetaE h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set θ := thetaE (n := m + 2) h with hθ
  have hψ : Function.Surjective (psi (m := m)) := psi_surjective (by omega)
  have hnegθ : θ (negE (m := m) (by omega)) ≠ 1 := by
    intro h1
    have h2 := congrArg (fun u : (Matrix (Fin N) (Fin N) ℚ)ˣ => (u : Matrix (Fin N) (Fin N) ℚ)) h1
    simp only [Units.val_one] at h2
    rw [hθ, thetaE_val] at h2
    have hc : ((((negE (m := m) (by omega) : H (m + 2)) : monomial (m + 2)) : (Cl (m + 2))ˣ) : Cl (m + 2)) = -1 := by
      rw [coe_negE]; rfl
    rw [hc, map_neg, map_one] at h2
    have h3 := congrFun (congrFun h2 ⟨0, hN⟩) ⟨0, hN⟩
    norm_num at h3
  have hNn : θ.ker.Normal := MonoidHom.normal_ker θ
  have hM : (θ.ker.map (psi (m := m))).Normal := hNn.map psi hψ
  have hA : IsSimpleGroup (alternatingGroup (Fin (m + 2))) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  have hxker : x ∈ θ.ker := MonoidHom.mem_ker.mpr hx
  haveI := hM
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (θ.ker.map (psi (m := m))) with hbot | htop
  · have hpx : psi x = 1 := by
      have hmem : psi x ∈ θ.ker.map (psi (m := m)) := Subgroup.mem_map_of_mem _ hxker
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    rcases ker_psi_eq hm x hpx with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx) hnegθ
  · exfalso
    have hdec : ∀ e : E (m + 2), ∃ k ∈ Subgroup.center (E (m + 2)), ∃ n ∈ θ.ker, e = n * k := by
      intro e
      have he : psi e ∈ θ.ker.map (psi (m := m)) := by rw [htop]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hpn⟩ := Subgroup.mem_map.mp he
      refine ⟨n⁻¹ * e, ?_, n, hn, by group⟩
      rw [center_E_eq hm, MonoidHom.mem_ker, map_mul, map_inv, hpn, inv_mul_cancel]
    have hcomm : ∀ a b : E (m + 2), ⁅a, b⁆ ∈ θ.ker := by
      intro a b
      obtain ⟨k₁, hk₁, n₁, hn₁, rfl⟩ := hdec a
      obtain ⟨k₂, hk₂, n₂, hn₂, rfl⟩ := hdec b
      rw [comm_central hk₁ hk₂]
      exact θ.ker.mul_mem (θ.ker.mul_mem (θ.ker.mul_mem hn₁ hn₂) (θ.ker.inv_mem hn₁)) (θ.ker.inv_mem hn₂)
    have hcommE : commutator (E (m + 2)) ≤ θ.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      exact hcomm a b
    have htopE : (⊤ : Subgroup (E (m + 2))) ≤ θ.ker := by
      rw [← Group.isPerfect_def.mp (E_isPerfect (by omega))]
      exact hcommE
    exact hnegθ (MonoidHom.mem_ker.mp (htopE (Subgroup.mem_top _)))

end Injective

section Words

open SpinM (Mdd Mw Mcomm gensM)

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ}

abbrev ValidQ (n : ℕ) (q : Q4) : Prop :=
  q.1 < n ∧ q.2.1 < n ∧ q.2.2.1 < n ∧ q.2.2.2 < n ∧ q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2

instance (n : ℕ) (q : Q4) : Decidable (ValidQ n q) := by
  unfold ValidQ; infer_instance

def ddH (n : ℕ) (q : Q4) : H n :=
  if h : ValidQ n q then
    have hab : (⟨q.1, h.1⟩ : Fin n) ≠ ⟨q.2.1, h.2.1⟩ := fun e => h.2.2.2.2.1 (congrArg Fin.val e)
    have hcd : (⟨q.2.2.1, h.2.2.1⟩ : Fin n) ≠ ⟨q.2.2.2, h.2.2.2.1⟩ :=
      fun e => h.2.2.2.2.2 (congrArg Fin.val e)
    ⟨dd hab hcd, subset_closure ⟨_, _, _, _, hab, hcd, rfl⟩⟩
  else 1

def wordH (n : ℕ) (X : Wd) : H n := (X.map (ddH n)).prod

def liftE (n : ℕ) (X Y : Wd) : E n :=
  ⟨⁅wordH n X, wordH n Y⁆, commutator_mem_commutator (mem_top _) (mem_top _)⟩

def gensE (n : ℕ) (ps : List (Wd × Wd)) : List (E n) :=
  ps.map (fun p => liftE n p.1 p.2) ++ ps.map (fun p => liftE n p.2 p.1)

def thetaM (h : GammaRel Γ n) : E n →* Matrix (Fin N) (Fin N) ℚ :=
  (Units.coeHom (Matrix (Fin N) (Fin N) ℚ)).comp (thetaE h)

theorem thetaM_injective_of_thetaE {h : GammaRel Γ n} (hinj : Function.Injective (thetaE h)) :
    Function.Injective (thetaM h) := by
  intro x y hxy
  apply hinj
  apply Units.ext
  exact hxy

theorem cliffHom_r' (h : GammaRel Γ n) (a b : Fin n) :
    cliffHom h (CFSG.Alternating.Multipliers.Spin.r a b) = Γ a.val - Γ b.val := by
  unfold CFSG.Alternating.Multipliers.Spin.r
  rw [map_sub, cliffHom_v, cliffHom_v]

theorem cliffHom_half (h : GammaRel Γ n) :
    cliffHom h (CFSG.Alternating.Multipliers.Spin.half : CliffordAlgebra
      (CFSG.Alternating.Multipliers.Spin.sumSq n)) = (1 / 2 : ℚ) • (1 : Matrix (Fin N) (Fin N) ℚ) := by
  unfold CFSG.Alternating.Multipliers.Spin.half
  exact cliffHom_algebraMap h _

theorem thetaH_ddH (h : GammaRel Γ n) (q : Q4) (hq : ValidQ n q) :
    ((thetaH h (ddH n q) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) = Mdd Γ q := by
  have hdd : ((thetaH h (ddH n q) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) =
      cliffHom h (CFSG.Alternating.Multipliers.Spin.half *
        CFSG.Alternating.Multipliers.Spin.r (⟨q.1, hq.1⟩ : Fin n) ⟨q.2.1, hq.2.1⟩ *
        CFSG.Alternating.Multipliers.Spin.r (⟨q.2.2.1, hq.2.2.1⟩ : Fin n) ⟨q.2.2.2, hq.2.2.2.1⟩) := by
    unfold ddH
    rw [dif_pos hq]
    rfl
  have hne : ¬ (q.1 = q.2.1 ∨ q.2.2.1 = q.2.2.2) := fun h => h.elim hq.2.2.2.2.1 hq.2.2.2.2.2
  have hMdd : SpinM.Mdd Γ q = (1 / 2 : ℚ) • ((Γ q.1 - Γ q.2.1) * (Γ q.2.2.1 - Γ q.2.2.2)) := by
    unfold SpinM.Mdd
    rw [if_neg hne]
  rw [hMdd, hdd, map_mul, map_mul, cliffHom_half, cliffHom_r', cliffHom_r']
  simp only [smul_mul_assoc, one_mul]

end Words

section Words2

open SpinM (Mdd Mw Mcomm gensM)

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ}

theorem validQ_swap {q : Q4} (hq : ValidQ n q) : ValidQ n (q.2.2.1, q.2.2.2, q.1, q.2.1) :=
  ⟨hq.2.2.1, hq.2.2.2.1, hq.1, hq.2.1, hq.2.2.2.2.2, hq.2.2.2.2.1⟩

theorem half_dd_dd_swap {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    (CFSG.Alternating.Multipliers.Spin.half * CFSG.Alternating.Multipliers.Spin.r a b *
      CFSG.Alternating.Multipliers.Spin.r c d) *
    (CFSG.Alternating.Multipliers.Spin.half * CFSG.Alternating.Multipliers.Spin.r c d *
      CFSG.Alternating.Multipliers.Spin.r a b) = (1 : CliffordAlgebra (CFSG.Alternating.Multipliers.Spin.sumSq n)) := by
  open CFSG.Alternating.Multipliers.Spin in
  have hA : r a b * r a b = 2 := r_mul_self hab
  have hB : r c d * r c d = 2 := r_mul_self hcd
  have h2c : r a b * (2 * r a b) = 2 * (r a b * r a b) := by
    rw [← mul_assoc, (Commute.ofNat_right (r a b) 2).eq, mul_assoc]
  have hhh : (half : Cl n) * half = algebraMap ℚ (Cl n) (1 / 4) := by
    rw [half, ← map_mul]; norm_num
  calc (half * r a b * r c d) * (half * r c d * r a b)
      = half * (r a b * (r c d * (half * (r c d * r a b)))) := by simp only [mul_assoc]
    _ = half * (r a b * (r c d * ((r c d * r a b) * half))) := by rw [half_comm (r c d * r a b)]
    _ = half * ((r a b * (r c d * (r c d * r a b))) * half) := by simp only [mul_assoc]
    _ = half * (half * (r a b * (r c d * (r c d * r a b)))) := by
          rw [half_comm (r a b * (r c d * (r c d * r a b)))]
    _ = (half * half) * (r a b * (r c d * (r c d * r a b))) := by rw [mul_assoc]
    _ = (half * half) * (r a b * ((r c d * r c d) * r a b)) := by simp only [mul_assoc]
    _ = (half * half) * (r a b * (2 * r a b)) := by rw [hB]
    _ = (half * half) * (2 * (r a b * r a b)) := by rw [h2c]
    _ = (half * half) * 4 := by rw [hA]; norm_num
    _ = algebraMap ℚ (Cl n) (1 / 4) * 4 := by rw [hhh]
    _ = 1 := by
          rw [← map_ofNat (algebraMap ℚ (Cl n)) 4, ← map_mul]; norm_num

theorem ddH_swap (q : Q4) (hq : ValidQ n q) :
    ddH n (q.2.2.1, q.2.2.2, q.1, q.2.1) = (ddH n q)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  have hq' : ValidQ n (q.2.2.1, q.2.2.2, q.1, q.2.1) := validQ_swap hq
  unfold ddH
  rw [dif_pos hq, dif_pos hq']
  have hab : (⟨q.1, hq.1⟩ : Fin n) ≠ ⟨q.2.1, hq.2.1⟩ := fun e => hq.2.2.2.2.1 (congrArg Fin.val e)
  have hcd : (⟨q.2.2.1, hq.2.2.1⟩ : Fin n) ≠ ⟨q.2.2.2, hq.2.2.2.1⟩ :=
    fun e => hq.2.2.2.2.2 (congrArg Fin.val e)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simpa [CFSG.Alternating.Multipliers.Spin.coe_dd] using half_dd_dd_swap hab hcd

theorem invW_cons (q : Q4) (X : Wd) : invW (q :: X) = invW X ++ [(q.2.2.1, q.2.2.2, q.1, q.2.1)] := by
  simp [invW, List.reverse_cons]

theorem wordH_invW (X : Wd) (hX : ∀ q ∈ X, ValidQ n q) : wordH n (invW X) = (wordH n X)⁻¹ := by
  induction X with
  | nil => simp [invW, wordH]
  | cons q X ih =>
    have hq : ValidQ n q := hX q List.mem_cons_self
    have ih' := ih (fun q' hq' => hX q' (List.mem_cons_of_mem _ hq'))
    have hw : wordH n (q :: X) = ddH n q * wordH n X := by simp [wordH]
    have hinv : wordH n (invW (q :: X)) =
        wordH n (invW X) * ddH n (q.2.2.1, q.2.2.2, q.1, q.2.1) := by
      rw [invW_cons]; simp [wordH]
    rw [hinv, ih', ddH_swap q hq, hw, mul_inv_rev]

theorem thetaH_wordH (h : GammaRel Γ n) (X : Wd) (hX : ∀ q ∈ X, ValidQ n q) :
    ((thetaH h (wordH n X) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) = Mw Γ X := by
  induction X with
  | nil => simp [wordH, Mw, thetaH]
  | cons q X ih =>
    have hq : ValidQ n q := hX q List.mem_cons_self
    have ih' := ih (fun q' hq' => hX q' (List.mem_cons_of_mem _ hq'))
    simp only [wordH, List.map_cons, List.prod_cons, Mw] at ih' ⊢
    rw [map_mul, Units.val_mul, thetaH_ddH h q hq]
    rw [ih']

theorem thetaE_liftE (h : GammaRel Γ n) (X Y : Wd) (hX : ∀ q ∈ X, ValidQ n q)
    (hY : ∀ q ∈ Y, ValidQ n q) :
    ((thetaE h (liftE n X Y) : (Matrix (Fin N) (Fin N) ℚ)ˣ) : Matrix (Fin N) (Fin N) ℚ) =
      Mcomm Γ (X, Y) := by
  have hc : thetaE h (liftE n X Y) =
      ⁅thetaH h (wordH n X), thetaH h (wordH n Y)⁆ := by
    rw [thetaE, MonoidHom.comp_apply]
    show thetaH h ⁅wordH n X, wordH n Y⁆ = _
    rw [map_commutatorElement]
  have hX' : ∀ q ∈ invW X, ValidQ n q := by
    intro q hq
    simp only [invW, List.mem_map, List.mem_reverse] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact validQ_swap (hX q' hq')
  have hY' : ∀ q ∈ invW Y, ValidQ n q := by
    intro q hq
    simp only [invW, List.mem_map, List.mem_reverse] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    exact validQ_swap (hY q' hq')
  rw [hc, commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
  have e1 : ((thetaH h (wordH n X))⁻¹ : (Matrix (Fin N) (Fin N) ℚ)ˣ) = thetaH h (wordH n (invW X)) := by
    rw [wordH_invW X hX, map_inv]
  have e2 : ((thetaH h (wordH n Y))⁻¹ : (Matrix (Fin N) (Fin N) ℚ)ˣ) = thetaH h (wordH n (invW Y)) := by
    rw [wordH_invW Y hY, map_inv]
  rw [e1, e2, thetaH_wordH h X hX, thetaH_wordH h Y hY, thetaH_wordH h _ hX', thetaH_wordH h _ hY']
  rfl

end Words2

section Transfer

open SpinM (Mdd Mw Mcomm gensM)

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ} {n : ℕ}

theorem thetaM_liftE (h : GammaRel Γ n) (X Y : Wd) (hX : ∀ q ∈ X, ValidQ n q)
    (hY : ∀ q ∈ Y, ValidQ n q) : thetaM h (liftE n X Y) = Mcomm Γ (X, Y) := by
  unfold thetaM
  rw [MonoidHom.comp_apply, Units.coeHom_apply]
  exact thetaE_liftE h X Y hX hY

theorem liftE_inv (X Y : Wd) : (liftE n X Y)⁻¹ = liftE n Y X := by
  apply Subtype.ext
  change ⁅wordH n X, wordH n Y⁆⁻¹ = ⁅wordH n Y, wordH n X⁆
  rw [commutatorElement_inv]

theorem gensE_map (h : GammaRel Γ n) (ps : List (Wd × Wd))
    (hps : ∀ p ∈ ps, (∀ q ∈ p.1, ValidQ n q) ∧ (∀ q ∈ p.2, ValidQ n q)) :
    (gensE n ps).map (thetaM h) = gensM Γ ps := by
  unfold gensE gensM
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    exact thetaM_liftE h p.1 p.2 (hps p hp).1 (hps p hp).2
  · apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    exact thetaM_liftE h p.2 p.1 (hps p hp).2 (hps p hp).1

theorem getD_map_one {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (l : List G) (i : ℕ) :
    (l.map f).getD i 1 = f (l.getD i 1) := by
  by_cases hi : i < l.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [List.getD_eq_getElem?_getD, hi, map_one]

theorem map_treeAux {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (gs : List G)
    (tr : List (ℕ × ℕ)) : ∀ acc : List G,
      (CoverAltGroup.treeAux gs acc tr).map f = CoverAltGroup.treeAux (gs.map f) (acc.map f) tr := by
  induction tr with
  | nil => intro acc; rfl
  | cons pg tr ih =>
    intro acc
    obtain ⟨p, g⟩ := pg
    simp only [CoverAltGroup.treeAux]
    rw [ih]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, map_mul, getD_map_one]

theorem treeTab_map {G K : Type*} [Monoid G] [Monoid K] (f : G →* K) (gs : List G)
    (tr : List (ℕ × ℕ)) :
    (CoverAltGroup.treeTab gs tr).map f = CoverAltGroup.treeTab (gs.map f) tr := by
  unfold CoverAltGroup.treeTab
  rw [map_treeAux]
  simp

theorem thetaM_injective_of (h : GammaRel Γ n) (hinj : Function.Injective (thetaM h)) :
    Function.Injective (thetaM h) := hinj

theorem closure_of_check (h : GammaRel Γ n) (hinj : Function.Injective (thetaM h))
    (ps : List (Wd × Wd)) (tr : List (ℕ × ℕ))
    (hps : ∀ p ∈ ps, (∀ q ∈ p.1, ValidQ n q) ∧ (∀ q ∈ p.2, ValidQ n q))
    (hnd : (CoverAltGroup.treeTab (gensM Γ ps) tr).Nodup)
    (hcl : ∀ x ∈ CoverAltGroup.treeTab (gensM Γ ps) tr, ∀ g ∈ gensM Γ ps,
      g * x ∈ CoverAltGroup.treeTab (gensM Γ ps) tr) :
    (∀ g ∈ gensE n ps, g⁻¹ ∈ gensE n ps) ∧
    (CoverAltGroup.treeTab (gensE n ps) tr).map (thetaM h) = CoverAltGroup.treeTab (gensM Γ ps) tr ∧
    (∀ x : E n, x ∈ Subgroup.closure {g | g ∈ gensE n ps} ↔ x ∈ CoverAltGroup.treeTab (gensE n ps) tr) ∧
      Nat.card (Subgroup.closure {g | g ∈ gensE n ps}) = (CoverAltGroup.treeTab (gensM Γ ps) tr).length := by
  have hmapE := gensE_map h ps hps
  have hmapT : (CoverAltGroup.treeTab (gensE n ps) tr).map (thetaM h) =
      CoverAltGroup.treeTab (gensM Γ ps) tr := by
    rw [treeTab_map, hmapE]
  have hinv : ∀ g ∈ gensE n ps, g⁻¹ ∈ gensE n ps := by
    intro g hg
    unfold gensE at hg ⊢
    rw [List.mem_append] at hg ⊢
    rcases hg with hg | hg
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      right
      exact List.mem_map.mpr ⟨p, hp, by simp [liftE_inv]⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hg
      left
      exact List.mem_map.mpr ⟨p, hp, by simp [liftE_inv]⟩
  have hndE : (CoverAltGroup.treeTab (gensE n ps) tr).Nodup := by
    apply List.Nodup.of_map (thetaM h)
    rw [hmapT]; exact hnd
  have hclE : ∀ x ∈ CoverAltGroup.treeTab (gensE n ps) tr, ∀ g ∈ gensE n ps,
      g * x ∈ CoverAltGroup.treeTab (gensE n ps) tr := by
    intro x hx g hg
    have hx' : thetaM h x ∈ CoverAltGroup.treeTab (gensM Γ ps) tr := by
      rw [← hmapT]; exact List.mem_map_of_mem hx
    have hg' : thetaM h g ∈ gensM Γ ps := by
      rw [← hmapE]; exact List.mem_map_of_mem hg
    have hmem := hcl _ hx' _ hg'
    rw [← hmapT] at hmem
    obtain ⟨y, hy, hyeq⟩ := List.mem_map.mp hmem
    have : y = g * x := hinj (by rw [hyeq, map_mul])
    rw [← this]; exact hy
  have hcl' := card_closure_eq_length_treeTab (gensE n ps) tr hinv hndE hclE
  refine ⟨hinv, hmapT, fun x => mem_closure_iff_mem_treeTab (gensE n ps) tr hinv hndE hclE x, ?_⟩
  rw [hcl', ← hmapT, List.length_map]

end Transfer

section Checks

open SpinNative

theorem wordsOK_spec {n : ℕ} {ps : List (Wd × Wd)} (h : wordsOK n ps = true) :
    ∀ p ∈ ps, (∀ q ∈ p.1, ValidQ n q) ∧ (∀ q ∈ p.2, ValidQ n q) := by
  intro p hp
  have h1 := (List.all_eq_true.mp h) p hp
  have key : ∀ q ∈ p.1 ++ p.2, ValidQ n q := by
    intro q hq
    have := (List.all_eq_true.mp h1) q hq
    simpa [ValidQ] using this
  exact ⟨fun q hq => key q (List.mem_append_left _ hq), fun q hq => key q (List.mem_append_right _ hq)⟩

def klP (idx : ℕ) : ℕ := (SpinNative.kleinS10.getD idx (0, 0, 0, 0)).1
def klQ (idx : ℕ) : ℕ := (SpinNative.kleinS10.getD idx (0, 0, 0, 0)).2.1
def klR (idx : ℕ) : ℕ := (SpinNative.kleinS10.getD idx (0, 0, 0, 0)).2.2.1
def klPar (idx : ℕ) : ℕ := (SpinNative.kleinS10.getD idx (0, 0, 0, 0)).2.2.2

theorem normalCheck_spec {N n : ℕ} {Γ : ℕ → SpinNative.Mat N}
    (hC : SpinNative.normalCheck Γ n = true) :
    GammaRel (Gm Γ) n ∧ SpinNative.wordsOK n SpinNative.pairsS8 = true ∧
      SpinNative.wordsOK n SpinNative.pairsA8 = true ∧
      (CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsS8) SpinNative.treeS8).Nodup ∧
      (∀ x ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsS8) SpinNative.treeS8,
        ∀ g ∈ SpinM.gensM (Gm Γ) SpinNative.pairsS8,
          g * x ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsS8) SpinNative.treeS8) ∧
      (CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsS8) SpinNative.treeS8).length
        = 128 ∧
      (CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8) SpinNative.treeA8).Nodup ∧
      (∀ x ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8) SpinNative.treeA8,
        ∀ g ∈ SpinM.gensM (Gm Γ) SpinNative.pairsA8,
          g * x ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8) SpinNative.treeA8) ∧
      (CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8) SpinNative.treeA8).length = 8 ∧
      (∀ x ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8) SpinNative.treeA8,
        x * x = 1) ∧
      (∀ g ∈ SpinM.gensM (Gm Γ) SpinNative.pairsS8, ∀ a ∈ SpinM.gensM (Gm Γ) SpinNative.pairsA8,
        ∃ b ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8) SpinNative.treeA8,
          g * a = b * g) := by
  unfold SpinNative.normalCheck at hC
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at hC
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hd⟩, he⟩, hf⟩, hg⟩, hh⟩, hi⟩ := hC
  obtain ⟨hndS, hclS⟩ := closedB_spec_M hd
  obtain ⟨hndA, hclA⟩ := closedB_spec_M hf
  rw [treeTab_gensM_map] at hndS hclS
  rw [toMat_gensM] at hclS
  rw [treeTab_gensM_map] at hndA hclA
  rw [toMat_gensM] at hclA
  have he' : (CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsS8)
      SpinNative.treeS8).length = 128 := by
    rw [← treeTab_gensM_map, List.length_map]; exact he
  have hg' : (CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8)
      SpinNative.treeA8).length = 8 := by
    rw [← treeTab_gensM_map, List.length_map]; exact hg
  have hA2 : ∀ x ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8)
      SpinNative.treeA8, x * x = 1 := by
    intro x hx
    rw [← treeTab_gensM_map] at hx
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
    rw [← toMat_mulM, hh x' hx', toMat_oneM]
  have hi' : ∀ g ∈ SpinM.gensM (Gm Γ) SpinNative.pairsS8,
      ∀ a ∈ SpinM.gensM (Gm Γ) SpinNative.pairsA8,
        ∃ b ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8) SpinNative.treeA8,
          g * a = b * g := by
    intro g hg'' a ha''
    rw [← toMat_gensM] at hg''
    rw [← toMat_gensM] at ha''
    obtain ⟨g', hg3, rfl⟩ := List.mem_map.mp hg''
    obtain ⟨a', ha3, rfl⟩ := List.mem_map.mp ha''
    obtain ⟨b, hbT, hbe⟩ := hi g' hg3 a' ha3
    refine ⟨toMat b, ?_, ?_⟩
    · rw [← treeTab_gensM_map]; exact List.mem_map_of_mem hbT
    · rw [← toMat_mulM, ← toMat_mulM, hbe]
  exact ⟨gamRelB_spec ha, hb, hc, hndS, hclS, he', hndA, hclA, hg', hA2, hi'⟩

theorem kleinCheck_spec {N n : ℕ} {Γ : ℕ → SpinNative.Mat N}
    (hC : SpinNative.kleinCheck Γ n = true) :
    GammaRel (Gm Γ) n ∧
    (∀ p ∈ SpinNative.pairsS10, (∀ q ∈ p.1, ValidQ n q) ∧ (∀ q ∈ p.2, ValidQ n q)) ∧
    (klTab Γ).Nodup ∧
    (∀ x ∈ klTab Γ, ∀ g ∈ SpinM.gensM (Gm Γ) SpinNative.pairsS10, g * x ∈ klTab Γ) ∧
    (klTab Γ).length = 256 ∧
    (∀ idx, idx < SpinNative.kleinS10.length →
      ((klTab Γ).getD (klP idx) 1 * (klTab Γ).getD (klP idx) 1 = 1 ∧
        (klTab Γ).getD (klQ idx) 1 * (klTab Γ).getD (klQ idx) 1 = 1 ∧
        (klTab Γ).getD (klP idx) 1 * (klTab Γ).getD (klQ idx) 1 =
          (klTab Γ).getD (klQ idx) 1 * (klTab Γ).getD (klP idx) 1 ∧
        (klTab Γ).getD (klP idx) 1 ≠ 1 ∧ (klTab Γ).getD (klQ idx) 1 ≠ 1 ∧
        (klTab Γ).getD (klP idx) 1 ≠ (klTab Γ).getD (klQ idx) 1 ∧
        (klTab Γ).getD (klR idx) 1 = (klTab Γ).getD (klP idx) 1 * (klTab Γ).getD (klQ idx) 1)) ∧
    (∀ idx, idx < SpinNative.kleinS10.length → idx = 0 ∨
      (klPar idx < idx ∧
        (klTab Γ).getD (klP idx) 1 * (klTab Γ).getD (klP (klPar idx)) 1 =
          (klTab Γ).getD (klP (klPar idx)) 1 * (klTab Γ).getD (klP idx) 1 ∧
        (klTab Γ).getD (klP idx) 1 * (klTab Γ).getD (klQ (klPar idx)) 1 =
          (klTab Γ).getD (klQ (klPar idx)) 1 * (klTab Γ).getD (klP idx) 1 ∧
        (klTab Γ).getD (klQ idx) 1 * (klTab Γ).getD (klP (klPar idx)) 1 =
          (klTab Γ).getD (klP (klPar idx)) 1 * (klTab Γ).getD (klQ idx) 1 ∧
        (klTab Γ).getD (klQ idx) 1 * (klTab Γ).getD (klQ (klPar idx)) 1 =
          (klTab Γ).getD (klQ (klPar idx)) 1 * (klTab Γ).getD (klQ idx) 1)) ∧
    (∀ i, i < (klTab Γ).length →
      (((klTab Γ).getD i 1 * (klTab Γ).getD i 1 = 1 ∧ (klTab Γ).getD i 1 ≠ 1) ↔
        i ∈ SpinNative.invS10)) ∧
    (∀ i ∈ SpinNative.invS10, ∀ j ∈ SpinNative.invS10,
      i = j ∨ ¬ ((klTab Γ).getD i 1 * (klTab Γ).getD j 1 =
          (klTab Γ).getD j 1 * (klTab Γ).getD i 1) ∨
        ∃ k ∈ SpinNative.kleinS10, i ∈ [0, k.1, k.2.1, k.2.2.1] ∧ j ∈ [0, k.1, k.2.1, k.2.2.1]) := by
  simp only [SpinNative.kleinCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.mem_range] at hC
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, hw⟩, hcl⟩, hlen⟩, hK1⟩, hK2⟩, hK3⟩, hK4⟩ := hC
  obtain ⟨hnd, hcl'⟩ := closedB_spec_M hcl
  rw [← klTab_eq] at hnd
  rw [← klTab_eq] at hcl'
  rw [toMat_gensM] at hcl'
  have hlen' : (klTab Γ).length = 256 := by
    rw [klTab_eq, List.length_map]; exact hlen
  have hlenEq : (SpinNative.treeTab (gensM Γ pairsS10) treeS10).length =
      (klTab Γ).length := by
    rw [klTab_eq, List.length_map]
  refine ⟨gamRelB_spec ha, wordsOK_spec hw, hnd, hcl', hlen', ?_, ?_, ?_, ?_⟩
  · intro idx hidx
    have hmem : SpinNative.kleinS10.getD idx (0, 0, 0, 0) ∈ SpinNative.kleinS10 := by
      rw [List.getD_eq_getElem _ _ hidx]; exact List.getElem_mem hidx
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hK1 _ hmem
    have e1 := congrArg toMat h1
    have e2 := congrArg toMat h2
    have e3 := congrArg toMat h3
    have e4 := (toMat_ne_one _).mpr h4
    have e5 := (toMat_ne_one _).mpr h5
    have e6 := (toMat_ne_iff _ _).mpr h6
    have e7 := congrArg toMat h7
    simp only [toMat_mulM, toMat_oneM, tab_getD_eq] at e1 e2 e3 e7
    simp only [tab_getD_eq] at e4 e5 e6
    exact ⟨e1, e2, e3, e4, e5, e6, e7⟩
  · intro idx hidx
    have h := hK2 idx hidx
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc, or_assoc] at h
    rcases h with h0 | ⟨hpar, c1, c2, c3, c4⟩
    · exact Or.inl h0
    · refine Or.inr ⟨hpar, ?_, ?_, ?_, ?_⟩
      · have e := congrArg toMat c1
        simp only [toMat_mulM, tab_getD_eq] at e
        exact e
      · have e := congrArg toMat c2
        simp only [toMat_mulM, tab_getD_eq] at e
        exact e
      · have e := congrArg toMat c3
        simp only [toMat_mulM, tab_getD_eq] at e
        exact e
      · have e := congrArg toMat c4
        simp only [toMat_mulM, tab_getD_eq] at e
        exact e
  · intro i hi
    have hiT : i < (SpinNative.treeTab (gensM Γ pairsS10) treeS10).length := by
      rw [hlenEq]; exact hi
    have h := decide_eq_decide.mp (hK3 i hiT)
    refine Iff.trans ?_ h
    rw [← tab_getD_eq]
    exact toMat_sq_iff _
  · intro i hi j hj
    have h := hK4 i hi j hj
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
      List.any_eq_true, Bool.and_eq_true, or_assoc, and_assoc] at h
    rcases h with h | h | ⟨k, hk, hik, hjk⟩
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      rw [← tab_getD_eq, ← tab_getD_eq]
      exact fun e => h ((toMat_mul_eq_iff _ _).mp e)
    · exact Or.inr (Or.inr ⟨k, hk, hik, hjk⟩)

end Checks

section Normal

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ}

theorem mem_normalizer_closure {G : Type*} [Group G] (gens : List G) (g : G)
    (h1 : ∀ a ∈ gens, g * a * g⁻¹ ∈ Subgroup.closure {x | x ∈ gens})
    (h2 : ∀ a ∈ gens, g⁻¹ * a * g⁻¹⁻¹ ∈ Subgroup.closure {x | x ∈ gens}) :
    g ∈ Subgroup.normalizer ((Subgroup.closure {x | x ∈ gens} : Subgroup G) : Set G) := by
  set A := Subgroup.closure {x | x ∈ gens} with hA
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hB : A ≤ A.comap (MulAut.conj g).toMonoidHom := by
      rw [hA, Subgroup.closure_le]
      intro a ha
      exact h1 a ha
    exact hB hy
  · intro hy
    have hB : A ≤ A.comap (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hA, Subgroup.closure_le]
      intro a ha
      exact h2 a ha
    have h : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ ∈ A := hB hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h

end Normal

section NormalCase

variable {N : ℕ}

theorem sylowFourJoined_normal (m : ℕ) (hm : 6 ≤ m) (hN : 0 < N) (Γ : ℕ → SpinNative.Mat N)
    (hC : SpinNative.normalCheck Γ (m + 2) = true)
    (k : ℕ) (hk : Nat.card (E (m + 2)) = 2 ^ 7 * k) (hodd : ¬ 2 ∣ k) :
    SylowFourJoined (E (m + 2)) := by
  haveI := finite_E hm
  obtain ⟨hrel, hvS, hvA, hndS, hclS, he, hndA, hclA, hg, hh, hi⟩ := normalCheck_spec hC
  have hinj : Function.Injective (thetaM (n := m + 2) hrel) :=
    thetaM_injective_of_thetaE (thetaE_injective hm hrel hN)
  obtain ⟨hinvS, hmapS, hmemS, hcardS⟩ := closure_of_check hrel hinj (ps := SpinNative.pairsS8)
    (tr := SpinNative.treeS8) (wordsOK_spec hvS) hndS hclS
  obtain ⟨hinvA, hmapA, hmemA, hcardA⟩ := closure_of_check hrel hinj (ps := SpinNative.pairsA8)
    (tr := SpinNative.treeA8) (wordsOK_spec hvA) hndA hclA
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup (E (m + 2)),
      S = Subgroup.closure {g | g ∈ gensE (m + 2) SpinNative.pairsS8} := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup (E (m + 2)),
      A = Subgroup.closure {g | g ∈ gensE (m + 2) SpinNative.pairsA8} := ⟨_, rfl⟩
  have hScard : Nat.card S = 2 ^ 7 := by rw [hSdef, hcardS, he]; norm_num
  have hAcard : Nat.card A = 8 := by rw [hAdef, hcardA, hg]
  have hgE : ∀ g ∈ gensE (m + 2) SpinNative.pairsS8,
      thetaM hrel g ∈ SpinM.gensM (Gm Γ) SpinNative.pairsS8 := by
    intro g hg'
    rw [← gensE_map hrel _ (wordsOK_spec hvS)]
    exact List.mem_map_of_mem hg'
  have hgA : ∀ a ∈ gensE (m + 2) SpinNative.pairsA8,
      thetaM hrel a ∈ SpinM.gensM (Gm Γ) SpinNative.pairsA8 := by
    intro a ha'
    rw [← gensE_map hrel _ (wordsOK_spec hvA)]
    exact List.mem_map_of_mem ha'
  have hconj : ∀ g ∈ gensE (m + 2) SpinNative.pairsS8, ∀ a ∈ gensE (m + 2) SpinNative.pairsA8,
      g * a * g⁻¹ ∈ A := by
    intro g hg' a ha'
    obtain ⟨b, hbT, hbeq⟩ := hi (thetaM hrel g) (hgE g hg') (thetaM hrel a) (hgA a ha')
    have hbmap : b ∈ (CoverAltGroup.treeTab (gensE (m + 2) SpinNative.pairsA8)
        SpinNative.treeA8).map (thetaM hrel) := by
      rw [hmapA]; exact hbT
    obtain ⟨b', hb'T, hb'eq⟩ := List.mem_map.mp hbmap
    have key : g * a = b' * g := hinj (by rw [map_mul, map_mul, hb'eq]; exact hbeq)
    rw [key, mul_assoc, mul_inv_cancel, mul_one, hAdef]
    exact (hmemA b').mpr hb'T
  have hSA : S ≤ Subgroup.normalizer (A : Set (E (m + 2))) := by
    rw [hSdef, Subgroup.closure_le]
    intro g hg'
    rw [hAdef]
    apply mem_normalizer_closure (gensE (m + 2) SpinNative.pairsA8) g
    · intro a ha'
      rw [← hAdef]
      exact hconj g hg' a ha'
    · intro a ha'
      rw [← hAdef]
      exact hconj g⁻¹ (hinvS g hg') a ha'
  have hidx : ¬ 2 ∣ S.index := by
    have h1 := S.card_mul_index
    rw [hScard, hk] at h1
    have h2 : S.index = k := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]; exact hodd
  obtain ⟨hP, hPS⟩ : ∃ P : Sylow 2 (E (m + 2)), (P : Subgroup (E (m + 2))) = S :=
    ⟨(IsPGroup.of_card hScard).toSylow hidx, rfl⟩
  have hA2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha'
    rw [hAdef] at ha'
    have haT := (hmemA a).mp ha'
    have hmem : thetaM hrel a ∈ CoverAltGroup.treeTab (SpinM.gensM (Gm Γ) SpinNative.pairsA8)
        SpinNative.treeA8 := by
      rw [← hmapA]; exact List.mem_map_of_mem haT
    have key : thetaM hrel (a * a) = thetaM hrel 1 := by
      rw [map_mul, map_one]; exact hh _ hmem
    exact hinj key
  have hA8 : 8 ≤ Nat.card A := by rw [hAcard]
  exact sylowFourJoined_of_normal_elemAbelian hP (A := A) (by rw [hPS]; exact hSA) hA2 hA8

end NormalCase

section KleinCase

variable {N : ℕ} {Γ : ℕ → Matrix (Fin N) (Fin N) ℚ}

theorem commute_closure_of_gens {G : Type*} [Group G] (S T : Set G)
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure T, x * y = y * x := by
  have hs : ∀ s ∈ S, ∀ y ∈ Subgroup.closure T, s * y = y * s := by
    intro s hs y hy
    induction hy using Subgroup.closure_induction with
    | mem t ht => exact h s hs t ht
    | one => simp
    | mul y₁ y₂ _ _ ih₁ ih₂ => rw [← mul_assoc, ih₁, mul_assoc, ih₂, mul_assoc]
    | inv y₁ _ ih => exact ((show Commute s y₁ from ih).inv_right).eq
  intro x hx y hy
  induction hx using Subgroup.closure_induction with
  | mem s hs' => exact hs s hs' y hy
  | one => simp
  | mul x₁ x₂ _ _ ih₁ ih₂ => rw [mul_assoc, ih₂, ← mul_assoc, ih₁, mul_assoc]
  | inv x₁ _ ih => exact ((show Commute x₁ y from ih).inv_left).eq

theorem le_centralizer_closure {G : Type*} [Group G] (S T : Set G)
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (commute_closure_of_gens S T h x hx y hy).symm

theorem exists_getD_of_mem {α : Type*} [Inhabited α] (l : List α) {x : α} (hx : x ∈ l) :
    ∃ i, i < l.length ∧ l.getD i default = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact ⟨i, hi, by simp [List.getD_eq_getElem?_getD, hi]⟩

end KleinCase

theorem getD_lt_of_ne {M : Type*} [One M] {l : List M} {i : ℕ} (h : l.getD i 1 ≠ 1) :
    i < l.length := by
  by_contra hc
  exact h (List.getD_eq_default l 1 (not_lt.mp hc))

theorem getD_mem_of_lt {M : Type*} [One M] {l : List M} {i : ℕ} (h : i < l.length) :
    l.getD i 1 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem exists_lt_getD {M : Type*} [One M] {l : List M} {x : M} (hx : x ∈ l) :
    ∃ i, i < l.length ∧ l.getD i 1 = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi]⟩

theorem getD_zero_treeAux {G : Type*} [Mul G] [One G] (gs : List G) :
    ∀ (acc : List G) (tr : List (ℕ × ℕ)), acc.head? = some 1 →
      (CoverAltGroup.treeAux gs acc tr).getD 0 1 = 1 := by
  intro acc tr
  induction tr generalizing acc with
  | nil =>
    intro h
    cases acc with
    | nil => simp at h
    | cons a acc' =>
      simp only [List.head?_cons, Option.some.injEq] at h; subst h
      simp [CoverAltGroup.treeAux]
  | cons pg tr ih =>
    intro h
    obtain ⟨p, g⟩ := pg
    apply ih
    cases acc with
    | nil => simp at h
    | cons a acc' => simp only [List.head?_cons, Option.some.injEq] at h; subst h; simp

theorem getD_zero_treeTab {G : Type*} [Mul G] [One G] (gs : List G) (tr : List (ℕ × ℕ)) :
    (CoverAltGroup.treeTab gs tr).getD 0 1 = 1 :=
  getD_zero_treeAux gs [1] tr (by simp)

theorem comm_of_thetaM {G : Type} [Group G] {H : Type} [Monoid H] (f : G →* H)
    (hf : Function.Injective f) {x y : G} (h : f x * f y = f y * f x) : x * y = y * x :=
  hf (by rw [map_mul, map_mul]; exact h)

theorem le_centralizer_pair {G : Type} [Group G] {a b c d : G}
    (h1 : a * c = c * a) (h2 : a * d = d * a) (h3 : b * c = c * b) (h4 : b * d = d * b) :
    Subgroup.closure ({a, b} : Set G) ≤
      Subgroup.centralizer (Subgroup.closure ({c, d} : Set G) : Set G) := by
  refine le_centralizer_closure _ _ ?_
  intro s hs t ht
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · exact h1
  · exact h2
  · exact h3
  · exact h4

theorem reflTransGen_chain {G : Type} [Group G] (L : ℕ) (K : ℕ → Subgroup G) (par : ℕ → ℕ)
    (hedge : ∀ idx, idx < L → idx ≠ 0 → par idx < idx ∧ CommFourAdj G (K idx) (K (par idx))) :
    ∀ idx, idx < L → Relation.ReflTransGen (CommFourAdj G) (K idx) (K 0) := by
  intro idx
  induction idx using Nat.strong_induction_on with
  | _ idx ih =>
    intro hidx
    by_cases h0 : idx = 0
    · subst h0
      exact Relation.ReflTransGen.refl
    · obtain ⟨hpar, hadj⟩ := hedge idx hidx h0
      exact Relation.ReflTransGen.head hadj (ih (par idx) hpar (lt_trans hpar hidx))

section KleinMain2

variable {N : ℕ}

theorem klein_joined {G : Type} [Group G] [Finite G] (S0 : Subgroup G) (T : List G)
    (f : G →* Matrix (Fin N) (Fin N) ℚ) (hf : Function.Injective f)
    (hmemS : ∀ x : G, x ∈ S0 ↔ x ∈ T) (hTE0 : T.getD 0 1 = 1)
    (TM : List (Matrix (Fin N) (Fin N) ℚ)) (hTM : T.map f = TM)
    (hK1 : ∀ idx, idx < SpinNative.kleinS10.length →
      (TM.getD (klP idx) 1 * TM.getD (klP idx) 1 = 1 ∧
        TM.getD (klQ idx) 1 * TM.getD (klQ idx) 1 = 1 ∧
        TM.getD (klP idx) 1 * TM.getD (klQ idx) 1 = TM.getD (klQ idx) 1 * TM.getD (klP idx) 1 ∧
        TM.getD (klP idx) 1 ≠ 1 ∧ TM.getD (klQ idx) 1 ≠ 1 ∧
        TM.getD (klP idx) 1 ≠ TM.getD (klQ idx) 1 ∧
        TM.getD (klR idx) 1 = TM.getD (klP idx) 1 * TM.getD (klQ idx) 1))
    (hK2 : ∀ idx, idx < SpinNative.kleinS10.length → idx = 0 ∨
      (klPar idx < idx ∧
        TM.getD (klP idx) 1 * TM.getD (klP (klPar idx)) 1 =
          TM.getD (klP (klPar idx)) 1 * TM.getD (klP idx) 1 ∧
        TM.getD (klP idx) 1 * TM.getD (klQ (klPar idx)) 1 =
          TM.getD (klQ (klPar idx)) 1 * TM.getD (klP idx) 1 ∧
        TM.getD (klQ idx) 1 * TM.getD (klP (klPar idx)) 1 =
          TM.getD (klP (klPar idx)) 1 * TM.getD (klQ idx) 1 ∧
        TM.getD (klQ idx) 1 * TM.getD (klQ (klPar idx)) 1 =
          TM.getD (klQ (klPar idx)) 1 * TM.getD (klQ idx) 1))
    (hK3 : ∀ i, i < TM.length →
      ((TM.getD i 1 * TM.getD i 1 = 1 ∧ TM.getD i 1 ≠ 1) ↔ i ∈ SpinNative.invS10))
    (hK4 : ∀ i ∈ SpinNative.invS10, ∀ j ∈ SpinNative.invS10,
      i = j ∨ ¬ (TM.getD i 1 * TM.getD j 1 = TM.getD j 1 * TM.getD i 1) ∨
        ∃ k ∈ SpinNative.kleinS10, i ∈ [0, k.1, k.2.1, k.2.2.1] ∧ j ∈ [0, k.1, k.2.1, k.2.2.1]) :
    ∀ E F : Subgroup G, IsKleinFour E → E ≤ S0 → IsKleinFour F → F ≤ S0 →
      Relation.ReflTransGen (CommFourAdj G) E F := by
  have hxm : ∀ i, f (T.getD i 1) = TM.getD i 1 := fun i => by
    rw [← hTM, getD_map_one]
  have hTlen : T.length = TM.length := by rw [← hTM, List.length_map]
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℕ → Subgroup G, ∀ idx, Kc idx =
      Subgroup.closure ({T.getD (klP idx) 1, T.getD (klQ idx) 1} : Set G) :=
    ⟨fun idx => Subgroup.closure ({T.getD (klP idx) 1, T.getD (klQ idx) 1} : Set G),
      fun _ => rfl⟩
  have hKlein : ∀ idx, idx < SpinNative.kleinS10.length →
      IsKleinFour (Kc idx) ∧ Nat.card (Kc idx) = 4 := by
    intro idx hidx'
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hK1 idx hidx'
    have ha2 : T.getD (klP idx) 1 * T.getD (klP idx) 1 = 1 :=
      hf (by simp only [map_mul, map_one, hxm]; exact h1)
    have hb2 : T.getD (klQ idx) 1 * T.getD (klQ idx) 1 = 1 :=
      hf (by simp only [map_mul, map_one, hxm]; exact h2)
    have hab : T.getD (klP idx) 1 * T.getD (klQ idx) 1 =
        T.getD (klQ idx) 1 * T.getD (klP idx) 1 :=
      hf (by simp only [map_mul, hxm]; exact h3)
    have ha1 : T.getD (klP idx) 1 ≠ 1 := fun h => h4 (by rw [← hxm, h, map_one])
    have hb1 : T.getD (klQ idx) 1 ≠ 1 := fun h => h5 (by rw [← hxm, h, map_one])
    have hne : T.getD (klP idx) 1 ≠ T.getD (klQ idx) 1 :=
      fun h => h6 (by rw [← hxm, ← hxm, h])
    rw [hKc idx]
    exact isKleinFour_closure_pair ha2 hb2 hab ha1 hb1 hne
  have hreq : ∀ idx, idx < SpinNative.kleinS10.length →
      T.getD (klR idx) 1 = T.getD (klP idx) 1 * T.getD (klQ idx) 1 := by
    intro idx hidx'
    obtain ⟨-, -, -, -, -, -, h7⟩ := hK1 idx hidx'
    exact hf (by rw [map_mul, hxm, hxm, hxm, h7])
  have hmemGen : ∀ idx, idx < SpinNative.kleinS10.length → ∀ (x : G) (t : ℕ),
      T.getD t 1 = x → (t = 0 ∨ t = klP idx ∨ t = klQ idx ∨ t = klR idx) → x ∈ Kc idx := by
    intro idx hidx' x t hx ht
    rw [hKc idx]
    rcases ht with rfl | rfl | rfl | rfl
    · rw [← hx, hTE0]; exact Subgroup.one_mem _
    · rw [← hx]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    · rw [← hx]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · rw [← hx, hreq idx hidx']
      exact mul_mem (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hcover : ∀ E' : Subgroup G, IsKleinFour E' → E' ≤ S0 →
      ∃ idx, idx < SpinNative.kleinS10.length ∧ E' = Kc idx := by
    intro E' hE' hle
    obtain ⟨a, b, ha, hb, ha2, hb2, hab, ha1, hb1, hne, hEq⟩ :=
      exists_pair_of_isKleinFour E' hE'
    obtain ⟨i, hi, hia⟩ := exists_lt_getD ((hmemS a).mp (hle ha))
    obtain ⟨j, hj, hjb⟩ := exists_lt_getD ((hmemS b).mp (hle hb))
    have hiL : i < TM.length := hTlen ▸ hi
    have hjL : j < TM.length := hTlen ▸ hj
    have hai : TM.getD i 1 * TM.getD i 1 = 1 ∧ TM.getD i 1 ≠ 1 := by
      rw [← hxm i, hia]
      exact ⟨by rw [← map_mul, ha2, map_one], fun h => ha1 (hf (by rw [h, map_one]))⟩
    have hbj : TM.getD j 1 * TM.getD j 1 = 1 ∧ TM.getD j 1 ≠ 1 := by
      rw [← hxm j, hjb]
      exact ⟨by rw [← map_mul, hb2, map_one], fun h => hb1 (hf (by rw [h, map_one]))⟩
    have hiI : i ∈ SpinNative.invS10 := (hK3 i hiL).mp hai
    have hjI : j ∈ SpinNative.invS10 := (hK3 j hjL).mp hbj
    have hij : i ≠ j := fun h => hne (by rw [← hia, ← hjb, h])
    have hcomm : TM.getD i 1 * TM.getD j 1 = TM.getD j 1 * TM.getD i 1 := by
      rw [← hxm i, ← hxm j, hia, hjb, ← map_mul, ← map_mul, hab]
    rcases hK4 i hiI j hjI with h | h | ⟨k, hk, hik, hjk⟩
    · exact absurd h hij
    · exact absurd hcomm h
    · obtain ⟨idx, hidx, hkidx⟩ := List.mem_iff_getElem.mp hk
      have hk1 : klP idx = k.1 := by
        rw [← hkidx]; simp only [klP, List.getD_eq_getElem _ _ hidx]
      have hk2 : klQ idx = k.2.1 := by
        rw [← hkidx]; simp only [klQ, List.getD_eq_getElem _ _ hidx]
      have hk3 : klR idx = k.2.2.1 := by
        rw [← hkidx]; simp only [klR, List.getD_eq_getElem _ _ hidx]
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hik hjk
      have hi4 : i = 0 ∨ i = klP idx ∨ i = klQ idx ∨ i = klR idx := by
        rcases hik with h0 | h0 | h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Or.inl (h0.trans hk1.symm))
        · exact Or.inr (Or.inr (Or.inl (h0.trans hk2.symm)))
        · exact Or.inr (Or.inr (Or.inr (h0.trans hk3.symm)))
      have hj4 : j = 0 ∨ j = klP idx ∨ j = klQ idx ∨ j = klR idx := by
        rcases hjk with h0 | h0 | h0 | h0
        · exact Or.inl h0
        · exact Or.inr (Or.inl (h0.trans hk1.symm))
        · exact Or.inr (Or.inr (Or.inl (h0.trans hk2.symm)))
        · exact Or.inr (Or.inr (Or.inr (h0.trans hk3.symm)))
      have hsub : Subgroup.closure ({a, b} : Set G) ≤ Kc idx := by
        rw [Subgroup.closure_le]
        intro x hx
        rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with h | h
        · rw [h]; exact hmemGen idx hidx a i hia hi4
        · rw [h]; exact hmemGen idx hidx b j hjb hj4
      refine ⟨idx, hidx, ?_⟩
      have hsubE : E' ≤ Kc idx := by rw [hEq]; exact hsub
      exact Subgroup.eq_of_le_of_card_ge hsubE
        ((hKlein idx hidx).2.trans hE'.card_four.symm).le
  have hedge : ∀ idx, idx < SpinNative.kleinS10.length → idx ≠ 0 →
      klPar idx < idx ∧ CommFourAdj G (Kc idx) (Kc (klPar idx)) := by
    intro idx hidx h0
    rcases hK2 idx hidx with h | ⟨hpar, c1, c2, c3, c4⟩
    · exact absurd h h0
    · refine ⟨hpar, (hKlein idx hidx).1, (hKlein _ (lt_trans hpar hidx)).1, ?_⟩
      rw [hKc idx, hKc (klPar idx)]
      exact le_centralizer_pair
        (comm_of_thetaM f hf (by rw [hxm, hxm]; exact c1))
        (comm_of_thetaM f hf (by rw [hxm, hxm]; exact c2))
        (comm_of_thetaM f hf (by rw [hxm, hxm]; exact c3))
        (comm_of_thetaM f hf (by rw [hxm, hxm]; exact c4))
  have hchain : ∀ idx, idx < SpinNative.kleinS10.length →
      Relation.ReflTransGen (CommFourAdj G) (Kc idx) (Kc 0) :=
    reflTransGen_chain _ Kc klPar hedge
  intro E' F' hE' hE'S hF' hF'S
  obtain ⟨i, hi, rfl⟩ := hcover E' hE' hE'S
  obtain ⟨j, hj, rfl⟩ := hcover F' hF' hF'S
  exact (hchain i hi).trans (reflTransGen_commFourAdj_symm (hchain j hj))

theorem sylowFourJoined_klein (m : ℕ) (hm : 8 ≤ m) (hN : 0 < N) (Γ : ℕ → SpinNative.Mat N)
    (hC : SpinNative.kleinCheck Γ (m + 2) = true)
    (k : ℕ) (hk : Nat.card (E (m + 2)) = 2 ^ 8 * k) (hodd : ¬ 2 ∣ k) :
    SylowFourJoined (E (m + 2)) := by
  haveI := finite_E (by omega : 6 ≤ m)
  obtain ⟨hrel, hps, hnd, hcl, hlen, hK1, hK2, hK3, hK4⟩ := kleinCheck_spec hC
  have hinj : Function.Injective (thetaM (n := m + 2) hrel) :=
    thetaM_injective_of_thetaE (thetaE_injective (by omega) hrel hN)
  obtain ⟨-, hmapS, hmemS, hcardS⟩ := closure_of_check hrel hinj (ps := SpinNative.pairsS10)
    (tr := SpinNative.treeS10) hps hnd hcl
  obtain ⟨TM, hTM⟩ : ∃ T : List (Matrix (Fin N) (Fin N) ℚ), T = klTab Γ := ⟨_, rfl⟩
  rw [← hTM] at hK1 hK2 hK3 hK4 hlen
  obtain ⟨TE, hTE⟩ : ∃ T : List (E (m + 2)),
      T = CoverAltGroup.treeTab (gensE (m + 2) SpinNative.pairsS10) SpinNative.treeS10 :=
    ⟨_, rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S : Subgroup (E (m + 2)),
      S = Subgroup.closure {g | g ∈ gensE (m + 2) SpinNative.pairsS10} := ⟨_, rfl⟩
  have hmapS' : TE.map (thetaM hrel) = TM := by rw [hTE, hTM]; exact hmapS
  have hcardS' : Nat.card (Subgroup.closure {g | g ∈ gensE (m + 2) SpinNative.pairsS10}) =
      TM.length := by
    rw [hTM]; exact hcardS
  have hmemS' : ∀ x : E (m + 2), x ∈ S0 ↔ x ∈ TE := fun x => by
    rw [hS0, hTE]; exact hmemS x
  have hTE0 : TE.getD 0 1 = 1 := by rw [hTE]; exact getD_zero_treeTab _ _
  have hS0card : Nat.card S0 = 2 ^ 8 := by rw [hS0, hcardS', hlen]; norm_num
  have hidx : ¬ 2 ∣ S0.index := by
    have h1 := S0.card_mul_index
    rw [hS0card, hk] at h1
    have h2 : S0.index = k := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]; exact hodd
  obtain ⟨hP, hPS⟩ : ∃ P : Sylow 2 (E (m + 2)), (P : Subgroup (E (m + 2))) = S0 :=
    ⟨(IsPGroup.of_card hS0card).toSylow hidx, rfl⟩
  refine sylowFourJoined_of_sylow hP ?_
  intro E F hE hES hF hFS
  rw [hPS] at hES hFS
  exact klein_joined S0 TE (thetaM hrel) hinj hmemS' hTE0 TM hmapS' hK1 hK2 hK3 hK4 E F hE hES
    hF hFS

end KleinMain2

section Final

theorem card_center_of_cover {Q : Type} [Group Q] [Finite Q] (hQ : IsQuasisimple Q)
    (hz : center Q ≠ ⊥) (h2 : IsPGroup 2 (center Q)) {n : ℕ} (hn : 5 ≤ n)
    (eQ : Q ⧸ center Q ≃* alternatingGroup (Fin n)) : Nat.card (center Q) = 2 := by
  haveI : Group.IsPerfect Q := hQ.1
  let η : Q →* alternatingGroup (Fin n) := eQ.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hη : Function.Surjective η := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center Q := by
    ext x
    simp only [η, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply, map_eq_one_iff _ eQ.injective, QuotientGroup.eq_one_iff]
  have hle := alternating_perfect_central_two_kernel_order_at_most_two hn η hη
    (by rw [hker]) (by rw [hker]; exact h2)
  rw [hker] at hle
  have hgt : 1 < Nat.card (center Q) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hz
  omega

theorem card_griess_alt {n : ℕ} (hn : 8 ≤ n) :
    Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin n))) = 2 := by
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess (alternatingGroup (Fin n))).toEquiv]
  exact card_hopfMultiplier_alternatingGroup hn

theorem card_sylow_of_card_two {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 2)
    (P : Sylow 2 G) : Nat.card P = 2 := by
  have h1 := P.card_mul_index
  have h2 : ¬ 2 ∣ P.index := P.not_dvd_index
  rw [hG] at h1
  have hi : P.index ∣ 2 := Dvd.intro_left _ h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hi with h3 | h3
  · rw [h3, mul_one] at h1; exact h1
  · exact (h2 (by omega)).elim

end Final

section Main

theorem sylowFourJoined_of_cover {Q : Type} [Group Q] [Finite Q] (hquasi : IsQuasisimple Q)
    (hz : center Q ≠ ⊥) (h2 : IsPGroup 2 (center Q)) {m : ℕ} (hm : 6 ≤ m)
    (eQ : Q ⧸ center Q ≃* alternatingGroup (Fin (m + 2)))
    (hSyl : SylowFourJoined (E (m + 2))) : SylowFourJoined Q := by
  have hzQ : Nat.card (center Q) = 2 := card_center_of_cover hquasi hz h2 (by omega) eQ
  have hGr : Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_griess_alt (by omega)
  haveI : Finite (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    Nat.finite_of_card_ne_zero (by rw [hGr]; norm_num)
  haveI := finite_E hm
  obtain ⟨e⟩ := (RankThree.PerfectCover.hopf_central_cover_consequences
    (alternatingGroup (Fin (m + 2)))).2 (fun S => card_sylow_of_card_two hGr S) Q (E (m + 2))
    hquasi (isQuasisimple_E hm) hzQ (card_center_E hm) ⟨eQ⟩ (quotCenter_E hm)
  exact SylowFourJoined.of_mulEquiv e.symm hSyl

theorem sylowFourJoined_E8 (hC : SpinNative.normalCheck SpinNative.gam8 (6 + 2) = true) :
    SylowFourJoined (E (6 + 2)) := by
  have hcard : Nat.card (E (6 + 2)) = 2 ^ 7 * 315 := by
    rw [card_E (by norm_num)]; norm_num [Nat.factorial]
  exact sylowFourJoined_normal 6 (by norm_num) (by norm_num) SpinNative.gam8 hC 315 hcard
    (by norm_num)

theorem sylowFourJoined_E9 (hC : SpinNative.normalCheck SpinNative.gam9 (7 + 2) = true) :
    SylowFourJoined (E (7 + 2)) := by
  have hcard : Nat.card (E (7 + 2)) = 2 ^ 7 * 2835 := by
    rw [card_E (by norm_num)]; norm_num [Nat.factorial]
  exact sylowFourJoined_normal 7 (by norm_num) (by norm_num) SpinNative.gam9 hC 2835 hcard
    (by norm_num)

theorem sylowFourJoined_E10 (hC : SpinNative.kleinCheck SpinNative.gam10 (8 + 2) = true) :
    SylowFourJoined (E (8 + 2)) := by
  have hcard : Nat.card (E (8 + 2)) = 2 ^ 8 * 14175 := by
    rw [card_E (by norm_num)]; norm_num [Nat.factorial]
  exact sylowFourJoined_klein 8 (by norm_num) (by norm_num) SpinNative.gam10 hC 14175 hcard
    (by norm_num)

theorem sylowFourJoined_E11 (hC : SpinNative.kleinCheck SpinNative.gam11 (9 + 2) = true) :
    SylowFourJoined (E (9 + 2)) := by
  have hcard : Nat.card (E (9 + 2)) = 2 ^ 8 * 155925 := by
    rw [card_E (by norm_num)]; norm_num [Nat.factorial]
  exact sylowFourJoined_klein 9 (by norm_num) (by norm_num) SpinNative.gam11 hC 155925 hcard
    (by norm_num)

end Main

end CFSG.ComponentClassification.Sol76.Sig.GSYard02

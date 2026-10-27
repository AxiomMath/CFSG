module

public import Certificates.Certificate27754
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowBase

public section

namespace CFSG.EvenSporadicStandard.YS14

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore

theorem closure_commute_singleton {G : Type*} [Group G] {S : Set G} {τ : G}
    (h : ∀ s ∈ S, s * τ = τ * s) : ∀ x ∈ Subgroup.closure S, x * τ = τ * x := by
  have hS : S ⊆ (Subgroup.centralizer {τ} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (h s hs)
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 ((Subgroup.closure_le _).2 hS hx)

theorem closure_pairwise_comm {G : Type*} [Group G] {S : Set G}
    (h : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  intro x hx y hy
  induction hy using Subgroup.closure_induction with
  | mem s hs => exact closure_commute_singleton (τ := s) (fun t ht => h t ht s hs) x hx
  | one => simp
  | mul a b _ _ ha hb =>
    exact Commute.mul_right (show Commute x a from ha) (show Commute x b from hb)
  | inv a _ ha => exact Commute.inv_right (show Commute x a from ha)

theorem closure_sq_one {G : Type*} [Group G] {S : Set G} (hsq : ∀ s ∈ S, s * s = 1)
    (hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x) :
    ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hsq s hs
  | one => simp
  | mul a b ha hb iha ihb =>
    have hab : a * b = b * a := hc a ha b hb
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hab]
      _ = a * a * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

noncomputable def fi22WGen (k i : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22E16Arr (4 * k + i))

noncomputable def fi22WSet (k : ℕ) : Set (Equiv.Perm (Fin 3510)) :=
  {g | ∃ i < 4, g = fi22WGen k i}

theorem fi22E16_conj :
    allLt 24 (fun L => isInvA 3510 (fi22E16Arr L) (invCand 3510 (fi22E16Arr L))) = true ∧
    allLt 24 (fun L => fi22InP (fi22E16Arr L)) = true ∧
    allLt 24 (fun L => eqA 3510 (compA 3510 (fi22E16Arr L) (fi22E16Arr L)) (idA 3510)) = true ∧
    allLt 24 (fun L => eqA 3510 (compA 3510 (fi22E16Arr L) (fi22ExtArr (21 + L / 4)))
      (compA 3510 (fi22ExtArr (21 + L / 4)) (fi22E16Arr L))) = true ∧
    allLt 24 (fun L => allLt 4 fun j =>
      eqA 3510 (compA 3510 (fi22E16Arr L) (fi22E16Arr (4 * (L / 4) + j)))
        (compA 3510 (fi22E16Arr (4 * (L / 4) + j)) (fi22E16Arr L))) = true ∧
    allLt 6 (fun k => allLt 16 fun m => allLt 16 fun m' =>
      m == m' || !(eqA 3510 (fi22E16ProdA k m) (fi22E16ProdA k m'))) = true := by
  have h := Certificates.certificate27754
  unfold fi22E16Check at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rep_fi22WGen {k i : ℕ} (hL : 4 * k + i < 24) :
    Rep 3510 (fi22E16Arr (4 * k + i)) (fi22WGen k i) :=
  (rep_permOfArr (allLt_spec fi22E16_conj.1 hL)).1

theorem mem_fi22P_fi22WGen
    {k i : ℕ} (hL : 4 * k + i < 24) :
    fi22WGen k i ∈ CFSG.Monster.B.Fischer.fi22P :=
  (fi22InP_iff (rep_fi22WGen hL)).1 (allLt_spec fi22E16_conj.2.1 hL)

theorem sq_fi22WGen {k i : ℕ} (hL : 4 * k + i < 24) :
    fi22WGen k i * fi22WGen k i = 1 :=
  (eqA_iff (rep_compA (rep_fi22WGen hL) (rep_fi22WGen hL)) (rep_idA (n := 3510))).1
    (allLt_spec fi22E16_conj.2.2.1 hL)

theorem comm_fi22WGen {k i j : ℕ} (hk : k < 6) (hi : i < 4)
    (hj : j < 4) : fi22WGen k i * fi22WGen k j = fi22WGen k j * fi22WGen k i := by
  have h₁ : allLt 4 (fun j => eqA 3510 (compA 3510 (fi22E16Arr (4 * k + i))
      (fi22E16Arr (4 * ((4 * k + i) / 4) + j)))
      (compA 3510 (fi22E16Arr (4 * ((4 * k + i) / 4) + j)) (fi22E16Arr (4 * k + i)))) = true :=
    allLt_spec fi22E16_conj.2.2.2.2.1 (show 4 * k + i < 24 by omega)
  have h₂ : eqA 3510 (compA 3510 (fi22E16Arr (4 * k + i)) (fi22E16Arr (4 * k + j)))
      (compA 3510 (fi22E16Arr (4 * k + j)) (fi22E16Arr (4 * k + i))) = true := by
    have h : eqA 3510 (compA 3510 (fi22E16Arr (4 * k + i))
        (fi22E16Arr (4 * ((4 * k + i) / 4) + j)))
        (compA 3510 (fi22E16Arr (4 * ((4 * k + i) / 4) + j)) (fi22E16Arr (4 * k + i))) = true :=
      allLt_spec h₁ hj
    rwa [show 4 * ((4 * k + i) / 4) + j = 4 * k + j by omega] at h
  exact eq_of_eqA (rep_compA (rep_fi22WGen (k := k) (i := i) (by omega))
      (rep_fi22WGen (k := k) (i := j) (by omega)))
    (rep_compA (rep_fi22WGen (k := k) (i := j) (by omega))
      (rep_fi22WGen (k := k) (i := i) (by omega))) h₂

theorem comm_fi22WGen_fi22ExtRep
    {k i : ℕ} (hk : k < 6) (hi : i < 4) :
    fi22WGen k i * fi22ExtRep k = fi22ExtRep k * fi22WGen k i := by
  have h : eqA 3510 (compA 3510 (fi22E16Arr (4 * k + i)) (fi22ExtArr (21 + (4 * k + i) / 4)))
      (compA 3510 (fi22ExtArr (21 + (4 * k + i) / 4)) (fi22E16Arr (4 * k + i))) = true :=
    allLt_spec fi22E16_conj.2.2.2.1 (show 4 * k + i < 24 by omega)
  rw [show (4 * k + i) / 4 = k by omega] at h
  exact eq_of_eqA (rep_compA (rep_fi22WGen (k := k) (i := i) (by omega)) (rep_fi22ExtRep hk))
    (rep_compA (rep_fi22ExtRep hk) (rep_fi22WGen (k := k) (i := i) (by omega))) h

noncomputable def fi22WProd (k m : ℕ) : Equiv.Perm (Fin 3510) :=
  (if m.testBit 0 then fi22WGen k 0 else 1) * (if m.testBit 1 then fi22WGen k 1 else 1) *
    ((if m.testBit 2 then fi22WGen k 2 else 1) * (if m.testBit 3 then fi22WGen k 3 else 1))

theorem rep_fi22WFactor {k : ℕ} (hk : k < 6) (m i : ℕ)
    (hi : i < 4) :
    Rep 3510 (if m.testBit i then fi22E16Arr (4 * k + i) else idA 3510)
      (if m.testBit i then fi22WGen k i else 1) := by
  by_cases h : m.testBit i
  · rw [if_pos h, if_pos h]
    exact rep_fi22WGen (by omega)
  · rw [if_neg h, if_neg h]
    exact rep_idA

theorem rep_fi22WProd {k : ℕ} (hk : k < 6) (m : ℕ) :
    Rep 3510 (fi22E16ProdA k m) (fi22WProd k m) := by
  have h := rep_compA
    (rep_compA (rep_fi22WFactor hk m 0 (by norm_num)) (rep_fi22WFactor hk m 1 (by norm_num)))
    (rep_compA (rep_fi22WFactor hk m 2 (by norm_num)) (rep_fi22WFactor hk m 3 (by norm_num)))
  exact h

theorem eq_of_fi22E16ProdA {k m m' : ℕ} (hk : k < 6)
    (hm : m < 16) (hm' : m' < 16)
    (he : eqA 3510 (fi22E16ProdA k m) (fi22E16ProdA k m') = true) : m = m' := by
  have h₁ : allLt 16 (fun m => allLt 16 fun m' =>
      m == m' || !(eqA 3510 (fi22E16ProdA k m) (fi22E16ProdA k m'))) = true :=
    allLt_spec fi22E16_conj.2.2.2.2.2 hk
  have h₂ : allLt 16 (fun m' => m == m' || !(eqA 3510 (fi22E16ProdA k m) (fi22E16ProdA k m')))
      = true :=
    allLt_spec h₁ hm
  have h : (m == m' || !(eqA 3510 (fi22E16ProdA k m) (fi22E16ProdA k m'))) = true :=
    allLt_spec h₂ hm'
  rw [he] at h
  simpa using h

theorem fi22_e16_witness :
    ∀ k < 6, ∃ E : Subgroup (Equiv.Perm (Fin 3510)), E ≤ CFSG.Monster.B.Fischer.fi22P ∧
      (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      (∀ x ∈ E, x * CFSG.Sporadic.FischerOddCore.fi22ExtRep k =
        CFSG.Sporadic.FischerOddCore.fi22ExtRep k * x) ∧ 16 ≤ Nat.card E := by
  intro k hk
  have hcomm : ∀ s ∈ fi22WSet k, ∀ t ∈ fi22WSet k, s * t = t * s := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    exact comm_fi22WGen hk hi hj
  have hsq : ∀ s ∈ fi22WSet k, s * s = 1 := by
    rintro _ ⟨i, hi, rfl⟩
    exact sq_fi22WGen (by omega)
  have hτ : ∀ s ∈ fi22WSet k, s * fi22ExtRep k = fi22ExtRep k * s := by
    rintro _ ⟨i, hi, rfl⟩
    exact comm_fi22WGen_fi22ExtRep hk hi
  have hP : ∀ s ∈ fi22WSet k, s ∈ CFSG.Monster.B.Fischer.fi22P := by
    rintro _ ⟨i, hi, rfl⟩
    exact mem_fi22P_fi22WGen (by omega)
  refine ⟨Subgroup.closure (fi22WSet k), (Subgroup.closure_le _).2 hP,
    closure_sq_one hsq (closure_pairwise_comm hcomm), closure_pairwise_comm hcomm,
    closure_commute_singleton hτ, ?_⟩
  have hF : ∀ (m i : ℕ), i < 4 →
      (if m.testBit i then fi22WGen k i else 1) ∈ Subgroup.closure (fi22WSet k) := by
    intro m i hi
    split_ifs
    · exact Subgroup.subset_closure ⟨i, hi, rfl⟩
    · exact Subgroup.one_mem _
  have hmem : ∀ m : ℕ, fi22WProd k m ∈ Subgroup.closure (fi22WSet k) := by
    intro m
    unfold fi22WProd
    exact mul_mem (mul_mem (hF m 0 (by norm_num)) (hF m 1 (by norm_num)))
      (mul_mem (hF m 2 (by norm_num)) (hF m 3 (by norm_num)))
  have hinj : Function.Injective
      (fun m : Fin 16 => (⟨fi22WProd k m, hmem m⟩ : ↥(Subgroup.closure (fi22WSet k)))) := by
    intro m m' h
    have hPeq : fi22WProd k m = fi22WProd k m' := congrArg Subtype.val h
    have he : eqA 3510 (fi22E16ProdA k m) (fi22E16ProdA k m') = true :=
      (eqA_iff (rep_fi22WProd hk m) (rep_fi22WProd hk m')).2 hPeq
    exact Fin.ext (eq_of_fi22E16ProdA hk m.2 m'.2 he)
  calc 16 = Nat.card (Fin 16) := (Nat.card_fin 16).symm
    _ ≤ Nat.card ↥(Subgroup.closure (fi22WSet k)) := Nat.card_le_card_of_injective _ hinj

end CFSG.EvenSporadicStandard.YS14

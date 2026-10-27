module

public import CFSG.RankThree.Native.HSMcLAut
public import Certificates.Certificate26960

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.RankThree.Native

theorem card_subtype_enum {M : Type*} [Group M] (S : Subgroup M) {n : ℕ} (f : ℕ → M)
    (hmem : ∀ x, x ∈ S ↔ ∃ i < n, f i = x) (hcard : Nat.card S = n) (p : M → Prop) :
    Nat.card {y : S // p y.1} = Nat.card {i : Fin n // p (f i.1)} := by
  let F : Fin n → S := fun i => ⟨f i.1, (hmem _).2 ⟨i.1, i.2, rfl⟩⟩
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨i, hi, hfi⟩ := (hmem y.1).1 y.2
    exact ⟨⟨i, hi⟩, Subtype.ext hfi⟩
  have hF : Function.Bijective F :=
    hsurj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.ofBijective F hF).symm fun y => ?_)
  have h := congrArg Subtype.val ((Equiv.ofBijective F hF).apply_symm_apply y)
  simp only [Equiv.ofBijective_apply] at h
  rw [show f ((Equiv.ofBijective F hF).symm y).1 = y.1 from h]

theorem s5InP_iff_rep {a : Array ℕ} {g : Equiv.Perm (Fin 100)}
    (hr : Rep 100 a g) : s5InP a = true ↔ g ∈ hs100P := by
  rw [hs100P_eq_original]
  exact siftA_iff_mem_originalSubgroup hs100ChainArrays (by norm_num) hs100_chain_check.1 hr

theorem s5InP_iff {a : Array ℕ} (hv : validA 100 a = true) :
    s5InP a = true ↔ permOfArr 100 a ∈ hs100P :=
  s5InP_iff_rep (rep_of_validA hv)

theorem s5Out1_iff {a : Array ℕ} (hv : validA 100 a = true) :
    s5Out1 a = true ↔ permOfArr 100 a ∉ hs100P ∧ permOfArr 100 a * permOfArr 100 a = 1 := by
  have hr := rep_of_validA hv
  rw [s5Out1, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, s5InP_iff hv,
    eqA_iff (rep_compA hr hr) rep_idA]

theorem s5OutZ_iff (hz : validA 100 s5Z = true) {a : Array ℕ}
    (hv : validA 100 a = true) :
    s5OutZ a = true ↔
      permOfArr 100 a ∉ hs100P ∧ permOfArr 100 a * permOfArr 100 a = permOfArr 100 s5Z := by
  have hr := rep_of_validA hv
  rw [s5OutZ, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, s5InP_iff hv,
    eqA_iff (rep_compA hr hr) (rep_of_validA hz)]

theorem s5_sylow_spec :
    ∃ (S₀ : Subgroup (Equiv.Perm (Fin 100))) (z₀ : Equiv.Perm (Fin 100)),
      S₀ ≤ hs100R ∧ Nat.card S₀ = 1024 ∧ z₀ ∈ hs100P ∧ z₀ * z₀ = 1 ∧ z₀ ≠ 1 ∧
      (∀ x ∈ S₀, x ∈ hs100P → z₀ * x = x * z₀) ∧
      Nat.card {y : S₀ // y.1 ∉ hs100P ∧ y.1 * y.1 = 1} = 104 ∧
      Nat.card {y : S₀ // y.1 ∉ hs100P ∧ y.1 * y.1 = z₀} = 40 := by
  classical
  have h : s5SylowOK = true := Certificates.certificate26960
  simp only [s5SylowOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨henum, hsize⟩, hsift⟩, hvz⟩, hinz⟩, hnez⟩, hz2⟩, hcen⟩, hc1⟩, hcZ⟩ := h
  have hps : ∀ p ∈ s5Keys, p < 100 := by
    intro p hp
    simp only [s5Keys, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hrz : Rep 100 s5Z (permOfArr 100 s5Z) := rep_of_validA hvz
  have hzP : permOfArr 100 s5Z ∈ hs100P := (s5InP_iff hvz).1 hinz
  have hu : Rep 100 s5U hs100U := rep_hs100U
  have hne1 : permOfArr 100 s5Z ≠ 1 := by
    intro h
    have h1 : eqA 100 s5Z (idA 100) = true := (eqA_iff hrz rep_idA).2 h
    rw [h1] at hnez
    exact absurd hnez (by simp)
  refine ⟨Subgroup.closure (permsA 100 s5SGens), permOfArr 100 s5Z, ?_, hcard.trans hsize, hzP,
    (eqA_iff (rep_compA hrz hrz) rep_idA).1 hz2, hne1, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hkv := enumOK_gens_valid henum hk
    have hrk := rep_of_validA hkv
    have hk' := allLt_spec hsift hk
    simp only [Bool.or_eq_true] at hk'
    rcases hk' with h1 | h1
    · exact hs100P_le_R ((s5InP_iff hkv).1 h1)
    · have h2 : hs100U * permOfArr 100 s5SGens[k]! ∈ hs100P :=
        (s5InP_iff_rep (rep_compA hu hrk)).1 h1
      have h4 := hs100R.mul_mem (hs100R.inv_mem hs100U_mem_R) (hs100P_le_R h2)
      simpa using h4
  · intro x hx hxP
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    have hrx := rep_of_validA (hval i hi)
    have hxin : s5InP s5SCert.pts[i]! = true := (s5InP_iff (hval i hi)).2 hxP
    have hmemL : s5SCert.pts[i]! ∈ s5SCert.pts.toList := by
      rw [getElem!_pos _ i hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    have h1 := List.all_eq_true.1 hcen _ hmemL
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h1 | h1
    · rw [hxin] at h1
      exact absurd h1 (by simp)
    · exact (eqA_iff (rep_compA hrz hrx) (rep_compA hrx hrz)).1 h1
  · rw [card_subtype_enum _ (fun i => permOfArr 100 s5SCert.pts[i]!) hmem hcard
      (fun y => y ∉ hs100P ∧ y * y = 1), Nat.card_eq_fintype_card, Fintype.card_subtype, ← hc1,
      s5Cnt1]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    exact (s5Out1_iff (hval i.1 i.2)).symm
  · rw [card_subtype_enum _ (fun i => permOfArr 100 s5SCert.pts[i]!) hmem hcard
      (fun y => y ∉ hs100P ∧ y * y = permOfArr 100 s5Z), Nat.card_eq_fintype_card,
      Fintype.card_subtype, ← hcZ, s5CntZ]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    exact (s5OutZ_iff hvz (hval i.1 i.2)).symm

end CFSG.EvenSporadicStandard.HSStd

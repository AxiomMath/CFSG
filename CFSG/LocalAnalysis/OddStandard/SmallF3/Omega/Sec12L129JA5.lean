module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JG
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open

theorem sec12A5_F1 : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ * σ = 1 → σ ≠ 1 →
    (Finset.univ.filter (fun v : Fin 5 → ZMod 2 => (∑ i, v i = 0) ∧ permVec σ v = v)).card ≤ 4 := by
  decide +kernel

theorem sec12A5_F2 : ∀ σ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → Equiv.Perm.sign τ = 1 →
    σ * σ = 1 → τ * τ = 1 → σ ≠ 1 → τ ≠ 1 → σ ≠ τ → σ * τ = τ * σ →
    (Finset.univ.filter (fun v : Fin 5 → ZMod 2 =>
      (∑ i, v i = 0) ∧ permVec σ v = v ∧ permVec τ v = v)).card ≤ 2 := by
  decide +kernel

theorem sec12A5_F3 : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ * σ = 1 →
    (Finset.univ.filter (fun g : Equiv.Perm (Fin 5) =>
      Equiv.Perm.sign g = 1 ∧ g * σ = σ * g)).card = 60 ∨
    (Finset.univ.filter (fun g : Equiv.Perm (Fin 5) =>
      Equiv.Perm.sign g = 1 ∧ g * σ = σ * g)).card = 4 := by
  decide +kernel

theorem sec12A5_card : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  have h2 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    rfl
  omega

theorem sec12A5_elemAb_card_le (Q : Subgroup ↥(alternatingGroup (Fin 5)))
    (hQ : IsElemAbelian 2 Q) : Nat.card Q ≤ 4 := by
  obtain ⟨n, hn⟩ := sec12J_card_two_pow hQ
  have hdvd : 2 ^ n ∣ 60 := by
    rw [← hn, ← sec12A5_card]
    exact Subgroup.card_subgroup_dvd_card Q
  have hn2 : n ≤ 2 := sec12J_two_pow_dvd_sixty hdvd
  calc Nat.card Q = 2 ^ n := hn
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    _ = 4 := by norm_num

theorem sec12A5_cent_card (σ : ↥(alternatingGroup (Fin 5))) (hσ : σ * σ = 1) :
    Nat.card (centralizer ({σ} : Set ↥(alternatingGroup (Fin 5)))) = 60 ∨
      Nat.card (centralizer ({σ} : Set ↥(alternatingGroup (Fin 5)))) = 4 := by
  have hσ' : (σ : Equiv.Perm (Fin 5)) * (σ : Equiv.Perm (Fin 5)) = 1 := congrArg Subtype.val hσ
  have hsign : Equiv.Perm.sign (σ : Equiv.Perm (Fin 5)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp σ.2
  let e : ↥(centralizer ({σ} : Set ↥(alternatingGroup (Fin 5)))) ≃
      {g : Equiv.Perm (Fin 5) // Equiv.Perm.sign g = 1 ∧
        g * (σ : Equiv.Perm (Fin 5)) = (σ : Equiv.Perm (Fin 5)) * g} :=
    { toFun := fun g => ⟨((g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)),
        Equiv.Perm.mem_alternatingGroup.mp (g : ↥(alternatingGroup (Fin 5))).2,
        (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp g.2 σ rfl)).symm⟩
      invFun := fun x => ⟨⟨x.1, Equiv.Perm.mem_alternatingGroup.mpr x.2.1⟩,
        Subgroup.mem_centralizer_iff.mpr (fun h hh => by
          rw [Set.mem_singleton_iff] at hh
          subst hh
          exact Subtype.ext x.2.2.symm)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h3 := sec12A5_F3 σ hsign hσ'
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h3

private lemma sec12A5_card_filter {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] :
    Nat.card {a // p a} = (Finset.univ.filter p).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma sec12A5_inv_facts {Q : Subgroup ↥(alternatingGroup (Fin 5))}
    (hQ : IsElemAbelian 2 Q) (a : ↥Q) (ha : a ≠ 1) :
    Equiv.Perm.sign (((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))) = 1 ∧
    ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
      ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = 1 ∧
    ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) ≠ 1 := by
  refine ⟨Equiv.Perm.mem_alternatingGroup.mp (a : ↥(alternatingGroup (Fin 5))).2, ?_, ?_⟩
  · have h := hQ.2 (a : ↥(alternatingGroup (Fin 5))) a.2
    rw [pow_two] at h
    exact congrArg Subtype.val h
  · intro h
    exact ha (Subtype.ext (Subtype.ext h))

theorem sec12A5_fix_le (Q : Subgroup ↥(alternatingGroup (Fin 5))) (hQ : IsElemAbelian 2 Q)
    (hne : Q ≠ ⊥) :
    Nat.card Q * Nat.card {v : Fin 5 → ZMod 2 //
      IsEvenVec v ∧ ∀ σ ∈ Q, permVec (σ : Equiv.Perm (Fin 5)) v = v} ≤ 8 := by
  have hQ4 := sec12A5_elemAb_card_le Q hQ
  obtain ⟨n, hn⟩ := sec12J_card_two_pow hQ
  have hQ1 : Nat.card Q ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq Q h)
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨hsa, hsqa, hna⟩ := sec12A5_inv_facts hQ a ha
  have hcard : Nat.card Q = 2 ∨ Nat.card Q = 4 := by
    have hn2 : n ≤ 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
      omega
    interval_cases n <;> simp_all
  rcases hcard with h2 | h4
  · have hle : Nat.card {v : Fin 5 → ZMod 2 //
        IsEvenVec v ∧ ∀ σ ∈ Q, permVec (σ : Equiv.Perm (Fin 5)) v = v} ≤
        (Finset.univ.filter (fun v : Fin 5 → ZMod 2 =>
          (∑ i, v i = 0) ∧ permVec ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) v =
            v)).card := by
      rw [← sec12A5_card_filter]
      exact sec12J_card_subtype_le (fun v hv => ⟨hv.1, hv.2 a a.2⟩)
    have h1 := sec12A5_F1 _ hsa hsqa hna
    rw [h2]
    omega
  · obtain ⟨b, hb1, hba⟩ : ∃ b : ↥Q, b ≠ 1 ∧ b ≠ a := by
      by_contra hcon
      push Not at hcon
      classical
      haveI : Fintype ↥Q := Fintype.ofFinite _
      have hsub : (Finset.univ : Finset ↥Q) ⊆ {1, a} := by
        intro x _
        by_cases hx1 : x = 1
        · simp [hx1]
        · simp [hcon x hx1]
      have h1 := Finset.card_le_card hsub
      have h2 : ({1, a} : Finset ↥Q).card ≤ 2 := Finset.card_le_two
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
      omega
    obtain ⟨hsb, hsqb, hnb⟩ := sec12A5_inv_facts hQ b hb1
    have hab : ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) ≠
        ((b : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) := by
      intro h
      exact hba (Subtype.ext (Subtype.ext h.symm))
    have hcomm : ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
        ((b : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        ((b : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) *
        ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) :=
      congrArg Subtype.val (CFSG.Open.IsElemAbelian.comm hQ a.2 b.2)
    have hle : Nat.card {v : Fin 5 → ZMod 2 //
        IsEvenVec v ∧ ∀ σ ∈ Q, permVec (σ : Equiv.Perm (Fin 5)) v = v} ≤
        (Finset.univ.filter (fun v : Fin 5 → ZMod 2 =>
          (∑ i, v i = 0) ∧
            permVec ((a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) v = v ∧
            permVec ((b : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) v = v)).card := by
      rw [← sec12A5_card_filter]
      exact sec12J_card_subtype_le (fun v hv => ⟨hv.1, hv.2 a a.2, hv.2 b b.2⟩)
    have h1 := sec12A5_F2 _ _ hsa hsb hsqa hsqb hna hnb hab hcomm
    rw [h4]
    omega

end CFSG.OddStandard.SmallF3.Omega

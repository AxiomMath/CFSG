module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Fischer.Classification.Uniqueness.Star

import CFSG.Fischer.Classification.PartIII.Symp.SymCount
import CFSG.Fischer.Classification.Uniqueness.Triple
import CFSG.Fischer.Classification.Recognition.CaseSym
import CFSG.Fischer.Classification.Orthogonal2.Local

public section

namespace CFSG.Fischer.Classification.SymPair

open CFSG.Blueprint.Fischer CFSG.Fischer Equiv Equiv.Perm
open CFSG.Fischer.Classification.LocalSymp (ne_of_commute_swap swap_ne_swap swap_mul_swap_comm)

variable {n : ℕ}

private theorem exists_ne_four (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ r : Fin n, r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ d := by
  classical
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, d} : Finset (Fin n))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_four (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
  exact ⟨r, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2⟩

private theorem exists_swap_swap_of_not_commute {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hne : swap a b * swap c d ≠ swap c d * swap a b) :
    ∃ u v w : Fin n, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧ swap a b = swap u v ∧ swap c d = swap v w := by
  by_cases hca : c = a
  · subst hca
    refine ⟨b, c, d, hab.symm, hcd, fun hbd => hne ?_, swap_comm _ _, rfl⟩
    rw [← hbd]
  by_cases hcb : c = b
  · subst hcb
    refine ⟨a, c, d, hab, hcd, fun had => hne ?_, rfl, rfl⟩
    rw [← had, swap_comm c a]
  by_cases hda : d = a
  · subst hda
    refine ⟨b, d, c, hab.symm, hcd.symm, fun hbc => hne ?_, swap_comm _ _, swap_comm _ _⟩
    rw [← hbc, swap_comm b d]
  by_cases hdb : d = b
  · subst hdb
    refine ⟨a, d, c, hab, hcd.symm, fun hac => hne ?_, rfl, swap_comm _ _⟩
    rw [← hac]
  exact absurd (swap_mul_swap_comm (Ne.symm hca) (Ne.symm hda) (Ne.symm hcb) (Ne.symm hdb)) hne

theorem tripleProperty_isSwap (hn : 5 ≤ n) : TripleProperty {σ : Perm (Fin n) | σ.IsSwap} := by
  rintro e x ⟨a₀, b₀, hab₀, rfl⟩ ⟨c₀, d₀, hcd₀, rfl⟩ hne y ⟨⟨p, q, hpq, rfl⟩, hsub⟩
  obtain ⟨a, b, c, hab, hbc, hac, he, hx⟩ := exists_swap_swap_of_not_commute hab₀ hcd₀ hne
  rw [he, hx] at hsub ⊢
  have hmu : ∀ u r : Fin n, u ≠ r → u ≠ a → u ≠ b → u ≠ c → r ≠ a → r ≠ b → r ≠ c →
      swap u r ∈ muSet {σ : Perm (Fin n) | σ.IsSwap} (swap a b) (swap b c) :=
    fun u r hur hua hub huc hra hrb hrc =>
      ⟨⟨⟨u, r, hur, rfl⟩, swap_ne_swap hur hua hub, swap_mul_swap_comm hua hub hra hrb⟩,
        ⟨⟨u, r, hur, rfl⟩, swap_ne_swap hur hub huc, swap_mul_swap_comm hub huc hrb hrc⟩⟩
  have hmem : ∀ u v : Fin n, u ≠ v → swap u v = swap p q → u = a ∨ u = b ∨ u = c := by
    intro u v huv huvy
    by_contra hu
    push Not at hu
    obtain ⟨hua, hub, huc⟩ := hu
    by_cases hv : v = a ∨ v = b ∨ v = c
    · obtain ⟨r, hra, hrb, hrc, hru⟩ := exists_ne_four hn a b c u
      obtain ⟨-, hne', hcomm'⟩ := hsub (hmu u r (Ne.symm hru) hua hub huc hra hrb hrc)
      rw [← huvy] at hne' hcomm'
      exact (ne_of_commute_swap huv (Ne.symm hru) hne' hcomm').1 rfl
    · push Not at hv
      obtain ⟨hva, hvb, hvc⟩ := hv
      obtain ⟨-, hne', -⟩ := hsub (hmu u v huv hua hub huc hva hvb hvc)
      exact hne' huvy
  have hp := hmem p q hpq rfl
  have hq := hmem q p hpq.symm (swap_comm q p)
  have h3 : swap a b * swap b c * swap a b = swap a c := by
    rw [swap_comm a b, swap_comm b c, swap_mul_swap_mul_swap hbc.symm hac.symm]
  rw [h3]
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hpq
    | simp [Set.mem_insert_iff, swap_comm]

theorem center_perm_eq_bot {Ω : Type*} [DecidableEq Ω] [Finite Ω] (h : 3 ≤ Nat.card Ω) :
    Subgroup.center (Perm Ω) = ⊥ := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  ext x
  by_contra hx
  rw [Perm.coe_one, id_eq] at hx
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({x, g x} : Finset Ω)) (t := Finset.univ)
    (by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact lt_of_le_of_lt Finset.card_le_two (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  have hc : g * swap x z = swap x z * g := (Subgroup.mem_center_iff.mp hg (swap x z)).symm
  rw [mul_swap_eq_swap_mul] at hc
  have he := congrArg (fun σ : Perm Ω => σ (g x)) (mul_right_cancel hc)
  simp only [swap_apply_left, swap_apply_of_ne_of_ne hx (Ne.symm hz.2)] at he
  exact hz.1 (g.injective he)

theorem localGroup_swap {a b : Fin n} (hab : a ≠ b) :
    LocalGroup {σ : Perm (Fin n) | σ.IsSwap} (swap a b) =
      (ofSubtype : Perm {x : Fin n // x ≠ a ∧ x ≠ b} →* Perm (Fin n)).range := by
  apply le_antisymm
  · rw [LocalGroup, Subgroup.closure_le]
    rintro σ ⟨⟨c, d, hcd, rfl⟩, hne, hcomm⟩
    obtain ⟨hca, hcb, hda, hdb⟩ := ne_of_commute_swap hab hcd hne hcomm
    exact ⟨swap ⟨c, hca, hcb⟩ ⟨d, hda, hdb⟩, by rw [ofSubtype_swap_eq]⟩
  · rw [MonoidHom.range_eq_map, ← closure_isSwap, MonoidHom.map_closure, LocalGroup]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨σ, ⟨u, v, huv, rfl⟩, rfl⟩
    have huv' : (u : Fin n) ≠ v := fun h => huv (Subtype.ext h)
    rw [ofSubtype_swap_eq]
    exact ⟨⟨u, v, huv', rfl⟩, swap_ne_swap huv' u.2.1 u.2.2,
      swap_mul_swap_comm u.2.1 u.2.2 v.2.1 v.2.2⟩

noncomputable def localGroupSwapEquiv {a b : Fin n} (hab : a ≠ b) :
    Perm {x : Fin n // x ≠ a ∧ x ≠ b} ≃* LocalGroup {σ : Perm (Fin n) | σ.IsSwap} (swap a b) :=
  (MonoidHom.ofInjective ofSubtype_injective).trans
    (MulEquiv.subgroupCongr (localGroup_swap hab).symm)

theorem center_localGroup_swap {a b : Fin n} (hab : a ≠ b) (hn : 5 ≤ n) :
    Subgroup.center (LocalGroup {σ : Perm (Fin n) | σ.IsSwap} (swap a b)) = ⊥ := by
  have hΩ := CFSG.Fischer.Classification.Recognition.SymO.card_compl hab
  rw [← Subgroup.map_center_eq (localGroupSwapEquiv hab), center_perm_eq_bot (by omega),
    Subgroup.map_bot]

noncomputable def localQuotientSwapEquiv {a b : Fin n} (hab : a ≠ b) (hn : 5 ≤ n) :
    LocalQuotient {σ : Perm (Fin n) | σ.IsSwap} (swap a b) ≃*
      Perm {x : Fin n // x ≠ a ∧ x ≠ b} :=
  (QuotientGroup.quotientMulEquivOfEq (center_localGroup_swap hab hn)).trans
    (QuotientGroup.quotientBot.trans (localGroupSwapEquiv hab).symm)

private theorem exists_ne_commutator_perm {Ω : Type*} [DecidableEq Ω] [Fintype Ω]
    (h : 5 ≤ Nat.card Ω) : ∃ x y : commutator (Perm Ω), x * y ≠ y * x := by
  have hcomm : commutator (Perm Ω) = alternatingGroup Ω := alternatingGroup.commutator_perm_eq h
  have hnc : ¬ IsMulCommutative (alternatingGroup Ω) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    omega
  by_contra hall
  push Not at hall
  refine hnc ⟨⟨fun x y => ?_⟩⟩
  have h := hall ⟨x, by rw [hcomm]; exact x.2⟩ ⟨y, by rw [hcomm]; exact y.2⟩
  apply Subtype.ext
  simpa using congrArg Subtype.val h

theorem localQuotient_swap_facts {a b : Fin n} (hab : a ≠ b) (hn : 7 ≤ n) :
    IsSimpleGroup (commutator (LocalQuotient {σ : Perm (Fin n) | σ.IsSwap} (swap a b))) ∧
      ∃ x y : commutator (LocalQuotient {σ : Perm (Fin n) | σ.IsSwap} (swap a b)),
        x * y ≠ y * x := by
  have hΩ := CFSG.Fischer.Classification.Recognition.SymO.card_compl hab
  have hcomm : commutator (Perm {x : Fin n // x ≠ a ∧ x ≠ b}) = alternatingGroup _ :=
    alternatingGroup.commutator_perm_eq (by omega)
  have : IsSimpleGroup (alternatingGroup {x : Fin n // x ≠ a ∧ x ≠ b}) :=
    alternatingGroup.isSimpleGroup (by omega)
  have : IsSimpleGroup (commutator (Perm {x : Fin n // x ≠ a ∧ x ≠ b})) :=
    (MulEquiv.subgroupCongr hcomm).isSimpleGroup
  let e := (localQuotientSwapEquiv hab (by omega)).symm
  exact ⟨Recognition.R3.isSimpleGroup_commutator_of_mulEquiv e,
    Orth2.exists_ne_commutator_of_mulEquiv e (exists_ne_commutator_perm (by omega))⟩

theorem sym_pair_facts {G : Type} [Group G] {D : Set G} {m : ℕ} (hm : 7 ≤ m)
    (φ : G ≃* Perm (Fin m)) (hφ : ∀ g, g ∈ D ↔ (φ g).IsSwap) :
    TripleProperty D ∧ NonabelianCommutator G ∧
      ∀ d ∈ D, IsSimpleGroup (commutator (LocalQuotient D d)) ∧
        ∃ a b : commutator (LocalQuotient D d), a * b ≠ b * a := by
  have hD : φ '' D = {σ : Perm (Fin m) | σ.IsSwap} := by
    ext σ
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hφ g).1 hg
    · intro hσ
      exact ⟨φ.symm σ, (hφ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hσ),
        MulEquiv.apply_symm_apply φ σ⟩
  refine ⟨(tripleProperty_congr φ hD).2 (tripleProperty_isSwap (by omega)), ?_, ?_⟩
  · exact Orth2.exists_ne_commutator_of_mulEquiv φ.symm
      (exists_ne_commutator_perm (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))
  · intro d hd
    obtain ⟨a, b, hab, had⟩ := (hφ d).1 hd
    let e : LocalQuotient D d ≃* LocalQuotient {σ : Perm (Fin m) | σ.IsSwap} (swap a b) :=
      localQuotientCongr φ hD had
    obtain ⟨hS, hna⟩ := localQuotient_swap_facts hab hm
    exact ⟨Recognition.R3.isSimpleGroup_commutator_of_mulEquiv e.symm,
      Orth2.exists_ne_commutator_of_mulEquiv e.symm hna⟩

end CFSG.Fischer.Classification.SymPair

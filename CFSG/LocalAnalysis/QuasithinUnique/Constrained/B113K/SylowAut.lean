module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddBasic
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Bridge

open Equiv Equiv.Perm Subgroup CFSG.QuasithinUnique.L246C127.AltBig

private theorem bk1_omega_fix {α : Type} [Fintype α] [DecidableEq α] (q : OddInv α) {e : Perm α}
    (h : ∀ x, x ≠ q.ω → e x = x ∨ e x = q.μ x) : e q.ω = q.ω := by
  by_contra hne
  obtain ⟨y, hy⟩ : ∃ y, e q.ω = y := ⟨_, rfl⟩
  have hyω : y ≠ q.ω := fun h' => hne (hy.trans h')
  rcases h y hyω with h1 | h1
  · exact hyω (e.injective (h1.trans hy.symm))
  · rcases h (q.μ y) (q.mu_ne_omega hyω) with h2 | h2
    · exact q.fpf y hyω (e.injective (h2.trans h1.symm))
    · rw [q.inv y] at h2
      exact hyω (q.mu_eq_omega_iff.1 (e.injective (h2.trans hy.symm)))

private theorem bk1_sylOddSub_mul_self {α : Type} [Fintype α] [DecidableEq α] {p : OddInv α}
    {σ : Perm α} (hσ : σ ∈ sylOddSub p) : σ * σ = 1 := by
  have hσ' := mem_sylOddSub.mp hσ
  ext z
  rw [Perm.mul_apply, Perm.one_apply]
  rcases hσ' z with h | h
  · rw [h, h]
  · rw [h]
    rcases hσ' (p.μ z) with h' | h'
    · by_cases hzω : z = p.ω
      · exact h'.trans (by rw [hzω]; exact p.fix)
      · exact absurd (σ.injective (h.trans h'.symm)).symm (p.fpf z hzω)
    · rw [h', p.inv]

theorem perm_sq_eq_one_of_commute_even {n : ℕ} (h6 : 6 ≤ n) (hev : Even n)
    {T : Subgroup ↥(alternatingGroup (Fin n))} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {σ : Perm (Fin n)} (hσ : ∀ t ∈ T, σ * (t : Perm (Fin n)) = (t : Perm (Fin n)) * σ) :
    σ * σ = 1 := by
  have hα : Even (Fintype.card (Fin n)) := by
    rw [Fintype.card_fin]
    exact hev
  obtain ⟨p, hp⟩ := exists_contained_of_sylow (α := Fin n) hα hT
  have hcomm : ∀ x ∈ (Set.univ : Set (Fin n)), ∀ y ∈ (Set.univ : Set (Fin n)),
      y ≠ x → y ≠ p.μ x → Commute σ (swap x (p.μ x) * swap y (p.μ y)) := by
    intro x _ y _ hyx hyμ
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp (hp x y hyx hyμ)
    have hteq' : (t : Perm (Fin n)) = swap x (p.μ x) * swap y (p.μ y) := hteq
    have key := hσ t ht
    rw [hteq'] at key
    exact key
  have h6' : 6 ≤ Nat.card (Set.univ : Set (Fin n)) := by
    rw [Nat.card_univ, Nat.card_fin]
    exact h6
  have hall := fix_pairs_of_commute p (W := Set.univ) (e := σ)
    (fun x _ => Set.mem_univ _) h6' hcomm
  have hmem : σ ∈ sylPairSub p := mem_sylPairSub.mpr (fun x => hall x (Set.mem_univ x))
  exact sylPairSub_mul_self hmem

theorem perm_sq_eq_one_of_commute_odd {n : ℕ} (h7 : 7 ≤ n) (hodd : Odd n)
    {T : Subgroup ↥(alternatingGroup (Fin n))} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {σ : Perm (Fin n)} (hσ : ∀ t ∈ T, σ * (t : Perm (Fin n)) = (t : Perm (Fin n)) * σ) :
    σ * σ = 1 := by
  have hα : Odd (Fintype.card (Fin n)) := by
    rw [Fintype.card_fin]
    exact hodd
  have h5 : 5 ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨p, _, hp⟩ := exists_oddInv_of_sylow (α := Fin n) hα h5 hT
  have hcomm : ∀ x ∈ ({x : Fin n | x ≠ p.ω} : Set (Fin n)),
      ∀ y ∈ ({x : Fin n | x ≠ p.ω} : Set (Fin n)), y ≠ x → y ≠ p.μ x →
        Commute σ (swap x (p.μ x) * swap y (p.μ y)) := by
    intro x hx y hy hyx hyμ
    have hx' : x ≠ p.ω := hx
    have hy' : y ≠ p.ω := hy
    obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp (hp x y hx' hy' hyx hyμ)
    have hteq' : (t : Perm (Fin n)) = swap x (p.μ x) * swap y (p.μ y) := hteq
    have key := hσ t ht
    rw [hteq'] at key
    exact key
  have hW : ∀ x ∈ ({x : Fin n | x ≠ p.ω} : Set (Fin n)),
      p.μ x ∈ ({x : Fin n | x ≠ p.ω} : Set (Fin n)) := by
    intro x hx
    exact p.mu_ne_omega hx
  have hWω : p.ω ∉ ({x : Fin n | x ≠ p.ω} : Set (Fin n)) := fun h => h rfl
  have hcard : 6 ≤ Nat.card ↥({x : Fin n | x ≠ p.ω} : Set (Fin n)) := by
    have hset : ({x : Fin n | x ≠ p.ω} : Set (Fin n)) = Set.univ \ {p.ω} := by
      ext x
      simp
    rw [Nat.card_coe_set_eq, hset, Set.ncard_diff_singleton_of_mem (Set.mem_univ p.ω),
      Set.ncard_univ, Nat.card_fin]
    omega
  have hfix := fix_pairs_of_commute_odd p (W := {x : Fin n | x ≠ p.ω}) (e := σ)
    hW hWω hcard hcomm
  have hall : ∀ x : Fin n, σ x = x ∨ σ x = p.μ x := by
    intro x
    by_cases hx : x = p.ω
    · left
      rw [hx]
      exact bk1_omega_fix p (fun z hz => hfix z hz)
    · exact hfix x hx
  have hmem : σ ∈ sylOddSub p := mem_sylOddSub.mpr hall
  exact bk1_sylOddSub_mul_self hmem

private theorem bk2_isSylowTwoOf_top (G : Type) [Group G] [Finite G] (P : Sylow 2 G) :
    CFSG.QuasithinUnique.IsSylowTwoOf (P : Subgroup G) ⊤ := by
  unfold CFSG.QuasithinUnique.IsSylowTwoOf
  refine ⟨le_top, P.isPGroup', ?_⟩
  have h1 : ((P : Subgroup G).subgroupOf ⊤).index = (P : Subgroup G).index :=
    Subgroup.relIndex_top_right (P : Subgroup G)
  rw [h1]
  exact Sylow.not_dvd_index P

private theorem bk2_sq_eq_one {n : ℕ} (hn : 7 ≤ n)
    {T : Subgroup ↥(alternatingGroup (Fin n))} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    {σ : Perm (Fin n)} (hσ : ∀ t ∈ T, σ * (t : Perm (Fin n)) = (t : Perm (Fin n)) * σ) :
    σ * σ = 1 := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact perm_sq_eq_one_of_commute_even (by omega) hev hT hσ
  · exact perm_sq_eq_one_of_commute_odd hn hodd hT hσ

private theorem bk2_mulAut_mul_self {n : ℕ} (α : MulAut ↥(alternatingGroup (Fin n)))
    (σ : Perm (Fin n))
    (hσ : ∀ g : ↥(alternatingGroup (Fin n)), (α g : Perm (Fin n)) = σ * (g : Perm (Fin n)) * σ⁻¹)
    (hσσ : σ * σ = 1) : α * α = 1 := by
  have hinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσσ
  refine MulEquiv.ext fun g => ?_
  show α (α g) = g
  apply Subtype.ext
  rw [hσ (α g), hσ g, hinv]
  have h2 : σ * (σ * (g : Perm (Fin n)) * σ) * σ = (σ * σ) * (g : Perm (Fin n)) * (σ * σ) := by
    group
  rw [h2, hσσ]
  simp

theorem sylowAutTrivial_alt_ge_seven {n : ℕ} (hn : 7 ≤ n) :
    SylowAutTrivial ↥(alternatingGroup (Fin n)) := by
  intro P α hodd hfix
  obtain ⟨σ, hσ⟩ :=
    CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le (Or.inr hn) α
  have hcomm : ∀ t ∈ (P : Subgroup ↥(alternatingGroup (Fin n))),
      σ * (t : Perm (Fin n)) = (t : Perm (Fin n)) * σ := by
    intro t ht
    have h1 : (t : Perm (Fin n)) = σ * (t : Perm (Fin n)) * σ⁻¹ := by
      rw [← hσ t, hfix t ht]
    calc σ * (t : Perm (Fin n)) = σ * (t : Perm (Fin n)) * σ⁻¹ * σ := by group
      _ = (t : Perm (Fin n)) * σ := by rw [← h1]
  have hT := bk2_isSylowTwoOf_top ↥(alternatingGroup (Fin n)) P
  have hσσ : σ * σ = 1 := bk2_sq_eq_one hn hT hcomm
  have hsq : α * α = 1 := bk2_mulAut_mul_self α σ hσ hσσ
  have hdvd : orderOf α ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h2] at hodd
    obtain ⟨k, hk⟩ := hodd
    omega

end CFSG.QuasithinUnique.Bridge

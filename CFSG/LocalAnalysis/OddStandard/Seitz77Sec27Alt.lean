module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27HaradaLocal
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup Equiv Equiv.Perm CFSG.Blueprint

private lemma eq_top_or_eq_alt (n : ℕ) (hn : 2 ≤ n) (N' : Subgroup (Equiv.Perm (Fin n)))
    (hA : alternatingGroup (Fin n) ≤ N') :
    N' = ⊤ ∨ N' = alternatingGroup (Fin n) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h1 : N'.index ∣ (alternatingGroup (Fin n)).index := Subgroup.index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at h1
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact Or.inl (Subgroup.index_eq_one.mp h)
  · exact Or.inr (eq_alternatingGroup_of_index_eq_two h)

private lemma cycleType_of_involution (n : ℕ) (τ : Equiv.Perm (Fin n)) (hτ2 : τ * τ = 1)
    (hτ1 : τ ≠ 1) :
    ∃ a : ℕ, 1 ≤ a ∧ τ.cycleType = Multiset.replicate a 2 := by
  have hord : orderOf τ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rwa [pow_two]) hτ1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := τ) (by rw [hord]; exact Nat.prime_two)
  exact ⟨m + 1, by omega, by rw [hm, hord]⟩

private lemma card_centralizer_involution (n a : ℕ) (τ : Equiv.Perm (Fin n)) (ha : 1 ≤ a)
    (h : τ.cycleType = Multiset.replicate a 2) :
    Nat.card ↥(centralizer ({τ} : Set (Equiv.Perm (Fin n)))) =
      (n - 2 * a).factorial * 2 ^ a * a.factorial := by
  have hfin : (Multiset.replicate a 2).toFinset = {2} := by
    rw [Multiset.toFinset_replicate]
    simp [Nat.pos_iff_ne_zero.mp ha]
  rw [Equiv.Perm.nat_card_centralizer, h, Fintype.card_fin, Multiset.sum_replicate,
    Multiset.prod_replicate, hfin, Finset.prod_singleton, Multiset.count_replicate_self]
  simp [mul_comm]

private lemma two_mul_le_of_cycleType (n a : ℕ) (τ : Equiv.Perm (Fin n))
    (h : τ.cycleType = Multiset.replicate a 2) : 2 * a ≤ n := by
  have := Equiv.Perm.sum_cycleType_le τ
  rw [h, Multiset.sum_replicate, Fintype.card_fin] at this
  simpa [mul_comm] using this

private lemma even_of_mem_alternatingGroup (n a : ℕ) (τ : Equiv.Perm (Fin n))
    (h : τ.cycleType = Multiset.replicate a 2) (hτ : τ ∈ alternatingGroup (Fin n)) :
    a % 2 = 0 := by
  have h1 : sign τ = 1 := Equiv.Perm.mem_alternatingGroup.mp hτ
  rw [Equiv.Perm.sign_of_cycleType, h, Multiset.sum_replicate, Multiset.card_replicate] at h1
  have h2 := (neg_one_pow_eq_one_iff_even (by decide)).mp h1
  obtain ⟨r, hr⟩ := h2
  simp only [smul_eq_mul] at hr
  omega

private lemma exists_swap_mem_centralizer (n : ℕ) (τ : Equiv.Perm (Fin n)) (hτ2 : τ * τ = 1)
    (hτ1 : τ ≠ 1) :
    ∃ x : Equiv.Perm (Fin n),
      x ∈ centralizer ({τ} : Set (Equiv.Perm (Fin n))) ∧ sign x = -1 := by
  obtain ⟨i, hi⟩ : ∃ i, τ i ≠ i := by
    by_contra h
    exact hτ1 (Equiv.ext fun i => by_contra fun hne => h ⟨i, hne⟩)
  have hτi : τ (τ i) = i := by
    have := congrArg (fun f : Equiv.Perm (Fin n) => f i) hτ2
    simpa using this
  refine ⟨swap i (τ i), ?_, sign_swap (Ne.symm hi)⟩
  rw [mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have key := Equiv.swap_apply_apply g i (g i)
  rw [hτi, swap_comm] at key
  calc g * swap i (g i) = (g * swap i (g i) * g⁻¹) * g := by group
    _ = swap i (g i) * g := by rw [← key]

private lemma two_mul_card_inf_alternatingGroup (n : ℕ) (C : Subgroup (Equiv.Perm (Fin n)))
    (x : Equiv.Perm (Fin n)) (hx : x ∈ C) (hodd : sign x = -1) :
    2 * Nat.card ↥(alternatingGroup (Fin n) ⊓ C) = Nat.card ↥C := by
  have h1 := Subgroup.relIndex_mul_card (H := alternatingGroup (Fin n)) (K := C)
  have h2 : (alternatingGroup (Fin n)).relIndex C = 2 := by
    rw [alternatingGroup_eq_sign_ker, Subgroup.relIndex_ker]
    have htop : C.map (sign : Equiv.Perm (Fin n) →* ℤˣ) = ⊤ := by
      rw [eq_top_iff]
      intro u _
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact one_mem _
      · exact ⟨x, hx, hodd⟩
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card]
    exact Fintype.card_units_int
  rw [h2] at h1
  exact h1

private lemma le_padicValNat_two_of_dvd {d k : ℕ} (hd : d ≠ 0) (h : 2 ^ k ∣ d) :
    k ≤ padicValNat 2 d :=
  (padicValNat_dvd_iff_le hd).mp h

private lemma padicValNat_two_lt_of_not_dvd {d k : ℕ} (hd : d ≠ 0) (h : ¬ 2 ^ k ∣ d) :
    padicValNat 2 d < k := by
  by_contra hk
  exact h ((padicValNat_dvd_iff_le hd).mpr (not_lt.mp hk))

private lemma finite_check_top (n a : ℕ) (hn : 7 ≤ n) (hn' : n ≤ 10) (ha : 1 ≤ a)
    (h2a : 2 * a ≤ n) :
    ¬ (120 ∣ (n - 2 * a).factorial * 2 ^ a * a.factorial ∧
       padicValNat 2 ((n - 2 * a).factorial * 2 ^ a * a.factorial) ≤ 4 ∧
       padicValNat 2 ((n - 2 * a).factorial * 2 ^ a * a.factorial) <
         padicValNat 2 n.factorial) := by
  have ha5 : a ≤ 5 := by omega
  rintro ⟨h1, h2, h3⟩
  interval_cases n <;> interval_cases a <;>
    first
    | omega
    | exact absurd h1 (by decide)
    | exact absurd h2 (not_le.mpr (lt_of_lt_of_le (by norm_num : 4 < 5)
        (le_padicValNat_two_of_dvd (k := 5) (by decide) (by decide))))
    | exact absurd h3 (not_lt.mpr (le_trans
        (Nat.lt_succ_iff.mp (padicValNat_two_lt_of_not_dvd (k := 5) (by decide) (by decide)))
        (le_padicValNat_two_of_dvd (k := 4) (by decide) (by decide))))

private lemma finite_check_alt (n a d m : ℕ) (hn : 7 ≤ n) (hn' : n ≤ 10) (ha : 1 ≤ a)
    (h2a : 2 * a ≤ n) (hae : a % 2 = 0)
    (hd : 2 * d = (n - 2 * a).factorial * 2 ^ a * a.factorial) (hm : 2 * m = n.factorial) :
    ¬ (120 ∣ d ∧ padicValNat 2 d ≤ 4 ∧ padicValNat 2 d < padicValNat 2 m) := by
  have hd' : d = ((n - 2 * a).factorial * 2 ^ a * a.factorial) / 2 := by omega
  have hm' : m = n.factorial / 2 := by omega
  subst hd' hm'
  have ha5 : a ≤ 5 := by omega
  rintro ⟨h1, h2, h3⟩
  interval_cases n <;> interval_cases a <;>
    first
    | omega
    | exact absurd h1 (by decide)
    | exact absurd h2 (not_le.mpr (lt_of_lt_of_le (by norm_num : 4 < 5)
        (le_padicValNat_two_of_dvd (k := 5) (by decide) (by decide))))

theorem alt_comb (n : ℕ) (hn : 7 ≤ n) (hn' : n ≤ 10) (N' : Subgroup (Equiv.Perm (Fin n)))
    (hA : alternatingGroup (Fin n) ≤ N') (τ : Equiv.Perm (Fin n)) (hτ : τ ∈ N')
    (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) :
    ¬ (120 ∣ Nat.card ↥(centralizer ({τ} : Set (Equiv.Perm (Fin n))) ⊓ N') ∧
       padicValNat 2 (Nat.card ↥(centralizer ({τ} : Set (Equiv.Perm (Fin n))) ⊓ N')) ≤ 4 ∧
       padicValNat 2 (Nat.card ↥(centralizer ({τ} : Set (Equiv.Perm (Fin n))) ⊓ N')) <
         padicValNat 2 (Nat.card N')) := by
  obtain ⟨a, ha, hcyc⟩ := cycleType_of_involution n τ hτ2 hτ1
  have hC := card_centralizer_involution n a τ ha hcyc
  have h2a := two_mul_le_of_cycleType n a τ hcyc
  have hperm : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rcases eq_top_or_eq_alt n (by omega) N' hA with rfl | rfl
  · rw [inf_top_eq, hC, Subgroup.card_top, hperm]
    exact finite_check_top n a hn hn' ha h2a
  · have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨x, hxC, hxodd⟩ := exists_swap_mem_centralizer n τ hτ2 hτ1
    have h2 : 2 * Nat.card ↥(centralizer ({τ} : Set (Equiv.Perm (Fin n))) ⊓
        alternatingGroup (Fin n)) = Nat.card ↥(centralizer ({τ} : Set (Equiv.Perm (Fin n)))) := by
      rw [inf_comm]
      exact two_mul_card_inf_alternatingGroup n _ x hxC hxodd
    have h3 := two_mul_nat_card_alternatingGroup (α := Fin n)
    rw [hperm] at h3
    exact finite_check_alt n a _ _ hn hn' ha h2a (even_of_mem_alternatingGroup n a τ hcyc hτ)
      (h2.trans hC) h3


theorem notAlt : NotAlt := by
  intro N _ _ X t o n hn hn' ⟨e⟩
  have hchar : (layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨ψ, hψ, hψk⟩ := exists_embedding_perm (K := layer N) o.cent_bot n (by omega)
    (by omega) e
  set N' : Subgroup (Perm (Fin n)) := ψ.range with hN'
  have hA : alternatingGroup (Fin n) ≤ N' := by
    intro a ha
    refine ⟨(e.symm ⟨a, ha⟩ : N), ?_⟩
    rw [hψk]
    simp
  have htt : ψ t * ψ t = 1 := by rw [← map_mul, o.loc.t_mul_t, map_one]
  have ht1 : ψ t ≠ 1 := by
    intro h
    have := hψ (h.trans (map_one ψ).symm)
    have h1 := o.loc.t_order
    rw [this, orderOf_one] at h1
    omega
  have hD : Nat.card ↥(centralizer ({t} : Set N)) =
      Nat.card ↥(centralizer ({ψ t} : Set (Perm (Fin n))) ⊓ N') := by
    have hmap : (centralizer ({t} : Set N)).map ψ =
        centralizer ({ψ t} : Set (Perm (Fin n))) ⊓ N' := by
      ext σ
      constructor
      · rintro ⟨g, hg, rfl⟩
        have hg' : g * t = t * g := mem_centralizer_singleton_iff.1 hg
        refine ⟨mem_centralizer_singleton_iff.2 ?_, ⟨g, rfl⟩⟩
        rw [← map_mul, ← map_mul, hg']
      · rintro ⟨hσ, g, rfl⟩
        refine ⟨g, mem_centralizer_singleton_iff.2 ?_, rfl⟩
        have hσ' : ψ g * ψ t = ψ t * ψ g := mem_centralizer_singleton_iff.1 hσ
        apply hψ
        rw [map_mul, map_mul, hσ']
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hψ).symm
  have hN : Nat.card N = Nat.card N' := Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv
  refine alt_comb n hn hn' N' hA (ψ t) ⟨t, rfl⟩ htt ht1 ⟨?_, ?_, ?_⟩
  · rw [← hD]
    exact o.loc.card_D_dvd
  · rw [← hD]
    exact o.loc.padicValNat_D_le
  · rw [← hD, ← hN]
    exact o.loc.not_sylow

end CFSG.OddStandard.Seitz77

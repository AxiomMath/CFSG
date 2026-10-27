module

public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMax

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Sporadic.Schreier
open CFSG.RankThree.PartTwo.KFacts.L34Max

def E0pow (p : Fin 3 × Fin 3) : Equiv.Perm (Fin 21) := e0a ^ (p.1 : ℕ) * e0b ^ (p.2 : ℕ)

def E0nine : Finset (Equiv.Perm (Fin 21)) :=
  (Finset.univ : Finset (Fin 3 × Fin 3)).image E0pow

theorem mul_mem_E0nine_aux :
    ∀ p q : Fin 3 × Fin 3, E0pow p * E0pow q ∈ E0nine := by decide +kernel

theorem inv_mem_E0nine_aux : ∀ p : Fin 3 × Fin 3, (E0pow p)⁻¹ ∈ E0nine := by
  decide +kernel

theorem one_mem_E0nine : (1 : Equiv.Perm (Fin 21)) ∈ E0nine := by
  rw [E0nine, Finset.mem_image]
  exact ⟨(0, 0), Finset.mem_univ _, by simp [E0pow]⟩

theorem e0b_mem_E0 : e0b ∈ E0 := by
  rw [E0_eq]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mul_mem_E0nine {x y : Equiv.Perm (Fin 21)} (hx : x ∈ E0nine) (hy : y ∈ E0nine) :
    x * y ∈ E0nine := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hy
  exact mul_mem_E0nine_aux p q

theorem inv_mem_E0nine {x : Equiv.Perm (Fin 21)} (hx : x ∈ E0nine) : x⁻¹ ∈ E0nine := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hx
  exact inv_mem_E0nine_aux p

theorem mem_of_mem_closure_E0nine {x : Equiv.Perm (Fin 21)}
    (hx : x ∈ Subgroup.closure (E0nine : Set (Equiv.Perm (Fin 21)))) : x ∈ E0nine := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact one_mem_E0nine
  | mul y z hy hz ihy ihz => exact mul_mem_E0nine ihy ihz
  | inv y hy ihy => exact inv_mem_E0nine ihy

theorem E0_le_closure_E0nine :
    E0 ≤ Subgroup.closure (E0nine : Set (Equiv.Perm (Fin 21))) := by
  rw [E0_eq, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · apply Subgroup.subset_closure
    change e0a ∈ E0nine
    rw [E0nine, Finset.mem_image]
    exact ⟨(1, 0), Finset.mem_univ _, by simp [E0pow]⟩
  · apply Subgroup.subset_closure
    change e0b ∈ E0nine
    rw [E0nine, Finset.mem_image]
    exact ⟨(0, 1), Finset.mem_univ _, by simp [E0pow]⟩

theorem E0nine_subset_E0 : (E0nine : Set (Equiv.Perm (Fin 21))) ⊆ E0 := by
  intro x hx
  rw [E0nine, Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact E0.mul_mem (E0.pow_mem e0a_mem _) (E0.pow_mem e0b_mem_E0 _)

theorem closure_E0nine_eq_E0 :
    Subgroup.closure (E0nine : Set (Equiv.Perm (Fin 21))) = E0 :=
  le_antisymm (Subgroup.closure_le E0 |>.mpr E0nine_subset_E0) E0_le_closure_E0nine

theorem exists_E0pow_eq_of_mem_E0 {x : Equiv.Perm (Fin 21)} (hx : x ∈ E0) :
    ∃ p : Fin 3 × Fin 3, E0pow p = x := by
  have hx' : x ∈ Subgroup.closure (E0nine : Set (Equiv.Perm (Fin 21))) := by
    rwa [closure_E0nine_eq_E0]
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp (mem_of_mem_closure_E0nine hx')
  exact ⟨p, hp⟩

def ofN0 (w : List ℤ) : Equiv.Perm (Fin 21) := evalCodes [n0a, n0b] w

def conjWordData : List (List ℤ) :=
  [[], [1, 1, 1], [1], [], [2, 1], [2], [1, 1], [1, 1, 2], [1, 2]]

def conjWord (p : Fin 3 × Fin 3) : List ℤ :=
  conjWordData.getD (3 * p.1.val + p.2.val) []

theorem conjWord_check :
    ∀ p : Fin 3 × Fin 3, E0pow p ≠ 1 →
      ofN0 (conjWord p) * e0a = E0pow p * ofN0 (conjWord p) := by
  decide +kernel

theorem exists_mem_N0_conj_e0a_eq {u : Equiv.Perm (Fin 21)} (hu : u ∈ E0) (hu1 : u ≠ 1) :
    ∃ n ∈ N0, n * e0a * n⁻¹ = u := by
  obtain ⟨p, hp⟩ := exists_E0pow_eq_of_mem_E0 hu
  have hne : E0pow p ≠ 1 := by rw [hp]; exact hu1
  refine ⟨ofN0 (conjWord p), ?_, ?_⟩
  · refine evalCodes_mem_of N0 ?_ (conjWord p)
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact n0a_mem
    · exact n0b_mem
  · have h := conjWord_check p hne
    calc
      ofN0 (conjWord p) * e0a * (ofN0 (conjWord p))⁻¹
          = (E0pow p * ofN0 (conjWord p)) * (ofN0 (conjWord p))⁻¹ := by rw [h]
      _ = E0pow p := by group
      _ = u := hp

theorem exists_mem_N0_conj_eq {a b : Equiv.Perm (Fin 21)} (ha : a ∈ E0) (ha1 : a ≠ 1)
    (hb : b ∈ E0) (hb1 : b ≠ 1) : ∃ n ∈ N0, n * a * n⁻¹ = b := by
  obtain ⟨na, hna, hna'⟩ := exists_mem_N0_conj_e0a_eq ha ha1
  obtain ⟨nb, hnb, hnb'⟩ := exists_mem_N0_conj_e0a_eq hb hb1
  refine ⟨nb * na⁻¹, N0.mul_mem hnb (N0.inv_mem hna), ?_⟩
  rw [← hna', ← hnb']
  group

theorem exists_mem_normalizer_conj_eq {X : Type*} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) {E : Subgroup X}
    (hE : Nat.card E = 9) {a b : X} (ha : a ∈ E) (ha1 : a ≠ 1) (hb : b ∈ E) (hb1 : b ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (E : Set X), n * a * n⁻¹ = b := by
  obtain ⟨e'⟩ := nonempty_mulEquiv_P21
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_map_eq_E0' (e.trans e') hE
  have hpa : (ψ a : Equiv.Perm (Fin 21)) ∈ E0 := by
    have h1 : ψ a ∈ E.map ψ.toMonoidHom := Subgroup.mem_map_of_mem ψ.toMonoidHom ha
    rw [hψ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hpb : (ψ b : Equiv.Perm (Fin 21)) ∈ E0 := by
    have h1 : ψ b ∈ E.map ψ.toMonoidHom := Subgroup.mem_map_of_mem ψ.toMonoidHom hb
    rw [hψ] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hpa1 : (ψ a : Equiv.Perm (Fin 21)) ≠ 1 := by
    intro h
    exact ha1 (ψ.injective (by apply Subtype.ext; simpa using h))
  have hpb1 : (ψ b : Equiv.Perm (Fin 21)) ≠ 1 := by
    intro h
    exact hb1 (ψ.injective (by apply Subtype.ext; simpa using h))
  obtain ⟨n, hnN, hnconj⟩ := exists_mem_N0_conj_eq hpa hpa1 hpb hpb1
  have hnP : n ∈ P21 := N0_le_P21 hnN
  have hnnorm : (⟨n, hnP⟩ : P21) ∈ Subgroup.normalizer (E0' : Set P21) := by
    rw [normalizer_E0']
    exact Subgroup.mem_subgroupOf.mpr hnN
  have hmap : (Subgroup.normalizer (E : Set X)).map ψ.toMonoidHom =
      Subgroup.normalizer (E.map ψ.toMonoidHom : Set P21) :=
    Subgroup.map_equiv_normalizer_eq E ψ
  rw [hψ] at hmap
  obtain ⟨m, hmN, hmψ⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hnnorm)
  refine ⟨m, hmN, ?_⟩
  apply ψ.injective
  rw [map_mul, map_mul, map_inv]
  rw [show ψ m = (⟨n, hnP⟩ : P21) from hmψ]
  exact Subtype.ext hnconj

private def conjPerm {X : Type*} [Group X] (E : Subgroup X)
    (n : Subgroup.normalizer (E : Set X)) : Equiv.Perm E where
  toFun x := ⟨(n : X) * (x : X) * (n : X)⁻¹,
    (Subgroup.mem_normalizer_iff.mp n.2 (x : X)).mp x.2⟩
  invFun x := ⟨(n : X)⁻¹ * (x : X) * (n : X),
    by
      simpa using
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) (x : X)).mp x.2⟩
  left_inv x := by
    ext
    group
  right_inv x := by
    ext
    group

private def conjHom {X : Type*} [Group X] (E : Subgroup X) :
    Subgroup.normalizer (E : Set X) →* Equiv.Perm E where
  toFun := conjPerm E
  map_one' := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (1 : X) * (x : X) * (1 : X)⁻¹ = (x : X)
    group
  map_mul' n m := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (n : X) * (m : X) * (x : X) * ((n : X) * (m : X))⁻¹ =
      (n : X) * ((m : X) * (x : X) * (m : X)⁻¹) * (n : X)⁻¹
    group

theorem centralizer_eq_of_card_eq_nine {X : Type*} [Group X]
    (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)) {E : Subgroup X}
    (hE : Nat.card E = 9) : Subgroup.centralizer (E : Set X) = E := by
  classical
  haveI : Finite X := Finite.of_injective (⇑e.toEquiv) e.toEquiv.injective
  haveI : Fintype E := Fintype.ofFinite E
  let C := Subgroup.centralizer (E : Set X)
  let N := Subgroup.normalizer (E : Set X)
  let ρ := conjHom E
  have hEC : E ≤ C := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcomm : IsMulCommutative E :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE]; norm_num)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (congrArg Subtype.val (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)).symm
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (E : Set X)
  have hker : ρ.ker = C.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h := congrArg (fun g : Equiv.Perm E => ((g ⟨y, hy⟩ : E) : X)) hn
      simp only [MonoidHom.one_apply, Equiv.Perm.coe_one, id_eq] at h
      have h' : (n : X) * y * (n : X)⁻¹ = y := h
      calc y * (n : X) = ((n : X) * y * (n : X)⁻¹) * (n : X) := by rw [h']
        _ = (n : X) * y := by group
    · intro hn
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change (n : X) * (x : X) * (n : X)⁻¹ = (x : X)
      rw [← Subgroup.mem_centralizer_iff.mp hn (x : X) x.2]
      group
  have hcard : Nat.card {x : E // x ≠ 1} = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun x : E => x = 1),
      Fintype.card_subtype_eq (1 : E)]
    have h9 : Fintype.card E = 9 := by rw [← Nat.card_eq_fintype_card, hE]
    omega
  have hNontrivial : Nontrivial E := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hE]
    norm_num
  obtain ⟨a, ha1⟩ := exists_ne (1 : E)
  have hconj_one : ∀ n : N, conjPerm E n (1 : E) = 1 := by
    intro n
    apply Subtype.ext
    simp [conjPerm]
  have hrange_fix : ∀ h : ρ.range, h.1 (1 : E) = 1 := by
    intro h
    obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp h.2
    rw [← hn]
    exact hconj_one n
  let f : ρ.range → {x : E // x ≠ 1} := fun h =>
    ⟨h.1 a, by
      intro h1
      exact ha1 ((h.1).injective (by rw [h1, hrange_fix h]))⟩
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨n, hnN, hnconj⟩ := exists_mem_normalizer_conj_eq e hE a.2
      (by intro h; exact ha1 (Subtype.ext h)) x.1.2
      (by intro h; exact x.2 (Subtype.ext h))
    refine ⟨⟨ρ ⟨n, hnN⟩, ⟨⟨n, hnN⟩, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hnconj
  have h8le : 8 ≤ Nat.card ρ.range := by
    have h := Nat.card_le_card_of_surjective f hf
    rwa [hcard] at h
  have h72 : Nat.card ρ.ker * Nat.card ρ.range = 72 := by
    rw [Subgroup.card_ker_mul_card_range ρ]
    exact card_normalizer_of_card_eq_nine e hE
  have hker_le : Nat.card ρ.ker ≤ 9 := by
    have h := Nat.mul_le_mul_left (Nat.card ρ.ker) h8le
    omega
  have hCcard : Nat.card ρ.ker = Nat.card C := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  have hC_le : Nat.card C ≤ 9 := hCcard ▸ hker_le
  exact (Subgroup.eq_of_le_of_card_ge hEC (by rw [hE]; exact hC_le)).symm

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

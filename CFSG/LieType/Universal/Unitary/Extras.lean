module

public import CFSG.LieType.Universal.Unitary.Roots
public import CFSG.LieType.Steinberg.Extras
import all CFSG.LieType.Universal.Unitary.Roots
import CFSG.LieType.Universal.Unitary.Extras.Basic
import CFSG.LieType.Universal.Unitary.Extras.Unipotent
import CFSG.LieType.Universal.Unitary.Extras.Torus
import CFSG.LieType.Universal.Unitary.Extras.RankOne
import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
import CFSG.LieType.Universal.Unitary.Extras.Commutator

public section

namespace CFSG.LieType.Universal.Unitary

open Matrix CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.BorelTits SUExtras

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

@[expose] noncomputable def rootDatum (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    UniversalRootDatum (SU (unitaryInvolution F p f) n) where
  rank := n / 2
  cartan := cartan n
  isFiniteType := isFiniteType_cartan n
  divisible := divisible n
  rootGroup := rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n

section General

variable {K : Type*} [Field K] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

private theorem exists_pos_of_mem_roots {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) :
    ∃ a b : Fin n, a ≠ b ∧ toStd n γ = weight n a - weight n b := by
  rw [roots_eq] at hγ
  rcases hγ with ⟨i, j, hij, -, -, -, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · exact ⟨i, j, hij, h⟩
  · exact ⟨i, Fin.rev i, hi, by rw [h, weight_rev', sub_neg_eq_add, two_nsmul]⟩
  · refine ⟨i, midIdx n he, fun h' => ?_, by rw [h, weight_eq_zero_of_rev_eq (rev_midIdx he),
      sub_zero]⟩
    rw [h'] at hi
    exact hi (rev_midIdx he).symm

private theorem weight_ne_two_smul_weight {c i : Fin n} (hi : i ≠ Fin.rev i) :
    weight n c ≠ 2 • weight n i := by
  intro h
  obtain ⟨ci, hci⟩ := exists_weight_ne_zero hi
  have h1 := congrFun h ci
  simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, weight_apply'] at h1
  have := ci.isLt
  split_ifs at h1 <;> omega

private theorem rootGroup_ne_bot {ζ : traceZero σ} (hζ : (ζ : K) ≠ 0) {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n)) : rootGroup σ hσ n γ ≠ ⊥ := by
  have key : ∀ (x : SU σ n) (a b : Fin n), x ∈ rootGroup σ hσ n γ → a ≠ b →
      mat σ n x a b ≠ 0 → rootGroup σ hσ n γ ≠ ⊥ := by
    intro x a b hx hab hne hbot
    rw [hbot, Subgroup.mem_bot] at hx
    rw [hx, map_one, one_apply_ne hab] at hne
    exact hne rfl
  have hγ' := hγ
  rw [roots_eq] at hγ'
  rcases hγ' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he, i, hi, h⟩
  · refine key _ i j (rootHom_mem hσ hij hi hj hji h.symm (Multiplicative.ofAdd 1)) hij ?_
    rw [mat_apply (rootHom _ _ _ _ _ _), coe_rootHom, toAdd_ofAdd, rootMatrix_apply_pq hij hji]
    exact one_ne_zero
  · refine key _ i (Fin.rev i) (longRootHom_mem hσ hi h.symm (Multiplicative.ofAdd ζ)) hi ?_
    rw [mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd, longRootMatrix_apply hi]
    exact hζ
  · have hik : i ≠ midIdx n he := fun h' => hi (by rw [h', rev_midIdx he])
    refine key _ i (Fin.rev i) (heisenberg_le hσ hi hik (rev_midIdx he) h.symm
      (longRootHom_mem_heisenberg hσ hi hik (rev_midIdx he) (Multiplicative.ofAdd ζ))) hi ?_
    rw [mat_apply (longRootHom _ _ _), coe_longRootHom, toAdd_ofAdd, longRootMatrix_apply hi]
    exact hζ

private theorem rootGroup_two_smul_le' {γ : Fin (n / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan n) (divisible n))
    (h2 : 2 • γ ∈ roots (isFiniteType_cartan n) (divisible n)) :
    rootGroup σ hσ n (2 • γ) ≤ rootGroup σ hσ n γ := by
  obtain ⟨c, d, -, hcd⟩ := exists_pos_of_mem_roots h2
  rw [toStd_nsmul_two] at hcd
  have hne := toStd_ne_zero_of_mem_roots hγ
  obtain ⟨-, hwc⟩ := eq_rev_of_weight_sub_eq_two_smul hcd.symm hne
  have hc : c ≠ Fin.rev c := by
    intro h
    exact hne (by rw [← hwc, weight_eq_zero_of_rev_eq h.symm])
  have hodd : ¬Even n := by
    intro he
    have hγ' := hγ
    rw [roots_eq] at hγ'
    rcases hγ' with ⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨he', -⟩
    · exact weight_ne_weight_sub hij hi hj hji (hwc.trans h)
    · exact weight_ne_two_smul_weight hi (hwc.trans h)
    · exact he' he
  have := rootGroup_two_smul_le hσ hodd hc hwc.symm
  rwa [two_zsmul, ← two_nsmul] at this

end General

theorem steinbergExtras (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) (_hn : 2 ≤ n)
    (ζ : traceZero (unitaryInvolution F p f)) (hζ : (ζ : F) ≠ 0) :
    SteinbergExtras (rootDatum hF n) (levelWeyl (unitaryInvolution_involutive hF) ζ)
      (levelTorus (unitaryInvolution F p f)) := by
  have hσ := unitaryInvolution_involutive hF
  have htr : ∀ x, unitaryInvolution F p f x = x → ∃ c, c + unitaryInvolution F p f c = x :=
    fun _ hx => exists_add_unitaryInvolution_eq hF hx
  have hnorm : ∀ x, unitaryInvolution F p f x = x → ∃ a, unitaryInvolution F p f a * a = x :=
    fun _ hx => exists_norm_eq hF hx
  exact
  { ne_bot := fun _ hγ => rootGroup_ne_bot hσ hζ hγ
    two_smul_le := fun _ hγ h2 => rootGroup_two_smul_le' hσ hγ h2
    commutator_mem := fun _ _ _ _ hind _ hx _ hy => commutator_mem hσ htr hind hx hy
    prodInjective_pos := fun L hL hmem hsort => prodInjective_of hσ 1 one_ne_zero L hL
      (fun γ hγ => ((hmem γ).1 hγ).1) (fun γ hγ => ((hmem γ).1 hγ).2.2)
      (fun γ hγ => by
        have h : 0 < ht (ι := Fin (n / 2)) γ := ((hmem γ).1 hγ).2.1
        omega)
      (hsort.imp fun {γ δ} h => by
        have h' : ht (ι := Fin (n / 2)) γ ≤ ht (ι := Fin (n / 2)) δ := h
        omega)
    prodInjective_neg := fun L hL hmem hsort => prodInjective_of hσ (-1) (by norm_num) L hL
      (fun γ hγ => ((hmem γ).1 hγ).1) (fun γ hγ => ((hmem γ).1 hγ).2.2)
      (fun γ hγ => by
        have h : ht (ι := Fin (n / 2)) γ < 0 := ((hmem γ).1 hγ).2.1
        omega)
      (hsort.imp fun {γ δ} h => by
        have h' : ht (ι := Fin (n / 2)) δ ≤ ht (ι := Fin (n / 2)) γ := h
        omega)
    posPart_inf_negPart := posPart_inf_negPart hσ
    rankOne_bruhat := fun k g hg => by
      by_cases hk : k.val + 1 < n / 2
      · exact rankOne_bruhat_short hk hζ hnorm g hg
      · by_cases he : Even n
        · exact rankOne_bruhat_last_even hk he hζ hnorm g hg
        · exact rankOne_bruhat_last_odd hk he hζ hnorm g hg
    eq_one_of_mem_normalizer := fun k u hu hn' => by
      by_cases hk : k.val + 1 < n / 2
      · exact eq_one_of_mem_normalizer_short hk u hu hn'
      · by_cases he : Even n
        · exact eq_one_of_mem_normalizer_last_even hk he hζ u hu hn'
        · exact eq_one_of_mem_normalizer_last_odd hk he hζ u hu hn'
    torus_commute := torus_commute
    torus_iSupIndep := torus_iSupIndep
    torus_inf_posPart := torus_inf_posPart hσ }

end CFSG.LieType.Universal.Unitary

module

public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

set_option linter.unusedSectionVars false

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem d4_cartan_perm_pow_six (π : Equiv.Perm (Fin Tag.D4.rank))
    (hπ : ∀ i j, Tag.D4.cartan (π i) (π j) = Tag.D4.cartan i j) : π ^ 6 = 1 := by
  have key : ∀ π : Equiv.Perm (Fin 4),
      (∀ i j : Fin 4, (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
        Fin 4 → Fin 4 → ℤ) (π i) (π j) =
        (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
          Fin 4 → Fin 4 → ℤ) i j) → π ^ 6 = 1 := by
    decide +kernel
  have hc : ∀ i j : Fin 4, Tag.D4.cartan i j =
      (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
        Fin 4 → Fin 4 → ℤ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  exact key π (fun i j => by rw [← hc, ← hc]; exact hπ i j)

theorem d4_perm_pow_of_odd (π : Equiv.Perm (Fin Tag.D4.rank))
    (hπ : ∀ i j, Tag.D4.cartan (π i) (π j) = Tag.D4.cartan i j) {m : ℕ} (hm : Odd m)
    (h : π ^ m = 1) : π = 1 ∨ π = TwistTag.D4.perm ∨ π = TwistTag.D4.perm ^ 2 := by
  have h6 := d4_cartan_perm_pow_six π hπ
  have hg : π ^ (Nat.gcd 6 m) = 1 := pow_gcd_eq_one.2 ⟨h6, h⟩
  have hg3 : Nat.gcd 6 m ∣ 3 := by
    have h1 : Nat.Coprime 2 m := (Nat.coprime_two_left).2 hm
    have : Nat.gcd (2 * 3) m = Nat.gcd 3 m := Nat.Coprime.gcd_mul_left_cancel 3 h1
    rw [show (6 : ℕ) = 2 * 3 from rfl, this]
    exact Nat.gcd_dvd_left 3 m
  have h3 : π ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := hg3
    rw [hk, pow_mul, hg, one_pow]
  exact perm_pow_of_cartanD4 π hπ h3

section Cert

variable
    {K : Type} [Field K] [Finite K]

theorem rootDiagUnit_mem_adjointGroup_D4 (hK : ringChar K = 2) (a : Fin Tag.D4.rank → Kˣ) :
    rootDiagUnit Tag.D4 a ∈ adjointGroup Tag.D4 K := by
  have hT := (even_power_two_Cartan_root_diagonals_inner Tag.D4
    (Or.inr (Or.inr (Or.inl rfl))) K hK).1 a
  have hle : torusGroup Tag.D4 K ≤ adjointGroup Tag.D4 K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact hle hT

theorem exists_odd_normal_form (hK : ringChar K = 2) {m : ℕ} (hm : Odd m)
    {α : MulAut (adjointGroup Tag.D4 K)} (hα : α ^ m = 1) :
    ∃ (g : adjointGroup Tag.D4 K) (σ : K ≃+* K) (ε : ℕ), ε < 3 ∧
      ∀ h : adjointGroup Tag.D4 K, (α h : ModGL Tag.D4 K) =
        (g : ModGL Tag.D4 K) * d4P K ^ ε *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.D4 K) *
            ((g : ModGL Tag.D4 K) * d4P K ^ ε)⁻¹ := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 α
  have hA : β ∈ unipotentPairAut Tag.D4 K := ⟨hU, hV⟩
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hA
  have hcart := cartan_perm_eq_D4 (K := K) (fun i => (hπ i).1)
  have hβm : β ^ m = MulAut.conj (((List.range m).map fun i => (β ^ i) c).prod)⁻¹ := by
    have h1 := conj_mul_pow c β m
    have h2 : MulAut.conj (((List.range m).map fun i => (β ^ i) c).prod) * β ^ m = 1 := by
      rw [← h1, hα]
    rw [eq_inv_of_mul_eq_one_right h2, map_inv]
  have hβmA : β ^ m ∈ unipotentPairAut Tag.D4 K := pow_mem hA m
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag (hβm ▸ hβmA)
  have hπm : π ^ m = 1 := by
    refine perm_map_simple_unique (α := β ^ m) (π := π ^ m) (π' := 1)
      (fun i => map_simplePos_pow (fun j => (hπ j).1) m i) (fun i => ?_)
    rw [hβm, hb, map_simplePosSubgroup_exactNormalAut b 1 0 i]
    rfl
  have hex : ∃ ε : ℕ, ε < 3 ∧ π = d4Rho ^ ε := by
    rcases d4_perm_pow_of_odd π hcart hm hπm with h | h | h
    · exact ⟨0, by norm_num, by rw [h]; rfl⟩
    · exact ⟨1, by norm_num, by rw [h]; exact (pow_one _).symm⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨ε, hε3, rfl⟩ := hex
  obtain ⟨a, σ, hβ⟩ := exists_normalAut_mul_graph (K := K) hπ
  have hdC := rootDiagUnit_mem_adjointGroup_D4 (K := K) hK a
  refine ⟨c * ⟨rootDiagUnit Tag.D4 a, hdC⟩, σ, ε, hε3, fun h => ?_⟩
  rw [hβ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_mul, coe_exactNormalAut_zero, coe_d4Graph, Subgroup.coe_inv]
  simp only [Subgroup.coe_mul, map_mul, map_inv, map_pow,
    units_map_entrywiseHom_diagramMap]
  have hP : Units.map (entrywiseHom σ.toRingHom) (d4P K) = d4P K :=
    units_map_entrywiseHom_diagramMap σ.toRingHom
  rw [hP]
  group

end Cert

end CFSG.LieType.ChevTwo.Semi

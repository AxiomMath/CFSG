module

public import CFSG.LieType.Chevalley.FixedCollection
public import CFSG.LieType.Chevalley.RootConj
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootOps

variable {τ : Tag} {K : Type} [Field K]

theorem Uminus_simple_le (i : Fin τ.rank) :
    Uminus τ K (simple τ i) ≤ (nativeRootSubgroups τ K).X (simpleRoot τ i) := by
  refine iSup₂_le fun α hα => ?_
  have : α = simpleRoot τ i := by
    by_contra hne
    have h := height_reflect_pos α.2 hα.1 (fun h => hne (Subtype.ext h))
    have h2 := hα.2
    rw [coe_smul_root, simple_smul] at h2
    omega
  rw [this]

theorem eltElement_injective (α : Root τ) :
    Function.Injective ((rootOperatorFamily τ).eltElement (K := K) α) := by
  intro c d h
  obtain ⟨j, ε, m, hε, -, hm⟩ := (rootOperatorFamily τ).exists_eltUnit_eq_conj K α
  have h1 : (rootOperatorFamily τ).eltUnit K α c = (rootOperatorFamily τ).eltUnit K α d :=
    congrArg (fun g : adjointGroup τ K => (g : ModGL τ K)) h
  rw [hm, hm, mul_left_inj, mul_right_inj] at h1
  have h2 := xOp_injective j (congrArg Units.val h1)
  rcases hε with rfl | rfl
  · simpa using h2
  · simpa using h2

theorem eq_one_of_conj_eltElement {β : Root τ} {h : adjointGroup τ K} {l : K} (hl : l ≠ 1)
    (hconj : ∀ c, h * (rootOperatorFamily τ).eltElement β c * h⁻¹ =
      (rootOperatorFamily τ).eltElement β (l * c))
    {y : adjointGroup τ K} (hy : y ∈ (nativeRootSubgroups τ K).X β) (hyc : h * y * h⁻¹ = y) :
    y = 1 := by
  obtain ⟨c, rfl⟩ := (rootOperatorFamily τ).mem_rootSubgroup.1 hy
  rw [hconj] at hyc
  have hc := eltElement_injective β hyc
  have : c = 0 := by
    have h' : (l - 1) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
    rcases mul_eq_zero.1 h' with h'' | h''
    · exact absurd (sub_eq_zero.1 h'') hl
    · exact h''
  rw [this, RootOperatorFamily.eltElement_zero]

variable [Finite K]

theorem conj_mem_X_of_mem_H {h x : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    {α : Root τ} (hx : x ∈ (nativeRootSubgroups τ K).X α) :
    h * x * h⁻¹ ∈ (nativeRootSubgroups τ K).X α := by
  obtain ⟨k, hk, rfl⟩ := (RootGroupData.mem_H_iff (D := nativeData τ K)).mp hh
  have := RootGroupData.conj_mem (D := nativeData τ K) k hx
  rwa [hk, one_smul] at this

theorem conj_mem_Uminus_of_mem_H {h x : adjointGroup τ K} (hh : h ∈ (nativeData τ K).H)
    {w : WeylGroup τ} (hx : x ∈ Uminus τ K w) : h * x * h⁻¹ ∈ Uminus τ K w :=
  RootGroupData.conj_mem_of_iSup (D := nativeData τ K) h
    (fun α hα _ hy => le_iSup₂_of_le (f := fun (β : Root τ)
      (_ : 0 < height β.1 ∧ height (w • β).1 < 0) => (nativeRootSubgroups τ K).X β) α hα le_rfl
        (conj_mem_X_of_mem_H hh hy)) hx

theorem eq_one_of_mem_Uminus_of_forall_commute {A : Set (adjointGroup τ K)}
    (hA : ∀ h ∈ A, h ∈ (nativeData τ K).H)
    (hchar : ∀ β : Root τ, 0 < height β.1 → ∀ y ∈ (nativeRootSubgroups τ K).X β,
      (∀ h ∈ A, h * y * h⁻¹ = y) → y = 1) :
    ∀ ω : List (Fin τ.rank), (coxeterSystem τ).IsReduced ω →
      ∀ u ∈ Uminus τ K ((coxeterSystem τ).wordProd ω), (∀ h ∈ A, h * u * h⁻¹ = u) → u = 1
  | [], _, u, hu, _ => by
    rwa [CoxeterSystem.wordProd_nil, Uminus_one, Subgroup.mem_bot] at hu
  | i :: ω, hred, u, hu, hc => by
    have hred' : (coxeterSystem τ).IsReduced ([i] ++ ω) := hred
    obtain ⟨-, hω⟩ := isReduced_left_right_of_append hred'
    have hlen := length_mul_of_isReduced_append hred'
    rw [CoxeterSystem.wordProd_singleton] at hlen
    rw [CoxeterSystem.wordProd_cons] at hu
    obtain ⟨⟨z, y⟩, ⟨hz, hy, hzy⟩, huniq⟩ := existsUnique_Uminus_mul hlen hu
    simp only at hz hy hzy
    set v' := (coxeterSystem τ).wordProd ω
    set m : monomialGroup τ K := ⟨nrep τ K v', nrep_mem_monomialGroup τ K v'⟩
    have hfix : ∀ h ∈ A, h * z * h⁻¹ = z ∧ h * y * h⁻¹ = y := by
      intro h hhA
      have hh := hA h hhA
      have hh' : nrep τ K v' * h * (nrep τ K v')⁻¹ ∈ (nativeData τ K).H :=
        RootGroupData.conj_mem_H (D := nativeData τ K) m hh
      have hp := huniq (h * z * h⁻¹, h * y * h⁻¹) ⟨conj_mem_Uminus_of_mem_H hh hz, by
          have e : nrep τ K v' * (h * y * h⁻¹) * (nrep τ K v')⁻¹ =
              (nrep τ K v' * h * (nrep τ K v')⁻¹) * (nrep τ K v' * y * (nrep τ K v')⁻¹) *
                (nrep τ K v' * h * (nrep τ K v')⁻¹)⁻¹ := by group
          rw [e]
          exact conj_mem_Uminus_of_mem_H hh' hy, by
          have := hc h hhA
          rw [hzy] at this ⊢
          calc z * y = h * (z * y) * h⁻¹ := this.symm
            _ = h * z * h⁻¹ * (h * y * h⁻¹) := by group⟩
      exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
    have hyX : y ∈ (nativeRootSubgroups τ K).X (v'⁻¹ • simpleRoot τ i) := by
      have hx := Uminus_simple_le i hy
      have h1 := RootGroupData.inv_conj_mem (D := nativeData τ K) m hx
      change (nrep τ K v')⁻¹ * (nrep τ K v' * y * (nrep τ K v')⁻¹) * nrep τ K v' ∈
        (nativeRootSubgroups τ K).X ((weylHom τ K m)⁻¹ • simpleRoot τ i) at h1
      rw [weylHom_nrep] at h1
      simpa [mul_assoc] using h1
    have hβ : 0 < height (v'⁻¹ • simpleRoot τ i).1 := by
      have hl : (coxeterSystem τ).length (simple τ i * v') =
          (coxeterSystem τ).length v' + 1 := by
        rw [hlen, (coxeterSystem τ).length_simple, add_comm]
      exact (length_simple_mul_eq_add_one_iff v' i).1 hl
    have hy1 : y = 1 := hchar _ hβ y hyX fun h hh => (hfix h hh).2
    rw [hzy, hy1, mul_one]
    exact eq_one_of_mem_Uminus_of_forall_commute hA hchar ω hω z hz fun h hh => (hfix h hh).1

theorem eq_one_of_mem_U_of_forall_commute {A : Set (adjointGroup τ K)}
    (hA : ∀ h ∈ A, h ∈ (nativeData τ K).H)
    (hchar : ∀ β : Root τ, 0 < height β.1 → ∀ y ∈ (nativeRootSubgroups τ K).X β,
      (∀ h ∈ A, h * y * h⁻¹ = y) → y = 1)
    {ω : List (Fin τ.rank)} (hred : (coxeterSystem τ).IsReduced ω)
    (hneg : negCheck τ ω = true) {u : adjointGroup τ K} (hu : u ∈ (nativeData τ K).U)
    (hc : ∀ h ∈ A, h * u * h⁻¹ = u) : u = 1 := by
  rw [← Uminus_eq_U_of_negCheck hneg] at hu
  exact eq_one_of_mem_Uminus_of_forall_commute hA hchar ω hred u hu hc

end CFSG.LieType.Chevalley

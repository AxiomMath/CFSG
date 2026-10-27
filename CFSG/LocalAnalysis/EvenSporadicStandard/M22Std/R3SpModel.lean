module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3SpAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.LayerA10Basic
public import CFSG.LieType.Steinberg.CentralExt.Model

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.EvenSporadicStandard.M24Std
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

theorem exists_outerWr1 {X : Type} [Group X] [Finite X] {z : X} (hz2 : z * z = 1)
    (hCz : Nat.card (centralizer ({z} : Set X)) = 1440)
    (hLie : LieModel (egaLayer X) .PSp 2 2 2)
    (hzE : z ∉ egaLayer X ⊔ centralizer (egaLayer X : Set X))
    (hC6 : Nonempty (↥(egaLayer X ⊓ centralizer ({z} : Set X)) ≃* Equiv.Perm (Fin 6))) :
    ∃ Eh : Subgroup X, OuterWr1 X z Eh (egaLayer X) := by
  classical
  have hEn : (egaLayer X).Normal := egaLayer_normal X
  have hn : ∀ e ∈ egaLayer X, z * e * z⁻¹ ∈ egaLayer X := fun e he => hEn.conj_mem e he z
  have hzE' : z ∉ egaLayer X := fun h => hzE (Subgroup.mem_sup_left h)
  have hc : StatedClassicalModel (egaLayer X) .PSp 2 2 2 :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hLie
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := id hc
  have hK2 : Nat.card K = 2 ^ 2 := by simpa using hK
  have hK4 : Nat.card K = 4 := by rw [hK2]; norm_num
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by norm_num) hK
  let ψ0 : egaLayer X ≃* antiSp K := e.trans (antiProjEquiv K).symm
  let α : MulAut (egaLayer X) := MulAut.conjNormal z
  have hα : ∀ x : egaLayer X, ((α x : egaLayer X) : X) = z * x * z⁻¹ := fun x =>
    MulAut.conjNormal_apply z x
  let β : MulAut (antiSp K) := MulAut.congr ψ0 α
  have hβ : ∀ x : egaLayer X, β (ψ0 x) = ψ0 (α x) := fun x => by
    simp [β]
  have hαα : α * α = 1 := by
    rw [← map_mul]
    have : z * z = 1 := hz2
    rw [this, map_one]
  have hβ2 : β * β = 1 := by
    rw [← map_mul, hαα, map_one]
  have hβinn : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp K) := by
    rintro ⟨g, hg⟩
    obtain ⟨e0, he0⟩ : ∃ e0 : egaLayer X, ψ0 e0 = g := ⟨ψ0.symm g, by simp⟩
    have key : ∀ x : egaLayer X, z * (x : X) * z⁻¹ = (e0 : X) * x * (e0 : X)⁻¹ := by
      intro x
      have h1 : MulAut.conj g (ψ0 x) = β (ψ0 x) := by rw [hg]
      have h2 : ψ0 (α x) = ψ0 (e0 * x * e0⁻¹) := by
        rw [← hβ, ← h1, MulAut.conj_apply, map_mul, map_mul, map_inv, he0]
      have h3 : α x = e0 * x * e0⁻¹ := ψ0.injective h2
      rw [← hα]
      exact congrArg Subtype.val h3
    apply hzE
    have hcen : (e0 : X)⁻¹ * z ∈ centralizer (egaLayer X : Set X) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := key ⟨x, hx⟩
      calc x * ((e0 : X)⁻¹ * z) = (e0 : X)⁻¹ * ((e0 : X) * x * (e0 : X)⁻¹) * z := by group
        _ = (e0 : X)⁻¹ * (z * x * z⁻¹) * z := by rw [← h1]
        _ = ((e0 : X)⁻¹ * z) * x := by group
    have : z = (e0 : X) * ((e0 : X)⁻¹ * z) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left e0.2) (Subgroup.mem_sup_right hcen)
  obtain ⟨c, hcβ⟩ := outer_involution_conj (n := 2) le_rfl hK2 β hβ2 hβinn
  let ψ : egaLayer X ≃* antiSp K := ψ0.trans (MulAut.conj c⁻¹)
  have hact : ∀ (x : egaLayer X) (hx : z * (x : X) * z⁻¹ ∈ egaLayer X),
      ψ ⟨z * x * z⁻¹, hx⟩ = frobAut K (ψ x) := by
    intro x hx
    have h1 : (⟨z * x * z⁻¹, hx⟩ : egaLayer X) = α x := Subtype.ext (hα x).symm
    rw [h1, frobAut_eq_minorAut_sq]
    have h2 : β (ψ0 x) = c * (minorAut K ^ 2) (c⁻¹ * ψ0 x * c) * c⁻¹ := by
      rw [hcβ]
      simp [MulAut.mul_apply, MulAut.conj_apply]
    show c⁻¹ * ψ0 (α x) * c⁻¹⁻¹ = (minorAut K ^ 2) (c⁻¹ * ψ0 x * c⁻¹⁻¹)
    rw [← hβ, h2]
    simp [mul_assoc]
  have hCE : Nat.card ↥(egaLayer X ⊓ centralizer ({z} : Set X)) = 720 := by
    obtain ⟨φ⟩ := hC6
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hnA : ∀ a ∈ egaLayer X ⊓ centralizer ({z} : Set X),
      z * a * z⁻¹ ∈ egaLayer X ⊓ centralizer ({z} : Set X) := by
    intro a ha
    have h1 : a * z = z * a := mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).2
    have : z * a * z⁻¹ = a := by rw [← h1]; group
    rw [this]
    exact ha
  have hzA : z ∉ egaLayer X ⊓ centralizer ({z} : Set X) := fun h => hzE' (Subgroup.mem_inf.1 h).1
  have hDcard : Nat.card (extSub (egaLayer X ⊓ centralizer ({z} : Set X)) z hz2 hnA) = 1440 := by
    rw [card_extSub hzA, hCE]
  have hDle : extSub (egaLayer X ⊓ centralizer ({z} : Set X)) z hz2 hnA ≤
      centralizer ({z} : Set X) := by
    intro x hx
    rcases hx with hx | hx
    · exact (Subgroup.mem_inf.1 hx).2
    · have h1 := (Subgroup.mem_inf.1 hx).2
      have hzC : z ∈ centralizer ({z} : Set X) := mem_centralizer_singleton_iff.2 rfl
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hzC)
      simpa using this
  have hDeq : extSub (egaLayer X ⊓ centralizer ({z} : Set X)) z hz2 hnA =
      centralizer ({z} : Set X) :=
    Subgroup.eq_of_le_of_card_ge hDle (by rw [hDcard, hCz])
  have hCzle : centralizer ({z} : Set X) ≤ extSub (egaLayer X) z hz2 hn := by
    rw [← hDeq]
    exact extSub_mono inf_le_left
  exact ⟨_, outerWr1_of_equiv hK4 hz2 hzE' hn ψ hact hCzle⟩

end CFSG.EvenSporadicStandard.M22Std

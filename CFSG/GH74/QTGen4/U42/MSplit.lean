module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.H13.A5Producer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

theorem fix_pa_eq : ∀ x : W5, pact pa x = x → ∃ u : W5, x = u * pact pa u := by
  decide +kernel

theorem fixed_pa_pb : ∀ x : W5, pact pa x = x → pact pb x = x → x = 1 ∨ x = W4 := by
  decide +kernel

theorem W4_eq : pact pa (Multiplicative.ofAdd (e2 0 1)) = Multiplicative.ofAdd (e2 0 1) ∧
    W4 = Multiplicative.ofAdd (e2 0 1) * pact pb (Multiplicative.ofAdd (e2 0 1)) := by
  decide +kernel

theorem fix_pa_pb_eq (x : W5) (ha : pact pa x = x) (hb : pact pb x = x) :
    ∃ y : W5, pact pa y = y ∧ x = y * pact pb y := by
  rcases fixed_pa_pb x ha hb with rfl | rfl
  · exact ⟨1, map_one _, by rw [map_one, one_mul]⟩
  · exact ⟨_, W4_eq.1, W4_eq.2⟩

theorem K4_facts : pa * pa = 1 ∧ pb * pb = 1 ∧ pb * pa * pb⁻¹ * pa⁻¹ = 1 := by
  decide

theorem InK4_cases : ∀ σ : Equiv.Perm (Fin 5), InK4 σ →
    σ = 1 ∨ σ = pa ∨ σ = pb ∨ σ = pa * pb := by
  decide +kernel

def klein {G : Type} [Group G] (a b : G) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) : Subgroup G where
  carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have hba : b * a = a * b := hab.symm
    have e1 : a * (a * b) = b := by rw [← mul_assoc, ha2, one_mul]
    have e2 : (a * b) * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha2, one_mul]
    have e3 : (a * b) * b = a := by rw [mul_assoc, hb2, mul_one]
    have e4 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb2, mul_one]
    have e5 : (a * b) * (a * b) = 1 := by
      rw [mul_assoc, ← mul_assoc b a b, hba, mul_assoc a b b, hb2, mul_one, ha2]
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ha2, hb2, hba, e1, e2, e3, e4, e5]
  inv_mem' := by
    have hba : b * a = a * b := hab.symm
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · rw [ia]; simp
    · rw [ib]; simp
    · rw [mul_inv_rev, ia, ib, hba]; simp

theorem mem_klein_iff {G : Type} [Group G] (a b : G) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : a * b = b * a) (x : G) :
    x ∈ klein a b ha2 hb2 hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b :=
  Iff.rfl

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : A5.Setting G T L V)
include S

theorem rho_V {v : G} (hv : v ∈ V) : S.frame.ρ ⟨v, Subgroup.le_normalizer hv⟩ = 1 := by
  refine S.frame.rho_eq_one_of_mem _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  exact B2F.isElemAbelian_comm S.elemAbelian_V hw hv

theorem eq_mul_conj_of_psi (g : ↥(Subgroup.normalizer (V : Set G))) {v : G} (hv : v ∈ V)
    {u₀ : W5} (h : S.frame.ψ ⟨v, hv⟩ = u₀ * pact (S.frame.ρ g) u₀) :
    v = (S.frame.ψ.symm u₀ : G) * ((g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹) := by
  have hmem : (g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp g.2 _).mp (S.frame.ψ.symm u₀).2
  have h2 : S.frame.ψ ⟨(g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹, hmem⟩ =
      pact (S.frame.ρ g) u₀ := by
    rw [S.psi_conj, MulEquiv.apply_symm_apply]
  have h3 : S.frame.ψ (S.frame.ψ.symm u₀ *
      ⟨(g : G) * (S.frame.ψ.symm u₀ : G) * (g : G)⁻¹, hmem⟩) = S.frame.ψ ⟨v, hv⟩ := by
    rw [map_mul, h2, MulEquiv.apply_symm_apply, h]
  exact (congrArg Subtype.val (S.frame.ψ.injective h3)).symm

end Setting

end CFSG.GH74.QTGen4.U42

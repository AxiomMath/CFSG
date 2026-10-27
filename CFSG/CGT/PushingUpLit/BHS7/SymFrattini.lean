module

public import CFSG.CGT.PushingUpLit.BHS7.SymSetup

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ} {m : ℕ}

omit [Finite Γ] in
theorem SymModel.baum_le_normalizer_W (X : SymModel G T E m) (hE : IsBTBlock G T E) :
    baum T ≤ Subgroup.normalizer (X.M.W : Set Γ) := by
  rw [X.hMW]
  exact (baum_le_normalizer_of_isBTBlock hE).trans
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E)

omit [Finite Γ] in
theorem SymModel.Ψ_conj_baum (X : SymModel G T E m) (hE : IsBTBlock G T E) (b : ↥(baum T))
    (e : ↥E) (hbe : (b : Γ) * (e : Γ) * (b : Γ)⁻¹ ∈ E) :
    X.M.Ψ ⟨(b : Γ) * (e : Γ) * (b : Γ)⁻¹, hbe⟩ = X.S b * X.M.Ψ e * (X.S b)⁻¹ :=
  X.M.Ψ_conj (X.baum_le_normalizer_W hE b.2) (fun w hw => X.hS b w hw) e hbe

theorem mem_normalizer_baum_of_Ψ_mem_normalizer (hT : IsSylowTwoOf T G) (hE : IsBTBlock G T E)
    (X : SymModel G T E m) (e : ↥E)
    (he : X.M.Ψ e ∈ Subgroup.normalizer
      (Subgroup.closure X.T' : Set (Equiv.Perm (Fin (2 * m + 1))))) :
    (e : Γ) ∈ Subgroup.normalizer (baum T : Set Γ) := by
  classical
  set Y : Subgroup (Equiv.Perm (Fin (2 * m + 1))) := Subgroup.closure X.T' with hY
  have hBE : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBT : baum T ≤ T := inf_le_left
  have hB2 : IsPGroup 2 ↥(baum T) := hT.2.1.to_le hBT
  have hEG : E ≤ G := hE.le
  have hBG : baum T ≤ G := hBT.trans hT.1
  set E₂ : Subgroup Γ := (Y.comap X.M.Ψ).map E.subtype with hE₂def
  have hE₂ : ∀ x : Γ, x ∈ E₂ ↔ ∃ hx : x ∈ E, X.M.Ψ ⟨x, hx⟩ ∈ Y := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨x, hx⟩, hy, rfl⟩
  have hE₂E : E₂ ≤ E := fun x hx => ((hE₂ x).1 hx).1
  have hE₂2 : IsPGroup 2 ↥E₂ := by
    intro x
    obtain ⟨hxE, hxY⟩ := (hE₂ x).1 x.2
    have hsq : (X.M.Ψ ⟨(x : Γ), hxE⟩) ^ 2 = 1 := sq_eq_one_of_mem_closure X.hs X.hc hxY
    have hxW : ((x : Γ) ^ 2) ∈ X.M.W := by
      have hxE2 : (x : Γ) ^ 2 ∈ E := E.pow_mem hxE 2
      have h1 : X.M.Ψ ⟨(x : Γ) ^ 2, hxE2⟩ = 1 := by
        have : (⟨(x : Γ) ^ 2, hxE2⟩ : ↥E) = (⟨(x : Γ), hxE⟩ : ↥E) ^ 2 := rfl
        rw [this, map_pow, hsq]
      exact X.M.hker ⟨(x : Γ) ^ 2, hxE2⟩ h1
    obtain ⟨k, hk⟩ := X.M.hW2 ⟨(x : Γ) ^ 2, hxW⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have hk' : ((x : Γ) ^ 2) ^ (2 ^ k) = 1 := by
      have := congrArg (fun z : ↥X.M.W => (z : Γ)) hk
      simpa using this
    show (x : Γ) ^ (2 ^ (k + 1)) = 1
    rw [pow_succ, mul_comm, pow_mul]
    exact hk'
  have hconjE₂ : ∀ b : ↥(baum T), ∀ x ∈ E₂, (b : Γ) * x * (b : Γ)⁻¹ ∈ E₂ := by
    intro b x hx
    obtain ⟨hxE, hxY⟩ := (hE₂ x).1 hx
    have hbx : (b : Γ) * x * (b : Γ)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hBE b.2) x).mp hxE
    refine (hE₂ _).2 ⟨hbx, ?_⟩
    rw [X.Ψ_conj_baum hE b ⟨x, hxE⟩ hbx]
    exact Y.mul_mem (Y.mul_mem (X.hSY b) hxY) (Y.inv_mem (X.hSY b))
  have hBE₂ : baum T ≤ Subgroup.normalizer (E₂ : Set Γ) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hconjE₂ ⟨b, hb⟩ x hx, fun hx => ?_⟩
    have := hconjE₂ ⟨b⁻¹, (baum T).inv_mem hb⟩ _ hx
    have e : ((⟨b⁻¹, (baum T).inv_mem hb⟩ : ↥(baum T)) : Γ) * (b * x * b⁻¹) *
        ((⟨b⁻¹, (baum T).inv_mem hb⟩ : ↥(baum T)) : Γ)⁻¹ = x := by
      show b⁻¹ * (b * x * b⁻¹) * b⁻¹⁻¹ = x
      group
    rwa [e] at this
  set P : Subgroup Γ := baum T ⊔ E₂ with hP
  have hP2 : IsPGroup 2 ↥P := hB2.to_sup_of_normal_right' hE₂2 hBE₂
  have hPG : P ≤ G := sup_le hBG (hE₂E.trans hEG)
  have hBP : baum T ≤ P := le_sup_left
  have hconjP : ∀ e₁ : ↥E, X.M.Ψ e₁ ∈ Subgroup.normalizer (Y : Set (Equiv.Perm (Fin (2 * m + 1)))) →
      ∀ g ∈ P, (e₁ : Γ) * g * (e₁ : Γ)⁻¹ ∈ P := by
    intro e₁ he₁ g hg
    have hgP : g ∈ (↑(baum T ⊔ E₂) : Set Γ) := hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (baum T) E₂ hBE₂] at hgP
    obtain ⟨b, hb, x, hx, rfl⟩ := hgP
    have hxE₂ : (e₁ : Γ) * x * (e₁ : Γ)⁻¹ ∈ E₂ := by
      obtain ⟨hxE, hxY⟩ := (hE₂ x).1 hx
      have h1 : (e₁ : Γ) * x * (e₁ : Γ)⁻¹ ∈ E := E.mul_mem (E.mul_mem e₁.2 hxE) (E.inv_mem e₁.2)
      refine (hE₂ _).2 ⟨h1, ?_⟩
      have : (⟨(e₁ : Γ) * x * (e₁ : Γ)⁻¹, h1⟩ : ↥E) = e₁ * ⟨x, hxE⟩ * e₁⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp he₁ _).mp hxY
    have hbe : (b : Γ) * ((e₁⁻¹ : ↥E) : Γ) * (b : Γ)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hBE hb) _).mp (e₁⁻¹).2
    have hcE : (e₁ : Γ) * ((b : Γ) * ((e₁⁻¹ : ↥E) : Γ) * (b : Γ)⁻¹) ∈ E := E.mul_mem e₁.2 hbe
    have hcE₂ : (e₁ : Γ) * ((b : Γ) * ((e₁⁻¹ : ↥E) : Γ) * (b : Γ)⁻¹) ∈ E₂ := by
      refine (hE₂ _).2 ⟨hcE, ?_⟩
      have h1 : (⟨(e₁ : Γ) * ((b : Γ) * ((e₁⁻¹ : ↥E) : Γ) * (b : Γ)⁻¹), hcE⟩ : ↥E) =
          e₁ * ⟨(b : Γ) * ((e₁⁻¹ : ↥E) : Γ) * (b : Γ)⁻¹, hbe⟩ := rfl
      rw [h1, map_mul, X.Ψ_conj_baum hE ⟨b, hb⟩ (e₁⁻¹) hbe, map_inv]
      have h2 : X.M.Ψ e₁ * (X.S ⟨b, hb⟩ * (X.M.Ψ e₁)⁻¹ * (X.S ⟨b, hb⟩)⁻¹) =
          (X.M.Ψ e₁ * X.S ⟨b, hb⟩ * (X.M.Ψ e₁)⁻¹) * (X.S ⟨b, hb⟩)⁻¹ := by group
      rw [h2]
      exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp he₁ _).mp (X.hSY ⟨b, hb⟩))
        (Y.inv_mem (X.hSY ⟨b, hb⟩))
    have hid : (e₁ : Γ) * ((b : Γ) * x) * (e₁ : Γ)⁻¹ =
        ((e₁ : Γ) * ((b : Γ) * ((e₁⁻¹ : ↥E) : Γ) * (b : Γ)⁻¹) * (b : Γ)) *
          ((e₁ : Γ) * x * (e₁ : Γ)⁻¹) := by
      simp only [Subgroup.coe_inv]
      group
    rw [hid]
    exact P.mul_mem (P.mul_mem ((le_sup_right : E₂ ≤ P) hcE₂) (hBP hb))
      ((le_sup_right : E₂ ≤ P) hxE₂)
  have heP : (e : Γ) ∈ Subgroup.normalizer (P : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconjP e he g hg, fun hg => ?_⟩
    have he' : X.M.Ψ e⁻¹ ∈ Subgroup.normalizer (Y : Set (Equiv.Perm (Fin (2 * m + 1)))) := by
      rw [map_inv]
      exact (Subgroup.normalizer _).inv_mem he
    have := hconjP e⁻¹ he' _ hg
    have e2 : ((e⁻¹ : ↥E) : Γ) * ((e : Γ) * g * (e : Γ)⁻¹) * ((e⁻¹ : ↥E) : Γ)⁻¹ = g := by
      simp only [Subgroup.coe_inv]
      group
    rwa [e2] at this
  exact mem_normalizer_baum_of_pGroup hT hP2 hPG hBP (hEG e.2) heP

end CFSG.CGT.PushingUpLit.BHS7

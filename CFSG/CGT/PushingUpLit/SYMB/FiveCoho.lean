module

public import CFSG.CGT.PushingUpLit.SYMB.Coho5
public import CFSG.CGT.PushingUpLit.BHS6.SymLocalBlock

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement

section General

variable {Γ : Type} [Group Γ] {G T V : Subgroup Γ} {n : ℕ}
  {φ : ↥G →* Equiv.Perm (Fin n)} {ψ : ↥V →* ↥(G6.coreMod n)} {T' : Set (Equiv.Perm (Fin n))}

structure V1Iso (S : SymSetting G T V n φ ψ T') (V₁ : Subgroup Γ) : Prop where
  le : V₁ ≤ V
  normal : G ≤ Subgroup.normalizer (V₁ : Set Γ)
  inj : ∀ v : ↥V, (v : Γ) ∈ V₁ → ψ v = 1 → v = 1
  surj : ∀ w : ↥(G6.coreMod n), ∃ v : ↥V, (v : Γ) ∈ V₁ ∧ ψ v = w

namespace V1Iso

variable {S : SymSetting G T V n φ ψ T'} {V₁ : Subgroup Γ}

theorem psi_conj (hV : V1Iso S V₁) {g : Γ} (hg : g ∈ G) {v : Γ} (hv : v ∈ V₁) :
    ψ ⟨g * v * g⁻¹, S.data.conj_mem hg (hV.le hv)⟩ =
      G6.coreAct n (φ ⟨g, hg⟩) (ψ ⟨v, hV.le hv⟩) :=
  S.data.equivar ⟨g, hg⟩ ⟨v, hV.le hv⟩ _

theorem eq_of_psi_eq (hV : V1Iso S V₁) {v w : Γ} (hv : v ∈ V₁) (hw : w ∈ V₁)
    (h : ψ ⟨v, hV.le hv⟩ = ψ ⟨w, hV.le hw⟩) : v = w := by
  have h1 : (⟨v, hV.le hv⟩ : ↥V) * (⟨w, hV.le hw⟩ : ↥V)⁻¹ = 1 := by
    apply hV.inj
    · exact V₁.mul_mem hv (V₁.inv_mem hw)
    · rw [map_mul, map_inv, h]
      exact mul_inv_cancel _
  have h2 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
  exact mul_inv_eq_one.1 h2

end V1Iso

end General

section Five

variable {Γ : Type} [Group Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}
  {S : SymSetting G T V 5 φ ψ T'} {V₁ E : Subgroup Γ}

theorem crossedHom_principal (hV : V1Iso S V₁) (hEG : E ≤ G)
    (hA : ∀ e (he : e ∈ E), φ ⟨e, hEG he⟩ ∈ alternatingGroup (Fin 5))
    (hs : ∀ σ ∈ alternatingGroup (Fin 5), ∃ e, ∃ he : e ∈ E, φ ⟨e, hEG he⟩ = σ)
    (c : Γ → Γ) (hcV : ∀ e ∈ E, c e ∈ V₁)
    (hcmul : ∀ e ∈ E, ∀ e' ∈ E, c (e * e') = c e * (e * c e' * e⁻¹))
    (hcK : ∀ (e : Γ) (he : e ∈ E), φ ⟨e, hEG he⟩ = 1 → c e = 1) [Finite ↥E] :
    ∃ v ∈ V₁, ∀ e ∈ E, c e = (e * v * e⁻¹) * v⁻¹ := by
  classical
  let η : ↥E →* Equiv.Perm (Fin 5) := φ.comp (Subgroup.inclusion hEG)
  have hη : ∀ e : ↥E, η e = φ ⟨e, hEG e.2⟩ := fun e => rfl
  let c' : ↥E → G6.coreMod 5 := fun e => ψ ⟨c e, hV.le (hcV e e.2)⟩
  have hc' : ∀ e e' : ↥E, c' (e * e') = c' e * (G6.coreAct 5 (η e)) (c' e') := by
    intro e e'
    have h1 : ψ ⟨c ((e * e' : ↥E) : Γ), hV.le (hcV _ (e * e').2)⟩ =
        ψ ⟨c e, hV.le (hcV e e.2)⟩ * ψ ⟨(e : Γ) * c e' * (e : Γ)⁻¹, S.data.conj_mem (hEG e.2)
          (hV.le (hcV e' e'.2))⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      exact hcmul e e.2 e' e'.2
    show ψ ⟨c ((e * e' : ↥E) : Γ), _⟩ = _
    rw [h1, hη, hV.psi_conj (hEG e.2) (hcV e' e'.2)]
  have hker : ∀ e : ↥E, η e = 1 → c' e = 1 := by
    intro e he
    have := hcK e e.2 he
    show ψ ⟨c e, _⟩ = 1
    have h1 : (⟨c e, hV.le (hcV e e.2)⟩ : ↥V) = 1 := Subtype.ext this
    rw [h1, map_one]
  obtain ⟨w, hw⟩ := coho_A5 η (fun e => hA e e.2)
    (fun σ hσ => by
      obtain ⟨e, he, hφ⟩ := hs σ hσ
      exact ⟨⟨e, he⟩, hφ⟩) c' hc' hker
  obtain ⟨v₀, hv₀, hψv₀⟩ := hV.surj w
  refine ⟨v₀, hv₀, fun e he => ?_⟩
  have hconj : (e : Γ) * v₀ * e⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hV.normal (hEG he)) _).mp hv₀
  have hc1 : c e ∈ V₁ := hcV e he
  have hrhs : (e * v₀ * e⁻¹) * (v₀ : Γ)⁻¹ ∈ V₁ := V₁.mul_mem hconj (V₁.inv_mem hv₀)
  apply hV.eq_of_psi_eq hc1 hrhs
  have h1 := hw ⟨e, he⟩
  have h2 : ψ ⟨(e * v₀ * e⁻¹) * (v₀ : Γ)⁻¹, hV.le hrhs⟩ =
      ψ ⟨e * v₀ * e⁻¹, hV.le hconj⟩ * (ψ v₀)⁻¹ := by
    have h3 := map_mul ψ (⟨e * v₀ * e⁻¹, hV.le hconj⟩ : ↥V) v₀⁻¹
    rw [map_inv] at h3
    exact h3
  rw [h2, hV.psi_conj (hEG he) hv₀, hψv₀]
  exact h1

end Five

end CFSG.CGT.PushingUpLit.SYMB

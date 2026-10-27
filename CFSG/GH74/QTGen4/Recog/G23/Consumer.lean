module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import Certificates.Data.G23RecogNativeInputs

public section

namespace CFSG.GH74.QTGen4.Recog.G23

variable {G : Type} [Group G]

theorem mem_sup_of_le_normalizer_aux {K B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ K ⊔ B) :
    ∃ k ∈ K, ∃ b ∈ B, x = k * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ b ∈ B, x = k * b}
      mul_mem' := by
        rintro _ _ ⟨k₁, hk₁, b₁, hb₁, rfl⟩ ⟨k₂, hk₂, b₂, hb₂, rfl⟩
        have hc : b₁ * k₂ * b₁⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hB hb₁) k₂).mp hk₂
        refine ⟨k₁ * (b₁ * k₂ * b₁⁻¹), K.mul_mem hk₁ hc, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
        group
      one_mem' := ⟨1, K.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨k, hk, b, hb, rfl⟩
        have hc : b⁻¹ * k⁻¹ * b⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hB (B.inv_mem hb)) k⁻¹).mp (K.inv_mem hk)
        refine ⟨b⁻¹ * k⁻¹ * b⁻¹⁻¹, hc, b⁻¹, B.inv_mem hb, ?_⟩
        group }
  have hKS : K ≤ S := fun k hk => ⟨k, hk, 1, B.one_mem, by simp⟩
  have hBS : B ≤ S := fun b hb => ⟨1, K.one_mem, b, hb, by simp⟩
  exact (sup_le hKS hBS : K ⊔ B ≤ S) hx

theorem le_normalizer_sup_aux {P A B : Subgroup G}
    (hA : P ≤ Subgroup.normalizer (A : Set G)) (hB : P ≤ Subgroup.normalizer (B : Set G)) :
    P ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hdir : ∀ h ∈ P, ∀ x ∈ A ⊔ B, h * x * h⁻¹ ∈ A ⊔ B := by
    intro h hh
    let S : Subgroup G := (A ⊔ B).comap (MulAut.conj h).toMonoidHom
    have hAS : A ≤ S := fun a ha => by
      have h1 : h * a * h⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hA hh) a).mp ha
      exact (le_sup_left : A ≤ A ⊔ B) h1
    have hBS : B ≤ S := fun b hb => by
      have h1 : h * b * h⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hB hh) b).mp hb
      exact (le_sup_right : B ≤ A ⊔ B) h1
    intro x hx
    exact (sup_le hAS hBS : A ⊔ B ≤ S) hx
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hdir h hh x
  · intro hx
    have h' := hdir h⁻¹ (P.inv_mem hh) _ hx
    have e : h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x := by group
    rw [e] at h'
    exact h'

theorem inv_of_decomp {H K Q B : Subgroup G}
    (hKH : K ≤ H) (hQK : Q ≤ K) (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hQn : H ≤ Subgroup.normalizer (Q : Set G)) (hBH : B ≤ H) (hHKB : H ≤ K ⊔ B)
    (hKQ : ∀ a ∈ K, ∀ b ∈ K, a⁻¹ * b⁻¹ * a * b ∈ Q)
    (hwinv : ∀ w ∈ B, w ∉ Q → ∀ x ∈ K, w * x * w⁻¹ * x ∈ Q) :
    ∀ w ∈ H, w ∉ K → ∀ x ∈ K, w * x * w⁻¹ * x ∈ Q := by
  intro w hwH hwK x hx
  obtain ⟨k, hk, w', hw', rfl⟩ :=
    mem_sup_of_le_normalizer_aux (hBH.trans hHK) (hHKB hwH)
  have hkH : k ∈ H := hKH hk
  have hw'Q : w' ∉ Q := fun hq => hwK (K.mul_mem hk (hQK hq))
  have hy := hwinv w' hw' hw'Q x hx
  have hyk := (Subgroup.mem_normalizer_iff.mp (hQn hkH) _).mp hy
  have hc := hKQ k⁻¹ (K.inv_mem hk) x hx
  rw [inv_inv] at hc
  have e : k * w' * x * (k * w')⁻¹ * x =
      (k * (w' * x * w'⁻¹ * x) * k⁻¹) * (k * x⁻¹ * k⁻¹ * x) := by group
  rw [e]
  exact Q.mul_mem hyk hc

end CFSG.GH74.QTGen4.Recog.G23

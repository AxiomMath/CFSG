module

public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndL34Model
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitAssembly46e

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

theorem EndB.card_center_le_of_isSylowOf {P Q : Subgroup X} (hP : IsSylowOf 2 P ⊤)
    (hQ : IsSylowOf 2 Q ⊤) :
    Nat.card ↥(Q ⊓ centralizer (Q : Set X)) ≤ Nat.card ↥(P ⊓ centralizer (P : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := GH74.GLS.C3.Layer2.exists_mem_conj_le_of_isSylowOf hP le_top hQ.isPGroup
  set φ := (MulAut.conj k⁻¹).toMonoidHom with hφ
  have hφy : ∀ y, φ y = k⁻¹ * y * k := fun y => by
    rw [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hle : Q.map φ ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    rw [hφy]
    exact hk y hy
  have hQP : Q.map φ = P := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hP.card_eq, hQ.card_eq]
  have hZ : (Q ⊓ centralizer (Q : Set X)).map φ ≤ P ⊓ centralizer (P : Set X) := by
    rintro _ ⟨y, ⟨hyQ, hyC⟩, rfl⟩
    refine ⟨hle ⟨y, hyQ, rfl⟩, mem_centralizer_iff.mpr fun x hx => ?_⟩
    rw [← hQP] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp hyC) x' hx']
  calc Nat.card ↥(Q ⊓ centralizer (Q : Set X)) =
        Nat.card ↥((Q ⊓ centralizer (Q : Set X)).map φ) :=
      (Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective).symm
    _ ≤ _ := Subgroup.card_le_of_le hZ

namespace Setting46e

theorem z_mem_center_V (hs : Setting46e t L p f S w z V i j) :
    z ∈ V ⊓ centralizer (V : Set X) := by
  refine ⟨hs.le_V hs.setup.z_mem.1, mem_centralizer_iff.mpr fun v hv => ?_⟩
  have h := hs.setup.conj_z_of_mem_normalizer_T (hs.sylow_V.le hv)
  calc v * z = v * z * v⁻¹ * v := by group
    _ = z * v := by rw [h]

theorem center_V_le (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j) :
    V ⊓ centralizer (V : Set X) ≤
      closure ({w ^ (orderOf w / 2) * t ^ i * z ^ j, z} : Set X) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  intro x hx
  have hxX := hs.setup.center_V_le_X hKC hs.sylow_V hs.le_V hx
  rcases hs.setup.mem_closure_beta_z_or (beta_mem_X i j) hs.beta.not_mem hxX with h | h
  · exact h
  · exfalso
    obtain ⟨v, hvU, hvS, -, hvt⟩ := hs.beta.exists_mem
    have hvc := hs.setup.closure_beta_z_le_centralizer hs.sylow_V hvU h
    have hvx : v * x = x * v := (mem_centralizer_iff.mp hx.2) v hvU.1
    have hvc' : v * (t⁻¹ * x) = (t⁻¹ * x) * v := (mem_centralizer_singleton_iff.mp hvc).symm
    have htv : v * t * v⁻¹ = t := by
      have h1 : v * t⁻¹ * v⁻¹ = t⁻¹ := by
        calc v * t⁻¹ * v⁻¹ = v * (t⁻¹ * x) * v⁻¹ * (v * x⁻¹ * v⁻¹) := by group
          _ = (t⁻¹ * x) * x⁻¹ := by
            rw [hvc', show v * x⁻¹ * v⁻¹ = x⁻¹ by
              calc v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
                _ = x⁻¹ := by rw [hvx]; group]
            group
          _ = t⁻¹ := by group
      calc v * t * v⁻¹ = (v * t⁻¹ * v⁻¹)⁻¹ := by group
        _ = t := by rw [h1, inv_inv]
    have hz1 := hs.setup.z_ne_one
    have hβz := hs.beta.ne_one
    rcases hvt with h1 | h1 <;> rw [htv] at h1
    · exact hz1 (by
        calc z = t⁻¹ * (t * z) := by group
          _ = 1 := by rw [← h1]; group)
    · have : β * z = 1 := by
        calc β * z = t⁻¹ * (t * β * z) := by group
          _ = 1 := by rw [← h1]; group
      have hβ2 : β * β = 1 := by
        rw [← sq]
        exact hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
      have hβz' : β = z := by
        have h2 : z = β⁻¹ := eq_inv_of_mul_eq_one_right this
        rw [h2, inv_eq_of_mul_eq_one_right hβ2]
      exact hs.setup.beta_ne_z hs.beta hβz'

theorem center_V_le_of_not_mem (hKC : AutPSL2CentralizerInput)
    (hs : Setting46e t L p f S w z V i j)
    (hβ : w ^ (orderOf w / 2) * t ^ i * z ^ j ∉ V ⊓ centralizer (V : Set X)) :
    V ⊓ centralizer (V : Set X) ≤ zpowers z := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβd
  intro x hx
  have hzV := hs.z_mem_center_V
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hβzc : β * z = z * β :=
    (mem_centralizer_singleton_iff.mp (K_le_centralizer_beta i j hs.lemma45.z_mem.2)).symm
  rcases mem_closure_pair hβ2 hz2 hβzc (hs.center_V_le hKC hx) with h | h | h | h
  · rw [h]; exact one_mem _
  · exact absurd (h ▸ hx) hβ
  · rw [h]; exact mem_zpowers z
  · exfalso
    apply hβ
    have : β = x * z⁻¹ := by rw [h]; group
    rw [this]
    exact mul_mem hx (inv_mem hzV)

theorem conj_t_mem_of_relIndex_two (hs : Setting46e t L p f S w z V i j)
    (hSV : S.relIndex V = 2) {v : X} (hv : v ∈ V) :
    v * t * v⁻¹ = t ∨ v * t * v⁻¹ = t * z ∨
      v * t * v⁻¹ = t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * z := by
  obtain ⟨v₁, hv₁U, hv₁S, -, hv₁t⟩ := hs.beta.exists_mem
  have htS : ∀ s ∈ S, s * t * s⁻¹ = t := fun s hs' => by
    have := mem_centralizer_singleton_iff.mp (hs.sylow.le hs')
    rw [this]; group
  by_cases hvS : v ∈ S
  · exact Or.inl (htS v hvS)
  · have hmem := inv_mul_mem_of_relIndex_two hSV hv₁U.1 hv hv₁S hvS
    have : v * t * v⁻¹ = v₁ * t * v₁⁻¹ := by
      calc v * t * v⁻¹ = v₁ * ((v₁⁻¹ * v) * t * (v₁⁻¹ * v)⁻¹) * v₁⁻¹ := by group
        _ = v₁ * t * v₁⁻¹ := by rw [htS _ hmem]
    rw [this]
    exact Or.inr hv₁t

theorem conj_t_ne_t_mul_beta (hKF : AutPSL2FusionInput) (hs : Setting46e t L p f S w z V i j)
    (hSV : S.relIndex V = 2) (g : X) :
    g * t * g⁻¹ ≠ t * (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβd
  intro hg
  have hβX : β ∈ closure {t, w ^ (orderOf w / 2), z} := beta_mem_X i j
  have htX : t ∈ closure {t, w ^ (orderOf w / 2), z} := subset_closure (by simp)
  have hgX : g * t * g⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} := hg ▸ mul_mem htX hβX
  obtain ⟨v, hvV, hvt⟩ := hs.setup.exists_conj_V_of_mem_X hKF hs.sylow_V hgX
  rw [hg] at hvt
  rcases hs.conj_t_mem_of_relIndex_two hSV hvV with h | h | h <;> rw [hvt] at h
  · exact hs.beta.ne_one (by
      calc β = t⁻¹ * (t * β) := by group
        _ = 1 := by rw [h]; group)
  · exact hs.setup.beta_ne_z hs.beta (by
      calc β = t⁻¹ * (t * β) := by group
        _ = z := by rw [h]; group)
  · exact hs.setup.z_ne_one (by
      calc z = (t * β)⁻¹ * (t * β * z) := by group
        _ = 1 := by rw [← h]; group)

end Setting46e

end CFSG.ComponentClassification.HarrisLit

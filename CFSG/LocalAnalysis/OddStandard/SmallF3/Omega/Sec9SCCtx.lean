module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCCore
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMCentB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B E1 : Subgroup G}

theorem sec9c_exists_noncomm (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hctx : Sec9E1 G t L S z g B t₀ E1) :
    ∃ e ∈ E1, e * t ≠ t * e := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨-, -, -, h4, hv, -⟩ :=
    asc82Lemma9N_of h36 h68 hB8 hT G t L S z g B t₀ hctx.choice
  have hMB := sec9m_M_cent_B hT h6 hctx
  refine sec9m_E1_not_le_A hctx (fun e he => ?_)
  have heM : e ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) := Subgroup.mem_sup_left he
  have hle : zpowers t ⊔ B ≤ centralizer ({e} : Set G) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcon e he
    · intro b hb
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hMB e heM b hb
  have hecent : e ∈ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.mp (hle hx) e (Set.mem_singleton e)).symm
  have heA : e ∈ centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) := by
    rw [h4]
    exact ⟨hctx.le_N he, hecent⟩
  exact sec9m_E1_cent_A hctx hv e he heA.2

theorem sec9c_ctx_core (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hctx : Sec9E1 G t L S z g B t₀ E1)
    {K : Subgroup G} {T : Set G} (hTN : ∀ x ∈ T, x ∈ centMod (Asub9 t t₀ B) B)
    (hTK : ∀ x ∈ T, x ∈ K)
    (hMK : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), ∀ k ∈ K, m * k * m⁻¹ ∈ K)
    (hirr : ∀ B' : Subgroup G, B' ≤ B → (∀ x ∈ T, ∀ c ∈ B', x * c * x⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = B) :
    2 ^ 8 ∣ Nat.card ↥((E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)) ⊓ K) := by
  have hO_le_N : oddCoreIn (centMod (Asub9 t t₀ B) B) ≤ centMod (Asub9 t t₀ B) B :=
    (oddCoreIn_normal _).1
  have hM_le_N : E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) ≤ centMod (Asub9 t t₀ B) B :=
    sup_le hctx.le_N hO_le_N
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b :=
    fun b hb b' hb' => CFSG.Open.IsElemAbelian.comm hctx.choice.B_e16.1 hb hb'
  have hMB := sec9m_M_cent_B hT h6 hctx
  have htA : t ∈ Asub9 t t₀ B := by
    rw [Asub9]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have ht0A : t₀ ∈ Asub9 t t₀ B := by
    rw [Asub9]
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t₀))
  have ha_t : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B),
      m * t * m⁻¹ * t⁻¹ ∈ B := fun m hm => (hM_le_N hm).2 t htA
  have ha_t0 : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B),
      m * t₀ * m⁻¹ * t₀⁻¹ ∈ B := fun m hm => (hM_le_N hm).2 t₀ ht0A
  obtain ⟨f₁, hf₁⟩ := sec9m_exists_commHom
    (M := E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)) (B := B) (a := t) hBc hMB ha_t
  obtain ⟨f₂, hf₂⟩ := sec9m_exists_commHom
    (M := E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)) (B := B) (a := t₀) hBc hMB ha_t0
  have hB_le_A : B ≤ Asub9 t t₀ B := by
    rw [Asub9]
    exact le_sup_right
  have hBM : B ≤ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) :=
    le_trans (le_trans hB_le_A hctx.A_le) le_sup_left
  have hTB : ∀ x ∈ T, x ∈ normalizer (B : Set G) := fun x hx => (hTN x hx).1
  have hTM : ∀ x ∈ T, ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B),
      x * m * x⁻¹ ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) :=
    fun x hx m hm =>
      (Subgroup.normal_subgroupOf_iff hM_le_N).mp hctx.normal m x hm (hTN x hx)
  have hker : ∀ b : ↥(E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)),
      (b : G) ∈ B → f₁ b = 1 ∧ f₂ b = 1 := by
    intro b hb
    constructor
    · apply Subtype.ext
      rw [hf₁ b, Subgroup.coe_one]
      have hcomm : (b : G) * t = t * (b : G) :=
        (sec9n_t_B hctx.choice.toSec9Ctx (b : G) hb).symm
      rw [hcomm]; group
    · apply Subtype.ext
      rw [hf₂ b, Subgroup.coe_one]
      have hcomm : (b : G) * t₀ = t₀ * (b : G) := (hctx.choice.t0_B (b : G) hb).symm
      rw [hcomm]; group
  have hequiv : ∀ x ∈ T, ∀ (m : ↥(E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)))
      (hm : x * (m : G) * x⁻¹ ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)),
      ((f₁ ⟨x * (m : G) * x⁻¹, hm⟩ : ↥B) : G) = x * ((f₁ m : ↥B) : G) * x⁻¹ ∧
        ((f₂ ⟨x * (m : G) * x⁻¹, hm⟩ : ↥B) : G) = x * ((f₂ m : ↥B) : G) * x⁻¹ := by
    intro x hx m hm
    have hna_t : x⁻¹ * t * x * t⁻¹ ∈ B := by
      have h := (inv_mem (hTN x hx)).2 t htA
      simpa using h
    have hna_t0 : x⁻¹ * t₀ * x * t₀⁻¹ ∈ B := by
      have h := (inv_mem (hTN x hx)).2 t₀ ht0A
      simpa using h
    constructor
    · calc ((f₁ ⟨x * (m : G) * x⁻¹, hm⟩ : ↥B) : G)
          = (x * (m : G) * x⁻¹) * t * (x * (m : G) * x⁻¹)⁻¹ * t⁻¹ :=
            hf₁ ⟨x * (m : G) * x⁻¹, hm⟩
        _ = x * ((m : G) * t * (m : G)⁻¹ * t⁻¹) * x⁻¹ :=
            sec9m_conj_comm hBc hna_t (hMB (m : G) m.2) (ha_t (m : G) m.2)
        _ = x * ((f₁ m : ↥B) : G) * x⁻¹ := by rw [hf₁ m]
    · calc ((f₂ ⟨x * (m : G) * x⁻¹, hm⟩ : ↥B) : G)
          = (x * (m : G) * x⁻¹) * t₀ * (x * (m : G) * x⁻¹)⁻¹ * t₀⁻¹ :=
            hf₂ ⟨x * (m : G) * x⁻¹, hm⟩
        _ = x * ((m : G) * t₀ * (m : G)⁻¹ * t₀⁻¹) * x⁻¹ :=
            sec9m_conj_comm hBc hna_t0 (hMB (m : G) m.2) (ha_t0 (m : G) m.2)
        _ = x * ((f₂ m : ↥B) : G) * x⁻¹ := by rw [hf₂ m]
  have hne : ∃ m : ↥(E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B)),
      f₁ m ≠ 1 ∨ f₂ m ≠ 1 := by
    obtain ⟨e, he, hene⟩ := sec9c_exists_noncomm h36 h68 hB8 hT h6 hctx
    refine ⟨⟨e, Subgroup.mem_sup_left he⟩, Or.inl ?_⟩
    intro hf1
    apply hene
    have h1 : ((f₁ ⟨e, Subgroup.mem_sup_left he⟩ : ↥B) : G) = 1 := by
      rw [hf1, Subgroup.coe_one]
    rw [hf₁ ⟨e, Subgroup.mem_sup_left he⟩] at h1
    calc e * t = e * t * e⁻¹ * e := by group
      _ = t * e := by rw [mul_inv_eq_one.mp h1]
  exact sec9c_core hctx.choice.B_e16 hBM hTB hTM hTK hMK hirr f₁ f₂ hker hequiv hne

end CFSG.OddStandard.SmallF3.Omega

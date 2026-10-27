module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBH

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)
open CFSG.ComponentClassification.HSFLit (HaradaInput ElemAbelianTwo)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable {Δ : LocalDatum X A}

namespace TwoBSplit

variable {φ : Δ.Fusion} (B : TwoBSplit φ)

theorem T₁_eq : B.T₁ = (φ.T : Subgroup X) := by
  by_contra hne
  have hnil : Group.IsNilpotent ↥(φ.T : Subgroup X) := φ.T.isPGroup'.isNilpotent
  have hlt : B.T₁.subgroupOf φ.T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm B.T₁_le fun y hy => ?_)
    have : (⟨y, hy⟩ : ↥(φ.T : Subgroup X)) ∈ B.T₁.subgroupOf φ.T := h ▸ mem_top _
    exact this
  obtain ⟨⟨y, hyT⟩, hyN, hyT₁⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyT₁' : y ∉ B.T₁ := fun h => hyT₁ (mem_subgroupOf.mpr h)
  have hconj : ∀ g ∈ B.T₁, y * g * y⁻¹ ∈ B.T₁ := fun g hg => by
    have := (mem_normalizer_iff.mp hyN ⟨g, B.T₁_le hg⟩).mp (mem_subgroupOf.mpr hg)
    exact mem_subgroupOf.mp this
  have hconj' : ∀ g ∈ B.T₁, y⁻¹ * g * y ∈ B.T₁ := fun g hg => by
    have hgT : y⁻¹ * g * y ∈ (φ.T : Subgroup X) :=
      mul_mem (mul_mem (inv_mem hyT) (B.T₁_le hg)) hyT
    have := (mem_normalizer_iff.mp hyN ⟨_, hgT⟩).mpr (mem_subgroupOf.mpr (by
      change y * (y⁻¹ * g * y) * y⁻¹ ∈ B.T₁
      rw [show y * (y⁻¹ * g * y) * y⁻¹ = g by group]
      exact hg))
    exact mem_subgroupOf.mp this
  have htzT₁ : Δ.t * Δ.dz ∈ B.T₁ := B.S_T₁ (mul_mem Δ.t_mem (Δ.D_le Δ.dz_mem))
  have hytz : y * (Δ.t * Δ.dz) * y⁻¹ = Δ.t * Δ.dz := by
    refine (B.eq_of_central_T₁ (hconj _ htzT₁) fun g hg => ?_).resolve_left fun h => ?_
    · have h := B.tz_central (hconj' g hg)
      calc y * (Δ.t * Δ.dz) * y⁻¹ * g = y * (Δ.t * Δ.dz * (y⁻¹ * g * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * g * y) * (Δ.t * Δ.dz)) * y⁻¹ := by rw [h]
        _ = g * (y * (Δ.t * Δ.dz) * y⁻¹) := by group
    · apply Δ.tz_ne_one
      calc Δ.t * Δ.dz = y⁻¹ * (y * (Δ.t * Δ.dz) * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
  have hyt : y * Δ.t * y⁻¹ = Δ.t ∨ y * Δ.t * y⁻¹ = Δ.dz := by
    refine B.eq_of_comm_T₁ (hconj _ (B.S_T₁ Δ.t_mem)) (fun h => Δ.t_ne_one ?_) (fun h => ?_)
      fun g hg => ?_
    · calc Δ.t = y⁻¹ * (y * Δ.t * y⁻¹) * y := by group
        _ = 1 := by rw [h]; group
    · apply Δ.dz_ne_one
      have h' : y * Δ.t * y⁻¹ = y * (Δ.t * Δ.dz) * y⁻¹ := by rw [h, hytz]
      have : Δ.t = Δ.t * Δ.dz := by
        calc Δ.t = y⁻¹ * (y * Δ.t * y⁻¹) * y := by group
          _ = y⁻¹ * (y * (Δ.t * Δ.dz) * y⁻¹) * y := by rw [h']
          _ = Δ.t * Δ.dz := by group
      calc Δ.dz = Δ.t⁻¹ * (Δ.t * Δ.dz) := by group
        _ = 1 := by rw [← this, inv_mul_cancel]
    · have hg' := hconj' g hg
      have he : g * (y * Δ.t * y⁻¹) * g⁻¹ =
          y * ((y⁻¹ * g * y) * Δ.t * (y⁻¹ * g * y)⁻¹) * y⁻¹ := by group
      rcases B.conj_t_T₁ hg' with h | h
      · left
        rw [he, h]
      · right
        rw [he, h]
        have htt : Δ.t * Δ.t = 1 := by rw [← pow_two, Δ.t_sq]
        calc y * Δ.dz * y⁻¹ = y * (Δ.t * Δ.t) * Δ.dz * y⁻¹ := by rw [htt, mul_one]
          _ = y * Δ.t * y⁻¹ * (y * (Δ.t * Δ.dz) * y⁻¹) := by group
          _ = y * Δ.t * y⁻¹ * (Δ.t * Δ.dz) := by rw [hytz]
  apply hyT₁'
  rcases hyt with h | h
  · exact B.S_T₁ (Δ.mem_S_of_conj_t φ.isPGroup φ.le hyT h)
  · have h' : B.e⁻¹ * y * Δ.t * (B.e⁻¹ * y)⁻¹ = Δ.t := by
      calc B.e⁻¹ * y * Δ.t * (B.e⁻¹ * y)⁻¹ = B.e⁻¹ * (y * Δ.t * y⁻¹) * B.e⁻¹⁻¹ := by group
        _ = B.e * (y * Δ.t * y⁻¹) * B.e⁻¹ := by rw [inv_inv, B.e_inv]
        _ = Δ.t := by rw [h, B.conj_e_dz]
    have hmem := Δ.mem_S_of_conj_t φ.isPGroup φ.le
      (mul_mem (inv_mem B.e_mem) hyT) h'
    have : y = B.e * (B.e⁻¹ * y) := by group
    rw [this]
    exact mul_mem B.e_T₁ (B.S_T₁ hmem)

theorem centralizer_E_S {y : X} (hyS : y ∈ Δ.S) (hyE : ∀ g ∈ B.E, y * g = g * y) : y ∈ B.E := by
  obtain ⟨a, ha, b, hb, rfl⟩ := B.decomp _ hyS
  have hye := hyE _ mem_E8_right
  have hybb := hyE _ mem_E8_mid
  have hx2b : φ.x ^ 2 * b * (φ.x ^ 2)⁻¹ ∈ Δ.D := Δ.conj_mem_D _ φ.sq_mem b hb
  have ha' : B.d₀⁻¹ * a * B.d₀ ∈ Δ.D := by
    simpa using Δ.conj_mem_D _ (inv_mem B.d₀S) a ha
  have h1 : B.e * (a * (φ.x * b * φ.x⁻¹)) * B.e⁻¹ =
      (φ.x ^ 2 * b * (φ.x ^ 2)⁻¹) * (φ.x * (B.d₀⁻¹ * a * B.d₀) * φ.x⁻¹) := by
    calc B.e * (a * (φ.x * b * φ.x⁻¹)) * B.e⁻¹ =
        (B.e * a * B.e⁻¹) * (B.e * (φ.x * b * φ.x⁻¹) * B.e⁻¹) := by group
      _ = (φ.x * (B.d₀⁻¹ * a * B.d₀) * φ.x⁻¹) * (φ.x ^ 2 * b * (φ.x ^ 2)⁻¹) := by
          rw [B.conj_e_D, B.conj_e_D1 hb]
      _ = _ := (B.comm₁ hx2b ha').symm
  have h2 : B.e * (a * (φ.x * b * φ.x⁻¹)) * B.e⁻¹ = a * (φ.x * b * φ.x⁻¹) := by
    rw [← hye]; group
  rw [h1] at h2
  have hb' := (B.uniq hx2b ha ha' hb h2).2
  have hcomm : a * Δ.db = Δ.db * a := by
    have hL : a * (φ.x * b * φ.x⁻¹) * (Δ.db * B.b₁) =
        (a * Δ.db) * (φ.x * (b * B.db') * φ.x⁻¹) := by
      rw [B.b₁_eq]
      calc a * (φ.x * b * φ.x⁻¹) * (Δ.db * (φ.x * B.db' * φ.x⁻¹)) =
          a * ((φ.x * b * φ.x⁻¹) * Δ.db) * (φ.x * B.db' * φ.x⁻¹) := by group
        _ = a * (Δ.db * (φ.x * b * φ.x⁻¹)) * (φ.x * B.db' * φ.x⁻¹) := by
            rw [B.comm₁ Δ.db_mem hb]
        _ = (a * Δ.db) * (φ.x * (b * B.db') * φ.x⁻¹) := by group
    have hR : Δ.db * B.b₁ * (a * (φ.x * b * φ.x⁻¹)) =
        (Δ.db * a) * (φ.x * (B.db' * b) * φ.x⁻¹) := by
      rw [B.b₁_eq]
      calc Δ.db * (φ.x * B.db' * φ.x⁻¹) * (a * (φ.x * b * φ.x⁻¹)) =
          Δ.db * ((φ.x * B.db' * φ.x⁻¹) * a) * (φ.x * b * φ.x⁻¹) := by group
        _ = Δ.db * (a * (φ.x * B.db' * φ.x⁻¹)) * (φ.x * b * φ.x⁻¹) := by
            rw [B.comm₁ ha B.db'_mem]
        _ = (Δ.db * a) * (φ.x * (B.db' * b) * φ.x⁻¹) := by group
    have := hybb
    rw [hL, hR] at this
    exact (B.uniq (mul_mem ha Δ.db_mem) (mul_mem Δ.db_mem ha) (mul_mem hb B.db'_mem)
      (mul_mem B.db'_mem hb) this).1
  have hy : a * (φ.x * b * φ.x⁻¹) = a * (B.e * a * B.e⁻¹) := by
    rw [B.conj_e_D, hb']
  rw [hy]
  have hzb₁ : Δ.dz * B.b₁ = B.b₁ * Δ.dz := by
    rw [B.b₁_eq]; exact B.comm₁ Δ.dz_mem B.db'_mem
  rcases Δ.mem_of_commute_db ha hcomm with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one, mul_inv_cancel]; exact one_mem _
  · rw [B.conj_e_dz, Δ.commute_t (Δ.D_le Δ.dz_mem)]
    exact mem_E8_left
  · exact mem_E8_mid
  · have : Δ.db * Δ.dz * (B.e * (Δ.db * Δ.dz) * B.e⁻¹) = Δ.db * B.b₁ * (Δ.t * Δ.dz) := by
      calc Δ.db * Δ.dz * (B.e * (Δ.db * Δ.dz) * B.e⁻¹) =
          Δ.db * Δ.dz * (B.b₁ * (B.e * Δ.dz * B.e⁻¹)) := by simp only [b₁]; group
        _ = Δ.db * (Δ.dz * B.b₁) * Δ.t := by rw [B.conj_e_dz]; group
        _ = Δ.db * B.b₁ * (Δ.t * Δ.dz) := by
            rw [hzb₁, mul_assoc, mul_assoc, ← Δ.commute_t (Δ.D_le Δ.dz_mem)]; group
    rw [this]
    exact mul_mem mem_E8_mid mem_E8_left

theorem centralizer_E {y : X} (hyT : y ∈ (φ.T : Subgroup X))
    (hyE : ∀ g ∈ B.E, y * g = g * y) : y ∈ B.E := by
  rw [← B.T₁_eq] at hyT
  rcases B.mem_T₁ hyT with h | h
  · exact B.centralizer_E_S h hyE
  · have hs := B.centralizer_E_S h fun g hg => by
      rw [mul_assoc, B.elem_E.comm _ mem_E8_right g hg, ← mul_assoc, hyE g hg, mul_assoc]
    have := mul_mem hs (mem_E8_right (a := Δ.t * Δ.dz) (b := Δ.db * B.b₁))
    rwa [← B.eq_mul_e] at this

include B in
theorem false_of_harada_split (hH : HaradaInput) (hX : ¬ SectionalRankLeFour X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hX
  refine HSFLit.gen4_of_harada hH φ.T (E8_le (φ.le (mul_mem Δ.t_mem (Δ.D_le Δ.dz_mem)))
    (φ.le B.bb_S) B.e_mem) B.elem_E B.card_E fun y hy hyE => B.centralizer_E hy hyE

end TwoBSplit

end LocalDatum

end CFSG.ComponentClassification.HSDihedral

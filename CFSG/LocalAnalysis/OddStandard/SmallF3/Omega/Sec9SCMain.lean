module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCCos
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SNoE1
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMThm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B E1 : Subgroup G}

private theorem sec9c_layerCent_le (L : Subgroup G) (s : G) : layerCent L s ≤ L :=
  (Subgroup.map_subtype_le (CFSG.layer ↥(L ⊓ centralizer ({s} : Set G)))).trans inf_le_left

theorem sec9c_exists_outer (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hN : Asc82NormA6)
    (hctx : Sec9E1 G t L S z g B t₀ E1) :
    ∃ s ∈ Asub9 t t₀ B, orderOf s = 2 ∧ ¬ InnerOn L s ∧ s ∉ zpowers t ⊔ B ∧
      ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), m * s = s * m := by
  obtain ⟨s, hsA, hsn, hsM⟩ := sec9m_exists_cent h36 h68 hB8 hT h6 hN hctx
  have hc : Sec9Ctx G t L S z g B t₀ := hctx.choice.toSec9Ctx
  have hLM : IsOm6M L := ⟨hc.toSec3SettingLB.component.isQuasisimple, hc.omega6m⟩
  refine ⟨s, hsA, ?_, ?_, hsn, hsM⟩
  · have hss : s * s = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one (sec9n_A_elem hc) hsA
    have hs1 : s ≠ 1 := fun h => hsn (h ▸ (zpowers t ⊔ B).one_mem)
    exact orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  · intro hin
    have hin' : s ∈ L ⊔ centralizer (L : Set G) := hin
    have hI := sec9n_A8_le_inner hc
    have hBI : ∀ b ∈ B, b ∈ L ⊔ centralizer (L : Set G) := fun b hb =>
      hI (Subgroup.mem_sup_right hb)
    have ht0 : ¬ InnerOn L t₀ := hT.i3_outer G L hLM t₀ (sec9n_t0_mem_normalizer hc) hc.t0_type
    obtain ⟨b, hb, h | h | h | h⟩ := sec9n_mem_A hc hsA
    · exact hsn (h ▸ Subgroup.mem_sup_right hb)
    · exact hsn (h ▸ (zpowers t ⊔ B).mul_mem (Subgroup.mem_sup_left (mem_zpowers t))
        (Subgroup.mem_sup_right hb))
    · refine ht0 ?_
      have : t₀ = s * b⁻¹ := by rw [h]; group
      rw [InnerOn, this]
      exact (L ⊔ centralizer (L : Set G)).mul_mem hin' ((L ⊔ centralizer (L : Set G)).inv_mem
        (hBI b hb))
    · refine ht0 ?_
      have htI : t ∈ L ⊔ centralizer (L : Set G) :=
        hI (Subgroup.mem_sup_left (mem_zpowers t))
      have : t₀ = t⁻¹ * s * b⁻¹ := by rw [h]; group
      rw [InnerOn, this]
      exact (L ⊔ centralizer (L : Set G)).mul_mem
        ((L ⊔ centralizer (L : Set G)).mul_mem ((L ⊔ centralizer (L : Set G)).inv_mem htI) hin')
        ((L ⊔ centralizer (L : Set G)).inv_mem (hBI b hb))

theorem asc82Sec9NoE1_of (hsh : Asc82Shapes) (h36 : Asc82Lemma36) (h68 : Asc82Lemma68)
    (hB8 : Asc82Sec8B) (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hN : Asc82NormA6)
    (hCos : Asc82Sec9Cos) : Asc82Sec9NoE1 := by
  intro G _ _ t L S z g B t₀ E1 hctx
  have hc : Sec9Ctx G t L S z g B t₀ := hctx.choice.toSec9Ctx
  have hS3 : Sec3SettingLB G t L := hc.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS3.component.isQuasisimple, hc.omega6m⟩
  have hB16 : IsElemAb2 B 4 := hc.B_e16
  obtain ⟨s, hsA, hs2, hsout, hsnot, hsM⟩ := sec9c_exists_outer h36 h68 hB8 hT h6 hN hctx
  have hsN : s ∈ normalizer (L : Set G) := sec9n_A_mem_normalizer hc s hsA
  have hMB := sec9m_M_cent_B hT h6 hctx
  have hAcomm : ∀ a ∈ Asub9 t t₀ B, ∀ a' ∈ Asub9 t t₀ B, a * a' = a' * a :=
    fun a ha a' ha' => CFSG.Open.IsElemAbelian.comm (sec9n_A_elem hc) ha ha'
  have hBA : B ≤ Asub9 t t₀ B := le_sup_right
  have htA : t ∈ Asub9 t t₀ B :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))
  have hsB : ∀ b ∈ B, s * b = b * s := fun b hb => hAcomm s hsA b (hBA hb)
  have hBL : B ≤ L := fun b hb => (hc.B_le hb).1
  obtain ⟨P, hP, hBP⟩ := sec68_exists_sylow_ge (IsPGroup.of_card hB16.2) hBL
  obtain ⟨b₀, hb₀, α, hα⟩ := hCos.exists_i1 G L hLM P hP B hBP hB16 s hs2 hsN hsB hsout
  obtain ⟨s', hs'eq⟩ : ∃ s' : G, s' = s * b₀ := ⟨_, rfl⟩
  rw [← hs'eq] at hα
  have hs'A : s' ∈ Asub9 t t₀ B := by
    rw [hs'eq]; exact (Asub9 t t₀ B).mul_mem hsA (hBA hb₀)
  have hs'2 : orderOf s' = 2 := by
    have hss : s' * s' = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one (sec9n_A_elem hc) hs'A
    have hs1 : s' ≠ 1 := by
      intro h
      apply hsnot
      have hsb : s = b₀⁻¹ := by
        rw [hs'eq] at h
        exact mul_eq_one_iff_eq_inv.mp h
      rw [hsb]
      exact Subgroup.mem_sup_right (B.inv_mem hb₀)
    exact orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hs'N : s' ∈ normalizer (L : Set G) := sec9n_A_mem_normalizer hc s' hs'A
  have hs'B : ∀ b ∈ B, s' * b = b * s' := fun b hb => hAcomm s' hs'A b (hBA hb)
  have hs't : s' ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm t htA s' hs'A).symm
  have hMs' : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), m * s' = s' * m := by
    intro m hm
    rw [hs'eq]
    calc m * (s * b₀) = (m * s) * b₀ := by rw [mul_assoc]
      _ = (s * m) * b₀ := by rw [hsM m hm]
      _ = s * (m * b₀) := by rw [mul_assoc]
      _ = s * (b₀ * m) := by rw [hMB m hm b₀ hb₀]
      _ = (s * b₀) * m := by rw [mul_assoc]
  obtain ⟨K, hJK, hKnorm, hK8⟩ :=
    sec9c_exists_K hsh h36 h6 hS3 hc.omega6m hs'2 hs't ⟨α, hα⟩
  let T : Set G :=
    {x | x ∈ layerCent L s' ⊓ normalizer (B : Set G) ∧ ∃ j : ℕ, x ^ (2 ^ j) = 1}
  have hTN : ∀ x ∈ T, x ∈ centMod (Asub9 t t₀ B) B := by
    rintro x ⟨⟨hxJ, hxB⟩, j, hxj⟩
    exact sec9m_lift hT hc (sec9c_layerCent_le L s' hxJ) hxB hxj
  have hTK : ∀ x ∈ T, x ∈ K := fun x hx => hJK hx.1.1
  have hMK : ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), ∀ k ∈ K, m * k * m⁻¹ ∈ K :=
    fun m hm k hk =>
      hKnorm m (Subgroup.mem_centralizer_singleton_iff.mpr (hMs' m hm)) k hk
  have hirr : ∀ B' : Subgroup G, B' ≤ B → (∀ x ∈ T, ∀ c ∈ B', x * c * x⁻¹ ∈ B') →
      B' = ⊥ ∨ B' = B := fun B' hB'B hinv =>
    hCos.irred G L hLM P hP B hBP hB16 s' hs'2 hs'N hs'B ⟨α, hα⟩ B' hB'B
      (fun x hx hx2 c hc' => hinv x ⟨hx, hx2⟩ c hc')
  have hdvd := sec9c_ctx_core h36 h68 hB8 hT h6 hctx hTN hTK hMK hirr
  exact hK8 (dvd_trans hdvd (Subgroup.card_dvd_of_le inf_le_right))

end CFSG.OddStandard.SmallF3.Omega

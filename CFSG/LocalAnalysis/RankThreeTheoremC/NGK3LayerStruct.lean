module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3LayerUnique
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamiliesAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X} {D : Subgroup X}

private theorem layer_omega_of_inf_le {Q D C : Subgroup X} {z : X} (hF : PlaneFacts Q D z)
    (hDQ : D ≤ Q) (hexp : ∀ x ∈ D, x ^ 3 = 1) (hzD : z ∈ D)
    (hQD : Q ≤ normalizer (D : Set X)) (hQC : Q ≤ normalizer (C : Set X))
    (hinf : ∀ x ∈ D ⊓ C, x ∈ zpowers z) {c : X} (hcQ : c ∈ Q) (hcC : c ∈ C) (hc3 : c ^ 3 = 1) :
    c ∈ zpowers z := by
  have hcomm : ∀ d ∈ D, c * d * c⁻¹ * d⁻¹ ∈ zpowers z := by
    intro d hd
    refine hinf _ ⟨?_, ?_⟩
    · exact D.mul_mem ((mem_normalizer_iff.1 (hQD hcQ) d).1 hd) (D.inv_mem hd)
    · have h2 : d * c⁻¹ * d⁻¹ ∈ C :=
        (mem_normalizer_iff.1 (hQC (hDQ hd)) c⁻¹).1 (C.inv_mem hcC)
      simpa [mul_assoc] using C.mul_mem hcC h2
  obtain ⟨δ, hδD, hδ⟩ := hF.inner c hcQ hcomm
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : X, c₀ = δ⁻¹ * c := ⟨_, rfl⟩
  have hcδ : c = δ * c₀ := by rw [hc₀]; simp
  have hc₀Q : c₀ ∈ Q := hc₀ ▸ Q.mul_mem (Q.inv_mem (hDQ hδD)) hcQ
  have hcomm₀ : ∀ d ∈ D, c₀ * d = d * c₀ := fun d hd => by rw [hc₀]; exact hδ d hd
  have hc₀3 : c₀ ^ 3 = 1 := by
    have h3 : c ^ 3 = δ ^ 3 * c₀ ^ 3 := by
      rw [hcδ]
      exact Commute.mul_pow (show Commute δ c₀ from (hcomm₀ δ hδD).symm) 3
    rw [hc3, hexp δ hδD, one_mul] at h3
    exact h3.symm
  have hc₀z : c₀ ∈ zpowers z := hF.omega_cent c₀ hc₀Q hcomm₀ hc₀3
  exact hinf c ⟨hcδ ▸ D.mul_mem hδD (zpowers_le.2 hzD hc₀z), hcC⟩

private theorem layer_omega_false {Q D L B : Subgroup X} {z : X} (hF : PlaneFacts Q D z)
    (hz3 : orderOf z = 3) (hzD : z ∈ D) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hzc : ∀ g : X, z * g = g * z) (hzL : ∀ k ∈ L, z * k = k * z)
    (hZ3 : ∀ w ∈ L, w ∈ centralizer (L : Set X) → w ^ 3 = 1 → w ∈ zpowers z)
    (hBL : B ≤ L) (hBD : B ≤ D) (hB9 : Nat.card B = 9) (hBe : IsElemAbelian 3 B)
    {d₀ : X} (hd₀D : d₀ ∈ D) (hd₀C : d₀ ∈ centralizer (L : Set X)) (hd₀z : d₀ ∉ zpowers z) :
    False := by
  have hcommz : ∀ e ∈ zpowers z, e * d₀ = d₀ * e := by
    intro e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 he
    exact (Commute.zpow_left (show Commute z d₀ from hzc d₀) k).eq
  have hcard : Nat.card ↥(zpowers z ⊔ zpowers d₀) = 9 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers z)
      (hexp d₀ hd₀D) hd₀z hcommz, Nat.card_zpowers, hz3]
  have hB'D : zpowers z ⊔ zpowers d₀ ≤ D := sup_le (zpowers_le.2 hzD) (zpowers_le.2 hd₀D)
  have hB'C : zpowers z ⊔ zpowers d₀ ≤ centralizer (L : Set X) :=
    sup_le (zpowers_le.2 (mem_centralizer_iff.2 fun k hk => (hzL k hk).symm)) (zpowers_le.2 hd₀C)
  have hBB' : B = zpowers z ⊔ zpowers d₀ :=
    hF.eq_of_comm B _ hBD hB'D hB9 hcard fun b hb b' hb' =>
      mem_centralizer_iff.1 (hB'C hb') b (hBL hb)
  have hBz : B ≤ zpowers z := fun b hb =>
    hZ3 b (hBL hb) (hB'C (hBB' ▸ hb)) (hBe.2 b hb)
  have hle := Subgroup.card_le_of_le hBz
  rw [hB9, Nat.card_zpowers, hz3] at hle
  omega

theorem NGKData.layer_structure (h : NGKData X P z D) (hF : PlaneFacts (P : Subgroup X) D z)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z) :
    ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ L.Normal ∧ z ∈ L ∧ (∀ k ∈ L, z * k = k * z) ∧
      center L ≠ ⊥ ∧ IsCyclic (center L) ∧
      (∀ c ∈ (P : Subgroup X) ⊓ centralizer (L : Set X), orderOf c = 3 → c ∈ zpowers z) ∧
      ∃ B : Subgroup X, B ≤ L ∧ B ≤ D ∧ Nat.card B = 9 ∧ IsElemAbelian 3 B ∧
        (P : Subgroup X) ≤ normalizer (B : Set X) := by
  obtain ⟨L, hL, huniq⟩ := h.exists_unique_component hF hB
  have hLn : L.Normal := CFSG.AGLEmbedding.normal_of_forall_isComponentOf_eq hL huniq
  have hZ : center L ≠ ⊥ := h.no_centerless hF L hL
  obtain ⟨hzL, hzc, hZB, hcyc⟩ := h.component_data hB hL hZ
  have hPL : (P : Subgroup X) ≤ normalizer (L : Set X) := le_normalizer_of_normal
  have hPC : (P : Subgroup X) ≤ normalizer (centralizer (L : Set X) : Set X) :=
    le_normalizer_of_normal
  obtain ⟨B, hBS, hBD, hB9, hBe, -, hBn⟩ := hF.inf_plane _ inf_le_left
    (le_trans (le_inf le_normalizer hPL) inf_normalizer_le_normalizer_inf)
    (h.not_isMulCommutative_inf hB hL hZ)
  have hBL : B ≤ L := hBS.trans inf_le_right
  refine ⟨L, hL, hLn, hzL, hzc, hZ, hcyc, ?_, B, hBL, hBD, hB9, hBe, hBn⟩
  intro c hc hc3
  have hZ3 : ∀ w ∈ L, w ∈ centralizer (L : Set X) → w ^ 3 = 1 → w ∈ zpowers z := by
    intro w hwL hwC hw3
    refine hB w (hZB ⟨w, hwL⟩ (mem_center_iff.2 fun k => Subtype.ext ?_)) hw3
    exact mem_centralizer_iff.1 hwC k k.2
  have hPCn : (P : Subgroup X) ≤
      normalizer (((P : Subgroup X) ⊓ centralizer (L : Set X) : Subgroup X) : Set X) :=
    le_trans (le_inf le_normalizer hPC) inf_normalizer_le_normalizer_inf
  by_cases hcase : ∀ x ∈ D ⊓ ((P : Subgroup X) ⊓ centralizer (L : Set X)), x ∈ zpowers z
  · exact layer_omega_of_inf_le hF h.plane.1 h.plane.2.2.1 h.zD h.normal hPCn hcase hc.1 hc
      (hc3 ▸ pow_orderOf_eq_one c)
  · obtain ⟨d₀, ⟨hd₀D, -, hd₀C⟩, hd₀z⟩ : ∃ d₀ ∈ D ⊓ ((P : Subgroup X) ⊓ centralizer (L : Set X)),
        d₀ ∉ zpowers z := by
      by_contra hcon
      exact hcase fun x hx => by_contra fun hxz => hcon ⟨x, hx, hxz⟩
    exact (layer_omega_false hF h.ord h.zD h.plane.2.2.1 h.zc' hzc hZ3 hBL hBD hB9 hBe hd₀D hd₀C
      hd₀z).elim

end CFSG.LocalAnalysis.RankThreeTheoremC

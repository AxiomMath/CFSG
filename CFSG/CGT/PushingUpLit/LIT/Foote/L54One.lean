module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L54Basic
public import CFSG.CGT.PushingUpLit.LIT.Foote.L55Group

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace QBlock

variable {K : Subgroup G}

theorem exists_subgroup_card_pow (h : QBlock K) {k : ℕ} (hk : k ≤ 3) :
    ∃ E : Subgroup G, E ≤ blockU K ∧ Nat.card E = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := h.isPGroup_blockU.exists_card_eq
  have h8 := h.eight_le_card_blockU
  have hm3 : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hdvd : 2 ^ k ∣ Nat.card ↥(blockU K) := by
    rw [hm]
    exact pow_dvd_pow 2 (hk.trans hm3)
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥(blockU K)) 2 hdvd
  refine ⟨E.map (blockU K).subtype, Subgroup.map_subtype_le E, ?_⟩
  rw [Subgroup.card_map_of_injective (blockU K).subtype_injective, hE]

end QBlock

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem part_one_core (hA : FooteTheoremA) {z₀ : G} (hz₀ : ZData J z₀) (hth : Three M J)
    (hno : ∀ h : G, h ∉ M → ∀ t ∈ J, t ∈ rightConjugate M h → t * t = 1 → t = 1) {y : G}
    (hy2 : y * y = 1) (hyC : Subgroup.centralizer ({y} : Set G) ≤ M) {h : G} (hh : h ∉ M)
    (hyh : y ∈ rightConjugate M h) : False := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  set B₁ := rightConjugate J h with hB₁
  set m₁ := h * y * h⁻¹ with hm₁def
  have hm₁ : m₁ ∈ M := (mem_rightConjugate_iff _ _ _).1 hyh
  set B₂ := rightConjugate J (m₁ * h) with hB₂
  have hB₂y : B₂ = rightConjugate B₁ y := by
    rw [hB₁, rightConjugate_mul, hB₂]
    congr 1
    rw [hm₁def]
    group
  have hBlk₁ : QBlock B₁ := c.block.conj h
  have hBlk₂ : QBlock B₂ := c.block.conj (m₁ * h)
  have hU₂ : blockU B₂ = rightConjugate (blockU B₁) y := by
    rw [hB₂y, blockU_rightConjugate]
  have hcommUU : ∀ a ∈ blockU B₁, ∀ b ∈ blockU B₂, a * b = b * a := by
    intro a ha b hb
    by_cases hB : B₁ = B₂
    · rw [← hB] at hb
      exact hBlk₁.blockU_comm a ha b hb
    · refine c.comm_conj_g h M.one_mem hm₁ ?_ ?_ ?_
      · rw [one_mul]
        exact hB
      · rw [one_mul]
        exact blockU_le B₁ ha
      · exact blockU_le B₂ hb
  set V := blockU B₁ ⊔ blockU B₂ with hV
  have hVel : CFSG.Open.IsElemAbelian 2 V :=
    L54.isElemAbelian_sup hBlk₁.isElemAbelian_blockU hBlk₂.isElemAbelian_blockU hcommUU
  have htV : ∀ v ∈ V, y * v * y⁻¹ ∈ V := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_commute hcommUU).1 hv
    have h1 : y * a * y⁻¹ ∈ blockU B₂ := by
      rw [hU₂, mem_rightConjugate_iff]
      have e : y * (y * a * y⁻¹) * y⁻¹ = a := by
        rw [hyi]
        calc y * (y * a * y) * y = (y * y) * a * (y * y) := by group
          _ = a := by rw [hy2]; group
      rw [e]
      exact ha
    have h2 : y * b * y⁻¹ ∈ blockU B₁ := by
      rw [hU₂, mem_rightConjugate_iff] at hb
      exact hb
    have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
    rw [e]
    exact V.mul_mem (le_sup_right (a := blockU B₁) h1) (le_sup_left (b := blockU B₂) h2)
  have hcard : 8 ≤ Nat.card V :=
    hBlk₁.eight_le_card_blockU.trans (Subgroup.card_le_of_le le_sup_left)
  obtain ⟨E, hEV, hEel, hE4, hEy⟩ := exists_fourGroup_centralizer hVel hy2 htV hcard
  have hEM : E ≤ M := fun e he =>
    hyC (Subgroup.mem_centralizer_singleton_iff.2 (hEy e he))
  have hEC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ rightConjugate M h := by
    intro e he he1
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_commute hcommUU).1 (hEV he)
    obtain ⟨c₃, hc₃, hX1, hX2⟩ := hth.exists_notin_g h B₁ B₂
    refine c.centralizer_le_of_centralizes_g h he1 (twoElem_of_mul_self (by
      have := hEel.2 e he
      simpa [pow_two] using this)) hc₃ ?_
    intro z hz
    have h1 : a * z = z * a := by
      refine c.comm_conj_g h M.one_mem hc₃ ?_ ?_ hz
      · rw [one_mul]
        exact fun h' => hX1 h'.symm
      · rw [one_mul]
        exact blockU_le B₁ ha
    have h2 : b * z = z * b := by
      refine c.comm_conj_g h hm₁ hc₃ ?_ ?_ hz
      · exact fun h' => hX2 h'.symm
      · exact blockU_le B₂ hb
    rw [hab]
    calc z * (a * b) = (z * a) * b := by group
      _ = (a * z) * b := by rw [h1]
      _ = a * (z * b) := by group
      _ = a * (b * z) := by rw [h2]
      _ = a * b * z := by group
  have hEN : E ≤ Subgroup.normalizer (J : Set G) :=
    c.lemma_5_3 hA hz₀ hEM hEel hE4 hh hEC
  obtain ⟨u, hu, -, -, hu1, -, -⟩ := exists_two_ne_one (W := E) (by omega)
  have hu2 : u * u = 1 := by simpa [pow_two] using hEel.2 u hu
  obtain ⟨a, haU, hau, k, hk, hak⟩ := hA G J c.block u (hEN hu) (twoElem_of_mul_self hu2)
    (by rw [hu2]; exact Subgroup.one_mem _)
  have haJ : a ∈ J := blockU_le J haU
  have haa : a * a = 1 := c.block.blockU_sq_eq_one a haU
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hak (by simp)
  have haMh : a ∈ rightConjugate M h :=
    hEC u hu hu1 (Subgroup.mem_centralizer_singleton_iff.2 hau)
  exact ha1 (hno h hh a haJ haMh haa)

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote

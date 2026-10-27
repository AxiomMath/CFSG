module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Closed
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.TypeArg

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

theorem card_statedSL_two7 (F : Type) [Field F] [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem q_eq_of_card {q₁ q₂ : ℕ} (h5₁ : 5 ≤ q₁) (h5₂ : 5 ≤ q₂)
    (h : q₁ * (q₁ ^ 2 - 1) = q₂ * (q₂ ^ 2 - 1)) : q₁ = q₂ := by
  have hq1 : 1 ≤ q₁ ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hq2 : 1 ≤ q₂ ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [hq1, hq2] at h
  have h1 : ((q₁ : ℤ) - q₂) * ((q₁ : ℤ) ^ 2 + q₁ * q₂ + (q₂ : ℤ) ^ 2 - 1) = 0 := by
    linear_combination h
  have h2 : (0 : ℤ) < (q₁ : ℤ) ^ 2 + q₁ * q₂ + (q₂ : ℤ) ^ 2 - 1 := by
    have : (5 : ℤ) ≤ q₁ := by exact_mod_cast h5₁
    have : (5 : ℤ) ≤ q₂ := by exact_mod_cast h5₂
    nlinarith
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact_mod_cast sub_eq_zero.1 h3
  · exact absurd h3 h2.ne'

theorem card_hat_eq_of_cmap {G : Type} [Group G] [Finite G] {K₁ K₂ : Subgroup G} {c : G}
    (h : cmap c K₁ = K₂) : Nat.card (HatT K₁) = Nat.card (HatT K₂) := by
  have key : ∀ K : Subgroup G,
      Nat.card (HatT K) * Nat.card (pPrimeCoreOf 2 K) = Nat.card ↥K := by
    intro K
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥K)
    have h2 : Nat.card (pPrimeCoreOf 2 K) = Nat.card (pPrimeCore 2 ↥K) := by
      unfold pPrimeCoreOf
      exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [h2]
    exact h1.symm
  have hmap : ∀ H : Subgroup G, Nat.card ↥(cmap c H) = Nat.card ↥H := fun H =>
    Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  subst h
  have e1 := key K₁
  have e2 := key (cmap c K₁)
  rw [pPrimeCoreOf_cmap, hmap, hmap] at e2
  have hpos : 0 < Nat.card (pPrimeCoreOf 2 K₁) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (e1.trans e2.symm)

theorem prop_7_1 (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (h44 : II4_44) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (h72 : Prop7_2)
    (h710 : Lemma7_10) : Prop7_1 := by
  intro G _ _ z S K₁ K₂ hstd hnf
  have hs6 : Std6 G z S := ⟨hstd.simple, hstd.rank, hstd.rank_le, hstd.gen4, hstd.classical, hstd.thm2, hstd.sylow, hstd.kgh⟩
  obtain ⟨ha, hb, -, hd⟩ := h61 G z S hs6
  have hr₁ := hstd.comp_rigid (K := K₁) (Or.inl rfl)
  have hr₂ := hstd.comp_rigid (K := K₂) (Or.inr rfl)
  have ha₁ := ha K₁ hr₁
  have ha₂ := ha K₂ hr₂
  have hb₁ := hb K₁ hr₁
  have hb₂ := hb K₂ hr₂
  have hd₁ := hd K₁ hr₁
  have hd₂ := hd K₂ hr₂
  obtain ⟨hQ, -, -⟩ := h41 G z S K₁ K₂ hstd
  have hp66 := h66 G z S K₁ K₂ hstd ha₁ ha₂ hb₁ hb₂
  have hstd7 : Std7 G z S K₁ K₂ := ⟨hstd, ha₁, ha₂, hb₁, hb₂, hd₁, hd₂, hQ, hp66, hnf⟩
  have hM := m4_of_std hII hstd
  have hzP : z ∈ Pz S z := ⟨hM.z_mem_S, by
    rw [hstd.rigidProduct_eq]
    exact mem_sup_left (hM.z_mem_comp (Or.inl rfl))⟩
  have hA : Hyp4A S z := by
    intro x hx hxc
    apply hnf x _ hxc
    unfold Rz at hx
    rw [hQ] at hx
    exact sup_le le_rfl (zpowers_le.2 hzP) hx
  obtain ⟨t, htS, htc, htne, htint⟩ := hL44 G z S K₁ K₂ hstd hA
  obtain ⟨-, htfus, htz⟩ := hL45 G z S K₁ K₂ hstd hA t htS htc htne htint
  obtain ⟨u, huP, huo, hune, hunorm⟩ := hpnf G z S K₁ K₂ ⟨hstd, hQ, hb₁, hb₂⟩
  have hsl : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) → ¬IsDoubleCoverOfAlt (HatT K) 7 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧
        Nonempty (HatT K ≃* StatedSL 2 F) := by
    intro K hK hdK
    have := h44 G hstd.simple z hstd.orderOf_z K (hstd.comp_isPCompIn hK) (hstd.comp_pRank hK)
    rcases this.1 with ⟨F, hF, hFin, ⟨hodd, h5⟩, he⟩ | h7
    · exact ⟨F, hF, hFin, hodd, h5, he⟩
    · exact absurd h7 hdK
  obtain ⟨F₁, hF₁, hFin₁, hodd₁, h5₁, ⟨e₁⟩⟩ := hsl K₁ (Or.inl rfl) hd₁
  obtain ⟨F₂, hF₂, hFin₂, hodd₂, h5₂, ⟨e₂⟩⟩ := hsl K₂ (Or.inr rfl) hd₂
  have hcm : cmap t⁻¹ K₁ = K₂ := by
    rw [cmap_eq_cj, inv_inv]
    exact ((interchanges_iff t).1 htint).1
  have hcard : Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) = Nat.card F₂ * (Nat.card F₂ ^ 2 - 1) := by
    rw [← card_statedSL_two7 F₁, ← card_statedSL_two7 F₂, ← Nat.card_congr e₁.toEquiv,
      ← Nat.card_congr e₂.toEquiv]
    exact card_hat_eq_of_cmap hcm
  have hq : Nat.card F₁ = Nat.card F₂ := q_eq_of_card h5₁ h5₂ hcard
  have hq₁ : HatSL2 K₁ (Nat.card F₁) := ⟨F₁, hF₁, hFin₁, rfl, ⟨e₁⟩⟩
  have hq₂ : HatSL2 K₂ (Nat.card F₁) := ⟨F₂, hF₂, hFin₂, hq.symm, ⟨e₂⟩⟩
  have hcfg : Cfg7 G z S K₁ K₂ t u (Nat.card F₁) :=
    ⟨hstd7, ⟨htS, htc, htne, htint, htfus, htz, huP, huo, hune, hunorm, hodd₁, h5₁, hq₁, hq₂⟩⟩
  obtain ⟨w, hc, hd'⟩ := h72 G z S K₁ K₂ t u (Nat.card F₁) hcfg
  exact ⟨Nat.card F₁, w, hodd₁, h5₁, hq₁, hq₂, h710 G z S K₁ K₂ t u (Nat.card F₁) w hcfg hc hd'⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec7

module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx67
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AbsCfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1Norm
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7 CFSG.GH74.GLS.Stage1.Thm3.Sec8
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem imgBar_sup_eq (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    ((K₁ ⊔ K₂ ⊔ S).subgroupOf (Cz z)).map (piC z) = imgBar z K₁ ⊔ imgBar z K₂ ⊔ imgBar z S := by
  have hM := hf.m4 hII
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  have hSC : S ≤ Cz z := hf.S_le_C hII
  unfold imgBar
  rw [Subgroup.subgroupOf_sup (sup_le hK₁C hK₂C) hSC, Subgroup.subgroupOf_sup hK₁C hK₂C,
    Subgroup.map_sup, Subgroup.map_sup]

theorem relIndex_barK (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    (imgBar z K₁ ⊔ imgBar z K₂).relIndex (imgBar z K₁ ⊔ imgBar z K₂ ⊔ imgBar z S) =
      (Pz S z).relIndex S := by
  have hM := hf.m4 hII
  have hSC : S ≤ Cz z := hf.S_le_C hII
  have hS2 : IsPGroup 2 ↥S := hf.S_pgroup hII
  have hPS : Pz S z ≤ S := inf_le_left
  have hPC : Pz S z ≤ Cz z := hPS.trans hSC
  have : (imgBar z K₁ ⊔ imgBar z K₂).Normal := hf.normal_imgBar_sup hII
  have hinf : (imgBar z K₁ ⊔ imgBar z K₂) ⊓ imgBar z S = imgBar z (Pz S z) := by
    apply le_antisymm
    · rintro x ⟨hxK, hxS⟩
      obtain ⟨s, hs, rfl⟩ := (mem_imgBar hSC).1 hxS
      rw [← hf.map_L hII] at hxK
      obtain ⟨y, hy, hyeq⟩ := hxK
      have hker : (⟨s, hSC hs⟩ : ↥(Cz z))⁻¹ * y ∈ pPrimeCore 2 ↥(Cz z) := QuotientGroup.eq.1 hyeq.symm
      have hOz : (s : G)⁻¹ * (y : G) ∈ Oz z := ⟨_, hker, rfl⟩
      have hyL : (y : G) ∈ K₁ ⊔ K₂ ⊔ Oz z := hy
      have hsL : s ∈ K₁ ⊔ K₂ ⊔ Oz z := by
        have e : s = (y : G) * ((s : G)⁻¹ * (y : G))⁻¹ := by group
        rw [e]
        exact mul_mem hyL (inv_mem (mem_sup_right hOz))
      have hsP : s ∈ Pz S z := by
        rw [← hf.S_inf_L hII]
        exact ⟨hs, hsL⟩
      exact piC_mem_imgBar hPC hsP
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := (mem_imgBar hPC).1 hx
      refine ⟨?_, piC_mem_imgBar hSC (hPS hs)⟩
      have hs' : s ∈ K₁ ⊔ K₂ := by
        have h1 : Pz S z ≤ rigidProduct z := inf_le_right
        rw [hf.std.rigidProduct_eq] at h1
        exact h1 hs
      rw [← hf.map_L hII]
      exact ⟨⟨s, hPC hs⟩, mem_sup_left hs', rfl⟩
  have hK := Subgroup.relIndex_sup_left (imgBar z S) (imgBar z K₁ ⊔ imgBar z K₂)
  rw [hK]
  have h1 := Subgroup.relIndex_mul_card (imgBar z K₁ ⊔ imgBar z K₂) (imgBar z S)
  have h2 := Subgroup.relIndex_mul_card (Pz S z) S
  rw [hinf, card_imgBar_eq_of_le hSC hS2 hPS] at h1
  rw [inf_eq_left.2 hPS] at h2
  have hcardS : Nat.card ↥(imgBar z S) = Nat.card ↥S :=
    card_imgBar_eq_of_le hSC hS2 (le_refl S)
  rw [hcardS] at h1
  have hpos : 0 < Nat.card ↥(Pz S z) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1, h2]


theorem c1_of_fused_of_swap (hII : II4_4_4_center) (h44 : II4_44) (h2A7 : IVK.Lifted.II4_2A7)
    (hFS : FStar_C) : C1_of_Fused := by
  intro G _ _ z S K₁ K₂ hf hS hrel hcard
  have hc₁ : IsPCompIn 2 (Cz z) K₁ := hf.std.comp_isPCompIn (Or.inl rfl)
  have hc₂ : IsPCompIn 2 (Cz z) K₂ := hf.std.comp_isPCompIn (Or.inr rfl)
  have hsl : ∀ K : Subgroup G, (K = K₁ ∨ K = K₂) → ¬ IsDoubleCoverOfAlt (HatT K) 7 →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧
        Nonempty (HatT K ≃* StatedSL 2 F) := by
    intro K hK hdK
    have := h44 G hf.std.simple z hf.std.orderOf_z K (hf.std.comp_isPCompIn hK)
      (hf.std.comp_pRank hK)
    rcases this.1 with ⟨F, hF, hFin, ⟨hodd, h5⟩, he⟩ | h7
    · exact ⟨F, hF, hFin, hodd, h5, he⟩
    · exact absurd h7 hdK
  obtain ⟨F₁, hF₁, hFin₁, hodd₁, h5₁, ⟨e₁⟩⟩ := hsl K₁ (Or.inl rfl) hf.d₁
  obtain ⟨F₂, hF₂, hFin₂, hodd₂, h5₂, ⟨e₂⟩⟩ := hsl K₂ (Or.inr rfl) hf.d₂
  obtain ⟨ι₁⟩ := imgBar_equiv hc₁
  obtain ⟨ι₂⟩ := imgBar_equiv hc₂
  obtain ⟨ea, hPa, hva⟩ := hf.card_P_hat hII (Or.inl rfl : K₁ = K₁ ∨ K₁ = K₂)
  obtain ⟨eb, hPb, hvb⟩ := hf.card_P_hat hII (Or.inr rfl : K₂ = K₁ ∨ K₂ = K₂)
  have hab : ea = eb := by
    have : (2 : ℕ) ^ ea = 2 ^ eb := by rw [← hPa, ← hPb]; exact hcard
    exact Nat.pow_right_injective le_rfl this
  have hSL₁ : (Nat.card (StatedSL 2 F₁)).factorization 2 = ea := by
    rw [← Nat.card_congr e₁.toEquiv]; exact hva
  have hSL₂ : (Nat.card (StatedSL 2 F₂)).factorization 2 = ea := by
    rw [← Nat.card_congr e₂.toEquiv, hab]; exact hvb
  have hv₁ : (Nat.card F₁ ^ 2 - 1).factorization 2 = ea := by
    rw [← Basic.two_val_statedSL F₁ hodd₁]; exact hSL₁
  have hv₂ : (Nat.card F₂ ^ 2 - 1).factorization 2 = ea := by
    rw [← Basic.two_val_statedSL F₂ hodd₂]; exact hSL₂
  have hP₁ : (Nat.card ↥(Pof S K₁)).factorization 2 = ea := by
    rw [hPa]; simp [Nat.Prime.factorization_pow Nat.prime_two]
  have hS' : S ≤ normalizer (K₁ : Set G) := fun s hs => by
    have : s ∈ S1 S K₁ := by rw [← hS]; exact hs
    exact this.2
  have hres : oPrimeResidual 2 (CentralizerBar z) = imgBar z K₁ ⊔ imgBar z K₂ ⊔ imgBar z S :=
    (oPrimeResidual_eq hII hf.std
      (N_normal hII hf.std (oddCommS_of_S1 hII h44 h2A7 hFS hf.std hf.hQ hS'))).trans
      (imgBar_sup_eq hII hf)
  have hKidx : ((imgBar z K₁ ⊔ imgBar z K₂).subgroupOf (oPrimeResidual 2 (CentralizerBar z))).index = 2 := by
    rw [hres]
    show (imgBar z K₁ ⊔ imgBar z K₂).relIndex (imgBar z K₁ ⊔ imgBar z K₂ ⊔ imgBar z S) = 2
    rw [relIndex_barK hII hf]; exact hrel
  have hKle : imgBar z K₁ ⊔ imgBar z K₂ ≤ oPrimeResidual 2 (CentralizerBar z) := by
    rw [hres]; exact le_sup_left
  have hcomm := imgBar_comm hII hf
  have hcardInf := imgBar_inf_card hII h44 hf
  have ε₁ : ↥(imgBar z K₁) ≃* StatedSL 2 F₁ := ι₁.symm.trans e₁
  have ε₂ : ↥(imgBar z K₂) ≃* StatedSL 2 F₂ := ι₂.symm.trans e₂
  have hcp : IsCentralProductOfSL2 (imgBar z K₁ ⊔ imgBar z K₂) F₁ F₂ :=
    ⟨imgBar z K₁, imgBar z K₂, rfl, hcomm, hcardInf, ⟨ε₁⟩, ⟨ε₂⟩⟩
  have hcp' : IsCentralProductOfSL2 (imgBar z K₁ ⊔ imgBar z K₂) F₂ F₁ :=
    Fused8.isCentralProductOfSL2_swap hcomm hcardInf ε₁ ε₂
  rcases le_total (Nat.card F₂) (Nat.card F₁) with hle | hle
  · obtain ⟨p, f, hp, hp2, hpf⟩ := Basic.exists_odd_prime_pow F₂ hodd₂
    refine ⟨Nat.card F₂, ⟨p, f, hp, hp2, hpf, ?_⟩, ?_⟩
    · rw [hv₂, hP₁]
    · exact ⟨F₁, F₂, hF₁, hF₂, hFin₁, hFin₂, hodd₁, hodd₂, hle, rfl, h5₁, by rw [hSL₁, hSL₂],
        imgBar z K₁ ⊔ imgBar z K₂, hKle, hKidx, hcp⟩
  · obtain ⟨p, f, hp, hp2, hpf⟩ := Basic.exists_odd_prime_pow F₁ hodd₁
    refine ⟨Nat.card F₁, ⟨p, f, hp, hp2, hpf, ?_⟩, ?_⟩
    · rw [hv₁, hP₁]
    · exact ⟨F₂, F₁, hF₂, hF₁, hFin₂, hFin₁, hodd₂, hodd₁, hle, rfl, h5₂, by rw [hSL₂, hSL₁],
        imgBar z K₁ ⊔ imgBar z K₂, hKle, hKidx, hcp'⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.F1

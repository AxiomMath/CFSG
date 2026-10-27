module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RJ
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelBase
public import CFSG.GH74.GLS.C3.Layer1.Th2T1RelLeaves
public import CFSG.GH74.GLS.C3.Layer1.Thm1L3A7

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P39R

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G]

theorem eight_le_or_eq_four {n : ℕ} (h4 : 4 ≤ n) (hn : ∃ k : ℕ, n = 2 ^ k) : 8 ≤ n ∨ n = 4 := by
  obtain ⟨k, rfl⟩ := hn
  by_cases hk : 3 ≤ k
  · left
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  · right
    have hk3 : k ≤ 2 := by omega
    interval_cases k <;> simp at h4 ⊢

namespace Frame39

variable {x y : G} {K T V W S P₀ : Subgroup G} {f z a f₁ : G}
  (F : Frame39 x y K T V W f z S a P₀ f₁)

include F

section Fin

variable [Finite G]

omit [Finite G] in
theorem f₁_mem_B : f₁ ∈ zpowers f ⊔ zpowers x := by
  rcases F.hf₁ with rfl | rfl
  · exact mem_sup_left (mem_zpowers _)
  · exact (zpowers f ⊔ zpowers x).mul_mem (mem_sup_left (mem_zpowers _))
      (mem_sup_right (mem_zpowers _))

omit [Finite G] in
theorem f₁_mem_J : f₁ ∈ thompsonJ2 T := by
  rw [F.h37a]
  exact mem_sup_right F.f₁_mem_B

theorem f₁_not_mem_P : f₁ ∉ T ⊓ K := by
  intro h
  have h1 : f₁ ∈ (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) := ⟨h, F.f₁_mem_B⟩
  rw [F.h37b, Subgroup.mem_bot] at h1
  have h2 := F.isFMember_f₁.2.1
  rw [h1, orderOf_one] at h2
  omega

theorem false_of_isConj_z (hzf : IsConj z f₁) : False := by
  apply F.f₁_not_mem_P
  rw [F.hPgen]
  exact subset_closure ⟨F.f₁_mem_J, hzf⟩

omit [Finite G] in
theorem false_of_x_mem_zCenter (hx : x ∈ zCenter (v₁ T f a)) : False := by
  have ha : a ∈ v₁ T f a := Subgroup.mem_sup_right (mem_zpowers a)
  have h1 : a * x = x * a := hx.2 a ha
  have h2 : x * z = x * 1 := by
    rw [← F.hax, mul_one]
    calc a * x * a⁻¹ = x * a * a⁻¹ := by rw [h1]
      _ = x := by group
  exact F.hz1 (mul_left_cancel h2)

theorem false_of_sup_eq (h33c : B_thm1_L33c'_rel) (h33d : B_thm1_L33d_rel)
    (hL32 : B_thm1_L32'_rel) (hG : C3Hyp G) (hN : NoV2Fine G)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5))
    (hJeq : pumpJ K f₁ = layerI K f₁ ⊔ pPrimeCoreOf 2 (pumpJ K f₁)) : False := by
  have cfg2 := F.cfg₂
  obtain ⟨-, hJn, -⟩ := hL32 G hG hN x y K f₁ cfg2.fmax h5
  have hyp : Hyp33 x y K T (v₁ T f a) S f₁ z := ⟨cfg2, hJeq⟩
  have h4 := cfg2.four_le_card_secD hJeq hJn
  have hDp : IsPGroup 2 ↥(secD K f₁ (v₁ T f a)) := cfg2.sylowV.isPGroup.to_le inf_le_left
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hDp
  rcases eight_le_or_eq_four h4 ⟨k, hk⟩ with hD8 | hD4
  · obtain ⟨hzf, -⟩ := h33c G hG hN x y K T (v₁ T f a) S f₁ z hyp hD8 F.v₁_ne_S h5
    exact F.false_of_isConj_z hzf
  · obtain ⟨hxZ, -⟩ := h33d G hG hN x y K T (v₁ T f a) S f₁ z hyp hD4 (Or.inl F.v₁_ne_S) h5
    exact F.false_of_x_mem_zCenter hxZ

theorem exists_third_data (h34a : B_thm1_L34a_rel) (hL32 : B_thm1_L32'_rel)
    (hP31c : B_thm1_P31c_rel) (hG : C3Hyp G) (hN : NoV2Fine G)
    (h5 : ¬ HasL2Model (kBar K) (fun q => q = 5))
    (hnotA7 : ¬ Nonempty (kBar K ≃* alternatingGroup (Fin 7))) (h8 : 8 ≤ Nat.card ↥(T ⊓ K))
    (hlt : layerI K f₁ ⊔ pPrimeCoreOf 2 (pumpJ K f₁) < pumpJ K f₁) :
    ∃ w₁ : G, Is2TerminalU2Triple f₁ w₁ (pumpJ K f₁) ∧
      ¬ HasL2Model (kBar (pumpJ K f₁)) (fun q => q = 5) ∧
      Nat.card (kBar (pumpJ K f₁)) = Nat.card (kBar K) := by
  have cfg2 := F.cfg₂
  obtain ⟨hJc, hJn, r, hrodd, hr5, hI, hKshape, hJshape, -⟩ :=
    hL32 G hG hN x y K f₁ cfg2.fmax h5
  have hKL2 : HasL2Model (kBar K) (fun q => q = r ^ 2) :=
    hKshape.resolve_right (fun h => hnotA7 h.2)
  have hIJ : layerI K f₁ ≤ pumpJ K f₁ := Thm1.layerI_le_pumpJ K f₁
  obtain ⟨w, -, hw⟩ := h34a G hG hN x y K T f₁ cfg2.fmax cfg2.setup cfg2.mem hlt h5
  have hJshape' : HasL2Model (kBar (pumpJ K f₁)) (fun q => q = r ^ 2) ∨
      Nonempty (kBar (pumpJ K f₁) ≃* alternatingGroup (Fin 7)) := by
    rcases hJshape with h | h | h
    · exact absurd (Thm1L34.sup_eq_of_hasL2Model hIJ hI h) (ne_of_lt hlt)
    · exact Or.inl h
    · exact Or.inr h
  rcases hJshape' with hJ2 | hJA7
  · refine ⟨w, hw, not_hasL2Model_five_of_sq hrodd hr5 hJ2, ?_⟩
    rw [Thm1L34.card_kBar_of_hasL2Model hJ2, Thm1L34.card_kBar_of_hasL2Model hKL2]
  · exfalso
    have hS : IsSylowOf 2 (zpowers f₁) (CxK f₁ (pumpJ K f₁)) :=
      hP31c G hG hN f₁ w _ hw (not_hasL2Model_five_of_alt7 hJA7)
    obtain ⟨e⟩ := hJA7
    have h32 : Nat.card ↥(v₁ T f a) ≤ 32 :=
      Thm1L3A7.card_le_32_of_A7 cfg2.hf2 cfg2.sylowV.isPGroup cfg2.sylowV.le hJc.1 hJn e hS
    have h64 := F.sixty_four_le_card_T h8
    have hcard := F.card_v₁
    omega

end Fin

end Frame39

end CFSG.GH74.GLS.C3.Layer1.Thm1P39R

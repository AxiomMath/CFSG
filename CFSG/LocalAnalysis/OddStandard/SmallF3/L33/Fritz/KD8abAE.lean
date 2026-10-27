module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8ACase
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abAM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abT2e

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open KD7 Sec8

theorem conj_k8 : ∀ (u : (ZMod 8)ˣ) (b : ZMod 8),
    aff8 u b * k8 * (aff8 u b)⁻¹ * k8⁻¹ = 1 ∨ aff8 u b * k8 * (aff8 u b)⁻¹ * k8⁻¹ = z8 := by
  decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem conj_k_cases {e : X} (he : e ∈ A.T) :
    e * S.k * e⁻¹ = S.k ∨ e * S.k * e⁻¹ = S.z * S.k ∨ e * S.k * e⁻¹ = t * S.k ∨
      e * S.k * e⁻¹ = t * S.z * S.k := by
  have hkT : S.k ∈ A.T := C.k_mem
  have hc : e * S.k * e⁻¹ * S.k⁻¹ ∈ A.T :=
    mul_mem (mul_mem (mul_mem he hkT) (inv_mem he)) (inv_mem hkT)
  have hψ : SD.ψX A (e * S.k * e⁻¹ * S.k⁻¹) = 1 ∨
      SD.ψX A (e * S.k * e⁻¹ * S.k⁻¹) = z8 := by
    rw [SD.ψX_comm he hkT, show SD.ψX A S.k = k8 from SDKD.ψX_k C]
    obtain ⟨u, b, hub⟩ : ∃ u b, aff8 u b = SD.ψX A e := by
      rw [SD.ψX_of_mem he]; exact A.ψ_mem_H8 _
    rw [← hub]
    exact conj_k8 u b
  have hk2 : S.k * S.k = 1 := by
    rw [← pow_two]; exact C.k_sq
  have hkinv : S.k⁻¹ = S.k := inv_eq_of_mul_eq_one_right hk2
  have hrw : ∀ c : X, e * S.k * e⁻¹ * S.k⁻¹ = c → e * S.k * e⁻¹ = c * S.k := fun c h => by
    rw [← h, inv_mul_cancel_right]
  rcases hψ with h | h
  · have hK : e * S.k * e⁻¹ * S.k⁻¹ ∈ A.K := (SD.ψX_eq_one_iff hc).mp h
    rcases SDKD.eq_one_or_eq_t_of_mem_K C hK with h' | h'
    · left; rw [hrw _ h', one_mul]
    · right; right; left; exact hrw _ h'
  · have hzc : S.z * (e * S.k * e⁻¹ * S.k⁻¹) ∈ A.T := mul_mem (z_mem_T S) hc
    have hK : S.z * (e * S.k * e⁻¹ * S.k⁻¹) ∈ A.K := by
      rw [← SD.ψX_eq_one_iff hzc, SD.ψX_mul (z_mem_T S) hc, ψX_z S, h]
      decide
    have hzz : S.z * S.z = 1 := zz S
    have hc' : e * S.k * e⁻¹ * S.k⁻¹ = S.z * (S.z * (e * S.k * e⁻¹ * S.k⁻¹)) := by
      rw [← mul_assoc, hzz, one_mul]
    rcases SDKD.eq_one_or_eq_t_of_mem_K C hK with h' | h'
    · right; left; rw [hrw _ (hc'.trans (by rw [h', mul_one]))]
    · right; right; right
      rw [hrw _ (hc'.trans (by rw [h']))]
      rw [show S.z * t = t * S.z from (z_comm_T S A.t_mem_T).symm]

variable {S}

theorem not_conjTo_k {T₁ : Subgroup X} (h4 : S.Sec4 T₁) : ¬ ConjTo t S.k := by
  intro h
  have hkB : S.k ∈ S.B := Frame.k_mem_B
  rcases (h4.fusion _ hkB).mp h with h' | h' | h' | h'
  · exact k_not_mem_L (C := C) (by
      have := congrArg (SD.ψX A) h'
      rw [show SD.ψX A S.k = k8 from SDKD.ψX_k C, SD.ψX_t] at this
      exact absurd this (by decide))
  · have := congrArg (SD.ψX A) h'
    rw [show SD.ψX A S.k = k8 from SDKD.ψX_k C, SD.ψX_mul A.t_mem_T (z_mem_T S), SD.ψX_t,
      ψX_z S, one_mul] at this
    exact absurd this (by decide)
  · exact SD.t_ne_one (A := A) (by
      calc t = t * S.k * S.k⁻¹ := by group
        _ = 1 := by rw [← h', mul_inv_cancel])
  · apply t_not_mem_L (A := A)
    have h1 : t * S.z = 1 := by
      calc t * S.z = t * S.z * S.k * S.k⁻¹ := by group
        _ = 1 := by rw [← h', mul_inv_cancel]
    have : t = S.z⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]; exact inv_mem (z_mem_L S)

theorem conj_k_cases' {T₁ : Subgroup X} (h4 : S.Sec4 T₁) {e : X} (he : e ∈ A.T) :
    e * S.k * e⁻¹ = S.k ∨ e * S.k * e⁻¹ = S.z * S.k := by
  have hn := not_conjTo_k h4
  have htk : ConjTo t (t * S.k) := (h4.fusion _ (mul_mem Frame.t_mem_B Frame.k_mem_B)).mpr
    (Or.inr (Or.inr (Or.inl rfl)))
  have htzk : ConjTo t (t * S.z * S.k) := (h4.fusion _
    (mul_mem (mul_mem Frame.t_mem_B Frame.z_mem_B) Frame.k_mem_B)).mpr
    (Or.inr (Or.inr (Or.inr rfl)))
  have hconj : ∀ c, e * S.k * e⁻¹ = c → ConjTo t c → False := by
    rintro c hc ⟨g, hg⟩
    apply hn
    refine ⟨e⁻¹ * g, ?_⟩
    calc e⁻¹ * g * t * (e⁻¹ * g)⁻¹ = e⁻¹ * (g * t * g⁻¹) * e := by group
      _ = S.k := by rw [hg, ← hc]; group
  rcases conj_k_cases S he with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hconj _ h htk).elim
  · exact (hconj _ h htzk).elim

theorem card_le_of_elem_le_T {T₁ : Subgroup X} (h4 : S.Sec4 T₁) {E : Subgroup X}
    (hE : ElemAbelianTwo E) (hET : E ≤ A.T) : Nat.card E ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push Not at hlt
  set F := E ⊓ centralizer ({S.k} : Set X) with hF
  have hFE : F ≤ E := inf_le_left
  have hFel : ElemAbelianTwo F :=
    ⟨fun a ha b hb => hE.comm a ha.1 b hb.1, fun a ha => hE.sq_eq_one a ha.1⟩
  have hFTE : F ≤ S.TE := fun a ha =>
    mem_TE_of_comm_k S (hET ha.1) (mem_centralizer_singleton_iff.mp ha.2)
  have hmemF : ∀ a ∈ E, a * S.k * a⁻¹ = S.k → a ∈ F := fun a ha h =>
    ⟨ha, mem_centralizer_singleton_iff.mpr (by
      calc a * S.k = (a * S.k * a⁻¹) * a := by group
        _ = S.k * a := by rw [h])⟩
  have hcardF : Nat.card E ≤ 2 * Nat.card F := by
    by_cases hall : E ≤ F
    · have := Subgroup.card_le_of_le hall
      omega
    · obtain ⟨e₀, he₀E, he₀F⟩ := Set.not_subset.mp hall
      have he₀k : e₀ * S.k * e₀⁻¹ = S.z * S.k := by
        rcases conj_k_cases' h4 (hET he₀E) with h | h
        · exact absurd (hmemF e₀ he₀E h) he₀F
        · exact h
      have hN : e₀ ∈ normalizer (F : Set X) := mem_normalizer_of_conj_le fun a ha => by
        rw [hE.comm e₀ he₀E a (hFE ha), mul_inv_cancel_right]; exact ha
      have he₀2 : e₀ * e₀ ∈ F := by
        rw [← pow_two, hE.sq_eq_one e₀ he₀E]; exact one_mem _
      have hle : E ≤ F ⊔ zpowers e₀ := by
        intro a ha
        rcases conj_k_cases' h4 (hET ha) with h | h
        · exact mem_sup_left (hmemF a ha h)
        · have hea : e₀ * a ∈ F := hmemF _ (mul_mem he₀E ha) (by
            rw [show e₀ * a * S.k * (e₀ * a)⁻¹ = e₀ * (a * S.k * a⁻¹) * e₀⁻¹ by group, h,
              show e₀ * (S.z * S.k) * e₀⁻¹ = (e₀ * S.z * e₀⁻¹) * (e₀ * S.k * e₀⁻¹) by group,
              conj_z S (hET he₀E), he₀k, ← mul_assoc, zz S, one_mul])
          have : a = e₀⁻¹ * (e₀ * a) := by group
          rw [this]
          exact mul_mem (mem_sup_right (inv_mem (mem_zpowers e₀))) (mem_sup_left hea)
      calc Nat.card E ≤ Nat.card (F ⊔ zpowers e₀ : Subgroup X) := Subgroup.card_le_of_le hle
        _ = 2 * Nat.card F := Sec8.card_sup_zpowers hN he₀2 he₀F
  have hFp : IsPGroup 2 F := (Sec7.isPGroup_of_elemAbelianTwo hE).to_le hFE
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hFp)
  have hn4 : 4 ≤ n := by
    by_contra h
    push Not at h
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨F₀', hF₀'⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) 2 (n := 4)
    (by rw [hn]; exact Nat.pow_dvd_pow 2 hn4)
  set F₀ := F₀'.map F.subtype with hF₀
  have hF₀F : F₀ ≤ F := map_subtype_le F₀'
  have hF₀card : Nat.card F₀ = 16 := by
    rw [hF₀, card_map_of_injective (subtype_injective F), hF₀']; norm_num
  have hF₀el : ElemAbelianTwo F₀ :=
    ⟨fun a ha b hb => hFel.comm a (hF₀F ha) b (hF₀F hb), fun a ha => hFel.sq_eq_one a (hF₀F ha)⟩
  have hEF₀ : ∀ r : X, IsRefl S r → F₀ = S.E r → E ≤ F₀ := by
    intro r hr heq a ha
    have hcomm : ∀ b ∈ F₀, a * b = b * a := fun b hb => hE.comm a ha b (hFE (hF₀F hb))
    have haTE : a ∈ S.TE := mem_TE_of_comm_k S (hET ha) (hcomm _ (heq ▸ Frame.k_mem_E r))
    rw [heq]
    exact mem_E_of_comm S hr haTE (hcomm _ (heq ▸ Frame.yi_mem_E r))
  have hle : E ≤ F₀ := by
    rcases eq_E_of_elem_le_TE S hF₀el (hF₀F.trans hFTE) hF₀card with h | h
    · exact hEF₀ _ (isRefl_y S) h
    · exact hEF₀ _ (isRefl_xy S) h
  have := Subgroup.card_le_of_le hle
  omega

theorem not_conjTo_of_elem32 {T₁ : Subgroup X} (h4 : S.Sec4 T₁) {g : X} {E : Subgroup X}
    (hE : ElemAbelianTwo E) (hEg : E ≤ centralizer ({g} : Set X)) (hcard : 32 ≤ Nat.card E) :
    ¬ ConjTo t g := by
  rintro ⟨c, hc⟩
  set f : X →* X := (MulAut.conj c⁻¹).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj c⁻¹).injective
  have hEel : ElemAbelianTwo (E.map f) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hE.comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hE.sq_eq_one a ha, map_one]
  have hEt : E.map f ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hag := mem_centralizer_singleton_iff.mp (hEg ha)
    rw [← hc] at hag
    simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * a * c * t = c⁻¹ * (a * (c * t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * t * c⁻¹) * a) * c := by rw [hag]
      _ = t * (c⁻¹ * a * c) := by group
  obtain ⟨h, -, hh⟩ := SD.exists_conj_le_T (A := A) (Sec7.isPGroup_of_elemAbelianTwo hEel) hEt
  have hEel' : ElemAbelianTwo ((E.map f).map (MulAut.conj h).toMonoidHom) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hEel.comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hEel.sq_eq_one a ha, map_one]
  have h16 := card_le_of_elem_le_T h4 hEel' hh
  rw [card_map_of_injective (MulAut.conj h).injective, card_map_of_injective hfinj] at h16
  omega

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD

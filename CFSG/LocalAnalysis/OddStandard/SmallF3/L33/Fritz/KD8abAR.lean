module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAK
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAE
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8abAT

public noncomputable section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8ab
open CFSG.ComponentClassification.HSFLit.KD8ab

open KD7 Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace AD

theorem elemAbelianTwo_W (H : AD S T₁) : ElemAbelianTwo (MA.W.map H.ι) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, MA.W_comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, pow_two, MA.W_sq a ha, map_one]

theorem not_conjTo_of_comm_W (H : AD S T₁) {x : X} (hx : x ∉ H.G.D₁.S₁)
    (hc : ∀ c : MA, MA.inW c = true → x * H.ι c = H.ι c * x) : ¬ ConjTo t x := by
  intro hconj
  obtain ⟨g, hg⟩ := hconj
  have hx2 : x ^ 2 = 1 := by
    rw [← hg, pow_two, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group,
      tt (A := A), mul_one, mul_inv_cancel]
  have hxW : x ∉ MA.W.map H.ι := fun h => hx (by
    obtain ⟨a, -, rfl⟩ := h
    exact H.ι_mem_S₁ a)
  have hcW : ∀ a ∈ MA.W.map H.ι, x * a = a * x := by
    rintro _ ⟨a, ha, rfl⟩
    exact hc a ha
  obtain ⟨hel, -, hcard⟩ := (H.elemAbelianTwo_W).sup_zpowers hx2 hxW hcW
  refine not_conjTo_of_elem32 H.G.h4 hel ?_ (by
    rw [hcard, card_map_of_injective H.ι_injective, MA.card_W]) ⟨g, hg⟩
  rw [sup_le_iff]
  refine ⟨fun a ha => ?_, zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)⟩
  rw [mem_centralizer_singleton_iff]
  exact (hcW a ha).symm

theorem not_conjTo_M₀ (H : AD S T₁) {m : X} (hm : m ∈ MA.M.map H.ι) : ¬ ConjTo t m := by
  rintro hc
  obtain ⟨x, hx, rfl⟩ := hm
  have h1 := MA.Kc_not_M x (H.mem_Kc_of_conjTo hc)
  have h2 : MA.inM x = true := hx
  rw [h2] at h1
  exact Bool.noConfusion h1

namespace TD

variable {H : AD S T₁} (T : H.TD)

theorem actsW : T.p * H.ι MA.t * T.p⁻¹ = H.ι (MA.t * MA.u) ∧
    T.p * H.ι MA.u * T.p⁻¹ = H.ι MA.u ∧
    T.p * H.ι MA.y * T.p⁻¹ = H.ι (MA.y * MA.w₁ * cOne T.e) ∧
    T.p * H.ι MA.z * T.p⁻¹ = H.ι MA.z ∧ T.p * H.ι MA.k * T.p⁻¹ = H.ι MA.k ∧
    T.p * H.ι MA.w₁ * T.p⁻¹ = H.ι MA.w₁ ∧ T.p * H.ι MA.v * T.p⁻¹ = H.ι MA.v := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := actsW_pAct T.e T.c₂ T.hc₂
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [T.p_conj_ι (by decide +kernel)]
  exacts [by rw [h1], by rw [h2], by rw [h3], by rw [h4], by rw [h5], by rw [h6], by rw [h7]]

theorem exists_ζ : ∃ ζ ∈ MA.ZList,
    T.p * H.ι MA.w₂ * T.p⁻¹ = H.ι (MA.condWit (cOne T.e) * ζ) := by
  have hmem : T.p * H.ι MA.w₂ * T.p⁻¹ ∈ H.G.D₁.S₁ :=
    Sec7.conj_mem_of_mem_normalizer T.p_mem_normalizer (H.ι_mem_S₁ _)
  obtain ⟨s, hs⟩ := H.mem_range_of_mem_S₁ hmem
  set ζ := (MA.condWit (cOne T.e))⁻¹ * s with hζ
  have hζc : ∀ g ∈ [MA.u, MA.w₁, MA.v, MA.z, MA.y, MA.t, MA.k], g * ζ = ζ * g := by
    intro g hg
    have hgT : MA.inT1 g = true := gens7_T1 g hg
    have h1 : T.p⁻¹ * H.ι g * T.p = H.ι (pAct T.e T.c₂ g) := by
      have h2 := T.p_conj_ι hgT
      rw [T.p_inv] at h2 ⊢
      exact h2
    have h3 : MA.inT1 (MA.w₂ * pAct T.e T.c₂ g * MA.w₂⁻¹) = true :=
      MA.T1_normal _ _ (pAct_T1 T.e T.c₂ T.hc₂ g)
    have h4 : H.ι s * H.ι g * (H.ι s)⁻¹ =
        H.ι (MA.condWit (cOne T.e) * g * (MA.condWit (cOne T.e))⁻¹) := by
      rw [hs, ← pAct_w₂ T.e T.c₂ T.hc₂ g hgT, ← T.p_conj_ι h3, map_mul, map_mul, map_inv, ← h1]
      group
    have h5 : H.ι (s * g * s⁻¹) = H.ι (MA.condWit (cOne T.e) * g *
        (MA.condWit (cOne T.e))⁻¹) := by rw [map_mul, map_mul, map_inv, h4]
    have h6 := H.ι_injective h5
    rw [hζ]
    calc g * ((MA.condWit (cOne T.e))⁻¹ * s) =
        (MA.condWit (cOne T.e))⁻¹ * (MA.condWit (cOne T.e) * g * (MA.condWit (cOne T.e))⁻¹) *
          s := by group
      _ = (MA.condWit (cOne T.e))⁻¹ * (s * g * s⁻¹) * s := by rw [h6]
      _ = (MA.condWit (cOne T.e))⁻¹ * s * g := by group
  have hζZ : ζ ∈ MA.ZList := by
    rcases MA.cent_T1 ζ hζc with h | h | h | h <;> rw [h] <;> simp [MA.ZList]
  exact ⟨ζ, hζZ, by rw [← hs, hζ, mul_inv_cancel_left]⟩

theorem exists_ρ : ∃ ρ : MA, MA.inW ρ = true ∧ T.p * H.ι MA.w₂ * T.p⁻¹ = H.ι (MA.w₂ * ρ) := by
  obtain ⟨ζ, hζZ, h⟩ := T.exists_ζ
  refine ⟨MA.w₂ * (MA.condWit (cOne T.e) * ζ),
    MA.condW_wit_W (cOne T.e) (cOne_mem T.e) ζ hζZ, ?_⟩
  rw [h, ← mul_assoc, MA.w₂_sq, one_mul]

theorem p_conj_W {c : MA} (hc : MA.inW c = true) : T.p * H.ι c * T.p⁻¹ = H.ι c := by
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := T.actsW
  have := map_mem_of_inSpan H.ι (MA.W_span c hc) (H := centralizer ({T.p} : Set X))
    fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rw [mem_centralizer_singleton_iff]
      rcases hg with rfl | rfl | rfl | rfl
      · calc H.ι MA.w₁ * T.p = (T.p * H.ι MA.w₁ * T.p⁻¹) * T.p := by rw [h6]
          _ = T.p * H.ι MA.w₁ := by group
      · calc H.ι MA.v * T.p = (T.p * H.ι MA.v * T.p⁻¹) * T.p := by rw [h7]
          _ = T.p * H.ι MA.v := by group
      · calc H.ι MA.z * T.p = (T.p * H.ι MA.z * T.p⁻¹) * T.p := by rw [h4]
          _ = T.p * H.ι MA.z := by group
      · calc H.ι MA.k * T.p = (T.p * H.ι MA.k * T.p⁻¹) * T.p := by rw [h5]
          _ = T.p * H.ι MA.k := by group
  rw [mem_centralizer_singleton_iff] at this
  rw [← this, mul_inv_cancel_right]

theorem p_conj_M1 {m : MA} (hm : MA.inM1 m = true) :
    ∃ c : MA, MA.inW c = true ∧ T.p * H.ι m * T.p⁻¹ = H.ι (m * c) := by
  obtain ⟨-, h2, h3, -, -, -, -⟩ := T.actsW
  have hcW : MA.inW (MA.w₁ * cOne T.e) = true :=
    MA.ZList_mul_W (cOne T.e) (cOne_mem T.e) MA.w₁ (by decide +kernel)
  obtain ⟨d, hd, hm'⟩ := MA.M1_decomp m hm
  have hpd := T.p_conj_W hd
  rcases hm' with rfl | rfl | rfl | rfl
  · exact ⟨1, by decide +kernel, by rw [hpd, mul_one]⟩
  · refine ⟨1, by decide +kernel, ?_⟩
    rw [map_mul, show T.p * (H.ι MA.u * H.ι d) * T.p⁻¹ = (T.p * H.ι MA.u * T.p⁻¹) *
      (T.p * H.ι d * T.p⁻¹) by group, h2, hpd, ← map_mul, mul_one]
  · refine ⟨MA.w₁ * cOne T.e, hcW, ?_⟩
    rw [map_mul, show T.p * (H.ι MA.y * H.ι d) * T.p⁻¹ = (T.p * H.ι MA.y * T.p⁻¹) *
      (T.p * H.ι d * T.p⁻¹) by group, h3, hpd, ← map_mul]
    congr 1
    rw [mul_assoc MA.y d, MA.W_comm d hd _ hcW]
    simp only [mul_assoc]
  · refine ⟨MA.w₁ * cOne T.e, hcW, ?_⟩
    rw [map_mul, map_mul, show T.p * (H.ι MA.u * H.ι MA.y * H.ι d) * T.p⁻¹ =
      (T.p * H.ι MA.u * T.p⁻¹) * (T.p * H.ι MA.y * T.p⁻¹) * (T.p * H.ι d * T.p⁻¹) by group,
      h2, h3, hpd, ← map_mul, ← map_mul]
    congr 1
    rw [mul_assoc (MA.u * MA.y) d, MA.W_comm d hd _ hcW]
    simp only [mul_assoc]

theorem p_conj_ι_mul (a b : MA) : T.p * H.ι (a * b) * T.p⁻¹ =
    (T.p * H.ι a * T.p⁻¹) * (T.p * H.ι b * T.p⁻¹) := by rw [map_mul]; group

theorem not_conjTo_of_not_mem {x : X} (hx : x ∈ T.R₂) (hxS : x ∉ H.G.D₁.S₁) :
    ¬ ConjTo t x := by
  have hxp : x * T.p⁻¹ ∈ H.G.D₁.S₁ := (T.mem_R₂ hx).resolve_left hxS
  set s := T.p⁻¹ * x with hs
  have hsS : s ∈ H.G.D₁.S₁ := by
    have := Sec7.conj_mem_of_mem_normalizer (inv_mem T.p_mem_normalizer) hxp
    rwa [show T.p⁻¹ * (x * T.p⁻¹) * T.p⁻¹⁻¹ = T.p⁻¹ * x by group] at this
  have hxe : x = T.p * s := by rw [hs]; group
  clear_value s
  obtain ⟨ŝ, rfl⟩ := H.mem_range_of_mem_S₁ hsS
  obtain ⟨ρ, hρ, hρe⟩ := T.exists_ρ
  have hσ : T.p * T.p = H.ι 1 := by rw [map_one, T.p_mul_p]
  have hσW : MA.inW 1 = true := MA.one_W
  have hpt : T.p * H.ι MA.t * T.p⁻¹ = H.ι (MA.t * MA.u) := T.actsW.1
  have hsq : ∀ y : X, x = T.p * y → x * x = (T.p * y * T.p⁻¹) * (T.p * T.p) * y := by
    intro y hy; rw [hy]; group
  have hinv : ∀ e : MA, x * x = H.ι e → MA.inW e = false → ¬ ConjTo t x := by
    intro e he hW ⟨g, hg⟩
    have h1 : x * x = 1 := by
      rw [← hg, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, tt (A := A),
        mul_one, mul_inv_cancel]
    rw [h1] at he
    have : e = 1 := H.ι_injective (by rw [← he, map_one])
    rw [this, MA.one_W] at hW
    exact Bool.noConfusion hW
  have hcomm_x : ∀ c : MA, ŝ * c = c * ŝ → MA.inW c = true → x * H.ι c = H.ι c * x := by
    intro c hsc hc
    calc x * H.ι c = T.p * H.ι (ŝ * c) := by rw [hxe, map_mul, mul_assoc]
      _ = T.p * H.ι (c * ŝ) := by rw [hsc]
      _ = (T.p * H.ι c * T.p⁻¹) * (T.p * H.ι ŝ) := by rw [map_mul]; group
      _ = H.ι c * x := by rw [T.p_conj_W hc, hxe]
  rcases MA.decomp ŝ with h | h | h | h
  · exact H.not_conjTo_of_comm_W hxS fun c hc => hcomm_x c (MA.M1_comm_W ŝ h c hc) hc
  · set m := MA.t * ŝ with hm
    have hŝ : ŝ = MA.t * m := by
      rw [hm, ← mul_assoc, show MA.t * MA.t = 1 by decide +kernel, one_mul]
    obtain ⟨c, hcW, hc⟩ := T.p_conj_M1 h
    refine hinv (MA.t * MA.u * m * (c * 1) * MA.t * m) ?_
      (MA.cert1 m h _ (MA.W_mul c hcW 1 hσW))
    rw [hsq _ hxe, hŝ, T.p_conj_ι_mul, hpt, hc, hσ]
    simp only [map_mul, map_one, mul_one]
    group
  · refine H.not_conjTo_of_comm_W hxS fun c hc => hcomm_x c ?_ hc
    calc ŝ * c = MA.w₂ * ((MA.w₂ * ŝ) * c) := by
          rw [← mul_assoc, ← mul_assoc, MA.w₂_sq, one_mul]
      _ = MA.w₂ * (c * (MA.w₂ * ŝ)) := by rw [MA.M1_comm_W _ h c hc]
      _ = (MA.w₂ * c) * (MA.w₂ * ŝ) := by rw [mul_assoc]
      _ = (c * MA.w₂) * (MA.w₂ * ŝ) := by rw [MA.w₂_comm_W' c hc]
      _ = c * ŝ := by rw [mul_assoc, ← mul_assoc MA.w₂, MA.w₂_sq, one_mul]
  · set m := MA.t * (MA.w₂ * ŝ) with hm
    have hŝ : ŝ = MA.w₂ * MA.t * m := by
      rw [hm, show MA.w₂ * MA.t * (MA.t * (MA.w₂ * ŝ)) = MA.w₂ * (MA.t * MA.t) * MA.w₂ * ŝ by
        group, show MA.t * MA.t = 1 by decide +kernel, mul_one, MA.w₂_sq, one_mul]
    obtain ⟨c, hcW, hc⟩ := T.p_conj_M1 h
    set ρ' := (MA.t * MA.u * m)⁻¹ * ρ * (MA.t * MA.u * m) with hρ'
    have hρ'W : MA.inW ρ' = true := by
      have := MA.W_normal (MA.t * MA.u * m)⁻¹ ρ hρ
      rwa [inv_inv] at this
    refine hinv (MA.w₂ * MA.t * MA.u * m * (ρ' * c * 1) * MA.w₂ * MA.t * m) ?_
      (MA.cert2 m h _ (MA.W_mul _ (MA.W_mul ρ' hρ'W c hcW) 1 hσW))
    rw [hsq _ hxe, hŝ, T.p_conj_ι_mul, T.p_conj_ι_mul, hρe, hpt, hc, hσ, hρ']
    simp only [map_mul, map_inv, map_one, mul_one]
    group

theorem exists_conj_R₂ {x : X} (hx : x ∈ T.R₂) (hc : ConjTo t x) :
    ∃ r ∈ T.R₂, x = r * t * r⁻¹ := by
  by_cases hxS : x ∈ H.G.D₁.S₁
  · obtain ⟨x', rfl⟩ := H.mem_range_of_mem_S₁ hxS
    rcases MA.Kc_conj x' (H.mem_Kc_of_conjTo hc) with ⟨s, hs⟩ | ⟨s, hs⟩
    · refine ⟨H.ι s, T.ι_mem_R₂ s, ?_⟩
      rw [← hs, map_mul, map_mul, map_inv, H.ι_t]
    · refine ⟨H.ι s * T.p, mul_mem (T.ι_mem_R₂ s) T.p_mem_R₂, ?_⟩
      rw [← hs, map_mul, map_mul, map_inv, ← T.actsW.1, H.ι_t]
      group
  · exact absurd hc (T.not_conjTo_of_not_mem hx hxS)

theorem p_mem_normalizer_M₀ : T.p ∈ normalizer ((MA.M.map H.ι : Subgroup X) : Set X) := by
  have hle : (MA.M.map H.ι).map (MulAut.conj T.p).toMonoidHom ≤ MA.M.map H.ι := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hconj := map_mem_of_inSpan ((MulAut.conj T.p).toMonoidHom.comp H.ι) (MA.M_span x hx)
      (H := MA.M.map H.ι) fun g hg => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        obtain ⟨ρ, hρ, hρe⟩ := T.exists_ρ
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := T.actsW
        have hM : ∀ y : MA, MA.inM y = true → H.ι y ∈ MA.M.map H.ι := fun y hy => ⟨y, hy, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hρe]; exact hM _ (MA.inM_w₂W ρ hρ)
        · rw [h2]; exact hM _ (by decide +kernel)
        · rw [h6]; exact hM _ (by decide +kernel)
        · rw [h7]; exact hM _ (by decide +kernel)
        · rw [h4]; exact hM _ (by decide +kernel)
        · rw [h3]
          exact hM _ (MA.M.mul_mem (MA.M.mul_mem (show MA.inM MA.y = true by decide +kernel)
            (show MA.inM MA.w₁ = true by decide +kernel)) (MA.ZList_M _ (cOne_mem T.e)))
        · rw [h5]; exact hM _ (by decide +kernel)
    simpa using hconj
  exact Sec7.mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (card_map_of_injective (MulAut.conj T.p).injective).symm))

@[expose] noncomputable def M : Subgroup X := MA.M.map H.ι ⊔ zpowers T.p

theorem M_le_R₂ : T.M ≤ T.R₂ := by
  refine sup_le ?_ (zpowers_le.mpr T.p_mem_R₂)
  rintro _ ⟨a, -, rfl⟩; exact T.ι_mem_R₂ a

theorem not_conjTo_M {m : X} (hm : m ∈ T.M) : ¬ ConjTo t m := by
  rcases Sec7.mem_or_of_mem_sup_zpowers T.p_mem_normalizer_M₀
    (by rw [T.p_sq]; exact one_mem _) hm with h | h
  · exact H.not_conjTo_M₀ h
  · refine T.not_conjTo_of_not_mem (T.M_le_R₂ hm) fun hS => T.p_not_mem_S₁ ?_
    obtain ⟨a, -, ha⟩ := h
    have := mul_mem (inv_mem (show m * T.p⁻¹ ∈ H.G.D₁.S₁ by rw [← ha]; exact H.ι_mem_S₁ a)) hS
    rwa [show (m * T.p⁻¹)⁻¹ * m = T.p by group] at this

end TD

end AD

end KD8ab

end CFSG.OddStandard.SmallF3.L33.KD

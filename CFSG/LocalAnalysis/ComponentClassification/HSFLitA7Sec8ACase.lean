module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8AR2

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

omit [Finite X] in
theorem relIndex_sup_zpowers {H : Subgroup X} {g : X} (hN : g ∈ normalizer (H : Set X))
    (hg2 : g * g ∈ H) (hg : g ∉ H) : H.relIndex (H ⊔ zpowers g) = 2 := by
  rw [relIndex, index_eq_two_iff]
  refine ⟨⟨g, mem_sup_right (mem_zpowers _)⟩, fun ⟨b, hb⟩ => ?_⟩
  simp only [mem_subgroupOf, Subgroup.coe_mul]
  rcases mem_or_of_mem_sup_zpowers hN (by rw [pow_two]; exact hg2) hb with h | h
  · refine Or.inr ⟨h, fun h' => hg ?_⟩
    have := mul_mem (inv_mem h) h'
    rwa [inv_mul_cancel_left] at this
  · refine Or.inl ⟨?_, fun h' => hg ?_⟩
    · have := mul_mem h hg2
      rwa [show b * g⁻¹ * (g * g) = b * g by group] at this
    · have := mul_mem (inv_mem h') h
      rwa [show b⁻¹ * (b * g⁻¹) = g⁻¹ by group, inv_mem_iff] at this

omit [Finite X] in
theorem card_sup_zpowers {H : Subgroup X} {g : X} (hN : g ∈ normalizer (H : Set X))
    (hg2 : g * g ∈ H) (hg : g ∉ H) : Nat.card (H ⊔ zpowers g : Subgroup X) = 2 * Nat.card H := by
  have h1 := card_mul_index (H.subgroupOf (H ⊔ zpowers g))
  rw [show Nat.card (H.subgroupOf (H ⊔ zpowers g)) = Nat.card H from
    Nat.card_congr (subgroupOfEquivOfLe le_sup_left).toEquiv] at h1
  rw [← h1, ← relIndex, relIndex_sup_zpowers hN hg2 hg, mul_comm]

namespace AData

variable (A : AData S F T₁)

noncomputable def Wsub : Subgroup X := MA.W.map A.ι

theorem elemAbelianTwo_W : ElemAbelianTwo A.Wsub := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, MA.W_comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, pow_two, MA.W_sq a ha, map_one]

theorem card_W : Nat.card A.Wsub = 16 := by
  rw [Wsub, card_map_of_injective A.ι_injective, MA.card_W]

theorem not_conjTo_of_comm_W {x : X} (hx : x ∉ A.D₁.S₁)
    (hc : ∀ c : MA, MA.inW c = true → x * A.ι c = A.ι c * x) : ¬ ConjTo S.t x := by
  intro hconj
  obtain ⟨g, hg⟩ := hconj
  have hx2 : x ^ 2 = 1 := by
    rw [← hg, pow_two, show g * S.t * g⁻¹ * (g * S.t * g⁻¹) = g * (S.t * S.t) * g⁻¹ by group,
      t_mul_t, mul_one, mul_inv_cancel]
  have hxW : x ∉ A.Wsub := fun h => hx (by
    obtain ⟨a, -, rfl⟩ := h
    exact A.ι_mem_S₁ a)
  have hcW : ∀ a ∈ A.Wsub, x * a = a * x := by
    rintro _ ⟨a, ha, rfl⟩
    exact hc a ha
  obtain ⟨hel, -, hcard⟩ := A.elemAbelianTwo_W.sup_zpowers hx2 hxW hcW
  refine not_conjTo_of_elem hel ?_ (by rw [hcard, A.card_W]) ⟨g, hg⟩
  rw [sup_le_iff]
  refine ⟨fun a ha => ?_, zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)⟩
  rw [mem_centralizer_singleton_iff]
  exact (hcW a ha).symm

variable {A}

namespace PData

variable (B : A.PData)

theorem p_conj_ι_mul (a b : MA) : B.p * A.ι (a * b) * B.p⁻¹ =
    (B.p * A.ι a * B.p⁻¹) * (B.p * A.ι b * B.p⁻¹) := by rw [map_mul]; group

theorem not_conjTo_of_not_mem {x : X} (hx : x ∈ B.R₂) (hxS : x ∉ A.D₁.S₁) :
    ¬ ConjTo S.t x := by
  have hxp : x * B.p⁻¹ ∈ A.D₁.S₁ := (B.mem_R₂ hx).resolve_left hxS
  set s := B.p⁻¹ * x with hs
  have hsS : s ∈ A.D₁.S₁ := by
    have := conj_mem_of_mem_normalizer (inv_mem B.hN) hxp
    rwa [show B.p⁻¹ * (x * B.p⁻¹) * B.p⁻¹⁻¹ = B.p⁻¹ * x by group] at this
  have hxe : x = B.p * s := by rw [hs]; group
  clear_value s
  obtain ⟨ŝ, rfl⟩ := A.mem_range_of_mem_S₁ hsS
  obtain ⟨σ, hσ, hσe⟩ := B.exists_σ
  obtain ⟨ρ, hρ, hρe⟩ := B.exists_ρ
  have hσW : MA.inW σ = true := MA.ZList_W σ hσ
  have hpt : B.p * A.ι MA.t * B.p⁻¹ = A.ι (MA.t * MA.u) := B.hW.1
  have hsq : ∀ y : X, x = B.p * y → x * x = (B.p * y * B.p⁻¹) * (B.p * B.p) * y := by
    intro y hy; rw [hy]; group
  have hinv : ∀ e : MA, x * x = A.ι e → MA.inW e = false → ¬ ConjTo S.t x := by
    intro e he hW ⟨g, hg⟩
    have h1 : x * x = 1 := by
      rw [← hg, show g * S.t * g⁻¹ * (g * S.t * g⁻¹) = g * (S.t * S.t) * g⁻¹ by group, t_mul_t,
        mul_one, mul_inv_cancel]
    rw [h1] at he
    have : e = 1 := A.ι_injective (by rw [← he, map_one])
    rw [this, MA.one_W] at hW
    exact Bool.noConfusion hW
  have hcomm_x : ∀ c : MA, ŝ * c = c * ŝ → MA.inW c = true → x * A.ι c = A.ι c * x := by
    intro c hsc hc
    calc x * A.ι c = B.p * A.ι (ŝ * c) := by rw [hxe, map_mul, mul_assoc]
      _ = B.p * A.ι (c * ŝ) := by rw [hsc]
      _ = (B.p * A.ι c * B.p⁻¹) * (B.p * A.ι ŝ) := by rw [map_mul]; group
      _ = A.ι c * x := by rw [B.p_conj_W hc, hxe]
  rcases MA.decomp ŝ with h | h | h | h
  ·
    exact A.not_conjTo_of_comm_W hxS fun c hc => hcomm_x c (MA.M1_comm_W ŝ h c hc) hc
  ·
    set m := MA.t * ŝ with hm
    have hŝ : ŝ = MA.t * m := by rw [hm, ← mul_assoc, show MA.t * MA.t = 1 by decide +kernel,
      one_mul]
    obtain ⟨c, hcW, hc⟩ := B.p_conj_M1 h
    refine hinv (MA.t * MA.u * m * (c * σ) * MA.t * m) ?_ (MA.cert1 m h _ (MA.W_mul c hcW σ hσW))
    rw [hsq _ hxe, hŝ, B.p_conj_ι_mul, hpt, hc, hσe]
    simp only [map_mul]
    group
  ·
    refine A.not_conjTo_of_comm_W hxS fun c hc => hcomm_x c ?_ hc
    calc ŝ * c = MA.w₂ * ((MA.w₂ * ŝ) * c) := by rw [← mul_assoc, ← mul_assoc, MA.w₂_sq, one_mul]
      _ = MA.w₂ * (c * (MA.w₂ * ŝ)) := by rw [MA.M1_comm_W _ h c hc]
      _ = (MA.w₂ * c) * (MA.w₂ * ŝ) := by rw [mul_assoc]
      _ = (c * MA.w₂) * (MA.w₂ * ŝ) := by rw [MA.w₂_comm_W' c hc]
      _ = c * ŝ := by rw [mul_assoc, ← mul_assoc MA.w₂, MA.w₂_sq, one_mul]
  ·
    set m := MA.t * (MA.w₂ * ŝ) with hm
    have hŝ : ŝ = MA.w₂ * MA.t * m := by
      rw [hm, show MA.w₂ * MA.t * (MA.t * (MA.w₂ * ŝ)) = MA.w₂ * (MA.t * MA.t) * MA.w₂ * ŝ by
        group, show MA.t * MA.t = 1 by decide +kernel, mul_one, MA.w₂_sq, one_mul]
    obtain ⟨c, hcW, hc⟩ := B.p_conj_M1 h
    set ρ' := (MA.t * MA.u * m)⁻¹ * ρ * (MA.t * MA.u * m) with hρ'
    have hρ'W : MA.inW ρ' = true := by
      have := MA.W_normal (MA.t * MA.u * m)⁻¹ ρ hρ
      rwa [inv_inv] at this
    refine hinv (MA.w₂ * MA.t * MA.u * m * (ρ' * c * σ) * MA.w₂ * MA.t * m) ?_
      (MA.cert2 m h _ (MA.W_mul _ (MA.W_mul ρ' hρ'W c hcW) σ hσW))
    rw [hsq _ hxe, hŝ, B.p_conj_ι_mul, B.p_conj_ι_mul, hρe, hpt, hc, hσe, hρ']
    simp only [map_mul, map_inv]
    group

theorem card_S₁_R₂ : Nat.card B.R₂ = 2 * Nat.card A.D₁.S₁ :=
  card_sup_zpowers B.hN B.p_sq_mem_S₁ B.p_not_mem_S₁

theorem exists_conj_R₂ {x : X} (hx : x ∈ B.R₂) (hc : ConjTo S.t x) :
    ∃ r ∈ B.R₂, x = r * S.t * r⁻¹ := by
  by_cases hxS : x ∈ A.D₁.S₁
  · obtain ⟨x', rfl⟩ := A.mem_range_of_mem_S₁ hxS
    rcases MA.Kc_conj x' (A.mem_Kc_of_conjTo hc) with ⟨s, hs⟩ | ⟨s, hs⟩
    · refine ⟨A.ι s, B.S₁_le_R₂ (A.ι_mem_S₁ s), ?_⟩
      rw [← hs, map_mul, map_mul, map_inv, A.ι_t]
    · refine ⟨A.ι s * B.p, mul_mem (B.S₁_le_R₂ (A.ι_mem_S₁ s)) B.p_mem_R₂, ?_⟩
      rw [← hs, map_mul, map_mul, map_inv, ← B.p_conj_t]
      group
  · exact absurd hc (B.not_conjTo_of_not_mem hx hxS)

theorem maximal (hnc : ¬ SubConj F.E₁ F.E₂) {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hle : B.R₂ ≤ Q) : Q = B.R₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨h, hhQ, hhN, hhR⟩ : ∃ h ∈ Q, h ∈ normalizer (B.R₂ : Set X) ∧ h ∉ B.R₂ := by
    set I := B.R₂.subgroupOf Q with hI
    have hIne : I ≠ ⊤ := by
      intro htop
      apply hne
      refine le_antisymm (fun x hx => ?_) hle
      have : (⟨x, hx⟩ : Q) ∈ I := by rw [htop]; trivial
      exact this
    have hnil : Group.IsNilpotent Q := hQ.isNilpotent
    have hlt : I < normalizer (I : Set Q) :=
      Group.normalizerCondition_of_isNilpotent I (lt_of_le_of_ne le_top hIne)
    obtain ⟨x, hxN, hxI⟩ := IsConcreteLE.exists_of_lt hlt
    refine ⟨x, x.2, ?_, fun h => hxI h⟩
    have hxsub : x ∈ (normalizer (B.R₂ : Set X)).subgroupOf Q := by
      rw [subgroupOf_normalizer_eq hle]
      exact hxN
    exact mem_subgroupOf.mp hxsub
  have hE₁R : ∀ e ∈ S.E F.yF, e ∈ B.R₂ := fun e he =>
    B.S₁_le_R₂ (A.T₁_le_S₁ (A.E₁_le_T₁ he))
  have hτR : h * S.t * h⁻¹ ∈ B.R₂ := conj_mem_of_mem_normalizer hhN (hE₁R _ (t_mem_E _))
  obtain ⟨r, hrR, hr⟩ := B.exists_conj_R₂ hτR ⟨h, rfl⟩
  set g := r⁻¹ * h with hg
  have hgQ : g ∈ Q := mul_mem (inv_mem (hle hrR)) hhQ
  have hgt : g * S.t * g⁻¹ = S.t := by
    rw [hg, show r⁻¹ * h * S.t * (r⁻¹ * h)⁻¹ = r⁻¹ * (h * S.t * h⁻¹) * r by group, hr]; group
  have hgR : ∀ e ∈ S.E F.yF, g * e * g⁻¹ ∈ B.R₂ := by
    intro e he
    rw [hg, show r⁻¹ * h * e * (r⁻¹ * h)⁻¹ = r⁻¹ * (h * e * h⁻¹) * r⁻¹⁻¹ by group]
    exact mul_mem (mul_mem (inv_mem hrR) (conj_mem_of_mem_normalizer hhN (hE₁R e he)))
      (inv_mem (inv_mem hrR))
  set A' := (S.E F.yF).map (MulAut.conj g).toMonoidHom with hA'
  have hTR : S.data.T ≤ B.R₂ := A.T_le_T₁.trans (A.T₁_le_S₁.trans B.S₁_le_R₂)
  have hA'T : A' ≤ S.data.T := by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine S.data.mem_T_of_commute B.isPGroup_R₂ hTR (hgR e he) ?_
    have hte : e * S.t = S.t * e := ((isRefl_yF F).elemAbelianTwo_E).comm _ he _ (t_mem_E _)
    calc g * e * g⁻¹ * S.t = g * e * g⁻¹ * (g * S.t * g⁻¹) := by rw [hgt]
      _ = g * (e * S.t) * g⁻¹ := by group
      _ = g * (S.t * e) * g⁻¹ := by rw [hte]
      _ = (g * S.t * g⁻¹) * (g * e * g⁻¹) := by group
      _ = S.t * (g * e * g⁻¹) := by rw [hgt]
  have hA'el : ElemAbelianTwo A' := by
    have hE := (isRefl_yF F).elemAbelianTwo_E
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hE.comm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.sq_eq_one x hx, map_one]
  have hA'card : Nat.card A' = 16 := by
    rw [hA', card_map_of_injective (MulAut.conj g).injective, (isRefl_yF F).card_E]
  rcases eq_E_of_elem_le_T F hA'el hA'T hA'card with h1 | h2
  ·
    have hgE : g ∈ normalizer (S.E F.yF : Set X) := mem_normalizer_of_map_eq h1
    have hmax := A.D₁.S₁_maximal (A.D₁.S₁ ⊔ zpowers g)
      (hQ.to_le (sup_le (B.S₁_le_R₂.trans hle) (zpowers_le.mpr hgQ))) le_sup_left
      (sup_le A.D₁.S₁_le (zpowers_le.mpr hgE))
    have hgS : g ∈ A.D₁.S₁ := hmax ▸ mem_sup_right (mem_zpowers g)
    apply hhR
    rw [show h = r * g by rw [hg]; group]
    exact mul_mem hrR (B.S₁_le_R₂ hgS)
  · exact hnc ⟨g, h2⟩

theorem p_mem_normalizer_M₀ : B.p ∈ normalizer (A.M₀ : Set X) := by
  have hle : A.M₀.map (MulAut.conj B.p).toMonoidHom ≤ A.M₀ := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hconj := map_mem_of_inSpan ((MulAut.conj B.p).toMonoidHom.comp A.ι) (MA.M_span x hx)
      (H := A.M₀) fun g hg => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply]
        obtain ⟨ρ, hρ, hρe⟩ := B.exists_ρ
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := B.hW
        have hM : ∀ y : MA, MA.inM y = true → A.ι y ∈ A.M₀ := fun y hy => ⟨y, hy, rfl⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [hρe]; exact hM _ (MA.inM_w₂W ρ hρ)
        · rw [h2]; exact hM _ (by decide +kernel)
        · rw [h6]; exact hM _ (by decide +kernel)
        · rw [h7]; exact hM _ (by decide +kernel)
        · rw [h4]; exact hM _ (by decide +kernel)
        · rw [h3]
          exact hM _ (MA.M.mul_mem (MA.M.mul_mem (show MA.inM MA.y = true by decide +kernel)
            (show MA.inM MA.w₁ = true by decide +kernel)) (MA.ZList_M _ B.hc))
        · rw [h5]; exact hM _ (by decide +kernel)
    simpa using hconj
  exact mem_normalizer_of_map_eq (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_map_of_injective (MulAut.conj _).injective]))

noncomputable def Mt : Subgroup X := A.M₀ ⊔ zpowers B.p

theorem p_sq_mem_M₀ : B.p * B.p ∈ A.M₀ := by
  obtain ⟨σ, hσ, hσe⟩ := B.exists_σ
  rw [hσe]; exact ⟨σ, MA.ZList_M σ hσ, rfl⟩

theorem p_not_mem_M₀ : B.p ∉ A.M₀ := fun h => B.p_not_mem_S₁ (A.M₀_le h)

theorem Mt_le : B.Mt ≤ B.R₂ := sup_le (A.M₀_le.trans B.S₁_le_R₂) (zpowers_le.mpr B.p_mem_R₂)

theorem card_Mt : Nat.card B.Mt = 256 := by
  rw [Mt, card_sup_zpowers B.p_mem_normalizer_M₀ B.p_sq_mem_M₀ B.p_not_mem_M₀, A.card_M₀]

theorem relIndex_Mt : B.Mt.relIndex B.R₂ = 2 := by
  have h1 := card_mul_index (B.Mt.subgroupOf B.R₂)
  rw [show Nat.card (B.Mt.subgroupOf B.R₂) = Nat.card B.Mt from
    Nat.card_congr (subgroupOfEquivOfLe B.Mt_le).toEquiv, B.card_Mt,
    show Nat.card B.R₂ = 512 by rw [B.card_S₁_R₂, A.card_S₁]] at h1
  rw [relIndex]
  omega

theorem not_conjTo_Mt {m : X} (hm : m ∈ B.Mt) : ¬ ConjTo S.t m := by
  rcases mem_or_of_mem_sup_zpowers B.p_mem_normalizer_M₀ (by rw [pow_two]; exact B.p_sq_mem_M₀)
    hm with h | h
  · exact A.not_conjTo_M₀ h
  · refine B.not_conjTo_of_not_mem (B.Mt_le hm) fun hS => B.p_not_mem_S₁ ?_
    have := mul_mem (inv_mem (A.M₀_le h)) hS
    rwa [show (m * B.p⁻¹)⁻¹ * m = B.p by group] at this

include B in
theorem false_of [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (hnc : ¬ SubConj F.E₁ F.E₂) : False :=
  false_of_transfer (S := S) hX (sylowOfMax B.isPGroup_R₂ fun _ hQ hle => B.maximal hnc hQ hle)
    B.Mt_le B.relIndex_Mt fun _ hm => B.not_conjTo_Mt hm

end PData

include A in
theorem false_of [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (hnc : ¬ SubConj F.E₁ F.E₂) : False := by
  obtain ⟨B⟩ := A.nonempty_PData
  exact PData.false_of B hX hnc

end AData

end Sec8

end CFSG.ComponentClassification.HSFLit

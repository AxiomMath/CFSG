module

public import CFSG.CGT.Foote81L6.TStruct.Transvect

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem inf_A_eq_repU (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E) : E ⊓ D.A = D.repU := by
  rw [D.repU_eq_A hm, inf_of_le_right (D.A_le_E64 hm hE)]

theorem exists_conj_Frep01_of_asymm (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E)
    (hasym : (D.typ E).1 ≠ (D.typ E).2) :
    ∃ h ∈ T, E.map (MulAut.conj h).toMonoidHom = D.Frep 0 1 := by
  obtain ⟨h, hh, e | e | e⟩ := D.exists_conj_Frep_of_inf_A hE (D.inf_A_eq_repU hm hE)
  · exfalso
    have := (D.typ_symm_map_conj_iff hE (D.T₀_le_T hh)).1
    rw [e, typ_Frep] at this
    exact hasym (this rfl)
  · exfalso
    have := (D.typ_symm_map_conj_iff hE (D.T₀_le_T hh)).1
    rw [e, typ_Frep] at this
    exact hasym (this rfl)
  · exact ⟨h, D.T₀_le_T hh, e⟩

theorem asymm_of_eq_map_conj_Frep01 {E : Subgroup G} {h : G} (hh : h ∈ T)
    (hEh : E = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) :
    IsE64 T E ∧ (D.typ E).1 ≠ (D.typ E).2 := by
  subst hEh
  refine ⟨(D.isE64_Frep 0 1).map_conj hh, fun h1 => ?_⟩
  have := (D.typ_symm_map_conj_iff (D.isE64_Frep 0 1) hh).1 h1
  rw [typ_Frep] at this
  exact absurd this (by decide)

theorem exists_tprime_of_asymm (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E)
    (hasym : (D.typ E).1 ≠ (D.typ E).2) :
    ∃ t' ∈ T ⊓ normalizer (E : Set G), t' * t' = 1 ∧ t' * D.t⁻¹ ∈ D.T₁ := by
  have hP := D.isE16_inf_B₀B₁ hE
  obtain ⟨hPdec, hV, -⟩ := D.E16_decomp hP
  have hasym' : (D.typ (E ⊓ (D.B₀ ⊔ D.B₁))).1 ≠ (D.typ (E ⊓ (D.B₀ ⊔ D.B₁))).2 := by
    rwa [D.typ_inf_B₀B₁]
  obtain ⟨β, hβ, hβP⟩ := D.exists_conj_E16_of_typ_eq (D.isE16_tConj hP) hP
    (D.typ_tConj_of_asymm hP hasym')
  have hxN : β * D.t ∈ normalizer ((E ⊓ (D.B₀ ⊔ D.B₁) : Subgroup G) : Set G) := by
    apply mem_normalizer_of_map_conj_eq
    rw [← map_conj_map_conj]
    exact hβP
  obtain ⟨c, hc, hcP⟩ := D.exists_conj_pairT hP.2.2 hV (x := β * D.t)
    (by rw [mul_inv_cancel_right]; exact hβ) hxN
  have hcT : c ∈ T := D.T₁_le_T (D.B₀B₁_le_T₁ hc)
  have htN : c * D.t * c⁻¹ ∈ normalizer ((E ⊓ (D.B₀ ⊔ D.B₁) : Subgroup G) : Set G) :=
    conj_mem_normalizer_of_map_conj_eq hcP (D.t_mem_normalizer_pairT _)
  have ht'T : c * D.t * c⁻¹ ∈ T := mul_mem (mul_mem hcT D.t_mem_T) (inv_mem hcT)
  refine ⟨c * D.t * c⁻¹, mem_inf.2 ⟨ht'T, ?_⟩, ?_, ?_⟩
  · apply mem_normalizer_of_map_conj_eq
    have hdec : E = D.A ⊔ (E ⊓ (D.B₀ ⊔ D.B₁)) := by
      apply le_antisymm
      · intro x hx
        obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hx
        refine mul_mem (mem_sup_left (mem_inf.1 hu).2) (mem_sup_right (mem_inf.2 ⟨?_, ?_⟩))
        · exact mul_mem (mem_inf.1 hw₀).1 (mem_inf.1 hw₁).1
        · exact mul_mem (mem_sup_left (mem_inf.1 hw₀).2) (mem_sup_right (mem_inf.1 hw₁).2)
      · exact sup_le (D.A_le_E64 hm hE) inf_le_left
    conv_lhs => rw [hdec]
    rw [Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer htN,
      map_conj_eq_self_of_mem_normalizer (D.T_le_normalizer_A ht'T)]
    exact hdec.symm
  · calc c * D.t * c⁻¹ * (c * D.t * c⁻¹) = c * (D.t * D.t) * c⁻¹ := by group
      _ = 1 := by rw [D.t_mul_t, mul_one, mul_inv_cancel]
  · rw [show c * D.t * c⁻¹ * D.t⁻¹ = c * (D.t * c⁻¹ * D.t⁻¹) by group]
    exact D.B₀B₁_le_T₁ (mul_mem hc (D.conj_mem_B₀B₁ D.t_mem_T (inv_mem hc)))

theorem exists_tprime (hm : m = 2) {E : Subgroup G}
    (hE : ∃ h ∈ T, E = (D.Frep 0 1).map (MulAut.conj h).toMonoidHom) :
    ∃ t' ∈ T ⊓ normalizer (E : Set G), t' * t' = 1 ∧ t' * D.t⁻¹ ∈ D.T₁ := by
  obtain ⟨h, hh, hEh⟩ := hE
  obtain ⟨hE64, hasym⟩ := D.asymm_of_eq_map_conj_Frep01 hh hEh
  exact D.exists_tprime_of_asymm hm hE64 hasym

theorem Astar_sup_eq {X : Subgroup G} (hb : D.b ∈ X) : D.Astar ⊔ X = D.A ⊔ X := by
  have hbX : ∀ u, D.bHom u ∈ X := fun u => by
    rcases D.bHom_mem u with h | h <;> rw [h]
    · exact one_mem _
    · exact hb
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    rw [D.Astar_eq_map]
    rintro _ ⟨g, hg, rfl⟩
    rw [D.starHom_apply]
    exact mul_mem (mem_sup_left (D.mem_Apart_iff.1 hg)) (mem_sup_right (hbX _))
  · refine sup_le (fun x hx => ?_) le_sup_right
    have hmem : D.starHom ⟨x, mem_sup_left hx⟩ ∈ D.Astar := by
      rw [D.Astar_eq_map]
      exact ⟨_, D.mem_Apart_iff.2 hx, rfl⟩
    have e : x = D.starHom ⟨x, mem_sup_left hx⟩ * (D.bHom (D.delta ⟨x, mem_sup_left hx⟩))⁻¹ := by
      rw [D.starHom_apply, mul_inv_cancel_right]
    rw [e]
    exact mul_mem (mem_sup_left hmem) (mem_sup_right (inv_mem (hbX _)))

theorem star_repW (i : ZMod 2) : D.star.repW i = D.repW i := rfl

theorem star_sConj (X : Subgroup G) : D.star.sConj X = D.sConj X := rfl

theorem b_mem_repW_sup (i j : ZMod 2) : D.b ∈ D.repW i ⊔ D.sConj (D.repW j) :=
  mul_mem (mem_sup_left (D.b₀_mem_of_isFourIn (D.isFourIn_repW i)))
    (mem_sup_right (D.b₁_mem_of_isFourIn (D.isFourIn_sConj₀ (D.isFourIn_repW j))))

theorem star_Frep (hm : m = 2) (i j : ZMod 2) : D.star.Frep i j = D.Frep i j := by
  rw [Frep, Frep, D.star.repU_eq_A hm, D.repU_eq_A hm, star_A, star_repW, star_repW, star_sConj]
  exact D.Astar_sup_eq (D.b_mem_repW_sup i j)

theorem exists_conj_Frep01_of_mem (hm : m = 2) {x : G}
    (hx : x ∈ D.A ⊔ (D.B₀ ⊔ zpowers D.b₁)) (hx2 : x * x = 1) :
    ∃ h ∈ T, x ∈ (D.Frep 0 1).map (MulAut.conj h).toMonoidHom := by
  have hZB : D.B₀ ⊔ zpowers D.b₁ ≤ D.B := sup_le D.B₀_le_B (zpowers_le.2 D.b₁_mem_B)
  obtain ⟨α, hα, y, hy, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
    fun u hu w hw => D.A_comm_B u hu w (hZB hw))).1 hx
  obtain ⟨r, hr, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
    fun u hu w hw => D.B₀_comm_B₁ u hu w ((zpowers_le.2 D.b₁_mem) hw))).1 hy
  have hz2 : z * z = 1 := by
    rcases eq_one_or_eq_of_mem_zpowers D.b₁_mul_b₁ hz with rfl | rfl
    · exact mul_one 1
    · exact D.b₁_mul_b₁
  have hαy : α * (r * z) = (r * z) * α := D.A_comm_B α hα _ (hZB hy)
  have hrz : r * z = z * r := D.B₀_comm_B₁ r hr z ((zpowers_le.2 D.b₁_mem) hz)
  have hsq : α * α * ((r * z) * (r * z)) = 1 * 1 := by
    rw [mul_one, ← hx2]
    calc α * α * ((r * z) * (r * z)) = α * (α * (r * z)) * (r * z) := by group
      _ = α * ((r * z) * α) * (r * z) := by rw [hαy]
      _ = α * (r * z) * (α * (r * z)) := by group
  obtain ⟨-, hyz⟩ := eq_and_eq_of_mul_eq_mul D.A_inf_B (mul_mem hα hα) (one_mem _)
    (mul_mem (hZB hy) (hZB hy)) (one_mem _) hsq
  have hr2 : r * r = 1 := by
    have : r * r * (z * z) = r * z * (r * z) := by
      calc r * r * (z * z) = r * (r * z) * z := by group
        _ = r * (z * r) * z := by rw [hrz]
        _ = r * z * (r * z) := by group
    rwa [hz2, mul_one, hyz] at this
  obtain ⟨e₀⟩ := D.B₀_iso
  obtain ⟨V, hVB, hV2, hV4, hrV⟩ := exists_four_of_mulEquiv_dihedral D.one_le_n_sub_one e₀ hr hr2
  have hV : IsFourIn D.B₀ V := ⟨hVB, hV2, hV4⟩
  have hW := D.isFourIn_sConj₀ (D.isFourIn_repW (D.cls V + 1))
  have hE := D.isE64_of_four D.isFourIn_repU hV hW
  have htyp : D.typ (D.repU ⊔ (V ⊔ D.sConj (D.repW (D.cls V + 1)))) = (D.cls V, D.cls V + 1) := by
    obtain ⟨-, h₀, h₁⟩ := D.inf_of_four D.isFourIn_repU hV hW
    rw [typ, h₀, h₁, sConj_sConj, cls_repW]
  have hasym : (D.typ (D.repU ⊔ (V ⊔ D.sConj (D.repW (D.cls V + 1))))).1 ≠
      (D.typ (D.repU ⊔ (V ⊔ D.sConj (D.repW (D.cls V + 1))))).2 := by
    rw [htyp]
    generalize D.cls V = u
    revert u
    decide
  obtain ⟨h, hh, e⟩ := D.exists_conj_Frep01_of_asymm hm hE hasym
  refine ⟨h⁻¹, inv_mem hh, ?_⟩
  rw [← eq_map_conj_inv_of_map_conj_eq e]
  refine mul_mem (mem_sup_left ?_) (mul_mem (mem_sup_right (mem_sup_left hrV)) ?_)
  · rw [D.repU_eq_A hm]
    exact hα
  · exact (zpowers_le.2 (D.b₁_mem_E64 hE)) hz

theorem conj_of_mem_R₀ {E : Subgroup G} (hE : IsE64 T E) {d : G}
    (hd : d ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) {v : G} (hv : v ∈ E) :
    d * v * d⁻¹ = v ∨ d * v * d⁻¹ = v * D.b₀ := by
  obtain ⟨-, -, hB₀, -⟩ := D.E64_decomp hE
  obtain ⟨e⟩ := D.B₀_iso
  have hz := symm_zc_eq e D.two_le_n_sub_one D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy
  obtain ⟨u, hu, w₀, hw₀, w₁, hw₁, rfl⟩ := (D.mem_E64_iff hE).1 hv
  have hdB := (mem_inf.1 hd).1
  have e1 : d * (u * (w₀ * w₁)) * d⁻¹ = u * ((d * w₀ * d⁻¹) * w₁) := by
    have h1 : d * u = u * d := (D.A_comm_B u (mem_inf.1 hu).2 d (D.B₀_le_B hdB)).symm
    have h2 : d * w₁ = w₁ * d := D.B₀_comm_B₁ d hdB w₁ (mem_inf.1 hw₁).2
    calc d * (u * (w₀ * w₁)) * d⁻¹ = (d * u) * w₀ * w₁ * d⁻¹ := by group
      _ = u * d * w₀ * (d⁻¹ * (d * w₁)) * d⁻¹ := by rw [h1]; group
      _ = u * d * w₀ * (d⁻¹ * (w₁ * d)) * d⁻¹ := by rw [h2]
      _ = u * ((d * w₀ * d⁻¹) * w₁) := by group
  rw [e1]
  rcases conj_of_mem_inf_normalizer_four e D.one_le_n_sub_one hB₀ hd hw₀ with h | h
  · left
    rw [h]
  · right
    rw [h, hz]
    have h3 : D.b₀ * w₁ = w₁ * D.b₀ := D.B₀_comm_B₁ _ D.b₀_mem w₁ (mem_inf.1 hw₁).2
    calc u * (w₀ * D.b₀ * w₁) = u * (w₀ * (D.b₀ * w₁)) := by group
      _ = u * (w₀ * (w₁ * D.b₀)) := by rw [h3]
      _ = u * (w₀ * w₁) * D.b₀ := by group

theorem mem_R₁_of_mem_normalizer {E : Subgroup G} {β : G} (hβ : β ∈ D.B₁)
    (hβN : β ∈ normalizer (E : Set G)) :
    β ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G) := by
  refine mem_inf.2 ⟨hβ, mem_normalizer_of_map_conj_eq ?_⟩
  rw [map_conj_inf, map_conj_eq_self_of_mem_normalizer hβN,
    map_conj_eq_self_of_mem_normalizer (le_normalizer hβ)]

theorem swap_d (hm : m = 2) {E : Subgroup G} (hE : IsE64 T E) {d₀ d₁ τ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀E : d₀ ∉ E)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁E : d₁ ∉ E)
    (hτ : τ ∈ T ⊓ normalizer (E : Set G)) (hτE : τ ∉ (D.B₀ ⊔ D.B₁) ⊔ E) :
    τ * d₀ * τ⁻¹ * d₁⁻¹ ∈ E := by
  obtain ⟨hτT, hτN⟩ := mem_inf.1 hτ
  haveI := hE.finite
  have hτ1 : τ ∉ D.T₁ := by
    intro h1
    apply hτE
    have h2 : τ ∈ D.T₁ ⊓ normalizer (E : Set G) := mem_inf.2 ⟨h1, hτN⟩
    rw [D.normalizer_E64_inf_T₁ hE] at h2
    have hle : (D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G)) ⊔
        ((D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) ⊔
          (D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G))) ≤ (D.B₀ ⊔ D.B₁) ⊔ E := by
      refine sup_le (fun x hx => mem_sup_right (D.A_le_E64 hm hE (mem_inf.1 hx).1))
        (sup_le ?_ ?_)
      · exact (inf_le_left.trans le_sup_left).trans le_sup_left
      · exact (inf_le_left.trans le_sup_right).trans le_sup_left
    exact hle h2
  have hτb : τ * D.b₀ * τ⁻¹ = D.b₁ := by
    by_cases h0 : τ ∈ D.T₀
    · exact D.conj_b₀_of_not_mem_T₁ h0 hτ1
    · exact D.conj_b₀_of_mul_t_mem_T₁ (D.mul_t_mem_T₁_of_mem_normalizer hE hτT h0 hτN)
  have hd₀N := D.mem_normalizer_of_mem_R₀ hE hd₀
  have hd₀T : d₀ ∈ T := D.B_le_T (D.B₀_le_B (mem_inf.1 hd₀).1)
  have hyT : τ * d₀ * τ⁻¹ ∈ T := mul_mem (mul_mem hτT hd₀T) (inv_mem hτT)
  have hyN : τ * d₀ * τ⁻¹ ∈ normalizer (E : Set G) :=
    mul_mem (mul_mem hτN hd₀N) (inv_mem hτN)
  have htv : ∀ v ∈ E, τ * d₀ * τ⁻¹ * v * (τ * d₀ * τ⁻¹)⁻¹ = v ∨
      τ * d₀ * τ⁻¹ * v * (τ * d₀ * τ⁻¹)⁻¹ = v * D.b₁ := by
    intro v hv
    have hv' : τ⁻¹ * v * τ ∈ E := by
      have := (mem_normalizer_iff.1 (inv_mem hτN) v).1 hv
      rwa [inv_inv] at this
    have e : τ * d₀ * τ⁻¹ * v * (τ * d₀ * τ⁻¹)⁻¹ = τ * (d₀ * (τ⁻¹ * v * τ) * d₀⁻¹) * τ⁻¹ := by
      group
    rw [e]
    rcases D.conj_of_mem_R₀ hE hd₀ hv' with h | h <;> rw [h]
    · left
      group
    · right
      rw [← hτb]
      group
  have hmove : ∃ v ∈ E, τ * d₀ * τ⁻¹ * v * (τ * d₀ * τ⁻¹)⁻¹ ≠ v := by
    by_contra hno
    apply hd₀E
    rw [← D.centralizer_E64 hE]
    refine mem_inf.2 ⟨hd₀T, mem_centralizer_iff.2 fun v hv => ?_⟩
    have hτv : τ * v * τ⁻¹ ∈ E := (mem_normalizer_iff.1 hτN v).1 hv
    have h1 : τ * d₀ * τ⁻¹ * (τ * v * τ⁻¹) * (τ * d₀ * τ⁻¹)⁻¹ = τ * v * τ⁻¹ := by
      by_contra h
      exact hno ⟨_, hτv, h⟩
    have h2 : d₀ * v * d₀⁻¹ = v := by
      have h3 : τ * (d₀ * v * d₀⁻¹) * τ⁻¹ = τ * v * τ⁻¹ := by rw [← h1]; group
      have := congrArg (fun g => τ⁻¹ * g * τ) h3
      simpa [mul_assoc] using this
    calc v * d₀ = (d₀ * v * d₀⁻¹) * d₀ := by rw [h2]
      _ = d₀ * v := by group
  have ha1 : D.b₁ ≠ D.a := fun h => by
    have h2 : D.a ∈ D.A ⊓ D.B := mem_inf.2 ⟨D.a_mem, h ▸ D.b₁_mem_B⟩
    rw [D.A_inf_B, mem_bot] at h2
    exact D.a_ne_one h2
  rcases D.transvection_E64_center hE hyT hyN htv hmove with ⟨α, -, -, hc⟩ | ⟨β, -, -, hc⟩ |
    ⟨β, hβ, hyβ, -⟩
  · exact absurd hc ha1
  · exact absurd hc.symm D.b₀_ne_b₁
  ·
    have hβN : β ∈ normalizer (E : Set G) := by
      have h1 : β = (τ * d₀ * τ⁻¹ * β⁻¹)⁻¹ * (τ * d₀ * τ⁻¹) := by group
      rw [h1]
      exact mul_mem (inv_mem (le_normalizer hyβ)) hyN
    have hβR := D.mem_R₁_of_mem_normalizer hβ hβN
    have hβE : β ∉ E := by
      intro hβE
      apply hd₀E
      have h1 : τ * d₀ * τ⁻¹ ∈ E := by
        rw [show τ * d₀ * τ⁻¹ = (τ * d₀ * τ⁻¹ * β⁻¹) * β by group]
        exact mul_mem hyβ hβE
      have := (mem_normalizer_iff.1 (inv_mem hτN) _).1 h1
      rwa [show τ⁻¹ * (τ * d₀ * τ⁻¹) * τ⁻¹⁻¹ = d₀ by group] at this
    obtain ⟨-, -, -, hB₁⟩ := D.E64_decomp hE
    haveI : Finite ↥(D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G)) :=
      Nat.finite_of_card_ne_zero (by rw [D.card_R₁ hE]; norm_num)
    have hβd := mul_inv_mem_of_card_eq_two_mul (le_inf hB₁.1 le_normalizer)
      (by rw [D.card_R₁ hE, hB₁.2.2]) hβR hd₁ (fun h => hβE (mem_inf.1 h).1)
      (fun h => hd₁E (mem_inf.1 h).1)
    rw [show τ * d₀ * τ⁻¹ * d₁⁻¹ = (τ * d₀ * τ⁻¹ * β⁻¹) * (β * d₁⁻¹) by group]
    exact mul_mem hyβ (mem_inf.1 hβd).1

end FooteCore

end CFSG.CGT.Foote81L6

module

public import CFSG.CGT.T75P.Dich81
public import CFSG.CGT.T75P.Conn81

public section

namespace CFSG.CGT.T75P

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75Q

variable {G : Type} [Group G] {T T₁ : Subgroup G}

theorem Std81.final_step (s : Std81 T T₁) (hInd : SimpleCaseUpTo (Nat.card G))
    (h215 : Lemma215Stmt) (hL : ListWCIdentification) {Y : Subgroup G} (hY : GoodY T Y)
    (hD : DihHyp T Y)
    (hZU : ∀ z ∈ ugen T ⊓ Subgroup.centralizer (ugen T : Set G), z * z = 1 → z = 1)
    {x t τ : G} (hx : x ∈ classD T) (hxY : x ∉ Y)
    (ht : t ∈ Subgroup.centralizer (Y : Set G)) (hτ : τ ∈ Subgroup.centralizer (Y : Set G))
    (ht2 : t * t = 1) (hτ2 : τ * τ = 1) (ht1 : t ≠ 1) (hτ1 : τ ≠ 1) (htτ : t ≠ τ)
    (hcomm : t * τ = τ * t) : False := by
  classical
  have hfin : Finite G := s.finite
  have hWC := s.hc.hy.pair.wc
  obtain ⟨z₁, z₂, g₁, g₂, hz₁, hz₂, hz12, hg₁, hg₂, hd₁, hd₂, hαβ, hγx, hγd, hγe, hγt, hγτ,
    hz₁z₂, hγ2⟩ := hD.dihedral_data hx hxY ht hτ ht2 hτ2 ht1 hτ1 htτ hcomm
  have hHY : hSub T (normIn T₁ T) ≤ Y := (hSub_le_ugen s.hc (by norm_num)).trans hY.ugen_le
  have htC : t ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
    Subgroup.centralizer_le hHY ht
  have hτC : τ ∈ Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
    Subgroup.centralizer_le hHY hτ
  have htY : ∀ y ∈ Y, y * t = t * y := fun y hy => Subgroup.mem_centralizer_iff.1 ht y hy
  have hτY : ∀ y ∈ Y, y * τ = τ * y := fun y hy => Subgroup.mem_centralizer_iff.1 hτ y hy
  set γ : G := z₁ * z₂ with hγdef
  set d : G := g₁⁻¹ * x * g₁ with hddef
  set e : G := g₂⁻¹ * x * g₂ with heddef
  set α : G := g₁ * t * g₁⁻¹ with hαdef
  set β : G := g₂ * τ * g₂⁻¹ with hβdef
  have hdD : d ∈ classD T := classD_conj hx g₁
  have heD : e ∈ classD T := classD_conj hx g₂
  have hdY : d ∈ Y := hg₁ ▸ hd₁
  have heY : e ∈ Y := hg₂ ▸ hd₂
  have hxd : x = g₁ * d * g₁⁻¹ := by rw [hddef]; group
  have hxe : x = g₂ * e * g₂⁻¹ := by rw [heddef]; group
  have hαx : α * x = x * α := by
    have h1 : t * d = d * t := (htY d hdY).symm
    calc α * x = g₁ * (t * d) * g₁⁻¹ := by rw [hxd, hαdef]; group
      _ = g₁ * (d * t) * g₁⁻¹ := by rw [h1]
      _ = x * α := by rw [hxd, hαdef]; group
  have hβx : β * x = x * β := by
    have h1 : τ * e = e * τ := (hτY e heY).symm
    calc β * x = g₂ * (τ * e) * g₂⁻¹ := by rw [hxe, hβdef]; group
      _ = g₂ * (e * τ) * g₂⁻¹ := by rw [h1]
      _ = x * β := by rw [hxe, hβdef]; group
  obtain ⟨y₁, hy₁, t₁, ht₁, ht₁1, hdy⟩ := classD_inter_le_deltaOf hWC s.hN_gen s.h66'
    T_le_ugen s.exists_ne_one hY.ugen_le hdD hdY
  obtain ⟨y₂, hy₂, t₂, ht₂, ht₂1, hey⟩ := classD_inter_le_deltaOf hWC s.hN_gen s.h66'
    T_le_ugen s.exists_ne_one hY.ugen_le heD heY
  have hh : (g₁ * y₁)⁻¹ * x * (g₁ * y₁) = t₁ := by
    rw [hxd, hdy]; group
  have hhT : (g₁ * y₁)⁻¹ * x * (g₁ * y₁) ∈ T := by rw [hh]; exact ht₁
  have hh1 : (g₁ * y₁)⁻¹ * x * (g₁ * y₁) ≠ 1 := by rw [hh]; exact ht₁1
  have hαC : (g₁ * y₁)⁻¹ * α * (g₁ * y₁) ∈
      Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
    s.conjC_of_comm (g := g₁) (by rw [hαdef]; simpa [mul_assoc] using htC) hαx hhT hh1
  have hβC : (g₁ * y₁)⁻¹ * β * (g₁ * y₁) ∈
      Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) :=
    s.conjC_of_comm (g := g₂) (by rw [hβdef]; simpa [mul_assoc] using hτC) hβx hhT hh1
  have hγC : (g₁ * y₁)⁻¹ * γ * (g₁ * y₁) ∈
      Subgroup.centralizer (hSub T (normIn T₁ T) : Set G) := by
    have : (g₁ * y₁)⁻¹ * γ * (g₁ * y₁) =
        ((g₁ * y₁)⁻¹ * α * (g₁ * y₁)) * ((g₁ * y₁)⁻¹ * β * (g₁ * y₁)) := by
      rw [show γ = α * β from hαβ.symm]; group
    rw [this]
    exact Subgroup.mul_mem _ hαC hβC
  have hClγ : ClD T γ := s.clD_of_conj (g := g₁ * y₁) hγC (by group)
  have hWd := s.comm_conj_ugen hClγ hγd hdy ht₁ ht₁1
  have hWe := s.comm_conj_ugen hClγ hγe hey ht₂ ht₂1
  have hγY : γ ∈ Subgroup.centralizer (Y : Set G) := by
    set e' : G := y₁⁻¹ * e * y₁ with he'def
    by_cases hb : e' ∈ ugen T
    ·
      have hz₁τ : z₁ * τ = τ * z₁ := by
        have h1 : τ * (t * z₁) = (t * z₁) * τ := (hτY (t * z₁) hd₁).symm
        have h2 : t * (τ * z₁) = t * (z₁ * τ) := by
          calc t * (τ * z₁) = (t * τ) * z₁ := by group
            _ = (τ * t) * z₁ := by rw [hcomm]
            _ = τ * (t * z₁) := by group
            _ = (t * z₁) * τ := h1
            _ = t * (z₁ * τ) := by group
        exact (mul_left_cancel h2).symm
      have hde : d * e = (t * τ) * γ := by
        calc d * e = (t * z₁) * (τ * z₂) := by rw [hg₁, hg₂]
          _ = t * (z₁ * τ) * z₂ := by group
          _ = t * (τ * z₁) * z₂ := by rw [hz₁τ]
          _ = (t * τ) * (z₁ * z₂) := by group
      obtain ⟨z', hz'def⟩ : ∃ z', z' = t₁ * e' := ⟨_, rfl⟩
      have hde' : d * e = y₁ * z' * y₁⁻¹ := by
        rw [hz'def, hdy, he'def]; group
      have hz'U : z' ∈ ugen T := by
        rw [hz'def]; exact (ugen T).mul_mem (T_le_ugen ht₁) hb
      have hz'eq : z' = (t * τ) * (y₁⁻¹ * γ * y₁) := by
        have h1 : z' = y₁⁻¹ * (d * e) * y₁ := by rw [hde']; group
        rw [h1, hde]
        have ht' : y₁⁻¹ * t = t * y₁⁻¹ := htY _ (Y.inv_mem hy₁)
        have hτ' : y₁⁻¹ * τ = τ * y₁⁻¹ := hτY _ (Y.inv_mem hy₁)
        calc y₁⁻¹ * ((t * τ) * γ) * y₁ = (y₁⁻¹ * t) * τ * γ * y₁ := by group
          _ = (t * y₁⁻¹) * τ * γ * y₁ := by rw [ht']
          _ = t * (y₁⁻¹ * τ) * γ * y₁ := by group
          _ = t * (τ * y₁⁻¹) * γ * y₁ := by rw [hτ']
          _ = (t * τ) * (y₁⁻¹ * γ * y₁) := by group
      have hz'C : ∀ u ∈ ugen T, z' * u = u * z' := by
        intro u hu
        have hu' : u ∈ Y := hY.ugen_le hu
        have h1 := hWd u hu
        have h2 : (y₁⁻¹ * γ * y₁) * u = u * (y₁⁻¹ * γ * y₁) := by
          calc (y₁⁻¹ * γ * y₁) * u = y₁⁻¹ * (γ * (y₁ * u * y₁⁻¹)) * y₁ := by group
            _ = y₁⁻¹ * ((y₁ * u * y₁⁻¹) * γ) * y₁ := by rw [h1]
            _ = u * (y₁⁻¹ * γ * y₁) := by group
        have h3 : (t * τ) * u = u * (t * τ) := by
          calc (t * τ) * u = t * (τ * u) := by group
            _ = t * (u * τ) := by rw [(hτY u hu')]
            _ = (t * u) * τ := by group
            _ = (u * t) * τ := by rw [(htY u hu')]
            _ = u * (t * τ) := by group
        rw [hz'eq]
        calc (t * τ) * (y₁⁻¹ * γ * y₁) * u = (t * τ) * ((y₁⁻¹ * γ * y₁) * u) := by group
          _ = (t * τ) * (u * (y₁⁻¹ * γ * y₁)) := by rw [h2]
          _ = ((t * τ) * u) * (y₁⁻¹ * γ * y₁) := by group
          _ = (u * (t * τ)) * (y₁⁻¹ * γ * y₁) := by rw [h3]
          _ = u * ((t * τ) * (y₁⁻¹ * γ * y₁)) := by group
      have hz'cen : z' ∈ ugen T ⊓ Subgroup.centralizer (ugen T : Set G) :=
        ⟨hz'U, Subgroup.mem_centralizer_iff.2 fun u hu => (hz'C u hu).symm⟩
      have ht₁2 : t₁ * t₁ = 1 := mul_self_eq_one_of_mem_classD hWC.1 (mem_classD_of_mem ht₁ ht₁1)
      have he'D : e' ∈ classD T := classD_conj heD y₁
      have he'2 : e' * e' = 1 := mul_self_eq_one_of_mem_classD hWC.1 he'D
      have hz'2 : z' * z' = 1 := by
        have hc := hz'C t₁ (T_le_ugen ht₁)
        have h1 : t₁ * z' = e' := by rw [hz'def, ← mul_assoc, ht₁2, one_mul]
        have h2 : z' * t₁ = e' := by rw [hc, h1]
        calc z' * z' = z' * (t₁ * e') := by rw [← hz'def]
          _ = (z' * t₁) * e' := by group
          _ = e' * e' := by rw [h2]
          _ = 1 := he'2
      have hz'1 := hZU z' hz'cen hz'2
      have hde1 : d * e = 1 := by rw [hde', hz'1]; group
      have hγinv : γ = ((t * τ))⁻¹ := by
        rw [hde] at hde1
        exact eq_inv_of_mul_eq_one_right hde1
      rw [hγinv]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ ht hτ)
    ·
      set k : G := y₁⁻¹ * y₂ with hkdef
      have hkY : k ∈ Y := Y.mul_mem (Y.inv_mem hy₁) hy₂
      set W' : Subgroup G := ugen T ⊔ conjSubgroup k (ugen T) with hW'def
      have hconjY : conjSubgroup k (ugen T) ≤ Y := by
        intro w hw
        have hw' : k⁻¹ * w * k ∈ ugen T := mem_conjSubgroup.1 hw
        have : w = k * (k⁻¹ * w * k) * k⁻¹ := by group
        rw [this]
        exact Y.mul_mem (Y.mul_mem hkY (hY.ugen_le hw')) (Y.inv_mem hkY)
      have hW'Y : W' ≤ Y := sup_le hY.ugen_le hconjY
      have hgood : GoodY T W' := by
        refine ⟨fun h => hY.ne_top (top_le_iff.1 (h ▸ hW'Y)), le_sup_left, ?_⟩
        refine sup_le ?_ ?_
        · refine (Subgroup.closure_le _).2 ?_
          intro δ hδ
          exact Subgroup.subset_closure ⟨gammaD_subset_classD hδ,
            (le_sup_left : ugen T ≤ W') (gammaD_subset_ugen hδ)⟩
        · rw [conjSubgroup_ugen k, Subgroup.closure_le]
          rintro _ ⟨δ, hδ, rfl⟩
          refine Subgroup.subset_closure ⟨?_, ?_⟩
          · have := classD_conj (gammaD_subset_classD hδ) k⁻¹
            simpa using this
          · refine (le_sup_right : conjSubgroup k (ugen T) ≤ W') ?_
            apply mem_conjSubgroup.2
            have : k⁻¹ * (k * δ * k⁻¹) * k = δ := by group
            rw [this]
            exact gammaD_subset_ugen hδ
      rcases s.type_dich hInd h215 hL hgood with hW | hnine
      · exfalso
        apply hb
        have he'k : e' = k * t₂ * k⁻¹ := by rw [he'def, hey, hkdef]; group
        have : e' ∈ conjSubgroup k (ugen T) := by
          rw [he'k]
          apply mem_conjSubgroup.2
          have : k⁻¹ * (k * t₂ * k⁻¹) * k = t₂ := by group
          rw [this]
          exact T_le_ugen ht₂
        have h2 : e' ∈ W' := (le_sup_right : conjSubgroup k (ugen T) ≤ W') this
        rwa [hW] at h2
      · have hWY : W' = Y := s.eq_of_le_of_nine hInd h215 hL hgood hY hW'Y hnine
        have hle : W' ≤ Subgroup.centralizer ({y₁⁻¹ * γ * y₁} : Set G) := by
          refine sup_le ?_ ?_
          · intro u hu
            apply Subgroup.mem_centralizer_singleton_iff.2
            have h1 := hWd u hu
            calc u * (y₁⁻¹ * γ * y₁) = y₁⁻¹ * ((y₁ * u * y₁⁻¹) * γ) * y₁ := by group
              _ = y₁⁻¹ * (γ * (y₁ * u * y₁⁻¹)) * y₁ := by rw [← h1]
              _ = (y₁⁻¹ * γ * y₁) * u := by group
          · intro w hw
            apply Subgroup.mem_centralizer_singleton_iff.2
            have hu : k⁻¹ * w * k ∈ ugen T := mem_conjSubgroup.1 hw
            have h1 := hWe _ hu
            have hyw : y₂ * (k⁻¹ * w * k) * y₂⁻¹ = y₁ * w * y₁⁻¹ := by rw [hkdef]; group
            rw [hyw] at h1
            calc w * (y₁⁻¹ * γ * y₁) = y₁⁻¹ * ((y₁ * w * y₁⁻¹) * γ) * y₁ := by group
              _ = y₁⁻¹ * (γ * (y₁ * w * y₁⁻¹)) * y₁ := by rw [← h1]
              _ = (y₁⁻¹ * γ * y₁) * w := by group
        rw [hWY] at hle
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : y₁⁻¹ * y * y₁ ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hy₁) hy) hy₁
        have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hy')
        calc y * γ = y₁ * ((y₁⁻¹ * y * y₁) * (y₁⁻¹ * γ * y₁)) * y₁⁻¹ := by group
          _ = y₁ * ((y₁⁻¹ * γ * y₁) * (y₁⁻¹ * y * y₁)) * y₁⁻¹ := by rw [← h1]
          _ = γ * y := by group
  exact hxY (hD.F1inv γ hγY hz12 hγ2 x hx hγx)

end CFSG.CGT.T75P

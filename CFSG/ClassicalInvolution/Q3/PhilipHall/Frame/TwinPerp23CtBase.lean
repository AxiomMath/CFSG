module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23CtAut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23LcTwin
public import CFSG.ClassicalInvolution.Asc77.AscSixBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77

section Base

variable {Y : Type} [Group Y] [Finite Y] {K₀ K' : Subgroup Y} {t e : Y}

@[expose] def hZero (K₀ : Subgroup Y) (t : Y) : Subgroup Y :=
  Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.normalizer (K₀ : Set Y)

theorem mem_hZero_iff {c : Y} :
    c ∈ hZero K₀ t ↔ c ∈ Subgroup.centralizer ({t} : Set Y) ∧ conjSub c K₀ = K₀ := by
  unfold hZero
  rw [Subgroup.mem_inf, mem_normalizer_iff_conjSub_eq]

theorem conjSub_of_mem_hZero (hne : K' ≠ K₀)
    (hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      (conjSub c K₀ = K₀ ∨ conjSub c K₀ = K') ∧ (conjSub c K' = K₀ ∨ conjSub c K' = K'))
    {c : Y} (hc : c ∈ hZero K₀ t) : conjSub c K' = K' := by
  obtain ⟨hct, hK₀⟩ := mem_hZero_iff.mp hc
  rcases (hperm c hct).2 with h | h
  · exact absurd (conjSub_injective c (h.trans hK₀.symm)) hne
  · exact h

theorem mem_hZero_of {c : Y} (hct : c ∈ Subgroup.centralizer ({t} : Set Y)) (h : conjSub c K₀ = K₀) :
    c ∈ hZero K₀ t := mem_hZero_iff.mpr ⟨hct, h⟩

variable (hne : K' ≠ K₀)
  (hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
    (conjSub c K₀ = K₀ ∨ conjSub c K₀ = K') ∧ (conjSub c K' = K₀ ∨ conjSub c K' = K'))

include hne hperm

@[expose] noncomputable def actHom : ↥(hZero K₀ t) →* MulAut ↥K₀ × MulAut ↥K' :=
  (K₀.normalizerMonoidHom.comp
      (Subgroup.inclusion (fun c hc => (Subgroup.mem_inf.mp hc).2))).prod
    (K'.normalizerMonoidHom.comp
      (Subgroup.inclusion (fun c hc => mem_normalizer_iff_conjSub_eq.mpr
        (conjSub_of_mem_hZero hne hperm hc))))

theorem actHom_fst (c : ↥(hZero K₀ t)) (x : ↥K₀) :
    (((actHom hne hperm c).1 x : ↥K₀) : Y) = (c : Y) * (x : Y) * (c : Y)⁻¹ := rfl

theorem actHom_snd (c : ↥(hZero K₀ t)) (x : ↥K') :
    (((actHom hne hperm c).2 x : ↥K') : Y) = (c : Y) * (x : Y) * (c : Y)⁻¹ := rfl

end Base

theorem exists_sylow_subgroupOf {Y : Type} [Group Y] [Finite Y] {V P : Subgroup Y}
    (h : IsSylow2In V P) :
    ∃ Q : Sylow 2 ↥P, (Q : Subgroup ↥P) = V.subgroupOf P := by
  refine ⟨⟨V.subgroupOf P, h.2.1.comap_subtype, ?_⟩, rfl⟩
  intro Q hQ hle
  have hVQ : V ≤ Q.map P.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le h.1]
    exact Subgroup.map_mono hle
  have := h.2.2 (Q.map P.subtype) (Subgroup.map_subtype_le _) (hQ.map _) hVQ
  rw [← Subgroup.comap_map_eq_self_of_injective P.subtype_injective Q, this]
  rfl


section Decomp

variable {Y : Type} [Group Y] [Finite Y] {K₀ K' : Subgroup Y} {t e : Y}

theorem decomp_hZero (hz : IsUniqueInvolution K₀ t) (hne : K' ≠ K₀)
    (q₁ : Nonempty (↥K₀ ≃* QuaternionGroup 2)) (q₂ : Nonempty (↥K' ≃* QuaternionGroup 2))
    (hcomm : ∀ k ∈ K₀, ∀ k' ∈ K', k * k' = k' * k)
    (hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      (conjSub c K₀ = K₀ ∨ conjSub c K₀ = K') ∧ (conjSub c K' = K₀ ∨ conjSub c K' = K'))
    (hz' : IsUniqueInvolution K' t)
    (htrans : ∀ a ∈ K₀, ∀ x ∈ K₀, ∀ b ∈ K', ∀ y ∈ K', a * a = t → x * x = t → b * b = t →
      y * y = t → ∃ g ∈ Subgroup.centralizer ({t} : Set Y), g ∈ Subgroup.centralizer ({e} : Set Y) ∧
        g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y)
    (hsyl : ∃ P₁ : Subgroup Y, IsSylow2In P₁ (hZero K₀ t) ∧
      P₁ ≤ Subgroup.centralizer ({e} : Set Y)) :
    ∀ c ∈ hZero K₀ t, ∃ d ∈ Subgroup.centralizer ((K₀ ⊔ K' : Subgroup Y) : Set Y),
      c * d⁻¹ ∈ Subgroup.centralizer ({e} : Set Y) := by
  classical
  obtain ⟨e₁⟩ := q₁
  obtain ⟨e₂⟩ := q₂
  set J : Subgroup ↥(hZero K₀ t) := (Subgroup.centralizer ({e} : Set Y)).subgroupOf (hZero K₀ t)
    with hJ
  set z₁ : ↥K₀ := ⟨t, hz.mem⟩ with hz₁def
  set z₂ : ↥K' := ⟨t, hz'.mem⟩ with hz₂def
  have hinvol : ∀ {Q : Subgroup Y} (e' : ↥Q ≃* QuaternionGroup 2) (hzQ : IsUniqueInvolution Q t)
      (hzm : t ∈ Q), e' (⟨t, hzm⟩ : ↥Q) = QuaternionGroup.a 2 := by
    intro Q e' hzQ hzm
    apply q8_invol_eq
    · rw [← map_mul]
      have : (⟨t, hzm⟩ : ↥Q) * ⟨t, hzm⟩ = 1 := Subtype.ext hzQ.sq
      rw [this, map_one]
    · intro h
      have : (⟨t, hzm⟩ : ↥Q) = 1 := e'.injective (h.trans (map_one e').symm)
      exact hzQ.ne_one (congrArg Subtype.val this)
  have hz₁ : e₁ z₁ = QuaternionGroup.a 2 := hinvol e₁ hz hz.mem
  have hz₂ : e₂ z₂ = QuaternionGroup.a 2 := hinvol e₂ hz' hz'.mem
  have hodd : Odd J.index := by
    obtain ⟨P₁, hP₁, hP₁e⟩ := hsyl
    obtain ⟨Q, hQ⟩ := exists_sylow_subgroupOf hP₁
    have h2 := Sylow.not_dvd_index Q
    have h3 : (Q : Subgroup ↥(hZero K₀ t)) ≤ J := by
      intro x hx
      rw [hQ] at hx
      exact Subgroup.mem_subgroupOf.mpr (hP₁e (Subgroup.mem_subgroupOf.mp hx))
    have h4 : J.index ∣ (Q : Subgroup ↥(hZero K₀ t)).index := Subgroup.index_dvd_of_le h3
    have h5 : Odd (Q : Subgroup ↥(hZero K₀ t)).index := by
      rcases Nat.even_or_odd (Q : Subgroup ↥(hZero K₀ t)).index with h | h
      · exact absurd (even_iff_two_dvd.mp h) h2
      · exact h
    exact h5.of_dvd_nat h4
  have key := exists_eq_of_odd_index e₁ e₂ hz₁ hz₂ (actHom hne hperm) J
    (fun a a' b b' ha ha' hb hb' => by
      have ha1 : (a : Y) * a = t := congrArg Subtype.val ha
      have ha1' : (a' : Y) * a' = t := congrArg Subtype.val ha'
      have hb1 : (b : Y) * b = t := congrArg Subtype.val hb
      have hb1' : (b' : Y) * b' = t := congrArg Subtype.val hb'
      obtain ⟨g, hgt, hge, hga, hgb⟩ := htrans a a.2 a' a'.2 b b.2 b' b'.2 ha1 ha1' hb1 hb1'
      have hgn : conjSub g K₀ = K₀ := by
        rcases (hperm g hgt).1 with h | h
        · exact h
        · exfalso
          have hmem : (a' : Y) ∈ K' := by
            have : g * (a : Y) * g⁻¹ ∈ conjSub g K₀ := conj_mem_conjSub a.2
            rw [h, hga] at this
            exact this
          have hc2 : ∀ j ∈ K₀, (a' : Y) * j = j * (a' : Y) := fun j hj =>
            (hcomm j hj a' hmem).symm
          have hsq := Lc.center_sq_of_q8 ⟨e₁⟩ a'.2 hc2
          rw [ha1'] at hsq
          exact hz.ne_one hsq
      have hgH : g ∈ hZero K₀ t := mem_hZero_of hgt hgn
      refine ⟨⟨g, hgH⟩, Subgroup.mem_subgroupOf.mpr hge, ?_, ?_⟩
      · apply Subtype.ext
        rw [actHom_fst]
        exact hga
      · apply Subtype.ext
        rw [actHom_snd]
        exact hgb) hodd
  intro c hc
  obtain ⟨f, hfJ, hf⟩ := key ⟨c, hc⟩
  have hfe : (f : Y) ∈ Subgroup.centralizer ({e} : Set Y) := Subgroup.mem_subgroupOf.mp hfJ
  refine ⟨(f : Y)⁻¹ * c, ?_, ?_⟩
  · have hle : K₀ ⊔ K' ≤ Subgroup.centralizer ({(f : Y)⁻¹ * c} : Set Y) := by
      refine sup_le (fun k hk => ?_) (fun k hk => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := congrArg (fun m : MulAut ↥K₀ × MulAut ↥K' => ((m.1 ⟨k, hk⟩ : ↥K₀) : Y)) hf
        simp only [actHom_fst] at h1
        calc k * ((f : Y)⁻¹ * c) = (f : Y)⁻¹ * ((f : Y) * k * (f : Y)⁻¹) * c := by group
          _ = (f : Y)⁻¹ * ((c : Y) * k * (c : Y)⁻¹) * c := by rw [h1]
          _ = ((f : Y)⁻¹ * c) * k := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := congrArg (fun m : MulAut ↥K₀ × MulAut ↥K' => ((m.2 ⟨k, hk⟩ : ↥K') : Y)) hf
        simp only [actHom_snd] at h1
        calc k * ((f : Y)⁻¹ * c) = (f : Y)⁻¹ * ((f : Y) * k * (f : Y)⁻¹) * c := by group
          _ = (f : Y)⁻¹ * ((c : Y) * k * (c : Y)⁻¹) * c := by rw [h1]
          _ = ((f : Y)⁻¹ * c) * k := by group
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  · have : (c : Y) * ((f : Y)⁻¹ * c)⁻¹ = f := by group
    rw [this]
    exact hfe


theorem decomp_of_twinData (hz : IsUniqueInvolution K₀ t) (hz' : IsUniqueInvolution K' t)
    (hne : K' ≠ K₀)
    (q₁ : Nonempty (↥K₀ ≃* QuaternionGroup 2)) (q₂ : Nonempty (↥K' ≃* QuaternionGroup 2))
    (hcomm : ∀ k ∈ K₀, ∀ k' ∈ K', k * k' = k' * k)
    (hperm : ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      (conjSub c K₀ = K₀ ∨ conjSub c K₀ = K') ∧ (conjSub c K' = K₀ ∨ conjSub c K' = K'))
    (htrans : ∀ a ∈ K₀, ∀ x ∈ K₀, ∀ b ∈ K', ∀ y ∈ K', a * a = t → x * x = t → b * b = t →
      y * y = t → ∃ g ∈ Subgroup.centralizer ({t} : Set Y), g ∈ Subgroup.centralizer ({e} : Set Y) ∧
        g * a * g⁻¹ = x ∧ g * b * g⁻¹ = y)
    (hswap : ∃ σ ∈ Subgroup.centralizer ({t} : Set Y), σ ∈ Subgroup.centralizer ({e} : Set Y) ∧
      conjSub σ K₀ = K')
    (hsyl : ∃ P₁ : Subgroup Y, IsSylow2In P₁ (hZero K₀ t) ∧
      P₁ ≤ Subgroup.centralizer ({e} : Set Y)) :
    ∀ c ∈ Subgroup.centralizer ({t} : Set Y),
      ∃ d ∈ Subgroup.centralizer ((K₀ ⊔ K' : Subgroup Y) : Set Y),
        c * d⁻¹ ∈ Subgroup.centralizer ({e} : Set Y) := by
  intro c hct
  rcases (hperm c hct).1 with h | h
  · exact decomp_hZero hz hne q₁ q₂ hcomm hperm hz' htrans hsyl c (mem_hZero_of hct h)
  · obtain ⟨σ, hσt, hσe, hσ⟩ := hswap
    have hct' : σ⁻¹ * c ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hσt) hct
    have hn : conjSub (σ⁻¹ * c) K₀ = K₀ := by
      rw [conjSub_mul, h, ← hσ, conjSub_inv_conjSub]
    obtain ⟨d, hd, hde⟩ := decomp_hZero hz hne q₁ q₂ hcomm hperm hz' htrans hsyl (σ⁻¹ * c)
      (mem_hZero_of hct' hn)
    refine ⟨d, hd, ?_⟩
    have : c * d⁻¹ = σ * ((σ⁻¹ * c) * d⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hσe hde

end Decomp


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CtDec

module

public import CFSG.ClassicalInvolution.Q3.Sec13StarBasic
public import CFSG.ClassicalInvolution.Q3.Sec13StarAE5Model
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

section Ident

variable {P : Set (Subgroup G)}

omit [Finite G] in
private theorem aeIdent_map_comm {n : ℕ} (I : AEIdent P n) {L M : Subgroup G} (hL : L ∈ P)
    (hM : M ∈ P) (hc : Commutes L M) :
    ∀ x ∈ (L.subgroupOf (pSpan P)).map I.φ, ∀ y ∈ (M.subgroupOf (pSpan P)).map I.φ,
      x * y = y * x := by
  intro x hx y hy
  obtain ⟨l, hl, rfl⟩ := I.exists_of_mem_map hL hx
  obtain ⟨m, hm, rfl⟩ := I.exists_of_mem_map hM hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc l hl m hm)

omit [Finite G] in
private theorem conj_mem_pSpan {g : G} (hg : ∀ L ∈ P, conjSub g L ∈ P) {y : G}
    (hy : y ∈ pSpan P) : g * y * g⁻¹ ∈ pSpan P :=
  (pSpan_le (H := (pSpan P).comap (MulAut.conj g).toMonoidHom) fun L hL _ hl =>
    le_pSpan (hg L hL) (conj_mem_conjSub hl)) hy

omit [Finite G] in
private theorem exists_conj_of_aut (I : AEIdent P 5)
    (c : ↥(pSpan P) ≃* ↥(pSpan P))
    (hc : ∀ L ∈ P, ∃ L' ∈ P,
      (L.subgroupOf (pSpan P)).map c.toMonoidHom = L'.subgroupOf (pSpan P)) :
    ∃ x : AE.AEQ 5, ∀ y : ↥(pSpan P), I.φ (c y) = x * I.φ y * x⁻¹ := by
  have hZ : Subgroup.center ↥(pSpan P) ≤ I.φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    refine TL4.AE5.eq_one_of_comm_aeBar fun m hm => ?_
    rw [← I.range_eq] at hm
    obtain ⟨y, rfl⟩ := hm
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y).symm]
  obtain ⟨f, hf⟩ : ∃ f : ↥(pSpan P) →* ↥((AE.aeSub 5).map (AE.mkQ 5)),
      ∀ y, (f y : AE.AEQ 5) = I.φ y :=
    ⟨I.φ.codRestrict _ fun y => by rw [← I.range_eq]; exact ⟨y, rfl⟩, fun _ => rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨m, hm⟩
    rw [← I.range_eq] at hm
    obtain ⟨y, rfl⟩ := hm
    exact ⟨y, Subtype.ext (hf y)⟩
  have hfk : f.ker = Subgroup.center ↥(pSpan P) := by
    refine le_antisymm (fun y hy => I.ker_le ?_) fun y hy => ?_
    · rw [MonoidHom.mem_ker, ← hf, MonoidHom.mem_ker.mp hy]
      rfl
    · exact MonoidHom.mem_ker.mpr (Subtype.ext ((hf y).trans (MonoidHom.mem_ker.mp (hZ hy))))
  have hck : f.ker.map c.toMonoidHom = f.ker := by
    rw [hfk]
    exact Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (Subgroup.center ↥(pSpan P)).Characteristic) c
  obtain ⟨β, hβ⟩ : ∃ β : MulAut ↥((AE.aeSub 5).map (AE.mkQ 5)), ∀ y, β (f y) = f (c y) := by
    refine ⟨((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.trans
      (QuotientGroup.congr f.ker f.ker c hck)).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun y => ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f y) =
        (y : ↥(pSpan P) ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    rfl
  have hsub : ∀ H : Subgroup ↥(pSpan P),
      (H.map I.φ).subgroupOf ((AE.aeSub 5).map (AE.mkQ 5)) = H.map f := by
    intro H
    ext m
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hym⟩
      exact ⟨y, hy, Subtype.ext ((hf y).trans hym)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (hf y).symm⟩
  have hcomp : β.toMonoidHom.comp f = f.comp c.toMonoidHom := MonoidHom.ext hβ
  obtain ⟨x, hx⟩ := TL4.model117_proved 5 le_rfl (by norm_num) β fun α hα b => by
    obtain ⟨L, hL, hLe⟩ := I.label_surj α hα b
    obtain ⟨L', hL', hcL⟩ := hc L hL
    obtain ⟨α', hα', b', hL'e⟩ := I.label L' hL'
    refine ⟨α', hα', b', ?_⟩
    rw [← hLe, ← hL'e, hsub, hsub, Subgroup.map_map, hcomp, ← Subgroup.map_map, hcL]
  refine ⟨x, fun y => ?_⟩
  rw [← hf (c y), ← hβ, hx, hf]

end Ident

namespace StarHyp

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

theorem aeIdent_map_injective {P : Set (Subgroup G)} (hP : P ⊆ Ω) {n : ℕ} (I : AEIdent P n)
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P)
    (he : (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ) : L = L' := by
  by_contra hne
  have key : ∀ l' ∈ L', ∃ l ∈ L, ∃ c : G, (∀ y ∈ pSpan P, c * y = y * c) ∧ l' = l * c := by
    intro l' hl'
    have hx := I.mem_map hL' hl'
    rw [← he] at hx
    obtain ⟨l, hl, hle⟩ := I.exists_of_mem_map hL hx
    have hk : (⟨l, le_pSpan hL hl⟩ : ↥(pSpan P))⁻¹ * ⟨l', le_pSpan hL' hl'⟩ ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hle, inv_mul_cancel]
    refine ⟨l, hl, l⁻¹ * l', fun y hy => ?_, (mul_inv_cancel_left l l').symm⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp (I.ker_le hk) ⟨y, hy⟩)).symm
  have hN : L' ≤ Subgroup.normalizer (L : Set G) := by
    intro l' hl'
    obtain ⟨l, hl, c, hc, rfl⟩ := key l' hl'
    refine Subgroup.mul_mem _ (Subgroup.le_normalizer hl)
      (Subgroup.centralizer_le_normalizer _ ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun x hx => (hc x (le_pSpan hL hx)).symm
  have hL2 := h.thmD.two L (hP hL)
  have hL'2 := h.thmD.two L' (hP hL')
  obtain ⟨S, hS⟩ := (hL'2.to_sup_of_normal_right' hL2 hN).exists_le_sylow
  have hcomm : Commutes L L' := Q3CP.l67Gen G Ω h.thmD.hyp S L
    (TC.mem_RSet_of_isPGroup (hP hL) hL2) L' (TC.mem_RSet_of_isPGroup (hP hL') hL'2)
    (le_sup_right.trans hS) (le_sup_left.trans hS) hne
  obtain ⟨v, hv, hvc⟩ := Sec6Gen.exists_noncentral h.thmD.hyp (hP hL') le_rfl hL'2
    (by rw [h.thmD.card L' (hP hL')]; norm_num)
  refine hvc fun w hw => ?_
  obtain ⟨l, hl, c, hc, rfl⟩ := key w hw
  calc v * (l * c) = v * l * c := (mul_assoc _ _ _).symm
    _ = l * v * c := by rw [hcomm l hl v hv]
    _ = l * (v * c) := mul_assoc _ _ _
    _ = l * (c * v) := by rw [hc v (le_pSpan hL' hv)]
    _ = l * c * v := (mul_assoc _ _ _).symm

theorem false_of_aeIdent_three {P : Set (Subgroup G)} (hP : P ⊆ Ω) (I : AEIdent P 5)
    {L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ P) (h₂ : L₂ ∈ P) (h₃ : L₃ ∈ P) (h₁₂ : L₁ ≠ L₂)
    (h₁₃ : L₁ ≠ L₃) (h₂₃ : L₂ ≠ L₃) (c₁₂ : Commutes L₁ L₂) (c₁₃ : Commutes L₁ L₃)
    (c₂₃ : Commutes L₂ L₃) : False := by
  have hα : ∀ {M M' : Subgroup G} {β β' : Finset (Fin 5)} {e : β.card = 4} {e' : β'.card = 4}
      {b b' : Bool}, M ∈ P → M' ∈ P → M ≠ M' → Commutes M M' →
      (M.subgroupOf (pSpan P)).map I.φ = AE.memBar β e b →
      (M'.subgroupOf (pSpan P)).map I.φ = AE.memBar β' e' b' → β = β' := by
    intro M M' β β' e e' b b' hM hM' hMM' hc hb hb'
    refine AE5Star.eq_of_commutes e e' (b := b) (b' := b') ?_ ?_
    · rw [← hb, ← hb']
      exact fun he => hMM' (h.aeIdent_map_injective hP I hM hM' he)
    · rw [← hb, ← hb']
      exact aeIdent_map_comm I hM hM' hc
  obtain ⟨α₁, e₁, b₁, hb₁⟩ := I.label L₁ h₁
  obtain ⟨α₂, e₂, b₂, hb₂⟩ := I.label L₂ h₂
  obtain ⟨α₃, e₃, b₃, hb₃⟩ := I.label L₃ h₃
  have hα₂ := hα h₁ h₂ h₁₂ c₁₂ hb₁ hb₂
  have hα₃ := hα h₁ h₃ h₁₃ c₁₃ hb₁ hb₃
  subst hα₂ hα₃
  have key : ∀ {M M' : Subgroup G} {b : Bool}, M ∈ P → M' ∈ P → M ≠ M' →
      (M.subgroupOf (pSpan P)).map I.φ = AE.memBar α₁ e₁ b →
      (M'.subgroupOf (pSpan P)).map I.φ = AE.memBar α₁ e₁ b → False :=
    fun hM hM' hMM' hb hb' => hMM' (h.aeIdent_map_injective hP I hM hM' (hb.trans hb'.symm))
  cases b₁ <;> cases b₂ <;> cases b₃
  all_goals first
    | exact key h₁ h₂ h₁₂ hb₁ hb₂
    | exact key h₁ h₃ h₁₃ hb₁ hb₃
    | exact key h₂ h₃ h₂₃ hb₂ hb₃

theorem mem_dstarComp_of_aeIdent {a : G}
    (I : AEIdent (Generic.centMembers Ω a) 5) {K K' K₁ : Subgroup G}
    (hK : K ∈ Generic.centMembers Ω a) (hK' : K' ∈ Generic.centMembers Ω a) (hne : K ≠ K')
    (hKK' : Commutes K K') (hK₁ : K₁ ∈ Ω) {g : G} (hg : g ∈ K₁) (hga : g * a = a * g)
    (hg4 : orderOf g = 4) (hgK : ∀ k ∈ K, g * k = k * g) (hgK' : ∀ k ∈ K', g * k = k * g) :
    ∀ L ∈ Generic.centMembers Ω a, L ∈ dstarComp Ω K₁ := by
  have hPΩ : Generic.centMembers Ω a ⊆ Ω := fun L hL => (Generic.mem_centMembers.mp hL).1
  have hcP : ∀ u : G, u * a = a * u → ∀ L ∈ Generic.centMembers Ω a,
      conjSub u L ∈ Generic.centMembers Ω a := by
    intro u hu L hL
    obtain ⟨hLΩ, hLa⟩ := Generic.mem_centMembers.mp hL
    refine Generic.mem_centMembers.mpr ⟨h.thmD.hyp.conjInvariant u L hLΩ, fun y hy => ?_⟩
    rw [mem_conjSub_iff] at hy
    have hla : Commute (u⁻¹ * y * u) a := Subgroup.mem_centralizer_singleton_iff.mp (hLa hy)
    have hua : Commute u a := hu
    have hya : Commute (u * (u⁻¹ * y * u) * u⁻¹) a := (hua.mul_left hla).mul_left hua.inv_left
    rw [show u * (u⁻¹ * y * u) * u⁻¹ = y by group] at hya
    exact Subgroup.mem_centralizer_singleton_iff.mpr hya.eq
  have hgP := hcP g hga
  have hgP' := hcP g⁻¹ (show Commute g a from hga).inv_left.eq
  obtain ⟨c, hc₁, hc₂⟩ : ∃ c : ↥(pSpan (Generic.centMembers Ω a)) ≃*
      ↥(pSpan (Generic.centMembers Ω a)),
      (∀ y, (c y : G) = g * y * g⁻¹) ∧ ∀ y, (c.symm y : G) = g⁻¹ * y * g :=
    ⟨{ toFun := fun y => ⟨g * y * g⁻¹, conj_mem_pSpan hgP y.2⟩
       invFun := fun y => ⟨g⁻¹ * y * g, by
         have := conj_mem_pSpan hgP' y.2
         rwa [inv_inv] at this⟩
       left_inv := fun y => Subtype.ext (by simp [mul_assoc])
       right_inv := fun y => Subtype.ext (by simp [mul_assoc])
       map_mul' := fun y y' => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl, fun _ => rfl⟩
  have hcL : ∀ L ∈ Generic.centMembers Ω a,
      (L.subgroupOf (pSpan (Generic.centMembers Ω a))).map c.toMonoidHom =
        (conjSub g L).subgroupOf (pSpan (Generic.centMembers Ω a)) := by
    intro L hL
    ext y
    rw [Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, mem_conjSub_iff, ← hc₂]
    rfl
  obtain ⟨x, hx⟩ := exists_conj_of_aut I c fun L hL => ⟨conjSub g L, hgP L hL, hcL L hL⟩
  have htr : ∀ L ∈ Generic.centMembers Ω a,
      ((conjSub g L).subgroupOf (pSpan (Generic.centMembers Ω a))).map I.φ =
        ((L.subgroupOf (pSpan (Generic.centMembers Ω a))).map I.φ).map
          (MulAut.conj x).toMonoidHom := by
    intro L hL
    rw [← hcL L hL, Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext hx
  have hxfix : ∀ M ∈ Generic.centMembers Ω a, (∀ k ∈ M, g * k = k * g) →
      ∀ m ∈ (M.subgroupOf (pSpan (Generic.centMembers Ω a))).map I.φ, x * m = m * x := by
    intro M hM hgM m hm
    obtain ⟨k, hk, rfl⟩ := I.exists_of_mem_map hM hm
    have e : c ⟨k, le_pSpan hM hk⟩ = ⟨k, le_pSpan hM hk⟩ := by
      apply Subtype.ext
      rw [hc₁]
      show g * k * g⁻¹ = k
      rw [hgM k hk, mul_inv_cancel_right]
    have := hx ⟨k, le_pSpan hM hk⟩
    rw [e] at this
    exact mul_inv_eq_iff_eq_mul.mp this.symm
  obtain ⟨α, hα, b, hKl⟩ := I.label K hK
  obtain ⟨α', hα', b', hK'l⟩ := I.label K' hK'
  have hd : AE.memBar α hα b ≠ AE.memBar α' hα' b' := by
    rw [← hKl, ← hK'l]
    exact fun he => hne (h.aeIdent_map_injective hPΩ I hK hK' he)
  have hcm : ∀ y ∈ AE.memBar α hα b, ∀ z ∈ AE.memBar α' hα' b', y * z = z * y := by
    rw [← hKl, ← hK'l]
    exact aeIdent_map_comm I hK hK' hKK'
  have hαα := AE5Star.eq_of_commutes hα hα' hd hcm
  subst hαα
  have hxK := hxfix K hK hgK
  have hxK' := hxfix K' hK' hgK'
  rw [hKl] at hxK
  rw [hK'l] at hxK'
  have hTF : (∀ m ∈ AE.memBar α hα true, x * m = m * x) ∧
      ∀ m ∈ AE.memBar α hα false, x * m = m * x := by
    cases b <;> cases b'
    · exact absurd rfl hd
    · exact ⟨hxK', hxK⟩
    · exact ⟨hxK, hxK'⟩
    · exact absurd rfl hd
  have hsq : ∀ (β : Finset (Fin 5)) (hβ : β.card = 4) (d : Bool),
      ((AE.memBar β hβ d).map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        AE.memBar β hβ d := by
    intro β hβ d
    have hinj := Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective
    have hTF' := AE.memBar_true_ne_false (le_refl 5) β hβ
    have key := AE5Star.conj_memBar_of_comm hα hTF.1 hTF.2 β hβ
    rcases key true with ht | ht <;> rcases key false with hf | hf
    · exact absurd (hinj (ht.trans hf.symm)) hTF'
    · cases d
      · rw [hf, hf]
      · rw [ht, ht]
    · cases d
      · rw [hf, ht]
      · rw [ht, hf]
    · exact absurd (hinj (ht.trans hf.symm)) hTF'
  have hgg : ∀ L ∈ Generic.centMembers Ω a, conjSub (g * g) L = L := by
    intro L hL
    obtain ⟨β, hβ, d, hLl⟩ := I.label L hL
    have hmem : conjSub (g * g) L ∈ Generic.centMembers Ω a := by
      rw [conjSub_mul]
      exact hgP _ (hgP L hL)
    refine h.aeIdent_map_injective hPΩ I hmem hL ?_
    rw [conjSub_mul, htr _ (hgP L hL), htr L hL, hLl, hsq]
  obtain ⟨z, hz⟩ := (h.thmD.hyp.omega1 K₁ hK₁).1
  have h4 : g ^ 4 = 1 := hg4 ▸ pow_orderOf_eq_one g
  have hz' : g * g = z := by
    refine (hz.unique (g * g) (K₁.mul_mem hg hg) ?_).resolve_left fun h1 => ?_
    · rw [← h4, pow_succ, pow_succ, pow_succ, pow_one]
      simp only [mul_assoc]
    · have h2 := orderOf_dvd_of_pow_eq_one ((pow_two g).trans h1)
      rw [hg4] at h2
      norm_num at h2
  have hv : IsUniqueInvolution K₁ (g * g) := by
    rw [hz']
    exact hz
  intro L hL
  exact h.mem_dstarComp_of_normalizes (hPΩ hL) hK₁ hv
    (mem_normalizer_iff_conjSub_eq.mpr (hgg L hL))

end StarHyp

end CFSG.ClassicalInvolution.Q3.Sec13

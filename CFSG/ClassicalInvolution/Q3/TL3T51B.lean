module

public import CFSG.ClassicalInvolution.Q3.TL3T51A

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

section General

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal

variable {n : ℕ}

private theorem exists_perm_of_memberPerm_of_conj (hn : 5 ≤ n)
    {β : MulAut ↥(TL4.aeModel n)} (hβ : TL4.Mdl117.MemberPerm β)
    (hex : ∃ σ : Equiv.Perm (Fin n), MulAut.conjNormal σ = autAlt hn β) :
    ∃ σ : Equiv.Perm (Fin n),
      (∀ x : ↥(TL4.aeModel n), permQ n ((β x : ↥(TL4.aeModel n)) : AEQ n) =
        σ * permQ n (x : AEQ n) * σ⁻¹) ∧
      ∀ (α : Finset (Fin n)) (h : α.card = 4),
        ((β (TL4.Mdl117.zBarG α h) : ↥(TL4.aeModel n)) : AEQ n) =
          zBar (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact h) := by
  obtain ⟨σ, hσ⟩ := hex
  have hperm : ∀ x : ↥(TL4.aeModel n), permQ n ((β x : ↥(TL4.aeModel n)) : AEQ n) =
      σ * permQ n (x : AEQ n) * σ⁻¹ := by
    intro x
    rw [permQ_aut_apply hn β x, ← autAlt_apply hn β, ← hσ, MulAut.conjNormal_apply]
  refine ⟨σ, hperm, fun α h => ?_⟩
  obtain ⟨α', h', b', he⟩ := hβ α h true
  have hα' : α' = α.map σ.toEmbedding := by
    refine eq_of_kleinOn_eq h' (by rw [Finset.card_map]; exact h) ?_
    rw [kleinOn_map, ← map_permQ_memBar α h true, ← map_permQ_memBar α' h' b']
    ext τ
    rw [Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨g, hg, rfl⟩ := TL4.Mdl117.exists_of_map_eq he hy
      refine ⟨permQ n (g : AEQ n), Subgroup.mem_map_of_mem _ hg, ?_⟩
      rw [hperm g]
      rfl
    · rintro ⟨_, hκ, rfl⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hκ
      have hxG : x ∈ TL4.aeModel n := memBar_le_aeModel α h true hx
      refine ⟨((β ⟨x, hxG⟩ : ↥(TL4.aeModel n)) : AEQ n),
        TL4.Mdl117.mem_of_map_eq he (g := ⟨x, hxG⟩) hx, ?_⟩
      rw [hperm ⟨x, hxG⟩]
      rfl
  subst hα'
  exact TL4.Mdl117.beta_zBar_of_map_eq hn he

private theorem exists_vec_of_permQ_eq {β₁ : MulAut ↥(TL4.Mdl117.GBar n)}
    (hβ₁ : ∀ g : ↥(TL4.Mdl117.GBar n),
      permQ n ((β₁ g : ↥(TL4.Mdl117.GBar n)) : AEQ n) = permQ n (g : AEQ n))
    (g : ↥(TL4.Mdl117.GBar n)) :
    ∃ v : Fin n → ZMod 2, ∑ i, v i = 0 ∧
      ((β₁ g : ↥(TL4.Mdl117.GBar n)) : AEQ n) = (g : AEQ n) * mkQ n (ofVec v) := by
  have hyG : (g : AEQ n)⁻¹ * ((β₁ g : ↥(TL4.Mdl117.GBar n)) : AEQ n) ∈ TL4.Mdl117.GBar n :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ g.2) (β₁ g).2
  have hp : permQ n ((g : AEQ n)⁻¹ * ((β₁ g : ↥(TL4.Mdl117.GBar n)) : AEQ n)) = 1 := by
    rw [map_mul, map_inv, hβ₁, inv_mul_cancel]
  obtain ⟨v, hv, hyv⟩ := TL4.Mdl117.exists_vec_of_permQ_eq_one hyG hp
  refine ⟨v, hv, ?_⟩
  rw [← hyv, mul_inv_cancel_left]

private theorem model117At_of_conj (hn5 : 5 ≤ n)
    (hAut : ∀ β : MulAut ↥(TL4.aeModel n), TL4.Mdl117.MemberPerm β →
      ∃ σ : Equiv.Perm (Fin n), MulAut.conjNormal σ = autAlt hn5 β) : Model117At n := by
  intro β hβ
  obtain ⟨σ, hperm, hσ⟩ := exists_perm_of_memberPerm_of_conj hn5 hβ (hAut β hβ)
  have hfix := TL4.Mdl117.exists_beta1 hσ
  set β₁ := (MulAut.conjNormal (mkQ n (ofPerm σ)))⁻¹ * β with hβ₁def
  have hβ₁perm : ∀ g : ↥(TL4.Mdl117.GBar n),
      permQ n ((β₁ g : ↥(TL4.Mdl117.GBar n)) : AEQ n) = permQ n (g : AEQ n) := by
    intro g
    rw [hβ₁def, MulAut.mul_apply, ← map_inv, MulAut.conjNormal_apply]
    have hc : permQ n (mkQ n (ofPerm σ)) = σ := rfl
    simp only [map_mul, map_inv, hc, hperm g]
    group
  have hgen : ∀ k : CarmichaelIndex n, ∃ w : Fin n → ZMod 2, TL4.Mdl117.NormAt k w ∧
      ((β₁ (TL4.Mdl117.altHom n (carmichaelCycle k)) : ↥(TL4.Mdl117.GBar n)) : AEQ n) =
        mkQ n (ofPerm (carmichaelPerm k) * ofVec w) := by
    intro k
    obtain ⟨v, -, e⟩ := exists_vec_of_permQ_eq hβ₁perm (TL4.Mdl117.altHom n (carmichaelCycle k))
    rw [TL4.Mdl117.coe_altHom, ← map_mul] at e
    change _ = mkQ n (ofPerm (carmichaelPerm k) * ofVec v) at e
    have h3 : mkQ n ((ofPerm (carmichaelPerm k) * ofVec v) ^ 3) = 1 := by
      rw [map_pow, ← e, ← Subgroup.coe_pow, ← map_pow, ← map_pow, carmichaelCycle_pow_three,
        map_one, map_one, Subgroup.coe_one]
    obtain ⟨w', hw', he⟩ := TL4.Mdl117.exists_norm_of_cube k h3
    exact ⟨w', hw', e.trans he.symm⟩
  choose w hw he using hgen
  have hpair : ∀ k l : CarmichaelIndex n, k ≠ l →
      w k (TL4.Mdl117.carmZero k) = w l (TL4.Mdl117.carmZero l) := by
    intro k l hkl
    refine TL4.Mdl117.eq_at_zero_of_sq hn5 hkl (hw k) (hw l) ?_
    rw [map_pow, map_mul, ← he k, ← he l, ← Subgroup.coe_mul, ← map_mul, ← Subgroup.coe_pow,
      ← map_pow, ← map_mul, ← map_pow, carmichaelCycle_mul_sq k l hkl, map_one, map_one,
      Subgroup.coe_one]
  obtain ⟨k₀⟩ : Nonempty (CarmichaelIndex n) := ⟨⟨⟨2, by omega⟩, le_rfl⟩⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = w k₀ (TL4.Mdl117.carmZero k₀) := ⟨_, rfl⟩
  have hc : ∀ k, w k (TL4.Mdl117.carmZero k) = c := by
    intro k
    rw [hcdef]
    by_cases hk : k = k₀
    · rw [hk]
    · exact hpair k k₀ hk
  have hu : ∀ k : CarmichaelIndex n, β₁ (TL4.Mdl117.altHom n (carmichaelCycle k)) =
      MulAut.conjNormal (mkQ n (ofVec (TL4.Mdl117.uVec c w)))
        (TL4.Mdl117.altHom n (carmichaelCycle k)) := by
    intro k
    apply Subtype.ext
    rw [he k, MulAut.conjNormal_apply, TL4.Mdl117.coe_altHom, ← map_inv, ← map_mul, ← map_mul]
    show _ = mkQ n (ofVec (TL4.Mdl117.uVec c w) * ofPerm (carmichaelPerm k) *
      (ofVec (TL4.Mdl117.uVec c w))⁻¹)
    rw [TL4.Mdl117.conj_uVec hw hc k]
  have heq : β₁ = MulAut.conjNormal (mkQ n (ofVec (TL4.Mdl117.uVec c w))) := by
    refine TL4.Mdl117.eq_of_agree_carmichael (by omega) hu fun v hv g hg => ?_
    apply Subtype.ext
    rw [TL4.Mdl117.fix_vec_of_fix_zBar_gen hn5 hfix hv g hg, MulAut.conjNormal_apply, hg,
      ← map_inv (mkQ n), ← map_mul (mkQ n), ← map_mul (mkQ n), TL4.Mdl117.conj_ofVec_ofVec]
  have hβe : β = MulAut.conjNormal (mkQ n (ofPerm σ)) *
      MulAut.conjNormal (mkQ n (ofVec (TL4.Mdl117.uVec c w))) := by
    rw [← heq, hβ₁def, mul_inv_cancel_left]
  refine ⟨mkQ n (ofPerm σ) * mkQ n (ofVec (TL4.Mdl117.uVec c w)), fun g => ?_⟩
  rw [hβe, MulAut.mul_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  group

private theorem exists_kleinOn_iff (hn : 5 ≤ n) {β : MulAut ↥(TL4.aeModel n)}
    (hβ : TL4.Mdl117.MemberPerm β) (α : Finset (Fin n)) (h : α.card = 4) :
    ∃ (α' : Finset (Fin n)) (_ : α'.card = 4), ∀ τ : alternatingGroup (Fin n),
      ((τ : Equiv.Perm (Fin n)) ∈ kleinOn α ↔
        ((autAlt hn β τ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) ∈ kleinOn α') := by
  obtain ⟨α', h', b', he⟩ := hβ α h true
  refine ⟨α', h', fun τ => ?_⟩
  constructor
  · intro hτ
    rw [← map_permQ_memBar α h true] at hτ
    obtain ⟨y, hy, hyτ⟩ := Subgroup.mem_map.mp hτ
    have hyG : y ∈ TL4.aeModel n := memBar_le_aeModel α h true hy
    have h1 := TL4.Mdl117.mem_of_map_eq he (g := ⟨y, hyG⟩) hy
    have h2 := permQ_aut_apply hn β ⟨y, hyG⟩
    have hτy : (⟨permQ n y, permQ_mem_alt hyG⟩ : alternatingGroup (Fin n)) = τ :=
      Subtype.ext hyτ
    have h5 : ((autAlt hn β τ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) =
        permQ n ((β ⟨y, hyG⟩ : ↥(TL4.aeModel n)) : AEQ n) := by
      rw [h2, autAlt_apply hn β τ, ← hτy]
    rw [h5, ← map_permQ_memBar α' h' b']
    exact Subgroup.mem_map_of_mem _ h1
  · intro hτ
    rw [autAlt_apply hn β τ, ← map_permQ_memBar α' h' b'] at hτ
    obtain ⟨z, hz, hzτ⟩ := Subgroup.mem_map.mp hτ
    obtain ⟨g, hg, hgz⟩ := TL4.Mdl117.exists_of_map_eq he hz
    have h2 := permQ_aut_apply hn β g
    have h3 : autAltHom β ⟨permQ n (g : AEQ n), permQ_mem_alt g.2⟩ = autAltHom β τ := by
      apply Subtype.ext
      rw [← h2, hgz]
      exact hzτ
    have h4 := autAltHom_injective hn β h3
    rw [← map_permQ_memBar α h true, ← h4]
    exact Subgroup.mem_map_of_mem _ hg

private theorem mul_mem_kleinOn_of_stable {A : Finset (Fin n)} {g : Equiv.Perm (Fin n)}
    (hg : ∀ x, x ∈ A ↔ g x ∈ A) {τ : Equiv.Perm (Fin n)} (hτ : τ ∈ kleinOn A) :
    g * τ * g⁻¹ ∈ kleinOn A := by
  have hmap : A.map g.toEmbedding = A := by
    ext x
    rw [Finset.mem_map_equiv, hg (g.symm x), Equiv.apply_symm_apply]
  have h := kleinOn_map g A
  rw [hmap] at h
  rw [h]
  exact ⟨τ, hτ, rfl⟩

private theorem stable_of_forall_mul_mem_kleinOn {A : Finset (Fin n)} (hA : A.card = 4)
    {g : Equiv.Perm (Fin n)} (hg : ∀ τ ∈ kleinOn A, g * τ * g⁻¹ ∈ kleinOn A) :
    ∀ x, x ∈ A ↔ g x ∈ A := by
  have h1 : kleinOn A ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, natCard_kleinOn hA]
    norm_num
  obtain ⟨⟨τ, hτ⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h1
  have hτ1 : τ ≠ 1 := fun h' => hne (Subtype.ext h')
  have hτ' := hg τ hτ
  have hτ'1 : g * τ * g⁻¹ ≠ 1 := by
    intro h
    apply hτ1
    calc τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  intro x
  rw [← moves_iff_of_mem_kleinOn hτ hτ1 x, ← moves_iff_of_mem_kleinOn hτ' hτ'1 (g x)]
  have e : (g * τ * g⁻¹) (g x) = g (τ x) := by simp [Equiv.Perm.mul_apply]
  rw [e, Ne, Ne, g.apply_eq_iff_eq]

end General

section Six

open Equiv Equiv.Perm
open CFSG.ClassicalInvolution.Q3.AE
open CFSG.ComponentClassification.CatalogueSchreierAlternating
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix

private theorem exists_stable_of_support_card_three : ∀ g : Perm (Fin 6), g.support.card = 3 →
    ∃ α : Finset (Fin 6), α.card = 4 ∧ ∀ x, x ∈ α ↔ g x ∈ α := by
  decide +kernel

private theorem support_card_three_of_stable : ∀ g : Perm (Fin 6), g ^ 3 = 1 → g ≠ 1 →
    ∀ α : Finset (Fin 6), α.card = 4 → (∀ x, x ∈ α ↔ g x ∈ α) → g.support.card = 3 := by
  decide +kernel

private theorem card_threeCycles_six :
    Nat.card {a : alternatingGroup (Fin 6) // (a : Perm (Fin 6)).support.card = 3} = 40 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

private theorem x_support : ((x : alternatingGroup (Fin 6)) : Perm (Fin 6)).support.card = 3 := by
  decide +kernel

private abbrev TPairs : Type :=
  {p : alternatingGroup (Fin 6) × alternatingGroup (Fin 6) //
    (p.1 : Perm (Fin 6)).support.card = 3 ∧ SecondImage p.1 p.2}

private theorem firstImage_of_support_card_three {a : alternatingGroup (Fin 6)}
    (ha : (a : Perm (Fin 6)).support.card = 3) : FirstImage a := by
  rw [firstImage_iff_order, ← Subgroup.orderOf_coe]
  exact (card_support_eq_three_iff.mp ha).orderOf

private theorem card_tPairs : Nat.card TPairs = 720 := by
  let e : TPairs ≃ (a : {a : alternatingGroup (Fin 6) // (a : Perm (Fin 6)).support.card = 3}) ×
      {b : alternatingGroup (Fin 6) // SecondImage a.1 b} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩⟩
      invFun := fun q => ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  have h18 : ∀ a : {a : alternatingGroup (Fin 6) // (a : Perm (Fin 6)).support.card = 3},
      Nat.card {b : alternatingGroup (Fin 6) // SecondImage a.1 b} = 18 :=
    fun a => secondImage_card a.1 (firstImage_of_support_card_three a.2)
  simp only [h18, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, card_threeCycles_six]

private theorem secondImage_map (ψ : MulAut (alternatingGroup (Fin 6)))
    {a b : alternatingGroup (Fin 6)} (h : SecondImage a b) : SecondImage (ψ a) (ψ b) := by
  rw [secondImage_iff_orders] at h ⊢
  simpa only [← map_mul, ← map_inv, MulEquiv.orderOf_eq] using h

private theorem secondImage_xy : SecondImage x y :=
  (secondImage_iff_orders x y).mpr ⟨y_order, xy_order, commutator_order⟩

private theorem support_card_conjNormal (σ : Perm (Fin 6)) {a : alternatingGroup (Fin 6)}
    (h : (a : Perm (Fin 6)).support.card = 3) :
    ((MulAut.conjNormal σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)).support.card = 3 := by
  rw [MulAut.conjNormal_apply, support_conj, Finset.card_map]
  exact h

private theorem exists_conjNormal_of_support_card_three (φ : MulAut (alternatingGroup (Fin 6)))
    (h3 : ((φ x : alternatingGroup (Fin 6)) : Perm (Fin 6)).support.card = 3) :
    ∃ σ : Perm (Fin 6), MulAut.conjNormal σ = φ := by
  let f : Perm (Fin 6) → TPairs := fun σ =>
    ⟨(MulAut.conjNormal σ x, MulAut.conjNormal σ y),
      support_card_conjNormal σ x_support, secondImage_map _ secondImage_xy⟩
  have hf : Function.Injective f := by
    intro σ τ h
    have hx : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 6))) x =
        MulAut.conjNormal τ x := congrArg (fun p => p.1.1) h
    have hy : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 6))) y =
        MulAut.conjNormal τ y := congrArg (fun p => p.1.2) h
    have : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 6))) = MulAut.conjNormal τ :=
      imagePairEvaluation_injective x y generating_pair (Subtype.ext (Prod.ext hx hy))
    exact CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6
      (by norm_num) this
  have hc : Nat.card TPairs ≤ Nat.card (Perm (Fin 6)) := by
    rw [card_tPairs, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  obtain ⟨σ, hσ⟩ := (hf.bijective_of_nat_card_le hc).2
    ⟨(φ x, φ y), h3, secondImage_map φ secondImage_xy⟩
  refine ⟨σ, ?_⟩
  have hx : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 6))) x = φ x :=
    congrArg (fun p => p.1.1) hσ
  have hy : (MulAut.conjNormal σ : MulAut (alternatingGroup (Fin 6))) y = φ y :=
    congrArg (fun p => p.1.2) hσ
  exact imagePairEvaluation_injective x y generating_pair (Subtype.ext (Prod.ext hx hy))

private theorem support_card_autAlt_x {β : MulAut ↥(TL4.aeModel 6)}
    (hβ : TL4.Mdl117.MemberPerm β) :
    ((autAlt (by norm_num : 5 ≤ 6) β x : alternatingGroup (Fin 6)) : Perm (Fin 6)).support.card =
      3 := by
  set φ := autAlt (by norm_num : 5 ≤ 6) β
  obtain ⟨α, hα, hxα⟩ := exists_stable_of_support_card_three _ x_support
  obtain ⟨α', hα', hK⟩ := exists_kleinOn_iff (by norm_num : 5 ≤ 6) hβ α hα
  have hnorm : ∀ τ' ∈ kleinOn α', ((φ x : alternatingGroup (Fin 6)) : Perm (Fin 6)) * τ' *
      ((φ x : alternatingGroup (Fin 6)) : Perm (Fin 6))⁻¹ ∈ kleinOn α' := by
    intro τ' hτ'
    let τ'' : alternatingGroup (Fin 6) :=
      ⟨τ', Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_kleinOn hτ')⟩
    have hφτ : φ (φ.symm τ'') = τ'' := φ.apply_symm_apply τ''
    have hτα : ((φ.symm τ'' : alternatingGroup (Fin 6)) : Perm (Fin 6)) ∈ kleinOn α :=
      (hK _).mpr (by rw [hφτ]; exact hτ')
    have h1 := mul_mem_kleinOn_of_stable hxα hτα
    have h2 := (hK (x * φ.symm τ'' * x⁻¹)).mp h1
    rw [map_mul, map_mul, map_inv, hφτ] at h2
    exact h2
  have hst := stable_of_forall_mul_mem_kleinOn hα' hnorm
  have hord : orderOf ((φ x : alternatingGroup (Fin 6)) : Perm (Fin 6)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact x_order
  refine support_card_three_of_stable _ ?_ ?_ α' hα' hst
  · rw [← hord]
    exact pow_orderOf_eq_one _
  · intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)

end Six

theorem model117At_six : Model117At 6 :=
  model117At_of_conj (by norm_num) fun _ hβ =>
    exists_conjNormal_of_support_card_three _ (support_card_autAlt_x hβ)

theorem model117At_of_five_le {n : ℕ} (hn : 5 ≤ n) : Model117At n := by
  rcases eq_or_ne n 6 with rfl | h6
  · exact model117At_six
  · exact model117At_of_ne_six hn h6

end CFSG.ClassicalInvolution.Q3.TC.Thin

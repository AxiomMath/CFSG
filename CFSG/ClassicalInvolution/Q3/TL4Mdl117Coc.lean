module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Vec
public import CFSG.ClassicalInvolution.Q3.AE.PermElt

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Mdl117

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr Certificates.AE117

variable {n : ℕ}

@[expose] def ofPermHom (n : ℕ) : Equiv.Perm (Fin n) →* Wr n where
  toFun := ofPerm
  map_one' := ofPerm_one
  map_mul' σ τ := (ofPerm_mul σ τ).symm

theorem ofPerm_mem_GBar {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    mkQ n (ofPerm σ) ∈ GBar n :=
  ⟨ofPerm σ, ⟨by simp [wsum, ofPerm], Equiv.Perm.mem_alternatingGroup.mp hσ⟩, rfl⟩

@[expose] def permG (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ alternatingGroup (Fin n)) : ↥(GBar n) :=
  ⟨mkQ n (ofPerm σ), ofPerm_mem_GBar hσ⟩

theorem coe_permG (σ : Equiv.Perm (Fin n)) (hσ : σ ∈ alternatingGroup (Fin n)) :
    ((permG σ hσ : ↥(GBar n)) : AEQ n) = mkQ n (ofPerm σ) := rfl

theorem permG_congr {σ τ : Equiv.Perm (Fin n)} (h : σ = τ) (hσ : σ ∈ alternatingGroup (Fin n))
    (hτ : τ ∈ alternatingGroup (Fin n)) : permG σ hσ = permG τ hτ := by
  subst h
  rfl

theorem ofVec_mul_ofPerm (w : Wr n) : ofVec w.vec * ofPerm w.perm = w :=
  Wr.ext (funext fun i => by show w.vec i + 0 = w.vec i; rw [add_zero])
    (by show 1 * w.perm = w.perm; rw [one_mul])

theorem conj_ofVec_ofVec (u v : Fin n → ZMod 2) : ofVec u * ofVec v * (ofVec u)⁻¹ = ofVec v := by
  rw [conj_ofVec]
  rfl

theorem coe_evalG (L : List ↥(GBar n)) (w : List ℕ) :
    ((evalG L w : ↥(GBar n)) : AEQ n) = evalG (L.map Subtype.val) w :=
  evalG_map (GBar n).subtype L w

theorem mkQ_ofPerm_evalG (gs : List (Equiv.Perm (Fin n))) (w : List ℕ) :
    mkQ n (ofPerm (evalG gs w)) = evalG (gs.map fun g => mkQ n (ofPerm g)) w :=
  evalG_map ((mkQ n).comp (ofPermHom n)) gs w

theorem mulAut_evalG (β : MulAut ↥(GBar n)) (a b : ↥(GBar n)) (w : List ℕ) :
    β (evalG [a, b] w) = evalG [β a, β b] w :=
  evalG_map β.toMonoidHom [a, b] w

theorem permG_evalG {g₁ g₂ : Equiv.Perm (Fin n)} (h₁ : g₁ ∈ alternatingGroup (Fin n))
    (h₂ : g₂ ∈ alternatingGroup (Fin n)) (w : List ℕ)
    (hw : evalG [g₁, g₂] w ∈ alternatingGroup (Fin n)) :
    permG (evalG [g₁, g₂] w) hw = evalG [permG g₁ h₁, permG g₂ h₂] w := by
  apply Subtype.ext
  rw [coe_evalG, coe_permG, mkQ_ofPerm_evalG]
  rfl

theorem exists_swap_of_isThreeCycle {σ : Equiv.Perm (Fin n)} (h3 : σ.IsThreeCycle) :
    ∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ σ = Equiv.swap a b * Equiv.swap b c := by
  obtain ⟨a, ha⟩ : σ.support.Nonempty := Finset.card_pos.mp (by rw [h3.card_support]; norm_num)
  have hab : a ≠ σ a := fun h => (Equiv.Perm.mem_support.mp ha) h.symm
  refine ⟨a, σ a, σ (σ a), hab, fun h => hab (σ.injective h), fun h => ?_,
    h3.eq_swap_mul_swap_iff_mem_support.mpr ha⟩
  have h3' : σ ^ 3 = 1 := by rw [← h3.orderOf]; exact pow_orderOf_eq_one σ
  have h4 : (σ ^ 3) a = σ (σ (σ a)) := by rw [pow_three]; rfl
  rw [h3', Equiv.Perm.one_apply, ← h] at h4
  exact hab h4

theorem eq_of_agree {g₁ g₂ : Equiv.Perm (Fin n)} {words : List (List ℕ)}
    (hG : genProp g₁ g₂ words) (h₁ : g₁ ∈ alternatingGroup (Fin n))
    (h₂ : g₂ ∈ alternatingGroup (Fin n)) {β γ : MulAut ↥(GBar n)}
    (hβ₁ : β (permG g₁ h₁) = γ (permG g₁ h₁)) (hβ₂ : β (permG g₂ h₂) = γ (permG g₂ h₂))
    (hvec : ∀ v : Fin n → ZMod 2, ∑ i, v i = 0 → ∀ g : ↥(GBar n),
      (g : AEQ n) = mkQ n (ofVec v) → β g = γ g) : β = γ := by
  let ψ : ↥(alternatingGroup (Fin n)) →* ↥(GBar n) :=
    ((mkQ n).comp ((ofPermHom n).comp (alternatingGroup (Fin n)).subtype)).codRestrict (GBar n)
      fun σ => ofPerm_mem_GBar σ.2
  have hψ : ∀ σ : ↥(alternatingGroup (Fin n)), ψ σ = permG σ.1 σ.2 := fun σ => rfl
  let K := MonoidHom.eqLocus (β.toMonoidHom.comp ψ) (γ.toMonoidHom.comp ψ)
  have h3 : ∀ σ : Equiv.Perm (Fin n), σ.IsThreeCycle →
      σ ∈ K.map (alternatingGroup (Fin n)).subtype := by
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.mpr hσ.sign
    refine ⟨⟨σ, hσA⟩, ?_, rfl⟩
    obtain ⟨a, b, c, hab, hbc, hac, hσe⟩ := exists_swap_of_isThreeCycle hσ
    obtain ⟨w, -, hw⟩ := hG a b c hab hbc hac
    have hwA : evalG [g₁, g₂] w ∈ alternatingGroup (Fin n) := by rw [hw, ← hσe]; exact hσA
    have he : permG σ hσA = evalG [permG g₁ h₁, permG g₂ h₂] w :=
      (permG_congr (hσe.trans hw.symm) hσA hwA).trans (permG_evalG h₁ h₂ w hwA)
    show β (ψ ⟨σ, hσA⟩) = γ (ψ ⟨σ, hσA⟩)
    rw [hψ, he, mulAut_evalG, mulAut_evalG, hβ₁, hβ₂]
  have hle : alternatingGroup (Fin n) ≤ K.map (alternatingGroup (Fin n)).subtype :=
    calc alternatingGroup (Fin n)
        = Subgroup.closure {σ : Equiv.Perm (Fin n) | σ.IsThreeCycle} :=
          (Equiv.Perm.closure_three_cycles_eq_alternating (α := Fin n)).symm
      _ ≤ K.map (alternatingGroup (Fin n)).subtype :=
          (Subgroup.closure_le _).mpr fun σ hσ => h3 σ hσ
  have hK : ∀ σ : ↥(alternatingGroup (Fin n)), β (permG σ.1 σ.2) = γ (permG σ.1 σ.2) := by
    intro σ
    obtain ⟨τ, hτ, hτσ⟩ := hle σ.2
    obtain rfl : τ = σ := Subtype.ext hτσ
    exact hτ
  refine MulEquiv.ext fun g => ?_
  obtain ⟨x, w, hw, rfl⟩ := g
  have hp : w.perm ∈ alternatingGroup (Fin n) := Equiv.Perm.mem_alternatingGroup.mpr hw.2
  have hv : ∑ i, w.vec i = 0 := hw.1
  have hsplit : (⟨mkQ n w, ⟨w, hw, rfl⟩⟩ : ↥(GBar n)) =
      ⟨mkQ n (ofVec w.vec), ofVec_mem_GBar hv⟩ * permG w.perm hp :=
    Subtype.ext (by rw [Subgroup.coe_mul, coe_permG, ← map_mul, ofVec_mul_ofPerm])
  rw [hsplit, map_mul, map_mul, hvec w.vec hv _ rfl, hK ⟨w.perm, hp⟩]

theorem exists_vec_conj {g₁ g₂ : Equiv.Perm (Fin n)} {rels : List (List ℕ)}
    (hC : cocProp g₁ g₂ rels) (h₁ : g₁ ∈ alternatingGroup (Fin n))
    (h₂ : g₂ ∈ alternatingGroup (Fin n)) (β₁ : MulAut ↥(GBar n)) {v₁ v₂ : Fin n → ZMod 2}
    (hv₁ : ∑ i, v₁ i = 0) (hv₂ : ∑ i, v₂ i = 0)
    (e₁ : ((β₁ (permG g₁ h₁) : ↥(GBar n)) : AEQ n) = mkQ n (ofPerm g₁ * ofVec v₁))
    (e₂ : ((β₁ (permG g₂ h₂) : ↥(GBar n)) : AEQ n) = mkQ n (ofPerm g₂ * ofVec v₂)) :
    ∃ u : Fin n → ZMod 2, β₁ (permG g₁ h₁) = MulAut.conjNormal (mkQ n (ofVec u)) (permG g₁ h₁) ∧
      β₁ (permG g₂ h₂) = MulAut.conjNormal (mkQ n (ofVec u)) (permG g₂ h₂) := by
  obtain ⟨hrel, hcoc⟩ := hC
  have hrel' : ∀ w ∈ rels,
      inPi (evalG [ofPerm g₁ * ofVec v₁, ofPerm g₂ * ofVec v₂] w) = true := by
    intro w hw
    have h1 : evalG [permG g₁ h₁, permG g₂ h₂] w = 1 := by
      apply Subtype.ext
      rw [coe_evalG]
      have h0 := (inPi_iff _).mp (hrel w hw)
      rw [evalG_map (mkQ n)] at h0
      exact h0
    have h2 := congrArg (fun x => ((β₁ x : ↥(GBar n)) : AEQ n)) h1
    simp only [mulAut_evalG, map_one, OneMemClass.coe_one] at h2
    rw [coe_evalG] at h2
    simp only [List.map_cons, List.map_nil, e₁, e₂] at h2
    rw [inPi_iff, evalG_map (mkQ n)]
    exact h2
  obtain ⟨u, hu₁, hu₂⟩ := hcoc v₁ v₂ hv₁ hv₂ hrel'
  refine ⟨u, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [e₁, MulAut.conjNormal_apply, coe_permG, ← (eqPi_iff _ _).mp hu₁, map_mul, map_mul,
      map_inv]
  · rw [e₂, MulAut.conjNormal_apply, coe_permG, ← (eqPi_iff _ _).mp hu₂, map_mul, map_mul,
      map_inv]

theorem model117_of (hn5 : 5 ≤ n) (hn8 : n ≠ 8) (hA : adjCheck n () = true)
    (hS : spanCheck n () = true) {g₁ g₂ : Equiv.Perm (Fin n)}
    (h₁ : g₁ ∈ alternatingGroup (Fin n)) (h₂ : g₂ ∈ alternatingGroup (Fin n))
    {rels words : List (List ℕ)} (hC : cocProp g₁ g₂ rels) (hG : genProp g₁ g₂ words)
    {β : MulAut ↥(GBar n)} (hβ : MemberPerm β) :
    ∃ x : AEQ n, ∀ g : ↥(GBar n), ((β g : ↥(GBar n)) : AEQ n) = x * g * x⁻¹ := by
  have hS' : spanProp n := of_decide_eq_true hS
  obtain ⟨σ, hσ⟩ := exists_perm_of_memberPerm hn5 hn8 (adjInv_of_check hA) hβ
  have hfix := exists_beta1 hσ
  obtain ⟨v₁, hv₁, e₁⟩ := exists_vec_of_fix_zBar hn5 hn8 hfix (permG g₁ h₁)
  obtain ⟨v₂, hv₂, e₂⟩ := exists_vec_of_fix_zBar hn5 hn8 hfix (permG g₂ h₂)
  rw [coe_permG, ← map_mul] at e₁ e₂
  obtain ⟨u, hu₁, hu₂⟩ := exists_vec_conj hC h₁ h₂ _ hv₁ hv₂ e₁ e₂
  have heq : (MulAut.conjNormal (mkQ n (ofPerm σ)))⁻¹ * β =
      MulAut.conjNormal (mkQ n (ofVec u)) := by
    refine eq_of_agree hG h₁ h₂ hu₁ hu₂ fun v hv g hg => ?_
    apply Subtype.ext
    rw [fix_vec_of_fix_zBar hS' hfix hv g hg, MulAut.conjNormal_apply, hg, ← map_inv (mkQ n),
      ← map_mul (mkQ n), ← map_mul (mkQ n), conj_ofVec_ofVec]
  have hβe : β = MulAut.conjNormal (mkQ n (ofPerm σ)) * MulAut.conjNormal (mkQ n (ofVec u)) := by
    rw [← heq, mul_inv_cancel_left]
  refine ⟨mkQ n (ofPerm σ) * mkQ n (ofVec u), fun g => ?_⟩
  rw [hβe, MulAut.mul_apply, MulAut.conjNormal_apply, MulAut.conjNormal_apply]
  group

end CFSG.ClassicalInvolution.Q3.TL4.Mdl117

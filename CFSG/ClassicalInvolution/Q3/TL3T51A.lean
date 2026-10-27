module

public import CFSG.ClassicalInvolution.Q3.TL3T51
public import CFSG.ClassicalInvolution.Q3.TL3T73
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GCoc
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117GSpan
public import CFSG.ClassicalInvolution.Q3.TL4Mdl117Gen

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal

variable {n : ℕ}

theorem exists_perm_of_memberPerm_of_aut (hn : 5 ≤ n)
    (hAut : ∀ φ : MulAut (alternatingGroup (Fin n)),
      ∃ σ : Equiv.Perm (Fin n), MulAut.conjNormal σ = φ)
    {β : MulAut ↥(TL4.aeModel n)} (hβ : TL4.Mdl117.MemberPerm β) :
    ∃ σ : Equiv.Perm (Fin n),
      (∀ x : ↥(TL4.aeModel n), permQ n ((β x : ↥(TL4.aeModel n)) : AEQ n) =
        σ * permQ n (x : AEQ n) * σ⁻¹) ∧
      ∀ (α : Finset (Fin n)) (h : α.card = 4),
        ((β (TL4.Mdl117.zBarG α h) : ↥(TL4.aeModel n)) : AEQ n) =
          zBar (α.map σ.toEmbedding) (by rw [Finset.card_map]; exact h) := by
  obtain ⟨σ, hσ⟩ := hAut (autAlt hn β)
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

theorem model117At_of_aut (hn5 : 5 ≤ n)
    (hAut : ∀ φ : MulAut (alternatingGroup (Fin n)),
      ∃ σ : Equiv.Perm (Fin n), MulAut.conjNormal σ = φ) : Model117At n := by
  intro β hβ
  obtain ⟨σ, hperm, hσ⟩ := exists_perm_of_memberPerm_of_aut hn5 hAut hβ
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

theorem model117At_of_ne_six (hn5 : 5 ≤ n) (hn6 : n ≠ 6) : Model117At n :=
  model117At_of_aut hn5 fun φ =>
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6).2 φ

theorem model117At_eight : Model117At 8 :=
  model117At_of_ne_six (by norm_num) (by norm_num)

end CFSG.ClassicalInvolution.Q3.TC.Thin

module

public import CFSG.CGT.Foote82.T66.CaseIIAltData
import CFSG.CGT.Foote82.Lemma62Tools

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel CFSG.QuasithinUnique
open Equiv Equiv.Perm

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem cycleType_of_orderOf_three {σ : Perm (Fin 6)} (h : orderOf σ = 3) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := σ) (by rw [h]; norm_num)
  rw [h] at hn
  have hs := sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hs
  rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl
  · left
    rw [hn]
    rfl
  · right
    rw [hn]
    rfl

theorem cycleType_of_orderOf_two {σ : Perm (Fin 6)} (h : orderOf σ = 2)
    (hσ : σ ∈ alternatingGroup (Fin 6)) : σ.cycleType = {2, 2} := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := σ) (by rw [h]; norm_num)
  rw [h] at hn
  have hs := sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hs
  have hsign := sign_of_cycleType σ
  rw [mem_alternatingGroup.1 hσ, hn, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
  · exact absurd hsign (by decide)
  · rw [hn]
    rfl
  · exact absurd hsign (by decide)

theorem cycleType_of_orderOf_two_odd {σ : Perm (Fin 6)} (h : orderOf σ = 2)
    (hσ : σ ∉ alternatingGroup (Fin 6)) : σ.cycleType = {2} ∨ σ.cycleType = {2, 2, 2} := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (σ := σ) (by rw [h]; norm_num)
  rw [h] at hn
  have hs := sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hs
  have hsign := sign_of_cycleType σ
  rw [hn, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  rw [mem_alternatingGroup] at hσ
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
  · left
    rw [hn]
    rfl
  · exact absurd (hsign.trans (by decide)) hσ
  · right
    rw [hn]
    rfl

@[expose] def conjL (L : Subgroup (GLV V)) (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) :
    MulAut ↥L where
  toFun l := ⟨(n : GLV V) * l * (n : GLV V)⁻¹,
    (Subgroup.mem_normalizer_iff.1 n.2 l).1 l.2⟩
  invFun l := ⟨(n : GLV V)⁻¹ * l * (n : GLV V), by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ n.2) l).1 l.2
    simpa using this⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjL_coe (L : Subgroup (GLV V)) (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) (l : ↥L) :
    ((conjL L n l : ↥L) : GLV V) = (n : GLV V) * l * (n : GLV V)⁻¹ := rfl

@[expose] def conjLHom (L : Subgroup (GLV V)) :
    ↥(Subgroup.normalizer (L : Set (GLV V))) →* MulAut ↥L where
  toFun := conjL L
  map_one' := MulEquiv.ext fun l => Subtype.ext (by simp [conjL_coe])
  map_mul' a b := MulEquiv.ext fun l => Subtype.ext (by
    simp only [conjL_coe, MulAut.mul_apply, Subgroup.coe_mul]
    group)

variable {L : Subgroup (GLV V)}

namespace AD

variable {α : ↥L →* ↥(alternatingGroup (Fin 6))} {β : ↥(commSpace L ⊤) →+ altHeart 6}
  (d : AD L α β)
include d

@[expose] noncomputable def αe (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) :
    ↥L ≃* ↥(alternatingGroup (Fin 6)) :=
  MulEquiv.ofBijective α ⟨d.α_injective hL, d.α_surj⟩

theorem αe_apply (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) (l : ↥L) :
    d.αe hL l = α l := rfl

@[expose] noncomputable def rho (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) :
    ↥(Subgroup.normalizer (L : Set (GLV V))) →* MulAut ↥(alternatingGroup (Fin 6)) :=
  (MulAut.congr (d.αe hL)).toMonoidHom.comp (conjLHom L)

theorem rho_apply (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6)))
    (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) (l : ↥L) :
    d.rho hL n (α l) = α (conjL L n l) := by
  simp only [rho, MulEquiv.coe_toMonoidHom, MonoidHom.coe_comp, Function.comp_apply,
    MulAut.congr_apply, conjLHom]
  rw [show α l = d.αe hL l from rfl]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem conj_mem_VL (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) (w : ↥(commSpace L ⊤)) :
    (n : GLV V) w ∈ commSpace L ⊤ :=
  invariant_commSpace (K' := Subgroup.normalizer (L : Set (GLV V)))
    (fun _ hn _ hl => (Subgroup.mem_normalizer_iff.1 hn _).1 hl)
    (invariant_top _) n n.2 w w.2

theorem conj_mem_fixed (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) {w : V}
    (hw : w ∈ fixedSpace L) : (n : GLV V) w ∈ fixedSpace L :=
  invariant_fixedSpace (K' := Subgroup.normalizer (L : Set (GLV V)))
    (fun _ hn _ hl => (Subgroup.mem_normalizer_iff.1 hn _).1 hl) n n.2 w hw

theorem isThreeCycle_rho (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6)))
    (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) :
    ((d.rho hL n CFSG.ComponentClassification.RankTwoAlt.a6c012 :
      ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)).IsThreeCycle := by
  obtain ⟨ℓ₀, hℓ₀⟩ := d.α_surj CFSG.ComponentClassification.RankTwoAlt.a6c012
  rw [← hℓ₀, d.rho_apply hL n ℓ₀]
  set ℓ' := conjL L n ℓ₀ with hℓ'
  have ho : orderOf (α ℓ') = 3 := by
    have e1 : orderOf (α ℓ') = orderOf ℓ' := MulEquiv.orderOf_eq (d.αe hL) ℓ'
    have e2 : orderOf ℓ' = orderOf ℓ₀ := MulEquiv.orderOf_eq (conjL L n) ℓ₀
    have e3 : orderOf (α ℓ₀) = orderOf ℓ₀ := MulEquiv.orderOf_eq (d.αe hL) ℓ₀
    rw [e1, e2, ← e3, hℓ₀]
    exact orderOf_eq_prime (by decide) (by decide)
  have ho' : orderOf ((α ℓ' : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = 3 := by
    rw [Subgroup.orderOf_coe, ho]
  rcases cycleType_of_orderOf_three ho' with h | h
  · exact h
  · exfalso
    obtain ⟨w₀, hw₀, hfix⟩ := d.exists_fixed ℓ₀ (by rw [hℓ₀]; rfl)
    set w' : ↥(commSpace L ⊤) := ⟨(n : GLV V) w₀, d.conj_mem_VL n w₀⟩
    have h1 : β ⟨(ℓ' : GLV V) w', d.conj_mem ℓ' w'⟩ = β w' := by
      rw [← sub_eq_zero, ← map_sub, d.beta_eq_zero_iff]
      have h2 : ((ℓ₀ : GLV V) w₀ - w₀) ∈ fixedSpace L := by
        have : β ⟨(ℓ₀ : GLV V) w₀ - w₀, d.sub_mem ℓ₀ w₀⟩ = 0 := by
          rw [show (⟨(ℓ₀ : GLV V) w₀ - w₀, d.sub_mem ℓ₀ w₀⟩ : ↥(commSpace L ⊤)) =
            ⟨(ℓ₀ : GLV V) w₀, d.conj_mem ℓ₀ w₀⟩ - w₀ from rfl, map_sub, hfix, sub_self]
        exact (d.beta_eq_zero_iff _).1 this
      have h3 := d.conj_mem_fixed n h2
      have e : ((⟨(ℓ' : GLV V) w', d.conj_mem ℓ' w'⟩ - w' : ↥(commSpace L ⊤)) : V) =
          (n : GLV V) ((ℓ₀ : GLV V) w₀ - w₀) := by
        simp [w', hℓ', conjL_coe]
      rw [e]
      exact h3
    have h0 := d.eq_zero_of_fixed ℓ' h w' h1
    apply hw₀
    rw [d.beta_eq_zero_iff] at h0 ⊢
    have h4 := d.conj_mem_fixed n⁻¹ h0
    have e : ((n⁻¹ : ↥(Subgroup.normalizer (L : Set (GLV V)))) : GLV V) (w' : V) = w₀ := by
      show ((n : GLV V)⁻¹) ((n : GLV V) w₀) = w₀
      simp
    rwa [e] at h4

theorem exists_perm (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6)))
    (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) :
    ∃ τ : Perm (Fin 6), ∀ l : ↥L,
      (α (conjL L n l) : Perm (Fin 6)) = τ * (α l : Perm (Fin 6)) * τ⁻¹ := by
  obtain ⟨τ, hτ⟩ := CFSG.ComponentClassification.RankTwoAlt.exists_perm_of_isThreeCycle
    (d.rho hL n) (d.isThreeCycle_rho hL n)
  refine ⟨τ, fun l => ?_⟩
  rw [← hτ (α l), d.rho_apply]

theorem finrank_c₀ (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) {ℓ₀ : ↥L}
    (hℓ₀ : α ℓ₀ = CFSG.ComponentClassification.RankTwoAlt.a6c012) :
    Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers (ℓ₀ : GLV V)) ⊤) = 2 := by
  set c : GLV V := (ℓ₀ : GLV V) with hc
  have hco : orderOf c = 3 := by
    rw [hc, Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq (d.αe hL) ℓ₀, d.αe_apply, hℓ₀]
    exact orderOf_eq_prime (by decide) (by decide)
  have hodd : Odd (Nat.card ↥(Subgroup.zpowers c)) := by
    rw [Nat.card_zpowers, hco]
    decide
  have hcompl := isCompl_fixedSpace_commSpace hodd
  set P := commSpace (Subgroup.zpowers c) ⊤ with hP
  have hPW : P ≤ commSpace L ⊤ := commSpace_mono (Subgroup.zpowers_le.2 ℓ₀.2) le_rfl
  have hfixP : ∀ p ∈ P, c p = p → p = 0 := by
    intro p hp hcp
    have hpf : p ∈ fixedSpace (Subgroup.zpowers c) := by
      intro k hk
      have : k ∈ MulAction.stabilizer (GLV V) p :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hcp) hk
      exact MulAction.mem_stabilizer_iff.1 this
    have h0 : p ∈ fixedSpace (Subgroup.zpowers c) ⊓ P := ⟨hpf, hp⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at h0
    exact h0
  have hsurj : ∀ p ∈ P, ∃ q ∈ P, p = c q - q := by
    let f : ↥P → ↥P := fun q => ⟨c q - q, sub_mem_commSpace (Subgroup.mem_zpowers c)
      Submodule.mem_top⟩
    have hf : Function.Injective f := by
      intro q q' hqq
      have h1 : c ((q : V) - q') = (q : V) - q' := by
        have := congrArg Subtype.val hqq
        simp only [f] at this
        rw [map_sub]
        exact sub_eq_sub_iff_sub_eq_sub.1 this
      have h2 := hfixP _ (P.sub_mem q.2 q'.2) h1
      exact Subtype.ext (sub_eq_zero.1 h2)
    intro p hp
    obtain ⟨q, hq⟩ := (Finite.injective_iff_surjective.1 hf) ⟨p, hp⟩
    exact ⟨q, q.2, (congrArg Subtype.val hq).symm⟩
  let g : ↥P →+ altHeart 6 :=
    β.comp (AddSubgroup.inclusion (show P.toAddSubgroup ≤ (commSpace L ⊤).toAddSubgroup from hPW))
  have hgapp : ∀ p : ↥P, g p = β ⟨p, hPW p.2⟩ := fun p => rfl
  have hg : Function.Injective g := by
    rw [← AddMonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [AddMonoidHom.mem_ker, hgapp, d.beta_eq_zero_iff] at hp
    have hp' : (p : V) ∈ fixedSpace (Subgroup.zpowers c) :=
      fixedSpace_anti (Subgroup.zpowers_le.2 ℓ₀.2) hp
    have h0 : (p : V) ∈ fixedSpace (Subgroup.zpowers c) ⊓ P := ⟨hp', p.2⟩
    rw [hcompl.inf_eq_bot, Submodule.mem_bot] at h0
    exact (AddSubgroup.mem_bot).2 (Subtype.ext h0)
  have hy : ∀ k, ∑ i, c3y k i = 0 := by decide
  have hrange : Set.range g = Set.range fun k : Fin 4 => hmk (c3y k) (hy k) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨q, hq, hpq⟩ := hsurj p p.2
      obtain ⟨x, hx, hβq⟩ := exists_hmk (β ⟨q, hPW hq⟩)
      obtain ⟨k, hk⟩ := c3_comm_le x hx
      refine ⟨k, ?_⟩
      have h1 := d.beta_sub ℓ₀ ⟨q, hPW hq⟩ hx hβq
      have e : (⟨p, hPW p.2⟩ : ↥(commSpace L ⊤)) =
          ⟨(ℓ₀ : GLV V) (⟨q, hPW hq⟩ : ↥(commSpace L ⊤)) - (⟨q, hPW hq⟩ : ↥(commSpace L ⊤)),
            d.sub_mem ℓ₀ _⟩ := Subtype.ext hpq
      rw [hgapp, e, h1]
      exact hmk_congr (by rw [hℓ₀, ← c3₀_eq]; exact hk.symm) _ _
    · rintro ⟨k, rfl⟩
      obtain ⟨x, hx, hk⟩ := c3_comm_ge k
      obtain ⟨w, hw⟩ := d.β_surj (hmk x hx)
      have hpP : (ℓ₀ : GLV V) w - w ∈ P := sub_mem_commSpace (Subgroup.mem_zpowers c)
        Submodule.mem_top
      refine ⟨⟨_, hpP⟩, ?_⟩
      rw [hgapp]
      have h1 := d.beta_sub ℓ₀ w hx hw
      rw [show (⟨((⟨_, hpP⟩ : ↥P) : V), hPW hpP⟩ : ↥(commSpace L ⊤)) =
        ⟨(ℓ₀ : GLV V) w - w, d.sub_mem ℓ₀ w⟩ from rfl, h1]
      exact hmk_congr (by rw [hℓ₀, ← c3₀_eq]; exact hk) _ _
  have hinj4 : Function.Injective fun k : Fin 4 => hmk (c3y k) (hy k) := by
    intro k l hkl
    by_contra hne
    rw [hmk_eq_hmk_iff] at hkl
    exact c3y_distinct k l hne hkl
  have hcard : Nat.card ↥P = 4 := by
    rw [Nat.card_congr (Equiv.ofInjective g hg), hrange,
      ← Nat.card_congr (Equiv.ofInjective _ hinj4), Nat.card_fin]
  have h2 := card_eq_two_pow_finrank ↥P
  rw [hcard] at h2
  have : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [this] at h2
  exact (Nat.pow_right_injective le_rfl h2).symm

theorem rho_mem_range (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6)))
    (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) :
    d.rho hL n ∈ (MulAut.conjNormal (H := alternatingGroup (Fin 6))).range := by
  obtain ⟨τ, hτ⟩ := d.exists_perm hL n
  refine ⟨τ, MulEquiv.ext fun σ => Subtype.ext ?_⟩
  obtain ⟨l, rfl⟩ := d.α_surj σ
  rw [MulAut.conjNormal_apply, d.rho_apply, hτ]

theorem rho_eq_one_iff (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6)))
    (n : ↥(Subgroup.normalizer (L : Set (GLV V)))) :
    d.rho hL n = 1 ↔ (n : GLV V) ∈ Subgroup.centralizer (L : Set (GLV V)) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := congrArg (fun θ : MulAut ↥(alternatingGroup (Fin 6)) => θ (α ⟨l, hl⟩)) h
    simp only [MulAut.one_apply] at h1
    rw [d.rho_apply] at h1
    have h2 := congrArg Subtype.val (d.α_injective hL h1)
    rw [conjL_coe] at h2
    calc l * (n : GLV V) = ((n : GLV V) * l * (n : GLV V)⁻¹) * (n : GLV V) := by
          rw [h2]
      _ = (n : GLV V) * l := by group
  · intro h
    refine MulEquiv.ext fun σ => ?_
    obtain ⟨l, rfl⟩ := d.α_surj σ
    rw [d.rho_apply, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [conjL_coe, ← Subgroup.mem_centralizer_iff.1 h l l.2, mul_inv_cancel_right]

theorem card_dvd (hL : Nonempty (↥L ≃* alternatingGroup (Fin 6))) {Q : Subgroup (GLV V)}
    (hQ : IsPGroup 2 ↥Q) (hQN : Q ≤ Subgroup.normalizer (L : Set (GLV V))) :
    Nat.card ↥Q ∣ 16 * Nat.card ↥(Q ⊓ Subgroup.centralizer (L : Set (GLV V))) := by
  set ρQ : ↥Q →* MulAut ↥(alternatingGroup (Fin 6)) :=
    (d.rho hL).comp (Subgroup.inclusion hQN) with hρQ
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ρQ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρQ).toEquiv] at hcard
  have hker : Nat.card ↥ρQ.ker = Nat.card ↥(Q ⊓ Subgroup.centralizer (L : Set (GLV V))) := by
    refine Nat.card_congr
      { toFun := fun q => ⟨((q : ↥Q) : GLV V), (q : ↥Q).2, (d.rho_eq_one_iff hL _).1 q.2⟩
        invFun := fun q => ⟨⟨q, q.2.1⟩, (d.rho_eq_one_iff hL ⟨q, hQN q.2.1⟩).2 q.2.2⟩
        left_inv := fun q => rfl
        right_inv := fun q => rfl }
  have hrange : ρQ.range ≤ (MulAut.conjNormal (H := alternatingGroup (Fin 6))).range := by
    rintro _ ⟨q, rfl⟩
    exact d.rho_mem_range hL _
  have h1 : Nat.card ↥ρQ.range ∣ 720 := by
    refine (Subgroup.card_dvd_of_le hrange).trans ?_
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MulAut.conjNormal (H := alternatingGroup (Fin 6))).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, Nat.card_perm,
      Nat.card_fin] at h2
    have h720 : Nat.factorial 6 = 720 := by decide
    rw [h720] at h2
    exact Dvd.intro _ h2.symm
  have h3 : IsPGroup 2 ↥ρQ.range := by
    rw [MonoidHom.range_eq_map]
    exact (hQ.of_equiv Subgroup.topEquiv.symm).map ρQ
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h3
  have h4 : Nat.card ↥ρQ.range ∣ 16 := by
    rw [hk] at h1 ⊢
    have hcop : Nat.Coprime (2 ^ k) 45 := Nat.Coprime.pow_left _ (by norm_num)
    exact hcop.dvd_of_dvd_mul_right (by simpa using h1)
  rw [hcard, ← hker]
  exact mul_dvd_mul_right h4 _

end AD

end CaseII

end CFSG.CGT.Foote82

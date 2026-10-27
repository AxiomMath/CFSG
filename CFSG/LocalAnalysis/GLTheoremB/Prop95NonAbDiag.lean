module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAbFactors

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb

open Subgroup

theorem not_isPGroup_two {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) : ¬ IsPGroup 2 T := by
  intro hT
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial T := IsSimpleGroup.toNontrivial
  haveI := hT.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h1 | h1
  · exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance h1
  · obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have ha : a ∈ Subgroup.center T := by rw [h1]; trivial
    exact ((Subgroup.mem_center_iff.1 ha) b).symm

theorem eq_bot_of_normal_isPGroup {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (U : Subgroup T) [U.Normal] (hU : IsPGroup 2 U) :
    U = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h | h
  · exact h
  · exfalso
    rw [h] at hU
    exact not_isPGroup_two hnab (hU.of_equiv Subgroup.topEquiv)

theorem exists_odd_orderOf {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) : ∃ s : T, s ≠ 1 ∧ Odd (orderOf s) := by
  by_contra hno
  push Not at hno
  apply not_isPGroup_two hnab
  rw [IsPGroup.iff_card (p := 2)]
  haveI : Nonempty T := ⟨1⟩
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {r} hr hrd => ?_⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r hrd
  by_contra hr2
  have hodd : Odd r := hr.eq_two_or_odd'.resolve_left hr2
  have hg1 : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hg
    exact hr.one_lt.ne hg
  exact hno g hg1 (hg ▸ hodd)


section Diag

variable {Q : Type*} [Group Q] {ι : Type*} {N : Subgroup Q} {S : ι → Subgroup Q}

theorem orbit_inj {σ : Equiv.Perm ι} {p : ℕ} (hp : p.Prime) (hσ : σ ^ p = 1) {i : ι}
    (hi : σ i ≠ i) {a b : ℕ} (h : (σ ^ a) i = (σ ^ b) i) : a ≡ b [MOD p] := by
  have hord : orderOf σ = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hσ) with h1 | h1
    · exact absurd (by rw [orderOf_eq_one_iff.1 h1]; rfl) hi
    · exact h1
  have h1 : (σ ^ ((p - 1) * b + a)) i = i := by
    have e1 : (σ ^ ((p - 1) * b + a)) i = (σ ^ ((p - 1) * b)) ((σ ^ a) i) := by
      rw [pow_add, Equiv.Perm.mul_apply]
    rw [e1, h, ← Equiv.Perm.mul_apply, ← pow_add]
    have : (p - 1) * b + b = p * b := by
      have := hp.one_lt
      calc (p - 1) * b + b = ((p - 1) + 1) * b := by ring
        _ = p * b := by congr 1; omega
    rw [this, pow_mul, hσ, one_pow]
    rfl
  by_contra hne
  have hdvd : ¬ p ∣ (p - 1) * b + a := by
    intro hdvd
    apply hne
    have h2 : (p - 1) * b + a ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).2 hdvd
    have h3 : p * b + a ≡ b [MOD p] := by
      have := h2.add_left b
      have e : b + ((p - 1) * b + a) = p * b + a := by
        have := hp.one_lt
        calc b + ((p - 1) * b + a) = ((p - 1) + 1) * b + a := by ring
          _ = p * b + a := by congr 2; omega
      simpa [e] using this
    have h4 : p * b + a ≡ a [MOD p] := by
      simp [Nat.ModEq, Nat.mul_add_mod]
    exact h4.symm.trans h3
  have hcop : Nat.Coprime ((p - 1) * b + a) (orderOf σ) := by
    rw [hord]; exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd).symm
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  have := perm_pow_fix h1 u
  rw [hu] at this
  exact hi this


theorem exists_diag [Finite ι] (hF : IsFactorization N S) {p : ℕ} (hp : p.Prime) {d : Q}
    (hd : d ^ p = 1) {i : ι} (hi : hF.actHom d i ≠ i) :
    ∃ Φ : ↥(S i) →* Q, Function.Injective Φ ∧ (∀ s, d * Φ s = Φ s * d) ∧
      (∀ s, Φ s ∈ ⨆ j ∈ Set.range (fun k : ℕ => ((hF.actHom d) ^ k) i), S j) ∧
      (∀ g : Q, g * d = d * g → ∀ s s' : ↥(S i), (s' : Q) = g * s * g⁻¹ →
        g * Φ s * g⁻¹ = Φ s') := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set σ := hF.actHom d with hσdef
  have hσ : σ ^ p = 1 := by rw [hσdef, ← map_pow, hd, map_one]
  let idx : ZMod p → ι := fun k => (σ ^ k.val) i
  have hidx : Function.Injective idx := by
    intro k l h
    have h1 := orbit_inj hp hσ hi h
    exact ZMod.val_injective p (h1.eq_of_lt_of_lt (ZMod.val_lt k) (ZMod.val_lt l))
  let ι' : ZMod p → ↥(S i) →* Q := fun k =>
    (MulAut.conj (d ^ k.val)).toMonoidHom.comp (S i).subtype
  have hι'apply : ∀ k s, ι' k s = d ^ k.val * (s : Q) * (d ^ k.val)⁻¹ := fun k s => rfl
  have hrange : ∀ k, (ι' k).range ≤ S (idx k) := by
    intro k x hx
    obtain ⟨s, rfl⟩ := hx
    rw [show S (idx k) = cj (d ^ k.val) (S i) from hF.S_actHom_pow d k.val i, mem_cj, hι'apply]
    simpa [mul_assoc] using s.2
  have hcomm : Pairwise fun k l => ∀ (x y : ↥(S i)), Commute (ι' k x) (ι' l y) := by
    intro k l hkl x y
    exact hF.commute (fun h => hkl (hidx h)) (hrange k ⟨x, rfl⟩) (hrange l ⟨y, rfl⟩)
  let ψ : (ZMod p → ↥(S i)) →* Q := MonoidHom.noncommPiCoprod ι' hcomm
  let δ : ↥(S i) →* (ZMod p → ↥(S i)) := Pi.monoidHom fun _ => MonoidHom.id ↥(S i)
  let Φ : ↥(S i) →* Q := ψ.comp δ
  have hΦapply : ∀ s, Φ s = Finset.univ.noncommProd (fun k => ι' k s)
      (fun k _ l _ hkl => hcomm hkl s s) := fun s => MonoidHom.noncommPiCoprod_apply (hcomm := hcomm) ι' (fun _ => s)
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · have hind : iSupIndep fun k => (ι' k).range := (hF.indep.comp hidx).mono hrange
    have hψ : Function.Injective ψ := MonoidHom.injective_noncommPiCoprod_of_iSupIndep ι' hind
      (fun k => (MulAut.conj (d ^ k.val)).injective.comp (S i).subtype_injective)
    have hδ : Function.Injective δ := fun a b h => congrFun h 0
    exact hψ.comp hδ
  · intro s
    let ρ : (ZMod p → ↥(S i)) →* (ZMod p → ↥(S i)) :=
      { toFun := fun f k => f (k - 1)
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have key : (MulAut.conj d).toMonoidHom.comp ψ = ψ.comp ρ := by
      refine MonoidHom.pi_ext fun k a => ?_
      have hρ : ρ (Pi.mulSingle k a) = Pi.mulSingle (k + 1) a := by
        funext j
        simp [ρ, Pi.mulSingle_apply, sub_eq_iff_eq_add]
      simp only [MonoidHom.comp_apply, hρ]
      rw [show ψ (Pi.mulSingle k a) = ι' k a from MonoidHom.noncommPiCoprod_mulSingle ι' k a,
        show ψ (Pi.mulSingle (k + 1) a) = ι' (k + 1) a from
          MonoidHom.noncommPiCoprod_mulSingle ι' (k + 1) a]
      have hv : d ^ (k + 1).val = d ^ (k.val + 1) := by
        rw [ZMod.val_add, ZMod.val_one, ← pow_eq_pow_mod _ hd]
      simp only [hι'apply, hv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_succ']
      group
    have h1 : d * Φ s * d⁻¹ = Φ s := by
      have h2 := congrArg (fun F => F (δ s)) key
      have hρδ : ρ (δ s) = δ s := rfl
      simp only [MonoidHom.comp_apply, hρδ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
      exact h2
    calc d * Φ s = d * Φ s * d⁻¹ * d := by group
      _ = Φ s * d := by rw [h1]
  · intro s
    rw [hΦapply]
    refine Subgroup.noncommProd_mem _ _ fun k _ => ?_
    exact Subgroup.mem_iSup_of_mem (idx k) (Subgroup.mem_iSup_of_mem
      (show idx k ∈ Set.range (fun k : ℕ => (σ ^ k) i) from ⟨k.val, rfl⟩) (hrange k ⟨s, rfl⟩))
  · intro g hg s s' hs'
    rw [hΦapply, hΦapply]
    have hmap := Finset.map_noncommProd Finset.univ (fun k => ι' k s)
      (fun k _ l _ hkl => hcomm hkl s s) (MulAut.conj g)
    rw [MulAut.conj_apply] at hmap
    rw [hmap]
    refine Finset.noncommProd_congr rfl (fun k _ => ?_) _
    have hgk : g * d ^ k.val = d ^ k.val * g := (Commute.pow_right (hg : Commute g d) k.val).eq
    simp only [hι'apply, MulAut.conj_apply, hs']
    calc g * (d ^ k.val * (s : Q) * (d ^ k.val)⁻¹) * g⁻¹
        = (g * d ^ k.val) * (s : Q) * (g * d ^ k.val)⁻¹ := by group
      _ = (d ^ k.val * g) * (s : Q) * (d ^ k.val * g)⁻¹ := by rw [hgk]
      _ = d ^ k.val * (g * s * g⁻¹) * (d ^ k.val)⁻¹ := by group

end Diag

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb

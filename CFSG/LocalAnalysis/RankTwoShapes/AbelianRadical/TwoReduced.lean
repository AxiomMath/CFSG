module

public import CFSG.LocalAnalysis.RankTwoShapes.HomocyclicSubgroup
public import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniAutomorphismKernel
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

public section

namespace CFSG.RankTwoShapes

open CFSG.RankThreeEvenClassification.Helpers

universe u v

section Punctured

variable (V : Type v) [Group V]

@[expose] def mulAutPuncturedPerm : MulAut V →* Equiv.Perm {v : V // v ≠ 1} where
  toFun f := Equiv.Perm.subtypePerm f.toEquiv (fun _ => f.map_ne_one_iff)
  map_one' := by ext; rfl
  map_mul' _ _ := by ext; rfl

theorem mulAutPuncturedPerm_apply (f : MulAut V) (w : {v : V // v ≠ 1}) :
    ((mulAutPuncturedPerm V f w : {v : V // v ≠ 1}) : V) = f w :=
  rfl

theorem mulAutPuncturedPerm_injective : Function.Injective (mulAutPuncturedPerm V) := by
  intro f g hfg
  ext w
  by_cases hw : w = 1
  · rw [hw, map_one, map_one]
  · have h := congrArg Subtype.val (Equiv.ext_iff.mp hfg ⟨w, hw⟩)
    rwa [mulAutPuncturedPerm_apply, mulAutPuncturedPerm_apply] at h

theorem card_punctured [Finite V] : Nat.card {v : V // v ≠ 1} = Nat.card V - 1 := by
  classical
  have := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

end Punctured

variable {Q : Type u} [CommGroup Q]

instance square_characteristic : (Subgroup.square Q).Characteristic := by
  refine ⟨fun φ => ?_⟩
  ext q
  simp only [Subgroup.mem_comap, Subgroup.mem_square, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨φ.symm r, φ.injective (by rw [hr, map_mul, MulEquiv.apply_symm_apply])⟩
  · rintro ⟨r, rfl⟩
    exact ⟨φ r, map_mul φ r r⟩

@[expose] noncomputable def squareQuotientAction (A : Subgroup (MulAut Q)) :
    A →* MulAut (Q ⧸ Subgroup.square Q) :=
  (characteristicQuotientAction (Subgroup.square Q)).comp A.subtype

theorem squareQuotientAction_apply (A : Subgroup (MulAut Q)) (a : A) (q : Q) :
    squareQuotientAction A a (q : Q ⧸ Subgroup.square Q) =
      (((a : MulAut Q) q : Q) : Q ⧸ Subgroup.square Q) :=
  characteristicQuotientAction_apply (Subgroup.square Q) a q

theorem card_quotient_square_le_four [Finite Q] (hrank : TwoRankLeTwo Q) :
    Nat.card (Q ⧸ Subgroup.square Q) ≤ 4 := by
  have hrange : (powMonoidHom 2 : Q →* Q).range = Subgroup.square Q := by
    ext q
    simp only [MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_square, IsSquare, pow_two]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
    · rintro ⟨r, rfl⟩
      exact ⟨r, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range (powMonoidHom 2 : Q →* Q)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.square Q)
  rw [hrange] at h1
  have hpos : 0 < Nat.card (Subgroup.square Q) := Nat.card_pos
  have heq : Nat.card (Q ⧸ Subgroup.square Q) = Nat.card (powMonoidHom 2 : Q →* Q).ker :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [← h2, h1])
  rw [heq]
  exact hrank _ inferInstance (fun e he => MonoidHom.mem_ker.mp he)

theorem isPGroup_ker_characteristicQuotientAction_square [Finite Q] (hQ : IsPGroup 2 Q) :
    IsPGroup 2 (characteristicQuotientAction (Subgroup.square Q)).ker := by
  have : Fact (IsPGroup 2 Q) := ⟨hQ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Subgroup.square Q ≤ frattini Q := by
    rintro q ⟨r, rfl⟩
    rw [← pow_two]
    exact CFSG.pth_power_mem_frattini_of_isPGroup r
  apply (frattini_automorphism_kernel_isPGroup 2 Nat.prime_two hQ).to_le
  intro α hα
  rw [characteristicQuotientAction_mem_kernel_iff] at hα ⊢
  intro q
  have h := hα q
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h ⊢
  exact hle h

theorem eq_one_of_apply_eq_of_square_quotient [Finite Q] (hQ : IsPGroup 2 Q) (α : MulAut Q)
    (hα : α ^ 3 = 1)
    (hfree : ∀ q : Q, ((α q : Q) : Q ⧸ Subgroup.square Q) = (q : Q ⧸ Subgroup.square Q) →
      q ∈ Subgroup.square Q)
    (q : Q) (hq : α q = q) : q = 1 := by
  have hα3 : ∀ s : Q, α (α (α s)) = s := fun s => by
    have h := congrArg (fun f : MulAut Q => f s) hα
    simpa [pow_succ, MulAut.mul_apply] using h
  have hsq : ∀ q : Q, α q = q → ∃ c : Q, α c = c ∧ q = c ^ 2 := by
    intro q hq
    obtain ⟨s, hs⟩ := hfree q (by rw [hq])
    have h1 : α s * α s = q := by rw [← map_mul, ← hs, hq]
    have h2 : α (α s) * α (α s) = q := by rw [← map_mul, h1, hq]
    refine ⟨s * α s * α (α s) * q⁻¹, ?_, ?_⟩
    · rw [map_mul, map_mul, map_mul, map_inv, hα3, hq]
      rw [mul_comm s (α s), mul_assoc (α s) s, mul_comm s (α (α s)), ← mul_assoc]
    · calc q = (s * s) * (α s * α s) * (α (α s) * α (α s)) * q⁻¹ * q⁻¹ := by
            rw [← hs, h1, h2]; group
        _ = (s * α s * α (α s) * q⁻¹) ^ 2 := by
            rw [pow_two]
            simp only [mul_assoc, mul_comm, mul_left_comm]
  have hpow : ∀ k : ℕ, ∀ q : Q, α q = q → ∃ c : Q, α c = c ∧ q = c ^ (2 ^ k) := by
    intro k
    induction k with
    | zero => exact fun q hq => ⟨q, hq, by rw [pow_zero, pow_one]⟩
    | succ k ih =>
      intro q hq
      obtain ⟨c, hc, rfl⟩ := ih q hq
      obtain ⟨d, hd, rfl⟩ := hsq c hc
      exact ⟨d, hd, by rw [← pow_mul, pow_succ, mul_comm]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := hQ.exists_card_eq
  obtain ⟨c, -, rfl⟩ := hpow m q hq
  rw [← hm, pow_card_eq_one']

theorem abelian_two_reduced_automorphisms [Finite Q] (hQ : IsPGroup 2 Q) (hrank : TwoRankLeTwo Q)
    (A : Subgroup (MulAut Q)) (heven : 2 ∣ Nat.card A) (hO2 : CFSG.pCore 2 A = ⊥) :
    ∃ n : ℕ, 1 ≤ n ∧
      Nonempty (Q ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) ∧
      Nat.card (Q ⧸ Subgroup.square Q) = 4 ∧
      Function.Bijective (squareQuotientAction A) ∧
      Nat.card (MulAut (Q ⧸ Subgroup.square Q)) = 6 ∧
      Nat.card A = 6 ∧ Nonempty (A ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := Q ⧸ Subgroup.square Q
  set π := squareQuotientAction A with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hO2]
    have hker : π.ker = (characteristicQuotientAction (Subgroup.square Q)).ker.comap A.subtype :=
      (MonoidHom.comap_ker _ _).symm
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [hker]
    exact (isPGroup_ker_characteristicQuotientAction_square hQ).comap_of_injective _
      A.subtype_injective
  set ρ := mulAutPuncturedPerm V
  have hρinj : Function.Injective ρ := mulAutPuncturedPerm_injective V
  set ψ := ρ.comp π
  have hψinj : Function.Injective ψ := hρinj.comp hπinj
  have hdvd : Nat.card A ∣ (Nat.card V - 1).factorial := by
    rw [← card_punctured V, ← Nat.card_perm]
    exact Subgroup.card_dvd_of_injective ψ hψinj
  have hV4 : Nat.card V ≤ 4 := card_quotient_square_le_four hrank
  have hV1 : 0 < Nat.card V := Nat.card_pos
  have hne2 : Nat.card A ≠ 2 := by
    intro h2
    have hp : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by rw [h2, pow_one])
    have htop : (⊤ : Subgroup A) ≤ CFSG.pCore 2 A := le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩
    have hcard := Subgroup.card_le_of_le htop
    rw [hO2, Subgroup.card_bot, Subgroup.card_top, h2] at hcard
    omega
  have hcases : Nat.card V = 4 ∧ Nat.card A = 6 := by
    obtain ⟨a, ha⟩ : ∃ a, Nat.card A = a := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, Nat.card V = d := ⟨_, rfl⟩
    rw [ha] at hdvd heven hne2 ⊢
    rw [hd] at hdvd hV4 hV1 ⊢
    have hapos : 0 < a := ha ▸ Nat.card_pos
    have hale : a ≤ (d - 1).factorial := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
    have hfac : (d - 1).factorial ≤ 6 := by interval_cases d <;> decide
    have ha6 : a ≤ 6 := hale.trans hfac
    clear hale hfac ha hd
    interval_cases d <;> interval_cases a <;> revert hdvd heven hne2 <;> decide
  obtain ⟨hV4', hA6⟩ := hcases
  have hpunct : Nat.card {v : V // v ≠ 1} = 3 := by rw [card_punctured V, hV4']
  have hψbij : Function.Bijective ψ := by
    refine hψinj.bijective_of_nat_card_le ?_
    rw [Nat.card_perm, hpunct, hA6]
    decide
  have hπsurj : Function.Surjective π := by
    intro β
    obtain ⟨a, ha⟩ := hψbij.2 (ρ β)
    exact ⟨a, hρinj ha⟩
  have hπbij : Function.Bijective π := ⟨hπinj, hπsurj⟩
  have hAut6 : Nat.card (MulAut V) = 6 := by
    rw [← Nat.card_congr (Equiv.ofBijective π hπbij), hA6]
  let e3 : {v : V // v ≠ 1} ≃ Fin 3 := Finite.equivFinOfCardEq hpunct
  have hS3 : Nonempty (A ≃* Equiv.Perm (Fin 3)) :=
    ⟨(MulEquiv.ofBijective ψ hψbij).trans (Equiv.permCongrHom e3)⟩
  let σ : Equiv.Perm {v : V // v ≠ 1} := Equiv.permCongrHom e3.symm (finRotate 3)
  have hσ3 : σ ^ 3 = 1 := by
    change Equiv.permCongrHom e3.symm (finRotate 3) ^ 3 = 1
    rw [← map_pow, show finRotate 3 ^ 3 = 1 by decide, map_one]
  have hσfree : ∀ w, σ w ≠ w := by
    intro w hw
    have hrot : ∀ i : Fin 3, finRotate 3 i ≠ i := by decide
    apply hrot (e3 w)
    have h := congrArg e3 hw
    change e3 (e3.symm (finRotate 3 (e3.symm.symm w))) = e3 w at h
    rwa [Equiv.apply_symm_apply, Equiv.symm_symm] at h
  obtain ⟨a, ha⟩ := hψbij.2 σ
  set α : MulAut Q := (a : MulAut Q) with hαdef
  have ha3 : a ^ 3 = 1 := hψinj (by rw [map_pow, ha, hσ3, map_one])
  have hα3 : α ^ 3 = 1 := by rw [hαdef, ← Subgroup.coe_pow, ha3, Subgroup.coe_one]
  have hfree : ∀ q : Q, ((α q : Q) : V) = (q : V) → q ∈ Subgroup.square Q := by
    intro q hq
    rw [← QuotientGroup.eq_one_iff]
    by_contra hne
    apply hσfree ⟨(q : V), hne⟩
    rw [← ha]
    apply Subtype.ext
    change (π a) (q : V) = (q : V)
    rw [hπ, squareQuotientAction_apply]
    exact hq
  have hfpf : ∀ q : Q, α q = q → q = 1 :=
    eq_one_of_apply_eq_of_square_quotient hQ α hα3 hfree
  obtain ⟨x, hxmax⟩ := Finite.exists_max (fun q : Q => orderOf q)
  obtain ⟨e, he⟩ := IsPGroup.iff_orderOf.mp hQ x
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    have htriv : ∀ q : Q, q = 1 := by
      intro q
      have h := hxmax q
      rw [he, he0, pow_zero] at h
      exact orderOf_eq_one_iff.mp (le_antisymm h (orderOf_pos q))
    have hsub : Subsingleton V := by
      refine ⟨fun v w => ?_⟩
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
      rw [htriv v, htriv w]
    have h1 : Nat.card V = 1 := Nat.card_unique
    omega
  obtain ⟨-, -, ⟨φ⟩, -, -, -, htop⟩ :=
    three_automorphism_homocyclic_subgroup hQ hrank α hα3 hfpf x hxmax he he1
  refine ⟨e, he1, ⟨Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr (htop mul_comm).symm).trans φ)⟩, hV4', hπbij, hAut6, hA6, hS3⟩

end CFSG.RankTwoShapes

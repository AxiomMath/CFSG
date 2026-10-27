module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreStd
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFRRank

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

@[expose] def InnerThree (X : Type*) [Group X] : Prop :=
  ∀ β : MulAut X, β ^ 3 = 1 → ∃ y : X, β = MulAut.conj y

@[expose] def CoreThree (X : Type*) [Group X] : Prop :=
  ∀ y : X, y ^ 3 = 1 → ∃ E : Subgroup X, E ≤ Subgroup.centralizer {y} ∧ IsElemAbelian 3 E ∧
    Nat.card E = 3 ^ 4

@[expose] def AutRankFour (X : Type*) [Group X] : Prop :=
  ∀ β : MulAut X, β ^ 3 = 1 → ∃ E : Subgroup X, E ≤ fixSubgroup β ∧ IsElemAbelian 3 E ∧
    Nat.card E = 3 ^ 4

variable {X Y : Type*} [Group X] [Group Y]

theorem isElemAbelian_of_forall {G : Type*} [Group G] {p : ℕ} (H : Subgroup G)
    (hc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (he : ∀ x ∈ H, x ^ p = 1) : IsElemAbelian p H :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, he⟩

private theorem congr_pow_three (e : X ≃* Y) {β : MulAut X} (hβ : β ^ 3 = 1) :
    MulAut.congr e β ^ 3 = 1 := by
  rw [← map_pow, hβ, map_one]

theorem innerThree_of_mulEquiv (e : X ≃* Y) (h : InnerThree Y) : InnerThree X := by
  intro β hβ
  obtain ⟨y, hy⟩ := h (MulAut.congr e β) (congr_pow_three e hβ)
  refine ⟨e.symm y, MulEquiv.ext fun x => ?_⟩
  have h1 : e (β x) = y * e x * y⁻¹ := by
    have h2 := congrArg (fun f : MulAut Y => f (e x)) hy
    change e (β (e.symm (e x))) = MulAut.conj y (e x) at h2
    rwa [MulEquiv.symm_apply_apply, MulAut.conj_apply] at h2
  rw [MulAut.conj_apply]
  apply e.injective
  rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem coreThree_of_mulEquiv (e : X ≃* Y) (h : CoreThree Y) : CoreThree X := by
  intro y hy
  obtain ⟨E, hE, hEa, hEc⟩ := h (e y) (by rw [← map_pow, hy, map_one])
  refine ⟨E.map (e.symm : Y →* X), ?_, KD264Lie.X1LinCore.Std.isElemAbelian_map' _ hEa, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hE hx)
    apply e.injective
    change e (e.symm x * y) = e (y * e.symm x)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h1]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hEc]

theorem autRankFour_of_inner (hZ : Subgroup.center X = ⊥) (hinn : InnerThree X)
    (hcore : CoreThree X) : AutRankFour X := by
  intro β hβ
  obtain ⟨y, rfl⟩ := hinn β hβ
  have hy3 : y ^ 3 = 1 := by
    have h1 : MulAut.conj (y ^ 3) = 1 := by rw [map_pow]; exact hβ
    have h2 : y ^ 3 ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun f : MulAut X => f g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * y ^ 3 = (y ^ 3 * g * (y ^ 3)⁻¹) * y ^ 3 := by rw [h3]
        _ = y ^ 3 * g := by group
    rw [hZ] at h2
    exact Subgroup.mem_bot.1 h2
  obtain ⟨E, hE, hEa, hEc⟩ := hcore y hy3
  refine ⟨E, fun x hx => ?_, hEa, hEc⟩
  rw [mem_fixSubgroup, MulAut.conj_apply, ← Subgroup.mem_centralizer_singleton_iff.1 (hE hx),
    mul_inv_cancel_right]

theorem center_quotient_center_eq_bot {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Subgroup.center (Q ⧸ Subgroup.center Q) = ⊥ := by
  have hs : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Q ⧸ Subgroup.center Q)) with
    h1 | h1
  · exact h1
  · exfalso
    have hcomm : ∀ a b : Q ⧸ Subgroup.center Q, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top a) b).symm
    have hle : commutator Q ≤ Subgroup.center Q := by
      rw [commutator, Subgroup.commutator_le]
      intro x _ y _
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    have htop : (⊤ : Subgroup Q) ≤ Subgroup.center Q := hQ.1 ▸ hle
    obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : Q ⧸ Subgroup.center Q)).mp hs.toNontrivial
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    exact ha ((QuotientGroup.eq_one_iff x).mpr (htop (Subgroup.mem_top x)))

theorem exists_elemAb_fix_of_quotient {Q : Type*} [Group Q] [Finite Q]
    (hZ3 : ∀ z ∈ Subgroup.center Q, z ^ 3 = 1 → z = 1)
    (hX : AutRankFour (Q ⧸ Subgroup.center Q)) (α : MulAut Q) (hα : α ^ 3 = 1) :
    ∃ E : Subgroup Q, E ≤ fixSubgroup α ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center Q with hZdef
  set π : Q →* Q ⧸ Z := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : ∀ x : Q, π x = 1 ↔ x ∈ Z := fun x => QuotientGroup.eq_one_iff x
  set αb : MulAut (Q ⧸ Z) := QuotientGroup.congr Z Z α (Subgroup.map_center_eq α) with hαbdef
  have hαb : ∀ x : Q, αb (π x) = π (α x) := fun x => rfl
  have hαb3 : αb ^ 3 = 1 := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hπs y
    have h1 : (α ^ 3) x = x := by rw [hα]; rfl
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hαb, hαb, hαb,
      MulAut.one_apply]
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply] at h1
    rw [h1]
  obtain ⟨Eb, hEb, hEba, hEbc⟩ := hX αb hαb3
  have h3Z : ¬ 3 ∣ Nat.card Z := by
    intro h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h
    have hz3 : (z : Q) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
    have hz1 : z = 1 := Subtype.ext (hZ3 z z.2 hz3)
    rw [hz1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  set P := Eb.comap π with hPdef
  have hPmap : P.map π = Eb := Subgroup.map_comap_eq_self_of_surjective hπs Eb
  have hdvd : 3 ^ 4 ∣ Nat.card P := by
    rw [← hEbc, ← hPmap]
    exact Subgroup.card_map_dvd P π
  obtain ⟨H0, hH0⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 3 hdvd
  set H := H0.map P.subtype with hHdef
  have hHP : H ≤ P := Subgroup.map_subtype_le H0
  have hHc : Nat.card H = 3 ^ 4 := by
    rw [hHdef, Subgroup.card_map_of_injective P.subtype_injective, hH0]
  have hHZ : ∀ h ∈ H, h ∈ Z → h = 1 := by
    have hcop : Nat.Coprime (3 ^ 4) (Nat.card Z) :=
      Nat.Coprime.pow_left 4 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3Z)
    have h1 : Nat.card (H ⊓ Z : Subgroup Q) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes hcop ?_ ?_
      · rw [← hHc]
        exact Subgroup.card_dvd_of_le inf_le_left
      · exact Subgroup.card_dvd_of_le inf_le_right
    have h2 := Subgroup.eq_bot_of_card_eq _ h1
    intro h hH hZ'
    have h3 : h ∈ H ⊓ Z := ⟨hH, hZ'⟩
    rw [h2] at h3
    exact Subgroup.mem_bot.1 h3
  have hHEb : ∀ h ∈ H, π h ∈ Eb := fun h hh => hHP hh
  refine ⟨H, ?_, isElemAbelian_of_forall H ?_ ?_, hHc⟩
  ·
    intro e he
    rw [mem_fixSubgroup]
    have hfix : αb (π e) = π e := mem_fixSubgroup.1 (hEb (hHEb e he))
    rw [hαb] at hfix
    have hz : e⁻¹ * α e ∈ Z := by
      rw [← hker, map_mul, map_inv, hfix, inv_mul_cancel]
    set z := e⁻¹ * α e with hzdef
    have hαe : α e = e * z := by rw [hzdef, mul_inv_cancel_left]
    have he3 : e ^ 3 = 1 := by
      refine hHZ _ (H.pow_mem he 3) ?_
      rw [← hker, map_pow]
      exact hEba.2 _ (hHEb e he)
    have hcomm : Commute e z := (Subgroup.mem_center_iff.1 hz e)
    have hz3 : z ^ 3 = 1 := by
      have h1 : α (e ^ 3) = (e * z) ^ 3 := by rw [map_pow, hαe]
      rw [he3, map_one, hcomm.mul_pow, he3, one_mul] at h1
      exact h1.symm
    have hz1 : z = 1 := hZ3 z hz hz3
    rw [hαe, hz1, mul_one]
  ·
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ H := H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx))
      (H.inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ Z := by
      rw [← hker]
      have hc := hEba.1.is_comm.comm ⟨π x, hHEb x hx⟩ ⟨π y, hHEb y hy⟩
      have hc' : π x * π y = π y * π x := congrArg Subtype.val hc
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc']
      group
    have h3 := hHZ _ h1 h2
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  ·
    intro x hx
    refine hHZ _ (H.pow_mem hx 3) ?_
    rw [← hker, map_pow]
    exact hEba.2 _ (hHEb x hx)

end CFSG.LocalAnalysis.GLTheoremA.SFRRank

end

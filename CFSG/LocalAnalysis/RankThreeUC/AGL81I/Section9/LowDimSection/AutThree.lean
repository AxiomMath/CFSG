module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
public import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.LowDimSection.Sections

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open FiveTransitive.CharacteristicAutomorphism (restrict quotient quotient_apply_mk)

section Helpers

variable {C : Type} [Group C]

private lemma apply_eq_of_mem_of_isCyclic (N : Subgroup C) [N.Characteristic] (hN : IsCyclic N)
    {G : Subgroup (MulAut C)} (hG : Group.IsPerfect G) {σ : MulAut C} (hσ : σ ∈ G) {z : C}
    (hz : z ∈ N) : σ z = z := by
  let f := (restrict N).comp G.subtype
  have : Group.IsPerfect f.range := Group.IsPerfect.range f
  have : IsMulCommutative f.range := ⟨⟨fun a b => Subtype.ext <| by
    obtain ⟨m, hm⟩ := (a : MulAut N).toMonoidHom.map_cyclic
    obtain ⟨n, hn⟩ := (b : MulAut N).toMonoidHom.map_cyclic
    simp only [MulEquiv.coe_toMonoidHom] at hm hn
    ext w
    simp only [Subgroup.coe_mul, MulAut.mul_apply, hm, hn]
    rw [← zpow_mul, ← zpow_mul, mul_comm]⟩⟩
  have h1 : f ⟨σ, hσ⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨f ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩ : f.range) 1)
  have := congrArg (fun a : MulAut N => ((a ⟨z, hz⟩ : N) : C)) h1
  simpa [f] using this

private lemma mul_comm_of_trivial_mod {N : Subgroup C} (hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    {σ τ : MulAut C} (hσN : ∀ z ∈ N, σ z = z) (hτN : ∀ z ∈ N, τ z = z)
    (hσ : ∀ x : C, x⁻¹ * σ x ∈ N) (hτ : ∀ x : C, x⁻¹ * τ x ∈ N) : σ * τ = τ * σ := by
  ext x
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ N, σ x = x * a := ⟨_, hσ x, by group⟩
  obtain ⟨b, hb, hbx⟩ : ∃ b ∈ N, τ x = x * b := ⟨_, hτ x, by group⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, hbx, map_mul, hσN b hb, hax, map_mul, hτN a ha, hbx,
    mul_assoc, mul_assoc, hN a ha b hb]

private lemma quot_mul_comm_of_commutator_le {N : Subgroup C} [N.Normal]
    (hcomm : commutator C ≤ N) (a b : C ⧸ N) : a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H a =>
  induction b using QuotientGroup.induction_on with | H b =>
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have h := hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top b⁻¹)
    (Subgroup.mem_top a⁻¹))
  convert h using 1
  simp only [commutatorElement_def]
  group

private lemma quot_pow_eq_one {N : Subgroup C} [N.Normal] {n : ℕ} (hpow : ∀ x : C, x ^ n ∈ N)
    (e : C ⧸ N) : e ^ n = 1 := by
  induction e using QuotientGroup.induction_on with
  | H x => rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hpow x

private lemma card_mulAut_quot_lt [Finite C] (hC : IsPGroup 3 C)
    (hcomm : commutator C ≤ Subgroup.center C) (hcube : ∀ x : C, x ^ 3 ∈ Subgroup.center C)
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 9) :
    Nat.card (MulAut (C ⧸ Subgroup.center C)) < 60 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := (hC.to_quotient (Subgroup.center C)).exists_card_eq
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hn ▸ hcard : 3 ^ n ≤ 3 ^ 2)
  rw [CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary
    (quot_mul_comm_of_commutator_le hcomm) (quot_pow_eq_one hcube) hn]
  interval_cases n <;> simp [Fin.prod_univ_succ]

private lemma ker_quotient_mul_comm (hZ : IsCyclic (Subgroup.center C))
    {G : Subgroup (MulAut C)} (hG : Group.IsPerfect G)
    (a b : ((quotient (Subgroup.center C)).comp G.subtype).ker) : a * b = b * a := by
  have htriv : ∀ k : ((quotient (Subgroup.center C)).comp G.subtype).ker,
      ∀ x : C, x⁻¹ * (k : G).1 x ∈ Subgroup.center C := fun k x => by
    have h := quotient_apply_mk (Subgroup.center C) (k : G).1 x
    have hk : quotient (Subgroup.center C) (k : G).1 = 1 := k.2
    rw [hk] at h
    simp only [MulAut.one_apply, QuotientGroup.mk'_apply] at h
    exact QuotientGroup.eq.1 h
  have hfix : ∀ k : ((quotient (Subgroup.center C)).comp G.subtype).ker,
      ∀ z ∈ Subgroup.center C, (k : G).1 z = z := fun k z hz =>
    apply_eq_of_mem_of_isCyclic _ hZ hG (k : G).2 hz
  refine Subtype.ext (Subtype.ext ?_)
  exact mul_comm_of_trivial_mod (fun x _ y hy => (Subgroup.mem_center_iff.1 hy x))
    (hfix a) (hfix b) (htriv a) (htriv b)

end Helpers

theorem false_of_mulAut_three {C : Type} [Group C] [Finite C] (hC : IsPGroup 3 C)
    (hZ : IsCyclic (Subgroup.center C)) (hcomm : commutator C ≤ Subgroup.center C)
    (hcube : ∀ x : C, x ^ 3 ∈ Subgroup.center C)
    (hcard : Nat.card (C ⧸ Subgroup.center C) ≤ 9) {G : Subgroup (MulAut C)}
    (hG : Group.IsPerfect G) {S : Type} [Group S] [IsSimpleGroup S] (hS : ¬ IsMulCommutative S)
    (ψ : ↥G →* S) (hψ : Function.Surjective ψ) : False := by
  set f := (quotient (Subgroup.center C)).comp G.subtype
  have hK : f.ker.map ψ = ⊥ := map_eq_bot_of_isSolvable hS hψ (MonoidHom.normal_ker f)
    (isSolvable_of_comm (ker_quotient_mul_comm hZ hG))
  have hle : ψ.ker.index ∣ f.ker.index :=
    Subgroup.index_dvd_of_le ((Subgroup.map_eq_bot_iff _).1 hK)
  have hSidx : ψ.ker.index = Nat.card S := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hψ, Subgroup.card_top]
  have hpos : 0 < f.ker.index := by rw [Subgroup.index_ker]; exact Nat.card_pos
  have hlt : f.ker.index < 60 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_card_group _).trans_lt (card_mulAut_quot_lt hC hcomm hcube hcard)
  have hcardS : Nat.card S ≤ f.ker.index := hSidx ▸ Nat.le_of_dvd hpos hle
  have : Finite S := Nat.finite_of_card_ne_zero <| by
    rw [← hSidx]; exact (Nat.pos_of_dvd_of_pos hle hpos).ne'
  have hna : ∃ x y : S, x * y ≠ y * x := by
    by_contra h
    push Not at h
    exact hS ⟨⟨h⟩⟩
  have := CFSG.GroupTheory.nonabelian_simple_order_at_least_sixty inferInstance hna
  omega

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

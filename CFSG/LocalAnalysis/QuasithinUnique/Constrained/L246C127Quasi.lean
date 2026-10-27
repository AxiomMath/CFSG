module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic
public import CFSG.Quasithin.Background.A1cKlein
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace L246C127

section CentralTwo

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem isPGroup_quotient_of_sup_eq_top {N Z : Subgroup A} [N.Normal] [Z.Normal] (hZ : IsPGroup 2 Z)
    (h : N ⊔ Z = ⊤) : IsPGroup 2 (A ⧸ N) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    have hx : x ∈ N ⊔ Z := h ▸ Subgroup.mem_top x
    obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    obtain ⟨k, hk⟩ := hZ ⟨z, hz⟩
    refine ⟨k, ?_⟩
    have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hn1 : (QuotientGroup.mk n : A ⧸ N) = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [QuotientGroup.mk_mul, hn1, one_mul, ← QuotientGroup.mk_pow, hzk, QuotientGroup.mk_one]

omit [Finite A] in
theorem mem_center_of_central_two
    (hA : ∀ (N : Subgroup A) [N.Normal], IsPGroup 2 (A ⧸ N) → N = ⊤)
    {Z : Subgroup A} [Z.Normal] (hZc : Z ≤ Subgroup.center A) (hZ2 : IsPGroup 2 Z) {x : A}
    (hx : ∀ a : A, ⁅x, a⁆ ∈ Z) : x ∈ Subgroup.center A := by
  let f : A →* Z :=
    { toFun := fun a => ⟨⁅x, a⁆, hx a⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hz : (⁅x, b⁆ : A) ∈ Subgroup.center A := hZc (hx b)
        have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]; group
        have e2 : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
          rw [Subgroup.mem_center_iff.1 hz a]; group
        simp only [Subgroup.coe_mul]
        rw [e, e2] }
  have hquot : IsPGroup 2 (A ⧸ f.ker) := by
    have hrange : IsPGroup 2 f.range := hZ2.to_subgroup f.range
    have : (A ⧸ f.ker) ≃* f.range := QuotientGroup.quotientKerEquivRange f
    exact hrange.of_equiv this.symm
  have hker : f.ker = ⊤ := hA f.ker hquot
  rw [Subgroup.mem_center_iff]
  intro a
  have : f a = 1 := by
    have : a ∈ f.ker := hker ▸ Subgroup.mem_top a
    exact MonoidHom.mem_ker.1 this
  have h1 : ⁅x, a⁆ = 1 := congrArg Subtype.val this
  exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm

omit [Finite A] in
theorem commutator_sup_eq_top {Z : Subgroup A} [Z.Normal]
    (hq : commutator (A ⧸ Z) = ⊤) : commutator A ⊔ Z = ⊤ := by
  have h1 : (commutator A).map (QuotientGroup.mk' Z) = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
    exact hq
  have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' Z) (commutator A)
  rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
  exact h2.symm

theorem isQuasisimple_or_card_three_of_central_two
    (hA : ∀ (N : Subgroup A) [N.Normal], IsPGroup 2 (A ⧸ N) → N = ⊤)
    {Z : Subgroup A} [Z.Normal] (hZc : Z ≤ Subgroup.center A) (hZ2 : IsPGroup 2 Z)
    (hq : CFSG.IsQuasisimple (A ⧸ Z) ∨ Nat.card (A ⧸ Z) = 3) :
    CFSG.IsQuasisimple A ∨ Nat.card A = 3 := by
  rcases hq with ⟨hperf, hsimple, hnc⟩ | h3
  · left
    have hAperf : Group.IsPerfect A := by
      rw [Group.isPerfect_def]
      have hsup := commutator_sup_eq_top (Z := Z) (Group.isPerfect_def.mp hperf)
      exact hA _ (isPGroup_quotient_of_sup_eq_top hZ2 hsup)
    have hcenter : Subgroup.center (A ⧸ Z) = (Subgroup.center A).map (QuotientGroup.mk' Z) := by
      apply le_antisymm
      · intro y hy
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z y
        refine ⟨x, mem_center_of_central_two hA hZc hZ2 fun a => ?_, rfl⟩
        have h1 := Subgroup.mem_center_iff.1 hy (QuotientGroup.mk' Z a)
        have h2 : ⁅(QuotientGroup.mk' Z x), (QuotientGroup.mk' Z a)⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.2 h1.symm
        rw [← map_commutatorElement] at h2
        exact (QuotientGroup.eq_one_iff _).1 h2
      · exact Subgroup.map_center_le_center (QuotientGroup.mk'_surjective Z)
    have hnorm : ((Subgroup.center A).map (QuotientGroup.mk' Z)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)
    let e : A ⧸ Subgroup.center A ≃* (A ⧸ Z) ⧸ Subgroup.center (A ⧸ Z) :=
      (QuotientGroup.quotientQuotientEquivQuotient Z (Subgroup.center A) hZc).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcenter.symm)
    refine ⟨hAperf, (MulEquiv.isSimpleGroup_congr e).2 hsimple, ?_⟩
    obtain ⟨a, b, hab⟩ := hnc
    exact ⟨e.symm a, e.symm b, fun h => hab (by
      have := congrArg e h
      simpa using this)⟩
  · right
    have hcyc : IsCyclic (A ⧸ Z) := by
      have : Fact (Nat.card (A ⧸ Z)).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
      exact isCyclic_of_prime_card h3
    have : IsMulCommutative A :=
      MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z)
        (by rw [QuotientGroup.ker_mk']; exact hZc)
    have h3d : 3 ∣ Nat.card A := by
      rw [← h3]; exact Subgroup.card_quotient_dvd_card Z
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h3d
    set C : Subgroup A := Subgroup.zpowers c with hC
    have hCcard : Nat.card C = 3 := by rw [hC, Nat.card_zpowers, hc]
    obtain ⟨k, hk⟩ := hZ2.exists_card_eq
    have hAcard : Nat.card A = 2 ^ k * 3 := by
      rw [← hk, ← h3, mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    have hq : IsPGroup 2 (A ⧸ C) := by
      refine IsPGroup.of_card (n := k) ?_
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
      rw [hAcard, hCcard] at h1
      omega
    have hCtop : C = ⊤ := hA C hq
    rw [hCtop, Subgroup.card_top] at hCcard
    exact hCcard

end CentralTwo

end L246C127

end CFSG.QuasithinUnique

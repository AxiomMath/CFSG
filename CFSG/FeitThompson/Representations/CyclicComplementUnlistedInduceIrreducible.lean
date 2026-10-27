module

public import CFSG.FeitThompson.Representations.LocalCharacterRowsRestrictIrreducibly
public import CFSG.FeitThompson.Representations.InducedIrreducibleNormOrbitFormula
import CFSG.FeitThompson.Representations.NoInducedIrreducibleFixedOrbitOrder
import CFSG.FeitThompson.Representations.InvariantDetectingCharsQuotientDegree
public import CFSG.FeitThompson.Representations.CoprimePrimeAutFixedConjugacyClasses
public import CFSG.FeitThompson.Representations.BrauerPermutationLemma
public import CFSG.FeitThompson.Representations.NormalCoreCharacterVanishing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open NormalInduction (conjClassFun conjClassFun_apply)

variable {L : Type*} [Group L] {K W₁ W₂ : Subgroup L}
  {σ : classFun ↥(W₁ ⊔ W₂) →ₗ[ℂ] classFun L}

theorem irrAut_conjNormal_eq_self_iff [K.Normal] {θ : ↑(Irr ↥K)} {g : L} :
    irrAut (MulAut.conjNormal (H := K) g) θ = θ ↔ g⁻¹ ∈ inertiaGroup K (θ : ↥K → ℂ) := by
  rw [irrAut_eq_self_iff, mem_inertiaGroup, funext_iff]
  refine forall_congr' fun n => ?_
  rw [conjClassFun_apply, inv_inv]

theorem inertiaGroup_resClassFun_eq_top [K.Normal] {χ : L → ℂ} (hχ : χ ∈ classFun L) :
    inertiaGroup K (resClassFun K χ) = ⊤ :=
  (Subgroup.eq_top_iff' _).2 fun g => mem_inertiaGroup.2 (conjClassFun_resClassFun K g hχ)

theorem exists_prime_orderOf_mem_inertiaGroup [Finite L] [K.Normal] {θ : ↥K → ℂ} {F : Subgroup L}
    (hF : F ≠ ⊥) (hFle : F ≤ inertiaGroup K θ) :
    ∃ (z : L) (q : ℕ), z ∈ F ∧ q.Prime ∧ orderOf z = q ∧ conjClassFun K z θ = θ := by
  have hcard : Nat.card ↥F ≠ 1 := fun hc => hF (Subgroup.card_eq_one.1 hc)
  obtain ⟨q, hq, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥F) q hdvd
  exact ⟨(x : L), q, x.2, hq, by rw [← Subgroup.orderOf_coe] at hx; exact hx,
    mem_inertiaGroup.1 (hFle x.2)⟩

namespace IsPrimeCyclicTIHyp

theorem exists_mem_left_ne_one (h : IsPrimeCyclicTIHyp K W₁ W₂) : ∃ z ∈ W₁, z ≠ 1 := by
  have hne := h.left_ne_bot
  rw [ne_eq, Subgroup.eq_bot_iff_forall] at hne
  push Not at hne
  obtain ⟨z, hz, hz1⟩ := hne
  exact ⟨z, hz, hz1⟩

theorem autFixedSubgroup_conjNormal_eq [K.Normal] (h : IsPrimeCyclicTIHyp K W₁ W₂) {z : L}
    (hz : z ∈ W₁) (hz1 : z ≠ 1) :
    autFixedSubgroup (MulAut.conjNormal (H := K) z) = W₂.subgroupOf K := by
  ext x
  rw [mem_autFixedSubgroup, Subgroup.mem_subgroupOf, ← h.centralizer_eq z hz hz1,
    Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨fun hx => ⟨x.2, ?_⟩, fun hx => Subtype.ext ?_⟩
  · have hval := congrArg (Subtype.val) hx
    rw [MulAut.conjNormal_apply] at hval
    calc (x : L) * z = (z * (x : L) * z⁻¹) * z := by rw [hval]
      _ = z * (x : L) := by group
  · rw [MulAut.conjNormal_apply, ← hx.2]
    group

theorem natCard_fixed_Irr_eq [Finite L] [K.Normal] (h : IsPrimeCyclicTIHyp K W₁ W₂) {z : L} {q : ℕ}
    (hz : z ∈ W₁) (hq : q.Prime) (hord : orderOf z = q) :
    Nat.card {χ : ↑(Irr ↥K) // irrAut (MulAut.conjNormal (H := K) z) χ = χ} = Nat.card ↥W₂ := by
  have hz1 : z ≠ 1 := by
    intro hcon
    rw [hcon, orderOf_one] at hord
    exact hq.one_lt.ne' hord.symm
  have hzW : q ∣ Nat.card ↥W₁ := by
    rw [← hord]
    exact (Subgroup.orderOf_mk z hz) ▸ orderOf_dvd_natCard (⟨z, hz⟩ : ↥W₁)
  have hqK : ¬ q ∣ Nat.card ↥K := fun hcon =>
    (Nat.Prime.not_coprime_iff_dvd.2 ⟨q, hq, hcon, hzW⟩) h.coprime_natCard
  have hbq : (MulAut.conjNormal (H := K) z) ^ q = 1 := by
    rw [← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  have hfix := h.autFixedSubgroup_conjNormal_eq hz hz1
  have hcomm : ∀ x y : ↥(autFixedSubgroup (MulAut.conjNormal (H := K) z)), x * y = y * x := by
    have hc : IsMulCommutative ↥W₂ := h.isCyclic_right.isMulCommutative
    let _ : CommGroup ↥W₂ := IsMulCommutative.instCommGroup
    rw [hfix]
    intro x y
    have e := Subgroup.subgroupOfEquivOfLe h.right_le
    exact e.injective (by rw [map_mul, map_mul, mul_comm])
  rw [natCard_fixed_Irr_eq_natCard_autFixedSubgroup hq hqK hbq hcomm, hfix,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.right_le).toEquiv]

theorem inertiaGroup_eq_of_inf_eq_bot [K.Normal] (h : IsPrimeCyclicTIHyp K W₁ W₂) {θ : ↥K → ℂ}
    (hθ : θ ∈ classFun ↥K) (hbot : W₁ ⊓ inertiaGroup K θ = ⊥) : inertiaGroup K θ = K := by
  refine le_antisymm (fun g hg => ?_) (le_inertiaGroup K hθ)
  obtain ⟨k, hk, w, hw, rfl⟩ := h.exists_decomp g
  have hkI : k ∈ inertiaGroup K θ := le_inertiaGroup K hθ hk
  have hwI : w ∈ inertiaGroup K θ := by
    have hm : k⁻¹ * (k * w) ∈ inertiaGroup K θ := mul_mem (inv_mem hkI) hg
    simpa using hm
  have hw1 : w = 1 := by
    have hm : w ∈ W₁ ⊓ inertiaGroup K θ := Subgroup.mem_inf.2 ⟨hw, hwI⟩
    rw [hbot] at hm
    exact Subgroup.mem_bot.1 hm
  rw [hw1, mul_one]
  exact hk

theorem inertiaGroup_primeTIres_eq_top [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (j : ↑(Irr ↥W₂)) : inertiaGroup K (h.primeTIres σ j) = ⊤ := by
  rw [primeTIres_def]
  exact inertiaGroup_resClassFun_eq_top
    (Irr_subset_classFun (h.primeTIirr_principal_left_mem_Irr hσ j))

theorem conjClassFun_primeTIres [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) (g : L)
    (j : ↑(Irr ↥W₂)) : conjClassFun K g (h.primeTIres σ j) = h.primeTIres σ j :=
  mem_inertiaGroup.1 (by rw [h.inertiaGroup_primeTIres_eq_top hσ j]; exact Subgroup.mem_top g)

theorem exists_primeTIres_eq_of_conjClassFun_eq [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ}
    (hθ : θ ∈ Irr ↥K) {z : L} (hz : z ∈ W₁) (hz1 : z ≠ 1) (hfix : conjClassFun K z θ = θ) :
    ∃ j : ↑(Irr ↥W₂), h.primeTIres σ j = θ := by
  classical
  have hcommW₂ : IsMulCommutative ↥W₂ := h.isCyclic_right.isMulCommutative
  obtain ⟨y, q, hyz, hq, hyord, hyfix⟩ :=
    exists_prime_orderOf_mem_inertiaGroup (θ := θ) (F := Subgroup.zpowers z)
      (by simpa using hz1) (Subgroup.zpowers_le.2 (mem_inertiaGroup.2 hfix))
  have hyW : y ∈ W₁ := (Subgroup.zpowers_le.2 hz) hyz
  set S := {χ : ↑(Irr ↥K) // irrAut (MulAut.conjNormal (H := K) y) χ = χ} with hS
  have hmem : ∀ j : ↑(Irr ↥W₂), irrAut (MulAut.conjNormal (H := K) y)
      ⟨h.primeTIres σ j, h.primeTIres_mem_Irr hσ j⟩ = ⟨h.primeTIres σ j, _⟩ :=
    fun j => irrAut_conjNormal_eq_self_iff.2 (by
      rw [h.inertiaGroup_primeTIres_eq_top hσ j]; exact Subgroup.mem_top _)
  set F : ↑(Irr ↥W₂) → S := fun j => ⟨⟨h.primeTIres σ j, h.primeTIres_mem_Irr hσ j⟩, hmem j⟩
  have hFinj : Function.Injective F := fun j k hjk =>
    h.primeTIres_injective hσ (congrArg (fun s : S => ((s.1 : ↥K → ℂ))) hjk)
  have hcard : Nat.card ↑(Irr ↥W₂) = Nat.card S := by
    rw [hS, h.natCard_fixed_Irr_eq hyW hq hyord, card_Irr_eq_card_of_isMulCommutative]
  have hsurj := ((Nat.bijective_iff_injective_and_card F).2 ⟨hFinj, hcard⟩).2
  obtain ⟨j, hj⟩ := hsurj ⟨⟨θ, hθ⟩,
    irrAut_conjNormal_eq_self_iff.2 (inv_mem (mem_inertiaGroup.2 hyfix))⟩
  exact ⟨j, congrArg (fun s : S => ((s.1 : ↥K → ℂ))) hj⟩

theorem exists_primeTIres_eq_iff [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ}
    (hθ : θ ∈ Irr ↥K) :
    (∃ j : ↑(Irr ↥W₂), h.primeTIres σ j = θ) ↔ ∃ z ∈ W₁, z ≠ 1 ∧ conjClassFun K z θ = θ := by
  refine ⟨fun hex => ?_, fun hex => ?_⟩
  · obtain ⟨j, hj⟩ := hex
    obtain ⟨z, hz, hz1⟩ := h.exists_mem_left_ne_one
    exact ⟨z, hz, hz1, hj ▸ h.conjClassFun_primeTIres hσ z j⟩
  · obtain ⟨z, hz, hz1, hfix⟩ := hex
    exact h.exists_primeTIres_eq_of_conjClassFun_eq hσ hθ hz hz1 hfix

theorem existsUnique_primeTIres_eq [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ}
    (hex : ∃ j : ↑(Irr ↥W₂), h.primeTIres σ j = θ) :
    ∃! j : ↑(Irr ↥W₂), h.primeTIres σ j = θ := by
  obtain ⟨j, hj⟩ := hex
  exact ⟨j, hj, fun k hk => h.primeTIres_injective hσ (hk.trans hj.symm)⟩

theorem inf_inertiaGroup_eq_bot_of_forall_ne [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ}
    (hθ : θ ∈ Irr ↥K) (hne : ∀ j : ↑(Irr ↥W₂), h.primeTIres σ j ≠ θ) :
    W₁ ⊓ inertiaGroup K θ = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_inf] at hz
  by_contra hz1
  rw [Subgroup.mem_bot] at hz1
  obtain ⟨j, hj⟩ := h.exists_primeTIres_eq_of_conjClassFun_eq hσ hθ hz.1 hz1
    (mem_inertiaGroup.1 hz.2)
  exact hne j hj

theorem indClassFun_mem_Irr_of_forall_ne [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ}
    (hθ : θ ∈ Irr ↥K) (hne : ∀ j : ↑(Irr ↥W₂), h.primeTIres σ j ≠ θ) :
    indClassFun K θ ∈ Irr L :=
  (FreeCore.mem_Irr_indClassFun_iff K hθ).2
    (h.inertiaGroup_eq_of_inf_eq_bot (Irr_subset_classFun hθ)
      (h.inf_inertiaGroup_eq_bot_of_forall_ne hσ hθ hne))

theorem isOrthogonal_indClassFun_primeTIirr [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ}
    (hθ : θ ∈ Irr ↥K) (hne : ∀ j : ↑(Irr ↥W₂), h.primeTIres σ j ≠ θ) (i : ↑(Irr ↥W₁))
    (j : ↑(Irr ↥W₂)) : IsOrthogonal (indClassFun K θ) (h.primeTIirr σ i j) := by
  classical
  have : Fintype ↥K := Fintype.ofFinite _
  rw [isOrthogonal_iff, cfInner_indClassFun_eq_cfInner_resClassFun
      (h.primeTIirr_mem_Irr hσ i j) hθ, h.resClassFun_primeTIirr i j,
    cfInner_eq_ite_of_mem_Irr (h.primeTIres_mem_Irr hσ j) hθ, if_neg (hne j)]

theorem cfInner_self_indClassFun_primeTIres [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (j : ↑(Irr ↥W₂)) : cfInner (indClassFun K (h.primeTIres σ j))
      (indClassFun K (h.primeTIres σ j)) = (Nat.card ↥W₁ : ℂ) := by
  have : Fintype ↑(Irr ↥W₁) := Fintype.ofFinite _
  rw [h.indClassFun_primeTIres hσ, h.cfInner_self_primeTIrow hσ]

theorem indClassFun_notMem_Irr_primeTIres [Fintype L] [Fintype ↥(W₁ ⊔ W₂)]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ)
    (j : ↑(Irr ↥W₂)) : indClassFun K (h.primeTIres σ j) ∉ Irr L := by
  intro hcon
  have hnorm : cfInner (indClassFun K (h.primeTIres σ j))
      (indClassFun K (h.primeTIres σ j)) = 1 := by
    rw [cfInner_eq_ite_of_mem_Irr hcon hcon, if_pos rfl]
  rw [h.cfInner_self_indClassFun_primeTIres hσ] at hnorm
  have h1 : 1 < Nat.card ↥W₁ := (Subgroup.one_lt_card_iff_ne_bot W₁).2 h.left_ne_bot
  exact (by omega : Nat.card ↥W₁ ≠ 1) (by exact_mod_cast hnorm)

theorem xor_exists_primeTIres_eq [Fintype L] [Fintype ↥(W₁ ⊔ W₂)] [K.Normal]
    (h : IsPrimeCyclicTIHyp K W₁ W₂) (hσ : IsCyclicTIIsometry (W₁ ⊔ W₂) W₁ W₂ σ) {θ : ↥K → ℂ}
    (hθ : θ ∈ Irr ↥K) :
    Xor (∃! j : ↑(Irr ↥W₂), h.primeTIres σ j = θ)
      (indClassFun K θ ∈ Irr L ∧ ∀ (i : ↑(Irr ↥W₁)) (j : ↑(Irr ↥W₂)),
        IsOrthogonal (indClassFun K θ) (h.primeTIirr σ i j)) := by
  by_cases hex : ∃ j : ↑(Irr ↥W₂), h.primeTIres σ j = θ
  · refine Or.inl ⟨h.existsUnique_primeTIres_eq hσ hex, ?_⟩
    obtain ⟨j, hj⟩ := hex
    exact fun hcon => h.indClassFun_notMem_Irr_primeTIres hσ j (hj ▸ hcon.1)
  · have hne : ∀ j : ↑(Irr ↥W₂), h.primeTIres σ j ≠ θ := fun j hj => hex ⟨j, hj⟩
    exact Or.inr ⟨⟨h.indClassFun_mem_Irr_of_forall_ne hσ hθ hne,
      fun i j => h.isOrthogonal_indClassFun_primeTIirr hσ hθ hne i j⟩,
      fun hcon => hex ⟨hcon.exists.choose, hcon.exists.choose_spec⟩⟩

end IsPrimeCyclicTIHyp

end CFSG.FeitThompson

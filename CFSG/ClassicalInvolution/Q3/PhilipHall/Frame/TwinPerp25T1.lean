module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25T0

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace WUnique

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem isUniqueInvolution_sq (hC : TwinSecCtx X Φ) {J : Subgroup X} (hJ : J ∈ Φ) {y : X}
    (hy : y ∈ J) (ho : orderOf y = 4) : IsUniqueInvolution J (y * y) := by
  obtain ⟨s, hs⟩ := (hC.S.hyp.omega1 J hJ).1
  have h4 : (y * y) * (y * y) = 1 := by
    have h := pow_orderOf_eq_one y
    rw [ho] at h
    calc (y * y) * (y * y) = y ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := h
  have hne : y * y ≠ 1 := by
    intro h
    have h2 : y ^ 2 = 1 := by rw [pow_two]; exact h
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [ho] at h3
    omega
  have hss : y * y = s := (hs.unique (y * y) (J.mul_mem hy hy) h4).resolve_left hne
  rw [hss]
  exact hs

theorem exists_gen (hC : TwinSecCtx X Φ) {U : Subgroup X} (hU : U ∈ USet Φ) :
    ∃ J ∈ Φ, ∃ y ∈ J, orderOf y = 4 ∧ U = Subgroup.zpowers y := by
  obtain ⟨R, -, J, hJ, hRJ, hUR, hcyc, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hC.S.hyp hU
  have hJR : J = R := hRJ.2.2 J le_rfl (hC.two J hJ) hRJ.1
  obtain ⟨e⟩ := hC.q8 J hJ
  have hJ8 : Nat.card ↥J = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hU4 : Nat.card ↥U = 4 := by
    have h1 : Nat.card ↥R = 8 := by rw [← hJR]; exact hJ8
    omega
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hgo : orderOf g = Nat.card ↥U := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgJ : (g : X) ∈ J := hJR ▸ hUR g.2
  refine ⟨J, hJ, g, hgJ, by rw [Subgroup.orderOf_coe, hgo, hU4], le_antisymm ?_ ?_⟩
  · intro u hu
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨u, hu⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  · exact Subgroup.zpowers_le.mpr g.2

theorem eq_one_or_eq_of_mem_zpowers {s t : X} (hs : s * s = 1) (ht : t ∈ Subgroup.zpowers s) :
    t = 1 ∨ t = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have h2 : s ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hs
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul, h2, one_zpow]
  · right
    rw [hn, zpow_add_one, zpow_mul, h2, one_zpow, one_mul]

theorem sq_eq_of_commute (hC : TwinSecCtx X Φ) {J₁ J₂ : Subgroup X} (hJ₁ : J₁ ∈ Φ) (hJ₂ : J₂ ∈ Φ)
    {y₁ y₂ : X} (h₁ : y₁ ∈ J₁) (h₂ : y₂ ∈ J₂) (o₁ : orderOf y₁ = 4) (o₂ : orderOf y₂ = 4)
    (hc : y₁ * y₂ = y₂ * y₁) : y₁ * y₁ = y₂ * y₂ := by
  by_contra hne
  refine hC.nc4 ⟨J₁, hJ₁, y₁, h₁, o₁, J₂, hJ₂, y₂ * y₂, isUniqueInvolution_sq hC hJ₂ h₂ o₂,
    fun h => hne h.symm, ?_⟩
  calc (y₂ * y₂) * y₁ = y₂ * (y₂ * y₁) := by group
    _ = y₂ * (y₁ * y₂) := by rw [hc]
    _ = (y₂ * y₁) * y₂ := by group
    _ = (y₁ * y₂) * y₂ := by rw [hc]
    _ = y₁ * (y₂ * y₂) := by group

theorem exists_nonempty_etaG (hC : TwinSecCtx X Φ) : ∃ η ∈ etaG Φ, η.Nonempty := by
  have hΩ : HypOmegaGen Φ := hC.S.hyp
  obtain ⟨K, hK, -⟩ := hC.twin
  obtain ⟨S, hKS⟩ := (hC.two K hK).exists_le_sylow
  have hKsyl : IsSylow2In K K :=
    ⟨le_rfl, hC.two K hK, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨U₀, hU₀, hU₀K, -⟩ := Sec6Gen.exists_invariant_mem_USet hΩ hK hKsyl (hC.two K hK) le_rfl
    (fun q hq => conjSub_eq_self_of_mem hq)
  obtain ⟨η, hη, hinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  refine ⟨η, ⟨S, hη, hinv⟩, ?_⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h1 := hη.2.2 {U₀}
    (by
      intro U hU
      rw [Set.mem_singleton_iff] at hU
      subst hU
      exact ⟨hU₀, hU₀K.trans hKS⟩)
    (by
      intro U hU U' hU' hUU'
      rw [Set.mem_singleton_iff] at hU hU'
      exact absurd (hU.trans hU'.symm) hUU')
  rw [hne, Set.ncard_singleton, Set.ncard_empty] at h1
  omega

end WUnique

theorem false_of_wUnique {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} (hC : TwinSecCtx X Φ)
    {V : Subgroup X} (hV : WSet Φ = {V}) : False := by
  have hΩ : HypOmegaGen Φ := hC.S.hyp
  have hVW : V ∈ WSet Φ := by rw [hV]; exact Set.mem_singleton V
  obtain ⟨η, hη, U₁, hU₁⟩ := WUnique.exists_nonempty_etaG hC
  have hUSet : ∀ U ∈ η, U ∈ USet Φ := by
    intro U hU
    obtain ⟨S₀, hS₀, -⟩ := hη
    exact (hS₀.1 hU).1
  have hVeq : (⨆ U ∈ η, U) = V := by
    have h : (⨆ U ∈ η, U) ∈ WSet Φ := ⟨η, hη, rfl⟩
    rw [hV] at h
    exact h
  have hleV : ∀ U ∈ η, U ≤ V := fun U hU => by
    rw [← hVeq]
    exact le_iSup₂ (f := fun U (_ : U ∈ η) => U) U hU
  have hnorm : ∀ g : X, conjSub g V = V := by
    intro g
    have h : conjSub g V ∈ WSet Φ := WSet.conj hΩ.conjInvariant hVW g
    rw [hV] at h
    exact h
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := Q3CL.Thompson.commutes_of_mem_WSet hΩ hVW
  obtain ⟨J₁, hJ₁, y₁, hy₁J, hy₁o, hU₁y⟩ := WUnique.exists_gen hC (hUSet U₁ hU₁)
  have hy₁V : y₁ ∈ V := hleV U₁ hU₁ (hU₁y ▸ Subgroup.mem_zpowers y₁)
  have hsInv : IsUniqueInvolution J₁ (y₁ * y₁) := WUnique.isUniqueInvolution_sq hC hJ₁ hy₁J hy₁o
  have hA : ∀ U ∈ η, ∀ u ∈ U, u * u ∈ Subgroup.zpowers (y₁ * y₁) := by
    intro U hU u hu
    obtain ⟨J, hJ, y, hyJ, hyo, hUy⟩ := WUnique.exists_gen hC (hUSet U hU)
    have hyV : y ∈ V := hleV U hU (hUy ▸ Subgroup.mem_zpowers y)
    have hsy : y₁ * y₁ = y * y :=
      WUnique.sq_eq_of_commute hC hJ₁ hJ hy₁J hyJ hy₁o hyo (hcomm y₁ hy₁V y hyV)
    rw [hUy] at hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    have h : y ^ k * y ^ k = (y₁ * y₁) ^ k := by
      rw [hsy, (Commute.refl y).mul_zpow k]
    rw [h]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hB : ∀ v ∈ V, v * v ∈ Subgroup.zpowers (y₁ * y₁) := by
    let H : Subgroup X :=
      { carrier := {v | v ∈ V ∧ v * v ∈ Subgroup.zpowers (y₁ * y₁)}
        mul_mem' := by
          rintro a b ⟨haV, ha⟩ ⟨hbV, hb⟩
          refine ⟨V.mul_mem haV hbV, ?_⟩
          have h : (a * b) * (a * b) = (a * a) * (b * b) := by
            calc (a * b) * (a * b) = a * (b * a) * b := by group
              _ = a * (a * b) * b := by rw [hcomm b hbV a haV]
              _ = (a * a) * (b * b) := by group
          rw [h]
          exact Subgroup.mul_mem _ ha hb
        one_mem' := ⟨V.one_mem, by rw [one_mul]; exact Subgroup.one_mem _⟩
        inv_mem' := by
          rintro a ⟨haV, ha⟩
          refine ⟨V.inv_mem haV, ?_⟩
          have h : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
          rw [h]
          exact Subgroup.inv_mem _ ha }
    have hVH : (⨆ U ∈ η, U) ≤ H :=
      iSup₂_le fun U hU u hu => ⟨hleV U hU hu, hA U hU u hu⟩
    rw [hVeq] at hVH
    exact fun v hv => (hVH hv).2
  have hcentral : ∀ x : X, x * (y₁ * y₁) * x⁻¹ = y₁ * y₁ := by
    intro x
    have h1 : x * y₁ * x⁻¹ ∈ V := by
      have h := conj_mem_conjSub (n := x) hy₁V
      rwa [hnorm x] at h
    have h2 := hB _ h1
    have h3 : (x * y₁ * x⁻¹) * (x * y₁ * x⁻¹) = x * (y₁ * y₁) * x⁻¹ := by group
    rw [h3] at h2
    rcases WUnique.eq_one_or_eq_of_mem_zpowers hsInv.sq h2 with h | h
    · exfalso
      apply hsInv.ne_one
      calc y₁ * y₁ = x⁻¹ * (x * (y₁ * y₁) * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
    · exact h
  refine hC.bad (y₁ * y₁) fun M hM => ?_
  obtain ⟨g, hg⟩ := hC.trans J₁ hJ₁ M hM
  have h := hsInv.conj g
  rw [hg, hcentral g] at h
  exact h

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T

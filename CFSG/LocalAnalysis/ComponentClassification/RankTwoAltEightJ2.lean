module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltEightPerm
public import CFSG.Sporadic.J2

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped Finset

section AltEight

theorem cycleType_of_mul_self_eight {s : Perm (Fin 8)} (h2 : s * s = 1) (h1 : s ≠ 1)
    (hs : sign s = 1) : s.cycleType = {2, 2} ∨ s.cycleType = {2, 2, 2, 2} := by
  have hall : ∀ x ∈ s.cycleType, x = 2 := by
    intro x hx
    have hord : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, h2])
    have h2le := two_le_of_mem_cycleType hx
    have hle := Nat.le_of_dvd (by norm_num) ((dvd_of_mem_cycleType hx).trans hord)
    omega
  have hrep : s.cycleType = Multiset.replicate (Multiset.card s.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hall
  set k := Multiset.card s.cycleType with hk
  have hsum := sum_cycleType_le s
  rw [hrep, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hsign := sign_of_cycleType s
  rw [hs, hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hk0 : k ≠ 0 := by
    intro h0
    apply h1
    rw [← cycleType_eq_zero, hrep, h0, Multiset.replicate_zero]
  have hev : k % 2 = 0 := by
    by_contra hodd
    have hodd' : Odd (k * 2 + k) := Nat.odd_iff.mpr (by omega)
    rw [hodd'.neg_one_pow] at hsign
    exact absurd hsign (by decide)
  rcases (by omega : k = 2 ∨ k = 4) with h | h
  · left
    rw [hrep, h]
    rfl
  · right
    rw [hrep, h]
    rfl

theorem mul_self_iff_cycleType_eight (σ : alternatingGroup (Fin 8)) :
    σ * σ = 1 ∧ σ ≠ 1 ↔
      (σ : Perm (Fin 8)).cycleType = {2, 2} ∨ (σ : Perm (Fin 8)).cycleType = {2, 2, 2, 2} := by
  constructor
  · rintro ⟨h2, h1⟩
    refine cycleType_of_mul_self_eight ?_ (fun h => h1 (Subtype.ext h)) σ.2
    rw [← Subgroup.coe_mul, h2]
    rfl
  · intro h
    have hord : orderOf (σ : Perm (Fin 8)) = 2 := by
      rw [← lcm_cycleType]
      rcases h with h | h <;> rw [h] <;> rfl
    refine ⟨Subtype.ext ?_, fun h1 => ?_⟩
    · rw [Subgroup.coe_mul, ← sq, ← hord, pow_orderOf_eq_one]
      rfl
    · rw [h1] at hord
      simp at hord

theorem thirtyTwo_dvd_card_centralizer_eight {σ : alternatingGroup (Fin 8)} (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) : 32 ∣ Nat.card (centralizer ({σ} : Set (alternatingGroup (Fin 8)))) := by
  have hs2 : (σ : Perm (Fin 8)) * σ = 1 := by
    rw [← Subgroup.coe_mul, h2]
    rfl
  have hs1 : (σ : Perm (Fin 8)) ≠ 1 := fun h => h1 (Subtype.ext h)
  have hC : 64 ∣ Nat.card (centralizer ({(σ : Perm (Fin 8))} : Set (Perm (Fin 8)))) := by
    rw [Perm.nat_card_centralizer, Fintype.card_fin]
    rcases cycleType_of_mul_self_eight hs2 hs1 σ.2 with h | h <;> rw [h] <;> decide
  have h := hC.trans (card_centralizer_dvd_two_mul_card_centralizer σ)
  omega

theorem ncard_involutions_eight :
    {σ : alternatingGroup (Fin 8) | σ * σ = 1 ∧ σ ≠ 1}.ncard = 315 := by
  set F₁ := Finset.univ.filter fun σ : alternatingGroup (Fin 8) =>
    (σ : Perm (Fin 8)).cycleType = {2, 2} with hF₁
  set F₂ := Finset.univ.filter fun σ : alternatingGroup (Fin 8) =>
    (σ : Perm (Fin 8)).cycleType = {2, 2, 2, 2} with hF₂
  have h22 : F₁.card = 210 := by
    rw [hF₁, AlternatingGroup.card_of_cycleType]
    decide
  have h24 : F₂.card = 105 := by
    rw [hF₂, AlternatingGroup.card_of_cycleType]
    decide
  have hset : {σ : alternatingGroup (Fin 8) | σ * σ = 1 ∧ σ ≠ 1} = ↑(F₁ ∪ F₂) := by
    ext σ
    rw [Set.mem_ofPred_eq, mul_self_iff_cycleType_eight, Finset.coe_union, Set.mem_union,
      Finset.mem_coe, Finset.mem_coe, hF₁, hF₂, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
  rw [hset, Set.ncard_coe_finset, Finset.card_union_of_disjoint, h22, h24]
  rw [Finset.disjoint_left]
  intro σ hσ hσ'
  rw [hF₁, Finset.mem_filter] at hσ
  rw [hF₂, Finset.mem_filter, hσ.2] at hσ'
  exact absurd hσ'.2 (by decide)

end AltEight

section J2

open CFSG.ComponentClassification.J2Cover


theorem mem_conjClass_twoA_of_injective {φ : alternatingGroup (Fin 8) →* P}
    (hφ : Function.Injective φ) {σ : alternatingGroup (Fin 8)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ((φ σ : P) : Perm (Fin 315)) ∈ conjClass P permTwoA := by
  set t : Perm (Fin 315) := ((φ σ : P) : Perm (Fin 315)) with htdef
  have htP : t ∈ P := (φ σ).2
  have ht2 : orderOf t = 2 := by
    rw [htdef, orderOf_coe, orderOf_injective φ hφ]
    exact orderOf_eq_prime (by rw [sq, h2]) h1
  obtain ⟨hcov, -, he1, -, -⟩ := inner_classes
  obtain ⟨r, hr, c, hc, htc⟩ := hcov t htP ht2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exfalso
    have hA : permA = c⁻¹ * t * c := by
      rw [htc]
      group
    set ψ₀ : centralizer ({σ} : Set (alternatingGroup (Fin 8))) →* Perm (Fin 315) :=
      (MulAut.conj c⁻¹).toMonoidHom.comp (P.subtype.comp (φ.comp (centralizer _).subtype))
      with hψ₀
    have hψ₀y : ∀ y, ψ₀ y = c⁻¹ * ((φ y : P) : Perm (Fin 315)) * c := fun y => by
      rw [hψ₀, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rfl
    have hmem : ∀ y, ψ₀ y ∈ centralizerIn P permA := by
      intro y
      rw [hψ₀y]
      refine mem_centralizerIn.mpr ⟨P.mul_mem (P.mul_mem (P.inv_mem hc) (φ y).2) hc, ?_⟩
      have hy : (y : alternatingGroup (Fin 8)) * σ = σ * y :=
        mem_centralizer_singleton_iff.mp y.2
      have hyt : ((φ y : P) : Perm (Fin 315)) * t = t * (φ y : P) := by
        rw [htdef, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hy]
      rw [hA]
      calc c⁻¹ * ((φ y : P) : Perm (Fin 315)) * c * (c⁻¹ * t * c) =
            c⁻¹ * (((φ y : P) : Perm (Fin 315)) * t) * c := by group
        _ = c⁻¹ * (t * (φ y : P)) * c := by rw [hyt]
        _ = c⁻¹ * t * c * (c⁻¹ * ((φ y : P) : Perm (Fin 315)) * c) := by group
    set ψ := ψ₀.codRestrict (centralizerIn P permA) hmem with hψdef
    have hψ : Function.Injective ψ := by
      intro y z hyz
      have h : ψ₀ y = ψ₀ z := congrArg Subtype.val hyz
      rw [hψ₀y, hψ₀y, mul_left_inj, mul_right_inj] at h
      exact Subtype.ext (hφ (Subtype.ext h))
    have hdvd := Subgroup.card_dvd_of_injective ψ hψ
    rw [he1, cent2B_facts.2.1] at hdvd
    have h32 := (thirtyTwo_dvd_card_centralizer_eight h2 h1).trans hdvd
    norm_num at h32
  · exact ⟨c, hc, htc⟩

theorem not_injective_alt8_P (φ : alternatingGroup (Fin 8) →* P) : ¬ Function.Injective φ := by
  intro hφ
  have := isSimpleGroup_P
  set f : alternatingGroup (Fin 8) → Perm (Fin 315) := fun σ => ((φ σ : P) : Perm (Fin 315))
    with hfdef
  have hf : Function.Injective f := fun a b h => hφ (Subtype.ext h)
  set I : Set (alternatingGroup (Fin 8)) := {σ | σ * σ = 1 ∧ σ ≠ 1} with hIdef
  set S := conjClass P permTwoA with hSdef
  have hIS : f '' I ⊆ S := by
    rintro _ ⟨σ, ⟨h2, h1⟩, rfl⟩
    exact mem_conjClass_twoA_of_injective hφ h2 h1
  have hcardS : S.ncard = 315 := inner_classes.2.2.2.1
  have hcardI : (f '' I).ncard = 315 := by
    rw [Set.ncard_image_of_injective _ hf, hIdef, ncard_involutions_eight]
  have hSI : S ⊆ f '' I :=
    (Set.eq_of_subset_of_ncard_le hIS (by rw [hcardS, hcardI])
      (conjClass_finite P permTwoA)).symm.subset
  set z : P := ⟨permTwoA, permTwoA_mem⟩ with hzdef
  have hN : normalClosure ({z} : Set P) ≤ φ.range := by
    rw [normalClosure, closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, hc⟩ := isConj_iff.mp hax
    have hxS : (x : Perm (Fin 315)) ∈ S :=
      ⟨c, c.2, by rw [← hc, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]⟩
    obtain ⟨σ, -, hσ⟩ := hSI hxS
    exact ⟨σ, Subtype.ext hσ⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (normalClosure ({z} : Set P)) with h | h
  · have hz : z ∈ normalClosure ({z} : Set P) := subset_normalClosure (Set.mem_singleton z)
    rw [h, mem_bot] at hz
    have h1 : permTwoA = 1 := congrArg Subtype.val hz
    have h2 := orderOf_permTwoA
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · rw [h, top_le_iff] at hN
    have hcard := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    rw [hN, card_top, card_P, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin] at hcard
    norm_num [Nat.factorial] at hcard

theorem not_injective_alt8_J2 (φ : alternatingGroup (Fin 8) →* NativeSporadic.J2) :
    ¬ Function.Injective φ := by
  intro hφ
  refine not_injective_alt8_P (nativeEquivP.toMonoidHom.comp φ) fun a b h => hφ ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  exact nativeEquivP.injective h

end J2

theorem not_injective_mulAut_of_card {Γ X : Type*} [Group Γ] [Finite Γ] [IsSimpleGroup Γ]
    [Group X] [Finite X] (hΓ : 2 < Nat.card Γ) (hZ : center X = ⊥)
    (hcard : Nat.card (MulAut X) = 2 * Nat.card X) (h : ∀ ψ : Γ →* X, ¬ Function.Injective ψ)
    (φ : Γ →* MulAut X) : ¬ Function.Injective φ := by
  intro hφ
  have hconj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [mem_bot, ← mem_bot (G := X), ← hZ, mem_center_iff]
    intro y
    have h1 := congrArg (fun α : MulAut X => α y) hx
    change x * y * x⁻¹ = y at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have hfin : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => (α : X → X)) DFunLike.coe_injective
  have hinner : Nat.card (inner X) = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv).symm
  have hindex : (inner X).index = 2 := by
    have h1 := (inner X).card_mul_index
    rw [hinner, hcard] at h1
    have hpos : 0 < Nat.card X := Nat.card_pos
    have h2 : Nat.card X * (inner X).index = Nat.card X * 2 := by rw [h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  set Q := (inner X).comap φ with hQdef
  have hQidx : Q.index ∣ 2 := by
    rw [hQdef, index_comap, ← hindex]
    exact relIndex_dvd_index_of_normal _ _
  have hQ : Q = ⊤ := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hQidx with h1 | h2
    · exact index_eq_one.mp h1
    · exfalso
      have : Q.Normal := normal_of_index_eq_two h2
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with hb | ht
      · rw [hb, index_bot] at h2
        omega
      · rw [ht, index_top] at h2
        omega
  have hmem : ∀ g, φ g ∈ inner X := fun g => by
    have hg : g ∈ Q := hQ ▸ mem_top g
    exact hg
  let e : X ≃* inner X := MonoidHom.ofInjective hconj
  apply h (e.symm.toMonoidHom.comp (φ.codRestrict (inner X) hmem))
  intro g g' hgg'
  apply hφ
  have h1 := congrArg (fun x => (e x : MulAut X)) hgg'
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, MonoidHom.codRestrict_apply] at h1
  exact h1

theorem not_injective_alt8_mulAut_J2
    (φ : alternatingGroup (Fin 8) →* MulAut NativeSporadic.J2) :
    ¬ Function.Injective φ := by
  have : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hfin : Finite NativeSporadic.J2 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
  have hZ : center NativeSporadic.J2 = ⊥ := by
    rw [← center_map_equiv J2Cover.nativeEquivP.symm, J2Cover.center_P, Subgroup.map_bot]
  refine not_injective_mulAut_of_card ?_ hZ J2Cover.j2_mulAut_card not_injective_alt8_J2 φ
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem not_injective_alt8_mulAut_M12
    (φ : alternatingGroup (Fin 8) →* MulAut NativeSporadic.M12) :
    ¬ Function.Injective φ := by
  intro hφ
  have h := Subgroup.card_dvd_of_injective φ hφ
  rw [M12Cover.card_mulAut, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin] at h
  norm_num [Nat.factorial] at h

end CFSG.ComponentClassification.RankTwoAlt

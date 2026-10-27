module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Cent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.F23L63Sylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44Golay
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44ModelPerm
public import CFSG.Sporadic.Fi23.InvCoverBase
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.EvenSporadicStandard.Solomon78.F23L63

open Subgroup CFSG.Sporadic.Fi23 CFSG.EvenSporadicStandard.TwoFi22
open CFSG.EvenSporadicStandard.TwoFi22.FrameJ CFSG.EvenSporadicStandard.TwoFi22.DS81
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Gen CFSG.EvenSporadicStandard.Wong77.Module
open CFSG.Blueprint.NativeSporadic (Carrier)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option linter.unusedSectionVars false

@[expose] def IsPermN {J : Type} [Group J] (p : Fin 23 → J) (n : J) (σ : Equiv.Perm (Fin 23)) :
    Prop :=
  ∀ i, n * p i * n⁻¹ = p (σ i)

theorem IsPermN.unique {J : Type} [Group J] {p : Fin 23 → J} (hp : Function.Injective p) {n : J}
    {σ τ : Equiv.Perm (Fin 23)} (h₁ : IsPermN p n σ) (h₂ : IsPermN p n τ) : σ = τ :=
  Equiv.ext fun i => hp ((h₁ i).symm.trans (h₂ i))

theorem IsPermN.one {J : Type} [Group J] (p : Fin 23 → J) : IsPermN p 1 1 := fun i => by simp

theorem IsPermN.mul {J : Type} [Group J] {p : Fin 23 → J} {n m : J} {σ τ : Equiv.Perm (Fin 23)}
    (hn : IsPermN p n σ) (hm : IsPermN p m τ) : IsPermN p (n * m) (σ * τ) := fun i => by
  have h : n * m * p i * (n * m)⁻¹ = n * (m * p i * m⁻¹) * n⁻¹ := by group
  rw [h, hm i, hn (τ i)]
  rfl

section Perm


theorem exists_fjPt_conj {n : J} (hn : n ∈ normalizer ((frameE : Subgroup J) : Set J))
    (i : Fin 23) : ∃ j, n * fjPt i * n⁻¹ = fjPt j := by
  have h1 : n * fjPt i * n⁻¹ ∈ (frameE : Subgroup J) :=
    (Subgroup.mem_normalizer_iff.1 hn _).1 (fjPt_mem_frameE i)
  have h2 : n * fjPt i * n⁻¹ ∈ D23 := conj_mem_D23 n _ (fjPt_mem i)
  obtain ⟨j, hj⟩ := mem_frameE_and_D23_iff.1 ⟨h1, h2⟩
  exact ⟨j, hj.symm⟩

theorem exists_isPermN {n : J} (hn : n ∈ normalizer ((frameE : Subgroup J) : Set J)) :
    ∃ σ : Equiv.Perm (Fin 23), IsPermN fjPt n σ := by
  choose f hf using exists_fjPt_conj hn
  have hinj : Function.Injective f := fun i j hij => by
    apply fjPt_injective
    have h : n * fjPt i * n⁻¹ = n * fjPt j * n⁻¹ := by rw [hf, hf, hij]
    exact mul_left_cancel (mul_right_cancel h)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), fun i => hf i⟩

@[expose] noncomputable def rhoN :
    normalizer ((frameE : Subgroup J) : Set J) →* Equiv.Perm (Fin 23) where
  toFun n := Classical.choose (exists_isPermN n.2)
  map_one' := IsPermN.unique fjPt_injective (Classical.choose_spec (exists_isPermN
    (one_mem (normalizer ((frameE : Subgroup J) : Set J))))) (IsPermN.one fjPt)
  map_mul' n m := IsPermN.unique fjPt_injective (Classical.choose_spec (exists_isPermN (n * m).2))
    (IsPermN.mul (Classical.choose_spec (exists_isPermN n.2))
      (Classical.choose_spec (exists_isPermN m.2)))

theorem rhoN_spec (n : normalizer ((frameE : Subgroup J) : Set J)) :
    IsPermN fjPt (n : J) (rhoN n) :=
  Classical.choose_spec (exists_isPermN n.2)

theorem rhoN_eq {n : normalizer ((frameE : Subgroup J) : Set J)} {σ : Equiv.Perm (Fin 23)}
    (h : IsPermN fjPt (n : J) σ) : rhoN n = σ :=
  IsPermN.unique fjPt_injective (rhoN_spec n) h

theorem rhoN_eq_one_iff {n : normalizer ((frameE : Subgroup J) : Set J)} :
    rhoN n = 1 ↔ ∀ x ∈ (frameE : Subgroup J), (n : J) * x = x * n := by
  constructor
  · intro h x hx
    obtain ⟨w, rfl⟩ := hx
    have h1 := conj_fjHom (n := (n : J)) (σ := 1) (fun i => by
      have := rhoN_spec n i
      rwa [h] at this) w
    have h2 : permW 1 w = w := rfl
    rw [h2] at h1
    calc (n : J) * fjHom w = ((n : J) * fjHom w * (n : J)⁻¹) * n := by group
      _ = fjHom w * n := by rw [h1]
  · intro h
    refine rhoN_eq fun i => ?_
    have := h (fjPt i) (fjPt_mem_frameE i)
    rw [mul_inv_eq_iff_eq_mul]
    exact this

theorem ker_rhoN : (rhoN : normalizer ((frameE : Subgroup J) : Set J) →* Equiv.Perm (Fin 23)).ker =
    (frameE : Subgroup J).subgroupOf (normalizer ((frameE : Subgroup J) : Set J)) := by
  ext n
  rw [MonoidHom.mem_ker, rhoN_eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact centralizer_frameE_le h
  · intro hn x hx
    exact frameE_comm _ hn _ hx

theorem rhoN_mem_permStab (n : normalizer ((frameE : Subgroup J) : Set J)) :
    rhoN n ∈ permStab golayCode := by
  refine FrameCd.mem_permStab_of_evC fun s => ?_
  have h := conj_ev (rhoN_spec n) s
  have key : ∀ t, evC t = 1 ↔ ev t = 1 := fun t => by
    rw [Subtype.ext_iff, evC_val, OneMemClass.coe_one]
  rw [key, key, ← h, conj_eq_one_iff]

end Perm

theorem mem_normalizer_of_forall_conj_mem {G : Type} [Group G] [Finite G] {H : Subgroup G} {n : G}
    (h : ∀ x ∈ H, n * x * n⁻¹ ∈ H) : n ∈ normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  let f : H → H := fun y => ⟨n * y * n⁻¹, h y y.2⟩
  have hf : Function.Injective f := fun y z hyz => by
    have h1 : n * (y : G) * n⁻¹ = n * z * n⁻¹ := congrArg Subtype.val hyz
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hf ⟨n * x * n⁻¹, hx⟩
  have h1 : n * (y : G) * n⁻¹ = n * x * n⁻¹ := congrArg Subtype.val hy
  have : (y : G) = x := mul_left_cancel (mul_right_cancel h1)
  exact this ▸ y.2

section Order


theorem card_ker_permHom_le : Nat.card (FrameCd.permHom :
    normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23)).ker ≤ 2 ^ 11 := by
  rw [← E0_card]
  have hmem : ∀ k : (FrameCd.permHom :
      normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23)).ker, (k.1 : ↥Cd) ∈ E0 := fun k => by
    refine centralizer_E0_le fun e he => ?_
    have hp : IsPerm (k.1 : ↥Cd) 1 := by
      have := FrameCd.isPerm_permOf k.1
      rwa [show FrameCd.permOf k.1 = 1 from MonoidHom.mem_ker.1 k.2] at this
    have := FrameCd.conj_eq_of_isPerm_one hp he
    calc (k.1 : ↥Cd) * e = ((k.1 : ↥Cd) * e * (k.1 : ↥Cd)⁻¹) * k.1 := by group
      _ = e * k.1 := by rw [this]
  refine Nat.card_le_card_of_injective (fun k => (⟨(k.1 : ↥Cd), hmem k⟩ : E0)) ?_
  intro k k' h
  exact Subtype.ext (Subtype.ext (congrArg (fun x : E0 => (x : ↥Cd)) h))

theorem card_range_permHom_ge : 443520 ≤ Nat.card (FrameCd.permHom :
    normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23)).range := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (FrameCd.permHom :
    normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange FrameCd.permHom).toEquiv,
    E0_card_normalizer] at h1
  have h3 : 443520 * 2 ^ 11 ≤ Nat.card (FrameCd.permHom :
      normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23)).range * 2 ^ 11 :=
    calc 443520 * 2 ^ 11 = 2 ^ 11 * 443520 := mul_comm _ _
      _ = _ := h1
      _ ≤ _ := Nat.mul_le_mul_left _ card_ker_permHom_le
  exact Nat.le_of_mul_le_mul_right h3 (by norm_num)

theorem mem_normalizer_frameE_of_mem {n : ↥Cd} (hn : n ∈ normalizer (E0 : Set ↥Cd)) :
    (n : J) ∈ normalizer ((frameE : Subgroup J) : Set J) := by
  have key : ∀ x ∈ (frameE : Subgroup J), (n : J) * x * (n : J)⁻¹ ∈ (frameE : Subgroup J) := by
    intro x hx
    have hxE : (⟨x, frameE_le_Cd hx⟩ : ↥Cd) ∈ E0 := Subgroup.mem_subgroupOf.2 hx
    have h1 := (Subgroup.mem_normalizer_iff.1 hn _).1 hxE
    rw [E0, Subgroup.mem_subgroupOf] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact h1
  exact mem_normalizer_of_forall_conj_mem key

theorem permHom_range_le : (FrameCd.permHom :
    normalizer (E0 : Set ↥Cd) →* Equiv.Perm (Fin 23)).range ≤
      rhoN.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 23)) (0 : Fin 23) := by
  rintro _ ⟨n, rfl⟩
  refine Subgroup.mem_inf.2 ⟨⟨⟨(n : ↥Cd), mem_normalizer_frameE_of_mem n.2⟩,
    rhoN_eq (FrameCd.isPerm_permOf n)⟩, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  exact (FrameCd.isPerm_permOf n).zero

end Order

section Main


theorem orbit_rhoN_zero : (MulAction.orbit (rhoN : normalizer ((frameE : Subgroup J) : Set J) →*
    Equiv.Perm (Fin 23)).range (0 : Fin 23)).ncard = 23 := by
  have h : MulAction.orbit (rhoN : normalizer ((frameE : Subgroup J) : Set J) →*
      Equiv.Perm (Fin 23)).range (0 : Fin 23) = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    obtain ⟨n, hn, hnj⟩ := exists_mem_normalizer_frameE (fjPt_mem_frameE 0) (fjPt_mem 0)
      (fjPt_mem_frameE j) (fjPt_mem j)
    refine ⟨⟨rhoN ⟨n, hn⟩, ⟨_, rfl⟩⟩, ?_⟩
    exact fjPt_injective ((rhoN_spec ⟨n, hn⟩ 0).symm.trans hnj)
  rw [h, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_range_rhoN_ge : 23 * 443520 ≤ Nat.card (rhoN :
    normalizer ((frameE : Subgroup J) : Set J) →* Equiv.Perm (Fin 23)).range := by
  have h := natCard_eq_ncard_orbit_mul (rhoN : normalizer ((frameE : Subgroup J) : Set J) →*
    Equiv.Perm (Fin 23)).range (0 : Fin 23)
  rw [orbit_rhoN_zero] at h
  have h2 := card_range_permHom_ge.trans (Subgroup.card_le_of_le permHom_range_le)
  rw [h]
  exact Nat.mul_le_mul_left 23 h2

theorem card_permStab_golay_le : Nat.card (permStab golayCode) ≤ 23 * 443520 := by
  have h := card_le_mul_card_inf_stabilizer (permStab golayCode) (0 : Fin 23) Finset.univ
    (fun g _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_left 23 card_permStab_golay_zero_le)

theorem range_rhoN_eq : (rhoN : normalizer ((frameE : Subgroup J) : Set J) →*
    Equiv.Perm (Fin 23)).range = CFSG.Blueprint.NativeSporadic.M23 := by
  have hle : (rhoN : normalizer ((frameE : Subgroup J) : Set J) →*
      Equiv.Perm (Fin 23)).range ≤ permStab golayCode := by
    rintro _ ⟨n, rfl⟩
    exact rhoN_mem_permStab n
  have h1 := Subgroup.eq_of_le_of_card_ge hle (card_permStab_golay_le.trans card_range_rhoN_ge)
  have h2 : CFSG.Blueprint.NativeSporadic.M23 = permStab golayCode :=
    Subgroup.eq_of_le_of_card_ge M23_le_permStab_golayCode
      (by rw [CFSG.Sporadic.Schreier.m23_card]; exact card_permStab_golay_le)
  exact h1.trans h2.symm

theorem frame_quotient_m23 :
    ∃ _hN : ((frameE : Subgroup J).subgroupOf
        (normalizer ((frameE : Subgroup J) : Set J))).Normal,
      Nonempty ((normalizer ((frameE : Subgroup J) : Set J)) ⧸
        (frameE : Subgroup J).subgroupOf (normalizer ((frameE : Subgroup J) : Set J)) ≃*
          Carrier .M23) := by
  have hN : ((frameE : Subgroup J).subgroupOf
      (normalizer ((frameE : Subgroup J) : Set J))).Normal := ker_rhoN ▸ MonoidHom.normal_ker rhoN
  refine ⟨hN, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq ker_rhoN.symm).trans
    ((QuotientGroup.quotientKerEquivRange rhoN).trans (MulEquiv.subgroupCongr range_rhoN_eq))

end Main

end CFSG.EvenSporadicStandard.Solomon78.F23L63

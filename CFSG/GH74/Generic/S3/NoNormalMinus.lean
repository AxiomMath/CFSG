module

public import CFSG.GH74.Generic.S3.Nbhd
public import CFSG.GH74.Generic.S3.L3Sylow
public import CFSG.GH74.KGroups.L3EpsNoNormalMinus

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem
  mem_centralizer_of_normalizerAct_eq_one)
open CFSG.GH74.KGroups.L3Eps (l3eps_no_normal_minus conj_injective_model_lin equivMapOfInjOn)

theorem injOn_map_center {L : Type} [Group L] [Finite L] (Q : Sylow 2 L)
    (hodd : Odd (Nat.card (center L))) :
    Set.InjOn (QuotientGroup.mk' (center L)) (Q : Subgroup L) := by
  intro a ha b hb hab
  have h2 : a⁻¹ * b ∈ center L := QuotientGroup.eq.1 hab
  have h3 : a⁻¹ * b ∈ (Q : Subgroup L) := Q.mul_mem (Q.inv_mem ha) hb
  exact inv_mul_eq_one.1 (eq_one_of_mem_pGroup_of_mem_center_odd Q.isPGroup' hodd h3 h2)

theorem b_L3_noNormalMinus : B_L3_noNormalMinus := by
  intro G _ _ t t' p f ⟨ht, ht'⟩ hp hp2 h5 L hLq hodd hmod H S hLH hHN hS M hMS hMn hMC
    G' _ _ L' R' hL'q hodd' hmod' hR' ⟨e⟩
  subst ht ht'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLperf : Group.IsPerfect ↥L := hLq.1
  set π : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L) with hπ
  have hX : StatedClassicalModel (↥L ⧸ center ↥L) .PSL 3 p f := stated_of_lieModel_PSL hmod
  have hX' : StatedClassicalModel (↥L' ⧸ center ↥L') .PSU 3 p f := stated_of_lieModel_PSU hmod'
  have hSH : S ≤ H := hS.le
  have hSN : S ≤ normalizer (L : Set G) := hSH.trans hHN
  have hS2 : IsPGroup 2 ↥S := hS.isPGroup
  let η : ↥S →* MulAut (↥L ⧸ center ↥L) := (normalizerAct L).comp (Subgroup.inclusion hSN)
  obtain ⟨Q, hQ⟩ := hS.inf_of_le_normalizer hLH hHN
  have hQS : ∀ l : ↥L, l ∈ (Q : Subgroup ↥L) → (l : G) ∈ S := by
    intro l hl
    have : (l : G) ∈ (Q : Subgroup ↥L).map L.subtype := ⟨l, hl, rfl⟩
    rw [hQ] at this
    exact this.1
  obtain ⟨hP2, hPmax⟩ := isMax_map_center Q hodd
  set P : Subgroup (↥L ⧸ center ↥L) := (Q : Subgroup ↥L).map π with hP
  set A : Subgroup (MulAut (↥L ⧸ center ↥L)) := η.range with hA
  have hA2 : IsPGroup 2 ↥A := IsPGroup.of_surjective hS2 η.rangeRestrict η.rangeRestrict_surjective
  have hconj : ∀ (l : ↥L) (hl : l ∈ (Q : Subgroup ↥L)),
      MulAut.conj (π l) = η ⟨(l : G), hQS l hl⟩ := by
    intro l hl
    exact (normalizerAct_of_mem L l.2).symm
  have hconjA : ∀ y ∈ P, MulAut.conj y ∈ A := by
    rintro _ ⟨l, hl, rfl⟩
    exact ⟨⟨(l : G), hQS l hl⟩, (hconj l hl).symm⟩
  have hAP : A ⊓ ComponentClassification.OuterAutomorphisms.inner (↥L ⧸ center ↥L) =
      P.map (MulAut.conj : (↥L ⧸ center ↥L) →* MulAut (↥L ⧸ center ↥L)) := by
    apply le_antisymm
    · rintro α ⟨hαA, hαI⟩
      obtain ⟨x, rfl⟩ := hαI
      have hinj := conj_injective_model_lin hX
      have hPt2 : IsPGroup 2 ↥(A.comap (MulAut.conj : (↥L ⧸ center ↥L) →* _)) :=
        hA2.comap_of_injective _ hinj
      have hPle : P ≤ A.comap (MulAut.conj : (↥L ⧸ center ↥L) →* _) := fun y hy => hconjA y hy
      have := hPmax _ hPt2 hPle (show x ∈ A.comap (MulAut.conj : (↥L ⧸ center ↥L) →* _) from hαA)
      exact ⟨x, this, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨hconjA y hy, ⟨y, rfl⟩⟩
  set Mbar : Subgroup (MulAut (↥L ⧸ center ↥L)) := (M.subgroupOf S).map η with hMbar
  have hMbarA : Mbar ≤ A := Subgroup.map_le_range η _
  have hMnA : ∀ a ∈ A, ∀ n ∈ Mbar, a * n * a⁻¹ ∈ Mbar := by
    rintro _ ⟨s, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨s * m * s⁻¹, hMn.conj_mem m hm s, ?_⟩
    simp only [map_mul, map_inv]
  have hinjM : Set.InjOn η (M.subgroupOf S : Set ↥S) := by
    intro a ha b hb hab
    have h1 : η (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥S) : G) ∈ centralizer (L : Set G) :=
      mem_centralizer_of_normalizerAct_eq_one L (a := Subgroup.inclusion hSN (a * b⁻¹)) h1
    have h3 : ((a * b⁻¹ : ↥S) : G) ∈ M := by
      have := (M.subgroupOf S).mul_mem ha ((M.subgroupOf S).inv_mem hb)
      exact this
    have h4 : ((a * b⁻¹ : ↥S) : G) ∈ M ⊓ centralizer (L : Set G) := ⟨h3, h2⟩
    rw [hMC, Subgroup.mem_bot] at h4
    have : (a * b⁻¹ : ↥S) = 1 := Subtype.ext h4
    exact mul_inv_eq_one.1 this
  obtain ⟨Q', hQ'⟩ := hR'
  obtain ⟨hR2, hRmax⟩ := isMax_map_center Q' hodd'
  set π' : ↥L' →* ↥L' ⧸ center ↥L' := QuotientGroup.mk' (center ↥L') with hπ'
  let e₁ : ↥Mbar ≃* ↥(M.subgroupOf S) := (equivMapOfInjOn η (M.subgroupOf S) hinjM).symm
  let e₂ : ↥(M.subgroupOf S) ≃* ↥M := Subgroup.subgroupOfEquivOfLe hMS
  let e₄ : ↥R' ≃* ↥(Q' : Subgroup ↥L') :=
    (MulEquiv.subgroupCongr hQ'.symm).trans
      ((Q' : Subgroup ↥L').equivMapOfInjective L'.subtype L'.subtype_injective).symm
  let e₅ : ↥(Q' : Subgroup ↥L') ≃* ↥((Q' : Subgroup ↥L').map π') :=
    equivMapOfInjOn π' (Q' : Subgroup ↥L') (injOn_map_center Q' hodd')
  exact l3eps_no_normal_minus hp2 h5 hX hX' hP2 hPmax A hA2 hAP Mbar hMbarA hMnA hR2 hRmax
    (((e₁.trans e₂).trans e).trans (e₄.trans e₅))

end CFSG.GH74.Generic.S3

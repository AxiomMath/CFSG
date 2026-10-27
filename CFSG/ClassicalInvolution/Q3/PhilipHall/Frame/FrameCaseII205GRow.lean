module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameCaseII205HComp
public import CFSG.ClassicalInvolution.Q3.TL4OddBasic
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf49G23Row
import CFSG.ClassicalInvolution.Q3.Q3CHHyp51

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

section Model


theorem center_eq_bot_of_lieModel_g2 {X : Type} [Group X] {p f : ℕ}
    (hm : CFSG.Blueprint.LieModel X .G2 0 p f) : Subgroup.center X = ⊥ := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm.chevalleyExceptionalModel (by decide)
  let e' : X ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K))).trans
      QuotientGroup.quotientBot)
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hx' : e' x ∈ Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e'.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .G2) (K := K),
    Subgroup.mem_bot] at hx'
  exact e'.injective (hx'.trans (map_one e').symm)

theorem isSimpleGroup_of_lieModel_g2 {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hm : CFSG.Blueprint.LieModel X .G2 0 p f) : IsSimpleGroup X := by
  have hq := (lieModel_g2_facts hp2 hm).1
  have hZ := center_eq_bot_of_lieModel_g2 hm
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup_congr.mp hq.2.1

end Model

section Simple

theorem exists_noncomm_of_center_eq_bot {X : Type} [Group X] [IsSimpleGroup X]
    (hZ : Subgroup.center X = ⊥) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  have hxc : x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun g => hcon g x
  rw [hZ, Subgroup.mem_bot] at hxc
  exact hx hxc

end Simple

section Components

theorem component_map_eq_top {H S : Type} [Group H] [Finite H] [Group S] [Finite S]
    [IsSimpleGroup S] (F : H →* S) (hF : Function.Surjective F) {L : Subgroup H}
    (hL : CFSG.IsComponent L) (hK : Odd (Nat.card F.ker)) : L.map F = ⊤ := by
  haveI : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
  haveI : Subsingleton (S ⧸ (⊤ : Subgroup S)) := QuotientGroup.subsingleton_quotient_top
  haveI : Group.IsSolvable (S ⧸ (⊤ : Subgroup S)) := inferInstance
  exact component_map_eq F hF hL hK (N := ⊤)

theorem autOddFreeInner_of_surj_simple {L Q : Type} [Group L] [Finite L] [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hLq : CFSG.IsQuasisimple L) (ψ : L →* Q)
    (hψ : Function.Surjective ψ) (hnab : ∃ a b : Q, a * b ≠ b * a)
    (hAO : Q3NM.AutOddFreeInner Q) : Q3NM.AutOddFreeInner L := by
  have hker_ne : ψ.ker ≠ ⊤ := by
    intro htop
    obtain ⟨a, b, hab⟩ := hnab
    obtain ⟨x, rfl⟩ := hψ a
    obtain ⟨y, rfl⟩ := hψ b
    have hx : x ∈ ψ.ker := htop ▸ Subgroup.mem_top x
    have hy : y ∈ ψ.ker := htop ▸ Subgroup.mem_top y
    exact hab (by rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy])
  have hker_le : ψ.ker ≤ Subgroup.center L :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hLq ψ.normal_ker).resolve_left hker_ne
  have hcen : Subgroup.center L ≤ ψ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzQ : ψ z ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := hψ q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    have hc : Subgroup.center Q = ⊥ := center_eq_bot_of_nonabelian' hnab
    rw [hc, Subgroup.mem_bot] at hzQ
    exact hzQ
  have hkereq : ψ.ker = Subgroup.center L := le_antisymm hker_le hcen
  let e : L ⧸ Subgroup.center L ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hkereq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  haveI : Group.IsPerfect L := hLq.1
  have hQ' : Q3NM.AutOddFreeInner (L ⧸ Subgroup.center L) :=
    Q3CH.autOddFreeInner_of_mulEquiv e.symm hAO
  exact Q3NM.autOddFreeInner_of_centralQuotient hQ'

end Components

section Block

theorem g23_block {Z : Type} [Group Z] [Finite Z] {T : Subgroup Z} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (F : ↥T →* Q) (hFs : Function.Surjective F) (hK : Odd (Nat.card F.ker))
    (hnab : ∃ a b : Q, a * b ≠ b * a) (hAO : Q3NM.AutOddFreeInner Q) {ζ : Z}
    (hmoved : ∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) → L ≤ T) :
    (∀ L₁ L₂ : Subgroup Z, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, ζ * y ≠ y * ζ) → (∃ y ∈ L₂, ζ * y ≠ y * ζ) → L₁ = L₂) ∧
    ∀ L : Subgroup Z, CFSG.IsComponent L → (∃ y ∈ L, ζ * y ≠ y * ζ) →
      Q3NM.AutOddFreeInner ↥L ∧ ∀ y ∈ T, ∃ l ∈ L, ∀ w ∈ L, y * w * y⁻¹ = l * w * l⁻¹ := by
  refine ⟨fun L₁ L₂ h₁ h₂ m₁ m₂ => ?_, fun L hL hm => ?_⟩
  · have hT₁ := hmoved L₁ h₁ m₁
    have hT₂ := hmoved L₂ h₂ m₂
    have c₁ := CFSG.LocalCores.component_overgroup h₁ hT₁
    have c₂ := CFSG.LocalCores.component_overgroup h₂ hT₂
    have e : L₁.subgroupOf T = L₂.subgroupOf T := by
      rcases CFSG.LocalCores.distinct_components_commute c₁ c₂ with h | hc
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        have e1 := component_map_eq_top F hFs c₁ hK
        have e2 := component_map_eq_top F hFs c₂ hK
        have ha : a ∈ (L₁.subgroupOf T).map F := by rw [e1]; exact Subgroup.mem_top a
        have hb : b ∈ (L₂.subgroupOf T).map F := by rw [e2]; exact Subgroup.mem_top b
        obtain ⟨x, hx, hxa⟩ := ha
        obtain ⟨y, hy, hyb⟩ := hb
        have hc' : ⁅x, y⁆ ∈ ⁅L₁.subgroupOf T, L₂.subgroupOf T⁆ :=
          Subgroup.commutator_mem_commutator hx hy
        rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc'
        apply hab
        rw [← hxa, ← hyb, ← map_mul, ← map_mul, hc']
    rw [← Subgroup.map_subgroupOf_eq_of_le hT₁, ← Subgroup.map_subgroupOf_eq_of_le hT₂, e]
  · have hLT := hmoved L hL hm
    have hc := CFSG.LocalCores.component_overgroup hL hLT
    have hmap := component_map_eq_top F hFs hc hK
    refine ⟨?_, fun y hy => ?_⟩
    · let ψ : ↥(L.subgroupOf T) →* Q := F.comp (L.subgroupOf T).subtype
      have hψ : Function.Surjective ψ := by
        intro q
        have hq : q ∈ (L.subgroupOf T).map F := by rw [hmap]; exact Subgroup.mem_top q
        obtain ⟨x, hx, hxq⟩ := hq
        exact ⟨⟨x, hx⟩, hxq⟩
      exact Q3CH.autOddFreeInner_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLT)
        (autOddFreeInner_of_surj_simple hc.1 ψ hψ hnab hAO)
    · obtain ⟨l', hl', hFl⟩ : ∃ l' ∈ L.subgroupOf T, F l' = F ⟨y, hy⟩ := by
        have hq : F ⟨y, hy⟩ ∈ (L.subgroupOf T).map F := by rw [hmap]; exact Subgroup.mem_top _
        obtain ⟨x, hx, hxq⟩ := hq
        exact ⟨x, hx, hxq⟩
      have hker : l'⁻¹ * (⟨y, hy⟩ : ↥T) ∈ F.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hFl, inv_mul_cancel]
      have hcomm : ∀ w ∈ L.subgroupOf T,
          (l'⁻¹ * (⟨y, hy⟩ : ↥T)) * w = w * (l'⁻¹ * (⟨y, hy⟩ : ↥T)) := by
        intro w hw
        have hN : F.ker.Normal := F.normal_ker
        rcases CFSG.LocalCores.component_subnormal_subgroup hc hN.isSubnormal with h | h
        · exact absurd h (component_not_le_of_odd hc hK)
        · have h1 : ⁅w, l'⁻¹ * (⟨y, hy⟩ : ↥T)⁆ ∈ ⁅L.subgroupOf T, F.ker⁆ :=
            Subgroup.commutator_mem_commutator hw hker
          rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
          exact h1.symm
      refine ⟨(l' : Z), Subgroup.mem_subgroupOf.mp hl', fun w hw => ?_⟩
      have hw₀ : (⟨w, hLT hw⟩ : ↥T) ∈ L.subgroupOf T := Subgroup.mem_subgroupOf.mpr hw
      have h2 : (l'⁻¹ * (⟨y, hy⟩ : ↥T)) * ⟨w, hLT hw⟩ * (l'⁻¹ * (⟨y, hy⟩ : ↥T))⁻¹ =
          ⟨w, hLT hw⟩ := by
        rw [hcomm _ hw₀]
        group
      have key : (⟨y, hy⟩ : ↥T) * ⟨w, hLT hw⟩ * (⟨y, hy⟩ : ↥T)⁻¹ = l' * ⟨w, hLT hw⟩ * l'⁻¹ := by
        calc (⟨y, hy⟩ : ↥T) * ⟨w, hLT hw⟩ * (⟨y, hy⟩ : ↥T)⁻¹
            = l' * ((l'⁻¹ * (⟨y, hy⟩ : ↥T)) * ⟨w, hLT hw⟩ * (l'⁻¹ * (⟨y, hy⟩ : ↥T))⁻¹) *
                l'⁻¹ := by group
          _ = l' * ⟨w, hLT hw⟩ * l'⁻¹ := by rw [h2]
      have := congrArg Subtype.val key
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem exists_inner_of_mem_sup_center {Q : Type} [Group Q] {T L : Subgroup Q}
    (hact : ∀ y ∈ T, ∃ l ∈ L, ∀ w ∈ L, y * w * y⁻¹ = l * w * l⁻¹) {x : Q}
    (hx : x ∈ T ⊔ Subgroup.center Q) : ∃ l ∈ L, ∀ w ∈ L, x * w * x⁻¹ = l * w * l⁻¹ := by
  obtain ⟨y, hy, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨l, hlL, hl⟩ := hact y hy
  refine ⟨l, hlL, fun w hw => ?_⟩
  have hc := Subgroup.mem_center_iff.mp hu w
  calc y * u * w * (y * u)⁻¹ = y * (u * w) * u⁻¹ * y⁻¹ := by group
    _ = y * (w * u) * u⁻¹ * y⁻¹ := by rw [hc]
    _ = y * w * y⁻¹ := by group
    _ = l * w * l⁻¹ := hl w hw

theorem mem_innSubgroup_of_isInducedAut {Q : Type} [Group Q] {L : Subgroup Q} {x : Q}
    {σ : MulAut ↥L} (hσ : TL4.IsInducedAut L x σ) {l : Q} (hlL : l ∈ L)
    (hl : ∀ w ∈ L, x * w * x⁻¹ = l * w * l⁻¹) : σ ∈ Q3NM.innSubgroup ↥L := by
  refine ⟨⟨l, hlL⟩, ?_⟩
  apply MulEquiv.ext
  intro w
  apply Subtype.ext
  rw [hσ w, hl w w.2]
  simp [MulAut.conj_apply]

end Block

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

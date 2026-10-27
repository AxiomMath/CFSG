module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeEndInputs

public section

namespace CFSG.ComponentClassification.GrSLit.HeT

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

variable {X X' : Type} [Group X] [Group X'] {L : Subgroup X} {L' : Subgroup X'}

@[expose] def trS (φ : ↥L ≃* ↥L') (A : Subgroup X) : Subgroup X' :=
  ((A.subgroupOf L).map φ.toMonoidHom).map L'.subtype

theorem trS_le (φ : ↥L ≃* ↥L') (A : Subgroup X) : trS φ A ≤ L' := map_subtype_le _

theorem mem_trS (φ : ↥L ≃* ↥L') {A : Subgroup X} {y : X'} :
    y ∈ trS φ A ↔ ∃ x : ↥L, (x : X) ∈ A ∧ (φ x : X') = y := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, mem_subgroupOf.mp hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, ⟨x, mem_subgroupOf.mpr hx, rfl⟩, rfl⟩

theorem mem_trS_of_mem (φ : ↥L ≃* ↥L') {A : Subgroup X} {x : ↥L} (hx : (x : X) ∈ A) :
    (φ x : X') ∈ trS φ A :=
  (mem_trS φ).mpr ⟨x, hx, rfl⟩

theorem mem_of_mem_trS (φ : ↥L ≃* ↥L') {A : Subgroup X} {x : ↥L} (hx : (φ x : X') ∈ trS φ A) :
    (x : X) ∈ A := by
  obtain ⟨x', hx', he⟩ := (mem_trS φ).mp hx
  rwa [φ.injective (Subtype.ext he)] at hx'

theorem trS_mono (φ : ↥L ≃* ↥L') {A B : Subgroup X} (h : A ≤ B) : trS φ A ≤ trS φ B :=
  fun _ hy => by
    obtain ⟨x, hx, rfl⟩ := (mem_trS φ).mp hy
    exact mem_trS_of_mem φ (h hx)

theorem trS_self (φ : ↥L ≃* ↥L') : trS φ L = L' := by
  apply le_antisymm (trS_le φ L)
  intro y hy
  exact (mem_trS φ).mpr ⟨φ.symm ⟨y, hy⟩, (φ.symm ⟨y, hy⟩).2, by simp⟩

theorem trS_bot (φ : ↥L ≃* ↥L') : trS φ (⊥ : Subgroup X) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_trS φ).mp hy
  rw [mem_bot] at hx ⊢
  rw [show x = 1 from Subtype.ext hx, map_one]
  rfl

theorem trS_sup (φ : ↥L ≃* ↥L') {A B : Subgroup X} (hA : A ≤ L) (hB : B ≤ L) :
    trS φ (A ⊔ B) = trS φ A ⊔ trS φ B := by
  unfold trS
  rw [← Subgroup.map_sup, ← Subgroup.map_sup, subgroupOf_sup hA hB]

theorem trS_injective (φ : ↥L ≃* ↥L') {A B : Subgroup X} (hA : A ≤ L) (hB : B ≤ L)
    (h : trS φ A = trS φ B) : A = B := by
  ext x
  constructor
  · intro hx
    have h1 : (φ ⟨x, hA hx⟩ : X') ∈ trS φ B := h ▸ mem_trS_of_mem φ hx
    exact mem_of_mem_trS φ h1
  · intro hx
    have h1 : (φ ⟨x, hB hx⟩ : X') ∈ trS φ A := h ▸ mem_trS_of_mem φ hx
    exact mem_of_mem_trS φ h1

@[expose] noncomputable def trEquiv (φ : ↥L ≃* ↥L') {A : Subgroup X} (hA : A ≤ L) :
    ↥A ≃* ↥(trS φ A) :=
  ((subgroupOfEquivOfLe hA).symm.trans ((A.subgroupOf L).equivMapOfInjective φ.toMonoidHom
    φ.injective)).trans ((((A.subgroupOf L).map φ.toMonoidHom)).equivMapOfInjective L'.subtype
    L'.subtype_injective)

theorem card_trS (φ : ↥L ≃* ↥L') {A : Subgroup X} (hA : A ≤ L) :
    Nat.card ↥(trS φ A) = Nat.card ↥A :=
  (Nat.card_congr (trEquiv φ hA).toEquiv).symm

theorem trS_inf_centralizer (φ : ↥L ≃* ↥L') {w : X} (hw : w ∈ L) :
    trS φ (L ⊓ centralizer ({w} : Set X)) =
      L' ⊓ centralizer ({(φ ⟨w, hw⟩ : X')} : Set X') := by
  ext y
  rw [mem_trS]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_inf.mpr ⟨(φ x).2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : x * ⟨w, hw⟩ = ⟨w, hw⟩ * x :=
      Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2)
    rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, h1]
  · intro hy
    obtain ⟨hyL, hyC⟩ := mem_inf.mp hy
    refine ⟨φ.symm ⟨y, hyL⟩, mem_inf.mpr ⟨(φ.symm ⟨y, hyL⟩).2, ?_⟩, by simp⟩
    rw [mem_centralizer_singleton_iff]
    have h1 : (⟨y, hyL⟩ : ↥L') * φ ⟨w, hw⟩ = φ ⟨w, hw⟩ * ⟨y, hyL⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp hyC)
    have h2 := congrArg φ.symm h1
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2

@[expose] noncomputable def restrEquiv (φ : ↥L ≃* ↥L') {w : X} (hw : w ∈ L) :
    ↥(L ⊓ centralizer ({w} : Set X)) ≃*
      ↥(L' ⊓ centralizer ({(φ ⟨w, hw⟩ : X')} : Set X')) :=
  (trEquiv φ (inf_le_left : L ⊓ centralizer ({w} : Set X) ≤ L)).trans
    (MulEquiv.subgroupCongr (trS_inf_centralizer φ hw))

theorem restrEquiv_apply (φ : ↥L ≃* ↥L') {w : X} (hw : w ∈ L)
    (a : ↥(L ⊓ centralizer ({w} : Set X))) :
    ((restrEquiv φ hw a : ↥(L' ⊓ centralizer ({(φ ⟨w, hw⟩ : X')} : Set X'))) : X') =
      φ ⟨a, (mem_inf.mp a.2).1⟩ := rfl

theorem trS_gsFixedLayer [Finite X] [Finite X'] (φ : ↥L ≃* ↥L') {w : X} (hw : w ∈ L) :
    trS φ (gsFixedLayer L w) = gsFixedLayer L' (φ ⟨w, hw⟩ : X') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP := FixedLayerPComponent.map_pLayer_mulEquiv 2 (restrEquiv φ hw)
  unfold gsFixedLayer
  rw [← hP]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (mem_trS φ).mp hy
    obtain ⟨a, ha, hax⟩ := hx
    refine ⟨restrEquiv φ hw a, mem_map_of_mem _ ha, ?_⟩
    rw [coe_subtype, restrEquiv_apply]
    congr 2
    exact Subtype.ext hax
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rw [coe_subtype, MulEquiv.coe_toMonoidHom, restrEquiv_apply]
    exact mem_trS_of_mem φ ⟨a, ha, rfl⟩

theorem heldTwoA_iff [Finite X] [Finite X'] (φ : ↥L ≃* ↥L') {w : X} (hw : w ∈ L) :
    HeldTwoA L' (φ ⟨w, hw⟩ : X') ↔ HeldTwoA L w := by
  have hord : orderOf (φ ⟨w, hw⟩ : X') = orderOf w := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  constructor
  · rintro ⟨-, h2, hK⟩
    refine ⟨hw, hord ▸ h2, fun h => hK ?_⟩
    rw [← trS_gsFixedLayer φ hw, h, trS_bot]
  · rintro ⟨-, h2, hK⟩
    refine ⟨(φ ⟨w, hw⟩).2, hord.symm ▸ h2, fun h => hK ?_⟩
    rw [← trS_gsFixedLayer φ hw] at h
    exact trS_injective φ ((gsFixedLayer_le_inf L w).trans inf_le_left) bot_le
      (h.trans (trS_bot φ).symm)

end CFSG.ComponentClassification.GrSLit.HeT

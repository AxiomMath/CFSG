module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbedding.PushingUpLemmas

public section

namespace CFSG.AGLEmbedding

open CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms

section Perfect

variable {Y : Type*} [Group Y]

theorem le_of_relIndex_le_four_of_perfect [Finite Y] {W C : Subgroup Y} (hW : ⁅W, W⁆ = W)
    (h4 : C.relIndex W ≤ 4) : W ≤ C := by
  have : Group.IsPerfect W := Subgroup.isPerfect_iff.mpr hW
  set C' := C.subgroupOf W with hC'
  have hcard : Nat.card (↥W ⧸ C') ≤ 4 := h4
  let φ : ↥W →* Equiv.Perm (↥W ⧸ C') := MulAction.toPermHom ↥W (↥W ⧸ C')
  have : Group.IsSolvable (Equiv.Perm (↥W ⧸ C')) := Equiv.Perm.isSolvable hcard
  have : Group.IsPerfect φ.range := Group.IsPerfect.range φ
  have : Subsingleton φ.range := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable (G := ↥φ.range) inferInstance
  intro w hw
  have h1 : φ ⟨w, hw⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨φ ⟨w, hw⟩, ⟨w, hw⟩, rfl⟩ : φ.range) 1)
  have h2 := congrArg (fun σ : Equiv.Perm (↥W ⧸ C') => σ (QuotientGroup.mk 1)) h1
  simp only [Equiv.Perm.one_apply] at h2
  have h3 : (QuotientGroup.mk (⟨w, hw⟩ * 1) : ↥W ⧸ C') = QuotientGroup.mk 1 := h2
  rw [QuotientGroup.eq] at h3
  have hinv : (⟨w, hw⟩ : ↥W)⁻¹ ∈ C' := by simpa using h3
  have h5 := C'.inv_mem hinv
  rw [inv_inv, hC', Subgroup.mem_subgroupOf] at h5
  exact h5

theorem exists_injective_conj_relIndex [Finite Y] (B L : Subgroup Y) :
    ∃ g : Fin ((Subgroup.normalizer (L : Set Y)).relIndex B) → Y, (∀ j, g j ∈ B) ∧
      Function.Injective fun j => L.map (MulAut.conj (g j)).toMonoidHom := by
  set NB := (Subgroup.normalizer (L : Set Y)).subgroupOf B with hNB
  have hidx : (Subgroup.normalizer (L : Set Y)).relIndex B = Nat.card (↥B ⧸ NB) := by
    rw [Subgroup.relIndex, Subgroup.index]
  rw [hidx]
  let e : Fin (Nat.card (↥B ⧸ NB)) ≃ (↥B ⧸ NB) := (Finite.equivFin _).symm
  refine ⟨fun j => ((Quotient.out (e j) : B) : Y), fun j => (Quotient.out (e j)).2, ?_⟩
  intro i j hij
  simp only at hij
  have hn : ((Quotient.out (e j) : B) : Y)⁻¹ * (Quotient.out (e i) : B) ∈
      Subgroup.normalizer (L : Set Y) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change L.map (MulAut.conj (_ * _)).toMonoidHom = L
    rw [map_conj_mul_eq, hij, ← map_conj_mul_eq, inv_mul_cancel]
    ext x
    simp
  have hmem : (Quotient.out (e j))⁻¹ * Quotient.out (e i) ∈ NB :=
    Subgroup.mem_subgroupOf.mpr (by simpa using hn)
  have heq : e j = e i := by
    rw [← Quotient.out_eq (e j), ← Quotient.out_eq (e i)]
    exact QuotientGroup.eq.mpr hmem
  exact e.injective heq.symm

theorem perfect_le_sup_centralizer_of_outer {L P : Subgroup Y} (hOut : Group.IsSolvable (Outer L))
    (hP : ⁅P, P⁆ = P) (hPN : P ≤ Subgroup.normalizer (L : Set Y)) :
    P ≤ L ⊔ Subgroup.centralizer (L : Set Y) := by
  have : Group.IsPerfect P := Subgroup.isPerfect_iff.mpr hP
  intro x hx
  obtain ⟨l, hl⟩ :=
    perfect_action_inner (L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)) ⟨x, hx⟩
  have hc : (l : Y)⁻¹ * x ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ = l * y * (l : Y)⁻¹ := by
      have := congrArg (fun a : MulAut L => ((a ⟨y, hy⟩ : L) : Y)) hl
      simpa [MulAut.conj_apply] using this
    calc y * ((l : Y)⁻¹ * x) = (l : Y)⁻¹ * (l * y * (l : Y)⁻¹) * x := by group
      _ = (l : Y)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = (l : Y)⁻¹ * x * y := by group
  have e : x = l * ((l : Y)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup l.2 hc

theorem relIndex_centralizer_dvd_card [Finite Y] {L U : Subgroup Y}
    (hU : U ≤ L ⊔ Subgroup.centralizer (L : Set Y)) :
    (Subgroup.centralizer (L : Set Y)).relIndex U ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  set C := Subgroup.centralizer (L : Set Y) with hCdef
  set N := Subgroup.normalizer (L : Set Y) with hNdef
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hUN : U ≤ N := hU.trans (sup_le hLN hCN)
  have hLC : L ≤ Subgroup.normalizer (C : Set Y) :=
    hLN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  set ρ := L.normalizerMonoidHom with hρ
  have hker : ρ.ker = C.subgroupOf N := Subgroup.normalizerMonoidHom_ker L
  have h1 : C.relIndex U = Nat.card ((U.subgroupOf N).map ρ) := by
    rw [← Subgroup.relIndex_subgroupOf hUN, ← hker, Subgroup.relIndex_ker]
  have h2 : C.relIndex L = Nat.card ((L.subgroupOf N).map ρ) := by
    rw [← Subgroup.relIndex_subgroupOf hLN, ← hker, Subgroup.relIndex_ker]
  have h3 : C.relIndex L = Nat.card (↥L ⧸ Subgroup.center ↥L) := by
    have hZ : C.subgroupOf L = Subgroup.center ↥L := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff, hCdef, Subgroup.mem_centralizer_iff]
      constructor
      · intro hx y
        exact Subtype.ext (hx y y.2)
      · intro hx y hy
        exact congrArg Subtype.val (hx ⟨y, hy⟩)
    rw [Subgroup.relIndex, hZ, Subgroup.index]
  have h4 : (U.subgroupOf N).map ρ ≤ (L.subgroupOf N).map ρ := by
    rintro _ ⟨u, hu, rfl⟩
    have huLC : (u : Y) ∈ ((L ⊔ C : Subgroup Y) : Set Y) := hU (Subgroup.mem_subgroupOf.mp hu)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L C hLC] at huLC
    obtain ⟨l, hl, c, hc, hlc⟩ := huLC
    refine ⟨⟨l, hLN hl⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    have hcK : (⟨c, hCN hc⟩ : N) ∈ ρ.ker := hker ▸ Subgroup.mem_subgroupOf.mpr hc
    have e : u = ⟨l, hLN hl⟩ * ⟨c, hCN hc⟩ := Subtype.ext hlc.symm
    rw [e, map_mul, (MonoidHom.mem_ker).mp hcK, mul_one]
  rw [h1, ← h3, h2]
  exact Subgroup.card_dvd_of_le h4

end Perfect

theorem commutator_barM_eq_self {G : Type} [Group G] {M W : Subgroup G} (hWM : W ≤ M)
    (hW : ⁅W, W⁆ = W) : ⁅barM M W, barM M W⁆ = barM M W := by
  have : Group.IsPerfect W := Subgroup.isPerfect_iff.mpr hW
  have : Group.IsPerfect (W.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hWM).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have : Group.IsPerfect (barM M W) :=
    Group.IsPerfect.map (H := W.subgroupOf M) (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
  exact Subgroup.isPerfect_iff.mp this

end CFSG.AGLEmbedding

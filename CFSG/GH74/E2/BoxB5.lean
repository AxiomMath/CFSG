module

public import CFSG.GH74.E2.BoxStd
public import CFSG.GH74.E2.BlackBoxesStd
public import CFSG.GH74.E2.BlackBoxesStdM11
public import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.AS16.E2.ShapeCards
public import CFSG.GH74.E2.Terminal
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.E2.Box

open Subgroup CFSG.GH74.GLS

theorem exists_two_comm_involutions_of_sd16
    {H : Type} [Group H] (P : Subgroup H)
    (e : ↥P ≃* CFSG.Open.SemidihedralGroup 4) :
    ∃ u v : H, orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v ∧ u * v = v * u := by
  let eM : ↥P ≃* SD16M := e.trans (CFSG.Semidihedral.presentationEquivModel 4 (by norm_num))
  obtain ⟨x, y, hx2, hy2, hx1, hy1, hxy, hne⟩ := sd16_two_involutions
  have hx : orderOf (eM.symm x : H) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  have hy : orderOf (eM.symm y : H) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  refine ⟨eM.symm x, eM.symm y, hx, hy, ?_, ?_⟩
  · intro h
    exact hne (eM.symm.injective (Subtype.ext h))
  · have : eM.symm x * eM.symm y = eM.symm y * eM.symm x := by
      rw [← map_mul, ← map_mul, hxy]
    exact congrArg Subtype.val this

theorem termComp_of_shapeLM
    (hComp : ComponentList) (hP : PumpUpData) {G : Type} [Group G]
    [Finite G] (hH : Hyp G) {t : G} (ht : orderOf t = 2) {K : Subgroup G} (hK : IsCompCen t K)
    (hsh : ShapeL33 ↥K ∨ ShapeM11 ↥K) : TermComp K := by
  have hcard : Nat.card ↥K = 5616 ∨ Nat.card ↥K = 7920 := by
    rcases hsh with h | h
    · left
      rw [CFSG.GH74.card_of_lieModel_PSL (by norm_num) h]
      decide
    · right
      exact CFSG.GH74.AS16.E2.card_of_shapeM11 h
  have hterm := isTerminalPair_of_card hComp hP hH ht hK (by omega) (by omega)
  exact fun y hy hy2 => hterm.2.2.2 y hy2 hy

theorem false_of_b5
    (hAS : AschbacherStandardL33) (hASM : AschbacherStandardM11)
    {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G} (ht : orderOf t = 2) {K : Subgroup G}
    (hK : IsCompCen t K) (hsh : ShapeL33 ↥K ∨ ShapeM11 ↥K) (hterm : TermComp K)
    (hnc : ∀ g : G, ¬ IsCompIn (centralizer (K : Set G)) (conjugate K g))
    (hSD : ∃ P : Sylow 2 ↥(Cen t ⊓ centralizer (K : Set G)),
      Nonempty (↥(P : Subgroup ↥(Cen t ⊓ centralizer (K : Set G))) ≃*
        CFSG.Open.SemidihedralGroup 4)) : False := by
  have hq := isCompCen_quasisimple hK
  have htC : t ∈ centralizer (K : Set G) :=
    mem_centralizer_iff.2 fun k hk => (mem_Cen.1 (hK.1 hk)).symm
  have hstd : CFSG.IsStandardSubgroup K :=
    AS16.isStandardSubgroup_of_terminal hq ht htC hterm hnc
  obtain ⟨P, ⟨e⟩⟩ := hSD
  obtain ⟨u, v, hu, hv, huv, hcomm⟩ := exists_two_comm_involutions_of_sd16 _ e
  have hmem : ∀ x : ↥(Cen t ⊓ centralizer (K : Set G)), (x : G) ∈ centralizer (K : Set G) :=
    fun x => x.2.2
  have hu' : orderOf ((u : ↥(Cen t ⊓ centralizer (K : Set G))) : G) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hu
  have hv' : orderOf ((v : ↥(Cen t ⊓ centralizer (K : Set G))) : G) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hv
  have huv' : ((u : ↥(Cen t ⊓ centralizer (K : Set G))) : G) ≠ (v : G) := fun h =>
    huv (Subtype.ext h)
  have hcomm' : ((u : ↥(Cen t ⊓ centralizer (K : Set G))) : G) * v = v * u :=
    congrArg Subtype.val hcomm
  rcases hsh with h | h
  · exact hAS G hH.simple hH.nonabelian hH.kgh K hstd h
      ⟨u, v, hu', hv', huv', hcomm', hmem u, hmem v⟩
  · exact hASM G hH.simple hH.nonabelian hH.kgh K hstd h
      ⟨u, v, hu', hv', huv', hcomm', hmem u, hmem v⟩

end CFSG.GH74.E2.Box

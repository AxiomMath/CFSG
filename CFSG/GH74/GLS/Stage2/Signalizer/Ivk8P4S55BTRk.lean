module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTStmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55GenAct
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55EL3Hbar

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSection_centralizer_of_fixSub {A : Type} [Group A] {J : Subgroup A} [J.Normal]
    (hZ : center ↥J = ⊥) (x : A) {Z : Type} [Group Z]
    (h : IsSection Z ↥(fixSub (actYHom (K := J) x))) :
    IsSection Z ↥(centralizer ({x} : Set A)) := by
  set C : Subgroup A := J ⊓ centralizer ({x} : Set A) with hC
  let f₀ : ↥C →* (↥J ⧸ center ↥J) :=
    (QuotientGroup.mk' (center ↥J)).comp (Subgroup.inclusion (inf_le_left : C ≤ J))
  have hf₀ : ∀ c, f₀ c ∈ fixSub (actYHom (K := J) x) := by
    intro c
    show actYHom (K := J) x (QuotientGroup.mk _) = QuotientGroup.mk _
    rw [actYHom_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have hc : (c : A) ∈ centralizer ({x} : Set A) := c.2.2
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    show x * (c : A) * x⁻¹ = c
    rw [← hc]
    group
  let f : ↥C →* ↥(fixSub (actYHom (K := J) x)) := f₀.codRestrict _ hf₀
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
    have hw' : actYHom (K := J) x (QuotientGroup.mk j) = QuotientGroup.mk j := hw
    rw [actYHom_mk, QuotientGroup.eq] at hw'
    have hjc : (MulAut.conjNormal x j)⁻¹ * j = 1 := by
      have := hw'
      rw [hZ, Subgroup.mem_bot] at this
      exact this
    have hje : MulAut.conjNormal x j = j := by
      rw [inv_mul_eq_one] at hjc
      exact hjc
    have hjx : (j : A) ∈ centralizer ({x} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg Subtype.val hje
      rw [MulAut.conjNormal_apply] at this
      calc (j : A) * x = x * (j : A) * x⁻¹ * x := by rw [this]
        _ = x * j := by group
    refine ⟨⟨j, j.2, hjx⟩, Subtype.ext ?_⟩
    rfl
  exact IsSection.of_le_le inf_le_right (IsSection.of_surjective f hf h)

theorem actYHom_injective {A : Type} [Group A] {J : Subgroup A} [J.Normal]
    (hC : centralizer (J : Set A) = ⊥) (hZ : center ↥J = ⊥) :
    Function.Injective (actYHom (K := J)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxC : x ∈ centralizer (J : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have h1 := congrArg (fun φ : MulAut (↥J ⧸ center ↥J) => φ (QuotientGroup.mk ⟨j, hj⟩)) hx
    simp only [MulAut.one_apply] at h1
    rw [actYHom_mk, QuotientGroup.eq, hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
    have h2 : x * j * x⁻¹ = j := by
      have := congrArg Subtype.val h1
      rwa [MulAut.conjNormal_apply] at this
    calc j * x = x * j * x⁻¹ * x := by rw [h2]
      _ = x * j := by group
  rw [hC] at hxC
  exact hxC

variable {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ} {H P : Subgroup G} {g : G}
  {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem false_of_rankCellK (hInv : InvSec) {F : (Y : Type) → [Group Y] → Prop}
    (hR : RankCellK k F) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) (J : Subgroup (HBar H)) (hJ : IsComponent J)
    (hF : F (↥J ⧸ center ↥J)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  obtain ⟨hbad, hrank⟩ := hR (↥J ⧸ center ↥J) hs hF
  obtain ⟨hJn, hJC, -⟩ := EL3.hbarComp_of_bad hInv h.ctx H hJ hbad
  have hZ : center ↥J = ⊥ := EL3.center_eq_bot_of_centralizer_eq_bot hJC
  set E : Subgroup (HBar H) := barIn H (E16 z t Q₁) with hE
  have hEel := barIn_E16_elem h hd
  have hinj := actYHom_injective hJC hZ
  have hcard : Nat.card ↥(E.map (actYHom (K := J))) = 16 := by
    rw [Subgroup.card_map_of_injective hinj, card_barIn_E16 h hd]
  have hle := hrank (E.map (actYHom (K := J))) (IsElementaryAbelian.map _) ?_
  · omega
  · rintro _ ⟨x, hxE, rfl⟩ hx1
    have hx1' : x ≠ 1 := fun h1 => hx1 (by rw [h1, map_one])
    have hx2 : orderOf x = 2 := by
      have hxx : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxE
      exact orderOf_eq_prime hxx hx1'
    intro Z _ _ hns hsec
    exact hbar_invsec hInv h.ctx H x hx2 Z hns (isSection_centralizer_of_fixSub hZ x hsec)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

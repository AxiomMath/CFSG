module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem frattini_map_subtype_le_of_commutator_le_of_pow_mem {p : ℕ} [Fact p.Prime]
    {V Z : Subgroup G} [Finite ↥V] (hV : IsPGroup p V) (hc : ⁅V, V⁆ ≤ Z)
    (hs : ∀ v ∈ V, v ^ p ∈ Z) : (frattini ↥V).map V.subtype ≤ Z := by
  haveI : Fact (IsPGroup p ↥V) := ⟨hV⟩
  rw [Subgroup.map_le_iff_le_comap,
    CFSG.frattini_eq_closure_commutator_union_powers (p := p), Subgroup.closure_le]
  rintro x (hx | ⟨y, rfl⟩)
  · have key : ∀ g h : ↥V, ⁅g, h⁆ ∈ Z.comap V.subtype := fun g h => by
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact hc (Subgroup.commutator_mem_commutator g.2 h.2)
    have hc' : (⁅(⊤ : Subgroup ↥V), (⊤ : Subgroup ↥V)⁆) ≤ Z.comap V.subtype :=
      Subgroup.commutator_le.mpr (fun g _ h _ => key g h)
    exact hc' hx
  · rw [SetLike.mem_coe, Subgroup.mem_comap]
    simpa using hs y.1 y.2

section Finite

variable [Finite G]

theorem frattini_map_subtype_mono {A B : Subgroup G}
    (hB : IsPGroup 2 B) (hAB : A ≤ B) :
    (frattini ↥A).map A.subtype ≤ (frattini ↥B).map B.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥B) := ⟨hB⟩
  refine frattini_map_subtype_le_of_commutator_le_of_pow_mem
    (p := 2) (V := A) (Z := (frattini ↥B).map B.subtype) (hB.to_le hAB) ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    have hcommB : _root_.commutator ↥B ≤ frattini ↥B :=
      CFSG.commutator_le_frattini_of_isPGroup (R := ↥B) (p := 2)
    have hmem : ⁅(⟨x, hAB hx⟩ : B), (⟨y, hAB hy⟩ : B)⁆ ∈ frattini ↥B :=
      hcommB (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    exact Subgroup.mem_map.mpr ⟨_, hmem, map_commutatorElement B.subtype _ _⟩
  · intro x hx
    have hpow : (⟨x, hAB hx⟩ : B) ^ 2 ∈ frattini ↥B :=
      CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥B) (p := 2) _
    exact Subgroup.mem_map.mpr ⟨(⟨x, hAB hx⟩ : B) ^ 2, hpow, by simp⟩

private theorem sq_mem_frattini_map_of_le_sup {W R P H : Subgroup G}
    (hW2 : IsPGroup 2 W) (hW : W = R ⊔ P) (hR : IsElementaryAbelian 2 R)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r)
    (hHW : H ≤ W) {x : G} (hx : x ∈ H) :
    x ^ 2 ∈ (frattini ↥P).map P.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, p, hp, hxrp⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := R) (B := P) hcomm
      (hW ▸ hHW hx)
  have hr2 : r ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) r hr
  have hcp : Commute r p := (commute_iff_eq r p).mpr (hcomm r hr p hp)
  have hx2 : x ^ 2 = p ^ 2 := by
    rw [← hxrp, hcp.mul_pow 2, hr2, one_mul]
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hW2.to_le (hW.symm ▸ le_sup_right)⟩
  rw [hx2]
  exact Subgroup.mem_map.mpr
    ⟨(⟨p, hp⟩ : P) ^ 2, CFSG.pth_power_mem_frattini_of_isPGroup (R := ↥P) (p := 2) _, by simp⟩

private theorem commutator_mem_frattini_map_of_le_sup {W R P H : Subgroup G}
    (hW2 : IsPGroup 2 W) (hW : W = R ⊔ P) (hR : IsElementaryAbelian 2 R)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r)
    (hHW : H ≤ W) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
    ⁅x, y⁆ ∈ (frattini ↥P).map P.subtype := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, p, hp, hxrp⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := R) (B := P) hcomm
      (hW ▸ hHW hx)
  obtain ⟨s, hs, q, hq, hysq⟩ :=
    CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute (A := R) (B := P) hcomm
      (hW ▸ hHW hy)
  have hrs : r * s = s * r :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := R)).comm ⟨r, hr⟩ ⟨s, hs⟩)
  have hcommut : ⁅x, y⁆ = ⁅p, q⁆ := by
    rw [← hxrp, ← hysq,
      CFSG.GroupTheory.commutatorElement_mul_of_commute (A := R) (B := P) hcomm hr hs hp hq,
      commutatorElement_eq_one_iff_mul_comm.mpr hrs, one_mul]
  rw [hcommut]
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hW2.to_le (hW.symm ▸ le_sup_right)⟩
  refine Subgroup.mem_map.mpr ⟨⁅(⟨p, hp⟩ : P), (⟨q, hq⟩ : P)⁆, ?_, ?_⟩
  · have hcommP : _root_.commutator ↥P ≤ frattini ↥P :=
      CFSG.commutator_le_frattini_of_isPGroup (R := ↥P) (p := 2)
    exact hcommP (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  · exact map_commutatorElement P.subtype (⟨p, hp⟩ : P) (⟨q, hq⟩ : P)

theorem frattini_map_subtype_le_of_le_sup {W R P : Subgroup G}
    (hW2 : IsPGroup 2 W) (hW : W = R ⊔ P)
    (hR : IsElementaryAbelian 2 R)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r) :
    ∀ H : Subgroup G, H ≤ W →
      (frattini ↥H).map H.subtype ≤ (frattini ↥P).map P.subtype := by
  intro H hHW
  refine frattini_map_subtype_le_of_commutator_le_of_pow_mem
    (p := 2) (V := H) (Z := (frattini ↥P).map P.subtype) (hW2.to_le hHW) ?_ ?_
  · rw [Subgroup.commutator_le]
    intro x hx y hy
    exact commutator_mem_frattini_map_of_le_sup hW2 hW hR hcomm hHW hx hy
  · intro x hx
    exact sq_mem_frattini_map_of_le_sup hW2 hW hR hcomm hHW hx

theorem frattini_map_subtype_eq_of_sup {W R P : Subgroup G}
    (hW2 : IsPGroup 2 W) (hW : W = R ⊔ P)
    (hR : IsElementaryAbelian 2 R)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r) :
    (frattini ↥W).map W.subtype = (frattini ↥P).map P.subtype := by
  apply le_antisymm
  · exact frattini_map_subtype_le_of_le_sup hW2 hW hR hcomm W le_rfl
  · exact frattini_map_subtype_mono hW2 (hW.symm ▸ le_sup_right)

theorem frattini_map_subtype_map_conj_eq_of_le_sup {W R P : Subgroup G}
    (hW2 : IsPGroup 2 W) (hW : W = R ⊔ P)
    (hR : IsElementaryAbelian 2 R)
    (hcomm : ∀ r ∈ R, ∀ p ∈ P, r * p = p * r)
    (g : G) (hPgW : P.map (MulAut.conj g).toMonoidHom ≤ W) :
    (frattini ↥(P.map (MulAut.conj g).toMonoidHom)).map
        (P.map (MulAut.conj g).toMonoidHom).subtype =
      (frattini ↥P).map P.subtype := by
  let Q : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  let e : ↥P ≃* ↥Q := MulEquiv.subgroupMap (MulAut.conj g) P
  have hfr : (frattini ↥P).map e.toMonoidHom = frattini ↥Q := by
    refine le_antisymm ?_ fun x hx => ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · have h := frattini_le_comap_frattini_of_surjective
        (φ := e.symm.toMonoidHom) e.symm.surjective
      exact ⟨e.symm x, h hx, by simp⟩
  have hcardFr : Nat.card (frattini ↥Q) = Nat.card (frattini ↥P) := by
    rw [← hfr, Subgroup.card_map_of_injective e.injective]
  have hcard : Nat.card ((frattini ↥Q).map Q.subtype) =
      Nat.card ((frattini ↥P).map P.subtype) := by
    rw [Subgroup.card_map_of_injective Q.subtype_injective,
      Subgroup.card_map_of_injective P.subtype_injective]
    exact hcardFr
  have hle : (frattini ↥Q).map Q.subtype ≤ (frattini ↥P).map P.subtype :=
    frattini_map_subtype_le_of_le_sup hW2 hW hR hcomm Q hPgW
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])

theorem frattini_map_subtype_ne_bot_of_not_isMulCommutative {P : Subgroup G}
    (hP2 : IsPGroup 2 P) (hP : ¬ IsMulCommutative P) :
    (frattini ↥P).map P.subtype ≠ ⊥ := by
  intro hbot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 ↥P) := ⟨hP2⟩
  have hfr : frattini ↥P = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (frattini ↥P) P.subtype_injective).mp hbot
  have hElem : IsElementaryAbelian 2 ↥P :=
    (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥P) (p := 2)).mp hfr
  exact hP hElem.toIsMulCommutative


theorem natCard_frattini_map_conj (H : Subgroup G) (g : G) :
    Nat.card ((frattini ↥(H.map (MulAut.conj g).toMonoidHom)).map
        (H.map (MulAut.conj g).toMonoidHom).subtype) =
      Nat.card ((frattini ↥H).map H.subtype) := by
  let K : Subgroup G := H.map (MulAut.conj g).toMonoidHom
  let e : ↥H ≃* ↥K := MulEquiv.subgroupMap (MulAut.conj g) H
  have hfr : (frattini ↥H).map e.toMonoidHom = frattini ↥K := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · have h := frattini_le_comap_frattini_of_surjective
        (φ := e.symm.toMonoidHom) e.symm.surjective
      exact fun x hx => ⟨e.symm x, h hx, by simp⟩
  have hcardFr : Nat.card (frattini ↥K) = Nat.card (frattini ↥H) := by
    rw [← hfr, Subgroup.card_map_of_injective e.injective]
  change Nat.card ((frattini ↥K).map K.subtype) =
    Nat.card ((frattini ↥H).map H.subtype)
  rw [Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.card_map_of_injective H.subtype_injective]
  exact hcardFr

end Finite

end CFSG.GroupTheory

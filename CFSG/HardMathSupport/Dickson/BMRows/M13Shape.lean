module

public import CFSG.HardMathSupport.Dickson.BMRows.M13L33Invol
public import CFSG.HardMathSupport.Dickson.BMRows.M13Normal
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.M13Shape

open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.BMRows.M13L33

theorem shapeRkAt_of_l33 {G : Type} [Group G] [Finite G] {x : G}
    (hx : orderOf x = 13) {Q : Subgroup G} (hQC : Q ≤ Subgroup.centralizer ({x} : Set G))
    (e : Q ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 3))
    (hC : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) ≤ 451 * 936)
    (hI : ∀ u : G, u * u = 1 → u ≠ 1 → u * x = x * u →
      Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) ≤ 936) :
    ShapeRkAt 13 GoodL33 TrivRk x := by
  haveI hp : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  haveI hsQ : IsSimpleGroup ↥Q := isSimple_of_equiv_sl e
  have hnab : ∃ a b : ↥Q, a * b ≠ b * a := noncomm_of_equiv_sl e
  have hQcard : Nat.card ↥Q = 5616 := card_of_equiv_sl e
  have hxcard : Nat.card ↥(Subgroup.zpowers x) = 13 := by rw [Nat.card_zpowers, hx]
  have hZ : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) → z = 1 := M13Normal.eq_one_of_central hnab
  have hconj : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ l ∈ Q, g * l * g⁻¹ ∈ Q :=
    M13Normal.conj_mem_of_small_index hnab hQC (by omega) (by rw [hxcard, hQcard]; omega)
  obtain ⟨u, hu2, hu1, hu48⟩ := exists_involution_cent_ge e
  have hcm := M13Normal.card_mul_cent_le hQC hZ u
  have hu2' : (u : G) * u = 1 := by simpa using congrArg Subtype.val hu2
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hux : (u : G) * x = x * u := Subgroup.mem_centralizer_singleton_iff.1 (hQC u.2)
  have h936 := hI u hu2' hu1' hux
  have hxZ : x ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
      Subgroup.mem_centralizer_iff.2 fun q hq => Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)⟩
  have hle : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G)) *
      48 ≤ 936 :=
    calc _ ≤ Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G)) *
          Nat.card ↥(Subgroup.centralizer ({u} : Set ↥Q)) := Nat.mul_le_mul_left _ hu48
      _ ≤ Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G) ⊓
          Subgroup.centralizer ({x} : Set G)) := hcm
      _ ≤ 936 := h936
  have hcent : IsPGroup 13 ↥(Subgroup.centralizer ({x} : Set G) ⊓
      Subgroup.centralizer (Q : Set G)) :=
    M13Normal.isPGroup_of_card_lt hxZ hx (m := 48) (N := 936) (by norm_num) hle (by norm_num)
  have hpQ : 13 ∣ Nat.card ↥Q := by rw [hQcard]; norm_num
  have hZ' : Subgroup.center ↥Q = ⊥ := M13Normal.center_eq_bot_of_simple_nonab hnab
  have hLq : CFSG.Open.IsQuasisimple ↥Q :=
    ⟨M13Normal.commutator_eq_top_of_simple_nonab hnab,
      ((QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hcore : CFSG.Open.GLAPPrimeCore 13 ↥Q = ⊥ :=
    glaPPrimeCore_eq_bot_of_simple hp.out hpQ
  exact shapeRkAt_of_normal_quasisimple hp.out hQC hconj hLq hpQ hcent
    ⟨(pSimpleEquivSelf Q hcore hZ').trans e⟩ trivial

end CFSG.HardMathSupport.Dickson.BMRows.M13Shape

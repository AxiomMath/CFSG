module

public import CFSG.GH74.GLS.Basic

import CFSG.GH74.GLS.Bg.Pu5.ZStructBasic
import CFSG.Adapters.Involutions
import CFSG.GH74.GLS.C3.Layer1.U1aRank

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

theorem elementary_rank_conjugate_closure_of_le_zStar
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {P T : Subgroup G} {x : G}
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hx2 : orderOf x = 2)
    (hB : Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} ≤
      T ⊓ CFSG.GH74.GLS.zStar P) :
    CFSG.IsElementaryAbelian 2 ↥(Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}) ∧
      2 ≤ CFSG.pRank 2 ↥(Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let B : Subgroup G :=
    Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}
  have hBdef : B = Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} := rfl
  have hBle : B ≤ T ⊓ CFSG.GH74.GLS.zStar P := by
    rw [hBdef]
    exact hB
  have hcommB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    have hA := hBle ha
    have hB' := hBle hb
    exact CFSG.GH74.GLS.Bg.Pu5.comm_of_mem_cSec (T := T) (K := P)
      (CFSG.ABGLocalTools.IsSylowOf.isPGroup hT)
      hA.1 hB'.1 hA.2.1 hB'.2.2
  have hx_sq : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, pow_two] at this
  have hgenB : ∀ a : G,
      a ∈ Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} → a ∈ B := by
    intro a ha
    rw [hBdef]
    exact ha
  have hBexp : Monoid.exponent ↥B ∣ 2 := by
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro z
    apply Subtype.ext
    have hzB : (z : G) ∈
        Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} := by
      rw [← hBdef]
      exact z.2
    have hzpow : (z : G) ^ 2 = 1 := by
      refine Subgroup.closure_induction (k := {a : G | a ∈ T ∧ IsConj x a})
        (p := fun a _ => a ^ 2 = 1) (x := (z : G)) ?_ ?_ ?_ ?_ hzB
      · intro a ha
        obtain ⟨c, rfl⟩ := isConj_iff.mp ha.2
        rw [pow_two]
        calc
          (c * x * c⁻¹) * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
          _ = 1 := by rw [hx_sq]; group
      · simp
      · intro a b ha hb ha2 hb2
        have hcomm_ab : a * b = b * a :=
          hcommB a (hgenB a ha)
            b (hgenB b hb)
        calc
          (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
            rw [pow_two, pow_two, pow_two]
            calc
              (a * b) * (a * b) = a * (b * a) * b := by group
              _ = a * (a * b) * b := by rw [hcomm_ab]
              _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, mul_one]
      · intro a ha ha2
        rw [inv_pow, ha2, inv_one]
    simpa using hzpow
  have hBcommClosure :
      IsMulCommutative ↥(Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}) :=
    Subgroup.isMulCommutative_closure (fun a ha b hb _ =>
      hcommB a (hgenB a (Subgroup.subset_closure ha))
        b (hgenB b (Subgroup.subset_closure hb)))
  have hBcomm : IsMulCommutative ↥B := by
    rw [hBdef]
    exact hBcommClosure
  have hBelem : CFSG.IsElementaryAbelian 2 ↥B := by
    refine { toIsMulCommutative := hBcomm, exponent_dvd_p := ?_ }
    exact hBexp
  obtain ⟨c, -, hcT⟩ :=
    CFSG.GH74.GLS.Bg.Pu5.exists_conj_mem_of_isSylowOf'
      (K := ⊤) (T := T) hT (Subgroup.mem_top x) ⟨1, by simpa using hx2⟩
  let x' : G := c * x * c⁻¹
  have hx'T : x' ∈ T := hcT
  have hx'2 : orderOf x' = 2 := by
    change orderOf (c * x * c⁻¹) = 2
    rw [CFSG.GH74.GLS.Bg.Pu5.orderOf_conj_eq', hx2]
  have hx'conj : IsConj x x' := isConj_iff.mpr ⟨c, rfl⟩
  have hexists : ∃ y : G, y ∈ T ∧ IsConj x' y ∧ y ≠ x' := by
    by_contra hno
    have hno' : ∀ y : G, y ∈ T → IsConj x' y → y = x' := by
      intro y hyT hyconj
      by_contra hyne
      exact hno ⟨y, hyT, hyconj, hyne⟩
    have hwc : ∀ g : G, g⁻¹ * x' * g ∈ T → g⁻¹ * x' * g = x' := by
      intro g hg
      exact hno' (g⁻¹ * x' * g) hg (isConj_iff.mpr ⟨g⁻¹, by group⟩)
    have hcentT : ∀ t ∈ T, t * x' = x' * t := by
      intro t ht
      have hmem : t⁻¹ * x' * t ∈ T :=
        T.mul_mem (T.mul_mem (T.inv_mem ht) hx'T) ht
      have heq : t⁻¹ * x' * t = x' := hwc t hmem
      calc
        t * x' = t * (t⁻¹ * x' * t) := by rw [heq]
        _ = x' * t := by group
    have hTdata :=
      (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T) (K := ⊤)).1 hT
    let S : Sylow 2 G := hTdata.2.1.toSylow (by
      rw [← Subgroup.relIndex_top_right]
      exact hTdata.2.2)
    have hScoe : (S : Subgroup G) = T := rfl
    have hx'S : x' ∈ (S : Subgroup G) := by
      simpa [hScoe] using hx'T
    have hcentS : (⟨x', hx'S⟩ : (S : Subgroup G)) ∈
        Subgroup.center (S : Subgroup G) := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      exact hcentT (s : G) (by simpa [hScoe] using s.2)
    have hx'2S : orderOf (⟨x', hx'S⟩ : (S : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk, hx'2]
    have hwcS : ∀ g : G, g⁻¹ * x' * g ∈ (S : Subgroup G) →
        g⁻¹ * x' * g = x' := by
      intro g hg
      rw [hScoe] at hg
      exact hwc g hg
    obtain ⟨hfac, -⟩ :=
      CFSG.Adapters.glauberman_zStar S ⟨x', hx'S⟩ hcentS hx'2S hwcS
    have hodd : CFSG.oddCore G = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.oddCore G) with h | h
      · exact h
      · exfalso
        exact CFSG.Adapters.not_mem_oddCore_of_orderOf_eq_two hx'2
          (by rw [h]; trivial)
    have hx'centG : x' ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨d, hd, k, hk, rfl⟩ := hfac g
      rw [hodd, Subgroup.mem_bot] at hk
      subst hk
      have := Subgroup.mem_centralizer_iff.1 hd x'
        (Set.mem_singleton_iff.2 rfl)
      simpa using this.symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · rw [h, Subgroup.mem_bot] at hx'centG
      rw [hx'centG, orderOf_one] at hx'2
      exact (by decide : (1 : ℕ) ≠ 2) hx'2
    · obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have ha : a ∈ Subgroup.center G := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.1 ha b).symm
  obtain ⟨y, hyT, hyconjx', hyne⟩ := hexists
  have hyconj : IsConj x y := hx'conj.trans hyconjx'
  have hx'B : x' ∈ B := hgenB x' (Subgroup.subset_closure ⟨hx'T, hx'conj⟩)
  have hyB : y ∈ B := hgenB y (Subgroup.subset_closure ⟨hyT, hyconj⟩)
  have hy2 : orderOf y = 2 := by
    obtain ⟨d, rfl⟩ := isConj_iff.mp hyconjx'
    rw [CFSG.GH74.GLS.Bg.Pu5.orderOf_conj_eq', hx'2]
  have hxy_comm : x' * y = y * x' := hcommB x' hx'B y hyB
  have hne : x' ≠ y := fun h => hyne h.symm
  have hrank : 2 ≤ CFSG.pRank 2 ↥B :=
    CFSG.GH74.GLS.C3.Layer1.U1a.two_le_pRank_of_commute
      hx'B hyB hx'2 hy2 hxy_comm hne
  rw [← hBdef]
  exact ⟨hBelem, hrank⟩

end CFSG.GH74.GLS.NT44

end

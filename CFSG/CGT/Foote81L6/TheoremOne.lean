module

public import CFSG.CGT.Foote81L6.DescentData
public import CFSG.Adapters.Involutions
public import CFSG.Holt.StarCase.Lemma26Basic
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import Certificates.Certificate43

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

@[expose] def FooteLemma6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (k n : ℕ) (D : FooteCore G T (k + 3) n),
    closure {x | x ∈ (T : Subgroup G) ∧ IsConj D.a x} = zpowers D.a ∨
      closure {x | x ∈ (T : Subgroup G) ∧ IsConj D.a x} = D.A ∨
      closure {x | x ∈ (T : Subgroup G) ∧ IsConj D.a x} = D.Astar

@[expose] def FooteCaseFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ) (D : FooteData G T 2 n),
    StronglyInvolutionClosed D.A T ∨ StronglyInvolutionClosed D.Astar T

@[expose] def FooteB₀Commutes : Prop :=
  ∀ (G : Type) [Group G] (T : Subgroup G) (m n : ℕ) (D : FooteCore G T m n),
    ∀ x ∈ D.B₀, ∀ y ∈ D.B₀, x * (D.t * y * D.t⁻¹) = (D.t * y * D.t⁻¹) * x

@[expose] def FooteLemma6Key : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (k n : ℕ) (D : FooteCore G T (k + 3) n),
    (∃ x : G, x * D.a * x⁻¹ ∈ (T : Subgroup G) ∧ x * D.a * x⁻¹ ∉ D.A) →
      ∃ y : G, ∃ a₁ ∈ D.A, orderOf a₁ = 2 ∧ a₁ ≠ D.a ∧ y * D.a * y⁻¹ = a₁ * D.b ∧
        y * D.b * y⁻¹ = D.b

@[expose] def FooteNotConjAB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (m n : ℕ) (D : FooteCore G T m n),
    ¬ IsConj D.a (D.a * D.b)

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem exists_conj_of_involution {x y : G} (hx : x ∈ D.A) (hx2 : orderOf x = 2) (hxa : x ≠ D.a)
    (hy : y ∈ D.A) (hy2 : orderOf y = 2) (hya : y ≠ D.a) :
    ∃ g ∈ D.A ⊔ zpowers D.t, g * x * g⁻¹ = y := by
  obtain ⟨i, hi⟩ := D.eAt_sr_of_involution (x := ⟨x, mem_sup_left hx⟩) hx hx2 hxa
  obtain ⟨i', hi'⟩ := D.eAt_sr_of_involution (x := ⟨y, mem_sup_left hy⟩) hy hy2 hya
  have hp := D.zpar_of_eAt_sr (x := ⟨x, mem_sup_left hx⟩) hx hi
  have hp' := D.zpar_of_eAt_sr (x := ⟨y, mem_sup_left hy⟩) hy hi'
  have hd : zpar m D.one_le_m (i - i') = 0 := by
    have : i - i' = (i - D.jt) - (i' - D.jt) := by ring
    rw [this, map_sub, hp, hp']
    decide
  obtain ⟨c, hc⟩ := (zpar_eq_zero_iff D.one_le_m).1 hd
  refine ⟨(D.eAt.symm (r c) : G), (D.eAt.symm (r c)).2, ?_⟩
  have : D.eAt.symm (r c) * ⟨x, mem_sup_left hx⟩ * (D.eAt.symm (r c))⁻¹ =
      ⟨y, mem_sup_left hy⟩ := by
    apply D.eAt.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hi, hi', inv_r, r_mul_sr,
      sr_mul_r]
    congr 1
    calc i - c + -c = i - (c + c) := by ring
      _ = i' := by rw [← hc]; ring
  exact congrArg Subtype.val this

theorem stronglyInvolutionClosed_of_closure_eq
    (h : closure {x | x ∈ T ∧ IsConj D.a x} = D.A) : StronglyInvolutionClosed D.A T := by
  have hex : ∃ x, x ∈ T ∧ IsConj D.a x ∧ x ≠ D.a := by
    by_contra hcon
    push Not at hcon
    have hle : closure {x | x ∈ T ∧ IsConj D.a x} ≤ zpowers D.a := by
      rw [closure_le]
      rintro x ⟨hxT, hxc⟩
      rw [hcon x hxT hxc]
      exact mem_zpowers _
    rw [h] at hle
    haveI : Finite ↥(zpowers D.a) := Nat.finite_of_card_ne_zero (by
      rw [card_zpowers_of_involution D.a_mul_a D.a_ne_one]; norm_num)
    have hcard := Subgroup.card_le_of_le hle
    rw [D.card_A, card_zpowers_of_involution D.a_mul_a D.a_ne_one] at hcard
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) D.two_le_m
    omega
  obtain ⟨x₀, hx₀T, hx₀c, hx₀a⟩ := hex
  have hx₀A : x₀ ∈ D.A := h ▸ subset_closure ⟨hx₀T, hx₀c⟩
  have hx₀2 : orderOf x₀ = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hx₀c
    rw [← hc, ← D.a_order]
    exact (SemiconjBy.orderOf_eq c (by simp [SemiconjBy, mul_assoc])).symm
  have hconj : ∀ y ∈ D.A, orderOf y = 2 → IsConj D.a y := by
    intro y hy hy2
    by_cases hya : y = D.a
    · rw [hya]
    · obtain ⟨g, -, hg⟩ := D.exists_conj_of_involution hx₀A hx₀2 hx₀a hy hy2 hya
      exact hx₀c.trans (isConj_iff.2 ⟨g, hg⟩)
  intro y hy hy2 g hg
  rw [← h]
  refine subset_closure ⟨hg, ?_⟩
  exact (hconj y hy hy2).trans (isConj_iff.2 ⟨g, rfl⟩)

theorem A_le_closure_involutions :
    D.A ≤ closure {x | x ∈ D.A ∧ orderOf x = 2 ∧ x ≠ D.a} := by
  intro x hx
  have hrefl : ∀ {v : ZMod (2 ^ m)}, zpar m D.one_le_m (v - D.jt) = 1 →
      ((D.eAt.symm (sr v) : G)) ∈ closure {x | x ∈ D.A ∧ orderOf x = 2 ∧ x ≠ D.a} :=
    fun hv => subset_closure ⟨D.eAt_symm_sr_mem hv, D.orderOf_eAt_symm_sr _,
      D.eAt_symm_sr_ne_a _⟩
  set g : ↥(D.A ⊔ zpowers D.t) := ⟨x, mem_sup_left hx⟩
  rcases (D.mem_A_iff_eAt g).1 hx with ⟨i, hi, hpar⟩ | ⟨i, hi, hpar⟩
  · have hu : zpar m D.one_le_m ((D.jt + 1) - D.jt) = 1 := by
      rw [add_sub_cancel_left, map_one]
    have hu' : zpar m D.one_le_m ((D.jt + 1 + i) - D.jt) = 1 := by
      rw [show D.jt + 1 + i - D.jt = 1 + i by ring, map_add, map_one, hpar, add_zero]
    have hprod : g = D.eAt.symm (sr (D.jt + 1)) * D.eAt.symm (sr (D.jt + 1 + i)) := by
      apply D.eAt.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, sr_mul_sr, hi]
      congr 1
      ring
    have hx' : x = ((D.eAt.symm (sr (D.jt + 1)) : G)) * D.eAt.symm (sr (D.jt + 1 + i)) := by
      have := congrArg Subtype.val hprod
      simpa using this
    rw [hx']
    exact mul_mem (hrefl hu) (hrefl hu')
  · have hx' : x = ((D.eAt.symm (sr i) : G)) := by
      have : g = D.eAt.symm (sr i) := by rw [← hi, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val this
    rw [hx']
    exact hrefl hpar

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm

theorem A_le_closure_conj_of {x₀ : G} (hx₀A : x₀ ∈ D.A) (hx₀a : x₀ ≠ D.a) (hx₀c : IsConj D.a x₀) :
    D.A ≤ closure {x | x ∈ T ∧ IsConj D.a x} := by
  have hx₀2 : orderOf x₀ = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hx₀c
    rw [← hc, orderOf_conj_eq, D.a_order]
  refine D.A_le_closure_involutions.trans ((closure_le _).2 ?_)
  rintro y ⟨hyA, hy2, hya⟩
  obtain ⟨g, -, hg⟩ := D.exists_conj_of_involution hx₀A hx₀2 hx₀a hyA hy2 hya
  exact subset_closure ⟨D.A_le_T hyA, hx₀c.trans (isConj_iff.2 ⟨g, hg⟩)⟩

end FooteCore

theorem footeLemma6_of_key (hK : FooteLemma6Key) (h3 : FooteNotConjAB) : FooteLemma6 := by
  intro G _ _ T k n D
  set C := closure {x | x ∈ (T : Subgroup G) ∧ IsConj D.a x}
  have haC : D.a ∈ C := subset_closure ⟨D.a_mem_T, IsConj.refl _⟩
  have hconj_mem : ∀ {X : Subgroup G}, (∀ x : G, x * D.a * x⁻¹ ∈ (T : Subgroup G) →
      x * D.a * x⁻¹ ∈ X) → C ≤ X := by
    intro X hX
    refine (closure_le _).2 ?_
    rintro x ⟨hxT, hxc⟩
    obtain ⟨g, rfl⟩ := isConj_iff.1 hxc
    exact hX g hxT
  by_cases hA : ∀ x : G, x * D.a * x⁻¹ ∈ (T : Subgroup G) → x * D.a * x⁻¹ ∈ D.A
  · have hCA : C ≤ D.A := hconj_mem hA
    by_cases hCa : C = zpowers D.a
    · exact Or.inl hCa
    · right; left
      obtain ⟨x₀, hx₀T, hx₀c, hx₀a⟩ : ∃ x, x ∈ (T : Subgroup G) ∧ IsConj D.a x ∧ x ≠ D.a := by
        by_contra hcon
        push Not at hcon
        apply hCa
        refine le_antisymm ((closure_le _).2 ?_) (zpowers_le.2 haC)
        rintro x ⟨hxT, hxc⟩
        rw [hcon x hxT hxc]
        exact mem_zpowers _
      exact le_antisymm hCA (D.A_le_closure_conj_of (hCA (subset_closure ⟨hx₀T, hx₀c⟩)) hx₀a hx₀c)
  · push Not at hA
    obtain ⟨x, hxT, hxA⟩ := hA
    obtain ⟨y, a₁, ha₁A, ha₁2, ha₁a, hya, hyb⟩ := hK G T k n D ⟨x, hxT, hxA⟩
    right; right
    have hab : a₁ * D.b ∈ D.Astar := subset_closure ⟨a₁, ha₁A, ha₁2, ha₁a, rfl⟩
    have hab_a : a₁ * D.b ≠ D.a := by
      intro h
      have : D.b = a₁⁻¹ * D.a := by rw [← h]; group
      have hbA : D.b ∈ D.A := this ▸ mul_mem (inv_mem ha₁A) D.a_mem
      have : D.b ∈ D.A ⊓ D.B := mem_inf.2 ⟨hbA, D.b_mem_B⟩
      rw [D.A_inf_B, mem_bot] at this
      exact D.b_ne_one this
    have hAsC : D.Astar ≤ C :=
      D.star.A_le_closure_conj_of (x₀ := a₁ * D.b) hab hab_a (isConj_iff.2 ⟨y, hya⟩)
    refine le_antisymm (hconj_mem fun x₁ hx₁T => ?_) hAsC
    by_contra hx₁
    obtain ⟨y₁, a₁', ha₁'A, ha₁'2, ha₁'a, hy₁a, -⟩ := hK G T k n D.star ⟨x₁, hx₁T, hx₁⟩
    obtain ⟨a₂, ha₂A, ha₂2, ha₂a, rfl⟩ := D.exists_of_involution_Astar ha₁'A ha₁'2 ha₁'a
    have h1 : y₁ * D.a * y₁⁻¹ = a₂ := by
      have := hy₁a
      rw [show D.star.b = D.b from rfl, show D.star.a = D.a from rfl, mul_assoc a₂, D.b_mul_b,
        mul_one] at this
      exact this
    obtain ⟨g, -, hg⟩ := D.exists_conj_of_involution ha₂A ha₂2 ha₂a ha₁A ha₁2 ha₁a
    have h2 : y * (D.a * D.b) * y⁻¹ = a₁ := by
      calc y * (D.a * D.b) * y⁻¹ = (y * D.a * y⁻¹) * (y * D.b * y⁻¹) := by group
        _ = a₁ * D.b * D.b := by rw [hya, hyb]
        _ = a₁ := by rw [mul_assoc, D.b_mul_b, mul_one]
    apply h3 G T (k + 3) n D
    have c1 : IsConj D.a a₂ := isConj_iff.2 ⟨y₁, h1⟩
    have c2 : IsConj a₂ a₁ := isConj_iff.2 ⟨g, hg⟩
    have c3 : IsConj (D.a * D.b) a₁ := isConj_iff.2 ⟨y, h2⟩
    exact (c1.trans c2).trans c3.symm

theorem footeTheorem1_of (hL6 : FooteLemma6) (hC4 : FooteCaseFour) (hB : FooteB₀Commutes) :
    FooteTheorem1 := by
  suffices h : ∀ m : ℕ, ∀ (G : Type) [Group G] [Finite G] (T : Sylow 2 G) (n : ℕ)
      (D : FooteData G T m n), StronglyInvolutionClosed D.A T ∨ StronglyInvolutionClosed D.Astar T by
    intro G _ _ T m n D
    exact h m G T n D
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G _ _ T n D
  have hm := D.two_le_m
  obtain rfl | ⟨k, rfl⟩ : m = 2 ∨ ∃ k, m = k + 3 := by
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · left; omega
    · right; exact ⟨m - 3, by omega⟩
  · exact hC4 G T n D
  by_contra hneither
  push Not at hneither
  obtain ⟨hnA, hnAs⟩ := hneither
  rcases hL6 G T k n D.toFooteCore with h | h | h
  ·
    have hwc : ∀ g : G, g⁻¹ * D.a * g ∈ (T : Subgroup G) → g⁻¹ * D.a * g = D.a := by
      intro g hg
      have hmem : g⁻¹ * D.a * g ∈ closure {x | x ∈ (T : Subgroup G) ∧ IsConj D.a x} :=
        subset_closure ⟨hg, isConj_iff.2 ⟨g⁻¹, by group⟩⟩
      rw [h, D.mem_zpowers_a_iff] at hmem
      rcases hmem with h1 | h1
      · exfalso
        apply D.a_ne_one
        have : D.a = g * (g⁻¹ * D.a * g) * g⁻¹ := by group
        rw [this, h1]
        group
      · exact h1
    have hzZ : (⟨D.a, D.a_mem_T⟩ : (T : Subgroup G)) ∈ Subgroup.center (T : Subgroup G) :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (D.a_comm_T y.2)
    have hz : orderOf (⟨D.a, D.a_mem_T⟩ : (T : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk, D.a_order]
    obtain ⟨-, hcen⟩ := CFSG.Adapters.glauberman_zStar T ⟨D.a, D.a_mem_T⟩ hzZ hz hwc
    set O := CFSG.oddCore G
    have hO : Odd (Nat.card O) := CFSG.Holt.StarLemma26.odd_card_oddCore G
    have haO : ∀ g : G, g * D.a * g⁻¹ * D.a⁻¹ ∈ O := by
      intro g
      have h1 := Subgroup.mem_center_iff.1 hcen (QuotientGroup.mk g)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h1
      have : g * D.a * g⁻¹ * D.a⁻¹ = (g * D.a)⁻¹⁻¹ * ((D.a * g))⁻¹ * ((D.a * g) * g⁻¹ * D.a⁻¹) := by
        group
      have h2 : (g * D.a)⁻¹ * (D.a * g) ∈ O := h1
      have h3 : g * D.a * g⁻¹ * D.a⁻¹ = (g * D.a) * ((g * D.a)⁻¹ * (D.a * g))⁻¹ *
          (g * D.a)⁻¹ := by group
      rw [h3]
      exact (inferInstance : O.Normal).conj_mem _ (inv_mem h2) _
    haveI : (D.descM O).Normal := D.toFooteCore.descM_normal haO
    let Dbar := D.descent hO haO (hB G T (k + 3) n D.toFooteCore)
    let Tbar : Sylow 2 (G ⧸ D.descM O) :=
      T.mapSurjective (QuotientGroup.mk'_surjective (D.descM O))
    rcases ih (k + 2) (by omega) (G ⧸ D.descM O) Tbar n Dbar with h' | h'
    · exact hnA (D.toFooteCore.stronglyInvolutionClosed_of_map hO D.A_le_T D.a_mem haO h')
    · have hAs : Dbar.Astar = D.Astar.map (QuotientGroup.mk' (D.descM O)) :=
        D.toFooteCore.Astar_descent hO
      have h'' : StronglyInvolutionClosed (D.Astar.map (QuotientGroup.mk' (D.descM O)))
          ((T : Subgroup G).map (QuotientGroup.mk' (D.descM O))) := by
        rw [← hAs]
        exact h'
      exact hnAs (D.toFooteCore.stronglyInvolutionClosed_of_map hO D.Astar_le_T D.a_mem_Astar haO
        h'')
  · exact hnA (D.toFooteCore.stronglyInvolutionClosed_of_closure_eq h)
  · exact hnAs (D.toFooteCore.star.stronglyInvolutionClosed_of_closure_eq h)

end CFSG.CGT.Foote81L6

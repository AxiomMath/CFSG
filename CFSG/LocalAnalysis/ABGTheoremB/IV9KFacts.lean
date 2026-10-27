module

public import CFSG.LocalAnalysis.ABGTheoremB.IV9Constrained
public import CFSG.LocalAnalysis.ABGTheoremB.CoverEmbedding
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.GroupTheory.ABGLocalTools.Criteria
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public noncomputable section

namespace CFSG.ABGTheoremB.Setting

open CFSG.ABGQGroups CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

section Generic

variable {G : Type u} [Group G]

private theorem exists_fixed_mem_coset' [Finite G] {D H : Subgroup G} (hD : IsPGroup 2 D)
    (hH : Odd (Nat.card H)) {v : G}
    (hinv : ∀ d ∈ D, ∀ l ∈ H, v⁻¹ * (d * (v * l) * d⁻¹) ∈ H) :
    ∃ l ∈ H, ∀ d ∈ D, d * (v * l) * d⁻¹ = v * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction D H :=
    { smul := fun d l => ⟨v⁻¹ * ((d : G) * (v * l) * (d : G)⁻¹), hinv d d.2 l l.2⟩
      one_smul := fun l => Subtype.ext (by
        change v⁻¹ * ((1 : G) * (v * l) * (1 : G)⁻¹) = l
        group)
      mul_smul := fun d₁ d₂ l => Subtype.ext (by
        change v⁻¹ * (((d₁ : G) * d₂) * (v * l) * ((d₁ : G) * d₂)⁻¹) =
          v⁻¹ * ((d₁ : G) * (v * (v⁻¹ * ((d₂ : G) * (v * l) * (d₂ : G)⁻¹))) * (d₁ : G)⁻¹)
        group) }
  obtain ⟨l, hl⟩ := hD.nonempty_fixed_point_of_prime_not_dvd_card H hH.not_two_dvd_nat
  refine ⟨l, l.2, fun d hd => ?_⟩
  have h : v⁻¹ * (d * (v * l) * d⁻¹) = l := congrArg Subtype.val (hl ⟨d, hd⟩)
  calc d * (v * l) * d⁻¹ = v * (v⁻¹ * (d * (v * l) * d⁻¹)) := by group
    _ = v * l := by rw [h]

private def abKernel (W : Subgroup G) : Subgroup G where
  carrier := {d | d ∈ Subgroup.normalizer (W : Set G) ∧ ∀ w ∈ W, d * w * d⁻¹ * w⁻¹ ∈ ⁅W, W⁆}
  one_mem' := ⟨one_mem _, fun w _ => by simp [one_mem]⟩
  mul_mem' := by
    rintro d₁ d₂ ⟨hd₁, h₁⟩ ⟨hd₂, h₂⟩
    refine ⟨mul_mem hd₁ hd₂, fun w hw => ?_⟩
    have hW' : d₁ * (d₂ * w * d₂⁻¹ * w⁻¹) * d₁⁻¹ ∈ ⁅W, W⁆ := by
      have hn : d₁ ∈ Subgroup.normalizer ((⁅W, W⁆ : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp hd₁)]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (h₂ w hw)
    have e : d₁ * d₂ * w * (d₁ * d₂)⁻¹ * w⁻¹ =
        (d₁ * (d₂ * w * d₂⁻¹ * w⁻¹) * d₁⁻¹) * (d₁ * w * d₁⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem hW' (h₁ w hw)
  inv_mem' := by
    rintro d ⟨hd, h⟩
    refine ⟨inv_mem hd, fun w hw => ?_⟩
    have hw' : d⁻¹ * w * d⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (inv_mem hd) w).mp hw
    have h' := h _ hw'
    have e : d⁻¹ * w * d⁻¹⁻¹ * w⁻¹ = (d * (d⁻¹ * w * d⁻¹⁻¹) * d⁻¹ * (d⁻¹ * w * d⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    rw [e]
    exact inv_mem h'

private theorem le_of_le_sup_commutator [Finite G] {r : ℕ} [Fact r.Prime] {W H : Subgroup G}
    (hW : IsPGroup r W) (hHW : H ≤ W) (h : W ≤ H ⊔ ⁅W, W⁆) : W ≤ H := by
  have : Fact (IsPGroup r W) := ⟨hW⟩
  have hsup : H.subgroupOf W ⊔ commutator W = ⊤ := by
    rw [eq_top_iff]
    intro w _
    have hw : (w : G) ∈ H ⊔ ⁅W, W⁆ := h w.2
    rw [← Subgroup.map_subtype_commutator, ← Subgroup.map_subgroupOf_eq_of_le hHW,
      ← Subgroup.map_sup] at hw
    obtain ⟨w', hw', hww'⟩ := hw
    rwa [← Subtype.ext hww']
  have hfr : H.subgroupOf W ⊔ frattini W = ⊤ :=
    eq_top_iff.mpr (hsup.ge.trans
      (sup_le_sup_left (CFSG.commutator_le_frattini_of_isPGroup (p := r)) _))
  have htop := frattini_nongenerating hfr
  intro w hw
  have : (⟨w, hw⟩ : W) ∈ H.subgroupOf W := htop ▸ Subgroup.mem_top _
  exact this

private theorem mem_centralizer_of_mem_abKernel [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {W : Subgroup G} (hW : IsPGroup r W) {g : G} {k : ℕ} (hg : g ^ 2 ^ k = 1)
    (hgW : g ∈ abKernel W) : g ∈ Subgroup.centralizer (W : Set G) := by
  have hD : IsPGroup 2 (Subgroup.zpowers g) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hg)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hDK : Subgroup.zpowers g ≤ abKernel W := Subgroup.zpowers_le.mpr hgW
  have hW'W : ⁅W, W⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem ha hb) (W.inv_mem ha)) (W.inv_mem hb)
  have hodd : Odd (Nat.card (⁅W, W⁆ : Subgroup G)) := by
    obtain ⟨n, hn⟩ := (hW.to_le hW'W).exists_card_eq
    rw [hn]
    exact ((Fact.out : r.Prime).odd_of_ne_two hr2).pow
  have hcov : W ≤ (W ⊓ Subgroup.centralizer {g}) ⊔ ⁅W, W⁆ := by
    intro w hw
    obtain ⟨l, hl, hfix⟩ := exists_fixed_mem_coset' hD hodd (v := w) (by
      intro d hd l hl
      obtain ⟨hdN, hdW⟩ := hDK hd
      have hn : d ∈ Subgroup.normalizer ((⁅W, W⁆ : Subgroup G) : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
          (Subgroup.mem_normalizer_iff_map_conj_eq.mp hdN)]
      have h1 := hdW w hw
      have h2 : d * l * d⁻¹ ∈ ⁅W, W⁆ := (Subgroup.mem_normalizer_iff.mp hn l).mp hl
      have e : w⁻¹ * (d * (w * l) * d⁻¹) = w⁻¹ * (d * w * d⁻¹ * w⁻¹) * w * (d * l * d⁻¹) := by
        group
      rw [e]
      refine mul_mem ?_ h2
      have h3 : w⁻¹ * (d * w * d⁻¹ * w⁻¹) * w⁻¹⁻¹ ∈ ⁅W, W⁆ := by
        have hn' : w⁻¹ ∈ Subgroup.normalizer ((⁅W, W⁆ : Subgroup G) : Set G) := by
          have hwN : w⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
            Subgroup.le_normalizer (W.inv_mem hw)
          rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
            (Subgroup.mem_normalizer_iff_map_conj_eq.mp hwN)]
        exact (Subgroup.mem_normalizer_iff.mp hn' _).mp h1
      simpa using h3)
    have hwl : w * l ∈ W ⊓ Subgroup.centralizer {g} := by
      refine Subgroup.mem_inf.mpr ⟨W.mul_mem hw (hW'W hl), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := hfix g (Subgroup.mem_zpowers g)
      calc w * l * g = g * (g⁻¹ * (w * l) * g) := by group
        _ = g * (w * l) := by
          congr 1
          calc g⁻¹ * (w * l) * g = g⁻¹ * (g * (w * l) * g⁻¹) * g := by rw [h]
            _ = w * l := by group
    have e : w = (w * l) * l⁻¹ := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hwl) (Subgroup.mem_sup_right (inv_mem hl))
  have hle := le_of_le_sup_commutator hW inf_le_left hcov
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have := (Subgroup.mem_inf.mp (hle hw)).2
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

end Generic

section SL2

variable {F : Type} [Field F] [Finite F]

private theorem sl2_isPerfect (hF : 4 ≤ Nat.card F) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := by
  apply CFSG.LinearGroups.special_linear_dimension_two_perfect
  have := Fintype.ofFinite F
  obtain ⟨u, -, hu⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact hF)
  exact ⟨u, hu⟩

private theorem sl2_normal_le_center_or_eq_top (hF : 4 ≤ Nat.card F)
    (M : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [M.Normal] :
    M ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) ∨ M = ⊤ := by
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  let π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  have : (M.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hs.eq_bot_or_eq_top_of_normal (M.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hsup : M ⊔ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊤ := by
      have := congrArg (Subgroup.comap π) h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
    have := sl2_isPerfect hF
    have hcomm : commutator (Matrix.SpecialLinearGroup (Fin 2) F) ≤ M := by
      rw [← QuotientGroup.ker_mk' M, ← Subgroup.map_eq_bot_iff, commutator_def,
        Subgroup.map_commutator, ← hsup, Subgroup.map_sup, (Subgroup.map_eq_bot_iff M).mpr
          (QuotientGroup.ker_mk' M).ge, bot_sup_eq, ← Subgroup.map_commutator,
        Subgroup.map_eq_bot_iff]
      have hZ : ⁅Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F),
          Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro z hz
        rw [Subgroup.mem_centralizer_iff]
        intro w _
        exact Subgroup.mem_center_iff.mp hz w
      rw [hZ]
      exact bot_le
    rw [Group.IsPerfect.commutator_eq_top] at hcomm
    exact top_le_iff.mp hcomm

variable {B : Type*} [Group B] {L : Subgroup B}

private theorem commutator_eq_of_mulEquiv_sl2 (hF : 4 ≤ Nat.card F)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) : ⁅L, L⁆ = L := by
  have := sl2_isPerfect hF
  have : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private theorem le_centerOf_or_eq_of_mulEquiv_sl2 (hF : 4 ≤ Nat.card F)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) (M : Subgroup B) (hML : M ≤ L)
    (hLM : L ≤ Subgroup.normalizer (M : Set B)) : M ≤ centerOf L ∨ M = L := by
  have hMn : (M.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hML).mpr hLM
  have : ((M.subgroupOf L).map e.toMonoidHom).Normal := hMn.map _ e.surjective
  rcases sl2_normal_le_center_or_eq_top hF ((M.subgroupOf L).map e.toMonoidHom) with h | h
  · left
    intro m hm
    refine Subgroup.mem_inf.mpr ⟨hML hm, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hc := h ⟨⟨m, hML hm⟩, hm, rfl⟩
    have h1 := Subgroup.mem_center_iff.mp hc (e ⟨l, hl⟩)
    have h2 : (⟨l, hl⟩ : L) * ⟨m, hML hm⟩ = ⟨m, hML hm⟩ * ⟨l, hl⟩ :=
      e.injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  · right
    refine le_antisymm hML fun l hl => ?_
    have hl' : e ⟨l, hl⟩ ∈ (M.subgroupOf L).map e.toMonoidHom := h ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hme⟩ := hl'
    have hm' : m = ⟨l, hl⟩ := e.injective hme
    rw [hm'] at hm
    exact hm

private theorem not_le_of_comm_of_mulEquiv_sl2 (hF : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) {Z : Subgroup B}
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) : ¬ L ≤ Z := by
  intro hLZ
  have hL := commutator_eq_of_mulEquiv_sl2 hF e
  have hbot : ⁅L, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hZ b (hLZ hb) a (hLZ ha)
  rw [hL] at hbot
  have hc : Nat.card L = 1 := Subgroup.card_eq_one.mpr hbot
  rw [Nat.card_congr e.toEquiv] at hc
  have hu := Nat.card_eq_one_iff_unique.mp hc
  exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2 (hu.1.elim _ _)

omit [Finite F] in
private theorem sq_ne_minusIdentity_of_mem_centerOf (h2 : (2 : F) ≠ 0)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F) {z : B} (hz : z ∈ centerOf L) :
    e ⟨z, (Subgroup.mem_inf.mp hz).1⟩ ^ 2 ≠ CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
  obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
  have hc : e ⟨z, hzL⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hzC l l.2)
  obtain ⟨c, hc2, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  intro h
  apply CFSG.Semidihedral.OddFieldSL2.minusIdentity_ne_one F h2
  rw [← h]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hcz, ← map_pow]
  simp only [Fintype.card_fin] at hc2
  rw [hc2, map_one, Matrix.SpecialLinearGroup.coe_one]

end SL2

section Linear

private theorem eq_one_or_eq_neg_one_of_det {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (h2 : (2 : k) ≠ 0) (hdim : Module.finrank k V ≤ 2)
    (t : Module.End k V) (ht : t * t = 1) (hdet : LinearMap.det t = 1) : t = 1 ∨ t = -1 := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have ht2 : ∀ v, t (t v) = v := fun v => by
    have := congrArg (fun f : Module.End k V => f v) ht
    simpa using this
  obtain ⟨v, hv⟩ : ∃ v, t v ≠ v := by
    by_contra h
    push Not at h
    exact hne1 (LinearMap.ext h)
  obtain ⟨u, hu⟩ : ∃ u, t u ≠ -u := by
    by_contra h
    push Not at h
    exact hne2 (LinearMap.ext fun x => by simp [h x])
  set e₁ := u + t u with he₁def
  set e₂ := v - t v with he₂def
  have he₁ : t e₁ = e₁ := by rw [he₁def, map_add, ht2, add_comm]
  have he₂ : t e₂ = -e₂ := by rw [he₂def, map_sub, ht2, neg_sub]
  have he₁0 : e₁ ≠ 0 := fun h => hu (eq_neg_of_add_eq_zero_right (by rw [← h]))
  have he₂0 : e₂ ≠ 0 := fun h => hv (sub_eq_zero.mp h).symm
  have hli : LinearIndependent k ![e₁, e₂] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg t hab
    rw [map_add, map_smul, map_smul, he₁, he₂, map_zero] at h1
    have h3 : (2 * a) • e₁ = 0 := by
      have h4 : (2 * a) • e₁ = (a • e₁ + b • e₂) + (a • e₁ + b • -e₂) := by module
      rw [h4, hab, h1, add_zero]
    have ha : a = 0 := by
      rcases smul_eq_zero.mp h3 with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h he₁0
    subst ha
    rw [zero_smul, zero_add] at hab
    exact ⟨rfl, (smul_eq_zero.mp hab).resolve_right he₂0⟩
  have hcard : Fintype.card (Fin 2) = Module.finrank k V := by
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at this ⊢
    omega
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = e₁ := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hb1 : b 1 = e₂ := by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have r0 : b.repr (t (b 0)) = Finsupp.single 0 1 := by
    rw [hb0, he₁, ← hb0, b.repr_self]
  have r1 : b.repr (t (b 1)) = -Finsupp.single 1 1 := by
    rw [hb1, he₂, ← hb1, map_neg, b.repr_self]
  have hd := LinearMap.det_toMatrix b t
  rw [hdet, Matrix.det_fin_two, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
    LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, r0, r1] at hd
  simp at hd
  apply h2
  linear_combination -hd

variable {G : Type u} [Group G]

private def conjW (W : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    W →* W where
  toFun w := ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg w).mp w.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

private theorem mem_abKernel_aux [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {W : Subgroup G}
    [Module (ZMod r) (Additive (Abelianization W))] {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (hab : W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆) {K : Subgroup G}
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) {g₁ g₂ : K} (hg₁ : g₁ ∈ commutator K)
    (hg₂ : g₂ ∈ commutator K) (h₁ : ((g₁ ^ 2 : K) : G) ∈ Subgroup.centralizer (W : Set G))
    (h₂ : ((g₂ ^ 2 : K) : G) ∈ Subgroup.centralizer (W : Set G)) :
    (g₁ : G) ∈ abKernel W ∨ (g₂ : G) ∈ abKernel W ∨ ((g₁ * g₂ : K) : G) ∈ abKernel W := by
  classical
  let φ : K → (W →* W) := fun k => conjW W k (hKW k.2)
  have hφ : ∀ (k : K) (w : W), ((φ k w : W) : G) = k * w * (k : G)⁻¹ := fun _ _ => rfl
  have hext : ∀ f g : Module.End (ZMod r) (Additive (Abelianization W)),
      (∀ w : W, f (Additive.ofMul (Abelianization.of w)) =
        g (Additive.ofMul (Abelianization.of w))) → f = g := by
    intro f g h
    apply LinearMap.ext
    intro x
    induction x using Additive.rec with
    | ofMul y =>
      induction y using QuotientGroup.induction_on with
      | H w => exact h w
  let ρ : K →* Module.End (ZMod r) (Additive (Abelianization W)) :=
    { toFun := fun k => (MonoidHom.toAdditive (Abelianization.map (φ k))).toZModLinearMap r
      map_one' := hext _ _ fun w => by
        change Additive.ofMul (Abelianization.of (φ 1 w)) = Additive.ofMul (Abelianization.of w)
        congr 2
        apply Subtype.ext
        rw [hφ]
        simp
      map_mul' := fun k₁ k₂ => hext _ _ fun w => by
        change Additive.ofMul (Abelianization.of (φ (k₁ * k₂) w)) =
          Additive.ofMul (Abelianization.of (φ k₁ (φ k₂ w)))
        congr 2
        apply Subtype.ext
        rw [hφ, hφ, hφ]
        simp only [Subgroup.coe_mul]
        group }
  have hρ : ∀ (k : K) (w : W), ρ k (Additive.ofMul (Abelianization.of w)) =
      Additive.ofMul (Abelianization.of (φ k w)) := fun _ _ => rfl
  have : Finite (Additive (Abelianization W)) := by
    have : Finite (Abelianization W) := (inferInstance : Finite (W ⧸ commutator W))
    exact (inferInstance : Finite (Abelianization W))
  have : FiniteDimensional (ZMod r) (Additive (Abelianization W)) := Module.Finite.of_finite
  have hspan : Submodule.span (ZMod r) {Additive.ofMul (Abelianization.of (⟨a, ha⟩ : W)),
      Additive.ofMul (Abelianization.of (⟨b, hb⟩ : W))} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    induction x using Additive.rec with
    | ofMul y =>
      induction y using QuotientGroup.induction_on with
      | H w =>
        change Additive.ofMul (Abelianization.of w) ∈ _
        set Q : Subgroup W := (Subgroup.closure {Abelianization.of (⟨a, ha⟩ : W),
          Abelianization.of (⟨b, hb⟩ : W)}).comap Abelianization.of with hQ
        have hQ' : Subgroup.closure {(⟨a, ha⟩ : W), ⟨b, hb⟩} ⊔ commutator W ≤ Q := by
          refine sup_le ?_ ?_
          · rw [Subgroup.closure_le]
            rintro z (rfl | rfl)
            · exact Subgroup.subset_closure (Set.mem_insert _ _)
            · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
          · intro z hz
            have : Abelianization.of z = 1 := by
              rw [← MonoidHom.mem_ker, Abelianization.ker_of]
              exact hz
            rw [hQ, Subgroup.mem_comap, this]
            exact one_mem _
        have hwmem : w ∈ Subgroup.closure {(⟨a, ha⟩ : W), ⟨b, hb⟩} ⊔ commutator W := by
          have h := hab w.2
          rw [← Subgroup.map_subtype_commutator, show ({a, b} : Set G) =
            W.subtype '' {(⟨a, ha⟩ : W), ⟨b, hb⟩} by simp,
            ← MonoidHom.map_closure, ← Subgroup.map_sup] at h
          obtain ⟨w', hw', hww'⟩ := h
          rwa [← Subtype.ext hww']
        have hof := hQ' hwmem
        change Abelianization.of w ∈ Subgroup.closure _ at hof
        refine Subgroup.closure_induction (p := fun y _ =>
          Additive.ofMul y ∈ Submodule.span (ZMod r) {Additive.ofMul (Abelianization.of
            (⟨a, ha⟩ : W)), Additive.ofMul (Abelianization.of (⟨b, hb⟩ : W))}) ?_ ?_ ?_ ?_ hof
        · rintro y (rfl | rfl)
          · exact Submodule.subset_span (Set.mem_insert _ _)
          · exact Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
        · exact Submodule.zero_mem _
        · intro y₁ y₂ _ _ h₁ h₂
          exact Submodule.add_mem _ h₁ h₂
        · intro y _ h
          exact Submodule.neg_mem _ h
  have hdim : Module.finrank (ZMod r) (Additive (Abelianization W)) ≤ 2 := by
    rw [← finrank_top, ← hspan]
    refine (finrank_span_le_card _).trans ?_
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have hdet : ∀ k ∈ commutator K, LinearMap.det (ρ k) = 1 := by
    intro k hk
    let f : K →* (ZMod r)ˣ := (LinearMap.det.comp ρ).toHomUnits
    have h := Abelianization.commutator_subset_ker f hk
    rw [MonoidHom.mem_ker] at h
    have := congrArg Units.val h
    simpa [f] using this
  have hsq : ∀ g : K, ((g ^ 2 : K) : G) ∈ Subgroup.centralizer (W : Set G) → ρ g * ρ g = 1 := by
    intro g hg
    rw [← map_mul, ← sq]
    refine hext _ _ fun w => ?_
    rw [hρ]
    change _ = Additive.ofMul (Abelianization.of w)
    congr 2
    apply Subtype.ext
    rw [hφ]
    have := Subgroup.mem_centralizer_iff.mp hg w w.2
    rw [← this, mul_inv_cancel_right]
  have hker : ∀ g : K, ρ g = 1 → (g : G) ∈ abKernel W := by
    intro g hg
    refine ⟨hKW g.2, fun w hw => ?_⟩
    have h := congrArg (fun f : Module.End (ZMod r) (Additive (Abelianization W)) =>
      f (Additive.ofMul (Abelianization.of (⟨w, hw⟩ : W)))) hg
    simp only [hρ, Module.End.one_apply] at h
    have h' : Abelianization.of (φ g ⟨w, hw⟩ * (⟨w, hw⟩ : W)⁻¹) = 1 := by
      rw [map_mul, map_inv, Additive.ofMul.injective h, mul_inv_cancel]
    rw [← MonoidHom.mem_ker, Abelianization.ker_of] at h'
    have h'' := Subgroup.mem_map_of_mem W.subtype h'
    rw [Subgroup.map_subtype_commutator] at h''
    simpa [hφ] using h''
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp this)
  rcases eq_one_or_eq_neg_one_of_det h2 hdim (ρ g₁) (hsq g₁ h₁) (hdet g₁ hg₁) with e₁ | e₁
  · exact Or.inl (hker g₁ e₁)
  rcases eq_one_or_eq_neg_one_of_det h2 hdim (ρ g₂) (hsq g₂ h₂) (hdet g₂ hg₂) with e₂ | e₂
  · exact Or.inr (Or.inl (hker g₂ e₂))
  refine Or.inr (Or.inr (hker _ ?_))
  rw [map_mul, e₁, e₂]
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.neg_apply, map_neg, neg_neg]
  rfl

private theorem mem_abKernel_of_two_generated [Finite G] {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2)
    {W : Subgroup G} (hexp : ∀ w ∈ W, w ^ r = 1) {a b : G} (ha : a ∈ W) (hb : b ∈ W)
    (hab : W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆) {K : Subgroup G}
    (hKW : K ≤ Subgroup.normalizer (W : Set G)) {g₁ g₂ : K} (hg₁ : g₁ ∈ commutator K)
    (hg₂ : g₂ ∈ commutator K) (h₁ : ((g₁ ^ 2 : K) : G) ∈ Subgroup.centralizer (W : Set G))
    (h₂ : ((g₂ ^ 2 : K) : G) ∈ Subgroup.centralizer (W : Set G)) :
    (g₁ : G) ∈ abKernel W ∨ (g₂ : G) ∈ abKernel W ∨ ((g₁ * g₂ : K) : G) ∈ abKernel W := by
  let _ : Module (ZMod r) (Additive (Abelianization W)) := AddCommGroup.zmodModule (by
    intro x
    induction x using Additive.rec with
    | ofMul y =>
      induction y using QuotientGroup.induction_on with
      | H w =>
        change r • Additive.ofMul (Abelianization.of w) = 0
        rw [← ofMul_pow, ← map_pow, show w ^ r = 1 from Subtype.ext (by simpa using hexp w w.2),
          map_one]
        rfl)
  exact mem_abKernel_aux hr2 ha hb hab hKW hg₁ hg₂ h₁ h₂

end Linear

section Quaternion

variable {F : Type} [Field F]

private theorem pow_sq_eq_minusIdentity {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hg : g ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F) {m : ℕ} (hm : Odd m) :
    (g ^ m) ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
  obtain ⟨c, rfl⟩ := hm
  rw [← pow_mul, mul_comm, pow_mul, hg, pow_succ, pow_mul,
    CFSG.Semidihedral.OddFieldSL2.minusIdentity_square, one_pow, one_mul]

private theorem exists_pow_eq_mul {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (hg : g ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F) {m : ℕ} (hm : Odd m) :
    ∃ s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F), s ^ 2 = 1 ∧ g ^ m = s * g := by
  obtain ⟨c, rfl⟩ := hm
  refine ⟨CFSG.Semidihedral.OddFieldSL2.minusIdentity F ^ c,
    Subgroup.pow_mem _ (CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F) c, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, CFSG.Semidihedral.OddFieldSL2.minusIdentity_square,
      one_pow]
  · rw [pow_succ, pow_mul, hg]

private theorem quaternion_pow_mul_sq (a b : F) (hab : a ^ 2 + b ^ 2 = -1) {m n : ℕ}
    (hm : Odd m) (hn : Odd n) :
    (CFSG.Semidihedral.OddLinearNormals.quarterTurn F ^ m *
        CFSG.Semidihedral.OddFieldSL2.secondGenerator F a b hab ^ n) ^ 2 =
      CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
  set i := CFSG.Semidihedral.OddLinearNormals.quarterTurn F
  set j := CFSG.Semidihedral.OddFieldSL2.secondGenerator F a b hab
  have hi := CFSG.Semidihedral.OddFieldSL2.quarterTurn_square F
  have hj := CFSG.Semidihedral.OddFieldSL2.secondGenerator_square F a b hab
  have hij : i * j = j * i⁻¹ := CFSG.Semidihedral.OddFieldSL2.generators_inversion F a b hab
  have hij2 : (i * j) ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
    rw [sq, ← hj, sq]
    calc i * j * (i * j) = j * i⁻¹ * (i * j) := by rw [hij]
      _ = j * j := by group
  obtain ⟨s, hs, hs2, hsm⟩ := exists_pow_eq_mul hi hm
  obtain ⟨s', hs', hs'2, hs'n⟩ := exists_pow_eq_mul hj hn
  have hc : s * s' ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := mul_mem hs hs'
  have hc2 : (s * s') ^ 2 = 1 := by
    have hcomm : Commute s s' := (Subgroup.mem_center_iff.mp hs s').symm
    rw [hcomm.mul_pow, hs2, hs'2, one_mul]
  rw [hsm, hs'n]
  have e : s * i * (s' * j) = s * s' * (i * j) := by
    have h1 : i * s' = s' * i := Subgroup.mem_center_iff.mp hs' i
    calc s * i * (s' * j) = s * (i * s') * j := by group
      _ = s * (s' * i) * j := by rw [h1]
      _ = s * s' * (i * j) := by group
  have hcomm' : Commute (s * s') (i * j) := (Subgroup.mem_center_iff.mp hc (i * j)).symm
  rw [e, hcomm'.mul_pow, hc2, one_mul, hij2]

end Quaternion

section Sigma

variable {G : Type u} [Group G] (σ : Setting G)

private theorem x_mem_L₀ [Finite G] (hσ : σ.IsValid) : σ.x ∈ σ.L₀ := by
  obtain ⟨F, _, _, hq, ψ, hψ, -⟩ := hσ.L₀_quotient
  have hodd : Odd (Nat.card F) := by
    rw [hq, q]
    exact (hσ.p_prime.odd_of_ne_two hσ.p_ne_two).pow
  have h2F : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨l, hl⟩ := hψ (CFSG.Semidihedral.OddFieldSL2.minusIdentity F)
  have h2 : 2 ∣ Nat.card σ.L₀ := by
    have h1 : orderOf (ψ l) ∣ orderOf l := orderOf_map_dvd ψ l
    rw [hl, CFSG.Semidihedral.OddFieldSL2.minusIdentity_orderOf F h2F] at h1
    exact h1.trans (orderOf_dvd_natCard l)
  have : (σ.L₀.subgroupOf σ.N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hσ.L₀_le_N).mpr hσ.N_le_normalizer_L₀
  have h2' : 2 ∣ Nat.card (σ.L₀.subgroupOf σ.N) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hσ.L₀_le_N).toEquiv]
  obtain ⟨w, hwZ, hw1, hw2, hwL⟩ :=
    exists_central_involution_of_even (S := σ.S.subtype (σ.S_le_N hσ)) h2'
  have hwS : ((w : σ.N) : G) ∈ (σ.S : Subgroup G) := w.2
  have hwC : ((w : σ.N) : G) ∈ Subgroup.centralizer ((σ.S : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : (⟨s, σ.S_le_N hσ hs⟩ : σ.N) ∈
        ((σ.S.subtype (σ.S_le_N hσ) : Sylow 2 σ.N) : Subgroup σ.N) := hs
    have h := Subgroup.mem_center_iff.mp hwZ ⟨⟨s, σ.S_le_N hσ hs⟩, hs'⟩
    exact congrArg (fun z : ((σ.S.subtype (σ.S_le_N hσ) : Sylow 2 σ.N) : Subgroup σ.N) =>
      ((z : σ.N) : G)) h
  have hword : orderOf ((w : σ.N) : G) = 2 := by
    apply orderOf_eq_prime
    · exact congrArg (fun z : ((σ.S.subtype (σ.S_le_N hσ) : Sylow 2 σ.N) : Subgroup σ.N) =>
        ((z : σ.N) : G)) hw2
    · intro h
      apply hw1
      apply Subtype.ext
      apply Subtype.ext
      exact h
  have hwx := hσ.center_involution _ (Subgroup.mem_inf.mpr ⟨hwS, hwC⟩) hword
  rw [← hwx]
  exact hwL

private theorem orderOf_xBar [Finite G] (hσ : σ.IsValid) :
    orderOf (QuotientGroup.mk' (σ.ON.subgroupOf σ.N) ⟨σ.x, σ.x_mem_N⟩) = 2 := by
  apply orderOf_eq_prime
  · rw [← map_pow]
    have : (⟨σ.x, σ.x_mem_N⟩ : σ.N) ^ 2 = 1 := by
      apply Subtype.ext
      have h := pow_orderOf_eq_one σ.x
      rw [hσ.x_order] at h
      exact h
    rw [this, map_one]
  · intro h
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    have h1 : orderOf σ.x ∣ Nat.card σ.ON := Subgroup.orderOf_dvd_natCard _ h
    rw [hσ.x_order] at h1
    exact σ.two_not_dvd_card_ON h1

private theorem ZBar_eq [Finite G] (hσ : σ.IsValid) (hN : σ.NStructure) :
    ((centerOf σ.D).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) =
      ((solvRadIn σ.N).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) := by
  have hZN : centerOf σ.D ≤ σ.N := inf_le_left.trans (σ.D_le_N hσ)
  rw [hN.N_solvRad, hN.center_S_eq_center_D, Subgroup.subgroupOf_sup σ.ON_le_N hZN,
    Subgroup.map_sup, (Subgroup.map_eq_bot_iff (σ.ON.subgroupOf σ.N)).mpr
      (by rw [QuotientGroup.ker_mk']), bot_sup_eq]

private theorem ZBar_normal [Finite G] (hσ : σ.IsValid) (hN : σ.NStructure) :
    (((centerOf σ.D).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N))).Normal := by
  rw [σ.ZBar_eq hσ hN]
  have h : (solvRadIn σ.N).subgroupOf σ.N = CFSG.solvableRadical σ.N :=
    Subgroup.comap_map_eq_self_of_injective σ.N.subtype_injective _
  rw [h]
  exact CFSG.ABGLocalTools.solvableRadical_normal.map _ (QuotientGroup.mk'_surjective _)

private theorem ZBar_comm :
    ∀ a ∈ ((centerOf σ.D).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)),
      ∀ b ∈ ((centerOf σ.D).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)),
        a * b = b * a := by
  rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz').2 (z : G)
    (Subgroup.mem_inf.mp hz).1

variable {F : Type} [Field F] [Finite F]

private theorem ZBar_inf_L₀Bar_le [Finite G] (hσ : σ.IsValid) (hN : σ.NStructure)
    (hF4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    (e : σ.L₀Bar ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ((centerOf σ.D).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) ⊓ σ.L₀Bar ≤
      centerOf σ.L₀Bar := by
  have := σ.ZBar_normal hσ hN
  have h₁ : σ.L₀Bar ≤ Subgroup.normalizer
      ((((centerOf σ.D).subgroupOf σ.N).map (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) :
        Subgroup (↥σ.N ⧸ σ.ON.subgroupOf σ.N)) : Set (↥σ.N ⧸ σ.ON.subgroupOf σ.N)) :=
    Subgroup.le_normalizer_of_normal
  rcases le_centerOf_or_eq_of_mulEquiv_sl2 hF4 e _ inf_le_right
      ((le_inf h₁ Subgroup.le_normalizer).trans
        Subgroup.inf_normalizer_le_normalizer_inf) with h | h
  · exact h
  · exact absurd (h ▸ inf_le_left) (not_le_of_comm_of_mulEquiv_sl2 hF4 h2 e (σ.ZBar_comm))

end Sigma

section KFacts

variable {G : Type u} [Group G]

private theorem mk_mem_solvableRadical [Finite G] {K : Subgroup G} {k : K}
    (hk : (k : G) ∈ solvRadIn K) :
    QuotientGroup.mk' (CFSG.oddCore K) k ∈ CFSG.solvableRadical (K ⧸ CFSG.oddCore K) := by
  rw [solvableRadical_quotient_oddCore (K := K)]
  obtain ⟨s, hs, hsk⟩ := hk
  exact ⟨s, hs, by rw [Subtype.ext hsk]⟩

private theorem exists_two_part {H : Type*} [Group H] [Finite H] (k : H) :
    ∃ m t : ℕ, Odd m ∧ (k ^ m) ^ 2 ^ t = 1 := by
  obtain ⟨t, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  exact ⟨m, t, hm, by rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]⟩

private theorem odd_orderOf_of_mem_oddCore {H : Type*} [Group H] [Finite H] {o : H}
    (ho : o ∈ CFSG.oddCore H) : Odd (orderOf o) := by
  have h : orderOf o ∣ Nat.card (CFSG.oddCore H) := by
    rw [← Subgroup.orderOf_mk o ho]
    exact orderOf_dvd_natCard _
  exact (odd_card_oddCore H).of_dvd_nat h

private theorem eq_one_of_mem_oddCore {H : Type*} [Group H] [Finite H] {o : H}
    (ho : o ∈ CFSG.oddCore H) {t : ℕ} (hot : o ^ 2 ^ t = 1) : o = 1 := by
  have hcop : Nat.Coprime (orderOf o) (2 ^ t) :=
    Nat.Coprime.pow_right t (Nat.coprime_two_right.mpr (odd_orderOf_of_mem_oddCore ho))
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hot))

private theorem mem_centralizer_of_sq_eq_one {W : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.centralizer (W : Set G)) (hyW : y ∈ Subgroup.normalizer (W : Set G))
    (hy : y ^ 2 = 1) (ho : Odd (orderOf (x⁻¹ * y))) :
    y ∈ Subgroup.centralizer (W : Set G) := by
  have hconj : ∀ w ∈ W, x⁻¹ * y * w * (x⁻¹ * y)⁻¹ = y * w * y⁻¹ := by
    intro w hw
    have hyw : y * w * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hyW w).mp hw
    have hxc := Subgroup.mem_centralizer_iff.mp hx _ hyw
    calc x⁻¹ * y * w * (x⁻¹ * y)⁻¹ = x⁻¹ * ((y * w * y⁻¹) * x) := by group
      _ = x⁻¹ * (x * (y * w * y⁻¹)) := by rw [hxc]
      _ = y * w * y⁻¹ := by group
  have ho2 : (x⁻¹ * y) ^ 2 ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hyw : y * w * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hyW w).mp hw
    have h1 : (x⁻¹ * y) ^ 2 * w * ((x⁻¹ * y) ^ 2)⁻¹ = w := by
      calc (x⁻¹ * y) ^ 2 * w * ((x⁻¹ * y) ^ 2)⁻¹ =
            x⁻¹ * y * (x⁻¹ * y * w * (x⁻¹ * y)⁻¹) * (x⁻¹ * y)⁻¹ := by rw [sq]; group
        _ = y * (y * w * y⁻¹) * y⁻¹ := by rw [hconj w hw, hconj _ hyw]
        _ = y ^ 2 * w * (y ^ 2)⁻¹ := by rw [sq]; group
        _ = w := by rw [hy]; group
    calc w * (x⁻¹ * y) ^ 2 = ((x⁻¹ * y) ^ 2 * w * ((x⁻¹ * y) ^ 2)⁻¹) * (x⁻¹ * y) ^ 2 := by
          rw [h1]
      _ = (x⁻¹ * y) ^ 2 * w := by group
  have ho' : x⁻¹ * y ∈ Subgroup.centralizer (W : Set G) := by
    obtain ⟨k, hk⟩ := ho
    have e : x⁻¹ * y = ((x⁻¹ * y) ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, ← hk,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact Subgroup.pow_mem _ ho2 _
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h := Subgroup.mem_centralizer_iff.mp ho' w hw
  have h2 : y * w * y⁻¹ = w := by
    rw [← hconj w hw, ← h]
    group
  calc w * y = y * w * y⁻¹ * y := by rw [h2]
    _ = y * w := by group

end KFacts

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

theorem IV9_h_II417 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) (hN : σ.NStructure) :
    ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ W : Subgroup G, W ≤ d.R →
      Subgroup.normalizer (d.R : Set G) ≤ Subgroup.normalizer (W : Set G) →
      (∀ w ∈ W, w ^ r = 1) →
      Subgroup.normalizer (d.R : Set G) ⊓ Subgroup.centralizer (W : Set G) ≤
        solvRadIn (Subgroup.normalizer (d.R : Set G)) →
      ¬ ∃ a ∈ W, ∃ b ∈ W, W ≤ Subgroup.closure {a, b} ⊔ ⁅W, W⁆ := by
  intro r hr d W hWR hKW hexp hCW ⟨a, ha, b, hb, hab⟩
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hKL := σ.normalizer_R_mem_familyL hσ hr d
  set K := Subgroup.normalizer (d.R : Set G) with hKdef
  obtain ⟨ι, hinj, hcomp, -, -, hL⟩ :=
    σ.exists_quotient_embedding_of_mem_familyL hσ hII hr.prime hr.dvd_ON hKL
  have hSZ := σ.map_solvableRadical_quotient_of_mem_familyL hσ hII hr.prime hr.dvd_ON hKL hcomp
  have hL₀ : σ.L₀Bar ≤ ι.range := (σ.L₀Bar_le_LBar).trans hL
  obtain ⟨F, _, _, hq, ⟨e⟩⟩ := σ.exists_L₀Bar_mulEquiv hσ
  have hodd : Odd (Nat.card F) := by
    rw [hq, q]
    exact (hσ.p_prime.odd_of_ne_two hσ.p_ne_two).pow
  have hF4 : 4 ≤ Nat.card F := by
    have := hσ.five_lt_q
    rw [hq]
    omega
  have h2 : (2 : F) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hWp : IsPGroup r W := d.R_sylow.isPGroup.to_le hWR
  have hxW : σ.x ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (σ.mem_N_iff w).mp (σ.ON_le_N (d.R_sylow.le (hWR hw)))
  set J : Subgroup (↥K ⧸ CFSG.oddCore ↥K) := σ.L₀Bar.comap ι with hJ
  let e' : J ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    ((J.equivMapOfInjective ι hinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hL₀))).trans e
  have he' : ∀ z : J, e' z = e ⟨ι z, z.2⟩ := fun _ => rfl
  have hnotS : ∀ z : J, e' z ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F →
      (z : ↥K ⧸ CFSG.oddCore ↥K) ∉ CFSG.solvableRadical (↥K ⧸ CFSG.oddCore ↥K) := by
    intro z hz hzS
    have h1 : ι z ∈ ((centerOf σ.D).subgroupOf σ.N).map
        (QuotientGroup.mk' (σ.ON.subgroupOf σ.N)) := hSZ ▸ Subgroup.mem_map_of_mem ι hzS
    have h3 := σ.ZBar_inf_L₀Bar_le hσ hN hF4 h2 e (Subgroup.mem_inf.mpr ⟨h1, z.2⟩)
    exact sq_ne_minusIdentity_of_mem_centerOf h2 e h3 (by rw [← he']; exact hz)
  have hxK : σ.x ∈ K := by
    obtain ⟨-, -, hDK, -⟩ := hKL
    exact hDK (σ.T_le_D hσ σ.x_mem_T)
  have hxJ : QuotientGroup.mk' (CFSG.oddCore ↥K) ⟨σ.x, hxK⟩ ∈ J := by
    change ι (QuotientGroup.mk ⟨σ.x, hxK⟩) ∈ σ.L₀Bar
    rw [hcomp ⟨σ.x, hxK⟩ σ.x_mem_N]
    exact ⟨⟨σ.x, σ.x_mem_N⟩, σ.x_mem_L₀ hσ, rfl⟩
  have hex : e' ⟨_, hxJ⟩ = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
    apply (CFSG.Semidihedral.OddFieldSL2.orderOf_eq_two_iff F h2 _).mp
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ← orderOf_injective ι hinj,
      QuotientGroup.mk'_apply, hcomp ⟨σ.x, hxK⟩ σ.x_mem_N]
    exact σ.orderOf_xBar hσ
  have hcommK : commutator (↥K ⧸ CFSG.oddCore ↥K) =
      (commutator ↥K).map (QuotientGroup.mk' (CFSG.oddCore ↥K)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hJcomm : ∀ z : J, (z : ↥K ⧸ CFSG.oddCore ↥K) ∈ commutator (↥K ⧸ CFSG.oddCore ↥K) := by
    intro z
    have hz : (z : ↥K ⧸ CFSG.oddCore ↥K) ∈ ⁅J, J⁆ := by
      rw [commutator_eq_of_mulEquiv_sl2 hF4 e']
      exact z.2
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top hz
  have hlift : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F,
      M ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F →
      ∃ (g : K) (m t : ℕ), Odd m ∧ g ∈ commutator K ∧ (g : G) ^ 2 ^ t = 1 ∧
        QuotientGroup.mk' (CFSG.oddCore ↥K) g = ((e'.symm M ^ m : J) : ↥K ⧸ CFSG.oddCore ↥K) ∧
        ((g ^ 2 : K) : G) ∈ Subgroup.centralizer (W : Set G) := by
    intro M hM
    have hk := hJcomm (e'.symm M)
    rw [hcommK] at hk
    obtain ⟨k, hk, hkM⟩ := hk
    obtain ⟨m, t, hm, hkt⟩ := exists_two_part k
    have hgM : QuotientGroup.mk' (CFSG.oddCore ↥K) (k ^ m) =
        ((e'.symm M ^ m : J) : ↥K ⧸ CFSG.oddCore ↥K) := by
      rw [map_pow, hkM, Subgroup.coe_pow]
    have hMm : e' (e'.symm M ^ m) ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F := by
      rw [map_pow, MulEquiv.apply_symm_apply]
      exact pow_sq_eq_minusIdentity hM hm
    have hsq : (e'.symm M ^ m) ^ 2 = ⟨_, hxJ⟩ := by
      apply e'.injective
      rw [map_pow, hMm, hex]
    have h4 : (k ^ m) ^ 4 = 1 := by
      apply eq_one_of_mem_oddCore (t := t)
      · rw [← QuotientGroup.eq_one_iff (N := CFSG.oddCore ↥K), ← QuotientGroup.mk'_apply,
          map_pow, hgM, show 4 = 2 * 2 by rfl, pow_mul, ← Subgroup.coe_pow, hsq]
        change (QuotientGroup.mk' (CFSG.oddCore ↥K) ⟨σ.x, hxK⟩) ^ 2 = 1
        rw [← map_pow]
        have : (⟨σ.x, hxK⟩ : K) ^ 2 = 1 := by
          apply Subtype.ext
          have h := pow_orderOf_eq_one σ.x
          rw [hσ.x_order] at h
          exact h
        rw [this, map_one]
      · rw [← pow_mul, mul_comm, pow_mul, hkt, one_pow]
    have hxo : (⟨σ.x, hxK⟩ : K)⁻¹ * (k ^ m) ^ 2 ∈ CFSG.oddCore ↥K := by
      rw [← QuotientGroup.eq]
      have h := congrArg Subtype.val hsq
      rw [Subgroup.coe_pow, ← hgM, ← map_pow] at h
      exact h.symm
    refine ⟨k ^ m, m, t, hm, Subgroup.pow_mem _ hk _, ?_, hgM, ?_⟩
    · rw [← Subgroup.coe_pow, hkt, Subgroup.coe_one]
    · apply mem_centralizer_of_sq_eq_one hxW (hKW ((k ^ m) ^ 2).2)
      · rw [← Subgroup.coe_pow, ← pow_mul, show 2 * 2 = 4 by rfl, h4, Subgroup.coe_one]
      · have := odd_orderOf_of_mem_oddCore hxo
        rwa [← Subgroup.orderOf_coe, Subgroup.coe_mul, Subgroup.coe_inv] at this
  have hnotS' : ∀ (g : K) (z : J), e' z ^ 2 = CFSG.Semidihedral.OddFieldSL2.minusIdentity F →
      QuotientGroup.mk' (CFSG.oddCore ↥K) g = (z : ↥K ⧸ CFSG.oddCore ↥K) →
        (g : G) ∉ Subgroup.centralizer (W : Set G) := by
    intro g z hz hgz hgW
    apply hnotS z hz
    rw [← hgz]
    exact mk_mem_solvableRadical (hCW (Subgroup.mem_inf.mpr ⟨g.2, hgW⟩))
  obtain ⟨a₀, b₀, hab₀⟩ := CFSG.Semidihedral.OddFieldSL2.sum_two_squares F hodd (-1)
  obtain ⟨g₁, m₁, t₁, hm₁, hg₁, hg₁t, hg₁J, hg₁W⟩ := hlift _
    (CFSG.Semidihedral.OddFieldSL2.quarterTurn_square F)
  obtain ⟨g₂, m₂, t₂, hm₂, hg₂, hg₂t, hg₂J, hg₂W⟩ := hlift _
    (CFSG.Semidihedral.OddFieldSL2.secondGenerator_square F a₀ b₀ hab₀)
  rcases mem_abKernel_of_two_generated hr2 hexp ha hb hab hKW hg₁ hg₂ hg₁W hg₂W with
    h | h | h
  · refine hnotS' g₁ _ ?_ hg₁J (mem_centralizer_of_mem_abKernel hr2 hWp hg₁t h)
    rw [map_pow, MulEquiv.apply_symm_apply]
    exact pow_sq_eq_minusIdentity (CFSG.Semidihedral.OddFieldSL2.quarterTurn_square F) hm₁
  · refine hnotS' g₂ _ ?_ hg₂J (mem_centralizer_of_mem_abKernel hr2 hWp hg₂t h)
    rw [map_pow, MulEquiv.apply_symm_apply]
    exact pow_sq_eq_minusIdentity
      (CFSG.Semidihedral.OddFieldSL2.secondGenerator_square F a₀ b₀ hab₀) hm₂
  · obtain ⟨m, t, hm, hgt⟩ := exists_two_part (g₁ * g₂)
    have hgk : (((g₁ * g₂) ^ m : K) : G) ∈ abKernel W := by
      rw [Subgroup.coe_pow]
      exact Subgroup.pow_mem _ h m
    have hgt' : (((g₁ * g₂) ^ m : K) : G) ^ 2 ^ t = 1 := by
      rw [← Subgroup.coe_pow, hgt, Subgroup.coe_one]
    refine hnotS' ((g₁ * g₂) ^ m)
      (((e'.symm (CFSG.Semidihedral.OddLinearNormals.quarterTurn F) ^ m₁) *
        (e'.symm (CFSG.Semidihedral.OddFieldSL2.secondGenerator F a₀ b₀ hab₀) ^ m₂)) ^ m) ?_ ?_
      (mem_centralizer_of_mem_abKernel hr2 hWp hgt' hgk)
    · rw [map_pow, map_mul, map_pow, map_pow, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
      exact pow_sq_eq_minusIdentity (quaternion_pow_mul_sq a₀ b₀ hab₀ hm₁ hm₂) hm
    · rw [map_pow, map_mul, hg₁J, hg₂J]
      simp only [Subgroup.coe_pow, Subgroup.coe_mul]

end CFSG.ABGTheoremB.Setting

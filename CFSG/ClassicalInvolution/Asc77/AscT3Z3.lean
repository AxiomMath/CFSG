module

public import CFSG.ClassicalInvolution.Asc77.AscT3Z3B
public import CFSG.ClassicalInvolution.Asc77.AscT3WGood
public import CFSG.ClassicalInvolution.Asc77.AscT3XCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T3CII

open CFSG.ClassicalInvolution.Asc77.T3CII.T3R
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.RankThree.PartTwo.KFacts CFSG.GorensteinWalter
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups commutatorElement

section Pure

variable {G : Type} [Group G] [Finite G]

theorem z3_mem_centralizerModOdd_sup {K K' : Subgroup G}
    (hKN : K' ≤ Subgroup.normalizer (K : Set G)) (hK'N : K ≤ Subgroup.normalizer (K' : Set G))
    {x : G} (hx : x ∈ cStar K) (hx' : x ∈ cStar K') :
    x ∈ centralizerModOdd (⊤ : Subgroup G) (K ⊔ K') := by
  have hxK : x ∈ centralizerModOdd (⊤ : Subgroup G) K := mem_centralizerModOdd_top_iff.mpr hx
  have hxK' : x ∈ centralizerModOdd (⊤ : Subgroup G) K' := mem_centralizerModOdd_top_iff.mpr hx'
  have hxN : x ∈ Subgroup.normalizer ((K ⊔ K' : Subgroup G) : Set G) :=
    late_mem_normalizer_sup (cStar_le_normalizer K hx) (cStar_le_normalizer K' hx')
  have hMK : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hKN
  have hMK' : K ⊔ K' ≤ Subgroup.normalizer (K' : Set G) :=
    sup_le hK'N Subgroup.le_normalizer
  have hOK : oddCoreOf K ≤ oddCoreOf (K ⊔ K') := oddCoreOf_le_oddCoreOf le_sup_left hMK
  have hOK' : oddCoreOf K' ≤ oddCoreOf (K ⊔ K') := oddCoreOf_le_oddCoreOf le_sup_right hMK'
  refine ⟨trivial, hxN, mem_normalizer_oddCore_of_mem_normalizer hxN, ?_⟩
  let U : Subgroup G :=
    { carrier := {l | l ∈ K ⊔ K' ∧ ⁅x, l⁆ ∈ oddCoreOf (K ⊔ K')}
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨(K ⊔ K').mul_mem haM hbM, ?_⟩
        have h1 : a * ⁅x, b⁆ * a⁻¹ ∈ oddCoreOf (K ⊔ K') :=
          mem_normalizer_oddCoreOf_of_mem_normalizer (Subgroup.le_normalizer haM) hb
        have e : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (oddCoreOf _).mul_mem ha h1
      one_mem' := ⟨(K ⊔ K').one_mem, by simp [commutatorElement_def]⟩
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨(K ⊔ K').inv_mem haM, ?_⟩
        have h1 : a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ ∈ oddCoreOf (K ⊔ K') :=
          mem_normalizer_oddCoreOf_of_mem_normalizer
            ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer haM))
            ((oddCoreOf _).inv_mem ha)
        have e : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact h1 }
  have hKU : K ≤ U := fun l hl => ⟨Subgroup.mem_sup_left hl, hOK (hxK.2.2.2 l hl)⟩
  have hK'U : K' ≤ U := fun l hl => ⟨Subgroup.mem_sup_right hl, hOK' (hxK'.2.2.2 l hl)⟩
  intro l hl
  exact (sup_le hKU hK'U hl).2

end Pure

section Std

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}


theorem Std20.z_perfect_central_involution (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) {P : Subgroup G}
    (hPC : P ≤ Subgroup.centralizer ({z} : Set G)) (hP : Group.IsPerfect ↥P) {c : G} (hcP : c ∈ P)
    (hcc : ∀ x ∈ P, c * x = x * c) (hc2 : c * c = 1) : c = 1 ∨ c = z := by
  by_cases hc1 : c = 1
  · exact Or.inl hc1
  right
  have hp := d.branch.odd
  have hq := d.branch.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hFcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hKop : IsOddPrimePower (Nat.card (GaloisField p f)) :=
    ⟨p, f, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp, Nat.one_le_iff_ne_zero.mpr hf, hFcard⟩
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hFcard]
    omega
  obtain ⟨eK⟩ := d.hyp.nonempty_equiv_sl2 d.late_mem_K
  obtain ⟨eK'⟩ := d.hyp.nonempty_equiv_sl2 d.late_mem_K'
  have hcK : c ∈ cStar K :=
    z3_perfect_center_mem_cStar hKop h4 eK (d.z_perfect_le_N_K hPC hP) hP hcP hcc
  have hcK' : c ∈ cStar K' :=
    z3_perfect_center_mem_cStar hKop h4 eK' (d.z_perfect_le_N_K' hPC hP) hP hcP hcc
  have hcM := z3_mem_centralizerModOdd_sup d.late_K'_le d.late_K_le hcK hcK'
  have hTC : Subgroup.zpowers c ≤ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.zpowers_le.mpr (hPC hcP)
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hc2) hc1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  obtain ⟨n, hnC, hnK, hnT⟩ := d.w_conj_into_S hTC hT2
  have hnK' : conjSub n K' = K' := (d.late_conj_iff hnC).mp hnK
  have hcS : n * c * n⁻¹ ∈ (S : Subgroup G) :=
    hnT (conj_mem_conjSub (Subgroup.mem_zpowers c))
  have hcM' := late_cmo_conj_mem hcM n
  have hsup : conjSub n (K ⊔ K') = K ⊔ K' := by rw [late_conjSub_sup, hnK, hnK']
  have htop : conjSub n (⊤ : Subgroup G) = ⊤ := by
    unfold conjSub
    rw [Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (MulAut.conj n).surjective
  rw [hsup, htop] at hcM'
  have hcmo : n * c * n⁻¹ ∈ centralizerModOdd (S : Subgroup G) (K ⊔ K') :=
    ⟨hcS, hcM'.2.1, hcM'.2.2.1, hcM'.2.2.2⟩
  rw [c7] at hcmo
  have hz2 : z * z = 1 := d.viol.hzK.sq
  rcases eq_one_or_eq_of_mem_zpowers hz2 hcmo with h | h
  · exfalso
    apply hc1
    have : c = n⁻¹ * (n * c * n⁻¹) * n := by group
    rw [this, h]
    group
  · have hnz : n * z * n⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hnC
      rw [this]
      group
    calc c = n⁻¹ * (n * c * n⁻¹) * n := by group
      _ = n⁻¹ * z * n := by rw [h]
      _ = z := by
        have : n⁻¹ * z * n = n⁻¹ * (n * z * n⁻¹) * n := by rw [hnz]
        rw [this]
        group


theorem Std20.z_not_conj_z [IsSimpleGroup G] (d : Std20 p f K K' J S R R' W V z t)
    (c7 : Concl20_7 S K K' z) (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R)
    (h9 : p ^ f ≠ 9) {b : G} (hb : FieldInv20 S K K' W z t b) (g : G) : g * z * g⁻¹ ≠ b := by
  intro hgb
  obtain ⟨e₀, hfe, h5, hzA, hmem, -, -⟩ := d.x_sectionData c9 h8 h9 hb
  set Kb : Subgroup G := perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)) with hKb
  have hKbP : Group.IsPerfect ↥Kb := finite_perfectResidualOf_isPerfect _
  have hzKb : z ∈ Kb := Subgroup.mem_subgroupOf.mp hmem.mem
  have hKbK : Kb ≤ K := (perfectResidualOf_le _).trans inf_le_left
  have hKbC : Kb ≤ Subgroup.centralizer ({b} : Set G) :=
    (perfectResidualOf_le _).trans inf_le_right
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := fun k hk =>
    d.r10a_X_le_C (le_sec20X_left hk)
  have hz2 : z * z = 1 := d.viol.hzK.sq
  set P : Subgroup G := conjSub g⁻¹ Kb with hP
  have hPmem : ∀ x ∈ P, g * x * g⁻¹ ∈ Kb := fun x hx => by
    have := mem_conjSub_iff.mp hx
    simpa using this
  have hPC : P ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    have hy := hPmem x hx
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hKbC hy)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : g * x * g⁻¹ * b = b * (g * x * g⁻¹) := h1
    rw [← hgb] at h2
    calc x * z = g⁻¹ * (g * x * g⁻¹ * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * z * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h2]
      _ = z * x := by group
  have hPperf : Group.IsPerfect ↥P := by
    apply Subgroup.isPerfect_iff.mpr
    rw [hP]
    unfold conjSub
    rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hKbP]
  have hcP : g⁻¹ * z * g ∈ P := by
    have := conj_mem_conjSub (n := g⁻¹) hzKb
    simpa using this
  have hcc : ∀ x ∈ P, (g⁻¹ * z * g) * x = x * (g⁻¹ * z * g) := by
    intro x hx
    have hy := hPmem x hx
    have hyz := Subgroup.mem_centralizer_singleton_iff.mp (hKz (hKbK hy))
    have h2 : g * x * g⁻¹ * z = z * (g * x * g⁻¹) := hyz
    calc (g⁻¹ * z * g) * x = g⁻¹ * (z * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹ * z) * g := by rw [h2]
      _ = x * (g⁻¹ * z * g) := by group
  have hc2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
    calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  rcases d.z_perfect_central_involution c7 hPC hPperf hcP hcc hc2 with h | h
  · apply d.viol.hzK.ne_one
    calc z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · apply hb.not_mem_X
    have hcomm : z * g = g * z := by
      calc z * g = g * (g⁻¹ * z * g) := by group
        _ = g * z := by rw [h]
    have hbz : b = z := by
      calc b = g * z * g⁻¹ := hgb.symm
        _ = z * g * g⁻¹ := by rw [← hcomm]
        _ = z := by group
    rw [hbz]
    exact le_sec20X_left d.viol.hzK.mem

end Std

end CFSG.ClassicalInvolution.Asc77.T3CII

module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarOuter
public import CFSG.GH74.Uniqueness.Bender.UnitaryFixed
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.GH74.Uniqueness.Bender

theorem card_le_two_of_forall_commute {F : Type*} [Group F] [Finite F] {x : F} (hx1 : x ≠ 1)
    (hx2 : x ^ 2 = 1) (hC : ∀ g : F, g * x = x * g → g = 1 ∨ g = x) {P : Subgroup F}
    (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hx2' : IsPGroup 2 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo]; rfl)
  obtain ⟨S, hS⟩ := hx2'.exists_le_sylow
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  have hxS : x ∈ (S : Subgroup F) := hS (mem_zpowers x)
  have hxZ : ∀ g ∈ (S : Subgroup F), g * x = x * g := by
    have : Nontrivial (S : Subgroup F) := ⟨⟨⟨x, hxS⟩, 1, fun h => hx1 (congrArg Subtype.val h)⟩⟩
    have hZ := (S.isPGroup').center_nontrivial
    obtain ⟨⟨c, hcZ⟩, hc1⟩ := exists_ne (1 : center (S : Subgroup F))
    have hc1' : (c : F) ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
    have hcx : (c : F) * x = x * c := by
      have := (mem_center_iff.mp hcZ) ⟨x, hxS⟩
      exact (congrArg Subtype.val this).symm
    have hcx' : (c : F) = x := (hC c hcx).resolve_left hc1'
    intro g hg
    have := (mem_center_iff.mp hcZ) ⟨g, hg⟩
    have h1 : g * c = c * g := congrArg Subtype.val this
    rw [hcx'] at h1
    exact h1
  have hSle : ((S : Subgroup F) : Set F) ⊆ {1, x} := fun g hg =>
    (hC g (hxZ g hg)).elim (fun h => Or.inl h) (fun h => Or.inr (Set.mem_singleton_iff.mpr h))
  have hcardS : Nat.card (S : Subgroup F) ≤ 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc ((S : Subgroup F) : Set F).ncard ≤ ({1, x} : Set F).ncard :=
          Set.ncard_le_ncard hSle (Set.toFinite _)
      _ = 2 := Set.ncard_pair (Ne.symm hx1)
  calc Nat.card P ≤ Nat.card (S' : Subgroup F) := card_le_of_le hS'
    _ = Nat.card (S : Subgroup F) := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ ≤ 2 := hcardS

theorem card_le_two_of_fix_unitary {D : Type} [Group D] [Finite D] {f e : ℕ}
    (hB : BenderType D f 3 e) {x : MulAut D} (hx : orderOf x = 2)
    (hout : ¬ ∃ g : D, ∀ y : D, x y = g * y * g⁻¹) (P : Subgroup (MulAut D)) (hP : IsPGroup 2 P)
    (hPfix : ∀ β ∈ P, ∀ j ∈ autFixed x, β j = j) : Nat.card P ≤ 2 := by
  have : Finite (MulAut D) :=
    Finite.of_injective (fun β : MulAut D => (β : D → D)) DFunLike.coe_injective
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  let F : Subgroup (MulAut D) :=
    { carrier := {β | ∀ j ∈ autFixed x, β j = j}
      mul_mem' := fun {β γ} hβ hγ j hj => by rw [MulAut.mul_apply, hγ j hj, hβ j hj]
      one_mem' := fun j _ => rfl
      inv_mem' := fun {β} hβ j hj => by
        rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hβ j hj] }
  have hxF : x ∈ F := fun j hj => hj
  have hPF : P ≤ F := fun β hβ => hPfix β hβ
  have hC : ∀ g : F, g * ⟨x, hxF⟩ = ⟨x, hxF⟩ * g → g = 1 ∨ g = ⟨x, hxF⟩ := by
    intro g hg
    have hg' : (g : MulAut D) * x = x * g := congrArg Subtype.val hg
    rcases hB.centralizer_unitary x hxx hout g hg' g.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hx1' : (⟨x, hxF⟩ : F) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hx2' : (⟨x, hxF⟩ : F) ^ 2 = 1 := Subtype.ext hx2
  have h := card_le_two_of_forall_commute hx1' hx2' hC (P := P.subgroupOf F) hP.comap_subtype
  rwa [Nat.card_congr (subgroupOfEquivOfLe hPF).toEquiv] at h

theorem psl2Model_simple_nonabelian {f : ℕ} (hf : 2 ≤ f) :
    IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model f) ∧
      ∃ a b : CFSG.Theory.Comparator.PSL2Model f, a * b ≠ b * a := by
  classical
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField 2 f), s.card = 4 := by
    have h4' : 4 ≤ Fintype.card (GaloisField 2 f) := by
      rw [← Nat.card_eq_fintype_card, hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField 2 f))) (n := 4) (by rw [Finset.card_univ]; exact h4')
    exact ⟨s, hs⟩
  obtain ⟨hnt, hsimple, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 f)
    (n := 2) le_rfl (Or.inr h4)
  have hperf := CFSG.LinearGroups.linear_projective_perfect (K := GaloisField 2 f) (n := 2) le_rfl
    (Or.inr h4)
  refine ⟨hsimple, ?_⟩
  by_contra hab
  push Not at hab
  have hbot :
      _root_.commutator (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) = ⊥ := by
    rw [_root_.commutator_def, commutator_eq_bot_iff_le_centralizer]
    intro g _
    rw [mem_centralizer_iff]
    intro h _
    exact hab h g
  have htop := hperf.commutator_eq_top
  rw [hbot] at htop
  obtain ⟨a, b, hne⟩ := hnt
  apply hne
  have ha : a ∈ (⊥ : Subgroup _) := htop ▸ mem_top a
  have hb : b ∈ (⊥ : Subgroup _) := htop ▸ mem_top b
  rw [mem_bot] at ha hb
  rw [ha, hb]

theorem hypOneStar_u3_outer {D : Type} [Group D] [Finite D] {f e : ℕ} (hf : 2 ≤ f)
    (hB : BenderType D f 3 e) {x u : MulAut D} (hx : orderOf x = 2) (hu : u ^ 2 = x)
    (hout : ¬ ∃ g : D, x = MulAut.conj g) {E : Subgroup (MulAut D)} (hEodd : Odd (Nat.card E))
    (hEu : ∀ e ∈ E, u * e * u⁻¹ ∈ E)
    (hE : ∀ c : D, MulAut.conj c * x = x * MulAut.conj c →
      ∀ e ∈ E, MulAut.conj c * e * (MulAut.conj c)⁻¹ ∈ E) :
    ∃ c : D, MulAut.conj c * x = x * MulAut.conj c ∧
      MulAut.conj c * u * (MulAut.conj c)⁻¹ ∉ E ⊔ zpowers u := by
  have hx2 : x ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxx : x * x = 1 := by rw [← sq]; exact hx2
  have hout' : ¬ ∃ g : D, ∀ y : D, x y = g * y * g⁻¹ := by
    rintro ⟨g, hg⟩
    exact hout ⟨g, MulEquiv.ext fun y => by rw [hg y, MulAut.conj_apply]⟩
  obtain ⟨φ⟩ := hB.fixed_unitary x hxx hout'
  obtain ⟨hs, a, b, hab⟩ := psl2Model_simple_nonabelian hf
  have hJs : IsSimpleGroup (autFixed x) := φ.isSimpleGroup
  have hJnab : ∃ a b : autFixed x, a * b ≠ b * a := by
    refine ⟨φ.symm a, φ.symm b, fun h => hab ?_⟩
    have := congrArg φ h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  exact hypOneStar_exists_of_simple_fixed hx hu (autFixed x) (fun y => Iff.rfl) hJs hJnab
    (card_le_two_of_fix_unitary hB hx hout') hEodd hEu hE

end CFSG.SeitzReduction.RankOne

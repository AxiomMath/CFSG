module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big.Faithful
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossReeF4Fam

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.SEITZ3
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross

section Conj

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ}

theorem pow_range_plane (hp : p.Prime) (P : ReePlane K a p) : ∀ x ∈ P.Ψ.range, x ^ p = 1 := by
  rintro _ ⟨z, rfl⟩
  rw [← map_pow]
  have : z ^ p = 1 := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · exact (mem_rootsOfUnity p _).1 z.1.2
    · exact (mem_rootsOfUnity p _).1 z.2.2
  rw [this, map_one]

theorem card_range_plane (hp : p.Prime) (hp2 : p ≠ 2) (P : ReePlane K a p) :
    Nat.card P.Ψ.range = p ^ 2 := by
  have hL2 : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hpL := natCast_ne_zero_algebraicClosure (K := K) hp hp2
  rw [← Nat.card_congr (MonoidHom.ofInjective P.Ψinj).toEquiv, Nat.card_prod]
  have := card_rootsOfUnity_pow (p := p) (e := 1) (L := AlgebraicClosure K) hpL
  rw [pow_one] at this
  rw [this, sq]

theorem exists_conj_plane (hp : p.Prime) (hp2 : p ≠ 2)
    (hsh : ∃ e, SylowShape p 2 e (ReeTag.F4.reeGamma K a)) (P : ReePlane K a p)
    (F : Subgroup (ReeTag.F4.reeGamma K a)) (hFp : ∀ x ∈ F, x ^ p = 1) (hFc : Nat.card F = p ^ 2) :
    ∃ γ : ReeTag.F4.reeGamma K a, F = cj P.Ψ.range γ := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, hsh⟩ := hsh
  have hE'p : ∀ x ∈ P.Ψ.range, x ^ p = 1 := pow_range_plane hp P
  have hE'c : Nat.card P.Ψ.range = p ^ 2 := card_range_plane hp hp2 P
  have hE'pg : IsPGroup p ↥P.Ψ.range := IsPGroup.of_card hE'c
  obtain ⟨S, hS⟩ := hE'pg.exists_le_sylow
  have h1 : IsPGroup p ↥(S : Subgroup (ReeTag.F4.reeGamma K a)) := S.isPGroup'
  have h2 : ¬ p ∣ (S : Subgroup (ReeTag.F4.reeGamma K a)).index := S.not_dvd_index
  obtain ⟨φ⟩ := hsh (S : Subgroup (ReeTag.F4.reeGamma K a)) h1 h2
  have hFpg : IsPGroup p ↥F := IsPGroup.of_card hFc
  obtain ⟨Q, hQ⟩ := hFpg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (ReeTag.F4.reeGamma K a) S Q
  have hQS : (Q : Subgroup (ReeTag.F4.reeGamma K a)) =
      cj (S : Subgroup (ReeTag.F4.reeGamma K a)) c := by
    have h1 : ((c • S : Sylow p (ReeTag.F4.reeGamma K a)) : Subgroup (ReeTag.F4.reeGamma K a)) =
        (Q : Subgroup (ReeTag.F4.reeGamma K a)) := by rw [hc]
    rw [← h1, Sylow.coe_subgroup_smul]
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_cj]
    simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]
  have hFS : cj F c⁻¹ ≤ (S : Subgroup (ReeTag.F4.reeGamma K a)) := by
    intro x hx
    have h1 : x ∈ cj (cj (S : Subgroup (ReeTag.F4.reeGamma K a)) c) c⁻¹ :=
      cj_le_cj (hQ.trans hQS.le) c⁻¹ hx
    rwa [cj_cj] at h1
  have hF' : cj F c⁻¹ = P.Ψ.range :=
    plane_unique hp φ hFS hS (fun x hx => pow_eq_one_of_mem_cj hFp hx) hE'p
      (by rw [card_cj]; exact hFc) hE'c
  exact ⟨c, by rw [← hF', cj_inv_cj]⟩

end Conj

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a p : ℕ}

theorem innerPlaneBalance_of_plane (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (hp : p.Prime)
    (hp3 : 3 < p) (hsh : ∃ e, SylowShape p 2 e (ReeTag.F4.reeGamma K a)) (P : ReePlane K a p) :
    InnerPlaneBalance p (ReeTag.F4.reeGamma K a) := by
  intro E hEin hE hEc H hH
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hinj : Function.Injective
      (MulAut.conj : ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) :=
    CFSG.LieType.SeitzGeneration.conj_injective_of_center_eq_bot
      (ReeTag.large_Ree_fixed_group_center_trivial a K hK)
  have hne : ∃ x ∈ E, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hall
    rw [this, Subgroup.card_bot] at hEc
    have h2p := hp.two_le
    nlinarith
  refine localDeltaIn_eq_bot_of_layers_faithful hp hinj hH hne ?_
  intro g hg hcomm hlayers
  set E₁ : Subgroup (ReeTag.F4.reeGamma K a) := E.comap (MulAut.conj :
    ReeTag.F4.reeGamma K a →* MulAut (ReeTag.F4.reeGamma K a)) with hE₁
  have hE₁mem : ∀ x, x ∈ E₁ ↔ MulAut.conj x ∈ E := fun x => Iff.rfl
  have hE₁map : E₁.map (MulAut.conj : ReeTag.F4.reeGamma K a →*
      MulAut (ReeTag.F4.reeGamma K a)) = E := by
    rw [hE₁, Subgroup.map_comap_eq]
    exact inf_of_le_right hEin
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := by
    intro x hx
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hx
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [← hEc, ← hE₁map, Subgroup.card_map_of_injective hinj]
  obtain ⟨γ, hγ⟩ := exists_conj_plane hp hp2 hsh P E₁ hE₁p hE₁c
  set cγ : MulAut (ReeTag.F4.reeGamma K a) := MulAut.conj γ with hcγ
  have hmem : ∀ z, MulAut.conj (γ * P.Ψ z * γ⁻¹) ∈ E := by
    intro z
    rw [← hE₁mem, hγ, mem_cj]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    exact ⟨z, rfl⟩
  have hcomm' : ∀ z, (cγ⁻¹ * g * cγ) * MulAut.conj (P.Ψ z) =
      MulAut.conj (P.Ψ z) * (cγ⁻¹ * g * cγ) := by
    intro z
    have he := hcomm _ (hmem z)
    have h1 : cγ⁻¹ * g * cγ * MulAut.conj (P.Ψ z) =
        cγ⁻¹ * (g * MulAut.conj (γ * P.Ψ z * γ⁻¹)) * cγ := by
      rw [map_mul, map_mul, map_inv, ← hcγ]
      group
    rw [h1, he, map_mul, map_mul, map_inv, ← hcγ]
    group
  have hfix' : ∀ z, z ≠ 1 → rootCharKernel (expTuple
      ((z.1 : (AlgebraicClosure K)ˣ)) (z.2 : (AlgebraicClosure K)ˣ) P.U) ≠ ∅ →
      ∀ A Sg, IsLayerDecomp P z A Sg → ∀ t ∈ Sg, (cγ⁻¹ * g * cγ) t = t := by
    intro z hz hne A Sg hd t ht
    have hL := isPLayer_of_layer ha hK hp hp3 P γ hz hne hd (hmem z)
    have h1 := hlayers _ hL (cγ t) ⟨t, ht, rfl⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, h1]
    exact MulAut.inv_apply_self _ _ _
  have h1 := faithful_std ha hK hp hp3 P _ hcomm' hfix'
  have : g = cγ * (cγ⁻¹ * g * cγ) * cγ⁻¹ := by group
  rw [this, h1]
  group

end Plane

section Final


theorem innerPlaneBalance_reeGamma_F4_of_dvd {a : ℕ} {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hdvd : p ∣ (2 ^ (2 * a + 1)) ^ 4 - 1) : InnerPlaneBalance p (ReeTag.F4.reeGamma K a) := by
  have hp5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h | h
    · have : p = 4 := by omega
      subst this
      norm_num at hp
    · exact h
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hle : 2 ^ (a + 1) ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases dvd_cases_of_dvd_pow_four_sub_one hp hdvd with h | h | h
  · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 1 := by
      have := int_dvd_sub_one' hq1 h
      exact_mod_cast this
    obtain ⟨P⟩ := exists_plane_phi1 hK hp hp3 hmM
    exact innerPlaneBalance_of_plane ha hK hp hp3 ⟨_, sylowShape_ree_phi1 hK hp hp5 h⟩ P
  · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 1 := by
      have := Int.natCast_dvd_natCast.2 h
      exact_mod_cast this
    obtain ⟨P⟩ := exists_plane_phi2 hK hp hp3 hmM
    exact innerPlaneBalance_of_plane ha hK hp hp3 ⟨_, sylowShape_ree_phi2 hK hp hp5 h⟩ P
  · rcases dvd_phi4_cases hp hp3 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) + 2 ^ (a + 1) + 1 := by
        have := Int.natCast_dvd_natCast.2 h1
        exact_mod_cast this
      obtain ⟨P⟩ := exists_plane_phi4p hK hp hp3 hmM
      exact innerPlaneBalance_of_plane ha hK hp hp3 ⟨_, sylowShape_ree_phi4 hK hp hp5 h⟩ P
    · have hmM : (p : ℤ) ∣ 2 ^ (2 * a + 1) - 2 ^ (a + 1) + 1 := by
        have := int_dvd_sub_add_one' hle h1
        exact_mod_cast this
      obtain ⟨P⟩ := exists_plane_phi4m hK hp hp3 hmM
      exact innerPlaneBalance_of_plane ha hK hp hp3 ⟨_, sylowShape_ree_phi4 hK hp hp5 h⟩ P

theorem reeF4InnerPlaneBalance_holds : ReeF4InnerPlaneBalance := by
  intro a K _ _ _ ha hK p hp hp5 hdvd
  exact innerPlaneBalance_reeGamma_F4_of_dvd ha hK hp (by omega) hdvd

end Final

end CFSG.HardMathSupport.Timmesfeld.LocalTwo.ReeF4Big

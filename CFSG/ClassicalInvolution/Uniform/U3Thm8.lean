module

public import CFSG.ClassicalInvolution.Uniform.U3Thm6
public import CFSG.ClassicalInvolution.Uniform.U3M11b
public import CFSG.ClassicalInvolution.Q3.OddCentralizerModels

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly CFSG.Blueprint
open scoped MatrixGroups

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Fact p.Prime] in
theorem ne_of_commutes_members (hΩ : HypOmegaModU (.sl2 p f) Ω) {A B : Subgroup G} (hA : A ∈ Ω)
    (hc : Commutes A B) : A ≠ B := by
  intro h
  obtain ⟨z, hz⟩ := hΩ.classical A hA
  obtain ⟨x, hx, y, hy, hxy⟩ := hz.exists_noncomm
  rw [← h] at hc
  exact hxy (hc x hx y hy)

end Members

section Connected

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}

theorem dConnected_of_connectedU (M : Ih8Model p f Ω t k e) (hΩ : HypOmegaModU (.sl2 p f) Ω)
    (hne : Ω.Nonempty) (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4)
    (hconn : RouteD.CommFamilyConnected (RouteD.ModelFund p t k e)) :
    Disconnected.DConnected Ω := by
  have hcls := M.fund_eq_cls hne hG2 hD4
  intro K hK J hJ
  obtain ⟨A, hA, rfl⟩ := (M.mem_iff K).mp hK
  obtain ⟨B, hB, rfl⟩ := (M.mem_iff J).mp hJ
  have h := hconn A (M.cls_sub hA) B (M.cls_sub hB)
  refine Relation.ReflTransGen.lift (fun U : Subgroup (modelUniv t k p e Fact.out).K =>
    U.map M.ψ) ?_ A B h
  rintro U V ⟨hU, hV, hc⟩
  have hU' : U ∈ M.cls := hcls ▸ hU
  have hV' : V ∈ M.cls := hcls ▸ hV
  have hcomm := ih8_commutes_map M.ψ hc
  exact ⟨M.map_mem hV', Disconnected.dAdj_of_commutes (M.map_mem hV')
    (ne_of_commutes_members hΩ (M.map_mem hU') hcomm) hcomm⟩

end Connected

section M11

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem classical_eq_of_mulEquiv_m11 (e : ↥NativeSporadic.M11 ≃* G) {K K' : Subgroup G} {z : G}
    (h : Q3.IsClassicalMember3 K z) (h' : Q3.IsClassicalMember3 K' z) : K = K' :=
  Subgroup.map_injective e.symm.injective
    (m11_classical_eq (h.map_mulEquiv e.symm) (h'.map_mulEquiv e.symm))

theorem noTwins_of_mulEquiv_m11 (e : ↥NativeSporadic.M11 ≃* G)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) : ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K := by
  intro K hK K' hK'
  obtain ⟨hK'Ω, z, hz, hz'⟩ := hK'
  obtain ⟨zK, hzK⟩ := hΩ.classical K hK
  obtain ⟨zK', hzK'⟩ := hΩ.classical K' hK'Ω
  have e1 : z = zK := hz.eq hzK.isUniqueInvolution_sl2
  have e2 : z = zK' := hz'.eq hzK'.isUniqueInvolution_sl2
  rw [e1] at hz
  have hzz : zK = zK' := e1.symm.trans e2
  subst hzz
  exact (classical_eq_of_mulEquiv_m11 e (hzK.toQ3 (by norm_num)) (hzK'.toQ3 (by norm_num))).symm

theorem dEdgeless_of_mulEquiv_m11 (e : ↥NativeSporadic.M11 ≃* G) (hΩ : HypOmegaModU (.sl2 3 1) Ω)
    (hcard : ∀ L ∈ Ω, Nat.card L = 24) : Disconnected.DEdgeless Ω := by
  have h24 : (2 : ℕ) ^ (Nat.factorization 24) 2 = 8 := by
    have h : (Nat.factorization 24) 2 = 3 := by
      rw [Nat.factorization_def _ Nat.prime_two]
      have h1 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow]
      have h0 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
      omega
    rw [h]
    norm_num
  have key : ∀ K ∈ Ω, ∀ J ∈ Ω, J ∉ omegaNbr Ω K := by
    intro K hK J hJ hnbr
    obtain ⟨-, hne, R, hR, hRJ, hRN⟩ := hnbr
    obtain ⟨J', hJ', P, rfl⟩ := hR
    obtain ⟨zK, hzK⟩ := hΩ.classical K hK
    obtain ⟨zJ, hzJ⟩ := hΩ.classical J hJ
    have hR2 : IsPGroup 2 ((P : Subgroup ↥J').map J'.subtype) := P.isPGroup'.map _
    have hR8 : Nat.card ((P : Subgroup ↥J').map J'.subtype) = 8 := by
      rw [Subgroup.card_map_of_injective J'.subtype_injective, Sylow.card_eq_multiplicity,
        hcard J' hJ', h24]
    exact hne (eq_of_two_group_le_normalizer_of_mulEquiv_m11 e (hzK.toQ3 (by norm_num))
      (hzJ.toQ3 (by norm_num)) hR2 hR8 hRJ hRN)
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact key K hK J hJ h
  · exact key J hJ K hK h

omit [Finite G] in
theorem exists_mulEquiv_m11 [IsSimpleGroup G] (D : OmegaLieU 3 1 Ω)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hne : Ω.Nonempty) (i : Fin D.card)
    (hc : D.kind i = Q3.CompData.m11) : Nonempty (↥NativeSporadic.M11 ≃* G) := by
  have hsurj : Function.Surjective (castHom hc (D.hom i)) := by
    have h := D.hom_surjective_of_simple hΩ hne i
    rw [← MonoidHom.range_eq_top] at h ⊢
    rw [range_castHom]
    exact h
  have hinj : Function.Injective (castHom hc (D.hom i)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact (castHom_ker_le_center hc (D.hom i) (D.ker_le_center i)).trans
      (Q3.center_m11_eq_bot Q3.m11Facts).le
  exact ⟨MulEquiv.ofBijective (castHom hc (D.hom i)) ⟨hinj, hsurj⟩⟩

omit [Finite G] in
theorem false_of_sl23_component [IsSimpleGroup G] [Finite G] (D : OmegaLieU 3 1 Ω)
    (hΩ : HypOmegaModU (.sl2 3 1) Ω) (hne : Ω.Nonempty) (hcard : D.card = 1) (i : Fin D.card)
    (hc : D.kind i = Q3.CompData.sl23) : False := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  obtain ⟨j, R, hR, hKR⟩ := D.fundamental K hK
  obtain rfl : j = i := Fin.ext (by have := i.2; have := j.2; omega)
  obtain ⟨R', hR', hRR⟩ := exists_map_castHom hc (D.hom j) hR
  have hR'top : R' = ⊤ := Set.mem_singleton_iff.mp hR'
  have hsurj := D.hom_surjective_of_simple hΩ ⟨K, hK⟩ j
  have hKtop : K = ⊤ := by
    rw [hKR, ← hRR, hR'top, Subgroup.map_top, range_castHom]
    exact MonoidHom.range_eq_top.mpr hsurj
  rw [hKtop] at hz
  exact hz.false_of_top

end M11

section Inputs

@[expose] def Ih8G2D4EdgeU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → (∀ J ∈ Ω, AEmpty Ω J) →
      (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
        ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ),
          Nonempty (Ih8Model 3 1 Ω t k e) → (t = .G2 ∨ t = .trialityD4) →
            Disconnected.DEdgeless Ω ∨ Disconnected.DConnected Ω

@[expose] def Ih8ThreeU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)),
    HypOmegaModU (.sl2 3 1) Ω → (∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J) →
      ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (k e : ℕ),
        Nonempty (Ih8Model 3 1 Ω t k e) → ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) →
          Disconnected.DEdgeless Ω

end Inputs

section Thm8

theorem thm8TypedBelowU_three_of (hG2D4 : Ih8G2D4EdgeU) (hThree : Ih8ThreeU) {n : ℕ}
    (hn : CITBelowT (.sl2 3 1) n) : Thm8TypedBelowU 3 1 n := by
  intro hp2 _ G _ _ _ hlt Ω hΩ hA hne htrans hNE hNC
  obtain ⟨D, hcard⟩ := exists_omegaLieU_of_simple hn hlt hΩ hne
  let i : Fin D.card := ⟨0, by omega⟩
  rcases D.valid i with ⟨t, k, e, ht, hadm, he, hc⟩ | ⟨h3, hc | hc⟩
  · have hLie : HasLieTypeU 3 1 Ω t k := ⟨D, hcard, i, e, he, ht, hadm, hc⟩
    let M := D.toIh8Model hΩ hne hcard i ht hadm he hc
    by_cases hG2d4 : t = .G2 ∨ t = .trialityD4
    · exfalso
      rcases hG2D4 G Ω hΩ hA htrans t k e ⟨M⟩ hG2d4 with h | h
      · exact hNE h
      · exact hNC h
    have hG2 : t ≠ .G2 := fun h => hG2d4 (Or.inl h)
    have hD4 : t ≠ .trialityD4 := fun h => hG2d4 (Or.inr h)
    have hef : e = 1 := he.resolve_right fun h => hD4 h.1
    subst hef
    have hA1 : ¬ (t = .PSL ∧ k = 2) := by
      rintro ⟨rfl, rfl⟩
      exact hadm.2.2.2.2 (by simp)
    have hthree : ((t = .PSL ∧ k = 3) ∨ (t = .PSU ∧ k = 3)) → False := fun h3' =>
      hNE (hThree G Ω hΩ htrans t k 1 ⟨M⟩ h3')
    rcases tag_casesU hp2 ht hadm hG2 hD4 with hconn | hsmall
    · exact (hNC (dConnected_of_connectedU M hΩ hne hG2 hD4 hconn)).elim
    · rcases hsmall with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hk2 : 2 ≤ k := hadm.2.2.1
        have : k = 2 ∨ k = 3 ∨ k = 4 := by omega
        rcases this with rfl | rfl | rfl
        · exact (hA1 ⟨rfl, rfl⟩).elim
        · exact (hthree (Or.inl ⟨rfl, rfl⟩)).elim
        · exact ⟨6, true, by norm_num, by norm_num, .PSL, 4,
            Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩), hLie⟩
      · have hk3 : 3 ≤ k := hadm.2.2.1
        have : k = 3 ∨ k = 4 := by omega
        rcases this with rfl | rfl
        · exact (hthree (Or.inr ⟨rfl, rfl⟩)).elim
        · exact ⟨6, false, by norm_num, by norm_num, .PSU, 4,
            Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)), hLie⟩
      · exact ⟨5, true, by norm_num, by norm_num, .PSp, 2, Or.inl ⟨rfl, rfl, rfl⟩, hLie⟩
      · exact ⟨7, true, by norm_num, by norm_num, .POmegaOdd, 3,
          Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, rfl, rfl⟩))), hLie⟩
      · exact ⟨8, true, by norm_num, by norm_num, .POmegaPlus, 4,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, by norm_num, rfl, rfl, rfl⟩)))),
          hLie⟩
      · exact ⟨8, false, by norm_num, by norm_num, .POmegaMinus, 4,
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by norm_num, by norm_num, rfl, rfl, rfl⟩)))),
          hLie⟩
  · exact (false_of_sl23_component D hΩ hne hcard i hc).elim
  · obtain ⟨e⟩ := exists_mulEquiv_m11 D hΩ hne i hc
    exact (hNE (dEdgeless_of_mulEquiv_m11 e hΩ (D.card_eq h3))).elim

end Thm8

end CFSG.ClassicalInvolution.Uniform

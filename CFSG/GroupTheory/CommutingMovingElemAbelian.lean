module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG

open CFSG.Open

variable {F X G : Type} [Field F] [AddCommGroup X] [Module F X] [Group G] [Finite G]

private noncomputable def fixator (act : G →* (X ≃ₗ[F] X)) (u : X) : Subgroup G where
  carrier := {g | act g u = u}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change act (g * h) u = u
    rw [map_mul, LinearEquiv.mul_apply, hh, hg]
  inv_mem' := by
    intro g hg
    have h : (act g)⁻¹ (u) = u := by
      have := congrArg (fun x => (act g)⁻¹ x) hg
      simpa using this.symm
    simpa [map_inv] using h

theorem exists_elemAbelian_of_commuting_moving {ι : Type} [Fintype ι] {r : ℕ} (hr : r.Prime)
    {H : Subgroup G} (t : ι → G) (u : ι → X) (act : G →* (X ≃ₗ[F] X))
    (hmem : ∀ i, t i ∈ H)
    (hord : ∀ i, orderOf (t i) = r)
    (hcomm : ∀ i j, Commute (t i) (t j))
    (hmove : ∀ i (a : ℤ), act (t i ^ a) (u i) = u i → (r : ℤ) ∣ a)
    (hfix : ∀ i j, i ≠ j → act (t i) (u j) = u j) :
    ∃ T : Subgroup G, T ≤ H ∧ IsElemAbelian r T ∧ Nat.card T = r ^ Nat.card ι ∧
      Nat.card ι ≤ CFSG.Open.pRank r T := by
  classical
  let Hcyc : ι → Subgroup G := fun i => Subgroup.zpowers (t i)
  have hHle : ∀ i, Hcyc i ≤ H := fun i => Subgroup.zpowers_le.mpr (hmem i)
  have hind : iSupIndep Hcyc := by
    rw [iSupIndep_def]
    intro i
    rw [Subgroup.disjoint_def]
    intro x hx hxsup
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hFix : ∀ y ∈ (⨆ (j) (_ : j ≠ i), Hcyc j), act y (u i) = u i := by
      intro y hy
      refine Subgroup.iSup_induction (S := fun j => ⨆ (_ : j ≠ i), Hcyc j)
        (C := fun z => act z (u i) = u i) hy ?_ ?_ ?_
      · intro j z hz
        refine Subgroup.iSup_induction (S := fun _ : j ≠ i => Hcyc j)
          (C := fun z => act z (u i) = u i) hz ?_ ?_ ?_
        · intro hij w hw
          have hmem : t j ∈ fixator act (u i) := hfix j i hij
          exact Subgroup.zpowers_le.mpr hmem hw
        · exact (fixator act (u i)).one_mem'
        · intro x y hx hy
          exact (fixator act (u i)).mul_mem hx hy
      · exact (fixator act (u i)).one_mem'
      · intro x y hx hy
        exact (fixator act (u i)).mul_mem hx hy
    have hfixu : act (t i ^ a) (u i) = u i := hFix (t i ^ a) hxsup
    have hz : (t i) ^ a = 1 := by
      obtain ⟨c, hc⟩ := hmove i a (by simpa using hfixu)
      rw [hc, zpow_mul, ← hord i, zpow_natCast, pow_orderOf_eq_one, one_zpow]
    simpa using hz
  have hCycComm : ∀ i, IsMulCommutative (Hcyc i) := by
    intro i
    rw [isMulCommutative_iff]
    intro x y
    apply Subtype.ext
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← ha, ← hb, ← zpow_add, ← zpow_add, add_comm]
  let φ : ∀ i, Hcyc i →* G := fun i => (Hcyc i).subtype
  have hcommφ : Pairwise fun i j => ∀ x y, Commute (φ i x) (φ j y) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp x.2
    obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp y.2
    change Commute (x : G) (y : G)
    rw [← ha, ← hb]
    exact (hcomm i j).zpow_left a |>.zpow_right b
  let f : (∀ i, Hcyc i) →* G := MonoidHom.noncommPiCoprod φ hcommφ
  have hf : Function.Injective f :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep (ϕ := φ) (hcomm := hcommφ)
      (by simpa [φ] using hind) (fun i => Subgroup.subtype_injective (Hcyc i))
  let T : Subgroup G := f.range
  have hTcl : T = Subgroup.closure (Set.range t) := by
    rw [show T = f.range from rfl, MonoidHom.noncommPiCoprod_range]
    rw [show (⨆ i, (φ i).range) = ⨆ i, Hcyc i from by simp [φ]]
    conv_lhs => rw [show (⨆ i, Hcyc i) = ⨆ i, Subgroup.closure ({t i} : Set G) from by
      simp [Hcyc, Subgroup.zpowers_eq_closure]]
    rw [← Subgroup.closure_iUnion]
    congr 1
    ext x
    simp [Set.mem_iUnion, Set.mem_range, Set.mem_singleton_iff, eq_comm]
  have hTle : T ≤ H := by
    rw [show T = f.range from rfl, MonoidHom.noncommPiCoprod_range]
    rw [show (⨆ i, (φ i).range) = ⨆ i, Hcyc i from by simp [φ]]
    exact iSup_le hHle
  have hcardH : Nat.card (∀ i, Hcyc i) = r ^ Nat.card ι := by
    rw [Nat.card_pi]
    trans ∏ _i : ι, r
    · exact Finset.prod_congr rfl fun i _ => by rw [Nat.card_zpowers, hord i]
    · rw [Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have hTcard : Nat.card T = r ^ Nat.card ι := by
    rw [show T = f.range from rfl, ← hcardH]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hTelem : IsElemAbelian r T := by
    rw [hTcl]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
      exact hcomm i j
    · rintro _ ⟨i, rfl⟩
      rw [← hord i]
      exact pow_orderOf_eq_one _
  have hTrank : Nat.card ι ≤ CFSG.Open.pRank r T :=
    CFSG.SectionRank.le_pRank hr.one_lt le_rfl hTelem hTcard
  exact ⟨T, hTle, hTelem, hTcard, hTrank⟩

end CFSG

end

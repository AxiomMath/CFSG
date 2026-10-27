module

public import CFSG.LieType.HighestRoot.CentIsogeny
public import CFSG.LieType.HighestRoot.CentChevalleyData
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny

public section

namespace CFSG.LieType.HighestRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.ChevAut

section Minuscule

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]

theorem isPGroup_minRootGroup {p : ℕ} [Fact p.Prime] [CharP k p] (γ : Fin τ.rank → ℤ) :
    IsPGroup p (hV.rootGroup k γ) := by
  rintro ⟨_, c, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  have hc : c ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [pow_one, Subgroup.coe_pow, ← map_pow, hc, map_one]
  rfl

theorem card_rankOne_le [Finite k] (i : Fin τ.rank) :
    Nat.card ↥(hV.rootGroup k (Pi.single i 1) ⊔ hV.rootGroup k (-Pi.single i 1)) ≤
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
  classical
  have : Fintype k := Fintype.ofFinite k
  choose F hF using fun g : ↥(hV.rootGroup k (Pi.single i 1) ⊔
    hV.rootGroup k (-Pi.single i 1)) => hV.exists_of_mem_rankOne k i g.2
  refine Nat.card_le_card_of_injective F fun g g' h => Subtype.ext (hV.endo_injective k ?_)
  rw [hF g, hF g', h]

end Minuscule

theorem eq_one_of_map_eq_one_of_card_le {G C : Type*} [Group G] [Group C] [Finite G]
    {k : Type} [Field k] (θ : G →* C) {J : Subgroup G}
    (e : J.map θ ≃* Matrix.SpecialLinearGroup (Fin 2) k)
    (hcard : Nat.card J ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k)) :
    ∀ x ∈ J, θ x = 1 → x = 1 := by
  have hbij := (θ.subgroupMap_surjective J).bijective_of_nat_card_le
    (by rw [Nat.card_congr e.toEquiv]; exact hcard)
  intro x hx h1
  have h : θ.subgroupMap J ⟨x, hx⟩ = θ.subgroupMap J 1 :=
    Subtype.ext (by rw [MonoidHom.subgroupMap_apply_coe, map_one, h1]; rfl)
  exact congrArg Subtype.val (hbij.1 h)

section Adjoint

variable {τ : Tag} {K : Type} [Field K]

theorem nonempty_rankOneGroup_adjDatum_equiv
    (hK : ringChar K ≠ 2) (i : Fin τ.rank) :
    Nonempty (rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single i 1) ≃*
      Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨hle, ⟨e⟩, -⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK (isRoot_single τ i)
  exact ⟨(MulEquiv.subgroupCongr (rankOneGroup_adjDatum _ (isRoot_single τ i))).trans
    ((Subgroup.subgroupOfEquivOfLe hle).trans e.symm)⟩

end Adjoint

section E6

variable (k : Type) [Field k] [Finite k]

theorem centralizerCondition_e6_of_check
    (hK : ringChar k ≠ 2) {i : Fin (Tag.rank .E6)}
    {wit : List ℕ} (hc : isolatedCheck .E6 i wit = true) :
    CentralizerCondition k (e6Data_valid.rootGroup k (Pi.single i 1) ⊔
      e6Data_valid.rootGroup k (-Pi.single i 1)) := by
  have := finite_minGroup e6Data_valid k
  have : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have hX : ∀ α, IsRoot .E6 α → (e6Data_valid.rootGroup k α).map (e6Isogeny k) =
      rootGroup (rootOperatorFamily .E6) k α := fun α hα => map_e6Isogeny_rootGroup k hα
  obtain ⟨e⟩ := nonempty_rankOneGroup_adjDatum_equiv (τ := .E6) hK i
  refine centralizerCondition_of_isogeny (p := ringChar k) (e6Isogeny k)
    (e6Data_valid.rootGroup k) noG2_E6' hK (e6Isogeny_ker_le_center k)
    (e6Isogeny_not_dvd_card_ker (p := ringChar k) k) hX
    (fun α _ => isPGroup_minRootGroup e6Data_valid k α) (symmetrizer_le_one .E6 rfl _) hc ?_
  exact eq_one_of_map_eq_one_of_card_le (e6Isogeny k)
    ((MulEquiv.subgroupCongr (map_sup_eq_rankOneGroup _ _ hX (isRoot_single _ _))).trans e)
    (card_rankOne_le e6Data_valid k i)

theorem centralizerCondition_e6
    (hK : ringChar k ≠ 2) :
    CentralizerCondition k (rankOneGroup (e6Datum k) (Pi.single (idx0 .E6) 1)) :=
  centralizerCondition_e6_of_check k hK isolatedCheck_E6

theorem highestRootCZ_e6Datum
    (hK : ringChar k ≠ 2) : HighestRootCZ (e6Datum k) k :=
  ⟨Pi.single (idx0 .E6) 1, (isLongest_single_E6 rfl _ (idx0 .E6)).1,
    (isLongest_single_E6 rfl _ (idx0 .E6)).2, centralizerCondition_e6 k hK⟩

end E6

section E7

variable (k : Type) [Field k] [Finite k]

theorem centralizerCondition_e7
    (hK : ringChar k ≠ 2) :
    CentralizerCondition k (rankOneGroup (e7Datum k) (Pi.single (idx0 .E7) 1)) := by
  have := finite_minGroup e7Data_valid k
  have : Fact (ringChar k).Prime := ⟨CharP.prime_ringChar k⟩
  have hX : ∀ α, IsRoot .E7 α → (e7Data_valid.rootGroup k α).map (e7Isogeny k) =
      rootGroup (rootOperatorFamily .E7) k α := fun α hα => map_e7Isogeny_rootGroup k hα
  obtain ⟨e⟩ := nonempty_rankOneGroup_adjDatum_equiv (τ := .E7) hK (idx0 .E7)
  refine centralizerCondition_of_isogeny (p := ringChar k) (e7Isogeny k)
    (e7Data_valid.rootGroup k) noG2_E7' hK (e7Isogeny_ker_le_center k)
    (e7Isogeny_not_dvd_card_ker (p := ringChar k) k) hX
    (fun α _ => isPGroup_minRootGroup e7Data_valid k α) (symmetrizer_le_one .E7 rfl _)
    isolatedCheck_E7 ?_
  exact eq_one_of_map_eq_one_of_card_le (e7Isogeny k)
    ((MulEquiv.subgroupCongr (map_sup_eq_rankOneGroup _ _ hX (isRoot_single _ _))).trans e)
    (card_rankOne_le e7Data_valid k (idx0 .E7))

theorem highestRootCZ_e7Datum
    (hK : ringChar k ≠ 2) : HighestRootCZ (e7Datum k) k :=
  ⟨Pi.single (idx0 .E7) 1, (isLongest_single_E7 rfl _ (idx0 .E7)).1,
    (isLongest_single_E7 rfl _ (idx0 .E7)).2, centralizerCondition_e7 k hK⟩

end E7

section Universal

open CFSG.LieType.Steinberg.Exceptional

variable (p f : ℕ) [Fact p.Prime]

theorem highestRootCZ_E6
    (hp : p ≠ 2) : HighestRootCZ (e6UniversalDatum p f) (GaloisField p f) :=
  highestRootCZ_e6Datum (GaloisField p f)
    (by rw [ringChar.eq (GaloisField p f) p]; exact hp)

theorem highestRootCZ_E7
    (hp : p ≠ 2) : HighestRootCZ (e7UniversalDatum p f) (GaloisField p f) :=
  highestRootCZ_e7Datum (GaloisField p f)
    (by rw [ringChar.eq (GaloisField p f) p]; exact hp)

end Universal

end CFSG.LieType.HighestRoot

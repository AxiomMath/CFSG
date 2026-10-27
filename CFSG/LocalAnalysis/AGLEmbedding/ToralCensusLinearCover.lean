module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinearCenter
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Cover
public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

@[expose] def KFactCoverLinear : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), IsComponentOf L ⊤ →
    Odd (Nat.card (Subgroup.center ↥L)) →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K] [CharP K 2], 3 ≤ n →
    ∀ e : ↥L ⧸ Subgroup.center ↥L ≃* LinearFlag.projectiveSL n K,
    ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L, Function.Surjective ρ ∧
      ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) ∧
      ∀ g, e (QuotientGroup.mk (ρ g)) = LinearFlag.proj n K g

namespace ToralCensus

open LinearFlag CFSG.GH74.Generic

theorem surjective_and_ker_le_of_compat {L : Type*} [Group L] (hL : commutator L = ⊤) {n : ℕ}
    {K : Type*} [Field K] (e : L ⧸ Subgroup.center L ≃* projectiveSL n K)
    (ρ : Matrix.SpecialLinearGroup (Fin n) K →* L)
    (hρ : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g) :
    Function.Surjective ρ ∧ ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  have hdec : ∀ x : L, ∃ s, ∃ z ∈ Subgroup.center L, x = z * ρ s := fun x => by
    obtain ⟨s, hs⟩ := proj_surjective n K (e (QuotientGroup.mk x))
    have hz : (ρ s)⁻¹ * x ∈ Subgroup.center L := QuotientGroup.eq.mp (e.injective (by
      rw [hρ, hs]))
    refine ⟨s, (ρ s)⁻¹ * x, hz, ?_⟩
    rw [← Subgroup.mem_center_iff.mp hz (ρ s), mul_inv_cancel_left]
  constructor
  · have hcomm : commutator L ≤ ρ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, z, hz, rfl⟩ := hdec x
      obtain ⟨t, w, hw, rfl⟩ := hdec y
      rw [CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hz hw,
        ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro x
    exact hcomm (hL ▸ Subgroup.mem_top x)
  · intro g hg
    rw [← scalars_eq_center, ← proj_eq_one_iff, ← hρ, MonoidHom.mem_ker.mp hg,
      QuotientGroup.mk_one, map_one]

theorem exists_compat_of_section {L : Type} [Group L] {n : ℕ} {K : Type} [Field K]
    (e : L ⧸ Subgroup.center L ≃* projectiveSL n K)
    (σ : Matrix.SpecialLinearGroup (Fin n) K →*
      ↥(CFSG.LieType.Steinberg.pullback (proj n K) (centralQuotientMap e)))
    (hσ : ∀ g, CFSG.LieType.Steinberg.pullbackFst _ _ (σ g) = g) :
    ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* L,
      ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g := by
  refine ⟨(MonoidHom.snd _ _).comp
    ((CFSG.LieType.Steinberg.pullback (proj n K) (centralQuotientMap e)).subtype.comp σ),
    fun g => ?_⟩
  have hmem := CFSG.LieType.Steinberg.mem_pullback.mp (σ g).2
  rw [← centralQuotientMap_apply]
  change centralQuotientMap e ((σ g : Matrix.SpecialLinearGroup (Fin n) K × L).2) = _
  rw [← hmem]
  exact congrArg (proj n K) (hσ g)

theorem card_ne_three_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] :
    Nat.card K ≠ 3 := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hcard⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hcard]
  intro h
  have h3 : 2 ^ (f : ℕ) % 2 = 1 := by rw [h]
  rw [Nat.pow_mod, Nat.mod_self, zero_pow f.ne_zero] at h3
  exact absurd h3 (by norm_num)

end ToralCensus

open ToralCensus LinearFlag CFSG.GH74.Generic in
theorem kFactCoverLinear_of_oddCenter
    (hZ : OddCenterLinear) : KFactCoverLinear := by
  intro Y _ _ L hL hodd n K _ _ _ hn e
  have hq := hL.2.2
  have : Group.IsPerfect ↥L := ⟨hq.1⟩
  suffices h : ∃ ρ : Matrix.SpecialLinearGroup (Fin n) K →* ↥L,
      ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g by
    obtain ⟨ρ, hρ⟩ := h
    obtain ⟨hs, hk⟩ := surjective_and_ker_le_of_compat hq.1 e ρ hρ
    exact ⟨ρ, hs, hk, hρ⟩
  have : Fintype K := Fintype.ofFinite K
  by_cases hK2 : Nat.card K = 2
  ·
    have hdvd := hZ Y L hL hodd n K ⟨e⟩
    have h1 : Nat.gcd n (Fintype.card K - 1) = 1 := by
      rw [← Nat.card_eq_fintype_card, hK2, show 2 - 1 = 1 from rfl, Nat.gcd_one_right]
    rw [h1, Nat.dvd_one] at hdvd
    have hZ1 : Subgroup.center ↥L = ⊥ := Subgroup.eq_bot_of_card_eq _ hdvd
    have hinj : Function.Injective (centralQuotientMap e) := by
      rw [← MonoidHom.ker_eq_bot_iff, centralQuotientMap_ker, hZ1]
    let φ := MulEquiv.ofBijective (centralQuotientMap e) ⟨hinj, centralQuotientMap_surjective e⟩
    refine ⟨φ.symm.toMonoidHom.comp (proj n K), fun g => ?_⟩
    rw [← centralQuotientMap_apply]
    exact φ.apply_symm_apply (proj n K g)
  by_cases h34 : n = 3 ∧ Nat.card K = 4
  · obtain ⟨rfl, hK4⟩ := h34
    have hmod := statedClassicalModel_of_projectiveSL_evenChar (f := 2) (by norm_num)
      (by rw [hK4]; norm_num) (by norm_num) (by omega) e
    exact CFSG.CGT.PushingUpLit.CGT6X.End4.exists_cover_l34 hmod hK4 e hodd
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hsep := CFSG.LieType.Steinberg.CentralExt.SLClosed.separating_of_card (m := m) (F := K)
      (by omega) hK2 (fun h => h34 ⟨by omega, h.2⟩)
      (fun h => card_ne_three_of_charTwo K h.2)
    obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_separating
      (by omega) hsep (CFSG.LieType.Steinberg.pullbackFst_surjective
        (β := proj (m + 1) K) (centralQuotientMap_surjective e))
      (CFSG.LieType.Steinberg.ker_pullbackFst_le_center (centralQuotientMap_ker e).le)
    exact exists_compat_of_section e σ hσ

theorem kFactCoverLinear_of_griess
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFactCoverLinear :=
  kFactCoverLinear_of_oddCenter (oddCenterLinear_of_griess hGA)

end CFSG.AGLEmbedding

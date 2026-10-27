module

public import CFSG.ClassicalInvolution.AschTight.C195
public import CFSG.ClassicalInvolution.AschTight.Hall196Syl

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ABGLocalTools CFSG.GorensteinWalter
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]

theorem isSylow2In_map_hom {A B : Type} [Group A] [Group B] [Finite A] (φ : A →* B)
    {P H : Subgroup A} (h : IsSylow2In P H) : IsSylow2In (P.map φ) (H.map φ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := isSylow2In_map_sylow (H.map φ)
    ((sylowOfIsSylow2In h).mapSurjective (MonoidHom.subgroupMap_surjective φ H))
  have h2 : (((sylowOfIsSylow2In h).mapSurjective (MonoidHom.subgroupMap_surjective φ H) :
      Sylow 2 ↥(H.map φ)) : Subgroup ↥(H.map φ)).map (H.map φ).subtype = P.map φ := by
    rw [Sylow.coe_mapSurjective, Subgroup.map_map]
    have h3 : (H.map φ).subtype.comp (φ.subgroupMap H) = φ.comp H.subtype := rfl
    rw [h3, ← Subgroup.map_map]
    change ((P.subgroupOf H).map H.subtype).map φ = P.map φ
    rw [Subgroup.map_subgroupOf_eq_of_le h.1]
  rw [h2] at h1
  exact h1

theorem eq_of_relIndex_eq_two {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (h2 : A.relIndex C = 2) (hB : ¬ B ≤ A) : B = C := by
  have h := Subgroup.relIndex_mul_relIndex A B C hAB hBC
  rw [h2] at h
  have hA : A.relIndex B ≠ 1 := fun h1 => hB (Subgroup.relIndex_eq_one.mp h1)
  have hb : B.relIndex C = 1 := by
    rcases Nat.dvd_prime Nat.prime_two |>.mp (Dvd.intro_left _ h) with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at h
      exact hA (by omega)
  exact le_antisymm hBC (Subgroup.relIndex_eq_one.mp hb)

theorem psl2MulAutOf_conj_eq (s : SL(2, F)) :
    psl2MulAutOf (MulAut.conj s) = MulAut.conj (QuotientGroup.mk s : PSL2 F) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H b => rfl

theorem congr_oddCoreQuotientAut_of_mem (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    {k : G} (hk : k ∈ K) :
    MulAut.congr e (oddCoreQuotientAut K (normalizerConj K ⟨k, Subgroup.le_normalizer hk⟩)) =
      MulAut.conj (e (QuotientGroup.mk ⟨k, hk⟩)) := by
  ext s
  obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm s)
  have hs : s = e (QuotientGroup.mk κ) := by rw [hκ, MulEquiv.apply_symm_apply]
  rw [hs, congr_oddCoreQuotientAut_apply, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1

theorem oddCoreQuotientAut_normalizerConj_eq_one_iff (n : Subgroup.normalizer (K : Set G)) :
    oddCoreQuotientAut K (normalizerConj K n) = 1 ↔ ∀ l ∈ K, ⁅(n : G), l⁆ ∈ Asc77.oddCoreOf K := by
  constructor
  · intro h l hl
    have h1 := congrArg (fun α : MulAut (K ⧸ classicalInvolutionOddCore K) =>
      α (QuotientGroup.mk (⟨l, hl⟩⁻¹ : K))) h
    simp only [MulAut.one_apply, oddCoreQuotientAut_mk] at h1
    refine ⟨_, QuotientGroup.eq.mp h1, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      normalizerConj_apply_coe, commutatorElement_def]
    group
  · intro h
    ext x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rw [oddCoreQuotientAut_mk, MulAut.one_apply]
      refine QuotientGroup.eq.mpr ?_
      obtain ⟨y, hy, hyx⟩ := h _ (K.inv_mem x.2)
      have hxy : (normalizerConj K n x)⁻¹ * x = y := by
        apply Subtype.ext
        rw [show ((y : K) : G) = K.subtype y from rfl, hyx]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe,
          commutatorElement_def]
        group
      rw [hxy]
      exact hy

theorem finite_pGammaL2 [Finite F] : Finite (PGammaL2 F) := by
  have : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) fun e e' h => by
      ext x
      exact congrFun h x
  exact Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) fun x y h =>
    SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

variable [Finite F] {p f : ℕ} [Fact p.Prime]

theorem normalizerToPGammaL2Mod_of_mem (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    {k : G} (hk : k ∈ K) :
    normalizerToPGammaL2Mod e hFcard hF h3 ⟨k, Subgroup.le_normalizer hk⟩ =
      SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk (e (QuotientGroup.mk ⟨k, hk⟩)) : PSL2 F)) := by
  apply pGammaL2ToMulAutPSL2_injective F hF h3
  rw [pGammaL2ToMulAutPSL2_normalizerToPGammaL2Mod, pGammaL2ToMulAutPSL2_inl,
    pgl2InnerAutPSL2_toPGL, congr_oddCoreQuotientAut_of_mem e hk, psl2MulAutOf_conj_eq]

theorem normalizerToPGammaL2Mod_mem_pGammaL2PSLRange
    (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) (hFcard : Nat.card F = p ^ f)
    (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F) {k : G} (hk : k ∈ K) :
    normalizerToPGammaL2Mod e hFcard hF h3 ⟨k, Subgroup.le_normalizer hk⟩ ∈
      pGammaL2PSLRange F :=
  (mem_pGammaL2PSLRange_iff F _).mpr ⟨_, (normalizerToPGammaL2Mod_of_mem e hFcard hF h3 hk).symm⟩

theorem map_subgroupOf_eq_pGammaL2PSLRange (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F) :
    (K.subgroupOf (Subgroup.normalizer (K : Set G))).map (normalizerToPGammaL2Mod e hFcard hF h3) =
      pGammaL2PSLRange F := by
  apply le_antisymm
  · rintro _ ⟨n, hn, rfl⟩
    exact normalizerToPGammaL2Mod_mem_pGammaL2PSLRange e hFcard hF h3
      (Subgroup.mem_subgroupOf.mp hn)
  · intro x hx
    obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff F x).mp hx
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_surjective (e.symm s)
    refine ⟨⟨κ, Subgroup.le_normalizer κ.2⟩, Subgroup.mem_subgroupOf.mpr κ.2, ?_⟩
    rw [normalizerToPGammaL2Mod_of_mem e hFcard hF h3 κ.2]
    have hs : e (QuotientGroup.mk κ) = s := by rw [hκ, MulEquiv.apply_symm_apply]
    rw [← hs]

theorem normalizerToPGammaL2Mod_eq_one_iff (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (hFcard : Nat.card F = p ^ f) (hF : IsOddPrimePower (Nat.card F)) (h3 : 3 < Nat.card F)
    (n : Subgroup.normalizer (K : Set G)) :
    normalizerToPGammaL2Mod e hFcard hF h3 n = 1 ↔ ∀ l ∈ K, ⁅(n : G), l⁆ ∈ Asc77.oddCoreOf K := by
  rw [← oddCoreQuotientAut_normalizerConj_eq_one_iff]
  refine ⟨oddCoreQuotientAut_eq_one_of_normalizerToPGammaL2Mod_eq_one e hFcard hF h3,
    fun h => ?_⟩
  apply pGammaL2ToMulAutPSL2_injective F hF h3
  rw [pGammaL2ToMulAutPSL2_normalizerToPGammaL2Mod, h, map_one, map_one]
  ext x
  induction x using QuotientGroup.induction_on with
  | H b => rfl

end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

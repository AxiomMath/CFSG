module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingDefs
public import CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCoverAlternating
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.Bridge
public import CFSG.Walter.Cited.CentralSplit

public section

namespace CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover

open CFSG.Open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem center_eq_of_fusionIsBenderGroup {D : Type*} [Group D] [Finite D] {Z : Subgroup D}
    [Z.Normal] (hZc : Z ≤ Subgroup.center D) (hperf : commutator D = ⊤)
    (hB : fusionIsBenderGroup (D ⧸ Z)) : Subgroup.center D = Z := by
  have : Group.IsPerfect D := ⟨hperf⟩
  have : IsSimpleGroup (D ⧸ Z) :=
    QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  refine le_antisymm ?_ hZc
  have : ((Subgroup.center D).map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.instNormalCenter.map _ (QuotientGroup.mk'_surjective Z)
  rcases Subgroup.Normal.eq_bot_or_eq_top ((Subgroup.center D).map (QuotientGroup.mk' Z)) with
    h | h
  · intro x hx
    have hx' : QuotientGroup.mk' Z x ∈ (Subgroup.center D).map (QuotientGroup.mk' Z) :=
      ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).1 hx'
  · exfalso
    obtain ⟨a, b, hab⟩ := QuasithinUnique.RankOneRecog.exists_noncommuting_of_perfect hB
    have hmem : ∀ c : D ⧸ Z, ∃ x ∈ Subgroup.center D, QuotientGroup.mk' Z x = c := fun c => by
      have hc : c ∈ (Subgroup.center D).map (QuotientGroup.mk' Z) := h ▸ Subgroup.mem_top c
      exact hc
    obtain ⟨x, hx, rfl⟩ := hmem a
    obtain ⟨y, -, rfl⟩ := hmem b
    exact hab (by rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx y).symm])

theorem exists_eq_conj_of_suzuki {B : Type} [Group B] {a : ℕ} (ha : 1 ≤ a) (e : B ≃* Sz a)
    (α : MulAut B) (hα2 : α * α = 1) : ∃ b : B, α = MulAut.conj b := by
  obtain ⟨e'⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hodd := (CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity.{0} B 2
    (2 * a + 1) ⟨rfl, a, ha, GaloisField 2 (2 * a + 1), inferInstance, inferInstance, rfl,
      GaloisField.card 2 (2 * a + 1) (by omega), ⟨e.trans e'⟩⟩).1.2.2
  set o : Outer B := QuotientGroup.mk α
  have ho2 : o ^ 2 = 1 := by rw [pow_two, ← QuotientGroup.mk_mul, hα2, QuotientGroup.mk_one]
  have ho : orderOf o = 1 :=
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ho2)
      (Nat.coprime_two_left.mpr hodd)).eq_one_of_dvd (orderOf_dvd_natCard o)
  have hin : α ∈ inner B := (QuotientGroup.eq_one_iff α).mp (orderOf_eq_one_iff.mp ho)
  obtain ⟨b, hb⟩ : ∃ b, MulAut.conj b = α := hin
  exact ⟨b, hb.symm⟩

theorem exists_eq_conj_of_fixes_sylow {D : Type} [Group D] [Finite D] [Group.IsPerfect D]
    (hZ2 : Nat.card (Subgroup.center D) = 2) (hB : fusionIsBenderGroup (D ⧸ Subgroup.center D))
    (α : MulAut (D ⧸ Subgroup.center D)) (hα2 : α * α = 1)
    (S : Sylow 2 (D ⧸ Subgroup.center D)) (hα : ∀ s ∈ (S : Subgroup _), α s = s) :
    ∃ b, α = MulAut.conj b := by
  have hp : IsPGroup 2 (Subgroup.center D) := IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  have hne : Subgroup.center D ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hZ2; omega
  have hB' := hB
  rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · rcases eq_or_lt_of_le hf with rfl | hf3
    ·
      have : IsSimpleGroup (D ⧸ Subgroup.center D) :=
        QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB'
      exact exists_eq_conj_of_card_sixty
        ((Nat.card_congr e.toEquiv).trans CFSG.Walter.Suzuki.card_psl24) α S hα
    ·
      exfalso
      have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
      let eJ := e.trans (CFSG.ShultStronglyClosedTI.glaSL2EquivNative f hf hcard).symm
      let η := eJ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center D))
      have hsurj : Function.Surjective η := eJ.surjective.comp (QuotientGroup.mk'_surjective _)
      have hker : η.ker = Subgroup.center D :=
        QuasithinUnique.RankOneRecog.ker_comp_centerQuotient eJ
      exact hne (hker.symm.trans
        (CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_trivial f hf3 hcard η
          hsurj hker.le (hker.symm ▸ hp)).1)
  ·
    exact absurd (QuasithinUnique.RankOneRecog.unitary_center_eq_bot hp hf e) hne
  · exact exists_eq_conj_of_suzuki ha e α hα2

end CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.BenderDoubleCover
open CFSG.ComponentClassification.PerfectAutomorphisms

theorem benderDoubleCoverRigidity : BenderDoubleCoverRigidity := by
  rintro D _ _ Z _ hZc hZ2 hperf hB φ hφ2 ⟨R, hR⟩
  have : Group.IsPerfect D := ⟨hperf⟩
  have hcenter : Subgroup.center D = Z := center_eq_of_fusionIsBenderGroup hZc hperf hB
  have hZ2' : Nat.card (Subgroup.center D) = 2 := hcenter ▸ hZ2
  have hBQ : fusionIsBenderGroup (D ⧸ Subgroup.center D) :=
    QuasithinUnique.RankOneRecog.fusionIsBenderGroup_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hcenter).symm hB
  have hp : IsPGroup 2 (Subgroup.center D) := IsPGroup.of_card (n := 1) (by rw [hZ2', pow_one])
  obtain ⟨b, hb⟩ := exists_eq_conj_of_fixes_sylow hZ2' hBQ (centerQuotientHom D φ)
    (by rw [← map_mul, hφ2, map_one]) (R.mapSurjective (QuotientGroup.mk'_surjective _))
    (fun s hs => by
      rw [Sylow.coe_mapSurjective] at hs
      obtain ⟨q, hq, rfl⟩ := hs
      exact (onCenterQuotient_apply_mk φ q).trans (congrArg _ (hR q hq)))
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center D) b
  have hφ : φ = MulAut.conj r := by
    refine centerQuotientHom_injective D (hb.trans (MulEquiv.ext fun x => ?_))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center D) x
    change _ = onCenterQuotient (MulAut.conj r) (QuotientGroup.mk' _ x)
    rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
      map_inv]
  have hrc : r ∈ Subgroup.centralizer ((R : Subgroup D) : Set D) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := hR q hq
    rw [hφ, MulAut.conj_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  by_cases hrZ : r ∈ Subgroup.center D
  · rw [hφ]
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hrZ x).symm,
      mul_inv_cancel_right]
  · have hbot := QuasithinUnique.RankOneRecog.center_eq_bot_of_noncentral_sylow_centralizer hp hBQ
      R hrc hrZ
    rw [hbot, Subgroup.card_bot] at hZ2'
    omega

end CFSG.ComponentClassification.AschbacherStrongEmbedding

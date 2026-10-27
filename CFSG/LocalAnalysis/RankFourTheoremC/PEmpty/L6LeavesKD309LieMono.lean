module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Main
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Plane
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieLift

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
open CFSG.LocalAnalysis.RankThreeUC.S15.ACore

@[expose] def KD309MonoModel : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (P : Sylow 5 Y) (x z : Y), Plane63 5 Y P x z →
    ∀ L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf L ⊤ →
      (∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L) →
      I291P65.Is29a ↥L → Nat.card (P : Subgroup Y) = 5 ^ 5 →
      ∃ Φ : M5 →* (Y ⧸ primeComplementCore (G := Y) 5), KerSc Φ ∧
        Nat.card (Pm.map Φ) = 5 ^ 5 ∧
        ∃ w : Y ⧸ primeComplementCore (G := Y) 5,
          w * Φ (monS (C := C5) sig5) * w⁻¹ = (Φ (mT ddv))⁻¹

theorem kd309LieMono_of_model (hM : KD309MonoModel) : KD309LieMono := by
  intro Y _ _ P x z hpl L hL hLu h29 hPcard
  obtain ⟨Φ, hΦ, hcard, hdft⟩ := hM Y P x z hpl L hL hLu h29 hPcard
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set O : Subgroup Y := primeComplementCore (G := Y) 5 with hO
  have hOcop : ¬ 5 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp (primeComplementCore_coprime 5)
  set π : Y →* Y ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hpP : IsPGroup 5 (P : Subgroup Y) := P.isPGroup'
  have inj : ∀ a ∈ (P : Subgroup Y), ∀ b ∈ (P : Subgroup Y), π a = π b → a = b :=
    inj_of_pgroup O hOcop hpP
  obtain ⟨hxP, hzP, hx5, hz5, hx1, hz1⟩ := I291P65.plane_facts hpl.prime hpl.plane
  have hzo : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  let Pb : Sylow 5 (Y ⧸ O) := Sylow.mapSurjective hπs P
  have hPb : (Pb : Subgroup (Y ⧸ O)) = (P : Subgroup Y).map π := rfl
  have hPbcard : Nat.card (Pb : Subgroup (Y ⧸ O)) = 5 ^ 5 := by
    rw [hPb, card_map_eq_of_inj π _ inj, hPcard]
  have hQp : IsPGroup 5 (Pt Φ) := IsPGroup.of_card (n := 5) hcard
  obtain ⟨Q', hQQ'⟩ := hQp.exists_le_sylow
  have hQ'card : Nat.card (Q' : Subgroup (Y ⧸ O)) = 5 ^ 5 := by
    have h1 := Q'.card_eq_multiplicity
    have h2 := Pb.card_eq_multiplicity
    rw [h1, ← h2, hPbcard]
  have hQeq : Pt Φ = (Q' : Subgroup (Y ⧸ O)) :=
    Subgroup.eq_of_le_of_card_ge hQQ' (by rw [hQ'card]; exact hcard.ge)
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (Y ⧸ O) Q' Pb
  have hconj : (Pt Φ).map (MulAut.conj y).toMonoidHom = (P : Subgroup Y).map π := by
    rw [← hPb, ← hy, Sylow.coe_subgroup_smul, hQeq]
    ext u
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      have h : (MulAut.conj y)⁻¹ • ((MulAut.conj y).toMonoidHom q) = q :=
        (MulAut.conj y).symm_apply_apply q
      rw [h]
      exact hq
    · intro hu
      refine ⟨(MulAut.conj y)⁻¹ • u, hu, ?_⟩
      exact (MulAut.conj y).apply_symm_apply u
  let Φ' : M5 →* (Y ⧸ O) := (MulAut.conj y).toMonoidHom.comp Φ
  have hΦ' : KerSc Φ' := by
    intro m
    change (MulAut.conj y) (Φ m) = 1 ↔ _
    rw [map_eq_one_iff _ (MulAut.conj y).injective]
    exact hΦ m
  have hPtΦ' : Pt Φ' = (P : Subgroup Y).map π := by
    rw [← hconj]
    unfold Pt
    rw [Subgroup.map_map]
  have hdft' : ∃ w : Y ⧸ O, w * Φ' (monS (C := C5) sig5) * w⁻¹ = (Φ' (mT ddv))⁻¹ := by
    obtain ⟨w, hw⟩ := hdft
    refine ⟨y * w * y⁻¹, ?_⟩
    have e1 : Φ' (monS (C := C5) sig5) = y * Φ (monS (C := C5) sig5) * y⁻¹ := rfl
    have e2 : Φ' (mT ddv) = y * Φ (mT ddv) * y⁻¹ := rfl
    rw [e1, e2]
    calc y * w * y⁻¹ * (y * Φ (monS (C := C5) sig5) * y⁻¹) * (y * w * y⁻¹)⁻¹
        = y * (w * Φ (monS (C := C5) sig5) * w⁻¹) * y⁻¹ := by group
      _ = y * (Φ (mT ddv))⁻¹ * y⁻¹ := congrArg (fun t => y * t * y⁻¹) hw
      _ = (y * Φ (mT ddv) * y⁻¹)⁻¹ := by group
  have hπz1 : π z ≠ 1 := by
    intro h1
    exact hz1 (inj z hzP 1 (one_mem _) (by rw [h1, map_one]))
  have hzcπ : ∀ p ∈ Pt Φ', p * π z = π z * p := by
    rw [hPtΦ']
    rintro _ ⟨p0, hp0, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hpl.z_central p0 hp0
    rw [← map_mul, ← map_mul, this]
  have hπzP : π z ∈ Pt Φ' := by
    rw [hPtΦ']
    exact ⟨z, hzP, rfl⟩
  obtain ⟨g', h', cfg⟩ := mon_cfg hΦ' hπzP hzcπ hπz1 hdft'
  rw [hPtΦ'] at cfg
  exact exists_cfg_of_quotient O hOcop hpP hzP hzo cfg

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

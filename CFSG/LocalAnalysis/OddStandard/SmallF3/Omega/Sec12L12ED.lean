module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EFrame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}

private theorem sec12E_relIndex_odd (F : Sec12Frame t L S) :
    Odd ((secXR t S L).relIndex (secCMB t S L)) := by
  have hRP : secR t ≤ secCMB t S L := (sec12E_R_le_C F).trans (sec12E_C_le_P F)
  have hXP : secXR t S L ≤ secCMB t S L := inf_le_left
  have hPM : secCMB t S L ≤ secM t S L := inf_le_left
  have hRnorm : ((secR t).subgroupOf (secCMB t S L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRP]
    intro h k hh hk
    exact sec12E_R_normal F (hPM hk) hh
  have hXnorm : ((secXR t S L).subgroupOf (secCMB t S L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hXP]
    intro h k hh hk
    exact sec12E_X_normal F (hPM hk) hh
  have hsupRX : secR t ⊔ secXR t S L = secCMB t S L := by
    refine le_antisymm (sup_le hRP hXP) ?_
    intro p hp
    obtain ⟨r, hr, x, hx, rfl⟩ := sec12E_P_eq_RX F hp
    exact Subgroup.mul_mem_sup hr hx
  have hsup : (secXR t S L).subgroupOf (secCMB t S L) ⊔
      (secR t).subgroupOf (secCMB t S L) = ⊤ := by
    have h := Subgroup.subgroupOf_sup hRP hXP
    rw [hsupRX, Subgroup.subgroupOf_self, sup_comm] at h
    exact h.symm
  haveI : ((secXR t S L).subgroupOf (secCMB t S L)).Normal := hXnorm
  have hindex : ((secXR t S L).subgroupOf (secCMB t S L)).index =
      ((secXR t S L).subgroupOf (secCMB t S L)).relIndex
        ((secR t).subgroupOf (secCMB t S L)) := by
    rw [← Subgroup.relIndex_top_right (H := (secXR t S L).subgroupOf (secCMB t S L)),
      ← hsup, Subgroup.relIndex_sup_left]
  have hdvd : ((secXR t S L).subgroupOf (secCMB t S L)).index ∣
      Nat.card ((secR t).subgroupOf (secCMB t S L)) := by
    rw [hindex]
    exact Subgroup.relIndex_dvd_card _ _
  have hcard : Nat.card ((secR t).subgroupOf (secCMB t S L)) = Nat.card (secR t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRP).toEquiv
  have hoddR : Odd (Nat.card (secR t)) := by
    have h := CFSG.ComponentClassification.OddCore.odd_card
      (↥(Subgroup.centralizer ({t} : Set G)))
    rw [secR, oddCoreIn, CFSG.inSubgroup,
      Subgroup.card_map_of_injective
        (Subgroup.centralizer ({t} : Set G)).subtype_injective]
    exact h
  exact hoddR.of_dvd_nat (hcard ▸ hdvd)

theorem sec12E_exists_normal_sylow (F : Sec12Frame t L S) :
    ∃ E0 : Subgroup G, IsSylow2Of E0 (secCMB t S L) ∧ secM t S L ≤ normalizer (E0 : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRP : secR t ≤ secCMB t S L := (sec12E_R_le_C F).trans (sec12E_C_le_P F)
  have hXP : secXR t S L ≤ secCMB t S L := inf_le_left
  have hPM : secCMB t S L ≤ secM t S L := inf_le_left
  have hRnorm : ((secR t).subgroupOf (secCMB t S L)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRP]
    intro h k hh hk
    exact sec12E_R_normal F (hPM hk) hh
  haveI : ((secR t).subgroupOf (secCMB t S L)).Normal := hRnorm
  have hPquot : IsPGroup 2 (↥(secCMB t S L) ⧸ (secR t).subgroupOf (secCMB t S L)) := by
    intro g
    refine Quotient.inductionOn' g fun p => ?_
    refine ⟨2, ?_⟩
    change (QuotientGroup.mk' ((secR t).subgroupOf (secCMB t S L)) p) ^ (2 ^ 2) = 1
    rw [show (2 : ℕ) ^ 2 = 4 from rfl, ← map_pow, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    simpa [Subgroup.mem_subgroupOf, Subgroup.coe_pow] using sec12E_pow_four F p.2
  haveI : Group.IsNilpotent (↥(secCMB t S L) ⧸ (secR t).subgroupOf (secCMB t S L)) :=
    hPquot.isNilpotent
  let ψ : ↥(secXR t S L) →* (↥(secCMB t S L) ⧸ (secR t).subgroupOf (secCMB t S L)) :=
    (QuotientGroup.mk' ((secR t).subgroupOf (secCMB t S L))).comp (Subgroup.inclusion hXP)
  have hker : ψ.ker ≤ Subgroup.center ↥(secXR t S L) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_center_iff]
    intro y
    ext
    have hxR : (x : G) ∈ secR t := by
      have h1 : Subgroup.inclusion hXP x ∈ (secR t).subgroupOf (secCMB t S L) :=
        (QuotientGroup.eq_one_iff (Subgroup.inclusion hXP x)).mp hx
      simpa [Subgroup.mem_subgroupOf] using h1
    have hyR : (y : G) ∈ Subgroup.centralizer (secR t : Set G) :=
      (Subgroup.mem_inf.mp y.2).2
    exact (Subgroup.mem_centralizer_iff.mp hyR (x : G) hxR).symm
  haveI : Group.IsNilpotent ↥(secXR t S L) := Subgroup.isNilpotent_of_ker_le_center ψ hker
  let T : Sylow 2 ↥(secXR t S L) := default
  have hTnormal : (T : Subgroup ↥(secXR t S L)).Normal := inferInstance
  set E0 : Subgroup G := (T : Subgroup ↥(secXR t S L)).map (secXR t S L).subtype with hE0def
  have hE0X : IsSylow2Of E0 (secXR t S L) := isSylow2Of_map_sylow T
  have hXodd : ¬ 2 ∣ (secXR t S L).relIndex (secCMB t S L) :=
    (sec12E_relIndex_odd F).not_two_dvd_nat
  have hE0P : IsSylow2Of E0 (secCMB t S L) := by
    refine ⟨hE0X.1.trans hXP, hE0X.2.1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex E0 (secXR t S L) (secCMB t S L) hE0X.1 hXP]
    intro h
    rcases Nat.prime_two.dvd_mul.mp h with h1 | h2
    · exact hE0X.2.2 h1
    · exact hXodd h2
  refine ⟨E0, hE0P, ?_⟩
  have hconj : ∀ (n : G), n ∈ secM t S L → ∀ y : G, y ∈ E0 → n * y * n⁻¹ ∈ E0 := by
    intro n hn y hy
    have hnX : n ∈ normalizer (secXR t S L : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · exact sec12E_X_normal F hn
      · intro hz
        have := sec12E_X_normal F (Subgroup.inv_mem _ hn) hz
        simpa [mul_assoc] using this
    rw [hE0def, Subgroup.mem_map] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    let φ : MulAut ↥(secXR t S L) := (secXR t S L).normalizerMonoidHom ⟨n, hnX⟩
    have hTchar : (T : Subgroup ↥(secXR t S L)).Characteristic :=
      Sylow.characteristic_of_normal T hTnormal
    have hfix : (T : Subgroup ↥(secXR t S L)).map φ.toMonoidHom =
        (T : Subgroup ↥(secXR t S L)) :=
      (Subgroup.characteristic_iff_map_eq.mp hTchar) φ
    have hφu : φ u ∈ (T : Subgroup ↥(secXR t S L)) := by
      have : φ u ∈ (T : Subgroup ↥(secXR t S L)).map φ.toMonoidHom := ⟨u, hu, rfl⟩
      rwa [hfix] at this
    have hcoe : (φ u : G) = n * (u : G) * n⁻¹ := rfl
    rw [hE0def, Subgroup.mem_map]
    exact ⟨φ u, hφu, hcoe⟩
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj m hm x
  · intro hx
    have := hconj m⁻¹ (Subgroup.inv_mem _ hm) (m * x * m⁻¹) hx
    simpa [mul_assoc] using this

theorem sec12E_sylow_normal (F : Sec12Frame t L S) {E : Subgroup G}
    (hE : IsSylow2Of E (secCMB t S L)) : secM t S L ≤ normalizer (E : Set G) := by
  obtain ⟨E0, hE0, hN⟩ := sec12E_exists_normal_sylow F
  have hPM : secCMB t S L ≤ secM t S L := inf_le_left
  obtain ⟨a, haP, ha⟩ := IsSylow2Of.exists_conj_mem hE0 hE
  have ha' : ∀ x : G, x ∈ E0 ↔ a⁻¹ * x * a ∈ E0 :=
    (Subgroup.mem_normalizer_iff''.mp (hN (hPM haP)))
  have hEeq : E = E0 := by
    ext x
    rw [ha x, ha' x]
  rw [hEeq]
  exact hN

theorem asc82Lemma12E_of (hp : Asc82Pre11) :
    ∀ (G : Type) [Group G] [Finite G] (t : G) (L S : Subgroup G) (z : G) (K1 K2 : Subgroup G),
      Sec10Ctx G t L S z K1 K2 → Sec1011Alt1 t S L → ∃ E : Subgroup G, Sec12Ctx G t L S z K1 K2 E := by
  intro G _ _ t L S z K1 K2 hctx halt1
  let F : Sec12Frame t L S := sec12Frame_of hp hctx halt1
  obtain ⟨E0, hE0, hN⟩ := sec12E_exists_normal_sylow F
  exact ⟨E0,
    { toSec10Ctx := hctx
      alt1 := halt1
      sylowE := hE0
      S_norm := F.hSM.trans hN
      ML_norm := inf_le_left.trans hN }⟩

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxN10
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.AGLEmbedding.AltOuterOdd
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Assembly
import CFSG.HardMathSupport.Timmesfeld.Tables.Alt.Rank
import CFSG.Holt.Induced
public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownComp
import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure L73Final (B : Subgroup G) (a : G) (K J I Sg : Subgroup G) : Prop where
  K_comp : GLAPComponent 3 (Subgroup.centralizer ({a} : Set G)) K
  K_type : IsL62Type 3 K
  B_eq_K : IsDirectZpowersInf B a K
  S_not_le : ¬ Sg ≤ GLAPPrimeCoreOf 3 K
  J8 : Nonempty (↥(imageMod 3 K J) ≃* ↥(alternatingGroup (Fin 8)))
  I7 : Nonempty (↥(imageMod 3 K I) ≃* ↥(alternatingGroup (Fin 7)))

private theorem y5x_mem_normalizer_centralizer {S : Set G} {b : G} (hb : ∀ s ∈ S, s * b = b * s) :
    b ∈ Subgroup.normalizer (Subgroup.centralizer S : Set G) := by
  have key : ∀ (c : G), (∀ s ∈ S, s * c = c * s) →
      ∀ g ∈ Subgroup.centralizer S, c * g * c⁻¹ ∈ Subgroup.centralizer S := by
    intro c hc g hg s hs
    have hg' : s * g = g * s := Subgroup.mem_centralizer_iff.1 hg s hs
    have hsc : s * c = c * s := hc s hs
    have hsc' : s * c⁻¹ = c⁻¹ * s := by
      calc s * c⁻¹ = c⁻¹ * (c * s) * c⁻¹ := by group
        _ = c⁻¹ * (s * c) * c⁻¹ := by rw [hsc]
        _ = c⁻¹ * s := by group
    calc s * (c * g * c⁻¹) = (s * c) * g * c⁻¹ := by group
      _ = (c * s) * g * c⁻¹ := by rw [hsc]
      _ = c * (s * g) * c⁻¹ := by group
      _ = c * (g * s) * c⁻¹ := by rw [hg']
      _ = (c * g * c⁻¹) * s := by
        calc c * (g * s) * c⁻¹ = c * g * (s * c⁻¹) := by group
          _ = c * g * (c⁻¹ * s) := by rw [hsc']
          _ = c * g * c⁻¹ * s := by group
  have hbi : ∀ s ∈ S, s * b⁻¹ = b⁻¹ * s := by
    intro s hs
    calc s * b⁻¹ = b⁻¹ * (b * s) * b⁻¹ := by group
      _ = b⁻¹ * (s * b) * b⁻¹ := by rw [hb s hs]
      _ = b⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key b hb h hh
  · intro hh
    have h1 := key b⁻¹ hbi _ hh
    have e : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
    rwa [e] at h1

theorem l73_B_norm_K (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn : n = 10 ∨ n = 11)
    (hyB : y ∈ B) {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L n y J a K T I Sg) :
    B ≤ Subgroup.normalizer (K : Set G) := by
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hB).1
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hDB : altDxy x y ≤ B := sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  have haB : a ∈ B := hDB C.a_mem
  intro b hb
  have hNa : b ∈ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) :=
    y5x_mem_normalizer_centralizer (fun s hs => by
      rw [Set.mem_singleton_iff.1 hs]
      exact isElemAbelian_commute hBel haB hb)
  have hND : b ∈ Subgroup.normalizer (Subgroup.centralizer (altDxy x y : Set G) : Set G) :=
    y5x_mem_normalizer_centralizer (fun d hd => isElemAbelian_commute hBel (hDB hd) hb)
  have hNLa : b ∈ Subgroup.normalizer (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)) : Set G) :=
    mem_normalizer_glaPLayer hNa
  have hNL : b ∈ Subgroup.normalizer (L : Set G) := IsSStarMax.normalizes hB hb
  have hNLD : b ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (altDxy x y : Set G) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq] at hNL hND ⊢
    rw [gLBConj_inf, hNL, hND]
  have hNJ : b ∈ Subgroup.normalizer (J : Set G) := by
    have := mem_normalizer_glaPLayer (p := 3) hNLD
    rwa [S.J_layer] at this
  rw [C.K_eq]
  exact mem_normalizer_closureIn hNJ hNLa

private theorem y5x_card_le_index_factorial {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (H : Subgroup X) (hH : H ≠ ⊤) : Nat.card X ≤ H.index.factorial := by
  have hcore : H.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ Subgroup.normalCore_le H)) hH
  have hinj : Function.Injective (MulAction.toPermHom X (X ⧸ H)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker, hcore]
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_perm, ← Subgroup.index_eq_card] at h1
  exact h1

private theorem y5x_inf_le_primeCore {I K : Subgroup G} (hIK : I ≤ K) [IsSimpleGroup (PQuot 3 I)]
    (h3 : 3 ∣ Nat.card (PQuot 3 I)) : I ⊓ GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 I := by
  have hMI : I ⊓ GLAPPrimeCoreOf 3 K ≤ I := inf_le_left
  have hMK : I ⊓ GLAPPrimeCoreOf 3 K ≤ GLAPPrimeCoreOf 3 K := inf_le_right
  have hnormal : ((I ⊓ GLAPPrimeCoreOf 3 K).subgroupOf I).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hMI]
    intro h k hh hk
    have hN := Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 K (hIK hk)) h
    exact ⟨I.mul_mem (I.mul_mem hk hh.1) (I.inv_mem hk), hN.1 hh.2⟩
  haveI := hnormal
  have hbot : imageMod 3 I (I ⊓ GLAPPrimeCoreOf 3 K) = ⊥ := by
    haveI : (imageMod 3 I (I ⊓ GLAPPrimeCoreOf 3 K)).Normal :=
      Subgroup.Normal.map hnormal _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (imageMod 3 I (I ⊓ GLAPPrimeCoreOf 3 K)) with h | h
    · exact h
    · exfalso
      have h1 : Nat.card (imageMod 3 I (I ⊓ GLAPPrimeCoreOf 3 K)) = Nat.card (PQuot 3 I) := by
        rw [h, Subgroup.card_top]
      have h2 : Nat.card (imageMod 3 I (I ⊓ GLAPPrimeCoreOf 3 K)) ∣
          Nat.card ((I ⊓ GLAPPrimeCoreOf 3 K).subgroupOf I) := Subgroup.card_map_dvd _ _
      have h3' : Nat.card ((I ⊓ GLAPPrimeCoreOf 3 K).subgroupOf I) =
          Nat.card (I ⊓ GLAPPrimeCoreOf 3 K : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMI).toEquiv
      have h4 : Nat.card (I ⊓ GLAPPrimeCoreOf 3 K : Subgroup G) ∣ Nat.card (GLAPPrimeCoreOf 3 K) :=
        Subgroup.card_dvd_of_le hMK
      have h5 : 3 ∣ Nat.card (GLAPPrimeCoreOf 3 K) := by
        refine h3.trans ?_
        rw [← h1]
        exact h2.trans (h3' ▸ h4)
      exact not_dvd_card_glaPPrimeCoreOf Nat.prime_three K h5
  exact (imageMod_eq_bot_iff hMI).1 hbot

theorem l73_imageMod_alt {B : Subgroup G} {x : G} {L : Subgroup G} {y : G} {J : Subgroup G}
    (S : AltSetup 3 B x L 11 y J) {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L 11 y J a K T I Sg)
    (hK : L72Single 3 (altDxy x y) J K a)
    (hJ8 : Nonempty (↥(imageMod 3 K J) ≃* ↥(alternatingGroup (Fin 8)))) :
    Nonempty (↥(imageMod 3 K I) ≃* ↥(alternatingGroup (Fin 7))) := by
  have hIJ : I ≤ J := C.ti.I_le_J
  have hIK : I ≤ K := hIJ.trans C.J_le_K
  have hI7 : Nonempty (PQuot 3 I ≃* ↥(alternatingGroup (Fin 7))) := C.ti.I_alt
  obtain ⟨eP⟩ := hI7
  haveI : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (PQuot 3 I) := MulEquiv.isSimpleGroup eP
  have hcardP : Nat.card (PQuot 3 I) = 2520 := by
    rw [Nat.card_congr eP.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eJ⟩ := hJ8
  have hcardJ : Nat.card ↥(imageMod 3 K J) = 20160 := by
    rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  haveI : IsSimpleGroup ↥(imageMod 3 K J) := MulEquiv.isSimpleGroup eJ
  have hMO := y5x_inf_le_primeCore hIK (by rw [hcardP]; norm_num)
  let ι : ↥I →* PQuot 3 K := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hIK)
  have hιrange : imageMod 3 K I = ι.range := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨(g : G), hg⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨Subgroup.inclusion hIK e, e.2, rfl⟩
  have hker : ι.ker ≤ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)).ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have hg1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (Subgroup.inclusion hIK g) = 1 := hg
    have hgK : Subgroup.inclusion hIK g ∈ GLAPPrimeCore 3 ↥K := (QuotientGroup.eq_one_iff _).1 hg1
    have hgOK : (g : G) ∈ GLAPPrimeCoreOf 3 K := ⟨Subgroup.inclusion hIK g, hgK, rfl⟩
    obtain ⟨h, hh, hhg⟩ := hMO ⟨g.2, hgOK⟩
    have hhg' : h = g := Subtype.ext hhg
    exact (QuotientGroup.eq_one_iff g).2 (hhg' ▸ hh)
  let ψ : ↥I →* PQuot 3 I := QuotientGroup.mk' (GLAPPrimeCore 3 ↥I)
  let ρ₀ : ↥I ⧸ ι.ker →* PQuot 3 I := QuotientGroup.lift ι.ker ψ hker
  let e1 : ↥(imageMod 3 K I) ≃* ↥ι.range := MulEquiv.subgroupCongr hιrange
  let e2 : ↥I ⧸ ι.ker ≃* ↥ι.range := QuotientGroup.quotientKerEquivRange ι
  let ρ : ↥(imageMod 3 K I) →* PQuot 3 I := ρ₀.comp (e2.symm.toMonoidHom.comp e1.toMonoidHom)
  have hρsurj : Function.Surjective ρ := by
    intro z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥I) z
    have hmem : ι g ∈ ι.range := ⟨g, rfl⟩
    refine ⟨e1.symm ⟨ι g, hmem⟩, ?_⟩
    have h1 : e2 (QuotientGroup.mk g : ↥I ⧸ ι.ker) = ⟨ι g, hmem⟩ := by
      apply Subtype.ext
      rfl
    have h2 : e2.symm ⟨ι g, hmem⟩ = (QuotientGroup.mk g : ↥I ⧸ ι.ker) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    show ρ₀ (e2.symm (e1 (e1.symm ⟨ι g, hmem⟩))) = _
    rw [MulEquiv.apply_symm_apply, h2]
    exact QuotientGroup.lift_mk ι.ker hker g
  have hcardrel : Nat.card ↥(imageMod 3 K I) = 2520 * Nat.card ↥ρ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    have h2 : Nat.card (↥(imageMod 3 K I) ⧸ ρ.ker) = Nat.card (PQuot 3 I) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj).toEquiv
    rw [h1, h2, hcardP]
  have hdvd : Nat.card ↥(imageMod 3 K I) ∣ Nat.card ↥(imageMod 3 K J) :=
    Subgroup.card_dvd_of_le (imageMod_mono hIJ)
  rw [hcardJ, hcardrel] at hdvd
  have hk8 : Nat.card ↥ρ.ker ∣ 8 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2520) (by simpa using hdvd)
  have hk : Nat.card ↥ρ.ker ≤ 8 := Nat.le_of_dvd (by norm_num) hk8
  generalize hkdef : Nat.card ↥ρ.ker = k at hcardrel hk8 hk
  interval_cases k
  all_goals try (norm_num at hk8)
  ·
    have hbot : ρ.ker = ⊥ := Subgroup.card_eq_one.1 hkdef
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hbot
    exact ⟨(MulEquiv.ofBijective ρ ⟨hinj, hρsurj⟩).trans eP⟩
  ·
    exfalso
    set H : Subgroup ↥(imageMod 3 K J) := (imageMod 3 K I).subgroupOf (imageMod 3 K J) with hHdef
    have hHcard : Nat.card H = 2520 * 2 := by
      rw [hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (imageMod_mono hIJ)).toEquiv, hcardrel]
    have hHne : H ≠ ⊤ := by
      intro h
      rw [h, Subgroup.card_top, hcardJ] at hHcard
      norm_num at hHcard
    have hmul := H.card_mul_index
    rw [hHcard, hcardJ] at hmul
    have hidx : H.index = 4 := by omega
    have := y5x_card_le_index_factorial H hHne
    rw [hidx, hcardJ] at this
    norm_num [Nat.factorial] at this
  ·
    exfalso
    set H : Subgroup ↥(imageMod 3 K J) := (imageMod 3 K I).subgroupOf (imageMod 3 K J) with hHdef
    have hHcard : Nat.card H = 2520 * 4 := by
      rw [hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (imageMod_mono hIJ)).toEquiv, hcardrel]
    have hHne : H ≠ ⊤ := by
      intro h
      rw [h, Subgroup.card_top, hcardJ] at hHcard
      norm_num at hHcard
    have hmul := H.card_mul_index
    rw [hHcard, hcardJ] at hmul
    have hidx : H.index = 2 := by omega
    have := y5x_card_le_index_factorial H hHne
    rw [hidx, hcardJ] at this
    norm_num [Nat.factorial] at this
  ·
    exfalso
    have hEq : imageMod 3 K I = imageMod 3 K J := by
      apply Subgroup.eq_of_le_of_card_ge (imageMod_mono hIJ)
      rw [hcardJ, hcardrel]
    have eI : ↥(imageMod 3 K I) ≃* ↥(alternatingGroup (Fin 8)) := (MulEquiv.subgroupCongr hEq).trans eJ
    haveI : IsSimpleGroup ↥(imageMod 3 K I) := MulEquiv.isSimpleGroup eI
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
    · have h1 : Nat.card ↥ρ.ker = 1 := Subgroup.card_eq_one.2 h
      omega
    · have h1 : Nat.card ↥ρ.ker = Nat.card ↥(imageMod 3 K I) := by rw [h, Subgroup.card_top]
      omega

theorem centralizer_zpowers_eq_s6 (g : G) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) = Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem centralizer_sup_eq (A B : Subgroup G) :
    Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (by exact_mod_cast le_sup_left))
      (Subgroup.centralizer_le (by exact_mod_cast le_sup_right))
  · intro g hg
    have hle : A ⊔ B ≤ Subgroup.centralizer ({g} : Set G) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hg.1 a ha))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hg.2 b hb))
    exact Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem l73_layer_CD (hc : S6Ctx G 3) (i182 : I182At G) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ}
    {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) :
    GLAPLayer 3 (Subgroup.centralizer (altDxy x y : Set G)) = J := by
  have hxL : L ≤ Subgroup.centralizer ({x} : Set G) := (IsSStarMax.component hB).1
  have hxD : x ∈ altDxy x y := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have hyD : y ∈ altDxy x y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
    isPGroup_of_isElemAbelian (isElemAbelian_zpowers_of_mem S.isElemAbelian_D hxD)
  have hyp : IsPGroup 3 (Subgroup.zpowers y) :=
    isPGroup_of_isElemAbelian (isElemAbelian_zpowers_of_mem S.isElemAbelian_D hyD)
  have hcomm : ∀ d ∈ Subgroup.zpowers x, ∀ e ∈ Subgroup.zpowers y, d * e = e * d := fun d hd e he =>
    isElemAbelian_commute S.isElemAbelian_D
      ((Subgroup.zpowers_le.2 hxD) hd) ((Subgroup.zpowers_le.2 hyD) he)
  have h := i182 hc.kProper (Subgroup.zpowers x) (Subgroup.zpowers y) hxp hyp hcomm
  rw [centralizer_zpowers_eq_s6, centralizer_zpowers_eq_s6, sstarMax_layer_eq hc hB] at h
  have hCD : Subgroup.centralizer (altDxy x y : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({y} : Set G) := by
    unfold altDxy
    rw [centralizer_sup_eq, centralizer_zpowers_eq_s6, centralizer_zpowers_eq_s6]
  have hJ := S.J_layer
  rw [hCD, ← inf_assoc, inf_eq_left.2 hxL] at hJ
  rw [hCD, ← h, hJ]

theorem l73_layer_KD (hc : S6Ctx G 3) (i182 : I182At G) {B : Subgroup G} {x : G} {L : Subgroup G}
    {n : ℕ} {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) {a : G}
    {K : Subgroup G} (haD : a ∈ altDxy x y) (hKsn : IsSubnormal K (Subgroup.centralizer ({a} : Set G)))
    (hJK : J ≤ K) (hJc : GLAPComponent 3 (K ⊓ Subgroup.centralizer (altDxy x y : Set G)) J) :
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (altDxy x y : Set G)) = J := by
  have hp := hc.prime
  have hCD : Subgroup.centralizer (altDxy x y : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (by simpa using haD)
  have hsn : IsSubnormal (K ⊓ Subgroup.centralizer (altDxy x y : Set G))
      (Subgroup.centralizer (altDxy x y : Set G)) := by
    have := hKsn.inf (Subgroup.centralizer (altDxy x y : Set G))
    rwa [inf_eq_right.2 hCD] at this
  refine le_antisymm ?_ (le_sSup hJc)
  calc GLAPLayer 3 (K ⊓ Subgroup.centralizer (altDxy x y : Set G))
      ≤ GLAPLayer 3 (Subgroup.centralizer (altDxy x y : Set G)) := glaPLayer_le_of_isSubnormal hp hsn
    _ = J := l73_layer_CD hc i182 hB S

theorem normalizer_outer_hom (p : ℕ) (L : Subgroup G) :
    ∃ f : ↥(Subgroup.normalizer (L : Set G)) →*
        CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot p L),
      f.ker = (L ⊔ centModSubgroup p L).subgroupOf (Subgroup.normalizer (L : Set G)) := by
  classical
  refine ⟨(QuotientGroup.mk'
    (CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot p L))).comp
    (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L), ?_⟩
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hlN : (l : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l.2
    have h1 : CentMod p L ((l : G)⁻¹ * (g : G)) := by
      have hmem : (l : G)⁻¹ * (g : G) ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ hlN) g.2
      refine (chev_barAut_eq_one_iff_centMod hmem).1 ?_
      have e1 : (⟨(l : G)⁻¹ * (g : G), hmem⟩ : ↥(Subgroup.normalizer (L : Set G))) =
          ⟨(l : G), hlN⟩⁻¹ * g := rfl
      rw [e1, map_mul, map_inv, ← hq, barAut_eq_conj_of_mem l.2]
      simp
    have h2 : (l : G)⁻¹ * (g : G) ∈ centModSubgroup p L := centMod_iff.1 h1
    have h3 : (g : G) = (l : G) * ((l : G)⁻¹ * (g : G)) := by group
    rw [h3]
    exact Subgroup.mul_mem_sup l.2 h2
  · intro hg
    have hH : ∀ z : G, z ∈ L ⊔ centModSubgroup p L → ∀ hz : z ∈ Subgroup.normalizer (L : Set G),
        CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L ⟨z, hz⟩ ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot p L) := by
      intro z hzL
      have hsub : L ⊔ centModSubgroup p L ≤
          ((CFSG.ComponentClassification.OuterAutomorphisms.inner (PQuot p L)).comap
            (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L)).map
              (Subgroup.normalizer (L : Set G)).subtype := by
        refine sup_le (fun l hl => ?_) (fun c hc => ?_)
        · refine ⟨⟨l, Subgroup.le_normalizer hl⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap, barAut_eq_conj_of_mem hl]
          exact ⟨_, rfl⟩
        · refine ⟨⟨c, (mem_centModSubgroup.1 hc).1⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, Subgroup.mem_comap,
            (chev_barAut_eq_one_iff_centMod (mem_centModSubgroup.1 hc).1).2 (centMod_iff.2 hc)]
          exact Subgroup.one_mem _
      intro hz
      obtain ⟨n, hn, hnz⟩ := hsub hzL
      have : n = ⟨z, hz⟩ := Subtype.ext hnz
      rw [this] at hn
      exact hn
    exact hH g hg g.2

theorem card_outer_pQuot_dvd_four {p n : ℕ} {L : Subgroup G} (hL : IsAltPType p L n) (hn : 5 ≤ n) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot p L)) ∣ 4 := by
  obtain ⟨e⟩ := hL
  have h4 := CFSG.AGLEmbedding.card_outer_alternatingGroup_dvd_four n hn
  rwa [← Nat.card_congr
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv] at h4

theorem perfect_le_sup_centMod {L P : Subgroup G} {n : ℕ} (hL : IsAltPType 3 L n) (hn : 5 ≤ n)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hperf : ⁅P, P⁆ = P) :
    P ≤ L ⊔ centModSubgroup 3 L := by
  obtain ⟨f, hf⟩ := normalizer_outer_hom 3 L
  have h4 := card_outer_pQuot_dvd_four hL hn
  haveI : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 L)) :=
    Nat.finite_of_card_ne_zero (fun h0 => by rw [h0] at h4; omega)
  haveI : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 L)) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (h4.trans (by norm_num : 4 ∣ 2 ^ 2))
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent (CFSG.ComponentClassification.OuterAutomorphisms.Outer (PQuot 3 L)) :=
      (IsPGroup.of_card hk).isNilpotent
    infer_instance
  haveI : Group.IsSolvable (↥(Subgroup.normalizer (L : Set G)) ⧸ f.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective f)
  have hP' : ⁅P.subgroupOf (Subgroup.normalizer (L : Set G)), P.subgroupOf (Subgroup.normalizer (L : Set G))⁆ =
      P.subgroupOf (Subgroup.normalizer (L : Set G)) := by
    apply Subgroup.map_injective (Subgroup.normalizer (L : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPN, hperf]
  intro g hg
  have h1 := perfect_le_of_quotient_solvable (M := f.ker) inferInstance hP'
    (Subgroup.mem_subgroupOf.2 hg : (⟨g, hPN hg⟩ : ↥(Subgroup.normalizer (L : Set G))) ∈
      P.subgroupOf (Subgroup.normalizer (L : Set G)))
  rw [hf] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem card_eq_card_autBar_mul (p : ℕ) {L A : Subgroup G} (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥A = Nat.card ↥(CFSG.HardMathSupport.Solomon.LocalBalance.autBar p A L) *
      Nat.card ↥(A ⊓ centModSubgroup p L : Subgroup G) := by
  classical
  let φ : ↥A →* MulAut (PQuot p L) :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L).comp (Subgroup.inclusion hAN)
  have hrange : φ.range = CFSG.HardMathSupport.Solomon.LocalBalance.autBar p A L := by
    unfold CFSG.HardMathSupport.Solomon.LocalBalance.autBar
    rw [inf_eq_left.2 hAN, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : φ.ker.map A.subtype = A ⊓ centModSubgroup p L := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      have ha' : CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L (Subgroup.inclusion hAN a) = 1 := ha
      exact ⟨a.2, centMod_iff.1 ((chev_barAut_eq_one_iff_centMod (hAN a.2)).1 ha')⟩
    · rintro ⟨hgA, hgC⟩
      refine ⟨⟨g, hgA⟩, ?_, rfl⟩
      show CFSG.HardMathSupport.Solomon.LocalBalance.barAut p L (Subgroup.inclusion hAN ⟨g, hgA⟩) = 1
      exact (chev_barAut_eq_one_iff_centMod (hAN hgA)).2 (centMod_iff.2 hgC)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange,
    ← Subgroup.card_map_of_injective A.subtype_injective, hker] at h2
  exact h2

private theorem pQuotHom_eq_one_of_pGroup {K : Subgroup G} {P : Subgroup ↥K} (hP : IsPGroup 3 P) {a : ↥K}
    (ha : a ∈ P) (h : pQuotHom 3 K a = 1) : a = 1 := by
  have he : a ∈ GLAPPrimeCore 3 ↥K := by rw [← ker_pQuotHom]; exact h
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := hP ⟨a, ha⟩
  have h1 : orderOf a ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf a ∣ Nat.card ↥(GLAPPrimeCore 3 ↥K) := Subgroup.orderOf_dvd_natCard _ he
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) h1 h2)

theorem exists_lift_elemAbelian_centralizing {K F E : Subgroup G} (hF3 : IsPGroup 3 F)
    (hFK : F ≤ centModSubgroup 3 K) (hEK : E ≤ K) (hE : IsElemAbelian 3 E) :
    ∃ E' : Subgroup G, E' ≤ K ⊓ Subgroup.centralizer (F : Set G) ∧ IsElemAbelian 3 E' ∧
      imageMod 3 K E' = imageMod 3 K E := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hFN : F ≤ Subgroup.normalizer (K : Set G) := fun g hg => (mem_centModSubgroup.1 (hFK hg)).1
  have hfix : ∀ (q : PQuot 3 K) (d : G) (hd : d ∈ F),
      CFSG.HardMathSupport.Solomon.LocalBalance.barAut 3 K ⟨d, hFN hd⟩ q = q := by
    intro q d hd
    rw [(chev_barAut_eq_one_iff_centMod (hFN hd)).2 (centMod_iff.2 (hFK hd))]
    rfl
  have htop : ∀ q : PQuot 3 K, q ∈ imageMod 3 K (K ⊓ Subgroup.centralizer (F : Set G)) := by
    intro q
    obtain ⟨k, rfl⟩ := pQuotHom_surjective 3 K q
    exact imageMod_fixed_lift hF3 hFN hFN le_rfl ⟨k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩ (hfix _)
  obtain ⟨hQel, -⟩ := imageMod_elemAbelian hp3 hEK hE
  obtain ⟨P, -, hPH, hP3, hPmap⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le (p := 3) (pQuotHom 3 K)
    (H := (K ⊓ Subgroup.centralizer (F : Set G)).subgroupOf K) (Q := imageMod 3 K E)
    (isPGroup_of_isElemAbelian hQel) (fun q _ => htop q) (E := ⊥) (IsPGroup.of_card (n := 0) (by simp))
    bot_le (by simp)
  have hinj : ∀ a ∈ P, ∀ b ∈ P, pQuotHom 3 K a = pQuotHom 3 K b → a = b := by
    intro a ha b hb hab
    have h1 : pQuotHom 3 K (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have := pQuotHom_eq_one_of_pGroup hP3 (P.mul_mem (P.inv_mem ha) hb) h1
    exact inv_mul_eq_one.1 this
  have hPQ : ∀ a ∈ P, pQuotHom 3 K a ∈ imageMod 3 K E := fun a ha => hPmap ▸ ⟨a, ha, rfl⟩
  refine ⟨P.map K.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    exact (Subgroup.mem_subgroupOf.1 (hPH hk))
  · refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha, ← hb]
      have hc : pQuotHom 3 K (a' * b') = pQuotHom 3 K (b' * a') := by
        rw [map_mul, map_mul]
        exact congrArg Subtype.val (hQel.1.is_comm.comm ⟨_, hPQ a' ha'⟩ ⟨_, hPQ b' hb'⟩)
      exact congrArg Subtype.val (hinj _ (P.mul_mem ha' hb') _ (P.mul_mem hb' ha') hc)
    · obtain ⟨a', ha', rfl⟩ := hx
      have h3 : pQuotHom 3 K (a' ^ 3) = pQuotHom 3 K 1 := by
        rw [map_pow, map_one]
        exact hQel.2 _ (hPQ a' ha')
      have := hinj _ (P.pow_mem ha' 3) 1 P.one_mem h3
      show ((a' : ↥K) : G) ^ 3 = 1
      rw [← Subgroup.coe_pow, this]
      rfl
  · have h1 : (P.map K.subtype).subgroupOf K = P :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective P
    unfold imageMod
    rw [h1]
    exact hPmap

theorem l73_rank_Cx (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {n : ℕ} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L n y J) (hn : n ≤ 11) :
    ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({x} : Set G) → IsElemAbelian 3 E → Nat.card ↥E ≤ 3 ^ 4 := by
  intro E hEx hE
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hn5 : 5 ≤ n := by have := S.seven_lt; omega
  have hN : E ≤ Subgroup.normalizer (L : Set G) := hEx.trans (l73_Cx_le_normalizer hc hB)
  obtain ⟨eL⟩ := S.alt
  have hZ : Subgroup.center (PQuot 3 L) = ⊥ := center_pQuot_eq_bot_of_equiv (by omega) eL
  have f : PSimple 3 L ≃* ↥(alternatingGroup (Fin n)) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans eL)
  haveI : Group.IsPerfect (PQuot 3 L) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isPerfect_barOf (IsSStarMax.component hB)
  have hcard := card_eq_card_autBar_mul 3 hN
  have hA : IsElemAbelian 3 (CFSG.HardMathSupport.Solomon.LocalBalance.autBar 3 E L) :=
    CFSG.HardMathSupport.Timmesfeld.Balance.Alt.isElemAbelian_autBar hE L
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hA
  have hrk : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (PQuot 3 L))) :=
    le_pRank_of_card_altSetup hp.one_lt le_top hA hk
  have hup := CFSG.HardMathSupport.Timmesfeld.Tables.Alt.pRank_aut_le (L := PQuot 3 L) hn5 f hp hc.odd
  have hk3 : k ≤ 3 := by omega
  have hS'el : IsElemAbelian 3 (E ⊓ centModSubgroup 3 L : Subgroup G) :=
    isElemAbelian_mono hE inf_le_left
  have hS'cyc : IsCyclic ↥(E ⊓ centModSubgroup 3 L : Subgroup G) :=
    (IsSStarMax.cycMod hB) (E ⊓ centModSubgroup 3 L) (fun g hg => centMod_iff.2 (Subgroup.mem_inf.1 hg).2)
      (isPGroup_of_isElemAbelian hS'el)
  have hS'card : Nat.card ↥(E ⊓ centModSubgroup 3 L : Subgroup G) ≤ 3 := by
    haveI := hS'cyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(E ⊓ centModSubgroup 3 L : Subgroup G))
    have hgord : orderOf g = Nat.card ↥(E ⊓ centModSubgroup 3 L : Subgroup G) :=
      orderOf_eq_card_of_forall_mem_zpowers hg
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hS'el.2 (g : G) g.2)
    rw [← hgord]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  rw [hcard, hk]
  calc 3 ^ k * Nat.card ↥(E ⊓ centModSubgroup 3 L : Subgroup G) ≤ 3 ^ 3 * 3 :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hk3) hS'card
    _ = 3 ^ 4 := by norm_num

theorem l73_exists_cycle_c (hc : S6Ctx G 3) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G} {J : Subgroup G}
    (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 11 y J) (hyB : y ∈ B) {a : G}
    {K T I Sg : Subgroup G} (C : L73Ctx B x L 11 y J a K T I Sg) :
    ∃ c ∈ B ⊓ I, c ≠ 1 ∧ c ^ 3 = 1 ∧ ∃ eJ : PQuot 3 J ≃* ↥(alternatingGroup (Fin 8)),
      (permOfMod 3 J 8 eJ c).cycleType = {3} := by
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hB).1
  have hIJ : I ≤ J := C.ti.I_le_J
  have hEB : (B ⊓ I : Subgroup G) ≤ B := inf_le_left
  have hE9 : Nat.card ↥(B ⊓ I : Subgroup G) = 9 := by
    have := l73_card_B_inf_I hc hB S (Or.inr rfl) hyB C
    simpa using this
  have hEJ : (B ⊓ I : Subgroup G) ≤ J := inf_le_right.trans hIJ
  obtain ⟨h1, h2⟩ := imageMod_elemAbelian hc.prime hEJ (isElemAbelian_mono hBel hEB)
  have hJ8 : IsAltPType 3 J 8 := S.J_alt
  obtain ⟨eJ⟩ := hJ8
  obtain ⟨q, hq, hqc⟩ := exists_three_cycle_of_maxRank eJ (by norm_num) h1 (by rw [h2.trans hE9]; norm_num)
  obtain ⟨g, hg, rfl⟩ := hq
  have hgE : (g : G) ∈ (B ⊓ I : Subgroup G) := hg
  refine ⟨(g : G), hgE, ?_, ?_, eJ, ?_⟩
  · intro h1'
    have : permOfQ eJ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) g) = 1 := by
      have : g = 1 := Subtype.ext h1'
      subst this
      simp [permOfQ]
    rw [this] at hqc
    simp at hqc
  · exact hBel.2 _ (hEB hgE)
  · have hperm : permOfMod 3 J 8 eJ (g : G) = permOfQ eJ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) g) := by
      unfold permOfQ permOfMod
      rw [dif_pos g.2]
      rfl
    rw [hperm]
    exact hqc

theorem layer_cent_three_cycle {Q : Type} [Group Q] [Finite Q] (e : Q ≃* ↥(alternatingGroup (Fin 8))) {q : Q}
    (hq : (permOfQ e q).cycleType = {3}) : GLAPLayer 3 (Subgroup.centralizer ({q} : Set Q)) ≠ ⊥ := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hσ : ((e q : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)).cycleType = {3} := hq
  have hF := altFix_isPComponent_cycle hp (by norm_num) hσ (by norm_num) (by norm_num)
  have h1 := glaPComponent_map_mulEquiv hp e.symm hF
  have hC : (Subgroup.centralizer ({e q} : Set ↥(alternatingGroup (Fin 8)))).map e.symm.toMonoidHom =
      Subgroup.centralizer ({q} : Set Q) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : w * e q = e q * w := Subgroup.mem_centralizer_singleton_iff.1
        (show w ∈ Subgroup.centralizer ({e q} : Set ↥(alternatingGroup (Fin 8))) from hw)
      show e.symm w ∈ Subgroup.centralizer ({q} : Set Q)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply e.injective
      simpa using hw'
    · intro hz
      have hz' : z * q = q * z := Subgroup.mem_centralizer_singleton_iff.1 hz
      refine ⟨e z, ?_, by simp⟩
      show e z ∈ Subgroup.centralizer ({e q} : Set ↥(alternatingGroup (Fin 8)))
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg e hz'
      simpa using this
  rw [hC] at h1
  haveI := AltDown.nontrivial_of_glaPComponent hp h1
  intro hbot
  have hle : Subgroup.map e.symm.toMonoidHom (altFix ((e q : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8))) ≤
      GLAPLayer 3 (Subgroup.centralizer ({q} : Set Q)) := le_sSup h1
  rw [hbot, le_bot_iff] at hle
  exact (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance hle

theorem l73_layer_cent_cycle_ne_bot {J : Subgroup G} (eJ : PQuot 3 J ≃* ↥(alternatingGroup (Fin 8))) {c : G}
    (hcJ : c ∈ J) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1) (hcyc : (permOfMod 3 J 8 eJ c).cycleType = {3}) :
    GLAPLayer 3 (J ⊓ Subgroup.centralizer ({c} : Set G)) ≠ ⊥ := by
  intro h
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have h1 := imageMod_glaPLayer hp (inf_le_left : J ⊓ Subgroup.centralizer ({c} : Set G) ≤ J)
  rw [h, imageMod_centralizer_eq hp hcJ (orderOf_eq_prime hc3 hc1)] at h1
  have hbot : imageMod 3 J (⊥ : Subgroup G) = ⊥ := by
    unfold imageMod
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h1
  refine layer_cent_three_cycle eJ (q := modOf 3 J c hcJ) ?_ h1.symm
  have hperm : permOfQ eJ (modOf 3 J c hcJ) = permOfMod 3 J 8 eJ c := by
    unfold permOfQ permOfMod modOf
    rw [dif_pos hcJ]
  rw [hperm]
  exact hcyc

theorem l73_isGStar_K (hc : S6Ctx G 3) (i182 : I182At G) {B : Subgroup G} {x : G} {L : Subgroup G} {y : G}
    {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 11 y J) (hyB : y ∈ B) {a : G}
    {K T I Sg : Subgroup G} (C : L73Ctx B x L 11 y J a K T I Sg)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) : IsGStar 3 B K := by
  have hp := hc.prime
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hB).1
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have hDB : altDxy x y ≤ B := sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  obtain ⟨c, hcBI, hc1, hc3, eJ, hcyc⟩ := l73_exists_cycle_c hc hB S hyB C
  obtain ⟨hBeq, hBinf⟩ := C.ti.B_eq_I (Or.inr rfl)
  have hcB : c ∈ B := hcBI.1
  have hcJ : c ∈ J := C.ti.I_le_J hcBI.2
  have hZ0 := l73_layer_cent_cycle_ne_bot eJ hcJ hc1 hc3 hcyc
  have hzcB : Subgroup.zpowers c ≤ B := (Subgroup.zpowers_le).2 hcB
  have hE'B : altDxy x y ⊔ Subgroup.zpowers c ≤ B := sup_le hDB hzcB
  have hE'el : IsElemAbelian 3 (altDxy x y ⊔ Subgroup.zpowers c : Subgroup G) := isElemAbelian_mono hBel hE'B
  have hE'27 : Nat.card ↥(altDxy x y ⊔ Subgroup.zpowers c : Subgroup G) = 3 ^ 3 := by
    have hN : Subgroup.zpowers c ≤ Subgroup.normalizer ((altDxy x y : Subgroup G) : Set G) := fun g hg =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd =>
        isElemAbelian_commute hBel (hDB hd) (hzcB hg))
    have h1 := card_sup_mul_card_inf_of_le_normalizer hN
    have hinf : altDxy x y ⊓ Subgroup.zpowers c = ⊥ := by
      rw [eq_bot_iff, ← hBinf]
      exact inf_le_inf_left _ (le_inf hzcB ((Subgroup.zpowers_le).2 hcBI.2))
    rw [hinf, Subgroup.card_bot, Nat.card_zpowers, orderOf_eq_prime hc3 hc1, S.card_D] at h1
    omega
  have hLD := l73_layer_CD hc i182 hB S
  have hcomm : ∀ d ∈ altDxy x y, ∀ e ∈ Subgroup.zpowers c, d * e = e * d := fun d hd e he =>
    isElemAbelian_commute hBel (hDB hd) (hzcB he)
  have hI := i182 hc.kProper (altDxy x y) (Subgroup.zpowers c) (isPGroup_of_isElemAbelian S.isElemAbelian_D)
    (isPGroup_of_isElemAbelian (isElemAbelian_mono hBel hzcB)) hcomm
  rw [hLD, centralizer_zpowers_eq_s6] at hI
  have hCE : Subgroup.centralizer ((altDxy x y ⊔ Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer (altDxy x y : Set G) ⊓ Subgroup.centralizer ({c} : Set G) := by
    rw [centralizer_sup_eq, centralizer_zpowers_eq_s6]
  have hJCD : J ≤ Subgroup.centralizer (altDxy x y : Set G) := S.J_comp.1.trans inf_le_right
  have hZ1 : GLAPLayer 3 (Subgroup.centralizer ((altDxy x y ⊔ Subgroup.zpowers c : Subgroup G) : Set G)) ≠ ⊥ := by
    rw [hCE, ← hI]; exact hZ0
  have hZle : GLAPLayer 3 (Subgroup.centralizer ((altDxy x y ⊔ Subgroup.zpowers c : Subgroup G) : Set G)) ≤
      K ⊓ Subgroup.centralizer ((altDxy x y ⊔ Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [hCE, ← hI]
    refine (sSup_le fun M hM => hM.1 : GLAPLayer 3 (J ⊓ Subgroup.centralizer ({c} : Set G)) ≤ _).trans ?_
    intro j hj
    exact ⟨C.J_le_K hj.1, hJCD hj.1, hj.2⟩
  refine ⟨_, hE'B, hE'el, hE'27, ?_⟩
  rw [closureIn_eq_self hBK]
  intro hbot
  apply hZ1
  have h2 := glaPLayer_le_layer_of_le hp (inf_le_right : K ⊓ Subgroup.centralizer
    ((altDxy x y ⊔ Subgroup.zpowers c : Subgroup G) : Set G) ≤ _) hZle
  rw [hbot] at h2
  exact le_bot_iff.1 h2

private theorem y5x_mem_primeCore_iff {K : Subgroup G} (z : ↥K) :
    z ∈ GLAPPrimeCore 3 ↥K ↔ (z : G) ∈ GLAPPrimeCoreOf 3 K := by
  constructor
  · intro h
    exact ⟨z, h, rfl⟩
  · rintro ⟨w, hw, hwz⟩
    have hwz' : w = z := Subtype.ext hwz
    exact hwz' ▸ hw

private theorem y5x_conj_mem_primeCore {K : Subgroup G} {h o : G} (hh : h ∈ K)
    (ho : o ∈ GLAPPrimeCoreOf 3 K) : h * o * h⁻¹ ∈ GLAPPrimeCoreOf 3 K :=
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_glaPPrimeCoreOf 3 K hh) o).1 ho

private theorem y5x_mk_comm {K : Subgroup G} {g k : G} (hg : g ∈ K) (hk : k ∈ K)
    (h : g * k * g⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 K) :
    (QuotientGroup.mk ⟨g, hg⟩ : PQuot 3 K) * QuotientGroup.mk ⟨k, hk⟩ =
      QuotientGroup.mk ⟨k, hk⟩ * QuotientGroup.mk ⟨g, hg⟩ := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, y5x_mem_primeCore_iff]
  have hgk : g * k ∈ K := K.mul_mem hg hk
  have e : (((⟨g, hg⟩ : ↥K) * ⟨k, hk⟩)⁻¹ * (⟨k, hk⟩ * ⟨g, hg⟩) : ↥K).1 = (g * k)⁻¹ * (k * g) := rfl
  rw [e, show (g * k)⁻¹ * (k * g) = (g * k)⁻¹ * (g * k * g⁻¹ * k⁻¹)⁻¹ * (g * k) by group]
  have h2 := y5x_conj_mem_primeCore (K.inv_mem hgk) (Subgroup.inv_mem _ h)
  rwa [inv_inv] at h2

private theorem y5x_mem_primeCore_of_centMod {K : Subgroup G} (hK : Subgroup.center (PQuot 3 K) = ⊥)
    {k : G} (hkK : k ∈ K) (hkc : k ∈ centModSubgroup 3 K) : k ∈ GLAPPrimeCoreOf 3 K := by
  obtain ⟨-, hc⟩ := hkc
  have hmem : (QuotientGroup.mk ⟨k, hkK⟩ : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
    apply y5x_mk_comm hg hkK
    have := hc g hg
    rwa [commutatorElement_def] at this
  rw [hK, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
  exact (y5x_mem_primeCore_iff ⟨k, hkK⟩).1 hmem

private theorem y5x_le_normalizer_of_comm {B H : Subgroup G} (hB : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hHB : H ≤ B) : B ≤ Subgroup.normalizer (H : Set G) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hcomm := hB b hb h (hHB hh)
    have e : b * h * b⁻¹ = h := by
      calc b * h * b⁻¹ = h * b * b⁻¹ := by rw [hcomm]
        _ = h := by group
    rw [e]
    exact hh
  · intro hh
    have hc : b * h * b⁻¹ ∈ B := hHB hh
    have e1 := hB b hb (b * h * b⁻¹) hc
    have e2 : b * h * b⁻¹ = h := by
      calc b * h * b⁻¹ = b⁻¹ * (b * (b * h * b⁻¹)) := by group
        _ = b⁻¹ * ((b * h * b⁻¹) * b) := by rw [e1]
        _ = h := by group
    rw [e2] at hh
    exact hh

theorem l73_rank_one (hc : S6Ctx G 3) (i106 : I106L62At G) {B : Subgroup G} {x : G} {L : Subgroup G}
    {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 11 y J) {a : G}
    {K T I Sg : Subgroup G} (C : L73Ctx B x L 11 y J a K T I Sg) (hL62 : IsL62Type 3 K) :
    ∀ F : Subgroup G, F ≤ centModSubgroup 3 K ⊓ Subgroup.centralizer ({a} : Set G) →
      IsElemAbelian 3 F → Nat.card ↥F ≤ 3 := by
  intro F hF hFel
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Subgroup.center (PQuot 3 K) = ⊥ := hL62.2
  have hFK : F ≤ centModSubgroup 3 K := fun f hf => (Subgroup.mem_inf.1 (hF hf)).1
  have hF3 : IsPGroup 3 F := isPGroup_of_isElemAbelian hFel
  haveI : IsMulCommutative ↥F := hFel.1
  obtain ⟨E, U, hEK, hEel, hEcard, hUK, hU2, hUnot, hEN⟩ := (i106 K hL62).2
  obtain ⟨E', hE'C, hE'el, hE'im⟩ := exists_lift_elemAbelian_centralizing hF3 hFK hEK hEel
  have hE'K : E' ≤ K := fun e he => (Subgroup.mem_inf.1 (hE'C he)).1
  haveI : IsMulCommutative ↥E' := hE'el.1
  have hFE' : ∀ e ∈ E', ∀ f ∈ F, e * f = f * e := fun e he f hf =>
    ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (hE'C he)).2) f hf).symm
  have hE'C' : E' ≤ Subgroup.centralizer (F : Set G) := fun e he =>
    Subgroup.mem_centralizer_iff.2 (fun f hf => (hFE' e he f hf).symm)
  have hFC : F ≤ Subgroup.centralizer (E' : Set G) := fun f hf =>
    Subgroup.mem_centralizer_iff.2 (fun e he => hFE' e he f hf)
  have hE'card : Nat.card ↥E' = 3 ^ 3 := by
    rw [← (imageMod_elemAbelian hp hE'K hE'el).2, hE'im, (imageMod_elemAbelian hp hEK hEel).2, hEcard]
  have hE'F : E' ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzE, hzF⟩ := Subgroup.mem_inf.1 hz
    have hzO : z ∈ GLAPPrimeCoreOf 3 K :=
      mem_glaPPrimeCoreOf_of_centMod hZ (hE'K hzE) (centMod_iff.2 (hFK hzF))
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hord : orderOf z = 3 := orderOf_eq_prime (hE'el.2 z hzE) hz1
    have hdvd : orderOf (⟨z, hzO⟩ : ↥(GLAPPrimeCoreOf 3 K)) ∣ Nat.card ↥(GLAPPrimeCoreOf 3 K) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord] at hdvd
    exact not_dvd_card_glaPPrimeCoreOf hp K hdvd
  have hcardsup := card_sup_mul_card_inf_of_le_normalizer (A := E') (B := F)
    (hFC.trans (Subgroup.centralizer_le_normalizer _))
  rw [hE'F, Subgroup.card_bot, mul_one, hE'card] at hcardsup
  have hH : (E' ⊔ F : Subgroup G) ≤ Subgroup.centralizer ((E' ⊔ F : Subgroup G) : Set G) := by
    rw [centralizer_sup_eq]
    exact le_inf (sup_le (Subgroup.le_centralizer E') hFC)
      (sup_le hE'C' (Subgroup.le_centralizer F))
  have hHcomm : IsMulCommutative ↥(E' ⊔ F : Subgroup G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.1 hH
  have hdec : ∀ x ∈ E' ⊔ F, ∃ e ∈ E', ∃ f ∈ F, e * f = x := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, F.one_mem, mul_one y⟩
      · exact ⟨1, E'.one_mem, y, hy, one_mul y⟩
    · exact ⟨1, E'.one_mem, 1, F.one_mem, one_mul 1⟩
    · rintro a b _ _ ⟨e₁, he₁, f₁, hf₁, rfl⟩ ⟨e₂, he₂, f₂, hf₂, rfl⟩
      refine ⟨e₁ * e₂, E'.mul_mem he₁ he₂, f₁ * f₂, F.mul_mem hf₁ hf₂, ?_⟩
      calc e₁ * e₂ * (f₁ * f₂) = e₁ * (e₂ * f₁) * f₂ := by group
        _ = e₁ * (f₁ * e₂) * f₂ := by rw [hFE' e₂ he₂ f₁ hf₁]
        _ = e₁ * f₁ * (e₂ * f₂) := by group
    · rintro a _ ⟨e, he, f, hf, rfl⟩
      refine ⟨e⁻¹, E'.inv_mem he, f⁻¹, F.inv_mem hf, ?_⟩
      have hc : Commute e f := hFE' e he f hf
      rw [mul_inv_rev]
      exact hc.inv_inv
  have hHexp : ∀ x ∈ E' ⊔ F, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨e, he, f, hf, rfl⟩ := hdec x hx
    rw [(show Commute e f from hFE' e he f hf).mul_pow, hE'el.2 e he, hFel.2 f hf, one_mul]
  have hHel : IsElemAbelian 3 (E' ⊔ F : Subgroup G) := ⟨hHcomm, hHexp⟩
  have hPgrp : IsPGroup 3 (E' ⊔ F : Subgroup G) := isPGroup_of_isElemAbelian hHel
  obtain ⟨Ub, hUb⟩ : ∃ Ub : Subgroup (PQuot 3 K), Ub = imageMod 3 K U := ⟨_, rfl⟩
  obtain ⟨Uh, hUh⟩ : ∃ Uh : Subgroup G, Uh = preMod 3 K Ub := ⟨_, rfl⟩
  obtain ⟨hUb2, hUbN⟩ := l72_imageMod_facts (p := 3) hEK hUK hU2 hEN
  rw [← hUb] at hUb2 hUbN
  have hUhK : Uh ≤ K := by
    intro z hz
    rw [hUh] at hz
    obtain ⟨hzK, -⟩ := mem_preMod_iff.1 hz
    exact hzK
  have hUUh : U ≤ Uh := by
    intro u hu
    rw [hUh, hUb]
    refine mem_preMod_iff.2 ⟨hUK hu, ?_⟩
    exact Subgroup.mem_map.2 ⟨⟨u, hUK hu⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩
  have hOUh : GLAPPrimeCoreOf 3 K ≤ Uh := by
    intro o ho
    have hoK : o ∈ K := primeCoreOf_le_self 3 K ho
    have h1 : (QuotientGroup.mk ⟨o, hoK⟩ : PQuot 3 K) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((y5x_mem_primeCore_iff ⟨o, hoK⟩).2 ho)
    rw [hUh]
    refine mem_preMod_iff.2 ⟨hoK, ?_⟩
    rw [h1]
    exact Subgroup.one_mem _
  have hE'N : E' ≤ Subgroup.normalizer (Uh : Set G) := by
    intro e he
    have heK : e ∈ K := hE'K he
    have hmem : (QuotientGroup.mk ⟨e, heK⟩ : PQuot 3 K) ∈ imageMod 3 K E' :=
      Subgroup.mem_map.2 ⟨⟨e, heK⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
    rw [hE'im] at hmem
    rw [hUh]
    exact mem_normalizer_preMod heK (hUbN hmem)
  have hFN : F ≤ Subgroup.normalizer (Uh : Set G) := by
    intro f hf
    have hfK : f ∈ centModSubgroup 3 K := hFK hf
    have hfN : f ∈ Subgroup.normalizer (K : Set G) := (mem_centModSubgroup.1 hfK).1
    have hcm : ∀ h ∈ K, ⁅h, f⁆ ∈ GLAPPrimeCoreOf 3 K :=
      fun h hh => (mem_centModSubgroup.1 hfK).2 h hh
    rw [Subgroup.mem_normalizer_iff]
    intro h
    by_cases hhK : h ∈ K
    · have hid : f * h * f⁻¹ = (⁅h, f⁆)⁻¹ * h := by
        rw [commutatorElement_def]
        group
      have ho : ⁅h, f⁆ ∈ Uh := hOUh (hcm h hhK)
      rw [hid, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ ho)]
    · constructor
      · intro hh
        exact absurd (hUhK hh) hhK
      · intro hh
        exact absurd (hUhK hh) (fun hK' => hhK ((Subgroup.mem_normalizer_iff.1 hfN h).2 hK'))
  have hcopUh : Nat.Coprime 3 (Nat.card ↥Uh) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 (fun h3 => ?_)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hzG3 : (z : G) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one z
      rw [hz] at h
      simpa using congrArg Subtype.val h
    have hz1 : (z : G) ≠ 1 := by
      intro h1
      have hz' : z = 1 := Subtype.ext h1
      rw [hz', orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hzK : (z : G) ∈ K := hUhK z.2
    have hzU' : (z : G) ∈ preMod 3 K Ub := by
      rw [← hUh]
      exact z.2
    obtain ⟨_hzKq, hzU⟩ := mem_preMod_iff.1 hzU'
    obtain ⟨q, hq⟩ : ∃ q : PQuot 3 K, q = QuotientGroup.mk ⟨(z : G), hzK⟩ := ⟨_, rfl⟩
    have hq3 : q ^ 3 = 1 := by
      rw [hq, ← QuotientGroup.mk_pow]
      have h1 : (⟨(z : G), hzK⟩ : ↥K) ^ 3 = 1 := Subtype.ext (by simpa using hzG3)
      rw [h1, QuotientGroup.mk_one]
    have hqU : q ∈ Ub := by
      rw [hq]
      exact hzU
    have hq1 : q = 1 := by
      obtain ⟨k, hk⟩ := hUb2 ⟨q, hqU⟩
      have hw3 : (⟨q, hqU⟩ : ↥Ub) ^ 3 = 1 := Subtype.ext (by simpa using hq3)
      have h1 : orderOf (⟨q, hqU⟩ : ↥Ub) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
      have h2 : orderOf (⟨q, hqU⟩ : ↥Ub) ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
      have h3' : orderOf (⟨q, hqU⟩ : ↥Ub) = 1 :=
        Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) h1 h2
      exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3')
    have hzO : (z : G) ∈ GLAPPrimeCoreOf 3 K :=
      (y5x_mem_primeCore_iff ⟨(z : G), hzK⟩).1 ((QuotientGroup.eq_one_iff _).1 (hq.symm.trans hq1))
    have hdvd : orderOf (⟨(z : G), hzO⟩ : ↥(GLAPPrimeCoreOf 3 K)) ∣
        Nat.card ↥(GLAPPrimeCoreOf 3 K) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, orderOf_eq_prime hzG3 hz1] at hdvd
    exact not_dvd_card_glaPPrimeCoreOf hp K hdvd
  have hodd : ¬ Odd (Nat.card ↥Uh) := by
    have hUbot : U ≠ ⊥ := fun h => hUnot (by rw [h]; exact bot_le)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hU2
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hUbot (Subgroup.card_eq_one.1 (by rw [hm]; norm_num))
    have h2U : 2 ∣ Nat.card ↥U := by
      rw [hm]
      exact dvd_pow_self 2 hm0
    exact Nat.not_odd_iff_even.2 (even_iff_two_dvd.2 (h2U.trans (Subgroup.card_dvd_of_le hUUh)))
  obtain ⟨U', hU'Uh, hU'bot, hU'2, hU'N⟩ :=
    exists_invariant_twoGroup hp hc.odd hPgrp (sup_le hE'N hFN) hcopUh hodd
  have hbound := card_le_pow_glaTwoLocalRank hp hHel hU'bot hU'2 hU'N
  have hB34 : Nat.card ↥B = 3 ^ 4 := l73_card_B hc hB S (by norm_num)
  have hBGL : Nat.card ↥B = 3 ^ GLATwoLocalRank 3 G := (IsSStarMax.bmax hB).2.1
  rw [← hBGL, hB34, hcardsup] at hbound
  norm_num at hbound
  omega

theorem l73_B_eq_K (hc : S6Ctx G 3) (i106 : I106L62At G) (i71 : I71L62At G) {B : Subgroup G} {x : G}
    {L : Subgroup G} {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L) (S : AltSetup 3 B x L 11 y J)
    {a : G} {K T I Sg : Subgroup G} (C : L73Ctx B x L 11 y J a K T I Sg) (hL62 : IsL62Type 3 K)
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) : IsDirectZpowersInf B a K := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hBel : IsElemAbelian 3 B := (IsSStarMax.bmax hB).1
  have hBcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b :=
    fun b hb c hc' => isElemAbelian_commute hBel hb hc'
  obtain ⟨hBeq, -⟩ := C.ti.B_eq_I (Or.inr rfl)
  have hDB : altDxy x y ≤ B := by
    intro z hz
    rw [hBeq]
    exact Subgroup.mem_sup_left hz
  have haB : a ∈ B := hDB C.a_mem
  have ha3 : a ^ 3 = 1 := S.isElemAbelian_D.2 a C.a_mem
  have ha1 : a ≠ 1 := C.a_ne
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := isSubnormal_le' C.K_sn
  have hO_le_K : GLAPPrimeCoreOf 3 K ≤ K := primeCoreOf_le_self 3 K
  have hKC1 : ∀ k ∈ K, k ∈ centModSubgroup 3 K → k ∈ GLAPPrimeCoreOf 3 K :=
    fun k hk hkc => y5x_mem_primeCore_of_centMod hL62.2 hk hkc
  have hO_C1 : GLAPPrimeCoreOf 3 K ≤ centModSubgroup 3 K ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro o ho
    refine Subgroup.mem_inf.2 ⟨⟨Subgroup.le_normalizer (hO_le_K ho), fun l hl => ?_⟩, hKa (hO_le_K ho)⟩
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (y5x_conj_mem_primeCore hl ho) (Subgroup.inv_mem _ ho)
  have haK : a ∉ K := by
    intro haK
    have hcm : a ∈ centModSubgroup 3 K := by
      refine ⟨hBK haB, fun l hl => ?_⟩
      have hla : l * a = a * l := Subgroup.mem_centralizer_singleton_iff.1 (hKa hl)
      have h1 : ⁅l, a⁆ = 1 := by
        rw [commutatorElement_def, hla]
        group
      rw [h1]
      exact Subgroup.one_mem _
    have hO := y5x_mem_primeCore_of_centMod hL62.2 haK hcm
    have hdvd : orderOf (⟨a, hO⟩ : ↥(GLAPPrimeCoreOf 3 K)) ∣ Nat.card ↥(GLAPPrimeCoreOf 3 K) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, orderOf_eq_prime ha3 ha1] at hdvd
    exact not_dvd_card_glaPPrimeCoreOf hp K hdvd
  have hdecomp : ∀ b ∈ B, ∃ l ∈ K,
      b * l⁻¹ ∈ centModSubgroup 3 K ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro b hb
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := hBK hb
    have hb3 : IsPGroup 3 (Subgroup.zpowers b) :=
      isPGroup_of_isElemAbelian (isElemAbelian_zpowers_of_mem hBel hb)
    obtain ⟨l, hlK, hl⟩ := i71 K hL62 b hbN hb3
    refine ⟨l, hlK, Subgroup.mem_inf.2 ⟨⟨?_, fun k hk => ?_⟩, ?_⟩⟩
    · exact Subgroup.mul_mem _ hbN (Subgroup.inv_mem _ (Subgroup.le_normalizer hlK))
    · obtain ⟨y, hy⟩ : ∃ y, y = l⁻¹ * k * l := ⟨_, rfl⟩
      have hyK : y ∈ K := by
        rw [hy]
        exact K.mul_mem (K.mul_mem (K.inv_mem hlK) hk) hlK
      obtain ⟨w, hw⟩ : ∃ w, w = b * y * b⁻¹ := ⟨_, rfl⟩
      have hwK : w ∈ K := by
        rw [hw]
        exact (Subgroup.mem_normalizer_iff.1 hbN y).1 hyK
      have hbw : b⁻¹ * w * b = y := by
        rw [hw]
        group
      have hO1 : (l⁻¹ * w * l)⁻¹ * y ∈ GLAPPrimeCoreOf 3 K := by
        have h1 := hl w hwK
        rwa [hbw] at h1
      have hO2 := y5x_conj_mem_primeCore hwK (y5x_conj_mem_primeCore hlK hO1)
      have e1 : k * (b * l⁻¹) * k⁻¹ * (b * l⁻¹)⁻¹ = k * w⁻¹ := by
        rw [hw, hy]
        group
      have e2 : w * (l * ((l⁻¹ * w * l)⁻¹ * y) * l⁻¹) * w⁻¹ = k * w⁻¹ := by
        rw [hy]
        group
      rw [e2] at hO2
      rw [commutatorElement_def, e1]
      exact hO2
    · exact Subgroup.mul_mem _ (Subgroup.mem_centralizer_singleton_iff.2 (hBcomm a haB b hb).symm)
        (Subgroup.inv_mem _ (hKa hlK))
  have hBKN : B ⊔ K ≤ Subgroup.normalizer (K : Set G) :=
    sup_le hBK (fun k hk => Subgroup.le_normalizer hk)
  have hKn : (K.subgroupOf (B ⊔ K)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_sup_right]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.1 (hBKN hk) h).1 hh
  haveI := hKn
  have hsupTop : B.subgroupOf (B ⊔ K) ⊔ K.subgroupOf (B ⊔ K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hdec : ∀ X : ↥(B ⊔ K), ∃ b ∈ B.subgroupOf (B ⊔ K), ∃ z ∈ K.subgroupOf (B ⊔ K),
      b * z = X := by
    intro X
    have hX : X ∈ B.subgroupOf (B ⊔ K) ⊔ K.subgroupOf (B ⊔ K) := by
      rw [hsupTop]
      exact Subgroup.mem_top X
    exact Subgroup.mem_sup_of_normal_right.1 hX
  have hpi : ∀ X : ↥(B ⊔ K), ∃ b : ↥(B ⊔ K), b ∈ B.subgroupOf (B ⊔ K) ∧
      QuotientGroup.mk' (K.subgroupOf (B ⊔ K)) X = QuotientGroup.mk' (K.subgroupOf (B ⊔ K)) b := by
    intro X
    obtain ⟨b, hb, z, hz, rfl⟩ := hdec X
    refine ⟨b, hb, ?_⟩
    have hz1 : QuotientGroup.mk' (K.subgroupOf (B ⊔ K)) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
    rw [map_mul, hz1, mul_one]
  have hV1 : ∀ x ∈ B ⊔ K, ∀ y ∈ B ⊔ K, x⁻¹ * y⁻¹ * x * y ∈ K := by
    intro x hx y hy
    obtain ⟨b1, hb1, hX⟩ := hpi (⟨x, hx⟩ : ↥(B ⊔ K))
    obtain ⟨b2, hb2, hY⟩ := hpi (⟨y, hy⟩ : ↥(B ⊔ K))
    have hcomm : (b1 : G) * (b2 : G) = (b2 : G) * (b1 : G) :=
      hBcomm _ (Subgroup.mem_subgroupOf.1 hb1) _ (Subgroup.mem_subgroupOf.1 hb2)
    have hcommS : b1 * b2 = b2 * b1 := Subtype.ext hcomm
    have hbb : b1⁻¹ * b2⁻¹ * b1 * b2 = 1 := by
      calc b1⁻¹ * b2⁻¹ * b1 * b2 = (b2 * b1)⁻¹ * (b1 * b2) := by group
        _ = (b1 * b2)⁻¹ * (b1 * b2) := by rw [← hcommS]
        _ = 1 := inv_mul_cancel _
    have key : QuotientGroup.mk' (K.subgroupOf (B ⊔ K))
        ((⟨x, hx⟩ : ↥(B ⊔ K))⁻¹ * (⟨y, hy⟩ : ↥(B ⊔ K))⁻¹ * (⟨x, hx⟩ : ↥(B ⊔ K)) * (⟨y, hy⟩ : ↥(B ⊔ K))) = 1 := by
      have e : QuotientGroup.mk' (K.subgroupOf (B ⊔ K))
          ((⟨x, hx⟩ : ↥(B ⊔ K))⁻¹ * (⟨y, hy⟩ : ↥(B ⊔ K))⁻¹ * (⟨x, hx⟩ : ↥(B ⊔ K)) * (⟨y, hy⟩ : ↥(B ⊔ K))) =
          QuotientGroup.mk' (K.subgroupOf (B ⊔ K)) (b1⁻¹ * b2⁻¹ * b1 * b2) := by
        simp only [map_mul, map_inv, hX, hY]
      rw [e, hbb, map_one]
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 key)
  have hV2 : ∀ x ∈ B ⊔ K, x ^ 3 ∈ K := by
    intro x hx
    obtain ⟨b, hb, hX⟩ := hpi (⟨x, hx⟩ : ↥(B ⊔ K))
    have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hBel.2 (b : G) (Subgroup.mem_subgroupOf.1 hb))
    have key : QuotientGroup.mk' (K.subgroupOf (B ⊔ K)) ((⟨x, hx⟩ : ↥(B ⊔ K)) ^ 3) = 1 := by
      rw [map_pow, hX, ← map_pow, hb3, map_one]
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 key)
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup G,
      F = (B ⊔ K) ⊓ (centModSubgroup 3 K ⊓ Subgroup.centralizer ({a} : Set G)) := ⟨_, rfl⟩
  have hF_mem : ∀ z, z ∈ F ↔
      z ∈ B ⊔ K ∧ z ∈ centModSubgroup 3 K ⊓ Subgroup.centralizer ({a} : Set G) := by
    intro z
    rw [hFdef, Subgroup.mem_inf]
  have hFBK : F ≤ B ⊔ K := fun z hz => ((hF_mem z).1 hz).1
  have hFC1 : F ≤ centModSubgroup 3 K ⊓ Subgroup.centralizer ({a} : Set G) :=
    fun z hz => ((hF_mem z).1 hz).2
  have hFN : F ≤ Subgroup.normalizer (K : Set G) := fun z hz => hBKN (hFBK hz)
  have hKF : K ⊓ F = GLAPPrimeCoreOf 3 K := by
    apply le_antisymm
    · rintro z ⟨hzK, hzF⟩
      exact hKC1 z hzK (Subgroup.mem_inf.1 (hFC1 hzF)).1
    · intro o ho
      exact ⟨hO_le_K ho, (hF_mem o).2 ⟨Subgroup.mem_sup_right (hO_le_K ho), hO_C1 ho⟩⟩
  have hBsub : ∀ b ∈ B, b ∈ K ⊔ F := by
    intro b hb
    obtain ⟨l, hlK, hu⟩ := hdecomp b hb
    have huBK : b * l⁻¹ ∈ B ⊔ K :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right (Subgroup.inv_mem _ hlK))
    have huF : b * l⁻¹ ∈ F := (hF_mem _).2 ⟨huBK, hu⟩
    have h2 : b * l⁻¹ * l ∈ K ⊔ F := Subgroup.mul_mem _ (Subgroup.mem_sup_right huF) (Subgroup.mem_sup_left hlK)
    simpa using h2
  have hsupKF : K ⊔ F = K ⊔ B := by
    apply le_antisymm
    · exact sup_le le_sup_left (hFBK.trans (sup_le le_sup_right le_sup_left))
    · exact sup_le le_sup_left (fun b hb => hBsub b hb)
  have hc1 := card_sup_mul_card_inf_of_le_normalizer hFN
  have hc2 := card_sup_mul_card_inf_of_le_normalizer hBK
  rw [hsupKF, hKF] at hc1
  have hKpos : 0 < Nat.card ↥K := Nat.card_pos
  have hFcard : Nat.card ↥F * Nat.card ↥(K ⊓ B) =
      Nat.card ↥(GLAPPrimeCoreOf 3 K) * Nat.card ↥B := by
    apply Nat.eq_of_mul_eq_mul_left hKpos
    calc Nat.card ↥K * (Nat.card ↥F * Nat.card ↥(K ⊓ B))
        = (Nat.card ↥K * Nat.card ↥F) * Nat.card ↥(K ⊓ B) := by ring
      _ = (Nat.card ↥(K ⊔ B) * Nat.card ↥(GLAPPrimeCoreOf 3 K)) * Nat.card ↥(K ⊓ B) := by rw [← hc1]
      _ = Nat.card ↥(GLAPPrimeCoreOf 3 K) * (Nat.card ↥(K ⊔ B) * Nat.card ↥(K ⊓ B)) := by ring
      _ = Nat.card ↥(GLAPPrimeCoreOf 3 K) * (Nat.card ↥K * Nat.card ↥B) := by rw [hc2]
      _ = Nat.card ↥K * (Nat.card ↥(GLAPPrimeCoreOf 3 K) * Nat.card ↥B) := by ring
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le (inf_le_right : K ⊓ B ≤ B)
  have hpos : 0 < Nat.card ↥(K ⊓ B) := Nat.card_pos
  have hFt : Nat.card ↥F = Nat.card ↥(GLAPPrimeCoreOf 3 K) * t := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [hFcard, ht]
    ring
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (isPGroup_of_isElemAbelian hBel)
  have htdvd : t ∣ 3 ^ m := ⟨Nat.card ↥(K ⊓ B), by rw [← hm, ht]; ring⟩
  obtain ⟨n, -, htn⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 htdvd
  have hdvdF : 3 ^ n ∣ Nat.card ↥F := by
    rw [hFt, htn]
    exact dvd_mul_left _ _
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvdF
  obtain ⟨P', hP'def⟩ : ∃ P' : Subgroup G, P' = P.map F.subtype := ⟨_, rfl⟩
  have hP'card : Nat.card ↥P' = 3 ^ n := by
    rw [hP'def, Subgroup.card_map_of_injective (f := F.subtype) Subtype.val_injective, hP]
  have hP'F : P' ≤ F := by
    rw [hP'def]
    exact Subgroup.map_subtype_le P
  have hP'C1 : P' ≤ centModSubgroup 3 K ⊓ Subgroup.centralizer ({a} : Set G) :=
    fun z hz => hFC1 (hP'F hz)
  have hP'O : P' ⊓ GLAPPrimeCoreOf 3 K = ⊥ := by
    have hcop : Nat.Coprime (3 ^ n) (Nat.card ↥(GLAPPrimeCoreOf 3 K)) :=
      Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp K))
    have h1 : Nat.card ↥(P' ⊓ GLAPPrimeCoreOf 3 K) ∣ 3 ^ n := by
      rw [← hP'card]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(P' ⊓ GLAPPrimeCoreOf 3 K) ∣ Nat.card ↥(GLAPPrimeCoreOf 3 K) :=
      Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.Coprime (Nat.card ↥(P' ⊓ GLAPPrimeCoreOf 3 K)) (3 ^ n) :=
      (Nat.Coprime.coprime_dvd_right h2 hcop).symm
    exact Subgroup.card_eq_one.1 (Nat.Coprime.eq_one_of_dvd h3 h1)
  have hPcomm : ∀ u ∈ P', ∀ v ∈ P', u * v = v * u := by
    intro u hu v hv
    have huF := hP'F hu
    have hvF := hP'F hv
    have huB : u ∈ B ⊔ K := ((hF_mem u).1 huF).1
    have hvB : v ∈ B ⊔ K := ((hF_mem v).1 hvF).1
    have h1 : u⁻¹ * v⁻¹ * u * v ∈ K := hV1 u huB v hvB
    have h2 : u⁻¹ * v⁻¹ * u * v ∈ F :=
      F.mul_mem (F.mul_mem (F.mul_mem (F.inv_mem huF) (F.inv_mem hvF)) huF) hvF
    have h3 : u⁻¹ * v⁻¹ * u * v ∈ P' :=
      P'.mul_mem (P'.mul_mem (P'.mul_mem (P'.inv_mem hu) (P'.inv_mem hv)) hu) hv
    have h4 : u⁻¹ * v⁻¹ * u * v ∈ GLAPPrimeCoreOf 3 K := by
      rw [← hKF]
      exact ⟨h1, h2⟩
    have h5 : u⁻¹ * v⁻¹ * u * v = 1 := by
      have h6 : u⁻¹ * v⁻¹ * u * v ∈ P' ⊓ GLAPPrimeCoreOf 3 K := ⟨h3, h4⟩
      rw [hP'O] at h6
      exact Subgroup.mem_bot.1 h6
    have e : v⁻¹ * u * v = u := by
      calc v⁻¹ * u * v = u * (u⁻¹ * v⁻¹ * u * v) := by group
        _ = u := by rw [h5, mul_one]
    calc u * v = v * (v⁻¹ * u * v) := by group
      _ = v * u := by rw [e]
  have hPexp : ∀ z ∈ P', z ^ 3 = 1 := by
    intro z hz
    have hzF := hP'F hz
    have h1 : z ^ 3 ∈ K := hV2 z ((hF_mem z).1 hzF).1
    have h2 : z ^ 3 ∈ F := F.pow_mem hzF 3
    have h3 : z ^ 3 ∈ P' := P'.pow_mem hz 3
    have h4 : z ^ 3 ∈ GLAPPrimeCoreOf 3 K := by
      rw [← hKF]
      exact ⟨h1, h2⟩
    have h6 : z ^ 3 ∈ P' ⊓ GLAPPrimeCoreOf 3 K := ⟨h3, h4⟩
    rw [hP'O] at h6
    exact Subgroup.mem_bot.1 h6
  have hP'el : IsElemAbelian 3 P' :=
    ⟨⟨⟨fun u v => Subtype.ext (hPcomm u.1 u.2 v.1 v.2)⟩⟩, hPexp⟩
  have hrank : Nat.card ↥P' ≤ 3 := l73_rank_one hc i106 hB S C hL62 P' hP'C1 hP'el
  have hn3 : 3 ^ n ≤ 3 := hP'card ▸ hrank
  have hBle : t ≠ 1 := by
    intro ht1
    have hcard : Nat.card ↥B ≤ Nat.card ↥(K ⊓ B) := by rw [ht, ht1, mul_one]
    have heq : K ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right hcard
    apply haK
    have h7 : a ∈ K ⊓ B := by
      rw [heq]
      exact haB
    exact h7.1
  have ht3 : t = 3 := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · interval_cases n
      · exact absurd (by simpa using htn) hBle
      · simpa using htn
    · exfalso
      have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
  have hZcard : Nat.card ↥(Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha3 ha1]
  have hZK : Subgroup.zpowers a ⊓ K = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers a ⊓ K) ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ K = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hZcard, h1])
      apply haK
      have h7 : a ∈ Subgroup.zpowers a ⊓ K := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact h7.2
  have hZBK : Subgroup.zpowers a ⊓ (B ⊓ K) = ⊥ := by
    have h1 := inf_le_inf_left (Subgroup.zpowers a) (inf_le_right : B ⊓ K ≤ K)
    rw [hZK] at h1
    exact le_bot_iff.1 h1
  have hZN : Subgroup.zpowers a ≤ Subgroup.normalizer ((B ⊓ K : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 haB).trans (y5x_le_normalizer_of_comm hBcomm inf_le_left)
  have hcardZ := card_sup_mul_card_inf_of_le_normalizer hZN
  have hBKinf : (B ⊓ K) ⊓ Subgroup.zpowers a = ⊥ := by
    rw [inf_comm]
    exact hZBK
  rw [hBKinf, Subgroup.card_bot, mul_one, hZcard] at hcardZ
  have hsup : (B ⊓ K) ⊔ Subgroup.zpowers a = B := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (Subgroup.zpowers_le.2 haB))
    have hBcard : Nat.card ↥B = Nat.card ↥(B ⊓ K) * 3 := by
      rw [ht, ht3, inf_comm]
    apply le_of_eq
    rw [hBcard, hcardZ]
  refine ⟨?_, hZBK⟩
  rw [sup_comm]
  exact hsup.symm

theorem l73_n11 (hc : S6Ctx G 3) (i183 : Input18_3_4) (i112 : I112StarAt G 3) (hne : AltNotWeakExcAt)
    (i1422 : I1422At G) (i2017 : I2017At G) (i182 : I182At G) (i106 : I106L62At G)
    (i71 : I71L62At G) {B : Subgroup G}
    {x : G} {L : Subgroup G} {y : G} {J : Subgroup G} (hB : IsSStarMax 3 B x L)
    (S : AltSetup 3 B x L 11 y J) (hyB : y ∈ B) {a : G} {K T I Sg : Subgroup G}
    (C : L73Ctx B x L 11 y J a K T I Sg) : L73Final B a K J I Sg := by
  have hn : (7 : ℕ) < 11 - 3 := by norm_num
  have hK : L72Single 3 (altDxy x y) J K a := by
    rw [C.K_eq]; exact l72_single hc i183 i112 hne hB S hn C.a_mem C.a_ne
  obtain ⟨b, hbD, hba, hDab⟩ := exists_pair_of_card_sq hc.prime S.card_D C.a_mem C.a_ne
    S.isElemAbelian_D
  have hXK : CFSG.Open.IsKGroup ↥(Subgroup.centralizer ({a} : Set G)) := kGroup_centralizer hc C.a_ne
  have hKa : K ≤ Subgroup.centralizer ({a} : Set G) := hK.comp.1
  have hJb : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set G)) J := by
    rw [← inf_centralizer_D_eq hKa hDab]; exact hK.J_comp
  have hb3 : b ^ 3 = 1 := S.isElemAbelian_D.2 b hbD
  have hbK : b ∈ Subgroup.normalizer (K : Set G) := hK.norm hbD
  have hJ8 : IsAltPType 3 J 8 := S.J_alt
  have hBK := l73_B_norm_K hc hB S (Or.inr rfl) hyB C
  have hxB : x ∈ B := (IsSStarMax.essential hB).1
  have haB : a ∈ B := (sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB) : altDxy x y ≤ B) C.a_mem
  have hIK : I ≤ K := C.ti.I_le_J.trans C.J_le_K
  have hJ8' := i1422 (Subgroup.centralizer ({a} : Set G)) K J b hXK hK.comp hbK hb3 hJb hJ8
  have hI7 : IsAltPType 3 I 7 := C.ti.I_alt
  have hI7' := l73_imageMod_alt S C hK hJ8'
  have hlayer := l73_layer_KD hc i182 hB S C.a_mem C.K_sn C.J_le_K hK.J_comp
  have hrank : ∀ E : Subgroup G, E ≤ (K ⊔ altDxy x y) ⊓ Subgroup.centralizer (altDxy x y : Set G) →
      IsElemAbelian 3 E → Nat.card ↥E ≤ 3 ^ 4 := fun E hE hEel =>
    l73_rank_Cx hc hB S (by norm_num) E
      (hE.trans (inf_le_right.trans (Subgroup.centralizer_le (by
        have : x ∈ altDxy x y := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
        simpa using this)))) hEel
  have hcent : CentMod 3 K a := centMod_of_mem_centralizer (fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKa hk))
  by_cases hSt : Sg ≤ GLAPPrimeCoreOf 3 K
  · exfalso
    have hG := l73_isGStar_K hc i182 hB S hyB C hBK
    have h413 := hc.stage4.2.1 B a K (IsSStarMax.bmax hB) haB C.a_ne hK.comp hG
    rw [closureIn_eq_self hBK] at h413
    exact l73_false_of_S_le_core hc C hSt h413
  · have hcen' : ¬ imageMod 3 K I ≤ Subgroup.centralizer ((imageMod 3 K Sg : Subgroup (PQuot 3 K)) :
        Set (PQuot 3 K)) := fun h => hSt (l73_S_le_core_of_cen hIK C.S_le_K C.S_comm h)
    have hL62 : IsL62Type 3 K := i2017 (Subgroup.centralizer ({a} : Set G)) K (altDxy x y) J I Sg hXK hK.comp
      hK.norm S.isElemAbelian_D S.card_D ⟨a, C.a_mem, C.a_ne, hcent⟩ hrank hlayer hK.J_comp hJ8'
      C.ti.I_le_J hI7' C.S_le_K C.S_two (sup_le C.I_norm C.D_norm) hcen'
    exact ⟨hK.comp, hL62, l73_B_eq_K hc i106 i71 hB S C hL62 hBK, hSt, hJ8', hI7'⟩

end CFSG.LocalAnalysis.GLTheoremA

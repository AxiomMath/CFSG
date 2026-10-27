module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZYN
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1W16
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentZOrder

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem isCharacteristicP_of_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ} (e : A ≃* B)
    (h : CFSG.IsCharacteristicP p A) : CFSG.IsCharacteristicP p B := by
  unfold CFSG.IsCharacteristicP at h ⊢
  intro b hb
  rw [← CFSG.pCore_map_iso p e] at hb ⊢
  refine ⟨e.symm b, h ?_, by simp⟩
  rw [Subgroup.mem_centralizer_iff] at hb ⊢
  intro a ha
  have h1 := hb (e a) ⟨a, ha, rfl⟩
  apply e.injective
  simpa using h1

theorem map_conj_centralizer_singleton {X : Type*} [Group X] (a c : X) :
    (Subgroup.centralizer {a}).map (MulAut.conj c : X →* X) =
      Subgroup.centralizer {c * a * c⁻¹} := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hh
    change c * h * c⁻¹ * (c * a * c⁻¹) = c * a * c⁻¹ * (c * h * c⁻¹)
    calc c * h * c⁻¹ * (c * a * c⁻¹) = c * (h * a) * c⁻¹ := by group
      _ = c * (a * h) * c⁻¹ := by rw [hh]
      _ = c * a * c⁻¹ * (c * h * c⁻¹) := by group
  · intro hg
    refine ⟨c⁻¹ * g * c, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by
      change c * (c⁻¹ * g * c) * c⁻¹ = g
      group⟩
    calc c⁻¹ * g * c * a = c⁻¹ * (g * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * a * c⁻¹ * g) * c := by rw [hg]
      _ = a * (c⁻¹ * g * c) := by group

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
  (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
include d htype

theorem normal_e1YSylow
    : (d.e1YSylow : Subgroup (E1Y (Subgroup.center J) u m y x)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine normal_of_abelian_sylow_E16_of_relIndex_of_pPrimeCore
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) d.e1YSylow ?_ ?_ ?_ ?_ ?_ <;>
    rw [d.coe_e1YSylow]
  · exact fun a ha b hb => d.commute_of_mem_map_e1Pi ha hb
  · exact fun a ha => d.mul_self_of_mem_map_e1Pi ha
  · exact d.card_map_e1Pi
  · exact d.relIndex_centralizer_normalizer_e1Y_le htype
  · exact fun n hn hnC a ha ha1 => d.conj_ne_of_not_mem_centralizer_e1Y htype hn hnC ha ha1

theorem conj_mem_e1RBar_sup_pPrimeCore
    {g : J ⧸ Subgroup.center J}
    (hg : g ∈ e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))) {r : J ⧸ Subgroup.center J}
    (hr : r ∈ e1RBar (Subgroup.center J) u m y x) :
    g * r * g⁻¹ ∈ e1RBar (Subgroup.center J) u m y x ⊔
      (CFSG.pPrimeCore 2 (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹)))).map
        (e1M0 (Subgroup.center J) (u * (x * u * x⁻¹))).subtype :=
  d.conj_mem_e1RBar_sup_of_normal (d.coe_e1YSylow ▸ d.normal_e1YSylow htype) hg hr

theorem exists_mul_mem_pPrimeCore_normalizer
    {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}) :
    ∃ o ∈ (CFSG.pPrimeCore 2 (Subgroup.centralizer
        {caseC3Word (Subgroup.center J) u m y x 40})).map
          (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype,
      ∃ n ∈ Subgroup.normalizer (e1EBar (Subgroup.center J) u m y x : Set (J ⧸ Subgroup.center J)),
        o * n = g :=
  d.exists_mul_of_mem_centralizer_forty htype
    (fun _ hg _ hr => d.conj_mem_e1RBar_sup_pPrimeCore htype hg hr) hg

theorem conj_mem_e1EBar_sup_pPrimeCore
    {g : J ⧸ Subgroup.center J}
    (hg : g ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})
    {s : J ⧸ Subgroup.center J} (hs : s ∈ e1EBar (Subgroup.center J) u m y x) :
    g * s * g⁻¹ ∈ e1EBar (Subgroup.center J) u m y x ⊔
      (CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})).map
        (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40}).subtype := by
  obtain ⟨o, ho, n, hn, rfl⟩ := d.exists_mul_mem_pPrimeCore_normalizer htype hg
  have hns : n * s * n⁻¹ ∈ e1EBar (Subgroup.center J) u m y x :=
    (Subgroup.mem_normalizer_iff.mp hn s).mp hs
  rw [show o * n * s * (o * n)⁻¹ =
    n * s * n⁻¹ * ((n * s * n⁻¹)⁻¹ * o * (n * s * n⁻¹)⁻¹⁻¹ * o⁻¹) by group]
  exact Subgroup.mul_mem_sup hns (Subgroup.mul_mem _ (conj_mem_map_subtype
    (d.e1EBar_le_centralizer_forty (Subgroup.inv_mem _ hns)) ho) (Subgroup.inv_mem _ ho))

theorem card_centralizer_forty_quotient_pPrimeCore :
    Nat.card (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})) =
        192 :=
  d.card_quotient_pPrimeCore_centralizer_forty
    (fun _ hg => d.exists_mul_mem_pPrimeCore_normalizer htype hg) htype

theorem isCharacteristicP_centralizer_forty_quotient_pPrimeCore :
    CFSG.IsCharacteristicP 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ⧸
      CFSG.pPrimeCore 2 (Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40})) :=
  d.isCharacteristicP_quotient_pPrimeCore_centralizer_forty
    (fun _ hg => d.exists_mul_mem_pPrimeCore_normalizer htype hg)

theorem card_and_isCharacteristicP_of_genuine
    {t : J ⧸ Subgroup.center J} (htt : t * t = 1)
    (ht1 : t ≠ 1) (hgen : CaseC3.Genuine (Subgroup.center J) t) :
    Nat.card (Subgroup.centralizer {t} ⧸ CFSG.pPrimeCore 2 (Subgroup.centralizer {t})) = 192 ∧
      CFSG.IsCharacteristicP 2
        (Subgroup.centralizer {t} ⧸ CFSG.pPrimeCore 2 (Subgroup.centralizer {t})) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (d.isConj_forty_of_genuine htype htt ht1 hgen)
  let e : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ≃*
      Subgroup.centralizer {t} := ((MulAut.conj c).subgroupMap _).trans
    (MulEquiv.subgroupCongr (by rw [← hc]; exact map_conj_centralizer_singleton _ _))
  let e' := QuotientGroup.congr (CFSG.pPrimeCore 2 _) (CFSG.pPrimeCore 2 _) e
    (CFSG.pPrimeCore_map_iso 2 e)
  exact ⟨(Nat.card_congr e'.toEquiv).symm.trans
    (d.card_centralizer_forty_quotient_pPrimeCore htype), isCharacteristicP_of_mulEquiv e'
      (d.isCharacteristicP_centralizer_forty_quotient_pPrimeCore htype)⟩

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

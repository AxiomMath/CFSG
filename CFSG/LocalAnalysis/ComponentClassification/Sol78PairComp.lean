module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78Residual
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Functor

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS

variable {X : Type} [Group X] [Finite X]

theorem le_pPrimeCore_of_odd {Q : Type*} [Group Q] {N : Subgroup Q} (hN : N.Normal)
    (hodd : Nat.Coprime 2 (Nat.card N)) : N ≤ pPrimeCore 2 Q :=
  le_sSup ⟨hN, hodd⟩

theorem isAltTwoComponent_oPrimeResidualOf {t u : X} {J : Subgroup X} {n : ℕ} (hn : 5 ≤ n)
    (hu : orderOf u = 2) (hJ : SolAltLit.IsAltTwoComponent t J n)
    (hJu : J ≤ centralizer ({u} : Set X))
    (hnorm : centralizer ({u} : Set X) ≤ normalizer
      ((pPrimeCoreOf 2 (centralizer ({u} : Set X)) ⊔ J : Subgroup X) : Set X)) :
    SolAltLit.IsAltTwoComponent u
      (oPrimeResidualOf 2 (pPrimeCoreOf 2 (centralizer ({u} : Set X)) ⊔ J)) n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hJt, hJc, ⟨e⟩⟩ := hJ
  set C := centralizer ({u} : Set X) with hC
  set O := pPrimeCoreOf 2 C with hO
  set Y := O ⊔ J with hY
  set J₁ := oPrimeResidualOf 2 Y with hJ₁
  have hOC : O ≤ C := map_subtype_le _
  have hYC : Y ≤ C := sup_le hOC hJu
  have hJ₁Y : J₁ ≤ Y := oPrimeResidualOf_le Y
  have hJ₁C : J₁ ≤ C := hJ₁Y.trans hYC
  have hJres : CatalogueBPrimeJoin.primeResidual 2 J = ⊤ :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ hJt).mp hJc).2.1
  have hJJ₁ : J ≤ J₁ := le_oPrimeResidualOf le_sup_right hJres
  have hCO : C ≤ normalizer (O : Set X) := le_normalizer_map_subtype (pPrimeCore 2 C)
  have hOodd : Nat.Coprime 2 (Nat.card O) := by
    rw [hO, pPrimeCoreOf, Subgroup.card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  have hJ₁n : (J₁.subgroupOf C).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hJ₁C]
    exact fun c hc => mem_normalizer_oPrimeResidualOf (hnorm hc)
  set φ : J →* J₁ ⧸ pPrimeCore 2 J₁ :=
    (QuotientGroup.mk' (pPrimeCore 2 J₁)).comp (inclusion hJJ₁) with hφ
  have hOJ₁ : (O ⊓ J₁).subgroupOf J₁ ≤ pPrimeCore 2 J₁ := by
    apply le_pPrimeCore_of_odd
    · rw [normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro c hc
      rw [mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        obtain ⟨hwO, hwJ⟩ := Subgroup.mem_inf.mp hw
        exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp (hCO (hJ₁C hc)) w).mp hwO,
          J₁.mul_mem (J₁.mul_mem hc hwJ) (J₁.inv_mem hc)⟩
      · intro hw
        obtain ⟨hwO, hwJ⟩ := Subgroup.mem_inf.mp hw
        refine Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp (hCO (hJ₁C hc)) w).mpr hwO, ?_⟩
        have : w = c⁻¹ * (c * w * c⁻¹) * c := by group
        rw [this]
        exact J₁.mul_mem (J₁.mul_mem (J₁.inv_mem hc) hwJ) hc
    · have h1 : Nat.card ((O ⊓ J₁).subgroupOf J₁) = Nat.card ↥(O ⊓ J₁) :=
        Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
      rw [h1]
      exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hOodd
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 J₁) q
    have hzY : (z : X) ∈ ((O ⊔ J : Subgroup X) : Set X) := hJ₁Y z.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left O J (hJu.trans hCO)] at hzY
    obtain ⟨o, ho, j, hj, hoj⟩ := hzY
    have hoJ₁ : o ∈ J₁ := by
      have : o = (z : X) * j⁻¹ := by rw [← hoj]; group
      rw [this]
      exact mul_mem z.2 (inv_mem (hJJ₁ hj))
    refine ⟨⟨j, hj⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    apply hOJ₁
    refine Subgroup.mem_inf.mpr ⟨?_, ((inclusion hJJ₁ ⟨j, hj⟩)⁻¹ * z).2⟩
    have h1 : (((inclusion hJJ₁ ⟨j, hj⟩)⁻¹ * z : J₁) : X) = j⁻¹ * o * j⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_inclusion]
      rw [← hoj]
      group
    change (((inclusion hJJ₁ ⟨j, hj⟩)⁻¹ * z : J₁) : X) ∈ O
    rw [h1]
    exact (mem_normalizer_iff.mp (hCO (hJu (inv_mem hj))) o).mp ho
  have hker : φ.ker = pPrimeCore 2 J := by
    apply le_antisymm
    · apply le_pPrimeCore_of_odd (MonoidHom.normal_ker φ)
      have hle : (φ.ker).map (inclusion hJJ₁) ≤ pPrimeCore 2 J₁ := by
        rintro _ ⟨k, hk, rfl⟩
        have hk' : φ k = 1 := hk
        rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hk'
        exact hk'
      have h1 := Subgroup.card_dvd_of_le hle
      rw [Subgroup.card_map_of_injective (inclusion_injective hJJ₁)] at h1
      exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
    · have hmap : (pPrimeCore 2 J).map φ ≤ pPrimeCore 2 (J₁ ⧸ pPrimeCore 2 J₁) := by
        apply le_pPrimeCore_of_odd ((pPrimeCore_normal (p := 2) (G := J)).map φ hφs)
        exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ φ) pPrimeCore_coprime_card
      rw [pPrimeCore_quotient_pPrimeCore_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff] at hmap
      exact hmap
  have e₁ : J₁ ⧸ pPrimeCore 2 J₁ ≃* alternatingGroup (Fin n) :=
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφs).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)).trans e
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hsimpA : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  have hsimp : IsSimpleGroup (J₁ ⧸ pPrimeCore 2 J₁) := e₁.isSimpleGroup
  have hnonab : ∃ a b : J₁ ⧸ pPrimeCore 2 J₁, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt_nonabelian (m := n) (by omega)
    exact ⟨e₁.symm a, e₁.symm b, fun h => hab (by simpa using congrArg e₁ h)⟩
  have hq : IsQuasisimple (J₁ ⧸ pPrimeCore 2 J₁) :=
    (LocalCores.isQuasisimple_of_isSimpleGroup hnonab).1
  refine ⟨hu, hJ₁C, ?_, ⟨e₁⟩⟩
  rw [CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J₁ C hJ₁C]
  exact ⟨hJ₁n.isSubnormal, primeResidual_oPrimeResidualOf Y, hq⟩

end CFSG.ComponentClassification.Sol78

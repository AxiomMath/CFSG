module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126U
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11Steps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L126Base
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4L46

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec126_mul_self_of_orderOf {t : G} (ht : orderOf t = 2) : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rw [ht, pow_two] at this
  exact this

theorem sec126_V_facts [Finite G] (hp : Asc82Pre11) (h120 : Asc82Lemma120)
    (h121 : Asc82Lemma121) (h124 : Asc82Lemma124) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 E : Subgroup G} (hctx : Sec12Ctx G t L S z K1 K2 E) :
    IsElemAb2 (secV t S L E) 8 ∧ secB S L ≤ secV t S L E ∧ secV t S L E ≤ E ∧
      E ≤ normalizer (secV t S L E : Set G) ∧ secV t S L E ⊔ zpowers t = E ∧
      secV t S L E ⊓ zpowers t = ⊥ ∧
      secV t S L E ⊓ centralizer ({t} : Set G) = secB S L := by
  obtain ⟨hpsp, htC, htL, htS, hSN, hsyl⟩ := hp.basic G t L S z hctx.toSec10Z
  obtain ⟨⟨hAE, -⟩, -, -, ⟨-, -, hE3⟩, -, -⟩ := h120 G t L S z K1 K2 E hctx
  obtain ⟨-, hVsup, hVinf, hEN, -, -, hNat⟩ := h121 G t L S z K1 K2 E hctx
  have ht2 : t * t = 1 := sec126_mul_self_of_orderOf hctx.involution
  have ht1 : t ≠ 1 := by
    intro h
    have := hctx.involution
    rw [h, orderOf_one] at this
    omega
  obtain ⟨φ, hBV, -⟩ := hNat
  have hVE : secV t S L E ≤ E := le_trans le_sup_left hVsup.le
  have hBt : ∀ b ∈ secB S L, b * t = t * b := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp htC) b (secB_le_L S L hb)
  have htN : t ∈ normalizer (secB S L : Set G) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    exact Subgroup.mem_centralizer_iff.mpr hBt
  refine ⟨h124 G t L S z K1 K2 E hctx, hBV, hVE, hEN, hVsup, hVinf, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.mp hv
    have hvE : v ∈ E := hVE hvV
    have hvA : v ∈ secA t S L := by
      refine (hE3 v hvE).mp ?_
      rw [Subgroup.mem_centralizer_singleton_iff] at hvC
      rw [hvC]
      group
    rcases sec126_mem_sup_zpowers htN ht2 hvA with h | ⟨b, hb, rfl⟩
    · exact h
    · exfalso
      have htV : t ∈ secV t S L E := by
        have := (secV t S L E).mul_mem ((secV t S L E).inv_mem (hBV hb)) hvV
        simpa using this
      have : t ∈ secV t S L E ⊓ zpowers t :=
        Subgroup.mem_inf.mpr ⟨htV, Subgroup.mem_zpowers t⟩
      rw [hVinf, Subgroup.mem_bot] at this
      exact ht1 this
  · intro hb
    refine Subgroup.mem_inf.mpr ⟨hBV hb, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hBt _ hb

theorem sec126_not_conj_mem [Finite G] {t : G} {V : Subgroup G}
    (hV : CFSG.Open.IsElemAbelian 2 V) (hcV : 32 < Nat.card ↥V)
    (hrank : ∀ F : Subgroup G, F ≤ centralizer ({t} : Set G) →
      CFSG.Open.IsElemAbelian 2 F → Nat.card ↥F ≤ 32) (g : G) : g⁻¹ * t * g ∉ V := by
  intro hg
  have hle : CFSG.conjugate V g⁻¹ ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : g⁻¹ * x * g * (g⁻¹ * t * g) = g⁻¹ * t * g * (g⁻¹ * x * g) := hV.comm hx hg
    have h3 : g⁻¹ * (x * t) * g = g⁻¹ * (t * x) * g := by
      calc g⁻¹ * (x * t) * g = g⁻¹ * x * g * (g⁻¹ * t * g) := by group
        _ = g⁻¹ * t * g * (g⁻¹ * x * g) := h2
        _ = g⁻¹ * (t * x) * g := by group
    exact mul_left_cancel (mul_right_cancel h3)
  have h := hrank _ hle (sec4_isElemAbelian_conjugate hV g⁻¹)
  rw [sec126_card_conjugate] at h
  omega

end CFSG.OddStandard.SmallF3.Omega

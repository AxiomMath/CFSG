module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Perm
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81A8Lift
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S7d
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Sec8
public import Certificates.Certificate2007
public import Certificates.Certificate2013
public import Certificates.Certificate2014
public import Certificates.Certificate2019
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Generic.Shapes
public import CFSG.GH74.Statements
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4d
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S3
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Statement
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5L34

public section

namespace CFSG.ComponentClassification.GSThmB.A8

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.CatFactsSmall CFSG.ComponentClassification.CatFactsSmall.A8

local notation "P8" => Equiv.Perm (Fin 8)

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H} {H₁ : h.L81Hyp}

theorem nonempty_J_equiv (H₁ : h.L81Hyp)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8))) :
    Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin 6)) := by
  rcases H₁.case8 with ⟨hJ, -, -⟩ | ⟨p, f, hp, hp2, hf, -, -, hK⟩
  · exact hJ
  · exfalso
    obtain ⟨e⟩ := hA8
    have h1 := CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hK
    rw [Nat.card_congr e.toEquiv, card_alt8] at h1
    have hq : 3 ≤ p ^ f :=
      (hp.two_le.lt_of_ne (Ne.symm hp2)).trans_le (Nat.le_self_pow (by omega) p)
    set q := p ^ f with hq'
    rcases Nat.lt_or_ge q 4 with h4 | h4
    · have hq3 : q = 3 := by omega
      rw [hq3] at h1
      norm_num at h1
    · have h2 : 4 ^ 4 * ((4 ^ 2 - 1) * (4 ^ 4 - 1)) ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
        have hq2 : 4 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h4 2
        have hq4 : 4 ^ 4 ≤ q ^ 4 := Nat.pow_le_pow_left h4 4
        exact Nat.mul_le_mul hq4 (Nat.mul_le_mul (Nat.sub_le_sub_right hq2 1)
          (Nat.sub_le_sub_right hq4 1))
      rw [← h1] at h2
      norm_num at h2

theorem card_Jbar (H₁ : h.L81Hyp)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8))) :
    Nat.card (h.J ⧸ pPrimeCore 2 h.J) = 360 := by
  obtain ⟨e⟩ := nonempty_J_equiv H₁ hA8
  rw [Nat.card_congr e.toEquiv, CatFactsSp4.card_alternatingGroup_six]

theorem exists_model (H₁ : h.L81Hyp) (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer)
    (hA8 : Nonempty (h.K ⧸ pPrimeCore 2 h.K ≃* alternatingGroup (Fin 8))) :
    ∃ M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8, M.P = QA8.originalSubgroup ∧
      M.A = QS8.originalSubgroup ∧ (M.Φ H₁.kloc.rhoA : P8) = s8 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := hA8
  obtain ⟨M, hP, hA⟩ := CatFactsSmall.A8.exists_model e
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact P_le_A
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by rw [hP, hA]; exact cent_triv
  set α := H₁.kloc.rhoA with hα
  have hs2 : (M.Φ α : P8) * (M.Φ α : P8) = 1 := by
    rw [← M.Φ_mul, hα, H₁.kloc.rhoA_mul_self, M.Φ_one]
  have hsP : (M.Φ α : P8) ∉ QA8.originalSubgroup := by
    rw [← hP, ← mem_range_conj_iff M hPA hcent]
    exact H₁.kloc.rhoA_not_mem_inner hCF1 hCF2
  have h5 : 5 ∣ Nat.card ↥(QA8.originalSubgroup ⊓ centralizer ({(M.Φ α : P8)} : Set P8)) := by
    rw [← hP, ← card_fixSubgroup M α]
    refine (show 5 ∣ 360 by norm_num).trans ?_
    rw [← card_Jbar H₁ ⟨e⟩]
    exact H₁.kloc.card_J_dvd_card_fix
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' 5 h5
  rw [Subgroup.orderOf_mk] at hxo
  have hx5 : x ∈ five8 := by
    rw [five8, List.mem_filter, mem_elemsT QA8 QA8_ok]
    refine ⟨hx.1, ?_⟩
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]
    exact ⟨hxo ▸ pow_orderOf_eq_one x, fun h1 => by rw [h1, orderOf_one] at hxo; omega⟩
  have hsA : (M.Φ α : P8) ∈ elemsT QS8 := by
    rw [mem_elemsT QS8 QS8_ok, ← hA]
    exact (M.Φ α).2
  obtain ⟨k, hk, hks⟩ := exists_conj_of_admCheck QA8_ok adm_ok hsA hs2 hsP hx5
    (mem_centralizer_singleton_iff.1 hx.2)
  have hkA : k ∈ M.A := hA ▸ admConj_mem k hk
  obtain ⟨M', hP', hA', hΦ'⟩ := exists_model_eq M α (σ₀ := s8) hkA (by rw [← hks]; group)
  exact ⟨M', hP'.trans hP, hA'.trans hA, hΦ'⟩

noncomputable abbrev psi (M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8) :
    normalizer (h.K : Set H) →* P8 :=
  M.ι.comp (Eight.oddBarAction h.K)

noncomputable abbrev rhoHat (H₁ : h.L81Hyp) (M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8) :
    ↥h.M3 →* P8 :=
  M.ι.comp H₁.kloc.rho

variable {M : AutModel (h.K ⧸ pPrimeCore 2 h.K) P8}

theorem rhoHat_eq_psi (m : ↥h.M3) :
    rhoHat H₁ M m =
      psi M ⟨m, Eight.sup_zpowers_le_normalizer H₁.kloc.a_mem_normalizer_K m.2⟩ := rfl

theorem psi_a (H₁ : h.L81Hyp) (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) :
    psi M ⟨h.a, H₁.kloc.a_mem_normalizer_K⟩ = s8 := hΦ

theorem psi_eq_one_iff (w : normalizer (h.K : Set H)) :
    psi M w = 1 ↔ (w : H) ∈ coreActionKernel h.K := by
  rw [← Eight.mem_ker_oddBarAction, MonoidHom.mem_ker]
  constructor
  · intro h1
    apply M.ι_injective
    rw [map_one]
    exact h1
  · intro h1
    show M.ι (Eight.oddBarAction h.K w) = 1
    rw [h1, map_one]

theorem psi_of_mem_K (hP : M.P = QA8.originalSubgroup) (hA : M.A = QS8.originalSubgroup) {k : H}
    (hk : k ∈ h.K) :
    psi M ⟨k, le_normalizer hk⟩ = modelEmb M ((⟨k, hk⟩ : h.K) : h.K ⧸ pPrimeCore 2 h.K) := by
  have hPA : M.P ≤ M.A := by rw [hP, hA]; exact P_le_A
  have hcent : ∀ g ∈ M.A, (∀ x ∈ M.P, g * x = x * g) → g = 1 := by
    rw [hP, hA]; exact cent_triv
  show M.ι (Eight.oddBarAction h.K ⟨(⟨k, hk⟩ : h.K), le_normalizer hk⟩) = _
  rw [Eight.oddBarAction_of_mem]
  exact Φ_conj M hPA hcent _

theorem psi_mem_A8 (hP : M.P = QA8.originalSubgroup) (hA : M.A = QS8.originalSubgroup) {k : H}
    (hk : k ∈ h.K) : psi M ⟨k, le_normalizer hk⟩ ∈ QA8.originalSubgroup := by
  rw [psi_of_mem_K hP hA hk, ← hP]
  exact modelEmb_mem M _

theorem exists_K_of_mem_A8 (hP : M.P = QA8.originalSubgroup) (hA : M.A = QS8.originalSubgroup)
    {π : P8} (hπ : π ∈ QA8.originalSubgroup) :
    ∃ k : H, ∃ hk : k ∈ h.K, psi M ⟨k, le_normalizer hk⟩ = π := by
  rw [← hP] at hπ
  obtain ⟨⟨k, hk⟩, hkπ⟩ := QuotientGroup.mk_surjective (M.e.symm ⟨π, hπ⟩)
  refine ⟨k, hk, ?_⟩
  rw [psi_of_mem_K hP hA hk, hkπ, modelEmb_symm]

theorem not_two_dvd_card_ker_rhoHat (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) :
    ¬ 2 ∣ Nat.card (rhoHat H₁ M).ker := by
  rw [MonoidHom.ker_comp_of_injective _ _ M.ι_injective]
  exact H₁.kloc.not_two_dvd_card_ker_modelHom hCF1 hCF2

theorem psi_tau {d : H₁.Data} (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) :
    psi M ⟨d.tau, le_normalizer d.tau_K⟩ =
      s8 * ((psi M ⟨d.g, le_normalizer d.g_K⟩)⁻¹ * s8 * psi M ⟨d.g, le_normalizer d.g_K⟩) := by
  have ha : (⟨h.a, H₁.kloc.a_mem_normalizer_K⟩ : normalizer (h.K : Set H)) *
      ((⟨d.g, le_normalizer d.g_K⟩ : normalizer (h.K : Set H))⁻¹ *
        ⟨h.a, H₁.kloc.a_mem_normalizer_K⟩ * ⟨d.g, le_normalizer d.g_K⟩) =
      ⟨d.tau, le_normalizer d.tau_K⟩ := Subtype.ext rfl
  rw [← ha, map_mul, map_mul, map_mul, map_inv, psi_a H₁ hΦ]

theorem psi_tau_ne_one (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {d : H₁.Data}
    (F : d.Facts) : psi M ⟨d.tau, le_normalizer d.tau_K⟩ ≠ 1 := by
  intro h3
  have hτM : d.tau ∈ h.M3 := d.tau_mem.2
  have hτ2 : (⟨d.tau, hτM⟩ : ↥h.M3) * ⟨d.tau, hτM⟩ = 1 := Subtype.ext d.tau_sq
  have h4 := Eight.injOn_of_isPGroup (not_two_dvd_card_ker_rhoHat (H₁ := H₁) (M := M) hCF1 hCF2)
    (isPGroup_zpowers_of_mul_self hτ2) (mem_zpowers _) (one_mem _)
    (show rhoHat H₁ M ⟨d.tau, hτM⟩ = rhoHat H₁ M 1 by rw [map_one, rhoHat_eq_psi]; exact h3)
  apply d.tau_not_mem_P hCF1 hCF2 F
  rw [show d.tau = 1 from congrArg Subtype.val h4]
  exact one_mem _

theorem psi_tau_mem (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {d : H₁.Data}
    (F : d.Facts) (hP : M.P = QA8.originalSubgroup) (hA : M.A = QS8.originalSubgroup)
    (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) :
    psi M ⟨d.tau, le_normalizer d.tau_K⟩ ∈ t15 := by
  have hγ := psi_mem_A8 hP hA d.g_K
  have h1 := psi_tau (d := d) hΦ
  have h2 : psi M ⟨d.tau, le_normalizer d.tau_K⟩ * psi M ⟨d.tau, le_normalizer d.tau_K⟩ = 1 := by
    rw [← map_mul, show (⟨d.tau, le_normalizer d.tau_K⟩ : normalizer (h.K : Set H)) *
      ⟨d.tau, le_normalizer d.tau_K⟩ = 1 from Subtype.ext d.tau_sq, map_one]
  have hne := psi_tau_ne_one (M := M) hCF1 hCF2 F
  rw [h1] at h2 hne ⊢
  exact mem_t15_of_conj hγ h2 hne

theorem card_D (hCF1 : CFSec8Simple) (hCF2 : CFSec8InnerCentralizer) {d : H₁.Data}
    (F : d.Facts) (hA : M.A = QS8.originalSubgroup) (hΦ : (M.Φ H₁.kloc.rhoA : P8) = s8) :
    Nat.card h.D = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker := not_two_dvd_card_ker_rhoHat (H₁ := H₁) (M := M) hCF1 hCF2
  set Q1 : Subgroup ↥h.M3 := (h.Q ⊓ h.M3).subgroupOf h.M3 with hQ1
  have hQ12 : IsPGroup 2 Q1 :=
    (h.toHyp52.sec8_isPGroup_Q.to_le inf_le_left : IsPGroup 2 ↥(h.Q ⊓ h.M3)).comap_subtype
  have hcQ : Nat.card (Q1.map (rhoHat H₁ M)) = 4 * Nat.card h.D := by
    rw [Eight.card_map_of_isPGroup hker hQ12, hQ1, Six.card_subgroupOf_eq,
      inf_eq_left.mpr inf_le_right, F.card_Q1]
  have hle : Q1.map (rhoHat H₁ M) ≤ QS8.originalSubgroup ⊓ centralizer ({s8} : Set P8) := by
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨hA ▸ M.ι_mem _, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hΦ]
    show M.ι (H₁.kloc.rho q) * M.ι H₁.kloc.rhoA = M.ι H₁.kloc.rhoA * M.ι (H₁.kloc.rho q)
    rw [← map_mul, ← map_mul, ← H₁.kloc.rho_aM, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (h.toHyp52.comm_a (mem_inf.mp hq).1.1)
  obtain ⟨n, hn⟩ := (hQ12.map (rhoHat H₁ M)).exists_card_eq
  have hdvd := card_dvd_of_le hle
  rw [card_CA0, hn] at hdvd
  have h32 : 2 ^ n ∣ 2 ^ 5 :=
    (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 45)).dvd_of_dvd_mul_right hdvd
  have h3 := Nat.le_of_dvd (by norm_num) h32
  have h4 := F.eight_le
  omega

end CFSG.ComponentClassification.GSThmB.A8

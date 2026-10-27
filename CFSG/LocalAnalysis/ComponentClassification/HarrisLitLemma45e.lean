module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45b

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

theorem le_pPrimeCore_of_isSolvable {K : Type*} [Group K] [Finite K]
    (hsimp : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hnonab : ∃ a b : K ⧸ pPrimeCore 2 K, a * b ≠ b * a)
    {N : Subgroup K} (hN : N.Normal) (hNs : Group.IsSolvable ↥N) : N ≤ pPrimeCore 2 K := by
  have hπs : Function.Surjective (QuotientGroup.mk' (pPrimeCore 2 K)) :=
    QuotientGroup.mk'_surjective _
  rcases (hN.map _ hπs).eq_bot_or_eq_top with hbot | htop
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  · exfalso
    have hsurj : Function.Surjective ((QuotientGroup.mk' (pPrimeCore 2 K)).comp N.subtype) := by
      intro y
      have hy : y ∈ N.map (QuotientGroup.mk' (pPrimeCore 2 K)) := by rw [htop]; exact mem_top y
      obtain ⟨n, hn, rfl⟩ := hy
      exact ⟨⟨n, hn⟩, rfl⟩
    have hsolv : Group.IsSolvable (K ⧸ pPrimeCore 2 K) := Group.isSolvable_of_surjective hsurj
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem mem_of_mem_ker_inf (hσ : Setup42 h hS w z) (i j : ℕ) {s : X}
    (hsM : s ∈ centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
    (hsC : s ∈ coreActionKernel L) :
    s ∈ ((centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ⊓
      (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype) ⊔
        closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j} := by
  have hmem : s ∈ centralizer ({t} : Set X) ⊓ coreActionKernel L := ⟨hsM.1, hsC⟩
  rw [h.dihedral.kernel_eq] at hmem
  have hOn : (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
      ≤ normalizer (zpowers t : Set X) := by
    rintro _ ⟨o, -, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j', rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute (o : X) t := mem_centralizer_singleton_iff.mp o.2
    exact (hc.zpow_right j').eq.symm
  have hmem' : s ∈ ((pPrimeCore 2 ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype : Set X) * (zpowers t : Set X) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hOn]
    exact hmem
  obtain ⟨_, ⟨o, ho, rfl⟩, y, hy, hsy⟩ := hmem'
  simp only at hsy
  have htM : t ∈ centralizer ({t} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} :=
    ⟨mem_centralizer_singleton_iff.mpr rfl, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hσ.beta_mem_H i j)).symm⟩
  have hyM : y ∈ centralizer ({t} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} :=
    (zpowers_le.mpr htM) hy
  have hoM : (o : X) ∈ centralizer ({t} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} := by
    have : (o : X) = s * y⁻¹ := by rw [← hsy, Subgroup.coe_subtype]; group
    rw [this]
    exact mul_mem hsM (inv_mem hyM)
  rw [← hsy]
  refine mul_mem (mem_sup_left ⟨hoM, ⟨o, ho, rfl⟩⟩) (mem_sup_right ?_)
  exact (zpowers_le.mpr (subset_closure (by simp))) hy

theorem solvableRadical_M (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (solvableRadical ↥(centralizer ({t} : Set X) ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).subtype =
      ((centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ⊓
        (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype) ⊔
        closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j} := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({t} : Set X) ⊓ centralizer {β} with hM
  set K := centralizerResidual L β with hK
  set OH := (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
    with hOH
  have hβM : β ∈ M := ⟨hσ.beta_mem_H i j, mem_centralizer_singleton_iff.mpr rfl⟩
  have htM : t ∈ M := ⟨mem_centralizer_singleton_iff.mpr rfl,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hσ.beta_mem_H i j)).symm⟩
  have hSn : ∀ a ∈ M, ∀ x ∈ (solvableRadical ↥M).map M.subtype,
      a * x * a⁻¹ ∈ (solvableRadical ↥M).map M.subtype := by
    rintro a ha _ ⟨y, hy, rfl⟩
    exact ⟨⟨a, ha⟩ * y * ⟨a, ha⟩⁻¹,
      (solvableRadical_normal (H := ↥M)).conj_mem y hy _, rfl⟩
  apply le_antisymm
  · intro s hs
    have hsM : s ∈ M := map_subtype_le _ hs
    have hL := hσ.lieModel_bar_K hFC hKC i j
    have hsimp := isSimpleGroup_of_lieModel_psl2 hL
    have hnonab := nonabelian_of_lieModel_psl2 hL
    have hSK : (solvableRadical ↥M).map M.subtype ⊓ K ≤ (pPrimeCore 2 ↥K).map K.subtype := by
      have hNn : (((solvableRadical ↥M).map M.subtype ⊓ K).subgroupOf K).Normal := by
        refine ⟨fun n hn k => ⟨hSn k (h.K_le_M β k.2) n hn.1, ?_⟩⟩
        exact K.mul_mem (K.mul_mem k.2 hn.2) (K.inv_mem k.2)
      have hQs : Group.IsSolvable ↥((solvableRadical ↥M).map M.subtype) := by
        have : Group.IsSolvable ↥(solvableRadical ↥M) := solvableRadical_isSolvable
        exact Group.isSolvable_of_surjective
          (f := (equivMapOfInjective _ M.subtype M.subtype_injective).toMonoidHom)
          (MulEquiv.surjective _)
      have hNs : Group.IsSolvable ↥(((solvableRadical ↥M).map M.subtype ⊓ K).subgroupOf K) := by
        have h1 : Group.IsSolvable ↥((solvableRadical ↥M).map M.subtype ⊓ K) :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)
        exact Group.isSolvable_of_surjective
          (f := (subgroupOfEquivOfLe (inf_le_right : (solvableRadical ↥M).map M.subtype ⊓ K ≤
            K)).symm.toMonoidHom) (MulEquiv.surjective _)
      have hle := le_pPrimeCore_of_isSolvable hsimp hnonab hNn hNs
      intro x hx
      exact ⟨⟨x, hx.2⟩, hle hx, rfl⟩
    have hfix : ∀ k ∈ K, k⁻¹ * (s * k * s⁻¹) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
      intro k hk
      have hkM : k ∈ M := h.K_le_M β hk
      have hc1 : k⁻¹ * (s * k * s⁻¹) ∈ K :=
        K.mul_mem (K.inv_mem hk) ((mem_normalizer_iff.mp (h.M_le_normalizer_K β hsM) k).mp hk)
      have hc2 : k⁻¹ * (s * k * s⁻¹) ∈ (solvableRadical ↥M).map M.subtype := by
        rw [show k⁻¹ * (s * k * s⁻¹) = (k⁻¹ * s * k⁻¹⁻¹) * s⁻¹ by group]
        exact mul_mem (hSn _ (inv_mem hkM) _ hs) (inv_mem hs)
      have := hSK ⟨hc2, hc1⟩
      rw [hK, hσ.oddCore_K hFC hKC i j] at this
      exact this.2
    rcases hσ.rho_eq_one_or_eq hFC hKC i j hsM.1 hfix with h1 | h1
    · exact hσ.mem_of_mem_ker_inf i j hsM ((h.mem_ker_rho _).mp h1)
    · have hbs : β⁻¹ * s ∈ M := mul_mem (inv_mem hβM) hsM
      have h2 : h.rho ⟨β⁻¹ * s, hbs.1⟩ = 1 := by
        show h.rho (⟨β, hσ.beta_mem_H i j⟩⁻¹ * ⟨s, hsM.1⟩) = 1
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 := hσ.mem_of_mem_ker_inf i j hbs ((h.mem_ker_rho _).mp h2)
      rw [show s = β * (β⁻¹ * s) by group]
      exact mul_mem (mem_sup_right (subset_closure (by simp))) h3
  ·
    have hAM : M ⊓ OH ≤ M := inf_le_left
    have hBM : closure {t, β} ≤ M := by
      rw [closure_le]
      rintro x (rfl | rfl)
      · exact htM
      · exact hβM
    have hA : ((M ⊓ OH).subgroupOf M).Normal := ⟨fun n hn a => ⟨M.mul_mem (M.mul_mem a.2 hn.1)
      (M.inv_mem a.2), conj_mem_map_pPrimeCore_self a.2.1 hn.2⟩⟩
    have hcomm : ∀ a ∈ M, ∀ b ∈ closure ({t, β} : Set X), a * b = b * a := by
      intro a ha b hb
      have : closure ({t, β} : Set X) ≤ centralizer ({a} : Set X) := by
        rw [closure_le]
        rintro x (rfl | rfl)
        · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha.1).symm
        · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha.2).symm
      exact (mem_centralizer_singleton_iff.mp (this hb)).symm
    have hB : ((closure {t, β}).subgroupOf M).Normal := ⟨fun n hn a => by
      show (a : X) * n * (a : X)⁻¹ ∈ closure {t, β}
      rw [hcomm a a.2 n hn, mul_inv_cancel_right]
      exact hn⟩
    have hAs : Group.IsSolvable ↥((M ⊓ OH).subgroupOf M) := by
      apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
      rw [Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv]
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right)
        (coprime_card_map_pPrimeCore _))
    have hBs : Group.IsSolvable ↥((closure {t, β}).subgroupOf M) := by
      have hUX : closure ({t, β} : Set X) ≤ closure {t, w ^ (orderOf w / 2), z} := by
        rw [closure_le]
        rintro x (rfl | rfl)
        · exact subset_closure (by simp)
        · exact beta_mem_X i j
      apply Group.isSolvable_of_comm
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      have haX := hUX (show ((a : ↥M) : X) ∈ closure {t, β} from a.2)
      have hbX := hUX (show ((b : ↥M) : X) ∈ closure {t, β} from b.2)
      exact (mem_centralizer_iff.mp (hσ.X_le_center_T haX).2 _ (hσ.X_le_T hbX)).symm
    have hle : ((M ⊓ OH) ⊔ closure {t, β}).subgroupOf M ≤ solvableRadical ↥M := by
      rw [subgroupOf_sup hAM hBM]
      exact le_sSup ⟨Subgroup.sup_normal _ _, isSolvable_sup_of_normal _ _⟩
    intro x hx
    exact ⟨⟨x, sup_le hAM hBM hx⟩, hle hx, rfl⟩

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit

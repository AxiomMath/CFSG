module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma45a
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFacts411
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem le_map_pPrimeCore {N A : Subgroup X} (hNA : N ≤ A)
    (hN : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (hodd : Nat.Coprime 2 (Nat.card N)) :
    N ≤ (pPrimeCore 2 ↥A).map A.subtype := by
  have hnorm : (N.subgroupOf A).Normal := ⟨fun n hn a => hN a a.2 n hn⟩
  have hcard : Nat.card (N.subgroupOf A) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv
  have hle : N.subgroupOf A ≤ pPrimeCore 2 ↥A := le_sSup ⟨hnorm, hcard ▸ hodd⟩
  intro x hx
  exact ⟨⟨x, hNA hx⟩, hle hx, rfl⟩

omit [Finite X] in
theorem conj_mem_map_pPrimeCore_self {A : Subgroup X} {a x : X} (ha : a ∈ A)
    (hx : x ∈ (pPrimeCore 2 ↥A).map A.subtype) : a * x * a⁻¹ ∈ (pPrimeCore 2 ↥A).map A.subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨a, ha⟩ * y * ⟨a, ha⟩⁻¹, (pPrimeCore_normal (p := 2) (G := ↥A)).conj_mem y hy _, rfl⟩

theorem coprime_card_map_pPrimeCore (A : Subgroup X) :
    Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥A).map A.subtype)) := by
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact pPrimeCore_coprime_card

omit [Finite X] in
theorem centralizer_le_coreActionKernel (K : Subgroup X) :
    centralizer (K : Set X) ≤ coreActionKernel K := by
  intro g hg
  rw [mem_coreActionKernel]
  refine ⟨Subgroup.centralizer_le_normalizer _ hg, fun j hj => ?_⟩
  have hjg : j * g = g * j := mem_centralizer_iff.mp hg j hj
  rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) by group, hjg, show
    j⁻¹ * g⁻¹ * (g * j) = 1 by group]
  exact one_mem _

variable {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

theorem oddCore_L_eq (h : Standing t L p f) :
    (pPrimeCore 2 ↥L).map L.subtype =
      L ⊓ (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype := by
  have hLH : L ≤ centralizer ({t} : Set X) := h.config.le_centralizer
  apply le_antisymm
  · refine le_inf (map_subtype_le _) (le_map_pPrimeCore ((map_subtype_le _).trans hLH)
      (fun a ha n hn => ?_) (coprime_card_map_pPrimeCore L))
    exact (mem_normalizer_iff.mp (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L
      (pPrimeCore 2 ↥L) (h.centralizer_le_normalizer ha)) n).mp hn
  · refine le_map_pPrimeCore inf_le_left (fun a ha n hn => ⟨L.mul_mem (L.mul_mem ha hn.1)
      (L.inv_mem ha), conj_mem_map_pPrimeCore_self (hLH ha) hn.2⟩) ?_
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      (coprime_card_map_pPrimeCore _)

omit [Finite X] in
theorem K_le_M (h : Standing t L p f) (β : X) :
    centralizerResidual L β ≤ centralizer ({t} : Set X) ⊓ centralizer {β} :=
  centralizerResidual_le.trans (inf_le_inf_right _ h.config.le_centralizer)

theorem perfectResidual_M (h : Standing t L p f) (β : X) :
    (perfectResidual ↥(centralizer ({t} : Set X) ⊓ centralizer {β})).map
      (centralizer ({t} : Set X) ⊓ centralizer {β}).subtype = centralizerResidual L β := by
  apply le_antisymm
  · have h1 := perfectResidual_map_mono
      (inf_le_left : centralizer ({t} : Set X) ⊓ centralizer {β} ≤ centralizer ({t} : Set X))
    rw [h.dihedral.residual] at h1
    exact le_perfectResidual_map (le_inf h1 ((map_subtype_le _).trans inf_le_right))
      (isPerfect_perfectResidual_map _)
  · exact le_perfectResidual_map (h.K_le_M β) (isPerfect_perfectResidual_map _)

theorem M_le_normalizer_K (h : Standing t L p f) (β : X) :
    centralizer ({t} : Set X) ⊓ centralizer {β} ≤
      normalizer (centralizerResidual L β : Set X) := by
  rw [← h.perfectResidual_M β]
  exact le_normalizer_perfectResidual_map _

omit [Finite X] in
theorem closure_le_centralizer_K (h : Standing t L p f) (β : X) :
    closure {t, β} ≤ centralizer (centralizerResidual L β : Set X) := by
  rw [closure_le]
  rintro g (rfl | rfl) <;> refine mem_centralizer_iff.mpr fun k hk => ?_
  · exact mem_centralizer_singleton_iff.mp (h.K_le_M _ hk).1
  · exact mem_centralizer_singleton_iff.mp (h.K_le_M _ hk).2

end Standing

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem rho_eq_one_or_eq (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) {y : X} (hyH : y ∈ centralizer ({t} : Set X))
    (hy : ∀ k ∈ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j),
      k⁻¹ * (y * k * y⁻¹) ∈ (pPrimeCore 2 ↥L).map L.subtype) :
    h.rho ⟨y, hyH⟩ = 1 ∨ h.rho ⟨y, hyH⟩ = h.rho ⟨_, hσ.beta_mem_H i j⟩ := by
  refine (hσ.fieldCentralizer hFC hKC i j).2.2.2 _ fun x hx => ?_
  rw [← range_barMap_perfectResidual (hσ.beta_mem_normalizer i j)
    (hσ.isPGroup_zpowers_beta i j)] at hx
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨n, hn, hnk⟩ := hy k k.2
  rw [barMap_apply, h.rho_apply, barAction_mk, QuotientGroup.eq]
  have hn' : (normalizerConj L ⟨y, h.centralizer_le_normalizer hyH⟩ (inclusion
      (perfectResidual_le (inf_le_left : L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}
        ≤ L)) k))⁻¹ * inclusion (perfectResidual_le (inf_le_left :
          L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} ≤ L)) k = n⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply, coe_inclusion]
    rw [show (n : X) = _ from hnk]
    group
  rw [hn']
  exact inv_mem hn

theorem oddCore_M (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).subtype =
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ⊓
        (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({t} : Set X) ⊓ centralizer {β} with hM
  set K := centralizerResidual L β with hK
  apply le_antisymm
  · intro o ho
    have hoM : o ∈ M := map_subtype_le _ ho
    refine ⟨hoM, ?_⟩
    have hfix : ∀ k ∈ K, k⁻¹ * (o * k * o⁻¹) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
      intro k hk
      have hkM : k ∈ M := h.K_le_M β hk
      have hc1 : k⁻¹ * (o * k * o⁻¹) ∈ K :=
        K.mul_mem (K.inv_mem hk) ((mem_normalizer_iff.mp (h.M_le_normalizer_K β hoM) k).mp hk)
      have hc2 : k⁻¹ * (o * k * o⁻¹) ∈ (pPrimeCore 2 ↥M).map M.subtype := by
        rw [show k⁻¹ * (o * k * o⁻¹) = (k⁻¹ * o * k⁻¹⁻¹) * o⁻¹ by group]
        exact mul_mem (conj_mem_map_pPrimeCore_self (inv_mem hkM) ho) (inv_mem ho)
      have hc3 : (pPrimeCore 2 ↥M).map M.subtype ⊓ K ≤ (pPrimeCore 2 ↥K).map K.subtype :=
        le_map_pPrimeCore inf_le_right (fun a ha n hn =>
          ⟨conj_mem_map_pPrimeCore_self (h.K_le_M β ha) hn.1,
            K.mul_mem (K.mul_mem ha hn.2) (K.inv_mem ha)⟩)
          (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_left)
            (coprime_card_map_pPrimeCore _))
      have := hc3 ⟨hc2, hc1⟩
      rw [hK, hσ.oddCore_K hFC hKC i j] at this
      exact this.2
    have hoH : o ∈ centralizer ({t} : Set X) := hoM.1
    have hodd : Odd (orderOf o) := by
      obtain ⟨o', ho', rfl⟩ := ho
      have hdvd : orderOf o' ∣ Nat.card (pPrimeCore 2 ↥M) := by
        rw [← Subgroup.orderOf_mk o' ho']
        exact orderOf_dvd_natCard _
      rw [Subgroup.coe_subtype, Subgroup.orderOf_coe]
      rcases Nat.even_or_odd (orderOf o') with he | ho''
      · exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right hdvd
          pPrimeCore_coprime_card) (even_iff_two_dvd.mp he)) (by norm_num)
      · exact ho''
    rcases hσ.rho_eq_one_or_eq hFC hKC i j hoH hfix with h1 | h1
    · exact h.mem_oddCore_of_mem_ker hoH ((h.mem_ker_rho _).mp h1) hodd
    · exfalso
      apply hσ.rho_beta_ne_one i j
      have hn : h.rho ⟨o, hoH⟩ ^ orderOf o = 1 := by
        rw [← map_pow, show (⟨o, hoH⟩ : ↥(centralizer ({t} : Set X))) ^ orderOf o = 1 from
          Subtype.ext (by rw [Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]), map_one]
      have h2 : h.rho ⟨_, hσ.beta_mem_H i j⟩ ^ 2 = 1 := by
        rw [← map_pow, show (⟨_, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 from
          Subtype.ext (by rw [Subgroup.coe_pow, hσ.sq_eq_one_of_mem_X (beta_mem_X i j),
            Subgroup.coe_one]), map_one]
      rw [h1] at hn
      obtain ⟨m, hm⟩ := hodd
      rwa [hm, pow_succ, pow_mul, h2, one_pow, one_mul] at hn
  · exact le_map_pPrimeCore inf_le_left (fun a ha n hn => ⟨M.mul_mem (M.mul_mem ha hn.1)
      (M.inv_mem ha), conj_mem_map_pPrimeCore_self ha.1 hn.2⟩)
      (Nat.Coprime.coprime_dvd_right (card_dvd_of_le inf_le_right) (coprime_card_map_pPrimeCore _))

theorem oddCore_K_H (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (pPrimeCore 2 ↥(centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))).map
        (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subtype =
      centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊓
        (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype := by
  rw [hσ.oddCore_K hFC hKC i j, h.oddCore_L_eq, ← inf_assoc,
    inf_eq_left.mpr (centralizerResidual_le_left (g := w ^ (orderOf w / 2) * t ^ i * z ^ j))]

theorem isSylowOf_T_M (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsSylowOf 2 (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w)
      (centralizer ({t} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) :=
  hσ.isSylowOf_centralizer hKC i j

theorem card_closure_t_beta (hσ : Setup42 h hS w z) (i j : ℕ) :
    Nat.card (closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j} : Subgroup X) = 4 := by
  classical
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hβ2 : β ^ 2 = 1 := hσ.sq_eq_one_of_mem_X (beta_mem_X i j)
  have htβ : t * β = β * t := (mem_centralizer_singleton_iff.mp (hσ.beta_mem_H i j)).symm
  have ht1 : t ≠ 1 := fun h1 => by
    have := h.config.orderOf_eq
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  have hβ1 : β ≠ 1 := fun h1 => hσ.rho_beta_ne_one i j (by
    rw [show (⟨β, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) = 1 from Subtype.ext h1,
      map_one])
  have hβt : β ≠ t := fun h1 => hσ.rho_beta_ne_one i j (by
    rw [show (⟨β, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) =
      ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ from Subtype.ext h1, h.rho_t])
  have hU : ((closure {t, β} : Subgroup X) : Set X) = ({1, t, β, t * β} : Finset X) := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · intro hx
      exact mem_closure_pair ht2 hβ2 htβ hx
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_mem _
      · exact subset_closure (by simp)
      · exact subset_closure (by simp)
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  have hcard : Nat.card (closure {t, β} : Subgroup X) =
      Nat.card (((({1, t, β, t * β} : Finset X) : Set X))) := by
    rw [← hU]
    rfl
  rw [hcard, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  have h1 : t * β ≠ 1 := fun h' => hβt (by
    rw [eq_inv_of_mul_eq_one_right h', inv_eq_of_mul_eq_one_right (by rw [← sq, ht2])])
  have h2 : t * β ≠ t := fun h' => hβ1 (by simpa using h')
  have h3 : t * β ≠ β := fun h' => ht1 (by simpa using h')
  rw [Finset.card_insert_of_notMem (by simp [ht1.symm, hβ1.symm, h1.symm]),
    Finset.card_insert_of_notMem (by simp [hβt.symm, h2.symm]),
    Finset.card_insert_of_notMem (by simp [h3.symm]), Finset.card_singleton]

theorem isSylowOf_tβ (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsSylowOf 2 (closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (centralizer ({t} : Set X) ⊓
        coreActionKernel (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set K := centralizerResidual L β with hK
  have hβH := hσ.beta_mem_H i j
  have hUX : closure {t, β} ≤ closure {t, w ^ (orderOf w / 2), z} := by
    rw [closure_le]
    rintro g (rfl | rfl)
    · exact subset_closure (by simp)
    · exact beta_mem_X i j
  have hle : closure {t, β} ≤ centralizer ({t} : Set X) ⊓ coreActionKernel K := by
    refine le_inf ?_ ((h.closure_le_centralizer_K β).trans
      (centralizer_le_coreActionKernel K))
    rw [closure_le]
    rintro g (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr rfl
    · exact hβH
  have hU2 : IsPGroup 2 (closure {t, β}) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hσ.sq_eq_one_of_mem_X (hUX x.2),
      Subgroup.coe_one])⟩
  refine isSylowOf_of_card_le hle hU2 fun Q hQ hQ2 hUQ => card_le_of_le fun q hq => ?_
  obtain ⟨hqH, hqK⟩ := hQ hq
  have hfix : ∀ k ∈ K, k⁻¹ * (q * k * q⁻¹) ∈ (pPrimeCore 2 ↥L).map L.subtype := by
    intro k hk
    have := (mem_coreActionKernel.mp (inv_mem hqK)).2 k hk
    rw [inv_inv, hσ.oddCore_K hFC hKC i j] at this
    rw [show k⁻¹ * (q * k * q⁻¹) = k⁻¹ * q * k * q⁻¹ by group]
    exact this.2
  have htU : zpowers t ≤ closure {t, β} := zpowers_le.mpr (subset_closure (by simp))
  obtain ⟨k₂, hk₂⟩ := hQ2 ⟨q, hq⟩
  have hq2 : q ^ 2 ^ k₂ = 1 := by simpa using congrArg Subtype.val hk₂
  rcases hσ.rho_eq_one_or_eq hFC hKC i j hqH hfix with h1 | h1
  · exact htU (h.mem_zpowers_of_mem_ker hqH ((h.mem_ker_rho _).mp h1) hq2)
  · have hβQ : β ∈ Q := hUQ (subset_closure (by simp))
    have hbq : β⁻¹ * q ∈ Q := Q.mul_mem (Q.inv_mem hβQ) hq
    have hbqH : β⁻¹ * q ∈ centralizer ({t} : Set X) := (hQ hbq).1
    have hρ : h.rho ⟨β⁻¹ * q, hbqH⟩ = 1 := by
      rw [show (⟨β⁻¹ * q, hbqH⟩ : ↥(centralizer ({t} : Set X))) = ⟨β, hβH⟩⁻¹ * ⟨q, hqH⟩ from rfl,
        map_mul, map_inv, h1, inv_mul_cancel]
    obtain ⟨k₃, hk₃⟩ := hQ2 ⟨_, hbq⟩
    have hbq2 : (β⁻¹ * q) ^ 2 ^ k₃ = 1 := by simpa using congrArg Subtype.val hk₃
    have hmem := htU (h.mem_zpowers_of_mem_ker hbqH ((h.mem_ker_rho _).mp hρ) hbq2)
    have := (closure {t, β}).mul_mem (subset_closure (by simp) : β ∈ closure {t, β}) hmem
    rwa [mul_inv_cancel_left] at this

theorem dihedral_or_semidihedral (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) (i j : ℕ) {R : Subgroup X}
    (hR : IsSylowOf 2 R
      (coreActionKernel (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))))
    (hUR : closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j} ≤ R) :
    R = closure {t, w ^ (orderOf w / 2) * t ^ i * z ^ j} ∨
      (∃ k : ℕ, 2 ≤ k ∧ Nonempty (↥R ≃* DihedralGroup (2 ^ k))) ∨
      ∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup n) := by
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  by_cases hRU : R = closure {t, β}
  · exact Or.inl hRU
  right
  have hsyl := hσ.isSylowOf_tβ hFC hKC i j
  have ht2 : t ^ 2 = 1 := by rw [← h.config.orderOf_eq, pow_orderOf_eq_one]
  have hβ2 : β ^ 2 = 1 := hσ.sq_eq_one_of_mem_X (beta_mem_X i j)
  have htβ : t * β = β * t := (mem_centralizer_singleton_iff.mp (hσ.beta_mem_H i j)).symm
  have hUab : closure {t, β} ≤ centralizer (closure {t, β} : Set X) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    rcases mem_closure_pair ht2 hβ2 htβ hx with rfl | rfl | rfl | rfl <;>
      rcases mem_closure_pair ht2 hβ2 htβ hy with rfl | rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, htβ, mul_assoc] <;> simp only [← mul_assoc, htβ]
  have hC : R ⊓ centralizer (closure {t, β} : Set X) ≤ closure {t, β} := by
    have hQ : R ⊓ centralizer (closure {t, β} : Set X) ≤
        centralizer ({t} : Set X) ⊓ coreActionKernel (centralizerResidual L β) :=
      fun x hx => ⟨mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp hx.2 t (subset_closure (by simp))).symm, hR.le hx.1⟩
    rw [hsyl.eq_of_le (le_inf hUR hUab) hQ (hR.isPGroup.to_le inf_le_left)]
  exact QuasithinUnique.suzuki_selfCentralizing_four hR.isPGroup hUR
    (hσ.card_closure_t_beta i j)
    (fun u hu => hσ.sq_eq_one_of_mem_X ((closure_le _).mpr (by
      rintro g (rfl | rfl)
      · exact subset_closure (by simp)
      · exact beta_mem_X i j) hu)) hC (fun h' => hRU h'.symm)

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit

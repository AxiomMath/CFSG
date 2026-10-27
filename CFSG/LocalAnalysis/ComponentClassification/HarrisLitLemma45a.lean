module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma410
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLiftField

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

theorem mem_oddCore_of_mem_ker (h : Standing t L p f) {s : X}
    (hsH : s ∈ centralizer ({t} : Set X)) (hsC : s ∈ coreActionKernel L) (hs : Odd (orderOf s)) :
    s ∈ (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype := by
  have hmem : s ∈ centralizer ({t} : Set X) ⊓ coreActionKernel L := ⟨hsH, hsC⟩
  rw [h.dihedral.kernel_eq] at hmem
  have hOn : (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype
      ≤ normalizer (zpowers t : Set X) := by
    rintro _ ⟨o, -, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    have hc : Commute (o : X) t := mem_centralizer_singleton_iff.mp o.2
    exact (hc.zpow_right j).eq.symm
  have hmem' : s ∈ ((pPrimeCore 2 ↥(centralizer ({t} : Set X))).map
      (centralizer ({t} : Set X)).subtype : Set X) * (zpowers t : Set X) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hOn]
    exact hmem
  obtain ⟨_, ⟨o, ho, rfl⟩, y, hy, rfl⟩ := hmem'
  simp only at hs ⊢
  rcases eq_one_or_eq_of_mem_zpowers h.config.orderOf_eq hy with hy1 | hy1
  · rw [hy1, mul_one]
    exact ⟨o, ho, rfl⟩
  · exfalso
    rw [hy1, Subgroup.coe_subtype] at hs
    have hc : Commute (o : X) t := mem_centralizer_singleton_iff.mp o.2
    have hdvd : orderOf (o : X) ∣ Nat.card (pPrimeCore 2 ↥(centralizer ({t} : Set X))) := by
      rw [Subgroup.orderOf_coe, ← Subgroup.orderOf_mk o ho]
      exact orderOf_dvd_natCard _
    have hcop : Nat.Coprime (orderOf (o : X)) (orderOf t) := by
      rw [h.config.orderOf_eq]
      exact Nat.Coprime.symm (Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card)
    rw [hc.orderOf_mul_eq_mul_orderOf_of_coprime hcop, h.config.orderOf_eq] at hs
    exact Nat.not_even_iff_odd.mpr hs (Nat.even_mul.mpr (Or.inr even_two))

end Standing

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

omit [Finite X] in
theorem beta_mem_X (i j : ℕ) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ closure {t, w ^ (orderOf w / 2), z} :=
  mul_mem (mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) i))
    (pow_mem (subset_closure (by simp)) j)

theorem beta_mem_S (hσ : Setup42 h hS w z) (i j : ℕ) : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ S :=
  S.mul_mem (S.mul_mem hσ.u_mem (S.pow_mem (h.t_mem hS) i)) (S.pow_mem hσ.z_mem.1 j)

theorem beta_mem_H (hσ : Setup42 h hS w z) (i j : ℕ) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ centralizer ({t} : Set X) :=
  hS.le (hσ.beta_mem_S i j)

theorem beta_mem_normalizer (hσ : Setup42 h hS w z) (i j : ℕ) :
    w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ normalizer (L : Set X) :=
  h.centralizer_le_normalizer (hσ.beta_mem_H i j)

theorem isPGroup_zpowers_beta (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsPGroup 2 (zpowers (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have h2 := hσ.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hd : orderOf (w ^ (orderOf w / 2) * t ^ i * z ^ j) ∣ 2 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one h2
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

omit [Finite X] in
theorem D_le_centralizer_beta (hσ : Setup42 h hS w z) (i j : ℕ) :
    S ⊓ L ≤ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} := by
  intro d hd
  rw [mem_centralizer_singleton_iff]
  have hu : Commute d (w ^ (orderOf w / 2)) := hσ.lift.comm_D d hd
  have ht : Commute d t := mem_centralizer_singleton_iff.mp (h.config.le_centralizer hd.2)
  have hz : Commute d z := hσ.z_comm_D hd
  exact ((hu.mul_right (ht.pow_right i)).mul_right (hz.pow_right j)).eq

theorem rho_beta_not_mem_inn (hσ : Setup42 h hS w z) (i j : ℕ) :
    h.rho ⟨_, hσ.beta_mem_H i j⟩ ∉ innAut (Bar L) := by
  intro hinn
  have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have hzH : z ∈ centralizer ({t} : Set X) := hS.le hσ.z_mem.1
  have hzInn : h.rho ⟨z, hzH⟩ ∈ innAut (Bar L) :=
    ⟨QuotientGroup.mk ⟨z, hσ.z_mem.2⟩, (h.rho_of_mem ⟨z, hσ.z_mem.2⟩).symm⟩
  have hβ : (⟨_, hσ.beta_mem_H i j⟩ : ↥(centralizer ({t} : Set X))) =
      ⟨w ^ (orderOf w / 2), hS.le hσ.u_mem⟩ * ⟨t, htH⟩ ^ i * ⟨z, hzH⟩ ^ j := rfl
  rw [hβ, map_mul, map_mul, map_pow, map_pow, h.rho_t, one_pow, mul_one] at hinn
  apply hσ.rho_u_not_mem_inn
  have := (innAut (Bar L)).mul_mem hinn
    ((innAut (Bar L)).inv_mem ((innAut (Bar L)).pow_mem hzInn j))
  rwa [mul_inv_cancel_right] at this

theorem rho_beta_ne_one (hσ : Setup42 h hS w z) (i j : ℕ) : h.rho ⟨_, hσ.beta_mem_H i j⟩ ≠ 1 :=
  fun h1 => hσ.rho_beta_not_mem_inn i j (h1 ▸ one_mem _)

theorem fieldCentralizer (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    Blueprint.LieModel ↥(perfectResidual ↥(fixedPoints
        (barAction L ⟨_, hσ.beta_mem_normalizer i j⟩))) .PSL 2 p (f / 2) ∧
      2 * Nat.card (perfectResidual ↥(fixedPoints (barAction L ⟨_, hσ.beta_mem_normalizer i j⟩))) =
        Nat.card (fixedPoints (barAction L ⟨_, hσ.beta_mem_normalizer i j⟩)) ∧
      (Nat.card (fixedPoints (barAction L ⟨_, hσ.beta_mem_normalizer i j⟩))).factorization 2 =
        (Nat.card (Bar L)).factorization 2 ∧
      ∀ φ : MulAut (Bar L),
        (∀ y ∈ (perfectResidual ↥(fixedPoints (barAction L ⟨_, hσ.beta_mem_normalizer i j⟩))).map
          (fixedPoints (barAction L ⟨_, hσ.beta_mem_normalizer i j⟩)).subtype, φ y = y) →
          φ = 1 ∨ φ = barAction L ⟨_, hσ.beta_mem_normalizer i j⟩ :=
  hFC (Bar L) p f h.config.prime h.config.ne_two
    (h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel) h.sixteen
    h.config.lieModel _ (hσ.isFieldAut_rho hKC i j (hσ.beta_mem_H i j))

theorem lieModel_bar_K (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    Blueprint.LieModel (Bar (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      .PSL 2 p (f / 2) :=
  lieModel_bar_centralizerResidual (hσ.beta_mem_normalizer i j) (hσ.isPGroup_zpowers_beta i j)
    h.config.ne_two (hσ.fieldCentralizer hFC hKC i j).1

theorem oddCore_K (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (pPrimeCore 2 ↥(centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))).map
        (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).subtype =
      centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ⊓
        (pPrimeCore 2 ↥L).map L.subtype :=
  map_pPrimeCore_centralizerResidual (hσ.beta_mem_normalizer i j) (hσ.isPGroup_zpowers_beta i j)
    h.config.ne_two (hσ.fieldCentralizer hFC hKC i j).1

theorem oddCore_CL (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (pPrimeCore 2 ↥(L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).map
        (L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).subtype =
      (L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ⊓
        (pPrimeCore 2 ↥L).map L.subtype :=
  map_pPrimeCore_centralizer (hσ.beta_mem_normalizer i j) (hσ.isPGroup_zpowers_beta i j)
    h.config.ne_two (hσ.fieldCentralizer hFC hKC i j).1 (hσ.fieldCentralizer hFC hKC i j).2.1

omit [Finite X] in
theorem D_le_CL (hσ : Setup42 h hS w z) (i j : ℕ) :
    S ⊓ L ≤ L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} :=
  le_inf inf_le_right (hσ.D_le_centralizer_beta i j)

theorem isSylowOf_D_CL (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsSylowOf 2 (S ⊓ L) (L ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) :=
  (h.isSylowOf_inf hS).of_le (hσ.D_le_CL i j) inf_le_left

theorem isSylowOf_Dstar (hσ : Setup42 h hS w z) (i j : ℕ) :
    IsSylowOf 2 (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j))
      (centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
  isSylowOf_inf_centralizerResidual (h.isSylowOf_inf hS) (hσ.D_le_centralizer_beta i j)

theorem relIndex_Dstar (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)).relIndex (S ⊓ L) = 2 :=
  relIndex_inf_centralizerResidual (hσ.beta_mem_normalizer i j) (hσ.isPGroup_zpowers_beta i j)
    h.config.ne_two (hσ.fieldCentralizer hFC hKC i j).1 (hσ.fieldCentralizer hFC hKC i j).2.1
    (hσ.fieldCentralizer hFC hKC i j).2.2.1 (h.isSylowOf_inf hS) (hσ.D_le_centralizer_beta i j)

theorem z_mem_Dstar (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    z ∈ S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) := by
  obtain ⟨c, hc, hc2⟩ := hσ.exists_commutator_sq_eq_z
  have := sq_mem_of_relIndex_two (hσ.relIndex_Dstar hFC hKC i j) (commutator_self_le _ hc)
  rwa [hc2] at this

theorem dihedral_Dstar (hFC : AutPSL2FieldCentralizerInput) (hKC : AutPSL2CentralizerInput)
    (hσ : Setup42 h hS w z) (i j : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty
      (↥(S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≃*
        DihedralGroup (2 ^ m)) := by
  obtain ⟨m, -, ⟨d⟩⟩ := dihedral_inf_centralizerResidual (hσ.beta_mem_normalizer i j)
    (hσ.isPGroup_zpowers_beta i j) h.config.ne_two (hσ.fieldCentralizer hFC hKC i j).1
    (h.isSylowOf_inf hS) (hσ.D_le_centralizer_beta i j)
  obtain ⟨m₀, hm₀, ⟨e⟩⟩ := hσ.dihedral
  refine ⟨m, ?_, ⟨d⟩⟩
  have h1 := relIndex_mul_card
    (inf_le_left : S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤ S ⊓ L)
  rw [hσ.relIndex_Dstar hFC hKC i j, Nat.card_congr d.toEquiv, Nat.card_congr e.toEquiv,
    DihedralGroup.nat_card, DihedralGroup.nat_card] at h1
  have h2 : 2 ^ (m + 1) = 2 ^ m₀ := by rw [pow_succ]; linarith
  have h3 := Nat.pow_right_injective le_rfl h2
  omega

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit

module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma44a

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ}

omit [Finite X] in
theorem map_conj_inf_centralizer {g τ : X} (hg : g ∈ centralizer ({t} : Set X)) :
    (centralizer ({t} : Set X) ⊓ centralizer {τ}).map (MulAut.conj g).toMonoidHom =
      centralizer ({t} : Set X) ⊓ centralizer {g * τ * g⁻¹} := by
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, map_conj_centralizer,
    map_conj_centralizer]
  congr 2
  have : g * t = t * g := mem_centralizer_singleton_iff.mp hg
  rw [this, mul_inv_cancel_right]

omit [Finite X] in
theorem isPGroup_quot_conj {g τ : X} (hg : g ∈ centralizer ({t} : Set X))
    (h1 : IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {τ}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {τ}))) :
    IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {g * τ * g⁻¹}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {g * τ * g⁻¹})) :=
  isPGroup_quot_of_mulEquiv ((equivMapOfInjective _ _ (MulEquiv.injective _)).trans
    (MulEquiv.subgroupCongr (map_conj_inf_centralizer hg))) h1

omit [Finite X] in
theorem card_conj_inf_centralizer {g τ : X} (hg : g ∈ centralizer ({t} : Set X)) :
    Nat.card ↥(centralizer ({t} : Set X) ⊓ centralizer {g * τ * g⁻¹}) =
      Nat.card ↥(centralizer ({t} : Set X) ⊓ centralizer {τ}) := by
  rw [← map_conj_inf_centralizer hg]
  exact Subgroup.card_map_of_injective (MulEquiv.injective _)

theorem factorization_two_succ {p f : ℕ} (hp : Odd p) (hf : Even f) :
    (p ^ f + 1).factorization 2 = 1 := by
  obtain ⟨k, rfl⟩ := hf
  obtain ⟨m, hm⟩ := hp.pow (n := k)
  have hq : p ^ (k + k) + 1 = 2 * (2 * (m ^ 2 + m) + 1) := by
    rw [← two_mul, pow_mul', hm]
    ring
  rw [hq, Nat.factorization_mul two_ne_zero (by omega), Finsupp.add_apply,
    Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd (by omega)]

namespace Standing.Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem rho_not_mem_of_not_mem_T (hσ : Setup42 h hS w z) {τ : X} (hτS : τ ∈ S)
    (hτT : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) :
    h.rho ⟨τ, hS.le hτS⟩ ∉ ((S.subgroupOf (centralizer ({t} : Set X))).map h.rho ⊓
      innAut (Bar L)) ⊔ zpowers (h.rho ⟨w, hS.le hσ.lift.mem⟩) := by
  intro hmem
  rw [← hσ.map_rho_T] at hmem
  obtain ⟨⟨x, hxH⟩, hxT, hx⟩ := hmem
  have hk : h.rho ⟨x⁻¹ * τ, mul_mem (inv_mem hxH) (hS.le hτS)⟩ = 1 := by
    show h.rho (⟨x, hxH⟩⁻¹ * ⟨τ, hS.le hτS⟩) = 1
    rw [map_mul, map_inv, hx, inv_mul_cancel]
  have hxS : x ∈ S := hσ.T_le hxT
  have h2 := h.mem_zpowers_of_rho_eq_one hS (S.mul_mem (S.inv_mem hxS) hτS) hk
  apply hτT
  rw [show τ = x * (x⁻¹ * τ) by group]
  exact mul_mem hxT (mem_sup_left (mem_sup_left h2))

theorem dihedral_CL_of_not_mem_T (hI : AutPSL2InvolutionInput) (hσ : Setup42 h hS w z)
    {τ : X} (hτS : τ ∈ S) (hτT : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hτ2 : τ ^ 2 = 1) :
    Nonempty (↥(L ⊓ centralizer {τ}) ⧸ (barMap L (inf_le_left : L ⊓ centralizer {τ} ≤ L)).ker ≃*
      DihedralGroup ((p ^ f + 1) / 2)) := by
  have hτN : τ ∈ normalizer (L : Set X) := h.centralizer_le_normalizer (hS.le hτS)
  have hτ2' : IsPGroup 2 (zpowers τ) := by
    have hd : orderOf τ ∣ 2 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hτ2
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  have hα2 : h.rho ⟨τ, hS.le hτS⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨τ, hS.le hτS⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow, hτ2, Subgroup.coe_one]), map_one]
  obtain ⟨⟨e⟩, -⟩ := (hσ.involutionInput hI).2.2 _ ⟨⟨τ, hS.le hτS⟩, hτS, rfl⟩
    (hσ.rho_not_mem_of_not_mem_T hτS hτT) hα2
  exact ⟨(QuotientGroup.quotientKerEquivRange _).trans
    ((MulEquiv.subgroupCongr (range_barMap_centralizer hτN hτ2')).trans e)⟩

theorem isSylowOf_z_CL_of_not_mem_T (hI : AutPSL2InvolutionInput) (hσ : Setup42 h hS w z)
    {τ : X} (hτS : τ ∈ S) (hτT : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hτ2 : τ ^ 2 = 1) :
    IsSylowOf 2 (zpowers z) (L ⊓ centralizer {τ}) := by
  obtain ⟨e⟩ := hσ.dihedral_CL_of_not_mem_T hI hτS hτT hτ2
  have hzC : z ∈ L ⊓ centralizer {τ} :=
    ⟨hσ.z_mem.2, mem_centralizer_singleton_iff.mpr (hσ.z_comm hτS).symm⟩
  refine isSylowOf_of_card (zpowers_le.mpr hzC) ?_
  rw [Nat.card_zpowers, hσ.z_order]
  have hcard : Nat.card ↥(L ⊓ centralizer {τ}) = Nat.card (DihedralGroup ((p ^ f + 1) / 2)) *
      Nat.card (barMap L (inf_le_left : L ⊓ centralizer {τ} ≤ L)).ker := by
    rw [← Nat.card_congr e.toEquiv]
    exact (barMap L _).ker.card_eq_card_quotient_mul_card_subgroup
  have hodd : Odd p := h.config.prime.odd_of_ne_two h.config.ne_two
  have heven := h.dihedral.even p f h.config.prime h.config.ne_two h.config.lieModel
  have hq : 2 * ((p ^ f + 1) / 2) = p ^ f + 1 := by
    have : 2 ∣ p ^ f + 1 := by
      have := (hodd.pow (n := f)).add_one
      exact even_iff_two_dvd.mp this
    omega
  rw [hcard, DihedralGroup.nat_card, hq, Nat.factorization_mul (by omega) Nat.card_pos.ne',
    Finsupp.add_apply, factorization_two_succ hodd heven, Nat.factorization_eq_zero_of_not_dvd
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_ker_barMap _)), add_zero,
    pow_one]

theorem isPGroup_quot_of_not_mem_T (hI : AutPSL2InvolutionInput) (hσ : Setup42 h hS w z)
    {τ : X} (hτS : τ ∈ S) (hτT : τ ∉ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w) (hτ2 : τ ^ 2 = 1) :
    IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {τ}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {τ})) := by
  have hτH := hS.le hτS
  have hα2 : h.rho ⟨τ, hτH⟩ ^ 2 = 1 := by
    rw [← map_pow, show (⟨τ, hτH⟩ : ↥(centralizer ({t} : Set X))) ^ 2 = 1 from
      Subtype.ext (by rw [Subgroup.coe_pow, hτ2, Subgroup.coe_one]), map_one]
  obtain ⟨-, hnc⟩ := (hσ.involutionInput hI).2.2 _ ⟨⟨τ, hτH⟩, hτS, rfl⟩
    (hσ.rho_not_mem_of_not_mem_T hτS hτT) hα2
  refine h.isPGroup_quot_of_rho inf_le_left ⟨mem_centralizer_singleton_iff.mpr rfl,
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hτH).symm⟩
    (isPGroup_quot_of_le ?_ hnc)
  rintro _ ⟨⟨a, haH⟩, ha, rfl⟩
  refine ⟨⟨_, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp ha.2)

theorem lemma44b (hI : AutPSL2InvolutionInput) (hKF : AutPSL2FusionInput)
    (hKC : AutPSL2CentralizerInput) (hσ : Setup42 h hS w z) {τ : X} (hτS : τ ∈ S)
    (hτ2 : τ ^ 2 = 1) (hτ1 : τ ≠ 1) (hτt : τ ≠ t)
    (hτ : ¬ IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {τ}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {τ}))) :
    ∃ g ∈ centralizer ({t} : Set X), ∃ i j : ℕ,
      g * τ * g⁻¹ = w ^ (orderOf w / 2) * t ^ i * z ^ j ∧
      twoPart (centralizer ({t} : Set X) ⊓ centralizer {τ}) =
        Nat.card (zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) := by
  have hτT : τ ∈ zpowers t ⊔ (S ⊓ L) ⊔ zpowers w := by
    by_contra hτT
    exact hτ (hσ.isPGroup_quot_of_not_mem_T hI hτS hτT hτ2)
  obtain ⟨g, hg, hgX⟩ := hσ.exists_conj_mem_X hKF hτT hτ2
  have hcases : g * τ * g⁻¹ ∉ zpowers t ⊔ (S ⊓ L) := by
    intro hD
    obtain ⟨a, c, ha, hc, hac⟩ := hσ.mem_X_tD hgX hD
    have hgt : g * t * g⁻¹ = t := by
      rw [show g * t = t * g from mem_centralizer_singleton_iff.mp hg, mul_inv_cancel_right]
    have hback : ∀ x : X, g * τ * g⁻¹ = x → τ = g⁻¹ * x * g := fun x hx => by
      rw [← hx]
      group
    rcases ha with ha | ha <;> rcases hc with hc | hc <;> rw [ha, hc] at hac
    · apply hτ1
      rw [hback _ hac]
      group
    ·
      apply hτ
      have h1 := (hσ.isPGroup_quot_centralizer_z hI).1
      rw [one_mul] at hac
      have h2 := isPGroup_quot_conj (inv_mem hg) h1
      rwa [← hac, show g⁻¹ * (g * τ * g⁻¹) * g⁻¹⁻¹ = τ by group] at h2
    · apply hτt
      rw [mul_one] at hac
      rw [hback _ hac, show g⁻¹ * t * g = t by
        rw [show g⁻¹ * t = t * g⁻¹ from mem_centralizer_singleton_iff.mp (inv_mem hg),
          inv_mul_cancel_right]]
    ·
      apply hτ
      have h1 := (hσ.isPGroup_quot_centralizer_z hI).1
      have heq : centralizer ({t} : Set X) ⊓ centralizer {z} =
          centralizer ({t} : Set X) ⊓ centralizer {t * z} := by
        ext y
        simp only [mem_inf, mem_centralizer_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have : y * (t * z) = t * (y * z) := by rw [← mul_assoc, h1, mul_assoc]
          rw [this, mul_assoc] at h2
          exact mul_left_cancel h2
      rw [heq] at h1
      have h2 := isPGroup_quot_conj (inv_mem hg) h1
      rwa [← hac, show g⁻¹ * (g * τ * g⁻¹) * g⁻¹⁻¹ = τ by group] at h2
  obtain ⟨i, j, hij⟩ := hσ.mem_X_not_tD hgX hcases
  refine ⟨g, hg, i, j, hij, ?_⟩
  rw [twoPart, ← card_conj_inf_centralizer hg, hij]
  exact ((hσ.isSylowOf_centralizer hKC i j).card_eq).symm

end Standing.Setup42

end CFSG.ComponentClassification.HarrisLit

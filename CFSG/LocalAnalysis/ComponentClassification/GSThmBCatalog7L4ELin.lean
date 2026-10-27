module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EType
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ERowO
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ERowS

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

namespace Catalog7L4M

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector CFSG.ComponentClassification.UnbalancedLayer

variable {H : Type} [Group H]

theorem centralizer_le_kernel (K : Subgroup H) :
    centralizer (K : Set H) ≤ coreActionKernel K := by
  intro g hg
  refine mem_coreActionKernel.mpr ⟨centralizer_le_normalizer _ hg, fun j hj => ?_⟩
  have h1 : j * g = g * j := mem_centralizer_iff.mp hg j hj
  rw [show j⁻¹ * g⁻¹ * j * g = 1 by
    calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
      _ = j⁻¹ * g⁻¹ * (g * j) := by rw [h1]
      _ = 1 := by group]
  exact one_mem _

variable [Finite H]

theorem false_of_four_group {b x : H} {K : Subgroup H} (hb : orderOf b = 2) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hxb : x ≠ b) (hxbc : x * b = b * x) (hbK : K ≤ centralizer ({b} : Set H))
    (hxK : ∀ y ∈ K, x * y = y * x)
    (hsyl : ∀ T : Subgroup H, IsPGroup 2 T →
      T ≤ centralizer ({b} : Set H) ⊓ coreActionKernel K → Nat.card T ≤ 2) : False := by
  classical
  have hb1 : b ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hX : IsPGroup 2 (zpowers b) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hb, pow_one])
  have hZ : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxo, pow_one])
  have hc' : ∀ i : ℤ, x * b ^ i * x⁻¹ = b ^ i := fun i => by
    rw [(Commute.zpow_right hxbc i).eq, mul_inv_cancel_right]
  have hZX : zpowers x ≤ normalizer ((zpowers b : Subgroup H) : Set H) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro g
    rw [mem_zpowers_iff, mem_zpowers_iff]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, (hc' i).symm⟩
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have h2 : x * g * x⁻¹ = x * b ^ i * x⁻¹ := by rw [← hi, hc' i]
      exact (mul_left_cancel (mul_right_cancel h2)).symm
  set T := zpowers b ⊔ zpowers x with hTdef
  have hT : IsPGroup 2 T := IsPGroup.to_sup_of_normal_left' hX hZ hZX
  have hTb : T ≤ centralizer ({b} : Set H) := by
    rw [sup_le_iff, zpowers_le, zpowers_le]
    exact ⟨mem_centralizer_singleton_iff.mpr rfl, mem_centralizer_singleton_iff.mpr hxbc⟩
  have hTK : T ≤ centralizer (K : Set H) := by
    rw [sup_le_iff, zpowers_le, zpowers_le]
    refine ⟨mem_centralizer_iff.mpr fun y hy => ?_, mem_centralizer_iff.mpr fun y hy => ?_⟩
    · exact mem_centralizer_singleton_iff.mp (hbK hy)
    · exact (hxK y hy).symm
  have hcard := hsyl T hT (le_inf hTb (hTK.trans (centralizer_le_kernel K)))
  have : Fintype T := Fintype.ofFinite T
  have hbT : b ∈ T := mem_sup_left (mem_zpowers b)
  have hxT : x ∈ T := mem_sup_right (mem_zpowers x)
  have h3 : ({1, ⟨b, hbT⟩, ⟨x, hxT⟩} : Finset T).card = 3 := by
    rw [Finset.card_eq_three]
    refine ⟨1, ⟨b, hbT⟩, ⟨x, hxT⟩, ?_, ?_, ?_, rfl⟩
    · intro h
      exact hb1 (congrArg Subtype.val h).symm
    · intro h
      exact hx1 (congrArg Subtype.val h).symm
    · intro h
      exact hxb (congrArg Subtype.val h).symm
  have h4 := Finset.card_le_univ ({1, ⟨b, hbT⟩, ⟨x, hxT⟩} : Finset T)
  rw [h3, ← Nat.card_eq_fintype_card] at h4
  omega

theorem false_of_psl4 (hC : centralizer (generalizedFitting H : Set H) = ⊥) {r e : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (he : 1 ≤ e)
    (hm : Blueprint.LieModel ↥(generalizedFitting H) .PSL 4 r e) {a b : H}
    (ha : orderOf a = 2) (hb : orderOf b = 2) {J K : Subgroup H}
    (hJF : J ≤ generalizedFitting H) (hKF : K ≤ generalizedFitting H)
    (hJa : J ≤ centralizer ({a} : Set H))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set H))))
    (hKb : K ≤ centralizer ({b} : Set H))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set H))))
    (hsyl : ∀ T : Subgroup H, IsPGroup 2 T →
      T ≤ centralizer ({b} : Set H) ⊓ coreActionKernel K → Nat.card T ≤ 2)
    (hbJ : b ∈ coreActionKernel J) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f)
    (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p f)
    (hKm : Blueprint.LieModel (K ⧸ pPrimeCore 2 K) .PSL 2 p (2 * f)) : False := by
  classical
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  obtain ⟨-, k, _, _, hk, ⟨φ₀⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hm
  have : CharP k r := finite_field_prime_power_characteristic hr he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k r]; exact hr2
  have htwo : (2 : k) ≠ 0 := Ring.two_ne_zero hk2
  have hq3 : 3 ≤ Nat.card k := by
    rw [hk]
    have h3 : 3 ≤ r := by have := hr.two_le; omega
    exact h3.trans (Nat.le_self_pow (by omega) r)
  set φ : ↥(generalizedFitting H) ≃* projectiveSL 4 k :=
    φ₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 4 k).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 k)) with hφ
  have hZ := OddSelector.center_projectiveSL_eq_bot (k := k) (by norm_num : 3 ≤ 4)
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hC φ hZ
  have h5' : 5 ≤ p ^ (2 * f) := h5.trans (Nat.pow_le_pow_right hp.pos (by omega))
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  obtain ⟨hJO, hJt⟩ := psl4_component_type hC hr hr2 he hk φ hinj hρW ha hJF hJa hJ hp hp2 h5 hJm
  obtain ⟨-, hKt⟩ := psl4_component_type hC hr hr2 he hk φ hinj hρW hb hKF hKb hK hp hp2 h5' hKm
  set q := Nat.card k with hqdef
  rcases hJt with ⟨hJq, -⟩ | ⟨hJq, h5k, A, hρa, hA, ψ, hψ, hJfac⟩
  ·
    rcases hKt with ⟨hKq, -⟩ | ⟨hKq, -⟩
    · rw [hpow, hJq] at hKq
      have h9 : 9 ≤ q ^ 2 := by nlinarith
      nlinarith
    · rw [hpow, hJq] at hKq
      have h9 : 9 ≤ q ^ 2 := by nlinarith
      nlinarith
  rcases hKt with ⟨hKq, hrow⟩ | ⟨hKq, -⟩
  swap
  ·
    rw [hpow, hJq] at hKq
    nlinarith
  rcases hrow with hS | ⟨B, hρb, hB, hns⟩
  ·
    obtain ⟨ν, hν, Ψ, C, -, hρb, -, -, -, -, -, -, hKmap, -⟩ := hS
    have : Fact (¬ IsSquare (ν : k)) := ⟨hν⟩
    obtain ⟨x₀, hx₀2, hx₀s, hx₀b, hx₀K, hx₀A⟩ :=
      OddSelector.Catalog7L4E.exists_rowS_involution ν hk2 Ψ C A
        (OddSelector.Catalog7L4E.isSquare_det_of_split htwo hA ψ hψ)
    rw [← hρa] at hx₀A
    obtain ⟨y, hy⟩ := hx₀A
    obtain ⟨x, hρx⟩ : ∃ x : H, ρ x = x₀ :=
      ⟨a * (φ.symm y : H), by
        rw [map_mul, hρW, MulEquiv.apply_symm_apply, hy, mul_inv_cancel_left]⟩
    have hsemi : ∀ X : GL (Fin 4) k, conjAut 4 k X ∈ semilinearAutGroup 4 k := fun X =>
      mem_semilinearAutGroup_iff.mpr ⟨X, 1, by rw [map_one, mul_one]⟩
    have hx1 : x ≠ 1 := by
      intro h
      apply hx₀s
      rw [← hρx, h, map_one]
      exact one_mem _
    have hxb : x ≠ b := by
      intro h
      apply hx₀s
      rw [← hρx, h, hρb]
      exact mul_mem (mul_mem (hsemi C) (hsemi _)) (inv_mem (hsemi C))
    have hx2 : x ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hρx, sq, hx₀2, map_one]
    have hxbc : x * b = b * x := by
      apply hinj
      rw [map_mul, map_mul, hρx, hρb]
      exact hx₀b.eq
    have hxK : ∀ z ∈ K, x * z = z * x := by
      intro z hz
      have h1 : ρ z ∈ K.map ρ := ⟨z, hz, rfl⟩
      rw [hKmap] at h1
      obtain ⟨t, ⟨g, rfl⟩, ht⟩ := h1
      apply hinj
      rw [map_mul, map_mul, hρx, ← ht]
      exact (hx₀K g).eq
    exact false_of_four_group hb hx2 hx1 hxb hxbc hKb hxK hsyl
  ·
    have hbJc : ∀ j ∈ J, b * j = j * b := by
      intro j hj
      have h1 := (mem_coreActionKernel.mp hbJ).2 j hj
      rw [hJO, Subgroup.map_bot, mem_bot] at h1
      calc b * j = b * (j * (j⁻¹ * b⁻¹ * j * b)) := by rw [h1, mul_one]
        _ = j * b := by group
    obtain ⟨fJ, hfJ, hJmap⟩ : ∃ fJ : SpecialLinearGroup (Fin 2) k →* GL (Fin 4) k,
        (fJ = splitLeftHom ψ ∨ fJ = splitRightHom ψ) ∧ J.map ρ = fJ.range.map (conjAut 4 k) := by
      rcases hJfac with h | h
      · exact ⟨_, Or.inl rfl, h⟩
      · exact ⟨_, Or.inr rfl, h⟩
    have hmemJ : ∀ U, ∃ j ∈ J, ρ j = conjAut 4 k (fJ U) := by
      intro U
      have h1 : conjAut 4 k (fJ U) ∈ J.map ρ := by
        rw [hJmap]
        exact ⟨fJ U, ⟨U, rfl⟩, rfl⟩
      obtain ⟨j, hj, hjeq⟩ := h1
      exact ⟨j, hj, hjeq⟩
    have hcA : ∀ U, conjAut 4 k (fJ U) ∈ centralizer {conjAut 4 k A * dualAut 4 k} := by
      intro U
      obtain ⟨j, hj, hjeq⟩ := hmemJ U
      rw [← hjeq, ← hρa]
      refine mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hJa hj)]
    have hcB : ∀ U, conjAut 4 k (fJ U) ∈ centralizer {conjAut 4 k B * dualAut 4 k} := by
      intro U
      obtain ⟨j, hj, hjeq⟩ := hmemJ U
      rw [← hjeq, ← hρb]
      refine mem_centralizer_singleton_iff.mpr ?_
      rw [← map_mul, ← map_mul, hbJc j hj]
    exact hns (OddSelector.Catalog7L4E.split_of_commute_factor hk2 h5k hA hB ψ hψ hfJ hcA hcB)

end Catalog7L4M

end CFSG.ComponentClassification.GSThmB

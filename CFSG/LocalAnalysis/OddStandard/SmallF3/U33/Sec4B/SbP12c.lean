module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP12b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTOrb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AC0A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.WreathB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

private lemma mem_zpowers_eq_one_or_eq {z g : G} (hz : z * z = 1) (hg : g ∈ zpowers z) :
    g = 1 ∨ g = z := by
  let H : Subgroup G :=
    { carrier := {g : G | g = 1 ∨ g = z}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by simp)
        · exact Or.inr (by simp)
        · exact Or.inl (by rw [hz])
      inv_mem' := by
        intro a ha
        rcases ha with rfl | rfl
        · exact Or.inl (by simp)
        · exact Or.inr (by rw [inv_eq_of_mul_eq_one_right hz]) }
  exact (Subgroup.zpowers_le.mpr (show z ∈ H from Or.inr rfl)) hg

private lemma baseGrp_le_L (hc : Ctx0 t L S x₁ x₂ lam rho) : baseGrp x₁ x₂ ≤ L := by
  rw [baseGrp, Subgroup.closure_le]
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact (S4A.generators_mem_L hc).1
  · exact (S4A.generators_mem_L hc).2.1

private lemma twoCore_commute_baseGrp (hc : Ctx0 t L S x₁ x₂ lam rho) :
    ∀ p ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, p * b = b * p := by
  intro p hp b hb
  have hpc : p ∈ Subgroup.centralizer (L : Set G) := by
    have hmem : p ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t := by
      rw [hc.hyp.centralizer_eq]
      exact hp
    exact hmem.1
  exact (Subgroup.mem_centralizer_iff.mp hpc b (baseGrp_le_L hc hb)).symm

theorem l12_CRt_normal (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    NormalIn (ctxR t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) (ctxR t tau x₁ x₂) := by
  constructor
  · exact inf_le_left
  · intro g hg k hk
    have hkR : k ∈ ctxR t tau x₁ x₂ := hk.1
    have hkt : k * t = t * k := Subgroup.mem_centralizer_singleton_iff.mp hk.2
    have hgR : g * k * g⁻¹ ∈ ctxR t tau x₁ x₂ :=
      (ctxR t tau x₁ x₂).mul_mem ((ctxR t tau x₁ x₂).mul_mem hg hkR)
        ((ctxR t tau x₁ x₂).inv_mem hg)
    have hu_mem : g⁻¹ * t * g ∈ conjIn (ctxR t tau x₁ x₂) t :=
      ⟨g⁻¹, (ctxR t tau x₁ x₂).inv_mem hg, by simp⟩
    rw [hc.tR] at hu_mem
    obtain ⟨v, hv, htv⟩ := Set.mem_smul_set.mp hu_mem
    have htv' : t * v = g⁻¹ * t * g := by simpa using htv
    have hkv : k * v = v * k := by
      have hVle : fourGrp x₁ x₂ ≤
          ctxO t tau x₁ x₂ ⊓ centralizer ((ctxO t tau x₁ x₂ : Subgroup G) : Set G) :=
        le_of_eq hc.center_O.symm
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hVle hv)).2 k
        (hc.R_le_O hkR)
    refine ⟨hgR, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc (g * k * g⁻¹) * t
        = g * (k * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * (k * (t * v)) * g⁻¹ := by rw [← htv']
      _ = g * ((k * t) * v) * g⁻¹ := by group
      _ = g * ((t * k) * v) * g⁻¹ := by rw [hkt]
      _ = g * (t * (k * v)) * g⁻¹ := by group
      _ = g * (t * (v * k)) * g⁻¹ := by rw [hkv]
      _ = g * ((t * v) * k) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * k) * g⁻¹ := by rw [htv']
      _ = t * (g * k * g⁻¹) := by group

theorem l12_card_CRt (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxR t tau x₁ x₂ ⊓ centralizer ({t} : Set G)) = 2 ^ 6 := by
  have h := card_eq_ncard_conjIn_mul (ctxR t tau x₁ x₂) t
  have hVcard : (fourGrp x₁ x₂ : Set G).ncard = 4 := by
    change Nat.card ↥(fourGrp x₁ x₂) = 4
    exact (hc.wreath.fourGrp_eq_omega).2.2
  rw [hc.tR, Set.ncard_smul_set, hVcard, hc.card_R] at h
  norm_num at h ⊢
  omega

theorem l12_card_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) : Nat.card ↥(ctxW t x₁ x₂) = 32 := by
  have hPcard : Nat.card ↥(twoCore t) = 2 := by
    rw [hc.l43, Nat.card_zpowers, hc.hyp.ord_t]
  have hBcard : Nat.card ↥(baseGrp x₁ x₂) = 16 := (hc.wreath.baseGrp_eq).2.2
  have hcomm : ∀ p ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, p * b = b * p :=
    twoCore_commute_baseGrp hc.toCtx0
  have hinf : twoCore t ⊓ baseGrp x₁ x₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := baseGrp_le_L hc.toCtx0 hx.2
    have hmem : x ∈ twoCore t ⊓ L := ⟨hx.1, hxL⟩
    rw [hc.hyp.twoCore_inf] at hmem
    simpa using hmem
  have hcard := card_sup_of_commute (P := twoCore t) (Q := baseGrp x₁ x₂) hcomm hinf
  change Nat.card ↥(twoCore t ⊔ baseGrp x₁ x₂) = 32
  rw [hcard, hPcard, hBcard] <;> norm_num

theorem l12_tau_normalizes_W (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    ∀ w ∈ ctxW t x₁ x₂, tau * w * tau⁻¹ ∈ ctxW t x₁ x₂ := by
  have hcomm : ∀ p ∈ twoCore t, ∀ b ∈ baseGrp x₁ x₂, p * b = b * p :=
    twoCore_commute_baseGrp hc.toCtx0
  have htau_t : tau * t = t * tau :=
    S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)
  have hPt : ∀ p ∈ twoCore t, tau * p * tau⁻¹ ∈ twoCore t := by
    intro p hp
    rw [hc.l43] at hp ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← hk]
    have hkeq : tau * t ^ k * tau⁻¹ = t ^ k := by
      rw [show tau * t ^ k = t ^ k * tau from Commute.zpow_right htau_t k]
      group
    rw [hkeq]
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
  have hB : ∀ b ∈ baseGrp x₁ x₂, tau * b * tau⁻¹ ∈ baseGrp x₁ x₂ := by
    intro b hb
    rw [baseGrp] at hb ⊢
    refine Subgroup.closure_induction
      (p := fun b _ => tau * b * tau⁻¹ ∈ Subgroup.closure ({x₁, x₂} : Set G))
      ?_ ?_ ?_ ?_ hb
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · rw [hc.tau_x₁]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
      · rw [hc.tau_x₂]
        exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
    · simpa using Subgroup.one_mem (Subgroup.closure ({x₁, x₂} : Set G))
    · intro a b _ _ ha hb
      have h : tau * (a * b) * tau⁻¹ = (tau * a * tau⁻¹) * (tau * b * tau⁻¹) := by group
      rw [h]
      exact Subgroup.mul_mem _ ha hb
    · intro a _ ha
      have h : tau * a⁻¹ * tau⁻¹ = (tau * a * tau⁻¹)⁻¹ := by group
      rw [h]
      exact Subgroup.inv_mem _ ha
  intro w hw
  rw [ctxW] at hw ⊢
  obtain ⟨p, hp, b, hb, rfl⟩ :=
    (mem_sup_iff_of_commute (P := twoCore t) (Q := baseGrp x₁ x₂) hcomm).mp hw
  have hp' : tau * p * tau⁻¹ ∈ twoCore t := hPt p hp
  have hb' : tau * b * tau⁻¹ ∈ baseGrp x₁ x₂ := hB b hb
  have hsplit : tau * (p * b) * tau⁻¹ = (tau * p * tau⁻¹) * (tau * b * tau⁻¹) := by
    group
  rw [hsplit]
  exact Subgroup.mul_mem_sup hp' hb'

theorem l12_card_W_tau (hc : Ctx4 t L S x₁ x₂ lam rho tau) :
    Nat.card ↥(ctxW t x₁ x₂ ⊔ zpowers tau) = 2 ^ 6 := by
  have htau2 : tau ^ 2 = 1 := hc.l44.1
  have htau_mul : tau * tau = 1 := by simpa [pow_two] using hc.l44.1
  have htinv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right htau_mul
  have hnorm : ∀ k ∈ zpowers tau, ∀ h ∈ ctxW t x₁ x₂, k * h * k⁻¹ ∈ ctxW t x₁ x₂ := by
    have hmem : tau ∈ normalizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact l12_tau_normalizes_W hc h hh
      · intro hh
        have hh' := l12_tau_normalizes_W hc (tau * h * tau⁻¹) hh
        have h1 : tau * (tau * h * tau⁻¹) * tau⁻¹ = h := by
          rw [htinv]
          calc tau * (tau * h * tau) * tau = (tau * tau) * h * (tau * tau) := by group
            _ = h := by rw [htau_mul]; group
        rwa [h1] at hh'
    intro k hk h hh
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hmem hk) h).mp hh
  have hinf : ctxW t x₁ x₂ ⊓ zpowers tau = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hWle : ctxW t x₁ x₂ ≤ twoCore t ⊔ L := by
      rw [ctxW]
      exact sup_le le_sup_left (le_trans (baseGrp_le_L hc.toCtx0) le_sup_right)
    rcases mem_zpowers_eq_one_or_eq htau_mul hx.2 with rfl | rfl
    · rfl
    · exact absurd (hWle hx.1) hc.tau_not_mem
  have hcard := card_sup_eq_mul (H := ctxW t x₁ x₂) (K := zpowers tau) hnorm hinf
  have htau_ne : tau ≠ 1 := by
    intro h
    apply hc.tau_not_mem
    rw [h]
    exact Subgroup.mem_sup_left (Subgroup.one_mem (twoCore t))
  have hZcard : Nat.card ↥(zpowers tau) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime htau2 htau_ne]
  rw [hcard, l12_card_W hc, hZcard]
  norm_num

theorem l12_W_tau_le_CRt (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxW t x₁ x₂ ⊔ zpowers tau ≤ ctxR t tau x₁ x₂ ⊓ centralizer ({t} : Set G) := by
  have htX : t ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have htauX : tau ∈ ctxX t tau x₁ x₂ := Subgroup.subset_closure (by simp)
  have hWR : ctxW t x₁ x₂ ≤ ctxR t tau x₁ x₂ := by
    rw [ctxW]
    refine sup_le ?_ ?_
    · rw [hc.l43]
      exact Subgroup.zpowers_le.mpr (hc.X_le_R htX)
    · exact le_trans hc.base_le_Q (l12_Q_le_R hc)
  have htW : t ∈ ctxW t x₁ x₂ := by
    rw [ctxW]
    exact Subgroup.mem_sup_left hc.hyp.mem_twoCore
  have hWcent : ctxW t x₁ x₂ ≤ centralizer ({t} : Set G) := by
    have hle : ctxW t x₁ x₂ ≤ centralizer ((ctxW t x₁ x₂ : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hc.abelian_W
    exact le_trans hle (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htW))
  have hτR : zpowers tau ≤ ctxR t tau x₁ x₂ :=
    Subgroup.zpowers_le.mpr (hc.X_le_R htauX)
  have hτcent : zpowers tau ≤ centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr
        (S4A.mem_invCent_iff.mp (hc.le_invCent hc.tau_mem)))
  exact le_inf (sup_le hWR hτR) (sup_le hWcent hτcent)

theorem l12_CRt_eq (hc : Ctx11 t L S x₁ x₂ lam rho tau) :
    ctxR t tau x₁ x₂ ⊓ centralizer ({t} : Set G) = ctxW t x₁ x₂ ⊔ zpowers tau := by
  symm
  refine eq_of_le_of_card_ge (l12_W_tau_le_CRt hc) ?_
  rw [l12_card_CRt hc, l12_card_W_tau hc.toCtx4] <;> norm_num
end CFSG.OddStandard.SmallF3.HarrisU33.S4B

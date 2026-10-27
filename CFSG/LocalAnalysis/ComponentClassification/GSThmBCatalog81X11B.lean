module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11C
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11Cy
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11S
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X11Tr

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁} {v : H} (hv : d.IsV v) (I : In81) (hst : d.Stage7 v)
  (hJ : Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 3 2)
include hv I hst hJ

theorem commutator_mem_PPv_of_mem_U {w : H} (hwU : w ∈ h.U81 v) (hwS : w ∉ h.S)
    (hSw : h.S ≤ h.P ⊔ (h.S ⊓ centralizer ({w} : Set H))) {x y : H} (hx : x ∈ h.U81 v)
    (hy : y ∈ h.U81 v) : x * y * x⁻¹ * y⁻¹ ∈ h.PPv v := by
  set M : Subgroup ↥(h.U81 v) := (h.PPv v).subgroupOf (h.U81 v) with hM
  have hMn : M.Normal := ⟨fun x hx g => by
    rw [hM, mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (U_le_normalizer_PPv hv g.2) _).mp hx⟩
  set q := QuotientGroup.mk' M with hq
  have hcomm : ∀ x y : ↥(h.U81 v), (x : H) * y * (x : H)⁻¹ * (y : H)⁻¹ ∈ h.PPv v →
      Commute (q x) (q y) := by
    intro x y hxy
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hq,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hM, mem_subgroupOf]
    exact hxy
  have hwU' : w ∈ h.U81 v := hwU
  have hSU : ∀ s ∈ h.S, s ∈ h.U81 v := fun s hs => mem_sup_left hs
  have hcS : ∀ s (hs : s ∈ h.S) t (ht : t ∈ h.S),
      Commute (q ⟨s, hSU s hs⟩) (q ⟨t, hSU t ht⟩) := fun s hs t ht =>
    hcomm _ _ (commutator_mem_PPv hv I hst hJ hs ht)
  have hcW : ∀ s (hs : s ∈ h.S), Commute (q ⟨s, hSU s hs⟩) (q ⟨w, hwU'⟩) := by
    intro s hs
    apply hcomm
    have hs' : s ∈ ((h.P ⊔ (h.S ⊓ centralizer ({w} : Set H)) : Subgroup H) : Set H) := hSw hs
    rw [coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans h.S_le_normalizer_P)] at hs'
    obtain ⟨π, hπ, c, hc, rfl⟩ := hs'
    have hcw : c * w = w * c := mem_centralizer_singleton_iff.mp (mem_inf.mp hc).2
    have hπ' : w * π⁻¹ * w⁻¹ ∈ h.PPv v :=
      (mem_normalizer_iff.mp (U_le_normalizer_PPv hv hwU) _).mp (mem_sup_left (inv_mem hπ))
    have e : π * c * w * (π * c)⁻¹ * w⁻¹ = π * (w * π⁻¹ * w⁻¹) := by
      calc π * c * w * (π * c)⁻¹ * w⁻¹ = π * (c * w) * c⁻¹ * π⁻¹ * w⁻¹ := by group
        _ = π * (w * c) * c⁻¹ * π⁻¹ * w⁻¹ := by rw [hcw]
        _ = π * (w * π⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem (mem_sup_left hπ) hπ'
  obtain ⟨s₀, hs₀, hws₀⟩ : ∃ s₀ ∈ h.S, w = s₀ * v := by
    rcases mem_U_cases hv hwU with h1 | h1
    · exact absurd h1 hwS
    · exact h1
  have hcases : ∀ u (hu : u ∈ h.U81 v), (∃ s, ∃ hs : s ∈ h.S, q ⟨u, hu⟩ = q ⟨s, hSU s hs⟩) ∨
      ∃ s, ∃ hs : s ∈ h.S, q ⟨u, hu⟩ = q ⟨s, hSU s hs⟩ * q ⟨w, hwU'⟩ := by
    intro u hu
    rcases mem_U_cases hv hu with h1 | ⟨s, hs, rfl⟩
    · exact Or.inl ⟨u, h1, rfl⟩
    · refine Or.inr ⟨s * s₀⁻¹, mul_mem hs (inv_mem hs₀), ?_⟩
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show s * v = s * s₀⁻¹ * w
      rw [hws₀]
      group
  have key : Commute (q ⟨x, hx⟩) (q ⟨y, hy⟩) := by
    rcases hcases x hx with ⟨s₁, hs₁, e₁⟩ | ⟨s₁, hs₁, e₁⟩ <;>
      rcases hcases y hy with ⟨s₂, hs₂, e₂⟩ | ⟨s₂, hs₂, e₂⟩ <;> rw [e₁, e₂]
    · exact hcS s₁ hs₁ s₂ hs₂
    · exact (hcS s₁ hs₁ s₂ hs₂).mul_right (hcW s₁ hs₁)
    · exact (hcS s₁ hs₁ s₂ hs₂).mul_left (hcW s₂ hs₂).symm
    · exact ((hcS s₁ hs₁ s₂ hs₂).mul_right (hcW s₁ hs₁)).mul_left
        ((hcW s₂ hs₂).symm.mul_right (Commute.refl _))
  rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hq,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hM, mem_subgroupOf] at key
  exact key

theorem exists_zmod_hom_U {w : H} (hwU : w ∈ h.U81 v) (hwS : w ∉ h.S)
    (hSw : h.S ≤ h.P ⊔ (h.S ⊓ centralizer ({w} : Set H))) (hu : h.a * d.sigma ∈ h.U81 v) :
    ∃ (n : ℕ) (χ : h.U81 v →* Multiplicative (ZMod n)), χ ⟨h.a * d.sigma, hu⟩ ≠ 1 := by
  set M : Subgroup ↥(h.U81 v) := (h.PPv v).subgroupOf (h.U81 v) with hM
  have hMn : M.Normal := ⟨fun x hx g => by
    rw [hM, mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.mp (U_le_normalizer_PPv hv g.2) _).mp hx⟩
  have hcomm : ∀ a b : ↥(h.U81 v) ⧸ M, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hM, mem_subgroupOf]
    have h1 := commutator_mem_PPv_of_mem_U hv I hst hJ hwU hwS hSw (inv_mem y.2) (inv_mem x.2)
    have e : (((x * y)⁻¹ * (y * x) : ↥(h.U81 v)) : H) =
        (y : H)⁻¹ * (x : H)⁻¹ * (y : H)⁻¹⁻¹ * (x : H)⁻¹⁻¹ := by
      simp only [coe_mul, coe_inv, inv_inv]
      group
    rw [e]
    exact h1
  have hne : (QuotientGroup.mk (⟨h.a * d.sigma, hu⟩ : ↥(h.U81 v)) : ↥(h.U81 v) ⧸ M) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff, hM, mem_subgroupOf]
    exact asigma_not_mem_PPv hv I hst
  obtain ⟨n, χ, hχ⟩ := X11.exists_zmod_hom_ne_one' hcomm hne
  exact ⟨n, χ.comp (QuotientGroup.mk' M), hχ⟩

theorem exists_normal_asigma {w : H} (hwU : w ∈ h.U81 v) (hwS : w ∉ h.S)
    (hSw : h.S ≤ h.P ⊔ (h.S ⊓ centralizer ({w} : Set H))) :
    ∃ (N : Subgroup H) (_ : N.Normal), IsCyclic (H ⧸ N) ∧ IsPGroup 2 (H ⧸ N) ∧
      h.a * d.sigma ∉ N := by
  have F := hst.facts
  have h3 := not_conj_asigma_sigma F hst.not_b_bz
  have hu : h.a * d.sigma ∈ h.U81 v := mem_sup_left (mul_mem h.toHyp52.a_mem_S d.sigma_mem_S)
  obtain ⟨n, χ, hχ⟩ := exists_zmod_hom_U hv I hst hJ hwU hwS hSw hu
  have hidx : ¬ 2 ∣ (h.U81 v).index := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T, hT⟩ := isSylow_U hv I.rk I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 I.c F
    exact hT ▸ T.not_dvd_index
  refine X11.exists_normal_of_zmod_character (isPGroup_U hv) hidx χ hu hχ asigma_mul_self ?_
  intro g hg hge
  have hvU : v ∈ h.U81 v := mem_sup_right (mem_zpowers v)
  have haU : h.a ∈ h.U81 v := mem_sup_left h.toHyp52.a_mem_S
  have hσU : d.sigma ∈ h.U81 v := mem_sup_left d.sigma_mem_S
  have hzU : d.z ∈ h.U81 v := mem_sup_left (h.toHyp52.D_le_S d.z_D)
  have e2 : (⟨h.a * d.sigma, hu⟩ : h.U81 v) = ⟨h.a, haU⟩ * ⟨d.sigma, hσU⟩ := rfl
  rcases conj_asigma_of_extremal hv I F h3 hge with he | he
  · exact congrArg χ (Subtype.ext he)
  · have e1 : (⟨g⁻¹ * (h.a * d.sigma) * g, hg⟩ : h.U81 v) = ⟨d.z, hzU⟩ * ⟨d.sigma, hσU⟩ :=
      Subtype.ext he
    have e3 : (⟨d.z, hzU⟩ : h.U81 v) = (⟨v, hvU⟩ : h.U81 v)⁻¹ * ⟨h.a, haU⟩ * ⟨v, hvU⟩ :=
      Subtype.ext hv.conj_a.symm
    have hza : χ ⟨d.z, hzU⟩ = χ ⟨h.a, haU⟩ := by
      rw [e3]
      exact X11.map_conj_eq χ _ _
    rw [e1, map_mul, hza, ← map_mul, ← e2]

theorem false_of_isSimpleGroup (h11 : GS81Step11Input)
    (hK : Blueprint.LieModel (h.K ⧸ pPrimeCore 2 h.K) .PSp 2 3 1) (hs : IsSimpleGroup H) :
    False := by
  obtain ⟨w, hwU, hwS, hSw⟩ := h11 H h H₁ d v hst hJ hK
  obtain ⟨N, hN, hcyc, -, huN⟩ := exists_normal_asigma hv I hst hJ hwU hwS hSw
  have hc := X11.not_mem_commutator_of_normal hcyc huN
  rcases (commutator_normal (⊤ : Subgroup H) ⊤).eq_bot_or_eq_top with h1 | h1
  · have h2 : ⁅h.a, v⁆ ∈ commutator H :=
      commutator_mem_commutator (mem_top h.a) (mem_top v)
    rw [_root_.commutator_def, h1, mem_bot, commutatorElement_def] at h2
    apply d.z_ne_a
    rw [← hv.conj_a]
    calc v⁻¹ * h.a * v = v⁻¹ * (h.a * v * h.a⁻¹ * v⁻¹)⁻¹ * h.a * v := by rw [h2, inv_one, mul_one]
      _ = h.a := by group
  · exact hc (by rw [_root_.commutator_def, h1]; exact mem_top _)

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB

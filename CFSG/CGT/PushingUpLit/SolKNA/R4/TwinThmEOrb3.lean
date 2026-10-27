module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEOrb1

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

namespace ThmE

section Orb3

variable {G : Type} [Group G]

theorem shape_noncommute' [Finite G] {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) (S : Sylow 2 G)
    {W : Subgroup G} (hWn : ∀ s ∈ (S : Subgroup G), conjSub s W = W)
    (hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x)
    {K₁ K₂ R₁ R₂ : Subgroup G} (hK₁ : K₁ ∈ Ω) (hK₂ : K₂ ∈ Ω) (hK₁₂ : K₁ ≠ K₂)
    (hR₁ : R₁ ∈ RSet Ω) (hR₂ : R₂ ∈ RSet Ω) (hR₁K₁ : R₁ ≤ K₁) (hR₂K₂ : R₂ ≤ K₂)
    (hR₁S : R₁ ≤ (S : Subgroup G)) (hR₂S : R₂ ≤ (S : Subgroup G)) {t : G}
    (htS : t ∈ (S : Subgroup G)) (ht2 : t * t = 1) (hne₁₂ : R₁ ≠ R₂)
    (hne₁₃ : R₁ ≠ conjSub t R₁) (hne₁₄ : R₁ ≠ conjSub t R₂) (hne₂₃ : R₂ ≠ conjSub t R₁)
    (hne₂₄ : R₂ ≠ conjSub t R₂) {u u' z : G} (hzK₁ : IsUniqueInvolution K₁ z)
    (hzK₂ : IsUniqueInvolution K₂ z) (hu : u ∈ R₁) (huW : u ∈ W) (hu4 : orderOf u = 4)
    (hu' : u' ∈ R₂) (hu'W : u' ∈ W) (hu'4 : orderOf u' = 4) (hz : u * u = z) (hz' : u' * u' = z)
    (hzt : t * z * t⁻¹ ≠ z) :
    TwinThmEW.D4Shape (S : Subgroup G) t (z * (t * z * t⁻¹))
      ((u * (t * u * t⁻¹)) * (u' * (t * u' * t⁻¹))⁻¹) := by
  classical
  obtain ⟨R₃, hR₃def⟩ : ∃ R, R = conjSub t R₁ := ⟨_, rfl⟩
  obtain ⟨R₄, hR₄def⟩ : ∃ R, R = conjSub t R₂ := ⟨_, rfl⟩
  obtain ⟨u₃, hu₃def⟩ : ∃ y, y = t * u * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨u₄, hu₄def⟩ : ∃ y, y = t * u' * t⁻¹ := ⟨_, rfl⟩
  obtain ⟨zt, hztdef⟩ : ∃ y, y = t * z * t⁻¹ := ⟨_, rfl⟩
  rw [← hR₃def] at hne₁₃ hne₂₃
  rw [← hR₄def] at hne₁₄ hne₂₄
  rw [← hu₃def, ← hu₄def, ← hztdef]
  rw [← hztdef] at hzt
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hR₃Ω : R₃ ∈ RSet Ω := hR₃def ▸ RSet.conj hΩ.conjInvariant hR₁ t
  have hR₄Ω : R₄ ∈ RSet Ω := hR₄def ▸ RSet.conj hΩ.conjInvariant hR₂ t
  have hR₃S : R₃ ≤ (S : Subgroup G) := hR₃def ▸ TwinThmEW.orb4_conjSub_le_of_mem htS hR₁S
  have hR₄S : R₄ ≤ (S : Subgroup G) := hR₄def ▸ TwinThmEW.orb4_conjSub_le_of_mem htS hR₂S
  have hne₃₄ : R₃ ≠ R₄ := by
    rw [hR₃def, hR₄def]
    exact fun h => hne₁₂ (conjSub_injective t h)
  have hq₁ : IsQuatSub R₁ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR₁
  have hq₂ : IsQuatSub R₂ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR₂
  have hq₃ : IsQuatSub R₃ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR₃Ω
  have hq₄ : IsQuatSub R₄ := Sec6Gen.isQuatSub_of_mem_RSet hΩ hR₄Ω
  have hK₃Ω : conjSub t K₁ ∈ Ω := hΩ.conjInvariant t K₁ hK₁
  have hK₄Ω : conjSub t K₂ ∈ Ω := hΩ.conjInvariant t K₂ hK₂
  have hR₃K₃ : R₃ ≤ conjSub t K₁ := hR₃def ▸ conjSub_mono hR₁K₁
  have hR₄K₄ : R₄ ≤ conjSub t K₂ := hR₄def ▸ conjSub_mono hR₂K₂
  have hzK₃ : IsUniqueInvolution (conjSub t K₁) zt := hztdef ▸ hzK₁.conj t
  have hzK₄ : IsUniqueInvolution (conjSub t K₂) zt := hztdef ▸ hzK₂.conj t
  have C12 := TwinThmEW.orb4_rset_commutes hΩ S hR₁ hR₂ hR₁S hR₂S hne₁₂
  have C13 := TwinThmEW.orb4_rset_commutes hΩ S hR₁ hR₃Ω hR₁S hR₃S hne₁₃
  have C14 := TwinThmEW.orb4_rset_commutes hΩ S hR₁ hR₄Ω hR₁S hR₄S hne₁₄
  have C23 := TwinThmEW.orb4_rset_commutes hΩ S hR₂ hR₃Ω hR₂S hR₃S hne₂₃
  have C24 := TwinThmEW.orb4_rset_commutes hΩ S hR₂ hR₄Ω hR₂S hR₄S hne₂₄
  have C34 := TwinThmEW.orb4_rset_commutes hΩ S hR₃Ω hR₄Ω hR₃S hR₄S hne₃₄
  have hu₃ : u₃ ∈ R₃ := hu₃def ▸ hR₃def ▸ conj_mem_conjSub hu
  have hu₄ : u₄ ∈ R₄ := hu₄def ▸ hR₄def ▸ conj_mem_conjSub hu'
  have hu₃W : u₃ ∈ W := by
    have := conj_mem_conjSub (n := t) huW
    rw [hWn t htS] at this
    rwa [hu₃def]
  have hu₄W : u₄ ∈ W := by
    have := conj_mem_conjSub (n := t) hu'W
    rw [hWn t htS] at this
    rwa [hu₄def]
  have hu₃4 : orderOf u₃ = 4 := by rw [hu₃def, orderOf_conj_mul_inv_eq]; exact hu4
  have hu₄4 : orderOf u₄ = 4 := by rw [hu₄def, orderOf_conj_mul_inv_eq]; exact hu'4
  have hzt₃ : u₃ * u₃ = zt := by rw [hu₃def, hztdef, ← hz]; group
  have hzt₄ : u₄ * u₄ = zt := by rw [hu₄def, hztdef, ← hz']; group
  have hz2 : z * z = 1 := TwinThmEW.orb4_four_pow_eq hu4 hz
  have hzt2 : zt * zt = 1 := TwinThmEW.orb4_four_pow_eq hu₃4 hzt₃
  have hz1 : z ≠ 1 := by rw [← hz]; exact TwinThmEW.orb4_sq_ne_one_of_orderOf_eq_four hu4
  have hc12 : Commute u u' := C12 u hu u' hu'
  have hc13 : Commute u u₃ := C13 u hu u₃ hu₃
  have hc14 : Commute u u₄ := C14 u hu u₄ hu₄
  have hc23 : Commute u' u₃ := C23 u' hu' u₃ hu₃
  have hc24 : Commute u' u₄ := C24 u' hu' u₄ hu₄
  have hc34 : Commute u₃ u₄ := C34 u₃ hu₃ u₄ hu₄
  have hsupp : ∀ R ∈ RSet Ω, R ≤ (S : Subgroup G) →
      (R ∈ ({R₁, R₂, R₃, R₄} : Set (Subgroup G)) ↔
        ¬ ∀ r ∈ R, r * ((u * u₃) * (u' * u₄)⁻¹) = ((u * u₃) * (u' * u₄)⁻¹) * r) := by
    intro R hR hRS
    constructor
    · rintro (h | h | h | h)
      · rw [h]
        have h1 := orb4_not_all_commute' hq₁ (v := u) (a := 1)
          (b := u₃ * (u' * u₄)⁻¹) hu hu4 (fun r _ => by simp)
          (fun r hr => (((show Commute r u₃ from C13 r hr u₃ hu₃).mul_right
            (((show Commute r u' from C12 r hr u' hu').mul_right
              (show Commute r u₄ from C14 r hr u₄ hu₄)).inv_right))).eq)
        have e1 : (u * u₃) * (u' * u₄)⁻¹ = 1 * u * (u₃ * (u' * u₄)⁻¹) := by group
        rw [e1]
        exact h1
      · rw [h]
        have h1 := orb4_not_all_commute' hq₂ (v := u'⁻¹) (a := u * u₃ * u₄⁻¹) (b := 1)
          (R₂.inv_mem hu') (by rw [orderOf_inv]; exact hu'4)
          (fun r hr => ((((show Commute r u from (C12 u hu r hr).symm).mul_right
            (show Commute r u₃ from C23 r hr u₃ hu₃)).mul_right
              (show Commute r u₄ from C24 r hr u₄ hu₄).inv_right)).eq)
          (fun r _ => by simp)
        have e1 : (u * u₃) * (u' * u₄)⁻¹ = (u * u₃ * u₄⁻¹) * u'⁻¹ * 1 := by group
        rw [e1]
        exact h1
      · rw [h]
        exact orb4_not_all_commute' hq₃ (v := u₃) (a := u) (b := (u' * u₄)⁻¹) hu₃ hu₃4
          (fun r hr => (C13 u hu r hr).symm)
          (fun r hr => (((show Commute r u' from (C23 u' hu' r hr).symm).mul_right
            (show Commute r u₄ from C34 r hr u₄ hu₄)).inv_right).eq)
      · rw [h]
        have h1 := orb4_not_all_commute' hq₄ (v := u₄⁻¹) (a := u * u₃) (b := u'⁻¹)
          (R₄.inv_mem hu₄) (by rw [orderOf_inv]; exact hu₄4)
          (fun r hr => (((show Commute r u from (C14 u hu r hr).symm).mul_right
            (show Commute r u₃ from (C34 u₃ hu₃ r hr).symm)).eq))
          (fun r hr => ((show Commute r u' from (C24 u' hu' r hr).symm).inv_right).eq)
        have e1 : (u * u₃) * (u' * u₄)⁻¹ = (u * u₃) * u₄⁻¹ * u'⁻¹ := by group
        rw [e1]
        exact h1
    · intro hnot
      by_contra hR'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hR'
      obtain ⟨h1, h2, h3, h4⟩ := hR'
      apply hnot
      have k1 := TwinThmEW.orb4_rset_commutes hΩ S hR hR₁ hRS hR₁S h1
      have k2 := TwinThmEW.orb4_rset_commutes hΩ S hR hR₂ hRS hR₂S h2
      have k3 := TwinThmEW.orb4_rset_commutes hΩ S hR hR₃Ω hRS hR₃S h3
      have k4 := TwinThmEW.orb4_rset_commutes hΩ S hR hR₄Ω hRS hR₄S h4
      intro r hr
      exact (((show Commute r u from k1 r hr u hu).mul_right (show Commute r u₃ from k3 r hr u₃ hu₃)).mul_right
        (((show Commute r u' from k2 r hr u' hu').mul_right
          (show Commute r u₄ from k4 r hr u₄ hu₄)).inv_right)).eq
  have hP : ∀ c ∈ (S : Subgroup G), c * ((u * u₃) * (u' * u₄)⁻¹) = ((u * u₃) * (u' * u₄)⁻¹) * c →
      conjSub c ((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) = (R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄) := by
    intro c hc hcd
    have := TwinThmEW.orb4_conjSub_sSup_eq (𝒮 := {R₁, R₂, R₃, R₄}) (d := (u * u₃) * (u' * u₄)⁻¹) hΩ
      (S := (S : Subgroup G))
      (by
        rintro R (h | h | h | h) <;> rw [h]
        · exact ⟨hR₁, hR₁S⟩
        · exact ⟨hR₂, hR₂S⟩
        · exact ⟨hR₃Ω, hR₃S⟩
        · exact ⟨hR₄Ω, hR₄S⟩) hsupp hc hcd
    have e : sSup ({R₁, R₂, R₃, R₄} : Set (Subgroup G)) = (R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄) := by
      simp [sSup_insert, sup_assoc]
    rwa [e] at this
  have hPP' : Commutes (R₁ ⊔ R₂) (R₃ ⊔ R₄) :=
    TwinThmEW.orb4_commutes_sup_right (TwinThmEW.orb4_commutes_sup_left C13 C23) (TwinThmEW.orb4_commutes_sup_left C14 C24)
  have hinter : ∀ v, v ∈ R₁ ⊔ R₂ → v ∈ R₃ ⊔ R₄ → v = 1 := by
    intro v hv1 hv2
    have hva : ∀ r ∈ R₁, r * v = v * r := fun r hr =>
      hPP' r (Subgroup.mem_sup_left hr) v hv2
    have hvb : ∀ r ∈ R₂, r * v = v * r := fun r hr =>
      hPP' r (Subgroup.mem_sup_right hr) v hv2
    have hv3 : ∀ r ∈ R₃, r * v = v * r := fun r hr =>
      (hPP' v hv1 r (Subgroup.mem_sup_left hr)).symm
    have hv4 : ∀ r ∈ R₄, r * v = v * r := fun r hr =>
      (hPP' v hv1 r (Subgroup.mem_sup_right hr)).symm
    rcases orb4_center_pair' C12 hq₁ hq₂ hR₁K₁ hR₂K₂ hzK₁ hzK₂ hz2 hv1 hva hvb with h | h
    · exact h
    · rcases orb4_center_pair' C34 hq₃ hq₄ hR₃K₃ hR₄K₄ hzK₃ hzK₄ hzt2 hv2 hv3 hv4 with h' | h'
      · exact h'
      · exact absurd (h'.symm.trans h) hzt
  have hconjP : ∀ x ∈ R₃ ⊔ R₄, t * x * t⁻¹ ∈ R₁ ⊔ R₂ := by
    intro x hx
    have h3 : conjSub t R₃ = R₁ := by rw [hR₃def, ← conjSub_mul, ht2, conjSub_one]
    have h4 : conjSub t R₄ = R₂ := by rw [hR₄def, ← conjSub_mul, ht2, conjSub_one]
    have := conj_mem_conjSub (n := t) hx
    rwa [TwinThmEW.orb4_conjSub_sup, h3, h4] at this
  have hconjP' : ∀ x ∈ R₁ ⊔ R₂, t * x * t⁻¹ ∈ R₃ ⊔ R₄ := by
    intro x hx
    have := conj_mem_conjSub (n := t) hx
    rwa [TwinThmEW.orb4_conjSub_sup, ← hR₃def, ← hR₄def] at this
  have hd₁ : z * zt ∈ ((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) ⊓ W := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ ?_ ?_, W.mul_mem ?_ ?_⟩
    · rw [← hz]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (R₁.mul_mem hu hu))
    · rw [← hzt₃]
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (R₃.mul_mem hu₃ hu₃))
    · rw [← hz]; exact W.mul_mem huW huW
    · rw [← hzt₃]; exact W.mul_mem hu₃W hu₃W
  have hd₂ : (u * u₃) * (u' * u₄)⁻¹ ∈ ((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) ⊓ W := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_)
      (Subgroup.inv_mem _ (Subgroup.mul_mem _ ?_ ?_)), W.mul_mem (W.mul_mem huW hu₃W)
        (W.inv_mem (W.mul_mem hu'W hu₄W))⟩
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hu)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left hu₃)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hu')
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right hu₄)
  have hczt : Commute z zt := by
    rw [← hz, ← hzt₃]
    exact (hc13.mul_right hc13).mul_left (hc13.mul_right hc13)
  have hdd : (z * zt) * (z * zt) = 1 := by
    calc (z * zt) * (z * zt) = z * (zt * z) * zt := by group
      _ = z * (z * zt) * zt := by rw [← hczt.eq]
      _ = (z * z) * (zt * zt) := by group
      _ = 1 := by rw [hz2, hzt2, one_mul]
  have hdN : (z * zt) * ((u * u₃) * (u' * u₄)⁻¹) = (u * u') * (u₃ * u₄) := by
    have h := TwinThmEW.orb4_comm4_id hc12 hc14 hc23 hc24 hc34 hc13
    rw [hz', hzt₄] at h
    calc (z * zt) * ((u * u₃) * (u' * u₄)⁻¹) = ((z * zt) * (u * u₃)) * (u' * u₄)⁻¹ := by group
      _ = (((u * u') * (u₃ * u₄)) * (u' * u₄)) * (u' * u₄)⁻¹ := by rw [h]
      _ = (u * u') * (u₃ * u₄) := by group
  have hczt' : Commute (u * u') zt := by
    rw [← hzt₃]
    exact (hc13.mul_right hc13).mul_left (hc23.mul_right hc23)
  refine ⟨((R₁ ⊔ R₂) ⊔ (R₃ ⊔ R₄)) ⊓ W, hd₁, hd₂, ?_, ?_⟩
  · intro c hc _ hcd
    rw [TwinThmEW.orb4_conjSub_inf, hP c hc hcd, hWn c hc]
  · intro w hw hww hwt
    obtain ⟨hwP, hwW⟩ := Subgroup.mem_inf.mp hw
    obtain ⟨a, ha, a', ha', rfl⟩ := exists_mul_of_mem_sup_of_commutes hPP' hwP
    have hp : t * a' * t⁻¹ ∈ R₁ ⊔ R₂ := hconjP a' ha'
    have hq : t * a * t⁻¹ ∈ R₃ ⊔ R₄ := hconjP' a ha
    have e1 : (t * a * t⁻¹) * (t * a' * t⁻¹) = a * a' := by
      calc (t * a * t⁻¹) * (t * a' * t⁻¹) = t * (a * a') * t⁻¹ := by group
        _ = a * a' := by rw [mul_inv_eq_iff_eq_mul]; exact hwt.symm
    have hcomm_pq : (t * a' * t⁻¹) * (t * a * t⁻¹) = (t * a * t⁻¹) * (t * a' * t⁻¹) :=
      hPP' _ hp _ hq
    have e2 : a * a' = (t * a' * t⁻¹) * (t * a * t⁻¹) := by rw [hcomm_pq, e1]
    have e3 : (t * a' * t⁻¹)⁻¹ * a = (t * a * t⁻¹) * a'⁻¹ := by
      calc (t * a' * t⁻¹)⁻¹ * a = (t * a' * t⁻¹)⁻¹ * (a * a') * a'⁻¹ := by group
        _ = (t * a' * t⁻¹)⁻¹ * ((t * a' * t⁻¹) * (t * a * t⁻¹)) * a'⁻¹ := by rw [← e2]
        _ = (t * a * t⁻¹) * a'⁻¹ := by group
    have e4 : (t * a' * t⁻¹)⁻¹ * a = 1 :=
      hinter _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hp) ha)
        (by rw [e3]; exact Subgroup.mul_mem _ hq (Subgroup.inv_mem _ ha'))
    have hap : a = t * a' * t⁻¹ := (inv_mul_eq_one.mp e4).symm
    have ha'q : a' = t * a * t⁻¹ := by
      rw [hap]
      calc a' = (t * t) * a' * (t * t)⁻¹ := by rw [ht2]; group
        _ = t * (t * a' * t⁻¹) * t⁻¹ := by group
    have haa : a * a = 1 := by
      have h1 : (a * a) * (a' * a') = 1 := by
        calc (a * a) * (a' * a') = a * (a * a') * a' := by group
          _ = a * (a' * a) * a' := by rw [hPP' a ha a' ha']
          _ = (a * a') * (a * a') := by group
          _ = 1 := hww
      have h2 : a * a = (a' * a')⁻¹ := eq_inv_of_mul_eq_one_left h1
      exact hinter _ (Subgroup.mul_mem _ ha ha)
        (by rw [h2]; exact Subgroup.inv_mem _ (Subgroup.mul_mem _ ha' ha'))
    have hau : a * u = u * a := by
      have h1 := hWab _ hwW u huW
      have h2 : u * a' = a' * u := hPP' u (Subgroup.mem_sup_left hu) a' ha'
      have : (a * u) * a' = (u * a) * a' := by
        calc (a * u) * a' = a * (u * a') := by group
          _ = a * (a' * u) := by rw [h2]
          _ = a * a' * u := by group
          _ = u * (a * a') := h1
          _ = (u * a) * a' := by group
      exact mul_right_cancel this
    have hau' : a * u' = u' * a := by
      have h1 := hWab _ hwW u' hu'W
      have h2 : u' * a' = a' * u' := hPP' u' (Subgroup.mem_sup_right hu') a' ha'
      have : (a * u') * a' = (u' * a) * a' := by
        calc (a * u') * a' = a * (u' * a') := by group
          _ = a * (a' * u') := by rw [h2]
          _ = a * a' * u' := by group
          _ = u' * (a * a') := h1
          _ = (u' * a) * a' := by group
      exact mul_right_cancel this
    rw [ha'q]
    rcases orb4_commute_AD hΩ S hK₁ hK₂ hK₁₂ hR₁ hR₂ hR₁K₁ hR₂K₂ hR₁S hR₂S hzK₁ hzK₂ hu hu4 hu' hu'4 hz hz' ha hau hau' haa
      with h | h | h | h
    · left
      rw [h]
      simp
    · right; left
      rw [h, ← hztdef]
    · right; right; right
      rw [h, hdN]
      have : t * (u * u') * t⁻¹ = u₃ * u₄ := by rw [hu₃def, hu₄def]; group
      rw [this]
    · right; right; left
      rw [h]
      have h1 : t * (z * (u * u')) * t⁻¹ = zt * (u₃ * u₄) := by
        rw [hztdef, hu₃def, hu₄def]; group
      rw [h1]
      calc z * (u * u') * (zt * (u₃ * u₄)) = z * ((u * u') * zt) * (u₃ * u₄) := by group
        _ = z * (zt * (u * u')) * (u₃ * u₄) := by rw [hczt'.eq]
        _ = (z * zt) * ((u * u') * (u₃ * u₄)) := by group
        _ = (z * zt) * ((z * zt) * ((u * u₃) * (u' * u₄)⁻¹)) := by rw [hdN]
        _ = ((z * zt) * (z * zt)) * ((u * u₃) * (u' * u₄)⁻¹) := by group
        _ = (u * u₃) * (u' * u₄)⁻¹ := by rw [hdd, one_mul]

end Orb3

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4

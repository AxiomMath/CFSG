module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma49E
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma48

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open scoped Pointwise

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

namespace Standing

namespace Setup42

variable {h : Standing t L p f} {S : Subgroup X} {hS : IsSylowOf 2 S (centralizer ({t} : Set X))}
  {w z : X}

theorem S_le_normalizer_T [Finite X] (hσ : Setup42 h hS w z) :
    S ≤ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
  fun _ hs => hσ.normalizer_S_le_normalizer_T (Subgroup.le_normalizer hs)

theorem ne_of_isSylowOf_normalizer [Finite X] (hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) : S ≠ V := by
  rintro rfl
  have hnot := (h.lemma41_of_lift hS hσ.lift hσ.gen3).2.2.2.2.2.2.2.2.2
  obtain ⟨Y, hY, hSY⟩ := exists_isSylowOf_ge hS.isPGroup (le_top : S ≤ ⊤)
  have hne : S ≠ Y := fun heq => hnot (heq ▸ hY)
  have hY2 : IsPGroup 2 Y := hY.isPGroup
  have : Group.IsNilpotent ↥Y := hY2.isNilpotent
  have hlt : S.subgroupOf Y < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hSY fun y hy => ?_)
    have : (⟨y, hy⟩ : ↥Y) ∈ S.subgroupOf Y := htop ▸ mem_top _
    exact this
  obtain ⟨y, hyN, hyS⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  have hyNS : (y : X) ∈ normalizer (S : Set X) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (mem_normalizer_iff.mp hyN ⟨x, hSY hx⟩).mp hx
    · intro hx
      have hxY : x ∈ Y := by
        have h1 : (y : X) * x * (y : X)⁻¹ ∈ Y := hSY hx
        have h2 := Y.mul_mem (Y.mul_mem (Y.inv_mem y.2) h1) y.2
        simpa [mul_assoc] using h2
      exact (mem_normalizer_iff.mp hyN ⟨x, hxY⟩).mpr hx
  have hP2 : IsPGroup 2 (S ⊔ zpowers (y : X) : Subgroup X) :=
    hY2.to_le (sup_le hSY (zpowers_le.mpr y.2))
  have hPN : S ⊔ zpowers (y : X) ≤
      normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X) :=
    sup_le hσ.S_le_normalizer_T (zpowers_le.mpr (hσ.normalizer_S_le_normalizer_T hyNS))
  have heq := hV.eq_of_le le_sup_left hPN hP2
  have : (y : X) ∈ S := by
    rw [← heq]
    exact mem_sup_right (mem_zpowers _)
  exact hyS this

theorem inf_centralizer_t [Finite X] (_hσ : Setup42 h hS w z) {V : Subgroup X}
    (hV : IsSylowOf 2 V (normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X)))
    (hSV : S ≤ V) : V ⊓ centralizer ({t} : Set X) = S :=
  hS.eq_of_le (le_inf hSV hS.le) inf_le_right (hV.isPGroup.to_le inf_le_left)

theorem sq_mem_centralizer_X [Finite X] (hσ : Setup42 h hS w z) {m : X}
    (hmN : m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
    (hmt : m ∈ centralizer ({t} : Set X)) :
    m ^ 2 ∈ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
  have hmX := hσ.normalizer_T_le_normalizer_X hmN
  have hmz : m * z * m⁻¹ = z := hσ.conj_z_of_mem_normalizer_T hmN
  have hmt' : m * t * m⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hmt]
    group
  have huX : w ^ (orderOf w / 2) ∈ closure {t, w ^ (orderOf w / 2), z} :=
    subset_closure (by simp)
  have hmu : m * w ^ (orderOf w / 2) * m⁻¹ ∈ closure {t, w ^ (orderOf w / 2), z} :=
    (mem_normalizer_iff.mp hmX _).mp huX
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := hσ.mem_X hmu
  have hma : m * a * m⁻¹ = a := by
    rcases ha with ha | ha <;> rw [ha]
    · group
    · exact hmt'
  have hmc : m * c * m⁻¹ = c := by
    rcases hc with hc | hc <;> rw [hc]
    · group
    · exact hmz
  have hb' : b = w ^ (orderOf w / 2) := by
    rcases hb with hb | hb
    · exfalso
      rw [hb, mul_one] at habc
      apply hσ.rho_u_not_mem_inn
      have hu : w ^ (orderOf w / 2) = a * c := by
        calc w ^ (orderOf w / 2) = m⁻¹ * (m * w ^ (orderOf w / 2) * m⁻¹) * m := by group
          _ = m⁻¹ * (a * c) * m := by rw [habc]
          _ = (m⁻¹ * a * m) * (m⁻¹ * c * m) := by group
          _ = a * c := by
            rw [show m⁻¹ * a * m = a by
              calc m⁻¹ * a * m = m⁻¹ * (m * a * m⁻¹) * m := by rw [hma]
                _ = a := by group,
              show m⁻¹ * c * m = c by
              calc m⁻¹ * c * m = m⁻¹ * (m * c * m⁻¹) * m := by rw [hmc]
                _ = c := by group]
      have haL : a ∈ zpowers t ⊔ L := by
        rcases ha with ha | ha <;> rw [ha]
        · exact one_mem _
        · exact mem_sup_left (mem_zpowers t)
      have hcL : c ∈ zpowers t ⊔ L := by
        rcases hc with hc | hc <;> rw [hc]
        · exact one_mem _
        · exact mem_sup_right hσ.z_mem.2
      have := h.rho_mem_innAut (mul_mem haL hcL) (hS.le (hu ▸ hσ.u_mem))
      convert this using 2
      exact Subtype.ext hu
    · exact hb
  rw [hb'] at habc
  have haX : a ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rcases ha with ha | ha <;> rw [ha]
    · exact one_mem _
    · exact subset_closure (by simp)
  have hcX : c ∈ closure {t, w ^ (orderOf w / 2), z} := by
    rcases hc with hc | hc <;> rw [hc]
    · exact one_mem _
    · exact subset_closure (by simp)
  have ha2 : a * a = 1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X haX
  have hc2 : c * c = 1 := by
    rw [← sq]
    exact hσ.sq_eq_one_of_mem_X hcX
  have hm2u : m ^ 2 * w ^ (orderOf w / 2) * (m ^ 2)⁻¹ = w ^ (orderOf w / 2) := by
    calc m ^ 2 * w ^ (orderOf w / 2) * (m ^ 2)⁻¹ =
          m * (m * w ^ (orderOf w / 2) * m⁻¹) * m⁻¹ := by rw [sq]; group
      _ = m * (a * w ^ (orderOf w / 2) * c) * m⁻¹ := by rw [habc]
      _ = (m * a * m⁻¹) * (m * w ^ (orderOf w / 2) * m⁻¹) * (m * c * m⁻¹) := by group
      _ = a * (a * w ^ (orderOf w / 2) * c) * c := by rw [hma, hmc, habc]
      _ = (a * a) * w ^ (orderOf w / 2) * (c * c) := by group
      _ = w ^ (orderOf w / 2) := by rw [ha2, hc2]; group
  have hm2t : m ^ 2 * t * (m ^ 2)⁻¹ = t := by
    calc m ^ 2 * t * (m ^ 2)⁻¹ = m * (m * t * m⁻¹) * m⁻¹ := by rw [sq]; group
      _ = t := by rw [hmt', hmt']
  have hm2z : m ^ 2 * z * (m ^ 2)⁻¹ = z := by
    calc m ^ 2 * z * (m ^ 2)⁻¹ = m * (m * z * m⁻¹) * m⁻¹ := by rw [sq]; group
      _ = z := by rw [hmz, hmz]
  have hgen : closure {t, w ^ (orderOf w / 2), z} ≤ centralizer ({m ^ 2} : Set X) := by
    rw [closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    rcases hx with hx | hx | hx <;> rw [hx]
    · calc t * m ^ 2 = (m ^ 2 * t * (m ^ 2)⁻¹) * m ^ 2 := by rw [hm2t]
        _ = m ^ 2 * t := by group
    · calc w ^ (orderOf w / 2) * m ^ 2 =
          (m ^ 2 * w ^ (orderOf w / 2) * (m ^ 2)⁻¹) * m ^ 2 := by rw [hm2u]
        _ = m ^ 2 * w ^ (orderOf w / 2) := by group
    · calc z * m ^ 2 = (m ^ 2 * z * (m ^ 2)⁻¹) * m ^ 2 := by rw [hm2z]
        _ = m ^ 2 * z := by group
  exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hgen hx)

theorem mem_centralizer_X_of_odd [Finite X] (hσ : Setup42 h hS w z) {m : X}
    (hmN : m ∈ normalizer ((zpowers t ⊔ (S ⊓ L) ⊔ zpowers w : Subgroup X) : Set X))
    (hmt : m ∈ centralizer ({t} : Set X)) (hodd : Odd (orderOf m)) :
    m ∈ centralizer ((closure {t, w ^ (orderOf w / 2), z} : Subgroup X) : Set X) := by
  have h2 := hσ.sq_mem_centralizer_X hmN hmt
  obtain ⟨k, hk⟩ := hodd
  have : m = (m ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf m + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact pow_mem h2 _

end Setup42

end Standing

end CFSG.ComponentClassification.HarrisLit

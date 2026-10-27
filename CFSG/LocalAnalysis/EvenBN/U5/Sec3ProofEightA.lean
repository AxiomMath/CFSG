module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.EvenBN.U5.CaseBBasic
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Four

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem Hyp.sec38a1_inv_t (hd : d.Hyp) : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right hd.t_mul_t

theorem Hyp.sec38a1_t_mem_normalizer_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.t ∈ normalizer (d.E : Set G) :=
  hd.T_le_normalizer_E hGMS hd.t_mem_T

theorem Hyp.sec38a1_mem_sup (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.E ⊔ zpowers d.t) : x ∈ d.E ∨ ∃ e ∈ d.E, x = e * d.t := by
  have hN : zpowers d.t ≤ normalizer (d.E : Set G) :=
    zpowers_le.2 (hd.sec38a1_t_mem_normalizer_E hGMS)
  obtain ⟨e, he, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hN hx
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  rcases hd.zpow_t_eq k with h1 | h1 <;> rw [h1]
  · left
    rw [mul_one]
    exact he
  · exact Or.inr ⟨e, he, rfl⟩

theorem Hyp.sec38a1_mem_VA (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {e : G} (he : e ∈ d.E) (hc : e⁻¹ * d.t * e * d.t ∈ d.V) : e ∈ d.V ⊔ d.A₂ := by
  obtain ⟨ψ, -, hker, hψ, -⟩ := hd.exists_E_hom hGMS
  have h1 : ψ ⟨e, he⟩ = QuotientGroup.mk (1 : d.A₂) := hψ ⟨e, he⟩ 1 _ hc (by simp)
  have h2 : (⟨e, he⟩ : d.E) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, h1]
    rfl
  rw [hker] at h2
  exact h2

theorem Hyp.sec38a1_not_E_le_VA (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ¬ d.E ≤ d.V ⊔ d.A₂ := fun hle => by
  have h1 := Subgroup.card_le_of_le hle
  rw [hd.card_E hGMS, hd.card_V_sup_A₂ hGMS] at h1
  have h4 := hd.four_le
  have : (2 ^ f) ^ 8 < (2 ^ f) ^ 14 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem Hyp.sec38a1_exists_cr_not_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : ∃ e ∈ d.E, e⁻¹ * d.t * e * d.t ∉ d.V := by
  by_contra hcon
  exact hd.sec38a1_not_E_le_VA hGMS fun e he => hd.sec38a1_mem_VA hGMS he (by
    by_contra hne
    exact hcon ⟨e, he, hne⟩)

theorem Hyp.sec38a1_cr_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {e₀ e' : G} (he₀ : e₀ ∈ d.E) (he' : e' ∈ d.E) (hc : ⁅e₀ * d.t, e'⁆ ∈ d.V) :
    e'⁻¹ * d.t * e' * d.t ∈ d.V := by
  have hE := hd.elemAbMod_V_E hGMS
  have huE : d.t * e' * d.t⁻¹ ∈ d.E :=
    (mem_normalizer_iff.1 (hd.sec38a1_t_mem_normalizer_E hGMS) e').1 he'
  have h1 : ⁅e₀, d.t * e' * d.t⁻¹⁆ ∈ d.V := hE.2 e₀ he₀ _ huE
  have h2 : ⁅e'⁻¹, d.t * e' * d.t⁻¹⁆ ∈ d.V := hE.2 _ (inv_mem he') _ huE
  have e1 : e'⁻¹ * d.t * e' * d.t⁻¹ =
      ⁅e'⁻¹, d.t * e' * d.t⁻¹⁆ * (⁅e₀, d.t * e' * d.t⁻¹⁆⁻¹ * ⁅e₀ * d.t, e'⁆) := by
    simp only [commutatorElement_def]
    group
  have : e'⁻¹ * d.t * e' * d.t⁻¹ ∈ d.V := by
    rw [e1]
    exact mul_mem h2 (mul_mem (inv_mem h1) hc)
  rwa [hd.sec38a1_inv_t] at this

theorem Hyp.sec38a1_V_comm (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {v y : G} (hv : v ∈ d.V) (hy : y ∈ d.E) : y * v = v * y := by
  have : v ∈ CFSG.centerIn d.E := by
    rw [hd.centerIn_E hGMS]
    exact hv
  exact mem_centralizer_iff.1 this.2 y hy

theorem Hyp.sec38a1_center_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {z : G} (hz : z ∈ CFSG.centerIn (d.E ⊔ zpowers d.t)) : z ∈ d.V := by
  obtain ⟨hzX, hzc⟩ := hz
  have hzc' := mem_centralizer_iff.1 hzc
  rcases hd.sec38a1_mem_sup hGMS hzX with hzE | ⟨e₀, he₀, rfl⟩
  · rw [← hd.centerIn_E hGMS]
    exact ⟨hzE, mem_centralizer_iff.2 fun y hy => hzc' y (mem_sup_left hy)⟩
  · exfalso
    obtain ⟨e', he', hne⟩ := hd.sec38a1_exists_cr_not_mem_V hGMS
    refine hne (hd.sec38a1_cr_mem_V hGMS he₀ he' ?_)
    have : ⁅e₀ * d.t, e'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (hzc' e' (mem_sup_left he')).symm
    rw [this]
    exact one_mem _

omit [Finite G] in
theorem sec38a1_comm_mul {a κ v : G} (hκ : a * κ = κ * a) (hv : a * v = v * a) :
    κ * v * a = a * (κ * v) := by
  rw [mul_assoc, ← hv, ← mul_assoc, ← hκ, mul_assoc]

theorem Hyp.sec38a1_mem_Zp (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {a : G} (ha : a ∈ d.A₂)
    (hc : ∀ e ∈ d.E, ⁅a, e⁆ ∈ CFSG.centerIn (d.E ⊔ zpowers d.t)) : a ∈ d.Zp := by
  have hZA : CFSG.centerIn d.A₂ = d.Zp := d.sec2_2_three.2.2.2.1
  rw [← hZA]
  refine ⟨ha, mem_centralizer_iff.2 fun w hw => ?_⟩
  have haE : a ∈ d.E := hd.A₂_le_E hGMS ha
  have hat : a * d.t * a⁻¹ = d.t := by
    rw [← hd.t_comm_A₂ ha, mul_inv_cancel_right]
  obtain ⟨e, he, hv⟩ := hd.exists_E_cr hGMS (mem_sup_right hw)
  have hκ : a * (e⁻¹ * d.t * e * d.t) = (e⁻¹ * d.t * e * d.t) * a := by
    have hz := mem_centralizer_iff.1 (hc e he).2 d.t (mem_sup_right (mem_zpowers _))
    set z := ⁅a, e⁆ with hzdef
    have hae : a * e * a⁻¹ = z * e := by rw [hzdef, commutatorElement_def]; group
    have hz' : z⁻¹ * d.t * z = d.t := by
      rw [mul_assoc, hz, ← mul_assoc, inv_mul_cancel, one_mul]
    have h1 : a * (e⁻¹ * d.t * e * d.t⁻¹) * a⁻¹ = e⁻¹ * d.t * e * d.t⁻¹ := by
      calc a * (e⁻¹ * d.t * e * d.t⁻¹) * a⁻¹
          = (a * e * a⁻¹)⁻¹ * (a * d.t * a⁻¹) * (a * e * a⁻¹) * (a * d.t * a⁻¹)⁻¹ := by group
        _ = (z * e)⁻¹ * d.t * (z * e) * d.t⁻¹ := by rw [hae, hat]
        _ = e⁻¹ * (z⁻¹ * d.t * z) * e * d.t⁻¹ := by group
        _ = e⁻¹ * d.t * e * d.t⁻¹ := by rw [hz']
    rw [hd.sec38a1_inv_t] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1)
  have hv0 : a * ((e⁻¹ * d.t * e * d.t)⁻¹ * w) = ((e⁻¹ * d.t * e * d.t)⁻¹ * w) * a :=
    hd.sec38a1_V_comm hGMS hv haE
  have hw : w = (e⁻¹ * d.t * e * d.t) * ((e⁻¹ * d.t * e * d.t)⁻¹ * w) := by group
  have key := sec38a1_comm_mul hκ hv0
  rw [← hw] at key
  exact key

theorem Hyp.sec38a1_Z₂_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x : G}
    (hx : x ∈ (Subgroup.upperCentralSeries ↥(d.E ⊔ zpowers d.t) 2).map
      (d.E ⊔ zpowers d.t).subtype) : x ∈ d.V := by
  obtain ⟨hxX, hxc⟩ := mem_map_upperCentralSeries_two.1 hx
  have hxE : x ∈ d.E := by
    rcases hd.sec38a1_mem_sup hGMS hxX with h1 | ⟨e₀, he₀, rfl⟩
    · exact h1
    · exfalso
      obtain ⟨e', he', hne⟩ := hd.sec38a1_exists_cr_not_mem_V hGMS
      exact hne (hd.sec38a1_cr_mem_V hGMS he₀ he'
        (hd.sec38a1_center_le hGMS (hxc e' (mem_sup_left he'))))
  have hxVA : x ∈ d.V ⊔ d.A₂ := by
    have h1 := hd.sec38a1_center_le hGMS (hxc d.t (mem_sup_right (mem_zpowers _)))
    have h2 : (x⁻¹)⁻¹ * d.t * x⁻¹ * d.t ∈ d.V := by
      have e1 : (x⁻¹)⁻¹ * d.t * x⁻¹ * d.t = ⁅x, d.t⁆ := by
        rw [commutatorElement_def, hd.sec38a1_inv_t]
        group
      rw [e1]
      exact h1
    have := inv_mem (hd.sec38a1_mem_VA hGMS (inv_mem hxE) h2)
    rwa [inv_inv] at this
  obtain ⟨v, hv, a, ha, rfl⟩ := hd.exists_mul_of_mem_VA hxVA
  have haE : a ∈ d.E := hd.A₂_le_E hGMS ha
  have haZ : a ∈ d.Zp := by
    refine hd.sec38a1_mem_Zp hGMS ha fun e he => ?_
    have e1 : ⁅v * a, e⁆ = ⁅a, e⁆ := by
      have hc : v * (a * e * a⁻¹) = (a * e * a⁻¹) * v := by
        have := hd.sec38a1_V_comm hGMS hv (mul_mem (mul_mem haE he) (inv_mem haE))
        exact this.symm
      simp only [commutatorElement_def]
      calc v * a * e * (v * a)⁻¹ * e⁻¹ = (v * (a * e * a⁻¹) * v⁻¹) * e⁻¹ := by group
        _ = a * e * a⁻¹ * e⁻¹ := by rw [hc]; group
    rw [← e1]
    exact hxc e (mem_sup_left he)
  exact mul_mem hv (hd.Zp_le_V haZ)

theorem Hyp.sec38a1_commutator_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {v : G} (hv : v ∈ d.V) : ⁅v, d.t⁆ ∈ d.V := by
  have htV : d.t ∈ normalizer (d.V : Set G) :=
    hd.normalizer_ZtP_le_normalizer_V hGMS (le_normalizer hd.t_mem_ZtP)
  have := (mem_normalizer_iff.1 htV v⁻¹).1 (inv_mem hv)
  rw [commutatorElement_def]
  have e : v * d.t * v⁻¹ * d.t⁻¹ = v * (d.t * v⁻¹ * d.t⁻¹) := by group
  rw [e]
  exact mul_mem hv this

theorem Hyp.sec38a1_comm_t (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {v : G} (hv : v ∈ d.V) : d.t * ⁅v, d.t⁆ = ⁅v, d.t⁆ * d.t := by
  have hκ2 : ⁅v, d.t⁆ * ⁅v, d.t⁆ = 1 :=
    hd.mul_self_eq_one_of_mem_V hGMS (hd.sec38a1_commutator_mem_V hGMS hv)
  have htt := hd.t_mul_t
  have ht := hd.sec38a1_inv_t
  have e1 : d.t * ⁅v, d.t⁆ * d.t = d.t * v * d.t * v⁻¹ * (d.t * d.t) := by
    rw [commutatorElement_def, ht]
    group
  have e2 : ⁅v, d.t⁆⁻¹ = d.t * v * d.t * v⁻¹ := by
    rw [commutatorElement_def]
    simp only [mul_inv_rev, inv_inv, ht]
    group
  have h1 : d.t * ⁅v, d.t⁆ * d.t = ⁅v, d.t⁆⁻¹ := by
    rw [e1, e2, htt, mul_one]
  calc d.t * ⁅v, d.t⁆ = d.t * ⁅v, d.t⁆ * (d.t * d.t) := by rw [htt, mul_one]
    _ = (d.t * ⁅v, d.t⁆ * d.t) * d.t := by group
    _ = ⁅v, d.t⁆⁻¹ * d.t := by rw [h1]
    _ = ⁅v, d.t⁆ * d.t := by rw [inv_eq_of_mul_eq_one_right hκ2]

theorem Hyp.sec38a1_V_le_Z₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V ≤ (Subgroup.upperCentralSeries ↥(d.E ⊔ zpowers d.t) 2).map
      (d.E ⊔ zpowers d.t).subtype := by
  intro v hv
  rw [mem_map_upperCentralSeries_two]
  refine ⟨mem_sup_left (d.V_le_E hv), fun y hy => ?_⟩
  have htV : d.t ∈ normalizer (d.V : Set G) :=
    hd.normalizer_ZtP_le_normalizer_V hGMS (le_normalizer hd.t_mem_ZtP)
  rcases hd.sec38a1_mem_sup hGMS hy with hyE | ⟨e, he, rfl⟩
  · have : ⁅v, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 (hd.sec38a1_V_comm hGMS hv hyE).symm
    rw [this]
    exact one_mem _
  · have hκV := hd.sec38a1_commutator_mem_V hGMS hv
    have hp : d.t * v⁻¹ * d.t⁻¹ ∈ d.V := (mem_normalizer_iff.1 htV v⁻¹).1 (inv_mem hv)
    have hpe : e * (d.t * v⁻¹ * d.t⁻¹) = (d.t * v⁻¹ * d.t⁻¹) * e :=
      hd.sec38a1_V_comm hGMS hp he
    have e1 : ⁅v, e * d.t⁆ = ⁅v, d.t⁆ := by
      calc ⁅v, e * d.t⁆ = v * (e * (d.t * v⁻¹ * d.t⁻¹) * e⁻¹) := by
            simp only [commutatorElement_def]; group
        _ = ⁅v, d.t⁆ := by rw [hpe]; simp only [commutatorElement_def]; group
    rw [e1]
    refine ⟨mem_sup_left (d.V_le_E hκV), mem_centralizer_iff.2 fun z hz => ?_⟩
    rcases hd.sec38a1_mem_sup hGMS hz with hzE | ⟨e', he', rfl⟩
    · exact hd.sec38a1_V_comm hGMS hκV hzE
    · calc e' * d.t * ⁅v, d.t⁆ = e' * (d.t * ⁅v, d.t⁆) := by group
        _ = e' * (⁅v, d.t⁆ * d.t) := by rw [hd.sec38a1_comm_t hGMS hv]
        _ = (e' * ⁅v, d.t⁆) * d.t := by group
        _ = (⁅v, d.t⁆ * e') * d.t := by rw [hd.sec38a1_V_comm hGMS hκV he']
        _ = ⁅v, d.t⁆ * (e' * d.t) := by group

theorem Hyp.sec38a1_secondCenter (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (Subgroup.upperCentralSeries ↥(d.E ⊔ zpowers d.t) 2).map (d.E ⊔ zpowers d.t).subtype =
      d.V :=
  le_antisymm (fun _ hx => hd.sec38a1_Z₂_le hGMS hx) (hd.sec38a1_V_le_Z₂ hGMS)

theorem Hyp.sec38a1_t_not_mem_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.t ∉ d.E := fun ht => by
  have : d.t ∈ d.E ⊓ d.B₂ := ⟨ht, mem_sup_left (mem_zpowers _)⟩
  rw [hd.E_inf_B₂ hGMS] at this
  exact hd.t_not_mem_L (d.P_le_L (d.A₂_le_P this))

theorem Hyp.sec38a1_B₂_le_normalizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.B₂ ≤ normalizer (d.V : Set G) := fun x hx =>
  hd.normalizer_B₄_le_normalizer_V hGMS
    (le_normalizer (by rw [hd.B₄_eq_V_sup_B₂]; exact mem_sup_right hx))

theorem Hyp.sec38a1_elemAbMod_VB₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ElemAbMod d.V (d.V ⊔ d.B₂) :=
  ElemAbMod.sup_of_le_normalizer (hd.sec38a1_B₂_le_normalizer_V hGMS)
    (ElemAbMod.of_le hd.elemAbMod_Zp_B₂ hd.Zp_le_V)

theorem Hyp.sec38a1_not_E_le_VB₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ¬ d.E ≤ d.V ⊔ d.B₂ := fun hle => by
  refine hd.sec38a1_not_E_le_VA hGMS ?_
  rw [← hd.E_inf_B₄ hGMS]
  exact le_inf le_rfl (hd.B₄_eq_V_sup_B₂ ▸ hle)

theorem Hyp.sec38a1_le_or_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {Y : Subgroup G} (hYX : Y ≤ d.E ⊔ zpowers d.t) (hY : ElemAbMod d.V Y) :
    Y ≤ d.E ∨ Y ≤ d.V ⊔ d.B₂ := by
  by_cases hYE : Y ≤ d.E
  · exact Or.inl hYE
  right
  obtain ⟨y₀, hy₀Y, hy₀E⟩ := IsConcreteLE.not_le_iff_exists.mp hYE
  obtain hy₀' | ⟨e₀, he₀, rfl⟩ := hd.sec38a1_mem_sup hGMS (hYX hy₀Y)
  · exact absurd hy₀' hy₀E
  have hVB : d.V ⊔ d.A₂ ≤ d.V ⊔ d.B₂ := sup_le_sup_left (le_sup_right : d.A₂ ≤ d.B₂) _
  intro y hy
  rcases hd.sec38a1_mem_sup hGMS (hYX hy) with hyE | ⟨e, he, rfl⟩
  · exact hVB (hd.sec38a1_mem_VA hGMS hyE
      (hd.sec38a1_cr_mem_V hGMS he₀ hyE (hY.2 _ hy₀Y y hy)))
  · have hsq := hY.1 _ hy
    have he2 := (hd.elemAbMod_V_E hGMS).1 e he
    have hc : e⁻¹ * d.t * e * d.t ∈ d.V := by
      have e1 : e⁻¹ * d.t * e * d.t = (e * e)⁻¹ * (e * d.t * (e * d.t)) := by group
      rw [e1]
      exact mul_mem (inv_mem he2) hsq
    exact mul_mem (hVB (hd.sec38a1_mem_VA hGMS he hc))
      (mem_sup_right (mem_sup_left (mem_zpowers _)))

theorem Hyp.sec38a1_maximal (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    (X : Subgroup G) :
    Maximal (fun Y : Subgroup G => d.V ≤ Y ∧ Y ≤ d.E ⊔ zpowers d.t ∧ ElemAbMod d.V Y) X ↔
      X = d.E ∨ X = d.V ⊔ d.B₂ := by
  have htB : d.t ∈ d.V ⊔ d.B₂ := mem_sup_right (mem_sup_left (mem_zpowers _))
  have hB₂X : d.B₂ ≤ d.E ⊔ zpowers d.t :=
    sup_le (le_sup_right) ((hd.A₂_le_E hGMS).trans le_sup_left)
  have hE : d.V ≤ d.E ∧ d.E ≤ d.E ⊔ zpowers d.t ∧ ElemAbMod d.V d.E :=
    ⟨d.V_le_E, le_sup_left, hd.elemAbMod_V_E hGMS⟩
  have hB : d.V ≤ d.V ⊔ d.B₂ ∧ d.V ⊔ d.B₂ ≤ d.E ⊔ zpowers d.t ∧
      ElemAbMod d.V (d.V ⊔ d.B₂) :=
    ⟨le_sup_left, sup_le (d.V_le_E.trans le_sup_left) hB₂X, hd.sec38a1_elemAbMod_VB₂ hGMS⟩
  have hBE : ¬ d.V ⊔ d.B₂ ≤ d.E := fun e => hd.sec38a1_t_not_mem_E hGMS (e htB)
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, hmax⟩
    rcases hd.sec38a1_le_or_le hGMS h2 h3 with h4 | h4
    · exact Or.inl (le_antisymm h4 (hmax hE h4))
    · exact Or.inr (le_antisymm h4 (hmax hB h4))
  · rintro (rfl | rfl)
    · refine ⟨hE, fun Y hY hle => ?_⟩
      rcases hd.sec38a1_le_or_le hGMS hY.2.1 hY.2.2 with h4 | h4
      · exact h4
      · exact absurd (hle.trans h4) (hd.sec38a1_not_E_le_VB₂ hGMS)
    · refine ⟨hB, fun Y hY hle => ?_⟩
      rcases hd.sec38a1_le_or_le hGMS hY.2.1 hY.2.2 with h4 | h4
      · exact absurd (hle.trans h4) hBE
      · exact h4

theorem Hyp.sec38a1_E_inf_T (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E ⊓ d.T = d.A₂ :=
  le_antisymm (hd.E_inf_T_le_A₂ hGMS) (le_inf (hd.A₂_le_E hGMS) (d.A₂_le_P.trans hd.P_le))

theorem Hyp.sec38a1_card_ET (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card ↥(d.E ⊔ d.T) * (2 ^ f) ^ 7 = (2 ^ f) ^ 14 * Nat.card d.T := by
  have h := Common.card_sup_mul_card_inf_eq (hd.T_le_normalizer_E hGMS)
  rw [hd.sec38a1_E_inf_T hGMS, d.card_A₂, hd.card_E hGMS] at h
  exact h

theorem Hyp.sec38a1_T_le_normalizer_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : d.T ≤ normalizer (d.B₆ : Set G) := fun s hs =>
  d.normalizer_le_normalizer_B₆
    (Common.mem_normalizer_sup (hd.T_le_normalizer_F hGMS hs) (hd.T_le_normalizer_B₃ hs))

theorem Hyp.sec38a1_B₆_inf_T_le (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.B₆ ⊓ d.T ≤ d.B₃ := by
  rintro x ⟨hxB, hxT⟩
  have hxt : x * d.t = d.t * x := mem_centralizer_singleton_iff.1 (hd.T_le_centralizer hxT)
  have hF : (x * d.t)⁻¹ * (d.t * x) ∈ d.F := by
    rw [hxt, inv_mul_cancel]
    exact one_mem _
  obtain ⟨y, hy, a, ha, hx | hx⟩ := hd.exists_of_mem_FB₃ (hd.mem_FB₃_of_mem_B₆ hGMS hxB hF)
  · have haT : a ∈ d.T := d.A₃_le_P.trans hd.P_le ha
    have hyT : y ∈ d.T := by
      have : y = x * a⁻¹ := by rw [hx]; group
      rw [this]
      exact mul_mem hxT (inv_mem haT)
    have hyA : y ∈ d.A₁ := by
      rw [← hd.F_inf_T hGMS]
      exact ⟨hy, hyT⟩
    rw [hx]
    exact mul_mem (d.A₃_le_B₃ (d.A₁_le_A₃ hyA)) (d.A₃_le_B₃ ha)
  · have haT : a ∈ d.T := d.A₃_le_P.trans hd.P_le ha
    have hyT : y ∈ d.T := by
      have : y = x * (d.t * a)⁻¹ := by rw [hx]; group
      rw [this]
      exact mul_mem hxT (inv_mem (mul_mem hd.t_mem_T haT))
    have hyA : y ∈ d.A₁ := by
      rw [← hd.F_inf_T hGMS]
      exact ⟨hy, hyT⟩
    rw [hx]
    exact mul_mem (d.A₃_le_B₃ (d.A₁_le_A₃ hyA))
      (mul_mem (mem_sup_left (mem_zpowers _)) (d.A₃_le_B₃ ha))

theorem Hyp.sec38a1_card_B₆ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card d.B₆ = 2 * (2 ^ f) ^ 16 := by
  have h1 := hd.card_B₆ hGMS
  have h2 := Common.card_sup_mul_card_inf_eq hd.B₃_le_normalizer_F
  rw [hd.F_inf_B₃ hGMS, d.card_A₁, hd.card_F hGMS, hd.card_B₃] at h2
  have h3 : Nat.card ↥(d.F ⊔ d.B₃) = 2 * (2 ^ f) ^ 12 := by
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ f) ^ 4) ?_
    rw [h2]
    ring
  rw [h1, h3]
  ring

theorem Hyp.sec38a1_card_B₆T (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (2 ^ f) ^ 8 * Nat.card d.T ≤ Nat.card ↥(d.B₆ ⊔ d.T) := by
  have h1 := Common.card_sup_mul_card_inf_eq (hd.sec38a1_T_le_normalizer_B₆ hGMS)
  rw [hd.sec38a1_card_B₆ hGMS] at h1
  have h2 : Nat.card ↥(d.B₆ ⊓ d.T) ≤ 2 * (2 ^ f) ^ 8 := by
    rw [← hd.card_B₃]
    exact Subgroup.card_le_of_le (hd.sec38a1_B₆_inf_T_le hGMS)
  have hpos : 0 < 2 * (2 ^ f) ^ 8 := by positivity
  refine Nat.le_of_mul_le_mul_right (c := 2 * (2 ^ f) ^ 8) ?_ hpos
  calc (2 ^ f) ^ 8 * Nat.card d.T * (2 * (2 ^ f) ^ 8) = 2 * (2 ^ f) ^ 16 * Nat.card d.T := by ring
    _ = Nat.card ↥(d.B₆ ⊔ d.T) * Nat.card ↥(d.B₆ ⊓ d.T) := h1.symm
    _ ≤ Nat.card ↥(d.B₆ ⊔ d.T) * (2 * (2 ^ f) ^ 8) := Nat.mul_le_mul_left _ h2

theorem sec38a1_not_isSylowOf_top {P Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hlt : Nat.card P < Nat.card Q) : ¬ IsSylowOf 2 P ⊤ := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := hP.card_eq
  obtain ⟨S, hS⟩ := hQ.exists_le_sylow
  have h2 := Sylow.card_eq_multiplicity S
  have h3 := Subgroup.card_le_of_le hS
  rw [Subgroup.card_top] at h1
  omega

theorem Hyp.sec38a1_notSylow (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    IsPGroup 2 ↥(d.E ⊔ d.T) ∧ ¬ IsSylowOf 2 (d.E ⊔ d.T) ⊤ := by
  refine ⟨(hd.isPGroup_E hGMS).to_sup_of_normal_left' hd.isPGroup_T
    (hd.T_le_normalizer_E hGMS), ?_⟩
  refine sec38a1_not_isSylowOf_top (Q := d.B₆ ⊔ d.T)
    (d.isPGroup_B₆.to_sup_of_normal_left' hd.isPGroup_T (hd.sec38a1_T_le_normalizer_B₆ hGMS)) ?_
  have h1 := hd.sec38a1_card_ET hGMS
  have h2 := hd.sec38a1_card_B₆T hGMS
  have hT : 0 < Nat.card d.T := Nat.card_pos
  have h4 := hd.four_le
  have h3 : Nat.card ↥(d.E ⊔ d.T) = (2 ^ f) ^ 7 * Nat.card d.T := by
    refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ f) ^ 7) ?_
    rw [h1]
    ring
  rw [h3]
  exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right
    (Nat.pow_lt_pow_right (by omega) (by norm_num)) hT) h2


theorem sec38a1_of_hyp (hp : d.CaseHyp) : d.Sec38a1 :=
  ⟨hp.hyp.sec38a1_secondCenter hp.gms, hp.hyp.sec38a1_maximal hp.gms,
    hp.hyp.sec38a1_notSylow hp.gms⟩

end Data

namespace CaseBParts

theorem sec38a1 : Sec38a1Statement :=
  fun _ _ _ _ _ _ _ _ hp => Data.sec38a1_of_hyp hp

end CaseBParts

end CFSG.LocalAnalysis.EvenBN.U5

module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryRTwoGroup

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

variable {G : Type*} [Group G]

namespace U3RTorus

variable {T₁ R₁ : Subgroup G} {t d k : G} (hd : U3RTorus T₁ R₁ t d k)
include hd

theorem comm_t_of_mem {g : G} (hg : g ∈ zpowers d) : g * t = t * g := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  exact (Commute.zpow_left hd.comm_t n).eq

theorem odd_k : Odd (orderOf k) := Odd.of_dvd_nat hd.odd (orderOf_dvd_of_mem_zpowers hd.k_mem)

end U3RTorus

namespace U3RComp

variable {T₁ R₁ R₂ : Subgroup G} {t d k : G} {q : ℕ} (hc : U3RComp T₁ R₁ R₂ t d)
  (h : U3RSetup T₁ R₁ t q)
include hc h

theorem le_normalizer_sup : R₂ ≤ normalizer ((T₁ ⊔ zpowers t : Subgroup G) : Set G) :=
  hc.le_R₁.trans h.le_normalizer_sup

theorem exists_mul {x : G} (hx : x ∈ R₁) : ∃ w ∈ T₁ ⊔ zpowers t, ∃ r ∈ R₂, w * r = x := by
  have hx' : x ∈ (((T₁ ⊔ zpowers t) ⊔ R₂ : Subgroup G) : Set G) := by rw [hc.sup]; exact hx
  rw [coe_mul_of_right_le_normalizer_left _ _ (hc.le_normalizer_sup h)] at hx'
  obtain ⟨w, hw, r, hr, hwr⟩ := hx'
  exact ⟨w, hw, r, hr, hwr⟩

theorem card [Finite G] : Nat.card R₂ = q ^ 2 := by
  have hprod := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer
    (hc.le_normalizer_sup h)
  rw [sup_comm, hc.sup, inf_comm, hc.inf, h.card_R₁, h.card_A₁, h.card_sup] at hprod
  have hpos : 0 < 2 * q ^ 3 := by have := h.four_le; positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [← hprod]
  ring

theorem rho_ker (r : G) (hr : r ∈ R₂) (hrt : r * t = t * r) : r ∈ szA₁ T₁ := by
  have hrW : r ∈ T₁ ⊔ zpowers t := by
    rw [← h.inf_centralizer]
    exact mem_inf.mpr ⟨hc.le_R₁ hr, mem_centralizer_singleton_iff.mpr hrt⟩
  rw [← hc.inf]
  exact mem_inf.mpr ⟨hrW, hr⟩

theorem rho_surj {b : G} (hb : b ∈ szA₁ T₁) : ∃ r ∈ R₂, r * t * r⁻¹ * t⁻¹ = b := by
  obtain ⟨x, hx, hxt⟩ := h.cover b hb
  obtain ⟨w, hw, r, hr, rfl⟩ := hc.exists_mul h hx
  refine ⟨r, hr, ?_⟩
  have h1 := h.rho_mul (h.le_R₁ hw) (hc.le_R₁ hr)
  rw [(h.rho_eq_one_iff (h.le_R₁ hw)).mpr hw, one_mul, hxt, mul_inv_cancel_right] at h1
  exact h1.symm

omit h in
theorem inf_T₁ : T₁ ⊓ R₂ = szA₁ T₁ := by
  apply le_antisymm
  · rw [← hc.inf]
    exact inf_le_inf_right _ le_sup_left
  · exact le_inf (szA₁_le T₁) hc.le

theorem conj_mem_R₁ {x r : G} (hx : x ∈ R₁) (hr : r ∈ R₂) : x * r * x⁻¹ ∈ R₂ := by
  have h1 := h.comm_mem_szA₁ hx (hc.le_R₁ hr)
  have e : x * r * x⁻¹ = (x * r * x⁻¹ * r⁻¹) * r := by group
  rw [e]
  exact mul_mem (hc.le h1) hr

theorem t_mem_normalizer : t ∈ normalizer (R₂ : Set G) := by
  refine mem_normalizer_iff.mpr fun r => ⟨fun hr => hc.conj_mem_R₁ h h.t_mem_R₁ hr, fun hr => ?_⟩
  have := hc.conj_mem_R₁ h (inv_mem h.t_mem_R₁) hr
  rwa [show t⁻¹ * (t * r * t⁻¹) * t⁻¹⁻¹ = r by group] at this

theorem k_comm (hd : U3RTorus T₁ R₁ t d k) {x : G} (hx : x ∈ R₂) : k * x = x * k := by
  have hxR := hc.le_R₁ hx
  have hkx : k * x * k⁻¹ ∈ R₂ := hc.conj_mem k hd.k_mem x hx
  have hkt : k * t = t * k := hd.comm_t_of_mem hd.k_mem
  have hkt' : k⁻¹ * t * k = t := by rw [mul_assoc, ← hkt, inv_mul_cancel_left]
  have hkt'' : k * t * k⁻¹ = t := by rw [hkt, mul_inv_cancel_right]
  have hkb : (x * t * x⁻¹ * t⁻¹) * k = k * (x * t * x⁻¹ * t⁻¹) :=
    mem_centralizer_iff.mp hd.k_centralizer _ (h.rho_mem x hxR)
  have hconj : (k * x * k⁻¹) * t * (k * x * k⁻¹)⁻¹ = x * t * x⁻¹ := by
    calc (k * x * k⁻¹) * t * (k * x * k⁻¹)⁻¹ = k * x * (k⁻¹ * t * k) * x⁻¹ * k⁻¹ := by group
      _ = k * (x * t * x⁻¹ * t⁻¹) * k⁻¹ * (k * t * k⁻¹) := by rw [hkt']; group
      _ = (x * t * x⁻¹ * t⁻¹) * t := by rw [← hkb, mul_inv_cancel_right, hkt'']
      _ = x * t * x⁻¹ := by group
  have hy : x⁻¹ * (k * x * k⁻¹) ∈ szA₁ T₁ := by
    refine hc.rho_ker h _ (mul_mem (inv_mem hx) hkx) ?_
    calc x⁻¹ * (k * x * k⁻¹) * t =
        x⁻¹ * ((k * x * k⁻¹) * t * (k * x * k⁻¹)⁻¹) * (k * x * k⁻¹) := by group
      _ = x⁻¹ * (x * t * x⁻¹) * (k * x * k⁻¹) := by rw [hconj]
      _ = t * (x⁻¹ * (k * x * k⁻¹)) := by group
  have h1 := conj_eq_of_odd_of_inv_mul_conj_mem hd.odd_k h.sq_A₁ hd.k_centralizer hy
  calc k * x = k * x * k⁻¹ * k := by group
    _ = x * k := by rw [h1]

theorem commute_T₁ (hd : U3RTorus T₁ R₁ t d k) {y r : G} (hy : y ∈ T₁) (hr : r ∈ R₂) :
    y * r = r * y := by
  have hrR := hc.le_R₁ hr
  have hkr : k * r = r * k := hc.k_comm h hd hr
  have hkr' : k⁻¹ * r * k = r := by rw [mul_assoc, ← hkr, inv_mul_cancel_left]
  have hkr'' : k⁻¹ * r⁻¹ * k = r⁻¹ := by
    rw [show k⁻¹ * r⁻¹ * k = (k⁻¹ * r * k)⁻¹ by group, hkr']
  have hkT : k ∈ normalizer (T₁ : Set G) := by
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hd.k_mem
    rw [← hn]
    exact zpow_mem hd.mem_normalizer_T₁ n
  set β : G → G := fun x => x * r * x⁻¹ * r⁻¹ with hβ
  have hβA : ∀ x ∈ T₁, β x ∈ szA₁ T₁ := fun x hx => h.comm_mem_szA₁ (h.T₁_le_R₁ hx) hrR
  have hβmul : ∀ x ∈ T₁, ∀ x' ∈ T₁, β (x * x') = β x * β x' := by
    intro x hx x' hx'
    have hxb : x * β x' = β x' * x := mem_centralizer_iff.mp (mem_szA₁.mp (hβA x' hx')).2 x hx
    calc β (x * x') = x * β x' * x⁻¹ * (x * r * x⁻¹ * r⁻¹) := by simp only [hβ]; group
      _ = β x' * β x := by rw [hxb]; simp only [hβ]; group
      _ = β x * β x' := (U3RSetup.szA₁_comm (hβA x hx) (hβA x' hx')).symm
  have hβ1 : ∀ a ∈ szA₁ T₁, β a = 1 := by
    intro a ha
    simp only [hβ]
    rw [h.szA₁_comm_R₁ ha hrR, mul_inv_cancel_right, mul_inv_cancel]
  have hβk : ∀ x ∈ T₁, β (k * x * k⁻¹) = β x := by
    intro x hx
    have hkb : β x * k = k * β x := mem_centralizer_iff.mp hd.k_centralizer _ (hβA x hx)
    calc β (k * x * k⁻¹) = k * x * (k⁻¹ * r * k) * x⁻¹ * (k⁻¹ * r⁻¹ * k) * k⁻¹ := by
          simp only [hβ]; group
      _ = k * β x * k⁻¹ := by rw [hkr', hkr'']; simp only [hβ]; group
      _ = β x := by rw [← hkb, mul_inv_cancel_right]
  obtain ⟨y', hy', hyy'⟩ := hd.k_surj y hy
  have hky' : k * y' * k⁻¹ ∈ T₁ := (mem_normalizer_iff.mp hkT y').mp hy'
  have hw : k * y' * k⁻¹ * y'⁻¹ ∈ T₁ := mul_mem hky' (inv_mem hy')
  have hβw : β (k * y' * k⁻¹ * y'⁻¹) = 1 := by
    rw [hβmul _ hky' _ (inv_mem hy'), hβk y' hy', ← hβmul _ hy' _ (inv_mem hy'), mul_inv_cancel]
    simp only [hβ]
    group
  have hya : y = (k * y' * k⁻¹ * y'⁻¹) * (y⁻¹ * (k * y' * k⁻¹ * y'⁻¹))⁻¹ := by group
  have hβy : β y = 1 := by
    rw [hya, hβmul _ hw _ (inv_mem (szA₁_le T₁ hyy')), hβw, hβ1 _ (inv_mem hyy'), one_mul]
  have e : y * r * y⁻¹ * r⁻¹ = 1 := hβy
  calc y * r = y * r * y⁻¹ * r⁻¹ * (r * y) := by group
    _ = r * y := by rw [e, one_mul]

theorem comm (hd : U3RTorus T₁ R₁ t d k) : ∀ x ∈ R₂, ∀ y ∈ R₂, x * y = y * x := by
  have hdt' : d * t * d⁻¹ = t := by rw [hd.comm_t, mul_inv_cancel_right]
  have hdt'' : d * t⁻¹ = t⁻¹ * d := by
    rw [show d * t⁻¹ = (t * d⁻¹)⁻¹ by group, show t⁻¹ * d = (d⁻¹ * t)⁻¹ by group]
    congr 1
    calc t * d⁻¹ = d⁻¹ * (d * t * d⁻¹) := by group
      _ = d⁻¹ * t := by rw [hdt']
  refine commute_of_sq_of_equivariant (U := R₂) (A := szA₁ T₁) (d := d)
    (fun r => r * t * r⁻¹ * t⁻¹) (fun u hu b hb => (h.szA₁_comm_R₁ hb (hc.le_R₁ hu)).symm)
    h.sq_A₁ (fun u hu => h.sq_mem_szA₁ (hc.le_R₁ hu)) (fun u hu => ?_) hd.trans
    (fun u hu => h.rho_mem u (hc.le_R₁ hu)) (fun u hu u' hu' => h.rho_mul (hc.le_R₁ hu)
      (hc.le_R₁ hu')) (fun u hu => ?_) (fun u _ => ?_)
  · have := hc.conj_mem d⁻¹ (inv_mem (mem_zpowers d)) u hu
    rwa [inv_inv] at this
  · rw [h.rho_eq_one_iff (hc.le_R₁ hu), ← hc.inf]
    exact ⟨fun h1 => mem_inf.mpr ⟨h1, hu⟩, fun h1 => (mem_inf.mp h1).1⟩
  · calc d⁻¹ * u * d * t * (d⁻¹ * u * d)⁻¹ * t⁻¹ =
        d⁻¹ * u * (d * t * d⁻¹) * u⁻¹ * (d * t⁻¹) := by group
      _ = d⁻¹ * (u * t * u⁻¹ * t⁻¹) * d := by rw [hdt', hdt'']; group

theorem inf_centralizer_T₁ (hd : U3RTorus T₁ R₁ t d k) :
    R₁ ⊓ centralizer (T₁ : Set G) = R₂ ⊔ zpowers t := by
  apply le_antisymm
  · rintro x ⟨hxR, hxC⟩
    obtain ⟨w, hw, r, hr, rfl⟩ := hc.exists_mul h hxR
    obtain ⟨y, hy, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.t_comm hw
    have hyA : y ∈ szA₁ T₁ := by
      refine mem_szA₁.mpr ⟨hy, mem_centralizer_iff.mpr fun y' hy' => ?_⟩
      have h1 : y' * (y * z * r) = y * z * r * y' := mem_centralizer_iff.mp hxC y' hy'
      have h2 : y' * z = z * y' :=
        commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.t_comm y' hy')
      have h3 : y' * r = r * y' := hc.commute_T₁ h hd hy' hr
      have h4 : y' * y * (z * r) = y * y' * (z * r) := by
        calc y' * y * (z * r) = y' * (y * z * r) := by group
          _ = y * z * r * y' := h1
          _ = y * (z * (r * y')) := by group
          _ = y * y' * (z * r) := by rw [← h3, ← mul_assoc z, ← h2]; group
      exact mul_right_cancel h4
    exact mul_mem (mul_mem (mem_sup_left (hc.le hyA)) (mem_sup_right hz)) (mem_sup_left hr)
  · refine sup_le (le_inf hc.le_R₁ fun r hr => mem_centralizer_iff.mpr fun y hy =>
      hc.commute_T₁ h hd hy hr) (zpowers_le.mpr ⟨h.t_mem_R₁, h.t_comm⟩)

theorem eq_of_comm [Finite G] (hd : U3RTorus T₁ R₁ t d k) {B : Subgroup G}
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB : B ≤ R₁ ⊓ centralizer (T₁ : Set G))
    (hBcard : Nat.card B = q ^ 2) : B = R₂ := by
  have h4 := h.four_le
  refine eq_of_comm_of_le_sup_zpowers h.t_sq (hc.t_mem_normalizer h) (hc.comm h hd) hBc
    (hB.trans (hc.inf_centralizer_T₁ h hd).le) (hc.rho_ker h) ?_ (by rw [hBcard, hc.card h])
  rw [h.card_A₁, hc.card h]
  nlinarith

theorem mem_normalizer [Finite G] (hd : U3RTorus T₁ R₁ t d k) {n : G}
    (hnR : n ∈ normalizer (R₁ : Set G)) (hnT : n ∈ normalizer (T₁ : Set G)) :
    n ∈ normalizer (R₂ : Set G) := by
  have key : ∀ m : G, m ∈ normalizer (R₁ : Set G) → m ∈ normalizer (T₁ : Set G) →
      ∀ x ∈ R₂, m * x * m⁻¹ ∈ R₂ := by
    intro m hmR hmT x hx
    set B := R₂.map (MulAut.conj m).toMonoidHom with hB
    have hmemB : ∀ y, y ∈ B ↔ ∃ x ∈ R₂, m * x * m⁻¹ = y := by
      intro y
      simp only [hB, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hBeq : B = R₂ := by
      refine hc.eq_of_comm h hd ?_ ?_ ?_
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := (hmemB a).mp ha
        obtain ⟨y, hy, rfl⟩ := (hmemB b).mp hb
        calc m * x * m⁻¹ * (m * y * m⁻¹) = m * (x * y) * m⁻¹ := by group
          _ = m * (y * x) * m⁻¹ := by rw [hc.comm h hd x hx y hy]
          _ = m * y * m⁻¹ * (m * x * m⁻¹) := by group
      · intro a ha
        obtain ⟨x, hx, rfl⟩ := (hmemB a).mp ha
        refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hmR x).mp (hc.le_R₁ hx),
          mem_centralizer_iff.mpr fun y hy => ?_⟩
        have hy' : m⁻¹ * y * m ∈ T₁ := (mem_normalizer_iff''.mp hmT y).mp hy
        have e := hc.commute_T₁ h hd hy' hx
        calc y * (m * x * m⁻¹) = m * ((m⁻¹ * y * m) * x) * m⁻¹ := by group
          _ = m * (x * (m⁻¹ * y * m)) * m⁻¹ := by rw [e]
          _ = m * x * m⁻¹ * y := by group
      · rw [hB, card_map_of_injective (MulAut.conj m).injective, hc.card h]
    rw [← hBeq]
    exact (hmemB _).mpr ⟨x, hx, rfl⟩
  refine mem_normalizer_iff.mpr fun x => ⟨key n hnR hnT x, fun hx => ?_⟩
  have := key n⁻¹ (inv_mem hnR) (inv_mem hnT) _ hx
  rwa [show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x by group] at this

omit h in
theorem sup_eq : T₁ ⊔ R₂ ⊔ zpowers t = R₁ := by
  rw [sup_right_comm, hc.sup]

end U3RComp

end CFSG.SeitzReduction.RankOne

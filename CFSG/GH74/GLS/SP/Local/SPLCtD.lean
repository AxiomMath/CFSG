module

public import CFSG.GH74.GLS.SP.Local.SPLCt0
public import CFSG.GH74.GLS.SP.Local.SPLCtY1

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

section Algebra

theorem ctd_algebra {G : Type} [Group G] {y y' u t z : G}
    (hyy' : y * y' = y' * y) (hu : u = y * y') (hy2 : y * y = t * z) (hy' : y' = z * y * z⁻¹)
    (hz2 : z * z = 1) (ht2 : t * t = 1) (hzt : z * t = t * z) (hzu : z * u = u * z) :
    y⁻¹ * u * y = u ∧ y⁻¹ * z * y = t * u ∧ y⁻¹ * t * y = z * u := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hzy : z * y = y' * z := by rw [hy', inv_mul_cancel_right]
  have e1 : y⁻¹ * u * y = u := by
    calc y⁻¹ * u * y = y⁻¹ * (y * y') * y := by rw [← hu]
      _ = y' * y := by group
      _ = u := by rw [← hyy', ← hu]
  have e2 : y⁻¹ * z * y = t * u := by
    have hy'u : y' = y⁻¹ * u := by rw [hu]; group
    have hyi2 : y⁻¹ * y⁻¹ = z * t := by
      calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
        _ = (t * z)⁻¹ := by rw [hy2]
        _ = z⁻¹ * t⁻¹ := mul_inv_rev t z
        _ = z * t := by rw [hzi, hti]
    calc y⁻¹ * z * y = y⁻¹ * (z * y) := mul_assoc _ _ _
      _ = y⁻¹ * (y' * z) := by rw [hzy]
      _ = y⁻¹ * ((y⁻¹ * u) * z) := by rw [← hy'u]
      _ = (y⁻¹ * y⁻¹) * u * z := by group
      _ = z * t * u * z := by rw [hyi2]
      _ = z * t * (u * z) := mul_assoc _ _ _
      _ = z * t * (z * u) := by rw [hzu]
      _ = (z * t) * z * u := by group
      _ = (t * z) * z * u := by rw [hzt]
      _ = t * (z * z) * u := by group
      _ = t * u := by rw [hz2, mul_one]
  have e3 : y⁻¹ * t * y = z * u := by
    have ht : t = y * y * z := by rw [hy2, mul_assoc, hz2, mul_one]
    have hzy2 : z * y = y * (t * u) := by rw [← e2]; group
    calc y⁻¹ * t * y = y⁻¹ * (y * y * z) * y := by rw [← ht]
      _ = y * (z * y) := by group
      _ = y * (y * (t * u)) := by rw [hzy2]
      _ = (y * y) * (t * u) := (mul_assoc y y (t * u)).symm
      _ = (t * z) * (t * u) := by rw [hy2]
      _ = t * (z * t) * u := by group
      _ = t * (t * z) * u := by rw [hzt]
      _ = (t * t) * z * u := by group
      _ = z * u := by rw [ht2, one_mul]
  exact ⟨e1, e2, e3⟩

theorem ctd_invol_split {G : Type} [Group G] {κ y : G} (h : κ * y * (κ * y) = 1) :
    y * y = (y * κ * y⁻¹)⁻¹ * κ⁻¹ := by
  have h1 : y = κ⁻¹ * y⁻¹ * κ⁻¹ := by
    have h2 : (κ * y * κ) * y = 1 := by
      calc (κ * y * κ) * y = κ * y * (κ * y) := by group
        _ = 1 := h
    calc y = (κ * y * κ)⁻¹ := eq_inv_of_mul_eq_one_right h2
      _ = κ⁻¹ * y⁻¹ * κ⁻¹ := by group
  calc y * y = y * (κ⁻¹ * y⁻¹ * κ⁻¹) := by rw [← h1]
    _ = (y * κ * y⁻¹)⁻¹ * κ⁻¹ := by group

end Algebra

section Geometry

variable {G : Type} [Group G] [Finite G] (D : SPLNot1 G)

theorem ctd_mem_K_of_normalizes (hs : SPLSetup D.toSPLNot0) {x : G} (hxC : x ∈ Cz D.z) (hx2 : x * x = 1)
    (hxN : x ∈ normalizer (D.K₁ : Set G)) : x ∈ D.K₁ ⊔ D.K₂ := by
  obtain ⟨k, hk, s, hsS, y, hy, rfl⟩ := hs.gen x hxC
  have hyN : y ∈ normalizer (D.K₁ : Set G) := by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact F_normalizes_K₁ hs y hy a ha
    · intro ha
      have h := F_normalizes_K₁ hs y⁻¹ (D.F.inv_mem hy) _ ha
      have e : y⁻¹ * (y * a * y⁻¹) * y⁻¹⁻¹ = a := by group
      rwa [e] at h
  have hksN : k * s ∈ normalizer (D.K₁ : Set G) := by
    have h := Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ hyN)
    rwa [mul_inv_cancel_right] at h
  have hsK : s ∈ D.K := by
    by_contra hsK
    exact swap_not_mem hs hsS hsK hk hksN
  have hκ : k * s ∈ D.K₁ ⊔ D.K₂ := D.K.mul_mem hk hsK
  have hyκ : y * (k * s) * y⁻¹ ∈ D.K₁ ⊔ D.K₂ := hs.comps.conj_sup_mem (F_le_C hs hy) hκ
  have hy2K : y * y ∈ D.K₁ ⊔ D.K₂ := by
    rw [ctd_invol_split hx2]
    exact (D.K₁ ⊔ D.K₂).mul_mem ((D.K₁ ⊔ D.K₂).inv_mem hyκ) ((D.K₁ ⊔ D.K₂).inv_mem hκ)
  have hy2 : y * y = 1 := by
    have h : y * y ∈ D.F ⊓ D.K := ⟨D.F.mul_mem hy hy, hy2K⟩
    rw [F_inf_K_eq hs] at h
    exact Subgroup.mem_bot.mp h
  have hy1 : y = 1 := by
    have hodd := F_odd D.toSPLNot0 hy
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  rw [hy1, mul_one]
  exact hκ

theorem ctd_swap_of_invol (hs : SPLSetup D.toSPLNot0) {x : G} (hxz : x * D.z = D.z * x) (hx2 : x * x = 1)
    (hxne : x ≠ D.z) (hxc : IsConj D.z x) :
    (∀ a ∈ D.K₁, x * a * x⁻¹ ∈ D.K₂) ∧ (∀ a ∈ D.K₂, x * a * x⁻¹ ∈ D.K₁) := by
  have hxC : x ∈ Cz D.z := mem_centralizer_singleton_iff.mpr hxz
  rcases hs.comps.perm hxC with ⟨e1, -⟩ | ⟨e1, e2⟩
  · exfalso
    have hxK := ctd_mem_K_of_normalizes D hs hxC hx2 (Subgroup.mem_normalizer_iff_map_conj_eq.mpr e1)
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact z_ne_one' D hs (isConj_one_right.mp hxc.symm)
    have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
    exact hs.syl.t_nconj (hxc.trans (hs.syl.inv_K hxK hxo hxne).symm)
  · exact ⟨fun a ha => LUComps.mem_of_map e1 ha, fun a ha => LUComps.mem_of_map e2 ha⟩

theorem ctd_conj_le_K (hs : SPLSetup D.toSPLNot0) {c : G} (hc : c * D.z * c⁻¹ = D.t * D.z) :
    ∀ i ∈ D.Ict, c⁻¹ * i * c ∈ D.K₁ ⊔ D.K₂ := by
  have hzt := z_comm_t' D hs
  have hz2 : orderOf D.z = 2 := hs.syl.z_inv
  have hzw : D.z ∈ centralizer ({D.t * D.z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc D.z * (D.t * D.z) = D.z * D.t * D.z := (mul_assoc _ _ _).symm
      _ = D.t * D.z * D.z := by rw [hzt]
  have hCC : centralizer ({D.z} : Set G) ⊓ centralizer ({D.t * D.z} : Set G) = D.C ⊓ D.Ct := by
    ext x
    constructor
    · rintro ⟨hxz, hxw⟩
      have h1 : x * D.z = D.z * x := mem_centralizer_singleton_iff.mp hxz
      have h3 : x * (D.t * D.z) = D.t * D.z * x := mem_centralizer_singleton_iff.mp hxw
      refine ⟨hxz, mem_centralizer_singleton_iff.mpr ?_⟩
      have h4 : x * D.t * D.z = D.t * x * D.z := by
        calc x * D.t * D.z = x * (D.t * D.z) := mul_assoc _ _ _
          _ = D.t * D.z * x := h3
          _ = D.t * (D.z * x) := mul_assoc _ _ _
          _ = D.t * (x * D.z) := by rw [← h1]
          _ = D.t * x * D.z := (mul_assoc _ _ _).symm
      exact mul_right_cancel h4
    · rintro ⟨hxz, hxt⟩
      have h1 : x * D.z = D.z * x := mem_centralizer_singleton_iff.mp hxz
      have h2 : x * D.t = D.t * x := mem_centralizer_singleton_iff.mp hxt
      refine ⟨hxz, mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * (D.t * D.z) = x * D.t * D.z := (mul_assoc _ _ _).symm
        _ = D.t * x * D.z := by rw [h2]
        _ = D.t * (x * D.z) := mul_assoc _ _ _
        _ = D.t * (D.z * x) := by rw [h1]
        _ = D.t * D.z * x := (mul_assoc _ _ _).symm
  have hΛ : IsPCompIn 2 (centralizer ({D.z} : Set G) ⊓ centralizer ({D.t * D.z} : Set G)) D.Ict := by
    rw [hCC]
    exact I_comp D hs
  have hbal := CFSG.GH74.GLS.Stage1.Thm2.Recip.le_pLayerOf_of_isPCompIn_inf hz2 hzw hΛ
  have hCt : centralizer ({D.t * D.z} : Set G) =
      Stage1.Thm3.Sec4.cmap c (centralizer ({D.z} : Set G)) := by
    rw [← hc]
    exact (CFSG.GH74.GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj D.z c).symm
  have hpl : pLayerOf 2 (centralizer ({D.t * D.z} : Set G)) =
      Stage1.Thm3.Sec4.cmap c (D.K₁ ⊔ D.K₂) := by
    rw [hCt, Stage1.Thm3.Sec4.pLayerOf_cmap c, hs.comps.pLayerOf_eq]
  intro i hi
  have h := hbal hi
  rw [hpl] at h
  exact Stage1.Thm3.Sec4.mem_cmap.mp h

end Geometry

theorem exists_d {G : Type} [Group G] [Finite G] (D : SPLNot1 G) (hs : SPLSetup D.toSPLNot0)
    {u : G} (huI : u ∈ D.Ict) (hu2 : orderOf u = 2) :
    ∃ g : G, g⁻¹ * u * g = u ∧ g⁻¹ * D.z * g = D.t * u ∧ g⁻¹ * D.t * g = D.z * u := by
  have hz2 : D.z * D.z = 1 := z_mul_z' D hs
  have ht2 : D.t * D.t = 1 := t_mul_t' D hs
  have hzt : D.z * D.t = D.t * D.z := z_comm_t' D hs
  have hzw' : D.z * (D.t * D.z) = D.t * D.z * D.z := by
    calc D.z * (D.t * D.z) = D.z * D.t * D.z := (mul_assoc _ _ _).symm
      _ = D.t * D.z * D.z := by rw [hzt]
  have huu : u * u = 1 := by
    have h : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    rwa [pow_two] at h
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    omega
  have hzu : D.z * u = u * D.z := z_central_in_K D hs (mem_zpowers D.z) u (Ict_le_K D hs huI)
  obtain ⟨c, hc⟩ := isConj_iff.mp hs.syl.tz_conj
  have hcz : c * D.z = D.t * D.z * c := by
    calc c * D.z = c * D.z * c⁻¹ * c := by group
      _ = D.t * D.z * c := by rw [hc]
  have hzc' : D.z * c⁻¹ = c⁻¹ * (D.t * D.z) := by
    calc D.z * c⁻¹ = c⁻¹ * (c * D.z * c⁻¹) := by group
      _ = c⁻¹ * (D.t * D.z) := by rw [hc]
  obtain ⟨zt, hztdef⟩ : ∃ zt : G, zt = c⁻¹ * D.z * c := ⟨_, rfl⟩
  have hzc : D.z = c * zt * c⁻¹ := by rw [hztdef]; group
  have hztz : zt * D.z = D.z * zt := by
    rw [hztdef]
    calc c⁻¹ * D.z * c * D.z = c⁻¹ * D.z * (c * D.z) := by group
      _ = c⁻¹ * D.z * (D.t * D.z * c) := by rw [hcz]
      _ = c⁻¹ * (D.z * (D.t * D.z)) * c := by group
      _ = c⁻¹ * ((D.t * D.z) * D.z) * c := by rw [hzw']
      _ = (c⁻¹ * (D.t * D.z)) * D.z * c := by group
      _ = (D.z * c⁻¹) * D.z * c := by rw [hzc']
      _ = D.z * (c⁻¹ * D.z * c) := by group
  have hzt2 : zt * zt = 1 := by
    rw [hztdef]
    calc c⁻¹ * D.z * c * (c⁻¹ * D.z * c) = c⁻¹ * (D.z * D.z) * c := by group
      _ = 1 := by rw [hz2]; group
  have hztne : zt ≠ D.z := by
    intro h
    have hD : c⁻¹ * D.z * c = D.z := hztdef.symm.trans h
    have h1 : c * D.z * c⁻¹ = D.z := by
      calc c * D.z * c⁻¹ = c * (c⁻¹ * D.z * c) * c⁻¹ := by rw [hD]
        _ = D.z := by group
    have h2 : D.t * D.z = D.z := hc.symm.trans h1
    have h3 : D.t = 1 := mul_right_cancel (h2.trans (one_mul D.z).symm)
    have h4 := hs.syl.t_ord
    rw [h3, orderOf_one] at h4
    omega
  have hztc : IsConj D.z zt := isConj_iff.mpr ⟨c⁻¹, by rw [hztdef, inv_inv]⟩
  obtain ⟨hz₁, hz₂⟩ := ctd_swap_of_invol D hs hztz hzt2 hztne hztc
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup G, P = Stage1.Thm3.Sec4.cmap c⁻¹ D.Ict := ⟨_, rfl⟩
  have hPmem : ∀ p : G, p ∈ P ↔ c * p * c⁻¹ ∈ D.Ict := by
    intro p
    rw [hPdef, Stage1.Thm3.Sec4.mem_cmap, inv_inv]
  have hPperf : ⁅P, P⁆ = P := by
    rw [hPdef, Stage1.Thm3.Sec4.cmap, ← Subgroup.map_commutator, Ict_perfect D hs]
  have hPK : P ≤ D.K₁ ⊔ D.K₂ := by
    intro p hp
    have hi : c * p * c⁻¹ ∈ D.Ict := (hPmem p).mp hp
    have h := ctd_conj_le_K D hs hc _ hi
    have e : c⁻¹ * (c * p * c⁻¹) * c = p := by group
    rwa [e] at h
  have hPz : ∀ p ∈ P, zt * p = p * zt := by
    intro p hp
    have hi : c * p * c⁻¹ ∈ D.Ict := (hPmem p).mp hp
    have h1 : D.z * (c * p * c⁻¹) = (c * p * c⁻¹) * D.z :=
      z_central_in_K D hs (mem_zpowers D.z) _ (Ict_le_K D hs hi)
    rw [hztdef]
    calc c⁻¹ * D.z * c * p = c⁻¹ * (D.z * (c * p * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * p * c⁻¹) * D.z) * c := by rw [h1]
      _ = p * (c⁻¹ * D.z * c) := by group
  have hu'P : c⁻¹ * u * c ∈ P := by
    rw [hPmem]
    have e : c * (c⁻¹ * u * c) * c⁻¹ = u := by group
    rw [e]
    exact huI
  have hu'2 : c⁻¹ * u * c * (c⁻¹ * u * c) = 1 := by
    calc c⁻¹ * u * c * (c⁻¹ * u * c) = c⁻¹ * (u * u) * c := by group
      _ = 1 := by rw [huu]; group
  have hu'1 : c⁻¹ * u * c ≠ 1 := by
    intro h
    apply hu1
    calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨y₀, hy₀, hy₀2, hu'⟩ := exists_y1 D.K₁ D.K₂ D.z zt hs.syl.z_inv hs.comps.inf_eq hs.comps.comm
    (fun x hx hx2 => K₁_inv_unique D.ext3 hs hx hx2) hzt2 hztz hz₁ hz₂ P hPperf hPK hPz (c⁻¹ * u * c)
    hu'P hu'2 hu'1
  have hyy' : c * y₀ * c⁻¹ * (c * (zt * y₀ * zt⁻¹) * c⁻¹) =
      c * (zt * y₀ * zt⁻¹) * c⁻¹ * (c * y₀ * c⁻¹) := by
    have h := hs.comps.comm y₀ hy₀ _ (hz₁ y₀ hy₀)
    calc c * y₀ * c⁻¹ * (c * (zt * y₀ * zt⁻¹) * c⁻¹) = c * (y₀ * (zt * y₀ * zt⁻¹)) * c⁻¹ := by group
      _ = c * ((zt * y₀ * zt⁻¹) * y₀) * c⁻¹ := by rw [h]
      _ = c * (zt * y₀ * zt⁻¹) * c⁻¹ * (c * y₀ * c⁻¹) := by group
  have hu : u = c * y₀ * c⁻¹ * (c * (zt * y₀ * zt⁻¹) * c⁻¹) := by
    calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
      _ = c * (y₀ * (zt * y₀ * zt⁻¹)) * c⁻¹ := by rw [hu']
      _ = c * y₀ * c⁻¹ * (c * (zt * y₀ * zt⁻¹) * c⁻¹) := by group
  have hy2 : c * y₀ * c⁻¹ * (c * y₀ * c⁻¹) = D.t * D.z := by
    calc c * y₀ * c⁻¹ * (c * y₀ * c⁻¹) = c * (y₀ * y₀) * c⁻¹ := by group
      _ = D.t * D.z := by rw [hy₀2]; exact hc
  have hy' : c * (zt * y₀ * zt⁻¹) * c⁻¹ = D.z * (c * y₀ * c⁻¹) * D.z⁻¹ := by
    conv_rhs => rw [hzc]
    group
  exact ⟨c * y₀ * c⁻¹, ctd_algebra hyy' hu hy2 hy' hz2 ht2 hzt hzu⟩

end CFSG.GH74.GLS.SP.Local

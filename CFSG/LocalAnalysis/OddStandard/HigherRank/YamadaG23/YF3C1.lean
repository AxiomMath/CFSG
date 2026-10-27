module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B4

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem f3_mem_Vt {s : Setting3 G L} {p : G}
    (hp : p ∈ (cen s.fr.B ⊔ zpowers s.t : Subgroup G)) :
    p ∈ cen s.fr.B ∨ ∃ v ∈ cen s.fr.B, p = v * s.t := by
  have hVc : cen s.fr.B ≤ Subgroup.centralizer ({s.t} : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact (s3_comm_t_of_mem_L s (f3_B_le_L s (Subgroup.mem_inf.mp hv).1)).symm
  have hVn : cen s.fr.B ≤ Subgroup.normalizer (zpowers s.t : Set G) :=
    hVc.trans (le_trans (Subgroup.centralizer_le_normalizer ({s.t} : Set G))
      (by simpa [Subgroup.zpowers_eq_closure] using
        Subgroup.normalizer_le_normalizer_closure ({s.t} : Set G)))
  have hcoe : (↑(cen s.fr.B ⊔ zpowers s.t) : Set G) = cen s.fr.B * zpowers s.t :=
    Subgroup.coe_mul_of_left_le_normalizer_right (cen s.fr.B) (zpowers s.t) hVn
  have hp' : p ∈ (cen s.fr.B : Set G) * (zpowers s.t : Set G) := by
    rw [← hcoe]; exact hp
  rw [Set.mem_mul] at hp'
  obtain ⟨v, hv, z, hz, rfl⟩ := hp'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have h2 : s.t ^ (2 : ℤ) = 1 := by
    rw [zpow_two, ← pow_two, ← s.t_order]
    exact pow_orderOf_eq_one s.t
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
  · left
    rw [hm, zpow_mul, h2, one_zpow, mul_one]
    exact hv
  · right
    refine ⟨v, hv, ?_⟩
    rw [hm, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

private theorem mem_normalizer_inf_centralizer {K V : Subgroup G} {a : G}
    (haK : a ∈ Subgroup.normalizer (K : Set G))
    (haV : a ∈ Subgroup.normalizer (V : Set G)) :
    a ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro b
  constructor
  · intro hb
    obtain ⟨hbK, hbC⟩ := Subgroup.mem_inf.mp hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_set_normalizer_iff.mp haK b).mp hbK
    · rw [Subgroup.mem_centralizer_iff] at hbC ⊢
      intro v hv
      have hv' : a⁻¹ * v * a ∈ V := (Subgroup.mem_set_normalizer_iff''.mp haV v).mp hv
      calc v * (a * b * a⁻¹) = a * ((a⁻¹ * v * a) * b) * a⁻¹ := by group
        _ = a * (b * (a⁻¹ * v * a)) * a⁻¹ := by rw [hbC (a⁻¹ * v * a) hv']
        _ = (a * b * a⁻¹) * v := by group
  · intro hb
    obtain ⟨hbK, hbC⟩ := Subgroup.mem_inf.mp hb
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_set_normalizer_iff.mp haK b).mpr hbK
    · rw [Subgroup.mem_centralizer_iff] at hbC ⊢
      intro v hv
      have hv' : a * v * a⁻¹ ∈ V := (Subgroup.mem_set_normalizer_iff.mp haV v).mp hv
      calc v * b = a⁻¹ * ((a * v * a⁻¹) * (a * b * a⁻¹)) * a := by group
        _ = a⁻¹ * ((a * b * a⁻¹) * (a * v * a⁻¹)) * a := by rw [hbC (a * v * a⁻¹) hv']
        _ = b * v := by group

theorem f3_X_le_normVt {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.X ≤ normalizer ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx k hk
  rcases f3_mem_Vt hk with hkV | ⟨v, hv, rfl⟩
  · exact Subgroup.mem_sup_left (f3_X_norm_V hH x hx k hkV)
  · have h1 : x * v * x⁻¹ ∈ cen s.fr.B := f3_X_norm_V hH x hx v hv
    obtain ⟨v', hv', hv'eq⟩ := f3_tX_sub hH x hx
    have hxconj : x * (v * s.t) * x⁻¹ = (x * v * x⁻¹) * (v' * s.t) := by
      rw [← hv'eq]; group
    rw [hxconj]
    exact Subgroup.mul_mem ((cen s.fr.B ⊔ zpowers s.t : Subgroup G))
      (Subgroup.mem_sup_left h1)
      (Subgroup.mul_mem ((cen s.fr.B ⊔ zpowers s.t : Subgroup G))
        (Subgroup.mem_sup_left hv') (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t)))

theorem f3_normVt_le_X {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normalizer ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) ≤ s.X := by
  intro x hxW
  have hxt_mem : x * s.t * x⁻¹ ∈ (cen s.fr.B ⊔ zpowers s.t : Subgroup G) :=
    (Subgroup.mem_set_normalizer_iff.mp hxW s.t).mp
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers s.t))
  have hxt_notL : x * s.t * x⁻¹ ∉ L := hH.h31.2.2.1 x
  rcases f3_mem_Vt hxt_mem with hvV | ⟨v, hv, heq⟩
  · exact absurd (f3_B_le_L s (Subgroup.mem_inf.mp hvV).1) hxt_notL
  · obtain ⟨y, hyY, hy⟩ := f3_Y_orbit hH v hv
    have hyX : y ∈ s.X := (Subgroup.mem_inf.mp hyY).1
    set h : G := y⁻¹ * x with hh_def
    have hh_conj : h * s.t * h⁻¹ = s.t := by
      have h1 : x * s.t * x⁻¹ = y * s.t * y⁻¹ := by rw [heq, ← hy]
      calc h * s.t * h⁻¹ = y⁻¹ * (x * s.t * x⁻¹) * y := by rw [hh_def]; group
        _ = y⁻¹ * (y * s.t * y⁻¹) * y := by rw [h1]
        _ = s.t := by group
    have hhH : h ∈ s.H := by
      show h ∈ Subgroup.centralizer ({s.t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      subst ha
      calc s.t * h = (h * s.t * h⁻¹) * h := by rw [hh_conj]
        _ = h * s.t := by group
    have hyW : y ∈ Subgroup.normalizer
        ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) := (f3_X_le_normVt hH) hyX
    have hhW : h ∈ Subgroup.normalizer
        ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) := by
      rw [hh_def]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyW) hxW
    have hhL : h ∈ Subgroup.normalizer (L : Set G) := s3_H_le_N s hH.hS hhH
    have hWinfL : ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) ⊓ L : Subgroup G) = cen s.fr.B := by
      apply le_antisymm
      · intro p hp
        obtain ⟨hpW, hpL⟩ := Subgroup.mem_inf.mp hp
        rcases f3_mem_Vt hpW with hpV | ⟨u, hu, hueq⟩
        · exact hpV
        · exfalso
          apply s3_t_not_mem_L s hH.h31
          have ht : s.t = u⁻¹ * p := by rw [hueq]; group
          rw [ht]
          exact L.mul_mem (L.inv_mem (f3_B_le_L s (Subgroup.mem_inf.mp hu).1)) hpL
      · intro p hp
        exact Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_sup_left hp, f3_B_le_L s (Subgroup.mem_inf.mp hp).1⟩
    have hhV : h ∈ Subgroup.normalizer (cen s.fr.B : Set G) := by
      have hmem : h ∈ Subgroup.normalizer
          ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) ⊓ Subgroup.normalizer (L : Set G) :=
        Subgroup.mem_inf.mpr ⟨hhW, hhL⟩
      have hhinf : h ∈ Subgroup.normalizer
          (((cen s.fr.B ⊔ zpowers s.t : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf hmem
      rwa [hWinfL] at hhinf
    have hhB : h ∈ Subgroup.normalizer (s.fr.B : Set G) := by
      have hB : (L ⊓ Subgroup.centralizer (cen s.fr.B : Set G) : Subgroup G) = s.fr.B :=
        f3_centIn_L_V hH
      have hhcent : h ∈ Subgroup.normalizer
          ((L ⊓ Subgroup.centralizer (cen s.fr.B : Set G) : Subgroup G) : Set G) :=
        mem_normalizer_inf_centralizer hhL hhV
      rwa [hB] at hhcent
    have hhN : h ∈ f3N s := Subgroup.mem_inf.mpr ⟨hhH, hhB⟩
    have hx : x = y * h := by rw [hh_def]; group
    rw [hx]
    exact s.X.mul_mem hyX (f3_N_le_X s hhN)

theorem f3_c1 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.X = normalizer ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) :=
  le_antisymm (f3_X_le_normVt hH) (f3_normVt_le_X hH)

theorem f3_c2 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normalizer ((cen s.fr.B ⊔ zpowers s.t : Subgroup G) : Set G) = normIn s.H s.fr.B ⊔ s.C₂ :=
  (f3_c1 hH).symm.trans (f3_X_eq_N_sup_C₂ hH)

theorem f3_c3 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    normIn s.H s.fr.B ⊔ s.C₂ ≤ normalizer (s.fr.B : Set G) :=
  (f3_X_eq_N_sup_C₂ hH) ▸ f3_X_le_normB hH

theorem f3_c4 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) : ⁅s.oddH, s.C₂⁆ = ⊥ := by
  rw [f3_oddH_eq_bot hH.hS s]
  exact Subgroup.commutator_bot_left _

theorem f3_c5 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.H ⊓ s.C₂ = s.fr.B ⊔ zpowers s.t :=
  f3_H_inf_C₂ hH

theorem f3_c6 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    conjClass s.C₂ s.t = s.tCoset (cen s.fr.B) := by
  ext w
  simp only [conjClass, Setting3.tCoset, Set.mem_setOf_eq]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨v, hv, hveq⟩ := f3_tX_sub hH c (f3_C₂_le_X hH hc)
    exact ⟨v, hv, hveq⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨y, hyY, hy⟩ := f3_Y_orbit hH v hv
    obtain ⟨c, hc, a, ha, rfl⟩ := f3_Y_eq_Y1X0 hH y hyY
    refine ⟨c, ?_, ?_⟩
    · rw [f3_C₂_eq_Y1 hH]; exact hc
    · rw [← hy]
      have haH : a ∈ s.H := (Subgroup.mem_inf.mp ha).1
      have hacomm : a * s.t = s.t * a :=
        (Subgroup.mem_centralizer_iff.mp haH s.t (by simp)).symm
      have haconj : a * s.t * a⁻¹ = s.t := by rw [hacomm]; group
      calc (c * a) * s.t * (c * a)⁻¹ = c * (a * s.t * a⁻¹) * c⁻¹ := by group
        _ = c * s.t * c⁻¹ := by rw [haconj]

end CFSG.OddStandard.HigherRank.YamadaG23

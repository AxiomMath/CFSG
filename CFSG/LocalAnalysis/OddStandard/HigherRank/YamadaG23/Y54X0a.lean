module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Cosets
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y5Frame
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Nrm
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y31SylConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem f4P_le_R (s : Setting3 G L) : f4P s ≤ s.R :=
  sup_le ((s3_F_le_A s).trans ((s3_A_le_S s).trans s.S_le_R))
    (Subgroup.zpowers_le.mpr (s3_t_mem_R s))

private theorem isPGroup_zpowers_of_sq_mem {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 2 P) {a : G} (ha : a ^ 2 ∈ P) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hdvd1 : orderOf a ∣ 2 * orderOf (a ^ 2) :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_mul, pow_orderOf_eq_one])
  have hdvd2 : orderOf (a ^ 2) ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.orderOf_dvd_natCard P ha
  refine IsPGroup.of_card_dvd_pow (n := k + 1) ?_
  rw [Nat.card_zpowers]
  calc orderOf a ∣ 2 * orderOf (a ^ 2) := hdvd1
    _ ∣ 2 * 2 ^ k := Nat.mul_dvd_mul_left 2 hdvd2
    _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

private theorem mem_conjSub_iff (V : Subgroup G) (h y : G) :
    y ∈ conjSub h V ↔ h⁻¹ * y * h ∈ V := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvv : h⁻¹ * (MulEquiv.toMonoidHom (MulAut.conj h)) v * h = v := by
      change h⁻¹ * (h * v * h⁻¹) * h = v
      group
    rwa [hvv]
  · intro hy
    refine ⟨h⁻¹ * y * h, hy, ?_⟩
    change h * (h⁻¹ * y * h) * h⁻¹ = y
    group

private theorem centIn_conjSub_eq_of_centIn_eq {V : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (L : Set G)) (hV : centIn L V = V) :
    centIn L (conjSub h V) = conjSub h V := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxL' : h⁻¹ * x * h ∈ L := (Subgroup.mem_normalizer_iff''.mp hh x).mp hxL
    have hxC' : h⁻¹ * x * h ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hxC ⊢
      intro v hv
      have hm : h * v * h⁻¹ ∈ conjSub h V := by
        refine (mem_conjSub_iff V h (h * v * h⁻¹)).mpr ?_
        have hvv : h⁻¹ * (h * v * h⁻¹) * h = v := by group
        rwa [hvv]
      have h1 : h * (v * (h⁻¹ * x * h)) * h⁻¹ = h * ((h⁻¹ * x * h) * v) * h⁻¹ := by
        calc h * (v * (h⁻¹ * x * h)) * h⁻¹ = (h * v * h⁻¹) * x := by group
          _ = x * (h * v * h⁻¹) := hxC (h * v * h⁻¹) hm
          _ = h * ((h⁻¹ * x * h) * v) * h⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h1)
    have hxV : h⁻¹ * x * h ∈ V := hV ▸ Subgroup.mem_inf.mpr ⟨hxL', hxC'⟩
    exact (mem_conjSub_iff V h x).mpr hxV
  · intro x hx
    have hxV : h⁻¹ * x * h ∈ V := (mem_conjSub_iff V h x).mp hx
    set v : G := h⁻¹ * x * h with hv_def
    have hvV : v ∈ V := hxV
    have hvL : v ∈ L := (Subgroup.mem_inf.mp (hV.symm ▸ hvV)).1
    have hvC : v ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.mp (hV.symm ▸ hvV)).2
    have hxv : h * v * h⁻¹ = x := by rw [hv_def]; group
    rw [← hxv]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hh v).mp hvL
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyV : h⁻¹ * y * h ∈ V := (mem_conjSub_iff V h y).mp hy
      set w : G := h⁻¹ * y * h with hw_def
      have hwV : w ∈ V := hyV
      have hyw : h * w * h⁻¹ = y := by rw [hw_def]; group
      have hwv : w * v = v * w := Subgroup.mem_centralizer_iff.mp hvC w hwV
      calc y * (h * v * h⁻¹) = (h * w * h⁻¹) * (h * v * h⁻¹) := by rw [← hyw]
        _ = h * (w * v) * h⁻¹ := by group
        _ = h * (v * w) * h⁻¹ := by rw [hwv]
        _ = (h * v * h⁻¹) * (h * w * h⁻¹) := by group
        _ = (h * v * h⁻¹) * y := by rw [← hyw]

theorem y54_X0_cosets {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∀ a ∈ f4X0 s, ∀ b ∈ f4X0 s, a ∈ f4P s ∨ b ∈ f4P s ∨ a⁻¹ * b ∈ f4P s := by
  have h := y5_cent_cosets hH (V := s.fr.F) (y54_F_le_L s)
  rw [y54_centIn_L_F hH] at h
  exact h

theorem y54_X0_eq_P {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e)
    (hRT : s.R = s.T) : f4X0 s = f4P s := by
  refine le_antisymm ?_ (y54_P_le_X0 hH)
  intro a ha
  by_contra haP
  have ha2 : a ^ 2 ∈ f4P s := by
    have h := y54_X0_cosets hH a⁻¹ (Subgroup.inv_mem (f4X0 s) ha) a ha
    rcases h with h | h | h
    · exact absurd (by simpa using Subgroup.inv_mem (f4P s) h) haP
    · exact absurd h haP
    · simpa [pow_two] using h
  have hP2 : IsPGroup 2 (f4P s) := IsPGroup.to_le s.sylow_R.2.1 (f4P_le_R s)
  have hQ : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_sq_mem hP2 ha2
  obtain ⟨h, hhH, hconj⟩ :=
    exists_conj_le_isSylowIn s.sylow_T hQ (Subgroup.zpowers_le.mpr ha.1)
  have hxaT : h * a * h⁻¹ ∈ s.T :=
    hconj ((mem_conjSub_iff (Subgroup.zpowers a) h (h * a * h⁻¹)).mpr (by
      have haa : h⁻¹ * (h * a * h⁻¹) * h = a := by group
      rw [haa]
      exact Subgroup.mem_zpowers a))
  have hhN : h ∈ Subgroup.normalizer (L : Set G) := s3_H_le_N s hH.hS hhH
  have hxaM : h * a * h⁻¹ ∈ L ⊔ zpowers s.t := by
    have hxaR : h * a * h⁻¹ ∈ s.R := hRT.symm ▸ hxaT
    rw [s3_R_eq s hH.hS, f3_centIn_H_L hH] at hxaR
    exact (Subgroup.mem_inf.mp hxaR).2
  obtain ⟨ℓ, hℓL, i, hℓi⟩ := y5_mem_L_sup_t s hxaM
  have hF'L : conjSub h s.fr.F ≤ L := by
    intro y hy
    have hyF : h⁻¹ * y * h ∈ s.fr.F := (mem_conjSub_iff s.fr.F h y).mp hy
    have hy_eq : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rw [← hy_eq]
    exact (Subgroup.mem_normalizer_iff.mp hhN (h⁻¹ * y * h)).mp (y54_F_le_L s hyF)
  have hxC' : h * a * h⁻¹ ∈ Subgroup.centralizer (conjSub h s.fr.F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyF : h⁻¹ * y * h ∈ s.fr.F := (mem_conjSub_iff s.fr.F h y).mp hy
    have hya : (h⁻¹ * y * h) * a = a * (h⁻¹ * y * h) :=
      Subgroup.mem_centralizer_iff.mp ha.2 (h⁻¹ * y * h) hyF
    have hy_eq : h * (h⁻¹ * y * h) * h⁻¹ = y := by group
    rw [← hy_eq]
    calc (h * (h⁻¹ * y * h) * h⁻¹) * (h * a * h⁻¹)
        = h * ((h⁻¹ * y * h) * a) * h⁻¹ := by group
      _ = h * (a * (h⁻¹ * y * h)) * h⁻¹ := by rw [hya]
      _ = (h * a * h⁻¹) * (h * (h⁻¹ * y * h) * h⁻¹) := by group
  have htC' : s.t ∈ Subgroup.centralizer (conjSub h s.fr.F : Set G) :=
    Subgroup.centralizer_le hF'L s.t_mem
  have htiC : s.t ^ i ∈ Subgroup.centralizer (conjSub h s.fr.F : Set G) :=
    Subgroup.zpow_mem _ htC' i
  have hℓC : ℓ ∈ Subgroup.centralizer (conjSub h s.fr.F : Set G) := by
    have hℓeq : ℓ = (h * a * h⁻¹) * (s.t ^ i)⁻¹ := by rw [hℓi]; group
    rw [hℓeq]
    exact Subgroup.mul_mem _ hxC' (Subgroup.inv_mem _ htiC)
  have hℓF' : ℓ ∈ conjSub h s.fr.F := by
    rw [← centIn_conjSub_eq_of_centIn_eq hhN (y54_centIn_L_F hH)]
    exact Subgroup.mem_inf.mpr ⟨hℓL, hℓC⟩
  have hℓV : h⁻¹ * ℓ * h ∈ s.fr.F := (mem_conjSub_iff s.fr.F h ℓ).mp hℓF'
  have hth : h⁻¹ * s.t ^ i * h = s.t ^ i := by
    have hcomm : Commute h s.t :=
      (Subgroup.mem_centralizer_iff.mp hhH s.t (by simp)).symm
    have hc := (hcomm.zpow_right i).eq
    calc h⁻¹ * s.t ^ i * h = h⁻¹ * (s.t ^ i * h) := by group
      _ = h⁻¹ * (h * s.t ^ i) := by rw [← hc]
      _ = s.t ^ i := by group
  have ha_eq : a = (h⁻¹ * ℓ * h) * s.t ^ i := by
    calc a = h⁻¹ * (ℓ * s.t ^ i) * h := by rw [← hℓi]; group
      _ = (h⁻¹ * ℓ * h) * (h⁻¹ * s.t ^ i * h) := by group
      _ = (h⁻¹ * ℓ * h) * s.t ^ i := by rw [hth]
  refine haP ?_
  rw [ha_eq]
  exact Subgroup.mul_mem_sup hℓV (Subgroup.zpow_mem _ (Subgroup.mem_zpowers s.t) i)

theorem y54_g_mem_X0 (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g ∈ f4X0 c.s := by
  obtain ⟨hgT, -, hact, hg2, -⟩ := c.g_spec hRT
  refine Subgroup.mem_inf.mpr ⟨c.s.sylow_T.1 hgT, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have hgf := y5_g_cent_F hH hg2 hact f hf
  calc f * c.g = (c.g * f * c.g⁻¹) * c.g := by rw [hgf]
    _ = c.g * f := by group

theorem y54_g_not_mem_P (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    c.g ∉ f4P c.s :=
  fun hgP => (c.g_spec hRT).2.1 (f4P_le_R c.s hgP)

theorem y54_X0_cases_g (c : Ctx5 G L) (hH : F33Hyp c.s c.e) (hRT : c.s.R ≠ c.s.T) :
    ∀ x ∈ f4X0 c.s, x ∈ f4P c.s ∨ c.g * x ∈ f4P c.s := by
  intro x hx
  have hgX0 : c.g ∈ f4X0 c.s := y54_g_mem_X0 c hH hRT
  have hgP : c.g ∉ f4P c.s := y54_g_not_mem_P c hH hRT
  rcases y54_X0_cosets hH c.g hgX0 x hx with h | h | h
  · exact absurd h hgP
  · exact Or.inl h
  · refine Or.inr ?_
    have hginv : c.g⁻¹ = c.g := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_two]
      exact (c.g_spec hRT).2.2.2.1
    rwa [hginv] at h

end CFSG.OddStandard.HigherRank.YamadaG23

module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3B2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Dec
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YF3Nu

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem f3_Y_isPGroup {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsPGroup 2 ↥(f3Y s) := by
  intro g
  have hg : (g : G) ^ 2 ∈ f3P s := f3_Y_sq hH (g : G) g.2
  obtain ⟨k, hk⟩ := f3_P_isPGroup s ⟨(g : G) ^ 2, hg⟩
  refine ⟨k + 1, Subtype.ext ?_⟩
  have hk' : ((g : G) ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [pow_succ' (2 : ℕ) k, pow_mul]
  exact hk'

theorem f3_Y1_le_Y {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3Y1 s ≤ f3Y s := by
  refine sup_le ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    have hb' : b * a * b⁻¹ ∈ f3Y s := (f3_extCtx hH).Y_N b hb a ha
    have hcomm : ⁅a, b⁆ = a * (b * a * b⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact (f3Y s).mul_mem ha ((f3Y s).inv_mem hb')
  · exact (f3_extCtx hH).P_le.trans (f3_extCtx hH).X₀_le

theorem f3_Y1_isPGroup {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    IsPGroup 2 ↥(f3Y1 s) :=
  (f3_Y_isPGroup hH).to_le (f3_Y1_le_Y hH)

theorem f3_C₂_eq_Y1 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    s.C₂ = f3Y1 s := by
  rw [f3_C₂_eq s]
  show (pCore 2 ↥(f3Y1 s)).map (f3Y1 s).subtype = f3Y1 s
  apply le_antisymm (Subgroup.map_subtype_le _)
  intro b hb
  have htop : (⊤ : Subgroup ↥(f3Y1 s)) ≤ pCore 2 ↥(f3Y1 s) :=
    le_sSup ⟨Subgroup.normal_top, (f3_Y1_isPGroup hH).of_equiv Subgroup.topEquiv.symm⟩
  exact ⟨⟨b, hb⟩, htop (Subgroup.mem_top _), rfl⟩

theorem f3_N_conj_k {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {k : G}
    (hk : k ∈ normIn L s.fr.B)
    (hkL : ∀ n ∈ normIn L s.fr.B, ∃ b ∈ s.fr.B, n * k * n⁻¹ = k * b ∨ n * k * n⁻¹ = k⁻¹ * b) :
    ∀ n ∈ f3N s, ∃ p ∈ f3P s, n * k * n⁻¹ = k * p ∨ n * k * n⁻¹ = k⁻¹ * p := by
  intro n hn
  obtain ⟨ℓ, hℓ, a, ha, hn_eq⟩ := f3_N_decomp hH n hn
  obtain ⟨b₀, hb₀, hℓk⟩ := hkL ℓ hℓ
  have haH : a ∈ s.H := ha.1
  have haC : a ∈ centralizer (cen s.fr.B : Set G) := ha.2
  have hkLmem : k ∈ L := hk.1
  have hkN : k ∈ normalizer (s.fr.B : Set G) := hk.2
  have hconjV : ∀ g ∈ normalizer (s.fr.B : Set G), ∀ v ∈ cen s.fr.B,
      g * v * g⁻¹ ∈ cen s.fr.B := by
    intro g hg v hv
    rw [cen, Subgroup.mem_inf] at hv ⊢
    refine ⟨(Subgroup.mem_set_normalizer_iff.mp hg v).mp hv.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hv ⊢
    intro b hb
    have hb' : g⁻¹ * b * g ∈ s.fr.B := (Subgroup.mem_set_normalizer_iff''.mp hg b).mp hb
    calc b * (g * v * g⁻¹)
        = g * ((g⁻¹ * b * g) * v) * g⁻¹ := by group
      _ = g * (v * (g⁻¹ * b * g)) * g⁻¹ := by rw [hv.2 (g⁻¹ * b * g) hb']
      _ = (g * v * g⁻¹) * b := by group
  have hkVinv : ∀ v ∈ cen s.fr.B, k⁻¹ * v * k ∈ cen s.fr.B :=
    fun v hv => by
      simpa using hconjV k⁻¹ ((Subgroup.normalizer (s.fr.B : Set G)).inv_mem hkN) v hv
  have hconjL : a * k * a⁻¹ ∈ L :=
    ((Subgroup.mem_set_normalizer_iff.mp (s3_H_le_N s hH.hS haH)) k).mp hkLmem
  have hcL : a * k * a⁻¹ * k⁻¹ ∈ L := L.mul_mem hconjL (L.inv_mem hkLmem)
  have hcC : a * k * a⁻¹ * k⁻¹ ∈ centralizer (cen s.fr.B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hva : v * a = a * v := (Subgroup.mem_centralizer_iff.mp haC) v hv
    have hkv : k⁻¹ * v * k ∈ cen s.fr.B := hkVinv v hv
    have ha' : (k⁻¹ * v * k) * a⁻¹ = a⁻¹ * (k⁻¹ * v * k) :=
      (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.centralizer (cen s.fr.B : Set G)).inv_mem haC) (k⁻¹ * v * k) hkv)
    calc v * (a * k * a⁻¹ * k⁻¹)
        = (v * a) * k * a⁻¹ * k⁻¹ := by group
      _ = (a * v) * k * a⁻¹ * k⁻¹ := by rw [hva]
      _ = a * (v * k) * a⁻¹ * k⁻¹ := by group
      _ = a * (k * (k⁻¹ * v * k)) * a⁻¹ * k⁻¹ := by group
      _ = a * k * ((k⁻¹ * v * k) * a⁻¹) * k⁻¹ := by group
      _ = a * k * (a⁻¹ * (k⁻¹ * v * k)) * k⁻¹ := by rw [ha']
      _ = (a * k * a⁻¹ * k⁻¹) * v := by group
  have hcB : a * k * a⁻¹ * k⁻¹ ∈ s.fr.B := by
    rw [← f3_centIn_L_V hH]
    exact ⟨hcL, hcC⟩
  have ha_conj : a * k * a⁻¹ = (a * k * a⁻¹ * k⁻¹) * k := by group
  have hb'B : ℓ * (a * k * a⁻¹ * k⁻¹) * ℓ⁻¹ ∈ s.fr.B :=
    (Subgroup.mem_set_normalizer_iff.mp hℓ.2 (a * k * a⁻¹ * k⁻¹)).mp hcB
  have hmain : (ℓ * a) * k * (ℓ * a)⁻¹ =
      (ℓ * (a * k * a⁻¹ * k⁻¹) * ℓ⁻¹) * (ℓ * k * ℓ⁻¹) := by
    have h1 : (ℓ * a) * k * (ℓ * a)⁻¹ = ℓ * (a * k * a⁻¹) * ℓ⁻¹ := by group
    rw [h1, ha_conj]
    group
  rw [hn_eq, hmain]
  rcases hℓk with hℓk | hℓk
  · refine ⟨k⁻¹ * (ℓ * (a * k * a⁻¹ * k⁻¹) * ℓ⁻¹) * k * b₀,
      (f3P s).mul_mem
        (Subgroup.mem_sup_left ((Subgroup.mem_set_normalizer_iff''.mp hkN _).mp hb'B))
        (Subgroup.mem_sup_left hb₀), Or.inl ?_⟩
    rw [hℓk]
    group
  · refine ⟨k * (ℓ * (a * k * a⁻¹ * k⁻¹) * ℓ⁻¹) * k⁻¹ * b₀,
      (f3P s).mul_mem
        (Subgroup.mem_sup_left ((Subgroup.mem_set_normalizer_iff.mp hkN _).mp hb'B))
        (Subgroup.mem_sup_left hb₀), Or.inr ?_⟩
    rw [hℓk]
    group

theorem f3_hfix {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {k : G}
    (hk : k ∈ normIn L s.fr.B) (hkv : ∀ v ∈ cen s.fr.B, k * v * k⁻¹ = v → v = 1) :
    ∀ y ∈ f3Y s, y⁻¹ * (k * y * k⁻¹) ∈ f3X0 s → y ∈ f3X0 s := by
  intro y hy hz
  have hkH : k ∈ s.H := s3_L_le_H s hH.hS hk.1
  have hkX : k ∈ s.X := f3_N_le_X s ⟨hkH, hk.2⟩
  have hky : k * y * k⁻¹ ∈ f3Y s := f3_Y_normal hH k hkX y hy
  have hyinv : y⁻¹ ∈ f3Y s := (f3Y s).inv_mem hy
  have hzY : y⁻¹ * (k * y * k⁻¹) ∈ f3Y s := (f3Y s).mul_mem hyinv hky
  have hphi_z : f3phi s (y⁻¹ * (k * y * k⁻¹)) = 1 :=
    (f3_phi_eq_one hH (y⁻¹ * (k * y * k⁻¹)) hzY).mpr hz
  have hmul := f3_phi_mul hH y⁻¹ hyinv (k * y * k⁻¹) hky
  have hphi_inv : f3phi s y⁻¹ = (f3phi s y)⁻¹ := by
    have h1 : f3phi s (y⁻¹ * y) = f3phi s y⁻¹ * f3phi s y :=
      f3_phi_mul hH y⁻¹ hyinv y hy
    have h0 : f3phi s (y⁻¹ * y) = 1 := by
      rw [inv_mul_cancel]
      simp [f3phi]
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have hkcomm : k * s.t = s.t * k := (Subgroup.mem_centralizer_iff.mp s.t_mem) k hk.1
  have hconj := f3_phi_conj s hkcomm y
  have heq : (f3phi s y)⁻¹ * (k * f3phi s y * k⁻¹) = 1 := by
    calc (f3phi s y)⁻¹ * (k * f3phi s y * k⁻¹)
        = f3phi s y⁻¹ * f3phi s (k * y * k⁻¹) := by rw [hphi_inv, hconj]
      _ = f3phi s (y⁻¹ * (k * y * k⁻¹)) := hmul.symm
      _ = 1 := hphi_z
  have hfixv : k * f3phi s y * k⁻¹ = f3phi s y := (inv_mul_eq_one.mp heq).symm
  exact (f3_phi_eq_one hH y hy).mp (hkv (f3phi s y) (f3_phi_mem hH y hy) hfixv)

theorem f3_Y1_inf_X0 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    f3Y1 s ⊓ f3X0 s = f3P s := by
  refine le_antisymm ?_ (le_inf le_sup_right (f3_P_le_X0 s))
  intro x hx
  obtain ⟨hxY1, hxX0⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk, hk3, _, hkv, _, hknorm⟩ := f3_exists_k hH
  have hkH : k ∈ s.H := s3_L_le_H s hH.hS hk.1
  exact ext_nu (f3_extCtx hH) (f3_Y_sq hH) ⟨hkH, hk.2⟩
    (by rw [hk3]; exact (f3P s).one_mem) (f3_N_conj_k hH hk hknorm) (f3_hfix hH hk hkv)
    x hxX0 hxY1

end CFSG.OddStandard.HigherRank.YamadaG23

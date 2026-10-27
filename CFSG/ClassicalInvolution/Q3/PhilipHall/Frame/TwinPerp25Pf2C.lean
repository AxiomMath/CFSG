module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf2G
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpWz
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25Pf2B

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S

open CFSG.ClassicalInvolution.Asc77.C25Y (GoodFusion)
open CFSG.ClassicalInvolution.Asc77.C25H (zpow_eq_one_or_self)
open CFSG.ClassicalInvolution.Asc77.C25W (InFour mem_zStarOf_centralizer_conj_iff good_of_mem_zpowers exists_sq_mem_mod exists_conj_ge_sylow)
open CFSG.ClassicalInvolution.Asc77.C25Y (mem_closure_pair)
open scoped commutatorElement

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

@[expose] def P25_SqZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ cA S R R', a * a = 1 → a ≠ 1 →
      (∀ x ∈ R, a * x = x * a) → (∀ x ∈ R', a * x = x * a) → BadElt z a →
      ∀ g x : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) →
        x ∈ Subgroup.centralizer ({a} : Set G) → x * x = g * z * g⁻¹ → x * x * x * x = 1 →
        ∃ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ = g * z * g⁻¹

@[expose] def P25_CentExt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [CoreLike G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ cA S R R', a * a = 1 → a ≠ 1 → a ≠ z →
      (∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) → BadElt z a →
      ∀ y ∈ cA S R R', y * a = a * y → InFour a z (y * y) →
        (∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) → InFour a z y

structure FourData (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (a : G) : Prop where
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haz : a ≠ z
  haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
  hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z
  hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
    b = 1 ∨ b = a ∨ b = z ∨ b = a * z

namespace FourData

variable {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G}

theorem haS (h : FourData hyp a) : a ∈ (S : Subgroup G) := h.haA.1

theorem haz_comm (h : FourData hyp a) : a * z = z * a := hyp.hzS a h.haS

theorem hz2 (_h : FourData hyp a) : z * z = 1 := hyp.std.setting.hz.sq

theorem hz1 (_h : FourData hyp a) : z ≠ 1 := hyp.std.setting.hz.ne_one

theorem haR (h : FourData hyp a) : ∀ x ∈ R, a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp h.haA.2) x (Subgroup.mem_sup_left hx)).symm

theorem haR' (h : FourData hyp a) : ∀ x ∈ R', a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp h.haA.2) x (Subgroup.mem_sup_right hx)).symm

theorem haK (h : FourData hyp a) : a ∈ trivialOnQuot K ∧ a ∈ trivialOnQuot K' := by
  exact ⟨trivialOnQuot_of_centralizes hyp h.ha2 h.haR, trivialOnQuot_of_centralizes' hyp h.ha2 h.haR'⟩

theorem mem_center (h : FourData hyp a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({a * z} : Set G))) :
    ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a := by
  intro s hs
  rcases h.hconj s hs with h1 | h1
  · exact h1
  · exfalso
    have hsz : s * z * s⁻¹ = z := by
      calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
        _ = z := by group
    have h2 := (mem_zStarOf_centralizer_conj_iff (z := z) (a := a) (c := s) hsz).mp
      (by rw [h1]; exact hgood)
    exact hbad h2

end FourData

theorem comm_of_mem_sylow {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G}
    (h : FourData hyp a) (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({a * z} : Set G)))
    {V : Subgroup G} (hV2 : IsPGroup 2 V) (haV : a ∈ V) (hzV : z ∈ V) :
    ∀ y ∈ V, (y * z = z * y ∨ y * (a * z) = (a * z) * y) → y * a = a * y := by
  intro y hy hyc
  have hz2 := h.hz2
  have hcen := h.mem_center hbad hgood
  have haz' := h.haz_comm
  rcases hyc with hyz | hyaz
  ·
    have hSH : (S : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS s hs)
    have hT2 : IsPGroup 2 (V ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G) :=
      hV2.to_le inf_le_left
    obtain ⟨c, hc, hcT⟩ := exists_conj_ge_sylow hSH hT2 inf_le_right
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hczc : c * z * c⁻¹ = z := by
      calc c * z * c⁻¹ = (z * c) * c⁻¹ := by rw [hcz]
        _ = z := by group
    have hczc' : c⁻¹ * z * c⁻¹⁻¹ = z := by
      calc c⁻¹ * z * c⁻¹⁻¹ = c⁻¹ * (c * z * c⁻¹) * c⁻¹⁻¹ := by rw [hczc]
        _ = z := by group
    have haT : a ∈ V ⊓ Subgroup.centralizer ({z} : Set G) :=
      ⟨haV, Subgroup.mem_centralizer_singleton_iff.mpr haz'⟩
    have ha'S : c⁻¹ * a * c ∈ (S : Subgroup G) := hcT a haT
    have ha'A := conj_mem_Csub hyp h.haK.1 h.haK.2 hczc'
      (by simpa using ha'S : c⁻¹ * a * c⁻¹⁻¹ ∈ (S : Subgroup G))
    have ha'eq : c⁻¹ * a * c = a := by
      have ha'A' : c⁻¹ * a * c ∈ (S : Subgroup G) ⊓
          Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) := by simpa using ha'A
      rcases h.hA0 _ ha'A' with h1 | h1 | h1 | h1
      · exfalso
        apply h.ha1
        calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
          _ = 1 := by rw [h1]; group
      · exact h1
      · exfalso
        apply h.haz
        calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
          _ = c * z * c⁻¹ := by rw [h1]
          _ = z := hczc
      · exfalso
        have := (mem_zStarOf_centralizer_conj_iff (z := z) (a := a) (c := c⁻¹) hczc').mp
          (by rw [show c⁻¹ * a * c⁻¹⁻¹ = a * z by simpa using h1]; exact hgood)
        exact hbad this
    have hac : a * c = c * a := by
      calc a * c = c * (c⁻¹ * a * c) := by group
        _ = c * a := by rw [ha'eq]
    have hy' : c⁻¹ * y * c ∈ (S : Subgroup G) :=
      hcT y ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr hyz⟩
    have h2 : (c⁻¹ * y * c) * a * (c⁻¹ * y * c)⁻¹ = a := hcen _ hy'
    have h3 : (c⁻¹ * y * c) * a = a * (c⁻¹ * y * c) := by
      calc (c⁻¹ * y * c) * a = (c⁻¹ * y * c) * a * (c⁻¹ * y * c)⁻¹ * (c⁻¹ * y * c) := by group
        _ = a * (c⁻¹ * y * c) := by rw [h2]
    calc y * a = c * ((c⁻¹ * y * c) * (c⁻¹ * a * c)) * c⁻¹ := by group
      _ = c * ((c⁻¹ * y * c) * a) * c⁻¹ := by rw [ha'eq]
      _ = c * (a * (c⁻¹ * y * c)) * c⁻¹ := by rw [h3]
      _ = c * ((c⁻¹ * a * c) * (c⁻¹ * y * c)) * c⁻¹ := by rw [ha'eq]
      _ = a * y := by group
  ·
    have hTV : Subgroup.closure ({y, z} : Set G) ≤ V := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hy
      · exact hzV
    have hT2 : IsPGroup 2 (Subgroup.closure ({y, z} : Set G)) := hV2.to_le hTV
    have hzaz : z * (a * z) = (a * z) * z := by
      calc z * (a * z) = (z * a) * z := by group
        _ = (a * z) * z := by rw [haz']
    have hTC : Subgroup.closure ({y, z} : Set G) ≤ Subgroup.centralizer ({a * z} : Set G) := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyaz
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzaz
    have hzT : z ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hyT : y ∈ Subgroup.closure ({y, z} : Set G) := Subgroup.subset_closure (by simp)
    have hyz : y * z = z * y :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (T7T.le_centralizer_of_mem_zStarOf hgood hzT hTC hT2 hyT)
    calc y * a = y * ((a * z) * z) := by rw [mul_assoc, hz2, mul_one]
      _ = (y * (a * z)) * z := by group
      _ = ((a * z) * y) * z := by rw [hyaz]
      _ = (a * z) * (y * z) := by group
      _ = (a * z) * (z * y) := by rw [hyz]
      _ = ((a * z) * z) * y := by group
      _ = a * y := by rw [mul_assoc a z z, hz2, mul_one]
theorem no_mixed (hSq : P25_SqZ)
    {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G} (h : FourData hyp a)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hgood : z ∈ zStarOf (Subgroup.centralizer ({a * z} : Set G))) : False := by
  classical
  have hs : Hyp23Setting Ω K K' z := hyp.std.setting
  have hst := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hz : IsUniqueInvolution K z := hs.hz
  have hz2 := h.hz2
  have hz1 := h.hz1
  have haz' := h.haz_comm
  
  have hcen := h.mem_center hbad hgood
  obtain ⟨g, hgS, hgC, hgn⟩ := exists_exceptional_in_S hcen hz2
    (not_goodFusion hyp h.ha2 h.ha1 h.haz h.haA h.hconj h.hA0)
  have htz : (g * z * g⁻¹) * z = z * (g * z * g⁻¹) := hyp.hzS _ hgS
  have hta : (g * z * g⁻¹) * a = a * (g * z * g⁻¹) :=
    Subgroup.mem_centralizer_singleton_iff.mp hgC
  
  set A₄ : Subgroup G := Subgroup.closure ({a, z} : Set G) with hA₄
  have hE : IsElemAbelian2 A₄ 2 :=
    T7A.isElemAbelian2_closure_pair h.ha2 hz2 h.ha1 hz1 h.haz haz'
  have hA2 : IsPGroup 2 A₄ := IsPGroup.of_card (n := 2) hE.1
  have haA₄ : a ∈ A₄ := Subgroup.subset_closure (by simp)
  have hzA₄ : z ∈ A₄ := Subgroup.subset_closure (by simp)
  have hAC : A₄ ≤ Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
    rw [hA₄, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hta.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr htz.symm
  obtain ⟨V, hV, hAV⟩ := IsSylow2In.exists_ge hA2 hAC
  have haV : a ∈ V := hAV haA₄
  have hzV : z ∈ V := hAV hzA₄
  have hJ : conjSub g K ∈ Ω := hΩ.conjInvariant g K hst.mem
  have htJ : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hz.conj g
  have hP : PartIHyp Ω := ⟨hΩ, hst.cls, hst.aEmpty⟩
  have hΓ : gamma1 A₄ (V ⊓ ⨆ L ∈ twinSet Ω (conjSub g K), L) ≤
      Subgroup.centralizer ({a} : Set G) := by
    unfold gamma1
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    intro y hy
    obtain ⟨⟨hyV, -⟩, hyw⟩ := (Subgroup.mem_inf.mp hy) |>.imp Subgroup.mem_inf.mp id
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyw' : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp hyw
    rcases mem_closure_pair h.ha2 hz2 haz' hw with h1 | h1 | h1 | h1
    · exact absurd h1 hw1
    · rw [h1] at hyw'
      exact hyw'
    · rw [h1] at hyw'
      exact comm_of_mem_sylow h hbad hgood hV.2.1 haV hzV y hyV (Or.inl hyw')
    · rw [h1] at hyw'
      exact comm_of_mem_sylow h hbad hgood hV.2.1 haV hzV y hyV (Or.inr hyw')
  
  obtain ⟨x, hxJ, hx4, hxa⟩ := CFSG.ClassicalInvolution.Q3.Q3CL.l9_3 hP (conjSub g K) hJ (g * z * g⁻¹) htJ V
    hV A₄ hAV hE a haA₄ h.ha1 hΓ
  have hxx : x * x = g * z * g⁻¹ := CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.sq_eq_of_orderOf_four htJ hxJ hx4
  have hx4' : x * x * x * x = 1 := by
    have h1 : x ^ 4 = 1 := by
      have := pow_orderOf_eq_one x
      rwa [hx4] at this
    calc x * x * x * x = x ^ 4 := by simp only [pow_succ, pow_zero, one_mul]
      _ = 1 := h1
  have hxC : x ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxa
  obtain ⟨h', hh'C, hh'⟩ := hSq G Ω K K' W S R R' z t u₁ u₂ hyp a h.haA h.ha2 h.ha1 h.haR h.haR' hbad g x hgC
    hxC hxx hx4'
  exact hgn h' hh'C hh'
theorem twisted_false {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a y : G}
    (ha2 : a * a = 1)
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hyA : y ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (hy2 : InFour a z (y * y))
    (hyc : ∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹))
    (hyaz : y * a * y⁻¹ = a * z) : False := by
  have haS : a ∈ (S : Subgroup G) := haA.1
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have haz' : a * z = z * a := hyp.hzS a haS
  have hyS : y ∈ (S : Subgroup G) := hyA.1
  have hyz : y * z = z * y := hyp.hzS y hyS
  have hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z := by
    intro s hs
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
      _ = z := by group
  have hya : y * a = a * z * y := by
    calc y * a = (y * a * y⁻¹) * y := by group
      _ = a * z * y := by rw [hyaz]
  have hcomm_false : y * a = a * y → False := by
    intro hc
    have h1 : y * a * y⁻¹ = a := by rw [hc]; group
    rw [hyaz] at h1
    exact hz1 (mul_left_cancel (a := a) (b := z) (c := 1) (by rw [mul_one]; exact h1))
  have hy2' : y * y = 1 ∨ y * y = z := by
    rcases hy2 with h | h | h | h
    · exact Or.inl h
    · exfalso
      apply hcomm_false
      calc y * a = y * (y * y) := by rw [h]
        _ = (y * y) * y := by group
        _ = a * y := by rw [h]
    · exact Or.inr h
    · exfalso
      apply hcomm_false
      have h1 : y * (a * z) = (a * z) * y := by
        calc y * (a * z) = y * (y * y) := by rw [h]
          _ = (y * y) * y := by group
          _ = (a * z) * y := by rw [h]
      have h2 : (y * a) * z = (a * y) * z := by
        calc (y * a) * z = y * (a * z) := by group
          _ = (a * z) * y := h1
          _ = a * (z * y) := by group
          _ = a * (y * z) := by rw [hyz]
          _ = (a * y) * z := by group
      exact mul_right_cancel h2
  have hFc := conj_mem_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  have hFyc : ∀ s ∈ (S : Subgroup G),
      s * y * s⁻¹ * y⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := fun s hs =>
    (inFour_iff_mem_closure ha2 hz2 haz').mp (hyc s hs)
  obtain ⟨y', hy'A, hy'sq, hy'a, hy'c⟩ : ∃ y' : G,
      y' ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) ∧
      y' * y' = z ∧ y' * a = a * z * y' ∧
      ∀ s ∈ (S : Subgroup G), s * y' * s⁻¹ * y'⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
    rcases hy2' with h | h
    ·
      refine ⟨y * a, Subgroup.mul_mem _ hyA haA, ?_, ?_, ?_⟩
      · calc y * a * (y * a) = (y * a * y⁻¹) * (y * y) * a := by group
          _ = a * z * 1 * a := by rw [hyaz, h]
          _ = a * (z * a) := by rw [mul_one]; group
          _ = a * (a * z) := by rw [haz']
          _ = (a * a) * z := by group
          _ = z := by rw [ha2, one_mul]
      · calc y * a * a = y := by rw [mul_assoc, ha2, mul_one]
          _ = a * z * (a * z * y) := by
            calc y = (a * z * a * z) * y := by
                  have : a * z * a * z = 1 := by
                    calc a * z * a * z = a * (z * a) * z := by group
                      _ = a * (a * z) * z := by rw [haz']
                      _ = (a * a) * (z * z) := by group
                      _ = 1 := by rw [ha2, hz2, one_mul]
                  rw [this, one_mul]
              _ = a * z * (a * z * y) := by group
          _ = a * z * (y * a) := by rw [hya]
      · intro s hs
        have hsa : s * a * s⁻¹ * a⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
          have := hFc s hs a (Subgroup.subset_closure (by simp))
          exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
        have h3 := Subgroup.mul_mem _ (hFyc s hs) (hFc y hyS _ hsa)
        convert h3 using 1
        group
    · exact ⟨y, hyA, h, hya, hFyc⟩
  have hy'S : y' ∈ (S : Subgroup G) := hy'A.1
  have hy'z : y' * z = z * y' := hyp.hzS y' hy'S
  have hy'az : y' * (a * z) = a * y' := by
    calc y' * (a * z) = (y' * a) * z := by group
      _ = (a * z * y') * z := by rw [hy'a]
      _ = a * z * (y' * z) := by group
      _ = a * z * (z * y') := by rw [hy'z]
      _ = a * (z * z) * y' := by group
      _ = a * y' := by rw [hz2, mul_one]
  have haz4 : a * z * a * z = 1 := by
    calc a * z * a * z = a * (z * a) * z := by group
      _ = a * (a * z) * z := by rw [haz']
      _ = (a * a) * (z * z) := by group
      _ = 1 := by rw [ha2, hz2, one_mul]
  have hy'zp : z ∈ Subgroup.zpowers y' := ⟨2, by show y' ^ (2 : ℤ) = z; rw [zpow_two, hy'sq]⟩
  have hBc : ∀ s ∈ (S : Subgroup G), s * y' * s⁻¹ ∈ Subgroup.zpowers y' := by
    intro s hs
    set w := s * y' * s⁻¹ with hw
    have hww : w * w = z := by
      calc w * w = s * (y' * y') * s⁻¹ := by rw [hw]; group
        _ = z := by rw [hy'sq, hzS s hs]
    have hwf : w = (w * y'⁻¹) * y' := by group
    have hf := hy'c s hs
    rcases mem_closure_pair ha2 hz2 haz' hf with h | h | h | h
    · have : w = y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = y'; rw [h, one_mul]
      rw [this]
      exact Subgroup.mem_zpowers y'
    · exfalso
      have hw' : w = a * y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = a * y'; rw [h]
      have h1 : (a * y') * (a * y') = 1 := by
        calc (a * y') * (a * y') = a * (y' * a) * y' := by group
          _ = a * (a * z * y') * y' := by rw [hy'a]
          _ = (a * a) * z * (y' * y') := by group
          _ = 1 := by rw [ha2, hy'sq, one_mul, hz2]
      rw [hw', h1] at hww
      exact hz1 hww.symm
    · have : w = z * y' := by rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = z * y'; rw [h]
      rw [this]
      exact Subgroup.mul_mem _ hy'zp (Subgroup.mem_zpowers y')
    · exfalso
      have hw' : w = a * z * y' := by
        rw [hwf]; show (s * y' * s⁻¹ * y'⁻¹) * y' = a * z * y'; rw [h]
      have h1 : (a * z * y') * (a * z * y') = 1 := by
        calc (a * z * y') * (a * z * y') = a * z * (y' * (a * z)) * y' := by group
          _ = a * z * (a * y') * y' := by rw [hy'az]
          _ = (a * z * a) * (y' * y') := by group
          _ = (a * z * a) * z := by rw [hy'sq]
          _ = 1 := haz4
      rw [hw', h1] at hww
      exact hz1 hww.symm
  have hBc' : ∀ s ∈ (S : Subgroup G), ∀ b ∈ Subgroup.zpowers y',
      s * b * s⁻¹ ∈ Subgroup.zpowers y' := by
    intro s hs b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ (hBc s hs) k
  have hBn : ∀ s ∈ (S : Subgroup G), conjSub s (Subgroup.zpowers y') = Subgroup.zpowers y' := by
    intro s hs
    ext x
    rw [mem_conjSub_iff]
    constructor
    · intro hx
      have := hBc' s hs _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hBc' s⁻¹ ((S : Subgroup G).inv_mem hs) _ hx
      simpa [mul_assoc] using this
  have hBS : Subgroup.zpowers y' ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hy'S
  have hall : ∀ b ∈ Subgroup.zpowers y', b ≠ 1 →
      z ∈ zStarOf (Subgroup.centralizer ({b} : Set G)) := fun b hb hb1 =>
    good_of_mem_zpowers (z_mem_zpowers_of_sq hy'sq hz2 hb hb1)
  have hE := T7T.c25_5_proved G Ω K K' W S R R' z t u₁ u₂ hyp
    (Subgroup.zpowers y') hy'zp hBS hBn hall
  have hy'z' : y' ∈ Subgroup.zpowers z := hE ▸ Subgroup.mem_zpowers y'
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'z'
  have h1 : y' * y' = 1 := by
    rcases zpow_eq_one_or_self hz2 k with h | h
    · rw [← hk, h]; simp
    · rw [← hk, h]; exact hz2
  rw [hy'sq] at h1
  exact hz1 h1
theorem fourExhausts_of_centExt (hExt : P25_CentExt)
    {hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂} {a : G}
    (haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G))
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hbad : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G))) :
    ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
      InFour a z b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨b, hbA, hbF⟩ := hcon
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have haS : a ∈ (S : Subgroup G) := haA.1
  have haz' : a * z = z * a := hyp.hzS a haS
  have hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z := by
    intro s hs
    calc s * z * s⁻¹ = (z * s) * s⁻¹ := by rw [hyp.hzS s hs]
      _ = z := by group
  have hzA := (z_facts hyp).1
  set A : Subgroup G := (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
    with hA
  set F : Subgroup G := Subgroup.closure ({a, z} : Set G) with hF
  have hFA : F ≤ A := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact haA
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hzA
  have hFne : F ≠ A := by
    intro hFA'
    apply hbF
    exact (inFour_iff_mem_closure ha2 hz2 haz').mpr (by rw [← hF, hFA']; exact hbA)
  have hAn : ∀ s ∈ (S : Subgroup G), conjSub s A = A := fun s hs =>
    cA_normal hyp hs
  have hFn := conjSub_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  have hFc := conj_mem_closure_pair (S := S) ha2 hz2 haz' hconj hzS
  obtain ⟨y, hyA, hyF, hy2, hyc⟩ := exists_sq_mem_mod S.isPGroup' inf_le_left hAn hFA hFn hFne
  have hyS : y ∈ (S : Subgroup G) := hyA.1
  have hyaF : y * a * y⁻¹ ∈ F := hFc y hyS a (Subgroup.subset_closure (by simp))
  rcases mem_closure_pair ha2 hz2 haz' hyaF with h | h | h | h
  · exfalso
    apply ha1
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group
  · apply hyF
    have hcomm : y * a = a * y := by
      calc y * a = (y * a * y⁻¹) * y := by group
        _ = a * y := by rw [h]
    exact (inFour_iff_mem_closure ha2 hz2 haz').mp
      (hExt G Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hcomm
        ((inFour_iff_mem_closure ha2 hz2 haz').mpr hy2)
        fun s hs => (inFour_iff_mem_closure ha2 hz2 haz').mpr (hyc s hs))
  · exfalso
    apply haz
    calc a = y⁻¹ * (y * a * y⁻¹) * y := by group
      _ = y⁻¹ * z * y := by rw [h]
      _ = z := by
        have := hyp.hzS y hyS
        calc y⁻¹ * z * y = y⁻¹ * (z * y) := by group
          _ = y⁻¹ * (y * z) := by rw [this]
          _ = z := by group
  · exact twisted_false (hyp := hyp) ha2 haA hconj hyA
      ((inFour_iff_mem_closure ha2 hz2 haz').mpr hy2)
      (fun s hs => (inFour_iff_mem_closure ha2 hz2 haz').mpr (hyc s hs)) h
end CFSG.ClassicalInvolution.Q8P.Asc77.P25S

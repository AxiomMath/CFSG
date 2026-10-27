module

public import CFSG.ClassicalInvolution.Asc77.AscC25W1
public import CFSG.ClassicalInvolution.Asc77.AscC25Y2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped commutatorElement

namespace C25W

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {z : G} {S : Sylow 2 G} {R R' : Subgroup G}
  {t u₁ u₂ : G}


theorem sylow_le_centralizer_of_central {a : G} {S : Sylow 2 G}
    (hcen : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc s * a = (s * a * s⁻¹) * s := by group
    _ = a * s := by rw [hcen s hs]

structure FourData (hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂) (a : G) : Prop where
  ha2 : a * a = 1
  ha1 : a ≠ 1
  haz : a ≠ z
  haA : a ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G)
  hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z
  hA0 : ∀ b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G),
    b = 1 ∨ b = a ∨ b = z ∨ b = a * z

namespace FourData

variable {hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂} {a : G}

theorem haS (h : FourData hyp a) : a ∈ (S : Subgroup G) := h.haA.1

theorem haz_comm (h : FourData hyp a) : a * z = z * a := hyp.hzS a h.haS

theorem hz2 (_h : FourData hyp a) : z * z = 1 := hyp.std.setting.hz.sq

theorem hz1 (_h : FourData hyp a) : z ≠ 1 := hyp.std.setting.hz.ne_one

theorem haR (h : FourData hyp a) : ∀ x ∈ R, a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp h.haA.2) x (Subgroup.mem_sup_left hx)).symm

theorem haR' (h : FourData hyp a) : ∀ x ∈ R', a * x = x * a := fun x hx =>
  ((Subgroup.mem_centralizer_iff.mp h.haA.2) x (Subgroup.mem_sup_right hx)).symm

theorem haK (h : FourData hyp a) : a ∈ trivialOnQuot K ∧ a ∈ trivialOnQuot K' := by
  obtain ⟨-, -, -, hK₂, hK₂', -⟩ := C25X.layer_a_frame hyp h.ha2 h.ha1 h.haR h.haR'
  exact ⟨hK₂.2, hK₂'.2⟩

theorem hazA (h : FourData hyp a) :
    a * z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
  Subgroup.mul_mem _ h.haA (T7T.z_mem_centralizer_of_hyp hyp)

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

theorem exists_exceptional_in_S {a : G}
    (hcen : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a) (hz2 : z * z = 1)
    (hnGF : ¬ C25Y.GoodFusion z a) :
    ∃ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) ∧
      g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) ∧
      ∀ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ ≠ g * z * g⁻¹ := by
  unfold C25Y.GoodFusion at hnGF
  push Not at hnGF
  obtain ⟨w, hwC, hw⟩ := hnGF
  have hSH : (S : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) :=
    sylow_le_centralizer_of_central hcen
  have hb2 : (w * z * w⁻¹) * (w * z * w⁻¹) = 1 := by
    calc (w * z * w⁻¹) * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hT2 : IsPGroup 2 (Subgroup.zpowers (w * z * w⁻¹)) := isPGroup_zpowers_of_sq_eq_one hb2
  have hTH : Subgroup.zpowers (w * z * w⁻¹) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.zpowers_le.mpr hwC
  obtain ⟨c, hc, hcT⟩ := exists_conj_ge_sylow hSH hT2 hTH
  refine ⟨c⁻¹ * w, ?_, ?_, ?_⟩
  · have := hcT (w * z * w⁻¹) (Subgroup.mem_zpowers _)
    convert this using 1
    group
  · have h1 : c⁻¹ * (w * z * w⁻¹) * c ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hwC) hc
    convert h1 using 1
    group
  · intro h hh heq
    apply hw (c * h) (Subgroup.mul_mem _ hc hh)
    calc c * h * z * (c * h)⁻¹ = c * (h * z * h⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * w * z * (c⁻¹ * w)⁻¹) * c⁻¹ := by rw [heq]
      _ = w * z * w⁻¹ := by group

theorem comm_of_mem_sylow {hyp : Hyp25 p f Ω K K' W S R R' z t u₁ u₂} {a : G}
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
    have ha'A := C25Y.conj_mem_Csub hyp h.haK.1 h.haK.2 hczc'
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

end C25W

end CFSG.ClassicalInvolution.Asc77

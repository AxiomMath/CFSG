module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2J
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4K2L31

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.K2
open scoped commutatorElement

section Conj

variable {G : Type} [Group G]

theorem k2_mem_map_conj {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem k2_mem_normalizer_map_conj {K : Subgroup G} {z : G} (x : G)
    (hz : z ∈ normalizer (K : Set G)) :
    x * z * x⁻¹ ∈ normalizer ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hz ⊢
  intro h
  rw [k2_mem_map_conj, k2_mem_map_conj]
  have := hz (x⁻¹ * h * x)
  have e : x⁻¹ * (x * z * x⁻¹ * h * (x * z * x⁻¹)⁻¹) * x = z * (x⁻¹ * h * x) * z⁻¹ := by
    group
  rw [e]
  exact this

theorem k2_mem_centralizer_map_conj {K : Subgroup G} {y : G} (x : G) :
    x * y * x⁻¹ ∈ centralizer ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ↔
      y ∈ centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h k hk
    have := h (x * k * x⁻¹) ⟨k, hk, by simp [MulAut.conj_apply]⟩
    have e1 : x * k * x⁻¹ * (x * y * x⁻¹) = x * (k * y) * x⁻¹ := by group
    have e2 : x * y * x⁻¹ * (x * k * x⁻¹) = x * (y * k) * x⁻¹ := by group
    rw [e1, e2] at this
    have := mul_left_cancel (mul_right_cancel this)
    exact this
  · rintro h _ ⟨k, hk, rfl⟩
    have := h k hk
    show x * k * x⁻¹ * (x * y * x⁻¹) = x * y * x⁻¹ * (x * k * x⁻¹)
    calc x * k * x⁻¹ * (x * y * x⁻¹) = x * (k * y) * x⁻¹ := by group
      _ = x * (y * k) * x⁻¹ := by rw [this]
      _ = x * y * x⁻¹ * (x * k * x⁻¹) := by group

theorem k2_comm_map_conj {K : Subgroup G} {z : G} (x : G) (h : ⁅K, zpowers z⁆ = K) :
    ⁅K.map (MulAut.conj x).toMonoidHom, zpowers (x * z * x⁻¹)⁆ =
      K.map (MulAut.conj x).toMonoidHom := by
  have h1 := Subgroup.map_commutator (f := (MulAut.conj x).toMonoidHom) (H₁ := K)
    (H₂ := zpowers z)
  rw [h, MonoidHom.map_zpowers] at h1
  have e : (MulAut.conj x).toMonoidHom z = x * z * x⁻¹ := by simp [MulAut.conj_apply]
  rw [e] at h1
  exact h1.symm

end Conj

section Main

variable {G : Type} [Group G]

@[expose] def KATwoComps : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S : Subgroup G), Stage2Ctx G z k S →
    ∀ H J J' : Subgroup G, H ≠ ⊤ → IsCompIn H J → IsCompIn H J' → J ≠ J' →
      KATwoY (↥J ⧸ center ↥J)

theorem ivk_8_13_two_of_KA (hKA : KATwoComps) : IVK_8_13_two := by
  intro G _ _ z k S hctx H J₁ J₂ hH hJ₁ hJ₂ hne hz2' hz₁ hz₂ hJ₁z hJ₂z x hxH hx₁ hx₂ p P hp hp2
    hPp hPHN hPz hPnorm hPnc₁ hPnc₂
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2', pow_two] at this
  have hq₁ : IsQuasisimple ↥J₁ := K0.quasisimple_of_isCompIn hJ₁
  have hq₂ : IsQuasisimple ↥J₂ := K0.quasisimple_of_isCompIn hJ₂
  have hcomm : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a := comps_commute hJ₁ hJ₂ hne
  set f : G →* G := (MulAut.conj x).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj x).injective
  set z' : G := x * z * x⁻¹ with hz'
  set P' : Subgroup G := P.map f with hP'
  have hz'2 : z' * z' = 1 := by
    rw [hz']
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hz'₁ : z' ∈ normalizer (J₁ : Set G) := by
    have := k2_mem_normalizer_map_conj (K := J₂) x hz₂
    rwa [hx₂] at this
  have hz'₂ : z' ∈ normalizer (J₂ : Set G) := by
    have := k2_mem_normalizer_map_conj (K := J₁) x hz₁
    rwa [hx₁] at this
  have hJ₁z' : ⁅J₁, zpowers z'⁆ = J₁ := by
    have := k2_comm_map_conj (K := J₂) x hJ₂z
    rwa [hx₂] at this
  have hJ₂z' : ⁅J₂, zpowers z'⁆ = J₂ := by
    have := k2_comm_map_conj (K := J₁) x hJ₁z
    rwa [hx₁] at this
  have hP'p : IsPGroup p ↥P' := IsPGroup.of_equiv hPp (Subgroup.equivMapOfInjective P f hfinj)
  have hPN₁ : P ≤ normalizer (J₁ : Set G) := fun y hy => (hPHN hy).1.2
  have hPN₂ : P ≤ normalizer (J₂ : Set G) := fun y hy => (hPHN hy).2
  have hP'N₁ : P' ≤ normalizer (J₁ : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have := k2_mem_normalizer_map_conj (K := J₂) x (hPN₂ hy)
    rw [hx₂] at this
    simpa [hf, MulAut.conj_apply] using this
  have hP'N₂ : P' ≤ normalizer (J₂ : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have := k2_mem_normalizer_map_conj (K := J₁) x (hPN₁ hy)
    rw [hx₁] at this
    simpa [hf, MulAut.conj_apply] using this
  have hP'nc₁ : ¬ P' ≤ centralizer (J₁ : Set G) := by
    intro h
    apply hPnc₂
    intro y hy
    have h1 : x * y * x⁻¹ ∈ centralizer (J₁ : Set G) := h ⟨y, hy, by simp [hf, MulAut.conj_apply]⟩
    rw [← hx₂] at h1
    exact (k2_mem_centralizer_map_conj x).mp h1
  have hP'nc₂ : ¬ P' ≤ centralizer (J₂ : Set G) := by
    intro h
    apply hPnc₁
    intro y hy
    have h1 : x * y * x⁻¹ ∈ centralizer (J₂ : Set G) := h ⟨y, hy, by simp [hf, MulAut.conj_apply]⟩
    rw [← hx₁] at h1
    exact (k2_mem_centralizer_map_conj x).mp h1
  have hP'z : ∀ y ∈ P', z' * y = y * z' := by
    rintro _ ⟨y, hy, rfl⟩
    have := hPz y hy
    show x * z * x⁻¹ * (x * y * x⁻¹) = x * y * x⁻¹ * (x * z * x⁻¹)
    calc x * z * x⁻¹ * (x * y * x⁻¹) = x * (z * y) * x⁻¹ := by group
      _ = x * (y * z) * x⁻¹ := by rw [this]
      _ = x * y * x⁻¹ * (x * z * x⁻¹) := by group
  have hP'n : ∀ c ∈ H, c * z' = z' * c → c ∈ normalizer (P' : Set G) := by
    intro c hc hcz
    have hc' : x⁻¹ * c * x ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hxH) hc) hxH
    have hcz' : x⁻¹ * c * x * z = z * (x⁻¹ * c * x) := by
      have hcz2 : c * (x * z * x⁻¹) = (x * z * x⁻¹) * c := hcz
      calc x⁻¹ * c * x * z = x⁻¹ * (c * (x * z * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * z * x⁻¹) * c) * x := by rw [hcz2]
        _ = z * (x⁻¹ * c * x) := by group
    have h1 := k2_mem_normalizer_map_conj (K := P) x (hPnorm _ hc' hcz')
    have e3 : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
    rwa [e3] at h1
  have hKA₁ : KATwoY (↥J₁ ⧸ center ↥J₁) := hKA G z k S hctx H J₁ J₂ hH hJ₁ hJ₂ hne
  have hKA₂ : KATwoY (↥J₂ ⧸ center ↥J₂) := hKA G z k S hctx H J₂ J₁ hH hJ₂ hJ₁ hne.symm
  obtain ⟨a₁, ha₁, hc₁⟩ := jlevel_two hq₁ hKA₁ hz₁ hz'₁ hz2 hz'2 hJ₁z hJ₁z' hp hp2 hPp hP'p
    hPN₁ hP'N₁ hPnc₁ hP'nc₁ hPz hP'z (fun y hy hyz => hPnorm y (hJ₁.1 hy) hyz)
    (fun y hy hyz => hP'n y (hJ₁.1 hy) hyz)
  obtain ⟨a₂, ha₂, hc₂⟩ := jlevel_two hq₂ hKA₂ hz₂ hz'₂ hz2 hz'2 hJ₂z hJ₂z' hp hp2 hPp hP'p
    hPN₂ hP'N₂ hPnc₂ hP'nc₂ hPz hP'z (fun y hy hyz => hPnorm y (hJ₂.1 hy) hyz)
    (fun y hy hyz => hP'n y (hJ₂.1 hy) hyz)
  set n : G := z * z' with hn
  have hxz : ⁅x, z⁆ = n⁻¹ := by
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hz'i : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
    rw [hn, mul_inv_rev, hz'i, hzi, commutatorElement_def, hzi]
  have hcent₁ : a₂⁻¹ ∈ centralizer (J₁ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => hcomm g hg a₂⁻¹ (J₂.inv_mem ha₂)
  have hcent₂ : a₁⁻¹ ∈ centralizer (J₂ : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => (hcomm a₁⁻¹ (J₁.inv_mem ha₁) g hg).symm
  have hu₁ : (a₁ * a₂)⁻¹ * n ∈ centralizer (J₁ : Set G) := by
    have e : (a₁ * a₂)⁻¹ * n = a₂⁻¹ * (a₁⁻¹ * n) := by group
    rw [e]
    exact Subgroup.mul_mem _ hcent₁ hc₁
  have hu₂ : (a₁ * a₂)⁻¹ * n ∈ centralizer (J₂ : Set G) := by
    have hc : a₁ * a₂ = a₂ * a₁ := hcomm a₁ ha₁ a₂ ha₂
    have e : (a₁ * a₂)⁻¹ * n = a₁⁻¹ * (a₂⁻¹ * n) := by rw [hc, mul_inv_rev, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ hcent₂ hc₂
  have hu : (a₁ * a₂)⁻¹ * n ∈ centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := by
    have hle : J₁ ⊔ J₂ ≤ centralizer ({(a₁ * a₂)⁻¹ * n} : Set G) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu₁ g hg)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hu₂ g hg)
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hm : a₁ * a₂ ∈ J₁ ⊔ J₂ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right ha₂)
  have hn' : n = (a₁ * a₂) * ((a₁ * a₂)⁻¹ * n) := by group
  have hmem : n ∈ J₁ ⊔ J₂ ⊔ centralizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := by
    rw [hn']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm) (Subgroup.mem_sup_right hu)
  rw [hxz]
  exact Subgroup.inv_mem _ hmem

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

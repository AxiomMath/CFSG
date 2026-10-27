module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y14
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup YamadaD CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {d : YamadaD.Data G}

theorem exists_comm_of_theta_mem_D₂ (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    {x : G} (hxt : x⁻¹ * (d.t * x * d.t⁻¹) ∈ d.D₂) :
    ∃ w ∈ d.D₂, d.t * (x * w⁻¹) = (x * w⁻¹) * d.t := by
  have ht' : d.t⁻¹ = d.t := h.t_inv
  have hcθ : x⁻¹ * (d.t * x * d.t⁻¹) = d.theta x := (theta_eq' h x).symm
  have hcc : (d.theta x)⁻¹ = d.theta x :=
    inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV (hcθ ▸ hxt))
  have hct : d.t * d.theta x * d.t = d.theta x := by rw [t_theta_t h, hcc]
  have hcA : d.theta x ∈ d.A₂ := by
    rw [← h.D₂_inf_H]
    refine mem_inf.mpr ⟨hcθ ▸ hxt, mem_centralizer_singleton_iff.mpr ?_⟩
    calc d.theta x * d.t = d.t⁻¹ * (d.t * d.theta x * d.t) := by group
      _ = d.t * d.theta x := by rw [hct, ht']
  obtain ⟨w, hw, hwc⟩ := exists_D₂_surj_eq h hB hV hcA
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (h.D₂_sq hB hV hw)
  have hθw : d.theta w = d.theta x := by
    rw [theta_eq' h, hww]
    exact hwc
  refine ⟨w, hw, ?_⟩
  have e1 : x⁻¹ * d.t * x * d.t = w⁻¹ * d.t * w * d.t := hθw.symm
  calc d.t * (x * w⁻¹) = x * (x⁻¹ * d.t * x * d.t) * d.t⁻¹ * w⁻¹ := by group
    _ = x * (w⁻¹ * d.t * w * d.t) * d.t⁻¹ * w⁻¹ := by rw [e1]
    _ = x * w⁻¹ * d.t := by group

theorem g1 (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) :
    ∀ x ∈ normalizer (d.D₂ : Set G), x⁻¹ * (d.t * x * d.t⁻¹) ∈ d.D₂ →
      ∃ y ∈ normalizer (d.A₂ : Set G) ⊓ centralizer ({d.t} : Set G), y⁻¹ * x ∈ d.D₂ := by
  intro x hxN hxt
  obtain ⟨w, hw, hyt⟩ := exists_comm_of_theta_mem_D₂ h hB hV hxt
  have hyN : x * w⁻¹ ∈ normalizer (d.D₂ : Set G) :=
    mul_mem hxN (inv_mem (le_normalizer hw))
  refine ⟨x * w⁻¹, mem_inf.mpr ⟨mem_normalizer_of_conj_mem fun a ha => ?_,
    mem_centralizer_singleton_iff.mpr hyt.symm⟩, ?_⟩
  · have haD := (mem_normalizer_iff.mp hyN a).mp (h.A₂_le_D₂ ha)
    rw [← h.D₂_inf_H]
    refine mem_inf.mpr ⟨haD, mem_centralizer_singleton_iff.mpr ?_⟩
    have hat : d.t * a = a * d.t := t_comm_of_mem_L h (h.A₂_le_L ha)
    have hyt' : d.t * (x * w⁻¹)⁻¹ = (x * w⁻¹)⁻¹ * d.t := by
      calc d.t * (x * w⁻¹)⁻¹ = (x * w⁻¹)⁻¹ * ((x * w⁻¹) * d.t) * (x * w⁻¹)⁻¹ := by group
        _ = (x * w⁻¹)⁻¹ * (d.t * (x * w⁻¹)) * (x * w⁻¹)⁻¹ := by rw [hyt]
        _ = (x * w⁻¹)⁻¹ * d.t := by group
    calc x * w⁻¹ * a * (x * w⁻¹)⁻¹ * d.t = x * w⁻¹ * a * (d.t * (x * w⁻¹)⁻¹) := by
          rw [hyt']; group
      _ = x * w⁻¹ * (a * d.t) * (x * w⁻¹)⁻¹ := by group
      _ = x * w⁻¹ * (d.t * a) * (x * w⁻¹)⁻¹ := by rw [hat]
      _ = (d.t * (x * w⁻¹)) * a * (x * w⁻¹)⁻¹ := by rw [hyt]; group
      _ = d.t * (x * w⁻¹ * a * (x * w⁻¹)⁻¹) := by group
  · rw [show (x * w⁻¹)⁻¹ * x = w by group]
    exact hw

theorem g2 (h : Hyp d) (hSyl : IsSylowOf 2 d.S d.L) (hSA : d.S ≤ normalizer (d.A₂ : Set G))
    (hA₂S : d.A₂ ≤ d.S) (hNL : d.L ⊓ normalizer (d.A₂ : Set G) ≤ d.K₂ ⊔ d.A₂) :
    normalizer (d.A₂ : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      d.K₂ ⊔ (normalizer (d.S : Set G) ⊓ centralizer ({d.t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  obtain ⟨hxA, hxH⟩ := mem_inf.mp hx
  set M := d.L ⊓ normalizer (d.A₂ : Set G)
  have hxL : x ∈ normalizer (d.L : Set G) := h.H_le_normalizer_L hxH
  have hSL : d.S ≤ d.L := hSyl.le
  have hSM : d.S ≤ M := le_inf hSL hSA
  have hSylM : IsSylowOf 2 d.S M := hSyl.of_le hSM inf_le_left
  set S' := d.S.map (MulAut.conj x).toMonoidHom
  have hS'M : S' ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    have hsM := hSM hs
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hxL s).mp (mem_inf.mp hsM).1, ?_⟩
    exact mul_mem (mul_mem hxA (mem_inf.mp hsM).2) (inv_mem hxA)
  have hcard : Nat.card S' = Nat.card d.S := card_map_of_injective (MulEquiv.injective _)
  have hSylM' : IsSylowOf 2 S' M := isSylowOf_of_card hS'M (by rw [hcard, hSylM.card_eq])
  obtain ⟨k, hkM, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj hSylM hSylM'
  have hn : k⁻¹ * x ∈ normalizer (d.S : Set G) := by
    apply mem_normalizer_of_conj_mem
    intro s hs
    have h1 : x * s * x⁻¹ ∈ S' := ⟨s, hs, rfl⟩
    have h2 := (hk _).mp h1
    rwa [show k⁻¹ * (x * s * x⁻¹) * k = k⁻¹ * x * s * (k⁻¹ * x)⁻¹ by group] at h2
  have hkH : k ∈ centralizer ({d.t} : Set G) := h.L_le_H (mem_inf.mp hkM).1
  have hnH : k⁻¹ * x ∈ centralizer ({d.t} : Set G) := mul_mem (inv_mem hkH) hxH
  have e : x = k * (k⁻¹ * x) := by group
  have hA₂le : d.A₂ ≤ normalizer (d.S : Set G) ⊓ centralizer ({d.t} : Set G) :=
    fun a ha => mem_inf.mpr ⟨le_normalizer (hA₂S ha), h.L_le_H (h.A₂_le_L ha)⟩
  rw [e]
  exact mul_mem ((sup_le le_sup_left (hA₂le.trans le_sup_right)) (hNL hkM))
    (mem_sup_right (mem_inf.mpr ⟨hn, hnH⟩))

theorem nS (h : Hyp d) (hB : HypB d) (hZS : d.S ⊓ centralizer (d.S : Set G) = zpowers d.z)
    (hNA : normalizer (d.S : Set G) ≤ normalizer (d.A₂ : Set G))
    (hNL : d.L ⊓ normalizer (d.A₂ : Set G) ≤ d.K₂ ⊔ d.A₂) :
    normalizer (d.S : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      normalizer (d.D₂ : Set G) ⊓ normalizer ((d.K₂ ⊔ d.A₂ : Subgroup G) : Set G) ⊓
        normalizer (d.D₁ : Set G) := by
  intro x hx
  obtain ⟨hxS, hxH⟩ := mem_inf.mp hx
  have hxt' : x * d.t = d.t * x := mem_centralizer_singleton_iff.mp hxH
  have hxt : x ∈ normalizer (zpowers d.t : Set G) :=
    YamadaPar.mem_normalizer_of_conj_eq fun y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      rw [(Commute.zpow_right (show Commute x d.t from hxt') k).eq, mul_inv_cancel_right]
  have hxz : x ∈ normalizer (zpowers d.z : Set G) := by
    rw [← hZS]
    exact Hyp.mem_normalizer_inf hxS
      (mem_normalizer_of_conj_mem fun _ hn => conj_mem_centralizer hxS hn)
  have hxZR : x ∈ normalizer (d.ZR : Set G) := YamadaD.mem_normalizer_sup hxz hxt
  have hxA := hNA hxS
  have hxD₂ : x ∈ normalizer (d.D₂ : Set G) :=
    Hyp.mem_normalizer_inf (h.C₂_normal (YamadaD.mem_normalizer_sup hxA hxt))
      (mem_normalizer_of_conj_mem fun _ hn => conj_mem_centralizer (h.X_le_normalizer_V₁ hxZR) hn)
  have hxKA : x ∈ normalizer ((d.K₂ ⊔ d.A₂ : Subgroup G) : Set G) := by
    have heq : d.K₂ ⊔ d.A₂ = d.L ⊓ normalizer (d.A₂ : Set G) :=
      le_antisymm (sup_le (le_inf hB.K₂_le_L hB.K₂_le_normalizer) (le_inf h.A₂_le_L le_normalizer))
        hNL
    rw [heq]
    exact Hyp.mem_normalizer_inf (h.H_le_normalizer_L hxH)
      (mem_normalizer_of_conj_mem fun _ hn => mul_mem (mul_mem hxA hn) (inv_mem hxA))
  exact mem_inf.mpr ⟨mem_inf.mpr ⟨hxD₂, hxKA⟩, Hyp.XV_le_normalizer_D₁ (h.X_le_XV hxZR)⟩

theorem normalizer_S_le (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1)
    (hZS : d.S ⊓ centralizer (d.S : Set G) = zpowers d.z)
    (hNA : normalizer (d.S : Set G) ≤ normalizer (d.A₂ : Set G))
    (hNL : d.L ⊓ normalizer (d.A₂ : Set G) ≤ d.K₂ ⊔ d.A₂)
    (hNL₁ : d.L ⊓ centralizer ({d.z} : Set G) ≤ d.K₁ ⊔ d.A₁) :
    normalizer (d.S : Set G) ⊓ centralizer ({d.t} : Set G) ≤
      normalizer ((YamadaPar.nOne d.D₁ d.K₁ d.D₂ : Subgroup G) : Set G) ⊓
        normalizer ((YamadaN2.nTwo d.D₂ d.K₂ d.D₁ : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨⟨hxD₂, hxKA⟩, hxD₁⟩ := mem_inf.mp (nS h hB hZS hNA hNL hx)
  obtain ⟨hxS, hxH⟩ := mem_inf.mp hx
  have hzS : d.z ∈ d.S ⊓ centralizer (d.S : Set G) := hZS ▸ mem_zpowers d.z
  have hxzS : x * d.z * x⁻¹ ∈ d.S ⊓ centralizer (d.S : Set G) :=
    (mem_normalizer_iff.mp (Hyp.mem_normalizer_inf hxS
      (mem_normalizer_of_conj_mem fun _ hn => conj_mem_centralizer hxS hn)) _).mp hzS
  rw [hZS] at hxzS
  have hxz : x * d.z = d.z * x := by
    rcases h.mem_zpowers_z_iff.mp hxzS with h1 | h1
    · exfalso
      apply h.z_ne_one
      have := congrArg (fun y => x⁻¹ * y * x) h1
      simpa [mul_assoc] using this
    · calc x * d.z = x * d.z * x⁻¹ * x := by group
        _ = d.z * x := by rw [h1]
  have hxKA₁ : x ∈ normalizer ((d.K₁ ⊔ d.A₁ : Subgroup G) : Set G) := by
    have heq : d.K₁ ⊔ d.A₁ = d.L ⊓ centralizer ({d.z} : Set G) := by
      refine le_antisymm (sup_le (le_inf h.K₁_le_L h.K₁_cent_z) (le_inf h.A₁_le_L ?_)) hNL₁
      intro a ha
      exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.z_cent_A₁ a ha)
    rw [heq]
    refine Hyp.mem_normalizer_inf (h.H_le_normalizer_L hxH) ?_
    exact mem_normalizer_of_conj_mem fun c hc => mem_centralizer_singleton_iff.mpr (by
      have hcz := mem_centralizer_singleton_iff.mp hc
      calc x * c * x⁻¹ * d.z = x * c * (x⁻¹ * d.z * x) * x⁻¹ := by group
        _ = x * c * d.z * x⁻¹ := by
          rw [show x⁻¹ * d.z * x = d.z by
            calc x⁻¹ * d.z * x = x⁻¹ * (d.z * x) := by group
              _ = x⁻¹ * (x * d.z) := by rw [hxz]
              _ = d.z := by group]
        _ = x * d.z * c * x⁻¹ := by rw [mul_assoc x c, hcz, ← mul_assoc]
        _ = d.z * x * c * x⁻¹ := by rw [hxz]
        _ = d.z * (x * c * x⁻¹) := by group)
  have hA₁ := h.A₁_le_D₁ hB hV
  have e₁ : YamadaPar.nOne d.D₁ d.K₁ d.D₂ = d.D₁ ⊔ (d.K₁ ⊔ d.A₁) ⊔ d.D₂ :=
    le_antisymm (sup_le_sup_right (sup_le_sup_left le_sup_left _) _)
      (sup_le (sup_le le_sup_left (sup_le le_sup_right (hA₁.trans le_sup_left)) |>.trans
        le_sup_left) le_sup_right)
  have e₂ : YamadaN2.nTwo d.D₂ d.K₂ d.D₁ = d.D₂ ⊔ (d.K₂ ⊔ d.A₂) ⊔ d.D₁ :=
    le_antisymm (sup_le_sup_right (sup_le_sup_left le_sup_left _) _)
      (sup_le (sup_le le_sup_left (sup_le le_sup_right (h.A₂_le_D₂.trans le_sup_left)) |>.trans
        le_sup_left) le_sup_right)
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [e₁]
    exact YamadaD.mem_normalizer_sup (YamadaD.mem_normalizer_sup hxD₁ hxKA₁) hxD₂
  · rw [e₂]
    exact YamadaD.mem_normalizer_sup (YamadaD.mem_normalizer_sup hxD₂ hxKA) hxD₁

end CFSG.EvenSmallLie.UnitarySix.Child5

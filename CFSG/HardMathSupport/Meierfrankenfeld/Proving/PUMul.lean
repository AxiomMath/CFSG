module

public import CFSG.Quasithin.Background.Module
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.Proving

open CFSG.Quasithin

variable {W : Type} [CommGroup W]

@[expose] def pUMul (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {g | (∀ u ∈ U, g u = u) ∧ ∀ w : W, g w * w⁻¹ ∈ U}
  one_mem' := by
    show (∀ u ∈ U, (1 : MulAut W) u = u) ∧ ∀ w : W, (1 : MulAut W) w * w⁻¹ ∈ U
    exact ⟨fun u _ => rfl, fun w => by show w * w⁻¹ ∈ U; simp⟩
  mul_mem' := by
    intro g h hg hh
    have hg' : (∀ u ∈ U, g u = u) ∧ ∀ w : W, g w * w⁻¹ ∈ U := hg
    have hh' : (∀ u ∈ U, h u = u) ∧ ∀ w : W, h w * w⁻¹ ∈ U := hh
    show (∀ u ∈ U, (g * h) u = u) ∧ ∀ w : W, (g * h) w * w⁻¹ ∈ U
    refine ⟨fun u hu => ?_, fun w => ?_⟩
    · show g (h u) = u
      rw [hh'.1 u hu, hg'.1 u hu]
    · show g (h w) * w⁻¹ ∈ U
      have e : g (h w) * w⁻¹ = (g (h w) * (h w)⁻¹) * (h w * w⁻¹) := by group
      rw [e]
      exact U.mul_mem (hg'.2 _) (hh'.2 _)
  inv_mem' := by
    intro g hg
    have hg' : (∀ u ∈ U, g u = u) ∧ ∀ w : W, g w * w⁻¹ ∈ U := hg
    show (∀ u ∈ U, g⁻¹ u = u) ∧ ∀ w : W, g⁻¹ w * w⁻¹ ∈ U
    refine ⟨fun u hu => ?_, fun w => ?_⟩
    · have h1 : g⁻¹ (g u) = u := MulEquiv.symm_apply_apply g u
      rwa [hg'.1 u hu] at h1
    · have hx : g (g⁻¹ w) = w := MulEquiv.apply_symm_apply g w
      have hmem := U.inv_mem (hg'.2 (g⁻¹ w))
      rw [hx] at hmem
      have e : (w * (g⁻¹ w)⁻¹)⁻¹ = g⁻¹ w * w⁻¹ := by group
      rw [e] at hmem
      exact hmem

theorem mem_pUMul {U : Subgroup W} {g : MulAut W} :
    g ∈ pUMul U ↔ (∀ u ∈ U, g u = u) ∧ ∀ w : W, g w * w⁻¹ ∈ U := Iff.rfl

theorem pUMul_mul_comm {U : Subgroup W} {g h : MulAut W} (hg : g ∈ pUMul U) (hh : h ∈ pUMul U) :
    g * h = h * g := by
  obtain ⟨hg1, hg2⟩ := mem_pUMul.1 hg
  obtain ⟨hh1, hh2⟩ := mem_pUMul.1 hh
  ext w
  obtain ⟨u, hu, hgu⟩ : ∃ u ∈ U, g w = u * w := ⟨g w * w⁻¹, hg2 w, (inv_mul_cancel_right _ _).symm⟩
  obtain ⟨v, hv, hhv⟩ : ∃ v ∈ U, h w = v * w := ⟨h w * w⁻¹, hh2 w, (inv_mul_cancel_right _ _).symm⟩
  show g (h w) = h (g w)
  rw [hhv, hgu, map_mul, map_mul, hg1 v hv, hh1 u hu, hgu, hhv]
  exact mul_left_comm _ _ _

theorem pUMul_mul_self (hW : ∀ w : W, w * w = 1) {U : Subgroup W} {g : MulAut W}
    (hg : g ∈ pUMul U) : g * g = 1 := by
  obtain ⟨hg1, hg2⟩ := mem_pUMul.1 hg
  ext w
  obtain ⟨u, hu, hgu⟩ : ∃ u ∈ U, g w = u * w := ⟨g w * w⁻¹, hg2 w, (inv_mul_cancel_right _ _).symm⟩
  show g (g w) = w
  rw [hgu, map_mul, hg1 u hu, hgu, ← mul_assoc, hW u, one_mul]

theorem conj_mem_pUMul {U : Subgroup W} {c g : MulAut W} (hc : ∀ u ∈ U, c u ∈ U)
    (hc' : ∀ u ∈ U, c⁻¹ u ∈ U) (hg : g ∈ pUMul U) : c * g * c⁻¹ ∈ pUMul U := by
  obtain ⟨hg1, hg2⟩ := mem_pUMul.1 hg
  have hcc : ∀ x : W, c (c⁻¹ x) = x := fun x => MulEquiv.apply_symm_apply c x
  rw [mem_pUMul]
  refine ⟨fun u hu => ?_, fun w => ?_⟩
  · show c (g (c⁻¹ u)) = u
    rw [hg1 (c⁻¹ u) (hc' u hu), hcc]
  · show c (g (c⁻¹ w)) * w⁻¹ ∈ U
    have h1 : c (g (c⁻¹ w) * (c⁻¹ w)⁻¹) ∈ U := hc _ (hg2 (c⁻¹ w))
    have h2 : c (g (c⁻¹ w) * (c⁻¹ w)⁻¹) = c (g (c⁻¹ w)) * w⁻¹ := by
      rw [map_mul, map_inv, hcc]
    rw [← h2]
    exact h1

theorem le_pUMul_fixV {E : Subgroup (MulAut W)} (hq : IsQuadratic E) : E ≤ pUMul (fixV E) := by
  intro g hg
  rw [mem_pUMul]
  refine ⟨fun u hu => (mem_fixV.1 hu) g hg, fun w => ?_⟩
  exact hq (Subgroup.subset_closure ⟨g, hg, w, rfl⟩)

theorem zpow_apply_eq_of_apply_eq {g : MulAut W} {u : W} (hu : g u = u) (k : ℤ) :
    (g ^ k) u = u := by
  refine Int.induction_on k ?_ ?_ ?_
  · exact congrArg (fun f : MulAut W => f u) (zpow_zero g)
  · intro n ih
    rw [zpow_add_one, MulAut.mul_apply, hu, ih]
  · intro n ih
    have hinv : g⁻¹ u = u := by
      have h1 : g⁻¹ (g u) = u := MulEquiv.symm_apply_apply g u
      rwa [hu] at h1
    rw [zpow_sub_one, MulAut.mul_apply, hinv, ih]

theorem le_fixV_zpowers_of_mem_pUMul {U : Subgroup W} {g : MulAut W} (hg : g ∈ pUMul U) :
    U ≤ fixV (Subgroup.zpowers g) := by
  obtain ⟨hg1, _⟩ := mem_pUMul.1 hg
  intro u hu
  rw [mem_fixV]
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact zpow_apply_eq_of_apply_eq (hg1 u hu) k

theorem apply_mem_fixV_zpowers_of_commute {a c : MulAut W} (hca : c * a = a * c) {u : W}
    (hu : u ∈ fixV (Subgroup.zpowers a)) : c u ∈ fixV (Subgroup.zpowers a) := by
  rw [mem_fixV] at hu ⊢
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hcomm : Commute c (a ^ k) := (show Commute c a from hca).zpow_right k
  calc (a ^ k) (c u) = (a ^ k * c) u := rfl
    _ = (c * a ^ k) u := by rw [← hcomm.eq]
    _ = c ((a ^ k) u) := rfl
    _ = c u := by rw [hu (a ^ k) hx]

theorem card_fixV_sq_le_of_inverts_sq_fpf [Finite W] {ζ t : MulAut W}
    (hfpf : ∀ w : W, ζ (ζ w) = w → w = 1) (hinv : t * ζ * t⁻¹ = ζ⁻¹) :
    Nat.card (fixV (Subgroup.zpowers t)) * Nat.card (fixV (Subgroup.zpowers t)) ≤ Nat.card W := by
  have htz : ∀ w : W, t (ζ w) = ζ⁻¹ (t w) := by
    intro w
    have h1 : t * ζ = ζ⁻¹ * t := by
      have := congrArg (· * t) hinv
      simpa [mul_assoc] using this
    exact congrArg (fun f : MulAut W => f w) h1
  have hmemC : ∀ c : W, c ∈ fixV (Subgroup.zpowers t) ↔ t c = c := fun c =>
    ⟨fun h => (mem_fixV.1 h) t (Subgroup.mem_zpowers t), fun h => mem_fixV.2 (fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      exact zpow_apply_eq_of_apply_eq h k)⟩
  let f : ↥(fixV (Subgroup.zpowers t)) × ↥(fixV (Subgroup.zpowers t)) → W :=
    fun p => (p.1 : W) * ζ (p.2 : W)
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [f] at h
    have hc : ((b' : W) / (b : W)) ∈ fixV (Subgroup.zpowers t) :=
      (fixV (Subgroup.zpowers t)).div_mem b'.2 b.2
    have hd : ((a : W) / (a' : W)) ∈ fixV (Subgroup.zpowers t) :=
      (fixV (Subgroup.zpowers t)).div_mem a.2 a'.2
    have hdz : (a : W) / (a' : W) = ζ ((b' : W) / (b : W)) := by
      rw [map_div, div_eq_div_iff_mul_eq_mul]
      rw [mul_comm (ζ (b' : W)) (a' : W)]
      exact h
    set c : W := (b' : W) / (b : W) with hcdef
    have h1 : t c = c := (hmemC c).1 hc
    have h2 : t (ζ c) = ζ c := by rw [← hdz]; exact (hmemC _).1 hd
    rw [htz, h1] at h2
    have h3 : ζ (ζ c) = c := by
      have := congrArg ζ h2
      simpa using this.symm
    have hc1 : c = 1 := hfpf c h3
    have hbb : (b' : W) = b := by
      rw [hcdef, div_eq_one] at hc1
      exact hc1
    have hdd : (a : W) = a' := by
      rw [hc1, map_one, div_eq_one] at hdz
      exact hdz
    exact Prod.ext (Subtype.ext hdd) (Subtype.ext hbb.symm)
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using this

theorem eq_one_of_mem_center_of_mul_self {G : Type} [Group G] [Finite G]
    (hodd : Odd (Nat.card (Subgroup.center G))) {ζ : G} (hζ : ζ ∈ Subgroup.center G)
    (h2 : ζ * ζ = 1) : ζ = 1 := by
  have key : ∀ z : Subgroup.center G, z ^ 2 = 1 → z = 1 := by
    intro z hz2
    have hd1 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    have hd2 : orderOf z ∣ Nat.card (Subgroup.center G) := orderOf_dvd_natCard z
    have hodd' : Odd (orderOf z) := Odd.of_dvd_nat hodd hd2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd1 with h1 | h1
    · exact orderOf_eq_one_iff.1 h1
    · exfalso
      rw [h1] at hodd'
      obtain ⟨m, hm⟩ := hodd'
      omega
  have hz : (⟨ζ, hζ⟩ : Subgroup.center G) = 1 :=
    key _ (Subtype.ext (by simp [pow_two, h2]))
  have := congrArg Subtype.val hz
  simpa using this

end CFSG.HardMathSupport.Meierfrankenfeld.Proving

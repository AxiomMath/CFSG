module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W8
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W9
public import CFSG.ClassicalInvolution.Q3.TL4LinkB2b4
public import CFSG.ClassicalInvolution.Q3.TL4ExitDichL2
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2Defs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (ne_of_mem_omegaNbr)
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.Blueprint

section Acts

variable {Y : Type} [Group Y]

private theorem conj_mem_of_conjSub_eq {Λ : Subgroup Y} {c : Y} (hc : conjSub c Λ = Λ) {z : Y}
    (hz : z ∈ Λ) : c * z * c⁻¹ ∈ Λ := by
  have h := conj_mem_conjSub hz c
  rwa [hc] at h

private theorem conj_mem_oddCoreOf {Λ : Subgroup Y} {c : Y} (hc : conjSub c Λ = Λ) {o : Y}
    (ho : o ∈ oddCoreOf Λ) : c * o * c⁻¹ ∈ oddCoreOf Λ := by
  have h := conj_mem_conjSub ho c
  rwa [← Thompson.oddCoreOf_conjSub_eq, hc] at h

private theorem mul_inv_mem_oddCoreOf_of_mk_eq {Λ : Subgroup Y} {a b : Y} (ha : a ∈ Λ)
    (hb : b ∈ Λ) (h : (QuotientGroup.mk ⟨a, ha⟩ : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) =
      QuotientGroup.mk ⟨b, hb⟩) : a * b⁻¹ ∈ oddCoreOf Λ := by
  rw [QuotientGroup.eq] at h
  have h1 := Subgroup.inv_mem _ h
  rw [mul_inv_rev, inv_inv] at h1
  have h2 := Subgroup.Normal.conj_mem inferInstance _ h1 ⟨b, hb⟩
  rw [show (⟨b, hb⟩ : ↥Λ) * ((⟨b, hb⟩ : ↥Λ)⁻¹ * ⟨a, ha⟩) * (⟨b, hb⟩ : ↥Λ)⁻¹ =
    ⟨a, ha⟩ * (⟨b, hb⟩ : ↥Λ)⁻¹ by group] at h2
  exact ⟨_, h2, rfl⟩

private theorem actsLike_refl (Λ : Subgroup Y) (x : Y) : ActsLike Λ x x := by
  intro z _
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

private theorem actsLike_symm {Λ : Subgroup Y} {x w : Y} (h : ActsLike Λ x w) :
    ActsLike Λ w x := by
  intro z hz
  have h1 := Subgroup.inv_mem _ (h z hz)
  rwa [mul_inv_rev, inv_inv] at h1

private theorem actsLike_trans {Λ : Subgroup Y} {x w v : Y} (h1 : ActsLike Λ x w)
    (h2 : ActsLike Λ w v) : ActsLike Λ x v := by
  intro z hz
  have h3 := Subgroup.mul_mem _ (h1 z hz) (h2 z hz)
  rwa [show x * z * x⁻¹ * (w * z * w⁻¹)⁻¹ * (w * z * w⁻¹ * (v * z * v⁻¹)⁻¹) =
    x * z * x⁻¹ * (v * z * v⁻¹)⁻¹ by group] at h3

private theorem actsTriv_iff {Λ : Subgroup Y} {x : Y} : ActsTriv Λ x ↔ ActsLike Λ x 1 := by
  constructor
  · intro h z hz
    have h1 := h z hz
    rwa [show x * z * x⁻¹ * z⁻¹ = x * z * x⁻¹ * (1 * z * 1⁻¹)⁻¹ by group] at h1
  · intro h z hz
    have h1 := h z hz
    rwa [show x * z * x⁻¹ * (1 * z * 1⁻¹)⁻¹ = x * z * x⁻¹ * z⁻¹ by group] at h1

private theorem actsLike_mul {Λ : Subgroup Y} {x y w v : Y} (hx : ActsLike Λ x w)
    (hy : ActsLike Λ y v) (hv : conjSub v Λ = Λ) (hxn : conjSub x Λ = Λ) :
    ActsLike Λ (x * y) (w * v) := by
  intro z hz
  have hz1 : v * z * v⁻¹ ∈ Λ := conj_mem_of_conjSub_eq hv hz
  have h3 := Subgroup.mul_mem _ (conj_mem_oddCoreOf hxn (hy z hz)) (hx _ hz1)
  rwa [show x * (y * z * y⁻¹ * (v * z * v⁻¹)⁻¹) * x⁻¹ *
      (x * (v * z * v⁻¹) * x⁻¹ * (w * (v * z * v⁻¹) * w⁻¹)⁻¹) =
    x * y * z * (x * y)⁻¹ * (w * v * z * (w * v)⁻¹)⁻¹ by group] at h3

private theorem actsLike_inv {Λ : Subgroup Y} {x w : Y} (hx : ActsLike Λ x w)
    (hw : conjSub w⁻¹ Λ = Λ) (hxn : conjSub x⁻¹ Λ = Λ) : ActsLike Λ x⁻¹ w⁻¹ := by
  intro z hz
  have hz1 : w⁻¹ * z * w⁻¹⁻¹ ∈ Λ := conj_mem_of_conjSub_eq hw hz
  have h1 := conj_mem_oddCoreOf hxn (Subgroup.inv_mem _ (hx _ hz1))
  rwa [show x⁻¹ * (x * (w⁻¹ * z * w⁻¹⁻¹) * x⁻¹ * (w * (w⁻¹ * z * w⁻¹⁻¹) * w⁻¹)⁻¹)⁻¹ * x⁻¹⁻¹ =
    x⁻¹ * z * x⁻¹⁻¹ * (w⁻¹ * z * w⁻¹⁻¹)⁻¹ by group] at h1

private theorem actsLike_conj {Λ : Subgroup Y} {x w : Y} (h : ActsLike Λ x w) (g : Y) :
    ActsLike (conjSub g Λ) (g * x * g⁻¹) (g * w * g⁻¹) := by
  intro z hz
  rw [mem_conjSub_iff] at hz
  rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
  rw [show g⁻¹ * (g * x * g⁻¹ * z * (g * x * g⁻¹)⁻¹ * (g * w * g⁻¹ * z * (g * w * g⁻¹)⁻¹)⁻¹) * g =
    x * (g⁻¹ * z * g) * x⁻¹ * (w * (g⁻¹ * z * g) * w⁻¹)⁻¹ by group]
  exact h _ hz

private theorem actsTriv_conj {Λ : Subgroup Y} {x : Y} (h : ActsTriv Λ x) (g : Y) :
    ActsTriv (conjSub g Λ) (g * x * g⁻¹) := by
  have h1 := actsLike_conj (actsTriv_iff.mp h) g
  rw [show g * 1 * g⁻¹ = 1 by group] at h1
  exact actsTriv_iff.mpr h1

private theorem innerModOdd_of_actsLike {Λ : Subgroup Y} {x w : Y} (hw : InnerModOdd Λ w)
    (h : ActsLike Λ x w) : InnerModOdd Λ x := by
  obtain ⟨v, hv, hwv⟩ := hw
  exact ⟨v, hv, actsLike_trans h hwv⟩

private theorem innerModOdd_mul {Λ : Subgroup Y} {x y : Y} (hx : InnerModOdd Λ x)
    (hy : InnerModOdd Λ y) (hxn : conjSub x Λ = Λ) : InnerModOdd Λ (x * y) := by
  obtain ⟨w, hw, hxw⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  exact ⟨w * v, Λ.mul_mem hw hv, actsLike_mul hxw hyv (conjSub_eq_self_of_mem hv) hxn⟩

private theorem innerModOdd_inv {Λ : Subgroup Y} {x : Y} (hx : InnerModOdd Λ x)
    (hxn : conjSub x⁻¹ Λ = Λ) : InnerModOdd Λ x⁻¹ := by
  obtain ⟨w, hw, hxw⟩ := hx
  exact ⟨w⁻¹, Λ.inv_mem hw, actsLike_inv hxw (conjSub_eq_self_of_mem (Λ.inv_mem hw)) hxn⟩

private theorem innerModOdd_conj {Λ : Subgroup Y} {x : Y} (hx : InnerModOdd Λ x) (g : Y) :
    InnerModOdd (conjSub g Λ) (g * x * g⁻¹) := by
  obtain ⟨w, hw, hxw⟩ := hx
  exact ⟨g * w * g⁻¹, conj_mem_conjSub hw g, actsLike_conj hxw g⟩

private theorem innerModOdd_conj_iff {Λ : Subgroup Y} (x g : Y) :
    InnerModOdd Λ x ↔ InnerModOdd (conjSub g Λ) (g * x * g⁻¹) := by
  refine ⟨fun h => innerModOdd_conj h g, fun h => ?_⟩
  have h1 := innerModOdd_conj h g⁻¹
  rwa [conjSub_inv_conjSub, show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

private theorem innerModOdd_of_actsTriv {Λ : Subgroup Y} {x : Y} (h : ActsTriv Λ x) :
    InnerModOdd Λ x :=
  ⟨1, Λ.one_mem, actsTriv_iff.mp h⟩

private theorem innerModOdd_of_mul_odd {Λ : Subgroup Y} {g k : Y}
    (hg : g ∈ Subgroup.normalizer (Λ : Set Y)) (hk : k ∈ Subgroup.normalizer (Λ : Set Y))
    (hg2 : g * g = 1) (hkodd : Odd (orderOf k)) (h : InnerModOdd Λ (g * k)) :
    InnerModOdd Λ g := by
  have hz : g * k ∈ Subgroup.normalizer (Λ : Set Y) := Subgroup.mul_mem _ hg hk
  have key : ∀ j : ℕ, (g⁻¹ ^ j)⁻¹ * k ^ j ∈ Subgroup.normalizer (Λ : Set Y) ∧
      InnerModOdd Λ ((g⁻¹ ^ j)⁻¹ * k ^ j) := by
    intro j
    induction j with
    | zero =>
      simp only [pow_zero, inv_one, one_mul]
      exact ⟨Subgroup.one_mem _, ⟨1, Λ.one_mem, actsLike_refl Λ 1⟩⟩
    | succ j ih =>
      obtain ⟨hN, hI⟩ := ih
      have e : (g⁻¹ ^ (j + 1))⁻¹ * k ^ (j + 1) =
          g * ((g⁻¹ ^ j)⁻¹ * k ^ j) * g⁻¹ * (g * k) := by
        rw [pow_succ, pow_succ]
        group
      rw [e]
      have hc : g * ((g⁻¹ ^ j)⁻¹ * k ^ j) * g⁻¹ ∈ Subgroup.normalizer (Λ : Set Y) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hN) (Subgroup.inv_mem _ hg)
      refine ⟨Subgroup.mul_mem _ hc hz, innerModOdd_mul ?_ h (mem_normalizer_iff_conjSub_eq.mp hc)⟩
      have h1 := innerModOdd_conj hI g
      rwa [mem_normalizer_iff_conjSub_eq.mp hg] at h1
  obtain ⟨-, h1⟩ := key (orderOf k)
  rw [pow_orderOf_eq_one, mul_one, inv_pow, inv_inv] at h1
  obtain ⟨r, hr⟩ := hkodd
  rwa [hr, pow_succ, pow_mul, sq, hg2, one_pow, one_mul] at h1

private theorem natCard_conjSub' (g : Y) (H : Subgroup Y) :
    Nat.card ↥(conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem mem_closure_pair_cases {a b : Y} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) {p : Y} (hp : p ∈ Subgroup.closure {a, b}) :
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have hSa : ∀ y : Y, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (a * y = 1 ∨ a * y = a ∨ a * y = b ∨ a * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one a))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
  have hSb : ∀ y : Y, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (b * y = 1 ∨ b * y = a ∨ b * y = b ∨ b * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl (mul_one b)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
  induction hp using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left x hx y _ hy =>
    rcases hx with rfl | rfl
    · exact hSa y hy
    · exact hSb y hy
  | inv_mul_cancel x hx y _ hy =>
    rcases hx with rfl | rfl
    · rw [hainv]
      exact hSa y hy
    · rw [hbinv]
      exact hSb y hy

end Acts

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2Set.t_ne_u (hs : Z2Set n R S t J u R₀ T₀ P) : t ≠ u := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  exact ne_of_mem_omegaNbr ((TightLargeHypR.typeRFam hs.large).noTwins _ hK) hs.hJ
    hs.large.datum.isUniqueInvolution_core hs.hu

private theorem Z2Set.mem_cls_conj (hs : Z2Set n R S t J u R₀ T₀ P) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (c : Y) :
    conjSub c L ∈ CoreAssembly.conjClass (tightCore R) :=
  hs.large.datum.hypOmegaGen.conjInvariant c L hL

private theorem Z2Set.eq_J_of_inv (hs : Z2Set n R S t J u R₀ T₀ P) {M : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) (hMu : IsUniqueInvolution M u) : M = J :=
  (TightLargeHypR.typeRFam hs.large).noTwins J hs.hJ.1 M ⟨hM, u, hs.hu, hMu⟩

private theorem Z2Set.t2 (hs : Z2Set n R S t J u R₀ T₀ P) : t * t = 1 :=
  hs.large.datum.isUniqueInvolution_core.sq

private theorem Z2Set.u2 (hs : Z2Set n R S t J u R₀ T₀ P) : u * u = 1 :=
  hs.hu.sq

private theorem Z2Set.tu_comm (hs : Z2Set n R S t J u R₀ T₀ P) : t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hs.large.datum.hypOmegaGen
    hs.large.datum.isUniqueInvolution_core hs.hJ hs.hu

private theorem Z2Set.conjSub_K_fix (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = t) : conjSub c (tightCore R) = tightCore R :=
  eq_core_of_isUniqueInvolution hs.large (hs.mem_cls_conj ⟨1, conjSub_one _⟩ c) (by
    have h := hs.large.datum.isUniqueInvolution_core.conj c
    rwa [hc] at h)

private theorem Z2Set.conjSub_K_swap (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = u) : conjSub c (tightCore R) = J :=
  hs.eq_J_of_inv (hs.mem_cls_conj ⟨1, conjSub_one _⟩ c) (by
    have h := hs.large.datum.isUniqueInvolution_core.conj c
    rwa [hc] at h)

private theorem Z2Set.conjSub_J_fix (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = u) : conjSub c J = J :=
  hs.eq_J_of_inv (hs.mem_cls_conj hs.hJ.1 c) (by
    have h := hs.hu.conj c
    rwa [hc] at h)

private theorem Z2Set.conjSub_J_swap (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = t) : conjSub c J = tightCore R :=
  eq_core_of_isUniqueInvolution hs.large (hs.mem_cls_conj hs.hJ.1 c) (by
    have h := hs.hu.conj c
    rwa [hc] at h)

private theorem Z2Set.conjSub_Λt_fix (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = t) : conjSub c (linkLayer R t) = linkLayer R t := by
  show conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t) =
    linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_K_fix hc, hc]

private theorem Z2Set.conjSub_Λt_swap (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = u) : conjSub c (linkLayer R t) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := by
  show conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t) = _
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_K_swap hc, hc]

private theorem Z2Set.conjSub_Λu_fix (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = u) : conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := by
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_J_fix hc, hc]

private theorem Z2Set.conjSub_Λu_swap (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = t) : conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayer R t := by
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_J_swap hc, hc]

private theorem conj_eq_of_comm {c x : Y} (h : c * x = x * c) : c * x * c⁻¹ = x := by
  rw [h, mul_inv_cancel_right]

private theorem Z2Set.conjSub_Λt_of_mem (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c ∈ edgeCent (P : Subgroup Y) t u) : conjSub c (linkLayer R t) = linkLayer R t :=
  hs.conjSub_Λt_fix (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hc.1.2))

private theorem Z2Set.conjSub_Λu_of_mem (hs : Z2Set n R S t J u R₀ T₀ P) {c : Y}
    (hc : c ∈ edgeCent (P : Subgroup Y) t u) :
    conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
  hs.conjSub_Λu_fix (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hc.2))

private theorem Z2Set.swap_u (hs : Z2Set n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) : b * u * b⁻¹ = t := by
  rcases hs.perm hbP with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd (h1.symm.trans hbt) hs.t_ne_u
  · exact h2

private theorem Z2Set.swap_of_not_mem (hs : Z2Set n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbA : b ∉ edgeCent (P : Subgroup Y) t u) :
    b * t * b⁻¹ = u := by
  rcases hs.perm hbP with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd (hs.mem_edgeCent_iff.mpr ⟨hbP, h1⟩) hbA
  · exact h1

private theorem inv_conj_of_conj {b x y : Y} (h : b * x * b⁻¹ = y) : b⁻¹ * y * b⁻¹⁻¹ = x := by
  rw [← h]
  group

private theorem conj_pow' (g b : Y) (k : ℕ) : (g⁻¹ * b * g) ^ k = g⁻¹ * b ^ k * g := by
  have h := conj_pow (a := g⁻¹) (b := b) (i := k)
  rwa [inv_inv] at h

private theorem eq_of_conj_eq {g b c : Y} (h : g⁻¹ * b * g = g⁻¹ * c * g) : b = c := by
  have h1 := congrArg (fun z => g * z * g⁻¹) h
  simpa [mul_assoc] using h1

private theorem Z2Set.t_mem_P (hs : Z2Set n R S t J u R₀ T₀ P) : t ∈ (P : Subgroup Y) := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  refine hs.hR₀P (CFSG.ClassicalInvolution.Asc77.T3.mem_of_isPGroup
    hs.large.datum.isUniqueInvolution_core hs.hR₀.1 hs.hR₀.2.1 ?_)
  have h8 := Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
    (mem_RSet_of_isSylow2In hK hs.hR₀)
  omega

private theorem Z2Set.u_mem_P (hs : Z2Set n R S t J u R₀ T₀ P) : u ∈ (P : Subgroup Y) := by
  refine hs.hT₀P (CFSG.ClassicalInvolution.Asc77.T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1 ?_)
  have h8 := Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
    (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀)
  omega

private theorem Z2Set.tu_not_conj_u (hs : Z2Set n R S t J u R₀ T₀ P) (g : Y) :
    g * (t * u) * g⁻¹ ≠ u := by
  intro h
  obtain ⟨m, hm⟩ := hs.exists_conj_u
  apply hs.tu_not_conj (m⁻¹ * g)
  rw [show m⁻¹ * g * (t * u) * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * (t * u) * g⁻¹) * m by group, h, ← hm]
  group

private theorem Z2Set.tu_ne_one (hs : Z2Set n R S t J u R₀ T₀ P) : t * u ≠ 1 := by
  intro h
  apply hs.t_ne_u
  have h1 : u = t⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h1, inv_eq_of_mul_eq_one_left hs.t2]

private theorem Z2Set.eq_tu_of_conj_mem_E (hs : Z2Set n R S t J u R₀ T₀ P) {g : Y}
    (h : g⁻¹ * (t * u) * g ∈ Subgroup.closure ({t, u} : Set Y)) :
    g⁻¹ * (t * u) * g = t * u := by
  rcases mem_closure_pair_cases hs.t2 hs.u2 hs.tu_comm h with h' | h' | h' | h'
  · exfalso
    apply hs.tu_ne_one
    have h1 := congrArg (fun z => g * z * g⁻¹) h'
    simpa [mul_assoc] using h1
  · exact absurd (by rw [inv_inv]; exact h') (hs.tu_not_conj g⁻¹)
  · exact absurd (by rw [inv_inv]; exact h') (hs.tu_not_conj_u g⁻¹)
  · exact h'

private theorem mem_centralizer_of_conj_eq {g a : Y} (h : g⁻¹ * a * g = a) :
    g⁻¹ ∈ Subgroup.centralizer ({a} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g⁻¹ * a = g⁻¹ * a * g * g⁻¹ := by group
    _ = a * g⁻¹ := by rw [h]

theorem linkLayer_commutator_mem_oddCoreOf_core (hL : TightLargeHypR 3 n Y R S t) {y : Y}
    (hy : y ∈ linkLayer R t) {x : Y} (hx : x ∈ tightCore R) :
    y * x * y⁻¹ * x⁻¹ ∈ oddCoreOf (tightCore R) := by
  have hΩ := hL.datum.hypOmegaGen
  have ht := hL.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hNt : Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    (TightLargeHypR.typeRFam hL).tight _ hK t ht
  let H : Subgroup Y :=
    { carrier := {y | conjSub y (tightCore R) = tightCore R ∧
        ∀ x ∈ tightCore R, y * x * y⁻¹ * x⁻¹ ∈ oddCoreOf (tightCore R)}
      one_mem' := ⟨conjSub_one _, fun x _ => by
        rw [show (1 : Y) * x * 1⁻¹ * x⁻¹ = 1 by group]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨by rw [conjSub_mul, hb, ha], fun x hx => ?_⟩
        have h3 := Subgroup.mul_mem _ (conj_mem_oddCoreOf ha (hb' x hx)) (ha' x hx)
        rwa [show a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) =
          a * b * x * (a * b)⁻¹ * x⁻¹ by group] at h3
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        have ha1 : conjSub a⁻¹ (tightCore R) = tightCore R := by
          conv_lhs => rw [← ha]
          rw [conjSub_inv_conjSub]
        refine ⟨ha1, fun x hx => ?_⟩
        have h2 := Subgroup.inv_mem _ (ha' _ (conj_mem_of_conjSub_eq ha1 hx))
        rwa [show (a * (a⁻¹ * x * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * x * a⁻¹⁻¹)⁻¹)⁻¹ =
          a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ by group] at h2 }
  suffices hle : linkLayer R t ≤ H from (hle hy).2 x hx
  refine iSup₂_le fun J hJ => ?_
  obtain ⟨u', hu'⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨hJΩ, hJne, T, hT, hTJ, hTN⟩ := id hJ
  have hTs : IsSylow2In T J := Q3CL.Sec7.isSylow2In_of_mem_RSet_of_le hΩ hT hJΩ hTJ
  have hTt : T ≤ Subgroup.centralizer ({t} : Set Y) := fun z hz =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hTN hz)
  have hTs' : IsSylow2In T (J ⊓ Subgroup.centralizer ({t} : Set Y)) :=
    ⟨le_inf hTJ hTt, hTs.2.1, fun V' hV'M hV'2 hle => hTs.2.2 V' (hV'M.trans inf_le_left) hV'2 hle⟩
  show tightCore (J ⊓ Subgroup.centralizer ({t} : Set Y)) ≤ H
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨hgJt, hg2⟩
  obtain ⟨V, hV, hgV⟩ := IsSylow2In.exists_ge hg2 (Subgroup.zpowers_le.mpr hgJt)
  obtain ⟨c, hc, hcV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hTs' hV
  have hVJ : IsSylow2In V J := by
    rw [← hcV]
    have h1 := hTs.conj c
    rwa [conjSub_eq_self_of_mem hc.1] at h1
  have hcomm := Q3CL.Thompson.comm_le_oddCore_of_isSylow2In Sec6Gen.l6_2Gen hΩ hK hJΩ
    (Ne.symm hJne) ht hu' hVJ (hV.1.trans inf_le_right)
  refine ⟨mem_normalizer_iff_conjSub_eq.mp (hNt hgJt.2), fun x hx => ?_⟩
  exact hcomm (Subgroup.commutator_mem_commutator (hgV (Subgroup.mem_zpowers g)) hx)

private noncomputable def linkChi (hL : TightLargeHypR 3 n Y R S t) :
    ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y)) →* MulAut ↥(linkGrp R t) :=
  (MulAut.congr (linkLayerEquiv hL)).toMonoidHom.comp
    ((oddCoreQuotientAut ↥(linkLayer R t)).comp (normalizerConj (linkLayer R t)))

private theorem linkLayerHom'_eq (hL : TightLargeHypR 3 n Y R S t) (z : ↥(linkLayer R t)) :
    linkLayerHom' hL z = linkLayerEquiv hL (QuotientGroup.mk z) :=
  Subtype.ext (linkLayerEquiv_mk hL z).symm

private theorem linkChi_apply (hL : TightLargeHypR 3 n Y R S t)
    (c : ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))) (z : ↥(linkLayer R t)) :
    linkChi hL c (linkLayerHom' hL z) = linkLayerHom' hL (normalizerConj (linkLayer R t) c z) := by
  rw [linkLayerHom'_eq, linkLayerHom'_eq]
  simp only [linkChi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private theorem mem_oddCoreOf_of_linkLayerHom'_eq (hL : TightLargeHypR 3 n Y R S t)
    {a b : ↥(linkLayer R t)} (h : linkLayerHom' hL a = linkLayerHom' hL b) :
    (a : Y) * (b : Y)⁻¹ ∈ oddCoreOf (linkLayer R t) := by
  have h1 : a * b⁻¹ ∈ (linkLayerHom' hL).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rw [ker_linkLayerHom] at h1
  exact ⟨_, h1, rfl⟩

private theorem linkLayerHom'_eq_of_mem (hL : TightLargeHypR 3 n Y R S t)
    {a b : ↥(linkLayer R t)} (h : (a : Y) * (b : Y)⁻¹ ∈ oddCoreOf (linkLayer R t)) :
    linkLayerHom' hL a = linkLayerHom' hL b := by
  obtain ⟨o, ho, hoe⟩ := h
  have e : o = a * b⁻¹ := Subtype.ext hoe
  have h1 : a * b⁻¹ ∈ (linkLayerHom' hL).ker := by
    rw [ker_linkLayerHom, ← e]
    exact ho
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

private theorem linkChi_eq_conj_iff (hL : TightLargeHypR 3 n Y R S t)
    (c : ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))) (w : ↥(linkLayer R t)) :
    linkChi hL c = MulAut.conj (linkLayerHom' hL w) ↔ ActsLike (linkLayer R t) c w := by
  constructor
  · intro h z hz
    have h1 : linkChi hL c (linkLayerHom' hL ⟨z, hz⟩) =
        MulAut.conj (linkLayerHom' hL w) (linkLayerHom' hL ⟨z, hz⟩) := by rw [h]
    rw [linkChi_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h1
    exact mem_oddCoreOf_of_linkLayerHom'_eq hL h1
  · intro h
    ext x
    obtain ⟨z, rfl⟩ := linkLayerHom'_surjective hL x
    rw [linkChi_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    exact congrArg Subtype.val (linkLayerHom'_eq_of_mem hL (h z z.2))

private theorem linkChi_eq_one_iff (hL : TightLargeHypR 3 n Y R S t)
    (c : ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))) :
    linkChi hL c = 1 ↔ ActsTriv (linkLayer R t) c := by
  rw [actsTriv_iff, show (1 : MulAut ↥(linkGrp R t)) = MulAut.conj (linkLayerHom' hL 1) by
    rw [map_one, map_one]]
  exact linkChi_eq_conj_iff hL c 1

private theorem card_psl2_of_mod16 {F : Type} [Field F] [Finite F] (h16 : Nat.card F % 16 = 9) :
    ∃ m : ℕ, Odd m ∧ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 8 * m := by
  rw [OrderReductions.LinearOrders.card_projectiveSpecialLinear F 2 (by norm_num)]
  obtain ⟨a, ha⟩ : ∃ a, Nat.card F = 16 * a + 9 := ⟨Nat.card F / 16, by omega⟩
  have hprod : ∏ index ∈ Finset.Icc 2 2, (Nat.card F ^ index - 1) = Nat.card F ^ 2 - 1 := by simp
  have hgcd : Nat.gcd 2 (Nat.card F - 1) = 2 := by
    rw [ha, show 16 * a + 9 - 1 = 2 * (8 * a + 4) by omega]
    exact Nat.gcd_mul_right_right _ _
  have hsq : Nat.card F ^ 2 - 1 = 16 * ((2 * a + 1) * (8 * a + 5)) := by
    have h1 : Nat.card F ^ 2 = 16 * ((2 * a + 1) * (8 * a + 5)) + 1 := by rw [ha]; ring
    omega
  refine ⟨(16 * a + 9) * ((2 * a + 1) * (8 * a + 5)), ?_, ?_⟩
  · refine Odd.mul ⟨8 * a + 4, by ring⟩ (Odd.mul ⟨a, by ring⟩ ⟨4 * a + 2, by ring⟩)
  · rw [hprod, hgcd, hsq, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one, ha,
      show (16 * a + 9) * (16 * ((2 * a + 1) * (8 * a + 5))) =
        2 * (8 * ((16 * a + 9) * ((2 * a + 1) * (8 * a + 5)))) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]

private theorem Z2Set.fstar_card (hs : Z2Set n R S t J u R₀ T₀ P) :
    (∃ m : ℕ, Odd m ∧ Nat.card ↥(genFittingFStar ↥(linkGrp R t)) = 8 * m) ∧
      Subgroup.center ↥(genFittingFStar ↥(linkGrp R t)) = ⊥ := by
  obtain ⟨p, f, hp, hp2, hf, h16, hk⟩ := hs.mod16
  haveI := hs.simple
  obtain ⟨-, -, F, _, _, hFc, ⟨e⟩⟩ := MF163.psl2_of_lieModel hk
  obtain ⟨m, hm, hcardF⟩ := card_psl2_of_mod16 (F := F) (by rw [hFc]; exact h16)
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center ↥(genFittingFStar ↥(linkGrp R t)))
  have h2 : Nat.card (↥(genFittingFStar ↥(linkGrp R t)) ⧸
      Subgroup.center ↥(genFittingFStar ↥(linkGrp R t))) = 8 * m :=
    (Nat.card_congr e.toEquiv).trans hcardF
  rw [h2] at h1
  have hZ : Subgroup.center ↥(genFittingFStar ↥(linkGrp R t)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center ↥(genFittingFStar ↥(linkGrp R t))) with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at h1
      have hpos : 0 < Nat.card ↥(genFittingFStar ↥(linkGrp R t)) := Nat.card_pos
      have hm1 : 1 ≤ m := hm.pos
      nlinarith
  rw [hZ, Subgroup.card_bot, mul_one] at h1
  exact ⟨⟨m, hm, h1⟩, hZ⟩

private theorem Z2Set.card_le_sixteen (hs : Z2Set n R S t J u R₀ T₀ P)
    {D : Subgroup ↥(linkGrp R t)} (hD : IsPGroup 2 ↥D) : Nat.card ↥D ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨m, hm, hcard⟩, -⟩ := hs.fstar_card
  set N := genFittingFStar ↥(linkGrp R t) with hN
  haveI : N.Normal := CFSG.ClassicalInvolution.genFittingFStar_normal _
  have h1 := Subgroup.relIndex_mul_card N D
  have h2 : N.relIndex D ≤ 2 := by
    have h3 := Subgroup.relIndex_dvd_index_of_normal N D
    have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact (Nat.le_of_dvd hpos h3).trans hs.index
  have h3 : Nat.card ↥(N ⊓ D) ≤ 8 := by
    have hp2 : IsPGroup 2 ↥(N ⊓ D) := hD.to_le inf_le_right
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hp2
    have hdvd : Nat.card ↥(N ⊓ D) ∣ 8 * m := hcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ k) m :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
    exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hdvd)
  calc Nat.card ↥D = N.relIndex D * Nat.card ↥(N ⊓ D) := h1.symm
    _ ≤ 2 * 8 := Nat.mul_le_mul h2 h3
    _ = 16 := by norm_num

private theorem Z2Set.conj_injective (hs : Z2Set n R S t J u R₀ T₀ P) :
    Function.Injective (MulAut.conj : ↥(linkGrp R t) →* MulAut ↥(linkGrp R t)) := by
  haveI := hs.simple
  obtain ⟨⟨m, hm, hcard⟩, hZ⟩ := hs.fstar_card
  have hnab : ∃ a b : ↥(genFittingFStar ↥(linkGrp R t)), a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center ↥(genFittingFStar ↥(linkGrp R t)) = ⊤ :=
      eq_top_iff.mpr fun a _ => Subgroup.mem_center_iff.mpr fun b => h b a
    rw [htop] at hZ
    have h1 := congrArg (fun H : Subgroup ↥(genFittingFStar ↥(linkGrp R t)) => Nat.card ↥H) hZ
    simp only [Subgroup.card_top, Subgroup.card_bot] at h1
    have hm1 : 1 ≤ m := hm.pos
    omega
  have hC := CFSG.ClassicalInvolution.centralizer_genFittingFStar_eq_bot hnab
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxC : x ∈ Subgroup.centralizer
      ((genFittingFStar ↥(linkGrp R t) : Subgroup ↥(linkGrp R t)) : Set ↥(linkGrp R t)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    have h1 := congrArg (fun α : MulAut ↥(linkGrp R t) => α y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc y * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  rw [hC] at hxC
  exact hxC

theorem Z2Set.exists_split_t (hs : Z2Set n R S t J u R₀ T₀ P)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    {x : Y} (hx : x ∈ edgeCent (P : Subgroup Y) t u) (hin : InnerModOdd (linkLayer R t) x) :
    ∃ s ∈ edgeCent (P : Subgroup Y) t u, ActsLike (linkLayer R t) s x ∧
      ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht := hs.large.datum.isUniqueInvolution_core
  have hTF := TightLargeHypR.typeRFam hs.large
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.large.datum.hypOmegaGen hK hs.hJ.1 hs.hJ
  obtain ⟨g, hg⟩ := hs.exists_conj_u
  have hgu : g⁻¹ * u * g⁻¹⁻¹ = t := inv_conj_of_conj hg
  have hΛtu : conjSub g (linkLayer R t) = linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
    hs.conjSub_Λt_swap hg
  have hΛut : conjSub g⁻¹ (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayer R t := hs.conjSub_Λu_swap hgu
  have hNt : ∀ {c : Y}, c ∈ Subgroup.centralizer ({t} : Set Y) →
      c ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) := fun hc =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.conjSub_Λt_fix (conj_eq_of_comm
      (Subgroup.mem_centralizer_singleton_iff.mp hc)))
  have hJu : J ≤ Subgroup.centralizer ({u} : Set Y) := hTF.le_centralizer hs.hJ.1 hs.hu
  have hT₀t : T₀ ≤ Subgroup.centralizer ({t} : Set Y) := fun z hz =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hs.hT₀N hz)
  have hT₀Λ : T₀ ≤ linkLayer R t := fun z hz => coreAt_le_linkLayerAt hs.hJ
    (Subgroup.subset_closure ⟨⟨hs.hT₀.1 hz, hT₀t hz⟩,
      hs.hT₀.2.1.to_le (Subgroup.zpowers_le.mpr hz)⟩)
  obtain ⟨eT⟩ := hTF.quat J hs.hJ.1 T₀ hs.hT₀
  have hT₀card : Nat.card ↥T₀ = 8 := by
    rw [Nat.card_congr eT.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have huT : IsUniqueInvolution T₀ u :=
    ⟨CFSG.ClassicalInvolution.Asc77.T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1 (by omega),
      hs.hu.ne_one, hs.hu.sq, fun y hy hy2 => hs.hu.unique y (hs.hT₀.1 hy) hy2⟩
  have hT₀triv : ∀ z ∈ T₀, ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) z := by
    intro z hz
    have hzc : z ∈ coreAt u J := Subgroup.subset_closure ⟨⟨hs.hT₀.1 hz, hJu (hs.hT₀.1 hz)⟩,
      hs.hT₀.2.1.to_le (Subgroup.zpowers_le.mpr hz)⟩
    have hzc' : g⁻¹ * z * g⁻¹⁻¹ ∈ coreAt t (tightCore R) := by
      have h1 := conj_mem_conjSub hzc g⁻¹
      rwa [conjSub_coreAt_conj, hgu, hs.conjSub_J_swap hgu] at h1
    have h2 := actsTriv_conj (fun y hy => commutator_mem_oddCoreOf_linkLayer' hs.large hzc' hy) g
    rwa [hΛtu, show g * (g⁻¹ * z * g⁻¹⁻¹) * g⁻¹ = z by group] at h2
  obtain ⟨Q, hQ⟩ := (hs.hT₀.2.1.comap_of_injective (linkLayer R t).subtype
    Subtype.val_injective).exists_le_sylow
  set S₂ : Subgroup Y := (Q : Subgroup ↥(linkLayer R t)).map (linkLayer R t).subtype with hS₂def
  have hS₂Λ : S₂ ≤ linkLayer R t := Subgroup.map_subtype_le _
  have hT₀S₂ : T₀ ≤ S₂ := fun z hz => ⟨⟨z, hT₀Λ hz⟩, hQ hz, rfl⟩
  have hS₂2 : IsPGroup 2 ↥S₂ := Q.isPGroup'.map _
  have hLQ : Function.Injective
      ((linkLayerHom' hs.large).comp (Q : Subgroup ↥(linkLayer R t)).subtype) := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hq' : (q : ↥(linkLayer R t)) ∈ (linkLayerHom' hs.large).ker := hq
    rw [ker_linkLayerHom] at hq'
    exact Subtype.ext (eq_one_of_isPGroup_of_mem_odd
      (CFSG.ComponentClassification.OddCore.odd_card ↥(linkLayer R t)) hq'
      (Q.isPGroup'.to_le (Subgroup.zpowers_le.mpr q.2)))
  have hQcard : Nat.card ↥(Q : Subgroup ↥(linkLayer R t)) ≤ 16 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hLQ).toEquiv]
    exact hs.card_le_sixteen (Q.isPGroup'.of_equiv (MonoidHom.ofInjective hLQ))
  have hS₂card : Nat.card ↥S₂ ≤ 16 := by
    rw [hS₂def, Subgroup.card_map_of_injective Subtype.val_injective]
    exact hQcard
  have hidx : T₀.relIndex S₂ ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card T₀ S₂
    rw [inf_eq_left.mpr hT₀S₂, hT₀card] at h1
    omega
  have hS₂T : ∀ s ∈ S₂, s * s ∈ T₀ ∧ ∀ z ∈ T₀, s * z * s⁻¹ ∈ T₀ := by
    intro s hs₂
    have hpos : T₀.relIndex S₂ ≠ 0 := by
      intro h0
      have h1 := Subgroup.relIndex_mul_card T₀ S₂
      rw [h0, zero_mul] at h1
      exact absurd h1.symm Nat.card_pos.ne'
    rcases (by omega : T₀.relIndex S₂ = 1 ∨ T₀.relIndex S₂ = 2) with h1 | h2
    · have hsT : s ∈ T₀ := Subgroup.relIndex_eq_one.mp h1 hs₂
      exact ⟨T₀.mul_mem hsT hsT, fun z hz => T₀.mul_mem (T₀.mul_mem hsT hz) (T₀.inv_mem hsT)⟩
    · have h2' : (T₀.subgroupOf S₂).index = 2 := h2
      haveI := Subgroup.normal_of_index_eq_two h2'
      refine ⟨?_, fun z hz => ?_⟩
      · have h3 := Subgroup.sq_mem_of_index_two h2' ⟨s, hs₂⟩
        rw [Subgroup.mem_subgroupOf] at h3
        simpa [sq] using h3
      · have h3 := (inferInstance : (T₀.subgroupOf S₂).Normal).conj_mem ⟨z, hT₀S₂ hz⟩
          (Subgroup.mem_subgroupOf.mpr hz) ⟨s, hs₂⟩
        rw [Subgroup.mem_subgroupOf] at h3
        exact h3
  have hS₂N : ∀ s ∈ S₂, conjSub s T₀ = T₀ := by
    intro s hs₂
    refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
    · rw [mem_conjSub_iff] at hz
      have h1 := (hS₂T s hs₂).2 _ hz
      rwa [show s * (s⁻¹ * z * s) * s⁻¹ = z by group] at h1
    · rw [mem_conjSub_iff]
      have h1 := (hS₂T s⁻¹ (S₂.inv_mem hs₂)).2 z hz
      rwa [inv_inv] at h1
  have hS₂u : S₂ ≤ Subgroup.centralizer ({u} : Set Y) := fun s hs₂ =>
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      have h1 := huT.conj_eq (hS₂N s hs₂)
      calc s * u = s * u * s⁻¹ * s := by group
        _ = u * s := by rw [h1])
  have hS₂t : S₂ ≤ Subgroup.centralizer ({t} : Set Y) := hS₂Λ.trans linkLayerAt_le_centralizer
  have hS₂M : S₂ ≤ Subgroup.normalizer
      ((tightCore R ⊓ Subgroup.centralizer ({u} : Set Y) : Subgroup Y) : Set Y) := by
    intro s hs₂
    rw [mem_normalizer_iff_conjSub_eq, conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj s).injective]
    have h1 : conjSub s (tightCore R) = tightCore R := hs.conjSub_K_fix
      (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp (hS₂t hs₂)))
    have h2 : conjSub s (Subgroup.centralizer ({u} : Set Y)) =
        Subgroup.centralizer ({u} : Set Y) := by
      rw [Balance.conjSub_centralizer_singleton,
        conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp (hS₂u hs₂))]
    exact congrArg₂ (· ⊓ ·) h1 h2
  obtain ⟨X₀, hX₀, hS₂X₀⟩ := IsSylow2In.exists_ge hS₂2
    (le_sup_right : S₂ ≤ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) ⊔ S₂)
  have hR₀' := Asc77.isSylow2In_inf_of_le_normalizer hX₀ le_sup_left
    (sup_le Subgroup.le_normalizer hS₂M)
  have hR₀M : IsSylow2In R₀ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) :=
    ⟨le_inf hs.hR₀.1 hs.hR₀u, hs.hR₀.2.1, fun V hVM hV2 hle =>
      hs.hR₀.2.2 V (hVM.trans inf_le_left) hV2 hle⟩
  obtain ⟨m, hm, hmR⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hR₀M hR₀'
  have hR₀'K : IsSylow2In (X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)))
      (tightCore R) := by
    rw [← hmR]
    have h1 := hs.hR₀.conj m
    rwa [conjSub_eq_self_of_mem hm.1] at h1
  have hS₂R : ∀ s ∈ S₂, ∀ r ∈ X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)),
      s * r = r * s := by
    intro s hs₂ r hr
    have hsr : s * r * s⁻¹ ∈ X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) :=
      ⟨X₀.mul_mem (X₀.mul_mem (hS₂X₀ hs₂) hr.1) (X₀.inv_mem (hS₂X₀ hs₂)),
        (Subgroup.mem_normalizer_iff.mp (hS₂M hs₂) r).mp hr.2⟩
    have hc := Subgroup.mul_mem _ hsr (Subgroup.inv_mem _ hr)
    have hcO := linkLayer_commutator_mem_oddCoreOf_core hs.large (hS₂Λ hs₂) hr.2.1
    have h1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hcO
      (hR₀'K.2.1.to_le (Subgroup.zpowers_le.mpr hc))
    calc s * r = s * r * s⁻¹ * r⁻¹ * (r * s) := by group
      _ = r * s := by rw [h1, one_mul]
  obtain ⟨eR⟩ := hTF.quat _ hK _ hR₀'K
  have htR₀' : t ∈ X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) := by
    refine CFSG.ClassicalInvolution.Asc77.T3.mem_of_isPGroup ht hR₀'K.1 hR₀'K.2.1 ?_
    rw [Nat.card_congr eR.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hR₀'Λu : X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)) ≤
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := fun r hr =>
    coreAt_le_linkLayerAt hKJ (Subgroup.subset_closure ⟨⟨hr.2.1, hr.2.2⟩,
      hR₀'K.2.1.to_le (Subgroup.zpowers_le.mpr hr)⟩)
  have hQΛ : conjSub g⁻¹ (X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y))) ≤
      linkLayer R t := by
    have h1 := conjSub_mono (n := g⁻¹) hR₀'Λu
    rwa [hΛut] at h1
  set ιQ : ↥(conjSub g⁻¹ (X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)))) →*
      ↥(linkGrp R t) := (linkLayerHom' hs.large).comp (Subgroup.inclusion hQΛ) with hιQdef
  have hιQ : Function.Injective ιQ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hq' : Subgroup.inclusion hQΛ q ∈ (linkLayerHom' hs.large).ker := hq
    rw [ker_linkLayerHom] at hq'
    have hQ2 : IsPGroup 2
        ↥(conjSub g⁻¹ (X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)))) :=
      hR₀'K.2.1.map _
    have h1 := eq_one_of_isPGroup_of_mem_odd
      (CFSG.ComponentClassification.OddCore.odd_card ↥(linkLayer R t)) hq'
      ((hQ2.comap_of_injective (linkLayer R t).subtype Subtype.val_injective).to_le
        (Subgroup.zpowers_le.mpr (show Subgroup.inclusion hQΛ q ∈
          (conjSub g⁻¹ (X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)))).subgroupOf
            (linkLayer R t) from q.2)))
    exact Subgroup.inclusion_injective hQΛ (h1.trans (map_one _).symm)
  let eQ : ↥(conjSub g⁻¹ (X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y)))) ≃*
      QuaternionGroup 2 :=
    ((X₀ ⊓ (tightCore R ⊓ Subgroup.centralizer ({u} : Set Y))).equivMapOfInjective
      (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm.trans eR
  let eP : ↥ιQ.range ≃* QuaternionGroup 2 := (MonoidHom.ofInjective hιQ).symm.trans eQ
  have hdΛ : g⁻¹ * t * g⁻¹⁻¹ ∈ linkLayer R t := hQΛ (conj_mem_conjSub htR₀' g⁻¹)
  have heP : ((eP.symm (QuaternionGroup.a 2) : ↥ιQ.range) : ↥(linkGrp R t)) =
      linkLayerHom' hs.large ⟨g⁻¹ * t * g⁻¹⁻¹, hdΛ⟩ := by
    have hinv : ((eR.symm (QuaternionGroup.a 2) : ↥(X₀ ⊓ (tightCore R ⊓
        Subgroup.centralizer ({u} : Set Y)))) : Y) = t := by
      have hsq : ((eR.symm (QuaternionGroup.a 2) : ↥(X₀ ⊓ (tightCore R ⊓
          Subgroup.centralizer ({u} : Set Y)))) : Y) * (eR.symm (QuaternionGroup.a 2) : Y) = 1 := by
        rw [← Subgroup.coe_mul, ← map_mul, show QuaternionGroup.a 2 * QuaternionGroup.a 2 =
          (1 : QuaternionGroup (2 ^ (3 - 2))) by decide, map_one, Subgroup.coe_one]
      rcases ht.unique _ (hR₀'K.1 (eR.symm _).2) hsq with h | h
      · exfalso
        have h1 : eR.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
        rw [map_eq_one_iff _ eR.symm.injective] at h1
        exact absurd h1 (by decide)
      · exact h
    show ιQ (eQ.symm (QuaternionGroup.a 2)) = _
    rw [hιQdef, MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    show ((eQ.symm (QuaternionGroup.a 2) : ↥(conjSub g⁻¹ (X₀ ⊓ (tightCore R ⊓
      Subgroup.centralizer ({u} : Set Y))))) : Y) = _
    show (MulAut.conj g⁻¹) ((eR.symm (QuaternionGroup.a 2) : ↥(X₀ ⊓ (tightCore R ⊓
      Subgroup.centralizer ({u} : Set Y)))) : Y) = _
    rw [MulAut.conj_apply, hinv]
  obtain ⟨p, f, hp, hp2, hf, h9, hk⟩ := hs.model
  have hsplit : ∀ s ∈ S₂, ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) s ∨
      ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (s * t) := by
    intro s hs₂
    have hct : g⁻¹ * s * g⁻¹⁻¹ ∈ Subgroup.centralizer ({t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hgu]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hS₂u hs₂)
      rw [show g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * u * g⁻¹⁻¹) = g⁻¹ * (s * u) * g⁻¹⁻¹ by group, h1]
      group
    have hcN := hNt hct
    have hc2 : ActsTriv (linkLayer R t) (g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * s * g⁻¹⁻¹)) := by
      have h1 := actsTriv_conj (hT₀triv _ (hS₂T s hs₂).1) g⁻¹
      rwa [hΛut, show g⁻¹ * (s * s) * g⁻¹⁻¹ = g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * s * g⁻¹⁻¹) by group] at h1
    have hβ2 : linkChi hs.large ⟨_, hcN⟩ * linkChi hs.large ⟨_, hcN⟩ = 1 := by
      rw [← map_mul]
      exact (linkChi_eq_one_iff hs.large _).mpr hc2
    have hβP : ∀ y ∈ ιQ.range, linkChi hs.large ⟨_, hcN⟩ y = y := by
      rintro _ ⟨q, rfl⟩
      rw [hιQdef, MonoidHom.comp_apply, linkChi_apply]
      congr 1
      apply Subtype.ext
      obtain ⟨r, hr, hrq⟩ := q.2
      show g⁻¹ * s * g⁻¹⁻¹ * (q : Y) * (g⁻¹ * s * g⁻¹⁻¹)⁻¹ = q
      have hrq' : (q : Y) = g⁻¹ * r * g⁻¹⁻¹ := hrq.symm
      rw [hrq', show g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * r * g⁻¹⁻¹) * (g⁻¹ * s * g⁻¹⁻¹)⁻¹ =
        g⁻¹ * (s * r) * s⁻¹ * g⁻¹⁻¹ by group, hS₂R s hs₂ r hr]
      group
    rcases model163L2Q8_proved ↥(linkGrp R t) hs.simple hs.index p f hp hp2 hf h9 hk ιQ.range
      eP _ hβ2 hβP with h | h
    · left
      have h1 := actsTriv_conj ((linkChi_eq_one_iff hs.large _).mp h) g
      rwa [hΛtu, show g * (g⁻¹ * s * g⁻¹⁻¹) * g⁻¹ = s by group] at h1
    · right
      rw [heP] at h
      have hcd := (linkChi_eq_conj_iff hs.large _ _).mp h
      have h1 := actsLike_mul hcd (actsLike_refl _ (g⁻¹ * t * g⁻¹⁻¹)⁻¹)
        (conjSub_eq_self_of_mem ((linkLayer R t).inv_mem hdΛ))
        (mem_normalizer_iff_conjSub_eq.mp hcN)
      rw [mul_inv_cancel] at h1
      have h2 := actsTriv_conj (actsTriv_iff.mpr h1) g
      rwa [hΛtu, show g * (g⁻¹ * s * g⁻¹⁻¹ * (g⁻¹ * t * g⁻¹⁻¹)⁻¹) * g⁻¹ = s * t⁻¹ by group,
        inv_eq_of_mul_eq_one_left hs.t2] at h2
  let Ku : Subgroup Y :=
    { carrier := {c | c ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) ∧
        ActsTriv (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) c}
      one_mem' := ⟨Subgroup.one_mem _, fun z _ => by
        rw [show (1 : Y) * z * 1⁻¹ * z⁻¹ = 1 by group]
        exact Subgroup.one_mem _⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, actsTriv_iff.mpr ?_⟩
        have h1 := actsLike_mul (actsTriv_iff.mp ha') (actsTriv_iff.mp hb') (by rw [conjSub_one])
          (hs.conjSub_Λu_fix (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp ha.2)))
        rwa [mul_one] at h1
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, actsTriv_iff.mpr ?_⟩
        have h1 := actsLike_inv (actsTriv_iff.mp ha') (by rw [inv_one, conjSub_one])
          (hs.conjSub_Λu_fix (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp
            (Subgroup.inv_mem _ ha.2))))
        rwa [inv_one] at h1 }
  have hKuE : Ku ≤ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) :=
    fun c hc => hc.1
  have hKuN : Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) ≤
      Subgroup.normalizer (Ku : Set Y) := by
    have key : ∀ e ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y),
        ∀ c ∈ Ku, e * c * e⁻¹ ∈ Ku := by
      intro e he c hc
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ he hc.1) (Subgroup.inv_mem _ he), ?_⟩
      have h1 := actsTriv_conj hc.2 e
      rwa [hs.conjSub_Λu_fix (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp he.2))]
        at h1
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro c
    refine ⟨key e he c, fun h => ?_⟩
    have h1 := key e⁻¹ (Subgroup.inv_mem _ he) _ h
    rwa [show e⁻¹ * (e * c * e⁻¹) * e⁻¹⁻¹ = c by group] at h1
  have hA2 : IsPGroup 2 ↥(edgeCent (P : Subgroup Y) t u) :=
    P.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hAE : IsSylow2In (edgeCent (P : Subgroup Y) t u)
      (Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y)) := by
    refine ⟨fun c hc => ⟨hc.1.2, hc.2⟩, hA2, fun V hVE hV2 hAV => ?_⟩
    obtain ⟨c, -, hcV⟩ := hs.exists_conj_le_edgeCent hV2 (hVE.trans inf_le_left)
      (hVE.trans inf_le_right)
    have hcard : Nat.card ↥V ≤ Nat.card ↥(edgeCent (P : Subgroup Y) t u) := by
      rw [← natCard_conjSub' c V]
      exact Subgroup.card_le_of_le hcV
    exact (Subgroup.eq_of_le_of_card_ge hAV hcard).symm
  have hB := Asc77.isSylow2In_inf_of_le_normalizer hAE hKuE hKuN
  have ht2 : IsPGroup 2 ↥(Subgroup.zpowers t) := Balance.isPGroup_zpowers_of_mul_self_eq_one hs.t2
  have hS₂tN : S₂ ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup Y) : Set Y) := by
    intro s hs₂
    rw [Subgroup.mem_normalizer_iff]
    intro z
    obtain hst := Subgroup.mem_centralizer_singleton_iff.mp (hS₂t hs₂)
    have hc : ∀ w ∈ Subgroup.zpowers t, s * w * s⁻¹ = w := by
      rintro _ ⟨k, rfl⟩
      exact conj_eq_of_comm ((Commute.zpow_right (show Commute s t from hst) k).eq)
    constructor
    · intro hz
      rw [hc z hz]
      exact hz
    · intro hz
      have h1 : z = s⁻¹ * (s * z * s⁻¹) * s := by group
      rw [h1, show s⁻¹ * (s * z * s⁻¹) * s = s⁻¹ * (s * z * s⁻¹) * s⁻¹⁻¹ by group]
      have hs' : s⁻¹ * (s * z * s⁻¹) * s⁻¹⁻¹ = s * z * s⁻¹ := by
        have hst' : s⁻¹ * t = t * s⁻¹ := by
          rw [Subgroup.mem_centralizer_singleton_iff.symm]
          exact Subgroup.inv_mem _ (hS₂t hs₂)
        obtain ⟨k, hk⟩ := hz
        rw [← hk]
        exact conj_eq_of_comm ((Commute.zpow_right (show Commute s⁻¹ t from hst') k).eq)
      rw [hs']
      exact hz
  have hH₀2 : IsPGroup 2 ↥((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku) :=
    (hS₂2.to_sup_of_normal_right' ht2 hS₂tN).to_le inf_le_left
  obtain ⟨H₁, hH₁, hH₀H₁⟩ := IsSylow2In.exists_ge hH₀2 inf_le_right
  obtain ⟨k, hk, hkB⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hH₁ hB
  have hH₀B : conjSub k ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku) ≤ edgeCent (P : Subgroup Y) t u ⊓ Ku := by
    rw [← hkB]
    exact conjSub_mono hH₀H₁
  have hCtN : Subgroup.centralizer ({t} : Set Y) ≤
      Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) := fun c hc => hNt hc
  let sharp : Subgroup Y → Subgroup ↥(linkGrp R t) := fun H =>
    ((H.subgroupOf (Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))).map
      (linkChi hs.large)).comap MulAut.conj
  have hmem_sharp : ∀ {H : Subgroup Y} {xb : ↥(linkGrp R t)}, xb ∈ sharp H ↔
      ∃ c : ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y)), (c : Y) ∈ H ∧
        linkChi hs.large c = MulAut.conj xb := by
    intro H xb
    simp only [sharp, Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  have hsharp_mono : ∀ {H H' : Subgroup Y}, H ≤ H' → sharp H ≤ sharp H' := by
    intro H H' hle xb hx
    obtain ⟨c, hc, hcx⟩ := hmem_sharp.mp hx
    exact hmem_sharp.mpr ⟨c, hle hc, hcx⟩
  have hsharpA2 : IsPGroup 2 ↥(sharp (edgeCent (P : Subgroup Y) t u)) :=
    ((hA2.comap_of_injective (Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y)).subtype
      Subtype.val_injective).map _).comap_of_injective _ hs.conj_injective
  have htN : t ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) :=
    hCtN (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hχt : linkChi hs.large ⟨t, htN⟩ = 1 := by
    refine (linkChi_eq_one_iff hs.large _).mpr fun z hz => ?_
    have hzt : t * z = z * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
    show t * z * t⁻¹ * z⁻¹ ∈ _
    rw [show t * z * t⁻¹ * z⁻¹ = 1 by rw [hzt]; group]
    exact Subgroup.one_mem _
  have htE : t ∈ Subgroup.centralizer ({t} : Set Y) ⊓ Subgroup.centralizer ({u} : Set Y) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
      Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm⟩
  have hQH₀ : (Q : Subgroup ↥(linkLayer R t)).map (linkLayerHom' hs.large) ≤
      sharp ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku) := by
    rintro _ ⟨q, hq, rfl⟩
    have hs₂ : (q : Y) ∈ S₂ := ⟨q, hq, rfl⟩
    have hqN : (q : Y) ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) :=
      hCtN (hS₂t hs₂)
    have hχq : linkChi hs.large ⟨q, hqN⟩ = MulAut.conj (linkLayerHom' hs.large q) :=
      (linkChi_eq_conj_iff hs.large _ q).mpr (actsLike_refl _ _)
    have hqE : (q : Y) ∈ Subgroup.centralizer ({t} : Set Y) ⊓
        Subgroup.centralizer ({u} : Set Y) := ⟨hS₂t hs₂, hS₂u hs₂⟩
    rcases hsplit _ hs₂ with h | h
    · exact hmem_sharp.mpr ⟨⟨q, hqN⟩, ⟨Subgroup.mem_sup_left hs₂, hqE, h⟩, hχq⟩
    · refine hmem_sharp.mpr ⟨⟨q, hqN⟩ * ⟨t, htN⟩,
        ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left hs₂)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)), Subgroup.mul_mem _ hqE htE, h⟩, ?_⟩
      rw [map_mul, hχt, mul_one, hχq]
  have hkN : k ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) := hCtN hk.1.1
  have hconjk : (sharp ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku)).map
      (linkChi hs.large ⟨k, hkN⟩).toMonoidHom ≤
        sharp (conjSub k ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku)) := by
    rintro _ ⟨xb, hxb, rfl⟩
    obtain ⟨c, hc, hcx⟩ := hmem_sharp.mp hxb
    refine hmem_sharp.mpr ⟨⟨k, hkN⟩ * c * ⟨k, hkN⟩⁻¹, conj_mem_conjSub hc k, ?_⟩
    rw [map_mul, map_mul, map_inv, hcx]
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.coe_toMonoidHom, map_mul, map_inv,
      MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hQ'card : ∀ {D : Subgroup ↥(linkGrp R t)}, IsPGroup 2 ↥D →
      Nat.card ↥D ≤ Nat.card ↥((Q : Subgroup ↥(linkLayer R t)).map (linkLayerHom' hs.large)) := by
    intro D hD
    obtain ⟨P', hP'⟩ := hD.exists_le_sylow
    have h1 := Subgroup.card_le_of_le hP'
    have e1 : Nat.card ↥((Q : Subgroup ↥(linkLayer R t)).map (linkLayerHom' hs.large)) =
        Nat.card ↥(P' : Subgroup ↥(linkGrp R t)) := by
      rw [← Sylow.coe_mapSurjective (linkLayerHom'_surjective hs.large) Q,
        Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    exact h1.trans e1.ge
  have hcard_chain : Nat.card ↥(sharp (edgeCent (P : Subgroup Y) t u)) ≤
      Nat.card ↥(sharp (edgeCent (P : Subgroup Y) t u ⊓ Ku)) := by
    calc Nat.card ↥(sharp (edgeCent (P : Subgroup Y) t u))
        ≤ Nat.card ↥((Q : Subgroup ↥(linkLayer R t)).map (linkLayerHom' hs.large)) :=
          hQ'card hsharpA2
      _ ≤ Nat.card ↥(sharp ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku)) := Subgroup.card_le_of_le hQH₀
      _ = Nat.card ↥((sharp ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku)).map
            (linkChi hs.large ⟨k, hkN⟩).toMonoidHom) :=
          (Subgroup.card_map_of_injective (linkChi hs.large ⟨k, hkN⟩).injective).symm
      _ ≤ Nat.card ↥(sharp (conjSub k ((S₂ ⊔ Subgroup.zpowers t) ⊓ Ku))) :=
          Subgroup.card_le_of_le hconjk
      _ ≤ Nat.card ↥(sharp (edgeCent (P : Subgroup Y) t u ⊓ Ku)) :=
          Subgroup.card_le_of_le (hsharp_mono hH₀B)
  have hBA : sharp (edgeCent (P : Subgroup Y) t u ⊓ Ku) = sharp (edgeCent (P : Subgroup Y) t u) :=
    Subgroup.eq_of_le_of_card_ge (hsharp_mono inf_le_left) hcard_chain
  obtain ⟨w, hw, hxw⟩ := hin
  have hxN : x ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) := hCtN hx.1.2
  have hχx : linkChi hs.large ⟨x, hxN⟩ = MulAut.conj (linkLayerHom' hs.large ⟨w, hw⟩) :=
    (linkChi_eq_conj_iff hs.large _ ⟨w, hw⟩).mpr hxw
  have hwA : linkLayerHom' hs.large ⟨w, hw⟩ ∈ sharp (edgeCent (P : Subgroup Y) t u) :=
    hmem_sharp.mpr ⟨⟨x, hxN⟩, hx, hχx⟩
  rw [← hBA] at hwA
  obtain ⟨b, hbB, hbw⟩ := hmem_sharp.mp hwA
  have hbw' := (linkChi_eq_conj_iff hs.large b ⟨w, hw⟩).mp hbw
  exact ⟨b, hbB.1, actsLike_trans hbw' (actsLike_symm hxw), hbB.2.2⟩

theorem Z2Set.innerModOdd_conj_swap (hs : Z2Set n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) (x : Y) :
    InnerModOdd (linkLayer R t) x ↔
      InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (b * x * b⁻¹) := by
  rw [innerModOdd_conj_iff x b, hs.conjSub_Λt_swap hbt]

theorem Z2Set.exists_involution_of_inner_sq (hs : Z2Set n R S t J u R₀ T₀ P)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    {b : Y} (hbP : b ∈ (P : Subgroup Y)) (hbA : b ∉ edgeCent (P : Subgroup Y) t u)
    (hin : InnerModOdd (linkLayer R t) (b * b)) :
    ∃ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1 := by
  have hbt := hs.swap_of_not_mem hbP hbA
  have hbu := hs.swap_u hbP hbt
  have hbt' : b⁻¹ * t * b⁻¹⁻¹ = u := inv_conj_of_conj hbu
  have hbu' : b⁻¹ * u * b⁻¹⁻¹ = t := inv_conj_of_conj hbt
  have hbb := hs.mul_self_mem_edgeCent hbP
  have hxA : (b * b)⁻¹ ∈ edgeCent (P : Subgroup Y) t u := Subgroup.inv_mem _ hbb
  have hxin : InnerModOdd (linkLayer R t) (b * b)⁻¹ :=
    innerModOdd_inv hin (hs.conjSub_Λt_of_mem hxA)
  obtain ⟨s, hsA, hs1, hs2⟩ := hs.exists_split_t hall hxA hxin
  have hcP : b * s ∈ (P : Subgroup Y) := (P : Subgroup Y).mul_mem hbP hsA.1.1
  have hzA : b⁻¹ * s * b⁻¹⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
    hs.conj_mem_edgeCent ((P : Subgroup Y).inv_mem hbP) hsA
  have e : b * s * (b * s) = b * b * (b⁻¹ * s * b⁻¹⁻¹) * s := by group
  refine ⟨b * s, hcP, fun h => hbA ?_, ?_⟩
  · have e' : b = b * s * s⁻¹ := by group
    rw [e']
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hsA)
  refine hs.eq_one_of_actsTriv (hs.mul_self_mem_edgeCent hcP) ?_ ?_
  ·
    rw [e, actsTriv_iff]
    have h1 : ActsLike (linkLayer R t) (b⁻¹ * s * b⁻¹⁻¹) 1 := by
      have h := actsLike_conj (actsTriv_iff.mp hs2) b⁻¹
      rwa [hs.conjSub_Λu_swap hbu', show b⁻¹ * 1 * b⁻¹⁻¹ = 1 by group] at h
    have h2 := actsLike_mul (actsLike_refl _ (b * b)) h1 (by rw [conjSub_one])
      (hs.conjSub_Λt_of_mem hbb)
    have h3 := actsLike_mul h2 hs1 (hs.conjSub_Λt_of_mem hxA)
      (hs.conjSub_Λt_of_mem (Subgroup.mul_mem _ hbb hzA))
    rwa [show b * b * 1 * (b * b)⁻¹ = 1 by group] at h3
  ·
    rw [e, actsTriv_iff]
    have h1 : ActsLike (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
        (b⁻¹ * s * b⁻¹⁻¹) (b * b)⁻¹ := by
      have h := actsLike_conj hs1 b⁻¹
      rwa [hs.conjSub_Λt_swap hbt', show b⁻¹ * (b * b)⁻¹ * b⁻¹⁻¹ = (b * b)⁻¹ by group] at h
    have h2 := actsLike_mul (actsLike_refl _ (b * b)) h1 (hs.conjSub_Λu_of_mem hxA)
      (hs.conjSub_Λu_of_mem hbb)
    have h3 := actsLike_mul h2 (actsTriv_iff.mp hs2) (by rw [conjSub_one])
      (hs.conjSub_Λu_of_mem (Subgroup.mul_mem _ hbb hzA))
    rwa [show b * b * (b * b)⁻¹ * 1 = 1 by group] at h3

theorem Z2Set.innerModOdd_mul_inv_of_outer (hs : Z2Set n R S t J u R₀ T₀ P) {x y : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) (hy : y ∈ edgeCent (P : Subgroup Y) t u)
    (hxo : ¬ InnerModOdd (linkLayer R t) x) (hyo : ¬ InnerModOdd (linkLayer R t) y) :
    InnerModOdd (linkLayer R t) (x * y⁻¹) := by
  classical
  let χ : ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y)) →*
      MulAut ↥(linkGrp R t) :=
    (MulAut.congr (linkLayerEquiv hs.large)).toMonoidHom.comp
      ((oddCoreQuotientAut ↥(linkLayer R t)).comp (normalizerConj (linkLayer R t)))
  have hN : ∀ {c : Y}, c ∈ edgeCent (P : Subgroup Y) t u →
      c ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) := fun hc =>
    mem_normalizer_iff_conjSub_eq.mpr (hs.conjSub_Λt_of_mem hc)
  have hact : ∀ (c : ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y)))
      (w : ↥(linkGrp R t)), χ c = MulAut.conj w → InnerModOdd (linkLayer R t) c := by
    intro c w hcw
    obtain ⟨q, rfl⟩ := (linkLayerEquiv hs.large).surjective w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨w', w'.2, fun z hz => ?_⟩
    have h1 := congrArg (fun α : MulAut ↥(linkGrp R t) =>
      α (linkLayerEquiv hs.large (QuotientGroup.mk ⟨z, hz⟩))) hcw
    simp only [χ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    have h2 := (linkLayerEquiv hs.large).injective h1
    rw [oddCoreQuotientAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] at h2
    have hcz : (c : Y) * z * (c : Y)⁻¹ ∈ linkLayer R t :=
      conj_mem_of_conjSub_eq (mem_normalizer_iff_conjSub_eq.mp c.2) hz
    have hwz : (w' : Y) * z * (w' : Y)⁻¹ ∈ linkLayer R t :=
      (linkLayer R t).mul_mem ((linkLayer R t).mul_mem w'.2 hz) ((linkLayer R t).inv_mem w'.2)
    have e1 : (normalizerConj (linkLayer R t) c) ⟨z, hz⟩ = ⟨(c : Y) * z * (c : Y)⁻¹, hcz⟩ := rfl
    have e2 : w' * ⟨z, hz⟩ * w'⁻¹ = (⟨(w' : Y) * z * (w' : Y)⁻¹, hwz⟩ : ↥(linkLayer R t)) := rfl
    rw [e1, e2] at h2
    exact mul_inv_mem_oddCoreOf_of_mk_eq hcz hwz h2
  have hQ : ∃ Q : Subgroup ↥(linkGrp R t), Nonempty (↥Q ≃* QuaternionGroup 2) := by
    have hsec := lieLinkSection_of hs.large hs.z2.1
    have hmem : (secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t) ∈
        linkFam R t := ⟨_, ⟨J, hs.hJ, rfl⟩, le_linkGrp hs.hJ, rfl⟩
    obtain ⟨Q, hQ, -⟩ := IsSylow2In.exists_ge (T := ⊥)
      (P := (secImg (CoreAssembly.conjClass (tightCore R)) t J).subgroupOf (linkGrp R t))
      IsPGroup.of_bot bot_le
    exact ⟨Q, hsec.1.quat _ hmem Q hQ⟩
  obtain ⟨Q, hQ⟩ := hQ
  obtain ⟨p, f, hp, hp2, hf, h16, hk⟩ := hs.mod16
  have hM := (modelOutL2_proved ↥(linkGrp R t) hs.simple hs.index p f hp hp2 hf h16 hk Q hQ).2
  have h2pow : ∀ {c : Y} (hc : c ∈ edgeCent (P : Subgroup Y) t u),
      ∃ k : ℕ, χ ⟨c, hN hc⟩ ^ 2 ^ k = 1 := by
    intro c hc
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨c, hc.1.1⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have e : (⟨c, hN hc⟩ : ↥(Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y))) ^ 2 ^ k
        = 1 := Subtype.ext (by
      have h1 := congrArg Subtype.val hk
      simpa using h1)
    rw [e, map_one]
  have hout : ∀ {c : Y} (hc : c ∈ edgeCent (P : Subgroup Y) t u),
      ¬ InnerModOdd (linkLayer R t) c → ¬ ∃ w, χ ⟨c, hN hc⟩ = MulAut.conj w :=
    fun hc hco ⟨w, hw⟩ => hco (hact _ w hw)
  obtain ⟨w, hw⟩ := hM (χ ⟨x, hN hx⟩) (χ ⟨y, hN hy⟩) (h2pow hx) (h2pow hy) (hout hx hxo)
    (hout hy hyo)
  rw [← map_inv, ← map_mul] at hw
  exact hact _ w hw

theorem Z2Set.innerModOdd_iff_of_noInvolution (hs : Z2Set n R S t J u R₀ T₀ P)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    (hno : ¬ ∃ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1) {x : Y}
    (hx : x ∈ edgeCent (P : Subgroup Y) t u) :
    InnerModOdd (linkLayer R t) x ↔
      InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x := by
  obtain ⟨b, hbP, hbt⟩ := hs.exists_swap
  have hbu := hs.swap_u hbP hbt
  have hbA : b ∉ edgeCent (P : Subgroup Y) t u := fun h =>
    hs.t_ne_u ((conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp h.1.2)).symm.trans hbt)
  have hbb := hs.mul_self_mem_edgeCent hbP
  have hbbt : ¬ InnerModOdd (linkLayer R t) (b * b) := fun h =>
    hno (hs.exists_involution_of_inner_sq hall hbP hbA h)
  have key : ∀ x ∈ edgeCent (P : Subgroup Y) t u, InnerModOdd (linkLayer R t) x →
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x → False := by
    intro x hx hxt hxu
    obtain ⟨s, hsA, hs1, hs2⟩ := hs.exists_split_t hall hx hxt
    have hsi : s⁻¹ ∈ edgeCent (P : Subgroup Y) t u := Subgroup.inv_mem _ hsA
    have hx'A : s⁻¹ * x ∈ edgeCent (P : Subgroup Y) t u := Subgroup.mul_mem _ hsi hx
    have hx't : ActsLike (linkLayer R t) (s⁻¹ * x) 1 := by
      have h1 := actsLike_inv hs1 (hs.conjSub_Λt_of_mem (Subgroup.inv_mem _ hx))
        (hs.conjSub_Λt_of_mem hsi)
      have h2 := actsLike_mul h1 (actsLike_refl _ x) (hs.conjSub_Λt_of_mem hx)
        (hs.conjSub_Λt_of_mem hsi)
      rwa [inv_mul_cancel] at h2
    have hx'u : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
        (s⁻¹ * x) := by
      intro h
      apply hxu
      have h1 := innerModOdd_mul (innerModOdd_of_actsTriv hs2) h (hs.conjSub_Λu_of_mem hsA)
      rwa [mul_inv_cancel_left] at h1
    have hcP : b * (s⁻¹ * x) ∈ (P : Subgroup Y) := (P : Subgroup Y).mul_mem hbP hx'A.1.1
    have hcA : b * (s⁻¹ * x) ∉ edgeCent (P : Subgroup Y) t u := by
      intro h
      apply hbA
      have e : b = b * (s⁻¹ * x) * (s⁻¹ * x)⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hx'A)
    have hzA : b⁻¹ * (s⁻¹ * x) * b⁻¹⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
      hs.conj_mem_edgeCent ((P : Subgroup Y).inv_mem hbP) hx'A
    have hz_out : ¬ InnerModOdd (linkLayer R t) (b⁻¹ * (s⁻¹ * x) * b⁻¹⁻¹) := by
      rw [hs.innerModOdd_conj_swap hbP hbt,
        show b * (b⁻¹ * (s⁻¹ * x) * b⁻¹⁻¹) * b⁻¹ = s⁻¹ * x by group]
      exact hx'u
    have hzi_out : ¬ InnerModOdd (linkLayer R t) (b⁻¹ * (s⁻¹ * x) * b⁻¹⁻¹)⁻¹ := by
      intro h
      apply hz_out
      have h1 := innerModOdd_inv h (by rw [inv_inv]; exact hs.conjSub_Λt_of_mem hzA)
      rwa [inv_inv] at h1
    have h1 := hs.innerModOdd_mul_inv_of_outer hbb (Subgroup.inv_mem _ hzA) hbbt hzi_out
    rw [inv_inv] at h1
    have hcc : InnerModOdd (linkLayer R t) (b * (s⁻¹ * x) * (b * (s⁻¹ * x))) := by
      refine innerModOdd_of_actsLike h1 ?_
      have h2 := actsLike_mul (actsLike_refl _ (b * b * (b⁻¹ * (s⁻¹ * x) * b⁻¹⁻¹))) hx't
        (by rw [conjSub_one]) (hs.conjSub_Λt_of_mem (Subgroup.mul_mem _ hbb hzA))
      rwa [mul_one, show b * b * (b⁻¹ * (s⁻¹ * x) * b⁻¹⁻¹) * (s⁻¹ * x) =
        b * (s⁻¹ * x) * (b * (s⁻¹ * x)) by group] at h2
    exact hno (hs.exists_involution_of_inner_sq hall hcP hcA hcc)
  constructor
  · intro hxt
    by_contra hxu
    exact key x hx hxt hxu
  · intro hxu
    by_contra hxt
    have hbt' : b⁻¹ * t * b⁻¹⁻¹ = u := inv_conj_of_conj hbu
    have hyA : b⁻¹ * x * b⁻¹⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
      hs.conj_mem_edgeCent ((P : Subgroup Y).inv_mem hbP) hx
    refine key _ hyA ?_ ?_
    · rw [hs.innerModOdd_conj_swap hbP hbt, show b * (b⁻¹ * x * b⁻¹⁻¹) * b⁻¹ = x by group]
      exact hxu
    · rwa [← hs.innerModOdd_conj_swap ((P : Subgroup Y).inv_mem hbP) hbt']

theorem Z2Set.sq_outer_of_noInvolution (hs : Z2Set n R S t J u R₀ T₀ P)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    (hno : ¬ ∃ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1) {y : Y}
    (hyP : y ∈ (P : Subgroup Y)) (hyA : y ∉ edgeCent (P : Subgroup Y) t u) :
    ¬ InnerModOdd (linkLayer R t) (y * y) ∧
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (y * y) := by
  have hyt := hs.swap_of_not_mem hyP hyA
  have h1 : ¬ InnerModOdd (linkLayer R t) (y * y) := fun h =>
    hno (hs.exists_involution_of_inner_sq hall hyP hyA h)
  refine ⟨h1, fun h => h1 ?_⟩
  rw [hs.innerModOdd_conj_swap hyP hyt, show y * (y * y) * y⁻¹ = y * y by group]
  exact h

theorem Z2Set.pow_four_mul_eq (hs : Z2Set n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) {m : ℕ} (h1 : b ^ (4 * m) ≠ 1)
    (h2 : b ^ (8 * m) = 1) : b ^ (4 * m) = t * u := by
  have hbu := hs.swap_u hbP hbt
  have hbb := hs.mul_self_mem_edgeCent hbP
  have hx : b ^ (2 * m) ∈ edgeCent (P : Subgroup Y) t u := by
    rw [pow_mul, sq]
    exact Subgroup.pow_mem _ hbb m
  have h4 : (b ^ (2 * m)) ^ 4 = 1 := by
    rw [← pow_mul, show 2 * m * 4 = 8 * m by ring, h2]
  have hE := hs.sq_mem_E hx h4
  rw [← pow_mul, show 2 * m * 2 = 4 * m by ring] at hE
  have hcomm : b * b ^ (4 * m) = b ^ (4 * m) * b := (Commute.self_pow b (4 * m)).eq
  rcases mem_closure_pair_cases hs.t2 hs.u2 hs.tu_comm hE with h | h | h | h
  · exact absurd h h1
  · exfalso
    apply hs.t_ne_u
    rw [← hbt, ← h, hcomm, mul_inv_cancel_right]
  · exfalso
    apply hs.t_ne_u
    rw [← hbu, ← h, hcomm, mul_inv_cancel_right]
  · exact h

theorem Z2Set.innerModOdd_t_of_mem_omegaNbr (hs : Z2Set n R S t J u R₀ T₀ P) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hy : IsUniqueInvolution L y) : InnerModOdd (linkLayer R t) y := by
  have hyL : y ∈ coreAt t L := Subgroup.subset_closure
    ⟨⟨hy.mem, hyA.1.2⟩, Balance.isPGroup_zpowers_of_mul_self_eq_one hy.sq⟩
  refine ⟨y, coreAt_le_linkLayerAt hL hyL, fun z _ => ?_⟩
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem Z2Set.innerModOdd_u_of_mem_omegaNbr (hs : Z2Set n R S t J u R₀ T₀ P) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J)
    (hy : IsUniqueInvolution L y) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y := by
  have hyL : y ∈ coreAt u L := Subgroup.subset_closure
    ⟨⟨hy.mem, hyA.2⟩, Balance.isPGroup_zpowers_of_mul_self_eq_one hy.sq⟩
  refine ⟨y, coreAt_le_linkLayerAt hL hyL, fun z _ => ?_⟩
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem Z2Set.not_innerModOdd_conj (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1)
    (hyt : ¬ InnerModOdd (linkLayer R t) y)
    (hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y) {c : Y}
    (hc : c ∈ Subgroup.centralizer ({t * u} : Set Y))
    (hcy : c * y * c⁻¹ ∈ edgeCent (P : Subgroup Y) t u) :
    ¬ InnerModOdd (linkLayer R t) (c * y * c⁻¹) ∧
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) (c * y * c⁻¹) := by
  have hcl : ConjInvariant (CoreAssembly.conjClass (tightCore R)) :=
    hs.large.datum.hypOmegaGen.conjInvariant
  have htu := hs.tu_comm
  have hmem_a : ∀ {z : Y}, z * t = t * z → z * u = u * z →
      z ∈ Subgroup.centralizer ({t * u} : Set Y) := by
    intro z h1 h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc z * (t * u) = z * t * u := by group
      _ = t * (z * u) := by rw [h1]; group
      _ = t * u * z := by rw [h2]; group
  have hOa : oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) ≤
      Subgroup.centralizer ({t * u} : Set Y) := (oddCoreOf_le_self _).trans layerY_le_centralizer
  have hOn : ∀ d ∈ Subgroup.centralizer ({t * u} : Set Y),
      conjSub d (oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u))) =
        oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) := fun d hd => by
    rw [← Thompson.oddCoreOf_conjSub_eq, layerY_conjSub_eq hcl hd]
  have hOodd := oddCoreOf_odd_natCard (layerY (CoreAssembly.conjClass (tightCore R)) (t * u))
  have ha2 : t * u * (t * u) = 1 := by
    rw [show t * u * (t * u) = t * (u * t) * u by group, ← htu,
      show t * (t * u) * u = (t * t) * (u * u) by group, hs.t2, hs.u2, one_mul]
  have hat : t * u * t = t * (t * u) := by rw [mul_assoc, ← htu, ← mul_assoc]
  have hEa : Subgroup.closure ({t * u, t} : Set Y) ≤ Subgroup.centralizer ({t * u} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hat.symm
  have hEN : Subgroup.closure ({t * u, t} : Set Y) ≤ Subgroup.normalizer
      ((oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) : Subgroup Y) : Set Y) :=
    fun e he => mem_normalizer_iff_conjSub_eq.mpr (hOn e (hEa he))
  have hE2 : IsPGroup 2 ↥(Subgroup.closure ({t * u, t} : Set Y)) := by
    intro e
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
    rcases mem_closure_pair_cases ha2 hs.t2 hat e.2 with h | h | h | h <;> rw [h]
    · exact one_mul 1
    · exact ha2
    · exact hs.t2
    · rw [show t * u * t * (t * u * t) = t * (u * (t * t) * u) * t by group, hs.t2, mul_one,
        hs.u2, mul_one, hs.t2]
  have hEsyl : IsSylow2In (Subgroup.closure ({t * u, t} : Set Y))
      (Subgroup.closure ({t * u, t} : Set Y) ⊔
        oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u))) := by
    refine ⟨le_sup_left, hE2, fun V' hV'M hV'2 hEV' => le_antisymm (fun v hv => ?_) hEV'⟩
    have hvM : v ∈ ((Subgroup.closure ({t * u, t} : Set Y) ⊔
        oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) : Subgroup Y) : Set Y) :=
      hV'M hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hEN] at hvM
    obtain ⟨e, he, o, ho, rfl⟩ := Set.mem_mul.mp hvM
    have hoV : o ∈ V' := by
      have h1 := V'.mul_mem (V'.inv_mem (hEV' he)) hv
      rwa [inv_mul_cancel_left] at h1
    have ho1 : o = 1 := eq_one_of_isPGroup_of_mem_odd hOodd ho
      (hV'2.to_le (Subgroup.zpowers_le.mpr hoV))
    rw [ho1, mul_one]
    exact he
  have hcM := mem_normalizer_iff_conjSub_eq.mp (h1 hc)
  have hcEsyl := hEsyl.conj c
  rw [hcM] at hcEsyl
  obtain ⟨m, hm, hmE⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hEsyl hcEsyl
  have hmM : m ∈ ((oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) ⊔
      Subgroup.closure ({t * u, t} : Set Y) : Subgroup Y) : Set Y) := by
    rw [sup_comm]
    exact hm
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hEN] at hmM
  obtain ⟨o, ho, e, he, rfl⟩ := Set.mem_mul.mp hmM
  have hoE : conjSub o (Subgroup.closure ({t * u, t} : Set Y)) =
      conjSub c (Subgroup.closure ({t * u, t} : Set Y)) := by
    rw [← hmE, conjSub_mul, conjSub_eq_self_of_mem he]
  have hnE : conjSub (o⁻¹ * c) (Subgroup.closure ({t * u, t} : Set Y)) =
      Subgroup.closure ({t * u, t} : Set Y) := by
    rw [conjSub_mul, ← hoE, conjSub_inv_conjSub]
  have hna : o⁻¹ * c ∈ Subgroup.centralizer ({t * u} : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hOa ho)) hc
  have hnt : o⁻¹ * c * t * (o⁻¹ * c)⁻¹ ∈ Subgroup.closure ({t * u, t} : Set Y) := by
    rw [← hnE]
    exact conj_mem_conjSub (Subgroup.subset_closure (by simp)) _
  have hnu_of : o⁻¹ * c * t * (o⁻¹ * c)⁻¹ * (o⁻¹ * c * u * (o⁻¹ * c)⁻¹) = t * u := by
    rw [show o⁻¹ * c * t * (o⁻¹ * c)⁻¹ * (o⁻¹ * c * u * (o⁻¹ * c)⁻¹) =
      o⁻¹ * c * (t * u) * (o⁻¹ * c)⁻¹ by group]
    exact conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hna)
  have hperm : (o⁻¹ * c * t * (o⁻¹ * c)⁻¹ = t ∧ o⁻¹ * c * u * (o⁻¹ * c)⁻¹ = u) ∨
      (o⁻¹ * c * t * (o⁻¹ * c)⁻¹ = u ∧ o⁻¹ * c * u * (o⁻¹ * c)⁻¹ = t) := by
    rcases mem_closure_pair_cases ha2 hs.t2 hat hnt with h | h | h | h
    · exfalso
      apply hs.large.datum.isUniqueInvolution_core.ne_one
      have h2 := congrArg (fun z => (o⁻¹ * c)⁻¹ * z * (o⁻¹ * c)) h
      simpa [mul_assoc] using h2
    · exfalso
      apply hs.tu_not_conj (o⁻¹ * c)⁻¹
      rw [← h]
      group
    · refine Or.inl ⟨h, ?_⟩
      rw [h] at hnu_of
      exact mul_left_cancel hnu_of
    · refine Or.inr ⟨by rw [h, mul_assoc, ← htu, ← mul_assoc, hs.t2, one_mul], ?_⟩
      rw [h] at hnu_of
      have h3 : t * u * t * (o⁻¹ * c * u * (o⁻¹ * c)⁻¹) = t * u * t * t := by
        rw [hnu_of, mul_assoc (t * u) t t, hs.t2, mul_one]
      exact mul_left_cancel h3
  have hy't : ¬ InnerModOdd (linkLayer R t) (o⁻¹ * c * y * (o⁻¹ * c)⁻¹) ∧
      ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u)
        (o⁻¹ * c * y * (o⁻¹ * c)⁻¹) := by
    rcases hperm with ⟨h1t, h1u⟩ | ⟨h1t, h1u⟩
    · refine ⟨fun h => hyt ?_, fun h => hyu ?_⟩
      · rwa [innerModOdd_conj_iff y (o⁻¹ * c), hs.conjSub_Λt_fix h1t]
      · rwa [innerModOdd_conj_iff y (o⁻¹ * c), hs.conjSub_Λu_fix h1u]
    · refine ⟨fun h => hyu ?_, fun h => hyt ?_⟩
      · rwa [innerModOdd_conj_iff y (o⁻¹ * c), hs.conjSub_Λu_swap h1u]
      · rwa [innerModOdd_conj_iff y (o⁻¹ * c), hs.conjSub_Λt_swap h1t]
  have hyt' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.1.2
  have hyu' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.2
  have hcomm_y' : ∀ {z w : Y}, o⁻¹ * c * w * (o⁻¹ * c)⁻¹ = z → y * w = w * y →
      o⁻¹ * c * y * (o⁻¹ * c)⁻¹ * z = z * (o⁻¹ * c * y * (o⁻¹ * c)⁻¹) := by
    intro z w hw hyw
    rw [← hw, show o⁻¹ * c * y * (o⁻¹ * c)⁻¹ * (o⁻¹ * c * w * (o⁻¹ * c)⁻¹) =
      o⁻¹ * c * (y * w) * (o⁻¹ * c)⁻¹ by group, hyw]
    group
  have hy'tu : o⁻¹ * c * y * (o⁻¹ * c)⁻¹ * t = t * (o⁻¹ * c * y * (o⁻¹ * c)⁻¹) ∧
      o⁻¹ * c * y * (o⁻¹ * c)⁻¹ * u = u * (o⁻¹ * c * y * (o⁻¹ * c)⁻¹) := by
    rcases hperm with ⟨h1t, h1u⟩ | ⟨h1t, h1u⟩
    · exact ⟨hcomm_y' h1t hyt', hcomm_y' h1u hyu'⟩
    · exact ⟨hcomm_y' h1u hyu', hcomm_y' h1t hyt'⟩
  have hy'2 : o⁻¹ * c * y * (o⁻¹ * c)⁻¹ * (o⁻¹ * c * y * (o⁻¹ * c)⁻¹) = 1 := by
    rw [show o⁻¹ * c * y * (o⁻¹ * c)⁻¹ * (o⁻¹ * c * y * (o⁻¹ * c)⁻¹) =
      o⁻¹ * c * (y * y) * (o⁻¹ * c)⁻¹ by group, hy2]
    group
  have hy'a := hmem_a hy'tu.1 hy'tu.2
  have hk : (o⁻¹ * c * y * (o⁻¹ * c)⁻¹)⁻¹ * (c * y * c⁻¹) ∈
      oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) (t * u)) := by
    rw [show (o⁻¹ * c * y * (o⁻¹ * c)⁻¹)⁻¹ * (c * y * c⁻¹) =
      (o⁻¹ * c * y * (o⁻¹ * c)⁻¹)⁻¹ * o * (o⁻¹ * c * y * (o⁻¹ * c)⁻¹)⁻¹⁻¹ * o⁻¹ by group]
    refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ ho)
    have h2 := conj_mem_conjSub ho (o⁻¹ * c * y * (o⁻¹ * c)⁻¹)⁻¹
    rwa [hOn _ (Subgroup.inv_mem _ hy'a)] at h2
  have hkodd : Odd (orderOf ((o⁻¹ * c * y * (o⁻¹ * c)⁻¹)⁻¹ * (c * y * c⁻¹))) :=
    hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hk)
  have e : c * y * c⁻¹ = o⁻¹ * c * y * (o⁻¹ * c)⁻¹ *
      ((o⁻¹ * c * y * (o⁻¹ * c)⁻¹)⁻¹ * (c * y * c⁻¹)) := by group
  have hy'A_t : o⁻¹ * c * y * (o⁻¹ * c)⁻¹ ∈
      Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr (hs.conjSub_Λt_fix (conj_eq_of_comm hy'tu.1))
  have hy'A_u : o⁻¹ * c * y * (o⁻¹ * c)⁻¹ ∈ Subgroup.normalizer
      ((linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u : Subgroup Y) : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr (hs.conjSub_Λu_fix (conj_eq_of_comm hy'tu.2))
  have hcy_t : c * y * c⁻¹ ∈ Subgroup.normalizer ((linkLayer R t : Subgroup Y) : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr (hs.conjSub_Λt_of_mem hcy)
  have hcy_u : c * y * c⁻¹ ∈ Subgroup.normalizer
      ((linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u : Subgroup Y) : Set Y) :=
    mem_normalizer_iff_conjSub_eq.mpr (hs.conjSub_Λu_of_mem hcy)
  refine ⟨fun h => hy't.1 ?_, fun h => hy't.2 ?_⟩
  · refine innerModOdd_of_mul_odd hy'A_t (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy'A_t) hcy_t)
      hy'2 hkodd ?_
    rwa [← e]
  · refine innerModOdd_of_mul_odd hy'A_u (Subgroup.mul_mem _ (Subgroup.inv_mem _ hy'A_u) hcy_u)
      hy'2 hkodd ?_
    rwa [← e]

private theorem Z2Set.innerModOdd_t_t (hs : Z2Set n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayer R t) t := by
  refine innerModOdd_of_actsTriv fun z hz => ?_
  have hzt : t * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
  rw [show t * z * t⁻¹ * z⁻¹ = 1 by rw [hzt]; group]
  exact Subgroup.one_mem _

private theorem Z2Set.innerModOdd_t_u (hs : Z2Set n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayer R t) u := by
  refine ⟨u, coreAt_le_linkLayerAt hs.hJ (Subgroup.subset_closure
    ⟨⟨hs.hu.mem, Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm.symm⟩,
      Balance.isPGroup_zpowers_of_mul_self_eq_one hs.u2⟩), actsLike_refl _ u⟩

private theorem Z2Set.innerModOdd_u_u (hs : Z2Set n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) u := by
  refine innerModOdd_of_actsTriv fun z hz => ?_
  have hzu : u * z = z * u :=
    (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
  rw [show u * z * u⁻¹ * z⁻¹ = 1 by rw [hzu]; group]
  exact Subgroup.one_mem _

private theorem Z2Set.innerModOdd_u_t (hs : Z2Set n R S t J u R₀ T₀ P) :
    InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) t := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hKJ := Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hs.large.datum.hypOmegaGen hK hs.hJ.1 hs.hJ
  refine ⟨t, coreAt_le_linkLayerAt hKJ (Subgroup.subset_closure
    ⟨⟨hs.large.datum.isUniqueInvolution_core.mem,
      Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm⟩,
      Balance.isPGroup_zpowers_of_mul_self_eq_one hs.t2⟩), actsLike_refl _ t⟩

private theorem Z2Set.isSylow2In_edgeCent_t (hs : Z2Set n R S t J u R₀ T₀ P) :
    IsSylow2In (edgeCent (P : Subgroup Y) t u) (Subgroup.centralizer ({t} : Set Y)) := by
  classical
  have hΩ := hs.large.datum.hypOmegaGen
  have ht := hs.large.datum.isUniqueInvolution_core
  have hTF := TightLargeHypR.typeRFam hs.large
  have hA2 : IsPGroup 2 ↥(edgeCent (P : Subgroup Y) t u) :=
    P.isPGroup'.to_le (inf_le_left.trans inf_le_left)
  have hT₀A : T₀ ≤ edgeCent (P : Subgroup Y) t u := fun x hx =>
    ⟨⟨hs.hT₀P hx, S1916.normalizer_le_centralizer_of_isUniqueInvolution ht (hs.hT₀N hx)⟩,
      hTF.le_centralizer hs.hJ.1 hs.hu (hs.hT₀.1 hx)⟩
  have hfixA : ∀ J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      (∀ a ∈ edgeCent (P : Subgroup Y) t u, conjSub a J' = J') → J' = J := by
    intro J' hJ' hfix
    by_contra hne
    have hJJ' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J' :=
      ⟨hs.hJ.1, fun h => hne h.symm, T₀, mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀, hs.hT₀.1,
        fun x hx => mem_normalizer_iff_conjSub_eq.mpr (hfix x (hT₀A hx))⟩
    exact hs.not_mem_omegaNbr_J hJ' (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hJ'.1 hs.hJ.1 hJJ')
  let act : ∀ Q : Subgroup Y, Q ≤ Subgroup.centralizer ({t} : Set Y) →
      MulAction ↥Q ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :=
    fun Q hQ =>
      { smul := fun q J' => ⟨conjSub (q : Y) J'.1, conjSub_mem_omegaNbr_core hs.large J'.2 (hQ q.2)⟩
        one_smul := fun J' => Subtype.ext (conjSub_one _)
        mul_smul := fun q₁ q₂ J' => Subtype.ext (conjSub_mul _ _ _) }
  have hAt : edgeCent (P : Subgroup Y) t u ≤ Subgroup.centralizer ({t} : Set Y) :=
    inf_le_left.trans inf_le_right
  refine ⟨hAt, hA2, fun V hVt hV2 hAV => ?_⟩
  have hVJ : ∀ v ∈ V, conjSub v J = J := by
    letI := act _ hAt
    letI := act V hVt
    have hFA : MulAction.fixedPoints ↥(edgeCent (P : Subgroup Y) t u)
        ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) = {⟨J, hs.hJ⟩} := by
      ext J'
      simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
      constructor
      · intro h
        exact Subtype.ext (hfixA J'.1 J'.2 fun a ha => congrArg Subtype.val (h ⟨a, ha⟩))
      · rintro rfl a
        exact Subtype.ext (hs.conjSub_J_fix (conj_eq_of_comm
          (Subgroup.mem_centralizer_singleton_iff.mp a.2.2)))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h1 := hA2.card_modEq_card_fixedPoints
      ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    have h2 := hV2.card_modEq_card_fixedPoints
      ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    have hc1 : Nat.card ↥({⟨J, hs.hJ⟩} : Set
        ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))) = 1 := Nat.card_unique
    rw [hFA, hc1] at h1
    have hne : (MulAction.fixedPoints ↥V
        ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      have hc0 : Nat.card ↥(∅ : Set
          ↥(omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))) = 0 := by simp
      rw [h, hc0] at h2
      have h3 := h1.symm.trans h2
      simp [Nat.ModEq] at h3
    obtain ⟨J', hJ'⟩ := hne
    have hJ'J : J'.1 = J :=
      hfixA J'.1 J'.2 fun a ha => congrArg Subtype.val (hJ' ⟨a, hAV ha⟩)
    intro v hv
    have h4 := congrArg Subtype.val (hJ' ⟨v, hv⟩)
    rw [← hJ'J]
    exact h4
  have hVu : V ≤ Subgroup.centralizer ({u} : Set Y) := fun v hv =>
    S1916.normalizer_le_centralizer_of_isUniqueInvolution hs.hu
      (mem_normalizer_iff_conjSub_eq.mpr (hVJ v hv))
  obtain ⟨c, -, hcV⟩ := hs.exists_conj_le_edgeCent hV2 hVt hVu
  have hcard : Nat.card ↥V ≤ Nat.card ↥(edgeCent (P : Subgroup Y) t u) := by
    rw [← natCard_conjSub' c V]
    exact Subgroup.card_le_of_le hcV
  exact (Subgroup.eq_of_le_of_card_ge hAV hcard).symm

private theorem Z2Set.isSylow2In_edgeCent_u (hs : Z2Set n R S t J u R₀ T₀ P) :
    IsSylow2In (edgeCent (P : Subgroup Y) t u) (Subgroup.centralizer ({u} : Set Y)) := by
  obtain ⟨b, hbP, hbt⟩ := hs.exists_swap
  have hbA : conjSub b (edgeCent (P : Subgroup Y) t u) = edgeCent (P : Subgroup Y) t u := by
    apply le_antisymm
    · intro x hx
      rw [mem_conjSub_iff] at hx
      have h := hs.conj_mem_edgeCent hbP hx
      rwa [show b * (b⁻¹ * x * b) * b⁻¹ = x by group] at h
    · intro x hx
      rw [mem_conjSub_iff]
      have h := hs.conj_mem_edgeCent ((P : Subgroup Y).inv_mem hbP) hx
      rwa [inv_inv] at h
  have h := hs.isSylow2In_edgeCent_t.conj b
  rwa [Balance.conjSub_centralizer_singleton, hbt, hbA] at h

private theorem Z2Set.false_of_big_t (hs : Z2Set n R S t J u R₀ T₀ P) {y : Y}
    (hyt : ¬ InnerModOdd (linkLayer R t) y) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    {V : Subgroup Y} (hV2 : IsPGroup 2 ↥V) (hVL : V ≤ L)
    (hVt : V ≤ Subgroup.centralizer ({t} : Set Y)) (hV4 : 2 < Nat.card ↥V) : False := by
  obtain ⟨V', hV', hVV'⟩ := IsSylow2In.exists_ge hV2 hVt
  obtain ⟨d, hd, hdA⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hs.isSylow2In_edgeCent_t hV'
  have hVA : conjSub d⁻¹ V ≤ edgeCent (P : Subgroup Y) t u := by
    have h := conjSub_mono (n := d⁻¹) hVV'
    rwa [← hdA, conjSub_inv_conjSub] at h
  have hcard : 2 < Nat.card ↥(conjSub d⁻¹ L ⊓ (P : Subgroup Y)) := by
    refine lt_of_lt_of_le (by rwa [natCard_conjSub']) (Subgroup.card_le_of_le
      (le_inf (conjSub_mono hVL) (hVA.trans (inf_le_left.trans inf_le_left))))
  have hdt : d⁻¹ * t * d⁻¹⁻¹ = t :=
    conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.centralizer ({t} : Set Y)).inv_mem hd))
  apply hyt
  rw [innerModOdd_conj_iff y d⁻¹, hs.conjSub_Λt_fix hdt]
  rcases hs.eq_of_two_lt_card (hs.mem_cls_conj hL d⁻¹) (hyL.conj d⁻¹) hcard with h | h
  · rw [h]
    exact hs.innerModOdd_t_t
  · rw [h]
    exact hs.innerModOdd_t_u

private theorem Z2Set.false_of_big_u (hs : Z2Set n R S t J u R₀ T₀ P) {y : Y}
    (hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    {V : Subgroup Y} (hV2 : IsPGroup 2 ↥V) (hVL : V ≤ L)
    (hVu : V ≤ Subgroup.centralizer ({u} : Set Y)) (hV4 : 2 < Nat.card ↥V) : False := by
  obtain ⟨V', hV', hVV'⟩ := IsSylow2In.exists_ge hV2 hVu
  obtain ⟨d, hd, hdA⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hs.isSylow2In_edgeCent_u hV'
  have hVA : conjSub d⁻¹ V ≤ edgeCent (P : Subgroup Y) t u := by
    have h := conjSub_mono (n := d⁻¹) hVV'
    rwa [← hdA, conjSub_inv_conjSub] at h
  have hcard : 2 < Nat.card ↥(conjSub d⁻¹ L ⊓ (P : Subgroup Y)) := by
    refine lt_of_lt_of_le (by rwa [natCard_conjSub']) (Subgroup.card_le_of_le
      (le_inf (conjSub_mono hVL) (hVA.trans (inf_le_left.trans inf_le_left))))
  have hdu : d⁻¹ * u * d⁻¹⁻¹ = u :=
    conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.centralizer ({u} : Set Y)).inv_mem hd))
  apply hyu
  rw [innerModOdd_conj_iff y d⁻¹, hs.conjSub_Λu_fix hdu]
  rcases hs.eq_of_two_lt_card (hs.mem_cls_conj hL d⁻¹) (hyL.conj d⁻¹) hcard with h | h
  · rw [h]
    exact hs.innerModOdd_u_t
  · rw [h]
    exact hs.innerModOdd_u_u

private theorem Z2Set.two_lt_card_of_mem_USet (hs : Z2Set n R S t J u R₀ T₀ P) {V : Subgroup Y}
    (hV : V ∈ USet (CoreAssembly.conjClass (tightCore R))) : 2 < Nat.card ↥V := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hs.large.datum.hypOmegaGen hV
  omega

theorem Z2Set.false_of_type33 (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1)
    (hyt : ¬ InnerModOdd (linkLayer R t) y)
    (hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    {Vt Vu : Subgroup Y} (hVt : IsSylow2In Vt (L ⊓ Subgroup.centralizer ({t} : Set Y)))
    (hyVt : y ∈ Vt) (hVu : IsSylow2In Vu (L ⊓ Subgroup.centralizer ({u} : Set Y)))
    (hyVu : y ∈ Vu) (h3t : Vt ∈ USet (CoreAssembly.conjClass (tightCore R)))
    (h3u : Vu ∈ USet (CoreAssembly.conjClass (tightCore R))) : False :=
  hs.false_of_big_t hyt hL hyL hVt.2.1 (hVt.1.trans inf_le_left) (hVt.1.trans inf_le_right)
    (hs.two_lt_card_of_mem_USet h3t)

theorem Z2Set.false_of_type32 (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1)
    (hyt : ¬ InnerModOdd (linkLayer R t) y)
    (hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    {Vt Vu : Subgroup Y} (hVt : IsSylow2In Vt (L ⊓ Subgroup.centralizer ({t} : Set Y)))
    (hyVt : y ∈ Vt) (hVu : IsSylow2In Vu (L ⊓ Subgroup.centralizer ({u} : Set Y)))
    (hyVu : y ∈ Vu) (h3t : Vt ∈ USet (CoreAssembly.conjClass (tightCore R)))
    (h2u : Vu = Subgroup.zpowers y) : False :=
  hs.false_of_big_t hyt hL hyL hVt.2.1 (hVt.1.trans inf_le_left) (hVt.1.trans inf_le_right)
    (hs.two_lt_card_of_mem_USet h3t)

theorem Z2Set.false_of_type23 (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1)
    (hyt : ¬ InnerModOdd (linkLayer R t) y)
    (hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    {Vt Vu : Subgroup Y} (hVt : IsSylow2In Vt (L ⊓ Subgroup.centralizer ({t} : Set Y)))
    (hyVt : y ∈ Vt) (hVu : IsSylow2In Vu (L ⊓ Subgroup.centralizer ({u} : Set Y)))
    (hyVu : y ∈ Vu) (h2t : Vt = Subgroup.zpowers y)
    (h3u : Vu ∈ USet (CoreAssembly.conjClass (tightCore R))) : False :=
  hs.false_of_big_u hyu hL hyL hVu.2.1 (hVu.1.trans inf_le_left) (hVu.1.trans inf_le_right)
    (hs.two_lt_card_of_mem_USet h3u)

theorem Z2Set.false_of_type22 (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1)
    (hyt : ¬ InnerModOdd (linkLayer R t) y)
    (hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y)
    {L : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    {Vt Vu : Subgroup Y} (hVt : IsSylow2In Vt (L ⊓ Subgroup.centralizer ({t} : Set Y)))
    (hyVt : y ∈ Vt) (hVu : IsSylow2In Vu (L ⊓ Subgroup.centralizer ({u} : Set Y)))
    (hyVu : y ∈ Vu) (h2t : Vt = Subgroup.zpowers y) (h2u : Vu = Subgroup.zpowers y) : False := by
  have hTF := TightLargeHypR.typeRFam hs.large
  have hyt' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.1.2
  have hyu' : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyA.2
  have hE2 : IsPGroup 2 ↥(Subgroup.closure ({t, u} : Set Y)) := by
    intro e
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, sq, Subgroup.coe_mul, Subgroup.coe_one]
    rcases mem_closure_pair_cases hs.t2 hs.u2 hs.tu_comm e.2 with h | h | h | h <;> rw [h]
    · exact one_mul 1
    · exact hs.t2
    · exact hs.u2
    · rw [show t * u * (t * u) = t * (u * t) * u by group, ← hs.tu_comm,
        show t * (t * u) * u = (t * t) * (u * u) by group, hs.t2, hs.u2, one_mul]
  have hEy : Subgroup.closure ({t, u} : Set Y) ≤ Subgroup.centralizer ({y} : Set Y) := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyt'.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hyu'.symm
  obtain ⟨X, hX, hEX⟩ := IsSylow2In.exists_ge hE2 hEy
  have hRy := Asc77.isSylow2In_inf_of_le_normalizer hX (hTF.le_centralizer hL hyL)
    (hTF.tight L hL y hyL)
  have hN : ∀ {z : Y}, z ∈ Subgroup.closure ({t, u} : Set Y) →
      z ∈ Subgroup.normalizer ((X ⊓ L : Subgroup Y) : Set Y) := by
    intro z hz
    have hzX : z ∈ X := hEX hz
    have hzL : z ∈ Subgroup.normalizer (L : Set Y) := hTF.tight L hL y hyL (hEy hz)
    rw [mem_normalizer_iff_conjSub_eq] at hzL ⊢
    rw [conjSub, Subgroup.map_inf_eq _ _ _ (MulAut.conj z).injective]
    exact congrArg₂ (· ⊓ ·) (mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hzX)) hzL
  have htE : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have huE : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  obtain ⟨e⟩ := hTF.quat L hL _ hRy
  have houter : ∀ {z : Y} {V : Subgroup Y},
      IsSylow2In V (L ⊓ Subgroup.centralizer ({z} : Set Y)) → V = Subgroup.zpowers y →
        LinkDisc.B2b.Outer (X ⊓ L) z := by
    intro z V hV hVy w hw hwz
    have hw2 : IsPGroup 2 ↥(Subgroup.zpowers w) :=
      hRy.2.1.to_le (Subgroup.zpowers_le.mpr hw)
    obtain ⟨V', hV', hwV'⟩ := IsSylow2In.exists_ge hw2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr
        ⟨hw.2, Subgroup.mem_centralizer_singleton_iff.mpr hwz⟩))
    obtain ⟨x, -, hxV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hV hV'
    have hcard : Nat.card ↥V' = 2 := by
      rw [← hxV, natCard_conjSub', hVy, Nat.card_zpowers,
        orderOf_eq_prime (by rw [sq]; exact hyL.sq) hyL.ne_one]
    have h1 : orderOf w ∣ 2 := by
      rw [← hcard, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le hwV'
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hnot := LinkDisc.B2b.quatAutFacts_three.not_outer_triple e (hN htE) (hN huE) hs.tu_comm
    hs.t2 hs.u2
  have htu : ¬ LinkDisc.B2b.Outer (X ⊓ L) (t * u) := fun h =>
    hnot ⟨houter hVt h2t, houter hVu h2u, h⟩
  simp only [LinkDisc.B2b.Outer, not_forall] at htu
  obtain ⟨w, hw, hwa, hww⟩ := htu
  have hw2 : IsPGroup 2 ↥(Subgroup.zpowers w) := hRy.2.1.to_le (Subgroup.zpowers_le.mpr hw)
  obtain ⟨c, hc, hcw⟩ := hs.exists_conj_le hw2
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hwa))
  have hw4 : 2 < orderOf w := by
    by_contra hle
    push Not at hle
    have hpos := orderOf_pos w
    interval_cases h : orderOf w
    · exact hww (by rw [orderOf_eq_one_iff.mp h, one_mul])
    · exact hww (by rw [← sq, ← h, pow_orderOf_eq_one])
  have hcard : 2 < Nat.card ↥(conjSub c L ⊓ (P : Subgroup Y)) := by
    refine lt_of_lt_of_le (by rwa [natCard_conjSub', Nat.card_zpowers]) (Subgroup.card_le_of_le
      (le_inf (conjSub_mono (Subgroup.zpowers_le.mpr hw.2)) hcw))
  rcases hs.eq_of_two_lt_card (hs.mem_cls_conj hL c) (hyL.conj c) hcard with h | h
  · have h3 := (hs.not_innerModOdd_conj h1 hyA hy2 hyt hyu hc
      (by rw [h]; exact ⟨⟨hs.t_mem_P, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm⟩)).1
    rw [h] at h3
    exact h3 hs.innerModOdd_t_t
  · have h3 := (hs.not_innerModOdd_conj h1 hyA hy2 hyt hyu hc
      (by rw [h]; exact ⟨⟨hs.u_mem_P, Subgroup.mem_centralizer_singleton_iff.mpr hs.tu_comm.symm⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)).1
    rw [h] at h3
    exact h3 hs.innerModOdd_t_u

theorem Z2Set.pair_types (hs : Z2Set n R S t J u R₀ T₀ P) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (hyL : IsUniqueInvolution L y)
    (hyt : y ≠ t) (hyu : y ≠ u) :
    ∃ Vt Vu : Subgroup Y, IsSylow2In Vt (L ⊓ Subgroup.centralizer ({t} : Set Y)) ∧ y ∈ Vt ∧
      IsSylow2In Vu (L ⊓ Subgroup.centralizer ({u} : Set Y)) ∧ y ∈ Vu ∧
      (Vt = Subgroup.zpowers y ∨ Vt ∈ USet (CoreAssembly.conjClass (tightCore R)) ∨
        L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) ∧
      (Vu = Subgroup.zpowers y ∨ Vu ∈ USet (CoreAssembly.conjClass (tightCore R)) ∨
        L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J) := by
  have hΩ := hs.large.datum.hypOmegaGen
  have hTF := TightLargeHypR.typeRFam hs.large
  have ht := hs.large.datum.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  have hy2 : IsPGroup 2 ↥(Subgroup.zpowers y) :=
    Balance.isPGroup_zpowers_of_mul_self_eq_one hyL.sq
  have key : ∀ {M : Subgroup Y} {z : Y}, M ∈ CoreAssembly.conjClass (tightCore R) →
      IsUniqueInvolution M z → y ≠ z → y ∈ Subgroup.centralizer ({z} : Set Y) →
      ∃ V : Subgroup Y, IsSylow2In V (L ⊓ Subgroup.centralizer ({z} : Set Y)) ∧ y ∈ V ∧
        (V = Subgroup.zpowers y ∨ V ∈ USet (CoreAssembly.conjClass (tightCore R)) ∨
          L ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M) := by
    intro M z hM hz hyz hyc
    have hNz : Subgroup.centralizer ({z} : Set Y) ≤ Subgroup.normalizer (M : Set Y) :=
      hTF.tight M hM z hz
    have hLtw : L ∉ twinSet (CoreAssembly.conjClass (tightCore R)) M := by
      rintro ⟨-, z', hz'M, hz'L⟩
      exact hyz ((hyL.eq hz'L).trans (hz.eq hz'M).symm)
    obtain ⟨V, hV, hyV⟩ := IsSylow2In.exists_ge hy2
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hyL.mem, hyc⟩))
    have hyV' : y ∈ V := hyV (Subgroup.mem_zpowers y)
    refine ⟨V, hV, hyV', ?_⟩
    rcases Sec6Gen.l6_2Gen Y _ hΩ M hM z hz L hL hLtw y hyL V hV hyV' with
      ⟨-, hne⟩ | ⟨hV1, -⟩ | ⟨hVU, -⟩ | ⟨hVR, -⟩
    · exact absurd (mem_normalizer_iff_conjSub_eq.mp (hNz hyc)) hne
    · exact Or.inl hV1
    · exact Or.inr (Or.inl hVU)
    · refine Or.inr (Or.inr ⟨hL, (fun hLM => hyz ?_), V, hVR, hV.1.trans inf_le_left,
        (hV.1.trans inf_le_right).trans hNz⟩)
      rw [hLM] at hyL
      exact hyL.eq hz
  obtain ⟨Vt, hVt, hyVt, ht'⟩ := key hK ht hyt hyA.1.2
  obtain ⟨Vu, hVu, hyVu, hu'⟩ := key hs.hJ.1 hs.hu hyu hyA.2
  exact ⟨Vt, Vu, hVt, hyVt, hVu, hyVu, ht', hu'⟩

theorem Z2Set.not_conj_t_of_outer (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u) {y : Y}
    (hyA : y ∈ edgeCent (P : Subgroup Y) t u) (hy2 : y * y = 1)
    (hyt : ¬ InnerModOdd (linkLayer R t) y)
    (hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y) (g : Y) :
    g * y * g⁻¹ ≠ t := by
  intro hg
  have hyg : y = g⁻¹ * t * g := by rw [← hg]; group
  have hL : conjSub g⁻¹ (tightCore R) ∈ CoreAssembly.conjClass (tightCore R) := ⟨g⁻¹, rfl⟩
  have hyL : IsUniqueInvolution (conjSub g⁻¹ (tightCore R)) y := by
    have h2 := hs.large.datum.isUniqueInvolution_core.conj g⁻¹
    rwa [inv_inv, ← hyg] at h2
  have hne_t : y ≠ t := by
    intro he
    apply hyt
    rw [he]
    refine ⟨1, Subgroup.one_mem _, fun z hz => ?_⟩
    have hzt : t * z = z * t :=
      (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
    rw [show t * z * t⁻¹ * (1 * z * 1⁻¹)⁻¹ = 1 by rw [hzt]; group]
    exact Subgroup.one_mem _
  have hne_u : y ≠ u := by
    intro he
    apply hyu
    rw [he]
    refine ⟨1, Subgroup.one_mem _, fun z hz => ?_⟩
    have hzu : u * z = z * u :=
      (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer hz)).symm
    rw [show u * z * u⁻¹ * (1 * z * 1⁻¹)⁻¹ = 1 by rw [hzu]; group]
    exact Subgroup.one_mem _
  obtain ⟨Vt, Vu, hVt, hyVt, hVu, hyVu, ht', hu'⟩ := hs.pair_types hyA hL hyL hne_t hne_u
  rcases ht' with h2t | h3t | h4t
  · rcases hu' with h2u | h3u | h4u
    · exact hs.false_of_type22 h1 hyA hy2 hyt hyu hL hyL hVt hyVt hVu hyVu h2t h2u
    · exact hs.false_of_type23 h1 hyA hy2 hyt hyu hL hyL hVt hyVt hVu hyVu h2t h3u
    · exact hyu (hs.innerModOdd_u_of_mem_omegaNbr hyA h4u hyL)
  · rcases hu' with h2u | h3u | h4u
    · exact hs.false_of_type32 h1 hyA hy2 hyt hyu hL hyL hVt hyVt hVu hyVu h3t h2u
    · exact hs.false_of_type33 h1 hyA hy2 hyt hyu hL hyL hVt hyVt hVu hyVu h3t h3u
    · exact hyu (hs.innerModOdd_u_of_mem_omegaNbr hyA h4u hyL)
  · exact hyt (hs.innerModOdd_t_of_mem_omegaNbr hyA h4t hyL)

theorem Z2Set.not_conj_tu_of_outer (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    (hno : ¬ ∃ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1) {x : Y}
    (hxA : x ∈ edgeCent (P : Subgroup Y) t u) (hx2 : x * x = 1)
    (hxt : ¬ InnerModOdd (linkLayer R t) x)
    (hxu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) x) (g : Y) :
    g * x * g⁻¹ ≠ t * u := by
  intro hg
  have hxt' : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxA.1.2
  have hxu' : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxA.2
  obtain ⟨m, hm⟩ := hs.exists_conj_u
  have hQ2 : IsPGroup 2 ↥(conjSub g ((P : Subgroup Y) ⊓ Subgroup.centralizer ({x} : Set Y))) :=
    (P.isPGroup'.to_le inf_le_left).map _
  have hQa : conjSub g ((P : Subgroup Y) ⊓ Subgroup.centralizer ({x} : Set Y)) ≤
      Subgroup.centralizer ({t * u} : Set Y) := by
    intro q hq
    rw [mem_conjSub_iff] at hq
    have h1 : g⁻¹ * q * g * x = x * (g⁻¹ * q * g) :=
      Subgroup.mem_centralizer_singleton_iff.mp hq.2
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have h2 : g * (g⁻¹ * q * g * x) * g⁻¹ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [h1]
    rw [show g * (g⁻¹ * q * g * x) * g⁻¹ = q * (g * x * g⁻¹) by group,
      show g * (x * (g⁻¹ * q * g)) * g⁻¹ = g * x * g⁻¹ * q by group] at h2
    exact h2
  obtain ⟨c, hc, hcQ⟩ := hs.exists_conj_le hQ2 hQa
  obtain ⟨k, hk⟩ : ∃ k : Y, k = c * g := ⟨_, rfl⟩
  have hkx : k * x * k⁻¹ = t * u := by
    rw [hk, show c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ by group, hg,
      conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hc)]
  have hkP : ∀ q ∈ (P : Subgroup Y), q * x = x * q → k * q * k⁻¹ ∈ (P : Subgroup Y) := by
    intro q hq hqx
    apply hcQ
    rw [hk, show c * g * q * (c * g)⁻¹ = c * (g * q * g⁻¹) * c⁻¹ by group]
    have hq' : q ∈ (P : Subgroup Y) ⊓ Subgroup.centralizer ({x} : Set Y) :=
      ⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr hqx⟩
    exact conj_mem_conjSub (conj_mem_conjSub hq' g) c
  have ht₁ : k * t * k⁻¹ ∈ edgeCent (P : Subgroup Y) t u := by
    have h1 := hs.hweak_t h1 (g := k⁻¹) (by rw [inv_inv]; exact hkP t hs.t_mem_P hxt'.symm)
    rwa [inv_inv] at h1
  have hu₁ : k * u * k⁻¹ ∈ edgeCent (P : Subgroup Y) t u := by
    have e : k * u * k⁻¹ = (k * m)⁻¹⁻¹ * t * (k * m)⁻¹ := by rw [← hm]; group
    rw [e]
    refine hs.hweak_t h1 ?_
    rw [← e]
    exact hkP u hs.u_mem_P hxu'.symm
  set Q' := conjSub k⁻¹ ((P : Subgroup Y) ⊓ Subgroup.centralizer ({k * t * k⁻¹} : Set Y) ⊓
    Subgroup.centralizer ({k * u * k⁻¹} : Set Y)) with hQ'
  have hQ'2 : IsPGroup 2 ↥Q' := (P.isPGroup'.to_le (inf_le_left.trans inf_le_left)).map _
  have hcomm_conj : ∀ {q a : Y}, k * q * k⁻¹ * (k * a * k⁻¹) = k * a * k⁻¹ * (k * q * k⁻¹) →
      q * a = a * q := by
    intro q a h
    have h2 : k⁻¹ * (k * q * k⁻¹ * (k * a * k⁻¹)) * k = k⁻¹ * (k * a * k⁻¹ * (k * q * k⁻¹)) * k :=
      by rw [h]
    rwa [show k⁻¹ * (k * q * k⁻¹ * (k * a * k⁻¹)) * k = q * a by group,
      show k⁻¹ * (k * a * k⁻¹ * (k * q * k⁻¹)) * k = a * q by group] at h2
  have hQ't : Q' ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro q hq
    rw [hQ', mem_conjSub_iff, inv_inv] at hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm_conj (Subgroup.mem_centralizer_singleton_iff.mp hq.1.2)
  have hQ'u : Q' ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro q hq
    rw [hQ', mem_conjSub_iff, inv_inv] at hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcomm_conj (Subgroup.mem_centralizer_singleton_iff.mp hq.2)
  have hmemQ' : ∀ q ∈ (P : Subgroup Y), q * (k * t * k⁻¹) = k * t * k⁻¹ * q →
      q * (k * u * k⁻¹) = k * u * k⁻¹ * q → k⁻¹ * q * k ∈ Q' := by
    intro q hq h1 h2
    rw [hQ', mem_conjSub_iff, inv_inv, show k * (k⁻¹ * q * k) * k⁻¹ = q by group]
    exact ⟨⟨hq, Subgroup.mem_centralizer_singleton_iff.mpr h1⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr h2⟩
  have htQ' : k⁻¹ * t * k ∈ Q' := hmemQ' t hs.t_mem_P
    (Subgroup.mem_centralizer_singleton_iff.mp ht₁.1.2).symm
    (Subgroup.mem_centralizer_singleton_iff.mp hu₁.1.2).symm
  have huQ' : k⁻¹ * u * k ∈ Q' := hmemQ' u hs.u_mem_P
    (Subgroup.mem_centralizer_singleton_iff.mp ht₁.2).symm
    (Subgroup.mem_centralizer_singleton_iff.mp hu₁.2).symm
  obtain ⟨d, hd, hdQ⟩ := hs.exists_conj_le_edgeCent hQ'2 hQ't hQ'u
  have ht'' : d * (k⁻¹ * t * k) * d⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
    hdQ (conj_mem_conjSub htQ' d)
  have hu'' : d * (k⁻¹ * u * k) * d⁻¹ ∈ edgeCent (P : Subgroup Y) t u :=
    hdQ (conj_mem_conjSub huQ' d)
  have hinner : ∀ y ∈ edgeCent (P : Subgroup Y) t u, ∀ h : Y, y = h * t * h⁻¹ →
      InnerModOdd (linkLayer R t) y := by
    intro y hy h hyh
    by_contra hyt
    have hyu : ¬ InnerModOdd (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) y :=
      fun h' => hyt ((hs.innerModOdd_iff_of_noInvolution hall hno hy).mpr h')
    have hy2 : y * y = 1 := by
      rw [hyh, show h * t * h⁻¹ * (h * t * h⁻¹) = h * (t * t) * h⁻¹ by group, hs.t2]
      group
    exact hs.not_conj_t_of_outer h1 hy hy2 hyt hyu h⁻¹ (by rw [hyh]; group)
  have hi1 := hinner _ ht'' (d * k⁻¹) (by group)
  have hi2 := hinner _ hu'' (d * k⁻¹ * m) (by rw [← hm]; group)
  have hdx : InnerModOdd (linkLayer R t) (d * x * d⁻¹) := by
    have h3 := innerModOdd_mul hi1 hi2 (hs.conjSub_Λt_of_mem ht'')
    have e : d * (k⁻¹ * t * k) * d⁻¹ * (d * (k⁻¹ * u * k) * d⁻¹) = d * (k⁻¹ * (t * u) * k) * d⁻¹ :=
      by group
    rwa [e, ← hkx, show k⁻¹ * (k * x * k⁻¹) * k = x by group] at h3
  apply hxt
  rw [innerModOdd_conj_iff x d, hs.conjSub_Λt_fix (conj_eq_of_comm
    (Subgroup.mem_centralizer_singleton_iff.mp hd.1))]
  exact hdx

theorem Z2Set.hT1_of_noInvolution (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    (hno : ¬ ∃ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) (g : Y) :
    g⁻¹ * b * g ∉ edgeCent (P : Subgroup Y) t u := by
  intro he
  have hbA : b ∉ edgeCent (P : Subgroup Y) t u := fun h =>
    hs.t_ne_u ((conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp h.1.2)).symm.trans hbt)
  have hbb := hs.mul_self_mem_edgeCent hbP
  have he8 := hs.pow_eight he
  rw [conj_pow'] at he8
  have hb8 : b ^ 8 = 1 := eq_of_conj_eq (g := g) (by rw [he8]; group)
  obtain ⟨m, hm⟩ := hs.exists_conj_u
  by_cases hb4 : b ^ 4 = 1
  · by_cases hb2 : b ^ 2 = 1
    · exact hno ⟨b, hbP, hbA, by rw [← sq]; exact hb2⟩
    ·
      have he4 : (g⁻¹ * b * g) ^ 4 = 1 := by rw [conj_pow', hb4]; group
      have hE := hs.sq_mem_E he he4
      rw [conj_pow', sq] at hE
      have hsq := hs.sq_outer_of_noInvolution hall hno hbP hbA
      have hbb2 : b * b * (b * b) = 1 := by
        rw [show b * b * (b * b) = b ^ 4 by simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
        exact hb4
      rcases mem_closure_pair_cases hs.t2 hs.u2 hs.tu_comm hE with h | h | h | h
      · exact hb2 (by rw [sq]; exact eq_of_conj_eq (g := g) (by rw [h]; group))
      · exact hs.not_conj_t_of_outer h1 hbb hbb2 hsq.1 hsq.2 g⁻¹ (by rw [inv_inv]; exact h)
      · refine hs.not_conj_t_of_outer h1 hbb hbb2 hsq.1 hsq.2 (m⁻¹ * g⁻¹) ?_
        rw [show m⁻¹ * g⁻¹ * (b * b) * (m⁻¹ * g⁻¹)⁻¹ = m⁻¹ * (g⁻¹ * (b * b) * g) * m by group, h,
          ← hm]
        group
      · exact hs.not_conj_tu_of_outer h1 hall hno hbb hbb2 hsq.1 hsq.2 g⁻¹
          (by rw [inv_inv]; exact h)
  ·
    have hb4' : b ^ 4 = t * u := by
      have h := hs.pow_four_mul_eq hbP hbt (m := 1) (by simpa using hb4) (by simpa using hb8)
      simpa using h
    have hee : (g⁻¹ * b * g) ^ 2 ∈ edgeCent (P : Subgroup Y) t u := Subgroup.pow_mem _ he 2
    have hE := hs.sq_mem_E hee (by rw [← pow_mul, conj_pow', hb8]; group)
    rw [← pow_mul, conj_pow', hb4'] at hE
    have hc := mem_centralizer_of_conj_eq (hs.eq_tu_of_conj_mem_E hE)
    have hcg : g⁻¹ * b * g⁻¹⁻¹ ∈ (P : Subgroup Y) := by rw [inv_inv]; exact he.1.1
    exact hbA ((hs.mem_edgeCent_iff_conj h1 hbP hc hcg).mpr (by rw [inv_inv]; exact he))

theorem Z2Set.hb_of_noInvolution (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    (hno : ¬ ∃ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) (g : Y) (k : ℕ)
    (hg : g⁻¹ * b ^ (2 * k) * g ∈ (P : Subgroup Y)) :
    g⁻¹ * b ^ (2 * k) * g ∈ edgeCent (P : Subgroup Y) t u := by
  by_contra hxA
  have hbb := hs.mul_self_mem_edgeCent hbP
  have hy : b ^ (2 * k) ∈ edgeCent (P : Subgroup Y) t u := by
    rw [pow_mul, sq]
    exact Subgroup.pow_mem _ hbb k
  have hy8 := hs.pow_eight hy
  rw [← pow_mul] at hy8
  by_cases hx2 : g⁻¹ * b ^ (2 * k) * g * (g⁻¹ * b ^ (2 * k) * g) = 1
  · exact hno ⟨_, hg, hxA, hx2⟩
  have hxx : g⁻¹ * b ^ (2 * k) * g * (g⁻¹ * b ^ (2 * k) * g) = g⁻¹ * b ^ (4 * k) * g := by
    rw [← sq, conj_pow', ← pow_mul, show 2 * k * 2 = 4 * k by ring]
  by_cases hx4 : b ^ (8 * k) = 1
  ·
    have hb4k : b ^ (4 * k) ≠ 1 := fun h => hx2 (by rw [hxx, h]; group)
    have hbtu := hs.pow_four_mul_eq hbP hbt hb4k (by simpa using hx4)
    have hsq := hs.sq_outer_of_noInvolution hall hno hg hxA
    have hxxA := hs.mul_self_mem_edgeCent hg
    have hxx2 : g⁻¹ * b ^ (2 * k) * g * (g⁻¹ * b ^ (2 * k) * g) *
        (g⁻¹ * b ^ (2 * k) * g * (g⁻¹ * b ^ (2 * k) * g)) = 1 := by
      rw [hxx, show g⁻¹ * b ^ (4 * k) * g * (g⁻¹ * b ^ (4 * k) * g) =
        g⁻¹ * (b ^ (4 * k) * b ^ (4 * k)) * g by group, ← pow_add,
        show 4 * k + 4 * k = 8 * k by ring, hx4]
      group
    exact hs.not_conj_tu_of_outer h1 hall hno hxxA hxx2 hsq.1 hsq.2 g
      (by rw [hxx, hbtu]; group)
  ·
    have hbtu := hs.pow_four_mul_eq hbP hbt (m := 2 * k)
      (by rw [show 4 * (2 * k) = 8 * k by ring]; exact hx4)
      (by rw [show 8 * (2 * k) = 2 * k * 8 by ring]; exact hy8)
    rw [show 4 * (2 * k) = 8 * k by ring] at hbtu
    have hxxA := hs.mul_self_mem_edgeCent hg
    have hE := hs.sq_mem_E hxxA (by
      rw [hxx, conj_pow', ← pow_mul, show 4 * k * 4 = 2 * k * 8 by ring, hy8]
      group)
    rw [hxx, conj_pow', ← pow_mul, show 4 * k * 2 = 8 * k by ring, hbtu] at hE
    have hc := mem_centralizer_of_conj_eq (hs.eq_tu_of_conj_mem_E hE)
    have hcg : g⁻¹ * b ^ (2 * k) * g⁻¹⁻¹ ∈ (P : Subgroup Y) := by rw [inv_inv]; exact hg
    have h3 := (hs.mem_edgeCent_iff_conj h1 hy.1.1 hc hcg).mp hy
    rw [inv_inv] at h3
    exact hxA h3

theorem Z2Set.false_of_noInvolution (hs : Z2Set n R S t J u R₀ T₀ P)
    (h1 : C264One (CoreAssembly.conjClass (tightCore R)) t u)
    (hall : ∀ R₁ T₁ : Subgroup Y, IsSylow2In R₁ (tightCore R) →
      R₁ ≤ Subgroup.centralizer ({u} : Set Y) → IsSylow2In T₁ J →
      T₁ ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) → NoA1 t u R₁ T₁)
    (hno : ¬ ∃ c ∈ (P : Subgroup Y), c ∉ edgeCent (P : Subgroup Y) t u ∧ c * c = 1) : False := by
  obtain ⟨b, hbP, hbt⟩ := hs.exists_swap
  have hbA : b ∉ edgeCent (P : Subgroup Y) t u := by
    intro h
    have hbt' : b * t * b⁻¹ = t := by
      rw [Subgroup.mem_centralizer_singleton_iff.mp h.1.2, mul_inv_cancel_right]
    exact hs.t_ne_u (hbt'.symm.trans hbt)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine false_of_transfer_1515 (p := 2) (P := (P : Subgroup Y))
    (Q := edgeCent (P : Subgroup Y) t u) (R₀ := R₀) (u := b)
    (fun _ _ f hf => LinkZ2B.hom_eq_one_of_sylow_tight hs.large.cls.2.1 hs.hR₀ f hf)
    P.isPGroup' P.not_dvd_index (fun x hx q hq => hs.conj_mem_edgeCent hx hq)
    ⟨b, hbP, fun x hx => ?_⟩ hbP hbA (fun g k hg => hs.hb_of_noInvolution h1 hall hno hbP hbt g k hg)
    (fun g hg _ => hs.mem_or_mem_of_swap hbP hbt hg)
    (fun g => hs.hT1_of_noInvolution h1 hall hno hbP hbt g) (hs.hweak h1)
  rcases hs.mem_or_mem_of_swap hbP hbt hx with h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4.Z2W

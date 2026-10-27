module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Asc77.T8 (ne_of_mem_omegaNbr)
open CFSG.ClassicalInvolution.Disconnected (DConnected)
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Acts

variable {Y : Type} [Group Y]

theorem conj_mem_of_conjSub_eq {Λ : Subgroup Y} {c : Y} (hc : conjSub c Λ = Λ) {z : Y}
    (hz : z ∈ Λ) : c * z * c⁻¹ ∈ Λ := by
  have h := conj_mem_conjSub hz c
  rwa [hc] at h

theorem conj_mem_oddCoreOf {Λ : Subgroup Y} {c : Y} (hc : conjSub c Λ = Λ) {o : Y}
    (ho : o ∈ oddCoreOf Λ) : c * o * c⁻¹ ∈ oddCoreOf Λ := by
  have h := conj_mem_conjSub ho c
  rwa [← Thompson.oddCoreOf_conjSub_eq, hc] at h

theorem actsLike_refl (Λ : Subgroup Y) (x : Y) : ActsLike Λ x x := by
  intro z _
  rw [mul_inv_cancel]
  exact Subgroup.one_mem _

theorem actsLike_symm {Λ : Subgroup Y} {x w : Y} (h : ActsLike Λ x w) :
    ActsLike Λ w x := by
  intro z hz
  have h1 := Subgroup.inv_mem _ (h z hz)
  rwa [mul_inv_rev, inv_inv] at h1

theorem actsLike_trans {Λ : Subgroup Y} {x w v : Y} (h1 : ActsLike Λ x w)
    (h2 : ActsLike Λ w v) : ActsLike Λ x v := by
  intro z hz
  have h3 := Subgroup.mul_mem _ (h1 z hz) (h2 z hz)
  rwa [show x * z * x⁻¹ * (w * z * w⁻¹)⁻¹ * (w * z * w⁻¹ * (v * z * v⁻¹)⁻¹) =
    x * z * x⁻¹ * (v * z * v⁻¹)⁻¹ by group] at h3

theorem actsTriv_iff {Λ : Subgroup Y} {x : Y} : ActsTriv Λ x ↔ ActsLike Λ x 1 := by
  constructor
  · intro h z hz
    have h1 := h z hz
    rwa [show x * z * x⁻¹ * z⁻¹ = x * z * x⁻¹ * (1 * z * 1⁻¹)⁻¹ by group] at h1
  · intro h z hz
    have h1 := h z hz
    rwa [show x * z * x⁻¹ * (1 * z * 1⁻¹)⁻¹ = x * z * x⁻¹ * z⁻¹ by group] at h1

theorem actsLike_mul {Λ : Subgroup Y} {x y w v : Y} (hx : ActsLike Λ x w)
    (hy : ActsLike Λ y v) (hv : conjSub v Λ = Λ) (hxn : conjSub x Λ = Λ) :
    ActsLike Λ (x * y) (w * v) := by
  intro z hz
  have hz1 : v * z * v⁻¹ ∈ Λ := conj_mem_of_conjSub_eq hv hz
  have h3 := Subgroup.mul_mem _ (conj_mem_oddCoreOf hxn (hy z hz)) (hx _ hz1)
  rwa [show x * (y * z * y⁻¹ * (v * z * v⁻¹)⁻¹) * x⁻¹ *
      (x * (v * z * v⁻¹) * x⁻¹ * (w * (v * z * v⁻¹) * w⁻¹)⁻¹) =
    x * y * z * (x * y)⁻¹ * (w * v * z * (w * v)⁻¹)⁻¹ by group] at h3

theorem actsLike_inv {Λ : Subgroup Y} {x w : Y} (hx : ActsLike Λ x w)
    (hw : conjSub w⁻¹ Λ = Λ) (hxn : conjSub x⁻¹ Λ = Λ) : ActsLike Λ x⁻¹ w⁻¹ := by
  intro z hz
  have hz1 : w⁻¹ * z * w⁻¹⁻¹ ∈ Λ := conj_mem_of_conjSub_eq hw hz
  have h1 := conj_mem_oddCoreOf hxn (Subgroup.inv_mem _ (hx _ hz1))
  rwa [show x⁻¹ * (x * (w⁻¹ * z * w⁻¹⁻¹) * x⁻¹ * (w * (w⁻¹ * z * w⁻¹⁻¹) * w⁻¹)⁻¹)⁻¹ * x⁻¹⁻¹ =
    x⁻¹ * z * x⁻¹⁻¹ * (w⁻¹ * z * w⁻¹⁻¹)⁻¹ by group] at h1

theorem actsLike_conj {Λ : Subgroup Y} {x w : Y} (h : ActsLike Λ x w) (g : Y) :
    ActsLike (conjSub g Λ) (g * x * g⁻¹) (g * w * g⁻¹) := by
  intro z hz
  rw [mem_conjSub_iff] at hz
  rw [Thompson.oddCoreOf_conjSub_eq, mem_conjSub_iff]
  rw [show g⁻¹ * (g * x * g⁻¹ * z * (g * x * g⁻¹)⁻¹ * (g * w * g⁻¹ * z * (g * w * g⁻¹)⁻¹)⁻¹) * g =
    x * (g⁻¹ * z * g) * x⁻¹ * (w * (g⁻¹ * z * g) * w⁻¹)⁻¹ by group]
  exact h _ hz

theorem actsTriv_conj {Λ : Subgroup Y} {x : Y} (h : ActsTriv Λ x) (g : Y) :
    ActsTriv (conjSub g Λ) (g * x * g⁻¹) := by
  have h1 := actsLike_conj (actsTriv_iff.mp h) g
  rw [show g * 1 * g⁻¹ = 1 by group] at h1
  exact actsTriv_iff.mpr h1

theorem innerModOdd_mul {Λ : Subgroup Y} {x y : Y} (hx : InnerModOdd Λ x)
    (hy : InnerModOdd Λ y) (hxn : conjSub x Λ = Λ) : InnerModOdd Λ (x * y) := by
  obtain ⟨w, hw, hxw⟩ := hx
  obtain ⟨v, hv, hyv⟩ := hy
  exact ⟨w * v, Λ.mul_mem hw hv, actsLike_mul hxw hyv (conjSub_eq_self_of_mem hv) hxn⟩

theorem innerModOdd_inv {Λ : Subgroup Y} {x : Y} (hx : InnerModOdd Λ x)
    (hxn : conjSub x⁻¹ Λ = Λ) : InnerModOdd Λ x⁻¹ := by
  obtain ⟨w, hw, hxw⟩ := hx
  exact ⟨w⁻¹, Λ.inv_mem hw, actsLike_inv hxw (conjSub_eq_self_of_mem (Λ.inv_mem hw)) hxn⟩

theorem innerModOdd_conj {Λ : Subgroup Y} {x : Y} (hx : InnerModOdd Λ x) (g : Y) :
    InnerModOdd (conjSub g Λ) (g * x * g⁻¹) := by
  obtain ⟨w, hw, hxw⟩ := hx
  exact ⟨g * w * g⁻¹, conj_mem_conjSub hw g, actsLike_conj hxw g⟩

theorem innerModOdd_conj_iff {Λ : Subgroup Y} (x g : Y) :
    InnerModOdd Λ x ↔ InnerModOdd (conjSub g Λ) (g * x * g⁻¹) := by
  refine ⟨fun h => innerModOdd_conj h g, fun h => ?_⟩
  have h1 := innerModOdd_conj h g⁻¹
  rwa [conjSub_inv_conjSub, show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1

theorem innerModOdd_of_actsTriv {Λ : Subgroup Y} {x : Y} (h : ActsTriv Λ x) :
    InnerModOdd Λ x :=
  ⟨1, Λ.one_mem, actsTriv_iff.mp h⟩

theorem natCard_conjSub' (g : Y) (H : Subgroup Y) :
    Nat.card ↥(conjSub g H) = Nat.card ↥H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_closure_pair_cases {a b : Y} (ha : a * a = 1) (hb : b * b = 1)
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

variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y} {R₀ T₀ : Subgroup Y} {P : Sylow 2 Y}

theorem Z2SetR.t_ne_u (hs : Z2SetR r n R S t J u R₀ T₀ P) : t ≠ u := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  exact ne_of_mem_omegaNbr ((TightLargeHypR.typeRFam hs.large).noTwins _ hK) hs.hJ
    hs.large.datum.isUniqueInvolution_core hs.hu

theorem Z2SetR.mem_cls_conj (hs : Z2SetR r n R S t J u R₀ T₀ P) {L : Subgroup Y}
    (hL : L ∈ CoreAssembly.conjClass (tightCore R)) (c : Y) :
    conjSub c L ∈ CoreAssembly.conjClass (tightCore R) :=
  hs.large.datum.hypOmegaGen.conjInvariant c L hL

theorem Z2SetR.eq_J_of_inv (hs : Z2SetR r n R S t J u R₀ T₀ P) {M : Subgroup Y}
    (hM : M ∈ CoreAssembly.conjClass (tightCore R)) (hMu : IsUniqueInvolution M u) : M = J :=
  (TightLargeHypR.typeRFam hs.large).noTwins J hs.hJ.1 M ⟨hM, u, hs.hu, hMu⟩

theorem Z2SetR.t2 (hs : Z2SetR r n R S t J u R₀ T₀ P) : t * t = 1 :=
  hs.large.datum.isUniqueInvolution_core.sq

theorem Z2SetR.u2 (hs : Z2SetR r n R S t J u R₀ T₀ P) : u * u = 1 :=
  hs.hu.sq

theorem Z2SetR.tu_comm (hs : Z2SetR r n R S t J u R₀ T₀ P) : t * u = u * t :=
  Q3CL.T8.mul_comm_of_mem_omegaNbr hs.large.datum.hypOmegaGen
    hs.large.datum.isUniqueInvolution_core hs.hJ hs.hu

theorem Z2SetR.conjSub_K_fix (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = t) : conjSub c (tightCore R) = tightCore R :=
  eq_core_of_isUniqueInvolution hs.large (hs.mem_cls_conj ⟨1, conjSub_one _⟩ c) (by
    have h := hs.large.datum.isUniqueInvolution_core.conj c
    rwa [hc] at h)

theorem Z2SetR.conjSub_K_swap (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = u) : conjSub c (tightCore R) = J :=
  hs.eq_J_of_inv (hs.mem_cls_conj ⟨1, conjSub_one _⟩ c) (by
    have h := hs.large.datum.isUniqueInvolution_core.conj c
    rwa [hc] at h)

theorem Z2SetR.conjSub_J_fix (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = u) : conjSub c J = J :=
  hs.eq_J_of_inv (hs.mem_cls_conj hs.hJ.1 c) (by
    have h := hs.hu.conj c
    rwa [hc] at h)

theorem Z2SetR.conjSub_J_swap (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = t) : conjSub c J = tightCore R :=
  eq_core_of_isUniqueInvolution hs.large (hs.mem_cls_conj hs.hJ.1 c) (by
    have h := hs.hu.conj c
    rwa [hc] at h)

theorem Z2SetR.conjSub_Λt_fix (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = t) : conjSub c (linkLayer R t) = linkLayer R t := by
  show conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t) =
    linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_K_fix hc, hc]

theorem Z2SetR.conjSub_Λt_swap (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * t * c⁻¹ = u) : conjSub c (linkLayer R t) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := by
  show conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) (tightCore R) t) = _
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_K_swap hc, hc]

theorem Z2SetR.conjSub_Λu_fix (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = u) : conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u := by
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_J_fix hc, hc]

theorem Z2SetR.conjSub_Λu_swap (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c * u * c⁻¹ = t) : conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayer R t := by
  rw [conjSub_linkLayerAt hs.large.datum.hypOmegaGen.conjInvariant, hs.conjSub_J_swap hc, hc]

theorem conj_eq_of_comm {c x : Y} (h : c * x = x * c) : c * x * c⁻¹ = x := by
  rw [h, mul_inv_cancel_right]

theorem Z2SetR.conjSub_Λt_of_mem (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c ∈ edgeCent (P : Subgroup Y) t u) : conjSub c (linkLayer R t) = linkLayer R t :=
  hs.conjSub_Λt_fix (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hc.1.2))

theorem Z2SetR.conjSub_Λu_of_mem (hs : Z2SetR r n R S t J u R₀ T₀ P) {c : Y}
    (hc : c ∈ edgeCent (P : Subgroup Y) t u) :
    conjSub c (linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u) =
      linkLayerAt (CoreAssembly.conjClass (tightCore R)) J u :=
  hs.conjSub_Λu_fix (conj_eq_of_comm (Subgroup.mem_centralizer_singleton_iff.mp hc.2))

theorem Z2SetR.swap_u (hs : Z2SetR r n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbt : b * t * b⁻¹ = u) : b * u * b⁻¹ = t := by
  rcases hs.perm hbP with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd (h1.symm.trans hbt) hs.t_ne_u
  · exact h2

theorem Z2SetR.swap_of_not_mem (hs : Z2SetR r n R S t J u R₀ T₀ P) {b : Y}
    (hbP : b ∈ (P : Subgroup Y)) (hbA : b ∉ edgeCent (P : Subgroup Y) t u) :
    b * t * b⁻¹ = u := by
  rcases hs.perm hbP with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd (hs.mem_edgeCent_iff.mpr ⟨hbP, h1⟩) hbA
  · exact h1

theorem inv_conj_of_conj {b x y : Y} (h : b * x * b⁻¹ = y) : b⁻¹ * y * b⁻¹⁻¹ = x := by
  rw [← h]
  group

theorem conj_pow' (g b : Y) (k : ℕ) : (g⁻¹ * b * g) ^ k = g⁻¹ * b ^ k * g := by
  have h := conj_pow (a := g⁻¹) (b := b) (i := k)
  rwa [inv_inv] at h

theorem Z2SetR.t_mem_P (hs : Z2SetR r n R S t J u R₀ T₀ P) : t ∈ (P : Subgroup Y) := by
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := ⟨1, conjSub_one _⟩
  refine hs.hR₀P (CFSG.ClassicalInvolution.Asc77.T3.mem_of_isPGroup
    hs.large.datum.isUniqueInvolution_core hs.hR₀.1 hs.hR₀.2.1 ?_)
  have h8 := Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
    (mem_RSet_of_isSylow2In hK hs.hR₀)
  omega

theorem Z2SetR.u_mem_P (hs : Z2SetR r n R S t J u R₀ T₀ P) : u ∈ (P : Subgroup Y) := by
  refine hs.hT₀P (CFSG.ClassicalInvolution.Asc77.T3.mem_of_isPGroup hs.hu hs.hT₀.1 hs.hT₀.2.1 ?_)
  have h8 := Sec6Gen.eight_le_of_mem_RSet hs.large.datum.hypOmegaGen
    (mem_RSet_of_isSylow2In hs.hJ.1 hs.hT₀)
  omega

theorem Z2SetR.tu_not_conj_u (hs : Z2SetR r n R S t J u R₀ T₀ P) (g : Y) :
    g * (t * u) * g⁻¹ ≠ u := by
  intro h
  obtain ⟨m, hm⟩ := hs.exists_conj_u
  apply hs.tu_not_conj (m⁻¹ * g)
  rw [show m⁻¹ * g * (t * u) * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * (t * u) * g⁻¹) * m by group, h, ← hm]
  group

theorem Z2SetR.tu_ne_one (hs : Z2SetR r n R S t J u R₀ T₀ P) : t * u ≠ 1 := by
  intro h
  apply hs.t_ne_u
  have h1 : u = t⁻¹ := eq_inv_of_mul_eq_one_right h
  rw [h1, inv_eq_of_mul_eq_one_left hs.t2]

theorem Z2SetR.eq_tu_of_conj_mem_E (hs : Z2SetR r n R S t J u R₀ T₀ P) {g : Y}
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

theorem mem_centralizer_of_conj_eq {g a : Y} (h : g⁻¹ * a * g = a) :
    g⁻¹ ∈ Subgroup.centralizer ({a} : Set Y) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g⁻¹ * a = g⁻¹ * a * g * g⁻¹ := by group
    _ = a * g⁻¹ := by rw [h]

end Cit3

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

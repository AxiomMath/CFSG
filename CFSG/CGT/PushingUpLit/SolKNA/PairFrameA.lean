module

public import CFSG.CGT.PushingUpLit.SolKNA.CaseData
public import CFSG.CGT.PushingUpLit.SolKNA.PairFrame
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.Open (IsElemAbelian)

variable {G : Type} [Group G]

structure AData (R T W : Subgroup G) : Prop extends TIPair R T where
  elem_T : ∀ t ∈ T, t * t = 1
  T_le : T ≤ W
  W_le : W ≤ R ⊔ T
  normal : R ⊔ T ≤ Subgroup.normalizer (W : Set G)
  card_W : Nat.card ↥W = Nat.card ↥T ^ 3
  Z_sq : ∀ x ∈ W, x * x ∈ W ⊓ Subgroup.centralizer (W : Set G)
  Z_comm : ∀ x ∈ W, ∀ y ∈ W, x * y * x⁻¹ * y⁻¹ ∈ W ⊓ Subgroup.centralizer (W : Set G)
  Z_le_comm : W ⊓ Subgroup.centralizer (W : Set G) ≤ ⁅W, W⁆
  iso : Nonempty (↥(W ⊓ Subgroup.centralizer (W : Set G)) ≃* ↥T)
  relIndex_two : W.relIndex (R ⊔ T) = 2
  card_N : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) ≤ Nat.card ↥T

namespace AData

theorem center_comm {W : Subgroup G} {z w : G} (hz : z ∈ W ⊓ Subgroup.centralizer (W : Set G))
    (hw : w ∈ W) : z * w = w * z :=
  (Subgroup.mem_centralizer_iff.mp hz.2 w hw).symm

section Basic

variable {R T W : Subgroup G} (A : AData R T W)
include A

theorem conj_mem_W {s w : G} (hs : s ∈ R ⊔ T) (hw : w ∈ W) : s * w * s⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp (A.normal hs) w).mp hw

theorem conj_mem_R {t r : G} (ht : t ∈ T) (hr : r ∈ R) : t * r * t⁻¹ ∈ R :=
  (Subgroup.mem_normalizer_iff.mp (A.T_norm ht) r).mp hr

theorem inf_sup_eq : (W ⊓ R) ⊔ T = W := by
  refine le_antisymm (sup_le inf_le_left A.T_le) fun w hw => ?_
  obtain ⟨r, hr, t, ht, rfl⟩ := A.exists_mul (A.W_le hw)
  have hrW : r ∈ W := by
    have := W.mul_mem hw (W.inv_mem (A.T_le ht))
    simpa using this
  exact Subgroup.mul_mem_sup ⟨hrW, hr⟩ ht

theorem conj_mem_H {s h : G} (hs : s ∈ R ⊔ T) (hh : h ∈ W ⊓ R) : s * h * s⁻¹ ∈ W ⊓ R :=
  ⟨A.conj_mem_W hs hh.1, (Subgroup.mem_normalizer_iff.mp (A.S_le_normalizer hs) h).mp hh.2⟩

theorem S_le_normalizer_H : R ⊔ T ≤ Subgroup.normalizer ((W ⊓ R : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => A.conj_mem_H hs hh, fun hh => ?_⟩
  have := A.conj_mem_H ((R ⊔ T).inv_mem hs) hh
  simpa [mul_assoc] using this

theorem comm_mem_R {a b : G} (ha : a ∈ R ⊔ T) (hb : b ∈ R ⊔ T) : a * b * a⁻¹ * b⁻¹ ∈ R := by
  obtain ⟨r₁, hr₁, t₁, ht₁, rfl⟩ := A.exists_mul ha
  obtain ⟨r₂, hr₂, t₂, ht₂, rfl⟩ := A.exists_mul hb
  have h : t₁ * t₂ = t₂ * t₁ := A.comm_T t₁ ht₁ t₂ ht₂
  have e : r₁ * t₁ * (r₂ * t₂) * (r₁ * t₁)⁻¹ * (r₂ * t₂)⁻¹ =
      (r₁ * (t₁ * r₂ * t₁⁻¹)) * (r₂ * (t₂ * r₁ * t₂⁻¹))⁻¹ := by
    calc r₁ * t₁ * (r₂ * t₂) * (r₁ * t₁)⁻¹ * (r₂ * t₂)⁻¹
        = (r₁ * t₁ * (r₂ * t₂)) * (r₂ * t₂ * (r₁ * t₁))⁻¹ := by group
      _ = (r₁ * (t₁ * r₂ * t₁⁻¹) * (t₁ * t₂)) * (r₂ * (t₂ * r₁ * t₂⁻¹) * (t₂ * t₁))⁻¹ := by
        group
      _ = (r₁ * (t₁ * r₂ * t₁⁻¹)) * (r₂ * (t₂ * r₁ * t₂⁻¹))⁻¹ := by
        rw [← h]
        group
  rw [e]
  exact R.mul_mem (R.mul_mem hr₁ (A.conj_mem_R ht₁ hr₂))
    (R.inv_mem (R.mul_mem hr₂ (A.conj_mem_R ht₂ hr₁)))

theorem Z_le_R : W ⊓ Subgroup.centralizer (W : Set G) ≤ R := by
  intro z hz
  have hcomm : ⁅W, W⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact A.comm_mem_R (A.W_le ha) (A.W_le hb)
  exact hcomm (A.Z_le_comm hz)

theorem Z_le_H : W ⊓ Subgroup.centralizer (W : Set G) ≤ W ⊓ R :=
  le_inf inf_le_left A.Z_le_R

theorem Z_le_N :
    W ⊓ Subgroup.centralizer (W : Set G) ≤ R ⊓ Subgroup.normalizer (T : Set G) := by
  intro z hz
  rw [A.inf_normalizer_eq]
  exact ⟨A.Z_le_R hz, Subgroup.mem_centralizer_iff.mpr fun t ht =>
    (center_comm hz (A.T_le ht)).symm⟩

theorem inv_eq_self {t : G} (ht : t ∈ T) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (A.elem_T t ht)

theorem conj_inv_eq {x t : G} (ht : t ∈ T) : (x * t * x⁻¹)⁻¹ = x * t * x⁻¹ := by
  have h : (x * t * x⁻¹)⁻¹ = x * t⁻¹ * x⁻¹ := by group
  rw [h, A.inv_eq_self ht]

theorem mem_N_of_comm {c t : G} (hc : c ∈ R) (ht : t ∈ T) (ht1 : t ≠ 1) (h : c * t = t * c) :
    c ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  have hcS : c ∈ R ⊔ T := Subgroup.mem_sup_left hc
  have hmem : t ∈ T ⊓ rightConjugate T c := by
    refine ⟨ht, (mem_rightConjugate_iff T c _).mpr ?_⟩
    have : c * t * c⁻¹ = t := by rw [h]; group
    rw [this]
    exact ht
  have hne : T ⊓ rightConjugate T c ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.mem_bot] at hmem
    exact ht1 hmem
  exact ⟨hc, (rightConjugate_eq_self_iff T c).mp (A.ti c hcS hne)⟩

theorem exists_of_comm {s t : G} (hs : s ∈ R ⊔ T) (ht : t ∈ T) (ht1 : t ≠ 1)
    (h : s * t = t * s) :
    ∃ n ∈ R ⊓ Subgroup.normalizer (T : Set G), ∃ t₀ ∈ T, s = n * t₀ := by
  obtain ⟨r, hr, t₀, ht₀, rfl⟩ := A.exists_mul hs
  refine ⟨r, ?_, t₀, ht₀, rfl⟩
  apply A.mem_N_of_comm hr ht ht1
  have hT : t₀ * t = t * t₀ := A.comm_T t₀ ht₀ t ht
  have h' : r * t * t₀ = t * r * t₀ := by
    calc r * t * t₀ = r * (t * t₀) := by group
      _ = r * (t₀ * t) := by rw [hT]
      _ = r * t₀ * t := by group
      _ = t * (r * t₀) := h
      _ = t * r * t₀ := by group
  exact mul_right_cancel h'

theorem comm_mem_H {x t : G} (hx : x ∈ R) (ht : t ∈ T) : t * x * t⁻¹ * x⁻¹ ∈ W ⊓ R := by
  refine ⟨?_, R.mul_mem (A.conj_mem_R ht hx) (R.inv_mem hx)⟩
  have h1 : x * t⁻¹ * x⁻¹ ∈ W :=
    A.conj_mem_W (Subgroup.mem_sup_left hx) (W.inv_mem (A.T_le ht))
  have h2 : t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
  rw [h2]
  exact W.mul_mem (A.T_le ht) h1

theorem conj_comm_mem_Z {x t : G} (hx : x ∈ R) (ht : t ∈ T) :
    (x * t * x⁻¹) * t * (x * t * x⁻¹) * t ∈ W ⊓ Subgroup.centralizer (W : Set G) := by
  have hcW : x * t * x⁻¹ ∈ W := A.conj_mem_W (Subgroup.mem_sup_left hx) (A.T_le ht)
  have := A.Z_comm _ hcW t (A.T_le ht)
  rwa [A.conj_inv_eq ht, A.inv_eq_self ht] at this

theorem comm_sq_eq {x t : G} (hx : x ∈ R) (ht : t ∈ T) :
    (t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹) =
      (x * t * x⁻¹) * t * (x * t * x⁻¹) * t := by
  have htq := center_comm (A.conj_comm_mem_Z hx ht) (A.T_le ht)
  have hp : t * x * t⁻¹ * x⁻¹ = t * (x * t * x⁻¹) := by
    calc t * x * t⁻¹ * x⁻¹ = t * (x * t⁻¹ * x⁻¹) := by group
      _ = t * (x * t * x⁻¹) := by rw [A.inv_eq_self ht]
  rw [hp]
  refine mul_right_cancel (b := t) ?_
  calc t * (x * t * x⁻¹) * (t * (x * t * x⁻¹)) * t
      = t * ((x * t * x⁻¹) * t * (x * t * x⁻¹) * t) := by group
    _ = (x * t * x⁻¹) * t * (x * t * x⁻¹) * t * t := htq.symm

theorem comm_mul {x s t : G} (hx : x ∈ R) (hs : s ∈ T) (ht : t ∈ T) :
    ∃ c ∈ W ⊓ Subgroup.centralizer (W : Set G),
      (s * t) * x * (s * t)⁻¹ * x⁻¹ = c * (s * x * s⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹) := by
  have hps := (A.comm_mem_H hx hs).1
  have hpt := (A.comm_mem_H hx ht).1
  refine ⟨(s * (t * x * t⁻¹ * x⁻¹) * s⁻¹ * (t * x * t⁻¹ * x⁻¹)⁻¹) *
    ((t * x * t⁻¹ * x⁻¹) * (s * x * s⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹)⁻¹ * (s * x * s⁻¹ * x⁻¹)⁻¹),
    Subgroup.mul_mem _ (A.Z_comm _ (A.T_le hs) _ hpt) (A.Z_comm _ hpt _ hps), by group⟩

end Basic

section Counting

variable [Finite G] {R T W : Subgroup G} (A : AData R T W)
include A

theorem card_S : Nat.card ↥(R ⊔ T) = Nat.card ↥R * Nat.card ↥T :=
  CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer A.T_norm
    (by rw [inf_comm]; exact A.inf_eq)

theorem card_W_eq : Nat.card ↥W = Nat.card ↥(W ⊓ R) * Nat.card ↥T := by
  have hinf : (W ⊓ R) ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ T ⊓ R := ⟨hx.2, hx.1.2⟩
    rwa [A.inf_eq] at hx'
  have hsup := CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer
    (le_sup_right.trans A.S_le_normalizer_H) hinf
  rwa [A.inf_sup_eq] at hsup

theorem card_H : Nat.card ↥(W ⊓ R) = Nat.card ↥T ^ 2 := by
  have h := A.card_W_eq
  rw [A.card_W] at h
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card ↥(W ⊓ R) * Nat.card ↥T = Nat.card ↥T ^ 3 := h.symm
    _ = Nat.card ↥T ^ 2 * Nat.card ↥T := by ring

theorem card_R : Nat.card ↥R = 2 * Nat.card ↥(W ⊓ R) := by
  have h1 := Subgroup.relIndex_mul_card W (R ⊔ T)
  rw [inf_eq_left.mpr A.W_le, A.relIndex_two, A.card_S, A.card_W_eq] at h1
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card ↥R * Nat.card ↥T = 2 * (Nat.card ↥(W ⊓ R) * Nat.card ↥T) := h1.symm
    _ = 2 * Nat.card ↥(W ⊓ R) * Nat.card ↥T := by ring

theorem relIndex_R : (W ⊓ R).relIndex R = 2 := by
  have h1 := Subgroup.relIndex_mul_card (W ⊓ R) R
  rw [inf_eq_left.mpr (inf_le_right : W ⊓ R ≤ R), A.card_R] at h1
  have hpos : 0 < Nat.card ↥(W ⊓ R) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem center_eq :
    W ⊓ Subgroup.centralizer (W : Set G) = R ⊓ Subgroup.normalizer (T : Set G) := by
  obtain ⟨e⟩ := A.iso
  refine Subgroup.eq_of_le_of_card_ge A.Z_le_N ?_
  rw [Nat.card_congr e.toEquiv]
  exact A.card_N

theorem card_N_eq : Nat.card ↥(R ⊓ Subgroup.normalizer (T : Set G)) = Nat.card ↥T := by
  obtain ⟨e⟩ := A.iso
  rw [← A.center_eq]
  exact Nat.card_congr e.toEquiv

theorem N_le_H : R ⊓ Subgroup.normalizer (T : Set G) ≤ W ⊓ R := by
  rw [← A.center_eq]
  exact A.Z_le_H

theorem N_le_W : R ⊓ Subgroup.normalizer (T : Set G) ≤ W :=
  A.N_le_H.trans inf_le_left

theorem N_conj {r n : G} (hr : r ∈ R) (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) :
    r * n * r⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  rw [← A.center_eq] at hn ⊢
  have hrS : r ∈ R ⊔ T := Subgroup.mem_sup_left hr
  refine ⟨A.conj_mem_W hrS hn.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have hw' : r⁻¹ * w * r⁻¹⁻¹ ∈ W := A.conj_mem_W ((R ⊔ T).inv_mem hrS) hw
  have h1 := center_comm hn hw'
  calc w * (r * n * r⁻¹) = r * ((r⁻¹ * w * r⁻¹⁻¹) * n) * r⁻¹ := by group
    _ = r * (n * (r⁻¹ * w * r⁻¹⁻¹)) * r⁻¹ := by rw [h1]
    _ = (r * n * r⁻¹) * w := by group

theorem N_central {n h : G} (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) (hh : h ∈ W) :
    n * h = h * n := by
  rw [← A.center_eq] at hn
  exact center_comm hn hh

theorem elem_N {n : G} (hn : n ∈ R ⊓ Subgroup.normalizer (T : Set G)) : n * n = 1 := by
  rw [← A.center_eq] at hn
  obtain ⟨e⟩ := A.iso
  let z : ↥(W ⊓ Subgroup.centralizer (W : Set G)) := ⟨n, hn⟩
  have h1 : e (z * z) = 1 := by
    rw [map_mul]
    exact Subtype.ext (A.elem_T _ (e z).2)
  have h2 : z * z = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem pow_four {x : G} (hx : x ∈ W ⊓ R) : x ^ 4 = 1 := by
  have h1 := A.Z_sq x hx.1
  rw [A.center_eq] at h1
  calc x ^ 4 = (x * x) * (x * x) := by simp [pow_succ, mul_assoc]
    _ = 1 := A.elem_N h1

theorem mem_W_of_comm {s t : G} (hs : s ∈ R ⊔ T) (ht : t ∈ T) (ht1 : t ≠ 1)
    (h : s * t = t * s) : s ∈ W := by
  obtain ⟨n, hn, t₀, ht₀, rfl⟩ := A.exists_of_comm hs ht ht1 h
  exact W.mul_mem (A.N_le_W hn) (A.T_le ht₀)

theorem exists_conj_eq {t z : G} (ht : t ∈ T) (ht1 : t ≠ 1)
    (hz : z ∈ W ⊓ Subgroup.centralizer (W : Set G)) : ∃ w ∈ W, w * t * w⁻¹ = z * t := by
  have htW : t ∈ W := A.T_le ht
  let g : ↥W → ↥(W ⊓ Subgroup.centralizer (W : Set G)) := fun w =>
    ⟨(w : G) * t * (w : G)⁻¹ * t⁻¹, A.Z_comm w w.2 t htW⟩
  have hmul : ∀ a b : ↥W, g (a * b) = g a * g b := by
    intro a b
    apply Subtype.ext
    have hu : (a : G) * t * (a : G)⁻¹ * t⁻¹ ∈ W ⊓ Subgroup.centralizer (W : Set G) :=
      A.Z_comm a a.2 t htW
    have hv : (b : G) * t * (b : G)⁻¹ * t⁻¹ ∈ W ⊓ Subgroup.centralizer (W : Set G) :=
      A.Z_comm b b.2 t htW
    have hav : (a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) =
        ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G) := (center_comm hv a.2).symm
    have huv : ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) =
        ((b : G) * t * (b : G)⁻¹ * t⁻¹) * ((a : G) * t * (a : G)⁻¹ * t⁻¹) :=
      center_comm hu hv.1
    show ((a : G) * (b : G)) * t * ((a : G) * (b : G))⁻¹ * t⁻¹ =
      ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹)
    calc ((a : G) * (b : G)) * t * ((a : G) * (b : G))⁻¹ * t⁻¹
        = (a : G) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) * t * (a : G)⁻¹ * t⁻¹ := by group
      _ = ((b : G) * t * (b : G)⁻¹ * t⁻¹) * (a : G) * t * (a : G)⁻¹ * t⁻¹ := by rw [hav]
      _ = ((b : G) * t * (b : G)⁻¹ * t⁻¹) * ((a : G) * t * (a : G)⁻¹ * t⁻¹) := by group
      _ = ((a : G) * t * (a : G)⁻¹ * t⁻¹) * ((b : G) * t * (b : G)⁻¹ * t⁻¹) := huv.symm
  let f : ↥W →* ↥(W ⊓ Subgroup.centralizer (W : Set G)) := MonoidHom.mk' g hmul
  have hf : ∀ w : ↥W, ((f w : ↥(W ⊓ Subgroup.centralizer (W : Set G))) : G) =
      (w : G) * t * (w : G)⁻¹ * t⁻¹ := fun w => rfl
  have hker_mem : ∀ w : ↥W, w ∈ f.ker → (w : G) * t = t * (w : G) := by
    intro w hw
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hw)
    rw [hf w] at h1
    have h2 : (w : G) * t * (w : G)⁻¹ * t⁻¹ = 1 := h1
    have h3 : (w : G) * t * (w : G)⁻¹ = t := mul_inv_eq_one.mp h2
    calc (w : G) * t = ((w : G) * t * (w : G)⁻¹) * (w : G) := by group
      _ = t * (w : G) := by rw [h3]
  have hker_le : Nat.card ↥f.ker ≤ Nat.card ↥T ^ 2 := by
    have key : ∀ n ∈ R ⊓ Subgroup.normalizer (T : Set G), ∀ s ∈ T, s * n * s⁻¹ = n := by
      intro n hn s hs
      have h := A.N_comm hn hs
      rw [← h]
      group
    have hTN : T ≤ Subgroup.normalizer
        ((R ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) := by
      intro s hs
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        rw [key n hn s hs]
        exact hn
      · intro hn
        have h1 := key (s * n * s⁻¹) hn s⁻¹ (T.inv_mem hs)
        have h2 : s⁻¹ * (s * n * s⁻¹) * s⁻¹⁻¹ = n := by group
        rw [h2] at h1
        rw [h1]
        exact hn
    have hinf : (R ⊓ Subgroup.normalizer (T : Set G)) ⊓ T = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hx' : x ∈ T ⊓ R := ⟨hx.2, hx.1.1⟩
      rwa [A.inf_eq] at hx'
    have hsup := CFSG.ComponentClassification.AschbacherTheorem3.card_sup_of_le_normalizer
      hTN hinf
    have hmem : ∀ w : ↥f.ker, w.1.1 ∈ (R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T := by
      intro w
      obtain ⟨n, hn, t₀, ht₀, he⟩ :=
        A.exists_of_comm (A.W_le w.1.2) ht ht1 (hker_mem w.1 w.2)
      rw [he]
      exact Subgroup.mul_mem_sup hn ht₀
    let k : ↥f.ker → ↥((R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T) := fun w =>
      ⟨w.1.1, hmem w⟩
    have hk : Function.Injective k := by
      intro a b hab
      have h := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h)
    calc Nat.card ↥f.ker ≤ Nat.card ↥((R ⊓ Subgroup.normalizer (T : Set G)) ⊔ T) :=
          Nat.card_le_card_of_injective k hk
      _ = Nat.card ↥T ^ 2 := by rw [hsup, A.card_N_eq, sq]
  obtain ⟨e⟩ := A.iso
  have hrange_le : Nat.card ↥f.range ≤ Nat.card ↥T := by
    calc Nat.card ↥f.range ≤ Nat.card ↥(W ⊓ Subgroup.centralizer (W : Set G)) :=
          Subgroup.card_le_card_group _
      _ = Nat.card ↥T := Nat.card_congr e.toEquiv
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  have hrange_ge : Nat.card ↥T ≤ Nat.card ↥f.range := by
    have h1 : Nat.card ↥T ^ 2 * Nat.card ↥T ≤ Nat.card ↥T ^ 2 * Nat.card ↥f.range := by
      calc Nat.card ↥T ^ 2 * Nat.card ↥T = Nat.card ↥T ^ 3 := by ring
        _ = Nat.card ↥W := A.card_W.symm
        _ = Nat.card ↥f.ker * Nat.card ↥f.range := (Subgroup.card_ker_mul_card_range f).symm
        _ ≤ Nat.card ↥T ^ 2 * Nat.card ↥f.range := Nat.mul_le_mul_right _ hker_le
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hpos 2)
  have hrange_top : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by
    rw [Nat.card_congr e.toEquiv]
    exact le_antisymm hrange_le hrange_ge)
  obtain ⟨w, hw⟩ := (MonoidHom.range_eq_top.mp hrange_top) ⟨z, hz⟩
  refine ⟨w, w.2, ?_⟩
  have h1 := congrArg Subtype.val hw
  rw [hf w] at h1
  have h2 : (w : G) * t * (w : G)⁻¹ * t⁻¹ = z := h1
  calc (w : G) * t * (w : G)⁻¹ = ((w : G) * t * (w : G)⁻¹ * t⁻¹) * t := by group
    _ = z * t := by rw [h2]

theorem not_comm_conj {x t : G} (hx : x ∈ R) (hxH : x ∉ W ⊓ R) (ht : t ∈ T) (ht1 : t ≠ 1) :
    (x * t * x⁻¹) * t ≠ t * (x * t * x⁻¹) := by
  intro hc
  have hxS : x ∈ R ⊔ T := Subgroup.mem_sup_left hx
  have hcW : x * t * x⁻¹ ∈ W := A.conj_mem_W hxS (A.T_le ht)
  obtain ⟨n, hn, t₀, ht₀, hct⟩ := A.exists_of_comm (A.W_le hcW) ht ht1 hc
  have hhW : t⁻¹ * (x * t * x⁻¹) ∈ W := W.mul_mem (W.inv_mem (A.T_le ht)) hcW
  have hhR : t⁻¹ * (x * t * x⁻¹) ∈ R := by
    have h1 : t⁻¹ * x * t ∈ R := by
      have := A.conj_mem_R (T.inv_mem ht) hx
      simpa using this
    have h2 : t⁻¹ * (x * t * x⁻¹) = (t⁻¹ * x * t) * x⁻¹ := by group
    rw [h2]
    exact R.mul_mem h1 (R.inv_mem hx)
  have hnt : n * t⁻¹ = t⁻¹ * n := A.N_comm hn (T.inv_mem ht)
  have h3 : t⁻¹ * t₀ = n⁻¹ * (t⁻¹ * (x * t * x⁻¹)) := by
    rw [hct]
    calc t⁻¹ * t₀ = n⁻¹ * (n * t⁻¹) * t₀ := by group
      _ = n⁻¹ * (t⁻¹ * n) * t₀ := by rw [hnt]
      _ = n⁻¹ * (t⁻¹ * (n * t₀)) := by group
  have h4 : t⁻¹ * t₀ ∈ W ⊓ R := by
    rw [h3]
    exact (W ⊓ R).mul_mem ((W ⊓ R).inv_mem (A.N_le_H hn)) ⟨hhW, hhR⟩
  have h5 : t⁻¹ * t₀ ∈ T ⊓ R := ⟨T.mul_mem (T.inv_mem ht) ht₀, h4.2⟩
  rw [A.inf_eq, Subgroup.mem_bot] at h5
  have ht0 : t₀ = t := by
    have : t₀ = t * (t⁻¹ * t₀) := by group
    rw [this, h5, mul_one]
  have hnZ : n ∈ W ⊓ Subgroup.centralizer (W : Set G) := by
    rw [A.center_eq]
    exact hn
  obtain ⟨w, hwW, hw⟩ := A.exists_conj_eq ht ht1 hnZ
  have hw' : w * t * w⁻¹ = x * t * x⁻¹ := by rw [hw, hct, ht0]
  have hcomm : (x⁻¹ * w) * t = t * (x⁻¹ * w) := by
    calc (x⁻¹ * w) * t = x⁻¹ * (w * t * w⁻¹) * w := by group
      _ = x⁻¹ * (x * t * x⁻¹) * w := by rw [hw']
      _ = t * (x⁻¹ * w) := by group
  have hxwS : x⁻¹ * w ∈ R ⊔ T := (R ⊔ T).mul_mem ((R ⊔ T).inv_mem hxS) (A.W_le hwW)
  have hxwW : x⁻¹ * w ∈ W := A.mem_W_of_comm hxwS ht ht1 hcomm
  have hxinvW : x⁻¹ ∈ W := by
    have : x⁻¹ = (x⁻¹ * w) * w⁻¹ := by group
    rw [this]
    exact W.mul_mem hxwW (W.inv_mem hwW)
  exact hxH ⟨W.inv_mem_iff.mp hxinvW, hx⟩

theorem comm_sq_ne_one {x t : G} (hx : x ∈ R) (hxH : x ∉ W ⊓ R) (ht : t ∈ T) (ht1 : t ≠ 1) :
    (t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹) ≠ 1 := by
  intro h1
  rw [A.comm_sq_eq hx ht] at h1
  refine A.not_comm_conj hx hxH ht ht1 ?_
  have h2 : ((x * t * x⁻¹) * t) * ((x * t * x⁻¹) * t) = 1 := by
    calc ((x * t * x⁻¹) * t) * ((x * t * x⁻¹) * t) = (x * t * x⁻¹) * t * (x * t * x⁻¹) * t := by
          group
      _ = 1 := h1
  have h3 : (x * t * x⁻¹) * t = ((x * t * x⁻¹) * t)⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [mul_inv_rev, A.inv_eq_self ht, A.conj_inv_eq ht] at h3
  exact h3

theorem comm_not_mem {x t : G} (hx : x ∈ R) (hxH : x ∉ W ⊓ R) (ht : t ∈ T) (ht1 : t ≠ 1) :
    t * x * t⁻¹ * x⁻¹ ∉ R ⊓ Subgroup.normalizer (T : Set G) := fun hp =>
  A.comm_sq_ne_one hx hxH ht ht1 (A.elem_N hp)

theorem gen {x : G} (hx : x ∈ R) (hxH : x ∉ W ⊓ R) {h : G} (hh : h ∈ W ⊓ R) :
    ∃ t ∈ T, ∃ z ∈ R ⊓ Subgroup.normalizer (T : Set G), h = z * (t * x * t⁻¹ * x⁻¹) := by
  let Φ : ↥T × ↥(R ⊓ Subgroup.normalizer (T : Set G)) → ↥(W ⊓ R) := fun p =>
    ⟨(p.2 : G) * ((p.1 : G) * x * (p.1 : G)⁻¹ * x⁻¹),
      (W ⊓ R).mul_mem (A.N_le_H p.2.2) (A.comm_mem_H hx p.1.2)⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨t, z⟩ ⟨t', z'⟩ hΦ
    have hΦ' : (z : G) * ((t : G) * x * (t : G)⁻¹ * x⁻¹) =
        (z' : G) * ((t' : G) * x * (t' : G)⁻¹ * x⁻¹) := congrArg Subtype.val hΦ
    have hΦ0 := hΦ'
    obtain ⟨s, hsT, hs⟩ : ∃ s ∈ T, (t : G) = s * t' :=
      ⟨(t : G) * (t' : G)⁻¹, T.mul_mem t.2 (T.inv_mem t'.2), by group⟩
    obtain ⟨c, hc, hmul⟩ := A.comm_mul hx hsT t'.2
    rw [hs, hmul] at hΦ'
    have h2 : (z : G) * c * (s * x * s⁻¹ * x⁻¹) = z' := by
      refine mul_right_cancel (b := (t' : G) * x * (t' : G)⁻¹ * x⁻¹) ?_
      calc (z : G) * c * (s * x * s⁻¹ * x⁻¹) * ((t' : G) * x * (t' : G)⁻¹ * x⁻¹)
          = (z : G) * (c * (s * x * s⁻¹ * x⁻¹) * ((t' : G) * x * (t' : G)⁻¹ * x⁻¹)) := by
            group
        _ = (z' : G) * ((t' : G) * x * (t' : G)⁻¹ * x⁻¹) := hΦ'
    have hcN : c ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
      rw [← A.center_eq]
      exact hc
    have hps : s * x * s⁻¹ * x⁻¹ ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
      have e : s * x * s⁻¹ * x⁻¹ = ((z : G) * c)⁻¹ * (z' : G) := by
        rw [← h2]
        group
      rw [e]
      exact (R ⊓ Subgroup.normalizer (T : Set G)).mul_mem
        ((R ⊓ Subgroup.normalizer (T : Set G)).inv_mem
          ((R ⊓ Subgroup.normalizer (T : Set G)).mul_mem z.2 hcN)) z'.2
    have hs1 : s = 1 := by
      by_contra hne
      exact A.comm_not_mem hx hxH hsT hne hps
    rw [hs1, one_mul] at hs
    have hz_eq : (z : G) = z' := by
      rw [hs] at hΦ0
      exact mul_right_cancel hΦ0
    exact Prod.ext (Subtype.ext hs) (Subtype.ext hz_eq)
  have hcard : Nat.card ↥(W ⊓ R) ≤ Nat.card (↥T × ↥(R ⊓ Subgroup.normalizer (T : Set G))) :=
    le_of_eq (by rw [Nat.card_prod, A.card_N_eq, A.card_H, sq])
  obtain ⟨⟨t, z⟩, hz⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨h, hh⟩
  exact ⟨(t : G), t.2, (z : G), z.2, (congrArg Subtype.val hz).symm⟩

theorem exists_not_mem_H : ∃ x ∈ R, x ∉ W ⊓ R := by
  by_contra hcon
  have h1 : (W ⊓ R).relIndex R = 1 :=
    Subgroup.relIndex_eq_one.mpr fun x hx => by
      by_contra hxH
      exact hcon ⟨x, hx, hxH⟩
  rw [A.relIndex_R] at h1
  omega

theorem omega_le {h : G} (hh : h ∈ W ⊓ R) (h2 : h ^ 2 = 1) :
    h ∈ R ⊓ Subgroup.normalizer (T : Set G) := by
  obtain ⟨x, hx, hxH⟩ := A.exists_not_mem_H
  obtain ⟨t, ht, z, hz, rfl⟩ := A.gen hx hxH hh
  by_cases ht1 : t = 1
  · subst ht1
    simpa using hz
  · exfalso
    have hp : (t * x * t⁻¹ * x⁻¹) ∈ W := (A.comm_mem_H hx ht).1
    have hzp : (z : G) * (t * x * t⁻¹ * x⁻¹) = (t * x * t⁻¹ * x⁻¹) * z := A.N_central hz hp
    have h3 : (z * (t * x * t⁻¹ * x⁻¹)) * (z * (t * x * t⁻¹ * x⁻¹)) =
        (t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹) := by
      calc (z * (t * x * t⁻¹ * x⁻¹)) * (z * (t * x * t⁻¹ * x⁻¹))
          = z * ((t * x * t⁻¹ * x⁻¹) * z) * (t * x * t⁻¹ * x⁻¹) := by group
        _ = z * (z * (t * x * t⁻¹ * x⁻¹)) * (t * x * t⁻¹ * x⁻¹) := by rw [hzp]
        _ = (z * z) * ((t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹)) := by group
        _ = (t * x * t⁻¹ * x⁻¹) * (t * x * t⁻¹ * x⁻¹) := by rw [A.elem_N hz, one_mul]
    have h4 : (z * (t * x * t⁻¹ * x⁻¹)) * (z * (t * x * t⁻¹ * x⁻¹)) = 1 := by
      rw [← sq]
      exact h2
    exact A.comm_sq_ne_one hx hxH ht ht1 (h3.symm.trans h4)

end Counting

theorem toCaseII5 [Finite G] {K R T W : Subgroup G} (A : AData R T W)
    (hT4 : 4 ≤ Nat.card ↥T) (hK : ((W ⊓ R).subgroupOf K).Normal) :
    CaseII5 K R T (W ⊓ R) where
  elem_T := ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (A.comm_T a a.2 b b.2),
    fun x hx => by rw [sq]; exact A.elem_T x hx⟩
  four_le := hT4
  H_le := inf_le_right
  relIndex_two := A.relIndex_R
  card_H := A.card_H
  pow_four := fun x hx => A.pow_four hx
  omega_le := fun x hx hx2 => A.omega_le hx hx2
  N_le := A.N_le_H
  N_central := fun n hn h hh => A.N_central hn hh.1
  elem_N := fun n hn => A.elem_N hn
  iso := by
    obtain ⟨e⟩ := A.iso
    exact ⟨(MulEquiv.subgroupCongr A.center_eq).symm.trans e⟩
  N_conj := fun r hr n hn => A.N_conj hr hn
  normal := hK
  gen := fun x hx hxH h hh => A.gen hx hxH hh
  comm_mem := fun x hx _ t ht => A.comm_mem_H hx ht
  comm_not_mem := fun x hx hxH t ht ht1 => A.comm_not_mem hx hxH ht ht1

end AData

end CFSG.CGT.PushingUpLit.SolKNA

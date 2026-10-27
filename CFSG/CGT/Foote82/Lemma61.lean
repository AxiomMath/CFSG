module

public import CFSG.CGT.Foote82.Setup
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem sub_one_pow_two_pow {R : Type*} [Ring R] (h2 : (2 : R) = 0) (x : R) (k : ℕ) :
    (x - 1) ^ 2 ^ k = x ^ 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsq : ∀ y : R, (y - 1) ^ 2 = y ^ 2 - 1 := fun y => by
      have : (y - 1) ^ 2 = y ^ 2 - 1 - 2 * (y - 1) := by noncomm_ring
      rw [this, h2, zero_mul, sub_zero]
    rw [pow_succ, pow_mul, pow_mul, ih, hsq]

private theorem sub_one_pow_eq_zero {s : GLV V} (hs : IsPGroup 2 (Subgroup.zpowers s)) :
    ∃ k : ℕ, ((s : Module.End (ZMod 2) V) - 1) ^ 2 ^ k = 0 := by
  obtain ⟨k, hk⟩ := hs ⟨s, Subgroup.mem_zpowers s⟩
  have hk' : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hvv : ∀ v : V, v + v = 0 := fun v => by
    have h2v : (2 : ZMod 2) • v = 0 := by
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_smul]
    rwa [two_smul] at h2v
  have h2 : (2 : Module.End (ZMod 2) V) = 0 := by
    ext v
    simp [two_nsmul, hvv]
  refine ⟨k, ?_⟩
  rw [sub_one_pow_two_pow h2, sub_eq_zero]
  have hpow := map_pow
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (R := ZMod 2) (M := V)) s (2 ^ k)
  rw [hk', map_one] at hpow
  exact hpow.symm

theorem commSpace_commSpace_top_of_perfect {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L) :
    commSpace L (commSpace L ⊤) = commSpace L ⊤ := by
  refine le_antisymm (commSpace_mono le_rfl le_top) ?_
  let K : Subgroup (GLV V) :=
    { carrier := {k | ∀ v, k v - v ∈ commSpace L (commSpace L ⊤)}
      mul_mem' := fun {a b} ha hb v => by
        have h := (commSpace L (commSpace L ⊤)).add_mem (ha (b v)) (hb v)
        rwa [sub_add_sub_cancel] at h
      one_mem' := fun v => by simp
      inv_mem' := fun {a} ha v => by
        have h := (commSpace L (commSpace L ⊤)).neg_mem (ha (a⁻¹ v))
        simpa using h }
  have hcomm : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g hg h hh v
    obtain ⟨u, rfl⟩ : ∃ u, v = h (g u) := ⟨g⁻¹ (h⁻¹ v), by simp⟩
    have e1 : (g * h * g⁻¹ * h⁻¹) (h (g u)) = g (h u) := by
      simp
    have e2 : g (h u) - h (g u) = (g (h u - u) - (h u - u)) - (h (g u - u) - (g u - u)) := by
      simp only [map_sub]
      abel
    show (g * h * g⁻¹ * h⁻¹) (h (g u)) - h (g u) ∈ commSpace L (commSpace L ⊤)
    rw [e1, e2]
    exact (commSpace L (commSpace L ⊤)).sub_mem
      (sub_mem_commSpace hg (sub_mem_commSpace hh Submodule.mem_top))
      (sub_mem_commSpace hh (sub_mem_commSpace hg Submodule.mem_top))
  rw [hperf] at hcomm
  exact commSpace_le_iff.2 fun l hl _ _ => hcomm hl _

private theorem apply_eq_zero_of_commSpace {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    (hirr : HasIrrTildeV L) {N : Module.End (ZMod 2) V} {k : ℕ} (hk : N ^ k = 0)
    (hNl : ∀ l ∈ L, ∀ v, N (l v) = l (N v)) : ∀ w ∈ commSpace L ⊤, N w = 0 := by
  have hirr' : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
  obtain ⟨hCW, hmin⟩ := hirr'
  have hNW : ∀ w ∈ commSpace L ⊤, N w ∈ commSpace L ⊤ := by
    have h : commSpace L ⊤ ≤ (commSpace L ⊤).comap N := by
      refine commSpace_le_iff.2 fun l hl u _ => ?_
      show N (l u - u) ∈ commSpace L ⊤
      rw [map_sub, hNl l hl]
      exact sub_mem_commSpace hl Submodule.mem_top
    exact fun w hw => h hw
  have hNC : ∀ c ∈ fixedSpace L ⊓ commSpace L ⊤, N c ∈ fixedSpace L ⊓ commSpace L ⊤ := by
    intro c hc
    refine ⟨fun l hl => ?_, hNW c hc.2⟩
    rw [← hNl l hl, hc.1 l hl]
  have hInv : Invariant L (commSpace L ⊤ ⊓ (fixedSpace L ⊓ commSpace L ⊤).comap N) := by
    intro l hl u hu
    refine ⟨?_, ?_⟩
    · have h := (commSpace L ⊤).add_mem hu.1 (sub_mem_commSpace hl (Submodule.mem_top : u ∈ ⊤))
      simpa using h
    · show N (l u) ∈ fixedSpace L ⊓ commSpace L ⊤
      have hNu : N u ∈ fixedSpace L ⊓ commSpace L ⊤ := hu.2
      rw [hNl l hl, hNu.1 l hl]
      exact hNu
  have hKC : fixedSpace L ⊓ commSpace L ⊤ ≤
      commSpace L ⊤ ⊓ (fixedSpace L ⊓ commSpace L ⊤).comap N :=
    fun c hc => ⟨hc.2, hNC c hc⟩
  rcases hmin _ hInv hKC inf_le_left with hKeq | hKeq
  · exfalso
    obtain ⟨w, hwW, hwC⟩ := SetLike.exists_of_lt hCW
    have key : ∀ j : ℕ, (N ^ j) w ∈ commSpace L ⊤ ∧
        (N ^ j) w ∉ fixedSpace L ⊓ commSpace L ⊤ := by
      intro j
      induction j with
      | zero => exact ⟨by simpa using hwW, by simpa using hwC⟩
      | succ j ih =>
        have hx : (N ^ (j + 1)) w = N ((N ^ j) w) := by
          rw [pow_succ', Module.End.mul_apply]
        rw [hx]
        refine ⟨hNW _ ih.1, fun hC => ih.2 ?_⟩
        rw [← hKeq]
        exact ⟨ih.1, hC⟩
    refine (key k).2 ?_
    rw [hk]
    exact Submodule.zero_mem _
  · have hNWC : ∀ w ∈ commSpace L ⊤, N w ∈ fixedSpace L ⊓ commSpace L ⊤ := by
      intro w hw
      have h : w ∈ commSpace L ⊤ ⊓ (fixedSpace L ⊓ commSpace L ⊤).comap N := by
        rw [hKeq]
        exact hw
      exact h.2
    have hle : commSpace L (commSpace L ⊤) ≤ LinearMap.ker N := by
      refine commSpace_le_iff.2 fun l hl u hu => ?_
      have hNu : N u ∈ fixedSpace L ⊓ commSpace L ⊤ := hNWC u hu
      rw [LinearMap.mem_ker, map_sub, hNl l hl, hNu.1 l hl, sub_self]
    intro w hw
    exact hle (by rwa [commSpace_commSpace_top_of_perfect hperf])

theorem lemma61 {L : Subgroup (GLV V)} {s : GLV V} (hperf : ⁅L, L⁆ = L) (hirr : HasIrrTildeV L)
    (hcomm : ∀ l ∈ L, l * s = s * l) (hs : IsPGroup 2 (Subgroup.zpowers s)) :
    (∀ l ∈ L, ∀ w ∈ commSpace (Subgroup.zpowers s) ⊤, l w = w) ∧
      commSpace L ⊤ ≤ fixedSpace (Subgroup.zpowers s) := by
  obtain ⟨k, hk⟩ := sub_one_pow_eq_zero hs
  have hNv : ∀ v, ((s : Module.End (ZMod 2) V) - 1) v = s v - v := fun v => by simp
  have hsl : ∀ l ∈ L, ∀ v, l (s v) = s (l v) := fun l hl v => by
    have := congrArg (fun f : GLV V => f v) (hcomm l hl)
    simpa using this
  have hNl : ∀ l ∈ L, ∀ v, ((s : Module.End (ZMod 2) V) - 1) (l v) =
      l (((s : Module.End (ZMod 2) V) - 1) v) := fun l hl v => by
    rw [hNv, hNv, map_sub, hsl l hl]
  have hker := apply_eq_zero_of_commSpace hperf hirr hk hNl
  have hfix : ∀ w ∈ commSpace L ⊤, ∀ t ∈ Subgroup.zpowers s, t w = w := by
    intro w hw t ht
    have hsw : s w = w := sub_eq_zero.1 ((hNv w).symm.trans (hker w hw))
    have hst : t ∈ MulAction.stabilizer (GLV V) w :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hsw) ht
    exact MulAction.mem_stabilizer_iff.1 hst
  refine ⟨fun l hl => ?_, fun w hw t ht => hfix w hw t ht⟩
  have hle : commSpace (Subgroup.zpowers s) ⊤ ≤
      LinearMap.eqLocus (l : V →ₗ[ZMod 2] V) LinearMap.id := by
    refine commSpace_le_iff.2 fun t ht u _ => ?_
    have hlt : l (t u) = t (l u) := by
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have hc : l * s ^ n = s ^ n * l := ((Commute.zpow_right (hcomm l hl) n)).eq
      have := congrArg (fun f : GLV V => f u) hc
      simpa using this
    have h1 : t (l u - u) = l u - u := hfix _ (sub_mem_commSpace hl Submodule.mem_top) t ht
    rw [map_sub] at h1
    have h2 : t (l u) = l u - u + t u := sub_eq_iff_eq_add.1 h1
    rw [LinearMap.mem_eqLocus]
    show l (t u - u) = t u - u
    rw [map_sub, hlt, h2]
    abel
  exact fun w hw => hle hw

theorem Setup6.lemma61 {G S L : Subgroup (GLV V)} (h : Setup6 G S L) {s : GLV V} (hs : s ∈ S) :
    (∀ l ∈ L, ∀ w ∈ commSpace (Subgroup.zpowers s) ⊤, l w = w) ∧
      commSpace L ⊤ ≤ fixedSpace (Subgroup.zpowers s) := by
  have hLC : L ≤ G ⊓ Subgroup.centralizer (S : Set (GLV V)) := h.component.1
  have hperf : ⁅L, L⁆ = L :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 h.component.2.2.1)
  refine _root_.CFSG.CGT.Foote82.lemma61 hperf h.irrTilde (fun l hl => ?_) ?_
  · exact ((Subgroup.mem_centralizer_iff.1 (hLC hl).2) s hs).symm
  · exact h.isPGroup.to_le (Subgroup.zpowers_le.2 hs)

end CFSG.CGT.Foote82

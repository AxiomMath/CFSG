module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.SylowCenters
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Bruhat
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.Defs

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

theorem ofNat_eq_mod_two_D4 {R : Type*} [AddGroupWithOne R] [CharP R 2] (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : R) = ((n % 2 : ℕ) : R) := by
  rw [← Nat.cast_ofNat, CharP.natCast_eq_natCast R 2]
  exact (Nat.mod_modEq _ _).symm

macro "triality_ring2" : tactic =>
  `(tactic| ((try simp only [CharTwo.neg_eq, CharTwo.sub_eq_add]) <;> ring_nf <;>
    (try simp only [ofNat_eq_mod_two_D4, Nat.reduceMod, Nat.cast_one, Nat.cast_zero, mul_one,
      mul_zero, one_mul, zero_mul, add_zero, zero_add, neg_zero])))

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

abbrev qComm (a b : d.Γ) : d.Γ := d.σ a * d.σ (d.σ b) + d.σ (d.σ a) * d.σ b

abbrev e₅Comm (a b : d.Γ) : d.Γ₀ := d.tr (a * d.σ a * d.σ (d.σ b))

abbrev e₆Comm (a b : d.Γ) : d.Γ₀ := d.tr (a * d.σ b * d.σ (d.σ b))

theorem coe_tr_of_Γ₀ (c : d.Γ₀) : (d.tr (c : d.Γ) : d.Γ) = c := by
  rw [coe_fixedTrace, apply_coe_fixedSubfield, apply_coe_fixedSubfield]
  triality_ring2

theorem nm_ne_zero_of_ne {a : d.Γ} (ha : a ≠ 0) : (d.nm a : d.Γ) ≠ 0 := by
  rw [coe_fixedNorm]
  exact mul_ne_zero (mul_ne_zero ha ((map_ne_zero d.σ).2 ha))
    ((map_ne_zero d.σ).2 ((map_ne_zero d.σ).2 ha))

theorem σ_div_eq_of_qComm {s c : d.Γ} (hs : s ≠ 0) (h : d.qComm s c = 0) :
    d.σ (c / s) = c / s := by
  set γ := c / s with hγ
  have hc : c = s * γ := by rw [hγ, mul_div_cancel₀ _ hs]
  have hs1 : d.σ s ≠ 0 := (map_ne_zero d.σ).2 hs
  have hs2 : d.σ (d.σ s) ≠ 0 := (map_ne_zero d.σ).2 hs1
  simp only [qComm, hc, map_mul] at h
  have h1 : d.σ s * d.σ (d.σ s) * (d.σ (d.σ γ) + d.σ γ) = 0 := by linear_combination h
  have h2 : d.σ (d.σ γ) + d.σ γ = 0 := (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hs1 hs2)
  have h4 : d.σ (d.σ γ) = d.σ γ := CharTwo.add_eq_zero.1 h2
  have h5 := congrArg d.σ h4
  rw [d.σ_cube, h4] at h5
  exact h5.symm

theorem eq_zero_of_comm_conds {s c e : d.Γ} (hs : s ≠ 0) (hQ : d.qComm s c = 0)
    (h5 : (d.e₅Comm s c : d.Γ) + d.tr (s * e) = 0) (hce : (d.tr (c * e) : d.Γ) = 0) :
    c = 0 ∧ (d.tr (s * e) : d.Γ) = 0 := by
  have hγ := d.σ_div_eq_of_qComm hs hQ
  set γ := c / s with hγdef
  have hc : c = s * γ := by rw [hγdef, mul_div_cancel₀ _ hs]
  set γ₀ : d.Γ₀ := ⟨γ, hγ⟩ with hγ₀
  have hσσγ : d.σ (d.σ γ) = γ := by rw [hγ, hγ]
  have hNmem : d.σ ((d.nm s : d.Γ) * γ) = (d.nm s : d.Γ) * γ := by
    rw [map_mul, apply_coe_fixedSubfield, hγ]
  have he5 : (d.e₅Comm s c : d.Γ) = (d.nm s : d.Γ) * γ := by
    have hx : s * d.σ s * d.σ (d.σ c) = (d.nm s : d.Γ) * γ := by
      rw [hc, map_mul, map_mul, hσσγ, coe_fixedNorm]
      ring
    have hfix : (d.nm s : d.Γ) * γ = ((d.nm s * γ₀ : d.Γ₀) : d.Γ) := rfl
    rw [e₅Comm, hx, hfix, d.coe_tr_of_Γ₀]
  have hse : (d.tr (s * e) : d.Γ) = (d.nm s : d.Γ) * γ := by
    rw [he5] at h5
    exact (CharTwo.add_eq_zero.1 h5).symm
  have hce' : (d.tr (c * e) : d.Γ) = γ * d.tr (s * e) := by
    rw [hc, show s * γ * e = (γ₀ : d.Γ) * (s * e) by rw [hγ₀]; ring, d.tr_smul]
  rw [hce', hse] at hce
  have hN := d.nm_ne_zero_of_ne hs
  have hγ0 : γ = 0 := by
    have : (d.nm s : d.Γ) * (γ * γ) = 0 := by linear_combination hce
    exact mul_self_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hN)
  refine ⟨by rw [hc, hγ0, mul_zero], by rw [hse, hγ0, mul_zero]⟩

@[expose] noncomputable def nfc (g : X) : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀ :=
  Function.invFun d.nf g

theorem nf_nfc {g : X} (hg : g ∈ d.S) : d.nf (d.nfc g) = g :=
  Function.invFun_eq (d.mem_S.1 hg)

theorem nfc_nf (a : d.Γ × d.Γ₀ × d.Γ × d.Γ × d.Γ₀ × d.Γ₀) : d.nfc (d.nf a) = a :=
  Function.leftInverse_invFun d.nf_injective a

theorem coord_mul_eq_add {A : Type*} [AddGroup A] {x : A → X} {N : Subgroup X} {c : X → A}
    (hc : ∀ a, ∀ n ∈ N, c (x a * n) = a) (hx : ∀ a a', (x (a + a'))⁻¹ * (x a * x a') ∈ N)
    (hN : ∀ a, x a ∈ normalizer (N : Set X)) {g g' : X} (hg : ∃ a, ∃ n ∈ N, x a * n = g)
    (hg' : ∃ a, ∃ n ∈ N, x a * n = g') : c (g * g') = c g + c g' := by
  obtain ⟨a, n, hn, rfl⟩ := hg
  obtain ⟨a', n', hn', rfl⟩ := hg'
  have hn'' : (x a')⁻¹ * n * x a' ∈ N := (mem_normalizer_iff''.1 (hN a') n).1 hn
  have e : x a * n * (x a' * n') =
      x (a + a') * ((x (a + a'))⁻¹ * (x a * x a') * ((x a')⁻¹ * n * x a') * n') := by group
  rw [e, hc _ _ (mul_mem (mul_mem (hx a a') hn'') hn'), hc _ _ hn, hc _ _ hn']

theorem nfc_x₁_mul {a : d.Γ} {n : X} (hn : n ∈ d.D) : (d.nfc (d.x₁ a * n)).1 = a := by
  obtain ⟨a₂, a₃, a₄, a₅, a₆, rfl⟩ := d.mem_D_coords hn
  rw [show d.x₁ a * d.nf (0, a₂, a₃, a₄, a₅, a₆) = d.nf (a, a₂, a₃, a₄, a₅, a₆) by
    simp only [nf_apply, d.x₁_zero, one_mul, mul_assoc], nfc_nf]

theorem nfc_fst_of_mem_D {g : X} (hg : g ∈ d.D) : (d.nfc g).1 = 0 := by
  simpa [d.x₁_zero] using d.nfc_x₁_mul (a := 0) hg

theorem nfc_fst_mul {g g' : X} (hg : g ∈ d.S) (hg' : g' ∈ d.S) :
    (d.nfc (g * g')).1 = (d.nfc g).1 + (d.nfc g').1 :=
  coord_mul_eq_add (c := fun g => (d.nfc g).1) (fun _ _ hn => d.nfc_x₁_mul hn)
    (fun a a' => by rw [d.x₁_add, inv_mul_cancel]; exact one_mem _)
    (fun a => d.S_le_normalizer_D (d.U₁_le_S (d.x₁_mem_U₁ a))) (d.mem_S_iff.1 hg)
    (d.mem_S_iff.1 hg')

theorem mem_D_of_nfc_fst {g : X} (hg : g ∈ d.S) (h : (d.nfc g).1 = 0) : g ∈ d.D := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hg
  rw [d.nfc_x₁_mul hn] at h
  rw [h, d.x₁_zero, one_mul]
  exact hn

theorem mem_D_iff_x₂_x₃ {g : X} : g ∈ d.D ↔ ∃ b c, ∃ w ∈ d.W, d.x₂ b * d.x₃ c * w = g := by
  constructor
  · intro hg
    obtain ⟨b, n, hn, rfl⟩ := d.mem_D_iff.1 hg
    obtain ⟨c, w, hw, rfl⟩ := d.mem_F_iff.1 hn
    exact ⟨b, c, w, hw, by rw [mul_assoc]⟩
  · rintro ⟨b, c, w, hw, rfl⟩
    exact mul_mem (mul_mem (d.x₂_mem_D b) (d.F_le_D (d.x₃_mem_F c))) (d.F_le_D (d.W_le_F hw))

theorem mem_M_iff_x₁_x₃ {g : X} : g ∈ d.M ↔ ∃ a c, ∃ w ∈ d.W, d.x₁ a * d.x₃ c * w = g := by
  constructor
  · intro hg
    obtain ⟨a, n, hn, rfl⟩ := d.mem_M_iff.1 hg
    obtain ⟨c, w, hw, rfl⟩ := d.mem_F_iff.1 hn
    exact ⟨a, c, w, hw, by rw [mul_assoc]⟩
  · rintro ⟨a, c, w, hw, rfl⟩
    exact mul_mem (mul_mem (d.x₁_mem_M a) (d.F_le_M (d.x₃_mem_F c))) (d.F_le_M (d.W_le_F hw))

theorem nfc_x₂_x₃_mul {b : d.Γ₀} {c : d.Γ} {w : X} (hw : w ∈ d.W) :
    (d.nfc (d.x₂ b * d.x₃ c * w)).2.1 = b ∧ (d.nfc (d.x₂ b * d.x₃ c * w)).2.2.1 = c := by
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hw
  rw [show d.x₂ b * d.x₃ c * d.nf (0, 0, 0, a₄, a₅, a₆) = d.nf (0, b, c, a₄, a₅, a₆) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul, mul_assoc], nfc_nf]
  exact ⟨rfl, rfl⟩

theorem nfc_x₁_x₃_mul {a c : d.Γ} {w : X} (hw : w ∈ d.W) :
    (d.nfc (d.x₁ a * d.x₃ c * w)).1 = a ∧ (d.nfc (d.x₁ a * d.x₃ c * w)).2.1 = 0 ∧
      (d.nfc (d.x₁ a * d.x₃ c * w)).2.2.1 = c := by
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hw
  rw [show d.x₁ a * d.x₃ c * d.nf (0, 0, 0, a₄, a₅, a₆) = d.nf (a, 0, c, a₄, a₅, a₆) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul, mul_one, mul_assoc], nfc_nf]
  exact ⟨rfl, rfl, rfl⟩

theorem nfc_bc_mul {g g' : X} (hg : g ∈ d.D) (hg' : g' ∈ d.D) :
    ((d.nfc (g * g')).2.1, (d.nfc (g * g')).2.2.1) =
      ((d.nfc g).2.1, (d.nfc g).2.2.1) + ((d.nfc g').2.1, (d.nfc g').2.2.1) := by
  have key := coord_mul_eq_add (x := fun p : d.Γ₀ × d.Γ => d.x₂ p.1 * d.x₃ p.2) (N := d.W)
    (c := fun g => ((d.nfc g).2.1, (d.nfc g).2.2.1))
    (fun p _ hn => Prod.ext (d.nfc_x₂_x₃_mul hn).1 (d.nfc_x₂_x₃_mul hn).2)
    (fun p p' => by
      have e : (d.x₂ (p + p').1 * d.x₃ (p + p').2)⁻¹ * (d.x₂ p.1 * d.x₃ p.2 *
          (d.x₂ p'.1 * d.x₃ p'.2)) = 1 := by
        rw [Prod.fst_add, Prod.snd_add, d.x₂_add, d.x₃_add]
        rw [show d.x₂ p.1 * d.x₃ p.2 * (d.x₂ p'.1 * d.x₃ p'.2) =
          d.x₂ p.1 * (d.x₃ p.2 * d.x₂ p'.1) * d.x₃ p'.2 by group,
          ← (d.commute₂₃ p'.1 p.2).eq]
        group
      rw [e]
      exact one_mem _)
    (fun p => mul_mem (d.S_le_normalizer_W (d.U₂_le_S (d.x₂_mem_U₂ p.1)))
      (d.S_le_normalizer_W (d.U₃_le_S (d.x₃_mem_U₃ p.2))))
    (by obtain ⟨b, c, w, hw, h⟩ := d.mem_D_iff_x₂_x₃.1 hg; exact ⟨(b, c), w, hw, h⟩)
    (by obtain ⟨b, c, w, hw, h⟩ := d.mem_D_iff_x₂_x₃.1 hg'; exact ⟨(b, c), w, hw, h⟩)
  exact key

theorem mul_mul_inv_eq_of_commute {G : Type*} [Group G] {a b : G} (h : Commute a b) :
    a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]

theorem nfc_ac_mul {g g' : X} (hg : g ∈ d.M) (hg' : g' ∈ d.M) :
    ((d.nfc (g * g')).1, (d.nfc (g * g')).2.2.1) =
      ((d.nfc g).1, (d.nfc g).2.2.1) + ((d.nfc g').1, (d.nfc g').2.2.1) := by
  have key := coord_mul_eq_add (x := fun p : d.Γ × d.Γ => d.x₁ p.1 * d.x₃ p.2) (N := d.W)
    (c := fun g => ((d.nfc g).1, (d.nfc g).2.2.1))
    (fun p _ hn => Prod.ext (d.nfc_x₁_x₃_mul hn).1 (d.nfc_x₁_x₃_mul hn).2.2)
    (fun p p' => by
      have e : (d.x₁ (p + p').1 * d.x₃ (p + p').2)⁻¹ * (d.x₁ p.1 * d.x₃ p.2 *
          (d.x₁ p'.1 * d.x₃ p'.2)) =
          (d.x₃ p'.2)⁻¹ * ⁅(d.x₃ p.2)⁻¹, (d.x₁ p'.1)⁻¹⁆ * d.x₃ p'.2 := by
        rw [Prod.fst_add, Prod.snd_add, d.x₁_add, d.x₃_add, commutatorElement_def]
        group
      rw [e, d.x₃_inv p.2, d.x₁_inv]
      exact (mem_normalizer_iff''.1 (d.S_le_normalizer_W (d.U₃_le_S (d.x₃_mem_U₃ p'.2))) _).1
        (commutatorElement_mem_comm.1 (d.comm₁₃_mem_W _ _)))
    (fun p => mul_mem (d.S_le_normalizer_W (d.U₁_le_S (d.x₁_mem_U₁ p.1)))
      (d.S_le_normalizer_W (d.U₃_le_S (d.x₃_mem_U₃ p.2))))
    (by obtain ⟨a, c, w, hw, h⟩ := d.mem_M_iff_x₁_x₃.1 hg; exact ⟨(a, c), w, hw, h⟩)
    (by obtain ⟨a, c, w, hw, h⟩ := d.mem_M_iff_x₁_x₃.1 hg'; exact ⟨(a, c), w, hw, h⟩)
  exact key

theorem commutator_W_W_eq_bot : ⁅d.W, d.W⁆ = ⊥ := by
  refine le_bot_iff.1 (commutator_sup_right_le (le_normalizer_bot_subgroup _)
    (le_normalizer_bot_subgroup _) d.commutator_W_U₄.le ?_)
  exact (commutator_mono_left (d.W_le_F.trans d.F_le_M)).trans d.commutator_M_Y.le

theorem mul_comm_of_mem_W {w w' : X} (hw : w ∈ d.W) (hw' : w' ∈ d.W) : w * w' = w' * w := by
  have h := commutator_mem_commutator hw hw'
  rw [d.commutator_W_W_eq_bot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem mul_self_eq_one_of_mem_W {w : X} (hw : w ∈ d.W) : w * w = 1 := by
  obtain ⟨a₄, a₅, a₆, rfl⟩ := d.mem_W_coords hw
  simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul]
  have h45 := (d.commute₄₅ a₄ a₅).eq
  have h46 := (d.commute₄₆ a₄ a₆).eq
  have h56 := (d.commute₅₆ a₅ a₆).eq
  calc d.x₄ a₄ * d.x₅ a₅ * d.x₆ a₆ * (d.x₄ a₄ * d.x₅ a₅ * d.x₆ a₆) =
      d.x₄ a₄ * d.x₅ a₅ * (d.x₆ a₆ * d.x₄ a₄) * d.x₅ a₅ * d.x₆ a₆ := by group
    _ = d.x₄ a₄ * (d.x₅ a₅ * d.x₄ a₄) * (d.x₆ a₆ * d.x₅ a₅) * d.x₆ a₆ := by
        rw [← h46]; group
    _ = d.x₄ a₄ * d.x₄ a₄ * (d.x₅ a₅ * d.x₅ a₅) * (d.x₆ a₆ * d.x₆ a₆) := by
        rw [← h45, ← h56]; group
    _ = 1 := by rw [d.x₄_mul_self, d.x₅_mul_self, d.x₆_mul_self]; group

theorem comm_eq_one_of_M_Y {x y : X} (hx : x ∈ d.M) (hy : y ∈ d.Y) : ⁅x, y⁆ = 1 := by
  have h := commutator_mem_commutator hx hy
  rwa [d.commutator_M_Y, mem_bot] at h

theorem commutatorElement_mul_right_conj {G : Type*} [Group G] (g h k : G) :
    ⁅g, h * k⁆ = ⁅g, h⁆ * (h * ⁅g, k⁆ * h⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem comm_x₁_F (a c e : d.Γ) {y : X} (hy : y ∈ d.Y) :
    ⁅d.x₁ a, d.x₃ c * d.x₄ e * y⁆ =
      d.x₄ (d.qComm a c) * d.x₅ (d.e₅Comm a c + d.tr (a * e)) * d.x₆ (d.e₆Comm a c) := by
  have h1 : ⁅d.x₁ a, d.x₄ e * y⁆ = d.x₅ (d.tr (a * e)) := by
    rw [commutatorElement_mul_right_conj, d.comm₁₄, d.comm_eq_one_of_M_Y (d.x₁_mem_M a) hy,
      mul_one, mul_inv_cancel, mul_one]
  rw [mul_assoc, commutatorElement_mul_right_conj, h1, mul_mul_inv_eq_of_commute (d.commute₃₅ c _),
    d.comm₁₃, d.x₅_add]
  change d.x₄ (d.qComm a c) * d.x₅ (d.e₅Comm a c) * d.x₆ (d.e₆Comm a c) * d.x₅ (d.tr (a * e)) = _
  rw [mul_assoc _ (d.x₆ _), ← (d.commute₅₆ _ _).eq]
  group

theorem F_elt_mul_self (c e : d.Γ) {y : X} (hy : y ∈ d.Y) :
    d.x₃ c * d.x₄ e * y * (d.x₃ c * d.x₄ e * y) = d.x₆ (d.tr (c * e)) := by
  have hw : d.x₄ e * y ∈ d.W := mul_mem (d.x₄_mem_W e) (d.Y_le_W hy)
  have h1 : ⁅d.x₃ c, d.x₄ e * y⁆ = d.x₆ (d.tr (c * e)) := by
    rw [commutatorElement_mul_right_conj, d.comm₃₄,
      d.comm_eq_one_of_M_Y (d.F_le_M (d.x₃_mem_F c)) hy, mul_one, mul_inv_cancel, mul_one]
  rw [mul_assoc (d.x₃ c), mul_mul_self_eq_commutatorElement (d.x₃_mul_self c), h1,
    d.mul_self_eq_one_of_mem_W hw, mul_one]

theorem comm_D_W (b : d.Γ₀) (c : d.Γ) {w : X} (hw : w ∈ d.W) (e : d.Γ) (f g : d.Γ₀) :
    ⁅d.x₂ b * d.x₃ c * w, d.x₄ e * d.x₅ f * d.x₆ g⁆ = d.x₆ (d.tr (c * e) + b * f) := by
  have hz : d.x₄ e * d.x₅ f * d.x₆ g ∈ d.W :=
    mul_mem (mul_mem (d.x₄_mem_W e) (d.x₅_mem_W f)) (d.x₆_mem_W g)
  have hy : d.x₅ f * d.x₆ g ∈ d.Y := mul_mem (d.x₅_mem_Y f) (d.x₆_mem_Y g)
  have hwz : ⁅w, d.x₄ e * d.x₅ f * d.x₆ g⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2 (d.mul_comm_of_mem_W hw hz)
  have h3 : ⁅d.x₃ c, d.x₄ e * d.x₅ f * d.x₆ g⁆ = d.x₆ (d.tr (c * e)) := by
    rw [mul_assoc, commutatorElement_mul_right_conj, d.comm₃₄,
      d.comm_eq_one_of_M_Y (d.F_le_M (d.x₃_mem_F c)) hy, mul_one, mul_inv_cancel, mul_one]
  have h25 : ⁅d.x₂ b, d.x₅ f * d.x₆ g⁆ = d.x₆ (b * f) := by
    rw [commutatorElement_mul_right_conj, d.comm₂₅,
      commutatorElement_eq_one_iff_commute.2 (d.commute₂₆ b g), mul_one, mul_inv_cancel, mul_one]
  have h2 : ⁅d.x₂ b, d.x₄ e * d.x₅ f * d.x₆ g⁆ = d.x₆ (b * f) := by
    rw [mul_assoc, commutatorElement_mul_right_conj, h25,
      commutatorElement_eq_one_iff_commute.2 (d.commute₂₄ b e), one_mul,
      mul_mul_inv_eq_of_commute (d.commute₄₆ e _)]
  rw [commutatorElement_mul_left_eq_conj_mul, hwz, mul_one, mul_inv_cancel, one_mul,
    commutatorElement_mul_left_eq_conj_mul, h3, h2, mul_mul_inv_eq_of_commute (d.commute₂₆ b _),
    ← d.x₆_add]

theorem card_span_mul_card_orth_eq {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [Module.Finite F V] (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (S : AddSubgroup V) :
    Nat.card (Submodule.span F (S : Set V)) * Nat.card {z : V // ∀ s ∈ S, B s z = 0} =
      Nat.card V := by
  classical
  have : Finite V := Module.finite_of_finite F
  set W := Submodule.span F (S : Set V) with hW
  have hD : ∀ z : V, (∀ s ∈ S, B s z = 0) ↔ z ∈ B.orthogonal W := by
    intro z
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h n hn
      induction hn using Submodule.span_induction with
      | mem x hx => exact h x hx
      | zero => simp
      | add x y _ _ hx hy =>
        change B x z = 0 at hx
        change B y z = 0 at hy
        rw [map_add, LinearMap.add_apply, hx, hy, add_zero]
      | smul c x _ hx =>
        change B (c • x) z = 0
        change B x z = 0 at hx
        rw [map_smul, LinearMap.smul_apply, hx, smul_zero]
    · intro h s hs
      exact h s (Submodule.subset_span hs)
  have e1 : Nat.card {z : V // ∀ s ∈ S, B s z = 0} = Nat.card (B.orthogonal W) :=
    Nat.card_congr (Equiv.subtypeEquivRight hD)
  have hfin := LinearMap.BilinForm.finrank_orthogonal hB W
  have hle : Module.finrank F W ≤ Module.finrank F V := Submodule.finrank_le W
  rw [e1, Module.natCard_eq_pow_finrank (K := F) (V := W),
    Module.natCard_eq_pow_finrank (K := F) (V := B.orthogonal W),
    Module.natCard_eq_pow_finrank (K := F) (V := V), ← pow_add, hfin]
  congr 1
  omega

theorem card_mul_card_bilinOrth_le {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
    [Module F V] [Module.Finite F V] (B : LinearMap.BilinForm F V) (hB : B.Nondegenerate)
    (S : AddSubgroup V) :
    Nat.card S * Nat.card {z : V // ∀ s ∈ S, B s z = 0} ≤ Nat.card V := by
  have : Finite V := Module.finite_of_finite F
  refine le_trans (Nat.mul_le_mul_right _ ?_) (card_span_mul_card_orth_eq B hB S).le
  exact Nat.card_le_card_of_injective (fun s => ⟨s, Submodule.subset_span s.2⟩)
    fun a b h => Subtype.ext (congrArg Subtype.val h :)

theorem card_eq_card_range_mul_card_ker {G H : Type*} [Group G] [Finite G] [Group H]
    (φ : G →* H) : Nat.card G = Nat.card φ.range * Nat.card φ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]

theorem card_toAddSubgroup'_eq {A : Type*} [AddCommGroup A] (T : Subgroup (Multiplicative A)) :
    Nat.card (Subgroup.toAddSubgroup' T) = Nat.card T :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd (fun _ => Iff.rfl))

theorem tr_add_eq_add (a b : d.Γ) : d.tr (a + b) = d.tr a + d.tr b := by
  apply Subtype.ext
  simp only [coe_fixedTrace, map_add, Subfield.coe_add]
  ring

@[expose] noncomputable def trBilin : LinearMap.BilinForm d.Γ₀ d.Γ :=
  LinearMap.mk₂ d.Γ₀ (fun x y => d.tr (x * y))
    (fun x x' y => by rw [add_mul, d.tr_add_eq_add])
    (fun l x y => Subtype.ext (by
      rw [Algebra.smul_def, smul_eq_mul, Subfield.coe_mul, ← d.tr_smul, mul_assoc]; rfl))
    (fun x y y' => by rw [mul_add, d.tr_add_eq_add])
    (fun l x y => Subtype.ext (by
      rw [Algebra.smul_def, smul_eq_mul, Subfield.coe_mul, ← d.tr_smul, mul_left_comm]; rfl))

theorem trBilin_apply (x y : d.Γ) : d.trBilin x y = d.tr (x * y) := rfl

theorem trBilin_nondegenerate : d.trBilin.Nondegenerate :=
  ⟨fun x hx => d.eq_zero_of_forall_tr_mul hx,
    fun y hy => d.eq_zero_of_forall_tr_mul fun b => by rw [mul_comm]; exact hy b⟩

@[expose] noncomputable def pairBilin : LinearMap.BilinForm d.Γ₀ (d.Γ₀ × d.Γ) :=
  (LinearMap.mul d.Γ₀ d.Γ₀).compl₁₂ (LinearMap.fst _ _ _) (LinearMap.fst _ _ _) +
    d.trBilin.compl₁₂ (LinearMap.snd _ _ _) (LinearMap.snd _ _ _)

theorem pairBilin_apply (x y : d.Γ₀ × d.Γ) : d.pairBilin x y = x.1 * y.1 + d.tr (x.2 * y.2) :=
  rfl

theorem pairBilin_nondegenerate : d.pairBilin.Nondegenerate := by
  have h0 : d.tr 0 = 0 := Subtype.ext (by rw [coe_fixedTrace]; simp)
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h1 := hx (1, 0)
    rw [pairBilin_apply, mul_zero, mul_one, h0, add_zero] at h1
    exact Prod.ext h1 (d.eq_zero_of_forall_tr_mul fun t => by
      have := hx (0, t)
      rwa [pairBilin_apply, mul_zero, zero_add] at this)
  · have h1 := hy (1, 0)
    rw [pairBilin_apply, zero_mul, one_mul, h0, add_zero] at h1
    exact Prod.ext h1 (d.eq_zero_of_forall_tr_mul fun t => by
      have := hy (0, t)
      rwa [pairBilin_apply, zero_mul, zero_add, mul_comm] at this)

theorem eq_nf_of_mem_D {g : X} (hg : g ∈ d.D) : g = d.x₂ (d.nfc g).2.1 * d.x₃ (d.nfc g).2.2.1 *
    (d.x₄ (d.nfc g).2.2.2.1 * d.x₅ (d.nfc g).2.2.2.2.1 * d.x₆ (d.nfc g).2.2.2.2.2) := by
  conv_lhs => rw [← d.nf_nfc (d.D_le_S hg)]
  rw [nf_apply, d.nfc_fst_of_mem_D hg, d.x₁_zero, one_mul]
  group

theorem nfc_one : d.nfc 1 = 0 := by
  rw [show (1 : X) = d.nf (0, 0, 0, 0, 0, 0) by simp [nf_apply, d.x₁_zero, d.x₂_zero,
    d.x₃_zero, d.x₄_zero, d.x₅_zero, d.x₆_zero], nfc_nf]
  rfl

theorem yamada_3_11_1 {A : Subgroup X} (hAD : A ≤ d.D)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ q ^ 5 := by
  classical
  have := d.finite
  let ψ : A →* Multiplicative (d.Γ₀ × d.Γ) :=
    { toFun := fun g => Multiplicative.ofAdd ((d.nfc g).2.1, (d.nfc g).2.2.1)
      map_one' := by
        change Multiplicative.ofAdd ((d.nfc 1).2.1, (d.nfc 1).2.2.1) = 1
        rw [d.nfc_one]
        rfl
      map_mul' := fun g g' => by
        change Multiplicative.ofAdd ((d.nfc (g * g')).2.1, (d.nfc (g * g')).2.2.1) = _
        rw [d.nfc_bc_mul (hAD g.2) (hAD g'.2)]
        rfl }
  have hψ : ∀ g : A, Multiplicative.toAdd (ψ g) = ((d.nfc g).2.1, (d.nfc g).2.2.1) := fun _ => rfl
  set T₁ := Subgroup.toAddSubgroup' ψ.range with hT₁
  have hcard := card_eq_card_range_mul_card_ker ψ
  rw [← card_toAddSubgroup'_eq] at hcard
  have hker : ∀ x : ψ.ker, (d.nfc x).2.1 = 0 ∧ (d.nfc x).2.2.1 = 0 := by
    intro x
    have h := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 x.2)
    rw [hψ] at h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  have horth : ∀ x : ψ.ker, ∀ t ∈ T₁,
      d.pairBilin t ((d.nfc x).2.2.2.2.1, (d.nfc x).2.2.2.1) = 0 := by
    intro x t ht
    rw [Subgroup.mem_toAddSubgroup'] at ht
    obtain ⟨y, hy⟩ := ht
    have hy' := congrArg Multiplicative.toAdd hy
    rw [hψ, toAdd_ofAdd] at hy'
    have hx := d.eq_nf_of_mem_D (hAD x.1.2)
    rw [(hker x).1, (hker x).2, d.x₂_zero, d.x₃_zero, one_mul, one_mul] at hx
    have hyD := d.eq_nf_of_mem_D (hAD y.2)
    have hc := hcomm y y.2 x x.1.2
    rw [← commutatorElement_eq_one_iff_mul_comm, hyD, hx, d.comm_D_W _ _ (mul_mem (mul_mem
      (d.x₄_mem_W _) (d.x₅_mem_W _)) (d.x₆_mem_W _)), d.x₆_eq_one_iff] at hc
    rw [← hy', pairBilin_apply, add_comm]
    exact hc
  let F : ψ.ker → {z : d.Γ₀ × d.Γ // ∀ t ∈ T₁, d.pairBilin t z = 0} × d.Γ₀ := fun x =>
    (⟨((d.nfc x).2.2.2.2.1, (d.nfc x).2.2.2.1), fun t ht => horth x t ht⟩, (d.nfc x).2.2.2.2.2)
  have hF : Function.Injective F := by
    intro x x' hxx
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxx
    obtain ⟨⟨he, hd⟩, hf⟩ := hxx
    have h1 := d.nf_nfc (d.D_le_S (hAD x.1.2))
    have h2 := d.nf_nfc (d.D_le_S (hAD x'.1.2))
    have hco : d.nfc (x : X) = d.nfc (x' : X) := by
      refine Prod.ext ((d.nfc_fst_of_mem_D (hAD x.1.2)).trans
        (d.nfc_fst_of_mem_D (hAD x'.1.2)).symm) (Prod.ext ((hker x).1.trans (hker x').1.symm)
        (Prod.ext ((hker x).2.trans (hker x').2.symm) (Prod.ext hd (Prod.ext he hf))))
    apply Subtype.ext; apply Subtype.ext
    rw [← h1, ← h2, hco]
  have hinj := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod] at hinj
  have hA := card_mul_card_bilinOrth_le d.pairBilin d.pairBilin_nondegenerate T₁
  rw [Nat.card_prod, d.card_Γ₀, d.card_Γ] at hA
  rw [d.card_Γ₀] at hinj
  rw [hcard]
  calc Nat.card T₁ * Nat.card ψ.ker ≤ Nat.card T₁ *
        (Nat.card {z : d.Γ₀ × d.Γ // ∀ t ∈ T₁, d.pairBilin t z = 0} * q) :=
        Nat.mul_le_mul_left _ hinj
    _ = Nat.card T₁ * Nat.card {z : d.Γ₀ × d.Γ // ∀ t ∈ T₁, d.pairBilin t z = 0} * q := by ring
    _ ≤ q * q ^ 3 * q := Nat.mul_le_mul_right _ hA
    _ = q ^ 5 := by ring

theorem mem_W_of_commute_x₁_mul {s : d.Γ} (hs : s ≠ 0) {g n : X} (hg : g ∈ d.D) (hn : n ∈ d.D)
    (hc : d.x₁ s * g * n = n * (d.x₁ s * g)) (hsq : n * n = 1) :
    n ∈ d.W ∧ (d.tr (s * (d.nfc n).2.2.2.1) : d.Γ) = 0 := by
  have hc1 : ⁅d.x₁ s * g, n⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 hc
  have hgnV : ⁅g, n⁆ ∈ d.V := d.commutator_D_D (commutator_mem_commutator hg hn)
  have hx₁ : d.x₁ s ∈ d.S := d.U₁_le_S (d.x₁_mem_U₁ s)
  have hW : ⁅d.x₁ s, n⁆ ∈ d.W := by
    rw [← commutatorElement_mul_mem_iff (d.S_le_normalizer_W hx₁)
      (d.Y_le_W (d.V_le_Y hgnV)), hc1]
    exact one_mem _
  have hnD := d.eq_nf_of_mem_D hn
  set b := (d.nfc n).2.1
  set c := (d.nfc n).2.2.1
  set e := (d.nfc n).2.2.2.1
  set f := (d.nfc n).2.2.2.2.1
  set h := (d.nfc n).2.2.2.2.2
  have hb : b = 0 := by
    rw [hnD, mul_assoc, commutatorElement_mul_right_conj] at hW
    have h2 : d.x₂ b * ⁅d.x₁ s, d.x₃ c * (d.x₄ e * d.x₅ f * d.x₆ h)⁆ * (d.x₂ b)⁻¹ ∈ d.W :=
      (mem_normalizer_iff.1 (d.S_le_normalizer_W (d.U₂_le_S (d.x₂_mem_U₂ b))) _).1
        (d.commutator_S_F (commutator_mem_commutator hx₁ (mul_mem (d.x₃_mem_F c)
          (d.W_le_F (mul_mem (mul_mem (d.x₄_mem_W e) (d.x₅_mem_W f)) (d.x₆_mem_W h))))))
    rw [mul_mem_cancel_right h2, d.comm₁₂, mul_assoc,
      mul_mem_cancel_right (mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)), d.x₃_mem_W_iff] at hW
    exact Subtype.ext ((mul_eq_zero.1 hW).resolve_left hs)
  have hy : d.x₅ f * d.x₆ h ∈ d.Y := mul_mem (d.x₅_mem_Y f) (d.x₆_mem_Y h)
  have hn' : n = d.x₃ c * d.x₄ e * (d.x₅ f * d.x₆ h) := by
    rw [hnD, hb, d.x₂_zero, one_mul]
    group
  have hform := d.comm_x₁_F s c e hy
  rw [← hn'] at hform
  have hY : ⁅d.x₁ s, n⁆ ∈ d.Y := by
    rw [← commutatorElement_mul_mem_iff (d.S_le_normalizer_Y hx₁) (d.V_le_Y hgnV), hc1]
    exact one_mem _
  rw [hform, mul_assoc, mul_mem_cancel_right (mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)),
    d.x₄_mem_Y_iff] at hY
  have hV : ⁅d.x₁ s, n⁆ ∈ d.V := by
    rw [← commutatorElement_mul_mem_iff (d.S_le_normalizer_V hx₁) hgnV, hc1]
    exact one_mem _
  rw [hform, hY, d.x₄_zero, one_mul, mul_mem_cancel_right (d.x₆_mem_V _), d.x₅_mem_V_iff] at hV
  have hsq' := hsq
  rw [hn', d.F_elt_mul_self c e hy, d.x₆_eq_one_iff] at hsq'
  obtain ⟨hc0, hse⟩ := d.eq_zero_of_comm_conds hs hY (by
    have := congrArg Subtype.val hV
    rwa [Subfield.coe_add] at this) (by rw [hsq']; rfl)
  refine ⟨?_, hse⟩
  rw [hn', hc0, d.x₃_zero, one_mul]
  exact mul_mem (d.x₄_mem_W e) (d.Y_le_W hy)

theorem eq_x₁_mul_of_mem_S {g : X} (hg : g ∈ d.S) : ∃ n ∈ d.D, g = d.x₁ (d.nfc g).1 * n := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hg
  exact ⟨n, hn, by rw [d.nfc_x₁_mul hn]⟩

theorem card_le_of_elementary_le_S {E : Subgroup X} (hES : E ≤ d.S)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ q ^ 5 := by
  classical
  have := d.finite
  let φ : E →* Multiplicative d.Γ :=
    { toFun := fun g => Multiplicative.ofAdd (d.nfc g).1
      map_one' := by
        change Multiplicative.ofAdd (d.nfc 1).1 = 1
        rw [d.nfc_one]
        rfl
      map_mul' := fun g g' => by
        change Multiplicative.ofAdd (d.nfc (g * g')).1 = _
        rw [d.nfc_fst_mul (hES g.2) (hES g'.2)]
        rfl }
  have hφ : ∀ g : E, Multiplicative.toAdd (φ g) = (d.nfc g).1 := fun _ => rfl
  set SE := Subgroup.toAddSubgroup' φ.range with hSE
  have hcard := card_eq_card_range_mul_card_ker φ
  rw [← card_toAddSubgroup'_eq] at hcard
  have hkerD : ∀ x : φ.ker, (x : X) ∈ d.D := fun x => by
    have h := congrArg Multiplicative.toAdd (MonoidHom.mem_ker.1 x.2)
    rw [hφ] at h
    exact d.mem_D_of_nfc_fst (hES x.1.2) h
  have hmemSE : ∀ s : d.Γ, s ∈ SE ↔ ∃ y : E, (d.nfc y).1 = s := by
    intro s
    rw [Subgroup.mem_toAddSubgroup']
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← hφ, hy, toAdd_ofAdd]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  by_cases hS : ∃ s ∈ SE, s ≠ 0
  · obtain ⟨s₀, hs₀SE, hs₀⟩ := hS
    have hcond : ∀ x : φ.ker, (x : X) ∈ d.W ∧ ∀ s ∈ SE, d.trBilin s (d.nfc x).2.2.2.1 = 0 := by
      intro x
      have key : ∀ s ∈ SE, s ≠ 0 →
          (x : X) ∈ d.W ∧ (d.tr (s * (d.nfc (x : X)).2.2.2.1) : d.Γ) = 0 := by
        intro s hs hs0
        obtain ⟨y, hy⟩ := (hmemSE s).1 hs
        obtain ⟨n, hn, hyn⟩ := d.eq_x₁_mul_of_mem_S (hES y.2)
        rw [hy] at hyn
        have hc := hcomm _ y.2 _ x.1.2
        rw [hyn] at hc
        exact d.mem_W_of_commute_x₁_mul hs0 hn (hkerD x) hc (hsq _ x.1.2)
      refine ⟨(key s₀ hs₀SE hs₀).1, fun s hs => ?_⟩
      by_cases hs0 : s = 0
      · rw [hs0, map_zero, LinearMap.zero_apply]
      · exact Subtype.ext (key s hs hs0).2
    let F : φ.ker → {e : d.Γ // ∀ s ∈ SE, d.trBilin s e = 0} × d.Γ₀ × d.Γ₀ := fun x =>
      (⟨(d.nfc x).2.2.2.1, (hcond x).2⟩, (d.nfc x).2.2.2.2.1, (d.nfc x).2.2.2.2.2)
    have hF : Function.Injective F := by
      intro x x' hxx
      simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at hxx
      obtain ⟨he, hf, hh⟩ := hxx
      obtain ⟨a₄, a₅, a₆, hx⟩ := d.mem_W_coords (hcond x).1
      obtain ⟨b₄, b₅, b₆, hx'⟩ := d.mem_W_coords (hcond x').1
      rw [← hx, nfc_nf] at he hf hh
      rw [← hx', nfc_nf] at he hf hh
      apply Subtype.ext; apply Subtype.ext
      rw [← hx, ← hx']
      simp only at he hf hh
      rw [he, hf, hh]
    have hinj := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_prod, d.card_Γ₀] at hinj
    have hA := card_mul_card_bilinOrth_le d.trBilin d.trBilin_nondegenerate SE
    rw [d.card_Γ] at hA
    rw [hcard]
    calc Nat.card SE * Nat.card φ.ker ≤
          Nat.card SE * (Nat.card {e : d.Γ // ∀ s ∈ SE, d.trBilin s e = 0} * (q * q)) :=
          Nat.mul_le_mul_left _ hinj
      _ = Nat.card SE * Nat.card {e : d.Γ // ∀ s ∈ SE, d.trBilin s e = 0} * (q * q) := by ring
      _ ≤ q ^ 3 * (q * q) := Nat.mul_le_mul_right _ hA
      _ = q ^ 5 := by ring
  · push Not at hS
    have hED : E ≤ d.D := fun x hx => d.mem_D_of_nfc_fst (hES hx)
      (hS _ ((hmemSE _).2 ⟨⟨x, hx⟩, rfl⟩))
    exact d.yamada_3_11_1 hED hcomm

include d in
theorem card_le_of_isElemAbelian {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ q ^ 5 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := d.finite
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => by
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE.2 x hx
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hE2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, sq]; exact hsq x x.2)⟩
  obtain ⟨Q, hQ⟩ := hE2.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P Q
  rw [Sylow.coe_subgroup_smul, hP] at hQ
  set E' : Subgroup X := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hE'S : E' ≤ d.S := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hQ hx
    have : (MulAut.conj g⁻¹).toMonoidHom x = y := by
      rw [← hyx]
      change g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
      group
    rw [this]
    exact hy
  rw [← hcard]
  refine d.card_le_of_elementary_le_S hE'S ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]

@[expose] def tripleHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {x : A → X} {y : B → X} {z : C → X} (hx : ∀ a b, x (a + b) = x a * x b)
    (hy : ∀ a b, y (a + b) = y a * y b) (hz : ∀ a b, z (a + b) = z a * z b)
    (hxy : ∀ a b, Commute (x a) (y b)) (hxz : ∀ a c, Commute (x a) (z c))
    (hyz : ∀ b c, Commute (y b) (z c)) : Multiplicative (A × B × C) →* X where
  toFun p := x (Multiplicative.toAdd p).1 * y (Multiplicative.toAdd p).2.1 *
    z (Multiplicative.toAdd p).2.2
  map_one' := by
    simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, map_zero_of_add hx, map_zero_of_add hy,
      map_zero_of_add hz, mul_one]
  map_mul' p p' := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, hx, hy, hz]
    set a := (Multiplicative.toAdd p).1
    set b := (Multiplicative.toAdd p).2.1
    set c := (Multiplicative.toAdd p).2.2
    set a' := (Multiplicative.toAdd p').1
    set b' := (Multiplicative.toAdd p').2.1
    set c' := (Multiplicative.toAdd p').2.2
    have hzc : Commute (z c) (x a' * y b') := ((hxz a' c).symm.mul_right (hyz b' c).symm)
    calc x a * x a' * (y b * y b') * (z c * z c') =
        x a * (x a' * y b) * y b' * (z c * z c') := by group
      _ = x a * (y b * x a') * y b' * (z c * z c') := by rw [(hxy a' b).eq]
      _ = x a * y b * ((x a' * y b') * z c) * z c' := by group
      _ = x a * y b * (z c * (x a' * y b')) * z c' := by rw [hzc.eq]
      _ = x a * y b * z c * (x a' * y b' * z c') := by group

theorem isElemAbelian_range_tripleHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] {x : A → X} {y : B → X} {z : C → X} (hx : ∀ a b, x (a + b) = x a * x b)
    (hy : ∀ a b, y (a + b) = y a * y b) (hz : ∀ a b, z (a + b) = z a * z b)
    (hxy : ∀ a b, Commute (x a) (y b)) (hxz : ∀ a c, Commute (x a) (z c))
    (hyz : ∀ b c, Commute (y b) (z c)) (h2 : ∀ p : A × B × C, p + p = 0) :
    CFSG.Open.IsElemAbelian 2 (tripleHom hx hy hz hxy hxz hyz).range := by
  refine ⟨⟨⟨fun g g' => ?_⟩⟩, ?_⟩
  · obtain ⟨p, hp⟩ := g.2
    obtain ⟨p', hp'⟩ := g'.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hp, ← hp', ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨p, rfl⟩
    rw [← map_pow, sq, ← ofAdd_toAdd p, ← ofAdd_add, h2, ofAdd_zero, map_one]

theorem card_range_tripleHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {x : A → X} {y : B → X} {z : C → X} (hx : ∀ a b, x (a + b) = x a * x b)
    (hy : ∀ a b, y (a + b) = y a * y b) (hz : ∀ a b, z (a + b) = z a * z b)
    (hxy : ∀ a b, Commute (x a) (y b)) (hxz : ∀ a c, Commute (x a) (z c))
    (hyz : ∀ b c, Commute (y b) (z c))
    (hinj : ∀ p p' : A × B × C, x p.1 * y p.2.1 * z p.2.2 = x p'.1 * y p'.2.1 * z p'.2.2 →
      p = p') :
    Nat.card (tripleHom hx hy hz hxy hxz hyz).range = Nat.card A * Nat.card B * Nat.card C := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (f := tripleHom hx hy hz hxy hxz hyz)
    (fun p p' h => by
      have := hinj (Multiplicative.toAdd p) (Multiplicative.toAdd p') h
      exact this)).toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod,
    mul_assoc]

theorem prod_add_self_eq_zero {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (hA : ∀ a : A, a + a = 0) (hB : ∀ b : B, b + b = 0) (hC : ∀ c : C, c + c = 0)
    (p : A × B × C) : p + p = 0 :=
  Prod.ext (hA _) (Prod.ext (hB _) (hC _))

@[expose] noncomputable def eU₁Y : Subgroup X :=
  (tripleHom d.x₁_add d.x₅_add d.x₆_add d.commute₁₅ d.commute₁₆ d.commute₅₆).range

@[expose] noncomputable def eU₂U₃V : Subgroup X :=
  (tripleHom d.x₂_add d.x₃_add d.x₆_add d.commute₂₃ d.commute₂₆ d.commute₃₆).range

@[expose] noncomputable def eW : Subgroup X :=
  (tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆ d.commute₅₆).range

theorem isElemAbelian_eU₁Y : CFSG.Open.IsElemAbelian 2 d.eU₁Y :=
  isElemAbelian_range_tripleHom _ _ _ _ _ _
    (prod_add_self_eq_zero CharTwo.add_self_eq_zero d.add_self_Γ₀ d.add_self_Γ₀)

theorem isElemAbelian_eU₂U₃V : CFSG.Open.IsElemAbelian 2 d.eU₂U₃V :=
  isElemAbelian_range_tripleHom _ _ _ _ _ _
    (prod_add_self_eq_zero d.add_self_Γ₀ CharTwo.add_self_eq_zero d.add_self_Γ₀)

theorem isElemAbelian_eW : CFSG.Open.IsElemAbelian 2 d.eW :=
  isElemAbelian_range_tripleHom _ _ _ _ _ _
    (prod_add_self_eq_zero CharTwo.add_self_eq_zero d.add_self_Γ₀ d.add_self_Γ₀)

theorem card_eU₁Y : Nat.card d.eU₁Y = q ^ 5 := by
  rw [eU₁Y, card_range_tripleHom, d.card_Γ, d.card_Γ₀]
  · ring
  · intro p p' h
    have h' : d.nf (p.1, 0, 0, 0, p.2.1, p.2.2) = d.nf (p'.1, 0, 0, 0, p'.2.1, p'.2.2) := by
      simpa only [nf_apply, d.x₂_zero, d.x₃_zero, d.x₄_zero, mul_one] using h
    have := d.nf_injective h'
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (Prod.ext this.2.2.2.2.1 this.2.2.2.2.2)

theorem card_eU₂U₃V : Nat.card d.eU₂U₃V = q ^ 5 := by
  rw [eU₂U₃V, card_range_tripleHom, d.card_Γ, d.card_Γ₀]
  · ring
  · intro p p' h
    have h' : d.nf (0, p.1, p.2.1, 0, 0, p.2.2) = d.nf (0, p'.1, p'.2.1, 0, 0, p'.2.2) := by
      simpa only [nf_apply, d.x₁_zero, d.x₄_zero, d.x₅_zero, mul_one, one_mul] using h
    have := d.nf_injective h'
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.2.1 (Prod.ext this.2.2.1 this.2.2.2.2.2)

theorem card_eW : Nat.card d.eW = q ^ 5 := by
  rw [eW, card_range_tripleHom, d.card_Γ, d.card_Γ₀]
  · ring
  · intro p p' h
    have h' : d.nf (0, 0, 0, p.1, p.2.1, p.2.2) = d.nf (0, 0, 0, p'.1, p'.2.1, p'.2.2) := by
      simpa only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul] using h
    have := d.nf_injective h'
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.2.2.2.1 (Prod.ext this.2.2.2.2.1 this.2.2.2.2.2)

theorem mem_range_tripleHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {x : A → X} {y : B → X} {z : C → X} (hx : ∀ a b, x (a + b) = x a * x b)
    (hy : ∀ a b, y (a + b) = y a * y b) (hz : ∀ a b, z (a + b) = z a * z b)
    (hxy : ∀ a b, Commute (x a) (y b)) (hxz : ∀ a c, Commute (x a) (z c))
    (hyz : ∀ b c, Commute (y b) (z c)) (a : A) (b : B) (c : C) :
    x a * y b * z c ∈ (tripleHom hx hy hz hxy hxz hyz).range :=
  ⟨Multiplicative.ofAdd (a, b, c), rfl⟩

theorem eU_le_S : d.eU₁Y ≤ d.S ∧ d.eU₂U₃V ≤ d.S ∧ d.eW ≤ d.S := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro _ ⟨p, rfl⟩
  · exact mul_mem (mul_mem (d.U₁_le_S (d.x₁_mem_U₁ _)) (d.U₅_le_S (d.x₅_mem_U₅ _)))
      (d.V_le_S (d.x₆_mem_V _))
  · exact mul_mem (mul_mem (d.U₂_le_S (d.x₂_mem_U₂ _)) (d.U₃_le_S (d.x₃_mem_U₃ _)))
      (d.V_le_S (d.x₆_mem_V _))
  · exact mul_mem (mul_mem (d.U₄_le_S (d.x₄_mem_U₄ _)) (d.U₅_le_S (d.x₅_mem_U₅ _)))
      (d.V_le_S (d.x₆_mem_V _))

include d in
theorem pRank_eq_of_le [Finite X] {f : ℕ} (hq : q = 2 ^ f) {E H : Subgroup X} (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian 2 E) (hcard : Nat.card E = q ^ 5) :
    CFSG.Open.pRank 2 H = 5 * f := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le one_lt_two fun E' _ hE' => ?_
    calc Nat.card E' ≤ q ^ 5 := d.card_le_of_isElemAbelian hE'
      _ = 2 ^ (5 * f) := by rw [hq, ← pow_mul, mul_comm]
  · exact CFSG.SectionRank.le_pRank one_lt_two hEH hE (by rw [hcard, hq, ← pow_mul, mul_comm])

theorem yamada_3_11_3 [Finite X] {f : ℕ} (hq : q = 2 ^ f) :
    CFSG.Open.pRank 2 d.S = 5 * f ∧ CFSG.Open.pRank 2 (⊤ : Subgroup X) = 5 * f ∧
      (⨆ (A : Subgroup X) (_ : A ≤ d.S ∧ IsMulCommutative A ∧
        CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 d.S), A) = d.S := by
  obtain ⟨h₁, h₂, h₃⟩ := d.eU_le_S
  have hS := d.pRank_eq_of_le hq h₃ d.isElemAbelian_eW d.card_eW
  refine ⟨hS, d.pRank_eq_of_le hq le_top d.isElemAbelian_eW d.card_eW, ?_⟩
  have key : ∀ A : Subgroup X, A ≤ d.S → CFSG.Open.IsElemAbelian 2 A → Nat.card A = q ^ 5 →
      A ≤ ⨆ (A : Subgroup X) (_ : A ≤ d.S ∧ IsMulCommutative A ∧
        CFSG.Open.pRank 2 A = CFSG.Open.pRank 2 d.S), A := fun A hAS hA hcA =>
    le_iSup₂_of_le A ⟨hAS, hA.1, by rw [hS, d.pRank_eq_of_le hq le_rfl hA hcA]⟩ le_rfl
  have k₁ := key _ h₁ d.isElemAbelian_eU₁Y d.card_eU₁Y
  have k₂ := key _ h₂ d.isElemAbelian_eU₂U₃V d.card_eU₂U₃V
  have k₃ := key _ h₃ d.isElemAbelian_eW d.card_eW
  refine le_antisymm (iSup₂_le fun A hA => hA.1) ?_
  rw [S, sixClosure, closure_le]
  rintro g (((((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩) | ⟨a, rfl⟩)
  · have h := mem_range_tripleHom d.x₁_add d.x₅_add d.x₆_add d.commute₁₅ d.commute₁₆
      d.commute₅₆ a 0 0
    rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one] at h
    exact k₁ h
  · have h := mem_range_tripleHom d.x₂_add d.x₃_add d.x₆_add d.commute₂₃ d.commute₂₆
      d.commute₃₆ a 0 0
    rw [d.x₃_zero, d.x₆_zero, mul_one, mul_one] at h
    exact k₂ h
  · have h := mem_range_tripleHom d.x₂_add d.x₃_add d.x₆_add d.commute₂₃ d.commute₂₆
      d.commute₃₆ 0 a 0
    rw [d.x₂_zero, d.x₆_zero, one_mul, mul_one] at h
    exact k₂ h
  · have h := mem_range_tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆
      d.commute₅₆ a 0 0
    rw [d.x₅_zero, d.x₆_zero, mul_one, mul_one] at h
    exact k₃ h
  · have h := mem_range_tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆
      d.commute₅₆ 0 a 0
    rw [d.x₄_zero, d.x₆_zero, one_mul, mul_one] at h
    exact k₃ h
  · have h := mem_range_tripleHom d.x₄_add d.x₅_add d.x₆_add d.commute₄₅ d.commute₄₆
      d.commute₅₆ 0 0 a
    rw [d.x₄_zero, d.x₅_zero, one_mul, one_mul] at h
    exact k₃ h

theorem eq_nf_of_mem_M {g : X} (hg : g ∈ d.M) : g = d.x₁ (d.nfc g).1 *
    (d.x₃ (d.nfc g).2.2.1 * d.x₄ (d.nfc g).2.2.2.1 *
      (d.x₅ (d.nfc g).2.2.2.2.1 * d.x₆ (d.nfc g).2.2.2.2.2)) := by
  have h2 : (d.nfc g).2.1 = 0 := by
    obtain ⟨a, c, w, hw, rfl⟩ := d.mem_M_iff_x₁_x₃.1 hg
    exact (d.nfc_x₁_x₃_mul hw).2.1
  conv_lhs => rw [← d.nf_nfc (d.M_le_S hg)]
  rw [nf_apply, h2, d.x₂_zero, mul_one]
  group

theorem mem_F_of_mem_M_of_nfc_fst {g : X} (hg : g ∈ d.M) (h : (d.nfc g).1 = 0) : g ∈ d.F := by
  rw [d.eq_nf_of_mem_M hg, h, d.x₁_zero, one_mul]
  exact mul_mem (mul_mem (d.x₃_mem_F _) (d.x₄_mem_F _)) (mul_mem (d.x₅_mem_F _) (d.x₆_mem_F _))

theorem nfc_x₄_x₅_x₆ (e : d.Γ) (f g : d.Γ₀) :
    d.nfc (d.x₄ e * d.x₅ f * d.x₆ g) = (0, 0, 0, e, f, g) := by
  rw [show d.x₄ e * d.x₅ f * d.x₆ g = d.nf (0, 0, 0, e, f, g) by
    simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul], nfc_nf]

theorem eq_zero_of_x₄_x₅_x₆_eq_one {e : d.Γ} {f g : d.Γ₀} (h : d.x₄ e * d.x₅ f * d.x₆ g = 1) :
    e = 0 ∧ f = 0 ∧ g = 0 := by
  have h1 := d.nfc_x₄_x₅_x₆ e f g
  rw [h, d.nfc_one] at h1
  simp only [Prod.ext_iff] at h1
  exact ⟨h1.2.2.2.1.symm, h1.2.2.2.2.1.symm, h1.2.2.2.2.2.symm⟩

theorem M_elt_mul_self (a c e : d.Γ) {y : X} (hy : y ∈ d.Y) :
    d.x₁ a * (d.x₃ c * d.x₄ e * y) * (d.x₁ a * (d.x₃ c * d.x₄ e * y)) =
      d.x₄ (d.qComm a c) * d.x₅ (d.e₅Comm a c + d.tr (a * e)) *
        d.x₆ (d.e₆Comm a c + d.tr (c * e)) := by
  rw [mul_mul_self_eq_commutatorElement (d.x₁_mul_self a), d.comm_x₁_F a c e hy,
    d.F_elt_mul_self c e hy,
    d.x₆_add, mul_assoc]

theorem comm_M_of_mem_Y {a a' : d.Γ} {n n' : X} (hn : n ∈ d.F) (hn' : n' ∈ d.F)
    (h₁ : ⁅d.x₁ a', n⁆ ∈ d.Y) (h₂ : ⁅d.x₁ a, n'⁆ ∈ d.Y) :
    ⁅d.x₁ a * n, d.x₁ a' * n'⁆ = ⁅d.x₁ a', n⁆⁻¹ * ⁅n, n'⁆ * ⁅d.x₁ a, n'⁆ := by
  have hV : ⁅n, n'⁆ ∈ d.V := d.commutator_F_F (commutator_mem_commutator hn hn')
  have hcV : ∀ g ∈ d.S, Commute g ⁅n, n'⁆ := fun g hg =>
    (mem_centralizer_iff.1 (d.S_le_centralizer_V hg) _ hV).symm
  have hY₁ : ⁅n, d.x₁ a'⁆ ∈ d.Y := by
    rw [← commutatorElement_inv]
    exact inv_mem h₁
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_conj,
    commutatorElement_mul_right_conj,
    mul_mul_inv_eq_of_commute (hcV _ (d.U₁_le_S (d.x₁_mem_U₁ a'))),
    commutatorElement_eq_one_iff_commute.2 (commute_of_add d.x₁_add a a'), one_mul,
    mul_mul_inv_eq_of_commute (commutatorElement_eq_one_iff_commute.1
      (d.comm_eq_one_of_M_Y (d.x₁_mem_M a') h₂)),
    show d.x₁ a * (⁅n, d.x₁ a'⁆ * ⁅n, n'⁆) * (d.x₁ a)⁻¹ = ⁅n, d.x₁ a'⁆ * ⁅n, n'⁆ from
      mul_mul_inv_eq_of_commute (commutatorElement_eq_one_iff_commute.1
        (d.comm_eq_one_of_M_Y (d.x₁_mem_M a) (mul_mem hY₁ (d.V_le_Y hV)))),
    ← commutatorElement_inv]

theorem σ_mul_of_Γ₀ (l : d.Γ₀) (x : d.Γ) : d.σ ((l : d.Γ) * x) = l * d.σ x := by
  rw [map_mul, apply_coe_fixedSubfield]

theorem qComm_smul_smul (l m : d.Γ₀) (x : d.Γ) : d.qComm ((l : d.Γ) * x) ((m : d.Γ) * x) = 0 := by
  simp only [qComm, d.σ_mul_of_Γ₀]
  triality_ring2

theorem e₅Comm_smul_smul (l m : d.Γ₀) (x : d.Γ) :
    (d.e₅Comm ((l : d.Γ) * x) ((m : d.Γ) * x) : d.Γ) = l * l * m * d.nm x := by
  have e : (l : d.Γ) * x * d.σ ((l : d.Γ) * x) * d.σ (d.σ ((m : d.Γ) * x)) =
      ((l * l * m : d.Γ₀) : d.Γ) * (d.nm x : d.Γ) := by
    rw [d.σ_mul_of_Γ₀, d.σ_mul_of_Γ₀, d.σ_mul_of_Γ₀, coe_fixedNorm]
    push_cast
    ring
  rw [e₅Comm, e, d.tr_smul, d.coe_tr_of_Γ₀]
  push_cast
  ring

theorem tr_smul_mul (l : d.Γ₀) (x e : d.Γ) :
    (d.tr ((l : d.Γ) * x * e) : d.Γ) = l * d.tr (x * e) := by
  rw [mul_assoc, d.tr_smul]

theorem e₅Comm_mul_mul {l m x : d.Γ} (hl : d.σ l = l) (hm : d.σ m = m) :
    (d.e₅Comm (l * x) (m * x) : d.Γ) = l * l * m * d.nm x :=
  d.e₅Comm_smul_smul ⟨l, hl⟩ ⟨m, hm⟩ x

theorem e₅Comm_mul_right {m x : d.Γ} (hm : d.σ m = m) :
    (d.e₅Comm x (m * x) : d.Γ) = m * d.nm x := by
  have h := d.e₅Comm_mul_mul (l := 1) (x := x) (map_one d.σ) hm
  rwa [one_mul, one_mul, one_mul] at h

theorem tr_mul_mul_of_fixed {l x e : d.Γ} (hl : d.σ l = l) :
    (d.tr (l * x * e) : d.Γ) = l * d.tr (x * e) :=
  d.tr_smul_mul ⟨l, hl⟩ x e

theorem x₅_mul_x₆_inj {a b a' b' : d.Γ₀} (h : d.x₅ a * d.x₆ b = d.x₅ a' * d.x₆ b') :
    a = a' ∧ b = b' := by
  have h1 := d.nfc_x₄_x₅_x₆ 0 a b
  rw [d.x₄_zero, one_mul, h, ← one_mul (d.x₅ a'), ← d.x₄_zero, d.nfc_x₄_x₅_x₆] at h1
  simp only [Prod.ext_iff] at h1
  exact ⟨h1.2.2.2.2.1.symm, h1.2.2.2.2.2.symm⟩

theorem σ_div_of_σ_eq {a b : d.Γ} (ha : d.σ a = a) (hb : d.σ b = b) : d.σ (a / b) = a / b := by
  rw [map_div₀, ha, hb]

theorem exists_coeff_of_elementary_le_M {B : Subgroup X} (hBM : B ≤ d.M)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) (hBF : ¬ B ≤ d.F) :
    ∃ t : d.Γ₀, ∀ b ∈ B, (d.nfc b).2.2.1 = (t : d.Γ) * (d.nfc b).1 := by
  obtain ⟨b₀, hb₀B, hb₀F⟩ := Set.not_subset.1 hBF
  have hα₀ : (d.nfc b₀).1 ≠ 0 := fun h => hb₀F (d.mem_F_of_mem_M_of_nfc_fst (hBM hb₀B) h)
  have hBD : ∀ b ∈ B, (d.nfc b).1 = 0 → (d.nfc b).2.2.1 = 0 := by
    intro b hb h0
    obtain ⟨n, hn, hb₀n⟩ := d.eq_x₁_mul_of_mem_S (d.M_le_S (hBM hb₀B))
    have hc := hcomm _ hb₀B _ hb
    rw [hb₀n] at hc
    obtain ⟨a₄, a₅, a₆, h⟩ := d.mem_W_coords (d.mem_W_of_commute_x₁_mul hα₀ hn
      (d.mem_D_of_nfc_fst (d.M_le_S (hBM hb)) h0) hc (hsq b hb)).1
    rw [← h, nfc_nf]
  have hQ : ∀ b ∈ B, d.qComm (d.nfc b).1 (d.nfc b).2.2.1 = 0 ∧
      (d.e₅Comm (d.nfc b).1 (d.nfc b).2.2.1 : d.Γ) + d.tr ((d.nfc b).1 * (d.nfc b).2.2.2.1) =
        0 := by
    intro b hb
    have h := hsq b hb
    rw [d.eq_nf_of_mem_M (hBM hb),
      d.M_elt_mul_self _ _ _ (mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _))] at h
    obtain ⟨h4, h5, -⟩ := d.eq_zero_of_x₄_x₅_x₆_eq_one h
    exact ⟨h4, by have := congrArg Subtype.val h5; rwa [Subfield.coe_add] at this⟩
  have hfix : ∀ b ∈ B, (d.nfc b).1 ≠ 0 →
      d.σ ((d.nfc b).2.2.1 / (d.nfc b).1) = (d.nfc b).2.2.1 / (d.nfc b).1 :=
    fun b hb h0 => d.σ_div_eq_of_qComm h0 (hQ b hb).1
  have hβ : ∀ b ∈ B, (d.nfc b).1 ≠ 0 →
      (d.nfc b).2.2.1 = (d.nfc b).2.2.1 / (d.nfc b).1 * (d.nfc b).1 :=
    fun b hb h0 => (div_mul_cancel₀ _ h0).symm
  set α₀ := (d.nfc b₀).1 with hα₀def
  set t₀ := (d.nfc b₀).2.2.1 / α₀ with ht₀def
  have ht₀ : d.σ t₀ = t₀ := hfix b₀ hb₀B hα₀
  refine ⟨⟨t₀, ht₀⟩, fun b hb => ?_⟩
  change (d.nfc b).2.2.1 = t₀ * (d.nfc b).1
  by_cases hα : (d.nfc b).1 = 0
  · rw [hα, mul_zero, hBD b hb hα]
  set α := (d.nfc b).1 with hαdef
  set l := (d.nfc b).2.2.1 / α with hldef
  have hl : d.σ l = l := hfix b hb hα
  rw [hβ b hb hα]
  change l * α = t₀ * α
  congr 1
  have hco := d.nfc_ac_mul (hBM hb) (hBM hb₀B)
  simp only [Prod.mk_add_mk, Prod.mk.injEq] at hco
  obtain ⟨hco1, hco3⟩ := hco
  by_cases hdep : d.σ (α / α₀) = α / α₀
  · set μ := α / α₀ with hμdef
    have hαμ : α = μ * α₀ := by rw [hμdef, div_mul_cancel₀ _ hα₀]
    have hμ0 : μ ≠ 0 := fun h => hα (by rw [hαμ, h, zero_mul])
    by_cases hμ1 : μ = 1
    ·
      have hαα : α = α₀ := by rw [hαμ, hμ1, one_mul]
      have h0 : (d.nfc (b * b₀)).1 = 0 := by rw [hco1, ← hαdef, hαα, CharTwo.add_self_eq_zero]
      have h3 := hBD _ (mul_mem hb hb₀B) h0
      rw [hco3] at h3
      have h3' := CharTwo.add_eq_zero.1 h3
      rw [hβ b hb hα, hβ b₀ hb₀B hα₀] at h3'
      change l * α = t₀ * α₀ at h3'
      rw [hαα] at h3'
      exact mul_right_cancel₀ hα₀ h3'
    ·
      have hc := hcomm _ hb₀B _ hb
      rw [← commutatorElement_eq_one_iff_mul_comm, d.eq_nf_of_mem_M (hBM hb₀B),
        d.eq_nf_of_mem_M (hBM hb)] at hc
      set e₀ := (d.nfc b₀).2.2.2.1
      set e := (d.nfc b).2.2.2.1
      have hy₀ : d.x₅ (d.nfc b₀).2.2.2.2.1 * d.x₆ (d.nfc b₀).2.2.2.2.2 ∈ d.Y :=
        mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)
      have hy : d.x₅ (d.nfc b).2.2.2.2.1 * d.x₆ (d.nfc b).2.2.2.2.2 ∈ d.Y :=
        mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)
      have hb₀3 : (d.nfc b₀).2.2.1 = t₀ * α₀ := by rw [ht₀def, div_mul_cancel₀ _ hα₀]
      have hb3 : (d.nfc b).2.2.1 = l * μ * α₀ := by
        rw [hldef, mul_assoc, ← hαμ, div_mul_cancel₀ _ hα]
      have hq₁ : d.qComm α (d.nfc b₀).2.2.1 = 0 := by
        rw [hαμ, hb₀3]
        exact d.qComm_smul_smul ⟨μ, hdep⟩ ⟨t₀, ht₀⟩ α₀
      have hlμ : d.σ (l * μ) = l * μ := by rw [map_mul, hl, hdep]
      have hq₂ : d.qComm α₀ (d.nfc b).2.2.1 = 0 := by
        rw [hb3]
        have := d.qComm_smul_smul 1 ⟨l * μ, hlμ⟩ α₀
        rwa [OneMemClass.coe_one, one_mul] at this
      have hf₁ := d.comm_x₁_F α (d.nfc b₀).2.2.1 e₀ hy₀
      have hf₂ := d.comm_x₁_F α₀ (d.nfc b).2.2.1 e hy
      rw [hq₁, d.x₄_zero, one_mul] at hf₁
      rw [hq₂, d.x₄_zero, one_mul] at hf₂
      have hF₀ : d.x₃ (d.nfc b₀).2.2.1 * d.x₄ e₀ *
          (d.x₅ (d.nfc b₀).2.2.2.2.1 * d.x₆ (d.nfc b₀).2.2.2.2.2) ∈ d.F :=
        mul_mem (mul_mem (d.x₃_mem_F _) (d.x₄_mem_F _)) (d.W_le_F (d.Y_le_W hy₀))
      have hF : d.x₃ (d.nfc b).2.2.1 * d.x₄ e *
          (d.x₅ (d.nfc b).2.2.2.2.1 * d.x₆ (d.nfc b).2.2.2.2.2) ∈ d.F :=
        mul_mem (mul_mem (d.x₃_mem_F _) (d.x₄_mem_F _)) (d.W_le_F (d.Y_le_W hy))
      rw [d.comm_M_of_mem_Y hF₀ hF (by rw [hf₁]; exact mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _))
        (by rw [hf₂]; exact mul_mem (d.x₅_mem_Y _) (d.x₆_mem_Y _)), hf₁, hf₂] at hc
      obtain ⟨c, hc6⟩ := d.commutator_F_F (commutator_mem_commutator hF₀ hF)
      rw [← hc6] at hc
      set A := d.e₅Comm α (d.nfc b₀).2.2.1 + d.tr (α * e₀)
      set A' := d.e₆Comm α (d.nfc b₀).2.2.1
      set B' := d.e₅Comm α₀ (d.nfc b).2.2.1 + d.tr (α₀ * e)
      set C' := d.e₆Comm α₀ (d.nfc b).2.2.1
      have hA : A = B' := by
        rw [mul_assoc] at hc
        have h1 : d.x₅ A * d.x₆ A' = d.x₅ B' * d.x₆ (c + C') :=
          calc d.x₅ A * d.x₆ A' = d.x₆ c * (d.x₅ B' * d.x₆ C') := inv_mul_eq_one.1 hc
            _ = d.x₅ B' * (d.x₆ c * d.x₆ C') := by
                rw [← mul_assoc, ← (d.commute₅₆ B' c).eq, mul_assoc]
            _ = d.x₅ B' * d.x₆ (c + C') := by rw [d.x₆_add]
        exact (d.x₅_mul_x₆_inj h1).1
      have hs₀ := (hQ b₀ hb₀B).2
      have hs := (hQ b hb).2
      have hN := d.nm_ne_zero_of_ne hα₀
      have hA' : (d.e₅Comm α (d.nfc b₀).2.2.1 : d.Γ) + d.tr (α * e₀) =
          d.e₅Comm α₀ (d.nfc b).2.2.1 + d.tr (α₀ * e) := by
        rw [← Subfield.coe_add, ← Subfield.coe_add]
        exact congrArg Subtype.val hA
      rw [hb₀3, hb3, hαμ, d.e₅Comm_mul_mul hdep ht₀, d.tr_mul_mul_of_fixed hdep,
        d.e₅Comm_mul_right hlμ] at hA'
      rw [← hα₀def, hb₀3, d.e₅Comm_mul_right ht₀] at hs₀
      rw [← hαdef, hb3, hαμ, d.e₅Comm_mul_mul hdep hlμ, d.tr_mul_mul_of_fixed hdep] at hs
      have hs₀' : (d.tr (α₀ * e₀) : d.Γ) = t₀ * d.nm α₀ := (CharTwo.add_eq_zero.1 hs₀).symm
      have hs' : μ * (d.tr (α₀ * e) : d.Γ) = μ * μ * (l * μ) * d.nm α₀ :=
        (CharTwo.add_eq_zero.1 hs).symm
      have hs'' : (d.tr (α₀ * e) : d.Γ) = μ * (l * μ) * d.nm α₀ := by
        apply mul_left_cancel₀ hμ0
        rw [hs']
        ring
      rw [hs₀', hs''] at hA'
      have key : (d.nm α₀ : d.Γ) * μ * (1 + μ) * (l + t₀) = 0 := by
        linear_combination (norm := triality_ring2) hA'
      have h1μ : (1 : d.Γ) + μ ≠ 0 := fun h => hμ1 (CharTwo.add_eq_zero.1 h).symm
      exact CharTwo.add_eq_zero.1 ((mul_eq_zero.1 key).resolve_left
        (mul_ne_zero (mul_ne_zero hN hμ0) h1μ))
  ·
    have hsum : α + α₀ ≠ 0 := fun h => hdep (by
      rw [CharTwo.add_eq_zero.1 h, div_self hα₀, map_one])
    have hα'' : (d.nfc (b * b₀)).1 ≠ 0 := by rw [hco1]; exact hsum
    set l'' := (d.nfc (b * b₀)).2.2.1 / (d.nfc (b * b₀)).1 with hl''def
    have hl'' : d.σ l'' = l'' := hfix _ (mul_mem hb hb₀B) hα''
    have h3 : (d.nfc (b * b₀)).2.2.1 = l'' * (d.nfc (b * b₀)).1 := hβ _ (mul_mem hb hb₀B) hα''
    rw [hco3, hco1, hβ b hb hα, hβ b₀ hb₀B hα₀] at h3
    change l * α + t₀ * α₀ = l'' * (α + α₀) at h3
    have h4 : (l + l'') * α = (t₀ + l'') * α₀ := by linear_combination (norm := triality_ring2) h3
    by_cases hll : l + l'' = 0
    · rw [hll, zero_mul] at h4
      have h5 : t₀ + l'' = 0 := (mul_eq_zero.1 h4.symm).resolve_right hα₀
      rw [CharTwo.add_eq_zero.1 hll, CharTwo.add_eq_zero.1 h5]
    · exfalso
      apply hdep
      have h6 : α / α₀ = (t₀ + l'') / (l + l'') := by
        rw [div_eq_div_iff hα₀ hll, mul_comm, h4, mul_comm]
      rw [h6]
      exact d.σ_div_of_σ_eq (by rw [map_add, ht₀, hl'']) (by rw [map_add, hl, hl''])

theorem v_normalizes_W : d.v ∈ normalizer (d.W : Set X) := by
  have := d.finite
  refine mem_normalizer_fintype (conj_mem_sup ?_ (conj_mem_sup ?_ ?_))
  · rintro _ ⟨a, rfl⟩
    rw [d.v_conj_x₄]
    exact d.x₄_mem_W a
  · rintro _ ⟨a, rfl⟩
    rw [d.v_conj_x₅]
    exact d.x₆_mem_W a
  · rintro _ ⟨a, rfl⟩
    rw [d.v_conj_x₆]
    exact d.x₅_mem_W a

theorem exists_conj_x₂_eq (t : d.Γ₀) (α : d.Γ) {w : X} (hw : w ∈ d.W) :
    ∃ w' ∈ d.W, (d.x₂ t)⁻¹ * (d.x₁ α * d.x₃ (t * α) * w) * d.x₂ t = d.x₁ α * w' := by
  have hx₂ : d.x₂ t ∈ normalizer (d.W : Set X) := d.S_le_normalizer_W (d.U₂_le_S (d.x₂_mem_U₂ t))
  have hx₃ : d.x₃ (t * α) ∈ normalizer (d.W : Set X) :=
    d.S_le_normalizer_W (d.U₃_le_S (d.x₃_mem_U₃ _))
  set w₀ := d.x₄ (d.σ α * d.σ (d.σ α) * t) * d.x₅ (d.nm α * t) with hw₀
  have hw₀W : w₀ ∈ d.W := mul_mem (d.x₄_mem_W _) (d.x₅_mem_W _)
  have h1 : (d.x₂ t)⁻¹ * d.x₁ α * d.x₂ t = d.x₁ α * (d.x₃ (α * t) * w₀) := by
    have e : (d.x₂ t)⁻¹ * d.x₁ α * d.x₂ t = d.x₁ α * ⁅(d.x₁ α)⁻¹, (d.x₂ t)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e, d.x₁_inv, d.x₂_inv, d.comm₁₂, mul_assoc (d.x₃ _)]
  have h2 : (d.x₂ t)⁻¹ * d.x₃ (t * α) * d.x₂ t = d.x₃ (t * α) := by
    rw [d.x₂_inv, (d.commute₂₃ t _).eq, mul_assoc, d.x₂_mul_self, mul_one]
  have h3 : (d.x₂ t)⁻¹ * w * d.x₂ t ∈ d.W := (mem_normalizer_iff''.1 hx₂ w).1 hw
  refine ⟨(d.x₃ (t * α))⁻¹ * w₀ * d.x₃ (t * α) * ((d.x₂ t)⁻¹ * w * d.x₂ t),
    mul_mem ((mem_normalizer_iff''.1 hx₃ _).1 hw₀W) h3, ?_⟩
  have e : (d.x₂ t)⁻¹ * (d.x₁ α * d.x₃ (t * α) * w) * d.x₂ t =
      ((d.x₂ t)⁻¹ * d.x₁ α * d.x₂ t) * ((d.x₂ t)⁻¹ * d.x₃ (t * α) * d.x₂ t) *
        ((d.x₂ t)⁻¹ * w * d.x₂ t) := by group
  rw [e, h1, h2]
  have h4 : d.x₃ (α * t) * d.x₃ (t * α) = 1 := by
    rw [← d.x₃_add, mul_comm α, CharTwo.add_self_eq_zero, d.x₃_zero]
  calc d.x₁ α * (d.x₃ (α * t) * w₀) * d.x₃ (t * α) * ((d.x₂ t)⁻¹ * w * d.x₂ t) =
      d.x₁ α * (d.x₃ (α * t) * d.x₃ (t * α)) * ((d.x₃ (t * α))⁻¹ * w₀ * d.x₃ (t * α)) *
        ((d.x₂ t)⁻¹ * w * d.x₂ t) := by group
    _ = _ := by rw [h4, mul_one, mul_assoc]

theorem yamada_3_11_2_conj {B : Subgroup X} (hBM : B ≤ d.M)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) (hBF : ¬ B ≤ d.F) :
    ∃ x ∈ d.U₂, ∀ b ∈ B, (x * d.v)⁻¹ * b * (x * d.v) ∈ d.F := by
  obtain ⟨t, ht⟩ := d.exists_coeff_of_elementary_le_M hBM hcomm hsq hBF
  refine ⟨d.x₂ t, d.x₂_mem_U₂ t, fun b hb => ?_⟩
  have hb' := d.eq_nf_of_mem_M (hBM hb)
  rw [ht b hb] at hb'
  have hw : d.x₄ (d.nfc b).2.2.2.1 * (d.x₅ (d.nfc b).2.2.2.2.1 * d.x₆ (d.nfc b).2.2.2.2.2) ∈ d.W :=
    mul_mem (d.x₄_mem_W _) (mul_mem (d.x₅_mem_W _) (d.x₆_mem_W _))
  obtain ⟨w', hw', he⟩ := d.exists_conj_x₂_eq t (d.nfc b).1 hw
  have e : (d.x₂ t * d.v)⁻¹ * b * (d.x₂ t * d.v) =
      d.v⁻¹ * ((d.x₂ t)⁻¹ * (d.x₁ (d.nfc b).1 * d.x₃ (t * (d.nfc b).1) *
        (d.x₄ (d.nfc b).2.2.2.1 * (d.x₅ (d.nfc b).2.2.2.2.1 * d.x₆ (d.nfc b).2.2.2.2.2))) *
          d.x₂ t) * d.v := by
    conv_lhs => rw [hb']
    group
  rw [e, he, show d.v⁻¹ * (d.x₁ (d.nfc b).1 * w') * d.v =
    (d.v⁻¹ * d.x₁ (d.nfc b).1 * d.v) * (d.v⁻¹ * w' * d.v) by group, d.v_inv, d.v_x₁]
  have hvw := (mem_normalizer_iff.1 d.v_normalizes_W w').1 hw'
  rw [d.v_inv] at hvw
  exact mul_mem (d.x₃_mem_F _) (d.W_le_F hvw)

end TrialityD4Data

end CFSG.LocalAnalysis.EvenBN.TrialityD4

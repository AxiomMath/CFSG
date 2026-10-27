module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L107bAux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Comb

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure SecNatCoord (φ : (Fin 5 → ZMod 2) → G) (V : Subgroup G) : Prop where
  mem : ∀ v, IsEvenVec v → φ v ∈ V
  mul : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w
  inj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w
  onto : ∀ x ∈ V, ∃ v, IsEvenVec v ∧ φ v = x

@[expose] def SecActs (φ : (Fin 5 → ZMod 2) → G) (h : G) (σ : Equiv.Perm (Fin 5)) : Prop :=
  ∀ v, IsEvenVec v → h * φ v * h⁻¹ = φ (permVec σ v)

private instance sec123_decIsEvenVec : DecidablePred (IsEvenVec (n := 5)) := fun v => by
  unfold IsEvenVec; infer_instance

theorem sec123_isEvenVec_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

theorem sec123_isEvenVec_add {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp [Finset.sum_add_distrib, hv, hw]

theorem sec123_add_self (v : Fin 5 → ZMod 2) : v + v = 0 := by
  funext i
  have : ∀ a : ZMod 2, a + a = 0 := by decide
  exact this (v i)

theorem sec123_eq_of_add_eq_zero {v w : Fin 5 → ZMod 2} (h : v + w = 0) : v = w := by
  funext i
  have : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact this (v i) (w i) (congrFun h i)

theorem SecNatCoord.map_zero {φ : (Fin 5 → ZMod 2) → G} {V : Subgroup G}
    (hφ : SecNatCoord φ V) : φ 0 = 1 := by
  have h := hφ.mul 0 0 sec123_isEvenVec_zero sec123_isEvenVec_zero
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem SecNatCoord.mul_self_eq_one {φ : (Fin 5 → ZMod 2) → G} {V : Subgroup G}
    (hφ : SecNatCoord φ V) {x : G} (hx : x ∈ V) : x * x = 1 := by
  obtain ⟨v, hv, rfl⟩ := hφ.onto x hx
  rw [← hφ.mul v v hv hv, sec123_add_self, hφ.map_zero]

theorem SecActs.unique {φ : (Fin 5 → ZMod 2) → G} {V : Subgroup G} {h : G}
    {σ τ : Equiv.Perm (Fin 5)} (hφ : SecNatCoord φ V) (h1 : SecActs φ h σ) (h2 : SecActs φ h τ) :
    σ = τ := by
  apply permVec_injective_five
  intro v hv
  apply hφ.inj _ _ (isEvenVec_permVec σ hv) (isEvenVec_permVec τ hv)
  rw [← h1 v hv, h2 v hv]

theorem SecActs.mul {φ : (Fin 5 → ZMod 2) → G} {h h' : G} {σ τ : Equiv.Perm (Fin 5)}
    (h1 : SecActs φ h σ) (h2 : SecActs φ h' τ) : SecActs φ (h * h') (σ * τ) := by
  intro v hv
  have e : (h * h') * φ v * (h * h')⁻¹ = h * (h' * φ v * h'⁻¹) * h⁻¹ := by group
  rw [e, h2 v hv, h1 _ (isEvenVec_permVec τ hv), permVec_mul]

theorem sec123_hom {φ : (Fin 5 → ZMod 2) → G} {V H : Subgroup G} (hφ : SecNatCoord φ V)
    (hact : ∀ h ∈ H, ∃ σ, SecActs φ h σ) :
    ∃ ρ : ↥H →* Equiv.Perm (Fin 5), ∀ h : ↥H, SecActs φ (h : G) (ρ h) := by
  choose f hf using fun h : ↥H => hact h.1 h.2
  refine ⟨MonoidHom.mk' f ?_, hf⟩
  intro a b
  exact SecActs.unique hφ (hf (a * b)) ((hf a).mul (hf b))

theorem sec123_natmod_hom {V H : Subgroup G} (hV : IsNatModS5 V ⊥ H) :
    ∃ (φ : (Fin 5 → ZMod 2) → G) (ρ : ↥H →* Equiv.Perm (Fin 5)),
      SecNatCoord φ V ∧ Function.Surjective ρ ∧ ∀ h : ↥H, SecActs φ (h : G) (ρ h) := by
  obtain ⟨φ, -, -, -, -, hmem, hadd, hker, hons, hact, hsur⟩ := hV
  have hmul : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w := by
    intro v w hv hw
    have := Subgroup.mem_bot.mp (hadd v w hv hw)
    exact (inv_mul_eq_one.mp this).symm
  have hone : φ 0 = 1 := by
    exact Subgroup.mem_bot.mp ((hker 0 sec123_isEvenVec_zero).mpr (Set.mem_singleton 0))
  have hinj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w := by
    intro v w hv hw hvw
    have h1 : φ (v + w) = 1 := by
      rw [hmul v w hv hw, hvw, ← hmul w w hw hw, sec123_add_self, hone]
    have h2 : v + w ∈ ({0} : Set (Fin 5 → ZMod 2)) :=
      (hker (v + w) (sec123_isEvenVec_add hv hw)).mp (by rw [h1]; exact Subgroup.one_mem _)
    exact sec123_eq_of_add_eq_zero (Set.mem_singleton_iff.mp h2)
  have hcoord : SecNatCoord φ V :=
    ⟨hmem, hmul, hinj, fun x hx => by
      obtain ⟨v, hv, hvx⟩ := hons x hx
      exact ⟨v, hv, inv_mul_eq_one.mp (Subgroup.mem_bot.mp hvx)⟩⟩
  have hact' : ∀ h ∈ H, ∃ σ, SecActs φ h σ := by
    intro h hh
    obtain ⟨σ, -, hσ⟩ := hact h hh
    exact ⟨σ, fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hσ v hv))⟩
  obtain ⟨ρ, hρ⟩ := sec123_hom hcoord hact'
  refine ⟨φ, ρ, hcoord, fun σ => ?_, hρ⟩
  obtain ⟨h, hh, hσ⟩ := hsur σ (Subgroup.mem_top σ)
  refine ⟨⟨h, hh⟩, SecActs.unique hcoord (hρ ⟨h, hh⟩) ?_⟩
  exact fun v hv => inv_mul_eq_one.mp (Subgroup.mem_bot.mp (hσ v hv))

theorem sec123_card_cent {φ : (Fin 5 → ZMod 2) → G} {V : Subgroup G} (hφ : SecNatCoord φ V)
    {h : G} {a b : Fin 5} (hab : a ≠ b) (hact : SecActs φ h (Equiv.swap a b)) :
    Nat.card ↥(V ⊓ centralizer ({h} : Set G)) = 8 := by
  have hcount : ∀ a b : Fin 5, a ≠ b →
      Fintype.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ permVec (Equiv.swap a b) v = v} = 8 := by
    decide +kernel
  have hF : Nat.card {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ permVec (Equiv.swap a b) v = v} = 8 := by
    rw [Nat.card_eq_fintype_card]
    exact hcount a b hab
  have hcent : ∀ x : G, x ∈ centralizer ({h} : Set G) ↔ h * x * h⁻¹ = x := by
    intro x
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hx
      have h1 := hx h (Set.mem_singleton h)
      calc h * x * h⁻¹ = (x * h) * h⁻¹ := by rw [h1]
        _ = x := by group
    · intro hx y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      calc h * x = (h * x * h⁻¹) * h := by group
        _ = x * h := by rw [hx]
  let e : {v : Fin 5 → ZMod 2 // IsEvenVec v ∧ permVec (Equiv.swap a b) v = v} ≃
      ↥(V ⊓ centralizer ({h} : Set G)) :=
    { toFun := fun v => ⟨φ v.1, hφ.mem _ v.2.1, (hcent _).mpr (by
        rw [hact _ v.2.1, v.2.2])⟩
      invFun := fun x => ⟨Classical.choose (hφ.onto x.1 x.2.1), by
        obtain ⟨hv, hvx⟩ := Classical.choose_spec (hφ.onto x.1 x.2.1)
        refine ⟨hv, ?_⟩
        apply hφ.inj _ _ (isEvenVec_permVec _ hv) hv
        rw [← hact _ hv, hvx]
        exact (hcent _).mp x.2.2⟩
      left_inv := fun v => by
        apply Subtype.ext
        exact hφ.inj _ _ (Classical.choose_spec (hφ.onto (φ v.1) (hφ.mem _ v.2.1))).1 v.2.1
          (Classical.choose_spec (hφ.onto (φ v.1) (hφ.mem _ v.2.1))).2
      right_inv := fun x => by
        apply Subtype.ext
        exact (Classical.choose_spec (hφ.onto x.1 x.2.1)).2 }
  rw [← Nat.card_congr e, hF]

theorem sec123_not_central {φ : (Fin 5 → ZMod 2) → G} {V : Subgroup G} (hφ : SecNatCoord φ V)
    {h : G} {a b : Fin 5} (hab : a ≠ b) (hact : SecActs φ h (Equiv.swap a b)) :
    ∃ x ∈ V, h * x * h⁻¹ ≠ x := by
  have hmove : ∀ a b : Fin 5, a ≠ b →
      ∃ v : Fin 5 → ZMod 2, ∑ i, v i = 0 ∧ v ∘ ⇑(Equiv.swap a b).symm ≠ v := by
    decide +kernel
  obtain ⟨v, hv, hne⟩ := hmove a b hab
  refine ⟨φ v, hφ.mem v hv, ?_⟩
  rw [hact v hv]
  intro heq
  exact hne (hφ.inj _ _ (isEvenVec_permVec _ hv) hv heq)

end CFSG.OddStandard.SmallF3.Omega

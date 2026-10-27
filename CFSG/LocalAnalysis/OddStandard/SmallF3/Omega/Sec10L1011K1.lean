module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011Gen

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A : Type} [Group A] [Finite A] {B : Subgroup A} {t : A} {K : Subgroup (MulAut A)}
  {φ : (Fin 5 → ZMod 2) → A}

@[expose] def sec1011_KB (B : Subgroup A) (K : Subgroup (MulAut A)) : Subgroup (MulAut A) where
  carrier := {α | α ∈ K ∧ ∀ b ∈ B, α b = b}
  one_mem' := ⟨K.one_mem, fun b _ => rfl⟩
  mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, fun x hx => by
    rw [MulAut.mul_apply, hb.2 x hx, ha.2 x hx]⟩
  inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, fun x hx => by
    show a.symm x = x
    rw [MulEquiv.symm_apply_eq]
    exact (ha.2 x hx).symm⟩

structure Sec1011A1 (B : Subgroup A) (t : A) (K : Subgroup (MulAut A))
    (φ : (Fin 5 → ZMod 2) → A) : Prop where
  core : Sec1011Core B t K φ
  trans : sec1011_orb K t = {a | ∃ b ∈ B, a = t * b}
  iso : Nonempty (↥(K ⊓ MulAction.stabilizer (MulAut A) t) ≃* ↥(alternatingGroup (Fin 5))) ∨
    Nonempty (↥(K ⊓ MulAction.stabilizer (MulAut A) t) ≃* Equiv.Perm (Fin 5))

private instance instDecidableIsEvenVec5' (v : Fin 5 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

theorem sec1011_wfour_ne_zero' (i : Fin 5) : sec1011_wfour i ≠ 0 := by
  intro h
  have hw := sec1011_wfour_weight i
  rw [h] at hw
  simpa [vecWeight] using hw

theorem sec1011_card_orbit_mul_card_stabilizer {G α : Type} [Group G] [MulAction G α]
    (b : α) : Nat.card (MulAction.orbit G b) * Nat.card (MulAction.stabilizer G b) =
      Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G b)

theorem Sec1011A1.card_K (h : Sec1011A1 B t K φ) :
    Nat.card ↥K = 16 * Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) := by
  have horb_eq : (MulAction.orbit ↥K t : Set A) = sec1011_orb K t := by
    ext a
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨(m : MulAut A), m.2, hm.symm⟩
    · rintro ⟨α, hα, ha⟩
      exact ⟨⟨α, hα⟩, ha.symm⟩
  have horb : Nat.card (MulAction.orbit ↥K t) = 16 := by
    let f : B → MulAction.orbit ↥K t := fun b =>
      ⟨t * b, by
        rw [horb_eq, h.trans]
        exact ⟨b, b.2, rfl⟩⟩
    have hbij : Function.Bijective f := by
      constructor
      · intro b₁ b₂ h12
        apply Subtype.ext
        exact mul_left_cancel (congrArg Subtype.val h12)
      · intro c
        have hc : c.1 ∈ ({a | ∃ b ∈ B, a = t * b} : Set A) := by
          rw [← h.trans, ← horb_eq]
          exact c.2
        obtain ⟨b, hb, hbc⟩ := hc
        refine ⟨⟨b, hb⟩, ?_⟩
        apply Subtype.ext
        change t * b = c.1
        exact hbc.symm
    have hc := Nat.card_congr (Equiv.ofBijective f hbij)
    rw [← hc, h.core.card_B]
  have hstab_eq : MulAction.stabilizer ↥K t =
      (MulAction.stabilizer (MulAut A) t).subgroupOf K := by
    ext m
    simp only [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
    constructor <;> intro h <;> simpa [Subgroup.smul_def, MulAut.smul_def] using h
  have hcard_stab : Nat.card ↥(MulAction.stabilizer ↥K t) =
      Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) := by
    rw [hstab_eq]
    rw [← Subgroup.card_subtype K ((MulAction.stabilizer (MulAut A) t).subgroupOf K),
      Subgroup.subgroupOf_map_subtype, inf_comm]
  have hOS := sec1011_card_orbit_mul_card_stabilizer (G := ↥K) t
  rw [horb, hcard_stab] at hOS
  exact hOS.symm

theorem Sec1011A1.card_K_cases (h : Sec1011A1 B t K φ) :
    Nat.card ↥K = 960 ∨ Nat.card ↥K = 1920 := by
  have hK := h.card_K
  rcases h.iso with hp | hp
  · left
    obtain ⟨e⟩ := hp
    have hcard : Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    rw [hK, hcard]
  · right
    obtain ⟨e⟩ := hp
    have hcard : Nat.card ↥(K ⊓ MulAction.stabilizer (MulAut A) t) = 120 := by
      rw [Nat.card_congr e.toEquiv, sec1011_card_perm_five]
    rw [hK, hcard]

theorem Sec1011A1.exists_three (h : Sec1011A1 B t K φ) {v0 : Fin 5 → ZMod 2}
    (hv0 : IsEvenVec v0) (hw : vecWeight v0 = 4) :
    ∃ α ∈ K, α ≠ 1 ∧ α ^ 3 = 1 ∧ α (φ v0) = φ v0 := by
  obtain ⟨σ, hσ, hσne, hσ3, hσv⟩ := sec1011_alt3_fixing v0 hw
  obtain ⟨n, hnK, hnt, hn⟩ := h.core.N_act σ hσ
  have hnv0 : n (φ v0) = φ v0 := by
    rw [hn v0 hv0, hσv]
  have hpow : ∀ k : ℕ, ∀ v, IsEvenVec v → (n ^ k) (φ v) = φ (permVec (σ ^ k) v) := by
    intro k
    induction k with
    | zero => intro v _; simp [permVec_one]
    | succ k ih =>
        intro v hv
        rw [pow_succ', MulAut.mul_apply, ih v hv,
          hn _ (isEvenVec_permVec (σ ^ k) hv), ← permVec_mul, pow_succ']
  have ht3 : (n ^ 3) t = t := by
    have htn : ∀ k : ℕ, (n ^ k) t = t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, hnt]
    exact htn 3
  have hB3 : ∀ b ∈ B, (n ^ 3) b = b := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := (h.core.mem_B b).1 hb
    rw [hpow 3 v hv, hσ3, permVec_one]
  have hn3 : n ^ 3 = 1 := h.core.eq_one_of_fix hB3 ht3
  refine ⟨n, hnK, ?_, hn3, hnv0⟩
  intro hn1
  apply hσne
  apply permVec_injective_five
  intro v hv
  rw [permVec_one]
  have hφv : φ (permVec σ v) = φ v := by
    rw [← hn v hv, hn1]
    rfl
  exact h.core.inj _ _ (isEvenVec_permVec σ hv) hv hφv

end CFSG.OddStandard.SmallF3.Omega

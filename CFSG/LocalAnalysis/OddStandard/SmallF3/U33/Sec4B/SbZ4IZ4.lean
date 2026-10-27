module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ2A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ1A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

@[expose] def z4iM (K : Subgroup H) (τ l : H) : Subgroup H := K ⊔ closure {τ, l}

private lemma z4i_pow_add_fin {G : Type*} [Group G] (x : G) (hx : x * x = 1)
    (a a' : Fin 2) : x ^ (a : ℕ) * x ^ (a' : ℕ) = x ^ ((a + a' : Fin 2) : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod (n := 2) ((a : ℕ) + (a' : ℕ))
      (by simpa [pow_two] using hx), ← Fin.val_add]

private lemma z4i_fin_pow_self_inv {G : Type*} [Group G] (x : G) (hx : x * x = 1)
    (a : Fin 2) : (x ^ (a : ℕ))⁻¹ = x ^ (a : ℕ) := by
  rw [← inv_pow, inv_eq_of_mul_eq_one_right hx]

private lemma z4i_mul_pair_comm {G : Type*} [Group G] {a₁ a₂ b₁ b₂ : G}
    (h : Commute a₂ b₁) : a₁ * a₂ * (b₁ * b₂) = (a₁ * b₁) * (a₂ * b₂) := by
  calc a₁ * a₂ * (b₁ * b₂) = a₁ * (a₂ * b₁) * b₂ := by group
    _ = a₁ * (b₁ * a₂) * b₂ := by rw [h.eq]
    _ = (a₁ * b₁) * (a₂ * b₂) := by group

private lemma z4i_fin2_add_eq_zero {a a' : Fin 2} (h : a + a' = 0) : a = a' := by
  revert h
  fin_cases a <;> fin_cases a' <;> decide

namespace ZEData

variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}

private lemma word_mul_tl (h : ZEData Q Y V V' B K ρ t τ l) (b c b' c' : Fin 2) :
    (τ ^ (b : ℕ) * l ^ (c : ℕ)) * (τ ^ (b' : ℕ) * l ^ (c' : ℕ)) =
      τ ^ ((b + b' : Fin 2) : ℕ) * l ^ ((c + c' : Fin 2) : ℕ) := by
  rw [z4i_mul_pair_comm ((show Commute l τ from h.tau_l.symm).pow_pow c b'),
      z4i_pow_add_fin τ h.tau_sq b b', z4i_pow_add_fin l h.l_sq c c']

private lemma word_sq_tl (h : ZEData Q Y V V' B K ρ t τ l) (b c : Fin 2) :
    (τ ^ (b : ℕ) * l ^ (c : ℕ)) * (τ ^ (b : ℕ) * l ^ (c : ℕ)) = 1 := by
  rw [word_mul_tl h b c b c]
  have hb : (b + b : Fin 2) = 0 := by fin_cases b <;> decide
  have hc : (c + c : Fin 2) = 0 := by fin_cases c <;> decide
  rw [hb, hc]
  simp

private lemma mem_closure_tl_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ closure ({τ, l} : Set H) ↔ ∃ b c : Fin 2, x = τ ^ (b : ℕ) * l ^ (c : ℕ) := by
  let W : Subgroup H :=
    { carrier := {x | ∃ b c : Fin 2, x = τ ^ (b : ℕ) * l ^ (c : ℕ)}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨b, c, rfl⟩ ⟨b', c', rfl⟩
        exact ⟨b + b', c + c', word_mul_tl h b c b' c'⟩
      inv_mem' := by
        rintro x ⟨b, c, rfl⟩
        exact ⟨b, c, by
          rw [mul_inv_rev, z4i_fin_pow_self_inv τ h.tau_sq b,
            z4i_fin_pow_self_inv l h.l_sq c]
          exact ((show Commute l τ from h.tau_l.symm).pow_pow c b).eq⟩ }
  constructor
  · intro hx
    refine (Subgroup.closure_le (k := ({τ, l} : Set H)) W).mpr ?_ hx
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · rintro ⟨b, c, rfl⟩
    have hτ : τ ∈ closure ({τ, l} : Set H) := Subgroup.subset_closure (by simp)
    have hl : l ∈ closure ({τ, l} : Set H) := Subgroup.subset_closure (by simp)
    exact (closure ({τ, l} : Set H)).mul_mem
      ((closure ({τ, l} : Set H)).pow_mem hτ (b : ℕ))
      ((closure ({τ, l} : Set H)).pow_mem hl (c : ℕ))

private lemma closure_tl_norm_K (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ s ∈ closure ({τ, l} : Set H), ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
  have hle : closure ({τ, l} : Set H) ≤ z4iT3 t τ l :=
    Subgroup.closure_mono (by
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      rcases hg with rfl | rfl <;> simp)
  intro s hs k hk
  exact h.T3_norm_K s (hle hs) k hk

private lemma closure_tl_inf_K (h : ZEData Q Y V V' B K ρ t τ l) :
    K ⊓ closure ({τ, l} : Set H) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hxK, hxT⟩ := hx
  obtain ⟨b, c, rfl⟩ := (mem_closure_tl_iff h).mp hxT
  have hmem : t ^ ((0 : Fin 2) : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) ∈ K := by
    simpa using hxK
  obtain ⟨_, hb, hc⟩ := h.word_mem_K hmem
  rw [hb, hc]
  simp

private lemma card_closure_tl (h : ZEData Q Y V V' B K ρ t τ l) :
    Nat.card (closure ({τ, l} : Set H)) = 4 := by
  classical
  let f : Fin 2 × Fin 2 → closure ({τ, l} : Set H) := fun p =>
    ⟨τ ^ (p.1 : ℕ) * l ^ (p.2 : ℕ), (mem_closure_tl_iff h).mpr ⟨p.1, p.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b, c⟩ ⟨b', c'⟩ heq
      have hw : τ ^ (b : ℕ) * l ^ (c : ℕ) = τ ^ (b' : ℕ) * l ^ (c' : ℕ) :=
        congrArg Subtype.val heq
      have hunit : (τ ^ (b : ℕ) * l ^ (c : ℕ)) * (τ ^ (b' : ℕ) * l ^ (c' : ℕ)) = 1 := by
        rw [hw, word_sq_tl h b' c']
      have hword : τ ^ ((b + b' : Fin 2) : ℕ) * l ^ ((c + c' : Fin 2) : ℕ) = 1 := by
        rw [← word_mul_tl h b c b' c']
        exact hunit
      have hK : t ^ ((0 : Fin 2) : ℕ) * τ ^ ((b + b' : Fin 2) : ℕ) *
          l ^ ((c + c' : Fin 2) : ℕ) ∈ K := by
        rw [mul_assoc, hword]
        simp
      obtain ⟨_, hbb, hcc⟩ := h.word_mem_K hK
      exact Prod.ext (z4i_fin2_add_eq_zero hbb) (z4i_fin2_add_eq_zero hcc)
    · rintro ⟨x, hx⟩
      obtain ⟨b, c, rfl⟩ := (mem_closure_tl_iff h).mp hx
      exact ⟨(b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  norm_num [Fintype.card_prod]

theorem mem_M_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ z4iM K τ l ↔ ∃ k ∈ K, ∃ b c : Fin 2, x = k * τ ^ (b : ℕ) * l ^ (c : ℕ) := by
  rw [z4iM, mem_sup_iff_of_normalizes (H := K) (K := closure ({τ, l} : Set H))
    (closure_tl_norm_K h)]
  constructor
  · rintro ⟨k, hk, s, hs, rfl⟩
    obtain ⟨b, c, rfl⟩ := (mem_closure_tl_iff h).mp hs
    exact ⟨k, hk, b, c, by rw [mul_assoc]⟩
  · rintro ⟨k, hk, b, c, rfl⟩
    exact ⟨k, hk, τ ^ (b : ℕ) * l ^ (c : ℕ), (mem_closure_tl_iff h).mpr ⟨b, c, rfl⟩,
      by rw [mul_assoc]⟩

theorem M_le_Vc (h : ZEData Q Y V V' B K ρ t τ l) : z4iM K τ l ≤ z4iVc K t τ l := by
  show K ⊔ closure ({τ, l} : Set H) ≤ K ⊔ z4iT3 t τ l
  refine sup_le_sup_left ?_ K
  exact Subgroup.closure_mono (by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
    rcases hg with rfl | rfl <;> simp)

theorem t_not_mem_M (h : ZEData Q Y V V' B K ρ t τ l) : t ∉ z4iM K τ l := by
  intro ht
  obtain ⟨k, hk, b, c, hkt⟩ := (mem_M_iff h).mp ht
  have hkt' : t = k * (τ ^ (b : ℕ) * l ^ (c : ℕ)) := by rw [hkt, mul_assoc]
  have hsq : (τ ^ (b : ℕ) * l ^ (c : ℕ)) * (τ ^ (b : ℕ) * l ^ (c : ℕ)) = 1 :=
    word_sq_tl h b c
  have hk_eq : k = t * (τ ^ (b : ℕ) * l ^ (c : ℕ)) := by
    rw [hkt']
    rw [show (k * (τ ^ (b : ℕ) * l ^ (c : ℕ))) * (τ ^ (b : ℕ) * l ^ (c : ℕ)) =
      k * ((τ ^ (b : ℕ) * l ^ (c : ℕ)) * (τ ^ (b : ℕ) * l ^ (c : ℕ))) by
        rw [mul_assoc]]
    rw [hsq, mul_one]
  have hmem : t ^ ((1 : Fin 2) : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) ∈ K := by
    have h1 : t ^ ((1 : Fin 2) : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)
        = t * (τ ^ (b : ℕ) * l ^ (c : ℕ)) := by simp [mul_assoc]
    rw [h1, ← hk_eq]
    exact hk
  obtain ⟨ha, _, _⟩ := h.word_mem_K hmem
  exact absurd ha (by decide)

theorem card_M (h : ZEData Q Y V V' B K ρ t τ l) : Nat.card (z4iM K τ l) = 1024 := by
  have hcard := card_sup_eq_mul (H := K) (K := closure ({τ, l} : Set H))
    (closure_tl_norm_K h) (closure_tl_inf_K h)
  show Nat.card ↥(K ⊔ closure ({τ, l} : Set H)) = 1024
  rw [hcard, h.card_K, card_closure_tl h]

theorem M_relIndex (h : ZEData Q Y V V' B K ρ t τ l) :
    (z4iM K τ l).relIndex (z4iVc K t τ l) = 2 := by
  have hinf : z4iM K τ l ⊓ z4iVc K t τ l = z4iM K τ l := inf_of_le_left (M_le_Vc h)
  have hrc := Subgroup.relIndex_mul_card (H := z4iM K τ l) (K := z4iVc K t τ l)
  rw [hinf, card_M h, card_Vc h] at hrc
  omega

private lemma cent_Y_of_mem_K1 (h : ZEData Q Y V V' B K ρ t τ l) {u : H}
    (hu : u ∈ z4iK1 K τ) : ∀ y ∈ Y, u * y = y * u := by
  intro y hy
  have hmem : u ∈ z4iF K t τ ⊓ centralizer (Y : Set H) := by
    rw [h.F_inf_cent_Y]
    exact hu
  exact (Subgroup.mem_centralizer_iff.mp hmem.2 y hy).symm

theorem invol_M (h : ZEData Q Y V V' B K ρ t τ l) {u : H} (hu : u ∈ z4iM K τ l)
    (hu2 : u * u = 1) :
    (∀ y ∈ Y, u * y = y * u) ∨ (∃ w ∈ K, u = w * l * w⁻¹) ∨
      (∃ w ∈ K, u = w * (τ * l) * w⁻¹) := by
  obtain ⟨k, hk, b, c, hku⟩ := (mem_M_iff h).mp hu
  fin_cases b <;> fin_cases c
  · left
    exact cent_Y_of_mem_K1 h (by
      rw [mem_K1_iff h]
      exact ⟨k, hk, 0, by rw [hku]; simp⟩)
  · right; left
    have hul : u = l * (l * k * l) := by
      rw [hku]
      simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one, one_mul]
      rw [show l * (l * k * l) = (l * l) * k * l by group, h.l_sq]
      group
    have hs : l * k * l ∈ K := by
      have h' := h.l_norm_K k hk
      rwa [inv_eq_of_mul_eq_one_right h.l_sq] at h'
    exact h.invol_lK u ⟨l * k * l, hs, hul⟩ hu2
  · left
    exact cent_Y_of_mem_K1 h (by
      rw [mem_K1_iff h]
      exact ⟨k, hk, 1, by rw [hku]; simp⟩)
  · right; right
    have hT : τ * l ∈ z4iT3 t τ l :=
      (z4iT3 t τ l).mul_mem (tau_mem_T3 t τ l) (l_mem_T3 t τ l)
    have htaul2 : (τ * l) * (τ * l) = 1 := h.T3_sq (τ * l) hT
    have hs : (τ * l) * k * (τ * l) ∈ K := by
      have h' := h.T3_norm_K (τ * l) hT k hk
      rwa [inv_eq_of_mul_eq_one_right htaul2] at h'
    have hul : u = (τ * l) * ((τ * l) * k * (τ * l)) := by
      rw [hku]
      simp only [Fin.val_one, pow_one, Fin.val_zero, pow_zero, mul_one]
      calc k * τ * l = k * (τ * l) := by group
        _ = (τ * l) * ((τ * l) * k * (τ * l)) := by
            rw [show (τ * l) * ((τ * l) * k * (τ * l)) =
              ((τ * l) * (τ * l)) * k * (τ * l) by group, htaul2]
            group
    exact h.invol_taulK u ⟨(τ * l) * k * (τ * l), hs, hul⟩ hu2

end ZEData

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

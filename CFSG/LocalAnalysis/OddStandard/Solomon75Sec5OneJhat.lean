module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneT8
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4Conj

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG
open scoped commutatorElement

section Lift

variable {n : ℕ}

@[expose] noncomputable def lift8 (hn : 8 ≤ n) : Perm (Fin 8) →* Perm (Fin n) :=
  Perm.viaEmbeddingHom (Fin.castLEEmb hn)

theorem lift8_apply_castLE (hn : 8 ≤ n) (g : Perm (Fin 8)) (i : Fin 8) :
    lift8 hn g (Fin.castLE hn i) = Fin.castLE hn (g i) := by
  simp only [lift8, Perm.viaEmbeddingHom_apply]
  exact Equiv.Perm.viaEmbedding_apply g (Fin.castLEEmb hn) i

theorem lift8_apply_of_le (hn : 8 ≤ n) (g : Perm (Fin 8)) {x : Fin n} (hx : 8 ≤ x.val) :
    lift8 hn g x = x := by
  simp only [lift8, Perm.viaEmbeddingHom_apply]
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i, rfl⟩
  have := i.2
  simp at hx
  omega

theorem lift8_injective (hn : 8 ≤ n) : Function.Injective (lift8 hn) :=
  Perm.viaEmbeddingHom_injective _

theorem sign_lift8 (hn : 8 ≤ n) (σ : Perm (Fin 8)) : Perm.sign (lift8 hn σ) = Perm.sign σ := by
  classical
  have h := Equiv.Perm.sign_extendDomain σ
    (Equiv.ofInjective (Fin.castLEEmb hn).1 (Fin.castLEEmb hn).2)
  rw [← h]
  simp only [lift8, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding]
  congr

theorem card_support_lift8 (hn : 8 ≤ n) (σ : Perm (Fin 8)) :
    (lift8 hn σ).support.card = σ.support.card := by
  classical
  have h := Equiv.Perm.card_support_extend_domain
    (Equiv.ofInjective (Fin.castLEEmb hn).1 (Fin.castLEEmb hn).2) (g := σ)
  rw [← h]
  simp only [lift8, Perm.viaEmbeddingHom_apply, Perm.viaEmbedding]
  congr

theorem lift8_swap (hn : 8 ≤ n) (a b : Fin 8) :
    lift8 hn (swap a b) = swap (Fin.castLE hn a) (Fin.castLE hn b) := by
  refine Equiv.Perm.ext fun x => ?_
  by_cases hx : x.val < 8
  · obtain ⟨i, rfl⟩ : ∃ i : Fin 8, Fin.castLE hn i = x := ⟨⟨x.val, hx⟩, Fin.ext rfl⟩
    rw [lift8_apply_castLE]
    exact ((Fin.castLE_injective hn).swap_apply a b i).symm
  · rw [lift8_apply_of_le hn _ (by omega)]
    rw [swap_apply_of_ne_of_ne]
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro h; have := congrArg Fin.val h; simp at this; omega

end Lift

section Gens

open AhatData

variable {n k : ℕ} {K : Type} [Group K]

theorem pairEmb_eq_castLE (hn : 8 ≤ n) (hkn : 2 * k ≤ n) (hk4 : 4 ≤ k) (a : Fin 8) :
    pairEmb n k hkn (⟨a.val / 2, by omega⟩, ⟨a.val % 2, by omega⟩) = Fin.castLE hn a := by
  apply Fin.ext
  simp only [pairEmb, Function.Embedding.coeFn_mk, Fin.val_castLE]
  omega

theorem stdInv_castLE (hn : 8 ≤ n) (hkn : 2 * k ≤ n) (hk4 : 4 ≤ k) {a b : Fin 8}
    (hab : a.val / 2 = b.val / 2) (hne : a ≠ b) :
    stdInv n k hkn (Fin.castLE hn a) = Fin.castLE hn b := by
  have h1 := pairEmb_eq_castLE hn hkn hk4 a
  have h2 := pairEmb_eq_castLE hn hkn hk4 b
  have hsw : ∀ x y : Fin 2, x ≠ y → Equiv.swap (0 : Fin 2) 1 x = y := by decide
  have hr : Equiv.swap (0 : Fin 2) 1 ⟨a.val % 2, by omega⟩ = ⟨b.val % 2, by omega⟩ := by
    apply hsw
    intro h
    have h' : a.val % 2 = b.val % 2 := congrArg Fin.val h
    exact hne (Fin.ext (by omega))
  rw [← h1, stdInv_apply_pair, hr, ← h2]
  congr 1
  exact Prod.ext (Fin.ext hab) rfl

theorem exists_lift_dbl (hn : 8 ≤ n) (hkn : 2 * k ≤ n) (hk4 : 4 ≤ k) (C : CoverSetup n K)
    {α : MulAut K} (h : C.Induces α (stdInv n k hkn)) {a b c d : Fin 8}
    (hab : a.val / 2 = b.val / 2) (hcd : c.val / 2 = d.val / 2) (hne1 : a ≠ b) (hne2 : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ∃ x ∈ fixSub α, C.ρ x = lift8 hn (swap a b * swap c d) := by
  have hinj := Fin.castLE_injective hn
  rw [map_mul, lift8_swap, lift8_swap]
  have hab' : Fin.castLE hn a ≠ Fin.castLE hn b := fun e => hne1 (hinj e)
  have hcd' : Fin.castLE hn c ≠ Fin.castLE hn d := fun e => hne2 (hinj e)
  have hac' : Fin.castLE hn a ≠ Fin.castLE hn c := fun e => hac (hinj e)
  have had' : Fin.castLE hn a ≠ Fin.castLE hn d := fun e => had (hinj e)
  have hbc' : Fin.castLE hn b ≠ Fin.castLE hn c := fun e => hbc (hinj e)
  have hbd' : Fin.castLE hn b ≠ Fin.castLE hn d := fun e => hbd (hinj e)
  obtain ⟨x, hx⟩ := C.exists_ρ_eq (sign_swap_mul_swap hab' hcd')
  refine ⟨x, ?_, hx⟩
  exact h.apply_eq_of_dbl_swapped hab' hac' had' hbc' hbd' hcd'
    (stdInv_castLE hn hkn hk4 hab hne1) (stdInv_castLE hn hkn hk4 hab.symm hne1.symm)
    (stdInv_castLE hn hkn hk4 hcd hne2) (stdInv_castLE hn hkn hk4 hcd.symm hne2.symm) hx

theorem lift8_eq_pairHom (hn : 8 ≤ n) (hkn : 2 * k ≤ n) (hk4 : 4 ≤ k) {v : Perm (Fin 8)}
    {τ : Perm (Fin k)}
    (hv : ∀ (q r : ℕ) (hq : q < 4) (hr : r < 2),
      (v ⟨2 * q + r, by omega⟩).val = 2 * (τ ⟨q, by omega⟩).val + r)
    (hτ2 : ∀ q : Fin k, 4 ≤ q.val → τ q = q) :
    lift8 hn v = pairHom n k hkn τ := by
  refine Equiv.Perm.ext fun x => ?_
  by_cases hx : x ∈ Set.range (pairEmb n k hkn)
  · obtain ⟨⟨q, r⟩, rfl⟩ := hx
    rw [pairHom_apply_pair]
    by_cases hq : q.val < 4
    · have hpt : pairEmb n k hkn (q, r) = Fin.castLE hn ⟨2 * q.val + r.val, by
          have := r.2; omega⟩ := Fin.ext (by simp [pairEmb])
      rw [hpt, lift8_apply_castLE]
      apply Fin.ext
      have h1 := hv q.val r.val hq r.2
      simp only [pairEmb, Function.Embedding.coeFn_mk, Fin.val_castLE]
      omega
    · rw [hτ2 q (by omega)]
      apply lift8_apply_of_le
      have := r.2
      simp only [pairEmb, Function.Embedding.coeFn_mk]
      omega
  · rw [pairHom_apply_of_notMem τ x hx]
    apply lift8_apply_of_le
    by_contra hlt
    apply hx
    refine ⟨(⟨x.val / 2, by omega⟩, ⟨x.val % 2, by omega⟩), ?_⟩
    apply Fin.ext
    simp only [pairEmb, Function.Embedding.coeFn_mk]
    omega

@[expose] def tauA (hk4 : 4 ≤ k) : Perm (Fin k) :=
  swap ⟨0, by omega⟩ ⟨1, by omega⟩ * swap ⟨2, by omega⟩ ⟨3, by omega⟩

@[expose] def tauB (hk4 : 4 ≤ k) : Perm (Fin k) :=
  swap ⟨0, by omega⟩ ⟨2, by omega⟩ * swap ⟨1, by omega⟩ ⟨3, by omega⟩

theorem tauA_mem_alt (hk4 : 4 ≤ k) : tauA hk4 ∈ alternatingGroup (Fin k) := by
  rw [Perm.mem_alternatingGroup, tauA, Perm.sign_mul, Perm.sign_swap, Perm.sign_swap]
  · decide
  · intro h; have := congrArg Fin.val h; simp at this
  · intro h; have := congrArg Fin.val h; simp at this

theorem tauB_mem_alt (hk4 : 4 ≤ k) : tauB hk4 ∈ alternatingGroup (Fin k) := by
  rw [Perm.mem_alternatingGroup, tauB, Perm.sign_mul, Perm.sign_swap, Perm.sign_swap]
  · decide
  · intro h; have := congrArg Fin.val h; simp at this
  · intro h; have := congrArg Fin.val h; simp at this

theorem lift8_v1_eq (hn : 8 ≤ n) (hkn : 2 * k ≤ n) (hk4 : 4 ≤ k) :
    lift8 hn (swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7) = pairHom n k hkn (tauA hk4) := by
  refine lift8_eq_pairHom hn hkn hk4 (fun q r hq hr => ?_) (fun q hq => ?_)
  · interval_cases q <;> interval_cases r <;> simp [tauA, Equiv.swap_apply_def, Fin.ext_iff]
  · have h0 : q.val ≠ 0 := by omega
    have h1 : q.val ≠ 1 := by omega
    have h2 : q.val ≠ 2 := by omega
    have h3 : q.val ≠ 3 := by omega
    simp [tauA, Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]

theorem lift8_v2_eq (hn : 8 ≤ n) (hkn : 2 * k ≤ n) (hk4 : 4 ≤ k) :
    lift8 hn (swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7) = pairHom n k hkn (tauB hk4) := by
  refine lift8_eq_pairHom hn hkn hk4 (fun q r hq hr => ?_) (fun q hq => ?_)
  · interval_cases q <;> interval_cases r <;> simp [tauB, Equiv.swap_apply_def, Fin.ext_iff]
  · have h0 : q.val ≠ 0 := by omega
    have h1 : q.val ≠ 1 := by omega
    have h2 : q.val ≠ 2 := by omega
    have h3 : q.val ≠ 3 := by omega
    simp [tauB, Equiv.swap_apply_def, Fin.ext_iff, h0, h1, h2, h3]

theorem exists_lift_T8 [Finite K] (hn : 8 ≤ n) (hkn : 2 * k ≤ n) (hk4 : 4 ≤ k) (C : CoverSetup n K)
    {α : MulAut K} (h : C.Induces α (stdInv n k hkn)) :
    ∀ t ∈ T8, ∃ x ∈ fixSub α, C.ρ x = lift8 hn t := by
  intro t ht
  induction ht using Subgroup.closure_induction with
  | mem g hg =>
    have hg' : g ∈ T8gens := hg
    simp only [T8gens, List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact exists_lift_dbl hn hkn hk4 C h (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact exists_lift_dbl hn hkn hk4 C h (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact exists_lift_dbl hn hkn hk4 C h (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact exists_lift_dbl hn hkn hk4 C h (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact exists_lift_dbl hn hkn hk4 C h (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · exact exists_lift_dbl hn hkn hk4 C h (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    · rw [lift8_v1_eq hn hkn hk4]
      exact h.exists_lift_pairHom _ (tauA_mem_alt hk4)
    · rw [lift8_v2_eq hn hkn hk4]
      exact h.exists_lift_pairHom _ (tauB_mem_alt hk4)
  | one => exact ⟨1, one_mem _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, hx, hxa⟩ := ha
    obtain ⟨y, hy, hyb⟩ := hb
    exact ⟨x * y, mul_mem hx hy, by rw [map_mul, map_mul, hxa, hyb]⟩
  | inv a _ ha =>
    obtain ⟨x, hx, hxa⟩ := ha
    exact ⟨x⁻¹, inv_mem hx, by rw [map_inv, map_inv, hxa]⟩

end Gens

section Jhat

open AhatData

variable {n : ℕ} {K : Type} [Group K] [Finite K]

theorem exists_jhat (hn : 8 ≤ n) (C : CoverSetup n K) {α : MulAut K} {σ : Perm (Fin n)}
    (h : C.Induces α σ) (hσ : σ * σ = 1) {k : ℕ} (hk : σ.support.card = 2 * k) (hk4 : 4 ≤ k) :
    ∃ J : Subgroup K, J ≤ fixSub α ∧ Nat.card J = 64 ∧ Nat.card (Subgroup.center J) ≤ 4 ∧
      J ≤ Subgroup.closure {x | x ∈ J ∧ x * x = 1} := by
  have hkn : 2 * k ≤ n := by
    have := Finset.card_le_univ σ.support
    simpa [hk] using this
  obtain ⟨g, hg⟩ := exists_conj_stdInv (h := hkn) hσ hk
  set C' : CoverSetup n K := C.conjPerm g with hC'
  have hI : C'.Induces α (stdInv n k hkn) := by
    have := h.conjPerm g
    rwa [hg] at this
  set T : Subgroup (Perm (Fin n)) := T8.map (lift8 hn) with hT
  have hTalt : ∀ t ∈ T, sign t = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [sign_lift8]
    exact Perm.mem_alternatingGroup.1 (T8_le_alternatingGroup ht)
  have hTlift : ∀ t ∈ T, ∃ x ∈ fixSub α, C'.ρ x = t := by
    rintro _ ⟨t, ht, rfl⟩
    exact exists_lift_T8 hn hkn hk4 C' hI t ht
  set J : Subgroup K := T.comap C'.ρ with hJ
  have hJmem : ∀ x, x ∈ J ↔ C'.ρ x ∈ T := fun x => Iff.rfl
  have hcenJ : ∀ x ∈ Subgroup.center K, x ∈ J := fun x hx => by
    rw [hJmem, (C'.ρ_eq_one_iff).2 hx]; exact one_mem _
  let φ : ↥J →* ↥T := (C'.ρ.comp J.subtype).codRestrict T (fun x => x.2)
  have hφapp : ∀ x : ↥J, ((φ x : ↥T) : Perm (Fin n)) = C'.ρ x := fun x => rfl
  have hφsurj : Function.Surjective φ := by
    rintro ⟨t, ht⟩
    obtain ⟨x, -, hxt⟩ := hTlift t ht
    exact ⟨⟨x, by rw [hJmem, hxt]; exact ht⟩, Subtype.ext hxt⟩
  have hkerφ : Nat.card φ.ker = 2 := by
    have e : φ.ker ≃ Subgroup.center K :=
      { toFun := fun x => ⟨(x.1 : K), (C'.ρ_eq_one_iff).1 (by
          have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
          simpa [hφapp] using this)⟩
        invFun := fun c => ⟨⟨c, hcenJ c c.2⟩, MonoidHom.mem_ker.2 (Subtype.ext (by
          rw [hφapp]; exact (C'.ρ_eq_one_iff).2 c.2))⟩
        left_inv := fun x => rfl
        right_inv := fun c => rfl }
    rw [Nat.card_congr e]
    exact C'.center_card
  have hcardT : Nat.card T = 32 := by
    rw [hT, Subgroup.card_map_of_injective (lift8_injective hn)]
    exact T8_card
  have hcardJ : Nat.card J = 64 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : φ.range = ⊤ := MonoidHom.range_eq_top.2 hφsurj
    rw [h2, Subgroup.card_top, hkerφ, hcardT] at h1
    omega
  have hcenT : Nat.card (Subgroup.center T) = 2 := by
    have e : ↥T8 ≃* ↥T := Subgroup.equivMapOfInjective T8 (lift8 hn) (lift8_injective hn)
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact T8_center_card
  have hcenJ4 : Nat.card (Subgroup.center J) ≤ 4 := by
    let χ : ↥(Subgroup.center J) →* ↥T := φ.comp (Subgroup.center J).subtype
    have hrange : χ.range ≤ Subgroup.center T := by
      rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro u
      obtain ⟨y, rfl⟩ := hφsurj u
      show φ y * φ x = φ x * φ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 x.2 y]
    have hkerle : Nat.card χ.ker ≤ Nat.card φ.ker := by
      let f : χ.ker → φ.ker := fun x => ⟨(x.1 : ↥J), MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 x.2)⟩
      exact Nat.card_le_card_of_injective f (fun a b hab => by
        have := congrArg (fun w : φ.ker => (w : ↥J)) hab
        exact Subtype.ext (Subtype.ext this))
    have h1 := Subgroup.card_ker_mul_card_range χ
    have h2 : Nat.card χ.range ≤ Nat.card (Subgroup.center T) := Subgroup.card_le_of_le hrange
    rw [← h1]
    calc Nat.card χ.ker * Nat.card χ.range ≤ 2 * 2 :=
          Nat.mul_le_mul (hkerφ ▸ hkerle) (hcenT ▸ h2)
      _ = 4 := by norm_num
  have hαz : ∀ x ∈ Subgroup.center K, α x = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, map_one]
    · have hαx : α x ∈ Subgroup.center K := by
        have h := Subgroup.map_center_eq α
        rw [← h]
        exact ⟨x, hx, rfl⟩
      exact C'.center_eq_of_ne_one hαx hx (fun h1 => hx1 (α.injective (by rw [h1, map_one]))) hx1
  have hJfix : J ≤ fixSub α := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hTlift (C'.ρ x) hx
    have hc : y⁻¹ * x ∈ Subgroup.center K := by
      rw [← C'.ρ_eq_one_iff, map_mul, map_inv, hyx, inv_mul_cancel]
    have h1 : α (y⁻¹ * x) = y⁻¹ * x := hαz _ hc
    have h2 : α y = y := mem_fixSub.1 hy
    show α x = x
    have : x = y * (y⁻¹ * x) := by group
    rw [this, map_mul, h2, h1]
  refine ⟨J, hJfix, hcardJ, hcenJ4, ?_⟩
  set J₀ : Subgroup K := Subgroup.closure {x | x ∈ J ∧ x * x = 1} with hJ₀
  have hTle : T ≤ J₀.map C'.ρ := by
    have hTeq : T = Subgroup.closure (lift8 hn ''
        {t : Perm (Fin 8) | t ∈ T8 ∧ t * t = 1 ∧ t.support.card = 8}) := by
      rw [hT, ← MonoidHom.map_closure, ← T8_eq_closure_involutions]
    rw [hTeq, Subgroup.closure_le]
    rintro _ ⟨t₈, ⟨ht8, ht2, ht8c⟩, rfl⟩
    have htT : lift8 hn t₈ ∈ T := ⟨t₈, ht8, rfl⟩
    obtain ⟨x, -, hxρ⟩ := hTlift _ htT
    have hxJ : x ∈ J := by rw [hJmem, hxρ]; exact htT
    have hsq : C'.ρ x * C'.ρ x = 1 := by rw [hxρ, ← map_mul, ht2, map_one]
    have hx2 : x * x = 1 :=
      (C'.sq_eq_one_iff_dvd hn hsq).2 (by rw [hxρ, card_support_lift8, ht8c])
    exact ⟨x, Subgroup.subset_closure ⟨hxJ, hx2⟩, hxρ⟩
  have heT : lift8 hn (swap 0 1 * swap 2 3) ∈ T := ⟨_, swap_mul_swap_mem_T8, rfl⟩
  obtain ⟨y, hyJ₀, hyρ⟩ := hTle heT
  have hyρ' : C'.ρ y = swap (Fin.castLE hn 0) (Fin.castLE hn 1) *
      swap (Fin.castLE hn 2) (Fin.castLE hn 3) := by
    rw [hyρ, map_mul, lift8_swap, lift8_swap]
  have hinj := Fin.castLE_injective hn
  have hyy : y * y ≠ 1 :=
    C'.sq_dbl_ne_one hn (fun e => absurd (hinj e) (by decide)) (fun e => absurd (hinj e)
      (by decide)) (fun e => absurd (hinj e) (by decide)) (fun e => absurd (hinj e)
      (by decide)) (fun e => absurd (hinj e) (by decide)) (fun e => absurd (hinj e)
      (by decide)) hyρ'
  have hyyc : y * y ∈ Subgroup.center K := by
    apply C'.sq_mem_center
    rw [hyρ, ← map_mul]
    have : (swap (0 : Fin 8) 1 * swap 2 3) * (swap 0 1 * swap 2 3) = 1 := by decide
    rw [this, map_one]
  have hcenJ₀ : ∀ c ∈ Subgroup.center K, c ∈ J₀ := by
    intro c hc
    by_cases hc1 : c = 1
    · rw [hc1]; exact one_mem _
    · have : c = y * y := C'.center_eq_of_ne_one hc hyyc hc1 hyy
      rw [this]; exact mul_mem hyJ₀ hyJ₀
  intro x hx
  obtain ⟨y', hy'J₀, hy'ρ⟩ := hTle hx
  have hc : y'⁻¹ * x ∈ Subgroup.center K := by
    rw [← C'.ρ_eq_one_iff, map_mul, map_inv, hy'ρ, inv_mul_cancel]
  have : x = y' * (y'⁻¹ * x) := by group
  rw [this]
  exact mul_mem hy'J₀ (hcenJ₀ _ hc)

end Jhat

end CFSG.OddStandard.Solomon75

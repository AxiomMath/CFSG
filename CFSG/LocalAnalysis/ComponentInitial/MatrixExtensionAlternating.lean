module

public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionBasic

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace MatrixExtension

open Matrix
open scoped commutatorElement

theorem exists_ne_of_four {n : ℕ} (hn : 4 ≤ n) (a b c : Fin n) :
    ∃ l : Fin n, l ≠ a ∧ l ≠ b ∧ l ≠ c := by
  classical
  by_contra! h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c} := fun z _ => by
    by_cases hza : z = a
    · simp [hza]
    by_cases hzb : z = b
    · simp [hzb]
    simp [h z hza hzb]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_le_three (a := a) (b := b) (c := c)
  omega

theorem exists_ne_of_five {n : ℕ} (hn : 5 ≤ n) (a b c d : Fin n) :
    ∃ l : Fin n, l ≠ a ∧ l ≠ b ∧ l ≠ c ∧ l ≠ d := by
  classical
  by_contra! h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, b, c, d} := fun z _ => by
    by_cases hza : z = a
    · simp [hza]
    by_cases hzb : z = b
    · simp [hzb]
    by_cases hzc : z = c
    · simp [hzc]
    simp [h z hza hzb hzc]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, Fintype.card_fin] at this
  have := Finset.card_le_four (a := a) (b := b) (c := c) (d := d)
  omega

section Off

variable {n : ℕ}

theorem binaryTransvection_congr_binaryOff_of_ne {a b : Fin n} (h : a ≠ b) {i j : Fin n}
    (hi : i ≠ b) (hj : j ≠ b) :
    (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2)) * binaryOff i j *
        (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = binaryOff i j := by
  rw [binaryTransvection_congr_binaryOff, ite_eq_right hi, ite_eq_right hj, add_zero, add_zero]

theorem binaryTransvection_congr_binaryOff_left {a i : Fin n} (h : a ≠ i) {j : Fin n}
    (hj : j ≠ i) :
    (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2)) * binaryOff i j *
        (binaryTransvection h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      binaryOff i j + binaryOff a j := by
  rw [binaryTransvection_congr_binaryOff, ite_eq_left rfl, ite_eq_right hj, add_zero]

end Off

section Core

variable {n : ℕ} {M : Type*} [AddCommGroup M]
  {act : GL (Fin n) (ZMod 2) →* AddMonoid.End M} {π : M →+ Matrix (Fin n) (Fin n) (ZMod 2)}

local notation "𝕏" => binaryTransvection

theorem act_sub_mem_ker {g : GL (Fin n) (ZMod 2)}
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) {x y : M}
    (h : (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x * (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      π y) : act g x - y ∈ π.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, hπact, h]
  exact sub_self _

theorem act_binaryTransvection_eq_of_ne (hn : 5 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    {a b : Fin n} (hab : a ≠ b) {i j : Fin n} (hi : i ≠ b) (hj : j ≠ b) {x : M}
    (hx : π x = binaryOff i j) : act (𝕏 hab) x = x := by
  obtain ⟨l, hla, hlb, hli, hlj⟩ := exists_ne_of_five hn a b i j
  rw [← commutatorElement_binaryTransvection hla.symm hlb hab]
  refine act_commutatorElement_apply_eq act hC (act_sub_mem_ker hπact ?_)
    (act_sub_mem_ker hπact ?_)
  · rw [hx, binaryTransvection_congr_binaryOff_of_ne _ (Ne.symm hli) (Ne.symm hlj)]
  · rw [hx, binaryTransvection_congr_binaryOff_of_ne _ hi hj]

theorem act_sub_sub_mem_ker
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) {a i : Fin n} (hai : a ≠ i) {j : Fin n}
    (hji : j ≠ i) {x y : M} (hx : π x = binaryOff i j) (hy : π y = binaryOff a j) :
    act (𝕏 hai) x - x - y ∈ π.ker := by
  rw [AddMonoidHom.mem_ker, map_sub, map_sub, hπact, hx, hy,
    binaryTransvection_congr_binaryOff_left _ hji]
  abel

variable [Module (ZMod 2) M]

theorem alt_defect_eq_of_commutator
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hF1 : ∀ {a b : Fin n} (hab : a ≠ b) {i j : Fin n}, i ≠ b → j ≠ b → ∀ {x : M},
      π x = binaryOff i j → act (𝕏 hab) x = x)
    {o : Fin n → Fin n → M} (ho : ∀ i j, π (o i j) = binaryOff i j) {a i j k : Fin n}
    (hai : a ≠ i) (hak : a ≠ k) (hki : k ≠ i) (hji : j ≠ i) (hjk : j ≠ k) :
    act (𝕏 hai) (o i j) - o i j - o a j = act (𝕏 hak) (o k j) - o k j - o a j := by
  obtain ⟨c₁, hc₁, e₁⟩ : ∃ c ∈ π.ker, act (𝕏 hki) (o i j) = o i j + o k j + c :=
    ⟨_, act_sub_sub_mem_ker hπact hki hji (ho i j) (ho k j), by abel⟩
  obtain ⟨c₂, hc₂, e₂⟩ : ∃ c ∈ π.ker, act (𝕏 hak) (o k j) = o k j + o a j + c :=
    ⟨_, act_sub_sub_mem_ker hπact hak hjk (ho k j) (ho a j), by abel⟩
  have f₁ := hF1 hak hki.symm hjk (ho i j)
  have f₂ := hF1 hki hki hji (ho k j)
  have f₃ := hF1 hki hai hji (ho a j)
  have f₄ := hF1 hak hak hjk (ho a j)
  have k₁ : ∀ g, act g c₁ = c₁ := fun g => hC g _ hc₁
  have k₂ : ∀ g, act g c₂ = c₂ := fun g => hC g _ hc₂
  have hcomm : act (𝕏 hai) (o i j) =
      act (𝕏 hak) (act (𝕏 hki) (act (𝕏 hak) (act (𝕏 hki) (o i j)))) := by
    rw [← commutatorElement_binaryTransvection hak hki hai, commutatorElement_def,
      binaryTransvection_inv, binaryTransvection_inv, act_mul_apply, act_mul_apply,
      act_mul_apply]
  rw [hcomm, e₁, e₂]
  simp only [map_add, f₁, e₁, e₂, f₂, f₃, f₄, k₁, k₂]
  linear_combination (norm := match_scalars <;> decide) (0 : ZMod 2) • (rfl : c₁ = c₁)

theorem alt_defect_eq_of_commute
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    {o : Fin n → Fin n → M} (ho : ∀ i j, π (o i j) = binaryOff i j) {a b i j : Fin n}
    (hai : a ≠ i) (hbj : b ≠ j) (hib : i ≠ b) (hja : j ≠ a) (hij : i ≠ j) :
    act (𝕏 hai) (o i b) - o i b - o a b = act (𝕏 hbj) (o a j) - o a j - o a b := by
  obtain ⟨c₁, hc₁, e₁⟩ : ∃ c ∈ π.ker, act (𝕏 hbj) (o i j) = o i j + o i b + c :=
    ⟨_, act_sub_sub_mem_ker hπact hbj hij ((ho i j).trans (binaryOff_comm i j))
      ((ho i b).trans (binaryOff_comm i b)), by abel⟩
  obtain ⟨c₂, hc₂, e₂⟩ : ∃ c ∈ π.ker, act (𝕏 hai) (o i j) = o i j + o a j + c :=
    ⟨_, act_sub_sub_mem_ker hπact hai hij.symm (ho i j) (ho a j), by abel⟩
  have k₁ : ∀ g, act g c₁ = c₁ := fun g => hC g _ hc₁
  have k₂ : ∀ g, act g c₂ = c₂ := fun g => hC g _ hc₂
  have h := congrArg (fun g => act g (o i j)) (binaryTransvection_commute hai hbj hib hja)
  simp only [act_mul_apply, e₁, e₂, map_add, k₁, k₂] at h
  linear_combination (norm := match_scalars <;> decide) (1 : ZMod 2) • h

theorem alt_defect_eq_add
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hF1 : ∀ {a b : Fin n} (hab : a ≠ b) {i j : Fin n}, i ≠ b → j ≠ b → ∀ {x : M},
      π x = binaryOff i j → act (𝕏 hab) x = x)
    {o : Fin n → Fin n → M} (ho : ∀ i j, π (o i j) = binaryOff i j)
    (hod : ∀ i, o i i = 0) {a i j : Fin n} (hai : a ≠ i) (hij : i ≠ j) (haj : a ≠ j) :
    act (𝕏 haj) (o i j) - o i j - o a i =
      (act (𝕏 hai) (o a i) - o a i) + (act (𝕏 hij) (o a j) - o a j - o a i) := by
  obtain ⟨c₁, hc₁, e₁⟩ : ∃ c ∈ π.ker, act (𝕏 hij) (o i j) = o i j + c :=
    ⟨_, by
      have h := act_sub_sub_mem_ker hπact hij hij (x := o i j) (y := o i i)
        ((ho i j).trans (binaryOff_comm i j)) (ho i i)
      rwa [hod, sub_zero] at h, by abel⟩
  obtain ⟨c₂, hc₂, e₂⟩ : ∃ c ∈ π.ker, act (𝕏 hai) (o i j) = o i j + o a j + c :=
    ⟨_, act_sub_sub_mem_ker hπact hai hij.symm (ho i j) (ho a j), by abel⟩
  obtain ⟨c₃, hc₃, e₃⟩ : ∃ c ∈ π.ker, act (𝕏 hij) (o a j) = o a j + o a i + c :=
    ⟨_, act_sub_sub_mem_ker hπact hij haj ((ho a j).trans (binaryOff_comm a j))
      ((ho a i).trans (binaryOff_comm a i)), by abel⟩
  obtain ⟨c₄, hc₄, e₄⟩ : ∃ c ∈ π.ker, act (𝕏 hai) (o a i) = o a i + c :=
    ⟨_, by
      have h := act_sub_sub_mem_ker hπact hai hai (x := o a i) (y := o a a)
        ((ho a i).trans (binaryOff_comm a i)) (ho a a)
      rwa [hod, sub_zero] at h, by abel⟩
  have f₁ := hF1 hai hai hij.symm (ho a j)
  have k₁ : ∀ g, act g c₁ = c₁ := fun g => hC g _ hc₁
  have k₂ : ∀ g, act g c₂ = c₂ := fun g => hC g _ hc₂
  have k₃ : ∀ g, act g c₃ = c₃ := fun g => hC g _ hc₃
  have hcomm : act (𝕏 haj) (o i j) =
      act (𝕏 hai) (act (𝕏 hij) (act (𝕏 hai) (act (𝕏 hij) (o i j)))) := by
    rw [← commutatorElement_binaryTransvection hai hij haj, commutatorElement_def,
      binaryTransvection_inv, binaryTransvection_inv, act_mul_apply, act_mul_apply,
      act_mul_apply]
  rw [hcomm, e₁, e₃, e₄]
  simp only [map_add, e₁, e₂, e₃, e₄, f₁, k₁, k₂, k₃]
  linear_combination (norm := match_scalars <;> decide) (0 : ZMod 2) • (rfl : c₁ = c₁)

theorem alt_defect_symm (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hF1 : ∀ {a b : Fin n} (hab : a ≠ b) {i j : Fin n}, i ≠ b → j ≠ b → ∀ {x : M},
      π x = binaryOff i j → act (𝕏 hab) x = x)
    {o : Fin n → Fin n → M} (ho : ∀ i j, π (o i j) = binaryOff i j)
    (hos : ∀ i j, o i j = o j i) {a j i i' : Fin n} (hai : a ≠ i) (hji : j ≠ i)
    (hji' : j ≠ i') (hai' : a ≠ i') :
    act (𝕏 hai) (o i j) - o i j - o a j = act (𝕏 hji') (o i' a) - o i' a - o j a := by
  by_cases hii' : i = i'
  · subst hii'
    obtain ⟨k, hka, hki, hkj⟩ := exists_ne_of_four hn a i j
    have h1 := alt_defect_eq_of_commute hπact hC ho hai (Ne.symm hkj) hji.symm hka hki.symm
    have h2 := alt_defect_eq_of_commutator hπact hC hF1 ho (a := j) (i := k) (j := a) (k := i)
      hkj.symm hji hki.symm hka.symm hai
    rw [h1, hos a k, hos a j]
    exact h2
  · have h1 := alt_defect_eq_of_commute hπact hC ho hai hji' hji.symm (Ne.symm hai') hii'
    rw [h1, hos a i', hos a j]

theorem alt_act_eq_self (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hF1 : ∀ {a b : Fin n} (hab : a ≠ b) {i j : Fin n}, i ≠ b → j ≠ b → ∀ {x : M},
      π x = binaryOff i j → act (𝕏 hab) x = x)
    {o : Fin n → Fin n → M} (ho : ∀ i j, π (o i j) = binaryOff i j)
    (hos : ∀ i j, o i j = o j i) (hod : ∀ i, o i i = 0) {a i : Fin n} (hai : a ≠ i) :
    act (𝕏 hai) (o a i) = o a i := by
  obtain ⟨j, hja, hji⟩ := exists_ne_ne_of_three_le (by omega) a i
  have h := alt_defect_eq_add hπact hC hF1 ho hod hai hji.symm hja.symm
  have h' := alt_defect_symm hn hπact hC hF1 ho hos (j := i) (i := j) (i' := j) hja.symm
    hji.symm hji.symm hja.symm
  rw [hos j i, hos j a, hos i a] at h'
  rw [h'] at h
  linear_combination (norm := match_scalars <;> decide) (1 : ZMod 2) • h

theorem zmod_two_add_self (x : M) : x + x = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem exists_off_equivariant_lifts (hn : 4 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hF1 : ∀ {a b : Fin n} (hab : a ≠ b) {i j : Fin n}, i ≠ b → j ≠ b → ∀ {x : M},
      π x = binaryOff i j → act (𝕏 hab) x = x)
    (hlift : ∀ i j : Fin n, ∃ x, π x = binaryOff i j) :
    ∃ o : Fin n → Fin n → M, (∀ i j, π (o i j) = binaryOff i j) ∧ (∀ i j, o i j = o j i) ∧
      (∀ i, o i i = 0) ∧ ∀ (a b : Fin n) (h : a ≠ b) (i j : Fin n),
        act (𝕏 h) (o i j) = o i j + (if i = b then o a j else 0) +
          (if j = b then o i a else 0) := by
  classical
  choose p hp using hlift
  set o₀ : Fin n → Fin n → M := fun i j => if i < j then p i j else if j < i then p j i else 0
    with ho₀
  have ho₀π : ∀ i j, π (o₀ i j) = binaryOff i j := by
    intro i j
    simp only [ho₀]
    split_ifs with h₁ h₂
    · exact hp i j
    · rw [hp, binaryOff_comm]
    · rw [le_antisymm (not_lt.mp h₂) (not_lt.mp h₁), binaryOff_self, map_zero]
  have ho₀s : ∀ i j, o₀ i j = o₀ j i := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [ho₀, h, lt_asymm h]
    · rfl
    · simp [ho₀, h, lt_asymm h]
  have ho₀d : ∀ i, o₀ i i = 0 := fun i => by simp [ho₀]
  choose t ht using fun a j : Fin n => exists_ne_ne_of_three_le (by omega : 3 ≤ n) a j
  set d : Fin n → Fin n → M := fun a j =>
    act (𝕏 (ht a j).1.symm) (o₀ (t a j) j) - o₀ (t a j) j - o₀ a j with hd
  have hdmem : ∀ a j, a ≠ j → d a j ∈ π.ker := fun a j haj =>
    act_sub_sub_mem_ker hπact (ht a j).1.symm (ht a j).2.symm (ho₀π _ _) (ho₀π _ _)
  have hdd : ∀ a, d a a = 0 := by
    intro a
    simp only [hd, ho₀d, sub_zero, ho₀s (t a a) a]
    rw [alt_act_eq_self hn hπact hC hF1 ho₀π ho₀s ho₀d (ht a a).1.symm, sub_self]
  have hdk : ∀ a j, d a j ∈ π.ker := fun a j => by
    rcases eq_or_ne a j with rfl | haj
    · rw [hdd]
      exact zero_mem _
    · exact hdmem a j haj
  have hds : ∀ a j, d a j = d j a := by
    intro a j
    rcases eq_or_ne a j with rfl | haj
    · rfl
    · exact alt_defect_symm hn hπact hC hF1 ho₀π ho₀s (ht a j).1.symm (ht a j).2.symm
        (ht j a).1.symm (ht j a).2.symm
  have hdef : ∀ a i j (hai : a ≠ i), j ≠ i → j ≠ a →
      act (𝕏 hai) (o₀ i j) = o₀ i j + o₀ a j + d a j := by
    intro a i j hai hji hja
    by_cases hit : i = t a j
    · subst hit
      simp only [hd]
      abel
    · have h := alt_defect_eq_of_commutator hπact hC hF1 ho₀π hai (ht a j).1.symm (Ne.symm hit)
        hji (ht a j).2.symm
      simp only [hd]
      rw [← h]
      abel
  refine ⟨fun i j => o₀ i j + d i j, fun i j => ?_, fun i j => ?_, fun i => ?_,
    fun a b hab i j => ?_⟩
  · dsimp only
    rw [map_add, ho₀π, (AddMonoidHom.mem_ker).mp (hdk i j), add_zero]
  · dsimp only
    rw [ho₀s, hds]
  · dsimp only
    rw [ho₀d, hdd, add_zero]
  · dsimp only
    rw [map_add, hC _ _ (hdk i j)]
    by_cases hib : i = b <;> by_cases hjb : j = b
    · subst hib
      subst hjb
      simp only [↓reduceIte, ho₀d, map_zero, hdd, zero_add, ho₀s j a, hds j a]
      exact (zmod_two_add_self _).symm
    · subst hib
      rw [ite_eq_left rfl, ite_eq_right hjb, add_zero]
      by_cases hja : j = a
      · subst hja
        rw [ho₀s i j, alt_act_eq_self hn hπact hC hF1 ho₀π ho₀s ho₀d hab, ho₀d, hdd, add_zero,
          add_zero]
      · rw [hdef a i j hab hjb hja]
        abel
    · subst hjb
      rw [ite_eq_right hib, ite_eq_left rfl, add_zero]
      by_cases hia : i = a
      · subst hia
        rw [alt_act_eq_self hn hπact hC hF1 ho₀π ho₀s ho₀d hab, ho₀d, hdd, add_zero, add_zero]
      · rw [ho₀s i j, hdef a j i hab hib hia, ho₀s j i, ho₀s a i, hds a i]
        abel
    · rw [ite_eq_right hib, ite_eq_right hjb, add_zero, add_zero,
        hF1 hab hib hjb (ho₀π i j)]

theorem alt_exists_invariant_complement (hn : 5 ≤ n)
    (hπact : ∀ g x, π (act g x) = (g : Matrix (Fin n) (Fin n) (ZMod 2)) * π x *
      (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) (hC : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hlift : ∀ i j : Fin n, ∃ x, π x = binaryOff i j) :
    ∃ S : AddSubgroup M, (∀ g, ∀ x ∈ S, act g x ∈ S) ∧ (∀ x ∈ S, π x = 0 → x = 0) ∧
      ∀ X ∈ binaryAltMatrices n, ∃ x ∈ S, π x = X := by
  obtain ⟨o, ho, hos, hod, hact⟩ := exists_off_equivariant_lifts (by omega) hπact hC
    (fun hab _ _ hi hj _ hx => act_binaryTransvection_eq_of_ne hn hπact hC hab hi hj hx) hlift
  obtain ⟨hinj, hsurj⟩ := altSection_closure_spec o hod hos π ho
  refine ⟨_, fun g => act_mem_of_closure_eq_top act closure_binaryTransvection ?_ ?_ g, hinj,
    hsurj⟩
  · rintro _ ⟨a, b, h, rfl⟩
    exact ⟨a, b, h, (binaryTransvection_inv h).symm⟩
  · rintro _ ⟨a, b, h, rfl⟩ x hx
    have hmem : ∀ k l, o k l ∈ AddSubgroup.closure (Set.range fun p : Fin n × Fin n =>
        o p.1 p.2) := fun k l => AddSubgroup.subset_closure ⟨(k, l), rfl⟩
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨⟨i, j⟩, rfl⟩ := hy
      change act (𝕏 h) (o i j) ∈ _
      rw [hact]
      refine add_mem (add_mem (hmem i j) ?_) ?_
      · split_ifs
        · exact hmem a j
        · exact zero_mem _
      · split_ifs
        · exact hmem i a
        · exact zero_mem _
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy

end Core

section Group

variable {n : ℕ} {P : Type*} [Group P]

theorem binaryAlt_eq_sum (X : binaryAltMatrices n) :
    X = ∑ p ∈ binaryUpperPairs n, ((X : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2).val •
      (⟨binaryOff p.1 p.2, binaryOff_mem_binaryAltMatrices _ _⟩ : binaryAltMatrices n) := by
  apply Subtype.ext
  refine Eq.trans ?_ (AddSubgroup.val_finsetSum _ _ _).symm
  have hs : ∀ p : Fin n × Fin n, (((((X : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2).val •
      (⟨binaryOff p.1 p.2, binaryOff_mem_binaryAltMatrices _ _⟩ : binaryAltMatrices n)) :
        binaryAltMatrices n) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (X : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2 •
        (single p.1 p.2 (1 : ZMod 2) + single p.2 p.1 1) := fun p => by
    rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
    rfl
  refine Eq.trans ?_ (Finset.sum_congr rfl fun p _ => (hs p).symm)
  ext a b
  refine Eq.trans ?_ (binaryUpperSum_apply _ a b).symm
  obtain ⟨hXt, hXd⟩ := X.2
  split_ifs with hab hba
  · rfl
  · exact (congrFun₂ hXt a b).symm
  · rw [le_antisymm (not_lt.mp hba) (not_lt.mp hab), hXd]

theorem eq_top_of_lifts_binaryAlt (π : P →* Multiplicative (binaryAltMatrices n)) {K : Subgroup P}
    (hK : π.ker ≤ K) (hlift : ∀ i j, ∃ x ∈ K, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      binaryOff i j) : K = ⊤ := by
  have hmap : ∀ v : Multiplicative (binaryAltMatrices n), v ∈ K.map π := by
    intro v
    have hv : v = ∏ p ∈ binaryUpperPairs n, Multiplicative.ofAdd
        (⟨binaryOff p.1 p.2, binaryOff_mem_binaryAltMatrices _ _⟩ : binaryAltMatrices n) ^
          ((v.toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) p.1 p.2).val := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_pow, toAdd_ofAdd]
      exact binaryAlt_eq_sum v.toAdd
    rw [hv]
    refine Finset.prod_induction _ (· ∈ K.map π) (fun _ _ ha hb => mul_mem ha hb) (one_mem _)
      fun p _ => pow_mem ?_ _
    obtain ⟨x, hxK, hx⟩ := hlift p.1 p.2
    exact ⟨x, hxK, Multiplicative.toAdd.injective (Subtype.ext hx)⟩
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨k, hkK, hk⟩ := hmap (π z)
  have hker : k⁻¹ * z ∈ K := hK (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, inv_mul_cancel])
  simpa using K.mul_mem hkK hker

theorem binaryAlt_commute (hn : 5 ≤ n) (act : GL (Fin n) (ZMod 2) →* MulAut P)
    (π : P →* Multiplicative (binaryAltMatrices n)) (hπ : Function.Surjective π)
    (hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
    (hC : π.ker ≤ Subgroup.center P) (hCfix : ∀ g, ∀ c ∈ π.ker, act g c = c) :
    ∀ x y : P, x * y = y * x := by
  classical
  have hinj : ∀ {x y : P}, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) → π x = π y := fun h =>
    Multiplicative.toAdd.injective (Subtype.ext h)
  have himul : ∀ x y : P, ((π (x * y)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) +
        ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) :=
    fun x y => by rw [map_mul, toAdd_mul, AddSubgroup.coe_add]
  have hzero : ∀ {x : P}, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = 0 → x ∈ π.ker :=
    fun h => by
      rw [MonoidHom.mem_ker]
      exact Multiplicative.toAdd.injective (Subtype.ext h)
  have hlift : ∀ i j, ∃ x : P, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j :=
    fun i j => by
      obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨binaryOff i j,
        binaryOff_mem_binaryAltMatrices i j⟩)
      exact ⟨x, by rw [hx]; rfl⟩
  choose p hp using hlift
  have hH : ∀ a b : Multiplicative (binaryAltMatrices n), a * b = b * a := fun a b =>
    Multiplicative.toAdd.injective (Subtype.ext (by
      simp only [toAdd_mul, AddSubgroup.coe_add]
      exact add_comm _ _))
  have hinv : ∀ g (x y : P), ⁅act g x, act g y⁆ = ⁅x, y⁆ := fun g x y =>
    (map_commutatorElement (act g) x y).symm.trans
      (hCfix g _ (commutatorElement_mem_ker π hH x y))
  have key : ∀ (g : GL (Fin n) (ZMod 2)) (x y z : P),
      ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) →
      ((π (act g z)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((π z).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) +
          ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) → ⁅x, y⁆ = 1 := by
    intro g x y z h₁ h₂
    have h := hinv g x z
    rw [commutatorElement_eq_of_map_eq π hC (hinj h₁) (hinj (h₂.trans (himul z y).symm)),
      commutatorElement_mul_right_of_ker π hH hC] at h
    exact mul_eq_left.mp h
  have hb : ∀ (x y : P) (i j l : Fin n), i ≠ j → i ≠ l → j ≠ l →
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j →
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i l → ⁅x, y⁆ = 1 := by
    intro x y i j l hij hil hjl hx hy
    obtain ⟨k, hki, hkj, hkl⟩ := exists_ne_of_four (by omega) i j l
    refine key (binaryTransvection hkl.symm) x y (p i k) ?_ ?_
    · rw [hπact, hx, binaryTransvection_congr_binaryOff_of_ne _ (Ne.symm hki) (Ne.symm hkj)]
    · rw [hπact, hp, hy, binaryOff_comm i k, binaryTransvection_congr_binaryOff_left _ hki.symm,
        binaryOff_comm l i]
  have hc : ∀ (x y : P) (i j k m : Fin n), i ≠ j → k ≠ m → k ≠ i → k ≠ j → m ≠ i → m ≠ j →
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j →
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff k m → ⁅x, y⁆ = 1 := by
    intro x y i j k m _ hkm _ _ _ _ hx hy
    obtain ⟨l, hli, hlj, hlk, hlm⟩ := exists_ne_of_five hn i j k m
    refine key (binaryTransvection hlm.symm) x y (p k l) ?_ ?_
    · rw [hπact, hx, binaryTransvection_congr_binaryOff_of_ne _ (Ne.symm hli) (Ne.symm hlj)]
    · rw [hπact, hp, hy, binaryOff_comm k l, binaryTransvection_congr_binaryOff_left _ hlk.symm,
        binaryOff_comm l k, binaryOff_comm m k]
  have hall : ∀ (x y : P) (i j k l : Fin n),
      ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j →
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff k l → ⁅x, y⁆ = 1 := by
    intro x y i j k l hx hy
    by_cases hij : i = j
    · rw [hij, binaryOff_self] at hx
      exact commutatorElement_eq_one_of_mem_center_left (hC (hzero hx)) y
    by_cases hkl : k = l
    · rw [hkl, binaryOff_self] at hy
      exact commutatorElement_eq_one_of_mem_center_right x (hC (hzero hy))
    by_cases hki : k = i
    · subst hki
      by_cases hlj : l = j
      · subst hlj
        rw [commutatorElement_eq_of_map_eq π hC rfl (hinj (hy.trans hx.symm)),
          commutatorElement_self]
      · exact hb x y k j l hij hkl (Ne.symm hlj) hx hy
    by_cases hkj : k = j
    · subst hkj
      by_cases hli : l = i
      · subst hli
        rw [commutatorElement_eq_of_map_eq π hC rfl
            (hinj (hy.trans ((binaryOff_comm k l).trans hx.symm))),
          commutatorElement_self]
      · exact hb x y k i l (Ne.symm hij) hkl (Ne.symm hli) (hx.trans (binaryOff_comm i k)) hy
    by_cases hli : l = i
    · subst hli
      exact hb x y l j k hij (Ne.symm hki) (Ne.symm hkj) hx (hy.trans (binaryOff_comm k l))
    by_cases hlj : l = j
    · subst hlj
      exact hb x y l i k (Ne.symm hij) (Ne.symm hkj) (Ne.symm hki)
        (hx.trans (binaryOff_comm i l)) (hy.trans (binaryOff_comm k l))
    exact hc x y i j k l hij hkl hki hkj hli hlj hx hy
  have hcent : ∀ x : P, (∀ i j, ⁅x, p i j⁆ = 1) → ∀ y, x * y = y * x := by
    intro x hx
    have htop : Subgroup.centralizer {x} = ⊤ := by
      refine eq_top_of_lifts_binaryAlt π (fun c hc => ?_) fun i j => ⟨p i j, ?_, hp i j⟩
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp (hC hc) x).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (commutatorElement_eq_one_iff_mul_comm.mp (hx i j)).symm
    intro y
    have hy : y ∈ Subgroup.centralizer {x} := htop ▸ Subgroup.mem_top y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    exact hy.symm
  have hp' : ∀ i j y, p i j * y = y * p i j := fun i j =>
    hcent (p i j) fun k l => hall _ _ i j k l (hp i j) (hp k l)
  intro x y
  exact hcent x (fun i j => commutatorElement_eq_one_iff_mul_comm.mpr (hp' i j x).symm) y

theorem binaryAlt_sq_eq_one (hn : 3 ≤ n) (act : GL (Fin n) (ZMod 2) →* MulAut P)
    (π : P →* Multiplicative (binaryAltMatrices n)) (hπ : Function.Surjective π)
    (hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
    (hC2 : ∀ c ∈ π.ker, c ^ 2 = 1) (hCfix : ∀ g, ∀ c ∈ π.ker, act g c = c)
    (hcomm : ∀ x y : P, x * y = y * x) : ∀ x : P, x ^ 2 = 1 := by
  have hinj : ∀ {x y : P}, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) → π x = π y := fun h =>
    Multiplicative.toAdd.injective (Subtype.ext h)
  have hsqmul : ∀ x y : P, (x * y) ^ 2 = x ^ 2 * y ^ 2 := fun x y =>
    (show Commute x y from hcomm x y).mul_pow 2
  let K : Subgroup P :=
    { carrier := {z | z ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => by
        change (a * b) ^ 2 = 1
        rw [hsqmul, ha, hb, one_mul]
      one_mem' := one_pow 2
      inv_mem' := fun {a} ha => by
        change a⁻¹ ^ 2 = 1
        rw [inv_pow, ha, inv_one] }
  have hlift : ∀ i j, ∃ x : P, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j :=
    fun i j => by
      obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨binaryOff i j,
        binaryOff_mem_binaryAltMatrices i j⟩)
      exact ⟨x, by rw [hx]; rfl⟩
  have hsqlift : ∀ i j (x : P), ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) = binaryOff i j →
      x ^ 2 = 1 := by
    intro i j x hx
    by_cases hij : i = j
    · subst hij
      rw [binaryOff_self] at hx
      exact hC2 x (by
        rw [MonoidHom.mem_ker]
        exact Multiplicative.toAdd.injective (Subtype.ext hx))
    obtain ⟨k, hki, hkj⟩ := exists_ne_ne_of_three_le hn i j
    obtain ⟨y, hy⟩ := hlift i k
    have hysq : y ^ 2 ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      rw [map_pow, toAdd_pow, AddSubgroup.coe_nsmul, hy, two_nsmul]
      exact binary_add_self _
    have hgy : π (act (binaryTransvection hkj.symm) y) = π (y * x) := hinj (by
      rw [hπact, hy, binaryOff_comm i k, binaryTransvection_congr_binaryOff_left _ hki.symm,
        map_mul, toAdd_mul, AddSubgroup.coe_add, hy, hx, binaryOff_comm k i, binaryOff_comm j i])
    obtain ⟨c, hc, hcy⟩ : ∃ c ∈ π.ker, act (binaryTransvection hkj.symm) y = y * x * c :=
      ⟨(y * x)⁻¹ * act (binaryTransvection hkj.symm) y, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hgy, inv_mul_cancel], by group⟩
    have h : (act (binaryTransvection hkj.symm) y) ^ 2 = (y * x * c) ^ 2 := by rw [hcy]
    rw [← map_pow, hCfix _ _ hysq, hsqmul, hsqmul, hC2 c hc, mul_one] at h
    exact (mul_eq_left.mp h.symm)
  intro x
  have htop : K = ⊤ := eq_top_of_lifts_binaryAlt π (fun c hc => hC2 c hc) fun i j => by
    obtain ⟨x, hx⟩ := hlift i j
    exact ⟨x, hsqlift i j x hx, hx⟩
  have hx : x ∈ K := htop ▸ Subgroup.mem_top x
  exact hx

end Group

end MatrixExtension

open Matrix MatrixExtension CFSG.Assembly in
theorem binary_alternating_matrix_central_extension_splitting {n : ℕ} (hn : 5 ≤ n) {P : Type*}
    [Group P] [Finite P] (_hP : IsPGroup 2 P) (act : GL (Fin n) (ZMod 2) →* MulAut P)
    (π : P →* Multiplicative (binaryAltMatrices n)) (hπ : Function.Surjective π)
    (hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) * ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) *
        (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ)
    (hC : π.ker ≤ Subgroup.center P) (hC2 : ∀ c ∈ π.ker, c ^ 2 = 1)
    (hCfix : ∀ g, ∀ c ∈ π.ker, act g c = c) :
    IsElemAbelian 2 (⊤ : Subgroup P) ∧
      ∃ P₀ : Subgroup P, (∀ g, ∀ x ∈ P₀, act g x ∈ P₀) ∧ π.ker ⊓ P₀ = ⊥ ∧ π.ker ⊔ P₀ = ⊤ ∧
        Function.Bijective (π.comp P₀.subtype) := by
  have hcomm := binaryAlt_commute hn act π hπ hπact hC hCfix
  have hsq := binaryAlt_sq_eq_one (by omega) act π hπ hπact hC2 hCfix hcomm
  have hinj : ∀ {x y : P}, ((π x).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((π y).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) → π x = π y := fun h =>
    Multiplicative.toAdd.injective (Subtype.ext h)
  let _ : CommGroup P := { (inferInstance : Group P) with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive P) := AddCommGroup.zmodModule fun x => by
    rw [← ofMul_toMul x, ← ofMul_pow, hsq, ofMul_one]
  let actA : GL (Fin n) (ZMod 2) →* AddMonoid.End (Additive P) :=
    { toFun := fun g => MonoidHom.toAdditive (act g).toMonoidHom
      map_one' := by
        ext x
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        ext x
        rw [map_mul]
        rfl }
  have hactA : ∀ g x, actA g x = Additive.ofMul (act g x.toMul) := fun _ _ => rfl
  let πA : Additive P →+ Matrix (Fin n) (Fin n) (ZMod 2) :=
    { toFun := fun x => ((π x.toMul).toAdd : Matrix (Fin n) (Fin n) (ZMod 2))
      map_zero' := by simp
      map_add' := fun x y => by simp }
  have hπA : ∀ x, πA x = ((π x.toMul).toAdd : Matrix (Fin n) (Fin n) (ZMod 2)) := fun _ => rfl
  have hkerA : ∀ x : Additive P, πA x = 0 → x.toMul ∈ π.ker := fun x h => by
    rw [MonoidHom.mem_ker]
    exact Multiplicative.toAdd.injective (Subtype.ext h)
  obtain ⟨S, hSinv, hSinj, hSsurj⟩ := alt_exists_invariant_complement hn (act := actA)
    (π := πA) (fun g x => by rw [hactA, hπA, hπA, toMul_ofMul, hπact])
    (fun g c hc => by rw [hactA, hCfix g _ (hkerA c hc), ofMul_toMul])
    (fun i j => by
      obtain ⟨x, hx⟩ := hπ (Multiplicative.ofAdd ⟨binaryOff i j,
        binaryOff_mem_binaryAltMatrices i j⟩)
      exact ⟨Additive.ofMul x, by rw [hπA, toMul_ofMul, hx]; rfl⟩)
  let P₀ : Subgroup P :=
    { carrier := {x | Additive.ofMul x ∈ S}
      mul_mem' := fun {a b} ha hb => by
        change Additive.ofMul (a * b) ∈ S
        rw [ofMul_mul]
        exact S.add_mem ha hb
      one_mem' := by
        change Additive.ofMul (1 : P) ∈ S
        rw [ofMul_one]
        exact S.zero_mem
      inv_mem' := fun {a} ha => by
        change Additive.ofMul a⁻¹ ∈ S
        rw [ofMul_inv]
        exact S.neg_mem ha }
  have hP₀ : ∀ x, x ∈ P₀ ↔ Additive.ofMul x ∈ S := fun _ => Iff.rfl
  have hone : ∀ x ∈ P₀, π x = 1 → x = 1 := fun x hx h => by
    have h' := hSinj (Additive.ofMul x) hx (by
      rw [hπA, toMul_ofMul, h]
      rfl)
    rwa [← ofMul_one, Additive.ofMul.injective.eq_iff] at h'
  have hexists : ∀ v : Multiplicative (binaryAltMatrices n), ∃ x ∈ P₀, π x = v := fun v => by
    obtain ⟨s, hs, hsv⟩ := hSsurj _ v.toAdd.2
    exact ⟨s.toMul, by rwa [hP₀, ofMul_toMul], Multiplicative.toAdd.injective
      (Subtype.ext (by rw [← hsv, hπA]))⟩
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcomm a b)⟩⟩, fun x _ => hsq x⟩, P₀,
    fun g x hx => ?_, ?_, ?_, ⟨?_, fun v => ?_⟩⟩
  · rw [hP₀] at hx ⊢
    have := hSinv g _ hx
    rwa [hactA, toMul_ofMul] at this
  · refine eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hone x hx.2 hx.1)
  · refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨y, hy, hyz⟩ := hexists (π z)
    have hzy : z * y⁻¹ ∈ π.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hyz, mul_inv_cancel]
    have := Subgroup.mul_mem_sup hzy hy
    rwa [inv_mul_cancel_right] at this
  · rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hone x x.2 hx)
  · obtain ⟨x, hx, hxv⟩ := hexists v
    exact ⟨⟨x, hx⟩, hxv⟩

end CFSG.LocalAnalysis.ComponentInitial

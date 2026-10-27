module

public import CFSG.CGT.Foote81L6.Normalizer.Hyp
public import CFSG.CGT.Foote81L6.Normalizer.SymBasic
public import CFSG.CGT.Foote81L6.Normalizer.GroupAux

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Equiv

theorem fixes_of_closure {X : Type*} [Group X] {M : Subgroup X} {d z u : X}
    (hgen : Subgroup.closure {g | ∃ m ∈ M, g = m * d * m⁻¹} = M)
    (hnorm : ∀ m ∈ M, (m * u * m⁻¹ = u ∨ m * u * m⁻¹ = z ∨ m * u * m⁻¹ = u * z) ∧
      (m * z * m⁻¹ = u ∨ m * z * m⁻¹ = z ∨ m * z * m⁻¹ = u * z))
    {V : Type*} [Mul V] (ρ : X →* MulAut V) (hd : ∀ v, ρ z v = v → ρ u v = v → ρ d v = v) :
    ∀ m ∈ M, ∀ v, ρ z v = v → ρ u v = v → ρ m v = v := by
  have hfix : ∀ g, (g = u ∨ g = z ∨ g = u * z) → ∀ v, ρ z v = v → ρ u v = v → ρ g v = v := by
    rintro g (rfl | rfl | rfl) v hz hu
    · exact hu
    · exact hz
    · rw [map_mul, MulAut.mul_apply, hz, hu]
  have hstab : ∀ m ∈ M, ∀ v, ρ z v = v → ρ u v = v →
      ρ z (ρ m v) = ρ m v ∧ ρ u (ρ m v) = ρ m v := by
    intro m hm v hz hu
    have hm' := hnorm m⁻¹ (M.inv_mem hm)
    rw [inv_inv] at hm'
    have e : ∀ g : X, ρ g (ρ m v) = ρ m (ρ (m⁻¹ * g * m) v) := by
      intro g
      simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply]
      rw [MulEquiv.apply_symm_apply]
    exact ⟨by rw [e, hfix _ hm'.2 v hz hu], by rw [e, hfix _ hm'.1 v hz hu]⟩
  intro m hm v hz hu
  rw [← hgen] at hm
  revert v
  refine Subgroup.closure_induction (p := fun m _ => ∀ v, ρ z v = v → ρ u v = v → ρ m v = v)
    ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨k, hk, rfl⟩ v hz hu
    have hk' := hstab k⁻¹ (M.inv_mem hk) v hz hu
    simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply]
    have h1 : ρ k⁻¹ v = (ρ k).symm v := by rw [map_inv]; rfl
    rw [← h1, hd _ hk'.1 hk'.2, h1, MulEquiv.apply_symm_apply]
  · intro v _ _
    rw [map_one, MulAut.one_apply]
  · intro a b _ _ ha hb v hz hu
    rw [map_mul, MulAut.mul_apply, hb v hz hu, ha v hz hu]
  · intro a _ ha v hz hu
    have h1 := ha v hz hu
    rw [map_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq, h1]

namespace IsSymDirect

variable {X : Type*} [Group X] [Finite X] {d₀ d₁ : X} {n : ℕ} [NeZero n]
  {φ : X →* Perm (Fin n)}

theorem mem₀ (_hφ : IsSymDirect d₀ d₁ φ) : d₀ ∈ Subgroup.normalClosure ({d₀} : Set X) :=
  Subgroup.subset_normalClosure rfl

theorem injOn (hφ : IsSymDirect d₀ d₁ φ) {a b : X}
    (ha : a ∈ Subgroup.normalClosure ({d₀} : Set X))
    (hb : b ∈ Subgroup.normalClosure ({d₀} : Set X)) (hab : φ a = φ b) : a = b := by
  have h1 : a⁻¹ * b ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
  rw [hφ.ker_eq] at h1
  have h2 : a⁻¹ * b ∈ Subgroup.normalClosure ({d₀} : Set X) ⊓ pPrimeCore 2 X :=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb, h1⟩
  rw [hφ.inf_eq, Subgroup.mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem map_normalClosure (hφ : IsSymDirect d₀ d₁ φ) :
    (Subgroup.normalClosure ({d₀} : Set X)).map φ = ⊤ := by
  have h1 := congrArg (Subgroup.map φ) hφ.sup_eq
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ hφ.surjective] at h1
  have h2 : (pPrimeCore 2 X).map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hφ.ker_eq]
  rw [h2, sup_bot_eq] at h1
  exact h1

theorem exists_mem_eq (hφ : IsSymDirect d₀ d₁ φ) (g : X) :
    ∃ a ∈ Subgroup.normalClosure ({d₀} : Set X), φ a = φ g := by
  have : φ g ∈ (Subgroup.normalClosure ({d₀} : Set X)).map φ := by
    rw [hφ.map_normalClosure]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, hag⟩ := this
  exact ⟨a, ha, hag⟩

@[expose] noncomputable def normalClosureEquiv (hφ : IsSymDirect d₀ d₁ φ) :
    Subgroup.normalClosure ({d₀} : Set X) ≃* Perm (Fin n) :=
  MulEquiv.ofBijective (φ.comp (Subgroup.normalClosure ({d₀} : Set X)).subtype)
    ⟨fun a b hab => Subtype.ext (hφ.injOn a.2 b.2 hab), fun σ => by
      obtain ⟨g, rfl⟩ := hφ.surjective σ
      obtain ⟨a, ha, hag⟩ := hφ.exists_mem_eq g
      exact ⟨⟨a, ha⟩, hag⟩⟩

theorem normalClosureEquiv_apply (hφ : IsSymDirect d₀ d₁ φ)
    (a : Subgroup.normalClosure ({d₀} : Set X)) : hφ.normalClosureEquiv a = φ a := rfl

theorem mul_self₀ (hφ : IsSymDirect d₀ d₁ φ) : d₀ * d₀ = 1 :=
  hφ.injOn (Subgroup.mul_mem _ hφ.mem₀ hφ.mem₀) (Subgroup.one_mem _)
    (by rw [map_mul, hφ.map₀, swap_mul_self, map_one])

theorem mul_self₁ (hφ : IsSymDirect d₀ d₁ φ) : d₁ * d₁ = 1 :=
  hφ.injOn (Subgroup.mul_mem _ hφ.mem₁ hφ.mem₁) (Subgroup.one_mem _)
    (by rw [map_mul, hφ.map₁, swap_mul_self, map_one])

theorem commute₀₁ (hn : n = 4 ∨ n = 5) (hφ : IsSymDirect d₀ d₁ φ) : d₀ * d₁ = d₁ * d₀ :=
  hφ.injOn (Subgroup.mul_mem _ hφ.mem₀ hφ.mem₁) (Subgroup.mul_mem _ hφ.mem₁ hφ.mem₀)
    (by rw [map_mul, map_mul, hφ.map₀, hφ.map₁, (perm_swap_pair hn).2.1])

theorem ne₀₁ (hn : n = 4 ∨ n = 5) (hφ : IsSymDirect d₀ d₁ φ) : d₀ ≠ d₁ := fun h =>
  (perm_swap_pair hn).2.2 (by rw [← hφ.map₀, ← hφ.map₁, h])

theorem commute_of_mem_pPrimeCore (hφ : IsSymDirect d₀ d₁ φ) {o : X}
    (ho : o ∈ pPrimeCore 2 X) : o * d₀ = d₀ * o ∧ o * d₁ = d₁ * o :=
  ⟨(hφ.commute d₀ hφ.mem₀ o ho).symm, (hφ.commute d₁ hφ.mem₁ o ho).symm⟩

theorem mem_pPrimeCore_of_commute (hn : n = 4 ∨ n = 5) (hφ : IsSymDirect d₀ d₁ φ) {x : X}
    (hx : Odd (orderOf x)) (h0 : x * d₀ = d₀ * x) (h1 : x * d₁ = d₁ * x) :
    x ∈ pPrimeCore 2 X := by
  rw [← hφ.ker_eq, MonoidHom.mem_ker]
  have hc0 : φ x * swap 0 1 = swap 0 1 * φ x := by rw [← hφ.map₀, ← map_mul, ← map_mul, h0]
  have hc1 : φ x * swap 2 3 = swap 2 3 * φ x := by rw [← hφ.map₁, ← map_mul, ← map_mul, h1]
  have h2 := perm_mul_self_of_commute hn (φ x) hc0 hc1
  have hodd : Odd (orderOf (φ x)) := hx.of_dvd_nat (orderOf_map_dvd φ x)
  exact eq_one_of_pow_two_pow_of_odd (k := 1) (by rw [pow_one, pow_two]; exact h2) hodd

theorem le_pPrimeCore_of_commute (hn : n = 4 ∨ n = 5) (hφ : IsSymDirect d₀ d₁ φ)
    {P : Subgroup X} (hP : Odd (Nat.card P)) (h0 : ∀ p ∈ P, p * d₀ = d₀ * p)
    (h1 : ∀ p ∈ P, p * d₁ = d₁ * p) : P ≤ pPrimeCore 2 X := fun p hp =>
  hφ.mem_pPrimeCore_of_commute hn (hP.of_dvd_nat (Subgroup.orderOf_dvd_natCard P hp))
    (h0 p hp) (h1 p hp)

theorem card_pPrimeCore (hφ : IsSymDirect d₀ d₁ φ)
    (hL1 : Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
      Subgroup.centralizer ({d₁} : Set X)) = 1 ∨
      Nat.card ↥(pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
        Subgroup.centralizer ({d₁} : Set X)) = 3) :
    Nat.card (pPrimeCore 2 X) = 1 ∨ Nat.card (pPrimeCore 2 X) = 3 := by
  have h : pPrimeCore 2 X ⊓ Subgroup.centralizer ({d₀} : Set X) ⊓
      Subgroup.centralizer ({d₁} : Set X) = pPrimeCore 2 X := by
    apply le_antisymm (inf_le_left.trans inf_le_left)
    intro o ho
    exact ⟨⟨ho, Subgroup.mem_centralizer_singleton_iff.mpr (hφ.commute_of_mem_pPrimeCore ho).1⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (hφ.commute_of_mem_pPrimeCore ho).2⟩
  rwa [h] at hL1

theorem mem_normalClosure_of_pow (hφ : IsSymDirect d₀ d₁ φ) {g : X} {k : ℕ}
    (hg : g ^ 2 ^ k = 1) : g ∈ Subgroup.normalClosure ({d₀} : Set X) := by
  obtain ⟨a, ha, hag⟩ := hφ.exists_mem_eq g
  set o := a⁻¹ * g with hodef
  have ho : o ∈ pPrimeCore 2 X := by
    rw [← hφ.ker_eq, MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
  have hga : g = a * o := by rw [hodef]; group
  have hpow : g ^ 2 ^ k = a ^ 2 ^ k * o ^ 2 ^ k := by
    rw [hga]
    exact (Commute.mul_pow (hφ.commute a ha o ho) _)
  have hok : o ^ 2 ^ k ∈ Subgroup.normalClosure ({d₀} : Set X) ⊓ pPrimeCore 2 X := by
    refine ⟨?_, Subgroup.pow_mem _ ho _⟩
    have : o ^ 2 ^ k = (a ^ 2 ^ k)⁻¹ := by
      rw [hpow] at hg
      exact eq_inv_of_mul_eq_one_right hg
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ ha _)
  rw [hφ.inf_eq, Subgroup.mem_bot] at hok
  have ho1 : o = 1 := eq_one_of_pow_two_pow_of_odd hok (odd_orderOf_of_mem_pPrimeCore ho)
  rw [hga, ho1, mul_one]
  exact ha

theorem le_normalClosure_of_isPGroup (hφ : IsSymDirect d₀ d₁ φ) {P : Subgroup X}
    (hP : IsPGroup 2 P) : P ≤ Subgroup.normalClosure ({d₀} : Set X) := fun p hp => by
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  exact hφ.mem_normalClosure_of_pow (by simpa using congrArg Subtype.val hk)

theorem exists_normalized_four (hn : n = 4 ∨ n = 5) (hφ : IsSymDirect d₀ d₁ φ)
    {M : Subgroup X} (hM₀ : d₀ ∈ M) (hM₁ : d₁ ∈ M) (ψ : M ≃* Perm (Fin 4)) :
    ∃ ψ' : M ≃* Perm (Fin 4), ψ' ⟨d₀, hM₀⟩ = swap 0 1 ∧ ψ' ⟨d₁, hM₁⟩ = swap 2 3 := by
  classical
  obtain ⟨h23, hcomm, hne⟩ := perm_swap_pair hn
  set s : Perm (Fin 4) →* ℤˣ := (Perm.sign.comp (φ.comp M.subtype)).comp ψ.symm.toMonoidHom
  have hs_apply : ∀ m : M, s (ψ m) = Perm.sign (φ m) := fun m => by
    simp [s]
  have hs₀ : s (ψ ⟨d₀, hM₀⟩) = -1 := by
    rw [hs_apply]
    exact (show Perm.sign (φ d₀) = -1 by rw [hφ.map₀]; exact Perm.sign_swap (fin_zero_ne_one_of hn))
  have hs₁ : s (ψ ⟨d₁, hM₁⟩) = -1 := by
    rw [hs_apply]
    exact (show Perm.sign (φ d₁) = -1 by rw [hφ.map₁]; exact Perm.sign_swap h23)
  have hsurj : Function.Surjective s := by
    intro x
    rcases Int.units_eq_one_or x with rfl | rfl
    · exact ⟨1, map_one s⟩
    · exact ⟨_, hs₀⟩
  have hseq : s = Perm.sign := Perm.eq_sign_of_surjective_hom hsurj
  have hinv : ∀ (d : X) (hd : d ∈ M), d * d = 1 → ψ ⟨d, hd⟩ * ψ ⟨d, hd⟩ = 1 := by
    intro d hd hdd
    rw [← map_mul, ← map_one ψ]
    exact congrArg ψ (Subtype.ext hdd)
  obtain ⟨i, j, hij, hψ₀⟩ := perm_eq_swap_of_sign (n := 4) (Or.inl rfl) _
    (hinv d₀ hM₀ hφ.mul_self₀) (by rw [← hseq]; exact hs₀)
  obtain ⟨k, l, hkl, hψ₁⟩ := perm_eq_swap_of_sign (n := 4) (Or.inl rfl) _
    (hinv d₁ hM₁ hφ.mul_self₁) (by rw [← hseq]; exact hs₁)
  have hc : swap i j * swap k l = swap k l * swap i j := by
    rw [← hψ₀, ← hψ₁, ← map_mul, ← map_mul]
    exact congrArg ψ (Subtype.ext (hφ.commute₀₁ hn))
  have hne' : swap i j ≠ swap k l := by
    rw [← hψ₀, ← hψ₁]
    intro h
    exact hφ.ne₀₁ hn (congrArg Subtype.val (ψ.injective h))
  obtain ⟨σ, hσ₀, hσ₁⟩ := perm_exists_conj_swap_pair (n := 4) (Or.inl rfl) i j k l hij hkl hc hne'
  refine ⟨ψ.trans (MulAut.conj σ), ?_, ?_⟩
  · show σ * ψ ⟨d₀, hM₀⟩ * σ⁻¹ = swap 0 1
    rw [hψ₀, hσ₀]
  · show σ * ψ ⟨d₁, hM₁⟩ * σ⁻¹ = swap 2 3
    rw [hψ₁, hσ₁]

theorem sym_four (hn : n = 4 ∨ n = 5) (hφ : IsSymDirect d₀ d₁ φ) {M : Subgroup X}
    (hM₀ : d₀ ∈ M) (hM₁ : d₁ ∈ M) (ψ : M ≃* Perm (Fin 4)) :
    Subgroup.closure {g | ∃ m ∈ M, g = m * d₀ * m⁻¹} = M ∧
      ∃ u ∈ M, (∃ m ∈ M, u = m * (d₀ * d₁) * m⁻¹) ∧ u ≠ d₀ * d₁ ∧
        u * (d₀ * d₁) = d₀ * d₁ * u ∧
        ∀ m ∈ M, (m * u * m⁻¹ = u ∨ m * u * m⁻¹ = d₀ * d₁ ∨ m * u * m⁻¹ = u * (d₀ * d₁)) ∧
          (m * (d₀ * d₁) * m⁻¹ = u ∨ m * (d₀ * d₁) * m⁻¹ = d₀ * d₁ ∨
            m * (d₀ * d₁) * m⁻¹ = u * (d₀ * d₁)) := by
  classical
  obtain ⟨ψ', hψ₀, hψ₁⟩ := hφ.exists_normalized_four hn hM₀ hM₁ ψ
  set ι : Perm (Fin 4) →* X := M.subtype.comp ψ'.symm.toMonoidHom with hι
  have hιM : ∀ σ, ι σ ∈ M := fun σ => (ψ'.symm σ).2
  have hιinj : Function.Injective ι := fun a b h => ψ'.symm.injective (Subtype.ext h)
  have hι₀ : ι (swap 0 1) = d₀ := by
    rw [hι, MonoidHom.comp_apply, ← hψ₀]
    simp
  have hι₁ : ι (swap 2 3) = d₁ := by
    rw [hι, MonoidHom.comp_apply, ← hψ₁]
    simp
  have hιψ : ∀ m (hm : m ∈ M), ι (ψ' ⟨m, hm⟩) = m := fun m hm => by
    rw [hι, MonoidHom.comp_apply]
    simp
  obtain ⟨hne, hcomm, -, hconj, -, hnorm⟩ := perm_four_klein
  have hz : ι (swap 0 1 * swap 2 3) = d₀ * d₁ := by rw [map_mul, hι₀, hι₁]
  refine ⟨le_antisymm ?_ ?_, ι (swap 0 2 * swap 1 3), hιM _, ⟨ι (swap 1 2), hιM _, ?_⟩, ?_, ?_,
    fun m hm => ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact M.mul_mem (M.mul_mem hm hM₀) (M.inv_mem hm)
  · intro m hm
    have htop : ψ' ⟨m, hm⟩ ∈ Subgroup.normalClosure ({swap (0 : Fin 4) 1} : Set (Perm (Fin 4))) := by
      rw [perm_normalClosure_swap (by decide)]
      exact Subgroup.mem_top _
    rw [← hιψ m hm]
    refine Subgroup.closure_induction
      (p := fun σ _ => ι σ ∈ Subgroup.closure {g | ∃ m ∈ M, g = m * d₀ * m⁻¹}) ?_ ?_ ?_ ?_ htop
    · intro σ hσ
      obtain ⟨b, hb, hconj'⟩ := Group.mem_conjugatesOfSet_iff.mp hσ
      rw [Set.mem_singleton_iff] at hb
      rw [hb] at hconj'
      obtain ⟨τ, rfl⟩ := isConj_iff.mp hconj'
      refine Subgroup.subset_closure ⟨ι τ, hιM τ, ?_⟩
      rw [map_mul, map_mul, map_inv, hι₀]
    · rw [map_one]; exact Subgroup.one_mem _
    · intro a b _ _ ha hb; rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    · intro a _ ha; rw [map_inv]; exact Subgroup.inv_mem _ ha
  · rw [← hz, ← map_inv, ← map_mul, ← map_mul, hconj]
  · rw [← hz]
    exact hιinj.ne hne
  · rw [← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨hu, hz'⟩ := hnorm (ψ' ⟨m, hm⟩)
    have e : ∀ σ : Perm (Fin 4), m * ι σ * m⁻¹ = ι (ψ' ⟨m, hm⟩ * σ * (ψ' ⟨m, hm⟩)⁻¹) := by
      intro σ
      rw [map_mul, map_mul, map_inv, hιψ]
    refine ⟨?_, ?_⟩
    · rw [e]
      rcases hu with h1 | h1 | h1
      · exact Or.inl (by rw [h1])
      · exact Or.inr (Or.inl (by rw [h1, hz]))
      · exact Or.inr (Or.inr (by rw [h1, map_mul, hz]))
    · rw [← hz, e]
      rcases hz' with h1 | h1 | h1
      · exact Or.inl (by rw [h1])
      · exact Or.inr (Or.inl (by rw [h1]))
      · exact Or.inr (Or.inr (by rw [h1, map_mul]))

theorem sym_four_fixes (hn : n = 4 ∨ n = 5) (hφ : IsSymDirect d₀ d₁ φ) {M : Subgroup X}
    (hM₀ : d₀ ∈ M) (hM₁ : d₁ ∈ M) (ψ : M ≃* Perm (Fin 4)) :
    ∃ u ∈ M, (∃ m ∈ M, u = m * (d₀ * d₁) * m⁻¹) ∧ u ≠ d₀ * d₁ ∧
      u * (d₀ * d₁) = d₀ * d₁ * u ∧
      ∀ {V : Type*} [Mul V] (ρ : X →* MulAut V),
        (∀ v, ρ (d₀ * d₁) v = v → ρ u v = v → ρ d₀ v = v) →
          ∀ m ∈ M, ∀ v, ρ (d₀ * d₁) v = v → ρ u v = v → ρ m v = v := by
  obtain ⟨hgen, u, huM, hconj, hne, hcomm, hnorm⟩ := hφ.sym_four hn hM₀ hM₁ ψ
  exact ⟨u, huM, hconj, hne, hcomm, fun ρ hd => fixes_of_closure hgen hnorm ρ hd⟩

end IsSymDirect

end CFSG.CGT.Foote81L6.Normalizer

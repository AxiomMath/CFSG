module

public import CFSG.Open.LocalVocabulary
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open

theorem exists_stable_sylow_fixing {G : Type*} [Group G] [Finite G] (α : MulAut G)
    (hα : α ^ 3 = 1) (A : Subgroup G) (hA : IsElemAbelian 3 A) (hfix : ∀ a ∈ A, α a = a) :
    ∃ S : Sylow 3 G, A ≤ (S : Subgroup G) ∧ (S : Subgroup G).map α.toMonoidHom = S := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hA.2 g g.2)⟩
  set H₁ : Subgroup (MulAut G) := A.map (MulAut.conj : G →* MulAut G) with hH₁
  set H₂ : Subgroup (MulAut G) := Subgroup.zpowers α with hH₂
  have hH₁p : IsPGroup 3 H₁ := hAp.map _
  have hH₂p : IsPGroup 3 H₂ := by
    have hord : orderOf α ∣ 3 := orderOf_dvd_of_pow_eq_one hα
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (by simpa using hord : orderOf α ∣ 3 ^ 1)
    exact IsPGroup.of_card (n := k) (by rw [hH₂, Nat.card_zpowers, hk])
  have hcomm : ∀ a ∈ A, Commute (MulAut.conj a) α := by
    intro a ha
    show MulAut.conj a * α = α * MulAut.conj a
    ext x
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hfix a ha]
  have hnorm : H₁ ≤ Subgroup.normalizer (H₂ : Set (MulAut G)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hcomm a ha).zpow_right n).symm.eq
  have hX : IsPGroup 3 (H₁ ⊔ H₂ : Subgroup (MulAut G)) :=
    hH₁p.to_sup_of_normal_right' hH₂p hnorm
  have hmod := hX.card_modEq_card_fixedPoints (Sylow 3 G)
  have hsyl : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hfix' : Nat.card (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G)) (Sylow 3 G)) ≡
      1 [MOD 3] := hmod.symm.trans hsyl
  have hne : Nonempty (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G)) (Sylow 3 G)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G))
        (Sylow 3 G)) := by
      by_contra h0
      have : Nat.card (MulAction.fixedPoints (H₁ ⊔ H₂ : Subgroup (MulAut G)) (Sylow 3 G)) = 0 := by
        omega
      rw [this] at hfix'
      exact absurd (Nat.ModEq.symm hfix') (by decide)
    exact (Nat.card_pos_iff.1 hpos).1
  obtain ⟨⟨S, hS⟩⟩ := hne
  refine ⟨S, ?_, ?_⟩
  · refine (hAp.sylow_mem_fixedPoints_iff (Q := S)).1 ?_
    rw [MulAction.mem_fixedPoints]
    intro a
    have h1 : (⟨MulAut.conj (a : G), (le_sup_left : H₁ ≤ H₁ ⊔ H₂) ⟨a, a.2, rfl⟩⟩ : ↥(H₁ ⊔ H₂)) • S = S := hS _
    exact h1
  · have h1 : (⟨α, (le_sup_right : H₂ ≤ H₁ ⊔ H₂) (Subgroup.mem_zpowers α)⟩ : ↥(H₁ ⊔ H₂)) • S = S := hS _
    have h2 : (((⟨α, (le_sup_right : H₂ ≤ H₁ ⊔ H₂) (Subgroup.mem_zpowers α)⟩ : ↥(H₁ ⊔ H₂)) • S : Sylow 3 G) :
        Subgroup G) = S := congrArg (fun T : Sylow 3 G => (T : Subgroup G)) h1
    have h3 := (Sylow.pointwise_smul_def (g := (⟨α, (le_sup_right : H₂ ≤ H₁ ⊔ H₂) (Subgroup.mem_zpowers α)⟩ :
        ↥(H₁ ⊔ H₂))) (P := S)).symm.trans h2
    rw [Subgroup.pointwise_smul_def] at h3
    exact h3

theorem card_le_prod_of_filtration {G : Type*} [Group G] [Finite G] (N : ℕ → Subgroup G)
    {Q : ℕ → Type*} [∀ k, Group (Q k)] [∀ k, Finite (Q k)] (π : ∀ k, N k →* Q k) (d : ℕ)
    (hbot : N d = ⊥) (hchain : ∀ k, N (k + 1) ≤ N k)
    (hker : ∀ k (x : N k), π k x = 1 ↔ (x : G) ∈ N (k + 1))
    (A : Subgroup G) (hA : A ≤ N 0) (B : ℕ → ℕ)
    (hB : ∀ k < d, Nat.card {q : Q k // ∃ x : N k, (x : G) ∈ A ∧ π k x = q} ≤ B k) :
    Nat.card A ≤ ∏ k ∈ Finset.range d, B k := by
  have key : ∀ k < d, Nat.card ↥(A ⊓ N k) ≤ B k * Nat.card ↥(A ⊓ N (k + 1)) := by
    intro k hk
    set M : Subgroup G := A ⊓ N k with hM
    let φ : ↥M →* Q k := (π k).comp (Subgroup.inclusion (inf_le_right : M ≤ N k))
    have hkerE : Nat.card φ.ker = Nat.card ↥(A ⊓ N (k + 1)) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, ?_⟩
          invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
      · have hx : φ x.1 = 1 := x.2
        exact ⟨x.1.2.1, (hker k ⟨x.1.1, x.1.2.2⟩).1 hx⟩
      · exact ⟨y.2.1, hchain k y.2.2⟩
      · rw [MonoidHom.mem_ker]
        exact (hker k ⟨y.1, hchain k y.2.2⟩).2 y.2.2
    have hrange : Nat.card φ.range ≤ B k := by
      refine le_trans ?_ (hB k hk)
      refine Nat.card_le_card_of_injective (fun q => ⟨q.1, ?_⟩) ?_
      · obtain ⟨x, hx⟩ := q.2
        exact ⟨⟨x.1, (inf_le_right : M ≤ N k) x.2⟩, x.2.1, hx⟩
      · intro a b h
        have := congrArg Subtype.val h
        exact Subtype.ext this
    have := Subgroup.card_ker_mul_card_range φ
    rw [hkerE] at this
    calc Nat.card ↥M = Nat.card ↥(A ⊓ N (k + 1)) * Nat.card φ.range := this.symm
      _ ≤ Nat.card ↥(A ⊓ N (k + 1)) * B k := Nat.mul_le_mul_left _ hrange
      _ = B k * Nat.card ↥(A ⊓ N (k + 1)) := mul_comm _ _
  have step : ∀ k ≤ d, Nat.card ↥(A ⊓ N 0) ≤ (∏ j ∈ Finset.range k, B j) * Nat.card ↥(A ⊓ N k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := key k (by omega)
      calc Nat.card ↥(A ⊓ N 0) ≤ (∏ j ∈ Finset.range k, B j) * Nat.card ↥(A ⊓ N k) := h1
        _ ≤ (∏ j ∈ Finset.range k, B j) * (B k * Nat.card ↥(A ⊓ N (k + 1))) :=
          Nat.mul_le_mul_left _ h2
        _ = (∏ j ∈ Finset.range (k + 1), B j) * Nat.card ↥(A ⊓ N (k + 1)) := by
          rw [Finset.prod_range_succ]; ring
  have h := step d le_rfl
  have hA0 : A ⊓ N 0 = A := inf_eq_left.2 hA
  rw [hA0] at h
  rw [hbot, inf_bot_eq, Subgroup.card_bot, mul_one] at h
  exact h

theorem linearIndependent_of_fixed {F₀ K : Type*} [Field F₀] [Field K] [Algebra F₀ K]
    (σ : K ≃+* K) (hF₀ : ∀ x : K, σ x = x → x ∈ Set.range (algebraMap F₀ K))
    {V : Type*} [AddCommGroup V] [Module F₀ V] [Module K V] [IsScalarTower F₀ K V]
    (τ : V →+ V) (hτ : ∀ (c : K) (a : V), τ (c • a) = σ c • τ a) {ι : Type*} (v : ι → V)
    (hv : ∀ i, τ (v i) = v i) (hli : LinearIndependent F₀ v) : LinearIndependent K v := by
  classical
  rw [linearIndependent_iff']
  suffices H : ∀ n : ℕ, ∀ s : Finset ι, s.card ≤ n → ∀ g : ι → K, ∑ i ∈ s, g i • v i = 0 →
      ∀ i ∈ s, g i = 0 by
    intro s g hg i hi
    exact H s.card s le_rfl g hg i hi
  intro n
  induction n with
  | zero =>
    intro s hs g _ i hi
    have : s = ∅ := Finset.card_eq_zero.1 (by omega)
    simp [this] at hi
  | succ n ih =>
    intro s hs g hg i₀ hi₀
    by_contra hne
    set g' : ι → K := fun j => (g i₀)⁻¹ * g j with hg'def
    have hg' : ∑ j ∈ s, g' j • v j = 0 := by
      calc ∑ j ∈ s, g' j • v j = (g i₀)⁻¹ • ∑ j ∈ s, g j • v j := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ => mul_smul _ _ _
        _ = 0 := by rw [hg, smul_zero]
    have hg'i : g' i₀ = 1 := inv_mul_cancel₀ hne
    have h2 : ∑ j ∈ s, σ (g' j) • v j = 0 := by
      have := congrArg τ hg'
      rw [map_sum, map_zero] at this
      simpa [hτ, hv] using this
    have h3 : ∑ j ∈ s.erase i₀, (g' j - σ (g' j)) • v j = 0 := by
      rw [Finset.sum_erase _ (by rw [hg'i, map_one, sub_self, zero_smul])]
      simp only [sub_smul, Finset.sum_sub_distrib, hg', h2, sub_zero]
    have h4 := ih (s.erase i₀) (by rw [Finset.card_erase_of_mem hi₀]; omega) _ h3
    have h5 : ∀ j ∈ s, g' j ∈ Set.range (algebraMap F₀ K) := by
      intro j hj
      by_cases hji : j = i₀
      · rw [hji, hg'i]; exact ⟨1, map_one _⟩
      · exact hF₀ _ (sub_eq_zero.1 (h4 j (Finset.mem_erase.2 ⟨hji, hj⟩))).symm
    choose! c hc using h5
    have h6 : ∑ j ∈ s, c j • v j = 0 := by
      rw [← hg']
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← hc j hj, algebraMap_smul]
    have h7 := linearIndependent_iff'.1 hli s c h6 i₀ hi₀
    have := hc i₀ hi₀
    rw [h7, map_zero, hg'i] at this
    exact one_ne_zero this.symm

theorem card_fixed_pow_le {K : Type*} [Field K] [Finite K] {I : Type*} [Fintype I]
    (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ : σ ≠ 1) (τ : (I → K) →+ (I → K))
    (hτ : ∀ (c : K) (a : I → K), τ (c • a) = σ c • τ a) :
    Nat.card {a : I → K // τ a = a} ^ 3 ≤ Nat.card K ^ Fintype.card I := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup (K ≃+* K) := Subgroup.zpowers σ with hA
  set F₀ : Subfield K := FixedPoints.subfield A K with hF₀def
  have hord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ
  have hcardA : Nat.card A = 3 := by rw [hA, Nat.card_zpowers, hord]
  have hKcard : Nat.card K = Nat.card F₀ ^ 3 := by
    have := CFSG.Semidihedral.FixedFieldData.nat_card_eq_fixedSubfield_card_pow K A
    rwa [hcardA] at this
  have hmem : ∀ x : K, σ x = x → x ∈ F₀ := by
    intro x hx a
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    have : ∀ m : ℤ, (σ ^ m) x = x := by
      intro m
      have hstab : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) x :=
        (Subgroup.zpowers_le (H := MulAction.stabilizer (K ≃+* K) x)).mpr hx
      exact hstab (Subgroup.zpow_mem_zpowers σ m)
    change (a : K ≃+* K) x = x
    rw [← hm]
    exact this m
  have hσF : ∀ c : F₀, σ (c : K) = c := by
    intro c
    exact c.2 ⟨σ, Subgroup.mem_zpowers σ⟩
  let W : Submodule F₀ (I → K) :=
    { carrier := {a | τ a = a}
      add_mem' := fun {a b} ha hb => by
        change τ (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := by
        change τ 0 = 0
        exact map_zero _
      smul_mem' := fun c a ha => by
        change τ (c • a) = c • a
        have hc : c • a = (c : K) • a := rfl
        rw [hc, hτ, hσF c]
        exact congrArg ((c : K) • ·) ha }
  haveI : Finite W := Finite.of_injective (fun w : W => (w : I → K)) Subtype.val_injective
  have hfin : Module.Finite F₀ W := Module.Finite.of_finite
  set d := Module.finrank F₀ W with hd
  let b := Module.finBasis F₀ W
  let vs : Fin d → (I → K) := fun i => (b i : I → K)
  have hli : LinearIndependent F₀ vs := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hvs : ∀ i, τ (vs i) = vs i := fun i => (b i).2
  have hKli : LinearIndependent K vs :=
    linearIndependent_of_fixed σ (fun x hx => ⟨⟨x, hmem x hx⟩, rfl⟩) τ hτ vs hvs hli
  have hdle : d ≤ Fintype.card I := by
    have := hKli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] at this
    exact this
  have hW : Nat.card {a : I → K // τ a = a} = Nat.card F₀ ^ d :=
    (Module.natCard_eq_pow_finrank (K := F₀) (V := W))
  calc Nat.card {a : I → K // τ a = a} ^ 3 = (Nat.card F₀ ^ 3) ^ d := by
        rw [hW, ← pow_mul, ← pow_mul, mul_comm]
    _ = Nat.card K ^ d := by rw [hKcard]
    _ ≤ Nat.card K ^ Fintype.card I :=
        Nat.pow_le_pow_right Nat.card_pos hdle

end CFSG.LocalAnalysis.GLTheoremA

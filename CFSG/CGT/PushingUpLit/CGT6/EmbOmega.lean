module

public import CFSG.CGT.PushingUpLit.CGT6.EmbeddingNodes
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoType
public import CFSG.Quasithin.Background.D2Fitting

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement Matrix

theorem eq_top_of_isSubnormal {H : Type*} [Group H] {K : Subgroup H} (hK : K.IsSubnormal)
    (h : ∀ N : Subgroup H, N.Normal → K ≤ N → N = ⊤) : K = ⊤ := by
  have key : ∀ L : Subgroup H, L.IsSubnormal → K ≤ L → L = ⊤ := by
    intro L hL
    induction hL with
    | top => intro _; rfl
    | step L' M hLM _ hN ih =>
      intro hKL
      have hM : M = ⊤ := ih (hKL.trans hLM)
      subst hM
      refine h L' ?_ hKL
      rw [← Subgroup.normalizer_eq_top_iff]
      exact top_le_iff.mp ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).mp hN)
  exact key K hK le_rfl

theorem embOmega_conclusion {Γ : Type*} [Group Γ] {X Y : Subgroup Γ} (hYX : Y ≤ X) (hne : Y ≠ X)
    (h : ∀ N : Subgroup ↥X, N.Normal → Y.subgroupOf X ≤ N → N = ⊤) :
    (∀ N : Subgroup Γ, Y ≤ N → N ≤ X → (N.subgroupOf X).Normal → N = X) ∧
      ¬ (Y.subgroupOf X).IsSubnormal := by
  refine ⟨fun N hYN hNX hn => ?_, fun hs => ?_⟩
  · have := h (N.subgroupOf X) hn (fun x hx => hYN hx)
    exact le_antisymm hNX (Subgroup.subgroupOf_eq_top.mp this)
  · have := eq_top_of_isSubnormal hs h
    exact hne (le_antisymm hYX (Subgroup.subgroupOf_eq_top.mp this))

theorem embOmega_minus {V : Type} [CommGroup V] {X Y : Subgroup (MulAut V)} {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNatSectionBy (omegaMinusAct n) X (commV X) ⊥) (hYX : Y ≤ X) (hY1 : Y ≠ ⊥) :
    ∀ N : Subgroup ↥X, N.Normal → Y.subgroupOf X ≤ N → N = ⊤ := by
  obtain ⟨-, θ, -⟩ := hnat
  have hS : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n))) :=
    isSimpleGroup_sl2_gf (by omega)
  have : IsSimpleGroup ↥X := θ.isSimpleGroup
  intro N hN hYN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exfalso
    apply hY1
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hYX hy⟩ : ↥X) ∈ N := hYN hy
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exact h

section Plus

theorem eq_top_of_normal_prod {S : Type*} [Group S] [IsSimpleGroup S]
    (hc : Subgroup.center S = ⊥) {N : Subgroup (S × S)} [hN : N.Normal]
    (h1 : ∃ y ∈ N, y.1 ≠ 1) (h2 : ∃ y ∈ N, y.2 ≠ 1) : N = ⊤ := by
  have hfirst : (N.comap (MonoidHom.inl S S)) = ⊤ := by
    have : (N.comap (MonoidHom.inl S S)).Normal := Subgroup.normal_comap _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inl S S)) with h | h
    · exfalso
      obtain ⟨⟨a, b⟩, hab, ha⟩ := h1
      have hnc : a ∉ Subgroup.center S := by
        rw [hc]
        exact fun h => ha (Subgroup.mem_bot.mp h)
      rw [Subgroup.mem_center_iff] at hnc
      push Not at hnc
      obtain ⟨c, hc'⟩ := hnc
      have hmem : (c, 1) * (a, b) * (c, 1)⁻¹ * (a, b)⁻¹ ∈ N :=
        N.mul_mem (hN.conj_mem _ hab _) (N.inv_mem hab)
      have : MonoidHom.inl S S (c * a * c⁻¹ * a⁻¹) ∈ N := by
        convert hmem using 1
        ext <;> simp
      have hbot : c * a * c⁻¹ * a⁻¹ ∈ N.comap (MonoidHom.inl S S) := this
      rw [h, Subgroup.mem_bot] at hbot
      have h1 : c * a * c⁻¹ = a := mul_inv_eq_one.mp hbot
      exact hc' (mul_inv_eq_iff_eq_mul.mp h1)
    · exact h
  have hsecond : (N.comap (MonoidHom.inr S S)) = ⊤ := by
    have : (N.comap (MonoidHom.inr S S)).Normal := Subgroup.normal_comap _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap (MonoidHom.inr S S)) with h | h
    · exfalso
      obtain ⟨⟨a, b⟩, hab, hb⟩ := h2
      have hnc : b ∉ Subgroup.center S := by
        rw [hc]
        exact fun h => hb (Subgroup.mem_bot.mp h)
      rw [Subgroup.mem_center_iff] at hnc
      push Not at hnc
      obtain ⟨c, hc'⟩ := hnc
      have hmem : (1, c) * (a, b) * (1, c)⁻¹ * (a, b)⁻¹ ∈ N :=
        N.mul_mem (hN.conj_mem _ hab _) (N.inv_mem hab)
      have : MonoidHom.inr S S (c * b * c⁻¹ * b⁻¹) ∈ N := by
        convert hmem using 1
        ext <;> simp
      have hbot : c * b * c⁻¹ * b⁻¹ ∈ N.comap (MonoidHom.inr S S) := this
      rw [h, Subgroup.mem_bot] at hbot
      have h1 : c * b * c⁻¹ = b := mul_inv_eq_one.mp hbot
      exact hc' (mul_inv_eq_iff_eq_mul.mp h1)
    · exact h
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have ha : (a, 1) ∈ N := by
    have : a ∈ N.comap (MonoidHom.inl S S) := by rw [hfirst]; trivial
    exact this
  have hb : (1, b) ∈ N := by
    have : b ∈ N.comap (MonoidHom.inr S S) := by rw [hsecond]; trivial
    exact this
  have := N.mul_mem ha hb
  simpa using this

end Plus

section Transvections

variable {F : Type} [Field F]

theorem top_of_first {K : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))}
    (h1 : ∀ M : Matrix (Fin 2) (Fin 2) F,
      Multiplicative.ofAdd ((!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * M - M) ∈ K)
    (h2 : ∀ M : Matrix (Fin 2) (Fin 2) F,
      Multiplicative.ofAdd ((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * M - M) ∈ K) :
    K = ⊤ := by
  rw [eq_top_iff]
  intro m _
  have hm : ∃ N, m = Multiplicative.ofAdd N := ⟨Multiplicative.toAdd m, rfl⟩
  obtain ⟨N, hN⟩ := hm
  rw [hN]
  have e1 : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) * !![0, 0; N 0 0, N 0 1] -
      !![0, 0; N 0 0, N 0 1] = !![N 0 0, N 0 1; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e2 : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) * !![N 1 0, N 1 1; 0, 0] -
      !![N 1 0, N 1 1; 0, 0] = !![0, 0; N 1 0, N 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e3 : N = !![N 0 0, N 0 1; 0, 0] + !![0, 0; N 1 0, N 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h1' := h1 !![0, 0; N 0 0, N 0 1]
  have h2' := h2 !![N 1 0, N 1 1; 0, 0]
  rw [e1] at h1'
  rw [e2] at h2'
  rw [e3]
  exact K.mul_mem h1' h2'

theorem top_of_second {K : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F))}
    (h1 : ∀ M : Matrix (Fin 2) (Fin 2) F,
      Multiplicative.ofAdd (M * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) - M) ∈ K)
    (h2 : ∀ M : Matrix (Fin 2) (Fin 2) F,
      Multiplicative.ofAdd (M * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) - M) ∈ K) :
    K = ⊤ := by
  rw [eq_top_iff]
  intro m _
  have hm : ∃ N, m = Multiplicative.ofAdd N := ⟨Multiplicative.toAdd m, rfl⟩
  obtain ⟨N, hN⟩ := hm
  rw [hN]
  have e1 : !![0, N 0 0; 0, N 1 0] * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F) -
      !![0, N 0 0; 0, N 1 0] = !![N 0 0, 0; N 1 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e2 : !![N 0 1, 0; N 1 1, 0] * (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) -
      !![N 0 1, 0; N 1 1, 0] = !![0, N 0 1; 0, N 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have e3 : N = !![N 0 0, 0; N 1 0, 0] + !![0, N 0 1; 0, N 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have h1' := h1 !![0, N 0 0; 0, N 1 0]
  have h2' := h2 !![N 0 1, 0; N 1 1, 0]
  rw [e1] at h1'
  rw [e2] at h2'
  rw [e3]
  exact K.mul_mem h1' h2'

end Transvections

section ModuleSection

variable {V : Type} [CommGroup V]

theorem mem_map_commV_of_act {X Y : Subgroup (MulAut V)} {S M : Type*} [Group S] [Group M]
    {act : S → M → M} (hYX : Y ≤ X) (hinv : ∀ x ∈ X, ∀ p ∈ commV X, x p ∈ commV X)
    (θ : ↥X ≃* S) (β : ↥(commV X) →* M) (hβs : Function.Surjective β)
    (hβe : ∀ (x : ↥X) (p : ↥(commV X)) (hp : (x : MulAut V) p ∈ commV X),
      β ⟨(x : MulAut V) p, hp⟩ = act (θ x) (β p))
    (y : ↥Y) (m : M) :
    act (θ (Subgroup.inclusion hYX y)) m * m⁻¹ ∈ ((commV Y).subgroupOf (commV X)).map β := by
  obtain ⟨u, rfl⟩ := hβs m
  have hyu : (y : MulAut V) (u : V) ∈ commV X := hinv y (hYX y.2) u u.2
  have hm1 : (y : MulAut V) (u : V) * (u : V)⁻¹ ∈ commV X := mul_mem hyu (inv_mem u.2)
  refine ⟨⟨(y : MulAut V) (u : V) * (u : V)⁻¹, hm1⟩, ?_, ?_⟩
  · exact G6.mem_commV_of_mem y.2 (u : V)
  · have hx : (⟨(y : MulAut V) (u : V) * (u : V)⁻¹, hm1⟩ : ↥(commV X)) =
        ⟨(y : MulAut V) (u : V), hyu⟩ * u⁻¹ := rfl
    show β _ = _
    rw [hx, map_mul, map_inv]
    congr 1
    exact hβe (Subgroup.inclusion hYX y) u hyu

theorem card_commV_eq_of_top {X Y : Subgroup (MulAut V)} {M : Type*} [Group M] (hYX : Y ≤ X)
    (β : ↥(commV X) →* M) (hβinj : Function.Injective β)
    (htop : ((commV Y).subgroupOf (commV X)).map β = ⊤) : Nat.card ↥(commV Y) = Nat.card M := by
  have h1 := Subgroup.card_map_of_injective (K := (commV Y).subgroupOf (commV X)) hβinj
  rw [htop, Subgroup.card_top] at h1
  rw [h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (commV_mono hYX)).toEquiv).symm

end ModuleSection

section Factors

variable {Γ : Type*} [Group Γ]

theorem exists_eq_fst {X Y : Subgroup Γ} {S : Type*} [Group S] [Finite S] (hYX : Y ≤ X)
    (θ : ↥X ≃* S × S) (hSL : Nonempty (↥Y ≃* S))
    (hfactor : ∀ y : ↥Y, (θ (Subgroup.inclusion hYX y)).2 = 1) (a : S) :
    ∃ y : ↥Y, θ (Subgroup.inclusion hYX y) = (a, 1) := by
  let f : ↥Y →* S := (MonoidHom.fst S S).comp (θ.toMonoidHom.comp (Subgroup.inclusion hYX))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (θ (Subgroup.inclusion hYX y)).1 = 1 := hy
    have : θ (Subgroup.inclusion hYX y) = 1 := Prod.ext h1 (hfactor y)
    have h3 : Subgroup.inclusion hYX y = 1 := θ.injective (by rw [this, map_one])
    exact (Subgroup.inclusion_injective hYX) (by rw [h3, map_one])
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, Nat.card_congr hSL.some.toEquiv⟩
  obtain ⟨y, hy⟩ := hbij.2 a
  exact ⟨y, Prod.ext hy (hfactor y)⟩

theorem exists_eq_snd {X Y : Subgroup Γ} {S : Type*} [Group S] [Finite S] (hYX : Y ≤ X)
    (θ : ↥X ≃* S × S) (hSL : Nonempty (↥Y ≃* S))
    (hfactor : ∀ y : ↥Y, (θ (Subgroup.inclusion hYX y)).1 = 1) (b : S) :
    ∃ y : ↥Y, θ (Subgroup.inclusion hYX y) = (1, b) := by
  let f : ↥Y →* S := (MonoidHom.snd S S).comp (θ.toMonoidHom.comp (Subgroup.inclusion hYX))
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (θ (Subgroup.inclusion hYX y)).2 = 1 := hy
    have : θ (Subgroup.inclusion hYX y) = 1 := Prod.ext (hfactor y) h1
    have h3 : Subgroup.inclusion hYX y = 1 := θ.injective (by rw [this, map_one])
    exact (Subgroup.inclusion_injective hYX) (by rw [h3, map_one])
  have hbij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, Nat.card_congr hSL.some.toEquiv⟩
  obtain ⟨y, hy⟩ := hbij.2 b
  exact ⟨y, Prod.ext (hfactor y) hy⟩

end Factors

section PlusMain

abbrev SLq (n : ℕ) : Type := Matrix.SpecialLinearGroup (Fin 2) (Fq n)

theorem card_matrix_fq {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))) = 2 ^ (4 * n) := by
  have hF : Nat.card (Fq n) = 2 ^ n := GaloisField.card 2 n hn
  have h1 : Nat.card (Multiplicative (Matrix (Fin 2) (Fin 2) (Fq n))) =
      Nat.card (Matrix (Fin 2) (Fin 2) (Fq n)) := Nat.card_congr Multiplicative.toAdd
  rw [h1]
  show Nat.card (Fin 2 → Fin 2 → Fq n) = _
  rw [Nat.card_fun, Nat.card_fun, hF, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
    ← pow_mul, ← pow_mul]
  ring_nf

theorem omegaPlusAct_one_mul_inv {n : ℕ} (b : SLq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    omegaPlusAct n (1, b) (Multiplicative.ofAdd M) * (Multiplicative.ofAdd M)⁻¹ =
      Multiplicative.ofAdd (M * (b : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ - M) := by
  show Multiplicative.ofAdd (((1 : SLq n) : Matrix (Fin 2) (Fin 2) (Fq n)) * M *
    (b : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ) * (Multiplicative.ofAdd M)⁻¹ = _
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, ← ofAdd_neg, ← ofAdd_add, ← sub_eq_add_neg]

theorem omegaPlusAct_mul_one_mul_inv {n : ℕ} (a : SLq n) (M : Matrix (Fin 2) (Fin 2) (Fq n)) :
    omegaPlusAct n (a, 1) (Multiplicative.ofAdd M) * (Multiplicative.ofAdd M)⁻¹ =
      Multiplicative.ofAdd ((a : Matrix (Fin 2) (Fin 2) (Fq n)) * M - M) := by
  show Multiplicative.ofAdd ((a : Matrix (Fin 2) (Fin 2) (Fq n)) * M *
    ((1 : SLq n) : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ) * (Multiplicative.ofAdd M)⁻¹ = _
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one, ← ofAdd_neg,
    ← ofAdd_add, ← sub_eq_add_neg]

theorem embOmega_plus {V : Type} [CommGroup V] [Finite V] {X Y : Subgroup (MulAut V)} {n : ℕ}
    (hn : 2 ≤ n) (hnat : IsNatSectionBy (omegaPlusAct n) X (commV X) ⊥) (hYX : Y ≤ X)
    (hSL : Nonempty (↥Y ≃* SLq n)) (hcard : Nat.card ↥(commV Y) = 2 ^ (3 * n)) :
    ∀ N : Subgroup ↥X, N.Normal → Y.subgroupOf X ≤ N → N = ⊤ := by
  classical
  obtain ⟨hinv, θ, β, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have : p ∈ β.ker := hp
    rw [hβk, Subgroup.bot_subgroupOf] at this
    exact this
  have hS : IsSimpleGroup (SLq n) := isSimpleGroup_sl2_gf hn
  have hc : Subgroup.center (SLq n) = ⊥ := center_sl2_eq_bot (Fq n)
  have hn0 : n ≠ 0 := by omega
  have hKmem : ∀ y : ↥Y, ∀ m, omegaPlusAct n (θ (Subgroup.inclusion hYX y)) m * m⁻¹ ∈
      ((commV Y).subgroupOf (commV X)).map β :=
    fun y m => mem_map_commV_of_act hYX hinv θ β hβs hβe y m
  have hKtop : ((commV Y).subgroupOf (commV X)).map β = ⊤ → False := fun h => by
    have h1 := card_commV_eq_of_top hYX β hβinj h
    rw [hcard, card_matrix_fq hn0] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  let U1 : SLq n := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let L1 : SLq n := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hTU : (U1 : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ = !![1, 0; 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [U1]
  have hTL : (L1 : Matrix (Fin 2) (Fin 2) (Fq n))ᵀ = !![1, 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [L1]
  have hA : ∃ y : ↥Y, (θ (Subgroup.inclusion hYX y)).1 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hKtop
    refine top_of_second ?_ ?_
    · intro M
      obtain ⟨y, hy⟩ := exists_eq_snd hYX θ hSL hcon U1
      have := hKmem y (Multiplicative.ofAdd M)
      rw [hy, omegaPlusAct_one_mul_inv, hTU] at this
      exact this
    · intro M
      obtain ⟨y, hy⟩ := exists_eq_snd hYX θ hSL hcon L1
      have := hKmem y (Multiplicative.ofAdd M)
      rw [hy, omegaPlusAct_one_mul_inv, hTL] at this
      exact this
  have hB : ∃ y : ↥Y, (θ (Subgroup.inclusion hYX y)).2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hKtop
    refine top_of_first ?_ ?_
    · intro M
      obtain ⟨y, hy⟩ := exists_eq_fst hYX θ hSL hcon U1
      have := hKmem y (Multiplicative.ofAdd M)
      rw [hy, omegaPlusAct_mul_one_mul_inv] at this
      exact this
    · intro M
      obtain ⟨y, hy⟩ := exists_eq_fst hYX θ hSL hcon L1
      have := hKmem y (Multiplicative.ofAdd M)
      rw [hy, omegaPlusAct_mul_one_mul_inv] at this
      exact this
  intro N hN hYN
  have hN0 : (N.map θ.toMonoidHom).Normal := hN.map θ.toMonoidHom θ.surjective
  have hY0 : ∀ y : ↥Y, θ (Subgroup.inclusion hYX y) ∈ N.map θ.toMonoidHom := fun y =>
    ⟨_, hYN (show Subgroup.inclusion hYX y ∈ Y.subgroupOf X from y.2), rfl⟩
  have htop : N.map θ.toMonoidHom = ⊤ := by
    refine eq_top_of_normal_prod hc ?_ ?_
    · obtain ⟨y, hy⟩ := hA
      exact ⟨_, hY0 y, hy⟩
    · obtain ⟨y, hy⟩ := hB
      exact ⟨_, hY0 y, hy⟩
  rw [eq_top_iff]
  intro x _
  have : θ x ∈ N.map θ.toMonoidHom := by
    rw [htop]
    trivial
  obtain ⟨z, hz, hzx⟩ := this
  have : z = x := θ.injective hzx
  rwa [← this]

end PlusMain

theorem embOmega_holds : EmbOmega := by
  intro V _ _ _ X Y n hn hnat hYX hne hSL hcard
  have hY1 : Y ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥Y = Nat.card (SLq n) := Nat.card_congr hSL.some.toEquiv
    rw [h, Subgroup.card_bot, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
      GaloisField.card 2 n (by omega)] at h1
    have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    generalize 2 ^ n = q at h1 hq
    have hq2 : 16 ≤ q * q := Nat.mul_le_mul hq hq
    rw [pow_two] at h1
    have h3 : 15 ≤ q * q - 1 := by omega
    have h4 : 4 * 15 ≤ q * (q * q - 1) := Nat.mul_le_mul hq h3
    omega
  have hmain : ∀ N : Subgroup ↥X, N.Normal → Y.subgroupOf X ≤ N → N = ⊤ := by
    rcases hnat with h | h
    · exact embOmega_plus hn h hYX hSL hcard
    · exact embOmega_minus hn h hYX hY1
  exact embOmega_conclusion hYX hne hmain

end CFSG.CGT.PushingUpLit.CGT6

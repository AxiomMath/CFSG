module

public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.SectionRank.OddCover Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Abstract

theorem index_le_card_ker_of_endo {G : Type*} [CommGroup G] [Finite G] (ψ : G →* G)
    (N : Subgroup G) (h : ∀ g, ψ g ∈ N) : N.index ≤ Nat.card ψ.ker := by
  have h1 : ψ.range ≤ N := by
    rintro _ ⟨g, rfl⟩
    exact h g
  have h2 : N.index ∣ ψ.range.index := Subgroup.index_dvd_of_le h1
  have h3 : ψ.range.index = Nat.card ψ.ker := by
    have a := Subgroup.card_mul_index ψ.range
    have b := Subgroup.card_ker_mul_card_range ψ
    have hpos : 0 < Nat.card ψ.range := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (a.trans (b.symm.trans (mul_comm _ _)))
  rw [h3] at h2
  exact Nat.le_of_dvd Nat.card_pos h2

theorem relIndex_map_eq_of_ker_le {G H : Type*} [Group G] [Group H] (f : G →* H)
    {B N : Subgroup G} (hNB : N ≤ B) (hk : f.ker ⊓ B ≤ N) :
    (N.map f).relIndex (B.map f) = N.relIndex B := by
  let fB : B →* B.map f := f.subgroupMap B
  have hsurj : Function.Surjective fB := f.subgroupMap_surjective B
  have hker : fB.ker ≤ N.subgroupOf B := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : f x = 1 := congrArg Subtype.val hx
    exact hk ⟨hx', x.2⟩
  have h := Subgroup.index_map_eq (N.subgroupOf B) hsurj hker
  have hmap : (N.subgroupOf B).map fB = (N.map f).subgroupOf (B.map f) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨b, hb, hby⟩
      exact ⟨b.1, hb, congrArg Subtype.val hby⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hNB hb⟩, hb, rfl⟩
  rw [hmap] at h
  exact h

end Abstract

section KK

variable {K : Type} [Field K]

@[expose] def sig2 : Kˣ × Kˣ →* Kˣ × Kˣ where
  toFun x := ((x.1 * x.2)⁻¹, x.1)
  map_one' := by simp
  map_mul' x y := by
    refine Prod.ext ?_ rfl
    show ((x.1 * y.1) * (x.2 * y.2))⁻¹ = (x.1 * x.2)⁻¹ * (y.1 * y.2)⁻¹
    rw [mul_mul_mul_comm, mul_inv]

theorem sig2_apply (x : Kˣ × Kˣ) : sig2 x = ((x.1 * x.2)⁻¹, x.1) := rfl

theorem fixed_of_sig2 {x : Kˣ × Kˣ} (h : sig2 x = x) : x.1 ^ 3 = 1 ∧ x.2 = x.1 := by
  rw [sig2_apply] at h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only at e1 e2
  refine ⟨?_, e2.symm⟩
  rw [← e2, inv_eq_iff_mul_eq_one] at e1
  rw [pow_three']
  exact e1

theorem card_ker_le_three [Finite K] (B : Subgroup (Kˣ × Kˣ)) (ψ : B →* B)
    (hψ : ∀ b : B, ((ψ b : B) : Kˣ × Kˣ) = sig2 b * (b : Kˣ × Kˣ)⁻¹) :
    Nat.card ψ.ker ≤ 3 := by
  have hfix : ∀ b : ψ.ker, ((b : B) : Kˣ × Kˣ).1 ^ 3 = 1 ∧
      ((b : B) : Kˣ × Kˣ).2 = ((b : B) : Kˣ × Kˣ).1 := by
    intro b
    apply fixed_of_sig2
    have h1 := hψ b
    rw [MonoidHom.mem_ker.1 b.2] at h1
    have h2 : (1 : Kˣ × Kˣ) = sig2 ((b : B) : Kˣ × Kˣ) * ((b : B) : Kˣ × Kˣ)⁻¹ := h1
    exact (mul_inv_eq_one.1 h2.symm)
  let φ : ψ.ker → rootsOfUnity 3 K := fun b => ⟨((b : B) : Kˣ × Kˣ).1, (mem_rootsOfUnity _ _).2 (hfix b).1⟩
  have hφ : Function.Injective φ := by
    intro b c hbc
    have h1 : ((b : B) : Kˣ × Kˣ).1 = ((c : B) : Kˣ × Kˣ).1 := congrArg Subtype.val hbc
    apply Subtype.ext
    apply Subtype.ext
    refine Prod.ext h1 ?_
    rw [(hfix b).2, (hfix c).2, h1]
  calc Nat.card ψ.ker ≤ Nat.card (rootsOfUnity 3 K) := Nat.card_le_card_of_injective φ hφ
    _ ≤ 3 := card_rootsOfUnity K 3

theorem card_ker_cube_le_nine [Finite K] (B : Subgroup (Kˣ × Kˣ)) :
    Nat.card (powMonoidHom 3 : B →* B).ker ≤ 9 := by
  have hker : ∀ b : (powMonoidHom 3 : B →* B).ker, ((b : B) : Kˣ × Kˣ).1 ^ 3 = 1 ∧
      ((b : B) : Kˣ × Kˣ).2 ^ 3 = 1 := by
    intro b
    have h1 : ((b : B) : Kˣ × Kˣ) ^ 3 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 b.2)
    exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
  let φ : (powMonoidHom 3 : B →* B).ker → rootsOfUnity 3 K × rootsOfUnity 3 K := fun b =>
    (⟨((b : B) : Kˣ × Kˣ).1, (mem_rootsOfUnity _ _).2 (hker b).1⟩,
     ⟨((b : B) : Kˣ × Kˣ).2, (mem_rootsOfUnity _ _).2 (hker b).2⟩)
  have hφ : Function.Injective φ := by
    intro b c hbc
    simp only [φ, Prod.mk.injEq, Subtype.mk.injEq] at hbc
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hbc.1 hbc.2
  calc Nat.card (powMonoidHom 3 : B →* B).ker
      ≤ Nat.card (rootsOfUnity 3 K × rootsOfUnity 3 K) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card (rootsOfUnity 3 K) * Nat.card (rootsOfUnity 3 K) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity K 3) (card_rootsOfUnity K 3)
    _ = 9 := by norm_num

theorem relIndex_le_nine_of_cube [Finite K] (B N : Subgroup (Kˣ × Kˣ)) (_hNB : N ≤ B)
    (hcube : ∀ b ∈ B, b ^ 3 ∈ N) : N.relIndex B ≤ 9 := by
  have := index_le_card_ker_of_endo (powMonoidHom 3 : B →* B) (N.subgroupOf B)
    (fun g => by
      show ((g : Kˣ × Kˣ) ^ 3) ∈ N
      exact hcube g g.2)
  exact this.trans (card_ker_cube_le_nine B)

theorem relIndex_le_three_of_sig2 [Finite K] (B N : Subgroup (Kˣ × Kˣ)) (_hNB : N ≤ B)
    (hB : ∀ b ∈ B, sig2 b ∈ B) (hN : ∀ b ∈ B, sig2 b * b⁻¹ ∈ N) : N.relIndex B ≤ 3 := by
  let ψ : B →* B :=
    { toFun := fun b => ⟨sig2 b * (b : Kˣ × Kˣ)⁻¹, B.mul_mem (hB b b.2) (B.inv_mem b.2)⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show sig2 ((x : Kˣ × Kˣ) * (y : Kˣ × Kˣ)) * ((x : Kˣ × Kˣ) * (y : Kˣ × Kˣ))⁻¹ =
          (sig2 x * (x : Kˣ × Kˣ)⁻¹) * (sig2 y * (y : Kˣ × Kˣ)⁻¹)
        rw [map_mul, mul_inv]
        exact mul_mul_mul_comm _ _ _ _ }
  have h1 := index_le_card_ker_of_endo ψ (N.subgroupOf B) (fun g => hN g g.2)
  exact h1.trans (card_ker_le_three B ψ (fun b => rfl))

end KK



section Gamma

variable {K : Type} [Field K]

@[expose] def shiftΓ (d : Fin 3 → Kˣ) : Fin 3 → Kˣ := ![d 2, d 0, d 1]

@[expose] def lamΓ : (Fin 3 → Kˣ) →* Kˣ × Kˣ where
  toFun d := (d 0 * (d 1)⁻¹, d 1 * (d 2)⁻¹)
  map_one' := by simp
  map_mul' x y := by
    refine Prod.ext ?_ ?_
    · show x 0 * y 0 * (x 1 * y 1)⁻¹ = x 0 * (x 1)⁻¹ * (y 0 * (y 1)⁻¹)
      rw [mul_inv]; exact mul_mul_mul_comm _ _ _ _
    · show x 1 * y 1 * (x 2 * y 2)⁻¹ = x 1 * (x 2)⁻¹ * (y 1 * (y 2)⁻¹)
      rw [mul_inv]; exact mul_mul_mul_comm _ _ _ _

theorem lamΓ_apply (d : Fin 3 → Kˣ) : lamΓ d = (d 0 * (d 1)⁻¹, d 1 * (d 2)⁻¹) := rfl

theorem lamΓ_shift (d : Fin 3 → Kˣ) : lamΓ (shiftΓ d) = sig2 (lamΓ d) := by
  rw [sig2_apply]
  refine Prod.ext ?_ ?_
  · simp only [lamΓ_apply, shiftΓ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    group
  · simp only [lamΓ_apply, shiftΓ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]

theorem const_of_lamΓ_eq_one {d : Fin 3 → Kˣ} (h : lamΓ d = 1) : ∀ i, d i = d 0 := by
  rw [lamΓ_apply] at h
  have e1 := congrArg Prod.fst h
  have e2 := congrArg Prod.snd h
  simp only [Prod.fst_one, Prod.snd_one, mul_inv_eq_one] at e1 e2
  intro i
  fin_cases i
  · rfl
  · exact e1.symm
  · exact e2.symm.trans e1.symm

variable [Finite K]

theorem relIndex_le_three_Gamma (B N : Subgroup (Fin 3 → Kˣ)) (hNB : N ≤ B)
    (hB : ∀ d ∈ B, shiftΓ d ∈ B) (hN : ∀ d ∈ B, shiftΓ d * d⁻¹ ∈ N)
    (hC : ∀ d ∈ B, (∀ i, d i = d 0) → d ∈ N) : N.relIndex B ≤ 3 := by
  have hk : lamΓ.ker ⊓ B ≤ N := fun d hd => hC d hd.2 (const_of_lamΓ_eq_one hd.1)
  rw [← relIndex_map_eq_of_ker_le lamΓ hNB hk]
  refine relIndex_le_three_of_sig2 _ _ (Subgroup.map_mono hNB) ?_ ?_
  · rintro _ ⟨d, hd, rfl⟩
    exact ⟨shiftΓ d, hB d hd, lamΓ_shift d⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact ⟨shiftΓ d * d⁻¹, hN d hd, by rw [map_mul, map_inv, lamΓ_shift]⟩

theorem relIndex_le_nine_Gamma (B N : Subgroup (Fin 3 → Kˣ)) (hNB : N ≤ B)
    (hcube : ∀ d ∈ B, d ^ 3 ∈ N)
    (hC : ∀ d ∈ B, (∀ i, d i = d 0) → d ∈ N) : N.relIndex B ≤ 9 := by
  have hk : lamΓ.ker ⊓ B ≤ N := fun d hd => hC d hd.2 (const_of_lamΓ_eq_one hd.1)
  rw [← relIndex_map_eq_of_ker_le lamΓ hNB hk]
  refine relIndex_le_nine_of_cube _ _ (Subgroup.map_mono hNB) ?_
  rintro _ ⟨d, hd, rfl⟩
  exact ⟨d ^ 3, hcube d hd, by rw [map_pow]⟩

end Gamma

section GL3

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def torusFHom (M : Subgroup Kˣ) : (Fin 3 → M) →* GL (Fin 3) K where
  toFun d := diagHom 3 (fun i => (d i : Kˣ))
  map_one' := by
    show diagHom (K := K) 3 (1 : Fin 3 → Kˣ) = 1
    exact map_one _
  map_mul' x y := by
    show diagHom (K := K) 3 ((fun i => (x i : Kˣ)) * (fun i => (y i : Kˣ))) = _
    rw [map_mul]

theorem torusFHom_injective (M : Subgroup Kˣ) : Function.Injective (torusFHom (K := K) M) := by
  intro x y h
  have h' := diagHom_injective 3 h
  funext i
  exact Subtype.ext (congrFun h' i)

@[expose] noncomputable def torusF (M : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) :=
  (torusFHom M).range

theorem mem_torusF {M : Subgroup Kˣ} {x : GL (Fin 3) K} :
    x ∈ torusF M ↔ ∃ d : Fin 3 → Kˣ, (∀ i, d i ∈ M) ∧ x = diagHom 3 d := by
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨fun i => (d i : Kˣ), fun i => (d i).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨fun i => ⟨d i, hd i⟩, rfl⟩

theorem card_torusF (M : Subgroup Kˣ) : Nat.card (torusF (K := K) M) = Nat.card M ^ 3 := by
  rw [torusF, ← Nat.card_congr (MonoidHom.ofInjective (torusFHom_injective M)).toEquiv,
    Nat.card_fun]
  simp

theorem torusF_comm (M : Subgroup Kˣ) {x y : GL (Fin 3) K} (hx : x ∈ torusF M)
    (hy : y ∈ torusF M) : x * y = y * x := by
  obtain ⟨a, -, rfl⟩ := mem_torusF.1 hx
  obtain ⟨b, -, rfl⟩ := mem_torusF.1 hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem cycGL_conj_mem_torusF (M : Subgroup Kˣ) {x : GL (Fin 3) K} (hx : x ∈ torusF M) :
    cycGL * x * cycGL⁻¹ ∈ torusF M := by
  obtain ⟨d, hd, rfl⟩ := mem_torusF.1 hx
  rw [cycGL_conj_diagHom]
  refine mem_torusF.2 ⟨_, fun i => ?_, rfl⟩
  fin_cases i <;> simp [hd]

theorem cycGL_mem_normalizer_torusF (M : Subgroup Kˣ) :
    cycGL ∈ Subgroup.normalizer (torusF (K := K) M : Set (GL (Fin 3) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact cycGL_conj_mem_torusF M
  · intro hx
    have h := cycGL_conj_mem_torusF M (cycGL_conj_mem_torusF M hx)
    rw [show cycGL * (cycGL * (cycGL * x * cycGL⁻¹) * cycGL⁻¹) * cycGL⁻¹ =
        (cycGL * cycGL * cycGL) * x * (cycGL * cycGL * cycGL)⁻¹ by group] at h
    have h3' : (cycGL : GL (Fin 3) K) * cycGL * cycGL = 1 := by
      calc (cycGL : GL (Fin 3) K) * cycGL * cycGL = cycGL ^ 3 := by rw [pow_three, mul_assoc]
        _ = 1 := cycGL_pow_three
    rw [h3', one_mul, inv_one, mul_one] at h
    exact h

theorem zpow_cycGL_mem_torusF (M : Subgroup Kˣ) {k : ℤ}
    (hk : (cycGL : GL (Fin 3) K) ^ k ∈ torusF M) : (cycGL : GL (Fin 3) K) ^ k = 1 := by
  have h3 : (cycGL : GL (Fin 3) K) ^ k = cycGL ^ ((k % 3).toNat) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    have h := zpow_mod_orderOf (cycGL : GL (Fin 3) K) k
    rw [orderOf_cycGL] at h
    exact h.symm
  rw [h3] at hk ⊢
  have hlt : (k % 3).toNat < 3 := by omega
  obtain ⟨d, -, hd⟩ := mem_torusF.1 hk
  interval_cases h : (k % 3).toNat
  · rw [pow_zero]
  · exfalso
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hd) 1) 0
    simp [coe_cycGL, cycMat, coe_diagHom] at this
  · exfalso
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hd) 2) 0
    simp [coe_cycGL, cycMat, coe_diagHom, sq, Matrix.mul_apply, Fin.sum_univ_three] at this

theorem card_torusF_sup_cyc (M : Subgroup Kˣ) :
    Nat.card ↥(torusF M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K)) = 3 * Nat.card M ^ 3 := by
  rw [card_sup_zpowers_of_normalizer (cycGL_mem_normalizer_torusF M)
    (fun k hk => zpow_cycGL_mem_torusF M hk), card_torusF, orderOf_cycGL, mul_comm]

theorem relIndex_torusF_sup_cyc (M : Subgroup Kˣ) :
    (torusF M).relIndex (torusF M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K)) = 3 := by
  have hle : torusF M ≤ torusF M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K) := le_sup_left
  have h := Subgroup.relIndex_mul_card (torusF M)
    (torusF M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K))
  rw [inf_eq_left.2 hle, card_torusF, card_torusF_sup_cyc] at h
  have hpos : 0 < Nat.card M ^ 3 := pow_pos Nat.card_pos 3
  exact Nat.eq_of_mul_eq_mul_right hpos h

theorem scalar_eq_diagHom' (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 3) c = diagHom 3 (fun _ => c) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_scalar, coe_diagHom]
  rfl

theorem relIndex_comap_diagHom {N S : Subgroup (GL (Fin 3) K)} (hNS : N ≤ S)
    (hS : S ≤ (diagHom (K := K) 3).range) :
    N.relIndex S = (N.comap (diagHom 3)).relIndex (S.comap (diagHom 3)) := by
  rw [← Subgroup.relIndex_map_map_of_injective (N.comap _) (S.comap _) (diagHom_injective 3),
    Subgroup.map_comap_eq_self (hNS.trans hS), Subgroup.map_comap_eq_self hS]

end GL3

section Main

variable {K : Type} [Field K] [Finite K]

theorem conj_by_torus_mul_cyc (M : Subgroup Kˣ) {t s : GL (Fin 3) K} (ht : t ∈ torusF M)
    (hs : s ∈ torusF M) :
    (t * cycGL) * s * (t * cycGL)⁻¹ = cycGL * s * cycGL⁻¹ := by
  have hu := cycGL_conj_mem_torusF M hs
  have hcomm := torusF_comm M ht hu
  calc (t * cycGL) * s * (t * cycGL)⁻¹ = t * (cycGL * s * cycGL⁻¹) * t⁻¹ := by group
    _ = (cycGL * s * cycGL⁻¹ * t) * t⁻¹ := by rw [hcomm]
    _ = cycGL * s * cycGL⁻¹ := by group

theorem exists_torus_mul_cyc_mem (M : Subgroup Kˣ) {S : Subgroup (GL (Fin 3) K)}
    (hS : S ≤ torusF M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K))
    (hST : ¬ S ≤ torusF M) : ∃ t ∈ torusF M, t * cycGL ∈ S := by
  obtain ⟨x, hxS, hxT⟩ := Set.not_subset.1 hST
  obtain ⟨t, ht, j, hj, rfl⟩ :=
    exists_mul_pow_of_mem_sup_zpowers (cycGL_mem_normalizer_torusF M) (hS hxS)
  rw [orderOf_cycGL] at hj
  have h3 : (cycGL : GL (Fin 3) K) ^ 3 = 1 := cycGL_pow_three
  interval_cases j
  · rw [pow_zero, mul_one] at hxT
    exact absurd ht hxT
  · exact ⟨t, ht, by simpa using hxS⟩
  · refine ⟨cycGL * t⁻¹ * cycGL⁻¹, ?_, ?_⟩
    · have := cycGL_conj_mem_torusF M ((torusF M).inv_mem ht)
      exact this
    · have hinv : (t * cycGL ^ 2)⁻¹ ∈ S := S.inv_mem hxS
      have e : (t * cycGL ^ 2)⁻¹ = cycGL * t⁻¹ * cycGL⁻¹ * cycGL := by
        have hw : (cycGL : GL (Fin 3) K)⁻¹ = cycGL ^ 2 := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', h3]
        have hw2 : ((cycGL : GL (Fin 3) K) ^ 2)⁻¹ = cycGL := by
          rw [← hw, inv_inv]
        rw [_root_.mul_inv_rev, hw2]
        group
      rw [← e]
      exact hinv

theorem relIndex_le_nine_of_le_monomial (M : Subgroup Kˣ) {S N : Subgroup (GL (Fin 3) K)}
    (hNS : N ≤ S) (hS : S ≤ torusF M ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K))
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, ⁅x, y⁆ ∈ N) (hcube : ∀ x ∈ S, x ^ 3 ∈ N)
    (hZ : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ S →
      Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ N) :
    N.relIndex S ≤ 9 := by
  classical
  set T := torusF M with hT
  set Sy := T ⊔ Subgroup.zpowers (cycGL : GL (Fin 3) K) with hSy
  have hTr : (diagHom (K := K) 3).range = (diagHom (K := K) 3).range := rfl
  have hTle : T ≤ (diagHom (K := K) 3).range := fun x hx => by
    obtain ⟨d, -, rfl⟩ := mem_torusF.1 hx
    exact ⟨d, rfl⟩
  have hconst : ∀ {R : Subgroup (GL (Fin 3) K)}, (∀ c : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ S → Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ R) →
      ∀ d : Fin 3 → Kˣ, diagHom 3 d ∈ S → (∀ i, d i = d 0) → diagHom 3 d ∈ R := by
    intro R hR d hd hconst
    have : d = fun _ => d 0 := funext hconst
    rw [this, ← scalar_eq_diagHom'] at hd ⊢
    exact hR _ hd
  by_cases hST : S ≤ T
  · rw [relIndex_comap_diagHom hNS (hST.trans hTle)]
    refine relIndex_le_nine_Gamma _ _ (Subgroup.comap_mono hNS) ?_ ?_
    · intro d hd
      show diagHom 3 (d ^ 3) ∈ N
      rw [map_pow]
      exact hcube _ hd
    · intro d hd hd0
      exact hconst hZ d hd hd0
  · obtain ⟨t1, ht1, hx1⟩ := exists_torus_mul_cyc_mem M hS hST
    set S0 := S ⊓ T with hS0
    set N1 := N ⊓ S0 with hN1
    have hS0S : S0 ≤ S := inf_le_left
    have hN1S0 : N1 ≤ S0 := inf_le_right
    have hN1N : N1 ≤ N := inf_le_left
    have hS0T : S0 ≤ T := inf_le_right
    have h1 : S0.relIndex S ≤ 3 := by
      have h := Subgroup.inf_relIndex_right T S
      rw [inf_comm] at h
      rw [hS0, h]
      have hne : T.relIndex Sy ≠ 0 := by rw [hSy, relIndex_torusF_sup_cyc]; norm_num
      have := Subgroup.relIndex_le_of_le_right hS hne
      rwa [hSy, relIndex_torusF_sup_cyc] at this
    have hshift : ∀ d : Fin 3 → Kˣ, diagHom 3 d ∈ S0 → diagHom 3 (shiftΓ d) ∈ S0 := by
      intro d hd
      have hdS : diagHom 3 d ∈ S := hS0S hd
      have hdT : diagHom 3 d ∈ T := hS0T hd
      have hc := conj_by_torus_mul_cyc M ht1 hdT
      have e : diagHom 3 (shiftΓ d) = (t1 * cycGL) * diagHom 3 d * (t1 * cycGL)⁻¹ := by
        rw [hc, cycGL_conj_diagHom]; rfl
      refine ⟨?_, mem_torusF.2 ⟨_, ?_, rfl⟩⟩
      · rw [e]
        exact S.mul_mem (S.mul_mem hx1 hdS) (S.inv_mem hx1)
      · intro i
        obtain ⟨e', he', hee⟩ := mem_torusF.1 hdT
        have := diagHom_injective 3 hee
        subst this
        fin_cases i <;> simp [shiftΓ, he']
    have h2 : N1.relIndex S0 ≤ 3 := by
      rw [relIndex_comap_diagHom hN1S0 (hS0T.trans hTle)]
      refine relIndex_le_three_Gamma _ _ (Subgroup.comap_mono hN1S0) hshift ?_ ?_
      · intro d hd
        have hdS : diagHom 3 d ∈ S := hS0S hd
        have hdT : diagHom 3 d ∈ T := hS0T hd
        have hc := conj_by_torus_mul_cyc M ht1 hdT
        have e : diagHom 3 (shiftΓ d * d⁻¹) = ⁅t1 * cycGL, diagHom 3 d⁆ := by
          rw [map_mul, map_inv, commutatorElement_def, hc, cycGL_conj_diagHom]; rfl
        have hcN : ⁅t1 * cycGL, diagHom 3 d⁆ ∈ N := hcomm _ hx1 _ hdS
        refine ⟨?_, ?_⟩
        · show diagHom 3 (shiftΓ d * d⁻¹) ∈ N
          rw [e]
          exact hcN
        · show diagHom 3 (shiftΓ d * d⁻¹) ∈ S0
          rw [map_mul, map_inv]
          exact S0.mul_mem (hshift d hd) (S0.inv_mem hd)
      · intro d hd hd0
        have hdS : diagHom 3 d ∈ S := hS0S hd
        exact ⟨hconst hZ d hdS hd0, hd⟩
    have h3 : N.relIndex S ∣ N1.relIndex S := Subgroup.relIndex_dvd_of_le_left S hN1N
    have h4 : N1.relIndex S = N1.relIndex S0 * S0.relIndex S :=
      (Subgroup.relIndex_mul_relIndex N1 S0 S hN1S0 hS0S).symm
    have hpos : N1.relIndex S ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    calc N.relIndex S ≤ N1.relIndex S := Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h3
      _ = N1.relIndex S0 * S0.relIndex S := h4
      _ ≤ 3 * 3 := Nat.mul_le_mul h2 h1
      _ = 9 := by norm_num

end Main

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

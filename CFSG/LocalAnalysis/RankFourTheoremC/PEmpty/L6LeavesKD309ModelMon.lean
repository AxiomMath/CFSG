module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieMon
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMonEmb
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieMap

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

open CFSG.LocalAnalysis.RankThreeUC.S15.ACore Equiv Subgroup Fin.NatCast
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L

@[expose] def PmC (C : Type) [CommGroup C] : Subgroup (Mon C 5) := (zpowers sig5).comap monPerm

variable {C : Type} [CommGroup C]

theorem mem_PmC {x : Mon C 5} : x ∈ PmC C ↔ x.right ∈ zpowers sig5 := Iff.rfl

theorem monT_mem_PmC (t : Fin 5 → C) : monT t ∈ PmC C := by
  rw [mem_PmC]
  change (monPerm (monT t)) ∈ zpowers sig5
  rw [monPerm_monT]
  exact one_mem _

theorem monS_mem_PmC : monS (C := C) sig5 ∈ PmC C := by
  rw [mem_PmC]
  change (monPerm (monS (C := C) sig5)) ∈ zpowers sig5
  rw [monPerm_monS]
  exact mem_zpowers _

theorem monPerm_surjective : Function.Surjective (monPerm : Mon C 5 →* Perm (Fin 5)) :=
  fun σ => ⟨monS σ, monPerm_monS σ⟩

theorem card_PmC [Finite C] : Nat.card (PmC C) = Nat.card C ^ 5 * 5 := by
  have h1 := Subgroup.card_mul_index (PmC C)
  have h2 : (PmC C).index = (zpowers sig5).index :=
    Subgroup.index_comap_of_surjective _ monPerm_surjective
  have h3 := Subgroup.card_mul_index (zpowers sig5)
  rw [Nat.card_zpowers, orderOf_sig5, Nat.card_perm, Nat.card_fin] at h3
  have h4 : (zpowers sig5).index = 24 := by
    have h5 : (5 : ℕ).factorial = 120 := by decide
    rw [h5] at h3
    omega
  rw [card_mon, h2, h4] at h1
  have h6 : (5 : ℕ).factorial = 120 := by decide
  rw [h6] at h1
  omega

@[expose] def monSub (C : Type) [CommGroup C] : Subgroup (Mon C 5) :=
  PmC C ⊓ (monDet : Mon C 5 →* C).ker

theorem mem_monSub {x : Mon C 5} : x ∈ monSub C ↔ x ∈ PmC C ∧ monDet x = 1 := Iff.rfl

theorem card_Pm : Nat.card Pm = 5 ^ 6 := by
  have h := card_PmC (C := C5)
  rw [card_C5] at h
  rw [show Nat.card Pm = Nat.card (PmC C5) from rfl, h]
  norm_num

theorem card_monSub_mul [Finite C] : Nat.card (monSub C) * Nat.card C = Nat.card C ^ 5 * 5 := by
  set f : PmC C →* C := (monDet : Mon C 5 →* C).comp (PmC C).subtype with hf
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨⟨monT (fun i => if i = 0 then c else 1), monT_mem_PmC _⟩, ?_⟩
    change monDet (monT (fun i : Fin 5 => if i = 0 then c else 1)) = c
    rw [monDet_monT]
    simp [Fin.prod_univ_five]
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, card_PmC] at h1
  have h2 : f.ker = (monSub C).subgroupOf (PmC C) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_monSub]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hle : monSub C ≤ PmC C := inf_le_left
  rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h1
  exact h1

theorem card_monSub [Finite C] : Nat.card (monSub C) = Nat.card C ^ 4 * 5 := by
  have h := card_monSub_mul (C := C)
  have hpos : 0 < Nat.card C := Nat.card_pos
  have : Nat.card (monSub C) * Nat.card C = Nat.card C ^ 4 * 5 * Nat.card C := by
    rw [h]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem monS_mul_gen (a b : Perm (Fin 5)) : monS (C := C) (a * b) = monS a * monS b :=
  map_mul (SemidirectProduct.inr : Perm (Fin 5) →* Mon C 5) a b

theorem monS_one_gen : monS (C := C) (1 : Perm (Fin 5)) = 1 :=
  map_one (SemidirectProduct.inr : Perm (Fin 5) →* Mon C 5)

theorem monT_one_gen : monT (C := C) (1 : Fin 5 → C) = 1 :=
  map_one (SemidirectProduct.inl : (Fin 5 → C) →* Mon C 5)

theorem monS_mul_monT (σ : Perm (Fin 5)) (t : Fin 5 → C) :
    monS σ * monT t = monT (t ∘ σ.symm) * monS σ := by
  have h := monS_mul_monT_mul_monS_inv σ t
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem pow_monT_mul_monS (t : Fin 5 → C) (σ : Perm (Fin 5)) (n : ℕ) :
    (monT t * monS σ) ^ n =
      monT (∏ j ∈ Finset.range n, fun i => t ((σ ^ j)⁻¹ i)) * monS (σ ^ n) := by
  induction n with
  | zero => simp [monT, monS]
  | succ n ih =>
    have hprod : (∏ j ∈ Finset.range (n + 1), fun i => t ((σ ^ j)⁻¹ i)) =
        t * ((∏ j ∈ Finset.range n, fun i => t ((σ ^ j)⁻¹ i)) ∘ σ.symm) := by
      rw [Finset.prod_range_succ', mul_comm]
      congr 1
      funext i
      simp only [Function.comp_apply, Finset.prod_apply]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [pow_succ', mul_inv_rev]
      rfl
    calc (monT t * monS σ) ^ (n + 1) = (monT t * monS σ) * (monT t * monS σ) ^ n := pow_succ' _ _
      _ = monT t * (monS σ * monT (∏ j ∈ Finset.range n, fun i => t ((σ ^ j)⁻¹ i))) *
            monS (σ ^ n) := by rw [ih]; simp only [mul_assoc]
      _ = monT t * (monT ((∏ j ∈ Finset.range n, fun i => t ((σ ^ j)⁻¹ i)) ∘ σ.symm) *
            monS σ) * monS (σ ^ n) := by rw [monS_mul_monT]
      _ = monT (t * ((∏ j ∈ Finset.range n, fun i => t ((σ ^ j)⁻¹ i)) ∘ σ.symm)) *
            monS (σ * σ ^ n) := by
          rw [monT_mul, monS_mul_gen]
          simp only [mul_assoc]
      _ = monT (∏ j ∈ Finset.range (n + 1), fun i => t ((σ ^ j)⁻¹ i)) * monS (σ ^ (n + 1)) := by
          rw [hprod, pow_succ']

theorem sig5_pow_apply (n : ℕ) (i : Fin 5) : (sig5 ^ n) i = i + (n : Fin 5) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, sig5_apply, Nat.cast_succ, add_assoc]

theorem sig5_pow_inv_apply (n : ℕ) (i : Fin 5) : (sig5 ^ n)⁻¹ i = i - (n : Fin 5) := by
  rw [Equiv.Perm.inv_eq_iff_eq, sig5_pow_apply, sub_add_cancel]

theorem prod_orbit (t : Fin 5 → C) (n : ℕ) (hn : (n : Fin 5) ≠ 0) (i : Fin 5) :
    ∏ j ∈ Finset.range 5, t ((sig5 ^ (n * j))⁻¹ i) = ∏ x, t x := by
  have hinj : ∀ k i : Fin 5, k ≠ 0 → Function.Injective (fun j : Fin 5 => i - k * j) := by
    decide +kernel
  have hbij : Function.Bijective (fun j : Fin 5 => i - (n : Fin 5) * j) :=
    Finite.injective_iff_bijective.mp (hinj _ i hn)
  rw [Finset.prod_range]
  refine Fintype.prod_bijective (fun j : Fin 5 => i - (n : Fin 5) * j) hbij _ t (fun j => ?_)
  rw [sig5_pow_inv_apply]
  congr 2
  ext
  simp [Fin.val_mul, Nat.mul_mod]

theorem monT_injective_gen : Function.Injective (monT : (Fin 5 → C) → Mon C 5) :=
  SemidirectProduct.inl_injective

theorem pow_five_monSub (hC : ∀ c : C, c ^ 5 = 1) {m : Mon C 5} (hm : m ∈ monSub C) :
    m ^ 5 = 1 := by
  have hmP : m ∈ PmC C := hm.1
  have hdet : monDet m = 1 := hm.2
  have hdet' : ∏ i, m.left i = 1 := by
    have h1 : monDet m = ∏ i, m.left i := by
      conv_lhs => rw [mon_eq_monT_mul_monS m]
      rw [map_mul, monDet_monT, monDet_monS, mul_one]
    rw [← h1]
    exact hdet
  obtain ⟨n, hn⟩ : ∃ n : ℕ, sig5 ^ n = m.right := by
    have h := mem_powers_iff_mem_zpowers.mpr (mem_PmC.mp hmP)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp h
    exact ⟨n, hn⟩
  have hm' : m = monT m.left * monS (sig5 ^ n) := by
    rw [hn]
    exact mon_eq_monT_mul_monS m
  rw [hm', pow_monT_mul_monS]
  by_cases h0 : (n : Fin 5) = 0
  · have h5 : 5 ∣ n := Fin.natCast_eq_zero.mp h0
    obtain ⟨k, rfl⟩ := h5
    have h1 : sig5 ^ (5 * k) = 1 := by rw [pow_mul, sig5_pow_five, one_pow]
    have h2 : (∏ j ∈ Finset.range 5, fun i => m.left (((sig5 ^ (5 * k)) ^ j)⁻¹ i)) = 1 := by
      funext i
      rw [Finset.prod_apply]
      simp only [h1, one_pow, inv_one, Equiv.Perm.coe_one, id_eq, Finset.prod_const,
        Finset.card_range]
      exact hC _
    rw [h2, monT_one_gen, h1, one_pow, monS_one_gen, mul_one]
  · have h3 : (sig5 ^ (n * 5)) = 1 := by rw [mul_comm, pow_mul, sig5_pow_five, one_pow]
    have hpow : (sig5 ^ n) ^ 5 = 1 := by rw [← pow_mul, h3]
    have hprod : (∏ j ∈ Finset.range 5, fun i => m.left (((sig5 ^ n) ^ j)⁻¹ i)) = 1 := by
      funext i
      rw [Finset.prod_apply]
      have : ∀ j ∈ Finset.range 5, m.left (((sig5 ^ n) ^ j)⁻¹ i) =
          m.left ((sig5 ^ (n * j))⁻¹ i) := fun j _ => by rw [pow_mul]
      rw [Finset.prod_congr rfl this, prod_orbit m.left n h0 i, hdet']
      rfl
    rw [hprod, hpow, monT_one_gen, monS_one_gen, mul_one]

theorem not_comm_monSub {c : C} (hc : c ^ 2 ≠ 1) :
    ∃ a ∈ monSub C, ∃ b ∈ monSub C, a * b ≠ b * a := by
  refine ⟨monT ![c, c⁻¹, 1, 1, 1], ⟨monT_mem_PmC _, MonoidHom.mem_ker.mpr ?_⟩, monS sig5,
    ⟨monS_mem_PmC, MonoidHom.mem_ker.mpr ?_⟩, ?_⟩
  · rw [monDet_monT]
    simp [Fin.prod_univ_five]
  · rw [monDet_monS]
  · intro h
    have h1 : monS sig5 * monT ![c, c⁻¹, 1, 1, 1] = monT ![c, c⁻¹, 1, 1, 1] * monS sig5 := h.symm
    rw [monS_mul_monT] at h1
    have h2 := mul_right_cancel h1
    have h3 := monT_injective_gen h2
    have h4 := congrFun h3 1
    simp only [Function.comp_apply, sig5_symm_apply] at h4
    have h5 : (1 : Fin 5) - 1 = 0 := by decide
    rw [h5] at h4
    simp at h4
    apply hc
    rw [pow_two]
    have h6 : c = c⁻¹ := h4
    calc c * c = c * c⁻¹ := by rw [← h6]
      _ = 1 := mul_inv_cancel c

theorem isPGroup_monSub [Finite C] {a : ℕ} (hC : Nat.card C = 5 ^ a) :
    IsPGroup 5 (monSub C) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine IsPGroup.of_card (n := 4 * a + 1) ?_
  rw [card_monSub, hC, ← pow_mul, ← pow_succ, mul_comm]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M

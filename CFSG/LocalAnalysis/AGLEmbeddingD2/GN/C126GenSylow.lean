module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenPerm

public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm

variable {N : ℕ}

def fixTwo (p x : Fin N) : Subgroup (Perm (Fin N)) where
  carrier := {σ | σ p = p ∧ σ x = x}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨by simp [Perm.mul_apply, ha.1, hb.1], by simp [Perm.mul_apply, ha.2, hb.2]⟩
  inv_mem' := fun {a} ha =>
    ⟨Equiv.Perm.inv_eq_iff_eq.2 ha.1.symm, Equiv.Perm.inv_eq_iff_eq.2 ha.2.symm⟩

theorem card_fixTwo (p x : Fin N) (hpx : p ≠ x) : Nat.card ↥(fixTwo p x) = (N - 2).factorial := by
  classical
  let q : Fin N → Prop := fun a => a ≠ p ∧ a ≠ x
  have e1 : ↥(fixTwo p x) ≃ {f : Perm (Fin N) // ∀ a, ¬ q a → f a = a} :=
    Equiv.subtypeEquivRight (fun σ => by
      constructor
      · rintro ⟨h1, h2⟩ a ha
        by_cases hap : a = p
        · rw [hap]; exact h1
        · have : a = x := by
            by_contra hax
            exact ha ⟨hap, hax⟩
          rw [this]; exact h2
      · intro h
        exact ⟨h p (fun hq => hq.1 rfl), h x (fun hq => hq.2 rfl)⟩)
  have e2 := (Equiv.Perm.subtypeEquivSubtypePerm q).symm
  rw [Nat.card_congr (e1.trans e2), Nat.card_perm]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (Finset.univ.filter q) = (({p, x} : Finset (Fin N))ᶜ) := by
    ext a; simp [q]
  rw [this, Finset.card_compl, Finset.card_pair hpx, Fintype.card_fin]


theorem padicValNat_factorial_two_pow_succ_eq {m : ℕ} (hm : 1 ≤ m) :
    padicValNat 2 (2 ^ m + 1).factorial = m + padicValNat 2 (2 ^ m - 1).factorial := by
  have hodd : ¬ 2 ∣ 2 ^ m + 1 := by
    have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
    omega
  have hpos : 0 < 2 ^ m := by positivity
  rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _),
    padicValNat.eq_zero_of_not_dvd hodd, zero_add, ← Nat.mul_factorial_pred hpos.ne',
    padicValNat.mul hpos.ne' (Nat.factorial_ne_zero _), padicValNat.prime_pow]

theorem transitive_on_compl {m : ℕ} (hm : 1 ≤ m) (D : Subgroup (Perm (Fin (2 ^ m + 1))))
    (hD : Nat.card D = 2 ^ padicValNat 2 (2 ^ m + 1).factorial) (p : Fin (2 ^ m + 1))
    (hpD : ∀ d ∈ D, d p = p) {x y : Fin (2 ^ m + 1)} (hx : x ≠ p) (hy : y ≠ p) :
    ∃ d ∈ D, d x = y := by
  classical
  have hxp : p ≠ x := hx.symm
  have hn2 : 2 ^ m + 1 - 2 = 2 ^ m - 1 := by omega
  have hstab : Nat.card (MulAction.stabilizer ↥D x) ∣ (2 ^ m - 1).factorial := by
    have h1 := card_fixTwo p x hxp
    rw [hn2] at h1
    rw [← h1]
    have hle : (MulAction.stabilizer ↥D x).map D.subtype ≤ fixTwo p x := by
      rintro _ ⟨d, hd, rfl⟩
      exact ⟨hpD d d.2, hd⟩
    rw [← Subgroup.card_map_of_injective D.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hD2 : IsPGroup 2 ↥D := IsPGroup.of_card hD
  obtain ⟨s, hs⟩ := (IsPGroup.iff_card (p := 2)).1 (hD2.to_subgroup (MulAction.stabilizer ↥D x))
  have hsw : s ≤ padicValNat 2 (2 ^ m - 1).factorial := by
    rw [hs] at hstab
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.factorial_ne_zero _)).1
      hstab
    rwa [Nat.factorization_def _ Nat.prime_two] at this
  have hidx := MulAction.index_stabilizer (G := ↥D) (x := x)
  have hmul := Subgroup.index_mul_card (MulAction.stabilizer ↥D x)
  rw [hidx, hs, hD, padicValNat_factorial_two_pow_succ_eq hm, pow_add] at hmul
  have hpos : 0 < 2 ^ s := by positivity
  have horb : 2 ^ m ≤ (MulAction.orbit ↥D x).ncard := by
    have h1 : 2 ^ m * 2 ^ s ≤ (MulAction.orbit ↥D x).ncard * 2 ^ s := by
      rw [hmul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hsw)
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hsub : (MulAction.orbit ↥D x : Set (Fin (2 ^ m + 1))) ⊆ {z | z ≠ p} := by
    rintro _ ⟨d, rfl⟩ hdx
    have : (d : Perm (Fin (2 ^ m + 1))) x = p := hdx
    have h2 : (d : Perm (Fin (2 ^ m + 1))) p = p := hpD d d.2
    exact hx ((d : Perm (Fin (2 ^ m + 1))).injective (this.trans h2.symm))
  have hcompl : ({z | z ≠ p} : Set (Fin (2 ^ m + 1))).ncard = 2 ^ m := by
    have e : ({z | z ≠ p} : Set (Fin (2 ^ m + 1))) =
        ((Finset.univ.erase p : Finset _) : Set _) := by
      ext z; simp
    rw [e, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ,
      Fintype.card_fin]
    rfl
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcompl]; exact horb) (Set.toFinite _)
  have hy' : y ∈ MulAction.orbit ↥D x := by rw [heq]; exact hy
  obtain ⟨d, hd⟩ := hy'
  exact ⟨d, d.2, hd⟩

theorem sup_c3_eq_top {m : ℕ} (hm : 2 ≤ m) (D : Subgroup (Perm (Fin (2 ^ m + 1))))
    (hD : Nat.card D = 2 ^ padicValNat 2 (2 ^ m + 1).factorial) {a b p : Fin (2 ^ m + 1)}
    (hab : a ≠ b) (hap : a ≠ p) (hpD : ∀ d ∈ D, d p = p) (hsw : swap a b ∈ D) :
    D ⊔ Subgroup.closure {c3 a b p} = ⊤ := by
  classical
  set X : Subgroup (Perm (Fin (2 ^ m + 1))) := D ⊔ Subgroup.closure {c3 a b p} with hX
  have hDX : D ≤ X := le_sup_left
  have hcX : c3 a b p ∈ X := Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  have hcp : c3 a b p p = a := c3_apply_right
  have htr : ∀ {x y : Fin (2 ^ m + 1)}, x ≠ p → y ≠ p → ∃ d ∈ D, d x = y := fun hx hy =>
    transitive_on_compl (by omega) D hD p hpD hx hy
  have hreach : ∀ x : Fin (2 ^ m + 1), ∃ g ∈ X, g p = x := by
    intro x
    by_cases hxp : x = p
    · exact ⟨1, X.one_mem, by simp [hxp]⟩
    · obtain ⟨d, hd, hdx⟩ := htr hap hxp
      exact ⟨d * c3 a b p, X.mul_mem (hDX hd) hcX, by rw [Perm.mul_apply, hcp, hdx]⟩
  have : MulAction.IsPretransitive ↥X (Fin (2 ^ m + 1)) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨gx, hgx, hx⟩ := hreach x
    obtain ⟨gy, hgy, hy⟩ := hreach y
    refine ⟨⟨gy * gx⁻¹, X.mul_mem hgy (X.inv_mem hgx)⟩, ?_⟩
    show (gy * gx⁻¹) x = y
    rw [Perm.mul_apply, ← hx]
    simpa using hy
  have : Nontrivial (Fin (2 ^ m + 1)) := by
    refine ⟨⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩⟩
    simp [Fin.ext_iff]
  have hcoatom : IsCoatom (MulAction.stabilizer ↥X p) := by
    refine ⟨?_, fun B hB => ?_⟩
    · intro htop
      have : (⟨c3 a b p, hcX⟩ : ↥X) ∈ MulAction.stabilizer ↥X p := by rw [htop]; trivial
      rw [MulAction.mem_stabilizer_iff] at this
      exact hap (by
        have h2 : c3 a b p p = p := this
        rw [hcp] at h2
        exact h2)
    · obtain ⟨b₀, hb₀B, hb₀S⟩ := IsConcreteLE.exists_of_lt hB
      have hb₀p : (b₀ : Perm (Fin (2 ^ m + 1))) p ≠ p := by
        intro h
        exact hb₀S (by rw [MulAction.mem_stabilizer_iff]; exact h)
      have hDstab : ∀ d (hd : d ∈ D), (⟨d, hDX hd⟩ : ↥X) ∈ B := by
        intro d hd
        refine hB.le ?_
        rw [MulAction.mem_stabilizer_iff]
        exact hpD d hd
      have hmove : ∀ x : Fin (2 ^ m + 1), ∃ b ∈ B, (b : Perm (Fin (2 ^ m + 1))) p = x := by
        intro x
        by_cases hxp : x = p
        · exact ⟨1, B.one_mem, by simp [hxp]⟩
        · obtain ⟨d, hd, hdq⟩ := htr hb₀p hxp
          exact ⟨⟨d, hDX hd⟩ * b₀, B.mul_mem (hDstab d hd) hb₀B, by
            show (d * (b₀ : Perm (Fin (2 ^ m + 1)))) p = x
            rw [Perm.mul_apply, hdq]⟩
      rw [eq_top_iff]
      intro y _
      obtain ⟨b', hb', hbp'⟩ := hmove ((y : Perm (Fin (2 ^ m + 1))) p)
      have hs : b'⁻¹ * y ∈ MulAction.stabilizer ↥X p := by
        rw [MulAction.mem_stabilizer_iff, mul_smul]
        have h1 : y • p = b' • p := hbp'.symm
        rw [h1, inv_smul_smul]
      have := B.mul_mem hb' (hB.le hs)
      simpa using this
  have hprim := (MulAction.isCoatom_stabilizer_iff_preprimitive ↥X p).1 hcoatom
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim (swap a b)
    ⟨a, b, hab, rfl⟩ (Subgroup.mem_sup_left hsw)


end CFSG.AGLEmbeddingD2.GN

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenU

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

theorem eq_zpow_of_commute_p456_p123 {σ : Perm (Fin 7)} (h1 : Commute σ p456)
    (h2 : Commute σ p123) : ∃ a b : ℤ, σ = p456 ^ a * p123 ^ b := by
  have hrest : ∀ x, x ∉ p456.support → x ∉ p123.support → σ x = x := by
    intro x hx1 hx2
    have h0 : ∀ y : Fin 7, y ∉ p456.support → y ∉ p123.support → y = 0 := by decide
    obtain ⟨hs1, -⟩ := (p456_isThreeCycle.isCycle.commute_iff).mp h1
    obtain ⟨hs2, -⟩ := (p123_isThreeCycle.isCycle.commute_iff).mp h2
    have a1 : σ x ∉ p456.support := fun h => hx1 ((hs1 x).mp h)
    have a2 : σ x ∉ p123.support := fun h => hx2 ((hs2 x).mp h)
    exact (h0 _ a1 a2).trans (h0 x hx1 hx2).symm
  exact eq_zpow_mul_zpow_of_commute p456_isThreeCycle p123_isThreeCycle disjoint_p456_p123 hrest
    h1 h2

theorem eq_one_of_commute_kOf : ∀ (π : Perm (Fin 4)) (i : Fin 4), i ≠ 0 →
    π * kOf i = kOf i * π → π ^ 3 = 1 → π = 1 := by
  decide

theorem pow_three_of_odd {π : Perm (Fin 4)} {m : ℕ} (hm : Odd m) (h : π ^ m = 1) : π ^ 3 = 1 := by
  have h1 : orderOf π ∣ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf π ∣ 24 := by
    have := orderOf_dvd_card (G := Perm (Fin 4)) (x := π)
    rwa [Fintype.card_perm, Fintype.card_fin, show Nat.factorial 4 = 24 by decide] at this
  have hodd : Odd (orderOf π) := hm.of_dvd_nat h1
  have key : ∀ d < 25, d ∣ 24 → d % 2 = 1 → d ∣ 3 := by decide
  exact orderOf_dvd_iff_pow_eq_one.mp
    (key _ (by have := Nat.le_of_dvd (by norm_num) h2; omega) h2 (Nat.odd_iff.mp hodd))

namespace Seven

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 7)} {ψB : B ≃* alternatingGroup (Fin 7)}

@[expose] def InOmega (ψA : A ≃* alternatingGroup (Fin 7)) (ψB : B ≃* alternatingGroup (Fin 7))
    (g : G) : Prop :=
  ∃ k₀ ∈ centralizer (A : Set G) ⊓ centralizer (B : Set G), ∃ i j : ℤ,
    g = k₀ * w ψA ^ i * v ψB ^ j

theorem inOmega_one : InOmega ψA ψB (1 : G) :=
  ⟨1, one_mem _, 0, 0, by simp⟩

theorem w_comm_v (hco : AltCoords 7 A B ψA ψB) : Commute (w ψA) (v ψB) :=
  ((mem_centralizer_iff.mp (v_mem_centralizer_A hco)) _ (w_mem ψA))

theorem inOmega_mul (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    {g g' : G} (hg : InOmega ψA ψB g) (hg' : InOmega ψA ψB g') : InOmega ψA ψB (g * g') := by
  obtain ⟨k₁, hk₁, i, j, rfl⟩ := hg
  obtain ⟨k₂, hk₂, a, b, rfl⟩ := hg'
  have hwN := hN (mem_sup_left (le_normalizer (w_mem ψA)))
  have hvN := hN (mem_sup_right (le_normalizer (v_mem ψB)))
  set c := w ψA ^ i * v ψB ^ j with hc
  have hcN : c ∈ normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) :
      Subgroup G) : Set G) := mul_mem (zpow_mem hwN i) (zpow_mem hvN j)
  refine ⟨k₁ * (c * k₂ * c⁻¹), mul_mem hk₁ ((mem_normalizer_iff.mp hcN k₂).mp hk₂), i + a, j + b,
    ?_⟩
  have hvw : v ψB ^ j * w ψA ^ a = w ψA ^ a * v ψB ^ j :=
    ((w_comm_v hco).zpow_zpow a j).eq.symm
  rw [zpow_add, zpow_add]
  calc k₁ * w ψA ^ i * v ψB ^ j * (k₂ * w ψA ^ a * v ψB ^ b)
      = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * (v ψB ^ j * w ψA ^ a) * v ψB ^ b) := by
        rw [hc]; group
    _ = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * w ψA ^ a * (v ψB ^ j * v ψB ^ b)) := by
        rw [hvw]; group
    _ = k₁ * (c * k₂ * c⁻¹) * (w ψA ^ i * w ψA ^ a) * (v ψB ^ j * v ψB ^ b) := by group

theorem u_pow_three : u ψA ^ 3 = 1 := by
  have h : a456 ^ 3 = 1 := Subtype.ext (by decide)
  show ((ψA.symm a456 : A) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]

theorem v_pow_three : v ψB ^ 3 = 1 := by
  have h : a123 ^ 3 = 1 := Subtype.ext (by decide)
  show ((ψB.symm a123 : B) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]

theorem u_comm_of_mem_T {t : G} (ht : t ∈ T ψA) : u ψA * t = t * u ψA := by
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := ht
  have hc : a456 * k = k * a456 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rcases rootV7_cases hk with h | h | h | h <;> rw [h] <;> decide
  show ((ψA.symm a456 : A) : G) * (ψA.symm k : A) = (ψA.symm k : A) * (ψA.symm a456 : A)
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]

theorem exists_kOf_of_mem_T {t : G} (ht : t ∈ T ψA) (ht1 : t ≠ 1) :
    ∃ (htA : t ∈ A) (i : Fin 4), i ≠ 0 ∧
      ((ψA ⟨t, htA⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) (kOf i) := by
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := ht
  obtain ⟨k', hk', hkk⟩ := (mem_rootV_iff (by norm_num) k).mp hk
  obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hk'
  refine ⟨(ψA.symm k).2, i, fun hi => ht1 ?_, ?_⟩
  · have hk1 : k = 1 := by
      apply Subtype.ext
      rw [← hkk, hi]
      exact map_one _
    show ((ψA.symm k : A) : G) = 1
    rw [hk1, map_one, Subgroup.coe_one]
  · have : (⟨A.subtype (ψA.symm.toMonoidHom k), (ψA.symm k).2⟩ : A) = ψA.symm k := rfl
    rw [this, MulEquiv.apply_symm_apply, ← hkk]

theorem inOmega_of_mem [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    {s : G} (hs : s ∈ VF ψA) (hs1 : s ≠ 1) {h : G} (hH : h ∈ H7 ψA ψB)
    (hhs : h ∈ centralizer ({s} : Set G)) (hodd : Odd (orderOf h)) : InOmega ψA ψB h := by
  have hC5B := hco.2.2.2.2.2.2.2.2
  obtain ⟨t, htT, rfl⟩ := hs
  set xx := x ψA with hxx
  have hxs : xx * ((MulAut.conj xx⁻¹).toMonoidHom t) * xx⁻¹ = t := by
    show xx * (xx⁻¹ * t * xx⁻¹⁻¹) * xx⁻¹ = t
    group
  have htC : t ∈ centralizer (B : Set G) := hco.1.le htT
  have ht2 : t * t = 1 := mul_self_of_mem_T htT
  have ht1 : t ≠ 1 := fun h' => hs1 (by rw [h', map_one])
  set h' := xx * h * xx⁻¹ with hh'
  have key : ∀ a b : G, a * b = b * a →
      (xx * a * xx⁻¹) * (xx * b * xx⁻¹) = (xx * b * xx⁻¹) * (xx * a * xx⁻¹) := fun a b hab => by
    calc (xx * a * xx⁻¹) * (xx * b * xx⁻¹) = xx * (a * b) * xx⁻¹ := by group
      _ = xx * (b * a) * xx⁻¹ := by rw [hab]
      _ = (xx * b * xx⁻¹) * (xx * a * xx⁻¹) := by group
  have h't : h' * t = t * h' := by
    have := key h _ (mem_centralizer_singleton_iff.mp hhs)
    rwa [hxs] at this
  have h'u : h' * u ψA = u ψA * h' := by
    have := key h (w ψA) (mem_centralizer_singleton_iff.mp (mem_inf.mp hH).1)
    rwa [x_mul_w] at this
  have hxv : xx * v ψB * xx⁻¹ = v ψB := by
    rw [(mem_centralizer_iff.mp (v_mem_centralizer_A hco)) _ (x_mem ψA), mul_inv_cancel_right]
  have h'v : h' * v ψB = v ψB * h' := by
    have := key h (v ψB) (mem_centralizer_singleton_iff.mp (mem_inf.mp hH).2)
    rwa [hxv] at this
  have h'N : h' ∈ normalizer (B : Set G) :=
    ht1B t htC ht2 ht1 (mem_centralizer_singleton_iff.mpr h't)
  have huN := u_normalizes hco
  have hvN : v ψB ∈ normalizer (B : Set G) := le_normalizer (v_mem ψB)
  set σ := actPerm ψB (Or.inr le_rfl) ⟨h', h'N⟩ with hσdef
  have hcomm : ∀ {z : G} (hz : z ∈ normalizer (B : Set G)), h' * z = z * h' →
      Commute σ (actPerm ψB (Or.inr le_rfl) ⟨z, hz⟩) := fun hz hhz => by
    show σ * _ = _ * σ
    rw [hσdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hhz
  have c1 := hcomm huN h'u
  rw [actPerm_u hco] at c1
  have c2 := hcomm hvN h'v
  rw [actPerm_v] at c2
  obtain ⟨a, b, hσ⟩ := eq_zpow_of_commute_p456_p123 c1 c2
  set c := h' * (u ψA ^ a * v ψB ^ b)⁻¹ with hcdef
  have hcN : c ∈ normalizer (B : Set G) :=
    mul_mem h'N (inv_mem (mul_mem (zpow_mem huN a) (zpow_mem hvN b)))
  have hcB : c ∈ centralizer (B : Set G) := by
    apply (actPerm_eq_one_iff ψB (Or.inr le_rfl) ⟨c, hcN⟩).mp
    have : (⟨c, hcN⟩ : normalizer (B : Set G)) =
        ⟨h', h'N⟩ * ((⟨u ψA, huN⟩ : normalizer (B : Set G)) ^ a *
          (⟨v ψB, hvN⟩ : normalizer (B : Set G)) ^ b)⁻¹ := Subtype.ext (by simp [hcdef])
    rw [this, map_mul, map_inv, map_mul, map_zpow, map_zpow, actPerm_u hco, actPerm_v, ← hσ]
    exact mul_inv_cancel _
  have hut : Commute (u ψA) t := u_comm_of_mem_T htT
  have hvt : Commute (v ψB) t :=
    (show Commute t (v ψB) from (mem_centralizer_iff.mp (v_mem_centralizer_A hco)) t
      (T_le ψA htT)).symm
  have hct : Commute c t :=
    (show Commute h' t from h't).mul_left ((hut.zpow_left a).mul_left (hvt.zpow_left b)).inv_left
  have hcz : Commute h' (u ψA ^ a * v ψB ^ b)⁻¹ :=
    (((show Commute h' (u ψA) from h'u).zpow_right a).mul_right
      ((show Commute h' (v ψB) from h'v).zpow_right b)).inv_right
  have huv : Commute (u ψA) (v ψB) :=
    (show Commute (v ψB) (u ψA) from ((mem_centralizer_iff.mp (v_mem_centralizer_A hco)) _
      (u_mem ψA)).symm).symm
  have hz3 : (u ψA ^ a * v ψB ^ b) ^ 3 = 1 := by
    rw [(huv.zpow_zpow a b).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, u_pow_three,
      v_pow_three, one_zpow, one_zpow, one_mul]
  set m := orderOf h * 3 with hm
  have hmodd : Odd m := Nat.odd_mul.mpr ⟨hodd, by decide⟩
  have hcm : c ^ m = 1 := by
    rw [hcdef, hcz.mul_pow, hm, pow_mul, mul_comm, pow_mul, inv_pow, hz3, inv_one, one_pow,
      mul_one, hh', conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel, one_pow]
  obtain ⟨hcNA, π, hπfix, hπact⟩ := hC5B c hcB
  have hactc : actPerm ψA (Or.inr le_rfl) ⟨c, hcNA⟩ = π := actPerm_eq_of _ _ _ _ fun a => by
    obtain ⟨ha, hae⟩ := hπact a
    exact hae
  have hπm : π ^ m = 1 := by
    have : (⟨c, hcNA⟩ : normalizer (A : Set G)) ^ m = 1 := Subtype.ext (by simp [hcm])
    rw [← hactc, ← map_pow, this, map_one]
  obtain ⟨htA, i, hi0, hti⟩ := exists_kOf_of_mem_T htT ht1
  obtain ⟨ha, hae⟩ := hπact ⟨t, htA⟩
  have h2 : (⟨c * t * c⁻¹, ha⟩ : A) = ⟨t, htA⟩ :=
    Subtype.ext (by show c * t * c⁻¹ = t; rw [hct.eq, mul_inv_cancel_right])
  rw [h2, hti] at hae
  obtain ⟨π', rfl⟩ := exists_perm_four_of_fix (by norm_num : 4 ≤ 7) hπfix
  have hcomm' : π' * kOf i = kOf i * π' := by
    apply viaEmbeddingHom_injective (fourEmb (by norm_num : 4 ≤ 7))
    rw [map_mul (viaEmbeddingHom _) π', map_mul (viaEmbeddingHom _) _ π']
    calc _ = viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) π' *
          viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) (kOf i) *
            (viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) π')⁻¹ *
              viaEmbeddingHom (fourEmb (by norm_num : 4 ≤ 7)) π' := by group
      _ = _ := by rw [← hae]
  have h3 : π' ^ 3 = 1 := by
    refine pow_three_of_odd hmodd (viaEmbeddingHom_injective (fourEmb (by norm_num : 4 ≤ 7)) ?_)
    rw [map_pow, hπm, map_one]
  have hπ'1 := eq_one_of_commute_kOf π' i hi0 hcomm' h3
  have hcA : c ∈ centralizer (A : Set G) := by
    apply (actPerm_eq_one_iff ψA (Or.inr le_rfl) ⟨c, hcNA⟩).mp
    rw [hactc, hπ'1, map_one]
  have hxN : xx ∈ normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) :
      Subgroup G) : Set G) := hN (mem_sup_left (le_normalizer (x_mem ψA)))
  have hu' : (MulAut.conj xx⁻¹) (u ψA) = w ψA := by
    rw [MulAut.conj_apply, ← x_mul_w, ← hxx]
    group
  have hv' : (MulAut.conj xx⁻¹) (v ψB) = v ψB := by
    rw [MulAut.conj_apply, inv_inv]
    nth_rw 1 [← hxv]
    group
  have hh : (MulAut.conj xx⁻¹) h' = h := by
    rw [MulAut.conj_apply, hh']
    group
  have hh'c : h' = c * (u ψA ^ a * v ψB ^ b) := by
    rw [hcdef]
    group
  refine ⟨(MulAut.conj xx⁻¹) c, (mem_normalizer_iff.mp (inv_mem hxN) c).mp (mem_inf.mpr
    ⟨hcA, hcB⟩), a, b, ?_⟩
  rw [← hh, hh'c, map_mul (MulAut.conj xx⁻¹) c, map_mul (MulAut.conj xx⁻¹) (u ψA ^ a),
    map_zpow, map_zpow, hu', hv', mul_assoc]

theorem core_le [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (hN : normalizer (A : Set G) ⊔ normalizer (B : Set G) ≤
      normalizer ((centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    {g : G} (hg : g ∈ (pPrimeCore 2 (H7 ψA ψB)).map (H7 ψA ψB).subtype) : InOmega ψA ψB g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := (pPrimeCore 2 (H7 ψA ψB)).map (H7 ψA ψB).subtype with hK
  have hKcard : Nat.card K = Nat.card (pPrimeCore 2 (H7 ψA ψB)) :=
    card_map_of_injective (H7 ψA ψB).subtype_injective
  have hKodd : ¬ 2 ∣ Nat.card K := by
    rw [hKcard]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  have hKH : K ≤ H7 ψA ψB := map_subtype_le _
  have hHN : H7 ψA ψB ≤ normalizer (K : Set G) := by
    intro s hs
    have := pPrimeCore_normal (p := 2) (G := H7 ψA ψB)
    apply le_normalizer_map (H7 ψA ψB).subtype
    exact ⟨⟨s, hs⟩, le_normalizer_of_normal (K := ⊤) (mem_top _), rfl⟩
  have hgen := RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 2
    Nat.prime_two (VF ψA) K (fun s => Subtype.ext (by simpa [sq] using mul_self_of_mem_VF s.2))
    (by rw [card_VF]; norm_num) hKodd ((VF_le_H7 hco).trans hHN)
  rw [hgen] at hg
  refine Subgroup.iSup_induction (C := InOmega ψA ψB) _ hg (fun s y hy => ?_) inOmega_one
    (fun y z hy hz => inOmega_mul hco hN hy hz)
  refine Subgroup.iSup_induction (C := InOmega ψA ψB) _ hy (fun hs1 z hz => ?_) inOmega_one
    (fun y z hy hz => inOmega_mul hco hN hy hz)
  obtain ⟨hzK, hzs⟩ := mem_inf.mp hz
  have hodd : Odd (orderOf z) :=
    Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKodd))
      (Subgroup.orderOf_dvd_natCard _ hzK)
  exact inOmega_of_mem hco hN ht1B s.2 (fun h => hs1 (Subtype.ext h)) (hKH hzK) hzs hodd

end Seven

end CFSG.ComponentClassification.RankTwoAlt

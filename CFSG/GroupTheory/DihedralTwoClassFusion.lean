module

public import CFSG.Dihedral.DihedralFusionDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
import CFSG.GroupTheory.DihedralTwoClassFusionSupport

public section

namespace CFSG.GorensteinWalter.TwoClassFusion

open DihedralGroup BenderSuzuki.PFchapter1section1

universe u

theorem fusionDecomposition_sr_parity {X : Type u} [Group X] {S : Subgroup X} {m : ℕ}
    (hm : 2 ≤ m) (e : S ≃* DihedralGroup (2 ^ m)) (i : ZMod (2 ^ m)) {z : X}
    (hz : DihedralFusionDecomposition S (Subgroup.zpowers (e.symm (sr i) : X)) z) :
    IsConj (e.symm (sr i) : X) (e.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X) ∨
      ∃ k : ZMod (2 ^ m), z⁻¹ * (e.symm (sr i) : X) * z = e.symm (sr k) ∧
        (Even k.val ↔ Even i.val) := by
  set x : X := (e.symm (sr i) : X)
  let ι : DihedralGroup (2 ^ m) →* X := S.subtype.comp e.symm.toMonoidHom
  have hι : ∀ a, ι a = (e.symm a : X) := fun _ => rfl
  have hιinj : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hιS : ∀ y (hy : y ∈ S), ι (e ⟨y, hy⟩) = y := fun y hy => by simp [ι]
  induction hz with
  | one => exact Or.inr ⟨i, by simp [x], Iff.rfl⟩
  | @tail g h U _ hUS hcur hstep ih =>
    rcases ih with hxt | ⟨k, hk, hpar⟩
    · exact Or.inl hxt
    have hgh : (g * h)⁻¹ * x * (g * h) = h⁻¹ * ι (sr k) * h := by
      rw [hι, ← hk]
      group
    rcases hstep with ⟨rfl, hhS⟩ | ⟨hU, hhN⟩
    · obtain ⟨k', hk', hpar'⟩ := exists_conj_sr_eq (by omega) (e ⟨h, hhS⟩) k
      refine Or.inr ⟨k', ?_, hpar'.trans hpar⟩
      rw [hgh, ← hι (sr k'), ← hk', map_mul, map_mul, map_inv, hιS]
    · have hw : ι (sr k) ∈ U := hcur (Subgroup.mem_map.mpr ⟨x, Subgroup.mem_zpowers x, by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hι, hk]⟩)
      have hv : h⁻¹ * ι (sr k) * h ∈ U := by
        simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) (ι (sr k))).mp hw
      have hcomm := congrArg Subtype.val
        (mul_comm_of_exponent_two hU.exponent_two (⟨_, hw⟩ : U) ⟨_, hv⟩)
      simp only [Subgroup.coe_mul] at hcomm
      obtain ⟨d, hd⟩ : ∃ d, ι d = h⁻¹ * ι (sr k) * h := ⟨e ⟨_, hUS hv⟩, hιS _ _⟩
      rw [← hd] at hcomm
      have hdcomm : Commute (sr k) d := hιinj (by rw [map_mul, map_mul, hcomm])
      rw [hgh, ← hd]
      rcases eq_of_commute_sr hm hdcomm with rfl | rfl | rfl | rfl
      · exfalso
        have hw1 : ι (sr k) = ι 1 := by
          rw [map_one]
          calc ι (sr k) = h * (h⁻¹ * ι (sr k) * h) * h⁻¹ := by group
            _ = 1 := by rw [← hd, map_one]; group
        exact absurd ((hιinj hw1).trans one_def) (fun h => by cases h)
      · left
        rw [show (e.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X) = (g * h)⁻¹ * x * (g * h) by
          rw [hgh, ← hd]; rfl]
        exact isConj_iff.mpr ⟨(g * h)⁻¹, by group⟩
      · exact Or.inr ⟨k, rfl, hpar⟩
      · exact Or.inr ⟨_, rfl, (even_val_add_half hm k).trans hpar⟩

theorem dihedral_reflection_fusion_through_center {X : Type u} [Group X] [Finite X]
    (D : Sylow 2 X) {m : ℕ} (hm : 2 ≤ m) (e : (D : Subgroup X) ≃* DihedralGroup (2 ^ m))
    (i j : ZMod (2 ^ m)) (hij : Even i.val ↔ ¬ Even j.val)
    (h : IsConj ((e.symm (DihedralGroup.sr i) : X)) ((e.symm (DihedralGroup.sr j) : X))) :
    IsConj ((e.symm (DihedralGroup.sr i) : X))
      ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  set x : X := (e.symm (sr i) : X)
  have hPD : Subgroup.zpowers x ≤ (D : Subgroup X) := Subgroup.zpowers_le.mpr (e.symm (sr i)).2
  have himage : rightConjugate (Subgroup.zpowers x) c⁻¹ ≤ (D : Subgroup X) := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [map_zpow]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hc]
    exact Subgroup.zpow_mem _ (e.symm (sr j)).2 n
  obtain ⟨z, hz, -, hzx⟩ := dihedral_fusion_decomposition D hm e _ hPD c⁻¹ himage
  have hzxy : z⁻¹ * x * z = (e.symm (sr j) : X) := by
    rw [hzx x (Subgroup.mem_zpowers x), inv_inv, hc]
  rcases fusionDecomposition_sr_parity hm e i hz with hxt | ⟨k, hk, hpar⟩
  · exact hxt
  · have hkj : k = j := sr.inj (e.symm.injective (Subtype.val_injective (hk.symm.trans hzxy)))
    subst hkj
    tauto

theorem isConj_center_or_sr_zero_or_sr_one {X : Type u} [Group X] [Finite X]
    (D : Sylow 2 X) {m : ℕ} (hm : 2 ≤ m) (e : (D : Subgroup X) ≃* DihedralGroup (2 ^ m))
    {y : X} (hy : orderOf y = 2) :
    IsConj y (e.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X) ∨
      IsConj y (e.symm (sr 0) : X) ∨ IsConj y (e.symm (sr 1) : X) := by
  let ι : DihedralGroup (2 ^ m) →* X := (D : Subgroup X).subtype.comp e.symm.toMonoidHom
  have hιinj : Function.Injective ι := Subtype.val_injective.comp e.symm.injective
  have hP : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X D Q
  have hyD : g⁻¹ * y * g ∈ (D : Subgroup X) := by
    have hyQ : y ∈ ((g • D : Sylow 2 X) : Subgroup X) := hQ (Subgroup.mem_zpowers y)
    rwa [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at hyQ
  obtain ⟨a, ha⟩ : ∃ a, ι a = g⁻¹ * y * g := ⟨e ⟨_, hyD⟩, by simp [ι]⟩
  have hya : IsConj y (ι a) := ha ▸ isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hao : orderOf a = 2 := by
    rw [← orderOf_injective ι hιinj, ha, ← hy]
    exact (SemiconjBy.orderOf_eq g⁻¹ (by simp [SemiconjBy, mul_assoc])).symm
  rcases eq_r_half_or_sr_of_orderOf_eq_two hm hao with rfl | ⟨k, rfl⟩
  · exact Or.inl hya
  · rcases isConj_sr_zero_or_one k with hk | hk
    · exact Or.inr (Or.inl (hya.trans (ι.map_isConj hk)))
    · exact Or.inr (Or.inr (hya.trans (ι.map_isConj hk)))

theorem dihedral_two_class_fusion_pattern {X : Type u} [Group X] [Finite X]
    (D : Sylow 2 X) {m : ℕ} (hm : 2 ≤ m) (e : (D : Subgroup X) ≃* DihedralGroup (2 ^ m))
    (htwo : ∃ u v : X, orderOf u = 2 ∧ orderOf v = 2 ∧ ¬ IsConj u v ∧
      ∀ x : X, orderOf x = 2 → IsConj x u ∨ IsConj x v) :
    (IsConj ((e.symm (DihedralGroup.sr 0) : X))
        ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X)) ∧
      ¬ IsConj ((e.symm (DihedralGroup.sr 1) : X))
        ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X))) ∨
    (IsConj ((e.symm (DihedralGroup.sr 1) : X))
        ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X)) ∧
      ¬ IsConj ((e.symm (DihedralGroup.sr 0) : X))
        ((e.symm (DihedralGroup.r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X))) := by
  obtain ⟨u, v, hu, hv, huv, hcover⟩ := htwo
  let ι : DihedralGroup (2 ^ m) →* X := (D : Subgroup X).subtype.comp e.symm.toMonoidHom
  have hord : ∀ a, orderOf (e.symm a : X) = orderOf a :=
    orderOf_injective ι (Subtype.val_injective.comp e.symm.injective)
  set t : X := (e.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X)
  have ht2 : orderOf t = 2 := (hord _).trans (orderOf_r_half (by omega))
  have hs2 : ∀ k, orderOf (e.symm (sr k) : X) = 2 := fun k => (hord _).trans (orderOf_sr k)
  have h01 := dihedral_reflection_fusion_through_center D hm e 0 1
    (iff_of_true even_val_zero (not_even_val_one (by omega)))
  by_cases hst : IsConj (e.symm (sr 0) : X) t <;> by_cases hs't : IsConj (e.symm (sr 1) : X) t
  · refine absurd ?_ huv
    have hall : ∀ y : X, orderOf y = 2 → IsConj y t := fun y hy => by
      rcases isConj_center_or_sr_zero_or_sr_one D hm e hy with h | h | h
      exacts [h, h.trans hst, h.trans hs't]
    exact (hall u hu).trans (hall v hv).symm
  · exact Or.inl ⟨hst, hs't⟩
  · exact Or.inr ⟨hs't, hst⟩
  · have hss : ¬ IsConj (e.symm (sr 0) : X) (e.symm (sr 1) : X) := fun h => hst (h01 h)
    exfalso
    rcases hcover t ht2 with h1 | h1 <;> rcases hcover _ (hs2 0) with h2 | h2 <;>
      rcases hcover _ (hs2 1) with h3 | h3
    all_goals first
      | exact hst (h2.trans h1.symm)
      | exact hs't (h3.trans h1.symm)
      | exact hss (h2.trans h3.symm)

theorem exists_normal_index_two_of_normal_index_four {X : Type u} [Group X] [Finite X]
    {N : Subgroup X} (hN : N.Normal) (hindex : N.index = 4) :
    ∃ M : Subgroup X, M.Normal ∧ M.index = 2 := by
  have hcard : Nat.card (X ⧸ N) = 4 := by rw [← Subgroup.index_eq_card, hindex]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X ⧸ N) 2 (by rw [hcard]; norm_num)
  have hJ : (Subgroup.zpowers x).index = 2 := by
    have h := (Subgroup.zpowers x).index_mul_card
    rw [Nat.card_zpowers, hx, hcard] at h
    omega
  exact ⟨(Subgroup.zpowers x).comap (QuotientGroup.mk' N),
    (Subgroup.normal_of_index_eq_two hJ).comap _,
    (Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N)).trans hJ⟩

theorem exists_normal_index_two_of_not_isConj {X : Type u} [Group X] [Finite X]
    (D : Sylow 2 X) {m : ℕ} (hm : 1 ≤ m) (e : (D : Subgroup X) ≃* DihedralGroup (2 ^ m))
    {u v : X} (hu : orderOf u = 2) (hv : orderOf v = 2) (huv : ¬ IsConj u v) :
    ∃ N : Subgroup X, N.Normal ∧ N.index = 2 := by
  have hdih : HasDihedralSylowTwo X := fun S => ⟨m, hm, ⟨(Sylow.equiv S D).trans e⟩⟩
  have hinv : ∀ {y : X}, orderOf y = 2 → BenderSuzuki.PFAppendixIII.IsInvolution y :=
    fun {y} hy => ⟨fun h1 => by simp [h1] at hy, by rw [← hy]; exact pow_orderOf_eq_one y⟩
  rcases gw_lemma_2_1 hdih with h1 | h2 | ⟨⟨N, hN, hindex⟩, -⟩
  · obtain ⟨g, hg⟩ := h1.2.1 u v (hinv hu) (hinv hv)
    exact absurd (isConj_iff.mpr ⟨g, hg⟩) huv
  · exact h2.1
  · exact exists_normal_index_two_of_normal_index_four hN hindex

theorem le_of_normal_index_two_of_sr_mem {X : Type u} [Group X] [Finite X]
    (D : Sylow 2 X) {m : ℕ} (e : (D : Subgroup X) ≃* DihedralGroup (2 ^ m)) (k : ZMod (2 ^ m))
    {N₁ N₂ : Subgroup X} (hN₁ : N₁.Normal) (h₁ : N₁.index = 2) (hN₂ : N₂.Normal)
    (h₂ : N₂.index = 2) (hk₁ : (e.symm (sr k) : X) ∈ N₁) (hk₂ : (e.symm (sr k) : X) ∈ N₂) :
    N₁ ≤ N₂ := by
  by_contra hle
  have : NeZero (2 ^ m) := ⟨pow_ne_zero m two_ne_zero⟩
  let ι : DihedralGroup (2 ^ m) →* X := (D : Subgroup X).subtype.comp e.symm.toMonoidHom
  have hrel : N₂.relIndex N₁ = 2 := by
    have hdvd : N₂.relIndex N₁ ∣ 2 := h₂ ▸ Subgroup.relIndex_dvd_index_of_normal N₂ N₁
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h) hle
    · exact h
  have hNindex : (N₁ ⊓ N₂).index = 4 := by
    have h := Subgroup.relIndex_inf_mul_relIndex N₂ N₁ ⊤
    rw [inf_top_eq, Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, hrel, h₁,
      inf_comm] at h
    omega
  let q : X →* X ⧸ (N₁ ⊓ N₂) := QuotientGroup.mk' (N₁ ⊓ N₂)
  have hmap : (D : Subgroup X).map q = ⊤ := by
    apply Subgroup.index_eq_one.mp
    have h1 := Subgroup.index_map_dvd (D : Subgroup X) (QuotientGroup.mk'_surjective (N₁ ⊓ N₂))
    have h2 : ((D : Subgroup X).map q).index ∣ 2 ^ 2 := by
      have := Subgroup.index_dvd_card ((D : Subgroup X).map q)
      rwa [← Subgroup.index_eq_card, hNindex] at this
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    rcases j with _ | j
    · simpa using hj
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans (hj ▸ h1))
        (Sylow.not_dvd_index D)
  have hρ : q (ι (r 1)) ^ 2 = 1 := by
    rw [← map_pow, pow_two, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨Subgroup.mul_self_mem_of_index_two h₁ _, Subgroup.mul_self_mem_of_index_two h₂ _⟩
  have hσ : q (ι (sr k)) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨hk₁, hk₂⟩
  have hrot : ∀ b : ZMod (2 ^ m), q (ι (r b)) ∈ Subgroup.zpowers (q (ι (r 1))) := fun b => by
    rw [show r b = r 1 ^ b.val by rw [r_one_pow, ZMod.natCast_zmod_val], map_pow, map_pow]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hsub : (D : Subgroup X).map q ≤ Subgroup.zpowers (q (ι (r 1))) := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨a, rfl⟩ : ∃ a, ι a = d := ⟨e ⟨d, hd⟩, by simp [ι]⟩
    rcases dihedralGroup_cases a with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact hrot b
    · rw [show sr b = sr k * r (b - k) by rw [sr_mul_r, add_sub_cancel], map_mul, map_mul, hσ,
        one_mul]
      exact hrot (b - k)
  have hcard : Nat.card (X ⧸ (N₁ ⊓ N₂)) ≤ 2 := by
    calc Nat.card (X ⧸ (N₁ ⊓ N₂)) = Nat.card ((D : Subgroup X).map q) := by
          rw [hmap, Subgroup.card_top]
      _ ≤ Nat.card (Subgroup.zpowers (q (ι (r 1)))) := Subgroup.card_le_of_le hsub
      _ = orderOf (q (ι (r 1))) := Nat.card_zpowers _
      _ ≤ 2 := orderOf_le_of_pow_eq_one two_pos hρ
  rw [← Subgroup.index_eq_card, hNindex] at hcard
  omega

theorem dihedral_two_class_unique_index_two {X : Type u} [Group X] [Finite X]
    (D : Sylow 2 X) {m : ℕ} (hm : 2 ≤ m) (e : (D : Subgroup X) ≃* DihedralGroup (2 ^ m))
    (htwo : ∃ u v : X, orderOf u = 2 ∧ orderOf v = 2 ∧ ¬ IsConj u v ∧
      ∀ x : X, orderOf x = 2 → IsConj x u ∨ IsConj x v) :
    ∃! X₀ : Subgroup X, X₀.Normal ∧ X₀.index = 2 := by
  obtain ⟨k, hk⟩ : ∃ k : ZMod (2 ^ m), IsConj (e.symm (sr k) : X)
      (e.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X) := by
    rcases dihedral_two_class_fusion_pattern D hm e htwo with ⟨h, -⟩ | ⟨h, -⟩
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hmem : ∀ {N : Subgroup X}, N.Normal → N.index = 2 → (e.symm (sr k) : X) ∈ N := by
    intro N hN hNi
    obtain ⟨g, hg⟩ := isConj_iff.mp hk
    have hpow : 2 ^ (m - 2) + 2 ^ (m - 2) = 2 ^ (m - 1) := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have hsq : (e.symm (r ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))) : X) =
        (e.symm (r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) : X) *
          (e.symm (r ((2 ^ (m - 2) : ℕ) : ZMod (2 ^ m))) : X) := by
      rw [← Subgroup.coe_mul, ← map_mul, r_mul_r, ← Nat.cast_add, hpow]
    have htN := hN.conj_mem _ (hsq ▸ Subgroup.mul_self_mem_of_index_two hNi _) g⁻¹
    rwa [← hg, show ∀ a : X, g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by intro a; group] at htN
  obtain ⟨u, v, hu, hv, huv, -⟩ := htwo
  obtain ⟨N, hN, hNi⟩ := exists_normal_index_two_of_not_isConj D (by omega) e hu hv huv
  refine ⟨N, ⟨hN, hNi⟩, fun N' hN' => le_antisymm ?_ ?_⟩
  · exact le_of_normal_index_two_of_sr_mem D e k hN'.1 hN'.2 hN hNi (hmem hN'.1 hN'.2)
      (hmem hN hNi)
  · exact le_of_normal_index_two_of_sr_mem D e k hN hNi hN'.1 hN'.2 (hmem hN hNi)
      (hmem hN'.1 hN'.2)

end CFSG.GorensteinWalter.TwoClassFusion

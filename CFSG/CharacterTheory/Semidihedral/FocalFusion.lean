module

public import CFSG.CharacterTheory.Semidihedral.FusionTypes
public import CFSG.CharacterTheory.Semidihedral.FocalTransfer
public import CFSG.CharacterTheory.Semidihedral.StructureTransport

public section

namespace CFSG.Semidihedral.FocalFusion

open CFSG.Open CFSG.Semidihedral

variable {G : Type*} [Group G]

@[expose] def fusionClosure (n : ℕ) (ι : SemidihedralGroup n →* G) :
    Subgroup (SemidihedralGroup n) :=
  Subgroup.closure {d | ∃ x y, IsConj (ι x) (ι y) ∧ d = x⁻¹ * y}

theorem map_fusionClosure (n : ℕ) (ι : SemidihedralGroup n →* G) :
    (fusionClosure n ι).map ι = ι.range.focalSubgroup := by
  rw [fusionClosure, MonoidHom.map_closure,
    Subgroup.focalSubgroup_eq_closure_isConj]
  congr 1
  ext g
  constructor
  · rintro ⟨d, ⟨x, y, hxy, rfl⟩, rfl⟩
    refine ⟨ι x, ⟨x, rfl⟩, ι y, ⟨y, rfl⟩, hxy, ?_⟩
    rw [map_mul, map_inv]
  · rintro ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab, rfl⟩
    exact ⟨a⁻¹ * b, ⟨a, b, hab, rfl⟩, by rw [map_mul, map_inv]⟩

theorem commutator_le_fusionClosure (n : ℕ) (ι : SemidihedralGroup n →* G) :
    commutator (SemidihedralGroup n) ≤ fusionClosure n ι := by
  have h : commutator (SemidihedralGroup n) ≤
      (⊤ : Subgroup (SemidihedralGroup n)).focalSubgroup := by
    change ⁅(⊤ : Subgroup (SemidihedralGroup n)), ⊤⁆ ≤ _
    exact Subgroup.commutator_le_focalSubgroup _
  rw [Subgroup.focalSubgroup_eq_closure_isConj] at h
  apply h.trans
  apply Subgroup.closure_mono
  rintro d ⟨x, _, y, _, hxy, hd⟩
  exact ⟨x, y, ι.map_isConj hxy, hd⟩

theorem r_sq_mem_fusionClosure (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) : r n ^ 2 ∈ fusionClosure n ι :=
  commutator_le_fusionClosure n ι (r_sq_mem_commutator n hn)

theorem conjugate_pair_order (n : ℕ) (ι : SemidihedralGroup n →* G)
    (hι : Function.Injective ι) {x y : SemidihedralGroup n}
    (hxy : IsConj (ι x) (ι y)) : orderOf x = orderOf y := by
  have ho := conjugate_orderOf_eq hxy
  simpa only [orderOf_injective ι hι] using ho

theorem rotation_exterior_fusion (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι)
    (i j : ZMod (modulus n))
    (hxy : IsConj (ι (element n (by omega) i 0))
      (ι (element n (by omega) j 1))) :
    (j.val % 2 = 0 → IsConj (ι (s n)) (ι (z n))) ∧
    (j.val % 2 = 1 → IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))) := by
  have ho := conjugate_pair_order n ι hι hxy
  constructor
  · intro hj
    have hi : orderOf (element n (by omega) i 0) = 2 :=
      ho.trans ((outside_involution_iff n (by omega) j).mpr hj)
    have hx : element n (by omega) i 0 = z n := by
      rw [(rotation_involution_iff n (by omega) i).mp hi, ← z_eq_element n (by omega)]
    have hs := ι.map_isConj (even_exterior_conjugate n hn j hj)
    exact hs.trans (by simpa only [hx] using hxy.symm)
  · intro hj
    have hi : orderOf (element n (by omega) i 0) = 4 :=
      ho.trans ((outside_order_four_iff n (by omega) j).mpr hj)
    exact (ι.map_isConj (odd_exterior_conjugate n hn j hj)).trans
      (hxy.symm.trans (ι.map_isConj (rotation_four_conjugate_quarter n hn i hi)))

theorem rotation_exterior_difference_mem (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι)
    (H : Subgroup (SemidihedralGroup n)) (hr : r n ^ 2 ∈ H)
    (hs : IsConj (ι (s n)) (ι (z n)) → s n ∈ H)
    (hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3)))) → r n * s n ∈ H)
    (i j : ZMod (modulus n))
    (hxy : IsConj (ι (element n (by omega) i 0))
      (ι (element n (by omega) j 1))) :
    (element n (by omega) i 0)⁻¹ * element n (by omega) j 1 ∈ H := by
  have ho := conjugate_pair_order n ι hι hxy
  have hi := rotation_exterior_even n hn i j ho
  have hx := even_rotation_mem n (by omega) H hr i hi
  have hf := rotation_exterior_fusion n hn ι hι i j hxy
  have hy : element n (by omega) j 1 ∈ H := by
    by_cases hj : j.val % 2 = 0
    · have hjs := hs (hf.1 hj)
      have hjr := even_rotation_mem n (by omega) H hr j hj
      have he : element n (by omega) j 1 = element n (by omega) j 0 * s n := by
        rw [s_eq_element n (by omega), element_rotation_mul, add_zero]
      rw [he]
      exact H.mul_mem hjr hjs
    · have hj : j.val % 2 = 1 := by omega
      exact odd_reflection_mem n (by omega) H hr (hq (hf.2 hj)) j hj
  exact H.mul_mem (H.inv_mem hx) hy

theorem conjugate_difference_mem (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι)
    (H : Subgroup (SemidihedralGroup n)) (hr : r n ^ 2 ∈ H)
    (hs : IsConj (ι (s n)) (ι (z n)) → s n ∈ H)
    (hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3)))) → r n * s n ∈ H)
    (x y : SemidihedralGroup n) (hxy : IsConj (ι x) (ι y)) : x⁻¹ * y ∈ H := by
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective x
  obtain ⟨⟨j, d⟩, rfl⟩ := (coordinateEquiv n (by omega)).symm.surjective y
  change IsConj (ι (element n (by omega) i e)) (ι (element n (by omega) j d)) at hxy
  change (element n (by omega) i e)⁻¹ * element n (by omega) j d ∈ H
  have hR : Subgroup.zpowers (r n ^ 2) ≤ H := Subgroup.zpowers_le.mpr hr
  rcases exponent_cases e with rfl | rfl <;> rcases exponent_cases d with rfl | rfl
  · exact hR (same_parity_difference_mem n (by omega) i j 0
      (rotation_order_parity n hn i j (conjugate_pair_order n ι hι hxy)))
  · exact rotation_exterior_difference_mem n hn ι hι H hr hs hq i j hxy
  · have h := H.inv_mem
      (rotation_exterior_difference_mem n hn ι hι H hr hs hq j i hxy.symm)
    simpa only [mul_inv_rev, inv_inv] using h
  · exact hR (same_parity_difference_mem n (by omega) i j 1
      (outside_order_parity n (by omega) i j (conjugate_pair_order n ι hι hxy)))

theorem fusionClosure_le (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι)
    (H : Subgroup (SemidihedralGroup n)) (hr : r n ^ 2 ∈ H)
    (hs : IsConj (ι (s n)) (ι (z n)) → s n ∈ H)
    (hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3)))) → r n * s n ∈ H) :
    fusionClosure n ι ≤ H := by
  rw [fusionClosure, Subgroup.closure_le]
  rintro d ⟨x, y, hxy, rfl⟩
  exact conjugate_difference_mem n hn ι hι H hr hs hq x y hxy

theorem even_power_mem (n : ℕ) (H : Subgroup (SemidihedralGroup n))
    (hr : r n ^ 2 ∈ H) (k : ℕ) (hk : Even k) : r n ^ k ∈ H := by
  obtain ⟨a, ha⟩ := hk
  have he : k = 2 * a := by omega
  rw [he, pow_mul]
  exact H.pow_mem hr _

theorem s_mem_fusionClosure (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hs : IsConj (ι (s n)) (ι (z n))) :
    s n ∈ fusionClosure n ι := by
  have hz : z n ∈ fusionClosure n ι :=
    even_power_mem n _ (r_sq_mem_fusionClosure n hn ι) (half n) (half_even (by omega))
  have hd : (s n)⁻¹ * z n ∈ fusionClosure n ι :=
    Subgroup.subset_closure ⟨s n, z n, hs, rfl⟩
  have hinv := (fusionClosure n ι).mul_mem hd ((fusionClosure n ι).inv_mem hz)
  have hsInv : (s n)⁻¹ ∈ fusionClosure n ι := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hinv
  simpa only [inv_inv] using (fusionClosure n ι).inv_mem hsInv

theorem rs_mem_fusionClosure (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G)
    (hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))) :
    r n * s n ∈ fusionClosure n ι := by
  have hv : r n ^ (2 ^ (n - 3)) ∈ fusionClosure n ι :=
    even_power_mem n _ (r_sq_mem_fusionClosure n hn ι) _ (quarter_even n hn)
  have hd : (r n * s n)⁻¹ * r n ^ (2 ^ (n - 3)) ∈ fusionClosure n ι :=
    Subgroup.subset_closure ⟨r n * s n, r n ^ (2 ^ (n - 3)), hq, rfl⟩
  have hinv := (fusionClosure n ι).mul_mem hd ((fusionClosure n ι).inv_mem hv)
  have hsInv : (r n * s n)⁻¹ ∈ fusionClosure n ι := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hinv
  simpa only [inv_inv] using (fusionClosure n ι).inv_mem hsInv

theorem fusionClosure_eq_derived (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι)
    (hs : ¬ IsConj (ι (s n)) (ι (z n)))
    (hq : ¬ IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))) :
    fusionClosure n ι = Subgroup.zpowers (r n ^ 2) := by
  exact le_antisymm (fusionClosure_le n hn ι hι _ (Subgroup.mem_zpowers _)
    (fun h => (hs h).elim) (fun h => (hq h).elim))
    (Subgroup.zpowers_le.mpr (r_sq_mem_fusionClosure n hn ι))

theorem fusionClosure_eq_dihedral (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι)
    (hs : IsConj (ι (s n)) (ι (z n)))
    (hq : ¬ IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))) :
    fusionClosure n ι = dihedralSubgroup n := by
  apply le_antisymm
  · exact fusionClosure_le n hn ι hι _ (r_sq_mem_dihedralSubgroup n)
      (fun _ => s_mem_dihedralSubgroup n) (fun h => (hq h).elim)
  · rw [dihedralSubgroup, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact r_sq_mem_fusionClosure n hn ι
    · exact s_mem_fusionClosure n hn ι hs

theorem fusionClosure_eq_quaternion (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι)
    (hs : ¬ IsConj (ι (s n)) (ι (z n)))
    (hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))) :
    fusionClosure n ι = quaternionSubgroup n := by
  apply le_antisymm
  · exact fusionClosure_le n hn ι hι _ (r_sq_mem_quaternionSubgroup n)
      (fun h => (hs h).elim) (fun _ => rs_mem_quaternionSubgroup n)
  · rw [quaternionSubgroup, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact r_sq_mem_fusionClosure n hn ι
    · exact rs_mem_fusionClosure n hn ι hq

theorem eq_top_of_r_mem_s_mem (n : ℕ) (hn : 3 ≤ n)
    (H : Subgroup (SemidihedralGroup n)) (hr : r n ∈ H) (hs : s n ∈ H) : H = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨⟨i, e⟩, rfl⟩ := (coordinateEquiv n hn).symm.surjective x
  change element n hn i e ∈ H
  rw [element_eq]
  exact H.mul_mem (H.pow_mem hr _) (H.pow_mem hs _)

theorem fusionClosure_eq_top (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G)
    (hs : IsConj (ι (s n)) (ι (z n)))
    (hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))) :
    fusionClosure n ι = ⊤ := by
  have hsF := s_mem_fusionClosure n hn ι hs
  have hrsF := rs_mem_fusionClosure n hn ι hq
  have hrF : r n ∈ fusionClosure n ι := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using
      (fusionClosure n ι).mul_mem hrsF ((fusionClosure n ι).inv_mem hsF)
  exact eq_top_of_r_mem_s_mem n (by omega) _ hrF hsF

theorem fusionClosure_eq_top_iff (n : ℕ) (hn : 4 ≤ n)
    (ι : SemidihedralGroup n →* G) (hι : Function.Injective ι) :
    fusionClosure n ι = ⊤ ↔ IsConj (ι (s n)) (ι (z n)) ∧
      IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3)))) := by
  constructor
  · intro htop
    by_cases hs : IsConj (ι (s n)) (ι (z n))
    · refine ⟨hs, ?_⟩
      by_contra hq
      have h := fusionClosure_eq_dihedral n hn ι hι hs hq
      have hr : r n ∈ dihedralSubgroup n := by rw [← h, htop]; trivial
      exact r_not_mem_dihedralSubgroup n (by omega) hr
    · by_cases hq : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3))))
      · have h := fusionClosure_eq_quaternion n hn ι hι hs hq
        have hsm : s n ∈ quaternionSubgroup n := by rw [← h, htop]; trivial
        exact (s_not_mem_quaternionSubgroup n (by omega) hsm).elim
      · have h := fusionClosure_eq_derived n hn ι hι hs hq
        have hr : r n ∈ Subgroup.zpowers (r n ^ 2) := by rw [← h, htop]; trivial
        have hd : Subgroup.zpowers (r n ^ 2) ≤ dihedralSubgroup n :=
          Subgroup.zpowers_le.mpr (r_sq_mem_dihedralSubgroup n)
        exact (r_not_mem_dihedralSubgroup n (by omega) (hd hr)).elim
  · rintro ⟨hs, hq⟩
    exact fusionClosure_eq_top n hn ι hs hq

@[expose] def ambientHom (n : ℕ) (S : Subgroup G)
    (f : SemidihedralGroup n ≃* S) : SemidihedralGroup n →* G :=
  S.subtype.comp f.toMonoidHom

theorem ambientHom_injective (n : ℕ) (S : Subgroup G)
    (f : SemidihedralGroup n ≃* S) : Function.Injective (ambientHom n S f) :=
  Subtype.val_injective.comp f.injective

theorem ambientHom_range (n : ℕ) (S : Subgroup G)
    (f : SemidihedralGroup n ≃* S) : (ambientHom n S f).range = S := by
  rw [ambientHom, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr f.surjective,
    Subgroup.map_top, Subgroup.range_subtype]

theorem map_fusionClosure_to_supplied (n : ℕ) (S : Subgroup G)
    (f : SemidihedralGroup n ≃* S) :
    (fusionClosure n (ambientHom n S f)).map f.toMonoidHom = S.focalSubgroupOf := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.map_map, ← ambientHom, map_fusionClosure,
    ambientHom_range, Subgroup.map_focalSubgroupOf]

theorem supplied_fusionClosure_eq_derived [Finite G] (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    (fusionClosure n (ambientHom n (S : Subgroup G) f)).map f.toMonoidHom =
      (commutator G).subgroupOf S := by
  rw [map_fusionClosure_to_supplied, Subgroup.focalSubgroupOf_def,
    ← Subgroup.commutator_inf_eq_focalSubgroup S, Subgroup.inf_subgroupOf_right]

theorem derived_subgroupOf_eq_top_iff [Finite G] (n : ℕ) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) :
    (commutator G).subgroupOf S = ⊤ ↔
      fusionClosure n (ambientHom n (S : Subgroup G) f) = ⊤ := by
  rw [← supplied_fusionClosure_eq_derived n S f]
  constructor
  · intro h
    have hc := congrArg (Subgroup.comap f.toMonoidHom) h
    rw [Subgroup.comap_map_eq_self_of_injective f.injective, Subgroup.comap_top] at hc
    exact hc
  · intro h
    rw [h, Subgroup.map_top_of_surjective _ f.surjective]

theorem semidihedral_focal_subgroup_four_cases [Finite G] (n : ℕ) (hn : 4 ≤ n)
    (S : Sylow 2 G) (f : SemidihedralGroup n ≃* S) :
    let r := f (CFSG.Semidihedral.r n)
    let s := f (CFSG.Semidihedral.s n)
    let m := 2 ^ (n - 1)
    let z := r ^ (m / 2)
    let v := r ^ (m / 4)
    let R := Subgroup.zpowers (r ^ 2)
    let D := Subgroup.closure {r ^ 2, s}
    let Q := Subgroup.closure {r ^ 2, r * s}
    let a := IsConj (s : G) (z : G)
    let b := IsConj ((r * s : S) : G) (v : G)
    (¬ a → ¬ b → (commutator G).subgroupOf S = R) ∧
    (a → ¬ b → (commutator G).subgroupOf S = D) ∧
    (¬ a → b → (commutator G).subgroupOf S = Q) ∧
    (a → b → (commutator G).subgroupOf S = ⊤) ∧
    ((∀ H : Subgroup G, H.index ≠ 2) ↔ a ∧ b) := by
  dsimp only
  let ι := ambientHom n (S : Subgroup G) f
  have hι : Function.Injective ι := ambientHom_injective n (S : Subgroup G) f
  have hz : ι (z n) = ((f (r n) ^ (modulus n / 2) : S) : G) := by
    change (f (z n) : G) = _
    rw [z, map_pow, modulus_div_two n (by omega)]
  have hv : ι (r n ^ (2 ^ (n - 3))) =
      ((f (r n) ^ (modulus n / 4) : S) : G) := by
    change (f (r n ^ (2 ^ (n - 3))) : G) = _
    rw [map_pow, modulus_div_four n hn]
  have hr : ι (r n * s n) = ((f (r n) * f (s n) : S) : G) := by
    change (f (r n * s n) : G) = _
    rw [map_mul]
  change
    (¬ IsConj (ι (s n)) ((f (r n) ^ (modulus n / 2) : S) : G) →
      ¬ IsConj ((f (r n) * f (s n) : S) : G)
        ((f (r n) ^ (modulus n / 4) : S) : G) →
      (commutator G).subgroupOf S = Subgroup.zpowers (f (r n) ^ 2)) ∧
    (IsConj (ι (s n)) ((f (r n) ^ (modulus n / 2) : S) : G) →
      ¬ IsConj ((f (r n) * f (s n) : S) : G)
        ((f (r n) ^ (modulus n / 4) : S) : G) →
      (commutator G).subgroupOf S = Subgroup.closure {f (r n) ^ 2, f (s n)}) ∧
    (¬ IsConj (ι (s n)) ((f (r n) ^ (modulus n / 2) : S) : G) →
      IsConj ((f (r n) * f (s n) : S) : G)
        ((f (r n) ^ (modulus n / 4) : S) : G) →
      (commutator G).subgroupOf S = Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)}) ∧
    (IsConj (ι (s n)) ((f (r n) ^ (modulus n / 2) : S) : G) →
      IsConj ((f (r n) * f (s n) : S) : G)
        ((f (r n) ^ (modulus n / 4) : S) : G) → (commutator G).subgroupOf S = ⊤) ∧
    ((∀ H : Subgroup G, H.index ≠ 2) ↔
      IsConj (ι (s n)) ((f (r n) ^ (modulus n / 2) : S) : G) ∧
      IsConj ((f (r n) * f (s n) : S) : G)
        ((f (r n) ^ (modulus n / 4) : S) : G))
  rw [← hz, ← hv, ← hr]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hs hq
    rw [← supplied_fusionClosure_eq_derived n S f,
      fusionClosure_eq_derived n hn ι hι hs hq, MonoidHom.map_zpowers, map_pow]
    rfl
  · intro hs hq
    rw [← supplied_fusionClosure_eq_derived n S f,
      fusionClosure_eq_dihedral n hn ι hι hs hq]
    exact map_dihedralSubgroup n f
  · intro hs hq
    rw [← supplied_fusionClosure_eq_derived n S f,
      fusionClosure_eq_quaternion n hn ι hι hs hq]
    exact map_quaternionSubgroup n f
  · intro hs hq
    rw [← supplied_fusionClosure_eq_derived n S f,
      fusionClosure_eq_top n hn ι hs hq, Subgroup.map_top_of_surjective _ f.surjective]
  · rw [FocalTransfer.no_index_two_iff_derived_subgroupOf_eq_top S,
      derived_subgroupOf_eq_top_iff n S f, fusionClosure_eq_top_iff n hn ι hι]

end CFSG.Semidihedral.FocalFusion

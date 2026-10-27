module

public import CFSG.Fischer.Classification.PartII.Twins.Basic

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2G

variable {G : Type} [Group G] {D : Set G}

theorem ncard_muSet_eq (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {a b a' b' : G} (ha : a ∈ D) (hb : b ∈ LocalClass D a)
    (ha' : a' ∈ D) (hb' : b' ∈ LocalClass D a') :
    (muSet D a' b').ncard = (muSet D a b).ncard := by
  obtain ⟨g, rfl, rfl⟩ := Pair.exists_conj_pair_of_commute hP hZ hS ha hb.1 ha' hb'.1
    hb.2.1.symm hb.2.2.symm hb'.2.1.symm hb'.2.2.symm
  rw [← Pair.image_conj_muSet hP, Set.ncard_image_of_injective _ (conj_injective g)]

theorem isTwin_localClass (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d a b : G} (hd : d ∈ D)
    (h : IsTwin (LocalClass D d) a b) (hab : a ≠ b) : IsTwin (LocalClass D a) d b := by
  have := Pair.finite hP
  obtain ⟨ha, hb, hcomm, hall⟩ := h
  have hda : d ∈ LocalClass D a := ⟨hd, ha.2.1.symm, ha.2.2.symm⟩
  have hba : b ∈ LocalClass D a := ⟨hb.1, hab.symm, hcomm.symm⟩
  have hdb : d ∈ LocalClass D b := ⟨hd, hb.2.1.symm, hb.2.2.symm⟩
  have hsub : muSet D a d \ {b} ⊆ muSet D a b \ {d} := by
    rintro y ⟨⟨hya, hyd⟩, hyb⟩
    exact ⟨⟨hya, hyd.1, hyb, (hall y hyd).1 hya.2.2⟩, hyd.2.1⟩
  have hcard : (muSet D a b \ {d}).ncard ≤ (muSet D a d \ {b}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem (show d ∈ muSet D a b from ⟨hda, hdb⟩),
      Set.ncard_sdiff_singleton_of_mem (show b ∈ muSet D a d from ⟨hba, hb⟩),
      ncard_muSet_eq hP hZ hS ha.1 hda ha.1 hba]
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard
  refine ⟨hda, hba, hb.2.2.symm, fun y hy => ⟨fun hyd => ?_, fun hyb => ?_⟩⟩
  · by_cases hyd' : y = d
    · subst hyd'
      exact hb.2.2.symm
    · exact (hall y ⟨hy.1, hyd', hyd⟩).1 hy.2.2
  · by_cases hyd' : y = d
    · subst hyd'
      rfl
    by_cases hyb' : y = b
    · subst hyb'
      exact hb.2.2
    have hmem : y ∈ muSet D a b \ {d} := ⟨⟨hy, hy.1, hyb', hyb⟩, hyd'⟩
    rw [← heq] at hmem
    exact hmem.1.2.2.2

theorem insert_twinClass_eq (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d f y z : G} (hd : d ∈ D)
    (hy : y ∈ twinClass (LocalClass D d) f) (hz : z ∈ twinClass (LocalClass D d) f)
    (hyz : y ≠ z) :
    insert d (twinClass (LocalClass D d) f) = insert y (twinClass (LocalClass D y) z) := by
  have hdz : IsTwin (LocalClass D y) d z :=
    isTwin_localClass hP hZ hS hd (isTwin_of_mem hy hz) hyz
  ext x
  simp only [Set.mem_insert_iff, mem_twinClass]
  constructor
  · rintro (rfl | hx)
    · exact Or.inr (isTwin_symm hdz)
    · by_cases hxy : x = y
      · exact Or.inl hxy
      · have hdx := isTwin_localClass hP hZ hS hd (isTwin_of_mem hy hx) (Ne.symm hxy)
        exact Or.inr (isTwin_trans (isTwin_symm hdz) hdx)
  · rintro (rfl | hx)
    · exact Or.inr hy
    · by_cases hxd : x = d
      · exact Or.inl hxd
      · have hdx : IsTwin (LocalClass D y) d x := isTwin_trans hdz hx
        have hyx := isTwin_localClass hP hZ hS hy.2.1.1 hdx (Ne.symm hxd)
        exact Or.inr (isTwin_trans hy hyx)

theorem conj_mul_self_eq (hP : Pair G D) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hcd : c * d ≠ d * c) : d * c * d * (d * c)⁻¹ = c := by
  have e1 : d * c * d = c * d * c := Pair.mul_mul_eq hP hd hc fun h => hcd h.symm
  calc d * c * d * (d * c)⁻¹ = d * c * d * (c⁻¹ * d⁻¹) := by rw [mul_inv_rev]
    _ = c * d * (c * c) * d := by
        rw [e1, Pair.inv_eq hP hc, Pair.inv_eq hP hd]; simp only [mul_assoc]
    _ = c := by rw [Pair.mul_self hP hc, mul_one, mul_assoc, Pair.mul_self hP hd, mul_one]

theorem twinFree_muSet (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d c : G} (hd : d ∈ D) (hc : c ∈ D)
    (hcd : c * d ≠ d * c) : TwinFree (LocalClass D d) (muSet D d c) := by
  intro a ha b hb h
  by_contra hab
  have hfix : ∀ x ∈ muSet D d c, d * c * x * (d * c)⁻¹ = x := by
    intro x hx
    have hxd : x * d = d * x := hx.1.2.2
    have hxc : x * c = c * x := hx.2.2.2
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hxc, ← mul_assoc, ← hxd, mul_assoc]
  have hc' : IsTwin (LocalClass D c) a b := by
    have h' := LocalU.isTwin_conj hP (d * c) h
    rwa [conj_mul_self_eq hP hd hc hcd, hfix a ha, hfix b hb] at h'
  have h1 := isTwin_localClass hP hZ hS hd h hab
  have h2 := isTwin_localClass hP hZ hS hc hc' hab
  exact hcd (isTwin_trans h1 (isTwin_symm h2)).2.2.1.symm

end O2G

end CFSG.Fischer.Classification

module

public import CFSG.Mathlib.GroupTheory.Focal
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Semidihedral.FocalTransfer

open Subgroup Function

variable {G : Type*} [Group G]

@[expose] def conjugatePairFocal (H : Subgroup G) : Subgroup H :=
  Subgroup.closure {z : H | ∃ x y : H, IsConj (x : G) (y : G) ∧ z = y * x⁻¹}

theorem isConj_inv {x y : G} (hxy : IsConj x y) : IsConj x⁻¹ y⁻¹ := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  exact isConj_iff.mpr ⟨g, by group⟩

theorem map_conjugatePairFocal (H : Subgroup G) :
    (conjugatePairFocal H).map H.subtype = H.focalSubgroup := by
  rw [conjugatePairFocal, MonoidHom.map_closure, H.focalSubgroup_eq_closure_isConj]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ⟨x, y, hxy, rfl⟩, rfl⟩
    refine ⟨(y : G)⁻¹, H.inv_mem y.property, (x : G)⁻¹, H.inv_mem x.property,
      (isConj_inv hxy).symm, ?_⟩
    simp
  · rintro ⟨x, hx, y, hy, hxy, rfl⟩
    refine ⟨⟨x⁻¹ * y, H.mul_mem (H.inv_mem hx) hy⟩, ?_, rfl⟩
    refine ⟨⟨y⁻¹, H.inv_mem hy⟩, ⟨x⁻¹, H.inv_mem hx⟩,
      (isConj_inv hxy).symm, ?_⟩
    apply Subtype.ext
    simp

theorem conjugatePairFocal_eq_focalSubgroupOf (H : Subgroup G) :
    conjugatePairFocal H = H.focalSubgroupOf := by
  apply Subgroup.map_subtype_inj.mp
  rw [map_conjugatePairFocal, Subgroup.map_focalSubgroupOf]

instance conjugatePairFocal_normal (H : Subgroup G) : (conjugatePairFocal H).Normal := by
  rw [conjugatePairFocal_eq_focalSubgroupOf]
  infer_instance

theorem commutator_le_conjugatePairFocal (H : Subgroup G) :
    commutator H ≤ conjugatePairFocal H := by
  rw [conjugatePairFocal_eq_focalSubgroupOf]
  exact H.commutator_le_focalSubgroupOf

instance conjugatePairFocal_quotient_commutative (H : Subgroup G) :
    IsMulCommutative (H ⧸ conjugatePairFocal H) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (commutator_le_conjugatePairFocal H)

open scoped IsMulCommutative

@[expose] noncomputable def focalTransfer (H : Subgroup G) [H.FiniteIndex] :
    G →* H ⧸ conjugatePairFocal H :=
  MonoidHom.transfer (QuotientGroup.mk' (conjugatePairFocal H))

private theorem transfer_eq_pow_of_eq_focal (H : Subgroup G) [H.FiniteIndex]
    (F : Subgroup H) [F.Normal] [IsMulCommutative (H ⧸ F)]
    (hF : F = H.focalSubgroupOf) (s : H) :
    (QuotientGroup.mk' F).transfer (s : G) = (QuotientGroup.mk' F s) ^ H.index := by
  subst F
  exact H.transferFocal_eq_pow s

theorem focalTransfer_eq_pow (H : Subgroup G) [H.FiniteIndex] (s : H) :
    focalTransfer H s = (QuotientGroup.mk' (conjugatePairFocal H) s) ^ H.index :=
  transfer_eq_pow_of_eq_focal H (conjugatePairFocal H)
    (conjugatePairFocal_eq_focalSubgroupOf H) s

section Sylow

variable [Finite G] {p : ℕ} [Fact (Nat.Prime p)] (S : Sylow p G)

theorem conjugatePairFocal_eq_derived_subgroupOf :
    conjugatePairFocal (S : Subgroup G) = (commutator G).subgroupOf S := by
  rw [conjugatePairFocal_eq_focalSubgroupOf, Subgroup.focalSubgroupOf_def,
    ← Subgroup.commutator_inf_eq_focalSubgroup S]
  ext s
  simp [Subgroup.mem_subgroupOf]

theorem focalQuotient_pow_index_bijective :
    Bijective fun q : S ⧸ conjugatePairFocal (S : Subgroup G) => q ^ S.index :=
  ((S.isPGroup'.to_quotient (conjugatePairFocal (S : Subgroup G))).powEquiv'
    S.not_dvd_index).bijective

private theorem transfer_properties_of_eq_focal (F : Subgroup S) [F.Normal]
    [IsMulCommutative (S ⧸ F)] (hF : F = (S : Subgroup G).focalSubgroupOf) :
    Surjective (QuotientGroup.mk' F).transfer ∧
    ((QuotientGroup.mk' F).transfer.domRestrict S).ker = F ∧
    (QuotientGroup.mk' F).transfer.ker ⊓ S = F.map (S : Subgroup G).subtype := by
  subst F
  exact ⟨Subgroup.transferFocal_surjective S,
    Subgroup.ker_restrict_transferFocal_eq_focalSubgroupOf S,
    by simpa only [Subgroup.map_focalSubgroupOf, Subgroup.transferFocal] using
      Subgroup.ker_transferFocal_inf_eq_focalSubgroup S⟩

theorem focalTransfer_surjective : Surjective (focalTransfer (S : Subgroup G)) :=
  (transfer_properties_of_eq_focal S (conjugatePairFocal (S : Subgroup G))
    (conjugatePairFocal_eq_focalSubgroupOf (S : Subgroup G))).1

theorem ker_restrict_focalTransfer :
    ((focalTransfer (S : Subgroup G)).domRestrict S).ker =
      conjugatePairFocal (S : Subgroup G) :=
  (transfer_properties_of_eq_focal S (conjugatePairFocal (S : Subgroup G))
    (conjugatePairFocal_eq_focalSubgroupOf (S : Subgroup G))).2.1

theorem ker_focalTransfer_inf :
    (focalTransfer (S : Subgroup G)).ker ⊓ S =
      (conjugatePairFocal (S : Subgroup G)).map (S : Subgroup G).subtype :=
  (transfer_properties_of_eq_focal S (conjugatePairFocal (S : Subgroup G))
    (conjugatePairFocal_eq_focalSubgroupOf (S : Subgroup G))).2.2

@[expose] def abelianizationSylow : Sylow p (Abelianization G) :=
  S.mapSurjective (show Surjective (Abelianization.of : G →* Abelianization G) from
    QuotientGroup.mk'_surjective (commutator G))

theorem abelianizationSylow_eq_map :
    (abelianizationSylow S : Subgroup (Abelianization G)) =
      (S : Subgroup G).map Abelianization.of := rfl

@[expose] def abelianizationToSylow : S →* abelianizationSylow S where
  toFun s := ⟨Abelianization.of (s : G), by
    change Abelianization.of (s : G) ∈ (S : Subgroup G).map Abelianization.of
    exact ⟨s, s.property, rfl⟩⟩
  map_one' := Subtype.ext (map_one Abelianization.of)
  map_mul' s t := Subtype.ext (map_mul Abelianization.of (s : G) (t : G))

theorem abelianizationToSylow_surjective : Surjective (abelianizationToSylow S) := by
  rintro ⟨a, ha⟩
  obtain ⟨g, hg, rfl⟩ := ha
  exact ⟨⟨g, hg⟩, rfl⟩

theorem ker_abelianizationToSylow :
    (abelianizationToSylow S).ker = conjugatePairFocal (S : Subgroup G) := by
  rw [conjugatePairFocal_eq_derived_subgroupOf]
  ext s
  change abelianizationToSylow S s = 1 ↔ (s : G) ∈ commutator G
  rw [Subtype.ext_iff]
  change Abelianization.of (s : G) = 1 ↔ (s : G) ∈ commutator G
  rw [← Abelianization.ker_of G]
  rfl

@[expose] noncomputable def focalQuotientEquivAbelianizationSylow :
    S ⧸ conjugatePairFocal (S : Subgroup G) ≃* abelianizationSylow S :=
  (QuotientGroup.quotientMulEquivOfEq (ker_abelianizationToSylow S).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (abelianizationToSylow S)
      (abelianizationToSylow_surjective S))

theorem focalQuotientEquivAbelianizationSylow_mk (s : S) :
    (focalQuotientEquivAbelianizationSylow S
      (QuotientGroup.mk' (conjugatePairFocal (S : Subgroup G)) s) : Abelianization G) =
      Abelianization.of (s : G) := by
  change ((QuotientGroup.quotientKerEquivOfSurjective (abelianizationToSylow S)
    (abelianizationToSylow_surjective S)) (QuotientGroup.mk s) : Abelianization G) = _
  rfl

theorem sylow_focal_subgroup_via_transfer :
    (conjugatePairFocal (S : Subgroup G)).Normal ∧
    commutator S ≤ conjugatePairFocal (S : Subgroup G) ∧
    conjugatePairFocal (S : Subgroup G) = (commutator G).subgroupOf S ∧
    (∀ s : S, focalTransfer (S : Subgroup G) s =
      (QuotientGroup.mk' (conjugatePairFocal (S : Subgroup G)) s) ^ S.index) ∧
    Surjective (focalTransfer (S : Subgroup G)) ∧
    ((focalTransfer (S : Subgroup G)).domRestrict S).ker =
      conjugatePairFocal (S : Subgroup G) ∧
    (focalTransfer (S : Subgroup G)).ker ⊓ S =
      (conjugatePairFocal (S : Subgroup G)).map (S : Subgroup G).subtype ∧
    (abelianizationSylow S : Subgroup (Abelianization G)) =
      (S : Subgroup G).map Abelianization.of ∧
    ∃ e : S ⧸ conjugatePairFocal (S : Subgroup G) ≃* abelianizationSylow S,
      ∀ s : S, (e (QuotientGroup.mk' (conjugatePairFocal (S : Subgroup G)) s) :
        Abelianization G) = Abelianization.of (s : G) := by
  exact ⟨inferInstance, commutator_le_conjugatePairFocal (S : Subgroup G),
    conjugatePairFocal_eq_derived_subgroupOf S,
    (fun s => focalTransfer_eq_pow (S : Subgroup G) s),
    focalTransfer_surjective S, ker_restrict_focalTransfer S, ker_focalTransfer_inf S,
    abelianizationSylow_eq_map S, focalQuotientEquivAbelianizationSylow S,
    focalQuotientEquivAbelianizationSylow_mk S⟩

end Sylow

theorem exists_index_prime_of_nontrivial_abelian_pgroup
    {A : Type*} [Group A] [IsMulCommutative A] [Finite A] [Nontrivial A]
    {p : ℕ} [Fact (Nat.Prime p)] (hA : IsPGroup p A) :
    ∃ M : Subgroup A, M.Normal ∧ M.index = p := by
  obtain ⟨n, hn, hcard⟩ := hA.nontrivial_iff_card.mp inferInstance
  obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
    (Fact.out : Nat.Prime p) hA
    (show p ^ (n - 1) ≤ Nat.card A from hcard ▸
      Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (Nat.sub_le n 1))
  refine ⟨M, inferInstance, ?_⟩
  have hmul := M.card_mul_index
  rw [hM, hcard] at hmul
  have hexp : p ^ n = p ^ (n - 1) * p := by
    calc
      p ^ n = p ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn]
      _ = p ^ (n - 1) * p := pow_succ p (n - 1)
  rw [hexp] at hmul
  exact Nat.mul_left_cancel (pow_pos (Nat.Prime.pos Fact.out) _) hmul

section SylowTwo

variable [Finite G] (S : Sylow 2 G)

theorem exists_index_two_of_focal_ne (hF : (S : Subgroup G).focalSubgroup ≠ S) :
    ∃ H : Subgroup G, H.Normal ∧ H.index = 2 := by
  have hproper : conjugatePairFocal (S : Subgroup G) ≠ ⊤ := by
    intro htop
    apply hF
    rw [← map_conjugatePairFocal (S : Subgroup G), htop, Subgroup.map_top,
      Subgroup.range_subtype]
  have : Nontrivial (S ⧸ conjugatePairFocal (S : Subgroup G)) :=
    QuotientGroup.nontrivial_iff.mpr hproper
  obtain ⟨M, hnormal, hindex⟩ := exists_index_prime_of_nontrivial_abelian_pgroup
    (S.isPGroup'.to_quotient (conjugatePairFocal (S : Subgroup G)))
  let : M.Normal := hnormal
  refine ⟨M.comap (focalTransfer (S : Subgroup G)), inferInstance, ?_⟩
  exact (M.index_comap_of_surjective (focalTransfer_surjective S)).trans hindex

theorem quotient_index_two_restrict_surjective (H : Subgroup G) (hH : H.index = 2)
    [H.Normal] : Surjective ((QuotientGroup.mk' H).domRestrict S) := by
  have hcard : Nat.card (G ⧸ H) = 2 := hH
  have hquotient : IsPGroup 2 (G ⧸ H) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  let Q : Sylow 2 (G ⧸ H) := S.mapSurjective (QuotientGroup.mk'_surjective H)
  have htop : (Q : Subgroup (G ⧸ H)) = ⊤ :=
    (Q.is_maximal' (hquotient.to_subgroup ⊤) le_top).symm
  apply MonoidHom.range_eq_top.mp
  exact (MonoidHom.domRestrict_range (S : Subgroup G) (QuotientGroup.mk' H)).trans htop

theorem focal_ne_of_index_two (H : Subgroup G) (hH : H.index = 2) :
    (S : Subgroup G).focalSubgroup ≠ S := by
  let : H.Normal := Subgroup.normal_of_index_eq_two hH
  have hcard : Nat.card (G ⧸ H) = 2 := hH
  let : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
  have hderived : commutator G ≤ H := by
    have h := Abelianization.commutator_subset_ker (QuotientGroup.mk' H)
    rwa [QuotientGroup.ker_mk'] at h
  intro hF
  have hSH : (S : Subgroup G) ≤ H := by
    rw [← hF]
    exact (S : Subgroup G).focalSubgroup_le_commutator.trans hderived
  have hsubsingleton : Subsingleton (G ⧸ H) := by
    apply subsingleton_of_forall_eq 1
    intro q
    obtain ⟨s, rfl⟩ := quotient_index_two_restrict_surjective S H hH q
    exact (QuotientGroup.eq_one_iff (N := H) (x := (s : G))).mpr (hSH s.property)
  have htop : H = ⊤ := QuotientGroup.subsingleton_iff.mp hsubsingleton
  have hone : H.index = 1 := Subgroup.index_eq_one.mpr htop
  omega

theorem no_index_two_iff_focal_eq :
    (∀ H : Subgroup G, H.index ≠ 2) ↔ (S : Subgroup G).focalSubgroup = S := by
  constructor
  · intro h
    by_contra hF
    obtain ⟨H, _, hH⟩ := exists_index_two_of_focal_ne S hF
    exact h H hH
  · intro hF H hH
    exact focal_ne_of_index_two S H hH hF

theorem no_index_two_iff_derived_subgroupOf_eq_top :
    (∀ H : Subgroup G, H.index ≠ 2) ↔ (commutator G).subgroupOf S = ⊤ := by
  rw [no_index_two_iff_focal_eq S, Subgroup.subgroupOf_eq_top,
    ← Subgroup.commutator_inf_eq_focalSubgroup S]
  exact ⟨fun h => by rw [← h]; exact inf_le_left,
    fun h => inf_eq_right.mpr h⟩

end SylowTwo

end CFSG.Semidihedral.FocalTransfer

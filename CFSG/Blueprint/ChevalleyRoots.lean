module

public import CFSG.Blueprint.ChevalleyRootsInputs
public import Certificates.Certificate113

public import CFSG.Blueprint.Chevalley

public section

namespace CFSG.Blueprint.Chevalley

namespace RootCertificate

variable {τ : Tag} (C : RootCertificate τ)

variable {C}

end RootCertificate

theorem g2Certificate_check : g2Certificate.check = true := by
  exact Certificates.certificate113.1

theorem f4Certificate_check : f4Certificate.check = true := by
  exact Certificates.certificate113.2.1

theorem d4Certificate_check : d4Certificate.check = true := by
  exact Certificates.certificate113.2.2.1

theorem e6Certificate_check : e6Certificate.check = true := by
  exact Certificates.certificate113.2.2.2.1

theorem e7Certificate_check : e7Certificate.check = true := by
  exact Certificates.certificate113.2.2.2.2.1

theorem e8Certificate_check : e8Certificate.check = true := by
  exact Certificates.certificate113.2.2.2.2.2.1

namespace Tag

theorem rootCertificate_check : ∀ τ : Tag, τ.rootCertificate.check = true
  | G2 => g2Certificate_check
  | F4 => f4Certificate_check
  | D4 => d4Certificate_check
  | E6 => e6Certificate_check
  | E7 => e7Certificate_check
  | E8 => e8Certificate_check

end Tag

theorem mem_rootFinset {τ : Tag} {v : Fin τ.rank → ℤ} : v ∈ rootFinset τ ↔ IsRoot τ v := by
  rw [rootFinset, List.mem_toFinset, List.mem_map,
    RootCertificate.isRoot_iff τ.rootCertificate_check]
  simp only [List.mem_range]

instance (τ : Tag) : Fintype {v : Fin τ.rank → ℤ // IsRoot τ v} :=
  Fintype.subtype (rootFinset τ) fun _ => mem_rootFinset

instance (τ : Tag) : Finite (Label τ) := inferInstance

theorem finite_setOf_isRoot (τ : Tag) : {v | IsRoot τ v}.Finite :=
  (rootFinset τ).finite_toSet.subset fun _ hv => mem_rootFinset.2 hv

namespace RootCertificate

variable {τ : Tag} (C : RootCertificate τ)

end RootCertificate

theorem g2Certificate_checkSigns : g2Certificate.checkSigns = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.1

theorem f4Certificate_checkSigns : f4Certificate.checkSigns = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.1

theorem d4Certificate_checkSigns : d4Certificate.checkSigns = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.1

theorem e6Certificate_checkSigns : e6Certificate.checkSigns = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.1

theorem e7Certificate_checkSigns : e7Certificate.checkSigns = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.1

theorem e8Certificate_checkSigns : e8Certificate.checkSigns = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.2.1

theorem g2Certificate_checkNodup : g2Certificate.checkNodup = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem f4Certificate_checkNodup : f4Certificate.checkNodup = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem d4Certificate_checkNodup : d4Certificate.checkNodup = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e6Certificate_checkNodup : e6Certificate.checkNodup = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e7Certificate_checkNodup : e7Certificate.checkNodup = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem e8Certificate_checkNodup : e8Certificate.checkNodup = true := by
  exact Certificates.certificate113.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem Tag.rootCertificate_checkSigns : ∀ τ : Tag, τ.rootCertificate.checkSigns = true
  | .G2 => g2Certificate_checkSigns
  | .F4 => f4Certificate_checkSigns
  | .D4 => d4Certificate_checkSigns
  | .E6 => e6Certificate_checkSigns
  | .E7 => e7Certificate_checkSigns
  | .E8 => e8Certificate_checkSigns

theorem Tag.rootCertificate_checkNodup : ∀ τ : Tag, τ.rootCertificate.checkNodup = true
  | .G2 => g2Certificate_checkNodup
  | .F4 => f4Certificate_checkNodup
  | .D4 => d4Certificate_checkNodup
  | .E6 => e6Certificate_checkNodup
  | .E7 => e7Certificate_checkNodup
  | .E8 => e8Certificate_checkNodup

namespace Tag

end Tag

theorem card_rootFinset (τ : Tag) : (rootFinset τ).card = τ.rootCount := by
  have h := τ.rootCertificate_checkNodup
  simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
  rw [rootFinset, List.toFinset_card_of_nodup, List.length_map, List.length_range,
    τ.rootCertificate_length]
  exact List.Nodup.of_map (fun v => List.ofFn v) (by rw [List.map_map]; exact h)

theorem card_isRoot (τ : Tag) :
    Fintype.card {v : Fin τ.rank → ℤ // IsRoot τ v} = τ.rootCount := by
  rw [Fintype.card_of_subtype (rootFinset τ) fun _ => mem_rootFinset, card_rootFinset]

theorem IsRoot.nonneg_or_nonpos {τ : Tag} {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    (∀ j, 0 ≤ v j) ∨ ∀ j, v j ≤ 0 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hv
  have h := τ.rootCertificate_checkSigns
  simp only [RootCertificate.checkSigns, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.or_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at h
  exact (h k hk).1

theorem IsRoot.ne_zero {τ : Tag} {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) : v ≠ 0 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hv
  have h := τ.rootCertificate_checkSigns
  simp only [RootCertificate.checkSigns, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at h
  obtain ⟨j, hj⟩ := (h k hk).2
  exact fun h0 => hj (congrFun h0 j)

theorem IsRoot.height_ne_zero {τ : Tag} {v : Fin τ.rank → ℤ} (hv : IsRoot τ v) :
    height v ≠ 0 := by
  intro h0
  apply hv.ne_zero
  rcases hv.nonneg_or_nonpos with hs | hs
  · ext j
    exact le_antisymm ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => hs j).1 h0 j
      (Finset.mem_univ j)).le (hs j)
  · ext j
    have h0' : ∑ i, -v i = 0 := by rw [Finset.sum_neg_distrib, ← height, h0, neg_zero]
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => neg_nonneg.2 (hs i)).1 h0' j
      (Finset.mem_univ j)
    simpa using this

end CFSG.Blueprint.Chevalley

module

public import CFSG.Fischer.Classification.Uniqueness.Triple
public import CFSG.Fischer.Classification.Unitary.Model

public section

namespace CFSG.Fischer.Classification.Unitary

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer CFSG.Fischer

section Congr

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem muSet_congr (φ : X ≃* Y) (hE : φ '' E = F) (d c : X) :
    muSet F (φ d) (φ c) = φ '' muSet E d c := by
  rw [← hE, muSet_map]

theorem image_mem_muFamily (φ : X ≃* Y) (hE : φ '' E = F) {d : X} {O : Set X}
    (hO : O ∈ muFamily E d) : φ '' O ∈ muFamily F (φ d) := by
  obtain ⟨c, hc, hcd, rfl⟩ := hO
  refine ⟨φ c, hE ▸ ⟨c, hc, rfl⟩, fun h => hcd (φ.injective ?_), (muSet_congr φ hE d c)⟩
  rw [map_mul, map_mul, h]

theorem symm_image_eq (φ : X ≃* Y) (hE : φ '' E = F) : φ.symm '' F = E := by
  rw [← hE]
  exact image_symm_image φ E

@[expose] def muFamilyCongr (φ : X ≃* Y) (hE : φ '' E = F) (d : X) :
    muFamily E d ≃ muFamily F (φ d) where
  toFun O := ⟨φ '' O, image_mem_muFamily φ hE O.2⟩
  invFun Q := ⟨φ.symm '' Q, by
    have := image_mem_muFamily φ.symm (symm_image_eq φ hE) Q.2
    rwa [φ.symm_apply_apply] at this⟩
  left_inv O := Subtype.ext (φ.toEquiv.symm_image_image O)
  right_inv Q := Subtype.ext (φ.toEquiv.image_symm_image Q)

theorem image_conj_image (φ : X ≃* Y) (f : X) (O : Set X) :
    (fun s => φ f * s * φ f) '' (φ '' O) = φ '' ((fun s => f * s * f) '' O) := by
  rw [Set.image_image, Set.image_image]
  exact Set.image_congr fun s _ => by rw [map_mul, map_mul]

theorem muGraph_rel_congr (φ : X ≃* Y) (hE : φ '' E = F) {d : X} {O Q : Set X} :
    (∃ f ∈ LocalClass F (φ d), f ∉ φ '' O ∧ (fun s => f * s * f) '' (φ '' O) = φ '' Q) ↔
      ∃ f ∈ LocalClass E d, f ∉ O ∧ (fun s => f * s * f) '' O = Q := by
  rw [localClass_congr φ hE rfl]
  constructor
  · rintro ⟨_, ⟨f, hf, rfl⟩, hfO, hQ⟩
    refine ⟨f, hf, fun h => hfO ⟨f, h, rfl⟩, ?_⟩
    rw [image_conj_image] at hQ
    exact φ.injective.image_injective hQ
  · rintro ⟨f, hf, hfO, hQ⟩
    refine ⟨φ f, ⟨f, hf, rfl⟩, fun h => hfO (φ.injective.mem_set_image.1 h), ?_⟩
    rw [image_conj_image, hQ]

@[expose] def muGraphCongr (φ : X ≃* Y) (hE : φ '' E = F) (d : X) :
    muGraph E d ≃g muGraph F (φ d) where
  toEquiv := muFamilyCongr φ hE d
  map_rel_iff' {O Q} := by
    rw [muGraph, muGraph, SimpleGraph.fromRel_adj, SimpleGraph.fromRel_adj]
    refine and_congr (muFamilyCongr φ hE d).injective.ne_iff (or_congr ?_ ?_)
    · exact muGraph_rel_congr φ hE
    · exact muGraph_rel_congr φ hE

theorem coverRigid_congr (φ : X ≃* Y) (hE : φ '' E = F) {d : X} {r : muFamily E d}
    (h : CoverRigid (muGraph E d) r) :
    CoverRigid (muGraph F (φ d)) (muFamilyCongr φ hE d r) :=
  h.map (muGraphCongr φ hE d)

theorem coverRigid_of_mem (hP : Pair X E) {d d' : X} (hd : d ∈ E) (hd' : d' ∈ E)
    {r : muFamily E d} (h : CoverRigid (muGraph E d) r) :
    ∃ r' : muFamily E d', CoverRigid (muGraph E d') r' := by
  obtain ⟨φ, hφE, hφd⟩ := Pair.exists_mulEquiv hP hd hd'
  subst hφd
  exact ⟨_, coverRigid_congr φ hφE h⟩

end Congr

variable {m : ℕ}

theorem tq_mem_localClass_iff (hm : 3 ≤ m) {v w : Fin m → K} (hv0 : v ≠ 0)
    (hv : herm frob v v = 0) (hw0 : w ≠ 0) (hw : herm frob w w = 0) :
    tq w ∈ LocalClass (DG m) (tq v) ↔ herm frob v w = 0 ∧ ∀ c : K, w ≠ c • v := by
  rw [LocalClass, Set.mem_ofPred_eq, ne_comm, Ne, tq_eq_tq_iff hm hv0 hv hw0 hw,
    tq_commute_iff hm hw0 hw hv0 hv]
  refine ⟨fun ⟨_, h1, h2⟩ => ⟨herm_eq_zero_comm frob frob_frob h2, fun c hc => h1 ⟨c, hc⟩⟩,
    fun ⟨h1, h2⟩ => ⟨tq_mem_DG hw0 hw, fun ⟨c, hc⟩ => h2 c hc,
      herm_eq_zero_comm frob frob_frob h1⟩⟩

theorem localClass_DG (hm : 3 ≤ m) {v : Fin m → K} (hv0 : v ≠ 0) (hv : herm frob v v = 0) :
    LocalClass (DG m) (tq v) = {q | ∃ w : Fin m → K, w ≠ 0 ∧ herm frob w w = 0 ∧
      herm frob v w = 0 ∧ (∀ c : K, w ≠ c • v) ∧ tq w = q} := by
  ext q
  constructor
  · intro hq
    obtain ⟨w, hw0, hw, rfl⟩ := hq.1
    obtain ⟨h1, h2⟩ := (tq_mem_localClass_iff hm hv0 hv hw0 hw).1 hq
    exact ⟨w, hw0, hw, h1, h2, rfl⟩
  · rintro ⟨w, hw0, hw, h1, h2, rfl⟩
    exact (tq_mem_localClass_iff hm hv0 hv hw0 hw).2 ⟨h1, h2⟩

theorem ne_smul_of_herm_ne_zero {v w y : Fin m → K} (hv : herm frob y v = 0)
    (hw : herm frob y w ≠ 0) (c : K) : w ≠ c • v := by
  rintro rfl
  rw [herm_smul_right, hv, mul_zero] at hw
  exact hw rfl

theorem exists_isotropic_perp (hm : 4 ≤ m) {v : Fin m → K} (hv0 : v ≠ 0)
    (hv : herm frob v v = 0) :
    ∃ w : Fin m → K, w ≠ 0 ∧ herm frob w w = 0 ∧ herm frob v w = 0 ∧ ∀ c : K, w ≠ c • v := by
  have hσ := isUnitaryInvolution_frob
  obtain ⟨u, -, hu, hvu⟩ := exists_partner_frob hv0 hv
  obtain ⟨z, hz, hvz, huz⟩ := exists_norm_one_perp_pair hσ (by omega) hv hu hvu
  obtain ⟨z', hz', hzz', hvz', huz'⟩ := exists_norm_one_perp_three hσ hm hz hv hu hvu
    (herm_eq_zero_comm frob frob_frob hvz) (herm_eq_zero_comm frob frob_frob huz)
  have hz'z : herm frob z' z = 0 := herm_eq_zero_comm frob frob_frob hzz'
  have hzw : herm frob z (z + z') = 1 := by rw [herm_add_right, hz, hzz', add_zero]
  refine ⟨z + z', fun h => ?_, ?_, ?_, fun c hc => ?_⟩
  · rw [h, herm_zero_right] at hzw
    exact zero_ne_one hzw
  · rw [herm_add_left, herm_add_right, herm_add_right, hz, hz', hzz', hz'z, add_zero, zero_add,
      add_self_K]
  · rw [herm_add_right, hvz, hvz', add_zero]
  · have h1 : herm frob u (z + z') = 0 := by rw [herm_add_right, huz, huz', add_zero]
    have hc0 : c = 0 := by
      rw [hc, herm_smul_right, herm_conj frob frob_frob, hvu, map_one, mul_one] at h1
      exact h1
    rw [hc0, zero_smul] at hc
    rw [hc, herm_zero_right] at hzw
    exact zero_ne_one hzw

theorem exists_not_commute_localClass_DG (hm : 4 ≤ m) {v : Fin m → K} (hv0 : v ≠ 0)
    (hv : herm frob v v = 0) :
    ∀ f ∈ LocalClass (DG m) (tq v), ∃ g ∈ LocalClass (DG m) (tq v), g * f ≠ f * g := by
  rw [localClass_DG (by omega) hv0 hv]
  rintro _ ⟨w, hw0, hw, hvw, hwv, rfl⟩
  obtain ⟨x, hx, hvx, hwx⟩ := exists_iso_perp isUnitaryInvolution_frob hv0 hv hw hvw hwv
  have hx0 : x ≠ 0 := by rintro rfl; exact hwx (herm_zero_right frob w)
  refine ⟨tq x, ⟨x, hx0, hx, hvx, ne_smul_of_herm_ne_zero (herm_eq_zero_comm frob frob_frob hvw)
    hwx, rfl⟩, fun h => hwx ?_⟩
  exact (tq_commute_iff (by omega) hw0 hw hx0 hx).1 h.symm

theorem localClass_DU_eq_image (v : Fin m → K) :
    LocalClass (DU m) (tqU v) = (u2Equiv m).symm '' LocalClass (DG m) (tq v) :=
  localClass_congr (u2Equiv m).symm (symm_image_eq _ (image_DU m)) (tqU_eq v).symm

theorem tqU_mem_localClass_iff (hm : 3 ≤ m) {v w : Fin m → K} (hv0 : v ≠ 0)
    (hv : herm frob v v = 0) (hw0 : w ≠ 0) (hw : herm frob w w = 0) :
    tqU w ∈ LocalClass (DU m) (tqU v) ↔ herm frob v w = 0 ∧ ∀ c : K, w ≠ c • v := by
  rw [← tq_mem_localClass_iff hm hv0 hv hw0 hw, localClass_DU_eq_image, tqU_eq,
    (u2Equiv m).symm.injective.mem_set_image]

theorem localClass_DU_nonempty (hm : 4 ≤ m) {d : U2 m} (hd : d ∈ DU m) :
    (LocalClass (DU m) d).Nonempty := by
  obtain ⟨v, hv0, hv, rfl⟩ := mem_DU_iff.1 hd
  obtain ⟨w, hw0, hw, hvw, hwv⟩ := exists_isotropic_perp hm hv0 hv
  exact ⟨tqU w, (tqU_mem_localClass_iff (by omega) hv0 hv hw0 hw).2 ⟨hvw, hwv⟩⟩

end CFSG.Fischer.Classification.Unitary

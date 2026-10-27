module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62BlockCMBorel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open scoped commutatorElement
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Involution

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

@[expose] def invol : ProjectiveSpecialUnitaryMatrixGroup J := torus J hJ (-1)

theorem invol_mem_torusGroup : invol J hJ ∈ torusGroup J hJ := torus_mem_torusGroup J hJ (-1)

theorem invol_mem_normalizer :
    invol J hJ ∈
      Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  torusGroup_le_normalizer_rootGroup J hJ (invol_mem_torusGroup J hJ)

theorem invol_mul_self : invol J hJ * invol J hJ = 1 := by
  rw [invol, ← map_mul]
  have : (-1 : Kˣ) * (-1) = 1 := by simp
  rw [this, map_one]

theorem invol_action_val (z : Coord J) :
    ((hermitianTorusAction J (-1) z : Coord J) : K × K) = (-z.1.1, z.1.2) := by
  rw [Prod.ext_iff]
  constructor
  · simp [hermitianTorusAction_fst]
  · simp [hermitianTorusAction_snd]

theorem invol_ne_one (h2 : (2 : K) ≠ 0) : invol J hJ ≠ 1 := by
  intro h
  have h1 : Matrix.ProjGenLinGroup.mk (hermitianTorusGL J (-1)) = 1 := congrArg Subtype.val h
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar] at h1
  obtain ⟨c, hc⟩ := h1
  have h00 := congrFun (congrFun hc 0) 0
  have h11 := congrFun (congrFun hc 1) 1
  simp [hermitianTorusMatrix] at h00 h11
  apply h2
  linear_combination h00 - h11

theorem weyl_mul_invol : weyl J hJ * invol J hJ = invol J hJ * weyl J hJ := by
  have h := weyl_mul_torus_mul_weyl J hJ (-1)
  have h1 : (Units.map J.conj.toMonoidHom (-1 : Kˣ))⁻¹ = -1 := by
    ext
    simp
  rw [h1] at h
  have h2 : weyl J hJ * invol J hJ = invol J hJ * (weyl J hJ)⁻¹ :=
    eq_mul_inv_of_mul_eq h
  rw [h2, weyl_inv]

theorem weyl_mem_centralizer_invol :
    weyl J hJ ∈ Subgroup.centralizer ({invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (weyl_mul_invol J hJ)

theorem root_mem_centralizer_invol_iff (h2 : (2 : K) ≠ 0) (z : Coord J) :
    root J hJ z ∈
        Subgroup.centralizer ({invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      z.1.1 = 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hconj : invol J hJ * root J hJ z * (invol J hJ)⁻¹ =
      root J hJ (hermitianTorusAction J (-1) z) := torus_mul_root_mul_inv J hJ (-1) z
  have hval := invol_action_val J z
  constructor
  · intro h
    have h1 : root J hJ (hermitianTorusAction J (-1) z) = root J hJ z := by
      rw [← hconj, ← h]
      group
    have h3 := root_injective J hJ h1
    have h4 := congrArg (fun w : Coord J => (w : K × K).1) h3
    simp only [hval] at h4
    have h5 : (2 : K) * z.1.1 = 0 := by linear_combination -h4
    exact (mul_eq_zero.mp h5).resolve_left h2
  · intro hz
    have h1 : hermitianTorusAction J (-1) z = z := by
      apply Subtype.ext
      rw [hval]
      ext <;> simp [hz]
    rw [h1] at hconj
    calc root J hJ z * invol J hJ = (invol J hJ * root J hJ z * (invol J hJ)⁻¹) * invol J hJ := by
          rw [hconj]
      _ = invol J hJ * root J hJ z := by group

theorem coord_mul_comm_of_fst_eq_zero (z w : Coord J) (hz : z.1.1 = 0) : z * w = w * z := by
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val, hz]
  ext <;> simp [add_comm]

end Involution

theorem exists_pow_conj_of_involution {G : Type*} [Group G] {p : ℕ} (hp : Odd p) {r ι : G}
    (hii : ι * ι = 1) (hrp : r ^ p = 1) (htt : (r * ι) * (r * ι) = 1) :
    ∃ k : ℕ, r * ι = r ^ k * ι * (r ^ k)⁻¹ := by
  obtain ⟨m, hm⟩ := hp
  have hinv : ι⁻¹ = ι := inv_eq_of_mul_eq_one_right hii
  have hconj : ι * r * ι = r⁻¹ := by
    calc ι * r * ι = r⁻¹ * ((r * ι) * (r * ι)) := by group
      _ = r⁻¹ := by rw [htt, mul_one]
  refine ⟨m + 1, ?_⟩
  have h1 : ι * r ^ (m + 1) * ι = (r ^ (m + 1))⁻¹ := by
    have h := conj_pow (a := ι) (b := r) (i := m + 1)
    rw [hinv] at h
    calc ι * r ^ (m + 1) * ι = (ι * r * ι) ^ (m + 1) := h.symm
      _ = (r ^ (m + 1))⁻¹ := by rw [hconj, inv_pow]
  have h2 : ι * (r ^ (m + 1))⁻¹ * ι = r ^ (m + 1) := by
    have h3 := congrArg (·⁻¹) h1
    simpa [mul_inv_rev, hinv, mul_assoc] using h3
  have h3 : r ^ (m + 1) * r ^ (m + 1) = r := by
    rw [← pow_add, show m + 1 + (m + 1) = p + 1 by omega, pow_succ, hrp, one_mul]
  calc r * ι = (r ^ (m + 1) * r ^ (m + 1)) * ι := by rw [h3]
    _ = r ^ (m + 1) * (ι * (r ^ (m + 1))⁻¹ * ι) * ι := by rw [h2]
    _ = r ^ (m + 1) * ι * (r ^ (m + 1))⁻¹ * (ι * ι) := by group
    _ = r ^ (m + 1) * ι * (r ^ (m + 1))⁻¹ := by rw [hii, mul_one]

section InvolutionFinite

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem normalizer_rootGroup_eq_stabilizer_pinf (hq : 2 < p ^ f) :
    Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ) := by
  have hN := isCoatom_normalizer_rootGroup J hJ hK hfix hq
  have h2 := isMultiplyPretransitive_two J hJ (p ^ f) hK hfix
  have : MulAction.IsPretransitive (ProjectiveSpecialUnitaryMatrixGroup J) (IsoPoint J) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have : Nontrivial (IsoPoint J) := by
    rw [← Finite.one_lt_card_iff_nontrivial, card_isoPoint J hJ (p ^ f) hK hfix]
    have : 0 < (p ^ f) ^ 3 := pow_pos (by omega) _
    omega
  have hprim := MulAction.isPreprimitive_of_is_two_pretransitive h2
  have hco := MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
    (ProjectiveSpecialUnitaryMatrixGroup J) (pinf J hJ)
  exact (hco.le_iff.mp
    (stabilizer_pinf_le_normalizer_rootGroup J hJ (p ^ f) hK hfix)).resolve_left hN.1

theorem exists_mul_of_mem_normalizer (hq : 2 < p ^ f) {t : ProjectiveSpecialUnitaryMatrixGroup J}
    (ht : t ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :
    ∃ r ∈ rootGroup J hJ, ∃ d ∈ torusGroup J hJ, t = r * d := by
  have hmem : t ∈ ((rootGroup J hJ ⊔ torusGroup J hJ :
      Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set _) := by
    rw [rootGroup_sup_torusGroup J hJ (p ^ f) hK hfix,
      ← normalizer_rootGroup_eq_stabilizer_pinf J hJ hK hfix hq]
    exact ht
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (torusGroup_le_normalizer_rootGroup J hJ)] at hmem
  obtain ⟨r, hr, d, hd, rfl⟩ := hmem
  exact ⟨r, hr, d, hd, rfl⟩

theorem eq_one_or_eq_invol (h2 : (2 : K) ≠ 0) {d : ProjectiveSpecialUnitaryMatrixGroup J}
    (hd : d ∈ torusGroup J hJ) (hdd : d * d = 1) : d = 1 ∨ d = invol J hJ := by
  classical
  have hcyc := isCyclic_torusGroup J hJ (p ^ f) hK hfix
  have : Fintype (torusGroup J hJ) := Fintype.ofFinite _
  set x : torusGroup J hJ := ⟨d, hd⟩ with hxdef
  set y : torusGroup J hJ := ⟨invol J hJ, invol_mem_torusGroup J hJ⟩ with hydef
  have hx : x ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hdd)
  have hy : y ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using invol_mul_self J hJ)
  by_contra hne
  push Not at hne
  have hx1 : x ≠ 1 := fun h => hne.1 (congrArg Subtype.val h)
  have hxy : x ≠ y := fun h => hne.2 (congrArg Subtype.val h)
  have hy1 : y ≠ 1 := fun h => invol_ne_one J hJ h2 (congrArg Subtype.val h)
  have hle := IsCyclic.card_pow_eq_one_le (α := torusGroup J hJ) (n := 2) (by norm_num)
  have hsub : ({1, x, y} : Finset (torusGroup J hJ)) ⊆
      Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp
    · simpa using hx
    · simpa using hy
  have h3 : ({1, x, y} : Finset (torusGroup J hJ)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨1, x, y, hx1.symm, hy1.symm, hxy, rfl⟩
  have := Finset.card_le_card hsub
  omega

theorem rootGroup_inf_centralizer_invol (h2 : (2 : K) ≠ 0) :
    rootGroup J hJ ⊓
        Subgroup.centralizer ({invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      rootGroup J hJ ⊓
        Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  apply le_antisymm
  · rintro g ⟨hgR, hgC⟩
    obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 hgR
    have hz : z.1.1 = 0 := (root_mem_centralizer_invol_iff J hJ h2 z).1 hgC
    refine ⟨hgR, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨w', rfl⟩ := (mem_rootGroup J hJ).1 hw
    rw [← map_mul, ← map_mul]
    congr 1
    exact (coord_mul_comm_of_fst_eq_zero J z w' hz).symm
  · intro g hg
    have hg' : g ∈ ⁅rootGroup J hJ, rootGroup J hJ⁆ := by
      rw [commutator_rootGroup J hJ hK hfix]
      exact hg
    have hSk : ⁅rootGroup J hJ, rootGroup J hJ⁆ ≤ (coordFst J).ker.map (root J hJ) := by
      rw [Subgroup.commutator_le]
      rintro _ ⟨z, rfl⟩ _ ⟨w, rfl⟩
      refine ⟨⁅z, w⁆, ?_, map_commutatorElement (root J hJ) z w⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    obtain ⟨z, hzker, rfl⟩ := hSk hg'
    have hz : z.1.1 = 0 := by
      have h1 : (Multiplicative.ofAdd z.1.1 : Multiplicative K) = 1 := hzker
      exact ofAdd_eq_one.mp h1
    exact ⟨root_mem_rootGroup J hJ z, (root_mem_centralizer_invol_iff J hJ h2 z).2 hz⟩

theorem isElemAbelian_inf_centralizer_invol [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : (2 : K) ≠ 0) :
    CFSG.Open.IsElemAbelian p (rootGroup J hJ ⊓
      Subgroup.centralizer ({invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  rw [rootGroup_inf_centralizer_invol J hJ hK hfix h2]
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2.1).symm
  · exact pow_prime_of_mem_rootGroup J hJ hp hp2 hx.1

theorem card_inf_centralizer_invol (h2 : (2 : K) ≠ 0) :
    Nat.card (rootGroup J hJ ⊓
      Subgroup.centralizer ({invol J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :
        Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = p ^ f := by
  rw [rootGroup_inf_centralizer_invol J hJ hK hfix h2, ← commutator_rootGroup J hJ hK hfix]
  exact card_commutator_rootGroup J hJ hK hfix

theorem exists_conj_invol [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 < p ^ f)
    (h2 : (2 : K) ≠ 0) {t : ProjectiveSpecialUnitaryMatrixGroup J}
    (ht : t ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) (ht2 : orderOf t = 2) :
    ∃ u ∈ rootGroup J hJ, t = u * invol J hJ * u⁻¹ := by
  obtain ⟨r, hr, d, hd, rfl⟩ := exists_mul_of_mem_normalizer J hJ hK hfix hq ht
  have htt : (r * d) * (r * d) = 1 := by
    have := pow_orderOf_eq_one (r * d)
    rwa [ht2, pow_two] at this
  have hdN : d ∈ Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    torusGroup_le_normalizer_rootGroup J hJ hd
  have hdd_mem : d * d ∈ rootGroup J hJ := by
    have h1 : d * d = (r * (d * r * d⁻¹))⁻¹ := by
      calc d * d = (r * (d * r * d⁻¹))⁻¹ * ((r * (d * r * d⁻¹)) * (d * d)) := by group
        _ = (r * (d * r * d⁻¹))⁻¹ := by
          have : (r * (d * r * d⁻¹)) * (d * d) = (r * d) * (r * d) := by group
          rw [this, htt, mul_one]
    rw [h1]
    exact inv_mem (mul_mem hr ((Subgroup.mem_normalizer_iff.mp hdN r).mp hr))
  have hdd : d * d = 1 := by
    have hmem : d * d ∈ rootGroup J hJ ⊓ torusGroup J hJ := ⟨hdd_mem, mul_mem hd hd⟩
    rw [(huppert_explicit J hJ (p ^ f) hK hfix).2.2.2.2.1] at hmem
    exact Subgroup.mem_bot.mp hmem
  rcases eq_one_or_eq_invol J hJ hK hfix h2 hd hdd with rfl | rfl
  · exfalso
    have hrp : (r * 1) ^ p = 1 := by
      rw [mul_one]
      exact pow_prime_of_mem_rootGroup J hJ hp hp2 hr
    have hdvd := orderOf_dvd_of_pow_eq_one hrp
    rw [ht2] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm
  · obtain ⟨k, hk⟩ := exists_pow_conj_of_involution
      (hp.eq_two_or_odd'.resolve_left hp2) (invol_mul_self J hJ)
      (pow_prime_of_mem_rootGroup J hJ hp hp2 hr) htt
    exact ⟨r ^ k, pow_mem hr k, hk⟩

theorem exists_involution_model [CharP K p] (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 < p ^ f) :
    ∃ Jv ∈ Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)), orderOf Jv = 2 ∧
      (∀ t ∈ Subgroup.normalizer
          (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)), orderOf t = 2 →
        ∃ u ∈ rootGroup J hJ, t = u * Jv * u⁻¹) ∧
      CFSG.Open.IsElemAbelian p (rootGroup J hJ ⊓
        Subgroup.centralizer ({Jv} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) ∧
      Nat.card (rootGroup J hJ ⊓
        Subgroup.centralizer ({Jv} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :
          Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) = p ^ f ∧
      ¬ Subgroup.centralizer ({Jv} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) ≤
        Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
  refine ⟨invol J hJ, invol_mem_normalizer J hJ, ?_, fun t ht ht2 =>
    exists_conj_invol J hJ hK hfix hp hp2 hq h2 ht ht2,
    isElemAbelian_inf_centralizer_invol J hJ hK hfix hp hp2 h2,
    card_inf_centralizer_invol J hJ hK hfix h2, fun hle => ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact invol_mul_self J hJ) (invol_ne_one J hJ h2)
  · have := hle (weyl_mem_centralizer_invol J hJ)
    rw [normalizer_rootGroup_eq_stabilizer_pinf J hJ hK hfix hq] at this
    exact weyl_not_mem_stabilizer J hJ this

end InvolutionFinite

theorem map_centralizer_singleton {L G : Type*} [Group L] [Group G] (e : L ≃* G) (j : L) :
    (Subgroup.centralizer ({j} : Set L)).map e.toMonoidHom =
      Subgroup.centralizer ({e j} : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := (mem_centralizer_image_iff e {j} x).2 hx
    simpa [Set.image_singleton] using this
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact (mem_centralizer_image_iff e {j} (e.symm y)).1 (by simpa [Set.image_singleton] using hy)

end CFSG.AGLEmbedding.UnitaryModel

namespace CFSG.AGLEmbedding

open CFSG.UnitaryThreeRecognition.Model (rootGroup)

theorem kFactUnitaryInvolution : KFactUnitaryInvolution := by
  intro L _ _ d hd h U
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hf, hq, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
    UnitaryModel.exists_equiv_psu (UnitaryModel.statedClassicalModel hd h)
  have : CharP K 3 := UnitaryModel.charP_of_card Nat.prime_three hK
  obtain ⟨S, hS⟩ := UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := UnitaryModel.exists_equiv_map_eq e U S
  have hU : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hS
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer (rootGroup J hJ : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  obtain ⟨Jv, hJvN, hJv2, hconj, hel, hcard, hnc⟩ :=
    UnitaryModel.exists_involution_model J hJ hK hfix Nat.prime_three (by norm_num) hq
  have hmemN : ∀ x : L, x ∈ Subgroup.normalizer ((U : Subgroup L) : Set L) ↔
      e' x ∈ Subgroup.normalizer (rootGroup J hJ : Set _) := fun x => by
    rw [← hN]
    exact (UnitaryModel.mem_map_iff e' _ x).symm
  have hinf : ((U : Subgroup L) ⊓ Subgroup.centralizer ({e'.symm Jv} : Set L)).map
      e'.toMonoidHom = rootGroup J hJ ⊓ Subgroup.centralizer ({Jv} : Set _) := by
    rw [Subgroup.map_inf _ _ e'.toMonoidHom e'.injective, hU,
      UnitaryModel.map_centralizer_singleton, MulEquiv.apply_symm_apply]
  refine ⟨e'.symm Jv, (hmemN _).2 (by simpa using hJvN), ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hJv2
  · intro t ht ht2
    obtain ⟨u, hu, htu⟩ := hconj (e' t) ((hmemN t).1 ht) (by rw [MulEquiv.orderOf_eq]; exact ht2)
    refine ⟨e'.symm u, ?_, ?_⟩
    · rw [← hU] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      show e'.symm (e' y) ∈ (U : Subgroup L)
      rw [MulEquiv.symm_apply_apply]
      exact hy
    · apply e'.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact htu
  · rw [← UnitaryModel.isElemAbelian_map_iff e', hinf]
    exact hel
  · rw [← Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hinf]
    exact hcard
  · intro hle
    apply hnc
    have := Subgroup.map_mono (f := e'.toMonoidHom) hle
    rw [UnitaryModel.map_centralizer_singleton, MulEquiv.apply_symm_apply, hN] at this
    exact this

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.Assembly.LowTwoRank CFSG.BenderSuzuki.MatrixGroups CFSG.UnitaryThreeRecognition.Model

theorem statedClassicalModel {L : Type} [Group L] {p : ℕ} {d : TauCeti.ValidLieTypeIndex}
    (hd : IsUnitaryIndex p d) (h : Nonempty (L ≃* CatGroup d)) :
    StatedClassicalModel L .PSU 3 p d.1.fieldExponent := by
  obtain ⟨q, rfl, hdq⟩ := hd
  have hfe : d.1.fieldExponent = q.exponent := by rw [hdq]; simp
  rw [hfe]
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.twistedA 2 q := hdq
  obtain ⟨e⟩ := h
  exact CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e

theorem exists_equiv_psu {L : Type} [Group L] {p f : ℕ}
    (h : StatedClassicalModel L .PSU 3 p f) :
    p.Prime ∧ 1 ≤ f ∧ 2 < p ^ f ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (J : HermitianForm 3 K),
        J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧ Nat.card K = (p ^ f) ^ 2 ∧
        Nat.card {x : K // J.conj x = x} = p ^ f ∧
        Nonempty (L ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨⟨hp, hf, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨J, hJ, -, hfix⟩ := exists_standardHermitianForm (K := K) p f hK
  obtain ⟨e'⟩ := nonempty_psu_equiv_statedProj J (p ^ f) hK hfix
  have hq : 2 < p ^ f := by
    have h2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have h3 : p ^ f ≠ 2 := fun h0 => hne (by rw [h0])
    omega
  exact ⟨hp, hf, hq, K, inferInstance, inferInstance, J, hJ, hK, hfix, ⟨e.trans e'.symm⟩⟩

theorem exists_equiv_map_eq {L G : Type*} [Group L] [Finite L] [Group G] {p : ℕ} [Fact p.Prime]
    (e : L ≃* G) (U : Sylow p L) (P : Sylow p G) :
    ∃ e' : L ≃* G, (U : Subgroup L).map e'.toMonoidHom = P := by
  have : Finite G := Finite.of_equiv L e.toEquiv
  set U' := U.mapSurjective (f := (e : L →* G)) e.surjective with hU'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U' P
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h2 : ((g • U' : Sylow p G) : Subgroup G) =
      (U' : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hg, hU', Sylow.coe_mapSurjective, Subgroup.map_map] at h2
  exact h2.symm

theorem charP_of_card {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hF : Nat.card F = (p ^ f) ^ 2) : CharP F p := by
  have := Fintype.ofFinite F
  obtain ⟨r, hch, n, hr, hcard⟩ := FiniteField.card' F
  have hdvd : r ∣ p := by
    have : r ∣ (p ^ f) ^ 2 := by
      rw [← hF, Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self r n.ne_zero
    exact hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow this)
  rwa [(Nat.prime_dvd_prime_iff_eq hr hp).mp hdvd] at hch

section Transport

variable {L G : Type*} [Group L] [Group G]

theorem mem_map_iff (e : L ≃* G) (S : Subgroup L) (x : L) :
    e x ∈ S.map e.toMonoidHom ↔ x ∈ S := by
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem mem_centralizer_image_iff (e : L ≃* G) (S : Set L) (x : L) :
    e x ∈ Subgroup.centralizer (e '' S) ↔ x ∈ Subgroup.centralizer S := by
  simp only [Subgroup.mem_centralizer_iff, Set.forall_mem_image, ← map_mul, e.injective.eq_iff]

theorem mem_centralizer_map_iff (e : L ≃* G) (S : Subgroup L) (x : L) :
    e x ∈ Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup G) : Set G) ↔
      x ∈ Subgroup.centralizer (S : Set L) := by
  rw [Subgroup.coe_map]
  exact mem_centralizer_image_iff e _ x

theorem isElemAbelian_map_iff {p : ℕ} (e : L ≃* G) (E : Subgroup L) :
    CFSG.Open.IsElemAbelian p (E.map e.toMonoidHom) ↔ CFSG.Open.IsElemAbelian p E := by
  unfold CFSG.Open.IsElemAbelian
  rw [← Subgroup.le_centralizer_iff_isMulCommutative,
    ← Subgroup.le_centralizer_iff_isMulCommutative]
  refine and_congr ?_ ?_
  · constructor
    · intro h x hx
      exact (mem_centralizer_map_iff e E x).1 (h ((mem_map_iff e E x).2 hx))
    · rintro h _ ⟨x, hx, rfl⟩
      exact (mem_centralizer_map_iff e E x).2 (h hx)
  · constructor
    · intro h x hx
      have := h (e x) ((mem_map_iff e E x).2 hx)
      rw [← map_pow, ← map_one e] at this
      exact e.injective this
    · rintro h _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_pow, h x hx, map_one]

end Transport

theorem succ_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    refine ⟨k, ?_⟩
    have h : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    omega

theorem prod_toNat_icc (q : ℕ) (hq : 1 ≤ q) :
    ∏ i ∈ Finset.Icc 2 3, (((q : ℕ) : ℤ) ^ i - (-1) ^ i).toNat = (q ^ 2 - 1) * (q ^ 3 + 1) := by
  have h2 : Finset.Icc 2 3 = {2, 3} := by decide
  have h₂ : (((q : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
      push_cast [Nat.cast_sub this]
      ring
    rw [this, Int.toNat_natCast]
  have h₃ : (((q : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [this, Int.toNat_natCast]
  rw [h2, Finset.prod_pair (by norm_num), h₂, h₃]

theorem card_mul_gcd {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (p ^ f) ^ 2) {L : Type} [Group L]
    (e : L ≃* StatedProj (StatedSU 3 (p ^ f) K)) :
    Nat.card L * Nat.gcd 3 (p ^ f + 1) =
      (p ^ f) ^ 3 * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 2 - 1) := by
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp hf hK (by norm_num : 2 ≤ 3)]
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  generalize p ^ f = q at hq
  rw [prod_toNat_icc q hq]
  have hdvd : Nat.gcd 3 (q + 1) ∣ q ^ (3 * (3 - 1) / 2) * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right ((Nat.gcd_dvd_right _ _).trans
      (succ_dvd_sq_sub_one q)) _) _
  rw [Nat.div_mul_cancel hdvd, show 3 * (3 - 1) / 2 = 3 by norm_num]
  ring

theorem pos_pow_of_card {K : Type} [Finite K] {p f : ℕ}
    (hK : Nat.card K = (p ^ f) ^ 2) [Nonempty K] : 0 < p ^ f := by
  refine Nat.pos_of_ne_zero fun h => ?_
  have : Nat.card K = 0 := by rw [hK, h]; rfl
  exact Nat.card_pos.ne' this

theorem not_dvd_mul_of_dvd {p q : ℕ} (hp : p.Prime) (hpq : p ∣ q) (hq : 1 ≤ q) :
    ¬ p ∣ (q ^ 3 + 1) * (q ^ 2 - 1) := by
  intro h
  have h3 : ¬ p ∣ q ^ 3 + 1 := fun h' =>
    hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right (dvd_pow hpq (by norm_num))).mp h'))
  have h2 : ¬ p ∣ q ^ 2 - 1 := by
    intro h'
    have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    have : p ∣ q ^ 2 - 1 + 1 := by
      rw [Nat.sub_add_cancel hq2]
      exact dvd_pow hpq (by norm_num)
    exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h').mp this))
  rcases (Nat.Prime.dvd_mul hp).mp h with h' | h'
  · exact h3 h'
  · exact h2 h'

section Model

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem card_rootGroup_eq : Nat.card (rootGroup J hJ) = p ^ (3 * f) := by
  rw [card_rootGroup J hJ (p ^ f) hK hfix, ← pow_mul, mul_comm]

theorem isPGroup_rootGroup : IsPGroup p (rootGroup J hJ) :=
  IsPGroup.of_card (card_rootGroup_eq J hJ hK hfix)

theorem index_rootGroup_mul :
    (rootGroup J hJ).index * Nat.gcd 3 (p ^ f + 1) = ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 2 - 1) := by
  have hcard := card_psu J hJ (p ^ f) hK hfix
  have hR := card_rootGroup J hJ (p ^ f) hK hfix
  have hmul := (rootGroup J hJ).card_mul_index
  have hdvd : Nat.gcd (p ^ f + 1) 3 ∣ ((p ^ f) ^ 3 + 1) * (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) :=
    Dvd.dvd.mul_left ((Nat.gcd_dvd_left _ _).trans (succ_dvd_sq_sub_one _)) _
  have hP : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) * Nat.gcd (p ^ f + 1) 3 =
      ((p ^ f) ^ 3 + 1) * (p ^ f) ^ 3 * ((p ^ f) ^ 2 - 1) := by
    rw [hcard, Nat.div_mul_cancel hdvd]
  rw [← hmul, hR] at hP
  rw [Nat.gcd_comm 3]
  have hpos : 0 < (p ^ f) ^ 3 := pow_pos (pos_pow_of_card hK) _
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (p ^ f) ^ 3 * ((rootGroup J hJ).index * Nat.gcd (p ^ f + 1) 3)
      = (p ^ f) ^ 3 * (rootGroup J hJ).index * Nat.gcd (p ^ f + 1) 3 := by ring
    _ = _ := by rw [hP]; ring

theorem exists_sylow_eq_rootGroup [Fact p.Prime] (hf : 1 ≤ f) :
    ∃ S : Sylow p (ProjectiveSpecialUnitaryMatrixGroup J), (S : Subgroup _) = rootGroup J hJ := by
  refine ⟨(isPGroup_rootGroup J hJ hK hfix).toSylow ?_, rfl⟩
  intro hdvd
  have hmul := index_rootGroup_mul J hJ hK hfix
  have hpq : p ∣ p ^ f := dvd_pow_self p (by omega)
  exact not_dvd_mul_of_dvd Fact.out hpq (pos_pow_of_card hK) ((hdvd.mul_right _).trans hmul.dvd)

theorem isCoatom_normalizer_rootGroup (hq : 2 < p ^ f) :
    IsCoatom (Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
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
  have hle := stabilizer_pinf_le_normalizer_rootGroup J hJ (p ^ f) hK hfix
  rcases hco.le_iff.mp hle with h | h
  · exfalso
    have hsimple := isSimpleGroup_psu J (p ^ f) hK hfix hq
    have hnorm : (rootGroup J hJ).Normal := Subgroup.normalizer_eq_top_iff.mp h
    rcases hnorm.eq_bot_or_eq_top with hbot | htop
    · have := card_rootGroup J hJ (p ^ f) hK hfix
      rw [hbot, Subgroup.card_bot] at this
      have h1 : 1 < (p ^ f) ^ 3 := one_lt_pow₀ (by omega) (by norm_num)
      omega
    · exact hco.1 (top_le_iff.mp (htop ▸ rootGroup_le_stabilizer J hJ))
  · rwa [h]

end Model

section Coord

variable {K : Type} [Field K] (J : HermitianForm 3 K)

theorem coord_pow_val (z : Coord J) (n : ℕ) :
    ((z ^ n : Coord J) : K × K) =
      ((n : K) * z.1.1, (n : K) * z.1.2 - (n.choose 2 : K) * (z.1.1 * J.conj z.1.1)) := by
  induction n with
  | zero => simp [coord_one_val]
  | succ n ih =>
    rw [pow_succ, coord_mul_val, ih]
    have hch : ((n + 1).choose 2 : K) = n + n.choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
      push_cast
      ring
    ext
    · simp only [Nat.cast_succ]
      ring
    · simp only [Nat.cast_succ, hch]
      ring

theorem coord_pow_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] (z : Coord J) :
    z ^ p = 1 := by
  have h3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have h0 : (p : K) = 0 := CharP.cast_eq_zero K p
  have h1 : (p.choose 2 : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K p]
    exact hp.dvd_choose_self (by norm_num) h3
  apply Subtype.ext
  rw [coord_pow_val, coord_one_val, h0, h1]
  simp

@[expose] def coordFst : Coord J →* Multiplicative K where
  toFun z := Multiplicative.ofAdd z.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def fixedSubgroup : Subgroup (Multiplicative K) where
  carrier := {a | J.conj (Multiplicative.toAdd a) = Multiplicative.toAdd a}
  mul_mem' := by
    intro a b ha hb
    show J.conj (Multiplicative.toAdd a + Multiplicative.toAdd b) = _
    rw [map_add, show J.conj (Multiplicative.toAdd a) = _ from ha,
      show J.conj (Multiplicative.toAdd b) = _ from hb]
    rfl
  one_mem' := by
    show J.conj 0 = 0
    exact map_zero _
  inv_mem' := by
    intro a ha
    show J.conj (-Multiplicative.toAdd a) = _
    rw [map_neg, show J.conj (Multiplicative.toAdd a) = _ from ha]
    rfl

@[expose] def realCoord : Subgroup (Coord J) := (fixedSubgroup J).comap (coordFst J)

theorem coordFst_surjective (h2 : (2 : K) ≠ 0) : Function.Surjective (coordFst J) := by
  intro a
  set x := Multiplicative.toAdd a
  refine ⟨⟨(x, -(x * J.conj x) / 2), ?_⟩, rfl⟩
  dsimp only
  rw [map_div₀, map_neg, map_mul, conj_conj, map_ofNat]
  field_simp
  ring

theorem mul_comm_of_mem_realCoord {z w : Coord J} (hz : z ∈ realCoord J) (hw : w ∈ realCoord J) :
    z * w = w * z := by
  have hz' : J.conj z.1.1 = z.1.1 := hz
  have hw' : J.conj w.1.1 = w.1.1 := hw
  apply Subtype.ext
  rw [coord_mul_val, coord_mul_val, hz', hw']
  ext
  · exact add_comm _ _
  · dsimp only
    ring

variable [Finite K] {p f : ℕ} (hK : Nat.card K = (p ^ f) ^ 2)
  (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem card_realCoord (hcoord : Nat.card (Coord J) = (p ^ f) ^ 3) (h2 : (2 : K) ≠ 0) :
    Nat.card (realCoord J) = (p ^ f) ^ 2 := by
  have hsurj := coordFst_surjective J h2
  have hidx : (realCoord J).index = (fixedSubgroup J).index :=
    Subgroup.index_comap_of_surjective _ hsurj
  have hF : Nat.card (fixedSubgroup J) = p ^ f := by
    rw [← hfix]
    exact Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun a => Iff.rfl)
  have hM : Nat.card (Multiplicative K) = (p ^ f) ^ 2 := by
    rw [← hK]
    exact Nat.card_congr Multiplicative.toAdd
  have h1 := (realCoord J).card_mul_index
  have h2' := (fixedSubgroup J).card_mul_index
  rw [hF, hM] at h2'
  rw [hcoord, hidx] at h1
  have hpos : 0 < p ^ f := pos_pow_of_card hK
  have hi : (fixedSubgroup J).index = p ^ f := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h2', sq]
  rw [hi] at h1
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h1]
  ring

end Coord

section Root

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ}
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem commutator_rootGroup :
    ⁅rootGroup J hJ, rootGroup J hJ⁆ =
      rootGroup J hJ ⊓ Subgroup.centralizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have h := (huppert_explicit J hJ (p ^ f) hK hfix).2.2.2.2.2.2.2.2.1
  rw [← Subgroup.map_subtype_commutator, h]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    intro g hg
    have := Subgroup.mem_center_iff.mp hy ⟨g, hg⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxR, hxc⟩
    refine ⟨⟨x, hxR⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
    exact Subtype.ext (hxc g.1 g.2)

omit [Finite K] hK hfix in
theorem pow_prime_of_mem_rootGroup (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    {u : ProjectiveSpecialUnitaryMatrixGroup J} (hu : u ∈ rootGroup J hJ) : u ^ p = 1 := by
  obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 hu
  rw [← map_pow, coord_pow_prime J hp hp2 z, map_one]

theorem exists_elemAbelian_rootGroup (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p] :
    ∃ E : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J), E ≤ rootGroup J hJ ∧
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ (2 * f) := by
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have hcoord : Nat.card (Coord J) = (p ^ f) ^ 3 := by
    rw [Nat.card_congr (rootCoord J hJ).toEquiv, card_rootGroup J hJ (p ^ f) hK hfix]
  refine ⟨(realCoord J).map (root J hJ), Subgroup.map_le_range _ _,
    ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a, ⟨z, hz, ha⟩⟩ := a
    obtain ⟨b, ⟨w, hw, hb⟩⟩ := b
    apply Subtype.ext
    show a * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm_of_mem_realCoord J hz hw]
  · obtain ⟨z, -, rfl⟩ := hx
    rw [← map_pow, coord_pow_prime J hp hp2 z, map_one]
  · rw [Subgroup.card_map_of_injective (root_injective J hJ), card_realCoord J hK hfix hcoord h2,
      ← pow_mul, mul_comm]

end Root

end CFSG.AGLEmbedding.UnitaryModel

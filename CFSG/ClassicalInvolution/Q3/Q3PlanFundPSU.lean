module

public import CFSG.ClassicalInvolution.Q3.Q3PlanFundPSL
public import CFSG.ClassicalInvolution.Q3.M11Branch
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalPSU

public section

namespace CFSG.ClassicalInvolution.Q3

open Matrix CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.ModelFacts
  CFSG.ComponentClassification Module
open scoped MatrixGroups

section Su

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p] {n : ℕ}

theorem eq_one_of_pow_three_eq_one_of_natCard_nine (hF : Nat.card F = 9) {d : F}
    (hd : d ^ 3 = 1) : d = 1 := by
  have : Fintype F := Fintype.ofFinite F
  have h1 := FiniteField.pow_card d
  rw [Fintype.card_eq_nat_card, hF] at h1
  calc d = d ^ 9 := h1.symm
    _ = (d ^ 3) ^ 3 := by ring
    _ = 1 := by rw [hd]; norm_num

theorem exists_mul_of_det_eq_one_su (h2 : (2 : F) ≠ 0) {z : Su F p f n} (hz : z * z = 1)
    {x : Su F p f n} (hxz : x * z = z * x)
    (hdet : (partOn (eMinus (suMat z)) (ePlus (suMat z)) (suMat x)).det = 1) :
    ∃ a ∈ longRootGroupSU F p f (suMat z), ∃ b ∈ longRootGroupSU F p f (-suMat z), x = a * b := by
  have hD := suMat_mul_self_of_mul_self hz
  have hsum := eMinus_add_ePlus (D := suMat z) h2
  have hsum' : ePlus (suMat z) + eMinus (suMat z) = 1 := (add_comm _ _).trans hsum
  have hef := eMinus_mul_ePlus hD
  have hfe := ePlus_mul_eMinus hD
  have hxD : suMat x * suMat z = suMat z * suMat x := by rw [← suMat_mul, ← suMat_mul, hxz]
  have hprod := partOn_mul_partOn hsum hef hfe (commute_eMinus' hxD) (commute_ePlus' hxD)
  have hdetp : (partOn (ePlus (suMat z)) (eMinus (suMat z)) (suMat x)).det = 1 := by
    have := congrArg Matrix.det hprod
    rw [Matrix.det_mul, hdet, one_mul] at this
    rw [this]
    exact det_suMat x
  have hunit₁ := conjTr_partOn_mul_partOn h2 hz hxD
  have hunit₂ := conjTr_partOn_mul_partOn' h2 hz hxD
  have hDe : suMat z = ePlus (suMat z) - eMinus (suMat z) := eq_ePlus_sub_eMinus h2
  have h1D : (1 : Matrix (Fin n) (Fin n) F) + suMat z = (2 : F) • ePlus (suMat z) :=
    one_add_eq_smul_ePlus h2
  have h1D' : (1 : Matrix (Fin n) (Fin n) F) + -suMat z = (2 : F) • eMinus (suMat z) := by
    rw [← sub_eq_add_neg]
    exact one_sub_eq_smul_eMinus h2
  refine ⟨Models.mkSU F p f _ hdet hunit₁, ?_, Models.mkSU F p f _ hdetp hunit₂, ?_, ?_⟩
  · rw [mem_longRootGroupSU, Models.suMat_mkSU]
    refine ⟨?_, ?_⟩
    · have e1 := partOn_mul_sub hsum hef hfe (suMat x)
      have e2 := sub_mul_partOn hsum hef hfe (suMat x)
      rw [← hDe] at e1 e2
      rw [e1, e2]
    · rw [h1D, Matrix.mul_smul, partOn_mul_right hef hfe hsum]
  · rw [mem_longRootGroupSU, Models.suMat_mkSU]
    refine ⟨?_, ?_⟩
    · have e1 := partOn_mul_sub hsum' hfe hef (suMat x)
      have e2 := sub_mul_partOn hsum' hfe hef (suMat x)
      have hDe' : -suMat z = eMinus (suMat z) - ePlus (suMat z) := by
        calc -suMat z = -(ePlus (suMat z) - eMinus (suMat z)) := by rw [← hDe]
          _ = eMinus (suMat z) - ePlus (suMat z) := neg_sub _ _
      rw [← hDe'] at e1 e2
      rw [e1, e2]
    · rw [h1D', Matrix.mul_smul, partOn_mul_right hfe hef hsum']
  · apply suMat_injective
    rw [suMat_mul, Models.suMat_mkSU, Models.suMat_mkSU]
    exact hprod.symm

theorem det_partOn_eq_one_of_pow_three (hF9 : Nat.card F = 9) (h2 : (2 : F) ≠ 0)
    {z : Su F p f n} (hz : z * z = 1) {x : Su F p f n} (hxz : x * z = z * x) (hx3 : x ^ 3 = 1) :
    (partOn (eMinus (suMat z)) (ePlus (suMat z)) (suMat x)).det = 1 := by
  have hD := suMat_mul_self_of_mul_self hz
  have hsum := eMinus_add_ePlus (D := suMat z) h2
  have hef := eMinus_mul_ePlus hD
  have hfe := ePlus_mul_eMinus hD
  have hxD : suMat x * suMat z = suMat z * suMat x := by rw [← suMat_mul, ← suMat_mul, hxz]
  have hMe := commute_eMinus' hxD
  have hMf := commute_ePlus' hxD
  have hMMe : (suMat x * suMat x) * eMinus (suMat z) = eMinus (suMat z) * (suMat x * suMat x) := by
    rw [Matrix.mul_assoc, hMe, ← Matrix.mul_assoc, hMe, Matrix.mul_assoc]
  have hMMf : (suMat x * suMat x) * ePlus (suMat z) = ePlus (suMat z) * (suMat x * suMat x) := by
    rw [Matrix.mul_assoc, hMf, ← Matrix.mul_assoc, hMf, Matrix.mul_assoc]
  have hM3 : suMat x * (suMat x * suMat x) = 1 := by
    rw [← suMat_mul, ← suMat_mul, ← pow_three, hx3, suMat_one]
  have h1 := partOn_mul hsum hef hfe hMe hMe hMf
  have h2' := partOn_mul hsum hef hfe hMe hMMe hMMf
  rw [hM3, partOn_one hsum hef, h1] at h2'
  have hd := congrArg Matrix.det h2'
  rw [Matrix.det_one, Matrix.det_mul, Matrix.det_mul] at hd
  exact eq_one_of_pow_three_eq_one_of_natCard_nine hF9 (by rw [pow_three]; exact hd.symm)

theorem open_isQuasisimple_su_of_three_le (hF : Nat.card F = (p ^ f) ^ 2) {k : ℕ} (hk : 3 ≤ k)
    (hnq : (k, p ^ f) ≠ (3, 2)) : CFSG.Open.IsQuasisimple (Su F p f k) := by
  have hq' := isQuasisimple_statedSU_of_card hF hk hnq
  let e : Su F p f k ≃* CFSG.Assembly.LowTwoRank.StatedSU k (p ^ f) F :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF k)
  exact open_isQuasisimple (isQuasisimple_of_mulEquiv e.symm hq'.1)

theorem centerExp_su (hF : Nat.card F = (p ^ f) ^ 2) {k : ℕ} (hk : 3 ≤ k)
    (hnq : (k, p ^ f) ≠ (3, 2)) {j : ℕ} (hj : Nat.card F = 2 ^ j + 1) :
    CenterExp (Su F p f k) j := by
  refine CenterExp.of_mulEquiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hF k)) ?_
  intro z hz
  rw [(isQuasisimple_statedSU_of_card hF hk hnq).2] at hz
  exact Subtype.ext (by
    simpa using pow_eq_one_of_mem_statedScalars hj (Subgroup.mem_subgroupOf.mp hz))

theorem longRootGroupSU_inf_neg_eq_bot (h2 : (2 : F) ≠ 0) (z : Su F p f n) :
    longRootGroupSU F p f (suMat z) ⊓ longRootGroupSU F p f (-suMat z) = ⊥ := by
  refine eq_bot_iff.mpr fun x ⟨hx1, hx2⟩ => ?_
  have hx : suToSL (unitaryInvolution F p f) n x ∈
      longRootGroup (suMat z) ⊓ longRootGroup (-suMat z) := ⟨hx1, hx2⟩
  rw [longRootGroup_inf_neg_eq_bot h2, Subgroup.mem_bot] at hx
  exact Subgroup.mem_bot.mpr (suToSL_injective (by rw [hx, map_one]))

end Su

section Main

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem isLongRootSU2_of_isClassicalMember3 (hq : p ^ f = 3) (hF : Nat.card F = (p ^ f) ^ 2)
    {n : ℕ} (hn : 2 ≤ n) {L : Subgroup (Su F p f n)} {z : Su F p f n}
    (h : IsClassicalMember3 L z) (hO : classicalInvolutionOddCore L = ⊥) :
    IsLongRootSU2 F p f hn L z := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hp2 : p ≠ 2 := by
    intro hp2
    have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
      (hq ▸ dvd_pow_self p hf)
    omega
  have hF9 : Nat.card F = 9 := by rw [hF, hq]; norm_num
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_charP_ne_two hp2
  obtain ⟨eL⟩ := h.nonempty_equiv_sl2 hO
  let e : SL(2, ZMod 3) ≃* L := eL.symm
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hz1 : z ≠ 1 := h.ne_one
  have hLz : ∀ x ∈ L, x * z = z * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.subnormal hx)
  obtain ⟨a, ha, g, hg, hAm, hAp⟩ := exists_longRootGroupSU_data hF h2 (by omega) hzz
  set Am : Subgroup (Su F p f n) := longRootGroupSU F p f (suMat z) with hAmdef
  set Ap : Subgroup (Su F p f n) := longRootGroupSU F p f (-suMat z) with hApdef
  have hcube : ∀ y ∈ L, y ^ 3 = 1 → y ∈ Am ⊔ Ap := fun y hy hy3 => by
    obtain ⟨a', ha', b', hb', hab⟩ := exists_mul_of_det_eq_one_su h2 hzz (hLz y hy)
      (det_partOn_eq_one_of_pow_three hF9 h2 hzz (hLz y hy) hy3)
    rw [hab]
    exact Subgroup.mul_mem_sup ha' hb'
  have hLsup : L ≤ Am ⊔ Ap := by
    intro x hx
    obtain ⟨g', hg'⟩ := e.surjective ⟨x, hx⟩
    obtain ⟨a₁, b₁, c₁, ha₁, hb₁, hc₁, rfl⟩ := sl2Three_exists_cubes g'
    have hcub : ∀ y : SL(2, ZMod 3), y ^ 3 = 1 → ((e y : L) : Su F p f n) ∈ Am ⊔ Ap :=
      fun y hy => hcube _ (e y).2 (by rw [← Subgroup.coe_pow, ← map_pow, hy, map_one]; rfl)
    have hx' : x = ((e a₁ : L) : Su F p f n) * (e b₁ : L) * (e c₁ : L) := by
      have := congrArg Subtype.val hg'
      rw [map_mul, map_mul] at this
      exact this.symm
    rw [hx']
    exact mul_mem (mul_mem (hcub a₁ ha₁) (hcub b₁ hb₁)) (hcub c₁ hc₁)
  have hcomm : ∀ x ∈ Am, ∀ y ∈ Ap, x * y = y * x := fun x hx y hy =>
    commute_of_mem_longRootGroupSU_neg h2 hzz hx hy
  have hinf : Am ⊓ Ap = ⊥ := longRootGroupSU_inf_neg_eq_bot h2 z
  have hzAm : z ∈ Am := mem_longRootGroupSU_self hzz
  have hAmC : Am ≤ Subgroup.centralizer ({z} : Set (Su F p f n)) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_longRootGroupSU hx)
  have hApC : Ap ≤ Subgroup.centralizer ({z} : Set (Su F p f n)) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply suMat_injective
    rw [suMat_mul, suMat_mul]
    have := hx.1
    rw [Matrix.mul_neg, Matrix.neg_mul] at this
    exact neg_injective this
  have hsub : IsSubnormal L (Am ⊔ Ap) := by
    have := isSubnormal_inf h.subnormal (Am ⊔ Ap)
    rwa [inf_eq_left.mpr hLsup, inf_eq_right.mpr (sup_le hAmC hApC)] at this
  obtain ⟨eAm0⟩ := nonempty_mulEquiv_map_blockEmb (F := F) (p := p) (f := f)
    (by omega : 0 + a ≤ n) g
  obtain ⟨eAp0⟩ := nonempty_mulEquiv_map_blockEmb (F := F) (p := p) (f := f)
    (by omega : a + (n - a) ≤ n) g
  obtain ⟨eAm⟩ : Nonempty (Su F p f a ≃* ↥Am) := ⟨eAm0.trans (MulEquiv.subgroupCongr hAm.symm)⟩
  obtain ⟨eAp⟩ : Nonempty (Su F p f (n - a) ≃* ↥Ap) :=
    ⟨eAp0.trans (MulEquiv.subgroupCongr hAp.symm)⟩
  obtain ⟨e2⟩ := nonempty_sl2_mulEquiv_su_two (K := F) (p := p) (f := f) hF
  obtain ⟨e3⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three
    (F := ↥(fixedSubfield F p f)) (by rw [card_fixedSubfield hF, hq])
  have hnq : ∀ k : ℕ, (k, p ^ f) ≠ (3, 2) := fun k h' => by
    have := congrArg Prod.snd h'
    simp only at this
    omega
  have hB : Subsingleton ↥Ap ∨
      (CFSG.Open.IsQuasisimple ↥Ap ∧ IsPGroup 2 (Subgroup.center ↥Ap)) ∨
      Nonempty (SL(2, ZMod 3) ≃* ↥Ap) := by
    generalize hbdef : n - a = b at eAp
    rcases Nat.lt_or_ge b 3 with hb3 | hb3
    · rcases Nat.lt_or_ge b 2 with hb2 | hb2
      · left
        have : Subsingleton (Su F p f b) := subsingleton_su_of_le_one (by omega)
        exact eAp.surjective.subsingleton
      · right
        right
        obtain rfl : b = 2 := by omega
        exact ⟨e3.symm.trans (e2.trans eAp)⟩
    · right
      left
      exact ⟨Components.quasisimple_of_equiv eAp.symm
        (open_isQuasisimple_su_of_three_le hF hb3 (hnq b)),
        (CenterExp.of_mulEquiv eAp.symm
          (centerExp_su hF hb3 (hnq b) (j := 3) (by rw [hF9]; norm_num))).isPGroup⟩
  have hLA : L ≤ Am := le_of_isSubnormal_of_commute hcomm hinf e hLsup hsub hB h.mem hz1 hzAm
  have hLA' : IsSubnormal L Am := by
    have := isSubnormal_inf h.subnormal Am
    rwa [inf_eq_left.mpr hLA, inf_eq_right.mpr hAmC] at this
  have ha2 : a = 2 := by
    by_contra hne
    rcases Nat.lt_or_ge a 2 with hlt | hge
    · have hsing : Subsingleton (Su F p f a) := subsingleton_su_of_le_one (by omega)
      have : Subsingleton Am := eAm.surjective.subsingleton
      exact hz1 (congrArg Subtype.val (Subsingleton.elim (⟨z, hzAm⟩ : Am) 1))
    · exact not_isQuasisimple_of_member3 e hLA hLA'
        (Components.quasisimple_of_equiv eAm.symm
          (open_isQuasisimple_su_of_three_le hF (by omega) (hnq a)))
  subst ha2
  have hcard : Nat.card Am ≤ 24 := by
    rw [← Nat.card_congr eAm.toEquiv, ← Nat.card_congr e2.toEquiv, Nat.card_congr e3.toEquiv,
      natCard_sl2Three]
  have : Finite Am := Nat.finite_of_card_ne_zero (fun h0 => by
    have := Nat.card_pos (α := ↥Am)
    omega)
  have hLeq : L = Am := eq_of_le_of_natCard_le e hLA hcard
  refine ⟨g, ?_, ?_⟩
  · rw [hLeq, hAm]
    rfl
  · apply suMat_injective
    rw [suMat_mul, suMat_mul, suMat_rootInvSU]
    calc suMat z = suMat z * (suMat g * suMat g⁻¹) := by
          rw [suMat_mul_suMat_inv, Matrix.mul_one]
      _ = (suMat z * suMat g) * suMat g⁻¹ := (Matrix.mul_assoc _ _ _).symm
      _ = suMat g * negBlock F n 0 * suMat g⁻¹ := by rw [hg]; rfl

end Main

section Model

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem

variable {p f : ℕ} [Fact p.Prime]

theorem exists_conj_rankOne_of_isClassicalMember3 {F : Type} [Field F] [Finite F] [CharP F p]
    (hq : p ^ f = 3) (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) {k : Fin (n / 2)}
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = 2 • weight n (lowIdx k))
    (hγ' : toStd n (-γ) = 2 • weight n (Fin.rev (lowIdx k)))
    {L : Subgroup (SU (unitaryInvolution F p f) n)} {z : SU (unitaryInvolution F p f) n}
    (hL : IsClassicalMember3 L z) (hO : classicalInvolutionOddCore L = ⊥) :
    ∃ c : SU (unitaryInvolution F p f) n, L =
      (rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n γ ⊔
        rootGroup (unitaryInvolution F p f) (unitaryInvolution_involutive hF) n (-γ)).map
          (MulAut.conj c).toMonoidHom := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hp2 : p ≠ 2 := by
    intro hp2
    have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
      (hq ▸ dvd_pow_self p hf)
    omega
  obtain ⟨P, hP⟩ := exists_wittMatrix hF n
  have hL' := hL.map_mulEquiv (conjEquiv P hP)
  have hO' : classicalInvolutionOddCore (L.map (conjEquiv P hP).toMonoidHom) = ⊥ := by
    let eL := L.equivMapOfInjective (conjEquiv P hP).toMonoidHom (conjEquiv P hP).injective
    have hmap : (classicalInvolutionOddCore L).map eL.toMonoidHom =
        classicalInvolutionOddCore (L.map (conjEquiv P hP).toMonoidHom) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant eL
    rw [← hmap, hO, Subgroup.map_bot]
  have hLR : IsLongRootSU2 F p f hn (L.map (conjEquiv P hP).toMonoidHom) (conjEquiv P hP z) :=
    isLongRootSU2_of_isClassicalMember3 hq hF hn hL' hO'
  obtain ⟨i₀, hR⟩ := exists_isLongRootSU2_map_rankOne hF hp2 hn hγ hγ' P hP
  obtain ⟨c, hc⟩ := exists_conj_of_isLongRootSU2 hLR hR
  exact ⟨(conjEquiv P hP).symm c, eq_map_conj_of_map_eq _ hc⟩

theorem classicalMembersFundamental3Tag_PSU : ClassicalMembersFundamental3Tag .PSU := by
  intro n hp hFT hadm L z hL hO
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hn2 : 2 ≤ n := by omega
  have : NeZero (2 * 1) := ⟨by omega⟩
  have hF : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 :=
    card_galoisField_two_mul 3 1 le_rfl
  have hM : Generic.modelUniv .PSU n 3 1 hp =
      ⟨↥(SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) n),
        Unitary.rootDatum (card_galoisField_two_mul 3 1 le_rfl) n⟩ :=
    (rfl : Generic.modelUniv .PSU n 3 1 hp = ModelFacts.modelUniv .PSU n 3 1 hp).trans
      (modelUniv_PSU (n := n) (p := 3) (f := 1) le_rfl)
  obtain ⟨k, γ, hγlong, hγ, hγ'⟩ := exists_longest_root_psu hp hadm
  suffices h : ∀ M : LieUniversal, M =
      ⟨↥(SU (unitaryInvolution (GaloisField 3 (2 * 1)) 3 1) n),
        Unitary.rootDatum (card_galoisField_two_mul 3 1 le_rfl) n⟩ →
      ∀ (L : Subgroup M.K) (z : M.K), IsClassicalMember3 L z → classicalInvolutionOddCore L = ⊥ →
        L ∈ Generic.fundamentalSubgroups .PSU M.D from h _ hM L z hL hO
  intro M hM' L z hL hO
  subst hM'
  obtain ⟨c, hc⟩ := exists_conj_rankOne_of_isClassicalMember3 (p := 3) (f := 1) (by norm_num) hF
    hn2 hγ hγ' hL hO
  exact ⟨c, γ, Or.inl hγlong, hc⟩

end Model

end CFSG.ClassicalInvolution.Q3

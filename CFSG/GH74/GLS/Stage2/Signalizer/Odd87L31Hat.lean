module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Red
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Stmt
import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

section HatCover

theorem hat_pPrimeCore_eq_bot {G : Type} [Group G] [Finite G] (J : Subgroup G) :
    pPrimeCore 2 (↥J ⧸ pPrimeCore 2 ↥J) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥J)).ker := by
    rw [QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  have h := (prime_complement_kernel_core_preimage (p := 2)
    (QuotientGroup.mk' (pPrimeCore 2 ↥J)) (QuotientGroup.mk'_surjective _) hk).2
  rw [← h, QuotientGroup.map_mk'_self]

theorem hat_equiv_of_cover {G : Type} [Group G] [Finite G] {J X : Subgroup G} (hXJ : X ≤ J)
    (hcov : ∀ j ∈ J, ∃ x ∈ X, ∃ n ∈ pPrimeCoreOf 2 J, j = x * n)
    (hq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) :
    Nonempty (↥X ⧸ pPrimeCore 2 ↥X ≃* (↥J ⧸ pPrimeCore 2 ↥J)) := by
  have _ := hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥X →* ↥J ⧸ pPrimeCore 2 ↥J := hatMap J hXJ
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, n, hn, hjx⟩ := hcov j j.2
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hatMap_apply]
    obtain ⟨n', hn', rfl⟩ := hn
    have h1 : (⟨x, hXJ hx⟩ : ↥J)⁻¹ * j = n' := by
      apply Subtype.ext
      simp [hjx]
    exact QuotientGroup.eq.mpr (h1 ▸ hn')
  have hker : f.ker = pPrimeCore 2 ↥X := by
    apply le_antisymm
    · have hcop : Nat.Coprime 2 (Nat.card f.ker) := by
        have hle : f.ker.map X.subtype ≤ pPrimeCoreOf 2 J := by
          rintro _ ⟨x, hx, rfl⟩
          exact (mem_ker_hatMap J hXJ x).mp hx
        have h1 : Nat.card (f.ker.map X.subtype) ∣ Nat.card (pPrimeCoreOf 2 J) :=
          Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_map_of_injective X.subtype_injective] at h1
        exact Nat.coprime_two_left.mpr ((odd_card_pPrimeCoreOf_J J).of_dvd_nat h1)
      exact le_sSup ⟨inferInstance, hcop⟩
    · intro x hx
      have h1 : f x ∈ pPrimeCore 2 (↥J ⧸ pPrimeCore 2 ↥J) :=
        map_pPrimeCore_le f hsurj ⟨x, hx, rfl⟩
      rw [hat_pPrimeCore_eq_bot J] at h1
      exact h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

end HatCover

section HatLayer

theorem hat_layer_eq_top {M : Type} [Group M] (hM : IsQuasisimple M) : layer M = ⊤ :=
  CFSG.WholeGroup.layer_eq_top_of_isQuasisimple hM

theorem hat_map_pLayerOf_subgroupOf {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ((pLayerOf 2 H).subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) =
      layer (↥H ⧸ pPrimeCore 2 ↥H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pLayerOf 2 H = (CFSG.pLayer ↥H 2).map H.subtype := by
    rw [TwoThin.pLayerOf_two_eq_map,
      CFSG.ComponentClassification.LocalBFailure.pLayer_two_eq_twoLayer]
  have h2 : ((CFSG.pLayer ↥H 2).map H.subtype).subgroupOf H = CFSG.pLayer ↥H 2 :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [h1, h2]
  exact CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient

theorem hat_pLayerOf_equiv {G : Type} [Group G] [Finite G] (X : Subgroup G)
    (hq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X)) :
    Nonempty (↥(pLayerOf 2 X) ⧸ pPrimeCore 2 ↥(pLayerOf 2 X) ≃* (↥X ⧸ pPrimeCore 2 ↥X)) := by
  refine hat_equiv_of_cover (TwoThin.pLayerOf_le 2 X) (fun j hj => ?_) hq
  have h1 := hat_map_pLayerOf_subgroupOf X
  rw [hat_layer_eq_top hq] at h1
  have hmem : (QuotientGroup.mk (⟨j, hj⟩ : ↥X) : ↥X ⧸ pPrimeCore 2 ↥X) ∈
      ((pLayerOf 2 X).subgroupOf X).map (QuotientGroup.mk' (pPrimeCore 2 ↥X)) := by
    rw [h1]
    trivial
  obtain ⟨x, hx, hxj⟩ := hmem
  have hmk : (x⁻¹ * ⟨j, hj⟩ : ↥X) ∈ pPrimeCore 2 ↥X := QuotientGroup.eq.mp hxj
  exact ⟨(x : G), hx, (x : G)⁻¹ * j, ⟨x⁻¹ * ⟨j, hj⟩, hmk, by simp⟩, by group⟩

end HatLayer

section ClauseB

theorem hat_not_isSolvable_of_isQuasisimple {G : Type} [Group G] {X : Subgroup G}
    (hq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X)) : ¬ Group.IsSolvable ↥X := by
  intro hsol
  obtain ⟨hperf, hsimp, -⟩ := hq
  have hsolQ : Group.IsSolvable (↥X ⧸ pPrimeCore 2 ↥X) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (pPrimeCore 2 ↥X))
      (QuotientGroup.mk'_surjective _)
  have : IsSimpleGroup ((↥X ⧸ pPrimeCore 2 ↥X) ⧸ center (↥X ⧸ pPrimeCore 2 ↥X)) := hsimp
  have hnt : Nontrivial (↥X ⧸ pPrimeCore 2 ↥X) :=
    (QuotientGroup.mk_surjective (s := center (↥X ⧸ pPrimeCore 2 ↥X))).nontrivial
  have := hperf
  exact Group.IsPerfect.not_isSolvable (↥X ⧸ pPrimeCore 2 ↥X) hsolQ

theorem hat_isL2_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {P : ℕ → Prop}
    (h : IVK.IsL2 X P) : IVK.IsL2 Y P := by
  obtain ⟨F₀, i₁, i₂, hP, ⟨e'⟩⟩ := h
  exact ⟨F₀, i₁, i₂, hP, ⟨e.symm.trans e'⟩⟩

theorem l31_b_of_four {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (h29n : Lemma29NonSolv) (hctx : Stage2Ctx G z k S) {U X : Subgroup G}
    (hU : IVK.IsFourSubgroup U) (hX : X ≤ centralizer (U : Set G))
    (hq : IsQuasisimple (↥X ⧸ pPrimeCore 2 ↥X)) :
    Nonempty (↥X ⧸ pPrimeCore 2 ↥X ≃* alternatingGroup (Fin 7)) ∨
      IVK.IsL2 (↥X ⧸ pPrimeCore 2 ↥X) Odd := by
  obtain ⟨e⟩ := hat_pLayerOf_equiv X hq
  rcases h29n G z k S hctx U hU X hX (hat_not_isSolvable_of_isQuasisimple hq) with hL2 | ⟨⟨e'⟩⟩
  · exact Or.inr (hat_isL2_of_mulEquiv e hL2)
  · exact Or.inl ⟨e.symm.trans e'⟩

end ClauseB

section FourSubgroups

theorem hat_isFourSubgroup_of_card_sq {G : Type} [Group G] (V : Subgroup G)
    (h4 : Nat.card V = 4) (hsq : ∀ v ∈ V, v * v = 1) : IVK.IsFourSubgroup V := by
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
    intro v hv w hw
    have h1 : v * w * (v * w) = 1 := hsq _ (V.mul_mem hv hw)
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v hv)
    have hw' : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hsq w hw)
    have h2 : v * w = (v * w)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [h2, mul_inv_rev, hv', hw']
  refine ⟨?_, h4⟩
  exact
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hVcomm a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun a => by
        apply Subtype.ext
        simpa [sq] using hsq a a.2) }

theorem hat_isFourSubgroup_map {X Y : Type} [Group X] [Group Y] {V : Subgroup X}
    (hV : IVK.IsFourSubgroup V) (f : X →* Y) (hf : Function.Injective f) :
    IVK.IsFourSubgroup (V.map f) := by
  obtain ⟨hEA, hc⟩ := hV
  have := hEA
  exact ⟨IsElementaryAbelian.map f, by rw [Subgroup.card_map_of_injective hf, hc]⟩

theorem hat_exists_isFourSubgroup_of_involutions {G : Type} [Group G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hne : a ≠ b) : ∃ V : Subgroup G, IVK.IsFourSubgroup V := by
  have hba : b * a = a * b := hab.symm
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haab : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have hbab : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have habb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have haba : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have hab2 : a * b * (a * b) = 1 := by rw [← mul_assoc, haba, hb]
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, hbi])
  have habA : a * b ≠ a := fun h => hb1 (by simpa using h)
  have habB : a * b ≠ b := fun h => ha1 (by simpa using h)
  let V : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
          simp [ha, hb, hba, haab, hbab, habb, haba, hab2]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rcases hx with hx | hx | hx | hx <;> rw [hx]
        · simp
        · simp [hai]
        · simp [hbi]
        · simp [mul_inv_rev, hai, hbi, hba] }
  have hV : (V : Set G) = {1, a, b, a * b} := by
    ext x
    simp [V]
  have hcard : Nat.card V = 4 := by
    have h1 : Nat.card V = (V : Set G).ncard := Nat.card_coe_set_eq (V : Set G)
    rw [h1, hV, Set.ncard_insert_of_notMem (by simp [ha1.symm, hb1.symm, hab1.symm]),
      Set.ncard_insert_of_notMem (by simp [hne, habA.symm]), Set.ncard_pair habB.symm]
  have hsq : ∀ v ∈ V, v * v = 1 := by
    intro v hv
    rcases hv with hv | hv | hv | hv <;> rw [hv]
    · simp
    · exact ha
    · exact hb
    · exact hab2
  exact ⟨V, hat_isFourSubgroup_of_card_sq V hcard hsq⟩

theorem hat_exists_isFourSubgroup_dihedral (c : ℕ) (hc : 1 ≤ c) :
    ∃ V : Subgroup (DihedralGroup (2 * c)), IVK.IsFourSubgroup V := by
  have hcc : (c : ZMod (2 * c)) + (c : ZMod (2 * c)) = 0 := by
    have h : ((2 * c : ℕ) : ZMod (2 * c)) = 0 := ZMod.natCast_self (2 * c)
    push_cast at h
    rw [← h]
    ring
  have hc0 : (c : ZMod (2 * c)) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.le_of_dvd hc h
    omega
  refine hat_exists_isFourSubgroup_of_involutions
    (a := DihedralGroup.r (c : ZMod (2 * c))) (b := DihedralGroup.sr 0) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [DihedralGroup.r_mul_r, hcc, DihedralGroup.r_zero]
  · exact DihedralGroup.sr_mul_self 0
  · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, zero_sub, zero_add,
      neg_eq_of_add_eq_zero_left hcc]
  · intro h
    rw [← DihedralGroup.r_zero] at h
    exact hc0 (DihedralGroup.r.inj h)
  · intro h
    rw [← DihedralGroup.r_zero] at h
    cases h
  · intro h
    cases h

theorem exists_four_of_isDihedral {G : Type} [Group G] {R : Subgroup G} (hR : IsPGroup 2 ↥R)
    (h : IsDihedral ↥R) : ∃ U : Subgroup G, U ≤ R ∧ IVK.IsFourSubgroup U := by
  obtain ⟨m, k, -, hk2, ⟨e⟩⟩ := h
  have hD : IsPGroup 2 (DihedralGroup k) := hR.of_equiv e
  obtain ⟨n, hn⟩ := hD (DihedralGroup.r 1)
  have hkn : k ∣ 2 ^ n := by
    have := orderOf_dvd_of_pow_eq_one hn
    rwa [DihedralGroup.orderOf_r_one] at this
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hkn
  have hi0 : i ≠ 0 := by
    rintro rfl
    simp at hi
    omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  obtain ⟨c, rfl⟩ : ∃ c, k = 2 * c := ⟨2 ^ j, by rw [hi, pow_succ']⟩
  obtain ⟨V, hV⟩ := hat_exists_isFourSubgroup_dihedral c (by omega)
  refine ⟨(V.map e.symm.toMonoidHom).map R.subtype, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · rw [Subgroup.map_map]
    exact hat_isFourSubgroup_map hV _ (R.subtype_injective.comp e.symm.injective)

theorem hat_exists_isFourSubgroup_of_two_le_pRank {Y : Type} [Group Y] [Finite Y]
    (h : 2 ≤ pRank 2 Y) : ∃ E : Subgroup Y, IVK.IsFourSubgroup E := by
  set S := {r : ℕ | ∃ A : Subgroup Y, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} with hSdef
  have hne : S.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : pRank 2 Y = 0 := by
      show sSup S = 0
      rw [hne, csSup_empty]
      rfl
    omega
  have hbdd : BddAbove S := by
    refine ⟨Nat.card Y, ?_⟩
    rintro r ⟨A, -, hA⟩
    have h1 : r < 2 ^ r := Nat.lt_two_pow_self
    have h2 : Nat.card A ≤ Nat.card Y := Subgroup.card_le_card_group A
    omega
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
  have hm : 2 ≤ sSup S := h
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (G := A)
    (by rw [hcard]; exact pow_dvd_pow 2 hm)
  have h4 : Nat.card (F.map A.subtype) = 4 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hF]
    norm_num
  refine ⟨F.map A.subtype, hat_isFourSubgroup_of_card_sq _ h4 ?_⟩
  rintro _ ⟨f, -, rfl⟩
  have hf : f ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A) f
  simpa [sq] using congrArg Subtype.val hf

end FourSubgroups

section ClauseBWrapper

theorem l31_b_of_isDihedral {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S : Subgroup G}
    (h29n : Lemma29NonSolv) (hctx : Stage2Ctx G z k S) {H J R : Subgroup G}
    (hJ : IsPCompIn 2 H J)
    (hR : CFSG.ABGLocalTools.IsSylowOf 2 R (H ⊓ centralizerSection J (pPrimeCoreOf 2 J)))
    (hd : IsDihedral ↥R) :
    Nonempty (Hat J ≃* alternatingGroup (Fin 7)) ∨ IVK.IsL2 (Hat J) Odd := by
  obtain ⟨hpg, -, -, hcomm, hJ0J, hcov⟩ := l31_reduce hJ hR
  have hqJ : IsQuasisimple (Hat J) := TwoThin.isQuasisimple_hat hJ
  obtain ⟨e⟩ := hat_equiv_of_cover hJ0J hcov hqJ
  have hq0 : IsQuasisimple (Hat (redJ0 J R)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hqJ
  obtain ⟨U, hUR, hU⟩ := exists_four_of_isDihedral hpg hd
  have hX : redJ0 J R ≤ centralizer (U : Set G) := fun x hx =>
    mem_centralizer_iff.mpr fun u hu => (hcomm x hx u (hUR hu)).symm
  rcases l31_b_of_four h29n hctx hU hX hq0 with ⟨⟨e'⟩⟩ | hL2
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr (hat_isL2_of_mulEquiv e hL2)

end ClauseBWrapper

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

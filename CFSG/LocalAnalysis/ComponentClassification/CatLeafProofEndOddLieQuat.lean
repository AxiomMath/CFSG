module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASymplecticExclusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QdSLNotInvolvedOfDihedralSylowTwo
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Basic
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Seven
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
open scoped MatrixGroups

@[expose] def QuatComponentForm (G : Type) [Group G] : Prop :=
  ∀ L : Subgroup G, IsComponent L → ∃ H : Subgroup L, Nonempty (H ≃* QuaternionGroup 2)

theorem quatComponentForm_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : QuatComponentForm H) : QuatComponentForm G := by
  intro L hL
  obtain ⟨Q, ⟨eQ⟩⟩ := h _ (LocalCores.isComponent_map_mulEquiv e hL)
  let eL : L ≃* L.map e.toMonoidHom := L.equivMapOfInjective _ e.injective
  exact ⟨Q.map eL.symm.toMonoidHom,
    ⟨(Q.equivMapOfInjective _ eL.symm.injective).symm.trans eQ⟩⟩

theorem exists_quaternion_of_injective_SL {F : Type*} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) {G : Type*} [Group G] (φ : SL(2, F) →* G)
    (hφ : Function.Injective φ) : ∃ H : Subgroup G, Nonempty (H ≃* QuaternionGroup 2) := by
  refine UnbalancedGS.SymplecticExclusion.exists_quaternion_of_sl2_hom hF φ fun h => ?_
  have h1 : (-1 : SL(2, F)) = 1 := hφ (h.trans (map_one φ).symm)
  have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) h1
  simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    Matrix.neg_apply, Matrix.one_apply_eq] at h00
  exact Ring.two_ne_zero hF (by linear_combination -h00)

theorem exists_quaternion_of_mulEquiv_SL {F : Type*} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    {G : Type*} [Group G] (e : G ≃* SL(2, F)) :
    ∃ H : Subgroup G, Nonempty (H ≃* QuaternionGroup 2) :=
  exists_quaternion_of_injective_SL hF e.symm.toMonoidHom e.symm.injective

theorem quaternionGroup_two_eq_of_sq_eq_one :
    ∀ x : QuaternionGroup 2, x ^ 2 = 1 → x = 1 ∨ x = QuaternionGroup.a 2 := by
  decide

theorem not_nonempty_quaternion_equiv_dihedral {k : ℕ} (hk : 1 ≤ k) :
    ¬ Nonempty (QuaternionGroup 2 ≃* DihedralGroup (2 ^ k)) := by
  rintro ⟨e⟩
  have hinv : ∀ i : ZMod (2 ^ k), e.symm (DihedralGroup.sr i) = QuaternionGroup.a 2 := by
    intro i
    rcases quaternionGroup_two_eq_of_sq_eq_one (e.symm (DihedralGroup.sr i))
      (by rw [← map_pow, sq, DihedralGroup.sr_mul_self, map_one]) with h | h
    · have h' : DihedralGroup.sr i = 1 := e.symm.injective (h.trans (map_one _).symm)
      rw [DihedralGroup.one_def] at h'
      cases h'
    · exact h
  have h01 : (0 : ZMod (2 ^ k)) = 1 :=
    DihedralGroup.sr.inj (e.symm.injective ((hinv 0).trans (hinv 1).symm))
  have : Fact (1 < 2 ^ k) := ⟨Nat.one_lt_pow (by omega) (by omega)⟩
  have hval := congrArg ZMod.val h01
  norm_num [ZMod.val_zero, ZMod.val_one] at hval

theorem false_of_quaternion_of_hasDihedralSylowTwo {G : Type*} [Group G] [Finite G]
    (hG : GorensteinWalter.HasDihedralSylowTwo G) (H : Subgroup G)
    (e : H ≃* QuaternionGroup 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 (QuaternionGroup 2) := by
    rw [IsPGroup.iff_card]
    refine ⟨3, ?_⟩
    norm_num [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hP : IsPGroup 2 H := hQ.of_equiv e.symm
  obtain ⟨S, hHS⟩ := hP.exists_le_sylow
  obtain ⟨m, hm, ⟨eS⟩⟩ := hG S
  let eT : QuaternionGroup 2 ≃* (H.subgroupOf S).map eS.toMonoidHom :=
    e.symm.trans ((Subgroup.subgroupOfEquivOfLe hHS).symm.trans
      ((H.subgroupOf S).equivMapOfInjective _ eS.injective))
  rcases GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral hm
      ((H.subgroupOf S).map eS.toMonoidHom) with hc | ⟨k, hk, ⟨eT'⟩⟩
  · have hQ8 : ¬ IsMulCommutative (QuaternionGroup 2) := by
      intro h
      let : IsMulCommutative (QuaternionGroup 2) := h
      have hcomm := (IsMulCommutative.is_comm
        (M := QuaternionGroup 2)).comm
          (QuaternionGroup.a 1 : QuaternionGroup 2)
          (QuaternionGroup.xa 0 : QuaternionGroup 2)
      simp only [QuaternionGroup.a_mul_xa, QuaternionGroup.xa_mul_a] at hcomm
      have hbad := QuaternionGroup.xa.inj hcomm
      exact (by decide : (-(1 : ZMod 4)) ≠ 1) hbad
    exact hQ8 (eT.isCyclic.mpr hc).isMulCommutative
  · exact not_nonempty_quaternion_equiv_dihedral hk ⟨eT.trans eT'⟩

theorem eq_one_of_mem_pPrimeCore_of_quaternion {K : Type*} [Group K] [Finite K]
    {H : Subgroup K} (e : H ≃* QuaternionGroup 2) {h : H}
    (hh : (h : K) ∈ pPrimeCore 2 K) : h = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH : Nat.card H = 2 ^ 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have h1 : orderOf h ∣ 2 ^ 3 := hH ▸ orderOf_dvd_natCard h
  have h2 : orderOf h ∣ Nat.card (pPrimeCore 2 K) := by
    have e1 : orderOf (h : K) = orderOf h := Subgroup.orderOf_coe h
    have e2 : orderOf ((⟨(h : K), hh⟩ : pPrimeCore 2 K) : K) =
        orderOf (⟨(h : K), hh⟩ : pPrimeCore 2 K) := Subgroup.orderOf_coe _
    rw [← e1]
    change orderOf ((⟨(h : K), hh⟩ : pPrimeCore 2 K) : K) ∣ _
    rw [e2]
    exact orderOf_dvd_natCard _
  have hc : Nat.Coprime (orderOf h) 2 :=
    (Nat.Coprime.coprime_dvd_right h2 (pPrimeCore_coprime_card (p := 2) (G := K))).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right 3 hc) h1)

theorem center_quotient_pPrimeCore_eq_bot_of_footeFamilyType {X : Type} [Group X]
    {K : Subgroup X} [Finite K] (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hF : FooteFamilyType K) : center (K ⧸ pPrimeCore 2 K) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih := FooteLit.hasDihedralSylowTwo_of_footeFamilyType hF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (K ⧸ pPrimeCore 2 K)) with h | h
  · exact h
  · exfalso
    have htop : Open.fusionZStar K = ⊤ := by
      rw [Sol78.fusionZStar_eq_comap, h, comap_top]
    obtain ⟨S⟩ : Nonempty (Sylow 2 (K ⧸ Open.fusionZStar K)) := inferInstance
    obtain ⟨m, -, ⟨eS⟩⟩ := hdih S
    have h1 : Nat.card (S : Subgroup (K ⧸ Open.fusionZStar K)) ≤ (Open.fusionZStar K).index :=
      Subgroup.card_le_card_group _
    have hidx : (Open.fusionZStar K).index = 1 := Subgroup.index_eq_one.2 htop
    rw [hidx, Nat.card_congr eS.toEquiv, DihedralGroup.nat_card] at h1
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega

theorem exists_mul_ne_of_footeFamilyType {X : Type} [Group X] {K : Subgroup X} [Finite K]
    (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hF : FooteFamilyType K) :
    ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hZ := center_quotient_pPrimeCore_eq_bot_of_footeFamilyType hs hF
  obtain ⟨x, hx⟩ := exists_ne (1 : K ⧸ pPrimeCore 2 K)
  apply hx
  have hxZ : x ∈ center (K ⧸ pPrimeCore 2 K) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h b a]
  rw [hZ] at hxZ
  exact hxZ

theorem false_of_footeFamilyType_quaternion {X : Type} [Group X] {K : Subgroup X} [Finite K]
    (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hF : FooteFamilyType K) (H : Subgroup K)
    (e : H ≃* QuaternionGroup 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih := FooteLit.hasDihedralSylowTwo_of_footeFamilyType hF
  have hZ := center_quotient_pPrimeCore_eq_bot_of_footeFamilyType hs hF
  have hZ' : Open.fusionZStar K = pPrimeCore 2 K := (Sol78.fusionZStar_eq_iff K).2 hZ
  let ψ : H →* K ⧸ Open.fusionZStar K := (QuotientGroup.mk' (Open.fusionZStar K)).comp H.subtype
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    have hh' : (h : K) ∈ pPrimeCore 2 K := by
      rw [← hZ']
      exact (QuotientGroup.eq_one_iff _).1 hh
    rw [eq_one_of_mem_pPrimeCore_of_quaternion e hh']
    exact Subgroup.one_mem _
  exact false_of_quaternion_of_hasDihedralSylowTwo hdih ψ.range
    ((MonoidHom.ofInjective hψ).symm.trans e)

theorem false_of_isTwoComponentAt_of_quat {X : Type} [Group X] [Finite X] {z : X}
    {K : Subgroup X}
    (hq : ∀ L : Subgroup (centralizer ({z} : Set X)), IsPComponent 2 L → IsQuasisimple L)
    (hQ : QuatComponentForm (centralizer ({z} : Set X))) (hK : IsTwoComponentAt z K)
    (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hF : FooteFamilyType K) : False := by
  obtain ⟨-, hKC, hKc⟩ := hK
  have hLc : IsComponent (K.subgroupOf (centralizer ({z} : Set X))) :=
    ⟨hq _ hKc, by obtain ⟨_, _, h, _⟩ := hKc; exact h⟩
  obtain ⟨H, ⟨e⟩⟩ := hQ _ hLc
  let eK : K.subgroupOf (centralizer ({z} : Set X)) ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  exact false_of_footeFamilyType_quaternion hs hF (H.map eK.toMonoidHom)
    ((H.equivMapOfInjective _ eK.injective).symm.trans e)

end CFSG.ComponentClassification.CatLeafProof

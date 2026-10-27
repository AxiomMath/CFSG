module

public import CFSG.HardMathSupport.Dickson.SuzukiReeB.Helpers
import CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.ReeG2Outer
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerBridge
import CFSG.RankThree.Chevalley.SteinbergCFSmallReeComponentCores
import CFSG.Walter.ReeOrder.WardLocal.Main
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Ree.Duality
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.HardMathSupport.Dickson.SuzukiReeB

open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem three_dvd_mul_sq_sub_one (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  have h : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h with h | h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
    have h2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    omega
  · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
    have h2 : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    omega

private theorem isSolvable_of_odd_normal_two_quotient {C : Type} [Group C] [Finite C]
    (N : Subgroup C) [N.Normal] (hN : Nat.Coprime 2 (Nat.card N)) (hQ : IsPGroup 2 (C ⧸ N)) :
    Group.IsSolvable C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp hN)
  haveI : Group.IsNilpotent (C ⧸ N) := hQ.isNilpotent
  exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => ⟨⟨x, hx⟩, rfl⟩)

private theorem hasNormalPComplement_two_of_cyclic {C : Type} [Group C] [Finite C]
    (hcyc : ∀ S : Sylow 2 C, IsCyclic S) : CFSG.HasNormalPComplement 2 C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h2 : 2 ∣ Nat.card C
  · let S : Sylow 2 C := Classical.choice Sylow.nonempty
    have hmin : (Nat.card C).minFac = 2 := (Nat.minFac_eq_two_iff (Nat.card C)).2 h2
    have hNC : Subgroup.normalizer (S : Set C) ≤ Subgroup.centralizer (S : Set C) :=
      (hcyc S).normalizer_le_centralizer hmin
    have hScenter : (S : Subgroup C) ≤
        CFSG.centerIn (G := C) (Subgroup.normalizer (S : Subgroup C)) := by
      intro s hs
      refine ⟨Subgroup.le_normalizer hs, ?_⟩
      change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set C) : Set C)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
    exact CFSG.hasNormalPComplement_of_sylow_le_center_normalizer 2 S hScenter
  · have hodd : Odd (Nat.card C) := by
      rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
      exact h2
    refine ⟨⊤, inferInstance, ?_, ?_⟩
    · simpa using hodd.coprime_two_left
    · intro x
      refine ⟨0, ?_⟩
      have hsub : Subsingleton (C ⧸ (⊤ : Subgroup C)) := QuotientGroup.subsingleton_quotient_top
      simpa using (@Subsingleton.elim _ hsub x 1)

section Dihedral


private theorem isPGroup_two_quotient_of_dihedral {C : Type} [Group C] [Finite C]
    (h3 : ¬ 3 ∣ Nat.card C) (hD : CFSG.GorensteinWalter.HasDihedralSylowTwo C) :
    IsPGroup 2 (C ⧸ CFSG.pPrimeCore 2 C) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases (CFSG.GorensteinWalter.gorensteinWalter : CFSG.GorensteinWalter.gorensteinWalterStatement)
      C hD with ⟨_, hq⟩ | ⟨_, ⟨e⟩⟩ | ⟨_, K, hKp, L, hLn, hLi, hLm⟩
  · exact hq
  · exfalso
    apply h3
    have h7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have h1 : Nat.card (C ⧸ CFSG.pPrimeCore 2 C) = 2520 := by
      rw [Nat.card_congr e.toEquiv, h7]
    exact (show 3 ∣ 2520 by norm_num).trans (h1 ▸ Subgroup.card_quotient_dvd_card _)
  · exfalso
    apply h3
    refine Dvd.dvd.trans ?_ ((Subgroup.card_subgroup_dvd_card L).trans
      (Subgroup.card_quotient_dvd_card _))
    have hodd : Odd (Nat.card K) := by
      obtain ⟨p, n, hp, hpodd, hn, hpn⟩ := hKp
      rw [hpn]
      exact hpodd.pow
    have h2 : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) := by
      have hK1 : Nat.card K % 2 = 1 := Nat.odd_iff.mp hodd
      have hK2 : Nat.card K ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hK1]
      exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _
    rcases hLm with ⟨⟨eL⟩⟩ | ⟨⟨eL⟩⟩
    · rw [Nat.card_congr eL.toEquiv, CFSG.GorensteinWalter.psl2_card_formula K hKp]
      have h3' := three_dvd_mul_sq_sub_one (Nat.card K)
      obtain ⟨m, hm⟩ := h2
      rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hm] at h3'
      omega
    · rw [Nat.card_congr eL.toEquiv, CFSG.GorensteinWalter.pgl2_card_formula K]
      exact three_dvd_mul_sq_sub_one _

private theorem isSolvable_of_three_not_dvd_of_sylow_two_small {C : Type} [Group C] [Finite C]
    (h3 : ¬ 3 ∣ Nat.card C)
    (hT : ∀ T : Sylow 2 C, Nat.card T ≤ 4 ∧
      ∀ a ∈ (T : Subgroup C), ∀ b ∈ (T : Subgroup C), a * b = b * a ∧ a * a = 1) :
    Group.IsSolvable C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 C) := inferInstance
  have hcard : ∀ T : Sylow 2 C, Nat.card T = Nat.card T₀ := fun T =>
    Nat.card_congr (Sylow.equiv T T₀).toEquiv
  have hpow : ∀ T : Sylow 2 C, Nat.card T = 2 ^ (Nat.card C).factorization 2 := fun T =>
    T.card_eq_multiplicity
  by_cases h4 : Nat.card T₀ = 4
  · have hD : CFSG.GorensteinWalter.HasDihedralSylowTwo C := by
      intro T
      refine ⟨1, le_refl 1, ?_⟩
      have hT4 : Nat.card T = 4 := (hcard T).trans h4
      have hK : IsKleinFour ↥(T : Subgroup C) := by
        refine ⟨hT4, ?_⟩
        haveI : Nontrivial ↥(T : Subgroup C) := by
          rw [← Finite.one_lt_card_iff_nontrivial]
          change 1 < Nat.card (T : Subgroup C)
          rw [hT4]
          norm_num
        rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
        intro g hg
        apply orderOf_eq_prime
        · have h' : g * g = 1 := Subtype.ext ((hT T).2 g.1 g.2 g.1 g.2).2
          simpa [sq] using h'
        · exact hg
      have e := (IsKleinFour.nonempty_mulEquiv (G₁ := ↥(T : Subgroup C))
        (G₂ := DihedralGroup 2)).some
      exact ⟨by simpa using e⟩
    exact isSolvable_of_odd_normal_two_quotient (CFSG.pPrimeCore 2 C) CFSG.pPrimeCore_coprime_card
      (isPGroup_two_quotient_of_dihedral h3 hD)
  · have hcycT : ∀ T : Sylow 2 C, IsCyclic T := by
      intro T
      have h4' : Nat.card T ≠ 4 := by rw [hcard T]; exact h4
      have hk : (Nat.card C).factorization 2 ≤ 1 := by
        by_contra hlt
        push Not at hlt
        have : 2 ^ 2 ≤ 2 ^ (Nat.card C).factorization 2 := Nat.pow_le_pow_right (by norm_num) hlt
        have := (hT T).1
        have := hpow T
        omega
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with h0 | h1
      · have : Nat.card T = 1 := by rw [hpow T, h0]; rfl
        haveI : Subsingleton T := (Nat.card_eq_one_iff_unique.mp this).1
        infer_instance
      · have : Nat.card T = 2 := by rw [hpow T, h1]; rfl
        exact isCyclic_of_prime_card this
    obtain ⟨N, hNn, hNc, hNq⟩ := hasNormalPComplement_two_of_cyclic hcycT
    haveI := hNn
    exact isSolvable_of_odd_normal_two_quotient N hNc hNq

end Dihedral

section Ward


open CFSG.Walter.Ward CFSG.Walter.WardLocal CFSG.Walter.JT

private theorem not_three_dvd_card_centralizer {G : Type} [Group G] [Finite G]
    (h : ReeTypeHyp G) {x : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hx : orderOf x = p) : ¬ 3 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  classical
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨k, hk, hq⟩, hG⟩ := ward_order h
  letI : Fintype G := Fintype.ofFinite G
  haveI : CharP h.F 3 := ree_charP_three h hq
  obtain ⟨S, D, B, -⟩ := exists_data h hq hG
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.centralizer ({x} : Set G))) 3 h3
  have hyx : (y : G) * x = x * (y : G) := Subgroup.mem_centralizer_singleton_iff.mp y.2
  have hcomm : Commute x (y : G) := hyx.symm
  have hy3 : orderOf (y : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hcop : (orderOf x).Coprime (orderOf (y : G)) := by
    rw [hx, hy3]
    exact (Nat.coprime_primes hp Nat.prime_three).mpr hp3
  have hxy : orderOf (x * (y : G)) = p * 3 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hx, hy3]
  have hodd : Odd (orderOf (x * (y : G))) := by
    rw [hxy]
    exact (hp.odd_of_ne_two hp2).mul (by decide)
  have h3' : 3 ∣ orderOf (x * (y : G)) := by rw [hxy]; exact dvd_mul_left 3 p
  have hdvd := B.card_centralizer_dvd hq hG hodd h3'
  have hxmem : x ∈ Subgroup.centralizer ({x * (y : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (x * (y : G)) = x * ((y : G) * x) := by rw [hyx]
      _ = x * (y : G) * x := (mul_assoc _ _ _).symm
  have hpdvd : p ∣ Nat.card (Subgroup.centralizer ({x * (y : G)} : Set G)) := by
    rw [← hx, ← Subgroup.orderOf_mk x hxmem]
    exact orderOf_dvd_natCard _
  rcases (Nat.Prime.dvd_mul hp).mp (hpdvd.trans hdvd) with h2 | h2
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · have h3q : p ∣ 3 := by
      have := hp.dvd_of_dvd_pow h2
      rw [hq] at this
      exact hp.dvd_of_dvd_pow this
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3q)

private theorem sylow_two_centralizer_small {G : Type} [Group G] [Finite G] (hJ : JTHyp G)
    (hJ2 : hJ.p ≠ 2) {x : G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hx : orderOf x = p)
    (C : Subgroup G) (hC : ∀ c ∈ C, c * x = x * c) (T : Sylow 2 C) :
    Nat.card T ≤ 4 ∧ ∀ a ∈ (T : Subgroup C), ∀ b ∈ (T : Subgroup C), a * b = b * a ∧ a * a = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hSyl, -, hcent, -⟩ := lemma_2_1 hJ hJ2
  have hcardT' : Nat.card ((T : Subgroup C).map C.subtype) = Nat.card T := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
  have hT'p : IsPGroup 2 ((T : Subgroup C).map C.subtype) :=
    IsPGroup.of_card (n := (Nat.card C).factorization 2)
      (by rw [hcardT']; exact T.card_eq_multiplicity)
  obtain ⟨E, hTE⟩ := hT'p.exists_le_sylow
  obtain ⟨hEA, hE8⟩ := hSyl E
  haveI := hEA
  have hT'C : ∀ e ∈ (T : Subgroup C).map C.subtype, e * x = x * e := by
    intro e he
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp he
    exact hC c c.2
  refine ⟨?_, ?_⟩
  · by_contra hgt
    push Not at hgt
    have h8 : Nat.card T ∣ 2 ^ 3 := by
      have := Subgroup.card_dvd_of_le hTE
      rw [hE8, hcardT'] at this
      simpa using this
    obtain ⟨i, hi, hTi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h8
    have hT8 : Nat.card T = 8 := by
      rw [hTi] at hgt ⊢
      interval_cases i <;> simp_all
    have hEq : (T : Subgroup C).map C.subtype = (E : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge hTE (by rw [hE8, hcardT', hT8])
    have hxE : x ∈ Subgroup.centralizer ((E : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      exact hT'C e (hEq ▸ he)
    rw [hcent E] at hxE
    have hx2 : x ^ 2 = 1 :=
      CFSG.elemPow_eq_one_of_isElementaryAbelian (A := (E : Subgroup G)) x hxE
    have : p ∣ 2 := hx ▸ orderOf_dvd_of_pow_eq_one hx2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  · intro a ha b hb
    have haE : (a : G) ∈ (E : Subgroup G) := hTE (Subgroup.mem_map_of_mem _ ha)
    have hbE : (b : G) ∈ (E : Subgroup G) := hTE (Subgroup.mem_map_of_mem _ hb)
    refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
    · have := hEA.toIsMulCommutative.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩
      have h' : (a : G) * b = b * a := congrArg Subtype.val this
      exact h'
    · have h2 :=
        CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := (E : Subgroup G)) (a : G) haE
      simpa [sq] using h2

end Ward

private theorem isQuasisimple_of_simple_nonab {L : Type*} [Group L] (hs : IsSimpleGroup L)
    (hnc : ∃ a b : L, a * b ≠ b * a) : CFSG.IsQuasisimple L := by
  haveI := hs
  have hc : Subgroup.center L = ⊥ := by
    rcases (inferInstance : (Subgroup.center L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  refine ⟨?_,
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup, ?_⟩
  · refine Group.isPerfect_def.mpr ?_
    rcases (inferInstance : (commutator L).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hmem : ⁅a, b⁆ ∈ commutator L :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hab hmem
    · exact h
  · obtain ⟨a, b, hab⟩ := hnc
    refine ⟨(a : L ⧸ Subgroup.center L), (b : L ⧸ Subgroup.center L), fun h => hab ?_⟩
    have := (QuotientGroup.eq (s := Subgroup.center L) (a := a * b) (b := b * a)).mp (by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, h])
    rw [hc, Subgroup.mem_bot] at this
    exact inv_mul_eq_one.mp this

private theorem perfectInLayer_of_commutator_simple {S : Type*} [Group S] [Finite S]
    (β : MulAut S) {Γ' : Type*} [Group Γ'] (e : ↥(fixSubgroup β) ≃* Γ')
    (hs : IsSimpleGroup ↥(commutator Γ')) (hnc : ∃ x y : ↥(commutator Γ'), x * y ≠ y * x) :
    PerfectInLayer β := by
  set C := fixSubgroup β with hC
  have hmap : (commutator ↥C).map e.toMonoidHom = commutator Γ' := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  let eN : ↥(commutator ↥C) ≃* ↥(commutator Γ') :=
    ((commutator ↥C).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hsC : IsSimpleGroup ↥(commutator ↥C) := eN.isSimpleGroup
  have hncC : ∃ x y : ↥(commutator ↥C), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eN.symm x, eN.symm y, fun h => hxy (by simpa using congrArg eN h)⟩
  let N : Subgroup S := (commutator ↥C).map C.subtype
  have hNC : N.subgroupOf C = commutator ↥C :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  let eN' : ↥(commutator ↥C) ≃* ↥N :=
    (commutator ↥C).equivMapOfInjective C.subtype C.subtype_injective
  have hNn : (N.subgroupOf C).Normal := by rw [hNC]; infer_instance
  refine perfectInLayer_of_normal_quasisimple β (N := N) (Subgroup.map_subtype_le _) hNn ?_ ?_
  · haveI := hsC
    have hsN : IsSimpleGroup ↥N := eN'.symm.isSimpleGroup
    have hncN : ∃ x y : ↥N, x * y ≠ y * x := by
      obtain ⟨x, y, hxy⟩ := hncC
      exact ⟨eN' x, eN' y, fun h => hxy (by simpa using congrArg eN'.symm h)⟩
    exact isQuasisimple_of_simple_nonab hsN hncN
  · refine Group.isSolvable_of_comm fun x y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hNC]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

section Gamma

open CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification CFSG.RankThree.PartOne.Sec66T


private theorem isSolvable_centralizer_reeGamma {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {x : ReeTag.G2.reeGamma K a}
    (hx : orderOf x = p) :
    Group.IsSolvable (Subgroup.centralizer ({x} : Set (ReeTag.G2.reeGamma K a))) := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  obtain ⟨hJT, hJ3, -⟩ := CFSG.Walter.Ree.Model.small_Ree_jtHyp a ha K hK
  obtain ⟨hW⟩ := CFSG.Walter.Ree.Model.small_Ree_reeTypeHyp a ha K hK
  refine isSolvable_of_three_not_dvd_of_sylow_two_small
    (not_three_dvd_card_centralizer hW hp hp2 hp3 hx) fun T => ?_
  exact sylow_two_centralizer_small hJT (by rw [hJ3]; decide) hp hp2 hx _
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc) T

private theorem perfectInLayer_reeGamma {a : ℕ} (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {β : MulAut (ReeTag.G2.reeGamma K a)} (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) : PerfectInLayer β := by
  have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hin : β ∈
      (MulAut.conj : ReeTag.G2.reeGamma K a →* MulAut (ReeTag.G2.reeGamma K a)).range
  · obtain ⟨-, hsimple, hnc⟩ := CatalogueBSmallRee.reeGamma_G2_simple ha K hK
    haveI := hsimple
    obtain ⟨x, rfl, hxp, hx1⟩ :=
      exists_eq_conj_of_mem_range (b3Lie_center_eq_bot hnc) hin hβ hβ1
    refine perfectInLayer_of_isSolvable _ ?_
    rw [fixSubgroup_conj]
    exact isSolvable_centralizer_reeGamma ha K hK hp hp2 hp3 (orderOf_eq_prime hxp hx1)
  · obtain ⟨-, δ, σ, hσord, hδ, -⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp hp2 β
        hβ hin
    obtain ⟨b, -, hbcard, hchar, ⟨eC⟩⟩ :=
      CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.reeG2_fixed_data hK hp hp2 hσord
    haveI := hchar
    obtain ⟨hs, hnc, -⟩ :=
      CatalogueBSmallRee.small_Ree_whole_group_p_components b (fixSubfield σ) hbcard
    have hfix : fixSubgroup (ReeTag.G2.reeGammaFieldAut K a σ) =
        fixSub (ReeTag.G2.reeGammaFieldAut K a σ) :=
      Subgroup.ext fun y => by rw [mem_fixSubgroup, mem_fixSub]
    have hσ : PerfectInLayer (ReeTag.G2.reeGammaFieldAut K a σ) :=
      perfectInLayer_of_commutator_simple _ ((MulEquiv.subgroupCongr hfix).trans eC) hs hnc
    have h2 := LieSemisimple.perfectInLayer_conj δ⁻¹ _ hσ
    rwa [← hδ, show δ⁻¹ * (δ * β * δ⁻¹) * δ⁻¹⁻¹ = β by group] at h2

end Gamma

theorem perfectInLayer_reeG2
    (m : ℕ) (hv : (TauCeti.LieTypeIndex.reeG2 m).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {β : MulAut S} (hβ : β ^ p = 1) (hβ1 : β ≠ 1) :
    CFSG.HardMathSupport.Solomon.Coordinator.PerfectInLayer β := by
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ :=
    CFSG.RankThree.Chevalley.exists_mulEquiv_reeGamma_G2_of_reeTitsModel
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_reeG2 m ⟨hv, he⟩)
  refine LieSemisimple.perfectInLayer_of_congr e β ?_
  refine perfectInLayer_reeGamma ha K hK hp hp2 hp3 ?_ ?_
  · rw [← map_pow, hβ, map_one]
  · intro h
    exact hβ1 ((MulAut.congr e).map_eq_one_iff.mp h)

end CFSG.HardMathSupport.Dickson.SuzukiReeB

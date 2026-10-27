module

public import CFSG.ClassicalInvolution.Q3.TL3Main
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

theorem isSubnormal_sup_normal {G : Type*} [Group G] {J C N : Subgroup G}
    (h : IsSubnormal J C) (hN : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    IsSubnormal (J ⊔ N) (C ⊔ N) := by
  induction h with
  | refl H => exact IsSubnormal.refl _
  | @step H M K hHM hHn hMK ih =>
    have hMC : M ≤ K := isSubnormal_le hMK
    refine IsSubnormal.step (sup_le_sup_right hHM N) ?_ (ih hN)
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le_sup_right hHM N)]
    have hHnorm : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHn
    have key : ∀ m ∈ M, ∀ y ∈ H ⊔ N, m * y * m⁻¹ ∈ H ⊔ N := by
      intro m hm
      have hle : H ⊔ N ≤ (H ⊔ N).comap (MulAut.conj m).toMonoidHom := by
        refine sup_le (fun h' hh' => ?_) (fun n hn => ?_)
        · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hHnorm hm) h').mp hh')
        · exact Subgroup.mem_sup_right (hN m (hMC hm) n hn)
      exact fun y hy => hle hy
    refine sup_le (fun m hm => ?_) (le_sup_right.trans Subgroup.le_normalizer)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key m hm y hy, fun hy => ?_⟩
    have := key m⁻¹ (M.inv_mem hm) _ hy
    simpa [mul_assoc] using this

theorem sl2Three_exists_order_three : ∃ y : SL(2, ZMod 3), y ^ 3 = 1 ∧ y ≠ 1 := by
  decide +kernel

theorem sl2Three_centralizer_card :
    ∀ y : SL(2, ZMod 3), y ^ 3 = 1 → y ≠ 1 →
      Fintype.card {z : SL(2, ZMod 3) // z * y = y * z} ≤ 6 := by
  decide +kernel

theorem exists_threeElement_of_isClassicalMember3 {G : Type} [Group G] [Finite G] {R : Subgroup G}
    (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2)))) {t : G}
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    {J : Subgroup G} (hRJ : R ≤ J) (hJ : IsClassicalMember3 J t) :
    ∃ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) ∧ x ^ 3 ^ k = 1 ∧
      (∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) ∧
      IsSubnormal (R ⊔ Subgroup.zpowers x ⊔ oddCoreImg (Subgroup.centralizer ({t} : Set G)))
        (Subgroup.centralizer ({t} : Set G)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({t} : Set G) with hC
  have hJC : J ≤ C := isSubnormal_le hJ.subnormal
  have hCR : C ≤ Subgroup.normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn
  have hRJn : (R.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRJ).mpr (hJC.trans hCR)
  have hOR : oddCoreImg R ≤ oddCoreImg J :=
    Balance.oddCoreIn_le_of_isSubnormal (isSubnormal_of_normal_subgroupOf hRJ hRJn)
  have hOJC : oddCoreImg J ≤ oddCoreImg C := Balance.oddCoreIn_le_of_isSubnormal hJ.subnormal
  obtain ⟨φ⟩ := hJ.nonempty_equiv
  obtain ⟨y0, hy03, hy01⟩ := sl2Three_exists_order_three
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (φ.symm y0)
  have hNpos : 0 < orderOf g := orderOf_pos g
  obtain ⟨a, b, hb3, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd hNpos.ne' 3 (by norm_num)
  set f : J →* SL(2, ZMod 3) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore J)) with hf
  have hfg : f g = y0 := by
    simp [hf, hg]
  set xJ : J := g ^ b with hxJ
  set x : G := (xJ : G) with hx
  have hxJmem : x ∈ J := xJ.2
  have hxC : x ∈ C := hJC hxJmem
  have hx3 : x ^ 3 ^ a = 1 := by
    have : xJ ^ 3 ^ a = 1 := by
      rw [hxJ, ← pow_mul, mul_comm, ← hN]
      exact pow_orderOf_eq_one g
    have := congrArg (fun z : J => (z : G)) this
    simpa using this
  set y1 : SL(2, ZMod 3) := f xJ with hy1
  have hy1eq : y1 = y0 ^ b := by rw [hy1, hxJ, map_pow, hfg]
  have hy13 : y1 ^ 3 = 1 := by rw [hy1eq, ← pow_mul, mul_comm, pow_mul, hy03, one_pow]
  have hy11 : y1 ≠ 1 := by
    intro h
    rw [hy1eq] at h
    have hord : orderOf y0 = 3 := orderOf_eq_prime hy03 hy01
    have : 3 ∣ b := hord ▸ orderOf_dvd_of_pow_eq_one h
    exact hb3 this
  have hker : ∀ z : J, f z = 1 ↔ z ∈ classicalInvolutionOddCore J := by
    intro z
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let ι : (S : Subgroup R) →* J := (Subgroup.inclusion hRJ).comp (S : Subgroup R).subtype
  let ψ : (S : Subgroup R) →* SL(2, ZMod 3) := f.comp ι
  have hιinj : Function.Injective ι := fun u v h => by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : J => (z : G)) h
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : ι u ∈ classicalInvolutionOddCore J := (hker _).mp hu
    obtain ⟨m, hm⟩ := S.isPGroup' u
    have h2 : (ι u) ^ 2 ^ m = 1 := by rw [← map_pow, hm, map_one]
    have h3 : orderOf (ι u) ∣ Nat.card (classicalInvolutionOddCore J) := by
      have := orderOf_dvd_natCard (⟨ι u, h1⟩ : classicalInvolutionOddCore J)
      simpa using this
    have h4 : orderOf (ι u) ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h2
    have hodd : Odd (Nat.card (classicalInvolutionOddCore J)) :=
      CFSG.ComponentClassification.OddCore.odd_card J
    have h5 : orderOf (ι u) = 1 := by
      have hodd' : Odd (orderOf (ι u)) := hodd.of_dvd_nat h3
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
      rcases j with _ | j
      · simpa using hj
      · exfalso
        have h2dvd : 2 ∣ orderOf (ι u) := by rw [hj]; exact dvd_pow_self 2 (Nat.succ_ne_zero j)
        exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2dvd)
    exact hιinj (by rw [map_one]; exact orderOf_eq_one_iff.mp h5)
  have hSr : ∃ r : ℕ, 3 ≤ r ∧ Nat.card (S : Subgroup R) = 4 * 2 ^ (r - 2) := by
    obtain ⟨r, hr, ⟨e⟩⟩ := hS
    exact ⟨r, hr, by rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]⟩
  obtain ⟨r, hr, hSc⟩ := hSr
  have h8 : 8 ≤ Nat.card (S : Subgroup R) := by
    rw [hSc]
    have : 2 ^ 1 ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hb : ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R := by
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ u : (S : Subgroup R), ψ u * y1 = y1 * ψ u := by
      intro u
      have hu : (((u : R)) : G) ∈ R := (u : R).2
      obtain ⟨w, hw, hwe⟩ := hOR (hcon _ hu)
      have hcomm' : ⁅xJ, ι u⁆ ∈ classicalInvolutionOddCore J := by
        have : w = ⁅xJ, ι u⁆ := by
          apply Subtype.ext
          have hwe' : (w : G) = ⁅x, (((u : R)) : G)⁆ := hwe
          rw [hwe']
          simp [commutatorElement_def, hx, ι]
        rwa [← this]
      have h1 : f ⁅xJ, ι u⁆ = 1 := (hker _).mpr hcomm'
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h1
      exact (h1.eq).symm
    have hcard : Nat.card (S : Subgroup R) ≤ 6 := by
      calc Nat.card (S : Subgroup R)
          ≤ Nat.card {z : SL(2, ZMod 3) // z * y1 = y1 * z} :=
            Nat.card_le_card_of_injective (fun u => ⟨ψ u, hcomm u⟩)
              (fun u v h => hψinj (congrArg Subtype.val h))
        _ = Fintype.card {z : SL(2, ZMod 3) // z * y1 = y1 * z} := Nat.card_eq_fintype_card
        _ ≤ 6 := sl2Three_centralizer_card y1 hy13 hy11
    omega
  set RJ : Subgroup J := R.subgroupOf J with hRJdef
  set H : Subgroup SL(2, ZMod 3) := RJ.map f ⊔ Subgroup.zpowers y1 with hH
  have hψH : ∀ u : (S : Subgroup R), ψ u ∈ H := by
    intro u
    refine Subgroup.mem_sup_left ⟨ι u, ?_, rfl⟩
    show ((ι u : J) : G) ∈ R
    exact (u : R).2
  have hd1 : Nat.card (S : Subgroup R) ∣ Nat.card H := by
    have hle : ψ.range ≤ H := by
      rintro _ ⟨u, rfl⟩
      exact hψH u
    have := Subgroup.card_dvd_of_le hle
    rwa [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv] at this
  have hd2 : 3 ∣ Nat.card H := by
    have hord : orderOf y1 = 3 := orderOf_eq_prime hy13 hy11
    have := Subgroup.card_dvd_of_le (le_sup_right : Subgroup.zpowers y1 ≤ H)
    rwa [Nat.card_zpowers, hord] at this
  have hd3 : Nat.card H ∣ 24 := by
    have := Subgroup.card_subgroup_dvd_card H
    rwa [natCard_sl2Three] at this
  have hcop : Nat.Coprime (Nat.card (S : Subgroup R)) 3 := by
    rw [hSc]
    refine Nat.Coprime.mul_left (by norm_num) ?_
    exact Nat.Coprime.pow_left _ (by norm_num)
  have hdd : Nat.card (S : Subgroup R) * 3 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hd1 hd2
  have hHcard : Nat.card H = Nat.card SL(2, ZMod 3) := by
    have h24 : Nat.card H ≤ 24 := Nat.le_of_dvd (by norm_num) hd3
    have h24' : 24 ≤ Nat.card (S : Subgroup R) * 3 := by omega
    have h24'' : Nat.card (S : Subgroup R) * 3 ≤ Nat.card H :=
      Nat.le_of_dvd Nat.card_pos hdd
    rw [natCard_sl2Three]
    omega
  have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hHcard
  have hmap : H = (RJ ⊔ Subgroup.zpowers xJ).map f := by
    rw [hH, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hmapJ : (RJ ⊔ Subgroup.zpowers xJ).map J.subtype = R ⊔ Subgroup.zpowers x := by
    rw [Subgroup.map_sup, hRJdef, Subgroup.map_subgroupOf_eq_of_le hRJ, MonoidHom.map_zpowers]
    rfl
  have hOC : oddCoreImg C ≤ C := oddCoreImg_le C
  have hJle : J ≤ R ⊔ Subgroup.zpowers x ⊔ oddCoreImg C := by
    intro j hj
    have hjH : f ⟨j, hj⟩ ∈ H := by rw [hHtop]; exact Subgroup.mem_top _
    rw [hmap] at hjH
    obtain ⟨m, hm, hmj⟩ := hjH
    have hk : m⁻¹ * ⟨j, hj⟩ ∈ classicalInvolutionOddCore J :=
      (hker _).mp (by rw [map_mul, map_inv, hmj, inv_mul_cancel])
    have hmG : (m : G) ∈ R ⊔ Subgroup.zpowers x := by
      rw [← hmapJ]
      exact Subgroup.mem_map_of_mem J.subtype hm
    have hkG : ((m⁻¹ * ⟨j, hj⟩ : J) : G) ∈ oddCoreImg C := hOJC ⟨_, hk, rfl⟩
    have hjeq : j = (m : G) * ((m⁻¹ * ⟨j, hj⟩ : J) : G) := by simp
    rw [hjeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmG) (Subgroup.mem_sup_right hkG)
  refine ⟨x, a, hxC, hx3, hb, ?_⟩
  have hJ0 : R ⊔ Subgroup.zpowers x ⊔ oddCoreImg C = J ⊔ oddCoreImg C := by
    refine le_antisymm (sup_le (sup_le (hRJ.trans le_sup_left)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hxJmem))) le_sup_right)
      (sup_le hJle le_sup_right)
  have hconj : ∀ c ∈ C, ∀ n ∈ oddCoreImg C, c * n * c⁻¹ ∈ oddCoreImg C := fun c hc n hn =>
    conj_mem_oddCoreImg (Subgroup.le_normalizer hc) hn
  have hsn := isSubnormal_sup_normal hJ.subnormal hconj
  rw [sup_eq_left.mpr hOC] at hsn
  rwa [hJ0]


theorem tightSubnormalLarge_of_tightLift3 (h : TightLift3) : TightSubnormalLarge := by
  intro G _ _ _ hnab hlarge R S hS t ht hto hRC hRn h2
  obtain ⟨J, hRJ, hJ⟩ := h G hnab hlarge R S hS t ht hto hRC hRn h2
  exact exists_threeElement_of_isClassicalMember3 S hS hRC hRn hRJ hJ

theorem TightLift3.nonempty_mulEquiv_q8 (h : TightLift3) {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (genFittingFStar G)] (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a)
    (hlarge : ¬ TwoSubgroupsFourGenerated (genFittingFStar G)) (R : Subgroup G) (S : Sylow 2 R)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup R) ≃* QuaternionGroup (2 ^ (r - 2))))
    {t : G} (ht : t ∈ (S : Subgroup R).map R.subtype) (hto : orderOf t = 2)
    (hRC : R ≤ Subgroup.centralizer ({t} : Set G))
    (hRn : (R.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal)
    (h2 : IsPGroup 2 (R ⧸ classicalInvolutionOddCore R)) :
    Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := by
  obtain ⟨x, k, hxC, hx3, hxR, -⟩ := tightSubnormalLarge_of_tightLift3 h G hnab hlarge R S hS t ht
    hto hRC hRn h2
  exact tl3_nonempty_mulEquiv_q8 S hS h2
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hRC).mp hRn) hxC hx3 hxR

theorem tightLift3_iff_tightSubnormalLarge : TightLift3 ↔ TightSubnormalLarge :=
  ⟨tightSubnormalLarge_of_tightLift3, tightLift3_of_tightSubnormalLarge⟩

end CFSG.ClassicalInvolution.Q3

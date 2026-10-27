module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Row50
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs104
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Field
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U48No5
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U48

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 center_SU4 card_SU4 isSimpleGroup_SU4
  fieldFactor4)

theorem card_of_isU4two {S : Type} [Group S] (h : catalogIs S S9.isU4two) : Nat.card S = 25920 := by
  obtain ⟨g⟩ := bridge_u4two h
  rw [Nat.card_congr g.toEquiv]
  exact CFSG.LieType.Multipliers.U42.card_PSp43

variable {G : Type} [Group G] [Finite G] {X L I : Subgroup G} {d : G}

theorem gamma_fixed_of_mem (hd : d ∈ Subgroup.normalizer (L : Set G)) (e : PQuot 3 L ≃* SU4)
    (γ : MulAut SU4) (hγ : ∀ q : PQuot 3 L, γ (e q) = e (barAut L d hd q))
    (x : ↥L) (hx : (x : G) ∈ Subgroup.centralizer ({d} : Set G)) :
    γ (piOf L e x) = piOf L e x := by
  have hxd : (x : G) * d = d * (x : G) := Subgroup.mem_centralizer_singleton_iff.1 hx
  have h1 : conjL L d hd x = x := by
    apply Subtype.ext
    rw [conjL_apply]
    calc d⁻¹ * (x : G) * d = d⁻¹ * ((x : G) * d) := by rw [mul_assoc]
      _ = d⁻¹ * (d * (x : G)) := by rw [hxd]
      _ = x := by group
  change γ (e (QuotientGroup.mk x)) = e (QuotientGroup.mk x)
  rw [hγ, barAut_mk, h1]

theorem false_of_inner_ne_one (hd : d ∈ Subgroup.normalizer (L : Set G)) (e : PQuot 3 L ≃* SU4)
    (γ : MulAut SU4) (hγ : ∀ q : PQuot 3 L, γ (e q) = e (barAut L d hd q))
    {g : SU4} (hg : MulAut.conj g = γ) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hI : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({d} : Set G)) I)
    (hIcat : catalogIs (PSimple 3 I) S9.isU4two) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hIL : I ≤ L := hI.1.trans inf_le_left
  have hIC : I ≤ Subgroup.centralizer ({d} : Set G) := hI.1.trans inf_le_right
  let ψ : ↥I →* SU4 := (piOf L e).comp (Subgroup.inclusion hIL)
  have hker3 : ¬ 3 ∣ Nat.card (piOf L e).ker := not_three_dvd_card_ker_piOf e
  have hdvd : Nat.card ψ.ker ∣ Nat.card (piOf L e).ker := by
    have hle : ψ.ker.map (Subgroup.inclusion hIL) ≤ (piOf L e).ker := by
      rintro _ ⟨k, hk, rfl⟩
      exact hk
    rw [← Subgroup.card_map_of_injective (K := ψ.ker) (Subgroup.inclusion_injective hIL)]
    exact Subgroup.card_dvd_of_le hle
  have hcop : Nat.Coprime 3 (Nat.card ψ.ker) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    exact fun h3 => hker3 (h3.trans hdvd)
  have hkerle : ψ.ker ≤ GLAPPrimeCore 3 ↥I := le_sSup ⟨inferInstance, hcop⟩
  have hcard : Nat.card (PSimple 3 I) = 25920 := card_of_isU4two hIcat
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := PSimple 3 I) 5
    (by rw [hcard]; norm_num)
  obtain ⟨x₀, hx₀⟩ := toSimple_surjective 3 I u
  set m := orderOf (ψ x₀) with hm
  have hm5 : 5 ∣ m := by
    have h1 : (ψ x₀) ^ m = 1 := pow_orderOf_eq_one _
    have h2 : x₀ ^ m ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, h1]
    have h3 : toSimple 3 I (x₀ ^ m) = 1 := by
      have := hkerle h2
      change (QuotientGroup.mk (QuotientGroup.mk (x₀ ^ m) : PQuot 3 I) : PSimple 3 I) = 1
      rw [QuotientGroup.eq_one_iff]
      have h1' : (QuotientGroup.mk (x₀ ^ m) : PQuot 3 I) = 1 :=
        (QuotientGroup.eq_one_iff _).2 this
      rw [h1']
      exact Subgroup.one_mem _
    rw [map_pow, hx₀] at h3
    rw [← hu]
    exact orderOf_dvd_of_pow_eq_one h3
  have hm0 : 0 < m := orderOf_pos _
  have hm5' : 5 ≤ m := Nat.le_of_dvd hm0 hm5
  set w : SU4 := (ψ x₀) ^ (m / 5) with hw
  have hw5 : w ^ 5 = 1 := by
    rw [hw, ← pow_mul, show m / 5 * 5 = m from Nat.div_mul_cancel hm5]
    exact pow_orderOf_eq_one _
  have hw1 : w ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  have hwfix : MulAut.conj g w = w := by
    rw [hg]
    have hwψ : w = ψ (x₀ ^ (m / 5)) := by rw [hw, map_pow]
    rw [hwψ]
    exact gamma_fixed_of_mem hd e γ hγ (Subgroup.inclusion hIL (x₀ ^ (m / 5)))
      (hIC (x₀ ^ (m / 5)).2)
  have hc : w * g = g * w := by
    have h := hwfix
    rw [MulAut.conj_apply] at h
    calc w * g = (g * w * g⁻¹) * g := by rw [h]
      _ = g * w := by group
  exact hw1 (no_five hg3 hg1 hw5 hc)

theorem false_of_inner_eq_one (hd : d ∈ Subgroup.normalizer (L : Set G)) (hd3 : d ^ 3 = 1)
    (e : PQuot 3 L ≃* SU4) (γ : MulAut SU4) (hγ : ∀ q : PQuot 3 L, γ (e q) = e (barAut L d hd q))
    (hγ1 : γ = 1) (hI : GLAPComponent 3 (L ⊓ Subgroup.centralizer ({d} : Set G)) I)
    (hIcat : catalogIs (PSimple 3 I) S9.isU4two) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := isSimpleGroup_SU4
  set Y : Subgroup G := L ⊓ Subgroup.centralizer ({d} : Set G) with hY
  have hYL : Y ≤ L := inf_le_left
  let π : ↥Y →* SU4 := (piOf L e).comp (Subgroup.inclusion hYL)
  have hπ : Function.Surjective π := by
    intro c
    obtain ⟨x, hx⟩ := piOf_surjective L e c
    have hfix : (QuotientGroup.mk (conjL L d hd x) : PQuot 3 L) = QuotientGroup.mk x := by
      have h1 := hγ (QuotientGroup.mk x)
      rw [hγ1, MulAut.one_apply, barAut_mk] at h1
      exact (e.injective h1).symm
    obtain ⟨x', hx'c, hx'mk⟩ := exists_cent_lift_outer hd hd3 x hfix
    refine ⟨⟨(x' : G), x'.2, Subgroup.mem_centralizer_singleton_iff.2 hx'c⟩, ?_⟩
    rw [← hx]
    change e (QuotientGroup.mk x') = e (QuotientGroup.mk x)
    rw [hx'mk]
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    have hdvd : Nat.card π.ker ∣ Nat.card (piOf L e).ker := by
      have hle : π.ker.map (Subgroup.inclusion hYL) ≤ (piOf L e).ker := by
        rintro _ ⟨k, hk, rfl⟩
        exact hk
      rw [← Subgroup.card_map_of_injective (K := π.ker) (Subgroup.inclusion_injective hYL)]
      exact Subgroup.card_dvd_of_le hle
    exact fun h3 => not_three_dvd_card_ker_piOf e (h3.trans hdvd)
  have hC : GLAPPrimeCore 3 SU4 = ⊥ :=
    pPrimeCore_eq_bot_of_simple (by rw [card_SU4]; norm_num)
  have hS : CFSG.Open.IsQuasisimple ↥(⊤ : Subgroup SU4) := by
    haveI : IsSimpleGroup ↥(⊤ : Subgroup SU4) := Subgroup.topEquiv.isSimpleGroup
    refine isQuasisimple_of_simple_nonabelian ?_
    intro hcomm
    obtain ⟨a, b, hab⟩ := exists_noncomm_SU4
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm (⟨a, trivial⟩ : ↥(⊤ : Subgroup SU4))
      ⟨b, trivial⟩))
  obtain ⟨J, hJ, hJl, -, ⟨ε⟩⟩ := layer_of_surj π hπ hker3 hC ⊤ hS (fun T _ => le_top)
  have hIJ : I ≤ J := by
    rw [← hJl]
    unfold GLAPLayer
    exact le_sSup hI
  have hIeq : I = J :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.glaPComponent_eq_of_le Nat.prime_three hI hJ hIJ
  subst hIeq
  let e' : PQuot 3 I ≃* SU4 := ε.trans Subgroup.topEquiv
  have hZ : Subgroup.center (PQuot 3 I) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e' z ∈ Subgroup.center SU4 := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w'
      obtain ⟨v, rfl⟩ := e'.surjective w'
      rw [← map_mul, ← map_mul, hz v]
    rw [center_SU4, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e'.injective (by rw [hz', map_one])
  have hcard : Nat.card (PSimple 3 I) = 25920 := card_of_isU4two hIcat
  have h1 : Nat.card (PSimple 3 I) = Nat.card SU4 := by
    rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, Nat.card_congr e'.toEquiv]
  rw [hcard, card_SU4] at h1
  norm_num at h1

end CFSG.LocalAnalysis.GLTheoremA.CatB.U48

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.CatB
open CFSG.LocalAnalysis.GLTheoremA.CatB.U48
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU48 (SU4 center_SU4 fieldFactor4
  mem_range_conj_of_fieldFactor4_eq_one)

section Row40


theorem fieldU48At_holds (G : Type) [Group G] [Finite G] : FieldU48At G := by
  intro X L I d hL hcat hd hd3 hI hIcat
  have hZ := center_pquot_eq_bot_of_u48 hL hcat
  let e := pqModelP hZ hcat
  let γ : MulAut SU4 := MulAut.congr e (barAut L d hd)
  have hγ : ∀ q : PQuot 3 L, γ (e q) = e (barAut L d hd q) := by
    intro q
    change (MulAut.congr e (barAut L d hd)) (e q) = _
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hγ3 : γ ^ 3 = 1 := by
    have h : (MulAut.congr e) (barAut L d hd ^ 3) = 1 := by
      rw [barAut_pow_three L d hd hd3, map_one]
    rwa [map_pow] at h
  by_cases hff : fieldFactor4 γ = 1
  · exfalso
    obtain ⟨g, hg⟩ := mem_range_conj_of_fieldFactor4_eq_one hff
    have hg3 : g ^ 3 = 1 := by
      have h1 : MulAut.conj (g ^ 3) = 1 := by rw [map_pow, hg, hγ3]
      have h2 : g ^ 3 ∈ Subgroup.center SU4 := by
        rw [Subgroup.mem_center_iff]
        intro z
        have := congrArg (fun α : MulAut SU4 => α z) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc z * g ^ 3 = (g ^ 3 * z * (g ^ 3)⁻¹) * g ^ 3 := by rw [this]
          _ = g ^ 3 * z := by group
      rw [center_SU4, Subgroup.mem_bot] at h2
      exact h2
    by_cases hg1 : g = 1
    · apply false_of_inner_eq_one hd hd3 e γ hγ _ hI hIcat
      rw [← hg, hg1, map_one]
    · exact false_of_inner_ne_one hd e γ hγ hg hg3 hg1 hI hIcat
  · exact fieldOn_of_outer hL hd hZ e γ hγ hγ3 hff

end Row40

end CFSG.LocalAnalysis.GLTheoremA

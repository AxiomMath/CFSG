module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.Cat3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5Setting

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5

open Subgroup
open scoped Pointwise

private abbrev B35 : Subgroup Z35 :=
  (⊤ : Subgroup (Multiplicative (ZMod 3))).prod (alternatingGroup (Fin 5))

private lemma zmod3_pow_three (z : Multiplicative (ZMod 3)) : z ^ 3 = 1 := by
  revert z; decide

private lemma card_mult_zmod3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
  rw [Nat.card_eq_fintype_card]; exact ZMod.card 3

private lemma card_alternating_five : Nat.card (↥(alternatingGroup (Fin 5))) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]; decide

private lemma card_B35 : Nat.card B35 = 180 := by
  have h := Nat.card_congr (Subgroup.prodEquiv
    (⊤ : Subgroup (Multiplicative (ZMod 3))) (alternatingGroup (Fin 5))).toEquiv
  rw [Nat.card_prod, Subgroup.card_top] at h
  rw [card_mult_zmod3, card_alternating_five] at h
  norm_num at h ⊢
  exact h

private lemma conj_centralizer_inf {Y : Type*} [Group Y] {N : Subgroup Y} (hN : N.Normal)
    {x : Y} {g : Y} :
    (N ⊓ centralizer ({x} : Set Y)).map ((MulAut.conj g : Y →* Y))
      = N ⊓ centralizer ({g * x * g⁻¹} : Set Y) := by
  have himg : ((MulAut.conj g : Y →* Y) '' {x}) = ({g * x * g⁻¹} : Set Y) := by
    rw [Set.image_singleton]; rfl
  have himg' : (((MulAut.conj g).symm : Y →* Y) '' {g * x * g⁻¹}) = ({x} : Set Y) := by
    rw [Set.image_singleton]
    congr 1
    show (MulEquiv.symm (MulAut.conj g)) (g * x * g⁻¹) = x
    rw [MulAut.conj_symm_apply]
    group
  apply le_antisymm
  · refine le_trans (Subgroup.map_inf_le (H := N) (K := centralizer ({x} : Set Y))
        (f := (MulAut.conj g : Y →* Y))) ?_
    refine inf_le_inf (le_of_eq ?_) ?_
    · haveI := hN
      exact Subgroup.Normal.map_conj_eq N g
    · calc (centralizer {x}).map (MulAut.conj g : Y →* Y)
          ≤ centralizer ((MulAut.conj g : Y →* Y) '' {x}) :=
            Subgroup.map_centralizer_le_centralizer_image _ _
        _ = centralizer ({g * x * g⁻¹} : Set Y) := by rw [himg]
  · have hback : (N ⊓ centralizer ({g * x * g⁻¹} : Set Y)).map
        ((MulAut.conj g).symm : Y →* Y) ≤ N ⊓ centralizer ({x} : Set Y) := by
      refine le_trans (Subgroup.map_inf_le (H := N)
        (K := centralizer ({g * x * g⁻¹} : Set Y))
        (f := ((MulAut.conj g).symm : Y →* Y))) ?_
      refine inf_le_inf (le_of_eq ?_) ?_
      · have hsymm : ((MulAut.conj g).symm : Y →* Y) = (MulAut.conj g⁻¹ : Y →* Y) := by
          ext y
          show (MulEquiv.symm (MulAut.conj g)) y = (MulAut.conj g⁻¹) y
          rw [MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]
        rw [hsymm]
        haveI := hN
        exact Subgroup.Normal.map_conj_eq N g⁻¹
      · calc (centralizer ({g * x * g⁻¹} : Set Y)).map ((MulAut.conj g).symm : Y →* Y)
            ≤ centralizer (((MulAut.conj g).symm : Y →* Y) '' {g * x * g⁻¹}) :=
              Subgroup.map_centralizer_le_centralizer_image _ _
          _ = centralizer ({x} : Set Y) := by rw [himg']
    have hcomp : ((MulAut.conj g) : Y →* Y).comp ((MulAut.conj g).symm : Y →* Y) =
        MonoidHom.id Y := by
      ext y
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      exact MulEquiv.apply_symm_apply (MulAut.conj g) y
    calc (N ⊓ centralizer ({g * x * g⁻¹} : Set Y))
        = ((N ⊓ centralizer ({g * x * g⁻¹} : Set Y)).map
            ((MulAut.conj g).symm : Y →* Y)).map ((MulAut.conj g) : Y →* Y) := by
            rw [Subgroup.map_map, hcomp, Subgroup.map_id]
      _ ≤ (N ⊓ centralizer ({x} : Set Y)).map ((MulAut.conj g) : Y →* Y) :=
            Subgroup.map_mono hback

theorem threeA5OrS5_of_normal_z35 {M : Subgroup Z35} (hM : M.Normal) (h9 : 9 ∣ Nat.card M) :
    ThreeA5OrS5 ↥M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hfac : (Nat.card Z35).factorization 3 = 2 := by
    rw [card_z35]
    have h1 : 3 ^ 2 ∣ 360 := by norm_num
    have h2 : ¬ 3 ^ 3 ∣ 360 := by norm_num
    have hp : Nat.Prime 3 := by norm_num
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 2) (n := 360)
      hp (by norm_num)).mp h1
    have hlt := (Nat.Prime.pow_dvd_iff_le_factorization (p := 3) (k := 3) (n := 360)
      hp (by norm_num)).not.mp h2
    omega
  obtain ⟨K, hKcard, -, hKM⟩ :=
    Sylow.exists_subgroup_card_pow_prime_le_le (p := 3) (n := 2) (H := ⊥) (L := M)
      (by norm_num) (by simp) (by simpa using h9) bot_le
  let S : Sylow 3 Z35 := Sylow.ofCard K (by rw [hKcard, hfac])
  have hScoe : (S : Subgroup Z35) = K := Sylow.coe_ofCard K _
  have hSM : (S : Subgroup Z35) ≤ M := by rw [hScoe]; exact hKM
  have hord : ∀ y : Z35, orderOf y = 3 → y ∈ M := by
    intro y hy
    have hzp : IsPGroup 3 ↥(zpowers y) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; norm_num)
    obtain ⟨T, hT⟩ := hzp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Z35 S T
    have hTM : (T : Subgroup Z35) ≤ M := by
      haveI := hM
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact (Subgroup.map_mono hSM).trans_eq (Subgroup.Normal.map_conj_eq M g)
    exact hTM (hT (mem_zpowers y))
  have hBle : B35 ≤ M := by
    rw [Subgroup.prod_le_iff]
    constructor
    · rw [Subgroup.map_le_iff_le_comap]
      intro z _
      by_cases hz : z = 1
      · subst hz; exact one_mem M
      · exact hord (z, 1) (by
          rw [Prod.orderOf, orderOf_eq_prime (p := 3) (zmod3_pow_three z) hz, orderOf_one,
            Nat.lcm_one_right])
    · rw [Subgroup.map_le_iff_le_comap, ← Equiv.Perm.closure_three_cycles_eq_alternating,
        Subgroup.closure_le]
      rintro σ hσ
      exact hord (1, σ) (by rw [Prod.orderOf, orderOf_one, hσ.orderOf, Nat.lcm_one_left])
  have hBindex : B35.index = 2 := by
    have hmul := Subgroup.card_mul_index B35
    rw [card_B35, card_z35] at hmul
    omega
  have hdvd : M.index ∣ B35.index := Subgroup.index_dvd_of_le hBle
  rw [hBindex] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · right
    have hMtop : M = ⊤ := Subgroup.index_eq_one.mp h1
    exact ⟨(MulEquiv.subgroupCongr hMtop).trans Subgroup.topEquiv⟩
  · left
    have hMcard : Nat.card M = 180 := by
      have hmul := Subgroup.card_mul_index M
      rw [h2, card_z35] at hmul
      omega
    have hMB : M = B35 :=
      (Subgroup.eq_of_le_of_card_ge hBle (by rw [hMcard, card_B35])).symm
    refine ⟨(MulEquiv.subgroupCongr hMB).trans ?_⟩
    exact (Subgroup.prodEquiv (⊤ : Subgroup (Multiplicative (ZMod 3)))
      (alternatingGroup (Fin 5))).trans
      (MulEquiv.prodCongr Subgroup.topEquiv (MulEquiv.refl (↥(alternatingGroup (Fin 5)))))

namespace Setting

variable {Y : Type*} [Group Y] [Finite Y] {P : Subgroup Y}

theorem factorization_three_of_le (h : Setting Y P) {N : Subgroup Y} (hPN : P ≤ N) :
    (Nat.card N).factorization 3 = 2 := by
  have h9 : 9 ∣ Nat.card N := by
    rw [← h.card]
    exact Subgroup.card_dvd_of_le hPN
  have h27 : ¬ 3 ^ 3 ∣ Nat.card N := by
    intro hd
    exact h.not_dvd (dvd_trans hd (Subgroup.card_subgroup_dvd_card N))
  have hp : Nat.Prime 3 := by norm_num
  have hpos : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have h1 : 2 ≤ (Nat.card N).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hpos).mp
      (by rw [show (3:ℕ)^2 = 9 from by norm_num]; exact h9)
  have h2 : ¬ 3 ≤ (Nat.card N).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hpos).not.mp h27
  omega

theorem threeA5OrS5_of_le (h : Setting Y P) {N : Subgroup Y} (hN : N.Normal) (hPN : P ≤ N)
    (x : ↥N) (hx : orderOf x = 3) : ThreeA5OrS5 ↥(centralizer ({x} : Set ↥N)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hxY : orderOf (x : Y) = 3 := by rw [orderOf_coe, hx]
  obtain ⟨g, hgP⟩ := exists_conj_mem_of_card_eq_pow (p := 3) (k := 2) (P := P)
      (by rw [h.card]; norm_num) (by simpa using h.not_dvd) hxY
  set x' : Y := g * (x : Y) * g⁻¹ with hx'def
  have hx'3 : orderOf x' = 3 := by
    rw [hx'def]
    rw [← SemiconjBy.orderOf_eq g (show SemiconjBy g (x : Y) (g * (x : Y) * g⁻¹) by
      rw [SemiconjBy]; group)]
    exact hxY
  have hx'P : x' ∈ P := by rw [hx'def]; exact hgP
  let C : Subgroup Y := centralizer ({x'} : Set Y)
  obtain ⟨e⟩ := h.centralizer_equiv hx'3
  let M : Subgroup Z35 := (N.subgroupOf C).map (e : ↥C →* Z35)
  have hMnorm : M.Normal :=
    (hN.subgroupOf C).map (e : ↥C →* Z35) e.surjective
  have hPC : P ≤ C := by
    intro p hp
    exact Subgroup.mem_centralizer_singleton_iff.mpr (h.comm p hp x' hx'P)
  have hP_le : P ≤ N ⊓ C := le_inf hPN hPC
  have h9inf : 9 ∣ Nat.card ↥(N ⊓ C) := by
    have hc := Subgroup.card_dvd_of_le hP_le
    rw [h.card] at hc
    exact hc
  have hcard_map : Nat.card M = Nat.card ↥(N.subgroupOf C) := by
    dsimp only [M]; exact Subgroup.card_map_of_injective e.injective
  have hcard_sub : Nat.card ↥(N.subgroupOf C) = Nat.card ↥(N ⊓ C) := by
    rw [← Subgroup.inf_subgroupOf_right N C]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ⊓ C ≤ C from inf_le_right)).toEquiv
  have h9M : 9 ∣ Nat.card M := by rw [hcard_map, hcard_sub]; exact h9inf
  have h3M : ThreeA5OrS5 ↥M := threeA5OrS5_of_normal_z35 hMnorm h9M
  have hC1_eq : (centralizer ({x} : Set ↥N)).map N.subtype
      = (N ⊓ centralizer ({(x:Y)} : Set Y)) := by
    ext a
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, Subtype.ext_iff.mp hz⟩
    · rintro ⟨haN, haC⟩
      exact ⟨⟨a, haN⟩, Subtype.ext_iff.mpr haC, rfl⟩
  have hDD' : (N ⊓ centralizer ({(x:Y)} : Set Y)).map ((MulAut.conj g : Y →* Y))
      = N ⊓ C := by
    have h := conj_centralizer_inf hN (x := (x:Y)) (g := g)
    simpa only [C, hx'def] using h
  have iso1 : ↥(centralizer ({x} : Set ↥N)) ≃* ↥(N ⊓ centralizer ({(x:Y)} : Set Y)) :=
    (Subgroup.equivMapOfInjective (centralizer ({x} : Set ↥N)) N.subtype
      N.subtype_injective).trans (MulEquiv.subgroupCongr hC1_eq)
  have iso2 : ↥(N ⊓ centralizer ({(x:Y)} : Set Y)) ≃* ↥(N ⊓ C) :=
    (Subgroup.equivMapOfInjective (N ⊓ centralizer ({(x:Y)} : Set Y))
      ((MulAut.conj g) : Y →* Y) (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hDD')
  have iso3 : ↥(N ⊓ C) ≃* ↥M :=
    (Subgroup.subgroupOfEquivOfLe (show N ⊓ C ≤ C from inf_le_right)).symm |>.trans
      ((MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right N C)).trans
        (Subgroup.equivMapOfInjective (N.subgroupOf C) (e : ↥C →* Z35) e.injective))
  have ee : ↥(centralizer ({x} : Set ↥N)) ≃* ↥M := iso1.trans (iso2.trans iso3)
  rcases h3M with h3 | h3
  · obtain ⟨e5⟩ := h3
    exact Or.inl ⟨ee.trans e5⟩
  · obtain ⟨e5⟩ := h3
    exact Or.inr ⟨ee.trans e5⟩

theorem false_of_selfCentralizing (h : Setting Y P) {N : Subgroup Y} [N.Normal]
    (hsol : Group.IsSolvable (Y ⧸ N)) {c : Y} (hcN : c ∈ N) (hc3 : orderOf c = 3)
    (hcC : N ⊓ centralizer ({c} : Set Y) = zpowers c) : False := by
  let C : Subgroup Y := centralizer ({c} : Set Y)
  have hcC' : c ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let φ : ↥C →* Y ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  have hker : φ.ker = (zpowers c).subgroupOf C := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show QuotientGroup.mk' N (a : Y) = 1 ↔ (a : Y) ∈ zpowers c
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← hcC, Subgroup.mem_inf]
    exact ⟨fun hN => ⟨hN, a.2⟩, fun h => h.1⟩
  have hzp_le : zpowers c ≤ C := by rw [Subgroup.zpowers_le]; exact hcC'
  haveI : Group.IsSolvable ↥(zpowers c) := inferInstance
  have hker_sol : Group.IsSolvable ↥φ.ker := by
    rw [hker]
    exact solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hzp_le :
        ↥((zpowers c).subgroupOf C) →* ↥(zpowers c)))
      (Subgroup.subgroupOfEquivOfLe hzp_le).injective
  have hCsol : Group.IsSolvable ↥C := by
    haveI := hker_sol
    haveI : Group.IsSolvable (Y ⧸ N) := hsol
    exact solvable_of_ker_le_range (φ.ker.subtype) φ
      (le_of_eq (Subgroup.range_subtype φ.ker).symm)
  obtain ⟨e⟩ := h.centralizer_equiv hc3
  have hZsol : Group.IsSolvable Z35 := by
    haveI := hCsol
    exact solvable_of_surjective (f := (e : ↥C →* Z35)) e.surjective
  haveI := hZsol
  exact Equiv.Perm.fin_5_not_solvable (solvable_of_surjective
    (f := MonoidHom.snd (Multiplicative (ZMod 3)) (Equiv.Perm (Fin 5)))
    (fun σ => ⟨(1, σ), rfl⟩))

end Setting

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.ONan.S5


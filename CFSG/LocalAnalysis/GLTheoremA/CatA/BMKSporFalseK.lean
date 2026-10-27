module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Image
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMKSporDefs
public import CFSG.HardMathSupport.Dickson.BMRows.KFormBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Root8
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Alt
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma83Alt

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.BMRows (kRows_of_isKGroup isKGroup_pSimple)
open CFSG.HardMathSupport.Dickson.BMRows (kRows_of_isKGroup isKGroup_pSimple)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.LocalAnalysis.GLTheoremA.AltDown
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.LocalAnalysis.GLTheoremA.I2017
open scoped commutatorElement

section BMKSporFalseK

theorem up7a8_spor_falseK {m : ℕ} (h : SporAltNoCompK m) (hm : 5 ≤ m) {G : Type} [Group G] [Finite G]
    {X K J : Subgroup G} {y : G} (hK : GLAPComponent 3 X K)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyp : y ^ 3 = 1) (hncent : ¬ CentMod 3 K y)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (s : TauCeti.SporadicName) (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hA : IsAltPType 3 J m) (hT : CFSG.Open.IsKGroup (PSimple 3 K)) : False := by
  obtain ⟨hKB, hKM⟩ := kRows_of_isKGroup hT e
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp' : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  obtain ⟨Q, _, _, K', y', ⟨eK⟩, hnorm, hpow, hcentmod, hcomp⟩ :=
    exists_pQuot_transfer Nat.prime_three hyp' hyN
  obtain ⟨J', hJ', ⟨eJ⟩⟩ := hcomp J hJ
  have hJ'le : J' ≤ K' := hJ'.1.trans inf_le_left
  have hq0 : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hq' : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eK.symm hq0
  haveI : Group.IsPerfect ↥K' := ⟨hq'.1⟩
  have eS : (↥K' ⧸ Subgroup.center ↥K') ≃* PSimple 3 K :=
    QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  have hK'bot : CFSG.pPrimeCore 3 ↥K' = ⊥ := by
    have hkcop : Nat.Coprime 3 (Nat.card eK.toMonoidHom.ker) := by
      rw [(MonoidHom.ker_eq_bot_iff eK.toMonoidHom).2 eK.injective, Subgroup.card_bot]
      exact Nat.coprime_one_right 3
    have hmap := CFSG.Semidihedral.Local.pPrimeCore_map_eq_of_coprime_ker 3 eK.toMonoidHom
      eK.surjective hkcop
    have hq1 : CFSG.pPrimeCore 3 (PQuot 3 K) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
    rw [hq1] at hmap
    rw [eq_bot_iff]
    intro x hx
    have hx' : eK.toMonoidHom x ∈ (CFSG.pPrimeCore 3 ↥K').map eK.toMonoidHom := Subgroup.mem_map_of_mem _ hx
    rw [hmap, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.2 (eK.injective (hx'.trans (map_one eK).symm))
  obtain ⟨β, hβp, hβfix⟩ := up7a8_exists_conjAut hnorm (hpow 3 hyp)
  have hJ₁' : GLAPComponent 3 (fixSubgroup β) (J'.subgroupOf K') := by
    rw [hβfix]
    exact glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ'
  have hker : (QuotientGroup.mk' (Subgroup.center ↥K')).ker ≤ Subgroup.center ↥K' :=
    (QuotientGroup.ker_mk' _).le
  have hπs : Function.Surjective (QuotientGroup.mk' (Subgroup.center ↥K')) :=
    QuotientGroup.mk'_surjective _
  have hαβ : ∀ k : ↥K', QuotientGroup.mk' (Subgroup.center ↥K') (β k) =
      centerQuotientHom ↥K' β (QuotientGroup.mk' (Subgroup.center ↥K') k) :=
    fun k => (onCenterQuotient_apply_mk β k).symm
  have hJS0 : GLAPComponent 3 (fixSubgroup (centerQuotientHom ↥K' β))
      ((J'.subgroupOf K').map (QuotientGroup.mk' (Subgroup.center ↥K'))) :=
    glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center ↥K')) hker β
      (centerQuotientHom ↥K' β) hαβ hπs Nat.prime_three hJ₁'
  have hβbarP : (centerQuotientHom ↥K' β) ^ 3 = 1 := by rw [← map_pow, hβp, map_one]
  have hβbar1 : centerQuotientHom ↥K' β ≠ 1 := by
    intro hb
    have hβ1 : β = 1 := centerQuotientHom_injective ↥K' (hb.trans (map_one _).symm)
    apply hncent
    apply hcentmod
    intro x hx
    have hmem : (⟨x, hx⟩ : ↥K') ∈ fixSubgroup β := by
      rw [mem_fixSubgroup, hβ1]
      rfl
    rw [hβfix, Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hmem
    exact hmem.2
  have hHA : Nonempty (PQuot 3 (J'.subgroupOf K') ≃* alternatingGroup (Fin m)) := by
    obtain ⟨g₁⟩ := nonempty_pQuot_equiv_subgroupOf 3 hJ'le
    obtain ⟨eA⟩ := hA
    exact ⟨g₁.trans (eJ.symm.trans eA)⟩
  obtain ⟨eH⟩ := hHA
  have hJSA : IsAltPType 3 ((J'.subgroupOf K').map (QuotientGroup.mk' (Subgroup.center ↥K'))) m := by
    obtain ⟨φ⟩ := up7a8_pQuot_map_equiv 3 (J'.subgroupOf K') (QuotientGroup.mk' (Subgroup.center ↥K'))
      (fun x hx hfx => by
        have hxZ : x ∈ Subgroup.center ↥K' := (QuotientGroup.eq_one_iff x).1 hfx
        exact up7a8_central_inj hm eH hK'bot (x := x) hx hxZ)
    exact ⟨φ.symm.trans eH⟩
  exact h (↥K' ⧸ Subgroup.center ↥K') s ⟨eS.trans e⟩ hKB hKM (centerQuotientHom ↥K' β) hβbarP hβbar1
    ((J'.subgroupOf K').map (QuotientGroup.mk' (Subgroup.center ↥K'))) hJS0 hJSA

namespace I2017

variable {G : Type} [Group G] [Finite G]

theorem i2017_spor_falseK (hS : SporAltNoCompK 8) {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 K))
    {α : MulAut (PQuot 3 K)} (hα3 : α ^ 3 = 1) (hα1 : α ≠ 1) {J : Subgroup (PQuot 3 K)}
    (hJ : GLAPComponent 3 (fixSubgroup α) J) (hJ8 : Nonempty (↥J ≃* ↥(alternatingGroup (Fin 8))))
    (s : TauCeti.SporadicName) (eS : PSimple 3 K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hT : CFSG.Open.IsKGroup (PSimple 3 K)) : False := by
  obtain ⟨hKB, hKM⟩ := kRows_of_isKGroup hT eS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect (PQuot 3 K) := ⟨hq.1⟩
  have hT : CFSG.pPrimeCore 3 (PQuot 3 K) = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  set β : MulAut (PSimple 3 K) := centerQuotientHom (PQuot 3 K) α with hβdef
  have hβ3 : β ^ 3 = 1 := by
    rw [hβdef, ← map_pow, hα3, map_one]
  have hβ1 : β ≠ 1 := by
    intro h
    apply hα1
    exact centerQuotientHom_injective (PQuot 3 K) (h.trans (map_one _).symm)
  set π : PQuot 3 K →* PSimple 3 K := QuotientGroup.mk' (Subgroup.center (PQuot 3 K)) with hπdef
  have hker : π.ker ≤ Subgroup.center (PQuot 3 K) := (QuotientGroup.ker_mk' _).le
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hαβ : ∀ k : PQuot 3 K, π (α k) = centerQuotientHom (PQuot 3 K) α (π k) :=
    fun k => (onCenterQuotient_apply_mk α k).symm
  have hJS : GLAPComponent 3 (fixSubgroup β) (J.map π) :=
    glaPComponent_map_fixSubgroup π hker α β hαβ hπs Nat.prime_three hJ
  obtain ⟨eJ⟩ := hJ8
  have hJA8 : IsAltPType 3 J 8 := isAltPType_of_mulEquiv_alt8 eJ
  have hf : ∀ x : PQuot 3 K, x ∈ J → π x = 1 → x = 1 := by
    intro x hxJ hx1
    have hxZ : x ∈ Subgroup.center (PQuot 3 K) := (QuotientGroup.eq_one_iff x).1 hx1
    obtain ⟨e8⟩ := hJA8
    exact up7a8_central_inj (by norm_num) e8 hT hxJ hxZ
  obtain ⟨φ⟩ := up7a8_pQuot_map_equiv 3 J π hf
  obtain ⟨e8⟩ := hJA8
  have hJSA : IsAltPType 3 (J.map π) 8 := ⟨φ.symm.trans e8⟩
  exact hS (PSimple 3 K) s ⟨eS⟩ hKB hKM β hβ3 hβ1 (J.map π) hJS hJSA

end I2017

variable {G : Type} [Group G] [Finite G]

theorem i2017At_of_lieK (hL : I2017LieAt G) (hS : I1422SporSK) : I2017At G := by
  intro X K D J I R hX hK hDN hD hD9 hdz hE hJLay hJC hJA hIJ hIA hRK hR hIDR hnc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card (p := 3) (n := 2) (by rw [hD9]; norm_num)
  obtain ⟨d, hd, hd1, hdC⟩ := hdz
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  have hIN : I ≤ Subgroup.normalizer (R : Set G) := le_trans le_sup_left hIDR
  have hIRbar : imageMod 3 K I ≤ Subgroup.normalizer (imageMod 3 K R : Set (PQuot 3 K)) :=
    S8.L83.imageMod_le_normalizer hIN
  have hRbar : IsPGroup 2 (imageMod 3 K R) := S8.L83.isPGroup_imageMod hR
  have hIJbar : imageMod 3 K I ≤ imageMod 3 K J := S8.L83.imageMod_mono hIJ
  by_cases hall : ∀ x ∈ D, CentMod 3 K x
  ·
    have hfix1 : ∀ q : PQuot 3 K, barAut 3 K ⟨1, Subgroup.one_mem _⟩ q = q →
        ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDN he⟩ q = q := by
      intro q _ e he
      rw [(barAut_eq_one_iff_centMod (hDN he)).2 (hall e he), MulAut.one_apply]
    have hJt := i2017_component_fix hDN hDp D.one_mem hfix1 hJC
    have h1 : (⟨(1 : G), Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (K : Set G))) = 1 := rfl
    rw [h1, map_one, up7a8_fixSubgroup_one] at hJt
    have hJtop : imageMod 3 K J = ⊤ := top_of_component_top hq hJt
    obtain ⟨eJ⟩ := hJA
    let eK : PQuot 3 K ≃* ↥(alternatingGroup (Fin 8)) :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hJtop).symm.trans eJ)
    have hroot : IsRootAlt eK (⊤ : Subgroup (PQuot 3 K)) 8 := isRootAlt_top (by norm_num) eK
    have hI7 : IsRootAlt eK (imageMod 3 K I) 7 :=
      root7_of_le_root8 eK hroot le_top (by
        obtain ⟨eI⟩ := hIA
        exact ⟨eI⟩)
    exact (hnc (i2013At_holds (PQuot 3 K) 8 7 eK _ (by norm_num) (by norm_num) hI7 _ hRbar hIRbar)).elim
  ·
    push Not at hall
    obtain ⟨x, hx, hxC⟩ := hall
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hDN hx
    have hα3 : (barAut 3 K ⟨x, hxN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have h3 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hD.2 x hx)
      rw [h3, map_one]
    have hα1 : barAut 3 K ⟨x, hxN⟩ ≠ 1 := fun h => hxC ((barAut_eq_one_iff_centMod hxN).1 h)
    have hfixD : ∀ q : PQuot 3 K, barAut 3 K ⟨x, hxN⟩ q = q →
        ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDN he⟩ q = q :=
      fun q hq' e he => fix_all_of_fix_x hDN hD hD9 hd hx hdC hd1 hxC hq' e he
    have hJt := i2017_component_fix hDN hDp hx hfixD hJC
    obtain ⟨eJ⟩ := hJA
    have hJ8 : IsAltPType 3 (imageMod 3 K J) 8 := isAltPType_of_mulEquiv_alt8 eJ
    have hcat : IsCatalogGroup (PSimple 3 K) :=
      CFSG.LocalAnalysis.GLTheoremA.I2611.isCatalogGroup_center_quotient' ((hX.of_le hK.1).quotient _) hq
    obtain ⟨i, ⟨eS⟩⟩ := hcat
    cases i with
    | cyclic r hr =>
      exfalso
      obtain ⟨a, b, hab⟩ := (chev_pSimple_simple_nonabelian Nat.prime_three hK).2
      apply hab
      apply eS.injective
      simp only [map_mul]
      exact mul_comm _ _
    | alternating n hn =>
      have hn8 : 8 ≤ n := eight_le_of_alt8_sub hn ⟨eJ⟩ eS
      obtain ⟨eK⟩ := up7a8_pQuot_alt_of_center hK hn8 eS
      have hroot8 : IsRootAlt eK (imageMod 3 K J) 8 :=
        root8_of_fix_component eK hα3 hJt hJ8
      have hI7 : IsRootAlt eK (imageMod 3 K I) 7 := by
        obtain ⟨eI⟩ := hIA
        exact root7_of_le_root8 eK hroot8 hIJbar ⟨eI⟩
      have hn7 : 7 ≤ n := by omega
      exact (hnc (i2013At_holds (PQuot 3 K) n 7 eK _ (by norm_num) hn7 hI7 _ hRbar hIRbar)).elim
    | sporadic s =>
      exact (I2017.i2017_spor_falseK hS hq hα3 hα1 hJt ⟨eJ⟩ s eS (isKGroup_pSimple hX hK)).elim
    | lie dl =>
      exact hL X K D J I R hX hK hDN hD hD9 ⟨d, hd, hd1, hdC⟩ hE hJLay hJC ⟨eJ⟩ hIJ hIA hRK hR hIDR hnc
        ⟨dl.1.characteristic, up7a8_char_prime dl.1, ⟨TauCeti.CFSGIndex.lie dl, by simp [onLie], ⟨eS⟩⟩⟩

end BMKSporFalseK

end CFSG.LocalAnalysis.GLTheoremA

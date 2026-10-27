module

public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Wreathed.PrimewisePerfectLift
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.LocalAnalysis.GLTheoremA.Basic
public import CFSG.LocalAnalysis.GLTheoremA.S6.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

theorem isCyclic_of_isPGroup_quotient {H : Type} [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    {p : ℕ} [hp : Fact p.Prime] (hN : ¬ p ∣ Nat.card N)
    (hH : ∀ S : Subgroup H, IsPGroup p S → IsCyclic S)
    (S : Subgroup (H ⧸ N)) (hS : IsPGroup p S) : IsCyclic S := by
  classical
  let P : Subgroup H := S.comap (QuotientGroup.mk' N)
  have hNP : N ≤ P := by
    intro n hn
    rw [Subgroup.mem_comap]
    rw [show (QuotientGroup.mk' N) n = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact S.one_mem
  let f : ↥P →* ↥S := ((QuotientGroup.mk' N).comp P.subtype).codRestrict S fun x => x.2
  have hf_surj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N (y : H ⧸ N)
    have hxP : x ∈ P := by
      rw [Subgroup.mem_comap, hx]
      exact y.2
    exact ⟨⟨x, hxP⟩, Subtype.ext hx⟩
  have hf_ker : f.ker = N.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' N (x : H) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).1 h1
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff _).2 hx
  have hPcard : Nat.card ↥P = Nat.card N * Nat.card ↥S := by
    have h := Subgroup.card_ker_mul_card_range f
    rw [hf_ker, MonoidHom.range_eq_top.2 hf_surj, Subgroup.card_top] at h
    rw [← h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
  have hkfac : (Nat.card ↥P).factorization p = k := by
    rw [hPcard, hk, Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero k hp.out.ne_zero)]
    simp [Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN,
      Nat.Prime.factorization_pow hp.out]
  obtain ⟨R⟩ : Nonempty (Sylow p ↥P) := inferInstance
  have hRcard : Nat.card ↥R = p ^ k :=
    (Sylow.card_eq_multiplicity R).trans (by rw [hkfac])
  let R' : Subgroup H := (R : Subgroup ↥P).map P.subtype
  have hR'card : Nat.card R' = p ^ k := by
    change Nat.card ↥(Subgroup.map P.subtype (R : Subgroup ↥P)) = p ^ k
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    change Nat.card ↥R = p ^ k
    exact hRcard
  have hR'p : IsPGroup p R' := IsPGroup.of_card hR'card
  let g : ↥R' →* ↥S :=
    ((QuotientGroup.mk' N).comp R'.subtype).codRestrict S fun x =>
      Subgroup.mem_comap.1 (Subgroup.map_subtype_le (H := P) (R : Subgroup ↥P) x.2)
  have hg_inj : Function.Injective g := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxN : (x : H) ∈ N := by
      have h1 : QuotientGroup.mk' N (x : H) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hxR : (x : H) ∈ R' := x.2
    have hordR : orderOf (x : H) ∣ p ^ k := by
      rw [← hR'card]; exact Subgroup.orderOf_dvd_natCard R' hxR
    have hordN : orderOf (x : H) ∣ Nat.card N :=
      Subgroup.orderOf_dvd_natCard N hxN
    have hcop : Nat.Coprime (p ^ k) (Nat.card N) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
    have h1 : orderOf (x : H) = 1 := Nat.eq_one_of_dvd_coprimes hcop hordR hordN
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.1 ((Subgroup.orderOf_coe x).symm.trans h1)
  have hg_ker : g.ker = ⊥ := (MonoidHom.ker_eq_bot_iff g).mpr hg_inj
  have hg_card : Nat.card ↥g.range = Nat.card ↥R' := by
    have h := Subgroup.card_ker_mul_card_range g
    rw [hg_ker, Subgroup.card_bot, one_mul] at h
    exact h
  have hg_surj : Function.Surjective g := by
    have htop : g.range = ⊤ := by
      refine Subgroup.eq_top_of_card_eq g.range ?_
      calc Nat.card ↥g.range = Nat.card ↥R' := hg_card
        _ = p ^ k := hR'card
        _ = Nat.card ↥S := hk.symm
    exact MonoidHom.range_eq_top.1 htop
  haveI : IsCyclic ↥R' := hH R' hR'p
  exact isCyclic_of_surjective g hg_surj


theorem not_three_dvd_card_subgroupOf_centralizer {Ω : Type} [Group Ω] {L : Subgroup Ω}
    (hnoZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) :
    ¬ 3 ∣ Nat.card ↥((L ⊓ Subgroup.centralizer (L : Set Ω)).subgroupOf
      (Subgroup.centralizer (L : Set Ω))) := by
  have hLC : L ⊓ Subgroup.centralizer (L : Set Ω) =
      (Subgroup.center ↥L).map L.subtype :=
    CFSG.GroupTheory.inf_centralizer_eq_map_center L
  have hcard : Nat.card ↥((L ⊓ Subgroup.centralizer (L : Set Ω)).subgroupOf
      (Subgroup.centralizer (L : Set Ω))) = Nat.card (Subgroup.center ↥L) :=
    Nat.card_congr ((Subgroup.subgroupOfEquivOfLe
      (inf_le_right : L ⊓ Subgroup.centralizer (L : Set Ω) ≤
        Subgroup.centralizer (L : Set Ω))).trans
      ((MulEquiv.subgroupCongr hLC).trans
        (Subgroup.equivMapOfInjective (Subgroup.center ↥L) L.subtype
          L.subtype_injective).symm)).toEquiv
  rwa [hcard]

theorem isDirectZpowersInf_of_le_sup_centralizer {Ω : Type} [Group Ω] [Finite Ω]
    {L B : Subgroup Ω} {x : Ω} (hLn : L.Normal) (hB : IsElemAbelian 3 B) (hxB : x ∈ B)
    (hx1 : x ≠ 1) (hxL : L ≤ Subgroup.centralizer ({x} : Set Ω))
    (hBL : B ≤ L ⊔ Subgroup.centralizer (L : Set Ω))
    (hcent : ∀ b ∈ B, b ∈ Subgroup.centralizer (L : Set Ω) ↔ b ∈ Subgroup.zpowers x)
    (hnoZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L))
    (hcyc : ∀ S : Subgroup Ω, S ≤ Subgroup.centralizer (L : Set Ω) → IsPGroup 3 S → IsCyclic S) :
    IsDirectZpowersInf B x L := by
  classical
  haveI := hLn
  let C : Subgroup Ω := Subgroup.centralizer (L : Set Ω)
  have hxL' : x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.1 (hxL hl)
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hxnc : x ∉ L := by
    intro hxmem
    have hxcenter : (⟨x, hxmem⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 hxL' (g : Ω) g.2
    have hdvd : 3 ∣ Nat.card (Subgroup.center ↥L) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hxcenter
      rw [Subgroup.orderOf_mk, orderOf_eq_prime hx3 hx1] at h
      exact h
    exact hnoZ hdvd
  have hBsup : B ≤ C ⊔ L := by
    rw [sup_comm]
    exact hBL
  let e : ↥C ⧸ (L.subgroupOf C) ≃* ↥(C ⊔ L) ⧸ (L.subgroupOf (C ⊔ L)) :=
    QuotientGroup.quotientInfEquivProdNormalQuotient (G := Ω) C L
  let q : ↥B →* ↥(C ⊔ L) ⧸ (L.subgroupOf (C ⊔ L)) :=
    (QuotientGroup.mk' (L.subgroupOf (C ⊔ L))).comp
      (Subgroup.inclusion hBsup : ↥B →* ↥(C ⊔ L))
  let φ : ↥B →* ↥C ⧸ (L.subgroupOf C) := e.symm.toMonoidHom.comp q
  have hφker : φ.ker = (B ⊓ L).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : φ b = 1 ↔ q b = 1 := by
      constructor
      · intro h
        apply e.symm.injective
        simpa [φ] using h
      · intro h
        show e.symm.toMonoidHom (q b) = 1
        rw [h, map_one]
    rw [h1]
    show (QuotientGroup.mk' (L.subgroupOf (C ⊔ L))) (Subgroup.inclusion hBsup b) = 1 ↔
      (b : Ω) ∈ B ⊓ L
    constructor
    · intro h
      have hL : (Subgroup.inclusion hBsup b : ↥(C ⊔ L)) ∈ L.subgroupOf (C ⊔ L) :=
        (QuotientGroup.eq_one_iff _).1 h
      exact ⟨b.2, Subgroup.mem_subgroupOf.1 hL⟩
    · rintro ⟨-, hL⟩
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hL)
  have hBtop : IsElemAbelian 3 (⊤ : Subgroup ↥B) := by
    haveI : IsMulCommutative ↥B := hB.1
    refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm' (a : ↥B) (b : ↥B))⟩⟩, fun a _ => ?_⟩
    exact Subtype.ext (by simpa using hB.2 (a : ↥B) a.2)
  have hφrange_el : IsElemAbelian 3 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact hBtop.map φ
  have hN3 : ¬ 3 ∣ Nat.card ↥(L.subgroupOf C) := by
    have h := not_three_dvd_card_subgroupOf_centralizer (Ω := Ω) (L := L) hnoZ
    simpa [C] using h
  have hcycC : ∀ S : Subgroup C, IsPGroup 3 S → IsCyclic S := by
    intro S hS
    have h1 := hcyc (S.map C.subtype) (Subgroup.map_subtype_le (H := C) S)
      (hS.map C.subtype)
    exact (Subgroup.equivMapOfInjective S C.subtype C.subtype_injective).isCyclic.mpr h1
  have hφp : IsPGroup 3 φ.range := isPGroup_of_isElemAbelian hφrange_el
  have hφcyc : IsCyclic φ.range := isCyclic_of_isPGroup_quotient hN3 hcycC φ.range hφp
  have hAcyc : IsCyclic (↥B ⧸ (B ⊓ L).subgroupOf B) := by
    have e1 : (↥B ⧸ (B ⊓ L).subgroupOf B) ≃* φ.range :=
      (QuotientGroup.quotientMulEquivOfEq hφker).symm.trans
        (QuotientGroup.quotientKerEquivRange φ)
    exact e1.isCyclic.mpr hφcyc
  have hQel : IsElemAbelian 3 (⊤ : Subgroup (↥B ⧸ (B ⊓ L).subgroupOf B)) := by
    have hmap := hBtop.map (QuotientGroup.mk' ((B ⊓ L : Subgroup Ω).subgroupOf B))
    rw [← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective ((B ⊓ L : Subgroup Ω).subgroupOf B))] at hmap
    exact hmap
  have hQcard : Nat.card (↥B ⧸ (B ⊓ L).subgroupOf B) ≤ 3 := by
    obtain ⟨g, hg⟩ := hAcyc.exists_generator
    have hg3 : g ^ 3 = 1 := hQel.2 g (Subgroup.mem_top g)
    have hord : orderOf g ≤ 3 := by
      have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
      have := Nat.le_of_dvd (by norm_num) hdvd
      exact this
    have htop : (⊤ : Subgroup (↥B ⧸ (B ⊓ L).subgroupOf B)) = Subgroup.zpowers g :=
      le_antisymm (fun x _ => hg x) le_top
    have hcard : Nat.card (↥B ⧸ (B ⊓ L).subgroupOf B) = orderOf g := by
      rw [← Nat.card_zpowers, ← htop, Subgroup.card_top]
    rw [hcard]; exact hord
  have hcardBL : Nat.card ↥((B ⊓ L : Subgroup Ω).subgroupOf B) = Nat.card (B ⊓ L : Subgroup Ω) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : B ⊓ L ≤ B)).toEquiv
  have hBcard : Nat.card B ≤ 3 * Nat.card (B ⊓ L : Subgroup Ω) := by
    have h := Subgroup.card_ker_mul_card_range (QuotientGroup.mk' ((B ⊓ L : Subgroup Ω).subgroupOf B))
    rw [QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.2 (QuotientGroup.mk'_surjective ((B ⊓ L : Subgroup Ω).subgroupOf B)),
      Subgroup.card_top] at h
    calc Nat.card B = Nat.card ↥((B ⊓ L : Subgroup Ω).subgroupOf B) *
          Nat.card (↥B ⧸ (B ⊓ L).subgroupOf B) := h.symm
      _ ≤ Nat.card (B ⊓ L : Subgroup Ω) * 3 :=
        Nat.mul_le_mul (le_of_eq hcardBL) hQcard
      _ = 3 * Nat.card (B ⊓ L : Subgroup Ω) := by ring
  have hdisj : Subgroup.zpowers x ⊓ (B ⊓ L) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzx, hzBL⟩
    rw [Subgroup.mem_bot]
    have hzC : z ∈ C := (Subgroup.zpowers_le.2 hxL') hzx
    have hzcenter : (⟨z, hzBL.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_centralizer_iff.1 hzC (g : Ω) g.2
    have hz3 : z ^ 3 = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hzx
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx3,
        one_zpow]
    have hzord : orderOf (⟨z, hzBL.2⟩ : ↥L) ∣ 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_dvd_of_pow_eq_one hz3
    have hzc : orderOf (⟨z, hzBL.2⟩ : ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hzcenter
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnoZ
    have h1 : orderOf (⟨z, hzBL.2⟩ : ↥L) = 1 := Nat.eq_one_of_dvd_coprimes hcop hzord hzc
    have hz1 : (⟨z, hzBL.2⟩ : ↥L) = 1 := orderOf_eq_one_iff.1 h1
    exact Subtype.ext_iff.1 hz1
  have hnorm : (B ⊓ L) ≤ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup Ω) : Set Ω) := by
    intro b hb
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz => ?_)
    exact isElemAbelian_commute hB ((Subgroup.zpowers_le.2 hxB) hz) hb.1
  have hsupcard : Nat.card (Subgroup.zpowers x ⊔ (B ⊓ L : Subgroup Ω) : Subgroup Ω) =
      3 * Nat.card (B ⊓ L : Subgroup Ω) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (Subgroup.zpowers x : Subgroup Ω) (B ⊓ L : Subgroup Ω) hnorm
      (disjoint_iff.mpr hdisj), Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hle : (Subgroup.zpowers x ⊔ (B ⊓ L : Subgroup Ω) : Subgroup Ω) ≤ B :=
    sup_le (Subgroup.zpowers_le.2 hxB) inf_le_left
  refine ⟨?_, hdisj⟩
  have hBle : Nat.card B ≤ Nat.card (Subgroup.zpowers x ⊔ (B ⊓ L : Subgroup Ω) : Subgroup Ω) := by
    rw [hsupcard]; exact hBcard
  exact (Subgroup.eq_of_le_of_card_ge hle hBle).symm

end CFSG.LocalAnalysis.GLTheoremA.T171S

end

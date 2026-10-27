module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.PlaneInT
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoBalance
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.PointConfigCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Endgame
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.KFactDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Lemma42Generic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3ZT u3U0 U3LineWC KFactWeakClosureHeis
  GenericComponentClass u3_endgame card_inf_centralizer_of_nonabelian_card_p_cube
  exists_isElemAbelian_card_sq_of_nonabelian)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

theorem typeII_aut_pgroup_card_dvd [Fact p.Prime] {K : Type} [Group K] [Finite K]
    (hK : SylowIsHeisenberg p K) (hno : NoOuterP p K) (hz : Subgroup.center K = ⊥)
    (S : Subgroup (MulAut K)) (hS : IsPGroup p S) : Nat.card S ∣ p ^ 3 := by
  classical
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  let π : MulAut K →* Outer K := QuotientGroup.mk' _
  have hSπ : IsPGroup p (S.map π) := hS.map π
  have hSle : S ≤ (MulAut.conj : K →* MulAut K).range := by
    have h1 : S.map π = ⊥ := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hSπ
      have hdvd : Nat.card (S.map π) ∣ Nat.card (Outer K) := Subgroup.card_subgroup_dvd_card _
      by_cases hn0 : n = 0
      · rw [hn0, pow_zero] at hn
        exact Subgroup.eq_bot_of_card_eq _ hn
      · exfalso
        apply hno
        rw [hn] at hdvd
        exact (dvd_pow_self p hn0).trans hdvd
    intro g hg
    have h2 : π g ∈ S.map π := ⟨g, hg, rfl⟩
    rw [h1, Subgroup.mem_bot] at h2
    exact (QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner K) g).mp h2
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : g ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut K => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.mp h3).symm
    rw [hz, Subgroup.mem_bot] at hg'
    exact hg'
  set H : Subgroup K := S.comap (MulAut.conj : K →* MulAut K) with hH
  have hmap : H.map (MulAut.conj : K →* MulAut K) = S :=
    Subgroup.map_comap_eq_self hSle
  have hcardH : Nat.card S = Nat.card H := by
    have h4 := Subgroup.card_map_of_injective (K := H) hinj
    rwa [hmap] at h4
  have hHp : IsPGroup p H := hS.comap_of_injective (MulAut.conj : K →* MulAut K) hinj
  obtain ⟨Sy, hSy⟩ := hHp.exists_le_sylow
  have h5 : Nat.card H ∣ Nat.card (Sy : Subgroup K) := Subgroup.card_dvd_of_le hSy
  rw [(hK Sy).1] at h5
  rw [hcardH]
  exact h5

theorem typeII_aut_pgroup_card_dvd_of_equiv [Fact p.Prime] {K L : Type} [Group K] [Finite K] [Group L]
    (e : L ≃* K) (hK : SylowIsHeisenberg p K) (hno : NoOuterP p K) (hz : Subgroup.center K = ⊥)
    (S : Subgroup (MulAut L)) (hS : IsPGroup p S) : Nat.card S ∣ p ^ 3 := by
  let φ : MulAut L ≃* MulAut K := MulAut.congr e
  have h1 : IsPGroup p (S.map φ.toMonoidHom) := hS.map φ.toMonoidHom
  have h2 := typeII_aut_pgroup_card_dvd hK hno hz _ h1
  rwa [Subgroup.card_map_of_injective φ.injective] at h2

private theorem typeII_struct_add_le_pRank {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] [Finite G]
    {E₁ E₂ H : Subgroup G} (hE₁ : IsElemAbelian p E₁) (hE₂ : IsElemAbelian p E₂) {r₁ r₂ : ℕ}
    (h₁ : Nat.card E₁ = p ^ r₁) (h₂ : Nat.card E₂ = p ^ r₂)
    (hc : ∀ x ∈ E₁, ∀ y ∈ E₂, Commute x y) (hdisj : E₁ ⊓ E₂ = ⊥)
    (h₁H : E₁ ≤ H) (h₂H : E₂ ≤ H) : r₁ + r₂ ≤ CFSG.Open.pRank p H := by
  let f : E₁ × E₂ →* G := MonoidHom.noncommCoprod E₁.subtype E₂.subtype
    (fun x y => hc x x.2 y y.2)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h : (x : G) * y = 1 := hxy
    have hx : (x : G) ∈ E₁ ⊓ E₂ := Subgroup.mem_inf.2 ⟨x.2, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact E₂.inv_mem y.2⟩
    rw [hdisj, Subgroup.mem_bot] at hx
    have hy : (y : G) = 1 := by rw [hx, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hx, Subtype.ext hy⟩
  have hc₁ := hE₁.1
  have hc₂ := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (A := E₁ × E₂) ?_ ?_ ?_ f hf ?_
  · rintro ⟨a, b⟩ ⟨c, d⟩
    exact Prod.ext (mul_comm' a c) (mul_comm' b d)
  · rintro ⟨a, b⟩
    exact Prod.ext (Subtype.ext (hE₁.2 a a.2)) (Subtype.ext (hE₂.2 b b.2))
  · rw [Nat.card_prod, h₁, h₂, pow_add]
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    exact H.mul_mem (h₁H a.2) (h₂H b.2)

theorem typeII_T_structure (hX : ExtraFacts Typ p Shape) (hc : PointConfig Typ G p P M x J) :
    Nat.card (u3T P x J) = p ^ 3 ∧ (∀ t ∈ u3T P x J, t ^ p = 1) ∧
      ¬ IsMulCommutative (u3T P x J) ∧ x ∉ J := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hc.le_cent
  have hCJ : C ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  set O : Subgroup G := rankThreePrimeCore p J with hO
  have hOJ : O ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOcop : p.Coprime (Nat.card O) := CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hOcop' : ¬ p ∣ Nat.card O := (hp.coprime_iff_not_dvd).mp hOcop
  have hkcop : ¬ p ∣ Nat.card ψ.ker := by
    rw [hker]
    have : Nat.card (O.subgroupOf J) = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOJ).toEquiv
    rw [this]
    exact hOcop'
  have hZ : Subgroup.center Q = ⊥ :=
    u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  have hSylJ : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hJC hCJ
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ
  set T0 : Subgroup J := (Tsyl : Subgroup J) with hT0
  have hTinj : ∀ t ∈ T0, ψ t = 1 → t = 1 := u3main_eq_one_of_ker ψ hkcop Tsyl.isPGroup'
  let Tsyl' : Sylow p Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = T0.map ψ := Sylow.coe_mapSurjective hψ Tsyl
  obtain ⟨hcard, hnab', hexp⟩ := hX.sylow Q hQ Tsyl'
  have hnab : ¬ IsMulCommutative (Tsyl' : Subgroup Q) := by
    intro hcomm
    obtain ⟨a, ha, b, hb, hab⟩ := hnab'
    exact hab (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  rw [hTsyl'] at hcard hexp hnab
  have hinjT0 : Function.Injective (ψ.comp T0.subtype) :=
    (injective_iff_map_eq_one _).mpr fun a ha => Subtype.ext (hTinj a a.2 ha)
  have hmapcard : Nat.card (T0.map ψ) = Nat.card T0 := by
    have e1 : (ψ.comp T0.subtype).range = T0.map ψ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinjT0).toEquiv]
  have hTcard : Nat.card (u3T P x J) = Nat.card T0 := by
    rw [← hTsyl, Subgroup.card_map_of_injective J.subtype_injective]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hTcard, ← hmapcard]
    exact hcard
  · intro t ht
    rw [← hTsyl] at ht
    obtain ⟨t0, ht0, rfl⟩ := ht
    have h1 : (ψ t0) ^ p = 1 := hexp _ ⟨t0, ht0, rfl⟩
    have h2 : t0 ^ p = 1 := by
      apply hTinj _ (T0.pow_mem ht0 p)
      rw [map_pow]
      exact h1
    show ((t0 : J) : G) ^ p = 1
    rw [← Subgroup.coe_pow, h2]
    rfl
  · intro hcomm
    apply hnab
    have hc0 : IsMulCommutative T0 := by
      refine ⟨⟨fun a b => ?_⟩⟩
      have := hcomm.is_comm.comm ⟨(a : J), by rw [← hTsyl]; exact ⟨a, a.2, rfl⟩⟩
        ⟨(b : J), by rw [← hTsyl]; exact ⟨b, b.2, rfl⟩⟩
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : u3T P x J => (z : G)) this
    infer_instance
  · exact u3main_not_mem hc.generic.2.1.2.1 hc.generic.2.1.2.2.1 hJC hOcop' ψ hψ hker hZ

theorem typeII_S_decomp (hX : ExtraFacts Typ p Shape) (hc : PointConfig Typ G p P M x J) :
    ∃ Z : Subgroup G, IsCyclic Z ∧ x ∈ Z ∧ Z ≤ u3S P x ∧
      (∀ z ∈ Z, ∀ t ∈ u3T P x J, z * t = t * z) ∧ u3T P x J ⊓ Z = ⊥ ∧
      u3T P x J ⊔ Z = u3S P x := by
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := typeII_T_structure hX hc
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 := hc.five
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Q, hQg, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hC
  have hJC : J ≤ C := hc.le_cent
  have hCJ : C ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  set O : Subgroup G := rankThreePrimeCore p J with hO
  have hOJ : O ≤ J := CFSG.AGLEmbedding.glbPrimeCore_le p J
  have hOC : O ≤ C := hOJ.trans hJC
  have hOcop : p.Coprime (Nat.card O) := CFSG.AGLEmbedding.glbPrimeCore_coprime p J
  have hOnorm : C ≤ Subgroup.normalizer (O : Set G) := by
    intro g hg
    have hgJ : J.map (MulAut.conj g).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCJ hg)
    have h1 := glbPrimeCore_map_automorphism p J (MulAut.conj g)
    rw [hgJ] at h1
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  let O' : Subgroup C := O.subgroupOf C
  haveI hO'n : O'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOC).mpr hOnorm
  let π : C →* C ⧸ O' := QuotientGroup.mk' O'
  let J' : Subgroup C := J.subgroupOf C
  haveI hJ'n : J'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJC).mpr hCJ
  let L : Subgroup (C ⧸ O') := J'.map π
  haveI hLn : L.Normal := Subgroup.Normal.map hJ'n π (QuotientGroup.mk'_surjective O')
  let eJ : J' ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  let ψ' : J' →* Q := ψ.comp eJ.toMonoidHom
  have hψ' : Function.Surjective ψ' := hψ.comp eJ.surjective
  let πJ : J' →* L := (π.comp J'.subtype).codRestrict L (fun j => Subgroup.mem_map_of_mem π j.2)
  have hπJ : Function.Surjective πJ := by
    rintro ⟨_, j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩
  have hkerEq : ψ'.ker = πJ.ker := by
    ext j
    have h1 : ψ' j = 1 ↔ ((j : C) : G) ∈ O := by
      have h : ψ (eJ j) = 1 ↔ eJ j ∈ ψ.ker := MonoidHom.mem_ker.symm
      rw [show ψ' j = ψ (eJ j) from rfl, h, hker, Subgroup.mem_subgroupOf]
      rfl
    have h2 : πJ j = 1 ↔ ((j : C) : G) ∈ O := by
      constructor
      · intro h
        have h' : π (j : C) = 1 := congrArg Subtype.val h
        exact (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (j : C)).mp h'))
      · intro h
        apply Subtype.ext
        exact (QuotientGroup.eq_one_iff (j : C)).mpr (Subgroup.mem_subgroupOf.mpr h)
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, h1, h2]
  let eL : L ≃* Q :=
    (QuotientGroup.quotientKerEquivOfSurjective πJ hπJ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkerEq.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ'))
  have hQZ : Subgroup.center Q = ⊥ :=
    u3main_center_bot hOJ hc.perfect hc.lt hc.minimal ψ hψ hker
  have hLZ : ∀ l : L, (∀ m : L, m * l = l * m) → l = 1 := by
    intro l hl
    have : eL l ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := eL.surjective q
      rw [← map_mul, ← map_mul, hl m]
    rw [hQZ, Subgroup.mem_bot] at this
    exact eL.injective (this.trans (map_one eL).symm)
  let χ : C →* MulAut L := (MulAut.conjNormal (H := L)).comp π
  have hχapp : ∀ (c : C) (l : L), ((χ c l : L) : C ⧸ O') = π c * (l : C ⧸ O') * (π c)⁻¹ := by
    intro c l
    exact MulAut.conjNormal_apply (π c) l
  have hPO : (P : Subgroup G) ⊓ O = ⊥ := by
    have hPp : IsPGroup p ↥((P : Subgroup G) ⊓ O) := P.isPGroup'.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    have hdvd : Nat.card ((P : Subgroup G) ⊓ O : Subgroup G) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_right
    have hk0 : k = 0 := by
      by_contra hk0
      have : p ∣ Nat.card O := (dvd_pow_self p hk0).trans (hk ▸ hdvd)
      exact (hp.coprime_iff_not_dvd.mp hOcop) this
    rw [hk0, pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  let S' : Subgroup C := (P : Subgroup G).subgroupOf C
  let T' : Subgroup C := (u3T P x J).subgroupOf C
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTP : u3T P x J ≤ (P : Subgroup G) := (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_left
  have hTC : u3T P x J ≤ C := hTJ.trans hJC
  have hT'S' : T' ≤ S' := fun t ht => hTP ht
  have hχT : ∀ t : C, t ∈ T' → χ t = 1 → t = 1 := by
    intro t ht h1
    have htT : (t : G) ∈ u3T P x J := ht
    have htJ' : t ∈ J' := hTJ htT
    have hl : π t ∈ L := Subgroup.mem_map_of_mem π htJ'
    have hcomm : ∀ m : L, m * (⟨π t, hl⟩ : L) = ⟨π t, hl⟩ * m := by
      intro m
      apply Subtype.ext
      have h2 := congrArg (fun φ : MulAut L => ((φ m : L) : C ⧸ O')) h1
      simp only [hχapp, MulAut.one_apply] at h2
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have h3 : (⟨π t, hl⟩ : L) = 1 := hLZ _ hcomm
    have h4 : π t = 1 := congrArg Subtype.val h3
    have h5 : (t : G) ∈ O := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff t).mp h4)
    have h6 : (t : G) ∈ (P : Subgroup G) ⊓ O := ⟨hTP htT, h5⟩
    rw [hPO, Subgroup.mem_bot] at h6
    exact Subtype.ext h6
  have hT'card : Nat.card T' = p ^ 3 := by
    rw [show Nat.card T' = Nat.card (u3T P x J) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv, hTcard]
  have hinjχ : Function.Injective (χ.comp T'.subtype) :=
    (injective_iff_map_eq_one _).mpr fun a ha => Subtype.ext (hχT a a.2 ha)
  have hmapT' : Nat.card (T'.map χ) = p ^ 3 := by
    have e1 : (χ.comp T'.subtype).range = T'.map χ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← e1, ← Nat.card_congr (MonoidHom.ofInjective hinjχ).toEquiv, hT'card]
  have hSp : IsPGroup p S' := P.isPGroup'.comap_subtype
  have hdvdA : Nat.card (S'.map χ) ∣ p ^ 3 :=
    typeII_aut_pgroup_card_dvd_of_equiv eL (hX.sylow Q hQ) (hX.noOuter Q hQ) hQZ (S'.map χ)
      (hSp.map χ)
  have hAeq : T'.map χ = S'.map χ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hT'S')
      (by rw [hmapT']; exact Nat.le_of_dvd (pow_pos hp.pos 3) hdvdA)
  let Z : Subgroup G := (S' ⊓ χ.ker).map C.subtype
  have hZmem : ∀ z : G, z ∈ Z ↔ ∃ hzC : z ∈ C, z ∈ (P : Subgroup G) ∧ χ ⟨z, hzC⟩ = 1 := by
    intro z
    constructor
    · rintro ⟨c, ⟨hcS, hcker⟩, rfl⟩
      exact ⟨c.2, hcS, hcker⟩
    · rintro ⟨hzC, hzP, hz1⟩
      exact ⟨⟨z, hzC⟩, ⟨hzP, hz1⟩, rfl⟩
  have hZS : Z ≤ u3S P x := fun z hz => by
    obtain ⟨hzC, hzP, -⟩ := (hZmem z).mp hz
    exact ⟨hzP, hzC⟩
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxZ : x ∈ Z := by
    refine (hZmem x).mpr ⟨hxC, hc.generic.1, ?_⟩
    ext l
    rw [hχapp, MulAut.one_apply]
    obtain ⟨c, hcl⟩ := QuotientGroup.mk'_surjective O' (l : C ⧸ O')
    rw [← hcl, ← map_mul, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    have h1 : (c : G) * x = x * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp c.2
    show x * (c : G) * x⁻¹ = c
    rw [← h1, mul_inv_cancel_right]
  have hZT : ∀ z ∈ Z, ∀ t ∈ u3T P x J, z * t = t * z := by
    intro z hz t ht
    obtain ⟨hzC, hzP, hz1⟩ := (hZmem z).mp hz
    have htC : t ∈ C := hTC ht
    have hl : π ⟨t, htC⟩ ∈ L :=
      Subgroup.mem_map_of_mem π (show (⟨t, htC⟩ : C) ∈ J' from hTJ ht)
    have h1 : π ⟨z, hzC⟩ * π ⟨t, htC⟩ = π ⟨t, htC⟩ * π ⟨z, hzC⟩ := by
      have h2 := congrArg (fun φ : MulAut L => ((φ ⟨π ⟨t, htC⟩, hl⟩ : L) : C ⧸ O')) hz1
      simp only [hχapp, MulAut.one_apply] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
    have h2 : π (⟨z, hzC⟩ * ⟨t, htC⟩) = π (⟨t, htC⟩ * ⟨z, hzC⟩) := by
      rw [map_mul, map_mul, h1]
    have h3 := (QuotientGroup.eq (s := O')).mp h2
    have h4 : (z * t)⁻¹ * (t * z) ∈ O := Subgroup.mem_subgroupOf.mp h3
    have h5 : (z * t)⁻¹ * (t * z) ∈ (P : Subgroup G) :=
      mul_mem (inv_mem (mul_mem hzP (hTP ht))) (mul_mem (hTP ht) hzP)
    have h6 : (z * t)⁻¹ * (t * z) ∈ (P : Subgroup G) ⊓ O := ⟨h5, h4⟩
    rw [hPO, Subgroup.mem_bot, inv_mul_eq_one] at h6
    exact h6
  have hTZ : u3T P x J ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hgC, hgP, hg1⟩ := (hZmem g).mp hg.2
    have : (⟨g, hgC⟩ : C) = 1 := hχT _ (show (⟨g, hgC⟩ : C) ∈ T' from hg.1) hg1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hsup : u3T P x J ⊔ Z = u3S P x := by
    apply le_antisymm
    · exact sup_le inf_le_left hZS
    · intro s hs
      have hsC : s ∈ C := hs.2
      have hsS' : (⟨s, hsC⟩ : C) ∈ S' := hs.1
      have hmem : χ ⟨s, hsC⟩ ∈ T'.map χ := by
        rw [hAeq]
        exact Subgroup.mem_map_of_mem χ hsS'
      obtain ⟨t, htT', htχ⟩ := hmem
      have htT : (t : G) ∈ u3T P x J := htT'
      have hz : ((t⁻¹ * ⟨s, hsC⟩ : C) : G) ∈ Z := by
        rw [hZmem]
        refine ⟨(t⁻¹ * ⟨s, hsC⟩).2, ?_, ?_⟩
        · rw [Subgroup.coe_mul, Subgroup.coe_inv]
          exact mul_mem (inv_mem (hTP htT)) hs.1
        · show χ (t⁻¹ * ⟨s, hsC⟩) = 1
          rw [map_mul, map_inv, htχ, inv_mul_cancel]
      have hs' : s = (t : G) * ((t⁻¹ * ⟨s, hsC⟩ : C) : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
      rw [hs']
      exact Subgroup.mul_mem_sup htT hz
  have hZp : IsPGroup p ↥Z := P.isPGroup'.to_le (fun z hz => ((hZmem z).mp hz).2.1)
  have hZcyc : IsCyclic Z := by
    by_contra hnc
    haveI : Fact (IsPGroup p ↥Z) := ⟨hZp⟩
    obtain ⟨E, -, hEcard, hEel⟩ := CFSG.lemma_4_5_a hp2 hnc
    haveI : CFSG.IsElementaryAbelian p (E.map Z.subtype) := CFSG.IsElementaryAbelian.map_subtype
    set E' : Subgroup G := E.map Z.subtype with hE'
    have hE'card : Nat.card E' = p ^ 2 := by
      rw [hE', Subgroup.card_map_of_injective Z.subtype_injective, hEcard]
    have hE'elem : IsElemAbelian p E' :=
      ⟨inferInstance, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
    have hE'Z : E' ≤ Z := by
      rintro _ ⟨e', -, rfl⟩
      exact e'.2
    obtain ⟨ET, hETT, hETel, hETcard, -⟩ :=
      exists_isElemAbelian_card_sq_of_nonabelian hTcard hTexp hTnab
    have hcomm : ∀ a ∈ ET, ∀ b ∈ E', Commute a b := fun a ha b hb =>
      (hZT b (hE'Z hb) a (hETT ha)).symm
    have hdisj : ET ⊓ E' = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have : g ∈ u3T P x J ⊓ Z := ⟨hETT hg.1, hE'Z hg.2⟩
      rwa [hTZ] at this
    have hST : u3T P x J ≤ u3S P x := inf_le_left
    have h4 := typeII_struct_add_le_pRank hp hETel hE'elem hETcard hE'card hcomm hdisj
      (H := u3S P x) (hETT.trans hST) (hE'Z.trans hZS)
    have h3 : CFSG.Open.pRank p (u3S P x) = 3 := hc.generic.2.2.2
    omega
  exact ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩

theorem typeII_U0_facts (hX : ExtraFacts Typ p Shape) (hc : PointConfig Typ G p P M x J) :
    IsElemAbelian p (u3U0 P x J) ∧ Nat.card (u3U0 P x J) = p ^ 2 ∧ u3U0 P x J ≤ u3S P x ∧
      x ∈ u3U0 P x J ∧ (∀ s ∈ u3S P x, ∀ u ∈ u3U0 P x J, s * u = u * s) ∧
      Nat.card (u3ZT P x J) = p ∧ u3ZT P x J ≤ J := by
  obtain ⟨hTcard, hTexp, hTnab, hxJ⟩ := typeII_T_structure hX hc
  obtain ⟨Z, hZcyc, hxZ, hZS, hZT, hTZ, hsup⟩ := typeII_S_decomp hX hc
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hx1 : x ≠ 1 := hc.generic.2.1.2.1
  have hxp : x ^ p = 1 := hc.generic.2.1.2.2.1
  have hZTcard : Nat.card (u3ZT P x J) = p :=
    card_inf_centralizer_of_nonabelian_card_p_cube hTcard hTnab
  have hZT_T : u3ZT P x J ≤ u3T P x J := inf_le_left
  have hT_S : u3T P x J ≤ u3S P x := inf_le_left
  have hZT_J : u3ZT P x J ≤ J := hZT_T.trans inf_le_right
  have hZT_S : u3ZT P x J ≤ u3S P x := hZT_T.trans hT_S
  have hxS : x ∈ u3S P x := ⟨hc.generic.1, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hSx : ∀ s ∈ u3S P x, s * x = x * s := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mp hs.2
  have hSz : ∀ z ∈ u3ZT P x J, ∀ s ∈ u3S P x, s * z = z * s := by
    intro z hz s hs
    have hzC : z ∈ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G) := hz.2
    have hzT : z ∈ u3T P x J := hz.1
    have hle : u3S P x ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [← hsup]
      refine sup_le (fun t ht => ?_) (fun c hc' => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (Subgroup.mem_centralizer_iff.mp hzC t ht).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact (hZT c hc' z hzT).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hs) z rfl).symm
  have hU0S : u3U0 P x J ≤ u3S P x :=
    sup_le hZT_S (Subgroup.zpowers_le.mpr hxS)
  have hcentral : ∀ s ∈ u3S P x, ∀ u ∈ u3U0 P x J, s * u = u * s := by
    intro s hs u hu
    have hle : u3U0 P x J ≤ Subgroup.centralizer ({s} : Set G) := by
      refine sup_le (fun z hz => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hSz z hz s hs
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hSx s hs
    exact Subgroup.mem_centralizer_iff.mp (hle hu) s rfl
  have hxcard : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
  have hdisj : u3ZT P x J ⊓ Subgroup.zpowers x = ⊥ := by
    have hdvd : Nat.card (u3ZT P x J ⊓ Subgroup.zpowers x : Subgroup G) ∣ p := by
      have := Subgroup.card_dvd_of_le
        (inf_le_right : u3ZT P x J ⊓ Subgroup.zpowers x ≤ Subgroup.zpowers x)
      rwa [hxcard] at this
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hpp
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : u3ZT P x J ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hxcard, hpp])
      have hxmem : x ∈ u3ZT P x J ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxJ (hZT_J hxmem.1)
  have hcomm : ∀ (a : u3ZT P x J) (b : Subgroup.zpowers x),
      Commute ((u3ZT P x J).subtype a) ((Subgroup.zpowers x).subtype b) := by
    intro a b
    have haS : (a : G) ∈ u3S P x := hZT_S a.2
    have hle : Subgroup.zpowers x ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hSx a haS
    exact (Subgroup.mem_centralizer_iff.mp (hle b.2) a rfl)
  let f : (u3ZT P x J) × (Subgroup.zpowers x) →* G :=
    MonoidHom.noncommCoprod (u3ZT P x J).subtype (Subgroup.zpowers x).subtype hcomm
  have hrange : f.range = u3U0 P x J := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
    rfl
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have h : (a : G) * b = 1 := hab
    have hmem : (a : G) ∈ u3ZT P x J ⊓ Subgroup.zpowers x :=
      ⟨a.2, by
        rw [eq_inv_of_mul_eq_one_left h]
        exact Subgroup.inv_mem _ b.2⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    have hb : (b : G) = 1 := by rw [hmem, one_mul] at h; exact h
    rw [Subgroup.mem_bot, Prod.mk_eq_one]
    exact ⟨Subtype.ext hmem, Subtype.ext hb⟩
  have hcardU0 : Nat.card (u3U0 P x J) = p ^ 2 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, Nat.card_prod, hZTcard,
      hxcard, sq]
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hcentral a (hU0S a.2) b b.2)⟩⟩, ?_⟩, hcardU0, hU0S,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x), hcentral, hZTcard, hZT_J⟩
  intro u hu
  rw [← hrange] at hu
  obtain ⟨⟨a, b⟩, rfl⟩ := hu
  have hfab : f (a, b) = (a : G) * b := rfl
  have hcab : Commute (a : G) (b : G) := hcomm a b
  rw [hfab, hcab.mul_pow]
  have ha : (a : G) ^ p = 1 := hTexp a (hZT_T a.2)
  have hb : (b : G) ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  rw [ha, hb, one_mul]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

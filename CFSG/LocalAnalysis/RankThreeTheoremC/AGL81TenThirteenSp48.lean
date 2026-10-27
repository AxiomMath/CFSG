module

import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Loc
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenBlock
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeCfg
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeListOf
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48CenFact
import CFSG.LieType.SeitzGeneration.SpFourThree
public import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CfgData
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Bar
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Block
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Rank
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped commutatorElement Pointwise

variable (G : Type) [Group G] [Finite G]

namespace Sp48Cfg

variable {G}

private theorem le_pRank' {X : Type*} [Group X] [Finite X] {p k : ℕ} (hp : 1 < p)
    {E H : Subgroup X} (hEH : E ≤ H) (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k) :
    k ≤ Open.pRank p H :=
  CFSG.SectionRank.le_pRank hp hEH hE hc

private theorem elemAbelian_sup {X : Type*} [Group X] [Finite X] {p : ℕ} {A B : Subgroup X}
    (hA : IsElemAbelian p A) (hB : IsElemAbelian p B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hAB : A ⊓ B = ⊥) :
    IsElemAbelian p (A ⊔ B) ∧ Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  have hN : B ≤ normalizer (A : Set X) := fun y hy => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun x hx => hc x hx y hy)
  have hmul := coe_mul_of_left_le_normalizer_right A B (fun x hx =>
    centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun y hy => (hc x hx y hy).symm))
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩, ?_⟩
  · have ha : (a : X) ∈ ((A : Set X) * (B : Set X)) := by rw [← hmul]; exact a.2
    have hb : (b : X) ∈ ((A : Set X) * (B : Set X)) := by rw [← hmul]; exact b.2
    obtain ⟨x, hx, y, hy, hxy'⟩ := ha
    obtain ⟨x', hx', y', hy', hxy''⟩ := hb
    change (a : X) * b = b * a
    rw [← hxy', ← hxy'']
    have c1 : x * x' = x' * x := congrArg Subtype.val (hA.1.1.comm ⟨x, hx⟩ ⟨x', hx'⟩)
    have c2 : y * y' = y' * y := congrArg Subtype.val (hB.1.1.comm ⟨y, hy⟩ ⟨y', hy'⟩)
    calc x * y * (x' * y') = x * (y * x') * y' := by group
      _ = x * (x' * y) * y' := by rw [← hc x' hx' y hy]
      _ = (x * x') * (y * y') := by group
      _ = (x' * x) * (y' * y) := by rw [c1, c2]
      _ = x' * (x * y') * y := by group
      _ = x' * (y' * x) * y := by rw [hc x hx y' hy']
      _ = x' * y' * (x * y) := by group
  · have ha' : a ∈ ((A : Set X) * (B : Set X)) := by rw [← hmul]; exact ha
    obtain ⟨x, hx, y, hy, rfl⟩ := ha'
    have hcxy : Commute x y := hc x hx y hy
    rw [hcxy.mul_pow, hA.2 x hx, hB.2 y hy, one_mul]
  · have h := card_sup_mul_card_inf_eq_of_le_normalizer hN
    rwa [hAB, card_bot, mul_one] at h

private theorem elemAbelian_zpowers {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {x : X} (hx : orderOf x = p) :
    IsElemAbelian p (zpowers x) ∧ Nat.card (zpowers x) = p := by
  refine ⟨⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩, by rw [Nat.card_zpowers, hx]⟩
  · obtain ⟨m, hm⟩ := mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 b.2
    change (a : X) * b = b * a
    rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx,
      pow_orderOf_eq_one, one_zpow]

private theorem zpowers_inf_eq_bot {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {x : X} (hx : orderOf x = p) {B : Subgroup X} (hxB : x ∉ B) : zpowers x ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro y ⟨hy, hyB⟩
  rw [mem_bot]
  by_contra hy1
  apply hxB
  have hy' : orderOf y = p := by
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hy
    have hd : orderOf (x ^ m) ∣ p := orderOf_dvd_of_pow_eq_one (by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx,
        pow_orderOf_eq_one, one_zpow])
    rcases (Nat.dvd_prime hp).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hy1
    · exact h
  have hzz : zpowers y = zpowers x := by
    refine eq_of_le_of_card_ge (zpowers_le.2 hy) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hx, hy']
  have : x ∈ zpowers y := hzz ▸ mem_zpowers x
  exact zpowers_le.2 hyB this

open CFSG.AGLEmbedding.KFactProofs.Sp48 in
private theorem le_of_centralizers {Y : Type*} [Group Y] {K Z A : Subgroup Y} (eK : K ≃* Sp8)
    (hAK : A ≤ K) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 9)
    (hZ : ∀ a ∈ A, a ≠ 1 → ∀ k ∈ K, k * a = a * k → k ∈ Z) : K ≤ Z := by
  classical
  set E : Subgroup Sp8 := (A.subgroupOf K).map eK.toMonoidHom with hE
  have hEc : Nat.card E = 9 := by
    rw [hE, card_map_of_injective eK.injective, ← hAc]
    exact Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    obtain ⟨hcA, -⟩ := hA
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mul_comm_of_mem_isMulCommutative A (mem_subgroupOf.mp ha)
      (mem_subgroupOf.mp hb))
  have hexpE : ∀ x ∈ E, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA.2 _ (mem_subgroupOf.mp ha))
    rw [← map_pow, h1, map_one]
  have h3 : (3 : CFSG.Quasithin.GF8) ≠ 0 := by decide
  have hc : ∃ c : CFSG.Quasithin.GF8, c ≠ 0 ∧ c ≠ 1 :=
    ⟨CFSG.Quasithin.GF8.ofNat' 2, by decide, by decide⟩
  have hgen := CFSG.LieType.SeitzGeneration.closure_centralizers_spFour_three h3 hc hcommE
    hexpE hEc
  have hle : closure {g : Sp8 | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} ≤
      Z.comap (K.subtype.comp eK.symm.toMonoidHom) := by
    rw [closure_le]
    rintro g ⟨_, ⟨a, ha, rfl⟩, hx1, hgx⟩
    have ha1 : (a : Y) ≠ 1 := fun h => hx1 (by
      rw [show a = 1 from Subtype.ext h, map_one])
    refine hZ (a : Y) (mem_subgroupOf.mp ha) ha1 _ (eK.symm g).2 ?_
    have := congrArg (fun t : Sp8 => ((eK.symm t : K) : Y)) hgx
    simpa using this
  intro k hk
  have hk' : eK ⟨k, hk⟩ ∈ closure {g : Sp8 | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g} := by
    rw [hgen]
    exact mem_top _
  simpa using hle hk'

private theorem exists_spE {Y : Type*} [Group Y] {K : Subgroup Y}
    (eK : K ≃* CFSG.AGLEmbedding.KFactProofs.Sp48.Sp8) :
    ∃ A : Subgroup Y, A ≤ K ∧ IsElemAbelian 3 A ∧ Nat.card A = 9 ∧
      ∀ a ∈ A, ∃ s ∈ CFSG.AGLEmbedding.KFactProofs.Sp48.spE, a = ((eK.symm s : K) : Y) := by
  open CFSG.AGLEmbedding.KFactProofs.Sp48 in
  have hEel : IsElemAbelian 3 spE := by
    refine ⟨IsMulCommutative.of_comm ?_, fun x hx => ((mem_spE_iff_cube x).1 hx).2⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    exact Subtype.ext (comm_spT0 a (spE_le_spT0 ha) b (spE_le_spT0 hb))
  open CFSG.AGLEmbedding.KFactProofs.Sp48 in
  refine ⟨(spE.map eK.symm.toMonoidHom).map K.subtype, map_subtype_le _,
    IsElemAbelian.map (IsElemAbelian.map hEel _) _, ?_, ?_⟩
  · rw [card_map_of_injective K.subtype_injective, card_map_of_injective eK.symm.injective,
      card_spE]
  · rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩

private theorem imH_ne_bot {H I₀ : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hI₀H : I₀ ≤ H) {T : Type} [Group T]
    [Nontrivial T] (f : I₀ →* T) (hf : Function.Surjective f)
    (hfk : (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker) : imH H I₀ ≠ ⊥ := by
  intro hWb
  have hf1 : ∀ x : I₀, f x = 1 := by
    intro x
    apply hfk
    rw [mem_subgroupOf]
    refine ⟨⟨x, hI₀H x.2⟩, ?_, rfl⟩
    have h1 : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hI₀H x.2⟩ = 1 := by
      have hmem : QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hI₀H x.2⟩ ∈
          imH H I₀ := mem_map_of_mem _ (mem_subgroupOf.mpr x.2)
      rw [hWb, mem_bot] at hmem
      exact hmem
    change QuotientGroup.mk' (primeComplementCore (G := H) 3) ⟨x, hI₀H x.2⟩ ∈ centralizer _
    rw [h1]
    exact one_mem _
  obtain ⟨a, b, hab⟩ := exists_pair_ne T
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  exact hab (by rw [hf1, hf1])

private theorem not_isSolvable_d1X0 {M H L I₀ : Subgroup G}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} (hLM : L ≤ M)
    (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hI₀c : IsTwoPrimeComponent I₀ I₀) {T : Type} [Group T]
    [Nontrivial T] (f : I₀ →* T) (hf : Function.Surjective f)
    (hfk : (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker) : ¬ Group.IsSolvable (d1X0 3 M H) := by
  intro hsol
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hI₀M : I₀ ≤ H ⊓ M := le_inf hI₀H (hI₀.le.trans (inf_le_right.trans hLM))
  have hWX : imH H I₀ ≤ d1X0 3 M H :=
    map_mono fun x hx => mem_subgroupOf.mpr (hI₀M (mem_subgroupOf.mp hx))
  have hperf : ⁅imH H I₀, imH H I₀⁆ = imH H I₀ := by
    have h1 : ⁅I₀.subgroupOf H, I₀.subgroupOf H⁆ = I₀.subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hI₀H, hI₀c.perfect]
    rw [← map_commutator, h1]
  haveI := hsol
  haveI : Group.IsSolvable (imH H I₀) := solvable_of_solvable_injective (inclusion_injective hWX)
  haveI : Nontrivial (imH H I₀) := (nontrivial_iff_ne_bot _).2 (imH_ne_bot hI₀H f hf hfk)
  haveI : Group.IsPerfect (imH H I₀) := by
    refine ⟨map_injective (imH H I₀).subtype_injective ?_⟩
    rw [map_subtype_commutator, hperf, ← MonoidHom.range_eq_map, range_subtype]
  exact Group.IsPerfect.not_isSolvable (imH H I₀) inferInstance

open CFSG.AGLEmbedding.KFactProofs.Sp48 in
private theorem exists_inSitu (hKN : KFactSp48NonsolvLocal) {P : Sylow 3 G}
    {M H Q : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hd : AGL81CfgData 3 P M H Q K) {dK : TauCeti.ValidLieTypeIndex}
    (hdK : IsSpFourEightIndex dK) (eK : K ≃* CatGroup dK)
    (hns : ¬ Group.IsSolvable (d1X0 3 M H)) :
    ∃ (T : Sylow 3 (H ⧸ primeComplementCore (G := H) 3))
      (A₀ V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      Sp48NInSitu (T : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (d1X0 3 M H) K A₀ V₀ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  set O := primeComplementCore (G := H) 3 with hOdef
  set π := QuotientGroup.mk' O with hπ
  have hnle := hd.not_le_X0
  have hne : K ≠ ⊥ := fun h => hnle (by rw [h]; exact bot_le)
  have hk := hd.kbar
  subst hk
  have hKn : (d1KBar 3 M H).Normal := d1KBar_normal_of_escape he hd.base hd.le_H hne
  haveI := hKn
  obtain ⟨R, hBR, hRM, hR, -⟩ := exists_isSylowIn_of_isAGLQ he hd.base hd.le_H
  set T : Sylow 3 (H ⧸ O) := hR.toSylow.mapSurjective (QuotientGroup.mk'_surjective O) with hT
  have hTeq : (T : Subgroup (H ⧸ O)) = (R.subgroupOf H).map π := by
    rw [hT, Sylow.coe_mapSurjective, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  obtain ⟨E, hET, hEab, hEcard, hcore⟩ := cores_le_d1X0 he hd.base hBR hRM hR
  rw [← hTeq] at hET hcore
  obtain ⟨⟨eSp⟩, hcardK⟩ := exists_equiv_sp8 hdK eK
  haveI : IsSimpleGroup Sp8 := isSimple_sp8_of_index hdK eK eSp
  haveI : IsSimpleGroup (d1KBar 3 M H) := eSp.isSimpleGroup
  have hZK : center (d1KBar 3 M H) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (d1KBar 3 M H)) with h | h
    · exact h
    · exfalso
      haveI : IsMulCommutative (d1KBar 3 M H) := center_eq_top_iff.1 h
      have hpr := (Group.is_simple_iff_prime_card (α := d1KBar 3 M H)).1 inferInstance
      rw [hcardK] at hpr
      exact absurd hpr (by norm_num)
  obtain ⟨A₀, hA₀K, hA₀, hA₀c, hA₀s⟩ := Sp48Cfg.exists_spE (K := d1KBar 3 M H) eSp
  have hSeitz : ∀ A : Subgroup (H ⧸ O), A ≤ d1KBar 3 M H → IsElemAbelian 3 A →
      Nat.card A = 9 → (∀ a ∈ A, a ≠ 1 → ∀ k ∈ d1KBar 3 M H, k * a = a * k →
        k ∈ d1X0 3 M H) → False :=
    fun A hAK hA hAc hZ => hnle (Sp48Cfg.le_of_centralizers eSp hAK hA hAc hZ)
  have hmem : ∀ c ∈ centralizer ((d1KBar 3 M H : Subgroup (H ⧸ O)) : Set (H ⧸ O)),
      orderOf c = 3 → c ∈ d1KBar 3 M H := by
    intro c hc hc3
    by_contra hcK
    have hcomm : ∀ a ∈ A₀, ∀ b ∈ zpowers c, a * b = b * a := by
      intro a ha b hb
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
      exact (mem_centralizer_iff.1 (zpow_mem hc m)) a (hA₀K ha)
    obtain ⟨hzc, hzcard⟩ := Sp48Cfg.elemAbelian_zpowers Nat.prime_three hc3
    have hinf : A₀ ⊓ zpowers c = ⊥ := by
      rw [inf_comm]
      exact Sp48Cfg.zpowers_inf_eq_bot Nat.prime_three hc3 fun h => hcK (hA₀K h)
    obtain ⟨hB₀, hB₀c⟩ := Sp48Cfg.elemAbelian_sup hA₀ hzc hcomm hinf
    have hB₀p : IsPGroup 3 (A₀ ⊔ zpowers c : Subgroup (H ⧸ O)) := fun x =>
      ⟨1, Subtype.ext (by simpa using hB₀.2 x x.2)⟩
    obtain ⟨Q', hQ'⟩ := hB₀p.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (H ⧸ O) Q' T
    have hgT : ((A₀ ⊔ zpowers c : Subgroup (H ⧸ O))).map (MulAut.conj g).toMonoidHom ≤
        (T : Subgroup (H ⧸ O)) := by
      have h1 : ((g • Q' : Sylow 3 (H ⧸ O)) : Subgroup (H ⧸ O)) =
          (Q' : Subgroup (H ⧸ O)).map (MulAut.conj g).toMonoidHom := by
        rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
        rfl
      rw [hg] at h1
      rw [h1]
      exact map_mono hQ'
    set B : Subgroup (H ⧸ O) := (A₀ ⊔ zpowers c).map (MulAut.conj g).toMonoidHom with hBdef
    set A : Subgroup (H ⧸ O) := A₀.map (MulAut.conj g).toMonoidHom with hAdef
    set z : H ⧸ O := g * c * g⁻¹ with hz
    have hBel : IsElemAbelian 3 B := IsElemAbelian.map hB₀ _
    have hBc : Nat.card B = 3 ^ 3 := by
      rw [hBdef, card_map_of_injective (MulAut.conj g).injective, hB₀c, hA₀c, hzcard]
      norm_num
    have hAB : A ≤ B := map_mono le_sup_left
    have hzB : z ∈ B := ⟨c, mem_sup_right (mem_zpowers c), rfl⟩
    have hAK : A ≤ d1KBar 3 M H := by
      rintro _ ⟨a, ha, rfl⟩
      exact hKn.conj_mem a (hA₀K ha) g
    have hzC : z ∈ centralizer ((d1KBar 3 M H : Subgroup (H ⧸ O)) : Set (H ⧸ O)) :=
      normal_centralizer.conj_mem c hc g
    have hzK : z ∉ d1KBar 3 M H := by
      intro h
      apply hcK
      have := hKn.conj_mem z h g⁻¹
      rwa [hz, show g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c by group] at this
    have hz3 : orderOf z = 3 := by
      rw [hz, show g * c * g⁻¹ = MulAut.conj g c from rfl, MulEquiv.orderOf_eq, hc3]
    have hA : IsElemAbelian 3 A := IsElemAbelian.map hA₀ _
    have hAc : Nat.card A = 9 := by
      rw [hAdef, card_map_of_injective (MulAut.conj g).injective, hA₀c]
    have h3T : 3 ≤ Open.pRank 3 (T : Subgroup (H ⧸ O)) :=
      Sp48Cfg.le_pRank' (by norm_num) hgT hBel hBc
    rw [if_pos h3T] at hcore
    refine hSeitz A hAK hA hAc fun a ha ha1 k hk hka => ?_
    have ha3 : orderOf a = 3 := orderOf_eq_prime (hA.2 a ha) ha1
    set X : Subgroup (H ⧸ O) := zpowers a ⊔ zpowers z with hXdef
    have haz : ∀ x ∈ zpowers a, ∀ y ∈ zpowers z, x * y = y * x := by
      intro x hx y hy
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
      exact (mem_centralizer_iff.1 (zpow_mem hzC n)) _ (zpow_mem (hAK ha) m)
    have hXinf : zpowers a ⊓ zpowers z = ⊥ := by
      rw [inf_comm]
      exact Sp48Cfg.zpowers_inf_eq_bot Nat.prime_three hz3 fun h =>
        hzK ((zpowers_le.2 (hAK ha)) h)
    obtain ⟨hXel, hXc⟩ := Sp48Cfg.elemAbelian_sup
      (Sp48Cfg.elemAbelian_zpowers Nat.prime_three ha3).1
      (Sp48Cfg.elemAbelian_zpowers Nat.prime_three hz3).1 haz hXinf
    have hXB : X ≤ B := sup_le (zpowers_le.2 (hAB ha)) (zpowers_le.2 hzB)
    have hX2 : 2 ≤ Open.pRank 3 X := Sp48Cfg.le_pRank' (by norm_num) le_rfl hXel (by
      rw [hXc, Nat.card_zpowers, Nat.card_zpowers, ha3, hz3]; norm_num)
    have hX3 : 3 ≤ Open.pRank 3 (X ⊔ ((T : Subgroup (H ⧸ O)) ⊓ centralizer (X : Set (H ⧸ O)))) := by
      refine Sp48Cfg.le_pRank' (by norm_num) ?_ hBel hBc
      intro b hb
      refine mem_sup_right ⟨hgT hb, mem_centralizer_iff.2 fun x hx => ?_⟩
      exact congrArg Subtype.val (hBel.1.1.comm ⟨x, hXB hx⟩ ⟨b, hb⟩)
    have hNX := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3
      ((hXB.trans hgT)) hX2 hX3
    refine hcore (hNX (centralizer_le_normalizer _ ?_))
    rw [mem_centralizer_iff]
    intro x hx
    have hk' : x ∈ centralizer ({k} : Set (H ⧸ O)) := by
      have hle : X ≤ centralizer ({k} : Set (H ⧸ O)) := by
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
        · exact mem_centralizer_singleton_iff.2 hka.symm
        · exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hzC) k hk).symm
      exact hle hx
    exact mem_centralizer_singleton_iff.1 hk'
  have hC : centralizer ((d1KBar 3 M H : Subgroup (H ⧸ O)) : Set (H ⧸ O)) = ⊥ :=
    centralizer_eq_bot_of_forall_mem Nat.prime_three (by norm_num)
      (primeComplementCore_quotient_eq_bot (G := H) 3) hKn hmem hZK
  have h3T : 3 ≤ Open.pRank 3 (T : Subgroup (H ⧸ O)) := by
    by_contra hlt
    rw [if_neg hlt] at hcore
    have hEK : E ≤ d1KBar 3 M H := by
      intro e he
      by_contra heK
      have he3 : e ^ 3 ^ 1 = 1 := by rw [pow_one]; exact hEab.2 e he
      obtain ⟨φ, hφ, hφ3, hφK⟩ := exists_frob (eK := eSp) hC heK he3
      have hφc : ∀ a ∈ A₀, ∀ b ∈ zpowers φ, a * b = b * a := by
        intro a ha b hb
        obtain ⟨s, hs, rfl⟩ := hA₀s a ha
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
        have h1 : φ * ((eSp.symm s : d1KBar 3 M H) : H ⧸ O) * φ⁻¹ =
            ((eSp.symm s : d1KBar 3 M H) : H ⧸ O) := by
          rw [← coe_symm_adHom, hφ, (fr_eq_self_iff_mem_spE (spE_le_spT0 hs)).2 hs]
        have h2 : Commute φ ((eSp.symm s : d1KBar 3 M H) : H ⧸ O) := by
          rw [commute_iff_eq]
          calc φ * ((eSp.symm s : d1KBar 3 M H) : H ⧸ O) =
              φ * ((eSp.symm s : d1KBar 3 M H) : H ⧸ O) * φ⁻¹ * φ := by group
            _ = ((eSp.symm s : d1KBar 3 M H) : H ⧸ O) * φ := by rw [h1]
        exact ((h2.zpow_left m).eq).symm
      have hφ1 : φ ≠ 1 := fun h => hφK (h ▸ one_mem _)
      have hφo : orderOf φ = 3 := orderOf_eq_prime hφ3 hφ1
      obtain ⟨hzφ, hzφc⟩ := Sp48Cfg.elemAbelian_zpowers Nat.prime_three hφo
      have hinf : A₀ ⊓ zpowers φ = ⊥ := by
        rw [inf_comm]
        exact Sp48Cfg.zpowers_inf_eq_bot Nat.prime_three hφo fun h => hφK (hA₀K h)
      obtain ⟨hB, hBc⟩ := Sp48Cfg.elemAbelian_sup hA₀ hzφ hφc hinf
      have h3top : 3 ≤ Open.pRank 3 (⊤ : Subgroup (H ⧸ O)) :=
        Sp48Cfg.le_pRank' (by norm_num) le_top hB (by rw [hBc, hA₀c, hzφc]; norm_num)
      rw [← (CFSG.SectionRank.pRank_sylow T).1] at h3top
      exact hlt h3top
    refine hSeitz E hEK hEab hEcard fun e he he1 k hk hke => hcore ?_
    have he3 : orderOf e = 3 := orderOf_eq_prime (hEab.2 e he) he1
    obtain ⟨hze, hzec⟩ := Sp48Cfg.elemAbelian_zpowers Nat.prime_three he3
    have hN : normalizer (zpowers e : Set (H ⧸ O)) ≤ GLBCore 3 1 E :=
      le_sSup ⟨zpowers e, zpowers_le.2 he,
        Sp48Cfg.le_pRank' (by norm_num) le_rfl hze (by rw [hzec, pow_one]), rfl⟩
    refine hN (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hx
    exact ((Commute.zpow_left (show Commute e k from hke.symm) m).eq)
  rw [if_pos h3T] at hcore
  have hY₀ : d1X0 3 M H ≠ ⊤ := fun h => hnle (h ▸ le_top)
  obtain ⟨A₀', V₀, hI⟩ := hKN (H ⧸ O) (d1KBar 3 M H) dK hdK hKn ⟨eK⟩ hC T (d1X0 3 M H) h3T hcore
    hY₀ hns
  exact ⟨T, A₀', V₀, hI⟩

private theorem exists_localized_factors_cfg {M H L : Subgroup G}
    (h3 : TwoLocalPhaseThree M H) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hDL : imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ ⊥)
    {T K A₀ V₀ : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hI : Sp48NInSitu T (imH H (H ⊓ M)) K A₀ V₀) :
    ∃ (V₁ V₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) (L₁ L₂ : Subgroup G),
      IsWeakSBlock M (pCoreOf 2 H) L₁ ∧ IsWeakSBlock M (pCoreOf 2 H) L₂ ∧
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁ ≤ H ∧
      Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂ ≤ H ∧
      ⁅V₁, V₁⁆ = V₁ ∧ ⁅V₂, V₂⁆ = V₂ ∧ ⁅V₁, V₂⁆ = ⊥ ∧ IsCaseTwoGroup 3 V₁ ∧
      IsCaseTwoGroup 3 V₂ ∧
      V₁ ≤ imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁) ∧
      V₂ ≤ imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂) ∧
      imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁) ≤
        Subgroup.normalizer ((V₁ ⊔ V₂ : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) ∧
      imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂) ≤
        Subgroup.normalizer ((V₁ ⊔ V₂ : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) 3)) ∧
      (L₁ ≠ L₂ →
        imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₁) ≤
          Subgroup.normalizer (V₁ : Set (H ⧸ primeComplementCore (G := H) 3)) ∧
        imH H (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L₂) ≤
          Subgroup.normalizer (V₂ : Set (H ⧸ primeComplementCore (G := H) 3))) := by
  classical
  set S : Subgroup G := pCoreOf 2 H with hS
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3) with hπ
  set N : Subgroup G := GLBPrimeCore 3 H with hN
  have hKS : H ⊓ M = M ⊓ Subgroup.normalizer (S : Set G) :=
    h3.toTwoLocalPair.inf_eq_inf_normalizer_twoCore
  have hO2 : pCoreOf 2 M ≤ N :=
    (h3.toTwoLocalPair.twoCore_M_le h3.twoCore_inf).trans
      (pCoreOf_le_glbPrimeCore Nat.prime_two (by norm_num) H)
  obtain ⟨V₁, V₂, h12, hcomm, hp1, hp2, ⟨d₁, hd₁, ⟨e₁⟩⟩, ⟨d₂, hd₂, ⟨e₂⟩⟩, -, -, -⟩ := hI.factors
  have hc₁ : IsCaseTwoGroup 3 V₁ := ⟨d₁, hd₁, ⟨e₁⟩⟩
  have hc₂ : IsCaseTwoGroup 3 V₂ := ⟨d₂, hd₂, ⟨e₂⟩⟩
  have hs₁ : IsSimpleGroup V₁ := isSimpleGroup_of_isCaseTwoGroup_three hc₁
  have hs₂ : IsSimpleGroup V₂ := isSimpleGroup_of_isCaseTwoGroup_three hc₂
  have hnab : ∀ (W : Subgroup (H ⧸ primeComplementCore (G := H) 3)), IsSimpleGroup W →
      ⁅W, W⁆ = W → ∃ a b : W, a * b ≠ b * a := by
    intro W hWs hWp
    by_contra hcon
    push Not at hcon
    have : Nontrivial W := inferInstance
    have hbot : ⁅W, W⁆ ≤ ⊥ := Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hcon ⟨g₁, h₁⟩ ⟨g₂, h₂⟩)
    obtain ⟨a, b, hab⟩ := exists_pair_ne W
    apply hab
    have ha : (a : H ⧸ primeComplementCore (G := H) 3) ∈ (⊥ : Subgroup _) :=
      hbot (hWp.ge a.2)
    have hb : (b : H ⧸ primeComplementCore (G := H) 3) ∈ (⊥ : Subgroup _) :=
      hbot (hWp.ge b.2)
    rw [Subgroup.mem_bot] at ha hb
    exact Subtype.ext (ha.trans hb.symm)
  have hnab₁ := hnab V₁ hs₁ hp1
  have hnab₂ := hnab V₂ hs₂ hp2
  let ι := {L' : Subgroup G // ∃ k ∈ H ⊓ M, L' = L.map (MulAut.conj k).toMonoidHom}
  have hweak : ∀ L' : ι, IsWeakSBlock M S L'.1 := by
    rintro ⟨L', k, hk, rfl⟩
    have hkS : k ∈ Subgroup.normalizer (S : Set G) := (hKS ▸ hk).2
    refine { toIsTwoPrimeComponent := hL.toIsTwoPrimeComponent.map_conj hk.2,
             not_le_normalizer := fun hle => hL.not_le_normalizer fun x hx => ?_ }
    have h1 : k * x * k⁻¹ ∈ Subgroup.normalizer (S : Set G) :=
      hle ⟨x, hx, by simp [MulAut.conj_apply]⟩
    have e : x = k⁻¹ * (k * x * k⁻¹) * k := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hkS) h1) hkS
  have hNle : ∀ L' : ι, Subgroup.normalizer (S : Set G) ⊓ L'.1 ≤ H ⊓ M := fun L' x hx => by
    rw [hKS]
    exact ⟨(hweak L').le hx.2, hx.1⟩
  have hNH : ∀ L' : ι, Subgroup.normalizer (S : Set G) ⊓ L'.1 ≤ H := fun L' =>
    (hNle L').trans inf_le_left
  set Pt : ι → Subgroup (H ⧸ primeComplementCore (G := H) 3) :=
    fun L' => imH H (Subgroup.normalizer (S : Set G) ⊓ L'.1) with hPt
  have hbc : ∀ L' L'' : ι, L' ≠ L'' → ∀ x ∈ Pt L', ∀ y ∈ Pt L'', x * y = y * x := by
    intro L' L'' hne x hx y hy
    have hne' : L'.1 ≠ L''.1 := fun h => hne (Subtype.ext h)
    have hc : ⁅L'.1, L''.1⁆ ≤ N :=
      ((hweak L').toIsTwoPrimeComponent.commutator_le (hweak L'').toIsTwoPrimeComponent
        hne').trans hO2
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have ha' : (a : G) ∈ L'.1 := (Subgroup.mem_subgroupOf.mp ha).2
    have hb' : (b : G) ∈ L''.1 := (Subgroup.mem_subgroupOf.mp hb).2
    have h1 : ((⁅a, b⁆ : H) : G) ∈ N := by
      have := hc (Subgroup.commutator_mem_commutator ha' hb')
      simpa [commutatorElement_def] using this
    have h2 := (mem_glbPrimeCore_iff_mk_eq_one (p := 3) ⁅a, b⁆).mp h1
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  set D : Subgroup (H ⧸ primeComplementCore (G := H) 3) := ⨆ L' : ι, Pt L' with hD
  have hDX : D ≤ imH H (H ⊓ M) := iSup_le fun L' =>
    Subgroup.map_mono (Subgroup.subgroupOf_mono H (hNle L'))
  have hXD : imH H (H ⊓ M) ≤
      Subgroup.normalizer (D : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    refine le_normalizer_of_forall_map_conj_le fun x hx => ?_
    obtain ⟨k', hk', rfl⟩ := hx
    have hkKM : (k' : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hk'
    have hkS : (k' : G) ∈ Subgroup.normalizer (S : Set G) := (hKS ▸ hkKM).2
    rw [hD, Subgroup.map_iSup]
    refine iSup_le fun L' => ?_
    obtain ⟨k₀, hk₀, hL'⟩ := L'.2
    have hconj : (L'.1).map (MulAut.conj (k' : G)).toMonoidHom =
        L.map (MulAut.conj ((k' : G) * k₀)).toMonoidHom := by
      rw [hL', map_conj_mul_eq]
    have hmem : (L'.1).map (MulAut.conj (k' : G)).toMonoidHom ∈
        {L'' : Subgroup G | ∃ k ∈ H ⊓ M, L'' = L.map (MulAut.conj k).toMonoidHom} :=
      ⟨(k' : G) * k₀, (H ⊓ M).mul_mem hkKM hk₀, hconj⟩
    refine (map_conj_imH_le k'.2).trans ?_
    have hN' : (Subgroup.normalizer (S : Set G)).map (MulAut.conj (k' : G)).toMonoidHom =
        Subgroup.normalizer (S : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkS)
    have e : (Subgroup.normalizer (S : Set G) ⊓ L'.1).map (MulAut.conj (k' : G)).toMonoidHom =
        Subgroup.normalizer (S : Set G) ⊓ (L'.1).map (MulAut.conj (k' : G)).toMonoidHom := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj (k' : G)).injective, hN']
    rw [e]
    exact le_iSup Pt (⟨(L'.1).map (MulAut.conj (k' : G)).toMonoidHom, hmem⟩ : ι)
  have hDne : D ≠ ⊥ := by
    intro hbot
    have hLι : L ∈ {L'' : Subgroup G | ∃ k ∈ H ⊓ M,
        L'' = L.map (MulAut.conj k).toMonoidHom} :=
      ⟨1, (H ⊓ M).one_mem, by ext x; simp⟩
    apply hDL
    rw [eq_bot_iff, ← hbot]
    exact le_iSup Pt (⟨L, hLι⟩ : ι)
  have hV₀D : V₀ ≤ D := (hI.minimal D hDX hXD).resolve_left hDne
  have hV₀N : ∀ L' : ι, Pt L' ≤ Subgroup.normalizer (V₀ : Set _) := fun L' =>
    ((le_iSup Pt L').trans hDX).trans hI.V_normal
  have hV₁V₀ : V₁ ≤ V₀ := h12 ▸ le_sup_left
  have hV₂V₀ : V₂ ≤ V₀ := h12 ▸ le_sup_right
  have hV₁n : V₀ ≤ Subgroup.normalizer (V₁ : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [← h12]
    refine sup_le Subgroup.le_normalizer fun b hb => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun a ha => ?_)
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this)
  have hV₂n : V₀ ≤ Subgroup.normalizer (V₂ : Set (H ⧸ primeComplementCore (G := H) 3)) := by
    rw [← h12]
    refine sup_le (fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)) Subgroup.le_normalizer
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm
  have hDV : D ≤ Subgroup.normalizer (V₀ : Set (H ⧸ primeComplementCore (G := H) 3)) :=
    hDX.trans hI.V_normal
  obtain ⟨i₁, hi₁⟩ := exists_le_of_commuting_family Pt hbc hV₀D hDV hI.V_perfect hV₁V₀ hV₁n
    hp1 hs₁ hnab₁
  obtain ⟨i₂, hi₂⟩ := exists_le_of_commuting_family Pt hbc hV₀D hDV hI.V_perfect hV₂V₀ hV₂n
    hp2 hs₂ hnab₂
  have hVsup : ∀ L' : ι, Pt L' ≤ Subgroup.normalizer
      ((V₁ ⊔ V₂ : Subgroup (H ⧸ primeComplementCore (G := H) 3)) :
        Set (H ⧸ primeComplementCore (G := H) 3)) := fun L' => h12 ▸ hV₀N L'
  refine ⟨V₁, V₂, i₁.1, i₂.1, hweak i₁, hweak i₂, hNH i₁, hNH i₂, hp1, hp2, hcomm, hc₁, hc₂,
    hi₁, hi₂, hVsup i₁, hVsup i₂, fun hne => ?_⟩
  have hne' : i₁ ≠ i₂ := fun h => hne (congrArg Subtype.val h)
  have hVc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb => by
    have := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  exact ⟨le_normalizer_of_commute_blocks (hbc i₁ i₂ hne') hi₁ hi₂ hVc (hVsup i₁) hs₂ hnab₂,
    le_normalizer_of_commute_blocks (hbc i₂ i₁ hne'.symm) hi₂ hi₁
      (fun b hb a ha => (hVc a ha b hb).symm) (by rw [sup_comm]; exact hVsup i₂) hs₁ hnab₁⟩


private theorem false_of_two_blocks_rank (hrank : evenRank G = 3) {M L₁ L₂ : Subgroup G}
    (hM : IsTwoLocal M) (h₁ : IsTwoPrimeComponent M L₁) (h₂ : IsTwoPrimeComponent M L₂)
    (hne : L₁ ≠ L₂) {E₁ E₂ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hE₁ : E₁ ≤ barM M L₁)
    (hE₂ : E₂ ≤ barM M L₂) (he₁ : IsElemAbelian 7 E₁) (he₂ : IsElemAbelian 7 E₂)
    (hc₁ : Nat.card E₁ = 7 ^ 2) (hc₂ : Nat.card E₂ = 7 ^ 2)
    (hz : E₁ ⊓ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) : False := by
  have hbar : barM M L₁ ≠ barM M L₂ := fun he => hne (h₁.eq_of_barM_eq h₂ he)
  have hcom := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.component
    h₂.component hbar
  have hcomm : ∀ h ∈ barM M L₁, ∀ y ∈ barM M L₂, h * y = y * h := by
    intro h hh y hy
    have h' := Subgroup.commutator_mem_commutator hh hy
    rw [hcom, Subgroup.mem_bot] at h'
    exact commutatorElement_eq_one_iff_mul_comm.mp h'
  have hinf : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff, ← hz]
    refine le_inf inf_le_left fun y hy => ?_
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => hcomm h hh y (hE₂ hy.2)
  obtain ⟨hel, hcard⟩ := Sp48Cfg.elemAbelian_sup he₁ he₂
    (fun x hx y hy => hcomm x (hE₁ hx) y (hE₂ hy)) hinf
  have h4 : 4 ≤ Open.pRank 7 (barM M (L₁ ⊔ L₂)) :=
    Sp48Cfg.le_pRank' (by norm_num)
      (sup_le (hE₁.trans (barM_mono le_sup_left)) (hE₂.trans (barM_mono le_sup_right))) hel
      (by rw [hcard, hc₁, hc₂]; norm_num)
  have hLsup : L₁ ⊔ L₂ ≤ M := sup_le h₁.le h₂.le
  have h8 := pRank_barM_le (q := 7) (by norm_num) (by norm_num) M (L₁ ⊔ L₂) hLsup
  have h9 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 7 (by norm_num) hLsup
  have h10 := local_pRank_le_evenRank (G := G) 7 (by norm_num) (by norm_num) M hM
  omega

end Sp48Cfg

theorem agl81TenThirteenSp48_of_sigma (hσ : 3 ∈ rankThreeSigmaA G)
    (hKN : KFactSp48NonsolvLocal) (hK3c : KFactBlockL28Transvection)
    (hK3r1 : KFactBlockL28Rank) (hK3r2 : KFactBlockL28TwoRank) (h85 : Asc81bEightFive)
    (h93 : Asc81bNineThree) (hNX : CFSG.AGLEmbeddingD2.NoXBlockFor G)
    (h98 : AGL81NineEightFour G) :
    Setting G → ∀ (P : Sylow 3 G) (M H Q : Subgroup G)
      (K : Subgroup (H ⧸ primeComplementCore (G := H) 3)),
      AGL81CfgData 3 P M H Q K → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∀ I₀ ∈ cZero (H ⊓ L), IsTwoPrimeComponent I₀ I₀ →
      ∀ (q : TauCeti.PrimePower) (dK dJ : TauCeti.ValidLieTypeIndex), q.p = 2 →
      q.exponent = 3 → dK.1 = .B 2 q → dJ.1 = .A 1 q → Nonempty (K ≃* CatGroup dK) →
      ∀ f : I₀ →* CatGroup dJ, Function.Surjective f →
        (d1PlusCore 3 H K).subgroupOf I₀ ≤ f.ker → False := by
  intro hS P M H Q K hd L hL I₀ hI₀ hI₀c q dK dJ hq2 hq3 hdK hdJ ⟨eK⟩ f hf hfk
  have hdJc : IsCaseTwoIndex 3 dJ := Or.inl ⟨rfl, q, hq2, hq3, hdJ⟩
  haveI : Nontrivial (CatGroup dJ) :=
    (isSimpleGroup_of_isCaseTwoGroup_three ⟨dJ, hdJc, ⟨MulEquiv.refl _⟩⟩).toNontrivial
  have hns := Sp48Cfg.not_isSolvable_d1X0 hL.le hI₀ hI₀c f hf hfk
  obtain ⟨T, A₀, V₀, hI⟩ := Sp48Cfg.exists_inSitu hKN hd ⟨q, hq2, hq3, hdK⟩ eK hns
  have hT3 := hd.toTwoLocalPhaseThree' hS h98
  have hyps : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
      BlockL28Hyps M (pCoreOf 2 H) L' := fun L' hL' =>
    blockL28Hyps_of_cfg h85 h93 hNX h98 hS hd hL'
  have hI₀H : I₀ ≤ H := hI₀.le.trans inf_le_left
  have hDL : imH H (normalizer (pCoreOf 2 H : Set G) ⊓ L) ≠ ⊥ := by
    intro hbot
    apply Sp48Cfg.imH_ne_bot hI₀H f hf hfk
    rw [eq_bot_iff, ← hbot]
    refine map_mono fun x hx => mem_subgroupOf.mpr ?_
    have hx' := hI₀.le (mem_subgroupOf.mp hx)
    rw [hT3.toTwoLocalPair.normalizer_twoCore_H]
    exact hx'
  obtain ⟨V₁, V₂, L₁, L₂, hL₁, hL₂, hH₁, hH₂, hp1, -, hcomm, hc₁, hc₂, hV₁, hV₂, hn₁, -,
    hsep⟩ := Sp48Cfg.exists_localized_factors_cfg hT3 hL hDL hI
  obtain ⟨H₁', R₁', hesc⟩ := hd.escape
  by_cases hLeq : L₁ = L₂
  ·
    subst hLeq
    have hq := hasL28Quot2_of_normal hH₁ hV₁ hV₂ hn₁ hp1 hcomm hc₁ hc₂
    exact false_of_three_le_pRank_barM hS.rank hσ hesc.maxTwoLocal_M.1 hL₁.le
      (hK3r2 G M _ L₁ (hyps L₁ hL₁) (nineThreeTwo_of_hasL28Quot hK3c (hyps L₁ hL₁)
        hq.hasL28Quot) hq)
  ·
    obtain ⟨hn₁', hn₂'⟩ := hsep hLeq
    have hE : ∀ L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L' →
        HasL28Quot (pCoreOf 2 H) L' → ∃ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
          E ≤ barM M L' ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
          E ⊓ centralizer (barM M L' : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥ := fun L' hL' hs =>
      hK3r1 G M _ L' (hyps L' hL') (nineThreeTwo_of_hasL28Quot hK3c (hyps L' hL') hs) hs
    obtain ⟨E₁, hE₁, he₁, hc₁', hz₁⟩ := hE L₁ hL₁ (hasL28Quot_of_normal hH₁ hV₁ hn₁' hc₁)
    obtain ⟨E₂, hE₂, he₂, hc₂', -⟩ := hE L₂ hL₂ (hasL28Quot_of_normal hH₂ hV₂ hn₂' hc₂)
    exact Sp48Cfg.false_of_two_blocks_rank hS.rank hesc.maxTwoLocal_M.1
      hL₁.toIsTwoPrimeComponent hL₂.toIsTwoPrimeComponent hLeq hE₁ hE₂ he₁ he₂ hc₁' hc₂' hz₁

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

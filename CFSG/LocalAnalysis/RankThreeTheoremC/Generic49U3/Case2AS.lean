module

import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogComponent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped commutatorElement Pointwise

private theorem perfect_fix {Y : Type*} [Group Y] {L : Subgroup Y} (hperf : commutator ↥L = ⊤)
    {g : Y} (hg : g ∈ normalizer (L : Set Y))
    (h : ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ centralizer (L : Set Y)) :
    g ∈ centralizer (L : Set Y) := by
  have hconj : ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun l hl => (mem_normalizer_iff.mp hg l).mp hl
  let ψ : ↥L →* ↥L := MonoidHom.mk'
    (fun a => ⟨g * (a : Y) * g⁻¹ * (a : Y)⁻¹, L.mul_mem (hconj a a.2) (L.inv_mem a.2)⟩) (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      apply Subtype.ext
      have hz : a⁻¹ * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * a⁻¹ :=
        mem_centralizer_iff.mp (h b hb) _ (L.inv_mem ha)
      show g * (a * b) * g⁻¹ * (a * b)⁻¹ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹)
      calc g * (a * b) * g⁻¹ * (a * b)⁻¹
          = g * a * g⁻¹ * ((g * b * g⁻¹ * b⁻¹) * a⁻¹) := by group
        _ = g * a * g⁻¹ * (a⁻¹ * (g * b * g⁻¹ * b⁻¹)) := by rw [hz]
        _ = (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) := by group)
  have hψ : ∀ a b : ↥L, ψ ⁅a, b⁆ = 1 := by
    intro a b
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    show (g * a * g⁻¹ * a⁻¹) * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * (g * a * g⁻¹ * a⁻¹)
    exact (mem_centralizer_iff.mp (h a a.2) _ (L.mul_mem (hconj b b.2) (L.inv_mem b.2))).symm
  have hker : commutator ↥L ≤ ψ.ker := Subgroup.commutator_le.mpr (fun a _ b _ => hψ a b)
  rw [hperf] at hker
  rw [mem_centralizer_iff]
  intro l hl
  have h1 : ψ ⟨l, hl⟩ = 1 := hker (Subgroup.mem_top _)
  have h2 : g * l * g⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : g * l = l * g := by
    calc g * l = (g * l * g⁻¹ * l⁻¹) * l * g := by group
      _ = l * g := by rw [h2, one_mul]
  exact h3.symm

private lemma exists_pow_mul_eq {Y : Type*} [Group Y] {L : Subgroup Y} {a : Y}
    (ha : ∀ l ∈ L, a * l * a⁻¹ ∈ L) (l : Y) (hl : l ∈ L) (m : ℕ) :
    ∃ l' ∈ L, (l * a) ^ m = l' * a ^ m := by
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨l', hl', h⟩ := ih
    refine ⟨l * (a * l' * a⁻¹), L.mul_mem hl (ha l' hl'), ?_⟩
    rw [pow_succ', h, pow_succ' a]
    group

private theorem exists_pow_eq_one_of_mem_ker {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    {L P : Subgroup Y} (hcore : primeComplementCore (G := Y) p = ⊥) (hL : IsComponentOf L ⊤)
    (hP : IsPGroup p P) (hPL : P ≤ normalizer (L : Set Y)) {y : Y} (hy : y ∈ L ⊔ P)
    (hyc : y ∈ centralizer (L : Set Y)) : ∃ k : ℕ, y ^ p ^ k = 1 := by
  have hmul : (↑(L ⊔ P) : Set Y) = (L : Set Y) * (P : Set Y) :=
    coe_mul_of_right_le_normalizer_left L P hPL
  obtain ⟨l, hl, a, ha, rfl⟩ : ∃ l ∈ L, ∃ a ∈ P, l * a = y := by
    have h : y ∈ (↑(L ⊔ P) : Set Y) := hy
    rw [hmul] at h
    exact h
  obtain ⟨k, hk⟩ := hP ⟨a, ha⟩
  have hk' : a ^ p ^ k = 1 := congrArg Subtype.val hk
  obtain ⟨l', hl', hpow⟩ := exists_pow_mul_eq
    (fun l hl => (mem_normalizer_iff.mp (hPL ha) l).mp hl) l hl (p ^ k)
  have hmem : (l * a) ^ p ^ k ∈ centralizer (L : Set Y) := Subgroup.pow_mem _ hyc _
  rw [hpow, hk', mul_one] at hmem
  have hZ := CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf (Fact.out : p.Prime) hcore hL
  have hcen : (⟨l', hl'⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro m
    exact Subtype.ext (mem_centralizer_iff.mp hmem m m.2)
  obtain ⟨j, hj⟩ := hZ ⟨⟨l', hl'⟩, hcen⟩
  have hj' : l' ^ p ^ j = 1 := congrArg (fun z : ↥(center ↥L) => ((z : ↥L) : Y)) hj
  refine ⟨k + j, ?_⟩
  rw [pow_add, pow_mul, hpow, hk', mul_one]
  exact hj'

private def kerAct {Y : Type*} [Group Y] (L P : Subgroup Y) : Subgroup ↥(L ⊔ P) :=
  (centralizer (L : Set Y)).subgroupOf (L ⊔ P)

private lemma kerAct_normal {Y : Type*} [Group Y] {L P : Subgroup Y}
    (hN : L ⊔ P ≤ normalizer (L : Set Y)) : (kerAct L P).Normal where
  conj_mem := by
    rintro ⟨n, hnN⟩ hn ⟨g, hgN⟩
    have hn' : n ∈ centralizer (L : Set Y) := hn
    show g * n * g⁻¹ ∈ centralizer (L : Set Y)
    rw [mem_centralizer_iff]
    intro l hl
    have hg : g ∈ normalizer (L : Set Y) := hN hgN
    have hl' : g⁻¹ * l * g ∈ L := (mem_normalizer_iff''.mp hg l).mp hl
    have hc := mem_centralizer_iff.mp hn' _ hl'
    calc l * (g * n * g⁻¹) = g * ((g⁻¹ * l * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * l * g)) * g⁻¹ := by rw [hc]
      _ = (g * n * g⁻¹) * l := by group

structure IsAlmostSimpleOf (p : ℕ) {Y : Type} [Group Y] [Finite Y] (L P : Subgroup Y) {X : Type}
    [Group X] [Finite X] (π : ↥(L ⊔ P) →* X) (K : Subgroup X) (Q : Sylow p X) : Prop where
  surj : Function.Surjective π
  K_eq : K = (L.subgroupOf (L ⊔ P)).map π
  Q_eq : (Q : Subgroup X) = (P.subgroupOf (L ⊔ P)).map π
  ker_iff : ∀ n : ↥(L ⊔ P), π n = 1 ↔ (n : Y) ∈ centralizer (L : Set Y)
  ker_le : ∀ n : ↥(L ⊔ P), (n : Y) ∈ centralizer (L : Set Y) → (n : Y) ∈ P
  normal : K.Normal
  simple : IsSimpleGroup K
  nonab : ∃ a b : K, a * b ≠ b * a
  catalog : IsCatalogGroup K
  cent : centralizer (K : Set X) = ⊥
  dvd : p ∣ Nat.card K
  sup : K ⊔ (Q : Subgroup X) = ⊤

theorem exists_almostSimple {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y]
    (hcore : primeComplementCore (G := Y) p = ⊥) (hcat : CatalogSimpleSections Y)
    {L P : Subgroup Y} (hL : IsComponentOf L ⊤) (hsyl : ∃ S : Sylow p Y, (S : Subgroup Y) = P)
    (hPL : P ≤ normalizer (L : Set Y)) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (π : ↥(L ⊔ P) →* X) (K : Subgroup X)
      (Q : Sylow p X), IsAlmostSimpleOf p L P π K Q := by
  obtain ⟨S, rfl⟩ := hsyl
  have hN : L ⊔ (S : Subgroup Y) ≤ normalizer (L : Set Y) := sup_le le_normalizer hPL
  obtain ⟨Cn, hCn_mem, hCnN⟩ : ∃ Cn : Subgroup ↥(L ⊔ (S : Subgroup Y)),
      (∀ n, n ∈ Cn ↔ (n : Y) ∈ centralizer (L : Set Y)) ∧ Cn.Normal :=
    ⟨kerAct L S, fun n => Iff.rfl, kerAct_normal hN⟩
  haveI := hCnN
  have hLN : L ≤ L ⊔ (S : Subgroup Y) := le_sup_left
  have hSN : (S : Subgroup Y) ≤ L ⊔ (S : Subgroup Y) := le_sup_right
  have hπs : Function.Surjective (QuotientGroup.mk' Cn) := QuotientGroup.mk'_surjective Cn
  let f₀ : ↥L →* (↥(L ⊔ (S : Subgroup Y)) ⧸ Cn) :=
    (QuotientGroup.mk' Cn).comp (Subgroup.inclusion hLN)
  have hker : f₀.ker = center ↥L := by
    ext l
    rw [MonoidHom.mem_ker, mem_center_iff]
    have h1 : f₀ l = 1 ↔ (l : Y) ∈ centralizer (L : Set Y) :=
      (QuotientGroup.eq_one_iff (Subgroup.inclusion hLN l)).trans (hCn_mem _)
    rw [h1, mem_centralizer_iff]
    constructor
    · intro h m
      exact Subtype.ext (h m m.2)
    · intro h m hm
      exact congrArg Subtype.val (h ⟨m, hm⟩)
  have hK : f₀.range = (L.subgroupOf (L ⊔ (S : Subgroup Y))).map (QuotientGroup.mk' Cn) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLN l, mem_subgroupOf.mpr l.2, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, mem_subgroupOf.mp hn⟩, rfl⟩
  let e : (↥L ⧸ center ↥L) ≃* ↥f₀.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange f₀)
  haveI : IsSimpleGroup (↥L ⧸ center ↥L) := hL.2.2.2
  haveI hsimple : IsSimpleGroup ↥f₀.range := e.symm.isSimpleGroup
  have hnonab : ∃ a b : ↥f₀.range, a * b ≠ b * a := by
    by_contra hcon
    push_neg at hcon
    have h1 : commutator ↥L ≤ center ↥L := by
      rw [← hker]
      refine Subgroup.commutator_le.mpr (fun a _ b _ => ?_)
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hcon ⟨f₀ a, a, rfl⟩ ⟨f₀ b, b, rfl⟩)
    rw [hL.2.2.1] at h1
    have h2 : f₀.ker = ⊤ := by rw [hker]; exact top_le_iff.mp h1
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥f₀.range)
    obtain ⟨l, hl⟩ := x.2
    have h3 : f₀ l = 1 := by
      have : l ∈ f₀.ker := by rw [h2]; trivial
      exact this
    apply hx
    apply Subtype.ext
    rw [← hl, h3]
    rfl
  have hcatalog : IsCatalogGroup ↥f₀.range :=
    hcat.surjective_image L f₀.rangeRestrict f₀.rangeRestrict_surjective hnonab
  have hker_le : ∀ n : ↥(L ⊔ (S : Subgroup Y)), (n : Y) ∈ centralizer (L : Set Y) →
      (n : Y) ∈ (S : Subgroup Y) := by
    intro n hn
    have hpg : IsPGroup p ↥Cn := by
      intro c
      obtain ⟨k, hk⟩ := exists_pow_eq_one_of_mem_ker hcore hL S.isPGroup' hPL c.1.2
        ((hCn_mem c.1).mp c.2)
      exact ⟨k, Subtype.ext (Subtype.ext hk)⟩
    have hle := IsPGroup.le_sylow_of_normal hpg (S.subtype hSN)
    exact hle ((hCn_mem n).mpr hn)
  have hcent : centralizer (f₀.range : Set (↥(L ⊔ (S : Subgroup Y)) ⧸ Cn)) = ⊥ := by
    rw [eq_bot_iff_forall]
    intro y hy
    obtain ⟨g, rfl⟩ := hπs y
    have hg : (g : Y) ∈ centralizer (L : Set Y) := by
      refine perfect_fix hL.2.2.1 (hN g.2) (fun l hl => ?_)
      have hlN : l ∈ L ⊔ (S : Subgroup Y) := hLN hl
      have hmemK : QuotientGroup.mk' Cn ⟨l, hlN⟩ ∈ f₀.range := ⟨⟨l, hl⟩, rfl⟩
      have hcomm := mem_centralizer_iff.mp hy _ hmemK
      have h1 : QuotientGroup.mk' Cn ⁅g, ⟨l, hlN⟩⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm.symm
      exact (hCn_mem _).mp ((QuotientGroup.eq_one_iff _).mp h1)
    exact (QuotientGroup.eq_one_iff g).mpr ((hCn_mem g).mpr hg)
  have hdvd : p ∣ Nat.card ↥f₀.range := by
    rw [← Nat.card_congr e.toEquiv]
    exact CFSG.AGLEmbedding.prime_dvd_card_center_quotient_of_isComponentOf (Fact.out : p.Prime)
      hcore hL
  have hsup : f₀.range ⊔ (Sylow.mapSurjective hπs (S.subtype hSN) : Subgroup _) = ⊤ := by
    rw [hK, Sylow.coe_mapSurjective, Sylow.coe_subtype, ← Subgroup.map_sup,
      ← subgroupOf_sup hLN hSN, subgroupOf_self, Subgroup.map_top,
      MonoidHom.range_eq_top.mpr hπs]
  exact ⟨_, inferInstance, inferInstance, QuotientGroup.mk' Cn, f₀.range,
    Sylow.mapSurjective hπs (S.subtype hSN),
    { surj := hπs
      K_eq := hK
      Q_eq := rfl
      ker_iff := fun n => (QuotientGroup.eq_one_iff n).trans (hCn_mem n)
      ker_le := hker_le
      normal := by
        rw [hK]
        exact Subgroup.Normal.map ((normal_subgroupOf_iff_le_normalizer hLN).mpr hN) _ hπs
      simple := hsimple
      nonab := hnonab
      catalog := hcatalog
      cent := hcent
      dvd := hdvd
      sup := hsup }⟩

theorem IsAlmostSimpleOf.weakClosed_transfer {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L P : Subgroup Y}
    {X : Type} [Group X] [Finite X] {π : ↥(L ⊔ P) →* X} {K : Subgroup X} {Q : Sylow p X}
    (hπ : IsAlmostSimpleOf p L P π K Q) {A : Subgroup Y} (hA : A ≤ P)
    (hwc : ∀ g : Y, A.map (MulAut.conj g).toMonoidHom ≤ P → A.map (MulAut.conj g).toMonoidHom = A) :
    ∀ g : X, ((A.subgroupOf (L ⊔ P)).map π).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup X) →
      ((A.subgroupOf (L ⊔ P)).map π).map (MulAut.conj g).toMonoidHom = (A.subgroupOf (L ⊔ P)).map π := by
  intro g hg
  obtain ⟨g₀, rfl⟩ := hπ.surj g
  have h1 : A.map (MulAut.conj (g₀ : Y)).toMonoidHom ≤ P := by
    rintro _ ⟨a, ha, rfl⟩
    have haN : a ∈ L ⊔ P := (le_sup_right : P ≤ L ⊔ P) (hA ha)
    have hmem : π (g₀ * ⟨a, haN⟩ * g₀⁻¹) ∈ (Q : Subgroup X) := by
      apply hg
      exact ⟨π ⟨a, haN⟩, ⟨⟨a, haN⟩, mem_subgroupOf.mpr ha, rfl⟩, by simp⟩
    rw [hπ.Q_eq] at hmem
    obtain ⟨b, hb, hbeq⟩ := hmem
    have hb' : (b : Y) ∈ P := mem_subgroupOf.mp hb
    have hker : π (b⁻¹ * (g₀ * ⟨a, haN⟩ * g₀⁻¹)) = 1 := by
      rw [map_mul, map_inv, hbeq, inv_mul_cancel]
    have hP' : ((b⁻¹ * (g₀ * ⟨a, haN⟩ * g₀⁻¹) : ↥(L ⊔ P)) : Y) ∈ P :=
      hπ.ker_le _ ((hπ.ker_iff _).mp hker)
    have hP'' : (b : Y)⁻¹ * ((g₀ : Y) * a * (g₀ : Y)⁻¹) ∈ P := hP'
    have h4 : (g₀ : Y) * a * (g₀ : Y)⁻¹ = (b : Y) * ((b : Y)⁻¹ * ((g₀ : Y) * a * (g₀ : Y)⁻¹)) := by
      group
    show (g₀ : Y) * a * (g₀ : Y)⁻¹ ∈ P
    rw [h4]
    exact P.mul_mem hb' hP''
  have h2 : A.map (MulAut.conj (g₀ : Y)).toMonoidHom = A := hwc g₀ h1
  have h3 : ∀ a ∈ A, (g₀ : Y) * a * (g₀ : Y)⁻¹ ∈ A := fun a ha => by
    have : (g₀ : Y) * a * (g₀ : Y)⁻¹ ∈ A.map (MulAut.conj (g₀ : Y)).toMonoidHom := ⟨a, ha, rfl⟩
    rwa [h2] at this
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨_, ⟨a', ha', rfl⟩, rfl⟩
    refine ⟨g₀ * a' * g₀⁻¹, mem_subgroupOf.mpr ?_, ?_⟩
    · exact h3 _ (mem_subgroupOf.mp ha')
    · simp
  · exact (Subgroup.card_map_of_injective (MulAut.conj (π g₀)).injective).ge

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

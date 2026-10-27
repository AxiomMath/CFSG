module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.Open.RankThreeDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row28One

variable {X : Type} [Group X] [Finite X]

theorem exists_isElemAbelian_normalizer_le {Y : Type} [Group Y] [Finite Y] {B : Subgroup Y}
    (hB3 : IsPGroup 3 B) (hB : B ≠ ⊥) :
    ∃ F : Subgroup Y, F ≤ B ∧ F ≠ ⊥ ∧ IsElemAbelian 3 F ∧
      Subgroup.normalizer (B : Set Y) ≤ Subgroup.normalizer (F : Set Y) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let F : Subgroup Y :=
    { carrier := {x | x ∈ B ∧ (∀ b ∈ B, x * b = b * x) ∧ x ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨haB, hac, ha3⟩ ⟨hbB, hbc, hb3⟩
        refine ⟨B.mul_mem haB hbB, fun c hc => ?_, ?_⟩
        · calc a * b * c = a * (b * c) := mul_assoc _ _ _
            _ = a * (c * b) := by rw [hbc c hc]
            _ = a * c * b := (mul_assoc _ _ _).symm
            _ = c * a * b := by rw [hac c hc]
            _ = c * (a * b) := mul_assoc _ _ _
        · have hcomm : Commute a b := hac b hbB
          rw [hcomm.mul_pow, ha3, hb3, one_mul]
      one_mem' := ⟨B.one_mem, fun b _ => by simp, one_pow 3⟩
      inv_mem' := by
        rintro a ⟨haB, hac, ha3⟩
        refine ⟨B.inv_mem haB, fun c hc => ?_, ?_⟩
        · have h1 := hac c hc
          calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * c) * a⁻¹ := by rw [h1]
            _ = c * a⁻¹ := by group
        · rw [inv_pow, ha3, inv_one] }
  have hFB : F ≤ B := fun x hx => hx.1
  have hFea : IsElemAbelian 3 F :=
    ⟨⟨⟨fun a b => Subtype.ext (a.2.2.1 b.1 (hFB b.2))⟩⟩, fun x hx => hx.2.2⟩
  have hF0 : F ≠ ⊥ := by
    haveI : Nontrivial ↥B := (Subgroup.nontrivial_iff_ne_bot B).2 hB
    haveI : Nontrivial ↥(Subgroup.center ↥B) := hB3.center_nontrivial
    have hcp : IsPGroup 3 ↥(Subgroup.center ↥B) := hB3.to_subgroup _
    have hdvd : 3 ∣ Nat.card ↥(Subgroup.center ↥B) := by
      rcases hcp.card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card.ne')
      · exact h
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
    have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    have hy : ((x : ↥B) : Y) ∈ F := by
      refine ⟨(x : ↥B).2, fun b hb => ?_, ?_⟩
      · have := Subgroup.mem_center_iff.1 x.2 ⟨b, hb⟩
        exact (congrArg Subtype.val this).symm
      · have := congrArg (fun z : ↥(Subgroup.center ↥B) => (((z : ↥B)) : Y)) hx3
        simpa using this
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hy
    have hx1 : x = 1 := Subtype.ext (Subtype.ext hy)
    rw [hx1, orderOf_one] at hx
    norm_num at hx
  have key : ∀ n ∈ Subgroup.normalizer (B : Set Y), ∀ y ∈ F, n * y * n⁻¹ ∈ F := by
    intro n hn y hy
    obtain ⟨hyB, hyc, hy3⟩ := hy
    refine ⟨(Subgroup.mem_normalizer_iff.1 hn y).1 hyB, fun b hb => ?_, ?_⟩
    · have hb' : n⁻¹ * b * n ∈ B := by
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) b).1 hb
        simpa using this
      have h1 := hyc _ hb'
      calc n * y * n⁻¹ * b = n * (y * (n⁻¹ * b * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * b * n) * y) * n⁻¹ := by rw [h1]
        _ = b * (n * y * n⁻¹) := by group
    · rw [conj_pow, hy3]; group
  refine ⟨F, hFB, hF0, hFea, fun n hn => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => key n hn y hy
  · intro hy
    have := key n⁻¹ (inv_mem hn) _ hy
    simpa [mul_assoc] using this

end Row28One

section Row28Three

variable {X : Type} [Group X] [Finite X] {G : Type} [Group G] [Finite G]

theorem isSolvable_mulAut_of_card_three {Y : Type} [Group Y] {A : Subgroup Y} (h : Nat.card A = 3) :
    Group.IsSolvable (MulAut ↥A) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [h]; norm_num)
  haveI : IsCyclic A := isCyclic_of_prime_card (p := 3) h
  haveI : Group.IsSolvable (ZMod (Nat.card ↥A))ˣ := inferInstance
  exact solvable_of_solvable_injective (f := (IsCyclic.mulAutMulEquiv A).toMonoidHom)
    (IsCyclic.mulAutMulEquiv A).injective

end Row28Three

section Row28Cyc

variable {X : Type} [Group X] [Finite X] {G : Type} [Group G] [Finite G]

theorem cMHat_normal {L : Subgroup X} (hL : L.Normal) : (cMHat L).Normal := by
  unfold cMHat cMBar
  haveI : (barO2 L).Normal :=
    hL.map (QuotientGroup.mk' (CFSG.pCore 2 X)) (QuotientGroup.mk'_surjective _)
  haveI : (Subgroup.centralizer ((barO2 L : Subgroup (X ⧸ CFSG.pCore 2 X)) :
      Set (X ⧸ CFSG.pCore 2 X))).Normal := inferInstance
  exact Subgroup.Normal.comap inferInstance _

theorem pRank_three_eq_one_of_cyclic_sylow {I Q : Subgroup X} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I)
    (hc : IsCyclic ↥Q) (h1 : 1 ≤ CFSG.Open.pRank 3 I) : CFSG.Open.pRank 3 I = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ h1
  refine CFSG.SectionRank.pRank_le (by norm_num) ?_
  intro E hEI hE
  have hE3 : IsPGroup 3 E := fun x => ⟨1, by
    have := hE.2 x x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨S, hS⟩ := (hE3.comap_subtype (K := I)).exists_le_sylow
  have hS' : CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup ↥I).map I.subtype) I := ⟨S, rfl⟩
  have hES : E ≤ (S : Subgroup ↥I).map I.subtype := fun x hx => ⟨⟨x, hEI hx⟩, hS hx, rfl⟩
  obtain ⟨k₀, hk₀, hconj⟩ := hQ.exists_mem_conj hS'
  let f : ↥E →* ↥Q :=
    ((MulAut.conj k₀⁻¹).toMonoidHom.comp E.subtype).codRestrict Q (fun x => by
      have := (hconj (x : X)).1 (hES x.2)
      simpa [MulAut.conj_apply] using this)
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    apply Subtype.ext
    simpa [f, MulAut.conj_apply, mul_assoc] using this
  haveI : IsCyclic E := isCyclic_of_injective f hf
  have hpow : ∀ x : E, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hE.2 x x.2)
  have hexp : Monoid.exponent E ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  have hdvd : Nat.card E ∣ 3 := by rw [← IsCyclic.exponent_eq_card]; exact hexp
  simpa using Nat.le_of_dvd (by norm_num) hdvd

end Row28Cyc

section Row28NonG

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_centralizer_le {M S : Subgroup G}
    (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 M)
    (hC : Subgroup.centralizer (S : Set G) ≤ M)
    (h7 : 7 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (S : Set G))) :
    Subgroup.normalizer (S : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  refine hstrong.2.2 g hgM ?_
  refine h7.trans (Subgroup.card_dvd_of_le (le_inf inf_le_left ?_))
  intro x hx
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.1 hx
  have hconj : g⁻¹ * x * g ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : g * s * g⁻¹ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 hg s).1 hs
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.1 hxC) _ hs'
    calc s * (g⁻¹ * x * g) = g⁻¹ * ((g * s * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * s * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * s := by group
  exact ⟨g⁻¹ * x * g, hC hconj, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem mem_uniqueSet_of_D {M : Subgroup G} (hM : rankThreeIsMaxTwoLocal M) {P D A : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M) (hDP : D ≤ P) (hDZ : ∀ d ∈ D, ∀ y ∈ P, d * y = y * d)
    (hAD : A ≤ D) (hNA : Subgroup.normalizer (A : Set G) ≤ M) (hDU : D ∈ uniqueSet M) :
    A ∈ uniqueSet M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM : A ≤ M := hAD.trans hDU.1
  refine ⟨hAM, fun g hAg => ?_⟩
  set B : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom with hBdef
  have hBM : B ≤ M := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨m, hm, hma⟩ := Subgroup.mem_map.1 (hAg ha)
    have : g * m * g⁻¹ = a := by simpa [MulAut.conj_apply] using hma
    have hb : g⁻¹ * a * g = m := by rw [← this]; group
    simpa [MulAut.conj_apply, hb] using hm
  have hB3 : IsPGroup 3 B := (hP.isPGroup.to_le (hAD.trans hDP)).map (MulAut.conj g⁻¹).toMonoidHom
  have hB3' : IsPGroup 3 (B.subgroupOf M) := hB3.comap_subtype
  obtain ⟨Q, hQ⟩ := hB3'.exists_le_sylow
  have hP' : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup ↥M).map M.subtype) M := ⟨Q, rfl⟩
  have hBP' : B ≤ (Q : Subgroup ↥M).map M.subtype := by
    intro b hb
    exact ⟨⟨b, hBM hb⟩, hQ (by exact hb), rfl⟩
  obtain ⟨k, hkM, hk⟩ := hP.exists_mem_conj hP'
  have hkB : ∀ b ∈ B, k⁻¹ * b * k ∈ P := fun b hb => (hk b).1 (hBP' hb)
  set h : G := g * k with hh
  have hcomm : ∀ d ∈ D, h * d * h⁻¹ ∈ M := by
    intro d hd
    have hmem : h * d * h⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hb : g⁻¹ * a * g ∈ B := ⟨a, ha, by simp [MulAut.conj_apply]⟩
      have h1 := hDZ d hd _ (hkB _ hb)
      calc a * (h * d * h⁻¹) = h * ((h⁻¹ * a * h) * d) * h⁻¹ := by group
        _ = h * (d * (h⁻¹ * a * h)) * h⁻¹ := by
            have e : h⁻¹ * a * h = k⁻¹ * (g⁻¹ * a * g) * k := by rw [hh]; group
            rw [e, ← h1]
        _ = h * d * h⁻¹ * a := by group
    exact hNA ((Subgroup.centralizer_le_normalizer (A : Set G)) hmem)
  have hDle : D ≤ M.map (MulAut.conj h⁻¹).toMonoidHom := by
    intro d hd
    exact ⟨h * d * h⁻¹, hcomm d hd, by simp [MulAut.conj_apply]; group⟩
  have hMh := hDU.2 h⁻¹ hDle
  have hhM : h ∈ M := by
    have : h⁻¹ ∈ Subgroup.normalizer (M : Set G) := mem_normalizer_iff_map_conj_eq.2 hMh
    rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing M hM] at this
    simpa using M.inv_mem this
  have hgM : g ∈ M := by
    have : g = h * k⁻¹ := by rw [hh]; group
    rw [this]
    exact M.mul_mem hhM (M.inv_mem hkM)
  exact mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hgM)

theorem pCoreOf_centralizer_ne_bot {M : Subgroup G} {d : ↥M} {u : ↥M}
    (hu : u ∈ CFSG.pCore 2 ↥M) (hu1 : u ≠ 1) (hdu : (d : ↥M) * u = u * d) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({(d : G)} : Set G) ⊓ M) ≠ ⊥ := by
  set H : Subgroup G := Subgroup.centralizer ({(d : G)} : Set G) ⊓ M with hH
  have huH : (u : G) ∈ H := by
    refine Subgroup.mem_inf.2 ⟨?_, u.2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have := congrArg Subtype.val hdu
    simpa using this
  have hHM : H ≤ M := inf_le_right
  let f : ↥H →* ↥M := Subgroup.inclusion hHM
  have hf : Function.Injective f := Subgroup.inclusion_injective hHM
  have hNn : ((CFSG.pCore 2 ↥M).comap f).Normal := Subgroup.Normal.comap inferInstance f
  have hNp : IsPGroup 2 ((CFSG.pCore 2 ↥M).comap f) :=
    (CFSG.pCore_isPGroup).comap_of_injective f hf
  have hle : (CFSG.pCore 2 ↥M).comap f ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hNn, hNp⟩
  have hmem : (⟨(u : G), huH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := hle hu
  intro hbot
  have : (u : G) ∈ CFSG.Open.pCoreOf 2 H := ⟨⟨(u : G), huH⟩, hmem, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hu1 (Subtype.ext this)

end Row28NonG

section Row28NonAssembly

variable {X : Type} [Group X] [Finite X] {G : Type} [Group G] [Finite G]

theorem isCyclic_conjSub_iff (i : X) (Q : Subgroup X) : IsCyclic ↥(conjSub i Q) ↔ IsCyclic ↥Q := by
  have e : ↥Q ≃* ↥(conjSub i Q) :=
    Q.equivMapOfInjective (MulAut.conj i).toMonoidHom (MulAut.conj i).injective
  exact ⟨fun h => isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective,
    fun h => isCyclic_of_surjective e.toMonoidHom e.surjective⟩

theorem normalizer_le_gamma {R B : Subgroup G} (hBR : B ≤ R) (hB : 1 ≤ CFSG.Open.pRank 3 B) :
    Subgroup.normalizer (B : Set G) ≤ CFSG.Open.rankThreeGamma 1 3 R :=
  le_sSup ⟨B, hBR, hB, rfl⟩

end Row28NonAssembly

section Row28NonMain

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_map_subtype_top {M : Subgroup G} {P : Subgroup ↥M}
    (h : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) : CFSG.ABGLocalTools.IsSylowOf 3 (P.map M.subtype) M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop : (⊤ : Subgroup ↥M).map M.subtype = M := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have h1 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) M (A := P) (B := ⊤)).mpr h
  rwa [htop] at h1

theorem isElemAbelian_map_subtype {M : Subgroup G} {D : Subgroup ↥M} {p : ℕ}
    (h : IsElemAbelian p D) : IsElemAbelian p (D.map M.subtype) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    have := h.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
    show (a : G) * b = b * a
    rw [← ha, ← hb]
    exact congrArg (fun z : D => ((z : ↥M) : G)) this
  · obtain ⟨x', hx', rfl⟩ := hx
    have := h.2 x' hx'
    show ((x' : ↥M) : G) ^ p = 1
    rw [← Subgroup.coe_pow, this]
    rfl

theorem orderOf_eq_three_of_card_three {Y : Type} [Group Y] {A B : Subgroup Y} (hA : Nat.card A = 3)
    (hB : Nat.card B = 3) (hAB1 : ∀ x ∈ A ⊓ B, x = 1) {a b : Y} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hb : b ∈ B) (hb1 : b ≠ 1) (hab : a * b = b * a) :
    orderOf a = 3 ∧ orderOf b = 3 ∧ orderOf (a * b) = 3 := by
  have hoa : orderOf a = 3 := by
    have h1 : orderOf a ∣ 3 := by
      have := orderOf_dvd_natCard (⟨a, ha⟩ : ↥A)
      rwa [Subgroup.orderOf_mk, hA] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) ha1
    · exact h
  have hob : orderOf b = 3 := by
    have h1 : orderOf b ∣ 3 := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : ↥B)
      rwa [Subgroup.orderOf_mk, hB] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hb1
    · exact h
  refine ⟨hoa, hob, ?_⟩
  have hcomm : Commute a b := hab
  have ha3 : a ^ 3 = 1 := hoa ▸ pow_orderOf_eq_one a
  have hb3 : b ^ 3 = 1 := hob ▸ pow_orderOf_eq_one b
  have hpow : (a * b) ^ 3 = 1 := by rw [hcomm.mul_pow, ha3, hb3]; simp
  have hne : a * b ≠ 1 := by
    intro h
    have hbA : b ∈ A := by
      rw [eq_inv_of_mul_eq_one_right h]
      exact A.inv_mem ha
    exact hb1 (hAB1 b ⟨hbA, hb⟩)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime hpow hne

theorem dvd_card_inf_centralizer {M : Subgroup G} {x d : ↥M} (hx : orderOf x = 7)
    (hxd : x * d = d * x) : 7 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ({(d : G)} : Set G)) := by
  have hle : Subgroup.zpowers (x : G) ≤ M ⊓ Subgroup.centralizer ({(d : G)} : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (congrArg Subtype.val hxd).symm
  have hc : Nat.card (Subgroup.zpowers (x : G)) = 7 := by
    rw [Nat.card_zpowers]
    have : orderOf (x : G) = orderOf x := Subgroup.orderOf_coe x
    rw [this, hx]
  rw [← hc]
  exact Subgroup.card_dvd_of_le hle

end Row28NonMain

end CFSG.LocalAnalysis.RankThreeUC.S15

module

public import CFSG.GH74.Uniqueness.SU.SU4L181
public import CFSG.GH74.Uniqueness.SU.SU4Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem gammaElem_le {S K : Subgroup G}
    (h : ∀ E : Subgroup G, E ≤ S → Open.IsElemAbelian 2 E → 2 ≤ Open.pRank 2 E →
      3 ≤ Open.pRank 2 (centralizer (E : Set G) ⊓ S) → normalizer (E : Set G) ≤ K) :
    gammaElem S ≤ K := by
  unfold gammaElem
  exact iSup_le fun E => iSup_le fun h1 => iSup_le fun h2 => iSup_le fun h3 =>
    iSup_le fun h4 => h E h1 h2 h3 h4

theorem normalizer_le_gammaElem {S E : Subgroup G} (h1 : E ≤ S) (h2 : Open.IsElemAbelian 2 E)
    (h3 : 2 ≤ Open.pRank 2 E) (h4 : 3 ≤ Open.pRank 2 (centralizer (E : Set G) ⊓ S)) :
    normalizer (E : Set G) ≤ gammaElem S := by
  unfold gammaElem
  exact le_iSup_of_le E (le_iSup_of_le h1 (le_iSup_of_le h2 (le_iSup_of_le h3
    (le_iSup_of_le h4 le_rfl))))

omit [Finite G] in
theorem conjSub_eq_of_mem_normalizer {g : G} {E : Subgroup G} (hg : g ∈ normalizer (E : Set G)) :
    conjSub g E = E := by
  ext y
  rw [mem_conjSub]
  have h := Subgroup.mem_normalizer_iff.mp (inv_mem hg) y
  simpa using h.symm

omit [Finite G] in
theorem mem_compSet_mono {X Y U E : Subgroup G} (h : X ≤ Y) (hE : E ∈ compSet X U) :
    E ∈ compSet Y U := by
  have := mem_compSet_conj_of_le (g := 1) (X := X) (Y := Y) (by rwa [conjSub_one]) hE
  simpa [conjSub_one] using this

theorem Setup18Core.isNormalEp2 {S : Sylow 2 G} {U : Subgroup G} (h : Setup18Core S U) :
    SU1.IsNormalEp2 2 (S : Subgroup G) U := ⟨h.four.1, h.normal, h.four.2.1, h.four.2.2⟩

theorem Setup18Core.isPGroup {S : Sylow 2 G} {U : Subgroup G} (_h : Setup18Core S U) :
    IsPGroup 2 (S : Subgroup G) := S.isPGroup'

theorem normalizer_le_stabComp {S : Sylow 2 G} {U : Subgroup G} (h : Setup18Core S U)
    {E : Subgroup G} (hE2 : 2 ≤ Open.pRank 2 E)
    (hE3 : 3 ≤ Open.pRank 2 (centralizer (E : Set G) ⊓ (S : Subgroup G))) :
    normalizer (E : Set G) ≤ stabComp U := by
  obtain ⟨F, hFle, hF, hFcard⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hE3
  have hrel := (SU1.ig10_20_ii Nat.prime_two h.isPGroup h.isNormalEp2).2.1
  have hFS : F ≤ (S : Subgroup G) := hFle.trans inf_le_right
  have hrelF : (centralizer (U : Set G)).relIndex F ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hFS (SU1.relIndex_ne_zero_of_finite _ _)).trans hrel
  have hmul := Subgroup.relIndex_mul_card (H := centralizer (U : Set G)) (K := F)
  have h4 : 4 ≤ Nat.card ↥(centralizer (U : Set G) ⊓ F) := by
    rw [hFcard] at hmul
    have h5 : (centralizer (U : Set G)).relIndex F * Nat.card ↥(centralizer (U : Set G) ⊓ F) ≤
        2 * Nat.card ↥(centralizer (U : Set G) ⊓ F) := Nat.mul_le_mul_right _ hrelF
    omega
  obtain ⟨V, hVle, hVel, hVcard⟩ := SU1.exists_vertex_le Nat.prime_two
    (SU1.IsElemAbelian.mono inf_le_right hF) (by simpa using h4)
  have hVU : IsFour ⊤ V := ⟨le_top, hVel, hVcard⟩
  have hU4 : IsFour ⊤ U := ⟨le_top, h.four.2.1, h.four.2.2⟩
  have hVcomp : V ∈ compSet ⊤ U := by
    refine mem_compSet_of_commute hU4 hVU (fun a ha b hb => ?_)
    exact Subgroup.mem_centralizer_iff.mp (hVle hb).1 a ha
  have hall : ∀ E₀ : Subgroup G, IsFour ⊤ E₀ → E₀ ≤ E → E₀ ∈ compSet ⊤ U := by
    intro E₀ hE₀ hE₀E
    have : E₀ ∈ compSet ⊤ V := by
      refine mem_compSet_of_commute hVU hE₀ (fun a ha b hb => ?_)
      have haF : a ∈ F := (hVle ha).2
      exact (Subgroup.mem_centralizer_iff.mp (hFle haF).1 b (hE₀E hb)).symm
    exact compSet_trans hVcomp this
  obtain ⟨E₀, hE₀E, hE₀el, hE₀card⟩ := SU1.exists_isElemAbelian_of_le_pRank Nat.prime_two hE2
  have hE₀4 : IsFour ⊤ E₀ := ⟨le_top, hE₀el, hE₀card⟩
  intro g hg
  refine mem_stabComp.mpr (permutesComp_of_mem (A := E₀) (hall E₀ hE₀4 hE₀E) ?_)
  refine hall _ (isFour_conjSub (g := g) (X := ⊤) (Y := ⊤) le_top hE₀4) ?_
  rw [← conjSub_eq_of_mem_normalizer hg]
  exact conjSub_mono hE₀E

variable {G : Type} [Group G]

theorem normal_oResidual (Y : Type*) [Group Y] : (GLS.oResidual 2 Y).Normal := by
  constructor
  intro n hn g
  unfold GLS.oResidual at hn ⊢
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    apply Subgroup.subset_closure
    have h1 : orderOf ((MulAut.conj g).toMonoidHom x) = orderOf x :=
      orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    have h2 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [h2] at h1
    show Nat.Coprime (orderOf (g * x * g⁻¹)) 2
    rw [h1]
    exact hx
  | one => simp
  | mul a b _ _ iha ihb =>
    have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
    have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ iha

section Finite

variable [Finite G]

theorem exists_odd_order_ne_one (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) :
    ∃ g : G, Nat.Coprime (orderOf g) 2 ∧ g ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hP : IsPGroup 2 G := by
    refine IsPGroup.iff_card.mpr ⟨(Nat.card G).primeFactorsList.length, ?_⟩
    refine Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := G)).ne' (fun {d} hd hdd => ?_)
    by_contra hd2
    have := Fact.mk hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) d hdd
    have hcop : Nat.Coprime (orderOf x) 2 := by
      rw [hx]
      exact (Nat.coprime_primes hd Nat.prime_two).mpr hd2
    have h1 := hcon x hcop
    rw [h1, orderOf_one] at hx
    exact hd.one_lt.ne hx
  have := hs.toNontrivial
  have hnt : Nontrivial (Subgroup.center G) := hP.center_nontrivial
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center G)
    rw [h] at hz
    exact hz1 (Subtype.ext (Subgroup.mem_bot.mp hz))
  · obtain ⟨a, b, hab⟩ := hn
    have : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem oResidual_top_map_eq_top (hs : IsSimpleGroup G) (hn : ∃ a b : G, a * b ≠ b * a) :
    (GLS.oResidual 2 ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = ⊤ := by
  have hN : ((GLS.oResidual 2 ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).Normal :=
    Subgroup.Normal.map (normal_oResidual _) _ (fun g => ⟨⟨g, trivial⟩, rfl⟩)
  have := hN
  rcases hs.eq_bot_or_eq_top_of_normal
    ((GLS.oResidual 2 ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype) with h | h
  · exfalso
    obtain ⟨g, hg, hg1⟩ := exists_odd_order_ne_one hs hn
    have hmem : g ∈ (GLS.oResidual 2 ↥(⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype := by
      refine ⟨⟨g, trivial⟩, ?_, rfl⟩
      apply Subgroup.subset_closure
      show Nat.Coprime (orderOf (⟨g, trivial⟩ : ↥(⊤ : Subgroup G))) 2
      rw [← Subgroup.orderOf_coe]
      exact hg
    rw [h] at hmem
    exact hg1 (Subgroup.mem_bot.mp hmem)
  · exact h

end Finite

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_compSet {X S U A : Subgroup G} (hS : IsSylowIn X S)
    (hSrk : 3 ≤ Open.pRank 2 S) (hU : SU1.IsNormalEp2 2 S U) (hA : IsFour X A)
    (hAnon : ¬ IsIsolatedVertex X A) : ∃ m ∈ X, conjSub m A ∈ compSet X U := by
  have hB : ∃ B, IsFour X B ∧ (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ B ≠ A := by
    by_contra hcon
    push Not at hcon
    exact hAnon (isIsolatedVertex_iff.mpr ⟨hA, hcon⟩)
  obtain ⟨B, hB4, hBc, hBne⟩ := hB
  have hABel : Open.IsElemAbelian 2 (A ⊔ B) := SU1.IsElemAbelian.sup hA.2.1 hB4.2.1 hBc
  have hABX : A ⊔ B ≤ X := sup_le hA.1 hB4.1
  have hABp : IsPGroup 2 ↥(A ⊔ B) := by
    obtain ⟨k, hk⟩ := SU1.IsElemAbelian.exists_card Nat.prime_two hABel
    exact IsPGroup.of_card hk
  obtain ⟨S', hS', hABS'⟩ := exists_isSylowIn_ge hABX hABp
  obtain ⟨c, hcX, hSc⟩ := hS.exists_conj_eq hS'
  have hU' : SU1.IsNormalEp2 2 S' (conjSub c U) := by
    rw [hSc]
    refine ⟨conjSub_mono hU.1, ?_, isElemAbelian_conjSub hU.2.2.1, ?_⟩
    · exact (conjSub_mono hU.2.1).trans (conjSub_normalizer c U).le
    · rw [card_conjSub]; exact hU.2.2.2
  have hS'rk : 3 ≤ Open.pRank 2 S' := by
    rw [hSc, pRank_conjSub (by norm_num)]; exact hSrk
  have hA' : A ≤ S' := le_sup_left.trans hABS'
  have hB' : B ≤ S' := le_sup_right.trans hABS'
  have hAnon' : ¬ SU1.IsIsolated 2 (⟨A, hA', hA.2.1, hA.2.2⟩ : SU1.Ep2Vertex 2 S') := fun h =>
    h ⟨B, hB', hB4.2.1, hB4.2.2⟩
      ⟨fun e => hBne (congrArg Subtype.val e).symm, hBc⟩
  have hUv : ¬ SU1.IsIsolated 2
      (⟨conjSub c U, hU'.1, hU'.2.2.1, hU'.2.2.2⟩ : SU1.Ep2Vertex 2 S') :=
    SU1.not_isIsolated_of_isNormalEp2 Nat.prime_two hS'.2.1 hS'rk hU' _ rfl
  obtain ⟨-, hall⟩ := SU1.ig10_21_ii Nat.prime_two hS'.2.1 hS'rk ⟨conjSub c U, hU'⟩
  have hreach := hall _ _ hAnon' hUv
  have hcomp : A ∈ compSet S' (conjSub c U) :=
    ⟨⟨hU'.1, hU'.2.2.1, hU'.2.2.2⟩, ⟨hA', hA.2.1, hA.2.2⟩, hreach.symm⟩
  have hcompX : A ∈ compSet X (conjSub c U) := mem_compSet_mono hS'.1 hcomp
  have hcX' : conjSub c⁻¹ X = X := conjSub_self_of_mem (X.inv_mem hcX)
  refine ⟨c⁻¹, X.inv_mem hcX, ?_⟩
  have := (mem_compSet_conj (g := c⁻¹) (X := X) (Y := X) (U := conjSub c U) (E := A) hcX').mp
    hcompX
  rwa [conjSub_inv_conjSub] at this

omit [Finite G] in
theorem exists_conj_mem_compSet_of_two {X U A B : Subgroup G} {g₁ g₂ : G}
    (hX : conjSub g₂⁻¹ X = X) (h₁ : conjSub g₁ A ∈ compSet X U)
    (h₂ : conjSub g₂ B ∈ compSet X U) : conjSub (g₂⁻¹ * g₁) A ∈ compSet X B := by
  have h3 : conjSub g₁ A ∈ compSet X (conjSub g₂ B) := compSet_trans (compSet_symm h₂) h₁
  have h4 := (mem_compSet_conj (g := g₂⁻¹) hX).mp h3
  rwa [conjSub_inv_conjSub, ← conjSub_mul] at h4

theorem lemma183_a {S : Sylow 2 G} {U : Subgroup G} (h : Setup18Core S U) :
    ∀ g ∈ gammaElem (S : Subgroup G), PermutesComp U g := fun _ hg =>
  mem_stabComp.mp (gammaElem_le (K := stabComp U)
    (fun _E _ _ hE2 hE3 => normalizer_le_stabComp h hE2 hE3) hg)

theorem lemma183_b {S : Sylow 2 G} {U : Subgroup G} (h : Setup18Core S U) :
    ∀ V : Subgroup G, ¬ IsIsolatedVertex ⊤ V := by
  intro V hV
  have hX : 3 ≤ Open.pRank 2 (⊤ : Subgroup G) :=
    h.rank.trans (SU1.pRank_mono (by norm_num) le_top)
  obtain ⟨x, z, S', K, hc⟩ := lemma181_core hX hV
  have := oResidual_top_map_eq_top h.simple h.nonab
  exact hc.x_not (by rw [this]; exact Subgroup.mem_top x)

theorem lemma183_c {S : Sylow 2 G} {U : Subgroup G} (h : Setup18Core S U) :
    ∀ A B : Subgroup G, IsFour ⊤ A → IsFour ⊤ B → ∃ g : G, conjSub g A ∈ compSet ⊤ B := by
  intro A B hA hB
  have hS : IsSylowIn (⊤ : Subgroup G) (S : Subgroup G) := sylow_isSylowIn_top S
  obtain ⟨g₁, -, h₁⟩ := exists_conj_mem_compSet hS h.rank h.isNormalEp2 hA (lemma183_b h A)
  obtain ⟨g₂, -, h₂⟩ := exists_conj_mem_compSet hS h.rank h.isNormalEp2 hB (lemma183_b h B)
  exact ⟨g₂⁻¹ * g₁, exists_conj_mem_compSet_of_two (conjSub_top _) h₁ h₂⟩

theorem lemma183_d {S : Sylow 2 G} {U : Subgroup G} (h : Setup18Core S U) :
    (∃ E : Subgroup G, IsFour ⊤ E ∧ E ∉ compSet ⊤ U) → ∃ g : G, ¬ PermutesComp U g := by
  rintro ⟨E, hE, hEn⟩
  have hU : IsFour ⊤ U := ⟨le_top, h.four.2.1, h.four.2.2⟩
  obtain ⟨g, hg⟩ := lemma183_c h E U hE hU
  exact ⟨g, fun hp => hEn (mem_compSet_of_conj_mem hp hg)⟩

theorem lemma183_core : Lemma183CoreStmt := by
  intro G _ _ S U h
  exact ⟨lemma183_a h, lemma183_b h, lemma183_c h, lemma183_d h⟩

theorem lemma183 : Lemma183Stmt := by
  intro G _ _ S U h
  exact lemma183_core G S U h.toSetup18Core

end CFSG.GH74.Uniqueness.SU.SU4

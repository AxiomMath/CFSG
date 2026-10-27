module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Leaves
public import CFSG.LocalAnalysis.GL83PartI.I_32
public import CFSG.LocalAnalysis.GL83PartI.I_33

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open scoped Pointwise

namespace Sec12b

section Generic

variable {G : Type} [Group G] [Finite G]

theorem mul_mem_iSup_of_perm {ι : Sort*} (H : Subgroup G) (K : ι → Subgroup G)
    (hK : ∀ i, ∀ h ∈ H, ∀ k ∈ K i, ∃ k' ∈ K i, ∃ h' ∈ H, h * k = k' * h')
    {v : G} (hv : v ∈ ⨆ i, K i) :
    ∀ h ∈ H, ∃ v' ∈ ⨆ i, K i, ∃ h' ∈ H, h * v = v' * h' := by
  refine Subgroup.iSup_induction K
    (C := fun v => ∀ h ∈ H, ∃ v' ∈ ⨆ i, K i, ∃ h' ∈ H, h * v = v' * h') hv ?_ ?_ ?_
  · intro i k hk h hh
    obtain ⟨k', hk', h', hh', e⟩ := hK i h hh k hk
    exact ⟨k', le_iSup K i hk', h', hh', e⟩
  · intro h hh
    exact ⟨1, one_mem _, h, hh, by simp⟩
  · intro x y hx hy h hh
    obtain ⟨x', hx', h1, hh1, e1⟩ := hx h hh
    obtain ⟨y', hy', h2, hh2, e2⟩ := hy h1 hh1
    exact ⟨x' * y', mul_mem hx' hy', h2, hh2,
      by rw [← mul_assoc, e1, mul_assoc, e2, ← mul_assoc]⟩

theorem pRank_bot {p : ℕ} (hp : 1 < p) : CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := by
  unfold CFSG.Open.pRank
  apply le_antisymm
  · apply csSup_le'
    intro k hk
    obtain ⟨E, hE, -, hcard⟩ := hk
    have hE' : E = ⊥ := le_bot_iff.1 hE
    subst hE'
    rw [Subgroup.card_bot] at hcard
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact h0.le
    · exfalso
      have := Nat.one_lt_pow hpos.ne' hp
      omega
  · exact Nat.zero_le _

theorem cent_le_cent_of_mem {F : Subgroup G} {x : G} (hx : x ∈ F) :
    Subgroup.centralizer (F : Set G) ≤ Subgroup.centralizer ({x} : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hg y hx

theorem layer_le (p : ℕ) (X : Subgroup G) [Finite G] : GLAPLayer p X ≤ X := by
  unfold GLAPLayer
  apply sSup_le
  intro L hL
  exact hL.1

theorem comp_le {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) : L ≤ X :=
  h.1

theorem le_kx {p : ℕ} (x : G) (J : Subgroup G) : J ≤ Kx p J x := by
  unfold Kx
  have h1 : GLBConj 1 J ≤ ⨆ g ∈ GLAPLayer p (Subgroup.centralizer ({x} : Set G)), GLBConj g J :=
    le_iSup₂ (f := fun g _ => GLBConj g J) 1 (one_mem _)
  rwa [gLBConj_one] at h1

theorem kx_le_cent {p : ℕ} {x : G} {J : Subgroup G}
    (hJ : J ≤ Subgroup.centralizer ({x} : Set G)) :
    Kx p J x ≤ Subgroup.centralizer ({x} : Set G) := by
  unfold Kx
  refine iSup₂_le fun g hg => ?_
  have hgC : g ∈ Subgroup.centralizer ({x} : Set G) := layer_le p _ hg
  intro y hy
  rw [mem_gLBConj] at hy
  have hy' : y = g⁻¹ * (g * y * g⁻¹) * g := by group
  rw [hy']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgC) (hJ hy)) hgC

theorem cent_ne_top {m p : ℕ} (hS : GLStanding G m p) {a : G} (ha : a ≠ 1) [Finite G] :
    Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  haveI := hS.simple
  intro htop
  have hac : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top g
    rw [Subgroup.mem_centralizer_iff] at hg
    exact (hg a (Set.mem_singleton a)).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hc | hc
  · rw [hc] at hac
    exact ha (Subgroup.mem_bot.1 hac)
  · obtain ⟨x, y, hxy⟩ := hS.nonabelian
    have hx : x ∈ Subgroup.center G := by
      rw [hc]
      exact Subgroup.mem_top x
    rw [Subgroup.mem_center_iff] at hx
    exact hxy (hx y).symm

end Generic

section Cover

variable {G : Type} [Group G] [Finite G]

theorem mem_mul_glaPPrimeCoreOf_of_barX {p : ℕ} {X J : Subgroup G} (hJX : J ≤ X)
    (hcov : barX p X J = ⊤) {k : G} (hk : k ∈ X) :
    ∃ j ∈ J, ∃ o ∈ GLAPPrimeCoreOf p X, k = j * o := by
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨k, hk⟩ : ↥X) ∈ barX p X J := by
    rw [hcov]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyk⟩ := hmem
  have hyJ : (y : G) ∈ J := Subgroup.mem_subgroupOf.1 hy
  have hos : y⁻¹ * (⟨k, hk⟩ : ↥X) ∈ GLAPPrimeCore p ↥X :=
    (QuotientGroup.eq (s := GLAPPrimeCore p ↥X)).1 hyk
  refine ⟨y, hyJ, ((y⁻¹ * ⟨k, hk⟩ : ↥X) : G), ?_, by simp⟩
  exact Subgroup.mem_map.2 ⟨_, hos, rfl⟩

theorem mul_eq_mul_of_cover {p : ℕ} (hp : p.Prime) {Cx X J M : Subgroup G}
    (hJX : J ≤ X) (hXC : X ≤ Cx) (hN : Cx ≤ Subgroup.normalizer (X : Set G))
    (hcov : barX p X J = ⊤) (hO : GLAPPrimeCoreOf p Cx ≤ M) :
    (J : Set G) * ((M ⊓ Cx : Subgroup G) : Set G) =
      ((M ⊓ Cx : Subgroup G) : Set G) * (J : Set G) := by
  have hnX : (X.subgroupOf Cx).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
  have hOX : GLAPPrimeCoreOf p X ≤ GLAPPrimeCoreOf p Cx :=
    glaPPrimeCoreOf_le_of_normal hp hXC hnX
  have L1 : ∀ c ∈ (M ⊓ Cx : Subgroup G), ∀ j ∈ J,
      c * j ∈ (J : Set G) * ((M ⊓ Cx : Subgroup G) : Set G) := by
    intro c hc j hj
    have hcj : c * j * c⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.1 (hN hc.2) j).1 (hJX hj)
    obtain ⟨j₁, hj₁, o, ho, e⟩ := mem_mul_glaPPrimeCoreOf_of_barX hJX hcov hcj
    have ho' : o ∈ GLAPPrimeCoreOf p Cx := hOX ho
    have hoC : o ∈ (M ⊓ Cx : Subgroup G) :=
      ⟨hO ho', (Subgroup.map_subtype_le _ : GLAPPrimeCoreOf p Cx ≤ Cx) ho'⟩
    refine Set.mem_mul.2 ⟨j₁, hj₁, o * c, Subgroup.mul_mem _ hoC hc, ?_⟩
    calc j₁ * (o * c) = (j₁ * o) * c := by group
      _ = c * j * c⁻¹ * c := by rw [← e]
      _ = c * j := by group
  have L2 : ∀ j ∈ J, ∀ c ∈ (M ⊓ Cx : Subgroup G),
      j * c ∈ ((M ⊓ Cx : Subgroup G) : Set G) * (J : Set G) := by
    intro j hj c hc
    obtain ⟨j₂, hj₂, c₂, hc₂, e⟩ :=
      Set.mem_mul.1 (L1 c⁻¹ (Subgroup.inv_mem _ hc) j⁻¹ (Subgroup.inv_mem _ hj))
    refine Set.mem_mul.2 ⟨c₂⁻¹, Subgroup.inv_mem _ hc₂, j₂⁻¹, Subgroup.inv_mem _ hj₂, ?_⟩
    calc c₂⁻¹ * j₂⁻¹ = (j₂ * c₂)⁻¹ := by group
      _ = (c⁻¹ * j⁻¹)⁻¹ := by rw [e]
      _ = j * c := by group
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨j, hj, c, hc, rfl⟩ := Set.mem_mul.1 hg
    exact L2 j hj c hc
  · intro g hg
    obtain ⟨c, hc, j, hj, rfl⟩ := Set.mem_mul.1 hg
    exact L1 c hc j hj

end Cover


section Prop121Steps

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_mono {p : ℕ} {H K : Subgroup G} (hHK : H ≤ K) (hK : IsElemAbelian p K) :
    IsElemAbelian p H := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => hK.2 x (hHK hx)⟩
  have h2 := congrArg Subtype.val (hK.1.is_comm.comm (⟨a.1, hHK a.2⟩ : K) ⟨b.1, hHK b.2⟩)
  exact Subtype.ext h2

theorem exists_ne_one_of_index {F A : Subgroup G} (hA : A ≤ F) (hidx : (A.subgroupOf F).index = 3)
    {E : Subgroup G} (hEF : E ≤ F) (hE9 : Nat.card E = 9) : ∃ x ∈ A, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hA0 : A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Subgroup.mem_bot).2 (hcon x hx)
  have hsub : A.subgroupOf F = ⊥ := by
    rw [hA0]
    ext y
    simp
  have h1 : (A.subgroupOf F).index = Nat.card F := by
    rw [hsub, Subgroup.index_bot]
  have h2 : Nat.card E ≤ Nat.card F := Subgroup.card_le_of_le hEF
  omega

theorem le_iSup_centralizer_hyperplane {F S : Subgroup G} (hF : IsElemAbelian 3 F)
    (hFne : F ≠ ⊥) (hS : IsPGroup 2 S) (hFS : F ≤ Subgroup.normalizer (S : Set G)) :
    S ≤ ⨆ (A : Subgroup G) (_ : A ≤ F ∧ (A.subgroupOf F).index = 3),
      S ⊓ Subgroup.centralizer (A : Set G) :=
  GL83.le_iSup_hyperplane (p := 3) (by norm_num) (by norm_num) hFne hF hS hFS

theorem exists_card_nine {F : Subgroup G} (hF : CFSG.Open.pRank 3 F = 2) :
    ∃ E : Subgroup G, E ≤ F ∧ Nat.card E = 9 := by
  have hbot : IsElemAbelian 3 (⊥ : Subgroup G) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : a = 1 := Subtype.ext (Subgroup.mem_bot.1 a.2)
      have hb : b = 1 := Subtype.ext (Subgroup.mem_bot.1 b.2)
      rw [ha, hb]
    · rw [Subgroup.mem_bot.1 hx, one_pow]
  have hne : ({k : ℕ | ∃ E : Subgroup G, E ≤ F ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}).Nonempty :=
    ⟨0, ⊥, bot_le, hbot, by simp⟩
  have hbdd : BddAbove ({k : ℕ | ∃ E : Subgroup G, E ≤ F ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}) := by
    refine ⟨Nat.card F, ?_⟩
    rintro k ⟨E, hEF, -, hE⟩
    have h1 : Nat.card E ≤ Nat.card F := Subgroup.card_le_of_le hEF
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  have hmem := Nat.sSup_mem hne hbdd
  unfold CFSG.Open.pRank at hF
  rw [hF] at hmem
  obtain ⟨E, hEF, -, hE⟩ := hmem
  exact ⟨E, hEF, by rw [hE]; norm_num⟩

theorem pCore_le_join {M F : Subgroup G} (hFM : F ≤ M) (hF : IsElemAbelian 3 F)
    (hF2 : CFSG.Open.pRank 3 F = 2) :
    pCoreOf 2 M ≤ ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1), M ⊓ Cg x := by
  obtain ⟨E, hEF, hE9⟩ := exists_card_nine hF2
  have hFne : F ≠ ⊥ := by
    intro hF0
    have h1 : Nat.card E ≤ Nat.card F := Subgroup.card_le_of_le hEF
    rw [hF0, Subgroup.card_bot] at h1
    omega
  have hT : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hFN : F ≤ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    hFM.trans (le_normalizer_pCoreOf 2 M)
  refine (le_iSup_centralizer_hyperplane hF hFne hT hFN).trans (iSup₂_le fun A hA => ?_)
  obtain ⟨x, hxA, hx1⟩ := exists_ne_one_of_index hA.1 hA.2 hEF hE9
  have hxF : x ∈ F := hA.1 hxA
  intro g hg
  have hgM : g ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hg.1
  have hgC : g ∈ Cg x := cent_le_cent_of_mem hxA hg.2
  have hmemW : M ⊓ Cg x ≤ ⨆ (x' : G) (_ : x' ∈ F) (_ : x' ≠ 1), M ⊓ Cg x' :=
    le_iSup_of_le x (le_iSup_of_le hxF (le_iSup_of_le hx1 le_rfl))
  exact hmemW ⟨hgM, hgC⟩



theorem ne_bot_of_card_nine {F E : Subgroup G} (hEF : E ≤ F) (hE9 : Nat.card E = 9) : F ≠ ⊥ := by
  intro hF0
  have h1 : Nat.card E ≤ Nat.card F := Subgroup.card_le_of_le hEF
  rw [hF0, Subgroup.card_bot] at h1
  omega

end Prop121Steps

section Prop121Conditional

variable {G : Type} [Group G] [Finite G]

theorem core_le_W_of_inputs (h123 : Lemma123Statement) (h124 : Lemma124Statement)
    {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K) (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) :
    pCoreOf 2 M ≤ ⨆ (x : G) (_ : x ∈ centBar 3 A K) (_ : x ≠ 1), M ⊓ Cg x := by
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  obtain ⟨⟨-, -, -, -, -, hF2, -⟩, -, -, -⟩ := h124 h hK hK3 hKM hu₀ hA0
  have hF2' : CFSG.Open.pRank 3 (centBar 3 A K) = 2 := hF2
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hFA : centBar 3 A K ≤ A := by
    unfold centBar
    exact inf_le_right
  exact pCore_le_join (hFA.trans (h.pair.1.2.1.1.1.1)) (isElemAbelian_mono hFA hAel) hF2'

theorem noncommute_of_inputs (h123 : Lemma123Statement) (h124 : Lemma124Statement)
    {m p : ℕ} {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K) (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) :
    ∃ x ∈ centBar 3 A K, x ≠ 1 ∧
      ∃ b ∈ A ⊓ GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G)),
        ∃ s ∈ pCoreOf 2 M ⊓ Cg x, b * s ≠ s * b := by
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  have hS : GLStanding G m 3 := h.standing
  obtain ⟨⟨-, -, -, -, hcard, hF2, -⟩, -, -, -⟩ := h124 h hK hK3 hKM hu₀ hA0
  have hcard' : Nat.card ↥(A ⊓ GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G))) = 9 :=
    hcard
  have hF2' : CFSG.Open.pRank 3 (centBar 3 A K) = 2 := hF2
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hFA : centBar 3 A K ≤ A := by
    unfold centBar
    exact inf_le_right
  have hFel : IsElemAbelian 3 (centBar 3 A K) := isElemAbelian_mono hFA hAel
  have hFM : centBar 3 A K ≤ M := hFA.trans hAM
  obtain ⟨E9, hE9F, hE9⟩ := exists_card_nine hF2'
  have hFne : centBar 3 A K ≠ ⊥ := ne_bot_of_card_nine hE9F hE9
  have hTwoLocal : IsTwoLocal M := h.pre.1.1
  have hS2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hFN : centBar 3 A K ≤ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    hFM.trans (le_normalizer_pCoreOf 2 M)
  by_contra hcon
  push Not at hcon
  have hBS : A ⊓ GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G)) ≤ pCoreOf 2 M := by
    intro b hb
    have hbA : b ∈ A := hb.1
    have hbM : b ∈ M := hAM hbA
    have hT' : pCoreOf 2 M ≤ Subgroup.centralizer ({b} : Set G) := by
      refine (le_iSup_centralizer_hyperplane hFel hFne hS2 hFN).trans (iSup₂_le fun A' hA' => ?_)
      obtain ⟨x, hxA', hx1⟩ := exists_ne_one_of_index hA'.1 hA'.2 hE9F hE9
      have hxF : x ∈ centBar 3 A K := hA'.1 hxA'
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hcon x hxF hx1 y hb g ⟨hg.1, cent_le_cent_of_mem hxA' hg.2⟩
    have hbC : b ∈ Subgroup.centralizer ((pCoreOf 2 M : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact ((Subgroup.mem_centralizer_iff.1 (hT' hg)) b (Set.mem_singleton b)).symm
    exact hS.charTwo M hTwoLocal ⟨hbM, hbC⟩
  have hB2 : IsPGroup 2 ↥(A ⊓ GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G))) :=
    hS2.to_le hBS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hB2
  rw [hcard'] at hn
  have hn4 : n < 4 := by
    by_contra hc
    push Not at hc
    have h16 : (2 : ℕ) ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hc
    norm_num at h16
    omega
  interval_cases n <;> norm_num at hn

end Prop121Conditional

end Sec12b

open Sec12b in
theorem lemma125_i_of_inputs (h123 : Lemma123Statement) (h124 : Lemma124Statement)
    (h111 : Prop111Statement) {G : Type} [Group G] [Finite G] {m p : ℕ}
    {B M E A : Subgroup G} {a : G} (h : Cex121 G m p B M E A a) {K : Subgroup G}
    (hK : GLAPComponent 3 (Cg a) K) (hK3 : IsLThreeFour (barOf 3 K ⧸ Subgroup.center (barOf 3 K)))
    (hKM : ¬ Covers 3 (Cg a) (M ⊓ Cg a) K)
    (hu₀ : ∃ u ∈ Tof p M a ⊓ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G),
      ∃ hu : u ∈ Subgroup.normalizer (K : Set G), IsUnitaryAut (barAut 3 K ⟨u, hu⟩))
    (hA0 : Nat.card (E ⊓ A : Subgroup G) = 9 ∧ InducesFaithfulInner 3 (E ⊓ A) K) :
    let F := centBar 3 A K
    let J := GLAPLayer 3 (K ⊓ Subgroup.centralizer (F : Set G))
    let W := ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1), M ⊓ Cg x
    J ⊔ W ≠ ⊤ := by
  intro F J W
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  have hS : GLStanding G m 3 := h.standing
  haveI : IsSimpleGroup G := hS.simple
  obtain ⟨⟨-, -, -, -, -, hF2, -⟩, hII, -, -⟩ := h124 h hK hK3 hKM hu₀ hA0
  have hF2' : CFSG.Open.pRank 3 F = 2 := hF2
  have hII' : ∀ x ∈ F, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (Kx 3 J x : Set G) ∧ barX 3 (Kx 3 J x) J = ⊤ := hII
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hFA : F ≤ A := by
    show centBar 3 A K ≤ A
    unfold centBar
    exact inf_le_right
  have hFM : F ≤ M := hFA.trans hAM
  have hJle : J ≤ K ⊓ Subgroup.centralizer (F : Set G) := layer_le 3 _
  have hJC : J ≤ Subgroup.centralizer (F : Set G) := hJle.trans inf_le_right
  have hJCa : J ≤ Subgroup.centralizer ({a} : Set G) :=
    hJle.trans (inf_le_left.trans (comp_le hK))
  have hF0 : F ≠ ⊥ := by
    intro hF
    have h0 : CFSG.Open.pRank 3 F = 0 := by
      rw [hF]
      exact pRank_bot (by norm_num)
    omega
  have hJtop : J ≠ ⊤ := fun hJ =>
    cent_ne_top hS h.ha.2 (top_le_iff.1 (by rw [← hJ]; exact hJCa))
  have hJN : J ≤ Subgroup.normalizer (F : Set G) :=
    fun j hj => Subgroup.centralizer_le_normalizer _ (hJC hj)
  have hWM : W ≤ M := iSup_le fun x => iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hMtop : M ≠ ⊤ := isTwoLocal_ne_top hS h.pre.1.1
  have hWtop : W ≠ ⊤ := fun hW => hMtop (top_le_iff.1 (by rw [← hW]; exact hWM))
  have hFW : F ≤ W := by
    intro f hf
    by_cases hf1 : f = 1
    · rw [hf1]
      exact Subgroup.one_mem _
    · have hmem : f ∈ (⨆ (_ : f ∈ F) (_ : f ≠ 1), M ⊓ Cg f : Subgroup G) := by
        rw [iSup_pos hf, iSup_pos hf1]
        refine ⟨hFM hf, Subgroup.mem_centralizer_iff.2 ?_⟩
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        rfl
      exact le_iSup (fun i => ⨆ (_ : i ∈ F) (_ : i ≠ 1), M ⊓ Cg i) f hmem
  have hperm : ∀ x ∈ F, x ≠ 1 → (J : Set G) * ((M ⊓ Cg x : Subgroup G) : Set G) =
      ((M ⊓ Cg x : Subgroup G) : Set G) * (J : Set G) := by
    intro x hxF hx1
    obtain ⟨hN, hcov⟩ := hII' x hxF hx1
    have hO : GLAPPrimeCoreOf 3 (Cg x) ≤ M := h111 h.toSec11 (hFA hxF) hx1
    have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := hJC.trans (cent_le_cent_of_mem hxF)
    exact mul_eq_mul_of_cover (p := 3) (by norm_num) (le_kx x J) (kx_le_cent hJx) hN hcov hO
  have hK : ∀ i, ∀ g ∈ J, ∀ k ∈ (⨆ (_ : i ∈ F) (_ : i ≠ 1), M ⊓ Cg i : Subgroup G),
      ∃ k' ∈ (⨆ (_ : i ∈ F) (_ : i ≠ 1), M ⊓ Cg i : Subgroup G), ∃ g' ∈ J, g * k = k' * g' := by
    intro i g hg k hk
    by_cases hi : i ∈ F ∧ i ≠ 1
    · rw [iSup_pos hi.1, iSup_pos hi.2] at hk ⊢
      have hmem : g * k ∈ (J : Set G) * ((M ⊓ Cg i : Subgroup G) : Set G) :=
        Set.mul_mem_mul hg hk
      rw [hperm i hi.1 hi.2] at hmem
      obtain ⟨c, hc, j, hj, e⟩ := Set.mem_mul.1 hmem
      exact ⟨c, hc, j, hj, e.symm⟩
    · have hbot : (⨆ (_ : i ∈ F) (_ : i ≠ 1), M ⊓ Cg i : Subgroup G) = ⊥ := by
        by_cases h1 : i ∈ F
        · have h2 : ¬ i ≠ 1 := fun h2 => hi ⟨h1, h2⟩
          rw [iSup_pos h1, iSup_neg h2]
        · rw [iSup_neg h1]
      rw [hbot] at hk ⊢
      rw [Subgroup.mem_bot.1 hk]
      exact ⟨1, Subgroup.one_mem _, g, hg, by simp⟩
  have hPW : ∀ g ∈ J, ∀ v ∈ W, ∃ v' ∈ W, ∃ g' ∈ J, g * v = v' * g' :=
    fun g hg v hv => mul_mem_iSup_of_perm J (fun i => ⨆ (_ : i ∈ F) (_ : i ≠ 1), M ⊓ Cg i) hK hv
      g hg
  let Q : Subgroup G :=
    { carrier := (W : Set G) * (J : Set G)
      mul_mem' := by
        intro a b ha hb
        obtain ⟨w₁, hw₁, j₁, hj₁, rfl⟩ := Set.mem_mul.1 ha
        obtain ⟨w₂, hw₂, j₂, hj₂, rfl⟩ := Set.mem_mul.1 hb
        obtain ⟨v', hv', g', hg', e⟩ := hPW j₁ hj₁ w₂ hw₂
        refine Set.mem_mul.2 ⟨w₁ * v', Subgroup.mul_mem _ hw₁ hv', g' * j₂,
          Subgroup.mul_mem _ hg' hj₂, ?_⟩
        calc w₁ * v' * (g' * j₂) = w₁ * (v' * g') * j₂ := by group
          _ = w₁ * (j₁ * w₂) * j₂ := by rw [← e]
          _ = w₁ * j₁ * (w₂ * j₂) := by group
      one_mem' := Set.mem_mul.2 ⟨1, Subgroup.one_mem _, 1, Subgroup.one_mem _, mul_one 1⟩
      inv_mem' := by
        intro a ha
        obtain ⟨w, hw, j, hj, rfl⟩ := Set.mem_mul.1 ha
        obtain ⟨v', hv', g', hg', e⟩ :=
          hPW j⁻¹ (Subgroup.inv_mem _ hj) w⁻¹ (Subgroup.inv_mem _ hw)
        refine Set.mem_mul.2 ⟨v', hv', g', hg', ?_⟩
        calc v' * g' = j⁻¹ * w⁻¹ := e.symm
          _ = (w * j)⁻¹ := by group }
  have hle : J ⊔ W ≤ Q := by
    refine sup_le (fun j hj => Set.mem_mul.2 ⟨1, Subgroup.one_mem _, j, hj, one_mul j⟩)
      (fun w hw => Set.mem_mul.2 ⟨w, hw, 1, Subgroup.one_mem _, mul_one w⟩)
  intro hTop
  have huniv : (W : Set G) * (J : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    have hg : g ∈ J ⊔ W := by
      rw [hTop]
      exact Subgroup.mem_top g
    exact hle hg
  exact (GL83.I_32_8_proved G W J F hWtop hJtop hF0 hFW hJN) huniv

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

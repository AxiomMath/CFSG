module

public import CFSG.LocalAnalysis.RankThreeUC.GN15Steps
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN CFSG.Quasithin
  CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

section Bookkeeping

variable {G : Type*} [Group G]

private theorem exists_mul_of_mem_sup_of_le_centralizer' {A K : Subgroup G}
    (hAK : A ≤ Subgroup.centralizer (K : Set G)) {x : G} (hx : x ∈ A ⊔ K) :
    ∃ a ∈ A, ∃ k ∈ K, x = a * k := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right A K
    (hAK.trans (Subgroup.centralizer_le_normalizer _))
  have hx' : x ∈ ((A ⊔ K : Subgroup G) : Set G) := hx
  rw [h] at hx'
  obtain ⟨a, ha, k, hk, rfl⟩ := hx'
  exact ⟨a, ha, k, hk, rfl⟩

private theorem le_centralizer_centralizer_self' (B : Subgroup G) :
    B ≤ Subgroup.centralizer (Subgroup.centralizer (B : Set G) : Set G) :=
  Subgroup.le_centralizer_iff.mpr le_rfl

theorem mem_sup_centralizer_biSup (F : Finset (Subgroup G))
    (hcomm : ∀ B ∈ F, ∀ B' ∈ F, B ≠ B' → B ≤ Subgroup.centralizer (B' : Set G)) {g : G}
    (hg : ∀ B ∈ F, g ∈ B ⊔ Subgroup.centralizer (B : Set G)) :
    g ∈ (⨆ B ∈ F, B) ⊔ Subgroup.centralizer ((⨆ B ∈ F, B : Subgroup G) : Set G) := by
  classical
  induction F using Finset.induction_on generalizing g with
  | empty => simp [Subgroup.mem_centralizer_iff]
  | insert B₀ F hB₀ ih =>
    have hB₀F : ∀ B ∈ F, B ≠ B₀ := fun B hB h => hB₀ (h ▸ hB)
    obtain ⟨d₀, hd₀, c₀, hc₀, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer'
      (le_centralizer_centralizer_self' B₀) (hg B₀ (Finset.mem_insert_self _ _))
    have hc₀F : ∀ B ∈ F, c₀ ∈ B ⊔ Subgroup.centralizer (B : Set G) := by
      intro B hB
      have h1 : d₀⁻¹ ∈ Subgroup.centralizer (B : Set G) :=
        inv_mem (hcomm B₀ (Finset.mem_insert_self _ _) B (Finset.mem_insert_of_mem hB)
          (hB₀F B hB).symm hd₀)
      have h2 : d₀⁻¹ * (d₀ * c₀) ∈ B ⊔ Subgroup.centralizer (B : Set G) :=
        mul_mem (Subgroup.mem_sup_right h1) (hg B (Finset.mem_insert_of_mem hB))
      simpa using h2
    have hih := ih (fun B hB B' hB' hne => hcomm B (Finset.mem_insert_of_mem hB) B'
      (Finset.mem_insert_of_mem hB') hne) hc₀F
    obtain ⟨d₁, hd₁, c₁, hc₁, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer'
      (le_centralizer_centralizer_self' (⨆ B ∈ F, B)) hih
    have hDF : (⨆ B ∈ F, B : Subgroup G) ≤ Subgroup.centralizer (B₀ : Set G) :=
      iSup₂_le fun B hB => hcomm B (Finset.mem_insert_of_mem hB) B₀
        (Finset.mem_insert_self _ _) (hB₀F B hB)
    have hc₁B₀ : c₁ ∈ Subgroup.centralizer (B₀ : Set G) := by
      have : d₁⁻¹ * (d₁ * c₁) ∈ Subgroup.centralizer (B₀ : Set G) :=
        mul_mem (inv_mem (hDF hd₁)) hc₀
      simpa using this
    have hc₁' : c₁ ∈ Subgroup.centralizer ((B₀ ⊔ ⨆ B ∈ F, B : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hsub : B₀ ⊔ (⨆ B ∈ F, B) ≤ Subgroup.centralizer ({c₁} : Set G) := by
        refine sup_le ?_ ?_
        · intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hc₁B₀ y hy
        · intro y hy
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hc₁ y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hx)
    rw [Finset.iSup_insert, ← mul_assoc]
    exact Subgroup.mul_mem_sup (mul_mem (Subgroup.mem_sup_left hd₀) (Subgroup.mem_sup_right hd₁)) hc₁'

end Bookkeeping

section OuterCommutative

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {G : Type*} [Group G]

theorem commutator_mem_sup_centralizer_of_isMulCommutative_outer {B : Subgroup G}
    (hB : IsMulCommutative (Outer ↥B)) {w j : G} (hw : w ∈ Subgroup.normalizer (B : Set G))
    (hj : j ∈ Subgroup.normalizer (B : Set G)) :
    ⁅w, j⁆ ∈ B ⊔ Subgroup.centralizer (B : Set G) := by
  let wn : Subgroup.normalizer (B : Set G) := ⟨w, hw⟩
  let jn : Subgroup.normalizer (B : Set G) := ⟨j, hj⟩
  have hmk : ⁅(QuotientGroup.mk (B.normalizerMonoidHom wn) : Outer ↥B),
      (QuotientGroup.mk (B.normalizerMonoidHom jn) : Outer ↥B)⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.2
      ((isMulCommutative_iff.1 hB) _ _)
  have hin : ⁅B.normalizerMonoidHom wn, B.normalizerMonoidHom jn⁆ ∈ inner ↥B := by
    apply (QuotientGroup.eq_one_iff _).1
    exact (map_commutatorElement (QuotientGroup.mk' (inner ↥B)) _ _).trans hmk
  obtain ⟨c, hc⟩ := hin
  have hx : ∀ x : B, ((⁅w, j⁆ * x * ⁅w, j⁆⁻¹ : G)) = (c : G) * x * (c : G)⁻¹ := by
    intro x
    have h1 := congrArg (fun f : MulAut ↥B => ((f x : B) : G)) hc
    have h2 : ((⁅B.normalizerMonoidHom wn, B.normalizerMonoidHom jn⁆ x : B) : G) =
        ⁅w, j⁆ * x * ⁅w, j⁆⁻¹ := by
      rw [← map_commutatorElement B.normalizerMonoidHom wn jn]
      rfl
    rw [← h2]
    exact h1.symm
  have hcent : (c : G)⁻¹ * ⁅w, j⁆ ∈ Subgroup.centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxB
    have : ⁅w, j⁆ * x * ⁅w, j⁆⁻¹ = (c : G) * x * (c : G)⁻¹ := hx ⟨x, hxB⟩
    calc x * ((c : G)⁻¹ * ⁅w, j⁆) = (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * ⁅w, j⁆ := by group
      _ = (c : G)⁻¹ * (⁅w, j⁆ * x * ⁅w, j⁆⁻¹) * ⁅w, j⁆ := by rw [this]
      _ = ((c : G)⁻¹ * ⁅w, j⁆) * x := by group
  have : ⁅w, j⁆ = (c : G) * ((c : G)⁻¹ * ⁅w, j⁆) := by group
  rw [this]
  exact Subgroup.mul_mem_sup c.2 hcent

end OuterCommutative

section Components

variable {G : Type*} [Group G]

private theorem isComponentOf_conjSub' {L : Subgroup G} (hL : IsComponentOf L ⊤) (g : G) :
    IsComponentOf (B6.conjSub g L) ⊤ :=
  (CFSG.isComponent_iff_open _).1
    (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g)
      ((CFSG.isComponent_iff_open L).2 hL))

@[expose] def gnCompNormalizer (G : Type*) [Group G] : Subgroup G :=
  ⨅ L ∈ {L : Subgroup G | IsComponentOf L ⊤}, Subgroup.normalizer (L : Set G)

theorem mem_gnCompNormalizer {k : G} :
    k ∈ gnCompNormalizer G ↔
      ∀ L : Subgroup G, IsComponentOf L ⊤ → k ∈ Subgroup.normalizer (L : Set G) := by
  simp [gnCompNormalizer, Subgroup.mem_iInf]

theorem normal_gnCompNormalizer : (gnCompNormalizer G).Normal where
  conj_mem k hk g := by
    rw [mem_gnCompNormalizer] at hk ⊢
    intro L hL
    have h1 := hk _ (isComponentOf_conjSub' hL g⁻¹)
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro x
    have h2 := h1 (g⁻¹ * x * g)
    simp only [B6.mem_conjSub, inv_inv] at h2
    convert h2 using 2 <;> group

end Components

section Layer

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

@[expose] def gnWComp (T : Subgroup X) : Subgroup X :=
  (gnCompNormalizer (X ⧸ gnC T)).comap (toStar T)

omit [Finite X] in
theorem gnWComp_normal : (gnWComp T).Normal := by
  have := normal_gnCompNormalizer (G := X ⧸ gnC T)
  exact Subgroup.Normal.comap this _

omit [Finite X] in
theorem mem_gnWComp_iff {w : X} : w ∈ gnWComp T ↔
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ →
      toStar T w ∈ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := by
  rw [gnWComp, Subgroup.mem_comap, mem_gnCompNormalizer]

theorem thompsonJ_le_gnWComp (hX : GNSetting X T) : thompsonJ T ≤ gnWComp T := fun j hj =>
  mem_gnWComp_iff.2 fun _ hL => thompsonJ_le_normalizer_of_isComponentOf hX hL ⟨j, hj, rfl⟩

omit [Finite X] in
theorem gnC_le_gnQPre : gnC T ≤ gnQPre T := fun z hz => by
  show toStar T z ∈ Subgroup.centralizer (gnDStar T : Set (X ⧸ gnC T))
  have h1 : toStar T z = 1 := (QuotientGroup.eq_one_iff z).2 hz
  rw [h1]
  exact one_mem _

omit [Finite X] in
theorem mem_gnQPre_sup_gnDPre_of_mem_sup {x : X}
    (hx : toStar T x ∈ gnDStar T ⊔ Subgroup.centralizer (gnDStar T : Set (X ⧸ gnC T))) :
    x ∈ gnQPre T ⊔ gnDPre T := by
  obtain ⟨d, hd, c, hc, hxdc⟩ := exists_mul_of_mem_sup_of_le_centralizer'
    (le_centralizer_centralizer_self' (gnDStar T)) hx
  obtain ⟨xd, rfl⟩ := QuotientGroup.mk_surjective d
  obtain ⟨xc, rfl⟩ := QuotientGroup.mk_surjective c
  have hxdc' : ((xd * xc : X) : X ⧸ gnC T) = (x : X ⧸ gnC T) := by
    rw [QuotientGroup.mk_mul]
    exact hxdc.symm
  have hz : (xd * xc)⁻¹ * x ∈ gnC T := QuotientGroup.eq.mp hxdc'
  have hxd : xd ∈ gnDPre T := hd
  have hxc : xc ∈ gnQPre T := hc
  have hx' : x = xd * xc * ((xd * xc)⁻¹ * x) := by group
  rw [hx']
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hxd) (Subgroup.mem_sup_left hxc))
    (Subgroup.mem_sup_left (gnC_le_gnQPre hz))

end Layer

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

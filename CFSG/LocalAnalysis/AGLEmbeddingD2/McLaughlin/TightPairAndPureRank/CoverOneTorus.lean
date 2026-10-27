module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneShort
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverBig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneNodes

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding.BlockCyc CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Open CFSG.HallHigman
open scoped commutatorElement

section Pkg

variable {K : Type} [Group K] {D : UniversalRootDatum K} {H : Fin D.rank → Subgroup K}

@[expose] def HasTorusSL2 (D : UniversalRootDatum K) (H : Fin D.rank → Subgroup K)
    (i : Fin D.rank) (F : Type) [Field F] : Prop :=
  ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* K, Function.Injective φ ∧
    (∀ c, φ (sl2Upper c) ∈ D.rootGroup (Pi.single i 1)) ∧
    (∀ c, φ (sl2Lower c) ∈ D.rootGroup (-Pi.single i 1)) ∧
    rankOne D.rootGroup i ≤ φ.range ∧
    ∃ d b : Matrix.SpecialLinearGroup (Fin 2) F, d * b ≠ b * d ∧ φ d ∈ H i

variable {F : Type} [Field F]

theorem HasTorusSL2.hasSL2Node {i : Fin D.rank} (h : HasTorusSL2 D H i F) : HasSL2Node D i F := by
  obtain ⟨φ, hinj, hU, hL, -⟩ := h
  exact ⟨φ, hinj, hU, hL⟩

theorem HasTorusSL2.eq_one_of_central [Finite F] [CharP F 2] (h4 : 4 ≤ Nat.card F) {i : Fin D.rank}
    (h : HasTorusSL2 D H i F) {z : K} (hz : z ∈ rankOne D.rootGroup i)
    (hc : ∀ g ∈ rankOne D.rootGroup i, z * g = g * z) : z = 1 := by
  obtain ⟨φ, hinj, hU, hL, hrange, -⟩ := h
  obtain ⟨a, rfl⟩ := hrange hz
  have hS := sl2_isSimpleGroup (k := F) h4
  have hcl : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
      Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    rw [Subgroup.closure_le]
    have key : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, φ g ∈ rankOne D.rootGroup i →
        g ∈ Subgroup.centralizer ({a} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      apply hinj
      rw [map_mul, map_mul]
      exact hc _ hg
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact key _ (le_sup_left (a := D.rootGroup (Pi.single i 1)) (hU c))
    · exact key _ (le_sup_right (b := D.rootGroup (-Pi.single i 1)) (hL c))
  have hcen : ∀ g : Matrix.SpecialLinearGroup (Fin 2) F, g * a = a * g := fun g => by
    have := Subgroup.mem_centralizer_iff.1 (hcl (Sp.mem_closure_sl2 g)) a (Set.mem_singleton a)
    exact this.symm
  have hmem : a ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Subgroup.mem_center_iff.2 fun g => (hcen g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) with hb | ht
  · rw [hb, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
  · exfalso
    have hall : ∀ g g' : Matrix.SpecialLinearGroup (Fin 2) F, g * g' = g' * g := fun g g' => by
      have : g' ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [ht]; exact Subgroup.mem_top _
      exact (Subgroup.mem_center_iff.1 this g)
    exact sl2_upper_lower_not_commute (F := F) (by
      rw [hall (sl2Upper 1 * sl2Lower 1) (sl2Upper 1)])

end Pkg

section Main

variable {K Y : Type} [Group K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {F : Type} [Field F] [Finite F]
  [CharP F 2]

theorem false_short_orth {M : ℕ} (h : BorelQuotient D n H π M) (h4 : 4 ≤ Nat.card F) {s t : Fin D.rank}
    (hs : HasSL2Node D s F) (ht : HasOrderThree D t) (hts : t ≠ s) (hc : D.cartan t s = 0)
    {C : Subgroup Y} (hC : SolvFree C) (hsC : (rankOne D.rootGroup s).map π ≤ C)
    (htC : (rankOne D.rootGroup t).map π ≤ C) : False := by
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_of_nodes h hc hts ht hs.hasOrderThreeNC
  have hEC : E ≤ C := hE.trans (sup_le htC hsC)
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.not_isPSolvable_map_rankOne_of_sl2Node h h4 hs
    (hC E _ hEC hsC hel hcard)

theorem false_of_E9_short {M : ℕ} (h : BorelQuotient D n H π M) (h4 : 4 ≤ Nat.card F)
    {s : Fin D.rank} (hs : HasSL2Node D s F) {C : Subgroup Y} (hC : SolvFree C)
    (hsC : (rankOne D.rootGroup s).map π ≤ C) {E : Subgroup Y} (hEC : E ≤ C)
    (hel : IsElemAbelian 3 E) (hcard : Nat.card E = 9) : False :=
  CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.not_isPSolvable_map_rankOne_of_sl2Node h h4 hs
    (hC E _ hEC hsC hel hcard)

theorem false_short_long [Finite K] (h : BorelQuotient D n H π 3) (h4 : 4 ≤ Nat.card F) {s j : Fin D.rank}
    (hs : HasTorusSL2 D H s F) (hj : HasOrderThree D j)
    (h6 : Nat.card (rankOne D.rootGroup j) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a)
    {C : Subgroup Y} (hC : SolvFree C) (hsC : (rankOne D.rootGroup s).map π ≤ C)
    (hjC : (rankOne D.rootGroup j).map π ≤ C) : False := by
  have hnode := hs.hasSL2Node
  obtain ⟨φ, hinj, hU, hL, hrange, d, b, hdb, hd⟩ := hs
  have hh0L : φ d ∈ rankOne D.rootGroup s := h.ct.H_le s hd
  have hh03 : φ d ^ 3 = 1 := h.torus_pow s _ hd
  obtain ⟨c, hcL, hc1, hc3⟩ := exists_order_three_rankOne hj
  have hcomm : ∀ g ∈ rankOne D.rootGroup j, φ d * g = g * φ d :=
    torus_centralizes_rankOne_of_card_six h h6.1 hd
  obtain ⟨g, hg, hgc⟩ : ∃ g ∈ rankOne D.rootGroup j, g * c ≠ c * g := by
    by_contra hno
    push Not at hno
    exact hc1 (Lie.eq_one_of_central_of_card_six h6.1 h6.2 hcL fun x hx => (hno x hx).symm)
  have hb₁ : ¬ Commute (φ b) (φ d) := fun hcb => hdb (hinj (by
    rw [map_mul, map_mul]; exact (hcb.eq).symm))
  obtain ⟨E, hE, hel, hcard⟩ := exists_E9_le_of_commuting_orders π h.ker_central
    (a₁ := φ d) (a₂ := c) (b₁ := φ b) (b₂ := g) hh03 hc3 (hcomm c hcL)
    (hcomm g hg).symm hgc hb₁
  have hz₁ : Subgroup.zpowers (π (φ d)) ≤ C :=
    Subgroup.zpowers_le.2 (hsC ⟨φ d, hh0L, rfl⟩)
  have hz₂ : Subgroup.zpowers (π c) ≤ C := Subgroup.zpowers_le.2 (hjC ⟨c, hcL, rfl⟩)
  have hEC : E ≤ C := hE.trans (sup_le hz₁ hz₂)
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.not_isPSolvable_map_rankOne_of_sl2Node h h4 hnode
    (hC E _ hEC hsC hel hcard)

theorem noncomm_of_card_six_of_hasOrderThree {M : ℕ} (h : BorelQuotient D n H π M) {i : Fin D.rank}
    (h6 : Nat.card (rankOne D.rootGroup i) = 6) (h3 : HasOrderThree D i) :
    ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a := by
  obtain ⟨x, hx, y, hy, hxy3, c, hc⟩ := h3
  by_contra hno
  push Not at hno
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _ hα
  have hxL : x ∈ rankOne D.rootGroup i := Subgroup.mem_sup_left hx
  have hyL : y ∈ rankOne D.rootGroup i := Subgroup.mem_sup_right hy
  have hsq : ∀ z ∈ rankOne D.rootGroup i, (∃ m : ℕ, z ^ 2 ^ m = 1) → z ^ 2 = 1 := by
    rintro z hz ⟨m, hm⟩
    have h1 : orderOf z ∣ 6 := h6 ▸ Subgroup.orderOf_dvd_natCard _ hz
    have h2 : orderOf z ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h2
    rw [hj] at h1
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have := (pow_dvd_pow 2 (show 2 ≤ j by omega)).trans h1
      norm_num at this
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨m, hm⟩ := h.pGroup _ hα ⟨x, hx⟩
  obtain ⟨m', hm'⟩ := h.pGroup _ hα' ⟨y, hy⟩
  have hx2 : x ^ 2 = 1 := hsq x hxL ⟨m, congrArg Subtype.val hm⟩
  have hy2 : y ^ 2 = 1 := hsq y hyL ⟨m', congrArg Subtype.val hm'⟩
  have hcm : x * y = y * x := hno x hxL y hyL
  have : (x * y) ^ 3 = x * y := by
    rw [Commute.mul_pow (show Commute x y from hcm)]
    calc x ^ 3 * y ^ 3 = x ^ 2 * x * (y ^ 2 * y) := by group
      _ = x * y := by rw [hx2, hy2]; group
  have hxy : x * y = 1 := by rw [← this]; exact hxy3
  apply hc
  rw [hxy]
  group

end Main

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

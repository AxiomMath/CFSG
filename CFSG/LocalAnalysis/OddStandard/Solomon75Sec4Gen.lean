module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GenPerm
public import CFSG.LocalAnalysis.OddStandard.Solomon75AhatDataSylow
public import CFSG.SignalizerFunctorTheorem.Glauberman.Basic

public section

namespace CFSG.OddStandard.Solomon75.AhatData

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS

variable {n : ℕ} {K : Type} [Group K]

theorem exists_coverCtx_conj [NeZero n] [Finite K] (hn : 8 ≤ n) (hn' : n ≤ 11)
    (hK : IsDoubleCoverOfAlt K n) (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128)
    (hgood : SylowGood n (P0 n)) (S : Sylow 2 K) :
    ∃ (g : Perm (Fin n)) (X : CoverCtx n K (S : Subgroup K)), X.Q = conjSub g (P0 n) := by
  let C := CoverSetup.ofCover hK
  obtain ⟨g, hg⟩ := exists_conj_comap hn hn' hK C hP0 S
  obtain ⟨a, -, b, -, c, -, ha, hb, hc, h2, h3⟩ := hgood.eight
  refine ⟨g, ⟨C, conjSub g (P0 n), ?_, hg, hgood.conj g, hn', ?_, ?_, ?_⟩, rfl⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := exists_conj_mem.1 hx
    have hy' := P0_le_alternatingGroup hn hn' hy
    rw [Perm.mem_alternatingGroup] at hy' ⊢
    simp [Perm.sign_mul, hy']
  · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hP0]
  · exact fun x hx => C.isoI_sq_eq_one hn hn' ⟨a, b, c, ha, hb, hc, h2, h3⟩ hx
  · exact fun x hx => C.dblI_sq_ne_one hn hx

@[expose] def liftPair {S : Subgroup K} (X : CoverCtx n K S) (a : Perm (Fin n))
    (ha : a * a = 1) : Subgroup K :=
  (pairSub a ha).comap X.C.ρ

theorem mem_liftPair {S : Subgroup K} (X : CoverCtx n K S) {a : Perm (Fin n)} (ha : a * a = 1)
    {x : K} : x ∈ liftPair X a ha ↔ X.C.ρ x = 1 ∨ X.C.ρ x = a := Iff.rfl

theorem isElemAbelian_liftPair {S : Subgroup K} (X : CoverCtx n K S) {a : Perm (Fin n)}
    (ha : a * a = 1) (hia : IsoI a) : Open.IsElemAbelian 2 (liftPair X a ha) :=
  X.isElemAbelian_comap (E := pairSub a ha) (by
    rintro σ (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr hia)

theorem card_liftPair {S : Subgroup K} (X : CoverCtx n K S) {a : Perm (Fin n)}
    (ha : a * a = 1) (hia : IsoI a) (haQ : a ∈ X.Q) : Nat.card (liftPair X a ha) = 4 := by
  have hle : pairSub a ha ≤ alternatingGroup (Fin n) := by
    rintro σ (rfl | rfl)
    · exact one_mem _
    · exact X.hQA haQ
  have h1 := X.C.card_comap hle
  rw [card_pairSub ha hia.ne_one] at h1
  exact h1

theorem liftPair_le {S : Subgroup K} (X : CoverCtx n K S) {a : Perm (Fin n)}
    (ha : a * a = 1) (haQ : a ∈ X.Q) : liftPair X a ha ≤ S := by
  intro x hx
  apply X.mem_of_ρ_mem
  rcases (mem_liftPair X ha).1 hx with h | h
  · rw [h]
    exact X.Q.one_mem
  · rw [h]
    exact haQ

theorem mem_normalizer_liftPair {S : Subgroup K} (X : CoverCtx n K S) {a : Perm (Fin n)}
    (ha : a * a = 1) {x : K} (hx : X.C.ρ x * a = a * X.C.ρ x) :
    x ∈ normalizer (liftPair X a ha : Set K) := by
  rw [mem_set_normalizer_iff]
  intro y
  have hconj : ∀ q : Perm (Fin n), (q = 1 ∨ q = a) ↔
      (X.C.ρ x * q * (X.C.ρ x)⁻¹ = 1 ∨ X.C.ρ x * q * (X.C.ρ x)⁻¹ = a) := by
    intro q
    constructor
    · rintro (rfl | rfl)
      · left; group
      · right
        calc X.C.ρ x * q * (X.C.ρ x)⁻¹ = (X.C.ρ x * q) * (X.C.ρ x)⁻¹ := rfl
          _ = (q * X.C.ρ x) * (X.C.ρ x)⁻¹ := by rw [hx]
          _ = q := by group
    · rintro (h | h)
      · left
        have : q = (X.C.ρ x)⁻¹ * (X.C.ρ x * q * (X.C.ρ x)⁻¹) * X.C.ρ x := by group
        rw [this, h]
        group
      · right
        have : q = (X.C.ρ x)⁻¹ * (X.C.ρ x * q * (X.C.ρ x)⁻¹) * X.C.ρ x := by group
        rw [this, h]
        calc (X.C.ρ x)⁻¹ * a * X.C.ρ x = (X.C.ρ x)⁻¹ * (a * X.C.ρ x) := by group
          _ = (X.C.ρ x)⁻¹ * (X.C.ρ x * a) := by rw [hx]
          _ = a := by group
  show (X.C.ρ y = 1 ∨ X.C.ρ y = a) ↔ (X.C.ρ (x * y * x⁻¹) = 1 ∨ X.C.ρ (x * y * x⁻¹) = a)
  rw [map_mul, map_mul, map_inv]
  exact hconj _

theorem le_pRank_of_elem [Finite K] {H E : Subgroup K} (hEH : E ≤ H)
    (hE : Open.IsElemAbelian 2 E) {k : ℕ} (hk : Nat.card E = 2 ^ k) : k ≤ Open.pRank 2 H :=
  CFSG.SectionRank.le_pRank (by norm_num) hEH hE hk

theorem CoverCtx.card_le_sixteen [Finite K] {S : Subgroup K} (X : CoverCtx n K S)
    {E : Subgroup K} (hES : E ≤ S) (hE : Open.IsElemAbelian 2 E) : Nat.card E ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hk4 : k ≤ 4 := (le_pRank_of_elem hES hE hk).trans (X.rank).le
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    _ = 16 := by norm_num

theorem comap_le_thompsonJ [Finite K] {S : Subgroup K} (X : CoverCtx n K S)
    {E8 : Subgroup (Perm (Fin n))} (hEQ : E8 ≤ X.Q) (hE8 : Nat.card E8 = 8)
    (hiso : ∀ e ∈ E8, e = 1 ∨ IsoI e) :
    E8.comap X.C.ρ ≤ SignalizerFunctorTheorem.Glauberman.thompsonJ 2 S := by
  have hA : E8 ≤ alternatingGroup (Fin n) := fun e he => by
    rcases hiso e he with rfl | h
    · exact one_mem _
    · exact Perm.mem_alternatingGroup.2 h.sign_eq_one
  have hel := X.isElemAbelian_comap hiso
  have hcard : Nat.card (E8.comap X.C.ρ) = 16 := by
    rw [X.card_comap hA, hE8]
  have hle : E8.comap X.C.ρ ≤ S := (Subgroup.comap_mono hEQ).trans X.hS.symm.le
  refine le_sSup ⟨hle, hel, fun E' hE'S hE' => ?_⟩
  rw [hcard]
  exact X.card_le_sixteen hE'S hE'

theorem top_of_normalizer_family [Finite K] (C : CoverSetup n K) {T : Subgroup K}
    (l : List (Perm (Fin n) × Perm (Fin n)))
    (hgen : alternatingGroup (Fin n) ≤ Subgroup.closure {g | ∃ p ∈ l, p.2 = g})
    (hl : ∀ p ∈ l, p.2 ∈ alternatingGroup (Fin n) ∧ ∃ E : Subgroup K, E ≤ T ∧
      IsMulCommutative E ∧ 2 ≤ Open.pRank 2 E ∧ ∀ x, C.ρ x = p.2 → x ∈ normalizer (E : Set K))
    (hne : l ≠ []) :
    (⨆ (E : Subgroup K) (_ : E ≤ T) (_ : IsMulCommutative E) (_ : 2 ≤ Open.pRank 2 E),
      normalizer (E : Set K)) = ⊤ := by
  set H := ⨆ (E : Subgroup K) (_ : E ≤ T) (_ : IsMulCommutative E) (_ : 2 ≤ Open.pRank 2 E),
      normalizer (E : Set K) with hH
  have hmem : ∀ E : Subgroup K, E ≤ T → IsMulCommutative E → 2 ≤ Open.pRank 2 E →
      normalizer (E : Set K) ≤ H := fun E h1 h2 h3 =>
    le_iSup₂_of_le E h1 (le_iSup₂_of_le h2 h3 le_rfl)
  have hZ : center K ≤ H := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil l hne
    obtain ⟨-, E, hET, hEc, hEr, -⟩ := hl p hp
    exact (Subgroup.center_le_normalizer _).trans (hmem E hET hEc hEr)
  have hgenH : ∀ p ∈ l, p.2 ∈ H.map C.ρ := by
    intro p hp
    obtain ⟨hpA, E, hET, hEc, hEr, hEn⟩ := hl p hp
    obtain ⟨x, hx⟩ := C.exists_ρ_eq (Perm.mem_alternatingGroup.1 hpA)
    exact ⟨x, hmem E hET hEc hEr (hEn x hx), hx⟩
  have hclos : Subgroup.closure {g | ∃ p ∈ l, p.2 = g} ≤ H.map C.ρ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    exact hgenH p hp
  rw [eq_top_iff]
  intro x _
  obtain ⟨h, hh, hρ⟩ := hclos (hgen (Perm.mem_alternatingGroup.2 (C.sign_ρ x)))
  have hker : x * h⁻¹ ∈ center K := by
    rw [← C.ρ_eq_one_iff, map_mul, map_inv, ← hρ, mul_inv_cancel]
  have : x = (x * h⁻¹) * h := by group
  rw [this]
  exact H.mul_mem (hZ hker) hh

theorem GenGood.ne_nil (hn : 3 ≤ n) {l : List (Perm (Fin n) × Perm (Fin n))}
    (hgen : alternatingGroup (Fin n) ≤ Subgroup.closure {g | ∃ p ∈ l, p.2 = g}) : l ≠ [] := by
  rintro rfl
  have hS : {g : Perm (Fin n) | ∃ p ∈ ([] : List (Perm (Fin n) × Perm (Fin n))), p.2 = g} = ∅ := by
    ext g
    simp
  rw [hS, Subgroup.closure_empty] at hgen
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := fun h => by simpa [a, b] using congrArg Fin.val h
  have hac : a ≠ c := fun h => by simpa [a, c] using congrArg Fin.val h
  have hc3 : (swap a b * swap a c).IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac
    (fun h => by simpa [b, c] using congrArg Fin.val h)
  have h1 := hgen hc3.mem_alternatingGroup
  have h2 : swap a b * swap a c = 1 := (Subgroup.mem_bot).1 h1
  have := hc3.card_support
  rw [h2] at this
  simp at this

theorem normalizers_generate_of_genGood_S [NeZero n] [Finite K] (hn : 8 ≤ n) (hn' : n ≤ 11)
    (hK : IsDoubleCoverOfAlt K n) (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128)
    (hgood : SylowGood n (P0 n)) (hgen : GenGood n (P0 n) false) (S : Sylow 2 K) :
    (⨆ (E : Subgroup K) (_ : E ≤ (S : Subgroup K)) (_ : IsMulCommutative E)
      (_ : 2 ≤ Open.pRank 2 E), normalizer (E : Set K)) = ⊤ := by
  obtain ⟨g, X, hXQ⟩ := exists_coverCtx_conj hn hn' hK hP0 hgood S
  have hGG : GenGood n X.Q false := hXQ ▸ hgen.conj g
  obtain ⟨l, hl, hgenl⟩ := hGG.ex
  refine top_of_normalizer_family X.C l hgenl (fun p hp => ?_) (GenGood.ne_nil (by omega) hgenl)
  obtain ⟨h1, h2, h3, h4, -⟩ := hl p hp
  have hel := isElemAbelian_liftPair X h2.1 h2
  refine ⟨h3, liftPair X p.1 h2.1, liftPair_le X h2.1 h1, hel.1, ?_, fun x hx =>
    mem_normalizer_liftPair X h2.1 (by rw [hx]; exact h4)⟩
  exact le_pRank_of_elem le_rfl hel (k := 2) (by rw [card_liftPair X h2.1 h2 h1]; norm_num)

theorem normalizers_generate_of_genGood_J [NeZero n] [Finite K] (hn : 8 ≤ n) (hn' : n ≤ 11)
    (hK : IsDoubleCoverOfAlt K n) (hP0 : Nat.card (P0 n) = if n ≤ 9 then 64 else 128)
    (hgood : SylowGood n (P0 n)) (hgen : GenGood n (P0 n) true) (S : Sylow 2 K) :
    (⨆ (E : Subgroup K) (_ : E ≤ SignalizerFunctorTheorem.Glauberman.thompsonJ 2 (S : Subgroup K))
      (_ : IsMulCommutative E) (_ : 2 ≤ Open.pRank 2 E), normalizer (E : Set K)) = ⊤ := by
  obtain ⟨g, X, hXQ⟩ := exists_coverCtx_conj hn hn' hK hP0 hgood S
  have hGG : GenGood n X.Q true := hXQ ▸ hgen.conj g
  obtain ⟨l, hl, hgenl⟩ := hGG.ex
  refine top_of_normalizer_family X.C l hgenl (fun p hp => ?_) (GenGood.ne_nil (by omega) hgenl)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hl p hp
  obtain ⟨E8, hE8Q, hE8c, hE8i, haE⟩ := h5 rfl
  have hel := isElemAbelian_liftPair X h2.1 h2
  refine ⟨h3, liftPair X p.1 h2.1, ?_, hel.1, ?_, fun x hx =>
    mem_normalizer_liftPair X h2.1 (by rw [hx]; exact h4)⟩
  · exact (Subgroup.comap_mono (pairSub_le_of_mem h2.1 haE)).trans
      (comap_le_thompsonJ X hE8Q hE8c hE8i)
  · exact le_pRank_of_elem le_rfl hel (k := 2) (by rw [card_liftPair X h2.1 h2 h1]; norm_num)

end CFSG.OddStandard.Solomon75.AhatData

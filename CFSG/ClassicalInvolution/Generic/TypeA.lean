module

public import CFSG.ClassicalInvolution.Generic.Sign
public import CFSG.ClassicalInvolution.Generic.Base
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.Standard
public import CFSG.ClassicalInvolution.Phan.Main

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups

section Restrict

variable {X : Type} [Group X] {H : Type} [Group H]

theorem map_codRestrict_eq (θ : H →* X) (J : Subgroup X) (hθ : ∀ x, θ x ∈ J) (B : Subgroup H) :
    B.map (θ.codRestrict J hθ) = (B.map θ).subgroupOf J := by
  ext y
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
  · intro hy
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_subgroupOf.mp hy
    exact ⟨b, hb, Subtype.ext hby⟩

theorem linearBlockStandardPair_subgroupOf {K : Type} [Field K] {J W U V : Subgroup X}
    (hW : W ≤ J) (h : WeakCT.LinearBlockStandardPair K W U V) :
    WeakCT.LinearBlockStandardPair K (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := h
  have hθ : ∀ x, θ x ∈ J := fun x => hW (by rw [← hrange]; exact ⟨x, rfl⟩)
  refine ⟨θ.codRestrict J hθ, c, ?_, by rwa [MonoidHom.ker_codRestrict], ?_⟩
  · rw [MonoidHom.range_eq_map, map_codRestrict_eq, ← MonoidHom.range_eq_map, hrange]
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [map_codRestrict_eq, map_codRestrict_eq, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [map_codRestrict_eq, map_codRestrict_eq, h1, h2]
      exact ⟨rfl, rfl⟩

theorem unitaryBlockStandardPair_subgroupOf {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] {J W U V : Subgroup X} (hW : W ≤ J)
    (h : Phan.UnitaryBlockStandardPair K p f W U V) :
    Phan.UnitaryBlockStandardPair K p f (W.subgroupOf J) (U.subgroupOf J) (V.subgroupOf J) := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := h
  have hθ : ∀ x, θ x ∈ J := fun x => hW (by rw [← hrange]; exact ⟨x, rfl⟩)
  refine ⟨θ.codRestrict J hθ, c, ?_, by rwa [MonoidHom.ker_codRestrict], ?_⟩
  · rw [MonoidHom.range_eq_map, map_codRestrict_eq, ← MonoidHom.range_eq_map, hrange]
  · rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [map_codRestrict_eq, map_codRestrict_eq, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [map_codRestrict_eq, map_codRestrict_eq, h1, h2]
      exact ⟨rfl, rfl⟩

theorem linearBlockStandardPair_symm {K : Type} [Field K] {W U V : Subgroup X}
    (h : WeakCT.LinearBlockStandardPair K W U V) : WeakCT.LinearBlockStandardPair K W V U := by
  obtain ⟨θ, c, hr, hk, h1 | h1⟩ := h
  · exact ⟨θ, c, hr, hk, Or.inr h1⟩
  · exact ⟨θ, c, hr, hk, Or.inl h1⟩

theorem unitaryBlockStandardPair_symm {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] {W U V : Subgroup X} (h : Phan.UnitaryBlockStandardPair K p f W U V) :
    Phan.UnitaryBlockStandardPair K p f W V U := by
  obtain ⟨θ, c, hr, hk, h1 | h1⟩ := h
  · exact ⟨θ, c, hr, hk, Or.inr h1⟩
  · exact ⟨θ, c, hr, hk, Or.inl h1⟩

end Restrict

section PairSup

variable {F : Type} [Field F] {G : Type} [Group G]

theorem LinearA2Pair.linearBlockStandardPair_sup {E K L : Subgroup G} (h : LinearA2Pair F E K L) :
    WeakCT.LinearBlockStandardPair F (K ⊔ L) K L := by
  obtain ⟨θ, hker, hK, hL, -, -⟩ := h
  have e : ∀ B : Subgroup SL(3, F),
      B.map (MulAut.conj (1 : SL(3, F))⁻¹).toMonoidHom = B := fun B => by
    rw [inv_one]
    exact conjSub_one B
  refine ⟨θ, 1, ?_, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.range_eq_map, ← WeakCT.B12_sup_B23 (K := F), Subgroup.map_sup, hK, hL]
  · rw [e, hK]
  · rw [e, hL]

theorem LinearPair.linearBlockStandardPair_sup {E K L : Subgroup G} (h : LinearPair F E K L) :
    WeakCT.LinearBlockStandardPair F (K ⊔ L) K L := by
  rcases h with h | h
  · exact h.linearBlockStandardPair_sup
  · rw [sup_comm]
    exact linearBlockStandardPair_symm h.linearBlockStandardPair_sup

theorem LinearA2Pair.nonempty_equiv_left {E K L : Subgroup G} (h : LinearA2Pair F E K L) :
    Nonempty (SL(2, F) ≃* ↥K) := by
  obtain ⟨θ, hker, hK, -, -, -⟩ := h
  have hinj := WeakCT.comp_blockSL_injective (K := F) hker (i := 0) (k := 2) (by omega)
    (by omega)
  have hrange : (θ.comp (WeakCT.blockSL F 3 2 0 (by omega))).range = K := by
    rw [MonoidHom.range_comp]
    exact hK
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem LinearA2Pair.nonempty_equiv_right {E K L : Subgroup G} (h : LinearA2Pair F E K L) :
    Nonempty (SL(2, F) ≃* ↥L) := by
  obtain ⟨θ, hker, -, hL, -, -⟩ := h
  have hinj := WeakCT.comp_blockSL_injective (K := F) hker (i := 1) (k := 2) (by omega)
    (by omega)
  have hrange : (θ.comp (WeakCT.blockSL F 3 2 1 (by omega))).range = L := by
    rw [MonoidHom.range_comp]
    exact hL
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem LinearPair.nonempty_equiv_fst {E K L : Subgroup G} (h : LinearPair F E K L) :
    Nonempty (SL(2, F) ≃* ↥K) := by
  rcases h with h | h
  · exact h.nonempty_equiv_left
  · exact h.nonempty_equiv_right

variable {K' : Type} [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]

theorem UnitaryA2Pair.unitaryBlockStandardPair_sup (hK : Nat.card K' = (p ^ f) ^ 2)
    (hq : p ^ f ≠ 2) {E P Q : Subgroup G} (h : UnitaryA2Pair K' p f E P Q) :
    Phan.UnitaryBlockStandardPair K' p f (P ⊔ Q) P Q := by
  obtain ⟨θ, hker, hP, hQ, -, -⟩ := h
  have e : ∀ B : Subgroup (Phan.Su K' p f 3),
      B.map (MulAut.conj (1 : Phan.Su K' p f 3)⁻¹).toMonoidHom = B := fun B => by
    rw [inv_one]
    exact conjSub_one B
  refine ⟨θ, 1, ?_, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.range_eq_map, ← Phan.B12_sup_B23_eq_top hK hq, Subgroup.map_sup, hP, hQ]
  · rw [e, hP]
  · rw [e, hQ]

theorem UnitaryPair.unitaryBlockStandardPair_sup (hK : Nat.card K' = (p ^ f) ^ 2)
    (hq : p ^ f ≠ 2) {E P Q : Subgroup G} (h : UnitaryPair K' p f E P Q) :
    Phan.UnitaryBlockStandardPair K' p f (P ⊔ Q) P Q := by
  rcases h with h | h
  · exact h.unitaryBlockStandardPair_sup hK hq
  · rw [sup_comm]
    exact unitaryBlockStandardPair_symm (h.unitaryBlockStandardPair_sup hK hq)

theorem UnitaryA2Pair.nonempty_equiv_left (hK : Nat.card K' = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryA2Pair K' p f E P Q) : Nonempty (Phan.Su K' p f 2 ≃* ↥P) := by
  obtain ⟨θ, hker, hP, -, -, -⟩ := h
  have hinj := Phan.comp_embSUid_injective hK hker 2
  have hrange : (θ.comp (CFSG.LieType.Steinberg.embSUid
      (CFSG.LieType.BorelTits.unitaryInvolution K' p f) 2)).range = P := by
    rw [MonoidHom.range_comp]
    exact hP
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem UnitaryA2Pair.nonempty_equiv_right (hK : Nat.card K' = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryA2Pair K' p f E P Q) : Nonempty (Phan.Su K' p f 2 ≃* ↥Q) := by
  obtain ⟨θ, hker, -, hQ, -, -⟩ := h
  have hinj := Phan.comp_embSUid_injective hK hker 0
  have hrange : (θ.comp (CFSG.LieType.Steinberg.embSUid
      (CFSG.LieType.BorelTits.unitaryInvolution K' p f) 0)).range = Q := by
    rw [MonoidHom.range_comp]
    exact hQ
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

theorem UnitaryPair.nonempty_equiv_fst (hK : Nat.card K' = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryPair K' p f E P Q) : Nonempty (Phan.Su K' p f 2 ≃* ↥P) := by
  rcases h with h | h
  · exact h.nonempty_equiv_left hK
  · exact h.nonempty_equiv_right hK

end PairSup

section Transpositions

open Equiv

@[expose] def adjSwap (n : ℕ) (i : Fin n) : Perm (Fin (n + 1)) := swap i.castSucc i.succ

theorem isSwap_adjSwap (n : ℕ) (i : Fin n) : (adjSwap n i).IsSwap :=
  ⟨i.castSucc, i.succ, (Fin.castSucc_lt_succ).ne, rfl⟩

theorem adjSwap_injective (n : ℕ) : Function.Injective (adjSwap n) := by
  intro i j h
  have h1 := congrArg (fun τ : Perm (Fin (n + 1)) => τ i.castSucc) h
  simp only [adjSwap, swap_apply_left] at h1
  by_cases hij : i.castSucc = j.castSucc
  · exact Fin.castSucc_injective _ hij
  · by_cases hij2 : i.castSucc = j.succ
    · rw [hij2, swap_apply_right] at h1
      have := congrArg Fin.val h1
      simp [Fin.ext_iff] at hij2 this
      omega
    · rw [swap_apply_of_ne_of_ne hij hij2] at h1
      have := congrArg Fin.val h1
      simp at this

theorem closure_adjSwap (n : ℕ) : Subgroup.closure (Set.range (adjSwap n)) = ⊤ :=
  Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ n)

theorem mem_reflSet_adjSwap_iff {n : ℕ} (hn : 1 ≤ n) (r : Perm (Fin (n + 1))) :
    r ∈ reflSet (adjSwap n) ↔ r.IsSwap := by
  constructor
  · rintro ⟨w, i, rfl⟩
    refine ⟨w i.castSucc, w i.succ, fun h => ?_, ?_⟩
    · exact (Fin.castSucc_lt_succ).ne (w.injective h)
    · rw [adjSwap, swap_apply_apply]
  · rintro ⟨x, y, hxy, rfl⟩
    obtain ⟨w, hw⟩ := isConj_iff.mp
      (Equiv.Perm.isConj_swap (w := (⟨0, hn⟩ : Fin n).castSucc) (x := (⟨0, hn⟩ : Fin n).succ)
        (y := x) (z := y) (Fin.castSucc_lt_succ).ne hxy)
    exact ⟨w, ⟨0, hn⟩, hw.symm⟩

theorem adjSwap_comm {n : ℕ} {i j : Fin n} (h : (i : ℕ) + 1 < j) :
    adjSwap n i * adjSwap n j = adjSwap n j * adjSwap n i := by
  apply Perm.Disjoint.commute
  apply Perm.disjoint_swap_swap
  simp [Fin.ext_iff]
  omega

theorem adjSwap_not_comm {n : ℕ} {i j : Fin n} (h : (j : ℕ) = i + 1) :
    adjSwap n i * adjSwap n j ≠ adjSwap n j * adjSwap n i := by
  intro hc
  have h1 := congrArg (fun τ : Perm (Fin (n + 1)) => τ i.castSucc) hc
  simp only [adjSwap, Perm.mul_apply, swap_apply_left] at h1
  have e1 : swap j.castSucc j.succ i.castSucc = i.castSucc := by
    apply swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff] <;> omega
  have e2 : swap j.castSucc j.succ i.succ = j.succ := by
    have : i.succ = j.castSucc := by simp [Fin.ext_iff]; omega
    rw [this, swap_apply_left]
  rw [e1, swap_apply_left, e2] at h1
  have := congrArg Fin.val h1
  simp at this
  omega

theorem adjSwap_exists_not_comm {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    ∃ j : Fin n, adjSwap n i * adjSwap n j ≠ adjSwap n j * adjSwap n i := by
  by_cases hi : (i : ℕ) + 1 < n
  · exact ⟨⟨i + 1, hi⟩, adjSwap_not_comm (by simp)⟩
  · exact ⟨⟨i - 1, by omega⟩,
      Ne.symm (adjSwap_not_comm (i := ⟨i - 1, by omega⟩) (j := i) (by simp; omega))⟩

theorem swap_eq_swap_of_moved {α : Type*} [DecidableEq α] {σ : Perm α} (hσ : σ.IsSwap) {x : α}
    (hx : σ x ≠ x) : σ = swap x (σ x) := by
  obtain ⟨a, b, hab, rfl⟩ := hσ
  by_cases hxa : x = a
  · subst hxa
    simp
  · by_cases hxb : x = b
    · subst hxb
      simp [swap_comm]
    · exact absurd (swap_apply_of_ne_of_ne hxa hxb) hx

theorem commute_swaps_iff_disjoint {α : Type*} [DecidableEq α] {σ τ : Perm α} (hσ : σ.IsSwap)
    (hτ : τ.IsSwap) (hne : σ ≠ τ) : σ * τ = τ * σ ↔ σ.Disjoint τ := by
  constructor
  · intro hc
    by_contra hnd
    have : ∃ x, σ x ≠ x ∧ τ x ≠ x := by
      by_contra h
      apply hnd
      intro x
      by_cases h1 : σ x = x
      · exact Or.inl h1
      · exact Or.inr (Classical.byContradiction fun h2 => h ⟨x, h1, h2⟩)
    obtain ⟨x, hx1, hx2⟩ := this
    have e1 := swap_eq_swap_of_moved hσ hx1
    have e2 := swap_eq_swap_of_moved hτ hx2
    have hyz : σ x ≠ τ x := fun h => hne (by rw [e1, e2, h])
    have h1 := congrArg (fun π : Perm α => π x) hc
    simp only [Perm.mul_apply] at h1
    have a1 : σ (τ x) = τ x := by
      rw [e1]
      exact swap_apply_of_ne_of_ne hx2 (Ne.symm hyz)
    have a2 : τ (σ x) = σ x := by
      rw [e2]
      exact swap_apply_of_ne_of_ne hx1 hyz
    rw [a1, a2] at h1
    exact hyz h1.symm
  · intro h
    exact h.commute.eq

end Transpositions

section TypeAData

open Equiv

variable {F : Type} [Field F] [Finite F] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

structure TypeAData (Fr : ToralFrame F Ω E S) (n : ℕ) where
  β : ↥S ≃ {τ : Perm (Fin (n + 1)) // τ.IsSwap}
  comm_iff : ∀ K L : ↥S, K ≠ L →
    (Commutes (K : Subgroup G) (L : Subgroup G) ↔
      (β K : Perm (Fin (n + 1))).Disjoint (β L : Perm (Fin (n + 1))))
  rho_eq : ∀ K L : ↥S, (β (Fr.rho K L) : Perm (Fin (n + 1))) =
    (β K : Perm (Fin (n + 1))) * (β L : Perm (Fin (n + 1))) * (β K : Perm (Fin (n + 1)))⁻¹

@[expose] noncomputable def TypeAData.toWeylData {Fr : ToralFrame F Ω E S} {n : ℕ}
    (T : TypeAData Fr n) (hn : 1 ≤ n) : WeylData Fr (Fin n) (Perm (Fin (n + 1))) where
  s := adjSwap n
  gen := closure_adjSwap n
  β := T.β.trans (Equiv.subtypeEquivProp
    (funext fun r => propext (mem_reflSet_adjSwap_iff hn r).symm))
  comm_iff K L hKL := by
    have hne : (T.β K : Perm (Fin (n + 1))) ≠ T.β L := fun h => hKL (T.β.injective (Subtype.ext h))
    rw [T.comm_iff K L hKL, ← commute_swaps_iff_disjoint (T.β K).2 (T.β L).2 hne]
    rfl
  rho_eq K L := T.rho_eq K L

@[expose] noncomputable def TypeAData.base {Fr : ToralFrame F Ω E S} {n : ℕ}
    (T : TypeAData Fr n) (i : Fin n) : ↥S :=
  T.β.symm ⟨adjSwap n i, isSwap_adjSwap n i⟩

theorem TypeAData.base_eq {Fr : ToralFrame F Ω E S} {n : ℕ} (T : TypeAData Fr n) (hn : 1 ≤ n)
    (i : Fin n) : (T.toWeylData hn).base i = T.base i :=
  rfl

theorem TypeAData.iSup_base {Fr : ToralFrame F Ω E S} {n : ℕ} (T : TypeAData Fr n) (hn : 1 ≤ n) :
    ⨆ i, (T.base i : Subgroup G) = sSup S :=
  (T.toWeylData hn).span_eq_sSup

theorem TypeAData.exists_conj {Fr : ToralFrame F Ω E S} {n : ℕ} (T : TypeAData Fr n) (hn : 1 ≤ n)
    (K : ↥S) : ∃ (i : Fin n) (g : Subgroup.normalizer (E : Set G)),
      g ∈ Subgroup.closure (Set.range fun j : Fin n =>
        (⟨Fr.w (T.base j), Fr.w_mem_normalizer (T.base j)⟩ : Subgroup.normalizer (E : Set G))) ∧
      Fr.act g (T.base i) = K :=
  (T.toWeylData hn).exists_conj K

theorem TypeAData.nonCommConnected {Fr : ToralFrame F Ω E S} {n : ℕ} (T : TypeAData Fr n) :
    NonCommConnected S := by
  obtain ⟨K₀, hK₀, -⟩ := Fr.exists_ne
  have : Nonempty ↥S := ⟨⟨K₀, hK₀⟩⟩
  refine SimpleGraph.Connected.mk (fun K L => ?_)
  by_cases hKL : K = L
  · subst hKL
    exact SimpleGraph.Reachable.refl K
  by_cases hc : Commutes (K : Subgroup G) (L : Subgroup G)
  · have hd := (T.comm_iff K L hKL).mp hc
    obtain ⟨a, b, hab, hKe⟩ := (T.β K).2
    obtain ⟨c, d, hcd, hLe⟩ := (T.β L).2
    have h1 := hd b
    rw [hKe, hLe, swap_apply_right] at h1
    have hLb : swap c d b = b := h1.resolve_left hab
    have hbc : b ≠ c := by
      rintro rfl
      rw [swap_apply_left] at hLb
      exact hcd hLb.symm
    have h2 := hd c
    rw [hKe, hLe, swap_apply_left] at h2
    have hKc : swap a b c = c := h2.resolve_right hcd.symm
    have hac : a ≠ c := by
      rintro rfl
      rw [swap_apply_left] at hKc
      exact hab hKc.symm
    set M : ↥S := T.β.symm ⟨swap b c, ⟨b, c, hbc, rfl⟩⟩ with hM
    have hβM : (T.β M : Perm (Fin (n + 1))) = swap b c := by
      rw [hM, Equiv.apply_symm_apply]
    have hKM : K ≠ M := by
      intro h
      have := congrArg (fun K' : ↥S => (T.β K' : Perm (Fin (n + 1))) a) h
      simp only [hKe, hβM, swap_apply_left] at this
      rw [swap_apply_of_ne_of_ne hab.symm.symm hac] at this
      exact hab this.symm
    have hKM' : ¬ Commutes (K : Subgroup G) (M : Subgroup G) := by
      intro hcm
      rcases (T.comm_iff K M hKM).mp hcm b with h | h
      · rw [hKe, swap_apply_right] at h
        exact hab h
      · rw [hβM, swap_apply_left] at h
        exact hbc h.symm
    have hML : M ≠ L := by
      intro h
      have := congrArg (fun K' : ↥S => (T.β K' : Perm (Fin (n + 1))) b) h
      simp only [hLe, hβM, swap_apply_left] at this
      have hbd : b ≠ d := fun h' => by rw [h'] at hLb; exact hcd (by simpa using hLb)
      rw [swap_apply_of_ne_of_ne hbc hbd] at this
      exact hbc this.symm
    have hML' : ¬ Commutes (M : Subgroup G) (L : Subgroup G) := by
      intro hcm
      rcases (T.comm_iff M L hML).mp hcm c with h | h
      · rw [hβM, swap_apply_right] at h
        exact hbc h
      · rw [hLe, swap_apply_left] at h
        exact hcd h.symm
    exact (SimpleGraph.Adj.reachable (nonCommGraph_adj.mpr ⟨hKM, hKM'⟩)).trans
      (SimpleGraph.Adj.reachable (nonCommGraph_adj.mpr ⟨hML, hML'⟩))
  · exact SimpleGraph.Adj.reachable (nonCommGraph_adj.mpr ⟨hKL, hc⟩)

end TypeAData

section Glue

variable {F : Type} [Field F] [Finite F] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)} {Fr : ToralFrame F Ω E S} {ι W : Type} [Group W]
  (WD : WeylData Fr ι W)

theorem WeylData.linearPair_base {i j : ι} (h : WD.s i * WD.s j ≠ WD.s j * WD.s i)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ LinearPair F E K L) :
    LinearPair F E (WD.base i : Subgroup G) (WD.base j : Subgroup G) := by
  obtain ⟨hne, hnc⟩ := WD.base_not_commutes h
  rcases hA2 _ (WD.base i).2 _ (WD.base j).2 (fun h => hne (Subtype.ext h)) with hc | hp
  · exact absurd hc hnc
  · exact hp

theorem WeylData.linearBlockStandardPair {i j : ι} (h : WD.s i * WD.s j ≠ WD.s j * WD.s i)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ LinearPair F E K L) :
    WeakCT.LinearBlockStandardPair F (WD.baseIn i ⊔ WD.baseIn j) (WD.baseIn i) (WD.baseIn j) := by
  have := linearBlockStandardPair_subgroupOf (J := WD.span)
    (sup_le (WD.base_le_span i) (WD.base_le_span j))
    (WD.linearPair_base h hA2).linearBlockStandardPair_sup
  have h2 : WD.baseIn i ⊔ WD.baseIn j =
      ((WD.base i : Subgroup G) ⊔ (WD.base j : Subgroup G)).subgroupOf WD.span :=
    (Subgroup.subgroupOf_sup (WD.base_le_span i) (WD.base_le_span j)).symm
  rw [h2]
  exact this

theorem WeylData.exists_pair_linear {i j : ι} (h : WD.s i * WD.s j ≠ WD.s j * WD.s i)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ LinearPair F E K L) :
    ∃ W', WeakCT.LinearBlockStandardPair F W' (WD.baseIn i) (WD.baseIn j) :=
  ⟨_, WD.linearBlockStandardPair h hA2⟩

theorem WeylData.nonempty_equiv_linear {i j : ι} (h : WD.s i * WD.s j ≠ WD.s j * WD.s i)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ LinearPair F E K L) :
    Nonempty (SL(2, F) ≃* ↥(WD.baseIn i)) := by
  obtain ⟨e⟩ := (WD.linearPair_base h hA2).nonempty_equiv_fst
  exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe (WD.base_le_span i)).symm⟩

variable {K' : Type} [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]

theorem WeylData.unitaryPair_base {i j : ι} (h : WD.s i * WD.s j ≠ WD.s j * WD.s i)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ UnitaryPair K' p f E K L) :
    UnitaryPair K' p f E (WD.base i : Subgroup G) (WD.base j : Subgroup G) := by
  obtain ⟨hne, hnc⟩ := WD.base_not_commutes h
  rcases hA2 _ (WD.base i).2 _ (WD.base j).2 (fun h => hne (Subtype.ext h)) with hc | hp
  · exact absurd hc hnc
  · exact hp

theorem WeylData.unitaryBlockStandardPair {i j : ι} (hK : Nat.card K' = (p ^ f) ^ 2)
    (hq : p ^ f ≠ 2) (h : WD.s i * WD.s j ≠ WD.s j * WD.s i)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ UnitaryPair K' p f E K L) :
    Phan.UnitaryBlockStandardPair K' p f (WD.baseIn i ⊔ WD.baseIn j) (WD.baseIn i)
      (WD.baseIn j) := by
  have := unitaryBlockStandardPair_subgroupOf (J := WD.span)
    (sup_le (WD.base_le_span i) (WD.base_le_span j))
    ((WD.unitaryPair_base h hA2).unitaryBlockStandardPair_sup hK hq)
  have h2 : WD.baseIn i ⊔ WD.baseIn j =
      ((WD.base i : Subgroup G) ⊔ (WD.base j : Subgroup G)).subgroupOf WD.span :=
    (Subgroup.subgroupOf_sup (WD.base_le_span i) (WD.base_le_span j)).symm
  rw [h2]
  exact this

theorem WeylData.nonempty_equiv_unitary {i j : ι} (hK : Nat.card K' = (p ^ f) ^ 2)
    (h : WD.s i * WD.s j ≠ WD.s j * WD.s i)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ UnitaryPair K' p f E K L) :
    Nonempty (Phan.Su K' p f 2 ≃* ↥(WD.baseIn i)) := by
  obtain ⟨e⟩ := (WD.unitaryPair_base h hA2).nonempty_equiv_fst hK
  exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe (WD.base_le_span i)).symm⟩

end Glue

section Recognition

variable {F : Type} [Field F] [Finite F] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}

theorem TypeAData.weakCTSystem {Fr : ToralFrame F Ω E S} {n : ℕ} (T : TypeAData Fr n)
    (hn : 2 ≤ n) (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ LinearPair F E K L) :
    WeakCT.WeakCTSystem F n (T.toWeylData (by omega : 1 ≤ n)).baseIn
      (fun i j => (T.toWeylData (by omega : 1 ≤ n)).baseIn i ⊔
        (T.toWeylData (by omega : 1 ≤ n)).baseIn j) :=
  { iso := fun i => by
      obtain ⟨j, hj⟩ := adjSwap_exists_not_comm hn i
      exact (T.toWeylData (by omega : 1 ≤ n)).nonempty_equiv_linear hj hA2
    join := fun _ _ _ => rfl
    comm := fun i j hij => (T.toWeylData (by omega : 1 ≤ n)).baseIn_commute
      ((T.toWeylData (by omega : 1 ≤ n)).base_commutes (adjSwap_injective n)
        (fun h => by subst h; omega) (adjSwap_comm hij))
    pair := fun i j hij => (T.toWeylData (by omega : 1 ≤ n)).linearBlockStandardPair
      (adjSwap_not_comm hij) hA2
    gen := (T.toWeylData (by omega : 1 ≤ n)).iSup_baseIn }

theorem TypeAData.weakPhanA {K' : Type} [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime]
    [CharP K' p] {Fr : ToralFrame F Ω E S} {n : ℕ} (T : TypeAData Fr n) (hn : 2 ≤ n)
    (hK : Nat.card K' = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ UnitaryPair K' p f E K L) :
    Phan.WeakPhanA K' p f n (T.toWeylData (by omega : 1 ≤ n)).baseIn
      (fun i j => (T.toWeylData (by omega : 1 ≤ n)).baseIn i ⊔
        (T.toWeylData (by omega : 1 ≤ n)).baseIn j) :=
  { iso := fun i => by
      obtain ⟨j, hj⟩ := adjSwap_exists_not_comm hn i
      exact (T.toWeylData (by omega : 1 ≤ n)).nonempty_equiv_unitary hK hj hA2
    join := fun _ _ _ => rfl
    comm := fun i j hij => (T.toWeylData (by omega : 1 ≤ n)).baseIn_commute
      ((T.toWeylData (by omega : 1 ≤ n)).base_commutes (adjSwap_injective n)
        (fun h => by subst h; omega) (adjSwap_comm hij))
    pair := fun i j hij => (T.toWeylData (by omega : 1 ≤ n)).unitaryBlockStandardPair hK hq
      (adjSwap_not_comm hij) hA2
    gen := (T.toWeylData (by omega : 1 ≤ n)).iSup_baseIn }

theorem typeA_linear (Fr : ToralFrame F Ω E S) {n : ℕ} (hn : 3 ≤ n) (T : TypeAData Fr n)
    {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ LinearPair F E K L) :
    ∃ ψ : SL(n + 1, F) →* ↥(sSup S), Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center SL(n + 1, F) ∧ CFSG.IsQuasisimple ↥(sSup S) ∧
      CFSG.Blueprint.LieModel (↥(sSup S) ⧸ Subgroup.center ↥(sSup S))
        CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f := by
  have hq : 4 ≤ p ^ f := by
    have := Fr.five
    omega
  have key := WeakCT.weakCT_recognition F p f hp hF hq hn (T.weakCTSystem (by omega) hA2)
  rw [(T.toWeylData (by omega : 1 ≤ n)).span_eq_sSup] at key
  exact key

theorem typeA_unitary {K' : Type} [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]
    (Fr : ToralFrame F Ω E S) {n : ℕ} (hn : 3 ≤ n) (T : TypeAData Fr n)
    (hK : Nat.card K' = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ UnitaryPair K' p f E K L) :
    ∃ θ : Phan.Su K' p f (n + 1) →* ↥(sSup S), Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center (Phan.Su K' p f (n + 1)) := by
  have hq5 : 5 ≤ p ^ f := by
    have := Fr.five
    omega
  have key := Phan.weakPhan_recognition K' p f hK hq5 hn
    (T.weakPhanA (by omega) hK (by omega) hA2)
  rw [(T.toWeylData (by omega : 1 ≤ n)).span_eq_sSup] at key
  exact key

theorem exists_prime_pow_card (F : Type*) [Field F] [Finite F] :
    ∃ p f : ℕ, p.Prime ∧ Nat.card F = p ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  exact ⟨ringChar F, n, hp, by rw [Nat.card_eq_fintype_card, hcard]⟩

theorem typeA_linear_exists (Fr : ToralFrame F Ω E S) {n : ℕ} (hn : 3 ≤ n) (T : TypeAData Fr n)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → Commutes K L ∨ LinearPair F E K L) :
    ∃ p f : ℕ, p.Prime ∧ Nat.card F = p ^ f ∧
      ∃ ψ : SL(n + 1, F) →* ↥(sSup S), Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center SL(n + 1, F) ∧ CFSG.IsQuasisimple ↥(sSup S) ∧
        CFSG.Blueprint.LieModel (↥(sSup S) ⧸ Subgroup.center ↥(sSup S))
          CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f := by
  obtain ⟨p, f, hp, hF⟩ := exists_prime_pow_card F
  exact ⟨p, f, hp, hF, typeA_linear Fr hn T hp hF hA2⟩

theorem typeA_end_to_end {K' : Type} [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]
    (Fr : ToralFrame F Ω E S) {n : ℕ} (hn : 3 ≤ n) (T : TypeAData Fr n)
    (hK : Nat.card K' = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f)
    (hA2 : ∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Commutes K L ∨ LinearPair F E K L ∨ UnitaryPair K' p f E K L) :
    ((∀ K ∈ S, Nat.card (centPart K E) = Nat.card F - 1) ∧
        ∃ ψ : SL(n + 1, F) →* ↥(sSup S), Function.Surjective ψ ∧
          ψ.ker ≤ Subgroup.center SL(n + 1, F) ∧ CFSG.IsQuasisimple ↥(sSup S) ∧
          CFSG.Blueprint.LieModel (↥(sSup S) ⧸ Subgroup.center ↥(sSup S))
            CFSG.Assembly.LowTwoRank.StatedLieTag.PSL (n + 1) p f) ∨
      ((∀ K ∈ S, Nat.card (centPart K E) = Nat.card F + 1) ∧
        ∃ θ : Phan.Su K' p f (n + 1) →* ↥(sSup S), Function.Surjective θ ∧
          θ.ker ≤ Subgroup.center (Phan.Su K' p f (n + 1))) := by
  have hpair : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L →
      LinearPair F E K L ∨ UnitaryPair K' p f E K L := fun K hK' L hL hKL hnc => by
    rcases hA2 K hK' L hL hKL with h | h
    · exact absurd h hnc
    · exact h
  rcases Fr.sign_constant_pairs T.nonCommConnected hK hF hpair with ⟨hc, hl⟩ | ⟨hc, hu⟩
  · exact Or.inl ⟨hc, typeA_linear Fr hn T (Fact.out : p.Prime) hF fun K hK' L hL hKL =>
      (em (Commutes K L)).imp_right fun hnc => hl K hK' L hL hKL hnc⟩
  · exact Or.inr ⟨hc, typeA_unitary Fr hn T hK hF fun K hK' L hL hKL =>
      (em (Commutes K L)).imp_right fun hnc => hu K hK' L hL hKL hnc⟩

end Recognition

end CFSG.ClassicalInvolution.Generic

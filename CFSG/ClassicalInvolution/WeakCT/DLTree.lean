module

public import CFSG.ClassicalInvolution.WeakCT.Tree
public import CFSG.ClassicalInvolution.WeakCT.SpAgree
public import CFSG.ClassicalInvolution.WeakCT.SpPair

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open scoped MatrixGroups

section Frame

variable {K : Type} [Field K] [Finite K] {X : Type} [Group X] {r : ℕ}
  {adj : Fin r → Fin r → Prop} {par : Fin r → Fin r} {dep : Fin r → ℕ} {k₀ : Fin r}

theorem exists_frame_of_tree_sp (hK : 4 ≤ Nat.card K) (hT : RootedTree adj par dep k₀)
    (hroot : ∃ c, adj k₀ c ∨ adj c k₀) {U : Fin r → Subgroup X} {a b : Fin r} (hab : adj a b)
    (hpar : par b = a) (hb0 : b ≠ k₀)
    (hcomm : ∀ i j, i ≠ j → ¬ adj i j → ¬ adj j i → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j, adj i j → ¬ (i = a ∧ j = b) →
      ∃ W, LinearBlockStandardPair K W (U i) (U j))
    (hsp : ∃ W, SymplecticBlockStandardPair K W (U a) (U b)) :
    ∃ ρ : Fin r → SL(2, K) →* X, (∀ k, Function.Injective (ρ k) ∧ (ρ k).range = U k) ∧
      (∀ i j, adj i j → ¬ (i = a ∧ j = b) → ∃ ψ : SL(3, K) →* X,
        ψ.comp (blk K 0) = ρ i ∧ ψ.comp (blk K 1) = ρ j) ∧
      ∃ ψ : StatedSp 2 K →* X, ψ.ker ≤ Subgroup.center (StatedSp 2 K) ∧
        ψ.comp (spBlock K 1) = ρ a ∧ ψ.comp (spBlock K 0) = ρ b := by
  classical
  have hK3 : 3 ≤ Nat.card K := by omega
  obtain ⟨adj', hadj'⟩ : ∃ adj' : Fin r → Fin r → Prop,
      ∀ i j, adj' i j ↔ adj i j ∧ ¬ (i = a ∧ j = b) := ⟨_, fun _ _ => Iff.rfl⟩
  have hadj'adj : ∀ i j, adj' i j → adj i j := fun i j h => ((hadj' i j).1 h).1
  have hne_ab : a ≠ b := fun h => by
    subst h
    exact hT.asymm _ _ hab hab
  have hba : ¬ adj b a := hT.asymm _ _ hab
  have hnorm : ∀ i j, adj' i j → ∃ θ : SL(3, K) →* X, θ.ker ≤ Subgroup.center SL(3, K) ∧
      (Bs K 0).map θ = U i ∧ (Bs K 1).map θ = U j := by
    intro i j h
    obtain ⟨W, hW⟩ := hpair i j ((hadj' i j).1 h).1 ((hadj' i j).1 h).2
    obtain ⟨θ, -, hker, h0, h1⟩ := pair_normalize hW
    exact ⟨θ, hker, h0, h1⟩
  choose θ hθk hθ0 hθ1 using hnorm
  obtain ⟨θd, -, hdk, hd1i, hd0i, hd1, hd0⟩ := pair_normalize_sp hsp.choose_spec
  have hdf : ∀ v : Fin 2, Function.Injective (θd.comp (spBlock K v)) :=
    Fin.forall_fin_two.2 ⟨hd0i, hd1i⟩
  have hnb : ∀ k p q, (adj k p ∨ adj p k) → (adj k q ∨ adj q k) → p ≠ q →
      ∀ x ∈ U p, ∀ y ∈ U q, x * y = y * x := by
    intro k p q hkp hkq hpq x hx y hy
    refine hcomm p q hpq (fun h => hT.no_triangle hkp hkq (Or.inl h) hpq) (fun h =>
      hT.no_triangle hkp hkq (Or.inr h) hpq) x hx y hy
  let TS1 : Subgroup X := (diagTorus2 K).map (θd.comp (spBlock K 1))
  let TS0 : Subgroup X := (diagTorus2 K).map (θd.comp (spBlock K 0))
  have agree_ff : ∀ k p q (hp : adj' k p) (hq : adj' k q),
      (Ds K 0).map (θ k p hp) = (Ds K 0).map (θ k q hq) := by
    intro k p q hp hq
    by_cases hpq : p = q
    · subst hpq; rfl
    · exact torus_agree_gen hK3 0 0 (hθk k p hp) (hθk k q hq) (by rw [hθ0, hθ0])
        (fun x hx y hy => by
          rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx hy
          exact hnb k p q (Or.inl (hadj'adj _ _ hp)) (Or.inl (hadj'adj _ _ hq)) hpq x hx y hy)
  have agree_fs : ∀ k p q (hp : adj' k p) (hq : adj' q k),
      (Ds K 0).map (θ k p hp) = (Ds K 1).map (θ q k hq) := by
    intro k p q hp hq
    have hpq : p ≠ q := fun h => by
      subst h
      exact hT.asymm _ _ (hadj'adj _ _ hp) (hadj'adj _ _ hq)
    exact torus_agree_gen hK3 0 1 (hθk k p hp) (hθk q k hq) (by rw [hθ0, hθ1])
      (fun x hx y hy => by
        rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hx
        rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hy
        exact hnb k p q (Or.inl (hadj'adj _ _ hp)) (Or.inr (hadj'adj _ _ hq)) hpq x hx y hy)
  have agree_ss : ∀ k p q (hp : adj' p k) (hq : adj' q k),
      (Ds K 1).map (θ p k hp) = (Ds K 1).map (θ q k hq) := by
    intro k p q hp hq
    by_cases hpq : p = q
    · subst hpq; rfl
    · exact torus_agree_gen hK3 1 1 (hθk p k hp) (hθk q k hq) (by rw [hθ1, hθ1])
        (fun x hx y hy => by
          rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hx hy
          exact hnb k p q (Or.inr (hadj'adj _ _ hp)) (Or.inr (hadj'adj _ _ hq)) hpq x hx y hy)
  have agree_a_f : ∀ q (hq : adj' a q), TS1 = (Ds K 0).map (θ a q hq) := by
    intro q hq
    have hbq : b ≠ q := fun h => by
      subst h
      exact ((hadj' _ _).1 hq).2 ⟨rfl, rfl⟩
    exact torus_agree_sp_sl3 hK 1 0 hdf (hθk a q hq) (hd1.trans (hθ0 a q hq).symm)
      (fun x hx y hy => by
        rw [show (1 : Fin 2).rev = 0 from rfl, hd0] at hx
        rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hy
        exact hnb a b q (Or.inl hab) (Or.inl (hadj'adj _ _ hq)) hbq x hx y hy)
  have agree_a_s : ∀ q (hq : adj' q a), TS1 = (Ds K 1).map (θ q a hq) := by
    intro q hq
    have hbq : b ≠ q := fun h => by
      subst h
      exact hba (hadj'adj _ _ hq)
    exact torus_agree_sp_sl3 hK 1 1 hdf (hθk q a hq) (hd1.trans (hθ1 q a hq).symm)
      (fun x hx y hy => by
        rw [show (1 : Fin 2).rev = 0 from rfl, hd0] at hx
        rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hy
        exact hnb a b q (Or.inl hab) (Or.inr (hadj'adj _ _ hq)) hbq x hx y hy)
  have agree_b_f : ∀ q (hq : adj' b q), TS0 = (Ds K 0).map (θ b q hq) := by
    intro q hq
    have haq : a ≠ q := fun h => by
      subst h
      exact hba (hadj'adj _ _ hq)
    exact torus_agree_sp_sl3 hK 0 0 hdf (hθk b q hq) (hd0.trans (hθ0 b q hq).symm)
      (fun x hx y hy => by
        rw [show (0 : Fin 2).rev = 1 from rfl, hd1] at hx
        rw [show (0 : Fin 2).rev = 1 from rfl, hθ1] at hy
        exact hnb b a q (Or.inr hab) (Or.inl (hadj'adj _ _ hq)) haq x hx y hy)
  have agree_b_s : ∀ q (hq : adj' q b), TS0 = (Ds K 1).map (θ q b hq) := by
    intro q hq
    have haq : a ≠ q := fun h => by
      subst h
      exact ((hadj' _ _).1 hq).2 ⟨rfl, rfl⟩
    exact torus_agree_sp_sl3 hK 0 1 hdf (hθk q b hq) (hd0.trans (hθ1 q b hq).symm)
      (fun x hx y hy => by
        rw [show (0 : Fin 2).rev = 1 from rfl, hd1] at hx
        rw [show (1 : Fin 2).rev = 0 from rfl, hθ0] at hy
        exact hnb b a q (Or.inr hab) (Or.inr (hadj'adj _ _ hq)) haq x hx y hy)
  let Seen : Fin r → Subgroup X → Prop := fun k T =>
    (∃ q, ∃ h : adj' k q, (Ds K 0).map (θ k q h) = T) ∨
      (∃ q, ∃ h : adj' q k, (Ds K 1).map (θ q k h) = T) ∨ (k = a ∧ TS1 = T) ∨ (k = b ∧ TS0 = T)
  have seen_unique : ∀ k T T', Seen k T → Seen k T' → T = T' := by
    intro k T T' h1 h2
    rcases h1 with ⟨q, h, h1⟩ | ⟨q, h, h1⟩ | ⟨hk1, h1⟩ | ⟨hk1, h1⟩ <;>
      rcases h2 with ⟨q', h', h2⟩ | ⟨q', h', h2⟩ | ⟨hk2, h2⟩ | ⟨hk2, h2⟩ <;>
      rw [← h1, ← h2]
    · exact agree_ff k q q' h h'
    · exact agree_fs k q q' h h'
    · subst hk2; exact (agree_a_f q h).symm
    · subst hk2; exact (agree_b_f q h).symm
    · exact (agree_fs k q' q h' h).symm
    · exact agree_ss k q q' h h'
    · subst hk2; exact (agree_a_s q h).symm
    · subst hk2; exact (agree_b_s q h).symm
    · subst hk1; exact agree_a_f q' h'
    · subst hk1; exact agree_a_s q' h'
    · exact absurd (hk1.symm.trans hk2) hne_ab
    · subst hk1; exact agree_b_f q' h'
    · subst hk1; exact agree_b_s q' h'
    · exact absurd (hk2.symm.trans hk1) hne_ab
  let TorGood : Fin r → Subgroup X → Prop := fun k T => ∀ T', Seen k T' → T' = T
  have torGood_of_seen : ∀ k T, Seen k T → TorGood k T := fun k T hT' T' hT'' =>
    seen_unique k T' T hT'' hT'
  let N : Fin r → (SL(2, K) →* X) → Prop := fun k ρ =>
    Function.Injective ρ ∧ ρ.range = U k ∧ ∀ T, TorGood k T → (diagTorus2 K).map ρ = T
  let E : Fin r → (SL(2, K) →* X) → (SL(2, K) →* X) → Prop := fun k ρp ρc =>
    (adj' (par k) k → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρp ∧ ψ.comp (blk K 1) = ρc) ∧
      (adj' k (par k) → ∃ ψ : SL(3, K) →* X, ψ.comp (blk K 0) = ρc ∧ ψ.comp (blk K 1) = ρp) ∧
      (k = b → ∃ ψ : StatedSp 2 K →* X, ψ.ker ≤ Subgroup.center (StatedSp 2 K) ∧
        ψ.comp (spBlock K 1) = ρp ∧ ψ.comp (spBlock K 0) = ρc)
  have h₀ : ∃ ρ₀, N k₀ ρ₀ := by
    obtain ⟨c, hc | hc⟩ := hroot
    · by_cases hk : k₀ = a ∧ c = b
      · obtain ⟨hk1, -⟩ := hk
        refine ⟨θd.comp (spBlock K 1), hd1i, ?_, fun T hT' => ?_⟩
        · rw [hd1, hk1]
        · exact hT' TS1 (Or.inr (Or.inr (Or.inl ⟨hk1, rfl⟩)))
      · have h' : adj' k₀ c := (hadj' _ _).2 ⟨hc, hk⟩
        refine ⟨(θ k₀ c h').comp (blk K 0), comp_blk_injective (hθk _ _ h') 0, ?_,
          fun T hT' => ?_⟩
        · rw [← map_Bs, hθ0]
        · rw [← map_Ds]
          exact hT' _ (Or.inl ⟨c, h', rfl⟩)
    · have hk : ¬ (c = a ∧ k₀ = b) := fun h => hb0 h.2.symm
      have h' : adj' c k₀ := (hadj' _ _).2 ⟨hc, hk⟩
      refine ⟨(θ c k₀ h').comp (blk K 1), comp_blk_injective (hθk _ _ h') 1, ?_,
        fun T hT' => ?_⟩
      · rw [← map_Bs, hθ1]
      · rw [← map_Ds]
        exact hT' _ (Or.inr (Or.inl ⟨c, h', rfl⟩))
  obtain ⟨ρ₀, hρ₀⟩ := h₀
  have hf : ∀ k, k ≠ k₀ → ∀ ρp, N (par k) ρp → ∃ ρc, N k ρc ∧ E k ρp ρc := by
    intro k hk ρp ⟨hinj, hrange, htor⟩
    by_cases hkb : k = b
    ·
      subst hkb
      rw [hpar] at hrange htor
      obtain ⟨θ', hθ'k, hθ'1, hθ'0i, hθ'0, hθ'D⟩ := exists_adjust_sp_long hK hdk hd1i hd0i hinj
        (by rw [hrange, hd1])
        (htor TS1 (torGood_of_seen a TS1 (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
      refine ⟨θ'.comp (spBlock K 0), ⟨hθ'0i, hθ'0.trans hd0, fun T hT' => ?_⟩, ?_, ?_, ?_⟩
      · exact hθ'D.trans (hT' TS0 (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      · rw [hpar]
        intro h
        exact (((hadj' _ _).1 h).2 ⟨rfl, rfl⟩).elim
      · rw [hpar]
        intro h
        exact (hba (hadj'adj _ _ h)).elim
      · intro _
        exact ⟨θ', hθ'k, hθ'1, rfl⟩
    · rcases hT.adj_par k hk with h | h
      ·
        have h' : adj' (par k) k := (hadj' _ _).2 ⟨h, fun hh => hkb hh.2⟩
        obtain ⟨θ', hθ'k, hθ'0, hθ'1, hθ'D⟩ := exists_adjust_side hK 0 (hθk _ _ h') hinj
          (by rw [hrange, ← hθ0 _ _ h'])
          (htor _ (torGood_of_seen _ _ (Or.inl ⟨k, h', rfl⟩)))
        refine ⟨θ'.comp (blk K 1), ⟨comp_blk_injective hθ'k 1, ?_, fun T hT' => ?_⟩,
          fun _ => ⟨θ', hθ'0, rfl⟩, fun h'' => absurd h (hT.asymm _ _ (hadj'adj _ _ h'')),
          fun h'' => absurd h'' hkb⟩
        · rw [← map_Bs]
          exact hθ'1.trans (hθ1 _ _ h')
        · rw [← map_Ds]
          exact hθ'D.trans (hT' _ (Or.inr (Or.inl ⟨par k, h', rfl⟩)))
      ·
        have h' : adj' k (par k) := by
          refine (hadj' _ _).2 ⟨h, fun hh => ?_⟩
          obtain ⟨hk1, hpk⟩ := hh
          have h1 := hT.lt k hk
          have h2 := hT.lt b hb0
          rw [hpk, hk1] at h1
          rw [hpar] at h2
          omega
        obtain ⟨θ', hθ'k, hθ'1, hθ'0, hθ'D⟩ := exists_adjust_side hK 1 (hθk _ _ h') hinj
          (by rw [hrange, ← hθ1 _ _ h'])
          (htor _ (torGood_of_seen _ _ (Or.inr (Or.inl ⟨k, h', rfl⟩))))
        refine ⟨θ'.comp (blk K 0), ⟨comp_blk_injective hθ'k 0, ?_, fun T hT' => ?_⟩,
          fun h'' => absurd (hadj'adj _ _ h'') (hT.asymm _ _ h), fun _ => ⟨θ', rfl, hθ'1⟩,
          fun h'' => absurd h'' hkb⟩
        · rw [← map_Bs]
          exact hθ'0.trans (hθ0 _ _ h')
        · rw [← map_Ds]
          exact hθ'D.trans (hT' _ (Or.inl ⟨par k, h', rfl⟩))
  obtain ⟨ρ, -, hρN, hρE⟩ := exists_tree_family N E par dep k₀ hT.lt hf hρ₀
  refine ⟨ρ, fun k => ⟨(hρN k).1, (hρN k).2.1⟩, fun i j hij hne => ?_, ?_⟩
  · have h' : adj' i j := (hadj' _ _).2 ⟨hij, hne⟩
    rcases hT.par_of_adj i j hij with ⟨hj, hpj⟩ | ⟨hi, hpi⟩
    · have := (hρE j hj).1
      rw [hpj] at this
      exact this h'
    · have := (hρE i hi).2.1
      rw [hpi] at this
      exact this h'
  · have := (hρE b hb0).2.2 rfl
    rw [hpar] at this
    exact this

end Frame

end CFSG.ClassicalInvolution.WeakCT

module

public import CFSG.CGT.PushingUpLit.SolKR2.Pair

public section

namespace CFSG.CGT.PushingUpLit.SolKR2

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n.Tim78
open CFSG.RankThree.GF2n (conjSubgroup_mul conjSubgroup_eq_self_iff card_conjSubgroup
  exists_mul_of_mem_sup le_normalizer_of_comm mem_normalizer_sup)
open CFSG.RankThree.PartTwo (omegaOneSub omegaOneSub_le)

variable {G : Type} [Group G]

@[expose] def IsSig (B A : Subgroup G) : Prop :=
  ∃ e : G, A = conjSubgroup e (omegaOneSub B)

@[expose] def SigCover (B L : Subgroup G) : Prop :=
  ∀ l ∈ L, l ≠ 1 → ∃ Q : Subgroup G, IsSig B Q ∧ Q ≤ L ∧ l ∈ Q

variable [Finite G] {M B : Subgroup G}

namespace IsSig

omit [Finite G] in
theorem conj {A : Subgroup G} (hA : IsSig B A) (k : G) : IsSig B (conjSubgroup k A) := by
  obtain ⟨e, rfl⟩ := hA
  exact ⟨k * e, (conjSubgroup_mul k e _).symm⟩

section Facts

variable (h : R2 M B)
include h

omit [Finite G] in
theorem card {A : Subgroup G} (hA : IsSig B A) : Nat.card ↥A = 4 := by
  obtain ⟨e, rfl⟩ := hA
  exact Pair.card_conj_B0 h e

theorem inf_eq_bot {A A' : Subgroup G} (hA : IsSig B A) (hA' : IsSig B A') (hne : A ≠ A') :
    A ⊓ A' = ⊥ := by
  obtain ⟨e, rfl⟩ := hA
  obtain ⟨e', rfl⟩ := hA'
  by_contra hbot
  exact hne (conjSubgroup_eq_of_inf_ne_bot h.isTI_B0 hbot)

end Facts

end IsSig

theorem cover_of_five {L : Subgroup G} (hL : Nat.card ↥L = 16) {T : Finset (Subgroup G)}
    (hT : T.card = 5) (hle : ∀ Q ∈ T, Q ≤ L) (hcard : ∀ Q ∈ T, Nat.card ↥Q = 4)
    (hti : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Q ⊓ Q' = ⊥) :
    ∀ l ∈ L, l ≠ 1 → ∃ Q ∈ T, l ∈ Q := by
  classical
  have : Fintype G := Fintype.ofFinite G
  let S : Subgroup G → Finset G := fun Q => (Finset.univ.filter (· ∈ Q)).erase 1
  have hSc : ∀ Q : Subgroup G, Nat.card ↥Q = (Finset.univ.filter (· ∈ Q)).card := by
    intro Q
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h1mem : ∀ Q : Subgroup G, (1 : G) ∈ Finset.univ.filter (· ∈ Q) := fun Q => by
    simp
  have hS : ∀ Q : Subgroup G, (S Q).card = Nat.card ↥Q - 1 := by
    intro Q
    simp only [S]
    rw [Finset.card_erase_of_mem (h1mem Q), hSc]
  have hmemS : ∀ (Q : Subgroup G) (x : G), x ∈ S Q ↔ x ≠ 1 ∧ x ∈ Q := by
    intro Q x
    simp [S]
  have hdisj : ∀ Q ∈ T, ∀ Q' ∈ T, Q ≠ Q' → Disjoint (S Q) (S Q') := by
    intro Q hQ Q' hQ' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hmemS] at hx hx'
    have : x ∈ Q ⊓ Q' := ⟨hx.2, hx'.2⟩
    rw [hti Q hQ Q' hQ' hne, Subgroup.mem_bot] at this
    exact hx.1 this
  have hU : (T.biUnion S).card = 15 := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun Q hQ => by rw [hS, hcard Q hQ])]
    simp [hT]
  intro l hl hl1
  by_contra hcon
  push Not at hcon
  have hl' : l ∉ T.biUnion S := by
    intro hmem
    rw [Finset.mem_biUnion] at hmem
    obtain ⟨Q, hQ, hx⟩ := hmem
    rw [hmemS] at hx
    exact hcon Q hQ hx.2
  have hsub : insert l (T.biUnion S) ⊆ S L := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · rw [hmemS]
      exact ⟨hl1, hl⟩
    · rw [Finset.mem_biUnion] at hx
      obtain ⟨Q, hQ, hx⟩ := hx
      rw [hmemS] at hx ⊢
      exact ⟨hx.1, hle Q hQ hx.2⟩
  have h16 : (insert l (T.biUnion S)).card = 16 := by
    rw [Finset.card_insert_of_notMem hl', hU]
  have h1 := Finset.card_le_card hsub
  rw [h16, hS, hL] at h1
  omega

omit [Finite G] in
theorem card_sup_of_commute {X Y : Subgroup G} (hcomm : ∀ a ∈ X, ∀ b ∈ Y, a * b = b * a)
    (hXY : X ⊓ Y = ⊥) : Nat.card ↥(X ⊔ Y) = Nat.card ↥X * Nat.card ↥Y := by
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_comm fun x hx y hy => (hcomm y hy x hx).symm
  let f : ↥X × ↥Y → ↥(X ⊔ Y) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, v⟩ ⟨u', v'⟩ hh
      have h' : (u : G) * v = u' * v' := congrArg Subtype.val hh
      have hw : (u' : G)⁻¹ * u ∈ X ⊓ Y := by
        refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.inv_mem u'.2) u.2, ?_⟩
        rw [show (u' : G)⁻¹ * u = v' * (v : G)⁻¹ by
          calc (u' : G)⁻¹ * u = (u' : G)⁻¹ * (u * v) * (v : G)⁻¹ := by group
            _ = (u' : G)⁻¹ * (u' * v') * (v : G)⁻¹ := by rw [h']
            _ = v' * (v : G)⁻¹ := by group]
        exact Y.mul_mem v'.2 (Y.inv_mem v.2)
      rw [hXY, Subgroup.mem_bot, inv_mul_eq_one] at hw
      have hv : (v : G) = v' := by
        calc (v : G) = (u : G)⁻¹ * (u * v) := by group
          _ = (u : G)⁻¹ * (u' * v') := by rw [h']
          _ = v' := by rw [← hw]; group
      exact Prod.ext (Subtype.ext hw.symm) (Subtype.ext hv)
    · rintro ⟨n, hn⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hYX hn
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

section NoCert

variable (h : R2 M B)
include h

theorem ncpair_of_noncomm {g g' : G}
    (hcomm : ∀ a ∈ conjSubgroup g (omegaOneSub B), ∀ b ∈ conjSubgroup g' (omegaOneSub B),
      a * b = b * a)
    (hnc : ¬ ∀ a ∈ conjSubgroup g (omegaTwoSub B), ∀ b ∈ conjSubgroup g' (omegaTwoSub B),
      a * b = b * a) :
    NCPair (conjSubgroup g (omegaTwoSub B)) (conjSubgroup g' (omegaTwoSub B)) := by
  have hset : Setup210 (conjSubgroup g (omegaTwoSub B)) (conjSubgroup g' (omegaTwoSub B)) := by
    refine Pair.setup210_conj h g g' ?_
    intro hbot
    apply Pair.conj_B0_ne_bot h g
    rw [eq_bot_iff, ← hbot]
    refine le_inf (Pair.conj_B0_le_U h g) (fun x hx => ?_)
    obtain ⟨⟨f, hf⟩, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Pair.conj_B0_ne_bot h g')
    exact Pair.mem_normalizer_conj_U h hf (fun e => hf1 (Subtype.ext e)) (hcomm x hx f hf)
  exact ⟨hset, Pair.pow_four_conj h g, hnc⟩

end NoCert

section Cert

variable
  (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput) (h : R2 M B)
include hCen hU h

theorem sigCover_of_ncpair {e e' : G}
    (hcomm : ∀ a ∈ conjSubgroup e (omegaOneSub B), ∀ b ∈ conjSubgroup e' (omegaOneSub B),
      a * b = b * a)
    (hnc : ¬ ∀ a ∈ conjSubgroup e (omegaTwoSub B), ∀ b ∈ conjSubgroup e' (omegaTwoSub B),
      a * b = b * a) :
    SigCover B (conjSubgroup e (omegaOneSub B) ⊔ conjSubgroup e' (omegaOneSub B)) := by
  have P := ncpair_of_noncomm h hcomm hnc
  have hΩ := Pair.omegaOne_conj_U h e
  have hΩ' := Pair.omegaOne_conj_U h e'
  intro l hl hl1
  rw [← hΩ, ← hΩ'] at hl
  obtain ⟨a, ha, b, hb, rfl⟩ := P.exists_mul hCen hU hl
  have ha' : a ∈ conjSubgroup e (omegaOneSub B) := by rw [← hΩ]; exact ha
  have hb' : b ∈ conjSubgroup e' (omegaOneSub B) := by rw [← hΩ']; exact hb
  by_cases ha1 : a = 1
  · subst ha1
    exact ⟨conjSubgroup e' (omegaOneSub B), ⟨e', rfl⟩, le_sup_right, by rwa [one_mul]⟩
  · obtain ⟨y, hy, hya⟩ := Pair.exists_conj_mul hCen hU P (Pair.card_conj_U h e')
      (by rw [hΩ']; exact Pair.card_conj_B0 h e') ha ha1 hb
    refine ⟨conjSubgroup y (conjSubgroup e (omegaOneSub B)), IsSig.conj ⟨e, rfl⟩ y, ?_, ?_⟩
    · intro z hz
      rw [mem_conjSubgroup] at hz
      have hn : y⁻¹ * z * y ∈ omegaOneSub (conjSubgroup e (omegaTwoSub B)) ⊔
          omegaOneSub (conjSubgroup e' (omegaTwoSub B)) := by
        rw [hΩ, hΩ']
        exact Subgroup.mem_sup_left hz
      have := P.conj_mem_N hCen hU (Subgroup.mem_sup_right hy) hn
      rwa [show y * (y⁻¹ * z * y) * y⁻¹ = z by group, hΩ, hΩ'] at this
    · have hab : a * b = b * a :=
        P.comm_N hCen hU (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
      rw [mem_conjSubgroup]
      have : y⁻¹ * (a * b) * y = a := by
        rw [hab, ← hya]
        group
      rwa [this]

end Cert

section Torus

variable (h : R2 M B)
include h

theorem sigCover_of_torus {F F' F'' K : Subgroup G} (hF : IsSig B F) (hF' : IsSig B F')
    (hF'' : IsSig B F'') (hne : F ≠ F') (hcomm : ∀ a ∈ F, ∀ b ∈ F', a * b = b * a)
    (hle : F'' ≤ F ⊔ F') (h1 : F'' ≠ F) (h2 : F'' ≠ F')
    (hK3 : Nat.card ↥K = 3) (hKF : ∀ k ∈ K, ∀ a ∈ F, k * a = a * k)
    (hKF' : K ≤ Subgroup.normalizer (F' : Set G))
    (hfpf : ∀ k ∈ K, k ≠ 1 → ∀ b ∈ F', k * b * k⁻¹ = b → b = 1) :
    SigCover B (F ⊔ F') := by
  classical
  have hFF' : F ⊓ F' = ⊥ := IsSig.inf_eq_bot h hF hF' hne
  have hF''F : F'' ⊓ F = ⊥ := IsSig.inf_eq_bot h hF'' hF h1
  have hF''F' : F'' ⊓ F' = ⊥ := IsSig.inf_eq_bot h hF'' hF' h2
  have hL : Nat.card ↥(F ⊔ F') = 16 := by
    rw [card_sup_of_commute hcomm hFF', IsSig.card h hF, IsSig.card h hF']
  have hKFn : K ≤ Subgroup.normalizer (F : Set G) := le_normalizer_of_comm hKF
  have hKL : ∀ k ∈ K, conjSubgroup k (F ⊔ F') = F ⊔ F' := fun k hk =>
    conjSubgroup_eq_self_iff.mpr (mem_normalizer_sup (hKFn hk) (hKF' hk))
  have hconjle : ∀ k ∈ K, conjSubgroup k F'' ≤ F ⊔ F' := by
    intro k hk
    rw [← hKL k hk]
    exact Subgroup.map_mono hle
  have hstab : ∀ k ∈ K, conjSubgroup k F'' = F'' → k = 1 := by
    intro k hk hconj
    by_contra hk1
    have hF''ne : F'' ≠ ⊥ := by
      intro hb
      have := IsSig.card h hF''
      rw [hb, Subgroup.card_bot] at this
      omega
    obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF''ne
    have hw1' : w ≠ 1 := fun e => hw1 (Subtype.ext e)
    have hF'F : F' ≤ Subgroup.normalizer (F : Set G) :=
      le_normalizer_of_comm fun x hx y hy => (hcomm y hy x hx).symm
    obtain ⟨u, hu, u', hu', rfl⟩ := exists_mul_of_mem_sup hF'F (hle hw)
    have hu'1 : u' ≠ 1 := by
      intro e
      apply hw1'
      rw [e, mul_one] at hw ⊢
      have : u ∈ F'' ⊓ F := ⟨hw, hu⟩
      rwa [hF''F, Subgroup.mem_bot] at this
    have hkw : k * (u * u') * k⁻¹ ∈ F'' := by
      have : k * (u * u') * k⁻¹ ∈ conjSubgroup k F'' := by
        rw [mem_conjSubgroup, show k⁻¹ * (k * (u * u') * k⁻¹) * k = u * u' by group]
        exact hw
      rwa [hconj] at this
    have hku : k * u * k⁻¹ = u := by
      rw [hKF k hk u hu, mul_inv_cancel_right]
    have hku' : k * u' * k⁻¹ ∈ F' := (Subgroup.mem_normalizer_iff.mp (hKF' hk) u').mp hu'
    have hprod : (u * u')⁻¹ * (k * (u * u') * k⁻¹) = u'⁻¹ * (k * u' * k⁻¹) := by
      calc (u * u')⁻¹ * (k * (u * u') * k⁻¹)
          = (u * u')⁻¹ * ((k * u * k⁻¹) * (k * u' * k⁻¹)) := by group
        _ = (u * u')⁻¹ * (u * (k * u' * k⁻¹)) := by rw [hku]
        _ = u'⁻¹ * (k * u' * k⁻¹) := by group
    have hmem : u'⁻¹ * (k * u' * k⁻¹) ∈ F'' ⊓ F' := by
      refine ⟨?_, F'.mul_mem (F'.inv_mem hu') hku'⟩
      rw [← hprod]
      exact F''.mul_mem (F''.inv_mem hw) hkw
    rw [hF''F', Subgroup.mem_bot, inv_mul_eq_one] at hmem
    exact hu'1 (hfpf k hk hk1 u' hu' hmem.symm)
  have hinj : Function.Injective (fun k : ↥K => conjSubgroup (k : G) F'') := by
    intro k k' hkk
    have hkk' : conjSubgroup (k : G) F'' = conjSubgroup (k' : G) F'' := hkk
    have : conjSubgroup ((k' : G)⁻¹ * k) F'' = F'' := by
      rw [conjSubgroup_mul, hkk', ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have h1' := hstab _ (K.mul_mem (K.inv_mem k'.2) k.2) this
    exact Subtype.ext (inv_mul_eq_one.mp h1').symm
  have : Fintype ↥K := Fintype.ofFinite _
  let Tk : Finset (Subgroup G) := Finset.univ.image (fun k : ↥K => conjSubgroup (k : G) F'')
  have hTk : Tk.card = 3 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hK3]
  have hFTk : F ∉ Tk := by
    intro hmem
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
    apply h1
    have : F'' = conjSubgroup (k : G)⁻¹ F := by
      rw [← hk, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [this]
    exact conjSubgroup_eq_self_iff.mpr (hKFn (K.inv_mem k.2))
  have hF'Tk : F' ∉ Tk := by
    intro hmem
    obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hmem
    apply h2
    have : F'' = conjSubgroup (k : G)⁻¹ F' := by
      rw [← hk, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    rw [this]
    exact conjSubgroup_eq_self_iff.mpr (hKF' (K.inv_mem k.2))
  let T : Finset (Subgroup G) := insert F (insert F' Tk)
  have hFT : F ∉ insert F' Tk := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hne, hFTk⟩
  have hT : T.card = 5 := by
    simp only [T]
    rw [Finset.card_insert_of_notMem hFT, Finset.card_insert_of_notMem hF'Tk, hTk]
  have hmemT : ∀ Q ∈ T, IsSig B Q ∧ Q ≤ F ⊔ F' := by
    intro Q hQ
    simp only [T, Tk, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hQ
    rcases hQ with rfl | rfl | ⟨k, rfl⟩
    · exact ⟨hF, le_sup_left⟩
    · exact ⟨hF', le_sup_right⟩
    · exact ⟨IsSig.conj hF'' _, hconjle k k.2⟩
  intro l hl hl1
  obtain ⟨Q, hQ, hlQ⟩ := cover_of_five hL hT (fun Q hQ => (hmemT Q hQ).2)
    (fun Q hQ => IsSig.card h (hmemT Q hQ).1)
    (fun Q hQ Q' hQ' hne' => IsSig.inf_eq_bot h (hmemT Q hQ).1 (hmemT Q' hQ').1 hne') l hl hl1
  exact ⟨Q, (hmemT Q hQ).1, (hmemT Q hQ).2, hlQ⟩

@[expose] def HasTorus (E V : Subgroup G) : Prop :=
  ∃ K : Subgroup G, K ≤ E ⊔ V ∧ Nat.card ↥K = 3 ∧ K ≤ Subgroup.normalizer (E : Set G) ∧
    K ≤ Subgroup.normalizer (V : Set G) ∧
    ∀ k ∈ K, k ≠ 1 → ∀ w ∈ omegaOneSub V, k * w * k⁻¹ = w → w = 1

theorem sigCover_of_witness_of_torus {e e' w : G}
    (hne : conjSubgroup e (omegaOneSub B) ≠ conjSubgroup e' (omegaOneSub B))
    (hcomm1 : ∀ a ∈ conjSubgroup e (omegaTwoSub B), ∀ b ∈ conjSubgroup e' (omegaTwoSub B),
      a * b = b * a)
    (hw : conjSubgroup w (omegaTwoSub B) ≤
      Subgroup.centralizer (conjSubgroup e (omegaTwoSub B) : Set G))
    {F'' : Subgroup G} (hF'' : IsSig B F'')
    (hle : F'' ≤ conjSubgroup e (omegaOneSub B) ⊔ conjSubgroup e' (omegaOneSub B))
    (h1 : F'' ≠ conjSubgroup e (omegaOneSub B)) (h2 : F'' ≠ conjSubgroup e' (omegaOneSub B))
    (hT : HasTorus (conjSubgroup w (omegaTwoSub B)) (conjSubgroup e' (omegaTwoSub B))) :
    SigCover B (conjSubgroup e (omegaOneSub B) ⊔ conjSubgroup e' (omegaOneSub B)) := by
  obtain ⟨K, hKX, hK3, -, hKV, hfpf⟩ := hT
  have hcomm : ∀ a ∈ conjSubgroup e (omegaOneSub B), ∀ b ∈ conjSubgroup e' (omegaOneSub B),
      a * b = b * a := fun a ha b hb =>
    hcomm1 a (Pair.conj_B0_le_U h e ha) b (Pair.conj_B0_le_U h e' hb)
  have hXC : conjSubgroup w (omegaTwoSub B) ⊔ conjSubgroup e' (omegaTwoSub B) ≤
      Subgroup.centralizer (conjSubgroup e (omegaTwoSub B) : Set G) := by
    refine sup_le hw (fun x hx => ?_)
    rw [Subgroup.mem_centralizer_iff]
    exact fun u hu => hcomm1 u hu x hx
  have hKF : ∀ k ∈ K, ∀ a ∈ conjSubgroup e (omegaOneSub B), k * a = a * k := by
    intro k hk a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hXC (hKX hk))) a
      (Pair.conj_B0_le_U h e ha)).symm
  have hKF' : K ≤ Subgroup.normalizer (conjSubgroup e' (omegaOneSub B) : Set G) := by
    intro k hk
    rw [← conjSubgroup_eq_self_iff]
    have hk' := conjSubgroup_eq_self_iff.mpr (hKV hk)
    rw [← Pair.omegaOne_conj_U h e', ← omegaOneSub_conj (Pair.comm_conj_U h e'), hk']
  refine sigCover_of_torus h ⟨e, rfl⟩ ⟨e', rfl⟩ hF'' hne hcomm hle h1 h2 hK3 hKF hKF' ?_
  intro k hk hk1 b hb hkb
  exact hfpf k hk hk1 b (by rw [Pair.omegaOne_conj_U h e']; exact hb) hkb

theorem sigCover_of_witness_of_lemma
    (htorus : ∀ E V : Subgroup G, NCPair E V → Nat.card ↥E = 16 →
      Nat.card ↥(omegaOneSub E) = 4 → HasTorus E V)
    (hγ : ∀ f e e' : G, conjSubgroup e (omegaOneSub B) ≤
        Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) →
      conjSubgroup e' (omegaOneSub B) ≤
        Subgroup.centralizer (conjSubgroup f (omegaTwoSub B) : Set G) →
      ∀ a ∈ conjSubgroup e (omegaOneSub B), ∀ b ∈ conjSubgroup e' (omegaOneSub B),
        a * b = b * a)
    {e e' w : G} (hne : conjSubgroup e (omegaOneSub B) ≠ conjSubgroup e' (omegaOneSub B))
    (hcomm1 : ∀ a ∈ conjSubgroup e (omegaTwoSub B), ∀ b ∈ conjSubgroup e' (omegaTwoSub B),
      a * b = b * a)
    (hw : conjSubgroup w (omegaTwoSub B) ≤
      Subgroup.centralizer (conjSubgroup e (omegaTwoSub B) : Set G))
    (hwnc : ¬ ∀ a ∈ conjSubgroup w (omegaTwoSub B), ∀ b ∈ conjSubgroup e' (omegaTwoSub B),
      a * b = b * a)
    {F'' : Subgroup G} (hF'' : IsSig B F'')
    (hle : F'' ≤ conjSubgroup e (omegaOneSub B) ⊔ conjSubgroup e' (omegaOneSub B))
    (h1 : F'' ≠ conjSubgroup e (omegaOneSub B)) (h2 : F'' ≠ conjSubgroup e' (omegaOneSub B)) :
    SigCover B (conjSubgroup e (omegaOneSub B) ⊔ conjSubgroup e' (omegaOneSub B)) := by
  have hE0 : conjSubgroup w (omegaOneSub B) ≤
      Subgroup.centralizer (conjSubgroup e (omegaTwoSub B) : Set G) :=
    (Pair.conj_B0_le_U h w).trans hw
  have hF'C : conjSubgroup e' (omegaOneSub B) ≤
      Subgroup.centralizer (conjSubgroup e (omegaTwoSub B) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => hcomm1 u hu x (Pair.conj_B0_le_U h e' hx)
  have P := ncpair_of_noncomm h (hγ e w e' hE0 hF'C) hwnc
  have hT := htorus _ _ P (Pair.card_conj_U h w)
    (by rw [Pair.omegaOne_conj_U h w]; exact Pair.card_conj_B0 h w)
  exact sigCover_of_witness_of_torus h hne hcomm1 hw hF'' hle h1 h2 hT

end Torus

end CFSG.CGT.PushingUpLit.SolKR2

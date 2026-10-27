module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Sp62Transport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62EscapeModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameScan

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two
open CFSG.PreuniquenessRankFour.Helpers

theorem eq_top_of_T0_C_le
    {Y₀ : Subgroup H6} (hT : T0 ≤ Y₀) (hC : Subgroup.centralizer ({elt cW0} : Set H6) ≤ Y₀) :
    Y₀ = ⊤ := by
  obtain ⟨hc1, hc2⟩ := cIo1_cTau12_mem_centralizer
  have hX : ∀ c ∈ gensX, elt c ∈ Y₀ := by
    intro c hc
    simp only [gensX, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (hc | hc) | hc | hc
    · exact hT (elt_mem_Hgen (c := c) hc)
    · exact hC (Alt0_le_centralizer (elt_mem_Hgen (c := c) hc))
    · rw [hc]; exact hC hc1
    · rw [hc]; exact hC hc2
  obtain ⟨hτ, hι, hgD⟩ := mem_of_gensX hX
  have hW : W0 ≤ Y₀ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, hc, rfl⟩
    have hWD : gensWD = gensT ++ [cTau, cIo, cGD] := rfl
    rw [hWD, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hT (elt_mem_Hgen (c := c) hc)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      exacts [hτ, hι, hgD]
  exact eq_top_of_mem_not_mem hW (hC (Alt0_le_centralizer elt_cAlt0_mem_Alt0))
    elt_cAlt0_not_mem_W0

structure Sp62FrameDatum {Y : Type} [Group Y] [Finite Y] (T J : Subgroup Y) (b : Y) : Prop where
  le : J ≤ T
  elem : IsElemAbelian 3 J
  card : Nat.card J = 3 ^ 3
  uniq : ∀ J' : Subgroup Y, J' ≤ T → IsElemAbelian 3 J' → Nat.card J' = 3 ^ 3 → J' = J
  cent : T ⊓ Subgroup.centralizer (J : Set Y) ≤ J
  dvd : 48 ∣ (Subgroup.centralizer (J : Set Y)).relIndex (Subgroup.normalizer (J : Set Y))
  mem : b ∈ J
  order : orderOf b = 3
  idx : (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup Y) : Set Y)).relIndex
    (Subgroup.normalizer (J : Set Y)) = 3
  gen : ∀ Y₀ : Subgroup Y, T ≤ Y₀ → Y₀ ≠ ⊤ → ¬ Subgroup.centralizer ({b} : Set Y) ≤ Y₀

theorem Sp62FrameDatum.of_mulEquiv {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X ≃* Y) {T J : Subgroup X} {b : X} (h : Sp62FrameDatum T J b) :
    Sp62FrameDatum (T.map f.toMonoidHom) (J.map f.toMonoidHom) (f b) := by
  have hinj : Function.Injective f.toMonoidHom := f.injective
  have hmap : ∀ A : Subgroup Y, (A.map f.symm.toMonoidHom).map f.toMonoidHom = A := fun A => by
    rw [Subgroup.map_map]
    ext x
    simp
  have hmem : ∀ (A : Subgroup X) (x : X), f x ∈ A.map f.toMonoidHom ↔ x ∈ A := fun A x =>
    Subgroup.mem_map_iff_mem hinj
  refine ⟨Subgroup.map_mono h.le, elementary_abelian_map 3 h.elem f.toMonoidHom,
    (Subgroup.card_map_of_injective hinj).trans h.card, ?_, ?_, ?_, Subgroup.mem_map_of_mem _ h.mem,
    (MulEquiv.orderOf_eq f b).trans h.order, ?_, ?_⟩
  · intro J'' hJT hJe hJc
    have hle : J''.map f.symm.toMonoidHom ≤ T := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht, hty⟩ := hJT hy
      have hfy : f.symm.toMonoidHom y = t := by rw [← hty]; simp
      rw [hfy]
      exact ht
    have := h.uniq _ hle (elementary_abelian_map 3 hJe f.symm.toMonoidHom)
      (by rw [Subgroup.card_map_of_injective f.symm.injective, hJc])
    rw [← hmap J'', this]
  · intro x hx
    obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨x, rfl⟩ := f.surjective x
    have hxC' : x ∈ Subgroup.centralizer (J : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      apply f.injective
      have := Subgroup.mem_centralizer_iff.1 hxC (f j) (Subgroup.mem_map_of_mem _ hj)
      simpa using this
    exact (hmem J x).2 (h.cent (Subgroup.mem_inf.2 ⟨(hmem T x).1 hxT, hxC'⟩))
  · rw [← sp62_map_centralizer, ← sp62_map_normalizer,
      Subgroup.relIndex_map_map_of_injective _ _ hinj]
    exact h.dvd
  · have hz : Subgroup.zpowers (f b) = (Subgroup.zpowers b).map f.toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      rfl
    rw [hz, ← sp62_map_normalizer, ← sp62_map_normalizer,
      Subgroup.relIndex_map_map_of_injective _ _ hinj]
    exact h.idx
  · intro Y₀ hTY hne hC
    set Y₁ := Y₀.map f.symm.toMonoidHom with hY₁
    refine h.gen Y₁ ?_ ?_ ?_
    · rintro t ht
      have : f t ∈ Y₀ := hTY (Subgroup.mem_map_of_mem _ ht)
      exact ⟨f t, this, by simp⟩
    · intro htop
      apply hne
      rw [← hmap Y₀, ← hY₁, htop, Subgroup.map_top_of_surjective _ f.surjective]
    · intro x hx
      have hfx : f x ∈ Subgroup.centralizer ({f b} : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have := Subgroup.mem_centralizer_iff.1 hx b rfl
        rw [← map_mul, ← map_mul, this]
      refine ⟨f x, hC hfx, by simp⟩

theorem sp62FrameDatum_H6 :
    Sp62FrameDatum T0 B0 (elt cW0) where
  le := B0_le_T0
  elem := B0_elemAbelian
  card := card_B0
  uniq := fun J' hJ' hJe hJc => eq_B0_of_elemAbelian hJ' hJe hJc
  cent := fun x hx => centralizer_B0_le (Subgroup.mem_inf.1 hx).2
  dvd := by
    have hB : B0 ≤ Subgroup.centralizer (B0 : Set H6) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      exact congrArg Subtype.val (B0_elemAbelian.1.is_comm.comm ⟨b', hb'⟩ ⟨b, hb⟩)
    have h1 := Subgroup.relIndex_mul_card (H := Subgroup.centralizer (B0 : Set H6)) (K := N0)
    have h2 : Subgroup.centralizer (B0 : Set H6) ⊓ N0 = B0 := by
      refine le_antisymm ?_ (le_inf hB B0_le_N0)
      intro x hx
      exact centralizer_N0_le (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).2,
        (Subgroup.mem_inf.1 hx).1⟩)
    rw [h2, card_B0, card_N0] at h1
    rw [normalizer_B0_eq]
    have : (Subgroup.centralizer (B0 : Set H6)).relIndex N0 = 48 := by
      have h3 : (Subgroup.centralizer (B0 : Set H6)).relIndex N0 * 27 = 48 * 27 := by
        rw [show 3 ^ 3 = 27 by norm_num] at h1
        rw [h1]
      exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3
    rw [this]
  mem := w0_mem_B0
  order := orderOf_w0
  idx := by
    rw [normalizer_B0_eq]
    exact relIndex_normalizer_zpowers_N0
  gen := fun Y₀ hT hne hC => hne (eq_top_of_T0_C_le hT hC)

theorem kFactSp62Frame_holds :
    KFactSp62Frame := by
  intro Y _ _ K d hd hKn ⟨e⟩ hC T
  obtain ⟨Ψ, hT⟩ := exists_equiv_H6_sylow K d hd e hC T
  have h := sp62FrameDatum_H6.of_mulEquiv Ψ.symm
  have hT' : T0.map Ψ.symm.toMonoidHom = (T : Subgroup Y) := by
    rw [← hT, Subgroup.map_map]
    ext x
    simp
  rw [hT'] at h
  exact ⟨_, _, h.le, h.elem, h.card, h.uniq, h.cent, h.dvd, h.mem, h.order, h.idx, h.gen⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

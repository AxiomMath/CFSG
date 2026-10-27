module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDPresentMul
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Model

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.SDPresent

open Subgroup Equiv CFSG.ComponentClassification.HSFLit

private abbrev I : Type := Fin 8 × Fin 2 × Fin 2

private def iA : I := (⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩)

private def iB : I := (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩)

private def iC : I := (⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩)

private def step (p q : I) : I :=
  (⟨(p.1.val + 3 ^ p.2.1.val * 5 ^ p.2.2.val * q.1.val) % 8, Nat.mod_lt _ (by decide)⟩,
   ⟨(p.2.1.val + q.2.1.val) % 2, Nat.mod_lt _ (by decide)⟩,
   ⟨(p.2.2.val + q.2.2.val) % 2, Nat.mod_lt _ (by decide)⟩)

private lemma card_I : Nat.card I = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def nfIdx {Γ : Type*} [Group Γ] (a b c : Γ) (p : I) :
    closure ({a, b, c} : Set Γ) :=
  ⟨nf a b c p.1.val p.2.1.val p.2.2.val,
    nf_mem_closure (a := a) (b := b) (c := c) p.1.val p.2.1.val p.2.2.val⟩

private lemma nf_step {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c) (p q : I) :
    nf a b c p.1.val p.2.1.val p.2.2.val * nf a b c q.1.val q.2.1.val q.2.2.val =
      nf a b c (step p q).1.val (step p q).2.1.val (step p q).2.2.val := by
  rw [nf_mul h, nf_mod h]
  simp only [step, Fin.val_mk]

private lemma nfIdx_mul {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c) (p q : I) :
    nfIdx a b c p * nfIdx a b c q = nfIdx a b c (step p q) := by
  apply Subtype.ext
  exact nf_step h p q

private lemma nfIdx_surjective {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c) :
    Function.Surjective (nfIdx a b c) := by
  intro g
  obtain ⟨i, j, e, hi, hj, he, hg⟩ :=
    exists_nf_of_mem_closure (a := a) (b := b) (c := c) h g.2
  exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨e, he⟩), Subtype.ext hg.symm⟩

private lemma nfIdx_iA {Γ : Type*} [Group Γ] (a b c : Γ) :
    nfIdx a b c iA = genA a b c := by
  apply Subtype.ext
  simp [nfIdx, genA, nf, iA]

private lemma nfIdx_iB {Γ : Type*} [Group Γ] (a b c : Γ) :
    nfIdx a b c iB = genB a b c := by
  apply Subtype.ext
  simp [nfIdx, genB, nf, iB]

private lemma nfIdx_iC {Γ : Type*} [Group Γ] (a b c : Γ) :
    nfIdx a b c iC = genC a b c := by
  apply Subtype.ext
  simp [nfIdx, genC, nf, iC]

private noncomputable def nfEquiv {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c)
    (hc : Nat.card (closure ({a, b, c} : Set Γ)) = 32) :
    I ≃ closure ({a, b, c} : Set Γ) :=
  Equiv.ofBijective (nfIdx a b c)
    ((nfIdx_surjective h).bijective_of_nat_card_le (by simp [card_I, hc]))

private lemma nfEquiv_iA {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c)
    (hc : Nat.card (closure ({a, b, c} : Set Γ)) = 32) :
    nfEquiv h hc iA = genA a b c := by
  simp only [nfEquiv, Equiv.ofBijective_apply]
  exact nfIdx_iA a b c

private lemma nfEquiv_iB {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c)
    (hc : Nat.card (closure ({a, b, c} : Set Γ)) = 32) :
    nfEquiv h hc iB = genB a b c := by
  simp only [nfEquiv, Equiv.ofBijective_apply]
  exact nfIdx_iB a b c

private lemma nfEquiv_iC {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c)
    (hc : Nat.card (closure ({a, b, c} : Set Γ)) = 32) :
    nfEquiv h hc iC = genC a b c := by
  simp only [nfEquiv, Equiv.ofBijective_apply]
  exact nfIdx_iC a b c

theorem exists_mulEquiv {Γ Γ' : Type*} [Group Γ] [Group Γ'] {a b c : Γ} {a' b' c' : Γ'}
    (h : Rel a b c) (h' : Rel a' b' c')
    (hc : Nat.card (closure ({a, b, c} : Set Γ)) = 32)
    (hc' : Nat.card (closure ({a', b', c'} : Set Γ')) = 32) :
    ∃ e : closure ({a, b, c} : Set Γ) ≃* closure ({a', b', c'} : Set Γ'),
      e (genA a b c) = genA a' b' c' ∧ e (genB a b c) = genB a' b' c' ∧
        e (genC a b c) = genC a' b' c' := by
  let F : closure ({a, b, c} : Set Γ) →* closure ({a', b', c'} : Set Γ') :=
    MonoidHom.mk' (fun g => nfEquiv h' hc' ((nfEquiv h hc).symm g)) (by
      intro g g'
      have h1 : g * g' =
          nfEquiv h hc (step ((nfEquiv h hc).symm g) ((nfEquiv h hc).symm g')) := by
        conv_lhs =>
          rw [← Equiv.apply_symm_apply (nfEquiv h hc) g,
            ← Equiv.apply_symm_apply (nfEquiv h hc) g']
        change nfIdx a b c ((nfEquiv h hc).symm g) *
            nfIdx a b c ((nfEquiv h hc).symm g') =
          nfIdx a b c (step ((nfEquiv h hc).symm g) ((nfEquiv h hc).symm g'))
        exact nfIdx_mul h _ _
      rw [h1, Equiv.symm_apply_apply]
      change nfIdx a' b' c' (step ((nfEquiv h hc).symm g) ((nfEquiv h hc).symm g')) =
        nfIdx a' b' c' ((nfEquiv h hc).symm g) * nfIdx a' b' c' ((nfEquiv h hc).symm g')
      rw [← nfIdx_mul h' _ _])
  have hbij : Function.Bijective
      (fun g => nfEquiv h' hc' ((nfEquiv h hc).symm g)) :=
    (nfEquiv h' hc').bijective.comp (nfEquiv h hc).symm.bijective
  refine ⟨MulEquiv.ofBijective F hbij, ?_, ?_, ?_⟩
  · change nfEquiv h' hc' ((nfEquiv h hc).symm (genA a b c)) = genA a' b' c'
    rw [← nfEquiv_iA h hc, Equiv.symm_apply_apply, nfEquiv_iA h' hc']
  · change nfEquiv h' hc' ((nfEquiv h hc).symm (genB a b c)) = genB a' b' c'
    rw [← nfEquiv_iB h hc, Equiv.symm_apply_apply, nfEquiv_iB h' hc']
  · change nfEquiv h' hc' ((nfEquiv h hc).symm (genC a b c)) = genC a' b' c'
    rw [← nfEquiv_iC h hc, Equiv.symm_apply_apply, nfEquiv_iC h' hc']

private lemma nfIdx_surj_H8' :
    ∀ p : (ZMod 8)ˣ × ZMod 8,
      ∃ q : I, aff8 p.1 p.2 = nf (aff8 u5 1) y8 k8 q.1.val q.2.1.val q.2.2.val := by
  decide +kernel

theorem rel_H8 : Rel (aff8 u5 1) y8 k8 where
  a_pow := by decide
  b_sq := by decide
  c_sq := by decide
  b_a := by decide
  c_a := by decide
  c_b := by decide

theorem closure_H8_eq :
    closure ({aff8 u5 1, y8, k8} : Set (Perm (ZMod 8))) = H8 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact aff8_mem_H8 u5 1
    · exact aff8_mem_H8 (-1) 0
    · exact aff8_mem_H8 u5 0
  · rintro g hg
    obtain ⟨u, b, rfl⟩ := hg
    obtain ⟨q, hq⟩ := nfIdx_surj_H8' (u, b)
    rw [hq]
    exact nf_mem_closure (a := aff8 u5 1) (b := y8) (c := k8) q.1.val q.2.1.val q.2.2.val

private noncomputable def aff8Equiv : ((ZMod 8)ˣ × ZMod 8) ≃ H8 :=
  Equiv.ofBijective (fun p => (⟨aff8 p.1 p.2, aff8_mem_H8 p.1 p.2⟩ : H8)) (by
    refine ⟨?_, ?_⟩
    · rintro ⟨u, b⟩ ⟨u', b'⟩ h
      obtain ⟨h1, h2⟩ := aff8_injective (congrArg (fun x : H8 => (x : Perm (ZMod 8))) h)
      exact Prod.ext h1 h2
    · rintro ⟨g, hg⟩
      obtain ⟨u, b, rfl⟩ := hg
      exact ⟨(u, b), Subtype.ext rfl⟩)

theorem card_H8 : Nat.card H8 = 32 := by
  rw [← Nat.card_congr aff8Equiv, Nat.card_prod, card_units_zmod_eight,
    Nat.card_eq_fintype_card, ZMod.card]

theorem exists_mulEquiv_H8 {Γ : Type*} [Group Γ] {a b c : Γ} (h : Rel a b c)
    (hc : Nat.card (closure ({a, b, c} : Set Γ)) = 32) :
    ∃ e : closure ({a, b, c} : Set Γ) ≃* ↥H8,
      (e (genA a b c) : Perm (ZMod 8)) = aff8 u5 1 ∧ (e (genB a b c) : Perm (ZMod 8)) = y8 ∧
        (e (genC a b c) : Perm (ZMod 8)) = k8 := by
  have hc' : Nat.card (closure ({aff8 u5 1, y8, k8} : Set (Perm (ZMod 8)))) = 32 := by
    rw [closure_H8_eq, card_H8]
  obtain ⟨e, hA, hB, hC⟩ :=
    exists_mulEquiv (Γ := Γ) (Γ' := Perm (ZMod 8)) (a := a) (b := b) (c := c)
      (a' := aff8 u5 1) (b' := y8) (c' := k8) h rel_H8 hc hc'
  refine ⟨e.trans (MulEquiv.subgroupCongr closure_H8_eq), ?_, ?_, ?_⟩
  · rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, hA]
    rfl
  · rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, hB]
    rfl
  · rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, hC]
    rfl

end CFSG.OddStandard.SmallF3.L33.KD.SDPresent

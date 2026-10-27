module

public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreRigid
public import CFSG.HardMathSupport.RichardWeiss.Proving.AltDegreeBound

public section

namespace CFSG.HardMathSupport.RichardWeiss.Coordinator

open scoped commutatorElement
open CFSG.AGLEmbedding CFSG.Open CFSG.HardMathSupport.Cooperstein.Proving
  CFSG.HardMathSupport.RichardWeiss.Proving

theorem exists_noncomm_quotient_center {X : Type*} [Group X] (hq : CFSG.Open.IsQuasisimple X) :
    ∃ a b : X ⧸ Subgroup.center X, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hperf, hsimple⟩ := hq
  have : IsSimpleGroup (X ⧸ Subgroup.center X) := hsimple
  have hle : commutator X ≤ Subgroup.center X := by
    refine Subgroup.commutator_le.2 fun x _ y _ => ?_
    rw [← QuotientGroup.eq_one_iff, show (QuotientGroup.mk ⁅x, y⁆ : X ⧸ Subgroup.center X) =
      ⁅QuotientGroup.mk x, QuotientGroup.mk y⁆ from map_commutatorElement
        (QuotientGroup.mk' (Subgroup.center X)) x y]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hcon _ _)
  obtain ⟨a, ha⟩ := exists_ne (1 : X ⧸ Subgroup.center X)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  exact ha ((QuotientGroup.eq_one_iff x).2 (hle (hperf ▸ Subgroup.mem_top x)))

theorem false_of_quasisimple_alt_le_three {X : Type*} [Group X] (hq : CFSG.Open.IsQuasisimple X) {m : ℕ}
    (hm : m ≤ 3) (e : X ≃* alternatingGroup (Fin m)) : False := by
  have hc : IsMulCommutative (alternatingGroup (Fin m)) := by
    apply alternatingGroup.isMulCommutative_iff_card_le_three.mpr
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hm
  obtain ⟨a, b, hab⟩ := exists_noncomm_quotient_center hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have hxy : x * y = y * x := by
    apply e.injective
    rw [map_mul, map_mul]
    exact hc.is_comm.comm _ _
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

theorem nonempty_quotient_center_equiv_alt {X : Type*} [Group X] {m : ℕ} (hm : 4 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) :
    Nonempty (X ⧸ Subgroup.center X ≃* alternatingGroup (Fin m)) := by
  have hc : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using hm)
  have hmap : (Subgroup.center X).map e.toMonoidHom = Subgroup.center (alternatingGroup (Fin m)) :=
    Subgroup.map_center_eq e
  exact ⟨(QuotientGroup.congr _ _ e hmap).trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)⟩

theorem five_le_of_quasisimple_alt {X : Type*} [Group X] (hq : CFSG.Open.IsQuasisimple X) {m : ℕ}
    (e : X ≃* alternatingGroup (Fin m)) : 5 ≤ m := by
  by_contra hlt
  rcases Nat.lt_or_ge m 4 with h | h
  · exact false_of_quasisimple_alt_le_three hq (by omega) e
  · obtain ⟨e'⟩ := nonempty_quotient_center_equiv_alt h e
    have hs : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
    exact hlt (five_le_of_isSimpleGroup_alt (S := X ⧸ Subgroup.center X) (exists_noncomm_quotient_center hq) e')

theorem card_quotient_pCore_le {Γ : Type*} [Group Γ] [Finite Γ] {J Lb : Subgroup Γ}
    (h : J ≤ Lb) : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) ≤ Nat.card ↥Lb :=
  (Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective).trans
    (Subgroup.card_le_of_le h)

theorem barM_mono {G : Type} [Group G] {M X Y : Subgroup G} (h : X ≤ Y) :
    barM M X ≤ barM M Y := by
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y, h hy, rfl⟩

theorem card_alternatingGroup_fin {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (alternatingGroup (Fin m)) = m.factorial / 2 := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_perm_prod (r s : ℕ) :
    Nat.card (Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) = r.factorial * s.factorial := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_perm, Fintype.card_fin, Fintype.card_fin]

section Degrees

variable {G : Type} [Group G] [Finite G]

theorem degree_cases {M S L : Subgroup G} (hL : IsWeakSBlock M S L)
    (h678 : NineThreeSix M S L ∨ NineThreeSeven M S L ∨ NineThreeEight M S L) :
    (∃ m : ℕ, 10 ≤ m ∧
      Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin m))) ∨
    (Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
        CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* Equiv.Perm (Fin 3))) ∨
    (Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 8)) ∧
      ∃ f : ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) →* Equiv.Perm (Fin 6),
        Function.Surjective f) := by
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  have hJL : barM M (Subgroup.normalizer (S : Set G) ⊓ L) ≤ barM M L :=
    barM_mono inf_le_right
  rcases h678 with h6 | h7 | h8
  ·
    obtain ⟨-, n, ⟨e⟩, ⟨eQ⟩⟩ := h6
    have hsimple : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hq.2
    have h5 : 5 ≤ 2 * n :=
      five_le_of_isSimpleGroup_alt (exists_noncomm_quotient_center hq) e
    rcases Nat.lt_or_ge n 5 with hn | hn
    · have hn' : n = 3 ∨ n = 4 := by omega
      rcases hn' with rfl | rfl
      · exact Or.inr (Or.inl ⟨⟨e⟩, ⟨eQ⟩⟩)
      · exact (not_nonempty_quotient_perm_four ⟨eQ⟩).elim
    · exact Or.inl ⟨2 * n, by omega, ⟨e⟩⟩
  ·
    obtain ⟨-, n, ⟨e⟩, ⟨eQ⟩⟩ := h7
    have h5 : 5 ≤ 4 * n := five_le_of_quasisimple_alt hq e
    have hn2 : n ≠ 2 := by
      rintro rfl
      exact not_nonempty_quotient_iso_of_pCore_ne_bot pCore_two_perm_two_ne_bot ⟨eQ⟩
    exact Or.inl ⟨4 * n, by omega, nonempty_quotient_center_equiv_alt (by omega) e⟩
  ·
    simp only [NineThreeEight] at h8
    obtain ⟨-, N, r, hNe, hr2, h0, h2, h4, ⟨e⟩, φ, -, -⟩ := h8
    have h5 : 5 ≤ N := five_le_of_quasisimple_alt hq e
    have hcard : r.factorial * (N - 2 * r).factorial ≤ N.factorial / 2 := by
      rw [← card_perm_prod]
      calc Nat.card (Equiv.Perm (Fin r) × Equiv.Perm (Fin (N - 2 * r)))
          = Nat.card (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ⧸
              CFSG.pCore 2 ↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L))) :=
            (Nat.card_congr φ.toEquiv).symm
        _ ≤ Nat.card ↥(barM M L) := card_quotient_pCore_le hJL
        _ = Nat.card (alternatingGroup (Fin N)) := Nat.card_congr e.toEquiv
        _ = N.factorial / 2 := card_alternatingGroup_fin (by omega)
    obtain ⟨k, hk⟩ := hNe
    rcases Nat.lt_or_ge N 10 with hN | hN
    · have hN' : N = 6 ∨ N = 8 := by omega
      rcases hN' with rfl | rfl
      · have hr : r = 0 := by omega
        subst hr
        norm_num [Nat.factorial] at hcard
      · have hr : r = 0 ∨ r = 1 := by omega
        rcases hr with rfl | rfl
        · norm_num [Nat.factorial] at hcard
        · refine Or.inr (Or.inr ⟨⟨e⟩, (MonoidHom.snd _ _).comp
            (φ.toMonoidHom.comp (QuotientGroup.mk' _)), ?_⟩)
          intro y
          obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (φ.symm (1, y))
          refine ⟨x, ?_⟩
          simp [hx]
    · exact Or.inl ⟨N, hN, nonempty_quotient_center_equiv_alt (by omega) e⟩

end Degrees

end CFSG.HardMathSupport.RichardWeiss.Coordinator

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCComp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.GroupTheory.WeirSylow
open scoped commutatorElement

section Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem torus_mono {l l' : List (V × V)} (h : ∀ q ∈ l', q ∈ l) : torus Q l' ≤ torus Q l :=
  Subgroup.closure_mono (fun g ⟨q, hq, hg⟩ => ⟨q, h q hq, hg⟩)

theorem polar_Wspan_Wspan {l₁ l₂ : List (V × V)} (h : ∀ p ∈ l₁, ∀ q ∈ l₂, PairPerp Q p q) {a b : V}
    (ha : a ∈ Wspan l₁) (hb : b ∈ Wspan l₂) : polar Q a b = 0 := by
  induction l₁ generalizing a with
  | nil =>
    rw [Wspan_nil, Submodule.mem_bot] at ha
    rw [ha, polar_zero_left]
  | cons p l₁ ih =>
    obtain ⟨u, hu, a', ha', rfl⟩ := Submodule.mem_sup.1 ha
    rw [polar_add_left, polar_planeSpan_Wspan (fun q hq => h p List.mem_cons_self q hq) hu hb,
      ih (fun p' hp' q hq => h p' (List.mem_cons_of_mem _ hp') q hq) ha', add_zero]

theorem isPlusType_of_Wspan_eq_top {l : List (V × V)} (h : Wspan l = ⊤)
    (hp : IsPlusType (Q.comp (Wspan l).subtype)) : IsPlusType Q := by
  refine (isPlusType_congr (Q := Q.comp (Wspan l).subtype) (Q' := Q) ?_).1 hp
  exact { toLinearEquiv := LinearEquiv.ofTop (Wspan l) h, map_app' := fun m => rfl }

end Aux

section Assemble

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem isPlusType_of_no_minusPair {X : Submodule (ZMod 2) V} (hX2 : finrank (ZMod 2) X = 2)
    (hno : ¬ ∃ a b : V, a ∈ X ∧ b ∈ X ∧ MinusPair Q a b) : IsPlusType (Q.comp X.subtype) := by
  by_cases hex : ∃ x ∈ X, x ≠ 0 ∧ Q x = 0
  · obtain ⟨x, hx, hx0, hQx⟩ := hex
    refine ⟨Submodule.span (ZMod 2) {(⟨x, hx⟩ : X)}, ?_, ?_⟩
    · rw [finrank_span_singleton (fun h => hx0 (congrArg Subtype.val h)), hX2]
    · intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      change Q ((c • (⟨x, hx⟩ : X) : X) : V) = 0
      rw [Submodule.coe_smul, QuadraticMap.map_smul, hQx]
      simp
  · exfalso
    push Not at hex
    have hQ1 : ∀ x ∈ X, x ≠ 0 → Q x = 1 := fun x hx hx0 =>
      (zmod_two_cases (Q x)).resolve_left (hex x hx hx0)
    have hXne : X ≠ ⊥ := by
      rintro rfl
      simp at hX2
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    have hnle : ¬ X ≤ Submodule.span (ZMod 2) {a} := by
      intro hle
      have := Submodule.finrank_mono hle
      rw [finrank_span_singleton ha0, hX2] at this
      omega
    obtain ⟨b, hb, hba⟩ := SetLike.not_le_iff_exists.1 hnle
    have hb0 : b ≠ 0 := fun h => hba (by rw [h]; exact Submodule.zero_mem _)
    have hbne : b ≠ a := fun h => hba (by rw [h]; exact Submodule.mem_span_singleton_self a)
    have hab0 : a + b ≠ 0 := by
      intro h
      apply hbne
      have := vec_add_self a
      linear_combination (norm := module) h - this
    apply hno
    refine ⟨a, b, ha, hb, ⟨hQ1 a ha ha0, hQ1 b hb hb0, ?_⟩⟩
    rw [polar_eq, hQ1 _ (X.add_mem ha hb) hab0, hQ1 a ha ha0, hQ1 b hb hb0]
    decide

theorem omCore_abstract (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {n : ℕ}
    (hdim : finrank (ZMod 2) V = 2 * n) (hn : 5 ≤ n ∨ (n = 4 ∧ ¬ IsPlusType Q))
    {E : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hEΩ : E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hE : IsElemAbelian 3 E)
    (hmax : ∀ E' : Subgroup (V ≃ₗ[ZMod 2] V),
      E' ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ →
      IsElemAbelian 3 E' → Nat.card E' ≤ Nat.card E) :
    ∃ (s j : ℕ) (F L : Subgroup (V ≃ₗ[ZMod 2] V)), Nat.card E = 3 ^ s ∧ F ≤ E ∧
      IsElemAbelian 3 F ∧ Nat.card F = 3 ^ j ∧ min 2 (s - 1) ≤ j ∧
      L ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓
        Subgroup.centralizer (F : Set (V ≃ₗ[ZMod 2] V)) ∧
      (∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ⊓
        Subgroup.centralizer (F : Set (V ≃ₗ[ZMod 2] V)), ∀ x ∈ L, g * x * g⁻¹ ∈ L) ∧
      CFSG.Open.IsQuasisimple ↥L ∧ 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨l, hl, hEeq, hno⟩ := exists_frame_max hQ hEΩ hE hmax
  have hcardE : Nat.card E = 3 ^ l.length := by rw [hEeq, card_torus hl]
  have hPd : finrank (ZMod 2) (perpL Q l) = 2 * n - 2 * l.length := by
    rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hl.finrank_Wspan]
  have hle2 := hl.finrank_perpL_le hQ hno
  have hWle : finrank (ZMod 2) (Wspan l) ≤ finrank (ZMod 2) V := Submodule.finrank_le _
  rw [hl.finrank_Wspan, hdim] at hWle
  have h4 : 4 ≤ n := by rcases hn with h | ⟨h, _⟩ <;> omega
  have hs : l.length = n ∨ l.length + 1 = n := by omega
  rcases hs with hs | hs
  ·
    have h5 : 5 ≤ n := by
      rcases hn with h | ⟨h4', hnp⟩
      · exact h
      · exfalso
        apply hnp
        have hP0 : perpL Q l = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
        have htop : Wspan l = ⊤ := by
          have := hl.isCompl.sup_eq_top
          rwa [hP0, sup_bot_eq] at this
        refine isPlusType_of_Wspan_eq_top htop ((isPlusType_Wspan_iff hl).2 ?_)
        rw [show l.length = 4 by omega]
        decide
    rcases l with _ | ⟨p₁, _ | ⟨p₂, _ | ⟨p₃, l'⟩⟩⟩
    · simp at hs; omega
    · simp at hs; omega
    · simp at hs; omega
    · have hlen : l'.length + 3 = n := by simpa using hs
      have hlI : IsFrame Q l' := hl.tail.tail.tail
      have hlJ : IsFrame Q [p₁, p₂, p₃] :=
        hl.sublist (List.Sublist.cons₂ _ (List.Sublist.cons₂ _ (List.Sublist.cons₂ _
          (List.nil_sublist _))))
      have hPI : finrank (ZMod 2) (perpL Q l') = 6 := by
        rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hlI.finrank_Wspan]
        omega
      have hle : Wspan [p₁, p₂, p₃] ≤ perpL Q l' := by
        intro w hw
        rw [perpL, LinearMap.BilinForm.mem_orthogonal_iff]
        intro m hm
        rw [QuadraticMap.polarBilin_apply_apply]
        refine polar_Wspan_Wspan (l₁ := l') (l₂ := [p₁, p₂, p₃]) (fun q hq p hp => ?_) hm hw
        have hpq := (List.pairwise_append.1 (show List.Pairwise (PairPerp Q)
          ([p₁, p₂, p₃] ++ l') from hl.perp)).2.2 p hp q hq
        exact hpq.symm
      have heq : Wspan [p₁, p₂, p₃] = perpL Q l' :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hlJ.finrank_Wspan, hPI]; rfl)
      have hts : ¬ IsPlusType (Q.comp (perpL Q l').subtype) := by
        intro hp
        have h := (isPlusType_Wspan_iff hlJ).1
          ((isPlusType_congr (CFSG.RankThree.PartOne.K159.isometryOfEq Q heq)).2 hp)
        have h3 : ([p₁, p₂, p₃] : List (V × V)).length = 3 := rfl
        rw [h3] at h
        exact absurd h (by decide)
      obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_component hQ (lJ := [p₁, p₂, p₃]) (lI := l')
        hl (by simp) (Or.inr hPI) hts
      refine ⟨(p₁ :: p₂ :: p₃ :: l').length, l'.length, torus Q l', L, hcardE, ?_,
        torus_isElemAbelian hlI, card_torus hlI, ?_, hL1, hL2, hL3, hL4⟩
      · rw [hEeq]
        exact torus_mono (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hq)))
      · simp only [List.length_cons]
        omega
  ·
    rcases l with _ | ⟨p, l'⟩
    · simp at hs; omega
    · have hlen : l'.length + 2 = n := by simpa using hs
      obtain ⟨hp, hperp, hlI⟩ := isFrame_cons.1 hl
      have hPI : finrank (ZMod 2) (perpL Q l') = 4 := by
        rw [perpL, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hlI.finrank_Wspan]
        omega
      have hV0 : finrank (ZMod 2) (perpL Q (p :: l')) = 2 := by
        rw [hPd]
        simp only [List.length_cons]
        omega
      have hV0plus : IsPlusType (Q.comp (perpL Q (p :: l')).subtype) :=
        isPlusType_of_no_minusPair hV0 hno
      have horth : ∀ a ∈ planeSpan p, ∀ b ∈ perpL Q (p :: l'), polar Q a b = 0 := by
        intro a ha b hb
        obtain ⟨hb1, hb2⟩ := (mem_perpL_iff _ b).1 hb p List.mem_cons_self
        obtain ⟨c, d, rfl⟩ := (mem_planeSpan_iff p a).1 ha
        rw [polar_add_left, polar_smul_left, polar_smul_left, hb1, hb2]
        simp
      have hdisj : Disjoint (planeSpan p) (perpL Q (p :: l')) := by
        rw [disjoint_iff, eq_bot_iff]
        intro x hx
        obtain ⟨hb1, hb2⟩ := (mem_perpL_iff _ x).1 hx.2 p List.mem_cons_self
        have := hp.eq_zero_of_mem_planeSpan_of_mem_perp hx.1 ((mem_perpPlane_iff p x).2 ⟨hb1, hb2⟩)
        exact (Submodule.mem_bot _).2 this
      have hle : planeSpan p ⊔ perpL Q (p :: l') ≤ perpL Q l' := by
        refine sup_le ?_ ?_
        · intro a ha
          rw [perpL, LinearMap.BilinForm.mem_orthogonal_iff]
          intro m hm
          rw [QuadraticMap.polarBilin_apply_apply, polar_comm]
          exact polar_planeSpan_Wspan hperp ha hm
        · intro x hx
          rw [mem_perpL_iff] at hx ⊢
          exact fun q hq => hx q (List.mem_cons_of_mem _ hq)
      have hfin : finrank (ZMod 2) (planeSpan p ⊔ perpL Q (p :: l') : Submodule (ZMod 2) V) = 4 := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq (planeSpan p) (perpL Q (p :: l'))
        rw [hdisj.eq_bot, finrank_bot, hp.finrank_planeSpan, hV0] at h
        omega
      have heq : planeSpan p ⊔ perpL Q (p :: l') = perpL Q l' :=
        Submodule.eq_of_le_of_finrank_eq hle (by rw [hfin, hPI])
      have hndV0 : (QuadraticMap.polarBilin (Q.comp (perpL Q (p :: l')).subtype)).Nondegenerate :=
        nondeg_comp_subtype (hl.perpL_nondeg hQ)
      have hts : ¬ IsPlusType (Q.comp (perpL Q l').subtype) := by
        intro hpl
        have h1 := (isPlusType_congr (CFSG.RankThree.PartOne.K159.isometryOfEq Q heq)).2 hpl
        rw [isPlusType_sup_iff hdisj horth (nondeg_planeSpan hp) hndV0 (le_refl 1) (le_refl 1)
          (by rw [hp.finrank_planeSpan]) (by rw [hV0])] at h1
        exact not_isPlusType_planeSpan hp (h1.2 hV0plus)
      obtain ⟨L, hL1, hL2, hL3, hL4⟩ := exists_component hQ (lJ := [p]) (lI := l') hl
        (by simp) (Or.inl hPI) hts
      refine ⟨(p :: l').length, l'.length, torus Q l', L, hcardE, ?_,
        torus_isElemAbelian hlI, card_torus hlI, ?_, hL1, hL2, hL3, hL4⟩
      · rw [hEeq]
        exact torus_mono (fun q hq => List.mem_cons_of_mem _ hq)
      · simp only [List.length_cons]
        omega

end Assemble

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC

end

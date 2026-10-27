module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12a

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a2

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)

section Subnormal

variable {G : Type} [Group G]

theorem subgroupOf_inf_normal {H M Y : Subgroup G} (hH : (H.subgroupOf M).Normal) :
    ((H ⊓ Y).subgroupOf (M ⊓ Y)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ H ⊓ Y := Subgroup.mem_subgroupOf.1 hn
  have hm : (n : G) ∈ M := (inf_le_left : M ⊓ Y ≤ M) n.2
  have hgM : (g : G) ∈ M := (inf_le_left : M ⊓ Y ≤ M) g.2
  have hgY : (g : G) ∈ Y := (inf_le_right : M ⊓ Y ≤ Y) g.2
  have h1 : (g : G) * n * (g : G)⁻¹ ∈ H := by
    have := hH.conj_mem ⟨n, hm⟩ (Subgroup.mem_subgroupOf.2 hn'.1) ⟨g, hgM⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  have h2 : (g : G) * n * (g : G)⁻¹ ∈ Y :=
    Y.mul_mem (Y.mul_mem hgY hn'.2) (Y.inv_mem hgY)
  refine Subgroup.mem_subgroupOf.2 ?_
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact ⟨h1, h2⟩

theorem isSubnormal_inf {J X : Subgroup G} (h : IsSubnormal J X) (Y : Subgroup G) :
    IsSubnormal (J ⊓ Y) (X ⊓ Y) := by
  induction h with
  | refl H => exact IsSubnormal.refl _
  | step hHM hnorm _ ih =>
    exact IsSubnormal.step (inf_le_inf_right _ hHM) (subgroupOf_inf_normal hnorm) ih

theorem isSubnormal_trans {A B : Subgroup G} (h : IsSubnormal A B) :
    ∀ {C : Subgroup G}, IsSubnormal B C → IsSubnormal A C := by
  induction h with
  | refl H => exact fun hC => hC
  | step hAM hnorm _ ih => exact fun hC => IsSubnormal.step hAM hnorm (ih hC)

theorem isSubnormal_le {A B : Subgroup G} (h : IsSubnormal A B) : A ≤ B := by
  induction h with
  | refl H => exact le_rfl
  | step hHM _ _ ih => exact hHM.trans ih

theorem mem_sup_of_le_normalizer {K X P : Subgroup G} (hPK : P ≤ K)
    (hXK : K ≤ Subgroup.normalizer (X : Set G)) {x : G} (hx : x ∈ X ⊔ P) :
    ∃ u ∈ X, ∃ p ∈ P, x = u * p := by
  let S : Subgroup G :=
    { carrier := {x | ∃ u ∈ X, ∃ p ∈ P, x = u * p}
      one_mem' := ⟨1, X.one_mem, 1, P.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨u, hu, p, hp, rfl⟩ ⟨u', hu', p', hp', rfl⟩
        refine ⟨u * (p * u' * p⁻¹), X.mul_mem hu ?_, p * p', P.mul_mem hp hp', by group⟩
        exact (Subgroup.mem_normalizer_iff.1 (hXK (hPK hp)) u').1 hu'
      inv_mem' := by
        rintro _ ⟨u, hu, p, hp, rfl⟩
        refine ⟨p⁻¹ * u⁻¹ * p, ?_, p⁻¹, P.inv_mem hp, by group⟩
        have h1 := (Subgroup.mem_normalizer_iff.1 (hXK (hPK (P.inv_mem hp))) u⁻¹).1
          (X.inv_mem hu)
        simpa using h1 }
  have hXS : X ≤ S := fun u hu => ⟨u, hu, 1, P.one_mem, by simp⟩
  have hPS : P ≤ S := fun p hp => ⟨1, X.one_mem, p, hp, by simp⟩
  exact (sup_le hXS hPS) hx

theorem isSubnormal_of_normal {V K : Subgroup G} (hVK : V ≤ K) (hV : (V.subgroupOf K).Normal) :
    IsSubnormal V K :=
  IsSubnormal.step hVK hV (IsSubnormal.refl K)

end Subnormal

section PCore

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_of_isSubnormal_aux {p : ℕ} [Fact p.Prime] {M H : Subgroup G}
    (h : IsSubnormal M H) :
    ∀ Y : Subgroup G, IsPGroup p Y → Y ≤ M → M ≤ Subgroup.normalizer (Y : Set G) →
      Y ≤ CFSG.Open.pCoreOf p H := by
  induction h with
  | refl K =>
    intro Y hY hYK hKN
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hYK hKN hY
  | @step Mb M1 Ktop hMM1 hnorm _ ih =>
    intro Y hY hYM hMN
    have hYZ : Y ≤ CFSG.Open.pCoreOf p Mb :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hYM hMN hY
    have hZ : IsPGroup p (CFSG.Open.pCoreOf p Mb : Subgroup G) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup p Mb
    have hZM1 : CFSG.Open.pCoreOf p Mb ≤ M1 :=
      (CFSG.LieType.BorelTits.pCoreOf_le p Mb).trans hMM1
    have hM1 : M1 ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p Mb : Set G) :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hMM1).1 hnorm).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf p Mb)
    exact hYZ.trans (ih _ hZ hZM1 hM1)

theorem le_pCoreOf_of_isSubnormal {p : ℕ} [Fact p.Prime] {X H : Subgroup G}
    (h : IsSubnormal X H) (hX : IsPGroup p X) : X ≤ CFSG.Open.pCoreOf p H :=
  le_pCoreOf_of_isSubnormal_aux h X hX le_rfl Subgroup.le_normalizer

end PCore

section Tof

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem normalizer_tof (M : Subgroup G) (a : G) {k : G} (hkM : k ∈ M) (hka : k ∈ Cg a) :
    k ∈ Subgroup.normalizer ((Tof p M a : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
    (Sec12a.mem_normalizer_inf (le_normalizer_alphaOf p M hkM) (Subgroup.le_normalizer hka))

end Tof

section Core

variable {G : Type} [Group G] [Finite G]

theorem core_inf_le_pCoreOf_Cg2 (a e : G) :
    CFSG.Open.pCoreOf 2 (Cg e) ⊓ Cg a ≤ CFSG.Open.pCoreOf 2 (Cg2 e a) := by
  rw [Sec12a.cg2_eq_inf]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Cg e)).to_le inf_le_left)
  · intro x hx
    exact ⟨hx.2, CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx.1⟩
  · intro k hk
    exact Sec12a.mem_normalizer_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Cg e) hk.2)
      (Subgroup.le_normalizer hk.1)

theorem pCoreOf_inf_le_pCoreOf_Cg2 {J : Subgroup G} (a e : G) (hJ : IsSubnormal J (Cg e)) :
    CFSG.Open.pCoreOf 2 (J ⊓ Cg a) ≤ CFSG.Open.pCoreOf 2 (Cg2 e a) := by
  have hK : IsSubnormal (J ⊓ Cg a) (Cg e ⊓ Cg a) := isSubnormal_inf hJ (Cg a)
  have hVK : IsSubnormal (CFSG.Open.pCoreOf 2 (J ⊓ Cg a)) (J ⊓ Cg a) :=
    isSubnormal_of_normal (CFSG.LieType.BorelTits.pCoreOf_le 2 (J ⊓ Cg a))
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 (J ⊓ Cg a))).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (J ⊓ Cg a)))
  have hV : IsSubnormal (CFSG.Open.pCoreOf 2 (J ⊓ Cg a)) (Cg e ⊓ Cg a) :=
    isSubnormal_trans hVK hK
  rw [Sec12a.cg2_eq_inf, inf_comm (Cg a) (Cg e)]
  exact le_pCoreOf_of_isSubnormal hV (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (J ⊓ Cg a))

end Core

@[expose] def BlockLayer : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a), ¬ Tof p M a ≤ CFSG.Open.pCoreOf 2 M →
      ∀ e ∈ E ⊓ A, e ≠ 1 →
        Tof p M a ⊓ Cg e ≤ CFSG.Open.pCoreOf 2 (Cg e) ⊔
          ⨆ (J : Subgroup G) (_ : J ≤ alphaOf p M ∧ IsSubnormal J (Cg e)),
            CFSG.Open.pCoreOf 2 (J ⊓ Cg a)

theorem caseB122i_of_inputs (hBlock : BlockLayer) : Sec12a.CaseB122i := by
  unfold Sec12a.CaseB122i
  intro G _ _ m p B M E A a h hT e he he1
  have hB := (show BlockLayer from hBlock) h hT e he he1
  have hP : (⨆ (J : Subgroup G) (_ : J ≤ alphaOf p M ∧ IsSubnormal J (Cg e)),
      CFSG.Open.pCoreOf 2 (J ⊓ Cg a)) ≤ CFSG.Open.pCoreOf 2 (Cg2 e a) :=
    iSup₂_le fun J hJ => pCoreOf_inf_le_pCoreOf_Cg2 a e hJ.2
  have hPe : (⨆ (J : Subgroup G) (_ : J ≤ alphaOf p M ∧ IsSubnormal J (Cg e)),
      CFSG.Open.pCoreOf 2 (J ⊓ Cg a)) ≤ Cg e :=
    iSup₂_le fun J hJ =>
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left).trans (isSubnormal_le hJ.2)
  have hPa : (⨆ (J : Subgroup G) (_ : J ≤ alphaOf p M ∧ IsSubnormal J (Cg e)),
      CFSG.Open.pCoreOf 2 (J ⊓ Cg a)) ≤ Cg a :=
    iSup₂_le fun J _ => (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right
  intro x hx
  have hxa : x ∈ Cg a := Sec12a.tof_le_cg M a hx.1
  have hxe : x ∈ Cg e := hx.2
  obtain ⟨u, hu, q, hq, hxuq⟩ := mem_sup_of_le_normalizer hPe
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Cg e)) (hB hx)
  have hqa : q ∈ Cg a := hPa hq
  have hua : u ∈ Cg a := by
    have hu_eq : u = x * q⁻¹ := by rw [hxuq]; group
    rw [hu_eq]
    exact (Cg a).mul_mem hxa ((Cg a).inv_mem hqa)
  have hu' : u ∈ CFSG.Open.pCoreOf 2 (Cg2 e a) :=
    core_inf_le_pCoreOf_Cg2 a e ⟨hu, hua⟩
  rw [hxuq]
  exact (CFSG.Open.pCoreOf 2 (Cg2 e a)).mul_mem hu' (hP hq)

section Derived

variable {G : Type} [Group G]

theorem le_derivedInf_of_perfect {J H : Subgroup G} (hJH : J ≤ H) (hJ : ⁅J, J⁆ = J) :
    J ≤ derivedInf H := by
  unfold derivedInf
  refine le_iInf fun n => ?_
  induction n with
  | zero =>
    rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hJH
  | succ n ih =>
    rw [derivedSeries_succ, Subgroup.map_commutator]
    calc J = ⁅J, J⁆ := hJ.symm
      _ ≤ _ := Subgroup.commutator_mono ih ih

end Derived

section Iii

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

@[expose] def PieceIII (p : ℕ) (M A : Subgroup G) (a x : G) (V J : Subgroup G) : Prop :=
  V ≤ Tof p M a ⊓ Subgroup.centralizer (A : Set G) ∧ V ≤ J ∧ J ≤ alphaOf p M ⊓ Cg x ∧
    ⁅J, J⁆ = J ∧ J ≤ ⨆ g ∈ (alphaOf p M ⊓ Cg x), GLBConj g V

@[expose] def BlockIII : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {a : G}
    (h : Cex121 G m p B M E A a) {F : Subgroup G} (_hF : IsEkIn p 2 A F),
    ¬ Tof p M a ≤ CFSG.Open.pCoreOf 2 M →
      Tof p M a ⊓ Subgroup.centralizer (A : Set G) ≤
        (Tof p M a ⊓ Subgroup.centralizer (A : Set G) ⊓ CFSG.Open.pCoreOf 2 M) ⊔
          ⨆ (x : G) (_ : x ∈ F) (_ : x ≠ 1) (V : Subgroup G) (J : Subgroup G)
            (_ : PieceIII p M A a x V J), V

theorem caseB122iii_of_inputs (hBlock : BlockIII) : Sec12a.CaseB122iii := by
  unfold Sec12a.CaseB122iii
  intro G _ _ m p B M E A a h F hF hT
  have hB := (show BlockIII from hBlock) h hF hT
  refine ⟨fun x => ⨆ (V : Subgroup G) (J : Subgroup G) (_ : PieceIII p M A a x V J), V,
    ?_, ?_, ?_⟩
  · intro x _ _
    exact iSup_le fun V => iSup_le fun J => iSup_le fun hP => hP.1
  · refine le_antisymm ?_ ?_
    · refine hB.trans (sup_le_sup_left ?_ _)
      refine iSup_le fun x => iSup_le fun hxF => iSup_le fun hx1 =>
        iSup_le fun V => iSup_le fun J => iSup_le fun hP => ?_
      refine le_iSup_of_le x (le_iSup_of_le hxF (le_iSup_of_le hx1 ?_))
      exact le_iSup_of_le V (le_iSup_of_le J (le_iSup_of_le hP le_rfl))
    · refine sup_le inf_le_left (iSup_le fun x => iSup_le fun _ =>
        iSup_le fun _ => iSup_le fun V => iSup_le fun J => iSup_le fun hP => hP.1)
  · intro x _ _
    refine iSup_le fun V => iSup_le fun J => iSup_le fun hP => ?_
    have hVVx : V ≤ ⨆ (V' : Subgroup G) (J' : Subgroup G) (_ : PieceIII p M A a x V' J'), V' :=
      le_iSup_of_le V (le_iSup_of_le J (le_iSup_of_le hP le_rfl))
    have hJN : J ≤ ⨆ g ∈ (alphaOf p M ⊓ Cg x),
        GLBConj g (⨆ (V' : Subgroup G) (J' : Subgroup G) (_ : PieceIII p M A a x V' J'), V') :=
      hP.2.2.2.2.trans (iSup₂_mono fun g _ => Subgroup.map_mono hVVx)
    exact hP.2.1.trans (le_derivedInf_of_perfect hJN hP.2.2.2.1)

end Iii

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12a2

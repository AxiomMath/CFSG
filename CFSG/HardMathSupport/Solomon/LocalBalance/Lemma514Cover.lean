module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7
public import CFSG.Foundations.Catalog

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Ns
open scoped Matrix

set_option linter.unusedSectionVars false

namespace Lemma514CoverNs

structure InndiagVocab where
  innDiag : ∀ (Y : Type) [Group Y], Subgroup (MulAut Y)

variable {G : Type} [Group G] [Finite G]

abbrev Cs (g : G) : Subgroup G := Subgroup.centralizer ({g} : Set G)
abbrev CD (D : Subgroup G) : Subgroup G := Subgroup.centralizer (D : Set G)
@[expose] noncomputable def ncl (H J : Subgroup G) : Subgroup G := ⨆ g ∈ H, GLBConj g J

@[expose] def TrivOn (K : Subgroup G) (g : G) : Prop :=
  ∃ h : g ∈ Subgroup.normalizer (K : Set G), barAut 3 K ⟨g, h⟩ = 1

@[expose] def IndInn (V : InndiagVocab) (K : Subgroup G) (g : G) : Prop :=
  ∃ h : g ∈ Subgroup.normalizer (K : Set G), barAut 3 K ⟨g, h⟩ ∈ V.innDiag (barOf 3 K)

@[expose] def IsPSLn (n r : ℕ) (Y : Type*) [Group Y] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ∧
    Nonempty (Y ≃* StatedProj (StatedSL n F))

@[expose] def IsPSUn (n r : ℕ) (Y : Type*) [Group Y] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ^ 2 ∧
    Nonempty (Y ≃* StatedProj (StatedSU n r F))

@[expose] def IsL3Eps (r : ℕ) (Y : Type*) [Group Y] : Prop :=
  (r % 3 = 1 ∧ IsPSLn 3 r Y) ∨ (r % 3 = 2 ∧ IsPSUn 3 r Y)

@[expose] def IsTypeL2 (r : ℕ) (Y : Type*) [Group Y] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = r ∧
    Nonempty ((Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL 2 F))


@[expose] def IsEntrywiseAutPSLn (n : ℕ) {F : Type} [Field F] (σ : F ≃+* F)
    (φ : MulAut (StatedProj (StatedSL n F))) : Prop :=
  ∀ A A' : ↥(StatedSL n F),
    ((A' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map σ →
    φ (QuotientGroup.mk A) = QuotientGroup.mk A'

@[expose] def IsFieldAutPSLn (n : ℕ) {Y : Type*} [Group Y] (α : MulAut Y) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (θ : (Y ⧸ Subgroup.center Y) ≃* StatedProj (StatedSL n F))
    (σ : F ≃+* F) (φ γ : MulAut (StatedProj (StatedSL n F))),
    IsEntrywiseAutPSLn n σ φ ∧
      ∀ y : Y, θ (QuotientGroup.mk (α y)) = (γ * φ * γ⁻¹) (θ (QuotientGroup.mk y))

@[expose] def InducesFieldAutN (n : ℕ) (L : Subgroup G) (g : G) : Prop :=
  ∃ h : g ∈ Subgroup.normalizer (L : Set G), IsFieldAutPSLn n (barAut 3 L ⟨g, h⟩)

@[expose] def IsL3Raw (r : ℕ) (Y : Type*) [Group Y] : Prop := IsPSLn 3 r Y ∨ IsPSUn 3 r Y

noncomputable abbrev CLay (K : Subgroup G) (g : G) : Subgroup G := GLAPLayer 3 (K ⊓ Cs g)


@[expose] def Input18_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), IsKGroup ↥X → ∀ Q : Subgroup G, Q ≤ X →
    IsPGroup 3 Q → GLAPLayer 3 (X ⊓ CD Q) ≤ GLAPLayer 3 X

@[expose] def Input18_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G → ∀ D E : Subgroup G,
    IsPGroup 3 D → IsPGroup 3 E → (∀ d ∈ D, ∀ e ∈ E, d * e = e * d) →
      GLAPLayer 3 (GLAPLayer 3 (CD D) ⊓ CD E) = GLAPLayer 3 (CD D ⊓ CD E)

@[expose] def Input18_3_4G : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G → ∀ D E : Subgroup G,
    IsElemAbelian 3 E → D ≤ E → ∀ J : Subgroup G, GLAPComponent 3 (CD E) J →
      ∃ 𝒞 : Set (Subgroup G), (∀ L ∈ 𝒞, GLAPComponent 3 (CD D) L) ∧
        (⨆ L ∈ 𝒞, L) = ncl (GLAPLayer 3 (CD D)) J ∧
        (∀ L ∈ 𝒞, ∀ e ∈ E, GLBConj e L ∈ 𝒞) ∧ ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, ∃ e ∈ E, GLBConj e L = L'

@[expose] def Input9_2_3 (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I : Subgroup G), CFSG.Open.IsQuasisimple (barOf 3 I) →
    IsKGroup ↥I → ∀ x : G, x ∈ Subgroup.normalizer (I : Set G) → x ^ 3 = 1 → ¬ IndInn V I x →
      ∀ J : Subgroup G, GLAPComponent 3 (I ⊓ Cs x) J → ∀ r0 : ℕ, 10 ≤ r0 → IsTypeL2 r0 (barOf 3 J) →
        IsTypeL2 (r0 ^ 3) (barOf 3 I)

@[expose] def Input14_31_4 (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I B : Subgroup G), CFSG.Open.IsQuasisimple (barOf 3 I) →
    IsKGroup ↥I → B ≤ Subgroup.normalizer (I : Set G) → GLATwoLocalRank 3 ↥(I ⊔ B) ≤ 4 →
    IsElemAbelian 3 B → (∃ c ∈ B, c ≠ 1 ∧ c ∈ CD I) →
    ∀ (A : Subgroup G) (x : G), A ≤ B → x ∈ A → Nat.card A = 9 → ¬ TrivOn I x →
    ∀ J : Subgroup G, GLAPComponent 3 (I ⊓ Cs x) J → ∀ q : ℕ, IsTypeL2 q (barOf 3 J) →
      ¬ 3 ∣ q → q ≠ 8 → (∀ a ∈ A, IndInn V I a) →
      (∀ a ∈ A, a ∉ Subgroup.zpowers x → InducesFieldAutN 2 J a ∧ ¬ TrivOn J a) →
        (∃ r0 : ℕ, r0 ^ 3 = q ∧ IsPSUn 6 r0 (barOf 3 I ⧸ Subgroup.center (barOf 3 I))) ∧
        J = CLay I x ∧
        ∃ a ∈ A, a ≠ 1 ∧ ∃ r0 : ℕ, r0 ^ 3 = q ∧ ∃ H₁ H₂ H₃ : Subgroup G,
          GLAPComponent 3 (I ⊓ Cs a) H₁ ∧ GLAPComponent 3 (I ⊓ Cs a) H₂ ∧
          GLAPComponent 3 (I ⊓ Cs a) H₃ ∧ H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
          CLay I a = H₁ ⊔ H₂ ⊔ H₃ ∧
          (∀ H : Subgroup G, (H = H₁ ∨ H = H₂ ∨ H = H₃) → IsTypeL2 r0 (barOf 3 H)) ∧
          ∀ H H' : Subgroup G, (H = H₁ ∨ H = H₂ ∨ H = H₃) → (H' = H₁ ∨ H' = H₂ ∨ H' = H₃) →
            ∃ e ∈ A, GLBConj e H = H'


section Glue

theorem gl_isSubnormal_inf {G : Type} [Group G] {A B : Subgroup G} (C : Subgroup G)
    (h : IsSubnormal A B) : IsSubnormal (A ⊓ C) (B ⊓ C) := isSubnormal_inf h C

theorem gl_isSubnormal_of_le {G : Type} [Group G] {A B C : Subgroup G} (h : IsSubnormal A C)
    (hAB : A ≤ B) (hBC : B ≤ C) : IsSubnormal A B := isSubnormal_of_le_of_le h hAB hBC

theorem gl_comp_lift {G : Type} [Group G] [Finite G] {Y' Y J : Subgroup G}
    (hsn : IsSubnormal Y' Y) (hJ : GLAPComponent 3 Y' J) : GLAPComponent 3 Y J := by
  obtain ⟨hJY', hJsn, hcomp, hmin⟩ := hJ
  have hY'Y : Y' ≤ Y := isSubnormal_le' hsn
  have hJsnY : IsSubnormal J Y := isSubnormal_trans' hJsn hsn
  refine ⟨hJY'.trans hY'Y, hJsnY, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := Y) 3 hJsnY
    rwa [barX_self] at this
  · have e : ↥(barX 3 Y J) ≃* ↥(barX 3 Y' J) :=
      (quotEquivBarX Nat.prime_three (hJY'.trans hY'Y) hJsnY).symm.trans
        (quotEquivBarX Nat.prime_three hJY' hJsn)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcomp.2.2
  · intro J' hlt hJ'sn heq
    have hJ'J : J' ≤ J := hlt.le
    have hJ'sn' : IsSubnormal J' Y' :=
      isSubnormal_trans' (isSubnormal_of_le_of_le hJ'sn hJ'J (hJY'.trans hY'Y)) hJsn
    have hcore : J ⊓ GLAPPrimeCoreOf 3 Y ≤ GLAPPrimeCoreOf 3 Y' := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal Nat.prime_three hJsnY]
      exact CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_le_of_isSubnormal Nat.prime_three hJsn
    refine hmin J' hlt hJ'sn' ?_
    show barX 3 Y' J' = barX 3 Y' J
    refine le_antisymm (barX_mono 3 hJ'J) ?_
    refine barX_le_of_forall (hJ'J.trans hJY') (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := Y) (le_of_eq heq.symm) hk
      ((hJY'.trans hY'Y) hk)
    exact ⟨j, hj, hcore ⟨J.mul_mem (J.inv_mem (hJ'J hj)) hk, hjk⟩⟩

theorem gl_comp_restrict {G : Type} [Group G] [Finite G] {Y Y'' J : Subgroup G}
    (hJ : GLAPComponent 3 Y J) (h1 : J ≤ Y'') (h2 : Y'' ≤ Y) : GLAPComponent 3 Y'' J :=
  glaPComponent_of_le Nat.prime_three hJ h1 h2

theorem gl_comp_eq_of_le {G : Type} [Group G] [Finite G] {X K J : Subgroup G}
    (hK : GLAPComponent 3 X K) (hJ : GLAPComponent 3 X J) (hle : J ≤ K) : J = K := by
  refine glaPComponent_unique hJ hK ?_
  exact CFSG.ComponentClassification.LocalComponents.eq_of_le _ _ hJ.2.2.1 hK.2.2.1
    (barX_mono 3 hle)

theorem gla_not_comm {Γ : Type} [Group Γ] {J : Subgroup Γ}
    (hJ : CFSG.Open.IsQuasisimple ↥J) : ¬ ∀ n ∈ J, ∀ q ∈ J, n * q = q * n := by
  intro hc
  obtain ⟨hperf, hs⟩ := hJ
  have hab : ∀ a b : ↥J, a * b = b * a := fun a b =>
    Subtype.ext (hc a a.2 b b.2)
  have hbot : commutator ↥J = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top]
    exact Subgroup.eq_top_iff' _ |>.2 fun a => Subgroup.mem_center_iff.2 fun b => hab b a
  have hsub : Subsingleton ↥J := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ commutator ↥J := hperf ▸ Subgroup.mem_top a
    have hb : b ∈ commutator ↥J := hperf ▸ Subgroup.mem_top b
    rw [hbot, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have : Subsingleton (↥J ⧸ Subgroup.center ↥J) :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).subsingleton
  exact (not_nontrivial_iff_subsingleton.2 this) hs.toNontrivial

theorem gla_eq_of_subnormal {Γ : Type} [Group Γ] {Q J : Subgroup Γ}
    (h : IsSubnormal J Q) (hq : CFSG.Open.IsQuasisimple ↥Q)
    (hJ : ¬ ∀ n ∈ J, ∀ q ∈ Q, n * q = q * n) : J = Q := by
  induction h with
  | refl => rfl
  | @step H M K hHM hn hM ih =>
    have hMK : M = K := ih hq fun hc => hJ fun n hn q hq' => hc n (hHM hn) q hq'
    subst hMK
    have hnorm : ∀ q ∈ M, ∀ n ∈ H, q * n * q⁻¹ ∈ H := fun q hq' n hn' => by
      have := hn.conj_mem ⟨n, hHM hn'⟩ (by simpa [Subgroup.mem_subgroupOf] using hn') ⟨q, hq'⟩
      simpa [Subgroup.mem_subgroupOf] using this
    rcases normal_central_or_eq hq hHM hnorm with hc | hc
    · exact absurd hc (fun hc => hJ fun n hn q hq' => hc n hn q hq')
    · exact hc

theorem gl_comp_in_quasi {Γ : Type} [Group Γ] {Q J : Subgroup Γ}
    (hq : CFSG.Open.IsQuasisimple ↥Q) (hJ : IsComponentOf J Q) : J = Q :=
  gla_eq_of_subnormal hJ.2.1 hq fun hc => gla_not_comm hJ.2.2 fun n hn q hq' => hc n hn q (hJ.1 hq')

theorem gl_comp_iff_layer {G : Type} [Group G] [Finite G] {Z J : Subgroup G} :
    GLAPComponent 3 Z J ↔ GLAPComponent 3 (GLAPLayer 3 Z) J := by
  have hle : GLAPLayer 3 Z ≤ Z := sSup_le fun L hL => hL.1
  constructor
  · intro hJ
    exact gl_comp_restrict hJ (le_sSup hJ) hle
  · intro hJ
    have hnorm : ((GLAPLayer 3 Z).subgroupOf Z).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hg : (g : G) ∈ Z := g.2
      have hcl : GLAPLayer 3 Z ≤ GLBConj (g : G) (GLAPLayer 3 Z) := by
        refine sSup_le fun L hL x hx => ?_
        rw [mem_gLBConj]
        have hc := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL (g : G)⁻¹
        rw [gLBConj_eq_of_mem' (Z.inv_mem hg)] at hc
        have hx' : (g : G) * x * (g : G)⁻¹ ∈ GLBConj (g : G)⁻¹ L := by
          rw [mem_gLBConj]; simpa [mul_assoc] using hx
        exact (le_sSup hc : GLBConj (g : G)⁻¹ L ≤ GLAPLayer 3 Z) hx'
      have := mem_gLBConj.1 (hcl hn)
      simpa using this
    exact gl_comp_lift (IsSubnormal.step hle hnorm (IsSubnormal.refl Z)) hJ

variable {G : Type} [Group G] [Finite G]

theorem glb_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B :=
  h.of_mulEquiv e.symm

theorem glb_inf_core_le {H A : Subgroup G} (hHA : H ≤ A) :
    H ⊓ GLAPPrimeCoreOf 3 A ≤ GLAPPrimeCoreOf 3 H := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set O := GLAPPrimeCoreOf 3 A with hO
  set N0 : Subgroup ↥H := O.subgroupOf H with hN0
  have hnorm : N0.Normal := by
    refine ⟨fun n hn h' => ?_⟩
    show ((h' * n * h'⁻¹ : ↥H) : G) ∈ O
    have := (Subgroup.mem_normalizer_iff.1
      (le_normalizer_glaPPrimeCoreOf 3 A (hHA h'.2)) (n : G)).1 hn
    simpa using this
  have hdvd : Nat.card N0 ∣ Nat.card O := by
    have h1 : N0.map H.subtype = H ⊓ O := by
      rw [hN0, ← Subgroup.inf_subgroupOf_right O H]
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : O ⊓ H ≤ H)]
      exact inf_comm _ _
    have h2 : Nat.card (N0.map H.subtype) = Nat.card N0 :=
      Subgroup.card_map_of_injective H.subtype_injective
    rw [← h2, h1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime 3 (Nat.card N0) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf hp A (hd.trans hdvd)
  have hle : N0 ≤ GLAPPrimeCore 3 ↥H := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx.2), rfl⟩

theorem gl_barOf_equiv {X K : Subgroup G} (h : GLAPComponent 3 X K) :
    Nonempty (barOf 3 K ≃* ↥(barX 3 X K)) :=
  ⟨quotEquivBarX Nat.prime_three h.1 h.2.1⟩

theorem gl_quasi_barX {X K : Subgroup G} (h : GLAPComponent 3 X K) :
    CFSG.Open.IsQuasisimple ↥(barX 3 X K) := h.2.2.1.2.2

theorem gl_quasi_barOf {X K : Subgroup G} (h : GLAPComponent 3 X K) :
    CFSG.Open.IsQuasisimple (barOf 3 K) := by
  obtain ⟨e⟩ := gl_barOf_equiv h
  exact glb_isQuasisimple_of_mulEquiv e.symm (gl_quasi_barX h)

theorem gl_card_barX {X K : Subgroup G} (h : GLAPComponent 3 X K) :
    Nat.card ↥(barX 3 X K) = Nat.card (barOf 3 K) := by
  obtain ⟨e⟩ := gl_barOf_equiv h
  exact (Nat.card_congr e.toEquiv).symm

theorem gl_cover_of_barX_eq {X J K : Subgroup G} (hK : GLAPComponent 3 X K) (hJK : J ≤ K)
    (h : barX 3 X J = barX 3 X K) : K ≤ J ⊔ GLAPPrimeCoreOf 3 K := by
  intro k hk
  have hkX : k ∈ X := hK.1 hk
  have hmem : (QuotientGroup.mk ⟨k, hkX⟩ : ↥X ⧸ GLAPPrimeCore 3 ↥X) ∈ barX 3 X J := by
    rw [h]
    exact (mem_barX_iff' 3 X K _).2 ⟨⟨k, hkX⟩, hk, rfl⟩
  obtain ⟨j, hj, hjk⟩ := (mem_barX_iff' 3 X J _).1 hmem
  have hker : j⁻¹ * ⟨k, hkX⟩ ∈ GLAPPrimeCore 3 ↥X := QuotientGroup.eq.1 hjk
  have hker' : ((j⁻¹ * ⟨k, hkX⟩ : ↥X) : G) ∈ GLAPPrimeCoreOf 3 X := ⟨_, hker, rfl⟩
  have hjK : (j : G) ∈ K := hJK hj
  have hc : (j : G)⁻¹ * k ∈ GLAPPrimeCoreOf 3 K :=
    glb_inf_core_le (H := K) (A := X) hK.1 ⟨K.mul_mem (K.inv_mem hjK) hk, hker'⟩
  have : k = (j : G) * ((j : G)⁻¹ * k) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hj hc

theorem gl_barX_eq_of_cover {X J K : Subgroup G} (hK : GLAPComponent 3 X K) (hJK : J ≤ K)
    (h : K ≤ J ⊔ GLAPPrimeCoreOf 3 K) : barX 3 X J = barX 3 X K := by
  refine le_antisymm (barX_mono' 3 hJK) ?_
  have hJX : J ≤ X := hJK.trans hK.1
  set P : Subgroup ↥X := (barX 3 X J).comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) with hP
  have hsup : J ⊔ GLAPPrimeCoreOf 3 K ≤ P.map X.subtype := by
    refine sup_le ?_ ?_
    · intro j hj
      exact ⟨⟨j, hJX hj⟩, (mem_barX_iff' 3 X J _).2 ⟨⟨j, hJX hj⟩, hj, rfl⟩, rfl⟩
    · intro c hc
      have hcX : c ∈ GLAPPrimeCoreOf 3 X := glaPPrimeCoreOf_le_of_isSubnormal 3 hK.2.1 hc
      obtain ⟨c', hc', rfl⟩ := hcX
      refine ⟨c', ?_, rfl⟩
      show QuotientGroup.mk' _ c' ∈ barX 3 X J
      have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) c' = 1 := (QuotientGroup.eq_one_iff c').2 hc'
      rw [h1]
      exact one_mem _
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hsup (h ((Subgroup.mem_subgroupOf).1 hx))
  have : y = x := Subtype.ext hyx
  subst this
  exact hy

theorem gl_barX_eq_of_isComponentOf {X J K : Subgroup G} (hK : GLAPComponent 3 X K)
    (hJ : IsComponentOf (barX 3 X J) (barX 3 X K)) : barX 3 X J = barX 3 X K :=
  gl_comp_in_quasi (gl_quasi_barX hK) hJ

theorem gl_barOf_equiv_of_centreless {X J F : Subgroup G} (hFJ : F ≤ J) (hF3 : IsPGroup 3 F)
    (hF : F ≠ ⊥) (hJX : J ≤ X) (hq : CFSG.Open.IsQuasisimple ↥(barX 3 X J))
    (hZ : Subgroup.center ↥(barX 3 X J) = ⊥) : Nonempty (barOf 3 J ≃* ↥(barX 3 X J)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set f := barMap 3 hJX with hf
  have hsurj : Function.Surjective f := barMap_surjective hJX
  have hkerc : Nat.Coprime 3 (Nat.card f.ker) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
    refine not_dvd_card_glaPPrimeCoreOf hp X (hd.trans ?_)
    have hc : Nat.card (f.ker.map J.subtype) = Nat.card f.ker :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [← hc]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨Subgroup.inclusion hJX k, QuotientGroup.eq_one_iff _ |>.1 (Subtype.ext_iff.1 hk), rfl⟩
  have hker_le : f.ker ≤ GLAPPrimeCore 3 ↥J := le_sSup ⟨f.normal_ker, hkerc⟩
  have hO_le : GLAPPrimeCore 3 ↥J ≤ f.ker := by
    set N' : Subgroup ↥(barX 3 X J) := (GLAPPrimeCore 3 ↥J).map f with hN'
    have hN'n : N'.Normal := Subgroup.Normal.map inferInstance f hsurj
    have hOc : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) := by
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
      refine not_dvd_card_glaPPrimeCoreOf hp J ?_
      unfold GLAPPrimeCoreOf
      rw [Subgroup.card_map_of_injective J.subtype_injective]
      exact hd
    obtain ⟨-, hs⟩ := hq
    have hnm : (N'.map (QuotientGroup.mk' (Subgroup.center ↥(barX 3 X J)))).Normal :=
      Subgroup.Normal.map hN'n _ (QuotientGroup.mk'_surjective _)
    rcases (haveI := hnm; hs.eq_bot_or_eq_top_of_normal (N'.map (QuotientGroup.mk' (Subgroup.center ↥(barX 3 X J))))) with h0 | h1
    · have : N' = ⊥ := by
        rw [eq_bot_iff]
        intro n hn
        have : QuotientGroup.mk' (Subgroup.center ↥(barX 3 X J)) n ∈
            N'.map (QuotientGroup.mk' (Subgroup.center ↥(barX 3 X J))) := ⟨n, hn, rfl⟩
        rw [h0] at this
        have h2 : n ∈ Subgroup.center ↥(barX 3 X J) := by
          simpa using this
        rw [hZ] at h2
        exact h2
      intro x hx
      have : f x ∈ N' := ⟨x, hx, rfl⟩
      rw [‹N' = ⊥›] at this
      exact this
    · exfalso
      have hN'top : N' = ⊤ := by
        rw [eq_top_iff]
        intro y _
        have : QuotientGroup.mk' (Subgroup.center ↥(barX 3 X J)) y ∈
            N'.map (QuotientGroup.mk' (Subgroup.center ↥(barX 3 X J))) := by
          rw [h1]; trivial
        obtain ⟨n, hn, hny⟩ := this
        have h2 : n⁻¹ * y ∈ Subgroup.center ↥(barX 3 X J) := QuotientGroup.eq.1 hny
        rw [hZ] at h2
        have : y = n := by
          have := (Subgroup.mem_bot.1 h2)
          rw [inv_mul_eq_one] at this
          exact this.symm
        rw [this]; exact hn
      set F' : Subgroup ↥J := F.subgroupOf J with hF'
      have hF'3 : IsPGroup 3 F' := hF3.of_equiv (Subgroup.subgroupOfEquivOfLe hFJ).symm
      have hinj : Function.Injective (f.comp F'.subtype) := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro y hy
        have hy1 : (y : ↥J) ∈ f.ker := MonoidHom.mem_ker.1 hy
        have hord : orderOf (⟨(y : ↥J), hy1⟩ : ↥f.ker) ∣ Nat.card f.ker := orderOf_dvd_natCard _
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hF'3) y
        have hord' : orderOf (y : ↥J) = orderOf y := Subgroup.orderOf_coe y
        have h3 : orderOf (⟨(y : ↥J), hy1⟩ : ↥f.ker) = orderOf (y : ↥J) := Subgroup.orderOf_mk _ _
        rw [h3, hord', hk] at hord
        have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hkerc) hord
        rw [this] at hk
        have : y = 1 := orderOf_eq_one_iff.1 hk
        rw [this]; exact one_mem _
      have hdiv1 : Nat.card F' ∣ Nat.card ↥(barX 3 X J) := Subgroup.card_dvd_of_injective _ hinj
      have hdiv2 : Nat.card ↥(barX 3 X J) ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
        have e1 : Nat.card N' = Nat.card ↥(barX 3 X J) := by
          rw [hN'top]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
        rw [← e1]
        exact Subgroup.card_map_dvd (H := GLAPPrimeCore 3 ↥J) f
      obtain ⟨n, hn⟩ := hF'3.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero, Subgroup.card_eq_one] at hn
        apply hF
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hFJ hx⟩ : ↥J) ∈ F' := hx
        rw [hn] at this
        exact Subgroup.mem_bot.2 (congrArg Subtype.val (Subgroup.mem_bot.1 this))
      have h3 : 3 ∣ Nat.card (GLAPPrimeCore 3 ↥J) := by
        refine dvd_trans ?_ (hdiv1.trans hdiv2)
        rw [hn]; exact dvd_pow_self 3 hn0
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hOc h3
  have hker : f.ker = GLAPPrimeCore 3 ↥J := le_antisymm hker_le hO_le
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

theorem glc_coe_normalizerMonoidHom {K : Subgroup G} {g : G}
    (h : g ∈ Subgroup.normalizer (K : Set G)) (x : ↥K) :
    ((K.normalizerMonoidHom ⟨g, h⟩ x : ↥K) : G) = g * x * g⁻¹ := rfl

theorem glc_mem_primeCoreOf {K : Subgroup G} (z : ↥K) :
    (z : G) ∈ GLAPPrimeCoreOf 3 K ↔ z ∈ GLAPPrimeCore 3 ↥K := by
  unfold GLAPPrimeCoreOf
  exact Subgroup.mem_map_iff_mem K.subtype_injective

theorem gl_trivOn_iff {K : Subgroup G} {g : G} : TrivOn K g ↔
    g ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ GLAPPrimeCoreOf 3 K := by
  constructor
  · rintro ⟨h, h1⟩
    refine ⟨h, fun k hk => ?_⟩
    have h2 := congrArg (fun φ => φ (QuotientGroup.mk ⟨k, hk⟩)) h1
    simp only [barAut_mk, MulAut.one_apply] at h2
    rw [QuotientGroup.eq_iff_div_mem] at h2
    have := (glc_mem_primeCoreOf (K := K) (K.normalizerMonoidHom ⟨g, h⟩ ⟨k, hk⟩ / ⟨k, hk⟩)).2 h2
    simpa [div_eq_mul_inv, glc_coe_normalizerMonoidHom] using this
  · rintro ⟨h, h1⟩
    refine ⟨h, ?_⟩
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [barAut_mk, MulAut.one_apply]
      rw [QuotientGroup.eq_iff_div_mem]
      refine (glc_mem_primeCoreOf _).1 ?_
      simpa [div_eq_mul_inv, glc_coe_normalizerMonoidHom] using h1 x x.2

theorem gl_barAut_mul {K : Subgroup G} {g h : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hh : h ∈ Subgroup.normalizer (K : Set G)) :
    barAut 3 K ⟨g * h, mul_mem hg hh⟩ = barAut 3 K ⟨g, hg⟩ * barAut 3 K ⟨h, hh⟩ :=
  map_mul (barAut 3 K) (⟨g, hg⟩ : ↥(Subgroup.normalizer (K : Set G))) ⟨h, hh⟩

theorem gl_indInn_mul {V : InndiagVocab} {K : Subgroup G} {g h : G} (hg : IndInn V K g)
    (hh : IndInn V K h) : IndInn V K (g * h) := by
  obtain ⟨hg, h1⟩ := hg
  obtain ⟨hh, h2⟩ := hh
  exact ⟨mul_mem hg hh, by rw [gl_barAut_mul hg hh]; exact mul_mem h1 h2⟩

theorem gl_indInn_pow {V : InndiagVocab} {K : Subgroup G} {g : G} (hg : IndInn V K g) (j : ℕ) :
    IndInn V K (g ^ j) := by
  induction j with
  | zero =>
    refine ⟨by simpa using one_mem _, ?_⟩
    have : (⟨g ^ 0, by simpa using one_mem (Subgroup.normalizer (K : Set G))⟩ :
        ↥(Subgroup.normalizer (K : Set G))) = 1 := by ext; simp
    rw [this, map_one]
    exact one_mem _
  | succ j ih =>
    rw [pow_succ]
    exact gl_indInn_mul ih hg

theorem gl_indInn_of_trivOn {V : InndiagVocab} {K : Subgroup G} {g : G} (h : TrivOn K g) :
    IndInn V K g := by
  obtain ⟨hg, h1⟩ := h
  exact ⟨hg, by rw [h1]; exact one_mem _⟩

theorem gl_mul_trivOn {V : InndiagVocab} {K : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hh : TrivOn K h) :
    (IndInn V K (g * h) ↔ IndInn V K g) ∧ (TrivOn K (g * h) ↔ TrivOn K g) := by
  obtain ⟨hh, h1⟩ := hh
  have key : barAut 3 K ⟨g * h, mul_mem hg hh⟩ = barAut 3 K ⟨g, hg⟩ := by
    rw [gl_barAut_mul hg hh, h1, mul_one]
  constructor
  · constructor
    · rintro ⟨_, h2⟩
      exact ⟨hg, by rw [← key]; exact h2⟩
    · rintro ⟨_, h2⟩
      exact ⟨mul_mem hg hh, by rw [key]; exact h2⟩
  · constructor
    · rintro ⟨_, h2⟩
      exact ⟨hg, by rw [← key]; exact h2⟩
    · rintro ⟨_, h2⟩
      exact ⟨mul_mem hg hh, by rw [key]; exact h2⟩

theorem gl_trivOn_of_le_centralizer {K : Subgroup G} {g : G} (h : K ≤ Cs g) : TrivOn K g := by
  have hc : ∀ k ∈ K, g * k * g⁻¹ = k := fun k hk => by
    have := Subgroup.mem_centralizer_iff.1 (h hk) g (by simp)
    rw [mul_inv_eq_iff_eq_mul]; exact this
  rw [gl_trivOn_iff]
  refine ⟨?_, fun k hk => by rw [hc k hk]; simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk; rw [hc k hk]; exact hk
  · intro hk
    have h1 := hc _ hk
    have h2 : g * k * g⁻¹ = k := by
      have h3 := congrArg (fun x => g⁻¹ * x * g) h1
      have e1 : g⁻¹ * (g * (g * k * g⁻¹) * g⁻¹) * g = g * k * g⁻¹ := by group
      have e2 : g⁻¹ * (g * k * g⁻¹) * g = k := by group
      rw [e1, e2] at h3
      exact h3
    rwa [h2] at hk

theorem gl_trivOn_restrict {K J : Subgroup G} {g : G} (hJK : J ≤ K)
    (hgJ : g ∈ Subgroup.normalizer (J : Set G)) (h : TrivOn K g) : TrivOn J g := by
  rw [gl_trivOn_iff] at h ⊢
  refine ⟨hgJ, fun k hk => ?_⟩
  set M : Subgroup ↥J := (GLAPPrimeCore 3 ↥K).comap (Subgroup.inclusion hJK) with hM
  have hMn : M.Normal := Subgroup.Normal.comap inferInstance _
  have hcard : Nat.Coprime 3 (Nat.card M) := by
    have h1 : (M.map (Subgroup.inclusion hJK)) ≤ GLAPPrimeCore 3 ↥K :=
      Subgroup.map_comap_le _ _
    have h2 : Nat.card (M.map (Subgroup.inclusion hJK)) = Nat.card M :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hJK)
    have h3 := Subgroup.card_dvd_of_le h1
    rw [h2] at h3
    exact (coprime_card_gLAPPrimeCore_aux 3 ↥K).coprime_dvd_right h3
  have hle : M ≤ GLAPPrimeCore 3 ↥J := le_sSup ⟨hMn, hcard⟩
  have hc : g * k * g⁻¹ * k⁻¹ ∈ J := by
    have := Subgroup.mem_normalizer_iff.1 hgJ k
    exact mul_mem (this.1 hk) (inv_mem hk)
  have hk1 := h.2 k (hJK hk)
  unfold GLAPPrimeCoreOf at hk1 ⊢
  rw [Subgroup.mem_map] at hk1 ⊢
  refine ⟨⟨_, hc⟩, hle ?_, rfl⟩
  show Subgroup.inclusion hJK ⟨_, hc⟩ ∈ GLAPPrimeCore 3 ↥K
  obtain ⟨z, hz, hzeq⟩ := hk1
  have : Subgroup.inclusion hJK ⟨_, hc⟩ = z := by
    apply Subtype.ext; exact hzeq.symm
  rw [this]; exact hz

end Glue

@[expose] def IsInnDiagPSL (n : ℕ) {Y : Type} [Group Y] {F : Type} [Field F]
    (e : Y ≃* StatedProj (StatedSL n F)) (α : MulAut Y) : Prop :=
  ∃ g : GL (Fin n) F, ∀ A A' : ↥(StatedSL n F),
    (A' : GL (Fin n) F) = g * (A : GL (Fin n) F) * g⁻¹ →
      e (α (e.symm (QuotientGroup.mk A))) = QuotientGroup.mk A'

@[expose] def IsInnDiagPSU (n r : ℕ) {Y : Type} [Group Y] {F : Type} [Field F]
    (e : Y ≃* StatedProj (StatedSU n r F)) (α : MulAut Y) : Prop :=
  ∃ g : GL (Fin n) F,
    (((g : Matrix (Fin n) (Fin n) F).map (· ^ r))ᵀ * (g : Matrix (Fin n) (Fin n) F) = 1) ∧
    ∀ A A' : ↥(StatedSU n r F),
      (A' : GL (Fin n) F) = g * (A : GL (Fin n) F) * g⁻¹ →
        e (α (e.symm (QuotientGroup.mk A))) = QuotientGroup.mk A'

@[expose] def LinkInndiag (V : InndiagVocab) : Prop :=
  (∀ (n : ℕ), (n = 2 ∨ n = 3) → ∀ (Y : Type) [Group Y] (F : Type) [Field F]
    (e : Y ≃* StatedProj (StatedSL n F)) (α : MulAut Y),
      α ∈ V.innDiag Y ↔ IsInnDiagPSL n e α) ∧
  (∀ (r : ℕ) (Y : Type) [Group Y] (F : Type) [Field F]
    (e : Y ≃* StatedProj (StatedSU 3 r F)) (α : MulAut Y),
      α ∈ V.innDiag Y ↔ IsInnDiagPSU 3 r e α)

@[expose] def InputL3T : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G),
    CFSG.Open.IsQuasisimple (barOf 3 K) → g ^ 3 = 1 → TrivOn K g →
      GLAPComponent 3 (K ⊓ Cs g) (CLay K g) ∧ K ≤ CLay K g ⊔ GLAPPrimeCoreOf 3 K

@[expose] def InputL3fix (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G) (r : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsL3Raw r (barOf 3 K) → g ^ 3 = 1 →
    InducesFieldAut 3 K g → ¬ TrivOn K g →
      ¬ IndInn V K g ∧ ∃ r0 : ℕ, r = r0 ^ 3 ∧
        ((GLAPComponent 3 (K ⊓ Cs g) (CLay K g) ∧ IsL3Raw r0 (barOf 3 (CLay K g)) ∧
          (IsPSLn 3 r (barOf 3 K) → IsPSLn 3 r0 (barOf 3 (CLay K g))) ∧
          (IsPSUn 3 r (barOf 3 K) → IsPSUn 3 r0 (barOf 3 (CLay K g)))) ∨
        (CLay K g = ⊥ ∧ r = 8 ∧ IsPSUn 3 8 (barOf 3 K)))

@[expose] def InputL3inn (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G) (r : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsL3Eps r (barOf 3 K) → g ^ 3 = 1 →
    IndInn V K g → ¬ TrivOn K g →
      ¬ InducesFieldAut 3 K g ∧
        (CLay K g = ⊥ ∨ (GLAPComponent 3 (K ⊓ Cs g) (CLay K g) ∧ IsTypeL2 r (barOf 3 (CLay K g))))

@[expose] def InputL3y0 (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G) (r : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsL3Eps r (barOf 3 K) → r ≠ 8 → g ^ 3 = 1 →
    InducesFieldAut 3 K g → ¬ TrivOn K g →
      ∃ y₀ ∈ K ⊓ Cs g, y₀ ^ 3 = 1 ∧ IndInn V K y₀ ∧ ¬ TrivOn K y₀ ∧ ∃ r0 : ℕ, r = r0 ^ 3 ∧
        GLAPComponent 3 (K ⊓ Cs g ⊓ Cs y₀) (GLAPLayer 3 (K ⊓ Cs g ⊓ Cs y₀)) ∧
        IsTypeL2 r0 (barOf 3 (GLAPLayer 3 (K ⊓ Cs g ⊓ Cs y₀)))

@[expose] def InputL3out (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g h : G) (r : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsL3Raw r (barOf 3 K) → g ∈ Subgroup.normalizer (K : Set G) →
    h ∈ Subgroup.normalizer (K : Set G) → g ^ 3 = 1 → h ^ 3 = 1 → g * h = h * g →
      IndInn V K g ∨ ∃ j : ℕ, IndInn V K (h * g ^ j)

@[expose] def InputL3fld (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G) (r : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsL3Raw r (barOf 3 K) → g ∈ Subgroup.normalizer (K : Set G) →
    g ^ 3 = 1 → ¬ IndInn V K g → InducesFieldAut 3 K g

@[expose] def InputL3rk : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (r : ℕ), IsL3Eps r Y →
    ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E ≤ 9

@[expose] def InputL3iso : Prop :=
  ∀ (Y : Type) [Group Y] (r r' : ℕ), IsL3Raw r Y → IsL3Raw r' Y →
    r = r' ∧ ¬ (IsPSLn 3 r Y ∧ IsPSUn 3 r' Y)

@[expose] def InputL3size : Prop :=
  ∀ (Y Y' : Type) [Group Y] [Group Y'] [Finite Y] [Finite Y'] (r : ℕ),
    IsL3Raw r Y → IsL3Raw (r ^ 3) Y' → Nat.card Y < Nat.card Y'

@[expose] def InputL3L2 : Prop :=
  ∀ (Y : Type) [Group Y] (r r' : ℕ), IsL3Eps r Y → IsTypeL2 r' Y → False

@[expose] def InputL2fld : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g : G) (s r0 : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsTypeL2 s (barOf 3 K) → g ∈ Subgroup.normalizer (K : Set G) →
    g ^ 3 = 1 → ∀ J : Subgroup G, GLAPComponent 3 (K ⊓ Cs g) J → IsTypeL2 r0 (barOf 3 J) →
      (TrivOn K g ∧ (s = r0 ∨ ((s = 4 ∨ s = 5) ∧ (r0 = 4 ∨ r0 = 5)))) ∨
      (¬ TrivOn K g ∧ InducesFieldAutN 2 K g ∧
        (s = r0 ^ 3 ∨ ((r0 = 4 ∨ r0 = 5) ∧ (s = 64 ∨ s = 125))))

@[expose] def InputL2exp (V : InndiagVocab) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G) (g h : G) (s r0 : ℕ),
    CFSG.Open.IsQuasisimple (barOf 3 K) → IsTypeL2 s (barOf 3 K) → g ∈ Subgroup.normalizer (K : Set G) →
    h ∈ Subgroup.normalizer (K : Set G) → g ^ 3 = 1 → h ^ 3 = 1 → g * h = h * g → ¬ IndInn V K g →
      ∀ J : Subgroup G, GLAPComponent 3 (K ⊓ Cs g ⊓ Cs h) J → IsTypeL2 r0 (barOf 3 J) →
        (s = r0 ^ 3 ∨ ((r0 = 4 ∨ r0 = 5) ∧ (s = 64 ∨ s = 125)))

@[expose] def InputFixComp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKProper G → ∀ (X : Subgroup G)
    (𝒞 : Set (Subgroup G)) (E : Subgroup G) (a : G) (N : Subgroup G),
    (∀ C ∈ 𝒞, GLAPComponent 3 X C) → E ≤ X → IsElemAbelian 3 E →
    (∀ C ∈ 𝒞, ∀ e ∈ E, GLBConj e C ∈ 𝒞) → (∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ E, GLBConj e C = C') →
    a ∈ E → GLAPComponent 3 (X ⊓ Cs a) N → N ≤ (⨆ C ∈ 𝒞, C) →
    E ≤ Subgroup.normalizer (N : Set G) →
      ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ k : ℕ, GLBConj (a ^ k) C = C'

structure Inputs (V : InndiagVocab) : Prop where
  i181 : Input18_1
  i182 : Input18_2
  i1823 : (∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
      CFSG.Open.IsKProper G → ∀ x y : G, orderOf x = 3 → orderOf y = 3 → x * y = y * x → ∀ J :
      Subgroup G, GLAPComponent 3 (GLAPLayer 3 (Cs x) ⊓ Cs y) J → GLAPComponent 3 (GLAPLayer 3 (ncl
      (GLAPLayer 3 (Cs y)) J ⊓ Cs x)) J ∧ ∃ hx : x ∈ Cs y, IsComponentOf (barX 3 (Cs y) J) (barX 3
      (Cs y) (ncl (GLAPLayer 3 (Cs y)) J) ⊓ Subgroup.centralizer ({(QuotientGroup.mk ⟨x, hx⟩ : ↥(Cs
      y) ⧸ GLAPPrimeCore 3 ↥(Cs y))} : Set (↥(Cs y) ⧸ GLAPPrimeCore 3 ↥(Cs y)))))
  i1834 : Input18_3_4G
  i25 : Input2_5
  i92 : Input9_2_3 V
  i1431 : Input14_31_4 V
  l3T : InputL3T
  l3fix : InputL3fix V
  l3inn : InputL3inn V
  l3y0 : InputL3y0 V
  l3out : InputL3out V
  l3fld : InputL3fld V
  l3rk : InputL3rk
  l3iso : InputL3iso
  l3size : InputL3size
  l3l2 : InputL3L2
  l2fld : InputL2fld
  l2exp : InputL2exp V
  fixcomp : InputFixComp
  zk : Gap515CentreK


noncomputable abbrev JOf (L A : Subgroup G) : Subgroup G := GLAPLayer 3 (L ⊓ CD A)

noncomputable def Iof (y : G) (J0 D : Subgroup G) : Subgroup G :=
  ncl (GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ D))) J0

structure Ctx (B : Subgroup G) (b : G) (L A : Subgroup G) (x : G) : Prop where
  stand : ∃ m, GLStanding G m 3
  c4 : GLCaseFour G 3
  b1 : IsBOneMax 3 B
  hw : IsExtremalWitness B b L A
  xA : x ∈ A
  x1 : x ≠ 1
  xb : x ∉ Subgroup.zpowers b
  ncov : ¬ KOf L A x ≤ JOf L A ⊔ GLAPPrimeCoreOf 3 (KOf L A x)

theorem ctx_kproper {B : Subgroup G} {b : G} {L A : Subgroup G} {x : G} (c : Ctx B b L A x) :
    CFSG.Open.IsKProper G := by
  obtain ⟨m, hS⟩ := c.stand
  exact hS.kProper

theorem ctx_simple {B : Subgroup G} {b : G} {L A : Subgroup G} {x : G} (c : Ctx B b L A x) :
    IsSimpleGroup G := by
  obtain ⟨m, hS⟩ := c.stand
  exact hS.simple

theorem ctx_nonab {B : Subgroup G} {b : G} {L A : Subgroup G} {x : G} (c : Ctx B b L A x) :
    ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨m, hS⟩ := c.stand
  exact hS.nonabelian

variable {B : Subgroup G} {b : G} {L A : Subgroup G} {x : G}

structure S1Facts (B : Subgroup G) (b : G) (L A : Subgroup G) (x : G) : Prop where
  compK : GLAPComponent 3 (Cs x) (KOf L A x)
  bK : b ∈ Subgroup.normalizer (KOf L A x : Set G)
  fldK : InducesFieldAut 3 (KOf L A x) b
  compL : GLAPComponent 3 (Cs b) L
  fldLx : InducesFieldAut 3 L x
  quasiL : CFSG.Open.IsQuasisimple (barOf 3 L)
  JK : JOf L A ≤ KOf L A x
  JL : JOf L A ≤ L
  inf : L ⊓ CD A = L ⊓ Cs x
  card_le : Nat.card (barOf 3 (KOf L A x)) ≤ Nat.card (barOf 3 L)
  ext : ∃ q : ℕ, IsL3Eps q (barOf 3 L) ∧ (q % 3 = 2 → q ≠ 8)
  Aeq : Subgroup.zpowers x ⊔ Subgroup.zpowers b = A
  Acard : Nat.card A = 9
  Ael : IsElemAbelian 3 A
  hx3 : x ^ 3 = 1
  hb3 : b ^ 3 = 1
  hxb : x * b = b * x
  b1 : b ≠ 1
  bA : b ∈ A
  Kb : KOf L A b = L
  fldKa : ∀ a ∈ A, a ∉ Subgroup.zpowers b → a ≠ 1 → GLAPComponent 3 (Cs a) (KOf L A a) ∧
    InducesFieldAut 3 (KOf L A a) b ∧ b ∈ Subgroup.normalizer (KOf L A a : Set G)
  Fne : ∃ F : Subgroup G, F ≤ JOf L A ∧ IsPGroup 3 F ∧ F ≠ ⊥

theorem p1_pu (c : Ctx B b L A x) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hab : a ∉ Subgroup.zpowers b) :
    GLAPComponent 3 (Cs a) (KOf L A a) ∧ InducesFieldAut 3 (KOf L A a) b ∧
      b ∈ Subgroup.normalizer (KOf L A a : Set G) ∧
      Nat.card (barOf 3 (KOf L A a)) ≤ Nat.card (barOf 3 L) := by
  have hw := c.hw
  have hpu := kOf_eq_pumpUp hw haA hab
  obtain ⟨-, -, -, -, -, ⟨-, hA, -, hfld, -, -⟩, hx3⟩ := hw
  obtain ⟨h1, h2, h3⟩ := hx3 a (hA.1 haA) ha1 (hfld a haA)
  rw [← hpu] at h1 h2 h3
  exact ⟨h1, h2, h2.1, h3⟩

theorem s1_basic (c : Ctx B b L A x) : S1Facts B b L A x := by
  have hw := c.hw
  have hBe : IsElemAbelian 3 B := c.b1.1.1
  obtain ⟨hbB, hb1, hLcomp, -, hext, ⟨hFcard, hA, hbA, hfld, hFJ, -⟩, -⟩ := c.hw
  have hAeq := A_eq_sup hA.2.1 (by simpa using hA.2.2) hbA c.xA hb1 c.xb
  have hJL : JOf L A ≤ L := (glaPLayer_le' 3 _).trans inf_le_left
  have hF3 : IsPGroup 3 ↥(B ⊓ L) := Lemma514Ns.isPGroup_of_isElemAbelian' (isElemAbelian_inf_left' hBe L)
  have hFne : B ⊓ L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hFcard
    omega
  obtain ⟨hcK, hfK, hbK, hcard⟩ := p1_pu c c.xA c.x1 c.xb
  refine ⟨hcK, hbK, hfK, hLcomp, hfld x c.xA, gl_quasi_barOf hLcomp, le_kOf L A x, hJL,
    inf_centralizer_eq_of_A hAeq c.xA hLcomp.1, hcard, ?_, hAeq, by simpa using hA.2.2, hA.2.1,
    hA.2.1.2 x c.xA, hA.2.1.2 b hbA, comm_of_isElemAbelian' hA.2.1 c.xA hbA, hb1, hbA, ?_, ?_, ?_⟩
  · rcases hext with ⟨K, _, _, h, ⟨f⟩⟩ | ⟨K, _, _, q, hK, hq, hq8, ⟨f⟩⟩
    · exact ⟨Nat.card K, Or.inl ⟨h, K, inferInstance, inferInstance, rfl, ⟨f⟩⟩, fun h2 => by omega⟩
    · exact ⟨q, Or.inr ⟨hq, K, inferInstance, inferInstance, hK, ⟨f⟩⟩, fun _ => hq8⟩
  · unfold KOf
    exact layer_closure_eq hLcomp hJL hFJ hF3 hFne (center_barX_of_isExtremalType hLcomp hext)
  · intro a haA hab ha1
    obtain ⟨h1, h2, h3, -⟩ := p1_pu c haA ha1 hab
    exact ⟨h1, h2, h3⟩
  · exact ⟨B ⊓ L, hFJ, hF3, hFne⟩

structure S2Facts (V : InndiagVocab) (B : Subgroup G) (b : G) (L A : Subgroup G) (x : G) : Prop where
  J1 : GLAPComponent 3 (L ⊓ Cs x) (JOf L A)
  JA : GLAPComponent 3 (CD A) (JOf L A)
  Jxb : GLAPComponent 3 (GLAPLayer 3 (Cs x) ⊓ Cs b) (JOf L A)
  Jbx : GLAPComponent 3 (GLAPLayer 3 (Cs b) ⊓ Cs x) (JOf L A)
  Jne : JOf L A ≠ ⊥

omit [Finite G] in
theorem p2_layer_le (X : Subgroup G) : GLAPLayer 3 X ≤ X := sSup_le fun _ hL => hL.1

omit [Finite G] in
theorem p2_CD_zpowers (g : G) : CD (Subgroup.zpowers g) = Cs g := by
  ext y
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Set.mem_singleton_iff,
    forall_eq]
  constructor
  · intro h
    exact h g (Subgroup.mem_zpowers g)
  · intro h z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute g y := h
    exact (hc.zpow_left n).eq

theorem p2_CD_A (s1 : S1Facts B b L A x) : CD A = Cs x ⊓ Cs b := by
  rw [← s1.Aeq, ← p2_CD_zpowers x, ← p2_CD_zpowers b]
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨fun z hz => h z (Subgroup.mem_sup_left hz), fun z hz => h z (Subgroup.mem_sup_right hz)⟩
  · rintro ⟨h1, h2⟩ z hz
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({y} : Set G) := by
      refine sup_le (fun u hu => ?_) (fun v hv => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact h1 u hu
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact h2 v hv
    have := hle hz
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this

omit [Finite G] in
theorem p2_JOf_eq (s1 : S1Facts B b L A x) : JOf L A = CLay L x := by
  show GLAPLayer 3 (L ⊓ CD A) = GLAPLayer 3 (L ⊓ Cs x)
  rw [s1.inf]

theorem p2_J1 {V : InndiagVocab} (hi : Inputs V) (s1 : S1Facts B b L A x) :
    GLAPComponent 3 (L ⊓ Cs x) (JOf L A) := by
  rw [p2_JOf_eq s1]
  by_cases hT : TrivOn L x
  · exact (hi.l3T G L x s1.quasiL s1.hx3 hT).1
  · obtain ⟨q, hq, hq8⟩ := s1.ext
    have hraw : IsL3Raw q (barOf 3 L) := by
      rcases hq with ⟨_, h⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨_, r0, hr, h | h⟩ := hi.l3fix G L x q s1.quasiL hraw s1.hx3 s1.fldLx hT
    · exact h.1
    · exfalso
      obtain ⟨_, h8, _⟩ := h
      subst h8
      rcases hq with ⟨h3, _⟩ | ⟨h3, _⟩
      · omega
      · exact hq8 h3 rfl

omit [Finite G] in
theorem p2_pgroup {g : G} (h : g ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; simp)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; simp)

theorem s2_J {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x) :
    S2Facts V B b L A x := by
  have hK := ctx_kproper c
  have hJ1 := p2_J1 hi s1
  have hCD := p2_CD_A s1
  have hxP : IsPGroup 3 (Subgroup.zpowers x) := p2_pgroup s1.hx3
  have hbP : IsPGroup 3 (Subgroup.zpowers b) := p2_pgroup s1.hb3
  have hcomm : ∀ d ∈ Subgroup.zpowers x, ∀ e ∈ Subgroup.zpowers b, d * e = e * d := by
    intro d hd e he
    have : Commute x b := s1.hxb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact ((this.zpow_zpow m n).eq)
  have hJA : GLAPComponent 3 (CD A) (JOf L A) := by
    refine gl_comp_lift ?_ hJ1
    have := gl_isSubnormal_inf (Cs x) s1.compL.2.1
    rw [hCD, inf_comm (Cs x) (Cs b)]
    exact this
  have hJlay : JOf L A ≤ GLAPLayer 3 (CD A) := le_sSup hJA
  have hCDle : CD A ≤ Cs x ⊓ Cs b := hCD.le
  have h1 := hi.i182 G hK (Subgroup.zpowers x) (Subgroup.zpowers b) hxP hbP hcomm
  rw [p2_CD_zpowers, p2_CD_zpowers, ← hCD] at h1
  have h2 := hi.i182 G hK (Subgroup.zpowers b) (Subgroup.zpowers x) hbP hxP
    (fun d hd e he => (hcomm e he d hd).symm)
  rw [p2_CD_zpowers, p2_CD_zpowers, inf_comm (Cs b) (Cs x), ← hCD] at h2
  refine ⟨hJ1, hJA, ?_, ?_, ?_⟩
  · refine gl_comp_restrict hJA ?_ ?_
    · rw [← h1] at hJlay
      exact hJlay.trans (p2_layer_le _)
    · exact (inf_le_inf (p2_layer_le _) le_rfl).trans hCD.ge
  · refine gl_comp_restrict hJA ?_ ?_
    · rw [← h2] at hJlay
      exact hJlay.trans (p2_layer_le _)
    · exact (inf_le_inf (p2_layer_le _) le_rfl).trans (by rw [hCD, inf_comm])
  · obtain ⟨F, hF, _, hF0⟩ := s1.Fne
    intro h
    rw [h] at hF
    exact hF0 (le_bot_iff.mp hF)

theorem k_type {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    (s2 : S2Facts V B b L A x) (hb : ¬ TrivOn (KOf L A x) b) :
    ∃ r' r0' : ℕ, r' = r0' ^ 3 ∧ IsL3Raw r' (barOf 3 (KOf L A x)) ∧
      JOf L A = CLay (KOf L A x) b ∧ IsL3Raw r0' (barOf 3 (JOf L A)) ∧ ¬ IndInn V (KOf L A x) b ∧
      (IsPSLn 3 r' (barOf 3 (KOf L A x)) → IsPSLn 3 r0' (barOf 3 (JOf L A))) ∧
      (IsPSUn 3 r' (barOf 3 (KOf L A x)) → IsPSUn 3 r0' (barOf 3 (JOf L A))) := by
  obtain ⟨m, hS⟩ := c.stand
  obtain ⟨e⟩ := gl_barOf_equiv s1.compK
  have hZ : Subgroup.center ↥(barX 3 (Cs x) (KOf L A x)) = ⊥ :=
    hi.zk G m hS c.c4 B c.b1 b L A c.hw x c.xA c.x1 c.xb
  have hZ' : Subgroup.center (barOf 3 (KOf L A x)) = ⊥ := center_eq_bot_of_mulEquiv' e hZ
  let E : (barOf 3 (KOf L A x) ⧸ Subgroup.center (barOf 3 (KOf L A x))) ≃*
      barOf 3 (KOf L A x) :=
    (QuotientGroup.quotientMulEquivOfEq hZ').trans QuotientGroup.quotientBot
  have hraw : ∃ r', IsL3Raw r' (barOf 3 (KOf L A x)) := by
    obtain ⟨hN, hfa⟩ := s1.fldK
    rcases hfa with h1 | ⟨F, iF, fF, θ, σ, φ, γ, _⟩ | ⟨F, iF, fF, q, θ, σ, φ, γ, hq, _⟩
    · exact absurd ⟨hN, h1⟩ hb
    · exact ⟨Nat.card F, Or.inl ⟨F, iF, fF, rfl, ⟨E.symm.trans θ⟩⟩⟩
    · exact ⟨q, Or.inr ⟨F, iF, fF, hq, ⟨E.symm.trans θ⟩⟩⟩
  obtain ⟨r', hr'⟩ := hraw
  have hb3 : orderOf b = 3 := orderOf_eq_prime s1.hb3 s1.b1
  have hx3 : orderOf x = 3 := orderOf_eq_prime s1.hx3 (c.x1)
  obtain ⟨hJc, -⟩ := (@hi.i1823 G _ _ (ctx_simple c) (ctx_nonab c) (ctx_kproper c)) b x hb3 hx3
    s1.hxb.symm (JOf L A) s2.Jbx
  have hKdef : KOf L A x = ncl (GLAPLayer 3 (Cs x)) (JOf L A) := rfl
  rw [← hKdef] at hJc
  have hJc' : GLAPComponent 3 (KOf L A x ⊓ Cs b) (JOf L A) := gl_comp_iff_layer.2 hJc
  have hle : JOf L A ≤ CLay (KOf L A x) b :=
    le_sSup (show JOf L A ∈ {L' | GLAPComponent 3 (KOf L A x ⊓ Cs b) L'} from hJc')
  obtain ⟨hnInn, r0, hr0, hrest⟩ := hi.l3fix G (KOf L A x) b r' (gl_quasi_barOf s1.compK) hr'
    s1.hb3 s1.fldK hb
  rcases hrest with ⟨hcomp, hraw0, hL, hU⟩ | ⟨hbot, -, -⟩
  · have hJeq : JOf L A = CLay (KOf L A x) b := gl_comp_eq_of_le hcomp hJc' hle
    refine ⟨r', r0, hr0, hr', hJeq, ?_, hnInn, ?_, ?_⟩
    · rw [hJeq]; exact hraw0
    · intro h; rw [hJeq]; exact hL h
    · intro h; rw [hJeq]; exact hU h
  · exact absurd (le_bot_iff.1 (hbot ▸ hle)) s2.Jne

theorem p3_barX_le_cent {X K : Subgroup G} {g : G} (hsn : IsSubnormal K X) (hg : g ∈ X)
    (hT : TrivOn K g) :
    barX 3 X K ≤ Subgroup.centralizer
      ({(QuotientGroup.mk ⟨g, hg⟩ : ↥X ⧸ GLAPPrimeCore 3 ↥X)} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  intro z hz
  obtain ⟨k, hk, rfl⟩ := (mem_barX_iff' 3 X K z).1 hz
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  obtain ⟨_, hc⟩ := gl_trivOn_iff.1 hT
  have h1 := hc (k : G) hk
  have h2 := glaPPrimeCoreOf_le_of_isSubnormal 3 hsn h1
  obtain ⟨y, hy, hyc⟩ := h2
  have hyeq : y = ⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹ * k⁻¹ := Subtype.ext (by simpa using hyc)
  have h3 : (QuotientGroup.mk y : ↥X ⧸ GLAPPrimeCore 3 ↥X) = 1 :=
    (QuotientGroup.eq_one_iff y).2 hy
  rw [hyeq] at h3
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h3
  exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h3)

theorem p3_raw_of_equiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y') {r : ℕ}
    (h : IsL3Raw r Y) : IsL3Raw r Y' := by
  rcases h with ⟨F, hF, hfin, hc, ⟨e'⟩⟩ | ⟨F, hF, hfin, hc, ⟨e'⟩⟩
  · exact Or.inl ⟨F, hF, hfin, hc, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨F, hF, hfin, hc, ⟨e.symm.trans e'⟩⟩

theorem p3_raw_of_eps {Y : Type*} [Group Y] {r : ℕ} (h : IsL3Eps r Y) : IsL3Raw r Y := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inl h
  · exact Or.inr h

theorem s3_nontriv {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    (s2 : S2Facts V B b L A x) : ¬ TrivOn (KOf L A x) b ∧ ¬ TrivOn L x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho_b : orderOf b = 3 := orderOf_eq_prime s1.hb3 s1.b1
  have ho_x : orderOf x = 3 := orderOf_eq_prime s1.hx3 c.x1
  have ha : ¬ TrivOn (KOf L A x) b := by
    intro hT
    obtain ⟨_, hx, hcomp⟩ := (@hi.i1823 G _ _ (ctx_simple c) (ctx_nonab c) (ctx_kproper c)) b x
      ho_b ho_x s1.hxb.symm (JOf L A) s2.Jbx
    have hle := p3_barX_le_cent s1.compK.2.1 hx hT
    have hinf : barX 3 (Cs x) (ncl (GLAPLayer 3 (Cs x)) (JOf L A)) ⊓ Subgroup.centralizer
        ({(QuotientGroup.mk ⟨b, hx⟩ : ↥(Cs x) ⧸ GLAPPrimeCore 3 ↥(Cs x))} :
          Set (↥(Cs x) ⧸ GLAPPrimeCore 3 ↥(Cs x))) = barX 3 (Cs x) (KOf L A x) :=
      inf_eq_left.2 hle
    rw [hinf] at hcomp
    have heq := gl_barX_eq_of_isComponentOf s1.compK hcomp
    exact c.ncov (gl_cover_of_barX_eq s1.compK s1.JK heq)
  refine ⟨ha, ?_⟩
  intro hT
  obtain ⟨r', r0', h3, hK, hJeq, hJraw, -, -, -⟩ := k_type hi c s1 s2 ha
  obtain ⟨_, hx, hcomp⟩ := (@hi.i1823 G _ _ (ctx_simple c) (ctx_nonab c) (ctx_kproper c)) x b
    ho_x ho_b s1.hxb (JOf L A) s2.Jxb
  have hncl : ncl (GLAPLayer 3 (Cs b)) (JOf L A) = L := s1.Kb
  have hle := p3_barX_le_cent s1.compL.2.1 hx hT
  have hinf : barX 3 (Cs b) (ncl (GLAPLayer 3 (Cs b)) (JOf L A)) ⊓ Subgroup.centralizer
      ({(QuotientGroup.mk ⟨x, hx⟩ : ↥(Cs b) ⧸ GLAPPrimeCore 3 ↥(Cs b))} :
        Set (↥(Cs b) ⧸ GLAPPrimeCore 3 ↥(Cs b))) = barX 3 (Cs b) L := by
    rw [hncl]; exact inf_eq_left.2 hle
  rw [hinf] at hcomp
  have heq := gl_barX_eq_of_isComponentOf s1.compL hcomp
  obtain ⟨F, hFJ, hF3, hF⟩ := s1.Fne
  have hZ := center_barX_of_isExtremalType s1.compL c.hw.2.2.2.2.1
  have hq := gl_quasi_barX s1.compL
  have hJX : JOf L A ≤ Cs b := s1.JL.trans s1.compL.1
  obtain ⟨e1⟩ := gl_barOf_equiv_of_centreless hFJ hF3 hF hJX (heq ▸ hq) (heq ▸ hZ)
  obtain ⟨e2⟩ := gl_barOf_equiv s1.compL
  let e3 : barOf 3 (JOf L A) ≃* barOf 3 L :=
    (e1.trans (MulEquiv.subgroupCongr heq)).trans e2.symm
  obtain ⟨q, hqL, -⟩ := s1.ext
  have hJq : IsL3Raw q (barOf 3 (JOf L A)) := p3_raw_of_equiv e3.symm (p3_raw_of_eps hqL)
  have hr : r0' = q := (hi.l3iso _ r0' q hJraw hJq).1
  subst hr
  rw [h3] at hK
  exact absurd (hi.l3size (barOf 3 L) (barOf 3 (KOf L A x)) r0' (p3_raw_of_eps hqL) hK)
    (not_lt.2 s1.card_le)

structure S4Facts (V : InndiagVocab) (L A : Subgroup G) (b x : G) (q q0 : ℕ) : Prop where
  q3 : q = q0 ^ 3
  tL : IsL3Eps q (barOf 3 L)
  q8 : q % 3 = 2 → q ≠ 8
  tJ : IsL3Eps q0 (barOf 3 (JOf L A))
  tK : IsL3Eps q (barOf 3 (KOf L A x))
  quasiK : CFSG.Open.IsQuasisimple (barOf 3 (KOf L A x))
  JeqK : JOf L A = CLay (KOf L A x) b
  nxL : ¬ IndInn V L x
  nbK : ¬ IndInn V (KOf L A x) b

theorem p4_cube_mod (r : ℕ) : r ^ 3 % 3 = r % 3 := by
  have h : r % 3 = 0 ∨ r % 3 = 1 ∨ r % 3 = 2 := by omega
  rcases h with h | h | h <;> simp [Nat.pow_mod, h]

theorem s4_types {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    (s2 : S2Facts V B b L A x) (s3 : ¬ TrivOn (KOf L A x) b ∧ ¬ TrivOn L x) :
    ∃ q q0 : ℕ, S4Facts V L A b x q q0 := by
  obtain ⟨q, tL, q8⟩ := s1.ext
  have hmod : q % 3 = 1 ∨ q % 3 = 2 := by
    rcases tL with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hraw : IsL3Raw q (barOf 3 L) := by
    rcases tL with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨nxL, r0, hq, hcase⟩ :=
    hi.l3fix G L x q s1.quasiL hraw s1.hx3 s1.fldLx s3.2
  rcases hcase with ⟨_, hr0raw, hpL, hpU⟩ | ⟨_, h8, _⟩
  swap
  · exfalso
    apply q8 _ h8
    omega
  have hCL : CLay L x = JOf L A := by
    show GLAPLayer 3 (L ⊓ Cs x) = GLAPLayer 3 (L ⊓ CD A)
    rw [s1.inf]
  have tr : ∀ P : Subgroup G → Prop, P (CLay L x) → P (JOf L A) := fun P h => hCL ▸ h
  replace hr0raw : IsL3Raw r0 (barOf 3 (JOf L A)) := tr (fun K => IsL3Raw r0 (barOf 3 K)) hr0raw
  replace hpL : IsPSLn 3 q (barOf 3 L) → IsPSLn 3 r0 (barOf 3 (JOf L A)) := fun h =>
    tr (fun K => IsPSLn 3 r0 (barOf 3 K)) (hpL h)
  replace hpU : IsPSUn 3 q (barOf 3 L) → IsPSUn 3 r0 (barOf 3 (JOf L A)) := fun h =>
    tr (fun K => IsPSUn 3 r0 (barOf 3 K)) (hpU h)
  have hr0mod : r0 % 3 = q % 3 := by rw [hq]; exact (p4_cube_mod r0).symm
  have tJ : IsL3Eps r0 (barOf 3 (JOf L A)) := by
    rcases tL with ⟨h1, hL⟩ | ⟨h1, hL⟩
    · exact Or.inl ⟨by omega, hpL hL⟩
    · exact Or.inr ⟨by omega, hpU hL⟩
  have hrawJ : IsL3Raw r0 (barOf 3 (JOf L A)) := by
    rcases tJ with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨r', r0', hr', rawK, JeqK, rawJ', nbK, presL, presU⟩ :=
    k_type hi c s1 s2 s3.1
  obtain ⟨he1, hn1⟩ := hi.l3iso (barOf 3 (JOf L A)) r0 r0' hrawJ rawJ'
  obtain ⟨he2, hn2⟩ := hi.l3iso (barOf 3 (JOf L A)) r0' r0 rawJ' hrawJ
  subst he1
  have hr'q : r' = q := by rw [hr', hq]
  have tK : IsL3Eps q (barOf 3 (KOf L A x)) := by
    rw [hr'q] at rawK presL presU
    rcases tJ with ⟨h1, hJ⟩ | ⟨h1, hJ⟩
    · refine Or.inl ⟨by omega, ?_⟩
      rcases rawK with h | h
      · exact h
      · exact absurd ⟨hJ, presU h⟩ hn1
    · refine Or.inr ⟨by omega, ?_⟩
      rcases rawK with h | h
      · exact absurd ⟨presL h, hJ⟩ hn2
      · exact h
  exact ⟨q, r0, ⟨hq, tL, q8, tJ, tK, gl_quasi_barOf s1.compK, JeqK, nxL, nbK⟩⟩

theorem p4a_psln_equiv {n r : ℕ} {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsPSLn n r Y) : IsPSLn n r Y' := by
  obtain ⟨F, _, _, hc, ⟨f⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, ⟨e.symm.trans f⟩⟩

theorem p4a_psun_equiv {n r : ℕ} {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsPSUn n r Y) : IsPSUn n r Y' := by
  obtain ⟨F, _, _, hc, ⟨f⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hc, ⟨e.symm.trans f⟩⟩

theorem p4a_l3eps_equiv {r : ℕ} {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsL3Eps r Y) : IsL3Eps r Y' :=
  h.imp (fun h => ⟨h.1, p4a_psln_equiv e h.2⟩) (fun h => ⟨h.1, p4a_psun_equiv e h.2⟩)

theorem p4a_raw_of_fieldAut {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥) (α : MulAut Y)
    (hα : α ≠ 1) (h : IsFieldAutThree α) : ∃ r : ℕ, IsL3Raw r Y := by
  let e : Y ≃* (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  rcases h with h | ⟨F, hF, hfin, θ, σ, φ, γ, -, -⟩ | ⟨F, hF, hfin, q, θ, σ, φ, γ, hc, -⟩
  · exact absurd h hα
  · exact ⟨Nat.card F, Or.inl ⟨F, hF, hfin, rfl, ⟨e.trans θ⟩⟩⟩
  · exact ⟨q, Or.inr ⟨F, hF, hfin, hc, ⟨e.trans θ⟩⟩⟩

omit [Finite G] in
theorem p4a_barOf_eq {H H' : Subgroup G} (h : H = H') : Nonempty (barOf 3 H ≃* barOf 3 H') := by
  subst h
  exact ⟨MulEquiv.refl _⟩

omit [Finite G] in
theorem p4a_CD_eq {A : Subgroup G} {a b : G}
    (hAeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = A) (haA : a ∈ A) (hbA : b ∈ A) :
    CD A = Cs a ⊓ Cs b := by
  refine le_antisymm (le_inf (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA))
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbA))) ?_
  intro y hy
  obtain ⟨hya, hyb⟩ := Subgroup.mem_inf.1 hy
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Cs y := by
    refine sup_le ((Subgroup.zpowers_le).2 ?_) ((Subgroup.zpowers_le).2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.1 hya a rfl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.1 hyb b rfl).symm
  rw [hAeq] at hle
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_iff.1 (hle hh) y rfl).symm

theorem p4a_barX_le_centralizer {X K : Subgroup G} {g : G} (hK : GLAPComponent 3 X K)
    (hg : g ∈ X) (h : TrivOn K g) :
    barX 3 X K ≤ Subgroup.centralizer
      ({(QuotientGroup.mk ⟨g, hg⟩ : ↥X ⧸ GLAPPrimeCore 3 ↥X)} :
        Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
  intro z hz
  obtain ⟨k, hkK, rfl⟩ := (mem_barX_iff' 3 X K z).1 hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  have hc := ((gl_trivOn_iff).1 h).2 (k : G) hkK
  have hc' : g * (k : G) * g⁻¹ * (k : G)⁻¹ ∈ GLAPPrimeCoreOf 3 X :=
    glaPPrimeCoreOf_le_of_isSubnormal 3 hK.2.1 hc
  obtain ⟨n, hn, hne⟩ := hc'
  have hne' : (n : G) = g * (k : G) * g⁻¹ * (k : G)⁻¹ := hne
  have hmul : (⟨g, hg⟩ : ↥X) * k = n * (k * ⟨g, hg⟩) := by
    apply Subtype.ext
    show g * (k : G) = (n : G) * ((k : G) * g)
    rw [hne']
    group
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hmul, QuotientGroup.mk_mul,
    (QuotientGroup.eq_one_iff n).2 hn, one_mul]

theorem s4_all {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    (s2 : S2Facts V B b L A x) (s3 : ¬ TrivOn (KOf L A x) b ∧ ¬ TrivOn L x) {q q0 : ℕ}
    (s4 : S4Facts V L A b x q q0) :
    ∀ a ∈ A, a ≠ 1 → GLAPComponent 3 (Cs a) (KOf L A a) ∧
      ∃ r : ℕ, (r = q ∨ r = q0) ∧ IsL3Eps r (barOf 3 (KOf L A a)) ∧
        CFSG.Open.IsQuasisimple (barOf 3 (KOf L A a))  := by
  intro a haA ha1
  have hBe : IsElemAbelian 3 B := c.b1.1.1
  by_cases hab : a ∈ Subgroup.zpowers b
  · have hCa := centralizer_eq_of_mem_zpowers hBe c.hw.1 s1.b1 hab ha1
    have hK : KOf L A a = L := by
      have : KOf L A a = KOf L A b := by unfold KOf; rw [hCa]
      rw [this, s1.Kb]
    refine ⟨?_, q, Or.inl rfl, ?_, ?_⟩
    · have hCa' : Cs a = Cs b := hCa
      rw [hK, hCa']; exact s1.compL
    · rw [hK]; exact s4.tL
    · rw [hK]; exact s1.quasiL
  · obtain ⟨hcomp, hfld, hbN⟩ := s1.fldKa a haA hab ha1
    have hquasi := gl_quasi_barOf hcomp
    refine ⟨hcomp, ?_⟩
    obtain ⟨m, hS⟩ := c.stand
    have hZK : Subgroup.center ↥(barX 3 (Cs a) (KOf L A a)) = ⊥ :=
      hi.zk G m hS c.c4 B c.b1 b L A c.hw a haA ha1 hab
    obtain ⟨F, hFJ, hF3, hFne⟩ := s1.Fne
    have hJK : JOf L A ≤ KOf L A a := le_kOf L A a
    have hJA : JOf L A ≤ CD A := (glaPLayer_le' 3 _).trans inf_le_right
    have hJa : JOf L A ≤ Cs a :=
      hJA.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA))
    by_cases hcov : KOf L A a ≤ JOf L A ⊔ GLAPPrimeCoreOf 3 (KOf L A a)
    · have hbx : barX 3 (Cs a) (JOf L A) = barX 3 (Cs a) (KOf L A a) :=
        gl_barX_eq_of_cover hcomp hJK hcov
      have e1 := (gl_barOf_equiv hcomp).some
      have hq : CFSG.Open.IsQuasisimple ↥(barX 3 (Cs a) (JOf L A)) := by
        rw [hbx]; exact gl_quasi_barX hcomp
      have hZ : Subgroup.center ↥(barX 3 (Cs a) (JOf L A)) = ⊥ := by
        rw [hbx]; exact hZK
      have e2 := (gl_barOf_equiv_of_centreless hFJ hF3 hFne hJa hq hZ).some
      have e : barOf 3 (KOf L A a) ≃* barOf 3 (JOf L A) :=
        (e1.trans (MulEquiv.subgroupCongr hbx.symm)).trans e2.symm
      exact ⟨q0, Or.inr rfl, p4a_l3eps_equiv e.symm s4.tJ, hquasi⟩
    · have hkp := ctx_kproper c
      have ha3 : orderOf a = 3 := orderOf_eq_prime (s1.Ael.2 a haA) ha1
      have hb3 : orderOf b = 3 := orderOf_eq_prime s1.hb3 s1.b1
      have hcomm : b * a = a * b := comm_of_isElemAbelian' s1.Ael s1.bA haA
      have hAeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = A :=
        A_eq_sup s1.Ael s1.Acard s1.bA haA s1.b1 hab
      have hCD : CD A = Cs a ⊓ Cs b := p4a_CD_eq hAeq haA s1.bA
      have hJL : JOf L A ≤ L := s1.JL
      have hLlay : L ≤ GLAPLayer 3 (Cs b) := le_sSup s1.compL
      have hJab : GLAPComponent 3 (GLAPLayer 3 (Cs b) ⊓ Cs a) (JOf L A) := by
        have h1 : GLAPComponent 3 (Cs a ⊓ Cs b) (JOf L A) := hCD ▸ s2.JA
        refine gl_comp_restrict h1 (le_inf (hJL.trans hLlay) hJa) ?_
        exact fun y hy => ⟨hy.2, glaPLayer_le' 3 _ hy.1⟩
      obtain ⟨h1, hbCa, hIC⟩ := (@hi.i1823 G _ _ (ctx_simple c) (ctx_nonab c) hkp) b a hb3 ha3
        hcomm (JOf L A) hJab
      have hncl : ncl (GLAPLayer 3 (Cs a)) (JOf L A) = KOf L A a := rfl
      rw [hncl] at h1 hIC
      have hnt : ¬ TrivOn (KOf L A a) b := by
        intro htriv
        have hle := p4a_barX_le_centralizer hcomp hbCa htriv
        rw [inf_eq_left.2 hle] at hIC
        have hb := gl_barX_eq_of_isComponentOf hcomp hIC
        exact hcov (gl_cover_of_barX_eq hcomp hJK hb)
      have hZbar : Subgroup.center (barOf 3 (KOf L A a)) = ⊥ :=
        center_eq_bot_of_mulEquiv' (gl_barOf_equiv hcomp).some hZK
      obtain ⟨hnb, hfa⟩ := hfld
      have hα : barAut 3 (KOf L A a) ⟨b, hnb⟩ ≠ 1 := fun h => hnt ⟨hnb, h⟩
      obtain ⟨r, hr⟩ := p4a_raw_of_fieldAut hZbar _ hα hfa
      obtain ⟨-, r0, hr0, hdisj⟩ := hi.l3fix G (KOf L A a) b r hquasi hr s1.hb3 ⟨hnb, hfa⟩ hnt
      rcases hdisj with ⟨hc, hraw0, hL, hU⟩ | ⟨hbot, -, -⟩
      · have hJeq : JOf L A = CLay (KOf L A a) b :=
          gl_comp_eq_of_le hc (gl_comp_iff_layer.2 h1) h1.1
        have e := (p4a_barOf_eq hJeq.symm).some
        have hraw0' : IsL3Raw r0 (barOf 3 (JOf L A)) :=
          hraw0.imp (p4a_psln_equiv e) (p4a_psun_equiv e)
        have hL' : IsPSLn 3 r (barOf 3 (KOf L A a)) → IsPSLn 3 r0 (barOf 3 (JOf L A)) :=
          fun h => p4a_psln_equiv e (hL h)
        have hU' : IsPSUn 3 r (barOf 3 (KOf L A a)) → IsPSUn 3 r0 (barOf 3 (JOf L A)) :=
          fun h => p4a_psun_equiv e (hU h)
        clear hraw0 hL hU
        have hrawq0 : IsL3Raw q0 (barOf 3 (JOf L A)) :=
          s4.tJ.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)
        have hr0q : r0 = q0 := (hi.l3iso _ r0 q0 hraw0' hrawq0).1
        have hrq : r = q := by rw [hr0, hr0q, s4.q3]
        have hmod : ∀ n : ℕ, (n ^ 3) % 3 = n % 3 ∨ (n % 3 = 0) := by
          intro n
          have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
          rcases this with h | h | h
          · exact Or.inr h
          · left; rw [Nat.pow_mod, h]
          · left; rw [Nat.pow_mod, h]
        refine ⟨q, Or.inl rfl, ?_, hquasi⟩
        rcases hr with hr | hr
        · rcases s4.tJ with ⟨h3, hJ⟩ | ⟨h3, hJ⟩
          · refine Or.inl ⟨?_, hrq ▸ hr⟩
            rw [s4.q3]
            rcases hmod q0 with h | h <;> omega
          · exact absurd ⟨hL' hr, hJ⟩ (hi.l3iso _ r0 q0 hraw0' hrawq0).2
        · rcases s4.tJ with ⟨h3, hJ⟩ | ⟨h3, hJ⟩
          · exact absurd ⟨hJ, hU' hr⟩ (hi.l3iso _ q0 r0 hrawq0 hraw0').2
          · refine Or.inr ⟨?_, hrq ▸ hr⟩
            rw [s4.q3]
            rcases hmod q0 with h | h <;> omega
      · exfalso
        have hJle : JOf L A ≤ CLay (KOf L A a) b := h1.1
        rw [hbot, le_bot_iff] at hJle
        exact s2.Jne hJle

structure S5Facts (V : InndiagVocab) (L A : Subgroup G) (b x : G) (q0 : ℕ) (y0 : G) (J0 : Subgroup G) :
    Prop where
  y0L : y0 ∈ L ⊓ Cs x
  y03 : y0 ^ 3 = 1
  y0inn : IndInn V L y0
  y0nt : ¬ TrivOn L y0
  J0def : J0 = GLAPLayer 3 (L ⊓ CD (A ⊔ Subgroup.zpowers y0))
  J0J : J0 ≤ JOf L A
  J0comp : GLAPComponent 3 (L ⊓ CD (A ⊔ Subgroup.zpowers y0)) J0
  J0type : IsTypeL2 q0 (barOf 3 J0)

theorem p5_CD_sup_zpowers (A : Subgroup G) (y : G) :
    CD (A ⊔ Subgroup.zpowers y) = CD A ⊓ Cs y := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact ⟨fun g hg => h g (Subgroup.mem_sup_left hg),
      h y (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))⟩
  · rintro ⟨h1, h2⟩ g hg
    have hle : A ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le ?_ ?_
      · intro a ha
        simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
          forall_eq]
        exact (h1 a ha).symm
      · rw [Subgroup.zpowers_le]
        simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
          forall_eq]
        exact h2.symm
    have := hle hg
    rw [Subgroup.mem_centralizer_iff] at this
    exact (this z rfl).symm

theorem p5_inf_CD_zpowers (X : Subgroup G) (y : G) :
    X ⊓ CD (Subgroup.zpowers y) = X ⊓ Cs y := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Set.mem_singleton_iff, forall_eq]
  refine and_congr_right fun _ => ⟨fun h => h y (Subgroup.mem_zpowers y), fun h g hg => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  exact ((Commute.zpow_left (show Commute y z from h) k)).eq

omit [Finite G] in
theorem p5_isKGroup_of_open {X : Type} [Group X] [Finite X] (h : CFSG.Open.IsKGroup X) :
    CFSG.IsKGroup X :=
  CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
    CFSG.Assembly.inCatalog_containsAbelianSimple h

theorem p5_isPGroup_zpowers {y : G} (h : y ^ 3 = 1) : IsPGroup 3 (Subgroup.zpowers y) := by
  intro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, ?_⟩
  ext
  simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [h]

theorem s5_y0 {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    (s3 : ¬ TrivOn (KOf L A x) b ∧ ¬ TrivOn L x) {q q0 : ℕ} (s4 : S4Facts V L A b x q q0) :
    ∃ (y0 : G) (J0 : Subgroup G), S5Facts V L A b x q0 y0 J0 := by
  have hnT : ¬ TrivOn L x := s3.2
  have hq8 : q ≠ 8 := fun h => by have := s4.q8; subst h; simp at this
  obtain ⟨y0, hy0, hy03, hyinn, hynt, r0, hqr, hcomp, hty⟩ :=
    hi.l3y0 G L x q s1.quasiL s4.tL hq8 s1.hx3 s1.fldLx hnT
  have hr : r0 = q0 := by
    have : r0 ^ 3 = q0 ^ 3 := hqr.symm.trans s4.q3
    exact Nat.pow_left_injective (by norm_num) this
  subst hr
  have hCD : L ⊓ CD (A ⊔ Subgroup.zpowers y0) = L ⊓ Cs x ⊓ Cs y0 := by
    rw [p5_CD_sup_zpowers, ← inf_assoc, s1.inf]
  have hXne : L ⊓ Cs x ≠ ⊤ := by
    intro h
    exact hnT (gl_trivOn_of_le_centralizer
      (fun z hz => (Subgroup.mem_inf.mp (h ▸ Subgroup.mem_top z : z ∈ L ⊓ Cs x)).2))
  have hK : CFSG.IsKGroup ↥(L ⊓ Cs x) :=
    p5_isKGroup_of_open (isKGroup_of_isKProper (ctx_kproper c) hXne)
  have h181 := hi.i181 G (L ⊓ Cs x) hK (Subgroup.zpowers y0)
    (by rw [Subgroup.zpowers_le]; exact hy0) (p5_isPGroup_zpowers hy03)
  rw [p5_inf_CD_zpowers] at h181
  refine ⟨y0, GLAPLayer 3 (L ⊓ Cs x ⊓ Cs y0), ⟨hy0, hy03, hyinn, hynt,
    by rw [hCD], ?_, by rw [hCD]; exact hcomp, hty⟩⟩
  show GLAPLayer 3 (L ⊓ Cs x ⊓ Cs y0) ≤ GLAPLayer 3 (L ⊓ CD A)
  rw [s1.inf]; exact h181

structure S6Facts (V : InndiagVocab) (L A : Subgroup G) (b x : G) (y0 y : G) (J0 : Subgroup G) : Prop where
  yM : y ∈ A ⊔ Subgroup.zpowers y0
  yA : y ∉ A
  y3 : y ^ 3 = 1
  Meq : A ⊔ Subgroup.zpowers y = A ⊔ Subgroup.zpowers y0
  Mel : IsElemAbelian 3 (A ⊔ Subgroup.zpowers y)
  yK : IndInn V (KOf L A x) y
  yKnt : ¬ TrivOn (KOf L A x) y
  yL : IndInn V L y
  yLnt : ¬ TrivOn L y
  J0M : GLAPComponent 3 (CD (A ⊔ Subgroup.zpowers y)) J0
  normKa : ∀ a ∈ A, a ≠ 1 → y ∈ Subgroup.normalizer (KOf L A a : Set G) ∧
    J0 ≤ KOf L A a

theorem p6_center_barOf {r : ℕ} {Y : Type*} [Group Y] (h : IsL3Eps r Y)
    (hperf : commutator Y = ⊤) : Subgroup.center Y = ⊥ := by
  rcases h with ⟨h3, F, _, _, hF, ⟨e⟩⟩ | ⟨h3, F, _, _, hF, ⟨e⟩⟩
  · exact center_eq_bot_of_mulEquiv' e (center_statedProj_SL (by rw [hF]; exact h3)
      (perfect_of_mulEquiv' e hperf))
  · exact center_eq_bot_of_mulEquiv' e (center_statedProj_SU hF h3 (perfect_of_mulEquiv' e hperf))

theorem p6_center_barX {X K : Subgroup G} {r : ℕ} (hK : GLAPComponent 3 X K)
    (h : IsL3Eps r (barOf 3 K)) : Subgroup.center ↥(barX 3 X K) = ⊥ := by
  obtain ⟨e⟩ := gl_barOf_equiv hK
  exact center_eq_bot_of_mulEquiv' e.symm (p6_center_barOf h (gl_quasi_barOf hK).1)

theorem p6_isTypeL2_of_equiv {r : ℕ} {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsTypeL2 r Y) : IsTypeL2 r Y' := by
  obtain ⟨F, hF, hfin, hc, ⟨f⟩⟩ := h
  refine ⟨F, hF, hfin, hc, ⟨?_⟩⟩
  refine (QuotientGroup.congr (Subgroup.center Y') (Subgroup.center Y) e.symm ?_).trans f
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩ g
    apply e.injective
    simpa using hw (e g)
  · intro hz
    refine ⟨e z, fun g => ?_, by simp⟩
    apply e.symm.injective
    simpa using hz (e.symm g)

theorem p6_layer_norm {X : Subgroup G} {e : G} (he : e ∈ X) :
    e ∈ Subgroup.normalizer (GLAPLayer 3 X : Set G) := by
  have key : ∀ e ∈ X, GLBConj e (GLAPLayer 3 X) ≤ GLAPLayer 3 X := by
    intro e he
    unfold GLBConj
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun M hM => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hM e
    rw [gLBConj_eq_of_mem' he] at h
    exact le_sSup h
  have h1 := key e he
  have h2 := gLBConj_mono e (key e⁻¹ (X.inv_mem he))
  rw [gLBConj_gLBConj_inv] at h2
  exact mem_normalizer_iff_gLBConj_eq.2 (le_antisymm h1 h2)

omit [Finite G] in
theorem p6_norm_of_commute {J : Subgroup G} {g : G} (h : ∀ w ∈ J, g * w = w * g) :
    g ∈ Subgroup.normalizer (J : Set G) :=
  Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun w hw => (h w hw).symm)

theorem p6_norm_comp {Xa K J F : Subgroup G} {e : G} {r : ℕ}
    (hK : GLAPComponent 3 Xa K) (hr : IsL3Eps r (barOf 3 K))
    (heX : e ∈ Xa) (heJ : e ∈ Subgroup.normalizer (J : Set G))
    (hJK : J ≤ K) (hFJ : F ≤ J) (hF3 : IsPGroup 3 F) (hF : F ≠ ⊥) :
    e ∈ Subgroup.normalizer (K : Set G) := by
  have hK' : GLAPComponent 3 Xa (GLBConj e K) := by
    have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK e
    rwa [gLBConj_eq_of_mem' heX] at h
  by_cases hbar : barX 3 Xa (GLBConj e K) = barX 3 Xa K
  · exact mem_normalizer_iff_gLBConj_eq.2 (glaPComponent_unique hK' hK hbar)
  · exfalso
    have hcomm : ⁅barX 3 Xa (GLBConj e K), barX 3 Xa K⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK'.2.2.1 hK.2.2.1 hbar
    have hcen := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hFK' : F ≤ GLBConj e K := by
      intro f hf
      rw [mem_gLBConj]
      exact hJK (((Subgroup.mem_normalizer_iff.1 heJ) f).1 (hFJ hf))
    have hFX : F ≤ Xa := hFJ.trans (hJK.trans hK.1)
    apply barX_ne_bot_of_isPGroup hFX hF3 hF
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ barX 3 Xa K := barX_mono' 3 (hFJ.trans hJK) hz
    have h2 : z ∈ barX 3 Xa (GLBConj e K) := barX_mono' 3 hFK' hz
    have hz0 : (⟨z, h1⟩ : ↥(barX 3 Xa K)) ∈ Subgroup.center ↥(barX 3 Xa K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 (hcen h2) g g.2)
    rw [p6_center_barX hK hr] at hz0
    have := congrArg Subtype.val (Subgroup.mem_bot.1 hz0)
    exact Subgroup.mem_bot.2 this

theorem p6_yKnt {V : InndiagVocab} (hi : Inputs V) (s1 : S1Facts B b L A x)
    (s2 : S2Facts V B b L A x) {q q0 : ℕ} (s4 : S4Facts V L A b x q q0)
    {y0 y : G} {J0 : Subgroup G} (s5 : S5Facts V L A b x q0 y0 J0)
    (hyJ : y ∈ Subgroup.normalizer (JOf L A : Set G)) (hy3 : y ^ 3 = 1)
    (hMeq : A ⊔ Subgroup.zpowers y = A ⊔ Subgroup.zpowers y0) :
    ¬ TrivOn (KOf L A x) y := by
  intro hT
  have hJsn : IsSubnormal (JOf L A) (L ⊓ Cs x) := s2.J1.2.1
  have hTJ : TrivOn (JOf L A) y := gl_trivOn_restrict s1.JK hyJ hT
  have hQ := gl_quasi_barOf s2.J1
  obtain ⟨hc1, hc2⟩ := hi.l3T G (JOf L A) y hQ hy3 hTJ
  have hJCD : JOf L A ≤ CD A := (glaPLayer_le' 3 _).trans inf_le_right
  have hyM : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have eq1 : JOf L A ⊓ Cs y = JOf L A ⊓ CD (A ⊔ Subgroup.zpowers y) := by
    ext w
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hw, hwy⟩
      refine ⟨hw, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      have hle : A ⊔ Subgroup.zpowers y ≤ Cs w := by
        refine sup_le (fun a ha => Subgroup.mem_centralizer_iff.2 fun h' hh' => ?_)
          ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_iff.2 fun h' hh' => ?_))
        · rw [Set.mem_singleton_iff.1 hh']
          exact ((Subgroup.mem_centralizer_iff.1 (hJCD hw)) a ha).symm
        · rw [Set.mem_singleton_iff.1 hh']
          exact (Subgroup.mem_centralizer_iff.1 hwy y rfl).symm
      exact (Subgroup.mem_centralizer_iff.1 (hle hh) w rfl).symm
    · rintro ⟨hw, hwM⟩
      exact ⟨hw, Subgroup.centralizer_le (Set.singleton_subset_iff.2 hyM) hwM⟩
  have hc1' : GLAPComponent 3 (JOf L A ⊓ CD (A ⊔ Subgroup.zpowers y)) (CLay (JOf L A) y) := by
    have := hc1
    rwa [eq1] at this
  have hsn : IsSubnormal (JOf L A ⊓ CD (A ⊔ Subgroup.zpowers y))
      (L ⊓ CD (A ⊔ Subgroup.zpowers y0)) := by
    have h1 := gl_isSubnormal_inf (CD (A ⊔ Subgroup.zpowers y)) hJsn
    have e : (L ⊓ Cs x) ⊓ CD (A ⊔ Subgroup.zpowers y) = L ⊓ CD (A ⊔ Subgroup.zpowers y0) := by
      rw [← s1.inf, hMeq, inf_assoc]
      congr 1
      exact inf_eq_right.2 (Subgroup.centralizer_le (by
        intro a ha; exact Subgroup.mem_sup_left ha))
    rwa [e] at h1
  have hlift := gl_comp_lift hsn hc1'
  have hCJ0 : CLay (JOf L A) y ≤ J0 := by
    rw [s5.J0def]
    exact le_sSup hlift
  have hcov : JOf L A ≤ J0 ⊔ GLAPPrimeCoreOf 3 (JOf L A) :=
    hc2.trans (sup_le_sup_right hCJ0 _)
  have hbar : barX 3 (L ⊓ Cs x) J0 = barX 3 (L ⊓ Cs x) (JOf L A) :=
    gl_barX_eq_of_cover s2.J1 s5.J0J hcov
  obtain ⟨F, hFJ, hF3, hF1⟩ := s1.Fne
  have hJX : JOf L A ≤ L ⊓ Cs x := s2.J1.1
  have hJ0X : J0 ≤ L ⊓ Cs x := s5.J0J.trans hJX
  have hFX : F ≤ L ⊓ Cs x := hFJ.trans hJX
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3F : 3 ∣ Nat.card F := by
    rcases hF3.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hF1
    · exact h
  have h3 : 3 ∣ Nat.card J0 := by
    have h1 : Nat.card (barX 3 (L ⊓ Cs x) F) ∣ Nat.card (barX 3 (L ⊓ Cs x) J0) :=
      Subgroup.card_dvd_of_le (by rw [hbar]; exact barX_mono' 3 hFJ)
    rw [card_barX' hF3 hFX] at h1
    have h2 : Nat.card (barX 3 (L ⊓ Cs x) J0) ∣ Nat.card ↥(J0.subgroupOf (L ⊓ Cs x)) :=
      Subgroup.card_map_dvd _ _
    have h4 : Nat.card ↥(J0.subgroupOf (L ⊓ Cs x)) = Nat.card J0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ0X).toEquiv
    rw [h4] at h2
    exact (h3F.trans h1).trans h2
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥J0) 3 h3
  have hF0J0 : Subgroup.zpowers (g : G) ≤ J0 := (Subgroup.zpowers_le).2 g.2
  have hF0card : Nat.card (Subgroup.zpowers (g : G)) = 3 ^ 1 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg, pow_one]
  have hF03 : IsPGroup 3 (Subgroup.zpowers (g : G)) := IsPGroup.of_card hF0card
  have hF0ne : Subgroup.zpowers (g : G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hF0card
    omega
  obtain ⟨e0⟩ := gl_barOf_equiv_of_centreless (X := L ⊓ Cs x) hF0J0 hF03 hF0ne hJ0X
    (by rw [hbar]; exact gl_quasi_barX s2.J1) (by rw [hbar]; exact p6_center_barX s2.J1 s4.tJ)
  obtain ⟨e1⟩ := gl_barOf_equiv s2.J1
  have e : barOf 3 J0 ≃* barOf 3 (JOf L A) :=
    e0.trans ((MulEquiv.subgroupCongr hbar).trans e1.symm)
  exact hi.l3l2 (barOf 3 (JOf L A)) q0 q0 s4.tJ (p6_isTypeL2_of_equiv e s5.J0type)

theorem s6_y {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    (s2 : S2Facts V B b L A x) (s3 : ¬ TrivOn (KOf L A x) b ∧ ¬ TrivOn L x) {q q0 : ℕ}
    (s4 : S4Facts V L A b x q q0)
    (s4a : ∀ a ∈ A, a ≠ 1 → GLAPComponent 3 (Cs a) (KOf L A a) ∧
      ∃ r : ℕ, (r = q ∨ r = q0) ∧ IsL3Eps r (barOf 3 (KOf L A a)) ∧
        CFSG.Open.IsQuasisimple (barOf 3 (KOf L A a)))
    {y0 : G} {J0 : Subgroup G} (s5 : S5Facts V L A b x q0 y0 J0) :
    ∃ y : G, S6Facts V L A b x y0 y J0 := by
  have hLC : L ≤ Cs b := s1.compL.1
  have hy0X : y0 ∈ L ⊓ CD A := by rw [s1.inf]; exact s5.y0L
  have hy0L : y0 ∈ L := hy0X.1
  have hy0A : ∀ a ∈ A, a * y0 = y0 * a := fun a ha =>
    Subgroup.mem_centralizer_iff.1 hy0X.2 a ha
  have hby0 : b * y0 = y0 * b := hy0A b s1.bA
  have hJle : JOf L A ≤ L ⊓ CD A := glaPLayer_le' 3 _
  have hy0J : y0 ∈ Subgroup.normalizer (JOf L A : Set G) := p6_layer_norm hy0X
  obtain ⟨F, hFJ, hF3, hF1⟩ := s1.Fne
  have hy0Cs : ∀ a ∈ A, y0 ∈ Cs a := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact hy0A a ha
  have hraw : IsL3Raw q (barOf 3 (KOf L A x)) := by
    rcases s4.tK with ⟨_, h⟩ | ⟨_, h⟩
    exacts [Or.inl h, Or.inr h]
  have hKcomp := fun a (ha : a ∈ A) (ha1 : a ≠ 1) => (s4a a ha ha1)
  have hnormK : ∀ a ∈ A, a ≠ 1 → ∀ e : G, e ∈ Cs a → e ∈ Subgroup.normalizer (JOf L A : Set G) →
      e ∈ Subgroup.normalizer (KOf L A a : Set G) := by
    intro a ha ha1 e he heJ
    obtain ⟨hc, r, -, hr, -⟩ := s4a a ha ha1
    exact p6_norm_comp hc hr he heJ (le_kOf L A a) hFJ hF3 hF1
  have hy0N : y0 ∈ Subgroup.normalizer (KOf L A x : Set G) :=
    hnormK x c.xA c.x1 y0 (hy0Cs x c.xA) hy0J
  rcases hi.l3out G (KOf L A x) b y0 q s4.quasiK hraw s1.bK hy0N s1.hb3 s5.y03 hby0 with h | ⟨j, hj⟩
  · exact absurd h s4.nbK
  obtain ⟨y, hyd⟩ : ∃ y : G, y = y0 * b ^ j := ⟨_, rfl⟩
  rw [← hyd] at hj
  have hbj : b ^ j ∈ A := A.pow_mem s1.bA j
  have hbj3 : (b ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, s1.hb3, one_pow]
  have hcomm : Commute y0 (b ^ j) := (show Commute b y0 from hby0).symm.pow_right j
  have hy3 : y ^ 3 = 1 := by rw [hyd, hcomm.mul_pow, s5.y03, hbj3, mul_one]
  have hyM : y ∈ A ⊔ Subgroup.zpowers y0 := by
    rw [hyd]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y0))
      (Subgroup.mem_sup_left hbj)
  have hMeq : A ⊔ Subgroup.zpowers y = A ⊔ Subgroup.zpowers y0 := by
    apply le_antisymm
    · exact sup_le le_sup_left ((Subgroup.zpowers_le).2 hyM)
    · refine sup_le le_sup_left ((Subgroup.zpowers_le).2 ?_)
      have : y0 = y * (b ^ j)⁻¹ := by rw [hyd]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left hbj))
  have hycomm : ∀ a ∈ A, a * y = y * a := by
    intro a ha
    rw [hyd]
    exact ((show Commute a y0 from hy0A a ha).mul_right
      (show Commute a (b ^ j) from comm_of_isElemAbelian' s1.Ael ha hbj)).eq
  have hyCD : y ∈ CD A := Subgroup.mem_centralizer_iff.2 fun a ha => hycomm a ha
  have hyCs : ∀ a ∈ A, y ∈ Cs a := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact hycomm a ha
  have hyJ : y ∈ Subgroup.normalizer (JOf L A : Set G) := by
    rw [hyd]
    refine Subgroup.mul_mem _ hy0J (p6_norm_of_commute fun w hw => ?_)
    exact Subgroup.mem_centralizer_iff.1 (hJle hw).2 _ hbj
  have hzy : IsElemAbelian 3 (Subgroup.zpowers y) := by
    refine ⟨inferInstance, fun w hw => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy3, one_zpow]
  have hLb : ∀ w ∈ L, ∀ n : ℕ, b ^ n * w = w * b ^ n := by
    intro w hw n
    have hh : b * w = w * b := Subgroup.mem_centralizer_iff.1 (hLC hw) b rfl
    exact ((show Commute b w from hh).pow_left n).eq
  have hLtriv : TrivOn L (b ^ j) := gl_trivOn_of_le_centralizer fun w hw =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]; exact hLb w hw j
  have hy0nL : y0 ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hy0L
  have hmL := gl_mul_trivOn (V := V) hy0nL hLtriv
  refine ⟨y, hyM, ?_, hy3, hMeq, ?_, hj, p6_yKnt hi s1 s2 s4 s5 hyJ hy3 hMeq, ?_, ?_, ?_, ?_⟩
  · intro hyA
    have hy0A' : y0 ∈ A := by
      have : y0 = y * (b ^ j)⁻¹ := by rw [hyd]; group
      rw [this]
      exact A.mul_mem hyA (A.inv_mem hbj)
    obtain ⟨-, -, -, -, -, ⟨-, -, -, hfa, -⟩, -⟩ := c.hw
    exact (hi.l3inn G L y0 q s1.quasiL s4.tL s5.y03 s5.y0inn s5.y0nt).1 (hfa y0 hy0A')
  · refine isElemAbelian_sup_of_commute' s1.Ael hzy fun a ha w hw => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((show Commute a y from hycomm a ha).zpow_right n).eq
  · rw [hyd]; exact hmL.1.2 s5.y0inn
  · rw [hyd]; exact fun h => s5.y0nt (hmL.2.1 h)
  · rw [hMeq]
    have hsn : IsSubnormal (L ⊓ CD (A ⊔ Subgroup.zpowers y0)) (CD (A ⊔ Subgroup.zpowers y0)) := by
      have h1 := gl_isSubnormal_inf (CD (A ⊔ Subgroup.zpowers y0)) s1.compL.2.1
      have e : Cs b ⊓ CD (A ⊔ Subgroup.zpowers y0) = CD (A ⊔ Subgroup.zpowers y0) :=
        inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2
          (Subgroup.mem_sup_left s1.bA)))
      rwa [e] at h1
    exact gl_comp_lift hsn s5.J0comp
  · intro a ha ha1
    exact ⟨hnormK a ha ha1 y (hyCs a ha) hyJ, s5.J0J.trans (le_kOf L A a)⟩

structure S7aFacts (L A : Subgroup G) (b x y : G) (q : ℕ) (J0 : Subgroup G) : Prop where
  Icomp : ∀ a ∈ A, a ≠ 1 → GLAPComponent 3 (Cs y ⊓ Cs a) (Iof y J0 (Subgroup.zpowers a))
  IleK : ∀ a ∈ A, a ≠ 1 → Iof y J0 (Subgroup.zpowers a) ≤ KOf L A a
  J0I : ∀ a ∈ A, a ≠ 1 → J0 ≤ Iof y J0 (Subgroup.zpowers a)
  Ix2 : IsTypeL2 q (barOf 3 (Iof y J0 (Subgroup.zpowers x)))
  Ib2 : IsTypeL2 q (barOf 3 (Iof y J0 (Subgroup.zpowers b)))

theorem p7a_ne_bot_of_comp {X K : Subgroup G} (h : GLAPComponent 3 X K) : K ≠ ⊥ := by
  intro hK
  have hq := h.2.2.1.2.2
  subst hK
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot] at hq
  obtain ⟨u, v, huv⟩ := hq.2.toNontrivial.exists_pair_ne
  refine huv ?_
  induction u using QuotientGroup.induction_on with | _ u' =>
  induction v using QuotientGroup.induction_on with | _ v' =>
  rw [Subsingleton.elim u' v']

theorem p7a_CD_sup (H K : Subgroup G) : CD (H ⊔ K) = CD H ⊓ CD K := by
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hz
    exact ⟨fun h hh => hz h (Subgroup.mem_sup_left hh), fun h hh => hz h (Subgroup.mem_sup_right hh)⟩
  · rintro ⟨h1, h2⟩
    have hle : H ⊔ K ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact (h1 h hh).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact (h2 h hh).symm
    intro h hh
    have := (Subgroup.mem_centralizer_iff.1 (hle hh)) z (Set.mem_singleton z)
    exact this.symm

theorem p7a_CD_zpowers (a : G) : CD (Subgroup.zpowers a) = Cs a := by
  show Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) = _
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem p7a_layer_le (Z : Subgroup G) : GLAPLayer 3 Z ≤ Z :=
  sSup_le fun _ hL => hL.1

theorem p7a_dich {V : InndiagVocab} (hi : Inputs V) {K : Subgroup G} {g : G} {r : ℕ}
    (hq : CFSG.Open.IsQuasisimple (barOf 3 K)) (hr : IsL3Eps r (barOf 3 K))
    (hgN : g ∈ Subgroup.normalizer (K : Set G)) (hg3 : g ^ 3 = 1) :
    (CLay K g = ⊥ ∨ GLAPComponent 3 (K ⊓ Cs g) (CLay K g)) ∧
    (IndInn V K g → ¬ TrivOn K g → CLay K g = ⊥ ∨
      (GLAPComponent 3 (K ⊓ Cs g) (CLay K g) ∧ IsTypeL2 r (barOf 3 (CLay K g)))) := by
  by_cases hT : TrivOn K g
  · exact ⟨Or.inr (hi.l3T G K g hq hg3 hT).1, fun _ h => absurd hT h⟩
  · by_cases hI : IndInn V K g
    · have h := (hi.l3inn G K g r hq hr hg3 hI hT).2
      exact ⟨h.imp id (fun h' => h'.1), fun _ _ => h⟩
    · have hraw : IsL3Raw r (barOf 3 K) := by
        rcases hr with ⟨_, h⟩ | ⟨_, h⟩
        · exact Or.inl h
        · exact Or.inr h
      have hfld := hi.l3fld G K g r hq hraw hgN hg3 hI
      obtain ⟨-, r0, -, h | h⟩ := hi.l3fix G K g r hq hraw hg3 hfld hT
      · exact ⟨Or.inr h.1, fun h' => absurd h' hI⟩
      · exact ⟨Or.inl h.1, fun h' => absurd h' hI⟩

theorem p7a_core {V : InndiagVocab} (hi : Inputs V) (kp : CFSG.Open.IsKProper G)
    {a y : G} {M J0 Ka : Subgroup G} {r : ℕ}
    (hMel : IsElemAbelian 3 M) (haM : a ∈ M) (hyM : y ∈ M)
    (hKa : GLAPComponent 3 (Cs a) Ka) (hq : CFSG.Open.IsQuasisimple (barOf 3 Ka))
    (hr : IsL3Eps r (barOf 3 Ka)) (hyN : y ∈ Subgroup.normalizer (Ka : Set G))
    (hJ0K : J0 ≤ Ka) (hJ0M : GLAPComponent 3 (CD M) J0) :
    Iof y J0 (Subgroup.zpowers a) = CLay Ka y ∧
    GLAPComponent 3 (Cs y ⊓ Cs a) (CLay Ka y) ∧
    (IndInn V Ka y → ¬ TrivOn Ka y → IsTypeL2 r (barOf 3 (CLay Ka y))) := by
  have hy3 : y ^ 3 = 1 := hMel.2 y hyM
  have hDM : Subgroup.zpowers y ⊔ Subgroup.zpowers a ≤ M :=
    sup_le (Subgroup.zpowers_le.2 hyM) (Subgroup.zpowers_le.2 haM)
  have hD : CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a) = Cs y ⊓ Cs a := by
    rw [p7a_CD_sup, p7a_CD_zpowers, p7a_CD_zpowers]
  obtain ⟨𝒞, h𝒞comp, h𝒞sup, -, -⟩ := hi.i1834 G kp _ M hMel hDM J0 hJ0M
  have hIof : Iof y J0 (Subgroup.zpowers a) =
      ncl (GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a))) J0 := rfl
  have hlay : GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a)) ≤ GLAPLayer 3 (Cs a) := by
    have hPa : IsPGroup 3 (Subgroup.zpowers a) :=
      (Lemma514Ns.isPGroup_of_isElemAbelian' hMel).to_le (Subgroup.zpowers_le.2 haM)
    have hPy : IsPGroup 3 (Subgroup.zpowers y) :=
      (Lemma514Ns.isPGroup_of_isElemAbelian' hMel).to_le (Subgroup.zpowers_le.2 hyM)
    have hcomm : ∀ d ∈ Subgroup.zpowers a, ∀ e ∈ Subgroup.zpowers y, d * e = e * d := by
      intro d hd e he
      exact hMel.1.is_comm.comm (⟨d, Subgroup.zpowers_le.2 haM hd⟩ : M) ⟨e, Subgroup.zpowers_le.2 hyM he⟩ |> fun h => by
        simpa using congrArg Subtype.val h
    have h := hi.i182 G kp _ _ hPa hPy hcomm
    rw [p7a_CD_zpowers, p7a_CD_zpowers] at h
    rw [hD, inf_comm, ← h]
    exact (p7a_layer_le _).trans (inf_le_left)
  have hlayN : GLAPLayer 3 (Cs a) ≤ Subgroup.normalizer (Ka : Set G) :=
    sSup_le fun M' hM' => comp_le_normalizer hKa hM'
  have hIK : ncl (GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a))) J0 ≤ Ka := by
    refine iSup₂_le fun g hg => ?_
    calc GLBConj g J0 ≤ GLBConj g Ka := gLBConj_mono g hJ0K
      _ = Ka := gLBConj_eq_of_mem_normalizer (hlayN (hlay hg))
  have hdich := p7a_dich hi hq hr hyN hy3
  have hall : ∀ C' ∈ 𝒞, C' = CLay Ka y := by
    intro C' hC'
    have hcomp := h𝒞comp C' hC'
    rw [hD] at hcomp
    have hC'Ka : C' ≤ Ka :=
      (le_iSup₂ (f := fun L (_ : L ∈ 𝒞) => L) C' hC').trans (h𝒞sup ▸ hIK)
    have hsub : C' ≤ Ka ⊓ Cs y := le_inf hC'Ka (hcomp.1.trans inf_le_left)
    have hres : GLAPComponent 3 (Ka ⊓ Cs y) C' :=
      gl_comp_restrict hcomp hsub (le_inf inf_le_right (inf_le_left.trans hKa.1))
    have hle : C' ≤ CLay Ka y := le_sSup hres
    have hne : CLay Ka y ≠ ⊥ := fun h =>
      p7a_ne_bot_of_comp hcomp (le_bot_iff.1 (h ▸ hle))
    exact gl_comp_eq_of_le (hdich.1.resolve_left hne) hres hle
  obtain ⟨C0, hC0⟩ : ∃ C0, C0 ∈ 𝒞 := by
    by_contra h
    push Not at h
    have h1 : (⨆ L ∈ 𝒞, L) = ⊥ := le_bot_iff.1 (iSup₂_le fun C hC => absurd hC (h C))
    have h2 : J0 ≤ ncl (GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a))) J0 := by
      have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a))) =>
        GLBConj g J0) 1 (Subgroup.one_mem _)
      rwa [gLBConj_one] at this
    rw [← h𝒞sup, h1] at h2
    exact p7a_ne_bot_of_comp hJ0M (le_bot_iff.1 h2)
  have hIeq : Iof y J0 (Subgroup.zpowers a) = CLay Ka y := by
    rw [hIof, ← h𝒞sup]
    exact le_antisymm (iSup₂_le fun C hC => (hall C hC).le)
      (((hall C0 hC0).symm.le).trans (le_iSup₂ (f := fun L (_ : L ∈ 𝒞) => L) C0 hC0))
  have hcompΛ : GLAPComponent 3 (Cs y ⊓ Cs a) (CLay Ka y) := by
    have := h𝒞comp C0 hC0
    rw [hD, hall C0 hC0] at this
    exact this
  have hne : CLay Ka y ≠ ⊥ := p7a_ne_bot_of_comp hcompΛ
  refine ⟨hIeq, hcompΛ, fun hI hT => ?_⟩
  rcases hdich.2 hI hT with h | h
  · exact absurd h hne
  · exact h.2

theorem s7a_Ia {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    (s2 : S2Facts V B b L A x) (s3 : ¬ TrivOn (KOf L A x) b ∧ ¬ TrivOn L x) {q q0 : ℕ}
    (s4 : S4Facts V L A b x q q0)
    (s4a : ∀ a ∈ A, a ≠ 1 → GLAPComponent 3 (Cs a) (KOf L A a) ∧
      ∃ r : ℕ, (r = q ∨ r = q0) ∧ IsL3Eps r (barOf 3 (KOf L A a)) ∧
        CFSG.Open.IsQuasisimple (barOf 3 (KOf L A a)))
    {y0 y : G} {J0 : Subgroup G} (s5 : S5Facts V L A b x q0 y0 J0) (s6 : S6Facts V L A b x y0 y J0) :
    S7aFacts L A b x y q J0 := by
  have kp := ctx_kproper c
  have hMel := s6.Mel
  have hyM : y ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have haM : ∀ a ∈ A, a ∈ A ⊔ Subgroup.zpowers y := fun a ha => Subgroup.mem_sup_left ha
  have gen : ∀ a ∈ A, a ≠ 1 → Iof y J0 (Subgroup.zpowers a) = CLay (KOf L A a) y ∧
      GLAPComponent 3 (Cs y ⊓ Cs a) (CLay (KOf L A a) y) := by
    intro a ha ha1
    obtain ⟨hKa, r, -, hr, hq⟩ := s4a a ha ha1
    obtain ⟨hyN, hJ0K⟩ := s6.normKa a ha ha1
    exact (p7a_core hi kp hMel (haM a ha) hyM hKa hq hr hyN hJ0K s6.J0M).imp id (fun h => h.1)
  have hJ0I : ∀ a : G, J0 ≤ Iof y J0 (Subgroup.zpowers a) := by
    intro a
    have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a))) =>
      GLBConj g J0) 1 (Subgroup.one_mem _)
    rwa [gLBConj_one] at this
  refine ⟨fun a ha ha1 => ?_, fun a ha ha1 => ?_, fun a _ _ => hJ0I a, ?_, ?_⟩
  · rw [(gen a ha ha1).1]; exact (gen a ha ha1).2
  · rw [(gen a ha ha1).1]
    exact (p7a_layer_le _).trans inf_le_left
  · obtain ⟨hyN, hJ0K⟩ := s6.normKa x c.xA c.x1
    have h := p7a_core hi kp hMel (haM x c.xA) hyM s1.compK s4.quasiK s4.tK hyN hJ0K s6.J0M
    rw [h.1]
    exact h.2.2 s6.yK s6.yKnt
  · have hJ0K : J0 ≤ L := by
      have := (s6.normKa b s1.bA s1.b1).2
      rwa [s1.Kb] at this
    have h := p7a_core hi kp hMel (haM b s1.bA) hyM s1.compL s1.quasiL s4.tL s6.yL.1 hJ0K s6.J0M
    rw [h.1]
    exact h.2.2 s6.yL s6.yLnt

structure S7bFacts (A : Subgroup G) (y : G) (J0 : Subgroup G) : Prop where
  I1comp : GLAPComponent 3 (Cs y) (Iof y J0 ⊥)
  I1norm : A ≤ Subgroup.normalizer (Iof y J0 ⊥ : Set G)
  Icomp : ∀ a ∈ A, a ≠ 1 → GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs a) (Iof y J0 (Subgroup.zpowers a))

omit [Finite G] in
theorem p7b_ne_bot {X L : Subgroup G} [Finite G] (h : GLAPComponent 3 X L) : L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore 3 ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

omit [Finite G] in
theorem p7b_CD_zpowers (g : G) : CD (Subgroup.zpowers g) = Cs g := by
  rw [Subgroup.zpowers_eq_closure]; exact Subgroup.centralizer_closure _

omit [Finite G] in
theorem p7b_CD_sup (S T : Subgroup G) : CD (S ⊔ T) = CD S ⊓ CD T := by
  rw [Subgroup.sup_eq_closure]
  show Subgroup.centralizer ((Subgroup.closure ((S : Set G) ∪ T) : Subgroup G) : Set G) = _
  rw [Subgroup.centralizer_closure]
  ext z
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_union, SetLike.mem_coe]
  constructor
  · intro h
    exact ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩
  · rintro ⟨h1, h2⟩ g (hg | hg)
    · exact h1 g hg
    · exact h2 g hg

omit [Finite G] in
theorem p7b_norm_of_conj_le {K : Subgroup G} {e : G} (h1 : GLBConj e K ≤ K)
    (h2 : GLBConj e⁻¹ K ≤ K) : e ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have : e * z * e⁻¹ ∈ GLBConj e⁻¹ K := mem_gLBConj.2 (by rw [show e⁻¹ * (e * z * e⁻¹) * e⁻¹⁻¹ = z by group]; exact hz)
    exact h2 this
  · intro hz
    exact h1 (mem_gLBConj.2 hz)

omit [Finite G] in
theorem p7b_layer_le_conj (g : G) (X : Subgroup G) :
    GLBConj g (GLAPLayer 3 X) ≤ GLAPLayer 3 (GLBConj g X) := by
  refine (Subgroup.map_le_iff_le_comap).2 (sSup_le fun L hL => ?_)
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hL g)

omit [Finite G] in
theorem p7b_mem_norm_layer {X : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (X : Set G)) :
    e ∈ Subgroup.normalizer (GLAPLayer 3 X : Set G) := by
  refine p7b_norm_of_conj_le ?_ ?_
  · have := p7b_layer_le_conj e X
    rwa [gLBConj_eq_of_mem_normalizer he] at this
  · have := p7b_layer_le_conj e⁻¹ X
    rwa [gLBConj_eq_of_mem_normalizer (inv_mem he)] at this

omit [Finite G] in
theorem p7b_ncl_conj_le {H J : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (H : Set G))
    (hJ : GLBConj e J = J) : GLBConj e (ncl H J) ≤ ncl H J := by
  refine (Subgroup.map_le_iff_le_comap).2 (iSup₂_le fun g hg => ?_)
  rw [← Subgroup.map_le_iff_le_comap]
  show GLBConj e (GLBConj g J) ≤ ncl H J
  have hmem : e⁻¹ * g * e ∈ H := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem he) g).1 hg
    simpa [mul_assoc] using this
  have : GLBConj e (GLBConj g J) = GLBConj (e⁻¹ * g * e) J := by
    conv_rhs => rw [← hJ]
    rw [gLBConj_gLBConj, gLBConj_gLBConj]
    congr 1
    group
  rw [this]
  exact le_iSup₂ (f := fun g (_ : g ∈ H) => GLBConj g J) (e⁻¹ * g * e) hmem

omit [Finite G] in
theorem p7b_mem_norm_ncl {H J : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (H : Set G))
    (hJ : GLBConj e J = J) : e ∈ Subgroup.normalizer (ncl H J : Set G) := by
  refine p7b_norm_of_conj_le (p7b_ncl_conj_le he hJ) (p7b_ncl_conj_le (inv_mem he) ?_)
  have := congrArg (GLBConj e⁻¹) hJ
  rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
  exact this.symm

omit [Finite G] in
theorem p7b_gLBConj_eq_of_comm {J : Subgroup G} {e : G} (hJ : ∀ j ∈ J, e * j = j * e) :
    GLBConj e J = J := by
  ext j
  rw [mem_gLBConj]
  constructor
  · intro h
    have h1 := hJ _ h
    have : e * j * e⁻¹ = j := by
      have h2 : e * (e * j * e⁻¹) = e * j := by
        rw [h1]; group
      have := mul_left_cancel h2
      exact this
    rwa [this] at h
  · intro h
    rw [show e * j * e⁻¹ = j by rw [hJ j h]; group]
    exact h

theorem s7b_I1 {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    {q q0 : ℕ} {y0 y : G} {J0 : Subgroup G} (s5 : S5Facts V L A b x q0 y0 J0)
    (s6 : S6Facts V L A b x y0 y J0) (s7a : S7aFacts L A b x y q J0) : S7bFacts A y J0 := by
  classical
  have hKP := ctx_kproper c
  set E : Subgroup G := A ⊔ Subgroup.zpowers y with hE
  have hAE : A ≤ E := le_sup_left
  have hyE : y ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hMel : IsElemAbelian 3 E := s6.Mel
  have hcomm : ∀ e ∈ E, ∀ g ∈ E, e * g = g * e := fun e he g hg => comm_of_isElemAbelian' hMel he hg
  have hinCD : ∀ e ∈ A, ∀ D : Subgroup G, D ≤ E → e ∈ CD D := fun e he D hD => by
    rw [Subgroup.mem_centralizer_iff]
    exact fun h hh => hcomm h (hD hh) e (hAE he)
  have hJ0cd : J0 ≤ CD E := s6.J0M.1
  have hJe : ∀ e ∈ A, GLBConj e J0 = J0 := fun e he =>
    p7b_gLBConj_eq_of_comm (fun j hj => by
      have := Subgroup.mem_centralizer_iff.1 (hJ0cd hj) e (hAE he)
      exact this)
  have hzy : Subgroup.zpowers y ≤ E := Subgroup.zpowers_le.2 hyE
  have hza : ∀ a ∈ A, Subgroup.zpowers a ≤ E := fun a ha => Subgroup.zpowers_le.2 (hAE ha)
  have hI1def : Iof y J0 ⊥ = ncl (GLAPLayer 3 (CD (Subgroup.zpowers y))) J0 := by
    unfold Iof; rw [sup_bot_eq]
  obtain ⟨𝒞, hcomp, hsup, hstab, htrans⟩ :=
    hi.i1834 G hKP (Subgroup.zpowers y) E hMel hzy J0 s6.J0M
  simp only [p7b_CD_zpowers] at hcomp hsup
  rw [p7b_CD_zpowers] at hI1def

  have hI1 : Iof y J0 ⊥ = ⨆ C ∈ 𝒞, C := hI1def.trans hsup.symm
  have hAy : ∀ e ∈ A, e ∈ Cs y := fun e he => by
    have := hinCD e he (Subgroup.zpowers y) hzy
    rwa [p7b_CD_zpowers] at this
  have hAstab : ∀ C ∈ 𝒞, ∀ e ∈ A, GLBConj e C ∈ 𝒞 := fun C hC e he => hstab C hC e (hAE he)
  have hAtrans : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ e ∈ A, GLBConj e C = C' := by
    intro C hC C' hC'
    obtain ⟨e, he, hCe⟩ := htrans C hC C' hC'
    have key : ∃ a ∈ A, ∀ D ∈ 𝒞, GLBConj e D = GLBConj a D := by
      have he' : e ∈ Subgroup.closure ((A : Set G) ∪ (Subgroup.zpowers y : Set G)) := by
        rwa [← Subgroup.sup_eq_closure]
      refine Subgroup.closure_induction
        (p := fun g _ => ∃ a ∈ A, ∀ D ∈ 𝒞, GLBConj g D = GLBConj a D) ?_ ?_ ?_ ?_ he'
      · intro g hg
        rcases hg with hg | hg
        · exact ⟨g, hg, fun _ _ => rfl⟩
        · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
          refine ⟨1, A.one_mem, fun D hD => ?_⟩
          have hDy : D ≤ Cs y := (hcomp D hD).1
          rw [gLBConj_one]
          refine p7b_gLBConj_eq_of_comm (fun d hd => ?_)
          have hd' : y * d = d * y := by
            have := Subgroup.mem_centralizer_iff.1 (hDy hd) y rfl
            exact this
          exact (Commute.zpow_left (show Commute y d from hd') k).eq
      · exact ⟨1, A.one_mem, fun _ _ => rfl⟩
      · rintro g1 g2 - - ⟨a1, ha1, h1⟩ ⟨a2, ha2, h2⟩
        refine ⟨a1 * a2, A.mul_mem ha1 ha2, fun D hD => ?_⟩
        calc GLBConj (g1 * g2) D = GLBConj g2 (GLBConj g1 D) := (gLBConj_gLBConj g2 g1 D).symm
          _ = GLBConj g2 (GLBConj a1 D) := by rw [h1 D hD]
          _ = GLBConj a2 (GLBConj a1 D) := h2 _ (hAstab D hD a1 ha1)
          _ = GLBConj (a1 * a2) D := gLBConj_gLBConj a2 a1 D
      · rintro g hg ⟨a, ha, h⟩
        have hgE : g ∈ E := by rwa [hE, Subgroup.sup_eq_closure]
        refine ⟨a⁻¹, A.inv_mem ha, fun D hD => ?_⟩
        have hD' : GLBConj g⁻¹ D ∈ 𝒞 := hstab D hD g⁻¹ (E.inv_mem hgE)
        have h' := h _ hD'
        have e1 : GLBConj g (GLBConj g⁻¹ D) = D := by
          rw [gLBConj_gLBConj, inv_mul_cancel, gLBConj_one]
        have e2 : GLBConj a (GLBConj g⁻¹ D) = D := h'.symm.trans e1
        calc GLBConj g⁻¹ D = GLBConj a⁻¹ (GLBConj a (GLBConj g⁻¹ D)) := by
              rw [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
          _ = GLBConj a⁻¹ D := by rw [e2]
    obtain ⟨a, ha, hD⟩ := key
    exact ⟨a, ha, by rw [← hCe, hD C hC]⟩
  have hLay : ∀ a ∈ A, GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a)) ≤
      GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ ⊥)) := by
    intro a ha
    have pz : IsPGroup 3 (Subgroup.zpowers y) := (Lemma514Ns.isPGroup_of_isElemAbelian' hMel).to_le hzy
    have pa : IsPGroup 3 (Subgroup.zpowers a) := (Lemma514Ns.isPGroup_of_isElemAbelian' hMel).to_le (hza a ha)
    have hc : ∀ d ∈ Subgroup.zpowers y, ∀ e ∈ Subgroup.zpowers a, d * e = e * d :=
      fun d hd e he => hcomm d (hzy hd) e (hza a ha he)
    rw [sup_bot_eq]
    calc GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a))
        = GLAPLayer 3 (CD (Subgroup.zpowers y) ⊓ CD (Subgroup.zpowers a)) := by rw [p7b_CD_sup]
      _ = GLAPLayer 3 (GLAPLayer 3 (CD (Subgroup.zpowers y)) ⊓ CD (Subgroup.zpowers a)) :=
          (hi.i182 G hKP _ _ pz pa hc).symm
      _ ≤ GLAPLayer 3 (CD (Subgroup.zpowers y)) := (glaPLayer_le' _ _).trans inf_le_left
  have hIa_le : ∀ a ∈ A, Iof y J0 (Subgroup.zpowers a) ≤ Iof y J0 ⊥ := by
    intro a ha
    unfold Iof ncl
    exact iSup₂_le fun g hg =>
      le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ ⊥))) => GLBConj g J0) g
        (hLay a ha hg)
  have hNnorm : ∀ a ∈ A, A ≤ Subgroup.normalizer (Iof y J0 (Subgroup.zpowers a) : Set G) := by
    intro a ha e he
    exact p7b_mem_norm_ncl (H := GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a)))
      (J := J0)
      (p7b_mem_norm_layer (Subgroup.le_normalizer (hinCD e he _ (sup_le hzy (hza a ha)))))
      (hJe e he)
  have hfix : ∀ a ∈ A, a ≠ 1 → ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, ∃ k : ℕ, GLBConj (a ^ k) C = C' := by
    intro a ha ha1
    exact hi.fixcomp G hKP (Cs y) 𝒞 A a (Iof y J0 (Subgroup.zpowers a)) (fun C hC => hcomp C hC)
      (fun e he => hAy e he) s1.Ael hAstab hAtrans ha (s7a.Icomp a ha ha1)
      ((hIa_le a ha).trans hI1.le) (hNnorm a ha)
  have hJ0I : J0 ≤ Iof y J0 ⊥ := by
    unfold Iof ncl
    exact le_trans (by rw [gLBConj_one]) (le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ ⊥))) => GLBConj g J0) 1 (one_mem _))
  obtain ⟨C0, hC0⟩ : 𝒞.Nonempty := by
    rcases 𝒞.eq_empty_or_nonempty with h | h
    · exfalso
      have : Iof y J0 ⊥ = ⊥ := by rw [hI1, h]; simp
      exact p7b_ne_bot s6.J0M (le_bot_iff.1 (this ▸ hJ0I))
    · exact h
  have hsing : ∀ C ∈ 𝒞, C = C0 := by
    have hA9 : Nat.card A = 9 := s1.Acard
    have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.1 (by rw [hA9]; norm_num)
    obtain ⟨⟨a0, h0⟩, hne⟩ := exists_ne (1 : A)
    have ha01 : a0 ≠ 1 := fun h => hne (Subtype.ext h)
    have ha03 : a0 ^ 3 = 1 := s1.Ael.2 a0 h0
    have hk : ∀ e : A, ∃ k : Fin 3, GLBConj (a0 ^ (k : ℕ)) C0 = GLBConj (e : G) C0 := by
      intro e
      obtain ⟨k, hk⟩ := hfix a0 h0 ha01 C0 hC0 (GLBConj (e : G) C0) (hAstab C0 hC0 e e.2)
      refine ⟨⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
      rw [← hk]
      congr 1
      conv_rhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, ha03, one_pow, one_mul]
    choose f hf using hk
    have : Fintype A := Fintype.ofFinite A
    have hcard : Fintype.card (Fin 3) < Fintype.card A := by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card (α := A), hA9]; norm_num
    obtain ⟨e1, e2, hne12, hfe⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
    have hee : GLBConj (e1 : G) C0 = GLBConj (e2 : G) C0 := by
      rw [← hf e1, ← hf e2, hfe]
    have hstabC0 : GLBConj ((e2 : G) * (e1 : G)⁻¹) C0 = C0 := by
      have := congrArg (GLBConj ((e1 : G)⁻¹)) hee
      rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
      exact this.symm
    have hmemA : (e2 : G) * (e1 : G)⁻¹ ∈ A := A.mul_mem e2.2 (A.inv_mem e1.2)
    have hne1 : (e2 : G) * (e1 : G)⁻¹ ≠ 1 := by
      intro h
      apply hne12
      apply Subtype.ext
      exact (mul_inv_eq_one.1 h).symm
    have hpow : ∀ k : ℕ, GLBConj (((e2 : G) * (e1 : G)⁻¹) ^ k) C0 = C0 := by
      intro k
      induction k with
      | zero => simp [gLBConj_one]
      | succ k ih =>
        rw [pow_succ, ← gLBConj_gLBConj, ih, hstabC0]
    intro C hC
    obtain ⟨k, hk⟩ := hfix _ hmemA hne1 C0 hC0 C hC
    rw [← hk, hpow k]
  have hI1eq : Iof y J0 ⊥ = C0 := by
    rw [hI1]
    exact le_antisymm (iSup₂_le fun C hC => (hsing C hC).le)
      (le_iSup₂ (f := fun C (_ : C ∈ 𝒞) => C) C0 hC0)
  refine ⟨?_, ?_, ?_⟩
  · rw [hI1eq]; exact hcomp C0 hC0
  · intro e he
    exact p7b_mem_norm_ncl (H := GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ ⊥))) (J := J0)
      (p7b_mem_norm_layer (Subgroup.le_normalizer (hinCD e he _ (sup_le hzy bot_le))))
      (hJe e he)
  · intro a ha ha1
    have hI1y : Iof y J0 ⊥ ≤ Cs y := by rw [hI1eq]; exact (hcomp C0 hC0).1
    exact gl_comp_restrict (s7a.Icomp a ha ha1)
      (le_inf (hIa_le a ha) ((s7a.Icomp a ha ha1).1.trans inf_le_right))
      (inf_le_inf_right _ hI1y)

structure S7cFacts (A : Subgroup G) (b x y : G) (J0 : Subgroup G) : Prop where
  bIx : InducesFieldAutN 2 (Iof y J0 (Subgroup.zpowers x)) b ∧
    ¬ TrivOn (Iof y J0 (Subgroup.zpowers x)) b
  xIb : InducesFieldAutN 2 (Iof y J0 (Subgroup.zpowers b)) x ∧
    ¬ TrivOn (Iof y J0 (Subgroup.zpowers b)) x
  xI1 : ¬ TrivOn (Iof y J0 ⊥) x
  bI1 : ¬ TrivOn (Iof y J0 ⊥) b

theorem p7c_gLBConj_iSup_le {g : G} {ι : Sort*} {P : ι → Prop} {F : ι → Subgroup G}
    {T : Subgroup G} (h : ∀ i, P i → GLBConj g (F i) ≤ T) :
    GLBConj g (⨆ (i) (_ : P i), F i) ≤ T := by
  unfold GLBConj at h ⊢
  rw [Subgroup.map_le_iff_le_comap]
  exact iSup₂_le fun i hi => Subgroup.map_le_iff_le_comap.1 (h i hi)

theorem p7c_mem_normalizer_of_gLBConj_le {g : G} {T : Subgroup G} (h₁ : GLBConj g T ≤ T)
    (h₂ : GLBConj g⁻¹ T ≤ T) : g ∈ Subgroup.normalizer (T : Set G) := by
  refine mem_normalizer_iff_gLBConj_eq.2 (le_antisymm h₁ ?_)
  have h := gLBConj_mono g h₂
  rwa [gLBConj_gLBConj_inv] at h

theorem p7c_normalizer_layer {C : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer (GLAPLayer 3 C : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (C : Set G),
      GLBConj g (GLAPLayer 3 C) ≤ GLAPLayer 3 C := by
    intro g hg
    have hC : GLBConj g C = C := mem_normalizer_iff_gLBConj_eq.1 hg
    have h1 : GLBConj g (GLAPLayer 3 C) =
        ⨆ K ∈ {L | GLAPComponent 3 C L}, GLBConj g K := by
      unfold GLAPLayer GLBConj
      rw [sSup_eq_iSup, Subgroup.map_iSup]
      simp only [Subgroup.map_iSup]
    rw [h1]
    refine iSup₂_le fun K hK => ?_
    have := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK g
    rw [hC] at this
    exact le_sSup this
  exact p7c_mem_normalizer_of_gLBConj_le (key g hg) (key g⁻¹ ((Subgroup.normalizer _).inv_mem hg))

theorem p7c_gLBConj_Iof_le {y g : G} {J0 D : Subgroup G}
    (hgC : g ∈ CD (Subgroup.zpowers y ⊔ D)) (hgJ : g ∈ CD J0) :
    GLBConj g (Iof y J0 D) ≤ Iof y J0 D := by
  unfold Iof ncl
  refine p7c_gLBConj_iSup_le fun k hk => ?_
  have hgN : g ∈ Subgroup.normalizer (GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ D)) : Set G) :=
    p7c_normalizer_layer (Subgroup.le_normalizer hgC)
  have hgJN : g ∈ Subgroup.normalizer (J0 : Set G) := Subgroup.centralizer_le_normalizer _ hgJ
  have hh : g⁻¹ * k * g ∈ GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ D)) := by
    have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hgN) k).1 hk
    simpa using this
  rw [gLBConj_gLBConj]
  have e : k * g = g * (g⁻¹ * k * g) := by group
  rw [e, ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer hgJN]
  exact le_iSup₂_of_le (f := fun k (_ : k ∈ GLAPLayer 3 (CD (Subgroup.zpowers y ⊔ D))) =>
    GLBConj k J0) _ hh le_rfl

theorem p7c_mem_normalizer_Iof {y g : G} {J0 D : Subgroup G}
    (hgC : g ∈ CD (Subgroup.zpowers y ⊔ D)) (hgJ : g ∈ CD J0) :
    g ∈ Subgroup.normalizer (Iof y J0 D : Set G) :=
  p7c_mem_normalizer_of_gLBConj_le (p7c_gLBConj_Iof_le hgC hgJ)
    (p7c_gLBConj_Iof_le (inv_mem hgC) (inv_mem hgJ))

open scoped commutatorElement in
theorem p7c_center_equiv {Q P : Type*} [Group Q] [Group P] (hQc : commutator Q = ⊤)
    (hQs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (hPs : IsSimpleGroup (P ⧸ Subgroup.center P))
    (Θ : Q →* P) (hΘ : Function.Surjective Θ) :
    Nonempty ((Q ⧸ Subgroup.center Q) ≃* (P ⧸ Subgroup.center P)) := by
  set Φ : Q →* P ⧸ Subgroup.center P := (QuotientGroup.mk' (Subgroup.center P)).comp Θ with hΦdef
  have hΦ : Function.Surjective Φ := (QuotientGroup.mk'_surjective _).comp hΘ
  have hK : Φ.ker = Subgroup.center Q := by
    apply le_antisymm
    · intro k hk
      have : (Φ.ker.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
        Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
      rcases hQs.eq_bot_or_eq_top_of_normal
        (Φ.ker.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
      · have : QuotientGroup.mk' (Subgroup.center Q) k ∈ (⊥ : Subgroup _) :=
          h ▸ Subgroup.mem_map_of_mem _ hk
        rwa [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      · exfalso
        have hq : ∀ q : Q, ∃ z ∈ Subgroup.center Q, Φ q = Φ z := by
          intro q
          have : QuotientGroup.mk' (Subgroup.center Q) q ∈
              Φ.ker.map (QuotientGroup.mk' (Subgroup.center Q)) := by rw [h]; trivial
          obtain ⟨k', hk', hkq⟩ := this
          refine ⟨k'⁻¹ * q, QuotientGroup.eq.1 hkq, ?_⟩
          rw [map_mul, map_inv, MonoidHom.mem_ker.1 hk', inv_one, one_mul]
        have hc : commutator Q ≤ Φ.ker := by
          rw [commutator_def]
          refine Subgroup.commutator_le.2 fun q1 _ q2 _ => ?_
          obtain ⟨z1, hz1, e1⟩ := hq q1
          obtain ⟨z2, hz2, e2⟩ := hq q2
          rw [MonoidHom.mem_ker, map_commutatorElement, e1, e2, ← map_commutatorElement]
          have : ⁅z1, z2⁆ = (1 : Q) := by
            rw [commutatorElement_eq_one_iff_mul_comm]
            exact (Subgroup.mem_center_iff.1 hz2 z1)
          rw [this, map_one]
        rw [hQc] at hc
        have := hPs.toNontrivial
        obtain ⟨x, hx⟩ := exists_ne (1 : P ⧸ Subgroup.center P)
        obtain ⟨q, rfl⟩ := hΦ x
        exact hx (MonoidHom.mem_ker.1 (hc trivial))
    · intro z hz
      rw [MonoidHom.mem_ker, hΦdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro p
      obtain ⟨q, rfl⟩ := hΘ p
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz q]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hK.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ hΦ)⟩

theorem p7c_typeL2_of_cover {K J : Subgroup G} (hJK : J ≤ K)
    (hcov : K ≤ J ⊔ GLAPPrimeCoreOf 3 K)
    (hKq : CFSG.Open.IsQuasisimple (barOf 3 K)) (hJq : CFSG.Open.IsQuasisimple (barOf 3 J))
    {r : ℕ} (h : IsTypeL2 r (barOf 3 J)) : IsTypeL2 r (barOf 3 K) := by
  obtain ⟨F, hF, hFin, hcard, ⟨e⟩⟩ := h
  set f : ↥J →* barOf 3 K :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)).comp (Subgroup.inclusion hJK) with hfdef
  have hsup : (J.subgroupOf K) ⊔ GLAPPrimeCore 3 ↥K = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : (z : G) ∈ J ⊔ GLAPPrimeCoreOf 3 K := hcov z.2
    have hmap : (z : G) ∈ ((J.subgroupOf K) ⊔ GLAPPrimeCore 3 ↥K).map K.subtype := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJK]
      exact hz
    obtain ⟨w, hw, hwz⟩ := hmap
    have : w = z := Subtype.ext hwz
    rwa [this] at hw
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    have hz : z ∈ (J.subgroupOf K) ⊔ GLAPPrimeCore 3 ↥K := by rw [hsup]; trivial
    have hm : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) z ∈
        ((J.subgroupOf K) ⊔ GLAPPrimeCore 3 ↥K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) :=
      Subgroup.mem_map_of_mem _ hz
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at hm
    obtain ⟨w, hw, hwz⟩ := hm
    exact ⟨⟨w, (Subgroup.mem_subgroupOf).1 hw⟩, hwz⟩
  have hker : f.ker ≤ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).ker := by
    intro j hj
    have h1 : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) (Subgroup.inclusion hJK j) = 1 := hj
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    set N : Subgroup ↥J := (GLAPPrimeCoreOf 3 K).subgroupOf J with hN
    have hnorm : N.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have h2 := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_glaPPrimeCoreOf 3 K (hJK g.2)) (n : G)).1 ((Subgroup.mem_subgroupOf).1 hn)
      exact (Subgroup.mem_subgroupOf).2 (by simpa using h2)
    have hcop : Nat.Coprime 3 (Nat.card N) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hdvd => ?_
      refine not_dvd_card_glaPPrimeCoreOf Nat.prime_three K (hdvd.trans ?_)
      have hc : Nat.card (N.map J.subtype) = Nat.card N :=
        Subgroup.card_map_of_injective J.subtype_injective
      rw [← hc]
      refine Subgroup.card_dvd_of_le ?_
      rintro _ ⟨k, hk, rfl⟩
      exact (Subgroup.mem_subgroupOf).1 hk
    have hNle : N ≤ GLAPPrimeCore 3 ↥J := le_sSup ⟨hnorm, hcop⟩
    have hjN : j ∈ N := (Subgroup.mem_subgroupOf).2 ⟨_, h1, rfl⟩
    exact (QuotientGroup.eq_one_iff _).2 (hNle hjN)
  set Θ : barOf 3 K →* barOf 3 J :=
    (QuotientGroup.lift f.ker (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)) hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.toMonoidHom with hΘdef
  have hΘ : Function.Surjective Θ := by
    intro p
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective p
    refine ⟨f j, ?_⟩
    simp only [hΘdef, MonoidHom.comp_apply]
    have : (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f j) = (j : ↥J ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, this]; rfl
  obtain ⟨e'⟩ := p7c_center_equiv hKq.1 hKq.2 hJq.2 Θ hΘ
  exact ⟨F, hF, hFin, hcard, ⟨e'.trans e⟩⟩

theorem p7c_one_lt {r : ℕ} {Y : Type*} [Group Y] (h : IsTypeL2 r Y) : 1 < r := by
  obtain ⟨F, hF, hFin, hcard, _⟩ := h
  rw [← hcard]
  exact Finite.one_lt_card

theorem p7c_nontriv_I1 {V : InndiagVocab} {y : G} (hi : Inputs V) {I1 Ia Ia' : Subgroup G} {a a' : G} {q : ℕ}
    (hI1 : GLAPComponent 3 (Cs y) I1) (hIa : GLAPComponent 3 (I1 ⊓ Cs a) Ia)
    (hIa' : GLAPComponent 3 (I1 ⊓ Cs a') Ia') (ha3 : a ^ 3 = 1) (ha'3 : a' ^ 3 = 1)
    (hN1 : a' ∈ Subgroup.normalizer (I1 : Set G)) (hNa : a' ∈ Subgroup.normalizer (Ia : Set G))
    (hnt : ¬ TrivOn Ia a') (hqa : IsTypeL2 q (barOf 3 Ia)) (hqa' : IsTypeL2 q (barOf 3 Ia')) :
    ¬ TrivOn I1 a := by
  intro htriv
  have hq1 : CFSG.Open.IsQuasisimple (barOf 3 I1) := gl_quasi_barOf hI1
  obtain ⟨hcomp, hcov⟩ := hi.l3T G I1 a hq1 ha3 htriv
  have hle : Ia ≤ CLay I1 a := le_sSup hIa
  have heq : Ia = CLay I1 a := gl_comp_eq_of_le hcomp hIa hle
  rw [← heq] at hcov
  have hIaI1 : Ia ≤ I1 := hIa.1.trans inf_le_left
  have htype : IsTypeL2 q (barOf 3 I1) :=
    p7c_typeL2_of_cover hIaI1 hcov hq1 (gl_quasi_barOf hIa) hqa
  have hq : 1 < q := p7c_one_lt hqa
  rcases hi.l2fld G I1 a' q q hq1 htype hN1 ha'3 Ia' hIa' hqa' with h | ⟨_, _, h⟩
  · exact hnt (gl_trivOn_restrict hIaI1 hNa h.1)
  · have : q ^ 3 > q := by nlinarith [Nat.mul_le_mul hq hq]
    have h2 : 2 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega

theorem p7c_cd_of_mel {M S : Subgroup G} (hMel : IsElemAbelian 3 M) {g : G} (hg : g ∈ M)
    (hS : S ≤ M) : g ∈ CD S :=
  Subgroup.mem_centralizer_iff.2 fun h hh => comm_of_isElemAbelian' hMel (hS hh) hg

theorem p7c_cd_J0 {M J0 : Subgroup G} (hJ : J0 ≤ CD M) {g : G} (hg : g ∈ M) : g ∈ CD J0 :=
  Subgroup.mem_centralizer_iff.2 fun j hj => ((Subgroup.mem_centralizer_iff.1 (hJ hj)) g hg).symm

theorem p7c_cs_symm {z y : G} (h : z ∈ Cs y) : y ∈ Cs z := by
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  exact h.symm

theorem p7c_mem_CD {A : Subgroup G} {z y : G} (hA : A ≤ Cs z) (hy : y ∈ Cs z) :
    z ∈ CD (A ⊔ Subgroup.zpowers y) := by
  refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
  have h1 : h ∈ Cs z := sup_le hA (Subgroup.zpowers_le.2 hy) hh
  exact ((Subgroup.mem_centralizer_iff.1 h1) z rfl).symm

theorem p7c_field_part {V : InndiagVocab} (hi : Inputs V) {A : Subgroup G} {a a' y : G}
    {J0 : Subgroup G} {q q0 : ℕ}
    (hA : Subgroup.zpowers a ⊔ Subgroup.zpowers a' = A)
    (hIcomp : GLAPComponent 3 (Cs y ⊓ Cs a) (Iof y J0 (Subgroup.zpowers a)))
    (J0I : J0 ≤ Iof y J0 (Subgroup.zpowers a))
    (J0M : GLAPComponent 3 (CD (A ⊔ Subgroup.zpowers y)) J0)
    (hnorm : a' ∈ Subgroup.normalizer (Iof y J0 (Subgroup.zpowers a) : Set G))
    (ha'3 : a' ^ 3 = 1)
    (hI2 : IsTypeL2 q (barOf 3 (Iof y J0 (Subgroup.zpowers a))))
    (hJ0t : IsTypeL2 q0 (barOf 3 J0)) (hq : q = q0 ^ 3) :
    InducesFieldAutN 2 (Iof y J0 (Subgroup.zpowers a)) a' ∧
      ¬ TrivOn (Iof y J0 (Subgroup.zpowers a)) a' := by
  have ha'A : a' ∈ A := hA ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers a'))
  have haA : a ∈ A := hA ▸ (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hAM : A ≤ A ⊔ Subgroup.zpowers y := le_sup_left
  have hJ0a' : J0 ≤ Cs a' := fun j hj => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (J0M.1 hj) a' (hAM ha'A)).symm
  have hle : Iof y J0 (Subgroup.zpowers a) ⊓ Cs a' ≤ CD (A ⊔ Subgroup.zpowers y) := by
    intro z hz
    obtain ⟨hzI, hza'⟩ := hz
    obtain ⟨hzy, hza⟩ := hIcomp.1 hzI
    refine p7c_mem_CD ?_ (p7c_cs_symm hzy)
    rw [← hA]
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact p7c_cs_symm hza
    · exact p7c_cs_symm hza'
  have hcomp : GLAPComponent 3 (Iof y J0 (Subgroup.zpowers a) ⊓ Cs a') J0 :=
    gl_comp_restrict J0M (le_inf J0I hJ0a') hle
  have hq0 : 1 < q0 := p7c_one_lt hJ0t
  rcases hi.l2fld G _ a' q q0 (gl_quasi_barOf hIcomp) hI2 hnorm ha'3 J0 hcomp hJ0t with
    h | ⟨h1, h2, _⟩
  · exfalso
    have : q0 ^ 3 > q0 := by nlinarith [Nat.mul_le_mul hq0 hq0]
    have h8 : 2 ^ 3 ≤ q0 ^ 3 := Nat.pow_le_pow_left hq0 3
    omega
  · exact ⟨h2, h1⟩

theorem s7c_fields {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    {q q0 : ℕ} (s4 : S4Facts V L A b x q q0) {y0 y : G} {J0 : Subgroup G}
    (s5 : S5Facts V L A b x q0 y0 J0) (s6 : S6Facts V L A b x y0 y J0)
    (s7a : S7aFacts L A b x y q J0) (s7b : S7bFacts A y J0) : S7cFacts A b x y J0 := by
  have hAM : A ≤ A ⊔ Subgroup.zpowers y := le_sup_left
  have hnorm : ∀ {g : G} {D : Subgroup G}, g ∈ A → D ≤ A →
      g ∈ Subgroup.normalizer (Iof y J0 D : Set G) := fun {g D} hg hD =>
    p7c_mem_normalizer_Iof
      (p7c_cd_of_mel s6.Mel (hAM hg) (sup_le le_sup_right (hD.trans hAM)))
      (p7c_cd_J0 s6.J0M.1 (hAM hg))
  have hxA : Subgroup.zpowers x ≤ A := Subgroup.zpowers_le.2 c.xA
  have hbA : Subgroup.zpowers b ≤ A := Subgroup.zpowers_le.2 s1.bA
  have hAeq' : Subgroup.zpowers b ⊔ Subgroup.zpowers x = A := by rw [sup_comm]; exact s1.Aeq
  have bIx := p7c_field_part hi s1.Aeq (s7a.Icomp x c.xA c.x1) (s7a.J0I x c.xA c.x1) s6.J0M
    (hnorm s1.bA hxA) s1.hb3 s7a.Ix2 s5.J0type s4.q3
  have xIb := p7c_field_part hi hAeq' (s7a.Icomp b s1.bA s1.b1) (s7a.J0I b s1.bA s1.b1) s6.J0M
    (hnorm c.xA hbA) s1.hx3 s7a.Ib2 s5.J0type s4.q3
  refine ⟨bIx, xIb, ?_, ?_⟩
  · exact p7c_nontriv_I1 hi s7b.I1comp (s7b.Icomp x c.xA c.x1) (s7b.Icomp b s1.bA s1.b1) s1.hx3
      s1.hb3 (s7b.I1norm s1.bA) (hnorm s1.bA hxA) bIx.2 s7a.Ix2 s7a.Ib2
  · exact p7c_nontriv_I1 hi s7b.I1comp (s7b.Icomp b s1.bA s1.b1) (s7b.Icomp x c.xA c.x1) s1.hb3
      s1.hx3 (s7b.I1norm c.xA) (hnorm c.xA hbA) xIb.2 s7a.Ib2 s7a.Ix2


theorem s7d_inn {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    {q q0 : ℕ} (s4 : S4Facts V L A b x q q0) {y0 y : G} {J0 : Subgroup G}
    (s5 : S5Facts V L A b x q0 y0 J0) (s6 : S6Facts V L A b x y0 y J0)
    (s7a : S7aFacts L A b x y q J0) (s7b : S7bFacts A y J0) (s7c : S7cFacts A b x y J0) :
    ∀ a ∈ A, IndInn V (Iof y J0 ⊥) a := by
  have hy : y ≠ 1 := fun h => s6.yA (h ▸ A.one_mem)
  have hKG : CFSG.IsKGroup ↥(Iof y J0 ⊥) := by
    obtain ⟨m, hS⟩ := c.stand
    refine p5_isKGroup_of_open (isKGroup_of_isKProper hS.kProper (C := Iof y J0 ⊥) ?_)
    intro htop
    have hle := s7b.I1comp.1
    rw [htop] at hle
    exact centralizer_singleton_ne_top hS hy (top_le_iff.1 hle)
  have hq0 : 2 ≤ q0 := by
    obtain ⟨F, _, hF, hcard, _⟩ := s5.J0type
    have := Finite.one_lt_card (α := F)
    omega
  have hJ0I : J0 ≤ Iof y J0 ⊥ := by
    intro w hw
    unfold Iof ncl
    exact Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (Subgroup.one_mem _)
      (by rw [gLBConj_one]; exact hw))
  have key : ∀ g h : G, g ∈ A → g ≠ 1 → g ^ 3 = 1 → h ∈ A → h ^ 3 = 1 → g * h = h * g →
      Subgroup.zpowers g ⊔ Subgroup.zpowers h = A →
      IsTypeL2 q (barOf 3 (Iof y J0 (Subgroup.zpowers g))) → IndInn V (Iof y J0 ⊥) g := by
    intro g h hg hg1 hg3 hh hh3 hgh hAgh hT
    by_contra hnot
    have hgn : g ∈ Subgroup.normalizer (Iof y J0 ⊥ : Set G) := s7b.I1norm hg
    have hhn : h ∈ Subgroup.normalizer (Iof y J0 ⊥ : Set G) := s7b.I1norm hh
    have hq10 : 10 ≤ q := by
      have h8 := s4.q8
      have h3 := s4.q3
      by_contra hlt
      have hq02 : q0 ≤ 2 := by
        by_contra hgt
        have := Nat.pow_le_pow_left (show 3 ≤ q0 by omega) 3
        omega
      have hq2 : q0 = 2 := by omega
      subst hq2
      omega
    have hq1 := hi.i92 G (Iof y J0 ⊥) (gl_quasi_barOf s7b.I1comp) hKG g hgn hg3 hnot _
      (s7b.Icomp g hg hg1) q hq10 hT
    have hI1y : Iof y J0 ⊥ ≤ Cs y := s7b.I1comp.1
    have hle : Iof y J0 ⊥ ⊓ Cs g ⊓ Cs h ≤ CD (A ⊔ Subgroup.zpowers y) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      have hsub : A ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({z} : Set G) := by
        refine sup_le ?_ ?_
        · rw [← hAgh]
          refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
          · have := Subgroup.mem_centralizer_iff.1 hz.1.2 g (by simp)
            simpa [Subgroup.mem_centralizer_iff, eq_comm] using this
          · have := Subgroup.mem_centralizer_iff.1 hz.2 h (by simp)
            simpa [Subgroup.mem_centralizer_iff, eq_comm] using this
        · refine Subgroup.zpowers_le.2 ?_
          have := Subgroup.mem_centralizer_iff.1 (hI1y hz.1.1) y (by simp)
          simpa [Subgroup.mem_centralizer_iff, eq_comm] using this
      intro w hw
      have := Subgroup.mem_centralizer_iff.1 (hsub hw) z (by simp)
      exact this.symm
    have hJ0le : J0 ≤ Iof y J0 ⊥ ⊓ Cs g ⊓ Cs h := by
      intro w hw
      have hwM := s6.J0M.1 hw
      have hgM : g ∈ A ⊔ Subgroup.zpowers y := (le_sup_left : A ≤ A ⊔ Subgroup.zpowers y) hg
      have hhM : h ∈ A ⊔ Subgroup.zpowers y := (le_sup_left : A ≤ A ⊔ Subgroup.zpowers y) hh
      refine ⟨⟨hJ0I hw, ?_⟩, ?_⟩
      · show w ∈ Subgroup.centralizer ({g} : Set G)
        rw [Subgroup.mem_centralizer_iff]; intro u hu
        rw [Set.mem_singleton_iff] at hu; subst hu
        exact Subgroup.mem_centralizer_iff.1 hwM _ hgM
      · show w ∈ Subgroup.centralizer ({h} : Set G)
        rw [Subgroup.mem_centralizer_iff]; intro u hu
        rw [Set.mem_singleton_iff] at hu; subst hu
        exact Subgroup.mem_centralizer_iff.1 hwM _ hhM
    have hcomp := gl_comp_restrict s6.J0M hJ0le hle
    have h3 := hi.l2exp G (Iof y J0 ⊥) g h (q ^ 3) q0 (gl_quasi_barOf s7b.I1comp) hq1 hgn hhn hg3
      hh3 hgh hnot J0 hcomp s5.J0type
    rcases h3 with h3 | ⟨_, h3⟩
    · rw [s4.q3, ← pow_mul] at h3
      have := Nat.pow_lt_pow_right (a := q0) (by omega) (by norm_num : 3 < 3 * 3)
      omega
    · have := Nat.pow_le_pow_left hq10 3
      norm_num at this
      omega
  have hx3 := s1.hx3
  have hb3 := s1.hb3
  have hbA := s1.bA
  have hxn : IndInn V (Iof y J0 ⊥) x :=
    key x b c.xA c.x1 hx3 hbA hb3 s1.hxb s1.Aeq (s7a.Ix2)
  have hbn : IndInn V (Iof y J0 ⊥) b :=
    key b x hbA s1.b1 hb3 c.xA hx3 s1.hxb.symm (by rw [sup_comm]; exact s1.Aeq) (s7a.Ib2)
  intro a ha
  rw [← s1.Aeq, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    ← Subgroup.closure_union] at ha
  induction ha using Subgroup.closure_induction with
  | mem w hw =>
    rcases hw with hw | hw
    · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hxn
    · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hbn
  | one => simpa using gl_indInn_pow hxn 0
  | mul u v _ _ hu hv => exact gl_indInn_mul hu hv
  | inv u _ hu =>
    have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
    have hpos := hfin.orderOf_pos
    have : u⁻¹ = u ^ (orderOf u - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    rw [this]; exact gl_indInn_pow hu _

def S8Facts (A : Subgroup G) (b y : G) (q0 : ℕ) (J0 : Subgroup G) : Prop :=
  ∃ (a : G) (H1 H2 H3 : Subgroup G), a ∈ A ∧ a ≠ 1 ∧ a ∉ Subgroup.zpowers b ∧
    GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs a) H1 ∧ GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs a) H2 ∧
    GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs a) H3 ∧ H1 ≠ H2 ∧ H1 ≠ H3 ∧ H2 ≠ H3 ∧
    CLay (Iof y J0 ⊥) a = H1 ⊔ H2 ⊔ H3 ∧
    (∀ H : Subgroup G, (H = H1 ∨ H = H2 ∨ H = H3) →
      ∃ r0 : ℕ, ¬ 3 ∣ r0 ∧ IsTypeL2 r0 (barOf 3 H)) ∧
    ∀ H H' : Subgroup G, (H = H1 ∨ H = H2 ∨ H = H3) → (H' = H1 ∨ H' = H2 ∨ H' = H3) →
      ∃ e ∈ A, GLBConj e H = H'

theorem p8_map_mem_statedSL (n : ℕ) {F : Type} [Field F] (σ : F ≃+* F) (A : ↥(StatedSL n F)) :
    Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin n) F) ∈ StatedSL n F := by
  have : StatedSL n F ≤ (StatedSL n F).comap (Matrix.GeneralLinearGroup.map (σ : F →+* F)) := by
    unfold StatedSL
    rw [Subgroup.closure_le]
    intro B hB
    apply Subgroup.subset_closure
    show (((Matrix.GeneralLinearGroup.map (σ : F →+* F) B : GL (Fin n) F)) :
      Matrix (Fin n) (Fin n) F).det = 1
    have h1 : (((Matrix.GeneralLinearGroup.map (σ : F →+* F) B : GL (Fin n) F)) :
      Matrix (Fin n) (Fin n) F) = (σ : F →+* F).mapMatrix (B : Matrix (Fin n) (Fin n) F) := rfl
    rw [h1, ← RingHom.map_det]
    have : (B : Matrix (Fin n) (Fin n) F).det = 1 := hB
    rw [this]; simp
  exact this A.2

theorem p8_isEntrywise_pow (n : ℕ) {F : Type} [Field F] (σ : F ≃+* F)
    (φ : MulAut (StatedProj (StatedSL n F))) (h : IsEntrywiseAutPSLn n σ φ) (j : ℕ) :
    IsEntrywiseAutPSLn n (σ ^ j) (φ ^ j) := by
  induction j with
  | zero =>
    intro A A' hA
    have : A' = A := by
      apply Subtype.ext; apply Units.ext
      simpa using hA
    subst this; simp
  | succ j ih =>
    intro A A' hA
    set A1 : ↥(StatedSL n F) :=
      ⟨Matrix.GeneralLinearGroup.map (σ : F →+* F) (A : GL (Fin n) F),
        p8_map_mem_statedSL n σ A⟩ with hA1
    have h1 : φ (QuotientGroup.mk A) = QuotientGroup.mk A1 := h A A1 rfl
    have h2 : (φ ^ j) (QuotientGroup.mk A1) = QuotientGroup.mk A' := by
      apply ih A1 A'
      rw [hA]
      ext i k
      simp [hA1, pow_succ]
    rw [pow_succ, MulAut.mul_apply, h1, h2]


theorem p8_isFieldAut_pow (n : ℕ) {Y : Type*} [Group Y] {α : MulAut Y}
    (h : IsFieldAutPSLn n α) (j : ℕ) : IsFieldAutPSLn n (α ^ j) := by
  obtain ⟨F, hF, hfin, θ, σ, φ, γ, hφ, hα⟩ := h
  refine ⟨F, hF, hfin, θ, σ ^ j, φ ^ j, γ, p8_isEntrywise_pow n σ φ hφ j, ?_⟩
  have key : ∀ (i : ℕ) (y : Y), θ (QuotientGroup.mk ((α ^ i) y)) =
      ((γ * φ * γ⁻¹) ^ i) (θ (QuotientGroup.mk y)) := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih =>
      intro y
      rw [pow_succ α i, MulAut.mul_apply, ih, hα, pow_succ (γ * φ * γ⁻¹) i]
      rfl
  intro y
  rw [key j y, conj_pow]

omit [Finite G] in
theorem p8_inducesFieldAutN_pow {n : ℕ} {K : Subgroup G} {g : G}
    (h : InducesFieldAutN n K g) (j : ℕ) : InducesFieldAutN n K (g ^ j) := by
  obtain ⟨hg, hf⟩ := h
  refine ⟨pow_mem hg j, ?_⟩
  have : barAut 3 K ⟨g ^ j, pow_mem hg j⟩ = (barAut 3 K ⟨g, hg⟩) ^ j := by
    rw [← map_pow]; rfl
  rw [this]
  exact p8_isFieldAut_pow n hf j

omit [Finite G] in
theorem p8_not_trivOn_pow {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    (hg3 : g ^ 3 = 1) (hnt : ¬ TrivOn K g) {j : ℕ} (hj : ¬ 3 ∣ j) : ¬ TrivOn K (g ^ j) := by
  rintro ⟨hgj, h1⟩
  apply hnt
  refine ⟨hg, ?_⟩
  have hk : ∃ k : ℕ, (g ^ j) ^ k = g := by
    have hj' : j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hj' with h | h
    · refine ⟨1, ?_⟩
      have : g ^ j = g ^ (j % 3) := by
        conv_lhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, hg3, one_pow, mul_one]
      rw [pow_one, this, h, pow_one]
    · refine ⟨2, ?_⟩
      have : g ^ j = g ^ (j % 3) := by
        conv_lhs => rw [← Nat.mod_add_div j 3, pow_add, pow_mul, hg3, one_pow, mul_one]
      rw [this, h, ← pow_mul, show 2 * 2 = 1 + 3 by norm_num, pow_add, hg3, mul_one, pow_one]
  obtain ⟨k, hk⟩ := hk
  have : barAut 3 K ⟨g, hg⟩ = (barAut 3 K ⟨g ^ j, hgj⟩) ^ k := by
    rw [← map_pow]
    congr 1
    apply Subtype.ext
    simpa using hk.symm
  rw [this, h1, one_pow]

omit [Finite G] in
theorem p8_mem_normalizer_of_le_cs {J : Subgroup G} {u : G} (h : J ≤ Cs u) :
    u ∈ Subgroup.normalizer (J : Set G) := by
  refine Subgroup.centralizer_le_normalizer (J : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.1 (h hk) u rfl).symm

omit [Finite G] in
theorem p8_inv_pow {u : G} (hu3 : u ^ 3 = 1) (i : ℕ) : (u ^ i)⁻¹ = u ^ (2 * i) :=
  inv_eq_of_mul_eq_one_right (by
    rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hu3, one_pow])

omit [Finite G] in
theorem p8_mem_sup_of_commute {u v a : G} (huv : u * v = v * u) (hu3 : u ^ 3 = 1)
    (hv3 : v ^ 3 = 1) (ha : a ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    ∃ i j : ℕ, a = v ^ j * u ^ i := by
  have hc : Commute u v := huv
  let S : Subgroup G :=
    { carrier := {a | ∃ i j : ℕ, a = v ^ j * u ^ i}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        refine ⟨i + i', j + j', ?_⟩
        calc v ^ j * u ^ i * (v ^ j' * u ^ i')
            = v ^ j * (u ^ i * v ^ j') * u ^ i' := by simp only [mul_assoc]
          _ = v ^ j * (v ^ j' * u ^ i) * u ^ i' := by rw [(hc.pow_pow i j').eq]
          _ = v ^ (j + j') * u ^ (i + i') := by rw [pow_add, pow_add]; simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨2 * i, 2 * j, ?_⟩
        rw [mul_inv_rev, p8_inv_pow hu3, p8_inv_pow hv3, (hc.pow_pow (2 * i) (2 * j)).eq] }
  have : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ S :=
    sup_le (Subgroup.zpowers_le.2 ⟨1, 0, by simp⟩) (Subgroup.zpowers_le.2 ⟨0, 1, by simp⟩)
  exact this ha

theorem p8_fieldHyp {u v : G} {A J : Subgroup G} (hA : Subgroup.zpowers u ⊔ Subgroup.zpowers v = A)
    (hu3 : u ^ 3 = 1) (hv3 : v ^ 3 = 1) (huv : u * v = v * u) (hJu : J ≤ Cs u)
    (hv : InducesFieldAutN 2 J v ∧ ¬ TrivOn J v) :
    ∀ a ∈ A, a ∉ Subgroup.zpowers u → InducesFieldAutN 2 J a ∧ ¬ TrivOn J a := by
  intro a haA hau
  obtain ⟨i, j, rfl⟩ := p8_mem_sup_of_commute huv hu3 hv3 (hA ▸ haA)
  have hj : ¬ 3 ∣ j := by
    rintro ⟨k, rfl⟩
    apply hau
    have : v ^ (3 * k) = 1 := by rw [pow_mul, hv3, one_pow]
    rw [this, one_mul]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers u) i
  obtain ⟨⟨hvN, hvf⟩, hvnt⟩ := hv
  have huN : u ∈ Subgroup.normalizer (J : Set G) := p8_mem_normalizer_of_le_cs hJu
  have huiN := pow_mem huN i
  have hJui : J ≤ Cs (u ^ i) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have : u * k = k * u := (Subgroup.mem_centralizer_iff.1 (hJu hk) u rfl)
    exact ((Commute.pow_left (show Commute u k from this) i).eq)
  have hTriv : TrivOn J (u ^ i) := gl_trivOn_of_le_centralizer hJui
  have hvjN := pow_mem hvN j
  have hmul : barAut 3 J ⟨v ^ j * u ^ i, mul_mem hvjN huiN⟩ = barAut 3 J ⟨v ^ j, hvjN⟩ := by
    rw [gl_barAut_mul hvjN huiN]
    obtain ⟨_, h1⟩ := hTriv
    rw [h1, mul_one]
  refine ⟨⟨mul_mem hvjN huiN, ?_⟩, ?_⟩
  · rw [hmul]
    exact (p8_inducesFieldAutN_pow ⟨hvN, hvf⟩ j).2
  · rintro ⟨hN, h1⟩
    refine p8_not_trivOn_pow hvN hv3 hvnt hj ⟨hvjN, ?_⟩
    rw [← hmul]; exact h1

theorem s8_apply {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    {q q0 : ℕ} (s4 : S4Facts V L A b x q q0) {y0 y : G} {J0 : Subgroup G}
    (s5 : S5Facts V L A b x q0 y0 J0) (s6 : S6Facts V L A b x y0 y J0)
    (s7a : S7aFacts L A b x y q J0) (s7b : S7bFacts A y J0) (s7c : S7cFacts A b x y J0)
    (s7d : ∀ a ∈ A, IndInn V (Iof y J0 ⊥) a) : S8Facts A b y q0 J0 := by
  have hKP := ctx_kproper c
  have hI1le : Iof y J0 ⊥ ≤ Cs y := s7b.I1comp.1
  have hy1 : y ∈ CD (Iof y J0 ⊥) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.1 (hI1le hk) y rfl).symm
  have hyN : y ∈ Subgroup.normalizer ((Iof y J0 ⊥ : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hy1
  have hCsy : Cs y ≠ ⊤ := by
    intro htop
    apply s6.yKnt
    exact gl_trivOn_of_le_centralizer (by rw [htop]; exact le_top)
  have hI1top : Iof y J0 ⊥ ≠ ⊤ := by
    intro h
    rw [h] at hI1le
    exact hCsy (top_le_iff.1 hI1le)
  have hMN : A ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer ((Iof y J0 ⊥ : Subgroup G) : Set G) :=
    sup_le s7b.I1norm (Subgroup.zpowers_le.2 hyN)
  have hrk : GLATwoLocalRank 3 ↥(Iof y J0 ⊥ ⊔ (A ⊔ Subgroup.zpowers y)) ≤ 4 := by
    calc _ ≤ GLATwoLocalRank 3 G :=
          CFSG.LocalAnalysis.GLTheoremB.glaTwoLocalRank_subgroup_le (by norm_num) _
      _ = 4 := c.c4.2.1
  have hq : ¬ 3 ∣ q ∧ q ≠ 8 := by
    rcases s4.tL with ⟨h, _⟩ | ⟨h, _⟩
    · omega
    · refine ⟨by omega, s4.q8 h⟩
  have hc : ∃ c ∈ A ⊔ Subgroup.zpowers y, c ≠ 1 ∧ c ∈ CD (Iof y J0 ⊥) :=
    ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y),
      fun h => s6.yA (by rw [h]; exact A.one_mem), hy1⟩
  have hIxle : Iof y J0 (Subgroup.zpowers x) ≤ Cs x :=
    (s7a.Icomp x c.xA c.x1).1.trans inf_le_right
  have hIble : Iof y J0 (Subgroup.zpowers b) ≤ Cs b :=
    (s7a.Icomp b s1.bA s1.b1).1.trans inf_le_right
  have h1 := hi.i1431 G (Iof y J0 ⊥) (A ⊔ Subgroup.zpowers y) (gl_quasi_barOf s7b.I1comp)
    (p5_isKGroup_of_open (isKGroup_of_isKProper hKP hI1top)) hMN hrk s6.Mel hc A x le_sup_left c.xA s1.Acard s7c.xI1
    (Iof y J0 (Subgroup.zpowers x)) (s7b.Icomp x c.xA c.x1) q s7a.Ix2 hq.1 hq.2 s7d
    (p8_fieldHyp s1.Aeq s1.hx3 s1.hb3 s1.hxb hIxle s7c.bIx)
  have h2 := hi.i1431 G (Iof y J0 ⊥) (A ⊔ Subgroup.zpowers y) (gl_quasi_barOf s7b.I1comp)
    (p5_isKGroup_of_open (isKGroup_of_isKProper hKP hI1top)) hMN hrk s6.Mel hc A b le_sup_left s1.bA s1.Acard s7c.bI1
    (Iof y J0 (Subgroup.zpowers b)) (s7b.Icomp b s1.bA s1.b1) q s7a.Ib2 hq.1 hq.2 s7d
    (p8_fieldHyp (by rw [sup_comm]; exact s1.Aeq) s1.hb3 s1.hx3 s1.hxb.symm hIble s7c.xIb)
  obtain ⟨-, -, a, haA, ha1, r0, hr0, H1, H2, H3, c1, c2, c3, n12, n13, n23, hlay, hty, htrans⟩ :=
    h1
  obtain ⟨-, hIb, -⟩ := h2
  have hr03 : ¬ 3 ∣ r0 := fun h => hq.1 (hr0 ▸ dvd_pow h (by norm_num))
  refine ⟨a, H1, H2, H3, haA, ha1, ?_, c1, c2, c3, n12, n13, n23, hlay,
    fun H hH => ⟨r0, hr03, hty H hH⟩, htrans⟩
  intro hab
  have hcs : Cs a = Cs b := centralizer_eq_of_mem_zpowers s1.Ael s1.bA s1.b1 hab ha1
  have hIbc := s7b.Icomp b s1.bA s1.b1
  have hLa : CLay (Iof y J0 ⊥) a = Iof y J0 (Subgroup.zpowers b) := by
    rw [hIb]
    show GLAPLayer 3 (Iof y J0 ⊥ ⊓ Cs a) = GLAPLayer 3 (Iof y J0 ⊥ ⊓ Cs b)
    rw [hcs]
  have c1' : GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs b) H1 := by rw [← hcs]; exact c1
  have c2' : GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs b) H2 := by rw [← hcs]; exact c2
  have hH1 : H1 ≤ Iof y J0 (Subgroup.zpowers b) := by
    rw [← hLa, hlay]; exact le_sup_left.trans le_sup_left
  have hH2 : H2 ≤ Iof y J0 (Subgroup.zpowers b) := by
    rw [← hLa, hlay]; exact le_sup_right.trans le_sup_left
  exact n12 ((gl_comp_eq_of_le hIbc c1' hH1).trans (gl_comp_eq_of_le hIbc c2' hH2).symm)

theorem p9a_comp_mem {X H1 H2 H3 K : Subgroup G} (h1 : GLAPComponent 3 X H1)
    (h2 : GLAPComponent 3 X H2) (h3 : GLAPComponent 3 X H3) (hK : GLAPComponent 3 X K)
    (hle : K ≤ H1 ⊔ H2 ⊔ H3) : K = H1 ∨ K = H2 ∨ K = H3 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n1, n2, n3⟩ := hcon
  have hcen : ∀ {H : Subgroup G}, GLAPComponent 3 X H → K ≠ H →
      barX 3 X K ≤ Subgroup.centralizer (barX 3 X H : Set _) := fun hH hne =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hK.2.2.1 hH.2.2.1
        (fun h => hne (glaPComponent_uniqueAux hK hH h)))
  have hbar : barX 3 X K ≤ barX 3 X H1 ⊔ barX 3 X H2 ⊔ barX 3 X H3 := by
    unfold barX
    have hsub : K.subgroupOf X ≤ H1.subgroupOf X ⊔ H2.subgroupOf X ⊔ H3.subgroupOf X := by
      have e : (H1 ⊔ H2 ⊔ H3).subgroupOf X =
          H1.subgroupOf X ⊔ H2.subgroupOf X ⊔ H3.subgroupOf X := by
        unfold Subgroup.subgroupOf
        have r1 : H1 ⊔ H2 ≤ X.subtype.range := by
          rw [Subgroup.range_subtype]; exact sup_le h1.1 h2.1
        have r2 : H3 ≤ X.subtype.range := by rw [Subgroup.range_subtype]; exact h3.1
        have r3 : H1 ≤ X.subtype.range := by rw [Subgroup.range_subtype]; exact h1.1
        have r4 : H2 ≤ X.subtype.range := by rw [Subgroup.range_subtype]; exact h2.1
        rw [Subgroup.comap_sup_eq_of_le_range X.subtype r3 r4,
          Subgroup.comap_sup_eq_of_le_range X.subtype r1 r2]
      rw [← e]
      intro w hw
      exact hle hw
    calc (K.subgroupOf X).map _ ≤ (H1.subgroupOf X ⊔ H2.subgroupOf X ⊔ H3.subgroupOf X).map _ :=
          Subgroup.map_mono hsub
      _ = _ := by rw [Subgroup.map_sup, Subgroup.map_sup]
  have hc1 := hcen h1 n1
  have hc2 := hcen h2 n2
  have hc3 := hcen h3 n3
  have hcomm : IsMulCommutative (barX 3 X K) := by
    refine ⟨⟨fun u v => ?_⟩⟩
    have hv : barX 3 X H1 ⊔ barX 3 X H2 ⊔ barX 3 X H3 ≤
        Subgroup.centralizer ({(v : ↥X ⧸ GLAPPrimeCore 3 ↥X)} : Set (↥X ⧸ GLAPPrimeCore 3 ↥X)) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro q hq
        exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff] at hh; subst hh
          exact (Subgroup.mem_centralizer_iff.1 (hc1 v.2) q hq).symm
      · intro q hq
        exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff] at hh; subst hh
          exact (Subgroup.mem_centralizer_iff.1 (hc2 v.2) q hq).symm
      · intro q hq
        exact Subgroup.mem_centralizer_iff.2 fun h hh => by
          rw [Set.mem_singleton_iff] at hh; subst hh
          exact (Subgroup.mem_centralizer_iff.1 (hc3 v.2) q hq).symm
    have := Subgroup.mem_centralizer_iff.1 (hv (hbar u.2)) (v : _) (Set.mem_singleton _)
    exact Subtype.ext this.symm
  have hq := gl_quasi_barX hK
  obtain ⟨hperf, hsimple⟩ := hq
  have hbot : commutator ↥(barX 3 X K) = ⊥ := by
    rw [commutator_def]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun u _ =>
      Subgroup.mem_centralizer_iff.2 fun w _ => hcomm.is_comm.comm w u
  have hone : ∀ g : ↥(barX 3 X K), g = 1 := fun g => by
    have : g ∈ (⊤ : Subgroup ↥(barX 3 X K)) := trivial
    rw [← hperf, hbot] at this
    exact this
  have := hsimple
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (↥(barX 3 X K) ⧸ Subgroup.center ↥(barX 3 X K))
  obtain ⟨gx, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨gy, rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (by rw [hone gx, hone gy])

theorem p9a_layer_conj {X : Subgroup G} {e : G} (he : e ∈ X) :
    GLBConj e (GLAPLayer 3 X) ≤ GLAPLayer 3 X := by
  have hX : GLBConj e X = X :=
    mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer he)
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have h := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK e
  rw [hX] at h
  exact le_sSup h

theorem p9a_ncl_conj {L J : Subgroup G} {e : G} (hL : ∀ g ∈ L, e⁻¹ * g * e ∈ L)
    (hJ : ∀ j ∈ J, e⁻¹ * j * e ∈ J) : GLBConj e (ncl L J) ≤ ncl L J := by
  unfold ncl
  have hc : GLBConj e (⨆ g ∈ L, GLBConj g J) = ⨆ g ∈ L, GLBConj e (GLBConj g J) := by
    unfold GLBConj
    rw [Subgroup.map_iSup]
    simp_rw [Subgroup.map_iSup]
  rw [hc]
  refine iSup₂_le fun g hg => ?_
  refine le_iSup₂_of_le (e⁻¹ * g * e) (hL g hg) ?_
  intro x hx
  rw [mem_gLBConj] at hx ⊢
  rw [mem_gLBConj] at hx
  have := hJ _ hx
  convert this using 1
  group

theorem s9a_H_le {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    {q q0 : ℕ} {y0 y : G} {J0 : Subgroup G} (s5 : S5Facts V L A b x q0 y0 J0)
    (s6 : S6Facts V L A b x y0 y J0) (s7a : S7aFacts L A b x y q J0) (s7b : S7bFacts A y J0)
    (s8 : S8Facts A b y q0 J0) :
    ∃ a ∈ A, a ≠ 1 ∧ ∃ H : Subgroup G, H ≤ Iof y J0 (Subgroup.zpowers a) ∧
      ∃ E : Subgroup (↥(Cs a) ⧸ GLAPPrimeCore 3 ↥(Cs a)), IsElemAbelian 3 E ∧ Nat.card E = 27 ∧
        E ≤ barX 3 (Cs a) H := by
  exfalso
  obtain ⟨a, H1, H2, H3, haA, ha1, -, hc1, hc2, hc3, h12, h13, h23, hCL, -, htr⟩ := s8
  have hIa := s7b.Icomp a haA ha1
  have hle : Iof y J0 (Subgroup.zpowers a) ≤ H1 ⊔ H2 ⊔ H3 := hCL ▸ le_sSup hIa
  have hmem := p9a_comp_mem hc1 hc2 hc3 hIa hle
  have hnorm : ∀ e ∈ A, GLBConj e (Iof y J0 (Subgroup.zpowers a)) ≤
      Iof y J0 (Subgroup.zpowers a) := by
    intro e he
    have hMe : e ∈ A ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left he
    have hcomm : ∀ m ∈ A ⊔ Subgroup.zpowers y, m * e = e * m := fun m hm => by
      have := s6.Mel.1.is_comm.comm (⟨m, hm⟩ : ↥(A ⊔ Subgroup.zpowers y)) ⟨e, hMe⟩
      exact congrArg Subtype.val this
    have hS : Subgroup.zpowers y ⊔ Subgroup.zpowers a ≤ A ⊔ Subgroup.zpowers y :=
      sup_le le_sup_right (Subgroup.zpowers_le.2 (le_sup_left (a := A) haA))
    have hC : e ∈ CD (Subgroup.zpowers y ⊔ Subgroup.zpowers a) :=
      Subgroup.mem_centralizer_iff.2 fun h hh => hcomm h (hS hh)
    refine p9a_ncl_conj (fun g hg => ?_) (fun j hj => ?_)
    · have h1 := gLBConj_mono e⁻¹ (p9a_layer_conj hC)
      rw [gLBConj_inv_gLBConj] at h1
      have := mem_gLBConj.1 (h1 hg)
      simpa using this
    · have hjC := s6.J0M.1 hj
      have h := Subgroup.mem_centralizer_iff.1 hjC e hMe
      have h' : e * j = j * e := h
      rw [mul_assoc, ← h', inv_mul_cancel_left]
      exact hj
  have fin : ∀ Hi Hj : Subgroup G, Hi ≠ Hj → GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs a) Hi →
      GLAPComponent 3 (Iof y J0 ⊥ ⊓ Cs a) Hj → Iof y J0 (Subgroup.zpowers a) = Hi →
      (∃ e ∈ A, GLBConj e Hi = Hj) → False := by
    intro Hi Hj hne hi hj heq ⟨e, he, hconj⟩
    have := hnorm e he
    rw [heq, hconj] at this
    exact hne (gl_comp_eq_of_le hi hj this).symm
  rcases hmem with h | h | h
  · obtain ⟨e, he, hconj⟩ := htr H1 H2 (Or.inl rfl) (Or.inr (Or.inl rfl))
    exact fin H1 H2 h12 hc1 hc2 h ⟨e, he, hconj⟩
  · obtain ⟨e, he, hconj⟩ := htr H2 H1 (Or.inr (Or.inl rfl)) (Or.inl rfl)
    exact fin H2 H1 h12.symm hc2 hc1 h ⟨e, he, hconj⟩
  · obtain ⟨e, he, hconj⟩ := htr H3 H1 (Or.inr (Or.inr rfl)) (Or.inl rfl)
    exact fin H3 H1 h13.symm hc3 hc1 h ⟨e, he, hconj⟩

theorem p9b_isPSLn_congr {n r : ℕ} {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : IsPSLn n r Y) : IsPSLn n r Z := by
  obtain ⟨F, hF, hFin, hc, ⟨φ⟩⟩ := h
  exact ⟨F, hF, hFin, hc, ⟨e.symm.trans φ⟩⟩

theorem p9b_isPSUn_congr {n r : ℕ} {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : IsPSUn n r Y) : IsPSUn n r Z := by
  obtain ⟨F, hF, hFin, hc, ⟨φ⟩⟩ := h
  exact ⟨F, hF, hFin, hc, ⟨e.symm.trans φ⟩⟩

theorem p9b_isL3Eps_congr {r : ℕ} {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (h : IsL3Eps r Y) : IsL3Eps r Z :=
  h.imp (fun h => ⟨h.1, p9b_isPSLn_congr e h.2⟩) (fun h => ⟨h.1, p9b_isPSUn_congr e h.2⟩)

theorem s9b_rank {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) {q q0 : ℕ}
    (s4a : ∀ a ∈ A, a ≠ 1 → GLAPComponent 3 (Cs a) (KOf L A a) ∧
      ∃ r : ℕ, (r = q ∨ r = q0) ∧ IsL3Eps r (barOf 3 (KOf L A a)) ∧
        CFSG.Open.IsQuasisimple (barOf 3 (KOf L A a))) :
    ∀ a ∈ A, a ≠ 1 → ∀ E : Subgroup (↥(Cs a) ⧸ GLAPPrimeCore 3 ↥(Cs a)),
      E ≤ barX 3 (Cs a) (KOf L A a) → IsElemAbelian 3 E → Nat.card E ≤ 9 := by
  intro a ha ha1 E hE hEe
  obtain ⟨hc, r, -, hr, -⟩ := s4a a ha ha1
  obtain ⟨e⟩ := gl_barOf_equiv hc
  have hY := p9b_isL3Eps_congr e hr
  have h9 := hi.l3rk _ r hY (E.subgroupOf (barX 3 (Cs a) (KOf L A a)))
    (isElemAbelian_subgroupOf' hEe _)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv] at h9

theorem s9_end {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) (s1 : S1Facts B b L A x)
    {q q0 : ℕ}
    (s4a : ∀ a ∈ A, a ≠ 1 → GLAPComponent 3 (Cs a) (KOf L A a) ∧
      ∃ r : ℕ, (r = q ∨ r = q0) ∧ IsL3Eps r (barOf 3 (KOf L A a)) ∧
        CFSG.Open.IsQuasisimple (barOf 3 (KOf L A a)))
    {y0 y : G} {J0 : Subgroup G} (s5 : S5Facts V L A b x q0 y0 J0) (s6 : S6Facts V L A b x y0 y J0)
    (s7a : S7aFacts L A b x y q J0) (s7b : S7bFacts A y J0) (s8 : S8Facts A b y q0 J0) : False := by
  obtain ⟨a, haA, ha1, H, hH, E, hE, hE27, hEH⟩ := s9a_H_le hi c s1 s5 s6 s7a s7b s8
  have hHK : H ≤ KOf L A a := hH.trans (s7a.IleK a haA ha1)
  have hle : barX 3 (Cs a) H ≤ barX 3 (Cs a) (KOf L A a) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, (Subgroup.mem_subgroupOf).2 (hHK ((Subgroup.mem_subgroupOf).1 hw)), rfl⟩
  have := s9b_rank hi c s4a a haA ha1 E (hEH.trans hle) hE
  omega

theorem ctx_false {V : InndiagVocab} (hi : Inputs V) (c : Ctx B b L A x) : False := by
  have s1 := s1_basic c
  have s2 := s2_J hi c s1
  have s3 := s3_nontriv hi c s1 s2
  obtain ⟨q, q0, s4⟩ := s4_types hi c s1 s2 s3
  have s4a := s4_all hi c s1 s2 s3 s4
  obtain ⟨y0, J0, s5⟩ := s5_y0 hi c s1 s3 s4
  obtain ⟨y, s6⟩ := s6_y hi c s1 s2 s3 s4 s4a s5
  have s7a := s7a_Ia hi c s1 s2 s3 s4 s4a s5 s6
  have s7b := s7b_I1 hi c s1 s5 s6 s7a
  have s7c := s7c_fields hi c s1 s4 s5 s6 s7a s7b
  have s7d := s7d_inn hi c s1 s4 s5 s6 s7a s7b s7c
  have s8 := s8_apply hi c s1 s4 s5 s6 s7a s7b s7c s7d
  exact s9_end hi c s1 s4a s5 s6 s7a s7b s8

theorem cover514_of_inputs (V : InndiagVocab) (hi : Inputs V) : Cover514 := by
  intro G _ _ m hS hC B hB b L A hw a haA ha1 hab
  by_contra hne
  exact ctx_false hi ⟨⟨m, hS⟩, hC, hB, hw, haA, ha1, hab, hne⟩

theorem lemma514_of_inputs (V : InndiagVocab) (hi : Inputs V) : Lemma514 :=
  lemma514_of_cover (cover514_of_inputs V hi)

end Lemma514CoverNs

end CFSG.HardMathSupport.Solomon.LocalBalance

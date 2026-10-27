module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Assembly
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Goldschmidt

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open
open scoped commutatorElement

section Lifting

theorem commutator_mul_central {G : Type*} [Group G] {b₁ b₂ c₁ c₂ : G}
    (h1 : c₁ ∈ Subgroup.center G) (h2 : c₂ ∈ Subgroup.center G) :
    ⁅b₁ * c₁, b₂ * c₂⁆ = ⁅b₁, b₂⁆ := by
  have e1 : ∀ x y : G, c₁ * (x * y) = x * (c₁ * y) := fun x y => by
    rw [← mul_assoc, ← Subgroup.mem_center_iff.mp h1 x, mul_assoc]
  have e2 : ∀ x y : G, c₂ * (x * y) = x * (c₂ * y) := fun x y => by
    rw [← mul_assoc, ← Subgroup.mem_center_iff.mp h2 x, mul_assoc]
  have e1' : ∀ x y : G, c₁⁻¹ * (x * y) = x * (c₁⁻¹ * y) := fun x y => by
    have := Subgroup.inv_mem _ h1
    rw [← mul_assoc, ← Subgroup.mem_center_iff.mp this x, mul_assoc]
  simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
  rw [e1 b₂, e1 c₂, e1' b₁⁻¹, e1 b₁⁻¹, mul_inv_cancel_left, e2 b₁⁻¹, mul_inv_cancel_left]

theorem eq_of_map_mk_eq_of_le_center {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : N ≤ Subgroup.center G) {L M : Subgroup G} (hL : ⁅L, L⁆ = L) (hM : ⁅M, M⁆ = M)
    (h : L.map (QuotientGroup.mk' N) = M.map (QuotientGroup.mk' N)) : L = M := by
  have key : ∀ {A B : Subgroup G}, A.map (QuotientGroup.mk' N) ≤ B.map (QuotientGroup.mk' N) →
      ∀ a ∈ A, ∃ b ∈ B, ∃ c ∈ Subgroup.center G, a = b * c := by
    intro A B hAB a ha
    have : QuotientGroup.mk' N a ∈ B.map (QuotientGroup.mk' N) := hAB ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := this
    refine ⟨b, hb, b⁻¹ * a, hN ?_, by group⟩
    have : (b : G ⧸ N) = a := hba
    exact QuotientGroup.eq.mp this
  have hle : ∀ {A B : Subgroup G}, ⁅A, A⁆ = A →
      A.map (QuotientGroup.mk' N) ≤ B.map (QuotientGroup.mk' N) → A ≤ B := by
    intro A B hA hAB
    have : ⁅A, A⁆ ≤ B := by
      refine Subgroup.commutator_le.mpr fun a ha a' ha' => ?_
      obtain ⟨b, hb, c, hc, rfl⟩ := key hAB a ha
      obtain ⟨b', hb', c', hc', rfl⟩ := key hAB a' ha'
      rw [commutator_mul_central hc hc']
      exact B.mul_mem (B.mul_mem (B.mul_mem hb hb') (B.inv_mem hb)) (B.inv_mem hb')
    rwa [hA] at this
  exact le_antisymm (hle hL h.le) (hle hM h.ge)

theorem commutes_of_map_commutes_of_le_center {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : N ≤ Subgroup.center G) {L M : Subgroup G} (hL : ⁅L, L⁆ = L)
    (h : ∀ a ∈ L, ∀ b ∈ M, QuotientGroup.mk' N a * QuotientGroup.mk' N b =
      QuotientGroup.mk' N b * QuotientGroup.mk' N a) :
    ∀ a ∈ L, ∀ b ∈ M, a * b = b * a := by
  intro a₀ ha₀ b hb
  have hcen : ∀ a ∈ L, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center G := by
    intro a ha
    refine hN ?_
    rw [← QuotientGroup.eq_one_iff]
    have := h a ha b hb
    have e : ((a * b * a⁻¹ * b⁻¹ : G) : G ⧸ N) =
        QuotientGroup.mk' N a * QuotientGroup.mk' N b * (QuotientGroup.mk' N a)⁻¹ *
          (QuotientGroup.mk' N b)⁻¹ := by
      simp [QuotientGroup.mk'_apply]
    rw [e, this]
    group
  have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  let f : ↥L →* G :=
    { toFun := fun a => (a : G) * b * (a : G)⁻¹ * b⁻¹
      map_one' := by simp
      map_mul' := by
        intro a a'
        have hc' := hcen a' a'.2
        have hc'' := Subgroup.mem_center_iff.mp hc'
        calc ((a * a' : ↥L) : G) * b * ((a * a' : ↥L) : G)⁻¹ * b⁻¹
            = (a : G) * ((a' : G) * b * (a' : G)⁻¹ * b⁻¹) * (b * (a : G)⁻¹ * b⁻¹) := by
              simp only [Subgroup.coe_mul, mul_inv_rev]
              group
          _ = ((a' : G) * b * (a' : G)⁻¹ * b⁻¹) * (a : G) * (b * (a : G)⁻¹ * b⁻¹) := by
              rw [← hc'' (a : G)]
          _ = ((a' : G) * b * (a' : G)⁻¹ * b⁻¹) * ((a : G) * b * (a : G)⁻¹ * b⁻¹) := by group
          _ = ((a : G) * b * (a : G)⁻¹ * b⁻¹) * ((a' : G) * b * (a' : G)⁻¹ * b⁻¹) := by
              rw [hc'' ((a : G) * b * (a : G)⁻¹ * b⁻¹)] }
  have hcomm : ∀ x y : ↥L, f x * f y = f y * f x := fun x y =>
    (Subgroup.mem_center_iff.mp (hcen y y.2) (f x)).symm ▸ rfl
  have h1 := hom_trivial_of_perfect_of_commute hperf f hcomm ⟨a₀, ha₀⟩
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Lifting

section Class

variable {Y : Type} [Group Y]

@[expose] def ConjInvariant2A7 (Λ : Set (Subgroup Y)) : Prop :=
  ∀ (g : Y) (L : Subgroup Y), L ∈ Λ → L.map (MulAut.conj g).toMonoidHom ∈ Λ

structure InClass2A7 (Λ : Set (Subgroup Y)) : Prop where
  nonempty : Λ.Nonempty
  conjInvariant : ConjInvariant2A7 Λ
  generated : ⨆ L ∈ Λ, L = ⊤
  classical : ∀ L ∈ Λ, ∃ z : Y, IsClassical2A7 ⊤ L z

end Class

structure A7SystemData (X : Type) [Group X] (Φ : Set (Subgroup X)) where
  card : ℕ
  comp : Fin card → Subgroup X
  perfect : ∀ i, Group.IsPerfect ↥(comp i)
  witness : ∀ i, A7Witness (comp i)
  commute : ∀ i j, i ≠ j → ∀ a ∈ comp i, ∀ b ∈ comp j, a * b = b * a
  generate : ⨆ i, comp i = ⊤
  members : Φ = Set.range comp

@[expose] def A7System (X : Type) [Group X] (Φ : Set (Subgroup X)) : Prop :=
  Nonempty (A7SystemData X Φ)

section Mod

variable {Y : Type} [Group Y]

@[expose] def oddQuotientFamily2A7 (Λ : Set (Subgroup Y)) :
    Set (Subgroup (Y ⧸ classicalInvolutionOddCore Y)) :=
  Subgroup.map (QuotientGroup.mk' (classicalInvolutionOddCore Y)) '' Λ

@[expose] def A7SystemMod (Λ : Set (Subgroup Y)) : Prop :=
  A7System (Y ⧸ classicalInvolutionOddCore Y) (oddQuotientFamily2A7 Λ)

end Mod

@[expose] def CITInductive2A7 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Λ : Set (Subgroup Y)), InClass2A7 Λ → A7SystemMod Λ

@[expose] def CITBelow2A7 (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < n →
    ∀ Λ : Set (Subgroup Y), InClass2A7 Λ → A7SystemMod Λ

theorem CITBelow2A7.mono {m n : ℕ} (h : m ≤ n) (hn : CITBelow2A7 n) : CITBelow2A7 m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ

@[expose] def CITStep2A7 (n : ℕ) : Prop :=
  CITBelow2A7 n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ Λ : Set (Subgroup Y), InClass2A7 Λ → A7SystemMod Λ

theorem citInductive2A7_of_step (h : ∀ n, CITStep2A7 n) : CITInductive2A7 := by
  have key : ∀ n, ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
      ∀ Λ : Set (Subgroup Y), InClass2A7 Λ → A7SystemMod Λ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Y _ _ hY Λ hΛ
      exact h n (fun Y' _ _ hlt Λ' hΛ' => ih _ hlt Y' rfl Λ' hΛ') Y hY Λ hΛ
  intro Y _ _ Λ hΛ
  exact key _ Y rfl Λ hΛ

section Sanity

namespace A7SystemData

variable {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : A7SystemData X Φ)

theorem comp_normal (i : Fin D.card) : (D.comp i).Normal := by
  have key : ∀ g ∈ (⨆ k, D.comp k : Subgroup X), ∀ n ∈ D.comp i, g * n * g⁻¹ ∈ D.comp i := by
    intro g hg
    induction hg using Subgroup.iSup_induction' with
    | hp k y hy =>
      intro n hn
      by_cases hki : k = i
      · subst hki
        exact (D.comp k).mul_mem ((D.comp k).mul_mem hy hn) ((D.comp k).inv_mem hy)
      · have := D.commute k i hki y hy n hn
        rw [this, mul_assoc, mul_inv_cancel, mul_one]
        exact hn
    | h1 => intro n hn; simpa using hn
    | hmul x y _ _ hx hy =>
      intro n hn
      have e : x * y * n * (x * y)⁻¹ = x * (y * n * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact hx _ (hy n hn)
  refine ⟨fun n hn g => key g ?_ n hn⟩
  rw [D.generate]
  trivial

end A7SystemData

theorem false_of_a7System_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) {Φ : Set (Subgroup X)} (D : A7SystemData X Φ)
    (i : Fin D.card) : False := by
  have hn : (D.comp i).Normal := D.comp_normal i
  have hw := D.witness i
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (D.comp i) with h0 | h0
  ·
    obtain ⟨-, hc, -⟩ := hw
    have : Subsingleton (↥(D.comp i) ⧸ classicalInvolutionOddCore ↥(D.comp i)) := by
      have : Subsingleton ↥(D.comp i) := by rw [h0]; infer_instance
      exact Function.Surjective.subsingleton (QuotientGroup.mk'_surjective _)
    have h1 : Nat.card (Subgroup.center (↥(D.comp i) ⧸ classicalInvolutionOddCore ↥(D.comp i))) = 1 :=
      Nat.card_unique
    omega
  ·
    obtain ⟨-, hc, -⟩ := hw
    set P : Subgroup X := D.comp i with hP
    have hPtop : P = ⊤ := h0
    let eP : ↥P ≃* X := (MulEquiv.subgroupCongr hPtop).trans Subgroup.topEquiv
    have : IsSimpleGroup ↥P := eP.isSimpleGroup
    have hPnab : ∃ a b : ↥P, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨eP.symm a, eP.symm b, fun h => hab (eP.symm.injective (by rw [map_mul, map_mul, h]))⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (classicalInvolutionOddCore ↥P) with ho | ho
    ·
      have hZ : Subgroup.center ↥P = ⊥ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hPnab).2
      let e : (↥P ⧸ classicalInvolutionOddCore ↥P) ≃* ↥P :=
        (QuotientGroup.quotientMulEquivOfEq ho).trans QuotientGroup.quotientBot
      have hZ' : Subgroup.center (↥P ⧸ classicalInvolutionOddCore ↥P) = ⊥ := by
        rw [← Subgroup.map_center_eq e.symm, hZ]
        simp
      rw [hZ', Subgroup.card_bot] at hc
      omega
    ·
      have : Subsingleton (↥P ⧸ classicalInvolutionOddCore ↥P) := by
        rw [ho]
        exact QuotientGroup.subsingleton_quotient_top
      have h1 : Nat.card (Subgroup.center (↥P ⧸ classicalInvolutionOddCore ↥P)) = 1 :=
        Nat.card_unique
      omega

theorem false_of_inductive2A7 (h : CITInductive2A7) {F : Type} [Group F] [Finite F]
    [IsSimpleGroup F] (hnab : ∃ a b : F, a * b ≠ b * a) {K : Subgroup F} {z : F}
    (hK : IsClassical2A7 ⊤ K z) : False := by
  let Λ : Set (Subgroup F) := Set.range fun g : F => K.map (MulAut.conj g).toMonoidHom
  have hK1 : K.map (MulAut.conj (1 : F)).toMonoidHom = K := by
    ext x
    simp
  have hconj : ConjInvariant2A7 Λ := by
    rintro g _ ⟨a, rfl⟩
    exact ⟨g * a, by rw [map_map_conj]⟩
  have hgen : ⨆ L ∈ Λ, L = ⊤ := by
    have hKΛ : K ∈ Λ := ⟨1, hK1⟩
    have hN : (⨆ L ∈ Λ, L).Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hle : (⨆ L ∈ Λ, L).map (MulAut.conj g).toMonoidHom ≤ ⨆ L ∈ Λ, L :=
        Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun L hL =>
          Subgroup.map_le_iff_le_comap.mp
            (le_iSup₂_of_le (L.map (MulAut.conj g).toMonoidHom) (hconj g L hL) le_rfl))
      exact hle ⟨n, hn, rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (⨆ L ∈ Λ, L) with h0 | h0
    · exfalso
      have hKle : K ≤ ⨆ L ∈ Λ, L := le_iSup₂_of_le K hKΛ le_rfl
      have hzK : z ∈ (⨆ L ∈ Λ, L) := hKle hK.mem
      rw [h0, Subgroup.mem_bot] at hzK
      have := hK.orderOf_eq_two
      rw [hzK, orderOf_one] at this
      omega
    · exact h0
  have hΛ : InClass2A7 Λ :=
    ⟨⟨K, 1, hK1⟩, hconj, hgen, by
      rintro _ ⟨g, rfl⟩
      refine ⟨g * z * g⁻¹, ?_⟩
      have h1 := hK.conj g
      rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1⟩
  obtain ⟨D⟩ := h F Λ hΛ
  have hz2 : 2 ∣ Nat.card F := hK.orderOf_eq_two ▸ orderOf_dvd_natCard z
  have hO : classicalInvolutionOddCore F = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (classicalInvolutionOddCore F) with h0 | h0
    · exact h0
    · exfalso
      have hodd : Odd (Nat.card (classicalInvolutionOddCore F)) :=
        CFSG.ComponentClassification.OddCore.odd_card F
      rw [h0, Subgroup.card_top] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hz2)
  let e : (F ⧸ classicalInvolutionOddCore F) ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have : IsSimpleGroup (F ⧸ classicalInvolutionOddCore F) := e.isSimpleGroup
  have hXnab := exists_noncomm_of_mulEquiv e.symm hnab
  have hmem : K.map (QuotientGroup.mk' (classicalInvolutionOddCore F)) ∈
      oddQuotientFamily2A7 Λ := ⟨K, ⟨1, hK1⟩, rfl⟩
  rw [D.members] at hmem
  obtain ⟨i, -⟩ := hmem
  exact false_of_a7System_of_simple hXnab D i

theorem cit2A7_of_inductive (h : CITInductive2A7) : CIT2A7 := by
  intro F _ _ _ hnab z hz K hzK hK _ _ hw
  obtain ⟨L, hL⟩ := exists_isClassical2A7_of_witness hz hzK hK hw.2
  exact (false_of_inductive2A7 h hnab hL).elim

end Sanity

section Local

variable {F : Type} [Group F]

@[expose] def normalClosureIn2A7 (C S : Subgroup F) : Subgroup F :=
  ⨆ c ∈ C, S.map (MulAut.conj c).toMonoidHom

theorem map_conj_eq_of_mem {C : Subgroup F} {c : F} (hc : c ∈ C) :
    C.map (MulAut.conj c).toMonoidHom = C := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact C.mul_mem (C.mul_mem hc hx) (C.inv_mem hc)
  · intro hy
    refine ⟨c⁻¹ * y * c, C.mul_mem (C.mul_mem (C.inv_mem hc) hy) hc, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (S : Subgroup F) : S.map (MulAut.conj (1 : F)).toMonoidHom = S := by
  ext x
  simp

theorem map_conj_le_normalClosureIn2A7 {C S : Subgroup F} {c : F} (hc : c ∈ C) :
    S.map (MulAut.conj c).toMonoidHom ≤ normalClosureIn2A7 C S :=
  le_iSup₂_of_le c hc le_rfl

theorem le_normalClosureIn2A7 {C S : Subgroup F} : S ≤ normalClosureIn2A7 C S := by
  have := map_conj_le_normalClosureIn2A7 (S := S) C.one_mem
  rwa [map_conj_one] at this

theorem normalClosureIn2A7_le_of {C S T : Subgroup F}
    (h : ∀ c ∈ C, S.map (MulAut.conj c).toMonoidHom ≤ T) : normalClosureIn2A7 C S ≤ T :=
  iSup₂_le h

theorem normalClosureIn2A7_le {C S : Subgroup F} (hS : S ≤ C) : normalClosureIn2A7 C S ≤ C := by
  refine iSup₂_le fun c hc => ?_
  calc S.map (MulAut.conj c).toMonoidHom ≤ C.map (MulAut.conj c).toMonoidHom := Subgroup.map_mono hS
    _ = C := map_conj_eq_of_mem hc

theorem map_conj_subgroupOf {Y₀ H : Subgroup F} (g : ↥Y₀) :
    (H.subgroupOf Y₀).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj (g : F)).toMonoidHom).subgroupOf Y₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(x : F), hx, ?_⟩
    simp [MulAut.conj_apply]
  · rintro ⟨h, hh, hhy⟩
    have hx : (g : F)⁻¹ * (y : F) * (g : F) ∈ Y₀ :=
      Y₀.mul_mem (Y₀.mul_mem (Y₀.inv_mem g.2) y.2) g.2
    refine ⟨⟨(g : F)⁻¹ * (y : F) * (g : F), hx⟩, ?_, ?_⟩
    · show (g : F)⁻¹ * (y : F) * (g : F) ∈ H
      have hhy' : (g : F) * h * (g : F)⁻¹ = (y : F) := by
        simpa [MulAut.conj_apply] using hhy
      have : (g : F)⁻¹ * (y : F) * (g : F) = h := by
        rw [← hhy']
        group
      rw [this]
      exact hh
    · apply Subtype.ext
      simp [MulAut.conj_apply, mul_assoc]

theorem IsClassical2A7.subgroupOf {Y L : Subgroup F} {u : F} (h : IsClassical2A7 Y L u)
    {Y₀ : Subgroup F} (hLY₀ : L ≤ Y₀) (hY₀ : Y₀ ≤ Y) :
    IsClassical2A7 (⊤ : Subgroup ↥Y₀) (L.subgroupOf Y₀) (⟨u, hLY₀ h.mem⟩ : ↥Y₀) := by
  have hperf := h.perfect
  have e : ↥(L.subgroupOf Y₀) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLY₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]
    exact h.orderOf_eq_two
  · exact h.mem
  · exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · have h1 := CFSG.ClassicalInvolution.isSubnormal_subgroupOf h.subnormal Y₀
    have e1 : (Y ⊓ Subgroup.centralizer ({u} : Set F)).subgroupOf Y₀ =
        ⊤ ⊓ Subgroup.centralizer ({(⟨u, hLY₀ h.mem⟩ : ↥Y₀)} : Set ↥Y₀) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_top, true_and,
        Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
      constructor
      · rintro ⟨-, hc⟩
        exact Subtype.ext hc
      · intro hc
        exact ⟨hY₀ x.2, congrArg Subtype.val hc⟩
    rwa [e1] at h1
  · exact A7Witness.of_mulEquiv e.symm h.witness

@[expose] def LocalOddCentral2A7 (F : Type) [Group F] : Prop :=
  ∀ x : F, orderOf x = 2 → Subgroup.centralizer ({x} : Set F) ≠ ⊤ → ∀ (L M : Subgroup F) (u v : F),
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) L u →
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) M v →
    classicalInvolutionOddCore ↥(normalClosureIn2A7 (Subgroup.centralizer ({x} : Set F)) (L ⊔ M)) ≤
      Subgroup.center ↥(normalClosureIn2A7 (Subgroup.centralizer ({x} : Set F)) (L ⊔ M))

theorem card_lt_of_ne_top' [Finite F] {H : Subgroup F} (h : H ≠ ⊤) : Nat.card H < Nat.card F := by
  have hmul := Subgroup.card_mul_index H
  have hidx : H.index ≠ 1 := fun h1 => h (Subgroup.index_eq_one.mp h1)
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hidx0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have : 2 ≤ H.index := by omega
  nlinarith

theorem classicalCommuteBelow_of_induction [Finite F] (hB : CITBelow2A7 (Nat.card F))
    (hO : LocalOddCentral2A7 F) : ClassicalCommuteBelow F := by
  intro x hx2 hx L M u v hL hM
  set C : Subgroup F := Subgroup.centralizer ({x} : Set F) with hC
  set Y₀ : Subgroup F := normalClosureIn2A7 C (L ⊔ M) with hY₀
  have hLM : L ⊔ M ≤ C := sup_le hL.le hM.le
  have hY₀C : Y₀ ≤ C := normalClosureIn2A7_le hLM
  have hLY₀ : L ≤ Y₀ := le_sup_left.trans le_normalClosureIn2A7
  have hMY₀ : M ≤ Y₀ := le_sup_right.trans le_normalClosureIn2A7
  have hY₀ne : Y₀ ≠ ⊤ := fun h => hx (top_le_iff.mp (h ▸ hY₀C))
  have hlt : Nat.card Y₀ < Nat.card F := card_lt_of_ne_top' hY₀ne
  have hLc : ∀ c ∈ C, L.map (MulAut.conj c).toMonoidHom ≤ Y₀ := fun c hc =>
    (Subgroup.map_mono le_sup_left).trans (map_conj_le_normalClosureIn2A7 hc)
  have hMc : ∀ c ∈ C, M.map (MulAut.conj c).toMonoidHom ≤ Y₀ := fun c hc =>
    (Subgroup.map_mono le_sup_right).trans (map_conj_le_normalClosureIn2A7 hc)
  let Λ₀ : Set (Subgroup ↥Y₀) :=
    {N' | ∃ c ∈ C, N' = (L.map (MulAut.conj c).toMonoidHom).subgroupOf Y₀ ∨
      N' = (M.map (MulAut.conj c).toMonoidHom).subgroupOf Y₀}
  have hL1 : L.map (MulAut.conj (1 : F)).toMonoidHom = L := map_conj_one L
  have hM1 : M.map (MulAut.conj (1 : F)).toMonoidHom = M := map_conj_one M
  have hLΛ : L.subgroupOf Y₀ ∈ Λ₀ := ⟨1, C.one_mem, Or.inl (by rw [hL1])⟩
  have hMΛ : M.subgroupOf Y₀ ∈ Λ₀ := ⟨1, C.one_mem, Or.inr (by rw [hM1])⟩
  have hΛ₀ : InClass2A7 Λ₀ := by
    refine ⟨⟨_, hLΛ⟩, ?_, ?_, ?_⟩
    · rintro g _ ⟨c, hc, hN | hN⟩
      · refine ⟨(g : F) * c, C.mul_mem (hY₀C g.2) hc, Or.inl ?_⟩
        rw [hN, map_conj_subgroupOf, map_map_conj]
      · refine ⟨(g : F) * c, C.mul_mem (hY₀C g.2) hc, Or.inr ?_⟩
        rw [hN, map_conj_subgroupOf, map_map_conj]
    · have hmapG : (⨆ N' ∈ Λ₀, N').map Y₀.subtype = Y₀ := by
        apply le_antisymm (Subgroup.map_subtype_le _)
        apply normalClosureIn2A7_le_of
        intro c hc
        rw [Subgroup.map_sup]
        have key : ∀ {H : Subgroup F}, H ≤ Y₀ → H.subgroupOf Y₀ ∈ Λ₀ →
            H ≤ (⨆ N' ∈ Λ₀, N').map Y₀.subtype := by
          intro H hH hmem
          have hle : H.subgroupOf Y₀ ≤ ⨆ N' ∈ Λ₀, N' := le_iSup₂_of_le _ hmem le_rfl
          calc H = (H.subgroupOf Y₀).map Y₀.subtype := by
                rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH]
            _ ≤ _ := Subgroup.map_mono hle
        exact sup_le (key (hLc c hc) ⟨c, hc, Or.inl rfl⟩) (key (hMc c hc) ⟨c, hc, Or.inr rfl⟩)
      apply Subgroup.map_injective Y₀.subtype_injective
      rw [hmapG, Subgroup.map_top, Subgroup.range_subtype]
    · rintro N' ⟨c, hc, hN | hN⟩
      · subst hN
        have h1 := hL.conj c
        rw [map_conj_eq_of_mem hc] at h1
        exact ⟨_, h1.subgroupOf (hLc c hc) hY₀C⟩
      · subst hN
        have h1 := hM.conj c
        rw [map_conj_eq_of_mem hc] at h1
        exact ⟨_, h1.subgroupOf (hMc c hc) hY₀C⟩
  obtain ⟨D⟩ := hB ↥Y₀ hlt Λ₀ hΛ₀
  have hOc := hO x hx2 hx L M u v hL hM
  have hLcl := hL.subgroupOf hLY₀ hY₀C
  have hMcl := hM.subgroupOf hMY₀ hY₀C
  have hperfL : ⁅L.subgroupOf Y₀, L.subgroupOf Y₀⁆ = L.subgroupOf Y₀ :=
    Subgroup.isPerfect_iff.mp hLcl.perfect
  have hperfM : ⁅M.subgroupOf Y₀, M.subgroupOf Y₀⁆ = M.subgroupOf Y₀ :=
    Subgroup.isPerfect_iff.mp hMcl.perfect
  have hmemL : (L.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) ∈
      oddQuotientFamily2A7 Λ₀ := ⟨_, hLΛ, rfl⟩
  have hmemM : (M.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) ∈
      oddQuotientFamily2A7 Λ₀ := ⟨_, hMΛ, rfl⟩
  rw [D.members] at hmemL hmemM
  obtain ⟨i, hi⟩ := hmemL
  obtain ⟨j, hj⟩ := hmemM
  by_cases hij : i = j
  · subst hij
    left
    have heq : (L.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) =
        (M.subgroupOf Y₀).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₀)) :=
      hi.symm.trans hj
    have h2 := Subgroup.subgroupOf_inj.mp
      (eq_of_map_mk_eq_of_le_center hOc hperfL hperfM heq)
    have e1 : L ⊓ Y₀ = L := inf_eq_left.mpr hLY₀
    have e2 : M ⊓ Y₀ = M := inf_eq_left.mpr hMY₀
    rw [e1, e2] at h2
    exact h2
  · right
    intro a ha b hb
    have hcomm := commutes_of_map_commutes_of_le_center hOc hperfL (M := M.subgroupOf Y₀)
      (fun a' ha' b' hb' => by
        have := D.commute i j hij _ (hi ▸ Subgroup.mem_map_of_mem _ ha') _
          (hj ▸ Subgroup.mem_map_of_mem _ hb')
        exact this)
    exact congrArg Subtype.val (hcomm ⟨a, hLY₀ ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
      ⟨b, hMY₀ hb⟩ (Subgroup.mem_subgroupOf.mpr hb))

theorem classicalQuasisimple_of_localOddCentral [Finite F]
    (hZ : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1) (hO : LocalOddCentral2A7 F) :
    ClassicalQuasisimple F := by
  intro L u hL
  have hu1 : u ≠ 1 := by
    intro h
    have := hL.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  set C : Subgroup F := Subgroup.centralizer ({u} : Set F) with hC
  have hCne : C ≠ ⊤ := by
    intro h
    apply hu1
    apply hZ u
    intro y
    have hy : y ∈ C := h ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_iff.mp hy u rfl
  have hLC : IsClassical2A7 C L u := hL.mono hL.le_centralizer le_top
  have h1 := hO u hL.orderOf_eq_two hCne L L u u hLC hLC
  set Y₀ : Subgroup F := normalClosureIn2A7 C (L ⊔ L) with hY₀
  have hLY₀ : L ≤ Y₀ := le_sup_left.trans le_normalClosureIn2A7
  have hY₀C : Y₀ ≤ C := normalClosureIn2A7_le (sup_le hLC.le hLC.le)
  have hsub : IsSubnormal L Y₀ := by
    have h2 := isSubnormal_inf hLC.subnormal Y₀
    have e1 : L ⊓ Y₀ = L := inf_eq_left.mpr hLY₀
    have e2 : (C ⊓ Subgroup.centralizer ({u} : Set F)) ⊓ Y₀ = Y₀ := by
      rw [← hC, inf_idem]
      exact inf_eq_right.mpr hY₀C
    rwa [e1, e2] at h2
  intro e he
  rw [Subgroup.mem_center_iff]
  intro l
  obtain ⟨hY, hmemY⟩ :=
    (CFSG.ComponentClassification.OddCore.subnormal_mem_iff hsub e.1 e.2).mp he
  have hc := h1 hmemY
  have hcomm := Subgroup.mem_center_iff.mp hc ⟨l.1, hLY₀ l.2⟩
  have h3 : (l : F) * (e : F) = (e : F) * (l : F) := congrArg Subtype.val hcomm
  exact Subtype.ext h3

end Local

@[expose] def CoreStep2A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassical2A7 ⊤ K z → CITBelow2A7 (Nat.card G) → False

@[expose] def LocalOddCentralStep2A7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassical2A7 ⊤ K z → CITBelow2A7 (Nat.card G) →
      LocalOddCentral2A7 G

theorem coreStep2A7_of_inputs (GS : GoldschmidtStronglyClosedExponent) (TW : TwinExclusion)
    (LOC : LocalOddCentralStep2A7) : CoreStep2A7 := by
  intro G _ _ _ hnab K z hK hB
  have hO := LOC G hnab K z hK hB
  exact false_of_classical2A7 hnab (classicalCommuteBelow_of_induction hB hO)
    (classicalQuasisimple_of_localOddCentral (center_trivial_of_simple hnab) hO) GS TW hK

@[expose] def StepReduction2A7 : Prop := CoreStep2A7 → ∀ n, CITStep2A7 n

theorem cit2A7_of_milestone (h : GoldschmidtMilestone) (TW : TwinExclusion)
    (LOC : LocalOddCentralStep2A7) (red : StepReduction2A7) : CIT2A7 :=
  cit2A7_of_inductive (citInductive2A7_of_step
    (red (coreStep2A7_of_inputs (goldschmidtStronglyClosedExponent_of_milestone h) TW LOC)))

end CFSG.ClassicalInvolution.Hat2A7

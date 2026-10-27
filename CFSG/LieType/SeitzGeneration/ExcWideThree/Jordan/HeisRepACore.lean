module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Jordan.HeisRepARoot
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294K29ExcRankLang
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Fischer CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


namespace HeisA

theorem three_cycle_orbit : ∀ π : Equiv.Perm (Fin 3), π 0 ≠ 0 → π (π 0) ≠ 0 →
    ∀ i, ∃ e : Fin 3, π^[(e : ℕ)] i = 0 := by decide

theorem theta_fixed_of_lang {G : Type*} [Group G] (F : G →* G) {Qs m z X₀ : G}
    (hmz : z⁻¹ * (Qs * F z * Qs⁻¹) = m) (hX₀ : Qs * F X₀ * Qs⁻¹ = X₀) :
    (m * Qs) * F (z⁻¹ * X₀ * z) * (m * Qs)⁻¹ = z⁻¹ * X₀ * z := by
  have hm : m * Qs * (F z)⁻¹ = z⁻¹ * Qs := by
    rw [← hmz]
    group
  calc (m * Qs) * F (z⁻¹ * X₀ * z) * (m * Qs)⁻¹
      = (m * Qs * (F z)⁻¹) * F X₀ * (m * Qs * (F z)⁻¹)⁻¹ := by
        simp only [map_mul, map_inv]
        group
    _ = (z⁻¹ * Qs) * F X₀ * (z⁻¹ * Qs)⁻¹ := by rw [hm]
    _ = z⁻¹ * (Qs * F X₀ * Qs⁻¹) * z := by group
    _ = z⁻¹ * X₀ * z := by rw [hX₀]

theorem norm_fixed_algebra {G : Type*} [Group G] (Φ : G →* G) {y X A B : G} (e : ℕ)
    (hA : A = y * X * y⁻¹) (hB : B = y * A * y⁻¹) (hy3 : y ^ 3 = 1) (hΦy : Φ y = y)
    (hΘ : y ^ e * Φ X * (y ^ e)⁻¹ = X) (hc01 : Commute X A) (hc02 : Commute X B) :
    y * (X * A * B) * y⁻¹ = X * A * B ∧ Φ (X * A * B) = X * A * B := by
  have hy3' : y * y * y = 1 := by rw [← pow_three']; exact hy3
  have hC : y * B * y⁻¹ = X := by
    have : y * B * y⁻¹ = (y * y * y) * X * (y * y * y)⁻¹ := by
      rw [hB, hA]
      group
    rw [this, hy3']
    group
  have hσ : y * (X * A * B) * y⁻¹ = X * A * B := by
    have e1 : y * (X * A * B) * y⁻¹ = A * B * X := by
      calc y * (X * A * B) * y⁻¹ = (y * X * y⁻¹) * (y * A * y⁻¹) * (y * B * y⁻¹) := by group
        _ = A * B * X := by rw [← hA, ← hB, hC]
    rw [e1]
    calc A * B * X = A * (B * X) := by group
      _ = A * (X * B) := by rw [hc02.eq.symm]
      _ = (A * X) * B := by group
      _ = (X * A) * B := by rw [hc01.eq.symm]
  refine ⟨hσ, ?_⟩
  set p := y ^ e with hp
  have hΦX : Φ X = p⁻¹ * X * p := by
    calc Φ X = p⁻¹ * (p * Φ X * p⁻¹) * p := by group
      _ = p⁻¹ * X * p := by rw [hΘ]
  have hcy : Commute y p := (Commute.refl y).pow_right e
  have hpy : p⁻¹ * y * p = y := by
    have h1 : y * p = p * y := hcy.eq
    rw [mul_assoc, h1]
    group
  have hpy' : p⁻¹ * y⁻¹ * p = y⁻¹ := by
    have h1 : y⁻¹ * p = p * y⁻¹ := (hcy.inv_left).eq
    rw [mul_assoc, h1]
    group
  have hconj : ∀ g : G, y * (p⁻¹ * g * p) * y⁻¹ = p⁻¹ * (y * g * y⁻¹) * p := by
    intro g
    calc y * (p⁻¹ * g * p) * y⁻¹ = (p⁻¹ * y * p) * (p⁻¹ * g * p) * (p⁻¹ * y⁻¹ * p) := by
          rw [hpy, hpy']
      _ = p⁻¹ * (y * g * y⁻¹) * p := by group
  have hΦA : Φ A = p⁻¹ * A * p := by
    rw [hA, map_mul, map_mul, map_inv, hΦy, hΦX]
    exact hconj X
  have hΦB : Φ B = p⁻¹ * B * p := by
    rw [hB, map_mul, map_mul, map_inv, hΦy, hΦA]
    exact hconj A
  have hyx : Commute y (X * A * B) := mul_inv_eq_iff_eq_mul.1 hσ
  have hΦx : Φ (X * A * B) = p⁻¹ * (X * A * B) * p := by
    rw [map_mul, map_mul, hΦX, hΦA, hΦB]
    group
  have hxp : Commute (X * A * B) p := hyx.symm.pow_right e
  rw [hΦx, mul_assoc, hxp.eq, inv_mul_cancel_left]

variable {L : Type} [Field L]

theorem actsAs_y0_pow (b : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6) (e : ℕ) :
    ActsAs ((rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) ^ e)
      (fun v => (w ^ e) • v) := by
  have h := ((actsAs_rootDiagUnit b).mul (actsAs_canonicalRep (L := L) w)).pow e
  have e' : ((id : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)) ∘ fun v => w • v)^[e] =
      fun v => (w ^ e) • v := by
    simp
  rwa [e'] at h

structure CompData (a : Fin Tag.E6.rank → Lˣ) (w : WeylGroup Tag.E6) where
  C : Fin 3 → Set (Fin Tag.E6.rank → ℤ)
  π : Equiv.Perm (Fin 3)
  root : ∀ j, ∀ β ∈ C j, IsRoot Tag.E6 β
  neg : ∀ j, ∀ β ∈ C j, -β ∈ C j
  sig : ∀ β, β ∈ rootCharKernel a ↔ ∃ j, β ∈ C j
  orth : ∀ i j, i ≠ j → ∀ β ∈ C i, ∀ γ ∈ C j,
    β ≠ γ ∧ β ≠ -γ ∧ ¬ IsRoot Tag.E6 (β + γ)
  clique : ∀ j, ∀ β ∈ C j, ∀ γ ∈ C j, iform β γ ≠ 0
  nonempty : ∀ j, (C j).Nonempty
  π_zero : π 0 ≠ 0
  π_two : π (π 0) ≠ 0
  wC : ∀ j, ∀ β ∈ C j, w • β ∈ C (π j)

theorem rootSpan_le_of_subset {S T : Set (Fin Tag.E6.rank → ℤ)} (h : S ⊆ T) :
    rootSpan Tag.E6 L S ≤ rootSpan Tag.E6 L T := by
  unfold rootSpan
  exact iSup₂_le fun α hα =>
    le_iSup₂_of_le (f := fun β (_ : β ∈ T) => rootSubgroup Tag.E6 L β) α (h hα) le_rfl

theorem familyKernel_unit (a : Fin Tag.E6.rank → Lˣ) :
    familyKernel (fun _ : Unit => a) = rootCharKernel a := by
  ext β
  simp [familyKernel, rootCharKernel]

theorem rootSpan_le_familyGroup (a : Fin Tag.E6.rank → Lˣ) :
    rootSpan Tag.E6 L (rootCharKernel a) ≤ familyGroup (K := L) (fun _ : Unit => a) := by
  rw [familyGroup, familyKernel_unit]
  exact le_sup_right

theorem rootSpan_comp_le_familyGroup {a : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6}
    (D : CompData a w) (j : Fin 3) :
    rootSpan Tag.E6 L (D.C j) ≤ familyGroup (K := L) (fun _ : Unit => a) :=
  (rootSpan_le_of_subset fun β hβ => (D.sig β).2 ⟨j, hβ⟩).trans (rootSpan_le_familyGroup a)

theorem conj_mem_comp {a : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6} (D : CompData a w)
    {g : ModGL Tag.E6 L} (hg : g ∈ familyGroup (K := L) (fun _ : Unit => a)) (j : Fin 3)
    {t : ModGL Tag.E6 L} (ht : t ∈ rootSpan Tag.E6 L (D.C j)) :
    g * t * g⁻¹ ∈ rootSpan Tag.E6 L (D.C j) :=
  (Subgroup.mem_normalizer_iff.1
    (familyGroup_le_normalizer_rootSpan D.root D.sig D.orth j hg) t).1 ht

theorem commute_comp {a : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6} (D : CompData a w)
    {i j : Fin 3} (hij : i ≠ j) {s t : ModGL Tag.E6 L} (hs : s ∈ rootSpan Tag.E6 L (D.C i))
    (ht : t ∈ rootSpan Tag.E6 L (D.C j)) : Commute s t :=
  commute_rootSpan_of_orth (D.root i) (D.root j) (D.orth i j hij) s hs t ht

theorem conj_y_mem_comp {a b : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6} (D : CompData a w)
    {u y : ModGL Tag.E6 L} (hu : u ∈ rootSpan Tag.E6 L (rootCharKernel a))
    (hy : y = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)
    (j : Fin 3) {s : ModGL Tag.E6 L} (hs : s ∈ rootSpan Tag.E6 L (D.C j)) :
    y * s * y⁻¹ ∈ rootSpan Tag.E6 L (D.C (D.π j)) := by
  have huM := rootSpan_le_familyGroup a hu
  have hA := (actsAs_rootDiagUnit (L := L) b).mul (actsAs_canonicalRep (L := L) w)
  have h1 := conj_mem_comp D huM j hs
  have h2 := conj_mem_rootSpan_of_actsAs hA (D.root j) (fun β hβ => D.wC j β hβ) _ h1
  have h3 := conj_mem_comp D (inv_mem huM) (D.π j) h2
  rw [hy]
  have e : (u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u) * s *
      (u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)⁻¹ =
      u⁻¹ * ((rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) *
        (u * s * u⁻¹) * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w)⁻¹) *
        u⁻¹⁻¹ := by group
  rw [e]
  exact h3

theorem pow_smul_mem_comp {a : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6} (D : CompData a w)
    (e : ℕ) : ∀ (j : Fin 3) (β : Fin Tag.E6.rank → ℤ), β ∈ D.C j →
      (w ^ e) • β ∈ D.C (D.π^[e] j) := by
  induction e with
  | zero => intro j β hβ; simpa using hβ
  | succ e ih =>
    intro j β hβ
    rw [Function.iterate_succ_apply', pow_succ', mul_smul]
    exact D.wC _ _ (ih j β hβ)

open CFSG.LocalAnalysis.RankFourTheoremC.ExcRank (canonicalRep_mem_familyGroup_of_closure)

theorem exists_theta_fixed [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) {a b : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6} (D : CompData a w)
    (hw : w ∈ rootCharStabilizer a) {u y n : ModGL Tag.E6 L}
    (hu : u ∈ rootSpan Tag.E6 L (rootCharKernel a))
    (hy : y = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)
    {g : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hn : ActsAs n g)
    (hgSig : ∀ β ∈ rootCharKernel a, g β ∈ rootCharKernel a)
    (hnN : n ∈ Subgroup.normalizer
      (familyGroup (K := L) (fun _ : Unit => a) : Set (ModGL Tag.E6 L))) :
    ∃ (e : ℕ) (z : ModGL Tag.E6 L) (β₁ : Fin Tag.E6.rank → ℤ) (c₀ : L),
      z ∈ familyGroup (K := L) (fun _ : Unit => a) ∧ β₁ ∈ D.C 0 ∧ c₀ ≠ 0 ∧
      (y ^ e * n) * entrywiseFrobGL Tag.E6 L ℓ f (z⁻¹ * pinnedX Tag.E6 L β₁ c₀ * z) *
        (y ^ e * n)⁻¹ = z⁻¹ * pinnedX Tag.E6 L β₁ c₀ * z := by
  set M := familyGroup (K := L) (fun _ : Unit => a) with hMdef
  set y₀ := rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w with hy₀
  have huM : u ∈ M := rootSpan_le_familyGroup a hu
  obtain ⟨β₁, hβ₁⟩ := D.nonempty 0
  have hβ₁Sig : β₁ ∈ rootCharKernel a := (D.sig β₁).2 ⟨0, hβ₁⟩
  obtain ⟨i₁, hi₁⟩ := (D.sig _).1 (hgSig β₁ hβ₁Sig)
  obtain ⟨e, he⟩ := three_cycle_orbit D.π D.π_zero D.π_two i₁
  have hγ : (w ^ (e : ℕ)) • g β₁ ∈ D.C 0 := by
    have := pow_smul_mem_comp D (e : ℕ) i₁ _ hi₁
    rwa [he] at this
  have hγSig : (w ^ (e : ℕ)) • g β₁ ∈ rootCharKernel a := (D.sig _).2 ⟨0, hγ⟩
  obtain ⟨v, hv, hvγ⟩ := exists_reflection_word_of_iform_ne_zero hβ₁Sig hγSig
    (D.clique 0 _ hγ _ hβ₁)
  have hnv : canonicalRep (coxeterSystem Tag.E6) L v ∈ M := by
    refine canonicalRep_mem_familyGroup_of_closure (fun _ : Unit => a) ?_
    rwa [familyKernel_unit]
  have hy₀N : y₀ ∈ Subgroup.normalizer (M : Set (ModGL Tag.E6 L)) :=
    mul_mem (Subgroup.le_normalizer (Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup b)))
      (canonicalRep_mem_normalizer_familyGroup (a := fun _ : Unit => a) (fun _ => hw))
  have hyeN : y₀ ^ (e : ℕ) ∈ Subgroup.normalizer (M : Set (ModGL Tag.E6 L)) := pow_mem hy₀N _
  set Qs := canonicalRep (coxeterSystem Tag.E6) L v * (y₀ ^ (e : ℕ) * n) with hQs
  have hQsN : Qs ∈ Subgroup.normalizer (M : Set (ModGL Tag.E6 L)) :=
    mul_mem (Subgroup.le_normalizer hnv) (mul_mem hyeN hnN)
  have hQact := (actsAs_canonicalRep (L := L) v).mul
    ((actsAs_y0_pow (L := L) b w (e : ℕ)).mul hn)
  obtain ⟨-, ε, hε, hεc⟩ := hQact β₁ (D.root 0 β₁ hβ₁)
  have hψ : ((fun x => v • x) ∘ ((fun x => (w ^ (e : ℕ)) • x) ∘ g)) β₁ = β₁ := hvγ
  have hεc' : ∀ c : L, Qs * pinnedX Tag.E6 L β₁ c * Qs⁻¹ = pinnedX Tag.E6 L β₁ (ε * c) :=
    fun c => by rw [hεc c, hψ]
  have hℓ : 1 < ℓ ^ f := Nat.one_lt_pow (by omega) (Fact.out : ℓ.Prime).one_lt
  have hq : 0 < ℓ ^ f - 1 := by omega
  obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq ε⁻¹ hq
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow hq.ne'] at hc₀
    exact inv_ne_zero hε hc₀.symm
  have hX₀ : Qs * entrywiseFrobGL Tag.E6 L ℓ f (pinnedX Tag.E6 L β₁ c₀) * Qs⁻¹ =
      pinnedX Tag.E6 L β₁ c₀ := by
    rw [entrywiseFrobGL_pinnedX, iterateFrobenius_def, hεc']
    congr 1
    have h1 : c₀ ^ (ℓ ^ f) = ε⁻¹ * c₀ := by
      rw [← hc₀, ← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [h1, mul_inv_cancel_left₀ hε]
  have hye : y ^ (e : ℕ) = u⁻¹ * y₀ ^ (e : ℕ) * u := by
    rw [hy]
    have := conj_pow (a := u⁻¹) (b := y₀) (i := (e : ℕ))
    simpa using this
  have hmM : y ^ (e : ℕ) * (y₀ ^ (e : ℕ))⁻¹ * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ ∈ M := by
    have h1 : y₀ ^ (e : ℕ) * u * (y₀ ^ (e : ℕ))⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.1 hyeN u).1 huM
    have h2 : y ^ (e : ℕ) * (y₀ ^ (e : ℕ))⁻¹ * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ =
        u⁻¹ * (y₀ ^ (e : ℕ) * u * (y₀ ^ (e : ℕ))⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ := by
      rw [hye]
      group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem huM) h1) (inv_mem hnv)
  obtain ⟨z, hzM, hzm⟩ := lang_familyGroup ℓ (fun _ : Unit => a) f hf Qs hQsN _ hmM
  have hmQ : y ^ (e : ℕ) * (y₀ ^ (e : ℕ))⁻¹ * (canonicalRep (coxeterSystem Tag.E6) L v)⁻¹ * Qs =
      y ^ (e : ℕ) * n := by
    rw [hQs]
    group
  have key := theta_fixed_of_lang (entrywiseFrobGL Tag.E6 L ℓ f) hzm hX₀
  rw [hmQ] at key
  exact ⟨e, z, β₁, c₀, hzM, hβ₁, hc₀ne, key⟩

theorem exists_fixed_norm [IsAlgClosed L] {ℓ : ℕ} [Fact ℓ.Prime] [CharP L ℓ] {f : ℕ}
    (hf : 1 ≤ f) {a b : Fin Tag.E6.rank → Lˣ} {w : WeylGroup Tag.E6} (D : CompData a w)
    (hw : w ∈ rootCharStabilizer a) {u y n : ModGL Tag.E6 L}
    (hu : u ∈ rootSpan Tag.E6 L (rootCharKernel a))
    (hy : y = u⁻¹ * (rootDiagUnit Tag.E6 b * canonicalRep (coxeterSystem Tag.E6) L w) * u)
    (hy3 : y ^ 3 = 1) {g : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hn : ActsAs n g)
    (hgSig : ∀ β ∈ rootCharKernel a, g β ∈ rootCharKernel a)
    (hnN : n ∈ Subgroup.normalizer
      (familyGroup (K := L) (fun _ : Unit => a) : Set (ModGL Tag.E6 L)))
    (hΦy : n * entrywiseFrobGL Tag.E6 L ℓ f y * n⁻¹ = y) :
    ∃ x ∈ familyGroup (K := L) (fun _ : Unit => a), x ≠ 1 ∧ x ^ ℓ = 1 ∧ y * x * y⁻¹ = x ∧
      n * entrywiseFrobGL Tag.E6 L ℓ f x * n⁻¹ = x := by
  obtain ⟨e, z, β₁, c₀, hzM, hβ₁, hc₀, hfix⟩ := exists_theta_fixed hf D hw hu hy hn hgSig hnN
  obtain ⟨X, hX⟩ : ∃ X, X = z⁻¹ * pinnedX Tag.E6 L β₁ c₀ * z := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = y * X * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = y * A * y⁻¹ := ⟨_, rfl⟩
  rw [← hX] at hfix
  have hXY : X ∈ rootSpan Tag.E6 L (D.C 0) := by
    have h := conj_mem_comp D (inv_mem hzM) 0
      (rootSubgroup_le_rootSpan hβ₁ (mem_rootSubgroup.2 ⟨c₀, rfl⟩))
    rw [inv_inv] at h
    rw [hX]
    exact h
  have hAY : A ∈ rootSpan Tag.E6 L (D.C (D.π 0)) := by
    rw [hA]
    exact conj_y_mem_comp D hu hy 0 hXY
  have hBY : B ∈ rootSpan Tag.E6 L (D.C (D.π (D.π 0))) := by
    rw [hB]
    exact conj_y_mem_comp D hu hy _ hAY
  have h01 : (0 : Fin 3) ≠ D.π 0 := fun h => D.π_zero h.symm
  have h02 : (0 : Fin 3) ≠ D.π (D.π 0) := fun h => D.π_two h.symm
  have h12 : D.π 0 ≠ D.π (D.π 0) := fun h => D.π_zero (D.π.injective h).symm
  have hc01 : Commute X A := commute_comp D h01 hXY hAY
  have hc02 : Commute X B := commute_comp D h02 hXY hBY
  have hc12 : Commute A B := commute_comp D h12 hAY hBY
  have hΘ : y ^ e * frobTwistGL Tag.E6 L ℓ f n X * (y ^ e)⁻¹ = X := by
    rw [frobTwistGL_apply]
    calc y ^ e * (n * entrywiseFrobGL Tag.E6 L ℓ f X * n⁻¹) * (y ^ e)⁻¹ =
        (y ^ e * n) * entrywiseFrobGL Tag.E6 L ℓ f X * (y ^ e * n)⁻¹ := by group
      _ = X := hfix
  obtain ⟨hσ, hΦ⟩ := norm_fixed_algebra (frobTwistGL Tag.E6 L ℓ f n) e hA hB hy3 hΦy hΘ hc01 hc02
  have hXℓ : X ^ ℓ = 1 := by
    have h1 : (z⁻¹ * pinnedX Tag.E6 L β₁ c₀ * z) ^ ℓ = z⁻¹ * pinnedX Tag.E6 L β₁ c₀ ^ ℓ * z := by
      have := conj_pow (a := z⁻¹) (b := pinnedX Tag.E6 L β₁ c₀) (i := ℓ)
      simpa using this
    rw [hX, h1, pinnedX_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, pinnedX_zero]
    group
  have hAℓ : A ^ ℓ = 1 := by
    rw [hA, conj_pow, hXℓ]
    group
  have hBℓ : B ^ ℓ = 1 := by
    rw [hB, conj_pow, hAℓ]
    group
  refine ⟨X * A * B, mul_mem (mul_mem ?_ ?_) ?_, ?_, ?_, hσ, hΦ⟩
  · exact rootSpan_comp_le_familyGroup D 0 hXY
  · exact rootSpan_comp_le_familyGroup D _ hAY
  · exact rootSpan_comp_le_familyGroup D _ hBY
  · intro hx1
    have hXcomm : ∀ s ∈ rootSpan Tag.E6 L (D.C 0), Commute X s := by
      intro s hs
      have hAs : Commute s A := commute_comp D h01 hs hAY
      have hBs : Commute s B := commute_comp D h02 hs hBY
      have hXe : X = (A * B)⁻¹ := by
        have : X * (A * B) = 1 := by rw [← mul_assoc]; exact hx1
        exact eq_inv_of_mul_eq_one_left this
      rw [hXe]
      exact (hAs.mul_right hBs).inv_right.symm
    have hs : z⁻¹ * pinnedX Tag.E6 L (-β₁) 1 * z ∈ rootSpan Tag.E6 L (D.C 0) := by
      have h := conj_mem_comp D (inv_mem hzM) 0
        (rootSubgroup_le_rootSpan (D.neg 0 β₁ hβ₁) (mem_rootSubgroup.2 ⟨1, rfl⟩))
      rw [inv_inv] at h
      exact h
    have hcomm := hXcomm _ hs
    rw [hX] at hcomm
    have heq := hcomm.eq
    have hPQ : pinnedX Tag.E6 L β₁ c₀ * pinnedX Tag.E6 L (-β₁) 1 =
        pinnedX Tag.E6 L (-β₁) 1 * pinnedX Tag.E6 L β₁ c₀ := by
      calc pinnedX Tag.E6 L β₁ c₀ * pinnedX Tag.E6 L (-β₁) 1 =
          z * (z⁻¹ * pinnedX Tag.E6 L β₁ c₀ * z * (z⁻¹ * pinnedX Tag.E6 L (-β₁) 1 * z)) * z⁻¹ := by
            group
        _ = z * (z⁻¹ * pinnedX Tag.E6 L (-β₁) 1 * z *
            (z⁻¹ * pinnedX Tag.E6 L β₁ c₀ * z)) * z⁻¹ := by
            rw [heq]
        _ = pinnedX Tag.E6 L (-β₁) 1 * pinnedX Tag.E6 L β₁ c₀ := by group
    exact not_commute_pinnedX_neg (D.root 0 β₁ hβ₁) hc₀ one_ne_zero hPQ
  · have hXAB : Commute (X * A) B := hc02.mul_left hc12
    rw [hXAB.mul_pow, hc01.mul_pow, hXℓ, hAℓ, hBℓ]
    group

end HeisA

end CFSG.LieType.SeitzGeneration.ExcWideThree

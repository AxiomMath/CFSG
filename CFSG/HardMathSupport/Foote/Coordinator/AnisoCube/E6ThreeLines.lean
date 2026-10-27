module

public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.PlaneLevi
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.Descent
public import CFSG.HardMathSupport.Foote.Coordinator.AnisoCube.SingerDiag
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeKernel
public import CFSG.HardMathSupport.Malle.SeitzCube.E6ThreeSL3Sign
public import CFSG.HardMathSupport.Malle.SeitzCube.FrameBaseChange
public import CFSG.LieType.Chevalley.E6EvenRootTorusCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

open CFSG.HardMathSupport.Malle.SeitzCube
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open scoped MatrixGroups

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A (m := 2)) ∅

theorem map_baseChangeGL_rootSpan_le
    {τ : Tag} {K L : Type} [Field K] [Field L] (f : K →+* L)
    (S : Set (Fin τ.rank → ℤ)) : (rootSpan τ K S).map (baseChangeGL f) ≤ rootSpan τ L S := by
  simp only [rootSpan, Subgroup.map_iSup]
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, baseChangeGL_pinnedX]
  exact pinnedX_mem_rootSpan hα (f c)

theorem mem_range_algebraMap_of_pow_card_eq {K : Type} [Field K] [Finite K] {r : ℕ}
    [Fact r.Prime] [CharP K r] {n : ℕ} [NeZero n] {c : FiniteField.Extension K r n}
    (hc : c ^ Nat.card K = c) : c ∈ (algebraMap K (FiniteField.Extension K r n)).range := by
  have hfix : ∀ g : FiniteField.Extension K r n ≃ₐ[K] FiniteField.Extension K r n, g c = c := by
    intro g
    obtain ⟨i, -, rfl⟩ := FiniteField.Extension.exists_frob_pow_eq K r n g
    rw [FiniteField.Extension.frob_iterate_apply]
    induction i with
    | zero => simp
    | succ i ih => rw [pow_succ, pow_mul, ih, hc]
  obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) c).2 hfix
  exact ⟨y, hy⟩

theorem conj_mul_conj_eq {G : Type*} [Group G] {a b c e : G} (hac : Commute a c)
    (hae : Commute a e) (hbc : Commute b c) :
    a * b * a⁻¹ * (c * e * c⁻¹) = a * c * (b * e) * (a * c)⁻¹ := by
  have hY : Commute a (c * e * c⁻¹) := (hac.mul_right hae).mul_right hac.inv_right
  calc a * b * a⁻¹ * (c * e * c⁻¹) = a * b * (a⁻¹ * (c * e * c⁻¹)) := by rw [mul_assoc]
    _ = a * b * ((c * e * c⁻¹) * a⁻¹) := by rw [hY.inv_left.eq]
    _ = a * (b * c) * e * (c⁻¹ * a⁻¹) := by group
    _ = a * (c * b) * e * (c⁻¹ * a⁻¹) := by rw [hbc.eq]
    _ = a * c * (b * e) * (a * c)⁻¹ := by group

theorem exists_RA2_frame_eq (i : Fin 3) {a b : Fin 3} (hab : a ≠ b) :
    ∃ γ ∈ RA2, e6A2Frame i γ = e6A2Root i a b := by
  fin_cases a <;> fin_cases b
  · exact absurd rfl hab
  · refine ⟨![1, 0], ?_, by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨0, 1, by decide, by decide⟩
  · refine ⟨![1, 1], ?_, by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨0, 2, by decide, by decide⟩
  · refine ⟨![-1, 0], ?_, by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨1, 0, by decide, by decide⟩
  · exact absurd rfl hab
  · refine ⟨![0, 1], ?_, by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨1, 2, by decide, by decide⟩
  · refine ⟨![-1, -1], ?_, by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨2, 0, by decide, by decide⟩
  · refine ⟨![0, -1], ?_, by funext l; simp [e6A2Frame, e6A2Root, e6A2Weight]; ring⟩
    rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
    exact ⟨2, 1, by decide, by decide⟩
  · exact absurd rfl hab


section Frame


@[expose] def IsSignedFrame (F : Type) [Field F]
    (ψ : Fin 3 → SL(3, F) →* adjointGroup Tag.E6 F) : Prop :=
  ∀ i : Fin 3, ∀ γ ∈ RA2, ∀ c : F,
    ((ψ i (CFSG.LieType.Steinberg.SL.x 2 F γ c) : adjointGroup Tag.E6 F) : ModGL Tag.E6 F) =
      pinnedX Tag.E6 F (e6A2Frame i γ) ((e6A2Sign i γ : F) * c)

theorem rootSpan_block_two_le_range {F : Type} [Field F]
    {ψ : Fin 3 → SL(3, F) →* adjointGroup Tag.E6 F} (hψ : IsSignedFrame F ψ) :
    rootSpan Tag.E6 F (e6BlockRoots 2) ≤ ((adjointGroup Tag.E6 F).subtype.comp (ψ 2)).range := by
  refine iSup₂_le fun α hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  obtain ⟨-, a, b, hab, rfl⟩ := (mem_e6BlockRoots 2 α).1 hα
  obtain ⟨γ, hγ, he⟩ := exists_RA2_frame_eq 2 hab
  refine ⟨CFSG.LieType.Steinberg.SL.x 2 F γ ((e6A2Sign 2 γ : F) * c), ?_⟩
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hψ 2 γ hγ, ← mul_assoc, he]
  congr 1
  rcases e6A2Sign_eq 2 γ with h | h <;> rw [h] <;> simp

theorem not_mem_block_zero_one {α : Fin Tag.E6.rank → ℤ}
    (h : ∃ k ∉ e6FrameLeviSet 0 ∪ e6FrameLeviSet 1, α k ≠ 0) :
    α ∉ e6BlockRoots 0 ∧ α ∉ e6BlockRoots 1 := by
  obtain ⟨k, hk, hαk⟩ := h
  rw [Set.mem_union, not_or] at hk
  refine ⟨fun hα => ?_, fun hα => ?_⟩
  · obtain ⟨-, a, b, hab, rfl⟩ := (mem_e6BlockRoots 0 α).1 hα
    obtain ⟨γ, -, he⟩ := exists_RA2_frame_eq 0 hab
    exact hαk (by rw [← he]; exact e6A2Frame_apply_eq_zero 0 γ hk.1)
  · obtain ⟨-, a, b, hab, rfl⟩ := (mem_e6BlockRoots 1 α).1 hα
    obtain ⟨γ, -, he⟩ := exists_RA2_frame_eq 1 hab
    exact hαk (by rw [← he]; exact e6A2Frame_apply_eq_zero 1 γ hk.2)

end Frame

section Main


theorem conj_mem_rootSpan_kernel_of_commute {K L : Type} [Field K] [Field L] (f : K →+* L)
    {S : Set (Fin Tag.E6.rank → ℤ)}
    (hfix : ∀ (a : Fin Tag.E6.rank → Lˣ) (v : ModGL Tag.E6 L), v ∈ rootSpan Tag.E6 L S →
      v ∈ Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 L)) →
      v ∈ rootSpan Tag.E6 L (rootCharKernel a ∩ S))
    (hLevi : parabolicLevi Tag.E6 L (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ≤
      Subgroup.normalizer (rootSpan Tag.E6 L S : Set (ModGL Tag.E6 L)))
    {ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K} (hψ : IsSignedFrame K ψ)
    {ψL : Fin 3 → SL(3, L) →* adjointGroup Tag.E6 L} (hψL : IsSignedFrame L ψL)
    (hLcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψL i A) (ψL j B))
    {g : SL(3, K)} {l : L} (hl : l * l ^ Nat.card K * l ^ (Nat.card K ^ 2) = 1) (hl0 : l ≠ 0)
    {s : SL(3, L)}
    (hconj : Matrix.SpecialLinearGroup.map f g = s * singerDiag (Nat.card K) l hl * s⁻¹)
    {x y : ℕ} {u : ModGL Tag.E6 K} (hu : u ∈ rootSpan Tag.E6 K S)
    (hc : Commute u ((ψ 0 (g ^ x) * ψ 1 (g ^ y) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) :
    ((ψL 0 s * ψL 1 s : adjointGroup Tag.E6 L) : ModGL Tag.E6 L)⁻¹ * baseChangeGL f u *
        ((ψL 0 s * ψL 1 s : adjointGroup Tag.E6 L) : ModGL Tag.E6 L) ∈
      rootSpan Tag.E6 L (rootCharKernel (e6KerChar (Units.mk0 l hl0) (Nat.card K) x y) ∩ S) := by
  classical
  set φ : Fin 3 → SL(3, K) →* ModGL Tag.E6 K :=
    fun i => (adjointGroup Tag.E6 K).subtype.comp (ψ i) with hφ
  set Φ : Fin 3 → SL(3, L) →* ModGL Tag.E6 L :=
    fun i => (adjointGroup Tag.E6 L).subtype.comp (ψL i) with hΦ
  have hΦc : ∀ i j, i ≠ j → ∀ A B, Commute (Φ i A) (Φ j B) := fun i j hij A B =>
    (hLcomm i j hij A B).map (adjointGroup Tag.E6 L).subtype
  have hmap : ∀ i A, Φ i (Matrix.SpecialLinearGroup.map f A) = baseChangeGL f (φ i A) :=
    fun i A => sl3Hom_map_eq_of_pinnedX f (e6A2Frame i) (e6A2Sign i) (φ i) (Φ i) (hψ i) (hψL i) A
  set ζ : Lˣ := Units.mk0 l hl0 with hζdef
  set q := Nat.card K with hqdef
  set d := singerDiag q l hl with hd
  have hdc : ((d : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal ![l, l ^ q, l ^ (q ^ 2)] := rfl
  have hdm : ∀ m : ℕ, ((d ^ m : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun j => ((e6Dg ζ q m j : Lˣ) : L) := by
    intro m
    rw [Matrix.SpecialLinearGroup.coe_pow, hdc, Matrix.diagonal_pow]
    congr 1
    funext j
    fin_cases j <;> simp [e6Dg, ← pow_mul, mul_comm, hζdef]
  have ht : ∀ (i : Fin 3) (m : ℕ),
      Φ i (d ^ m) = rootDiagUnit Tag.E6 (e6A2TorusChar i (e6Dg ζ q m)) := fun i m =>
    sl3Hom_diag_eq_rootDiagUnit_of_signs i (Φ i) (e6A2Sign i) (fun γ _ => e6A2Sign_eq i γ)
      (hψL i) (e6Dg ζ q m) (d ^ m) (hdm m)
  set X : ModGL Tag.E6 L := Φ 0 (d ^ x) * Φ 1 (d ^ y) with hX
  have htt : X = rootDiagUnit Tag.E6 (e6KerChar ζ q x y) := by
    rw [hX, ht, ht, ← rootDiagUnit_mul]
    rfl
  set h : ModGL Tag.E6 L := Φ 0 s * Φ 1 s with hh
  have hgL : ∀ m : ℕ, Matrix.SpecialLinearGroup.map f (g ^ m) = s * d ^ m * s⁻¹ := by
    intro m
    rw [map_pow, hconj, conj_pow]
  have hbX : baseChangeGL f (φ 0 (g ^ x) * φ 1 (g ^ y)) = h * X * h⁻¹ := by
    rw [map_mul, ← hmap, ← hmap, hgL, hgL, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact conj_mul_conj_eq (hΦc 0 1 (by decide) s s) (hΦc 0 1 (by decide) s _)
      (hΦc 0 1 (by decide) _ s)
  set uL := baseChangeGL f u with huLdef
  have huL : uL ∈ rootSpan Tag.E6 L S := map_baseChangeGL_rootSpan_le f S ⟨u, hu, rfl⟩
  have hcL : Commute uL (h * X * h⁻¹) := by
    rw [← hbX]
    exact (show Commute u (φ 0 (g ^ x) * φ 1 (g ^ y)) from hc).map (baseChangeGL f)
  have hvX : Commute (h⁻¹ * uL * h) X := by
    have e := hcL.eq
    show h⁻¹ * uL * h * X = X * (h⁻¹ * uL * h)
    calc h⁻¹ * uL * h * X = h⁻¹ * (uL * (h * X * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * X * h⁻¹) * uL) * h := by rw [e]
      _ = X * (h⁻¹ * uL * h) := by group
  have hψL' : ∀ i : Fin 3, ∀ γ : Fin 2 → ℤ, γ ∈ RA2 → ∃ ε : L, (ε = 1 ∨ ε = -1) ∧ ∀ c : L,
      ((ψL i (CFSG.LieType.Steinberg.SL.x 2 L γ c) : adjointGroup Tag.E6 L) : ModGL Tag.E6 L) =
        pinnedX Tag.E6 L (e6A2Frame i γ) (ε * c) := by
    intro i γ hγ
    refine ⟨(e6A2Sign i γ : L), ?_, hψL i γ hγ⟩
    rcases e6A2Sign_eq i γ with h1 | h1 <;> rw [h1] <;> simp
  have hh0 : Φ 0 s ∈ parabolicLevi Tag.E6 L (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
    parabolicLevi_mono Set.subset_union_left (range_le_parabolicLevi_E6 L ψL hψL' 0 s)
  have hh1 : Φ 1 s ∈ parabolicLevi Tag.E6 L (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) :=
    parabolicLevi_mono Set.subset_union_right (range_le_parabolicLevi_E6 L ψL hψL' 1 s)
  have hvS : h⁻¹ * uL * h ∈ rootSpan Tag.E6 L S := by
    have hn := hLevi (inv_mem (mul_mem hh0 hh1))
    have := (Subgroup.mem_normalizer_iff.1 hn uL).1 huL
    rwa [inv_inv] at this
  have hvC : h⁻¹ * uL * h ∈ Subgroup.centralizer
      ({rootDiagUnit Tag.E6 (e6KerChar ζ q x y)} : Set (ModGL Tag.E6 L)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [← htt]
    exact hvX.eq.symm
  exact hfix _ _ hvS hvC

theorem mem_range_two_of_commute {K : Type} [Field K] [Finite K] {r : ℕ} [Fact r.Prime]
    [CharP K r] {S : Set (Fin Tag.E6.rank → ℤ)}
    (hfix : ∀ (a : Fin Tag.E6.rank → (FiniteField.Extension K r 3)ˣ)
      (v : ModGL Tag.E6 (FiniteField.Extension K r 3)),
      v ∈ rootSpan Tag.E6 (FiniteField.Extension K r 3) S →
      v ∈ Subgroup.centralizer
        ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 (FiniteField.Extension K r 3))) →
      v ∈ rootSpan Tag.E6 (FiniteField.Extension K r 3) (rootCharKernel a ∩ S))
    (hS : ∀ α ∈ S, α ∉ e6BlockRoots 0 ∧ α ∉ e6BlockRoots 1)
    (hLevi : parabolicLevi Tag.E6 (FiniteField.Extension K r 3)
        (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1) ≤
      Subgroup.normalizer (rootSpan Tag.E6 (FiniteField.Extension K r 3) S :
        Set (ModGL Tag.E6 (FiniteField.Extension K r 3))))
    {ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K} (hψ : IsSignedFrame K ψ)
    {ψL : Fin 3 → SL(3, FiniteField.Extension K r 3) →*
      adjointGroup Tag.E6 (FiniteField.Extension K r 3)}
    (hψL : IsSignedFrame (FiniteField.Extension K r 3) ψL)
    (hLinj : ∀ i, Function.Injective (ψL i))
    (hLcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψL i A) (ψL j B))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpr : p ≠ r)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : SL(3, K)} (hg : orderOf g = p) {x y : ℕ}
    (hxy : ¬ (p ∣ x ∧ p ∣ y))
    (hD4 : ¬ p ∣ x → ∀ s : Fin 3, (y : ZMod p) ≠ (x : ZMod p) * (Nat.card K : ZMod p) ^ (s : ℕ))
    {u : ModGL Tag.E6 K} (hu : u ∈ rootSpan Tag.E6 K S)
    (hc : Commute u ((ψ 0 (g ^ x) * ψ 1 (g ^ y) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) :
    u ∈ ((adjointGroup Tag.E6 K).subtype.comp (ψ 2)).range := by
  classical
  set L := FiniteField.Extension K r 3 with hLdef
  set f : K →+* L := algebraMap K L with hfdef
  set φ : Fin 3 → SL(3, K) →* ModGL Tag.E6 K :=
    fun i => (adjointGroup Tag.E6 K).subtype.comp (ψ i) with hφ
  set Φ : Fin 3 → SL(3, L) →* ModGL Tag.E6 L :=
    fun i => (adjointGroup Tag.E6 L).subtype.comp (ψL i) with hΦ
  have hΦc : ∀ i j, i ≠ j → ∀ A B, Commute (Φ i A) (Φ j B) := fun i j hij A B =>
    (hLcomm i j hij A B).map (adjointGroup Tag.E6 L).subtype
  have hmap : ∀ i A, Φ i (Matrix.SpecialLinearGroup.map f A) = baseChangeGL f (φ i A) :=
    fun i A => sl3Hom_map_eq_of_pinnedX f (e6A2Frame i) (e6A2Sign i) (φ i) (Φ i) (hψ i) (hψL i) A
  obtain ⟨l, hl, s, hlord, hconj⟩ := exists_sl3_conj_singerDiag (K := K) (r := r) hp hp3 hpr hpq hg
  have hl0 : l ≠ 0 := by
    intro h0
    have h1 := pow_orderOf_eq_one l
    rw [hlord, h0, zero_pow hp.ne_zero] at h1
    exact zero_ne_one h1
  have hζ : orderOf (Units.mk0 l hl0) = p := by
    rw [← orderOf_units, Units.val_mk0]
    exact hlord
  have hvK := conj_mem_rootSpan_kernel_of_commute f hfix hLevi hψ hψL hLcomm hl hl0 hconj hu hc
  set h : ModGL Tag.E6 L := Φ 0 s * Φ 1 s with hh
  have hker : rootCharKernel (e6KerChar (Units.mk0 l hl0) (Nat.card K) x y) ∩ S ⊆
      e6BlockRoots 2 := by
    rintro α ⟨hαk, hαS⟩
    obtain ⟨hα0, hα1⟩ := hS α hαS
    by_cases hx : p ∣ x
    · have hy : ¬ p ∣ y := fun hy => hxy ⟨hx, hy⟩
      rw [rootCharKernel_e6KerChar_block02 hp hp3 hζ hpq hx hy] at hαk
      exact hαk.resolve_left hα0
    · by_cases hy : p ∣ y
      · rw [rootCharKernel_e6KerChar_block12 hp hp3 hζ hpq hx hy] at hαk
        exact hαk.resolve_left hα1
      · rw [rootCharKernel_e6KerChar_block2 hp hp3 hζ hpq hx hy (hD4 hx)] at hαk
        exact hαk
  obtain ⟨z, hz⟩ := rootSpan_block_two_le_range hψL (rootSpan_mono hker hvK)
  have hhz : Commute h (Φ 2 z) :=
    (hΦc 0 2 (by decide) s z).mul_left (hΦc 1 2 (by decide) s z)
  have huL2 : baseChangeGL f u = Φ 2 z := by
    have hz' : Φ 2 z = h⁻¹ * baseChangeGL f u * h := hz
    have e : baseChangeGL f u = h * (h⁻¹ * baseChangeGL f u * h) * h⁻¹ := by group
    rw [e, ← hz', hhz.eq, mul_inv_cancel_right]
  set σ : L →+* L := (FiniteField.Extension.frob K r 3).toAlgHom.toRingHom with hσ
  have hσf : σ.comp f = f := RingHom.ext fun c => (FiniteField.Extension.frob K r 3).commutes c
  have hσfix : ∀ c : L, σ c = c → c ∈ f.range := fun c hc =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← FiniteField.Extension.frob_apply]; exact hc)
  have hσmap : ∀ A, Φ 2 (Matrix.SpecialLinearGroup.map σ A) = baseChangeGL σ (Φ 2 A) :=
    fun A => sl3Hom_map_eq_of_pinnedX σ (e6A2Frame 2) (e6A2Sign 2) (Φ 2) (Φ 2) (hψL 2) (hψL 2) A
  have hΦinj : Function.Injective (Φ 2) := Subtype.val_injective.comp (hLinj 2)
  exact mem_range_of_baseChangeGL_mem_range f σ hσf hσfix (φ 2) (Φ 2) (hmap 2) hσmap hΦinj
    ⟨z, huL2.symm⟩

theorem mem_rootSpan_radical_inter_of_mem_centralizer {F : Type} [Field F]
    {J : Set (Fin Tag.E6.rank)} {a : Fin Tag.E6.rank → Fˣ} {v : ModGL Tag.E6 F}
    (hv : v ∈ rootSpan Tag.E6 F (parabolicRadicalRoots Tag.E6 J))
    (hva : v ∈ Subgroup.centralizer ({rootDiagUnit Tag.E6 a} : Set (ModGL Tag.E6 F))) :
    v ∈ rootSpan Tag.E6 F (rootCharKernel a ∩ parabolicRadicalRoots Tag.E6 J) :=
  CFSG.LieType.Chevalley.E6EvenRootTorus.mem_rootSpan_inter_of_mem_centralizer
    (fun _ hα => ⟨(mem_parabolicRadicalRoots_iff.1 hα).1, (mem_parabolicRadicalRoots_iff.1 hα).2.1⟩)
    (fun _ hα _ hβ _ _ hm hn hr => add_mem_parabolicRadicalRoots
      ⟨(mem_parabolicRadicalRoots_iff.1 hα).1, (mem_parabolicRadicalRoots_iff.1 hα).2.1⟩
      hβ hm hn hr)
    hv hva

theorem mem_range_two_of_mem_radical_of_commute {K : Type} [Field K] [Finite K] {r : ℕ}
    [Fact r.Prime] [CharP K r] {ψ : Fin 3 → SL(3, K) →* adjointGroup Tag.E6 K}
    (hψ : IsSignedFrame K ψ)
    {ψL : Fin 3 → SL(3, FiniteField.Extension K r 3) →*
      adjointGroup Tag.E6 (FiniteField.Extension K r 3)}
    (hψL : IsSignedFrame (FiniteField.Extension K r 3) ψL)
    (hLinj : ∀ i, Function.Injective (ψL i))
    (hLcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψL i A) (ψL j B))
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpr : p ≠ r)
    (hpq : p ∣ Nat.card K ^ 2 + Nat.card K + 1) {g : SL(3, K)} (hg : orderOf g = p) {x y : ℕ}
    (hxy : ¬ (p ∣ x ∧ p ∣ y))
    (hD4 : ¬ p ∣ x → ∀ s : Fin 3, (y : ZMod p) ≠ (x : ZMod p) * (Nat.card K : ZMod p) ^ (s : ℕ))
    {u : ModGL Tag.E6 K}
    (hu : u ∈ parabolicRadical Tag.E6 K (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
    (hc : Commute u ((ψ 0 (g ^ x) * ψ 1 (g ^ y) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) :
    u ∈ ((adjointGroup Tag.E6 K).subtype.comp (ψ 2)).range :=
  mem_range_two_of_commute (S := parabolicRadicalRoots Tag.E6 (e6FrameLeviSet 0 ∪ e6FrameLeviSet 1))
    (fun _ _ hv hva => mem_rootSpan_radical_inter_of_mem_centralizer hv hva)
    (fun _ hα => not_mem_block_zero_one (mem_parabolicRadicalRoots_iff.1 hα).2.2)
    ((parabolicLevi_le_parabolicSubgroup _).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical _))
    hψ hψL hLinj hLcomm hp hp3 hpr hpq hg hxy hD4 hu hc

end Main

end CFSG.HardMathSupport.Foote.Coordinator.AnisoCube

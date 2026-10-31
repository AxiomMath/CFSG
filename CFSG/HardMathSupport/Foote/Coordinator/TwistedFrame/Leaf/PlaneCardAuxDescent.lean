module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted2
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.ConjSub
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnSyl
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.RankThree.PartOne.KE.SLnShape

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.RankThree.PartOne.KE

set_option linter.unusedSectionVars false


namespace TwCardAux

theorem mem_frame_iff {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) (x : ModGL τ K) :
    x ∈ D.frame S ↔ x ∈ adjointGroup τ K ∧
      D.g⁻¹ * baseChangeGL (algebraMap K D.L) x * D.g ∈ rootSpan τ D.L S := by
  unfold LangLevi.frame
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, inv_inv]

variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ}

theorem g_mem_adjointGroup (D : LangLevi τ K w) : D.g ∈ adjointGroup τ D.L :=
  Pθ_le_adjointGroup τ D.L (Lθ_le_Pθ τ D.L D.g_mem)

abbrev fixedRootGroup (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) :
    Subgroup (ModGL τ D.L) :=
  rootSpan τ D.L S ⊓ twistedFixedPoints (canonicalRep (coxeterSystem τ) D.L w)
    (Units.map (entrywiseHom D.Fr))

theorem frame_equiv_fixed (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ))
    (hrat : ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb τ K D.L).range)
    (hfin : Finite ↥(rootSpan τ D.L S ⊓ twistedFixedPoints
      (canonicalRep (coxeterSystem τ) D.L w) (Units.map (entrywiseHom D.Fr))))
    (hperf : ⁅rootSpan τ D.L S ⊓ twistedFixedPoints
        (canonicalRep (coxeterSystem τ) D.L w) (Units.map (entrywiseHom D.Fr)),
      rootSpan τ D.L S ⊓ twistedFixedPoints
        (canonicalRep (coxeterSystem τ) D.L w) (Units.map (entrywiseHom D.Fr))⁆ =
      rootSpan τ D.L S ⊓ twistedFixedPoints
        (canonicalRep (coxeterSystem τ) D.L w) (Units.map (entrywiseHom D.Fr))) :
    Nonempty (↥(D.frame S) ≃* ↥(rootSpan τ D.L S ⊓ twistedFixedPoints
      (canonicalRep (coxeterSystem τ) D.L w) (Units.map (entrywiseHom D.Fr)))) := by
  classical
  set n := canonicalRep (coxeterSystem τ) D.L w with hn
  set Φ : ModGL τ D.L →* ModGL τ D.L := Units.map (entrywiseHom D.Fr) with hΦ
  set P : Subgroup (ModGL τ D.L) := rootSpan τ D.L S ⊓ twistedFixedPoints n Φ with hP
  have hgC : D.g ∈ adjointGroup τ D.L := g_mem_adjointGroup D
  have hlang : Φ D.g = D.g * n := D.lang
  have hle : D.frame S ≤ adjointGroup τ K := fun x hx => ((mem_frame_iff D S x).1 hx).1
  have hΦb : ∀ x : D.frame S,
      Φ (baseChangeGL (algebraMap K D.L) (x : ModGL τ K)) =
        baseChangeGL (algebraMap K D.L) (x : ModGL τ K) := fun x =>
    adjEmb_frobenius D.Fr D.hFr ⟨(x : ModGL τ K), hle x.2⟩
  let ψ : D.frame S →* ModGL τ D.L :=
    (MulAut.conj D.g⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K D.L)).comp (D.frame S).subtype)
  have hψ : ∀ x : D.frame S, ψ x = D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g :=
    fun x => by simp [ψ, MulAut.conj_apply]
  have hψmem : ∀ x : D.frame S, ψ x ∈ P := by
    intro x
    refine Subgroup.mem_inf.2 ⟨?_, mem_twistedFixedPoints.2 ?_⟩
    · rw [hψ]
      exact ((mem_frame_iff D S x).1 x.2).2
    · rw [hψ, map_mul, map_mul, map_inv, hΦb x, hlang]
      group
  let ψ' : D.frame S →* P := ψ.codRestrict P hψmem
  have hinj : Function.Injective ψ' := by
    intro x y h
    have h1 : ψ x = ψ y := congrArg Subtype.val h
    rw [hψ, hψ] at h1
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact Subtype.ext (baseChangeGL_injective (algebraMap K D.L) h2)
  have hsurj : Function.Surjective ψ' := by
    rintro ⟨y, hy⟩
    set P' : Subgroup (ModGL τ D.L) := P.map (MulAut.conj D.g).toMonoidHom with hP'
    haveI hPfin : Finite P := hfin
    have hP'fin : Finite P' :=
      Finite.of_equiv P (Subgroup.equivMapOfInjective P _ (MulAut.conj D.g).injective).toEquiv
    have hP'C : P' ≤ adjointGroup τ D.L := by
      rintro _ ⟨u, hu, rfl⟩
      have hu' : u ∈ adjointGroup τ D.L := rootSpan_le_adjointGroup D.L S hu.1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hgC hu') (inv_mem hgC)
    have hP'F : ∀ x ∈ P', Φ x = x := by
      rintro _ ⟨u, hu, rfl⟩
      have hu' : n * Φ u * n⁻¹ = u := mem_twistedFixedPoints.1 hu.2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, hlang]
      calc D.g * n * Φ u * (D.g * n)⁻¹ = D.g * (n * Φ u * n⁻¹) * D.g⁻¹ := by group
        _ = D.g * u * D.g⁻¹ := by rw [hu']
    have hP'perf : ⁅P', P'⁆ = P' := by
      rw [hP', ← Subgroup.map_commutator, hperf]
    have hmem : D.g * y * D.g⁻¹ ∈ P' :=
      ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    obtain ⟨z, hz⟩ := hrat P' hP'fin hP'C hP'F hP'perf hmem
    have hzx : (z : ModGL τ K) ∈ D.frame S := by
      rw [mem_frame_iff]
      refine ⟨z.2, ?_⟩
      have : baseChangeGL (algebraMap K D.L) (z : ModGL τ K) = D.g * y * D.g⁻¹ := hz
      rw [this]
      have e : D.g⁻¹ * (D.g * y * D.g⁻¹) * D.g = y := by group
      rw [e]
      exact hy.1
    refine ⟨⟨(z : ModGL τ K), hzx⟩, Subtype.ext ?_⟩
    show ψ ⟨(z : ModGL τ K), hzx⟩ = y
    rw [hψ]
    have : baseChangeGL (algebraMap K D.L) (z : ModGL τ K) = D.g * y * D.g⁻¹ := hz
    simp only [this]
    group
  exact ⟨MulEquiv.ofBijective ψ' ⟨hinj, hsurj⟩⟩

theorem frame_card_dvd_of (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ))
    (P₀ : Subgroup (ModGL τ D.L)) (hP₀ : P₀ ≤ fixedRootGroup D S) (hfin : Finite P₀)
    (hrat : P₀.map (MulAut.conj D.g).toMonoidHom ≤ (adjEmb τ K D.L).range) :
    Nat.card ↥P₀ ∣ Nat.card ↥(D.frame S) := by
  classical
  have hle : D.frame S ≤ adjointGroup τ K := fun x hx => ((mem_frame_iff D S x).1 hx).1
  let ψ : D.frame S →* ModGL τ D.L :=
    (MulAut.conj D.g⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K D.L)).comp (D.frame S).subtype)
  have hψ : ∀ x : D.frame S, ψ x = D.g⁻¹ * baseChangeGL (algebraMap K D.L) (x : ModGL τ K) * D.g :=
    fun x => by simp [ψ, MulAut.conj_apply]
  have hinj : Function.Injective ψ := by
    intro x y h
    rw [hψ, hψ] at h
    have h2 := mul_left_cancel (mul_right_cancel h)
    exact Subtype.ext (baseChangeGL_injective (algebraMap K D.L) h2)
  have hP₀ψ : P₀ ≤ ψ.range := by
    intro y hy
    have hmem : D.g * y * D.g⁻¹ ∈ P₀.map (MulAut.conj D.g).toMonoidHom :=
      ⟨y, hy, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    obtain ⟨z, hz⟩ := hrat hmem
    have hzx : (z : ModGL τ K) ∈ D.frame S := by
      rw [mem_frame_iff]
      refine ⟨z.2, ?_⟩
      have : baseChangeGL (algebraMap K D.L) (z : ModGL τ K) = D.g * y * D.g⁻¹ := hz
      rw [this]
      have e : D.g⁻¹ * (D.g * y * D.g⁻¹) * D.g = y := by group
      rw [e]
      exact (hP₀ hy).1
    refine ⟨⟨(z : ModGL τ K), hzx⟩, ?_⟩
    rw [hψ]
    have : baseChangeGL (algebraMap K D.L) (z : ModGL τ K) = D.g * y * D.g⁻¹ := hz
    simp only [this]
    group
  have h1 : Nat.card ↥P₀ ∣ Nat.card ψ.range := Subgroup.card_dvd_of_le hP₀ψ
  have h2 : Nat.card ψ.range = Nat.card ↥(D.frame S) := Nat.card_range_of_injective hinj
  rw [h2] at h1
  exact h1

theorem conj_fixedRootGroup (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ))
    (P₀ : Subgroup (ModGL τ D.L)) (hP₀ : P₀ ≤ fixedRootGroup D S) :
    P₀.map (MulAut.conj D.g).toMonoidHom ≤ adjointGroup τ D.L ∧
      ∀ x ∈ P₀.map (MulAut.conj D.g).toMonoidHom, Units.map (entrywiseHom D.Fr) x = x := by
  have hgC : D.g ∈ adjointGroup τ D.L := g_mem_adjointGroup D
  have hlang : Units.map (entrywiseHom D.Fr) D.g = D.g * canonicalRep (coxeterSystem τ) D.L w :=
    D.lang
  refine ⟨?_, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : u ∈ adjointGroup τ D.L := rootSpan_le_adjointGroup D.L S (hP₀ hu).1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hgC hu') (inv_mem hgC)
  · rintro _ ⟨u, hu, rfl⟩
    have hu' : canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) u *
        (canonicalRep (coxeterSystem τ) D.L w)⁻¹ = u := mem_twistedFixedPoints.1 (hP₀ hu).2
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [map_mul, map_mul, map_inv, hlang]
    calc D.g * canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) u *
          (D.g * canonicalRep (coxeterSystem τ) D.L w)⁻¹
        = D.g * (canonicalRep (coxeterSystem τ) D.L w * Units.map (entrywiseHom D.Fr) u *
          (canonicalRep (coxeterSystem τ) D.L w)⁻¹) * D.g⁻¹ := by group
      _ = D.g * u * D.g⁻¹ := by rw [hu']

theorem frame_card_dvd (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ))
    (hrat : ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb τ K D.L).range)
    (P₀ : Subgroup (ModGL τ D.L)) (hP₀ : P₀ ≤ fixedRootGroup D S) (hfin : Finite P₀)
    (hperf : ⁅P₀, P₀⁆ = P₀) :
    Nat.card ↥P₀ ∣ Nat.card ↥(D.frame S) := by
  refine frame_card_dvd_of D S P₀ hP₀ hfin ?_
  obtain ⟨hC, hF⟩ := conj_fixedRootGroup D S P₀ hP₀
  haveI : Finite P₀ := hfin
  refine hrat _ (Finite.of_equiv P₀
    (Subgroup.equivMapOfInjective P₀ _ (MulAut.conj D.g).injective).toEquiv) hC hF ?_
  rw [← Subgroup.map_commutator, hperf]

theorem frame_card_dvd_pgroup (D : LangLevi τ K w) (S : Set (Fin τ.rank → ℤ)) {p : ℕ}
    (hrat : ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → IsPGroup p P →
        P ≤ (adjEmb τ K D.L).range)
    (P₀ : Subgroup (ModGL τ D.L)) (hP₀ : P₀ ≤ fixedRootGroup D S) (hfin : Finite P₀)
    (hpg : IsPGroup p P₀) :
    Nat.card ↥P₀ ∣ Nat.card ↥(D.frame S) := by
  refine frame_card_dvd_of D S P₀ hP₀ hfin ?_
  obtain ⟨hC, hF⟩ := conj_fixedRootGroup D S P₀ hP₀
  haveI : Finite P₀ := hfin
  refine hrat _ (Finite.of_equiv P₀
    (Subgroup.equivMapOfInjective P₀ _ (MulAut.conj D.g).injective).toEquiv) hC hF ?_
  exact hpg.map _

theorem hrat_perfect {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) (D : LangLevi τ K w) :
    ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → ⁅P, P⁆ = P →
        P ≤ (adjEmb τ K D.L).range := by
  intro P hP hPC hPF hperf
  haveI := hP
  rw [adjEmb_range]
  exact (finite_fixed_subgroup_rational_perfect d hτ D.Fr D.hFr P hPC hPF).2.2 P le_rfl hperf

theorem hrat_pgroup {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) (D : LangLevi τ K w)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ∀ P : Subgroup (ModGL τ D.L), Finite P → P ≤ adjointGroup τ D.L →
      (∀ x ∈ P, Units.map (entrywiseHom D.Fr) x = x) → IsPGroup p P →
        P ≤ (adjEmb τ K D.L).range := by
  intro P hP hPC hPF hpg
  haveI := hP
  rw [adjEmb_range]
  exact (finite_fixed_subgroup_rational_perfect d hτ D.Fr D.hFr P hPC hPF).2.1 p hp hp3 P le_rfl hpg

section Unitary

open Matrix CFSG.RankThree.Classical2 CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

theorem card_unitarySet_int {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP Ω ℓ] (hf : 1 ≤ f) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card (unitarySet (ℓ ^ f) n : Set (GL (Fin n) Ω)) : ℤ) =
      ((ℓ ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((ℓ ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  obtain ⟨K, hKcard, hKmem⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_exists_subfield
    (Ω := Ω) (ℓ := ℓ) hf
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hKcard]
    exact pow_ne_zero _ (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero))
  have hrange : ∀ c : Ω, c ∈ Set.range K.subtype ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [← hKmem]
    exact ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun h => ⟨⟨c, h⟩, rfl⟩⟩
  have hinj : Function.Injective
      (GeneralLinearGroup.map K.subtype : GL (Fin n) K →* GL (Fin n) Ω) :=
    fun A B h => Units.ext (Matrix.map_injective K.subtype_injective (congrArg Units.val h))
  haveI : CharP K ℓ := (RingHom.charP_iff K.subtype K.subtype_injective ℓ).mpr inferInstance
  rw [← CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_image_SUid K.subtype hrange n (ℓ := ℓ) (f := f),
    Nat.card_image_of_injective hinj, SetLike.coe_sort_coe,
    SUid_eq_statedSU hKcard n]
  exact CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int ⟨Fact.out, hf, by rw [hKcard]; ring⟩ hn

theorem card_unitarySet_three {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP Ω ℓ] (hf : 1 ≤ f) :
    Nat.card (unitarySet (ℓ ^ f) 3 : Set (GL (Fin 3) Ω)) =
      (ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1)) := by
  have h := card_unitarySet_int (Ω := Ω) (ℓ := ℓ) hf (n := 3) (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at h
  have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos (Fact.out : ℓ.Prime).pos f)
  have h2 : ((Nat.card (unitarySet (ℓ ^ f) 3 : Set (GL (Fin 3) Ω)) : ℕ) : ℤ) =
      (((ℓ ^ f) ^ 3 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1)) : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub h1]
    norm_num
  exact_mod_cast h2

theorem card_unitarySet_five {Ω : Type} [Field Ω] [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP Ω ℓ] (hf : 1 ≤ f) :
    Nat.card (unitarySet (ℓ ^ f) 5 : Set (GL (Fin 5) Ω)) =
      (ℓ ^ f) ^ 10 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) *
        (((ℓ ^ f) ^ 4 - 1) * ((ℓ ^ f) ^ 5 + 1))) := by
  have h := card_unitarySet_int (Ω := Ω) (ℓ := ℓ) hf (n := 5) (by norm_num)
  rw [show Finset.Icc 2 5 = {2, 3, 4, 5} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton] at h
  rw [show 5 * (5 - 1) / 2 = 10 by norm_num] at h
  have h1 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ (pow_pos (Fact.out : ℓ.Prime).pos f)
  have h2 : 1 ≤ (ℓ ^ f) ^ 4 := Nat.one_le_pow _ _ (pow_pos (Fact.out : ℓ.Prime).pos f)
  have h3 : ((Nat.card (unitarySet (ℓ ^ f) 5 : Set (GL (Fin 5) Ω)) : ℕ) : ℤ) =
      (((ℓ ^ f) ^ 10 * (((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) *
        (((ℓ ^ f) ^ 4 - 1) * ((ℓ ^ f) ^ 5 + 1))) : ℕ) : ℤ) := by
    rw [h]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2]
    ring
  exact_mod_cast h3

theorem exists_prime_pow_card (K : Type) [Field K] [Finite K] :
    ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ Nat.card K = ℓ ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  exact ⟨ringChar K, n, hp, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

end Unitary

section UFrameSection

open Matrix CFSG.RankThree.Classical2
open scoped MatrixGroups

structure UFrame (τ : Tag) (L : Type) [Field L] (ν : ℕ) (S : Set (Fin τ.rank → ℤ)) where
  ρ : SL(ν, L) →* ModGL τ L
  r : Fin ν → Fin ν → Fin τ.rank → ℤ
  ε : Fin ν → Fin ν → Lˣ
  inj : Function.Injective ρ
  isRoot : ∀ i j, i ≠ j → IsRoot τ (r i j)
  gen : ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
    ρ (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (r i j) ((ε i j : L) * t)
  range : ρ.range = rootSpan τ L S

@[expose] def perm3 : Fin 6 → Equiv.Perm (Fin 3)
  | 0 => 1
  | 1 => Equiv.swap 0 1
  | 2 => Equiv.swap 0 2
  | 3 => Equiv.swap 1 2
  | 4 => Equiv.swap 0 1 * Equiv.swap 1 2
  | 5 => Equiv.swap 1 2 * Equiv.swap 0 1

theorem units_map_comp {L : Type} [Field L] (σ σ' : L →+* L) (g : ModGL τ L) :
    Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ') g) =
      Units.map (entrywiseHom (σ.comp σ')) g :=
  Units.ext (entrywise_entrywise σ σ' _)

theorem frobenius_bijective' {K : Type} [Field K] [Finite K] (D : LangLevi τ K w) :
    Function.Bijective D.Fr := by
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  refine ⟨D.Fr.injective, fun y => ?_⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (Nat.card_pos : 0 < Nat.card K)
  exact ⟨x, by rw [D.hFr, hx]⟩

theorem UFrame.fixedRoot_unitary {K : Type} [Field K] [Finite K] {w : WeylGroup τ}
    (D : LangLevi τ K w) {ν : ℕ} (hν : 3 ≤ ν) {S : Set (Fin τ.rank → ℤ)}
    (E : UFrame τ D.L ν S) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ i j, i ≠ j → w • E.r i j = E.r (π j) (π i)) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hk : Nat.card K = ℓ ^ f) :
    Finite ↥(fixedRootGroup D S) ∧
      Nat.card ↥(fixedRootGroup D S) =
        Nat.card (unitarySet (ℓ ^ f) ν : Set (GL (Fin ν) D.L)) ∧
      ((ν, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple ↥(fixedRootGroup D S) ∧
        Nat.card ↥(Subgroup.center ↥(fixedRootGroup D S)) = Nat.gcd ν (ℓ ^ f + 1)) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set n := canonicalRep (coxeterSystem τ) D.L w with hn
  have hnm : n ∈ monomialSubgroup τ D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hwn : weylQuotientHom τ D.L ⟨n, hnm⟩ = w :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep w)
  have hconj : ∀ i j : Fin ν, i ≠ j → ∃ b : D.Lˣ, ∀ c : D.L,
      n * pinnedX τ D.L (E.r i j) c * n⁻¹ = pinnedX τ D.L (E.r (π j) (π i)) ((b : D.L) * c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hnm (E.isRoot i j hij)
    exact ⟨μ, fun c => by rw [hμ c, hwn, hπ i j hij]⟩
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n E.ρ E.inj E.r E.ε E.gen D.Fr
    (frobenius_bijective' D) n (fun i j => (π j, π i)) (fun i j hij => (π.injective.ne hij).symm)
    (fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩) hconj
  have hq : ∀ c : D.L, D.Fr c = c ^ ℓ ^ f := fun c => by rw [D.hFr, hk]
  have hshape' : ∀ (i j : Fin ν) (hij : i ≠ j) (t : D.L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, D.L)) :
        Matrix (Fin ν) (Fin ν) D.L) = 1 + Matrix.single (π j) (π i) ((b i j : D.L) * t ^ ℓ ^ f) := by
    intro i j hij t
    rw [hshape i j hij t, hq]
  obtain ⟨-, ⟨H, hH⟩, hfin, hbig, -⟩ := sln_root_permuting_frobenius_fixed_unitary (k := K)
    (Ω := D.L) hℓ hf hk hν π Φ' b hshape'
  have hPeq : fixedRootGroup D S = (fixSubgroup Φ').map E.ρ := by
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy1' : y ∈ E.ρ.range := by rw [E.range]; exact hy1
      obtain ⟨X, rfl⟩ := hy1'
      refine ⟨X, ?_, rfl⟩
      have h := mem_twistedFixedPoints.1 hy2
      rw [hΦ' X] at h
      exact E.inj h
    · rintro ⟨X, hX, rfl⟩
      refine ⟨?_, mem_twistedFixedPoints.2 ?_⟩
      · rw [← E.range]
        exact ⟨X, rfl⟩
      · rw [hΦ' X]
        have h : Φ' X = X := hX
        rw [h]
  let e : ↥(fixedRootGroup D S) ≃* ↥(fixSubgroup Φ') :=
    ((MulEquiv.subgroupCongr hPeq).trans ((fixSubgroup Φ').equivMapOfInjective E.ρ E.inj).symm)
  refine ⟨Finite.of_equiv _ e.symm.toEquiv, ?_, fun hne => ?_⟩
  · rw [Nat.card_congr e.toEquiv]
    exact CFSG.GH74.GLS.Stage2.Bender.Thm1.mnSyl_card_eq_of_conj (fixSubgroup Φ')
      (unitarySet (ℓ ^ f) ν) (fun Y hY => hY.2.1) H hH
  · obtain ⟨hQ, -, hcard⟩ := hbig hne
    refine ⟨CFSG.IsQuasisimple.of_mulEquiv e hQ, ?_⟩
    rw [natCard_center_eq_of_mulEquiv e, hcard]

end UFrameSection

end TwCardAux

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

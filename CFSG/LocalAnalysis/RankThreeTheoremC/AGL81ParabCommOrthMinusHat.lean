module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusCover
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusSchur
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpOTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentLinUnitParabGroup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusBlocks
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusSemi

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.Assembly.LowTwoRank CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.LinUnitParab
  (not_isSolvable_of_isQuasisimple)
open scoped commutatorElement

section Blocks

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem eq_bot_of_isPGroup_of_norm_SL {k : ℕ} (T : Subgroup (GL (Fin k) K)) (hT : IsPGroup 2 T)
    (hnorm : ∀ (B : SpecialLinearGroup (Fin k) K), ∀ t ∈ T,
      (SpecialLinearGroup.toGL B : GL (Fin k) K) * t * (SpecialLinearGroup.toGL B)⁻¹ ∈ T) :
    T = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : SpecialLinearGroup (Fin k) K →* GL (Fin k) K := SpecialLinearGroup.toGL with hρ
  have hnormal : (T.comap ρ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hnorm g (ρ n) hn⟩
  have hle : T.comap ρ ≤ CFSG.pCore 2 (SpecialLinearGroup (Fin k) K) :=
    le_sSup ⟨hnormal, hT.comap_of_injective ρ SpecialLinearGroup.toGL_injective⟩
  rw [Sp.pCore_specialLinear_eq_bot] at hle
  rw [eq_bot_iff]
  intro t ht
  have hcomm : ∀ s ∈ ρ.range, t * s = s * t := by
    rintro _ ⟨g, rfl⟩
    have h1 : ρ g * t * (ρ g)⁻¹ ∈ T := hnorm g t ht
    have h2 : ρ g * t * (ρ g)⁻¹ * t⁻¹ ∈ T := T.mul_mem h1 (T.inv_mem ht)
    obtain ⟨g', hg'⟩ : ρ g * t * (ρ g)⁻¹ * t⁻¹ ∈ ρ.range := by
      have h3 : t * (ρ g)⁻¹ * t⁻¹ ∈ ρ.range :=
        Sp.conj_mem_range_toGL t (ρ.range.inv_mem ⟨g, rfl⟩)
      simpa only [mul_assoc] using ρ.range.mul_mem (⟨g, rfl⟩ : ρ g ∈ ρ.range) h3
    have hg'1 : g' = 1 :=
      Subgroup.mem_bot.mp (hle (by rw [Subgroup.mem_comap, hg']; exact h2))
    rw [hg'1, map_one] at hg'
    exact ((mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hg'.symm))).symm
  obtain ⟨k₀, hk₀⟩ := hT ⟨t, ht⟩
  exact Sp.eq_one_of_mem_center_of_pow_two_pow (Sp.mem_center_of_commute_with_range_toGL hcomm)
    (congrArg Subtype.val hk₀)

theorem eq_bot_of_isPGroup_of_norm_orthDerived {b c : K} {m : ℕ} (hm : 1 ≤ m)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0)
    (R : Subgroup (((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin m ⊕ Fin m → K) × (Fin 2 → K))))
    (hR : IsPGroup 2 R)
    (hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup (quadTail m (minusTailForm K b c)))
    (hnorm : ∀ g ∈ orthDerived (quadTail m (minusTailForm K b c)), ∀ x ∈ R, g * x * g⁻¹ ∈ R) :
    R = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q' := quadTail m (minusTailForm K b c) with hQ'
  set Ω := orthDerived Q' with hΩ
  obtain ⟨f, hK⟩ : ∃ f, Nat.card K = 2 ^ f := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
  obtain ⟨hsimple, hnc, -⟩ := orthResDer_facts hK hm hirr
  have hΩO : Ω ≤ TauCeti.QuadraticMap.orthogonalGroup Q' :=
    orthDerived_le_orthogonalGroup_of_commutator Q'
  have hW : ((R ⊓ Ω).subgroupOf Ω).Normal := ⟨fun y hy ω => by
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ ω.2 hy.2)
      (Subgroup.inv_mem _ ω.2)⟩
    have := hnorm ω ω.2 y hy.1
    simpa using this⟩
  have hbot : (R ⊓ Ω).subgroupOf Ω = ⊥ := by
    haveI : IsSimpleGroup ↥Ω := hsimple
    haveI := hW
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((R ⊓ Ω).subgroupOf Ω) with h | h
    · exact h
    · exfalso
      have hΩR : Ω ≤ R := fun ω hω => by
        have : (⟨ω, hω⟩ : ↥Ω) ∈ (R ⊓ Ω).subgroupOf Ω := h ▸ Subgroup.mem_top _
        exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 this)).1
      have hp : IsPGroup 2 ↥Ω := hR.to_le hΩR
      haveI : Finite (((Fin m ⊕ Fin m → K) × (Fin 2 → K)) ≃ₗ[K]
          ((Fin m ⊕ Fin m → K) × (Fin 2 → K))) := finite_orthLinearEquiv
      haveI : Finite ↥Ω := inferInstance
      haveI : Group.IsNilpotent ↥Ω := hp.isNilpotent
      have hsol : Group.IsSolvable ↥Ω := inferInstance
      exact not_isSolvable_of_isQuasisimple (orthMinus_isQuasisimple_of_simple hnc).1 hsol
  rw [eq_bot_iff]
  intro x hx
  have hcomm : ∀ ω ∈ Ω, x * ω = ω * x := by
    intro ω hω
    have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q' := hRO hx
    have h1 : ω * x * ω⁻¹ * x⁻¹ ∈ R :=
      R.mul_mem (hnorm ω hω x hx) (R.inv_mem hx)
    have h2 : ω * x * ω⁻¹ * x⁻¹ ∈ Ω := by
      have hc : ⁅x, ω⁻¹⁆ ∈ Ω := Subgroup.commutator_mem_commutator hxO (hΩO (Ω.inv_mem hω))
      have : ω * x * ω⁻¹ * x⁻¹ = ω * (⁅x, ω⁻¹⁆ * ω⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [this]
      exact Ω.mul_mem hω (Ω.mul_mem hc (Ω.inv_mem hω))
    have h3 : (⟨ω * x * ω⁻¹ * x⁻¹, h2⟩ : ↥Ω) ∈ (R ⊓ Ω).subgroupOf Ω :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨h1, h2⟩)
    rw [hbot, Subgroup.mem_bot] at h3
    have h4 : ω * x * ω⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h3
    calc x * ω = (ω * x * ω⁻¹ * x⁻¹) * (x * ω) := by rw [h4, one_mul]
      _ = ω * x := by group
  obtain ⟨-, a, ha0, ha⟩ := schur_tail hm hirr x.toAddEquiv (RingEquiv.refl K)
    (fun a v => by simp) 1
    (fun v => by
      have := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (hRO hx) v
      simpa using this)
    (fun g hg v => by
      have := hcomm g hg
      exact LinearEquiv.congr_fun this v)
  obtain ⟨v₀, hv₀⟩ := exists_quadTail_ne_zero (r := m) (b := b) (c := c) hirr
  have hx1 : x = 1 :=
    scalar_eq_one_of_isometry (hRO hx) (mem_scalars.2 ⟨a, fun v => ha v⟩) hv₀
  rw [hx1]
  exact Subgroup.one_mem _

end Blocks

namespace OmCover

variable {A : Type} [Group A] {Y P : Subgroup A} {r : ℕ} {K : Type} [Field K] {b c : K} {s : ℕ}
  {d : Fin (s + 1) → ℕ} (C : OmCover Y P r K b c d)

theorem mem_flag_iff (g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    g ∈ orthParab r (minusTailForm K b c) d ↔ ((C.ρ g : ↥Y) : A) ∈ P := by
  rw [← C.comap_eq]
  rfl

@[expose] noncomputable def toP : ↥(orthParab r (minusTailForm K b c) d) →* ↥P :=
  (((Y.subtype).comp C.ρ.toMonoidHom).comp
    (orthParab r (minusTailForm K b c) d).subtype).codRestrict P fun q =>
      (C.mem_flag_iff q.1).mp q.2

@[simp] theorem coe_toP (x : ↥(orthParab r (minusTailForm K b c) d)) :
    ((C.toP x : ↥P) : A) = ((C.ρ x : ↥Y) : A) := rfl

theorem toP_injective : Function.Injective C.toP := by
  intro x y h
  apply Subtype.ext
  apply C.ρ.injective
  apply Subtype.ext
  exact congrArg (fun z : ↥P => (z : A)) h

theorem toP_surjective (hPY : P ≤ Y) : Function.Surjective C.toP := by
  rintro ⟨w, hw⟩
  have hgQ : C.ρ.symm ⟨w, hPY hw⟩ ∈ orthParab r (minusTailForm K b c) d := by
    rw [C.mem_flag_iff, MulEquiv.apply_symm_apply]
    exact hw
  exact ⟨⟨_, hgQ⟩, Subtype.ext (by rw [coe_toP, MulEquiv.apply_symm_apply])⟩

@[expose] noncomputable def toHat :
    ↥(orthParab r (minusTailForm K b c) d) →* ↥P ⧸ CFSG.pCore 2 ↥P :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥P)).comp C.toP

theorem toHat_surjective (hPY : P ≤ Y) : Function.Surjective C.toHat :=
  (QuotientGroup.mk'_surjective _).comp (C.toP_surjective hPY)

theorem ker_toHat_eq : C.toHat.ker = (CFSG.pCore 2 ↥P).comap C.toP := by
  rw [toHat, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

variable [Finite A] [Finite K] [CharP K 2]

theorem isPGroup_ker_toHat : IsPGroup 2 C.toHat.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ker_toHat_eq]
  exact (CFSG.pCore_isPGroup (p := 2) (G := ↥P)).comap_of_injective C.toP C.toP_injective

theorem ker_orthLeviHom_le_ker_toHat (hd : OrthCuts r d) (hPY : P ≤ Y) :
    (orthLeviHom b c hd).ker ≤ C.toHat.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  haveI : ((orthLeviHom b c hd).ker.map C.toP).Normal :=
    (MonoidHom.normal_ker (orthLeviHom b c hd)).map C.toP (C.toP_surjective hPY)
  have hle : (orthLeviHom b c hd).ker.map C.toP ≤ CFSG.pCore 2 ↥P :=
    le_sSup ⟨inferInstance, (isPGroup_ker_orthLeviHom hd).map _⟩
  rw [ker_toHat_eq]
  exact hle ⟨x, hx, rfl⟩

theorem orthBlockHom_eq_one_of_mem_ker_toHat (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hPY : P ≤ Y) (l : Fin s) {x : ↥(orthParab r (minusTailForm K b c) d)}
    (hx : x ∈ C.toHat.ker) : orthBlockHom (minusTailForm K b c) hd l x = 1 := by
  set T := C.toHat.ker.map (orthBlockHom (minusTailForm K b c) hd l) with hT
  have hTp : IsPGroup 2 T := (isPGroup_ker_toHat C).map _
  have hbot : T = ⊥ := by
    refine eq_bot_of_isPGroup_of_norm_SL T hTp fun B t ht => ?_
    obtain ⟨y, hy, rfl⟩ := ht
    refine ⟨orthLeviSL hd (minusTailForm K b c) hr l B * y *
      (orthLeviSL hd (minusTailForm K b c) hr l B)⁻¹,
      (MonoidHom.normal_ker C.toHat).conj_mem y hy _, ?_⟩
    rw [map_mul, map_mul, map_inv, orthBlockHom_orthLeviSL_self]
  have hmem : orthBlockHom (minusTailForm K b c) hd l x ∈ T := ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem orthResHom_eq_one_of_mem_ker_toHat (hd : OrthCuts r d) (hr : 3 ≤ r)
    (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hPY : P ≤ Y) (hm : 1 ≤ r - d (Fin.last s))
    {x : ↥(orthParab r (minusTailForm K b c) d)} (hx : x ∈ C.toHat.ker) :
    orthResHom (minusTailForm K b c) hd x = 1 := by
  set R := C.toHat.ker.map (orthResHom (minusTailForm K b c) hd) with hR
  have hRp : IsPGroup 2 R := (isPGroup_ker_toHat C).map _
  have hRO : R ≤ TauCeti.QuadraticMap.orthogonalGroup
      (quadTail (r - d (Fin.last s)) (minusTailForm K b c)) := by
    rintro _ ⟨y, -, rfl⟩
    exact orthResHom_mem_orthogonalGroup hd y
  have hnorm : ∀ g ∈ orthDerived (quadTail (r - d (Fin.last s)) (minusTailForm K b c)),
      ∀ z ∈ R, g * z * g⁻¹ ∈ R := by
    intro g hg z hz
    obtain ⟨y, hy, rfl⟩ := hz
    refine ⟨orthLeviResElt b c hd (commutator_orthogonalGroup_quadTail_minus hr hirr) ⟨g, hg⟩ * y *
      (orthLeviResElt b c hd (commutator_orthogonalGroup_quadTail_minus hr hirr) ⟨g, hg⟩)⁻¹,
      (MonoidHom.normal_ker C.toHat).conj_mem y hy _, ?_⟩
    rw [map_mul, map_mul, map_inv, orthResHom_orthLeviResElt]
  have hbot := eq_bot_of_isPGroup_of_norm_orthDerived hm hirr R hRp hRO hnorm
  have hmem : orthResHom (minusTailForm K b c) hd x ∈ R := ⟨x, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

end OmCover

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

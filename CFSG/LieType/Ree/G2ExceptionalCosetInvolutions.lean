module

public import CFSG.LieType.Ree.G2ExceptionalFieldInvolutionComponents
public import CFSG.LieType.Chevalley.LangActualInvolutionReduction
public import CFSG.LieType.AlgebraicGroups.RootCoordinateLang
public import CFSG.LieType.Chevalley.EvenQuadraticGraphFieldDescent

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial

theorem coe_pow_apply_of_entrywise_frobenius {τ : Tag} {L : Type} [Field L] (p : ℕ) [ExpChar L p]
    (Fr : MulAut (adjointGroup τ L))
    (hFr : ∀ g, (Fr g : ModGL τ L) =
      Units.map (entrywiseHom (iterateFrobenius L p 1)) (g : ModGL τ L))
    (n : ℕ) (g : adjointGroup τ L) :
    ((Fr ^ n) g : ModGL τ L) =
      Units.map (entrywiseHom (iterateFrobenius L p n)) (g : ModGL τ L) := by
  induction n generalizing g with
  | zero =>
    rw [pow_zero, MulAut.one_apply, iterateFrobenius_zero]
    ext1
    exact (entrywise_id (R := L) _).symm
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, hFr]
    ext1
    simp only [Units.coe_map]
    refine (entrywise_entrywise (R := L) _ _ _).trans ?_
    congr 1
    refine RingHom.ext fun c => ?_
    rw [RingHom.comp_apply, iterateFrobenius_def, iterateFrobenius_def, iterateFrobenius_def,
      ← pow_mul, pow_one, ← pow_succ']

theorem G2_exceptional_coset_involution_conj
    (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (g : adjointGroup ReeTag.G2.tag K)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut K a) ^ 2 = 1) :
    ∃ ψ : MulAut (adjointGroup ReeTag.G2.tag K),
      ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K a) * ψ⁻¹ = ReeTag.G2.finiteReeAut K a := by
  classical
  have : CharP K 3 := ‹CharP K ReeTag.G2.prime›
  let : Algebra (ZMod 3) K := ZMod.algebra K 3
  let L := AlgebraicClosure K
  have : IsAlgClosure (ZMod 3) L := IsAlgClosure.ofAlgebraic (ZMod 3) K L
  have : CharP L 3 := charP_of_injective_algebraMap (algebraMap K L).injective 3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φK : MulAut (adjointGroup Tag.G2 K) := ReeTag.G2.finiteExceptionalAut K
  let FrK : MulAut (adjointGroup Tag.G2 K) := ReeTag.G2.finiteFrobeniusAut K
  let FK : MulAut (adjointGroup Tag.G2 K) := ReeTag.G2.finiteReeAut K a
  let g' : adjointGroup Tag.G2 K := g
  have hp0 : ReeTag.G2.perm ⟨0, by decide⟩ = ⟨1, by decide⟩ := by decide
  have hp1 : ReeTag.G2.perm ⟨1, by decide⟩ = ⟨0, by decide⟩ := by decide
  have he0 : ReeTag.G2.exponent ⟨0, by decide⟩ = 1 := by decide
  have he1 : ReeTag.G2.exponent ⟨1, by decide⟩ = 3 := by decide
  have hφx0 : ∀ c : K, φK (xElement ⟨0, by decide⟩ c) = xElement ⟨1, by decide⟩ c := fun c => by
    have h := ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := K) ⟨0, by decide⟩ c
    rw [hp0, he0, pow_one] at h
    exact h
  have hφx1 : ∀ c : K, φK (xElement ⟨1, by decide⟩ c) = xElement ⟨0, by decide⟩ (c ^ 3) :=
    fun c => by
    have h := ReeTag.finiteExceptionalAut_xElement (t := ReeTag.G2) (K := K) ⟨1, by decide⟩ c
    rw [hp1, he1] at h
    exact h
  have hφy0 : ∀ c : K, φK (yElement ⟨0, by decide⟩ c) = yElement ⟨1, by decide⟩ c := fun c => by
    have h := ReeTag.finiteExceptionalAut_yElement (t := ReeTag.G2) (K := K) ⟨0, by decide⟩ c
    rw [hp0, he0, pow_one] at h
    exact h
  have hφy1 : ∀ c : K, φK (yElement ⟨1, by decide⟩ c) = yElement ⟨0, by decide⟩ (c ^ 3) :=
    fun c => by
    have h := ReeTag.finiteExceptionalAut_yElement (t := ReeTag.G2) (K := K) ⟨1, by decide⟩ c
    rw [hp1, he1] at h
    exact h
  have hFrKc : ∀ u : adjointGroup Tag.G2 K, (FrK u : ModGL Tag.G2 K) =
      Units.map (entrywiseHom (frobenius K ReeTag.G2.prime)) (u : ModGL Tag.G2 K) := fun _ => rfl
  have hFK : ∀ u, FK u = φK ((FrK ^ a) u) := fun _ => rfl
  obtain ⟨Φ, hΦ, -, hΦFr, -⟩ := exceptional_Lang_G2_closure_exceptional_map (L := L)
  obtain ⟨⟨Fr, hFr⟩, -⟩ := (exceptional_Lang_root_coordinate_surjectivity 3 L).1 Tag.G2 1 le_rfl
  have hLang := (exceptional_Lang_root_coordinate_surjectivity 3 L).2.2 rfl Φ hΦ Fr hFr a
  obtain ⟨hsq, hcomm⟩ := hΦFr (iterateFrobenius L 3 1) fun c => by
    rw [iterateFrobenius_def, pow_one]
  have hFrtw : ∀ x, Fr x = frobeniusTwist Tag.G2 L (iterateFrobenius L 3 1) x := fun x =>
    Subtype.ext (hFr x)
  have hΦΦ : Φ * Φ = Fr := MulEquiv.ext fun x => by
    rw [MulAut.mul_apply, hFrtw]
    exact DFunLike.congr_fun hsq x
  have hΦFr' : Commute Φ Fr := MulEquiv.ext fun x => by
    rw [MulAut.mul_apply, MulAut.mul_apply, hFrtw, hFrtw]
    exact DFunLike.congr_fun hcomm x
  set S := Φ * Fr ^ a with hSdef
  have hSS : S * S = Fr ^ (2 * a + 1) := by
    have hc : Fr ^ a * Φ = Φ * Fr ^ a := ((hΦFr'.pow_right a).eq).symm
    calc S * S = Φ * (Fr ^ a * Φ) * Fr ^ a := by rw [hSdef]; group
      _ = Φ * Φ * (Fr ^ a * Fr ^ a) := by rw [hc]; group
      _ = Fr ^ (2 * a + 1) := by rw [hΦΦ, ← pow_add, ← pow_succ']; ring_nf
  set Frq := iterateFrobenius L 3 (2 * a + 1) with hFrq
  have hFrqc : ∀ c, Frq c = c ^ Nat.card K := fun c => by rw [hFrq, iterateFrobenius_def, hK]
  have hS2 : ∀ x : adjointGroup Tag.G2 L,
      ((S (S x) : adjointGroup Tag.G2 L) : ModGL Tag.G2 L) =
        Units.map (entrywiseHom Frq) (x : ModGL Tag.G2 L) := fun x => by
    rw [← MulAut.mul_apply, hSS]
    exact coe_pow_apply_of_entrywise_frobenius 3 Fr hFr _ x
  set ι := adjointBaseChangeHom Tag.G2 (algebraMap K L) with hιdef
  have hιx : ∀ (i : Fin Tag.G2.rank) (c : K), ι (xElement i c) = xElement i (algebraMap K L c) :=
    fun i c => Subtype.ext (baseChangeGL_xUnit _ i c)
  have hιy : ∀ (i : Fin Tag.G2.rank) (c : K), ι (yElement i c) = yElement i (algebraMap K L c) :=
    fun i c => Subtype.ext (baseChangeGL_yUnit _ i c)
  have hΦι : ∀ u : adjointGroup Tag.G2 K, Φ (ι u) = ι (φK u) := by
    have h := adjointGroup_hom_ext (f := Φ.toMonoidHom.comp ι) (g := ι.comp φK.toMonoidHom)
      (fun i c => by
        fin_cases i
        · exact ((congrArg Φ (hιx _ c)).trans (hΦ _).1).trans
            ((hιx _ c).symm.trans (congrArg ι (hφx0 c).symm))
        · exact ((congrArg Φ (hιx _ c)).trans (hΦ _).2.2.1).trans
            (((hιx _ (c ^ 3)).trans (by rw [map_pow])).symm.trans (congrArg ι (hφx1 c).symm)))
      (fun i c => by
        fin_cases i
        · exact ((congrArg Φ (hιy _ c)).trans (hΦ _).2.1).trans
            ((hιy _ c).symm.trans (congrArg ι (hφy0 c).symm))
        · exact ((congrArg Φ (hιy _ c)).trans (hΦ _).2.2.2).trans
            (((hιy _ (c ^ 3)).trans (by rw [map_pow])).symm.trans (congrArg ι (hφy1 c).symm)))
    exact fun u => DFunLike.congr_fun h u
  have hFrι : ∀ u : adjointGroup Tag.G2 K, Fr (ι u) = ι (FrK u) := fun u => by
    refine Subtype.ext ?_
    rw [hFr]
    change Units.map (entrywiseHom (iterateFrobenius L 3 1))
        (baseChangeGL (algebraMap K L) (u : ModGL Tag.G2 K)) =
      baseChangeGL (algebraMap K L) (FrK u : ModGL Tag.G2 K)
    have hσ : (iterateFrobenius L 3 1).comp (algebraMap K L) =
        (algebraMap K L).comp (frobenius K ReeTag.G2.prime) := RingHom.ext fun c => by
      simp only [RingHom.comp_apply, iterateFrobenius_def, frobenius_def, pow_one, map_pow]
      rfl
    rw [hFrKc, units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hσ]
  have hFrnι : ∀ (n : ℕ) (u : adjointGroup Tag.G2 K), (Fr ^ n) (ι u) = ι ((FrK ^ n) u) := by
    intro n
    induction n with
    | zero => intro u; rfl
    | succ n ih =>
      intro u
      rw [pow_succ, MulAut.mul_apply, pow_succ, MulAut.mul_apply]
      exact (congrArg (Fr ^ n) (hFrι u)).trans (ih _)
  have hSι : ∀ u : adjointGroup Tag.G2 K, S (ι u) = ι (FK u) := fun u => by
    rw [hSdef, MulAut.mul_apply, hFK]
    exact (congrArg Φ (hFrnι a u)).trans (hΦι _)
  have hrange : ι.range = langRationalImage Tag.G2 K L := by
    ext y
    rw [MonoidHom.mem_range, mem_langRationalImage]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨u, hu, huy⟩
      exact ⟨⟨u, hu⟩, Subtype.ext huy⟩
  obtain ⟨e, he⟩ : ∃ e : adjointGroup Tag.G2 K ≃* langRationalImage Tag.G2 K L,
      ∀ u, (e u : adjointGroup Tag.G2 L) = ι u :=
    ⟨(MonoidHom.ofInjective (adjointBaseChangeHom_injective Tag.G2 (algebraMap K L))).trans
      (MulEquiv.subgroupCongr hrange), fun _ => rfl⟩
  have hcongr : ∀ (β : MulAut (adjointGroup Tag.G2 K)) (v : adjointGroup Tag.G2 K),
      MulAut.congr e β (e v) = e (β v) := fun β v => by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  have hSH : (langRationalImage Tag.G2 K L).map S.toMonoidHom = langRationalImage Tag.G2 K L := by
    rw [← hrange, MonoidHom.map_range]
    have hcomp : S.toMonoidHom.comp ι = ι.comp FK.toMonoidHom := MonoidHom.ext hSι
    rw [hcomp, MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  have hx : ι g' ∈ Subgroup.normalizer
      (langRationalImage Tag.G2 K L : Set (adjointGroup Tag.G2 L)) :=
    Subgroup.le_normalizer (hrange ▸ ⟨g', rfl⟩)
  have hodd : Odd (Nat.card K) := hK ▸ Odd.pow (by decide)
  obtain ⟨-, hred⟩ := exceptional_Lang_actual_involution_conjugacy_reduction hodd Frq hFrqc S hSH
    hS2 hLang (ι g') hx
  let α : MulAut (adjointGroup Tag.G2 K) := MulAut.conj g' * FK
  have hα1 : α * α = 1 := by
    rw [← sq]
    exact hα
  have hα' : ∀ u, ((MulAut.congr e α) u : adjointGroup Tag.G2 L) = ι g' * S u * (ι g')⁻¹ := by
    intro u
    obtain ⟨v, rfl⟩ := e.surjective u
    rw [hcongr, he, he, hSι]
    change ι (g' * FK v * g'⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hα'2 : MulAut.congr e α * MulAut.congr e α = 1 := by
    rw [← map_mul, hα1, map_one]
  obtain ⟨h, -, ψ', -, hψ', -⟩ := hred (MulAut.congr e α) hα' hα'2
  have hψF : ψ' * MulAut.congr e α * ψ'⁻¹ = MulAut.congr e FK := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hψ' u]
    obtain ⟨v, rfl⟩ := e.surjective u
    rw [hcongr, he, he, hSι]
  have hfin : (MulAut.congr e).symm ψ' * α * ((MulAut.congr e).symm ψ')⁻¹ = FK := by
    refine (MulAut.congr e).injective ?_
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hψF
  exact ⟨(MulAut.congr e).symm ψ', hfin⟩

theorem G2_exceptional_coset_involution_fixed_p_components
    (a : ℕ) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1))
    (g : adjointGroup ReeTag.G2.tag K)
    (hα : (MulAut.conj g * ReeTag.G2.finiteReeAut K a) ^ 2 = 1) :
    (∃ ψ : MulAut (adjointGroup ReeTag.G2.tag K),
      ψ * (MulAut.conj g * ReeTag.G2.finiteReeAut K a) * ψ⁻¹ = ReeTag.G2.finiteReeAut K a) ∧
    (∀ p : ℕ, p.Prime → ∀ L : Subgroup
        ((MulAut.conj g * ReeTag.G2.finiteReeAut K a).toMonoidHom.eqLocus (MonoidHom.id _)),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) ∧
    (a = 0 → Nat.card ((MulAut.conj g * ReeTag.G2.finiteReeAut K a).toMonoidHom.eqLocus
      (MonoidHom.id _)) = 1512) := by
  classical
  obtain ⟨ψ, hψ⟩ := G2_exceptional_coset_involution_conj a K hK g hα
  obtain ⟨-, ⟨e, -⟩, -, -⟩ := fixed_centralizer_of_conj_eq hψ
  obtain ⟨-, -, -, -, hcomp, hzero⟩ := G2_exceptional_field_involution_fixed_p_components a K hK
  refine ⟨⟨ψ, hψ⟩, fun p hp L hL => ?_, fun ha => ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    have : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
    have : Finite ((MulAut.conj g * ReeTag.G2.finiteReeAut K a).toMonoidHom.eqLocus
      (MonoidHom.id _)) := Subtype.finite
    have : Finite ((ReeTag.G2.finiteReeAut K a).toMonoidHom.eqLocus (MonoidHom.id _)) :=
      Subtype.finite
    have hL' := (p_component_isomorphism_transport p hp e).1 L |>.1 hL
    exact (isQuasisimple_congr (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective)).2
      (hcomp p hp _ hL')
  · rw [Nat.card_congr e.toEquiv]
    exact (hzero ha).1

end CFSG.LieType.Ree

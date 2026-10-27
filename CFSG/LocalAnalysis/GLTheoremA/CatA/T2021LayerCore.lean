module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterLinear
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterUnitary
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterClassical
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterTriality
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterExc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterExcTwisted
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerExc
import CFSG.LocalAnalysis.GLTheoremA.CatB.List93RkL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015
  CFSG.LocalAnalysis.GLTheoremA.S10
open scoped Pointwise

theorem t2021Layer_twoPart_pow_mul (k : ℕ) {m : ℕ} (hm : m ≠ 0) :
    twoPart (2 ^ k * m) = 2 ^ k * twoPart m := by
  unfold twoPart
  rw [Nat.factorization_mul (pow_ne_zero k two_ne_zero) hm, Finsupp.add_apply, pow_add,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem t2021Layer_twoPart_dvd {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) : twoPart a ∣ twoPart b := by
  unfold twoPart
  exact pow_dvd_pow 2 ((Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hb h) hb).2 h 2)

theorem t2021Layer_card_le_two {S : Type} [Group S] [Finite S] {C E U : Subgroup S}
    (hEC : E ≤ C) (hUC : U ≤ C) (hEn : ∀ c ∈ C, ∀ x ∈ E, c * x * c⁻¹ ∈ E)
    (hU2 : IsPGroup 2 U) (hUE : U ⊓ E = ⊥)
    (h2 : twoPart (Nat.card C) ≤ 2 * twoPart (Nat.card E)) : Nat.card U ≤ 2 := by
  classical
  have hUN : U ≤ Subgroup.normalizer (E : Set S) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hEn u (hUC hu) x
    · intro hx
      have := hEn u⁻¹ (C.inv_mem (hUC hu)) _ hx
      simpa [mul_assoc] using this
  have hset : ((U ⊔ E : Subgroup S) : Set S) = (U : Set S) * (E : Set S) :=
    Subgroup.coe_mul_of_left_le_normalizer_right U E hUN
  have hbij : Function.Bijective fun x : ↥U × ↥E =>
      (⟨(x.1 : S) * x.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
        (Subgroup.mem_sup_right x.2.2)⟩ : ↥(U ⊔ E)) := by
    constructor
    · rintro ⟨u, e⟩ ⟨u', e'⟩ h
      have h0 : (u : S) * e = u' * e' := congrArg Subtype.val h
      have h1 : (u' : S)⁻¹ * u = e' * (e : S)⁻¹ := by
        calc (u' : S)⁻¹ * u = (u' : S)⁻¹ * ((u : S) * e) * (e : S)⁻¹ := by group
          _ = (u' : S)⁻¹ * ((u' : S) * e') * (e : S)⁻¹ := by rw [h0]
          _ = e' * (e : S)⁻¹ := by group
      have hmem : (u' : S)⁻¹ * u ∈ U ⊓ E :=
        ⟨U.mul_mem (U.inv_mem u'.2) u.2, h1 ▸ E.mul_mem e'.2 (E.inv_mem e.2)⟩
      rw [hUE, Subgroup.mem_bot] at hmem
      have hu : (u : S) = u' := by
        calc (u : S) = u' * ((u' : S)⁻¹ * u) := by group
          _ = u' := by rw [hmem, mul_one]
      have he : (e : S) = e' := by
        have := h0
        rw [hu] at this
        exact mul_left_cancel this
      exact Prod.ext (Subtype.ext hu) (Subtype.ext he)
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (U : Set S) * (E : Set S) := hset ▸ hx
      obtain ⟨u, hu, e, he, rfl⟩ := hx'
      exact ⟨(⟨u, hu⟩, ⟨e, he⟩), rfl⟩
  have hcard : Nat.card ↥(U ⊔ E) = Nat.card U * Nat.card E := by
    rw [← Nat.card_prod]
    exact (Nat.card_eq_of_bijective _ hbij).symm
  have hdvd : Nat.card U * Nat.card E ∣ Nat.card C :=
    hcard ▸ Subgroup.card_dvd_of_le (sup_le hUC hEC)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hU2
  have hE0 : Nat.card E ≠ 0 := Nat.card_pos.ne'
  have h3 := t2021Layer_twoPart_dvd hdvd Nat.card_pos.ne'
  rw [hk, t2021Layer_twoPart_pow_mul k hE0] at h3
  have h4 : 2 ^ k * twoPart (Nat.card E) ≤ 2 * twoPart (Nat.card E) :=
    (Nat.le_of_dvd (by unfold twoPart; positivity) h3).trans h2
  have hpos : 0 < twoPart (Nat.card E) := by unfold twoPart; positivity
  rw [hk]
  exact Nat.le_of_mul_le_mul_right h4 hpos

theorem t2021Layer_fix_of_card_le_two {S : Type} [Group S] [Finite S] {U : Subgroup S}
    (hU : Nat.card U ≤ 2) {φ : MulAut S} (hφ : ∀ u ∈ U, φ u ∈ U) : ∀ u ∈ U, φ u = u := by
  intro u hu
  by_contra hne
  have h1 : u ≠ 1 := by
    rintro rfl
    exact hne (map_one φ)
  have hφ1 : φ u ≠ 1 := by
    intro h
    apply h1
    have := congrArg φ.symm h
    simpa using this
  let f : Fin 3 → U := ![⟨1, U.one_mem⟩, ⟨u, hu⟩, ⟨φ u, hφ u hu⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hv : ((f i : U) : S) = f j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp [f] at hv ⊢ <;>
      first
        | exact absurd hv.symm h1
        | exact absurd hv h1
        | exact absurd hv.symm hφ1
        | exact absurd hv hφ1
        | exact absurd hv.symm hne
        | exact absurd hv hne
  have h3 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
  omega

theorem t2021Layer_range_elemAbelian {𝔅 X : Type} [Group 𝔅] [Group X] {p : ℕ} (ψ : 𝔅 →* X)
    (hexp : ∀ g : 𝔅, g ^ p = 1) (hcomm : ∀ g h : 𝔅, g * h = h * g) : IsElemAbelian p ψ.range := by
  refine ⟨⟨⟨?_⟩⟩, ?_⟩
  · rintro ⟨_, g, rfl⟩ ⟨_, h, rfl⟩
    exact Subtype.ext (by simp only [Subgroup.coe_mul]; rw [← map_mul, hcomm, map_mul])
  · rintro _ ⟨g, rfl⟩
    rw [← map_pow, hexp, map_one]

theorem t2021Layer_card_range {𝔅 X : Type} [Group 𝔅] [Finite 𝔅] [Group X] {p : ℕ} (ψ : 𝔅 →* X)
    (hrank : p ^ 3 * Nat.card {g : 𝔅 // ψ g = 1} ≤ Nat.card 𝔅) : p ^ 3 ≤ Nat.card ψ.range := by
  have hk : Nat.card {g : 𝔅 // ψ g = 1} = Nat.card ψ.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g => MonoidHom.mem_ker.symm)
  have h := Subgroup.card_ker_mul_card_range ψ
  rw [hk] at hrank
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  rw [← h, mul_comm (Nat.card ψ.ker)] at hrank
  exact Nat.le_of_mul_le_mul_right hrank hpos

section CoreOf

theorem t2021Layer_core_of {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {𝔅 : Type} [Group 𝔅] [Finite 𝔅] (ψS : 𝔅 →* MulAut (Q ⧸ Subgroup.center Q))
    (hcomm : ∀ g h : 𝔅, g * h = h * g) {a b₁ : 𝔅}
    (ha : GLAMarking Q fun lab _ _ I F θ => GLAPrimeField p lab I F (· = MulAut.congr θ (ψS a)))
    {T : Subgroup (Q ⧸ Subgroup.center Q)} (hT2 : IsPGroup 2 T)
    (hTinv : ∀ g : 𝔅, ∀ x ∈ T, ψS g x ∈ T)
    {t : Q ⧸ Subgroup.center Q} (ht : t ∈ T) (hta : ψS a t = t) (htb : ψS b₁ t ≠ t)
    {d : TauCeti.LieTypeIndex} {hd : d.Valid}
    (he : Nonempty ((Q ⧸ Subgroup.center Q) ≃* (TauCeti.CFSGIndex.lie ⟨d, hd⟩).Group))
    (hexc : ¬ KD264Lie.outerPLayerExc p d) (hnc : ¬ IsChevSimple p (Q ⧸ Subgroup.center Q))
    (hdvd : p ∣ Nat.card (Q ⧸ Subgroup.center Q)) :
    ∃ Kb Ub : Subgroup (Q ⧸ Subgroup.center Q),
      Kb ≤ fixSub (ψS a) ∧ (∀ c ∈ fixSub (ψS a), ∀ x ∈ Kb, c * x * c⁻¹ ∈ Kb) ∧
      (∀ g : 𝔅, ∀ x ∈ Kb, ψS g x ∈ Kb) ∧ IsSimpleGroup ↥Kb ∧ ¬ IsMulCommutative ↥Kb ∧
      p ∣ Nat.card ↥Kb ∧ Ub ≤ Kb ∧ IsPGroup 2 Ub ∧ Ub ≠ ⊥ ∧ ∀ g : 𝔅, ∀ u ∈ Ub, ψS g u ∈ Ub := by
  classical
  obtain ⟨hord, hnot⟩ := t2021Layer_not_mem hp hp2 ha
  have hαp : ψS a ^ p = 1 := hord ▸ pow_orderOf_eq_one _
  have hlay := KD264Lie.lieOuterPLayer_of_families (KD264Lie.lieOuterPLayer_linear p hp hp2)
      (KD264Lie.lieOuterPLayer_unitary p hp hp2) (KD264Lie.lieOuterPLayer_classicalBCD p hp hp2)
      (KD264Lie.lieOuterPLayer_triality p hp hp2) (KD264Lie.lieOuterPLayer_excUntwisted p hp hp2)
      (KD264Lie.lieOuterPLayer_excTwisted p hp hp2) d hd trivial hexc _ he hnc hdvd (ψS a) hαp hnot
  obtain ⟨J, hJ⟩ := FR.exists_component_of_ne_bot _ hlay
  have hJ' : GLAPComponent p (FP.fixSub (ψS a)) J := hJ
  have hJperf : ⁅J, J⁆ = J := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ'
  have hJ1 : J ≠ ⊥ := CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hJ'
  obtain ⟨E, hEC, hEs, hEna, hperf, h2, -⟩ := t2021Layer_coreSub hp hp2 ha ⟨J, hJ'.1, hJperf, hJ1⟩
  have hJE : J = E := FR.eq_core_of_glaPComponent hEs hEC hperf hJ'
  have hpE : p ∣ Nat.card E :=
    hJE ▸ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116pI_pcomp_card_dvd hp hJ'
  have hEperf : ⁅E, E⁆ = E := hJE ▸ hJperf
  have hfix : ∀ x, x ∈ FP.fixSub (ψS a) ↔ x ∈ fixSub (ψS a) := fun x => by
    rw [FP.mem_fixSub]
    rfl
  have hCinv : ∀ g : 𝔅, ∀ x ∈ FP.fixSub (ψS a), ψS g x ∈ FP.fixSub (ψS a) := by
    intro g x hx
    rw [FP.mem_fixSub] at hx ⊢
    rw [← MulAut.mul_apply, ← map_mul, hcomm, map_mul, MulAut.mul_apply, hx]
  have hEn : ∀ c ∈ FP.fixSub (ψS a), ∀ x ∈ E, c * x * c⁻¹ ∈ E := by
    intro c hc x hx
    have hle : E.map (MulAut.conj c).toMonoidHom ≤ E := by
      refine hperf _ ?_ (by rw [← Subgroup.map_commutator, hEperf])
      rintro _ ⟨y, hy, rfl⟩
      exact (FP.fixSub (ψS a)).mul_mem ((FP.fixSub (ψS a)).mul_mem hc (hEC hy))
        ((FP.fixSub (ψS a)).inv_mem hc)
    exact hle ⟨x, hx, rfl⟩
  have hEinv : ∀ g : 𝔅, ∀ x ∈ E, ψS g x ∈ E := by
    intro g x hx
    have hle : E.map (ψS g).toMonoidHom ≤ E := by
      refine hperf _ ?_ (by rw [← Subgroup.map_commutator, hEperf])
      rintro _ ⟨y, hy, rfl⟩
      exact hCinv g y (hEC hy)
    exact hle ⟨x, hx, rfl⟩
  refine ⟨E, (T ⊓ fixSub (ψS a)) ⊓ E, fun x hx => (hfix x).1 (hEC hx),
    fun c hc => hEn c ((hfix c).2 hc), hEinv, hEs, ?_, hpE, inf_le_right,
    hT2.to_le (inf_le_left.trans inf_le_left), ?_, ?_⟩
  · intro h
    obtain ⟨x, y, hxy⟩ := hEna
    exact hxy (h.is_comm.comm x y)
  · intro hUb
    have hUC : T ⊓ fixSub (ψS a) ≤ FP.fixSub (ψS a) := fun x hx => (hfix x).2 hx.2
    have hcard := t2021Layer_card_le_two hEC hUC hEn (hT2.to_le inf_le_left) hUb h2
    have hUinv : ∀ u ∈ T ⊓ fixSub (ψS a), ψS b₁ u ∈ T ⊓ fixSub (ψS a) := fun u hu =>
      ⟨hTinv b₁ u hu.1, (hfix _).1 (hCinv b₁ u ((hfix u).2 hu.2))⟩
    exact htb (t2021Layer_fix_of_card_le_two hcard hUinv t ⟨ht, hta⟩)
  · rintro g u ⟨⟨huT, huC⟩, huE⟩
    exact ⟨⟨hTinv g u huT, (hfix _).1 (hCinv g u ((hfix u).2 huC))⟩, hEinv g u huE⟩

end CoreOf

section Core

theorem t2021Layer_core {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {𝔅 : Type} [Group 𝔅] [Finite 𝔅] (ψS : 𝔅 →* MulAut (Q ⧸ Subgroup.center Q))
    (hexp : ∀ g : 𝔅, g ^ p = 1) (hcomm : ∀ g h : 𝔅, g * h = h * g)
    (hchev : IsChevSimple 2 (Q ⧸ Subgroup.center Q))
    (hD4 : ¬ (p = 3 ∧ catalogIs (Q ⧸ Subgroup.center Q)
      (onLie fun | .trialityD4 _ => True | _ => False)))
    (hrank : p ^ 3 * Nat.card {g : 𝔅 // ψS g = 1} ≤ Nat.card 𝔅) {a b₁ : 𝔅}
    (ha : GLAMarking Q fun lab _ _ I F θ => GLAPrimeField p lab I F (· = MulAut.congr θ (ψS a)))
    (hb : GLAMarking Q fun _ _ _ I _ θ => MulAut.congr θ (ψS b₁) ∈ I)
    {T : Subgroup (Q ⧸ Subgroup.center Q)} (hT2 : IsPGroup 2 T)
    (hTinv : ∀ g : 𝔅, ∀ x ∈ T, ψS g x ∈ T)
    {t : Q ⧸ Subgroup.center Q} (ht : t ∈ T) (hta : ψS a t = t) (htb : ψS b₁ t ≠ t) :
    ∃ Kb Ub : Subgroup (Q ⧸ Subgroup.center Q),
      Kb ≤ fixSub (ψS a) ∧ (∀ c ∈ fixSub (ψS a), ∀ x ∈ Kb, c * x * c⁻¹ ∈ Kb) ∧
      (∀ g : 𝔅, ∀ x ∈ Kb, ψS g x ∈ Kb) ∧ IsSimpleGroup ↥Kb ∧ ¬ IsMulCommutative ↥Kb ∧
      p ∣ Nat.card ↥Kb ∧ Ub ≤ Kb ∧ IsPGroup 2 Ub ∧ Ub ≠ ⊥ ∧ ∀ g : 𝔅, ∀ u ∈ Ub, ψS g u ∈ Ub := by
  obtain ⟨hord, hnot⟩ := t2021Layer_not_mem hp hp2 ha
  have hαp : ψS a ^ p = 1 := hord ▸ pow_orderOf_eq_one _
  have hαi : ψS a ∉ (MulAut.conj : (Q ⧸ Subgroup.center Q) →* MulAut (Q ⧸ Subgroup.center Q)).range :=
    fun h => hnot (CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _ h)
  have hE := t2021Layer_range_elemAbelian ψS hexp hcomm
  have hE3 := t2021Layer_card_range ψS hrank
  have hT1 : T ≠ ⊥ := by
    intro h
    apply htb
    rw [h, Subgroup.mem_bot] at ht
    rw [ht, map_one]
  obtain ⟨d, hd, -, he⟩ := t2021Layer_exists_index hp hp2 hαp hαi hchev
  have hexc : ¬ KD264Lie.outerPLayerExc p d := fun h =>
    t2021Layer_exc hp hp2 he h hD4 hE hE3 hT2 hT1 (by rintro _ ⟨g, rfl⟩ y hy; exact hTinv g y hy)
  have hL2 : ¬ (p = 3 ∧ catalogIs (Q ⧸ Subgroup.center Q) CFSG.LocalAnalysis.GLTheoremA.List93.l2Two) := by
    rintro ⟨rfl, hS⟩
    exact absurd hE3 (not_le.2 (CFSG.LocalAnalysis.GLTheoremA.List93.l2Two_holds _ hS ψS.range hE))
  have hnc := t2021Layer_not_chev hp hp2 hαp hαi hchev hL2
  have hb1 : ψS b₁ ≠ 1 := fun h => htb (by rw [h, MulAut.one_apply])
  have hdvd := t2021Layer_dvd_card hp hp2 (by rw [← map_pow, hexp, map_one]) hb1 hb
  exact t2021Layer_core_of hp hp2 ψS hcomm ha hT2 hTinv ht hta htb he hexc hnc hdvd

end Core

end CFSG.LocalAnalysis.GLTheoremA.T2021

end

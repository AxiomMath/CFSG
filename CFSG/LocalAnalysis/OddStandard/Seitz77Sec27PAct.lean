module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Cover
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Gen
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27Quot
public import CFSG.LocalAnalysis.OddStandard.Seitz77Levi
public import CFSG.LocalAnalysis.OddStandard.Seitz77PlaneASide
public import CFSG.LocalAnalysis.OddStandard.Seitz77WModule

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ComponentClassification.PSL3Four

theorem additive_cent_eq_scalar (g : F4V →+ F4V) (hU : ∀ γ v, g (cUp γ v) = cUp γ (g v))
    (hL : ∀ γ v, g (cLow γ v) = cLow γ (g v)) :
    ∃ c : F4, ∀ v, g v = ![c * v 0, c * v 1] := by
  have h1 : ∀ γ : F4, g ![γ, 1] = ![(g ![0, 1]) 0 + γ * (g ![0, 1]) 1, (g ![0, 1]) 1] := by
    intro γ
    have e : cUp γ ![0, 1] = ![γ, 1] := by simp [cUp]
    have h := hU γ ![0, 1]
    rw [e] at h
    exact h
  have h2 : ∀ γ : F4, g ![γ, 0] = ![γ * (g ![0, 1]) 1, 0] := by
    intro γ
    have e : (![γ, 0] : F4V) = ![γ, 1] - ![0, 1] := by
      ext i; fin_cases i <;> simp
    rw [e, map_sub, h1]
    ext i; fin_cases i <;> simp
  have h3 : ∀ γ : F4, g ![0, γ] = ![0, γ * (g ![0, 1]) 1] := by
    intro γ
    have e : (![0, γ] : F4V) = cLow γ ![1, 0] - ![1, 0] := by
      ext i; fin_cases i <;> simp [cLow]
    rw [e, map_sub, hL, h2 1]
    ext i; fin_cases i <;> simp [cLow]
  refine ⟨(g ![0, 1]) 1, fun v => ?_⟩
  have e : g v = g ![v 0, 0] + g ![0, v 1] := by
    rw [← map_add]
    congr 1
    ext i; fin_cases i <;> simp
  rw [e, h2 (v 0), h3 (v 1)]
  ext i; fin_cases i <;> simp [mul_comm]


namespace Levi

open CFSG.ComponentClassification.PSL3Four

theorem LeviData.toAdd_ne_zero {G : Type*} [Group G] {A R : Subgroup G} (L : LeviData A R)
    {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) : Multiplicative.toAdd (L.ι ⟨r, hr⟩) ≠ 0 := by
  intro h
  apply hr1
  have h1 : L.ι ⟨r, hr⟩ = 1 := Multiplicative.toAdd.injective (by simpa using h)
  have h2 : (⟨r, hr⟩ : ↥R) = 1 := L.ι.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem LeviData.mem_normalizer_of_actsAs {G : Type*} [Group G] {A R : Subgroup G}
    (L : LeviData A R) {x : G} {f : F4V → F4V} (hx : ActsAs L.ι x f) :
    x ∈ normalizer (R : Set G) := by
  have : Finite ↥R := Finite.of_equiv _ L.ι.symm.toEquiv
  exact Subgroup.mem_normalizer_fintype fun n hn => hx.conj_mem ⟨n, hn⟩

theorem LeviData.exists_conj_of_ne_one {G : Type*} [Group G] {A R : Subgroup G}
    (L : LeviData A R) {r s : G} (hr : r ∈ R) (hs : s ∈ R) (hr1 : r ≠ 1) (hs1 : s ≠ 1) :
    ∃ x : G, x ∈ A ∧ x ∈ normalizer (R : Set G) ∧ x * r * x⁻¹ = s := by
  obtain ⟨a, b, c, e, h⟩ :=
    WFacts.trans_words _ _ (LeviData.toAdd_ne_zero L hr hr1)
      (LeviData.toAdd_ne_zero L hs hs1)
  have hx : ActsAs L.ι (L.u a * L.l b * L.u c * L.l e)
      (fun v => cUp a (cLow b (cUp c (cLow e v)))) :=
    (((L.act_u a).comp (L.act_l b)).comp (L.act_u c)).comp (L.act_l e)
  refine ⟨L.u a * L.l b * L.u c * L.l e, ?_, LeviData.mem_normalizer_of_actsAs L hx, ?_⟩
  · exact A.mul_mem (A.mul_mem (A.mul_mem (L.u_mem a) (L.l_mem b)) (L.u_mem c)) (L.l_mem e)
  · obtain ⟨hmem, h1⟩ := hx ⟨r, hr⟩
    have h1' : L.ι ⟨L.u a * L.l b * L.u c * L.l e * r * (L.u a * L.l b * L.u c * L.l e)⁻¹, hmem⟩ =
        Multiplicative.ofAdd (cUp a (cLow b (cUp c (cLow e
          (Multiplicative.toAdd (L.ι ⟨r, hr⟩)))))) := h1
    have h2 : L.ι ⟨L.u a * L.l b * L.u c * L.l e * r * (L.u a * L.l b * L.u c * L.l e)⁻¹, hmem⟩ =
        L.ι ⟨s, hs⟩ := by
      rw [h1', h]
      exact ofAdd_toAdd _
    exact congrArg Subtype.val (L.ι.injective h2)

theorem LeviData.cent_cube {G : Type*} [Group G] {A R : Subgroup G} (L : LeviData A R)
    (g : MulAut ↥R)
    (hu : ∀ (γ : F4) (w : ↥R), g ⟨L.u γ * w * (L.u γ)⁻¹, (L.act_u γ).conj_mem w⟩ =
      ⟨L.u γ * (g w) * (L.u γ)⁻¹, (L.act_u γ).conj_mem (g w)⟩)
    (hl : ∀ (γ : F4) (w : ↥R), g ⟨L.l γ * w * (L.l γ)⁻¹, (L.act_l γ).conj_mem w⟩ =
      ⟨L.l γ * (g w) * (L.l γ)⁻¹, (L.act_l γ).conj_mem (g w)⟩) :
    g ^ 3 = 1 := by
  obtain ⟨g', hg'⟩ : ∃ g' : F4V →+ F4V, ∀ v, g' v =
      Multiplicative.toAdd (L.ι (g (L.ι.symm (Multiplicative.ofAdd v)))) :=
    ⟨{ toFun := fun v => Multiplicative.toAdd (L.ι (g (L.ι.symm (Multiplicative.ofAdd v))))
       map_zero' := by simp
       map_add' := fun v w => by simp [ofAdd_add] }, fun v => rfl⟩
  have key : ∀ w : ↥R,
      L.ι (g w) = Multiplicative.ofAdd (g' (Multiplicative.toAdd (L.ι w))) := by
    intro w
    rw [hg']
    simp
  have hU : ∀ γ v, g' (cUp γ v) = cUp γ (g' v) := by
    intro γ v
    obtain ⟨w, rfl⟩ : ∃ w : ↥R, Multiplicative.toAdd (L.ι w) = v :=
      ⟨L.ι.symm (Multiplicative.ofAdd v), by simp⟩
    obtain ⟨hmem, h1⟩ := L.act_u γ w
    obtain ⟨hmem', h2⟩ := L.act_u γ (g w)
    have h3 := key ⟨L.u γ * (w : G) * (L.u γ)⁻¹, hmem⟩
    rw [hu γ w, h2, h1] at h3
    rw [key w] at h3
    simpa [cUp] using h3.symm
  have hL : ∀ γ v, g' (cLow γ v) = cLow γ (g' v) := by
    intro γ v
    obtain ⟨w, rfl⟩ : ∃ w : ↥R, Multiplicative.toAdd (L.ι w) = v :=
      ⟨L.ι.symm (Multiplicative.ofAdd v), by simp⟩
    obtain ⟨hmem, h1⟩ := L.act_l γ w
    obtain ⟨hmem', h2⟩ := L.act_l γ (g w)
    have h3 := key ⟨L.l γ * (w : G) * (L.l γ)⁻¹, hmem⟩
    rw [hl γ w, h2, h1] at h3
    rw [key w] at h3
    simpa [cLow] using h3.symm
  obtain ⟨c, hc⟩ := additive_cent_eq_scalar g' hU hL
  have hinj : Function.Injective g' := by
    intro v w h
    rw [hg' v, hg' w] at h
    exact Multiplicative.ofAdd.injective
      (L.ι.symm.injective (g.injective (L.ι.injective (Multiplicative.toAdd.injective h))))
  have hc0 : c ≠ 0 := by
    intro h0
    have e1 : g' ![1, 0] = 0 := by
      rw [hc]
      ext i
      fin_cases i <;> simp [h0]
    have e2 : g' ![1, 0] = g' 0 := by rw [e1, map_zero]
    have := congrFun (hinj e2) 0
    simp at this
  have hc3 : c * c * c = 1 := by
    have h := congrArg Units.val (pow_three_eq_one (Units.mk0 c hc0))
    simpa [pow_three'] using h
  have hg'3 : ∀ v, g' (g' (g' v)) = v := by
    intro v
    simp only [hc]
    ext i
    fin_cases i
    · simp
      linear_combination (v 0) * hc3
    · simp
      linear_combination (v 1) * hc3
  have h3 : ∀ w : ↥R, g (g (g w)) = w := by
    intro w
    apply L.ι.injective
    rw [key (g (g w)), key (g w), key w]
    simp only [toAdd_ofAdd, hg'3, ofAdd_toAdd]
  rw [pow_three']
  exact MulEquiv.ext fun w => h3 w

end Levi

open scoped commutatorElement

@[expose] noncomputable def conjAct27 {G : Type*} [Group G] (R P : Subgroup G)
    (h : P ≤ normalizer (R : Set G)) : ↥P →* MulAut ↥R :=
  R.normalizerMonoidHom.comp (Subgroup.inclusion h)

theorem coe_conjAct27 {G : Type*} [Group G] {R P : Subgroup G} (h : P ≤ normalizer (R : Set G))
    (p : ↥P) (w : ↥R) : ((conjAct27 R P h p w : ↥R) : G) = (p : G) * (w : G) * (p : G)⁻¹ :=
  rfl

structure PStruct27 {G : Type} [Group G] [Finite G] (A R P : Subgroup G) : Prop where
  perfect : ⁅P, P⁆ = P
  le_A : P ≤ A
  le_norm : P ≤ normalizer (R : Set G)
  char : ∀ c ∈ normalizer (A : Set G) ⊓ normalizer (R : Set G), ∀ p ∈ P, c * p * c⁻¹ ∈ P
  simple : IsSimpleGroup ↥(conjAct27 R P le_norm).range
  card : Nat.card ↥(conjAct27 R P le_norm).range = 60
  trans : ∀ r ∈ R, ∀ s ∈ R, r ≠ 1 → s ≠ 1 → ∃ p ∈ P, p * r * p⁻¹ = s
  cent : ∀ g : MulAut ↥R, (∀ p : ↥P, g * conjAct27 R P le_norm p = conjAct27 R P le_norm p * g) →
    g ^ 3 = 1

theorem s27_nat_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem s27_commutator_eq_top_of_equiv_alt5 {S : Type*} [Group S]
    (e : S ≃* alternatingGroup (Fin 5)) : commutator S = ⊤ := by
  have h5 : commutator (alternatingGroup (Fin 5)) = ⊤ :=
    commutator_alternatingGroup_eq_top (by simp)
  have h1 : (commutator S).map e.toMonoidHom = commutator (alternatingGroup (Fin 5)) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  rw [h5] at h1
  exact Subgroup.map_injective e.injective
    (h1.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm)

theorem exists_pstruct27_of_hom {G : Type} [Group G] [Finite G] {A R : Subgroup G}
    (L : Levi.LeviData A R) {K : Type*} [Group K] (eK : K ≃* alternatingGroup (Fin 5))
    (Λ : ↥(A ⊓ normalizer (R : Set G)) →* K) (hΛs : Function.Surjective Λ)
    (hΛk : ∀ a : ↥(A ⊓ normalizer (R : Set G)), Λ a = 1 ↔ (a : G) ∈ centralizer (R : Set G)) :
    ∃ P : Subgroup G, PStruct27 A R P := by
  revert Λ
  generalize hN : A ⊓ normalizer (R : Set G) = NAR
  intro Λ hΛs hΛk
  have hNmem : ∀ x : G, x ∈ NAR ↔ x ∈ A ∧ x ∈ normalizer (R : Set G) := fun x => by
    rw [← hN]
    exact mem_inf
  have hNARn : NAR ≤ normalizer (R : Set G) := fun x hx => ((hNmem x).mp hx).2
  have hNARA : NAR ≤ A := fun x hx => ((hNmem x).mp hx).1
  set ρ : ↥NAR →* MulAut ↥R := conjAct27 R NAR hNARn with hρ
  have hρk : ∀ a : ↥NAR, ρ a = 1 ↔ (a : G) ∈ centralizer (R : Set G) := by
    intro a
    have : ρ a = R.normalizerMonoidHom ⟨a, hNARn a.2⟩ := rfl
    rw [this, ← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
  have hker : ρ.ker = Λ.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hρk, hΛk]
  obtain ⟨e₁⟩ := rangeEquiv_of_ker_eq ρ Λ hker
  have e₂ : Λ.range ≃* K :=
    (MulEquiv.subgroupCongr (MonoidHom.range_eq_top.mpr hΛs)).trans Subgroup.topEquiv
  let eS : ↥ρ.range ≃* alternatingGroup (Fin 5) := e₁.trans (e₂.trans eK)
  have hsimple : IsSimpleGroup ↥ρ.range := eS.isSimpleGroup
  have hcard : Nat.card ↥ρ.range = 60 := (Nat.card_congr eS.toEquiv).trans s27_nat_card_alt5
  have hperf : commutator ↥ρ.range = ⊤ := s27_commutator_eq_top_of_equiv_alt5 eS
  obtain ⟨P₀, hP₀perf, hP₀map, hP₀char⟩ :=
    exists_perfect_residual ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ) hperf
  set P : Subgroup G := P₀.map NAR.subtype with hP
  have hPNAR : P ≤ NAR := Subgroup.map_subtype_le _
  have hPn : P ≤ normalizer (R : Set G) := hPNAR.trans hNARn
  have hmemP : ∀ x : G, x ∈ P ↔ ∃ q : ↥NAR, q ∈ P₀ ∧ (q : G) = x := by
    intro x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
  have hrange : (conjAct27 R P hPn).range = ρ.range := by
    ext g
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨q, -, hq⟩ := (hmemP p).mp p.2
      exact ⟨q, by
        have : conjAct27 R P hPn p = ρ q := by
          ext w
          simp only [coe_conjAct27, hρ, ← hq]
        exact this.symm⟩
    · rintro ⟨a, rfl⟩
      have : (⟨ρ a, a, rfl⟩ : ↥ρ.range) ∈ P₀.map ρ.rangeRestrict := by
        rw [hP₀map]
        trivial
      obtain ⟨q, hq, hqa⟩ := this
      refine ⟨⟨q.1, (hmemP _).mpr ⟨q, hq, rfl⟩⟩, ?_⟩
      have hqa' : ρ q = ρ a := congrArg Subtype.val hqa
      rw [← hqa']
      ext w
      simp [coe_conjAct27, hρ]
  have eP : ↥(conjAct27 R P hPn).range ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hrange).trans eS
  refine ⟨P, ⟨?_, hPNAR.trans hNARA, hPn, ?_, eP.isSimpleGroup, ?_, ?_, ?_⟩⟩
  ·
    rw [← Subgroup.map_commutator, hP₀perf]
  ·
    rintro c ⟨hcA, hcR⟩ p hp
    obtain ⟨q, hq, rfl⟩ := (hmemP p).mp hp
    have hmem : ∀ a : ↥NAR, c * (a : G) * c⁻¹ ∈ NAR := fun a =>
      (hNmem _).mpr ⟨(mem_normalizer_iff.mp hcA a).mp (hNARA a.2),
        mul_mem (mul_mem hcR (hNARn a.2)) (inv_mem hcR)⟩
    have hmem' : ∀ a : ↥NAR, c⁻¹ * (a : G) * c ∈ NAR := fun a =>
      (hNmem _).mpr ⟨(mem_normalizer_iff''.mp hcA a).mp (hNARA a.2),
        mul_mem (mul_mem (inv_mem hcR) (hNARn a.2)) hcR⟩
    let f : ↥NAR ≃* ↥NAR :=
      { toFun := fun a => ⟨c * a * c⁻¹, hmem a⟩
        invFun := fun a => ⟨c⁻¹ * a * c, hmem' a⟩
        left_inv := fun a => Subtype.ext (by simp [mul_assoc])
        right_inv := fun a => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hf : f q ∈ P₀ := by
      rw [← hP₀char f]
      exact ⟨q, hq, rfl⟩
    exact (hmemP _).mpr ⟨f q, hf, rfl⟩
  ·
    exact (Nat.card_congr eP.toEquiv).trans s27_nat_card_alt5
  ·
    intro r hr s hs hr1 hs1
    obtain ⟨x, hxA, hxN, hx⟩ := L.exists_conj_of_ne_one hr hs hr1 hs1
    have : ρ ⟨x, (hNmem x).mpr ⟨hxA, hxN⟩⟩ ∈ (conjAct27 R P hPn).range := by
      rw [hrange]
      exact ⟨_, rfl⟩
    obtain ⟨p, hp⟩ := this
    refine ⟨p, p.2, ?_⟩
    have := congrArg (fun g : MulAut ↥R => ((g ⟨r, hr⟩ : ↥R) : G)) hp
    simp only [coe_conjAct27, hρ] at this
    rw [this]
    exact hx
  ·
    intro g hg
    refine L.cent_cube g (fun γ w => ?_) (fun γ w => ?_)
    · have hu : ρ ⟨L.u γ, (hNmem (L.u γ)).mpr
            ⟨L.u_mem γ, L.mem_normalizer_of_actsAs (L.act_u γ)⟩⟩ ∈
          (conjAct27 R P hPn).range := by
        rw [hrange]
        exact ⟨_, rfl⟩
      obtain ⟨p, hp⟩ := hu
      have h1 := congrArg (fun m : MulAut ↥R => m w) (hg p)
      simp only [MulAut.mul_apply, hp] at h1
      exact h1
    · have hl : ρ ⟨L.l γ, (hNmem (L.l γ)).mpr
            ⟨L.l_mem γ, L.mem_normalizer_of_actsAs (L.act_l γ)⟩⟩ ∈
          (conjAct27 R P hPn).range := by
        rw [hrange]
        exact ⟨_, rfl⟩
      obtain ⟨p, hp⟩ := hl
      have h1 := congrArg (fun m : MulAut ↥R => m w) (hg p)
      simp only [MulAut.mul_apply, hp] at h1
      exact h1

theorem Hyp.exists_pstruct27
    {G : Type} [Group G] [Finite G] {A V₁ V₂ W : Subgroup G} (h : Hyp G A) (d : Datum A)
    (hR : Radicals d.V V₁ V₂) (hW : W = V₁ ∨ W = V₂) :
    ∃ P : Subgroup G, PStruct27 A W P := by
  obtain ⟨hWV, hWe, hW16⟩ := hR.property hW
  have hWA : W ≤ A := hWV.trans d.V_isSylow.le
  obtain ⟨L⟩ := h.exists_leviData d hR hW
  obtain ⟨c, φ, i, hφs, hφk, hmap, -⟩ := exists_cover_data h.standard.1
    (CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h.model) h.odd
    d.V_isSylow hWV hWe hW16
  obtain ⟨Λ, hΛs, hΛk⟩ := exists_levi_hom hWA hWe c.card_k i φ hφs hφk.le
    (by rw [hφk]; exact h.odd) hmap
  obtain ⟨e⟩ := sl2_mulEquiv_alt5 c.k c.card_k
  exact exists_pstruct27_of_hom L e Λ hΛs hΛk

end CFSG.OddStandard.Seitz77

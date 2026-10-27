module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T156GDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bTools
public import CFSG.LocalAnalysis.GLTheoremA.S10.CaseGamma
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagInputs
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPCanon
public import CFSG.LocalAnalysis.GLTheoremA.CatA.OutCycCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bDesc
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03KD264
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQ
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T156

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.S3
open scoped commutatorElement

theorem ggFixDer_congr {X R : Type} [Group X] [Group R] (θ : X ≃* R) (β : MulAut X) :
    ggFixDer (MulAut.congr θ β) = (ggFixDer β).map θ.toMonoidHom := by
  have hsub : ggFixSub (MulAut.congr θ β) = (ggFixSub β).map θ.toMonoidHom := by
    ext y
    rw [mem_ggFixSub, Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨θ.symm y, ?_, by simp⟩
      rw [mem_ggFixSub]
      have h1 : θ (β (θ.symm y)) = y := by simpa [MulAut.congr_apply] using hy
      calc β (θ.symm y) = θ.symm (θ (β (θ.symm y))) := by simp
        _ = θ.symm y := by rw [h1]
    · rintro ⟨z, hz, rfl⟩
      rw [mem_ggFixSub] at hz
      simp [MulAut.congr_apply, hz]
  unfold ggFixDer
  rw [hsub, Subgroup.map_commutator]

theorem commutator_eq_self_of_simple {T : Type*} [Group T] {E : Subgroup T} (hE : IsSimpleGroup ↥E)
    (hna : ∃ x y : ↥E, x * y ≠ y * x) : ⁅E, E⁆ = E := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥E) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hna
    apply hxy
    have hc : ⁅x, y⁆ ∈ commutator ↥E :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · rw [← Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem center_eq_bot_of_simple' {E : Type*} [Group E] [IsSimpleGroup E] (hna : ∃ x y : E, x * y ≠ y * x) :
    Subgroup.center E = ⊥ := by
  obtain ⟨x, y, h⟩ := hna
  exact FR.center_eq_bot_of_simple_nonab h

theorem map_center_le_center_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) : (Subgroup.center A).map f ≤ Subgroup.center B := by
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz x)]

section Kernel

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem ker_chevQuotHom_le_center {p : ℕ} {S : Subgroup Ω} (hcore : GLAPPrimeCore p ↥S = ⊥) :
    (chevQuotHom p S).ker ≤ Subgroup.center ↥S := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro s
  have hx' : pQuotHom p S x ∈ Subgroup.center (PQuot p S) := by
    rw [MonoidHom.mem_ker] at hx
    have h : (QuotientGroup.mk' (Subgroup.center (PQuot p S))) (pQuotHom p S x) = 1 := hx
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hc : pQuotHom p S (s * x * s⁻¹ * x⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      Subgroup.mem_center_iff.1 hx' (pQuotHom p S s)]
    group
  have hk : s * x * s⁻¹ * x⁻¹ ∈ (pQuotHom p S).ker := hc
  rw [ker_pQuotHom, hcore, Subgroup.mem_bot] at hk
  calc s * x = s * x * s⁻¹ * x⁻¹ * x * s := by group
    _ = x * s := by rw [hk]; group

end Kernel

theorem commutatorElement_mul_central_left {G : Type*} [Group G] {g h z : G}
    (hz : z ∈ Subgroup.center G) : ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hzh : z * h = h * z := (Subgroup.mem_center_iff.1 hz h).symm
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * z * h * (z⁻¹ * g⁻¹) * h⁻¹ = g * (z * h) * z⁻¹ * g⁻¹ * h⁻¹ := by group
    _ = g * (h * z) * z⁻¹ * g⁻¹ * h⁻¹ := by rw [hzh]
    _ = g * h * g⁻¹ * h⁻¹ := by group

theorem commutatorElement_mul_central_right {G : Type*} [Group G] {g h z : G}
    (hz : z ∈ Subgroup.center G) : ⁅g, h * z⁆ = ⁅g, h⁆ := by
  have hzg : ∀ x : G, x * z = z * x := fun x => Subgroup.mem_center_iff.1 hz x
  simp only [commutatorElement_def, mul_inv_rev]
  calc g * (h * z) * g⁻¹ * (z⁻¹ * h⁻¹) = g * h * (z * g⁻¹) * z⁻¹ * h⁻¹ := by group
    _ = g * h * (g⁻¹ * z) * z⁻¹ * h⁻¹ := by rw [hzg g⁻¹]
    _ = g * h * g⁻¹ * h⁻¹ := by group

section Component

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem exists_pComponent_of_simple {p : ℕ} (hp : p.Prime) {S : Subgroup Ω}
    (hcore : GLAPPrimeCore p ↥S = ⊥) {b : Ω}
    {E : Subgroup (PSimple p S)} (hE : IsSimpleGroup ↥E) (hna : ∃ x y : ↥E, x * y ≠ y * x)
    (hpE : p ∣ Nat.card ↥E)
    (hED : E ≤ ((S ⊓ Subgroup.centralizer ({b} : Set Ω)).subgroupOf S).map (chevQuotHom p S))
    (hEn : ∀ y ∈ ((S ⊓ Subgroup.centralizer ({b} : Set Ω)).subgroupOf S).map (chevQuotHom p S),
      ∀ e ∈ E, y * e * y⁻¹ ∈ E) :
    ∃ J : Subgroup Ω, GLAPComponent p (S ⊓ Subgroup.centralizer ({b} : Set Ω)) J ∧
      chevTransfer p S J = E := by
  classical
  set X : Subgroup Ω := S ⊓ Subgroup.centralizer ({b} : Set Ω) with hX
  set π := chevQuotHom p S with hπ
  set XS : Subgroup ↥S := X.subgroupOf S with hXS
  set Ehat : Subgroup ↥S := XS ⊓ E.comap π with hEhat
  set JS : Subgroup ↥S := ⁅Ehat, Ehat⁆ with hJS
  have hXle : X ≤ S := inf_le_left
  have hEmap : Ehat.map π = E := by
    apply le_antisymm
    · exact (Subgroup.map_mono inf_le_right).trans (Subgroup.map_comap_le _ _)
    · intro e he
      obtain ⟨x, hx, hxe⟩ := hED he
      exact ⟨x, ⟨hx, show π x ∈ E by rw [hxe]; exact he⟩, hxe⟩
  have hperf : ⁅E, E⁆ = E := commutator_eq_self_of_simple hE hna
  have hJmap : JS.map π = E := by
    rw [hJS, Subgroup.map_commutator, hEmap, hperf]
  have hker := ker_chevQuotHom_le_center hcore
  have hdecomp : ∀ e ∈ Ehat, ∃ j ∈ JS, j⁻¹ * e ∈ Subgroup.center ↥S := by
    intro e he
    have h1 : π e ∈ JS.map π := by
      rw [hJmap]
      exact he.2
    obtain ⟨j, hj, hje⟩ := h1
    refine ⟨j, hj, hker ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hje, inv_mul_cancel]
  have hEhatcomm : ⁅Ehat, Ehat⁆ ≤ Ehat := Subgroup.commutator_le.2 fun g hg h hh =>
    Ehat.mul_mem (Ehat.mul_mem (Ehat.mul_mem hg hh) (Ehat.inv_mem hg)) (Ehat.inv_mem hh)
  have hJE : JS ≤ Ehat := hEhatcomm
  have hJperf : ⁅JS, JS⁆ = JS := by
    apply le_antisymm
    · exact Subgroup.commutator_le.2 fun g hg h hh =>
        JS.mul_mem (JS.mul_mem (JS.mul_mem hg hh) (JS.inv_mem hg)) (JS.inv_mem hh)
    · refine Subgroup.commutator_le.2 fun e₁ he₁ e₂ he₂ => ?_
      obtain ⟨j₁, hj₁, hz₁⟩ := hdecomp e₁ he₁
      obtain ⟨j₂, hj₂, hz₂⟩ := hdecomp e₂ he₂
      have he₁' : e₁ = j₁ * (j₁⁻¹ * e₁) := by group
      have he₂' : e₂ = j₂ * (j₂⁻¹ * e₂) := by group
      have hc : ⁅e₁, e₂⁆ = ⁅j₁, j₂⁆ := by
        rw [he₁', he₂', commutatorElement_mul_central_left hz₁,
          commutatorElement_mul_central_right hz₂]
      rw [hc]
      exact Subgroup.commutator_mem_commutator hj₁ hj₂
  have hEhatN : ∀ x ∈ XS, ∀ e ∈ Ehat, x * e * x⁻¹ ∈ Ehat := by
    intro x hx e he
    refine ⟨XS.mul_mem (XS.mul_mem hx he.1) (XS.inv_mem hx), ?_⟩
    show π (x * e * x⁻¹) ∈ E
    rw [map_mul, map_mul, map_inv]
    exact hEn (π x) ⟨x, hx, rfl⟩ (π e) he.2
  have hJN : ∀ x ∈ XS, ∀ j ∈ JS, x * j * x⁻¹ ∈ JS := by
    intro x hx j hj
    have hmap : Ehat.map (MulAut.conj x).toMonoidHom ≤ Ehat := by
      rintro _ ⟨e, he, rfl⟩
      exact hEhatN x hx e he
    have hJmap' : JS.map (MulAut.conj x).toMonoidHom ≤ JS := by
      rw [hJS, Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact hJmap' ⟨j, hj, by simp [MulAut.conj_apply]⟩
  set J : Subgroup Ω := JS.map S.subtype with hJdef
  have hJX : J ≤ X := by
    rintro _ ⟨j, hj, rfl⟩
    exact (hJE hj).1
  have hXN : X ≤ Subgroup.normalizer (J : Set Ω) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hxS : x ∈ S := hXle hx
    have hxXS : (⟨x, hxS⟩ : ↥S) ∈ XS := by
      rw [hXS, Subgroup.mem_subgroupOf]
      exact hx
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, hJN _ hxXS j hj, by simp⟩
    · rintro ⟨j, hj, hjy⟩
      have hx' : (⟨x, hxS⟩ : ↥S)⁻¹ ∈ XS := XS.inv_mem hxXS
      have h1 := hJN _ hx' j hj
      refine ⟨_, h1, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hjy ⊢
      rw [hjy]
      group
  have hsub : CFSG.Open.IsSubnormal J X :=
    CFSG.Open.IsSubnormal.step hJX ((Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 hXN)
      (CFSG.Open.IsSubnormal.refl X)
  let ρ0 : ↥JS →* PSimple p S := π.comp JS.subtype
  have hρ0 : ∀ j : ↥JS, ρ0 j ∈ E := fun j => by
    rw [← hJmap]
    exact ⟨j, j.2, rfl⟩
  let ρ : ↥JS →* ↥E := ρ0.codRestrict E hρ0
  have hρs : Function.Surjective ρ := by
    rintro ⟨e, he⟩
    rw [← hJmap] at he
    obtain ⟨j, hj, rfl⟩ := he
    exact ⟨⟨j, hj⟩, rfl⟩
  have hZE : Subgroup.center ↥E = ⊥ := by
    haveI := hE
    exact center_eq_bot_of_simple' hna
  have hkerZ : ρ.ker = Subgroup.center ↥JS := by
    apply le_antisymm
    · intro j hj
      rw [Subgroup.mem_center_iff]
      intro k
      have hj1 : π (j : ↥S) = 1 := by
        have := congrArg Subtype.val ((MonoidHom.mem_ker).1 hj)
        simpa [ρ, ρ0] using this
      have hjc : (j : ↥S) ∈ Subgroup.center ↥S := hker ((MonoidHom.mem_ker).2 hj1)
      exact Subtype.ext ((Subgroup.mem_center_iff.1 hjc (k : ↥S)))
    · intro z hz
      have h1 : ρ z ∈ Subgroup.center ↥E :=
        map_center_le_center_of_surjective ρ hρs ⟨z, hz, rfl⟩
      rw [hZE, Subgroup.mem_bot] at h1
      exact h1
  have eQ : ↥JS ⧸ Subgroup.center ↥JS ≃* ↥E :=
    (QuotientGroup.quotientMulEquivOfEq hkerZ).symm.trans (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)
  have hJSq : CFSG.Open.IsQuasisimple ↥JS := by
    refine ⟨?_, ?_⟩
    · apply Subgroup.map_injective JS.subtype_injective
      rw [Subgroup.map_subtype_commutator, hJperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    · haveI := hE
      exact (MulEquiv.isSimpleGroup_congr eQ).2 inferInstance
  have eJ : ↥JS ≃* ↥J := Subgroup.equivMapOfInjective JS S.subtype S.subtype_injective
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eJ hJSq
  have eJQ : ↥J ⧸ Subgroup.center ↥J ≃* ↥E :=
    (QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥JS) eJ.symm
      (Subgroup.map_center_eq eJ.symm)).trans eQ
  have hdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rw [Nat.card_congr eJQ.toEquiv]
    exact hpE
  refine ⟨J, S10.glaPComponent_of_quasisimple hp hsub hJq hdvd, ?_⟩
  rw [chevTransfer, hJdef, ← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  exact hJmap

theorem exists_pSimple_equiv {p : ℕ} (hp : p.Prime) {S X J : Subgroup Ω} (hJ : GLAPComponent p X J)
    (hXS : X ≤ S) {E : Subgroup (PSimple p S)} (hE : IsSimpleGroup ↥E)
    (hna : ∃ x y : ↥E, x * y ≠ y * x) (hpE : p ∣ Nat.card ↥E) (hT : chevTransfer p S J = E) :
    ∃ Θ : PSimple p J ≃* ↥E, ∀ j : ↥J,
      ((Θ (QuotientGroup.mk (QuotientGroup.mk j : PQuot p J)) : ↥E) : PSimple p S) =
        chevQuotHom p S ⟨(j : Ω), hXS (hJ.1 j.2)⟩ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hJS : J ≤ S := hJ.1.trans hXS
  let ρ0 : ↥J →* PSimple p S := (chevQuotHom p S).comp (Subgroup.inclusion hJS)
  have hρ0 : ∀ j : ↥J, ρ0 j ∈ E := fun j => by
    rw [← hT]
    exact ⟨Subgroup.inclusion hJS j, Subgroup.mem_subgroupOf.2 j.2, rfl⟩
  let ρ : ↥J →* ↥E := ρ0.codRestrict E hρ0
  have hρs : Function.Surjective ρ := by
    rintro ⟨e, he⟩
    rw [← hT] at he
    obtain ⟨s, hs, rfl⟩ := he
    exact ⟨⟨s, Subgroup.mem_subgroupOf.1 hs⟩, rfl⟩
  have hO : GLAPPrimeCore p ↥J ≤ ρ.ker := by
    haveI : (GLAPPrimeCore p ↥J).Normal := GLAPPrimeCore.normal p ↥J
    haveI : ((GLAPPrimeCore p ↥J).map ρ).Normal := Subgroup.Normal.map inferInstance ρ hρs
    haveI := hE
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((GLAPPrimeCore p ↥J).map ρ) with h | h
    · exact (Subgroup.map_eq_bot_iff _).1 h
    · exfalso
      have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥J)) := CFSG.pPrimeCore_coprime_card
      have h1 : Nat.card ↥((GLAPPrimeCore p ↥J).map ρ) ∣ Nat.card (GLAPPrimeCore p ↥J) :=
        Subgroup.card_map_dvd _ _
      rw [h, Subgroup.card_top] at h1
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop (hpE.trans h1)
  let ρ₁ : PQuot p J →* ↥E := QuotientGroup.lift (GLAPPrimeCore p ↥J) ρ hO
  have hρ₁s : Function.Surjective ρ₁ := by
    intro e
    obtain ⟨j, rfl⟩ := hρs e
    exact ⟨QuotientGroup.mk j, rfl⟩
  have hZE : Subgroup.center ↥E = ⊥ := by
    haveI := hE
    exact center_eq_bot_of_simple' hna
  have hZ : Subgroup.center (PQuot p J) ≤ ρ₁.ker := by
    intro z hz
    have h1 : ρ₁ z ∈ Subgroup.center ↥E := map_center_le_center_of_surjective ρ₁ hρ₁s ⟨z, hz, rfl⟩
    rw [hZE, Subgroup.mem_bot] at h1
    exact h1
  let ρ₂ : PSimple p J →* ↥E := QuotientGroup.lift (Subgroup.center (PQuot p J)) ρ₁ hZ
  have hρ₂s : Function.Surjective ρ₂ := by
    intro e
    obtain ⟨q, rfl⟩ := hρ₁s e
    exact ⟨QuotientGroup.mk q, rfl⟩
  have hρ₂i : Function.Injective ρ₂ := by
    obtain ⟨hsimp, -⟩ := chev_pSimple_simple_nonabelian hp hJ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ₂.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff ρ₂).1 h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hna
      apply hxy
      obtain ⟨x', rfl⟩ := hρ₂s x
      obtain ⟨y', rfl⟩ := hρ₂s y
      have hx' : x' ∈ ρ₂.ker := h ▸ Subgroup.mem_top x'
      have hy' : y' ∈ ρ₂.ker := h ▸ Subgroup.mem_top y'
      rw [MonoidHom.mem_ker] at hx' hy'
      rw [hx', hy']
  refine ⟨MulEquiv.ofBijective ρ₂ ⟨hρ₂i, hρ₂s⟩, fun j => rfl⟩

end Component

@[expose] def InnRank (p : ℕ) : LargeEvenRawCont := fun R _ I _ =>
  Finite R → ∀ E : Subgroup (MulAut R), IsElemAbelian p E → (∀ φ ∈ E, φ ∈ I) → p < Nat.card E →
    ∃ φ ∈ E, φ ≠ 1 ∧ φ ∈ (MulAut.conj : R →* MulAut R).range

theorem exists_ne_one_of_one_lt_card {G : Type*} [Group G] {E : Subgroup G} (h : 1 < Nat.card E) :
    ∃ φ ∈ E, φ ≠ 1 := by
  by_contra hc
  push Not at hc
  have hE : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hc
  rw [hE, Subgroup.card_bot] at h
  exact lt_irrefl 1 h

theorem innRank_of_outdiagCyclic {p : ℕ} (hp : 0 < p) {R : Type} [Group R] {I F : Set (MulAut R)}
    (h : GGOutdiagCyclic R I) : InnRank p R I F := by
  intro hRf E hE hEI hcard
  haveI := hRf
  haveI : Finite (MulAut R) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨φ₀, hφ₀⟩ := h
  set N := (MulAut.conj : R →* MulAut R).range with hN
  let f : ↥E →* MulAut R ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hx : ∀ a : ↥E, f a ∈ Subgroup.zpowers (QuotientGroup.mk' N φ₀) := fun a =>
    map_sup_zpowers_le N φ₀ ⟨a, hφ₀ (hEI a a.2), rfl⟩
  have hexp : ∀ a : ↥E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hE.2 a a.2)
  have h1 := OutCyc.card_le_mul_card_ker_of_cyclic f _ hx hp hexp
  have h2 : 1 < Nat.card f.ker := by
    by_contra h3
    push Not at h3
    have : Nat.card ↥E ≤ p := by nlinarith
    omega
  obtain ⟨a, ha, ha1⟩ := exists_ne_one_of_one_lt_card h2
  refine ⟨a, a.2, fun h' => ha1 (Subtype.ext h'), ?_⟩
  have h4 : QuotientGroup.mk' N (a : MulAut R) = 1 := ha
  exact (QuotientGroup.eq_one_iff _).1 h4


theorem cAll_innRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) : MI.CAll lab (LargeEvenSimpleGuard (InnRank p)) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  by_cases hd : MI.DerivedLab lab
  · refine FP.canonAll_derived hlab hd ?_ ?_
    · intro _ K _ _ hK hs hna hRf E hE _ hcard
      obtain ⟨φ, hφ, hφ1⟩ := exists_ne_one_of_one_lt_card (lt_of_le_of_lt hp.one_lt.le hcard)
      exact ⟨φ, hφ, hφ1, RawAutSmall.mem_inner_g2der hK hna hodd (hE.2 φ hφ)⟩
    · intro _ a ha K _ _ hK hs hna hRf E hE _ hcard
      obtain ⟨φ, hφ, hφ1⟩ := exists_ne_one_of_one_lt_card (lt_of_le_of_lt hp.one_lt.le hcard)
      exact ⟨φ, hφ, hφ1, RawAut.mem_inner_of_isPGroup_outer
        (RawAutSmall.isPGroup_outer_twF4der ha hK) hodd (hE.2 φ hφ)⟩
  · have h := (MI.canonAll_iff_legacyAll hlab hd _).2 (largeEvenLabelAll_outdiag_simple hlab)
    exact MI.CAll.mono (fun R _ I F h' hs hna => innRank_of_outdiagCyclic hp.pos (h' hs hna)) h

end CFSG.LocalAnalysis.GLTheoremA.T156

end

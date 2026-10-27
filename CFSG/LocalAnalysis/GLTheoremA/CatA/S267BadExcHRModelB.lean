module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenB
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcFldLayer
import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen (ModelBGen)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

section Witness


theorem entrywiseAdjointAut_coe_rootDiagUnit (σ : K ≃+* K) {a : Fin τ.rank → Kˣ}
    (ha : rootDiagUnit τ a ∈ adjointGroup τ K) :
    (entrywiseAdjointAut τ σ ⟨_, ha⟩ : ModGL τ K) =
      rootDiagUnit τ (fun i => Units.map σ.toRingHom.toMonoidHom (a i)) := by
  rw [coe_entrywiseAdjointAut]
  exact Units.ext (entrywise_rootDiag σ.toRingHom a)

theorem entrywiseAdjointAut_coe_pinnedX (σ : K ≃+* K) {β : Fin τ.rank → ℤ} {c : K}
    (hβ : pinnedX τ K β c ∈ adjointGroup τ K) :
    (entrywiseAdjointAut τ σ ⟨_, hβ⟩ : ModGL τ K) = pinnedX τ K β (σ c) := by
  rw [coe_entrywiseAdjointAut]
  exact Units.ext (entrywise_pinnedX σ.toRingHom β c)

theorem modelBGen_hr [Finite K] (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hK2 : ringChar K ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hdet : ¬ (p : ℤ) ∣ τ.cartan.det)
    {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hout : entrywiseAdjointAut τ σ ∉ (MulAut.conj : ↥(adjointGroup τ K) →* _).range)
    (hpK0 : p ∣ Nat.card (fixSubfield σ) ^ 2 - 1) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hσζ : σ (ζ : K) = ζ) (hk : ∀ γ, IsRoot τ γ → |γ (highNode τ)| ≤ 2)
    {n : Fin τ.rank → ℤ} (hn : ∀ l, ∑ j, n j * τ.cartan j l = if l = highNode τ then 1 else 0)
    (hJq : CFSG.Open.IsQuasisimple ↥(rootSpan τ K (perpRoots τ))) {i₁ : Fin τ.rank}
    (hi₁ : i₁ ≠ highNode τ) :
    ModelBGen p τ.rank ↥(adjointGroup τ K) (entrywiseAdjointAut τ σ) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite ↥(adjointGroup τ K) := generated_group_finite τ K
  set j₀ := highNode τ with hj₀
  set ψ := entrywiseAdjointAut τ σ with hψ
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hζ] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
  have hζ1 : ζ ≠ 1 := fun h => hζ2 (by rw [h, one_pow])
  set E := hrTorusHom (K := K) (τ := τ) hp hdet hζp with hE
  have hEinj : Function.Injective E := hrTorusHom_injective hp hdet hζ
  have hEsingle : ∀ s, ((E (singleHom j₀ s) : ↥(adjointGroup τ K)) : ModGL τ K) =
      rootDiagUnit τ (Pi.mulSingle j₀ (ζ ^ (Multiplicative.toAdd s).val)) := fun s => by
    rw [hE, coe_hrTorusHom, toAdd_singleHom, zetaPow_single]
  have hEtorus : ∀ x, ((E x : ↥(adjointGroup τ K)) : ModGL τ K) ∈ torusGroup τ K := fun x =>
    rootDiagUnit_mem_torusGroup_of_pow_eq_one hp hdet (zetaPow_pow_eq_one hζp _)
  set dζ : ↥(adjointGroup τ K) := E (singleHom j₀ (Multiplicative.ofAdd 1)) with hdζ
  have hdζc : (dζ : ModGL τ K) = rootDiagUnit τ (Pi.mulSingle j₀ ζ) := by
    rw [hdζ, hEsingle, toAdd_ofAdd, ZMod.val_one, pow_one]
  set A : Subgroup ↥(adjointGroup τ K) := E.range with hA
  set A₁ : Subgroup ↥(adjointGroup τ K) := (E.comp (singleHom j₀)).range with hA₁
  set J : Subgroup ↥(adjointGroup τ K) :=
    (rootSpan τ K (perpRoots τ)).subgroupOf (adjointGroup τ K) with hJ
  have hdζA₁ : dζ ∈ A₁ := ⟨_, rfl⟩
  have htmem : rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) ∈ adjointGroup τ K :=
    CFSG.LieType.AlgebraicGroups.torusGroup_le_adjointGroup
      (rootDiagUnit_mulSingle_mem_torusGroup hn _)
  set t : ↥(adjointGroup τ K) := ⟨_, htmem⟩ with ht
  have he₁ : (Pi.single i₁ 1 : Fin τ.rank → ℤ) ∈ perpRoots τ :=
    ⟨IsRoot.basis i₁, Pi.single_eq_of_ne' hi₁ 1⟩
  have he₁' : (-Pi.single i₁ 1 : Fin τ.rank → ℤ) ∈ perpRoots τ :=
    ⟨IsRoot.neg (IsRoot.basis i₁), by rw [Pi.neg_apply, Pi.single_eq_of_ne' hi₁ 1, neg_zero]⟩
  have hpJ : p ∣ Nat.card (rootSpan τ K (perpRoots τ)) := dvd_card_rootSpan hp hp2 hζ he₁ he₁'
  have hJcomp : GLAPComponent p (Subgroup.centralizer ((A₁ : Subgroup _) : Set ↥(adjointGroup τ K)))
      J := by
    refine CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.glaPComponent_subgroupOf _ hp _
      (rootSpan_le_adjointGroup K _) ?_ ?_ hJq hpJ
    · rintro l hl _ ⟨s, rfl⟩
      have hc := commute_of_mem_toralCentralizer
        (rootSpan_perpRoots_le_toralCentralizer (ζ ^ (Multiplicative.toAdd s).val) hl)
      rw [MonoidHom.comp_apply, hEsingle]
      exact hc
    · intro g hg hcomm l hl
      have hgc := hcomm dζ hdζA₁
      rw [hdζc] at hgc
      exact (Subgroup.mem_normalizer_iff.1 (toralCentralizer_mulSingle_le_normalizer hζ1 hζ2 hk
        (mem_toralCentralizer_of_commute hg hgc)) l).1 hl
  have hJX : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Co15.isQuasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).symm hJq
  have hpJX : p ∣ Nat.card ↥J := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (rootSpan_le_adjointGroup K _)).toEquiv]
    exact hpJ
  have hAN : A ≤ Subgroup.normalizer (J : Set ↥(adjointGroup τ K)) := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hN := Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootSpan (S := perpRoots τ) (K := K) (fun _ hα => hα.1)
        (hEtorus x)) (h : ModGL τ K)
    simp only [hJ, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hN
  have hσζk : ∀ m : ℕ, Units.map σ.toRingHom.toMonoidHom (ζ ^ m) = ζ ^ m := fun m => by
    rw [map_pow]
    congr 1
    exact Units.ext hσζ
  have hψA : ∀ a ∈ A, ψ a = a := by
    rintro _ ⟨x, rfl⟩
    apply Subtype.ext
    rw [hψ, show E x = ⟨_, rootDiagUnit_zetaPow_mem hp hdet hζp (Multiplicative.toAdd x)⟩ from rfl,
      entrywiseAdjointAut_coe_rootDiagUnit]
    congr 1
    funext i
    exact hσζk _
  have hψk : ∀ (k : ℕ) {β : Fin τ.rank → ℤ} {c : K} (hβ : pinnedX τ K β c ∈ adjointGroup τ K),
      ((ψ ^ k) ⟨_, hβ⟩ : ModGL τ K) = pinnedX τ K β ((σ ^ k) c) := by
    intro k β c hβ
    rw [hψ, ← entrywiseAdjointAut_pow, entrywiseAdjointAut_coe_pinnedX]
  refine ⟨?_, hout, A, A₁, J, t, ?_, ?_, hψA, ?_, ?_, hJcomp, hAN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hψ, ← entrywiseAdjointAut_pow, ← hσ, pow_orderOf_eq_one]
    exact map_one (entrywiseAdjointAutHom (τ := τ) (K := K))
  ·
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨u, hu⟩ := x.2
      obtain ⟨v, hv⟩ := y.2
      change (x : ↥(adjointGroup τ K)) * y = y * x
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ p = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        funext i
        rw [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply, ZMod.natCast_self, zero_mul]
      rw [this, map_one]
  · rw [hA, card_range_of_injective' hEinj, card_multiplicative_fun]
  · rintro _ ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · have hinj : Function.Injective (E.comp (singleHom (p := p) j₀)) := by
      rw [MonoidHom.coe_comp]; exact hEinj.comp (singleHom_injective j₀)
    rw [hA₁, card_range_of_injective' hinj, card_multiplicative_zmod]
  · exact map_perpJ_entrywiseAdjointAut σ
  ·
    rintro _ ⟨x, rfl⟩ k hk hx
    set α : ↥(adjointGroup τ K) →* ↥(adjointGroup τ K) :=
      (MulAut.conj (E x)).toMonoidHom.comp (ψ ^ k).toMonoidHom with hα
    have hfix := CFSG.LocalAnalysis.GLTheoremA.H81.UniA3.eq_of_mul_inv_mem_glaPPrimeCoreOf hp hJX
      hpJX α fun j hj => by
        have h2 := (GLAPPrimeCoreOf p J).inv_mem (hx j hj)
        rw [_root_.mul_inv_rev, inv_inv] at h2
        exact h2
    have hroot : ∀ i, i ≠ j₀ → ∀ c : K,
        (rootChar (zetaPow ζ (Multiplicative.toAdd x)) (Pi.single i 1) : K) * (σ ^ k) c = c := by
      intro i hi c
      have hjmem : pinnedX τ K (Pi.single i 1) c ∈ adjointGroup τ K := by
        rw [pinnedX_single]
        exact xUnit_mem_adjointGroup i c
      have hjJ : (⟨_, hjmem⟩ : ↥(adjointGroup τ K)) ∈ J := by
        rw [hJ, Subgroup.mem_subgroupOf]
        exact pinnedX_mem_rootSpan (S := perpRoots τ) (α := Pi.single i 1)
          ⟨IsRoot.basis i, Pi.single_eq_of_ne' hi 1⟩ c
      have h := congrArg (fun g : ↥(adjointGroup τ K) => (g : ModGL τ K)) (hfix _ hjJ)
      simp only [hα, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
      rw [hψk k hjmem, coe_hrTorusHom, rootDiagUnit_conj_pinnedX _ (IsRoot.basis i)] at h
      exact pinnedX_injective (R := K) (τ := τ) (Pi.single i 1) h
    have hσk : σ ^ k = 1 := by
      ext c
      have h1 := hroot i₁ hi₁ 1
      rw [map_one, mul_one] at h1
      have h2 := hroot i₁ hi₁ c
      rw [h1, one_mul] at h2
      exact h2
    have hk0 : k = 0 := by
      have hdvd : p ∣ k := by rw [← hσ]; exact orderOf_dvd_of_pow_eq_one hσk
      exact Nat.eq_zero_of_dvd_of_lt hdvd hk
    refine ⟨hk0, ?_⟩
    have hcoord : ∀ i, i ≠ j₀ → Multiplicative.toAdd x i = 0 := by
      intro i hi
      have h' := hroot i hi 1
      rw [map_one, mul_one, rootChar_single, zetaPow] at h'
      have h'' : ζ ^ (Multiplicative.toAdd x i).val = 1 := Units.ext h'
      have hdvd := orderOf_dvd_of_pow_eq_one h''
      rw [hζ] at hdvd
      exact (ZMod.val_eq_zero _).1 (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
    refine ⟨Multiplicative.ofAdd (Multiplicative.toAdd x j₀), ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    apply Multiplicative.toAdd.injective
    rw [toAdd_singleHom, toAdd_ofAdd]
    funext i
    by_cases hi : i = j₀
    · subst hi
      rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hi, hcoord i hi]
  · exact glaPLayer_perpJ_inf_fix_ne_bot hτ hK2 hp hp2 σ hpK0
  ·
    intro h1
    have h := congrArg (fun g : ↥(adjointGroup τ K) => (g : ModGL τ K)) h1
    change rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) = 1 at h
    rw [← rootDiagUnit_one (τ := τ) (K := K)] at h
    have h' := congrFun (rootDiagUnit_injective h) j₀
    rw [Pi.mulSingle_eq_same, Pi.one_apply] at h'
    exact hK2 ((neg_one_eq_one_iff (R := K)).1 (by simpa using congrArg Units.val h'))
  ·
    apply Subtype.ext
    change rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) ^ 2 = 1
    rw [rootDiagUnit_pow_hr, ← rootDiagUnit_one (τ := τ) (K := K)]
    congr 1
    rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]
  ·
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (j : ModGL τ K) * rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) =
      rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) * (j : ModGL τ K)
    exact commute_of_mem_toralCentralizer
      (rootSpan_perpRoots_le_toralCentralizer (-1 : Kˣ) (Subgroup.mem_subgroupOf.1 hj))
  ·
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show ((E x : ↥(adjointGroup τ K)) : ModGL τ K) * rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) =
      rootDiagUnit τ (Pi.mulSingle j₀ (-1 : Kˣ)) * ((E x : ↥(adjointGroup τ K)) : ModGL τ K)
    rw [coe_hrTorusHom, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  ·
    apply Subtype.ext
    rw [hψ, entrywiseAdjointAut_coe_rootDiagUnit]
    congr 1
    funext i
    by_cases hi : i = j₀
    · subst hi
      rw [Pi.mulSingle_eq_same]
      exact Units.ext (by simp)
    · rw [Pi.mulSingle_eq_of_ne hi, map_one]

end Witness

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end

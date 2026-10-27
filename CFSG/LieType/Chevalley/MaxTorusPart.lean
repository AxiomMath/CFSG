module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd

public section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.MaxTorusPart

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TableBExc.E6Three
  CFSG.HardMathSupport.Timmesfeld.Steinberg CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest3 CFSG.RankThree.CentralCover

section Characters

variable {τ : Tag} {L : Type} [Field L]

theorem rootChar_zetaVec (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (x : Fin τ.rank → ZMod 3)
    (β : Fin τ.rank → ℤ) :
    rootChar (zetaVec ζ hζ x) β = zmodPowHom ζ hζ (.ofAdd (triPairing x β)) := by
  simp only [rootChar, zetaVec, triPairing]
  rw [ofAdd_sum, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zmodPowHom_zpow, mul_comm]

theorem rootChar_zetaVec_eq_one_iff {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (x : Fin τ.rank → ZMod 3) (β : Fin τ.rank → ℤ) :
    rootChar (zetaVec ζ hζ x) β = 1 ↔ triPairing x β = 0 := by
  rw [rootChar_zetaVec]
  constructor
  · intro h
    have h' : zmodPowHom ζ hζ (.ofAdd (triPairing x β)) = zmodPowHom ζ hζ (.ofAdd 0) := by
      rw [h, ofAdd_zero, map_one]
    exact Multiplicative.ofAdd.injective (zmodPowHom_injective hζo hζ h')
  · intro h
    rw [h, ofAdd_zero, map_one]

theorem mem_rootCharStabilizer_zetaVec_iff {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (x : Fin τ.rank → ZMod 3) (w : WeylGroup τ) :
    w ∈ rootCharStabilizer (zetaVec ζ hζ x) ↔ ∀ v, triPairing x (w • v) = triPairing x v := by
  constructor
  · intro h v
    have h' := h v
    rw [rootChar_zetaVec, rootChar_zetaVec] at h'
    exact Multiplicative.ofAdd.injective (zmodPowHom_injective hζo hζ h')
  · intro h v
    change rootChar (zetaVec ζ hζ x) (w • v) = rootChar (zetaVec ζ hζ x) v
    rw [rootChar_zetaVec, rootChar_zetaVec, h v]

theorem adAct_wordProd_eq_triAct (ω : List (Fin τ.rank)) (x : Fin τ.rank → ZMod 3) :
    adAct τ 3 ((coxeterSystem τ).wordProd ω) x = triAct ω x := by
  rw [← adWord_eq_adAct]
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change adRefl τ 3 i (adWord τ 3 ω x) = triReflect i (triAct ω x)
    rw [ih]
    funext j
    simp only [adRefl, triReflect, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

theorem weylTuple_zetaVec_triAct (ζ : Lˣ) (hζ : ζ ^ 3 = 1) (ω : List (Fin τ.rank))
    (x : Fin τ.rank → ZMod 3) :
    weylTuple ((coxeterSystem τ).wordProd ω) (zetaVec ζ hζ x) = zetaVec ζ hζ (triAct ω x) := by
  rw [weylTuple_zetaVec, adAct_wordProd_eq_triAct]

end Characters

section Conj

variable {G : Type*} [Group G]

theorem finite_map_conj (E : Subgroup G) [Finite E] (g : G) :
    Finite (E.map (MulAut.conj g).toMonoidHom) :=
  Finite.of_equiv E (E.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv

theorem map_conj_le {E H : Subgroup G} (hE : E ≤ H) {g : G} (hg : g ∈ H) :
    E.map (MulAut.conj g).toMonoidHom ≤ H := by
  rintro _ ⟨x, hx, rfl⟩
  exact H.mul_mem (H.mul_mem hg (hE hx)) (H.inv_mem hg)

theorem map_conj_comm {E : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (g : G) :
    ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, ∀ y ∈ E.map (MulAut.conj g).toMonoidHom,
      x * y = y * x := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  rw [← map_mul, ← map_mul, hcomm x hx y hy]

theorem map_conj_pow_eq_one {E : Subgroup G} {p : ℕ} (hexp : ∀ x ∈ E, x ^ p = 1) (g : G) :
    ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x ^ p = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, hexp x hx, map_one]

end Conj

section Monomial

variable {τ : Tag} {L : Type} [Field L]

theorem weylQuotientHom_mem_rootCharStabilizer {a : Fin τ.rank → Lˣ} {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) (hna : rootDiagUnit τ a * n = n * rootDiagUnit τ a) :
    weylQuotientHom τ L ⟨n, hn⟩ ∈ rootCharStabilizer a := by
  obtain ⟨w, k, hk, e⟩ := monomialSubgroup_le_torusWeylCosets hn
  subst e
  rw [weylQuotientHom_torus_mul hk w hn, ← conj_canonicalRep_eq_iff]
  have hdk : rootDiagUnit τ a * k = k * rootDiagUnit τ a :=
    rootDiagUnit_mul_comm_of_mem_torusGroup a hk
  have h1 : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w =
      canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ a := by
    have e1 : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w =
        k⁻¹ * (rootDiagUnit τ a * (k * canonicalRep (coxeterSystem τ) L w)) := by
      rw [← mul_assoc (rootDiagUnit τ a) k, hdk]
      group
    rw [e1, hna]
    group
  rw [h1, mul_inv_cancel_right]

theorem exists_zetaVec_of_mem_torusGroup {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {u : ModGL τ L} (hu : u ∈ torusGroup τ L) (hu3 : u ^ 3 = 1) :
    ∃ x : Fin τ.rank → ZMod 3, u = rootDiagUnit τ (zetaVec ζ hζ x) := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  have hb3 : b ^ 3 = 1 := by
    have h1 : rootDiagUnit τ (b ^ 3) = rootDiagUnit τ 1 := by
      rw [rootDiagUnit_pow', rootDiagUnit_one, hu3]
    exact CFSG.LieType.Chevalley.rootDiagUnit_injective h1
  obtain ⟨x, hx⟩ := exists_zetaVec_eq (τ := τ) hζo hζ hb3
  exact ⟨x, by rw [hx]⟩

theorem triPairing_weylQuotientHom_smul {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) {x : Fin τ.rank → ZMod 3}
    (hx : rootDiagUnit τ (zetaVec ζ hζ x) * n = n * rootDiagUnit τ (zetaVec ζ hζ x))
    (v : Fin τ.rank → ℤ) :
    triPairing x (weylQuotientHom τ L ⟨n, hn⟩ • v) = triPairing x v :=
  (mem_rootCharStabilizer_zetaVec_iff hζo hζ x _).1
    (weylQuotientHom_mem_rootCharStabilizer hn hx) v

theorem prod_mem_kernelWeylGroup {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) {ι : Type}
    (e : ι → Fin τ.rank → ZMod 3) (R : List (List (Fin τ.rank) × Fin τ.rank))
    (hR : ∀ p ∈ R, ∀ k, triPairing (e k) ((coxeterSystem τ).wordProd p.1 • Pi.single p.2 1) = 0) :
    (R.map fun p => (coxeterSystem τ).wordProd p.1 * simple τ p.2 *
      ((coxeterSystem τ).wordProd p.1)⁻¹).prod ∈
        kernelWeylGroup (familyChar fun k => zetaVec ζ hζ (e k)) := by
  refine list_prod_mem fun r hr => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  refine Subgroup.subset_closure ⟨(coxeterSystem τ).wordProd p.1, p.2, ?_, rfl⟩
  rw [kernelRoots_familyChar]
  exact ⟨CFSG.LieType.Chevalley.IsRoot.smul (isRoot_single τ p.2) _, fun k =>
    (rootChar_zetaVec_eq_one_iff hζo hζ (e k) _).2 (hR p hp k)⟩

theorem exists_max_card_inf_torus (E : Subgroup (ModGL τ L)) [Finite E] :
    ∃ g₀ ∈ adjointGroup τ L, ∀ g ∈ adjointGroup τ L,
      Nat.card ↥(E.map (MulAut.conj g).toMonoidHom ⊓ torusGroup τ L) ≤
        Nat.card ↥(E.map (MulAut.conj g₀).toMonoidHom ⊓ torusGroup τ L) := by
  classical
  have hNle : ∀ g : ModGL τ L,
      Nat.card ↥(E.map (MulAut.conj g).toMonoidHom ⊓ torusGroup τ L) ≤ Nat.card E := by
    intro g
    have := finite_map_conj E g
    calc _ ≤ Nat.card ↥(E.map (MulAut.conj g).toMonoidHom) := Subgroup.card_le_of_le inf_le_left
      _ = Nat.card E := Subgroup.card_map_of_injective (MulAut.conj g).injective
  let N : ModGL τ L → ℕ := fun g =>
    Nat.card ↥(E.map (MulAut.conj g).toMonoidHom ⊓ torusGroup τ L)
  let S : Finset ℕ := (Finset.range (Nat.card E + 1)).filter fun k =>
    ∃ g ∈ adjointGroup τ L, N g = k
  have hS : S.Nonempty := ⟨N 1, Finset.mem_filter.2
    ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hNle 1)), 1, one_mem _, rfl⟩⟩
  obtain ⟨g₀, hg₀G, hg₀⟩ := (Finset.mem_filter.1 (S.max'_mem hS)).2
  refine ⟨g₀, hg₀G, fun g hg => ?_⟩
  change N g ≤ N g₀
  rw [hg₀]
  exact S.le_max' _ (Finset.mem_filter.2
    ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hNle g)), g, hg, rfl⟩)

theorem exists_conj_monomial_sylow [IsAlgClosed L] {ℓ p : ℕ} [Fact ℓ.Prime] [hp : Fact p.Prime]
    (hℓ : ℓ ≠ p) [CharP L ℓ] (halg : letI := ZMod.algebra L ℓ; Algebra.IsAlgebraic (ZMod ℓ) L)
    {S : Subgroup (WeylGroup τ)} (hS : ¬ p ∣ S.index)
    {F : Subgroup (ModGL τ L)} [Finite F] (hFG : F ≤ adjointGroup τ L)
    (hcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) (hexp : ∀ x ∈ F, x ^ p = 1) :
    ∃ c ∈ adjointGroup τ L,
      (∀ x ∈ F.map (MulAut.conj c).toMonoidHom, x ∈ monomialSubgroup τ L) ∧
      (∀ x ∈ F.map (MulAut.conj c).toMonoidHom, ∀ hx : x ∈ monomialSubgroup τ L,
        weylQuotientHom τ L ⟨x, hx⟩ ∈ S) ∧
      Nat.card ↥(F ⊓ torusGroup τ L) ≤
        Nat.card ↥(F.map (MulAut.conj c).toMonoidHom ⊓ torusGroup τ L) := by
  classical
  set U := F ⊓ torusGroup τ L with hU
  have : Finite U := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_left : F ⊓ torusGroup τ L ≤ F))
  have : Fintype U := Fintype.ofFinite U
  have hchar : ∀ u : U, ∃ b : Fin τ.rank → Lˣ, (u : ModGL τ L) = rootDiagUnit τ b :=
    fun u => exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_inf.1 u.2).2
  choose a ha using hchar
  obtain ⟨z, hzG, hza, hzN⟩ := exists_conj_le_monomial_familyCentralizer_bar (ℓ := ℓ) (p := p)
    hℓ halg a hFG (Set.toFinite _) (fun x hx u => by
      rw [← ha u]
      exact hcomm _ (Subgroup.mem_inf.1 u.2).1 x hx) hexp
  set F₂ := F.map (MulAut.conj z).toMonoidHom with hF₂
  set P : Subgroup (WeylGroup τ) :=
    (F₂.subgroupOf (monomialSubgroup τ L)).map (weylQuotientHom τ L) with hP
  have hPp : IsPGroup p P := by
    rintro ⟨_, x, hx, rfl⟩
    have hxp : x ^ p = 1 := by
      obtain ⟨x₀, hx₀, hxx⟩ := Subgroup.mem_subgroupOf.1 hx
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hxx, ← map_pow, hexp x₀ hx₀, map_one, Subgroup.coe_one]
    refine ⟨1, Subtype.ext ?_⟩
    change weylQuotientHom τ L x ^ p ^ 1 = 1
    rw [pow_one, ← map_pow, hxp, map_one]
  obtain ⟨v, hv⟩ := CFSG.StandardType.TableBF4.exists_conj_le_of_not_dvd_index hp.out hS hPp
  set m := canonicalRep (coxeterSystem τ) L v with hm
  have hmG : m ∈ adjointGroup τ L := canonicalRep_mem_adjointGroup (coxeterSystem τ) L v
  have hmN : m ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L v
  have hπm : weylQuotientHom τ L ⟨m, hmN⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hconj : ∀ x, (MulAut.conj (m * z)).toMonoidHom x = m * (z * x * z⁻¹) * m⁻¹ := by
    intro x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine ⟨m * z, mul_mem hmG hzG, ?_, fun x hx hxN => ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [hconj]
    exact mul_mem (mul_mem hmN (hzN x hx)) (inv_mem hmN)
  · obtain ⟨x₀, hx₀, rfl⟩ := hx
    have hx₁N : z * x₀ * z⁻¹ ∈ monomialSubgroup τ L := hzN x₀ hx₀
    have he : (⟨(MulAut.conj (m * z)).toMonoidHom x₀, hxN⟩ : monomialSubgroup τ L) =
        ⟨m, hmN⟩ * ⟨z * x₀ * z⁻¹, hx₁N⟩ * (⟨m, hmN⟩ : monomialSubgroup τ L)⁻¹ :=
      Subtype.ext (hconj x₀)
    rw [he, map_mul, map_mul, map_inv, hπm]
    apply hv
    refine ⟨weylQuotientHom τ L ⟨z * x₀ * z⁻¹, hx₁N⟩,
      ⟨⟨z * x₀ * z⁻¹, hx₁N⟩, Subgroup.mem_subgroupOf.2 ⟨x₀, hx₀, rfl⟩, rfl⟩, rfl⟩
  ·
    have hle : U.map (MulAut.conj (m * z)).toMonoidHom ≤
        F.map (MulAut.conj (m * z)).toMonoidHom ⊓ torusGroup τ L := by
      rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_inf.2 ⟨⟨u, (Subgroup.mem_inf.1 hu).1, rfl⟩, ?_⟩
      have h2 : u = rootDiagUnit τ (a ⟨u, hu⟩) := ha ⟨u, hu⟩
      have hzu : z * u * z⁻¹ = u := by
        rw [h2, ← hza ⟨u, hu⟩, mul_inv_cancel_right]
      rw [hconj, hzu, h2, hm, canonicalRep_conj_rootDiagUnit]
      exact rootDiagUnit_mem_torusGroup _
    have : Finite ↥(F.map (MulAut.conj (m * z)).toMonoidHom) := finite_map_conj F _
    have : Finite ↥(F.map (MulAut.conj (m * z)).toMonoidHom ⊓ torusGroup τ L) :=
      Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
    calc Nat.card U = Nat.card ↥(U.map (MulAut.conj (m * z)).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj (m * z)).injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle

theorem exists_conj_card_torus_lt_of_mem_kernelWeylGroup {p : ℕ} (hmon : MonomialToralAt τ p)
    [IsAlgClosed L] (hL : ringChar L ≠ p) {F : Subgroup (ModGL τ L)} [Finite F]
    {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (ha : ∀ u ∈ F ⊓ torusGroup τ L, ∃ i, rootDiagUnit τ (a i) = u)
    {n : ModGL τ L} (hnF : n ∈ F) (hnT : n ∉ torusGroup τ L) (hnN : n ∈ monomialSubgroup τ L)
    (hnp : n ^ p = 1) (hwK : weylQuotientHom τ L ⟨n, hnN⟩ ∈ kernelWeylGroup (familyChar a)) :
    ∃ g ∈ adjointGroup τ L, Nat.card ↥(F ⊓ torusGroup τ L) <
      Nat.card ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup τ L) := by
  classical
  obtain ⟨g, hgR, hgn⟩ := hmon L hL (ι → Lˣ) (familyChar a) n hnN hwK
    (weylQuotientHom_pow_eq_one hnN hnp)
  have hgG : g ∈ adjointGroup τ L := rootSpan_le_adjointGroup L _ hgR
  have hgU : ∀ u ∈ F ⊓ torusGroup τ L, g * u * g⁻¹ = u := by
    intro u hu
    obtain ⟨i, rfl⟩ := ha u hu
    have hgc : g ∈ Subgroup.centralizer {rootDiagUnit τ (a i)} := by
      refine rootSpan_le_centralizer (a i) (S := kernelRoots (familyChar a))
        (fun α hα => ?_) hgR
      rw [kernelRoots_familyChar] at hα
      exact ⟨hα.1, hα.2 i⟩
    rw [Subgroup.mem_centralizer_singleton_iff.1 hgc, mul_inv_cancel_right]
  refine ⟨g, hgG, ?_⟩
  set U := F ⊓ torusGroup τ L with hU
  have : Finite ↥(F.map (MulAut.conj g).toMonoidHom) := finite_map_conj F g
  have : Finite ↥(F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup τ L) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  have hle : U.map (MulAut.conj g).toMonoidHom ≤
      F.map (MulAut.conj g).toMonoidHom ⊓ torusGroup τ L := by
    rintro _ ⟨u, hu, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨u, (Subgroup.mem_inf.1 hu).1, rfl⟩, ?_⟩
    change g * u * g⁻¹ ∈ torusGroup τ L
    rw [hgU u hu]
    exact (Subgroup.mem_inf.1 hu).2
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  rw [← Subgroup.card_map_of_injective (K := U) hinj]
  refine lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun hcard => ?_
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  have hgn' : g * n * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := by
    rw [heq]
    exact Subgroup.mem_inf.2 ⟨⟨n, hnF, rfl⟩, hgn⟩
  obtain ⟨u, hu, hun⟩ := hgn'
  have hun' : u = n := by
    have h1 : g * u * g⁻¹ = g * n * g⁻¹ := hun
    exact mul_left_cancel (mul_right_cancel h1)
  exact hnT (hun' ▸ (Subgroup.mem_inf.1 hu).2)

end Monomial

end CFSG.LieType.Chevalley.MaxTorusPart

module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.FourUGeneric
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporFacts
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUModel

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.Burgoyne.U
open CFSG.RankThree.Classical (subfieldSU subfieldPSU subfieldPSU_injective subfieldPSU_mk
  exists_subfieldGL_eq_of_fixed mem_gramSU_of_subfieldGL range_subfieldPSU_le
  fixSubfield_unitaryFieldData fixSubfield_unitaryFieldData_bar)
open CFSG.LieType.Chevalley (fixSubfield)

section Fixed

variable {ℓ f e n : ℕ} {K : Type} [Field K]

theorem fixSubgroup_primeFormFieldSU_eq_range' (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) :
    fixSubgroup (primeFormFieldSU h hC σ) = (subfieldSU h h₀ hbar n).range := by
  ext x
  rw [mem_fixSubgroup]
  constructor
  · intro hx
    have hx' : glAut σ (x : GL (Fin n) K) = x := congrArg Subtype.val hx
    obtain ⟨g₀, hg₀⟩ := exists_subfieldGL_eq_of_fixed n hx'
    have hg₀S := mem_gramSU_of_subfieldGL h n h₀ hbar (hg₀ ▸ x.2)
    exact ⟨⟨g₀, hg₀S⟩, Subtype.ext hg₀⟩
  · rintro ⟨y, rfl⟩
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    change σ ((((y : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j :
      fixSubfield σ) : K) = (((y : GL (Fin n) (fixSubfield σ)) :
        Matrix (Fin n) (Fin n) (fixSubfield σ)) i j : K)
    exact (((y : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ)) i j).2

theorem map_range_subfieldSU (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) :
    (subfieldSU h h₀ hbar n).range.map
        (QuotientGroup.mk' (normOneScalars h (gramSU h ((1 : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) n)) = (subfieldPSU h h₀ hbar n).range := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hx
    exact MonoidHom.mem_range.2 ⟨(g : primeFormP h₀ _), subfieldPSU_mk h h₀ hbar n g⟩
  · intro hy
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.1 hy
    induction z using QuotientGroup.induction_on with
    | H g =>
      exact Subgroup.mem_map.2 ⟨subfieldSU h h₀ hbar n g, MonoidHom.mem_range.2 ⟨g, rfl⟩, rfl⟩

theorem mem_of_comm_quotient {G : Type} [Group G] {N : Subgroup G} [N.Normal]
    (h : ∀ a b : G ⧸ N, a * b = b * a) (x y : G) : (x * y)⁻¹ * (y * x) ∈ N := by
  have hxy := h (x : G ⧸ N) (y : G ⧸ N)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hxy
  exact hxy

theorem fixed_quotient_facts (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c)
    (hC : IsPrimeFormGram (1 : GL (Fin n) K)) :
    (subfieldPSU h h₀ hbar n).range ≤ fixSubgroup (primeFormFieldHom h hC σ) ∧
      ((subfieldPSU h h₀ hbar n).range.subgroupOf
        (fixSubgroup (primeFormFieldHom h hC σ))).Normal ∧
      ∀ x y : fixSubgroup (primeFormFieldHom h hC σ),
        (x * y)⁻¹ * (y * x) ∈
          (subfieldPSU h h₀ hbar n).range.subgroupOf (fixSubgroup (primeFormFieldHom h hC σ)) := by
  let Z : Subgroup ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    normOneScalars h (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n
  have hZ : Z ≤ Subgroup.center _ := normOneScalars_le_center h _ n
  have hαZ : Z.map ((primeFormFieldSU h hC σ : _ ≃* _) : _ →* _) = Z :=
    map_normOneScalars_field h hC σ
  have hCT : (fixSubgroup (primeFormFieldSU h hC σ)).map (QuotientGroup.mk' Z) =
      (subfieldPSU h h₀ hbar n).range := by
    rw [fixSubgroup_primeFormFieldSU_eq_range' h h₀ hbar hC]
    exact map_range_subfieldSU h h₀ hbar
  have key := CFSG.RankThree.GroupTheory.central_quotient_fixed_group_exact_sequence Z hZ
    (primeFormFieldSU h hC σ) hαZ
  obtain ⟨hZAn, δ, hA, hB, hC', hD, hEx⟩ := key
  obtain ⟨hZAΔ, hF, hG, hH, hnormEx⟩ := hEx
  obtain ⟨hnorm, ε, hεspec, hker, hsurj, ⟨e', he'⟩, hcomm, hpow⟩ := hnormEx
  haveI := hnorm
  refine ⟨range_subfieldPSU_le h n h₀ hbar, ?_, ?_⟩
  · rw [← hCT]
    exact hnorm
  · have hcommQ := fun a b => e'.injective ((e'.map_mul a b).trans
      ((hcomm (e' a) (e' b)).trans (e'.map_mul b a).symm))
    intro x y
    have hxy := mem_of_comm_quotient hcommQ x y
    rw [← hCT]
    exact hxy

end Fixed

section Groups

variable {ℓ f e n : ℕ} {K : Type} [Field K]

theorem range_subfieldPSU_mulEquiv (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K}
    (h₀ : UnitaryFieldData ℓ e (fixSubfield σ))
    (hbar : ∀ c : fixSubfield σ, (h₀.bar c : K) = h.bar c) (hn : 1 ≤ n) :
    Nonempty (↥(subfieldPSU h h₀ hbar n).range ≃*
      primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) : Matrix (Fin n) (Fin n) (fixSubfield σ))) :=
  ⟨(MonoidHom.ofInjective (subfieldPSU_injective h h₀ hbar n hn)).symm⟩

theorem isSolvable_quotient_of_mem {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (hN : ∀ x y : G, (x * y)⁻¹ * (y * x) ∈ N) : Group.IsSolvable (G ⧸ N) := by
  refine Group.isSolvable_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact hN x y

theorem psu62_facts {G : Type} [Group G] {k : Type} [Field k] [Finite k]
    (hk : Nat.card k = (2 ^ 1) ^ 2)
    (e : G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) k)) :
    IsSimpleGroup G ∧ (∃ x y : G, x * y ≠ y * x) ∧ 3 ∣ Nat.card G ∧
      CFSG.Open.IsQuasisimple G ∧ IsLieQuot G IsU6TwoIndex := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect (CFSG.Open.StatedSU 6 (2 ^ 1) k) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hk (by norm_num) (by decide)
  have hs : IsSimpleGroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) k)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU k 2 1 hk 6 (by norm_num)
      (by decide)
  have hsG : IsSimpleGroup G := e.isSimpleGroup_congr.2 hs
  have hnc0 : ∃ x y : CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) k),
      x * y ≠ y * x := by
    by_contra hcon
    push_neg at hcon
    haveI := hs
    haveI : IsMulCommutative (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) k)) :=
      ⟨⟨hcon⟩⟩
    haveI : Group.IsPerfect (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) k)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact Group.IsPerfect.not_isMulCommutative
      (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) k)) inferInstance
  have hnc : ∃ x y : G, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := hnc0
    refine ⟨e.symm a, e.symm b, fun hG => hab ?_⟩
    have := congrArg e hG
    simpa using this
  have hcard : 3 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two le_rfl hk
        (by norm_num : 2 ≤ 6)]
    decide
  have hq : CFSG.Open.IsQuasisimple G :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126.isQuasisimple_of_simple hsG hnc
  have hlie : IsLieQuot G IsU6TwoIndex := by
    haveI := hsG
    have hZ : Subgroup.center G = ⊥ := by
      rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnc
        apply hab
        have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.1 ha b).symm
    let eqG : G ⧸ Subgroup.center G ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) k) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)
    have hmodel : CFSG.Open.StatedClassicalModel (G ⧸ Subgroup.center G) .PSU (5 + 1) 2 1 :=
      ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, k, inferInstance, inferInstance, hk,
        ⟨eqG⟩⟩
    exact KSExact.isLieQuot_of_twistedA_model (m := 5) (p := 2) (f := 1) hmodel IsU6TwoIndex
      (fun q hq2 hq1 => ⟨q, ⟨hq2, hq1⟩, rfl⟩)
  exact ⟨hsG, hnc, hcard, hq, hlie⟩

theorem comap_fixed_facts {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (M' T' : Subgroup G')
    (hTM : T' ≤ M') (hn : (T'.subgroupOf M').Normal)
    (hc : ∀ x y : ↥M', (x * y)⁻¹ * (y * x) ∈ T'.subgroupOf M') :
    T'.comap e.toMonoidHom ≤ M'.comap e.toMonoidHom ∧
      ((T'.comap e.toMonoidHom).subgroupOf (M'.comap e.toMonoidHom)).Normal ∧
      ∀ x y : ↥(M'.comap e.toMonoidHom),
        (x * y)⁻¹ * (y * x) ∈ (T'.comap e.toMonoidHom).subgroupOf (M'.comap e.toMonoidHom) := by
  let f : ↥(M'.comap e.toMonoidHom) →* ↥M' :=
    (e.toMonoidHom.comp (M'.comap e.toMonoidHom).subtype).codRestrict M' (fun x => x.2)
  have hf : (T'.comap e.toMonoidHom).subgroupOf (M'.comap e.toMonoidHom) =
      (T'.subgroupOf M').comap f := by
    ext x
    exact Iff.rfl
  refine ⟨Subgroup.comap_mono hTM, ?_, ?_⟩
  · rw [hf]
    exact hn.comap f
  · intro x y
    rw [hf, Subgroup.mem_comap]
    simp only [map_mul, map_inv]
    exact hc (f x) (f y)

end Groups

variable {K0 : Type} [Field K0]

theorem u6_fix_unique_component (h : UnitaryFieldData 2 3 K0) {σ : K0 ≃+* K0}
    (hσ : orderOf σ = 3) :
    ∃ T : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 3) K0)),
      CFSG.Open.GLAPComponent 3 (fixSubgroup (uFieldAut h (by norm_num) σ)) T ∧
      (∀ L : Subgroup (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 3) K0)),
        CFSG.Open.GLAPComponent 3 (fixSubgroup (uFieldAut h (by norm_num) σ)) L → L = T) ∧
      CFSG.Open.IsQuasisimple ↥T ∧ IsLieQuot ↥T IsU6TwoIndex := by
  haveI : Finite K0 := h.finite
  haveI : Finite (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 3) K0)) :=
    CFSG.ClassicalGroups.Unitary.finite_statedProj_statedSU 6 (2 ^ 3) K0
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  let h₀ : UnitaryFieldData 2 1 (fixSubfield σ) := fixSubfield_unitaryFieldData h hp3 hp2 hσ
  have hbar : ∀ c : fixSubfield σ, (h₀.bar c : K0) = h.bar c :=
    fixSubfield_unitaryFieldData_bar h hp3 hp2 hσ
  have hC : IsPrimeFormGram (1 : GL (Fin 6) K0) := uGram_one
  have h6 : 1 ≤ 6 := by norm_num
  obtain ⟨hTM, hnorm, hcomm⟩ := fixed_quotient_facts (n := 6) h h₀ hbar hC
  obtain ⟨hTM', hnorm', hcomm'⟩ := comap_fixed_facts (uTransport h h6)
    (fixSubgroup (primeFormFieldHom h hC σ)) ((subfieldPSU h h₀ hbar 6).range) hTM hnorm hcomm
  have hMfix : fixSubgroup (uFieldAut h (by norm_num) σ) =
      (fixSubgroup (primeFormFieldHom h hC σ)).comap (uTransport h h6).toMonoidHom := by
    ext x
    rw [mem_fixSubgroup, Subgroup.mem_comap, mem_fixSubgroup]
    change (uTransport h h6).symm (primeFormFieldHom h hC σ ((uTransport h h6) x)) = x ↔ _
    constructor
    · intro hx
      have := congrArg (uTransport h h6) hx
      rwa [MulEquiv.apply_symm_apply] at this
    · intro hx
      rw [show primeFormFieldHom h hC σ ((uTransport h h6) x) = (uTransport h h6) x from hx,
        MulEquiv.symm_apply_apply]
  have hk : Nat.card ↥(fixSubfield σ) = (2 ^ 1) ^ 2 := by
    rw [h₀.card]
    norm_num
  let eT₀ : ↥(subfieldPSU h h₀ hbar 6).range ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) (fixSubfield σ)) :=
    (range_subfieldPSU_mulEquiv h h₀ hbar h6).some.trans (uTransport h₀ h6).symm
  have hmap : (((subfieldPSU h h₀ hbar 6).range).comap (uTransport h h6).toMonoidHom).map
      (uTransport h h6).toMonoidHom = (subfieldPSU h h₀ hbar 6).range :=
    Subgroup.map_comap_eq_self_of_surjective (uTransport h h6).surjective _
  let eT := ((uTransport h h6).subgroupMap
      (((subfieldPSU h h₀ hbar 6).range).comap (uTransport h h6).toMonoidHom)).trans
    ((MulEquiv.subgroupCongr hmap).trans eT₀)
  obtain ⟨hs, hnc, h3, hq, hlie⟩ := psu62_facts hk eT
  haveI := hnorm'
  refine ⟨((subfieldPSU h h₀ hbar 6).range).comap (uTransport h h6).toMonoidHom, ?_, ?_, hq,
    hlie⟩
  · rw [hMfix]
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims126.glaPComponent_of_simple_normal
      Nat.prime_three hTM' hnorm' hs hnc h3
  · intro L hL
    rw [hMfix] at hL
    exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporFacts.glaPComponent_eq_of_simple_normal
      hTM' hnorm' hs (isSolvable_quotient_of_mem _ hcomm') hL

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end

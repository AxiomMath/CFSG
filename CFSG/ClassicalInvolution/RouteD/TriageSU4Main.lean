module

public import CFSG.ClassicalInvolution.RouteD.TriageSU4Layer
public import CFSG.ClassicalInvolution.RouteD.TriageSU4Chain
public import CFSG.ClassicalInvolution.RouteD.TriageSU4Frame
public import CFSG.ClassicalInvolution.RouteD.TriageP1Rows
public import CFSG.ClassicalInvolution.Asc77.SU4ThreeStmt

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.SU4Pattern CFSG.ClassicalInvolution.RouteD.NonClassical
  CFSG.ClassicalInvolution.Models CFSG.LieType.Steinberg CFSG.LieType.BorelTits
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair diagConj2)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem su4LinearLift_of_frame (hP1 : P1RowSU4 p f) (hb : D4FrameRigid p f .POmegaPlus 4 f) :
    SU4LinearLiftStmt p f := by
  intro G _ _ _ hnab K z S hshape Λ K₁ K₂ z₁ hK₁ hK₂ hz₁ c02 p01 p12 hK₂i hz₁z
  classical
  have hp2 := S.odd
  have hq := S.five
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hcen := center_eq_bot hnab
  have hMFZ := Gaps.fundNoncentral p
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have hz₁2 : z₁ * z₁ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one z₁
    rwa [hz₁.orderOf_eq_two] at this
  have hKz : K ∈ centralizingMembers (conjClass K) {z} :=
    ⟨mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hK₂z : K₂ ∈ centralizingMembers (conjClass K) {z} :=
    mem_centralizingMembers_of_commutes hK₂ S.cls.mem c02.symm
  obtain ⟨w, hw⟩ := hΩ.classical K₂ hK₂
  have hK₂K : K₂ ≠ K := fun h => not_commutes_self_of_isClassicalMember S.cls (h ▸ c02)
  have hzw : z ≠ w := by
    intro hzw
    subst hzw
    obtain ⟨i, hit, hir, hiK⟩ := locImg_eq_range_of_involution hMFZ Λ.D hK₂z hw
    have hi1 : i ≠ Λ.i₁ := by
      rintro rfl
      rw [Λ.tag_eq] at hit
      exact absurd hit (by decide)
    exact hi1 (eq_of_locImg_le_range hΩ hex Λ.D hK₂z hiK.le hK₂i)
  have hP1x : LocalOddCentral (conjClass K) {z * w} :=
    hP1 G hnab K z S hshape K₂ hK₂ w hw c02 hzw
  have hK₁x : K₁ ≤ Subgroup.centralizer ({z * w} : Set G) :=
    SU4Pattern.chain_le_centralizer_mul (by omega) h2 S.cls hw c02 p01 p12
  have hK₁K : K₁ ≠ K := fun h => ne_of_linearBlockStandardPair p01.choose_spec h.symm
  have hnc : ¬ Commutes K K₁ := not_commutes_of_linearBlockStandardPair p01.choose_spec
  obtain ⟨T₁, hT₁, hT₁K, hT₁comm, j', hj'1, hT₁j'⟩ :=
    exists_twin_su hΩ hex S.p1 hp2 hq Λ (mem_conjClass_self K) S.cls
  have hK₂T : K₂ ≠ T₁ := by
    intro h
    apply hj'1
    exact eq_of_locImg_le_range hΩ hex Λ.D hK₂z (by rw [h]; exact hT₁j') hK₂i
  obtain ⟨D, c, htag, hrank, hexp, -, hKc, hK₂c, hT₁c, hallc⟩ :=
    exists_d4_component_of_twin_product hp2 hq hcen hΩ hex S.ih (mem_conjClass_self K)
      (single_class K) S.cls S.p1 hT₁ hT₁K hT₁comm hK₂z hK₂K hK₂T hw hzw hP1x
      ⟨K₁, ⟨hK₁, hK₁x⟩, hK₁K, hnc⟩
  have hK₁c := hallc K₁ ⟨hK₁, hK₁x⟩ hK₁K hnc
  have cKT : Commutes K T₁ := Commutes.symm (hT₁comm K hKz hT₁K.symm)
  have cTK₂ : Commutes T₁ K₂ := hT₁comm K₂ hK₂z hK₂T
  obtain ⟨N₄, hN₄c, d14, d24, d34, k14, k24, k34⟩ := exists_fourth_member hp2 hq hΩ hex hP1x D
    htag hrank hexp hKc hT₁c hK₂c hT₁K.symm hK₂K.symm hK₂T.symm cKT c02 cTK₂
  have hN₄z : N₄ ∈ centralizingMembers (conjClass K) {z} :=
    ⟨hN₄c.1.1, le_centralizer_of_commutes (Commutes.symm k14) S.cls.mem⟩
  have hK := card_galoisField_two_mul_eq (p := p) hq
  obtain ⟨l, hl, hl4⟩ :=
    exists_norm_one_pow_four (K := GaloisField p (2 * f)) (p := p) (f := f) hK hq
  obtain ⟨R, hR, hK₂R⟩ := Λ.exists_longRoot_of_mem hp2 hΩ S.p1 hK₂z hK₂i
  obtain ⟨g₁, hg₁⟩ := (mem_longRootSetU_iff (K := GaloisField p (2 * f)) (p := p) (f := f)
    (by norm_num : 2 ≤ 4)).mp hR
  have hg₁' : locImg (conjClass K) z K₂ =
      ((rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map
        (MulAut.conj g₁).toMonoidHom).map (Λ.ψ hp2) := by
    rw [hK₂R, hg₁]
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective
    (Λ.ψ hp2 (g₁ * su4TorusElt (GaloisField p (2 * f)) p f l hl * g₁⁻¹))
  have hyz : (y : G) * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp
    (centralizingLayer_le_centralizer (conjClass K) {z} y.2)
  have htz : (y : G) * z * (y : G)⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hyz
  have hcentr : ∀ {N : Subgroup G}, N ∈ centralizingMembers (conjClass K) {z} →
      (N = K₂ ∨ Commutes N K₂) → N ≤ Subgroup.centralizer ({(y : G)} : Set G) :=
    fun hN hNK₂ => le_centralizer_of_torus_lift hp2 hq hΩ S.p1 Λ hg₁' l hl y hy hN hNK₂
  have htw : (y : G) * w * (y : G)⁻¹ = w := by
    have := Subgroup.mem_centralizer_singleton_iff.mp ((hcentr hK₂z (Or.inl rfl)) hw.mem)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  have htx : (y : G) * (z * w) * (y : G)⁻¹ = z * w := by
    calc (y : G) * (z * w) * (y : G)⁻¹ = ((y : G) * z * (y : G)⁻¹) * ((y : G) * w * (y : G)⁻¹) := by
          group
      _ = z * w := by rw [htz, htw]
  have d03 : K ≠ N₄ := fun h => d14 h.symm
  have d13 : T₁ ≠ N₄ := fun h => d24 h.symm
  have d23 : K₂ ≠ N₄ := fun h => d34 h.symm
  have cK₂N : Commutes K₂ N₄ := k34
  let N : Fin 4 → Subgroup G := ![K, T₁, K₂, N₄]
  have hNmem : ∀ i, N i ∈ compMembers (conjClass K) (z * w) D c := by
    intro i
    fin_cases i
    exacts [hKc, hT₁c, hK₂c, hN₄c]
  have hinj : Function.Injective N := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
      | rfl
      | (exfalso
         simp only [N, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
           Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at hab
         first
         | exact hT₁K.symm hab
         | exact hT₁K hab
         | exact hK₂K.symm hab
         | exact hK₂K hab
         | exact d03 hab
         | exact d03 hab.symm
         | exact hK₂T.symm hab
         | exact hK₂T hab
         | exact d13 hab
         | exact d13 hab.symm
         | exact d23 hab
         | exact d23 hab.symm)
  have hcomm : ∀ i j, i ≠ j → Commutes (N i) (N j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
      | exact absurd rfl hij
      | exact cKT
      | exact Commutes.symm cKT
      | exact c02
      | exact Commutes.symm c02
      | exact cTK₂
      | exact Commutes.symm cTK₂
      | exact k14
      | exact Commutes.symm k14
      | exact k24
      | exact Commutes.symm k24
      | exact k34
      | exact Commutes.symm k34
  have hfix : ∀ i, N i ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
    intro i
    fin_cases i
    · exact hcentr hKz (Or.inr c02)
    · exact hcentr hT₁ (Or.inr cTK₂)
    · exact hcentr hK₂z (Or.inl rfl)
    · exact hcentr hN₄z (Or.inr (Commutes.symm k34))
  have hconj : conjSub (y : G) K₁ = K₁ := by
    refine conjSub_eq_of_frame hb hΩ hex hP1x hp2 hq D htag hrank hexp htx hNmem hinj hcomm hfix
      hK₁c p01 ?_
    obtain ⟨W, hW⟩ := p12
    exact ⟨W, linearBlockStandardPair_symm hW⟩
  have hz₁' : IsClassicalMember p f K₁ ((y : G) * z₁ * (y : G)⁻¹) := by
    have := hz₁.conj (y : G)
    rwa [hconj] at this
  have hz₁t : (y : G) * z₁ * (y : G)⁻¹ = z₁ :=
    unique_involution_of_isClassicalMember h2 (hex K₁ hK₁) hz₁' hz₁
  have hτ := Gaps.locAut_locAut hΩ.conjInvariant hz₁z hz₁2
  obtain ⟨θ, hθr, hθτ⟩ := exists_chart_of_standardPair hp2 hΩ.conjInvariant hz₁
    (le_centralizingLayer hK₂z) hz₁z p12
  set ψ₁ : Su (GaloisField p (2 * f)) p f 4 →* locQuot (conjClass K) z :=
    (Λ.ψ hp2).comp (MulAut.conj g₁).toMonoidHom with hψ₁
  have hker := (Λ.ψ_spec hp2).1
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center (Su (GaloisField p (2 * f)) p f 4) := by
    intro x hx
    have h1 : (MulAut.conj g₁).toMonoidHom x ∈ (Λ.ψ hp2).ker := hx
    exact (MulEquivClass.apply_mem_center_iff (MulAut.conj g₁)).1 (hker h1)
  have hψ₁range : ψ₁.range = (Λ.D.hom Λ.i₁).range := by
    rw [hψ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj g₁).surjective,
      Subgroup.map_top]
    exact (Λ.ψ_spec hp2).2.1
  have hθ : θ.range = (rootSU2 (GaloisField p (2 * f)) p f (by norm_num : 2 ≤ 4)).map ψ₁ := by
    rw [hθr, hg₁', Subgroup.map_map]
  have hT : Gaps.locAut hΩ.conjInvariant hz₁z
      (ψ₁ (su4TorusElt (GaloisField p (2 * f)) p f l hl)) =
      ψ₁ (su4TorusElt (GaloisField p (2 * f)) p f l hl) := by
    have e1 : ψ₁ (su4TorusElt (GaloisField p (2 * f)) p f l hl) = locMk (conjClass K) z y := by
      have : ψ₁ (su4TorusElt (GaloisField p (2 * f)) p f l hl) =
          Λ.ψ hp2 (g₁ * su4TorusElt (GaloisField p (2 * f)) p f l hl * g₁⁻¹) := rfl
      rw [this]
      exact hy.symm
    rw [e1, locAut_mk]
    congr 1
    apply Subtype.ext
    show z₁ * (y : G) * z₁⁻¹ = y
    have hcz : (y : G) * z₁ = z₁ * y := by
      have := hz₁t
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    rw [← hcz, mul_assoc, mul_inv_cancel, mul_one]
  have hstab : ∀ x, Gaps.locAut hΩ.conjInvariant hz₁z (ψ₁ x) ∈ ψ₁.range := by
    obtain ⟨A₀, hA₀⟩ := exists_blockEmb_not_central hK hp2 hq
    refine stab_of_noncentral hK hq ψ₁ ?_ (Gaps.locAut hΩ.conjInvariant hz₁z) hA₀ ?_
    · rw [hψ₁range]
      exact range_normal_of_lieSystem Λ.D Λ.i₁
    · have hmem : ψ₁ (blockEmb (GaloisField p (2 * f)) p f 4 2 0 (by omega) A₀) ∈ θ.range := by
        rw [hθ]
        exact ⟨_, ⟨A₀, rfl⟩, rfl⟩
      obtain ⟨s, hs⟩ := hmem
      rw [← hs, hθτ s]
      have : θ (diagConj2 (-1) 1 s) ∈ θ.range := ⟨_, rfl⟩
      rw [hθ] at this
      exact Subgroup.map_le_range _ _ this
  obtain ⟨ε⟩ : Nonempty (GaloisField p f ≃+* fixedSubfield (GaloisField p (2 * f)) p f) := by
    have hf : f ≠ 0 := by
      rintro rfl
      simp at hq
    have hcardF : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
    have hcardk : Nat.card (fixedSubfield (GaloisField p (2 * f)) p f) = p ^ f :=
      card_fixedSubfield hK
    have := Fintype.ofFinite (GaloisField p f)
    have := Fintype.ofFinite (fixedSubfield (GaloisField p (2 * f)) p f)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardF, hcardk])⟩
  have hlin₁ : LinearLift ψ₁ (Gaps.locAut hΩ.conjInvariant hz₁z) :=
    linearLift_of_torus_fixed hK hp2 hq ε ψ₁ hψ₁ker (Gaps.locAut hΩ.conjInvariant hz₁z) hτ
      hstab θ hθ (-1) hθτ l hl hl4 hT
  have hcomp : ψ₁.comp (MulAut.conj g₁⁻¹).toMonoidHom = Λ.ψ hp2 := by
    ext x
    show Λ.ψ hp2 (g₁ * (g₁⁻¹ * x * g₁⁻¹⁻¹) * g₁⁻¹) = Λ.ψ hp2 x
    congr 1
    group
  have := hlin₁.comp_conj g₁⁻¹
  rwa [hcomp] at this

end CFSG.ClassicalInvolution.Generic.CoreAssembly

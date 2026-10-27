module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPSp
public import CFSG.ClassicalInvolution.Q3.Q3TLKLink
public import CFSG.ClassicalInvolution.Q3.Q3TIYRank2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TIV
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow)
open scoped MatrixGroups


section Model

theorem center_and_noTwins_of_kind {t' : StatedLieTag} {n' : ℕ}
    (ht' : t' = .G2 ∨ t' = .trialityD4) (hadm : StatedLieAdmissible t' n' 3 1) {c : CompData}
    (hc : c = CompData.model t' n') :
    Subgroup.center c.G = ⊥ ∧ ∀ F ∈ c.fund, ∀ r : c.G, IsUniqueInvolution F r →
      ∀ g : c.G, IsUniqueInvolution (conjSub g F) r → conjSub g F = F := by
  subst hc
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  refine ⟨G2D4.center_modelUniv_g2d4_eq_bot hp2 ht' n' le_rfl, ?_⟩
  rcases ht' with rfl | rfl
  · have hn : n' = 0 := hadm.2.2.1
    subst hn
    exact G2D4Models.noTwins_g2 hp2 le_rfl
  · have hn : n' = 0 := hadm.2.2
    subst hn
    exact G2D4Models.noTwinsFund_of_td4_tag hp2 rfl hadm

end Model

section Corr

variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem exists_uniqueInvolution_of_corr3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    {D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)} {i : ι} {N : Subgroup G}
    {R : Subgroup (D.kind i).G} (hR : Corr3 Ω x D i N R) (hinj : Function.Injective (D.hom i))
    {w : G} (hw : IsClassicalMember3 N w) :
    ∃ (r : (D.kind i).G) (hwY : w ∈ locLayer Ω x), IsUniqueInvolution R r ∧
      D.hom i r = QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨w, hwY⟩ := by
  obtain ⟨hwY, hwm, hwsq, hw1, -⟩ := image_involution_facts3 hR.1 hw
  have hwm' := hwm
  rw [hR.2.2] at hwm'
  obtain ⟨r, hrR, hr⟩ := hwm'
  refine ⟨r, hwY, ⟨hrR, ?_, ?_, ?_⟩, hr⟩
  · intro h
    apply hw1
    rw [← hr, h, map_one]
  · apply hinj
    rw [map_mul, hr, hwsq, map_one]
  · intro y hy hy2
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      obtain ⟨e⟩ := nonempty_mulEquiv_locImg3 hΩ hex hR.1
      have hinv : ∀ s : SL(2, ZMod 3), s * s = 1 → s ≠ 1 → s = -1 := by decide +kernel
      have hya : D.hom i y ∈ locImg Ω x N := by
        rw [hR.2.2]
        exact Subgroup.mem_map_of_mem _ hy
      have h1 : e ⟨D.hom i y, hya⟩ = -1 := by
        refine hinv _ ?_ ?_
        · rw [← map_mul]
          have : (⟨D.hom i y, hya⟩ : locImg Ω x N) * ⟨D.hom i y, hya⟩ = 1 :=
            Subtype.ext (by
              show D.hom i y * D.hom i y = 1
              rw [← map_mul, hy2, map_one])
          rw [this, map_one]
        · intro h
          have : (⟨D.hom i y, hya⟩ : locImg Ω x N) = 1 := e.injective (h.trans e.map_one.symm)
          exact hy1 (hinj (by simpa using congrArg Subtype.val this))
      have h2 : e ⟨Gaps.locMk Ω x ⟨w, hwY⟩, hwm⟩ = -1 := by
        refine hinv _ ?_ ?_
        · rw [← map_mul]
          have : (⟨Gaps.locMk Ω x ⟨w, hwY⟩, hwm⟩ : locImg Ω x N) *
              ⟨Gaps.locMk Ω x ⟨w, hwY⟩, hwm⟩ = 1 := Subtype.ext hwsq
          rw [this, map_one]
        · intro h
          have : (⟨Gaps.locMk Ω x ⟨w, hwY⟩, hwm⟩ : locImg Ω x N) = 1 :=
            e.injective (h.trans e.map_one.symm)
          exact hw1 (congrArg Subtype.val this)
      have h3 : (⟨D.hom i y, hya⟩ : locImg Ω x N) = ⟨Gaps.locMk Ω x ⟨w, hwY⟩, hwm⟩ :=
        e.injective (h1.trans h2.symm)
      apply hinj
      rw [hr]
      exact congrArg Subtype.val h3

theorem false_of_g2d4_pair3 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} (hone : ∀ j : ι, j = i)
    {J J₂ : Subgroup G} {t : G} (hJ : J ∈ centralizingMembers Ω {x})
    (hJ₂ : J₂ ∈ centralizingMembers Ω {x}) (hJt : IsClassicalMember3 J t)
    (hJ₂t : IsClassicalMember3 J₂ t) (hne : J₂ ≠ J)
    (hxo : ∃ y ∈ locLayer Ω x, conjSub y J = J₂) {t' : StatedLieTag} {n' : ℕ}
    (hadm : StatedLieAdmissible t' n' 3 1) (hk : D.kind i = CompData.model t' n')
    (ht' : t' = .G2 ∨ t' = .trialityD4) : False := by
  classical
  obtain ⟨hcenter, hnt⟩ := center_and_noTwins_of_kind ht' hadm hk
  have hsurj := Q3TLK.hom_surjective_of_unique D i hone
  have hinj : Function.Injective (D.hom i) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact (D.ker_le_center i).trans hcenter.le
  obtain ⟨R, hR⟩ := exists_corr_left3 hΩ hex hP1 hO3 D (mem_comp_of_card_one3 D i hone hJ)
  obtain ⟨r, hwY, hru, hr⟩ := exists_uniqueInvolution_of_corr3 hΩ hex hR hinj hJt
  obtain ⟨y, hyY, hyJ⟩ := hxo
  obtain ⟨g, hg⟩ := hsurj (Gaps.locMk Ω x ⟨y, hyY⟩)
  have hyt : y * t * y⁻¹ = t := by
    have h1 : IsClassicalMember3 (conjSub y J) (y * t * y⁻¹) := hJt.conj y
    rw [hyJ] at h1
    exact involution_unique3 h1 hJ₂t
  have hgr : g * r * g⁻¹ = r := by
    apply hinj
    rw [map_mul, map_mul, map_inv, hg, hr, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show y * t * y⁻¹ = t
    exact hyt
  have hconj : IsUniqueInvolution (conjSub g R) r := by
    have := hru.conj g
    rwa [hgr] at this
  have hgR : conjSub g R = R := hnt R hR.2.1 r hru g hconj
  have himg : locImg Ω x (conjSub y J) = (conjSub g R).map (D.hom i) := by
    rw [Gaps.locImg_conjSub_layer J ⟨y, hyY⟩, hR.2.2, show Gaps.locMk Ω x ⟨y, hyY⟩ = D.hom i g from
      hg.symm]
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext a
    simp
  apply hne
  refine locImg_injOn3 hΩ hex hP1 hO3 hJ₂ hJ ?_
  rw [← hyJ, himg, hgR, hR.2.2]

end Corr

section Kind

theorem twinYKind3_sp2 : TwinYKind3On TwinRowSp2 := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e hP1u hO3u ι _ D hcard i
  obtain ⟨rfl, rfl⟩ := hP
  classical
  obtain ⟨J, t, A, hJ, hJK, hJT, hJu, hJ₂u, -⟩ := rank_setup3_sp2 h3 hnab hR hshape hT clsT e
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, isSubnormal_le hR.cls.subnormal⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨hft0, hG20, hD40, hE60, -⟩ := twinRow_tag_facts3 hrow
  have hCF := ModelFacts.commutingFundamentalGeneration3_nonTwisted hG20 hD40 hE60 hft0
    (twinRow_admissible3 hrow)
  have hxo : ∃ y ∈ locLayer (conjClass3 K) e.u, conjSub y J = A.J₂ :=
    c.xOrbit hCF e hKz hT.mem hT.ne.symm hKiso hTiso hJ hJK hJT A.hJ₂z A.hJ₂K A.hJ₂T
  have hJJ₂ : Commutes J A.J₂ := A.hJiso A.J₂ A.hJ₂t A.hJ₂J
  have hJJ₂ne : J ≠ A.J₂ := A.hJ₂J.symm
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hone : ∀ j : ι, j = i := fun j => (hx₀ j).trans (hx₀ i).symm
  have h₁ := mem_comp_of_card_one3 D i hone hJu
  have h₂ := mem_comp_of_card_one3 D i hone hJ₂u
  rcases D.valid i with ⟨t', n', hft, hadm, hk⟩ | hk | hk
  · have hG2 : t' ≠ .G2 := fun h =>
      false_of_g2d4_pair3 hΩ hex hP1u hO3u D hone hJu hJ₂u A.clsJ A.clsJ₂ A.hJ₂J hxo hadm hk
        (Or.inl h)
    have hD4 : t' ≠ .trialityD4 := fun h =>
      false_of_g2d4_pair3 hΩ hex hP1u hO3u D hone hJu hJ₂u A.clsJ A.clsJ₂ A.hJ₂J hxo hadm hk
        (Or.inr h)
    have hnA1 := not_psl_two_of_admissible3 hadm
    have hsc := EX.singleClass_of_kind hk hft hadm hG2 hD4
    have hpc := EX.powCop3_of_kind hk hft hadm hG2 hD4
    obtain ⟨F, hF, hFinj, hFcomm, hFtwin⟩ := EX.twinFamily_of_family3 (ι' := Fin 2) hΩ hex hP1u
      hO3u D hsc hpc ![J, A.J₂]
      (fun k => by fin_cases k; exacts [h₁, h₂])
      (by
        intro a b hab
        fin_cases a <;> fin_cases b
        · rfl
        · exact absurd hab hJJ₂ne
        · exact absurd hab.symm hJJ₂ne
        · rfl)
      (by
        intro k l hkl
        fin_cases k <;> fin_cases l
        · exact absurd rfl hkl
        · exact hJJ₂
        · exact hJJ₂.symm
        · exact absurd rfl hkl)
      (by
        intro M hM k l
        have key := A.nbhd_iff hM
        fin_cases k <;> fin_cases l
        · exact Iff.rfl
        · exact key
        · exact key.symm
        · exact Iff.rfl)
    have hmtc := EX.modelTwinClass_of_compData hk F hF hFinj hFcomm hFtwin
    have hmf := EX.mfTwin3 t' n' 2 hft hG2 hD4 hadm hnA1 le_rfl hmtc
    refine ⟨t', n', hk, ?_⟩
    rcases hmf with h | ⟨rfl, rfl, -⟩
    · exact twinRow_of_shapeTable_two h
    · exact Or.inl ⟨rfl, rfl, le_rfl⟩
  · exact absurd (eq_of_mem_compMembers_a13 hΩ hex hP1u hO3u (D := D) (i := i) hk h₁ h₂)
      hJJ₂ne
  · exact absurd hJJ₂ (not_commutes_of_m11_comp3 hΩ hex hP1u hO3u hk h₁ h₂)

end Kind

end CFSG.ClassicalInvolution.Q3.Q3TIY

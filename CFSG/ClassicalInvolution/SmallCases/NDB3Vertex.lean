module

public import CFSG.ClassicalInvolution.SmallCases.NDB2Vertex
public import CFSG.ClassicalInvolution.SmallCases.NDB3Model

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ComponentClassification
open CFSG.Assembly.LowTwoRank

namespace Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem mem_modOdd_of_commutes {A : Subgroup G} {z : G} (hA : CFSG.Open.IsElemAbelian 2 A)
    (hzA : z ∈ A) (hz1 : z ≠ 1) (hAY : A ≤ exactLayer Ω z) {e : G} (heA : e ∈ A) (he1 : e ≠ 1)
    (hez : e ≠ z) {q : OddQuot z} (hq : q ∈ memberJoin (exactFamily Ω z) z)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨e, he⟩ * q = q * oddQuotMk z ⟨e, he⟩) :
    q ∈ modOdd z (⨆ F ∈ CFSG.Open.signalizerFunctorEk 2 2 A,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z)) := by
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hAC : A ≤ Subgroup.centralizer ({z} : Set G) := Lemma52Proof.le_centralizer_of_mem hA hzA
  have hsqA : ∀ x ∈ A, x * x = 1 := fun x hx => by
    have := hA.2 x hx
    rwa [pow_two] at this
  have hzz : z * z = 1 := hsqA z hzA
  have hze : z * e = e * z := (Subgroup.mem_centralizer_singleton_iff.mp (hAC heA)).symm
  set F : Subgroup G := Subgroup.closure ({z, e} : Set G) with hF
  have hFA : F ≤ A := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzA
    · exact heA
  have hcard : Nat.card F = 4 :=
    card_closure_pair_eq_four hzz (hsqA e heA) hz1 he1 (fun h => hez h.symm) hze
  have hFE : F ∈ CFSG.Open.signalizerFunctorEk 2 2 A := ⟨hFA, by rw [hcard]; norm_num⟩
  have hFY : F ≤ exactLayer Ω z := hFA.trans hAY
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => hsqA x (hFA hx)
  have hcent : ∀ (x : G) (_ : x ∈ F) (hC : x ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨x, hC⟩ * q = q * oddQuotMk z ⟨x, hC⟩ := by
    refine ChainFrame.commutes_of_closure (oddQuotMk z) q (S := ({z, e} : Set G)) ?_ ?_
    · rintro s (rfl | rfl)
      · exact hzC
      · exact hAC heA
    · rintro s (rfl | rfl) hs
      · exact oddQuotMk_central hs q
      · exact hcomm hs
  obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (a := z) hF2 hFY hq hcent
  have hle : (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) ≤
      ⨆ F ∈ CFSG.Open.signalizerFunctorEk 2 2 A,
        (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) :=
    le_iSup₂ (f := fun F (_ : F ∈ CFSG.Open.signalizerFunctorEk 2 2 A) =>
      Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) F hFE
  exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hle ⟨hyF, hyY⟩), hyq⟩

theorem le_oddCore_sup_of_components (hΩ : ConjInvariant Ω) {a : G}
    (D : LocalLieSystemAt p f (exactFamily Ω a) a) {H : Subgroup G} (hHY : H ≤ exactLayer Ω a)
    (hψ : ∀ (j : Fin D.card) (k : (compModel D j).K),
      secComponentHom (normalizesLayer_exactFamily hΩ) D j k ∈ modOdd a H) :
    exactLayer Ω a ≤ oddCoreIn (exactLayer Ω a) ⊔ H := by
  have hN := normalizesLayer_exactFamily (c := a) hΩ
  have hgen : ∀ x : ↥(exactLayer Ω a) ⧸ CFSG.Open.classicalInvolutionOddCore ↥(exactLayer Ω a),
      sectionQuotientHom hN x ∈ modOdd a H := by
    have hle : (⨆ i, (D.hom i).range) ≤ (modOdd a H).comap (sectionQuotientHom hN) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨k, rfl⟩
      exact hψ j k
    intro x
    exact hle (by rw [D.generate]; exact Subgroup.mem_top x)
  intro y hy
  obtain ⟨c, hcH, hc⟩ := hgen (QuotientGroup.mk' _ ⟨y, hy⟩)
  have hcH' : (c : G) ∈ H := Subgroup.mem_subgroupOf.mp hcH
  have hcY : (c : G) ∈ exactLayer Ω a := hHY hcH'
  have heq : oddQuotMk a ⟨y, exactLayer_le_centralizer Ω a hy⟩ =
      oddQuotMk a ⟨c, exactLayer_le_centralizer Ω a hcY⟩ := by
    have h1 : sectionQuotientHom hN (QuotientGroup.mk' _ ⟨y, hy⟩) =
        oddQuotMk a ⟨y, exactLayer_le_centralizer Ω a hy⟩ := rfl
    rw [← h1, ← hc]
  have hker : (⟨y, hy⟩ : ↥(exactLayer Ω a)) * ⟨c, hcY⟩⁻¹ ∈
      (layerToOddQuot (exactFamily Ω a) a).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    exact mul_inv_eq_one.mpr heq
  rw [ker_layerToOddQuot_of_normalizes hN] at hker
  have hmem := mem_oddCoreIn_of_mem_classicalInvolutionOddCore hker
  have hmem' : y * (c : G)⁻¹ ∈ oddCoreIn (exactLayer Ω a) := by
    have : ((⟨y, hy⟩ * ⟨c, hcY⟩⁻¹ : ↥(exactLayer Ω a)) : G) = y * (c : G)⁻¹ := by simp
    rwa [this] at hmem
  have e : y = (y * (c : G)⁻¹) * c := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hmem') (Subgroup.mem_sup_right hcH')

theorem s_not_mem_closure {z₁ z₂ t₁ t₂ t₃ : G} (hz₁ : z₁ * z₁ = 1) (hz₂ : z₂ * z₂ = 1)
    (hc : z₁ * z₂ = z₂ * z₁) (hcard : Nat.card (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) = 8) :
    t₁ * t₂ * t₃ ∉ Subgroup.closure ({z₁, z₂} : Set G) := by
  intro hs
  have hle : TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ ≤ Subgroup.closure ({z₁, z₂} : Set G) := by
    show Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G) ≤ _
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    · exact hs
  have h1 := Subgroup.card_le_of_le hle
  have h2 := Theorem5.card_closure_pair_le_four hz₁ hz₂ hc
  omega

end Vertex

section Generation

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem generation_axis_vertex {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ : G} (hK₁ : K₁ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hsh : PSpShape p f Ω z₁) (hK₂ : K₂ ∈ tqMembers Ω z₁)
    (hz₂ : IsClassicalMember p f K₂ z₂) (hK₃ : K₃ ∈ tqMembers Ω z₁)
    (hz₃ : IsClassicalMember p f K₃ z₃) (hprod : z₁ * z₂ = z₃) (ht₁ : t₁ ∈ K₁)
    (ht₂ : t₂ ∈ K₂) (ht₃ : t₃ ∈ K₃) (hsq₁ : t₁ * t₁ = z₁) (hsq₂ : t₂ * t₂ = z₂)
    (hsq₃ : t₃ * t₃ = z₃) (c₁₂ : t₁ * t₂ = t₂ * t₁) (c₁₃ : t₁ * t₃ = t₃ * t₁)
    (helem : CFSG.Open.IsElemAbelian 2 (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃))
    (hcard : Nat.card (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) = 8) :
    CentralizerGenerationStar Ω (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) z₁ := by
  classical
  have hz₁c := isCentralInvolution_of_isClassicalMember hz₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hz₂
  have hz₃c := isCentralInvolution_of_isClassicalMember hz₃
  have hc2 := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz₁c.sq
  have hz₁B : z₁ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₂B : z₂ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hsB : t₁ * t₂ * t₃ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have hBC : TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ ≤ Subgroup.centralizer ({z₁} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem helem hz₁B
  have hz₂z₁ : z₂ ≠ z₁ := fun h => hz₃c.ne_one (by rw [← hprod, h, hz₁c.sq])
  have hzC : z₁ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hz₂C : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) := hBC hz₂B
  have hz₃C : z₃ ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [← hprod]
    exact Subgroup.mul_mem _ hzC hz₂C
  have hcomm₁ : ∀ {u : G}, t₁ * u = u * t₁ → u ∈ Subgroup.centralizer ({z₁} : Set G) :=
    fun h => Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← hsq₁]; exact (Axis.comm_sq h).symm)
  have ht₁C : t₁ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ rfl
  have ht₂C : t₂ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ c₁₂
  have ht₃C : t₃ ∈ Subgroup.centralizer ({z₁} : Set G) := hcomm₁ c₁₃
  have hzz : z₁ * z₂ = z₂ * z₁ :=
    (Subgroup.mem_centralizer_singleton_iff.mp hz₂C).symm
  have hsZ := Vertex.s_not_mem_closure (t₁ := t₁) (t₂ := t₂) (t₃ := t₃) hz₁c.sq hz₂c.sq hzz hcard
  obtain ⟨D, i₀, i₁, hcard2, hne, htag₁, hrank₁, hKbar, hinj, hcomm01, hcomp⟩ :=
    exists_pspVertex hΩ hp hq hK₁ hz₁ hsh
  set ψ₀ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₀ with hψ₀
  set ψ₁ := secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D i₁ with hψ₁
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz₁
  let C : XCtx p f Ω z₁ :=
    { K := K₁, hK := hK₁, hKz := hKz, hΩ := hΩ, hp := hp, hq := hq, D := D }
  have hz₁sq : oddQuotMk z₁ ⟨z₁, hzC⟩ * oddQuotMk z₁ ⟨z₁, hzC⟩ = 1 := by
    rw [← map_mul]
    exact (congrArg (oddQuotMk z₁) (Subtype.ext hz₁c.sq : (⟨z₁, hzC⟩ :
      ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨z₁, hzC⟩ = 1)).trans (map_one _)
  have he₃ : (⟨z₃, hz₃C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = ⟨z₁, hzC⟩ * ⟨z₂, hz₂C⟩ :=
    Subtype.ext hprod.symm
  have hz₂1 : oddQuotMk z₁ ⟨z₂, hz₂C⟩ ≠ 1 := fun h =>
    hz₂c.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₂c.sq) h))
  have hz₁1 : oddQuotMk z₁ ⟨z₁, hzC⟩ ≠ 1 := fun h =>
    hz₁c.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₁c.sq) h))
  have hne₂ : oddQuotMk z₁ ⟨z₂, hz₂C⟩ ≠ oddQuotMk z₁ ⟨z₁, hzC⟩ := by
    intro h
    apply hz₃c.ne_one
    have h1 : oddQuotMk z₁ ⟨z₃, hz₃C⟩ = 1 := by rw [he₃, map_mul, h, hz₁sq]
    exact congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₃c.sq) h1)
  have hne₃ : oddQuotMk z₁ ⟨z₃, hz₃C⟩ ≠ oddQuotMk z₁ ⟨z₁, hzC⟩ := by
    intro h
    apply hz₂c.ne_one
    have h1 : oddQuotMk z₁ ⟨z₂, hz₂C⟩ = 1 := by
      have e : (⟨z₂, hz₂C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = ⟨z₁, hzC⟩ * ⟨z₃, hz₃C⟩ :=
        Subtype.ext (show z₂ = z₁ * z₃ by rw [← hprod, ← mul_assoc, hz₁c.sq, one_mul])
      rw [e, map_mul, h, hz₁sq]
    exact congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₂c.sq) h1)
  obtain ⟨R₂, hR₂, hR₂img⟩ := hcomp K₂ hK₂ z₂ hz₂ hz₂C hne₂
  obtain ⟨R₃, hR₃, hR₃img⟩ := hcomp K₃ hK₃ z₃ hz₃ hz₃C hne₃
  have h4 : ∀ {t z : G}, t * t = z → z * z = 1 → t ^ 4 = 1 := fun ht hz => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ht, hz]
  have ht₂E : t₂ ∈ exactCore z₁ K₂ := Vertex.mem_exactCore_of_isPGroup hΩ hp hq hc2 hK₂ ht₂
    (Subgroup.mem_centralizer_singleton_iff.mp ht₂C)
    (Vertex.isPGroup_zpowers_of_pow_four (h4 hsq₂ hz₂c.sq))
  have ht₃E : t₃ ∈ exactCore z₁ K₃ := Vertex.mem_exactCore_of_isPGroup hΩ hp hq hc2 hK₃ ht₃
    (Subgroup.mem_centralizer_singleton_iff.mp ht₃C)
    (Vertex.isPGroup_zpowers_of_pow_four (h4 hsq₃ hz₃c.sq))
  have hK₁tq : K₁ ∈ tqMembers Ω z₁ := mem_tqMembers_of_isClassicalMember hK₁ hz₁
  have ht₁E : t₁ ∈ exactCore z₁ K₁ := Vertex.mem_exactCore_of_isPGroup hΩ hp hq hc2 hK₁tq ht₁
    (Subgroup.mem_centralizer_singleton_iff.mp ht₁C)
    (Vertex.isPGroup_zpowers_of_pow_four (h4 hsq₁ hz₁c.sq))
  obtain ⟨r₂, hr₂R, hr₂⟩ : oddQuotMk z₁ ⟨t₂, ht₂C⟩ ∈ R₂.map ψ₁ := by
    rw [hR₂img]
    exact oddQuotMk_mem_modOdd ht₂E ht₂C
  obtain ⟨r₃, hr₃R, hr₃⟩ : oddQuotMk z₁ ⟨t₃, ht₃C⟩ ∈ R₃.map ψ₁ := by
    rw [hR₃img]
    exact oddQuotMk_mem_modOdd ht₃E ht₃C
  have hx₂ : ψ₁ (r₂ * r₂) = oddQuotMk z₁ ⟨z₂, hz₂C⟩ := by
    rw [map_mul, hr₂, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext hsq₂)
  have hx₃ : ψ₁ (r₃ * r₃) = oddQuotMk z₁ ⟨z₃, hz₃C⟩ := by
    rw [map_mul, hr₃, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext hsq₃)
  have hcentral : ∀ {w : OddQuot z₁}, (∀ y : OddQuot z₁, w * y = y * w) →
      ∀ {c : (compModel D i₁).K}, ψ₁ c = w → c ∈ Subgroup.center (compModel D i₁).K := by
    intro w hw c hc
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul, hc]
    exact (hw (ψ₁ g)).symm
  have hcentR : ∀ {N : Subgroup G} {u : G} (hu : IsClassicalMember p f N u)
      (huC : u ∈ Subgroup.centralizer ({z₁} : Set G)) {R : Subgroup (compModel D i₁).K},
      R.map ψ₁ = modOdd z₁ (exactCore z₁ N) → ∀ {x : (compModel D i₁).K},
      ψ₁ x = oddQuotMk z₁ ⟨u, huC⟩ → ∀ r ∈ R, x * r = r * x := by
    intro N u hu huC R hR x hx r hr
    apply hinj
    have hmem : ψ₁ r ∈ modOdd z₁ (exactCore z₁ N) := hR ▸ ⟨r, hr, rfl⟩
    obtain ⟨k, hk, hkr⟩ := hmem
    rw [map_mul, map_mul, hx, ← hkr, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext
      ((isCentralInvolution_of_isClassicalMember hu).central _ (exactCore_le_left z₁ N hk)))
  have hR₂₃ : R₂ ≠ R₃ := by
    intro h
    have hU := C.isUniqueInvolution_modOdd hK₂ hz₂
    have hz₃mem : oddQuotMk z₁ ⟨z₃, hz₃C⟩ ∈ modOdd z₁ (exactCore z₁ K₂) := by
      rw [← hR₂img, h, hR₃img]
      exact oddQuotMk_mem_modOdd (mem_exactCore hz₃ hc2 hK₃.2) hz₃C
    have hz₃sq : oddQuotMk z₁ ⟨z₃, hz₃C⟩ * oddQuotMk z₁ ⟨z₃, hz₃C⟩ = 1 := by
      rw [← map_mul]
      exact (congrArg (oddQuotMk z₁) (Subtype.ext hz₃c.sq : (⟨z₃, hz₃C⟩ :
        ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨z₃, hz₃C⟩ = 1)).trans (map_one _)
    have hz₃1 : oddQuotMk z₁ ⟨z₃, hz₃C⟩ ≠ 1 := fun h' =>
      hz₃c.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₃c.sq) h'))
    have h23 := (hU.unique _ hz₃mem hz₃sq).resolve_left hz₃1
    apply hz₁1
    have h1 : oddQuotMk z₁ ⟨z₁, hzC⟩ * oddQuotMk z₁ ⟨z₂, hz₂C⟩ = oddQuotMk z₁ ⟨z₂, hz₂C⟩ := by
      rw [← map_mul, ← he₃]
      exact h23
    calc oddQuotMk z₁ ⟨z₁, hzC⟩
        = oddQuotMk z₁ ⟨z₁, hzC⟩ * oddQuotMk z₁ ⟨z₂, hz₂C⟩ * (oddQuotMk z₁ ⟨z₂, hz₂C⟩)⁻¹ := by
          group
      _ = 1 := by rw [h1, mul_inv_cancel]
  have hsame : r₂ * r₂ * (r₃ * r₃)⁻¹ ∈ Subgroup.center (compModel D i₁).K := by
    refine hcentral (w := (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹) (fun y => ?_) ?_
    · have := oddQuotMk_central hzC y
      calc (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ * y
          = (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ * (y * oddQuotMk z₁ ⟨z₁, hzC⟩) *
            (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ := by group
        _ = y * (oddQuotMk z₁ ⟨z₁, hzC⟩)⁻¹ := by rw [← this]; group
    · rw [map_mul, map_inv, hx₂, hx₃, he₃, map_mul]
      group
  have hcen1 : ∀ {a : (compModel D i₁).K}, a * a * (a * a)⁻¹ ∈
      Subgroup.center (compModel D i₁).K := fun {a} => by
    rw [mul_inv_cancel]
    exact Subgroup.one_mem _
  have hx1 : r₂ * r₂ ≠ 1 := fun h => hz₂1 (by rw [← hx₂, h, map_one])
  have hx'1 : r₃ * r₃ ≠ 1 := fun h => hz₃c.ne_one (congrArg Subtype.val
    (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₃c.sq) (by rw [← hx₃, h, map_one])))
  have h5 : 5 ≤ p ^ D.exp i₁ := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · rw [h]
      exact hq
    · rw [htag₁] at h
      cases h
  have hgen := sp4Gen_model hp (D.tag i₁) (D.rank i₁) (D.exp i₁) htag₁ hrank₁ (D.admissible i₁)
    h5 hR₂ hR₃ hR₂₃ (R₂.mul_mem hr₂R hr₂R) (hcentR hz₂ hz₂C hR₂img hx₂) hx1
    (R₃.mul_mem hr₃R hr₃R) (hcentR hz₃ hz₃C hR₃img hx₃) hx'1 hsame hr₂R hr₃R hcen1 hcen1
  have hAY : TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ ≤ exactLayer Ω z₁ := by
    show Subgroup.closure ({z₁, z₂, t₁ * t₂ * t₃} : Set G) ≤ _
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact exactCore_le_exactLayer hK₁tq (mem_exactCore hz₁ hc2 hK₁tq.2)
    · exact exactCore_le_exactLayer hK₂ (mem_exactCore hz₂ hc2 hK₂.2)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (exactCore_le_exactLayer hK₁tq ht₁E)
        (exactCore_le_exactLayer hK₂ ht₂E)) (exactCore_le_exactLayer hK₃ ht₃E)
  have hs1 : t₁ * t₂ * t₃ ≠ 1 := fun h => hsZ (h ▸ Subgroup.one_mem _)
  have hsz : t₁ * t₂ * t₃ ≠ z₁ := fun h => hsZ (h ▸ Subgroup.subset_closure (Set.mem_insert _ _))
  have hz₂s1 : z₂ * (t₁ * t₂ * t₃) ≠ 1 := fun h => hsZ (by
    rw [show t₁ * t₂ * t₃ = z₂ by rw [← mul_left_cancel_iff (a := z₂), h, hz₂c.sq]]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  have hz₂sz : z₂ * (t₁ * t₂ * t₃) ≠ z₁ := fun h => hsZ (by
    rw [show t₁ * t₂ * t₃ = z₂ * z₁ by rw [← h, ← mul_assoc, hz₂c.sq, one_mul]]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      (Subgroup.subset_closure (Set.mem_insert _ _)))
  have hts : t₂ * t₃ ∈ Subgroup.centralizer ({z₁} : Set G) := Subgroup.mul_mem _ ht₂C ht₃C
  have ht₁ψ : oddQuotMk z₁ ⟨t₁, ht₁C⟩ ∈ ψ₀.range := by
    rw [← hKbar]
    exact oddQuotMk_mem_modOdd ht₁ ht₁C
  have hsbar : ∀ hs : t₁ * t₂ * t₃ ∈ Subgroup.centralizer ({z₁} : Set G),
      oddQuotMk z₁ ⟨t₁ * t₂ * t₃, hs⟩ = oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ (r₂ * r₃) := by
    intro hs
    rw [map_mul, hr₂, hr₃, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk z₁) (Subtype.ext (mul_assoc t₁ t₂ t₃))
  have hmemJ : ∀ (j : Fin D.card) (k : (compModel D j).K),
      secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j k ∈
        memberJoin (exactFamily Ω z₁) z₁ := fun j k => C.psi_mem_memberJoin j k
  have hlift := fun {e : G} (heA : e ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) (he1 : e ≠ 1)
      (hez : e ≠ z₁) {q : OddQuot z₁} (hq : q ∈ memberJoin (exactFamily Ω z₁) z₁)
      (hc : ∀ he : e ∈ Subgroup.centralizer ({z₁} : Set G),
        oddQuotMk z₁ ⟨e, he⟩ * q = q * oddQuotMk z₁ ⟨e, he⟩) =>
    Vertex.mem_modOdd_of_commutes (Ω := Ω) helem hz₁B hz₁c.ne_one hAY heA he1 hez hq hc
  refine Vertex.le_oddCore_sup_of_components hΩ.conjInvariant D
    (iSup₂_le fun F _ => inf_le_right) fun j k => ?_
  rcases Seed.eq_or_eq_of_card_two hcard2 hne j with rfl | rfl
  · exact hlift hz₂B hz₂c.ne_one hz₂z₁ (hmemJ _ k) fun he =>
      (hcomm01 _ ⟨k, rfl⟩ _ (hx₂ ▸ ⟨r₂ * r₂, rfl⟩)).symm
  · have hP : (⊤ : Subgroup (compModel D j).K) ≤
        (modOdd z₁ (⨆ F ∈ CFSG.Open.signalizerFunctorEk 2 2 (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃),
          (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z₁))).comap ψ₁ := by
      rw [← hgen]
      refine sup_le (sup_le ?_ ?_) ?_ <;> intro r hr <;>
        have hr' := Subgroup.mem_centralizer_singleton_iff.mp hr <;>
        have hq := hmemJ _ r
      · refine hlift hz₂B hz₂c.ne_one hz₂z₁ hq fun he => ?_
        rw [← hx₂, ← map_mul, ← map_mul, hr']
      · refine hlift hsB hs1 hsz hq fun he => ?_
        have hrw : ψ₁ r * ψ₁ (r₂ * r₃) = ψ₁ (r₂ * r₃) * ψ₁ r := by
          rw [← map_mul, ← map_mul, hr']
        rw [hsbar he]
        calc oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ (r₂ * r₃) * ψ₁ r
            = oddQuotMk z₁ ⟨t₁, ht₁C⟩ * (ψ₁ r * ψ₁ (r₂ * r₃)) := by rw [mul_assoc, hrw]
          _ = ψ₁ r * (oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ (r₂ * r₃)) := by
            rw [← mul_assoc, hcomm01 _ ht₁ψ _ ⟨r, rfl⟩, mul_assoc]
      · refine hlift (Subgroup.mul_mem _ hz₂B hsB) hz₂s1 hz₂sz hq fun he => ?_
        have hrw : ψ₁ r * ψ₁ (r₂ * r₂ * (r₂ * r₃)) = ψ₁ (r₂ * r₂ * (r₂ * r₃)) * ψ₁ r := by
          rw [← map_mul, ← map_mul, hr']
        have e : oddQuotMk z₁ ⟨z₂ * (t₁ * t₂ * t₃), he⟩ =
            oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ (r₂ * r₂ * (r₂ * r₃)) := by
          have e1 : (⟨z₂ * (t₁ * t₂ * t₃), he⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) =
              ⟨z₂, hz₂C⟩ * ⟨t₁ * t₂ * t₃, hBC hsB⟩ := rfl
          rw [e1, map_mul, hsbar, map_mul ψ₁ (r₂ * r₂), hx₂, ← mul_assoc, ← mul_assoc]
          congr 1
          exact (hcomm01 _ ht₁ψ _ (hx₂ ▸ ⟨r₂ * r₂, rfl⟩)).symm
        rw [e]
        calc oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ (r₂ * r₂ * (r₂ * r₃)) * ψ₁ r
            = oddQuotMk z₁ ⟨t₁, ht₁C⟩ * (ψ₁ r * ψ₁ (r₂ * r₂ * (r₂ * r₃))) := by
              rw [mul_assoc, hrw]
          _ = ψ₁ r * (oddQuotMk z₁ ⟨t₁, ht₁C⟩ * ψ₁ (r₂ * r₂ * (r₂ * r₃))) := by
            rw [← mul_assoc, hcomm01 _ ht₁ψ _ ⟨r, rfl⟩, mul_assoc]
    exact hP (Subgroup.mem_top k)

end Generation

section Link

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem link_axis_vertex {Ω : Set (Subgroup G)} (hΩ : HypOmegaMod p f Ω) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ t₁ t₂ t₃ : G} (hK₁ : K₁ ∈ Ω)
    (hz₁ : IsClassicalMember p f K₁ z₁) (hsh : PSpShape p f Ω z₁) (hK₂ : K₂ ∈ tqMembers Ω z₁)
    (hz₂ : IsClassicalMember p f K₂ z₂) (hz₃ : IsClassicalMember p f K₃ z₃)
    (hprod : z₁ * z₂ = z₃) {S : Set (Subgroup G)} (h₁S : K₁ ∈ S) (h₂S : K₂ ∈ S) :
    InvolutionLinkStar p f Ω (TypeCSetup.axis z₁ z₂ t₁ t₂ t₃) S z₁ := by
  have hz₁c := isCentralInvolution_of_isClassicalMember hz₁
  have hz₂c := isCentralInvolution_of_isClassicalMember hz₂
  have hz₃c := isCentralInvolution_of_isClassicalMember hz₃
  have hc2 := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz₁c.sq
  have hz₁B : z₁ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hz₂B : z₂ ∈ TypeCSetup.axis z₁ z₂ t₁ t₂ t₃ :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hzC : z₁ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hK₁tq : K₁ ∈ tqMembers Ω z₁ := mem_tqMembers_of_isClassicalMember hK₁ hz₁
  obtain ⟨D, i₀, i₁, hcard2, hne, htag₁, hrank₁, hKbar, hinj, hcomm01, hcomp⟩ :=
    exists_pspVertex hΩ hp hq hK₁ hz₁ hsh
  have hKz := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp hq hz₁
  let C : XCtx p f Ω z₁ :=
    { K := K₁, hK := hK₁, hKz := hKz, hΩ := hΩ, hp := hp, hq := hq, D := D }
  have hz₁Y : z₁ ∈ exactLayer Ω z₁ :=
    exactCore_le_exactLayer hK₁tq (mem_exactCore hz₁ hc2 hK₁tq.2)
  have hz₂C : z₂ ∈ Subgroup.centralizer ({z₁} : Set G) := C.involution_mem_centralizer hK₂ hz₂
  have hz₂Y : z₂ ∈ exactLayer Ω z₁ :=
    exactCore_le_exactLayer hK₂ (C.involution_mem_exactCore hK₂ hz₂)
  have hz₃C : z₃ ∈ Subgroup.centralizer ({z₁} : Set G) := by
    rw [← hprod]
    exact Subgroup.mul_mem _ hzC hz₂C
  have hz₁sq : oddQuotMk z₁ ⟨z₁, hzC⟩ * oddQuotMk z₁ ⟨z₁, hzC⟩ = 1 := by
    rw [← map_mul]
    exact (congrArg (oddQuotMk z₁) (Subtype.ext hz₁c.sq : (⟨z₁, hzC⟩ :
      ↥(Subgroup.centralizer ({z₁} : Set G))) * ⟨z₁, hzC⟩ = 1)).trans (map_one _)
  have hne₂ : oddQuotMk z₁ ⟨z₂, hz₂C⟩ ≠ oddQuotMk z₁ ⟨z₁, hzC⟩ := by
    intro h
    apply hz₃c.ne_one
    have e : (⟨z₃, hz₃C⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) = ⟨z₁, hzC⟩ * ⟨z₂, hz₂C⟩ :=
      Subtype.ext hprod.symm
    have h1 : oddQuotMk z₁ ⟨z₃, hz₃C⟩ = 1 := by rw [e, map_mul, h, hz₁sq]
    exact congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hz₃c.sq) h1)
  obtain ⟨R₂, hR₂, hR₂img⟩ := hcomp K₂ hK₂ z₂ hz₂ hz₂C hne₂
  intro N hN w hw hdisj
  have key : ActsTrivOnQuot N z₁ ∨ w = z₁ := by
    rcases hdisj with h | ⟨L', hL', hL'z, hL'w⟩
    · exact Or.inl h
    · rcases actsTriv_or_eq hp hq hΩ hN hL' hw hL'z hL'w with h | h
      · exact Or.inr h
      · exact Or.inl h
  rcases key with htq | hwz
  swap
  · exact ⟨K₁, h₁S, z₁, hz₁B, hz₁, 1, Subgroup.one_mem _, by rw [hwz]; group⟩
  have hNtq : N ∈ tqMembers Ω z₁ := ⟨hN, mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩
  have hwc := isCentralInvolution_of_isClassicalMember hw
  have hwC := C.involution_mem_centralizer hNtq hw
  have hwY : w ∈ exactLayer Ω z₁ :=
    exactCore_le_exactLayer hNtq (C.involution_mem_exactCore hNtq hw)
  by_cases hwz : oddQuotMk z₁ ⟨w, hwC⟩ = oddQuotMk z₁ ⟨z₁, hzC⟩
  · obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY hz₁Y hwc.sq hz₁c.sq hwz
    exact ⟨K₁, h₁S, z₁, hz₁B, hz₁, o, oddCoreIn_le _ ho, hwo⟩
  obtain ⟨R, hR, hRimg⟩ := hcomp N hNtq w hw hwC hwz
  obtain ⟨g, hg⟩ := C.single i₁ (by rw [htag₁]; decide) (by rw [htag₁]; decide) R₂ hR₂ R hR
  obtain ⟨x, hxR, hx⟩ : oddQuotMk z₁ ⟨z₂, hz₂C⟩ ∈ R₂.map (C.psi i₁) := by
    show oddQuotMk z₁ ⟨z₂, hz₂C⟩ ∈ R₂.map (secComponentHom
      (normalizesLayer_exactFamily hΩ.conjInvariant) D i₁)
    rw [hR₂img]
    exact oddQuotMk_mem_modOdd (mem_exactCore hz₂ hc2 hK₂.2) hz₂C
  obtain ⟨y, hy, hyψ⟩ := C.exists_lift_psi i₁ g
  have hyC := exactLayer_le_centralizer Ω z₁ hy
  have hconjC : y * z₂ * y⁻¹ ∈ Subgroup.centralizer ({z₁} : Set G) :=
    mul_mem (mul_mem hyC hz₂C) (inv_mem hyC)
  have hconjY : y * z₂ * y⁻¹ ∈ exactLayer Ω z₁ := mul_mem (mul_mem hy hz₂Y) (inv_mem hy)
  have hbar : oddQuotMk z₁ ⟨y * z₂ * y⁻¹, hconjC⟩ = C.psi i₁ (g * x * g⁻¹) := by
    have : (⟨y * z₂ * y⁻¹, hconjC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) =
        ⟨y, hyC⟩ * ⟨z₂, hz₂C⟩ * ⟨y, hyC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hyψ, ← hx, map_mul, map_mul, map_inv]
  have hU := C.isUniqueInvolution_modOdd hNtq hw
  have hmem : C.psi i₁ (g * x * g⁻¹) ∈ modOdd z₁ (exactCore z₁ N) := by
    show C.psi i₁ (g * x * g⁻¹) ∈ modOdd z₁ (exactCore z₁ N)
    rw [← hRimg, hg]
    exact ⟨g * x * g⁻¹, ⟨x, hxR, rfl⟩, rfl⟩
  have hsq : C.psi i₁ (g * x * g⁻¹) * C.psi i₁ (g * x * g⁻¹) = 1 := by
    rw [← hbar, ← map_mul]
    have : (⟨y * z₂ * y⁻¹, hconjC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) *
        ⟨y * z₂ * y⁻¹, hconjC⟩ = 1 := Subtype.ext (by
      show y * z₂ * y⁻¹ * (y * z₂ * y⁻¹) = 1
      rw [show y * z₂ * y⁻¹ * (y * z₂ * y⁻¹) = y * (z₂ * z₂) * y⁻¹ by group, hz₂c.sq]
      group)
    rw [this, map_one]
  have h1 : C.psi i₁ (g * x * g⁻¹) ≠ 1 := by
    rw [← hbar]
    intro h
    apply hz₂c.ne_one
    have := eq_one_of_oddQuotMk_eq_one (Subtype.ext (show y * z₂ * y⁻¹ * (y * z₂ * y⁻¹) = 1 by
      rw [show y * z₂ * y⁻¹ * (y * z₂ * y⁻¹) = y * (z₂ * z₂) * y⁻¹ by group, hz₂c.sq]
      group) : (⟨y * z₂ * y⁻¹, hconjC⟩ : ↥(Subgroup.centralizer ({z₁} : Set G))) *
        ⟨y * z₂ * y⁻¹, hconjC⟩ = 1) h
    have h2 : y * z₂ * y⁻¹ = 1 := congrArg Subtype.val this
    calc z₂ = y⁻¹ * (y * z₂ * y⁻¹) * y := by group
      _ = 1 := by rw [h2]; group
  have hweq : oddQuotMk z₁ ⟨w, hwC⟩ = oddQuotMk z₁ ⟨y * z₂ * y⁻¹, hconjC⟩ := by
    rw [hbar]
    exact ((hU.unique _ hmem hsq).resolve_left h1).symm
  obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY hconjY hwc.sq
    (by rw [show y * z₂ * y⁻¹ * (y * z₂ * y⁻¹) = y * (z₂ * z₂) * y⁻¹ by group, hz₂c.sq]; group)
    hweq
  refine ⟨K₂, h₂S, z₂, hz₂B, hz₂, o * y, mul_mem (oddCoreIn_le _ ho) hy, ?_⟩
  rw [hwo]
  group

end Link

end CFSG.ClassicalInvolution.NDB

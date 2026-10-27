module

public import CFSG.GH74.Generic.S3.LxyShape1
public import CFSG.GH74.Generic.S3.Rank5Inv
public import CFSG.GH74.GLS.Stage4.SDWLayerFieldL
public import CFSG.GH74.GLS.Stage4.SDWLayerFieldU
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial
open CFSG.GH74.GLS (InG2 InC2 InT2 InB2 InCalK2 HasSL2Model)
open CFSG.GH74.Filter.ClassicalOdd (Q8)
open scoped MatrixGroups commutatorElement

section Normalized

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxy_isComponent_D (hnd : NbrData G t p f x y Iw Iv) :
    CFSG.IsComponent ((S45.barSub (y * x) Iv).subgroupOf
      (centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))))) := by
  have hΛD := hnd.lxy_isPCompIn_bar.1
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hΛD).symm
    (hnd.lxy_barSub_isQuasisimple hnd.lxy_Iv_le), ?_⟩
  exact CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
    (isPCompIn_two_iff.mp hnd.lxy_isPCompIn_bar).2.1 Subgroup.IsSubnormal.top

theorem NbrData.lxy_normalized (hgen : Gen4 (barQ ↥(centralizer ({y * x} : Set G))))
    (hnd : NbrData G t p f x y Iw Iv)
    {L : Subgroup (barQ ↥(centralizer ({y * x} : Set G)))} (hxL : xbar (y * x) ∉ L)
    (hle : S45.barSub (y * x) Iv ≤ L) {c : barQ ↥(centralizer ({y * x} : Set G))} (hcL : c ∈ L)
    (hcy : c * hnd.lxyY = hnd.lxyY * c) :
    ∀ k ∈ S45.barSub (y * x) Iv, c * k * c⁻¹ ∈ S45.barSub (y * x) Iv := by
  classical
  set Λ := S45.barSub (y * x) Iv with hΛ
  have hcs : c * hnd.lxyS = hnd.lxyS * c := by
    rw [hnd.lxyS_eq]
    have hu := Subgroup.mem_center_iff.1 (xbar_mem_center (y * x)) c
    calc c * (xbar (y * x) * hnd.lxyY) = (c * xbar (y * x)) * hnd.lxyY := by rw [mul_assoc]
      _ = (xbar (y * x) * c) * hnd.lxyY := by rw [hu]
      _ = xbar (y * x) * (c * hnd.lxyY) := by rw [mul_assoc]
      _ = xbar (y * x) * (hnd.lxyY * c) := by rw [hcy]
      _ = (xbar (y * x) * hnd.lxyY) * c := by rw [mul_assoc]
  by_contra! hbad
  obtain ⟨k₀, hk₀, hk₀'⟩ := hbad
  have hΛD : Λ ≤ centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))) :=
    hnd.lxy_isPCompIn_bar.1
  have hcD : c ∈ centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))) :=
    Subgroup.mem_centralizer_singleton_iff.2 hcs
  have hA := hnd.lxy_isComponent_D
  let cD : ↥(centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G))))) := ⟨c, hcD⟩
  let φ : ↥(centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G))))) ≃*
      ↥(centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G))))) := MulAut.conj cD
  have hB := CFSG.LocalCores.isComponent_map_mulEquiv φ hA
  rcases CFSG.LocalCores.distinct_components_commute hA hB with heq | hcomm
  · have hk₀D := hΛD hk₀
    have hmem : (⟨k₀, hk₀D⟩ : ↥(centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G))))))
        ∈ Λ.subgroupOf (centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G))))) := hk₀
    have : φ ⟨k₀, hk₀D⟩ ∈ (Λ.subgroupOf (centralizer ({hnd.lxyS} :
        Set (barQ ↥(centralizer ({y * x} : Set G)))))).map φ.toMonoidHom := ⟨_, hmem, rfl⟩
    rw [← heq] at this
    apply hk₀'
    have h2 := Subgroup.mem_subgroupOf.1 this
    simpa [φ, cD, MulAut.conj_apply] using h2
  · exfalso
    obtain ⟨F, hFf, hFfin, hFc, ⟨eS⟩⟩ := hnd.Iv_iso
    obtain ⟨φΛ, -⟩ := hnd.lxy_barSub_equiv hnd.lxy_Iv_le
    have hoddF : Odd (Nat.card F) := by
      rw [hFc]; exact (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
    have hF2 : ringChar F ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hoddF
    let e0 : SL(2, F) ≃* ↥Λ := eS.trans φΛ
    let Λ' : Subgroup (barQ ↥(centralizer ({y * x} : Set G))) := Λ.map (MulAut.conj c).toMonoidHom
    let e2 : SL(2, F) ≃* ↥Λ' :=
      e0.trans (Λ.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective)
    have hcomm' : ∀ a ∈ Λ, ∀ b ∈ Λ', a * b = b * a := by
      rintro a ha _ ⟨b₀, hb₀, rfl⟩
      have haD := hΛD ha
      have hb₀D := hΛD hb₀
      have h1 : (⟨a, haD⟩ : ↥(centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G))))))
          ∈ Λ.subgroupOf (centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G))))) := ha
      have h2 : φ ⟨b₀, hb₀D⟩ ∈ (Λ.subgroupOf (centralizer ({hnd.lxyS} :
          Set (barQ ↥(centralizer ({y * x} : Set G)))))).map φ.toMonoidHom := ⟨_, hb₀, rfl⟩
      have h3 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm h1
      have h4 := Subgroup.mem_centralizer_iff.1 h3 _ h2
      have h5 := congrArg Subtype.val h4
      simp only [φ, cD, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h5
      simpa [MulAut.conj_apply] using h5.symm
    have hind : ∀ a ∈ Λ, ∀ b ∈ Λ', xbar (y * x) ≠ a * b := by
      rintro a ha _ ⟨b₀, hb₀, rfl⟩ h
      apply hxL
      rw [h]
      refine L.mul_mem (hle ha) ?_
      simpa [MulAut.conj_apply] using L.mul_mem (L.mul_mem hcL (hle hb₀)) (L.inv_mem hcL)
    exact (not_gen4_of_sl2_pair_inv hF2 e0 e2 hcomm' (w := xbar (y * x))
      (fun a _ => Subgroup.mem_center_iff.1 (xbar_mem_center (y * x)) a)
      (fun b _ => Subgroup.mem_center_iff.1 (xbar_mem_center (y * x)) b)
      (xbar_mul_self hnd.lxy_inv) hind) hgen

end Normalized


section B2

@[expose] def B2NoncentralTable : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (L Λ : Subgroup H) (a : H), InB2 ↥L → Λ ≤ L → a ∈ Λ →
    a * a = 1 → a ≠ 1 → (∀ l ∈ Λ, l * a = a * l) → (∃ l ∈ L, l * a ≠ a * l) →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧ 5 ≤ Nat.card F ∧
      Nonempty (↥Λ ≃* SL(2, F))) →
    ((Λ.subgroupOf (L ⊓ centralizer ({a} : Set H))).IsSubnormal) → False

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxy_centralizer_eq (hnd : NbrData G t p f x y Iw Iv) :
    centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))) =
      centralizer ({hnd.lxyY} : Set (barQ ↥(centralizer ({y * x} : Set G)))) := by
  ext g
  simp only [Subgroup.mem_centralizer_singleton_iff]
  rw [hnd.lxyS_eq]
  have hu := Subgroup.mem_center_iff.1 (xbar_mem_center (y * x)) g
  constructor
  · intro h
    have h1 : g * (xbar (y * x) * hnd.lxyY) = (xbar (y * x) * hnd.lxyY) * g := h
    have h2 : xbar (y * x) * (g * hnd.lxyY) = xbar (y * x) * (hnd.lxyY * g) := by
      calc xbar (y * x) * (g * hnd.lxyY) = (xbar (y * x) * g) * hnd.lxyY := by rw [mul_assoc]
        _ = (g * xbar (y * x)) * hnd.lxyY := by rw [hu]
        _ = g * (xbar (y * x) * hnd.lxyY) := by rw [mul_assoc]
        _ = (xbar (y * x) * hnd.lxyY) * g := h1
        _ = xbar (y * x) * (hnd.lxyY * g) := by rw [mul_assoc]
    exact mul_left_cancel h2
  · intro h
    calc g * (xbar (y * x) * hnd.lxyY) = (g * xbar (y * x)) * hnd.lxyY := by rw [mul_assoc]
      _ = (xbar (y * x) * g) * hnd.lxyY := by rw [hu]
      _ = xbar (y * x) * (g * hnd.lxyY) := by rw [mul_assoc]
      _ = xbar (y * x) * (hnd.lxyY * g) := by rw [h]
      _ = (xbar (y * x) * hnd.lxyY) * g := by rw [mul_assoc]

theorem NbrData.lxy_false_of_inB2 (hB2 : B2NoncentralTable) (hnd : NbrData G t p f x y Iw Iv)
    {L : Subgroup (barQ ↥(centralizer ({y * x} : Set G)))} (hL : CFSG.IsComponent L)
    (hle : S45.barSub (y * x) Iv ≤ L) (hne : S45.barSub (y * x) Iv ≠ L) (hB : InB2 ↥L) : False := by
  set Λ := S45.barSub (y * x) Iv with hΛ
  have hΛq := hnd.lxy_barSub_isQuasisimple hnd.lxy_Iv_le
  have hsub := hnd.lxy_isComponent_D.2
  have hcenEq := hnd.lxy_centralizer_eq
  by_cases hcen : ∀ l ∈ L, l * hnd.lxyY = hnd.lxyY * l
  · have hLC : L ≤ centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))) := by
      intro l hl
      rw [hcenEq]
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcen l hl)
    have hsubL := CFSG.GH74.GLS.TwoThin.isSubnormal_inf_subgroupOf hsub hLC
    rcases quasisimple_subnormal_subgroups hL.1 hsubL with htop | hcen'
    · rw [Subgroup.subgroupOf_eq_top] at htop
      exact hne (le_antisymm hle htop)
    · obtain ⟨a, b, hab⟩ := S45.exists_noncomm_of_isQuasisimple hΛq
      apply hab
      have ha : (⟨a.1, hle a.2⟩ : ↥L) ∈ center ↥L :=
        hcen' (show _ ∈ Λ.subgroupOf L from a.2)
      have := Subgroup.mem_center_iff.1 ha ⟨b.1, hle b.2⟩
      exact Subtype.ext (congrArg Subtype.val this).symm
  · push Not at hcen
    obtain ⟨l, hlL, hl⟩ := hcen
    obtain ⟨F, hFf, hFfin, hFc, ⟨eS⟩⟩ := hnd.Iv_iso
    obtain ⟨φΛ, -⟩ := hnd.lxy_barSub_equiv hnd.lxy_Iv_le
    have hoddF : Odd (Nat.card F) := by
      rw [hFc]; exact (hnd.prime.1.odd_of_ne_two hnd.prime.2.1).pow
    have h5 : 5 ≤ Nat.card F := by rw [hFc]; exact hnd.prime.2.2
    have hW : L ⊓ centralizer ({hnd.lxyY} : Set (barQ ↥(centralizer ({y * x} : Set G)))) ≤
        centralizer ({hnd.lxyS} : Set (barQ ↥(centralizer ({y * x} : Set G)))) := by
      rw [hcenEq]; exact inf_le_right
    have hsub' := CFSG.GH74.GLS.TwoThin.isSubnormal_inf_subgroupOf hsub hW
    exact hB2 _ L Λ hnd.lxyY hB hle hnd.lxyY_mem hnd.lxyY_sq hnd.lxyY_ne_one hnd.lxyY_central
      ⟨l, hlL, hl⟩ ⟨F, hFf, hFfin, hoddF, h5, ⟨(eS.trans φΛ).symm⟩⟩ hsub'

end B2


section Level

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.lxy_level (hgen : Gen4 (barQ ↥(centralizer ({y * x} : Set G))))
    (hnd : NbrData G t p f x y Iw Iv)
    {L : Subgroup (barQ ↥(centralizer ({y * x} : Set G)))} (hxL : xbar (y * x) ∉ L)
    (hle : S45.barSub (y * x) Iv ≤ L) {p' f' : ℕ} (hp' : p'.Prime) (hp2' : p' ≠ 2)
    (hmod : LieModel ↥L .PSL 3 p' f' ∨ LieModel ↥L .PSU 3 p' f') : p' ^ f' = p ^ f := by
  obtain ⟨F, hFf, hFfin, hFc, ⟨eS⟩⟩ := hnd.Iv_iso
  obtain ⟨φΛ, -⟩ := hnd.lxy_barSub_equiv hnd.lxy_Iv_le
  set Λ := S45.barSub (y * x) Iv with hΛ
  have hyL : hnd.lxyY ∈ L := hle hnd.lxyY_mem
  let z : ↥L := ⟨hnd.lxyY, hyL⟩
  have hzz : z * z = 1 := Subtype.ext hnd.lxyY_sq
  have hz1 : z ≠ 1 := fun h => hnd.lxyY_ne_one (congrArg Subtype.val h)
  have hz : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hzz) hz1
  have hzK : z ∈ Λ.subgroupOf L := hnd.lxyY_mem
  have hK : HasSL2Model ↥(Λ.subgroupOf L) (fun q => q = p ^ f) :=
    ⟨F, hFf, hFfin, hFc, ⟨((Subgroup.subgroupOfEquivOfLe hle).trans (φΛ.symm.trans eS.symm)).trans
      (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 F).symm⟩⟩
  have h3 : 3 ≤ p ^ f := by have := hnd.prime.2.2; omega
  have hCK : ∀ c : ↥L, c * z = z * c → ∀ k ∈ Λ.subgroupOf L, c * k * c⁻¹ ∈ Λ.subgroupOf L := by
    intro c hc k hk
    have hcy : (c : barQ ↥(centralizer ({y * x} : Set G))) * hnd.lxyY = hnd.lxyY * c :=
      congrArg Subtype.val hc
    have := hnd.lxy_normalized hgen hxL hle c.2 hcy k hk
    exact this
  rcases hmod with hm | hm
  · obtain ⟨hadm, F', _, _, hF', ⟨e'⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSL hm
    have hE : CFSG.GH74.GLS.IVK.IsLnEps 3 ↥L 1 (p' ^ f') := Or.inl ⟨rfl, F', inferInstance, inferInstance, hF', ⟨e'⟩⟩
    exact CFSG.GH74.GLS.Stage4.Rest.field_eq_of_component_L3 hp' hp2' hE hnd.prime.1 hnd.prime.2.1 hK h3 hzK hz hCK
  · obtain ⟨hadm, F', _, _, hF', ⟨e'⟩⟩ := CFSG.GH74.Generic.stated_of_lieModel_PSU hm
    have hE : CFSG.GH74.GLS.IVK.IsLnEps 3 ↥L (-1) (p' ^ f') := Or.inr ⟨rfl, F', inferInstance, inferInstance, hF', ⟨e'⟩⟩
    exact CFSG.GH74.GLS.Stage4.Rest.field_eq_of_component_U3 hp' hp2' hE hnd.prime.1 hnd.prime.2.1 hK h3 hzK hz hCK

end Level

end CFSG.GH74.Generic.S3

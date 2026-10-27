module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Prop13Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Thm21Lemma15

public section

namespace CFSG.EvenSporadicStandard.HSStd.Prop13

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Induction.Junction
  CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem exists_isCompIn_of_involution_at [Finite H] (h15 : FS79Lemma15At H)
    (hkp : CFSG.Assembly.KProper CFSG.Blueprint.Catalog H) (hO : CFSG.oddCore H = ⊥)
    {A : Subgroup H} (hA : CFSG.Open.standardComponentIsStandard A) {t : H} (ht : orderOf t = 2)
    (htC : t ∈ centralizer (A : Set H)) :
    ∃ M : Subgroup H, IsCompIn M ⊤ ∧ A ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom := by
  have hS : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_orderOf_two ht
  have hT : IsPGroup 2 ↥(⊥ : Subgroup H) := IsPGroup.of_card (n := 0) (by simp)
  have hK : IsCompIn A (centralizer ((zpowers t : Subgroup H) : Set H)) := by
    rw [centralizer_zpowers_eq]
    exact isCompIn_centralizer_singleton hA ht htC
  obtain ⟨M, hM, hAM⟩ := exists_isCompIn_of_lemma15At h15 hkp hO hS hT (by simp) hK bot_le
  have hbot : centralizer (((⊥ : Subgroup H) : Subgroup H) : Set H) = ⊤ := by
    rw [Subgroup.centralizer_eq_top_iff_subset]
    simp
  rw [hbot] at hM
  refine ⟨M, hM, ?_⟩
  have h1 : A ≤ conjClosure M (zpowers t) := hAM.1.trans inf_le_right
  rwa [conjClosure_zpowers_eq M ht] at h1

theorem isQuasisimple_of_standard {A : Subgroup H} (hA : CFSG.Open.standardComponentIsStandard A) :
    CFSG.IsQuasisimple ↥A :=
  (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥A).2.2.1.2 hA.1

theorem normal_of_third_component [Finite H] {A M B : Subgroup H}
    (hA : CFSG.Open.standardComponentIsStandard A) {t : H} (hM : IsCompIn M ⊤)
    (hAM : A ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom) (hB : IsCompIn B ⊤) (hBM : B ≠ M)
    (hBMt : B ≠ M.map (MulAut.conj t).toMonoidHom) : A.Normal := by
  have hMt : IsCompIn (M.map (MulAut.conj t).toMonoidHom) ⊤ := hM.map_conj (mem_top t)
  have hBD : M ⊔ M.map (MulAut.conj t).toMonoidHom ≤ centralizer (B : Set H) := by
    refine sup_le (fun m hm => mem_centralizer_iff.2 fun b hb => ?_)
      (fun m hm => mem_centralizer_iff.2 fun b hb => ?_)
    · exact hB.commute_of_ne hM hBM b hb m hm
    · exact hB.commute_of_ne hMt hBMt b hb m hm
  have hAE : A ≤ layerIn (⊤ : Subgroup H) :=
    hAM.trans (sup_le (le_layerIn_of_isCompIn hM) (le_layerIn_of_isCompIn hMt))
  have hEN : layerIn (⊤ : Subgroup H) ≤ normalizer (A : Set H) := by
    intro g hg
    have hgD : g ∈ normalizer ((M ⊔ M.map (MulAut.conj t).toMonoidHom : Subgroup H) : Set H) :=
      mem_normalizer_sup (layerIn_le_normalizer hM hg) (layerIn_le_normalizer hMt hg)
    refine mem_normalizer_of_even_le hA (T := B) ?_
      (even_iff_two_dvd.1 (even_card_of_isQuasisimple hB.isQuasisimple))
    intro b hb
    have hbA : ∀ a ∈ M ⊔ M.map (MulAut.conj t).toMonoidHom, b * a = a * b := fun a ha =>
      mem_centralizer_iff.1 (hBD ha) b hb
    refine ⟨mem_centralizer_iff.2 fun a ha => (hbA a (hAM ha)).symm, ⟨g⁻¹ * b * g, ?_, ?_⟩⟩
    · refine mem_centralizer_iff.2 fun a ha => ?_
      have ha' : g * a * g⁻¹ ∈ M ⊔ M.map (MulAut.conj t).toMonoidHom :=
        (Subgroup.mem_normalizer_iff.1 hgD a).1 (hAM ha)
      have h1 := hbA _ ha'
      calc a * (g⁻¹ * b * g) = g⁻¹ * ((g * a * g⁻¹) * b) * g := by group
        _ = g⁻¹ * (b * (g * a * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * b * g) * a := by group
    · show g * (g⁻¹ * b * g) * g⁻¹ = b
      group
  have hEn := layerIn_normal (H := H)
  have hAnE : (A.subgroupOf (layerIn (⊤ : Subgroup H))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).2 hEN
  have hAs : A.IsSubnormal := Subgroup.IsSubnormal.trans hAE hAnE.isSubnormal hEn.isSubnormal
  exact normal_of_subnormal_standard hA (isQuasisimple_of_standard hA) hAs

theorem exists_mulEquiv_of_swap {A M : Subgroup H} {t : H} (ht : orderOf t = 2)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M.map (MulAut.conj t).toMonoidHom, x * y = y * x)
    (hMZ : M ⊓ centralizer (M : Set H) = ⊥) (hMs : IsSimpleGroup ↥M)
    (hAM : A ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom) (hAt : A ≤ centralizer ({t} : Set H))
    (hNA : centralizer ({t} : Set H) ≤ normalizer (A : Set H)) (hA1 : A ≠ ⊥) :
    Nonempty (↥M ≃* ↥A) := by
  have ht1 := mul_self_eq_one_of_orderOf ht
  have hσσ : ∀ x : H, t * (t * x * t⁻¹) * t⁻¹ = x := fun x => by
    calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
      _ = x := by rw [ht1]; group
  have hσmul : ∀ x y : H, t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := fun x y => by
    group
  have hMt_mem : ∀ z ∈ M, t * z * t⁻¹ ∈ M.map (MulAut.conj t).toMonoidHom :=
    fun z hz => ⟨z, hz, rfl⟩
  have hcommZ : ∀ x ∈ M, ∀ z ∈ M, x * (t * z * t⁻¹) = (t * z * t⁻¹) * x :=
    fun x hx z hz => hcomm x hx _ (hMt_mem z hz)
  have hinter : ∀ w ∈ M, w ∈ M.map (MulAut.conj t).toMonoidHom → w = 1 := by
    intro w hw hwt
    have h3 : w ∈ M ⊓ centralizer (M : Set H) :=
      Subgroup.mem_inf.2 ⟨hw, mem_centralizer_iff.2 fun x hx => hcomm x hx w hwt⟩
    rw [hMZ, Subgroup.mem_bot] at h3
    exact h3
  let ψ : ↥M →* H :=
    { toFun := fun m => (m : H) * (t * (m : H) * t⁻¹)
      map_one' := by simp
      map_mul' := by
        intro x y
        have hc := hcommZ y y.2 x x.2
        simp only [Subgroup.coe_mul]
        calc (x : H) * y * (t * ((x : H) * y) * t⁻¹)
            = (x : H) * ((y : H) * (t * (x : H) * t⁻¹)) * (t * (y : H) * t⁻¹) := by group
          _ = (x : H) * ((t * (x : H) * t⁻¹) * (y : H)) * (t * (y : H) * t⁻¹) := by rw [hc]
          _ = ((x : H) * (t * (x : H) * t⁻¹)) * ((y : H) * (t * (y : H) * t⁻¹)) := by group }
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : (m : H) * (t * (m : H) * t⁻¹) = 1 := hm
    have h2 : (m : H)⁻¹ = t * (m : H) * t⁻¹ := by
      calc (m : H)⁻¹ = (m : H)⁻¹ * ((m : H) * (t * (m : H) * t⁻¹)) := by rw [h1, mul_one]
        _ = t * (m : H) * t⁻¹ := by group
    have h3 : (m : H)⁻¹ = 1 := hinter _ (M.inv_mem m.2) (h2 ▸ hMt_mem m m.2)
    exact Subtype.ext (inv_eq_one.1 h3)
  have hψt : ∀ m : ↥M, ψ m ∈ centralizer ({t} : Set H) := by
    intro m
    rw [mem_centralizer_singleton_iff]
    have h1 : t * ((m : H) * (t * (m : H) * t⁻¹)) * t⁻¹ = (m : H) * (t * (m : H) * t⁻¹) := by
      rw [hσmul, hσσ]
      exact (hcommZ m m.2 m m.2).symm
    calc ((m : H) * (t * (m : H) * t⁻¹)) * t
        = (t * ((m : H) * (t * (m : H) * t⁻¹)) * t⁻¹) * t := by rw [h1]
      _ = t * ((m : H) * (t * (m : H) * t⁻¹)) := by group
  have hAψ : A ≤ ψ.range := by
    intro a ha
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm (hAM ha)
    obtain ⟨z, hz, rfl⟩ := hy
    have hat : t * (x * ((MulAut.conj t).toMonoidHom z)) * t⁻¹ =
        x * ((MulAut.conj t).toMonoidHom z) := by
      have h0 := mem_centralizer_singleton_iff.1 (hAt ha)
      calc t * (x * ((MulAut.conj t).toMonoidHom z)) * t⁻¹
          = (x * ((MulAut.conj t).toMonoidHom z) * t) * t⁻¹ := by rw [h0]
        _ = x * ((MulAut.conj t).toMonoidHom z) := by group
    have hzt : (MulAut.conj t).toMonoidHom z = t * z * t⁻¹ := rfl
    rw [hzt, hσmul, hσσ] at hat
    have h1 : x * (t * z * t⁻¹) = z * (t * x * t⁻¹) := by
      rw [← hat]
      exact (hcommZ z hz x hx).symm
    have h2 : z⁻¹ * x = t * (x * z⁻¹) * t⁻¹ := by
      calc z⁻¹ * x = z⁻¹ * (x * (t * z * t⁻¹)) * (t * z * t⁻¹)⁻¹ := by group
        _ = z⁻¹ * (z * (t * x * t⁻¹)) * (t * z * t⁻¹)⁻¹ := by rw [h1]
        _ = t * (x * z⁻¹) * t⁻¹ := by group
    have h3 : z⁻¹ * x = 1 :=
      hinter _ (M.mul_mem (M.inv_mem hz) hx)
        (h2 ▸ hMt_mem _ (M.mul_mem hx (M.inv_mem hz)))
    have hxz : x = z := (inv_inj.1 (mul_eq_one_iff_eq_inv.1 h3)).symm
    subst hxz
    exact ⟨⟨x, hx⟩, rfl⟩
  have hnormal : (A.subgroupOf ψ.range).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAψ).2 fun y hy => by
      obtain ⟨m, rfl⟩ := hy
      exact hNA (hψt m)
  have hsimple : IsSimpleGroup ↥ψ.range := (MonoidHom.ofInjective hψinj).symm.isSimpleGroup
  have := hnormal
  rcases hsimple.eq_bot_or_eq_top_of_normal (A.subgroupOf ψ.range) with hb | hT
  · exfalso
    apply hA1
    refine eq_bot_iff.2 fun a ha => ?_
    have : (⟨a, hAψ ha⟩ : ↥ψ.range) ∈ A.subgroupOf ψ.range := ha
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · have hle : ψ.range ≤ A := fun y hy => by
      have : (⟨y, hy⟩ : ↥ψ.range) ∈ A.subgroupOf ψ.range := by
        rw [hT]
        exact Subgroup.mem_top _
      exact this
    exact ⟨(MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr (le_antisymm hAψ hle).symm)⟩

end CFSG.EvenSporadicStandard.HSStd.Prop13

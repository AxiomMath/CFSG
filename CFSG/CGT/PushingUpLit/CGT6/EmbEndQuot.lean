module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Open.StandardDefs
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupMap
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.CGT.PushingUpLit.CGT6.EndQuot

open CFSG Subgroup
open scoped commutatorElement

section Basic

variable {Γ : Type} [Group Γ] (Λ : Subgroup Γ)

@[expose] def zc : Subgroup Γ := Λ ⊓ Subgroup.centralizer (Λ : Set Γ)

variable {Λ}

theorem mem_zc {x : Γ} : x ∈ zc Λ ↔ x ∈ Λ ∧ ∀ l ∈ Λ, l * x = x * l := by
  unfold zc
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

theorem zc_le : zc Λ ≤ Λ := inf_le_left

theorem comm_of_mem_zc {x l : Γ} (hx : x ∈ zc Λ) (hl : l ∈ Λ) : l * x = x * l :=
  (mem_zc.mp hx).2 l hl

instance zc_normal [hΛ : Λ.Normal] : (zc Λ).Normal := by
  unfold zc
  have : (Subgroup.centralizer (Λ : Set Γ)).Normal := Subgroup.normal_centralizer
  infer_instance

theorem commutator_zc : ⁅zc Λ, Λ⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact inf_le_right

theorem commutator_zc_of_le {Υ : Subgroup Γ} (h : Υ ≤ Λ) : ⁅zc Λ, Υ⁆ = ⊥ :=
  le_bot_iff.mp ((Subgroup.commutator_mono le_rfl h).trans commutator_zc.le)

end Basic

section Quotient

variable {Γ : Type} [Group Γ] {Λ Υ : Subgroup Γ} [Λ.Normal]

theorem ker_mk : (QuotientGroup.mk' (zc Λ)).ker = zc Λ := QuotientGroup.ker_mk' _

theorem centralizer_comap (hΥΛ : Υ ≤ Λ) (hperf : Group.IsPerfect Υ) :
    (Subgroup.centralizer ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) :
      Set (Γ ⧸ zc Λ))).comap (QuotientGroup.mk' (zc Λ)) = Subgroup.centralizer (Υ : Set Γ) := by
  apply le_antisymm
  · set D := (Subgroup.centralizer ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) :
      Set (Γ ⧸ zc Λ))).comap (QuotientGroup.mk' (zc Λ)) with hD
    have h1 : ⁅Υ, D⁆ ≤ zc Λ := by
      rw [Subgroup.commutator_le]
      intro y hy d hd
      rw [← ker_mk, MonoidHom.mem_ker, map_commutatorElement]
      have hd' := Subgroup.mem_centralizer_iff.mp hd (QuotientGroup.mk' (zc Λ) y)
        (Subgroup.mem_map_of_mem _ hy)
      exact commutatorElement_eq_one_iff_mul_comm.mpr hd'
    have h2 : ⁅⁅Υ, D⁆, Υ⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅Υ, D⁆, Υ⁆ ≤ ⁅zc Λ, Υ⁆ := Subgroup.commutator_mono h1 le_rfl
        _ = ⊥ := commutator_zc_of_le hΥΛ
        _ ≤ ⊥ := le_rfl
    have h3 := LocalCores.perfect_double_commutator hperf h2
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    exact h3
  · intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hx y hy).symm]

end Quotient

section Hom

variable {Γ H : Type} [Group Γ] [Group H] (f : Γ →* H)

theorem map_inf_of_ker_le {A B : Subgroup Γ} (hA : f.ker ≤ A) :
    A.map f ⊓ B.map f = (A ⊓ B).map f := by
  apply le_antisymm
  · rintro _ ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have hz : a⁻¹ * b ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hbA : b ∈ A := by
      have := mul_mem ha (hA hz)
      rwa [mul_inv_cancel_left] at this
    exact ⟨b, ⟨hbA, hb⟩, hab⟩
  · exact le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)

theorem mem_normalizer_map (hf : Function.Surjective f) {A : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (A : Set Γ)) :
    f g ∈ Subgroup.normalizer ((A.map f : Subgroup H) : Set H) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  obtain ⟨a, rfl⟩ := hf x
  constructor
  · rintro ⟨b, hb, hba⟩
    refine ⟨g * b * g⁻¹, (hg b).mp hb, ?_⟩
    rw [map_mul, map_mul, map_inv, hba]
  · rintro ⟨b, hb, hba⟩
    refine ⟨g⁻¹ * b * g, ?_, ?_⟩
    · have e : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
      exact (hg (g⁻¹ * b * g)).mpr (by rw [e]; exact hb)
    · rw [map_mul, map_mul, map_inv, hba]
      group

end Hom

section Perfect

variable {Γ : Type} [Group Γ] {Λ Υ : Subgroup Γ} [Λ.Normal]

theorem commutatorElement_mul_right_of_commute {a b z : Γ} (ha : z * a = a * z)
    (hb : z * b = b * z) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h1 : z * a⁻¹ = a⁻¹ * z := by
    have := congrArg (fun x => a⁻¹ * x * a⁻¹) ha
    simpa [mul_assoc] using this.symm
  have h2 : z * b⁻¹ = b⁻¹ * z := by
    have := congrArg (fun x => b⁻¹ * x * b⁻¹) hb
    simpa [mul_assoc] using this.symm
  calc ⁅a, b * z⁆ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]; group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h1]
    _ = ⁅a, b⁆ := by simp only [commutatorElement_def]; group

omit [Λ.Normal] in
theorem commutatorElement_mul_zc {y₁ y₂ z₁ z₂ : Γ} (hy₁ : y₁ ∈ Λ) (hy₂ : y₂ ∈ Λ)
    (hz₁ : z₁ ∈ zc Λ) (hz₂ : z₂ ∈ zc Λ) : ⁅y₁ * z₁, y₂ * z₂⁆ = ⁅y₁, y₂⁆ := by
  have c1 : ∀ {l : Γ}, l ∈ Λ → z₁ * l = l * z₁ := fun hl => (comm_of_mem_zc hz₁ hl).symm
  have c2 : ∀ {l : Γ}, l ∈ Λ → z₂ * l = l * z₂ := fun hl => (comm_of_mem_zc hz₂ hl).symm
  have hz₁Λ : z₁ ∈ Λ := zc_le hz₁
  have hz₂Λ : z₂ ∈ Λ := zc_le hz₂
  have e1 : ⁅y₁ * z₁, y₂ * z₂⁆ = ⁅y₁ * z₁, y₂⁆ :=
    commutatorElement_mul_right_of_commute
      (by rw [← mul_assoc, c2 hy₁, mul_assoc, c2 hz₁Λ, ← mul_assoc]) (c2 hy₂)
  have e2 : ⁅y₁ * z₁, y₂⁆ = ⁅y₁, y₂⁆ := by
    rw [← commutatorElement_inv, commutatorElement_mul_right_of_commute (c1 hy₂) (c1 hy₁)]
    exact commutatorElement_inv _ _
  rw [e1, e2]

theorem conj_mem_of_normalizer (hΥΛ : Υ ≤ Λ) (hperf : ⁅Υ, Υ⁆ = Υ) {g : Γ}
    (hg : QuotientGroup.mk' (zc Λ) g ∈ Subgroup.normalizer
      ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) : Set (Γ ⧸ zc Λ))) :
    Υ.map (MulAut.conj g).toMonoidHom ≤ Υ := by
  have hmem : ∀ y ∈ Υ, ∃ y' ∈ Υ, ∃ z ∈ zc Λ, g * y * g⁻¹ = y' * z := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := (Subgroup.mem_normalizer_iff.mp hg (QuotientGroup.mk' (zc Λ) y)).mp
      (Subgroup.mem_map_of_mem _ hy)
    refine ⟨y', hy', y'⁻¹ * (g * y * g⁻¹), ?_, by group⟩
    rw [← ker_mk, MonoidHom.mem_ker, map_mul, map_inv, hyy', map_mul, map_mul, map_inv]
    exact inv_mul_cancel _
  conv_lhs => rw [← hperf]
  rw [Subgroup.map_commutator, Subgroup.commutator_le]
  rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
  obtain ⟨a₁, ha₁, z₁, hz₁, e₁⟩ := hmem y₁ hy₁
  obtain ⟨a₂, ha₂, z₂, hz₂, e₂⟩ := hmem y₂ hy₂
  show ⁅g * y₁ * g⁻¹, g * y₂ * g⁻¹⁆ ∈ Υ
  rw [e₁, e₂, commutatorElement_mul_zc (hΥΛ ha₁) (hΥΛ ha₂) hz₁ hz₂]
  exact Subgroup.commutator_mem_commutator ha₁ ha₂ |> fun h => hperf ▸ h

theorem normalizer_comap (hΥΛ : Υ ≤ Λ) (hperf : ⁅Υ, Υ⁆ = Υ) :
    (Subgroup.normalizer ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) :
      Set (Γ ⧸ zc Λ))).comap (QuotientGroup.mk' (zc Λ)) = Subgroup.normalizer (Υ : Set Γ) := by
  ext g
  rw [Subgroup.mem_comap]
  constructor
  · intro hg
    have h1 := conj_mem_of_normalizer hΥΛ hperf hg
    have hg' : QuotientGroup.mk' (zc Λ) g⁻¹ ∈ Subgroup.normalizer
        ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) : Set (Γ ⧸ zc Λ)) := by
      rw [map_inv]
      exact inv_mem hg
    have h2 := conj_mem_of_normalizer hΥΛ hperf hg'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => h1 ⟨y, hy, rfl⟩, fun hy => ?_⟩
    have := h2 ⟨g * y * g⁻¹, hy, rfl⟩
    have e : (MulAut.conj g⁻¹).toMonoidHom (g * y * g⁻¹) = y := by
      show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
      group
    rwa [e] at this
  · intro hg
    exact mem_normalizer_map _ (QuotientGroup.mk'_surjective _) hg

omit [Λ.Normal] in
theorem isQuasisimple_iff_open (Q : Type) [Group Q] :
    CFSG.IsQuasisimple Q ↔ CFSG.Open.IsQuasisimple Q := by
  constructor
  · rintro ⟨hperf, hsimple, -⟩
    exact ⟨hperf.commutator_eq_top, hsimple⟩
  · intro h
    exact ⟨⟨h.1⟩, h.2, ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

omit [Λ.Normal] in
theorem inf_zc_eq_bot (hΥΛ : Υ ≤ Λ) (hc : Subgroup.center Υ = ⊥) : Υ ⊓ zc Λ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxΥ, hxz⟩
  have : (⟨x, hxΥ⟩ : Υ) ∈ Subgroup.center Υ := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (comm_of_mem_zc hxz (hΥΛ y.2))
  rw [hc, Subgroup.mem_bot] at this
  have := congrArg Subtype.val this
  simpa using this

theorem injOn_of_inf_zc (hΥΛ : Υ ≤ Λ) (hc : Subgroup.center Υ = ⊥) :
    Function.Injective ((QuotientGroup.mk' (zc Λ)).comp Υ.subtype) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : (x : Γ) ∈ zc Λ := by
    rw [← ker_mk, MonoidHom.mem_ker]
    exact hx
  have h2 : (x : Γ) ∈ Υ ⊓ zc Λ := ⟨x.2, h1⟩
  rw [inf_zc_eq_bot hΥΛ hc, Subgroup.mem_bot] at h2
  exact Subtype.ext (by rw [h2]; rfl)

theorem nonempty_equiv_map (hΥΛ : Υ ≤ Λ) (hc : Subgroup.center Υ = ⊥) :
    Nonempty (↥Υ ≃* ↥(Υ.map (QuotientGroup.mk' (zc Λ)))) := by
  have hinj := injOn_of_inf_zc hΥΛ hc
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

theorem oddCore_eq [Finite Γ] (hqs : CFSG.IsQuasisimple Λ) (hfs : generalizedFitting Γ = Λ)
    (hev : Even (Nat.card Λ)) (hzodd : Odd (Nat.card (zc Λ))) :
    CFSG.Open.standardOddCore Γ = zc Λ := by
  apply le_antisymm
  · apply sSup_le
    rintro N ⟨hN, hNodd⟩
    have hperfΛ : Group.IsPerfect Λ := hqs.1
    have hD : N ⊓ Λ ≤ zc Λ := by
      have hn : ((N ⊓ Λ).subgroupOf Λ).Normal := by
        have : (N ⊓ Λ).Normal := Subgroup.normal_inf_normal _ _
        exact Subgroup.normal_subgroupOf
      rcases LocalCores.quasisimple_normal_subgroups hqs hn with h | h
      · exfalso
        have hΛN : Λ ≤ N := by
          intro x hx
          have : (⟨x, hx⟩ : Λ) ∈ (N ⊓ Λ).subgroupOf Λ := by rw [h]; trivial
          exact this.1
        have := (Subgroup.card_dvd_of_le hΛN)
        exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hNodd this)) hev
      · intro x hx
        refine mem_zc.mpr ⟨hx.2, fun l hl => ?_⟩
        have := h (show (⟨x, hx.2⟩ : Λ) ∈ (N ⊓ Λ).subgroupOf Λ from hx)
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp this ⟨l, hl⟩)
    have h1 : ⁅Λ, N⁆ ≤ zc Λ := by
      rw [Subgroup.commutator_le]
      intro l hl n hn
      apply hD
      refine ⟨?_, ?_⟩
      · have h3 : ⁅l, n⁆ = (l * n * l⁻¹) * n⁻¹ := rfl
        rw [h3]
        exact N.mul_mem (hN.conj_mem n hn l) (N.inv_mem hn)
      · have h3 : ⁅l, n⁆ = l * (n * l⁻¹ * n⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [h3]
        exact mul_mem hl (Subgroup.Normal.conj_mem ‹Λ.Normal› l⁻¹ (Λ.inv_mem hl) n)
    have h2 : ⁅⁅Λ, N⁆, Λ⁆ = ⊥ := by
      refine le_bot_iff.mp ?_
      calc ⁅⁅Λ, N⁆, Λ⁆ ≤ ⁅zc Λ, Λ⁆ := Subgroup.commutator_mono h1 le_rfl
        _ = ⊥ := commutator_zc
        _ ≤ ⊥ := le_rfl
    have h3 := LocalCores.perfect_double_commutator hperfΛ h2
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    have hcent : Subgroup.centralizer (Λ : Set Γ) ≤ Λ := by
      have := centralizer_generalizedFitting_le Γ
      rwa [hfs] at this
    intro n hn
    exact ⟨hcent (h3 hn), h3 hn⟩
  · exact le_sSup ⟨inferInstance, hzodd⟩

omit [Λ.Normal] in
theorem not_le_zc (hqs : CFSG.IsQuasisimple Λ) : ¬ Λ ≤ zc Λ := by
  intro h
  have := LocalCores.isQuasisimple_nontrivial hqs
  obtain ⟨x, hx⟩ := exists_ne (1 : Λ)
  have hcomm : ∀ a b : Λ, a * b = b * a := fun a b =>
    Subtype.ext (comm_of_mem_zc (h b.2) a.2)
  have hbot : commutator Λ ≤ ⊥ := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm a b)
  rw [hqs.1.commutator_eq_top] at hbot
  exact hx (Subgroup.mem_bot.mp (hbot (Subgroup.mem_top x)))

theorem layer_quot [Finite Γ] (hqs : CFSG.IsQuasisimple Λ) (hfs : generalizedFitting Γ = Λ) :
    layer (Γ ⧸ zc Λ) = Λ.map (QuotientGroup.mk' (zc Λ)) := by
  have hnormal : (Λ.map (QuotientGroup.mk' (zc Λ))).Normal :=
    Subgroup.Normal.map ‹Λ.Normal› _ (QuotientGroup.mk'_surjective _)
  apply le_antisymm
  · apply sSup_le
    intro K hK
    rcases LocalCores.component_normal_subgroup hK hnormal with h | h
    · exact h
    · exfalso
      have hcent : Subgroup.centralizer (Λ.map (QuotientGroup.mk' (zc Λ)) : Set (Γ ⧸ zc Λ)) =
          (Subgroup.centralizer (Λ : Set Γ)).map (QuotientGroup.mk' (zc Λ)) := by
        have := centralizer_comap (Λ := Λ) (Υ := Λ) le_rfl hqs.1
        conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective (zc Λ)) (Subgroup.centralizer
            (Λ.map (QuotientGroup.mk' (zc Λ)) : Set (Γ ⧸ zc Λ)))]
        rw [this]
      have hKc : K ≤ Subgroup.centralizer (Λ.map (QuotientGroup.mk' (zc Λ)) : Set (Γ ⧸ zc Λ)) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hcl : Subgroup.centralizer (Λ : Set Γ) ≤ zc Λ := by
        have := centralizer_generalizedFitting_le Γ
        rw [hfs] at this
        exact fun x hx =>
          mem_zc.mpr ⟨this hx, fun l hl => (Subgroup.mem_centralizer_iff.mp hx l hl)⟩
      have hbot : (Subgroup.centralizer (Λ : Set Γ)).map (QuotientGroup.mk' (zc Λ)) = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_mk]
        exact hcl hx
      rw [hcent, hbot, le_bot_iff] at hKc
      have := LocalCores.isQuasisimple_nontrivial hK.1
      exact (Subgroup.nontrivial_iff_ne_bot K).mp this hKc
  · refine le_sSup ⟨LocalCores.isQuasisimple_map hqs _ (not_le_zc hqs ∘ fun h => ?_), ?_⟩
    · rw [ker_mk] at h
      exact h
    · exact hnormal.isSubnormal

theorem nonempty_equiv_layer :
    Nonempty (↥(Λ.map (QuotientGroup.mk' (zc Λ))) ≃* (↥Λ ⧸ Subgroup.center ↥Λ)) := by
  let f : ↥Λ →* Γ ⧸ zc Λ := (QuotientGroup.mk' (zc Λ)).comp Λ.subtype
  have hker : f.ker = Subgroup.center ↥Λ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hx y
      have : (x : Γ) ∈ zc Λ := by
        rw [← ker_mk, MonoidHom.mem_ker]; exact hx
      exact Subtype.ext (comm_of_mem_zc this y.2)
    · intro hx
      have : (x : Γ) ∈ zc Λ := mem_zc.mpr ⟨x.2, fun l hl => congrArg Subtype.val (hx ⟨l, hl⟩)⟩
      rw [← ker_mk, MonoidHom.mem_ker] at this
      exact this
  have hrange : f.range = Λ.map (QuotientGroup.mk' (zc Λ)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans (QuotientGroup.quotientMulEquivOfEq hker))⟩

omit [Λ.Normal] in
theorem even_card_of_pgroup {T : Subgroup Γ} [Finite Γ] (hT2 : IsPGroup 2 T) (hT : T ≠ ⊥) :
    Even (Nat.card T) := by
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hT
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hn
  rw [hn]
  exact (Nat.even_pow' hn0).mpr even_two

omit [Λ.Normal] in
theorem inf_zc_eq_bot_of_pgroup [Finite Γ] {T : Subgroup Γ} (hT2 : IsPGroup 2 T)
    (hzodd : Odd (Nat.card (zc Λ))) : T ⊓ zc Λ = ⊥ := by
  obtain ⟨n, hn⟩ := hT2.exists_card_eq
  have h1 : Nat.card ↥(T ⊓ zc Λ) ∣ Nat.card T := Subgroup.card_dvd_of_le inf_le_left
  have h2 : Nat.card ↥(T ⊓ zc Λ) ∣ Nat.card (zc Λ) := Subgroup.card_dvd_of_le inf_le_right
  rw [hn] at h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hk0 : k = 0 := by
    by_contra hk0
    have : 2 ∣ Nat.card ↥(T ⊓ zc Λ) := by
      rw [hk]; exact dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hzodd h2)) (even_iff_two_dvd.mpr this)
  rw [hk0, pow_zero, Subgroup.card_eq_one] at hk
  exact hk

theorem card_map_of_pgroup [Finite Γ] {T : Subgroup Γ} (hT2 : IsPGroup 2 T)
    (hzodd : Odd (Nat.card (zc Λ))) :
    Nat.card (T.map (QuotientGroup.mk' (zc Λ))) = Nat.card T := by
  have hinj : Function.Injective ((QuotientGroup.mk' (zc Λ)).comp T.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (x : Γ) ∈ zc Λ := by
      rw [← ker_mk, MonoidHom.mem_ker]; exact hx
    have h2 : (x : Γ) ∈ T ⊓ zc Λ := ⟨x.2, h1⟩
    rw [inf_zc_eq_bot_of_pgroup hT2 hzodd, Subgroup.mem_bot] at h2
    exact Subtype.ext (by rw [h2]; rfl)
  have hrange : ((QuotientGroup.mk' (zc Λ)).comp T.subtype).range =
      T.map (QuotientGroup.mk' (zc Λ)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem isSylowOf_map [Finite Γ] {C₀ T : Subgroup Γ} (hzC : zc Λ ≤ C₀) (hT : T ≤ C₀)
    (hT2 : IsPGroup 2 T) (hTmax : ∀ T' : Subgroup Γ, T ≤ T' → T' ≤ C₀ → IsPGroup 2 T' → T' = T) :
    ABGLocalTools.IsSylowOf 2 (T.map (QuotientGroup.mk' (zc Λ)))
      (C₀.map (QuotientGroup.mk' (zc Λ))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : ABGLocalTools.IsSylowOf 2 T C₀ := by
    have hT2' : IsPGroup 2 (T.subgroupOf C₀) := hT2.comap_subtype
    obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hT2'
    have hSS : ABGLocalTools.IsSylowOf 2 ((S : Subgroup C₀).map C₀.subtype) C₀ := ⟨S, rfl⟩
    have hTS : T ≤ (S : Subgroup C₀).map C₀.subtype := by
      intro x hx
      exact ⟨⟨x, hT hx⟩, hS hx, rfl⟩
    have heq := hTmax _ hTS (Subgroup.map_subtype_le _) hSS.isPGroup
    rw [← heq]
    exact hSS
  rw [ABGLocalTools.isSylowOf_iff] at hS ⊢
  obtain ⟨-, -, hnd⟩ := hS
  refine ⟨Subgroup.map_mono hT, hT2.map _, ?_⟩
  have h1 : (T.map (QuotientGroup.mk' (zc Λ))).relIndex (C₀.map (QuotientGroup.mk' (zc Λ))) =
      (T ⊔ zc Λ).relIndex C₀ := by
    rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, ker_mk]
  have h2 : (T ⊔ zc Λ).relIndex C₀ ∣ T.relIndex C₀ := by
    have := Subgroup.relIndex_mul_relIndex T (T ⊔ zc Λ) C₀ le_sup_left (sup_le hT hzC)
    exact ⟨T.relIndex (T ⊔ zc Λ), by rw [← this, mul_comm]⟩
  rw [h1]
  exact fun h => hnd (h.trans h2)

end Perfect

section Cfg

structure Cfg (Γ : Type) [Group Γ] [Finite Γ] (Λ Υ T : Subgroup Γ) [Λ.Normal] : Prop where
  le : Υ ≤ Λ
  qs : CFSG.IsQuasisimple Λ
  fs : generalizedFitting Γ = Λ
  zodd : Odd (Nat.card (zc Λ))
  perf : ⁅Υ, Υ⁆ = Υ
  cen : Subgroup.center Υ = ⊥
  evenΥ : Even (Nat.card Υ)
  std : CFSG.Open.standardIsStandardSubgroup Υ
  gen : ∀ N : Subgroup Γ, N.Normal → Υ ≤ N → Λ ≤ N
  hT : T ≤ Subgroup.centralizer (Υ : Set Γ)
  T2 : IsPGroup 2 T
  Tne : T ≠ ⊥
  Tmax : ∀ T' : Subgroup Γ, T ≤ T' → T' ≤ Subgroup.centralizer (Υ : Set Γ) → IsPGroup 2 T' →
    T' = T

variable {Γ : Type} [Group Γ] [Finite Γ] {Λ Υ T : Subgroup Γ} [Λ.Normal]

namespace Cfg

theorem perfΥ (h : Cfg Γ Λ Υ T) : Group.IsPerfect Υ := Subgroup.isPerfect_iff.mpr h.perf

theorem evenΛ (h : Cfg Γ Λ Υ T) : Even (Nat.card Λ) :=
  even_iff_two_dvd.mpr ((even_iff_two_dvd.mp h.evenΥ).trans (Subgroup.card_dvd_of_le h.le))

theorem oddCore (h : Cfg Γ Λ Υ T) : CFSG.Open.standardOddCore Γ = zc Λ :=
  oddCore_eq h.qs h.fs h.evenΛ h.zodd

theorem centralizer_le (h : Cfg Γ Λ Υ T) : Subgroup.centralizer (Λ : Set Γ) ≤ zc Λ := by
  have := centralizer_generalizedFitting_le Γ
  rw [h.fs] at this
  exact fun x hx => mem_zc.mpr ⟨this hx, fun l hl => Subgroup.mem_centralizer_iff.mp hx l hl⟩

theorem centralizer_zc (h : Cfg Γ Λ Υ T) : zc Λ ≤ Subgroup.centralizer (Υ : Set Γ) := by
  intro x hx y hy
  exact comm_of_mem_zc hx (h.le hy)

theorem nonempty_equiv (h : Cfg Γ Λ Υ T) :
    Nonempty (↥Υ ≃* ↥(Υ.map (QuotientGroup.mk' (zc Λ)))) :=
  nonempty_equiv_map h.le h.cen

theorem centralizer_map (h : Cfg Γ Λ Υ T) :
    Subgroup.centralizer ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) :
      Set (Γ ⧸ zc Λ)) = (Subgroup.centralizer (Υ : Set Γ)).map (QuotientGroup.mk' (zc Λ)) := by
  conv_lhs => rw [← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (zc Λ))
    (Subgroup.centralizer ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) :
      Set (Γ ⧸ zc Λ)))]
  rw [centralizer_comap h.le h.perfΥ]

theorem standard_map (h : Cfg Γ Λ Υ T) :
    CFSG.Open.standardIsStandardSubgroup (Υ.map (QuotientGroup.mk' (zc Λ))) :=
  (CFSG.ComponentClassification.GSThmB.isStandardSubgroup_map_mk'
    (CFSG.Open.standardComponentIsStandard.isStandardSubgroup h.std) h.zodd
    h.centralizer_zc).standardComponentIsStandard

theorem not_normal (h : Cfg Γ Λ Υ T) : ¬ (Υ.map (QuotientGroup.mk' (zc Λ))).Normal := by
  intro hn
  have hΥn : Υ.Normal := by
    have h1 := normalizer_comap h.le h.perf
    rw [Subgroup.normalizer_eq_top_iff.mpr hn, Subgroup.comap_top] at h1
    exact Subgroup.normalizer_eq_top_iff.mp h1.symm
  have hΛΥ : Λ ≤ Υ := h.gen Υ hΥn le_rfl
  have hTz : T ≤ zc Λ := fun x hx => h.centralizer_le (Subgroup.centralizer_le hΛΥ (h.hT hx))
  have hT : T ⊓ zc Λ = ⊥ := inf_zc_eq_bot_of_pgroup h.T2 h.zodd
  exact h.Tne (le_bot_iff.mp (hT ▸ le_inf le_rfl hTz))

theorem layer_eq (h : Cfg Γ Λ Υ T) :
    layer (Γ ⧸ zc Λ) = Λ.map (QuotientGroup.mk' (zc Λ)) :=
  layer_quot h.qs h.fs

theorem isSylow (h : Cfg Γ Λ Υ T) :
    ABGLocalTools.IsSylowOf 2 (T.map (QuotientGroup.mk' (zc Λ)))
      (Subgroup.centralizer ((Υ.map (QuotientGroup.mk' (zc Λ)) : Subgroup (Γ ⧸ zc Λ)) :
        Set (Γ ⧸ zc Λ))) := by
  rw [h.centralizer_map]
  exact isSylowOf_map h.centralizer_zc h.hT h.T2 h.Tmax

theorem card_map_T (h : Cfg Γ Λ Υ T) :
    Nat.card (T.map (QuotientGroup.mk' (zc Λ))) = Nat.card T :=
  card_map_of_pgroup h.T2 h.zodd

end Cfg

end Cfg

end CFSG.CGT.PushingUpLit.CGT6.EndQuot

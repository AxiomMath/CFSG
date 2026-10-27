module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CGT.PushingUpLit.BlocksCommuteDefs

public section

namespace CFSG.CGT.PushingUpLit.Glue

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
open scoped commutatorElement

theorem exists_commHom {Γ : Type} [Group Γ] {W : Subgroup Γ} {i : Γ}
    (hab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hi : ∀ w ∈ W, i * w * i⁻¹ ∈ W) :
    ∃ ψ : ↥W →* Γ, ∀ w : ↥W, ψ w = i * (w : Γ) * i⁻¹ * (w : Γ)⁻¹ := by
  refine ⟨MonoidHom.mk' (fun w : ↥W => i * (w : Γ) * i⁻¹ * (w : Γ)⁻¹) fun a b => ?_,
    fun w => rfl⟩
  have hx : (i * (b : Γ) * i⁻¹ * (b : Γ)⁻¹) * (a : Γ)⁻¹ =
      (a : Γ)⁻¹ * (i * (b : Γ) * i⁻¹ * (b : Γ)⁻¹) :=
    hab _ (mul_mem (hi b b.2) (inv_mem b.2)) _ (inv_mem a.2)
  show i * ((a : Γ) * b) * i⁻¹ * ((a : Γ) * b)⁻¹ =
    (i * (a : Γ) * i⁻¹ * (a : Γ)⁻¹) * (i * (b : Γ) * i⁻¹ * (b : Γ)⁻¹)
  calc i * ((a : Γ) * b) * i⁻¹ * ((a : Γ) * b)⁻¹
      = (i * (a : Γ) * i⁻¹) * ((i * (b : Γ) * i⁻¹ * (b : Γ)⁻¹) * (a : Γ)⁻¹) := by group
    _ = (i * (a : Γ) * i⁻¹) * ((a : Γ)⁻¹ * (i * (b : Γ) * i⁻¹ * (b : Γ)⁻¹)) := by rw [hx]
    _ = (i * (a : Γ) * i⁻¹ * (a : Γ)⁻¹) * (i * (b : Γ) * i⁻¹ * (b : Γ)⁻¹) := by group

theorem conj_conj_eq_of_commutator_mem {Γ : Type} [Group Γ] {E : Subgroup Γ}
    (hab : ∀ x ∈ oTwoIn E, ∀ y ∈ oTwoIn E, x * y = y * x) {i e w : Γ}
    (hi : i ∈ Subgroup.normalizer (E : Set Γ)) (he : e ∈ E) (hw : w ∈ oTwoIn E)
    (hc : i * e * i⁻¹ * e⁻¹ ∈ oTwoIn E) :
    i * (e * w * e⁻¹) * i⁻¹ = e * (i * w * i⁻¹) * e⁻¹ := by
  have hx : e * (i * w * i⁻¹) * e⁻¹ ∈ oTwoIn E :=
    conj_mem_oTwoIn (Subgroup.le_normalizer he) (conj_mem_oTwoIn hi hw)
  calc i * (e * w * e⁻¹) * i⁻¹
      = (i * e * i⁻¹ * e⁻¹) * (e * (i * w * i⁻¹) * e⁻¹) * (i * e * i⁻¹ * e⁻¹)⁻¹ := by group
    _ = e * (i * w * i⁻¹) * e⁻¹ := by rw [hab _ hc _ hx]; group

theorem commHom_conj {Γ : Type} [Group Γ] {E : Subgroup Γ}
    (hab : ∀ x ∈ oTwoIn E, ∀ y ∈ oTwoIn E, x * y = y * x) {i : Γ}
    (hi : i ∈ Subgroup.normalizer (E : Set Γ))
    (hc : ∀ e ∈ E, i * e * i⁻¹ * e⁻¹ ∈ oTwoIn E)
    {ψ : ↥(oTwoIn E) →* Γ}
    (hψ : ∀ w : ↥(oTwoIn E), ψ w = i * (w : Γ) * i⁻¹ * (w : Γ)⁻¹)
    {e : Γ} (he : e ∈ E) (w w' : ↥(oTwoIn E)) (h : (w' : Γ) = e * (w : Γ) * e⁻¹) :
    ψ w' = e * ψ w * e⁻¹ := by
  rw [hψ, hψ, h, conj_conj_eq_of_commutator_mem hab hi he w.2 (hc e he)]
  group

theorem commHom_range_le_commutator {Γ : Type} [Group Γ] {E : Subgroup Γ}
    (hab : ∀ x ∈ oTwoIn E, ∀ y ∈ oTwoIn E, x * y = y * x)
    (hperf : ⁅oTwoIn E, E⁆ = oTwoIn E) {i : Γ}
    (hi : i ∈ Subgroup.normalizer (E : Set Γ))
    (hc : ∀ e ∈ E, i * e * i⁻¹ * e⁻¹ ∈ oTwoIn E)
    {ψ : ↥(oTwoIn E) →* Γ}
    (hψ : ∀ w : ↥(oTwoIn E), ψ w = i * (w : Γ) * i⁻¹ * (w : Γ)⁻¹) :
    ψ.range ≤ ⁅ψ.range, E⁆ := by
  have hgen : ⁅oTwoIn E, E⁆ ≤ (⁅ψ.range, E⁆.comap ψ).map (oTwoIn E).subtype := by
    refine Subgroup.commutator_le.2 fun a ha e he => ?_
    have hea : e * a⁻¹ * e⁻¹ ∈ oTwoIn E :=
      conj_mem_oTwoIn (Subgroup.le_normalizer he) (inv_mem ha)
    have hae : ⁅a, e⁆ ∈ oTwoIn E := by
      have : ⁅a, e⁆ = a * (e * a⁻¹ * e⁻¹) := by rw [commutatorElement_def]; group
      rw [this]
      exact mul_mem ha hea
    refine ⟨⟨⁅a, e⁆, hae⟩, ?_, rfl⟩
    have h1 : ψ ⟨⁅a, e⁆, hae⟩ = ψ ⟨a, ha⟩ * ψ ⟨e * a⁻¹ * e⁻¹, hea⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show ⁅a, e⁆ = a * (e * a⁻¹ * e⁻¹)
      rw [commutatorElement_def]
      group
    have h2 : ψ ⟨e * a⁻¹ * e⁻¹, hea⟩ = e * (ψ ⟨a, ha⟩)⁻¹ * e⁻¹ := by
      have := commHom_conj hab hi hc hψ he (⟨a, ha⟩ : ↥(oTwoIn E))⁻¹
        ⟨e * a⁻¹ * e⁻¹, hea⟩ rfl
      rwa [map_inv] at this
    have h3 : ψ ⟨a, ha⟩ * (e * (ψ ⟨a, ha⟩)⁻¹ * e⁻¹) = ⁅ψ ⟨a, ha⟩, e⁆ := by
      rw [commutatorElement_def]
      group
    show ψ ⟨⁅a, e⁆, hae⟩ ∈ ⁅ψ.range, E⁆
    rw [h1, h2, h3]
    exact Subgroup.commutator_mem_commutator ⟨_, rfl⟩ he
  intro z hz
  obtain ⟨w, rfl⟩ := hz
  obtain ⟨w', hw', hww'⟩ := hgen (hperf.ge w.2)
  have hw : w' = w := Subtype.ext hww'
  subst hw
  exact hw'

theorem exists_ne_one_forall_conj_eq {Γ : Type} [Group Γ] [Finite Γ] {W I : Subgroup Γ}
    (hW : IsPGroup 2 W) (hWne : W ≠ ⊥) (hI : IsPGroup 2 I)
    (hIW : I ≤ Subgroup.normalizer (W : Set Γ)) :
    ∃ w ∈ W, w ≠ 1 ∧ ∀ i ∈ I, i * w * i⁻¹ = w := by
  have hP : IsPGroup 2 ↥(W ⊔ I) := hW.to_sup_of_normal_left' hI hIW
  have hPW : W ⊔ I ≤ Subgroup.normalizer (W : Set Γ) := sup_le Subgroup.le_normalizer hIW
  have hnormal : (W.subgroupOf (W ⊔ I)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPW
  have hnil : Group.IsNilpotent ↥(W ⊔ I) := hP.isNilpotent
  have hne : W.subgroupOf (W ⊔ I) ≠ ⊥ := by
    intro h
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact hWne (disjoint_self.1 (h.mono_right le_sup_left))
  obtain ⟨⟨c, hcW, hcZ⟩, hc1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(c : Γ), hcW, fun h => hc1 ?_, fun i hi => ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · have h1 := Subgroup.mem_center_iff.1 hcZ ⟨i, Subgroup.mem_sup_right hi⟩
    have h2 : i * (c : Γ) = (c : Γ) * i := congrArg Subtype.val h1
    rw [h2]
    group

theorem conj_eq_of_exists_fixed {Γ : Type} [Group Γ] [Finite Γ] {E : Subgroup Γ}
    (hX : IsShortGroup ↥E)
    (hab : ∀ x ∈ oTwoIn E, ∀ y ∈ oTwoIn E, x * y = y * x)
    (hperf : ⁅oTwoIn E, E⁆ = oTwoIn E) {i : Γ}
    (hi : i ∈ Subgroup.normalizer (E : Set Γ))
    (hc : ∀ e ∈ E, i * e * i⁻¹ * e⁻¹ ∈ oTwoIn E)
    {w₀ : Γ} (hw₀ : w₀ ∈ oTwoIn E) (hne : w₀ ≠ 1) (hfix : i * w₀ * i⁻¹ = w₀) :
    ∀ w ∈ oTwoIn E, i * w * i⁻¹ = w := by
  obtain ⟨ψ, hψ⟩ := exists_commHom hab (fun w hw => conj_mem_oTwoIn hi hw)
  have hψW : ∀ w : ↥(oTwoIn E), ψ w ∈ oTwoIn E := fun w => by
    rw [hψ]
    exact mul_mem (conj_mem_oTwoIn hi w.2) (inv_mem w.2)
  have hle : ψ.range ≤ oTwoIn E := by
    rintro _ ⟨w, rfl⟩
    exact hψW w
  have hnorm : ∀ e ∈ E, ∀ z ∈ ψ.range, e * z * e⁻¹ ∈ ψ.range := by
    rintro e he _ ⟨w, rfl⟩
    have hmem : e * (w : Γ) * e⁻¹ ∈ oTwoIn E :=
      conj_mem_oTwoIn (Subgroup.le_normalizer he) w.2
    exact ⟨⟨_, hmem⟩, commHom_conj hab hi hc hψ he w ⟨_, hmem⟩ rfl⟩
  have hcomm := commHom_range_le_commutator hab hperf hi hc hψ
  have hWU : oTwoIn E ≤ blockU E := hperf.ge
  have hNn : ∀ g ∈ E, ∀ n ∈ ψ.range ⊔ blockZ E, g * n * g⁻¹ ∈ ψ.range ⊔ blockZ E := by
    intro g hg
    have hsub : ψ.range ⊔ blockZ E ≤
        (ψ.range ⊔ blockZ E).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun n hn => ?_) (fun n hn => ?_)
      · exact Subgroup.mem_sup_left (hnorm g hg n hn)
      · exact Subgroup.mem_sup_right (conj_mem_blockZ (Subgroup.le_normalizer hg) hn)
    exact fun n hn => hsub hn
  rcases blockU_irred_of_short hX (ψ.range ⊔ blockZ E) le_sup_right
      (sup_le (hle.trans hWU) (blockZ_le_blockU E)) hNn with h | h
  ·
    have hzZ : ψ.range ≤ blockZ E := le_sup_left.trans h.le
    intro w hw
    have h1 : ψ ⟨w, hw⟩ ∈ ⁅ψ.range, E⁆ := hcomm ⟨⟨w, hw⟩, rfl⟩
    have h2 : ⁅ψ.range, E⁆ ≤ ⊥ := by
      refine Subgroup.commutator_le.2 fun z hz e he => ?_
      have hcent : e * z = z * e := Subgroup.mem_centralizer_iff.1 (hzZ hz).2 e he
      rw [Subgroup.mem_bot, commutatorElement_def, ← hcent]
      group
    have h3 : ψ ⟨w, hw⟩ = 1 := Subgroup.mem_bot.1 (h2 h1)
    rw [hψ] at h3
    exact mul_inv_eq_one.1 h3
  ·
    exfalso
    have hWle : oTwoIn E ≤ ψ.range ⊔ blockZ E := fun w hw => h.ge (hWU hw)
    have hnormZ : ψ.range ≤ Subgroup.normalizer (blockZ E : Set Γ) := by
      intro n hn
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      have hzW : z ∈ oTwoIn E := blockU_le_oTwoIn E (blockZ_le_blockU E hz)
      have hnW : n ∈ oTwoIn E := hle hn
      have : n * z * n⁻¹ = z := by
        rw [hab n hnW z hzW]
        group
      rw [this]
      exact hz
    have hsurj : oTwoIn E ≤ ψ.range := by
      calc oTwoIn E = ⁅oTwoIn E, E⁆ := hperf.symm
        _ ≤ ⁅ψ.range ⊔ blockZ E, E⁆ := Subgroup.commutator_mono hWle le_rfl
        _ ≤ ψ.range := by
          refine Subgroup.commutator_le.2 fun g hg e he => ?_
          have hmem : g ∈ ((ψ.range ⊔ blockZ E : Subgroup Γ) : Set Γ) := hg
          rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormZ] at hmem
          obtain ⟨n, hn, z, hz, rfl⟩ := hmem
          have hzc : e * z = z * e := Subgroup.mem_centralizer_iff.1 hz.2 e he
          have h1 : ⁅n * z, e⁆ = ⁅n, e⁆ := by
            rw [commutatorElement_def, commutatorElement_def]
            calc n * z * e * (n * z)⁻¹ * e⁻¹ = n * (z * e) * z⁻¹ * n⁻¹ * e⁻¹ := by group
              _ = n * (e * z) * z⁻¹ * n⁻¹ * e⁻¹ := by rw [← hzc]
              _ = n * e * n⁻¹ * e⁻¹ := by group
          have h2 : n * (e * n⁻¹ * e⁻¹) ∈ ψ.range := by
            refine mul_mem hn ?_
            have : e * n⁻¹ * e⁻¹ = (e * n * e⁻¹)⁻¹ := by group
            rw [this]
            exact inv_mem (hnorm e he n hn)
          have h3 : ⁅n, e⁆ = n * (e * n⁻¹ * e⁻¹) := by
            rw [commutatorElement_def]
            group
          rw [h1, h3]
          exact h2
    obtain ⟨f, hf⟩ : ∃ f : ↥(oTwoIn E) → ↥(oTwoIn E), ∀ w, (f w : Γ) = ψ w :=
      ⟨fun w => ⟨ψ w, hψW w⟩, fun _ => rfl⟩
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨w, hw⟩ := hsurj y.2
      exact ⟨w, Subtype.ext (by rw [hf]; exact hw)⟩
    have hfi : Function.Injective f := Finite.injective_iff_surjective.2 hfs
    have h0 : f ⟨w₀, hw₀⟩ = f 1 := by
      apply Subtype.ext
      rw [hf, hf, map_one, hψ]
      show i * w₀ * i⁻¹ * w₀⁻¹ = 1
      rw [hfix]
      group
    exact hne (congrArg Subtype.val (hfi h0))

theorem centralizes_oTwoIn_of_commutator_le {Γ : Type} [Group Γ] [Finite Γ] {E I : Subgroup Γ}
    (hX : IsShortGroup ↥E)
    (hab : ∀ x ∈ oTwoIn E, ∀ y ∈ oTwoIn E, x * y = y * x)
    (hperf : ⁅oTwoIn E, E⁆ = oTwoIn E)
    (hI2 : IsPGroup 2 I) (hIn : I ≤ Subgroup.normalizer (E : Set Γ))
    (hc : ∀ i ∈ I, ∀ e ∈ E, i * e * i⁻¹ * e⁻¹ ∈ oTwoIn E) :
    ∀ i ∈ I, ∀ w ∈ oTwoIn E, i * w * i⁻¹ = w := by
  have hWne : oTwoIn E ≠ ⊥ := fun h => blockU_ne_bot_of_short hX (hperf.trans h)
  obtain ⟨w₀, hw₀, hne, hfix⟩ := exists_ne_one_forall_conj_eq (isPGroup_oTwoIn E) hWne hI2
    (fun i hi => normalizer_le_normalizer_oTwoIn E (hIn hi))
  intro i hi
  exact conj_eq_of_exists_fixed hX hab hperf (hIn hi) (hc i hi) hw₀ hne (hfix i hi)

end CFSG.CGT.PushingUpLit.Glue

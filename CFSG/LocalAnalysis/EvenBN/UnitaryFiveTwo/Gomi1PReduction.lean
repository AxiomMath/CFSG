module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PFusion
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1PLayer

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open Subgroup CFSG CFSG.ABGLocalTools
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

structure SylowData (t : X) (Y U : Subgroup X) : Prop where
  le : U ≤ Y
  card : Nat.card U = 2 ^ 8
  norm : ∀ u ∈ U, t * u * t⁻¹ ∈ U
  t_not_mem : t ∉ U
  class_two : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, ⁅x, y⁆ * z = z * ⁅x, y⁆
  nonabelian : ∃ x ∈ U, ∃ y ∈ U, x * y ≠ y * x
  elem_abelian : ∃ E : Subgroup X, E ≤ U ∧ Nat.card E = 2 ^ 6 ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a * a = 1
  big_abelian : ∀ x ∈ U, x * x = 1 → x ≠ 1 → ∃ R : Subgroup X, R ≤ U ∧ x ∈ R ∧
    (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) ∧ Nat.card R = 2 ^ 6
  cocycle : ∀ u ∈ U, (u * t) * (u * t) = 1 → ∃ v ∈ U, u * t = v * t * v⁻¹
  card_cent : Nat.card (U ⊓ centralizer ({t} : Set X) : Subgroup X) = 2 ^ 4

structure Gomi1PFacts (Y L : Subgroup X) : Prop where
  simple : IsSimpleGroup L
  nonabelian : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a
  le : Y ≤ L
  normal : L.Normal
  index_odd : ¬ 2 ∣ Y.relIndex L
  centralizer_eq_bot : centralizer (L : Set X) = ⊥
  sylow : ∃ U : Subgroup X, U ≤ Y ∧ IsSylowOf 2 U L ∧ Nat.card U = 2 ^ 8 ∧
    (∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, ⁅x, y⁆ * z = z * ⁅x, y⁆) ∧ (∃ x ∈ U, ∃ y ∈ U, x * y ≠ y * x)
  elem_abelian : ∃ E : Subgroup X, E ≤ Y ∧ Nat.card E = 2 ^ 6 ∧
    (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a * a = 1

@[expose] def Gomi1PIdent (Y L : Subgroup X) : Prop := Gomi1PFacts Y L → L = Y

theorem isPerfect_of_simple_nonabelian {G : Type*} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have hm : ⁅a, b⁆ ∈ commutator G := commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot] at hm
    have : a * b * a⁻¹ * b⁻¹ = 1 := by simpa [commutatorElement_def] using hm
    calc a * b = a * b * a⁻¹ * b⁻¹ * b * a := by group
      _ = b * a := by rw [this]; group
  · exact h

theorem le_commutator_of_simple_nonabelian {Y : Subgroup X} [IsSimpleGroup Y]
    (hnab : ∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a) : Y ≤ commutator X := by
  have : Group.IsPerfect Y := isPerfect_of_simple_nonabelian (by
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩)
  calc Y = ⁅Y, Y⁆ := (Subgroup.commutator_eq_self).symm
    _ ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := commutator_mono le_top le_top

section Data

variable {t : X} {Y U : Subgroup X}

theorem not_conj_mem_of_data (D : SylowData t Y U) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hC : Nat.card (centralizer ({t} : Set X)) = 1440) (g : X) :
    g * t * g⁻¹ ∉ U := by
  intro hc
  have hcc : (g * t * g⁻¹) * (g * t * g⁻¹) = 1 := by
    calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hc1 : g * t * g⁻¹ ≠ 1 := by
    intro h
    apply ht1
    have : t = g⁻¹ * (g * t * g⁻¹) * g := by group
    rw [this, h]; group
  obtain ⟨R, hRU, hcR, hRab, hRcard⟩ := D.big_abelian _ hc hcc hc1
  set R' : Subgroup X := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'
  have hR'card : Nat.card R' = 2 ^ 6 := by
    rw [hR', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hRcard]
  have hR'C : R' ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := hRab r hr _ hcR
    show g⁻¹ * r * g⁻¹⁻¹ * t = t * (g⁻¹ * r * g⁻¹⁻¹)
    calc g⁻¹ * r * g⁻¹⁻¹ * t = g⁻¹ * (r * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * r) * g := by rw [h1]
      _ = t * (g⁻¹ * r * g⁻¹⁻¹) := by group
  have hdvd : Nat.card R' ∣ Nat.card (centralizer ({t} : Set X)) := Subgroup.card_dvd_of_le hR'C
  rw [hR'card, hC] at hdvd
  omega

theorem isPGroup_T_of_data (D : SylowData t Y U) (ht2 : t * t = 1) :
    IsPGroup 2 (U ⊔ zpowers t : Subgroup X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : IsPGroup 2 U := IsPGroup.of_card D.card
  have hnorm : zpowers t ≤ normalizer (U : Set X) := by
    intro g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    rw [mem_normalizer_iff]
    intro h
    rcases zpow_eq_one_or_self ht2 n with h1 | h1
    · rw [h1]; simp
    · rw [h1]
      refine ⟨fun hh => D.norm h hh, fun hh => ?_⟩
      have := D.norm _ hh
      have e : t * (t * h * t⁻¹) * t⁻¹ = h := by
        rw [inv_eq_of_mul_eq_one_right ht2]
        calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
          _ = h := by rw [ht2]; group
      rw [e] at this
      exact this
  exact hU.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self ht2) hnorm

theorem card_T_inf_centralizer_of_data (D : SylowData t Y U) (ht2 : t * t = 1) :
    Nat.card ((U ⊔ zpowers t) ⊓ centralizer ({t} : Set X) : Subgroup X) = 2 ^ 5 := by
  have htC : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
  have heq : (U ⊔ zpowers t) ⊓ centralizer ({t} : Set X) =
      (U ⊓ centralizer ({t} : Set X)) ⊔ zpowers t := by
    apply le_antisymm
    · rintro x ⟨hxT, hxC⟩
      obtain ⟨u, hu, rfl | rfl⟩ := (mem_sup_zpowers_iff_of_normalizes ht2 D.norm).mp hxT
      · exact mem_sup_left ⟨hu, hxC⟩
      · have huC : u ∈ centralizer ({t} : Set X) := by
          have := (centralizer ({t} : Set X)).mul_mem hxC
            ((centralizer ({t} : Set X)).inv_mem htC)
          simpa using this
        exact mul_mem (mem_sup_left ⟨hu, huC⟩) (mem_sup_right (mem_zpowers t))
    · exact le_inf (sup_le_sup_right inf_le_left _)
        (sup_le inf_le_right (zpowers_le.mpr htC))
  rw [heq, card_sup_zpowers_of_normalizes ht2, D.card_cent]
  · rfl
  · intro u hu
    have := mem_centralizer_singleton_iff.mp hu.2
    rw [← this]
    simpa using hu
  · exact fun h => D.t_not_mem h.1

theorem hfus_of_data (D : SylowData t Y U) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hC : Nat.card (centralizer ({t} : Set X)) = 1440) (g : X)
    (hg : g * t * g⁻¹ ∈ U ⊔ zpowers t) :
    ∃ τ ∈ U ⊔ zpowers t, g * t * g⁻¹ = τ * t * τ⁻¹ := by
  obtain ⟨u, hu, hcu | hcu⟩ := (mem_sup_zpowers_iff_of_normalizes ht2 D.norm).mp hg
  · exact absurd (hcu ▸ hu) (not_conj_mem_of_data D ht2 ht1 hC g)
  · have hsq : (u * t) * (u * t) = 1 := by
      rw [← hcu]
      calc (g * t * g⁻¹) * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
        _ = 1 := by rw [ht2]; group
    obtain ⟨v, hv, hvt⟩ := D.cocycle u hu hsq
    exact ⟨v, mem_sup_left hv, by rw [hcu, hvt]⟩

theorem not_isPGroup_of_card_979200 {Y : Subgroup X} (h : Nat.card Y = 979200) :
    ¬ IsPGroup 2 Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hY
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hY
  rw [h] at hn
  have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

theorem gomi1P_facts_of_data [IsSimpleGroup Y]
    (hO : oddCore X = ⊥) (ht2 : t * t = 1) (ht1 : t ≠ 1) (hYcard : Nat.card Y = 979200)
    (htn : ∀ y ∈ Y, t * y * t⁻¹ ∈ Y)
    (hout : ¬ ∃ y ∈ Y, ∀ z ∈ Y, t * z * t⁻¹ = y * z * y⁻¹)
    (hcent : centralizer ({t} : Set X) = (Y ⊓ centralizer ({t} : Set X)) ⊔ zpowers t)
    (hKcard : Nat.card (Y ⊓ centralizer ({t} : Set X) : Subgroup X) = 720)
    (hKZ : ∀ k ∈ Y ⊓ centralizer ({t} : Set X),
      (∀ k' ∈ Y ⊓ centralizer ({t} : Set X), k * k' = k' * k) → k = 1)
    (D : SylowData t Y U) : Gomi1PFacts Y (layer X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htY : t ∉ Y := fun h => hout ⟨t, h, fun z _ => rfl⟩
  have hKt : ∀ k ∈ Y ⊓ centralizer ({t} : Set X), k * t = t * k := fun k hk =>
    mem_centralizer_singleton_iff.mp hk.2
  have hC : Nat.card (centralizer ({t} : Set X)) = 1440 := by
    rw [hcent, card_sup_zpowers_of_normalizes ht2, hKcard]
    · intro k hk
      have h1 := hKt k hk
      have e : t * k * t⁻¹ = k := by
        calc t * k * t⁻¹ = k * t * t⁻¹ := by rw [← h1]
          _ = k := by group
      rw [e]
      exact hk
    · exact fun h => htY h.1
  have hTp : IsPGroup 2 (U ⊔ zpowers t : Subgroup X) := isPGroup_T_of_data D ht2
  have htT : t ∈ U ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hCT : ∃ m : ℕ, Odd m ∧ Nat.card (centralizer ({t} : Set X)) =
      Nat.card ((U ⊔ zpowers t) ⊓ centralizer ({t} : Set X) : Subgroup X) * m :=
    ⟨45, by decide, by rw [hC, card_T_inf_centralizer_of_data D ht2]; norm_num⟩
  have hTsyl : IsSylowOf 2 (U ⊔ zpowers t) ⊤ :=
    isSylowOf_top_of_fusion hTp htT hCT (hfus_of_data D ht2 ht1 hC)
  obtain ⟨-, -, hTidx⟩ := (isSylowOf_iff.mp hTsyl)
  rw [relIndex_top_right] at hTidx
  set P : Sylow 2 X := hTp.toSylow hTidx with hPdef
  have hPT : (P : Subgroup X) = U ⊔ zpowers t := IsPGroup.toSylow_coe hTp hTidx
  have hUP : U ≤ (P : Subgroup X) := hPT ▸ le_sup_left
  have htP : t ∈ (P : Subgroup X) := hPT ▸ htT
  have hidx : (U.subgroupOf (P : Subgroup X)).index = 2 := by
    rw [hPT]; exact index_eq_two_of_normalizes ht2 D.norm D.t_not_mem
  haveI hUn : (U.subgroupOf (P : Subgroup X)).Normal := normal_of_index_eq_two hidx
  have hfus₂ : ∀ g : X, g * t * g⁻¹ ∈ (P : Subgroup X) → g * t * g⁻¹ ∉ U := fun g _ =>
    not_conj_mem_of_data D ht2 ht1 hC g
  have htc : t ∉ commutator X :=
    not_mem_commutator_of_fusion hUP hUn hidx htP ht2 D.t_not_mem hfus₂
  have hYnab : ∃ a ∈ Y, ∃ b ∈ Y, a * b ≠ b * a := by
    obtain ⟨a, ha, b, hb, hab⟩ := D.nonabelian
    exact ⟨a, D.le ha, b, D.le hb, hab⟩
  have hYc : Y ≤ commutator X := le_commutator_of_simple_nonabelian hYnab
  have hUc : U ≤ commutator X := D.le.trans hYc
  have hSyl : IsSylowOf 2 U (commutator X) :=
    isSylowOf_commutator_of_fusion hUP hidx htP htc hUc
  have hp : pCore 2 X = ⊥ :=
    pCore_two_eq_bot (not_isPGroup_of_card_979200 hYcard) ht2 htn hout hcent.le
  have hF : fittingSubgroup X = ⊥ := fitting_eq_bot hO hp
  haveI : (layer X).Characteristic := LocalCores.layer_characteristic
  have htL : t ∉ layer X := fun h => htc (layer_le_commutator h)
  have hLnab : ∃ a ∈ layer X, ∃ b ∈ layer X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hL1 : ∀ x ∈ layer X, x = 1 := fun x hx =>
      eq_one_of_mem_layer_of_commute hF hx fun l hl => hcon l hl x hx
    have hcb := centralizer_layer_eq_bot (X := X) hF
    have hall : ∀ y : X, y = 1 := by
      intro y
      have hy : y ∈ centralizer (layer X : Set X) := by
        rw [mem_centralizer_iff]
        intro l hl
        rw [hL1 l hl]; simp
      rw [hcb] at hy
      exact mem_bot.mp hy
    obtain ⟨a, b, hab⟩ := exists_pair_ne Y
    exact hab (Subtype.ext ((hall a).trans (hall b).symm))
  have hYL : Y ≤ layer X := le_of_normal_of_not_mem ht2 hcent.le hKZ htL hLnab
  have hSylL : IsSylowOf 2 U (layer X) := hSyl.of_le (D.le.trans hYL) layer_le_commutator
  refine ⟨isSimpleGroup_layer_of_sylow hF hYL D.le hSylL, hLnab, hYL, inferInstance, ?_,
    centralizer_layer_eq_bot hF, ⟨U, D.le, hSylL, D.card, D.class_two, D.nonabelian⟩, ?_⟩
  · have h1 := (isSylowOf_iff.mp hSylL).2.2
    rw [← Subgroup.relIndex_mul_relIndex U Y (layer X) D.le hYL] at h1
    exact fun h2 => h1 (h2.mul_left _)
  · obtain ⟨E, hEU, hEc, hEab, hEexp⟩ := D.elem_abelian
    exact ⟨E, hEU.trans D.le, hEc, hEab, hEexp⟩

end Data

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

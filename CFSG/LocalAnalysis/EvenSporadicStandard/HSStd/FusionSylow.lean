module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Fusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.SylowConj

public section

namespace CFSG.EvenSporadicStandard.HSStd

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def SylowFusion {G : Type} [Group G] (L : Subgroup G) (t : G) : Prop :=
  ∃ (S : Subgroup G) (z : G), S ≤ centralizer ({t} : Set G) ∧ IsPGroup 2 S ∧
    ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G)) ∧ z ∈ S ∧ z ∈ L ∧ orderOf z = 2 ∧
    centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z ∧
    ∃ n ∈ normalizer (S : Set G), n * t * n⁻¹ = z * t

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.exists_normalizer_conj_of_fusionData
    (h : StdHyp G L) (hZ : center L = ⊥)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (hout : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2)
    (hFD : FusionData L) {t : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) :
    SylowFusion L t := by
  classical
  unfold SylowFusion
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨z, hz2, hCz, g, hg⟩ :=
    h.exists_conj_eq_mul_of_fusionData_sylow hZ hS hout hFD R ht ht2
  have htM : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hMN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    h.centralizer_le_normalizer ht ht2
  have hLM : L ≤ centralizer ({t} : Set G) := fun l hl =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht l hl)
  set A : Subgroup G := (R : Subgroup L).map L.subtype with hAdef
  have hA : IsPGroup 2 A :=
    (R.isPGroup').of_equiv (Subgroup.equivMapOfInjective _ L.subtype L.subtype_injective)
  have hB : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hAL : A ≤ L := Subgroup.map_subtype_le _
  have hBA : zpowers t ≤ centralizer (A : Set G) := fun b hb => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    rw [mem_centralizer_iff]
    intro a ha
    exact (Commute.zpow_right (show Commute a t from mem_centralizer_iff.1 ht a (hAL ha)) k).eq
  have hP := isPGroup_sup_of_le_centralizer hA hB hBA
  have hPM : A ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le (hAL.trans hLM) (zpowers_le.2 htM)
  have hPM' : IsPGroup 2 ((A ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G))) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  obtain ⟨S₀, hS₀⟩ := hPM'.exists_le_sylow
  set S : Subgroup G := (S₀ : Subgroup (centralizer ({t} : Set G))).map
    (centralizer ({t} : Set G)).subtype with hSdef
  have hSM : S ≤ centralizer ({t} : Set G) := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S :=
    S₀.isPGroup'.of_equiv (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _))
  have hSrel : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G)) := by
    have hsub : S.subgroupOf (centralizer ({t} : Set G)) =
        (S₀ : Subgroup (centralizer ({t} : Set G))) :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    have : S.relIndex (centralizer ({t} : Set G)) =
        (S₀ : Subgroup (centralizer ({t} : Set G))).index := by
      rw [Subgroup.relIndex, hsub]
    rw [this]
    exact S₀.not_dvd_index
  have hmemS : ∀ x ∈ A ⊔ zpowers t, x ∈ S := by
    intro x hx
    have hxS₀ : (⟨x, hPM hx⟩ : centralizer ({t} : Set G)) ∈
        (S₀ : Subgroup (centralizer ({t} : Set G))) :=
      hS₀ (show (⟨x, hPM hx⟩ : centralizer ({t} : Set G)) ∈
        (A ⊔ zpowers t).subgroupOf (centralizer ({t} : Set G)) from hx)
    exact ⟨⟨x, hPM hx⟩, hxS₀, rfl⟩
  have hAS : A ≤ S := fun a ha => hmemS a (mem_sup_left ha)
  have hSL : S ⊓ L = A := by
    refine le_antisymm ?_ (le_inf hAS hAL)
    have hQ : IsPGroup 2 ((S ⊓ L).subgroupOf L) :=
      (hS2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hRQ : (R : Subgroup L) ≤ (S ⊓ L).subgroupOf L := fun r hr =>
      ⟨hAS ⟨r, hr, rfl⟩, r.2⟩
    have hEq := R.is_maximal' hQ hRQ
    intro x hx
    have hx' : (⟨x, hx.2⟩ : L) ∈ (S ⊓ L).subgroupOf L := hx
    rw [hEq] at hx'
    exact ⟨⟨x, hx.2⟩, hx', rfl⟩
  have hzA : ∀ a ∈ A, (a : G) * z = z * a := by
    rintro _ ⟨r, hr, rfl⟩
    have hzc : z ∈ centralizer ((R : Subgroup L) : Set L) := by
      rw [hCz]; exact mem_zpowers z
    exact congrArg Subtype.val (mem_centralizer_iff.1 hzc r hr)
  have hcentA : ∀ w : L, (∀ a ∈ A, (a : G) * w = w * a) → w = 1 ∨ w = z := by
    intro w hw
    have : w ∈ centralizer ((R : Subgroup L) : Set L) := by
      rw [mem_centralizer_iff]
      intro x hx
      exact Subtype.ext (hw x ⟨x, hx, rfl⟩)
    rw [hCz] at this
    exact mem_zpowers_cases_of_orderOf_two hz2 this
  have hz2G : orderOf (z : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have hzS : ∀ s ∈ S, s * (z : G) = (z : G) * s := by
    intro s hs
    have hsN : s ∈ normalizer (L : Set G) := hMN (hSM hs)
    have hsiN : s⁻¹ ∈ normalizer (L : Set G) := hMN (hSM (S.inv_mem hs))
    have hz'L : s * (z : G) * s⁻¹ ∈ L := (mem_normalizer_iff.1 hsN (z : G)).1 z.2
    have hcomm : ∀ a ∈ A, (a : G) * ((⟨s * (z : G) * s⁻¹, hz'L⟩ : L) : G) =
        ((⟨s * (z : G) * s⁻¹, hz'L⟩ : L) : G) * a := by
      intro a ha
      have haL : s⁻¹ * a * s ∈ L := by
        have := (mem_normalizer_iff.1 hsiN a).1 (hAL ha)
        rwa [inv_inv] at this
      have haS : s⁻¹ * a * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) (hAS ha)) hs
      have haA : s⁻¹ * a * s ∈ A := by rw [← hSL]; exact ⟨haS, haL⟩
      have h1 := hzA _ haA
      calc a * (s * z * s⁻¹) = s * ((s⁻¹ * a * s) * z) * s⁻¹ := by group
        _ = s * (z * (s⁻¹ * a * s)) * s⁻¹ := by rw [h1]
        _ = s * z * s⁻¹ * a := by group
    rcases hcentA _ hcomm with h1 | h1
    · exfalso
      have h2 : s * (z : G) * s⁻¹ = 1 := congrArg Subtype.val h1
      have h3 : (z : G) = 1 := by
        calc (z : G) = s⁻¹ * (s * (z : G) * s⁻¹) * s := by group
          _ = 1 := by rw [h2]; group
      rw [h3, orderOf_one] at hz2G
      omega
    · have h2 : s * (z : G) * s⁻¹ = z := congrArg Subtype.val h1
      calc s * (z : G) = s * (z : G) * s⁻¹ * s := by group
        _ = z * s := by rw [h2]
  have hzS' : (z : G) ∈ S := by
    have hzZ : zpowers (z : G) ≤ centralizer (S : Set G) := fun b hb => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      rw [mem_centralizer_iff]
      intro s hs
      exact (Commute.zpow_right (show Commute s (z : G) from hzS s hs) k).eq
    have hzp : IsPGroup 2 (zpowers (z : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2G, pow_one])
    have hSz := isPGroup_sup_of_le_centralizer hS2 hzp hzZ
    have hSzM : S ⊔ zpowers (z : G) ≤ centralizer ({t} : Set G) :=
      sup_le hSM (zpowers_le.2 (hLM z.2))
    have hQ : IsPGroup 2 ((S ⊔ zpowers (z : G)).subgroupOf (centralizer ({t} : Set G))) :=
      hSz.of_equiv (Subgroup.subgroupOfEquivOfLe hSzM).symm
    have hS₀Q : (S₀ : Subgroup (centralizer ({t} : Set G))) ≤
        (S ⊔ zpowers (z : G)).subgroupOf (centralizer ({t} : Set G)) := by
      rintro ⟨x, hx⟩ hxS₀
      exact mem_sup_left ⟨⟨x, hx⟩, hxS₀, rfl⟩
    have hEq := S₀.is_maximal' hQ hS₀Q
    have hzQ : (⟨(z : G), hSzM (mem_sup_right (mem_zpowers _))⟩ :
        centralizer ({t} : Set G)) ∈
        (S ⊔ zpowers (z : G)).subgroupOf (centralizer ({t} : Set G)) :=
      mem_sup_right (mem_zpowers _)
    rw [hEq] at hzQ
    exact ⟨_, hzQ, rfl⟩
  have hSt' : S ≤ centralizer ({(z : G) * t} : Set G) := by
    intro s hs
    rw [mem_centralizer_singleton_iff]
    have hst := mem_centralizer_singleton_iff.1 (hSM hs)
    calc s * ((z : G) * t) = (s * z) * t := by group
      _ = (z * s) * t := by rw [hzS s hs]
      _ = z * (s * t) := by group
      _ = z * (t * s) := by rw [hst]
      _ = (z * t) * s := by group
  obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_conj (t := t) (t' := (z : G) * t) (g := g) hg
    hS2 hSM hSrel hSt'
  refine ⟨S, z, hSM, hS2, hSrel, hzS', z.2, hz2G, ?_, n, hn, hnt⟩
  rw [hSL]
  ext x
  constructor
  · rintro ⟨hxC, hxL⟩
    rcases hcentA ⟨x, hxL⟩ (fun a ha => mem_centralizer_iff.1 hxC a ha) with h1 | h1
    · have : x = 1 := congrArg Subtype.val h1
      rw [this]; exact one_mem _
    · have : x = z := congrArg Subtype.val h1
      rw [this]; exact mem_zpowers _
  · intro hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    have hk : (z : G) ^ k ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      exact (Commute.zpow_right (show Commute a (z : G) from hzA a ha) k).eq
    exact ⟨hk, Subgroup.zpow_mem L z.2 k⟩

end CFSG.EvenSporadicStandard.HSStd

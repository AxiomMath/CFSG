module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Layer
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open scoped Pointwise

section Orbit

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}

theorem RedConfig.le_normalizer_of_forall (h : RedConfig p P z D) (hQ : CFSG.pCore p X = ⊥)
    (hD : ∀ K : Subgroup X, IsComponentOf K ⊤ → D ≤ normalizer (K : Set X))
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : (P : Subgroup X) ≤ normalizer (K : Set X) := by
  classical
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h.ne_two)
  refine le_normalizer_of_card_components_le hp (m := 2) hp3 ?_ P.isPGroup' hK
  intro S hS
  by_contra hlt
  push Not at hlt
  obtain ⟨K₁, h₁S, K₂, h₂S, K₃, h₃S, h₁₂, h₁₃, h₂₃⟩ := Finset.two_lt_card.1 hlt
  have hK₁ := hS K₁ h₁S
  have hK₂ := hS K₂ h₂S
  have hK₃ := hS K₃ h₃S
  have hex : ∀ L : Subgroup X, IsComponentOf L ⊤ → ∃ c ∈ D, c ∈ L ∧ orderOf c = p := by
    intro L hL
    have hdvd : p ∣ Nat.card L :=
      (prime_dvd_card_center_quotient_of_isComponentOf hp h.core hL).trans
        (Subgroup.card_quotient_dvd_card (center L) |>.trans (by exact dvd_refl _))
    obtain ⟨c, hc, hcord⟩ := h.exists_mem_inf_of_normalizes (hD L hL) hdvd
    exact ⟨c, hc.1, hc.2, hcord⟩
  obtain ⟨c₁, hc₁D, hc₁K, hc₁o⟩ := hex K₁ hK₁
  obtain ⟨c₂, hc₂D, hc₂K, hc₂o⟩ := hex K₂ hK₂
  obtain ⟨c₃, hc₃D, hc₃K, hc₃o⟩ := hex K₃ hK₃
  have hcm : ∀ {A B : Subgroup X}, IsComponentOf A ⊤ → IsComponentOf B ⊤ → A ≠ B →
      A ≤ centralizer (B : Set X) := fun hA hB hAB =>
    commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne _ _ hA hB hAB)
  have hZ₁ := center_eq_bot_of_isComponentOf hp h.core hQ hK₁
  have hZ₂ := center_eq_bot_of_isComponentOf hp h.core hQ hK₂
  have hZ₃ := center_eq_bot_of_isComponentOf hp h.core hQ hK₃
  have hKZ : ∀ {K : Subgroup X}, center K = ⊥ → ∀ x ∈ K, x ∈ centralizer (K : Set X) → x = 1 := by
    intro K hZ x hx hxc
    have : (⟨x, hx⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      apply Subtype.ext
      exact mem_centralizer_iff.1 hxc k k.2
    rw [hZ, mem_bot] at this
    exact congrArg Subtype.val this
  have hDcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc₁p : c₁ ^ p = 1 := hc₁o ▸ pow_orderOf_eq_one c₁
  have hc₂p : c₂ ^ p = 1 := hc₂o ▸ pow_orderOf_eq_one c₂
  have hc₃p : c₃ ^ p = 1 := hc₃o ▸ pow_orderOf_eq_one c₃
  have hc₁1 : c₁ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hc₁o; exact hp.one_lt.ne hc₁o
  have hc₂1 : c₂ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hc₂o; exact hp.one_lt.ne hc₂o
  have hc₃1 : c₃ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hc₃o; exact hp.one_lt.ne hc₃o
  have hE₁ : IsElemAbelian p (zpowers c₁) := isElemAbelian_zpowers hc₁p
  have hE₁c : Nat.card (zpowers c₁) = p ^ 1 := by rw [Nat.card_zpowers, hc₁o, pow_one]
  have hc₂E₁ : c₂ ∈ centralizer ((zpowers c₁ : Subgroup X) : Set X) := by
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
    exact ((Commute.zpow_left (show Commute c₁ c₂ from hDcomm c₁ hc₁D c₂ hc₂D) k).eq)
  have hc₂nE₁ : c₂ ∉ zpowers c₁ := by
    intro hmem
    have hK₁le : zpowers c₁ ≤ K₁ := zpowers_le.2 hc₁K
    have : c₂ ∈ centralizer (K₁ : Set X) := hcm hK₂ hK₁ h₁₂.symm hc₂K
    exact hc₂1 (hKZ hZ₁ c₂ (hK₁le hmem) this)
  obtain ⟨hE₂, hE₂c⟩ := isElemAbelian_sup_zpowers hp hE₁ hE₁c hc₂o hc₂E₁ hc₂nE₁
  have hc₃E₂ : c₃ ∈ centralizer ((zpowers c₁ ⊔ zpowers c₂ : Subgroup X) : Set X) := by
    rw [mem_centralizer_iff]
    intro w hw
    have hle : zpowers c₁ ⊔ zpowers c₂ ≤ centralizer ({c₃} : Set X) := by
      refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
      · exact mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact hDcomm c₃ hc₃D c₁ hc₁D
      · exact mem_centralizer_iff.2 fun y hy => by
          rw [Set.mem_singleton_iff.1 hy]; exact hDcomm c₃ hc₃D c₂ hc₂D
    exact (mem_centralizer_iff.1 (hle hw) c₃ (Set.mem_singleton _)).symm
  have hc₃nE₂ : c₃ ∉ zpowers c₁ ⊔ zpowers c₂ := by
    intro hmem
    have hle : zpowers c₁ ⊔ zpowers c₂ ≤ centralizer (K₃ : Set X) :=
      sup_le (zpowers_le.2 (hcm hK₁ hK₃ h₁₃ hc₁K)) (zpowers_le.2 (hcm hK₂ hK₃ h₂₃ hc₂K))
    exact hc₃1 (hKZ hZ₃ c₃ hc₃K (hle hmem))
  obtain ⟨hE₃, hE₃c⟩ := isElemAbelian_sup_zpowers hp hE₂ hE₂c hc₃o hc₃E₂ hc₃nE₂
  have hE₃D : zpowers c₁ ⊔ zpowers c₂ ⊔ zpowers c₃ ≤ D :=
    sup_le (sup_le (zpowers_le.2 hc₁D) (zpowers_le.2 hc₂D)) (zpowers_le.2 hc₃D)
  have := Subgroup.card_le_of_le hE₃D
  rw [hE₃c, h.card] at this
  have hp1 := hp.one_lt
  have : p ^ 3 ≤ p ^ 2 := by simpa using this
  have := (Nat.pow_le_pow_iff_right hp1).1 this
  omega


theorem orbit_three {d : X} (hd3 : d ^ 3 = 1) {K₁ : Subgroup X} (hK₁ : IsComponentOf K₁ ⊤)
    (hnd : d ∉ normalizer (K₁ : Set X))
    (hcard : ∀ S : Finset (Subgroup X), (∀ K ∈ S, IsComponentOf K ⊤) → S.card ≤ 3) :
    ∃ K₂ K₃ : Subgroup X, K₂ = MulAut.conj d • K₁ ∧ K₃ = MulAut.conj d • K₂ ∧
      IsComponentOf K₂ ⊤ ∧ IsComponentOf K₃ ⊤ ∧ K₁ ≠ K₂ ∧ K₁ ≠ K₃ ∧ K₂ ≠ K₃ ∧
      MulAut.conj d • K₃ = K₁ ∧
      ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K₁ ∨ L = K₂ ∨ L = K₃ := by
  classical
  have hK₂ := isComponentOf_conj_smul hK₁ d
  have hK₃ := isComponentOf_conj_smul hK₂ d
  have h12 : K₁ ≠ MulAut.conj d • K₁ := fun h =>
    hnd ((conj_smul_eq_self_iff d K₁).1 h.symm)
  have hc3 : MulAut.conj d • (MulAut.conj d • (MulAut.conj d • K₁)) = K₁ := by
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, ← pow_three', hd3, map_one, one_smul]
  have h13 : K₁ ≠ MulAut.conj d • (MulAut.conj d • K₁) := fun h => by
    apply h12
    calc K₁ = MulAut.conj d • (MulAut.conj d • (MulAut.conj d • K₁)) := hc3.symm
      _ = MulAut.conj d • K₁ := by rw [← h]
  have h23 : MulAut.conj d • K₁ ≠ MulAut.conj d • (MulAut.conj d • K₁) := fun h =>
    h12 (MulAction.injective (MulAut.conj d) h)
  refine ⟨MulAut.conj d • K₁, MulAut.conj d • (MulAut.conj d • K₁), rfl, rfl, hK₂, hK₃, h12,
    h13, h23, hc3, ?_⟩
  intro L hL
  by_contra hne
  push Not at hne
  obtain ⟨hL1, hL2, hL3⟩ := hne
  have := hcard {K₁, MulAut.conj d • K₁, MulAut.conj d • (MulAut.conj d • K₁), L} (by
    intro K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl | rfl
    exacts [hK₁, hK₂, hK₃, hL])
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_singleton] at this
  · omega
  · simpa using hL3.symm
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h23, hL2.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h12, h13, hL1.symm⟩

theorem eq_one_of_central_in_layer (hZ : ∀ K : Subgroup X, IsComponentOf K ⊤ → center K = ⊥)
    {w : X} (hw : w ∈ CFSG.layer X) (hc : ∀ x ∈ CFSG.layer X, x * w = w * x) : w = 1 := by
  have hcen : (⟨w, hw⟩ : CFSG.layer X) ∈ center (CFSG.layer X) := by
    rw [mem_center_iff]
    intro x
    apply Subtype.ext
    exact hc x x.2
  have h1 := (CFSG.LocalCores.layer_center (G := X)).1
  have hbot : (⨆ K : CFSG.LocalCores.ComponentIndex X, (center K.1).map K.1.subtype) = ⊥ := by
    refine iSup_eq_bot.2 fun K => ?_
    rw [hZ K.1 ((CFSG.isComponent_iff_open K.1).1 K.2), Subgroup.map_bot]
  have hmem : w ∈ (center (CFSG.layer X)).map (CFSG.layer X).subtype := ⟨⟨w, hw⟩, hcen, rfl⟩
  rw [h1, hbot, mem_bot] at hmem
  exact hmem

theorem not_mem_sup_of_cycle (hZ : ∀ K : Subgroup X, IsComponentOf K ⊤ → center K = ⊥)
    {d w : X} (hdw : d * w = w * d) {K₁ K₂ K₃ : Subgroup X}
    (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) (h₃ : IsComponentOf K₃ ⊤)
    (h₁₂ : K₁ ≠ K₂) (h₁₃ : K₁ ≠ K₃) (h₂₃ : K₂ ≠ K₃)
    (hall : ∀ L : Subgroup X, IsComponentOf L ⊤ → L = K₁ ∨ L = K₂ ∨ L = K₃)
    (hc₁ : MulAut.conj d • K₁ = K₂) (hc₂ : MulAut.conj d • K₂ = K₃)
    (hc₃ : MulAut.conj d • K₃ = K₁) (hw : w ∈ CFSG.layer X) (hw1 : w ≠ 1) :
    w ∉ K₂ ⊔ K₃ := by
  classical
  have hcm : ∀ {A B : Subgroup X}, IsComponentOf A ⊤ → IsComponentOf B ⊤ → A ≠ B →
      A ≤ centralizer (B : Set X) := fun hA hB hAB =>
    commutator_eq_bot_iff_le_centralizer.mp
      (ComponentClassification.LocalComponents.commute_of_ne _ _ hA hB hAB)
  have hshift : ∀ A B : Subgroup X, w ∈ A ⊔ B → w ∈ (MulAut.conj d • A) ⊔ (MulAut.conj d • B) := by
    intro A B hAB
    have h1 : MulAut.conj d • (A ⊔ B) = (MulAut.conj d • A) ⊔ (MulAut.conj d • B) :=
      Subgroup.map_sup _ _ _
    have h2 : MulAut.conj d w ∈ MulAut.conj d • (A ⊔ B) := Subgroup.mem_map_of_mem _ hAB
    have h3 : MulAut.conj d w = w := by
      rw [MulAut.conj_apply]
      calc d * w * d⁻¹ = (w * d) * d⁻¹ := by rw [hdw]
        _ = w := by group
    rw [h3, h1] at h2
    exact h2
  intro hmem
  have hmem₂ : w ∈ K₃ ⊔ K₁ := by
    have := hshift _ _ hmem
    rwa [hc₂, hc₃] at this
  have hmem₃ : w ∈ K₁ ⊔ K₂ := by
    have := hshift _ _ hmem₂
    rwa [hc₃, hc₁] at this
  have hw1c : w ∈ centralizer (K₁ : Set X) :=
    (sup_le (hcm h₂ h₁ h₁₂.symm) (hcm h₃ h₁ h₁₃.symm)) hmem
  have hw2c : w ∈ centralizer (K₂ : Set X) :=
    (sup_le (hcm h₃ h₂ h₂₃.symm) (hcm h₁ h₂ h₁₂)) hmem₂
  have hw3c : w ∈ centralizer (K₃ : Set X) :=
    (sup_le (hcm h₁ h₃ h₁₃) (hcm h₂ h₃ h₂₃)) hmem₃
  refine hw1 (eq_one_of_central_in_layer hZ hw ?_)
  intro x hx
  have hlayer : CFSG.layer X ≤ centralizer ({w} : Set X) := by
    rw [CFSG.layer.eq_sSup]
    refine sSup_le fun L hL => ?_
    rcases hall L ((CFSG.isComponent_iff_open L).1 hL) with rfl | rfl | rfl
    · intro y hy; exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hw1c y hy))
    · intro y hy; exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hw2c y hy))
    · intro y hy; exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hw3c y hy))
  exact (mem_centralizer_singleton_iff.1 (hlayer hx))

theorem RedConfig.mem_layer (h : RedConfig p P z D) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    z ∈ CFSG.layer X := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hch : (CFSG.layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  haveI : (CFSG.layer X).Normal := inferInstance
  obtain ⟨t, htRK, ht, -⟩ := exists_mem_sylow_inf_component hp h.ne_two h.core P hK
  have hN : (P : Subgroup X) ⊓ CFSG.layer X ≠ ⊥ := by
    intro hbot
    have htl : t ∈ (P : Subgroup X) ⊓ CFSG.layer X := ⟨htRK.1, le_layer_of_isComponentOf hK htRK.2⟩
    rw [hbot, mem_bot] at htl
    rw [htl, orderOf_one] at ht
    exact hp.one_lt.ne ht
  have hz := mem_of_normalizing_ne_bot hp P.isPGroup' hN inf_le_left
    ((le_inf le_normalizer (by rw [normalizer_eq_top]; exact le_top)).trans
      inf_normalizer_le_normalizer_inf) h.ord h.unique
  exact hz.2

end Orbit

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2A7B_Data
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mul_comm_of_mem_isElemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hE ha hb

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normalizes {X N : Subgroup G}
    (hXN : X ≤ normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) =
      Nat.card X * Nat.card N := by
  have : (N.subgroupOf (X ⊔ N)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have : (N.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

omit [Finite G] in
theorem le_normalizer_of_le_of_isElemAbelian {p : ℕ} {E A B : Subgroup G}
    (hE : IsElemAbelian p E) (hA : A ≤ E) (hB : B ≤ E) : A ≤ normalizer (B : Set G) := by
  rw [le_normalizer_iff]
  intro a ha b hb
  rw [mul_inv_eq_iff_eq_mul.mpr (mul_comm_of_mem_isElemAbelian hE (hA ha) (hB hb))]
  exact hb

omit [Finite G] in
theorem card_sup_eq_mul_of_inf_eq_bot_of_isElemAbelian {p : ℕ} {E A B : Subgroup G}
    (hE : IsElemAbelian p E) (hA : A ≤ E) (hB : B ≤ E) (hAB : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h := card_sup_mul_card_inf_of_normalizes (le_normalizer_of_le_of_isElemAbelian hE hA hB)
  rwa [hAB, Subgroup.card_bot, mul_one] at h

theorem inf_eq_sup_eq_of_isElemAbelian_card_eq {V S B : Subgroup G}
    (hSV : S ≤ V) (hSn : V ≤ normalizer (S : Set G))
    (hquad : ∀ x ∈ V, x ∉ S → S ⊓ centralizer ({x} : Set G) = S ⊓ centralizer (V : Set G))
    (hidx : Nat.card V * Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G) ≤
      Nat.card S * Nat.card S)
    (hB : IsElemAbelian 2 B) (hBV : B ≤ V) (hBc : Nat.card B = Nat.card S) (hBS : B ≠ S) :
    B ⊓ S = S ⊓ centralizer (V : Set G) ∧ B ⊔ S = V := by
  have hBnS : ¬ B ≤ S := fun hle => hBS (Subgroup.eq_of_le_of_card_ge hle hBc.ge)
  obtain ⟨b₀, hb₀B, hb₀S⟩ : ∃ b₀ ∈ B, b₀ ∉ S := by
    by_contra hcon
    exact hBnS fun x hx => by_contra fun hxS => hcon ⟨x, hx, hxS⟩
  have hinfC : B ⊓ S ≤ S ⊓ centralizer (V : Set G) := by
    intro y hy
    have hyc : y ∈ S ⊓ centralizer ({b₀} : Set G) :=
      ⟨hy.2, mem_centralizer_singleton_iff.mpr (mul_comm_of_mem_isElemAbelian hB hy.1 hb₀B)⟩
    rwa [hquad b₀ (hBV hb₀B) hb₀S] at hyc
  have hprod := card_sup_mul_card_inf_of_normalizes (hBV.trans hSn)
  rw [hBc] at hprod
  have hTV : B ⊔ S ≤ V := sup_le hBV hSV
  have hle1 := Subgroup.card_le_of_le hinfC
  have hle2 := Subgroup.card_le_of_le hTV
  have hTpos : 0 < Nat.card (B ⊔ S : Subgroup G) := Nat.card_pos
  have hCpos : 0 < Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G) := Nat.card_pos
  have hI : Nat.card (B ⊓ S : Subgroup G) =
      Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G) := by
    refine le_antisymm hle1 (Nat.le_of_mul_le_mul_left ?_ hTpos)
    calc Nat.card (B ⊔ S : Subgroup G) * Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G)
        ≤ Nat.card V * Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hle2
      _ ≤ Nat.card S * Nat.card S := hidx
      _ = Nat.card (B ⊔ S : Subgroup G) * Nat.card (B ⊓ S : Subgroup G) := hprod.symm
  have hT : Nat.card (B ⊔ S : Subgroup G) = Nat.card V := by
    refine le_antisymm hle2 (Nat.le_of_mul_le_mul_right ?_ hCpos)
    calc Nat.card V * Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G)
        ≤ Nat.card S * Nat.card S := hidx
      _ = Nat.card (B ⊔ S : Subgroup G) * Nat.card (B ⊓ S : Subgroup G) := hprod.symm
      _ = Nat.card (B ⊔ S : Subgroup G) * Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G) := by
          rw [hI]
  exact ⟨Subgroup.eq_of_le_of_card_ge hinfC hI.ge, Subgroup.eq_of_le_of_card_ge hTV hT.ge⟩

theorem eq_of_isElemAbelian_card_eq_of_quad {V S B B' : Subgroup G}
    (hSV : S ≤ V) (hSn : V ≤ normalizer (S : Set G)) (hS : IsElemAbelian 2 S)
    (hquad : ∀ x ∈ V, x ∉ S → S ⊓ centralizer ({x} : Set G) = S ⊓ centralizer (V : Set G))
    (hidx : Nat.card V * Nat.card (S ⊓ centralizer (V : Set G) : Subgroup G) ≤
      Nat.card S * Nat.card S)
    (hB : IsElemAbelian 2 B) (hBV : B ≤ V) (hBc : Nat.card B = Nat.card S)
    (hB' : IsElemAbelian 2 B') (hB'V : B' ≤ V) (hB'c : Nat.card B' = Nat.card S)
    (hBS : B ≠ S) (hB'S : B' ≠ S) : B = B' := by
  obtain ⟨hBinf, hBsup⟩ := inf_eq_sup_eq_of_isElemAbelian_card_eq hSV hSn hquad hidx hB hBV hBc hBS
  obtain ⟨hB'inf, -⟩ :=
    inf_eq_sup_eq_of_isElemAbelian_card_eq hSV hSn hquad hidx hB' hB'V hB'c hB'S
  have hle : B' ≤ B := by
    intro b' hb'
    have hmem : b' ∈ ((B ⊔ S : Subgroup G) : Set G) := by
      rw [hBsup]
      exact hB'V hb'
    rw [coe_mul_of_left_le_normalizer_right B S (hBV.trans hSn)] at hmem
    obtain ⟨b, hb, u, hu, rfl⟩ := hmem
    by_cases hbS : b ∈ S
    · have : b * u ∈ B ⊓ S := by
        rw [hBinf, ← hB'inf]
        exact ⟨hb', mul_mem hbS hu⟩
      exact this.1
    · have hb2 : b * b = 1 := by
        rw [← sq]
        exact hB.2 b hb
      have hu2 : u * u = 1 := by
        rw [← sq]
        exact hS.2 u hu
      have hbu2 : b * u * (b * u) = 1 := by
        rw [← sq]
        exact hB'.2 _ hb'
      have h1 : b * u * b = u :=
        calc b * u * b = b * u * b * (u * u) := by rw [hu2, mul_one]
          _ = b * u * (b * u) * u := by simp only [mul_assoc]
          _ = u := by rw [hbu2, one_mul]
      have h2 : u * b = b * u :=
        calc u * b = b * u * b * b := by rw [h1]
          _ = b * u * (b * b) := mul_assoc _ _ _
          _ = b * u := by rw [hb2, mul_one]
      have huC : u ∈ S ⊓ centralizer ({b} : Set G) := ⟨hu, mem_centralizer_singleton_iff.mpr h2⟩
      rw [hquad b (hBV hb) hbS, ← hBinf] at huC
      exact mul_mem hb huC.1
  exact (Subgroup.eq_of_le_of_card_ge hle (hBc.trans hB'c.symm).le).symm

omit [Finite G] in
theorem commute_mul_iff_of_commute {u w v : G} (h : Commute w v) :
    Commute (u * w) v ↔ Commute u v :=
  ⟨fun hu => by simpa using hu.mul_left h.inv_left, fun hu => hu.mul_left h⟩

omit [Finite G] in
theorem a7_inf_centralizer_le {D H V J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hel : IsElemAbelian 2 (pCoreOf 2 H)) :
    pCoreOf 2 H ⊓ centralizer (J₁ : Set G) ≤ centralizer (V : Set G) := by
  intro w hw
  rw [mem_centralizer_iff]
  intro v hv
  have hle : J₁ ⊔ pCoreOf 2 H ≤ centralizer ({w} : Set G) := by
    refine sup_le (fun j hj => ?_) (fun s hs => ?_)
    · exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hw.2 j hj)
    · exact mem_centralizer_singleton_iff.mpr (mul_comm_of_mem_isElemAbelian hel hs hw.1)
  exact mem_centralizer_singleton_iff.mp (hle (hdata.V_le hv))

omit [Finite G] in
theorem a7_exists_mul_eq {D H V J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hel : IsElemAbelian 2 (pCoreOf 2 H)) {w : G} (hw : w ∈ pCoreOf 2 H) :
    ∃ u ∈ U, ∃ w₀ ∈ pCoreOf 2 H ⊓ centralizer (J₁ : Set G), u * w₀ = w := by
  have hcent : w ∈ centralizer (pCoreOf 2 H : Set G) :=
    mem_centralizer_iff.mpr fun h hh => mul_comm_of_mem_isElemAbelian hel hh hw
  have hmem := hdata.split w hw hcent (hel.2 w hw)
  have hnorm : U ≤ normalizer ((pCoreOf 2 H ⊓ centralizer (J₁ : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_le_of_isElemAbelian hel hdata.U_le inf_le_left
  have hmem' : w ∈ ((U ⊔ (pCoreOf 2 H ⊓ centralizer (J₁ : Set G)) : Subgroup G) : Set G) := hmem
  rw [coe_mul_of_left_le_normalizer_right U _ hnorm] at hmem'
  exact hmem'

omit [Finite G] in
theorem a7_inf_centralizer_eq {D H V J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hel : IsElemAbelian 2 (pCoreOf 2 H)) {x : G} (hx : x ∈ V) (hxS : x ∉ pCoreOf 2 H) :
    pCoreOf 2 H ⊓ centralizer ({x} : Set G) = pCoreOf 2 H ⊓ centralizer (V : Set G) := by
  have hW := a7_inf_centralizer_le hdata hel
  refine le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hx)))
  rintro w ⟨hwS, hwx⟩
  obtain ⟨u, hu, w₀, hw₀, rfl⟩ := a7_exists_mul_eq hdata hel hwS
  refine ⟨hwS, mem_centralizer_iff.mpr fun v hv => ?_⟩
  have hc : ∀ v ∈ V, Commute w₀ v := fun v hv => (mem_centralizer_iff.mp (hW hw₀) v hv).symm
  have hux : u ∈ U ⊓ centralizer ({x} : Set G) :=
    ⟨hu, mem_centralizer_singleton_iff.mpr
      ((commute_mul_iff_of_commute (hc x hx)).mp (mem_centralizer_singleton_iff.mp hwx))⟩
  rw [hdata.quad x hx hxS] at hux
  have huv : Commute u v := (mem_centralizer_iff.mp hux.2 v hv).symm
  exact ((commute_mul_iff_of_commute (hc v hv)).mpr huv).symm

omit [Finite G] in
theorem a7_card_mul_le {D H V J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hel : IsElemAbelian 2 (pCoreOf 2 H)) (hcard : Nat.card V = 4 * Nat.card (pCoreOf 2 H)) :
    Nat.card V * Nat.card (pCoreOf 2 H ⊓ centralizer (V : Set G) : Subgroup G) ≤
      Nat.card (pCoreOf 2 H) * Nat.card (pCoreOf 2 H) := by
  have hW := a7_inf_centralizer_le hdata hel
  have hUW : U ⊓ (pCoreOf 2 H ⊓ centralizer (J₁ : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ U ⊓ centralizer (J₁ : Set G) := ⟨hx.1, hx.2.2⟩
    rw [hdata.inter] at hx'
    exact hx'
  have hSsup : U ⊔ (pCoreOf 2 H ⊓ centralizer (J₁ : Set G)) = pCoreOf 2 H :=
    le_antisymm (sup_le hdata.U_le inf_le_left) fun w hw =>
      hdata.split w hw (mem_centralizer_iff.mpr fun h hh => mul_comm_of_mem_isElemAbelian hel hh hw)
        (hel.2 w hw)
  have hSC : pCoreOf 2 H ⊓ centralizer (V : Set G) =
      (U ⊓ centralizer (V : Set G)) ⊔ (pCoreOf 2 H ⊓ centralizer (J₁ : Set G)) := by
    refine le_antisymm ?_ (sup_le (le_inf (inf_le_left.trans hdata.U_le) inf_le_right)
      (le_inf inf_le_left hW))
    rintro w ⟨hwS, hwV⟩
    obtain ⟨u, hu, w₀, hw₀, rfl⟩ := a7_exists_mul_eq hdata hel hwS
    have hc : ∀ v ∈ V, Commute w₀ v := fun v hv => (mem_centralizer_iff.mp (hW hw₀) v hv).symm
    refine mul_mem_sup ⟨hu, mem_centralizer_iff.mpr fun v hv => ?_⟩ hw₀
    have h1 : Commute (u * w₀) v := (mem_centralizer_iff.mp hwV v hv).symm
    exact ((commute_mul_iff_of_commute (hc v hv)).mp h1).symm
  have hCU4 : Nat.card (U ⊓ centralizer (V : Set G) : Subgroup G) = 4 := by
    have h := hdata.idx
    rw [hdata.card_U] at h
    omega
  have hCUW : (U ⊓ centralizer (V : Set G)) ⊓ (pCoreOf 2 H ⊓ centralizer (J₁ : Set G)) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_right _ inf_le_left).trans hUW.le)
  have h1 : Nat.card (pCoreOf 2 H) =
      16 * Nat.card (pCoreOf 2 H ⊓ centralizer (J₁ : Set G) : Subgroup G) := by
    have h := card_sup_eq_mul_of_inf_eq_bot_of_isElemAbelian hel hdata.U_le inf_le_left hUW
    rwa [hSsup, hdata.card_U] at h
  have h2 : Nat.card (pCoreOf 2 H ⊓ centralizer (V : Set G) : Subgroup G) =
      4 * Nat.card (pCoreOf 2 H ⊓ centralizer (J₁ : Set G) : Subgroup G) := by
    rw [hSC, card_sup_eq_mul_of_inf_eq_bot_of_isElemAbelian hel (inf_le_left.trans hdata.U_le)
      inf_le_left hCUW, hCU4]
  rw [hcard, h2, h1]
  exact le_of_eq (by ring)

theorem a7_orbit_pCore_le_two {D H V J₁ U : Subgroup G} (hdata : A7ModuleData D H V J₁ U)
    (hSV : pCoreOf 2 H ≤ V) (hel : IsElemAbelian 2 (pCoreOf 2 H))
    (hcard : Nat.card V = 4 * Nat.card (pCoreOf 2 H))
    (hVn : V ≤ normalizer (pCoreOf 2 H : Set G)) :
    ∃ S₁ : Subgroup G, ∀ g ∈ normalizer (V : Set G),
      (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = pCoreOf 2 H ∨
        (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = S₁ := by
  have hquad : ∀ x ∈ V, x ∉ pCoreOf 2 H →
      pCoreOf 2 H ⊓ centralizer ({x} : Set G) = pCoreOf 2 H ⊓ centralizer (V : Set G) :=
    fun x hx hxS => a7_inf_centralizer_eq hdata hel hx hxS
  have hidx := a7_card_mul_le hdata hel hcard
  have hconj : ∀ g ∈ normalizer (V : Set G),
      (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom ≤ V ∧
        IsElemAbelian 2 ((pCoreOf 2 H).map (MulAut.conj g).toMonoidHom) ∧
        Nat.card ((pCoreOf 2 H).map (MulAut.conj g).toMonoidHom) = Nat.card (pCoreOf 2 H) := by
    intro g hg
    refine ⟨?_, CFSG.SectionRank.isElemAbelian_map hel _, ?_⟩
    · calc (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom
          ≤ V.map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hSV
        _ = V := mem_normalizer_iff_map_conj_eq.mp hg
    · exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  by_cases hex : ∃ E : Subgroup G, E ≤ V ∧ IsElemAbelian 2 E ∧
      Nat.card E = Nat.card (pCoreOf 2 H) ∧ E ≠ pCoreOf 2 H
  · obtain ⟨E, hEV, hEel, hEc, hES⟩ := hex
    refine ⟨E, fun g hg => ?_⟩
    by_cases h : (pCoreOf 2 H).map (MulAut.conj g).toMonoidHom = pCoreOf 2 H
    · exact Or.inl h
    · obtain ⟨h1, h2, h3⟩ := hconj g hg
      exact Or.inr
        (eq_of_isElemAbelian_card_eq_of_quad hSV hVn hel hquad hidx h2 h1 h3 hEel hEV hEc h hES)
  · refine ⟨⊥, fun g hg => Or.inl ?_⟩
    by_contra h
    obtain ⟨h1, h2, h3⟩ := hconj g hg
    exact hex ⟨_, h1, h2, h3, h⟩

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CPComp
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case1Misc
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
  (relPPrimeCore_eq_map relPPrimeCore_normal)

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H E : Subgroup G} {k : ℕ}

theorem isPComponentIn_map_subtype {L : Subgroup ↥H} (hL : CFSG.IsPComponent p L) :
    IsPComponentIn p (L.map H.subtype) H := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨l, -, rfl⟩
    exact l.2
  · have : (L.map H.subtype).subgroupOf H = L :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
    rw [this]
    exact hL

theorem le_pLayerIn {L : Subgroup G} (hL : IsPComponentIn p L H) : L ≤ pLayerIn p H := by
  have h1 : L.subgroupOf H ≤ CFSG.pLayer ↥H p := le_pLayer hL.2
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hL.1] at h2

theorem isPComponentIn_conj {L : Subgroup G} (hL : IsPComponentIn p L H) {y : G} (hy : y ∈ H) :
    IsPComponentIn p (L.map (MulAut.conj y).toMonoidHom) H := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    exact H.mul_mem (H.mul_mem hy (hL.1 hl)) (H.inv_mem hy)
  · have h1 : (L.map (MulAut.conj y).toMonoidHom).subgroupOf H =
        (L.subgroupOf H).map (MulAut.conj (⟨y, hy⟩ : ↥H)).toMonoidHom := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨a, ha, haz⟩
        refine ⟨⟨a, hL.1 ha⟩, ha, ?_⟩
        exact Subtype.ext (by simpa using haz)
      · rintro ⟨b, hb, hbz⟩
        refine ⟨b, hb, ?_⟩
        simpa using congrArg Subtype.val hbz
    rw [h1]
    exact isPComponent_map p (MulAut.conj (⟨y, hy⟩ : ↥H)) hL.2

theorem conj_mem_sSup {S : Set (Subgroup G)} {y : G}
    (hS : ∀ Y ∈ S, Y.map (MulAut.conj y).toMonoidHom ∈ S) {x : G} (hx : x ∈ sSup S) :
    y * x * y⁻¹ ∈ sSup S := by
  have h : (sSup S).map (MulAut.conj y).toMonoidHom ≤ sSup S := by
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun Y hY => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup (hS Y hY)
  exact h (Subgroup.mem_map_of_mem _ hx)

theorem conj_mem_kSub {y : G} (hyH : y ∈ H) (hyM : y ∈ M) {x : G} (hx : x ∈ kSub p M H) :
    y * x * y⁻¹ ∈ kSub p M H := by
  unfold kSub at hx ⊢
  split_ifs at hx ⊢ with hJ
  · refine conj_mem_sSup (S := {Y : Subgroup G | Y ≤ H ∧ Nat.card Y = p}) ?_ hx
    intro Y hY
    refine ⟨?_, ?_⟩
    · rintro _ ⟨l, hl, rfl⟩
      exact H.mul_mem (H.mul_mem hyH (hY.1 hl)) (H.inv_mem hyH)
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj y).toMonoidHom)
        (MulAut.conj y).injective]
      exact hY.2
  · refine conj_mem_sSup (S := {Y : Subgroup G | IsPComponentIn p Y H ∧ ¬ Y ≤ M}) ?_ hx
    intro Y hY
    refine ⟨isPComponentIn_conj hY.1 hyH, ?_⟩
    intro hle
    apply hY.2
    intro z hz
    have h1 : y * z * y⁻¹ ∈ M := hle ⟨z, hz, rfl⟩
    have h2 := M.mul_mem (M.mul_mem (M.inv_mem hyM) h1) hyM
    simpa [mul_assoc] using h2

private theorem comm_conj_aux {Γ : Type*} [Group Γ] (a b c : Γ)
    (h : a⁻¹ * b * a * c = c * (a⁻¹ * b * a)) : b * (a * c * a⁻¹) = a * c * a⁻¹ * b := by
  calc b * (a * c * a⁻¹) = a * (a⁻¹ * b * a * c) * a⁻¹ := by group
    _ = a * (c * (a⁻¹ * b * a)) * a⁻¹ := by rw [h]
    _ = a * c * a⁻¹ * b := by group

theorem conj_mem_xSub {y : G} (hyH : y ∈ H) (hyM : y ∈ M) {x : G} (hx : x ∈ xSub p M H) :
    y * x * y⁻¹ ∈ xSub p M H := by
  obtain ⟨z, hz, rfl⟩ := hx
  set π := QuotientGroup.mk' (primeComplementCore (G := ↥H) p) with hπ
  set hy : ↥H := ⟨y, hyH⟩ with hhy
  have hz' : π z ∈ centralizer ((kStar p M H : Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
      Set (↥H ⧸ primeComplementCore (G := ↥H) p)) := hz
  refine ⟨hy * z * hy⁻¹, ?_, rfl⟩
  show π (hy * z * hy⁻¹) ∈ centralizer ((kStar p M H :
    Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
      Set (↥H ⧸ primeComplementCore (G := ↥H) p))
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨u, hu, rfl⟩ := hw
  have hu0 : (u : G) ∈ kSub p M H := hu
  have hu' : hy⁻¹ * u * hy ∈ (kSub p M H).subgroupOf H := by
    have h3 : y⁻¹ * (u : G) * y⁻¹⁻¹ ∈ kSub p M H :=
      conj_mem_kSub (p := p) (M := M) (H := H) (H.inv_mem hyH) (M.inv_mem hyM) hu0
    show ((hy⁻¹ * u * hy : ↥H) : G) ∈ kSub p M H
    simpa using h3
  have hc := (mem_centralizer_iff.mp hz') (π (hy⁻¹ * u * hy)) ⟨hy⁻¹ * u * hy, hu', rfl⟩
  have hc2 : (π hy)⁻¹ * π u * π hy * π z = π z * ((π hy)⁻¹ * π u * π hy) := by
    simpa only [map_mul, map_inv] using hc
  simp only [map_mul, map_inv]
  exact comm_conj_aux _ _ _ hc2

theorem relPPrimeCore_le_xSub (hp : p.Prime) (M H : Subgroup G) :
    relPPrimeCore p H ≤ xSub p M H := by
  intro x hx
  rw [relPPrimeCore_eq_map hp H] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨z, ?_, rfl⟩
  show QuotientGroup.mk' (primeComplementCore (G := ↥H) p) z ∈ centralizer ((kStar p M H :
    Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
      Set (↥H ⧸ primeComplementCore (G := ↥H) p))
  have h1 : QuotientGroup.mk' (primeComplementCore (G := ↥H) p) z = 1 :=
    (QuotientGroup.eq_one_iff (N := primeComplementCore (G := ↥H) p) z).mpr hz
  rw [h1]
  exact Subgroup.one_mem _

theorem starImg_mono {A B : Subgroup G} (hAB : A ≤ B) : starImg p H A ≤ starImg p H B :=
  Subgroup.map_mono (Subgroup.comap_mono hAB)

theorem starImg_le_centralizer_kStar {A : Subgroup G} (hA : A ≤ xSub p M H) :
    starImg p H A ≤ centralizer ((kStar p M H :
      Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
        Set (↥H ⧸ primeComplementCore (G := ↥H) p)) := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨z, hz, hza⟩ := (hA (show (a : G) ∈ A from ha) : (a : G) ∈ xSub p M H)
  have hza' : z = a := Subtype.ext hza
  subst hza'
  exact hz

namespace NineCore

theorem starImg_eq_bot (h : NineCore G M p Q H E k) {A : Subgroup G} (hAH : A ≤ H)
    (hA2 : IsPGroup 2 A)
    (hP : starImg p H A ≤ centralizer ((CFSG.pCore p (↥H ⧸ primeComplementCore (G := ↥H) p) :
      Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
        Set (↥H ⧸ primeComplementCore (G := ↥H) p)))
    (hL : ∀ L : Subgroup G, IsPComponentIn p L H →
      (∀ a ∈ A, ∀ l ∈ L, l * a * l⁻¹ ∈ A) ∨
        starImg p H L ≤ centralizer ((starImg p H A :
          Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
            Set (↥H ⧸ primeComplementCore (G := ↥H) p))) :
    starImg p H A = ⊥ := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hA' : IsPGroup 2 (A.subgroupOf H) := hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  refine map_eq_bot_of_pComponents_normalize h.ne_two hA' hP ?_
  intro L' hL'
  have hsub : (L'.map H.subtype).subgroupOf H = L' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective L'
  rcases hL (L'.map H.subtype) (isPComponentIn_map_subtype hL') with hN | hC
  · have h1 : L' ≤ normalizer ((A.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      intro l hl
      rw [mem_normalizer_iff]
      intro x
      have hl' : (l : G) ∈ L'.map H.subtype := ⟨l, hl, rfl⟩
      have hli : ((l⁻¹ : ↥H) : G) ∈ L'.map H.subtype := ⟨l⁻¹, L'.inv_mem hl, rfl⟩
      show (x : G) ∈ A ↔ ((l * x * l⁻¹ : ↥H) : G) ∈ A
      constructor
      · intro hx
        exact hN _ hx _ hl'
      · intro hx
        have := hN _ hx _ hli
        simpa [mul_assoc] using this
    exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)
  · have hC' : L'.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) ≤
        centralizer ((A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) :
          Set (↥H ⧸ CFSG.pPrimeCore p ↥H)) := by
      unfold starImg at hC
      rwa [hsub] at hC
    exact hC'.trans (Subgroup.centralizer_le_normalizer _)

theorem le_relPPrimeCore_of_starImg_eq_bot (h : NineCore G M p Q H E k) {A : Subgroup G}
    (hAH : A ≤ H) (hA : starImg p H A = ⊥) : A ≤ relPPrimeCore p H := by
  intro a ha
  have h1 : (⟨a, hAH ha⟩ : ↥H) ∈ primeComplementCore (G := ↥H) p := by
    have h2 : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨a, hAH ha⟩ ∈
        starImg p H A := ⟨⟨a, hAH ha⟩, ha, rfl⟩
    rw [hA, Subgroup.mem_bot] at h2
    exact (QuotientGroup.eq_one_iff _).mp h2
  rw [relPPrimeCore_eq_map h.prime H]
  exact ⟨⟨a, hAH ha⟩, h1, rfl⟩

theorem le_pCoreOf_of_le_relPPrimeCore (h : NineCore G M p Q H E k) {A : Subgroup G}
    (hA2 : IsPGroup 2 A) (hAO : A ≤ relPPrimeCore p H)
    (hAn : ∀ o ∈ relPPrimeCore p H, ∀ a ∈ A, o * a * o⁻¹ ∈ A) : A ≤ pCoreOf 2 H := by
  set O : Subgroup G := relPPrimeCore p H with hO
  have hOH : O ≤ H := sSup_le fun _ hN => hN.1
  have hHO : H ≤ normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOH).mp
      (relPPrimeCore_normal h.prime H)
  have hOA : O ≤ normalizer (A : Set G) := by
    intro o ho
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hAn o ho x hx, fun hx => ?_⟩
    have := hAn o⁻¹ (O.inv_mem ho) _ hx
    simpa [mul_assoc] using this
  have h1 : A ≤ pCoreOf 2 O := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAO hOA hA2
  have h2 : pCoreOf 2 O ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 O).trans hOH)
      (hHO.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O))
      (pCoreOf_isPGroup 2 O)
  exact h1.trans h2

theorem nineEight_one (h : NineCore G M p Q H E k) (hJ : pLayerIn p H ≤ M) :
    pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := by
  have hSY : pCoreOf 2 (H ⊓ M) ≤ H ⊓ M := pCoreOf_le 2 _
  have hSn : ∀ y ∈ H ⊓ M, ∀ s ∈ pCoreOf 2 (H ⊓ M), y * s * y⁻¹ ∈ pCoreOf 2 (H ⊓ M) :=
    fun y hy s hs =>
      (mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M) hy) s).mp hs
  have hS2 : IsPGroup 2 (pCoreOf 2 (H ⊓ M)) := pCoreOf_isPGroup 2 _
  have hbot : starImg p H (pCoreOf 2 (H ⊓ M)) = ⊥ := by
    refine h.starImg_eq_bot (hSY.trans inf_le_left) hS2
      (h.starImg_le_centralizer_pCore hS2 hSY hSn) fun L hL => Or.inl ?_
    intro a ha l hl
    exact hSn l ⟨hL.1 hl, hJ (le_pLayerIn hL hl)⟩ a ha
  exact h.pCoreOf_inf_eq_of_le
    (h.le_relPPrimeCore_of_starImg_eq_bot (hSY.trans inf_le_left) hbot)

theorem nineEight_three (h : NineCore G M p Q H E k) :
    pCoreOf 2 (H ⊓ M) ⊓ xSub p M H = pCoreOf 2 H := by
  have hSY : pCoreOf 2 (H ⊓ M) ≤ H ⊓ M := pCoreOf_le 2 _
  have hSn : ∀ y ∈ H ⊓ M, ∀ s ∈ pCoreOf 2 (H ⊓ M), y * s * y⁻¹ ∈ pCoreOf 2 (H ⊓ M) :=
    fun y hy s hs =>
      (mem_normalizer_iff.mp (localGroup_le_normalizer_pCoreOf 2 (H ⊓ M) hy) s).mp hs
  have hS2 : IsPGroup 2 (pCoreOf 2 (H ⊓ M)) := pCoreOf_isPGroup 2 _
  set A : Subgroup G := pCoreOf 2 (H ⊓ M) ⊓ xSub p M H with hAdef
  have hAH : A ≤ H := inf_le_left.trans (hSY.trans inf_le_left)
  have hA2 : IsPGroup 2 A := hS2.to_le inf_le_left
  have hbot : starImg p H A = ⊥ := by
    refine h.starImg_eq_bot hAH hA2
      ((starImg_mono (inf_le_left : A ≤ pCoreOf 2 (H ⊓ M))).trans
        (h.starImg_le_centralizer_pCore hS2 hSY hSn)) fun L hL => ?_
    by_cases hLM : L ≤ M
    · refine Or.inl fun a ha l hl => ?_
      have hlY : l ∈ H ⊓ M := ⟨hL.1 hl, hLM hl⟩
      exact ⟨hSn l hlY a ha.1, conj_mem_xSub hlY.1 hlY.2 ha.2⟩
    · refine Or.inr ?_
      have hnJ : ¬ pLayerIn p H ≤ M := fun hJ => hLM ((le_pLayerIn hL).trans hJ)
      have hLK : L ≤ kSub p M H := by
        unfold kSub
        rw [if_neg hnJ]
        exact le_sSup ⟨hL, hLM⟩
      have hAc := starImg_le_centralizer_kStar (p := p) (M := M) (H := H)
        (inf_le_right : A ≤ xSub p M H)
      intro u hu
      rw [mem_centralizer_iff]
      intro v hv
      have huK : u ∈ kStar p M H := by
        obtain ⟨l, hl, rfl⟩ := hu
        exact ⟨l, Subgroup.comap_mono hLK hl, rfl⟩
      exact ((mem_centralizer_iff.mp (hAc hv)) u huK).symm
  have hAO : A ≤ relPPrimeCore p H := h.le_relPPrimeCore_of_starImg_eq_bot hAH hbot
  have hAn : ∀ o ∈ relPPrimeCore p H, ∀ a ∈ A, o * a * o⁻¹ ∈ A := by
    intro o ho a ha
    have hoH : o ∈ H := (sSup_le fun _ hN => hN.1 : relPPrimeCore p H ≤ H) ho
    have hoY : o ∈ H ⊓ M := ⟨hoH, h.relPPrimeCore_le ho⟩
    exact ⟨hSn o hoY a ha.1, conj_mem_xSub hoY.1 hoY.2 ha.2⟩
  haveI : Fact p.Prime := ⟨h.prime⟩
  refine le_antisymm (h.le_pCoreOf_of_le_relPPrimeCore hA2 hAO hAn)
    (le_inf h.pCoreOf_two_le_inf ?_)
  exact (CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.pCoreOf_two_le_relPPrimeCore
    h.ne_two H).trans (relPPrimeCore_le_xSub h.prime M H)

theorem nineEight_three_of_le (h : NineCore G M p Q H E k)
    (hX : sSup (invTwoSubgroups H Q) ≤ xSub p M H) : pCoreOf 2 (H ⊓ M) = pCoreOf 2 H := by
  have hSX : pCoreOf 2 (H ⊓ M) ≤ xSub p M H :=
    (le_sSup h.pCoreOf_inf_mem_invTwoSubgroups).trans hX
  have h3 := h.nineEight_three
  rwa [inf_eq_left.mpr hSX] at h3

end NineCore

namespace NineSettingGen

theorem starImg_eq_bot (h : NineSettingGen G M p Q H E k) {A : Subgroup G} (hAH : A ≤ H)
    (hA2 : IsPGroup 2 A)
    (hP : starImg p H A ≤ centralizer ((CFSG.pCore p (↥H ⧸ primeComplementCore (G := ↥H) p) :
      Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
        Set (↥H ⧸ primeComplementCore (G := ↥H) p)))
    (hL : ∀ L : Subgroup G, IsPComponentIn p L H →
      (∀ a ∈ A, ∀ l ∈ L, l * a * l⁻¹ ∈ A) ∨
        starImg p H L ≤ centralizer ((starImg p H A :
          Subgroup (↥H ⧸ primeComplementCore (G := ↥H) p)) :
            Set (↥H ⧸ primeComplementCore (G := ↥H) p))) :
    starImg p H A = ⊥ :=
  h.toCore.starImg_eq_bot hAH hA2 hP hL

theorem le_relPPrimeCore_of_starImg_eq_bot (h : NineSettingGen G M p Q H E k) {A : Subgroup G}
    (hAH : A ≤ H) (hA : starImg p H A = ⊥) : A ≤ relPPrimeCore p H :=
  h.toCore.le_relPPrimeCore_of_starImg_eq_bot hAH hA

theorem nineEight_three (h : NineSettingGen G M p Q H E k) :
    pCoreOf 2 (H ⊓ M) ⊓ xSub p M H = pCoreOf 2 H :=
  h.toCore.nineEight_three

end NineSettingGen

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

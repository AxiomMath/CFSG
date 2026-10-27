module

public import CFSG.LocalAnalysis.RankThreeUC.K37HGONLift
public import CFSG.LocalAnalysis.RankThreeUC.K37HGONSylow
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FDefs
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35Inner
import CFSG.HardMathSupport.Solomon.Coordinator.C25Bar3
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.IndexGen

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37H

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.S15.K37
open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma59Ns (InputONSylow)
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (gammaLBelow)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem k37G_E_le {K E S : Subgroup X} (hs : K37Setting X K E S) (hSyl : InputONSylow)
    (hHat : IsHatON ↥K) (hout : ¬ 3 ∣ Nat.card (Outer (↥K ⧸ Subgroup.center ↥K))) :
    E ≤ K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hs.normal
  intro e he
  by_contra heK
  have he1 : e ≠ 1 := fun h => heK (h ▸ K.one_mem)
  obtain ⟨k, hkc0⟩ := k37G_exists_lift hs hout he
  obtain ⟨c, hcdef⟩ : ∃ c : X, c = (k : X)⁻¹ * e := ⟨_, rfl⟩
  have hkc : c ∈ Subgroup.centralizer (K : Set X) := hcdef ▸ hkc0
  have hec : e = (k : X) * c := by rw [hcdef]; group
  have hcK : ∀ y ∈ K, y * c = c * y := Subgroup.mem_centralizer_iff.mp hkc
  have hcnotK : c ∉ K := fun h => heK (hec ▸ K.mul_mem k.2 h)
  have hkcomm : (k : X) * c = c * (k : X) := hcK k k.2
  have hcomm : Commute (k : X) c := hkcomm
  have he3 : e ^ 3 = 1 := hs.elem.2 e he
  have hke : e ^ 3 = (k : X) ^ 3 * c ^ 3 := by rw [hec]; exact hcomm.mul_pow 3
  have hk3mem : (k : X) ^ 3 ∈ Subgroup.centralizer (K : Set X) := by
    have h1 : (k : X) ^ 3 = (c ^ 3)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      rw [he3] at hke
      exact hke.symm
    rw [h1]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hkc 3)
  have hk3z : k ^ 3 ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (by simpa using Subgroup.mem_centralizer_iff.mp hk3mem g g.2)
  have hZ3 : Nat.card (Subgroup.center ↥K) = 3 := hHat.2.1
  have hk9 : k ^ 9 = 1 := by
    have h1 : (⟨k ^ 3, hk3z⟩ : Subgroup.center ↥K) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center ↥K) (x := ⟨k ^ 3, hk3z⟩)
      rwa [hZ3] at this
    have h2 := congrArg Subtype.val h1
    simpa [← pow_mul] using h2
  have hkP : IsPGroup 3 (Subgroup.zpowers k) := by
    have hdvd : orderOf k ∣ 3 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hk9)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hk3 : k ^ 3 = 1 := k37G_pow_three_of_isPGroup hSyl hHat hkP
  have hk3X : (k : X) ^ 3 = 1 := by
    have := congrArg Subtype.val hk3
    simpa using this
  have hc3 : c ^ 3 = 1 := by
    rw [hk3X, one_mul] at hke
    rw [← hke, he3]
  have hkz : k ∉ Subgroup.center ↥K := by
    intro hkz
    have hkC : (k : X) ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hkz ⟨g, hg⟩)
    have heC : e ∈ E ⊓ Subgroup.centralizer (K : Set X) :=
      ⟨he, hec ▸ Subgroup.mul_mem _ hkC hkc⟩
    rw [k37G_inf_centralizer_eq_bot hs, Subgroup.mem_bot] at heC
    exact he1 heC
  obtain ⟨F, hFel, hF27, hFk⟩ := k37G_exists_E27 hSyl hHat hkP hkz
  set FX : Subgroup X := F.map K.subtype with hFXdef
  have hFXel : IsElemAbelian 3 FX := CFSG.SectionRank.isElemAbelian_map hFel _
  have hFXcard : Nat.card FX = 27 := by
    rw [hFXdef, Subgroup.card_map_of_injective K.subtype_injective, hF27]
  have hFXK : FX ≤ K := Subgroup.map_subtype_le F
  have hcFX : c ∉ FX := fun h => hcnotK (hFXK h)
  have hFXc : ∀ a ∈ FX, a * c = c * a := fun a ha => hcK a (hFXK ha)
  obtain ⟨hFel81, hFcard⟩ :=
    CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hFXel hcFX hc3 hFXc
  rw [hFXcard] at hFcard
  have hFle : (FX ⊔ Subgroup.zpowers c : Subgroup X) ≤ Subgroup.centralizer ({e} : Set X) := by
    refine sup_le (fun a ha => ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      have h1 : a' * k = k * a' := hFk a' ha'
      have h2 : ((a' : ↥K) : X) * (k : X) = (k : X) * (a' : X) := congrArg Subtype.val h1
      change (a' : X) * e = e * (a' : X)
      rw [hec]
      calc (a' : X) * ((k : X) * c) = ((a' : X) * (k : X)) * c := by rw [mul_assoc]
        _ = ((k : X) * (a' : X)) * c := by rw [h2]
        _ = (k : X) * ((a' : X) * c) := by rw [mul_assoc]
        _ = (k : X) * (c * (a' : X)) := by rw [hcK a' a'.2]
        _ = (k : X) * c * (a' : X) := by rw [mul_assoc]
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [hec]
      calc c * ((k : X) * c) = (c * (k : X)) * c := by rw [mul_assoc]
        _ = ((k : X) * c) * c := by rw [← hkcomm]
  have hFΓ : (FX ⊔ Subgroup.zpowers c : Subgroup X) ≤ rankThreeGamma 1 3 E :=
    hFle.trans (CFSG.LocalAnalysis.AGL81TheoremCD.Section15.K35.centralizer_le_gamma hs.elem he he1)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (rankThreeGamma 1 3 E) :=
    CFSG.SectionRank.le_pRank (by norm_num) hFΓ hFel81 (k := 4) (by rw [hFcard]; norm_num)
  have h3 : CFSG.Open.pRank 3 (rankThreeGamma 1 3 E) ≤ 3 := by
    have := hs.rank_gamma
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at this
  omega


private theorem k37G_layer_le_self {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.Open.GLAPLayer 3 H ≤ H :=
  sSup_le fun _ hK => hK.1

theorem k37G_le_centGenI_of_E_le {K E S : Subgroup X} (hs : K37Setting X K E S) (hEK : E ≤ K)
    (hZ3 : Nat.card (Subgroup.center ↥K) = 3)
    (hgen : ∀ B₀ : Subgroup ↥K, IsElemAbelian 3 B₀ → Nat.card B₀ = 27 →
      (⊤ : Subgroup ↥K) ≤ gammaLBelow B₀ (⊤ : Subgroup ↥K)) :
    K ≤ GL83.CompFam.centGenI 3 E K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hs.normal
  set ZX : Subgroup X := (Subgroup.center ↥K).map K.subtype with hZXdef
  have hZXK : ZX ≤ K := Subgroup.map_subtype_le _
  have hZXcard : Nat.card ZX = 3 := by
    rw [hZXdef, Subgroup.card_map_of_injective K.subtype_injective, hZ3]
  have hZXc : ∀ z ∈ ZX, ∀ y ∈ K, z * y = y * z := by
    rintro _ ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hZXel : IsElemAbelian 3 ZX := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · exact Subtype.ext (hZXc a a.2 b (hZXK b.2))
    · have := pow_card_eq_one' (G := ZX) (x := ⟨y, hy⟩)
      rw [hZXcard] at this
      exact congrArg Subtype.val this
  have hEZ : E ⊓ ZX = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyE, hyZ⟩ := hy
    have hyC : y ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (hZXc y hyZ g hg).symm
    have : y ∈ E ⊓ Subgroup.centralizer (K : Set X) := ⟨hyE, hyC⟩
    rw [k37G_inf_centralizer_eq_bot hs] at this
    exact this
  have hEZc : ∀ x ∈ E, ∀ y ∈ ZX, x * y = y * x := fun x hx y hy => (hZXc y hy x (hEK hx)).symm
  obtain ⟨hHcard, hHcoe⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E ZX hEZc
  have hEZcard : Nat.card (E ⊓ ZX : Subgroup X) = 1 := by
    rw [hEZ]
    exact Subgroup.card_bot
  rw [hEZcard, hs.card, hZXcard] at hHcard
  have hHel : IsElemAbelian 3 (E ⊔ ZX) :=
    CFSG.RankThree.PartTwo.Sec13.isElemAbelian_sup hs.elem hZXel hEZc
  have hHK : E ⊔ ZX ≤ K := sup_le hEK hZXK
  set B₀ : Subgroup ↥K := (E ⊔ ZX).subgroupOf K with hB₀def
  have hB₀el : IsElemAbelian 3 B₀ := CFSG.Open.IsElemAbelian.subgroupOf hHel K
  have hB₀card : Nat.card B₀ = 27 := by
    rw [hB₀def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv]
    omega
  have hgenB := hgen B₀ hB₀el hB₀card
  have hpr3 : CFSG.pRank 3 ↥B₀ = 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_pRank_eq hB₀el (k := 3)
      (by rw [hB₀card]; norm_num)
  set W : Subgroup ↥K := (GL83.CompFam.centGenI 3 E K).comap K.subtype with hWdef
  have htop : (⊤ : Subgroup ↥K) ≤ W := by
    refine hgenB.trans ?_
    unfold gammaLBelow
    refine iSup₂_le fun E'' hE'' => ?_
    obtain ⟨hE''B, hrk⟩ := hE''
    refine (k37G_layer_le_self _).trans ?_
    intro y hy
    have hyc : y ∈ Subgroup.centralizer (E'' : Set ↥K) := hy.2
    obtain ⟨w, hwE'', hwZ⟩ : ∃ w ∈ E'', w ∉ Subgroup.center ↥K := by
      by_contra hall
      push Not at hall
      have hle : E'' ≤ Subgroup.center ↥K := hall
      have h1 : CFSG.pRank 3 ↥E'' ≤ 1 := by
        rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
        refine CFSG.SectionRank.pRank_le (by norm_num) fun F _ _ => ?_
        calc Nat.card F ≤ Nat.card ↥E'' := Subgroup.card_le_card_group F
          _ ≤ Nat.card (Subgroup.center ↥K) := Subgroup.card_le_of_le hle
          _ = 3 ^ 1 := by rw [hZ3]; norm_num
      rw [hpr3] at hrk
      omega
    have hwH : (w : X) ∈ E ⊔ ZX := Subgroup.mem_subgroupOf.mp (hE''B hwE'')
    have hwH' : (w : X) ∈ ((E : Set X) * (ZX : Set X)) := by
      rw [← hHcoe]
      exact hwH
    obtain ⟨ε, hεE, ζ, hζZ, hεζ⟩ := Set.mem_mul.mp hwH'
    have hε1 : ε ≠ 1 := by
      rintro rfl
      rw [one_mul] at hεζ
      obtain ⟨z, hz, hzζ⟩ := hζZ
      have hwz : w = z := Subtype.ext (hεζ.symm.trans hzζ.symm)
      exact hwZ (hwz ▸ hz)
    have hyw : (w : X) * (y : X) = (y : X) * (w : X) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hyc w hwE'')
    have hyζ : ζ * (y : X) = (y : X) * ζ := hZXc ζ hζZ y y.2
    have hyε : ε * (y : X) = (y : X) * ε := by
      rw [← hεζ] at hyw
      have h1 : ε * ζ * (y : X) = ε * (y : X) * ζ := by
        calc ε * ζ * (y : X) = ε * (ζ * (y : X)) := mul_assoc _ _ _
          _ = ε * ((y : X) * ζ) := by rw [hyζ]
          _ = ε * (y : X) * ζ := (mul_assoc _ _ _).symm
      have h2 : (y : X) * (ε * ζ) = (y : X) * ε * ζ := (mul_assoc _ _ _).symm
      exact mul_right_cancel (h1.symm.trans (hyw.trans h2))
    have hεord : orderOf ε = 3 := orderOf_eq_prime (hs.elem.2 ε hεE) hε1
    have hAE : Subgroup.zpowers ε ≤ E := Subgroup.zpowers_le.2 hεE
    have hAcard : Nat.card E ≤ 3 * Nat.card (Subgroup.zpowers ε) := by
      rw [Nat.card_zpowers, hεord, hs.card]
    have hyA : (y : X) ∈ K ⊓ Subgroup.centralizer ((Subgroup.zpowers ε : Subgroup X) : Set X) := by
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact (Commute.zpow_left (show Commute ε (y : X) from hyε) i).eq
    exact GL83.CompFam.le_centGenI hAE hAcard hyA
  intro x hx
  exact htop (Subgroup.mem_top ⟨x, hx⟩)

end CFSG.LocalAnalysis.RankThreeUC.S15.K37H

end

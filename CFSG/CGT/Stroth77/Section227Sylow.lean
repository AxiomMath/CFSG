module

public import CFSG.CGT.Stroth77.Section227Frame
public import CFSG.CGT.Stroth77.StrothAmbient
import CFSG.CGT.Stroth77.Section223Family
import CFSG.CGT.Stroth77.Section310Char
import CFSG.CGT.Stroth77.Section41
import CFSG.CGT.Stroth77.Section224
import CFSG.CGT.Stroth77.Stroth31Proof
import CFSG.CGT.Stroth77.StrothFrameAmbient
import CFSG.CGT.Stroth77.TorusCard
import CFSG.GroupTheory.FixedCosetCommutator
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.QuasithinUnique.Setting
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
import CFSG.LocalAnalysis.SectionRank.TitsCover
import CFSG.Quasithin.Background.A3Components
import CFSG.Quasithin.Background.A3ComponentsAmbient
import CFSG.Quasithin.Background.B4ModelsAction
import CFSG.Quasithin.Background.B4Statement
import CFSG.Quasithin.Background.B5Statement
import CFSG.Quasithin.Background.F9Basic
import CFSG.Quasithin.Background.G2A5Setting
import CFSG.Quasithin.H13.Sp62D3
import CFSG.Sporadic.J4.Simple
import CFSG.Sporadic.J4Base
import CFSG.Sporadic.Mathieu.M12
import CFSG.Sporadic.Mathieu.M24
import CFSG.Sporadic.Schreier.J4SBinary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
import Certificates.Certificate43

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)
open CFSG.ABGLocalTools (IsSylowOf)

namespace Arch76

theorem two_torsion_span_of_not_mem : ∀ u v : Co, 2 • u = 0 → 2 • v = 0 →
    v ∉ ([0, (1, 0, 0), (0, 2, 2), (1, 2, 2)] : List Co) →
    ∃ i j l : Bool, u = (if i then (1, 0, 0) else 0) + (if j then (0, 2, 2) else 0) +
      (if l then v else 0) := by
  decide +kernel

end Arch76

variable {G : Type} [Group G] [Finite G]

namespace StrothFrame

variable (F : StrothFrame G)

theorem mem_closure_w_xy_sq_of_commute {b v : G} (hv : v ∈ omegaIn 1 F.A)
    (hbw : b * (F.dA.c : G) = (F.dA.c : G) * b)
    (hbz : b * (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 =
      (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2 * b)
    (hbv : b * v = v * b)
    (hb : b ∉ Subgroup.centralizer ((omegaIn 1 F.A : Subgroup G) : Set G)) :
    v ∈ Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2} := by
  classical
  set K := F.dA.toConfig with hK
  have hAc : IsMulCommutative F.A := F.dA.isMulCommutative
  have h2 : ∀ {a : G}, a ∈ omegaIn 1 F.A → ∃ u : Arch76.Co, K.ev u = a ∧ 2 • u = 0 := by
    intro a ha
    have ha' := (mem_omegaIn_one_iff hAc).mp ha
    obtain ⟨u, hu⟩ := K.exists_ev ha'.1
    refine ⟨u, hu, ?_⟩
    rw [← K.ev_eq_one_iff, K.ev_nsmul, hu, pow_two, ha'.2]
  obtain ⟨v', rfl, hv2⟩ := h2 hv
  set W := Subgroup.closure {(F.dA.c : G), (K.x * K.y) ^ 2} with hW
  have hwW : K.w ∈ W := Subgroup.subset_closure (by simp [K])
  have hzW : (K.x * K.y) ^ 2 ∈ W := Subgroup.subset_closure (by simp)
  have hev022 : K.ev (0, 2, 2) = (K.x * K.y) ^ 2 := by
    rw [K.xy_sq]
    simp [Arch76.Config.ev, show (2 : ZMod 4).val = 2 from rfl]
  by_contra hvW
  have hnot : v' ∉ ([0, (1, 0, 0), (0, 2, 2), (1, 2, 2)] : List Arch76.Co) := by
    intro hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hvW (by rw [K.ev_zero]; exact one_mem W)
    · exact hvW (by rw [K.ev_w]; exact hwW)
    · exact hvW (by rw [hev022]; exact hzW)
    · exact hvW (by rw [K.ev_122]; exact mul_mem hwW hzW)
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  have hw' : K.w ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr hbw.symm
  have hz' : (K.x * K.y) ^ 2 ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr hbz.symm
  have hv' : K.ev v' ∈ Cb := Subgroup.mem_centralizer_singleton_iff.mpr hbv.symm
  apply hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨u, rfl, hu2⟩ := h2 ha
  obtain ⟨i, j, l, hu⟩ := Arch76.two_torsion_span_of_not_mem u v' hu2 hv2 hnot
  have hmem : K.ev u ∈ Cb := by
    rw [hu, K.ev_add, K.ev_add]
    refine mul_mem (mul_mem ?_ ?_) ?_
    · cases i
      · simp only [Bool.false_eq_true, ↓reduceIte, K.ev_zero]; exact one_mem Cb
      · simp only [↓reduceIte]; rw [K.ev_w]; exact hw'
    · cases j
      · simp only [Bool.false_eq_true, ↓reduceIte, K.ev_zero]; exact one_mem Cb
      · simp only [↓reduceIte]; rw [hev022]; exact hz'
    · cases l
      · simp only [Bool.false_eq_true, ↓reduceIte, K.ev_zero]; exact one_mem Cb
      · simp only [↓reduceIte]; exact hv'
  exact Subgroup.mem_centralizer_singleton_iff.mp hmem

end StrothFrame

namespace StrothFrame.IsD

variable {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem exists_mem_normalizer_not_mem_normalizer (h : F.IsD D dD) (hmn : τ.m < τ.n)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hall : IsConj (F.dA.c : G) ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) :
    ∃ p ∈ Subgroup.normalizer (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ({(F.dA.c : G)} : Set G) : Subgroup G) : Set G),
      p ∈ Subgroup.centralizer ({(F.dA.c : G)} : Set G) ∧
        p ∉ Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsSylowOf 2 ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))
      (Subgroup.normalizer (D : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hns.1, hns.2.1, hns.2.2⟩
  exact F.exists_mem_normalizer_not_mem hP inf_le_left (h.normalizer_le_normalizer_A hmn)
    ⟨F.uv_mem_S, h.uv_mem_normalizer⟩ ⟨F.t_mem_S, h.t_mem_normalizer⟩
    (fun s hs => h.commute_xy_sq hs) hall

theorem good_or_bad (h : F.IsD D dD) (hmn : τ.m < τ.n)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hall : IsConj (F.dA.c : G) ((F.dA.toConfig.x * F.dA.toConfig.y) ^ 2)) :
    (∃ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) ∧
        (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
            Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
          x * b * x⁻¹ ∈ B) ∧
        B ≠ D ∧ ∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) ∨
    ∃ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), y * y = 1 ∧ y ∉ D ∧
      y * (F.dA.c : G) = (F.dA.c : G) * y ∧
      ∀ d ∈ D, d⁻¹ * y⁻¹ * d * y ∈
        Subgroup.closure {(F.dA.c : G), (F.dA.toConfig.x * F.dA.toConfig.y) ^ 2} := by
  classical
  obtain ⟨p, hpQ, -, hpD⟩ := h.exists_mem_normalizer_not_mem_normalizer hmn hns hall
  set w : G := (F.dA.c : G) with hw
  set N := Subgroup.normalizer (D : Set G) with hN
  set Q := (F.S : Subgroup G) ⊓ N ⊓ Subgroup.centralizer ({w} : Set G) with hQ
  set V := omegaIn 1 D with hV
  have hDc : IsMulCommutative D := dD.isMulCommutative
  have hcommD := h.comm
  have hwD : w ∈ D := h.A_le F.dA.c.2
  have hw2 : w * w = 1 := by
    have := F.dA.toConfig.hw
    rwa [pow_two] at this
  have hwV : w ∈ V := mem_omegaIn_one_of_mul_self hwD hw2
  have hDQ : D ≤ Q := fun d hd => ⟨⟨h.le_S hd, Subgroup.le_normalizer hd⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr (hcommD d hd w hwD)⟩
  have hQN : Q ≤ N := fun q hq => hq.1.2
  have hRQ : (F.S : Subgroup G) ⊓ N ⊓ Subgroup.centralizer ((V : Subgroup G) : Set G) ≤ Q :=
    fun x hx => ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp hx.2) w hwV).symm⟩
  have hpQ' : ∀ q, q ∈ Q ↔ p * q * p⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hpQ
  set B : Subgroup G := D.map (MulAut.conj p).toMonoidHom with hB
  have hmemB : ∀ b ∈ B, ∃ d ∈ D, b = p * d * p⁻¹ := by
    rintro b ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  have hconjB : ∀ d ∈ D, p * d * p⁻¹ ∈ B := fun d hd => ⟨d, hd, rfl⟩
  have hBQ : B ≤ Q := by
    intro b hb
    obtain ⟨d, hd, rfl⟩ := hmemB b hb
    exact (hpQ' d).mp (hDQ hd)
  have hBn : ∀ q ∈ Q, ∀ b ∈ B, q * b * q⁻¹ ∈ B := by
    intro q hq b hb
    obtain ⟨d, hd, rfl⟩ := hmemB b hb
    have hq' : p⁻¹ * q * p ∈ Q := (hpQ' _).mpr (by
      rw [show p * (p⁻¹ * q * p) * p⁻¹ = q by group]; exact hq)
    have hd' : (p⁻¹ * q * p) * d * (p⁻¹ * q * p)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp (hQN hq') d).mp hd
    rw [show q * (p * d * p⁻¹) * q⁻¹ = p * ((p⁻¹ * q * p) * d * (p⁻¹ * q * p)⁻¹) * p⁻¹ by group]
    exact hconjB _ hd'
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := hmemB x hx
    obtain ⟨d', hd', rfl⟩ := hmemB y hy
    calc p * d * p⁻¹ * (p * d' * p⁻¹) = p * (d * d') * p⁻¹ := by group
      _ = p * (d' * d) * p⁻¹ := by rw [hcommD d hd d' hd']
      _ = p * d' * p⁻¹ * (p * d * p⁻¹) := by group
  have hBD : B ≠ D := by
    intro hBD
    apply hpD
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [← hBD]
      exact hconjB x hx
    · intro hx
      rw [← hBD] at hx
      obtain ⟨d, hd, hdx⟩ := hmemB _ hx
      have : x = d := by
        have h1 := congrArg (fun y => p⁻¹ * y * p) hdx
        simpa [mul_assoc] using h1
      rwa [this]
  by_cases hgood : ∀ b ∈ B, b ∈ Subgroup.centralizer ((V : Subgroup G) : Set G)
  · left
    exact ⟨B, fun b hb => ⟨(hBQ hb).1, hgood b hb⟩, fun x hx b hb => hBn x (hRQ hx) b hb,
      hBD, p, rfl⟩
  · right
    push Not at hgood
    obtain ⟨b, hbB, hbV⟩ := hgood
    have hex : ∃ v ∈ V, p * v * p⁻¹ ∉ D := by
      by_contra hno
      push Not at hno
      have hle : V.map (MulAut.conj p).toMonoidHom ≤ V := by
        rintro _ ⟨v, hv, rfl⟩
        have hv' := (mem_omegaIn_one_iff hDc).mp hv
        refine mem_omegaIn_one_of_mul_self (hno v hv) ?_
        show p * v * p⁻¹ * (p * v * p⁻¹) = 1
        calc p * v * p⁻¹ * (p * v * p⁻¹) = p * (v * v) * p⁻¹ := by group
          _ = 1 := by rw [hv'.2]; group
      have heq : V.map (MulAut.conj p).toMonoidHom = V :=
        Subgroup.eq_of_le_of_card_ge hle (by
          rw [Subgroup.card_map_of_injective (f := (MulAut.conj p).toMonoidHom)
            (MulAut.conj p).injective])
      apply hbV
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hvB : v ∈ B := by
        rw [← heq] at hv
        obtain ⟨v₀, hv₀, rfl⟩ := hv
        exact hconjB v₀ (omegaIn_le 1 D hv₀)
      exact hBc v hvB b hbB
    obtain ⟨v, hvV, hvD⟩ := hex
    have hv' := (mem_omegaIn_one_iff hDc).mp hvV
    obtain ⟨y, hy⟩ : ∃ y : G, y = p * v * p⁻¹ := ⟨_, rfl⟩
    have hyB : y ∈ B := by rw [hy]; exact hconjB v hv'.1
    have hyQ := hBQ hyB
    have hy2 : y * y = 1 := by
      rw [hy]
      calc p * v * p⁻¹ * (p * v * p⁻¹) = p * (v * v) * p⁻¹ := by group
        _ = 1 := by rw [hv'.2]; group
    have hyD : y ∉ D := by rw [hy]; exact hvD
    refine ⟨y, hyQ.1, hy2, hyD, Subgroup.mem_centralizer_singleton_iff.mp hyQ.2, fun d hd => ?_⟩
    have hyN : y ∈ N := hQN hyQ
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    obtain ⟨k, hk⟩ : ∃ k : G, k = d⁻¹ * y⁻¹ * d * y := ⟨_, rfl⟩
    rw [← hk]
    have hkD : k ∈ D := by
      have h1 : y⁻¹ * d * y ∈ D := (Subgroup.mem_normalizer_iff''.mp hyN d).mp hd
      rw [hk, show d⁻¹ * y⁻¹ * d * y = d⁻¹ * (y⁻¹ * d * y) by group]
      exact mul_mem (inv_mem hd) h1
    have hkB : k ∈ B := by
      have h1 : d⁻¹ * y⁻¹ * d⁻¹⁻¹ ∈ B := hBn d⁻¹ (hDQ (inv_mem hd)) y⁻¹ (inv_mem hyB)
      rw [inv_inv] at h1
      rw [hk]
      exact mul_mem h1 hyB
    have hk2 : k * k = 1 := by
      have e1 : y * k * y⁻¹ = y * d⁻¹ * y⁻¹ * d := by rw [hk]; group
      have e2 : k⁻¹ = y⁻¹ * d⁻¹ * y * d := by rw [hk]; group
      have e3 : y * k * y⁻¹ = k := by rw [hBc y hyB k hkB]; group
      have e4 : k = k⁻¹ :=
        calc k = y * k * y⁻¹ := e3.symm
          _ = y * d⁻¹ * y⁻¹ * d := e1
          _ = y⁻¹ * d⁻¹ * y * d := by rw [hyinv]
          _ = k⁻¹ := e2.symm
      calc k * k = k * k⁻¹ := by rw [← e4]
        _ = 1 := mul_inv_cancel k
    have hkV : k ∈ omegaIn 1 F.A := by
      rw [← h.omegaIn_one_eq]
      exact mem_omegaIn_one_of_mul_self hkD hk2
    have hbQ := hBQ hbB
    have hbV' : b ∉ Subgroup.centralizer ((omegaIn 1 F.A : Subgroup G) : Set G) := by
      rw [← h.omegaIn_one_eq]; exact hbV
    exact F.mem_closure_w_xy_sq_of_commute hkV (Subgroup.mem_centralizer_singleton_iff.mp hbQ.2)
      (h.commute_xy_sq hbQ.1.1) (hBc b hbB k hkB) hbV'

end StrothFrame.IsD

end CFSG.CGT.Stroth77

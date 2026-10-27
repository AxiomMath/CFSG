module

public import CFSG.ClassicalInvolution.Q3.TL4S289GenB
public import CFSG.ClassicalInvolution.Q3.TL4StarSecPair
public import CFSG.ClassicalInvolution.Q3.Q3AM289S4LX
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7AFinal
public import CFSG.ClassicalInvolution.Asc77.AscT7ASectD
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.Asc77.WP2Branch
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3T7LayerAEQ
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.Q3WAEDict
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLeaves
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.ClassicalInvolution.Uniform.U3IH8
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2
public import CFSG.Sporadic.J4.QT2LocProof
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77

namespace S289G

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem conjSub_centralizer_singleton (g y : X) :
    conjSub g (Subgroup.centralizer ({y} : Set X)) =
      Subgroup.centralizer ({g * y * g⁻¹} : Set X) := by
  ext x
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
      _ = g * y * g⁻¹ * x := by group
  · intro hx
    calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [hx]
      _ = y * (g⁻¹ * x * g) := by group

theorem starFrameGenAll_conj (hΦ : ConjInvariant Φ) {L L' : Subgroup X} {b : X}
    (hst : L' ∈ omegaStarNbr Φ L) (hn : L' ∉ omegaNbr Φ L) (hb : IsUniqueInvolution L' b)
    (hgen : ∀ a : X, IsUniqueInvolution L a →
      Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({b} : Set X) ⊔
        Subgroup.centralizer ({a * b} : Set X) = ⊤) (g : X) :
    StarFrameGenAll Φ (conjSub g L) := by
  refine StarFrameGenAll.of_pair (omegaStarNbr_conj hΦ hst g) (fun h => hn ?_) (hb.conj g) ?_
  · have h' := omegaNbr_conj hΦ h g⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at h'
  · intro a ha
    have ha' : IsUniqueInvolution L (g⁻¹ * a * g⁻¹⁻¹) := by
      have h1 := ha.conj g⁻¹
      rwa [conjSub_inv_conjSub] at h1
    have h2 : conjSub g (Subgroup.centralizer ({g⁻¹ * a * g⁻¹⁻¹} : Set X) ⊔
        Subgroup.centralizer ({b} : Set X) ⊔
          Subgroup.centralizer ({g⁻¹ * a * g⁻¹⁻¹ * b} : Set X)) = ⊤ := by
      rw [hgen _ ha']
      exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
    have hc := conjSub_centralizer_singleton g
    simp only [conjSub] at hc
    rw [conjSub, Subgroup.map_sup, Subgroup.map_sup, hc, hc, hc,
      show g * (g⁻¹ * a * g⁻¹⁻¹) * g⁻¹ = a by group,
      show g * (g⁻¹ * a * g⁻¹⁻¹ * b) * g⁻¹ = a * (g * b * g⁻¹) by group] at h2
    exact h2

variable [Finite X]

theorem starFrameGenAll_of_kframe {G : Type} [Group G] {𝓕 : Set (Subgroup G)} {ψ : G →* X}
    (hs : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    (hfund : ∀ L ∈ Φ, ∃ R ∈ 𝓕, IsSylow2In L (R.map ψ))
    (hcls : ∀ R ∈ 𝓕, ∀ R' ∈ 𝓕, ∃ g : X, R'.map ψ = conjSub g (R.map ψ))
    {Ra Rb : Subgroup G} (hRa : Ra ∈ 𝓕) (hRb : Rb ∈ 𝓕) {a b u : G}
    (hUa : IsUniqueInvolution Ra a) (hUb : IsUniqueInvolution Rb b)
    (haZ : a ∉ Subgroup.center G) (hbZ : b ∉ Subgroup.center G) (hu : u ∈ Rb)
    (hu4 : orderOf u = 4) (huu : u * u = b) (hau : a * u = u * a)
    (hnc : b * a⁻¹ ∉ Subgroup.center G)
    (hgen : Subgroup.centralizer ({a} : Set G) ⊔ Subgroup.centralizer ({b} : Set G) ⊔
      Subgroup.centralizer ({a * b} : Set G) = ⊤)
    (hR : TypeRFam 3 Φ)
    (h284 : ∀ M ∈ Φ, ∀ N ∈ omegaNbr Φ M, ∀ m n : X, IsUniqueInvolution M m →
      IsUniqueInvolution N n → m * n ∈ Subgroup.center X) :
    ∀ L ∈ Φ, StarFrameGenAll Φ L := by
  have hΦ := hR.hyp.conjInvariant
  intro L hL
  obtain ⟨R, hRf, hLR⟩ := hfund L hL
  obtain ⟨g₀, hg₀⟩ := hcls R hRf Ra hRa
  have hL₀ : conjSub g₀ L ∈ Φ := hΦ g₀ L hL
  have hL₀R : IsSylow2In (conjSub g₀ L) (Ra.map ψ) := hg₀ ▸ hLR.conj g₀
  have hψa1 : ψ a ≠ 1 := fun h => haZ (hker h)
  have hψa2 : ψ a * ψ a = 1 := by rw [← map_mul, hUa.sq, map_one]
  have hψaL : ψ a ∈ conjSub g₀ L := by
    refine mem_of_isSylow2In_of_central hL₀R (Subgroup.mem_map_of_mem ψ hUa.mem)
      (fun y hy => ?_) hψa2
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, hUa.commute_of_mem hy']
  obtain ⟨⟨z, hz⟩, -⟩ := hR.hyp.omega1 _ hL₀
  have hza : ψ a = z := (hz.unique _ hψaL hψa2).resolve_left hψa1
  rw [← hza] at hz
  have hU2 : IsPGroup 2 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num)
  obtain ⟨M₀, hM₀R, hUM⟩ := IsSylow2In.exists_ge (hU2.map ψ)
    (Subgroup.map_mono (Subgroup.zpowers_le.mpr hu))
  have hψu : ψ u ∈ M₀ := hUM (Subgroup.mem_map_of_mem ψ (Subgroup.mem_zpowers u))
  have hM₀ : M₀ ∈ Φ := by
    obtain ⟨g₁, hg₁⟩ := hcls R hRf Rb hRb
    have hS : IsSylow2In (conjSub g₁ L) (Rb.map ψ) := hg₁ ▸ hLR.conj g₁
    obtain ⟨c, -, hc⟩ := Disconnected.AschTight.S1916.IsSylow2In.exists_conj hS hM₀R
    rw [← hc, ← conjSub_mul]
    exact hΦ _ L hL
  have hψb1 : ψ b ≠ 1 := fun h => hbZ (hker h)
  have hψb2 : ψ b * ψ b = 1 := by rw [← map_mul, hUb.sq, map_one]
  have hψbM : ψ b ∈ M₀ := by
    rw [← huu, map_mul]
    exact M₀.mul_mem hψu hψu
  obtain ⟨⟨w, hw⟩, -⟩ := hR.hyp.omega1 _ hM₀
  have hwb : ψ b = w := (hw.unique _ hψbM hψb2).resolve_left hψb1
  rw [← hwb] at hw
  have hab : a * b = b * a := by
    calc a * b = a * (u * u) := by rw [huu]
      _ = (a * u) * u := by group
      _ = (u * a) * u := by rw [hau]
      _ = u * (a * u) := by group
      _ = u * (u * a) := by rw [hau]
      _ = b * a := by rw [← huu]; group
  have hne : ψ b ≠ ψ a := by
    intro h
    apply hnc
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hnZ : ψ a * ψ b ∉ Subgroup.center X := by
    intro h
    apply hnc
    rw [inv_eq_of_mul_eq_one_right hUa.sq, ← hab]
    exact Q3AM.S4L.mem_center_of_map_central ψ hker hperf (by rw [map_mul]; exact h)
  have hst : M₀ ∈ omegaStarNbr Φ (conjSub g₀ L) := by
    have hM₀2 : IsPGroup 2 M₀ := hM₀R.2.1
    have hM₀RS : M₀ ∈ RSet Φ := mem_RSet_of_isSylow2In hM₀ ⟨le_rfl, hM₀2, fun V hV _ hle =>
      le_antisymm hV hle⟩
    have hψu4 := orderOf_map_eq_four hker hu4 (by rw [huu]; exact hbZ)
    refine ⟨hM₀, fun he => hne (hw.eq (he ▸ hz)), Subgroup.zpowers (ψ u), ⟨M₀, hM₀RS,
      Subgroup.zpowers_le.mpr hψu, inferInstance, ?_⟩, Subgroup.zpowers_le.mpr hψu, ?_⟩
    · have h1 := Subgroup.relIndex_mul_card (Subgroup.zpowers (ψ u)) M₀
      rw [inf_eq_left.mpr (Subgroup.zpowers_le.mpr hψu), Nat.card_zpowers, hψu4,
        natCard_of_mem_RSet hR hM₀RS] at h1
      omega
    · refine Subgroup.zpowers_le.mpr (hR.tight _ hL₀ _ hz ?_)
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hau]
  have hn : M₀ ∉ omegaNbr Φ (conjSub g₀ L) := fun h => hnZ (h284 _ hL₀ _ h _ _ hz hw)
  have hgenX : ∀ a' : X, IsUniqueInvolution (conjSub g₀ L) a' →
      Subgroup.centralizer ({a'} : Set X) ⊔ Subgroup.centralizer ({ψ b} : Set X) ⊔
        Subgroup.centralizer ({a' * ψ b} : Set X) = ⊤ := by
    intro a' ha'
    rw [ha'.eq hz, ← map_mul]
    exact Q3AM.S4L.sup_centralizer_eq_top_of_map ψ hs hgen
  have h := starFrameGenAll_conj hΦ hst hn hw hgenX g₀⁻¹
  rwa [conjSub_inv_conjSub] at h

end S289G

end CFSG.ClassicalInvolution.Q3.TL4

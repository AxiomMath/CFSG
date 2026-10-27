module

public import CFSG.CGT.Stroth77.Section225FrameOrder
public import CFSG.CGT.Stroth77.Section225FrameBasic
public import CFSG.CGT.Stroth77.Section223Layer
public import CFSG.CGT.Stroth77.Stroth34Frame
public import CFSG.CGT.Stroth77.WeakTypeFamilyTwoComm
public import CFSG.CGT.Stroth77.StrothFrameAmbient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.J4SBinary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

open Matrix

namespace DeviationGeneric

open Stroth225Frame

local notation "𝓡[" S ", " D "]" =>
  S ⊓ Subgroup.normalizer (SetLike.coe D) ⊓ Subgroup.centralizer (SetLike.coe (mhoOne D))

variable {G : Type} [Group G] [Finite G] {S D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

theorem torusHalf_single (j : Fin 3) :
    torusHalf τ.k (Pi.single j 1) = (2 ^ (τ.k j - 1) : ℕ) • gen τ.k j := by
  funext i
  rw [torusHalf_apply, Pi.smul_apply, gen]
  by_cases hij : i = j
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same, halfHom_one, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, halfHom_zero, smul_zero]

omit [Finite G] in
theorem barD_eq_single (hk : ∀ i, 2 ≤ τ.k i) {j : Fin 3} {d : D}
    (hd : dD.e (Additive.ofMul d) = gen τ.k j) : barD dD hk d = Pi.single j 1 := by
  funext i
  rw [barD, hd, torusBar_apply, gen]
  by_cases hij : i = j
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same]
    exact ZMod.cast_one (dvd_pow_self 2 (by have := hk i; omega))
  · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij]
    exact ZMod.cast_zero

theorem commutators_of_devMat_eq_devD (hfam : τ.m + 2 = τ.n) (hk : ∀ i, 2 ≤ τ.k i) {s : G}
    (hs : s ∈ 𝓡[S, D]) (hd : devMat dD hk s hs = devD) :
    s * (dD.c : G) * s⁻¹ * (dD.c : G)⁻¹ = 1 ∧
      s * (dD.a : G) * s⁻¹ * (dD.a : G)⁻¹ = (dD.a : G) ^ (2 ^ (τ.m + 1)) ∧
      s * (dD.b : G) * s⁻¹ * (dD.b : G)⁻¹ = (dD.b : G) ^ (2 ^ (τ.m + 1)) := by
  have hkk := familyTwo_k hfam
  have hgen : ∀ (j : Fin 3) (d : D), dD.e (Additive.ofMul d) = gen τ.k j → τ.k j = τ.m + 2 →
      devD *ᵥ Pi.single j 1 = Pi.single j 1 →
      s * (d : G) * s⁻¹ * (d : G)⁻¹ = (d : G) ^ (2 ^ (τ.m + 1)) := by
    intro j d hdj hkj hdv
    have h := devMat_val_eq (dD := dD) hk s hs d
    rw [hd, barD_eq_single hk hdj, hdv, torusHalf_single, hkj, show τ.m + 2 - 1 = τ.m + 1 by omega,
      ← hdj, ← map_nsmul, ← ofMul_pow] at h
    have h' := congrArg Subtype.val (Additive.ofMul.injective (dD.e.injective h))
    simpa using h'
  refine ⟨?_, hgen 1 dD.a (StrothWeakTypeData.e_a dD) (by rw [hkk]; rfl) (by decide),
    hgen 2 dD.b (StrothWeakTypeData.e_b dD) (by rw [hkk]; rfl) (by decide)⟩
  have h := devMat_val_eq (dD := dD) hk s hs dD.c
  rw [hd, barD_c, show devD *ᵥ (![1, 0, 0] : Fin 3 → ZMod 2) = 0 by decide, map_zero,
    ← map_zero dD.e, ← ofMul_one] at h
  have h' := congrArg Subtype.val (Additive.ofMul.injective (dD.e.injective h))
  simpa using h'

end DeviationGeneric

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

namespace StrothFrame.IsD

private theorem mem_A_of_involution_of_isD (h : F.IsD D dD) :
    ∀ z ∈ (F.S : Subgroup G), z * z = 1 → z ∈ Subgroup.centralizer (F.A : Set G) →
      z⁻¹ * (dD.uv⁻¹ * z * dD.uv) ∈ F.A → z⁻¹ * (dD.t⁻¹ * z * dD.t) ∈ F.A → z ∈ F.A :=
  fun _ hzS hz2 hzA huv ht =>
    F.mem_A_of_involution hzS hz2 hzA (by rwa [← h.uv_eq]) (by rwa [← h.t_eq])

private theorem u_mem_S' (h : F.IsD D dD) : dD.u ∈ (F.S : Subgroup G) := h.u_eq ▸ F.u_mem_S

omit [Finite G] in
private theorem pow_two_pow_eq_one_of_addEquiv {B : Subgroup G} {k n : ℕ} (hkn : k + 2 ≤ n)
    (e : Additive B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2)))) {b : G}
    (hb : b ∈ B) : b ^ (2 ^ n) = 1 := by
  have hv : ∀ v : ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2)), (2 ^ n : ℕ) • v = 0 := by
    intro v
    obtain ⟨j, rfl⟩ : ∃ j, n = k + 2 + j := ⟨n - (k + 2), by omega⟩
    have h1 : (2 : ZMod (2 ^ k)) ^ (k + 2 + j) = 0 := by
      rw [pow_add, pow_add, show (2 : ZMod (2 ^ k)) ^ k = 0 by
        exact_mod_cast ZMod.natCast_self (2 ^ k)]
      ring
    have h2 : (2 : ZMod (2 ^ (k + 2))) ^ (k + 2 + j) = 0 := by
      rw [pow_add (2 : ZMod (2 ^ (k + 2))) (k + 2) j, show (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = 0 by
        exact_mod_cast ZMod.natCast_self (2 ^ (k + 2))]
      ring
    obtain ⟨p, q, r⟩ := v
    simp only [Prod.smul_mk, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, h1, h2, zero_mul]
    rfl
  have h := hv (e (Additive.ofMul ⟨b, hb⟩))
  rw [← map_nsmul, ← ofMul_pow] at h
  have h' : (⟨b, hb⟩ : B) ^ (2 ^ n) = 1 := by
    apply Additive.ofMul.injective
    apply e.injective
    rw [h, ofMul_one, map_zero]
  simpa using congrArg Subtype.val h'

theorem stroth_2_25_frame_two (h : F.IsD D dD) (hfam : τ.m + 2 = τ.n) (hm : 2 ≤ τ.m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (k : ℕ) (hk : k ≤ τ.n - 2) (B : Subgroup G)
    (hBR : B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G))
    (hB : Nonempty (Additive ↥B ≃+ (ZMod (2 ^ k) × ZMod (2 ^ (k + 2)) × ZMod (2 ^ (k + 2))))) :
    B ≤ Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) := by
  obtain ⟨e⟩ := hB
  exact DeviationGeneric.le_centralizer_omegaIn_of_pow_eq_one hfam hm
    (StrothTypeIndex.two_le_k_of_familyTwo hfam hm) h.le_S h.cent h.uv_mem_S h.t_mem_S
    (u_mem_S' h) (h.setting hns) h.A_le h.omegaIn_one_le_A
    (fun _ ha => F.pow_four_eq_one_of_mem_A ha) (mem_A_of_involution_of_isD h) hBR
    (fun _ hb => pow_two_pow_eq_one_of_addEquiv (by omega) e hb)

theorem stroth_2_25_frame_three (h : F.IsD D dD) (hfam : τ.m + 2 = τ.n) (hm : 2 ≤ τ.m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)))
    (hne : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) ≠ D) :
    ∃ s ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
        Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G),
      (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ((omegaIn (τ.n - 2) D : Subgroup G) : Set G) =
        D ⊔ Subgroup.zpowers s ∧
      s * s = (dD.c : G) ∧ ⁅Subgroup.zpowers s, D⁆ = ⁅Subgroup.zpowers dD.ρ, omegaIn 1 D⁆ := by
  have hk := StrothTypeIndex.two_le_k_of_familyTwo hfam hm
  obtain ⟨s, hs, hd, hs2, hsC, heq⟩ := DeviationGeneric.exists_eq_sup_zpowers_of_ne hfam hm hk
    h.le_S h.cent h.uv_mem_S h.t_mem_S (u_mem_S' h) (h.setting hns) h.A_le h.omegaIn_one_le_A
    (fun _ ha => F.pow_four_eq_one_of_mem_A ha) (mem_A_of_involution_of_isD h) hne
  obtain ⟨hc, ha, hb⟩ := DeviationGeneric.commutators_of_devMat_eq_devD hfam hk hs hd
  refine ⟨s, Subgroup.mem_inf.mpr ⟨hs, hsC⟩, heq, hs2, ?_⟩
  rw [dD.commutator_zpowers_eq_of_commutator_familyTwo
      (DeviationGeneric.mem_normalizer_of_mem_R hs)
      (DeviationGeneric.mem_centralizer_of_mem_R hs) hc ha hb,
    dD.commutator_zpowers_rho_omegaIn_one_familyTwo hk hfam]

theorem mem_omegaIn_one_of_familyTwo (h : F.IsD D dD) (hfam : τ.m + 2 = τ.n)
    (hm : 2 ≤ τ.m)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G))
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))) :
    ∀ z ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G),
      z * z = 1 → z ∈ omegaIn 1 D :=
  fun _ hz hz2 => DeviationGeneric.mem_omegaIn_one_of_mul_self_eq_one hfam hm
    (StrothTypeIndex.two_le_k_of_familyTwo hfam hm) h.le_S h.cent h.uv_mem_S h.t_mem_S
    (u_mem_S' h) (h.setting hns) h.A_le h.omegaIn_one_le_A
    (fun _ ha => F.pow_four_eq_one_of_mem_A ha) (mem_A_of_involution_of_isD h) hz hz2

end StrothFrame.IsD

end CFSG.CGT.Stroth77

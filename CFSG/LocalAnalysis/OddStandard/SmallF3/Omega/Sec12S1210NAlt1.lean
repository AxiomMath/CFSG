module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NA1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NBt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S1210NPure
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JA1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L129JBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec12N_alt1 [Finite G] {t : G} {L S V : Subgroup G} (hbd : Sec10BData t L S)
    (hV : IsElemAb2 V 8) (hCV : centralizer (V : Set G) = V ⊔ oddCoreIn (secN V))
    (hΩ : Sec128Alt1 t S L V) (htN : t ∈ secN V) (ht2 : t * t = 1)
    (hcent : Nat.card ↥(secNb V ⊓ Subgroup.centralizer ({betaOf V t} : Set (MulAut ↥V))) = 120) :
    ∃ N0 : Subgroup G, N0 ≤ secN V ∧ (N0.subgroupOf (secN V)).Normal ∧
      N0.relIndex (secN V) = 2 ∧ t ∉ N0 := by
  obtain ⟨φN, hφS, hker⟩ := hΩ
  obtain ⟨ρ, -, hρ, hρker, -⟩ := sec12D_struct hbd
  have hVN : V ≤ secN V := Subgroup.le_normalizer (H := V)
  have hVcard : 128 < Nat.card V := by
    rw [hV.2]
    norm_num
  have hkV : (V.subgroupOf (secN V)).map φN = sec12W_base ρ.ker := by
    rw [hρker]
    exact sec12J_alt1_key hbd hker hVN hV.1 hVcard
  have hO : oddCoreIn (secN V) ≤ centralizer (V : Set G) := by
    rw [hCV]
    exact le_sup_right
  have hVO : ∀ v ∈ V, ∀ o ∈ oddCoreIn (secN V), v * o = o * v := fun v hv o ho =>
    Subgroup.mem_centralizer_iff.mp (hO ho) v hv
  set β : ↥(secN V) →* ↥(secNb V) := sec12J_beta V with hβdef
  have hβ : ∀ n : ↥(secN V), β n = 1 ↔ φN n ∈ sec12W_base ρ.ker := by
    intro n
    rw [← hkV]
    constructor
    · intro h1
      have hn : (n : G) ∈ centralizer (V : Set G) := sec12J_beta_ker V h1
      rw [hCV] at hn
      obtain ⟨v, hv, o, ho, hn'⟩ := sec12J_mem_sup_of_comm hVO hn
      have ho' : o ∈ secN V := CFSG.ClassicalInvolution.Balance.oddCoreIn_le _ ho
      have hxo : n = ⟨v, hVN hv⟩ * ⟨o, ho'⟩ := Subtype.ext hn'
      have hφo : φN ⟨o, ho'⟩ = 1 := by
        have : (⟨o, ho'⟩ : ↥(secN V)) ∈ φN.ker := by
          rw [hker, Subgroup.mem_subgroupOf]
          exact ho
        exact MonoidHom.mem_ker.mp this
      refine Subgroup.mem_map.mpr ⟨⟨v, hVN hv⟩, Subgroup.mem_subgroupOf.mpr hv, ?_⟩
      rw [hxo, map_mul, hφo, mul_one]
    · intro h1
      obtain ⟨x, hx, hxn⟩ := Subgroup.mem_map.mp h1
      have hxV : (x : G) ∈ V := Subgroup.mem_subgroupOf.mp hx
      have h2 : x⁻¹ * n ∈ φN.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxn, inv_mul_cancel]
      rw [hker, Subgroup.mem_subgroupOf] at h2
      have h3 : (x : G)⁻¹ * (n : G) ∈ centralizer (V : Set G) := hO h2
      have h4 : (x : G) ∈ centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact hV.1.comm hh hxV
      have h5 : (n : G) ∈ centralizer (V : Set G) := by
        have := Subgroup.mul_mem _ h4 h3
        simpa using this
      exact sec12N_beta_one V h5
  let f : ↥(secN V) →* Multiplicative (ZMod 2) := RegularWreathProduct.rightHom.comp φN
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨n, hn⟩ := hφS (RegularWreathProduct.inl q)
    exact ⟨n, by
      show (φN n).right = q
      rw [hn]
      rfl⟩
  have htt : (⟨t, htN⟩ : ↥(secN V)) * ⟨t, htN⟩ = 1 := Subtype.ext ht2
  have hC : Nat.card (Subgroup.centralizer ({β ⟨t, htN⟩} : Set ↥(secNb V))) = 120 :=
    sec12N_cent_card htN hcent
  have htr : f ⟨t, htN⟩ ∉ (⊥ : Subgroup (Multiplicative (ZMod 2))) := fun h =>
    sec12N_alt1_false ρ hρ φN hφS β hβ htt (Subgroup.mem_bot.mp h) hC
  have hidx : (⊥ : Subgroup (Multiplicative (ZMod 2))).index = 2 := by
    rw [Subgroup.index_bot,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2)]
    exact Nat.card_zmod 2
  haveI : (⊥ : Subgroup (Multiplicative (ZMod 2))).Normal := Subgroup.normal_bot
  exact sec12N_of_hom f hfsurj hidx htN htr

end CFSG.OddStandard.SmallF3.Omega

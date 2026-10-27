module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.Steps
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Desc
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Endgame

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open

section Step25


theorem step25_holds : Step25 := by
  intro G _ _ d z₀ h49 hd hz h09 h17 h19 h20 h21 h22 h24 S hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSI : S ≤ Ig d := hS.1.1
  have hS2 : IsPGroup 2 S := hS.1.2.1
  have hsylT : fusionIsSylowIn 2 (sylT d) (centralizer ({d.t} : Set G)) :=
    h09.2.2.2.2.2.2.2.1
  have htT : d.t ∈ sylT d := by
    have h := h09.2.2.2.2.2.2.2.2.2.1
    have h1 : d.t ∈ zpowers d.t ⊔ (sylT d ⊓ centralizer ({z₀} : Set G)) :=
      mem_sup_left (mem_zpowers _)
    rwa [← h] at h1
  have htS : d.t ∈ S := hS.2 htT
  have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  have hSH : fusionIsSylowIn 2 S (Hg d) := (h22 S hS).2.1
  have hI : ∀ g ∈ Ig d, g ∈ normalizer (d.s56V : Set G) ∧
      actFun d.s56V g ∈ normalizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
    intro g hg
    obtain ⟨hgN, hgI⟩ := (mem_preIn_iff d.s56V (Is d)).1 hg
    exact ⟨hgN, (Subgroup.mem_inf.1 hgI).1⟩
  have hIA : ∀ g ∈ Ig d, actFun (Ws d) (actFun d.s56V g) ∈ (Ialpha d : Set (MulAut ↥(Ws d))) := by
    intro g hg
    obtain ⟨hgN, hgI⟩ := (mem_preIn_iff d.s56V (Is d)).1 hg
    exact actFun_mem_imgIn hgI (Subgroup.mem_inf.1 hgI).1
  have hAS : ∀ s ∈ S, actFun (Ws d) (actFun d.s56V s) ∈ (Alpha d S : Set (MulAut ↥(Ws d))) := by
    intro s hs
    have hsI := hSI hs
    obtain ⟨hsN, hsI'⟩ := (mem_preIn_iff d.s56V (Is d)).1 hsI
    exact actFun_mem_imgIn (actFun_mem_imgIn hs hsN) (Subgroup.mem_inf.1 hsI').1
  have hAS' : ∀ σ ∈ (Alpha d S : Set (MulAut ↥(Ws d))),
      ∃ s ∈ S, σ = actFun (Ws d) (actFun d.s56V s) := by
    intro σ hσ
    obtain ⟨a, haS, -, rfl⟩ := (mem_imgIn_iff (Ws d) (img d S)).1 hσ
    obtain ⟨s, hsS, -, rfl⟩ := (mem_imgIn_iff d.s56V S).1 haS
    exact ⟨s, hsS, rfl⟩
  have hP3 : {x | x ∈ (Alpha d S : Set (MulAut ↥(Ws d))) ∧
        ∃ i ∈ (Ialpha d : Set (MulAut ↥(Ws d))),
          x = i * actFun (Ws d) (actFun d.s56V d.t) * i⁻¹} =
      {x | ∃ s ∈ (Alpha d S : Set (MulAut ↥(Ws d))),
        x = s * actFun (Ws d) (actFun d.s56V d.t) * s⁻¹} :=
    (h21.2.1 S hS).2.2
  have h620 : ∀ h ∈ normalizer (d.s56V : Set G), h * d.t * h⁻¹ ∈ Ig d → h ∈ Ig d :=
    fun h hh hI' => (h20.2.2.2.2.2.2.1 h hh hI').2
  have hWab : IsElemAbelian 2 (Ws d) := h19.2.2.2.2.2.2.1
  have hWcard : Nat.card (Ws d) =
      Nat.card ↥(Ws d ⊓ centralizer ({actFun d.s56V d.t} : Set (MulAut ↥d.s56V))) *
        Nat.card ↥(Ws d ⊓ centralizer ({actFun d.s56V d.t} : Set (MulAut ↥d.s56V))) := by
    have hq : IsElemAbQuot (Ws d) (Us d) 4 := h19.2.2.2.2.2.1
    have h2 : Ws d ⊓ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)) = Us d := h20.2.2.2.1
    have h3 := Subgroup.relIndex_mul_card (Us d) (Ws d)
    rw [inf_eq_left.mpr hq.1, hq.2.2.2.2] at h3
    have h4 : Nat.card (Ws d) = 2 ^ 8 := h19.2.2.2.2.2.2.2
    have h5 : Nat.card (Us d) = 2 ^ 4 := by
      rw [h4] at h3
      have : 2 ^ 4 * Nat.card (Us d) = 2 ^ 4 * 2 ^ 4 := by rw [h3]; norm_num
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    show Nat.card (Ws d) = Nat.card ↥(Ws d ⊓ centralizer ({star d d.t} : Set (MulAut ↥d.s56V))) *
      Nat.card ↥(Ws d ⊓ centralizer ({star d d.t} : Set (MulAut ↥d.s56V)))
    rw [h2, h5, h4]
    norm_num
  have hWsyl : fusionIsSylowIn 2 (Ws d)
      (centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) ⊓
        imgIn d.s56V (normalizer (d.s56V : Set G))) := h20.2.2.2.2.1
  have hWS : Ws d ≤ imgIn d.s56V S := by
    have h := (h22 S hS).1.1
    have hmem : Ws d ∈ maxElemAbelian2 (img d S) := by rw [h]; exact rfl
    exact hmem.1
  have hTrans : ∀ S₀ : Subgroup G, fusionIsSylowIn 2 S₀ (centralizer (d.s56V : Set G)) →
      (∀ s ∈ S₀, d.t * s * d.t⁻¹ ∈ S₀) →
      ∀ a ∈ {x : G | (∃ h ∈ normalizer (d.s56V : Set G), h * d.t * h⁻¹ = x) ∧
        ∃ s ∈ S₀, x = s * d.t},
      ∀ b ∈ {x : G | (∃ h ∈ normalizer (d.s56V : Set G), h * d.t * h⁻¹ = x) ∧
        ∃ s ∈ S₀, x = s * d.t}, ∃ s ∈ S₀, s * a * s⁻¹ = b :=
    fun S₀ h1 h2 a ha b hb => h17.2.2.2.2.1 S₀ h1 h2 a ha b hb
  have hfusS : d.tG ∩ (S : Set G) = {x | ∃ s ∈ S, s * d.t * s⁻¹ = x} := by
    ext x
    constructor
    · rintro ⟨⟨g, rfl⟩, hxS⟩
      have hxH : g * d.t * g⁻¹ ∈ Hg d := preIn_le_normalizer _ _ (hSI hxS)
      have hx' : g * d.t * g⁻¹ ∈ d.tG ∩ (Hg d : Set G) := ⟨⟨g, rfl⟩, hxH⟩
      rw [h24] at hx'
      exact P6.exists_conj_of_mem_conj_normalizer hI hSI htS ht2 hS2 hSH hIA hAS hAS' hP3 h620
        hWab hWcard hWsyl hWS hTrans hxS hx'
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, rfl⟩, mul_mem (mul_mem hs htS) (inv_mem hs)⟩
  refine ⟨hfusS, ?_⟩
  have hfus : ∀ g : G, g⁻¹ * d.t * g ∈ S → ∃ s ∈ S, g⁻¹ * d.t * g = s⁻¹ * d.t * s := by
    intro g hg
    have h1 : g⁻¹ * d.t * g ∈ d.tG ∩ (S : Set G) := ⟨⟨g⁻¹, by simp⟩, hg⟩
    rw [hfusS] at h1
    obtain ⟨s, hs, hsg⟩ := h1
    exact ⟨s⁻¹, inv_mem hs, by rw [← hsg]; simp⟩
  have hTeq : S ⊓ centralizer ({d.t} : Set G) = sylT d :=
    hsylT.2.2 _ inf_le_right hS2.to_inf_left (le_inf hS.2 hsylT.1)
  have hCS : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ centralizer ({d.t} : Set G))
      (centralizer ({d.t} : Set G)) := by
    rw [hTeq]
    exact P6.isSylowOf_of_fusionIsSylowIn hsylT
  exact CFSG.LocalAnalysis.EvenBN.Tits.S56.s56_exists_sylow_eq S d.t hS2 htS hCS hfus

end Step25

end CFSG.LocalAnalysis.EvenBN.Tits.N

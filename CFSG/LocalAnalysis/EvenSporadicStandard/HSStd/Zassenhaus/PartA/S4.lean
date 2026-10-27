module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Stages
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S4Split

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup Wreath Open
open scoped commutatorElement

theorem odd_card_fusionOddCore_s4 (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem s4 : StepS4 := by
  intro G _ _ L t E W z hb a
  let C : Subgroup G := Cen a.y
  let yC : ↥C := ⟨a.y, mem_Cen.2 rfl⟩
  let tC : ↥C := ⟨t, a.t_cy⟩
  let O : Subgroup ↥C := fusionOddCore ↥C
  let Y : Subgroup ↥C := zpowers yC
  let f : ↥C →* Wr2 (Equiv.Perm (Fin 5)) := a.ι.comp (oMk C)
  have hOG : fusionOddCoreOf C = O.map C.subtype := rfl
  have hzp : ∀ x : ↥C, (x : G) ∈ zpowers a.y → x ∈ Y := by
    rintro x ⟨n, hn⟩
    refine ⟨n, Subtype.ext ?_⟩
    simpa using hn
  have hYc : Y ≤ center ↥C := by
    rw [zpowers_le]
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (mem_Cen.1 g.2)
  have hOmem : ∀ o ∈ O, (o : G) ∈ fusionOddCoreOf C := fun o ho => by
    rw [hOG]; exact ⟨o, ho, rfl⟩
  have hOcomm : ∀ o₁ ∈ O, ∀ o₂ ∈ O, ⁅o₁, o₂⁆ ∈ Y := fun o₁ h₁ o₂ h₂ =>
    hzp _ (by
      have := a.O_comm _ (hOmem o₁ h₁) _ (hOmem o₂ h₂)
      exact this)
  have hOinv : ∀ o ∈ O, tC * o * tC⁻¹ * o ∈ Y := fun o ho =>
    hzp _ (by
      have := a.O_inv _ (hOmem o ho)
      simpa [tC] using this)
  have htt : tC * tC = 1 := Subtype.ext hb.t_mul_t
  have hker : ∀ g : ↥C, f g = 1 ↔ g ∈ O := by
    intro g
    change a.ι (oMk C g) = 1 ↔ _
    rw [map_eq_one_iff a.ι a.ι_inj]
    exact QuotientGroup.eq_one_iff g
  have ht : f tC = tau := a.ι_t
  have hbase : ∀ x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5), ∃ g, f g = betaHom x := by
    rintro ⟨u, v⟩
    obtain ⟨q, hq⟩ := a.ι_alt u v
    obtain ⟨g, rfl⟩ := oMk_surjective C q
    exact ⟨g, hq⟩
  have hodd : Odd (Nat.card O) := odd_card_fusionOddCore_s4 ↥C
  obtain ⟨K₁C, K₂C, hK1O, hK12, hK1K2, hK1t, hK2t, ⟨e, he⟩, hdec, hsup⟩ :=
    s4_split O Y hodd hYc hOcomm htt hOinv f hker ht hbase
  have hsubinj : Function.Injective C.subtype := Subtype.val_injective
  have hconj : conjSub t (K₁C.map C.subtype) = K₂C.map C.subtype := by
    ext x
    constructor
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨tC * k * tC⁻¹, hK1t k hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨_, ⟨tC * k * tC⁻¹, hK2t k hk, rfl⟩, ?_⟩
      have h1 : tC * (tC * k * tC⁻¹) * tC⁻¹ = k := by
        calc tC * (tC * k * tC⁻¹) * tC⁻¹ = (tC * tC) * k * (tC⁻¹ * tC⁻¹) := by group
          _ = k := by
            have : tC⁻¹ * tC⁻¹ = 1 := by
              rw [← mul_inv_rev, htt, inv_one]
            rw [htt, this]; group
      have := congrArg Subtype.val h1
      simpa [tC] using this
  refine ⟨{ toPA3 := a
            K₁ := K₁C.map C.subtype
            eK₁ := (Subgroup.equivMapOfInjective K₁C C.subtype hsubinj).symm.trans e
            K₁_le := ?_
            K₁_O := ?_
            K₁_K₁t := ?_
            K₁_inf := ?_
            K₁_ι := ?_
            K₁_onto := ?_
            P₁_eq := ?_
            O_inf := ?_ }⟩
  · exact Subgroup.map_subtype_le K₁C
  · rintro _ ⟨k, hk, rfl⟩
    rw [hOG, Subgroup.mem_centralizer_iff]
    rintro _ ⟨o, ho, rfl⟩
    exact congrArg Subtype.val (hK1O k hk o ho).symm
  · rw [hconj]
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k', hk', rfl⟩
    exact congrArg Subtype.val (hK12 k hk k' hk').symm
  · rw [hconj, eq_bot_iff]
    rintro x ⟨⟨k, hk, rfl⟩, ⟨k', hk', hkk'⟩⟩
    have : k' = k := hsubinj hkk'
    subst this
    have := hK1K2 k' hk hk'
    simp [this]
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨e ⟨k, hk⟩, ?_⟩
    have h1 := he ⟨k, hk⟩
    exact h1
  · intro σ
    refine ⟨((e.symm σ : ↥K₁C) : ↥C), ?_, ?_⟩
    · exact ⟨_, (e.symm σ).2, rfl⟩
    · have h1 := he (e.symm σ)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
  · rintro g ⟨hg, u, v, huv⟩
    have hf : f ⟨g, hg⟩ = betaHom (u, v) := huv
    obtain ⟨o, ho, k₁, hk₁, k₂, hk₂, hgeq⟩ := hdec (u, v) ⟨g, hg⟩ hf
    have hg' : g = (o : G) * (k₁ : G) * (k₂ : G) := congrArg Subtype.val hgeq
    rw [SetLike.mem_coe, hg']
    have hk₂' : (k₂ : G) ∈ conjSub t (K₁C.map C.subtype) := by
      rw [hconj]; exact ⟨k₂, hk₂, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left (hOmem o ho)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨k₁, hk₁, rfl⟩)))
      (Subgroup.mem_sup_right hk₂')
  · rw [hconj, eq_bot_iff]
    rintro x ⟨hxO, hxs⟩
    rw [← Subgroup.map_sup] at hxs
    obtain ⟨s, hs, rfl⟩ := hxs
    rw [hOG] at hxO
    obtain ⟨o, ho, hos⟩ := hxO
    have : o = s := hsubinj hos
    subst this
    have := hsup o hs ho
    simp [this]

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

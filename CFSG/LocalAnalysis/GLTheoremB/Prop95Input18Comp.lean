module

public import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveOverlap
public import CFSG.Goldschmidt.Steps.G37Transport

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

section Layer

variable {X : Type} [Group X]

@[expose] def compE (X : Type) [Group X] : Subgroup X :=
  ⨆ (K : Subgroup X) (_ : IsComponentOf K ⊤), K

theorem le_compE {K : Subgroup X} (hK : IsComponentOf K ⊤) : K ≤ compE X :=
  le_iSup₂_of_le K hK le_rfl

theorem compE_le {N : Subgroup X} (h : ∀ K : Subgroup X, IsComponentOf K ⊤ → K ≤ N) :
    compE X ≤ N :=
  iSup₂_le fun K hK => h K hK

theorem isComponentOf_conj {K : Subgroup X} (hK : IsComponentOf K ⊤) (g : X) :
    IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ := by
  have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (MulAut.conj g) hK
  rwa [Subgroup.map_equiv_top] at h

theorem comp_comm [Finite X] {K L : Subgroup X} (hK : IsComponentOf K ⊤) (hL : IsComponentOf L ⊤)
    (hne : K ≠ L) {x y : X} (hx : x ∈ K) (hy : y ∈ L) : x * y = y * x :=
  CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.components_commute hK hL hne x hx y hy

theorem compE_normalizes [Finite X] {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    compE X ≤ Subgroup.normalizer (K : Set X) := by
  refine compE_le fun L hL => ?_
  by_cases hLK : L = K
  · subst hLK
    exact Subgroup.le_normalizer
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have hc : ∀ w ∈ K, x * w * x⁻¹ = w := fun w hw => by
      rw [comp_comm hL hK hLK hx hw]; group
    have hc' : ∀ w ∈ K, x⁻¹ * w * x⁻¹⁻¹ = w := fun w hw => by
      rw [comp_comm hL hK hLK (L.inv_mem hx) hw]; group
    intro z
    constructor
    · intro hz
      rw [hc z hz]
      exact hz
    · intro hz
      have e1 : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = x * z * x⁻¹ := hc' _ hz
      have e2 : z = x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ := by group
      rw [e2, e1]
      exact hz

theorem compE_normal : (compE X).Normal := by
  have hconj : ∀ g : X, (compE X).map (MulAut.conj g).toMonoidHom ≤ compE X := by
    intro g
    unfold compE
    rw [Subgroup.map_iSup]
    refine iSup_le fun K => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hK => ?_
    exact le_compE (isComponentOf_conj hK g)
  refine ⟨fun n hn g => ?_⟩
  have h := hconj g (Subgroup.mem_map_of_mem _ hn)
  have e : (MulAut.conj g).toMonoidHom n = g * n * g⁻¹ := rfl
  rw [← e]
  exact h

end Layer

section Top

variable {X : Type} [Group X] [Finite X]

theorem glaPPrimeCoreOf_top_eq_bot {p : ℕ} (hO : GLAPPrimeCore p X = ⊥) :
    GLAPPrimeCoreOf p (⊤ : Subgroup X) = ⊥ := by
  have hcore : GLAPPrimeCore p ↥(⊤ : Subgroup X) = ⊥ := by
    have h := glaPPrimeCore_map_iso p (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X)
    rw [hO] at h
    exact Subgroup.map_injective (Subgroup.topEquiv : ↥(⊤ : Subgroup X) ≃* X).injective
      (by simpa using h)
  unfold GLAPPrimeCoreOf
  rw [hcore, Subgroup.map_bot]

theorem le_glaPPrimeCoreOf_of_coprime {p : ℕ} (hp : p.Prime) {S A : Subgroup X}
    (hS : IsSubnormal S A) (hcop : Nat.Coprime p (Nat.card S)) :
    S ≤ GLAPPrimeCoreOf p A := by
  have htop : GLAPPrimeCore p ↥S = ⊤ :=
    top_le_iff.1 (le_sSup (show (⊤ : Subgroup ↥S).Normal ∧ Nat.Coprime p (Nat.card (⊤ : Subgroup ↥S))
      from ⟨inferInstance, by rwa [Subgroup.card_top]⟩))
  have hself : S ≤ GLAPPrimeCoreOf p S := by
    intro s hs
    refine ⟨⟨s, hs⟩, ?_, rfl⟩
    rw [htop]
    exact Subgroup.mem_top _
  exact hself.trans (glaPPrimeCoreOf_le_of_isSubnormal hp hS)

end Top

section Burnside

variable {X : Type} [Group X] [Finite X]

theorem not_central_sylow {p : ℕ} [hpF : Fact p.Prime] (hO : GLAPPrimeCore p X = ⊥)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) (P : Sylow p ↥K)
    (hP : ∀ x ∈ (P : Subgroup ↥K), ∀ y : ↥K, x * y = y * x) : False := by
  have hPn : (P : Subgroup ↥K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have e : g * n * g⁻¹ = n := by
      rw [← hP n hn g, mul_inv_cancel_right]
    rw [e]
    exact hn
  haveI := hPn
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := (P : Subgroup ↥K)) (Sylow.card_coprime_index P)
  have hPidx : Nat.card H = (P : Subgroup ↥K).index := hH.symm.index_eq_card.symm
  have hndvd : ¬ p ∣ Nat.card H := by
    rw [hPidx]
    exact Sylow.not_dvd_index P
  have hHn : H.Normal := by
    refine ⟨fun h hh g => ?_⟩
    have hg : g ∈ (P : Subgroup ↥K) ⊔ H := by
      rw [hH.sup_eq_top]
      exact Subgroup.mem_top g
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_left).1 hg
    rw [← hyz]
    have hyw := hP y hy (z * h * z⁻¹)
    have e : y * z * h * (y * z)⁻¹ = y * (z * h * z⁻¹) * y⁻¹ := by group
    rw [e]
    have e2 : y * (z * h * z⁻¹) * y⁻¹ = z * h * z⁻¹ := by
      rw [hyw]; group
    rw [e2]
    exact H.mul_mem (H.mul_mem hz hh) (H.inv_mem hz)
  set H' : Subgroup X := H.map K.subtype with hH'
  have hH'K : H' ≤ K := Subgroup.map_subtype_le H
  have hsub : H'.subgroupOf K = H := Subgroup.comap_map_eq_self_of_injective K.subtype_injective H
  have hH'n : (H'.subgroupOf K).Normal := by
    rw [hsub]
    exact hHn
  have hsnH : IsSubnormal H' ⊤ := IsSubnormal.step hH'K hH'n hK.2.1
  have hcardH' : Nat.card H' = Nat.card H :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hcop : Nat.Coprime p (Nat.card H') := by
    rw [hcardH']
    exact (Nat.Prime.coprime_iff_not_dvd hpF.out).2 hndvd
  have hle := le_glaPPrimeCoreOf_of_coprime hpF.out hsnH hcop
  rw [glaPPrimeCoreOf_top_eq_bot hO] at hle
  have hH'bot : H' = ⊥ := eq_bot_iff.2 hle
  have hcardH1 : Nat.card H = 1 := by
    rw [← hcardH', hH'bot, Subgroup.card_bot]
  have hPtop : (P : Subgroup ↥K) = ⊤ := by
    have h1 : (P : Subgroup ↥K).index = 1 := by
      rw [← hPidx, hcardH1]
    exact Subgroup.index_eq_one.1 h1
  have hcen : Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hP x (by rw [hPtop]; exact Subgroup.mem_top x) g).symm
  have hsubsing : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, hcen]
    exact Subgroup.mem_top _
  obtain ⟨_, hs⟩ := hK.2.2
  exact not_subsingleton (↥K ⧸ Subgroup.center ↥K) hsubsing

end Burnside

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem fusion_inf_normal {p : ℕ} [Fact p.Prime] {T H N : Subgroup X}
    (hT : CFSG.Open.fusionIsSylowIn p T H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    CFSG.Open.fusionIsSylowIn p (T ⊓ N) N := by
  obtain ⟨P, hP⟩ := CFSG.Goldschmidt.SStarTransport.exists_sylow_subgroupOf_of_normal hT hNH hN
  refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, fun Q hQN hQp hTQ => ?_⟩
  have hQsub : IsPGroup p (Q.subgroupOf N) := hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQN).symm
  have hle : T.subgroupOf N ≤ Q.subgroupOf N := by
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hTQ (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hx, x.2⟩))
  have hmax := P.is_maximal' hQsub (by rw [hP]; exact hle)
  rw [hP] at hmax
  have h2 := congrArg (Subgroup.map N.subtype) hmax
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hQN] at h2
  exact h2

end Sylow

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.Input18

module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4FamModel
public import CFSG.GH74.Generic.S45.LEvSporGen
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourExactModel
public import Certificates.Certificate5158
public import Certificates.Certificate2022
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73Q
public import CFSG.GH74.GLS.C3.Layer2.L5C19
public import CFSG.GH74.GLS.C3.Layer2.L5C5c
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvSpor
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4Kill
public import CFSG.GH74.Generic.S45.LEvSporAut
public import CFSG.GH74.Generic.S45.LEvSporLeaf1
public import CFSG.GH74.KGroups.L34Aut
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.Sporadic.Co1.Module.TwoBCert
public import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
  CFSG.GH74.Generic.S45
open CFSG.PSL3Four.Native (Tab enumBFS centTabs gTabs gensS r₂T r₃T idTab)
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_R enumerates_C₂ enumerates_C₃
  tabRep_r₂ tabRep_r₃ full_automorphism_action S_le_R conj_mem_S centralizer_S_inf_R r₁R r₂R r₃R r₄R
  orderOf_eq_two_iff eq_conj_of_isConj card_C₁ card_C₂ card_C₃ card_C₄ nonempty_equiv_of_stated
  r₁ r₂ r₃ r₄ C₁ C₂ C₃ C₄)
local notation "S42" => CFSG.ComponentClassification.PSL3Four.S
local notation "R42" => CFSG.ComponentClassification.PSL3Four.R
open scoped commutatorElement

theorem l34_autModel :
    AutModel CFSG.ComponentClassification.PSL3Four.S CFSG.ComponentClassification.PSL3Four.R := by
  obtain ⟨E, hE, -⟩ := full_automorphism_action
  refine
    { le := S_le_R
      conj_mem := fun x hx p hp => conj_mem_S hx hp
      surj := fun α => ?_
      inj := fun x hx hc => ?_ }
  · refine ⟨((E.symm α : ↥CFSG.ComponentClassification.PSL3Four.R) : Equiv.Perm (Fin 42)),
      (E.symm α).2, fun p => ?_⟩
    have := hE (E.symm α) p
    rw [MulEquiv.apply_symm_apply] at this
    exact this
  · have hx' : x ∈ Subgroup.centralizer
        (CFSG.ComponentClassification.PSL3Four.S : Set (Equiv.Perm (Fin 42))) ⊓
        CFSG.ComponentClassification.PSL3Four.R :=
      ⟨Subgroup.mem_centralizer_iff.2 (fun p hp => (hc p hp).symm), hx⟩
    rw [centralizer_S_inf_R, Subgroup.mem_bot] at hx'
    exact hx'

theorem l34_cent_table :
    (∀ x ∈ CFSG.ComponentClassification.PSL3Four.R, x * CFSG.ComponentClassification.PSL3Four.r₂ =
        CFSG.ComponentClassification.PSL3Four.r₂ * x →
      (∀ y ∈ CFSG.ComponentClassification.PSL3Four.C₂, x * y = y * x) →
        x = 1 ∨ x = CFSG.ComponentClassification.PSL3Four.r₂) ∧
    (∀ x ∈ CFSG.ComponentClassification.PSL3Four.R, x * CFSG.ComponentClassification.PSL3Four.r₃ =
        CFSG.ComponentClassification.PSL3Four.r₃ * x →
      (∀ y ∈ CFSG.ComponentClassification.PSL3Four.C₃, x * y = y * x) →
        x = 1 ∨ x = CFSG.ComponentClassification.PSL3Four.r₃) := by
  have h := Certificates.certificate5158
  simp only [Certificates.IvkL34.l34CentOK, Bool.and_eq_true] at h
  obtain ⟨h2, h3⟩ := h
  have key : ∀ (r : Equiv.Perm (Fin 42)) (rT : Tab) (_ : TabRep rT r)
      (Cg : Subgroup (Equiv.Perm (Fin 42)))
      (_ : Enumerates Cg (centTabs 42 (enumBFS 42 gensS 20160).tabs rT).toList)
      (_ : Certificates.IvkL34.centCheck rT (centTabs 42 (enumBFS 42 gensS 20160).tabs rT)
        (enumBFS 42 gTabs 241920).tabs = true),
      ∀ x ∈ CFSG.ComponentClassification.PSL3Four.R, x * r = r * x → (∀ y ∈ Cg, x * y = y * x) →
        x = 1 ∨ x = r := by
    intro r rT hr Cg hC hcheck x hx hxr hxC
    obtain ⟨t, ht, hrepx⟩ := enumerates_R.complete x hx
    have ht' : t ∈ (enumBFS 42 gTabs 241920).tabs := Array.mem_toList_iff.1 ht
    have h1 := (Array.all_eq_true_iff_forall_mem.1 hcheck) t ht'
    have hcomm : Certificates.IvkL34.commB 42 t rT = true :=
      ((hrepx.comp hr).beq_iff (hr.comp hrepx)).2 hxr
    have hCall : (centTabs 42 (enumBFS 42 gensS 20160).tabs rT).all
        (fun y => Certificates.IvkL34.commB 42 t y) = true := by
      rw [Array.all_eq_true_iff_forall_mem]
      intro s hs
      obtain ⟨g, hg, hrepg⟩ := hC.sound s (Array.mem_toList_iff.2 hs)
      exact ((hrepx.comp hrepg).beq_iff (hrepg.comp hrepx)).2 (hxC g hg)
    simp only [hcomm, hCall, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact Or.inl (hrepx.perm_eq (h1 ▸ TabRep.idTab))
    · exact Or.inr (hrepx.perm_eq (h1 ▸ hr))
  exact ⟨key _ _ tabRep_r₂ _ enumerates_C₂ h2, key _ _ tabRep_r₃ _ enumerates_C₃ h3⟩


theorem u2_arith_l34 {n z N : ℕ} (hN : N = 64 ∨ N = 168 ∨ N = 60 ∨ N = 72)
    (hn : n = 2520 ∨ ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ 2 * n = q * (q ^ 2 - 1)) (hz : Odd z)
    (hd : n * z ∣ N) : (N = 168 ∧ n = 168 ∧ z = 1) ∨ (N = 60 ∧ n = 60 ∧ z = 1) := by
  have hz0 : 0 < z := hz.pos
  have hnN : n ∣ N := Dvd.dvd.trans (Dvd.intro z rfl) hd
  have hN0 : 0 < N := by rcases hN with rfl | rfl | rfl | rfl <;> norm_num
  have hnle : n ≤ N := Nat.le_of_dvd hN0 hnN
  have hNle : N ≤ 168 := by rcases hN with rfl | rfl | rfl | rfl <;> norm_num
  rcases hn with rfl | ⟨q, hq5, hqo, hqn⟩
  · exfalso
    omega
  · have hq8 : q ≤ 8 := by
      by_contra hc
      push Not at hc
      have h1 : 9 * (9 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hc (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
      norm_num at h1
      omega
    obtain ⟨k, rfl⟩ := hqo
    have hk : k ≤ 3 := by omega
    have hk2 : 2 ≤ k := by omega
    interval_cases k <;>
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] at hqn
    · have hn60 : n = 60 := by omega
      subst hn60
      rcases hN with rfl | rfl | rfl | rfl
      · exfalso
        omega
      · exfalso
        omega
      · have hz1 : z = 1 := by
          have h1 : 60 * z ∣ 60 * 1 := by simpa using hd
          exact Nat.dvd_one.1 (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)
        exact Or.inr ⟨rfl, rfl, hz1⟩
      · exfalso
        omega
    · have hn168 : n = 168 := by omega
      subst hn168
      rcases hN with rfl | rfl | rfl | rfl
      · exfalso
        omega
      · have hz1 : z = 1 := by
          have h1 : 168 * z ∣ 168 * 1 := by simpa using hd
          exact Nat.dvd_one.1 (Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1)
        exact Or.inl ⟨rfl, rfl, hz1⟩
      · exfalso
        omega
      · exfalso
        omega

theorem l34_card_inf_centralizer_conj {c : Equiv.Perm (Fin 42)}
    (hc : c ∈ R42) (r : Equiv.Perm (Fin 42)) :
    Nat.card ↥(S42 ⊓ Subgroup.centralizer ({c * r * c⁻¹} : Set (Equiv.Perm (Fin 42)))) =
      Nat.card ↥(S42 ⊓ Subgroup.centralizer ({r} : Set (Equiv.Perm (Fin 42)))) :=
  GHInv.card_centralizerIn_conj_of_norm (H := S42) (fun h hh => conj_mem_S hc hh)
    (fun h hh => by simpa using conj_mem_S (Subgroup.inv_mem _ hc) hh) r

theorem l34_inv_cases {x : Equiv.Perm (Fin 42)} (hx : x ∈ R42)
    (hx2 : orderOf x = 2) :
    (∃ c ∈ R42, x = c * r₁ * c⁻¹ ∧
        Nat.card ↥(S42 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42)))) = 64) ∨
      (∃ c ∈ R42, x = c * r₂ * c⁻¹ ∧
        Nat.card ↥(S42 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42)))) = 168) ∨
      (∃ c ∈ R42, x = c * r₃ * c⁻¹ ∧
        Nat.card ↥(S42 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42)))) = 60) ∨
      (∃ c ∈ R42, x = c * r₄ * c⁻¹ ∧
        Nat.card ↥(S42 ⊓ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 42)))) = 72) := by
  have hxR : orderOf (⟨x, hx⟩ : ↥R42) = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  rcases (orderOf_eq_two_iff _).1 hxR with h | h | h | h
  · obtain ⟨c, hc, hce0⟩ := eq_conj_of_isConj h
    have hce : x = c * r₁ * c⁻¹ := hce0
    refine Or.inl ⟨c, hc, hce, ?_⟩
    rw [hce, l34_card_inf_centralizer_conj hc]
    have := card_C₁
    rwa [show CFSG.ComponentClassification.PSL3Four.C₁ = Subgroup.centralizer {r₁} ⊓ S42 from rfl,
      inf_comm] at this
  · obtain ⟨c, hc, hce0⟩ := eq_conj_of_isConj h
    have hce : x = c * r₂ * c⁻¹ := hce0
    refine Or.inr (Or.inl ⟨c, hc, hce, ?_⟩)
    rw [hce, l34_card_inf_centralizer_conj hc]
    have := card_C₂
    rwa [show CFSG.ComponentClassification.PSL3Four.C₂ = Subgroup.centralizer {r₂} ⊓ S42 from rfl,
      inf_comm] at this
  · obtain ⟨c, hc, hce0⟩ := eq_conj_of_isConj h
    have hce : x = c * r₃ * c⁻¹ := hce0
    refine Or.inr (Or.inr (Or.inl ⟨c, hc, hce, ?_⟩))
    rw [hce, l34_card_inf_centralizer_conj hc]
    have := card_C₃
    rwa [show CFSG.ComponentClassification.PSL3Four.C₃ = Subgroup.centralizer {r₃} ⊓ S42 from rfl,
      inf_comm] at this
  · obtain ⟨c, hc, hce0⟩ := eq_conj_of_isConj h
    have hce : x = c * r₄ * c⁻¹ := hce0
    refine Or.inr (Or.inr (Or.inr ⟨c, hc, hce, ?_⟩))
    rw [hce, l34_card_inf_centralizer_conj hc]
    have := card_C₄
    rwa [show CFSG.ComponentClassification.PSL3Four.C₄ = Subgroup.centralizer {r₄} ⊓ S42 from rfl,
      inf_comm] at this


theorem ivk73_l34 :
    Ivk73Empty (fun X _ => LieModel X .PSL 3 2 2) := by
  intro N _ _ L K Q h hL
  have hst := CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  obtain ⟨θ⟩ := nonempty_equiv_of_stated ↥L hst
  have hA := l34_autModel
  have := h.normal
  have hC : centralizer (L : Set N) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    exact h.cent_trivial n (fun l hl => (Subgroup.mem_centralizer_iff.1 hn l hl).symm)
  set ι : N →* Equiv.Perm (Fin 42) := hA.embed L θ with hιdef
  have hι : Function.Injective ι := hA.embed_injective L θ hC
  have hιR : ∀ x, ι x ∈ R42 := fun x => hA.embed_mem L θ x
  have hιL : ∀ s : ↥L, ι (s : N) = ((θ s : ↥S42) : Equiv.Perm (Fin 42)) :=
    fun s => hA.embed_coe L θ s
  have hιLmem : ∀ x ∈ L, ι x ∈ S42 := fun x hx => by
    have := hιL ⟨x, hx⟩
    rw [show ((⟨x, hx⟩ : ↥L) : N) = x from rfl] at this
    rw [this]
    exact (θ ⟨x, hx⟩).2
  obtain ⟨E, hEQ, hEa, hE4⟩ := h.exists_E
  obtain ⟨e₁, he₁E, e₂, he₂E, he₁2, he₂2, he₁₂⟩ :=
    CFSG.GH74.Generic.S45.exists_two_involutions hEa (by omega : 4 ≤ Nat.card ↥E)
  have hEQc : E ≤ centralizer (K : Set N) := hEQ.trans h.Q_sylow.le
  have hcomm : e₂ * e₁ = e₁ * e₂ := by
    have := hEa.toIsMulCommutative.is_comm.comm (⟨e₂, he₂E⟩ : ↥E) ⟨e₁, he₁E⟩
    exact congrArg Subtype.val this
  set K' : Subgroup (Equiv.Perm (Fin 42)) := K.map ι with hK'
  have hodd := odd_center_K h.kbar_cases
  obtain ⟨-, n, hn, -, hKcard⟩ := GHInv.u2_card_data' h.K_quasi h.kbar_cases hodd
  have hKK' : Nat.card ↥K' = Nat.card ↥K := Subgroup.card_map_of_injective hι
  have key : ∀ e ∈ E, orderOf e = 2 →
      ((∃ c ∈ R42, ι e = c * r₂ * c⁻¹) ∨ (∃ c ∈ R42, ι e = c * r₃ * c⁻¹)) ∧
        ∀ y, y ∈ K' ↔ (y ∈ S42 ∧ y * ι e = ι e * y) := by
    intro e heE he2
    have heC : e ∈ centralizer (K : Set N) := hEQc heE
    have hιe2 : orderOf (ι e) = 2 := by rw [orderOf_injective ι hι e]; exact he2
    have hK'cent : K' ≤ S42 ⊓ Subgroup.centralizer ({ι e} : Set (Equiv.Perm (Fin 42))) := by
      rintro _ ⟨k, hk, rfl⟩
      refine Subgroup.mem_inf.2 ⟨hιLmem k (h.K_le hk), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_iff.1 heC k hk]
    have hdvd : Nat.card ↥K ∣ Nat.card ↥(S42 ⊓
        Subgroup.centralizer ({ι e} : Set (Equiv.Perm (Fin 42)))) := by
      rw [← hKK']
      exact Subgroup.card_dvd_of_le hK'cent
    have hKd : n * Nat.card ↥(center ↥K) ∣ Nat.card ↥(S42 ⊓
        Subgroup.centralizer ({ι e} : Set (Equiv.Perm (Fin 42)))) := by
      rw [← hKcard]
      exact hdvd
    have eqK : ∀ N0 : ℕ, Nat.card ↥(S42 ⊓
        Subgroup.centralizer ({ι e} : Set (Equiv.Perm (Fin 42)))) = N0 →
        Nat.card ↥(center ↥K) = 1 → n = N0 →
        K' = S42 ⊓ Subgroup.centralizer ({ι e} : Set (Equiv.Perm (Fin 42))) := by
      intro N0 hN0 hz hnN
      refine Subgroup.eq_of_le_of_card_ge hK'cent ?_
      rw [hKK', hKcard, hz, hN0, hnN, mul_one]
    have hpair : K' = S42 ⊓ Subgroup.centralizer ({ι e} : Set (Equiv.Perm (Fin 42))) →
        ∀ y, y ∈ K' ↔ (y ∈ S42 ∧ y * ι e = ι e * y) := fun hK'eq y => by
      rw [hK'eq, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    rcases l34_inv_cases (hιR e) hιe2 with ⟨c, hc, hce, hcard⟩ | ⟨c, hc, hce, hcard⟩ |
      ⟨c, hc, hce, hcard⟩ | ⟨c, hc, hce, hcard⟩
    · exfalso
      rw [hcard] at hKd
      rcases u2_arith_l34 (Or.inl rfl) hn hodd hKd with h' | h' <;> omega
    · rw [hcard] at hKd
      rcases u2_arith_l34 (Or.inr (Or.inl rfl)) hn hodd hKd with ⟨-, hn168, hz1⟩ | ⟨h60, -, -⟩
      · exact ⟨Or.inl ⟨c, hc, hce⟩, hpair (eqK 168 hcard hz1 hn168)⟩
      · omega
    · rw [hcard] at hKd
      rcases u2_arith_l34 (Or.inr (Or.inr (Or.inl rfl))) hn hodd hKd with
        ⟨h168, -, -⟩ | ⟨-, hn60, hz1⟩
      · omega
      · exact ⟨Or.inr ⟨c, hc, hce⟩, hpair (eqK 60 hcard hz1 hn60)⟩
    · exfalso
      rw [hcard] at hKd
      rcases u2_arith_l34 (Or.inr (Or.inr (Or.inr rfl))) hn hodd hKd with h' | h' <;> omega
  obtain ⟨hcl₁, hK₁⟩ := key e₁ he₁E he₁2
  obtain ⟨-, hK₂⟩ := key e₂ he₂E he₂2
  obtain ⟨hT2, hT3⟩ := l34_cent_table
  have finish : ∀ (r : Equiv.Perm (Fin 42)) (Cg : Subgroup (Equiv.Perm (Fin 42))),
      (∀ y, y ∈ Cg ↔ (y ∈ S42 ∧ y * r = r * y)) →
      (∀ x ∈ R42, x * r = r * x → (∀ y ∈ Cg, x * y = y * x) → x = 1 ∨ x = r) →
      ∀ c ∈ R42, ι e₁ = c * r * c⁻¹ → False := by
    intro r Cg hCg htab c hc hce
    set x := c⁻¹ * ι e₂ * c with hx
    have hxR : x ∈ R42 :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) (hιR e₂)) hc
    have hι12 : ι e₂ * ι e₁ = ι e₁ * ι e₂ := by rw [← map_mul, ← map_mul, hcomm]
    have hxr : x * r = r * x := by
      rw [hce] at hι12
      calc x * r = c⁻¹ * (ι e₂ * (c * r * c⁻¹)) * c := by rw [hx]; group
        _ = c⁻¹ * ((c * r * c⁻¹) * ι e₂) * c := by rw [hι12]
        _ = r * x := by rw [hx]; group
    have hxC : ∀ y ∈ Cg, x * y = y * x := by
      intro y hy
      obtain ⟨hyS, hyr⟩ := (hCg y).1 hy
      have hcyS : c * y * c⁻¹ ∈ S42 := conj_mem_S hc hyS
      have hcy1 : c * y * c⁻¹ * ι e₁ = ι e₁ * (c * y * c⁻¹) := by
        rw [hce]
        calc c * y * c⁻¹ * (c * r * c⁻¹) = c * (y * r) * c⁻¹ := by group
          _ = c * (r * y) * c⁻¹ := by rw [hyr]
          _ = c * r * c⁻¹ * (c * y * c⁻¹) := by group
      have hmemK' : c * y * c⁻¹ ∈ K' := (hK₁ _).2 ⟨hcyS, hcy1⟩
      have hcy2 : c * y * c⁻¹ * ι e₂ = ι e₂ * (c * y * c⁻¹) := ((hK₂ _).1 hmemK').2
      calc x * y = c⁻¹ * (ι e₂ * (c * y * c⁻¹)) * c := by rw [hx]; group
        _ = c⁻¹ * ((c * y * c⁻¹) * ι e₂) * c := by rw [hcy2]
        _ = y * x := by rw [hx]; group
    have hι2x : ι e₂ = c * x * c⁻¹ := by rw [hx]; group
    rcases htab x hxR hxr hxC with h1 | h1
    · have h2 : ι e₂ = 1 := by rw [hι2x, h1]; group
      have he2one : e₂ = 1 := hι (by rw [h2, map_one])
      rw [he2one, orderOf_one] at he₂2
      omega
    · have h2 : ι e₂ = ι e₁ := by rw [hι2x, h1, hce]
      exact he₁₂ (hι h2)
  rcases hcl₁ with ⟨c, hc, hce⟩ | ⟨c, hc, hce⟩
  · exact finish r₂ C₂ (fun y => by
      rw [show C₂ = Subgroup.centralizer {r₂} ⊓ S42 from rfl, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff, and_comm]) hT2 c hc hce
  · exact finish r₃ C₃ (fun y => by
      rw [show C₃ = Subgroup.centralizer {r₃} ⊓ S42 from rfl, Subgroup.mem_inf,
        Subgroup.mem_centralizer_singleton_iff, and_comm]) hT3 c hc hce

end CFSG.GH74.GLS.IVK

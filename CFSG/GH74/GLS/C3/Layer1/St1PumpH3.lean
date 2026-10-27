module

public import CFSG.GH74.GLS.C3.Layer1.St1PumpH1

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpH1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2
  CFSG.GH74.GLS.C3.Layer1.P47 CFSG.GH74.Uniqueness.SU.SU1
open scoped Pointwise commutatorElement

section Lift

theorem exists_big_elemAbelian_le {G : Type} [Group G] [Finite G] (K B : Subgroup G)
    (hBea : CFSG.IsElementaryAbelian 2 ↥B)
    (hBsec : B ≤ centralizerSection K (pPrimeCoreOf 2 K))
    (V : Subgroup (kBar K)) (hVsq : ∀ v ∈ V, v * v = 1) (hV4 : 4 ∣ Nat.card ↥V)
    (hZ : ∀ z : kBar K, (∀ w : kBar K, z * w = w * z) → z = 1) :
    ∃ (m : ℕ) (Q : Subgroup G), 2 ≤ m ∧ (∀ q ∈ Q, q * q = 1) ∧
      Nat.card ↥Q = Nat.card ↥B * 2 ^ m ∧ Q ≤ B ⊔ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBp : IsPGroup 2 ↥B := CFSG.IsElementaryAbelian.isPGroup 2 ↥B
  have hBsq : ∀ b ∈ B, b * b = 1 := fun b hb => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b hb
    rwa [sq] at this
  set YK : Subgroup ↥K := pPrimeCore 2 ↥K with hYK
  set π : ↥K →* kBar K := QuotientGroup.mk' YK with hπ
  set Y : Subgroup G := pPrimeCoreOf 2 K with hY
  set EK : Subgroup ↥K := V.comap π with hEK
  set E : Subgroup G := EK.map K.subtype with hE
  have hπker : ∀ k : ↥K, π k = 1 ↔ k ∈ YK := fun k => QuotientGroup.eq_one_iff k
  have hYmem : ∀ z : ↥K, (z : G) ∈ Y ↔ z ∈ YK := fun z =>
    Subgroup.mem_map_iff_mem K.subtype_injective
  have hYcop : Nat.Coprime 2 (Nat.card ↥Y) := by
    have h1 : Nat.card ↥Y = Nat.card ↥YK := Subgroup.card_map_of_injective K.subtype_injective
    rw [h1]
    exact pPrimeCore_coprime_card (p := 2) (G := ↥K)
  have hEK_mem : ∀ k : ↥K, k ∈ EK ↔ π k ∈ V := fun k => Iff.rfl
  have hsec : ∀ g ∈ B, g ∈ normalizer (K : Set G) ∧ ∀ k ∈ K, ⁅k, g⁆ ∈ Y := fun g hg => by
    obtain ⟨hgK, -, hgc⟩ := hBsec hg
    exact ⟨hgK, hgc⟩
  have hconjE : ∀ g ∈ B, ∀ e ∈ E, g * e * g⁻¹ ∈ E := by
    intro g hg e he
    obtain ⟨hgK, hgc⟩ := hsec g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 he
    have hkK : (k : G) ∈ K := k.2
    have hgk : g * (k : G) * g⁻¹ ∈ K := (mem_normalizer_iff.1 hgK _).1 hkK
    have hcomm : ⁅g, (k : G)⁆ ∈ Y := by
      rw [← commutatorElement_inv]
      exact Y.inv_mem (hgc _ hkK)
    obtain ⟨yK, hyK, hyKeq⟩ := Subgroup.mem_map.1 hcomm
    refine Subgroup.mem_map.2 ⟨⟨g * (k : G) * g⁻¹, hgk⟩, ?_, rfl⟩
    have hyk : (⟨g * (k : G) * g⁻¹, hgk⟩ : ↥K) = yK * k := by
      apply Subtype.ext
      have : (yK : G) = ⁅g, (k : G)⁆ := hyKeq
      simp only [Subgroup.coe_mul, this, commutatorElement_def]
      group
    rw [hEK_mem, hyk, map_mul, (hπker yK).2 hyK, one_mul]
    exact hk
  have hBnorm : B ≤ normalizer (E : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hconjE g hg h hh, fun hh => ?_⟩
    have := hconjE g⁻¹ (B.inv_mem hg) _ hh
    simpa [mul_assoc] using this
  obtain ⟨P, hPE, hPp, hPcard, hPinv⟩ := exists_normalized_sylow_two E B hBp hBnorm
  have hEK_le : E ≤ K := Subgroup.map_subtype_le _
  have hPK : P ≤ K := hPE.trans hEK_le
  have h4E : 2 ^ 2 ∣ Nat.card ↥E := by
    have h1 : Nat.card ↥E = Nat.card ↥EK := Subgroup.card_map_of_injective K.subtype_injective
    have h2 : EK.map π = V := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) V
    have h3 : Nat.card ↥(EK.map π) ∣ Nat.card ↥EK := Subgroup.card_map_dvd EK π
    rw [h2] at h3
    rw [h1]
    exact (by norm_num : 2 ^ 2 ∣ 4).trans (hV4.trans h3)
  have hm2 : 2 ≤ (Nat.card ↥E).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h4E
  have hPsq : ∀ e ∈ P, e * e = 1 := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 (hPE he)
    have hk2 : π (k * k) = 1 := by
      rw [map_mul]
      exact hVsq _ ((hEK_mem k).1 hk)
    have hkk : ((k * k : ↥K) : G) ∈ Y := (hYmem _).2 ((hπker _).1 hk2)
    exact eq_one_of_mem_of_coprime hYcop hPp (by simpa using hkk) (P.mul_mem he he)
  have hcomm : ∀ b ∈ B, ∀ e ∈ P, b * e = e * b := by
    intro b hb e he
    obtain ⟨hbK, hbc⟩ := hsec b hb
    have h1 : ⁅b, e⁆ ∈ Y := by
      rw [← commutatorElement_inv]
      exact Y.inv_mem (hbc e (hPK he))
    have h2 : ⁅b, e⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (hPinv b hb e he) (P.inv_mem he)
    have h3 : ⁅b, e⁆ = 1 := eq_one_of_mem_of_coprime hYcop hPp h1 h2
    rw [commutatorElement_def] at h3
    have h4 : b * e * b⁻¹ = e := by
      have := mul_inv_eq_one.1 h3
      exact this
    calc b * e = b * e * b⁻¹ * b := by group
      _ = e * b := by rw [h4]
  have hdisj : ∀ b ∈ B, b ∈ P → b = 1 := by
    intro b hb hbP
    obtain ⟨kb, hkb, hkbeq⟩ := Subgroup.mem_map.1 (hPE hbP)
    have hkb' : (kb : G) = b := hkbeq
    have hcen : ∀ w : kBar K, π kb * w = w * π kb := by
      intro w
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective w
      show π kb * π k' = π k' * π kb
      rw [← map_mul, ← map_mul]
      show ((kb * k' : ↥K) : ↥K ⧸ YK) = ((k' * kb : ↥K) : ↥K ⧸ YK)
      rw [QuotientGroup.eq]
      refine (hYmem _).1 ?_
      have h1 := (hsec b⁻¹ (B.inv_mem hb)).2 ((k' : G)⁻¹) (K.inv_mem k'.2)
      have h2 : (((kb * k')⁻¹ * (k' * kb) : ↥K) : G) = ⁅(k' : G)⁻¹, b⁻¹⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, hkb']
        group
      rw [h2]
      exact h1
    have h1 : π kb = 1 := hZ _ hcen
    have h2 : (kb : G) ∈ Y := (hYmem _).2 ((hπker _).1 h1)
    rw [hkb'] at h2
    exact eq_one_of_mem_of_coprime hYcop hPp h2 hbP
  let φ : ↥B × ↥P →* G :=
    MonoidHom.noncommCoprod B.subtype P.subtype (fun b e => by
      show (b : G) * (e : G) = (e : G) * (b : G)
      exact hcomm b b.2 e e.2)
  have hφinj : Function.Injective φ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨B.subtype_injective, P.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
    intro x hxB hxP
    exact hdisj x hxB hxP
  refine ⟨(Nat.card ↥E).factorization 2, φ.range, hm2, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨b, e⟩, rfl⟩
    have h : φ (b, e) = (b : G) * (e : G) := rfl
    rw [h]
    have hb2 := hBsq b b.2
    have he2 := hPsq e e.2
    have hbe : (e : G) * b = b * e := (hcomm b b.2 e e.2).symm
    calc (b : G) * e * ((b : G) * e) = b * (e * b) * e := by group
      _ = b * (b * e) * e := by rw [hbe]
      _ = (b * b) * (e * e) := by group
      _ = 1 := by rw [hb2, he2, one_mul]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, ← hPcard]
  · rintro _ ⟨⟨b, e⟩, rfl⟩
    have h : φ (b, e) = (b : G) * (e : G) := rfl
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left b.2) (Subgroup.mem_sup_right (hPK e.2))

end Lift

section Four

variable {G : Type} [Group G] [Finite G]

theorem four_le_pRank_centralizer
    (hL34 : B_gen4_noL34_elem) (hG : Gen4 G) {x : G} {K : Subgroup G} (hpair : IsIL2Pair x K)
    (hU2 : InU2 (kBar K)) (h2 : 2 ≤ pRank 2 ↥(CxK x K)) :
    4 ≤ pRank 2 ↥(centralizer ({x} : Set G)) := by
  have hq : CFSG.IsQuasisimple (kBar K) := hU2.1
  have hcen : center (kBar K) = ⊥ := center_kBar_eq_bot hL34 hG hpair hU2
  have hZ := eq_one_of_forall_comm hcen
  obtain ⟨V, hVel, hV4⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hq
      (by rw [hcen, Subgroup.card_bot]; exact odd_one))
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := (isElemAbelian_iff.1 hVel).2 v hv
    rwa [sq] at this
  obtain ⟨B, hBle, hBea, hBcard⟩ := exists_elemAbelian_card_pRank (CxK x K)
  obtain ⟨m, Q, hm, hQsq, hQcard, hQle⟩ :=
    exists_big_elemAbelian_le K B hBea (hBle.trans inf_le_right) V hVsq (by rw [hV4]) hZ
  have hQea : CFSG.IsElementaryAbelian 2 ↥Q := isElementaryAbelian_two_of_mul_self Q hQsq
  have hQC : Q ≤ centralizer ({x} : Set G) :=
    hQle.trans (sup_le (hBle.trans inf_le_left) hpair.2.1)
  have := le_pRank_of_elem hQC hQea (k := pRank 2 ↥(CxK x K) + m)
    (by rw [hQcard, hBcard, pow_add])
  omega

end Four

end CFSG.GH74.GLS.C3.Layer1.PumpH1

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.PumpH1

@[expose] def B_prop14_h1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G → ∀ (x : G) (K : Subgroup G), IsIL2Pair x K →
    InU2 (kBar K) → pRank 2 ↥(CxK x K) ≤ 1 → 4 ≤ pRank 2 ↥(centralizer ({x} : Set G))

theorem b_prop14_of_h1
    (hL34 : B_gen4_noL34_elem) (h : B_prop14_h1) : B_prop14 := by
  intro G _ _ hG x K hpair hU2
  by_cases h2 : 2 ≤ pRank 2 ↥(CxK x K)
  · exact four_le_pRank_centralizer hL34 hG.gen4 hpair hU2 h2
  · exact h G hG x K hpair hU2 (by omega)

end CFSG.GH74.GLS

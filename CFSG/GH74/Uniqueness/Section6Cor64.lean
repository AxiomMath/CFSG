module

public import CFSG.GH74.Uniqueness.Section6AGroup
public import CFSG.GH74.Uniqueness.Section6ZJ
public import CFSG.GH74.Uniqueness.Section6Basic
public import CFSG.GH74.Uniqueness.Theorem1Final

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Cor64

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Section6A

omit [Finite X] in
theorem oPrimePrime_le_pPrimeCoreIn (p : ℕ) (D : Subgroup X) :
    oPrimePrime p D ≤ pPrimeCoreIn D :=
  Subgroup.map_subtype_le _

theorem normalizer_pPrimeCoreIn_le_normalizer_oPrimePrime (p : ℕ) (D : Subgroup X) :
    normalizer ((pPrimeCoreIn D : Subgroup X) : Set X) ≤
      normalizer ((oPrimePrime p D : Subgroup X) : Set X) :=
  section8_normalizer_map_subtype_le_of_characteristic (H := pPrimeCoreIn D)
    (K := pPrimeCore p ↥(pPrimeCoreIn D))

omit [Finite X] in
theorem commutator_le_of_le {N A B : Subgroup X} (hA : A ≤ N) (hB : B ≤ N) : ⁅A, B⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact N.mul_mem (N.mul_mem (N.mul_mem (hA ha) (hB hb)) (N.inv_mem (hA ha))) (N.inv_mem (hB hb))

end Section6A

theorem ZDSetup.oPrimePrime_eq_bot_of_prop63
    (S : ZDSetup X Z M) (hP63 : Prop63Stmt Z M)
    {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) {t : X} (ht : t ∈ Z) (htM : t ∉ M)
    (hβ : conjugate M t ∈ omegaFix M (W : Set X))
    (hzθ : z ∈ normalizer ((oPrimePrime p (M ⊓ conjugate M t) : Subgroup X) : Set X)) :
    oPrimePrime p (M ⊓ conjugate M t) = ⊥ := by
  have hZ := S.invariant
  have h := S.prodDisc
  set D : Subgroup X := M ⊓ conjugate M t with hD
  set θ : Subgroup X := oPrimePrime p D with hθ
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have htD : t ∈ normalizer (D : Set X) := mem_normalizer_inf_conjugate ht2
  have htK : t ∈ normalizer ((pPrimeCoreIn D : Subgroup X) : Set X) :=
    mem_normalizer_pPrimeCoreIn htD
  have htθ : t ∈ normalizer (θ : Set X) :=
    Section6A.normalizer_pPrimeCoreIn_le_normalizer_oPrimePrime p D htK
  have hKθ : pPrimeCoreIn D ≤ normalizer (θ : Set X) :=
    Subgroup.le_normalizer.trans (Section6A.normalizer_pPrimeCoreIn_le_normalizer_oPrimePrime p D)
  have hLθ : lSubgroup M z t ≤ normalizer (θ : Set X) := by
    refine sup_le (sup_le (Subgroup.zpowers_le.mpr hzθ) (Subgroup.zpowers_le.mpr htθ)) ?_
    exact Section6A.commutator_le_of_le (Subgroup.zpowers_le.mpr htθ) hKθ
  have hLtop : lSubgroup M z t = ⊤ := hP63 z p W hW t ht htM hβ
  have hNtop : normalizer (θ : Set X) = ⊤ := top_unique (hLtop ▸ hLθ)
  have hθn : θ.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  rcases hsimple.eq_bot_or_eq_top_of_normal θ with hbot | htop
  · exact hbot
  · exfalso
    have hθM : θ ≤ M :=
      (Section6A.oPrimePrime_le_pPrimeCoreIn p D).trans ((pPrimeCoreIn_le D).trans inf_le_left)
    exact h.ne_top (top_unique (htop ▸ hθM))

theorem ZDSetup.not_mem_normalizer_zjSubgroup_of_prop63
    (S : ZDSetup X Z M)
    (hP63 : Prop63Stmt Z M) {z : X} {p : ℕ} {W : Subgroup X} (hW : T4Cand Z M z p W) {t : X}
    (ht : t ∈ Z) (htM : t ∉ M) (hβ : conjugate M t ∈ omegaFix M (W : Set X))
    (hθ : oPrimePrime p (M ⊓ conjugate M t) = ⊥) {R : Subgroup X}
    (hRD : R ≤ M ⊓ conjugate M t) (hRp : IsPGroup p R)
    (hQ : ∃ Q : Subgroup X,
      ABGLocalTools.IsSylowOf p Q (pPrimeCoreIn (M ⊓ conjugate M t)) ∧ Q ≤ R) :
    z ∉ normalizer (zjSubgroup p R : Set X) := by
  intro hzZ
  have hZ := S.invariant
  have h := S.prodDisc
  have hp := hW.prime
  have hp2 := hW.ne_two
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQsyl, hQR⟩ := hQ
  set D : Subgroup X := M ⊓ conjugate M t with hD
  set K : Subgroup X := pPrimeCoreIn D with hK
  have ht2 : t * t = 1 := hZ.mul_self_eq_one ht
  have htD : t ∈ normalizer (D : Set X) := mem_normalizer_inf_conjugate ht2
  have htK : t ∈ normalizer (K : Set X) := mem_normalizer_pPrimeCoreIn htD
  have hKD : K ≤ D := pPrimeCoreIn_le D
  have hRK : R ≤ normalizer (K : Set X) := hRD.trans (pPrimeCoreIn_normalizes D)
  have hKodd : Odd (Nat.card K) := odd_card_pPrimeCoreIn D
  have hRodd : Odd (Nat.card R) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hRp
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  set G : Subgroup X := K ⊔ R with hG
  have hKG : K ≤ G := le_sup_left
  have hRG : R ≤ G := le_sup_right
  have hGD : G ≤ D := sup_le hKD hRD
  have hGodd : Odd (Nat.card G) := Section6A.odd_card_sup_of_le_normalizer hRK hKodd hRodd
  have hGsyl : ABGLocalTools.IsSylowOf p R G :=
    Section6A.isSylowOf_sup_of_le hp hRK hRp hQsyl hQR
  have hθ' : pPrimeCore p ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hθ
  have hGcore : pPrimeCore p ↥G = ⊥ := Section6A.pPrimeCore_sup_eq_bot hp hRK hRp hθ'
  have hGnorm : G ≤ normalizer (zjSubgroup p R : Set X) :=
    le_normalizer_zjSubgroup_of_odd hp hGsyl hGodd hGcore
  have hpm : p ∣ zNum Z M := by
    have h2 := hW.two_le_zNumShare hZ h
    unfold zNumShare at h2
    by_contra hnd
    have h0 : (zNum Z M).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnd
    rw [h0, pow_zero] at h2
    omega
  have hmK : zNum Z M ∣ Nat.card K := by
    obtain ⟨h1, h2, -⟩ := h.prop36d hZ ht htM hW.mem_Z hW.mem_M
    rw [← h1, h2]
    exact Subgroup.relIndex_dvd_card _ _
  have hpK : p ∣ Nat.card K := hpm.trans hmK
  have hRne : R ≠ ⊥ := by
    intro hR0
    have hQ0 : Q = ⊥ := by
      rw [hR0, le_bot_iff] at hQR
      exact hQR
    have hv : 1 ≤ (Nat.card K).factorization p :=
      (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hpK
    have hpQ : p ∣ Nat.card Q := by
      rw [hQsyl.card_eq]
      exact dvd_pow_self p (by omega)
    rw [hQ0, Subgroup.card_bot] at hpQ
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpQ)
  have hZ1ne : zjSubgroup p R ≠ ⊥ := zjSubgroup_ne_bot p hp hRp hRne
  have hZs := h.isZStarIn_inf_conjugate_sup hZ ht htM
  have htG : t ∈ normalizer (G : Set X) := by
    refine Section6A.mem_normalizer_sup_of_conj_mem ht2 (fun x hx => ?_) (fun r hr => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp htK x).mp hx)
    · have hrD : r⁻¹ ∈ D := D.inv_mem (hRD hr)
      have hc : r⁻¹ * t * r⁻¹⁻¹ * t⁻¹ ∈ K := commutator_mem_pPrimeCoreIn hZs htD hrD
      have e : t * r * t⁻¹ = r * (r⁻¹ * t * r⁻¹⁻¹ * t⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hr) (Subgroup.mem_sup_left hc)
  have hZsG : IsZStarIn (G ⊔ zpowers t) t :=
    IsZStarIn.restrict ht2 hZs (hGD.trans le_sup_left) htG
  have hbotN : t ∈ normalizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top t
  obtain ⟨Q', hQ'syl, -, htQ'⟩ := exists_invariant_sylow hp hp2 (hZ.1 t ht) htG hZsG bot_le
    IsPGroup.of_bot hbotN
  obtain ⟨w, hwG, hwR⟩ := exists_conj_of_isSylowOf hGsyl hQ'syl
  have hwG' : w ∈ (R ⊔ K : Subgroup X) := by
    rw [sup_comm]
    exact hwG
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right R K hRK] at hwG'
  obtain ⟨r, hr, k, hk, rfl⟩ := hwG'
  have hRr : conjugate R r = R := conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hr)
  rw [← conjugate_conjugate, hRr] at hwR
  rw [← hwR, normalizer_conjugate, mem_conjugate_iff] at htQ'
  have ht₁ : k * t * k⁻¹ ∈ normalizer (zjSubgroup p R : Set X) :=
    normalizer_le_normalizer_zjSubgroup p hp R htQ'
  have hkD : k ∈ D := hKD hk
  have hc : k * t * k⁻¹ * t⁻¹ ∈ K := commutator_mem_pPrimeCoreIn hZs htD hkD
  have hKN : K ≤ normalizer (zjSubgroup p R : Set X) := hKG.trans hGnorm
  have htN : t ∈ normalizer (zjSubgroup p R : Set X) := by
    have e : t = (k * t * k⁻¹ * t⁻¹)⁻¹ * (k * t * k⁻¹) := by group
    rw [e]
    exact (normalizer (zjSubgroup p R : Set X)).mul_mem
      ((normalizer (zjSubgroup p R : Set X)).inv_mem (hKN hc)) ht₁
  have hLN : lSubgroup M z t ≤ normalizer (zjSubgroup p R : Set X) := by
    refine sup_le (sup_le (Subgroup.zpowers_le.mpr hzZ) (Subgroup.zpowers_le.mpr htN)) ?_
    exact Section6A.commutator_le_of_le (Subgroup.zpowers_le.mpr htN) hKN
  have hLtop : lSubgroup M z t = ⊤ := hP63 z p W hW t ht htM hβ
  have hNtop : normalizer (zjSubgroup p R : Set X) = ⊤ := top_unique (hLtop ▸ hLN)
  have hZ1n : (zjSubgroup p R).Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  rcases hsimple.eq_bot_or_eq_top_of_normal (zjSubgroup p R) with hbot | htop
  · exact hZ1ne hbot
  · have hZ1M : zjSubgroup p R ≤ M :=
      (zjSubgroup_le p R).trans (hRD.trans inf_le_left)
    exact h.ne_top (top_unique (htop ▸ hZ1M))

theorem ZDSetup.cor64_of_prop63
    (S : ZDSetup X Z M) (hP63 : Prop63Stmt Z M) : Cor64Stmt Z M := by
  intro z p W hW β hβ hβM hzθ
  have hβΩ : β ∈ omega M := hβ.1
  obtain ⟨t, ht, hMt⟩ := S.prodDisc.exists_swap S.invariant (self_mem_omega M) hβΩ
  subst hMt
  have htM : t ∉ M := fun htM =>
    hβM ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr htM)
  have hθ := S.oPrimePrime_eq_bot_of_prop63 hP63 hW ht htM hβ hzθ
  exact ⟨hθ, fun R hRD hRp hQ =>
    S.not_mem_normalizer_zjSubgroup_of_prop63 hP63 hW ht htM hβ hθ hRD hRp hQ⟩

end Cor64

end CFSG.GH74.Uniqueness

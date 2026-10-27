module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieModelSL2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieReduce
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalTightCommuting
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ClassicalInvolution
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting
open scoped MatrixGroups commutatorElement

variable {H : Type} [Group H] {F : Type} [Field F] [Finite F]

theorem mem_conjSubgroup {g x : H} {J : Subgroup H} :
    x ∈ conjSubgroup g J ↔ g⁻¹ * x * g ∈ J := by
  rw [conjSubgroup, Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

theorem conjSubgroup_eq_rightConjugate (g : H) (J : Subgroup H) :
    conjSubgroup g J = rightConjugate J g⁻¹ := by
  ext x
  rw [mem_conjSubgroup, mem_rightConjugate_iff, inv_inv]

theorem conjSubgroup_conjSubgroup (g h : H) (J : Subgroup H) :
    conjSubgroup g (conjSubgroup h J) = conjSubgroup (g * h) J := by
  ext x
  simp only [mem_conjSubgroup, mul_inv_rev]
  group

@[expose] noncomputable def conjEquiv {J : Subgroup H} (e : J ≃* SL(2, F)) (g : H) :
    conjSubgroup g J ≃* SL(2, F) :=
  (J.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans e

omit [Finite F] in
theorem centralInv_conjEquiv {J : Subgroup H} (e : J ≃* SL(2, F)) (g : H) :
    centralInv (conjEquiv e g) = g * centralInv e * g⁻¹ := rfl

omit [Finite F] in
theorem centralizer_le_normalizer_conj {J : Subgroup H} (e : J ≃* SL(2, F))
    (hCZ : centralizer ({centralInv e} : Set H) ≤ normalizer (J : Set H)) (g : H) :
    centralizer ({centralInv (conjEquiv e g)} : Set H) ≤ normalizer (conjSubgroup g J : Set H) := by
  intro x hx
  rw [centralInv_conjEquiv, mem_centralizer_singleton_iff] at hx
  have hx' : g⁻¹ * x * g ∈ centralizer ({centralInv e} : Set H) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * x * g * centralInv e = g⁻¹ * (x * (g * centralInv e * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * centralInv e * g⁻¹) * x) * g := by rw [hx]
      _ = centralInv e * (g⁻¹ * x * g) := by group
  have hN := hCZ hx'
  rw [mem_normalizer_iff] at hN ⊢
  intro y
  rw [mem_conjSubgroup, mem_conjSubgroup]
  have := hN (g⁻¹ * y * g)
  rw [show g⁻¹ * x * g * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ = g⁻¹ * (x * y * x⁻¹) * g by group]
    at this
  exact this

theorem orderOf_centralInv {J : Subgroup H} (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F)) :
    orderOf (centralInv e) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (centralInv_sq e) (centralInv_ne_one e hF)

theorem tightlyEmbedded_of_centralizer_le [Finite H] {J : Subgroup H} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F))
    (hCZ : centralizer ({centralInv e} : Set H) ≤ normalizer (J : Set H)) : TightlyEmbedded J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, fun g hg => ?_⟩
  · have := orderOf_dvd_natCard (⟨centralInv e, centralInv_mem e⟩ : J)
    rw [Subgroup.orderOf_mk, orderOf_centralInv e hF] at this
    exact even_iff_two_dvd.mpr this
  · by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(J ⊓ rightConjugate J g)) 2 (even_iff_two_dvd.mp hodd)
    rw [Subgroup.orderOf_mk] at hw2
    obtain ⟨hwJ, hwg⟩ := mem_inf.mp hw
    rw [mem_rightConjugate_iff] at hwg
    have hwsq : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hw2
      omega
    have hwz : w = centralInv e := (eq_one_or_centralInv_of_sq e hF hwJ hwsq).resolve_left hw1
    have hgw : g * w * g⁻¹ = centralInv e := by
      refine (eq_one_or_centralInv_of_sq e hF hwg ?_).resolve_left ?_
      · rw [conj_pow, hwsq]
        group
      · intro h
        apply hw1
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = 1 := by rw [h]; group
    apply hg
    apply hCZ
    rw [mem_centralizer_singleton_iff, ← hwz]
    rw [← hwz] at hgw
    calc g * w = (g * w * g⁻¹) * g := by group
      _ = w * g := by rw [hgw]

theorem centralInv_mem_of_isSylowOf [Finite H] {J Q : Subgroup H} (e : J ≃* SL(2, F))
    (hF : Odd (Nat.card F)) (hQ : IsSylowOf 2 Q J) : centralInv e ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2J : 2 ∣ Nat.card J := by
    have := orderOf_dvd_natCard (⟨centralInv e, centralInv_mem e⟩ : J)
    rwa [Subgroup.orderOf_mk, orderOf_centralInv e hF] at this
  have hQc := hQ.card_eq
  have h2Q : 2 ∣ Nat.card Q := by
    rw [hQc]
    have hpos : 0 < (Nat.card J).factorization 2 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2J)
    exact dvd_pow_self 2 hpos.ne'
  obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2 h2Q
  rw [Subgroup.orderOf_mk] at hw2
  have hwsq : w ^ 2 = 1 := by rw [← hw2]; exact pow_orderOf_eq_one w
  have hw1 : w ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw2
    omega
  rw [← (eq_one_or_centralInv_of_sq e hF (hQ.le hw) hwsq).resolve_left hw1]
  exact hw

private theorem sl2Three_exp_aux : ∀ x : SL(2, ZMod 3), x ^ 12 = 1 := by
  decide +kernel

private theorem sl2Three_odd_aux : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 → x ≠ 1 →
    ∃ g : SL(2, ZMod 3), (x * (g * x⁻¹ * g⁻¹)) ^ 4 = 1 ∧ x * (g * x⁻¹ * g⁻¹) ≠ 1 := by
  decide +kernel

theorem eq_bot_of_normal_odd {J N : Subgroup H} (e : J ≃* SL(2, F)) (hF : Odd (Nat.card F))
    (hNJ : N ≤ J) (hJN : J ≤ normalizer (N : Set H)) (hodd : Odd (Nat.card N)) : N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot2 : ∀ y ∈ N, y ^ 4 = 1 → y = 1 := by
    intro y hy hy4
    have hdvd : orderOf y ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨y, hy⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    have h4 : orderOf y ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hy4
    have hcop : Nat.Coprime (2 ^ 2) (Nat.card N) :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h4 hdvd)
  by_cases h3 : Nat.card F = 3
  · classical
    have : Fintype F := Fintype.ofFinite F
    have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
      rw [← Nat.card_eq_fintype_card, h3, ZMod.card]
    set e' : J ≃* SL(2, ZMod 3) := e.trans (sl2RingEquiv (FiniteField.ringEquivOfCardEq hcard))
    rw [eq_bot_iff]
    intro x hx
    rw [mem_bot]
    by_contra hx1
    have hx3 : x ^ 3 = 1 := by
      have h12 : (⟨x, hNJ hx⟩ : J) ^ 12 = 1 :=
        e'.injective (by rw [map_pow, map_one]; exact sl2Three_exp_aux _)
      have hx12 : x ^ 12 = 1 := by simpa using congrArg Subtype.val h12
      have hdvd : orderOf x ∣ Nat.card N := by
        have := orderOf_dvd_natCard (⟨x, hx⟩ : N)
        rwa [Subgroup.orderOf_mk] at this
      have hodd' : Odd (orderOf x) := hodd.of_dvd_nat hdvd
      have h12' : orderOf x ∣ 4 * 3 := orderOf_dvd_of_pow_eq_one hx12
      have hc : Nat.Coprime (orderOf x) 4 :=
        Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hodd')
      exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_left h12')
    have hx3' : e' ⟨x, hNJ hx⟩ ^ 3 = 1 := by
      rw [← map_pow, show (⟨x, hNJ hx⟩ : J) ^ 3 = 1 from Subtype.ext (by simpa using hx3),
        map_one]
    have hx1' : e' ⟨x, hNJ hx⟩ ≠ 1 := fun h => hx1 (by
      have := congrArg Subtype.val (e'.injective (h.trans (map_one e').symm))
      simpa using this)
    obtain ⟨g, hg4, hg1⟩ := sl2Three_odd_aux _ hx3' hx1'
    set j : J := e'.symm g
    have hjx : (j : H) * x⁻¹ * (j : H)⁻¹ ∈ N :=
      (mem_normalizer_iff.mp (hJN j.2) x⁻¹).mp (inv_mem hx)
    have hy := mul_mem hx hjx
    set y : J := ⟨x, hNJ hx⟩ * (j * (⟨x, hNJ hx⟩ : J)⁻¹ * j⁻¹)
    have himg : e' y = e' ⟨x, hNJ hx⟩ * (g * (e' ⟨x, hNJ hx⟩)⁻¹ * g⁻¹) := by
      simp [y, j, map_mul, map_inv]
    have hy4 : y ^ 4 = 1 := e'.injective (by rw [map_pow, himg, hg4, map_one])
    have h4 : (x * ((j : H) * x⁻¹ * (j : H)⁻¹)) ^ 4 = 1 := by
      simpa [y] using congrArg Subtype.val hy4
    apply hg1
    have h1 := hnot2 _ hy h4
    rw [← himg]
    have : y = 1 := Subtype.ext (by simpa [y] using h1)
    rw [this, map_one]
  · have h4 : 4 ≤ Nat.card F := by
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      rcases hF with ⟨m, hm⟩
      omega
    have hNn : (N.subgroupOf J).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      exact (mem_normalizer_iff.mp (hJN g.2) x).mp hx⟩
    rcases normal_cases_of_equiv_sl2 h4 e (N.subgroupOf J) hNn with hb | hc | ht
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hNJ hx⟩ : J) ∈ N.subgroupOf J := mem_subgroupOf.mpr hx
      rw [hb, Subgroup.mem_bot] at this
      rw [mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      have hz : e.symm (-1) ∈ N.subgroupOf J := by
        rw [hc, mem_center_iff_of_equiv_sl2 e, MulEquiv.apply_symm_apply, mem_center_sl2_iff]
        exact Or.inr rfl
      have := hnot2 _ (mem_subgroupOf.mp hz) (by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, centralInv_sq e, one_pow])
      exact centralInv_ne_one e hF this
    · exfalso
      have hz : e.symm (-1) ∈ N.subgroupOf J := ht ▸ Subgroup.mem_top _
      have := hnot2 _ (mem_subgroupOf.mp hz) (by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, centralInv_sq e, one_pow])
      exact centralInv_ne_one e hF this

theorem exists_conj_fixed_or_commute (h3 : SL2OuterComm) [Finite H] (hF : Odd (Nat.card F))
    {J K T : Subgroup H} (e : J ≃* SL(2, F))
    (hCZ : centralizer ({centralInv e} : Set H) ≤ normalizer (J : Set H)) (hJK : J ≤ K)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set H)) :
    ∃ g ∈ K, ∀ τ ∈ T, conjSubgroup τ (conjSubgroup g J) = conjSubgroup g J ∨
      ∀ a ∈ conjSubgroup g J, ∀ b ∈ conjSubgroup τ (conjSubgroup g J), a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := K ⊔ T with hM
  have hMN : M ≤ normalizer (K : Set H) := sup_le Subgroup.le_normalizer hTK
  obtain ⟨Ps, hPs⟩ := (hT.comap_subtype : IsPGroup 2 (T.subgroupOf M)).exists_le_sylow
  set P : Subgroup H := (Ps : Subgroup M).map M.subtype with hPdef
  have hP : IsSylowOf 2 P M := ⟨Ps, rfl⟩
  have hTP : T ≤ P := fun x hx => ⟨⟨x, mem_sup_right hx⟩, hPs hx, rfl⟩
  have hS : IsSylowOf 2 (P ⊓ K) K := hP.inf_of_le_normalizer le_sup_left hMN
  have hP2 : IsPGroup 2 P := hP.isPGroup
  have hSτ : ∀ τ ∈ T, conjSubgroup τ (P ⊓ K) = P ⊓ K := by
    intro τ hτ
    have hτP : τ ∈ normalizer (P : Set H) := Subgroup.le_normalizer (hTP hτ)
    have hτK : τ ∈ normalizer (K : Set H) := hTK hτ
    ext x
    rw [mem_conjSubgroup, mem_inf, mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := (mem_normalizer_iff.mp hτP _).mp h1
        simpa [mul_assoc] using this
      · have := (mem_normalizer_iff.mp hτK _).mp h2
        simpa [mul_assoc] using this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have := (mem_normalizer_iff.mp (inv_mem hτP) _).mp h1
        simpa using this
      · have := (mem_normalizer_iff.mp (inv_mem hτK) _).mp h2
        simpa using this
  obtain ⟨Q₀, hQ₀⟩ := exists_isSylowOf 2 J
  obtain ⟨S', hS', hQS'⟩ : ∃ S' : Subgroup H, IsSylowOf 2 S' K ∧ Q₀ ≤ S' := by
    obtain ⟨R, hR⟩ := ((hQ₀.isPGroup).comap_subtype :
      IsPGroup 2 (Q₀.subgroupOf K)).exists_le_sylow
    exact ⟨(R : Subgroup K).map K.subtype, ⟨R, rfl⟩,
      fun x hx => ⟨⟨x, hJK (hQ₀.le hx)⟩, hR hx, rfl⟩⟩
  obtain ⟨k, hkK, hk⟩ := hS'.exists_mem_conj hS
  refine ⟨k, hkK, ?_⟩
  set J₁ := conjSubgroup k J with hJ₁
  set Q₁ := conjSubgroup k Q₀ with hQ₁
  set e₁ := conjEquiv e k
  have hCZ₁ := centralizer_le_normalizer_conj e hCZ k
  have htight₁ := tightlyEmbedded_of_centralizer_le e₁ hF hCZ₁
  have hQ₁J₁ : IsSylowOf 2 Q₁ J₁ := isSylowOf_map_hom hQ₀ (MulAut.conj k).toMonoidHom
  have hQ₁S : Q₁ ≤ P ⊓ K := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    exact (hk x).mpr (hQS' hx)
  intro τ hτ
  set J₂ := conjSubgroup τ J₁ with hJ₂
  set Q₂ := conjSubgroup τ Q₁ with hQ₂
  set e₂ := conjEquiv e₁ τ
  have hCZ₂ := centralizer_le_normalizer_conj e₁ hCZ₁ τ
  have hQ₂J₂ : IsSylowOf 2 Q₂ J₂ := isSylowOf_map_hom hQ₁J₁ (MulAut.conj τ).toMonoidHom
  have hQ₂S : Q₂ ≤ P ⊓ K := by
    rw [← hSτ τ hτ]
    exact map_mono hQ₁S
  by_cases hJ : J₂ = J₁
  · exact Or.inl hJ
  right
  have hJ₂r : J₂ = rightConjugate J₁ τ⁻¹ := conjSubgroup_eq_rightConjugate τ J₁
  have hτN : τ⁻¹ ∉ normalizer (J₁ : Set H) := by
    intro hN
    apply hJ
    rw [hJ₂r]
    exact (rightConjugate_eq_self_iff J₁ τ⁻¹).mpr hN
  have hodd12 : Odd (Nat.card (J₁ ⊓ J₂ : Subgroup H)) := by
    rw [hJ₂r]
    exact htight₁.2 τ⁻¹ hτN
  set z₁ := centralInv e₁
  set z₂ := centralInv e₂
  have hz₁Q : z₁ ∈ Q₁ := centralInv_mem_of_isSylowOf e₁ hF hQ₁J₁
  have hz₂Q : z₂ ∈ Q₂ := centralInv_mem_of_isSylowOf e₂ hF hQ₂J₂
  have hQne : Q₁ ≠ Q₂ := by
    intro hQ
    have hmem : z₁ ∈ J₁ ⊓ J₂ := mem_inf.mpr ⟨hQ₁J₁.le hz₁Q, hQ₂J₂.le (hQ ▸ hz₁Q)⟩
    have := orderOf_dvd_natCard (⟨z₁, hmem⟩ : ↥(J₁ ⊓ J₂))
    rw [Subgroup.orderOf_mk, orderOf_centralInv e₁ hF] at this
    exact (Nat.not_even_iff_odd.mpr hodd12) (even_iff_two_dvd.mpr this)
  obtain ⟨i₁, hi₁, j₁, hj₁, hij₁, hC₁⟩ := exists_quaternion_pair hF e₁ hQ₁J₁
  obtain ⟨i₂, hi₂, j₂, hj₂, hij₂, hC₂⟩ := exists_quaternion_pair hF e₂ hQ₂J₂
  have hcomm : Commutes Q₁ Q₂ := by
    have hs : Setup J₁ ⊤ Q₁ P :=
      { tight := htight₁
        le_inf := le_inf le_top hQ₁J₁.le
        sylow := fun R hR hR2 hQR => hQ₁J₁.eq_of_le hQR (hR.trans inf_le_right) hR2
        pGroup := hQ₁J₁.isPGroup
        ne_bot := fun h => centralInv_ne_one e₁ hF (by rw [h] at hz₁Q; exact mem_bot.mp hz₁Q)
        S_le := le_top
        S_pGroup := hP2
        le_S := hQ₁S.trans inf_le_left }
    have hΦ : frattini Q₁ ≠ ⊥ := by
      intro h
      have hsq : ∀ x ∈ Q₁, x ^ 2 = 1 := fun x hx => by
        have hmem := CFSG.SectionRank.Ccomm.pow_mem_frattini hQ₁J₁.isPGroup ⟨x, hx⟩
        rw [h, mem_bot] at hmem
        simpa using congrArg Subtype.val hmem
      apply centralInv_ne_one e₁ hF
      show centralInv e₁ = 1
      rw [← hij₁, commutatorElement_def]
      have hi : i₁⁻¹ = i₁ := by rw [inv_eq_iff_mul_eq_one, ← sq, hsq i₁ hi₁]
      have hj : j₁⁻¹ = j₁ := by rw [inv_eq_iff_mul_eq_one, ← sq, hsq j₁ hj₁]
      rw [hi, hj, show i₁ * j₁ * i₁ * j₁ = (i₁ * j₁) ^ 2 by rw [sq]; simp only [mul_assoc],
        hsq _ (mul_mem hi₁ hj₁)]
    exact hs.commutes_conjugatesIn hΦ Q₁
      ⟨1, mem_top _, (rightConjugate_one Q₁).symm, hQ₁S.trans inf_le_left⟩ Q₂
      ⟨τ⁻¹, mem_top _, conjSubgroup_eq_rightConjugate τ Q₁, hQ₂S.trans inf_le_left⟩ hQne
  have hQ₂N : ∀ b ∈ Q₂, b ∈ normalizer (J₁ : Set H) := fun b hb =>
    hCZ₁ (by rw [mem_centralizer_singleton_iff]; exact (hcomm z₁ hz₁Q b hb).symm)
  have hQ₁N : ∀ a ∈ Q₁, a ∈ normalizer (J₂ : Set H) := fun a ha =>
    hCZ₂ (by rw [mem_centralizer_singleton_iff]; exact hcomm a ha z₂ hz₂Q)
  have hz₂C : z₂ ∈ centralizer (J₁ : Set H) := by
    show centralInv e₂ ∈ _
    rw [← hij₂]
    exact commutator_mem_centralizer_of_sl2 h3 hF e₁ (hQ₁J₁.le hi₁) (hQ₁J₁.le hj₁) hC₁
      (hQ₂N i₂ hi₂) (hQ₂N j₂ hj₂) (hcomm i₁ hi₁ i₂ hi₂).symm (hcomm j₁ hj₁ i₂ hi₂).symm
      (hcomm i₁ hi₁ j₂ hj₂).symm (hcomm j₁ hj₁ j₂ hj₂).symm
  have hz₁C : z₁ ∈ centralizer (J₂ : Set H) := by
    show centralInv e₁ ∈ _
    rw [← hij₁]
    exact commutator_mem_centralizer_of_sl2 h3 hF e₂ (hQ₂J₂.le hi₂) (hQ₂J₂.le hj₂) hC₂
      (hQ₁N i₁ hi₁) (hQ₁N j₁ hj₁) (hcomm i₁ hi₁ i₂ hi₂) (hcomm i₁ hi₁ j₂ hj₂)
      (hcomm j₁ hj₁ i₂ hi₂) (hcomm j₁ hj₁ j₂ hj₂)
  have hJ₂N : J₂ ≤ normalizer (J₁ : Set H) := fun b hb =>
    hCZ₁ (by rw [mem_centralizer_singleton_iff]; exact mem_centralizer_iff.mp hz₁C b hb)
  have hJ₁N : J₁ ≤ normalizer (J₂ : Set H) := fun a ha =>
    hCZ₂ (by rw [mem_centralizer_singleton_iff]; exact mem_centralizer_iff.mp hz₂C a ha)
  have hbot : J₁ ⊓ J₂ = ⊥ := by
    refine eq_bot_of_normal_odd e₁ hF inf_le_left (fun x hx => ?_) hodd12
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mul_mem (mul_mem hx h1) (inv_mem hx), (mem_normalizer_iff.mp (hJ₁N hx) y).mp h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, (mem_normalizer_iff.mp (hJ₁N hx) y).mpr h2⟩
      rw [show y = x⁻¹ * (x * y * x⁻¹) * x by group]
      exact mul_mem (mul_mem (inv_mem hx) h1) hx
  intro a ha b hb
  have hc : ⁅a, b⁆ ∈ J₁ ⊓ J₂ := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) by rw [commutatorElement_def]; group]
      exact mul_mem ha ((mem_normalizer_iff.mp (hJ₂N hb) a⁻¹).mp (inv_mem ha))
    · rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (hJ₁N ha) b).mp hb) (inv_mem hb)
  rw [hbot, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

end CFSG.ComponentClassification.RankTwoOddLie

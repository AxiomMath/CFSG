module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4IdxKa

public section

namespace CFSG.ComponentClassification.GSThmB.CF23Diag

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.CatFactsL4U4
open scoped commutatorElement

theorem eq_one_of_mem_center_of_odd {Y : Type*} [Group Y] [Finite Y]
    {c : Y ⧸ pPrimeCore 2 Y} (hc : c ∈ center (Y ⧸ pPrimeCore 2 Y)) (ho : Odd (orderOf c)) :
    c = 1 := by
  have hZ : zpowers c ≤ center (Y ⧸ pPrimeCore 2 Y) := zpowers_le.2 hc
  have : (zpowers c).Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hZ hn) g, mul_inv_cancel_right]
    exact hn⟩
  have hle : zpowers c ≤ pPrimeCore 2 (Y ⧸ pPrimeCore 2 Y) :=
    CatFactsL4U4.le_pPrimeCore_of_normal (by
      rw [Nat.card_zpowers]
      exact Nat.coprime_two_left.mpr ho)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2] at hle
  exact mem_bot.mp (hle (mem_zpowers c))

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

abbrev Vbar : Type := OddBar h.V

noncomputable abbrev psi : ↥h.V →* Vbar h := QuotientGroup.mk' (pPrimeCore 2 ↥h.V)

theorem a_sq : h.a * h.a = 1 := by rw [← pow_two, ← h.orderOf_a, pow_orderOf_eq_one]

theorem a_inv : h.a⁻¹ = h.a := inv_eq_of_mul_eq_one_right (a_sq h)

theorem psi_eq_one_iff (v : ↥h.V) : psi h v = 1 ↔ (v : H) ∈ oddCoreIn h.V := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (mem_map_iff_mem h.V.subtype_injective).symm

theorem conjA_mem_Ka {k : H} (hk : k ∈ h.K) : h.a⁻¹ * k * h.a ∈ conjugate h.K h.a :=
  conj_mem_conjugate hk h.a

theorem conjA_mem_K {k : H} (hk : k ∈ conjugate h.K h.a) : h.a⁻¹ * k * h.a ∈ h.K := by
  have h1 := mem_conjugate_iff.mp hk
  rw [a_inv] at h1 ⊢
  exact h1

variable (hKa : conjugate h.K h.a ≠ h.K)

include hKa in
theorem Ka_le_kernel : conjugate h.K h.a ≤ coreActionKernel h.K := by
  obtain ⟨hKaW, hKac⟩ := IdxKa.isPComponent_Ka h
  exact B5a.le_coreActionKernel_of_ne h.isPComponent_K.1 hKaW h.isPComponent_K.2 hKac (Ne.symm hKa)

theorem oddK_le : oddCoreIn h.K ≤ oddCoreIn h.V := by
  have := (IdxKa.sup_facts h).2.2.1
  rwa [h.layer_eq_K] at this

include hKa in
theorem psi_comm {k w : H} (hk : k ∈ h.K) (hw : w ∈ conjugate h.K h.a) :
    psi h ⟨k, h.K_le_V hk⟩ * psi h ⟨w, h.conjugate_K_le_V hw⟩ =
      psi h ⟨w, h.conjugate_K_le_V hw⟩ * psi h ⟨k, h.K_le_V hk⟩ := by
  set k' : ↥h.V := ⟨k, h.K_le_V hk⟩
  set w' : ↥h.V := ⟨w, h.conjugate_K_le_V hw⟩
  have hc : ((⁅k', w'⁆ : ↥h.V) : H) ∈ oddCoreIn h.V := by
    have h1 := oddK_le h (commutatorElement_mem_oddCoreIn hk (Ka_le_kernel h hKa hw))
    rw [commutatorElement_def] at h1 ⊢
    exact h1
  have h1 := (psi_eq_one_iff h _).2 hc
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1

theorem mul_mul_swap {Y : Type*} [Group Y] {p1 p2 q1 q2 : Y} (hc : p2 * q1 = q1 * p2) :
    p1 * p2 * (q1 * q2) = p1 * q1 * (p2 * q2) := by
  rw [mul_assoc, ← mul_assoc p2, hc]
  simp only [mul_assoc]

@[expose] noncomputable def delta : ↥h.K →* Vbar h where
  toFun k := psi h ⟨k, h.K_le_V k.2⟩ *
    psi h ⟨h.a⁻¹ * k * h.a, h.conjugate_K_le_V (conjA_mem_Ka h k.2)⟩
  map_one' := by
    have e1 : (⟨((1 : ↥h.K) : H), h.K_le_V (1 : ↥h.K).2⟩ : ↥h.V) = 1 := Subtype.ext rfl
    have e2 : (⟨h.a⁻¹ * ((1 : ↥h.K) : H) * h.a, h.conjugate_K_le_V (conjA_mem_Ka h (1 : ↥h.K).2)⟩ :
        ↥h.V) = 1 := Subtype.ext (by simp)
    rw [e1, e2, map_one, mul_one]
  map_mul' k₁ k₂ := by
    have e1 : (⟨((k₁ * k₂ : ↥h.K) : H), h.K_le_V (k₁ * k₂).2⟩ : ↥h.V) =
        ⟨k₁, h.K_le_V k₁.2⟩ * ⟨k₂, h.K_le_V k₂.2⟩ := Subtype.ext rfl
    have e2 : (⟨h.a⁻¹ * ((k₁ * k₂ : ↥h.K) : H) * h.a,
        h.conjugate_K_le_V (conjA_mem_Ka h (k₁ * k₂).2)⟩ : ↥h.V) =
        ⟨h.a⁻¹ * k₁ * h.a, h.conjugate_K_le_V (conjA_mem_Ka h k₁.2)⟩ *
          ⟨h.a⁻¹ * k₂ * h.a, h.conjugate_K_le_V (conjA_mem_Ka h k₂.2)⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    rw [e1, e2, map_mul, map_mul]
    exact mul_mul_swap (psi_comm h hKa k₂.2 (conjA_mem_Ka h k₁.2))

theorem delta_apply (k : ↥h.K) : delta h hKa k = psi h ⟨k, h.K_le_V k.2⟩ *
    psi h ⟨h.a⁻¹ * k * h.a, h.conjugate_K_le_V (conjA_mem_Ka h k.2)⟩ := rfl

theorem KaN : conjugate h.K h.a ≤ normalizer (h.K : Set H) :=
  le_sup_right.trans (IdxKa.sup_facts h).1

theorem mem_sup_of_V {v : H} (hv : v ∈ h.V) : v ∈ h.K ⊔ conjugate h.K h.a := by
  rw [h.layer_eq_K]
  exact hv

theorem mem_center_of_comm {c : Vbar h}
    (h1 : ∀ k (hk : k ∈ h.K), c * psi h ⟨k, h.K_le_V hk⟩ = psi h ⟨k, h.K_le_V hk⟩ * c)
    (h2 : ∀ w (hw : w ∈ conjugate h.K h.a),
      c * psi h ⟨w, h.conjugate_K_le_V hw⟩ = psi h ⟨w, h.conjugate_K_le_V hw⟩ * c) :
    c ∈ center (Vbar h) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥h.V) g
  obtain ⟨k, hk, w, hw, hkw⟩ := IdxKa.exists_mul_of_mem_sup (KaN h) (mem_sup_of_V h v.2)
  have e : v = ⟨k, h.K_le_V hk⟩ * ⟨w, h.conjugate_K_le_V hw⟩ := Subtype.ext hkw.symm
  rw [e, map_mul]
  rw [mul_assoc, ← h2 w hw, ← mul_assoc, ← h1 k hk, mul_assoc]

include hKa in
theorem exists_delta_mul_center (v : ↥h.V) (hv : h.a⁻¹ * (v : H) * h.a = v) :
    ∃ k : ↥h.K, ∃ c ∈ center (Vbar h), psi h v = delta h hKa k * c := by
  obtain ⟨k, hk, w, hw, hkw⟩ := IdxKa.exists_mul_of_mem_sup (KaN h) (mem_sup_of_V h v.2)
  have hka : h.a⁻¹ * k * h.a ∈ conjugate h.K h.a := conjA_mem_Ka h hk
  have hwa : h.a⁻¹ * w * h.a ∈ h.K := conjA_mem_K h hw
  set u := psi h ⟨k, h.K_le_V hk⟩ with hu
  set u' := psi h ⟨w, h.conjugate_K_le_V hw⟩ with hu'
  set s := psi h ⟨h.a⁻¹ * k * h.a, h.conjugate_K_le_V hka⟩ with hs
  set s' := psi h ⟨h.a⁻¹ * w * h.a, h.K_le_V hwa⟩ with hs'
  have e1 : s * s' = u * u' := by
    rw [hs, hs', hu, hu', ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show h.a⁻¹ * k * h.a * (h.a⁻¹ * w * h.a) = k * w
    rw [hkw]
    calc h.a⁻¹ * k * h.a * (h.a⁻¹ * w * h.a) = h.a⁻¹ * (k * w) * h.a := by group
      _ = h.a⁻¹ * (v : H) * h.a := by rw [hkw]
      _ = v := hv
  have hss : s' * s = s * s' := psi_comm h hKa hwa hka
  have hc1 : u⁻¹ * s' = u' * s⁻¹ := by
    have : s' = u * u' * s⁻¹ := by rw [← e1, ← hss, mul_inv_cancel_right]
    rw [this]
    group
  have hcK : u⁻¹ * s' = psi h ⟨k⁻¹ * (h.a⁻¹ * w * h.a), h.K_le_V (mul_mem (inv_mem hk) hwa)⟩ := by
    rw [hu, hs', ← map_inv, ← map_mul]
    rfl
  have hcKa : u⁻¹ * s' =
      psi h ⟨w * (h.a⁻¹ * k * h.a)⁻¹, h.conjugate_K_le_V (mul_mem hw (inv_mem hka))⟩ := by
    rw [hc1, hu', hs, ← map_inv, ← map_mul]
    rfl
  have hcZ : u⁻¹ * s' ∈ center (Vbar h) := by
    refine mem_center_of_comm h (fun k₀ hk₀ => ?_) (fun w₀ hw₀ => ?_)
    · rw [hcKa]
      exact (psi_comm h hKa hk₀ (mul_mem hw (inv_mem hka))).symm
    · rw [hcK]
      exact psi_comm h hKa (mul_mem (inv_mem hk) hwa) hw₀
  refine ⟨⟨k, hk⟩, u⁻¹ * s', hcZ, ?_⟩
  have hv' : v = ⟨k, h.K_le_V hk⟩ * ⟨w, h.conjugate_K_le_V hw⟩ := Subtype.ext hkw.symm
  have hu'c : u' = u⁻¹ * s' * s := by rw [hc1]; group
  rw [hv', map_mul, ← hu, ← hu', hu'c, delta_apply, ← hu, ← hs]
  rw [mul_assoc u s, mem_center_iff.mp hcZ s]

theorem a_mem_normalizer_V : h.a ∈ normalizer (h.V : Set H) :=
  OddQuot.le_normalizer_layerIn h.W h.a_mem_normalizer

theorem a_mem_normalizer_O : h.a ∈ normalizer ((oddCoreIn h.V : Subgroup H) : Set H) :=
  UnbalancedGS.normalizer_le_normalizer_map_of_characteristic _ _ (a_mem_normalizer_V h)

theorem conjA_mem_V {v : H} (hv : v ∈ h.V) : h.a⁻¹ * v * h.a ∈ h.V := by
  have := (mem_normalizer_iff.mp (inv_mem (a_mem_normalizer_V h)) v).mp hv
  rwa [inv_inv] at this

theorem conjA_mem_O {v : H} (hv : v ∈ oddCoreIn h.V) : h.a⁻¹ * v * h.a ∈ oddCoreIn h.V := by
  have := (mem_normalizer_iff.mp (inv_mem (a_mem_normalizer_O h)) v).mp hv
  rwa [inv_inv] at this

@[expose] def sigmaV : ↥h.V →* ↥h.V where
  toFun v := ⟨h.a⁻¹ * v * h.a, conjA_mem_V h v.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' v w := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_sigmaV (v : ↥h.V) : ((sigmaV h v : ↥h.V) : H) = h.a⁻¹ * v * h.a := rfl

theorem sigmaV_le : pPrimeCore 2 ↥h.V ≤ (pPrimeCore 2 ↥h.V).comap (sigmaV h) := by
  intro v hv
  rw [mem_comap]
  obtain ⟨w, hw, hwe⟩ := conjA_mem_O h (⟨v, hv, rfl⟩ : (v : H) ∈ oddCoreIn h.V)
  have e : w = sigmaV h v := Subtype.ext hwe
  rw [← e]
  exact hw

@[expose] noncomputable def sigmaBar : Vbar h →* Vbar h :=
  QuotientGroup.map _ _ (sigmaV h) (sigmaV_le h)

theorem sigmaBar_psi (v : ↥h.V) : sigmaBar h (psi h v) = psi h (sigmaV h v) := rfl

theorem sigmaBar_sigmaBar (y : Vbar h) : sigmaBar h (sigmaBar h y) = y := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥h.V) y
  rw [sigmaBar_psi, sigmaBar_psi]
  congr 1
  apply Subtype.ext
  rw [coe_sigmaV, coe_sigmaV, a_inv h]
  calc h.a * (h.a * (v : H) * h.a) * h.a = (h.a * h.a) * v * (h.a * h.a) := by group
    _ = v := by rw [a_sq h]; group

theorem sigmaBar_K {k : H} (hk : k ∈ h.K) : sigmaBar h (psi h ⟨k, h.K_le_V hk⟩) =
    psi h ⟨h.a⁻¹ * k * h.a, h.conjugate_K_le_V (conjA_mem_Ka h hk)⟩ := rfl

theorem psi_Ka_eq {w : H} (hw : w ∈ conjugate h.K h.a) : psi h ⟨w, h.conjugate_K_le_V hw⟩ =
    sigmaBar h (psi h ⟨h.a⁻¹ * w * h.a, h.K_le_V (conjA_mem_K h hw)⟩) := by
  rw [sigmaBar_psi]
  congr 1
  apply Subtype.ext
  rw [coe_sigmaV]
  show w = h.a⁻¹ * (h.a⁻¹ * w * h.a) * h.a
  rw [a_inv h]
  calc w = (h.a * h.a) * w * (h.a * h.a) := by rw [a_sq h]; group
    _ = h.a * (h.a * w * h.a) * h.a := by group

theorem delta_eq (k : ↥h.K) : delta h hKa k =
    psi h ⟨k, h.K_le_V k.2⟩ * sigmaBar h (psi h ⟨k, h.K_le_V k.2⟩) := rfl

noncomputable abbrev psiK : ↥h.K →* Vbar h := (psi h).comp (inclusion h.K_le_V)

theorem ker_psi_le {X : Subgroup H} (hX : X ≤ h.V) :
    ((psi h).comp (inclusion hX)).ker ≤ pPrimeCore 2 ↥X := by
  apply CatFactsL4U4.le_pPrimeCore_of_normal
  let f : ((psi h).comp (inclusion hX)).ker →* pPrimeCore 2 ↥h.V :=
    ((inclusion hX).comp ((psi h).comp (inclusion hX)).ker.subtype).codRestrict _ (by
      intro j
      have hj : psi h (inclusion hX (j : ↥X)) = 1 := j.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hj)
  have hf : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z : pPrimeCore 2 ↥h.V => ((z : ↥h.V) : H)) hxy
    exact Subtype.ext (Subtype.ext this)
  exact Nat.Coprime.coprime_dvd_right (card_dvd_of_injective f hf) pPrimeCore_coprime_card

theorem ker_psiK : (psiK h).ker = pPrimeCore 2 ↥h.K := by
  refine le_antisymm (ker_psi_le h h.K_le_V) (fun k hk => ?_)
  rw [MonoidHom.mem_ker]
  exact (psi_eq_one_iff h _).2 (oddK_le h ⟨k, hk, rfl⟩)

theorem commute_psiK_iff (k k₀ : ↥h.K) :
    Commute (psiK h k) (psiK h k₀) ↔ Commute (k : OddBar h.K) (k₀ : OddBar h.K) := by
  have e : ((⁅k, k₀⁆ : ↥h.K) : OddBar h.K) = ⁅(k : OddBar h.K), (k₀ : OddBar h.K)⁆ :=
    map_commutatorElement (QuotientGroup.mk' (pPrimeCore 2 ↥h.K)) k k₀
  rw [← commutatorElement_eq_one_iff_commute, ← commutatorElement_eq_one_iff_commute,
    ← map_commutatorElement, ← e, ← MonoidHom.mem_ker, ker_psiK, QuotientGroup.eq_one_iff]

include hKa in
theorem oddK_le_ker_delta : pPrimeCore 2 ↥h.K ≤ (delta h hKa).ker := by
  intro k hk
  have hk' : (k : H) ∈ oddCoreIn h.V := oddK_le h ⟨k, hk, rfl⟩
  rw [MonoidHom.mem_ker, delta_eq, (psi_eq_one_iff h _).2 hk', map_one, one_mul]

@[expose] noncomputable def deltaBar : OddBar h.K →* Vbar h :=
  QuotientGroup.lift (pPrimeCore 2 ↥h.K) (delta h hKa) (oddK_le_ker_delta h hKa)

theorem deltaBar_mk (k : ↥h.K) : deltaBar h hKa (k : OddBar h.K) = delta h hKa k := rfl

theorem range_deltaBar : (deltaBar h hKa).range = (delta h hKa).range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

include hKa in
theorem delta_mem_center {k : ↥h.K} (hk : (k : OddBar h.K) ∈ center (OddBar h.K)) :
    delta h hKa k ∈ center (Vbar h) := by
  have hu : ∀ k₀ (hk₀ : k₀ ∈ h.K), psi h ⟨k, h.K_le_V k.2⟩ * psi h ⟨k₀, h.K_le_V hk₀⟩ =
      psi h ⟨k₀, h.K_le_V hk₀⟩ * psi h ⟨k, h.K_le_V k.2⟩ := fun k₀ hk₀ =>
    ((commute_psiK_iff h k ⟨k₀, hk₀⟩).2 (mem_center_iff.mp hk _).symm).eq
  rw [delta_eq]
  refine mem_center_of_comm h (fun k₀ hk₀ => ?_) (fun w hw => ?_)
  · rw [sigmaBar_K h k.2, mul_assoc, ← psi_comm h hKa hk₀ (conjA_mem_Ka h k.2), ← mul_assoc,
      hu k₀ hk₀, mul_assoc]
  · have e : sigmaBar h (psi h ⟨k, h.K_le_V k.2⟩) * psi h ⟨w, h.conjugate_K_le_V hw⟩ =
        psi h ⟨w, h.conjugate_K_le_V hw⟩ * sigmaBar h (psi h ⟨k, h.K_le_V k.2⟩) := by
      rw [psi_Ka_eq h hw, ← map_mul (sigmaBar h), ← map_mul (sigmaBar h),
        hu _ (conjA_mem_K h hw)]
    rw [mul_assoc, e, ← mul_assoc, psi_comm h hKa k.2 hw, mul_assoc]

include hKa in
theorem ker_deltaBar_le : (deltaBar h hKa).ker ≤ center (OddBar h.K) := by
  intro x hx
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MonoidHom.mem_ker, deltaBar_mk, delta_eq] at hx
  have hu : psi h ⟨k, h.K_le_V k.2⟩ = (sigmaBar h (psi h ⟨k, h.K_le_V k.2⟩))⁻¹ :=
    eq_inv_of_mul_eq_one_left hx
  rw [mem_center_iff]
  intro y
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective y
  refine ((commute_psiK_iff h k₀ k).1 ?_).eq
  show Commute (psi h ⟨k₀, h.K_le_V k₀.2⟩) (psi h ⟨k, h.K_le_V k.2⟩)
  rw [hu, sigmaBar_K h k.2]
  exact Commute.inv_right (show Commute _ _ from psi_comm h hKa k₀.2 (conjA_mem_Ka h k.2))

end CFSG.ComponentClassification.GSThmB.CF23Diag

module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step7Y

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {L : Subgroup G} {p f : ℕ}

omit [Finite G] in
theorem conj_mem_Q {L : Subgroup G} (hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    {x : G} (hx : x ∈ centralizer ({z} : Set G)) {q : G}
    (hq : q ∈ centralizer ({z} : Set G) ⊓ coreActionKernel L) :
    x * q * x⁻¹ ∈ centralizer ({z} : Set G) ⊓ coreActionKernel L := by
  obtain ⟨hqz, hqK⟩ := mem_inf.mp hq
  refine mem_inf.mpr ⟨mul_mem (mul_mem hx hqz) (inv_mem hx), ?_⟩
  have hxN := hHN hx
  have hqN := (mem_coreActionKernel.mp hqK).1
  have h1 : barAction L ⟨q, hqN⟩ = 1 := MonoidHom.mem_ker.mp ((mem_ker_barAction L _).mpr hqK)
  have h2 : barAction L ⟨x * q * x⁻¹, mul_mem (mul_mem hxN hqN) (inv_mem hxN)⟩ = 1 := by
    have h3 : (⟨x * q * x⁻¹, mul_mem (mul_mem hxN hqN) (inv_mem hxN)⟩ :
        ↥(normalizer (L : Set G))) = ⟨x, hxN⟩ * ⟨q, hqN⟩ * (⟨x, hxN⟩)⁻¹ := rfl
    rw [h3, map_mul, map_mul, map_inv, h1, mul_one, mul_inv_cancel]
  exact (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h2)

theorem mk_mem_center_of_le_of_mem_coreActionKernel {X K : Subgroup G} (hXK : X ≤ K) {u : G}
    (huX : u ∈ X) (huK : u ∈ coreActionKernel K) :
    (QuotientGroup.mk (⟨u, huX⟩ : ↥X) : Bar X) ∈ center (Bar X) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨⟨x, hxX⟩, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  obtain ⟨o, ho, hoeq⟩ := (mem_coreActionKernel.mp huK).2 x (hXK hxX)
  have hoeq' : ((o : ↥K) : G) = x⁻¹ * u⁻¹ * x * u := hoeq
  have hoX : ((o : ↥K) : G) ∈ X := by
    rw [hoeq']
    exact mul_mem (mul_mem (mul_mem (inv_mem hxX) (inv_mem huX)) hxX) huX
  have hoO := mem_pPrimeCore_of_le hXK hoX ⟨o, ho, rfl⟩
  have h1 : (⟨x, hxX⟩ * ⟨u, huX⟩ : ↥X)⁻¹ * (⟨u, huX⟩ * ⟨x, hxX⟩) = (⟨_, hoX⟩ : ↥X)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hoeq']
    group
  rw [h1]
  exact inv_mem hoO

section Certified


theorem C3Config.card_inf_Q_le_two (hI : C3Inputs) (h : C3Config G z L p f) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) :
    Nat.card ↥(S ⊓ (centralizer {z} ⊓ coreActionKernel L)) ≤ 2 := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d⟩ := h.exists_step6 hI hS
  set Q := centralizer ({z} : Set G) ⊓ coreActionKernel L with hQ
  set A := S ⊓ Q with hA
  by_contra hlt
  push Not at hlt
  have hA2 : IsPGroup 2 A := hS.isPGroup.to_le inf_le_left
  have hA4 : 4 ≤ Nat.card A := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA2
    rw [hk] at hlt ⊢
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k <;> simp at hlt
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
  have hLn := h.normal hI
  have hHN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  have hQn : ∀ x ∈ centralizer ({z} : Set G), ∀ q ∈ Q, x * q * x⁻¹ ∈ Q :=
    fun x hx q hq => conj_mem_Q hHN hx hq
  have hSQ : IsSylowOf 2 A Q := hS.inf_of_le_normalizer inf_le_left (fun x hx =>
    mem_normalizer_iff.mpr fun q => ⟨fun hq => hQn x hx q hq, fun hq => by
      have h1 := hQn x⁻¹ (inv_mem hx) _ hq
      rwa [show x⁻¹ * (x * q * x⁻¹) * x⁻¹⁻¹ = q by group] at h1⟩)
  have hAY : A ≤ d.Y := d.inf_Q_le_Y hI h hS
  obtain ⟨R, hR, hAR⟩ := exists_isSylowOf_le hAY hA2
  have hz₁H : d.z₁ ∈ centralizer ({z} : Set G) := h.hL.1 d.hz₁L
  have hYQ : ∀ r ∈ d.Y, r ∈ Q ∨ r * d.z₁⁻¹ ∈ Q := by
    intro r hr
    have hrz : r ∈ centralizer ({z} : Set G) := (mem_inf.mp ((d.mem_Y).mp hr).1).1
    rcases d.mem_Q_of_mem_Y hI h hr with h1 | h1
    · exact .inl (mem_inf.mpr ⟨hrz, h1⟩)
    · exact .inr (mem_inf.mpr ⟨mul_mem hrz (inv_mem hz₁H), h1⟩)
  have hRQ : Nat.card R ≤ 2 * Nat.card ↥(R ⊓ Q) :=
    card_le_two_mul_inf (fun q hq => by
      have h1 := hQn d.z₁⁻¹ (inv_mem hz₁H) q hq
      rwa [inv_inv] at h1) (fun r hr => hYQ r (hR.le hr))
  have hRQA : Nat.card ↥(R ⊓ Q) ≤ Nat.card A :=
    IsSylowOf.card_le hSQ inf_le_right (hR.isPGroup.to_le inf_le_left)
  have hzc : z * d.z₁ = d.z₁ * z := (mem_centralizer_singleton_iff.mp hz₁H).symm
  set B := A.map (MulAut.conj d.b).toMonoidHom with hB
  have hBY : B ≤ d.Y := by
    rintro _ ⟨a, ha, rfl⟩
    exact d.conj_b_mem_Y hzc (hAY ha)
  obtain ⟨y, hyY, hy⟩ := IsSylowOf.exists_conj_le hR hBY (hA2.map _)
  set B' := B.map (MulAut.conj y⁻¹).toMonoidHom with hB'
  have hB'R : B' ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := hy x hx
    simpa [MulAut.conj_apply] using h1
  have hcB' : Nat.card B' = Nat.card A := by
    rw [hB', card_map_of_injective (MulAut.conj y⁻¹).injective, hB,
      card_map_of_injective (MulAut.conj d.b).injective]
  have hAB : 2 ≤ Nat.card ↥(A ⊓ B') := by
    have e1 := Subgroup.relIndex_mul_card (H := A) (K := R)
    rw [inf_eq_left.mpr hAR] at e1
    have e2 := Subgroup.relIndex_mul_card (H := B') (K := R)
    rw [inf_eq_left.mpr hB'R, hcB'] at e2
    have e3 := Subgroup.relIndex_mul_card (H := A ⊓ B') (K := R)
    rw [inf_eq_left.mpr (inf_le_left.trans hAR)] at e3
    have e4 := Subgroup.relIndex_inf_le (H := A) (K := B') (L := R)
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have hn1 : 1 ≤ Nat.card ↥(A ⊓ B') := Nat.card_pos
    set a := A.relIndex R
    set b := B'.relIndex R
    set c := (A ⊓ B').relIndex R
    have ha2 : a ≤ 2 := by nlinarith
    have hb2 : b ≤ 2 := by nlinarith
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0, zero_mul] at e1; omega
      · exact h0
    have hb1 : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · rw [h0, zero_mul] at e2; omega
      · exact h0
    by_contra hn
    push Not at hn
    have hn' : Nat.card ↥(A ⊓ B') = 1 := by omega
    rw [hn', mul_one] at e3
    interval_cases a <;> interval_cases b <;> omega
  have hAB2 : IsPGroup 2 ↥(A ⊓ B') := hA2.to_le inf_le_left
  have h2dvd : 2 ∣ Nat.card ↥(A ⊓ B') := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hAB2
    rw [hm] at hAB ⊢
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hAB; norm_num at hAB
    · exact dvd_pow_self 2 h0.ne'
  obtain ⟨⟨τ, hτAB⟩, hτ2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(A ⊓ B')) 2 h2dvd
  have hτ : orderOf τ = 2 := by rw [Subgroup.orderOf_mk] at hτ2; exact hτ2
  obtain ⟨hτA, hτB'⟩ := mem_inf.mp hτAB
  obtain ⟨hτS, hτQ⟩ := mem_inf.mp hτA
  obtain ⟨hτz, hτK⟩ := mem_inf.mp hτQ
  obtain ⟨_, ⟨a, haA, rfl⟩, hτa⟩ := hτB'
  have haK : a ∈ coreActionKernel L := (mem_inf.mp (mem_inf.mp haA).2).2
  set ρ := y⁻¹ * d.b with hρ
  have hτρ : τ = ρ * a * ρ⁻¹ := by
    rw [← hτa, hρ]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hyM : y ∈ d.M := ((d.mem_Y).mp hyY).1
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hyM).1
  have hyz₁ : y * d.z₁ = d.z₁ * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hyM).2
  have hy' : (z * d.z₁) * y = y * (z * d.z₁) := by
    rw [mul_assoc, ← hyz₁, ← mul_assoc, ← hyz, mul_assoc]
  have hρz : ρ * z * ρ⁻¹ = z * d.z₁ := by
    calc ρ * z * ρ⁻¹ = y⁻¹ * (d.b * z * d.b⁻¹) * y := by rw [hρ]; group
      _ = y⁻¹ * ((z * d.z₁) * y) := by rw [d.hbz, mul_assoc]
      _ = z * d.z₁ := by rw [hy', ← mul_assoc, inv_mul_cancel, one_mul]
  have h' : C3Config G (z * d.z₁) (L.map (MulAut.conj ρ).toMonoidHom) p f := hρz ▸ h.conj ρ
  have hτz₁ : τ * d.z₁ = d.z₁ * τ :=
    commute_of_mem_coreActionKernel hS.isPGroup hτS hτK d.hz₁S d.hz₁L
  have hτzz₁ : τ ∈ centralizer ({z * d.z₁} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have hτz' : τ * z = z * τ := mem_centralizer_singleton_iff.mp hτz
    rw [← mul_assoc, hτz', mul_assoc, hτz₁, mul_assoc]
  have hτK' : τ ∈ coreActionKernel (L.map (MulAut.conj ρ).toMonoidHom) :=
    hτρ ▸ conj_mem_coreActionKernel haK ρ
  obtain ⟨K, hKc, hXK, hzK, -⟩ := h.step1 hI hτ hτz hτK
  obtain ⟨K', hK'c, -, hzz₁K', hzz₁c⟩ := h'.step1 hI hτ hτzz₁ hτK'
  set X := centralizerResidual L τ with hX
  obtain ⟨hXc, ⟨eX⟩, hXmem⟩ := h.pumpdown_Q hτ hτK
  have hzz₁L : z * d.z₁ ∈ L := mul_mem h.hzL d.hz₁L
  have hzz₁o : orderOf (z * d.z₁) = 2 := h'.hz
  have hzz₁τ : z * d.z₁ ∈ centralizer ({τ} : Set G) := mem_centralizer_comm hτzz₁
  have hzz₁X : z * d.z₁ ∈ X :=
    hXmem _ hzz₁L hzz₁τ ⟨1, by rw [pow_one, ← hzz₁o, pow_orderOf_eq_one]⟩
  have hzz₁K : z * d.z₁ ∈ K := hXK hzz₁X
  have hzz₁Q : z * d.z₁ ∈ coreActionKernel K := by
    by_cases hKK : K' = K
    · subst hKK
      have hN : z * d.z₁ ∈ normalizer (K' : Set G) := le_normalizer hzz₁K'
      exact (mem_ker_barAction K' ⟨_, hN⟩).mp (MonoidHom.mem_ker.mpr
        (barAction_eq_one_of_mem_center (t := ⟨_, hzz₁K'⟩) hzz₁c hN))
    · exact le_coreActionKernel_of_ne hK'c hKc hKK hzz₁K'
  have hcen := mk_mem_center_of_le_of_mem_coreActionKernel hXK hzz₁X hzz₁Q
  have hXz : X ≤ centralizer ({z} : Set G) := centralizerResidual_le_left.trans h.hL.1
  have hzX : z ∈ X := h.mem_pumpdown_Q hτ hτK hτz
  have hZ2 : Nat.card ↥(center (Bar X)) = 2 := by
    have h1 : Nat.card ↥(center (Bar L)) = 2 := h.hcov.2.1
    rwa [← OuterAutomorphisms.center_map_equiv eX,
      Subgroup.card_map_of_injective eX.injective] at h1
  have heq := eq_of_mk_mem_center_of_le hXz hzX h.hz hZ2 hzz₁X hzz₁o hcen
  have h1 : d.z₁ = 1 := by
    calc d.z₁ = z⁻¹ * (z * d.z₁) := by group
      _ = 1 := by rw [heq, inv_mul_cancel]
  have h2 := d.hz₁
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

end Certified

end CFSG.ComponentClassification.HarrisLit.T1

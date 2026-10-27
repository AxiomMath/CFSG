module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Map
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.Toolbox
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Gen

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Lift

variable {T : Type} [Group T] [Finite T]

theorem s7l_mem_zpowers_two {G : Type*} [Group G] {z x : G} (hz : z * z = 1)
    (hx : x ∈ zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨n, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    beta_reduce
    rw [zpow_mul, zpow_two, hz, one_zpow]
  · right
    beta_reduce
    rw [zpow_add_one, zpow_mul, zpow_two, hz, one_zpow, one_mul]

omit [Finite T] in
theorem s7l_eq_one_of_sq {A : Subgroup T} (hA : Odd (Nat.card A)) {a : T} (ha : a ∈ A)
    (h : a * a = 1) : a = 1 := by
  have h1 : orderOf a ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A ha
  have h2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
  · exact orderOf_eq_one_iff.1 h3
  · exfalso
    have := Odd.of_dvd_nat hA h1
    rw [h3] at this
    exact absurd this (by decide)

omit [Finite T] in
theorem s7l_not_mem_ker (F : Subgroup T) [F.Normal] (A : Subgroup T) [A.Normal] (t : T)
    (htF : t ∉ F) (ht2 : t * t = 1) (hAodd : Odd (Nat.card A))
    (hker : (xhatMap F).ker ≤ F ⊔ A) (hFA : ∀ f ∈ F, ∀ a ∈ A, f * a = a * f)
    (hFdisj : ∀ f ∈ F, f ∈ A → f = 1) : xhatMap F t ≠ 1 := by
  intro h
  have hxs : t ∈ ((F ⊔ A : Subgroup T) : Set T) := hker (MonoidHom.mem_ker.2 h)
  rw [Subgroup.mul_normal F A] at hxs
  obtain ⟨f, hf, a, ha, rfl⟩ := hxs
  apply htF
  have h1 : (f * f) * (a * a) = 1 := by
    have : f * a * (f * a) = (f * f) * (a * a) := by
      calc f * a * (f * a) = f * (a * f) * a := by simp only [mul_assoc]
        _ = f * (f * a) * a := by rw [← hFA f hf a ha]
        _ = (f * f) * (a * a) := by simp only [mul_assoc]
    rw [← this]
    exact ht2
  have h2 : a * a = (f * f)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : a * a = 1 :=
    hFdisj _ (h2 ▸ inv_mem (mul_mem hf hf)) (mul_mem ha ha)
  rw [s7l_eq_one_of_sq hAodd ha h3]
  simpa using hf

omit [Finite T] in
theorem s7l_cent_ker (F : Subgroup T) [F.Normal] (A : Subgroup T) [A.Normal] (t ub : T)
    (hCF : ∀ f ∈ F, t * f * t⁻¹ = f → f ∈ zpowers ub) (hAodd : Odd (Nat.card A))
    (hker : (xhatMap F).ker ≤ F ⊔ A)
    (hFdisj : ∀ f ∈ F, f ∈ A → f = 1) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    {x : T} (hxt : x * t = t * x) (hx1 : xhatMap F x = 1) : x ∈ zpowers ub := by
  have hxs : x ∈ ((F ⊔ A : Subgroup T) : Set T) := hker (MonoidHom.mem_ker.2 hx1)
  rw [Subgroup.mul_normal F A] at hxs
  obtain ⟨f, hf, a, ha, rfl⟩ := hxs
  have hconj : t * (f * a) * t⁻¹ = f * a := by rw [← hxt, mul_inv_cancel_right]
  have hf' : t * f * t⁻¹ ∈ F := ‹F.Normal›.conj_mem f hf t
  have e0 : t * (f * a) * t⁻¹ = (t * f * t⁻¹) * (t * a * t⁻¹) := by group
  rw [e0, hinv a ha] at hconj
  have e2 : t * f * t⁻¹ = f * (a * a) := by
    calc t * f * t⁻¹ = (t * f * t⁻¹ * a⁻¹) * a := by group
      _ = f * a * a := by rw [hconj]
      _ = f * (a * a) := by rw [mul_assoc]
  have h3 : f⁻¹ * (t * f * t⁻¹) = a * a := by rw [e2]; group
  have h4 : a * a = 1 := by
    apply hFdisj _ _ (mul_mem ha ha)
    rw [← h3]
    exact mul_mem (inv_mem hf) hf'
  have h5 : a = 1 := s7l_eq_one_of_sq hAodd ha h4
  subst h5
  rw [h4] at h3
  have h6 : f = t * f * t⁻¹ := inv_mul_eq_one.1 h3
  simpa using hCF f hf h6.symm

theorem exists_mulEquiv_cent_xhat (F : Subgroup T) [F.Normal]
    (A : Subgroup T) [A.Normal] (t ub : T) (B V : Subgroup T)
    (e : ↥B ≃* MulAut (alternatingGroup (Fin 6)))
    (ht2 : t * t = 1) (_hub2 : ub * ub = 1) (_hubc : ∀ g : T, g * ub = ub * g) (hubF : ub ∈ F)
    (_hub1 : ub ≠ 1) (htF : t ∉ F)
    (hCF : ∀ f ∈ F, t * f * t⁻¹ = f → f ∈ zpowers ub)
    (hfus : ∀ g : T, g * t * g⁻¹ * t⁻¹ ∈ F → ∃ w : T, w * t = t * w ∧ g * w⁻¹ ∈ F)
    (hAodd : Odd (Nat.card A)) (hker : (xhatMap F).ker ≤ F ⊔ A)
    (hFA : ∀ f ∈ F, ∀ a ∈ A, f * a = a * f) (hFdisj : ∀ f ∈ F, f ∈ A → f = 1)
    (_hF2 : IsPGroup 2 F) (hinv : ∀ a ∈ A, t * a * t⁻¹ = a⁻¹)
    (hV : V = zpowers t ⊔ zpowers ub) (hBt : ∀ b ∈ B, b * t = t * b)
    (hW : ∀ w : T, w * t = t * w → ∃ v ∈ V, ∃ b ∈ B, w = v * b)
    (hVB : ∀ x ∈ V, x ∈ B → x = 1) :
    orderOf (xhatMap F t) = 2 ∧
      Nonempty (↥(centralizer ({xhatMap F t} : Set ((T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F)))) ≃*
        Multiplicative (ZMod 2) × MulAut (alternatingGroup (Fin 6))) := by
  set κ : T →* (T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F) := xhatMap F with hκ
  have hz2 : κ t * κ t = 1 := by rw [← map_mul, ht2, map_one]
  have hne : κ t ≠ 1 := s7l_not_mem_ker F A t htF ht2 hAodd hker hFA hFdisj
  have hκub : κ ub = 1 := MonoidHom.mem_ker.1 (le_ker_xhatMap F hubF)
  have hubV : ub ∈ V := by
    rw [hV]; exact mem_sup_right (mem_zpowers ub)
  have hzub_le : zpowers ub ≤ F := zpowers_le.2 hubF
  refine ⟨?_, ?_⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact hz2) hne
  have key3 : ∀ x : T, x * t = t * x → κ x = 1 → x ∈ zpowers ub := fun x hxt hx1 =>
    s7l_cent_ker F A t ub hCF hAodd hker hFdisj hinv hxt hx1
  have hlift : ∀ g ∈ centralizer ({κ t} : Set ((T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F))),
      ∃ w : T, w * t = t * w ∧ κ w = g := by
    intro g hg
    have hmk2 : (QuotientGroup.mk t : T ⧸ F) * QuotientGroup.mk t = 1 := by
      rw [← QuotientGroup.mk_mul, ht2, QuotientGroup.mk_one]
    have h2 := map_centralizer_eq_of_odd (G := T ⧸ F) (Open.fusionOddCore (T ⧸ F))
      (natCard_fusionOddCore_odd' _) hmk2
    have hg' : g ∈ (centralizer ({(QuotientGroup.mk t : T ⧸ F)} : Set (T ⧸ F))).map
        (QuotientGroup.mk' (Open.fusionOddCore (T ⧸ F))) := by
      rw [h2]; exact hg
    obtain ⟨c, hc, hcg⟩ := hg'
    obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective c
    have hc' : (QuotientGroup.mk g0 : T ⧸ F) * QuotientGroup.mk t =
        QuotientGroup.mk t * QuotientGroup.mk g0 := mem_centralizer_singleton_iff.1 hc
    have hF1 : g0 * t * g0⁻¹ * t⁻¹ ∈ F := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hc']
      group
    obtain ⟨w, hw, hgw⟩ := hfus g0 hF1
    refine ⟨w, hw, ?_⟩
    have h1 : κ (g0 * w⁻¹) = 1 := MonoidHom.mem_ker.1 (le_ker_xhatMap F hgw)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [← h1]
    exact hcg
  have hVk : ∀ v ∈ V, κ v = 1 ∨ κ v = κ t := by
    have hle : V ≤ (zpowers (κ t)).comap κ := by
      rw [hV]
      refine sup_le ?_ ?_
      · rw [zpowers_le]
        exact Subgroup.mem_comap.2 (mem_zpowers _)
      · rw [zpowers_le]
        exact Subgroup.mem_comap.2 (by rw [hκub]; exact one_mem _)
    intro v hv
    exact s7l_mem_zpowers_two hz2 (Subgroup.mem_comap.1 (hle hv))
  have hBinj : ∀ b ∈ B, κ b = 1 → b = 1 := fun b hb h1 =>
    hVB b (by
      have := key3 b (hBt b hb) h1
      rw [hV]
      exact mem_sup_right this) hb
  set Γ : Subgroup ((T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F)) :=
    centralizer ({κ t} : Set ((T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F))) with hΓ
  have hzΓ : κ t ∈ Γ := mem_centralizer_singleton_iff.2 rfl
  let z : ↥Γ := ⟨κ t, hzΓ⟩
  have hz : ∀ g : ↥Γ, g * z = z * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.1 g.2)
  have hzz : z * z = 1 := Subtype.ext hz2
  let φ : ↥B →* (T ⧸ F) ⧸ Open.fusionOddCore (T ⧸ F) := κ.comp B.subtype
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    exact Subtype.ext (hBinj b b.2 hb)
  have hφΓ : φ.range ≤ Γ := by
    rintro _ ⟨b, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    show κ b * κ t = κ t * κ b
    rw [← map_mul, ← map_mul, hBt b b.2]
  let Bs : Subgroup ↥Γ := φ.range.subgroupOf Γ
  have hzB : z ∉ Bs := by
    rintro ⟨b, hb⟩
    have hb' : κ b = κ t := hb
    have hx1 : κ ((t⁻¹ * b : T)) = 1 := by
      rw [map_mul, map_inv, ← hb', inv_mul_cancel]
    have hxt : (t⁻¹ * b : T) * t = t * (t⁻¹ * b) := by
      rw [mul_assoc, hBt b b.2, inv_mul_cancel_left, mul_inv_cancel_left]
    obtain ⟨j, hj0⟩ := key3 _ hxt hx1
    have hj : ub ^ j = t⁻¹ * b := hj0
    have hbj : (b : T) = t * ub ^ j := by
      rw [hj]; group
    have hbV : (b : T) ∈ V := by
      rw [hbj, hV]
      exact mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right (zpow_mem (mem_zpowers ub) j))
    have h1 : (b : T) = 1 := hVB _ hbV b.2
    rw [h1] at hbj
    apply htF
    have : t = (ub ^ j)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hbj.symm
    rw [this]
    exact inv_mem (hzub_le (zpow_mem (mem_zpowers ub) j))
  have hcov : ∀ g : ↥Γ, g ∈ Bs ∨ z * g ∈ Bs := by
    intro g
    obtain ⟨w, hw, hwg⟩ := hlift g.1 g.2
    obtain ⟨v, hv, b, hb, rfl⟩ := hW w hw
    rw [map_mul] at hwg
    rcases hVk v hv with h1 | h1
    · left
      refine ⟨⟨b, hb⟩, ?_⟩
      show κ b = g.1
      rw [h1, one_mul] at hwg
      exact hwg
    · right
      refine ⟨⟨b, hb⟩, ?_⟩
      show κ b = κ t * g.1
      rw [h1] at hwg
      rw [← hwg, ← mul_assoc, hz2, one_mul]
  have eB : ↥Bs ≃* MulAut (alternatingGroup (Fin 6)) :=
    ((Subgroup.subgroupOfEquivOfLe hφΓ).trans (MonoidHom.ofInjective hφinj).symm).trans e
  exact exists_mulEquiv_prod hz hzz Bs hzB hcov eB

end Lift

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

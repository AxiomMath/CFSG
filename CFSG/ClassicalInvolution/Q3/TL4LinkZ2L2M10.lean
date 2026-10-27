module

public import CFSG.ClassicalInvolution.Q3.TL4MF165APair
public import CFSG.ClassicalInvolution.Q3.TL4MF163Psl
public import CFSG.ClassicalInvolution.Q3.TL4E3C269G9B
public import CFSG.ClassicalInvolution.Q3.TL4MF164Dat
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2M10

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.A6Facts CFSG.ClassicalInvolution.Asc77

theorem exists_orderOf_eq_two_pow {b c : P10} (hb : b ∈ A6Models.psl29) (hb2 : b * b = 1)
    (hb1 : b ≠ 1) (hc : c ∈ A6Models.autA6) (hcb : c * b = b * c) :
    ∃ k : ℕ, orderOf c = 2 ^ k := by
  obtain ⟨h, hh, hhb⟩ := E3C269G9.psl29_conj_zb hb hb2 hb1
  have hhA : h ∈ A6Models.autA6 := psl29_le_autA6 hh
  have hc' : h * c * h⁻¹ ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.mul_mem hhA hc) (A6Models.autA6.inv_mem hhA)
  have hcz : h * c * h⁻¹ * zb = zb * (h * c * h⁻¹) := by
    rw [← hhb]
    calc h * c * h⁻¹ * (h * b * h⁻¹) = h * (c * b) * h⁻¹ := by group
      _ = h * (b * c) * h⁻¹ := by rw [hcb]
      _ = h * b * h⁻¹ * (h * c * h⁻¹) := by group
  have hP := centralizer_le_P0_of_central zb_mem_P0 zb_ne_one zb_central hc' hcz
  have hdvd : orderOf (h * c * h⁻¹) ∣ 2 ^ 5 := by
    have h1 := Subgroup.orderOf_dvd_natCard P0 hP
    rw [card_P0] at h1
    exact h1
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  refine ⟨k, ?_⟩
  have e := MulEquiv.orderOf_eq (MulAut.conj h) c
  rw [MulAut.conj_apply] at e
  rw [← e, hk]

theorem oddCore_eq_bot_of_isPGroup {H : Type*} [Group H] [Finite H] (hH : IsPGroup 2 H) :
    classicalInvolutionOddCore H = ⊥ := by
  have hodd : Odd (Nat.card ↥(classicalInvolutionOddCore H)) :=
    CFSG.ComponentClassification.OddCore.odd_card H
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 (hH.to_subgroup (classicalInvolutionOddCore H))
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra h
    exact Nat.not_even_iff_odd.2 hodd (Nat.even_pow.2 ⟨even_two, h⟩)
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

private theorem alphaOf_eq_bot_of_oddCore {G : Type} [Group G] {A : Subgroup G} {a₀ : G}
    (ha₀ : a₀ ∈ A) (ha₀1 : a₀ ≠ 1)
    (h : ∀ a ∈ A, a ≠ 1 → oddCoreOf (Subgroup.centralizer ({a} : Set G)) = ⊥) :
    alphaOf A = ⊥ := by
  unfold alphaOf
  refine sup_eq_bot_iff.mpr ⟨?_, ?_⟩
  · refine le_bot_iff.mp (iSup₂_le fun a ha => iSup_le fun ha1 => ?_)
    rw [h a ha ha1]
    simp
  · exact le_bot_iff.mp ((iInf₂_le a₀ ha₀).trans ((iInf_le _ ha₀1).trans (h a₀ ha₀ ha₀1).le))

private theorem mem_closure_pair_cases {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b = b * a) {p : G} (hp : p ∈ Subgroup.closure {a, b}) :
    p = 1 ∨ p = a ∨ p = b ∨ p = a * b := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_left hb
  have hSa : ∀ y : G, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (a * y = 1 ∨ a * y = a ∨ a * y = b ∨ a * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inl (mul_one a))
    · exact Or.inl ha
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inr (Or.inl (by rw [← mul_assoc, ha, one_mul])))
  have hSb : ∀ y : G, (y = 1 ∨ y = a ∨ y = b ∨ y = a * b) →
      (b * y = 1 ∨ b * y = a ∨ b * y = b ∨ b * y = a * b) := by
    rintro y (rfl | rfl | rfl | rfl)
    · exact Or.inr (Or.inr (Or.inl (mul_one b)))
    · exact Or.inr (Or.inr (Or.inr hab.symm))
    · exact Or.inl hb
    · exact Or.inr (Or.inl (by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_one]))
  induction hp using Subgroup.closure_induction_left with
  | one => exact Or.inl rfl
  | mul_left x hx y _ hy =>
    rcases hx with rfl | rfl
    · exact hSa y hy
    · exact hSb y hy
  | inv_mul_cancel x hx y _ hy =>
    rcases hx with rfl | rfl
    · rw [hainv]
      exact hSa y hy
    · rw [hbinv]
      exact hSb y hy

theorem autAlphaPairs_of_equiv {K : Type} [Group K] (φ : K ≃* ↥A6Models.psl29) :
    AutAlphaPairs K := by
  intro 𝒳 hinn a a' ha2 ha1 hne hcomm hconj
  have : Finite K := Finite.of_equiv _ φ.symm.toEquiv
  have : Finite (MulAut K) :=
    Finite.of_injective (fun γ : MulAut K => (γ : K → K)) fun _ _ e => MulEquiv.ext (congrFun e)
  set Θ := Unc25K1.A6Model.thetaEquiv φ with hΘ
  have hΘc : ∀ b : K, ((Θ (MulAut.conj b) : ↥A6Models.autA6) : P10) =
      ((φ b : ↥A6Models.psl29) : P10) := fun b => congrArg Subtype.val
    (Unc25K1.A6Model.thetaEquiv_eq φ (MulAut.conj b) ⟨φ b, psl29_le_autA6 (φ b).2⟩ fun k => by
      rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
      rfl)
  have hodd : ∀ (w : ↥𝒳) (b : K), b * b = 1 → b ≠ 1 → (w : MulAut K) = MulAut.conj b →
      oddCoreOf (Subgroup.centralizer ({w} : Set ↥𝒳)) = ⊥ := by
    intro w b hb2 hb1 hwb
    have hφb2 : ((φ b : ↥A6Models.psl29) : P10) * (φ b : P10) = 1 := by
      rw [← Subgroup.coe_mul, ← map_mul, hb2, map_one, Subgroup.coe_one]
    have hφb1 : ((φ b : ↥A6Models.psl29) : P10) ≠ 1 := fun h =>
      hb1 (φ.injective (Subtype.ext (by rw [h, map_one, Subgroup.coe_one])))
    have hp : IsPGroup 2 ↥(Subgroup.centralizer ({w} : Set ↥𝒳)) := by
      intro γ
      have hγ : (γ : ↥𝒳) * w = w * γ := Subgroup.mem_centralizer_singleton_iff.mp γ.2
      have hγ' : ((Θ ((γ : ↥𝒳) : MulAut K) : ↥A6Models.autA6) : P10) * (φ b : P10) =
          (φ b : P10) * (Θ ((γ : ↥𝒳) : MulAut K) : P10) := by
        rw [← hΘc, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, ← hwb]
        exact congrArg (fun m : ↥𝒳 => ((Θ (m : MulAut K) : ↥A6Models.autA6) : P10)) hγ
      obtain ⟨k, hk⟩ :=
        exists_orderOf_eq_two_pow (φ b).2 hφb2 hφb1 (Θ ((γ : ↥𝒳) : MulAut K)).2 hγ'
      refine ⟨k, ?_⟩
      have e1 : orderOf ((Θ ((γ : ↥𝒳) : MulAut K) : ↥A6Models.autA6) : P10) = orderOf γ := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, Subgroup.orderOf_coe]
      rw [← hk, e1]
      exact pow_orderOf_eq_one γ
    unfold oddCoreOf
    rw [oddCore_eq_bot_of_isPGroup hp, Subgroup.map_bot]
  have ha'2 : a' * a' = 1 := by
    obtain ⟨g, rfl⟩ := hconj
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have ha'1 : a' ≠ 1 := by
    obtain ⟨g, rfl⟩ := hconj
    intro h
    apply ha1
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hx2 : (⟨MulAut.conj a, hinn a⟩ : ↥𝒳) * ⟨MulAut.conj a, hinn a⟩ = 1 := Subtype.ext (by
    show MulAut.conj a * MulAut.conj a = 1
    rw [← map_mul, ha2, map_one])
  have hy2 : (⟨MulAut.conj a', hinn a'⟩ : ↥𝒳) * ⟨MulAut.conj a', hinn a'⟩ = 1 := Subtype.ext (by
    show MulAut.conj a' * MulAut.conj a' = 1
    rw [← map_mul, ha'2, map_one])
  have hxy : (⟨MulAut.conj a, hinn a⟩ : ↥𝒳) * ⟨MulAut.conj a', hinn a'⟩ =
      ⟨MulAut.conj a', hinn a'⟩ * ⟨MulAut.conj a, hinn a⟩ := Subtype.ext (by
    show MulAut.conj a * MulAut.conj a' = MulAut.conj a' * MulAut.conj a
    rw [← map_mul, ← map_mul, hcomm])
  have hx1 : (⟨MulAut.conj a, hinn a⟩ : ↥𝒳) ≠ 1 := by
    intro h
    have h1 : MulAut.conj a = 1 := congrArg Subtype.val h
    apply ha1
    have hc : ∀ k : K, a * k = k * a := fun k => by
      have h2 := congrArg (fun γ : MulAut K => γ k) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc a * k = a * k * a⁻¹ * a := by group
        _ = k * a := by rw [h2]
    have h3 : ((φ a : ↥A6Models.psl29) : P10) = 1 :=
      centralizer_psl29 (psl29_le_autA6 (φ a).2) fun z hz => by
        obtain ⟨k, hk⟩ := φ.surjective ⟨z, hz⟩
        have h4 := congrArg (fun m : K => ((φ m : ↥A6Models.psl29) : P10)) (hc k)
        simp only [map_mul, Subgroup.coe_mul, hk] at h4
        exact h4
    exact φ.injective (Subtype.ext (by rw [h3, map_one, Subgroup.coe_one]))
  refine alphaOf_eq_bot_of_oddCore (Subgroup.subset_closure (Set.mem_insert _ _)) hx1 ?_
  intro w hw hw1
  rcases mem_closure_pair_cases hx2 hy2 hxy hw with rfl | rfl | rfl | rfl
  · exact absurd rfl hw1
  · exact hodd _ a ha2 ha1 rfl
  · exact hodd _ a' ha'2 ha'1 rfl
  · refine hodd _ (a * a') ?_ ?_ ?_
    · calc a * a' * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [hcomm]
        _ = a * a * (a' * a') := by group
        _ = 1 := by rw [ha2, ha'2, one_mul]
    · intro h
      apply hne
      calc a' = a⁻¹ * (a * a') := by group
        _ = a⁻¹ := by rw [h, mul_one]
        _ = a := inv_eq_of_mul_eq_one_left ha2
    · show MulAut.conj a * MulAut.conj a' = MulAut.conj (a * a')
      rw [map_mul]

theorem exists_ne_comm_of_equiv {K : Type} [Group K] (φ : K ≃* ↥A6Models.psl29) :
    ∃ a b : K, a * b ≠ b * a := by
  refine ⟨φ.symm ⟨A6Models.tAdd, Out21.A6.tAdd_mem_psl29⟩,
    φ.symm ⟨A6Models.tInv, Out21.A6.tInv_mem_psl29⟩, fun h => ?_⟩
  have h1 := congrArg (fun k => ((φ k : ↥A6Models.psl29) : P10)) h
  simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
  exact absurd h1 (by decide)

theorem exists_conj_of_equiv {K : Type} [Group K] (φ : K ≃* ↥A6Models.psl29) {a a' : K}
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha2' : a' * a' = 1) (ha1' : a' ≠ 1) :
    ∃ g : K, g * a * g⁻¹ = a' := by
  have key : ∀ b : K, b * b = 1 → b ≠ 1 →
      ∃ h ∈ A6Models.psl29, h * ((φ b : ↥A6Models.psl29) : P10) * h⁻¹ = zb := by
    intro b hb2 hb1
    refine E3C269G9.psl29_conj_zb (φ b).2 ?_ ?_
    · rw [← Subgroup.coe_mul, ← map_mul, hb2, map_one, Subgroup.coe_one]
    · intro h
      exact hb1 (φ.injective (Subtype.ext (by rw [h, map_one, Subgroup.coe_one])))
  obtain ⟨h₁, hh₁, e₁⟩ := key a ha2 ha1
  obtain ⟨h₂, hh₂, e₂⟩ := key a' ha2' ha1'
  refine ⟨φ.symm ⟨h₂⁻¹ * h₁, A6Models.psl29.mul_mem (A6Models.psl29.inv_mem hh₂) hh₁⟩, ?_⟩
  apply φ.injective
  apply Subtype.ext
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  show h₂⁻¹ * h₁ * ((φ a : ↥A6Models.psl29) : P10) * (h₂⁻¹ * h₁)⁻¹ = (φ a' : P10)
  calc h₂⁻¹ * h₁ * ((φ a : ↥A6Models.psl29) : P10) * (h₂⁻¹ * h₁)⁻¹ =
        h₂⁻¹ * (h₁ * (φ a : P10) * h₁⁻¹) * h₂ := by group
    _ = h₂⁻¹ * (h₂ * (φ a' : P10) * h₂⁻¹) * h₂ := by rw [e₁, e₂]
    _ = (φ a' : P10) := by group

theorem exists_conj_m10 {T S : ↥A6Models.m10} (hT2 : T * T = 1) (hT1 : T ≠ 1)
    (hS2 : S * S = 1) (hS1 : S ≠ 1) : ∃ g : ↥A6Models.m10, S = g * T * g⁻¹ := by
  have key : ∀ b : ↥A6Models.m10, b * b = 1 → b ≠ 1 →
      ∃ h ∈ A6Models.psl29, h * (b : P10) * h⁻¹ = zb := by
    intro b hb2 hb1
    have hb2' : (b : P10) * b = 1 := congrArg Subtype.val hb2
    exact E3C269G9.psl29_conj_zb (Out21.A6.m10_involution_mem_psl29 b.2 hb2') hb2'
      fun h => hb1 (Subtype.ext h)
  obtain ⟨h₁, hh₁, e₁⟩ := key T hT2 hT1
  obtain ⟨h₂, hh₂, e₂⟩ := key S hS2 hS1
  refine ⟨⟨h₂⁻¹ * h₁, Out21.A6.psl29_le_m10
    (A6Models.psl29.mul_mem (A6Models.psl29.inv_mem hh₂) hh₁)⟩, Subtype.ext ?_⟩
  show (S : P10) = h₂⁻¹ * h₁ * (T : P10) * (h₂⁻¹ * h₁)⁻¹
  calc (S : P10) = h₂⁻¹ * (h₂ * (S : P10) * h₂⁻¹) * h₂ := by group
    _ = h₂⁻¹ * (h₁ * (T : P10) * h₁⁻¹) * h₂ := by rw [e₁, e₂]
    _ = h₂⁻¹ * h₁ * (T : P10) * (h₂⁻¹ * h₁)⁻¹ := by group

section Theta

variable {X : Type} [Group X] {N : Subgroup X} [N.Normal] (φ : ↥N ≃* ↥A6Models.psl29)

noncomputable def theta : X →* ↥A6Models.autA6 :=
  (Unc25K1.A6Model.thetaEquiv φ).toMonoidHom.comp MulAut.conjNormal

theorem theta_coe (n : ↥N) :
    ((theta φ (n : X) : ↥A6Models.autA6) : P10) = ((φ n : ↥A6Models.psl29) : P10) := by
  have h := Unc25K1.A6Model.thetaEquiv_eq φ (MulAut.conjNormal (n : X))
    ⟨φ n, psl29_le_autA6 (φ n).2⟩ (fun k => by
      have hk : (MulAut.conjNormal (n : X)) k = n * k * n⁻¹ :=
        Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
      rw [hk, map_mul, map_mul, map_inv]
      rfl)
  exact congrArg Subtype.val h

theorem theta_injective (hC : Subgroup.centralizer (N : Set X) ≤ N) :
    Function.Injective (theta φ) := by
  have hinj : Function.Injective (MulAut.conjNormal : X →* MulAut N) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hc : ∀ m ∈ N, x * m = m * x := by
      intro m hm
      have h := congrArg (fun f : MulAut N => ((f ⟨m, hm⟩ : N) : X)) hx
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc x * m = x * m * x⁻¹ * x := by group
        _ = m * x := by rw [h]
    have hxN : x ∈ N := hC (Subgroup.mem_centralizer_iff.mpr fun m hm => (hc m hm).symm)
    have h1 : ((φ ⟨x, hxN⟩ : A6Models.psl29) : P10) = 1 := by
      refine centralizer_psl29 (psl29_le_autA6 (φ _).2) fun y hy => ?_
      obtain ⟨m, hm⟩ := φ.surjective ⟨y, hy⟩
      have h2 : (⟨x, hxN⟩ : N) * m = m * ⟨x, hxN⟩ := Subtype.ext (hc m m.2)
      have h3 := congrArg (fun n : N => ((φ n : A6Models.psl29) : P10)) h2
      simp only [map_mul, Subgroup.coe_mul, hm] at h3
      exact h3
    have h4 : φ ⟨x, hxN⟩ = 1 := Subtype.ext h1
    rw [map_eq_one_iff _ φ.injective] at h4
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h4)
  exact (Unc25K1.A6Model.thetaEquiv φ).injective.comp hinj

theorem map_range_theta (hC : Subgroup.centralizer (N : Set X) ≤ N) (hidx : N.index ≤ 2)
    {ι : QuaternionGroup 2 →* X} (hι : Function.Injective ι)
    (htN : ι (QuaternionGroup.a 2) ∈ N) :
    (theta φ).range.map A6Models.autA6.subtype = A6Models.m10 := by
  have hθ := theta_injective φ hC
  have hBA : (theta φ).range.map A6Models.autA6.subtype ≤ A6Models.autA6 := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hmem : ∀ x : X,
      ((theta φ x : A6Models.autA6) : P10) ∈ (theta φ).range.map A6Models.autA6.subtype :=
    fun x => ⟨theta φ x, ⟨x, rfl⟩, rfl⟩
  have hpsl : A6Models.psl29 ≤ (theta φ).range.map A6Models.autA6.subtype := by
    intro y hy
    have h := hmem (φ.symm ⟨y, hy⟩ : X)
    rw [theta_coe, MulEquiv.apply_symm_apply] at h
    exact h
  have hcardB : Nat.card ((theta φ).range.map A6Models.autA6.subtype) ≤ 720 := by
    rw [Subgroup.card_map_of_injective Subtype.val_injective,
      ← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, ← Subgroup.card_mul_index N,
      Nat.card_congr φ.toEquiv, card_psl29]
    omega
  have key : ∀ u v w : QuaternionGroup 2, u * v = w →
      ((theta φ (ι u) : A6Models.autA6) : P10) * ((theta φ (ι v) : A6Models.autA6) : P10) =
        ((theta φ (ι w) : A6Models.autA6) : P10) := by
    intro u v w h
    rw [← h, map_mul, map_mul, Subgroup.coe_mul]
  have hz : ((theta φ (ι (QuaternionGroup.a 2)) : A6Models.autA6) : P10) ∈ A6Models.psl29 := by
    show ((theta φ ((⟨_, htN⟩ : N) : X) : A6Models.autA6) : P10) ∈ A6Models.psl29
    rw [theta_coe]
    exact (φ _).2
  have hz1 : ((theta φ (ι (QuaternionGroup.a 2)) : A6Models.autA6) : P10) ≠ 1 := by
    intro h
    have h1 : theta φ (ι (QuaternionGroup.a 2)) = theta φ (ι 1) := by
      rw [map_one, map_one]
      exact Subtype.ext h
    exact absurd (hι (hθ h1)) (by decide)
  have hz2 := key _ _ _ (show QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2)
    by decide)
  rw [map_one, map_one, Subgroup.coe_one] at hz2
  exact E3C269G9.eq_m10_of_q8 hBA hpsl hcardB
    (hmem (ι (QuaternionGroup.a 1))) (hmem (ι (QuaternionGroup.xa 0))) hz hz2 hz1
    (key _ _ _ (show QuaternionGroup.a 1 * QuaternionGroup.a 1 = QuaternionGroup.a (n := 2) 2
      by decide))
    (key _ _ _ (show QuaternionGroup.xa 0 * QuaternionGroup.xa 0 = QuaternionGroup.a (n := 2) 2
      by decide))
    (by rw [key _ _ _ (show QuaternionGroup.a 1 * QuaternionGroup.xa 0 = QuaternionGroup.xa
        (n := 2) 3 by decide), key _ _ _ (show QuaternionGroup.xa 3 * QuaternionGroup.a 1 =
          QuaternionGroup.xa (n := 2) 0 by decide)])

theorem theta_mem_m10 (hC : Subgroup.centralizer (N : Set X) ≤ N) (hidx : N.index ≤ 2)
    {ι : QuaternionGroup 2 →* X} (hι : Function.Injective ι)
    (htN : ι (QuaternionGroup.a 2) ∈ N) (x : X) :
    ((theta φ x : ↥A6Models.autA6) : P10) ∈ A6Models.m10 := by
  rw [← map_range_theta φ hC hidx hι htN]
  exact ⟨theta φ x, ⟨x, rfl⟩, rfl⟩

include φ in
theorem mem_of_mul_self_eq_one (hC : Subgroup.centralizer (N : Set X) ≤ N) (hidx : N.index ≤ 2)
    {ι : QuaternionGroup 2 →* X} (hι : Function.Injective ι)
    (htN : ι (QuaternionGroup.a 2) ∈ N) {a : X} (ha : a * a = 1) : a ∈ N := by
  have hm := theta_mem_m10 φ hC hidx hι htN a
  have h2 : ((theta φ a : ↥A6Models.autA6) : P10) * (theta φ a : P10) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, ha, map_one, Subgroup.coe_one]
  obtain ⟨n, hn⟩ := φ.surjective ⟨_, Out21.A6.m10_involution_mem_psl29 hm h2⟩
  have h3 : theta φ (n : X) = theta φ a := Subtype.ext (by rw [theta_coe, hn])
  rw [← theta_injective φ hC h3]
  exact n.2

include φ in
theorem sup_centralizer_eq_top (hC : Subgroup.centralizer (N : Set X) ≤ N) (hidx : N.index ≤ 2)
    {ι : QuaternionGroup 2 →* X} (hι : Function.Injective ι)
    (htN : ι (QuaternionGroup.a 2) ∈ N) {a a' : X} (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (ha2' : a' * a' = 1) (ha1' : a' ≠ 1) (hne : a' ≠ a) (hcomm : a * a' = a' * a) :
    Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({a'} : Set X) = ⊤ := by
  let Ψ : X ≃* ↥A6Models.m10 := ((MonoidHom.ofInjective (theta_injective φ hC)).trans
    (Subgroup.equivMapOfInjective (theta φ).range A6Models.autA6.subtype
      Subtype.val_injective)).trans (MulEquiv.subgroupCongr (map_range_theta φ hC hidx hι htN))
  refine E3C269G.sup_centralizer_eq_top_of_equiv Ψ ?_
  have hT2 : Ψ a * Ψ a = 1 := by rw [← map_mul, ha2, map_one]
  have hT1 : Ψ a ≠ 1 := fun h => ha1 (Ψ.injective (h.trans (map_one Ψ).symm))
  have hS2 : Ψ a' * Ψ a' = 1 := by rw [← map_mul, ha2', map_one]
  have hS1 : Ψ a' ≠ 1 := fun h => ha1' (Ψ.injective (h.trans (map_one Ψ).symm))
  exact E3C269G9.sup_centralizer_m10 hT2 hT1 (by rw [← map_mul, ← map_mul, hcomm])
    (fun h => hne (Ψ.injective h)) (exists_conj_m10 hT2 hT1 hS2 hS1)

end Theta

theorem fields_of_fstar {X : Type} [Group X] [Finite X]
    (hs : IsSimpleGroup ↥(genFittingFStar X)) (hidx : (genFittingFStar X).index ≤ 2) {p f : ℕ}
    (hL : LieModel (FStarQuot X) .PSL 2 p f) (h9 : p ^ f = 9) {ι : QuaternionGroup 2 →* X}
    (hι : Function.Injective ι) :
    (∃ a b : ↥(genFittingFStar X), a * b ≠ b * a) ∧
      (∀ a : X, a * a = 1 → a ∈ genFittingFStar X) ∧
      AutAlphaPairs ↥(genFittingFStar X) ∧
      (∀ a a' : ↥(genFittingFStar X), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 →
        ∃ g : ↥(genFittingFStar X), g * a * g⁻¹ = a') ∧
      (∀ a a' : X, a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 → a' ≠ a → a * a' = a' * a →
        Subgroup.centralizer ({a} : Set X) ⊔ Subgroup.centralizer ({a'} : Set X) = ⊤) ∧
      (∀ (P : Subgroup X) (e : ↥P ≃* QuaternionGroup 2) (β : MulAut X), β * β = 1 →
        (∀ x ∈ P, β x = x) →
          β = 1 ∨ β = MulAut.conj ((e.symm (QuaternionGroup.a 2) : ↥P) : X)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := MF164.exists_fstar_equiv_psl2 hs hL
  let _ : Fintype F := Fintype.ofFinite F
  have hF9 : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hF, h9]
  obtain ⟨e6⟩ :=
    LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
      F hF9
  obtain ⟨-, ψ, -, -⟩ := Unc25K1.A6Model.exists_pslEquiv
  have : (genFittingFStar X).Normal := genFittingFStar_normal X
  have hC := CFSG.Adapters.generalized_fitting_self_centralizing X
  have htN : ι (QuaternionGroup.a 2) ∈ genFittingFStar X := by
    rw [show QuaternionGroup.a 2 = QuaternionGroup.a (n := 2) 1 * QuaternionGroup.a 1 by decide,
      map_mul]
    rcases Nat.lt_or_ge (genFittingFStar X).index 2 with h | h
    · have h1 : (genFittingFStar X).index = 1 := by
        have := Subgroup.index_ne_zero_of_finite (H := genFittingFStar X)
        omega
      rw [Subgroup.index_eq_one.mp h1]
      exact Subgroup.mem_top _
    · exact Subgroup.mul_self_mem_of_index_two (le_antisymm hidx h) _
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos f with hf0 | hf0
    · rw [hf0] at h9
      norm_num at h9
    · have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0.ne'
      rw [h9] at h2
      norm_num at h2
  set φ := (e.trans e6).trans ψ.symm
  refine ⟨exists_ne_comm_of_equiv φ, fun a ha => mem_of_mul_self_eq_one φ hC hidx hι htN ha,
    autAlphaPairs_of_equiv φ, fun a a' h1 h2 h3 h4 => exists_conj_of_equiv φ h1 h2 h3 h4,
    fun a a' h1 h2 h3 h4 h5 h6 => sup_centralizer_eq_top φ hC hidx hι htN h1 h2 h3 h4 h5 h6,
    fun P e β hβ hP => ?_⟩
  have := hs
  exact MF163.eq_one_or_conj_of_quat_psl2 hp2 hL (P.subtype.comp e.symm.toMonoidHom)
    (Subtype.val_injective.comp e.symm.injective) β hβ fun g => hP _ (e.symm g).2

end CFSG.ClassicalInvolution.Q3.TL4.Z2M10

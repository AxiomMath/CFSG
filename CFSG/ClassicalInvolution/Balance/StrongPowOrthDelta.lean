module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthSide
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.Balance (deltaCore)

@[expose] def OrthGenAniso : Prop :=
  ∀ (F V : Type) [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q : QuadraticForm F V), (polarBilin Q).Nondegenerate → Odd (Nat.card F) → 5 ≤ Nat.card F →
    7 ≤ Module.finrank F V → ∀ t₁ t₂ : V ≃ₗ[F] V,
      t₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q → t₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q →
      t₁ * t₁ = 1 → t₂ * t₂ = 1 → t₁ * t₂ = t₂ * t₁ →
      (∀ x : V, ∀ ε δ : F, t₁ x = ε • x → t₂ x = δ • x → Q x = 0 → x = 0) →
      ∀ H : Subgroup (V ≃ₗ[F] V),
        (∀ ε : F, ε * ε = 1 → elemOn Q (eigenSub t₁ ε) ≤ H) →
        (∀ δ : F, δ * δ = 1 → elemOn Q (eigenSub t₂ δ) ≤ H) →
        (∀ c : F, c * c = 1 → elemOn Q (eigenSub (t₁ * t₂) c) ≤ H) →
        elementaryGroup Q ≤ H

section Delta

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eigenvalue_sq_eq_one {t : V ≃ₗ[F] V} (ht : t * t = 1) {x : V} (hx : x ≠ 0) {ε : F}
    (h : t x = ε • x) : ε * ε = 1 := by
  have h1 : t (t x) = x := by
    have := congrArg (fun g : V ≃ₗ[F] V => g x) ht
    simpa using this
  rw [h, LinearEquiv.map_smul, h, smul_smul] at h1
  by_contra hne
  apply hx
  have : (ε * ε - 1) • x = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  exact (smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

theorem commute_of_deltaCore_orth [Finite F] [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hQ : (polarBilin Q).Nondegenerate)
    (h7 : 7 ≤ Module.finrank F V) (hperf : Group.IsPerfect (spinGroup Q))
    (hrange : (spinAction Q).range = elementaryGroup Q) (hAniso : OrthGenAniso) {X : Type}
    [Group X] [Finite X] (ψ : spinGroup Q →* X) (hker : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hnorm : ψ.range.Normal) {Fo : Subgroup X} (hcard : Nat.card Fo = 4)
    (hF2 : ∀ f ∈ Fo, f * f = 1) (htoral : ToralDiagOrth 2 ψ Fo) {d : X} (hd : d ∈ deltaCore Fo)
    {x : X} (hx : x ∈ ψ.range) : d * x = x * d := by
  obtain ⟨a, haF, b, hbF, ha1, hb1, hab1⟩ :=
    CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.exists_pair_of_card_four hcard hF2
  have hdmem : ∀ f ∈ Fo, f ≠ 1 → d ∈ involutionOddCore f := fun f hf hf1 =>
    CFSG.ClassicalInvolution.Balance.mem_deltaCore_iff.mp hd f hf hf1
  obtain ⟨P, hPc, hPO, hact⟩ := htoral
  obtain ⟨sa, hsaP, hsa2, αa, hαaθ, hαaψ⟩ := hact a haF
  obtain ⟨sb, hsbP, hsb2, αb, hαbθ, hαbψ⟩ := hact b hbF
  rw [pow_two] at hsa2 hsb2
  have hsaO := hPO sa hsaP
  have hsbO := hPO sb hsbP
  have hcomm : sa * sb = sb * sa := hPc sa hsaP sb hsbP
  have hsabO : sa * sb ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hPO _ (P.mul_mem hsaP hsbP)
  have hsab2 : (sa * sb) * (sa * sb) = 1 := by
    calc (sa * sb) * (sa * sb) = sa * (sb * sa) * sb := by group
      _ = sa * (sa * sb) * sb := by rw [hcomm]
      _ = (sa * sa) * (sb * sb) := by group
      _ = 1 := by rw [hsa2, hsb2, one_mul]
  have hθker := ker_spinAction_le_center Q
  set αab : spinGroup Q ≃* spinGroup Q := αb.trans αa with hαab
  have hαabψ : ∀ y, (a * b) * ψ y * (a * b)⁻¹ = ψ (αab y) := fun y => by
    have e : (a * b) * ψ y * (a * b)⁻¹ = a * (b * ψ y * b⁻¹) * a⁻¹ := by group
    rw [e, hαbψ y, hαaψ (αb y)]
    rfl
  have hαabθ : ∀ y, spinAction Q (αab y) = (sa * sb) * spinAction Q y * (sa * sb)⁻¹ := fun y => by
    have e : (sa * sb) * spinAction Q y * (sa * sb)⁻¹ =
        sa * (sb * spinAction Q y * sb⁻¹) * sa⁻¹ := by group
    rw [e, ← hαbθ y, ← hαaθ (αb y)]
    rfl
  set Hd : Subgroup (V ≃ₗ[F] V) :=
    ((Subgroup.centralizer ({d} : Set X)).comap ψ).map (spinAction Q) with hHd
  have side : ∀ (f : X) (α : spinGroup Q ≃* spinGroup Q) (s : V ≃ₗ[F] V),
      f ≠ 1 → f ∈ Fo → (∀ y, f * ψ y * f⁻¹ = ψ (α y)) →
      s ∈ TauCeti.QuadraticMap.orthogonalGroup Q → s * s = 1 →
      (∀ y, spinAction Q (α y) = s * spinAction Q y * s⁻¹) →
      ∀ ε : F, ε * ε = 1 → elemOn Q (eigenSub s ε) ≤ Hd := fun f α s hf1 hfF hαψ hsO hs2 hαθ ε hε =>
    elemOn_le_map_centralizer h2 hodd h5 hQ ψ hker hnorm (spinAction Q) hθker hrange f α hαψ s hsO
      hs2 hαθ hε (hdmem f hfF hf1)
  have sideA := side a αa sa ha1 haF hαaψ hsaO hsa2 hαaθ
  have sideB := side b αb sb hb1 hbF hαbψ hsbO hsb2 hαbθ
  have sideAB := side (a * b) αab (sa * sb) hab1 (Fo.mul_mem haF hbF) hαabψ hsabO hsab2 hαabθ
  have hGen : elementaryGroup Q ≤ Hd := by
    by_cases hiso : ∃ e : V, e ≠ 0 ∧ Q e = 0 ∧ ∃ ε δ : F, sa e = ε • e ∧ sb e = δ • e
    · obtain ⟨e, he0, hQe, ε, δ, he1, he2⟩ := hiso
      have hε : ε * ε = 1 := eigenvalue_sq_eq_one hsa2 he0 he1
      have hδ : δ * δ = 1 := eigenvalue_sq_eq_one hsb2 he0 he2
      obtain ⟨P₀, hP₀e, hP₀f₁, hP₀f₂⟩ := exists_hypPair_joint h2 hQ hsaO hsbO hsa2 hsb2 hcomm hε hδ
        hQe he0 he1 he2
      exact elementaryGroup_le_of_eigen h2 hQ (by omega) hsaO hsbO hsa2 hsb2 hcomm hε hδ P₀
        (by rw [hP₀e]; exact he1) hP₀f₁ (by rw [hP₀e]; exact he2) hP₀f₂
        (fun x hx => hx) (fun x hx => hx) (fun x hx => hx) (sideA ε hε) (sideB δ hδ)
        (sideAB (ε * δ) (by linear_combination (δ * δ) * hε + hδ))
    · push Not at hiso
      exact hAniso F V Q hQ hodd h5 h7 sa sb hsaO hsbO hsa2 hsb2 hcomm
        (fun x ε δ h1 h2' hQx => by
          by_contra hx0
          exact hiso x hx0 hQx ε δ h1 h2') Hd sideA sideB sideAB
  have htop : (Subgroup.centralizer ({d} : Set X)).comap ψ = ⊤ :=
    eq_top_of_range_le_map (spinAction Q) hθker (R := (Subgroup.centralizer ({d} : Set X)).comap ψ)
      (by rw [hrange]; exact hGen)
  obtain ⟨y, rfl⟩ := hx
  have hy : y ∈ (Subgroup.centralizer ({d} : Set X)).comap ψ := by rw [htop]; trivial
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hy
  exact hy.symm

end Delta

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

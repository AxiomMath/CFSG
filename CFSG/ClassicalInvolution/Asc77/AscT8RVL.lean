module

public import CFSG.ClassicalInvolution.Asc77.AscT8RFr

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8R

section Setup

variable {G : Type} [Group G] [Finite G]

theorem isSylow2In_conjSub_sylow (S : Sylow 2 G) (n : G) {H : Subgroup G}
    (h : conjSub n (S : Subgroup G) ≤ H) : IsSylow2In (conjSub n (S : Subgroup G)) H := by
  have h0 : IsSylow2In (S : Subgroup G) ⊤ := T8.isSylow2In_of_sylow_le S le_top
  have h1 : IsSylow2In (conjSub n (S : Subgroup G)) (conjSub n ⊤) := h0.conj n
  have htop : conjSub n (⊤ : Subgroup G) = ⊤ := by
    ext x
    simp [mem_conjSub_iff]
  rw [htop] at h1
  exact ⟨h, h1.2.1, fun V' _ hV2 hle => h1.2.2 V' le_top hV2 hle⟩

theorem exists_conj_sylow_of_centralizes (S : Sylow 2 G) {a : G}
    (haS : ∀ s ∈ (S : Subgroup G), s * a = a * s) {n x : G}
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) (hxc : x * (n * a * n⁻¹) = (n * a * n⁻¹) * x) :
    ∃ n' : G, n' * a * n'⁻¹ = n * a * n⁻¹ ∧ x ∈ conjSub n' (S : Subgroup G) := by
  set c : G := n * a * n⁻¹ with hc
  have hPC : conjSub n (S : Subgroup G) ≤ Subgroup.centralizer ({c} : Set G) := by
    intro y hy
    rw [mem_conjSub_iff] at hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := haS _ hy
    calc y * c = n * ((n⁻¹ * y * n) * a) * n⁻¹ := by rw [hc]; group
      _ = n * (a * (n⁻¹ * y * n)) * n⁻¹ := by rw [h1]
      _ = c * y := by rw [hc]; group
  have hPs := isSylow2In_conjSub_sylow S n hPC
  have hxC : Subgroup.zpowers x ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hxc
  obtain ⟨V, hV, hxV⟩ := IsSylow2In.exists_ge hx2 hxC
  obtain ⟨c₂, hc₂, hc₂V⟩ := Thompson.exists_conj_of_isSylow2In hPs hV
  have hc₂c : c₂ * c = c * c₂ := by
    exact Subgroup.mem_centralizer_singleton_iff.mp hc₂
  refine ⟨c₂ * n, ?_, ?_⟩
  · calc c₂ * n * a * (c₂ * n)⁻¹ = c₂ * (n * a * n⁻¹) * c₂⁻¹ := by group
      _ = c₂ * c * c₂⁻¹ := by rw [hc]
      _ = c := by rw [hc₂c]; group
  · rw [conjSub_mul, hc₂V]
    exact hxV (Subgroup.mem_zpowers x)

end Setup

section Cert

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

@[expose] def ExtraTrans (Ω : Set (Subgroup G)) (K J : Subgroup G) (S : Sylow 2 G) (z t : G) :
    Prop :=
  ∀ M ∈ Ω, 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G)) → M ≠ K → M ≠ J →
    ∃ c ∈ Subgroup.centralizer ({z * t} : Set G), conjSub c K = M ∨ conjSub c J = M


theorem conj_zt_mul_inv_mem_of_orderFour (hs : Std8 p f Ω K J S R T W z t)
    (hX : omegaNbrGen Ω K = J ⊔ oddCoreOf (omegaNbrGen Ω K)) (hV : ExtraTrans Ω K J S z t)
    {n x : G} (hxK : x ∈ K) (hx4 : orderOf x = 4)
    (hxc : x * (n * (z * t) * n⁻¹) = (n * (z * t) * n⁻¹) * x) :
    n * (z * t) * n⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := by
  have hp : p ≠ 2 := hs.stand.odd
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  have hK : K ∈ Ω := hs.stand.mem
  obtain ⟨hRΩ, hRK, hRS⟩ := hs.hR
  obtain ⟨hTΩ, hTJ, hTS⟩ := hs.hT
  have hJΩ : J ∈ Ω := hs.hJ.1
  have hRsyl : IsSylow2In R K := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hK hRΩ hRK
  have hTsyl : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hTΩ hTJ
  have h8R := hΩ.eight_le_of_mem_RSet hp hRΩ
  have h8T := hΩ.eight_le_of_mem_RSet hp hTΩ
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  have haS : ∀ s ∈ (S : Subgroup G), s * (z * t) = (z * t) * s := fun s hs' => by
    have := conj_zt_of_mem_sylow hs hX hs'
    calc s * (z * t) = (s * (z * t) * s⁻¹) * s := by group
      _ = (z * t) * s := by rw [this]
  obtain ⟨n', hn'c, hxn'⟩ := exists_conj_sylow_of_centralizes S haS hx2 hxc
  rw [← hn'c]
  have key : ∀ m : G, (conjSub m K = K ∨ conjSub m J = K) →
      m * (z * t) * m⁻¹ = n' * (z * t) * n'⁻¹ →
      n' * (z * t) * n'⁻¹ * (z * t)⁻¹ ∈ oddCoreOf (omegaNbrGen Ω K) := fun m hm hmc => by
    rw [← hmc]
    exact conj_zt_mul_inv_mem_of_conj hs hX hm
  set M : Subgroup G := conjSub n'⁻¹ K with hMdef
  have hMΩ : M ∈ Ω := hΩ.conjInvariant n'⁻¹ K hK
  have hKM : conjSub n' M = K := by rw [hMdef, conjSub_conjSub_inv]
  have hx'M : n'⁻¹ * x * n' ∈ M := by
    rw [hMdef, mem_conjSub_iff]
    have e : (n'⁻¹)⁻¹ * (n'⁻¹ * x * n') * n'⁻¹ = x := by group
    rw [e]
    exact hxK
  have hx'S : n'⁻¹ * x * n' ∈ (S : Subgroup G) := (mem_conjSub_iff.mp hxn')
  have hx'o : orderOf (n'⁻¹ * x * n') = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj n'⁻¹) x
    rw [MulAut.conj_apply, hx4] at this
    simpa using this
  have h4 : 4 ≤ Nat.card ↥(M ⊓ (S : Subgroup G)) := by
    have hle : Subgroup.zpowers (n'⁻¹ * x * n') ≤ M ⊓ (S : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hx'M) (Subgroup.zpowers_le.mpr hx'S)
    have := Subgroup.card_le_of_le hle
    rwa [Nat.card_zpowers, hx'o] at this
  have hKS : K ⊓ (S : Subgroup G) = R :=
    hRsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hRK hRS)
  have hJS : J ⊓ (S : Subgroup G) = T :=
    hTsyl.eq_of_le (S.isPGroup'.to_inf_right) inf_le_left (le_inf hTJ hTS)
  by_cases hSyl : IsSylow2In (M ⊓ (S : Subgroup G)) M
  · have hMR : M ⊓ (S : Subgroup G) ∈ RSet Ω := mem_RSet_of_isSylow2In hMΩ hSyl
    rcases eq_or_eq_of_mem_RSet_of_le hs hX hMR inf_le_right with h | h
    · have hRM : R ≤ M := h ▸ inf_le_left
      have hMK : M = K :=
        hΩ.eq_of_le_of_le hMΩ hK hRsyl.2.1 (by omega) hRM hRK
      refine key n' (Or.inl ?_) rfl
      have h' := hKM
      rw [hMK] at h'
      exact h'
    · have hTM : T ≤ M := h ▸ inf_le_left
      have hMJ : M = J :=
        hΩ.eq_of_le_of_le hMΩ hJΩ hTsyl.2.1 (by omega) hTM hTJ
      refine key n' (Or.inr ?_) rfl
      have h' := hKM
      rw [hMJ] at h'
      exact h'
  · have hMK : M ≠ K := by
      intro h
      exact hSyl (by rw [h, hKS]; exact hRsyl)
    have hMJ : M ≠ J := by
      intro h
      exact hSyl (by rw [h, hJS]; exact hTsyl)
    obtain ⟨c₁, hc₁, hc₁K⟩ := hV M hMΩ h4 hMK hMJ
    have hc₁a : c₁ * (z * t) * c₁⁻¹ = z * t := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc₁
      calc c₁ * (z * t) * c₁⁻¹ = ((z * t) * c₁) * c₁⁻¹ := by rw [this]
        _ = z * t := by group
    refine key (n' * c₁) ?_ ?_
    · rcases hc₁K with h | h
      · left
        rw [conjSub_mul, h, hKM]
      · right
        rw [conjSub_mul, h, hKM]
    · calc n' * c₁ * (z * t) * (n' * c₁)⁻¹ = n' * (c₁ * (z * t) * c₁⁻¹) * n'⁻¹ := by group
        _ = n' * (z * t) * n'⁻¹ := by rw [hc₁a]

end Cert

end T8R

end CFSG.ClassicalInvolution.Asc77

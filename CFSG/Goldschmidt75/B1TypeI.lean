module

public import CFSG.Goldschmidt75.B1Out
public import CFSG.Goldschmidt.Steps.G3aBorel

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup
open scoped MatrixGroups commutatorElement

variable {Q : Type} [Group Q]

theorem commutator_sup_le_of_comm {T D : Subgroup Q} (hD : D ≤ normalizer (T : Set Q))
    (hDab : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d) : ⁅T ⊔ D, T ⊔ D⁆ ≤ T := by
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h₁ : g₁ ∈ ((D ⊔ T : Subgroup Q) : Set Q) := by rw [sup_comm]; exact hg₁
  have h₂ : g₂ ∈ ((D ⊔ T : Subgroup Q) : Set Q) := by rw [sup_comm]; exact hg₂
  rw [coe_mul_of_left_le_normalizer_right _ _ hD] at h₁ h₂
  obtain ⟨d₁, hd₁, t₁, ht₁, rfl⟩ := h₁
  obtain ⟨d₂, hd₂, t₂, ht₂, rfl⟩ := h₂
  have hc : d₁ * d₂ ∈ normalizer (T : Set Q) := mul_mem (hD hd₁) (hD hd₂)
  have ht₁' : d₂⁻¹ * t₁ * d₂ ∈ T := by
    have := (mem_normalizer_iff.mp (hD (inv_mem hd₂)) t₁).mp ht₁
    simpa using this
  have ht₂' : d₁⁻¹ * t₂ * d₁ ∈ T := by
    have := (mem_normalizer_iff.mp (hD (inv_mem hd₁)) t₂).mp ht₂
    simpa using this
  have hin : d₂⁻¹ * t₁ * d₂ * t₂ * t₁⁻¹ * (d₁⁻¹ * t₂ * d₁)⁻¹ ∈ T :=
    mul_mem (mul_mem (mul_mem ht₁' ht₂) (inv_mem ht₁)) (inv_mem ht₂')
  have h12 : d₁ * d₂⁻¹ * d₁⁻¹ = d₂⁻¹ := by
    have h := hDab d₁ hd₁ d₂ hd₂
    calc d₁ * d₂⁻¹ * d₁⁻¹ = d₂⁻¹ * (d₂ * d₁) * d₂⁻¹ * d₁⁻¹ := by group
      _ = d₂⁻¹ * (d₁ * d₂) * d₂⁻¹ * d₁⁻¹ := by rw [h]
      _ = d₂⁻¹ := by group
  have e : ⁅d₁ * t₁, d₂ * t₂⁆ =
      (d₁ * d₂) * (d₂⁻¹ * t₁ * d₂ * t₂ * t₁⁻¹ * (d₁⁻¹ * t₂ * d₁)⁻¹) * (d₁ * d₂)⁻¹ := by
    rw [commutatorElement_def]
    calc d₁ * t₁ * (d₂ * t₂) * (d₁ * t₁)⁻¹ * (d₂ * t₂)⁻¹
        = d₁ * t₁ * d₂ * t₂ * t₁⁻¹ * d₁⁻¹ * t₂⁻¹ * d₂⁻¹ := by group
      _ = d₁ * t₁ * d₂ * t₂ * t₁⁻¹ * d₁⁻¹ * t₂⁻¹ * (d₁ * d₂⁻¹ * d₁⁻¹) := by rw [h12]
      _ = (d₁ * d₂) * (d₂⁻¹ * t₁ * d₂ * t₂ * t₁⁻¹ * (d₁⁻¹ * t₂ * d₁)⁻¹) * (d₁ * d₂)⁻¹ := by
        group
  rw [e]
  exact (mem_normalizer_iff.mp hc _).mp hin

theorem isSolvable_of_commutator_le [Finite Q] {P T : Subgroup Q} (hT : IsPGroup 2 T)
    (h : ⁅P, P⁆ ≤ T) : Group.IsSolvable P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : ∀ x : commutator P, ((x : P) : Q) ∈ T := by
    intro x
    apply h
    rw [← map_subtype_commutator]
    exact ⟨x, x.2, rfl⟩
  let φ : commutator P →* T :=
    { toFun := fun x => ⟨((x : P) : Q), hmap x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hφ : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h1 := congrArg Subtype.val hxy
    exact h1
  have hp : IsPGroup 2 (commutator P) := IsPGroup.of_injective hT φ hφ
  have : Group.IsNilpotent (commutator P) := hp.isNilpotent
  have : Group.IsSolvable (commutator P) := inferInstance
  exact Group.isSolvable_commutator_iff.mp this

theorem fusionIsBenderGroup_of_isGoldTypeI (hZ : center Q = ⊥) (hI : IsGoldTypeI Q) :
    fusionIsBenderGroup Q := by
  let eQ : Q ≃* Q ⧸ center Q :=
    (QuotientGroup.quotientBot (G := Q)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl ⟨n, by omega, ⟨eQ.trans e⟩⟩
  · exact Or.inr (Or.inr ⟨n, hn, ⟨eQ.trans e⟩⟩)
  · exact Or.inr (Or.inl ⟨n, hn, ⟨eQ.trans e⟩⟩)

theorem action_eq_one_typeI
    {Λ : Type} [Group Λ] [Group.IsPerfect Λ] [Finite Q] [IsSimpleGroup Q]
    (hZ : center Q = ⊥) (hI : IsGoldTypeI Q) (T : Sylow 2 Q) (Φ : Λ →* MulAut Q)
    (hfix : ∀ l, ∀ x ∈ Omega1 (T : Subgroup Q), Φ l x = x) (l : Λ) : Φ l = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := fusionIsBenderGroup_of_isGoldTypeI hZ hI
  obtain ⟨D, hDN, hDcyc, -, -, hTDN, -, -, hΩ, -, -, -, -, -, -, -, -, hcoat, h6⟩ := G32 Q hI T
  set C := centralizer ((Omega1 (T : Subgroup Q) : Subgroup Q) : Set Q) with hC
  have hTC : (T : Subgroup Q) ≤ C := by
    intro t ht
    rw [mem_centralizer_iff]
    intro x hx
    rw [hΩ] at hx
    exact (mem_centralizer_iff.mp (mem_inf.mp hx).2 t ht).symm
  have hTne : (T : Subgroup Q) ≠ ⊥ := by
    intro h
    apply hcoat.1
    rw [h, normalizer_eq_top]
  have hCne : C ≠ ⊤ := by
    intro hCtop
    rcases T.isPGroup'.card_eq_or_dvd with h1 | h2
    · exact hTne ((Subgroup.card_eq_one).mp h1)
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (T : Subgroup Q)) 2 h2
    have hx' : orderOf (x : Q) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have hx2 : (x : Q) ^ 2 = 1 := by
      have h := pow_orderOf_eq_one (x : Q)
      rwa [hx'] at h
    have hxΩ : (x : Q) ∈ Omega1 (T : Subgroup Q) := subset_closure ⟨x.2, hx2⟩
    have hxZ : (x : Q) ∈ center Q := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ C := hCtop ▸ mem_top g
      exact (mem_centralizer_iff.mp hg _ hxΩ).symm
    rw [hZ, mem_bot] at hxZ
    rw [hxZ, orderOf_one] at hx'
    exact absurd hx' (by norm_num)
  have hCN := h6 C hTC hCne
  have hDab : ∀ d ∈ D, ∀ d' ∈ D, d * d' = d' * d := by
    intro d hd d' hd'
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D)
    obtain ⟨m, hm⟩ := hg ⟨d, hd⟩
    obtain ⟨m', hm'⟩ := hg ⟨d', hd'⟩
    have e1 : d = ((g ^ m : D) : Q) := congrArg Subtype.val hm.symm
    have e2 : d' = ((g ^ m' : D) : Q) := congrArg Subtype.val hm'.symm
    rw [e1, e2, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← zpow_add, ← zpow_add, add_comm]
  set W := Φ.range with hW
  have hWin : W ≤ (MulAut.conj : Q →* MulAut Q).range := by
    rintro _ ⟨l', rfl⟩
    obtain ⟨x, hx⟩ := exists_conj_of_bender hB Φ l'
    exact ⟨x, hx.symm⟩
  set P := W.comap (MulAut.conj : Q →* MulAut Q) with hP
  have hPC : P ≤ C := by
    intro q hq
    obtain ⟨l', hl'⟩ := hq
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hfix l' x hx
    rw [hl', MulAut.conj_apply] at h1
    calc x * q = q * x * q⁻¹ * q := by rw [h1]
      _ = q * x := by group
  have hPsol : Group.IsSolvable P := by
    refine isSolvable_of_commutator_le T.isPGroup' ?_
    refine (commutator_mono (hPC.trans hCN) (hPC.trans hCN)).trans ?_
    rw [← hTDN]
    exact commutator_sup_le_of_comm hDN hDab
  have hWsol : Group.IsSolvable W := by
    have h := Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective
      (MulAut.conj : Q →* MulAut Q) P)
    rwa [hP, map_comap_eq_self hWin] at h
  have hWperf : Group.IsPerfect W := Group.IsPerfect.range Φ
  have hWbot : W = ⊥ := by
    by_contra hne
    have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hne
    exact Group.IsPerfect.not_isSolvable W hWsol
  have hl : Φ l ∈ W := ⟨l, rfl⟩
  rw [hWbot, mem_bot] at hl
  exact hl

end CFSG.Goldschmidt75

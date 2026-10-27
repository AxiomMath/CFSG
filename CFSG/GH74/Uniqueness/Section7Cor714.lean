module

public import CFSG.GH74.Uniqueness.Section7Cor713
public import CFSG.GH74.Uniqueness.Section4Residual

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Parity

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

@[expose] def Cor714.permZM (hZ : IsInvariantInvolutionSet Z) (M : Subgroup X) (m : M) :
    Equiv.Perm ↥(Z ∩ (M : Set X)) where
  toFun z := ⟨(m : X) * z * (m : X)⁻¹, by
    have h1 := hZ.2 (z : X) z.2.1 ((m : X)⁻¹)
    exact ⟨by simpa using h1, M.mul_mem (M.mul_mem m.2 z.2.2) (M.inv_mem m.2)⟩⟩
  invFun z := ⟨(m : X)⁻¹ * z * (m : X), hZ.2 (z : X) z.2.1 (m : X),
    M.mul_mem (M.mul_mem (M.inv_mem m.2) z.2.2) m.2⟩
  left_inv z := Subtype.ext (by simp [mul_assoc])
  right_inv z := Subtype.ext (by simp [mul_assoc])

@[expose] def Cor714.permHom (hZ : IsInvariantInvolutionSet Z) (M : Subgroup X) :
    M →* Equiv.Perm ↥(Z ∩ (M : Set X)) where
  toFun := Cor714.permZM hZ M
  map_one' := by
    ext z
    simp [Cor714.permZM]
  map_mul' a b := by
    ext z
    simp [Cor714.permZM, mul_assoc]

theorem ZDSetup.cor714_not_comm (S : ZDSetup X Z M) : ¬ ∀ a b : X, a * b = b * a := by
  intro hcomm
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  apply S.prodDisc.1
  rw [eq_top_iff]
  intro x _
  exact S.prodDisc.centralizer_le_of_mem hz hzM
    (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x z))

theorem ZDSetup.cor714_closure_odd_eq_top
    (S : ZDSetup X Z M) :
    Subgroup.closure {y : X | Odd (orderOf y)} = ⊤ := by
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.closure {y : X | Odd (orderOf y)})
    with h | h
  · exfalso
    have h2 : IsPGroup 2 X := by
      rw [IsPGroup.iff_orderOf]
      intro g
      obtain ⟨k, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
      have hdvd : 2 ^ k ∣ orderOf g := ⟨m, hgm⟩
      have hord : orderOf (g ^ 2 ^ k) = m := by
        rw [orderOf_pow_of_dvd (pow_ne_zero k two_ne_zero) hdvd, hgm,
          Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
      have hmem : g ^ 2 ^ k ∈ Subgroup.closure {y : X | Odd (orderOf y)} :=
        Subgroup.subset_closure (by show Odd (orderOf (g ^ 2 ^ k)); rw [hord]; exact hm)
      rw [h, Subgroup.mem_bot] at hmem
      have h1 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hmem
      rw [hgm] at h1
      have hm1 : m = 1 := by
        have := Nat.le_of_dvd (pow_pos two_pos k) h1
        have h3 : 2 ^ k * m ≤ 2 ^ k * 1 := by simpa using this
        have h4 := Nat.le_of_mul_le_mul_left h3 (pow_pos two_pos k)
        have h5 : 0 < m := hm.pos
        omega
      exact ⟨k, by rw [hgm, hm1, mul_one]⟩
    have : Group.IsNilpotent X := h2.isNilpotent
    have hsolv : Group.IsSolvable X := inferInstance
    exact S.cor714_not_comm (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv)
  · exact h

omit [Finite X] in
theorem Cor714.ncard_fixedPoints_permHom (hZ : IsInvariantInvolutionSet Z) {v : X} (hvM : v ∈ M) :
    (Function.fixedPoints (Cor714.permHom hZ M ⟨v, hvM⟩)).ncard =
      (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard := by
  have himage : (Subtype.val : ↥(Z ∩ (M : Set X)) → X) ''
      Function.fixedPoints (Cor714.permHom hZ M ⟨v, hvM⟩) =
      Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h1 : v * (z : X) * v⁻¹ = z := congrArg Subtype.val hz
      refine ⟨z.2.1, Subgroup.mem_inf.mpr ⟨?_, z.2.2⟩⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (z : X) * v = (v * (z : X) * v⁻¹) * v := by rw [h1]
        _ = v * z := by group
    · rintro ⟨hyZ, hyCM⟩
      obtain ⟨hyC, hyM⟩ := Subgroup.mem_inf.mp hyCM
      have hyv : y * v = v * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      refine ⟨⟨y, hyZ, hyM⟩, ?_, rfl⟩
      apply Subtype.ext
      show v * y * v⁻¹ = y
      rw [← hyv]
      group
  rw [← himage, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem ZDSetup.cor714_false_of_parity
    (S : ZDSetup X Z M) {v₁ v₂ : X} (h₁ : orderOf v₁ = 2)
    (h₂ : orderOf v₂ = 2) (hv₁ : v₁ ∈ M) (hv₂ : v₂ ∈ M)
    (hf₁ : (Z ∩ ((centralizer ({v₁} : Set X) ⊓ M : Subgroup X) : Set X)).ncard = 1) {n : ℕ}
    (hn : 2 ≤ n)
    (hf₂ : (Z ∩ ((centralizer ({v₂} : Set X) ⊓ M : Subgroup X) : Set X)).ncard = 2 ^ n - 1) :
    False := by
  classical
  have : Fintype ↥(Z ∩ (M : Set X)) := Fintype.ofFinite _
  let ρ := Cor714.permHom S.invariant M
  let ε : M →* ℤˣ := (Equiv.Perm.sign).comp ρ
  have key : ∀ (v : X) (hv2 : orderOf v = 2) (hvM : v ∈ M),
      ε ⟨v, hvM⟩ = (-1) ^ ((zNum Z M -
        (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard) / 2) := by
    intro v hv2 hvM
    have hvv : v * v = 1 := by rw [← pow_two, ← hv2]; exact pow_orderOf_eq_one v
    have hsq : (ρ ⟨v, hvM⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨v, hvM⟩ : M) ^ 2 = 1 := Subtype.ext (by simp [pow_two, hvv])
      rw [this, map_one]
    have h := Equiv.Perm.sign_of_pow_two_eq_one hsq
    show Equiv.Perm.sign (ρ ⟨v, hvM⟩) = _
    rw [h, ← Cor714.ncard_fixedPoints_permHom S.invariant hvM, ← Nat.card_coe_set_eq,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rfl
  have hle : ∀ v : X, (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard ≤
      zNum Z M := by
    intro v
    rw [zNum, ← Nat.card_coe_set_eq]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro y ⟨hyZ, hyCM⟩
    exact ⟨hyZ, (Subgroup.mem_inf.mp hyCM).2⟩
  have hm : Odd (zNum Z M) := S.odd_zNum
  have e₁ := key v₁ h₁ hv₁
  have e₂ := key v₂ h₂ hv₂
  rw [hf₁] at e₁
  rw [hf₂] at e₂
  have hle₂ := hle v₂
  rw [hf₂] at hle₂
  have h4 : 4 ∣ 2 ^ n := by
    have : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 hn
    simpa using this
  have hmodd : zNum Z M % 2 = 1 := Nat.odd_iff.mp hm
  have h5 : 4 ≤ 2 ^ n := Nat.le_of_dvd (pow_pos two_pos n) h4
  have hpar : ((zNum Z M - 1) / 2) % 2 = 1 ∨ ((zNum Z M - (2 ^ n - 1)) / 2) % 2 = 1 := by
    omega
  have hout : ∀ (v : X) (hvM : v ∈ M), ε ⟨v, hvM⟩ = -1 →
      v ∉ Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)} := by
    intro v hvM hε hmem
    have hle' : Subgroup.closure {y : X | y ∈ M ∧ Odd (orderOf y)} ≤ ε.ker.map M.subtype := by
      rw [Subgroup.closure_le]
      rintro y ⟨hyM, hyodd⟩
      refine ⟨⟨y, hyM⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
      have hord : (ε ⟨y, hyM⟩) ^ orderOf (⟨y, hyM⟩ : M) = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [Subgroup.orderOf_mk] at hord
      rcases Int.units_eq_one_or (ε ⟨y, hyM⟩) with h | h
      · exact h
      · rw [h, hyodd.neg_one_pow] at hord
        exact absurd hord (by decide)
    obtain ⟨k, hk, hkv⟩ := hle' hmem
    have hkeq : k = ⟨v, hvM⟩ := Subtype.ext hkv
    have hk' : ε k = 1 := MonoidHom.mem_ker.mp hk
    rw [hkeq, hε] at hk'
    exact absurd hk' (by decide)
  rcases hpar with hp | hp
  · have hε : ε ⟨v₁, hv₁⟩ = -1 := by
      rw [e₁]
      exact (Nat.odd_iff.mpr hp).neg_one_pow
    exact S.closure_odd_ne_top_of_not_mem hv₁ (hout v₁ hv₁ hε) S.cor714_closure_odd_eq_top
  · have hε : ε ⟨v₂, hv₂⟩ = -1 := by
      rw [e₂]
      exact (Nat.odd_iff.mpr hp).neg_one_pow
    exact S.closure_odd_ne_top_of_not_mem hv₂ (hout v₂ hv₂ hε) S.cor714_closure_odd_eq_top

end Parity

section Main

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem Cor714.not_isSolvable_of_isBenderGroup
    {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) : ¬ Group.IsSolvable K := by
  intro hsolv
  have : IsSimpleGroup K := isSimpleGroup_of_isBenderGroup hK
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_isBenderGroup hK
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

theorem ZDSetup.cor714_exists_mem_inter_centralizer (S : ZDSetup X Z M) {v : X}
    (hv2 : orderOf v = 2) (hvM : v ∈ M) :
    (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  obtain ⟨T, hTM, -, hcomm⟩ := S.exists_sylow_central hz hzM
  have hv2' : IsPGroup 2 (zpowers v) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hv2, pow_one]
  obtain ⟨h, hhM, hhT⟩ := exists_mem_conj_mem_sylow hTM hvM hv2'
  have hc : (h⁻¹ * v * h) * z = z * (h⁻¹ * v * h) := hcomm _ hhT
  refine ⟨h * z * h⁻¹, ?_, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
  · have := S.invariant.2 z hz h⁻¹
    simpa using this
  · rw [Subgroup.mem_centralizer_singleton_iff]
    calc h * z * h⁻¹ * v = h * (z * (h⁻¹ * v * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * v * h) * z) * h⁻¹ := by rw [hc]
      _ = v * (h * z * h⁻¹) := by group
  · exact M.mul_mem (M.mul_mem hhM hzM) (M.inv_mem hhM)

theorem ZDSetup.cor714_centralizer_ne_top
    (S : ZDSetup X Z M) {v : X} (hv2 : orderOf v = 2) :
    centralizer ({v} : Set X) ≠ ⊤ := by
  intro htop
  have hsimple : IsSimpleGroup X := S.theorem1_unconditional.1
  have hv1 : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv2; exact absurd hv2 (by norm_num)
  have hvc : v ∈ center X := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({v} : Set X) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h | h
  · rw [h, Subgroup.mem_bot] at hvc
    exact hv1 hvc
  · apply S.cor714_not_comm
    intro a b
    have : a ∈ center X := h ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp this b).symm

theorem ZDSetup.cor714_cases
    (S : ZDSetup X Z M) (h713 : Cor713Stmt Z M) (h713x : Cor713Extra Z M)
    {v : X} (hv2 : orderOf v = 2) (hvM : v ∈ M) (hc : ¬ centralizer ({v} : Set X) ≤ M) :
    ¬ zHull Z (centralizer ({v} : Set X)) ≤ M ∧
      ((Group.IsSolvable ↥(zHull Z (centralizer ({v} : Set X))) ∧
          (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard = 1) ∨
        (¬ Group.IsSolvable ↥(zHull Z (centralizer ({v} : Set X))) ∧
          ∃ n : ℕ, 2 ≤ n ∧
            (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard = 2 ^ n - 1)) := by
  have hne := S.cor714_exists_mem_inter_centralizer hv2 hvM
  have hF := S.cor714_centralizer_ne_top hv2
  obtain ⟨hnot, hcase⟩ := h713 _ hF hc hne
  refine ⟨hnot, ?_⟩
  by_cases hs : Group.IsSolvable ↥(zHull Z (centralizer ({v} : Set X)))
  · left
    refine ⟨hs, ?_⟩
    rcases hcase with ⟨-, u, -, hu, -⟩ | ⟨-, hB, -, -⟩
    · rw [hu, Set.ncard_singleton]
    · exfalso
      exact Cor714.not_isSolvable_of_isBenderGroup hB inferInstance
  · right
    exact ⟨hs, (h713x _ hF hc hne hs).2.2⟩

theorem ZDSetup.cor714_of_cor713
    (S : ZDSetup X Z M) (h713 : Cor713Stmt Z M)
    (h713x : Cor713Extra Z M) {v₁ v₂ : X} (h₁ : orderOf v₁ = 2) (h₂ : orderOf v₂ = 2)
    (hv₁ : v₁ ∈ M) (hv₂ : v₂ ∈ M) (hc₁ : ¬ centralizer ({v₁} : Set X) ≤ M)
    (hc₂ : ¬ centralizer ({v₂} : Set X) ≤ M) :
    (¬ zHull Z (centralizer ({v₁} : Set X)) ≤ M ∧ ¬ zHull Z (centralizer ({v₂} : Set X)) ≤ M) ∧
      (Group.IsSolvable ↥(zHull Z (centralizer ({v₁} : Set X))) ↔
        Group.IsSolvable ↥(zHull Z (centralizer ({v₂} : Set X)))) := by
  obtain ⟨hn₁, hcase₁⟩ := S.cor714_cases h713 h713x h₁ hv₁ hc₁
  obtain ⟨hn₂, hcase₂⟩ := S.cor714_cases h713 h713x h₂ hv₂ hc₂
  refine ⟨⟨hn₁, hn₂⟩, ?_⟩
  rcases hcase₁ with ⟨hs₁, hf₁⟩ | ⟨hs₁, n₁, hn₁2, hf₁⟩ <;>
    rcases hcase₂ with ⟨hs₂, hf₂⟩ | ⟨hs₂, n₂, hn₂2, hf₂⟩
  · exact ⟨fun _ => hs₂, fun _ => hs₁⟩
  · exact (S.cor714_false_of_parity h₁ h₂ hv₁ hv₂ hf₁ hn₂2 hf₂).elim
  · exact (S.cor714_false_of_parity h₂ h₁ hv₂ hv₁ hf₂ hn₁2 hf₁).elim
  · exact ⟨fun h => absurd h hs₁, fun h => absurd h hs₂⟩

theorem ZDSetup.cor714
    (S : ZDSetup X Z M) (hT4 : Theorem4Stmt Z M) {v₁ v₂ : X}
    (h₁ : orderOf v₁ = 2) (h₂ : orderOf v₂ = 2) (hv₁ : v₁ ∈ M) (hv₂ : v₂ ∈ M)
    (hc₁ : ¬ centralizer ({v₁} : Set X) ≤ M) (hc₂ : ¬ centralizer ({v₂} : Set X) ≤ M) :
    (¬ zHull Z (centralizer ({v₁} : Set X)) ≤ M ∧ ¬ zHull Z (centralizer ({v₂} : Set X)) ≤ M) ∧
      (Group.IsSolvable ↥(zHull Z (centralizer ({v₁} : Set X))) ↔
        Group.IsSolvable ↥(zHull Z (centralizer ({v₂} : Set X)))) :=
  S.cor714_of_cor713 (S.cor713 hT4) (S.cor713Extra hT4) h₁ h₂ hv₁ hv₂ hc₁ hc₂

end Main

end CFSG.GH74.Uniqueness

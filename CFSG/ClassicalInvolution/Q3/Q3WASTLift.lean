module

public import CFSG.ClassicalInvolution.Q3.Q3WASTSign
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Q3.Q3WAPow

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.RouteD
  CFSG.LieType.Universal CFSG.ClassicalInvolution.ModelFacts
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)
open scoped MatrixGroups commutatorElement



section Kernel

theorem ker_not_dvd_three_model {t : StatedLieTag} {n : ℕ} (hfund : Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) {X : Type} [Group X]
    (φ : (Generic.modelUniv t n 3 1 Nat.prime_three).K →* X)
    (hker : φ.ker ≤ Subgroup.center _) : ∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x := by
  obtain ⟨-, h2⟩ := modelFiniteCenterTwoGroup3 t n Nat.prime_three hfund hadm
  intro x hx h3
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨x, hker hx⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at h3
  have := (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

end Kernel

section Lift

variable {K X : Type} [Group K] [Group X]

theorem exists_lift_central_involution3 (φ : K →* X) (hker : φ.ker ≤ Subgroup.center K)
    (hcop : ∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) {R : Subgroup K} (e : R ≃* SL(2, GaloisField 3 1))
    {a : X} (ha : IsUniqueInvolution (R.map φ) a) :
    ∃ c ∈ R, orderOf c = 2 ∧ (∀ s ∈ R, orderOf s = 2 → s = c) ∧ a = φ c ∧
      (∀ z ∈ R, z ∈ φ.ker → z = 1) ∧ Pow3 R := by
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by
    rw [GaloisField.card 3 1 (by norm_num)]; decide
  have hP3 : Pow3 R := pow_three_mem_commutator_of_equiv card_gf3 e
  have hacent : ∀ y ∈ R, φ y * a = a * φ y := by
    intro y hy
    have hyR : φ y ∈ R.map φ := ⟨y, hy, rfl⟩
    have hk : φ y * a * (φ y)⁻¹ ∈ R.map φ :=
      (R.map φ).mul_mem ((R.map φ).mul_mem hyR ha.mem) ((R.map φ).inv_mem hyR)
    have hkk : φ y * a * (φ y)⁻¹ * (φ y * a * (φ y)⁻¹) = 1 := by
      calc φ y * a * (φ y)⁻¹ * (φ y * a * (φ y)⁻¹) = φ y * (a * a) * (φ y)⁻¹ := by group
        _ = 1 := by rw [ha.sq]; group
    rcases ha.unique _ hk hkk with h | h
    · exfalso
      apply ha.ne_one
      have := congrArg (fun x => (φ y)⁻¹ * x * φ y) h
      simpa [mul_assoc] using this
    · exact mul_inv_eq_iff_eq_mul.mp h
  obtain ⟨r, hr, hra⟩ := ha.mem
  have hcomm : ∀ y ∈ R, y * r = r * y := by
    intro y hy
    have h := commutes_of_map_commute_exponent3 φ hker hcop (A := Subgroup.zpowers r) (L := R)
      hP3 (fun a' ha' l hl => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
        rw [map_zpow, hra]
        exact ((Commute.zpow_left (show Commute a (φ l) from (hacent l hl).symm) k)).eq) r
      (Subgroup.mem_zpowers r) y hy
    exact h.symm
  have hrc : (⟨r, hr⟩ : R) ∈ Subgroup.center R :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcomm g g.2)
  have hrc₀ : r = (e.symm (-1) : R) := by
    rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e _).mp hrc) with h | h
    · exfalso
      have h1 : (⟨r, hr⟩ : R) = 1 := e.injective (by rw [h, map_one])
      have hr1 : r = 1 := congrArg Subtype.val h1
      exact ha.ne_one (by rw [← hra, hr1, map_one])
    · exact congrArg Subtype.val (e.injective (by rw [h, MulEquiv.apply_symm_apply]) :
        (⟨r, hr⟩ : R) = e.symm (-1))
  refine ⟨(e.symm (-1) : R), (e.symm (-1)).2, ?_, ?_, ?_, ?_, hP3⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, sl2_orderOf_neg_one hodd]
  · intro s hs hord
    have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨s, hs⟩).mp (by rwa [Subgroup.orderOf_mk])
    exact congrArg Subtype.val this
  · rw [← hra, hrc₀]
  · intro z hz hzk
    have hzc : z ∈ Subgroup.center K := hker hzk
    have hzr : (⟨z, hz⟩ : R) ∈ Subgroup.center R :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hzc (g : K))
    rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e _).mp hzr) with h | h
    · have h1 : (⟨z, hz⟩ : R) = 1 := e.injective (by rw [h, map_one])
      exact congrArg Subtype.val h1
    · exfalso
      have h1 : z = (e.symm (-1) : R) :=
        congrArg Subtype.val (e.injective (by rw [h, MulEquiv.apply_symm_apply]) :
          (⟨z, hz⟩ : R) = e.symm (-1))
      have hzr' : z = r := h1.trans hrc₀.symm
      exact ha.ne_one (by rw [← hra, ← hzr']; exact MonoidHom.mem_ker.mp hzk)

theorem conjSub_eq_of_map3 {φ : K →* X} (hker : φ.ker ≤ Subgroup.center K)
    (hcop : ∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) {R : Subgroup K} (hR : Pow3 R) {g : K}
    (h : conjSub (φ g) (R.map φ) = R.map φ) : conjSub g R = R := by
  have e : (conjSub g R).map φ = conjSub (φ g) (R.map φ) := by
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  exact eq_of_map_eq_of_pow3 φ hker hcop (hR.conjSub g) hR (e.trans h)

theorem commute_of_conjSub_map3 {φ : K →* X} (hker : φ.ker ≤ Subgroup.center K)
    (hcop : ∀ x ∈ φ.ker, ¬ 3 ∣ orderOf x) {R : Subgroup K} (hR : Pow3 R) {g i : K} (hi : i ∈ R)
    (hord : orderOf i = 2) (huniq : ∀ t ∈ R, orderOf t = 2 → t = i)
    (h : conjSub (φ g) (R.map φ) = R.map φ) : g * i = i * g := by
  have hN : conjSub g R = R := conjSub_eq_of_map3 hker hcop hR h
  have hmem : g * i * g⁻¹ ∈ R := by
    rw [← hN]
    exact ⟨i, hi, by simp⟩
  have hord' : orderOf (g * i * g⁻¹) = 2 := by
    rw [← hord]
    exact (MulAut.conj g).orderOf_eq i
  exact mul_inv_eq_iff_eq_mul.mp (huniq _ hmem hord')

end Lift

section Chain

theorem isPerfect_su3 {n : ℕ} (hn3 : 3 ≤ n) :
    Group.IsPerfect (Phan.Su (GaloisField 3 2) 3 1 n) := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 := card_galoisField_two_mul 3 1 le_rfl
  have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := n) hK hn3
    (by intro h; have := congrArg Prod.snd h; norm_num at this)).1
  have h2 := CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK n)).symm h
  exact h2.1

theorem unitaryBlockStandardPair_map3 {M Y : Type} [Group M] [Group Y] {W U V : Subgroup M}
    (h : UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W U V) (ψ : M →* Y)
    (hψ : ψ.ker ≤ Subgroup.center M) :
    UnitaryBlockStandardPair (GaloisField 3 2) 3 1 (W.map ψ) (U.map ψ) (V.map ψ) := by
  obtain ⟨θ, c, hW, hker, hUV⟩ := h
  have : Group.IsPerfect (Phan.Su (GaloisField 3 2) 3 1 3) := isPerfect_su3 le_rfl
  refine ⟨ψ.comp θ, c, ?_, Balance.ker_comp_le_center_of_perfect θ ψ hker hψ, ?_⟩
  · rw [MonoidHom.range_comp, hW]
  · rcases hUV with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem ChainSign3.map_of_commute {t : StatedLieTag} {n : ℕ} (h : ChainSign3 t n)
    (hfund : Generic.IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {X : Type} [Group X]
    (ψ : (Generic.modelUniv t n 3 1 Nat.prime_three).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (Generic.modelUniv t n 3 1 Nat.prime_three).K)
    {R₁ R₂ R₃ : Subgroup (Generic.modelUniv t n 3 1 Nat.prime_three).K}
    (h₁ : R₁ ∈ longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D)
    (h₂ : R₂ ∈ longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D)
    (h₃ : R₃ ∈ longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D)
    {c₁ c₂ c₃ : (Generic.modelUniv t n 3 1 Nat.prime_three).K} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hc₃ : c₃ ∈ R₃) (ho₁ : orderOf c₁ = 2) (ho₂ : orderOf c₂ = 2) (ho₃ : orderOf c₃ = 2)
    (h₁₂ : c₁ * c₂ = c₂ * c₁) (h₃₂ : c₃ * c₂ = c₂ * c₃) (h₁₃ : c₁ * c₃ = c₃ * c₁)
    (hR₁₃ : Commutes (R₁.map ψ) (R₃.map ψ)) (hne₁₂ : R₁.map ψ ≠ R₂.map ψ)
    (hne₃₂ : R₃.map ψ ≠ R₂.map ψ) (hnc₁₂ : ¬ Commutes (R₁.map ψ) (R₂.map ψ))
    (hnc₃₂ : ¬ Commutes (R₃.map ψ) (R₂.map ψ)) :
    ((∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map ψ) (R₂.map ψ)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₂.map ψ) (R₃.map ψ)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (R₁.map ψ) (R₂.map ψ)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (R₂.map ψ) (R₃.map ψ)) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hcop := ker_not_dvd_three_model hfund hadm ψ hker
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4
    (longestFundamental_subset t _ h₁)
  have hP₁ : Pow3 R₁ := pow_three_mem_commutator_of_equiv card_gf3 e₁
  have hmap : ∀ {A B : Subgroup (Generic.modelUniv t n 3 1 Nat.prime_three).K}, Commutes A B →
      Commutes (A.map ψ) (B.map ψ) := fun hAB => by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hAB x hx y hy]
  have hR₁₃' : Commutes R₁ R₃ := fun x hx y hy =>
    (commutes_of_map_commute_exponent3 ψ hker hcop (A := R₃) (L := R₁) hP₁
      (fun a ha l hl => (hR₁₃ _ ⟨l, hl, rfl⟩ _ ⟨a, ha, rfl⟩).symm) y hy x hx).symm
  rcases h (by norm_num) R₁ h₁ R₂ h₂ R₃ h₃ c₁ c₂ c₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ hR₁₃'
      (fun hh => hne₁₂ (by rw [hh])) (fun hh => hne₃₂ (by rw [hh]))
      (fun hh => hnc₁₂ (hmap hh)) (fun hh => hnc₃₂ (hmap hh)) with
    ⟨⟨_, hl₁⟩, ⟨_, hl₃⟩⟩ | ⟨⟨_, hu₁⟩, ⟨_, hu₃⟩⟩
  · exact Or.inl ⟨⟨_, Balance.linearBlockStandardPair_map_of_ker_le_center hl₁ ψ hker⟩,
      ⟨_, Balance.linearBlockStandardPair_map_of_ker_le_center hl₃ ψ hker⟩⟩
  · exact Or.inr ⟨⟨_, unitaryBlockStandardPair_map3 hu₁ ψ hker⟩,
      ⟨_, unitaryBlockStandardPair_map3 hu₃ ψ hker⟩⟩

theorem chainSign_of_lifts3 {t : StatedLieTag} {n : ℕ}
    (hcls : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus)
    (hadm : StatedLieAdmissible t n 3 1) {X : Type} [Group X]
    (φ : (Generic.modelUniv t n 3 1 Nat.prime_three).K →* X) (hker : φ.ker ≤ Subgroup.center _)
    {R₁ R₂ R₃ : Subgroup (Generic.modelUniv t n 3 1 Nat.prime_three).K}
    (h₁ : R₁ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D)
    (h₂ : R₂ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D)
    (h₃ : R₃ ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D)
    {a₁ a₂ a₃ : X} (ha₁ : IsUniqueInvolution (R₁.map φ) a₁)
    (ha₂ : IsUniqueInvolution (R₂.map φ) a₂) (ha₃ : IsUniqueInvolution (R₃.map φ) a₃)
    (hcen : ∀ y : X, a₁ * a₃ * y = y * (a₁ * a₃))
    (hnorm : conjSub a₂ (R₁.map φ) = R₁.map φ) (hR₁₃ : Commutes (R₁.map φ) (R₃.map φ))
    (hne₁₂ : R₁.map φ ≠ R₂.map φ) (hne₃₂ : R₃.map φ ≠ R₂.map φ)
    (hnc₁₂ : ¬ Commutes (R₁.map φ) (R₂.map φ)) (hnc₃₂ : ¬ Commutes (R₃.map φ) (R₂.map φ)) :
    ((∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R₂.map φ) (R₃.map φ)) ∨
      ((∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (R₁.map φ) (R₂.map φ)) ∧
        ∃ W, UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W (R₂.map φ) (R₃.map φ)) := by
  have hG2 : t ≠ .G2 := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hD4 : t ≠ .trialityD4 := by rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hfund : Generic.IsFundTag t := by
    rcases hcls with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hcop := ker_not_dvd_three_model hfund hadm φ hker
  have hSL2 : ∀ R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups hp2 hfund hadm hG2 hD4 hR
  have hlong : ∀ R ∈ Generic.fundamentalSubgroups t (Generic.modelUniv t n 3 1 Nat.prime_three).D,
      R ∈ longestFundamental (Generic.modelUniv t n 3 1 Nat.prime_three).D := fun R hR =>
    ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hR
  obtain ⟨c₁, hc₁, ho₁, hu₁, ha₁', -, hP₁⟩ :=
    exists_lift_central_involution3 φ hker hcop (hSL2 R₁ h₁).some ha₁
  obtain ⟨c₂, hc₂, ho₂, -, ha₂', -, -⟩ :=
    exists_lift_central_involution3 φ hker hcop (hSL2 R₂ h₂).some ha₂
  obtain ⟨c₃, hc₃, ho₃, -, ha₃', -, hP₃⟩ :=
    exists_lift_central_involution3 φ hker hcop (hSL2 R₃ h₃).some ha₃
  have hqs := ModelFacts.isQuasisimple_modelUniv t n 3 1 Nat.prime_three hfund hadm
  have : Group.IsPerfect (Generic.modelUniv t n 3 1 Nat.prime_three).K := ⟨hqs.1⟩
  have hR₁₃' : Commutes R₁ R₃ := fun x hx y hy =>
    (commutes_of_map_commute_exponent3 φ hker hcop (A := R₃) (L := R₁) hP₁
      (fun a ha l hl => (hR₁₃ _ ⟨l, hl, rfl⟩ _ ⟨a, ha, rfl⟩).symm) y hy x hx).symm
  have h₁₃ : c₁ * c₃ = c₃ * c₁ := hR₁₃' c₁ hc₁ c₃ hc₃
  have hz13 : c₁ * c₃ ∈ Subgroup.center (Generic.modelUniv t n 3 1 Nat.prime_three).K := by
    refine mem_center_of_comm_mem_center fun s => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have : φ (c₁ * c₃) = a₁ * a₃ := by rw [map_mul, ← ha₁', ← ha₃']
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hcen (φ s))
  have h₂₁ : c₂ * c₁ = c₁ * c₂ :=
    commute_of_conjSub_map3 hker hcop hP₁ hc₁ ho₁ hu₁ (by rw [← ha₂']; exact hnorm)
  have h₃₂ : c₃ * c₂ = c₂ * c₃ := by
    have hz := Subgroup.mem_center_iff.mp hz13 c₂
    have : c₁ * (c₂ * c₃) = c₁ * (c₃ * c₂) := by
      calc c₁ * (c₂ * c₃) = (c₁ * c₂) * c₃ := by rw [mul_assoc]
        _ = (c₂ * c₁) * c₃ := by rw [h₂₁]
        _ = c₂ * (c₁ * c₃) := by rw [mul_assoc]
        _ = (c₁ * c₃) * c₂ := hz
        _ = c₁ * (c₃ * c₂) := by rw [mul_assoc]
    exact (mul_left_cancel this).symm
  exact ChainSign3.map_of_commute (chainSign3_of_classical hcls hadm) hfund hadm hG2 hD4 φ hker
    (hlong R₁ h₁) (hlong R₂ h₂) (hlong R₃ h₃) hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₂₁.symm h₃₂ h₁₃ hR₁₃
    hne₁₂ hne₃₂ hnc₁₂ hnc₃₂

end Chain

end CFSG.ClassicalInvolution.Q3.Q3W

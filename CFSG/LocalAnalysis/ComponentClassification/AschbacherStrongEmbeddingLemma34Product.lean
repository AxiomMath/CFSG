module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Minimal

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AschbacherTheorem3 (IsDihedralTwoGroup IsSemidihedralTwoGroup)

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

omit [Finite G] in
theorem not_inf_centralizer_le_one (hc : ⁅A₁, A₂⁆ = ⊥) (h12 : ¬ A₁ ≤ A₂) {b : G}
    (hb : b ∈ A₁) : ¬ A₁ ⊓ Subgroup.centralizer ({b} : Set G) ≤ A₂ := by
  intro hle
  have hbA : b ∈ A₂ := hle ⟨hb, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  exact h12 fun x hx => hle ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_comm hc hx hbA).eq⟩

omit [Finite G] in
theorem not_inf_centralizer_le_two (hc : ⁅A₁, A₂⁆ = ⊥) (h21 : ¬ A₂ ≤ A₁) {b : G}
    (hb : b ∈ A₂) : ¬ A₂ ⊓ Subgroup.centralizer ({b} : Set G) ≤ A₁ := by
  have hc' : ⁅A₂, A₁⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hc
  exact not_inf_centralizer_le_one hc' h21 hb

omit [Finite G] in
theorem centralizer_conj_ne_top {y : G} (hy : y ∉ Subgroup.center G) (k : G) :
    Subgroup.centralizer ({k⁻¹ * y * k} : Set G) ≠ ⊤ := by
  intro htop
  apply hy
  rw [Subgroup.mem_center_iff]
  intro x
  have hx : k⁻¹ * x * k ∈ Subgroup.centralizer ({k⁻¹ * y * k} : Set G) :=
    htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have := congrArg (fun q => k * q * k⁻¹) hx
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at this
  exact this

omit [Finite G] in
theorem centralizer_le_of_conj {H : Subgroup G} {y k : G} (hk : k ∈ H)
    (hK : Subgroup.centralizer ({k⁻¹ * y * k} : Set G) ≤ H) :
    Subgroup.centralizer ({y} : Set G) ≤ H := by
  rw [centralizer_conj_eq] at hK
  intro x hx
  have hx' := hK (mem_rightConjugate_conj (g := k) hx)
  have := H.mul_mem (H.mul_mem hk hx') (H.inv_mem hk)
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using this

section Swap

variable {t : G}

omit [Finite G] in
theorem conj_mul_conj (htt : t * t = 1) (p q : G) :
    t * (p * q) * t = (t * p * t) * (t * q * t) := by
  calc t * (p * q) * t = t * p * (t * t) * q * t := by rw [htt, mul_one]; group
    _ = (t * p * t) * (t * q * t) := by group

@[expose] def swapTwistHom (hc : ⁅A₁, A₂⁆ = ⊥) (htt : t * t = 1)
    (hs₁ : rightConjugate A₁ t = A₂) : A₁ →* G where
  toFun b := (b : G) * (t * b * t)
  map_one' := by
    change 1 * (t * 1 * t) = 1
    rw [one_mul, mul_one, htt]
  map_mul' b d := by
    change (b : G) * d * (t * ((b : G) * d) * t) = (b : G) * (t * b * t) * ((d : G) * (t * d * t))
    have hdb : (d : G) * (t * b * t) = t * b * t * d :=
      (commute_of_comm hc d.2 (conj_mem_two_of_swap htt hs₁ b.2)).eq
    rw [conj_mul_conj htt]
    calc (b : G) * d * ((t * b * t) * (t * d * t))
        = (b : G) * ((d : G) * (t * b * t)) * (t * d * t) := by group
      _ = (b : G) * (t * b * t * d) * (t * d * t) := by rw [hdb]
      _ = (b : G) * (t * b * t) * ((d : G) * (t * d * t)) := by group

omit [Finite G] in
theorem swapTwistHom_apply (hc : ⁅A₁, A₂⁆ = ⊥) (htt : t * t = 1)
    (hs₁ : rightConjugate A₁ t = A₂) (b : A₁) :
    swapTwistHom hc htt hs₁ b = (b : G) * (t * b * t) := rfl

omit [Finite G] in
theorem swapTwistHom_range_le_centralizer (hc : ⁅A₁, A₂⁆ = ⊥) (htt : t * t = 1)
    (hs₁ : rightConjugate A₁ t = A₂) :
    (swapTwistHom hc htt hs₁).range ≤ Subgroup.centralizer ({t} : Set G) := by
  rintro _ ⟨b, rfl⟩
  rw [swapTwistHom_apply, Subgroup.mem_centralizer_singleton_iff]
  have h1 : (b : G) * (t * b * t) = t * b * t * b :=
    (commute_of_comm hc b.2 (conj_mem_two_of_swap htt hs₁ b.2)).eq
  calc (b : G) * (t * b * t) * t = (t * b * t * b) * t := by rw [h1]
    _ = t * ((b : G) * (t * b * t)) := by group

omit [Finite G] in
theorem swapTwistHom_injective (hc : ⁅A₁, A₂⁆ = ⊥) (htt : t * t = 1)
    (hs₁ : rightConjugate A₁ t = A₂) (hI : A₁ ⊓ A₂ = ⊥) :
    Function.Injective (swapTwistHom hc htt hs₁) := by
  rw [injective_iff_map_eq_one]
  intro b hb
  rw [swapTwistHom_apply] at hb
  have hinv : t * b * t = (b : G)⁻¹ := eq_inv_of_mul_eq_one_right hb
  have hbA : (b : G) ∈ A₁ ⊓ A₂ := by
    refine ⟨b.2, ?_⟩
    have := A₂.inv_mem (conj_mem_two_of_swap htt hs₁ b.2)
    rwa [hinv, inv_inv] at this
  rw [hI, Subgroup.mem_bot] at hbA
  exact Subtype.ext hbA

end Swap

namespace Minimal

variable (m : Minimal S A₁ A₂)
include m

theorem centralizer_le_of_mul {a₁ a₂ : G} (ha₁ : a₁ ∈ A₁) (ha₁2 : orderOf a₁ = 2)
    (ha₂ : a₂ ∈ A₂) (ha₂2 : orderOf a₂ = 2) (hcen : a₁ * a₂ ∉ Subgroup.center G) :
    Subgroup.centralizer ({a₁ * a₂} : Set G) ≤ overlapClosure A₁ A₂ := by
  have h := m.hyp
  have hA₁p : IsPGroup 2 A₁ := S.isPGroup'.to_le h.le_one
  have hA₂p : IsPGroup 2 A₂ := S.isPGroup'.to_le h.le_two
  set X := A₁ ⊓ Subgroup.centralizer ({a₁} : Set G) with hX
  have hX4 := four_le_card_inf_centralizer hA₁p h.rank_one ha₁ ha₁2
  have hXU : (X : Set G) ⊆ (A₁ : Set G) ∪ A₂ := fun x hx => Or.inl hx.1
  have hXS : X ≤ (S : Subgroup G) ⊓ Subgroup.centralizer ({a₁ * a₂} : Set G) := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨h.le_one hx.1, ?_⟩
    have hx1 : x * a₁ = a₁ * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
    have hx2 : x * a₂ = a₂ * x := (commute_of_comm h.comm hx.1 ha₂).eq
    rw [Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, hx1, mul_assoc, hx2,
      ← mul_assoc]
  obtain ⟨k, hk, ⟨P, hP⟩, hconj⟩ := h.exists_conj_sylow_inf m.sylow_le hXS
    (h.fixesOnly_of_card m.not_le₁₂ m.not_le₂₁ hXU hX4)
  have hcomm : Commute a₁ a₂ := commute_of_comm h.comm ha₁ ha₂
  have ha₁C : a₁ ∈ Subgroup.centralizer ({a₁ * a₂} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, mul_assoc a₁ a₂ a₁, ← hcomm.eq]
  have ha₂C : a₂ ∈ Subgroup.centralizer ({a₁ * a₂} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← mul_assoc, ← hcomm.eq]
  have hb₁ := hconj a₁ (Or.inl ha₁) ha₁C
  have hb₂ := hconj a₂ (Or.inr ha₂) ha₂C
  have hyk : k⁻¹ * (a₁ * a₂) * k = (k⁻¹ * a₁ * k) * (k⁻¹ * a₂ * k) := by group
  have hKne := centralizer_conj_ne_top hcen k
  have hord : ∀ {b : G}, orderOf b = 2 → orderOf (k⁻¹ * b * k) = 2 := fun hb => by
    rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]; exact hb
  have hy1 : k⁻¹ * (a₁ * a₂) * k ≠ 1 := by
    intro h1
    apply hcen
    have : a₁ * a₂ = 1 := by
      calc a₁ * a₂ = k * (k⁻¹ * (a₁ * a₂) * k) * k⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [this]
    exact Subgroup.one_mem _
  refine centralizer_le_of_conj hk ?_
  rcases hb₁ with hb₁ | hb₁ <;> rcases hb₂ with hb₂ | hb₂
  · exact m.centralizer_le (Or.inl (hyk ▸ A₁.mul_mem hb₁ hb₂)) hy1
  · exact h.centralizer_mul_le m.not_le₁₂ m.not_le₂₁ m.ih hyk hb₁ hb₂ hKne P hP
      (two_le_pRank_inf_centralizer hA₁p h.rank_one hb₁ (hord ha₁2))
      (two_le_pRank_inf_centralizer hA₂p h.rank_two hb₂ (hord ha₂2))
      (not_inf_centralizer_le_one h.comm m.not_le₁₂ hb₁)
      (not_inf_centralizer_le_two h.comm m.not_le₂₁ hb₂)
      (m.not_dihedralCase (K := Subgroup.centralizer ({k⁻¹ * (a₁ * a₂) * k} : Set G))
        (P : Subgroup _) (le_of_eq hP) (by
          rw [hyk, inf_centralizer_mul_left h.comm hb₂]
          exact not_inf_centralizer_le_one h.comm m.not_le₁₂ hb₁))
  · have hyk' : k⁻¹ * (a₁ * a₂) * k = (k⁻¹ * a₂ * k) * (k⁻¹ * a₁ * k) := by
      rw [hyk, (commute_of_comm h.comm hb₂ hb₁).eq]
    exact h.centralizer_mul_le m.not_le₁₂ m.not_le₂₁ m.ih hyk' hb₂ hb₁ hKne P hP
      (two_le_pRank_inf_centralizer hA₁p h.rank_one hb₂ (hord ha₂2))
      (two_le_pRank_inf_centralizer hA₂p h.rank_two hb₁ (hord ha₁2))
      (not_inf_centralizer_le_one h.comm m.not_le₁₂ hb₂)
      (not_inf_centralizer_le_two h.comm m.not_le₂₁ hb₁)
      (m.not_dihedralCase (K := Subgroup.centralizer ({k⁻¹ * (a₁ * a₂) * k} : Set G))
        (P : Subgroup _) (le_of_eq hP) (by
          rw [hyk', inf_centralizer_mul_left h.comm hb₁]
          exact not_inf_centralizer_le_one h.comm m.not_le₁₂ hb₂))
  · exact m.centralizer_le (Or.inr (hyk ▸ A₂.mul_mem hb₁ hb₂)) hy1

theorem fixesOnly_of_mul {a₁ a₂ : G} (ha₁ : a₁ ∈ A₁) (ha₁2 : orderOf a₁ = 2)
    (ha₂ : a₂ ∈ A₂) (ha₂2 : orderOf a₂ = 2) (hcen : a₁ * a₂ ∉ Subgroup.center G) :
    FixesOnly (overlapClosure A₁ A₂) (Subgroup.zpowers (a₁ * a₂)) := by
  have h := m.hyp
  set H := overlapClosure A₁ A₂ with hHdef
  have hcomm : Commute a₁ a₂ := commute_of_comm h.comm ha₁ ha₂
  have haa₁ : a₁ * a₁ = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp ha₁2).1
  have haa₂ : a₂ * a₂ = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp ha₂2).1
  have huu : a₁ * a₂ * (a₁ * a₂) = 1 := by
    rw [mul_assoc, hcomm.symm.left_comm, ← mul_assoc, haa₁, one_mul, haa₂]
  have hu1 : a₁ * a₂ ≠ 1 := fun h1 => hcen (h1 ▸ Subgroup.one_mem _)
  have hCu := m.centralizer_le_of_mul ha₁ ha₁2 ha₂ ha₂2 hcen
  rw [fixesOnly_zpowers_iff]
  intro g₀ hg₀
  by_contra hg₀H
  have hp : IsPGroup 2 (Subgroup.zpowers (g₀⁻¹ * (a₁ * a₂) * g₀)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hord : orderOf (g₀⁻¹ * (a₁ * a₂) * g₀) = 2 := by
      rw [← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]
      exact orderOf_eq_prime (by rw [sq]; exact huu) hu1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨k, hk, hkS⟩ := exists_conj_le_sylow m.sylow_le (Subgroup.zpowers_le.mpr hg₀) hp
  set g := g₀ * k with hgdef
  have hgH : g ∉ H := fun hg => hg₀H (by
    have := H.mul_mem hg (H.inv_mem hk)
    rwa [hgdef, mul_inv_cancel_right] at this)
  set t := g⁻¹ * (a₁ * a₂) * g with htdef
  have htS : t ∈ (S : Subgroup G) := by
    rw [htdef, hgdef, show (g₀ * k)⁻¹ * (a₁ * a₂) * (g₀ * k) =
      k⁻¹ * (g₀⁻¹ * (a₁ * a₂) * g₀) * k by group]
    exact hkS _ (Subgroup.mem_zpowers _)
  have htt : t * t = 1 := by
    rw [htdef, show g⁻¹ * (a₁ * a₂) * g * (g⁻¹ * (a₁ * a₂) * g) =
      g⁻¹ * (a₁ * a₂ * (a₁ * a₂)) * g by group, huu]
    group
  have hCt : Subgroup.centralizer ({t} : Set G) ≤ rightConjugate H g := by
    rw [htdef, centralizer_conj_eq]
    exact Subgroup.map_mono hCu
  have hfix : ∀ {b : G}, b ∈ (A₁ : Set G) ∪ A₂ → Commute t b → b = 1 := by
    intro b hb hbt
    by_contra hb1
    exact hgH (m.mem_of_mem_rightConjugate hb hb1
      (hCt (Subgroup.mem_centralizer_singleton_iff.mpr hbt.eq.symm)))
  have hnorm : t ∉ Subgroup.normalizer (A₁ : Set G) := by
    intro htN
    obtain ⟨b, hb, hb1, hbt⟩ :=
      exists_commute_of_mem_normalizer S.isPGroup' h.le_one h.ne_bot_one htS htN
    exact hb1 (hfix (Or.inl hb) hbt)
  obtain ⟨hs₁, hs₂⟩ : rightConjugate A₁ t = A₂ ∧ rightConjugate A₂ t = A₁ := by
    rcases h.sylow_le_pairStabilizer m.not_le₁₂ m.not_le₂₁ htS with ⟨h₁, -⟩ | hsw
    · exact absurd ((rightConjugate_eq_self_iff _ _).mp h₁) hnorm
    · exact hsw
  have hI : A₁ ⊓ A₂ = ⊥ := by
    by_contra hI
    have hIS : A₁ ⊓ A₂ ≤ (S : Subgroup G) := inf_le_left.trans h.le_one
    have htN : t ∈ Subgroup.normalizer ((A₁ ⊓ A₂ : Subgroup G) : Set G) := by
      rw [← rightConjugate_eq_self_iff, rightConjugate_inf_eq, hs₁, hs₂, inf_comm]
    obtain ⟨b, hb, hb1, hbt⟩ := exists_commute_of_mem_normalizer S.isPGroup' hIS hI htS htN
    exact hb1 (hfix (Or.inl hb.1) hbt)
  set R := (swapTwistHom h.comm htt hs₁).range with hRdef
  have hRC := swapTwistHom_range_le_centralizer h.comm htt hs₁
  have hRS : R ≤ (S : Subgroup G) := by
    rintro _ ⟨b, rfl⟩
    rw [swapTwistHom_apply]
    exact Subgroup.mul_mem _ (h.le_one b.2) (h.le_two (conj_mem_two_of_swap htt hs₁ b.2))
  have hRp : IsPGroup 2 R := S.isPGroup'.to_le hRS
  have hRcard : Nat.card R = Nat.card A₁ := by
    rw [hRdef, MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (swapTwistHom_injective h.comm htt hs₁ hI),
      Subgroup.card_top]
  have hTH : (conjSylow S g : Subgroup G) ≤ rightConjugate H g := by
    rw [coe_conjSylow]
    exact Subgroup.map_mono m.sylow_le
  obtain ⟨c, hc, hcR⟩ := exists_conj_le_sylow hTH (hRC.trans hCt) hRp
  set g' := g * c⁻¹ with hg'def
  have hcH : g * c * g⁻¹ ∈ H := (mem_rightConjugate_iff _ _ _).mp hc
  have hg'H : g' ∉ H := fun hg' => hgH (by
    have := H.mul_mem hcH hg'
    rwa [hg'def, show g * c * g⁻¹ * (g * c⁻¹) = g by group] at this)
  have hRT : R ≤ rightConjugate (S : Subgroup G) g' := by
    intro x hx
    rw [mem_rightConjugate_iff]
    have h1 := hcR x hx
    rw [coe_conjSylow, mem_rightConjugate_iff] at h1
    rw [hg'def, show g * c⁻¹ * x * (g * c⁻¹)⁻¹ = g * (c⁻¹ * x * c) * g⁻¹ by group]
    exact h1
  have hB := h.conj g'
  have hB12 : ¬ rightConjugate A₁ g' ≤ rightConjugate A₂ g' := by
    rw [rightConjugate_le_rightConjugate_iff]; exact m.not_le₁₂
  have hB21 : ¬ rightConjugate A₂ g' ≤ rightConjugate A₁ g' := by
    rw [rightConjugate_le_rightConjugate_iff]; exact m.not_le₂₁
  have hRstab : R ≤ pairStabilizer (rightConjugate A₁ g') (rightConjugate A₂ g') :=
    hRT.trans (by rw [← coe_conjSylow]; exact hB.sylow_le_pairStabilizer hB12 hB21)
  obtain ⟨y₀, hy₀R, hy₀1, hy₀N⟩ := exists_mem_normalizer_of_four_le hRstab
    (by rw [hRcard]; exact four_le_card_of_two_le_pRank h.rank_one)
  set V := R ⊓ Subgroup.normalizer (rightConjugate A₁ g' : Set G) with hVdef
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hy₀1
    have : y₀ ∈ V := ⟨hy₀R, hy₀N⟩
    rwa [hbot, Subgroup.mem_bot] at this
  obtain ⟨y, hyV, hy2, -⟩ := exists_central_involution (hRp.to_le inf_le_left) hVne
  obtain ⟨b, hb⟩ := hyV.1
  rw [swapTwistHom_apply] at hb
  have hyy : y * y = 1 := by rw [← sq]; exact (orderOf_eq_prime_iff.mp hy2).1
  have hy1 : y ≠ 1 := (orderOf_eq_prime_iff.mp hy2).2
  have hbb : (b : G) * b = 1 := by
    have hinj := swapTwistHom_injective h.comm htt hs₁ hI
    have h1 : swapTwistHom h.comm htt hs₁ (b * b) = 1 := by
      rw [map_mul, swapTwistHom_apply, hb, hyy]
    have := hinj (h1.trans (map_one _).symm)
    exact congrArg Subtype.val this
  have hb1 : (b : G) ≠ 1 := by
    intro h1
    apply hy1
    rw [← hb, h1, one_mul, mul_one, htt]
  have hb2 : orderOf (b : G) = 2 := orderOf_eq_prime (by rw [sq]; exact hbb) hb1
  have htbA : t * b * t ∈ A₂ := conj_mem_two_of_swap htt hs₁ b.2
  have htb2 : orderOf (t * b * t) = 2 := by
    have : t * b * t = t⁻¹ * b * t := by rw [inv_eq_of_mul_eq_one_left htt]
    rw [this, ← MulAut.conj_inv_apply, MulEquiv.orderOf_eq]
    exact hb2
  have hyc : y ∉ Subgroup.center G := by
    intro hyc
    refine m.false_of_central_of_inf_eq_bot hI hyc hyy (fun hyA => ?_) (fun hyA => ?_)
    · have : t * b * t ∈ A₁ ⊓ A₂ := by
        refine ⟨?_, htbA⟩
        have := A₁.mul_mem (A₁.inv_mem b.2) hyA
        rwa [← hb, inv_mul_cancel_left] at this
      rw [hI, Subgroup.mem_bot] at this
      apply hb1
      calc (b : G) = t * (t * b * t) * t := by
            rw [show t * (t * b * t) * t = (t * t) * b * (t * t) by group, htt, one_mul,
              mul_one]
        _ = 1 := by rw [this, mul_one, htt]
    · have : (b : G) ∈ A₁ ⊓ A₂ := by
        refine ⟨b.2, ?_⟩
        have := A₂.mul_mem hyA (A₂.inv_mem htbA)
        rwa [← hb, mul_inv_cancel_right] at this
      rw [hI, Subgroup.mem_bot] at this
      exact hb1 this
  have hCy : Subgroup.centralizer ({y} : Set G) ≤ H := by
    rw [← hb] at hyc ⊢
    exact m.centralizer_le_of_mul b.2 hb2 htbA htb2 hyc
  have hBT : rightConjugate A₁ g' ≤ rightConjugate (S : Subgroup G) g' :=
    Subgroup.map_mono h.le_one
  have hBne : rightConjugate A₁ g' ≠ ⊥ := fun hbot => h.ne_bot_one
    (Subgroup.eq_bot_of_card_eq _ (by rw [← rightConjugate_card A₁ g', hbot, Subgroup.card_bot]))
  have hTp : IsPGroup 2 (rightConjugate (S : Subgroup G) g') := by
    rw [← coe_conjSylow]; exact (conjSylow S g').isPGroup'
  obtain ⟨b', hb'B, hb'1, hb'y⟩ :=
    exists_commute_of_mem_normalizer hTp hBT hBne (hRT hyV.1) hyV.2
  have hb'H : b' ∈ H := hCy (Subgroup.mem_centralizer_singleton_iff.mpr hb'y.eq.symm)
  have hb₀A : g' * b' * g'⁻¹ ∈ A₁ := (mem_rightConjugate_iff _ _ _).mp hb'B
  have hb₀1 : g' * b' * g'⁻¹ ≠ 1 := by
    intro h1
    apply hb'1
    calc b' = g'⁻¹ * (g' * b' * g'⁻¹) * g' := by group
      _ = 1 := by rw [h1]; group
  apply hg'H
  refine (fixesOnly_zpowers_iff.mp (m.fixesOnly (Or.inl hb₀A) hb₀1)) g' ?_
  rw [show g'⁻¹ * (g' * b' * g'⁻¹) * g' = b' by group]
  exact hb'H

end Minimal

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding

module

public import CFSG.GH74.Uniqueness.Section124
public import CFSG.GH74.Uniqueness.Section128Index
public import CFSG.GH74.Uniqueness.Section1212
public import CFSG.GH74.Uniqueness.Section1213Meta

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

section Basic

omit [Finite X] in
theorem A5.isCentralInvolution_conj {s : X} (hs : IsCentralInvolution s) (g : X) :
    IsCentralInvolution (g * s * g⁻¹) := by
  obtain ⟨hs2, T, hsT, hcomm⟩ := hs
  refine ⟨by rw [A5.orderOf_conj, hs2], g • T, (mem_smul_sylow_iff T g _).mpr ⟨s, hsT, rfl⟩,
    fun y hy => ?_⟩
  obtain ⟨y₀, hy₀, rfl⟩ := (mem_smul_sylow_iff T g y).mp hy
  have h := hcomm y₀ hy₀
  calc g * y₀ * g⁻¹ * (g * s * g⁻¹) = g * (y₀ * s) * g⁻¹ := by group
    _ = g * (s * y₀) * g⁻¹ := by rw [h]
    _ = g * s * g⁻¹ * (g * y₀ * g⁻¹) := by group

omit [Finite X] in
theorem A5.eq_conjugate_inv {γ : Subgroup X} {g : X} {B : Subgroup X} (h : conjugate γ g = B) :
    γ = conjugate B g⁻¹ := by
  rw [← h, conjugate_conjugate, mul_inv_cancel, conjugate_one]

theorem A5.factorization_card_of_benderType
    {K : Type*} [Group K] [Finite K] {n i e : ℕ}
    (h : Bender.BenderType K n i e) : (Nat.card K).factorization 2 = n * i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  have h1 : 2 ^ (Nat.card K).factorization 2 = 2 ^ (n * i) := by
    rw [← Q.card_eq_multiplicity, hc.card_eq, pow_mul]
  exact Nat.pow_right_injective le_rfl h1

theorem A5.factorization_card_of_benderSub
    {F : Subgroup X} {n i e : ℕ}
    (hB : BenderSub Z M F n i e) : (Nat.card F).factorization 2 = n * i := by
  have hodd := A2.odd_card_center_of_benderSub hB
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥F)
  have hq : Nat.card (↥F ⧸ center ↥F) ≠ 0 := Nat.card_pos.ne'
  rw [hc, Nat.factorization_mul hq hodd.pos.ne', Finsupp.add_apply,
    A5.factorization_card_of_benderType hB.bender,
    Nat.factorization_eq_zero_of_not_dvd
      (fun hd => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd)), add_zero]

end Basic

section NotCentral

variable {c : Ctx12 Z M} {n i : ℕ}

theorem A5.not_isCentralInvolution
    (S : ZDSetup X Z M) (h1210 : Lemma1210Stmt Z M)
    (hL : LData c n i) {u : X} (hu : u ∈ c.D) (hu2 : orderOf u = 2) :
    ¬ IsCentralInvolution u := by
  rintro ⟨-, T, -, hTcomm⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup X := centralizer ({u} : Set X) with hC
  set B : Subgroup X := C ⊓ c.D with hB
  have hTC : (T : Subgroup X) ≤ C := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hTcomm y hy)
  have hdec := (S.lemma124 c n i hL u hu hu2).2.2.2.2
  have hLuC : cenHull Z u ≤ C := Cor713.zHull_le C
  have hBN : B ≤ normalizer (cenHull Z u : Set X) := fun b hb =>
    le_normalizer_zHull S.invariant C (mem_inf.mp hb).1
  have hsup : cenHull Z u ⊔ B = C := by
    refine le_antisymm (sup_le hLuC inf_le_left) (fun x hx => ?_)
    have hx' : x ∈ (cenHull Z u : Set X) * (B : Set X) := by
      rw [← hdec]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx'
    exact mul_mem_sup ha hb
  have hcard := Sec128.card_sup_mul_card_inf_of_le_normalizer hBN
  rw [hsup] at hcard
  have hd1 : Nat.card C ∣ Nat.card (cenHull Z u) * Nat.card B := ⟨_, hcard.symm⟩
  have hdvd : Nat.card C ∣ Nat.card (cenHull Z u) * Nat.card c.D :=
    hd1.trans (mul_dvd_mul_left _ (Subgroup.card_dvd_of_le inf_le_right))
  have hT : Nat.card T ∣ Nat.card C := Subgroup.card_dvd_of_le hTC
  rw [T.card_eq_multiplicity] at hT
  have hne : Nat.card (cenHull Z u) * Nat.card c.D ≠ 0 :=
    mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'
  have h2 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp (hT.trans hdvd)
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at h2
  have hn := hL.hn
  rcases h1210 c n i hL with ⟨hi, -, hall, hX⟩ | ⟨hi, -, hall, hX⟩ | ⟨-, -, hall, hX⟩
  · rw [(hall u hu hu2).1, A5.factorization_card_of_benderType hL.bender, hi] at h2
    omega
  · rw [(hall u hu hu2).1, A5.factorization_card_of_benderType hL.bender, hi] at h2
    omega
  · obtain ⟨e, he⟩ := (hall u hu hu2).2.1
    rw [A5.factorization_card_of_benderSub he] at h2
    omega

end NotCentral

section Fixed

theorem A5.exists_fixed_of_involution (S : ZDSetup X Z M) {s : X} (hs : orderOf s = 2) :
    ∃ γ ∈ omega M, conjugate γ s = γ := by
  obtain ⟨T, hT⟩ := S.prodDisc.exists_sylow_normalizer_le S.invariant
  have hTM : (T : Subgroup X) ≤ M := fun x hx => hT (Subgroup.le_normalizer hx)
  have hsp : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨T', hT'⟩ := hsp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X T' T
  have hs' : s ∈ (T' : Subgroup X) := hT' (Subgroup.mem_zpowers s)
  have hgs : g * s * g⁻¹ ∈ ((g • T' : Sylow 2 X) : Subgroup X) :=
    (mem_smul_sylow_iff T' g _).mpr ⟨s, hs', rfl⟩
  rw [hg] at hgs
  refine ⟨conjugate M g, ⟨g, rfl⟩, ?_⟩
  rw [S.prodDisc.conjugate_eq_iff_mem ⟨g, rfl⟩, mem_conjugate_iff]
  exact hTM hgs

theorem A5.exists_conj_mem_D
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {s : X} (hs : orderOf s = 2)
    {γ δ : Subgroup X} (hγ : γ ∈ omega M) (hδ : δ ∈ omega M) (hγδ : γ ≠ δ)
    (hsγ : conjugate γ s = γ) (hsδ : conjugate δ s = δ) :
    ∃ u ∈ c.D, orderOf u = 2 ∧ IsConj s u := by
  have hMt : M ≠ conjugate M c.t :=
    fun h => ((S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM) h.symm
  obtain ⟨g, hg1, hg2⟩ := S.theorem4.1 γ hγ δ hδ hγδ M (self_mem_omega M) (conjugate M c.t)
    ⟨c.t, rfl⟩ hMt
  have hfix : ∀ {ε B : Subgroup X}, conjugate ε g = B → conjugate ε s = ε →
      conjugate B (g⁻¹ * s * g) = B := by
    intro ε B hεB hεs
    rw [← hεB, conjugate_conjugate, show g * (g⁻¹ * s * g) = s * g by group,
      ← conjugate_conjugate, hεs]
  refine ⟨g⁻¹ * s * g, mem_inf.mpr ⟨?_, ?_⟩, ?_, isConj_iff.mpr ⟨g⁻¹, by group⟩⟩
  · exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mp (hfix hg1 hsγ)
  · exact (S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mp (hfix hg2 hsδ)
  · have := A5.orderOf_conj g⁻¹ s
    rwa [inv_inv, hs] at this

end Fixed

section Main

variable {c : Ctx12 Z M} {n i : ℕ}

theorem A5.mem_normalizer_of_swap (S : ZDSetup X Z M) (hL : LData c n i) {s : X}
    (hs1 : conjugate M s = conjugate M c.t) (hs2 : conjugate (conjugate M c.t) s = M) :
    s * c.t ∈ c.D ∧ s ∈ normalizer (c.L : Set X) := by
  have ht2 : c.t * c.t = 1 := S.invariant.mul_self_eq_one c.ht
  have hd1 : s * c.t ∈ M := by
    rw [← S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M), ← conjugate_conjugate, hs1,
      conjugate_conjugate, ht2, conjugate_one]
  have hd2 : s * c.t ∈ conjugate M c.t := by
    rw [← S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩, ← conjugate_conjugate, hs2]
  have hdD : s * c.t ∈ c.D := mem_inf.mpr ⟨hd1, hd2⟩
  refine ⟨hdD, ?_⟩
  have hDN : s * c.t ∈ normalizer (c.L : Set X) := by
    have h1 : s * c.t ∈ (c.L : Set X) * (c.D : Set X) :=
      Set.mem_mul.mpr ⟨1, c.L.one_mem, s * c.t, hdD, one_mul _⟩
    rw [← hL.normalizer_eq] at h1
    exact h1
  have htN : c.t ∈ normalizer (c.L : Set X) := Subgroup.le_normalizer c.t_mem_L
  have h2 := mul_mem hDN htN
  rwa [mul_assoc, ht2, mul_one] at h2

theorem A5.mem_of_swap
    (S : ZDSetup X Z M) (h127 : Lemma127Stmt Z M) (hL : LData c n i) {s : X}
    (hs : orderOf s = 2) (huniq : ∃! γ : Subgroup X, γ ∈ omega M ∧ conjugate γ s = γ)
    (hs1 : conjugate M s = conjugate M c.t) (hs2 : conjugate (conjugate M c.t) s = M) :
    s ∈ Z := by
  obtain ⟨-, hsN⟩ := A5.mem_normalizer_of_swap S hL hs1 hs2
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, pow_two] at this
  obtain ⟨γ₀, ⟨hγ₀, hsγ₀⟩, hγ₀u⟩ := huniq
  have hMt : conjugate M c.t ≠ M := (S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM
  have hone : ∀ γ δ : Subgroup X, γ ∈ omega M → δ ∈ omega M → conjugate γ s = γ →
      conjugate δ s = δ → γ = δ := fun γ δ hγ hδ hγs hδs =>
    (hγ₀u γ ⟨hγ, hγs⟩).trans (hγ₀u δ ⟨hδ, hδs⟩).symm
  have hαα : A2.conjAut c.L hsN * A2.conjAut c.L hsN = 1 := A2.conjAut_mul_self c.L hsN hss
  by_cases hinn : ∃ g : ↥c.L, ∀ x : ↥c.L, A2.conjAut c.L hsN x = g * x * g⁻¹
  · obtain ⟨g, hg⟩ := hinn
    have hgs : ∀ y ∈ c.L, s * y * s⁻¹ = (g : X) * y * (g : X)⁻¹ := fun y hy =>
      congrArg Subtype.val (hg ⟨y, hy⟩)
    obtain ⟨j, hj⟩ : ∃ j : X, j = (g : X)⁻¹ * s := ⟨_, rfl⟩
    have hjC : j ∈ centralizer (c.L : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hgs y hy
      rw [hj]
      calc y * ((g : X)⁻¹ * s) = (g : X)⁻¹ * ((g : X) * y * (g : X)⁻¹) * s := by group
        _ = (g : X)⁻¹ * (s * y * s⁻¹) * s := by rw [h1]
        _ = (g : X)⁻¹ * s * y := by group
    have hjD : j ∈ c.D := hL.centralizer_le hjC
    have hgj : (g : X) * j = j * g := (Subgroup.mem_centralizer_iff.mp hjC) g g.2
    have hsgj : s = (g : X) * j := by rw [hj]; group
    have h1 : (g : X) * g * (j * j) = 1 := by
      calc (g : X) * g * (j * j) = (g : X) * (g * j) * j := by group
        _ = (g : X) * (j * g) * j := by rw [hgj]
        _ = ((g : X) * j) * ((g : X) * j) := by group
        _ = s * s := by rw [← hsgj]
        _ = 1 := hss
    have hg2 : (g : X) * g = 1 := by
      have h2 : (g : X) * g = (j * j)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hmemC : (g : X) * g ∈ centralizer (c.L : Set X) := by
        rw [h2]
        exact (centralizer (c.L : Set X)).inv_mem ((centralizer (c.L : Set X)).mul_mem hjC hjC)
      have hcen : g * g ∈ center ↥c.L := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hmemC y y.2
      rw [hL.center_eq_bot, Subgroup.mem_bot] at hcen
      exact congrArg Subtype.val hcen
    have hj2 : j * j = 1 := by rwa [hg2, one_mul] at h1
    by_cases hj1 : j = 1
    · have hsg : s = (g : X) := by rw [hsgj, hj1, mul_one]
      have hsL : s ∈ c.L := by rw [hsg]; exact g.2
      exact hL.invol s hsL hs
    · exfalso
      have hjM : j ∈ M := (mem_inf.mp hjD).1
      have hjMt : j ∈ conjugate M c.t := (mem_inf.mp hjD).2
      by_cases hg1 : (g : X) = 1
      · apply hMt
        rw [← hs1, hsgj, hg1, one_mul]
        exact (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hjM
      · have hgo : orderOf (g : X) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
        have hgZ : (g : X) ∈ Z := hL.invol g g.2 hgo
        have hzg : IsConj c.z (g : X) := S.prodDisc.isConj_of_mem S.invariant c.hz hgZ
        have hjo : orderOf j = 2 := orderOf_eq_prime (by rw [pow_two]; exact hj2) hj1
        have hconj := (h127 c n i hL j hjD hjo).2 j g (IsConj.refl j) hzg hgj.symm
        rw [← hgj, ← hsgj] at hconj
        obtain ⟨k, hk⟩ := isConj_iff.mp hconj
        have hfix : ∀ B : Subgroup X, conjugate B j = B →
            conjugate (conjugate B k⁻¹) s = conjugate B k⁻¹ := by
          intro B hB
          rw [← hk, conjugate_conjugate, show k⁻¹ * (k * j * k⁻¹) = j * k⁻¹ by group,
            ← conjugate_conjugate, hB]
        have h1 := hfix M ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr hjM)
        have h2 := hfix (conjugate M c.t)
          ((S.prodDisc.conjugate_eq_iff_mem ⟨c.t, rfl⟩).mpr hjMt)
        have h3 := hone _ _ (conjugate_mem_omega (self_mem_omega M) k⁻¹)
          (conjugate_mem_omega ⟨c.t, rfl⟩ k⁻¹) h1 h2
        exact hMt (conjugate_injective k⁻¹ h3).symm
  · exfalso
    rcases hL.hi with hi1 | hi2
    · have hB : Bender.BenderType ↥c.L n 1 1 := hi1 ▸ hL.bender
      obtain ⟨y₁, y₂, h₁, h₂, hf₁, hf₂, hne⟩ :=
        hB.exists_fixed_noncommuting_involutions_linear _ hαα hinn
      have hkey : ∀ y : ↥c.L, y * y = 1 → A2.conjAut c.L hsN y = y → y ≠ 1 →
          (y : X) ∈ Z ∧ (y : X) ∈ γ₀ := by
        intro y hy hαy hy1
        have hyX1 : (y : X) ≠ 1 := fun h => hy1 (Subtype.ext h)
        have hyo : orderOf (y : X) = 2 :=
          orderOf_eq_prime (by rw [pow_two]; exact congrArg Subtype.val hy) hyX1
        have hsy : s * (y : X) = (y : X) * s := by
          have h1 : s * (y : X) * s⁻¹ = y := congrArg Subtype.val hαy
          calc s * (y : X) = s * (y : X) * s⁻¹ * s := by group
            _ = (y : X) * s := by rw [h1]
        refine ⟨hL.invol y y.2 hyo, ?_⟩
        have hfixy : conjugate (conjugate γ₀ (y : X)) s = conjugate γ₀ (y : X) := by
          rw [conjugate_conjugate, ← hsy, ← conjugate_conjugate, hsγ₀]
        have := hone _ _ (conjugate_mem_omega hγ₀ _) hγ₀ hfixy hsγ₀
        exact (S.prodDisc.conjugate_eq_iff_mem hγ₀).mp this
      have hy₁1 : y₁ ≠ 1 := by
        rintro rfl
        exact hne (by simp)
      have hy₂1 : y₂ ≠ 1 := by
        rintro rfl
        exact hne (by simp)
      obtain ⟨hz₁, hm₁⟩ := hkey y₁ h₁ hf₁ hy₁1
      obtain ⟨hz₂, hm₂⟩ := hkey y₂ h₂ hf₂ hy₂1
      obtain ⟨a, rfl⟩ := hγ₀
      have hmem : (y₁ : X) * y₂ ∈ zHull Z (conjugate M a) :=
        mul_mem (subset_closure ⟨hz₁, hm₁⟩) (subset_closure ⟨hz₂, hm₂⟩)
      have hsq := sq_eq_one_of_mem_zHull_conjugate S.invariant hL.m_abelian.2 a hmem
      have e1 : (y₁ : X)⁻¹ = y₁ := inv_eq_of_mul_eq_one_right (congrArg Subtype.val h₁)
      have e2 : (y₂ : X)⁻¹ = y₂ := inv_eq_of_mul_eq_one_right (congrArg Subtype.val h₂)
      have h3 : (y₁ : X) * y₂ = ((y₁ : X) * y₂)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← pow_two]; exact hsq)
      rw [mul_inv_rev, e1, e2] at h3
      exact hne (Subtype.ext h3)
    · have hB : Bender.BenderType ↥c.L n 2 1 := hi2 ▸ hL.bender
      exact hinn (hB.not_outer_involution_suzuki _ hαα)

theorem A5.mem_of_unique_fixed
    (S : ZDSetup X Z M) (h127 : Lemma127Stmt Z M) (hL : LData c n i)
    {s : X} (hs : orderOf s = 2) (huniq : ∃! γ : Subgroup X, γ ∈ omega M ∧ conjugate γ s = γ) :
    s ∈ Z := by
  have hss : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hs, pow_two] at this
  obtain ⟨γ₀, ⟨hγ₀, hsγ₀⟩, hγ₀u⟩ := huniq
  have hMt : M ≠ conjugate M c.t :=
    fun h => ((S.prodDisc.conjugate_ne_iff (self_mem_omega M)).mpr c.htM) h.symm
  obtain ⟨δ, hδ, hδγ⟩ : ∃ δ ∈ omega M, δ ≠ γ₀ := by
    by_cases h : M = γ₀
    · exact ⟨conjugate M c.t, ⟨c.t, rfl⟩, fun h' => hMt (h.trans h'.symm)⟩
    · exact ⟨M, self_mem_omega M, h⟩
  have hδs : conjugate δ s ≠ δ := fun h => hδγ (hγ₀u δ ⟨hδ, h⟩)
  obtain ⟨g, hg1, hg2⟩ := S.theorem4.1 δ hδ (conjugate δ s) (conjugate_mem_omega hδ s)
    (Ne.symm hδs) M (self_mem_omega M) (conjugate M c.t) ⟨c.t, rfl⟩ hMt
  have hconj : ∀ ε : Subgroup X,
      conjugate ε (g⁻¹ * s * g) = conjugate (conjugate (conjugate ε g⁻¹) s) g := by
    intro ε
    simp only [conjugate_conjugate, mul_assoc]
  have hδδ : conjugate (conjugate δ s) s = δ := by
    rw [conjugate_conjugate, hss, conjugate_one]
  have hs'1 : conjugate M (g⁻¹ * s * g) = conjugate M c.t := by
    rw [hconj, ← A5.eq_conjugate_inv hg1, hg2]
  have hs'2 : conjugate (conjugate M c.t) (g⁻¹ * s * g) = M := by
    rw [hconj, ← A5.eq_conjugate_inv hg2, hδδ, hg1]
  have hs'o : orderOf (g⁻¹ * s * g) = 2 := by
    have := A5.orderOf_conj g⁻¹ s
    rwa [inv_inv, hs] at this
  have hs'u : ∃! γ : Subgroup X, γ ∈ omega M ∧ conjugate γ (g⁻¹ * s * g) = γ := by
    refine ⟨conjugate γ₀ g, ⟨conjugate_mem_omega hγ₀ g, ?_⟩, ?_⟩
    · rw [hconj, conjugate_conjugate_inv, hsγ₀]
    · rintro γ ⟨hγ, hγs⟩
      have h1 : conjugate (conjugate γ g⁻¹) s = conjugate γ g⁻¹ := by
        have h2 := congrArg (fun B => conjugate B g⁻¹) hγs
        rwa [hconj, conjugate_conjugate_inv] at h2
      have h2 := hγ₀u _ ⟨conjugate_mem_omega hγ g⁻¹, h1⟩
      rw [← h2, conjugate_inv_conjugate]
  have hmem := A5.mem_of_swap S h127 hL hs'o hs'u hs'1 hs'2
  have := S.invariant.2 _ hmem g⁻¹
  rwa [inv_inv, show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at this

end Main

theorem ZDSetup.lemma1211
    (S : ZDSetup X Z M) (h1210 : Lemma1210Stmt Z M)
    (h127 : Lemma127Stmt Z M) : Lemma1211Stmt Z M := by
  intro c n i hL
  have htwo : ∀ s : X, orderOf s = 2 → s ∉ Z → ∃ γ δ : Subgroup X, γ ∈ omega M ∧
      δ ∈ omega M ∧ γ ≠ δ ∧ conjugate γ s = γ ∧ conjugate δ s = δ := by
    intro s hs hsZ
    obtain ⟨γ, hγ, hsγ⟩ := A5.exists_fixed_of_involution S hs
    by_contra hcon
    push Not at hcon
    apply hsZ
    refine A5.mem_of_unique_fixed S h127 hL hs ⟨γ, ⟨hγ, hsγ⟩, ?_⟩
    rintro δ ⟨hδ, hsδ⟩
    by_contra hne
    exact hcon γ δ hγ hδ (Ne.symm hne) hsγ hsδ
  have ha : ∀ s : X, orderOf s = 2 → (IsCentralInvolution s ↔ s ∈ Z) := by
    intro s hs
    refine ⟨fun hc => ?_, fun hz => S.isCentralInvolution hz⟩
    by_contra hsZ
    obtain ⟨γ, δ, hγ, hδ, hγδ, hsγ, hsδ⟩ := htwo s hs hsZ
    obtain ⟨u, huD, hu2, hsu⟩ := A5.exists_conj_mem_D S c hs hγ hδ hγδ hsγ hsδ
    obtain ⟨k, rfl⟩ := isConj_iff.mp hsu
    exact A5.not_isCentralInvolution S h1210 hL huD hu2 (A5.isCentralInvolution_conj hc k)
  refine ⟨ha, ?_, ?_⟩
  · intro T x hxM hxx hxT hxcomm
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    have hx2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨T₀, hT₀⟩ := S.prodDisc.exists_sylow_normalizer_le S.invariant
    have hT₀M : (T₀ : Subgroup X) ≤ M := fun y hy => hT₀ (Subgroup.le_normalizer hy)
    have hle : (Nat.card X).factorization 2 ≤ (Nat.card M).factorization 2 := by
      have h1 : Nat.card T₀ ∣ Nat.card M := Subgroup.card_dvd_of_le hT₀M
      rw [T₀.card_eq_multiplicity] at h1
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h1
    have hge : (Nat.card M).factorization 2 ≤ (Nat.card X).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card M) 2
    have hcard : Nat.card ((T : Subgroup ↥M).map M.subtype) =
        2 ^ (Nat.card X).factorization 2 := by
      rw [Subgroup.card_map_of_injective M.subtype_injective, T.card_eq_multiplicity,
        le_antisymm hge hle]
    have hcen : IsCentralInvolution x := by
      refine ⟨hx2, Sylow.ofCard _ hcard, ?_, fun y hy => (hxcomm y ?_).symm⟩
      · rw [Sylow.coe_ofCard]
        exact hxT
      · rwa [Sylow.coe_ofCard] at hy
    exact subset_closure ⟨(ha x hx2).mp hcen, hxM⟩
  · intro s hs hns
    have hsZ : s ∉ Z := fun h => hns (S.isCentralInvolution h)
    obtain ⟨γ, δ, hγ, hδ, hγδ, hsγ, hsδ⟩ := htwo s hs hsZ
    exact A5.exists_conj_mem_D S c hs hγ hδ hγδ hsγ hsδ

end CFSG.GH74.Uniqueness

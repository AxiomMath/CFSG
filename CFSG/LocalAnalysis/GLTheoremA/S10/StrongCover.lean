module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S10

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def PPrimePerfect (p : ℕ) (I : Subgroup G) : Prop :=
  ∀ M : Subgroup G, M ≤ I → (M.subgroupOf I).Normal → Nat.Coprime (M.relIndex I) p → M = I

theorem inf_eq_bot_of_isPGroup_of_coprime {p : ℕ} [hp : Fact p.Prime] {D M : Subgroup G}
    (hD : IsPGroup p D) (hM : Nat.Coprime (Nat.card M) p) : D ⊓ M = ⊥ := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hD.to_le (inf_le_left : D ⊓ M ≤ D))
  have hdvd : Nat.card (D ⊓ M : Subgroup G) ∣ Nat.card M := Subgroup.card_dvd_of_le inf_le_right
  rw [hn] at hdvd
  have h1 : p ^ n = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n hM.symm) hdvd
  exact Subgroup.card_eq_one.1 (by rw [hn, h1])

theorem exists_conj_of_isPGroup {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} [hp : Fact p.Prime]
    {P Q : Subgroup Γ} (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hPi : ¬ p ∣ P.index) (hQi : ¬ p ∣ Q.index) :
    ∃ g : Γ, ∀ x ∈ Q, ∃ y ∈ P, x = g * y * g⁻¹ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hP.toSylow hPi) (hQ.toSylow hQi)
  refine ⟨g, fun x hx => ?_⟩
  have hx' : x ∈ ((g • hP.toSylow hPi : Sylow p Γ) : Set Γ) := by
    rw [hg]
    exact hx
  rw [Sylow.coe_smul] at hx'
  obtain ⟨y, hy, rfl⟩ := hx'
  exact ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem exists_conj_iff_of_isPGroup {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} [hp : Fact p.Prime]
    {P Q : Subgroup Γ} (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hPi : ¬ p ∣ P.index) (hQi : ¬ p ∣ Q.index) :
    ∃ g : Γ, ∀ x : Γ, x ∈ Q ↔ ∃ y ∈ P, x = g * y * g⁻¹ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hP.toSylow hPi) (hQ.toSylow hQi)
  refine ⟨g, fun x => ⟨fun hx => ?_, fun hex => ?_⟩⟩
  · have hx' : x ∈ ((g • hP.toSylow hPi : Sylow p Γ) : Set Γ) := by
      rw [hg]
      exact hx
    rw [Sylow.coe_smul] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  · obtain ⟨y, hy, hxy⟩ := hex
    have hx' : x ∈ ((g • hP.toSylow hPi : Sylow p Γ) : Set Γ) := by
      rw [Sylow.coe_smul]
      exact ⟨y, hy, hxy.symm⟩
    rw [hg] at hx'
    exact hx'

theorem mem_centralizer_mul_of_coprime {p : ℕ} [Fact p.Prime] {D H M : Subgroup G}
    (hD : IsPGroup p D) (hM : Nat.Coprime (Nat.card M) p) (hMH : M ≤ H)
    (hMn : (M.subgroupOf H).Normal) (hDH : D ≤ Subgroup.normalizer (H : Set G))
    (hDM : D ≤ Subgroup.normalizer (M : Set G)) {h : G} (hh : h ∈ H)
    (hfix : ∀ d ∈ D, h⁻¹ * (d⁻¹ * h * d) ∈ M) :
    ∃ c ∈ H ⊓ Subgroup.centralizer (D : Set G), ∃ m ∈ M, h = c * m := by
  set X : Subgroup G := D ⊔ M with hXdef
  have hDX : D ≤ X := le_sup_left
  have hMX : M ≤ X := le_sup_right
  have hDM0 : D ⊓ M = ⊥ := inf_eq_bot_of_isPGroup_of_coprime hD hM
  have hMD0 : M ⊓ D = ⊥ := by rw [inf_comm]; exact hDM0
  have hXcard : Nat.card X = Nat.card M * Nat.card D := by
    have h1 := card_sup_mul_card_inf_of_le_normalizer (A := M) (B := D) hDM
    rw [hMD0, Subgroup.card_bot, mul_one, sup_comm] at h1
    exact h1
  have hXmul : ∀ x ∈ X, ∃ d ∈ D, ∃ m ∈ M, x = d * m := by
    intro x hx
    have hx' : x ∈ ((D ⊔ M : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D M hDM] at hx'
    obtain ⟨d, hd, m, hm, rfl⟩ := Set.mem_mul.1 hx'
    exact ⟨d, hd, m, hm, rfl⟩
  set K : Subgroup G := D.map (MulAut.conj h⁻¹).toMonoidHom with hKdef
  have hKX : K ≤ X := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hx
    have hm : h⁻¹ * (d⁻¹ * h * d) ∈ M := hfix d hd
    have e : (MulAut.conj h⁻¹).toMonoidHom d = d * (h⁻¹ * (d⁻¹ * h * d))⁻¹ := by
      show h⁻¹ * d * h⁻¹⁻¹ = d * (h⁻¹ * (d⁻¹ * h * d))⁻¹
      group
    rw [e]
    exact X.mul_mem (hDX hd) (hMX (M.inv_mem hm))
  have hKcard : Nat.card K = Nat.card D := by
    rw [hKdef]
    exact Nat.card_congr (Subgroup.equivMapOfInjective D _ (MulAut.conj h⁻¹).injective).symm.toEquiv
  have hrelD : D.relIndex X = Nat.card M := by
    have h1 := Subgroup.relIndex_mul_card D X
    rw [inf_eq_left.2 hDX] at h1
    have hpos : 0 < Nat.card D := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, hXcard, mul_comm]
  have hrelK : K.relIndex X = Nat.card M := by
    have h1 := Subgroup.relIndex_mul_card K X
    rw [inf_eq_left.2 hKX, hKcard] at h1
    have hpos : 0 < Nat.card D := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, hXcard, mul_comm]
  have hDi : ¬ p ∣ (D.subgroupOf X).index := by
    show ¬ p ∣ D.relIndex X
    rw [hrelD]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hM.symm
  have hKi : ¬ p ∣ (K.subgroupOf X).index := by
    show ¬ p ∣ K.relIndex X
    rw [hrelK]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hM.symm
  have hDp : IsPGroup p (D.subgroupOf X) := hD.comap_subtype
  have hKD : IsPGroup p K := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hD
    exact IsPGroup.of_card (n := n) (by rw [hKcard, hn])
  have hKp : IsPGroup p (K.subgroupOf X) := hKD.comap_subtype
  obtain ⟨g, hg⟩ := exists_conj_of_isPGroup hDp hKp hDi hKi
  obtain ⟨d₁, hd₁, m₁, hm₁, hg₁⟩ := hXmul ((g : G))⁻¹ (X.inv_mem g.2)
  have hgeq : (g : G) = m₁⁻¹ * d₁⁻¹ := by
    rw [← inv_inv (g : G), hg₁, mul_inv_rev]
  set a : G := m₁⁻¹ with ha_def
  have haM : a ∈ M := M.inv_mem hm₁
  have hnorm : ∀ d ∈ D, ∃ y ∈ D, (h * a)⁻¹ * d * (h * a) = y := by
    intro d hd
    have hxK : h⁻¹ * d * h ∈ K := Subgroup.mem_map.2 ⟨d, hd, by
      show h⁻¹ * d * h⁻¹⁻¹ = h⁻¹ * d * h
      rw [inv_inv]⟩
    obtain ⟨y, hy, hyx⟩ := hg ⟨h⁻¹ * d * h, hKX hxK⟩ (Subgroup.mem_subgroupOf.2 hxK)
    have hyx' : h⁻¹ * d * h = (g : G) * (y : G) * (g : G)⁻¹ := by
      have := congrArg Subtype.val hyx
      simpa using this
    refine ⟨d₁⁻¹ * (y : G) * d₁, D.mul_mem (D.mul_mem (D.inv_mem hd₁) (Subgroup.mem_subgroupOf.1 hy))
      hd₁, ?_⟩
    rw [hgeq] at hyx'
    calc (h * a)⁻¹ * d * (h * a) = a⁻¹ * (h⁻¹ * d * h) * a := by group
      _ = d₁⁻¹ * (y : G) * d₁ := by rw [hyx', ha_def]; group
  have hcomm : ∀ d ∈ D, d * (h * a) = (h * a) * d := by
    intro d hd
    obtain ⟨y, hy, hyeq⟩ := hnorm d⁻¹ (D.inv_mem hd)
    have hcD : (h * a)⁻¹ * d⁻¹ * (h * a) * d ∈ D :=
      D.mul_mem (by rw [hyeq]; exact hy) hd
    have hdM : d⁻¹ * a * d ∈ M := by
      have := (Subgroup.mem_normalizer_iff.1 (hDM (D.inv_mem hd)) a).1 haM
      rwa [inv_inv] at this
    have hcM : (h * a)⁻¹ * d⁻¹ * (h * a) * d ∈ M := by
      have e : (h * a)⁻¹ * d⁻¹ * (h * a) * d =
          a⁻¹ * (h⁻¹ * (d⁻¹ * h * d)) * (d⁻¹ * a * d) := by
        rw [ha_def]
        group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem haM) (hfix d hd)) hdM
    have hc1 : (h * a)⁻¹ * d⁻¹ * (h * a) * d = 1 := by
      have hmem : (h * a)⁻¹ * d⁻¹ * (h * a) * d ∈ D ⊓ M := Subgroup.mem_inf.2 ⟨hcD, hcM⟩
      rw [hDM0] at hmem
      exact (Subgroup.mem_bot.1 hmem)
    have h2 : d⁻¹ * (h * a) * d = h * a := by
      calc d⁻¹ * (h * a) * d = (h * a) * ((h * a)⁻¹ * d⁻¹ * (h * a) * d) := by group
        _ = h * a := by rw [hc1, mul_one]
    calc d * (h * a) = d * (d⁻¹ * (h * a) * d) := by rw [h2]
      _ = (h * a) * d := by group
  have hnH : h * a ∈ H := H.mul_mem hh (hMH haM)
  refine ⟨h * a, ⟨hnH, Subgroup.mem_centralizer_iff.2 fun d hd => hcomm d hd⟩, a⁻¹, M.inv_mem haM, ?_⟩
  exact (mul_inv_cancel_right h a).symm

theorem relIndex_dvd_of_le_of_normal {M K L : Subgroup G} (hKL : K ≤ L)
    (hn : (M.subgroupOf L).Normal) : M.relIndex K ∣ M.relIndex L := by
  rw [← Subgroup.relIndex_subgroupOf (H := M) hKL]
  haveI := hn
  exact Subgroup.relIndex_dvd_index_of_normal _ _

theorem coprime_relIndex_of_normal {p : ℕ} [Fact p.Prime] {I Θ M : Subgroup G}
    (hIΘ : I ≤ Subgroup.normalizer (Θ : Set G)) (hΘ : Nat.Coprime (Nat.card Θ) p)
    (hIM : I ≤ M) (hMX : M ≤ I ⊔ Θ) (hIn : (I.subgroupOf M).Normal) :
    Nat.Coprime (I.relIndex M) p := by
  have hMN : M ≤ Subgroup.normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIM).1 hIn
  have hB : M ⊓ Θ ≤ Subgroup.normalizer (I : Set G) := inf_le_left.trans hMN
  have hcard := card_sup_mul_card_inf_of_le_normalizer hB
  have hsup : I ⊔ (M ⊓ Θ) = M := by
    apply le_antisymm
    · exact sup_le hIM inf_le_left
    · intro m hm
      have hm' : m ∈ ((I ⊔ Θ : Subgroup G) : Set G) := hMX hm
      rw [Subgroup.coe_mul_of_left_le_normalizer_right I Θ hIΘ] at hm'
      obtain ⟨i, hi, θ, hθ, rfl⟩ := Set.mem_mul.1 hm'
      have hθM : θ ∈ M := by
        have e : θ = i⁻¹ * (i * θ) := by group
        rw [e]
        exact M.mul_mem (M.inv_mem (hIM hi)) hm
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hi) (Subgroup.mem_sup_right ⟨hθM, hθ⟩)
  have hinf : I ⊓ (M ⊓ Θ) = I ⊓ Θ := by rw [← inf_assoc, inf_eq_left.2 hIM]
  rw [hsup, hinf] at hcard
  have hI_rel : I.relIndex M * Nat.card I = Nat.card M := by
    have h := Subgroup.relIndex_mul_card I M
    rwa [inf_eq_left.2 hIM] at h
  have hpos : 0 < Nat.card I := Nat.card_pos
  have hq : I.relIndex M * Nat.card (I ⊓ Θ : Subgroup G) = Nat.card (M ⊓ Θ : Subgroup G) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc Nat.card I * (I.relIndex M * Nat.card (I ⊓ Θ : Subgroup G))
        = Nat.card M * Nat.card (I ⊓ Θ : Subgroup G) := by rw [← hI_rel]; ring
      _ = Nat.card I * Nat.card (M ⊓ Θ : Subgroup G) := hcard
  have hdvd : I.relIndex M ∣ Nat.card (M ⊓ Θ : Subgroup G) := Dvd.intro _ hq
  exact Nat.Coprime.coprime_dvd_left hdvd
    (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right) hΘ)

abbrev StrongGood (p : ℕ) (I A : Subgroup G) : Prop :=
  I ≤ A ∧ (I.subgroupOf A).Normal ∧ Nat.Coprime (I.relIndex A) p ∧
    ∀ M : Subgroup G, M ≤ A → (M.subgroupOf A).Normal → Nat.Coprime (M.relIndex A) p → I ≤ M

theorem strongGood_step {p : ℕ} [Fact p.Prime] {I Θ A M : Subgroup G}
    (hIΘ : I ≤ Subgroup.normalizer (Θ : Set G)) (hΘ : Nat.Coprime (Nat.card Θ) p)
    (hMX : M ≤ I ⊔ Θ) (hAM : A ≤ M) (hAn : (A.subgroupOf M).Normal)
    (hA : StrongGood p I A) : StrongGood p I M := by
  obtain ⟨hIA, hIAn, hIAcop, hmin⟩ := hA
  have hIM : I ≤ M := hIA.trans hAM
  have hMNA : M ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).1 hAn
  have hANI : A ≤ Subgroup.normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIA).1 hIAn
  have key : ∀ m ∈ M, ∀ x ∈ I, m * x * m⁻¹ ∈ I := by
    intro m hm
    set c : G →* G := (MulAut.conj m⁻¹).toMonoidHom with hc
    set J : Subgroup G := I.map c with hJ
    have hcA : ∀ a ∈ A, c a ∈ A := by
      intro a ha
      show m⁻¹ * a * m⁻¹⁻¹ ∈ A
      exact (Subgroup.mem_normalizer_iff.1 (hMNA (M.inv_mem hm)) a).1 ha
    have hAmap : A.map c = A := by
      apply le_antisymm
      · rintro _ ⟨a, ha, rfl⟩
        exact hcA a ha
      · intro a ha
        refine Subgroup.mem_map.2 ⟨m * a * m⁻¹, ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (hMNA hm) a).1 ha
        · show m⁻¹ * (m * a * m⁻¹) * m⁻¹⁻¹ = a
          group
    have hJA : J ≤ A := by
      rintro _ ⟨x, hx, rfl⟩
      exact hcA x (hIA hx)
    have hJn : (J.subgroupOf A).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hJA]
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hdir : ∀ b ∈ A, ∀ z ∈ J, b * z * b⁻¹ ∈ J := by
        intro b hb z hz
        obtain ⟨x, hx, rfl⟩ := hz
        have hb' : m * b * m⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hMNA hm) b).1 hb
        have hxI : (m * b * m⁻¹) * x * (m * b * m⁻¹)⁻¹ ∈ I :=
          (Subgroup.mem_normalizer_iff.1 (hANI hb') x).1 hx
        refine Subgroup.mem_map.2 ⟨(m * b * m⁻¹) * x * (m * b * m⁻¹)⁻¹, hxI, ?_⟩
        show m⁻¹ * ((m * b * m⁻¹) * x * (m * b * m⁻¹)⁻¹) * m⁻¹⁻¹ = b * (m⁻¹ * x * m⁻¹⁻¹) * b⁻¹
        group
      constructor
      · intro hy
        exact hdir a ha y hy
      · intro hy
        have := hdir a⁻¹ (A.inv_mem ha) _ hy
        have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
        rwa [e] at this
    have hJcop : Nat.Coprime (J.relIndex A) p := by
      have h := Subgroup.relIndex_map_map_of_injective (f := c) I A (MulAut.conj m⁻¹).injective
      rw [hAmap] at h
      rw [← hJ] at h
      rw [h]
      exact hIAcop
    have hIJ : I ≤ J := hmin J hJA hJn hJcop
    intro x hx
    have hxJ := hIJ hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxJ
    have e : y = m * x * m⁻¹ := by
      rw [← hyx]
      show y = m * (m⁻¹ * y * m⁻¹⁻¹) * m⁻¹
      group
    rw [← e]
    exact hy
  have hIn : (I.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hIM]
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact key m hm x
    · intro hx
      have := key m⁻¹ (M.inv_mem hm) _ hx
      have e : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
      rwa [e] at this
  have hcop : Nat.Coprime (I.relIndex M) p := coprime_relIndex_of_normal hIΘ hΘ hIM hMX hIn
  refine ⟨hIM, hIn, hcop, ?_⟩
  intro M' hM'M hM'n hM'cop
  have hK : M' ⊓ A ≤ A := inf_le_right
  have hMN' : M ≤ Subgroup.normalizer (M' : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hM'M).1 hM'n
  have hKn : ((M' ⊓ A).subgroupOf A).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK]
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hdir : ∀ b ∈ A, ∀ z ∈ M' ⊓ A, b * z * b⁻¹ ∈ M' ⊓ A := by
      intro b hb z hz
      have hz1 : z ∈ M' := (Subgroup.mem_inf.1 hz).1
      have hbM : b ∈ M := hAM hb
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hMN' hbM) z).1 hz1, ?_⟩
      exact A.mul_mem (A.mul_mem hb (Subgroup.mem_inf.1 hz).2) (A.inv_mem hb)
    constructor
    · intro hy
      exact hdir a ha y hy
    · intro hy
      have := hdir a⁻¹ (A.inv_mem ha) _ hy
      have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
      rwa [e] at this
  have hKcop : Nat.Coprime ((M' ⊓ A).relIndex A) p := by
    rw [Subgroup.inf_relIndex_right]
    exact Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_of_normal hAM hM'n) hM'cop
  exact (hmin (M' ⊓ A) hK hKn hKcop).trans inf_le_left

theorem strongGood_of_isSubnormal {p : ℕ} [Fact p.Prime] {I Θ : Subgroup G}
    (hIΘ : I ≤ Subgroup.normalizer (Θ : Set G)) (hΘ : Nat.Coprime (Nat.card Θ) p)
    {A B : Subgroup G} (hsub : IsSubnormal A B) :
    B ≤ I ⊔ Θ → StrongGood p I A → StrongGood p I B := by
  induction hsub with
  | refl H => exact fun _ h => h
  | @step H M K hHM hn hMK ih =>
    intro hBX hA
    exact ih hBX (strongGood_step hIΘ hΘ (hMK.le.trans hBX) hHM hn hA)

theorem le_of_pPrimePerfect_subnormal {p : ℕ} [Fact p.Prime] {I Θ : Subgroup G}
    (hI : PPrimePerfect p I) (hΘ : Nat.Coprime (Nat.card Θ) p)
    (hIΘ : I ≤ Subgroup.normalizer (Θ : Set G)) (hsub : IsSubnormal I (I ⊔ Θ)) :
    (I.subgroupOf (I ⊔ Θ)).Normal ∧
      ∀ M : Subgroup G, M ≤ I ⊔ Θ → (M.subgroupOf (I ⊔ Θ)).Normal →
        Nat.Coprime (M.relIndex (I ⊔ Θ)) p → I ≤ M := by
  have base : StrongGood p I I := by
    refine ⟨le_rfl, ?_, ?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl]
      exact Subgroup.le_normalizer
    · rw [Subgroup.relIndex_self]
      exact Nat.coprime_one_left p
    · intro M hMI hMn hcop
      exact le_of_eq (hI M hMI hMn hcop).symm
  have hgood := strongGood_of_isSubnormal hIΘ hΘ hsub le_rfl base
  obtain ⟨-, h1, -, h2⟩ := hgood
  exact ⟨h1, h2⟩

theorem eq_top_of_normal_coprime_index {p : ℕ} [hp : Fact p.Prime] {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) (hpQ : p ∣ Nat.card Q) (N : Subgroup Q) [hN : N.Normal]
    (hNi : Nat.Coprime N.index p) : N = ⊤ := by
  by_contra hne
  have hcen : N ≤ Subgroup.center Q :=
    le_center_of_normal_of_isQuasisimple hQ hN hne
  obtain ⟨P⟩ : Nonempty (Sylow p Q) := inferInstance
  have hPN : (P : Subgroup Q) ≤ N := by
    obtain ⟨n, hn⟩ := IsPGroup.index P.isPGroup' (N.subgroupOf (P : Subgroup Q)) 
    have hdvd : N.relIndex (P : Subgroup Q) ∣ N.index := Subgroup.relIndex_dvd_index_of_normal _ _
    have hn' : N.relIndex (P : Subgroup Q) = p ^ n := hn
    rw [hn'] at hdvd
    have hcop : Nat.Coprime (p ^ n) N.index := Nat.Coprime.pow_left n hNi.symm
    have h1 : p ^ n = 1 := Nat.Coprime.eq_one_of_dvd hcop hdvd
    exact Subgroup.relIndex_eq_one.1 (by rw [hn', h1])
  have hPcen : (P : Subgroup Q) ≤ Subgroup.center Q := hPN.trans hcen
  have hPnorm : Subgroup.normalizer (P : Set Q) ≤ Subgroup.centralizer (P : Set Q) := by
    intro g _
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    exact (Subgroup.mem_center_iff.1 (hPcen hh) g).symm
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hPnorm
  set K₀ : Subgroup Q := (MonoidHom.transferSylow P hPnorm).ker with hK₀
  have hcommK : (⁅(⊤ : Subgroup Q), ⊤⁆ : Subgroup Q) ≤ K₀ := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have hdec : ∀ g : Q, ∃ k ∈ K₀, ∃ x ∈ (P : Subgroup Q), g = k * x := by
      intro g
      have hg : g ∈ (K₀ : Set Q) * ((P : Subgroup Q) : Set Q) := by
        rw [(Subgroup.isComplement'_def.1 hcompl).mul_eq]
        exact Set.mem_univ g
      obtain ⟨k, hk, x, hx, rfl⟩ := Set.mem_mul.1 hg
      exact ⟨k, hk, x, hx, rfl⟩
    obtain ⟨k₁, hk₁, x₁, hx₁, rfl⟩ := hdec g₁
    obtain ⟨k₂, hk₂, x₂, hx₂, rfl⟩ := hdec g₂
    have hz₁ : x₁ ∈ Subgroup.center Q := hPcen hx₁
    have hz₂ : x₂ ∈ Subgroup.center Q := hPcen hx₂
    rw [commutatorElement_mul_center_right hz₂, commutatorElement_mul_center_left hz₁,
      commutatorElement_def]
    exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hk₁ hk₂) (K₀.inv_mem hk₁)) (K₀.inv_mem hk₂)
  have htop : K₀ = ⊤ := by
    have := hQ.1
    apply eq_top_iff.2
    rw [← this]
    exact hcommK
  have hPbot : (P : Subgroup Q) = ⊥ := by
    have h := Subgroup.isComplement'_top_left.1 (htop ▸ hcompl)
    exact h
  exact Sylow.ne_bot_of_dvd_card P hpQ hPbot

theorem mem_glaPPrimeCore_of_mem_glaPPrimeCoreOf {p : ℕ} {X : Subgroup G} {k : G}
    (hk : k ∈ GLAPPrimeCoreOf p X) (hkX : k ∈ X) : (⟨k, hkX⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
  obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.1 hk
  have : y = ⟨k, hkX⟩ := Subtype.ext hyk
  rw [← this]
  exact hy

theorem pPrimePerfect_of_glaPComponent {p : ℕ} [hp : Fact p.Prime] {X K : Subgroup G}
    (hK : GLAPComponent p X K) : PPrimePerfect p K := by
  have hK0 := hK
  obtain ⟨hKX, hsub, hcomp, hmin⟩ := hK
  have hpX : GLAPPrimeCoreOf p K ≤ GLAPPrimeCoreOf p X :=
    glaPPrimeCoreOf_le_of_isSubnormal hp.out hsub
  have hcompNt := isQuasisimple_nontrivial hcomp.2.2
  have hpK : p ∣ Nat.card K := by
    by_contra hndvd
    have hcopK : Nat.Coprime p (Nat.card K) := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hndvd
    have htopK : (⊤ : Subgroup ↥K) ≤ GLAPPrimeCore p ↥K := by
      have hc : Nat.Coprime p (Nat.card (⊤ : Subgroup ↥K)) := by
        rw [Subgroup.card_top]
        exact hcopK
      exact le_sSup ⟨inferInstance, hc⟩
    have hKO : K ≤ GLAPPrimeCoreOf p K := by
      intro k hk
      exact Subgroup.mem_map.2 ⟨⟨k, hk⟩, htopK (Subgroup.mem_top _), rfl⟩
    have hπ : (K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_glaPPrimeCore_of_mem_glaPPrimeCoreOf (hpX (hKO (Subgroup.mem_subgroupOf.1 hx))) x.2
    obtain ⟨x, y, hxy⟩ := hcompNt.exists_pair_ne
    have hall : ∀ z ∈ (K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)), z = 1 := by
      intro z hz
      rw [hπ] at hz
      exact Subgroup.mem_bot.1 hz
    exact hxy (Subtype.ext ((hall _ x.2).trans (hall _ y.2).symm))
  have hQK : CFSG.Open.IsQuasisimple (↥K ⧸ GLAPPrimeCore p ↥K) :=
    isQuasisimple_pQuot_of_glaPComponent hp.out hK0
  have hpQ : p ∣ Nat.card (↥K ⧸ GLAPPrimeCore p ↥K) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p ↥K)
    have h2 : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := CFSG.pPrimeCore_coprime_card
    rw [h1] at hpK
    exact Nat.Coprime.dvd_of_dvd_mul_right h2 hpK
  intro M hMK hMn hcop
  set mk : ↥K →* ↥K ⧸ GLAPPrimeCore p ↥K := QuotientGroup.mk' (GLAPPrimeCore p ↥K) with hmkdef
  have hNn : ((M.subgroupOf K).map mk).Normal :=
    hMn.map mk (QuotientGroup.mk'_surjective _)
  have hNi : Nat.Coprime ((M.subgroupOf K).map mk).index p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)) hcop
  have htop := eq_top_of_normal_coprime_index hQK hpQ ((M.subgroupOf K).map mk) hNi
  have hdec : ∀ k ∈ K, ∃ m ∈ M, ∃ o ∈ GLAPPrimeCoreOf p K, k = m * o := by
    intro k hk
    have hmem : mk ⟨k, hk⟩ ∈ (M.subgroupOf K).map mk := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m', hm', hmk'⟩ := Subgroup.mem_map.1 hmem
    have hq : m'⁻¹ * ⟨k, hk⟩ ∈ GLAPPrimeCore p ↥K := QuotientGroup.eq.1 hmk'
    refine ⟨(m' : G), Subgroup.mem_subgroupOf.1 hm', (m' : G)⁻¹ * k,
      Subgroup.mem_map.2 ⟨m'⁻¹ * ⟨k, hk⟩, hq, rfl⟩, ?_⟩
    simp
  have hπle : (K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)) ≤
      (M.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p X)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨m, hmM, o, ho, hxmo⟩ := hdec x (Subgroup.mem_subgroupOf.1 hx)
    have hoK : o ∈ K := by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 ho
      exact y.2
    have hoX : o ∈ X := hKX hoK
    refine Subgroup.mem_map.2 ⟨⟨m, hMK.trans hKX hmM⟩, Subgroup.mem_subgroupOf.2 hmM, ?_⟩
    have hinv : (⟨m, hKX (hMK hmM)⟩ : ↥X)⁻¹ * x = ⟨o, hoX⟩ := Subtype.ext (by
      show m⁻¹ * (x : G) = o
      rw [hxmo]
      group)
    have hmem : (⟨m, hKX (hMK hmM)⟩ : ↥X)⁻¹ * x ∈ GLAPPrimeCore p ↥X := by
      rw [hinv]
      exact mem_glaPPrimeCore_of_mem_glaPPrimeCoreOf (hpX ho) hoX
    exact QuotientGroup.eq.2 hmem
  by_contra hne
  have hlt : M < K := lt_of_le_of_ne hMK hne
  have hsubM : IsSubnormal M X := (IsSubnormal.step hMK hMn (IsSubnormal.refl K)).trans hsub
  apply hmin M hlt hsubM
  exact le_antisymm (Subgroup.map_mono (fun y hy => Subgroup.mem_subgroupOf.2
    (hMK (Subgroup.mem_subgroupOf.1 hy)))) hπle

theorem pPrimePerfect_glaPLayer (p : ℕ) [Fact p.Prime] (Y : Subgroup G) :
    PPrimePerfect p (GLAPLayer p Y) := by
  intro M hMY hMn hcop
  have hMN : GLAPLayer p Y ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMY).1 hMn
  have hcomp : ∀ K : Subgroup G, GLAPComponent p Y K → K ≤ M := by
    intro K hK
    have hKL : K ≤ GLAPLayer p Y := le_sSup hK
    have hKN : K ≤ Subgroup.normalizer (M : Set G) := hKL.trans hMN
    have hKn : ((M ⊓ K).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hdir : ∀ c ∈ K, ∀ w ∈ M ⊓ K, c * w * c⁻¹ ∈ M ⊓ K := by
        intro c hc w hw
        refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hKN hc) w).1 (Subgroup.mem_inf.1 hw).1,
          K.mul_mem (K.mul_mem hc (Subgroup.mem_inf.1 hw).2) (K.inv_mem hc)⟩
      constructor
      · intro hz
        exact hdir b hb z hz
      · intro hz
        have := hdir b⁻¹ (K.inv_mem hb) _ hz
        have e : b⁻¹ * (b * z * b⁻¹) * b⁻¹⁻¹ = z := by group
        rwa [e] at this
    have hKcop : Nat.Coprime ((M ⊓ K).relIndex K) p := by
      rw [Subgroup.inf_relIndex_right]
      exact Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_of_normal hKL hMn) hcop
    have hMK : M ⊓ K = K := pPrimePerfect_of_glaPComponent hK (M ⊓ K) inf_le_right hKn hKcop
    calc K = M ⊓ K := hMK.symm
      _ ≤ M := inf_le_left
  exact le_antisymm hMY (sSup_le fun K hK => hcomp K hK)

theorem conj_mem_sup_of {g : G} {A B : Subgroup G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) : ∀ t ∈ A ⊔ B, g * t * g⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  intro t ht
  exact hle ht

theorem mem_normalizer_of_conj' {g : G} {Y : Subgroup G} (h1 : ∀ t ∈ Y, g * t * g⁻¹ ∈ Y)
    (h2 : ∀ t ∈ Y, g⁻¹ * t * g⁻¹⁻¹ ∈ Y) : g ∈ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => h1 h hh, fun hh => ?_⟩
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  have := h2 _ hh
  rwa [e] at this

theorem mem_normalizer_inf_of {g : G} {A C : Subgroup G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hC : g ∈ Subgroup.normalizer (C : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hC ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA h, hC h]

theorem inf_le_glaPPrimeCoreOf {p : ℕ} [Fact p.Prime] {I Θ : Subgroup G}
    (hIΘ : I ≤ Subgroup.normalizer (Θ : Set G)) (hΘ : Nat.Coprime (Nat.card Θ) p) :
    I ⊓ Θ ≤ GLAPPrimeCoreOf p I := by
  have hJn : ((I ⊓ Θ).subgroupOf I).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxI := (Subgroup.mem_inf.1 hx).1
      have hxΘ := (Subgroup.mem_inf.1 hx).2
      exact Subgroup.mem_inf.2 ⟨I.mul_mem (I.mul_mem hi hxI) (I.inv_mem hi),
        (Subgroup.mem_normalizer_iff.1 (hIΘ hi) x).1 hxΘ⟩
    · intro hy
      have hyI := (Subgroup.mem_inf.1 hy).1
      have hyΘ := (Subgroup.mem_inf.1 hy).2
      have e : i⁻¹ * (i * x * i⁻¹) * i⁻¹⁻¹ = x := by group
      have e1 : i⁻¹ * (i * x * i⁻¹) * i = x := by group
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · have := I.mul_mem (I.mul_mem (I.inv_mem hi) hyI) hi
        rwa [e1] at this
      · have := (Subgroup.mem_normalizer_iff.1 (hIΘ (I.inv_mem hi)) _).1 hyΘ
        rwa [e] at this
  have hJcop : Nat.Coprime (Nat.card ((I ⊓ Θ).subgroupOf I)) p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    exact Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_right) hΘ
  have hmem : (I ⊓ Θ).subgroupOf I ≤ GLAPPrimeCore p ↥I := by
    unfold GLAPPrimeCore CFSG.pPrimeCore
    exact le_sSup ⟨hJn, hJcop.symm⟩
  intro x hx
  exact Subgroup.mem_map.2 ⟨⟨x, (Subgroup.mem_inf.1 hx).1⟩, hmem (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem normal_coprime_inf {p : ℕ} [Fact p.Prime] {L J₁ J₂ : Subgroup G} (hJ₁ : J₁ ≤ L)
    (hJ₂ : J₂ ≤ L) (hn₁ : (J₁.subgroupOf L).Normal) (hn₂ : (J₂.subgroupOf L).Normal)
    (hc₁ : Nat.Coprime (J₁.relIndex L) p) (hc₂ : Nat.Coprime (J₂.relIndex L) p) :
    ((J₁ ⊓ J₂).subgroupOf L).Normal ∧ Nat.Coprime ((J₁ ⊓ J₂).relIndex L) p := by
  have hN₁ : L ≤ Subgroup.normalizer (J₁ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁).1 hn₁
  have hN₂ : L ≤ Subgroup.normalizer (J₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂).1 hn₂
  refine ⟨?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (inf_le_left.trans hJ₁)]
    exact fun g hg => mem_normalizer_inf_of (hN₁ hg) (hN₂ hg)
  · have h1 := Subgroup.relIndex_mul_relIndex (J₁ ⊓ J₂) J₁ L inf_le_left hJ₁
    have h2 : (J₁ ⊓ J₂).relIndex J₁ = J₂.relIndex J₁ := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
    rw [← h1, h2]
    exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left
      (relIndex_dvd_of_le_of_normal hJ₁ hn₂) hc₂) hc₁

theorem exists_min_card_of {P : Subgroup G → Prop} (h : ∃ J, P J) :
    ∃ O, P O ∧ ∀ J, P J → Nat.card O ≤ Nat.card J := by
  classical
  have hex : ∃ k, ∃ J, P J ∧ Nat.card J = k := by
    obtain ⟨J, hJ⟩ := h
    exact ⟨_, J, hJ, rfl⟩
  obtain ⟨O, hO, hOk⟩ := Nat.find_spec hex
  refine ⟨O, hO, fun J hJ => ?_⟩
  rw [hOk]
  exact Nat.find_min' hex ⟨J, hJ, rfl⟩

theorem covers_of_weak {p : ℕ} [Fact p.Prime] {D I W N : Subgroup G}
    (hD : IsPGroup p D) (hIC : I ≤ Subgroup.centralizer (D : Set G))
    (hsub : IsSubnormal I (Subgroup.centralizer (D : Set G))) (hI : PPrimePerfect p I)
    (hW : Nat.Coprime (Nat.card W) p) (hDW : D ≤ Subgroup.normalizer (W : Set G))
    (hIW : I ≤ Subgroup.normalizer (W : Set G)) (hDN : D ≤ N)
    (hcov : ∀ i ∈ I, ∃ n ∈ N, ∃ w ∈ W, i = n * w) :
    S9.Covers p N I := by
  set C : Subgroup G := Subgroup.centralizer (D : Set G) with hCdef
  set Θ : Subgroup G := W ⊓ C with hΘdef
  have hΘcop : Nat.Coprime (Nat.card Θ) p :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hW
  have hconjΘ : ∀ i ∈ I, ∀ x ∈ Θ, i * x * i⁻¹ ∈ Θ := by
    intro i hi x hx
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hIW hi) x).1 (Subgroup.mem_inf.1 hx).1,
      C.mul_mem (C.mul_mem (hIC hi) (Subgroup.mem_inf.1 hx).2) (C.inv_mem (hIC hi))⟩
  have hIΘ : I ≤ Subgroup.normalizer (Θ : Set G) := by
    intro i hi
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjΘ i hi x
    · intro hx
      have := hconjΘ i⁻¹ (I.inv_mem hi) _ hx
      have e : i⁻¹ * (i * x * i⁻¹) * i⁻¹⁻¹ = x := by group
      rwa [e] at this
  set X : Subgroup G := I ⊔ Θ with hXdef
  have hΘX : Θ ≤ X := le_sup_right
  have hIX : I ≤ X := le_sup_left
  have hXC : X ≤ C := sup_le hIC inf_le_right
  have hXΘ : X ≤ Subgroup.normalizer (Θ : Set G) := sup_le hIΘ Subgroup.le_normalizer
  have hΘXn : ∀ n ∈ X, ∀ t ∈ Θ, n * t * n⁻¹ ∈ Θ := fun n hn t ht =>
    (Subgroup.mem_normalizer_iff.1 (hXΘ hn) t).1 ht
  have hsubX : IsSubnormal I X := by
    have h := hsub.inf X
    rwa [inf_eq_left.2 hIX, inf_eq_right.2 hXC] at h
  have hA := le_of_pPrimePerfect_subnormal hI hΘcop hIΘ hsubX
  have hXnI : X ≤ Subgroup.normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIX).1 hA.1
  set Y : Subgroup G := I ⊔ W with hYdef
  have hWY : W ≤ Y := le_sup_right
  have hIY : I ≤ Y := le_sup_left
  have hYN : Y ≤ Subgroup.normalizer (W : Set G) := sup_le hIW Subgroup.le_normalizer
  have hDY : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y := by
    intro d hd
    have hA' : ∀ a ∈ I, d * a * d⁻¹ ∈ I ⊔ W := by
      intro a ha
      have hda : d * a * d⁻¹ = a := by
        have h1 : d * a = a * d := Subgroup.mem_centralizer_iff.1 (hIC ha) d hd
        calc d * a * d⁻¹ = a * d * d⁻¹ := by rw [h1]
          _ = a := by group
      rw [hda]
      exact Subgroup.mem_sup_left ha
    have hB' : ∀ b ∈ W, d * b * d⁻¹ ∈ I ⊔ W := fun b hb =>
      Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hDW hd) b).1 hb)
    exact conj_mem_sup_of hA' hB'
  have hDNY : D ≤ Subgroup.normalizer (Y : Set G) := fun d hd =>
    mem_normalizer_of_conj' (hDY d hd) (fun y hy => hDY d⁻¹ (D.inv_mem hd) y hy)
  have hDNN : D ≤ Subgroup.normalizer (N : Set G) := fun d hd => Subgroup.le_normalizer (hDN hd)
  have hDH : D ≤ Subgroup.normalizer ((N ⊓ Y : Subgroup G) : Set G) := fun d hd =>
    mem_normalizer_inf_of (hDNN hd) (hDNY hd)
  have hdec : ∀ i ∈ I, ∃ c ∈ N, c ∈ X ∧ ∃ θ ∈ Θ, i = c * θ := by
    intro i hi
    obtain ⟨n, hnN, w, hwW, hiw⟩ := hcov i hi
    have hn' : n = i * w⁻¹ := by rw [hiw]; group
    have hnY : n ∈ Y := by
      rw [hn']
      exact Y.mul_mem (hIY hi) (Y.inv_mem (hWY hwW))
    have hnH : n ∈ N ⊓ Y := Subgroup.mem_inf.2 ⟨hnN, hnY⟩
    have hMH : W ⊓ (N ⊓ Y) ≤ N ⊓ Y := inf_le_right
    have hHW : N ⊓ Y ≤ Subgroup.normalizer (W : Set G) := inf_le_right.trans hYN
    have hMn : ((W ⊓ (N ⊓ Y)).subgroupOf (N ⊓ Y)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMH]
      intro h hh
      exact mem_normalizer_inf_of (hHW hh) (Subgroup.le_normalizer hh)
    have hMcop : Nat.Coprime (Nat.card ↥(W ⊓ (N ⊓ Y))) p :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hW
    have hDM : D ≤ Subgroup.normalizer ((W ⊓ (N ⊓ Y) : Subgroup G) : Set G) := fun d hd =>
      mem_normalizer_inf_of (hDW hd) (hDH hd)
    have hfix : ∀ d ∈ D, n⁻¹ * (d⁻¹ * n * d) ∈ W ⊓ (N ⊓ Y) := by
      intro d hd
      have hdi : d * i = i * d := Subgroup.mem_centralizer_iff.1 (hIC hi) d hd
      have hdiC : d⁻¹ * i * d = i := by
        calc d⁻¹ * i * d = d⁻¹ * (i * d) := by group
          _ = d⁻¹ * (d * i) := by rw [hdi]
          _ = i := by group
      have hxeq : n⁻¹ * (d⁻¹ * n * d) = w * (d⁻¹ * w⁻¹ * d) := by
        rw [hn']
        calc (i * w⁻¹)⁻¹ * (d⁻¹ * (i * w⁻¹) * d) = w * i⁻¹ * (d⁻¹ * i * d) * (d⁻¹ * w⁻¹ * d) := by
              group
          _ = w * (d⁻¹ * w⁻¹ * d) := by rw [hdiC]; group
      have hxW : n⁻¹ * (d⁻¹ * n * d) ∈ W := by
        rw [hxeq]
        have hdw : d⁻¹ * w⁻¹ * d ∈ W := by
          have := (Subgroup.mem_normalizer_iff.1 (hDW (D.inv_mem hd)) w⁻¹).1 (W.inv_mem hwW)
          rwa [inv_inv] at this
        exact W.mul_mem hwW hdw
      have hxH : n⁻¹ * (d⁻¹ * n * d) ∈ N ⊓ Y := by
        have hdn : d⁻¹ * n * d ∈ N ⊓ Y := by
          have := (Subgroup.mem_normalizer_iff.1 (hDH (D.inv_mem hd)) n).1 hnH
          rwa [inv_inv] at this
        exact (N ⊓ Y).mul_mem ((N ⊓ Y).inv_mem hnH) hdn
      exact Subgroup.mem_inf.2 ⟨hxW, hxH⟩
    obtain ⟨c, hcHC, m, hmM, hnc⟩ :=
      mem_centralizer_mul_of_coprime hD hMcop hMH hMn hDH hDM hnH hfix
    have hcH : c ∈ N ⊓ Y := (Subgroup.mem_inf.1 hcHC).1
    have hcC : c ∈ C := (Subgroup.mem_inf.1 hcHC).2
    have hθW : m * w ∈ W := W.mul_mem (Subgroup.mem_inf.1 hmM).1 hwW
    have hθC : m * w ∈ C := by
      have e : m * w = c⁻¹ * i := by
        rw [hiw, hnc]
        group
      rw [e]
      exact C.mul_mem (C.inv_mem hcC) (hIC hi)
    have hθΘ : m * w ∈ Θ := Subgroup.mem_inf.2 ⟨hθW, hθC⟩
    have hcX : c ∈ X := by
      have e : c = i * (m * w)⁻¹ := by
        rw [hiw, hnc]
        group
      rw [e]
      exact X.mul_mem (hIX hi) (X.inv_mem (hΘX hθΘ))
    exact ⟨c, (Subgroup.mem_inf.1 hcH).1, hcX, m * w, hθΘ, by rw [hiw, hnc]; group⟩
  set N₁ : Subgroup G := N ⊓ X with hN₁def
  have hXeq : X = N₁ ⊔ Θ := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ ((I ⊔ Θ : Subgroup G) : Set G) := hx
      rw [Subgroup.coe_mul_of_left_le_normalizer_right I Θ hIΘ] at hx'
      obtain ⟨i, hi, θ₀, hθ₀, rfl⟩ := Set.mem_mul.1 hx'
      obtain ⟨c, hcN, hcX, θ, hθ, hic⟩ := hdec i hi
      have e : i * θ₀ = c * (θ * θ₀) := by
        rw [hic]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hcN, hcX⟩))
        (Subgroup.mem_sup_right (Θ.mul_mem hθ hθ₀))
    · exact sup_le inf_le_right hΘX
  have hN₁X : N₁ ≤ X := inf_le_right
  have hN₁Θ : N₁ ≤ Subgroup.normalizer (Θ : Set G) := hN₁X.trans hXΘ
  have hN₁P : N₁ ≤ N₁ ∧ (N₁.subgroupOf N₁).Normal ∧ Nat.Coprime (N₁.relIndex N₁) p :=
    ⟨le_rfl, (Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl).2 Subgroup.le_normalizer,
      by rw [Subgroup.relIndex_self]; exact Nat.coprime_one_left p⟩
  obtain ⟨O, ⟨hON₁, hOn, hOc⟩, hOmin⟩ := exists_min_card_of
    (P := fun J => J ≤ N₁ ∧ (J.subgroupOf N₁).Normal ∧ Nat.Coprime (J.relIndex N₁) p) ⟨N₁, hN₁P⟩
  have hOX : O ≤ X := hON₁.trans hN₁X
  have hOΘ : O ≤ Subgroup.normalizer (Θ : Set G) := hOX.trans hXΘ
  have hN₁I : (N₁ ⊓ I) ≤ N₁ ∧ ((N₁ ⊓ I).subgroupOf N₁).Normal ∧
      Nat.Coprime ((N₁ ⊓ I).relIndex N₁) p := by
    refine ⟨inf_le_left, ?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro n hn
      exact mem_normalizer_inf_of (Subgroup.le_normalizer hn) (hXnI (hN₁X hn))
    · rw [Subgroup.inf_relIndex_left]
      exact Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_of_normal hN₁X hA.1)
        (coprime_relIndex_of_normal hIΘ hΘcop hIX le_rfl hA.1)
  have hOI : O ≤ N₁ ⊓ I := by
    have hJ := normal_coprime_inf hON₁ inf_le_left hOn hN₁I.2.1 hOc hN₁I.2.2
    have hle : Nat.card O ≤ Nat.card ↥(O ⊓ (N₁ ⊓ I)) :=
      hOmin _ ⟨inf_le_left.trans hON₁, hJ.1, hJ.2⟩
    have heq : O ⊓ (N₁ ⊓ I) = O := Subgroup.eq_of_le_of_card_ge inf_le_left hle
    calc O = O ⊓ (N₁ ⊓ I) := heq.symm
      _ ≤ N₁ ⊓ I := inf_le_right
  have hOI' : O ≤ I := hOI.trans inf_le_right
  have hOcov : O ≤ N ⊓ I := hOI.trans (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
  have hQX : O ⊔ Θ ≤ X := sup_le hOX hΘX
  have hconjN : ∀ n ∈ N₁, ∀ q ∈ O ⊔ Θ, n * q * n⁻¹ ∈ O ⊔ Θ := by
    intro n hn
    have hnO : ∀ o ∈ O, n * o * n⁻¹ ∈ O := by
      have hN1 : N₁ ≤ Subgroup.normalizer (O : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hON₁).1 hOn
      intro o ho
      exact (Subgroup.mem_normalizer_iff.1 (hN1 hn) o).1 ho
    apply conj_mem_sup_of (A := O) (B := Θ)
    · intro o ho
      exact Subgroup.mem_sup_left (hnO o ho)
    · intro t ht
      exact Subgroup.mem_sup_right (hΘXn n (hN₁X hn) t ht)
  have hconjΘ' : ∀ θ ∈ Θ, ∀ q ∈ O ⊔ Θ, θ * q * θ⁻¹ ∈ O ⊔ Θ := by
    intro θ hθ
    apply conj_mem_sup_of (A := O) (B := Θ)
    · intro o ho
      have h1 : o⁻¹ * θ * o⁻¹⁻¹ ∈ Θ := hΘXn o⁻¹ (X.inv_mem (hOX ho)) θ hθ
      have e : θ * o * θ⁻¹ = o * ((o⁻¹ * θ * o⁻¹⁻¹) * θ⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
        (Subgroup.mem_sup_right (Θ.mul_mem h1 (Θ.inv_mem hθ)))
    · intro t ht
      exact Subgroup.mem_sup_right (hΘXn θ (hΘX hθ) t ht)
  have hN₁nQ : N₁ ≤ Subgroup.normalizer ((O ⊔ Θ : Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_of_conj' (fun q hq => hconjN n hn q hq)
      (fun q hq => hconjN n⁻¹ (N₁.inv_mem hn) q hq)
  have hΘnQ : Θ ≤ Subgroup.normalizer ((O ⊔ Θ : Subgroup G) : Set G) := fun θ hθ =>
    mem_normalizer_of_conj' (fun q hq => hconjΘ' θ hθ q hq)
      (fun q hq => hconjΘ' θ⁻¹ (Θ.inv_mem hθ) q hq)
  have hXnQ : X ≤ Subgroup.normalizer ((O ⊔ Θ : Subgroup G) : Set G) := by
    rw [hXeq]
    exact sup_le hN₁nQ hΘnQ
  have hQnorm : ((O ⊔ Θ).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).2 hXnQ
  have hQcop : Nat.Coprime ((O ⊔ Θ).relIndex X) p := by
    have h1 : (O ⊔ Θ).relIndex X * Nat.card ↥(O ⊔ Θ) = Nat.card ↥X := by
      have := Subgroup.relIndex_mul_card (O ⊔ Θ) X
      rwa [inf_eq_left.2 hQX] at this
    have h2 : O.relIndex N₁ * Nat.card ↥O = Nat.card ↥N₁ := by
      have := Subgroup.relIndex_mul_card O N₁
      rwa [inf_eq_left.2 hON₁] at this
    have h3 : Nat.card ↥X * Nat.card ↥(Θ ⊓ N₁) = Nat.card ↥Θ * Nat.card ↥N₁ := by
      have := card_sup_mul_card_inf_of_le_normalizer (A := Θ) (B := N₁) hN₁Θ
      have hsup : Θ ⊔ N₁ = X := by rw [hXeq, sup_comm]
      rwa [hsup] at this
    have h4 : Nat.card ↥(O ⊔ Θ) * Nat.card ↥(Θ ⊓ O) = Nat.card ↥Θ * Nat.card ↥O := by
      have := card_sup_mul_card_inf_of_le_normalizer (A := Θ) (B := O) hOΘ
      rwa [sup_comm] at this
    have hcop_b : Nat.Coprime (Nat.card ↥(Θ ⊓ O)) p :=
      Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hΘcop
    have hqpos : 0 < Nat.card ↥(O ⊔ Θ) := Nat.card_pos
    have key : (O ⊔ Θ).relIndex X * Nat.card ↥(Θ ⊓ N₁) =
        O.relIndex N₁ * Nat.card ↥(Θ ⊓ O) := by
      apply Nat.eq_of_mul_eq_mul_right hqpos
      calc (O ⊔ Θ).relIndex X * Nat.card ↥(Θ ⊓ N₁) * Nat.card ↥(O ⊔ Θ)
          = (O ⊔ Θ).relIndex X * Nat.card ↥(O ⊔ Θ) * Nat.card ↥(Θ ⊓ N₁) := by ring
        _ = Nat.card ↥X * Nat.card ↥(Θ ⊓ N₁) := by rw [h1]
        _ = Nat.card ↥Θ * Nat.card ↥N₁ := h3
        _ = Nat.card ↥Θ * (O.relIndex N₁ * Nat.card ↥O) := by rw [h2]
        _ = O.relIndex N₁ * (Nat.card ↥Θ * Nat.card ↥O) := by ring
        _ = O.relIndex N₁ * (Nat.card ↥(O ⊔ Θ) * Nat.card ↥(Θ ⊓ O)) := by rw [h4]
        _ = O.relIndex N₁ * Nat.card ↥(Θ ⊓ O) * Nat.card ↥(O ⊔ Θ) := by ring
    exact Nat.Coprime.coprime_dvd_left ⟨Nat.card ↥(Θ ⊓ N₁), key.symm⟩
      (Nat.Coprime.mul_left hOc hcop_b)
  have hIQ : I ≤ O ⊔ Θ := hA.2 (O ⊔ Θ) hQX hQnorm hQcop
  have hcore : I ⊓ Θ ≤ GLAPPrimeCoreOf p I := inf_le_glaPPrimeCoreOf hIΘ hΘcop
  show (N ⊓ I) ⊔ GLAPPrimeCoreOf p I = I
  apply le_antisymm
  · exact sup_le inf_le_right (Subgroup.map_subtype_le _)
  · intro i hi
    have hi' : i ∈ ((O ⊔ Θ : Subgroup G) : Set G) := hIQ hi
    rw [Subgroup.coe_mul_of_left_le_normalizer_right O Θ hOΘ] at hi'
    obtain ⟨o, ho, θ, hθ, rfl⟩ := Set.mem_mul.1 hi'
    have hoI : o ∈ I := hOI' ho
    have hθI : θ ∈ I := by
      have := I.mul_mem (I.inv_mem hoI) hi
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hOcov ho))
      (Subgroup.mem_sup_right (hcore (Subgroup.mem_inf.2 ⟨hθI, hθ⟩)))

end CFSG.LocalAnalysis.GLTheoremA.S10

end

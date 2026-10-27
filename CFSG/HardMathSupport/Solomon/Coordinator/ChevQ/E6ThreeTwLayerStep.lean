module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerAbs
public import CFSG.LieType.SeitzGeneration.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.Open

structure TwLayerFacts (Y : Type*) [Group Y] (𝒟 : Subgroup (MulAut Y)) : Prop where
  nonabelian : ∃ x y : Y, x * y ≠ y * x
  normal : ∀ N : Subgroup Y, N.Normal → N ≤ Subgroup.center Y ∨ N = ⊤
  plane : ∀ a₁ ∈ 𝒟, ∀ a₂ ∈ 𝒟, a₁ * a₂ = a₂ * a₁ → a₁ ^ 3 = 1 → a₂ ^ 3 = 1 →
    (∀ i j : ℕ, a₁ ^ i * a₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j) →
      PlaneGen (Subgroup.closure ({a₁, a₂} : Set (MulAut Y)))
  fixed : ∀ a ∈ 𝒟, a ^ 3 = 1 → ∃ k : Y, k ∉ Subgroup.center Y ∧ a k = k

section Realized

variable {Y G : Type*} [Group Y] [Group G]

@[expose] def realizedAut (E : Subgroup (MulAut G)) (ρ : Y →* G) : Subgroup (MulAut Y) where
  carrier := {a | ∃ ε ∈ E, ∀ s, ρ (a s) = ε (ρ s)}
  one_mem' := ⟨1, E.one_mem, fun s => rfl⟩
  mul_mem' := by
    rintro a b ⟨ε, hε, ha⟩ ⟨ε', hε', hb⟩
    refine ⟨ε * ε', E.mul_mem hε hε', fun s => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, ha, hb]
  inv_mem' := by
    rintro a ⟨ε, hε, ha⟩
    refine ⟨ε⁻¹, E.inv_mem hε, fun s => ?_⟩
    have h := ha (a⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    show ρ (a⁻¹ s) = ε⁻¹ (ρ s)
    rw [h]
    simp

theorem fixed_of_mem_zpowers_abs {σ : MulAut G} {x : G} (h : σ x = x) {ε : MulAut G}
    (hε : ε ∈ Subgroup.zpowers σ) : ε x = x := by
  have hσ : σ ∈ MulAction.stabilizer (MulAut G) x := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut G) x := Subgroup.zpowers_le.2 hσ
  have := hle hε
  rwa [MulAction.mem_stabilizer_iff] at this

theorem pow_apply_of_act_abs {ρ : Y →* G} {ε : MulAut G} {a : MulAut Y}
    (h : ∀ s, ε (ρ s) = ρ (a s)) (n : ℕ) (s : Y) : (ε ^ n) (ρ s) = ρ ((a ^ n) s) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, h, ih]

theorem pow_three_eq_one_of_act {ρ : Y →* G} (hρ : Function.Injective ρ) {ε : MulAut G}
    (hε3 : ε ^ 3 = 1) {a : MulAut Y} (h : ∀ s, ε (ρ s) = ρ (a s)) : a ^ 3 = 1 := by
  refine MulEquiv.ext fun s => hρ ?_
  rw [← pow_apply_of_act_abs h 3 s, hε3]
  rfl

theorem mul_comm_of_act {ρ : Y →* G} (hρ : Function.Injective ρ) {ε₁ ε₂ : MulAut G}
    (hc : ε₁ * ε₂ = ε₂ * ε₁) {a₁ a₂ : MulAut Y} (h₁ : ∀ s, ε₁ (ρ s) = ρ (a₁ s))
    (h₂ : ∀ s, ε₂ (ρ s) = ρ (a₂ s)) : a₁ * a₂ = a₂ * a₁ := by
  refine MulEquiv.ext fun s => hρ ?_
  have e1 : ρ ((a₁ * a₂) s) = (ε₁ * ε₂) (ρ s) := by
    rw [MulAut.mul_apply, MulAut.mul_apply, ← h₁ (a₂ s), ← h₂ s]
  have e2 : ρ ((a₂ * a₁) s) = (ε₂ * ε₁) (ρ s) := by
    rw [MulAut.mul_apply, MulAut.mul_apply, ← h₂ (a₁ s), ← h₁ s]
  rw [e1, e2, hc]

end Realized

section Acts

variable {Y G : Type*} [Group Y] [Group G] {𝒟 : Subgroup (MulAut Y)}

theorem le_seitzHyperGamma_of_acts_abs (M : TwLayerFacts Y 𝒟) {E : Subgroup (MulAut G)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) {ρ : Y →* G}
    (hρ : Function.Injective ρ) {σ : MulAut G} (hσ : σ ∈ E) (hσ1 : σ ≠ 1)
    (hσρ : ∀ s, σ (ρ s) = ρ s) (hact : ∀ ε ∈ E, ∃ a ∈ 𝒟, ∀ s, ε (ρ s) = ρ (a s)) :
    ρ.range ≤ seitzHyperGamma 3 E := by
  classical
  by_cases hker : ∃ ε ∈ E, ε ∉ Subgroup.zpowers σ ∧ ∀ s, ε (ρ s) = ρ s
  · obtain ⟨ε, hε, hεσ, hfix⟩ := hker
    rintro _ ⟨s, rfl⟩
    exact mem_seitzHyperGamma_of_fixed hE hcard hσ hε hσ1 hεσ (hσρ s) (hfix s)
  push Not at hker
  obtain ⟨ε₁, hε₁, hε₁σ⟩ := exists_notMem_zpowers hE hcard hσ
  obtain ⟨ε₂, hε₂, hε₂c⟩ := exists_notMem_closure_pair hE hcard hσ hε₁
  obtain ⟨a₁, ha₁D, ha₁⟩ := hact ε₁ hε₁
  obtain ⟨a₂, ha₂D, ha₂⟩ := hact ε₂ hε₂
  have hσ3 : σ ^ 3 = 1 := hE.2 σ hσ
  have hε₁3 : ε₁ ^ 3 = 1 := hE.2 ε₁ hε₁
  have hε₂3 : ε₂ ^ 3 = 1 := hE.2 ε₂ hε₂
  have hcomm : ε₁ * ε₂ = ε₂ * ε₁ :=
    congrArg Subtype.val (hE.1.is_comm.comm (⟨ε₁, hε₁⟩ : E) ⟨ε₂, hε₂⟩)
  have hR₁ : a₁ ∈ realizedAut E ρ := ⟨ε₁, hε₁, fun s => (ha₁ s).symm⟩
  have hR₂ : a₂ ∈ realizedAut E ρ := ⟨ε₂, hε₂, fun s => (ha₂ s).symm⟩
  have hind : ∀ i j : ℕ, a₁ ^ i * a₂ ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
    intro i j hij
    have hfix : ∀ s, (ε₁ ^ i * ε₂ ^ j) (ρ s) = ρ s := by
      intro s
      rw [MulAut.mul_apply, pow_apply_of_act_abs ha₂ j s, pow_apply_of_act_abs ha₁ i]
      have := congrArg (fun φ : MulAut Y => φ s) hij
      simp only [MulAut.mul_apply, MulAut.one_apply] at this
      rw [this]
    have hmem : ε₁ ^ i * ε₂ ^ j ∈ E := E.mul_mem (E.pow_mem hε₁ i) (E.pow_mem hε₂ j)
    have hin : ε₁ ^ i * ε₂ ^ j ∈ Subgroup.zpowers σ := by
      by_contra hn
      obtain ⟨s, hs⟩ := hker _ hmem hn
      exact hs (hfix s)
    exact pow_mul_pow_mem_zpowers hε₁σ hε₂c hσ3 hε₁3 hε₂3 hin
  have hPG : PlaneGen (Subgroup.closure ({a₁, a₂} : Set (MulAut Y))) :=
    M.plane a₁ ha₁D a₂ ha₂D (mul_comm_of_act hρ hcomm ha₁ ha₂)
      (pow_three_eq_one_of_act hρ hε₁3 ha₁) (pow_three_eq_one_of_act hρ hε₂3 ha₂) hind
  have hcl_le : Subgroup.closure ({a₁, a₂} : Set (MulAut Y)) ≤ realizedAut E ρ := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hR₁
    · rcases hx with rfl
      exact hR₂
  have hcl : planeClosure (Subgroup.closure ({a₁, a₂} : Set (MulAut Y))) ≤
      (seitzHyperGamma 3 E).comap ρ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro k ⟨a, ha, ha1, hak⟩
    obtain ⟨ε, hε, hεa⟩ := hcl_le ha
    have hεσ : ε ∉ Subgroup.zpowers σ := by
      intro hmem
      apply ha1
      refine MulEquiv.ext fun s => hρ ?_
      rw [hεa s, fixed_of_mem_zpowers_abs (hσρ s) hmem]
      rfl
    show ρ k ∈ seitzHyperGamma 3 E
    exact mem_seitzHyperGamma_of_fixed hE hcard hσ hε hσ1 hεσ (hσρ k) (by rw [← hεa k, hak])
  rintro _ ⟨s, rfl⟩
  have hs : s ∈ planeClosure (Subgroup.closure ({a₁, a₂} : Set (MulAut Y))) := by
    rw [hPG]
    exact Subgroup.mem_top s
  exact hcl hs

end Acts

section Perm

variable {Y G : Type*} [Group Y] [Group G] {𝒟 : Subgroup (MulAut Y)}

theorem le_seitzHyperGamma_of_perm_abs (M : TwLayerFacts Y 𝒟) {E : Subgroup (MulAut G)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) {ρ : Y →* G} {B C : Subgroup G}
    {σ τ f : MulAut G} (hσ : σ ∈ E) (hτ : τ ∈ E) (hf : f ∈ E) (hσ1 : σ ≠ 1)
    (hτσ : τ ∉ Subgroup.zpowers σ) (hfσ : f ∉ Subgroup.zpowers σ)
    (hσρ : ∀ s, σ (ρ s) = ρ s) (hσB : ∀ x ∈ B, σ x = x) (hσC : ∀ x ∈ C, σ x = x)
    (hcomB : ∀ s, ∀ y ∈ B, ρ s * y = y * ρ s) (hcomC : ∀ s, ∀ y ∈ C, ρ s * y = y * ρ s)
    (hτρ : ∀ s, τ (ρ s) ∈ B) (hτB : ∀ y ∈ B, τ y ∈ C)
    {a : MulAut Y} (haD : a ∈ 𝒟) (ha3 : a ^ 3 = 1) (hfρ : ∀ s, f (ρ s) = ρ (a s)) :
    ρ.range ≤ seitzHyperGamma 3 E := by
  have hτ3 : ∀ z, τ (τ (τ z)) = z := by
    intro z
    have := congrArg (fun φ : MulAut G => φ z) (hE.2 τ hτ)
    simpa [pow_succ, MulAut.mul_apply] using this
  have hQ : ∀ q x : Y, a q = q → x * q * x⁻¹ ∈ (seitzHyperGamma 3 E).comap ρ := by
    intro q x hq
    have hρq : ρ q ∈ seitzHyperGamma 3 E := by
      refine mem_seitzHyperGamma_of_fixed hE hcard hσ hf hσ1 hfσ (hσρ q) ?_
      rw [hfρ q, hq]
    have hz₂B : τ (ρ x) ∈ B := hτρ x
    have hz₃C : τ (τ (ρ x)) ∈ C := hτB _ hz₂B
    have hc₂ : Commute (ρ x) (τ (ρ x)) := hcomB x _ hz₂B
    have hc₃ : Commute (ρ x) (τ (τ (ρ x))) := hcomC x _ hz₃C
    have hy : ρ x * τ (ρ x) * τ (τ (ρ x)) ∈ seitzHyperGamma 3 E := by
      refine mem_seitzHyperGamma_of_fixed hE hcard hσ hτ hσ1 hτσ ?_ ?_
      · rw [map_mul, map_mul, hσρ x, hσB _ hz₂B, hσC _ hz₃C]
      · rw [map_mul, map_mul, hτ3 (ρ x)]
        calc τ (ρ x) * τ (τ (ρ x)) * ρ x = (τ (ρ x) * τ (τ (ρ x))) * ρ x := rfl
          _ = ρ x * (τ (ρ x) * τ (τ (ρ x))) := (hc₂.mul_right hc₃).eq.symm
          _ = ρ x * τ (ρ x) * τ (τ (ρ x)) := (mul_assoc _ _ _).symm
    have hw : Commute (τ (ρ x) * τ (τ (ρ x))) (ρ q) :=
      Commute.mul_left (hcomB q _ hz₂B).symm (hcomC q _ hz₃C).symm
    have hconj : ρ x * τ (ρ x) * τ (τ (ρ x)) * ρ q * (ρ x * τ (ρ x) * τ (τ (ρ x)))⁻¹ =
        ρ (x * q * x⁻¹) := by
      calc ρ x * τ (ρ x) * τ (τ (ρ x)) * ρ q * (ρ x * τ (ρ x) * τ (τ (ρ x)))⁻¹
          = ρ x * ((τ (ρ x) * τ (τ (ρ x))) * ρ q * (τ (ρ x) * τ (τ (ρ x)))⁻¹) * (ρ x)⁻¹ := by
            group
        _ = ρ x * ρ q * (ρ x)⁻¹ := by rw [hw.mul_inv_cancel]
        _ = ρ (x * q * x⁻¹) := by simp [map_mul, map_inv]
    show ρ (x * q * x⁻¹) ∈ seitzHyperGamma 3 E
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hρq) (Subgroup.inv_mem _ hy)
  obtain ⟨k, hkc, hak⟩ := M.fixed a haD ha3
  have hle : Subgroup.normalClosure ({k} : Set Y) ≤ (seitzHyperGamma 3 E).comap ρ := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Group.mem_conjugatesOfSet_iff.1 hz
    rw [Set.mem_singleton_iff] at hw
    subst hw
    obtain ⟨c, rfl⟩ := isConj_iff.1 hzw
    exact hQ _ c hak
  have hnot : ¬ Subgroup.normalClosure ({k} : Set Y) ≤ Subgroup.center Y := fun h =>
    hkc (h (Subgroup.subset_normalClosure (Set.mem_singleton k)))
  have htop : Subgroup.normalClosure ({k} : Set Y) = ⊤ :=
    (M.normal _ inferInstance).resolve_left hnot
  rintro _ ⟨s, rfl⟩
  have : s ∈ (seitzHyperGamma 3 E).comap ρ := by
    apply hle
    rw [htop]
    exact Subgroup.mem_top s
  exact this

end Perm

section Step

variable {Y G : Type*} [Group Y] [Group G] {𝒟 : Subgroup (MulAut Y)}

theorem layerStep_abs (M : TwLayerFacts Y 𝒟) {E : Subgroup (MulAut G)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 27) {ρ : Fin 3 → Y →* G}
    (hρ : ∀ i, Function.Injective (ρ i))
    (hcomm : ∀ i j, i ≠ j → ∀ s t, ρ i s * ρ j t = ρ j t * ρ i s)
    {σ : MulAut G} (hσ : σ ∈ E) (hσ1 : σ ≠ 1) (hσρ : ∀ i s, σ (ρ i s) = ρ i s)
    (hdec : ∀ ε ∈ E, ∃ k : Fin 3,
      (∀ i, (ρ i).range.map ε.toMonoidHom = (ρ (i + k)).range) ∧
        (k = 0 → ∀ i, ∃ a ∈ 𝒟, ∀ s, ε (ρ i s) = ρ i (a s)))
    (i : Fin 3) : (ρ i).range ≤ seitzHyperGamma 3 E := by
  classical
  set R : Fin 3 → Subgroup G := fun i => (ρ i).range with hR
  have hRcomm : ∀ i j, i ≠ j → ∀ x ∈ R i, ∀ y ∈ R j, x * y = y * x := by
    rintro i j hij _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact hcomm i j hij s t
  have hRne : ∀ i j, R i = R j → i = j := by
    intro i j hij
    by_contra hne
    obtain ⟨x, y, hxy⟩ := M.nonabelian
    apply hxy
    apply hρ i
    have hy : ρ i y ∈ R j := by
      rw [← hij]
      exact ⟨y, rfl⟩
    rw [map_mul, map_mul]
    exact hRcomm i j hne _ ⟨x, rfl⟩ _ hy
  have hSh_mul : ∀ {ε₁ ε₂ : MulAut G} {k₁ k₂ : Fin 3},
      (∀ i, (R i).map ε₁.toMonoidHom = R (i + k₁)) →
      (∀ i, (R i).map ε₂.toMonoidHom = R (i + k₂)) →
        ∀ i, (R i).map (ε₁ * ε₂).toMonoidHom = R (i + (k₁ + k₂)) := by
    intro ε₁ ε₂ k₁ k₂ h₁ h₂ i
    have e : (ε₁ * ε₂).toMonoidHom = ε₁.toMonoidHom.comp ε₂.toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, h₂, h₁, add_assoc, add_comm k₂ k₁]
  have hSh_unique : ∀ {ε : MulAut G} {k k' : Fin 3},
      (∀ i, (R i).map ε.toMonoidHom = R (i + k)) →
      (∀ i, (R i).map ε.toMonoidHom = R (i + k')) → k = k' := by
    intro ε k k' h h'
    have := hRne _ _ ((h 0).symm.trans (h' 0))
    simpa using this
  have hAct : ∀ ε ∈ E, (∀ i, (R i).map ε.toMonoidHom = R (i + 0)) →
      ∀ i, ∃ a ∈ 𝒟, ∀ s, ε (ρ i s) = ρ i (a s) := by
    intro ε hε h0
    obtain ⟨k, hk, hact⟩ := hdec ε hε
    exact hact (hSh_unique hk h0)
  by_cases hI : ∀ ε ∈ E, ∀ i, (R i).map ε.toMonoidHom = R (i + 0)
  · exact le_seitzHyperGamma_of_acts_abs M hE hcard (hρ i) hσ hσ1 (hσρ i)
      (fun ε hε => hAct ε hε (hI ε hε) i)
  obtain ⟨τ, hτ, hτ0⟩ : ∃ τ ∈ E, ¬ ∀ i, (R i).map τ.toMonoidHom = R (i + 0) := by
    by_contra hcon
    exact hI fun ε hε => by_contra fun hne => hcon ⟨ε, hε, hne⟩
  obtain ⟨kτ, hτk, -⟩ := hdec τ hτ
  have hkτ : kτ ≠ 0 := by
    rintro rfl
    exact hτ0 hτk
  have hσ3 : σ ^ 3 = 1 := hE.2 σ hσ
  obtain ⟨ε₁, hε₁, hε₁σ⟩ := exists_notMem_zpowers hE hcard hσ
  obtain ⟨ε₂, hε₂, hε₂c⟩ := exists_notMem_closure_pair hE hcard hσ hε₁
  have hε₁3 : ε₁ ^ 3 = 1 := hE.2 ε₁ hε₁
  have hε₂3 : ε₂ ^ 3 = 1 := hE.2 ε₂ hε₂
  obtain ⟨s₁, hs₁, -⟩ := hdec ε₁ hε₁
  obtain ⟨s₂, hs₂, -⟩ := hdec ε₂ hε₂
  have hε₂σ : ε₂ ∉ Subgroup.zpowers σ := fun h =>
    hε₂c ((Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))) h)
  obtain ⟨f, hf, hfσ, hf0⟩ : ∃ f ∈ E, f ∉ Subgroup.zpowers σ ∧
      ∀ i, (R i).map f.toMonoidHom = R (i + 0) := by
    by_cases h₁ : s₁ = 0
    · subst h₁
      exact ⟨ε₁, hε₁, hε₁σ, hs₁⟩
    by_cases h₂ : s₂ = 0
    · subst h₂
      exact ⟨ε₂, hε₂, hε₂σ, hs₂⟩
    by_cases h12 : s₁ = s₂
    · refine ⟨ε₁ * ε₂ ^ 2, E.mul_mem hε₁ (E.pow_mem hε₂ 2), ?_, ?_⟩
      · intro hmem
        have := pow_mul_pow_mem_zpowers (a := 1) (b := 2) hε₁σ hε₂c hσ3 hε₁3 hε₂3
          (by rwa [pow_one])
        exact absurd this.1 (by norm_num)
      · have h := hSh_mul hs₁ (hSh_mul hs₂ hs₂)
        have e : s₁ + (s₂ + s₂) = 0 := by
          rw [← h12]
          exact (by decide : ∀ s : Fin 3, s + (s + s) = 0) s₁
        rw [e] at h
        rwa [pow_two]
    · refine ⟨ε₁ * ε₂, E.mul_mem hε₁ hε₂, ?_, ?_⟩
      · intro hmem
        have := pow_mul_pow_mem_zpowers (a := 1) (b := 1) hε₁σ hε₂c hσ3 hε₁3 hε₂3
          (by rwa [pow_one, pow_one])
        exact absurd this.1 (by norm_num)
      · have h := hSh_mul hs₁ hs₂
        have e : s₁ + s₂ = 0 :=
          (by decide : ∀ a b : Fin 3, a ≠ 0 → b ≠ 0 → a ≠ b → a + b = 0) s₁ s₂ h₁ h₂ h12
        rwa [e] at h
  obtain ⟨a, haD, ha⟩ := hAct f hf hf0 i
  have ha3 : a ^ 3 = 1 := pow_three_eq_one_of_act (hρ i) (hE.2 f hf) ha
  have hτσ : τ ∉ Subgroup.zpowers σ := by
    intro hmem
    apply hτ0
    intro j
    have hfix : ∀ x ∈ R j, τ x = x := by
      rintro _ ⟨t, rfl⟩
      exact fixed_of_mem_zpowers_abs (hσρ j t) hmem
    ext y
    rw [add_zero]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, hfix x hx]
      exact hx
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  have hik : i ≠ i + kτ := (by decide : ∀ i k : Fin 3, k ≠ 0 → i ≠ i + k) i kτ hkτ
  have hik2 : i ≠ i + kτ + kτ := (by decide : ∀ i k : Fin 3, k ≠ 0 → i ≠ i + k + k) i kτ hkτ
  have hτρ : ∀ s, τ (ρ i s) ∈ R (i + kτ) := by
    intro s
    have : τ (ρ i s) ∈ (R i).map τ.toMonoidHom := ⟨ρ i s, ⟨s, rfl⟩, rfl⟩
    rwa [hτk i] at this
  have hτB : ∀ y ∈ R (i + kτ), τ y ∈ R (i + kτ + kτ) := by
    intro y hy
    have : τ y ∈ (R (i + kτ)).map τ.toMonoidHom := ⟨y, hy, rfl⟩
    rwa [hτk (i + kτ)] at this
  exact le_seitzHyperGamma_of_perm_abs M hE hcard (ρ := ρ i) (B := R (i + kτ))
    (C := R (i + kτ + kτ)) hσ hτ hf hσ1 hτσ hfσ (hσρ i)
    (by rintro _ ⟨t, rfl⟩; exact hσρ _ t) (by rintro _ ⟨t, rfl⟩; exact hσρ _ t)
    (fun s y hy => hRcomm i (i + kτ) hik (ρ i s) ⟨s, rfl⟩ y hy)
    (fun s y hy => hRcomm i (i + kτ + kτ) hik2 (ρ i s) ⟨s, rfl⟩ y hy) hτρ hτB haD ha3
    (fun s => ha s)

end Step

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

module

public import CFSG.Holt.H78.Sec4Toolkit
import CFSG.Holt.H78.Prelim

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise commutatorElement

section Statements

variable (G : Type) [Group G] [Finite G] (Ω : Type) [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

structure CaseAData (α β : Ω) where
  D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β)
  oddCore_eq_bot : jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥
  alt : ∀ i, factorImage _ _ (D.L i) (D.ρ i) = alternatingGroup (D.Ψc i)
  mod4 : ∀ i, Fintype.card (D.Ψc i) % 4 = 1
  five : Fintype.card D.ι = 1 → ∀ i, Fintype.card (D.Ψc i) = 5 →
    ¬ Odd (Nat.card (twoPointKernel G Ω α β))

@[expose] def IsTypeAAt (α β : Ω) : Prop := Nonempty (CaseAData G Ω α β)

@[expose] def IsTypeBAt (α β : Ω) : Prop :=
  IsNaturalSE (twoPointJ G Ω α β) ∧ Odd (Nat.card (twoPointKernel G Ω α β))

@[expose] def p46Orbit (v : G) (P : Subgroup (typeLSection G Ω v)) (α : Ω) : Set Ω :=
  {ω | ∃ p ∈ P, ∃ a : fixSet Ω (Subgroup.zpowers v), (a : Ω) = α ∧ ((p • a : _) : Ω) = ω}

structure Prop46Setup (α : Ω) (v : G) (P : Subgroup (typeLSection G Ω v)) : Prop where
  typeL : IsTypeL G Ω α v
  normal : P.Normal
  minimal : ∀ R ≤ P, R.Normal → R = ⊥ ∨ R = P
  le_oddCore : P ≤ CFSG.pPrimeCore 2 (typeLSection G Ω v)
  one_point : ∀ β ∈ p46Orbit G Ω v P α, β ≠ α → ∃! γ, γ ∈ holtDelta G Ω α β ∧ v • γ = γ
  exists_w : ∀ β ∈ p46Orbit G Ω v P α, β ≠ α →
    ∃ w ∈ longInvSwap G Ω α β, Commute w v ∧ w * v ∈ longInv G Ω
  typeAB : ∀ β ∈ p46Orbit G Ω v P α, β ≠ α → 1 < Nat.card (holtDelta G Ω α β) →
    IsTypeAAt G Ω α β ∨ IsTypeBAt G Ω α β

@[expose] def caseACentralizer (α β : Ω) (v : G) (Λ : Set Ω) : Subgroup G :=
  Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) ⊓
    (stabilizer G α ⊓ stabilizer G β) ⊓ fixingSubgroup G Λ

variable {G Ω} in
@[expose] def IsAdmissible {α β : Ω} (v w : G) (A : CaseAData G Ω α β) (γ : holtDelta G Ω α β)
    (Λ : Set Ω) : Prop :=
  (2 ≤ Fintype.card A.D.ι ∧ ∃ i₀, Λ = (↑) '' {δ : holtDelta G Ω α β |
    ∀ j, j ≠ i₀ → A.D.coord δ j = A.D.coord γ j}) ∨
  (Fintype.card A.D.ι = 1 ∧ ¬ Odd (Nat.card (twoPointKernel G Ω α β)) ∧
    Λ = holtDelta G Ω α β) ∨
  (Fintype.card A.D.ι = 1 ∧ Odd (Nat.card (twoPointKernel G Ω α β)) ∧
    ∃ O : Set Ω, O ⊆ holtDelta G Ω α β ∧ (γ : Ω) ∉ O ∧ O.ncard = 4 ∧ v • O = O ∧ w • O = O ∧
      Λ = insert (γ : Ω) O)

structure CaseAStart (α : Ω) (v : G) (P : Subgroup (typeLSection G Ω v))
    where
  β : Ω
  mem : β ∈ p46Orbit G Ω v P α
  ne : β ≠ α
  A : CaseAData G Ω α β
  w : G
  w_mem : w ∈ longInvSwap G Ω α β
  w_comm : Commute w v
  wv_mem : w * v ∈ longInv G Ω
  γ : holtDelta G Ω α β
  v_fix : v • (γ : Ω) = γ
  Λ : Set Ω
  admissible : IsAdmissible v w A γ Λ

variable {G Ω} in
@[expose] def IsKappaMaximal {α : Ω} {v : G}
    {P : Subgroup (typeLSection G Ω v)} (X : CaseAStart G Ω α v P)
    (V : Subgroup G) : Prop :=
  ∀ (X' : CaseAStart G Ω α v P) (V' : Subgroup G), V' ≤ caseACentralizer G Ω α X'.β v X'.Λ →
    IsPGroup 2 V' → X'.Λ.ncard < X.Λ.ncard ∨ (X'.Λ.ncard = X.Λ.ncard ∧ Nat.card V' ≤ Nat.card V)

@[expose] def CaseAStepA7 (α : Ω) (v : G)
    (P : Subgroup (typeLSection G Ω v)) : Prop :=
  ∀ (X : CaseAStart G Ω α v P) (V : Subgroup G),
    fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ) →
    X.w ∈ Subgroup.normalizer (V : Set G) → IsKappaMaximal X V →
    ∀ (r : G) (β₁ γ₁ : Ω), IsPGroup 2 (Subgroup.zpowers r) →
      r ∈ Subgroup.centralizer (V : Set G) → Commute r v → r • α = α →
      fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) = {α, β₁, γ₁} →
      β₁ ∈ p46Orbit G Ω v P α → γ₁ ∈ p46Orbit G Ω v P α → γ₁ ∈ holtDelta G Ω α β₁ →
      v • γ₁ = γ₁ → 5 ≤ (holtDelta G Ω α β₁ ∩ fixSet Ω V).ncard →
      (∃ (hb : X.β ∈ fixSet Ω V) (hb₁ : β₁ ∈ fixSet Ω V) (hc : (X.γ : Ω) ∈ fixSet Ω V)
          (hc₁ : γ₁ ∈ fixSet Ω V),
        (⟨β₁, hb₁⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
          ⟨X.β, hb⟩ ∧
        (⟨γ₁, hc₁⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
          ⟨X.γ, hc⟩) →
      ∀ A₁ : CaseAData G Ω α β₁, 2 ≤ Fintype.card A₁.D.ι →
        ∃ j, V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r ≤
          twoPointNormalizer G Ω α β₁ (A₁.D.L j)

end Statements

section CentralLift

variable {Y Q : Type*} [Group Y] [Group Q]

theorem commutatorElement_mul_mem_center {c d : Y} (hc : c ∈ Subgroup.center Y)
    (hd : d ∈ Subgroup.center Y) (a b : Y) : ⁅c * a, d * b⁆ = ⁅a, b⁆ := by
  have hc' := Subgroup.mem_center_iff.mp hc
  have hd' := Subgroup.mem_center_iff.mp hd
  have e1 : ⁅c * a, d * b⁆ = c * (a * (d * b) * a⁻¹) * c⁻¹ * (d * b)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e1, ← hc' (a * (d * b) * a⁻¹), mul_inv_cancel_right]
  have e2 : a * (d * b) * a⁻¹ * (d * b)⁻¹ = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by
    rw [← mul_assoc a d b, hd' a]; group
  rw [e2, ← hd' (a * b * a⁻¹ * b⁻¹), mul_inv_cancel_right, commutatorElement_def]

theorem commute_of_map_mem_commutator (π : Y →* Q) (hker : π.ker ≤ Subgroup.center Y) {a : Y}
    {P : Subgroup Q} (hP : P ≤ π.range) (hPa : ∀ q ∈ P, Commute (π a) q) {y : Y}
    (hy : π y ∈ ⁅P, P⁆) : Commute a y := by
  have hcent : ∀ z ∈ P.comap π, a * z * a⁻¹ * z⁻¹ ∈ Subgroup.center Y := fun z hz => by
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, (hPa _ hz).eq]
    group
  have hconj : ∀ z ∈ P.comap π, a * z * a⁻¹ = (a * z * a⁻¹ * z⁻¹) * z := fun z _ => by group
  have hcomm : ⁅P.comap π, P.comap π⁆ ≤ Subgroup.centralizer {a} := by
    rw [Subgroup.commutator_le]
    intro z₁ hz₁ z₂ hz₂
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : a * ⁅z₁, z₂⁆ * a⁻¹ = ⁅a * z₁ * a⁻¹, a * z₂ * a⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [hconj z₁ hz₁, hconj z₂ hz₂, commutatorElement_mul_mem_center (hcent z₁ hz₁)
      (hcent z₂ hz₂)] at h1
    calc ⁅z₁, z₂⁆ * a = a * ⁅z₁, z₂⁆ * a⁻¹ * a := by rw [h1]
      _ = a * ⁅z₁, z₂⁆ := by group
  have hmap : (⁅P.comap π, P.comap π⁆).map π = ⁅P, P⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq, inf_eq_right.mpr hP]
  rw [← hmap] at hy
  obtain ⟨c, hc, hcy⟩ := hy
  have hk : c⁻¹ * y ∈ Subgroup.center Y := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcy, inv_mul_cancel])
  have hy' : y = c * (c⁻¹ * y) := by group
  rw [hy']
  exact (show Commute a c from
    (Subgroup.mem_centralizer_singleton_iff.mp (hcomm hc)).symm).mul_right
    (show Commute a (c⁻¹ * y) from Subgroup.mem_center_iff.mp hk a)

end CentralLift

section FourCycle

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

theorem mem_commutator_fixingSubgroup_of_sign_eq_one {S : Set Ψ} [DecidablePred (· ∈ S)]
    (h5 : 5 ≤ Fintype.card {x // x ∉ S}) {σ : Equiv.Perm Ψ} (hσS : ∀ x ∈ S, σ x = x)
    (hσ : Equiv.Perm.sign σ = 1) :
    σ ∈ ⁅fixingSubgroup (Equiv.Perm Ψ) S, fixingSubgroup (Equiv.Perm Ψ) S⁆ := by
  set p : Ψ → Prop := fun x => x ∉ S
  set f : Equiv.Perm {x // p x} := (Equiv.Perm.subtypeEquivSubtypePerm p).symm
    ⟨σ, fun a ha => hσS a (not_not.mp ha)⟩
  have hf : Equiv.Perm.ofSubtype f = σ := by
    rw [← Equiv.Perm.subtypeEquivSubtypePerm_apply_coe, Equiv.apply_symm_apply]
  have hfa : f ∈ alternatingGroup {x // p x} := by
    rw [Equiv.Perm.mem_alternatingGroup, ← Equiv.Perm.sign_ofSubtype, hf, hσ]
  rw [← alternatingGroup.commutator_perm_eq (by rwa [Nat.card_eq_fintype_card])] at hfa
  have hle : (⊤ : Subgroup (Equiv.Perm {x // p x})).map Equiv.Perm.ofSubtype ≤
      fixingSubgroup (Equiv.Perm Ψ) S := by
    rintro _ ⟨τ, -, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (not_not.mpr hx)
  have hmap := Subgroup.map_commutator (⊤ : Subgroup (Equiv.Perm {x // p x})) ⊤
    Equiv.Perm.ofSubtype
  have hσmem : σ ∈ (commutator (Equiv.Perm {x // p x})).map Equiv.Perm.ofSubtype :=
    ⟨f, hfa, hf⟩
  rw [commutator_def, hmap] at hσmem
  exact Subgroup.commutator_mono hle hle hσmem

variable {Y : Type*} [Group Y]

theorem commute_of_map_eq_of_sq (π : Y →* Equiv.Perm Ψ) (hker : π.ker ≤ Subgroup.center Y)
    (hπ : Function.Surjective π) {h g : Equiv.Perm Ψ}
    (hgS : ∀ x, h x ≠ x → (g * (h ^ 2)⁻¹) x = x) (hsign : Equiv.Perm.sign (g * (h ^ 2)⁻¹) = 1)
    (h5 : 5 ≤ Fintype.card {x // h x = x} ∨ g = h ^ 2) {a b : Y} (ha : π a = h)
    (hb : π b = g) : Commute a b := by
  have hb' : b = b * (a ^ 2)⁻¹ * a ^ 2 := by group
  rw [hb']
  refine Commute.mul_right ?_ (Commute.pow_right (Commute.refl a) 2)
  have hπb : π (b * (a ^ 2)⁻¹) = g * (h ^ 2)⁻¹ := by rw [map_mul, map_inv, map_pow, ha, hb]
  rcases h5 with h5 | h5
  · set S : Set Ψ := {x | h x ≠ x}
    have h5' : 5 ≤ Fintype.card {x // x ∉ S} := by
      simpa [S, Set.mem_ofPred_eq, not_not] using h5
    refine commute_of_map_mem_commutator π hker (P := fixingSubgroup (Equiv.Perm Ψ) S)
      (fun q _ => hπ q) (fun q hq => ?_) ?_
    · rw [ha]
      refine (Equiv.Perm.Disjoint.commute fun x => ?_).symm
      by_cases hx : h x = x
      · exact Or.inr hx
      · exact Or.inl ((mem_fixingSubgroup_iff _).mp hq x hx)
    · rw [hπb]
      exact mem_commutator_fixingSubgroup_of_sign_eq_one h5' hgS hsign
  · have h1 : b * (a ^ 2)⁻¹ ∈ Subgroup.center Y := hker (by
      rw [MonoidHom.mem_ker, hπb, h5, mul_inv_cancel])
    exact (Subgroup.mem_center_iff.mp h1 a)

end FourCycle

section LiftsCommute

variable {Q : Type} [Group Q]

@[expose] def LiftsCommute (R : Subgroup Q) (q g : Q) : Prop :=
  ∀ (Y : Type) [Group Y] (π : Y →* Q), π.ker ≤ Subgroup.center Y → π.range = R →
    ∀ a b : Y, π a = q → π b = g → Commute a b

theorem liftsCommute_of_mem_commutator {R P : Subgroup Q} (hPR : P ≤ R)
    {q g : Q} (hPq : ∀ p ∈ P, Commute q p) (e : ℕ) (hg : (q ^ e)⁻¹ * g ∈ ⁅P, P⁆) :
    LiftsCommute R q g := by
  intro Y _ π hker hrange a b ha hb
  have hb' : b = a ^ e * ((a ^ e)⁻¹ * b) := by group
  rw [hb']
  refine (Commute.pow_right (Commute.refl a) e).mul_right ?_
  refine commute_of_map_mem_commutator π hker (P := P) (hPR.trans hrange.ge)
    (fun p hp => ha ▸ hPq p hp) ?_
  rwa [map_mul, map_inv, map_pow, ha, hb]

theorem LiftsCommute.zpow {R : Subgroup Q} {q g : Q} (hq : q ∈ R) (h : LiftsCommute R q g)
    (n : ℤ) : LiftsCommute R (q ^ n) g := by
  intro Y _ π hker hrange a b ha hb
  obtain ⟨a₀, ha₀⟩ : q ∈ π.range := hrange ▸ hq
  have hk : (a₀ ^ n)⁻¹ * a ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, ha₀, ha, inv_mul_cancel]
  rw [show a = a₀ ^ n * ((a₀ ^ n)⁻¹ * a) by group]
  exact ((h Y π hker hrange a₀ b ha₀ hb).zpow_left n).mul_left
    (Subgroup.mem_center_iff.mp (hker hk) b).symm

end LiftsCommute

section SylowTools

variable {X : Type*} [Group X] [Finite X]

theorem fusionIsSylowIn_inf_of_normal_subgroupOf {S H N : Subgroup X}
    (hS : fusionIsSylowIn 2 S H) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    fusionIsSylowIn 2 (S ⊓ N) N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, fun P hPN hP hle => ?_⟩
  obtain ⟨R, hPR, hR⟩ := exists_fusionIsSylowIn_ge hP (hPN.trans hNH)
  obtain ⟨k, hk, hkR⟩ := exists_mem_conj_of_fusionIsSylowIn hS hR
  have hconj : ∀ x ∈ P, k⁻¹ * x * k ∈ S ⊓ N := fun x hx => ⟨(hkR x).mp (hPR hx), by
    have := hN.conj_mem ⟨x, hNH (hPN hx)⟩ (Subgroup.mem_subgroupOf.mpr (hPN hx))
      ⟨k⁻¹, inv_mem hk⟩
    simpa [Subgroup.mem_subgroupOf] using this⟩
  have hcard : Nat.card P ≤ Nat.card ↥(S ⊓ N) := Nat.card_le_card_of_injective
    (fun x : P => (⟨k⁻¹ * x * k, hconj x x.2⟩ : ↥(S ⊓ N))) (fun x y h => by
      have := congrArg Subtype.val h
      simp only [mul_left_inj, mul_right_inj] at this
      exact Subtype.ext this)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem exists_fusionIsSylowIn_ge_mem_normalizer {V F : Subgroup X} (hV : IsPGroup 2 V)
    (hVF : V ≤ F) {s : X} (hs : IsPGroup 2 (Subgroup.zpowers s))
    (hsF : s ∈ Subgroup.normalizer (F : Set X)) (hsV : s ∈ Subgroup.normalizer (V : Set X)) :
    ∃ W : Subgroup X, V ≤ W ∧ fusionIsSylowIn 2 W F ∧ s ∈ Subgroup.normalizer (W : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 (V ⊔ Subgroup.zpowers s : Subgroup X) :=
    hV.to_sup_of_normal_left' hs (Subgroup.zpowers_le.mpr hsV)
  have hBH : V ⊔ Subgroup.zpowers s ≤ F ⊔ Subgroup.zpowers s := sup_le_sup_right hVF _
  obtain ⟨Q, hBQ, hQ⟩ := exists_fusionIsSylowIn_ge hB hBH
  have hFn : F ⊔ Subgroup.zpowers s ≤ Subgroup.normalizer (F : Set X) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hsF)
  have hN : (F.subgroupOf (F ⊔ Subgroup.zpowers s)).Normal :=
    Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left |>.mpr hFn
  refine ⟨Q ⊓ F, le_inf (le_sup_left.trans hBQ) hVF,
    fusionIsSylowIn_inf_of_normal_subgroupOf hQ le_sup_left hN, ?_⟩
  have hsQ : s ∈ Q := hBQ (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hsQ, hsF⟩

theorem exists_commute_inv_mul_mem (N : Subgroup X) [N.Normal] (hN : Odd (Nat.card N))
    {x : X} (hx : IsPGroup 2 (Subgroup.zpowers x)) {g : X} (hg : g * x * g⁻¹ * x⁻¹ ∈ N) :
    ∃ c : X, Commute c x ∧ c⁻¹ * g ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h18 := lemma_1_8_centralizer (p := 2) N (fun h2 => by
    obtain ⟨k, hk⟩ := hN; omega) hx
  have hmem : QuotientGroup.mk' N g ∈ Subgroup.centralizer
      (((Subgroup.zpowers x).map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) := by
    rw [MonoidHom.map_zpowers, Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    have hc : Commute (QuotientGroup.mk' N g) (QuotientGroup.mk' N x) := by
      have h1 : QuotientGroup.mk' N (g * x * g⁻¹ * x⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hg
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      exact commutatorElement_eq_one_iff_commute.mp (by rw [commutatorElement_def]; exact h1)
    exact ((hc.zpow_right k).eq).symm
  rw [← h18] at hmem
  obtain ⟨c, hc, hcg⟩ := hmem
  refine ⟨c, ?_, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp hc x (Subgroup.mem_zpowers x)).symm
  · rw [← QuotientGroup.eq]
    exact hcg


theorem exists_odd_normal_inv_mul_mem {M Z : Subgroup X} [hM : M.Normal] (hZM : Z ≤ M)
    (hZ : Z ≤ Subgroup.center X) (hZ2 : IsPGroup 2 Z)
    (h2 : ∀ g ∈ M, IsPGroup 2 (Subgroup.zpowers g) → g ∈ Z) :
    ∃ O : Subgroup X, O.Normal ∧ Odd (Nat.card O) ∧ O ≤ M ∧ ∀ m ∈ M, ∃ z ∈ Z, z⁻¹ * m ∈ O := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z' : Subgroup M := Z.subgroupOf M
  have hZ'n : Z'.Normal := ⟨fun n hn g => by
    have hc := Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp hn)) (g : X)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc,
      mul_inv_cancel_right]
    exact Subgroup.mem_subgroupOf.mp hn⟩
  have hcardZ' : Nat.card Z' = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ2
  have hodd : Odd Z'.index := by
    obtain ⟨Q⟩ : Nonempty (Sylow 2 M) := inferInstance
    have hQ : (Q : Subgroup M) ≤ Z' := fun q hq => by
      refine Subgroup.mem_subgroupOf.mpr (h2 q q.2 ?_)
      have h1 : IsPGroup 2 (Subgroup.zpowers q) := Q.isPGroup'.to_le (Subgroup.zpowers_le.mpr hq)
      have h2' := h1.map M.subtype
      rwa [MonoidHom.map_zpowers] at h2'
    have hdvd := Subgroup.index_dvd_of_le hQ
    have hQodd : ¬ 2 ∣ (Q : Subgroup M).index := Q.not_dvd_index
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => hQodd (h.trans hdvd))
  have hcop : Nat.Coprime (Nat.card Z') Z'.index := by
    rw [hcardZ', hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHcard : Nat.card H = Z'.index := hH.symm.index_eq_card.symm
  set O : Subgroup X := H.map M.subtype
  have hOcard : Nat.card O = Nat.card H := Subgroup.card_map_of_injective M.subtype_injective
  have hOodd : Odd (Nat.card O) := by rw [hOcard, hHcard]; exact hodd
  have hdec : ∀ m ∈ M, ∃ z ∈ Z, z⁻¹ * m ∈ O := fun m hm => by
    obtain ⟨⟨z, h⟩, hzh⟩ := hH.2 ⟨m, hm⟩
    refine ⟨z, Subgroup.mem_subgroupOf.mp z.2, ⟨h, h.2, ?_⟩⟩
    have h1 := congrArg Subtype.val hzh
    simp only [Subgroup.coe_mul] at h1
    rw [← h1, Subgroup.coe_subtype, inv_mul_cancel_left]
  have hoddmem : ∀ m ∈ M, Odd (orderOf m) → m ∈ O := fun m hm hmo => by
    obtain ⟨z, hz, hzm⟩ := hdec m hm
    have hcz : Commute z (z⁻¹ * m) := (Subgroup.mem_center_iff.mp (hZ hz) _).symm
    have hk : (z⁻¹ * m) ^ Nat.card O = 1 := by
      have := congrArg Subtype.val (pow_card_eq_one' (G := O) (x := ⟨_, hzm⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hmk : m ^ Nat.card O = z ^ Nat.card O := by
      rw [show m = z * (z⁻¹ * m) by group, hcz.mul_pow, hk, mul_one]
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hZ2) ⟨z, hz⟩
    have hza : orderOf z = 2 ^ a := by rw [← Subgroup.orderOf_mk z hz]; exact ha
    have hcopz : Nat.Coprime (orderOf z) (Nat.card O) := by
      rw [hza]; exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hOodd)
    have h1 : orderOf (m ^ Nat.card O) = orderOf z := by
      rw [hmk, hcopz.orderOf_pow]
    have h2 : orderOf (m ^ Nat.card O) ∣ orderOf m := orderOf_pow_dvd _
    rw [h1, hza] at h2
    have ha0 : a = 0 := by
      by_contra ha0
      exact Nat.not_even_iff_odd.mpr (hmo.of_dvd_nat h2) (Nat.even_pow.mpr ⟨even_two, ha0⟩)
    rw [ha0, pow_zero, orderOf_eq_one_iff] at hza
    rw [hza, inv_one, one_mul] at hzm
    exact hzm
  refine ⟨O, ⟨fun o ho g => ?_⟩, hOodd, Subgroup.map_subtype_le H, hdec⟩
  have hoM : o ∈ M := Subgroup.map_subtype_le H ho
  refine hoddmem _ (hM.conj_mem o hoM g) ?_
  rw [show g * o * g⁻¹ = MulAut.conj g o from rfl, MulEquiv.orderOf_eq]
  exact hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard O ho)

theorem exists_odd_pow_mem_of_fusionIsSylowIn {W F : Subgroup X} (hW : fusionIsSylowIn 2 W F)
    {k : X} (hkF : k ∈ F) (hkW : k ∈ Subgroup.normalizer (W : Set X)) :
    ∃ m : ℕ, Odd m ∧ k ^ m ∈ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, m, hm, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
  refine ⟨m, hm, ?_⟩
  have h1 : (k ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
  have hP : IsPGroup 2 (Subgroup.zpowers (k ^ m)) := IsPGroup.of_card (n := b) (by
    rw [Nat.card_zpowers, hb])
  have hN : k ^ m ∈ Subgroup.normalizer (W : Set X) := Subgroup.pow_mem _ hkW m
  have hsup : IsPGroup 2 (W ⊔ Subgroup.zpowers (k ^ m) : Subgroup X) :=
    hW.2.1.to_sup_of_normal_left' hP (Subgroup.zpowers_le.mpr hN)
  have heq := hW.2.2 _ (sup_le hW.1 (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hkF m))) hsup
    le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

omit [Finite X] in
theorem exists_mem_mul_mem_centralizer {W : Subgroup X} {v ℓ k : X} (hv : v * v = 1)
    (hℓ : ℓ ∈ Subgroup.centralizer (W : Set X)) (hkW : k ∈ Subgroup.normalizer (W : Set X))
    {m : ℕ} (hm : Odd m) (hkm : k ^ m ∈ W) (hvk : v = ℓ * k) :
    ∃ y ∈ W, ∃ x ∈ Subgroup.centralizer (W : Set X), v = y * x := by
  have key : ∀ n : ℕ, ∀ w ∈ W, (ℓ * k) ^ n * w * ((ℓ * k) ^ n)⁻¹ = k ^ n * w * (k ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      have hkn : k ^ (n + 1) * w * (k ^ (n + 1))⁻¹ ∈ W := by
        have := Subgroup.pow_mem _ hkW (n + 1)
        exact (Subgroup.mem_normalizer_iff.mp this w).mp hw
      have hc := Subgroup.mem_centralizer_iff.mp hℓ _ hkn
      have e1 : (ℓ * k) ^ (n + 1) * w * ((ℓ * k) ^ (n + 1))⁻¹ =
          ℓ * k * ((ℓ * k) ^ n * w * ((ℓ * k) ^ n)⁻¹) * k⁻¹ * ℓ⁻¹ := by
        rw [pow_succ']
        generalize (ℓ * k) ^ n = P
        group
      have e2 : k ^ (n + 1) = k * k ^ n := pow_succ' k n
      rw [e1, ih w hw]
      calc ℓ * k * (k ^ n * w * (k ^ n)⁻¹) * k⁻¹ * ℓ⁻¹
          = ℓ * (k ^ (n + 1) * w * (k ^ (n + 1))⁻¹) * ℓ⁻¹ := by
            rw [e2]; generalize k ^ n = P; group
        _ = k ^ (n + 1) * w * (k ^ (n + 1))⁻¹ := by rw [← hc, mul_inv_cancel_right]
  obtain ⟨j, rfl⟩ := hm
  have hvm : v ^ (2 * j + 1) = v := by
    rw [pow_succ, pow_mul, sq, hv, one_pow, one_mul]
  refine ⟨k ^ (2 * j + 1), hkm, (k ^ (2 * j + 1))⁻¹ * v, ?_, by group⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 := key (2 * j + 1) w hw
  rw [← hvk, hvm] at h1
  calc w * ((k ^ (2 * j + 1))⁻¹ * v)
      = (k ^ (2 * j + 1))⁻¹ * (k ^ (2 * j + 1) * w * (k ^ (2 * j + 1))⁻¹) * v := by group
    _ = (k ^ (2 * j + 1))⁻¹ * v * w := by rw [← h1]; group

end SylowTools

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]

variable (Ω) in
abbrev restrictCentralizer (V : Subgroup G) :
    Subgroup.centralizer (V : Set G) →* centralizerImage Ω V :=
  (MulAction.toPermHom (Subgroup.centralizer (V : Set G)) (fixSet Ω V)).rangeRestrict

abbrev psiHom {K X : Type*} [Group K] [MulAction K X] (D : HoltData K X) :
    jHull K X →* ∀ i, Equiv.Perm (D.Ψc i) :=
  MonoidHom.pi D.ρ

theorem Sec4Setting.exists_lift [FaithfulSMul G Ω] (hS : Sec4Setting G Ω) {V W : Subgroup G}
    (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V)) (hVW : V ≤ W)
    (hW : fusionIsSylowIn 2 W (fixingSubgroup G (fixSet Ω V)))
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V))
    (hker : jOrbitKernel (centralizerImage Ω V) (fixSet Ω V) =
      jOddCore (centralizerImage Ω V) (fixSet Ω V))
    {x : G} (hxW : x ∈ Subgroup.centralizer (W : Set G)) (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (hxJ : restrictCentralizer Ω V ⟨x, Subgroup.centralizer_le hVW hxW⟩ ∈
      jHull (centralizerImage Ω V) (fixSet Ω V))
    {Q : Subgroup (∀ i, Equiv.Perm (D.Ψc i))} (hQ2 : IsPGroup 2 Q) (hQ : Q ≤ (psiHom D).range)
    (hlc : ∀ q ∈ Q, LiftsCommute (psiHom D).range q (psiHom D ⟨_, hxJ⟩))
    (ω₀ : fixSet Ω V)
    (hxω : ∀ ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀, x • (ω : Ω) = ω)
    (hQω : ∀ q ∈ Q, ∀ i, q i (D.coord ω₀ i) = D.coord ω₀ i) :
    ∃ (E : Subgroup G) (hEW : E ≤ Subgroup.centralizer (W : Set G)), IsPGroup 2 E ∧
      (∀ e ∈ E, Commute e x) ∧ (∀ e ∈ E, e • (ω₀ : Ω) = ω₀) ∧
      (∀ (e : G) (he : e ∈ E), ∃ hJ : restrictCentralizer Ω V
        ⟨e, Subgroup.centralizer_le hVW (hEW he)⟩ ∈ jHull (centralizerImage Ω V) (fixSet Ω V),
          psiHom D ⟨_, hJ⟩ ∈ Q) ∧
      ∀ q ∈ Q, ∃ (e : G) (he : e ∈ E), ∃ hJ : restrictCentralizer Ω V
        ⟨e, Subgroup.centralizer_le hVW (hEW he)⟩ ∈ jHull (centralizerImage Ω V) (fixSet Ω V),
          psiHom D ⟨_, hJ⟩ = q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWV : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le hVW
  set A := Subgroup.centralizer (W : Set G)
  set f : A →* (centralizerImage Ω V) :=
    (restrictCentralizer Ω V).comp (Subgroup.inclusion hWV) with hfdef
  set X' : Subgroup A := (jHull (centralizerImage Ω V) (fixSet Ω V)).comap f with hX'def
  set fX : X' →* jHull (centralizerImage Ω V) (fixSet Ω V) :=
    (f.comp X'.subtype).codRestrict _ (fun c => c.2)
    with hfXdef
  set φ : X' →* ∀ i, Equiv.Perm (D.Ψc i) := (psiHom D).comp fX with hφdef
  have hfapp : ∀ (c : A) (ω : fixSet Ω V),
      (((f c : (centralizerImage Ω V)) : Equiv.Perm (fixSet Ω V)) ω : Ω) =
      (c : G) • (ω : Ω) := fun _ _ => rfl
  have hgen : ∀ π ∈ longInv (centralizerImage Ω V) (fixSet Ω V), ∃ c : X',
      (fX c : (centralizerImage Ω V)) = π := by
    intro π hπ
    obtain ⟨c₀, hc₀J, hc₀V, hc₀π⟩ := (hS.mem_longInv_centralizerImage_iff hV h3 π).mp hπ
    obtain ⟨c, hcJ, hcW, hcc⟩ := hS.frattini h3 hW.2.1 hW.1 hc₀J
      (centralizer_le_stabilizer_fixSet V hc₀V)
    have hfc : f ⟨c, hcW⟩ = π := Subtype.ext (Equiv.ext fun ω =>
      Subtype.ext ((hcc ω ω.2).trans (hc₀π ω).symm))
    exact ⟨⟨⟨c, hcW⟩, by rw [Subgroup.mem_comap, hfc]; exact Subgroup.subset_closure hπ⟩,
      hfc⟩
  have hsurj : Function.Surjective fX := by
    intro y
    obtain ⟨y, hy⟩ := y
    induction hy using Subgroup.closure_induction with
    | mem π hπ => obtain ⟨c, hc⟩ := hgen π hπ; exact ⟨c, Subtype.ext hc⟩
    | one => exact ⟨1, by rw [map_one]; rfl⟩
    | mul π₁ π₂ _ _ ih₁ ih₂ =>
      obtain ⟨c₁, hc₁⟩ := ih₁
      obtain ⟨c₂, hc₂⟩ := ih₂
      exact ⟨c₁ * c₂, by rw [map_mul, hc₁, hc₂]; rfl⟩
    | inv π _ ih =>
      obtain ⟨c, hc⟩ := ih
      exact ⟨c⁻¹, by rw [map_inv, hc]; rfl⟩
  set ι' : X' →* G := A.subtype.comp X'.subtype
  have hι' : Function.Injective ι' := A.subtype_injective.comp X'.subtype_injective
  set Zc : Subgroup X' := W.comap ι'
  have hkerφ : ∀ c : X', φ c = 1 ↔
      (fX c : (centralizerImage Ω V)) ∈ jOddCore (centralizerImage Ω V) (fixSet Ω V) :=
    fun c => by
    rw [← hker, D.mem_jOrbitKernel_iff_rho, funext_iff]
    rfl
  have hZM : Zc ≤ φ.ker := fun c hc => by
    rw [MonoidHom.mem_ker, hkerφ]
    have h1 : f c = 1 := Subtype.ext (Equiv.ext fun ω => Subtype.ext (by
      rw [hfapp]; exact (mem_fixingSubgroup_iff G).mp (hW.1 hc) ω ω.2))
    have h2 : (fX c : (centralizerImage Ω V)) = 1 := h1
    rw [h2]
    exact Subgroup.one_mem _
  have hZcen : Zc ≤ Subgroup.center X' := fun c hc => Subgroup.mem_center_iff.mpr fun d => by
    apply hι'
    rw [map_mul, map_mul]
    exact (Subgroup.mem_centralizer_iff.mp (d : A).2 _ hc).symm
  have hZ2 : IsPGroup 2 Zc := hW.2.1.comap_of_injective ι' hι'
  have hodd2 : ∀ c ∈ φ.ker, IsPGroup 2 (Subgroup.zpowers c) → c ∈ Zc := by
    intro c hc hc2
    have hO := (hkerφ c).mp hc
    have h1 : (fX c : (centralizerImage Ω V)) = 1 := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hc2)
      have h2 : orderOf (fX c : (centralizerImage Ω V)) ∣ 2 ^ n := by
        rw [← hn, Nat.card_zpowers, Subgroup.orderOf_coe]
        exact orderOf_map_dvd fX c
      have h3 : orderOf (fX c : (centralizerImage Ω V)) ∣
          Nat.card (jOddCore (centralizerImage Ω V) (fixSet Ω V)) := by
        rw [← Subgroup.orderOf_mk _ hO]; exact orderOf_dvd_natCard _
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
      have hk0 : k = 0 := by
        by_contra hk0
        rw [hk] at h3
        exact Nat.not_even_iff_odd.mpr (odd_card_jOddCore.of_dvd_nat h3)
          (Nat.even_pow.mpr ⟨even_two, hk0⟩)
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    have hfix : ι' c ∈ fixingSubgroup G (fixSet Ω V) := (mem_fixingSubgroup_iff G).mpr
      fun ω hω => by
        have := congrArg
          (fun π : (centralizerImage Ω V) => ((π : Equiv.Perm (fixSet Ω V)) ⟨ω, hω⟩ : Ω)) h1
        exact this
    have hc2' : IsPGroup 2 (Subgroup.zpowers (ι' c)) := by
      rw [← MonoidHom.map_zpowers]; exact hc2.map ι'
    have hsup : IsPGroup 2 (W ⊔ Subgroup.zpowers (ι' c) : Subgroup G) :=
      hW.2.1.to_sup_of_normal_left' hc2' (Subgroup.zpowers_le.mpr
        (Subgroup.centralizer_le_normalizer _ (c : A).2))
    have heq := hW.2.2 _ (sup_le hW.1 (Subgroup.zpowers_le.mpr hfix)) hsup le_sup_left
    show ι' c ∈ W
    rw [← heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  obtain ⟨O', hO'n, hO'odd, hO'M, hdec⟩ :=
    exists_odd_normal_inv_mul_mem (X := X') (M := φ.ker) (Z := Zc) hZM hZcen hZ2 hodd2
  set π' : X' ⧸ O' →* ∀ i, Equiv.Perm (D.Ψc i) := QuotientGroup.lift O' φ hO'M
  have hkerπ' : π'.ker ≤ Subgroup.center (X' ⧸ O') := by
    intro q hq
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    have hm : m ∈ φ.ker := hq
    obtain ⟨z, hz, hzm⟩ := hdec m hm
    have hmz : (m : X' ⧸ O') = (z : X' ⧸ O') := by
      rw [QuotientGroup.eq]
      have := inv_mem hzm
      rwa [mul_inv_rev, inv_inv] at this
    rw [hmz]
    refine Subgroup.mem_center_iff.mpr fun q' => ?_
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective q'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hZcen hz) d]
  have hrange : π'.range = (psiHom D).range := by
    ext q
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨fX c, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨c, rfl⟩ := hsurj y
      exact ⟨(c : X' ⧸ O'), rfl⟩
  set x' : X' := ⟨⟨x, hxW⟩, hxJ⟩
  have hx'2 : IsPGroup 2 (Subgroup.zpowers x') := by
    have h1 := hx2.comap_of_injective ι' hι'
    exact h1.to_le (Subgroup.zpowers_le.mpr (Subgroup.mem_comap.mpr (Subgroup.mem_zpowers x)))
  have hlift : ∀ q ∈ Q, ∃ c : X', Commute c x' ∧ φ c = q := by
    intro q hq
    obtain ⟨y, rfl⟩ := hQ hq
    obtain ⟨a', rfl⟩ := hsurj y
    have hcomm := hlc _ hq (X' ⧸ O') π' hkerπ' hrange (a' : X' ⧸ O') (x' : X' ⧸ O') rfl rfl
    have hcomm' : a' * x' * a'⁻¹ * x'⁻¹ ∈ O' := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hcomm.eq]
      group
    obtain ⟨c, hcx, hca⟩ := exists_commute_inv_mul_mem O' hO'odd hx'2 hcomm'
    refine ⟨c, hcx, ?_⟩
    have := hO'M hca
    rwa [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at this
  set E₁ : Subgroup X' := Subgroup.centralizer {x'} ⊓ Q.comap φ
  have hE₁ : E₁.map φ = Q := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun q hq => ?_
    obtain ⟨c, hcx, hcq⟩ := hlift q hq
    exact ⟨c, ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcx.eq, by
      show φ c ∈ Q
      rw [hcq]; exact hq⟩, hcq⟩
  have hQsyl : fusionIsSylowIn 2 Q (E₁.map φ) := by
    rw [hE₁]; exact ⟨le_rfl, hQ2, fun P hPQ _ hQP => le_antisymm hPQ hQP⟩
  obtain ⟨E₀, hE₀, hE₀Q⟩ := exists_fusionIsSylowIn_map_eq φ hQsyl
  have hcoordE : ∀ c ∈ E₀, ∀ i, D.coord ((fX c : centralizerImage Ω V) • ω₀) i =
      D.coord ω₀ i := fun c hc i => by
    rw [D.coord_smul (fX c) ω₀ i]
    exact hQω _ (hE₀.1 hc).2 i
  set B₀ : Set Ω := Subtype.val '' orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀
  have hmapB : ∀ c ∈ E₀, ∀ ω ∈ B₀, ι' c • ω ∈ B₀ := by
    rintro c hc _ ⟨ω, ⟨o, rfl⟩, rfl⟩
    have h1 : (fX c : centralizerImage Ω V) • ω₀ ∈
        orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀ :=
      (D.coord_eq_iff _ _).mp (funext fun i => (hcoordE c hc i).symm)
    obtain ⟨o', ho'⟩ := h1
    refine ⟨((fX c : centralizerImage Ω V) * (o : centralizerImage Ω V) *
      (fX c : centralizerImage Ω V)⁻¹ * (o' : centralizerImage Ω V)) • ω₀, ⟨⟨_, ?_⟩, rfl⟩, ?_⟩
    · exact mul_mem ((jOddCore_normal (G := centralizerImage Ω V) (Ω := fixSet Ω V)).conj_mem
        _ o.2 _) o'.2
    · have ho'' : (o' : centralizerImage Ω V) • ω₀ = (fX c : centralizerImage Ω V) • ω₀ := ho'
      have key : ((fX c : centralizerImage Ω V) * (o : centralizerImage Ω V) *
          (fX c : centralizerImage Ω V)⁻¹ * (o' : centralizerImage Ω V)) • ω₀ =
          (fX c : centralizerImage Ω V) • ((o : centralizerImage Ω V) • ω₀) := by
        rw [mul_smul, ho'', ← mul_smul, inv_mul_cancel_right, mul_smul]
      exact congrArg Subtype.val key
  have hstab : E₀.map ι' ≤ stabilizer G B₀ := by
    rintro _ ⟨c, hc, rfl⟩
    rw [mem_stabilizer_iff]
    refine Set.Subset.antisymm ?_ fun ω hω => ⟨ι' c⁻¹ • ω, hmapB c⁻¹ (inv_mem hc) ω hω, ?_⟩
    · rintro _ ⟨ω, hω, rfl⟩
      exact hmapB c hc ω hω
    · show ι' c • ι' c⁻¹ • ω = ω
      rw [map_inv, smul_inv_smul]
  have hB₀odd : Odd (Nat.card B₀) := by
    rw [Nat.card_image_of_injective Subtype.val_injective]
    exact odd_card_orbit_jOddCore ω₀
  have hP2 : IsPGroup 2 ((E₀.map ι').subgroupOf (stabilizer G B₀)) :=
    (hE₀.2.1.map ι').comap_of_injective _ (stabilizer G B₀).subtype_injective
  obtain ⟨α', hα'⟩ := fixSet_nonempty_of_odd (Ω := B₀) hB₀odd hP2
  have hα'fix : ∀ c ∈ E₀, ι' c • (α' : Ω) = α' := fun c hc =>
    congrArg Subtype.val (hα' ⟨ι' c, hstab ⟨c, hc, rfl⟩⟩ ⟨c, hc, rfl⟩)
  obtain ⟨_, ⟨o₀, rfl⟩, hα'eq⟩ := α'.2
  obtain ⟨c₀, hc₀⟩ := hsurj ⟨((o₀⁻¹ : jOddCore (centralizerImage Ω V) (fixSet Ω V)) :
    centralizerImage Ω V), jOddCore_le_jHull (o₀⁻¹).2⟩
  have hc₀M : c₀ ∈ φ.ker := (hkerφ c₀).mpr (by rw [hc₀]; exact (o₀⁻¹).2)
  obtain ⟨z, hz, hzo⟩ := hdec c₀ hc₀M
  have hfz : fX z = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun ω => Subtype.ext
    ((mem_fixingSubgroup_iff G).mp (hW.1 hz) ω ω.2)))
  have hgo : ι' (z⁻¹ * c₀) • (α' : Ω) = ω₀ := by
    have h1 : fX (z⁻¹ * c₀) = fX c₀ := by rw [map_mul, map_inv, hfz, inv_one, one_mul]
    rw [← hα'eq]
    have h2 := congrArg (fun y : jHull (centralizerImage Ω V) (fixSet Ω V) =>
      (((y : centralizerImage Ω V) • (o₀ • ω₀ : fixSet Ω V) : fixSet Ω V) : Ω)) (h1.trans hc₀)
    simp only at h2
    rw [show (((o₀⁻¹ : jOddCore (centralizerImage Ω V) (fixSet Ω V)) :
      centralizerImage Ω V) • (o₀ • ω₀ : fixSet Ω V)) = ω₀ from inv_smul_smul o₀ ω₀] at h2
    exact h2
  have hNodd : ¬ 2 ∣ Nat.card (O'.map ι') := by
    rw [Subgroup.card_map_of_injective hι']; exact hO'odd.not_two_dvd_nat
  have hSN : Subgroup.zpowers x ≤ Subgroup.normalizer ((O'.map ι' : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.le_normalizer_map ι' ⟨x', ?_, rfl⟩)
    rw [Subgroup.normalizer_eq_top_iff.mpr hO'n]; exact Subgroup.mem_top _
  have hxα' : (α' : Ω) ∈ fixSet Ω (Subgroup.zpowers x) := by
    rw [fixSet_zpowers, mem_fixedBy, ← hα'eq]; exact hxω _ ⟨o₀, rfl⟩
  have hxω₀ : (ω₀ : Ω) ∈ fixSet Ω (Subgroup.zpowers x) := by
    rw [fixSet_zpowers, mem_fixedBy]; exact hxω _ (mem_orbit_self ω₀)
  obtain ⟨m, ⟨⟨o₁, ho₁, rfl⟩, hmx⟩, hmα⟩ := exists_mem_centralizer_smul_eq hNodd hx2 hSN hxα'
    hxω₀ ⟨_, hzo, rfl⟩ hgo
  have ho₁x : Commute o₁ x' := by
    have h1 := Subgroup.mem_centralizer_iff.mp hmx x (Subgroup.mem_zpowers x)
    exact (hι' (by rw [map_mul, map_mul]; exact h1)).symm
  have hφo₁ : φ o₁ = 1 := hO'M ho₁
  have hcx : ∀ c ∈ E₀, Commute c x' := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mp (hE₀.1 hc).1
  set E : Subgroup G := (E₀.map (MulAut.conj o₁).toMonoidHom).map ι'
  have hEW : E ≤ Subgroup.centralizer (W : Set G) := by
    rintro _ ⟨y, -, rfl⟩; exact (y : A).2
  refine ⟨E, hEW, (hE₀.2.1.map _).map ι', ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ((ho₁x.mul_left (hcx c hc)).mul_left ho₁x.inv_left).map ι'
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    show ι' (o₁ * c * o₁⁻¹) • (ω₀ : Ω) = ω₀
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, ← hmα, inv_smul_smul, hα'fix c hc, hmα]
  · rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj o₁ c : X').2, ?_⟩
    show φ (o₁ * c * o₁⁻¹) ∈ Q
    rw [map_mul, map_mul, map_inv, hφo₁, one_mul, inv_one, mul_one]
    exact (hE₀.1 hc).2
  · intro q hq
    rw [← hE₀Q] at hq
    obtain ⟨c, hc, rfl⟩ := hq
    refine ⟨ι' (o₁ * c * o₁⁻¹), ⟨_, ⟨c, hc, rfl⟩, rfl⟩, (o₁ * c * o₁⁻¹ : X').2, ?_⟩
    show φ (o₁ * c * o₁⁻¹) = φ c
    rw [map_mul, map_mul, map_inv, hφo₁, one_mul, inv_one, mul_one]
theorem Sec4Setting.exists_lift_elt [FaithfulSMul G Ω] (hS : Sec4Setting G Ω) {V W : Subgroup G}
    (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V)) (hVW : V ≤ W)
    (hW : fusionIsSylowIn 2 W (fixingSubgroup G (fixSet Ω V)))
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V))
    (hker : jOrbitKernel (centralizerImage Ω V) (fixSet Ω V) =
      jOddCore (centralizerImage Ω V) (fixSet Ω V))
    {x : G} (hxW : x ∈ Subgroup.centralizer (W : Set G)) (hx2 : IsPGroup 2 (Subgroup.zpowers x))
    (hxJ : restrictCentralizer Ω V ⟨x, Subgroup.centralizer_le hVW hxW⟩ ∈
      jHull (centralizerImage Ω V) (fixSet Ω V))
    {q : ∀ i, Equiv.Perm (D.Ψc i)} (hq : q ∈ (psiHom D).range) {s : ℕ} (hqs : q ^ 2 ^ s = 1)
    (hlc : LiftsCommute (psiHom D).range q (psiHom D ⟨_, hxJ⟩)) (ω₀ : fixSet Ω V)
    (hxω : ∀ ω ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω₀, x • (ω : Ω) = ω)
    (hqω : ∀ i, q i (D.coord ω₀ i) = D.coord ω₀ i) :
    ∃ (r : G) (hr : r ∈ Subgroup.centralizer (W : Set G)), Commute r x ∧
      IsPGroup 2 (Subgroup.zpowers r) ∧ r • (ω₀ : Ω) = ω₀ ∧
      ∃ hJ : restrictCentralizer Ω V ⟨r, Subgroup.centralizer_le hVW hr⟩ ∈
        jHull (centralizerImage Ω V) (fixSet Ω V), psiHom D ⟨_, hJ⟩ = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (Subgroup.zpowers q) := by
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hqs)
    exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
  obtain ⟨E, hEW, hE2, hEx, hEω, -, hEq⟩ := hS.exists_lift hV h3 hVW hW D hker hxW hx2 hxJ hQ2
    (Subgroup.zpowers_le.mpr hq) (fun _ ⟨n, hn⟩ => hn ▸ hlc.zpow hq n) ω₀ hxω
    (fun _ ⟨n, hn⟩ i => by
      rw [← hn]
      show (q i ^ n) (D.coord ω₀ i) = D.coord ω₀ i
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self (hqω i) n)
  obtain ⟨r, hr, hJ, hrq⟩ := hEq q (Subgroup.mem_zpowers q)
  exact ⟨r, hEW hr, hEx r hr, hE2.to_le (Subgroup.zpowers_le.mpr hr), hEω r hr, hJ, hrq⟩

end Lift

end CFSG.Holt.H78

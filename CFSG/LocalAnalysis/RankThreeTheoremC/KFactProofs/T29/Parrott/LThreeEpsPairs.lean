module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsMat
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsGroup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

section Pair

variable {X : Type} [Group X]

@[expose] def IsE9Pair (L : Subgroup X) (a b : X) : Prop :=
  a ∈ L ∧ b ∈ L ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a * b = b * a ∧ a ≠ 1 ∧ b ∉ zpowers a

variable [Finite X] {L : Subgroup X} {a b : X}

theorem IsE9Pair.three_le (h : IsE9Pair L a b) {x : X} (hx3 : x ^ 3 = 1) (hxL : x ∉ L)
    (hxa : a * x = x * a) (hxb : b * x = x * b) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set X)) :=
  three_le_of_pair hx3 hxL h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2 hxa hxb

theorem IsE9Pair.elemAbelian (h : IsE9Pair L a b) :
    IsElemAbelian 3 (zpowers a ⊔ zpowers b) ∧ Nat.card ↥(zpowers a ⊔ zpowers b) = 9 ∧
      zpowers a ⊔ zpowers b ≤ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨haL, hbL, ha3, hb3, hab, ha1, hb⟩ := h
  have hel : ∀ c : X, c ^ 3 = 1 → IsElemAbelian 3 (zpowers c) := fun c hc => by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute (fun u hu v hv => ?_) (fun u hu => ?_)
    · rw [Set.mem_singleton_iff] at hu hv
      rw [hu, hv]
    · rw [Set.mem_singleton_iff] at hu
      rw [hu, hc]
  have hcomm : ∀ u ∈ zpowers a, ∀ v ∈ zpowers b, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact ((Commute.zpow_left hab i).zpow_right j).eq
  refine ⟨(hel a ha3).sup_of_commute (hel b hb3) hcomm, ?_,
    sup_le (zpowers_le.2 haL) (zpowers_le.2 hbL)⟩
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers a) hb3 hb
    (fun u hu => hcomm u hu b (Subgroup.mem_zpowers b)), Nat.card_zpowers,
    orderOf_eq_prime ha3 ha1]

theorem IsE9Pair.exists_E27 (h : IsE9Pair L a b) {φ : X} (hφ3 : φ ^ 3 = 1) (hφL : φ ∉ L)
    (hφa : a * φ = φ * a) (hφb : b * φ = φ * b) :
    IsElemAbelian 3 ((zpowers a ⊔ zpowers b) ⊔ zpowers φ) ∧
      Nat.card ↥((zpowers a ⊔ zpowers b) ⊔ zpowers φ) = 27 := by
  obtain ⟨hE, hE9, hEL⟩ := h.elemAbelian
  have hEC : zpowers a ⊔ zpowers b ≤ centralizer ({φ} : Set X) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hφa))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hφb))
  have hcomm : ∀ e ∈ zpowers a ⊔ zpowers b, e * φ = φ * e := fun e he =>
    mem_centralizer_singleton_iff.1 (hEC he)
  have hZ : IsElemAbelian 3 (zpowers φ) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute (fun u hu v hv => ?_) (fun u hu => ?_)
    · rw [Set.mem_singleton_iff] at hu hv
      rw [hu, hv]
    · rw [Set.mem_singleton_iff] at hu
      rw [hu, hφ3]
  have hcomm' : ∀ e ∈ zpowers a ⊔ zpowers b, ∀ c ∈ zpowers φ, e * c = c * e := by
    intro e he c hc
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    exact ((Commute.zpow_right (hcomm e he) k)).eq
  refine ⟨hE.sup_of_commute hZ hcomm', ?_⟩
  rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three _ hφ3
    (fun h' => hφL (hEL h')) hcomm, hE9]

theorem IsE9Pair.three_le_of_mem (h : IsE9Pair L a b) {φ : X} (hφ3 : φ ^ 3 = 1) (hφL : φ ∉ L)
    (hφa : a * φ = φ * a) (hφb : b * φ = φ * b) {u : X}
    (hu : u ∈ (zpowers a ⊔ zpowers b) ⊔ zpowers φ) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({u} : Set X)) := by
  obtain ⟨hV, hV27⟩ := h.exists_E27 hφ3 hφL hφa hφb
  have hle : (zpowers a ⊔ zpowers b) ⊔ zpowers φ ≤ centralizer ({u} : Set X) := fun v hv =>
    mem_centralizer_singleton_iff.2 (hV.comm hv hu)
  exact CFSG.SectionRank.le_pRank (by norm_num) hle hV (k := 3) (by rw [hV27]; norm_num)

theorem IsE9Pair.three_le_left (h : IsE9Pair L a b) {φ : X} (hφ3 : φ ^ 3 = 1) (hφL : φ ∉ L)
    (hφa : a * φ = φ * a) (hφb : b * φ = φ * b) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({a} : Set X)) :=
  h.three_le_of_mem hφ3 hφL hφa hφb
    (le_sup_left (a := zpowers a ⊔ zpowers b) (le_sup_left (b := zpowers b) (mem_zpowers a)))

theorem IsE9Pair.three_le_right (h : IsE9Pair L a b) {φ : X} (hφ3 : φ ^ 3 = 1) (hφL : φ ∉ L)
    (hφa : a * φ = φ * a) (hφb : b * φ = φ * b) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({b} : Set X)) :=
  h.three_le_of_mem hφ3 hφL hφa hφb
    (le_sup_left (a := zpowers a ⊔ zpowers b) (le_sup_right (a := zpowers a) (mem_zpowers b)))

end Pair

section Matrix

variable {K : Type} [Field K]

@[expose] def IsPairExact (A B : GL (Fin 3) K) : Prop :=
  A ^ 3 = 1 ∧ B ^ 3 = 1 ∧ A * B = B * A ∧ A ∉ StatedScalars (Fin 3) K ∧
    ∀ k : ℕ, k < 3 → B ≠ A ^ k

@[expose] def IsPairMod (A B : GL (Fin 3) K) : Prop :=
  A ^ 3 ∈ StatedScalars (Fin 3) K ∧ B ^ 3 ∈ StatedScalars (Fin 3) K ∧
    A * B * A⁻¹ * B⁻¹ ∈ StatedScalars (Fin 3) K ∧ A ∉ StatedScalars (Fin 3) K ∧
    ∀ k : ℕ, k < 3 → B * (A ^ k)⁻¹ ∉ StatedScalars (Fin 3) K

theorem IsPairExact.conj {A B : GL (Fin 3) K} (h : IsPairExact A B) (g : GL (Fin 3) K) :
    IsPairExact (g * A * g⁻¹) (g * B * g⁻¹) := by
  obtain ⟨hA, hB, hAB, hAs, hk⟩ := h
  refine ⟨by rw [conj_pow, hA, mul_one, mul_inv_cancel], by rw [conj_pow, hB, mul_one,
    mul_inv_cancel], ?_, fun h' => hAs ((conj_mem_statedScalars_iff g A).1 h'), fun k hk3 h' => ?_⟩
  · calc g * A * g⁻¹ * (g * B * g⁻¹) = g * (A * B) * g⁻¹ := by group
      _ = g * (B * A) * g⁻¹ := by rw [hAB]
      _ = g * B * g⁻¹ * (g * A * g⁻¹) := by group
  · rw [conj_pow] at h'
    exact hk k hk3 (mul_left_cancel (mul_right_cancel h'))

theorem IsPairMod.conj {A B : GL (Fin 3) K} (h : IsPairMod A B) (g : GL (Fin 3) K) :
    IsPairMod (g * A * g⁻¹) (g * B * g⁻¹) := by
  obtain ⟨hA, hB, hAB, hAs, hk⟩ := h
  refine ⟨?_, ?_, ?_, fun h' => hAs ((conj_mem_statedScalars_iff g A).1 h'), fun k hk3 h' => ?_⟩
  · rw [conj_pow]
    exact (conj_mem_statedScalars_iff g _).2 hA
  · rw [conj_pow]
    exact (conj_mem_statedScalars_iff g _).2 hB
  · have e : g * A * g⁻¹ * (g * B * g⁻¹) * (g * A * g⁻¹)⁻¹ * (g * B * g⁻¹)⁻¹ =
        g * (A * B * A⁻¹ * B⁻¹) * g⁻¹ := by group
    rw [e]
    exact (conj_mem_statedScalars_iff g _).2 hAB
  · rw [conj_pow] at h'
    have e : g * B * g⁻¹ * (g * A ^ k * g⁻¹)⁻¹ = g * (B * (A ^ k)⁻¹) * g⁻¹ := by group
    rw [e] at h'
    exact hk k hk3 ((conj_mem_statedScalars_iff g _).1 h')

theorem diagUnits_inv (a b c : Kˣ) : (diagUnits a b c)⁻¹ = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, diagUnits_mul, mul_inv_cancel, mul_inv_cancel, mul_inv_cancel]
  apply Units.ext
  rw [Units.val_one, coe_diagUnits, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem isPairExact_diagTau_scalar {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {t : Kˣ}
    (ht : (t : K) = τ) :
    IsPairExact (diagTau hτ) (Matrix.GeneralLinearGroup.scalar (Fin 3) t) := by
  obtain ⟨u, hu, he⟩ := diagTau_eq_diagUnits' hτ
  have ht3 : t ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, ht, hτ, Units.val_one])
  refine ⟨diagTau_pow_three hτ, by rw [← map_pow, ht3, map_one],
    (commute_of_mem_statedScalars ⟨t, rfl⟩ _), diagTau_not_mem_statedScalars hτ hτ1,
    fun k _ h => ?_⟩
  have h22 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 2) h
  simp only [he, diagUnits_pow, coe_diagUnits, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h22
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, one_pow,
    Units.val_one] at h22
  exact hτ1 (by rw [← ht, h22])

theorem isPairMod_diagTau_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    IsPairMod (diagTau hτ) cycThree := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    simp at hτ
  obtain ⟨u, hu, he⟩ := diagTau_eq_diagUnits' hτ
  refine ⟨by rw [diagTau_pow_three]; exact ⟨1, by rw [map_one]⟩,
    by rw [cycThree_pow_three]; exact ⟨1, by rw [map_one]⟩, ?_,
    diagTau_not_mem_statedScalars hτ hτ1, fun k _ => ?_⟩
  · rw [diagTau_conj_cycThree hτ hτ0, mul_inv_cancel_right]
    exact ⟨_, rfl⟩
  · rw [he, diagUnits_pow, diagUnits_inv]
    exact cycThree_mul_diagUnits_not_mem _ _ _

theorem isPairMod_diagTau_diag {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {e ζ : Kˣ}
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    IsPairMod (diagTau hτ) (diagUnits (e * ζ) ζ ζ) := by
  obtain ⟨u, hu, he⟩ := diagTau_eq_diagUnits' hτ
  refine ⟨by rw [diagTau_pow_three]; exact ⟨1, by rw [map_one]⟩, ?_, ?_,
    diagTau_not_mem_statedScalars hτ hτ1, fun k _ hs => ?_⟩
  · rw [diagUnits_pow, diagUnits_mem_statedScalars_iff, mul_pow, he3, one_mul]
    exact ⟨rfl, rfl⟩
  · rw [he, diagUnits_commute, mul_inv_cancel_right, mul_inv_cancel]
    exact ⟨1, by rw [map_one]⟩
  · rw [he, diagUnits_pow, diagUnits_inv, diagUnits_mul, diagUnits_mem_statedScalars_iff] at hs
    obtain ⟨h1, h2⟩ := hs
    have hA : u ^ k = e := by
      have h3 : ζ * u ^ k = e * ζ := by
        calc ζ * u ^ k = (e * ζ * (u ^ k)⁻¹) * u ^ k := by rw [← h2, one_pow, inv_one, mul_one]
          _ = e * ζ := inv_mul_cancel_right _ _
      exact mul_left_cancel (h3.trans (mul_comm e ζ))
    have hB : (u ^ 2) ^ k = 1 := by
      have h3 : ζ * ((u ^ 2) ^ k)⁻¹ = ζ * 1 := by
        rw [h1, hA, mul_one, mul_comm e ζ, mul_inv_cancel_right]
      exact inv_eq_one.1 (mul_left_cancel h3)
    have hC : e ^ 2 = 1 := by
      rw [← hA, ← pow_mul, mul_comm, pow_mul]
      exact hB
    apply he1
    calc e = e ^ 3 * (e ^ 2)⁻¹ := by group
      _ = 1 := by rw [he3, hC, inv_one, mul_one]

end Matrix

namespace LModel

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem mem_center_of_mem_statedScalars (M : LModel L π p f K ν) {s : ↥(slPi π 3 (p ^ f) K)}
    (hs : (s : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) :
    s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K) := by
  rw [center_slPi_eq M.piField M.modThree, Subgroup.mem_subgroupOf]
  exact hs

theorem map_eq_one_of_mem_statedScalars (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1) {s : ↥(slPi π 3 (p ^ f) K)}
    (hs : (s : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) : ν s = 1 :=
  hproj s (M.mem_center_of_mem_statedScalars hs)

theorem isE9Pair_of_exact (M : LModel L π p f K ν) (hinj : Function.Injective ν)
    {s₁ s₂ : ↥(slPi π 3 (p ^ f) K)} (h : IsPairExact (s₁ : GL (Fin 3) K) s₂) :
    IsE9Pair L ((ν s₁ : ↥L) : X) ((ν s₂ : ↥L) : X) := by
  obtain ⟨h1, h2, h12, hs, hk⟩ := h
  have e1 : s₁ ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h1)
  have e2 : s₂ ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h2)
  refine ⟨(ν s₁).2, (ν s₂).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, e1, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, ← map_pow, e2, map_one, Subgroup.coe_one]
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext h12
  · intro h1'
    apply hs
    have : s₁ = 1 := hinj (by rw [map_one]; exact Subtype.ext h1')
    rw [this]
    exact ⟨1, by rw [map_one]; rfl⟩
  · intro hmem
    have hmem' : ν s₂ ∈ zpowers (ν s₁) := by
      obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk')⟩
    have h3 : ν s₁ ^ 3 = 1 := by rw [← map_pow, e1, map_one]
    rcases eq_of_mem_zpowers_of_pow_three h3 hmem' with h0 | h0 | h0
    · exact hk 0 (by norm_num) (by
        have := hinj (h0.trans (map_one ν).symm)
        rw [this, pow_zero]; rfl)
    · exact hk 1 (by norm_num) (by
        have := hinj h0
        rw [this, pow_one])
    · exact hk 2 (by norm_num) (by
        have := hinj (h0.trans (map_pow ν s₁ 2).symm)
        rw [this, SubgroupClass.coe_pow])

theorem isE9Pair_of_mod (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1)
    {s₁ s₂ : ↥(slPi π 3 (p ^ f) K)} (h : IsPairMod (s₁ : GL (Fin 3) K) s₂) :
    IsE9Pair L ((ν s₁ : ↥L) : X) ((ν s₂ : ↥L) : X) := by
  obtain ⟨h1, h2, h12, hs, hk⟩ := h
  have e1 : ν s₁ ^ 3 = 1 := by
    rw [← map_pow]
    exact M.map_eq_one_of_mem_statedScalars hproj (by rw [SubgroupClass.coe_pow]; exact h1)
  have e2 : ν s₂ ^ 3 = 1 := by
    rw [← map_pow]
    exact M.map_eq_one_of_mem_statedScalars hproj (by rw [SubgroupClass.coe_pow]; exact h2)
  refine ⟨(ν s₁).2, (ν s₂).2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, e1, Subgroup.coe_one]
  · rw [← Subgroup.coe_pow, e2, Subgroup.coe_one]
  · have hc : ν (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) = 1 :=
      M.map_eq_one_of_mem_statedScalars hproj (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact h12)
    simp only [map_mul, map_inv] at hc
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul]
    congr 1
    calc ν s₁ * ν s₂ = ν s₁ * ν s₂ * (ν s₁)⁻¹ * (ν s₂)⁻¹ * (ν s₂ * ν s₁) := by group
      _ = ν s₂ * ν s₁ := by rw [hc, one_mul]
  · intro h1'
    exact hs (M.ker_scalar s₁ (Subtype.ext h1'))
  · intro hmem
    have hmem' : ν s₂ ∈ zpowers (ν s₁) := by
      obtain ⟨k, hk'⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk')⟩
    have key : ∀ k : ℕ, ν s₂ = ν s₁ ^ k →
        (s₂ : GL (Fin 3) K) * ((s₁ : GL (Fin 3) K) ^ k)⁻¹ ∈ StatedScalars (Fin 3) K := by
      intro k hk'
      have : ν (s₂ * (s₁ ^ k)⁻¹) = 1 := by rw [map_mul, map_inv, map_pow, hk', mul_inv_cancel]
      have := M.ker_scalar _ this
      simpa using this
    rcases eq_of_mem_zpowers_of_pow_three e1 hmem' with h0 | h0 | h0
    · exact hk 0 (by norm_num) (key 0 (by rw [pow_zero]; exact h0))
    · exact hk 1 (by norm_num) (key 1 (by rw [pow_one]; exact h0))
    · exact hk 2 (by norm_num) (key 2 h0)

end LModel

section Fixed

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem IsLiftAt.commute_of_commute {x : X} {y : GL (Fin 3) K} (hx : IsLiftAt ν x y)
    {s : ↥(slPi π 3 (p ^ f) K)} (hs : y * s = s * y) :
    ((ν s : ↥L) : X) * x = x * ((ν s : ↥L) : X) := by
  have h := hx.act s s (by rw [hs, mul_inv_cancel_right])
  calc ((ν s : ↥L) : X) * x = x * ((ν s : ↥L) : X) * x⁻¹ * x := by rw [h]
    _ = x * ((ν s : ↥L) : X) := by group

theorem IsFieldAt.commute_of_eq {x : X} {σ : K ≃+* K} {H : GL (Fin 3) K}
    (hx : IsFieldAt ν x σ H) {s : ↥(slPi π 3 (p ^ f) K)}
    (hs : frobGL σ (H⁻¹ * s * H) = H⁻¹ * s * H) :
    ((ν s : ↥L) : X) * x = x * ((ν s : ↥L) : X) := by
  have h := hx.act s s (by rw [hs]; group)
  calc ((ν s : ↥L) : X) * x = x * ((ν s : ↥L) : X) * x⁻¹ * x := by rw [h]
    _ = x * ((ν s : ↥L) : X) := by group

theorem IsFieldAt.commute_of_mod (M : LModel L π p f K ν)
    (hproj : ∀ s ∈ Subgroup.center ↥(slPi π 3 (p ^ f) K), ν s = 1) {x : X} {σ : K ≃+* K}
    {H : GL (Fin 3) K} (hx : IsFieldAt ν x σ H) {s : ↥(slPi π 3 (p ^ f) K)}
    (hs : frobGL σ (H⁻¹ * s * H) * (H⁻¹ * s * H)⁻¹ ∈ StatedScalars (Fin 3) K) :
    ((ν s : ↥L) : X) * x = x * ((ν s : ↥L) : X) := by
  set t := M.fieldBy σ hx.mem s with ht
  have h := hx.act s t (M.coe_fieldBy σ hx.mem s)
  have hts : ν t = ν s := by
    have : ν (t * s⁻¹) = 1 := M.map_eq_one_of_mem_statedScalars hproj (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ht, M.coe_fieldBy]
      have e : H * frobGL σ (H⁻¹ * ↑s * H) * H⁻¹ * (↑s)⁻¹ =
          H * (frobGL σ (H⁻¹ * ↑s * H) * (H⁻¹ * ↑s * H)⁻¹) * H⁻¹ := by group
      rw [e]
      exact (conj_mem_statedScalars_iff H _).2 hs)
    rw [map_mul, map_inv, mul_inv_eq_one] at this
    exact this
  rw [hts] at h
  calc ((ν s : ↥L) : X) * x = x * ((ν s : ↥L) : X) * x⁻¹ * x := by rw [h]
    _ = x * ((ν s : ↥L) : X) := by group

end Fixed

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Main

public section

namespace CFSG.ClassicalInvolution.Asc77.MuTab.OrthHub

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped MatrixGroups

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def eps (K : Type) [Field K] : Fin 6 → K := ![1, 1, 1, 1, -1, -1]

theorem eps_mul_self (i : Fin 6) : eps K i * eps K i = 1 := by
  fin_cases i <;> simp [eps]

theorem eps_ne_zero (i : Fin 6) : eps K i ≠ 0 := by
  intro h
  have := eps_mul_self (K := K) i
  rw [h] at this
  simp at this

structure Sys (Q : QuadraticForm K V) where
  o : Fin 6 → V
  sq : ∀ i, Q (o i) = eps K i
  orth : ∀ i j, i ≠ j → polar Q (o i) (o j) = 0

namespace Sys

variable {Q : QuadraticForm K V} (S : Sys Q)

@[expose] def dm : (Fin 6 → K) →ₗ[K] V where
  toFun c := ∑ i, c i • S.o i
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [Finset.smul_sum, smul_smul]

theorem dm_apply (c : Fin 6 → K) : S.dm c = ∑ i, c i • S.o i := rfl

theorem polar_o_o (i j : Fin 6) : polar Q (S.o i) (S.o j) = if i = j then 2 * eps K i else 0 := by
  by_cases h : i = j
  · subst h
    simp only [polar_self, S.sq, nsmul_eq_mul, ite_true]
    norm_num
  · simp [h, S.orth i j h]

theorem polar_right_dm (x : V) (c : Fin 6 → K) :
    polar Q x (S.dm c) = ∑ i, c i * polar Q x (S.o i) := by
  rw [dm_apply]
  have : ∀ y : V, polar Q x y = polarBilin Q x y := fun y => rfl
  rw [this, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

theorem polar_dm_o (c : Fin 6 → K) (k : Fin 6) :
    polar Q (S.dm c) (S.o k) = c k * (2 * eps K k) := by
  rw [polar_comm, polar_right_dm]
  simp only [polar_o_o, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem polar_dm_dm (c d : Fin 6 → K) :
    polar Q (S.dm c) (S.dm d) = ∑ i, d i * (c i * (2 * eps K i)) := by
  rw [polar_right_dm]
  exact Finset.sum_congr rfl fun i _ => by rw [polar_dm_o]

theorem Q_dm (h2 : (2 : K) ≠ 0) (c : Fin 6 → K) : Q (S.dm c) = ∑ i, eps K i * (c i * c i) := by
  have h := polar_dm_dm S c c
  rw [polar_self] at h
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at h
  apply mul_left_cancel₀ h2
  rw [h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dm_injective (h2 : (2 : K) ≠ 0) : Function.Injective S.dm := by
  intro c d h
  funext k
  have := polar_dm_o S c k
  rw [h, polar_dm_o] at this
  have h3 : (2 : K) * eps K k ≠ 0 := mul_ne_zero h2 (eps_ne_zero k)
  exact (mul_right_cancel₀ h3 this).symm

theorem incl_coords_eq (fr : Frame Q) (x : V) :
    fr.incl (fr.coords x) = polar Q x fr.f₁ • fr.e₁ + polar Q x fr.e₁ • fr.f₁ +
      polar Q x fr.f₂ • fr.e₂ + polar Q x fr.e₂ • fr.f₂ := by
  rw [Frame.incl_apply, Frame.coords_apply]
  simp

@[expose] def D (m : Fin 6 → K) (x : V) : V :=
  x - S.dm (fun i => m i * eps K i * polar Q x (S.o i))

@[expose] def hubE1 (a b : K) : Fin 6 → K := ![1, 0, a, b, 0, 0]

@[expose] def hubF1 (a b q : K) : Fin 6 → K := ![q, 0, -(q * a), -(q * b), 0, 0]

@[expose] def hubE2 (a b : K) : Fin 6 → K := ![0, 1, -b, a, 0, 0]

@[expose] def hubF2 (a b q : K) : Fin 6 → K := ![0, q, q * b, -(q * a), 0, 0]

@[expose] def hubFrame (h2 : (2 : K) ≠ 0) {a b q : K} (hab : a * a + b * b = -1)
    (hq : 4 * q = 1) : Frame Q where
  P := ⟨S.dm (hubE1 a b), S.dm (hubF1 a b q), by
      rw [Q_dm S h2]
      simp [hubE1, Fin.sum_univ_six, eps]
      linear_combination hab, by
      rw [Q_dm S h2]
      simp [hubF1, Fin.sum_univ_six, eps]
      linear_combination (q * q) * hab, by
      rw [polar_dm_dm]
      simp [hubE1, hubF1, Fin.sum_univ_six, eps]
      linear_combination (-2 * q) * hab + hq⟩
  P' := ⟨S.dm (hubE2 a b), S.dm (hubF2 a b q), by
      rw [Q_dm S h2]
      simp [hubE2, Fin.sum_univ_six, eps]
      linear_combination hab, by
      rw [Q_dm S h2]
      simp [hubF2, Fin.sum_univ_six, eps]
      linear_combination (q * q) * hab, by
      rw [polar_dm_dm]
      simp [hubE2, hubF2, Fin.sum_univ_six, eps]
      linear_combination (-2 * q) * hab + hq⟩
  orth :=
    ⟨by
      rw [polar_dm_dm]
      simp [hubE1, hubE2, Fin.sum_univ_six, eps]
      ring, by
      rw [polar_dm_dm]
      simp [hubE1, hubF2, Fin.sum_univ_six, eps]
      ring, by
      rw [polar_dm_dm]
      simp [hubF1, hubE2, Fin.sum_univ_six, eps]
      ring, by
      rw [polar_dm_dm]
      simp [hubF1, hubF2, Fin.sum_univ_six, eps]
      ring⟩

theorem hub_La_neg_one (h2 : (2 : K) ≠ 0) {a b q : K} (hab : a * a + b * b = -1)
    (hq : 4 * q = 1) (x : V) :
    (S.hubFrame h2 hab hq).La (-1) x = S.D ![1, 1, 1, 1, 0, 0] x := by
  rw [Frame.La_neg_one_apply, incl_coords_eq]
  unfold D
  congr 1
  have key : (2 : K) • (polar Q x (S.dm (hubF1 a b q)) • S.dm (hubE1 a b) +
      polar Q x (S.dm (hubE1 a b)) • S.dm (hubF1 a b q) +
      polar Q x (S.dm (hubF2 a b q)) • S.dm (hubE2 a b) +
      polar Q x (S.dm (hubE2 a b)) • S.dm (hubF2 a b q)) =
      S.dm (fun i => ![1, 1, 1, 1, 0, 0] i * eps K i * polar Q x (S.o i)) := by
    rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, ← map_add,
      ← map_smul]
    congr 1
    funext k
    fin_cases k
    all_goals simp [polar_right_dm, hubE1, hubE2, hubF1, hubF2, Fin.sum_univ_six, eps]
    · linear_combination (polar Q x (S.o 0)) * hq
    · linear_combination (polar Q x (S.o 1)) * hq
    · linear_combination (-4 * q * polar Q x (S.o 2)) * hab + (polar Q x (S.o 2)) * hq
    · linear_combination (-4 * q * polar Q x (S.o 3)) * hab + (polar Q x (S.o 3)) * hq
  exact key

@[expose] def stdE1 (h : K) : Fin 6 → K := ![h, 0, 0, 0, h, 0]

@[expose] def stdF1 (h : K) : Fin 6 → K := ![h, 0, 0, 0, -h, 0]

@[expose] def stdE2 (h : K) : Fin 6 → K := ![0, h, 0, 0, 0, h]

@[expose] def stdF2 (h : K) : Fin 6 → K := ![0, h, 0, 0, 0, -h]

@[expose] def stdFrame (h2 : (2 : K) ≠ 0) {h : K} (hh : 2 * h = 1) : Frame Q where
  P := ⟨S.dm (stdE1 h), S.dm (stdF1 h), by
      rw [Q_dm S h2]
      simp [stdE1, Fin.sum_univ_six, eps], by
      rw [Q_dm S h2]
      simp [stdF1, Fin.sum_univ_six, eps], by
      rw [polar_dm_dm]
      simp [stdE1, stdF1, Fin.sum_univ_six, eps]
      linear_combination (2 * h + 1) * hh⟩
  P' := ⟨S.dm (stdE2 h), S.dm (stdF2 h), by
      rw [Q_dm S h2]
      simp [stdE2, Fin.sum_univ_six, eps], by
      rw [Q_dm S h2]
      simp [stdF2, Fin.sum_univ_six, eps], by
      rw [polar_dm_dm]
      simp [stdE2, stdF2, Fin.sum_univ_six, eps]
      linear_combination (2 * h + 1) * hh⟩
  orth :=
    ⟨by
      rw [polar_dm_dm]
      simp [stdE1, stdE2, Fin.sum_univ_six, eps], by
      rw [polar_dm_dm]
      simp [stdE1, stdF2, Fin.sum_univ_six, eps], by
      rw [polar_dm_dm]
      simp [stdF1, stdE2, Fin.sum_univ_six, eps], by
      rw [polar_dm_dm]
      simp [stdF1, stdF2, Fin.sum_univ_six, eps]⟩

theorem std_La_neg_one (h2 : (2 : K) ≠ 0) {h : K} (hh : 2 * h = 1) (x : V) :
    (S.stdFrame h2 hh).La (-1) x = S.D ![1, 1, 0, 0, 1, 1] x := by
  rw [Frame.La_neg_one_apply, incl_coords_eq]
  unfold D
  congr 1
  have key : (2 : K) • (polar Q x (S.dm (stdF1 h)) • S.dm (stdE1 h) +
      polar Q x (S.dm (stdE1 h)) • S.dm (stdF1 h) +
      polar Q x (S.dm (stdF2 h)) • S.dm (stdE2 h) +
      polar Q x (S.dm (stdE2 h)) • S.dm (stdF2 h)) =
      S.dm (fun i => ![1, 1, 0, 0, 1, 1] i * eps K i * polar Q x (S.o i)) := by
    rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, ← map_add, ← map_add, ← map_add,
      ← map_smul]
    congr 1
    funext k
    fin_cases k
    all_goals simp [polar_right_dm, stdE1, stdE2, stdF1, stdF2, Fin.sum_univ_six, eps]
    · linear_combination (2 * h + 1) * polar Q x (S.o 0) * hh
    · linear_combination (2 * h + 1) * polar Q x (S.o 1) * hh
    · linear_combination (-(2 * h + 1)) * polar Q x (S.o 4) * hh
    · linear_combination (-(2 * h + 1)) * polar Q x (S.o 5) * hh
  exact key

theorem polar_D (m : Fin 6 → K) (x : V) (k : Fin 6) :
    polar Q (S.D m x) (S.o k) = (1 - 2 * m k) * polar Q x (S.o k) := by
  unfold D
  rw [polar_sub_left, polar_dm_o]
  have := eps_mul_self (K := K) k
  linear_combination (-2 * m k * polar Q x (S.o k)) * this

theorem D_D (m m' : Fin 6 → K) (x : V) :
    S.D m (S.D m' x) =
      x - S.dm (fun i => (m i + m' i - 2 * m i * m' i) * eps K i * polar Q x (S.o i)) := by
  have e : (fun i => (m i + m' i - 2 * m i * m' i) * eps K i * polar Q x (S.o i)) =
      (fun i => m' i * eps K i * polar Q x (S.o i)) +
        (fun i => m i * eps K i * ((1 - 2 * m' i) * polar Q x (S.o i))) := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [e, map_add]
  show S.D m' x - S.dm (fun i => m i * eps K i * polar Q (S.D m' x) (S.o i)) = _
  simp only [polar_D]
  unfold D
  abel

theorem D_comm (m m' : Fin 6 → K) (x : V) : S.D m (S.D m' x) = S.D m' (S.D m x) := by
  rw [D_D, D_D]
  congr 2
  funext i
  ring

@[expose] def pad : (Fin 2 → K) →ₗ[K] (Fin 6 → K) where
  toFun c := ![c 0, c 1, 0, 0, 0, 0]
  map_add' c d := by
    funext i
    fin_cases i <;> simp
  map_smul' r c := by
    funext i
    fin_cases i <;> simp

theorem pad_injective : Function.Injective (pad (K := K)) := by
  intro c d h
  funext i
  fin_cases i
  · simpa [pad] using congrFun h 0
  · simpa [pad] using congrFun h 1

@[expose] def ovm : (Fin 2 → K) →ₗ[K] V := S.dm ∘ₗ pad

theorem ovm_apply (c : Fin 2 → K) : S.ovm c = S.dm (pad c) := rfl

theorem ovm_injective (h2 : (2 : K) ≠ 0) : Function.Injective S.ovm :=
  (S.dm_injective h2).comp pad_injective

theorem Q_ovm (h2 : (2 : K) ≠ 0) (c : Fin 2 → K) : Q (S.ovm c) = c 0 * c 0 + c 1 * c 1 := by
  rw [ovm_apply, Q_dm S h2]
  simp [pad, Fin.sum_univ_six, eps]

theorem D_dm (m u : Fin 6 → K) : S.D m (S.dm u) = S.dm (fun i => (1 - 2 * m i) * u i) := by
  unfold D
  simp only [polar_dm_o]
  rw [← map_sub]
  congr 1
  funext i
  have := eps_mul_self (K := K) i
  simp only [Pi.sub_apply]
  linear_combination (-2 * m i * u i) * this

theorem eq_add_of_D_eq_neg {m : Fin 6 → K} {x : V} (h : S.D m x = -x) :
    S.dm (fun i => m i * eps K i * polar Q x (S.o i)) = x + x := by
  unfold D at h
  calc S.dm (fun i => m i * eps K i * polar Q x (S.o i))
      = x - (x - S.dm (fun i => m i * eps K i * polar Q x (S.o i))) := by abel
    _ = x - -x := by rw [h]
    _ = x + x := by abel

theorem both_neg_iff (h2 : (2 : K) ≠ 0) (x : V) :
    (S.D ![1, 1, 1, 1, 0, 0] x = -x ∧ S.D ![1, 1, 0, 0, 1, 1] x = -x) ↔
      x ∈ LinearMap.range S.ovm := by
  constructor
  · rintro ⟨h1, h1'⟩
    have e1 := S.eq_add_of_D_eq_neg h1
    have e2 := S.eq_add_of_D_eq_neg h1'
    have hd := S.dm_injective h2 (e1.trans e2.symm)
    have h2' := congrFun hd 2
    have h3' := congrFun hd 3
    have h4' := congrFun hd 4
    have h5' := congrFun hd 5
    simp [eps] at h2' h3' h4' h5'
    refine ⟨fun j => (2 : K)⁻¹ * polar Q x (S.o (Fin.castLE (by omega) j)), ?_⟩
    have hx : (2 : K) • x = (2 : K) • S.ovm
        (fun j => (2 : K)⁻¹ * polar Q x (S.o (Fin.castLE (by omega) j))) := by
      rw [two_smul, ← e1, ovm_apply, ← map_smul]
      congr 1
      funext i
      fin_cases i
      all_goals simp [pad, eps, h2', h3', h4', h5']
      all_goals rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
    exact (smul_right_injective V h2 hx).symm
  · rintro ⟨c, rfl⟩
    constructor
    all_goals
      rw [ovm_apply, D_dm, ← map_neg]
      congr 1
      funext i
      fin_cases i
      all_goals simp [pad]
      all_goals ring

theorem mem_negSpace_iff_apply (i : V ≃ₗ[K] V) (x : V) : x ∈ negSpace i ↔ i x = -x := by
  simp [negSpace]

theorem inf_negSpace_eq (h2 : (2 : K) ≠ 0) {a b q h : K} (hab : a * a + b * b = -1)
    (hq : 4 * q = 1) (hh : 2 * h = 1) :
    negSpace ((S.hubFrame h2 hab hq).La (-1)) ⊓ negSpace ((S.stdFrame h2 hh).La (-1)) =
      LinearMap.range S.ovm := by
  ext x
  rw [Submodule.mem_inf, mem_negSpace_iff_apply, mem_negSpace_iff_apply, hub_La_neg_one,
    std_La_neg_one]
  exact both_neg_iff S h2 x

theorem La_neg_one_comm (h2 : (2 : K) ≠ 0) {a b q h : K} (hab : a * a + b * b = -1)
    (hq : 4 * q = 1) (hh : 2 * h = 1) :
    (S.hubFrame h2 hab hq).La (-1) * (S.stdFrame h2 hh).La (-1) =
      (S.stdFrame h2 hh).La (-1) * (S.hubFrame h2 hab hq).La (-1) := by
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, hub_La_neg_one, std_La_neg_one, D_comm]

end Sys

section FramePair

open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

variable {K' : Type} [Finite K] [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime]
  [CharP K' p] [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem unitaryPair_of_frames (hK : Nat.card K = p ^ f) (hK' : Nat.card K' = (p ^ f) ^ 2)
    (hodd : Odd (Nat.card K)) (fr₁ fr₂ : Frame Q)
    (hc : fr₁.La (-1) * fr₂.La (-1) = fr₂.La (-1) * fr₁.La (-1))
    (hdim : Module.finrank K ↥(negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1))) = 2)
    (hs : ¬ HasSingularVector Q (negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1)))) :
    UnitaryBlockStandardPair K' p f (fr₁.La.range ⊔ fr₂.La.range) fr₁.La.range fr₂.La.range := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have h₁ : IsFundamental Q fr₁.La.range (fr₁.La (-1)) := ⟨fr₁, rfl, rfl⟩
  have h₂ : IsFundamental Q fr₂.La.range (fr₂.La (-1)) := ⟨fr₂, rfl, rfl⟩
  have hN : fr₂.La (-1) ∈ Subgroup.normalizer (fr₁.La.range : Set (V ≃ₗ[K] V)) :=
    (mem_normalizer_iff_even hodd h₁ h₂ hc).mpr (by rw [hdim]; exact even_two)
  have hC : fr₂.La (-1) ∉ Subgroup.centralizer (fr₁.La.range : Set (V ≃ₗ[K] V)) := by
    intro hcent
    have hcent' : ∀ A : SL(2, K), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := fun A =>
      ((Subgroup.mem_centralizer_iff.mp hcent) _ ⟨A, rfl⟩).symm
    rcases Frame.orth_or_eq h2 hc.symm hcent' with horth | heq
    · obtain ⟨v, hv, hv0⟩ : ∃ v ∈ negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1)), v ≠ 0 := by
        have : (negSpace (fr₁.La (-1)) ⊓ negSpace (fr₂.La (-1))) ≠ ⊥ := by
          rw [← Submodule.one_le_finrank_iff, hdim]
          norm_num
        exact Submodule.exists_mem_ne_zero_of_ne_bot this
      refine hs ⟨v, hv, hv0, ?_⟩
      rw [Submodule.mem_inf, negSpace_La_neg_one h2, negSpace_La_neg_one h2] at hv
      obtain ⟨⟨X, hX⟩, ⟨Y, hY⟩⟩ := hv
      have hp : polar Q v v = 0 := by
        have := horth X Y
        rw [hX, hY] at this
        exact this
      have h' : (2 : K) * Q v = 0 := by
        rw [QuadraticMap.polar_self, nsmul_eq_mul] at hp
        simpa using hp
      exact (mul_eq_zero.mp h').resolve_left h2
    · rw [heq, inf_idem, negSpace_La_neg_one h2, Frame.finrank_span] at hdim
      omega
  exact lemma_6_10_unitary hK hK' hodd h₁ h₂ hc hN hC hs

theorem exists_unitaryPair [CharP K p] (S : Sys Q) (hK : Nat.card K = p ^ f)
    (hK' : Nat.card K' = (p ^ f) ^ 2) (hodd : Odd (Nat.card K)) (hneg : ¬ IsSquare (-1 : K)) :
    ∃ fr₁ fr₂ : Frame Q, UnitaryBlockStandardPair K' p f (fr₁.La.range ⊔ fr₂.La.range)
      fr₁.La.range fr₂.La.range := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have h4 : (4 : K) ≠ 0 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  obtain ⟨a₀, b₀, hab₀⟩ := CharP.sq_add_sq K p (-1)
  have hab : (a₀ : K) * a₀ + (b₀ : K) * b₀ = -1 := by
    have := hab₀
    push_cast at this
    linear_combination this
  have hq : 4 * (4 : K)⁻¹ = 1 := mul_inv_cancel₀ h4
  have hh : 2 * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
  refine ⟨S.hubFrame h2 hab hq, S.stdFrame h2 hh, unitaryPair_of_frames hK hK' hodd _ _
    (S.La_neg_one_comm h2 hab hq hh) ?_ ?_⟩
  · rw [S.inf_negSpace_eq h2 hab hq hh, LinearMap.finrank_range_of_inj (S.ovm_injective h2)]
    simp
  · rintro ⟨v, hv, hv0, hQ⟩
    rw [S.inf_negSpace_eq h2 hab hq hh] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [S.Q_ovm h2] at hQ
    apply hv0
    have h1 : c 1 = 0 := by
      by_contra h1
      exact hneg ⟨c 0 / c 1, by field_simp; linear_combination (-1 : K) * hQ⟩
    have h0 : c 0 = 0 := by
      rw [h1] at hQ
      simpa using hQ
    have : c = 0 := funext fun k => by fin_cases k <;> simp [h0, h1]
    rw [this, map_zero]

end FramePair

end CFSG.ClassicalInvolution.Asc77.MuTab.OrthHub

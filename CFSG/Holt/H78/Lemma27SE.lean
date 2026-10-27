module

public import CFSG.Holt.H78.Lemma27Fibre
import CFSG.Holt.H78.DataSocle
import CFSG.Holt.H78.DataSylow
import CFSG.Holt.H78.SEModelFive

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise commutatorElement

section Group

variable {X : Type*} [Group X]

theorem eq_one_of_mul_self_eq_one_of_odd_card [Finite X] (hX : Odd (Nat.card X)) {g : X}
    (hg : g * g = 1) : g = 1 := by
  have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hg)
  have h2 : orderOf g ∣ Nat.card X := orderOf_dvd_natCard g
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd (Nat.odd_iff.mp hX) (by omega)

theorem mul_mul_self_eq_one_of_odd_of_commute {t a b : X} (ht : t * t = 1) (ha : a * a = 1)
    (hb : b * b = 1) (hta : Odd (orderOf (t * a))) (h : Commute t (a * b)) :
    a * b * (a * b) = 1 := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hinv : (t * a) * (a * b) * (t * a)⁻¹ = (a * b)⁻¹ := by
    calc (t * a) * (a * b) * (t * a)⁻¹ = t * (b * a) * t⁻¹ := by
          rw [mul_inv_rev, ha', ← mul_assoc, ← mul_assoc, mul_assoc t a a, ha, mul_one]
          group
      _ = (a * b)⁻¹ := by
          have hc : t * (a * b)⁻¹ = (a * b)⁻¹ * t := h.inv_right.eq
          rw [mul_inv_rev, ha', hb'] at hc
          rw [hc, mul_inv_cancel_right, mul_inv_rev, ha', hb']
  have e1 : SemiconjBy (t * a) (a * b) (a * b)⁻¹ := by
    show (t * a) * (a * b) = (a * b)⁻¹ * (t * a)
    rw [← hinv, inv_mul_cancel_right]
  have e2 : SemiconjBy (t * a) (a * b)⁻¹ (a * b) := by simpa using e1.inv_right
  have hsq : Commute ((t * a) ^ 2) (a * b) := by
    rw [sq]
    exact e2.mul_left e1
  obtain ⟨m, hm⟩ := hta
  have e : ((t * a) ^ 2) ^ (m + 1) = t * a := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf (t * a) + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hc : Commute (t * a) (a * b) := e ▸ hsq.pow_left (m + 1)
  have hx : (a * b)⁻¹ = a * b := mul_right_cancel (e1.eq.symm.trans hc.eq)
  calc a * b * (a * b) = a * b * (a * b)⁻¹ := by rw [hx]
    _ = 1 := mul_inv_cancel _

end Group

section Products

variable {G : Type} [Group G] [Finite G] {Ω : Type}
  [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

namespace HoltData

theorem mul_mem_socPre_of_mem_longInv (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (D : HoltData G Ω) {u v : G}
    (hu : u ∈ longInv G Ω) (hv : v ∈ longInv G Ω) : u * v ∈ D.socPre := by
  obtain ⟨h, hh, rfl⟩ := exists_mem_jHull_conj_eq hG hB hu hv
  have e : u * (h * u * h⁻¹) = ⁅u, h⁆ := by
    rw [commutatorElement_def, inv_eq_self_of_mem_longInv hu, ← mul_assoc, ← mul_assoc]
  rw [e]
  exact D.commutator_jHull_le_socPre
    (Subgroup.commutator_mem_commutator (mem_jHull_of_mem_longInv hu) hh)

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem eq_one_of_mem_socPre_of_isNaturalSE (D : HoltData G Ω)
    (hSE : ∀ i, IsNaturalSE (D.M i)) {x : G} (hx : x ∈ D.socPre) (hx2 : x * x = 1) {α β : Ω}
    (hαβ : ∀ i, D.coord α i ≠ D.coord β i) (hxα : x • α = α) (hxβ : x • β = β) : x = 1 := by
  have hxH := D.socPre_le_jHull hx
  have hρ : ∀ i, D.ρ i ⟨x, hxH⟩ = 1 := by
    intro i
    obtain ⟨n, i', e, hA⟩ := (hSE i).exists_isBenderAction
    have hM := D.rho_mem_M_of_mem_socPre (h := ⟨x, hxH⟩) hx i
    have hfix : ∀ ω : Ω, x • ω = ω →
        (⟨_, hM⟩ : D.M i) ∈ stabilizer (D.M i) (D.coord ω i) := fun ω hω => by
      rw [mem_stabilizer_iff]
      show D.ρ i ⟨x, hxH⟩ (D.coord ω i) = D.coord ω i
      rw [← D.coord_smul]
      exact congrArg (D.coord · i) hω
    have h1 := eq_one_of_mul_self_eq_one_of_odd_card (hA.odd_card_stabilizer_inf (hαβ i))
      (g := ⟨⟨_, hM⟩, hfix α hxα, hfix β hxβ⟩) (by
        refine Subtype.ext (Subtype.ext ?_)
        show D.ρ i ⟨x, hxH⟩ * D.ρ i ⟨x, hxH⟩ = 1
        rw [← map_mul, ← map_one (D.ρ i)]
        exact congrArg (D.ρ i) (Subtype.ext hx2))
    exact congrArg (fun y : D.M i => (y : Equiv.Perm (D.Ψc i))) (congrArg Subtype.val h1)
  have hK : x ∈ jOrbitKernel G Ω := (D.mem_jOrbitKernel_iff_rho (h := ⟨x, hxH⟩)).mpr hρ
  have hO : x ∈ jOddCore G Ω := D.socPre_inf_jOrbitKernel ▸ Subgroup.mem_inf.mpr ⟨hx, hK⟩
  exact congrArg Subtype.val (eq_one_of_mul_self_eq_one_of_odd_card odd_card_jOddCore
    (g := ⟨x, hO⟩) (Subtype.ext hx2))

theorem odd_orderOf_mul_of_isNaturalSE (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (D : HoltData G Ω)
    (hSE : ∀ i, IsNaturalSE (D.M i)) {u w : G} {β γ : Ω} (hu : u ∈ longInvAt G Ω β)
    (hw : w ∈ longInvAt G Ω γ) (hβγ : ∀ i, D.coord β i ≠ D.coord γ i) :
    Odd (orderOf (u * w)) := by
  classical
  have hxS := D.mul_mem_socPre_of_mem_longInv hG hB hu.1 hw.1
  have hxH := D.socPre_le_jHull hxS
  have huH := mem_jHull_of_mem_longInv hu.1
  have hwH := mem_jHull_of_mem_longInv hw.1
  have hodd : ∀ i, Odd (orderOf (D.ρ i ⟨u * w, hxH⟩)) := by
    intro i
    obtain ⟨n, i', e, hA⟩ := (hSE i).exists_isBenderAction
    have huM := (D.rho_mem_M_iff hu.1 i).mpr (hSE i).not_isOuterFactor
    have hwM := (D.rho_mem_M_iff hw.1 i).mpr (hSE i).not_isOuterFactor
    have huJ := D.rho_mem_longInvAt hu i
    have hwJ := D.rho_mem_longInvAt hw i
    have h := hA.odd_orderOf_mul (a := ⟨_, huM⟩) (b := ⟨_, hwM⟩)
      (by rw [Subgroup.orderOf_mk]; exact huJ.1.1) (by rw [Subgroup.orderOf_mk]; exact hwJ.1.1)
      (α := D.coord β i) (β := D.coord γ i) huJ.2 hwJ.2 (hβγ i)
    rw [← Subgroup.orderOf_coe] at h
    have e : (⟨u * w, hxH⟩ : jHull G Ω) = ⟨u, huH⟩ * ⟨w, hwH⟩ := rfl
    rw [e, map_mul]
    exact h
  set k := ∏ i, orderOf (D.ρ i ⟨u * w, hxH⟩)
  have hk : Odd k := Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one
    fun i _ => hodd i
  have hK : (u * w) ^ k ∈ jOrbitKernel G Ω := by
    have h := (D.mem_jOrbitKernel_iff_rho (h := ⟨u * w, hxH⟩ ^ k)).mpr fun i => by
      rw [map_pow, ← orderOf_dvd_iff_pow_eq_one]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    simpa using h
  have hO : (u * w) ^ k ∈ jOddCore G Ω :=
    D.socPre_inf_jOrbitKernel ▸ Subgroup.mem_inf.mpr ⟨pow_mem hxS k, hK⟩
  have hoddO : Odd (orderOf ((u * w) ^ k)) := by
    rw [← Subgroup.orderOf_mk _ hO]
    exact odd_card_jOddCore.of_dvd_nat (orderOf_dvd_natCard _)
  refine (hk.mul hoddO).of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
  rw [pow_mul, pow_orderOf_eq_one]

end HoltData

end Products

section Case2b

variable {G : Type} [Group G] [Finite G] {Ω : Type}
  [MulAction G Ω] [Finite Ω] [FaithfulSMul G Ω]

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem HoltData.coord_ne_of_mem_longInvSwap (D : HoltData G Ω) {α β γ : Ω} {s : G}
    (hs : s ∈ longInvSwap G Ω α β) (hsγ : s ∈ longInvAt G Ω γ) {i : D.ι}
    (hαβ : D.coord α i ≠ D.coord β i) : D.coord β i ≠ D.coord γ i := by
  intro h
  have hJ := D.rho_mem_longInvAt hsγ i
  have h1 : D.ρ i ⟨s, mem_jHull_of_mem_longInv hs.1⟩ (D.coord α i) = D.coord β i := by
    rw [← D.coord_smul]
    exact congrArg (D.coord · i) hs.2
  have h2 : D.ρ i ⟨s, mem_jHull_of_mem_longInv hs.1⟩ (D.coord β i) = D.coord β i := by
    rw [h]
    exact hJ.2
  exact hαβ ((D.ρ i _).injective (h1.trans h2.symm))

theorem eq_of_conj_mul_eq_of_isNaturalSE (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (D : HoltData G Ω)
    (hSE : ∀ i, IsNaturalSE (D.M i)) {α β : Ω} (hαβ : ∀ i, D.coord α i ≠ D.coord β i)
    {t u s s' : G} (ht : t ∈ longInvAt G Ω α) (hu : u ∈ longInvSwap G Ω α β)
    (hs : s ∈ longInvSwap G Ω α β) (hs' : s' ∈ longInvSwap G Ω α β)
    (h : (s * u) * t * (s * u)⁻¹ = (s' * u) * t * (s' * u)⁻¹) : s = s' := by
  have hc : Commute (u * t * u⁻¹) (s' * s) := by
    show u * t * u⁻¹ * (s' * s) = s' * s * (u * t * u⁻¹)
    have e1 : s' * s * (u * t * u⁻¹) = s' * ((s * u) * t * (s * u)⁻¹) * s := by group
    have e2 : s' * ((s' * u) * t * (s' * u)⁻¹) * s =
        (s' * s') * (u * t * u⁻¹) * (s'⁻¹ * s) := by group
    rw [e1, h, e2, mul_self_eq_one_of_mem_longInv hs'.1, one_mul,
      inv_eq_self_of_mem_longInv hs'.1]
  have hw : u * t * u⁻¹ ∈ longInvAt G Ω β := hu.2 ▸ conj_mem_longInvAt ht u
  obtain ⟨γ, hγ⟩ := exists_mem_longInvAt hs'.1
  have hodd := D.odd_orderOf_mul_of_isNaturalSE hG hB hSE hw hγ
    fun i => D.coord_ne_of_mem_longInvSwap hs' hγ (hαβ i)
  have hsq := mul_mul_self_eq_one_of_odd_of_commute (mul_self_eq_one_of_mem_longInv hw.1)
    (mul_self_eq_one_of_mem_longInv hs'.1) (mul_self_eq_one_of_mem_longInv hs.1) hodd hc
  have hst := mul_mem_stabilizer_inf_of_mem_longInvSwap hs' hs
  have h1 := D.eq_one_of_mem_socPre_of_isNaturalSE hSE
    (D.mul_mem_socPre_of_mem_longInv hG hB hs'.1 hs.1) hsq hαβ hst.1 hst.2
  rw [← inv_eq_self_of_mem_longInv hs'.1]
  exact eq_inv_of_mul_eq_one_right h1

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
private theorem conj_mul_mem_longInvAt {α β : Ω} {t u s : G} (ht : t ∈ longInvAt G Ω α)
    (hu : u ∈ longInvSwap G Ω α β) (hs : s ∈ longInvSwap G Ω α β) :
    (s * u) * t * (s * u)⁻¹ ∈ longInvAt G Ω α := by
  have h := conj_mem_longInvAt ht (s * u)
  rwa [mem_stabilizer_iff.mp (mul_mem_stabilizer_inf_of_mem_longInvSwap hs hu).1] at h

private def conjSwapMap {α β : Ω} {t u : G} (ht : t ∈ longInvAt G Ω α)
    (hu : u ∈ longInvSwap G Ω α β) (s : longInvSwap G Ω α β) : longInvAt G Ω α :=
  ⟨((s : G) * u) * t * ((s : G) * u)⁻¹, conj_mul_mem_longInvAt ht hu s.2⟩

theorem card_longInvSwap_le_of_isNaturalSE (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (D : HoltData G Ω)
    (hSE : ∀ i, IsNaturalSE (D.M i)) {α β : Ω} (hαβ : ∀ i, D.coord α i ≠ D.coord β i) :
    Nat.card (longInvSwap G Ω α β) ≤ Nat.card (longInvAt G Ω α) := by
  rcases (longInvSwap G Ω α β).eq_empty_or_nonempty with h | ⟨u, hu⟩
  · simp [h]
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  exact Nat.card_le_card_of_injective (conjSwapMap ht hu) fun s s' h =>
    Subtype.ext (eq_of_conj_mul_eq_of_isNaturalSE hG hB D hSE hαβ ht hu s.2 s'.2
      (congrArg Subtype.val h))

theorem lemma27iAt_of_isNaturalSE (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (D : HoltData G Ω)
    (hSE : ∀ i, IsNaturalSE (D.M i)) {α β : Ω} (hαβ : ∀ i, D.coord α i ≠ D.coord β i)
    (hcard : Nat.card (longInvSwap G Ω α β) = Nat.card (longInvAt G Ω α)) :
    Lemma27iAt G Ω α β := by
  refine ⟨hcard, fun γ hγ => holtDelta'_eq_orbit_of_subset hγ ?_⟩
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  have : Nonempty (longInvAt G Ω α) := ⟨⟨t, ht⟩⟩
  have hpos : 0 < Nat.card (longInvSwap G Ω α β) := hcard ▸ Nat.card_pos
  obtain ⟨⟨u, hu⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  have hinj : Function.Injective (conjSwapMap ht hu) := fun s s' h =>
    Subtype.ext (eq_of_conj_mul_eq_of_isNaturalSE hG hB D hSE hαβ ht hu s.2 s'.2
      (congrArg Subtype.val h))
  have hsurj := (hinj.bijective_of_nat_card_le hcard.ge).2
  have hmem : ∀ δ ∈ holtDelta' G Ω α β,
      δ ∈ orbit ↥(stabilizer G α ⊓ stabilizer G β) (t • β) := by
    rintro _ ⟨s'', hs'', rfl⟩
    obtain ⟨⟨s, hs⟩, hfs⟩ := hsurj ⟨s'', hs''⟩
    have hsu := mul_mem_stabilizer_inf_of_mem_longInvSwap hs hu
    refine ⟨⟨s * u, hsu⟩, ?_⟩
    have e : s'' = (s * u) * t * (s * u)⁻¹ := (congrArg Subtype.val hfs).symm
    have hβ : (s * u)⁻¹ • β = β := by
      rw [inv_smul_eq_iff, mem_stabilizer_iff.mp hsu.2]
    show (s * u) • t • β = s'' • β
    rw [e]
    calc (s * u) • t • β = (s * u) • t • (s * u)⁻¹ • β := by rw [hβ]
      _ = ((s * u) * t * (s * u)⁻¹) • β := by simp only [mul_smul]
  rw [orbit_eq_iff.mpr (hmem γ hγ)]
  exact hmem

end Case2b

end CFSG.Holt.H78

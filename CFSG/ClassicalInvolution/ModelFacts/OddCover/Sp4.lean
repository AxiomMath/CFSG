module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sp4Basic
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Central
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SymInv
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.Sieg
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPart
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open Matrix CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Pairing

variable {E : Type*} [Group E]

@[expose, instance_reducible] def centerCommGroup (E : Type*) [Group E] :
    CommGroup (Subgroup.center E) :=
  { (inferInstance : Group (Subgroup.center E)) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a) }

theorem comm_mul_left_of_central {a b c : E} (h : ⁅b, c⁆ ∈ Subgroup.center E) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  have e : ⁅a * b, c⁆ = (a * ⁅b, c⁆ * a⁻¹) * ⁅a, c⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, conj_of_mem_center h a]

theorem comm_mul_right_of_central {a b c : E} (h : ⁅a, c⁆ ∈ Subgroup.center E) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [comm_mul_right_eq, conj_of_mem_center h b]

variable {X : Type*} [Group X] {π : E →* X}

theorem comm_eq_of_conj (hcen : π.ker ≤ Subgroup.center E) {a b a' b' : E} (g : E)
    (hab : Commute (π a) (π b)) (ha : π g * π a * (π g)⁻¹ = π a')
    (hb : π g * π b * (π g)⁻¹ = π b') : ⁅a', b'⁆ = ⁅a, b⁆ := by
  have hc := comm_mem_center_of_commute_map hcen hab
  calc ⁅a', b'⁆ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ :=
        (comm_eq_of_map_eq hcen (by rw [map_mul, map_mul, map_inv]; exact ha)
          (by rw [map_mul, map_mul, map_inv]; exact hb)).symm
    _ = g * ⁅a, b⁆ * g⁻¹ := (conj_comm g a b).symm
    _ = ⁅a, b⁆ := conj_of_mem_center hc g

end Pairing

section Fields

variable {K : Type} [Field K] [Finite K]

theorem exists_unit_sq_ne_one (h5 : 5 ≤ Nat.card K) : ∃ t : Kˣ, t ^ 2 ≠ 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨g, fun h2 => ?_⟩
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card Kˣ = Nat.card K - 1 := CFSG.SectionRank.OddCover.card_units_eq
  have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
  omega

end Fields

section Extension

variable {K : Type} [Field K] {E : Type*} [Group E] {π : E →* StatedSp 2 K}

@[expose] def Qhat (π : E →* StatedSp 2 K) : Subgroup E := (Qsp K).comap π

@[expose] noncomputable def Ahat (π : E →* StatedSp 2 K) : Subgroup E := (Nsp K).comap π

@[expose] noncomputable def Uhat4 (π : E →* StatedSp 2 K) : Subgroup E := (Usp K).comap π

theorem mem_Qhat {g : E} : g ∈ Qhat π ↔ ∃ x y z : K, π g = qSp x y z := Iff.rfl

theorem mem_Ahat {g : E} : g ∈ Ahat π ↔ ∃ r : K, π g = nSp r := Iff.rfl

theorem mem_Uhat4 {g : E} : g ∈ Uhat4 π ↔ ∃ x y z r : K, π g = qSp x y z * nSp r := Iff.rfl

theorem ker_le_Qhat : π.ker ≤ Qhat π := fun c hc =>
  ⟨0, 0, 0, by rw [MonoidHom.mem_ker.1 hc, qSp_zero]⟩

theorem Qhat_le_Uhat4 : Qhat π ≤ Uhat4 π := by
  rintro g ⟨x, y, z, h⟩
  exact ⟨x, y, z, 0, by rw [h, nSp_zero, mul_one]⟩

theorem Ahat_le_Uhat4 : Ahat π ≤ Uhat4 π := by
  rintro g ⟨r, h⟩
  exact ⟨0, 0, 0, r, by rw [h, qSp_zero, one_mul]⟩

theorem Uhat4_eq (hπ : Function.Surjective π) : Uhat4 π = Qhat π ⊔ Ahat π := by
  refine le_antisymm ?_ (sup_le Qhat_le_Uhat4 Ahat_le_Uhat4)
  rintro g ⟨x, y, z, r, h⟩
  obtain ⟨s, hs⟩ := hπ (nSp r)
  have hq : g * s⁻¹ ∈ Qhat π := ⟨x, y, z, by rw [map_mul, map_inv, h, hs, mul_inv_cancel_right]⟩
  have hsA : s ∈ Ahat π := ⟨r, hs⟩
  have : g = (g * s⁻¹) * s := by group
  rw [this]
  exact Subgroup.mul_mem_sup hq hsA

theorem Ahat_conj_Qhat {a q : E} (ha : a ∈ Ahat π) (hq : q ∈ Qhat π) : a * q * a⁻¹ ∈ Qhat π := by
  obtain ⟨r, hr⟩ := ha
  obtain ⟨x, y, z, hq⟩ := hq
  exact ⟨_, _, _, by rw [map_mul, map_mul, map_inv, hr, hq, nSp_conj_qSp]⟩

theorem torus_conj_Qhat {g q : E} {t : Kˣ × Kˣ} (hg : π g = lSp K (dGL t)) (hq : q ∈ Qhat π) :
    g * q * g⁻¹ ∈ Qhat π := by
  obtain ⟨x, y, z, hq⟩ := hq
  exact ⟨_, _, _, by rw [map_mul, map_mul, map_inv, hg, hq, lSp_dGL_conj_qSp]⟩

theorem Qhat_comm [Finite K] (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h5 : 5 ≤ Nat.card K) : ∀ a ∈ Qhat π, ∀ b ∈ Qhat π, a * b = b * a := by
  classical
  let _ := centerCommGroup E
  have hlift : ∀ u : K × K × K, ∃ g : E, π g = qSp u.1 u.2.1 u.2.2 := fun u => hπ _
  choose ℓ hℓ using hlift
  have hc : ∀ u u', ⁅ℓ u, ℓ u'⁆ ∈ Subgroup.center E := fun u u' =>
    comm_mem_center_of_commute_map hcen (by rw [hℓ, hℓ]; exact qSp_comm _ _ _ _ _ _)
  let B : K × K × K → K × K × K → Subgroup.center E := fun u u' => ⟨⁅ℓ u, ℓ u'⁆, hc u u'⟩
  have hB : ∀ u u', ((B u u' : Subgroup.center E) : E) = ⁅ℓ u, ℓ u'⁆ := fun _ _ => rfl
  have hadd : ∀ u v : K × K × K, π (ℓ (u + v)) = π (ℓ u * ℓ v) := by
    intro u v
    simp only [hℓ, map_mul, qSp_mul, Prod.fst_add, Prod.snd_add]
  have hcomm : ∀ u u', Commute (π (ℓ u)) (π (ℓ u')) := fun u u' => by
    rw [hℓ, hℓ]; exact qSp_comm _ _ _ _ _ _
  have hadd₁ : ∀ x x' y, B (x + x') y = B x y * B x' y := by
    intro x x' y
    apply Subtype.ext
    rw [Subgroup.coe_mul, hB, hB, hB, comm_eq_of_map_eq hcen (hadd x x') rfl,
      comm_mul_left_of_central (hc x' y)]
    exact Subgroup.mem_center_iff.1 (hc x y) _
  have hadd₂ : ∀ x y y', B x (y + y') = B x y * B x y' := by
    intro x y y'
    apply Subtype.ext
    rw [Subgroup.coe_mul, hB, hB, hB, comm_eq_of_map_eq hcen rfl (hadd y y'),
      comm_mul_right_of_central (hc x y')]
  have hone := eq_one_of_symInv (K := K) (W := Subgroup.center E)
    (exists_good_scalar h5)
    (by
      obtain ⟨t, ht⟩ := exists_unit_sq_ne_one h5
      refine ⟨(t : K), t.ne_zero, fun h1 => ht ?_, fun h1 => ht (Units.ext (by simpa using h1))⟩
      have : t = 1 := Units.ext h1
      rw [this, one_pow])
    B hadd₁ hadd₂ ?_ ?_ ?_
  · intro a ha b hb
    obtain ⟨x, y, z, ha⟩ := ha
    obtain ⟨x', y', z', hb⟩ := hb
    have h1 : ⁅a, b⁆ = ⁅ℓ (x, y, z), ℓ (x', y', z')⁆ :=
      comm_eq_of_map_eq hcen (by rw [ha, hℓ]) (by rw [hb, hℓ])
    have := congrArg Subtype.val (hone (x, y, z) (x', y', z'))
    exact commutatorElement_eq_one_iff_mul_comm.1 (h1.trans this)
  · intro t₁ t₂ h1 h2 u u'
    obtain ⟨g, hg⟩ := hπ (lSp K (dGL (Units.mk0 t₁ h1, Units.mk0 t₂ h2)))
    apply Subtype.ext
    rw [hB, hB]
    refine comm_eq_of_conj hcen g (hcomm u u') ?_ ?_
    · rw [hg, hℓ, hℓ]
      exact lSp_dGL_conj_qSp (Units.mk0 t₁ h1, Units.mk0 t₂ h2) u.1 u.2.1 u.2.2
    · rw [hg, hℓ, hℓ]
      exact lSp_dGL_conj_qSp (Units.mk0 t₁ h1, Units.mk0 t₂ h2) u'.1 u'.2.1 u'.2.2
  · intro u u'
    obtain ⟨g, hg⟩ := hπ (lSp K (uGL 1))
    apply Subtype.ext
    rw [hB, hB]
    refine comm_eq_of_conj hcen g (hcomm u u') ?_ ?_
    · rw [hg, hℓ, hℓ, lSp_uGL_conj_qSp]
      simp only [mul_one, one_pow, one_mul]
    · rw [hg, hℓ, hℓ, lSp_uGL_conj_qSp]
      simp only [mul_one, one_pow, one_mul]
  · intro u u'
    obtain ⟨g, hg⟩ := hπ (lSp K wGL)
    apply Subtype.ext
    rw [hB, hB]
    refine comm_eq_of_conj hcen g (hcomm u u') ?_ ?_
    · rw [hg, hℓ, hℓ, lSp_wGL_conj_qSp]
    · rw [hg, hℓ, hℓ, lSp_wGL_conj_qSp]


theorem Ahat_comm [Finite K] (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h5 : 5 ≤ Nat.card K) : ∀ a ∈ Ahat π, ∀ b ∈ Ahat π, a * b = b * a := by
  classical
  let _ := centerCommGroup E
  have hlift : ∀ r : K, ∃ g : E, π g = nSp r := fun r => hπ _
  choose ℓ hℓ using hlift
  have hcomm : ∀ r r', Commute (π (ℓ r)) (π (ℓ r')) := fun r r' => by
    rw [hℓ, hℓ]
    show nSp r * nSp r' = nSp r' * nSp r
    rw [← nSp_add, ← nSp_add, add_comm]
  have hc : ∀ r r', ⁅ℓ r, ℓ r'⁆ ∈ Subgroup.center E := fun r r' =>
    comm_mem_center_of_commute_map hcen (hcomm r r')
  let B : K → K → Subgroup.center E := fun r r' => ⟨⁅ℓ r, ℓ r'⁆, hc r r'⟩
  have hB : ∀ r r', ((B r r' : Subgroup.center E) : E) = ⁅ℓ r, ℓ r'⁆ := fun _ _ => rfl
  have hadd : ∀ r r' : K, π (ℓ (r + r')) = π (ℓ r * ℓ r') := by
    intro r r'
    rw [map_mul, hℓ, hℓ, hℓ, nSp_add]
  have hadd₁ : ∀ x x' y, B (x + x') y = B x y * B x' y := by
    intro x x' y
    apply Subtype.ext
    rw [Subgroup.coe_mul, hB, hB, hB, comm_eq_of_map_eq hcen (hadd x x') rfl,
      comm_mul_left_of_central (hc x' y)]
    exact Subgroup.mem_center_iff.1 (hc x y) _
  have hadd₂ : ∀ x y y', B x (y + y') = B x y * B x y' := by
    intro x y y'
    apply Subtype.ext
    rw [Subgroup.coe_mul, hB, hB, hB, comm_eq_of_map_eq hcen rfl (hadd y y'),
      comm_mul_right_of_central (hc x y')]
  have hone := eq_one_of_scalar_invariant (F := K) (V := K) (W := Subgroup.center E)
    (exists_good_scalar h5) B hadd₁ hadd₂ (fun a ha x y => by
      obtain ⟨g, hg⟩ := hπ (lSp K (dGL (Units.mk0 a ha, 1)))
      apply Subtype.ext
      rw [hB, hB]
      refine comm_eq_of_conj hcen g (hcomm x y) ?_ ?_
      · rw [hg, hℓ, hℓ, lSp_dGL_conj_nSp]
        simp
      · rw [hg, hℓ, hℓ, lSp_dGL_conj_nSp]
        simp)
  intro a ha b hb
  obtain ⟨r, ha⟩ := ha
  obtain ⟨r', hb⟩ := hb
  have h1 : ⁅a, b⁆ = ⁅ℓ r, ℓ r'⁆ :=
    comm_eq_of_map_eq hcen (by rw [ha, hℓ]) (by rw [hb, hℓ])
  have := congrArg Subtype.val (hone r r')
  exact commutatorElement_eq_one_iff_mul_comm.1 (h1.trans this)

theorem exists_kappa_sp [Finite K] [Finite E] {p f : ℕ} [hp : Fact p.Prime]
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hK : Nat.card K = p ^ f)
    (hf : 1 ≤ f) (h5 : 5 ≤ Nat.card K) (hker : IsPGroup p π.ker) :
    ∃ κ : E → E, (∀ y ∈ Qhat π, κ y ∈ π.ker) ∧
      (∀ y ∈ Qhat π, ∀ y' ∈ Qhat π, κ (y * y') = κ y * κ y') ∧ (∀ c ∈ π.ker, κ c = c) ∧
      ∀ g ∈ Ahat π, ∀ y ∈ Qhat π, κ (g * y * g⁻¹) = κ y := by
  classical
  have := Fintype.ofFinite K
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨s, hs⟩ := exists_unit_sq_ne_one h5
  set ν : K := (s : K) ^ 2 with hν
  have hν0 : ν ≠ 0 := pow_ne_zero 2 s.ne_zero
  have hν1 : ν ≠ 1 := fun h => hs (Units.ext (by simpa [hν] using h))
  obtain ⟨z, hz⟩ := hπ (lSp K (dGL (s, s)))
  set m := Nat.card K - 1 with hm
  have hmK : Nat.Coprime m (Nat.card π.ker) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hker
    rw [hk]
    refine Nat.Coprime.pow_right _ (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 ?_))
    intro hdvd
    have hpq : p ∣ Nat.card K := by rw [hK]; exact dvd_pow_self p (by omega)
    have := Nat.dvd_sub hpq hdvd
    rw [show Nat.card K - (Nat.card K - 1) = 1 by omega] at this
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
  have hconjpow : ∀ (i : ℕ) (y : E) (x' y' z' : K), π y = qSp x' y' z' →
      π (z ^ i * y * (z ^ i)⁻¹) = qSp (ν ^ i * x') (ν ^ i * y') (ν ^ i * z') := by
    intro i y x' y' z' hy
    rw [map_mul, map_mul, map_inv, map_pow, hz, ← map_pow, hy, ← map_pow, Prod.pow_mk,
      lSp_dGL_conj_qSp]
    simp only [Units.val_pow_eq_pow_val, hν]
    congr 1 <;> ring
  have hnorm : ∀ (n : ℕ) (y : E) (x' y' z' : K), π y = qSp x' y' z' →
      π (normSum z y n) = qSp ((∑ i ∈ Finset.range n, ν ^ i) * x')
        ((∑ i ∈ Finset.range n, ν ^ i) * y') ((∑ i ∈ Finset.range n, ν ^ i) * z') := by
    intro n y x' y' z' hy
    induction n with
    | zero => simp [qSp_zero]
    | succ n ih =>
      rw [normSum_succ, map_mul, ih, hconjpow n y x' y' z' hy, qSp_mul, Finset.sum_range_succ]
      congr 1 <;> ring
  have hgeom : ∑ i ∈ Finset.range m, ν ^ i = 0 := by
    have h1 := geom_sum_mul ν m
    have h2 : ν ^ m = 1 := by
      rw [hm, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card_sub_one_eq_one ν hν0
    rw [h2, sub_self] at h1
    exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hν1)
  have hN : ∀ y ∈ Qhat π, normSum z y m ∈ π.ker := by
    rintro y ⟨x', y', z', hy⟩
    rw [MonoidHom.mem_ker, hnorm m y x' y' z' hy, hgeom, zero_mul, zero_mul, zero_mul, qSp_zero]
  obtain ⟨κ, hκK, hκmul, hκid, hκinv⟩ := exists_retraction_fun (Y := Qhat π) (K := π.ker)
    ker_le_Qhat hcen (Qhat_comm hπ hcen h5) (z := z) (fun y hy => torus_conj_Qhat hz hy)
    (fun y hy => by
      simpa using torus_conj_Qhat (g := z⁻¹) (t := (s, s)⁻¹)
        (by rw [map_inv, hz, map_inv, map_inv]) hy)
    hmK hN
  refine ⟨κ, hκK, hκmul, hκid, fun g hg y hy => ?_⟩
  refine hκinv g (fun y hy => Ahat_conj_Qhat hg hy) (fun y _ => ?_) y hy
  refine conj_conj_comm_of_comm_mem_center (comm_mem_center_of_commute_map hcen ?_) y
  obtain ⟨r, hr⟩ := hg
  change π g * π z = π z * π g
  rw [hr, hz]
  have := lSp_dGL_conj_nSp (s, s) r
  simp only [mul_inv_cancel₀ s.ne_zero, one_mul] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem sp4_commutator_inf_ker_eq_bot [Finite K] [Finite E] {p f : ℕ} [Fact p.Prime]
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (hK : Nat.card K = p ^ f)
    (hf : 1 ≤ f) (h5 : 5 ≤ Nat.card K) (hker : IsPGroup p π.ker) :
    ⁅Uhat4 π, Uhat4 π⁆ ⊓ π.ker = ⊥ := by
  obtain ⟨κ, hκK, hκmul, hκid, hκinv⟩ := exists_kappa_sp hπ hcen hK hf h5 hker
  rw [Uhat4_eq hπ]
  exact commutator_sup_inf_eq_bot_of_sieg (C := π.ker) (Q := Qhat π) (A := Ahat π)
    (Ahat_comm hπ hcen h5) (fun a ha q hq => Ahat_conj_Qhat ha hq) hκmul hκid
    (fun y hy => hcen (hκK y hy)) hκinv

theorem sp4_ker_eq_bot_of_isPGroup [Finite K] [Finite E] [Group.IsPerfect E] {p f : ℕ}
    [Fact p.Prime] (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (h5 : 5 ≤ Nat.card K) (hker : IsPGroup p π.ker) :
    π.ker = ⊥ :=
  ker_eq_bot_of_commutator_inf_eq_bot π hπ hcen hker (isPGroup_Usp hK) (not_dvd_index_Usp hK hf)
    (sp4_commutator_inf_ker_eq_bot hπ hcen hK hf h5 hker)

end Extension

end CFSG.ClassicalInvolution.ModelFacts.OddCover

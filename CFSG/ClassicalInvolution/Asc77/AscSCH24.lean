module

public import CFSG.ClassicalInvolution.Asc77.AscSCH23
public import CFSG.ClassicalInvolution.Asc77.AscSCH22

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.CentralLift
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular mem_unitriangular
  card_unitriangular)

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def leviSUU : Multiplicative K →* gramSU h (hypGram2 2 K) :=
  (leviU h 2).comp slUhom

theorem leviUnipotentU_le_range : leviUnipotentU h 2 ≤ (leviSUU h).range := by
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨h1, h2⟩ := mem_unitriangular.1 hA
  refine ⟨Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) K) 0 1), ?_⟩
  have : slUhom (Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) K) 0 1)) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [slUhom, coe_slU, h2 0, h2 1, h1 1 0 (by decide)]
  exact congrArg (leviU h 2) this

theorem slD_conj_slU (w : Kˣ) (u : K) : slD w * slU u * (slD w)⁻¹ = slU ((w : K) ^ 2 * u) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_slD, coe_slU,
    coe_slU]
  have hw : (w : K) ≠ 0 := w.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  field_simp

theorem leviSUU_apply (u : K) : leviSUU h (Multiplicative.ofAdd u) = leviU h 2 (slU u) := by
  simp [leviSUU, slUhom]

theorem leviU_slD_leviSUU (w : Kˣ) (u : K) :
    leviU h 2 (slD w) * leviSUU h (Multiplicative.ofAdd u) * (leviU h 2 (slD w))⁻¹ =
      leviSUU h (Multiplicative.ofAdd ((w : K) ^ 2 * u)) := by
  rw [leviSUU_apply, leviSUU_apply, ← map_inv, ← map_mul, ← map_mul, slD_conj_slU]

section Main

variable {E : Type*} [Group E] {π : E →* gramSU h (hypGram2 2 K)}

theorem suTorus_conj_mem_siegelRadicalSU (a : Fin 2 → Kˣ) (ha : ∀ i, h.bar (a i) = a i)
    {x : gramSU h (hypGram2 2 K)} (hx : x ∈ siegelRadicalSU h 2) :
    suTorus h a ha * x * (suTorus h a ha)⁻¹ ∈ siegelRadicalSU h 2 := by
  obtain ⟨B, hB, hxB⟩ := (mem_siegelRadicalSU h).1 hx
  have hxs : (x : GL (Fin 2 ⊕ Fin 2) K) = siegelGL B := Units.ext hxB
  have hD : (Matrix.diagonal (fun i => (a i : K))).map h.bar =
      Matrix.diagonal (fun i => (a i : K)) := by
    rw [Matrix.diagonal_map (map_zero h.bar)]
    congr 1
    funext i
    exact ha i
  have hskew := skewHerm_conj h (Matrix.diagonal (fun i => (a i : K))) B hB
  rw [hD, Matrix.diagonal_transpose] at hskew
  refine (mem_siegelRadicalSU h).2 ⟨_, hskew, ?_⟩
  change ((torusGL a * (x : GL (Fin 2 ⊕ Fin 2) K) * (torusGL a)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = _
  rw [hxs, torusGL_conj_siegelGL]
  rfl

theorem card_radical_sup_levi (h : UnitaryFieldData ℓ f K) :
    Nat.card (siegelRadicalSU h 2 ⊔ leviUnipotentU h 2 : Subgroup (gramSU h (hypGram2 2 K))) =
      ℓ ^ (Nat.card (gramSU h (hypGram2 2 K))).factorization ℓ := by
  have := h.finite
  rw [card_sup_of_le_normalizer (leviUnipotentU_le_normalizer h)
    (siegelRadicalSU_inf_leviUnipotentU h), (siegel_radical_su h 2).2, leviUnipotentU,
    Subgroup.card_map_of_injective (leviU_injective h), card_unitriangular, h.card,
    pow_factorization_card_gramSU h (by norm_num)]
  norm_num
  ring

theorem gramSU_hyp_perfect_ker_eq_bot_defining {f : ℕ} (h : UnitaryFieldData 3 f K)
    (hq : 5 ≤ 3 ^ f) [Finite E] [Group.IsPerfect E] (π : E →* gramSU h (hypGram2 2 K))
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) (hCp : IsPGroup 3 π.ker) :
    π.ker = ⊥ := by
  have := h.finite
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hK2 : Nat.card K = (3 ^ f) ^ 2 := by rw [h.card, pow_mul']
  have hf2 : 2 ≤ f := by
    by_contra hf
    have : f ≤ 1 := by omega
    have : 3 ^ f ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h9 : 3 ^ (2 * f) ≠ 9 := by
    intro h9
    have : 3 ^ 4 ≤ 3 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := fixU K (3 ^ f))
  have hord : orderOf t = 3 ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht, card_fixU hK2]
  have htb : h.bar ((t : Kˣ) : K) = (t : Kˣ) := bar_fixU h t.2
  have ht2 : (t : Kˣ) ^ 2 ≠ 1 := by
    intro h2
    have h3 : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext h2)
    have := Nat.le_of_dvd (by norm_num) (hord ▸ h3)
    omega
  set τ : Kˣ := (t : Kˣ) with hτ
  have hτb : ∀ i : Fin 2,
      h.bar (((fun _ : Fin 2 => τ) i : Kˣ) : K) = ((fun _ : Fin 2 => τ) i : Kˣ) :=
    fun _ => htb
  set d : gramSU h (hypGram2 2 K) := suTorus h (fun _ => τ) hτb with hd
  have hdcop : Nat.Coprime (orderOf d) 3 := by
    have h1 : orderOf d ∣ orderOf τ := by
      refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change torusGL (fun _ : Fin 2 => τ) ^ orderOf τ = 1
      rw [← torusGL_const_pow, pow_orderOf_eq_one, torusGL_const_one]
    exact coprime_of_dvd_card_units hp h.card (by omega) (h1.trans (orderOf_dvd_natCard τ))
  obtain ⟨a, ha, hacop⟩ := exists_coprime_lift hp π hπ hdcop
  refine ker_eq_bot_of_unipotent π hπ hC hCp (siegelRadicalSU h 2) (leviUnipotentU h 2)
    (leviUnipotentU_le_normalizer h)
    (fun x hx y hy => mul_comm_of_liftPair_eq_one hπ (siegelSUHom h 2) hC
      (siegelSU_liftPair_eq_one h hπ hC (by norm_num) h9 ⟨τ, htb, ht2⟩) hx hy)
    (fun x hx y hy => mul_comm_of_liftPair_eq_one hπ (leviSUU h) hC
      (fun u u' => liftPair_self_eq_one_of_sq hπ (leviSUU h) hC (by norm_num) h.card h9
        (AddMonoidHom.id K) (fun c hc => ⟨leviU h 2 (slD (Units.mk0 c hc)), fun s => by
          rw [AddMonoidHom.id_apply, AddMonoidHom.id_apply, leviU_slD_leviSUU]
          simp⟩) u u')
      (leviUnipotentU_le_range h hx) (leviUnipotentU_le_range h hy))
    a hacop ?_ ?_ ?_ ?_
  · rw [ha]
    exact mem_normalizer_of_conj_mem fun x hx => suTorus_conj_mem_siegelRadicalSU h _ hτb hx
  · intro v hv
    rw [ha]
    obtain ⟨A, -, rfl⟩ := hv
    rw [mul_inv_eq_iff_eq_mul]
    exact Subtype.ext (Units.ext (torusGL_const_commute h τ A))
  · intro r hr hrfix
    rw [ha] at hrfix
    obtain ⟨v, rfl⟩ := hr
    have hτ2 : (τ : K) ^ 2 ≠ 1 := fun h1 => ht2 (Units.ext (by simpa using h1))
    have h1 : torusGL (fun _ : Fin 2 => τ) *
        siegelGL ((v.toAdd : skewHermMatrices h 2) : Matrix (Fin 2) (Fin 2) K) *
        (torusGL (fun _ : Fin 2 => τ))⁻¹ =
        siegelGL ((v.toAdd : skewHermMatrices h 2) : Matrix (Fin 2) (Fin 2) K) :=
      congrArg Subtype.val hrfix
    rw [torusGL_conj_siegelGL] at h1
    have h2 := siegelMat_injective (congrArg (fun g : GL (Fin 2 ⊕ Fin 2) K =>
      (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h1)
    have h3 : ((v.toAdd : skewHermMatrices h 2) : Matrix (Fin 2) (Fin 2) K) = 0 := by
      ext i j
      have := congrFun (congrFun h2 i) j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
      have h4 : ((τ : K) ^ 2 - 1) * ((v.toAdd : skewHermMatrices h 2) :
          Matrix (Fin 2) (Fin 2) K) i j = 0 := by linear_combination this
      rcases mul_eq_zero.1 h4 with h5 | h5
      · exact absurd (sub_eq_zero.1 h5) hτ2
      · simpa using h5
    have h6 : v = 1 := Multiplicative.toAdd.injective (Subtype.ext h3)
    rw [h6, map_one]
  · rw [card_radical_sup_levi h, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization_self hp, mul_one]

end Main

theorem defSU : DefSU := by
  intro K _ f h hq E _ _ _ π hπ hC hCp
  obtain ⟨φ⟩ := exists_statedSU_equiv_gramSU h
  have hker : (φ.toMonoidHom.comp π).ker = π.ker :=
    MonoidHom.ker_comp_of_injective _ _ φ.injective
  have := gramSU_hyp_perfect_ker_eq_bot_defining h hq (φ.toMonoidHom.comp π)
    (φ.surjective.comp hπ) (hker ▸ hC) (hker ▸ hCp)
  rwa [hker] at this

end CFSG.ClassicalInvolution.Asc77.SCH

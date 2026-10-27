module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootIrr
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootLevi
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootLeviTorus
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiAdd
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiGen
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiOps
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiWeyl
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiTorus
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootPsiFixed
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootParEq
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootField
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRootTransport

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Glue

variable
  {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem mem_Qbar_of_mem_radical {z : twistedE6RootGroup K σ}
    (hz : z ∈ twE6LongRootRadical (stdX σ)) :
    (z : ModGL TwistTag.E6.tag K) ∈ Qbar K ∧
      (z : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
  rw [radical_std_eq σ] at hz
  have h2 := Subgroup.mem_subgroupOf.1 hz
  exact ⟨(Subgroup.mem_inf.1 h2).1, (Subgroup.mem_inf.1 h2).2⟩

theorem mem_stdX_of_psi_eq_zero {z : twistedE6RootGroup K σ}
    (hz : (z : ModGL TwistTag.E6.tag K) ∈ Qbar K) (h : psi K (z : ModGL TwistTag.E6.tag K) = 0) :
    z ∈ stdX σ :=
  psi_eq_zero_imp_mem hz h

theorem irreducible_std (q : ℕ) (hr : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q)
    (hK : Nat.card K = q ^ 2) (M : Subgroup (twistedE6RootGroup K σ)) (hXM : stdX σ ≤ M)
    (hMQ : M ≤ twE6LongRootRadical (stdX σ))
    (hnorm : ∀ g ∈ twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ),
      M.map (MulAut.conj g).toMonoidHom = M) :
    M = stdX σ ∨ M = twE6LongRootRadical (stdX σ) := by
  have hσσ : ∀ c, σ (σ c) = c := fun c => by rw [hσ, hσ]; exact pow_pow_card_sq' hK c
  have hσ1 : ∃ c, σ c ≠ c := by
    obtain ⟨c, hc⟩ := exists_pow_ne (two_le_of_card_sq hK) hK
    exact ⟨c, by rw [hσ]; exact hc⟩
  have hcases3 : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → a = 0 ∨ a = 1 ∨ a = 2 := by
    decide
  have hconj : ∀ g ∈ twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ),
      ∀ m ∈ M, g * m * g⁻¹ ∈ M := by
    intro g hg m hm
    have h2 : g * m * g⁻¹ ∈ M.map (MulAut.conj g).toMonoidHom :=
      ⟨m, hm, by simp [MulAut.conj_apply]⟩
    rwa [hnorm g hg] at h2
  have hM : ∀ m ∈ M, (m : ModGL TwistTag.E6.tag K) ∈ Qbar K ∧
      (m : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    fun m hm => mem_Qbar_of_mem_radical σ (hMQ hm)
  let N : AddSubgroup (Rv K) :=
    { carrier := {v | ∃ m ∈ M, psi K (m : ModGL TwistTag.E6.tag K) = v}
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        refine ⟨m * m', M.mul_mem hm hm', ?_⟩
        rw [Subgroup.coe_mul, psi_mul (hM m hm).1 (hM m' hm').1]
      zero_mem' := ⟨1, M.one_mem, by simpa using psi_one (K := K)⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        refine ⟨m⁻¹, M.inv_mem hm, ?_⟩
        rw [Subgroup.coe_inv, psi_inv (hM m hm).1] }
  have hNmem : ∀ v, v ∈ N ↔ ∃ m ∈ M, psi K (m : ModGL TwistTag.E6.tag K) = v := fun v => Iff.rfl
  have hΦ : N ≤ RPhi K σ := by
    rintro _ ⟨m, hm, rfl⟩
    exact psi_mem_RPhi σ (hM m hm).1 (hM m hm).2
  have hk : ∀ t : K, σ t = t → ∀ v ∈ N, t • v ∈ N := by
    intro t ht v hv
    by_cases ht0 : t = 0
    · rw [ht0, zero_smul]; exact N.zero_mem
    obtain ⟨m, hm, rfl⟩ := hv
    have htmem : t ∈ orbitField TwistTag.E6 K σ.toRingHom a2 :=
      (mem_orbitField_of_card_eq_one σ.toRingHom card_orbit_a2 t).2 ht
    let u : (orbitField TwistTag.E6 K σ.toRingHom a2)ˣ :=
      Units.mk0 ⟨t, htmem⟩ (fun h => ht0 (congrArg Subtype.val h))
    have hg : n0G σ * hG σ a2 u * (n0G σ)⁻¹ ∈
        twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ) :=
      Subgroup.mem_sup_right (n0G_conj_hG_mem_twE6LongRootTorus K σ u)
    refine ⟨n0G σ * hG σ a2 u * (n0G σ)⁻¹ * m * (n0G σ * hG σ a2 u * (n0G σ)⁻¹)⁻¹,
      hconj _ hg m hm, ?_⟩
    have := psi_conj_torus σ u (m : ModGL TwistTag.E6.tag K)
    exact this.trans rfl
  have hX : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, xorb K σ a c v ∈ N := by
    intro a ha c hc v hv
    obtain ⟨m, hm, rfl⟩ := hv
    have hcases : a = 0 ∨ a = 1 ∨ a = 2 := hcases3 a ha
    have hcmem : c ∈ orbitField TwistTag.E6 K σ.toRingHom a := by
      rcases hcases with rfl | rfl | rfl
      · exact mem_orbitField_of_card_eq_two σ.toRingHom hσσ card_orbit_zero c
      · exact mem_orbitField_of_card_eq_two σ.toRingHom hσσ card_orbit_one c
      · exact (mem_orbitField_of_card_eq_one σ.toRingHom card_orbit_two c).2 (hc rfl)
    let c' : orbitField TwistTag.E6 K σ.toRingHom a := ⟨c, hcmem⟩
    have hg : xG σ a c' ∈
        twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ) :=
      Subgroup.mem_sup_left (xG_mem_twE6LongRootLevi K σ q hr hσ hK a ha c')
    refine ⟨xG σ a c' * m * (xG σ a c')⁻¹, hconj _ hg m hm, ?_⟩
    exact psi_conj_orbitX σ ha c' (m : ModGL TwistTag.E6.tag K)
  have hY : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∀ c : K, (a = 2 → σ c = c) →
      ∀ v ∈ N, yorb K σ a c v ∈ N := by
    intro a ha c hc v hv
    obtain ⟨m, hm, rfl⟩ := hv
    have hcases : a = 0 ∨ a = 1 ∨ a = 2 := hcases3 a ha
    have hcmem : c ∈ orbitField TwistTag.E6 K σ.toRingHom a := by
      rcases hcases with rfl | rfl | rfl
      · exact mem_orbitField_of_card_eq_two σ.toRingHom hσσ card_orbit_zero c
      · exact mem_orbitField_of_card_eq_two σ.toRingHom hσσ card_orbit_one c
      · exact (mem_orbitField_of_card_eq_one σ.toRingHom card_orbit_two c).2 (hc rfl)
    let c' : orbitField TwistTag.E6 K σ.toRingHom a := ⟨c, hcmem⟩
    have hg : yG σ a c' ∈
        twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ) :=
      Subgroup.mem_sup_left (yG_mem_twE6LongRootLevi K σ q hr hσ hK a ha c')
    refine ⟨yG σ a c' * m * (yG σ a c')⁻¹, hconj _ hg m hm, ?_⟩
    exact psi_conj_orbitY σ ha c' (m : ModGL TwistTag.E6.tag K)
  have hW : ∀ a : Fin TwistTag.E6.foldedTag.rank, a ≠ 3 → ∃ ε : Dr → K,
      (∀ γ, ε γ = 1 ∨ ε γ = -1) ∧ ∀ v ∈ N, (fun γ => ε γ * v (reflD a γ)) ∈ N := by
    intro a ha
    obtain ⟨ε, hε, hεz⟩ := psi_conj_orbitReflection (K := K) ha
    refine ⟨ε, hε, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    have hg : nG σ a ∈
        twE6LongRootLevi (stdX σ) (stdXm σ) ⊔ twE6LongRootTorus (stdX σ) (stdXm σ) :=
      Subgroup.mem_sup_left (nG_mem_twE6LongRootLevi K σ q hr hσ hK a ha)
    refine ⟨nG σ a * m * (nG σ a)⁻¹, hconj _ hg m hm, ?_⟩
    funext γ
    exact hεz (m : ModGL TwistTag.E6.tag K) γ
  rcases core_irreducible σ hσσ hσ1 N hΦ hk hX hY hW with hN | hN
  ·
    left
    refine le_antisymm (fun m hm => ?_) hXM
    have h0 : psi K (m : ModGL TwistTag.E6.tag K) = 0 := by
      have : psi K (m : ModGL TwistTag.E6.tag K) ∈ N := ⟨m, hm, rfl⟩
      rw [hN] at this
      exact this
    exact mem_stdX_of_psi_eq_zero σ (hM m hm).1 h0
  ·
    right
    refine le_antisymm hMQ (fun z hz => ?_)
    obtain ⟨hzQ, hzF⟩ := mem_Qbar_of_mem_radical σ hz
    obtain ⟨m, hm, hmz⟩ := hN (psi_mem_RPhi σ hzQ hzF)
    have hmQ := (hM m hm).1
    have h0 : psi K ((z * m⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) = 0 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, psi_mul hzQ (inv_mem hmQ), psi_inv hmQ, hmz]
      exact add_neg_cancel _
    have hzm : z * m⁻¹ ∈ stdX σ :=
      mem_stdX_of_psi_eq_zero σ (mul_mem hzQ (inv_mem hmQ)) h0
    have := M.mul_mem (hXM hzm) hm
    simpa using this

end Glue

end CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LongRoot

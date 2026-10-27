module

public import CFSG.LieType.Universal.Unitary.Extras.RankOne
public import CFSG.LieType.CentralExt.SL2Lift

public section

namespace CFSG.LieType.Steinberg

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras

variable {F : Type*} [Field F] {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c} {n : ℕ} {k : Fin (n / 2)}
  (hk : k.val + 1 < n / 2)

@[expose] noncomputable def rankOneShortHom :
    ↥(CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) →* SpecialLinearGroup (Fin 2) F where
  toFun g := ⟨toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g),
    (isBlk_short_of_mem hk g.2).2⟩
  map_one' := Subtype.ext (by
    change toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n 1) = 1
    rw [map_one]
    exact toBlock_one (lowIdx_ne_succ hk))
  map_mul' g h := Subtype.ext (by
    change toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n ((g : SU σ n) * h)) =
      toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g) *
        toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n h)
    rw [map_mul]
    exact toBlock_mul (lowIdx_ne_succ hk) (blkShort_hblk hk) (blkShort_succ_eq hk)
      (isBlk_short_of_mem hk g.2).1)

theorem coe_rankOneShortHom (g : ↥(CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k)) :
    ((rankOneShortHom hk g : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      toBlock (lowIdx k) (lowIdx ⟨k.val + 1, hk⟩) (mat σ n g) :=
  rfl

theorem rankOneShortHom_injective : Function.Injective (rankOneShortHom (hσ := hσ) hk) :=
  fun g h hgh => Subtype.ext (eq_of_toBlock_short hk g.2 h.2 (congrArg Subtype.val hgh))

theorem rankOneShortHom_surjective : Function.Surjective (rankOneShortHom (hσ := hσ) hk) := by
  set p : Fin n := lowIdx k
  set q : Fin n := lowIdx ⟨k.val + 1, hk⟩
  have hpq : p ≠ q := lowIdx_ne_succ hk
  have hp : p ≠ Fin.rev p := lowIdx_ne_rev k k
  have hq : q ≠ Fin.rev q := lowIdx_ne_rev _ _
  have hqp : q ≠ Fin.rev p := lowIdx_ne_rev _ _
  have hpq' : p ≠ Fin.rev q := lowIdx_ne_rev _ _
  rw [← MonoidHom.range_eq_top, eq_top_iff,
    ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field, Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  ·
    have hx := rootHom_mem hσ hpq hp hq hqp (toStd_short hk).symm (Multiplicative.ofAdd c)
    refine ⟨⟨_, Subgroup.mem_sup_left hx⟩, Subtype.ext ?_⟩
    rw [coe_rankOneShortHom, toBlock_of_mem_pos hk hx, mat_apply, coe_rootHom, toAdd_ofAdd,
      rootMatrix_apply_pq hpq hqp]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [SpecialLinearGroup.transvection_coe]
  ·
    have hy := rootHom_mem hσ hpq.symm hq hp hpq' (toStd_short_neg hk).symm
      (Multiplicative.ofAdd c)
    refine ⟨⟨_, Subgroup.mem_sup_right hy⟩, Subtype.ext ?_⟩
    rw [coe_rankOneShortHom, toBlock_of_mem_neg hk hy, mat_apply, coe_rootHom, toAdd_ofAdd,
      rootMatrix_apply_pq hpq.symm hpq']
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [SpecialLinearGroup.transvection_coe]
  · exact absurd rfl hij

@[expose] noncomputable def rankOneShortEquiv :
    ↥(CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) ≃* SpecialLinearGroup (Fin 2) F :=
  MulEquiv.ofBijective (rankOneShortHom hk)
    ⟨rankOneShortHom_injective hk, rankOneShortHom_surjective hk⟩

include hk in
theorem exists_rankOne_short_section [Finite F] (hF2 : ringChar F ≠ 2) {E : Type*} [Group E]
    [Finite E] {π : E →* SU σ n} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) :
    ∃ φ : ↥(CFSG.LieType.CurtisTits.rankOne (rootGroup σ hσ n) k) →* E, ∀ g, π (φ g) = g := by
  set e := rankOneShortEquiv (hσ := hσ) hk
  obtain ⟨ρ, hρ⟩ := CFSG.LieType.CentralExt.exists_lift hF2 hπ hcen h2
    ((Subgroup.subtype _).comp e.symm.toMonoidHom)
  refine ⟨ρ.comp e.toMonoidHom, fun g => ?_⟩
  have h := DFunLike.congr_fun hρ (e g)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    Subgroup.coe_subtype] at h
  exact h

end CFSG.LieType.Steinberg

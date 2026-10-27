module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S

open CFSG.RankThree.PerfectCover

instance hopfCover_finite (S : Type) [Group S] [Finite S] [Group.IsPerfect S] :
    Finite (HopfCover S) :=
  finite_hopfCover (inferInstance : Group.IsPerfect S)

section Counting

variable {S : Type} [Group S] [Finite S] [Group.IsPerfect S]

theorem card_hopfCover_eq_mul :
    Nat.card (HopfCover S) = Nat.card (hopfMultiplier S) * Nat.card S := by
  have h := Subgroup.card_ker_mul_card_range (hopfCoverMap S)
  rw [MonoidHom.range_eq_top.mpr (hopfCoverMap_surjective (S := S)), Subgroup.card_top] at h
  exact h.symm

theorem card_eq_card_ker_mul_of_surjective {A B : Type} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) :
    Nat.card A = Nat.card f.ker * Nat.card B := by
  have h := Subgroup.card_ker_mul_card_range f
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h
  exact h.symm

end Counting

section Lift

variable {S : Type} [Group S] [Finite S] [Group.IsPerfect S]

theorem exists_hopfLift {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (p : E →* S)
    (hp : Function.Surjective p) (hC : p.ker ≤ Subgroup.center E) :
    ∃ h : HopfCover S →* E, Function.Surjective h ∧ p.comp h = hopfCoverMap S ∧
      Subgroup.map h (hopfMultiplier S) = p.ker := by
  obtain ⟨-, h, hlift, -, hsurj, hmap, -⟩ :=
    perfect_central_kernel_quotient_of_hopf_multiplier p hp hC
  exact ⟨h, hsurj, hlift, hmap⟩

theorem ker_le_hopfMultiplier {E : Type} [Group E] {p : E →* S} {h : HopfCover S →* E}
    (hh : p.comp h = hopfCoverMap S) : h.ker ≤ hopfMultiplier S := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker, ← hh, MonoidHom.comp_apply, hx, map_one]

theorem card_hopfMultiplier_eq_mul {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (p : E →* S)
    (hp : Function.Surjective p) {h : HopfCover S →* E} (hsurj : Function.Surjective h)
    (hh : p.comp h = hopfCoverMap S) :
    Nat.card (hopfMultiplier S) = Nat.card h.ker * Nat.card p.ker := by
  have hS : 0 < Nat.card S := Nat.card_pos
  have e1 := card_hopfCover_eq_mul (S := S)
  have e2 := card_eq_card_ker_mul_of_surjective h hsurj
  have e3 := card_eq_card_ker_mul_of_surjective p hp
  apply Nat.eq_of_mul_eq_mul_right hS
  rw [← e1, e2, e3]
  ring

theorem card_ker_dvd_hopfMultiplier {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (p : E →* S)
    (hp : Function.Surjective p) (hC : p.ker ≤ Subgroup.center E) :
    Nat.card p.ker ∣ Nat.card (hopfMultiplier S) := by
  obtain ⟨h, hsurj, hh, -⟩ := exists_hopfLift p hp hC
  rw [card_hopfMultiplier_eq_mul p hp hsurj hh]
  exact Dvd.intro_left _ rfl

end Lift

section Main

variable {S Q Y : Type} [Group S] [Finite S] [Group.IsPerfect S]
variable [Group Q] [Finite Q] [Group.IsPerfect Q] [Group Y] [Finite Y] [Group.IsPerfect Y]

theorem exists_surj_kernel_not_three_dvd (p : Q →* S) (hp : Function.Surjective p)
    (hpc : p.ker ≤ Subgroup.center Q) (q : Y →* S) (hq : Function.Surjective q)
    (hqc : q.ker ≤ Subgroup.center Y) (hM : Nat.card (hopfMultiplier S) = 12)
    (hqk : Nat.card q.ker = 3) (h3 : 3 ∣ Nat.card p.ker) :
    ∃ π : Q →* Y, Function.Surjective π ∧ ¬ 3 ∣ Nat.card π.ker := by
  obtain ⟨hQ, hQs, hQl, -⟩ := exists_hopfLift p hp hpc
  obtain ⟨hY, hYs, hYl, -⟩ := exists_hopfLift q hq hqc
  have hMQ := card_hopfMultiplier_eq_mul p hp hQs hQl
  have hMY := card_hopfMultiplier_eq_mul q hq hYs hYl
  set NQ := hQ.ker with hNQdef
  set NY := hY.ker with hNYdef
  have hNY4 : Nat.card NY = 4 := by
    rw [hqk, hM] at hMY
    omega
  have hNQdvd : Nat.card NQ ∣ 4 := by
    obtain ⟨k, hk⟩ := h3
    rw [hk, hM] at hMQ
    exact ⟨k, by linarith [hMQ]⟩
  let T : Subgroup (HopfCover S) :=
    { carrier := {x | x ∈ hopfMultiplier S ∧ x ^ 4 = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha4⟩ ⟨hb, hb4⟩
        refine ⟨(hopfMultiplier S).mul_mem ha hb, ?_⟩
        have hc : Commute a b := by
          have := hopfMultiplier_le_center (S := S) ha
          exact ((Subgroup.mem_center_iff.1 this) b).symm
        rw [(hc.mul_pow 4), ha4, hb4, one_mul]
      one_mem' := ⟨(hopfMultiplier S).one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha4⟩
        exact ⟨(hopfMultiplier S).inv_mem ha, by rw [inv_pow, ha4, inv_one]⟩ }
  have hTM : T ≤ (hopfMultiplier S : Subgroup (HopfCover S)) := fun x hx => hx.1
  have hTdvd : Nat.card T ∣ 12 := by
    rw [← hM]
    exact Subgroup.card_dvd_of_le hTM
  have hT3 : ¬ 3 ∣ Nat.card T := by
    intro h3T
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3T
    have hx4 : (x : HopfCover S) ^ 4 = 1 := x.2.2
    have hd : orderOf (x : HopfCover S) ∣ 4 := orderOf_dvd_iff_pow_eq_one.2 hx4
    rw [Subgroup.orderOf_coe, hx] at hd
    norm_num at hd
  have hTdvd4 : Nat.card T ∣ 4 := by
    have hcop : Nat.Coprime (Nat.card T) 3 :=
      (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hT3))
    have : Nat.card T ∣ 4 * 3 := by simpa using hTdvd
    exact hcop.dvd_of_dvd_mul_right this
  have hNYT : NY ≤ T := by
    intro x hx
    have hxM : x ∈ hopfMultiplier S := ker_le_hopfMultiplier hYl hx
    refine ⟨hxM, ?_⟩
    have hd : orderOf x ∣ 4 := by
      rw [← hNY4]
      exact Subgroup.orderOf_dvd_natCard NY hx
    exact orderOf_dvd_iff_pow_eq_one.1 hd
  have hNQT : NQ ≤ T := by
    intro x hx
    have hxM : x ∈ hopfMultiplier S := ker_le_hopfMultiplier hQl hx
    refine ⟨hxM, ?_⟩
    have hd : orderOf x ∣ 4 := by
      exact (Subgroup.orderOf_dvd_natCard NQ hx).trans hNQdvd
    exact orderOf_dvd_iff_pow_eq_one.1 hd
  have hTle : Nat.card T ≤ 4 := Nat.le_of_dvd (by norm_num) hTdvd4
  have hNYle : Nat.card NY ≤ Nat.card T := Subgroup.card_le_of_le hNYT
  have hNYeq : NY = T := Subgroup.eq_of_le_of_card_ge hNYT (by omega)
  have hNQNY : NQ ≤ NY := by
    rw [hNYeq]
    exact hNQT
  let e : (HopfCover S ⧸ NQ) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective hQ hQs
  let g : (HopfCover S ⧸ NQ) →* Y := QuotientGroup.lift NQ hY (by
    intro x hx
    exact hNQNY hx)
  let π : Q →* Y := g.comp e.symm.toMonoidHom
  have hπQ : ∀ u : HopfCover S, π (hQ u) = hY u := by
    intro u
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    have : e.symm (hQ u) = (u : HopfCover S ⧸ NQ) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨u, rfl⟩ := hYs y
    exact ⟨hQ u, hπQ u⟩
  refine ⟨π, hπs, ?_⟩
  have hc1 := card_eq_card_ker_mul_of_surjective π hπs
  have hc2 := card_eq_card_ker_mul_of_surjective hQ hQs
  have hc3 := card_eq_card_ker_mul_of_surjective hY hYs
  have hYpos : 0 < Nat.card Y := Nat.card_pos
  have hkey : Nat.card π.ker * Nat.card NQ = Nat.card NY := by
    apply Nat.eq_of_mul_eq_mul_right hYpos
    calc Nat.card π.ker * Nat.card NQ * Nat.card Y
        = Nat.card NQ * (Nat.card π.ker * Nat.card Y) := by ring
      _ = Nat.card NQ * Nat.card Q := by rw [← hc1]
      _ = Nat.card (HopfCover S) := hc2.symm
      _ = Nat.card NY * Nat.card Y := hc3
  intro h3k
  have hdvd : Nat.card π.ker ∣ 4 := ⟨Nat.card NQ, by rw [← hNY4, hkey]⟩
  have h34 : 3 ∣ 4 := dvd_trans h3k hdvd
  norm_num at h34

end Main

end CFSG.LocalAnalysis.GLTheoremA.CatB.HU42S

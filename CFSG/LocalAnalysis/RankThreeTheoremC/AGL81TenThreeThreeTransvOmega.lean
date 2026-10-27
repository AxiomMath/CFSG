module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvOmegaAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeTransvOmegaLift
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsSpTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW

open CFSG.Open CFSG.AGLEmbedding Subgroup

namespace OmegaMinusEight

variable {A : Type} [Group A] [Finite A]

theorem pow_dvd_of_pow_dvd_mul {r e m k : ℕ} (hr : r.Prime) (hm : ¬ r ∣ m)
    (h : r ^ k ∣ r ^ e * m) : r ^ k ∣ r ^ e :=
  (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hr).2 hm)).dvd_of_dvd_mul_right h

theorem prime_cases_of_dvd_card_omega {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd : r ∣ 197406720) : r = 3 ∨ r = 5 ∨ r = 7 ∨ r = 17 := by
  rw [show (197406720 : ℕ) = 2 ^ 12 * 3 ^ 4 * 5 * 7 * 17 by norm_num] at hd
  rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
  · rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
    · rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
      · rcases (Nat.Prime.dvd_mul hr).1 hd with hd | hd
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
            (hr.dvd_of_dvd_pow hd)) hr2
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
            (hr.dvd_of_dvd_pow hd))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hd))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hd)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hd)))

theorem centralizes_of_odd_inner_aut {Y P : Subgroup A} (hPY : P ≤ Y) [IsSimpleGroup ↥Y]
    (hY : Nat.card Y = 197406720)
    (hAut : ∀ β : MulAut ↥Y, Odd (orderOf β) → ∃ g : ↥Y, β = MulAut.conj g)
    [IsSimpleGroup (↥P ⧸ CFSG.pCore 2 ↥P)] (hP : Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) = 1451520)
    {b : A} (hbo : Odd (orderOf b)) (hbY : b ∈ normalizer (Y : Set A))
    (hbP : b ∈ normalizer (P : Set A))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Y, b * y = y * b := by
  have hYnp : ¬ (Nat.card ↥Y).Prime := by rw [hY]; norm_num
  have hPnp : ¬ (Nat.card (↥P ⧸ CFSG.pCore 2 ↥P)).Prime := by rw [hP]; norm_num
  have hZY : Subgroup.center ↥Y = ⊥ := center_eq_bot_of_card_not_prime hYnp
  have hZP : Subgroup.center (↥P ⧸ CFSG.pCore 2 ↥P) = ⊥ := center_eq_bot_of_card_not_prime hPnp
  have hWtop : wSup (↥P ⧸ CFSG.pCore 2 ↥P) = ⊤ :=
    ParabComm.wSup_eq_top (isQuasisimple_of_card_not_prime hPnp)
  set β : MulAut ↥Y := Y.normalizerMonoidHom ⟨b, hbY⟩ with hβ
  have hβodd : Odd (orderOf β) := by
    refine hbo.of_dvd_nat ((orderOf_map_dvd _ _).trans ?_)
    rw [Subgroup.orderOf_mk]
  obtain ⟨g, hg⟩ := hAut β hβodd
  have hbg : ∀ y ∈ Y, b * y * b⁻¹ = (g : A) * y * (g : A)⁻¹ := by
    intro y hy
    have h1 := congrArg (fun φ : MulAut ↥Y => ((φ ⟨y, hy⟩ : ↥Y) : A)) hg
    simpa [hβ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] using h1
  by_cases hg1 : (g : A) = 1
  · intro y hy
    have h1 := hbg y hy
    rw [hg1, one_mul, inv_one, mul_one] at h1
    calc b * y = b * y * b⁻¹ * b := by group
      _ = y * b := by rw [h1]
  exfalso
  have hgm : g ^ orderOf β = 1 := by
    have h1 : MulAut.conj (g ^ orderOf β) = 1 := by rw [map_pow, ← hg, pow_orderOf_eq_one]
    have h2 : g ^ orderOf β ∈ Subgroup.center ↥Y := by
      rw [Subgroup.mem_center_iff]
      intro c
      have h3 := congrArg (fun φ : MulAut ↥Y => φ c) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hZY, Subgroup.mem_bot] at h2
    exact h2
  have hgodd : Odd (orderOf (g : A)) := by
    rw [Subgroup.orderOf_coe]
    exact hβodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hgm)
  have hgP : (g : A) ∈ normalizer (P : Set A) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hbg h (hPY hh)]
      exact (mem_normalizer_iff.1 hbP h).1 hh
    · intro hh
      have hhY : h ∈ Y := by
        have h1 := Y.mul_mem (Y.mul_mem (Y.inv_mem g.2) (hPY hh)) g.2
        have he : (g : A)⁻¹ * ((g : A) * h * (g : A)⁻¹) * (g : A) = h := by group
        rwa [he] at h1
      rw [← hbg h hhY] at hh
      exact (mem_normalizer_iff.1 hbP h).2 hh
  have hgcomm : ∀ w ∈ P, (g : A) * w * (g : A)⁻¹ * w⁻¹ ∈ pCoreOf 2 P := by
    intro w hw
    rw [← hbg w (hPY hw)]
    exact hW w hw (by rw [hWtop]; exact mem_top _)
  have hg_ne : orderOf (g : A) ≠ 1 := fun h => hg1 (orderOf_eq_one_iff.1 h)
  set r := (orderOf (g : A)).minFac
  have hrp : r.Prime := Nat.minFac_prime hg_ne
  have hrdvd : r ∣ orderOf (g : A) := Nat.minFac_dvd _
  have hrodd : r ≠ 2 := by
    intro h
    rw [h] at hrdvd
    exact (Nat.not_even_iff_odd.2 hgodd) (even_iff_two_dvd.2 hrdvd)
  set z : A := (g : A) ^ (orderOf (g : A) / r)
  have hzr : orderOf z = r := orderOf_pow_orderOf_div (orderOf_pos _).ne' hrdvd
  have hzY : z ∈ Y := Y.pow_mem g.2 _
  have hzP : z ∈ normalizer (P : Set A) := (normalizer (P : Set A)).pow_mem hgP _
  have hzcomm : ∀ w ∈ P, z * w * z⁻¹ * w⁻¹ ∈ pCoreOf 2 P :=
    commutator_pow_mem_pCoreOf hgP hgcomm (orderOf (g : A) / r)
  have hzodd : Odd (orderOf z) := by rw [hzr]; exact hrp.odd_of_ne_two hrodd
  set D : Subgroup A := P ⊓ centralizer {z}
  set C : Subgroup A := Y ⊓ centralizer {z}
  have hDC : D ≤ C := inf_le_inf_right _ hPY
  have hzC : z ∈ C := ⟨hzY, mem_centralizer_singleton_iff.2 rfl⟩
  have hcentC : ∀ c ∈ C, c * z = z * c := fun c hc => mem_centralizer_singleton_iff.1 hc.2
  obtain ⟨j, hj⟩ := exists_card_inf_centralizer hzP hzodd hzcomm
  have hdD : Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) ∣ Nat.card D := ⟨2 ^ j, by rw [hj, mul_comm]⟩
  have hCY : Nat.card C ∣ Nat.card Y := card_dvd_of_le inf_le_left
  have hzD : z ∉ D := by
    intro hzD
    have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨z, hzD.1⟩ ∈
        Subgroup.center (↥P ⧸ CFSG.pCore 2 ↥P) := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨d, rfl⟩ := exists_mem_inf_centralizer_lift hzP hzodd hzcomm x
      have hdz : (d : A) * z = z * (d : A) := mem_centralizer_singleton_iff.1 d.2.2
      rw [← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hdz)
    rw [hZP, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥P)) ⟨_, hcen⟩
    have hzk : z ^ 2 ^ k = 1 := by simpa using congrArg (fun x : ↥(CFSG.pCore 2 ↥P) => (x : A)) hk
    have h2 : r ∣ 2 ^ k := hzr ▸ orderOf_dvd_of_pow_eq_one hzk
    exact hrodd ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 (hrp.dvd_of_dvd_pow h2))
  have hrY : r ∣ 197406720 := by
    rw [← hY]
    have h1 : orderOf (⟨z, hzY⟩ : ↥Y) ∣ Nat.card Y := orderOf_dvd_natCard _
    rwa [Subgroup.orderOf_mk, hzr] at h1
  have key : ∀ e m : ℕ, 197406720 = r ^ e * m → ¬ r ∣ m → r ^ e ∣ 1451520 → False := by
    intro e m hem hm he
    refine hzD (mem_of_central_of_prime_order hDC hrp hzC hzr hcentC fun k hk => ?_)
    have h1 : r ^ k ∣ r ^ e * m := hem ▸ hY ▸ hk.trans hCY
    exact (pow_dvd_of_pow_dvd_mul hrp hm h1).trans (he.trans (hP ▸ hdD))
  rcases prime_cases_of_dvd_card_omega hrp hrodd hrY with h3 | h5 | h7 | h17
  · exact key 4 2437120 (by rw [h3]; norm_num) (by rw [h3]; norm_num) (by rw [h3]; norm_num)
  · exact key 1 39481344 (by rw [h5]; norm_num) (by rw [h5]; norm_num) (by rw [h5]; norm_num)
  · exact key 1 28200960 (by rw [h7]; norm_num) (by rw [h7]; norm_num) (by rw [h7]; norm_num)
  · have hCne : C ≠ Y := by
      intro hCY'
      have hzc : (⟨z, hzY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
        rw [Subgroup.mem_center_iff]
        intro c
        have : (c : A) ∈ C := by rw [hCY']; exact c.2
        exact Subtype.ext (mem_centralizer_singleton_iff.1 this.2)
      rw [hZY, Subgroup.mem_bot] at hzc
      have : z = 1 := congrArg Subtype.val hzc
      rw [this, orderOf_one, h17] at hzr
      omega
    have h17C : 17 ∣ Nat.card C := by
      have h1 : orderOf (⟨z, hzC⟩ : ↥C) ∣ Nat.card C := orderOf_dvd_natCard _
      rwa [Subgroup.orderOf_mk, hzr, h17] at h1
    have hcop : Nat.Coprime 17 (Nat.card D) := by
      rw [hj, hP]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right j (by norm_num)) (by norm_num)
    have h1 : 17 * Nat.card D ∣ Nat.card C :=
      hcop.mul_dvd_of_dvd_of_dvd h17C (card_dvd_of_le hDC)
    have h2 : 17 * 1451520 ∣ Nat.card C := (mul_dvd_mul_left 17 (hP ▸ hdD)).trans h1
    have hge : 24675840 ≤ Nat.card C := Nat.le_of_dvd Nat.card_pos h2
    have hmul : Nat.card C * C.relIndex Y = 197406720 := by
      have h3 := Subgroup.card_mul_index (C.subgroupOf Y)
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, hY] at h3
      exact h3
    have hidx : C.relIndex Y ≤ 8 := by
      by_contra hlt
      have := Nat.mul_le_mul hge (show 9 ≤ C.relIndex Y by omega)
      omega
    have h8 := (card_dvd_factorial_relIndex (inf_le_left : C ≤ Y) hCne).trans
      (Nat.factorial_dvd_factorial hidx)
    rw [hY] at h8
    have := Nat.le_of_dvd (Nat.factorial_pos 8) h8
    have h40320 : Nat.factorial 8 = 40320 := by decide
    omega

end OmegaMinusEight

open OmegaMinusEight

variable {A : Type} [Group A] [Finite A]

theorem centralizes_omegaMinusEight {Y P : Subgroup A} (hPY : P ≤ Y)
    (d d' : TauCeti.ValidLieTypeIndex)
    (hd : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .twistedD 4 q)
    (hd' : ∃ q : TauCeti.PrimePower, q.card = 2 ∧ d'.1 = .B 3 q)
    (eY : ↥Y ≃* (TauCeti.CFSGIndex.lie d).Group)
    (eP : ↥P ⧸ CFSG.pCore 2 ↥P ≃* (TauCeti.CFSGIndex.lie d').Group)
    {b : A} (hbo : Odd (orderOf b)) (hbY : b ∈ normalizer (Y : Set A))
    (hbP : b ∈ normalizer (P : Set A))
    (hW : ∀ w (hw : w ∈ P), QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨w, hw⟩ ∈
        wSup (↥P ⧸ CFSG.pCore 2 ↥P) → b * w * b⁻¹ * w⁻¹ ∈ pCoreOf 2 P) :
    ∀ y ∈ Y, b * y = y * b := by
  have hMY := statedClassicalModel_omegaMinusEight d hd eY
  haveI : IsSimpleGroup ↥Y :=
    (CFSG.LieType.Simplicity.fam_classical_converse _
      ((CFSG.Milestones.fam_classical_model_membership_alltags _).2 ⟨_, _, _, _, hMY⟩)).2.2
  have hcardY : Nat.card ↥Y = 197406720 := by
    rw [(CFSG.Timmesfeld.card_statedClassicalModel_two hMY).2.2.2.2 rfl]
    decide
  obtain ⟨q', hq2', hdq'⟩ := hd'
  obtain ⟨hqp', hqe'⟩ := primePower_eq_two hq2'
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d').Group :=
    (kFactSpTwoSimple_holds 3 d' le_rfl ⟨q', hq2', hdq'⟩).1
  haveI : IsSimpleGroup (↥P ⧸ CFSG.pCore 2 ↥P) := eP.isSimpleGroup
  have hcardP : Nat.card (↥P ⧸ CFSG.pCore 2 ↥P) = 1451520 := by
    rw [Nat.card_congr eP.toEquiv, card_catGroup_B_even le_rfl hqp' hdq', hqe']
    decide
  exact centralizes_of_odd_inner_aut hPY hcardY
    (fun β hβ => exists_conj_of_odd_orderOf_omegaMinusEight d hd eY β hβ) hcardP hbo hbY hbP hW

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.TransvW

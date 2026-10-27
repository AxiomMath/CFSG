module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888F3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R1b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888R3
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888D1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

private theorem s888c41_twoCoreIn_le_self (X : Subgroup G) : twoCoreIn X ≤ X := by
  unfold twoCoreIn CFSG.inSubgroup
  exact Subgroup.map_subtype_le _

private lemma s888c41_zpow_eq_one_or_self {a : G} (ha : a * a = 1) {x : G}
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : a ^ (2 : ℕ) = 1 := by rwa [pow_two]
  rw [zpow_eq_zpow_emod' k h2]
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    show a ^ (k % (2 : ℤ)) = 1
    rw [hk]; simp
  · right
    show a ^ (k % (2 : ℤ)) = a
    rw [hk]; simp

private lemma s888c41_kfam_zero : Kfam5 K₁ K₂ h 0 = K₁ := by simp [Kfam5]

private lemma s888c41_kfam_one : Kfam5 K₁ K₂ h 1 = K₂ := by simp [Kfam5]

private lemma s888c41_kfam_two : Kfam5 K₁ K₂ h 2 = CFSG.conjugate K₁ h := by simp [Kfam5]

private lemma s888c41_kfam_three : Kfam5 K₁ K₂ h 3 = CFSG.conjugate K₂ h := by simp [Kfam5]

private lemma s888c41_t_not_mem_zpowers_z (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : t ∉ zpowers z := by
  intro ht
  rcases s888c41_zpow_eq_one_or_self c.z_mul_self ht with h1 | hz
  · exact c.t_ne_one h1
  · exact c.t_ne_z h37 hz

private lemma s888c41_z_not_mem_zpowers_t (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ∉ zpowers t := by
  intro hz
  rcases s888c41_zpow_eq_one_or_self c.t_mul_self hz with h1 | ht
  · exact c.z_ne_one h1
  · exact c.t_ne_z h37 ht.symm

private lemma s888c41_z_not_mem_centralizer (h37 : Asc82Lemma37)
    (c : Sec5HCtx G t L S z r B A K₁ K₂ h) : z ∉ centralizer (L : Set G) := by
  intro hzC
  have hzL : z ∈ L := (c.pocket₁.2.1 c.pocket₁.1).1
  have hzZ : z ∈ centerIn L := by
    rw [sec5_mem_centerIn_iff]
    exact ⟨hzL, fun y hy => (Subgroup.mem_centralizer_iff.mp hzC y hy).symm⟩
  rw [c.centre] at hzZ
  exact s888c41_z_not_mem_zpowers_t h37 c hzZ

private lemma s888c41_pair_le_centralizer_sup {K : Fin 4 → Subgroup G} {z : G}
    (hq : Sec5B517Quad K z) {i j i' j' : Fin 4} (hij : i ≠ j) (hi'j' : i' ≠ j')
    (hii' : i ≠ i') (hij' : i ≠ j') (hji' : j ≠ i') (hjj' : j ≠ j') :
    Sec5B517Q8.pair hq i j ≤ centralizer ((K i' ⊔ K j' : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := sec5b_mem_sup_of_comm (hq.comm i j hij) hx.2
  obtain ⟨c, hc, d, hd, rfl⟩ := sec5b_mem_sup_of_comm (hq.comm i' j' hi'j') hy
  have hac : Commute a c := hq.comm i i' hii' a ha c hc
  have had : Commute a d := hq.comm i j' hij' a ha d hd
  have hbc : Commute b c := hq.comm j i' hji' b hb c hc
  have hbd : Commute b d := hq.comm j j' hjj' b hb d hd
  exact (Commute.mul_right (Commute.mul_left hac hbc) (Commute.mul_left had hbd)).eq.symm

theorem c41 (h514 : Asc82Lemma514) (h52a : Asc82Lemma52a) (h37 : Asc82Lemma37)
    (hF3 : Asc82FactOm6CentD) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {g : G}
    (hgt : g ∈ centralizer ({t} : Set G))
    (hgP : g ∈ centralizer ((twoCoreIn (K₁ ⊔ K₂) : Subgroup G) : Set G)) :
    ∃ c₀ ∈ centralizer ({t} : Set G), c₀ ∈ Qsub K₁ K₂ h ∧
      c₀ ∈ CFSG.conjugate K₁ h ⊔ CFSG.conjugate K₂ h ∧ g * c₀⁻¹ ∈ centralizer (L : Set G) := by
  classical
  have hq : Sec5B517Quad (Kfam5 K₁ K₂ h) z := sec5b517_quad h514 c
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  set R : Subgroup G := Sec5B517Q8.pair hq 2 3 with hRdef
  set E : Subgroup G := R ⊓ centralizer ({t} : Set G) with hEdef
  set D : Subgroup G := centralizer (L : Set G) with hDdef
  set Y : Subgroup G := centralizer ({t} : Set G) ⊓
    centralizer ((twoCoreIn (K₁ ⊔ K₂) : Subgroup G) : Set G) with hYdef
  have hRcard : Nat.card ↥R = 32 := by
    rw [hRdef]
    exact Sec5B517Q8.card_pair hq h23
  have hzR : z ∈ R := by
    rw [hRdef]
    exact ⟨z_mem_Q8 hq, Subgroup.mem_sup_left (hq.z_mem 2)⟩
  have htR : t ∈ R := by
    rw [hRdef]
    refine Sec5B517Q8.mem_pair_of_sq (i := 2) (j := 3) hq ?_ c.t_mul_self
    rw [s888c41_kfam_two, s888c41_kfam_three]
    exact c.t_mem_sup₃₄
  have ht_not_zpow : t ∉ zpowers z := s888c41_t_not_mem_zpowers_z h37 c
  have hEcard : Nat.card ↥E = 16 := by
    rw [hEdef]
    exact card_inf_centralizer_of_extra (R := R) (z := z) (e := t) hRcard hzR c.z_mul_self
      (fun x hx y hy => Sec5B517Q8.commutator_mem_zpowers hq h23 hx hy)
      (fun x hx h => Sec5B517Q8.central_pair hq h23 hx h) htR ht_not_zpow
  have hEinf_le : Nat.card ↥(E ⊓ D) ≤ 2 := by
    refine card_le_two_of_sq_eq_one (C := D) (P := E ⊓ D) inf_le_right ?_ ?_
    · exact h52a G t L c.toSec5Setting
    · intro x hx
      have hxsq : x * x ∈ zpowers z :=
        Sec5B517Q8.sq_mem_zpowers hq h23 hx.1.1
      rcases s888c41_zpow_eq_one_or_self c.z_mul_self hxsq with h1 | hz
      · exact h1
      · exact absurd (hz ▸ mul_mem hx.2 hx.2) (s888c41_z_not_mem_centralizer h37 c)
  have h8 : 8 ≤ D.relIndex E := by
    have hmul := Subgroup.relIndex_mul_card D E
    have hcard_le : Nat.card ↥(D ⊓ E) ≤ 2 := by
      rw [inf_comm]
      exact hEinf_le
    have h16 : 16 ≤ D.relIndex E * 2 := by
      calc (16 : ℕ) = Nat.card ↥E := hEcard.symm
        _ = D.relIndex E * Nat.card ↥(D ⊓ E) := hmul.symm
        _ ≤ D.relIndex E * 2 := Nat.mul_le_mul_left _ hcard_le
    omega
  have hYnorm : Y ≤ normalizer (L : Set G) ⊓
      centralizer ((twoCoreIn (K₁ ⊔ K₂) : Subgroup G) : Set G) := by
    intro y hy
    exact ⟨sec5b513_conjugate_eq_iff.mp (sec5_conj_L h52a c hy.1), hy.2⟩
  have hdvd : D.relIndex Y ∣ 8 := by
    rw [hDdef]
    exact hF3 G L z K₁ K₂ c.toSec5Setting.isOm6Z2 (sec5b517_oddCore_bot c) c.pocket.1
      c.pocket₁ c.pocket₂ c.ne c.comm c.prod Y hYnorm
  have hEY : E ≤ Y := by
    intro x hx
    have hxR : x ∈ R := hx.1
    refine ⟨hx.2, ?_⟩
    have hxc : x ∈ centralizer ((Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 : Subgroup G) : Set G) :=
      s888c41_pair_le_centralizer_sup (i := 2) (j := 3) (i' := 0) (j' := 1) hq h23
        (by decide) (by decide) (by decide) (by decide) (by decide) hxR
    have hle : (Kfam5 K₁ K₂ h 0 ⊔ Kfam5 K₁ K₂ h 1 : Subgroup G) = K₁ ⊔ K₂ := by
      rw [s888c41_kfam_zero, s888c41_kfam_one]
    rw [hle] at hxc
    exact Subgroup.centralizer_le (s888c41_twoCoreIn_le_self (K₁ ⊔ K₂)) hxc
  have hDnorm : ∀ y ∈ Y, ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
    intro y hy d hd
    have hconj : CFSG.conjugate L y = L := sec5_conj_L h52a c hy.1
    rw [hDdef] at hd ⊢
    rw [Subgroup.mem_centralizer_iff] at hd ⊢
    intro l hl
    have hyl : y⁻¹ * l * y ∈ L := sec5b_mem_of_conjugate_eq' hconj hl
    have hcomm := hd (y⁻¹ * l * y) hyl
    calc l * (y * d * y⁻¹) = y * ((y⁻¹ * l * y) * d) * y⁻¹ := by group
      _ = y * (d * (y⁻¹ * l * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * d * y⁻¹) * l := by group
  have hgY : g ∈ Y := ⟨hgt, hgP⟩
  obtain ⟨c₀, hc₀E, hgc₀⟩ :=
    exists_mul_of_relIndex_dvd (Y := Y) (D := D) (E := E) hEY hDnorm hdvd h8 g hgY
  refine ⟨c₀, hc₀E.2, ?_, ?_, ?_⟩
  · rw [sec5b517_Qsub_eq, hq.core_eq]
    exact hc₀E.1.1
  · have hmem : c₀ ∈ Kfam5 K₁ K₂ h 2 ⊔ Kfam5 K₁ K₂ h 3 := hc₀E.1.2
    rw [s888c41_kfam_two, s888c41_kfam_three] at hmem
    exact hmem
  · exact hgc₀

end CFSG.OddStandard.SmallF3.Omega

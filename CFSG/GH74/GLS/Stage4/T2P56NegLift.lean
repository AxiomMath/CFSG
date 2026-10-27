module

public import CFSG.GH74.GLS.Stage4.T2P56Lift
public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.GH74.GLS.LU.Local.L3Cover

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank

section CoverAt

@[expose] def U3CoverAt (q : ℕ) : Prop :=
  ∀ (J : Type) [Group J] [Finite J], IsLnEps 3 J (-1) q → ∀ (E : Type) [Group E] [Finite E],
    Group.IsPerfect E → ∀ π : E →* J, Function.Surjective π → π.ker ≤ Subgroup.center E →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧
        ∃ α : ↥(CFSG.Assembly.LowTwoRank.StatedSU 3 q F) →* E, Function.Surjective α

theorem u3CoverAt_of_l3Cover (hL3 : LU.Local.L3Cover) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ n) : U3CoverAt (p ^ n) := by
  intro J _ _ hJ E _ _ hE π hπ hker
  exact (hL3 J (-1) p n hp hp2 (Or.inr rfl) h5 hJ E hE π hπ hker).2 rfl

end CoverAt

section Schur

variable {F : Type} [Field F] [Finite F] {p n : ℕ}

theorem psu3_pair_ne (h5 : 5 ≤ p ^ n) : (3, p ^ n) ≠ (3, 2) := fun h => by
  simp only [Prod.mk.injEq, true_and] at h
  omega

theorem ker_le_center_of_surj_su (hp : p.Prime) (hF : Nat.card F = (p ^ n) ^ 2) (h5 : 5 ≤ p ^ n)
    {G' : Type} [Group G'] (β : ↥(StatedSU 3 (p ^ n) F) →* G') (hnc : ¬ ∀ a b : G', a * b = b * a)
    (hβ : Function.Surjective β) : β.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ n) F) := by
  have : Fact p.Prime := ⟨hp⟩
  have hq := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 3) hF le_rfl
    (psu3_pair_ne h5)).1
  refine CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq ?_
  by_contra h
  push Not at h
  apply hnc
  intro a b
  obtain ⟨x, rfl⟩ := hβ a
  obtain ⟨y, rfl⟩ := hβ b
  rw [h x, h y]

theorem su3_image_eq (hp : p.Prime) (hF : Nat.card F = (p ^ n) ^ 2) (h5 : 5 ≤ p ^ n)
    {P : Type} [Group P] (α : ↥(StatedSU 3 (p ^ n) F) →* P) (hα : Function.Surjective α)
    (hker : α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ n) F)) :
    IsSLnEps 3 P (-1) (p ^ n) ∨ IsLnEps 3 P (-1) (p ^ n) := by
  have : Fact p.Prime := ⟨hp⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h5
    · exact h
  have hcen := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (n := 3) hF le_rfl
    (psu3_pair_ne h5)).2
  set Z := (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (p ^ n) F) with hZ
  have hZ3 : Nat.card Z ∣ 3 := by
    rw [hZ, LU.Local.card_scalars_statedSU_three hp hn hF]
    exact Nat.gcd_dvd_left _ _
  have hkZ : α.ker ≤ Z := hcen ▸ hker
  have hK : Nat.card α.ker ∣ 3 := (Subgroup.card_dvd_of_le hkZ).trans hZ3
  rcases (Nat.dvd_prime Nat.prime_three).1 hK with h1 | h3
  · left
    have hbot : α.ker = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
    have hinj : Function.Injective α := (injective_iff_map_eq_one α).2 fun x hx => by
      have : x ∈ α.ker := hx
      rw [hbot] at this
      exact this
    exact Or.inr ⟨rfl, F, inferInstance, inferInstance, hF,
      ⟨(MulEquiv.ofBijective α ⟨hinj, hα⟩).symm⟩⟩
  · right
    have hZle : Nat.card Z ≤ Nat.card α.ker := by
      rw [h3]; exact Nat.le_of_dvd (by norm_num) hZ3
    have hKZ : α.ker = Z := Subgroup.eq_of_le_of_card_ge hkZ hZle
    exact Or.inr ⟨rfl, F, inferInstance, inferInstance, hF,
      ⟨(QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hKZ)⟩⟩

end Schur

theorem isLnEps_neg_facts {E : Type} [Group E] {p n : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ n) (hE : IsLnEps 3 E (-1) (p ^ n)) : IsSimpleGroup E ∧ Group.IsPerfect E := by
  obtain ⟨-, F, iF, iFin, hF, ⟨e⟩⟩ := hE.resolve_left (by rintro ⟨h, -⟩; norm_num at h)
  have : Fact p.Prime := ⟨hp⟩
  have hs : IsSimpleGroup (StatedProj (StatedSU 3 (p ^ n) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F p n hF 3 le_rfl
      (psu3_pair_ne h5)
  have hperf : Group.IsPerfect (StatedSU 3 (p ^ n) F) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hF le_rfl (psu3_pair_ne h5)
  have hperf' : Group.IsPerfect (StatedProj (StatedSU 3 (p ^ n) F)) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact ⟨e.isSimpleGroup, Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

section SchurStep

variable {Y : Type} [Group Y] [Finite Y]

theorem schur_step_gen_neg (N : Subgroup Y) [N.Normal] (E : Subgroup (Y ⧸ N)) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ n) (hcov : U3CoverAt (p ^ n)) [E.Normal]
    (hE : IsLnEps 3 ↥E (-1) (p ^ n)) {P : Subgroup Y} [P.Normal]
    (hPmap : P.map (QuotientGroup.mk' N) = E) (hPperf : ⁅P, P⁆ = P)
    (hBc : ∀ b ∈ P ⊓ N, ∀ x ∈ P, b * x = x * b) :
    IsSLnEps 3 ↥P (-1) (p ^ n) ∨ IsLnEps 3 ↥P (-1) (p ^ n) := by
  set π := QuotientGroup.mk' N with hπ
  let π' : ↥P →* ↥E := ((π.comp P.subtype).codRestrict E fun x => by
    rw [← hPmap]; exact ⟨x, x.2, rfl⟩)
  have hπ'surj : Function.Surjective π' := by
    intro e
    have : (e : Y ⧸ N) ∈ P.map π := by rw [hPmap]; exact e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hker : π'.ker ≤ Subgroup.center ↥P := by
    intro x hx
    have h1 : π (x : Y) = 1 := congrArg Subtype.val hx
    have hxN : (x : Y) ∈ N := (QuotientGroup.eq_one_iff (x : Y)).1 h1
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hBc x ⟨x.2, hxN⟩ g g.2).symm
  have hPperf' : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hPperf
  obtain ⟨F, iF, iFin, hF, α, hα⟩ := hcov ↥E hE ↥P hPperf' π' hπ'surj hker
  have hEnc : ¬ ∀ a b : ↥E, a * b = b * a := by
    obtain ⟨hEs, hEperf⟩ := isLnEps_neg_facts hp hp2 h5 hE
    intro hc
    have : IsMulCommutative ↥E := ⟨⟨hc⟩⟩
    exact Group.IsPerfect.not_isMulCommutative _ this
  have hker' : (π'.comp α).ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ n) F) :=
    ker_le_center_of_surj_su hp hF h5 (π'.comp α) hEnc (hπ'surj.comp hα)
  have hkα : α.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ n) F) := by
    intro x hx
    apply hker'
    have : α x = 1 := hx
    simp [MonoidHom.mem_ker, this]
  exact su3_image_eq hp hF h5 α hα hkα

end SchurStep

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem lift_core_neg (N : Subgroup Y) [N.Normal] (E : Subgroup (Y ⧸ N))
    (hL3 : LU.Local.L3Cover) [E.Normal] (hNodd : Odd (Nat.card N)) {p n : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ n) (hE : IsLnEps 3 ↥E (-1) (p ^ n)) {K : Subgroup Y}
    (hK : ⁅K, K⁆ = K) (hKE : K.map (QuotientGroup.mk' N) ≤ E) {z u a : Y} (hz2 : z * z = 1)
    (hz1 : z ≠ 1) (hu2 : u * u = 1) (hzne : z ≠ u) (hzu : z * u = u * z) (hzK : z ∈ K)
    (ha1 : a⁻¹ * z * a = u) (ha2 : a⁻¹ * u * a = z * u)
    (hstar : ∀ B : Subgroup Y, B.Normal → B ≤ N → ∀ b ∈ B, b * z = z * b → b * u = u * b) :
    ∃ P : Subgroup Y, K ≤ P ∧ (IsSLnEps 3 ↥P (-1) (p ^ n) ∨ IsLnEps 3 ↥P (-1) (p ^ n)) := by
  obtain ⟨hEs, hEperf⟩ := isLnEps_neg_facts hp hp2 h5 hE
  have hEc : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 hEperf
  obtain ⟨P, hPn, hPle, hPsup, hPperf⟩ := exists_perfect_core N E hEc
  have hKP : K ≤ P := perfect_le_core N E hNodd hPsup hK hKE
  have hPmap := map_eq_of_sup N E hPsup
  have hBc := core_centralizes N E hNodd hEs hPsup hPperf hz2 hz1 hu2 hzne hzu (hKP hzK) ha1 ha2
    (fun b hb => hstar (P ⊓ N) inferInstance inf_le_right b hb)
  exact ⟨P, hKP, schur_step_gen_neg N E hp hp2 h5 (u3CoverAt_of_l3Cover hL3 hp hp2 h5) hE hPmap
    hPperf hBc⟩

end Lift

end CFSG.GH74.GLS.Stage4.Rest

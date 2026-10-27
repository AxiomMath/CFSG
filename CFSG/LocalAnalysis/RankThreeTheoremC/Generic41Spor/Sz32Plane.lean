module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sz32Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

section Abstract

variable {X : Type*} [Group X]

theorem szd_card_zpowers_x {Q : Subgroup X} {a c y x : X} (hQ : Sz32QFacts Q a c y x) :
    Nat.card (Subgroup.zpowers x) = 5 := by
  rw [hQ.x_eq, Nat.card_zpowers,
    orderOf_pow_of_dvd (by norm_num) (by rw [hQ.ord_c]; norm_num), hQ.ord_c]

theorem szd_x_mem_Z {Q : Subgroup X} {a c y x : X} (hQ : Sz32QFacts Q a c y x) :
    x ∈ sz32Z a c := by
  have h : x ∈ Subgroup.zpowers (c ^ 5) := hQ.x_eq ▸ Subgroup.mem_zpowers x
  exact (le_sup_right : Subgroup.zpowers (c ^ 5) ≤ sz32Z a c) h

theorem szd_y_mem_Om (a c y : X) : y ∈ sz32Om a c y :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers y)

theorem szd_Z_le_Om (a c y : X) : sz32Z a c ≤ sz32Om a c y := le_sup_left

theorem szd_y_not_mem_Z {Q : Subgroup X} {a c y x : X} (hQ : Sz32QFacts Q a c y x) :
    y ∉ sz32Z a c := by
  intro hy
  have h1 : sz32Om a c y = sz32Z a c := sup_eq_left.2 (Subgroup.zpowers_le.2 hy)
  have h2 := hQ.Om_card
  rw [h1, hQ.Z_card] at h2
  norm_num at h2

theorem szd_card_sup_zpowers {A : Subgroup X} (hA : IsMulCommutative A) {g : X} (hg : g ∉ A)
    (hg5 : g ^ 5 = 1) (hcomm : ∀ a ∈ A, a * g = g * a) :
    Nat.card (A ⊔ Subgroup.zpowers g : Subgroup X) = Nat.card A * 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hc : ∀ (a : A) (n : Subgroup.zpowers g),
      Commute (A.subtype a) ((Subgroup.zpowers g).subtype n) := by
    rintro ⟨a, ha⟩ ⟨n, hn⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact Commute.zpow_right (hcomm a ha) k
  set f := MonoidHom.noncommCoprod A.subtype (Subgroup.zpowers g).subtype hc with hf_def
  have hrange : f.range = A ⊔ Subgroup.zpowers g := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hg1 : g ≠ 1 := fun h => hg (h ▸ A.one_mem)
  have hord : orderOf g = 5 := orderOf_eq_prime hg5 hg1
  have hfin : Finite (Subgroup.zpowers g) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord]; norm_num)
  have hdisj : Disjoint A (Subgroup.zpowers g) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro u ⟨huA, hug⟩
    rw [Subgroup.mem_bot]
    by_contra hu1
    apply hg
    have hle : Subgroup.zpowers u ≤ Subgroup.zpowers g := Subgroup.zpowers_le.mpr hug
    have hordu : orderOf u = 5 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp
        (hord ▸ orderOf_dvd_of_mem_zpowers hug) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hu1
      · exact h
    have heq : Subgroup.zpowers u = Subgroup.zpowers g :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordu])
    exact (Subgroup.zpowers_le.mpr huA) (heq ▸ Subgroup.mem_zpowers g)
  have hinj : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ hc).mpr ⟨A.subtype_injective, Subtype.val_injective,
      by rwa [Subgroup.range_subtype, Subgroup.range_subtype]⟩
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod,
    Nat.card_zpowers, hord]

theorem szd_inf_eq {U Z : Subgroup X} {x : X} (hU : Nat.card U = 25)
    (hx : Nat.card (Subgroup.zpowers x) = 5) (hxU : Subgroup.zpowers x ≤ U)
    (hxZ : Subgroup.zpowers x ≤ Z) (hUZ : ¬ U ≤ Z) : U ⊓ Z = Subgroup.zpowers x := by
  have hle : Subgroup.zpowers x ≤ U ⊓ Z := le_inf hxU hxZ
  haveI : Finite U := Nat.finite_of_card_ne_zero (by rw [hU]; norm_num)
  haveI hfin : Finite ↥(U ⊓ Z) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : U ⊓ Z ≤ U))
      (Subgroup.inclusion_injective _)
  have hd1 : Nat.card ↥(U ⊓ Z) ∣ 25 := hU ▸ Subgroup.card_dvd_of_le (inf_le_left : U ⊓ Z ≤ U)
  have hd2 : 5 ∣ Nat.card ↥(U ⊓ Z) := hx ▸ Subgroup.card_dvd_of_le hle
  obtain ⟨k, hk⟩ := hd2
  have hk5 : k ∣ 5 := by
    have h : 5 * k ∣ 5 * 5 := by rw [← hk]; simpa using hd1
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hk5 with h1 | h5
  · have hc : Nat.card ↥(U ⊓ Z) = 5 := by rw [hk, h1]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hx])).symm
  · exfalso
    have hc : Nat.card ↥(U ⊓ Z) = 25 := by rw [hk, h5]
    have h : U ⊓ Z = U :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : U ⊓ Z ≤ U) (by rw [hc, hU])
    exact hUZ (h ▸ inf_le_right)

theorem sz32_exists_plane {Q : Subgroup X} {a c y x : X} (hQ : Sz32QFacts Q a c y x) :
    ∃ U : Subgroup X, Sz32PlaneAbs (sz32Z a c) (sz32Om a c y) x U := by
  haveI hOmc : IsMulCommutative (sz32Om a c y) := hQ.Om_elem.1
  have hxZ : x ∈ sz32Z a c := szd_x_mem_Z hQ
  have hxOm : x ∈ sz32Om a c y := szd_Z_le_Om a c y hxZ
  have hyOm : y ∈ sz32Om a c y := szd_y_mem_Om a c y
  have hyZ : y ∉ sz32Z a c := szd_y_not_mem_Z hQ
  have hxcard : Nat.card (Subgroup.zpowers x) = 5 := szd_card_zpowers_x hQ
  have hzxZ : Subgroup.zpowers x ≤ sz32Z a c := Subgroup.zpowers_le.2 hxZ
  have hzxOm : Subgroup.zpowers x ≤ sz32Om a c y := hzxZ.trans (szd_Z_le_Om a c y)
  have hy_nmem : y ∉ Subgroup.zpowers x := fun h => hyZ (hzxZ h)
  have hy5 : y ^ 5 = 1 := hQ.Om_elem.2 y hyOm
  have hcommA : IsMulCommutative (Subgroup.zpowers x) := isMulCommutative_anti hzxOm
  have hcomm : ∀ b ∈ Subgroup.zpowers x, b * y = y * b := fun b hb =>
    setLike_mul_comm (s := sz32Om a c y) (hzxOm hb) hyOm
  have hUcard := szd_card_sup_zpowers hcommA hy_nmem hy5 hcomm
  have hleOm : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ sz32Om a c y :=
    sup_le hzxOm (Subgroup.zpowers_le.2 hyOm)
  have hUc : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup X) = 25 := by
    rw [hUcard, hxcard]
  refine ⟨Subgroup.zpowers x ⊔ Subgroup.zpowers y, ?_, ?_, hleOm, ?_, ?_⟩
  · exact ⟨isMulCommutative_anti hleOm, fun u hu => hQ.Om_elem.2 u (hleOm hu)⟩
  · rw [hUc]; norm_num
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  · refine szd_inf_eq hUc hxcard le_sup_left hzxZ ?_
    intro h
    exact hyZ (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))

end Abstract

section GLevel

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem sz32_plane {a c y : G} (hP : Sz32Struct P x J a c y) (hL : Sz32Lines P x (a ^ 5)) :
    ∃ U : Subgroup G, Sz32Plane P x a c y U := by
  obtain ⟨U, hU⟩ := sz32_exists_plane hP.facts
  have hUP : U ≤ (P : Subgroup G) := hU.le_Om.trans hP.facts.Om_le
  refine ⟨U, hU, hUP, ?_⟩
  intro g hg
  rcases hL.lines g (hg.trans hUP) with h | h
  · exact h
  · exfalso
    rw [h] at hg
    have hxU : Subgroup.zpowers x ≤ U := Subgroup.zpowers_le.2 hU.mem
    have hZ : sz32Z a c ≤ U := by
      refine sup_le hg ?_
      rw [← hP.facts.x_eq]
      exact hxU
    have hinf : U ⊓ sz32Z a c = sz32Z a c := inf_eq_right.2 hZ
    rw [hU.inf_Z] at hinf
    have hord : Nat.card (Subgroup.zpowers x) = 5 := by
      rw [Nat.card_zpowers]
      exact hP.decomp.pres.x_ord
    have hcard := hP.facts.Z_card
    rw [← hinf, hord] at hcard
    norm_num at hcard

end GLevel

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

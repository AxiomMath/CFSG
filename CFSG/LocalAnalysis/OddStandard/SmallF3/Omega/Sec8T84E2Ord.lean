module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84E2Cent

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open scoped Pointwise

theorem sec8t84_cent_order {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
    {B E : Subgroup G} (hE : Sec8E G t L S z g B E) (hCE : Asc82FinkCE) (hAut : Asc82FinkAut)
    (h89 : Asc82Lemma89) {R : Subgroup G}
    (hR : IsSylow2Of R (normalizer (E : Set G) ⊓ centralizer ({t} : Set G))) :
    Nat.card ↥R = 2 ^ 8 := by
  let X : Subgroup G := normalizer (E : Set G)
  let C : Subgroup G := centralizer (E : Set G)
  let Y : Subgroup G := X ⊓ centralizer ({t} : Set G)
  let K : Subgroup G := zpowers t ⊔ C
  let F : Subgroup (MulAut ↥B) := autIn (centralizer ({t} : Set G)) B
  obtain ⟨φ, hφsurj, hφker⟩ := (hAut G t L S z g B E hE).1
  have hFcard : Nat.card ↥F = 360 := by
    obtain ⟨e⟩ := h89 G t L S z g B hE.ctx
    calc Nat.card ↥F = Nat.card ↥(alternatingGroup (Fin 6)) := Nat.card_congr e.toEquiv
      _ = 360 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        norm_num [Nat.factorial]
  have hCX : (C.subgroupOf X).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer (E : Set G)
  have hXC : X ≤ normalizer (C : Set G) := by
    haveI : (C.subgroupOf X).Normal := hCX
    exact Subgroup.le_normalizer_of_normal_subgroupOf
      (Subgroup.centralizer_le_normalizer (E : Set G))
  have hYC : Y ≤ normalizer (C : Set G) := le_trans inf_le_left hXC
  let inclY : ↥Y →* ↥(Y ⊔ C) := Subgroup.inclusion (show Y ≤ Y ⊔ C from le_sup_left)
  let ψ : ↥Y →* ↥F := φ.comp inclY
  have hψsurj : Function.Surjective ψ := by
    intro f
    obtain ⟨h, hh⟩ := hφsurj f
    have hmem : (h : G) ∈ (Y : Set G) * (C : Set G) := by
      have hcoe : ((Y ⊔ C : Subgroup G) : Set G) = (Y : Set G) * (C : Set G) :=
        Subgroup.coe_mul_of_left_le_normalizer_right Y C hYC
      rw [← hcoe]
      exact h.2
    obtain ⟨y, hy, c, hc, hyc⟩ := hmem
    refine ⟨⟨y, hy⟩, ?_⟩
    have hker_c : φ (⟨c, Subgroup.mem_sup_right hc⟩ : ↥(Y ⊔ C)) = 1 := by
      rw [← MonoidHom.mem_ker, hφker, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_right hc
    have hh' : h = (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ C)) *
        ⟨c, Subgroup.mem_sup_right hc⟩ := by
      apply Subtype.ext
      show (h : G) = y * c
      exact hyc.symm
    rw [← hh, hh', map_mul, hker_c, mul_one]
    rfl
  have hψker : ψ.ker = (K ⊓ Y).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hy
      refine ⟨?_, y.2⟩
      have h1 : inclY y ∈ φ.ker := hy
      rw [hφker, Subgroup.mem_subgroupOf] at h1
      exact h1
    · rintro ⟨hyK, -⟩
      change φ (inclY y) = 1
      rw [← MonoidHom.mem_ker, hφker, Subgroup.mem_subgroupOf]
      exact hyK
  have hcardY : Nat.card ↥Y = Nat.card ↥F * Nat.card ↥(K ⊓ Y) := by
    have h1 : Nat.card ↥Y = Nat.card (↥Y ⧸ ψ.ker) * Nat.card ↥ψ.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    have h2 : Nat.card (↥Y ⧸ ψ.ker) = Nat.card ↥F :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (φ := ψ) hψsurj).toEquiv
    have h3 : Nat.card ↥ψ.ker = Nat.card ↥(K ⊓ Y) := by
      rw [hψker]
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (show K ⊓ Y ≤ Y from inf_le_right)).toEquiv
    rw [h1, h2, h3]
  obtain ⟨n, hnodd, hncard⟩ := (sec8t84_cent_E_card (G := G) hE hCE).2
  have hKinf : Nat.card ↥(K ⊓ Y) =
      2 * Nat.card ↥(C ⊓ centralizer ({t} : Set G)) :=
    sec8t84_K_inf_card (G := G) hE hCE
  have hncard' : Nat.card ↥(C ⊓ centralizer ({t} : Set G)) = 2 ^ 4 * n := hncard
  have hYcard : Nat.card ↥Y = 2 ^ 8 * (45 * n) := by
    rw [hcardY, hFcard, hKinf, hncard']
    ring
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hR.2.1
  have hrel : Nat.card ↥Y = Nat.card ↥R * R.relIndex Y := by
    have h := Subgroup.relIndex_mul_card (H := R) (K := Y)
    rw [inf_of_le_left hR.1, mul_comm] at h
    exact h.symm
  have huodd : Odd (R.relIndex Y) :=
    Nat.not_even_iff_odd.mp (fun he => hR.2.2 (even_iff_two_dvd.mp he))
  have hodd : Odd (45 * n) := Odd.mul (by norm_num) hnodd
  have heq : 2 ^ a * R.relIndex Y = 2 ^ 8 * (45 * n) := by
    calc 2 ^ a * R.relIndex Y = Nat.card ↥R * R.relIndex Y := by rw [ha]
      _ = Nat.card ↥Y := hrel.symm
      _ = 2 ^ 8 * (45 * n) := hYcard
  have hcop_a : Nat.Coprime (2 ^ a) (45 * n) :=
    (Nat.coprime_two_left.mpr hodd).pow_left a
  have hcop_8 : Nat.Coprime (2 ^ 8) (R.relIndex Y) :=
    (Nat.coprime_two_left.mpr huodd).pow_left 8
  have hdvd1 : 2 ^ a ∣ 2 ^ 8 := hcop_a.dvd_of_dvd_mul_right ⟨R.relIndex Y, heq.symm⟩
  have hdvd2 : 2 ^ 8 ∣ 2 ^ a := hcop_8.dvd_of_dvd_mul_right ⟨45 * n, heq⟩
  have ha8 : 2 ^ a = 2 ^ 8 := Nat.dvd_antisymm hdvd1 hdvd2
  rw [ha, ha8]

end CFSG.OddStandard.SmallF3.Omega

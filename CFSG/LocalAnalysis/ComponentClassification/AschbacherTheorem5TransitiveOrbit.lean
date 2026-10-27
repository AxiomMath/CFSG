module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveBasic

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

@[expose] def centralizing (D : Subgroup G) (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    Subgroup G :=
  ((Subgroup.centralizer (Ā : Set (D ⧸ aschbacherThm5OddCore D))).comap
    (QuotientGroup.mk' (aschbacherThm5OddCore D))).map D.subtype

theorem mem_centralizing_iff (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) (y : G) :
    y ∈ centralizing D Ā ↔ y ∈ D ∧
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D Ā) y := by
  rw [centralizing, Subgroup.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨d.2, (centralizes_iff_quotient_commutes D Ā d).mpr fun a ha => ?_⟩
    exact ((Subgroup.mem_centralizer_iff.mp hd) a ha).symm
  · rintro ⟨hy, hcent⟩
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((centralizes_iff_quotient_commutes D Ā ⟨y, hy⟩).mp hcent a ha).symm

theorem centralizing_le (Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)) :
    centralizing D Ā ≤ D :=
  Subgroup.map_subtype_le _

theorem centralizes_of_mem_centralizing {Ā : Subgroup (D ⧸ aschbacherThm5OddCore D)} {y : G}
    (hy : y ∈ centralizing D Ā) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D Ā) y :=
  ((mem_centralizing_iff Ā y).mp hy).2

theorem factor_le_centralizing (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    {i j : Fin r} (hij : i ≠ j) :
    aschbacherThm5Preimage D (Abar j) ≤ centralizing D (Abar i) := by
  intro y hy
  exact (mem_centralizing_iff (Abar i) y).mpr
    ⟨preimage_le D _ hy, cross_factor_centralizes D Abar hcomm i j hij y hy⟩

@[expose] def IsInvariant (D : Subgroup G) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (I : Set (Fin r)) : Prop :=
  ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ k ∈ I, ∀ l,
    (aschbacherThm5Preimage D (Abar k)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar l) → l ∈ I

@[expose] def orbit (D : Subgroup G) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (i : Fin r) : Set (Fin r) :=
  {k | ∃ h ∈ Subgroup.normalizer (D : Set G),
    (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
      aschbacherThm5Preimage D (Abar k)}

theorem mem_orbit_self (i : Fin r) : i ∈ orbit D Abar i :=
  ⟨1, Subgroup.one_mem _, by
    rw [map_one]
    exact Subgroup.map_id _⟩

theorem map_conj_inv {Y Z : Subgroup G} {h : G}
    (hYZ : Y.map (MulAut.conj h).toMonoidHom = Z) :
    Z.map (MulAut.conj h⁻¹).toMonoidHom = Y := by
  rw [← hYZ, Subgroup.map_map]
  convert Subgroup.map_id Y
  ext x
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

theorem orbit_isInvariant (i : Fin r) : IsInvariant D Abar (orbit D Abar i) := by
  rintro h hh k ⟨h', hh', hk⟩ l hl
  refine ⟨h * h', Subgroup.mul_mem _ hh hh', ?_⟩
  rw [← hl, ← hk, Subgroup.map_map, map_mul]
  rfl

theorem orbit_compl_isInvariant (i : Fin r) : IsInvariant D Abar (orbit D Abar i)ᶜ := by
  intro h hh k hk l hl hlorb
  apply hk
  obtain ⟨h', hh', hl'⟩ := hlorb
  refine ⟨h⁻¹ * h', Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hh', ?_⟩
  rw [map_mul, ← map_conj_inv hl, ← hl', Subgroup.map_map]
  rfl

@[expose] def orbitProduct (D : Subgroup G)
    (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)) (I : Set (Fin r)) : Subgroup G :=
  ⨆ k ∈ I, aschbacherThm5Preimage D (Abar k)

theorem factor_le_orbitProduct {I : Set (Fin r)} {k : Fin r} (hk : k ∈ I) :
    aschbacherThm5Preimage D (Abar k) ≤ orbitProduct D Abar I :=
  le_iSup₂_of_le k hk le_rfl

theorem orbitProduct_le_D (I : Set (Fin r)) : orbitProduct D Abar I ≤ D :=
  iSup₂_le fun k _ => preimage_le D (Abar k)

theorem orbitProduct_le_centralizing
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    {I : Set (Fin r)} {j : Fin r} (hj : j ∉ I) :
    orbitProduct D Abar I ≤ centralizing D (Abar j) :=
  iSup₂_le fun _ hk => factor_le_centralizing hcomm (fun hjk => hj (hjk ▸ hk))

theorem normalizer_le_normalizer_orbitProduct [Finite G] {I : Set (Fin r)}
    (hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j))
    (hI : IsInvariant D Abar I) :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (orbitProduct D Abar I : Set G) := by
  intro h hh
  rw [← Subgroup.mem_normalizer_iff_map_conj_eq.symm]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [orbitProduct, Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hk => ?_
    obtain ⟨l, hl⟩ := hperm h hh k
    rw [MulEquiv.toMonoidHom_eq_coe] at hl
    rw [hl]
    exact factor_le_orbitProduct (hI h hh k hk l hl)
  · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]

theorem tightlyEmbedded_of_le_centralizing [Finite G] (hC : Counterexample G D r Abar)
    {Q : Subgroup G} {k j : Fin r} (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q)
    (hQj : Q ≤ centralizing D (Abar j))
    (hHQ : Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup.normalizer (Q : Set G) = Subgroup.normalizer (D : Set G) ∧ TightlyEmbedded Q := by
  have hQD : Q ≤ D := hQj.trans (centralizing_le _)
  have hQH : Q ≤ Subgroup.normalizer (D : Set G) := hQD.trans Subgroup.le_normalizer
  have hN : Subgroup.normalizer (Q : Set G) = Subgroup.normalizer (D : Set G) := by
    refine le_antisymm (fun g hg => ?_) hHQ
    apply mem_normalizer_of_le_sup hC k g Q _ hQH (hkQ.trans le_sup_left)
    have hfix : rightConjugate Q g = Q := (rightConjugate_eq_self_iff Q g).mpr hg
    rw [← hfix]
    exact Subgroup.map_mono hQH
  refine ⟨hN, even_iff_two_dvd.mpr ((even_iff_two_dvd.mp (factor_even hC.hyp k)).trans
    (Subgroup.card_dvd_of_le hkQ)), ?_⟩
  intro x hx
  rw [hN] at hx
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  have htQ : (t : G) ∈ Q := (Subgroup.mem_inf.mp t.2).1
  have htQx : x * (t : G) * x⁻¹ ∈ Q :=
    (mem_rightConjugate_iff Q x t).mp (Subgroup.mem_inf.mp t.2).2
  have ht2 : (t : G) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at ht
    rw [← ht]
    exact pow_orderOf_eq_one _
  have ht1 : (t : G) ≠ 1 := by
    intro h1
    rw [← Subgroup.orderOf_coe, h1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  apply hx
  apply mem_normalizer_of_fusion hC j j (t := x * (t : G) * x⁻¹) (g := x)
  · refine ⟨1, ?_⟩
    rw [pow_one, show (x * (t : G) * x⁻¹) ^ 2 = x * (t : G) ^ 2 * x⁻¹ by
      rw [pow_two, pow_two]; group, ht2]
    group
  · intro h1
    apply ht1
    calc (t : G) = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  · exact centralizes_of_mem_centralizing (hQj htQx)
  · have heq : x⁻¹ * (x * (t : G) * x⁻¹) * x = t := by group
    rw [heq]
    exact centralizes_of_mem_centralizing (hQj htQ)

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5

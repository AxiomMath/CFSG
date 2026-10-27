module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10L1011P2Data

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] {L B' : Subgroup G} {c1 c2 : G}

theorem sec1011_LC_conj {n x : G} (hn : n ∈ normalizer (L : Set G))
    (hx : x ∈ L ⊔ centralizer (L : Set G)) : n * x * n⁻¹ ∈ L ⊔ centralizer (L : Set G) := by
  obtain ⟨l, hl, d, hd, rfl⟩ := exists_mul_of_mem_sup_of_commute
    (fun h hh k hk => Subgroup.mem_centralizer_iff.mp hk h hh) hx
  have hL : n * l * n⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hn l).mp hl
  have hC : n * d * n⁻¹ ∈ centralizer (L : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun l' hl' => ?_
    have hmem : n⁻¹ * l' * n ∈ L := (Subgroup.mem_normalizer_iff''.mp hn l').mp hl'
    have hcd : (n⁻¹ * l' * n) * d = d * (n⁻¹ * l' * n) :=
      Subgroup.mem_centralizer_iff.mp hd (n⁻¹ * l' * n) hmem
    calc l' * (n * d * n⁻¹)
        = n * ((n⁻¹ * l' * n) * d) * n⁻¹ := by group
      _ = n * (d * (n⁻¹ * l' * n)) * n⁻¹ := by rw [hcd]
      _ = (n * d * n⁻¹) * l' := by group
  have heq : n * (l * d) * n⁻¹ = (n * l * n⁻¹) * (n * d * n⁻¹) := by group
  rw [heq]
  exact Subgroup.mul_mem_sup hL hC

private theorem sec1011_inv_eq_of_orderOf_eq_two {A : Type*} [Group A] [Finite A] [IsCyclic A]
    {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  haveI : Fintype A := Fintype.ofFinite A
  have hd : 2 ∣ Fintype.card A := hx ▸ orderOf_dvd_card
  have h := IsCyclic.card_orderOf_eq_totient (α := A) (d := 2) hd
  rw [Nat.totient_two] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hxa : x ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩
  have hya : y ∈ ({a} : Finset A) := ha ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
  rw [Finset.mem_singleton] at hxa hya
  rw [hxa, hya]

theorem sec1011_C_invol_unique [Finite G]
    (h102 : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G)))) {D : Subgroup G}
    (hD : D ≤ centralizer (L : Set G)) (hsq : ∀ x ∈ D, x * x = 1) {x y : G} (hx : x ∈ D)
    (hy : y ∈ D) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 ↥D := fun g => ⟨1, by
    have h := hsq (g : G) g.2
    simp only [pow_one]
    exact Subtype.ext (by simpa [pow_two] using h)⟩
  have hD'2 : IsPGroup 2 (D.subgroupOf (centralizer (L : Set G))) :=
    hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hD).symm
  obtain ⟨Q, hQle⟩ := hD'2.exists_le_sylow
  haveI : IsCyclic ↥(Q : Subgroup ↥(centralizer (L : Set G))) := h102 Q
  have hD'cyc : IsCyclic ↥(D.subgroupOf (centralizer (L : Set G))) :=
    Subgroup.isCyclic_of_le hQle
  haveI : IsCyclic ↥(D.subgroupOf (centralizer (L : Set G))) := hD'cyc
  haveI : IsCyclic ↥D := isCyclic_of_surjective
    (Subgroup.subgroupOfEquivOfLe hD) (Subgroup.subgroupOfEquivOfLe hD).surjective
  have hx2 : orderOf (⟨x, hx⟩ : ↥D) = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨Subtype.ext (by simpa [pow_two] using hsq x hx),
      fun h => hx1 (Subtype.ext_iff.mp h)⟩
  have hy2 : orderOf (⟨y, hy⟩ : ↥D) = 2 := by
    rw [orderOf_eq_prime_iff]
    exact ⟨Subtype.ext (by simpa [pow_two] using hsq y hy),
      fun h => hy1 (Subtype.ext_iff.mp h)⟩
  exact Subtype.ext_iff.mp (sec1011_inv_eq_of_orderOf_eq_two hx2 hy2)

private theorem sec1011_C_part_sq {l d : G} (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (hsq : ∀ b ∈ B', b * b = 1) (hl : l ∈ L) (hd : d ∈ centralizer (L : Set G))
    (hb : l * d ∈ B') : d * d = 1 := by
  have hcomm : d * l = l * d := (Subgroup.mem_centralizer_iff.mp hd l hl).symm
  have hld : (l * d) * (l * d) = (l * l) * (d * d) := by
    calc (l * d) * (l * d) = l * (d * l) * d := by group
      _ = l * (l * d) * d := by rw [hcomm]
      _ = (l * l) * (d * d) := by group
  have hprod : (l * l) * (d * d) = 1 := by rw [← hld]; exact hsq (l * d) hb
  have hdd : d * d = (l * l)⁻¹ := (mul_eq_one_iff_inv_eq.mp hprod).symm
  have hmem : d * d ∈ L ⊓ centralizer (L : Set G) :=
    Subgroup.mem_inf.mpr ⟨by rw [hdd]; exact L.inv_mem (L.mul_mem hl hl),
      (centralizer (L : Set G)).mul_mem hd hd⟩
  have hbot : d * d ∈ (⊥ : Subgroup G) := by rwa [hLC] at hmem
  exact Subgroup.mem_bot.mp hbot

theorem sec1011_proj_unique [Finite G] (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (h102 : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G)))) (hsq : ∀ b ∈ B', b * b = 1)
    {l l' d d' : G} (hl : l ∈ L) (hl' : l' ∈ L) (hd : d ∈ centralizer (L : Set G))
    (hd' : d' ∈ centralizer (L : Set G)) (hb : l * d ∈ B') (hb' : l' * d' ∈ B') (hd1 : d ≠ 1)
    (hd1' : d' ≠ 1) : d = d' := by
  let D : Subgroup G :=
    { carrier := {d | d ∈ centralizer (L : Set G) ∧ ∃ l ∈ L, l * d ∈ B'}
      one_mem' := ⟨(centralizer (L : Set G)).one_mem,
        ⟨1, L.one_mem, by simpa using B'.one_mem⟩⟩
      mul_mem' := by
        rintro d1 d2 ⟨hd1C, l1, hl1, hb1⟩ ⟨hd2C, l2, hl2, hb2⟩
        refine ⟨(centralizer (L : Set G)).mul_mem hd1C hd2C, l1 * l2, L.mul_mem hl1 hl2, ?_⟩
        have hdl : d1 * l2 = l2 * d1 := (Subgroup.mem_centralizer_iff.mp hd1C l2 hl2).symm
        have heq : (l1 * l2) * (d1 * d2) = (l1 * d1) * (l2 * d2) := by
          calc (l1 * l2) * (d1 * d2) = l1 * (l2 * d1) * d2 := by group
            _ = l1 * (d1 * l2) * d2 := by rw [← hdl]
            _ = (l1 * d1) * (l2 * d2) := by group
        rw [heq]
        exact B'.mul_mem hb1 hb2
      inv_mem' := by
        rintro d ⟨hdC, l, hl, hb⟩
        refine ⟨(centralizer (L : Set G)).inv_mem hdC, l⁻¹, L.inv_mem hl, ?_⟩
        have hcomm : l⁻¹ * d⁻¹ = d⁻¹ * l⁻¹ :=
          Subgroup.mem_centralizer_iff.mp ((centralizer (L : Set G)).inv_mem hdC) l⁻¹
            (L.inv_mem hl)
        have hbinv : d⁻¹ * l⁻¹ ∈ B' := by simpa [mul_inv_rev] using B'.inv_mem hb
        rw [hcomm]
        exact hbinv }
  have hDC : D ≤ centralizer (L : Set G) := fun d hd => hd.1
  have hDsq : ∀ d ∈ D, d * d = 1 := by
    rintro d ⟨hdC, l, hl, hb⟩
    exact sec1011_C_part_sq hLC hsq hl hdC hb
  exact sec1011_C_invol_unique h102 hDC hDsq ⟨hd, ⟨l, hl, hb⟩⟩ ⟨hd', ⟨l', hl', hb'⟩⟩ hd1 hd1'

private theorem sec1011_conj_mem_L [Finite G] (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (h102 : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G)))) {b1 c : G}
    (hb1 : b1 ∈ B') (hsq : ∀ b ∈ B', b * b = 1) (hcB : c ∈ normalizer (B' : Set G))
    (hcLC : c ∈ L ⊔ centralizer (L : Set G))
    (hB'LC : B' ≤ L ⊔ centralizer (L : Set G)) :
    b1 * (c * b1 * c⁻¹) ∈ L := by
  have hcommLC : ∀ h ∈ L, ∀ k ∈ centralizer (L : Set G), h * k = k * h :=
    fun h hh k hk => Subgroup.mem_centralizer_iff.mp hk h hh
  obtain ⟨l1, hl1, d1, hd1C, hb1eq⟩ := exists_mul_of_mem_sup_of_commute hcommLC (hB'LC hb1)
  obtain ⟨lc, hlc, dc, hdcC, hceq⟩ := exists_mul_of_mem_sup_of_commute hcommLC hcLC
  have hb1' : l1 * d1 ∈ B' := by rw [← hb1eq]; exact hb1
  have hd1_sq : d1 * d1 = 1 := sec1011_C_part_sq hLC hsq hl1 hd1C hb1'
  have hl2 : lc * l1 * lc⁻¹ ∈ L := L.mul_mem (L.mul_mem hlc hl1) (L.inv_mem hlc)
  have hdc_l1 : dc * l1 = l1 * dc := (Subgroup.mem_centralizer_iff.mp hdcC l1 hl1).symm
  have heC : dc * d1 * dc⁻¹ ∈ centralizer (L : Set G) :=
    (centralizer (L : Set G)).mul_mem ((centralizer (L : Set G)).mul_mem hdcC hd1C)
      ((centralizer (L : Set G)).inv_mem hdcC)
  have hX_lc : (dc * d1 * dc⁻¹) * lc⁻¹ = lc⁻¹ * (dc * d1 * dc⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp heC lc⁻¹ (L.inv_mem hlc)).symm
  have hconj_eq : c * b1 * c⁻¹ = (lc * l1 * lc⁻¹) * (dc * d1 * dc⁻¹) := by
    rw [hceq, hb1eq, mul_inv_rev]
    rw [show (lc * dc) * (l1 * d1) * (dc⁻¹ * lc⁻¹)
          = lc * (dc * l1) * d1 * dc⁻¹ * lc⁻¹ by group]
    rw [hdc_l1]
    rw [show lc * (l1 * dc) * d1 * dc⁻¹ * lc⁻¹
          = (lc * l1) * ((dc * d1 * dc⁻¹) * lc⁻¹) by group]
    rw [hX_lc]
    group
  have hcBconj : c * b1 * c⁻¹ ∈ B' := (Subgroup.mem_normalizer_iff.mp hcB b1).mp hb1
  have hb' : (lc * l1 * lc⁻¹) * (dc * d1 * dc⁻¹) ∈ B' := by
    rw [← hconj_eq]; exact hcBconj
  have heq1 : d1 = dc * d1 * dc⁻¹ ∨ d1 = 1 := by
    by_cases h1 : d1 = 1
    · exact Or.inr h1
    · refine Or.inl (sec1011_proj_unique hLC h102 hsq hl1 hl2 hd1C heC hb1' hb' h1 ?_)
      intro hcon
      apply h1
      have := congrArg (fun z => dc⁻¹ * z * dc) hcon
      simpa [mul_assoc] using this
  have hd1e : d1 * (dc * d1 * dc⁻¹) = 1 := by
    rcases heq1 with heq1 | h1
    · rw [← heq1, hd1_sq]
    · rw [h1]; simp
  have hd1_l2 : d1 * (lc * l1 * lc⁻¹) = (lc * l1 * lc⁻¹) * d1 :=
    (Subgroup.mem_centralizer_iff.mp hd1C (lc * l1 * lc⁻¹) hl2).symm
  have hmain : b1 * (c * b1 * c⁻¹) = l1 * (lc * l1 * lc⁻¹) := by
    rw [hconj_eq, hb1eq]
    calc (l1 * d1) * ((lc * l1 * lc⁻¹) * (dc * d1 * dc⁻¹))
        = l1 * (d1 * (lc * l1 * lc⁻¹)) * (dc * d1 * dc⁻¹) := by group
      _ = l1 * ((lc * l1 * lc⁻¹) * d1) * (dc * d1 * dc⁻¹) := by rw [hd1_l2]
      _ = (l1 * (lc * l1 * lc⁻¹)) * (d1 * (dc * d1 * dc⁻¹)) := by group
      _ = l1 * (lc * l1 * lc⁻¹) := by rw [hd1e, mul_one]
  rw [hmain]
  exact L.mul_mem hl1 hl2

theorem sec1011_p2_le [Finite G] (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (h102 : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G)))) (hd : Sec1011P2Data L B' c1 c2) :
    B' ≤ L := by
  have hinv_sq : ∀ b ∈ B', b⁻¹ = b := by
    intro b hb
    exact (eq_inv_of_mul_eq_one_right (hd.sq b hb)).symm
  have hB'LC : B' ≤ L ⊔ centralizer (L : Set G) := by
    intro b hb
    obtain ⟨b1, hb1, b2, hb2, hspan⟩ := hd.span b hb
    have hf1 : b1 * (c1 * b1 * c1⁻¹) ∈ L ⊔ centralizer (L : Set G) := by
      have hconj : b1 * c1 * b1⁻¹ ∈ L ⊔ centralizer (L : Set G) :=
        sec1011_LC_conj (hd.normL hb1) hd.c1LC
      have heq : b1 * (c1 * b1 * c1⁻¹) = (b1 * c1 * b1⁻¹) * c1⁻¹ := by
        rw [hinv_sq b1 hb1]; group
      rw [heq]
      exact (L ⊔ centralizer (L : Set G)).mul_mem hconj
        ((L ⊔ centralizer (L : Set G)).inv_mem hd.c1LC)
    have hf2 : b2 * (c2 * b2 * c2⁻¹) ∈ L ⊔ centralizer (L : Set G) := by
      have hconj : b2 * c2 * b2⁻¹ ∈ L ⊔ centralizer (L : Set G) :=
        sec1011_LC_conj (hd.normL hb2) hd.c2LC
      have heq : b2 * (c2 * b2 * c2⁻¹) = (b2 * c2 * b2⁻¹) * c2⁻¹ := by
        rw [hinv_sq b2 hb2]; group
      rw [heq]
      exact (L ⊔ centralizer (L : Set G)).mul_mem hconj
        ((L ⊔ centralizer (L : Set G)).inv_mem hd.c2LC)
    rw [hspan]
    exact (L ⊔ centralizer (L : Set G)).mul_mem hf1 hf2
  intro b hb
  obtain ⟨b1, hb1, b2, hb2, hspan⟩ := hd.span b hb
  have hf1 : b1 * (c1 * b1 * c1⁻¹) ∈ L :=
    sec1011_conj_mem_L hLC h102 hb1 hd.sq hd.c1B hd.c1LC hB'LC
  have hf2 : b2 * (c2 * b2 * c2⁻¹) ∈ L :=
    sec1011_conj_mem_L hLC h102 hb2 hd.sq hd.c2B hd.c2LC hB'LC
  rw [hspan]
  exact L.mul_mem hf1 hf2

end CFSG.OddStandard.SmallF3.Omega

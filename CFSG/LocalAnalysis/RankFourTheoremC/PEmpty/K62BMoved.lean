module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BComp
import CFSG.Goldschmidt.Steps.Sec82PGroup
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62BCount

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

open CFSG CFSG.Open CFSG.LocalCores Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.Lemma213 (cjComp mem_cjComp_of_mem)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {x z : Y}

theorem moved_smul_eq_self_iff (g : Y) (C : ComponentIndex Y) :
    g • C = C ↔ g ∈ normalizer (C.1 : Set Y) := by
  rw [mem_normalizer_iff_map_conj_eq]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

section Card

variable {P : Subgroup Y}

theorem Cfg.le_card_movedOrbit (h : Cfg p P x z) {C : ComponentIndex Y} (hC : ¬ Fixed P C) :
    p ≤ Nat.card ↥(MulAction.orbit ↥P C) := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨n, hn⟩ := h.isPGroup.index (MulAction.stabilizer ↥P C)
  have hidx : (MulAction.stabilizer ↥P C).index = Nat.card ↥(MulAction.orbit ↥P C) := by
    rw [MulAction.index_stabilizer, Nat.card_coe_set_eq]
  have hne : (MulAction.stabilizer ↥P C).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hC
    intro g hg
    have hmem : (⟨g, hg⟩ : ↥P) ∈ MulAction.stabilizer ↥P C := by
      rw [h1]
      exact Subgroup.mem_top _
    exact (moved_smul_eq_self_iff g C).1 (MulAction.mem_stabilizer_iff.1 hmem)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hn)
  rw [← hidx, hn]
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n := Nat.pow_le_pow_right h.prime.pos (Nat.one_le_iff_ne_zero.2 hn0)

end Card

section Family

variable (P : Subgroup Y) (C : ComponentIndex Y)

abbrev MovedOrbit : Type := ↥(MulAction.orbit ↥P C)

noncomputable def movedRep (i : MovedOrbit P C) : ↥P :=
  Classical.choose (MulAction.mem_orbit_iff.mp i.2)

theorem movedRep_smul (i : MovedOrbit P C) : movedRep P C i • C = i.1 :=
  Classical.choose_spec (MulAction.mem_orbit_iff.mp i.2)

noncomputable def movedFam (U : Subgroup Y) (i : MovedOrbit P C) : Subgroup Y :=
  U.map (MulAut.conj ((movedRep P C i : ↥P) : Y)).toMonoidHom

variable {P C}

theorem moved_mem_conjMap_iff {U : Subgroup Y} {a v : Y} :
    v ∈ U.map (MulAut.conj a).toMonoidHom ↔ ∃ u ∈ U, a * u * a⁻¹ = v := by
  simp [Subgroup.mem_map]

theorem mem_movedFam_iff {U : Subgroup Y} {i : MovedOrbit P C} {v : Y} :
    v ∈ movedFam P C U i ↔ ∃ u ∈ U, ((movedRep P C i : ↥P) : Y) * u *
      ((movedRep P C i : ↥P) : Y)⁻¹ = v :=
  moved_mem_conjMap_iff

theorem movedFam_le_comp {U : Subgroup Y} (hUC : U ≤ C.1) (i : MovedOrbit P C) :
    movedFam P C U i ≤ i.1.1 := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_movedFam_iff.1 hv
  have h1 := mem_cjComp_of_mem ((movedRep P C i : ↥P) : Y) C (hUC hu)
  have h2 : cjComp ((movedRep P C i : ↥P) : Y) C = i.1 := movedRep_smul P C i
  rw [h2] at h1
  exact h1

theorem movedFam_le_of_le {U : Subgroup Y} (hUP : U ≤ P) (i : MovedOrbit P C) :
    movedFam P C U i ≤ P := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_movedFam_iff.1 hv
  exact P.mul_mem (P.mul_mem (movedRep P C i).2 (hUP hu)) (P.inv_mem (movedRep P C i).2)

theorem isElemAbelian_movedFam {U : Subgroup Y} (hU : IsElemAbelian p U) (i : MovedOrbit P C) :
    IsElemAbelian p (movedFam P C U i) :=
  hU.map _

theorem card_movedFam {U : Subgroup Y} (i : MovedOrbit P C) :
    Nat.card ↥(movedFam P C U i) = Nat.card ↥U :=
  Subgroup.card_map_of_injective (MulAut.conj _).injective

theorem card_centralPart_movedFam (U : Subgroup Y) (i : MovedOrbit P C) :
    Nat.card ↥(centralPart i.1 (movedFam P C U i)) = Nat.card ↥(centralPart C U) := by
  have h := card_centralPart_cjComp ((movedRep P C i : ↥P) : Y) C U
  have e : cjComp ((movedRep P C i : ↥P) : Y) C = i.1 := movedRep_smul P C i
  rw [e] at h
  exact h

theorem conj_mem_movedFam {U : Subgroup Y}
    (hTU : ∀ g ∈ P, g ∈ normalizer (C.1 : Set Y) → ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (h : ↥P) {u : Y} (hu : u ∈ U) :
    (h : Y) * u * (h : Y)⁻¹ ∈ movedFam P C U ⟨h • C, MulAction.mem_orbit C h⟩ := by
  set i : MovedOrbit P C := ⟨h • C, MulAction.mem_orbit C h⟩
  set a : ↥P := movedRep P C i with ha
  have hac : a • C = h • C := movedRep_smul P C i
  have hs : (a⁻¹ * h) • C = C := by rw [mul_smul, ← hac, inv_smul_smul]
  have hsN : ((a⁻¹ * h : ↥P) : Y) ∈ normalizer (C.1 : Set Y) :=
    (moved_smul_eq_self_iff _ C).1 hs
  have hv := hTU _ (a⁻¹ * h).2 hsN u hu
  refine mem_movedFam_iff.2 ⟨_, hv, ?_⟩
  rw [← ha]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem conj_mem_iSup_movedFam {U : Subgroup Y}
    (hTU : ∀ g ∈ P, g ∈ normalizer (C.1 : Set Y) → ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (h : ↥P) {e : Y} (he : e ∈ ⨆ i : MovedOrbit P C, movedFam P C U i) :
    (h : Y) * e * (h : Y)⁻¹ ∈ ⨆ i : MovedOrbit P C, movedFam P C U i := by
  have hle : (⨆ i : MovedOrbit P C, movedFam P C U i) ≤
      (⨆ i : MovedOrbit P C, movedFam P C U i).comap (MulAut.conj (h : Y)).toMonoidHom := by
    refine iSup_le fun i => ?_
    intro e he'
    obtain ⟨u, hu, rfl⟩ := mem_movedFam_iff.1 he'
    have key := conj_mem_movedFam hTU (h * movedRep P C i) hu
    have hmem := Subgroup.mem_iSup_of_mem (S := fun j : MovedOrbit P C => movedFam P C U j)
      ⟨(h * movedRep P C i) • C, MulAction.mem_orbit C (h * movedRep P C i)⟩ key
    rw [Subgroup.mem_comap]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp only [Subgroup.coe_mul] at hmem
    have e1 : (h : Y) * (((movedRep P C i : ↥P) : Y) * u * ((movedRep P C i : ↥P) : Y)⁻¹) *
        (h : Y)⁻¹ = (h : Y) * ((movedRep P C i : ↥P) : Y) * u *
        ((h : Y) * ((movedRep P C i : ↥P) : Y))⁻¹ := by group
    rw [e1]
    exact hmem
  exact hle he

theorem mem_normalizer_iSup_movedFam {U : Subgroup Y}
    (hTU : ∀ g ∈ P, g ∈ normalizer (C.1 : Set Y) → ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    {g : Y} (hg : g ∈ P) :
    g ∈ normalizer ((⨆ i : MovedOrbit P C, movedFam P C U i : Subgroup Y) : Set Y) := by
  rw [mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact conj_mem_iSup_movedFam hTU ⟨g, hg⟩ he
  · intro he
    have := conj_mem_iSup_movedFam hTU ⟨g⁻¹, P.inv_mem hg⟩ he
    have e1 : g⁻¹ * (g * e * g⁻¹) * g⁻¹⁻¹ = e := by group
    simp only [Subgroup.coe_inv] at this
    rw [e1] at this
    exact this

end Family

section Main

variable {P : Subgroup Y}

theorem Cfg.isCyclic_inf_of_moved (h : Cfg p P x z) (h64 : KFactCenterCyclicGeFive)
    {C : ComponentIndex Y} (hC : ¬ Fixed P C) : IsCyclic ↥(P ⊓ C.1) := by
  by_contra hnc
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  obtain ⟨U, hUR, hTU, hUc, hUp, hUab⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le (T := P ⊓ normalizer (C.1 : Set Y))
      (R := P ⊓ C.1) hp hp2 (h.isPGroup.to_le inf_le_left)
      (fun a ha => ⟨ha.1, le_normalizer ha.2⟩)
      (fun g hg => inf_normalizer_le_normalizer_inf ⟨le_normalizer hg.1, hg.2⟩) hnc
  have hUP : U ≤ P := hUR.trans inf_le_left
  have hUC : U ≤ C.1 := hUR.trans inf_le_right
  have hUe : IsElemAbelian p U := ⟨⟨⟨fun a b => Subtype.ext (hUab a a.2 b b.2)⟩⟩, hUp⟩
  have hTU' : ∀ g ∈ P, g ∈ normalizer (C.1 : Set Y) → ∀ u ∈ U, g * u * g⁻¹ ∈ U :=
    fun g hg hgN u hu => (mem_normalizer_iff.mp (hTU ⟨hg, hgN⟩) u).mp hu
  by_cases hcen : centralPart C U = U
  ·
    have hUz : U.subgroupOf C.1 ≤ center ↥C.1 := by
      intro a ha
      have haU : (a : Y) ∈ U := ha
      have hmem : (a : Y) ∈ centralPart C U := by rw [hcen]; exact haU
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact mem_centralizer_iff.mp (mem_centralPart_iff.mp hmem).2.2 c c.2
    obtain ⟨-, hsimple, a, b, hab⟩ := C.2.1
    have hcat : IsCatalogGroup (↥C.1 ⧸ center ↥C.1) :=
      h.catalog C.1 (center ↥C.1) inferInstance hsimple ⟨a, b, hab⟩
    have hUpg : IsPGroup p (U.subgroupOf C.1) := (h.isPGroup.to_le hUP).comap_subtype
    have hcyc := h64 C.1 (comp_isQuasisimple C) hcat p hp h.five_le (U.subgroupOf C.1) hUz hUpg
    exact CFSG.Goldschmidt.Sec82.not_isCyclic_of_card_sq hp hUc hUp
      ((isCyclic_subgroupOf_iff hUC).1 hcyc)
  ·
    letI : Fintype (MovedOrbit P C) := Fintype.ofFinite _
    have hUe' : ∀ i : MovedOrbit P C, IsElemAbelian p (movedFam P C U i) := fun i =>
      isElemAbelian_movedFam hUe i
    have hUle : ∀ i : MovedOrbit P C, movedFam P C U i ≤ (i.1 : ComponentIndex Y).1 :=
      movedFam_le_comp hUC
    obtain ⟨hEe, hcard1, hcard2⟩ := card_iSup_components hp
      (fun i : MovedOrbit P C => (i.1 : ComponentIndex Y)) Subtype.val_injective
      (movedFam P C U) hUle hUe'
    have hEP : (⨆ i : MovedOrbit P C, movedFam P C U i) ≤ P :=
      iSup_le fun i => movedFam_le_of_le hUP i
    have hxE := mem_normalizer_iSup_movedFam hTU' h.x_mem
    have hEcard := h.card_le_of_normalizes hEP hEe hxE
    have hs : p ≤ Fintype.card (MovedOrbit P C) := by
      rw [← Nat.card_eq_fintype_card]
      exact h.le_card_movedOrbit hC
    obtain ⟨s, hsdef⟩ : ∃ s, s = Fintype.card (MovedOrbit P C) := ⟨_, rfl⟩
    rw [← hsdef] at hs
    obtain ⟨t, htdef⟩ : ∃ t, t = Nat.card ↥(centralPart C U) := ⟨_, rfl⟩
    have hprod1 : ∏ i : MovedOrbit P C, Nat.card ↥(movedFam P C U i) = (p ^ 2) ^ s := by
      rw [Finset.prod_congr rfl (fun i _ => (card_movedFam i).trans hUc), Finset.prod_const,
        Finset.card_univ, hsdef]
    have hprod2 : ∏ i : MovedOrbit P C,
        Nat.card ↥(centralPart (i.1 : ComponentIndex Y) (movedFam P C U i)) = t ^ s := by
      rw [Finset.prod_congr rfl (fun i _ => (card_centralPart_movedFam U i).trans htdef.symm),
        Finset.prod_const, Finset.card_univ, hsdef]
    rw [hprod1, hprod2] at hcard1
    have htdvd : t ∣ p ^ 2 := by
      rw [htdef, ← hUc]
      exact Subgroup.card_dvd_of_le (centralPart_le C U)
    have htne : t ≠ p ^ 2 := by
      intro ht
      apply hcen
      refine Subgroup.eq_of_le_of_card_ge (centralPart_le C U) ?_
      rw [hUc, ← htdef, ht]
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).1 htdvd
    have hk2' : k < 2 := by
      rcases Nat.lt_or_ge k 2 with hlt | hge
      · exact hlt
      · exfalso
        have : k = 2 := le_antisymm hk2 hge
        exact htne (hk.trans (by rw [this]))
    have hq : Nat.card ↥(⨆ i : MovedOrbit P C, movedFam P C U i) ≤ p ^ s :=
      hEcard.trans (Nat.pow_le_pow_right hp.pos hs)
    have hqpos : 0 < p ^ s := pow_pos hp.pos s
    have hq2 : 2 ≤ p ^ s := by
      have h1 : p ^ 1 ≤ p ^ s := Nat.pow_le_pow_right hp.pos (hp.pos.trans_le hs)
      have h5 := h.five_le
      rw [pow_one] at h1
      omega
    have hsq : (p ^ 2) ^ s = p ^ s * p ^ s := by ring
    interval_cases k
    ·
      rw [pow_zero] at hk
      rw [hk, one_pow, mul_one, hsq] at hcard1
      have h1 : p ^ s * p ^ s ≤ p ^ s * 1 := by
        rw [mul_one]
        exact hcard1.trans hq
      have h2 := Nat.le_of_mul_le_mul_left h1 hqpos
      omega
    ·
      rw [pow_one] at hk
      have hj : centralPart ((⟨C, MulAction.mem_orbit_self C⟩ : MovedOrbit P C).1 :
          ComponentIndex Y) (movedFam P C U ⟨C, MulAction.mem_orbit_self C⟩) ≠ ⊥ := by
        intro hbot
        have h1 := card_centralPart_movedFam U (⟨C, MulAction.mem_orbit_self C⟩ : MovedOrbit P C)
        rw [hbot, Subgroup.card_bot, ← htdef, hk] at h1
        exact hp.one_lt.ne h1
      have hc2 := hcard2 ⟨⟨C, MulAction.mem_orbit_self C⟩, hj⟩
      rw [hprod1, hprod2, hk, hsq] at hc2
      have h3 : p * (p ^ s * p ^ s) ≤ 1 * (p ^ s * p ^ s) := by
        calc p * (p ^ s * p ^ s) ≤ Nat.card ↥(⨆ i : MovedOrbit P C, movedFam P C U i) * p ^ s :=
              hc2
          _ ≤ p ^ s * p ^ s := Nat.mul_le_mul_right _ hq
          _ = 1 * (p ^ s * p ^ s) := (one_mul _).symm
      have h4 := Nat.le_of_mul_le_mul_right h3 (Nat.mul_pos hqpos hqpos)
      exact absurd h4 (not_le.2 hp.one_lt)

end Main

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

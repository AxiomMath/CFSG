module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1Dat
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1NC1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7a_C1_le_C6 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    C1 c.e ≤ C6 c.e := by
  have hC1N : C1 c.e ≤ normalizer (C1 c.e : Set G) := Subgroup.le_normalizer
  have hnorm : ((C1 c.e).subgroupOf (normalizer (C1 c.e : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hC1N]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.mp hk h).mp hh
  have hcard : Nat.card ↥(C1 c.e) = 128 := y6_card_C1 (c.y7acfg hH).cfg
  have hpg : IsPGroup 2 ((C1 c.e).subgroupOf (normalizer (C1 c.e : Set G))) := by
    refine IsPGroup.of_card (n := 7) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC1N).toEquiv, hcard]
    norm_num
  have hle : (C1 c.e).subgroupOf (normalizer (C1 c.e : Set G)) ≤
      CFSG.pCore 2 ↥(normalizer (C1 c.e : Set G)) := by
    rw [CFSG.pCore]
    exact le_sSup ⟨hnorm, hpg⟩
  calc C1 c.e = ((C1 c.e).subgroupOf (normalizer (C1 c.e : Set G))).map
        (normalizer (C1 c.e : Set G)).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hC1N).symm
    _ ≤ (CFSG.pCore 2 ↥(normalizer (C1 c.e : Set G))).map
        (normalizer (C1 c.e : Set G)).subtype := Subgroup.map_mono hle
    _ = C6 c.e := rfl

theorem y7a_C6_le_X (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    C6 c.e ≤ y7aX c := by
  have hle : C6 c.e ≤ normalizer (C1 c.e : Set G) := by
    show (CFSG.pCore 2 ↥(normalizer (C1 c.e : Set G))).map
      (normalizer (C1 c.e : Set G)).subtype ≤ normalizer (C1 c.e : Set G)
    exact Subgroup.map_subtype_le _
  calc C6 c.e ≤ normalizer (C1 c.e : Set G) := hle
    _ = y7aX c := y7a_NC1_eq c hH hF

theorem y7a_C6_isPGroup (c : Ctx7 G L) : IsPGroup 2 (C6 c.e) := by
  show IsPGroup 2 ((CFSG.pCore 2 ↥(normalizer (C1 c.e : Set G))).map
    (normalizer (C1 c.e : Set G)).subtype)
  exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(normalizer (C1 c.e : Set G))))
    (normalizer (C1 c.e : Set G)).subtype

theorem y7a_C6_normal (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5) :
    ∀ x ∈ y7aX c, ∀ m ∈ C6 c.e, x * m * x⁻¹ ∈ C6 c.e := by
  intro x hx m hm
  change m ∈ (CFSG.pCore 2 ↥(normalizer (C1 c.e : Set G))).map
    (normalizer (C1 c.e : Set G)).subtype at hm
  change x * m * x⁻¹ ∈ (CFSG.pCore 2 ↥(normalizer (C1 c.e : Set G))).map
    (normalizer (C1 c.e : Set G)).subtype
  obtain ⟨b, hb, hbm⟩ := Subgroup.mem_map.mp hm
  have hxH : x ∈ normalizer (C1 c.e : Set G) := (y7a_NC1_eq c hH hF).symm ▸ hx
  have hconj := (CFSG.pCore_normal (p := 2) (G := ↥(normalizer (C1 c.e : Set G)))).conj_mem
    b hb (⟨x, hxH⟩ : ↥(normalizer (C1 c.e : Set G)))
  have hgoal : x * m * x⁻¹ = (normalizer (C1 c.e : Set G)).subtype
      ((⟨x, hxH⟩ : ↥(normalizer (C1 c.e : Set G))) * b *
        (⟨x, hxH⟩ : ↥(normalizer (C1 c.e : Set G)))⁻¹) := by
    rw [map_mul, map_mul, map_inv, hbm]
    simp
  rw [hgoal]
  exact Subgroup.mem_map_of_mem _ hconj

theorem y7a_mem_C6_iff (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    ∀ x : ↥(y7aX c), (x : G) ∈ C6 c.e ↔ ψ x ∈ P := by
  have hC6X : C6 c.e = pCoreOf 2 (y7aX c) := by
    rw [show C6 c.e = pCoreOf 2 (normalizer (C1 c.e : Set G)) from rfl,
      y7a_NC1_eq c hH hF]
  have hkerpg : IsPGroup 2 ψ.ker := by
    have hC1X : C1 c.e ≤ y7aX c :=
      (y6_C1_le_NAt (c.y7acfg hH).cfg).trans (y7a_Y_le_X c hH)
    have hcard : Nat.card ↥(C1 c.e) = 128 := y6_card_C1 (c.y7acfg hH).cfg
    rw [hP.ker]
    refine IsPGroup.of_card (n := 7) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC1X).toEquiv, hcard]
    norm_num
  have hcore : CFSG.pCore 2 ↥(y7aX c) = P.comap ψ := by
    refine le_antisymm ?_ ?_
    · intro b hb
      exact hP.P_max ((CFSG.pCore 2 ↥(y7aX c)).map ψ) (Subgroup.map_le_range ψ _) (by
        intro q hq m hm
        obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
        obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hm
        have hconj : g * b' * g⁻¹ ∈ CFSG.pCore 2 ↥(y7aX c) :=
          CFSG.pCore_normal.conj_mem b' hb' g
        have hmap : ψ (g * b' * g⁻¹) = ψ g * ψ b' * (ψ g)⁻¹ := by
          simp [map_mul]
        rw [← hmap]
        exact Subgroup.mem_map_of_mem ψ hconj)
        (IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(y7aX c))) ψ)
        (Subgroup.mem_map_of_mem ψ hb)
    · have hnorm : (P.comap ψ).Normal := by
        refine ⟨fun n hn g => ?_⟩
        show ψ (g * n * g⁻¹) ∈ P
        have hgn : ψ (g * n * g⁻¹) = ψ g * ψ n * (ψ g)⁻¹ := by
          simp [map_mul]
        rw [hgn]
        exact hP.P_normal (ψ g) ((MonoidHom.mem_range (f := ψ) (y := ψ g)).mpr ⟨g, rfl⟩)
          (ψ n) hn
      have hpc : IsPGroup 2 (P.comap ψ) :=
        hP.P_two.comap_of_ker_isPGroup ψ hkerpg
      rw [CFSG.pCore]
      exact le_sSup ⟨hnorm, hpc⟩
  intro x
  rw [hC6X, pCoreOf, hcore]
  show (y7aX c).subtype x ∈ (P.comap ψ).map (y7aX c).subtype ↔ ψ x ∈ P
  rw [Subgroup.mem_map_iff_mem (y7aX c).subtype_injective]
  rfl

theorem y7a_reg_free {P : Subgroup (Equiv.Perm (Fin 16))} (hcard : Nat.card P = 16)
    (htrans : ∀ i j : Fin 16, ∃ p ∈ P, p i = j) : ∀ p ∈ P, p 0 = 0 → p = 1 := by
  classical
  haveI : Fintype ↥P := Fintype.ofFinite ↥P
  haveI : Fintype (MulAction.orbit ↥P (0 : Fin 16)) := Fintype.ofFinite _
  haveI : Fintype (MulAction.stabilizer ↥P (0 : Fin 16)) := Fintype.ofFinite _
  intro p hp hp0
  have horbit : MulAction.orbit ↥P (0 : Fin 16) = Set.univ := by
    ext i
    refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
    obtain ⟨q, hq, hqi⟩ := htrans 0 i
    exact MulAction.mem_orbit_iff.mpr ⟨⟨q, hq⟩, by simpa using hqi⟩
  have hcardP : Fintype.card ↥P = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hcardOrbit : Fintype.card (MulAction.orbit ↥P (0 : Fin 16)) = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (horbit.symm ▸ Equiv.Set.univ (Fin 16))).trans (by simp)
  have hos := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥P) (0 : Fin 16)
  rw [hcardOrbit, hcardP] at hos
  have hstab : Fintype.card (MulAction.stabilizer ↥P (0 : Fin 16)) = 1 := by omega
  haveI : Subsingleton (MulAction.stabilizer ↥P (0 : Fin 16)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq hstab)
  have hmem : (⟨p, hp⟩ : ↥P) ∈ MulAction.stabilizer ↥P (0 : Fin 16) := by
    rw [MulAction.mem_stabilizer_iff]
    simpa using hp0
  have h1 : (⟨p, hp⟩ : ↥P) = 1 := by
    have hthis := Subsingleton.elim
      (⟨⟨p, hp⟩, hmem⟩ : MulAction.stabilizer ↥P (0 : Fin 16)) 1
    simpa using congrArg Subtype.val hthis
  exact Subtype.ext_iff.mp h1

theorem y7a_C6_inf_Y (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    C6 c.e ⊓ y7aY c = C1 c.e := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxC6, hxY⟩ := Subgroup.mem_inf.mp hx
    have hxX : x ∈ y7aX c := y7a_C6_le_X c hH hF hxC6
    have hxP : ψ ⟨x, hxX⟩ ∈ P :=
      (y7a_mem_C6_iff c hH hF hP ⟨x, hxX⟩).mp hxC6
    have hfix : ψ ⟨x, hxX⟩ 0 = 0 := (hP.stab ⟨x, hxX⟩).mpr hxY
    have h1 : ψ ⟨x, hxX⟩ = 1 := y7a_reg_free hP.P_card hP.P_trans _ hxP hfix
    have hker : ⟨x, hxX⟩ ∈ ψ.ker := MonoidHom.mem_ker.mpr h1
    rw [hP.ker] at hker
    exact hker
  · exact le_inf (y7a_C1_le_C6 c hH hF) (y6_C1_le_NAt (c.y7acfg hH).cfg)

theorem y7a_X_eq_C6Y (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (hF : c.toCtx5.Facts5)
    {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)} {lab : G → Fin 16}
    {P : Subgroup (Equiv.Perm (Fin 16))} (hP : Y7AReg c ψ lab P) :
    ∀ x ∈ y7aX c, ∃ m ∈ C6 c.e, ∃ y ∈ y7aY c, x = m * y := by
  intro x hxX
  let x' : ↥(y7aX c) := ⟨x, hxX⟩
  obtain ⟨p, hpP, hp0⟩ := hP.P_trans 0 (ψ x' 0)
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hP.P_le hpP)
  have hmC6 : (m : G) ∈ C6 c.e := by
    have hpP' : ψ m ∈ P := by
      have h := hpP
      rwa [← hm] at h
    exact (y7a_mem_C6_iff c hH hF hP m).mpr hpP'
  let y : ↥(y7aX c) := m⁻¹ * x'
  have hyfix : ψ y 0 = 0 := by
    have hval : ψ y = (ψ m)⁻¹ * ψ x' := by
      show ψ (m⁻¹ * x') = _
      rw [map_mul, map_inv]
    rw [hval]
    change (ψ m)⁻¹ (ψ x' 0) = 0
    rw [← hp0, ← hm]
    simp
  refine ⟨(m : G), hmC6, (y : G), (hP.stab y).mp hyfix, ?_⟩
  show x = (m : G) * (y : G)
  rw [show (y : G) = (m : G)⁻¹ * x from rfl]
  group

end CFSG.OddStandard.HigherRank.YamadaG23

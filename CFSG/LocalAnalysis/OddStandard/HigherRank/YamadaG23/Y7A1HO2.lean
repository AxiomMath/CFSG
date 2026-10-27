module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1S2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1LabC
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1O2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1P1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private lemma y7a_isSylowIn_map_subtype_three {V : Subgroup G} (P : Sylow 3 ↥V) :
    IsSylowIn 3 V ((P : Subgroup ↥V).map V.subtype) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

private lemma y7a_hO2_wit {c : Ctx7 G L} {ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16)}
    {lab : G → Fin 16} (hψ : Y7APsi c ψ lab) {q : Equiv.Perm (Fin 16)}
    (hq : q ∈ ψ.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16)) :
    ∃ x : ↥(y7aX c), ψ x = q ∧ (x : G) ∈ y7aY c := by
  obtain ⟨hqr, hqs⟩ := Subgroup.mem_inf.mp hq
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hqr
  refine ⟨x, hx, ?_⟩
  have hq0 : q 0 = 0 := by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hqs
    exact hqs
  exact (hψ.stab x).mp (by rw [hx]; exact hq0)

theorem y7a_hO2 (c : Ctx7 G L) (hH : F33Hyp c.s c.e) (ψ : ↥(y7aX c) →* Equiv.Perm (Fin 16))
    (lab : G → Fin 16) (hψ : Y7APsi c ψ lab) :
    ∀ N : Subgroup (Equiv.Perm (Fin 16)),
      N ≤ ψ.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16) →
      (∀ s ∈ ψ.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
        ∀ m ∈ N, s * m * s⁻¹ ∈ N) →
      IsPGroup 2 N → N = ⊥ := by
  intro N hN hnorm h2
  have hcfg := c.y7acfg hH
  have hD0 : (0 : Fin 16) ∉ lab '' y7aS c.s.fr.A (V1 c.e) c.s.t := by
    rintro ⟨w, hwS, hw0⟩
    have htU : c.s.t ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) :=
      ⟨Subgroup.mem_sup_right (y7a_t_mem_C0 hcfg), y7a_t_not_mem_AV hcfg⟩
    have hwU : w ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) := y7a_S_sub hcfg w hwS
    have hlab : lab c.s.t = lab w := by rw [hψ.lab_t, hw0]
    exact hwS.2 ((hψ.lab_iff c.s.t htU w hwU).mp hlab)
  have hcard : Nat.card ↥(lab '' y7aS c.s.fr.A (V1 c.e) c.s.t) = 9 :=
    y7a_card_lab_img (n := 16) (V := V1 c.e) lab
      (U := y7aU16 c.s.fr.A (C0 c.e) (V1 c.e))
      (S := y7aS c.s.fr.A (V1 c.e) c.s.t)
      (y7a_S_sub hcfg) hψ.lab_iff (y7a_S_V hcfg) (y7a_S_card hcfg)
  have hDodd : Odd (Nat.card ↥(lab '' y7aS c.s.fr.A (V1 c.e) c.s.t)) := by
    rw [hcard]; decide
  have hDinv : ∀ q ∈ ψ.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
      ∀ i ∈ lab '' y7aS c.s.fr.A (V1 c.e) c.s.t,
        q i ∈ lab '' y7aS c.s.fr.A (V1 c.e) c.s.t := by
    intro q hq i hi
    obtain ⟨w, hwS, hwi⟩ := hi
    obtain ⟨x, hx, hxY⟩ := y7a_hO2_wit hψ hq
    have hxA : (x : G) ∈ normalizer (c.s.fr.A : Set G) := s5_Y_le_NA c.toCtx5 hH hxY
    have hxC1 : (x : G) ∈ normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp x.2).1
    have hxV : (x : G) ∈ normalizer (V1 c.e : Set G) := (Subgroup.mem_inf.mp x.2).2
    have hxwS : (x : G) * w * (x : G)⁻¹ ∈ y7aS c.s.fr.A (V1 c.e) c.s.t :=
      y7a_S_conj hcfg hxA hxC1 hxV hxY w hwS
    refine ⟨(x : G) * w * (x : G)⁻¹, hxwS, ?_⟩
    have hwU : w ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) := y7a_S_sub hcfg w hwS
    calc lab ((x : G) * w * (x : G)⁻¹) = ψ x (lab w) := (hψ.act x w hwU).symm
      _ = q (lab w) := by rw [hx]
      _ = q i := by rw [hwi]
  have hDtr : ∀ i ∈ lab '' y7aS c.s.fr.A (V1 c.e) c.s.t,
      ∀ j ∈ lab '' y7aS c.s.fr.A (V1 c.e) c.s.t,
        ∃ q ∈ ψ.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16), q i = j := by
    rintro i ⟨w, hwS, rfl⟩ j ⟨w', hwS', rfl⟩
    obtain ⟨P₃, hP₃⟩ : ∃ P₃ : Subgroup G, IsSylowIn 3 (normIn L c.s.fr.A) P₃ :=
      ⟨_, y7a_isSylowIn_map_subtype_three (default : Sylow 3 ↥(normIn L c.s.fr.A))⟩
    have hP₃cent : P₃ ≤ centEl L c.s.fr.z := by
      rw [← hH.hLF.fact18.1.1]; exact hP₃.1
    have hP₃L : P₃ ≤ L := fun k hk => (hP₃cent hk).1
    have hP₃t : ∀ k ∈ P₃, k * c.s.t * k⁻¹ = c.s.t := by
      intro k hk
      have hmem : c.s.t ∈ centralizer (L : Set G) := c.s.t_mem
      rw [Subgroup.mem_centralizer_iff] at hmem
      rw [hmem k (hP₃L hk)]
      group
    have hP₃z : ∀ k ∈ P₃, k * c.s.fr.z * k⁻¹ = c.s.fr.z := by
      intro k hk
      have hkz : Commute k c.s.fr.z := by
        have hmem : k ∈ centralizer ({c.s.fr.z} : Set G) := (hP₃cent hk).2
        rw [Subgroup.mem_centralizer_iff] at hmem
        exact (hmem c.s.fr.z (Set.mem_singleton c.s.fr.z)).symm
      rw [hkz.eq]
      group
    have hP₃V : ∀ k ∈ P₃, ∀ v ∈ V1 c.e, k * v * k⁻¹ ∈ V1 c.e := by
      intro k hk v hv
      have hkX : k ∈ y7aX c := y7a_Y_le_X c hH (s5_NLA_le_Y c.toCtx5 hH (hP₃.1 hk))
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hkX).2 v).mp hv
    have h9 : IsOrbitMod P₃ (zpowers c.s.fr.z)
        ((c.s.fr.A : Set G) \ ((closure {c.s.fr.a₁, c.s.fr.b₁} : Set G) ∪
          (closure {c.s.fr.a₂, c.s.fr.b₂} : Set G))) :=
      (hH.hLF.fact18.1.2.2 P₃ hP₃).2.2
    obtain ⟨k, hkP, hkζ⟩ := y7a_S_trans hcfg hP₃t hP₃V hP₃z h9 w hwS w' hwS'
    have hkY : k ∈ y7aY c := s5_NLA_le_Y c.toCtx5 hH (hP₃.1 hkP)
    have hkX : k ∈ y7aX c := y7a_Y_le_X c hH hkY
    refine ⟨ψ ⟨k, hkX⟩, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨⟨⟨k, hkX⟩, rfl⟩, ?_⟩
      rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact (hψ.stab ⟨k, hkX⟩).mpr hkY
    · have hkwS : k * w * k⁻¹ ∈ y7aS c.s.fr.A (V1 c.e) c.s.t :=
        y7a_S_conj hcfg (s5_Y_le_NA c.toCtx5 hH hkY)
          (Subgroup.mem_inf.mp hkX).1 (Subgroup.mem_inf.mp hkX).2 hkY w hwS
      have hlab : lab (k * w * k⁻¹) = lab w' :=
        (hψ.lab_iff (k * w * k⁻¹) (y7a_S_sub hcfg _ hkwS) w'
          (y7a_S_sub hcfg w' hwS')).mpr hkζ
      calc ψ ⟨k, hkX⟩ (lab w) = lab (k * w * k⁻¹) :=
            hψ.act ⟨k, hkX⟩ w (y7a_S_sub hcfg w hwS)
        _ = lab w' := hlab
  have hfix : ∀ q ∈ ψ.range ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
      (∀ i ∈ lab '' y7aS c.s.fr.A (V1 c.e) c.s.t, q i = i) → q = 1 := by
    intro q hq hfixpt
    obtain ⟨x, hx, hxY⟩ := y7a_hO2_wit hψ hq
    have hxA : (x : G) ∈ normalizer (c.s.fr.A : Set G) := s5_Y_le_NA c.toCtx5 hH hxY
    have hxC1 : (x : G) ∈ normalizer ((c.s.fr.A ⊔ C0 c.e : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.mp x.2).1
    have hxV : (x : G) ∈ normalizer (V1 c.e : Set G) := (Subgroup.mem_inf.mp x.2).2
    have hfixS : ∀ w ∈ y7aS c.s.fr.A (V1 c.e) c.s.t,
        w⁻¹ * ((x : G) * w * (x : G)⁻¹) ∈ V1 c.e := by
      intro w hwS
      have hwU : w ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) := y7a_S_sub hcfg w hwS
      have hxwS : (x : G) * w * (x : G)⁻¹ ∈ y7aS c.s.fr.A (V1 c.e) c.s.t :=
        y7a_S_conj hcfg hxA hxC1 hxV hxY w hwS
      have hxwU : (x : G) * w * (x : G)⁻¹ ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) :=
        y7a_S_sub hcfg _ hxwS
      have hlabx : lab ((x : G) * w * (x : G)⁻¹) = lab w := by
        have h1 : q (lab w) = lab ((x : G) * w * (x : G)⁻¹) := by
          rw [← hx]; exact hψ.act x w hwU
        rw [← h1]
        exact hfixpt (lab w) ⟨w, hwS, rfl⟩
      exact (hψ.lab_iff w hwU ((x : G) * w * (x : G)⁻¹) hxwU).mp hlabx.symm
    have hfaith := y7a_S_faith hcfg hxA hxC1 hxV hxY hfixS
    have hpsi_one : ψ x = 1 := by
      refine Equiv.ext fun i => ?_
      obtain ⟨u, huU, hui⟩ := hψ.lab_surj i
      have hxuC1 : (x : G) * u * (x : G)⁻¹ ∈ c.s.fr.A ⊔ C0 c.e :=
        (Subgroup.mem_normalizer_iff.mp hxC1 u).mp huU.1
      have hxuAV : ((x : G) * u * (x : G)⁻¹ ∈ c.s.fr.A ⊔ V1 c.e) ↔
          (u ∈ c.s.fr.A ⊔ V1 c.e) := (y7a_conj_AV hcfg hxC1 hxV u).symm
      have hxuU : (x : G) * u * (x : G)⁻¹ ∈ y7aU16 c.s.fr.A (C0 c.e) (V1 c.e) :=
        ⟨hxuC1, fun h => huU.2 (hxuAV.mp h)⟩
      have hmemV : ((x : G) * u * (x : G)⁻¹)⁻¹ * u ∈ V1 c.e := by
        have hinv := (V1 c.e).inv_mem (hfaith u huU)
        simpa only [mul_inv_rev, inv_inv] using hinv
      have hlabu : lab ((x : G) * u * (x : G)⁻¹) = lab u :=
        (hψ.lab_iff ((x : G) * u * (x : G)⁻¹) hxuU u huU).mpr hmemV
      calc ψ x i = ψ x (lab u) := by rw [← hui]
        _ = lab ((x : G) * u * (x : G)⁻¹) := hψ.act x u huU
        _ = lab u := hlabu
        _ = i := hui
    rw [← hx]
    exact hpsi_one
  exact y7a_O2_trivial ψ.range (lab '' y7aS c.s.fr.A (V1 c.e) c.s.t)
    hD0 hDodd hDinv hDtr hfix N hN hnorm h2

end CFSG.OddStandard.HigherRank.YamadaG23

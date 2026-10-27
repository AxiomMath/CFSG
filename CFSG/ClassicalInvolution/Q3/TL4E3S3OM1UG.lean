module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UF
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UD
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1UE

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

open CFSG.Monster.B.Co2 CFSG.LieType.Multipliers.U43 CFSG.Assembly.LowTwoRank
open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.ComponentClassification.HarrisLit.P1.U43
open CFSG.ClassicalInvolution.Generic CFSG.LinearGroups.UnitaryThreeOverNine
open CFSG.ClassicalInvolution.Q3.TL4.E4C

theorem v0_mem_K0 : v0P ∈ K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem u1_mem_K1 : u1P ∈ K1 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem K0_mem_fixSet : K0 ∈ FixSet K0 d2P :=
  ⟨⟨1, P.one_mem, conjSub_one K0⟩, commute_d2_K0⟩

theorem mem_cent_d2 {c : Equiv.Perm (Fin 820)} (hc : c ∈ P) (hd : d2P * c = c * d2P) :
    c ∈ P ⊓ Subgroup.centralizer ({d2P} : Set (Equiv.Perm (Fin 820))) :=
  Subgroup.mem_inf.2 ⟨hc, Subgroup.mem_centralizer_singleton_iff.2 hd.symm⟩

theorem K0_le_cent :
    K0 ≤ P ⊓ Subgroup.centralizer ({d2P} : Set (Equiv.Perm (Fin 820))) :=
  fun c hc => mem_cent_d2 (K0_le_P hc) (commute_d2_K0 c hc)

theorem conjSub_le_P {g : Equiv.Perm (Fin 820)} (hg : g ∈ P) {K : Subgroup (Equiv.Perm (Fin 820))}
    (hK : K ≤ P) : conjSub g K ≤ P := by
  rintro _ ⟨k, hk, rfl⟩
  exact P.mul_mem (P.mul_mem hg (hK hk)) (P.inv_mem hg)

theorem yb_d2_le :
    Yb K0 d2P ≤ P ⊓ Subgroup.centralizer ({d2P} : Set (Equiv.Perm (Fin 820))) := by
  refine iSup₂_le fun C hC c hc => ?_
  obtain ⟨⟨g, hg, rfl⟩, hcomm⟩ := hC
  exact mem_cent_d2 (conjSub_le_P hg K0_le_P hc) (hcomm c hc)

theorem conjSub_beta_yb (m : StatedSU 3 3 F9) :
    conjSub (beta m) (Yb K0 d2P) = Yb K0 d2P := by
  rw [← yb_conj (beta_mem m)]
  have h1 : beta m * d2P * (beta m)⁻¹ = d2P := by rw [beta_comm, mul_inv_cancel_right]
  rw [h1]
  unfold Yb
  rw [fixSet_conj_left (beta_mem m)]


theorem yb_d2_eq : Yb K0 d2P = beta.range := by
  refine le_antisymm (range_beta ▸ yb_d2_le) ?_
  have := isSimpleGroup_statedSU
  have : ((Yb K0 d2P).comap beta).Normal := ⟨fun n hn m => by
    show beta (m * n * m⁻¹) ∈ Yb K0 d2P
    rw [map_mul, map_mul, map_inv, ← conjSub_beta_yb m]
    exact conj_mem_conjSub hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Yb K0 d2P).comap beta) with h | h
  · exfalso
    have hu : u0P ∈ beta.range := range_beta ▸ K0_le_cent u0_mem_K0
    obtain ⟨n, hn⟩ := hu
    have hnY : n ∈ (Yb K0 d2P).comap beta := by
      show beta n ∈ Yb K0 d2P
      rw [hn]
      exact le_iSup₂ (f := fun C (_ : C ∈ FixSet K0 d2P) => C) K0 K0_mem_fixSet u0_mem_K0
    rw [h, Subgroup.mem_bot] at hnY
    rw [hnY, map_one] at hn
    have h1 := rel_facts.2.2.1
    rw [← hn, mul_one] at h1
    exact rel_facts.1 h1.symm
  · rintro _ ⟨m, rfl⟩
    have hm : m ∈ (Yb K0 d2P).comap beta := by
      rw [h]
      exact Subgroup.mem_top m
    exact hm

theorem yb_d2_equiv : Nonempty (↥(Yb K0 d2P) ≃* StatedSU 3 3 F9) :=
  ⟨(MulEquiv.subgroupCongr yb_d2_eq).trans (MonoidHom.ofInjective beta_injective).symm⟩

theorem orderOf_r0 : orderOf r0P = 2 :=
  orderOf_eq_prime (by rw [sq]; exact rel_facts.2.1) rel_facts.1

theorem three_d2 (hd0 : Vtx.AmbientQuatDatum P K0 r0P) :
    ∀ C ∈ FixSet K0 d2P, ∃ y ∈ Yb K0 d2P, conjSub y C = C ∧ y ^ 3 = 1 ∧ ∃ c ∈ C, y * c ≠ c * y := by
  rintro C ⟨⟨g, hg, rfl⟩, hcomm⟩
  have hr' : g * r0P * g⁻¹ ∈ beta.range := by
    rw [range_beta]
    exact mem_cent_d2 (P.mul_mem (P.mul_mem hg mem_P.1) (P.inv_mem hg))
      (hcomm _ (conj_mem_conjSub r0_mem_K0))
  obtain ⟨a, ha⟩ : r0P ∈ beta.range := range_beta ▸ K0_le_cent r0_mem_K0
  obtain ⟨b, hb⟩ := hr'
  have ha2 : orderOf a = 2 := by rw [← orderOf_injective beta beta_injective a, ha, orderOf_r0]
  have hb2 : orderOf b = 2 := by
    rw [← orderOf_injective beta beta_injective b, hb, ← orderOf_r0]
    exact MulEquiv.orderOf_eq (MulAut.conj g) r0P
  obtain ⟨m, hm⟩ := isConj_iff.1 (isConj_of_orderOf_eq_two natCard_F9 ha2 hb2)
  have hhr : beta m * r0P * (beta m)⁻¹ = g * r0P * g⁻¹ := by
    rw [← hb, ← hm, map_mul, map_mul, map_inv, ha]
  have hq : (beta m)⁻¹ * g ∈ P := P.mul_mem (P.inv_mem (beta_mem m)) hg
  have hqr : (beta m)⁻¹ * g * r0P = r0P * ((beta m)⁻¹ * g) := by
    have : g * r0P = beta m * r0P * (beta m)⁻¹ * g := by rw [hhr, inv_mul_cancel_right]
    calc (beta m)⁻¹ * g * r0P = (beta m)⁻¹ * (g * r0P) := by group
      _ = (beta m)⁻¹ * (beta m * r0P * (beta m)⁻¹ * g) := by rw [this]
      _ = r0P * ((beta m)⁻¹ * g) := by group
  have hC' : conjSub ((beta m)⁻¹ * g) K0 = K0 := by
    by_contra hne
    have hK1 := twin_eq_K1 hd0 hq hqr hne
    apply rel_facts.2.2.2.2.2.2.2.2.1
    have hv : v1P ∈ conjSub ((beta m)⁻¹ * g) K0 := hK1 ▸ v1_mem_K1
    rw [conjSub_mul, mem_conjSub_iff, inv_inv] at hv
    have h1 := hcomm _ hv
    have h2 := beta_comm m
    have h4 : (beta m)⁻¹ * d2P = d2P * (beta m)⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h2, mul_inv_cancel_right]
    have e1 : d2P * (beta m * v1P * (beta m)⁻¹) = beta m * (d2P * v1P) * (beta m)⁻¹ := by
      rw [← mul_assoc, ← mul_assoc, ← h2]
      group
    have e2 : beta m * v1P * (beta m)⁻¹ * d2P = beta m * (v1P * d2P) * (beta m)⁻¹ := by
      calc beta m * v1P * (beta m)⁻¹ * d2P = beta m * v1P * ((beta m)⁻¹ * d2P) := by group
        _ = beta m * v1P * (d2P * (beta m)⁻¹) := by rw [h4]
        _ = beta m * (v1P * d2P) * (beta m)⁻¹ := by group
    have h3 : beta m * (d2P * v1P) * (beta m)⁻¹ = beta m * (v1P * d2P) * (beta m)⁻¹ := by
      rw [← e1, ← e2]
      exact h1
    simpa using h3
  have hCh : conjSub g K0 = conjSub (beta m) K0 := by
    calc conjSub g K0 = conjSub (beta m) (conjSub ((beta m)⁻¹ * g) K0) := by
          rw [← conjSub_mul, mul_inv_cancel_left]
      _ = conjSub (beta m) K0 := by rw [hC']
  have hy0 : y0P ∈ beta.range := range_beta ▸ mem_cent_d2 mem_P.2.2.2.2.2.2.2.1
    rel_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm
  rw [hCh]
  refine ⟨beta m * y0P * (beta m)⁻¹, ?_, ?_, ?_, beta m * u0P * (beta m)⁻¹,
    conj_mem_conjSub u0_mem_K0, ?_⟩
  · rw [yb_d2_eq]
    exact beta.range.mul_mem (beta.range.mul_mem ⟨m, rfl⟩ hy0) (beta.range.inv_mem ⟨m, rfl⟩)
  · rw [conjSub_conj, conjSub_y0]
  · rw [conj_pow, pow_three, rel_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, mul_one, mul_inv_cancel]
  · intro he
    apply rel_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have h1 : beta m * (y0P * u0P) * (beta m)⁻¹ = beta m * (u0P * y0P) * (beta m)⁻¹ := by
      calc beta m * (y0P * u0P) * (beta m)⁻¹ =
            beta m * y0P * (beta m)⁻¹ * (beta m * u0P * (beta m)⁻¹) := by group
        _ = beta m * u0P * (beta m)⁻¹ * (beta m * y0P * (beta m)⁻¹) := he
        _ = beta m * (u0P * y0P) * (beta m)⁻¹ := by group
    simpa using h1

theorem model_d2 (hd0 : Vtx.AmbientQuatDatum P K0 r0P) : Concl K0 d2P :=
  ⟨yb_d2_equiv, three_d2 hd0⟩

theorem model_K0 (hd0 : Vtx.AmbientQuatDatum P K0 r0P)
    {ρ q w : Equiv.Perm (Fin 820)} (hρ : ρ ∈ R) (hq : q ∈ P) (hqr : q * r0P = r0P * q)
    (hne : conjSub q K0 ≠ K0) (hρ2 : ρ * ρ = 1) (hfix : ∀ a ∈ K0, ρ * a = a * ρ)
    (hw : w ∈ conjSub q K0) (hw4 : orderOf w = 4)
    (hwB : ∀ b ∈ conjSub q K0, ρ * b * ρ⁻¹ = w * b * w⁻¹) : Concl K0 ρ := by
  rw [twin_eq_K1 hd0 hq hqr hne] at hw hwB
  have hwU : w ∈ L1P.drop 2 := by
    have hwL := (mem_K1_iff w).1 hw
    have hL : L1P = 1 :: r0P :: L1P.drop 2 := rfl
    rw [hL, List.mem_cons, List.mem_cons] at hwL
    rcases hwL with rfl | rfl | h
    · rw [orderOf_one] at hw4
      omega
    · rw [orderOf_r0] at hw4
      omega
    · exact h
  have hact : ∀ b ∈ K1, ρ * b = w * b * w⁻¹ * ρ := fun b hb => by
    rw [← hwB b hb, inv_mul_cancel_right]
  obtain ⟨g, hg, k, hk, rfl⟩ := mem_R_iff.1 hρ
  obtain ⟨c, hc, hcρ⟩ := cfg_classify hg hk ⟨hfix _ u0_mem_K0, hfix _ v0_mem_K0, hρ2, w, hwU,
    hact _ u1_mem_K1, hact _ v1_mem_K1⟩
  rw [hcρ, ← conjSub_gam hc]
  exact concl_conj (mem_P.2.2.2.2.2.2.2.2 c hc) (model_d2 hd0)

end CFSG.ClassicalInvolution.Q3.TL4.E3S3O.U4M

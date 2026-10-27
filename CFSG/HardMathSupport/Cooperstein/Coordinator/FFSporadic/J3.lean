module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.Sporadic.SmallOddCore.J3Aut
public import CFSG.Sporadic.Bridge.J3Surj
public import Certificates.Certificate129006
public import Certificates.Certificate129007
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Certificates.Native

theorem j3P_center_eq_bot :
    Subgroup.center ↥j3P = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hc : (z : Equiv.Perm (Fin 6156)) ∈
      Subgroup.centralizer (j3P : Set (Equiv.Perm (Fin 6156))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨h, hh⟩)
  rw [j3_centralizer_eq_bot, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext hc)

theorem j3P_mulAut_card :
    Nat.card (MulAut ↥j3P) ≤ 2 * Nat.card ↥j3P := by
  rw [card_j3P]
  exact j3_card_mulAut_le.trans (by norm_num)

theorem j3S_card_le {B : Subgroup (Equiv.Perm (Fin 6156))}
    (hBS : B ≤ CFSG.Sporadic.SmallOddCore.j3S) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 31 :=
  Certificates.certificate129007 B hBS hcomm hsq

theorem j3_exists_conj_le_S
    {B : Subgroup (Equiv.Perm (Fin 6156))} (hBR : B ≤ j3R)
    (hsq : ∀ x ∈ B, x * x = 1) :
    ∃ g ∈ j3R, ∀ x ∈ B, g⁻¹ * x * g ∈ CFSG.Sporadic.SmallOddCore.j3S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨S', hS'⟩, -⟩ := ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  have hB2 : IsPGroup 2 (B.subgroupOf j3R) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa [sq] using hsq _ (Subgroup.mem_subgroupOf.1 x.2)
  obtain ⟨T, hTle⟩ := hB2.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq j3R S' T
  refine ⟨x, x.2, fun b hb => ?_⟩
  have hbT : (⟨b, hBR hb⟩ : j3R) ∈ (T : Subgroup j3R) :=
    hTle (Subgroup.mem_subgroupOf.2 hb)
  rw [← hx, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hbT
  obtain ⟨s, hs, hst⟩ := hbT
  have hsS : (s : Equiv.Perm (Fin 6156)) ∈ CFSG.Sporadic.SmallOddCore.j3S := by
    rw [hS'] at hs
    exact Subgroup.mem_subgroupOf.mp hs
  have e : x⁻¹ * ⟨b, hBR hb⟩ * x = s := by
    rw [← hst, MulAut.smul_def, MulAut.conj_apply]
    group
  have e' := congrArg Subtype.val e
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e'
  rw [e']
  exact hsS

theorem j3R_elemAbelian_le
    {B : Subgroup (Equiv.Perm (Fin 6156))} (hBR : B ≤ j3R)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 4 := by
  obtain ⟨g, -, hgS⟩ := j3_exists_conj_le_S hBR hsq
  have hc : Nat.card (B.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hBS : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ CFSG.Sporadic.SmallOddCore.j3S := by
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hgS b hb
  have hcomm' : ∀ x ∈ B.map (MulAut.conj g⁻¹).toMonoidHom,
      ∀ y ∈ B.map (MulAut.conj g⁻¹).toMonoidHom, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [hcomm a ha b hb]
      _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group
  have hsq' : ∀ x ∈ B.map (MulAut.conj g⁻¹).toMonoidHom, x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g := by group
      _ = 1 := by rw [hsq a ha]; group
  have h31 := j3S_card_le hBS hcomm' hsq'
  rw [hc] at h31
  have hp : IsPGroup 2 B := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simpa [sq] using hsq x x.2
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at h31 ⊢
  exact Nat.pow_le_pow_right (by norm_num) (by
    by_contra hk4
    push Not at hk4
    have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    omega)

theorem j3P_rank_le :
    ∀ B : Subgroup ↥j3P, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ 4 := by
  intro B hcomm hsq
  have hPR : j3P ≤ j3R := le_sup_left
  have h := j3R_elemAbelian_le (B := B.map j3P.subtype)
    (by rintro _ ⟨b, -, rfl⟩; exact hPR b.2)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [Subgroup.coe_subtype]
      exact congrArg Subtype.val (hcomm a ha b hb))
    (by
      rintro _ ⟨a, ha, rfl⟩
      simp only [Subgroup.coe_subtype]
      exact congrArg Subtype.val (hsq a ha))
  rwa [Subgroup.card_map_of_injective j3P.subtype_injective] at h

theorem j3P_gen3
    (B : Subgroup ↥j3P)
    (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List ↥j3P, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set ↥j3P)), orderOf x = 19 := by
  obtain ⟨⟨t, htB⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact hsq t htB) ht1'
  obtain ⟨g, hg⟩ := j3_involution_conj_a ht2
  obtain ⟨-, hb, hab, -⟩ := AT_J3_image_pair_count
  have hb3 : j3b ^ 3 = 1 := by
    have : orderOf j3b = 3 := by rw [← Subgroup.orderOf_coe]; exact hb
    rw [← this]
    exact pow_orderOf_eq_one _
  have hab' : orderOf (j3a * j3b) = 19 := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
    exact hab
  have hbinv : j3b⁻¹ * j3b⁻¹ = j3b := by
    rw [← mul_inv_rev, inv_eq_iff_eq_inv, eq_inv_iff_mul_eq_one, ← pow_three', hb3]
  refine ⟨[1, g * j3b * g⁻¹, g * j3b⁻¹ * g⁻¹], rfl,
    t * (g * j3b * g⁻¹ * t * (g * j3b * g⁻¹)⁻¹) * (g * j3b⁻¹ * g⁻¹ * t * (g * j3b⁻¹ * g⁻¹)⁻¹),
    ?_, ?_⟩
  · refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure ?_)
      (Subgroup.subset_closure ⟨_, by simp, t, htB, rfl⟩))
      (Subgroup.subset_closure ⟨_, by simp, t, htB, rfl⟩)
    exact ⟨1, by simp, t, htB, by group⟩
  · have key : j3a * j3b * j3a * (j3b⁻¹ * j3b⁻¹) * j3a * j3b = (j3a * j3b) ^ 3 := by
      rw [hbinv, pow_three']
      simp only [mul_assoc]
    have hx : t * (g * j3b * g⁻¹ * t * (g * j3b * g⁻¹)⁻¹) *
        (g * j3b⁻¹ * g⁻¹ * t * (g * j3b⁻¹ * g⁻¹)⁻¹) = MulAut.conj g ((j3a * j3b) ^ 3) := by
      rw [MulAut.conj_apply, ← key, hg]
      group
    have hcop : (orderOf (j3a * j3b)).Coprime 3 := by rw [hab']; norm_num
    rw [hx, MulEquiv.orderOf_eq, hcop.orderOf_pow, hab']

theorem j3OuterWit_facts :
    orderOf (tp 6156 (j3CentTbl 21) * (j3Gen 1 * tp 6156 (j3CentTbl 21) * (j3Gen 1)⁻¹)) =
      19 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have h := Certificates.certificate129006
  unfold j3OuterWitCheck at h
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨hperm, h19⟩, hne⟩ := h
  have hn : (6156 : ℕ) < 2 ^ 32 := by norm_num
  have rt : Rep 6156 (j3CentTbl 21) (tp 6156 (j3CentTbl 21)) := rep_tp hperm
  have rb : Rep 6156 j3PGTbls[1]! (j3Gen 1) :=
    j3_groupData.rep 1 (by rw [show j3PGTbls.size = 2 from rfl]; norm_num)
  have ry : Rep 6156 (j3OuterWitTbl ())
      (tp 6156 (j3CentTbl 21) * (j3Gen 1 * (tp 6156 (j3CentTbl 21) * (j3Gen 1 * j3Gen 1)))) :=
    rt.compT (rb.compT (rt.compT (rb.compT rb)))
  have hb3 : j3Gen 1 ^ 3 = 1 := by
    rw [← AT_J3_image_pair_count.2.1]
    exact pow_orderOf_eq_one _
  have hbb : j3Gen 1 * j3Gen 1 = (j3Gen 1)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_three', hb3]
  have heq : tp 6156 (j3CentTbl 21) * (j3Gen 1 * tp 6156 (j3CentTbl 21) * (j3Gen 1)⁻¹) =
      tp 6156 (j3CentTbl 21) * (j3Gen 1 * (tp 6156 (j3CentTbl 21) * (j3Gen 1 * j3Gen 1))) := by
    rw [hbb]
    group
  rw [heq]
  refine orderOf_eq_prime ((tblEq_idT_iff hn (ry.powT hn 19)).1 h19) fun h1 => ?_
  rw [(tblEq_idT_iff hn ry).2 h1] at hne
  exact Bool.noConfusion hne

theorem j3P_outer_dihedral :
    ∀ ψ : MulAut ↥j3P, ψ ∉ (MulAut.conj : ↥j3P →* MulAut ↥j3P).range → ψ * ψ = 1 →
      ∃ α : MulAut ↥j3P, orderOf (ψ * (α * ψ * α⁻¹)) = 19 := by
  intro ψ hψ hψ2
  obtain ⟨eR, -, himage, -, -⟩ := ctuc_j3_full_automorphism_permutation_model
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j3_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨x, rfl⟩ := eR.surjective ψ
  have hxP : (x : Equiv.Perm (Fin 6156)) ∉ j3P := by
    intro hx
    apply hψ
    have hmem : eR x ∈ (j3P.subgroupOf j3R).map eR.toMonoidHom :=
      ⟨x, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [himage] at hmem
    exact hmem
  have hx2 : x * x = 1 := eR.injective (by rw [map_mul, hψ2, map_one])
  have hx1 : (x : Equiv.Perm (Fin 6156)) ≠ 1 := fun h => hxP (h ▸ j3P.one_mem)
  have hxord : orderOf (x : Equiv.Perm (Fin 6156)) = 2 :=
    orderOf_eq_prime (by rw [sq, ← Subgroup.coe_mul, hx2, Subgroup.coe_one]) hx1
  obtain ⟨r, hr, g, hg, hxg⟩ := hcover x x.2 hxord
  have hrP : tp 6156 r.rep ∉ j3P := by
    intro h
    apply hxP
    rw [hxg]
    exact j3P.mul_mem (j3P.mul_mem hg h) (j3P.inv_mem hg)
  have hout : r.outer = true := ((hrows r hr).2.2.1).2 hrP
  have hrep : r.rep = j3CentTbl 21 := by
    simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact absurd hout (by decide)
    · simp only
  rw [hrep] at hxg
  have hPR : j3P ≤ j3R := le_sup_left
  have hβP : g * j3Gen 1 * g⁻¹ ∈ j3P :=
    j3P.mul_mem (j3P.mul_mem hg (j3Gen_mem_P 1 (by norm_num))) (j3P.inv_mem hg)
  set β : ↥j3R := ⟨g * j3Gen 1 * g⁻¹, hPR hβP⟩ with hβ
  refine ⟨eR β, ?_⟩
  have hprod : eR x * (eR β * eR x * (eR β)⁻¹) = eR (x * (β * x * β⁻¹)) := by
    rw [map_mul, map_mul, map_mul, map_inv]
  rw [hprod, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hβ]
  rw [hxg]
  have hconj : g * tp 6156 (j3CentTbl 21) * g⁻¹ *
      (g * j3Gen 1 * g⁻¹ * (g * tp 6156 (j3CentTbl 21) * g⁻¹) * (g * j3Gen 1 * g⁻¹)⁻¹) =
      MulAut.conj g (tp 6156 (j3CentTbl 21) *
        (j3Gen 1 * tp 6156 (j3CentTbl 21) * (j3Gen 1)⁻¹)) := by
    rw [MulAut.conj_apply]
    group
  rw [hconj, MulEquiv.orderOf_eq]
  exact j3OuterWit_facts

noncomputable def j3CarrierEquiv :
    NativeSporadic.Carrier .J3 ≃* ↥j3P :=
  j3PermEquiv

theorem j3_weight_lt
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* ↥j3P)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hidx := index_fixV_eq_two_pow hW E
  apply weight_lt_of_lt_index
  rcases out2_dichotomy hW hq.1 hirr hE hEel e j3P_center_eq_bot j3P_mulAut_card (r := 4)
    (p := 19) (by norm_num) j3P_rank_le j3P_outer_dihedral with hEL | ⟨hdisp, hcard⟩
  · have hcard : Nat.card E ≤ 2 ^ 4 := card_le_two_pow_of_le hW hirr hEL hEel e j3P_rank_le
    have hBsq := imgSub_sq (hEL := hEL) (e := e) hEel
    have hBcard := card_imgSub hW hirr hEL hEel e
    have hne : imgSub L E hEL e ≠ ⊥ := by
      intro h
      have h1 : Nat.card (imgSub L E hEL e) = 1 := by rw [h]; simp
      rw [hBcard] at h1
      exact hEne (Subgroup.card_eq_one.1 h1)
    obtain ⟨cs, hcs, hx⟩ := j3P_gen3 _ hBsq hne
    have h := two_pow_le_of_inner_gen hW hEL e (k := 3) (p := 19) (by norm_num) ⟨cs, hcs, hx⟩
    rw [orderOf_two_zmod_19] at h
    have h2 := two_pow_le_of_pow_le hidx h (ρ := 6) (by norm_num)
    omega
  · rw [orderOf_two_zmod_19] at hdisp
    have h2 := two_pow_le_of_pow_le hidx hdisp (ρ := 9) (by norm_num)
    omega

theorem sporadicExclusion_J3 :
    QuasithinUnique.Setup.X1.SporadicExclusion .J3 := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hE hEne hEel _
  exact j3_weight_lt hW hq hirr (e.trans j3CarrierEquiv) hE hEne hEel

theorem noIrrFFOffender_J3 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .J3).Group :=
  Proving.noIrrFFOffender_of_exclusion sporadicExclusion_J3
    CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv

theorem gf2NoFFSporadicFor_J3 :
    GF2NoFFSporadicFor .J3 :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_J3

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

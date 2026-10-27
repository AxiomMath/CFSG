module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEInd2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

private noncomputable def psiHom {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) : ↥L →* ProjSim Q :=
  (ffInducesHom hm e).comp (Subgroup.inclusion Subgroup.le_normalizer)

private lemma psiHom_apply {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (l : ↥L) :
    psiHom hm e l = ffInducesHom hm e ⟨l, Subgroup.le_normalizer l.2⟩ := by
  apply congrArg (ffInducesHom hm e)
  exact Subtype.ext rfl

private lemma psiHom_eq_one_iff {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (hperf : commutator ↥L = ⊤) (l : ↥L) :
    psiHom hm e l = 1 ↔ l ∈ Subgroup.center ↥L := by
  rw [psiHom_apply, ffInducesHom_eq_one_iff hm e hperf]
  constructor
  · intro hc
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) (x : G) x.2)
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨x, hx⟩)

private lemma exists_psiHom_eq {L : Subgroup G} {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) {f : ProjSim Q}
    (hf : SimInOmegaStar hQ f) : ∃ l : ↥L, psiHom hm e l = f := by
  obtain ⟨y, hy, hyf⟩ := hf
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (e.symm ⟨y, hy⟩)
  refine ⟨q, ?_⟩
  have heq : e (QuotientGroup.mk q) = ⟨y, hy⟩ := by
    rw [hq]; exact e.apply_symm_apply ⟨y, hy⟩
  rw [psiHom_apply, ffInducesHom_of_mem hm e q (Subgroup.le_normalizer q.2), heq]
  simpa using hyf

theorem sec9u_lift_E16 [Finite G] {L : Subgroup G} (hL : IsOm6M L) {hQ : Q.Nondegenerate}
    (hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ) (F : Subgroup (ProjSim Q))
    (hF16 : Nat.card F = 2 ^ 4) (hFc : ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ * f₂ = f₂ * f₁)
    (hFsq : ∀ f ∈ F, f * f = 1) (hFΩ : ∀ f ∈ F, SimInOmegaStar hQ f) :
    ∃ (B : Subgroup G) (hBL : B ≤ L), IsElemAb2 B 4 ∧
      ∀ (b : G) (hb : b ∈ B), ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ ∈ F := by
  classical
  have hperf : commutator ↥L = ⊤ := Group.isPerfect_def.mp hL.1.1
  let Z : Subgroup ↥L := Subgroup.center ↥L
  have hoddZ : Odd (Nat.card Z) := by
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    have hodd' : 2 ∣ Nat.card Z := hodd.two_dvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 2 hodd'
    have hcZ : (c : ↥L) ∈ Z := c.2
    have hord : orderOf (((c : ↥Z) : ↥L) : G) = 2 := by
      have h1 : orderOf (((c : ↥Z) : ↥L) : G) = orderOf ((c : ↥Z) : ↥L) :=
        orderOf_injective L.subtype L.subtype_injective _
      have h2 : orderOf ((c : ↥Z) : ↥L) = orderOf (c : ↥Z) :=
        orderOf_injective Z.subtype Z.subtype_injective _
      rw [h1, h2]
      exact hc
    have hc2 : (((c : ↥Z) : ↥L) : G) * (((c : ↥Z) : ↥L) : G) = 1 := by
      rw [← pow_two, ← hord, pow_orderOf_eq_one]
    have hcCenterIn : (((c : ↥Z) : ↥L) : G) ∈ centerIn L := by
      rw [sec4_mem_centerIn_iff]
      refine ⟨((c : ↥Z) : ↥L).2, fun k hk => ?_⟩
      exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨k, hk⟩)).symm
    have hc1 : (((c : ↥Z) : ↥L) : G) = 1 := sec9g_centerIn_sq_eq_one hL hcCenterIn hc2
    have hc1' : (c : ↥Z) = 1 := Subtype.ext (Subtype.ext hc1)
    rw [hc1', orderOf_one] at hc
    omega
  let ψ : ↥L →* ProjSim Q := psiHom hm e
  let K : Subgroup ↥L := F.comap ψ
  have hZK : Z ≤ K := by
    intro z hz
    show ψ z ∈ F
    rw [show ψ z = 1 from (psiHom_eq_one_iff hm e hperf z).mpr hz]
    exact F.one_mem
  let ψK : ↥K →* F :=
    (ψ.comp K.subtype).codRestrict F (fun k => k.2)
  have hψK_apply : ∀ k : ↥K, (ψK k : ProjSim Q) = ψ (k : ↥L) := fun k => rfl
  have hψK_surj : Function.Surjective ψK := by
    intro f
    obtain ⟨l, hl⟩ := exists_psiHom_eq hm e (hFΩ f f.2)
    refine ⟨⟨l, by show ψ l ∈ F; rw [show ψ l = psiHom hm e l from rfl, hl]; exact f.2⟩, ?_⟩
    apply Subtype.ext
    simpa only [hψK_apply] using hl
  have hψK_ker : ψK.ker = Z.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      exact (psiHom_eq_one_iff hm e hperf (k : ↥L)).mp (by
        have := Subtype.ext_iff.mp hk
        rwa [hψK_apply k] at this)
    · intro hk
      apply Subtype.ext
      rw [hψK_apply k]
      exact (psiHom_eq_one_iff hm e hperf (k : ↥L)).mpr hk
  have hKcard : Nat.card ↥K = Nat.card Z * Nat.card F := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := ψK) hψK_surj
    rw [hψK_ker] at h
    have h2 : Nat.card (Z.subgroupOf K) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
    rw [h2] at h
    exact h.symm
  let N : Subgroup ↥K := Z.subgroupOf K
  have hNcard : Nat.card N = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv
  have hZpos : 0 < Nat.card Z :=
    Nat.card_pos_iff.mpr ⟨(OneMemClass.coe_nonempty Z).to_subtype, inferInstance⟩
  have hNindex : N.index = Nat.card F := by
    have h := Subgroup.card_mul_index N
    rw [hNcard, hKcard] at h
    exact Nat.mul_left_cancel hZpos h
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    rw [hNcard, hNindex, hF16]
    have h2 : Nat.Coprime (Nat.card Z) 2 := Nat.coprime_two_right.mpr hoddZ
    simpa using Nat.Coprime.pow_right 4 h2
  obtain ⟨H, hHcomp⟩ := Subgroup.exists_right_complement'_of_coprime (N := N) hcop
  have hHcard : Nat.card H = 2 ^ 4 := by
    have h := hHcomp.card_mul_card
    rw [hNcard, hKcard] at h
    rw [Nat.mul_left_cancel hZpos h, hF16]
  have hHN_bot : H ⊓ N = ⊥ := by
    rw [inf_comm]
    exact hHcomp.disjoint.eq_bot
  have hmemN : ∀ x : ↥K, x ∈ N ↔ ψK x = 1 := by
    intro x
    show x ∈ Z.subgroupOf K ↔ ψK x = 1
    rw [← hψK_ker, MonoidHom.mem_ker]
  have hHcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x := by
    intro x hx y hy
    have h1 : ψK (x * y) = ψK (y * x) := by
      rw [map_mul, map_mul]
      apply Subtype.ext
      simpa using hFc (ψK x) (ψK x).2 (ψK y) (ψK y).2
    have hmem : (x * y) * (y * x)⁻¹ ∈ N := by
      rw [hmemN, map_mul, map_inv, h1, mul_inv_cancel]
    have hmemH : (x * y) * (y * x)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hx hy) (H.inv_mem (H.mul_mem hy hx))
    have hbot : (x * y) * (y * x)⁻¹ = 1 := by
      have hle : (x * y) * (y * x)⁻¹ ∈ (H ⊓ N : Subgroup ↥K) := ⟨hmemH, hmem⟩
      rw [hHN_bot] at hle
      simpa using hle
    exact mul_inv_eq_one.mp hbot
  have hHsq : ∀ x ∈ H, x * x = 1 := by
    intro x hx
    have h1 : ψK (x * x) = 1 := by
      rw [map_mul]
      apply Subtype.ext
      simpa using hFsq (ψK x) (ψK x).2
    have hmem : x * x ∈ N := by rw [hmemN]; exact h1
    have hmemH : x * x ∈ H := H.mul_mem hx hx
    have hle : x * x ∈ (H ⊓ N : Subgroup ↥K) := ⟨hmemH, hmem⟩
    rw [hHN_bot] at hle
    simpa using hle
  let φB : ↥K →* G := L.subtype.comp K.subtype
  have hφBinj : Function.Injective φB := L.subtype_injective.comp K.subtype_injective
  let B : Subgroup G := H.map φB
  have hBL : B ≤ L := by
    intro b hb
    obtain ⟨h, _, rfl⟩ := Subgroup.mem_map.mp hb
    exact (K.subtype h).2
  have hBcard : Nat.card B = 2 ^ 4 := by
    change Nat.card (H.map φB) = 2 ^ 4
    rw [Subgroup.card_map_of_injective hφBinj, hHcard]
  have hBcomm : ∀ x y : ↥B, x * y = y * x := by
    intro x y
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    obtain ⟨hx, hhx, hxv⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨hy, hhy, hyv⟩ := Subgroup.mem_map.mp y.2
    rw [← hxv, ← hyv, ← map_mul, ← map_mul, hHcomm hx hhx hy hhy]
  have hBsq : ∀ x : G, x ∈ B → x ^ 2 = 1 := by
    intro x hx
    obtain ⟨h, hh, hv⟩ := Subgroup.mem_map.mp hx
    rw [← hv, pow_two, ← map_mul, hHsq h hh, map_one]
  have hBelem : CFSG.Open.IsElemAbelian 2 B :=
    ⟨isMulCommutative_iff.mpr hBcomm, hBsq⟩
  refine ⟨B, hBL, ⟨hBelem, hBcard⟩, ?_⟩
  intro b hb
  obtain ⟨h, hh, hbh⟩ := Subgroup.mem_map.mp hb
  have hval : ffInducesHom hm e ⟨b, Subgroup.le_normalizer (hBL hb)⟩ = psiHom hm e (h : ↥L) := by
    rw [psiHom_apply hm e (h : ↥L)]
    apply congrArg (ffInducesHom hm e)
    exact Subtype.ext hbh.symm
  rw [hval]
  exact (ψK h).2

end CFSG.OddStandard.SmallF3.Omega

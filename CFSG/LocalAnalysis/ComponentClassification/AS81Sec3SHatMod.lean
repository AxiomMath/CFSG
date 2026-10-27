module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatOmega
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatTabs
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatClosed
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3SHatK
import all CFSG.Fischer.F4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.Fischer CFSG.RankThree.OrthogonalInvolutions Sec3Theta Census Sec3Mod
open scoped Pointwise commutatorElement

namespace Sec3Mod

theorem neg_V (v : Census.V₀) : -v = v := by
  have key : ∀ c : F4, -c = c := by decide
  funext i
  exact key (v i)

theorem card_V : Nat.card Census.V₀ = 4096 := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card, F4.card, Nat.card_fin]
  norm_num

end Sec3Mod

namespace Sec38Hyp

namespace ThetaHyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  {H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀}
  {e : G} {b : Fin 6 → H.xsub.Qt} {t : Fin 6 → G} (hT : H.ThetaHyp e b t)
include hT

theorem Zs_le_SHat : Zs ≤ sec3SHat (Q₀ ⊔ Q) Zs :=
  (H.Zs_le_U hT.hZQ).trans (H.U_le_SHat hT.hQF)

theorem card_theta (X : Census.V₀ → Prop) :
    Nat.card {s : ↥(sec3SHat (Q₀ ⊔ Q) Zs) // X (theta z e t s)} = 4 * Nat.card {v // X v} := by
  have hθ : ∀ (v : Census.V₀) {c : G}, c ∈ Zs → theta z e t (hT.pre v * c) = v := fun v c hc => by
    rw [hT.theta_mul (hT.pre_mem v) (hT.Zs_le_SHat hc), hT.theta_pre,
      (hT.theta_eq_zero_iff (hT.Zs_le_SHat hc)).mpr hc, add_zero]
  have e1 : Nat.card {s : ↥(sec3SHat (Q₀ ⊔ Q) Zs) // X (theta z e t s)} =
      Nat.card ({v // X v} × ↥Zs) := Nat.card_congr
    { toFun := fun s => (⟨theta z e t s.1, s.2⟩, ⟨(hT.pre (theta z e t s.1))⁻¹ * s.1,
        (hT.theta_eq_iff s.1.2 (hT.pre_mem _)).mp (hT.theta_pre _).symm⟩)
      invFun := fun p => ⟨⟨hT.pre p.1.1 * p.2.1, mul_mem (hT.pre_mem _) (hT.Zs_le_SHat p.2.2)⟩,
        by
          change X (theta z e t (hT.pre p.1.1 * p.2.1))
          rw [hθ p.1.1 p.2.2]
          exact p.1.2⟩
      left_inv := fun s => Subtype.ext (Subtype.ext (mul_inv_cancel_left _ _))
      right_inv := fun p => by
        have h1 := hθ p.1.1 p.2.2
        refine Prod.ext (Subtype.ext h1) (Subtype.ext ?_)
        change (hT.pre (theta z e t (hT.pre p.1.1 * p.2.1)))⁻¹ * (hT.pre p.1.1 * p.2.1) = p.2.1
        rw [h1, inv_mul_cancel_left] }
  rw [e1, Nat.card_prod, H.q0.dData.suz.Zs_card, mul_comm]

theorem theta_comm (n : ↥(nSHat Q₀ Q Zs)) {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    theta z e t (s * (n : G) * s⁻¹ * (n : G)⁻¹) =
      theta z e t s + ((hT.hN n : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) (theta z e t s) := by
  rw [show s * (n : G) * s⁻¹ * (n : G)⁻¹ = s * ((n : G) * s⁻¹ * (n : G)⁻¹) by group,
    hT.theta_mul hs (conj_mem n.2.2 (inv_mem hs)), ← hT.hN_theta n (inv_mem hs),
    hT.theta_inv hs, map_neg, neg_V]

omit [Finite G] hT in
theorem comm_mem_SHat_of {s : G} (n : ↥(nSHat Q₀ Q Zs)) (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    s * (n : G) * s⁻¹ * (n : G)⁻¹ ∈ sec3SHat (Q₀ ⊔ Q) Zs := by
  rw [show s * (n : G) * s⁻¹ * (n : G)⁻¹ = s * ((n : G) * s⁻¹ * (n : G)⁻¹) by group]
  exact mul_mem hs (conj_mem n.2.2 (inv_mem hs))

theorem comm_mem_iff (n : ↥(nSHat Q₀ Q Zs)) {s : G} (hs : s ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    s * (n : G) * s⁻¹ * (n : G)⁻¹ ∈ Zs ↔
      ((hT.hN n : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) (theta z e t s) = theta z e t s := by
  rw [← hT.theta_eq_zero_iff (comm_mem_SHat_of n hs), hT.theta_comm n hs,
    add_eq_zero_iff_eq_neg, neg_V, eq_comm]

theorem mem_SHat_of_hN_eq_one (hN₁ : nSHat Q₀ Q Zs ≤ H.xsub.N) (k : ↥(nSHat Q₀ Q Zs))
    (h : hT.hN k = 1) (hk2 : (k : G) * k ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    (k : G) ∈ sec3SHat (Q₀ ⊔ Q) Zs := by
  obtain ⟨s, hs, w, hw, hk⟩ := H.exists_mul_of_comm_SHat hT.hΩ hT.hQF hT.hRc hT.hZQ (hN₁ k.2)
    k.2.1 fun s hs => hT.comm_mem_of_hN_eq_one k h hs
  have hwN : w ∈ normalizer (sec3SHat (Q₀ ⊔ Q) Zs : Set G) := by
    rw [show w = s⁻¹ * k by rw [hk]; group]
    exact mul_mem (le_normalizer (inv_mem hs)) k.2.2
  have hw2 : w * w ∈ sec3SHat (Q₀ ⊔ Q) Zs := by
    rw [show w * w = (w * s * w⁻¹)⁻¹ * (s⁻¹ * ((k : G) * k)) by rw [hk]; group]
    exact mul_mem (inv_mem (conj_mem hwN hs)) (mul_mem (inv_mem hs) hk2)
  have hS2 : IsPGroup 2 (sec3SHat (Q₀ ⊔ Q) Zs) :=
    IsPGroup.of_card (H.card_SHat hT.hΩ hT.hQF hT.hRc hT.hZQ hT.he hT.hez)
  have hw1 : w * w = 1 := by
    have h1 : w * w ∈ AS76b.oddCoreIn (centralizer ((Q₀ ⊔ Q : Subgroup G) : Set G)) ⊓
        sec3SHat (Q₀ ⊔ Q) Zs := ⟨mul_mem hw hw, hw2⟩
    rw [AS76b.oddCoreIn_inf_eq_bot hS2] at h1
    exact Subgroup.mem_bot.mp h1
  have hodd : Odd (orderOf w) :=
    (AS76b.odd_card_oddCoreIn _).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hw)
  have hw' : w = 1 := by
    have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw1)
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h3 | h3
    · exact orderOf_eq_one_iff.mp h3
    · rw [h3] at hodd
      exact absurd hodd (by decide)
  rw [hk, hw', mul_one]
  exact hs

section Census

variable
  (hN₁ : nSHat Q₀ Q Zs ≤ H.xsub.N)
  (hρΩ : H.ρG.range ≤ omegaGroup H.xsub.q H.xsub.q_nondegenerate)
include hN₁ hρΩ

theorem card_fix_hN (n : ↥(nSHat Q₀ Q Zs)) (hnS : (n : G) ∉ sec3SHat (Q₀ ⊔ Q) Zs)
    (hn2 : (n : G) * n ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    Nat.card {v : Census.V₀ // ((hT.hN n : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) v = v} = 256 := by
  have h2 : hT.hN n * hT.hN n = 1 := by
    rw [← map_mul]
    exact hT.hN_eq_one_of_mem_SHat hn2
  have h1 : hT.hN n ≠ 1 := fun h => hnS (hT.mem_SHat_of_hN_eq_one hN₁ n h hn2)
  exact card_fixV_of_invol (s := ⟨hT.hN n, hT.hN_mem_stab n (hN₁ n.2)⟩)
    (hT.hN_mem_Lc hN₁ hρΩ n) (Subtype.ext h2) fun h => h1 (congrArg Subtype.val h)

theorem card_comm_mem (n : ↥(nSHat Q₀ Q Zs)) (hnS : (n : G) ∉ sec3SHat (Q₀ ⊔ Q) Zs)
    (hn2 : (n : G) * n ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    Nat.card {s : ↥(sec3SHat (Q₀ ⊔ Q) Zs) // (s : G) * n * (s : G)⁻¹ * (n : G)⁻¹ ∈ Zs} =
      2 ^ 10 := by
  calc Nat.card {s : ↥(sec3SHat (Q₀ ⊔ Q) Zs) // (s : G) * n * (s : G)⁻¹ * (n : G)⁻¹ ∈ Zs}
      = Nat.card {s : ↥(sec3SHat (Q₀ ⊔ Q) Zs) //
          ((hT.hN n : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) (theta z e t s) = theta z e t s} :=
        Nat.card_congr (Equiv.subtypeEquivRight fun s => hT.comm_mem_iff n s.2)
    _ = 4 * Nat.card {v : Census.V₀ // ((hT.hN n : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) v = v} :=
        hT.card_theta fun v => ((hT.hN n : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) v = v
    _ = 2 ^ 10 := by rw [hT.card_fix_hN hN₁ hρΩ n hnS hn2]; norm_num

theorem card_commutator (n : ↥(nSHat Q₀ Q Zs)) (hnS : (n : G) ∉ sec3SHat (Q₀ ⊔ Q) Zs)
    (hn2 : (n : G) * n ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    2 ^ 6 ≤ Nat.card ↥(⁅sec3SHat (Q₀ ⊔ Q) Zs, zpowers (n : G)⁆ ⊔ Zs) := by
  set w := ((hT.hN n : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) with hw
  let f : Census.V₀ →+ Census.V₀ :=
    { toFun := fun v => v + w v
      map_zero' := by rw [map_zero, add_zero]
      map_add' := fun v v' => by rw [map_add]; abel }
  have hker : Nat.card f.ker = 256 := by
    rw [← hT.card_fix_hN hN₁ hρΩ n hnS hn2]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [AddMonoidHom.mem_ker]
    change v + w v = 0 ↔ w v = v
    rw [add_eq_zero_iff_eq_neg, neg_V, eq_comm]
  have hrange : Nat.card f.range = 16 := by
    have h := AddSubgroup.card_ker_mul_card_range f
    rw [hker, card_V] at h
    omega
  have hsub : ∀ u : ↥(sec3SHat (Q₀ ⊔ Q) Zs), theta z e t u ∈ f.range →
      (u : G) ∈ ⁅sec3SHat (Q₀ ⊔ Q) Zs, zpowers (n : G)⁆ ⊔ Zs := by
    intro u hu
    obtain ⟨v, hv⟩ := AddMonoidHom.mem_range.mp hu
    obtain ⟨s, hs, hsv⟩ := hT.theta_surjective v
    have hc : s * (n : G) * s⁻¹ * (n : G)⁻¹ ∈ ⁅sec3SHat (Q₀ ⊔ Q) Zs, zpowers (n : G)⁆ := by
      have h := Subgroup.commutator_mem_commutator hs (mem_zpowers (n : G))
      rwa [commutatorElement_def] at h
    have hθ : theta z e t u = theta z e t (s * (n : G) * s⁻¹ * (n : G)⁻¹) := by
      rw [hT.theta_comm n hs, hsv, ← hv]
      rfl
    have hz := (hT.theta_eq_iff u.2 (comm_mem_SHat_of n hs)).mp hθ
    rw [show (u : G) = (s * (n : G) * s⁻¹ * (n : G)⁻¹) *
      ((s * (n : G) * s⁻¹ * (n : G)⁻¹)⁻¹ * u) by group]
    exact mul_mem (mem_sup_left hc) (mem_sup_right hz)
  calc 2 ^ 6 = 4 * Nat.card f.range := by rw [hrange]; norm_num
    _ = Nat.card {u : ↥(sec3SHat (Q₀ ⊔ Q) Zs) // theta z e t u ∈ f.range} :=
        (hT.card_theta fun v => v ∈ f.range).symm
    _ ≤ _ := Nat.card_le_card_of_injective (fun u => ⟨u.1, hsub u.1 u.2⟩) fun u u' h => by
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h)

theorem range_facts {K : Subgroup G} (hK : K ≤ nSHat Q₀ Q Zs)
    (hK2 : ∀ a ∈ K, ∀ b ∈ K, a * a ∈ sec3SHat (Q₀ ⊔ Q) Zs ∧
      a * b * a⁻¹ * b⁻¹ ∈ sec3SHat (Q₀ ⊔ Q) Zs) :
    (hT.hN.comp (Subgroup.inclusion hK)).range ≤ Lc ∧
      (∀ y ∈ (hT.hN.comp (Subgroup.inclusion hK)).range, y * y = 1) ∧
      (∀ y ∈ (hT.hN.comp (Subgroup.inclusion hK)).range,
        ∀ y' ∈ (hT.hN.comp (Subgroup.inclusion hK)).range, y * y' = y' * y) ∧
      (K ⊓ sec3SHat (Q₀ ⊔ Q) Zs).relIndex K =
        Nat.card (hT.hN.comp (Subgroup.inclusion hK)).range := by
  set φ := hT.hN.comp (Subgroup.inclusion hK) with hφ
  have hker : φ.ker = (K ⊓ sec3SHat (Q₀ ⊔ Q) Zs).subgroupOf K := by
    ext d
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    constructor
    · intro h
      exact ⟨d.2, hT.mem_SHat_of_hN_eq_one hN₁ (Subgroup.inclusion hK d) h (hK2 d d.2 d d.2).1⟩
    · intro h
      exact hT.hN_eq_one_of_mem_SHat h.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact hT.hN_mem_Lc hN₁ hρΩ _
  · rintro _ ⟨d, rfl⟩
    rw [← map_mul]
    exact hT.hN_eq_one_of_mem_SHat (hK2 d d.2 d d.2).1
  · rintro _ ⟨a, rfl⟩ _ ⟨d, rfl⟩
    have h : φ (a * d * a⁻¹ * d⁻¹) = 1 := hT.hN_eq_one_of_mem_SHat (hK2 a a.2 d d.2).2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
    calc φ a * φ d = (φ a * φ d * (φ a)⁻¹ * (φ d)⁻¹) * (φ d * φ a) := by group
      _ = φ d * φ a := by rw [h, one_mul]
  · rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]

theorem card_comm_mem_le {K : Subgroup G} (hK : K ≤ nSHat Q₀ Q Zs)
    (hK2 : ∀ a ∈ K, ∀ b ∈ K, a * a ∈ sec3SHat (Q₀ ⊔ Q) Zs ∧
      a * b * a⁻¹ * b⁻¹ ∈ sec3SHat (Q₀ ⊔ Q) Zs)
    (hrel : (K ⊓ sec3SHat (Q₀ ⊔ Q) Zs).relIndex K = 16) :
    Nat.card {s : ↥(sec3SHat (Q₀ ⊔ Q) Zs) // ∀ d ∈ K, (s : G) * d * (s : G)⁻¹ * d⁻¹ ∈ Zs} ≤
      16 := by
  obtain ⟨hEL, hsq, hcomm, hidx⟩ := hT.range_facts hN₁ hρΩ hK hK2
  set Er := (hT.hN.comp (Subgroup.inclusion hK)).range with hEr
  have h2 := card_fix_le_two hEL hsq hcomm (hidx.symm.trans hrel)
  set X : Set (MulAction.stabilizer OV N0) := {x | (x : OV) ∈ Er} with hX
  have e1 := card_fix_V₀ X
  have e2 := card_fix_N0 X
  have hiff : ∀ s : ↥(sec3SHat (Q₀ ⊔ Q) Zs),
      (∀ d ∈ K, (s : G) * d * (s : G)⁻¹ * d⁻¹ ∈ Zs) ↔
        ∀ x ∈ X, ((x : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) (theta z e t s) = theta z e t s := by
    intro s
    constructor
    · rintro h x ⟨d, hd⟩
      rw [← hd]
      exact (hT.comm_mem_iff (Subgroup.inclusion hK d) s.2).mp (h d d.2)
    · intro h d hd
      exact (hT.comm_mem_iff ⟨d, hK hd⟩ s.2).mpr
        (h ⟨hT.hN ⟨d, hK hd⟩, hT.hN_mem_stab _ (hN₁ (hK hd))⟩ ⟨⟨d, hd⟩, rfl⟩)
  have h3 : Nat.card {i : Fin 64 // ∀ x ∈ X, sigma x i = i} ≤ 2 := h2
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff),
    hT.card_theta fun v => ∀ x ∈ X, ((x : OV) : Census.V₀ ≃ₗ[F4] Census.V₀) v = v, e1, ← e2]
  calc 4 * Nat.card {i : Fin 64 // ∀ x ∈ X, sigma x i = i} ^ 2 ≤ 4 * 2 ^ 2 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left h3 2)
    _ = 16 := by norm_num

theorem closedHyp : Sec3Closed.ClosedHyp (sec3SHat (Q₀ ⊔ Q) Zs) Zs where
  ZS := hT.Zs_le_SHat
  SC := SHat_le_C
  cardZ := H.q0.dData.suz.Zs_card
  cardS := H.card_SHat hT.hΩ hT.hQF hT.hRc hT.hZQ hT.he hT.hez
  commZ := fun _ hx _ hy => hT.comm_mem_SHat hx hy
  sqZ := fun _ hx => hT.mul_self_mem hx
  modA := fun n hn hnS hn2 => ⟨hT.card_commutator hN₁ hρΩ ⟨n, hn⟩ hnS hn2,
    hT.card_comm_mem hN₁ hρΩ ⟨n, hn⟩ hnS hn2⟩
  modB := fun K hK hK2 => by
    obtain ⟨hEL, hsq, hcomm, hidx⟩ := hT.range_facts hN₁ hρΩ hK hK2
    rw [hidx]
    exact card_le_sixteen hEL hsq hcomm
  modC := fun K hK hK2 hrel => hT.card_comm_mem_le hN₁ hρΩ hK hK2 hrel

end Census

end ThetaHyp

end Sec38Hyp

end CFSG.ComponentClassification.AS81

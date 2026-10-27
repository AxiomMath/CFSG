module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup

open scoped commutatorElement

variable {H : Type*} [Group H]

@[expose] def hatSub (x : H) [(zpowers x).Normal] (K : Subgroup (H ⧸ zpowers x)) : Subgroup H :=
  ⁅K.comap (QuotientGroup.mk' (zpowers x)), K.comap (QuotientGroup.mk' (zpowers x))⁆

variable {x : H} [(zpowers x).Normal] {K : Subgroup (H ⧸ zpowers x)}

theorem hatSub_le_comap : hatSub x K ≤ K.comap (QuotientGroup.mk' (zpowers x)) :=
  Subgroup.commutator_le_of_le le_rfl le_rfl

theorem hatSub_normal [K.Normal] : (hatSub x K).Normal := by
  unfold hatSub
  exact inferInstance

theorem map_hatSub (hK : ⁅K, K⁆ = K) :
    (hatSub x K).map (QuotientGroup.mk' (zpowers x)) = K := by
  rw [hatSub,
    Subgroup.map_commutator (K.comap (QuotientGroup.mk' (zpowers x)))
      (K.comap (QuotientGroup.mk' (zpowers x))) (QuotientGroup.mk' (zpowers x)),
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (zpowers x)) K, hK]

theorem comap_eq_hatSub_sup (hK : ⁅K, K⁆ = K) :
    K.comap (QuotientGroup.mk' (zpowers x)) = hatSub x K ⊔ zpowers x := by
  have h := Subgroup.comap_map_eq (QuotientGroup.mk' (zpowers x)) (hatSub x K)
  rw [map_hatSub hK, QuotientGroup.ker_mk'] at h
  exact h

theorem le_hatSub_of_perfect {P : Subgroup H} (hP : ⁅P, P⁆ = P)
    (hPK : P ≤ K.comap (QuotientGroup.mk' (zpowers x))) : P ≤ hatSub x K := by
  rw [← hP]
  exact Subgroup.commutator_mono hPK hPK

private theorem tw_commutator_mul_central {c d : H} (hc : c ∈ center H) (hd : d ∈ center H)
    (a b : H) : ⁅a * c, b * d⁆ = ⁅a, b⁆ := by
  have hca : a * c = c * a := Subgroup.mem_center_iff.mp hc a
  have hdb : b * d = d * b := Subgroup.mem_center_iff.mp hd b
  rw [hca, hdb]
  have hc' : ∀ g : H, g * c = c * g := Subgroup.mem_center_iff.mp hc
  have hd' : ∀ g : H, g * d = d * g := Subgroup.mem_center_iff.mp hd
  have e1 : ⁅c * a, d * b⁆ = c * (a * (d * b) * a⁻¹) * c⁻¹ * (d * b)⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e1, ← hc' (a * (d * b) * a⁻¹), mul_inv_cancel_right]
  have e2 : a * (d * b) * a⁻¹ * (d * b)⁻¹ = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by
    rw [← mul_assoc a d b, hd' a]; group
  rw [e2, ← hd' (a * b * a⁻¹ * b⁻¹), mul_inv_cancel_right, commutatorElement_def]

theorem hatSub_perfect (hxc : ∀ h : H, h * x = x * h) (hK : ⁅K, K⁆ = K) :
    ⁅hatSub x K, hatSub x K⁆ = hatSub x K := by
  have hcent : zpowers x ≤ center H :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hxc)
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) ?_
  rw [hatSub, Subgroup.commutator_def]
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨a, ha, b, hb, rfl⟩
  rw [comap_eq_hatSub_sup hK] at ha hb
  obtain ⟨a', ha', c, hc, hac⟩ := Subgroup.mem_sup_of_normal_right.mp ha
  obtain ⟨b', hb', d, hd, hbd⟩ := Subgroup.mem_sup_of_normal_right.mp hb
  rw [← hac, ← hbd, tw_commutator_mul_central (hcent hc) (hcent hd) a' b']
  exact Subgroup.commutator_mem_commutator ha' hb'

private theorem tw_map_comm_of_comm (hK : ⁅K, K⁆ = K) {h : H}
    (hcomm : ∀ n ∈ hatSub x K, h * n = n * h) :
    ∀ m ∈ K, QuotientGroup.mk' (zpowers x) h * m = m * QuotientGroup.mk' (zpowers x) h := by
  intro m hm
  have hm' : m ∈ (hatSub x K).map (QuotientGroup.mk' (zpowers x)) := by
    rw [map_hatSub hK]; exact hm
  obtain ⟨n, hn, hpn⟩ := Subgroup.mem_map.mp hm'
  rw [← hpn, ← map_mul, ← map_mul, hcomm n hn]

private theorem tw_comm_of_comm_mod (hxc : ∀ h : H, h * x = x * h) (hK : ⁅K, K⁆ = K) {h : H}
    (hcommK : ∀ m ∈ K,
      QuotientGroup.mk' (zpowers x) h * m = m * QuotientGroup.mk' (zpowers x) h) :
    ∀ n ∈ hatSub x K, h * n = n * h := by
  have hcent : zpowers x ≤ center H :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hxc)
  have hmem : ∀ n : K.comap (QuotientGroup.mk' (zpowers x)),
      ⁅h, (n : H)⁆ ∈ zpowers x := by
    intro n
    have hπ : QuotientGroup.mk' (zpowers x) ⁅h, (n : H)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcommK _ n.property
    simpa [QuotientGroup.ker_mk'] using MonoidHom.mem_ker.mpr hπ
  let φ : K.comap (QuotientGroup.mk' (zpowers x)) →* H :=
    { toFun := fun n => ⁅h, (n : H)⁆
      map_one' := by simp
      map_mul' := fun a b => by
        show ⁅h, (a : H) * (b : H)⁆ = ⁅h, (a : H)⁆ * ⁅h, (b : H)⁆
        rw [commutatorElement_mul_right_eq_mul_conj,
          show ⁅h, (a : H)⁆ * (a : H) * ⁅h, (b : H)⁆ * (a : H)⁻¹
            = ⁅h, (a : H)⁆ * ((a : H) * ⁅h, (b : H)⁆ * (a : H)⁻¹) by group,
          Subgroup.mem_center_iff.mp (hcent (hmem b)) (a : H), mul_inv_cancel_right] }
  have hkey : ∀ a b : K.comap (QuotientGroup.mk' (zpowers x)),
      ⁅h, ⁅(a : H), (b : H)⁆⁆ = 1 := by
    intro a b
    have h2 := map_commutatorElement φ a b
    change ⁅h, (K.comap (QuotientGroup.mk' (zpowers x))).subtype ⁅a, b⁆⁆
      = ⁅φ a, φ b⁆ at h2
    rw [map_commutatorElement (K.comap (QuotientGroup.mk' (zpowers x))).subtype a b] at h2
    change ⁅h, ⁅(K.comap (QuotientGroup.mk' (zpowers x))).subtype a,
      (K.comap (QuotientGroup.mk' (zpowers x))).subtype b⁆⁆ = 1
    rw [h2, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hcent (hmem a)) (φ b)).symm
  have hsub : hatSub x K ≤ Subgroup.centralizer ({h} : Set H) := by
    rw [hatSub, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact commutatorElement_eq_one_iff_mul_comm.mp (hkey ⟨a, ha⟩ ⟨b, hb⟩)
  intro n hn
  exact Subgroup.mem_centralizer_iff.mp (hsub hn) h (Set.mem_singleton h)

theorem mem_center_hatSub_iff (hxc : ∀ h : H, h * x = x * h) (hK : ⁅K, K⁆ = K) {k : H}
    (hk : k ∈ hatSub x K) :
    (∀ n ∈ hatSub x K, k * n = n * k) ↔
      ∀ m ∈ K, QuotientGroup.mk' (zpowers x) k * m = m * QuotientGroup.mk' (zpowers x) k :=
  ⟨tw_map_comm_of_comm hK, tw_comm_of_comm_mod hxc hK⟩

theorem nonempty_quotient_center_equiv (hxc : ∀ h : H, h * x = x * h) (hK : ⁅K, K⁆ = K) :
    Nonempty (↥(hatSub x K) ⧸ center ↥(hatSub x K) ≃* ↥K ⧸ center ↥K) := by
  let π := QuotientGroup.mk' (zpowers x)
  let toK : ↥(hatSub x K) →* ↥K :=
    { toFun := fun n => ⟨π (n : H), hatSub_le_comap n.property⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : H) (b : H)) }
  let f : ↥(hatSub x K) →* (↥K ⧸ center ↥K) := (QuotientGroup.mk' (center ↥K)).comp toK
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨b, hb_eq⟩ := QuotientGroup.mk'_surjective (center ↥K) y
    rw [← hb_eq]
    have hb : (b : H ⧸ zpowers x) ∈ (hatSub x K).map π := by
      rw [map_hatSub hK]; exact b.property
    obtain ⟨n, hn, hpn⟩ := Subgroup.mem_map.mp hb
    refine ⟨⟨n, hn⟩, ?_⟩
    have hbn : toK ⟨n, hn⟩ = b := Subtype.ext hpn
    change QuotientGroup.mk' (center ↥K) (toK ⟨n, hn⟩) = QuotientGroup.mk' (center ↥K) b
    rw [hbn]
  have hker : MonoidHom.ker f = center ↥(hatSub x K) := by
    apply le_antisymm
    · intro n hn
      rw [MonoidHom.mem_ker] at hn
      have hn1 : toK n ∈ center ↥K := by
        have h1 : ((toK n : ↥K) : (↥K) ⧸ center ↥K) = 1 := hn
        exact (QuotientGroup.eq_one_iff (toK n)).mp h1
      rw [Subgroup.mem_center_iff]
      intro m
      have hcomm : ∀ m' ∈ hatSub x K, (n : H) * m' = m' * (n : H) :=
        (mem_center_hatSub_iff hxc hK n.property).mpr
          (fun m hm => (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hn1 ⟨m, hm⟩)).symm)
      exact Subtype.ext (hcomm (m : H) m.property).symm
    · intro n hn
      rw [MonoidHom.mem_ker]
      change ((toK n : ↥K) : (↥K) ⧸ center ↥K) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro m
      have hncomm : ∀ m' ∈ hatSub x K, (n : H) * m' = m' * (n : H) := by
        intro m' hm'
        exact (Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hn ⟨m', hm'⟩)).symm
      have hcommK := (mem_center_hatSub_iff hxc hK n.property).mp hncomm
      exact Subtype.ext (hcommK (m : H ⧸ zpowers x) m.property).symm
  have e := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).symm.trans e⟩

end CFSG.OddStandard.AltStdSec.SwapPartner

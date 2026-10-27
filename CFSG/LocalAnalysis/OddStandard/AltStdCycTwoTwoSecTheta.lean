module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoSwap
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoTwoSecLift
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRootOut
public import CFSG.LocalAnalysis.OddStandard.AltStdWeakTwoSec

public section

namespace CFSG.OddStandard.AltStdCycTwo.Two

open Subgroup Equiv Equiv.Perm AltStdBal AltStdSec

abbrev TwoSecO {G : Type} [Group G] (x : G) : Type := TwoSec x ⧸ CFSG.oddCore (TwoSec x)

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z u : G}

section Basic

theorem swap_elt_ne (B : Base G L Q n z) (θ : L ≃* alternatingGroup (Fin n)) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf B θ hx).IsSwap) : x ≠ z ∧ x ≠ 1 := by
  have hτ1 : permOf B θ hx ≠ 1 := by
    obtain ⟨p, q, hpq, he⟩ := hτ
    intro h1
    rw [h1] at he
    have := congrArg (fun f : Perm (Fin n) => f p) he
    simp only [Perm.one_apply, swap_apply_left] at this
    exact hpq this
  refine ⟨fun hxz => hτ1 ?_, fun hx1 => hτ1 ?_⟩
  · have hxK : x ∈ centralizer (L : Set G) := by rw [hxz]; exact B.cyc.le B.cyc.mem
    exact (permOf_eq_one_iff B θ hx).2 hxK
  · have hxK : x ∈ centralizer (L : Set G) := by rw [hx1]; exact one_mem _
    exact (permOf_eq_one_iff B θ hx).2 hxK

theorem isKGroupCat_twoSecO (hS : StandardSetting G L) {x : G} (hx1 : x ≠ 1) :
    CFSG.SectionRank.IsKGroupCat (TwoSecO x) :=
  ((isKGroupCat_of_kProper hS.kProper _
    (centralizer_singleton_ne_top_of_simple hS.simple hS.nonab hx1)).quotient _).quotient _

theorem oddCore_twoSecO_eq_bot (x : G) : CFSG.oddCore (TwoSecO x) = ⊥ :=
  ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _

omit [Finite G] in
theorem eq_one_of_mul_self_of_odd {g : G} (hg : g * g = 1) (hodd : Odd (orderOf g)) : g = 1 := by
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg)
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
  · exact orderOf_eq_one_iff.1 h1
  · rw [h2] at hodd
    exact absurd hodd (by decide)

theorem odd_orderOf_of_mem_oddCoreOf {H : Subgroup G} {o : G} (ho : o ∈ oddCoreOf H) :
    Odd (orderOf o) := by
  obtain ⟨hoH, hO⟩ := mem_oddCoreOf_iff.1 ho
  have := orderOf_odd_of_mem_oddCore hO
  rwa [Subgroup.orderOf_mk] at this

theorem eq_one_of_mem_corr_of_mem_oddCoreOf (B : Base G L Q n z)
    (θ : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (h5 : 5 ≤ (fixFin (permOf B θ hx)).card) {w : G}
    (hwR : w ∈ corr (X := G) θ (altSub (fixFin (permOf B θ hx))))
    (hwO : w ∈ oddCoreOf (centralizer ({x} : Set G))) : w = 1 := by
  set F := fixFin (permOf B θ hx) with hF
  have hRx : corr (X := G) θ (altSub F) ≤ centralizer ({x} : Set G) := by
    intro r hr
    rw [mem_centralizer_singleton_iff]
    exact (comm_of_mem_corr_of_permOf_fix B θ hx (fun i hi => mem_fixFin.1 hi) hr).symm
  obtain ⟨φ⟩ := exists_equiv_corr_altSub (X := G) θ F
  have hbot := inf_oddCore_eq_bot_of_alt h5 ((Subgroup.subgroupOfEquivOfLe hRx).trans φ)
  obtain ⟨hwC, hwO'⟩ := mem_oddCoreOf_iff.1 hwO
  have hmem : (⟨w, hwC⟩ : ↥(centralizer ({x} : Set G))) ∈
      (corr (X := G) θ (altSub F)).subgroupOf (centralizer ({x} : Set G)) ⊓
        CFSG.oddCore ↥(centralizer ({x} : Set G)) := Subgroup.mem_inf.2 ⟨hwR, hwO'⟩
  rw [hbot] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hmem)

theorem swapIota_ofSubtype_sq_mem_corr (T : Shape G L Q n z u)
    (θ : L ≃* alternatingGroup (Fin n)) {F : Finset (Fin n)} (π : Perm ↥F) :
    (swapIota T θ (Perm.ofSubtype π) : G) * (swapIota T θ (Perm.ofSubtype π) : G) ∈
      corr (X := G) θ (altSub F) := by
  have hC := swapIota_mem_centralizer T θ (Perm.ofSubtype π)
  have hL : (swapIota T θ (Perm.ofSubtype π) : G) * (swapIota T θ (Perm.ofSubtype π) : G) ∈ L :=
    T.mul_self_mem (swapIota T θ (Perm.ofSubtype π)).2
  refine mem_corr.2 ⟨hL, ?_⟩
  have h1 := permOf_of_mem T.toBase θ (mul_mem hC hC) hL
  rw [permOf_mul T.toBase θ hC hC (mul_mem hC hC), permOf_swapIota] at h1
  rw [← h1]
  refine mem_altSub.2 ⟨?_, fun i hi => ?_⟩
  · rw [Perm.sign_mul, Int.units_mul_self]
  · have : Perm.ofSubtype π i = i := Perm.ofSubtype_apply_of_not_mem π hi
    simp [Perm.mul_apply, this]

end Basic

section Kappa

theorem conj_swapIota_mem_centralizer (T : Shape G L Q n z u)
    (θ : L ≃* alternatingGroup (Fin n)) {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    y * (swapIota T θ (Perm.ofSubtype π) : G) * y⁻¹ ∈ centralizer ({x} : Set G) := by
  have hst : (swapIota T θ (Perm.ofSubtype π) : G) * (swapIota T θ (permOf T.toBase θ hx) : G) =
      (swapIota T θ (permOf T.toBase θ hx) : G) * (swapIota T θ (Perm.ofSubtype π) : G) := by
    have : swapIota T θ (Perm.ofSubtype π) * swapIota T θ (permOf T.toBase θ hx) =
        swapIota T θ (permOf T.toBase θ hx) * swapIota T θ (Perm.ofSubtype π) := by
      rw [← map_mul, ← map_mul, ofSubtype_comm_of_fixFin π]
    exact congrArg Subtype.val this
  have hsz := swapIota_comm_z T θ (Perm.ofSubtype π)
  have key : ∀ s w : G, s * w = w * s →
      y * s * y⁻¹ * (y * w * y⁻¹) = y * w * y⁻¹ * (y * s * y⁻¹) := by
    intro s w hw
    calc y * s * y⁻¹ * (y * w * y⁻¹) = y * (s * w) * y⁻¹ := by group
      _ = y * (w * s) * y⁻¹ := by rw [hw]
      _ = y * w * y⁻¹ * (y * s * y⁻¹) := by group
  have hszt : ∀ s t : G, z * s = s * z → s * t = t * s → s * (z * t) = z * t * s := by
    intro s t h1 h2
    calc s * (z * t) = (s * z) * t := by group
      _ = (z * s) * t := by rw [h1]
      _ = z * (s * t) := by group
      _ = z * (t * s) := by rw [h2]
      _ = z * t * s := by group
  rw [mem_centralizer_singleton_iff]
  rcases hxy with h | h
  · have h1 := key _ _ hst
    rw [← h] at h1
    exact h1
  · have h1 := key _ _ (hszt _ _ hsz hst)
    rw [← h] at h1
    exact h1

@[expose] noncomputable def twoKappa (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹) :
    Perm ↥(fixFin (permOf T.toBase θ hx)) →* ↥(centralizer ({x} : Set G)) :=
  ((MulAut.conj y).toMonoidHom.comp ((L ⊔ zpowers u).subtype.comp
      ((swapIota T θ).toMonoidHom.comp
        (Perm.ofSubtype : Perm ↥(fixFin (permOf T.toBase θ hx)) →* Perm (Fin n))))).codRestrict _
    (conj_swapIota_mem_centralizer T θ hx hxy)

theorem twoKappa_apply (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) {x y : G}
    (hx : x ∈ centralizer ({z} : Set G))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    (twoKappa T θ hx hxy π : G) = y * (swapIota T θ (Perm.ofSubtype π) : G) * y⁻¹ := rfl

theorem twoKappa_mem_centralizer (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    (twoKappa T θ hx hxy π : G) ∈ centralizer ({z} : Set G) := by
  have hyC := oddY_le_centralizer_z T.cyc hy
  rw [twoKappa_apply]
  exact mul_mem (mul_mem hyC (swapIota_mem_centralizer T θ _)) (inv_mem hyC)

theorem permOf_twoKappa (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    permOf T.toBase θ (twoKappa_mem_centralizer T θ hx hy hxy π) = Perm.ofSubtype π :=
  (permOf_conj_of_mem_oddY T.toBase θ (swapIota_mem_centralizer T θ (Perm.ofSubtype π)) hy
    (twoKappa_mem_centralizer T θ hx hy hxy π)).trans (permOf_swapIota T θ _)

theorem twoKappa_comm_z (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    (twoKappa T θ hx hxy π : G) * z = z * twoKappa T θ hx hxy π :=
  mem_centralizer_singleton_iff.1 (twoKappa_mem_centralizer T θ hx hy hxy π)

theorem twoKappa_injective (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹) :
    Function.Injective (twoKappa T θ hx hxy) := by
  intro π₁ π₂ h
  have h1 : (twoKappa T θ hx hxy π₁ : G) = twoKappa T θ hx hxy π₂ := congrArg Subtype.val h
  rw [twoKappa_apply, twoKappa_apply] at h1
  have h2 : (swapIota T θ (Perm.ofSubtype π₁) : G) = swapIota T θ (Perm.ofSubtype π₂) := by
    calc (swapIota T θ (Perm.ofSubtype π₁) : G) =
        y⁻¹ * (y * (swapIota T θ (Perm.ofSubtype π₁) : G) * y⁻¹) * y := by group
      _ = y⁻¹ * (y * (swapIota T θ (Perm.ofSubtype π₂) : G) * y⁻¹) * y := by rw [h1]
      _ = swapIota T θ (Perm.ofSubtype π₂) := by group
  exact Perm.ofSubtype_injective ((swapIota T θ).injective (Subtype.ext h2))

@[expose] noncomputable def twoThetaO (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹) :
    Perm ↥(fixFin (permOf T.toBase θ hx)) →* TwoSecO x :=
  (QuotientGroup.mk' (CFSG.oddCore (TwoSec x))).comp
    ((QuotientGroup.mk' (zpowers (selfC x))).comp (twoKappa T θ hx hxy))

theorem twoThetaO_apply (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) {x y : G}
    (hx : x ∈ centralizer ({z} : Set G))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    twoThetaO T θ hx hxy π =
      (QuotientGroup.mk (QuotientGroup.mk (twoKappa T θ hx hxy π) : TwoSec x) : TwoSecO x) :=
  rfl

theorem twoThetaO_comm (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) {x y : G}
    (hx : x ∈ centralizer ({z} : Set G))
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (hzx : z ∈ centralizer ({x} : Set G)) (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    twoThetaO T θ hx hxy π * (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x) =
      QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) * twoThetaO T θ hx hxy π := by
  have h1 : twoKappa T θ hx hxy π * ⟨z, hzx⟩ = ⟨z, hzx⟩ * twoKappa T θ hx hxy π :=
    Subtype.ext (twoKappa_comm_z T θ hx hy hxy π)
  rw [twoThetaO_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, h1]

theorem twoThetaO_injective (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n))
    (hn : 7 ≤ n) {x y : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf T.toBase θ hx).IsSwap) (hx2 : x * x = 1)
    (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹) :
    Function.Injective (twoThetaO T θ hx hxy) := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  rw [twoThetaO_apply, QuotientGroup.eq_one_iff] at hπ
  set s : G := (swapIota T θ (Perm.ofSubtype π) : G) with hs
  have hkC := twoKappa_mem_centralizer T θ hx hy hxy π
  have hpk := permOf_twoKappa T θ hx hy hxy π
  have h5 : 5 ≤ (fixFin (permOf T.toBase θ hx)).card := by
    rw [card_fixFin_of_isSwap hτ]; omega
  have hsL : s * s ∈ L := T.mul_self_mem (swapIota T θ (Perm.ofSubtype π)).2
  have hkk : (twoKappa T θ hx hxy π : G) * twoKappa T θ hx hxy π = s * s := by
    rw [twoKappa_apply]
    have hys : s * s * y = y * (s * s) :=
      mem_centralizer_iff.1 (oddY_le_centralizer T.cyc hy) (s * s) hsL
    calc y * s * y⁻¹ * (y * s * y⁻¹) = (y * (s * s)) * y⁻¹ := by group
      _ = (s * s * y) * y⁻¹ := by rw [hys]
      _ = s * s := by group
  have hkR : (twoKappa T θ hx hxy π : G) * twoKappa T θ hx hxy π ∈
      corr (X := G) θ (altSub (fixFin (permOf T.toBase θ hx))) := by
    rw [hkk]
    exact swapIota_ofSubtype_sq_mem_corr T θ π
  obtain ⟨o, ho, hko⟩ := exists_oddCoreOf_of_mk_mem_oddCore hx2 hπ
  have hoC : o ∈ centralizer ({x} : Set G) := (mem_oddCoreOf_iff.1 ho).1
  have hkko : (twoKappa T θ hx hxy π : G) * twoKappa T θ hx hxy π = o * o := by
    rcases hko with h | h
    · rw [h]
    · have hxo : x * o = o * x := (mem_centralizer_singleton_iff.1 hoC).symm
      rw [h]
      calc x * o * (x * o) = x * (o * x) * o := by group
        _ = x * (x * o) * o := by rw [hxo]
        _ = (x * x) * (o * o) := by group
        _ = o * o := by rw [hx2, one_mul]
  have hooR : o * o ∈ corr (X := G) θ (altSub (fixFin (permOf T.toBase θ hx))) := hkko ▸ hkR
  have hoo : o * o = 1 := eq_one_of_mem_corr_of_mem_oddCoreOf T.toBase θ hx h5 hooR
    (mul_mem ho ho)
  have ho1 : o = 1 := eq_one_of_mul_self_of_odd hoo (odd_orderOf_of_mem_oddCoreOf ho)
  rcases hko with h | h
  · rw [ho1] at h
    apply twoKappa_injective T θ hx hxy
    rw [map_one]
    exact Subtype.ext h
  · exfalso
    rw [ho1, mul_one] at h
    have h2 := permOf_congr T.toBase θ h hkC hx
    rw [hpk] at h2
    exact ofSubtype_ne_of_isSwap hτ π h2

theorem twoThetaO_ne (T : Shape G L Q n z u) (θ : L ≃* alternatingGroup (Fin n)) (hn : 7 ≤ n)
    {x y : G} (hx : x ∈ centralizer ({z} : Set G)) (hτ : (permOf T.toBase θ hx).IsSwap)
    (hx2 : x * x = 1) (hy : y ∈ oddPart (centralizer (L : Set G) ⊓ centralizer ({z} : Set G)))
    (hxy : x = y * (swapIota T θ (permOf T.toBase θ hx) : G) * y⁻¹ ∨
      x = y * (z * (swapIota T θ (permOf T.toBase θ hx) : G)) * y⁻¹)
    (hzx : z ∈ centralizer ({x} : Set G)) (π : Perm ↥(fixFin (permOf T.toBase θ hx))) :
    twoThetaO T θ hx hxy π ≠
      (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x) := by
  intro hπ
  have hz2 : z * z = 1 := T.cyc.mul_self
  obtain ⟨k, hkdef⟩ : ∃ k, k = twoKappa T θ hx hxy π := ⟨_, rfl⟩
  have hkC : (k : G) ∈ centralizer ({z} : Set G) := by
    rw [hkdef]; exact twoKappa_mem_centralizer T θ hx hy hxy π
  have hkz : (k : G) * z = z * k := by
    rw [hkdef]; exact twoKappa_comm_z T θ hx hy hxy π
  have hpk : permOf T.toBase θ hkC = Perm.ofSubtype π := by
    subst hkdef; exact permOf_twoKappa T θ hx hy hxy π
  have hzbb : (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) : TwoSecO x) *
      QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) = 1 := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have : (⟨z, hzx⟩ : ↥(centralizer ({x} : Set G))) * ⟨z, hzx⟩ = 1 := Subtype.ext hz2
    rw [this]
    rfl
  have hππ : π * π = 1 := by
    apply twoThetaO_injective T θ hn hx hτ hx2 hy hxy
    rw [map_mul, hπ, hzbb, map_one]
  have hkk : (k : G) * k = 1 := by
    have : k * k = 1 := by rw [hkdef, ← map_mul, hππ, map_one]
    exact congrArg Subtype.val this
  have hkinv : (k : G)⁻¹ = k := inv_eq_of_mul_eq_one_right hkk
  obtain ⟨w, hw⟩ : ∃ w : ↥(centralizer ({x} : Set G)), w = k⁻¹ * ⟨z, hzx⟩ := ⟨_, rfl⟩
  have hwO : (QuotientGroup.mk w : TwoSec x) ∈ CFSG.oddCore (TwoSec x) := by
    rw [twoThetaO_apply, QuotientGroup.eq, ← hkdef] at hπ
    rw [hw, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hπ
  have hwG : (w : G) = k * z := by
    rw [hw, Subgroup.coe_mul, Subgroup.coe_inv, hkinv]
  have hww : (QuotientGroup.mk w : TwoSec x) * QuotientGroup.mk w = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : w * w = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hwG]
      calc (k : G) * z * (k * z) = (k : G) * (z * k) * z := by group
        _ = (k : G) * (k * z) * z := by rw [hkz]
        _ = ((k : G) * k) * (z * z) := by group
        _ = 1 := by rw [hkk, hz2, one_mul]
    rw [this]
    rfl
  have hw1 := eq_one_of_mul_self_of_odd hww (orderOf_odd_of_mem_oddCore hwO)
  rw [QuotientGroup.eq_one_iff] at hw1
  rcases (mem_zpowers_selfC_iff hx2).1 hw1 with h | h
  ·
    rw [hwG] at h
    have hzk : z = k := by
      calc z = (k : G)⁻¹ * (k * z) := by group
        _ = k := by rw [h, mul_one, hkinv]
    apply T.z_notMem
    have hyC := oddY_le_centralizer_z T.cyc hy
    have hyz : y⁻¹ * z * y = z := by
      rw [mul_assoc, ← mem_centralizer_singleton_iff.1 hyC]
      group
    have hkG : (k : G) = y * (swapIota T θ (Perm.ofSubtype π) : G) * y⁻¹ := by
      rw [hkdef, twoKappa_apply]
    have h3 : y⁻¹ * z * y = (swapIota T θ (Perm.ofSubtype π) : G) := by
      calc y⁻¹ * z * y = y⁻¹ * (k : G) * y := by rw [← hzk]
        _ = y⁻¹ * (y * (swapIota T θ (Perm.ofSubtype π) : G) * y⁻¹) * y := by rw [hkG]
        _ = (swapIota T θ (Perm.ofSubtype π) : G) := by group
    have hmem : y⁻¹ * z * y ∈ L ⊔ zpowers u := by
      rw [h3]
      exact (swapIota T θ (Perm.ofSubtype π)).2
    rw [hyz] at hmem
    exact hmem
  ·
    have hzC : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
    have hkiC : (k : G)⁻¹ ∈ centralizer ({z} : Set G) := inv_mem hkC
    have hm : (k : G)⁻¹ * z ∈ centralizer ({z} : Set G) := mul_mem hkiC hzC
    have hwx : (k : G)⁻¹ * z = x := by
      have h' := h
      rw [hw, Subgroup.coe_mul, Subgroup.coe_inv] at h'
      exact h'
    have h2 := permOf_congr T.toBase θ hwx hm hx
    rw [permOf_mul T.toBase θ hkiC hzC hm, permOf_inv T.toBase θ hkC hkiC,
      (permOf_eq_one_iff T.toBase θ hzC).2 (T.cyc.le T.cyc.mem), mul_one, hpk, ← map_inv] at h2
    exact ofSubtype_ne_of_isSwap hτ π⁻¹ h2

end Kappa

end CFSG.OddStandard.AltStdCycTwo.Two

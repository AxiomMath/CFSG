module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8S87a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8SFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Facts2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L66In
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L68a

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec8s_centerIn_commute {H : Subgroup G} {w b : G} (hw : w ∈ centerIn H)
    (hb : b ∈ H) : w * b = b * w := by
  rw [centerIn, Subgroup.mem_map] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  have h := Subgroup.mem_center_iff.mp hw' (⟨b, hb⟩ : ↥H)
  exact (congrArg Subtype.val h).symm

theorem sec8s_core {t z x : G} {Lg B : Subgroup G} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hBLg : B ≤ Lg) (hzB : z ∈ B)
    (hBe : ∀ b ∈ B, b * b = 1) (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (htB : ∀ b ∈ B, b * t = t * b) (htz : ∀ n ∈ Lg, n * (t * z) = (t * z) * n)
    (hxx : x * x = t) (hxn : x ∈ normalizer (Lg : Set G)) (hxB : ∀ b ∈ B, x * b = b * x)
    (hcent : ∀ l ∈ Lg, (∀ b ∈ B, l * b = b * l) →
      ∃ b ∈ B, ∃ w ∈ Lg, (∀ l' ∈ Lg, w * l' = l' * w) ∧ l = b * w)
    (hodd : ∀ w ∈ Lg, (∀ l' ∈ Lg, w * l' = l' * w) → Odd (orderOf w))
    (htrans : ∀ b ∈ B, b ≠ 1 → ∀ b' ∈ B, b' ≠ 1 →
      ∃ n ∈ Lg ⊓ normalizer (B : Set G), n * b * n⁻¹ = b')
    (hB3 : ∃ b ∈ B, b ≠ 1 ∧ b ≠ z) : False := by
  obtain ⟨b₀, hb₀B, hb₀1, hb₀z⟩ := hB3
  obtain ⟨n, hn, hnz⟩ := htrans z hzB hz1 b₀ hb₀B hb₀1
  have hnLg : n ∈ Lg := hn.1
  have hnN : n ∈ normalizer (B : Set G) := hn.2
  have hxinv : x⁻¹ ∈ normalizer (Lg : Set G) := inv_mem hxn
  have hxl' : x⁻¹ * n * x ∈ Lg := by
    have h := (Subgroup.mem_normalizer_iff.mp hxinv n).mp hnLg
    simpa using h
  have hb'B : ∀ b ∈ B, n⁻¹ * b * n ∈ B := by
    intro b hb
    have hninv : n⁻¹ ∈ normalizer (B : Set G) := (normalizer (B : Set G)).inv_mem hnN
    have h := (Subgroup.mem_normalizer_iff.mp hninv b).mp hb
    simpa using h
  have hycent : n * x * n⁻¹ ∈ centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hxb' : x * (n⁻¹ * b * n) = (n⁻¹ * b * n) * x := hxB _ (hb'B b hb)
    calc b * (n * x * n⁻¹)
        = n * ((n⁻¹ * b * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * b * n)) * n⁻¹ := by rw [← hxb']
      _ = (n * x * n⁻¹) * b := by group
  have hxcent : x ∈ centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact (hxB b hb).symm
  have hl'cent : x⁻¹ * (n * x * n⁻¹) ∈ centralizer (B : Set G) :=
    mul_mem (inv_mem hxcent) hycent
  have hl'Lg : x⁻¹ * (n * x * n⁻¹) ∈ Lg := by
    have heq : x⁻¹ * (n * x * n⁻¹) = (x⁻¹ * n * x) * n⁻¹ := by group
    rw [heq]
    exact Lg.mul_mem hxl' (Lg.inv_mem hnLg)
  obtain ⟨b₁, hb₁B, w, hwLg, hwcent, hl'eq⟩ :=
    hcent (x⁻¹ * (n * x * n⁻¹)) hl'Lg
      (fun b hb => (Subgroup.mem_centralizer_iff.mp hl'cent b hb).symm)
  have hy_eq : n * x * n⁻¹ = x * (b₁ * w) := by rw [← hl'eq]; group
  have hw'Lg : x⁻¹ * w * x ∈ Lg := by
    have h := (Subgroup.mem_normalizer_iff.mp hxinv w).mp hwLg
    simpa using h
  have hw'cent : ∀ l' ∈ Lg, (x⁻¹ * w * x) * l' = l' * (x⁻¹ * w * x) := by
    intro l' hl'
    have hxl' : x * l' * x⁻¹ ∈ Lg := (Subgroup.mem_normalizer_iff.mp hxn l').mp hl'
    have hcomm := hwcent (x * l' * x⁻¹) hxl'
    calc (x⁻¹ * w * x) * l'
        = x⁻¹ * (w * (x * l' * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * l' * x⁻¹) * w) * x := by rw [hcomm]
      _ = l' * (x⁻¹ * w * x) := by group
  have hwx : w * x = x * (x⁻¹ * w * x) := by group
  have hb₁w' : b₁ * (x⁻¹ * w * x) = (x⁻¹ * w * x) * b₁ :=
    (hw'cent b₁ (hBLg hb₁B)).symm
  have hb₁sq : b₁ * b₁ = 1 := hBe b₁ hb₁B
  have hb₁x : b₁ * x = x * b₁ := (hxB b₁ hb₁B).symm
  have hsq1 : (x * (b₁ * w)) * (x * (b₁ * w)) =
      (n * x * n⁻¹) * (n * x * n⁻¹) := by rw [hy_eq]
  have hbb : ((x⁻¹ * w * x) * b₁) * b₁ = x⁻¹ * w * x := by
    rw [mul_assoc, hb₁sq, mul_one]
  have hsq2 : (x * (b₁ * w)) * (x * (b₁ * w)) = t * ((x⁻¹ * w * x) * w) := by
    calc (x * (b₁ * w)) * (x * (b₁ * w))
        = x * b₁ * (w * x) * b₁ * w := by group
      _ = x * b₁ * (x * (x⁻¹ * w * x)) * b₁ * w := by rw [hwx]
      _ = (b₁ * x) * x * (x⁻¹ * w * x) * b₁ * w := by rw [← hb₁x]; group
      _ = b₁ * (x * x) * (x⁻¹ * w * x) * b₁ * w := by group
      _ = b₁ * t * (x⁻¹ * w * x) * b₁ * w := by rw [hxx]
      _ = t * b₁ * (x⁻¹ * w * x) * b₁ * w := by rw [htB b₁ hb₁B]
      _ = t * (b₁ * (x⁻¹ * w * x)) * b₁ * w := by group
      _ = t * ((x⁻¹ * w * x) * b₁) * b₁ * w := by rw [hb₁w']
      _ = t * (((x⁻¹ * w * x) * b₁) * b₁) * w := by group
      _ = t * (x⁻¹ * w * x) * w := by rw [hbb]
      _ = t * ((x⁻¹ * w * x) * w) := by group
  have hnt : n * t * n⁻¹ = (n * x * n⁻¹) * (n * x * n⁻¹) := by rw [← hxx]; group
  have hconj : n * t * n⁻¹ = (n * (t * z) * n⁻¹) * (n * z * n⁻¹) := by
    conv_lhs => rw [show t = (t * z) * z by rw [mul_assoc, hz2, mul_one]]
    group
  have hnt2 : n * t * n⁻¹ = (t * z) * b₀ := by
    rw [hconj, htz n hnLg, hnz]
    group
  have htu : t * ((x⁻¹ * w * x) * w) = t * (z * b₀) := by
    rw [← hsq2, hsq1, ← hnt, hnt2]
    group
  have hu_eq : (x⁻¹ * w * x) * w = z * b₀ := mul_left_cancel htu
  have hzb0sq : (z * b₀) * (z * b₀) = 1 := by
    calc (z * b₀) * (z * b₀) = z * (b₀ * z) * b₀ := by group
      _ = z * (z * b₀) * b₀ := by rw [← hBc z hzB b₀ hb₀B]
      _ = (z * z) * (b₀ * b₀) := by group
      _ = 1 := by rw [hz2, hBe b₀ hb₀B, mul_one]
  have hzb0ne : z * b₀ ≠ 1 := by
    intro h
    have h1 : b₀ = z⁻¹ := eq_inv_of_mul_eq_one_right h
    have h2 : b₀ = z := by rwa [inv_eq_of_mul_eq_one_right hz2] at h1
    exact hb₀z h2
  have hzb02 : orderOf (z * b₀) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hzb0ne
  have huLg : (x⁻¹ * w * x) * w ∈ Lg := Lg.mul_mem hw'Lg hwLg
  have hucent : ∀ l' ∈ Lg, ((x⁻¹ * w * x) * w) * l' = l' * ((x⁻¹ * w * x) * w) := by
    intro l' hl'
    calc ((x⁻¹ * w * x) * w) * l'
        = (x⁻¹ * w * x) * (w * l') := by group
      _ = (x⁻¹ * w * x) * (l' * w) := by rw [hwcent l' hl']
      _ = ((x⁻¹ * w * x) * l') * w := by group
      _ = (l' * (x⁻¹ * w * x)) * w := by rw [hw'cent l' hl']
      _ = l' * ((x⁻¹ * w * x) * w) := by group
  have hodd_u : Odd (orderOf ((x⁻¹ * w * x) * w)) := hodd _ huLg hucent
  rw [hu_eq, hzb02] at hodd_u
  exact (by decide : ¬ Odd 2) hodd_u

theorem asc82Lemma87_of (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (h85 : Asc82Lemma85)
    (h86 : Asc82Lemma86) (hB : Asc82Sec8B) (hM : Asc82Tab6M) (hI : Asc82Sec8I3) :
    Asc82Lemma87 := by
  intro G _ _ t L S z g B hctx y α
  classical
  by_contra hcon
  have hy : InducesTypeSome L y 6 (-1) 1 α ∨ InducesTypeSome L y 6 (-1) 3 α := by
    by_contra h
    rw [not_or] at h
    exact hcon ⟨h.1, h.2⟩
  have hS : Sec3SettingLB G t L := hctx.toSec3SettingLB
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hctx.omega6m⟩
  have hSyl : IsSylow2Of S (normalizer (L : Set G)) :=
    sec8s_sylow_normalizer h36 h68 h85 h86 hB hctx
  obtain ⟨B', hB'le, hB'e, x, hxSC, hxL, α', hx3⟩ := hI G L S hLM hSyl ⟨y, α, hy⟩
  have hxS : x ∈ S := hxSC.1
  have hxB : ∀ b ∈ B', x * b = b * x := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp hxSC.2 b hb).symm
  have ht2 : t * t = 1 := by rw [← pow_two, ← hS.involution, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : orderOf t = 1 := by rw [h, orderOf_one]
    have h2 := hS.involution
    omega
  have hz2ord : orderOf z = 2 := hctx.pocket.1
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz2ord, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    have h1 : orderOf z = 1 := by rw [h, orderOf_one]
    have h2 := hz2ord
    omega
  have h85c : S ⊓ L = S ⊓ CFSG.conjugate L g := h85 G t L S z g B hctx
  have hBLg : B' ≤ CFSG.conjugate L g := fun b hb => by
    have hb' : b ∈ S ⊓ L := ⟨(hB'le hb).2, (hB'le hb).1⟩
    rw [h85c] at hb'
    exact hb'.2
  have hbase : Sec8Base G t L S z g B' :=
    ⟨hctx.toSec8Setting, hctx.tz, hB'le, hB'e⟩
  have hzB : z ∈ B' := (hB G t L S z g B' hbase).1
  haveI : IsMulCommutative B' := hB'e.1.1
  have hBe : ∀ b ∈ B', b * b = 1 := fun b hb =>
    CFSG.Open.IsElemAbelian.mul_self_eq_one hB'e.1 hb
  have hBc : ∀ b ∈ B', ∀ b' ∈ B', b * b' = b' * b := fun b hb b' hb' =>
    CFSG.Open.IsElemAbelian.comm hB'e.1 hb hb'
  have htB : ∀ b ∈ B', b * t = t * b := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le (hB'le hb).1)
  have htz : ∀ n ∈ CFSG.conjugate L g, n * (t * z) = (t * z) * n := by
    intro n hn
    have hmL : g * n * g⁻¹ ∈ L := mem_conjugate_iff'.mp hn
    have hmt : (g * n * g⁻¹) * t = t * (g * n * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hmL)
    calc n * (t * z) = (g⁻¹ * (g * n * g⁻¹) * g) * (g⁻¹ * t * g) := by
          rw [← hctx.tz]; group
      _ = g⁻¹ * ((g * n * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * n * g⁻¹)) * g := by rw [hmt]
      _ = (g⁻¹ * t * g) * (g⁻¹ * (g * n * g⁻¹) * g) := by group
      _ = (t * z) * n := by rw [hctx.tz]; group
  have hLgM : IsOm6M (CFSG.conjugate L g) := sec68_isOm6M_conjugate hLM g
  have hxx : x * x = t := by
    by_cases hsq : x * x = 1
    · exfalso
      have hx1 : x ≠ 1 := by
        intro h
        exact hxL (h ▸ Subgroup.one_mem _)
      have hx2 : orderOf x = 2 := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (p := 2) (by rwa [pow_two]) hx1
      exact hctx.no_i3 x (hctx.sylow.1 hxS) hx2 α' hx3
    · have hxsqC : x * x ∈ centralizer (L : Set G) := sec68_sq_mem_centralizer hLM hx3
      have hxsqS : x * x ∈ S := S.mul_mem hxS hxS
      have hxsq : x * x ∈ Subgroup.zpowers t := by
        have h : x * x ∈ S ⊓ centralizer (L : Set G) := ⟨hxsqS, hxsqC⟩
        rwa [h86 G t L S z g B hctx] at h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxsq
      have hk2 : x * x = t ^ (k % 2) := by
        have h := zpow_mod_orderOf t k
        rw [hS.involution] at h
        exact (h.trans hk).symm
      have hrem : k % 2 = 0 ∨ k % 2 = 1 := by
        have h1 : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
        have h2 : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
        omega
      rcases hrem with h0 | h1
      · rw [h0, zpow_zero] at hk2
        exact absurd hk2 hsq
      · rw [h1, zpow_one] at hk2
        exact hk2
  have hxn : x ∈ normalizer ((CFSG.conjugate L g : Subgroup G) : Set G) :=
    sec8s_mem_normalizer_conj h36 hctx hxS
  have hB'p : IsPGroup 2 B' := IsPGroup.of_card (n := 4) hB'e.2
  obtain ⟨P, hPsyl, hB'P⟩ := sec68_exists_sylow_ge (H := CFSG.conjugate L g) hB'p hBLg
  obtain ⟨_, htrans, hcentB⟩ := hM.aut_B G (CFSG.conjugate L g) hLgM P hPsyl B' hB'P hB'e
  have hcent : ∀ l ∈ CFSG.conjugate L g,
      (∀ b ∈ B', l * b = b * l) →
      ∃ b ∈ B', ∃ w ∈ CFSG.conjugate L g,
        (∀ l' ∈ CFSG.conjugate L g, w * l' = l' * w) ∧ l = b * w := by
    intro l hl hlc
    have hlcent : l ∈ centralizer (B' : Set G) :=
      Subgroup.mem_centralizer_iff.mpr (fun b hb => (hlc b hb).symm)
    have hlmem : l ∈ CFSG.conjugate L g ⊓ centralizer (B' : Set G) := ⟨hl, hlcent⟩
    rw [hcentB] at hlmem
    obtain ⟨b, hbB, w, hwCenter, hl_eq⟩ :=
      exists_mul_of_mem_sup_of_commute (H := B') (K := centerIn (CFSG.conjugate L g))
        (fun b hb w hw => (sec8s_centerIn_commute hw (hBLg hb)).symm) hlmem
    refine ⟨b, hbB, w,
      Subgroup.map_subtype_le (Subgroup.center (CFSG.conjugate L g)) hwCenter, ?_, hl_eq⟩
    intro l' hl'
    exact sec8s_centerIn_commute hwCenter hl'
  have hodd : ∀ w ∈ CFSG.conjugate L g,
      (∀ l' ∈ CFSG.conjugate L g, w * l' = l' * w) → Odd (orderOf w) := by
    intro w hw hwc
    exact sec66_odd_of_mem_inf hLgM
      ⟨hw, Subgroup.mem_centralizer_iff.mpr (fun l' hl' => (hwc l' hl').symm)⟩
  have hB3 : ∃ b ∈ B', b ≠ 1 ∧ b ≠ z := by
    have hnot : ¬ (∀ b ∈ B', b = 1 ∨ b = z) := by
      intro hsub
      have hBle : B' ≤ Subgroup.zpowers z := by
        intro b hb
        rcases hsub b hb with h | h
        · rw [h]; exact Subgroup.one_mem _
        · rw [h]; exact Subgroup.mem_zpowers z
      have hle := Subgroup.card_le_of_le hBle
      rw [Nat.card_zpowers, hz2ord, hB'e.2] at hle
      norm_num at hle
    push Not at hnot
    exact hnot
  exact sec8s_core (Lg := CFSG.conjugate L g) (B := B') ht2 ht1 hz2 hz1 hBLg hzB hBe hBc
    htB htz hxx hxn hxB hcent hodd htrans hB3

end CFSG.OddStandard.SmallF3.Omega

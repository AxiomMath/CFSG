module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.Lift
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Layer0

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.EvenSporadicStandard.HSStd

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.false_of_tight_config_ge8 (h : StdHyp G L)
    (hZ : ∀ z ∈ center L, z ^ 2 = 1)
    (hout : (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range.index ∣ 2)
    (hOF : OddFixFourth (L ⧸ center L)) {T : Subgroup G} {s : G} {n : ℕ} (hn : 3 ≤ n)
    (hT : IsPGroup 2 T) (hTcyc : IsCyclic T) (hsT : s ∈ T) (hs : orderOf s = 2 ^ n)
    (hsN : s ∈ normalizer (L : Set G))
    (hTC : ∀ y ∈ T, y ∈ centralizer (L : Set G) → y = 1)
    (hnorm : ∀ x : G, x * s ^ 2 ^ (n - 1) = s ^ 2 ^ (n - 1) * x → ∀ y ∈ T, x * y * x⁻¹ ∈ T) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : commutator L = ⊤ := h.standard.1.1
  set C := centralizer (L : Set G) with hCdef
  set t₁ : G := s ^ 2 ^ (n - 1) with ht₁def
  have ht₁T : t₁ ∈ T := Subgroup.pow_mem _ hsT _
  have ht₁2 : orderOf t₁ = 2 := orderOf_pow_two_pow_pred (by omega) hs
  have ht₁1 : t₁ * t₁ = 1 := by rw [← sq, ← ht₁2, pow_orderOf_eq_one]
  have hs2 : s ^ 2 ∈ L ⊔ C := h.sq_mem_sup_centralizer hout hsN
  obtain ⟨l₂, hl₂, c₂, hc₂, hsq⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (A := L) (B := C) le_rfl hs2
  have hlc : Commute l₂ c₂ := mem_centralizer_iff.mp hc₂ l₂ hl₂
  set z : G := l₂ ^ 2 ^ (n - 2) with hzdef
  set c : G := c₂ ^ 2 ^ (n - 2) with hcdef
  have hzL : z ∈ L := Subgroup.pow_mem _ hl₂ _
  have hcC : c ∈ C := Subgroup.pow_mem _ hc₂ _
  have hzc : Commute z c := hlc.pow_pow _ _
  have ht₁zc : t₁ = z * c := by
    have h2n : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      rw [← pow_succ' 2 (n - 2)]; congr 1; omega
    rw [ht₁def, h2n, pow_mul, hsq, hlc.mul_pow]
  have hsq' : (z * c) * (z * c) = z * z * (c * c) := by
    calc (z * c) * (z * c) = z * (c * z) * c := by group
      _ = z * (z * c) * c := by rw [← hzc.eq]
      _ = z * z * (c * c) := by group
  have h1 : z * z * (c * c) = 1 := by rw [← hsq', ← ht₁zc, ht₁1]
  have hzzL : z * z ∈ L := L.mul_mem hzL hzL
  have hzzC : z * z ∈ C := by
    have hcc : c * c ∈ C := C.mul_mem hcC hcC
    have : z * z = (c * c)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]; exact C.inv_mem hcc
  have hzzZ : (⟨z * z, hzzL⟩ : L) ∈ center L := by
    have hmem : z * z ∈ (center L).map L.subtype := by
      rw [map_center_eq_inf_centralizer]; exact ⟨hzzL, hzzC⟩
    obtain ⟨w, hw, hwe⟩ := hmem
    have : w = ⟨z * z, hzzL⟩ := Subtype.ext hwe
    rwa [this] at hw
  set zL : L := ⟨z, hzL⟩ with hzLdef
  have hzL2 : zL * zL ∈ center L := hzzZ
  have hzcen : zL ∉ center L := by
    intro hz
    have hzC : z ∈ C := mem_centralizer_iff.2 fun l hl =>
      congrArg Subtype.val (mem_center_iff.1 hz ⟨l, hl⟩)
    have ht₁C : t₁ ∈ C := by rw [ht₁zc]; exact C.mul_mem hzC hcC
    have := hTC t₁ ht₁T ht₁C
    rw [this, orderOf_one] at ht₁2
    omega
  have hzbar : orderOf (zL : L ⧸ center L) = 2 := orderOf_mk_eq_two zL hzL2 hzcen
  set φ : MulAut (L ⧸ center L) := normalizerAction L ⟨s, hsN⟩ with hφdef
  have hφfix : ∀ q ∈ centralizer ({(zL : L ⧸ center L)} : Set (L ⧸ center L)),
      Odd (orderOf q) → φ q = q := by
    intro q hq hqodd
    obtain ⟨x, rfl, hxodd⟩ := exists_odd_lift hZ hqodd
    have hxz : Commute x zL :=
      commute_of_odd_of_commute_mk hZ hxodd (mem_centralizer_singleton_iff.1 hq)
    have hxz' : (x : G) * z = z * (x : G) := congrArg Subtype.val hxz.eq
    have hxc : (x : G) * c = c * (x : G) := mem_centralizer_iff.mp hcC x x.2
    have hxt : (x : G) * t₁ = t₁ * (x : G) := by
      rw [ht₁zc]
      calc (x : G) * (z * c) = (x * z) * c := by group
        _ = (z * x) * c := by rw [hxz']
        _ = z * (x * c) := by group
        _ = z * (c * x) := by rw [hxc]
        _ = z * c * x := by group
    have hxt' : (x : G)⁻¹ * t₁ = t₁ * (x : G)⁻¹ := by
      calc (x : G)⁻¹ * t₁ = (x : G)⁻¹ * (t₁ * x) * (x : G)⁻¹ := by group
        _ = (x : G)⁻¹ * (x * t₁) * (x : G)⁻¹ := by rw [hxt]
        _ = t₁ * (x : G)⁻¹ := by group
    have hxnorm : (x : G) ∈ normalizer (T : Set G) := by
      refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hnorm _ hxt y hy, fun hy => ?_⟩
      have := hnorm _ hxt' _ hy
      simpa [mul_assoc] using this
    have hxodd' : Odd (orderOf (x : G)) := by rwa [Subgroup.orderOf_coe]
    have hcomm : (x : G) * s = s * (x : G) :=
      haveI := hTcyc
      commute_of_odd_of_mem_normalizer hT hxodd' hxnorm s hsT
    have hxs : (x : G) = s * (x : G) * s⁻¹ := by
      calc (x : G) = (x : G) * s * s⁻¹ := by group
        _ = s * (x : G) * s⁻¹ := by rw [hcomm]
    exact normalizerAction_apply ⟨s, hsN⟩ x x hxs
  have hφ4 : φ ^ 4 = 1 := hOF _ hzbar φ hφfix
  have hs4C : s ^ 4 ∈ C := by
    have h4 : normalizerAction L ((⟨s, hsN⟩ : normalizer (L : Set G)) ^ 4) = 1 := by
      rw [map_pow]; exact hφ4
    simpa using (normalizerAction_eq_one_iff hL _).1 h4
  have hs4 : s ^ 4 = 1 := hTC _ (Subgroup.pow_mem T hsT 4) hs4C
  have hdvd : 2 ^ n ∣ 4 := hs ▸ orderOf_dvd_of_pow_eq_one hs4
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

end CFSG.EvenSporadicStandard.TwoHS

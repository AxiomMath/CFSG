module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

theorem exists_commutator_of_isPlaneDiagonal_odd {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hodd : p ≠ 2) {D : Subgroup X} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) {z g : X} (hz : z ∈ D) (hz1 : z ≠ 1)
    (hg : IsPlaneDiagonal p D z g) :
    ∀ d ∈ D, ∃ d' ∈ D, d = d'⁻¹ * g * d' * g⁻¹ := by
  obtain ⟨hgN, -, a, b, hab, hord, hga, hgd⟩ := hg
  have hconj : ∀ x ∈ D, g * x * g⁻¹ ∈ D := fun x hx => (mem_normalizer_iff.1 hgN x).1 hx
  have hp : p.Prime := Fact.out
  have hzp : z ^ p = 1 := hD.2 z hz
  have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
  have hab' : (a : ZMod p) * (b : ZMod p) = 1 := by
    have := congrArg (Nat.cast : ℕ → ZMod p) hab
    rwa [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_one] at this
  have ha1 : (a : ZMod p) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    have := hp.two_le
    omega
  have hb1 : (b : ZMod p) ≠ 1 := by
    intro h
    apply ha1
    rw [h, mul_one] at hab'
    exact hab'
  have hfix : ∀ w ∈ D, g * w * g⁻¹ = w → w = 1 := by
    intro w hw hgw
    by_contra hw1
    have hwp : w ^ p = 1 := hD.2 w hw
    have hwo : orderOf w = p := orderOf_eq_prime hwp hw1
    by_cases hwz : w ∈ Subgroup.zpowers z
    ·
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwz
      rw [← conj_zpow, hga, ← zpow_natCast, ← zpow_mul] at hgw
      have hmod : (a : ℤ) * k ≡ k [ZMOD (orderOf z : ℤ)] := zpow_eq_zpow_iff_modEq.1 hgw
      rw [hzord] at hmod
      have hZ : (((k : ℤ) - (a : ℤ) * k : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hmod.dvd
      push_cast at hZ
      have hmul : (1 - (a : ZMod p)) * (k : ZMod p) = 0 := by linear_combination hZ
      rcases mul_eq_zero.1 hmul with h | h
      · exact ha1 (sub_eq_zero.1 h).symm
      · have hpk : ((orderOf z : ℕ) : ℤ) ∣ k := by
          rw [hzord]
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd k p).1 h
        exact hw1 (orderOf_dvd_iff_zpow_eq_one.1 hpk)
    ·
      obtain ⟨c, hc⟩ := hgd w hw hwz
      have hwc : w = w ^ b * z ^ c := hgw.symm.trans hc
      have hu_w : z ^ c ∈ Subgroup.zpowers w := by
        have hzc : z ^ c = (w ^ b)⁻¹ * w := by
          calc z ^ c = (w ^ b)⁻¹ * (w ^ b * z ^ c) := by group
            _ = (w ^ b)⁻¹ * w := by rw [← hwc]
        rw [hzc]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
          (Subgroup.mem_zpowers w) b)) (Subgroup.mem_zpowers w)
      have hu_z : z ^ c ∈ Subgroup.zpowers z := Subgroup.pow_mem _ (Subgroup.mem_zpowers z) c
      have hu1 : z ^ c = 1 := by
        by_contra hne
        have hup : (z ^ c) ^ p = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hzp, one_pow]
        have hou : orderOf (z ^ c) = p := orderOf_eq_prime hup hne
        have h1 : Subgroup.zpowers (z ^ c) = Subgroup.zpowers z :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_z) (by
            rw [Nat.card_zpowers, Nat.card_zpowers, hzord, hou])
        have h2 : Subgroup.zpowers (z ^ c) = Subgroup.zpowers w :=
          Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hu_w) (by
            rw [Nat.card_zpowers, Nat.card_zpowers, hwo, hou])
        apply hwz
        have hww : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
        rw [← h2, h1] at hww
        exact hww
      rw [hu1, mul_one] at hwc
      have hwb : w ^ b = w ^ 1 := by rw [pow_one]; exact hwc.symm
      have hmodb : b ≡ 1 [MOD orderOf w] := pow_eq_pow_iff_modEq.1 hwb
      rw [hwo] at hmodb
      have hb : (b : ZMod p) = ((1 : ℕ) : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).2 hmodb
      exact hb1 (by simpa using hb)
  let ψ : D → D := fun x =>
    ⟨(x : X)⁻¹ * (g * (x : X) * g⁻¹), D.mul_mem (D.inv_mem x.2) (hconj _ x.2)⟩
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : (x : X)⁻¹ * (g * (x : X) * g⁻¹) = (y : X)⁻¹ * (g * (y : X) * g⁻¹) :=
      congrArg Subtype.val hxy
    have h2 : g * (y : X) * g⁻¹ = (y : X) * (x : X)⁻¹ * (g * (x : X) * g⁻¹) := by
      calc g * (y : X) * g⁻¹ = (y : X) * ((y : X)⁻¹ * (g * (y : X) * g⁻¹)) := by group
        _ = (y : X) * ((x : X)⁻¹ * (g * (x : X) * g⁻¹)) := by rw [h1]
        _ = (y : X) * (x : X)⁻¹ * (g * (x : X) * g⁻¹) := by group
    have hw : g * ((y : X) * (x : X)⁻¹) * g⁻¹ = (y : X) * (x : X)⁻¹ := by
      calc g * ((y : X) * (x : X)⁻¹) * g⁻¹
          = (g * (y : X) * g⁻¹) * (g * (x : X) * g⁻¹)⁻¹ := by group
        _ = (y : X) * (x : X)⁻¹ * (g * (x : X) * g⁻¹) * (g * (x : X) * g⁻¹)⁻¹ := by rw [h2]
        _ = (y : X) * (x : X)⁻¹ := by group
    have hyx : (y : X) * (x : X)⁻¹ = 1 :=
      hfix _ (D.mul_mem y.2 (D.inv_mem x.2)) hw
    exact Subtype.ext (mul_inv_eq_one.1 hyx).symm
  intro d hd
  obtain ⟨⟨d', hd'⟩, hdd⟩ := Finite.surjective_of_injective hψ ⟨d, hd⟩
  have h3 : (d' : X)⁻¹ * (g * d' * g⁻¹) = d := congrArg Subtype.val hdd
  refine ⟨d', hd', ?_⟩
  calc d = (d' : X)⁻¹ * (g * d' * g⁻¹) := h3.symm
    _ = d'⁻¹ * g * d' * g⁻¹ := by group

theorem i294_conjNormal_injective {Y : Type} [Group Y] {L : Subgroup Y}
    [L.Normal] (hC : Subgroup.centralizer (L : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal : Y →* MulAut L) := by
  intro g g' hgg
  have hcen : g'⁻¹ * g ∈ Subgroup.centralizer (L : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := congrArg (fun φ : MulAut L => ((φ ⟨l, hl⟩ : L) : Y)) hgg
    simp only [MulAut.conjNormal_apply] at h
    calc l * (g'⁻¹ * g) = g'⁻¹ * (g' * l * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * l * g⁻¹) * g := by rw [h]
      _ = g'⁻¹ * g * l := by group
  rw [hC, Subgroup.mem_bot] at hcen
  calc g = g' * (g'⁻¹ * g) := by group
    _ = g' := by rw [hcen, mul_one]

theorem le_of_autCommInner {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]
    (hC : centralizer (L : Set Y) = ⊥) (hO : AutCommInner ↥L) {p : ℕ} [Fact p.Prime]
    (hodd : p ≠ 2) {D : Subgroup Y} (hD : IsElemAbelian p D) (hcard : Nat.card D = p ^ 2)
    {z g : Y} (hz : z ∈ D) (hz1 : z ≠ 1) (hg : IsPlaneDiagonal p D z g) : D ≤ L := by
  intro d hd
  obtain ⟨d', -, hdd⟩ := exists_commutator_of_isPlaneDiagonal_odd hodd hD hcard hz hz1 hg d hd
  have hcomm : MulAut.conjNormal (H := L) d =
      MulAut.conjNormal (H := L) (d'⁻¹) * MulAut.conjNormal (H := L) g *
        (MulAut.conjNormal (H := L) (d'⁻¹))⁻¹ * (MulAut.conjNormal (H := L) g)⁻¹ := by
    rw [hdd]
    simp only [map_mul, map_inv, inv_inv]
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.1
    (hO (MulAut.conjNormal (H := L) (d'⁻¹)) (MulAut.conjNormal (H := L) g))
  have h2 : MulAut.conjNormal (H := L) (l : Y) = MulAut.conjNormal (H := L) d := by
    rw [MulAut.conjNormal_val]
    exact hl.trans hcomm.symm
  have h3 : (l : Y) = d := i294_conjNormal_injective hC h2
  rw [← h3]
  exact l.2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

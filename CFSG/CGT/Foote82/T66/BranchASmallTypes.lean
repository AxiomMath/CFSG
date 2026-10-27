module

public import CFSG.CGT.Foote82.T66.BranchASmallKey

public section

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L : Subgroup (GLV V)} {z : GLV V}

namespace Hyp

variable (hc : Hyp G L z)
include hc

theorem finrank_tvComm_le_of_TI (hTI : BASTIFails)
    (htype : IsAltNaturalModule L 6 ∨ IsOmegaMinusModule L 2) {g : GLV V} (hg : g ∈ G)
    (hne : g * z * g⁻¹ ≠ z) (hcomm : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) :
    Module.finrank (ZMod 2) ↥(tvComm L (g * z * g⁻¹)) ≤
      Module.finrank (ZMod 2) ↥(tildeVBot L) + 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hN, -⟩ := hc.mem_normalizer_of_Dz hg hne hcomm
  obtain ⟨l, hl, hne', hcomm', hinf⟩ := hTI V L htype hc.faithful hc.irrTilde _ hN
    (hc.orderOf_conj_z g) (fun l hl => hc.oddTransp_conj hg l hl) hlt
  have hlg : l * g ∈ G := G.mul_mem (hc.L_le hl) hg
  have hconj : l * (g * z * g⁻¹) * l⁻¹ = (l * g) * z * (l * g)⁻¹ := by group
  have hinf' : commSpace (Subgroup.zpowers (g * z * g⁻¹)) ⊤ ⊓
      commSpace (Subgroup.zpowers ((l * g) * z * (l * g)⁻¹)) ⊤ ≠ ⊥ := by
    intro h0
    apply hinf
    rw [eq_bot_iff] at h0 ⊢
    refine le_trans (inf_le_inf (commSpace_mono le_rfl le_top) ?_) h0
    rw [hconj]
    exact commSpace_mono le_rfl le_top
  have heq := hc.eq_of_commSpace_inf hg hlg hinf'
  have hu : l * (g * z * g⁻¹) * l⁻¹ ∈ Subgroup.centralizer (conjSg g L : Set (GLV V)) := by
    rw [heq, hconj]
    exact hc.conj_z_mem_centralizer _
  have huG : l * (g * z * g⁻¹) * l⁻¹ ∈ G := by
    rw [hconj]
    exact hc.conj_z_mem hlg
  have hu2 : orderOf (l * (g * z * g⁻¹) * l⁻¹) = 2 := by
    rw [orderOf_conj, hc.orderOf_conj_z]
  exact hne' (hc.eq_conj_z_of_commute hg huG hu hu2 hcomm'.symm)

theorem finrank_tvComm_le_of_eight (h15 : BASOmegaEight) (htype : IsOmegaMinusModule L 3)
    {g : GLV V} (hg : g ∈ G) (hne : g * z * g⁻¹ ≠ z)
    (hcomm : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)) :
    Module.finrank (ZMod 2) ↥(tvComm L (g * z * g⁻¹)) ≤
      Module.finrank (ZMod 2) ↥(tildeVBot L) + 1 := by
  obtain ⟨hN, -⟩ := hc.mem_normalizer_of_Dz hg hne hcomm
  exact h15 V L htype hc.faithful hc.irrTilde _ hN (hc.orderOf_conj_z g)
    (fun l hl => hc.oddTransp_conj hg l hl)

theorem eq_one_of_mem_center {x : GLV V} (hxL : x ∈ L)
    (hxc : ∀ l ∈ L, l * x = x * l) (hx2 : orderOf x = 2) : x = 1 := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx2, pow_one]
  have h := (lemma61 hc.perfect hc.irrTilde hxc hp).2
  refine hc.faithful x hxL fun w hw => ?_
  have hw' : x w = w := h hw x (Subgroup.mem_zpowers x)
  rw [hw', sub_self]
  exact (fixedSpace L).zero_mem

theorem false_of_A6Z3 (h7 : BASThreeA6) (h6 : BASA6NoSix) (htype : IsA6Z3Module L) : False := by
  obtain ⟨⟨α, hαs⟩, hdim⟩ := htype
  have hker : α.ker ≤ Subgroup.center ↥L := by
    have hnorm : ∀ a ∈ L, ∀ n ∈ α.ker.map L.subtype, a * n * a⁻¹ ∈ α.ker.map L.subtype := by
      rintro a ha _ ⟨n, hn, rfl⟩
      refine ⟨⟨a, ha⟩ * n * ⟨a, ha⟩⁻¹, ?_, rfl⟩
      have hn' : α n = 1 := hn
      show α (⟨a, ha⟩ * n * ⟨a, ha⟩⁻¹) = 1
      rw [map_mul, map_mul, hn', mul_one, map_inv, mul_inv_cancel]
    rcases CFSG.LargeExtraspecial.S5.commute_or_eq_of_normalized hc.quasisimple
        (Subgroup.map_subtype_le _) hnorm with h | h
    · intro n hn
      rw [Subgroup.mem_center_iff]
      intro a
      exact Subtype.ext (h n ⟨n, hn, rfl⟩ a a.2).symm
    · exfalso
      have hall : ∀ y : ↥L, α y = 1 := by
        intro y
        have : (y : GLV V) ∈ α.ker.map L.subtype := h.symm ▸ y.2
        obtain ⟨y', hy', hyy⟩ := this
        have : y' = y := Subtype.ext hyy
        rw [← this]
        exact hy'
      have hmem : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 0 2 ∈ alternatingGroup (Fin 6) :=
        Equiv.Perm.mem_alternatingGroup.2 (by
          rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]
          decide)
      obtain ⟨y, hy⟩ := hαs ⟨Equiv.swap 0 1 * Equiv.swap 0 2, hmem⟩
      rw [hall] at hy
      have hne1 : (1 : Equiv.Perm (Fin 6)) ≠ Equiv.swap 0 1 * Equiv.swap 0 2 := by decide
      exact hne1 (congrArg Subtype.val hy)
  by_cases hbot : α.ker = ⊥
  ·
    have hinj : Function.Injective α := (MonoidHom.ker_eq_bot_iff α).1 hbot
    exact h6 V L ⟨MulEquiv.ofBijective α ⟨hinj, hαs⟩⟩ hc.irrTilde hdim
  ·
    have hodd : Odd (Nat.card α.ker) := by
      by_contra heven
      rw [Nat.not_odd_iff_even] at heven
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 heven)
      have hxc : ∀ l ∈ L, l * (x : GLV V) = (x : GLV V) * l := by
        intro l hl
        have := Subgroup.mem_center_iff.1 (hker x.2) ⟨l, hl⟩
        exact (congrArg Subtype.val this)
      have hx2 : orderOf ((x : ↥L) : GLV V) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
      have h1 := hc.eq_one_of_mem_center (x : ↥L).2 hxc hx2
      rw [h1, orderOf_one] at hx2
      exact absurd hx2 (by norm_num)
    obtain ⟨g, hg, hne, hcomm⟩ := hc.exists_Dz
    obtain ⟨hN, hC⟩ := hc.mem_normalizer_of_Dz hg hne hcomm
    set d := g * z * g⁻¹ with hd
    have hd2 : d * d = 1 := hc.conj_z_mul_self g
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd2
    have hmap : L.map (MulAut.conj d).toMonoidHom = L :=
      (mem_normalizer_iff_conjSg_eq.1 hN)
    let δ : ↥L ≃* ↥L :=
      (L.equivMapOfInjective _ (MulAut.conj d).injective).trans (MulEquiv.subgroupCongr hmap)
    have hδ : ∀ y : ↥L, ((δ y : ↥L) : GLV V) = d * y * d⁻¹ := fun y => rfl
    have hδ2 : ∀ y, δ (δ y) = y := by
      intro y
      apply Subtype.ext
      rw [hδ, hδ]
      calc d * (d * (y : GLV V) * d⁻¹) * d⁻¹ = (d * d) * y * (d * d)⁻¹ := by group
        _ = y := by rw [hd2, one_mul, inv_one, mul_one]
    have hδ1 : ∃ y, δ y ≠ y := by
      by_contra hall
      push Not at hall
      apply hC
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have := congrArg Subtype.val (hall ⟨l, hl⟩)
      rw [hδ] at this
      calc l * d = (d * l * d⁻¹) * d := by rw [this]
        _ = d * l := by group
    have hperfL : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := hc.quasisimple.1
    obtain ⟨y, hy2, hyeven⟩ := h7 ↥L α hαs hperfL hker hodd hbot δ hδ2 hδ1
    have hval : ((δ y * y⁻¹ : ↥L) : GLV V) = d * ((y : GLV V) * d * (y : GLV V)⁻¹) := by
      rw [Subgroup.coe_mul, hδ, Subgroup.coe_inv, hdinv]
      group
    have horder : orderOf (δ y * y⁻¹) = orderOf (d * ((y : GLV V) * d * (y : GLV V)⁻¹)) := by
      rw [← hval, Subgroup.orderOf_coe]
    rcases hc.oddTransp_conj hg y y.2 with h1 | h1
    · rw [← horder] at h1
      omega
    · rw [← horder] at h1
      exact (Nat.not_even_iff_odd.2 h1) hyeven

end Hyp

end CFSG.CGT.Foote82.BAS

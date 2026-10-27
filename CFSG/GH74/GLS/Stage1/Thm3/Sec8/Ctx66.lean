module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx65
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.GrpA

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm3.Sec7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

namespace Fused8

theorem K₁₂_le_C (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) : K₁ ⊔ K₂ ≤ Cz z :=
  sup_le (hf.m4 hII).K₁_le (hf.m4 hII).K₂_le

theorem C_mem_normalizer_N (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) {c : G}
    (hc : c ∈ Cz z) : c ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  have hM := hf.m4 hII
  rw [mem_normalizer_iff]
  intro k
  refine ⟨fun hk => hM.C_norm_K hc hk, fun hk => ?_⟩
  have := hM.C_norm_K ((Cz z).inv_mem hc) hk
  simpa [mul_assoc] using this

theorem L_norm (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    ∀ c ∈ Cz z, ∀ l ∈ K₁ ⊔ K₂ ⊔ Oz z, c * l * c⁻¹ ∈ K₁ ⊔ K₂ ⊔ Oz z := by
  intro c hc l hl
  have hM := hf.m4 hII
  obtain ⟨n, hn, o, ho, rfl⟩ :=
    Basic.mem_sup_of_le_normalizer' (le_normalizer_Oz (hf.K₁₂_le_C hII)) hl
  have e : c * (n * o) * c⁻¹ = (c * n * c⁻¹) * (c * o * c⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (hM.C_norm_K hc hn)) (Subgroup.mem_sup_right (Oz_conj hc ho))

theorem S_inf_L (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    S ⊓ (K₁ ⊔ K₂ ⊔ Oz z) = Pz S z := by
  have hM := hf.m4 hII
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, N = K₁ ⊔ K₂ := ⟨_, rfl⟩
  have hNC : N ≤ Cz z := hN ▸ hf.K₁₂_le_C hII
  have hOnorm : Oz z ≤ normalizer (N : Set G) := fun o ho =>
    hN ▸ hf.C_mem_normalizer_N hII (TwoThin.pPrimeCoreOf_le (Cz z) ho)
  have hPz : Pz S z = S ⊓ N := by rw [Pz_eq hf.std, hN]; rfl
  rw [hPz, ← hN]
  apply le_antisymm
  · obtain ⟨L, hL⟩ : ∃ L : Subgroup G, L = N ⊔ Oz z := ⟨_, rfl⟩
    rw [← hL]
    obtain ⟨P', hP'⟩ : ∃ P' : Subgroup G, P' = S ⊓ L := ⟨_, rfl⟩
    rw [← hP']
    have hNL : N ≤ L := hL ▸ le_sup_left
    have hP'L : P' ≤ L := hP' ▸ inf_le_right
    have hP'S : P' ≤ S := hP' ▸ inf_le_left
    have hP'C : P' ≤ Cz z := hP'S.trans (hf.S_le_C hII)
    have hP'norm : P' ≤ normalizer (N : Set G) := fun x hx => hN ▸ hf.C_mem_normalizer_N hII (hP'C hx)
    have hP'2 : IsPGroup 2 ↥P' := (hf.S_pgroup hII).to_le hP'S
    have h1 := Basic.card_sup_mul_card_inf' (A := N) (B := Oz z) hOnorm
    rw [← hL] at h1
    have hr := Basic.card_mul_relIndex_of_le hNL
    have hposN : 0 < Nat.card ↥N := Nat.card_pos
    have hodd : Odd (N.relIndex L) := by
      have : N.relIndex L * Nat.card ↥(N ⊓ Oz z) = Nat.card ↥(Oz z) := by
        apply Nat.eq_of_mul_eq_mul_left hposN
        calc Nat.card ↥N * (N.relIndex L * Nat.card ↥(N ⊓ Oz z))
            = (Nat.card ↥N * N.relIndex L) * Nat.card ↥(N ⊓ Oz z) := by ring
          _ = Nat.card ↥L * Nat.card ↥(N ⊓ Oz z) := by rw [hr]
          _ = Nat.card ↥N * Nat.card ↥(Oz z) := h1
      exact Odd.of_dvd_nat card_Oz_odd (Dvd.intro _ this)
    have hNP : N ⊔ P' ≤ L := sup_le hNL hP'L
    have htower := Subgroup.relIndex_mul_relIndex N (N ⊔ P') L le_sup_left hNP
    have hodd' : Odd (N.relIndex (N ⊔ P')) :=
      Odd.of_dvd_nat hodd (Dvd.intro _ htower)
    have h2 := Basic.card_sup_mul_card_inf' (A := N) (B := P') hP'norm
    have hr' := Basic.card_mul_relIndex_of_le (le_sup_left : N ≤ N ⊔ P')
    have h3 : N.relIndex (N ⊔ P') * Nat.card ↥(N ⊓ P') = Nat.card ↥P' := by
      apply Nat.eq_of_mul_eq_mul_left hposN
      calc Nat.card ↥N * (N.relIndex (N ⊔ P') * Nat.card ↥(N ⊓ P'))
          = (Nat.card ↥N * N.relIndex (N ⊔ P')) * Nat.card ↥(N ⊓ P') := by ring
        _ = Nat.card ↥(N ⊔ P') * Nat.card ↥(N ⊓ P') := by rw [hr']
        _ = Nat.card ↥N * Nat.card ↥P' := h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP'2
    have hdvd : N.relIndex (N ⊔ P') ∣ 2 ^ k := by
      rw [← hk, ← h3]; exact Dvd.intro _ rfl
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hi0 : i = 0 := by
      by_contra hne
      rw [hi] at hodd'
      exact (Nat.not_even_iff_odd.2 hodd') (even_iff_two_dvd.2 (dvd_pow_self 2 hne))
    rw [hi, hi0, pow_zero, one_mul] at h3
    have hPN : N ⊓ P' = P' :=
      Subgroup.eq_of_le_of_card_ge (inf_le_right : N ⊓ P' ≤ P') (by omega)
    intro x hx
    have : x ∈ N ⊓ P' := by rw [hPN]; exact hx
    exact ⟨hP'S hx, this.1⟩
  · exact inf_le_inf le_rfl le_sup_left

theorem map_L (hII : II4_4_4_center) (hf : Fused8 G z S K₁ K₂) :
    ((K₁ ⊔ K₂ ⊔ Oz z).subgroupOf (Cz z)).map (piC z) = imgBar z K₁ ⊔ imgBar z K₂ := by
  have hM := hf.m4 hII
  have hK₁C : K₁ ≤ Cz z := hM.K₁_le
  have hK₂C : K₂ ≤ Cz z := hM.K₂_le
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ K₁ ⊔ K₂ ⊔ Oz z := hy
    obtain ⟨n, hn, o, ho, hno⟩ :=
      Basic.mem_sup_of_le_normalizer' (le_normalizer_Oz (hf.K₁₂_le_C hII)) hy'
    have hnC : n ∈ Cz z := hf.K₁₂_le_C hII hn
    have hoC : o ∈ Cz z := TwoThin.pPrimeCoreOf_le (Cz z) ho
    have e : y = ⟨n, hnC⟩ * ⟨o, hoC⟩ := Subtype.ext hno
    rw [e, map_mul]
    have h1 : piC z ⟨o, hoC⟩ = 1 := (hatMk_eq_one_iff (Cz z) ⟨o, hoC⟩).2 ho
    rw [h1, mul_one]
    have hT : (K₁ ⊔ K₂).subgroupOf (Cz z) ≤ (imgBar z K₁ ⊔ imgBar z K₂).comap (piC z) := by
      rw [Subgroup.subgroupOf_sup hK₁C hK₂C]
      refine sup_le (fun k hk => ?_) (fun k hk => ?_)
      · exact Subgroup.mem_sup_left (piC_mem_imgBar hK₁C hk)
      · exact Subgroup.mem_sup_right (piC_mem_imgBar hK₂C hk)
    exact hT (show (⟨n, hnC⟩ : ↥(Cz z)) ∈ (K₁ ⊔ K₂).subgroupOf (Cz z) from hn)
  · refine sup_le ?_ ?_
    · rintro x hx
      obtain ⟨k, hk, rfl⟩ := (mem_imgBar hK₁C).1 hx
      exact ⟨⟨k, hK₁C hk⟩, show k ∈ K₁ ⊔ K₂ ⊔ Oz z from
        Subgroup.mem_sup_left (Subgroup.mem_sup_left hk), rfl⟩
    · rintro x hx
      obtain ⟨k, hk, rfl⟩ := (mem_imgBar hK₂C).1 hx
      exact ⟨⟨k, hK₂C hk⟩, show k ∈ K₁ ⊔ K₂ ⊔ Oz z from
        Subgroup.mem_sup_left (Subgroup.mem_sup_right hk), rfl⟩

end Fused8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8

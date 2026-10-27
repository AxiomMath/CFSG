module

public import CFSG.GH74.GLS.Bg.TwoGroups.A88Model
public import CFSG.GH74.GLS.Bg.TwoGroups.Vocab

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

open Subgroup A44

theorem O2_le {G : Type*} [Group G] (A : Subgroup G) : O2 A ≤ A := by
  apply iSup_le
  rintro ⟨N, hN, -, -⟩
  exact hN

theorem K0_normal_mem : ∀ g : G96, ∀ x ∈ subOfList K0list K0_closed, g * x * g⁻¹ ∈ subOfList K0list K0_closed :=
  fun g x hx => K0_conj g.1 g.2 x.1 hx

theorem fix4 : ∀ a b c d : ZMod 8, ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) a = 1 →
    ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) b = 0 →
    ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) c = 0 →
    ZMod.castHom (by norm_num : 4 ∣ 8) (ZMod 4) d = 1 →
    ∀ v : ZMod 8 × ZMod 8, v + v + v + v = 0 → (M8.mk a b c d).act v = v := by decide +kernel

theorem iv2_2_2 :
    ∀ (H : Type) [CommGroup H], Nonempty (H ≃* Z8Z8) → ∀ A : Subgroup (MulAut H),
      ∀ b ∈ O2 (O2res A), b * b = 1 → ∀ h : H, h ^ 4 = 1 → b h = h := by
  intro H _ ⟨e⟩ A b hb hb2 h hh
  let ρ : MulAut H →* G96 := rho8.comp (MulAut.congr e).toMonoidHom
  let K0 : Subgroup G96 := subOfList K0list K0_closed
  have hK0n : ∀ g : G96, ∀ x ∈ K0, g * x * g⁻¹ ∈ K0 := K0_normal_mem
  have : K0.Normal := ⟨fun x hx g => hK0n g x hx⟩
  have hK0idx : K0.index = 8 := by
    have h1 := Subgroup.card_mul_index K0
    have hc : Nat.card K0 = 12 := by
      have e1 : {x : G96 // x ∈ K0} ≃ {x : G96 // x.1 ∈ K0list} :=
        (Equiv.refl G96).subtypeEquiv (p := fun x : G96 => x ∈ K0)
          (q := fun x : G96 => x.1 ∈ K0list) (fun x => Iff.rfl)
      rw [show Nat.card K0 = Nat.card {x : G96 // x ∈ K0} from rfl, Nat.card_congr e1,
        Nat.card_eq_fintype_card]
      exact card_K0
    have hG : Nat.card G96 = 96 := by rw [Nat.card_eq_fintype_card]; exact M4.card_G96
    rw [hc, hG] at h1
    omega
  let N : Subgroup (MulAut H) := K0.comap ρ ⊓ A
  have hNA : N ≤ A := inf_le_right
  have hnorm : A ≤ normalizer (N : Set (MulAut H)) := by
    intro a ha
    rw [mem_normalizer_iff]
    have fwd : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N := by
      intro a ha x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (mul_mem ha hx2) (inv_mem ha)⟩
      show ρ (a * x * a⁻¹) ∈ K0
      rw [map_mul, map_mul, map_inv]
      exact hK0n (ρ a) _ hx1
    intro x
    constructor
    · exact fun hx => fwd a ha x hx
    · intro hx
      have := fwd a⁻¹ (inv_mem ha) _ hx
      simpa [mul_assoc] using this
  have hidx : ∃ k : ℕ, N.relIndex A = 2 ^ k := by
    have h1 : N.relIndex A = (K0.comap ρ).relIndex A := Subgroup.inf_relIndex_right (K0.comap ρ) A
    have h2 : (K0.relIndex (A.map ρ)) ∣ 2 ^ 3 := by
      have := Subgroup.relIndex_dvd_index_of_normal K0 (A.map ρ)
      rw [hK0idx] at this
      exact this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact ⟨k, by rw [h1, Subgroup.relIndex_comap]; exact hk⟩
  have hle : O2res A ≤ N :=
    iInf_le (fun M : {M : Subgroup (MulAut H) // M ≤ A ∧ A ≤ normalizer (M : Set (MulAut H)) ∧
      ∃ k : ℕ, M.relIndex A = 2 ^ k} => M.1) ⟨N, hNA, hnorm, hidx⟩
  have hbN : b ∈ N := hle (O2_le _ hb)
  have hbK : ρ b ∈ K0 := (Subgroup.mem_inf.mp hbN).1
  have hρ2 : M4.mul (ρ b).1 (ρ b).1 = M4.one := by
    have : ρ b * ρ b = 1 := by rw [← map_mul, hb2, map_one]
    have := congrArg Subtype.val this
    simpa using this
  have hV : (ρ b).1 ∈ V4list := K0_sq_V _ hbK hρ2
  set x : M8 := toM8 (MulAut.congr e b) with hx
  have hxinv : x.IsInv := toM8_isInv _
  have hxsq : M8.mul x x = M8.one := by
    have : MulAut.congr e b * MulAut.congr e b = 1 := by
      rw [← map_mul, hb2, map_one]
    rw [← toM8_mul, this, toM8_one]
  have hred : M8.red x ∈ V4list := hV
  have hx1 : M8.red x = M4.one := lem22_check x.a x.b x.c x.d hxinv hxsq hred
  have hxmk : M8.mk x.a x.b x.c x.d = x := by cases x; rfl
  have hent := congrArg (fun m : M4 => (m.a, m.b, m.c, m.d)) hx1
  simp only [M8.red, M4.one, Prod.mk.injEq] at hent
  obtain ⟨ha, hb', hc, hd⟩ := hent
  have h4 : ∀ v : ZMod 8 × ZMod 8, v + v + v + v = 0 → x.act v = v := by
    intro v hv
    have := fix4 x.a x.b x.c x.d ha hb' hc hd v hv
    rwa [hxmk] at this
  have hw : Multiplicative.toAdd (e h) + Multiplicative.toAdd (e h) + Multiplicative.toAdd (e h) +
      Multiplicative.toAdd (e h) = 0 := by
    have h' : (e h) ^ 4 = 1 := by rw [← map_pow, hh, map_one]
    have h5 := congrArg Multiplicative.toAdd h'
    rw [toAdd_pow] at h5
    have h6 : (4 : ℕ) • Multiplicative.toAdd (e h) = Multiplicative.toAdd (e h) +
        Multiplicative.toAdd (e h) + Multiplicative.toAdd (e h) + Multiplicative.toAdd (e h) := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, succ_nsmul, three_nsmul]
      abel
    rw [← h6]
    exact h5
  apply e.injective
  apply Multiplicative.toAdd.injective
  have hconj : (MulAut.congr e b) (e h) = e (b h) := by simp [MulAut.congr_apply]
  have hphi := toAdd_phi8 (MulAut.congr e b) (Multiplicative.toAdd (e h))
  rw [ofAdd_toAdd, hconj, ← hx] at hphi
  rw [hphi, h4 _ hw]

end CFSG.GH74.GLS.Bg.TwoGroups

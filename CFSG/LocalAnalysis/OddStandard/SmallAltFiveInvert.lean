module

public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveLift
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveNonInversion
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveFusionValues
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveTransfer
public import CFSG.LocalAnalysis.OddStandard.SmallAltFivePhi

public section

namespace CFSG.OddStandard

open Subgroup Equiv CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}
  {S : Sylow 2 (centralizer (L : Set G))} {t : G} {e : L ≃* alternatingGroup (Fin 5)}

theorem Full.x_inverts (hf : Full L S t e) (Q : Sylow 2 (centralizer ({t} : Set G)))
    (hSQ : sg L S ≤ qg t Q) {x : G} (hx : x ∈ qg t Q) (hxA : x ∉ (qg t Q ⊓ L) ⊔ sg L S)
    (hx2 : x * x = 1) : ∀ u ∈ sg L S, x * u * x⁻¹ = u⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect G := ⟨hf.perfect⟩
  obtain ⟨s, a, hgen, hord, ha1, hcard, ht⟩ := exists_generator_sg hf.sector
  have ha2 : 2 ≤ a := by
    by_contra h
    have h1 : a = 1 := by omega
    have h4 := hf.four_le
    rw [hcard, h1] at h4
    norm_num at h4
  have hd := hf.qdata Q hSQ hx hxA hx2 hgen hord ha2
  have hsS : s ∈ sg L S := hgen ▸ mem_zpowers s
  have hxH : x ∈ centralizer ({t} : Set G) := qg_le_H t Q hx
  suffices hs : x * s * x⁻¹ = s⁻¹ by
    intro u hu
    rw [hgen] at hu
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
    rw [← conj_zpow, hs, inv_zpow]
  by_contra hnot
  have hNt := hd.normalizer_fixes_t hnot ht
  rw [hf.group_eq Q hSQ hx hxA] at hNt
  have hNle : normalizer ((qg t Q : Subgroup G) : Set G) ≤ centralizer ({t} : Set G) :=
    fun n hn => mem_centralizer_singleton_iff.mpr (by
      have h := hNt n hn
      calc n * t = (n * t * n⁻¹) * n := by group
        _ = t * n := by rw [h])
  have hQG : Nat.card (qg t Q) = 2 ^ (Nat.card G).factorization 2 :=
    card_eq_of_normalizer_le (qg_le_H t Q) (card_qg t Q) hNle
  let Qsyl : Sylow 2 G := Sylow.ofCard (qg t Q) hQG
  have htcent : ∀ q ∈ qg t Q, q * t = t * q := fun q hq =>
    mem_centralizer_singleton_iff.mp (qg_le_H t Q hq)
  have hiso : ∀ g : G, g⁻¹ * t * g ∈ QData.group (qg t Q ⊓ L) (sg L S) x →
      (∀ q ∈ QData.group (qg t Q ⊓ L) (sg L S) x, q * (g⁻¹ * t * g) = (g⁻¹ * t * g) * q) →
      g⁻¹ * t * g = t := by
    intro g _ hcent
    rw [hf.group_eq Q hSQ hx hxA] at hcent
    obtain ⟨n, hn, hnt⟩ := exists_mem_normalizer_conj Qsyl (fun u hu => htcent u hu)
      (fun u hu => hcent u hu) (g := g) rfl
    have hnt' : n⁻¹ * t * n = t := by
      have := hNt n⁻¹ (inv_mem hn)
      rwa [inv_inv] at this
    rw [← hnt, hnt']
  have hUH : L ⊔ zpowers x ≤ centralizer ({t} : Set G) :=
    sup_le hf.L_le_H (zpowers_le.mpr hxH)
  have hdec : ∀ h ∈ centralizer ({t} : Set G), ∃ k ∈ oddKer L ⊓ centralizer ({t} : Set G),
      ∃ b ∈ sg L S, ∃ u ∈ L ⊔ zpowers x, h = k * b * u := by
    intro h hh
    obtain ⟨u, hu, hρu⟩ := hf.exists_U_rhoAt_eq Q hSQ hx hxA hx2 (hf.rhoAt h)
    have huH : u ∈ centralizer ({t} : Set G) := hUH hu
    have hhu : h * u⁻¹ ∈ centralizer ({t} : Set G) :=
      Subgroup.mul_mem _ hh (Subgroup.inv_mem _ huH)
    have hr : h * u⁻¹ ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := by
      refine ⟨(hf.rhoAt_eq_one_iff hhu).1 ?_, hhu⟩
      rw [hf.rhoAt_mul hh (Subgroup.inv_mem _ huH), hf.rhoAt_inv huH, hρu]
      simp
    obtain ⟨k, hk, b, hb, hkb⟩ := hf.R_decomp hr
    exact ⟨k, hk, b, hb, u, hu, by rw [mul_assoc, ← mul_assoc k, ← hkb]; group⟩
  have huniq : ∀ k ∈ oddKer L ⊓ centralizer ({t} : Set G), ∀ b ∈ sg L S, ∀ u ∈ L ⊔ zpowers x,
      k * b * u = 1 → b = 1 := by
    intro k hk b hb u hu h1
    have huH : u ∈ centralizer ({t} : Set G) := hUH hu
    have hbH : b ∈ centralizer ({t} : Set G) := sg_le_centralizer_t hf.sector hb
    have hkρ : hf.rhoAt k = 1 :=
      (hf.rhoAt_eq_one_iff hk.2).2 (oddKer_le_centralizer hk.1)
    have hu1 : u = 1 := by
      refine hf.eq_one_of_rhoAt_eq_one_of_mem_U Q hSQ hx hxA hx2 hu ?_
      have := congrArg hf.rhoAt h1
      rw [hf.rhoAt_mul (Subgroup.mul_mem _ hk.2 hbH) huH, hf.rhoAt_mul hk.2 hbH, hkρ,
        hf.rhoAt_of_mem_sg hb, hf.rhoAt_one] at this
      simpa using this
    rw [hu1, mul_one] at h1
    have hb' : b = k⁻¹ := eq_inv_of_mul_eq_one_right h1
    have hb'' : b ∈ (oddKer L ⊓ centralizer ({t} : Set G)) ⊓ sg L S :=
      ⟨hb' ▸ Subgroup.inv_mem _ hk, hb⟩
    rw [hf.Kt_inf_sg, mem_bot] at hb''
    exact hb''
  obtain ⟨φ, hφKt, hφU, hφs⟩ := exists_parity_character
    (X := centralizer ({t} : Set G)) (Kt := oddKer L ⊓ centralizer ({t} : Set G))
    (U := L ⊔ zpowers x) (Sg := sg L S) (s := s) (a := a) inf_le_right hUH
    (sg_le_centralizer_t hf.sector) hord ha1 hgen (fun h hh k hk => hf.Kt_normalized hh hk)
    (fun u hu => hf.U_normalizes_sg Q hSQ hx hx2 hu hsS) hdec huniq
  have hφP : ∀ y : centralizer ({t} : Set G), (y : G) ∈ qg t Q ⊓ L → φ y = 1 := fun y hy =>
    hφU y (mem_sup_left hy.2)
  have hφx : ∀ y : centralizer ({t} : Set G), (y : G) = x → φ y = 1 := fun y hy =>
    hφU y (by rw [hy]; exact mem_sup_right (mem_zpowers x))
  let ψ : qg t Q →* Multiplicative (ZMod 2) := φ.comp (Subgroup.inclusion (qg_le_H t Q))
  refine transfer_fusion_contradiction (Q := qg t Q) (s := s) (a := a) ?_ (hSQ hsS) hord ψ ?_
  · exact Qsyl.not_dvd_index
  · intro g b hb hy
    have hyH := qg_le_H t Q hy
    exact hd.fusion_values hnot ht hiso φ hφP hφx hφs g b hb
      ((hf.group_eq Q hSQ hx hxA).symm ▸ hy) hyH

end CFSG.OddStandard

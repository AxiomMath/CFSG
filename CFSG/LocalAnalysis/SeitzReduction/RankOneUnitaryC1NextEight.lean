module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem false_of_card_range_eq_168 (hf : f = 3) (h168 : Nat.card H.perm.range = 168)
    (hs : IsSimpleGroup H.perm.range) : False := by
  classical
  obtain ⟨E, _, _, _, σ, hEcard, hσ, -, u, w, hc, hA⟩ :=
    H.stage.start.exists_rootCoords_of_card_sylow H.stage.card_sylow
  have hA₁T : szA₁ (szT₁ L T) ≤ szT₁ L T := szA₁_le _
  have hsq_eq : ∀ y ∈ szT₁ L T, ∀ y' ∈ szT₁ L T, u y = u y' → y ^ 2 = y' ^ 2 := by
    intro y hy y' hy' huy
    have hz : y⁻¹ * y' ∈ szA₁ (szT₁ L T) :=
      (hA _ (mul_mem (inv_mem hy) hy')).mpr (by rw [hc.u_mul_inv hy hy', huy, sub_self])
    have hzc : y * (y⁻¹ * y') = (y⁻¹ * y') * y :=
      mem_centralizer_iff.mp (mem_szA₁.mp hz).2 y hy
    have hy'e : y' = y * (y⁻¹ * y') := by group
    have hz2 := H.coords.sq_eq_one hz
    calc y ^ 2 = y ^ 2 * (y⁻¹ * y') ^ 2 := by rw [hz2, mul_one]
      _ = y * (y * (y⁻¹ * y')) * (y⁻¹ * y') := by rw [sq, sq]; group
      _ = y * ((y⁻¹ * y') * y) * (y⁻¹ * y') := by rw [hzc]
      _ = (y * (y⁻¹ * y')) ^ 2 := by rw [sq]; group
      _ = y' ^ 2 := by rw [← hy'e]
  choose ys hysT hysu using hc.u_surj
  set N : E → K := fun a => v (ys a ^ 2) with hNdef
  have hN_eq : ∀ y ∈ szT₁ L T, N (u y) = v (y ^ 2) := fun y hy => by
    show v (ys (u y) ^ 2) = v (y ^ 2)
    rw [hsq_eq _ (hysT _) y hy (hysu _)]
  choose bs hbsA hbsv using H.coords.surj
  have hbs_v : ∀ b ∈ szA₁ (szT₁ L T), bs (v b) = b := fun b hb =>
    H.coords.inj _ (hbsA _) _ hb (hbsv _)
  have hwmul : ∀ b ∈ szA₁ (szT₁ L T), ∀ b' ∈ szA₁ (szT₁ L T), w (b * b') = w b + w b' :=
    fun b hb b' hb' => hc.v_mul_of_u_eq_zero (hA₁T hb) (hA₁T hb') ((hA b (hA₁T hb)).mp hb)
  let ι : K →+ E := AddMonoidHom.mk' (fun s => w (bs s)) fun s s' => by
    have e : bs (s + s') = bs s * bs s' := H.coords.inj _ (hbsA _) _
      (mul_mem (hbsA s) (hbsA s')) (by rw [hbsv, H.coords.mul _ (hbsA s) _ (hbsA s'), hbsv, hbsv])
    show w (bs (s + s')) = w (bs s) + w (bs s')
    rw [e, hwmul _ (hbsA s) _ (hbsA s')]
  have hιv : ∀ b ∈ szA₁ (szT₁ L T), ι (v b) = w b := fun b hb => by
    show w (bs (v b)) = w b
    rw [hbs_v b hb]
  have hιinj : Function.Injective ι := by
    intro s s' h
    have h1 : w (bs s) = w (bs s') := h
    have h2 : bs s = bs s' := hc.inj _ (hA₁T (hbsA s)) _ (hA₁T (hbsA s'))
      (by rw [(hA _ (hA₁T (hbsA s))).mp (hbsA s), (hA _ (hA₁T (hbsA s'))).mp (hbsA s')]) h1
    rw [← hbsv s, ← hbsv s', h2]
  have hN9 : ∀ a, ι (N a) = a ^ 9 := by
    intro a
    have hb := H.stage.sq_mem_szA₁ (hysT a)
    show ι (v (ys a ^ 2)) = a ^ 9
    rw [hιv _ hb, (hc.sq (hysT a)).2, hysu, hσ, hf]
    ring
  have hE64 : Nat.card E = 64 := by rw [hEcard, hf]; norm_num
  have hK8 : Nat.card K = 8 := by rw [Nat.card_eq_fintype_card, H.card_K, hf]; norm_num
  refine false_of_affine_card_eq_168_of_norm_equivariant hE64 hK8 ι hιinj N hN9 H.perm.range
    ?_ h168 hs ?_
  · rintro _ ⟨n, rfl⟩ a b
    obtain ⟨ℓ, hℓ⟩ := H.perm_affine n
    rw [hℓ (a + b), hℓ a, hℓ b, map_add]
    ring
  · rintro _ ⟨n, rfl⟩
    have hnT := H.stage.normalizer_U_le_normalizer_T₁ H.mu H.lam H.nu n.2
    have hconjT : ∀ y ∈ szT₁ L T, (n : G) * y * (n : G)⁻¹ ∈ szT₁ L T := fun y hy =>
      (mem_normalizer_iff.mp hnT y).mp hy
    have hnA : ∀ y ∈ szT₁ L T, u y = 0 → u ((n : G) * y * (n : G)⁻¹) = 0 := fun y hy hu =>
      (hA _ (hconjT y hy)).mp (H.conj_mem_szA₁ n.2 ((hA y hy).mpr hu))
    have hnA' : ∀ y ∈ szT₁ L T, u ((n : G) * y * (n : G)⁻¹) = 0 → u y = 0 := by
      intro y hy hu
      have h1 := H.conj_mem_szA₁ (inv_mem n.2) ((hA _ (hconjT y hy)).mpr hu)
      rw [show (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * (n : G)⁻¹⁻¹ = y by group] at h1
      exact (hA y hy).mp h1
    obtain ⟨φ, hφ⟩ := hc.exists_addEquiv_conj hnT hnA hnA'
    refine ⟨φ, fun a => ?_⟩
    have hb := H.stage.sq_mem_szA₁ (hysT a)
    show H.perm n (v (ys a ^ 2)) - H.perm n 0 = N (φ a)
    rw [H.perm_v_szA₁ n hb, add_sub_cancel_right, ← conj_pow, ← hN_eq _ (hconjT _ (hysT a)),
      hφ _ (hysT a), hysu]

end U3C1Next

end CFSG.SeitzReduction.RankOne

module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R9Rest5
public import CFSG.GH74.GLS.Stage1.Main.P49Out
public import CFSG.GH74.GLS.Stage1.Main.P49X
public import CFSG.GH74.GLS.Stage1.Main.P49N

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec8
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K F U : Subgroup G} {x y : G}

theorem sl2_product_of_kd {Y : Type} [Group Y] [Finite Y] {Kb Hb : Subgroup Y} {Fq : Type} [Field Fq] [Finite Fq]
    (eK : ↥Kb ≃* StatedSL 2 Fq) (hodd : Odd (Nat.card Fq)) (h5 : 5 ≤ Nat.card Fq)
    (hv : (Nat.card ↥(StatedSL 2 Fq)).factorization 2 = 3)
    (hH : Nonempty (↥Hb ≃* StatedSL 2 (ZMod 3))) (hcomm : ∀ a ∈ Kb, ∀ b ∈ Hb, a * b = b * a)
    (hcard : Nat.card ↥(Kb ⊓ Hb) = 2) (hle : Kb ⊔ Hb ≤ oPrimeResidual 2 Y)
    (hidx : ((Kb ⊔ Hb).subgroupOf (oPrimeResidual 2 Y)).index = 2) :
    HasSL2ProductOfIndexTwoStage1 (oPrimeResidual 2 Y) 3 := by
  have h3 : Nat.card (ZMod 3) = 3 := Nat.card_zmod 3
  have h24 : (Nat.card ↥(StatedSL 2 (ZMod 3))).factorization 2 = 3 := by
    rw [card_statedSL_two', h3]
    have : (3 * (3 ^ 2 - 1) : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [this]
    exact two_val_pow_mul_odd' 3 (by decide)
  exact ⟨Fq, ZMod 3, inferInstance, inferInstance, inferInstance, inferInstance, hodd, by rw [h3]; decide,
    by rw [h3]; omega, h3, h5, by rw [hv, h24], Kb ⊔ Hb, hle, hidx, Kb, Hb, rfl, hcomm, hcard, ⟨eK⟩, hH⟩


theorem prop49_local_thm (hII : II4_4_4_center) (hq : II4_4_quat) (hdiag : IVK_diag_unique)
    (h19 : IVK_1_9_outer) (hsd : SD_facts) (hsdq : SD_sq_not_z) (hqc : Quat_centr) (hrn : Rnormal4)
    (h44 : II4_44) (hlift : II4_ord4_lift) (hIG : IG_15_16_ext) : Prop49_local := by
  intro G _ _ z S K F h hQF hquat U hUR hU4 hUn x hx3 hxW hxU hxz hcard hidx hy
  obtain ⟨y, hyS, hy2, hyR, hysd⟩ := hy
  have c : Ctx49 G z S K F U x y :=
    ⟨h, hQF, hquat, hUR, hU4, hUn, hx3, hxW, hxU, hxz, hcard, hidx, hyS, hy2, hyR, hysd⟩
  have hRS : Rz S z ≤ S := sup_le inf_le_left inf_le_left
  have hsl : IsSL2Or2A7 (HatT K) := h44 G h.simple z h.orderOf_z K h.comp_isPCompIn h.comp_pRank
  rcases hsl.1 with ⟨Fq, hF', hfin, ⟨hodd, h5⟩, ⟨eq⟩⟩ | h2A7
  swap
  · exfalso
    have hS : S = Pz S z ⊔ F := h.eq_of_2A7 h2A7
    have hR : Rz S z = S := by
      have e : Rz S z = Pz S z ⊔ F := by unfold Rz; rw [hQF]
      rw [e, ← hS]
    rw [hR, Subgroup.relIndex_self] at hidx
    exact absurd hidx (by norm_num)
  have hcl : Closed49 := ⟨hII, hq, hdiag, h19, hsd, hsdq, hqc, hrn⟩
  have hSyl := sylow_G_of_std6 h.toStd6r1.toStd6
  have hfus := fusion49 hIG hlift hcl c
  have hK1 := no_second_comp49 hcl c
  obtain ⟨h₀, t, t', h₀2, t2, t'2, ⟨g, hgS⟩, hh₀U, hh₀t, hh₀t', htU, ht'U, ht, ht', hdist⟩ :=
    local_N49 hcl hSyl c
  have hg2 : orderOf (g * h₀ * g⁻¹) = 2 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective h₀
    rw [← h₀2]
    simpa [MulAut.conj_apply] using this
  have hz : IsConj z h₀ := (hfus _ hgS hg2).trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
  obtain ⟨V, c3, hV4, hVX, hcX, hc3, hcV, hcn⟩ :=
    transport49 hz hU4 h₀2 t2 t'2 hh₀U hh₀t hh₀t' htU ht'U ht ht' hdist
  obtain ⟨nP, hnP⟩ := h.P_quat hq
  obtain ⟨nQ, hnQ⟩ := hquat
  have hQ' : IVK.IsQuaternionTwoGroup ↥(S ⊓ cSec K) nQ := by rw [← h.Qz_eq, hQF]; exact hnQ
  have hPQ : nP = nQ := by
    have h3 : Nat.card ↥(Pz S z) = Nat.card ↥(Qz S z) := hcard
    rw [h.Pz_eq, h.Qz_eq, R1.card_of_quat hnP, R1.card_of_quat hQ'] at h3
    exact Nat.pow_right_injective (le_refl 2) h3
  subst hPQ
  obtain ⟨hKn, hKq, hZ, hO, hcomp, hTs, hPb, hQb, hTc, hrot⟩ := bar_data49 hcl h44 hSyl hK1 c hnP hQ'
  obtain ⟨ι⟩ := imgBar_equiv h.comp_isPCompIn
  have eK : ↥(imgBar z K) ≃* StatedSL 2 Fq := ι.symm.trans eq
  obtain ⟨hn3, Hb, hHb, hcomm, hcard2, hle, hidx2⟩ :=
    kd_structure (imgBar z K) hKn hKq hZ (hout49 eK hodd h5) hO hcomp (imgBar z S) hTs hnP.1
      hPb hQb hTc hrot V c3 hV4 hVX hcX hc3 hcV hcn
  subst hn3
  have hP8 : Nat.card ↥(Pz S z) = 8 := by rw [h.Pz_eq, R1.card_of_quat hnP]; norm_num
  refine ⟨hP8, ?_, ?_⟩
  · have hP8' : Nat.card ↥(S ⊓ K) = 2 ^ 3 := by rw [R1.card_of_quat hnP]
    have hv3 := two_val_hatT h hP8'
    have hcardK : Nat.card (HatT K) = Nat.card (StatedSL 2 Fq) := Nat.card_congr eq.toEquiv
    have hv : (Nat.card ↥(StatedSL 2 Fq)).factorization 2 = 3 := by rw [← hcardK]; exact hv3
    exact sl2_product_of_kd eK hodd h5 hv hHb hcomm hcard2 hle hidx2
  · intro v hv hv2 hv1
    exact hfus v (hRS hv) (orderOf_eq_prime (by rwa [sq]) hv1)


end CFSG.GH74.GLS.Stage1.Thm3.Sec6

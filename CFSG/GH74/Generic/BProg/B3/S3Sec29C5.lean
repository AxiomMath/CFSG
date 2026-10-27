module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29C1
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wFacts
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3 CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3Sec29Cw

variable {G : Type} [Group G] [Finite G]

section Setting

variable {x y : G} {K A B Q D J R : Subgroup G}

theorem y_comm_Q (h : Ctx29w G x K A B Q y y D J) {q : G} (hq : q ∈ Q) : q * y = y * q :=
  ((Subgroup.mem_centralizer_iff.1 (h.Q_cent hq)) y (Subgroup.mem_inf.1 h.y_mem).1).symm

theorem Q_le_cSec_Ly (h : Ctx29w G x K A B Q y y D J) : Q ≤ cSec (Ly29 K y) := fun _ hq =>
  S3Ctx29Layer.mem_cSec_pLayerOf (Subgroup.mem_inf.1 (h.Q_syl.le hq)).2 (y_comm_Q h hq)

theorem y_mem_CxK_left (h : Ctx29w G x K A B Q y y D J) : y ∈ centralizer ({x} : Set G) := by
  have hAC : A ≤ centralizer ({x} : Set G) := h.src.1
  exact hAC (Subgroup.mem_inf.1 h.y_mem).1

theorem y_ne_one (h : Ctx29w G x K A B Q y y D J) : y ≠ 1 := by
  intro h1
  have := h.y_ord
  rw [h1, orderOf_one] at this
  omega

theorem y_not_mem_cSec (h : Ctx29w G x K A B Q y y D J) : y ∉ cSec K := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, hyE⟩ := h.exists_E
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hZ := B1.PilotS3.center_trivial_of_shape3 hK h.shape.qShape3
  intro hy
  exact y_ne_one h (S3Ctx29.eq_one_of_mem_cSec hZ hEK (CFSG.IsElementaryAbelian.isPGroup 2 ↥E) hyE hy)

theorem mem_normalizer_K (h : Ctx29w G x K A B Q y y D J) {r : G}
    (hr : r ∈ centralizer ({x} : Set G)) (hry : r * y = y * r) : r ∈ normalizer (K : Set G) := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, hyE⟩ := h.exists_E
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  exact S3Sec29C.mem_normalizer_of_comm hK (B1.PilotS3.center_trivial_of_shape3 hK h.shape.qShape3)
    (Subgroup.mem_inf.1 h.y_mem).2 h.y_ord hr hry

end Setting

section PartC

variable {x y : G} {K A B Q D J R : Subgroup G}

theorem J_comp (h : Ctx29w G x K A B Q y y D J) : IsPCompIn 2 (centralizer ({y} : Set G)) J := by
  rcases h.obs with h1 | ⟨-, h2, -⟩
  · exact h1.comp
  · exact h2.comp

theorem B_le_centralizer_y (h : Ctx29w G x K A B Q y y D J) : B ≤ centralizer ({y} : Set G) := by
  obtain ⟨hAB, -, -, hBel, -⟩ := h.ext
  intro b hb
  have hyB : y ∈ B := hAB (Subgroup.mem_inf.1 h.y_mem).1
  have := mul_comm' (⟨b, hb⟩ : ↥B) ⟨y, hyB⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)

end PartC

section PartC2

variable {x y : G} {K A B Q D J R : Subgroup G}

theorem part_c (hK26 : K26 G) (h : Ctx29w G x K A B Q y y D J) (h295 : B ⊓ cSec K ⊓ cSec J = ⊥)
    (h296 : Ly29 K y ≤ cSec J) (hRB : ∀ g ∈ B ⊓ cSec K, ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) = ⊥ := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, hyE⟩ := h.exists_E
  obtain ⟨-, -, -, hB0r⟩ := h.B_decomp ⟨hEK, hAE, hEel, hE4⟩
  obtain ⟨hAB, -, -, hBel, -⟩ := h.ext
  have hJ := J_comp h
  have hBy := B_le_centralizer_y h
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥B) ⟨c, hc⟩)
  have hyB : y ∈ B := hAB (Subgroup.mem_inf.1 h.y_mem).1
  have hZJ : Zstar (Jstar B J) ≤ cSec J := S3Sec29C.zstar_Jstar_le_cSec hBy hJ
  have hyJ : y ∈ cSec J := h296 (Ctx29w.layer hK26 h).2.1
  have hFJ : Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) ≤ cSec J :=
    inf_le_right.trans (sup_le (inf_le_right.trans hZJ) (by rw [Subgroup.zpowers_le]; exact hyJ))
  set B0 := B ⊓ cSec K with hB0
  set F := Q ⊓ ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y) with hF
  have hinv : ∀ g ∈ B0, ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
    intro g hg f hf
    have hgB : g ∈ B := (Subgroup.mem_inf.1 hg).1
    have hgQ : g ∈ Q := h.B0_le_Q hg
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgQ (Subgroup.mem_inf.1 hf).1) (inv_mem hgQ), ?_⟩
    have hle : (R ⊓ Zstar (Jstar B J)) ⊔ zpowers y ≤
        ((R ⊓ Zstar (Jstar B J)) ⊔ zpowers y).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun a ha => ?_) (fun a ha => ?_)
      · obtain ⟨haR, haZ⟩ := Subgroup.mem_inf.1 ha
        have h1 : g * a * g⁻¹ ∈ R := hRB g hg a haR
        have h2 : g * a * g⁻¹ ∈ Zstar (Jstar B J) :=
          S3Sec29C.Zstar_conj_mem _ (S3Sec29C.mem_normalizer_Jstar hgB) haZ
        exact Subgroup.mem_comap.2 (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨h1, h2⟩))
      · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        have hgy : g * y = y * g := hBc g hgB y hyB
        have : g * y ^ k * g⁻¹ = y ^ k := by
          have := (Commute.zpow_right (show Commute g y from hgy) k).eq
          rw [this]; group
        refine Subgroup.mem_comap.2 ?_
        show g * y ^ k * g⁻¹ ∈ _
        rw [this]
        exact Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers y k)
    exact hle (Subgroup.mem_inf.1 hf).2
  by_contra hne
  have hP2 : IsPGroup 2 ↥(F ⊔ B0) :=
    h.Q_syl.isPGroup.to_le (sup_le inf_le_left h.B0_le_Q)
  have hnormF : F ⊔ B0 ≤ normalizer (F : Set G) := by
    refine sup_le (Subgroup.le_normalizer) (fun g hg => ?_)
    rw [Subgroup.mem_normalizer_iff]
    intro f
    refine ⟨fun hf => hinv g hg f hf, fun hf => ?_⟩
    have := hinv g⁻¹ (inv_mem hg) _ hf
    simpa [mul_assoc] using this
  obtain ⟨z, hzF, hz2, hzc⟩ := S3Sec29C.exists_involution_central hP2 le_sup_left hne
    (fun p hp f hf => (Subgroup.mem_normalizer_iff.1 (hnormF hp) f).1 hf)
  have hzQ : z ∈ Q := (Subgroup.mem_inf.1 hzF).1
  have hzB0 : z ∈ B0 := by
    by_contra hzB
    have hzz : z * z = 1 := by
      have := pow_orderOf_eq_one z
      rwa [hz2, pow_two] at this
    have hcomm : ∀ b ∈ B0, ∀ k ∈ zpowers z, b * k = k * b := by
      intro b hb k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      exact (Commute.zpow_right (show Commute b z from hzc b (Subgroup.mem_sup_right hb)) n).eq
    have hi : B0 ⊓ zpowers z = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨hwB, hwz⟩ := Subgroup.mem_inf.1 hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hwz
      rcases Int.emod_two_eq_zero_or_one n with h0 | h1
      · have : z ^ n = 1 := by
          have h2 := zpow_mod_orderOf z n
          rw [hz2, Nat.cast_ofNat, h0, zpow_zero] at h2
          exact h2.symm
        rw [this]
        exact one_mem _
      · exfalso
        apply hzB
        have h2 := zpow_mod_orderOf z n
        rw [hz2, Nat.cast_ofNat, h1, zpow_one] at h2
        rw [← h2] at hwB
        exact hwB
    have hB0el : CFSG.IsElementaryAbelian 2 ↥B0 := Th2Sig6.isElementaryAbelian_of_le hBel inf_le_left
    have hB0card : Nat.card ↥B0 = 2 ^ 2 := by
      rw [C3.Layer1.Back.card_eq_two_pow_pRank hB0el, hB0r]
    have hE'card : Nat.card ↥(B0 ⊔ zpowers z) = 2 ^ 3 := by
      rw [S3Theta52.card_sup_of_commute hcomm hi, hB0card, Nat.card_zpowers, hz2]
      norm_num
    have hE'el : CFSG.IsElementaryAbelian 2 ↥(B0 ⊔ zpowers z) := by
      refine C3.Layer1.Back.isElementaryAbelian_of_forall ?_ ?_
      · intro u hu v hv
        obtain ⟨b1, hb1, k1, hk1, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hcomm hu
        obtain ⟨b2, hb2, k2, hk2, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hcomm hv
        have e1 := hcomm b2 hb2 k1 hk1
        have e2 : b1 * b2 = b2 * b1 :=
          hBc b1 (Subgroup.mem_inf.1 hb1).1 b2 (Subgroup.mem_inf.1 hb2).1
        have e3 : k1 * k2 = k2 * k1 := by
          obtain ⟨m1, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk1
          obtain ⟨m2, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk2
          exact (Commute.zpow_zpow_self z m1 m2).eq
        calc b1 * k1 * (b2 * k2) = b1 * (k1 * b2) * k2 := by group
          _ = b1 * (b2 * k1) * k2 := by rw [e1]
          _ = (b1 * b2) * (k1 * k2) := by group
          _ = (b2 * b1) * (k2 * k1) := by rw [e2, e3]
          _ = b2 * (b1 * k2) * k1 := by group
          _ = b2 * (k2 * b1) * k1 := by rw [hcomm b1 hb1 k2 hk2]
          _ = b2 * k2 * (b1 * k1) := by group
      · intro u hu
        obtain ⟨b, hb, k, hk, rfl⟩ := S3Theta52.exists_mul_of_mem_sup hcomm hu
        have e1 := hcomm b hb k hk
        have hbb : b * b = 1 := by
          have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B) b
            (Subgroup.mem_inf.1 hb).1
          rw [sq] at this
          exact this
        have hkk : k * k = 1 := by
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
          have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzz
          rw [← zpow_add, ← two_mul, zpow_mul, hz2', one_zpow]
        calc b * k * (b * k) = b * (k * b) * k := by group
          _ = b * (b * k) * k := by rw [← e1]
          _ = (b * b) * (k * k) := by group
          _ = 1 := by rw [hbb, hkk, one_mul]
    have hE'Q : B0 ⊔ zpowers z ≤ Q := sup_le h.B0_le_Q (by rw [Subgroup.zpowers_le]; exact hzQ)
    have h3 : pRank 2 ↥(B0 ⊔ zpowers z) = 3 := CFSG.pRank_eq_of_card_eq_pow one_lt_two hE'card
    have h4 := C3.Layer1.Back.pRank_mono' hE'Q
    have h5 := h.rank_Q
    omega
  have hzJ : z ∈ cSec J := hFJ hzF
  have : z ∈ B ⊓ cSec K ⊓ cSec J := Subgroup.mem_inf.2 ⟨hzB0, hzJ⟩
  rw [h295, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hz2
  omega

end PartC2

end S3Sec29Cw

end CFSG.GH74.Generic.BProg.B3

module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubMain
public import CFSG.ClassicalInvolution.Q3.Q3T8ThompsonD
public import CFSG.ClassicalInvolution.Q3.Q3T7P24A02

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

@[expose] def L7_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), PartIHyp Ω →
    ∀ W ∈ WSet Ω, ¬ DbarConnected Ω W → ∀ a ∈ Subgroup.normalizer (W : Set G), a * a = 1 →
      ∃ R ∈ DSet Ω W, conjSub a R = R
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
section Components
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
end Components
section Boundary
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Boundary
section GroupW
variable {G : Type} [Group G]
end GroupW
section Existence
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
end Existence
section Connected
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_not_mem_W {R K : Subgroup G}
    (hR : R ∈ DSet Ω W) (hK : K ∈ Ω)
    (hRK : IsSylow2In R K) : ∃ r ∈ R, r ∉ W := by
  obtain ⟨-, -, -, -, hcard⟩ := Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW hR hK hRK
  by_contra hcon
  push Not at hcon
  rw [inf_eq_left.mpr hcon] at hcard
  have : 0 < Nat.card R := Nat.card_pos
  omega
end Ctx
end Connected
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {W : Subgroup G}
section Fixed
variable [Finite G]

theorem exists_fixed_member (hΩ : HypOmegaMod Ω) {R₀ : Subgroup G}
    (hR₀ : R₀ ∈ DSet Ω W) {a : G} (haN : a ∈ Subgroup.normalizer (W : Set G)) (ha2 : a * a = 1)
    {K : Subgroup G} (hK : K ∈ Ω) (hR₀K : R₀ ≤ K) (hR₁K : conjSub a R₀ ≤ K) :
    ∃ R ∈ DSet Ω W, conjSub a R = R := by
  by_cases ha1 : a = 1
  · exact ⟨R₀, hR₀, by rw [ha1, conjSub_one]⟩
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR₀.1
  have h8 : 8 ≤ Nat.card R₀ := hΩ.eight_le_of_mem_RSet hR₀.1
  have hJK : J = K := hΩ.eq_of_le_of_le hJ hK hRJ.2.1 (by omega) hRJ.1 hR₀K
  subst hJK
  have hcard : Nat.card (conjSub a R₀) = Nat.card R₀ := natCard_conjSub R₀ a
  have haK : conjSub a J = J :=
    hΩ.eq_of_le_of_le (hΩ.conjInvariant a J hK) hK (isPGroup_conjSub a hRJ.2.1) (by omega)
      (conjSub_mono hRJ.1) hR₁K
  set N₁ : Subgroup G := J ⊓ Subgroup.normalizer (W : Set G) with hN₁
  have ha2g : IsPGroup 2 (Subgroup.zpowers a) := isPGroup_zpowers_of_mul_self_eq_one ha2 ha1
  have hzN : Subgroup.zpowers a ≤ Subgroup.normalizer (N₁ : Set G) :=
    Subgroup.zpowers_le.mpr (normalizer_inf_normalizer_conj haK haN)
  obtain ⟨R, hRN, hRfix⟩ := AscL62.exists_sylow_normalized ha2g hzN
  have hR₀N₁ : R₀ ≤ N₁ := le_inf hR₀K hR₀.2
  have hle : Nat.card R₀ ≤ Nat.card R := hRN.natCard_le hRJ.2.1 hR₀N₁
  have hRJ' : IsSylow2In R J := hRJ.of_natCard_le hRN.2.1 (hRN.1.trans inf_le_left) hle
  exact ⟨R, ⟨mem_RSet_of_isSylow2In hK hRJ', hRN.1.trans inf_le_right⟩,
    hRfix a (Subgroup.mem_zpowers a)⟩
omit [Finite G] in

theorem conjQ_conjQ [Finite G] (hΩ : HypOmegaMod Ω) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set
    G))
    (hg2 : g * g = 1) (q : ↥(muGroup Ω W)) : conjQ hΩ hg (conjQ hΩ hg q) = q := by
  apply Subtype.ext
  have hpa := piG_mul_self_of hg hg2
  have hinv : (piG W g)⁻¹ = piG W g := inv_eq_of_mul_eq_one_left hpa
  rw [conjQ_apply, conjQ_apply, hinv]
  calc piG W g * (piG W g * q.1 * piG W g) * piG W g
      = (piG W g * piG W g) * q.1 * (piG W g * piG W g) := by group
    _ = q.1 := by rw [hpa, one_mul, mul_one]

theorem dComm_of_commute (hΩ : HypOmegaMod Ω)
    (hW : W ∈ WSet Ω) {R₁ R₂ : Subgroup G} (h₁ : R₁ ∈ DSet Ω W) (h₂ : R₂ ∈ DSet Ω W) {r₁ r₂ : G}
    (hr₁ : r₁ ∈ R₁) (hr₂ : r₂ ∈ R₂) (hr₁W : r₁ ∉ W) (hr₂W : r₂ ∉ W)
    (hcomm : piG W r₁ * piG W r₂ = piG W r₂ * piG W r₁) (hne : piG W r₁ ≠ piG W r₂) :
    DComm W R₁ R₂ := by
  refine ⟨fun hle => hne ?_, fun x hx x' hx' => ?_⟩
  · exact (Q3CL.Thompson.piG_eq_of_le_sup hΩ hW h₁ h₂ hle hr₁ hr₂ hr₁W hr₂W).symm
  · by_cases hxW : x ∈ W
    · exact Subgroup.mem_sup_left (comm_mem_of_mem hxW (h₂.2 hx'))
    · by_cases hx'W : x' ∈ W
      · have h2 : x * x' * x⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (h₁.2 hx) x').mp hx'W
        exact Subgroup.mem_sup_left (W.mul_mem h2 (W.inv_mem hx'W))
      · have hc' : piG W x * piG W x' = piG W x' * piG W x := by
          rw [Q3CL.Thompson.D_piG_eq hΩ hW h₁ hx hr₁ hxW hr₁W, Q3CL.Thompson.D_piG_eq hΩ hW h₂ hx'
              hr₂ hx'W hr₂W]
          exact hcomm
        exact (piG_comm_iff (h₁.2 hx) (h₂.2 hx')).mp hc'

theorem exists_fixed_member_of_muDelta_fixed (hΩ : HypOmegaMod Ω) (hW : W ∈ WSet Ω) {a : G}
    (haN : a ∈ Subgroup.normalizer (W : Set G)) (ha2 : a * a = 1)
    (hx : ∃ x ∈ muDelta Ω W, conjQ hΩ haN x = x) : ∃ R ∈ DSet Ω W, conjSub a R = R := by
  obtain ⟨x, ⟨R₀, hR₀, r₀, hr₀, hr₀W, hxr⟩, hax⟩ := hx
  have hR₁ : conjSub a R₀ ∈ DSet Ω W := Q3CL.Thompson.conjSub_mem_D hΩ hR₀ haN
  have hr₁ : a * r₀ * a⁻¹ ∈ conjSub a R₀ := conj_mem_conjSub hr₀
  have hr₁W : a * r₀ * a⁻¹ ∉ W := fun h => hr₀W ((mem_normalizer_iff_of_mem haN r₀).mp h)
  have hpi : piG W (a * r₀ * a⁻¹) = piG W r₀ := by
    rw [← conjQ_val hΩ haN (hR₀.2 hr₀) hxr, hax, hxr]
  have hle : conjSub a R₀ ≤ R₀ ⊔ W ⊔ OCW W :=
    le_sup_of_piG_eq hr₀ hR₀.2 hR₁.2 fun y hy hyW =>
      (Q3CL.Thompson.D_piG_eq hΩ hW hR₁ hy hr₁ hyW hr₁W).trans hpi
  obtain ⟨K, hK, hR₀K, hR₁K⟩ := exists_member_of_D_same_gen hΩ hW hR₀ hR₁ hle
  exact exists_fixed_member hΩ hR₀ haN ha2 hK hR₀K hR₁K

theorem conj_mul_conj_eq (hΩ : HypOmegaMod Ω)
    (hW : W ∈ WSet Ω) {a : G} (ha2 : a * a = 1) {w v : G} (hw : w ∈ W) (hv : v ∈ W)
    (hvd : v = a * w * a⁻¹) : a * (w * v) * a⁻¹ = w * v := by
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hW
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have e1 : a * v * a⁻¹ = w := by
    rw [hvd, hai]
    calc a * (a * w * a) * a = (a * a) * w * (a * a) := by simp only [mul_assoc]
      _ = w := by rw [ha2, one_mul, mul_one]
  calc a * (w * v) * a⁻¹ = (a * w * a⁻¹) * (a * v * a⁻¹) := by group
    _ = v * w := by rw [e1, ← hvd]
    _ = w * v := hWab _ hv _ hw
end Fixed
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.muDeltaCent_eq_inter {e : G} (he : e ∈
    W) :
    muDeltaCent Ω W e = muDelta Ω W ∩ (muStab Ω W e : Set ↥(muGroup Ω W)) := by
  ext q
  constructor
  · rintro ⟨T, ⟨hT, hTe⟩, t, ht, htW, hq⟩
    refine ⟨⟨T, hT, t, ht, htW, hq⟩, (c.mem_muStab_iff he hT ht hq).mpr ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hTe ht)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  · rintro ⟨⟨R, hR, r, hr, hrW, hqr⟩, hqs⟩
    have hre := (c.mem_muStab_iff he hR hr hqr).mp hqs
    have hrc : r * e = e * r := by
      rw [mul_inv_eq_iff_eq_mul] at hre
      exact hre
    exact ⟨R, ⟨hR, Q3CL.Thompson.le_centralizer_of_mem c.hΩ c.hW hR hr hrW he hrc⟩, r, hr, hrW, hqr⟩
end Ctx
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_perm_four_of_wv (c : Q3CL.Thompson.Ctx Ω W) (hTT : Star3T.IsTT (muDelta Ω W))
    (hS : Star3T.IsStar (muDelta Ω W)) {R₁ R₂ : Subgroup G} (hR₁ : R₁ ∈ DSet Ω W)
    (hR₂ : R₂ ∈ DSet Ω W) (hDC : DComm W R₁ R₂) {r₁ : G} (hr₁ : r₁ ∈ R₁) (hr₁W : r₁ ∉ W)
    {d a : ↥(muGroup Ω W)} (hd : (d : NQuot (W ⊔ OCW W)) = piG W r₁)
    (hdΔ : d ∈ muDelta Ω W) (haΔ : a ∈ muDelta Ω W) (hconn : ¬ Star3T.Conn (muDelta Ω W) d a)
    (hk : (Star3T.cent (muDelta Ω W) d).ncard = 4) {w v : G} (hw : w ∈ R₁ ⊓ W)
    (hv : v ∈ R₂ ⊓ W) (hw4 : orderOf w = 4) (hv4 : orderOf v = 4) :
    ∃ ψ : ↥(Subgroup.closure (muDeltaCent Ω W (w * v))) ≃* Equiv.Perm (Fin 4),
      ∀ (x : ↥(muGroup Ω W)) (hx : x ∈ Subgroup.closure (muDeltaCent Ω W (w * v))),
        x ∈ muDeltaCent Ω W (w * v) ↔ (ψ ⟨x, hx⟩).IsSwap := by
  classical
  have hΩ := c.hΩ
  have he : w * v ∈ W := W.mul_mem hw.2 hv.2
  have he' : w⁻¹ * v ∈ W := W.mul_mem (W.inv_mem hw.2) hv.2
  
  obtain ⟨K₁, hK₁, hR₁K⟩ := exists_isSylow2In_of_mem_RSet hR₁.1
  obtain ⟨K₂, hK₂, hR₂K⟩ := exists_isSylow2In_of_mem_RSet hR₂.1
  obtain ⟨r₂, hr₂, hr₂W⟩ := c.exists_not_mem_W hR₂ hK₂ hR₂K
  let ρ₁ : Rep Ω W := ⟨K₁, R₁, r₁, hK₁, hR₁, hR₁K, hr₁, hr₁W⟩
  let ρ₂ : Rep Ω W := ⟨K₂, R₂, r₂, hK₂, hR₂, hR₂K, hr₂, hr₂W⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ↥(muGroup Ω W), (x₂ : NQuot (W ⊔ OCW W)) = piG W r₂ :=
    ⟨⟨piG W r₂, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR₂ hr₂))⟩, rfl⟩
  have hx₂Δ : x₂ ∈ muDelta Ω W := ⟨R₂, hR₂, r₂, hr₂, hr₂W, hx₂⟩
  have hcomm12 : ρ₁.img * ρ₂.img = ρ₂.img * ρ₁.img :=
    (piG_comm_iff (hR₁.2 hr₁) (hR₂.2 hr₂)).mpr (hDC.2 r₁ hr₁ r₂ hr₂)
  have hK12 : K₁ ≠ K₂ := by
    intro h
    exact hDC.1 (c.hkey R₁ hR₁ R₂ hR₂ K₁ hK₁ hR₁K.1 (h ▸ hR₂K.1))
  have hΩ12 : K₂ ∈ omegaNbr Ω K₁ := c.omega_of_comm ρ₁ ρ₂ hK12 hcomm12
  have hΩ21 : K₁ ∈ omegaNbr Ω K₂ := c.omega_of_comm ρ₂ ρ₁ hK12.symm hcomm12.symm
  have hwK : w ∈ K₁ ⊓ W := ⟨hR₁K.1 hw.1, hw.2⟩
  have hvK : v ∈ K₂ ⊓ W := ⟨hR₂K.1 hv.1, hv.2⟩
  obtain ⟨z₁, hz₁⟩ := hΩ.exists_uniqueInvolution hK₁
  obtain ⟨z₂, hz₂⟩ := hΩ.exists_uniqueInvolution hK₂
  have hw2 : w * w = z₁ := sq_eq_involution_of_orderOf_four hz₁ hwK.1 hw4
  have hv2 : v * v = z₂ := sq_eq_involution_of_orderOf_four hz₂ hvK.1 hv4
  
  have f1 : r₁ * w * r₁⁻¹ = w⁻¹ := c.conj_inv ρ₁ hwK
  have f2 : r₁ * v * r₁⁻¹ = v := by
    rw [mul_inv_eq_iff_eq_mul]
    exact c.centralizes ρ₁ ρ₂ hΩ12 hvK
  have f3 : r₂ * w * r₂⁻¹ = w := by
    rw [mul_inv_eq_iff_eq_mul]
    exact c.centralizes ρ₂ ρ₁ hΩ21 hwK
  have f4 : r₂ * v * r₂⁻¹ = v⁻¹ := c.conj_inv ρ₂ hvK
  have g1 : r₁ * (w * v) * r₁⁻¹ = w⁻¹ * v := by
    calc r₁ * (w * v) * r₁⁻¹ = (r₁ * w * r₁⁻¹) * (r₁ * v * r₁⁻¹) := by group
      _ = w⁻¹ * v := by rw [f1, f2]
  have g1' : r₁ * (w⁻¹ * v) * r₁⁻¹ = w * v := by
    calc r₁ * (w⁻¹ * v) * r₁⁻¹ = (r₁ * w * r₁⁻¹)⁻¹ * (r₁ * v * r₁⁻¹) := by group
      _ = w * v := by rw [f1, f2, inv_inv]
  have g2 : r₂ * (w * v) * r₂⁻¹ = w * v⁻¹ := by
    calc r₂ * (w * v) * r₂⁻¹ = (r₂ * w * r₂⁻¹) * (r₂ * v * r₂⁻¹) := by group
      _ = w * v⁻¹ := by rw [f3, f4]
  have hz₁ne : z₁ ≠ 1 := hz₁.ne_one
  have hz₂ne : z₂ ≠ 1 := hz₂.ne_one
  have n1 : w⁻¹ * v ≠ w * v := by
    intro h
    have h' : w⁻¹ = w := mul_right_cancel h
    apply hz₁ne
    rw [← hw2]
    calc w * w = w⁻¹ * w := by rw [h']
      _ = 1 := inv_mul_cancel w
  have n2 : w * v⁻¹ ≠ w * v := by
    intro h
    have h' : v⁻¹ = v := mul_left_cancel h
    apply hz₂ne
    rw [← hv2]
    calc v * v = v⁻¹ * v := by rw [h']
      _ = 1 := inv_mul_cancel v
  
  have hd₂ne : d ≠ x₂ := by
    intro h
    apply hK12
    refine c.K_eq_of_img_eq ρ₁ ρ₂ ?_
    have h' : (d : NQuot (W ⊔ OCW W)) = x₂ := congrArg Subtype.val h
    rw [hd, hx₂] at h'
    exact h'
  have hcommdx₂ : x₂ * d = d * x₂ := by
    rw [muGroup_comm_iff, hx₂, hd]
    exact hcomm12.symm
  have hx₂F : x₂ ∈ Star3T.cent (muDelta Ω W) d := ⟨hx₂Δ, hcommdx₂⟩
  have hdF : d ∈ Star3T.cent (muDelta Ω W) d := Star3T.self_mem_cent hdΔ
  have hFeq : ∀ z ∈ Star3T.cent (muDelta Ω W) d,
      Star3T.cent (muDelta Ω W) z = Star3T.cent (muDelta Ω W) d := fun z hz =>
    Star3T.cent_eq_of_mem_cent hTT hS hdΔ haΔ hconn hz
  have hΛ : ∀ y, y ∈ muDeltaCent Ω W (w * v) ↔ y ∈ muDelta Ω W ∧ y ∈ muStab Ω W (w * v) :=
    fun y => by rw [c.muDeltaCent_eq_inter he]; exact Iff.rfl
  have hd_not : d ∉ muStab Ω W (w * v) := by
    intro h
    have := (c.mem_muStab_iff he hR₁ hr₁ hd).mp h
    exact n1 (g1.symm.trans this)
  have hx₂_not : x₂ ∉ muStab Ω W (w * v) := by
    intro h
    have := (c.mem_muStab_iff he hR₂ hr₂ hx₂).mp h
    exact n2 (g2.symm.trans this)
  
  have hFstab : ∀ q ∈ Star3T.cent (muDelta Ω W) d, q ≠ d → q ≠ x₂ →
      q ∈ muStab Ω W (w * v) := by
    intro q hqF hqd hqx
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hqF.1
    have hqx₂ : q * x₂ = x₂ * q := by
      have : q ∈ Star3T.cent (muDelta Ω W) x₂ := by rw [hFeq x₂ hx₂F]; exact hqF
      exact this.2
    have hcd : ρ.img * ρ₁.img = ρ₁.img * ρ.img := by
      have h' := muGroup_comm_iff.mp hqF.2
      rw [hd, ← hρ] at h'
      exact h'
    have hcx : ρ.img * ρ₂.img = ρ₂.img * ρ.img := by
      have h' := muGroup_comm_iff.mp hqx₂
      rw [hx₂, ← hρ] at h'
      exact h'
    have hKne1 : ρ.K ≠ K₁ := fun h =>
      hqd (Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₁ h).trans hd.symm)))
    have hKne2 : ρ.K ≠ K₂ := fun h =>
      hqx (Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₂ h).trans hx₂.symm)))
    have e1 : ρ.r * w * ρ.r⁻¹ = w := by
      rw [mul_inv_eq_iff_eq_mul]
      exact c.centralizes ρ ρ₁ (c.omega_of_comm ρ ρ₁ hKne1 hcd) hwK
    have e2 : ρ.r * v * ρ.r⁻¹ = v := by
      rw [mul_inv_eq_iff_eq_mul]
      exact c.centralizes ρ ρ₂ (c.omega_of_comm ρ ρ₂ hKne2 hcx) hvK
    refine (c.mem_muStab_iff he ρ.hR ρ.hr hρ.symm).mpr ?_
    calc ρ.r * (w * v) * ρ.r⁻¹ = (ρ.r * w * ρ.r⁻¹) * (ρ.r * v * ρ.r⁻¹) := by group
      _ = w * v := by rw [e1, e2]
  
  have hAstab : ∀ q ∈ muDelta Ω W, q ∉ Star3T.cent (muDelta Ω W) d →
      q ∈ muStab Ω W (w * v) ∨ q ∈ muStab Ω W (w⁻¹ * v) := by
    intro q hqΔ hqF
    obtain ⟨ρ, hρ⟩ := exists_rep_of_mem_muDelta hqΔ
    have hKne1 : ρ.K ≠ K₁ := fun h => hqF (by
      have : q = d := Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₁ h).trans hd.symm))
      rw [this]
      exact hdF)
    have hKne2 : ρ.K ≠ K₂ := fun h => hqF (by
      have : q = x₂ := Subtype.ext (hρ.symm.trans ((c.img_eq_of_K_eq ρ ρ₂ h).trans hx₂.symm))
      rw [this]
      exact hx₂F)
    have hnot1 : K₁ ∉ omegaNbr Ω ρ.K := fun h => hqF (by
      have h' := c.comm_of_omega ρ ρ₁ h
      refine ⟨hqΔ, muGroup_comm_iff.mpr ?_⟩
      rw [hd, ← hρ]
      exact h')
    have hnot2 : K₂ ∉ omegaNbr Ω ρ.K := fun h => hqF (by
      have h' := c.comm_of_omega ρ ρ₂ h
      have : q ∈ Star3T.cent (muDelta Ω W) x₂ :=
        ⟨hqΔ, muGroup_comm_iff.mpr (by rw [hx₂, ← hρ]; exact h')⟩
      rwa [hFeq x₂ hx₂F] at this)
    obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution ρ.hK
    rcases c.stab_dichotomy ρ ρ₁ ρ₂ hKne1 hKne2 hnot1 hnot2 hwK hvK hz hz₁ hz₂ hw2 hv2 with
      h | h
    · exact Or.inl ((c.mem_muStab_iff he ρ.hR ρ.hr hρ.symm).mpr h)
    · exact Or.inr ((c.mem_muStab_iff he' ρ.hR ρ.hr hρ.symm).mpr h)
  have haF : a ∉ Star3T.cent (muDelta Ω W) d := fun h => hconn (Star3T.conn_of_mem_cent hdΔ h)
  have hdd : d * d = 1 := hTT.mul_self d hdΔ
  
  obtain ⟨a', ha'Δ, ha'S, ha'F⟩ : ∃ a' ∈ muDelta Ω W, a' ∈ muStab Ω W (w * v) ∧
      a' ∉ Star3T.cent (muDelta Ω W) d := by
    rcases hAstab a haΔ haF with h | h
    · exact ⟨a, haΔ, h, haF⟩
    · refine ⟨d * a * d, hTT.mul_mul_mem hdΔ haΔ, ?_, ?_⟩
      · obtain ⟨n, hnN, hn, hne⟩ := h
        have hr₁N := hR₁.2 hr₁
        have hinv₁ : (piG W r₁)⁻¹ = piG W r₁ :=
          inv_eq_of_mul_eq_one_left (Q3CL.Thompson.piG_mul_self_of_mem_D hΩ c.hW hR₁ hr₁)
        refine ⟨r₁ * n * r₁⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hr₁N hnN)
          (Subgroup.inv_mem _ hr₁N), ?_, ?_⟩
        · rw [Subgroup.coe_mul, Subgroup.coe_mul,
            piG_mul (Subgroup.mul_mem _ hr₁N hnN) (Subgroup.inv_mem _ hr₁N), piG_mul hr₁N hnN,
            piG_inv hr₁N, hinv₁, hd, hn]
        · have hr1inv : r₁⁻¹ * (w * v) * r₁ = w⁻¹ * v := by
            calc r₁⁻¹ * (w * v) * r₁ = r₁⁻¹ * (r₁ * (w⁻¹ * v) * r₁⁻¹) * r₁ := by rw [g1']
              _ = w⁻¹ * v := by group
          calc (r₁ * n * r₁⁻¹) * (w * v) * (r₁ * n * r₁⁻¹)⁻¹
              = r₁ * (n * (r₁⁻¹ * (w * v) * r₁) * n⁻¹) * r₁⁻¹ := by group
            _ = r₁ * (n * (w⁻¹ * v) * n⁻¹) * r₁⁻¹ := by rw [hr1inv]
            _ = r₁ * (w⁻¹ * v) * r₁⁻¹ := by rw [hne]
            _ = w * v := g1'
      · intro h'
        apply haF
        refine ⟨haΔ, ?_⟩
        have h2 := h'.2
        calc a * d = d * (d * a * d) := by
              calc a * d = (d * d) * a * d := by rw [hdd, one_mul]
                _ = d * (d * a * d) := by simp only [mul_assoc]
          _ = (d * a * d) * d := h2.symm
          _ = d * a := by
              calc (d * a * d) * d = d * a * (d * d) := by simp only [mul_assoc]
                _ = d * a := by rw [hdd, mul_one]
  
  have hsub : ({d, x₂} : Set ↥(muGroup Ω W)) ⊆ Star3T.cent (muDelta Ω W) d := by
    intro y hy
    rcases hy with h | h
    · rw [h]; exact hdF
    · rw [Set.mem_singleton_iff.mp h]; exact hx₂F
  have hcard2 : (Star3T.cent (muDelta Ω W) d \ {d, x₂}).ncard = 2 := by
    rw [Set.ncard_sdiff hsub, hk, Set.ncard_pair hd₂ne]
  obtain ⟨d₃, d₄, hd₃₄, hset⟩ := Set.ncard_eq_two.mp hcard2
  have hd₃ : d₃ ∈ Star3T.cent (muDelta Ω W) d \ {d, x₂} := by rw [hset]; exact Or.inl rfl
  have hd₄ : d₄ ∈ Star3T.cent (muDelta Ω W) d \ {d, x₂} := by rw [hset]; exact Or.inr rfl
  have hne3 : d₃ ≠ d ∧ d₃ ≠ x₂ := ⟨fun h => hd₃.2 (Or.inl h), fun h => hd₃.2 (Or.inr h)⟩
  have hne4 : d₄ ≠ d ∧ d₄ ≠ x₂ := ⟨fun h => hd₄.2 (Or.inl h), fun h => hd₄.2 (Or.inr h)⟩
  have hΛF : ∀ y, y ∈ muDeltaCent Ω W (w * v) → y ∈ Star3T.cent (muDelta Ω W) d →
      y = d₃ ∨ y = d₄ := by
    intro y hyΛ hyF
    have hyS := ((hΛ y).mp hyΛ).2
    have hyd : y ≠ d := fun h => hd_not (h ▸ hyS)
    have hyx : y ≠ x₂ := fun h => hx₂_not (h ▸ hyS)
    have hy : y ∈ Star3T.cent (muDelta Ω W) d \ {d, x₂} := by
      refine ⟨hyF, ?_⟩
      rintro (h | h)
      · exact hyd h
      · exact hyx h
    rw [hset] at hy
    exact hy
  have hd₃Λ : d₃ ∈ muDeltaCent Ω W (w * v) :=
    (hΛ d₃).mpr ⟨hd₃.1.1, hFstab d₃ hd₃.1 hne3.1 hne3.2⟩
  have hd₄Λ : d₄ ∈ muDeltaCent Ω W (w * v) :=
    (hΛ d₄).mpr ⟨hd₄.1.1, hFstab d₄ hd₄.1 hne4.1 hne4.2⟩
  have ha'Λ : a' ∈ muDeltaCent Ω W (w * v) := (hΛ a').mpr ⟨ha'Δ, ha'S⟩
  have hΛΔ : muDeltaCent Ω W (w * v) ⊆ muDelta Ω W := fun y hy => ((hΛ y).mp hy).1
  have hconj : ∀ g ∈ Subgroup.closure (muDeltaCent Ω W (w * v)),
      ∀ x ∈ muDeltaCent Ω W (w * v), g * x * g⁻¹ ∈ muDeltaCent Ω W (w * v) := by
    have hcl : Subgroup.closure (muDeltaCent Ω W (w * v)) ≤ muStab Ω W (w * v) :=
      (Subgroup.closure_le _).mpr fun y hy => ((hΛ y).mp hy).2
    intro g hg x hx
    refine (hΛ _).mpr ⟨hTT.conj_mem' (hΛΔ hx) g, ?_⟩
    exact (muStab Ω W (w * v)).mul_mem ((muStab Ω W (w * v)).mul_mem (hcl hg) ((hΛ x).mp hx).2)
      ((muStab Ω W (w * v)).inv_mem (hcl hg))
  have hconnΛ : ∀ y, Star3T.Conn (muDeltaCent Ω W (w * v)) d₃ y → y = d₃ ∨ y = d₄ := by
    intro y hy
    induction hy with
    | refl => exact Or.inl rfl
    | @tail b y' _ hbc ih =>
      have hbF : b ∈ Star3T.cent (muDelta Ω W) d := by
        rcases ih with h | h
        · rw [h]; exact hd₃.1
        · rw [h]; exact hd₄.1
      have hy'F : y' ∈ Star3T.cent (muDelta Ω W) d := by
        have : y' ∈ Star3T.cent (muDelta Ω W) b := ⟨hΛΔ hbc.2.1, hbc.2.2.symm⟩
        rwa [hFeq b hbF] at this
      exact hΛF y' hbc.2.1 hy'F
  have hc : ¬ Star3T.Conn (muDeltaCent Ω W (w * v)) d₃ a' := fun h => ha'F (by
    rcases hconnΛ a' h with h' | h'
    · rw [h']; exact hd₃.1
    · rw [h']; exact hd₄.1)
  have hcentΛ : Star3T.cent (muDeltaCent Ω W (w * v)) d₃ = {d₃, d₄} := by
    ext y
    constructor
    · rintro ⟨hyΛ, hyc⟩
      have hyF : y ∈ Star3T.cent (muDelta Ω W) d₃ := ⟨hΛΔ hyΛ, hyc⟩
      rw [hFeq d₃ hd₃.1] at hyF
      exact hΛF y hyΛ hyF
    · intro hy
      rcases hy with h | h
      · rw [h]; exact Star3T.self_mem_cent hd₃Λ
      · rw [Set.mem_singleton_iff.mp h]
        exact ⟨hd₄Λ, hTT.isClique_cent hS hdΔ haΔ hconn hd₄.1 hd₃.1⟩
  have hk' : (Star3T.cent (muDeltaCent Ω W (w * v)) d₃).ncard = 2 := by
    rw [hcentΛ]
    exact Set.ncard_pair hd₃₄
  exact Star3T.exists_mulEquiv_perm_four_of_closure hTT hS hΛΔ hconj hd₃Λ ha'Λ hc hk'
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77.Thompson
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}
namespace Ctx
open CFSG.ClassicalInvolution.Asc77.Thompson.Ctx
variable (c : Q3CL.Thompson.Ctx Ω W)
include c

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_mem_MGrp_piG_eq (hclC :
    Q3CL.ClassicalClause Ω) (g : ↥(muGroup Ω W)) :
    ∃ m ∈ MGrp Ω W, (g : NQuot (W ⊔ OCW W)) = piG W m := by
  have hP : PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  set L : Set G := {r | ∃ R ∈ DSet Ω W, r ∈ R} with hL
  have hLN : L ⊆ Subgroup.normalizer (W : Set G) := by
    rintro r ⟨R, hR, hr⟩
    exact hR.2 hr
  have hmem : g ∈ Subgroup.closure (muDelta Ω W) := by
    rw [hTT.closure_eq_top]
    trivial
  have h1 := Subgroup.mem_map_of_mem (muGroup Ω W).subtype hmem
  rw [MonoidHom.map_closure] at h1
  have hq' : (g : NQuot (W ⊔ OCW W)) ∈ Subgroup.closure (piG W '' L) := by
    refine Subgroup.closure_mono ?_ h1
    rintro _ ⟨q, ⟨R, hR, r, hr, hrW, hq⟩, rfl⟩
    exact ⟨r, ⟨R, hR, hr⟩, hq.symm⟩
  obtain ⟨m, hm, hmg⟩ := exists_mem_closure_of_mem_closure_piG hLN hq'
  refine ⟨m, ?_, hmg.symm⟩
  have hcl : Subgroup.closure L ≤ MGrp Ω W := by
    rw [Subgroup.closure_le]
    rintro r ⟨R, hR, hr⟩
    exact le_MGrp_of_mem_D hR hr
  exact hcl hm

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_conj_of_rep (hclC :
    Q3CL.ClassicalClause Ω) (hnc : ¬ DbarConnected Ω W) (ρ σ : Rep Ω W) :
    ∃ m ∈ MGrp Ω W, conjSub m ρ.K = σ.K := by
  have hP : PartIHyp Ω := ⟨c.hΩ, hclC, c.hA⟩
  have hTT : Star3T.IsTT (muDelta Ω W) :=
    isTT_muDelta c.hΩ c.hW (Q3CL.thompsonCube hP W c.hW)
  obtain ⟨d₀, hd₀, a₀, ha₀, hn₀⟩ :=
    exists_not_conn_of_not_connected c.hΩ c.hW hnc
  have hcls := hTT.exists_conj_of_not_conn hd₀ ha₀ hn₀
  obtain ⟨g₁, hg₁⟩ := hcls _ (T7D.imgQ_mem ρ)
  obtain ⟨g₂, hg₂⟩ := hcls _ (T7D.imgQ_mem σ)
  have hy : T7D.imgQ σ = (g₂ * g₁⁻¹) * T7D.imgQ ρ * (g₂ * g₁⁻¹)⁻¹ := by
    rw [hg₁, hg₂]
    group
  obtain ⟨m, hm, hmg⟩ := c.exists_mem_MGrp_piG_eq hclC (g₂ * g₁⁻¹)
  refine ⟨m, hm, ?_⟩
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_le_normalizer Ω W hm
  have himg : (T7D.conjRep c.hΩ hmN ρ).img = σ.img := by
    rw [T7D.conjRep_img, ← hmg]
    exact (congrArg Subtype.val hy).symm
  exact c.K_eq_of_img_eq (T7D.conjRep c.hΩ hmN ρ) σ himg

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.exists_conj_reps_of_mem_omegaStarNbr
    {K₁ J₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (hJ₁ : J₁ ∈ omegaStarNbr Ω K₁) :
    ∃ g : G, ∃ ρ σ : Rep Ω W, ρ.K = conjSub g K₁ ∧ σ.K = conjSub g J₁ := by
  obtain ⟨hJ₁Ω, -, U, hU, hUJ₁, hUN⟩ := hJ₁
  have hU2 : IsPGroup 2 U := c.hΩ.isPGroup_of_mem_USet hU
  obtain ⟨R, hRK, hRU⟩ := T3.exists_sylow_normalized hU2 hUN
  have hUR : U ≤ Subgroup.normalizer (R : Set G) := fun u hu =>
    mem_normalizer_iff_conjSub_eq.mpr (hRU u hu)
  obtain ⟨S₁, hS₁⟩ := (hU2.to_sup_of_normal_right' hRK.2.1 hUR).exists_le_sylow
  obtain ⟨S, hWS⟩ := exists_sylow_ge_of_mem_WSet c.hW
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₁ S
  have hUS : conjSub g U ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_left.trans hS₁)
    rwa [hg] at this
  have hRS : conjSub g R ≤ (S : Subgroup G) := by
    have := conjSub_mono (n := g) (le_sup_right.trans hS₁)
    rwa [hg] at this
  have hK' : conjSub g K₁ ∈ Ω := c.hΩ.conjInvariant g K₁ hK₁
  have hJ' : conjSub g J₁ ∈ Ω := c.hΩ.conjInvariant g J₁ hJ₁Ω
  have hR'K' : IsSylow2In (conjSub g R) (conjSub g K₁) := hRK.conj g
  have hR'D : conjSub g R ∈ DSet Ω W :=
    Q3CL.Thompson.mem_DSet_of_le_sylow c.hΩ c.hW hWS (mem_RSet_of_isSylow2In hK' hR'K') hRS
  obtain ⟨T, hTD, hTJ⟩ := Q3CL.Thompson.exists_sylow_mem_DSet c.hΩ c.hW hWS hJ'
    (USet.conj c.hΩ.conjInvariant hU g) (conjSub_mono hUJ₁) hUS
  obtain ⟨ρ, hρK, -⟩ := T7D.exists_rep c.hΩ c.hW hK' hR'K' hR'D
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep c.hΩ c.hW hJ' hTJ hTD
  exact ⟨g, ρ, σ, hρK, hσK⟩
end Ctx
end Thompson
section Frame
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' J W : Subgroup G} {z u t : G}
end Frame
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_fixed_muDelta_wylD4' (c : Q3CL.Thompson.Ctx Ω W) (hTT : Star3T.IsTT (muDelta Ω W))
    (hS : Star3T.IsStar (muDelta Ω W)) {a : G} (haN : a ∈ Subgroup.normalizer (W : Set G))
    (ha2 : a * a = 1) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) (hrW : r ∉ W)
    {x₀ a₀ : ↥(muGroup Ω W)} (hx₀Δ : x₀ ∈ muDelta Ω W)
    (hx₀ : (x₀ : NQuot (W ⊔ OCW W)) = piG W r) (ha₀ : a₀ ∈ muDelta Ω W)
    (hconn : ¬ Star3T.Conn (muDelta Ω W) x₀ a₀)
    (hk : (Star3T.cent (muDelta Ω W) x₀).ncard = 4) :
    ∃ x ∈ muDelta Ω W, conjQ c.hΩ haN x = x := by
  have hΩ : HypOmegaMod Ω := c.hΩ
  have hW : W ∈ WSet Ω := c.hW
  by_cases hfix : conjQ hΩ haN x₀ = x₀
  · exact ⟨x₀, hx₀Δ, hfix⟩
  have hyΔ : conjQ hΩ haN x₀ ∈ muDelta Ω W := conjQ_mem_muDelta hΩ haN hx₀Δ
  have hαy : conjQ hΩ haN (conjQ hΩ haN x₀) = x₀ := conjQ_conjQ hΩ haN ha2 x₀
  by_cases hcomm : x₀ * conjQ hΩ haN x₀ = conjQ hΩ haN x₀ * x₀
  swap
  · refine ⟨x₀ * conjQ hΩ haN x₀ * x₀, hTT.mul_mul_mem hx₀Δ hyΔ, ?_⟩
    rw [map_mul, map_mul, hαy]
    exact (hTT.braid hx₀Δ hyΔ hcomm).symm
  have hR' : conjSub a R ∈ DSet Ω W := Q3CL.Thompson.conjSub_mem_D hΩ hR haN
  have hr' : a * r * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hr
  have hr'W : a * r * a⁻¹ ∉ W := fun h => hrW ((mem_normalizer_iff_of_mem haN r).mp h)
  have hy' : ((conjQ hΩ haN x₀ : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) = piG W (a * r * a⁻¹) :=
    conjQ_val hΩ haN (hR.2 hr) hx₀
  have hDC : DComm W R (conjSub a R) := by
    refine dComm_of_commute hΩ hW hR hR' hr hr' hrW hr'W ?_ fun h => hfix (Subtype.ext ?_)
    · have := congrArg Subtype.val hcomm
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hy', hx₀] at this
      exact this
    · rw [hy', hx₀]
      exact h.symm
  obtain ⟨w, hwRW, hw4⟩ := exists_orderOf_four hΩ hW hR
  obtain ⟨v, hvd⟩ : ∃ v, v = a * w * a⁻¹ := ⟨_, rfl⟩
  have hvW : v ∈ W := hvd ▸ (mem_normalizer_iff_of_mem haN w).mpr hwRW.2
  have hv : v ∈ conjSub a R ⊓ W := ⟨hvd ▸ conj_mem_conjSub hwRW.1, hvW⟩
  have hv4 : orderOf v = 4 := by
    rw [hvd, ← hw4]
    exact orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective w
  obtain ⟨ψ, hψ⟩ := exists_perm_four_of_wv c hTT hS hR hR' hDC hr hrW hx₀ hx₀Δ ha₀ hconn hk hwRW hv
    hw4 hv4
  have hav := conj_mul_conj_eq hΩ hW ha2 hwRW.2 hvW hvd
  have hS' : ∀ x ∈ muDeltaCent Ω W (w * v), conjQ hΩ haN x ∈ muDeltaCent Ω W (w * v) := by
    intro x hx
    refine conjQ_mem_muDeltaOf hΩ haN
      (C := {T | T ∈ DSet Ω W ∧ T ≤ Subgroup.centralizer ({w * v} : Set G)})
      (fun T hT => ⟨Q3CL.Thompson.conjSub_mem_D hΩ hT.1 haN, fun z hz => ?_⟩) (fun T hT => hT.1) hx
    have hu : a⁻¹ * z * a ∈ T := mem_conjSub_iff.mp hz
    have hum : (a⁻¹ * z * a) * (w * v) = (w * v) * (a⁻¹ * z * a) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hT.2 hu)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : (a * (a⁻¹ * z * a) * a⁻¹) * (a * (w * v) * a⁻¹) =
        (a * (w * v) * a⁻¹) * (a * (a⁻¹ * z * a) * a⁻¹) := by
      have e1 : a * (a⁻¹ * z * a) * a⁻¹ * (a * (w * v) * a⁻¹) =
          a * ((a⁻¹ * z * a) * (w * v)) * a⁻¹ := by group
      have e2 : (a * (w * v) * a⁻¹) * (a * (a⁻¹ * z * a) * a⁻¹) =
          a * ((w * v) * (a⁻¹ * z * a)) * a⁻¹ := by group
      rw [e1, e2, hum]
    rw [hav] at h3
    have e3 : a * (a⁻¹ * z * a) * a⁻¹ = z := by group
    rwa [e3] at h3
  have hH : ∀ x ∈ Subgroup.closure (muDeltaCent Ω W (w * v)),
      conjQ hΩ haN x ∈ Subgroup.closure (muDeltaCent Ω W (w * v)) := by
    have : Subgroup.closure (muDeltaCent Ω W (w * v)) ≤
        (Subgroup.closure (muDeltaCent Ω W (w * v))).comap (conjQ hΩ haN).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro x hx
      exact Subgroup.subset_closure (hS' x hx)
    exact fun x hx => this hx
  obtain ⟨x, hxS, hxfix⟩ := Star3T.exists_fixed_of_perm_four (conjQ hΩ haN)
    (conjQ_conjQ hΩ haN ha2) hS' hH ψ hψ
  obtain ⟨T, hT, t, ht, htW, hxt⟩ := hxS
  exact ⟨x, ⟨T, hT.1, t, ht, htW, hxt⟩, hxfix⟩
end Thompson

theorem l7_12_proved : L7_12 := by
  intro G _ _ Ω hP W hW hnc a haN ha2
  have hΩ : HypOmegaMod Ω := hP.hyp
  refine Thompson.exists_fixed_member_of_muDelta_fixed hΩ hW haN ha2 ?_
  have hS : ∀ x ∈ Thompson.muDelta Ω W, Thompson.conjQ hΩ haN x ∈ Thompson.muDelta Ω W :=
    fun x hx => Thompson.conjQ_mem_muDelta hΩ haN hx
  have hαα := Thompson.conjQ_conjQ hΩ haN ha2
  have hTT := Thompson.isTT_muDelta hΩ hW (Q3CL.thompsonCube hP W hW)
  have hSt := Thompson.isStar_muDelta hΩ hW (thompsonStar G Ω hP W hW)
  obtain ⟨d, hd, a₀, ha₀, hconn⟩ := Thompson.exists_not_conn_of_not_connected hΩ hW hnc
  rcases thompsonClique G Ω hP W hW hnc d hd with hk | hk | ⟨hk, -⟩
  · obtain ⟨e, he⟩ := Star3T.exists_mulEquiv_perm_three hTT hSt hd ha₀ hconn hk
    exact Star3T.exists_fixed_of_perm_three (Thompson.conjQ hΩ haN) hαα hS (H := ⊤)
      (fun _ _ => Subgroup.mem_top _) (Subgroup.topEquiv.trans e) fun x _ => he x
  · obtain ⟨e, he⟩ := Star3T.exists_mulEquiv_perm_four hTT hSt hd ha₀ hconn hk
    exact Star3T.exists_fixed_of_perm_four (Thompson.conjQ hΩ haN) hαα hS (H := ⊤)
      (fun _ _ => Subgroup.mem_top _) (Subgroup.topEquiv.trans e) fun x _ => he x
  · obtain ⟨R, hR, r, hr, hrW, hxr⟩ := id hd
    exact Thompson.exists_fixed_muDelta_wylD4' ⟨hΩ, hW, Q3CL.thompsonKey hP W hW, hP.aEmpty⟩
      hTT hSt haN ha2 hR hr hrW hd hxr ha₀ hconn hk
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8

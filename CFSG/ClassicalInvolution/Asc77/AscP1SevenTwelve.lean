module

public import CFSG.ClassicalInvolution.Asc77.AscP1SevenSubMain
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenClique

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace Thompson

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_fixed_muDelta_wylD4' (c : Ctx p f Ω W) (hTT : Star3T.IsTT (muDelta Ω W))
    (hS : Star3T.IsStar (muDelta Ω W)) {a : G} (haN : a ∈ Subgroup.normalizer (W : Set G))
    (ha2 : a * a = 1) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) (hrW : r ∉ W)
    {x₀ a₀ : ↥(muGroup Ω W)} (hx₀Δ : x₀ ∈ muDelta Ω W)
    (hx₀ : (x₀ : NQuot (W ⊔ OCW W)) = piG W r) (ha₀ : a₀ ∈ muDelta Ω W)
    (hconn : ¬ Star3T.Conn (muDelta Ω W) x₀ a₀)
    (hk : (Star3T.cent (muDelta Ω W) x₀).ncard = 4) :
    ∃ x ∈ muDelta Ω W, conjQ c.hΩ haN x = x := by
  have hp : p ≠ 2 := c.hp
  have hq : 5 ≤ p ^ f := c.hq
  have hΩ : HypOmegaMod p f Ω := c.hΩ
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
  have hR' : conjSub a R ∈ DSet Ω W := conjSub_mem_D hΩ hR haN
  have hr' : a * r * a⁻¹ ∈ conjSub a R := conj_mem_conjSub hr
  have hr'W : a * r * a⁻¹ ∉ W := fun h => hrW ((mem_normalizer_iff_of_mem haN r).mp h)
  have hy' : ((conjQ hΩ haN x₀ : ↥(muGroup Ω W)) : NQuot (W ⊔ OCW W)) = piG W (a * r * a⁻¹) :=
    conjQ_val hΩ haN (hR.2 hr) hx₀
  have hDC : DComm W R (conjSub a R) := by
    refine dComm_of_commute hp hq hΩ hW hR hR' hr hr' hrW hr'W ?_ fun h => hfix (Subtype.ext ?_)
    · have := congrArg Subtype.val hcomm
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hy', hx₀] at this
      exact this
    · rw [hy', hx₀]
      exact h.symm
  obtain ⟨w, hwRW, hw4⟩ := exists_orderOf_four hp hq hΩ hW hR
  obtain ⟨v, hvd⟩ : ∃ v, v = a * w * a⁻¹ := ⟨_, rfl⟩
  have hvW : v ∈ W := hvd ▸ (mem_normalizer_iff_of_mem haN w).mpr hwRW.2
  have hv : v ∈ conjSub a R ⊓ W := ⟨hvd ▸ conj_mem_conjSub hwRW.1, hvW⟩
  have hv4 : orderOf v = 4 := by
    rw [hvd, ← hw4]
    exact orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective w
  obtain ⟨ψ, hψ⟩ := exists_perm_four_of_wv c hTT hS hR hR' hDC hr hrW hx₀ hx₀Δ ha₀ hconn hk hwRW hv
    hw4 hv4
  have hav := conj_mul_conj_eq hp hq hΩ hW ha2 hwRW.2 hvW hvd
  have hS' : ∀ x ∈ muDeltaCent Ω W (w * v), conjQ hΩ haN x ∈ muDeltaCent Ω W (w * v) := by
    intro x hx
    refine conjQ_mem_muDeltaOf hΩ haN
      (C := {T | T ∈ DSet Ω W ∧ T ≤ Subgroup.centralizer ({w * v} : Set G)})
      (fun T hT => ⟨conjSub_mem_D hΩ hT.1 haN, fun z hz => ?_⟩) (fun T hT => hT.1) hx
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

variable {p f : ℕ} [Fact p.Prime]

theorem l7_12_proved : L7_12 p f := by
  intro G _ _ Ω hP W hW hnc a haN ha2
  have hp : p ≠ 2 := hP.1
  have hq : 5 ≤ p ^ f := hP.2.1
  have hΩ : HypOmegaMod p f Ω := hP.2.2.1
  refine Thompson.exists_fixed_member_of_muDelta_fixed hp hq hΩ hW haN ha2 ?_
  have hS : ∀ x ∈ Thompson.muDelta Ω W, Thompson.conjQ hΩ haN x ∈ Thompson.muDelta Ω W :=
    fun x hx => Thompson.conjQ_mem_muDelta hΩ haN hx
  have hαα := Thompson.conjQ_conjQ hΩ haN ha2
  have hTT := Thompson.isTT_muDelta hp hq hΩ hW (thompsonCube G Ω hP W hW)
  have hSt := Thompson.isStar_muDelta hp hq hΩ hW (thompsonStar G Ω hP W hW)
  obtain ⟨d, hd, a₀, ha₀, hconn⟩ := Thompson.exists_not_conn_of_not_connected hp hq hΩ hW hnc
  rcases thompsonClique G Ω hP W hW hnc d hd with hk | hk | ⟨hk, -⟩
  · obtain ⟨e, he⟩ := Star3T.exists_mulEquiv_perm_three hTT hSt hd ha₀ hconn hk
    exact Star3T.exists_fixed_of_perm_three (Thompson.conjQ hΩ haN) hαα hS (H := ⊤)
      (fun _ _ => Subgroup.mem_top _) (Subgroup.topEquiv.trans e) fun x _ => he x
  · obtain ⟨e, he⟩ := Star3T.exists_mulEquiv_perm_four hTT hSt hd ha₀ hconn hk
    exact Star3T.exists_fixed_of_perm_four (Thompson.conjQ hΩ haN) hαα hS (H := ⊤)
      (fun _ _ => Subgroup.mem_top _) (Subgroup.topEquiv.trans e) fun x _ => he x
  · obtain ⟨R, hR, r, hr, hrW, hxr⟩ := id hd
    exact Thompson.exists_fixed_muDelta_wylD4' ⟨hp, hq, hΩ, hW, thompsonKey G Ω hP W hW, hP.2.2.2⟩
      hTT hSt haN ha2 hR hr hrW hd hxr ha₀ hconn hk

end CFSG.ClassicalInvolution.Asc77

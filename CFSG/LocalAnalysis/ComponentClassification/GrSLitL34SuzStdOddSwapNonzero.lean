module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapRoot
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapResidual
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapBar
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddSwapLift

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G] {A V K : Subgroup G} {t y : G}

theorem false_of_map_conj_eq_map_of_l34SuzOdd
    (hAut2A : SuzTwoACentralizerAutExtension) (h2AF : SuzTwoAFusion)
    (h2AC : SuzTwoACentralizerFacts) (hRig : SuzTwoBRootRigidity)
    (hS : L34SuzOddSetting A t) (hD : L34SuzOddData A V K y) {u : G} (hu : u ∈ V) (hu1 : u ≠ 1)
    {P : Subgroup G}
    (hc : P ≤ centralizer ((P.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G))
    (hPu : P ≤ centralizer ({u} : Set G))
    (hcomp : IsComponent (P.subgroupOf (centralizer ({u} : Set G))))
    (hne : P.map (MulAut.conj t).toMonoidHom ≠ P) (hK : K = (HarrisLit.swapDiag P t hc).range)
    {v : G} (hv : v ∈ V)
    (hvP : P.map (MulAut.conj v).toMonoidHom = P.map (MulAut.conj t).toMonoidHom) : False := by
  have hp2 : ∀ {M : Type} [Group M] {x : M}, x * x = 1 → IsPGroup 2 (zpowers x) := by
    intro M _ x hx
    have h : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx)
    rcases (Nat.dvd_prime Nat.prime_two).1 h with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1]; rfl)
  obtain ⟨a, haP, ha, hat⟩ :=
    exists_root_involution_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hne hK
  obtain ⟨d, hd⟩ : ∃ d : G, d = a * (t * a * t⁻¹) := ⟨_, rfl⟩
  obtain ⟨hdK, hd1, hd2, hau, hatd, havd, hadd⟩ :=
    root_identities_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hK hv hvP haP ha hat hd
  have hdA : d ∈ A := le_A_of_l34SuzOddData hD hdK
  have hEu := sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD (mem_sup_left hu)
  have hEv := sup_zpowers_le_centralizer_inf_of_l34SuzOdd hS hD (mem_sup_left hv)
  have hud : u * d = d * u := (mem_centralizer_iff.mp hEu.2 d hdK).symm
  have hvd : v * d = d * v := (mem_centralizer_iff.mp hEv.2 d hdK).symm
  have huA : u ∈ A := hD.le_A hu
  have hvA : v ∈ A := hD.le_A hv
  have hu2 : u * u = 1 := hD.mul_self u hu
  have hW := isSuzTwoBFour_map_of_l34SuzOdd hS hD
  have hπK := map_subgroupOf_eq_commutator_of_l34SuzOdd hS hD
  generalize hWdef : (V.subgroupOf A).map (QuotientGroup.mk' (center ↥A)) = W at hW hπK
  have hdW : QuotientGroup.mk' (center ↥A) (⟨d, hdA⟩ : ↥A) ∈
      ⁅centralizer (W : Set (↥A ⧸ center ↥A)), centralizer (W : Set (↥A ⧸ center ↥A))⁆ := by
    rw [← hπK]
    exact ⟨⟨d, hdA⟩, hdK, rfl⟩
  have hdo : orderOf (QuotientGroup.mk' (center ↥A) (⟨d, hdA⟩ : ↥A)) = 2 :=
    orderOf_mk'_eq_two_of_l34SuzOdd hS (Subtype.ext hd2) fun h => hd1 (congrArg Subtype.val h)
  have hcard := h2AF hS.suz W hW _ hdW hdo
  obtain ⟨hperf, hcen⟩ := h2AC hS.suz hdo hcard
  have hL := map_conj_centralizerResidual_eq_of_l34SuzOdd hS hatd hadd
  obtain ⟨α, hα⟩ := exists_mulAut_centralizer_of_l34SuzOdd hS hdA hd2 hperf hcen hL
  obtain ⟨β, hβd, hβ⟩ := hAut2A hS.suz hdo hcard α
  have hmemC : ∀ x : ↥A, (x : G) * d = d * x →
      QuotientGroup.mk' (center ↥A) x ∈
        centralizer ({QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩} : Set (↥A ⧸ center ↥A)) := by
    intro x hx
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hx)
  have key : ∀ x y : ↥A, (x : G) ∈ HarrisLit.centralizerResidual A d →
      (y : G) = a * x * a⁻¹ → (x : G) * d = d * x → (y : G) * d = d * y →
      β (QuotientGroup.mk' (center ↥A) x) = QuotientGroup.mk' (center ↥A) y := by
    intro x y hxL hxy hxd hyd
    have h := hβ ⟨_, hmemC x hxd⟩
    rw [hα x y hxL hxy (hmemC x hxd) (hmemC y hyd)] at h
    exact h
  have hβu : β (QuotientGroup.mk' (center ↥A) ⟨u, huA⟩) =
      QuotientGroup.mk' (center ↥A) ⟨u, huA⟩ :=
    key ⟨u, huA⟩ ⟨u, huA⟩
      (mem_centralizerResidual_of_isPGroup_of_l34SuzOdd hS hdA hd2 hperf huA hud (hp2 hu2))
      hau.symm hud hud
  have hβv : β (QuotientGroup.mk' (center ↥A) ⟨v, hvA⟩) =
      QuotientGroup.mk' (center ↥A) ⟨d * v, mul_mem hdA hvA⟩ :=
    key ⟨v, hvA⟩ ⟨d * v, mul_mem hdA hvA⟩
      (mem_centralizerResidual_of_isPGroup_of_l34SuzOdd hS hdA hd2 hperf hvA hvd
        (hp2 (hD.mul_self v hv)))
      havd.symm hvd (by change d * v * d = d * (d * v); rw [mul_assoc, hvd])
  have hdev : ∀ x ∈ ⁅centralizer (W : Set (↥A ⧸ center ↥A)),
      centralizer (W : Set (↥A ⧸ center ↥A))⁆,
      x * QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩ = QuotientGroup.mk' (center ↥A) ⟨d, hdA⟩ * x →
      IsPGroup 2 (zpowers x) →
        β x = x ∨ β x = QuotientGroup.mk' (center ↥A) ⟨u, huA⟩ * x := by
    intro x hx hxd hx2
    rw [← hπK] at hx
    obtain ⟨r, hrK, hrd, hr2, rfl⟩ := exists_lift_of_l34SuzOdd hS hD hdA hdK hd2 hx hxd hx2
    have hrL := mem_centralizerResidual_of_isPGroup_of_l34SuzOdd hS hdA hd2 hperf r.2 hrd hr2
    have hraL : a * r * a⁻¹ ∈ HarrisLit.centralizerResidual A d := by
      rw [← hL]
      exact ⟨r, hrL, rfl⟩
    have hraA : a * r * a⁻¹ ∈ A := HarrisLit.centralizerResidual_le_left hraL
    have hrad : a * r * a⁻¹ * d = d * (a * r * a⁻¹) :=
      mem_centralizer_singleton_iff.mp (HarrisLit.centralizerResidual_le hraL).2
    have hk := key r ⟨a * r * a⁻¹, hraA⟩ hrL rfl hrd hrad
    rcases conj_eq_or_eq_mul_of_l34SuzOdd hS hD hu hu1 hc hPu hcomp hne hK hv hvP haP ha hrK
        (by rw [← hd]; exact hrd) hraA with h | h
    · left
      rw [hk]
      exact congrArg _ (Subtype.ext h)
    · right
      rw [hk, ← map_mul]
      exact congrArg _ (Subtype.ext h)
  have huo := orderOf_mk'_eq_two_of_l34SuzOdd hS (x := ⟨u, huA⟩) (Subtype.ext hu2)
    fun h => hu1 (congrArg Subtype.val h)
  have hub1 : QuotientGroup.mk' (center ↥A) (⟨u, huA⟩ : ↥A) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huo
    exact absurd huo (by norm_num)
  have hubW : QuotientGroup.mk' (center ↥A) (⟨u, huA⟩ : ↥A) ∈ W := by
    rw [← hWdef]
    exact ⟨⟨u, huA⟩, hu, rfl⟩
  have hvbW : QuotientGroup.mk' (center ↥A) (⟨v, hvA⟩ : ↥A) ∈ W := by
    rw [← hWdef]
    exact ⟨⟨v, hvA⟩, hv, rfl⟩
  have hfix := hRig hS.suz W hW _ hubW hub1 _ hdW hdo β hβu hβd hdev _ hvbW
  rw [hβv] at hfix
  have h1 : QuotientGroup.mk' (center ↥A) (⟨d, hdA⟩ : ↥A) = 1 := by
    have h' : QuotientGroup.mk' (center ↥A) (⟨d, hdA⟩ : ↥A) *
        QuotientGroup.mk' (center ↥A) ⟨v, hvA⟩ = QuotientGroup.mk' (center ↥A) ⟨v, hvA⟩ := by
      rw [← map_mul]
      exact hfix
    simpa using h'
  rw [h1, orderOf_one] at hdo
  exact absurd hdo (by norm_num)

end CFSG.ComponentClassification.GrSLit.L34Sec5S

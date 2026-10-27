module

public import CFSG.CGT.PushingUpLit.SolK.TwoB
public import CFSG.CGT.PushingUpLit.SolK.HAway
public import CFSG.CGT.PushingUpLit.SolK.Arith
public import CFSG.CGT.PushingUpLit.SolK.TwoA

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : SolCfg G M X n)

namespace SolCfg

include S

theorem coord_eq_of_comm (hR : RSmall S) {t : G} (htM : t ∈ M) {i j : Fin (2 * n + 1)}
    (hθ : S.θ ⟨t, htM⟩ = swap i j) {z : ↥(pCoreOf 2 M)} (hz : t * (z : G) * t⁻¹ = (z : G)) :
    (i ∈ S.suppQ z ↔ j ∈ S.suppQ z) := by
  obtain ⟨r', hr', hzr⟩ := projWFun_spec S z
  have hw' : (projWFun S z : G) ∈ S.D.W := (projWFun S z).2
  have hcent := SolCfg.RSmall.central S hR htM hr'
  have hW' : t * (projWFun S z : G) * t⁻¹ ∈ S.D.W := S.W_normalized htM hw'
  have h1 : t * (projWFun S z : G) * t⁻¹ = (projWFun S z : G) := by
    have h2 : (t * (projWFun S z : G) * t⁻¹) * r' = (projWFun S z : G) * r' := by
      calc (t * (projWFun S z : G) * t⁻¹) * r' =
          (t * (projWFun S z : G) * t⁻¹) * (t * r' * t⁻¹) := by rw [hcent]
        _ = t * ((projWFun S z : G) * r') * t⁻¹ := by group
        _ = (projWFun S z : G) * r' := by rw [← hzr]; exact hz
    exact (S.decomp_unique hW' hw' hr' hr' h2).1
  have h3 := S.θ_spec ⟨t, htM⟩ (projWFun S z) hW'
  have h4 : (⟨t * (projWFun S z : G) * t⁻¹, hW'⟩ : ↥S.D.W) = projWFun S z := Subtype.ext h1
  rw [h4, hθ] at h3
  have h5 := congrArg (fun v => vcoord v i) h3
  simp only [vcoord_coreAct, Equiv.swap_inv, swap_apply_left] at h5
  rw [S.mem_suppQ, S.mem_suppQ]
  rw [h5]

theorem normalizer_TOf_le_M_two (hT : TightData S) (hQe : QElem S) (hR : RSmall S)
    (hn4 : 4 ≤ n) {w r : G} (hw : w ∈ S.D.W) (hr : r ∈ rOf M X)
    (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 2) (hKM : ¬ CGOf (w * r) ≤ M) :
    Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) ≤ M := by
  classical
  intro g hg
  by_contra hgM
  have hxQ : w * r ∈ pCoreOf 2 M := S.mul_mem_Q hw hr
  have hx1 : w * r ≠ 1 := S.mul_ne_one hw hr (by omega)
  obtain ⟨i, j, hij, hI⟩ := Finset.card_eq_two.1 hcard
  have hTQ := S.not_TOf_le_Q hT hxQ hx1 hKM
  obtain ⟨t, htT, htQ⟩ := IsConcreteLE.not_le_iff_exists.1 hTQ
  have htM : t ∈ M := TOf_le_M M _ htT
  have hθt : S.θ ⟨t, htM⟩ = swap i j := by
    rcases S.eq_one_or_swap_of_two hw hr hcard hij hI (TOf_le_M M _) (TOf_le_C M _)
      (isPGroup_TOf M _) (fun k hk u hu => normalized_TOf M (w * r) hk hu)
      (Subgroup.mem_map.2 ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.2 htT, rfl⟩) with h | h
    · exact absurd (S.mem_Q_of_theta_eq_one hR htM h) htQ
    · exact h
  set Z : Subgroup G := TOf M (w * r) ⊓ Subgroup.centralizer ((TOf M (w * r) : Subgroup G) : Set G)
    with hZ
  have hQT := S.Q_le_TOf hT hxQ
  have hZQ : Z ≤ pCoreOf 2 M := by
    intro z hz
    have hzM : z ∈ M := TOf_le_M M _ hz.1
    refine S.mem_Q_of_theta_eq_one hR hzM ?_
    refine (theta_eq_one_iff S.D S.xnorm S.hyp.two_le ⟨z, hzM⟩).2 fun w' hw' => ?_
    have h1 := Subgroup.mem_centralizer_iff.1 hz.2 w' (hQT (S.W_le_Q hw'))
    show z * w' * z⁻¹ = w'
    calc z * w' * z⁻¹ = (w' * z) * z⁻¹ := by rw [h1]
      _ = w' := by group
  have hDg : ∀ h ∈ Z, g⁻¹ * h * g ∈ pCoreOf 2 M := by
    intro h hh
    have hginv : g⁻¹ ∈ Subgroup.normalizer ((TOf M (w * r) : Subgroup G) : Set G) :=
      (Subgroup.normalizer _).inv_mem hg
    have hmemT : g⁻¹ * h * g ∈ TOf M (w * r) := by
      have := (Subgroup.mem_normalizer_iff.1 hginv h).1 hh.1
      simpa using this
    have hcentT : ∀ τ ∈ TOf M (w * r), τ * (g⁻¹ * h * g) = (g⁻¹ * h * g) * τ := by
      intro τ hτ
      have hτ' : g * τ * g⁻¹ ∈ TOf M (w * r) := (Subgroup.mem_normalizer_iff.1 hg τ).1 hτ
      have h1 := Subgroup.mem_centralizer_iff.1 hh.2 _ hτ'
      calc τ * (g⁻¹ * h * g) = g⁻¹ * ((g * τ * g⁻¹) * h) * g := by group
        _ = g⁻¹ * (h * (g * τ * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * h * g) * τ := by group
    exact hZQ ⟨hmemT, Subgroup.mem_centralizer_iff.2 hcentT⟩
  have hCt : pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G) ≤ Z := by
    intro q hq
    have hqt : q * t = t * q := Subgroup.mem_centralizer_singleton_iff.1 hq.2
    refine ⟨hQT hq.1, Subgroup.mem_centralizer_iff.2 fun τ hτ => ?_⟩
    have hτM : τ ∈ M := TOf_le_M M _ hτ
    have hcases : S.θ ⟨τ, hτM⟩ = 1 ∨ S.θ ⟨τ, hτM⟩ = swap i j :=
      S.eq_one_or_swap_of_two hw hr hcard hij hI (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
        (fun k hk u hu => normalized_TOf M (w * r) hk hu)
        (Subgroup.mem_map.2 ⟨⟨τ, hτM⟩, Subgroup.mem_subgroupOf.2 hτ, rfl⟩)
    rcases hcases with h | h
    · exact (hT.abelian _ (S.mem_Q_of_theta_eq_one hR hτM h) q hq.1)
    · have hM' : τ * t⁻¹ ∈ M := M.mul_mem hτM (M.inv_mem htM)
      have hdiv : τ * t⁻¹ ∈ pCoreOf 2 M := by
        refine S.mem_Q_of_theta_eq_one hR hM' ?_
        have : (⟨τ * t⁻¹, hM'⟩ : ↥M) = ⟨τ, hτM⟩ * ⟨t, htM⟩⁻¹ := rfl
        rw [this, map_mul, map_inv, h, hθt, mul_inv_cancel]
      have h1 : (τ * t⁻¹) * q = q * (τ * t⁻¹) := (hT.abelian _ hdiv q hq.1)
      calc τ * q = (τ * t⁻¹) * (t * q) := by group
        _ = (τ * t⁻¹) * (q * t) := by rw [hqt]
        _ = ((τ * t⁻¹) * q) * t := by group
        _ = (q * (τ * t⁻¹)) * t := by rw [h1]
        _ = q * τ := by group
  have hcentQ := S.card_Q_le_two_mul_cent hR htM hij hθt
  have hZc : Nat.card ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({t} : Set G)) ≤ Nat.card ↥Z :=
    Subgroup.card_le_of_le hCt
  have hA := S.hAway_of_four_le hT hQe hR hn4
  have hcl := S.card_le_of_conj_inter hT hQe hA hgM hZQ hDg
  have hD2 := S.card_D2_le (D := Z) hZQ hij (fun h => by
    refine S.coord_eq_of_comm hR htM hθt (z := ⟨h, hZQ h.2⟩) ?_
    have h1 := Subgroup.mem_centralizer_iff.1 h.2.2 t htT
    show t * (h : G) * t⁻¹ = (h : G)
    calc t * (h : G) * t⁻¹ = ((h : G) * t) * t⁻¹ := by rw [h1]
      _ = (h : G) := by group)
  have hQ2 := S.card_Q2_le
  have hRpos : 1 ≤ Nat.card ↥(rOf M X) := Nat.card_pos
  have hcardQ := S.card_Q
  have hW : Nat.card ↥S.D.W = Nat.card ↥(coreMod (2 * n + 1)) := Nat.card_congr S.D.β.toEquiv
  have hmul := card_coreMod_mul_two (n := 2 * n + 1) (odd_two_mul_add_one n)
  have hineq := counting_ineq (2 * n + 1) (Nat.card ↥(rOf M X)) (by omega) hRpos
  have hpow : (2 : ℕ) ^ (2 * n + 1) = 8 * 2 ^ (2 * n + 1 - 3) := by
    have : 2 * n + 1 = (2 * n + 1 - 3) + 3 := by omega
    conv_lhs => rw [this]
    rw [pow_add]
    ring
  rw [hcardQ, hW] at hcentQ
  have hmain : Nat.card ↥(coreMod (2 * n + 1)) * 2 = 2 ^ (2 * n + 1) := hmul
  nlinarith [hcentQ, hZc, hcl, hD2, hQ2, hineq, hpow, hmain]

end SolCfg

end CFSG.CGT.PushingUpLit.SolK

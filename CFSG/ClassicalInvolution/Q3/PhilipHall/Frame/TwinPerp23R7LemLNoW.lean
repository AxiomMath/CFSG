module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLP
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Abs
public import CFSG.ClassicalInvolution.Q3.Q3CLWylA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLSecV
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLT237
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTrans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTri
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTwin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section S4

open Equiv

theorem s3_eq_of_comm_sq : ∀ p q : Perm (Fin 3), p * p = 1 → q * q = 1 → p * q = q * p →
    p = 1 ∨ q = 1 ∨ p = q := by
  decide +kernel

theorem s4_comm_three : ∀ a v : Perm (Fin 4), a ^ 3 = 1 → a ≠ 1 → v * v = 1 → v ≠ 1 →
    a * v ≠ v * a := by
  decide +kernel

theorem s4_pow_twelve : ∀ a : Perm (Fin 4), a ^ 12 = 1 := by
  decide +kernel

theorem s4_eq_top_of_hasS3Quot {H : Subgroup (Perm (Fin 4))} (hH : HasS3Quot ↥H)
    {x x' : Perm (Fin 4)} (hx : x ∈ H) (hx' : x' ∈ H) (hx1 : x ≠ 1) (hx'1 : x' ≠ 1)
    (hne : x ≠ x') (hx2 : x * x = 1) (hx'2 : x' * x' = 1) (hc : x * x' = x' * x) : H = ⊤ := by
  obtain ⟨π, hπ⟩ := hH
  have hy2 : (⟨x, hx⟩ * ⟨x, hx⟩ : ↥H) = 1 := Subtype.ext hx2
  have hy'2 : (⟨x', hx'⟩ * ⟨x', hx'⟩ : ↥H) = 1 := Subtype.ext hx'2
  have hyc : (⟨x, hx⟩ * ⟨x', hx'⟩ : ↥H) = ⟨x', hx'⟩ * ⟨x, hx⟩ := Subtype.ext hc
  have hp := s3_eq_of_comm_sq (π ⟨x, hx⟩) (π ⟨x', hx'⟩) (by rw [← map_mul, hy2, map_one])
    (by rw [← map_mul, hy'2, map_one]) (by rw [← map_mul, ← map_mul, hyc])
  obtain ⟨v, hv1, hv2, hvk⟩ : ∃ v : ↥H, (v : Perm (Fin 4)) ≠ 1 ∧
      (v : Perm (Fin 4)) * v = 1 ∧ π v = 1 := by
    rcases hp with h | h | h
    · exact ⟨⟨x, hx⟩, hx1, hx2, h⟩
    · exact ⟨⟨x', hx'⟩, hx'1, hx'2, h⟩
    · refine ⟨⟨x, hx⟩ * ⟨x', hx'⟩, fun h1 => hne ?_, ?_, ?_⟩
      · have h1' : x * x' = 1 := h1
        calc x = x * (x' * x') := by rw [hx'2, mul_one]
          _ = x * x' * x' := by rw [mul_assoc]
          _ = x' := by rw [h1', one_mul]
      · show x * x' * (x * x') = 1
        calc x * x' * (x * x') = x * (x' * x) * x' := by simp only [mul_assoc]
          _ = x * (x * x') * x' := by rw [hc]
          _ = (x * x) * (x' * x') := by simp only [mul_assoc]
          _ = 1 := by rw [hx2, hx'2, one_mul]
      · rw [map_mul, h, ← map_mul, hy'2, map_one]
  have hv1' : v ≠ 1 := fun h => hv1 (congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := hπ (Equiv.swap 0 1 * Equiv.swap 1 2)
  have ha4 : π (a ^ 4) = Equiv.swap 0 1 * Equiv.swap 1 2 := by
    rw [map_pow, ha]
    decide
  have ha3 : ((a ^ 4 : ↥H) : Perm (Fin 4)) ^ 3 = 1 := by
    rw [Subgroup.coe_pow, ← pow_mul]
    exact s4_pow_twelve _
  have ha1 : ((a ^ 4 : ↥H) : Perm (Fin 4)) ≠ 1 := by
    intro h
    have h1 : a ^ 4 = 1 := Subtype.ext h
    rw [h1, map_one] at ha4
    exact absurd ha4 (by decide)
  have hvN : v ∈ π.ker := hvk
  have hwN : a ^ 4 * v * (a ^ 4)⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hvk, mul_one, mul_inv_cancel]
  have hw1 : a ^ 4 * v * (a ^ 4)⁻¹ ≠ 1 := fun h => hv1' (by
    calc v = (a ^ 4)⁻¹ * (a ^ 4 * v * (a ^ 4)⁻¹) * a ^ 4 := by group
      _ = 1 := by rw [h]; group)
  have hwv : a ^ 4 * v * (a ^ 4)⁻¹ ≠ v := by
    intro h
    refine s4_comm_three _ _ ha3 ha1 hv2 hv1 ?_
    have h' : a ^ 4 * v = v * a ^ 4 := by
      calc a ^ 4 * v = a ^ 4 * v * (a ^ 4)⁻¹ * a ^ 4 := by group
        _ = v * a ^ 4 := by rw [h]
    exact congrArg Subtype.val h'
  have h6 : Nat.card (Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
    rfl
  have h24 : Nat.card (Perm (Fin 4)) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
    rfl
  have hcard : Nat.card π.ker * 6 = Nat.card ↥H := by
    have h := Subgroup.card_ker_mul_card_of_surjective hπ
    rwa [h6] at h
  have hdvd : Nat.card π.ker * 6 ∣ 24 := by
    rw [hcard, ← h24]
    exact Subgroup.card_subgroup_dvd_card H
  have hpos : 0 < Nat.card π.ker := Nat.card_pos
  have hle : Nat.card π.ker ≤ 4 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hne1 : Nat.card π.ker ≠ 1 := by
    intro h
    have hb : π.ker = ⊥ := Subgroup.card_eq_one.mp h
    rw [hb] at hvN
    exact hv1' (Subgroup.mem_bot.mp hvN)
  have hne2 : Nat.card π.ker ≠ 2 := by
    intro h
    obtain ⟨z, -, hz⟩ := (Nat.card_eq_two_iff' (1 : ↥π.ker)).mp h
    have e1 : (⟨v, hvN⟩ : ↥π.ker) = z := hz _ (fun h' => hv1' (congrArg Subtype.val h'))
    have e2 : (⟨_, hwN⟩ : ↥π.ker) = z := hz _ (fun h' => hw1 (congrArg Subtype.val h'))
    exact hwv (congrArg Subtype.val (e2.trans e1.symm))
  have hk : Nat.card π.ker = 4 := by
    rcases (show Nat.card π.ker = 1 ∨ Nat.card π.ker = 2 ∨ Nat.card π.ker = 3 ∨
        Nat.card π.ker = 4 by omega) with h | h | h | h
    · exact absurd h hne1
    · exact absurd h hne2
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
  exact (Subgroup.card_eq_iff_eq_top H).mp (by rw [← hcard, hk, h24])

end S4

section WType

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem mem_center_of_wSet (F : Q8Pre X Φ) {K K' : Subgroup X} (hK : K ∈ Φ)
    (hK'tw : K' ∈ twinSet Φ K) (hne : K' ≠ K)
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set X) → J = K')
    (hperp' : ∀ J ∈ Φ, J ≠ K' → J ≤ Subgroup.normalizer (K' : Set X) → J = K) {a : X}
    (ha : HasS3Quot ↥(Ea Φ a)) (haK : K ≤ Subgroup.centralizer ({a} : Set X))
    (haK' : K' ≤ Subgroup.centralizer ({a} : Set X)) {W : Subgroup X} (hW1 : WSet Φ = {W}) :
    a ∈ Subgroup.center X := by
  have hΦ := F.hyp
  have h2 := F.two
  have hK'Φ : K' ∈ Φ := hK'tw.1
  have hW : W ∈ WSet Φ := by rw [hW1]; rfl
  have hP : Q3CL.PartIHypG Φ := ⟨hΦ, TC.Thin.classicalClause_of_two hΦ h2, F.aEmpty⟩
  have hWn : ∀ g : X, conjSub g W = W := fun g => by
    have := WSet.conj hΦ.conjInvariant hW g
    rwa [hW1] at this
  have hNW : ∀ g : X, g ∈ Subgroup.normalizer (W : Set X) := fun g =>
    mem_normalizer_iff_conjSub_eq.mpr (hWn g)
  have hW2 : IsPGroup 2 ↥W := Asc77.Thompson.isPGroup_of_mem_WSet hW
  have hOCW : OCW W = ⊥ := by
    haveI : (OCW W).Normal := ⟨fun y hy g => by
      have h := conj_mem_conjSub (n := g) hy
      rwa [mem_normalizer_iff_conjSub_eq.mp
        (Asc77.Thompson.normalizer_le_normalizer_OCW W (hNW g))] at h⟩
    have h := Hall196.le_classicalInvolutionOddCore (N := OCW W)
      (oddCoreOf_odd_natCard (Subgroup.centralizer (W : Set X)))
    rw [F.oddFree] at h
    exact le_bot_iff.mp h
  have hsyl : ∀ L ∈ Φ, IsSylow2In L L := fun L hL =>
    ⟨le_rfl, h2 L hL, fun V hVL _ hLV => le_antisymm hVL hLV⟩
  have hD : ∀ L ∈ Φ, L ∈ DSet Φ W := fun L hL =>
    ⟨mem_RSet_of_isSylow2In hL (hsyl L hL), fun x _ => hNW x⟩
  have hnW : ∀ L ∈ Φ, ∃ r ∈ L, r ∉ W := fun L hL =>
    Q3CL.Thompson.exists_not_mem_of_mem_D hΦ hW (hD L hL)
  have hrW : ∀ (g : X) {r : X}, r ∉ W → g * r * g⁻¹ ∉ W := fun g r hr h => hr (by
    have h' := conj_mem_conjSub (n := g⁻¹) h
    rwa [hWn, show g⁻¹ * (g * r * g⁻¹) * g⁻¹⁻¹ = r by group] at h')
  obtain ⟨r₀, hr₀, hr₀W⟩ := hnW K hK
  obtain ⟨r₁, hr₁, hr₁W⟩ := hnW K' hK'Φ
  obtain ⟨ρ₀, hρ₀, hρ₀r⟩ : ∃ ρ : Asc77.Thompson.Rep Φ W, ρ.K = K ∧ ρ.r = r₀ :=
    ⟨⟨K, K, r₀, hK, hD K hK, hsyl K hK, hr₀, hr₀W⟩, rfl, rfl⟩
  obtain ⟨ρ₁, hρ₁, hρ₁r⟩ : ∃ ρ : Asc77.Thompson.Rep Φ W, ρ.K = K' ∧ ρ.r = r₁ :=
    ⟨⟨K', K', r₁, hK'Φ, hD K' hK'Φ, hsyl K' hK'Φ, hr₁, hr₁W⟩, rfl, rfl⟩
  have hK'K : K' ∈ omegaNbr Φ K := by
    obtain ⟨-, z, hz, hz'⟩ := hK'tw
    exact Q3CL.T3.twin_mem_omegaNbr hΦ hK hK'Φ hne hz hz'
  have hnbK : ∀ N, N ∈ omegaNbr Φ K → N = K' := fun N h => by
    obtain ⟨hN, hNK, hNn⟩ := (TC.mem_omegaNbr_iff hΦ h2).mp h
    exact hperp N hN hNK hNn
  have hnbK' : ∀ N, N ∈ omegaNbr Φ K' → N = K := fun N h => by
    obtain ⟨hN, hNK, hNn⟩ := (TC.mem_omegaNbr_iff hΦ h2).mp h
    exact hperp' N hN hNK hNn
  have hnb : ∀ {M N : Subgroup X}, M ∈ Φ → N ∈ Φ → Disconnected.dAdj Φ M N →
      N ∈ omegaNbr Φ M := by
    intro M N hM hN h
    rcases h with h | h
    · exact h
    · exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΦ hN hM h
  have hcomp : ∀ J ∈ dComp Φ K, J = K ∨ J = K' := by
    intro J hJ
    change Relation.ReflTransGen
      (fun M N : Subgroup X => N ∈ Φ ∧ Disconnected.dAdj Φ M N) K J at hJ
    induction hJ with
    | refl => exact Or.inl rfl
    | tail _ hMN ih =>
      obtain ⟨hN, hadj⟩ := hMN
      rcases ih with h | h
      · rw [h] at hadj
        exact Or.inr (hnbK _ (hnb hK hN hadj))
      · rw [h] at hadj
        exact Or.inl (hnbK' _ (hnb hK'Φ hN hadj))
  obtain ⟨J, hJ, hJK, hJK'⟩ := exists_third_member hΦ h2 hK hK'tw hne ha
  obtain ⟨rJ, hrJ, hrJW⟩ := hnW J hJ
  obtain ⟨ρJ, hρJ⟩ : ∃ ρ : Asc77.Thompson.Rep Φ W, ρ.K = J :=
    ⟨⟨J, J, rJ, hJ, hD J hJ, hsyl J hJ, hrJ, hrJW⟩, rfl⟩
  have hJs : J ∈ dstarComp Φ K := by
    have h := Q3T6.Mu.muTab_omegaStar hP hW ρ₀ ρJ (by rw [hρ₀, hρJ]; exact Ne.symm hJK)
    rw [hρ₀, hρJ] at h
    exact Relation.ReflTransGen.single ⟨hJ, Or.inl h⟩
  have hnc : ¬ DbarConnected Φ W := by
    refine Q3T8.Asc77.thompsonGraphAll X Φ hP hK (fun h => ?_) hW
    rw [← h] at hJs
    rcases hcomp J hJs with h1 | h1
    · exact hJK h1
    · exact hJK' h1
  have hne01 : MuTab.muTabElt ρ₀ ≠ MuTab.muTabElt ρ₁ := by
    intro h
    have h' := (Q3T6.Mu.muTabElt_eq_iff hP hW ρ₀ ρ₁).mp h
    rw [hρ₀, hρ₁] at h'
    exact hne h'.symm
  have hcomm01 : MuTab.muTabElt ρ₀ * MuTab.muTabElt ρ₁ =
      MuTab.muTabElt ρ₁ * MuTab.muTabElt ρ₀ :=
    (Q3T6.Mu.muTab_commute_iff hP hW ρ₀ ρ₁ (by rw [hρ₀, hρ₁]; exact hne.symm)).mpr
      (by rw [hρ₀, hρ₁]; exact hK'K)
  have hcent : Star3T.cent (Asc77.Thompson.muDelta Φ W) (MuTab.muTabElt ρ₀) =
      {MuTab.muTabElt ρ₀, MuTab.muTabElt ρ₁} := by
    ext d
    constructor
    · rintro ⟨hd, hdc⟩
      obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hd
      by_cases hσ : σ.K = K
      · left
        exact (Q3T6.Mu.muTabElt_eq_iff hP hW σ ρ₀).mpr (hσ.trans hρ₀.symm)
      · right
        have h := (Q3T6.Mu.muTab_commute_iff hP hW ρ₀ σ
          (by rw [hρ₀]; exact Ne.symm hσ)).mp hdc.symm
        rw [hρ₀] at h
        exact (Q3T6.Mu.muTabElt_eq_iff hP hW σ ρ₁).mpr ((hnbK _ h).trans hρ₁.symm)
    · rintro (rfl | rfl)
      · exact ⟨MuTab.muTabElt_mem ρ₀, rfl⟩
      · exact ⟨MuTab.muTabElt_mem ρ₁, hcomm01.symm⟩
  obtain ⟨φ⟩ : MuIsoS4 Φ W := (Q3CL.Wyl.muIso_of_cent hP hW hnc ρ₀).2.1 (by
    rw [hcent]
    exact Set.ncard_pair hne01)
  have hM : ∀ g : X, g ∈ MGrp Φ W ⊔ OCW W := fun g => by
    have hg : g ∈ TC.Thin.pSpan Φ := by
      rw [F.gen]
      exact Subgroup.mem_top g
    exact Subgroup.mem_sup_left
      (TC.Thin.pSpan_le (fun L hL => Asc77.Thompson.le_MGrp_of_mem_D (hD L hL)) hg)
  let θ : X →* ↥(muGroup Φ W) :=
    { toFun := fun g => ⟨Asc77.Thompson.piG W g, Asc77.Thompson.piG_mem_muGroup (hM g)⟩
      map_one' := Subtype.ext (Asc77.Thompson.piG_of_mem_sup (Subgroup.one_mem _))
      map_mul' := fun g h => Subtype.ext (Asc77.Thompson.piG_mul (hNW g) (hNW h)) }
  have hθρ : ∀ ρ : Asc77.Thompson.Rep Φ W, θ ρ.r = MuTab.muTabElt ρ := fun ρ => rfl
  let ψ : X →* Equiv.Perm (Fin 4) := φ.toMonoidHom.comp θ
  have hψ : ∀ g : X, ψ g = φ (θ g) := fun g => rfl
  have hm1 : ∀ ρ : Asc77.Thompson.Rep Φ W, φ (MuTab.muTabElt ρ) ≠ 1 := fun ρ h =>
    Asc77.Thompson.muDelta_ne_one hW (MuTab.muTabElt_mem ρ)
      (φ.injective (h.trans (map_one φ).symm))
  have hm2 : ∀ ρ : Asc77.Thompson.Rep Φ W,
      φ (MuTab.muTabElt ρ) * φ (MuTab.muTabElt ρ) = 1 := fun ρ => by
    rw [← map_mul, Q3T6.Mu.muDelta_mul_self hΦ hW (MuTab.muTabElt_mem ρ), map_one]
  have hH : (Ea Φ a).map ψ = ⊤ := by
    refine s4_eq_top_of_hasS3Quot ?_ (x := φ (MuTab.muTabElt ρ₀))
      (x' := φ (MuTab.muTabElt ρ₁)) ⟨r₀, le_Ea hK haK hr₀, by rw [hψ, ← hρ₀r, hθρ]⟩
      ⟨r₁, le_Ea hK'Φ haK' hr₁, by rw [hψ, ← hρ₁r, hθρ]⟩ (hm1 ρ₀) (hm1 ρ₁)
      (fun h => hne01 (φ.injective h)) (hm2 ρ₀) (hm2 ρ₁)
      (by rw [← map_mul, ← map_mul, hcomm01])
    refine HasS3Quot.of_surjective (ψ.subgroupMap (Ea Φ a)) (ψ.subgroupMap_surjective _)
      (fun y hy => ?_) ha
    have h1 : φ (θ (y : X)) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    have h3 : Asc77.Thompson.piG W (y : X) = 1 :=
      congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm))
    have hyW : (y : X) ∈ W := by
      have h4 := (Asc77.Thompson.piG_eq_one_iff (hNW (y : X))).mp h3
      rwa [hOCW, sup_bot_eq] at h4
    obtain ⟨k, hk⟩ := hW2 ⟨(y : X), hyW⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hall : ∀ L ∈ Φ, L ≤ Subgroup.centralizer ({a} : Set X) := by
    intro L hL
    obtain ⟨g, rfl⟩ := F.trans K hK L hL
    obtain ⟨y, hy, hyg⟩ : ∃ y ∈ Ea Φ a, ψ y = ψ g := by
      have h : ψ g ∈ (Ea Φ a).map ψ := by
        rw [hH]
        exact Subgroup.mem_top _
      exact h
    have hθ : θ y = θ g := φ.injective (by rw [← hψ, ← hψ, hyg])
    have hgK : conjSub g K ∈ Φ := hΦ.conjInvariant g K hK
    have hyK : conjSub y K ∈ Φ := hΦ.conjInvariant y K hK
    obtain ⟨σg, hσg, hσgr⟩ : ∃ σ : Asc77.Thompson.Rep Φ W,
        σ.K = conjSub g K ∧ σ.r = g * r₀ * g⁻¹ :=
      ⟨⟨conjSub g K, conjSub g K, g * r₀ * g⁻¹, hgK, hD _ hgK, hsyl _ hgK,
        conj_mem_conjSub hr₀, hrW g hr₀W⟩, rfl, rfl⟩
    obtain ⟨σy, hσy, hσyr⟩ : ∃ σ : Asc77.Thompson.Rep Φ W,
        σ.K = conjSub y K ∧ σ.r = y * r₀ * y⁻¹ :=
      ⟨⟨conjSub y K, conjSub y K, y * r₀ * y⁻¹, hyK, hD _ hyK, hsyl _ hyK,
        conj_mem_conjSub hr₀, hrW y hr₀W⟩, rfl, rfl⟩
    have heq : MuTab.muTabElt σg = MuTab.muTabElt σy := by
      rw [← hθρ σg, ← hθρ σy, hσgr, hσyr]
      simp only [map_mul, map_inv, hθ]
    have hKK : conjSub g K = conjSub y K := by
      have h := (Q3T6.Mu.muTabElt_eq_iff hP hW σg σy).mp heq
      rwa [hσg, hσy] at h
    rw [hKK]
    intro l hl
    rw [mem_conjSub_iff] at hl
    have hya : y ∈ Subgroup.centralizer ({a} : Set X) := Ea_le_centralizer Φ a hy
    have hm : y * (y⁻¹ * l * y) * y⁻¹ ∈ Subgroup.centralizer ({a} : Set X) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hya (haK hl)) (Subgroup.inv_mem _ hya)
    rwa [show y * (y⁻¹ * l * y) * y⁻¹ = l by group] at hm
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ TC.Thin.pSpan Φ := by
    rw [F.gen]
    exact Subgroup.mem_top g
  exact Subgroup.mem_centralizer_singleton_iff.mp (TC.Thin.pSpan_le hall hg)

end WType

theorem secImage_le_centralizer_mk {Y : Type} [Group Y] {X Q : Subgroup Y} {c : Y} (hcX : c ∈ X)
    (hcQ : ∀ x ∈ Q, c * x = x * c) :
    secImage X Q ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨c, hcX⟩} : Set (SecQuot X)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hcQ y (Subgroup.mem_subgroupOf.mp hy)).symm


section Main

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y} {Z V : Subgroup Y}

theorem twin_pair_of_sylow_237 (hc : P23Cfg n Y R S t K' W u e g)
    (hL1 : SecCoresTwoGroup (Om R) V) {P₀ P₀' : Subgroup Y} (hP₀ : IsSylow2In P₀ (tightCore R))
    (hP₀' : IsSylow2In P₀' K') (hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y))
    (hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y)) :
    secImage (rLayerSub (Om R) V) P₀ ∈ p23SecFamV R V ∧
      secImage (rLayerSub (Om R) V) P₀' ∈ p23SecFamV R V ∧
      secImage (rLayerSub (Om R) V) P₀' ≠ secImage (rLayerSub (Om R) V) P₀ ∧
      (∃ zb : SecQuot (rLayerSub (Om R) V),
        IsUniqueInvolution (secImage (rLayerSub (Om R) V) P₀) zb ∧
          IsUniqueInvolution (secImage (rLayerSub (Om R) V) P₀') zb) ∧
      (∀ J ∈ p23SecFamV R V, J ≠ secImage (rLayerSub (Om R) V) P₀ →
        J ≤ Subgroup.normalizer ((secImage (rLayerSub (Om R) V) P₀ :
          Subgroup (SecQuot (rLayerSub (Om R) V))) : Set (SecQuot (rLayerSub (Om R) V))) →
          J = secImage (rLayerSub (Om R) V) P₀') ∧
      (∀ J ∈ p23SecFamV R V, J ≠ secImage (rLayerSub (Om R) V) P₀' →
        J ≤ Subgroup.normalizer ((secImage (rLayerSub (Om R) V) P₀' :
          Subgroup (SecQuot (rLayerSub (Om R) V))) : Set (SecQuot (rLayerSub (Om R) V))) →
          J = secImage (rLayerSub (Om R) V) P₀) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK'Ω : K' ∈ Om R := hc.std.hK'.1
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hP₀X : P₀ ≤ rLayerSub (Om R) V :=
    le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK₀ hP₀) hP₀C
  have hP₀'X : P₀' ≤ rLayerSub (Om R) V :=
    le_rLayerSub_of_mem (mem_RSet_of_isSylow2In hK'Ω hP₀') hP₀'C
  have htX : t ∈ rLayerSub (Om R) V := hP₀X (mem_sylow_of_isUniqueInvolution hΩ hK₀ hP₀ hz)
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hperp' : KPerp (Om R) K' = {K', tightCore R} := by
    rw [A7T22.kPerp_eq_of_twin hΩ hK₀ hc.std.hK', hperp, Set.pair_comm]
  refine ⟨⟨P₀, mem_RSet_of_isSylow2In hK₀ hP₀, hP₀C, rfl⟩,
    ⟨P₀', mem_RSet_of_isSylow2In hK'Ω hP₀', hP₀'C, rfl⟩, ?_,
    ⟨QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨t, htX⟩,
      isUniqueInvolution_secImage hΩ hK₀ hP₀ hP₀X hz htX,
      isUniqueInvolution_secImage hΩ hK'Ω hP₀' hP₀'X hz' htX⟩,
    perp_lift hΩ hL1 hK₀ hK'Ω hP₀ hP₀' hP₀C hP₀'C hperp,
    perp_lift hΩ hL1 hK'Ω hK₀ hP₀' hP₀ hP₀'C hP₀C hperp'⟩
  exact secImage_ne_of_twin hΩ hK₀ hK'Ω hP₀ hP₀' hP₀X hP₀'X hz hz' hc.std.hne
    (fun c hodd hcC => (hc.conjSub_eq_of_odd hcC hodd).1)

theorem centModE_of_central_237 (hc : P23Cfg n Y R S t K' W u e g) (hZ : P23ZData t u e Z)
    (hVZ : V ≤ Z) {c₁ c₂ : Y} (hc₁ : c₁ ∈ p23Orb Z t e) (hVc₁ : V ≤ aSub R Z c₁)
    (hc₂ : c₂ ∈ Z) (hc₂X : c₂ ∈ rLayerSub (Om R) V)
    (hcen : QuotientGroup.mk' (classicalInvolutionOddCore ↥(rLayerSub (Om R) V)) ⟨c₂, hc₂X⟩ ∈
      Subgroup.center (SecQuot (rLayerSub (Om R) V))) : CentModE R c₁ c₂ := by
  have hΩ : HypOmegaGen (Om R) := (CoreData.of_S hc.std.perp.core).hyp
  obtain ⟨-, hE₀E, hE₀X, hcov⟩ := p23_cover_V hc hZ hVZ hc₁ hVc₁
  have hc₁Z : c₁ ∈ Z := hZ.orb_le hc₁
  have hA : c₂ ∈ Subgroup.centralizer ((V ⊔ Subgroup.zpowers c₁ : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hZ.comm h ((sup_le hVZ (Subgroup.zpowers_le.mpr hc₁Z)) hh) c₂ hc₂
  have hN := F7L.mem_normalizer_rLayerSub hΩ hA
  exact L7.centMod_of_central_cover hE₀E hE₀X hcov hc₂X hcen
    (fun y hy => (Subgroup.mem_normalizer_iff.mp hN y).mp hy)
    (fun o ho => F7C.conj_mem_oddCoreOf_rLayer hΩ (hZ.le_cent hc₁Z hc₂) ho)

theorem lemLNoW_of_coreTwo {n : ℕ} (hT : Thm4RTwinBelow 3 n) (hL1 : LemLCoreTwo n) :
    LemLNoW n := by
  intro hcit hP Y _ _ R S t K' W u e g Z V f₁ f₂ ctx ⟨Wh, hW1⟩
  have hL := hL1 hcit hP Y R S t K' W u e g Z V f₁ f₂ ctx
  obtain ⟨hc, hno, hE, hZs, hZd, hVZ, hV1, hf₁, hf₂, hne, h₁, h₂⟩ := ctx
  obtain ⟨hf₁X, ha⟩ := p23_type237 hc hZd hVZ (modS3O_rLayer hc hE) hf₁ h₁
  have hf₁Z : f₁ ∈ Z := hZd.orb_le hf₁
  have hVfZ : V ⊔ Subgroup.zpowers f₁ ≤ Z := sup_le hVZ (Subgroup.zpowers_le.mpr hf₁Z)
  obtain ⟨⟨P₀, hP₀, hP₀C'⟩, ⟨P₀', hP₀', hP₀'C'⟩⟩ := exists_sylow_cent_twins hc hZd hVfZ
  have hVV : ((V : Subgroup Y) : Set Y) ⊆ ((V ⊔ Subgroup.zpowers f₁ : Subgroup Y) : Set Y) :=
    SetLike.coe_subset_coe.mpr le_sup_left
  have hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀C'.trans (Subgroup.centralizer_le hVV)
  have hP₀'C : P₀' ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀'C'.trans (Subgroup.centralizer_le hVV)
  have hfV : f₁ ∈ V ⊔ Subgroup.zpowers f₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers f₁)
  have hPf : ∀ x ∈ P₀, f₁ * x = x * f₁ := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀C' hx) f₁ hfV
  have hPf' : ∀ x ∈ P₀', f₁ * x = x * f₁ := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (hP₀'C' hx) f₁ hfV
  obtain ⟨hKb, hKb', hne', ⟨zb, hzb, hzb'⟩, hperp, hperp'⟩ :=
    twin_pair_of_sylow_237 hc hL hP₀ hP₀' hP₀C hP₀'C
  have hlt := card_secQuot_lt hc hV1
  have hΦΩ := p23SecFamV_hypOmegaGen hc hZd hVZ hL
  have F : Q8Pre (SecQuot (rLayerSub (Om R) V)) (p23SecFamV R V) :=
    { hyp := hΦΩ
      two := p23SecFamV_isPGroup hL
      q8 := p23SecFamV_q8 hc hL
      aEmpty := p23SecFamV_aEmpty hc hZd hVZ hL
      gen := p23SecFamV_pSpan R V
      trans := trans_of_twin hT hlt hΦΩ (p23SecFamV_isPGroup hL) (p23SecFamV_q8 hc hL)
        (p23SecFamV_aEmpty hc hZd hVZ hL)
        (CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V)) hKb
        ⟨hKb', zb, hzb, hzb'⟩ hne' hperp hperp' ha
      oddFree := CFSG.ComponentClassification.OddCore.quotient_corefree ↥(rLayerSub (Om R) V) }
  have hcen := mem_center_of_wSet F hKb ⟨hKb', zb, hzb, hzb'⟩ hne' hperp hperp' ha
    (secImage_le_centralizer_mk hf₁X hPf) (secImage_le_centralizer_mk hf₁X hPf') hW1
  exact not_centModE_of_ne_237 hP hc hE hno hZs hZd hf₂ hf₁ (Ne.symm hne)
    (centModE_of_central_237 hc hZd hVZ hf₂ h₂ hf₁Z hf₁X hcen)

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

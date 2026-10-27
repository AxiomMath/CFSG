module

public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.CGT.PushingUpLit.BHS.Prelim
public import CFSG.CGT.PushingUpLit.SubnormalTwoGroup
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem isSylowTwoOf_of_isSylowOf {T G : Subgroup Γ} (h : IsSylowOf 2 T G) : IsSylowTwoOf T G :=
  h

theorem isSylowOf_of_isSylowTwoOf {T G : Subgroup Γ} (h : IsSylowTwoOf T G) : IsSylowOf 2 T G :=
  h

theorem isSylowTwoOf_of_le_of_le {S M J : Subgroup Γ} (hS : IsSylowTwoOf S J) (hSM : S ≤ M)
    (hMJ : M ≤ J) : IsSylowTwoOf S M :=
  ⟨hSM, hS.2.1, fun hd => hS.2.2 (hd.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex S M J hSM
    hMJ)))⟩

section Block

variable {G T E : Subgroup Γ}

theorem baum_le_normalizer_of_isBTBlock (hE : IsBTBlock G T E) :
    baum T ≤ Subgroup.normalizer (E : Set Γ) := by
  have h := Subgroup.normalizer_commutator_ge_right E (baum T)
  rwa [hE.commutator] at h

theorem le_normalizer_pCoreOf_self (E : Subgroup Γ) :
    E ≤ Subgroup.normalizer (pCoreOf 2 E : Set Γ) :=
  CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 E

theorem opResidual_eq_of_isBTBlock [Finite Γ] (hE : IsBTBlock G T E) : opResidual 2 E = E := by
  have hY := SubTwo.noTwoQuotient_of_oResidualTwo hE.residual
  refine hY (opResidual 2 E) (opResidual_le 2 E) ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (opResidual_le 2 E)).mp
      (opResidual_normal 2 E)
  · intro y hy
    exact exists_pow_mem_opResidual (p := 2) hy

theorem omegaOneCenterOf_eq_self_of_elemAbelian {X : Subgroup Γ}
    (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (h2 : ∀ x ∈ X, x ^ 2 = 1) :
    omegaOneCenterOf X = X := by
  refine le_antisymm (C1GN.omegaOneCenterOf_le_self X) fun x hx => ?_
  refine Subgroup.subset_closure ⟨⟨hx, ?_⟩, h2 x hx⟩
  exact Subgroup.mem_centralizer_iff.mpr fun y hy => (hc x hx y hy).symm

theorem blockW_eq_pCoreOf (hE : IsBTBlock G T E) : blockW E = pCoreOf 2 E := by
  unfold blockW
  rw [omegaOneCenterOf_eq_self_of_elemAbelian hE.elemAbelian.1 hE.elemAbelian.2]
  exact hE.perfect

end Block

section Baum

variable [Finite Γ]

theorem thompsonJ_eq_of_baum_le {G T S : Subgroup Γ} (hT : IsSylowTwoOf T G) (hS2 : IsPGroup 2 S)
    (hSG : S ≤ G) (hBS : baum T ≤ S) : thompsonJ S = thompsonJ T := by
  obtain ⟨T', hT', hST'⟩ := B6.exists_isSylowTwoOf_ge hS2 hSG
  obtain ⟨g, -, hgT⟩ := B6.isSylowTwoOf_exists_conj hT hT'
  have hJT : thompsonJ T ≤ T' := (B6.thompsonJ_le_baum T).trans (hBS.trans hST')
  have hmax : ∀ A, IsMaxElemAbelian T A → IsMaxElemAbelian T' A := by
    intro A hA
    refine ⟨(B6.le_thompsonJ hA).trans hJT, hA.2.1, fun B hB hBe => ?_⟩
    have h1 : B6.conjSub g⁻¹ B ≤ T := by
      have := (B6.conjSub g⁻¹).le_iff_le.mpr hB
      rwa [hgT, ← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at this
    have h2 := hA.2.2 _ h1 (B6.isElemAbelian_conjSub hBe g⁻¹)
    rwa [B6.card_conjSub] at h2
  have hJ1 : thompsonJ T ≤ thompsonJ T' := iSup₂_le fun A hA => B6.le_thompsonJ (hmax A hA)
  have hJ2 : thompsonJ T' = thompsonJ T := by
    refine (Subgroup.eq_of_le_of_card_ge hJ1 ?_).symm
    rw [hgT, B6.thompsonJ_conjSub, B6.card_conjSub]
  have hJS : thompsonJ T' ≤ S := hJ2 ▸ ((B6.thompsonJ_le_baum T).trans hBS)
  rw [B6.thompsonJ_eq_of_le hJS hST', hJ2]

omit [Finite Γ] in
theorem le_normalizer_omegaOneCenterOf_thompsonJ (T : Subgroup Γ) :
    T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set Γ) :=
  (B6.le_normalizer_thompsonJ T).trans
    (normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv (thompsonJ T))

theorem baum_eq_of_isPGroup_of_baum_le {G T S : Subgroup Γ} (hT : IsSylowTwoOf T G)
    (hS2 : IsPGroup 2 S) (hSG : S ≤ G) (hBS : baum T ≤ S) : baum S = baum T := by
  have hJ := thompsonJ_eq_of_baum_le hT hS2 hSG hBS
  set Z0 : Subgroup Γ := omegaOneCenterOf (thompsonJ T) with hZ0
  have hbS : baum S = S ⊓ Subgroup.centralizer (Z0 : Set Γ) := by
    unfold baum
    rw [hJ]
  have hbT : baum T = T ⊓ Subgroup.centralizer (Z0 : Set Γ) := rfl
  set G' : Subgroup Γ := G ⊓ Subgroup.normalizer (Z0 : Set Γ) with hG'
  have hTG' : T ≤ G' := le_inf hT.1 (le_normalizer_omegaOneCenterOf_thompsonJ T)
  have hT' : IsSylowTwoOf T G' := isSylowTwoOf_of_le_of_le hT hTG' inf_le_left
  set N : Subgroup Γ := G' ⊓ Subgroup.centralizer (Z0 : Set Γ) with hN
  have hNG' : N ≤ G' := inf_le_left
  have hG'N : G' ≤ Subgroup.normalizer (N : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer (inf_le_right) hg⟩
  have hsyl : IsSylowTwoOf (T ⊓ N) N := B6.isSylowTwoOf_inf_normal hT' hNG' hG'N
  have hTN : T ⊓ N = baum T := by
    rw [hbT]
    ext x
    constructor
    · rintro ⟨hxT, -, hxC⟩
      exact ⟨hxT, hxC⟩
    · rintro ⟨hxT, hxC⟩
      exact ⟨hxT, hTG' hxT, hxC⟩
  rw [hTN] at hsyl
  have hbSN : baum S ≤ N := by
    intro x hx
    rw [hbS] at hx
    exact ⟨⟨hSG hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩, hx.2⟩
  have hbTS : baum T ≤ baum S := by
    rw [hbS]
    exact le_inf hBS (hbT ▸ inf_le_right)
  exact hsyl.eq_of_le hbTS hbSN (hS2.to_le (inf_le_left : baum S ≤ S))

end Baum

section Residual

variable [Finite Γ]

omit [Finite Γ] in
theorem opResidual_sup_eq {E D : Subgroup Γ} (hE : opResidual 2 E = E) (hD : IsPGroup 2 D)
    (hDE : D ≤ Subgroup.normalizer (E : Set Γ)) : opResidual 2 (E ⊔ D) = E := by
  have hge : opResidual 2 E ≤ opResidual 2 (E ⊔ D) := opResidual_mono 2 le_sup_left
  rw [hE] at hge
  refine le_antisymm ?_ hge
  refine opResidual_le_of_pow_mem fun x hx => ?_
  have hx' : x ∈ ((D ⊔ E : Subgroup Γ) : Set Γ) := by
    rw [sup_comm]
    exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D E hDE] at hx'
  obtain ⟨d, hd, e, he, rfl⟩ := hx'
  obtain ⟨k, hk⟩ := hD ⟨d, hd⟩
  have hk' : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have he' : d * e * d⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hDE hd) e).mp he
  have hdec : d * e = (d * e * d⁻¹) * d := by group
  obtain ⟨y, hy, h⟩ := SubTwo.exists_pow_mul_eq hDE he' hd (2 ^ k)
  refine ⟨k, ?_⟩
  show (d * e) ^ 2 ^ k ∈ E
  rw [hdec, h, hk', mul_one]
  exact hy

end Residual

theorem le_normalizer_iSup_conj {E B Q : Subgroup Γ} (hEQ : E ≤ Subgroup.normalizer (Q : Set Γ))
    (hQB : Q ≤ Subgroup.normalizer (B : Set Γ)) :
    Q ≤ Subgroup.normalizer ((⨆ e : E, conjSub (e : Γ) B : Subgroup Γ) : Set Γ) := by
  have key : ∀ q ∈ Q, conjSub q (⨆ e : E, conjSub (e : Γ) B) ≤ ⨆ e : E, conjSub (e : Γ) B := by
    intro q hq
    rw [conjSub_iSup]
    refine iSup_le fun e => ?_
    rw [← conjSub_mul]
    have hq' : (e : Γ)⁻¹ * q * e ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hEQ (E.inv_mem e.2)) q).mp hq
      simpa using this
    have hqe : q * (e : Γ) = (e : Γ) * ((e : Γ)⁻¹ * q * e) := by group
    rw [hqe, conjSub_mul, conjSub_eq_of_mem_normalizer (hQB hq')]
    exact le_iSup (fun e : E => conjSub (e : Γ) B) e
  intro q hq
  exact mem_normalizer_of_conjSub_le (key q hq) (key q⁻¹ (Q.inv_mem hq))

theorem iSup_conj_eq_sup_of_commutator_eq {E B : Subgroup Γ} (hEB : ⁅E, B⁆ = E) :
    (⨆ e : E, conjSub (e : Γ) B : Subgroup Γ) = E ⊔ B := by
  refine le_antisymm (iSup_le fun e => ?_) ?_
  · intro x hx
    rw [mem_conjSub_iff] at hx
    have hxe : x = (e : Γ) * ((e : Γ)⁻¹ * x * e) * (e : Γ)⁻¹ := by group
    rw [hxe]
    exact mul_mem (mul_mem ((le_sup_left : E ≤ E ⊔ B) e.2) ((le_sup_right : B ≤ E ⊔ B) hx))
      (inv_mem ((le_sup_left : E ≤ E ⊔ B) e.2))
  · refine sup_le ?_ ?_
    · refine le_trans (le_of_eq hEB.symm) (Subgroup.commutator_le.mpr fun e he b hb => ?_)
      have h1 : (e * b * e⁻¹ : Γ) ∈ conjSub (e : Γ) B := by
        rw [mem_conjSub_iff]
        simpa [mul_assoc] using hb
      have h2 : (e * b * e⁻¹ : Γ) ∈ ⨆ e : E, conjSub (e : Γ) B :=
        (le_iSup (fun e : E => conjSub (e : Γ) B) ⟨e, he⟩) h1
      have h3 : b⁻¹ ∈ ⨆ e : E, conjSub (e : Γ) B := by
        have : b⁻¹ ∈ conjSub ((1 : E) : Γ) B := by
          rw [mem_conjSub_iff]
          simpa using B.inv_mem hb
        exact (le_iSup (fun e : E => conjSub (e : Γ) B) 1) this
      have := mul_mem h2 h3
      simpa [commutatorElement_def, mul_assoc] using this
    · intro b hb
      have : b ∈ conjSub ((1 : E) : Γ) B := by
        rw [mem_conjSub_iff]
        simpa using hb
      exact (le_iSup (fun e : E => conjSub (e : Γ) B) 1) this

theorem mem_normalizer_commutator {H K : Subgroup Γ} {g : Γ}
    (hH : g ∈ Subgroup.normalizer (H : Set Γ)) (hK : g ∈ Subgroup.normalizer (K : Set Γ)) :
    g ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup Γ) : Set Γ) := by
  have h1 : conjSub g H = H := conjSub_eq_of_mem_normalizer hH
  have h2 : conjSub g K = K := conjSub_eq_of_mem_normalizer hK
  have h : conjSub g ⁅H, K⁆ = ⁅H, K⁆ := by
    unfold conjSub at h1 h2 ⊢
    rw [Subgroup.map_commutator, h1, h2]
  exact mem_normalizer_of_conjSub_eq h

theorem commutator_self_eq_bot {W : Subgroup Γ} (hW : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) :
    ⁅W, W⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hW x hx y hy

section PGroup

variable [Finite Γ]

theorem eq_bot_of_commutator_eq_self {S W : Subgroup Γ} (hS : IsPGroup 2 S) (hWS : W ≤ S)
    (h : ⁅W, S⁆ = W) : W = ⊥ := by
  have hnil : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries S).mp hnil
  have key : ∀ k, W ≤ S.lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact hWS
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ, ← h]
      exact Subgroup.commutator_mono ih le_rfl
  rw [eq_bot_iff, ← hn]
  exact key n

theorem commutator_lt_of_isPGroup {W Q : Subgroup Γ} (hW : IsPGroup 2 W) (hQ : IsPGroup 2 Q)
    (hQW : Q ≤ Subgroup.normalizer (W : Set Γ)) (hne : W ≠ ⊥) : ⁅W, Q⁆ < W := by
  have hle : ⁅W, Q⁆ ≤ W := Subgroup.le_normalizer_iff_commutator_le_left.mp hQW
  refine lt_of_le_of_ne hle fun h => hne ?_
  have hS : IsPGroup 2 ↥(W ⊔ Q) := IsPGroup.to_sup_of_normal_left' hW hQ hQW
  have hcomm : ⁅W, W ⊔ Q⁆ = W := by
    refine le_antisymm
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (sup_le Subgroup.le_normalizer hQW)) ?_
    calc W = ⁅W, Q⁆ := h.symm
      _ ≤ ⁅W, W ⊔ Q⁆ := Subgroup.commutator_mono le_rfl le_sup_right
  exact eq_bot_of_commutator_eq_self hS le_sup_left hcomm

end PGroup

theorem commute_of_odd_of_stab' {W' : Subgroup Γ} (hW' : IsPGroup 2 W') {k : Γ}
    (hk : Odd (orderOf k)) (hkW' : ∀ w ∈ W', k * w = w * k) {p : Γ} (hkp : ⁅k, p⁆ ∈ W') :
    k * p * k⁻¹ = p := by
  obtain ⟨w, hwdef⟩ : ∃ w, w = ⁅k, p⁆ := ⟨_, rfl⟩
  have hw : w ∈ W' := hwdef ▸ hkp
  have hkp' : k * p * k⁻¹ = w * p := by rw [hwdef, commutatorElement_def]; group
  have hkw : k * w * k⁻¹ = w := by
    have := hkW' w hw
    calc k * w * k⁻¹ = w * k * k⁻¹ := by rw [this]
      _ = w := by group
  have hpow : ∀ m : ℕ, k ^ m * p * (k ^ m)⁻¹ = w ^ m * p := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hkwm : k * w ^ m * k⁻¹ = w ^ m := by rw [← conj_pow, hkw]
      calc k ^ (m + 1) * p * (k ^ (m + 1))⁻¹ = k * (k ^ m * p * (k ^ m)⁻¹) * k⁻¹ := by group
        _ = k * (w ^ m * p) * k⁻¹ := by rw [ih]
        _ = (k * w ^ m * k⁻¹) * (k * p * k⁻¹) := by group
        _ = w ^ m * (w * p) := by rw [hkwm, hkp']
        _ = w ^ (m + 1) * p := by rw [pow_succ]; group
  have h1 := hpow (orderOf k)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
  have hwm : w ^ orderOf k = 1 := by
    have h2 : w ^ orderOf k * p = 1 * p := by rw [one_mul]; exact h1.symm
    exact mul_right_cancel h2
  obtain ⟨n, hn⟩ := hW' ⟨w, hw⟩
  have hn' : w ^ 2 ^ n = 1 := congrArg Subtype.val hn
  have hd1 : orderOf w ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
  have hd2 : orderOf w ∣ orderOf k := orderOf_dvd_of_pow_eq_one hwm
  have hcop : Nat.Coprime (2 ^ n) (orderOf k) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hk)
  have hcop' : Nat.Coprime (orderOf w) (orderOf k) := Nat.Coprime.coprime_dvd_left hd1 hcop
  have hw1 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd hcop' hd2
  rw [hkp', orderOf_eq_one_iff.mp hw1, one_mul]

theorem commute_of_odd_of_stab {P W' : Subgroup Γ} (hP : IsPGroup 2 P) (hW'P : W' ≤ P) {k : Γ}
    (hk : Odd (orderOf k)) (hkP : ∀ p ∈ P, ⁅k, p⁆ ∈ W') (hkW' : ∀ w ∈ W', k * w = w * k)
    {p : Γ} (hp : p ∈ P) : k * p * k⁻¹ = p :=
  commute_of_odd_of_stab' (hP.to_le hW'P) hk hkW' (hkP p hp)

theorem le_of_forall_odd_le {F K : Subgroup Γ} (hF : opResidual 2 F = F)
    (h : ∀ x ∈ F, Odd (orderOf x) → x ∈ K) : F ≤ K := by
  rw [← hF, opResidual, Subgroup.closure_le]
  rintro x ⟨hxF, hxc⟩
  exact h x hxF (Nat.coprime_two_right.mp hxc)

end CFSG.CGT.PushingUpLit.BHS6

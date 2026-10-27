module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2Align
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwap

public section

namespace CFSG.SeitzReduction.SeitzQ2

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)

section Diagonal

variable {G : Type*} [Group G] {t : G}

theorem isQuasisimple_iSup_of_diag {κ : Type*} {L : Subgroup G} (hL : IsSimpleGroup L)
    (F P : κ → Subgroup G)
    (hcomm : ∀ k l, (F l).map (MulAut.conj t).toMonoidHom ≤ centralizer (F k : Set G))
    (hperf : ∀ k, ⁅F k, F k⁆ = F k) (hδ : ∀ k, ∀ x ∈ F k, x * (t * x * t⁻¹) ∈ P k)
    (hsurjP : ∀ k, ∀ y ∈ P k, ∃ x ∈ F k, x * (t * x * t⁻¹) = y) (hgen : ⨆ k, P k = L) :
    CFSG.Open.IsQuasisimple (⨆ k, F k : Subgroup G) ∧
      (⨆ k, F k).map (MulAut.conj t).toMonoidHom ≤
        centralizer ((⨆ k, F k : Subgroup G) : Set G) ∧
      (∀ x ∈ ⨆ k, F k, x * (t * x * t⁻¹) ∈ L) ∧
      ∀ y ∈ L, ∃ x ∈ ⨆ k, F k, x * (t * x * t⁻¹) = y := by
  have h₁₂ := LinearPilot.map_conj_iSup_le_centralizer (U := F) hcomm
  have hPL : ∀ k, P k ≤ L := fun k => hgen ▸ le_iSup P k
  have hδL : ∀ x ∈ ⨆ k, F k, x * (t * x * t⁻¹) ∈ L :=
    LinearPilot.mul_conj_mem_of_mem_iSup h₁₂ fun k x hx => hPL k (hδ k x hx)
  have hsurj : ∀ y ∈ L, ∃ x ∈ ⨆ k, F k, x * (t * x * t⁻¹) = y := by
    intro y hy
    rw [← hgen] at hy
    refine LinearPilot.exists_mul_conj_eq_of_mem_iSup h₁₂ (fun k y hy => ?_) y hy
    obtain ⟨x, hx, hxy⟩ := hsurjP k y hy
    exact ⟨x, le_iSup F k hx, hxy⟩
  have hperfG := LinearPilot.commutator_iSup_eq_of_forall F hperf
  exact ⟨LinearPilot.isQuasisimple_of_linearSwapDiag h₁₂ hperfG hL hδL hsurj, h₁₂, hδL, hsurj⟩

end Diagonal

section Param

variable {G : Type*} [Group G]

structure SwapParam (t : G) (D : Subgroup G) where
  Ψ : D × D →* G
  ker_le : Ψ.ker ≤ center (D × D)
  diag : ∀ d : D, Ψ (d, d) = d
  swap : ∀ x y : D, t * Ψ (x, y) * t⁻¹ = Ψ (y, x)

namespace SwapParam

variable {t : G} {D : Subgroup G} (P : SwapParam t D)

@[expose] noncomputable def lft (x : G) : G := by
  classical exact if h : x ∈ D then P.Ψ (⟨x, h⟩, 1) else 1

theorem lft_of_mem {x : G} (h : x ∈ D) : P.lft x = P.Ψ (⟨x, h⟩, 1) := by
  rw [lft, dite_eq_left h]

theorem lft_of_not_mem {x : G} (h : x ∉ D) : P.lft x = 1 := by
  rw [lft, dite_eq_right h]

theorem conj_lft_of_mem {x : G} (h : x ∈ D) : t * P.lft x * t⁻¹ = P.Ψ (1, ⟨x, h⟩) := by
  rw [P.lft_of_mem h, P.swap]

theorem lft_mul_conj_lft {x : G} (h : x ∈ D) : P.lft x * (t * P.lft x * t⁻¹) = x := by
  rw [P.conj_lft_of_mem h, P.lft_of_mem h, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul, P.diag]

theorem commute_lft_conj_lft (x y : G) : Commute (P.lft x) (t * P.lft y * t⁻¹) := by
  by_cases hx : x ∈ D
  · by_cases hy : y ∈ D
    · rw [P.conj_lft_of_mem hy, P.lft_of_mem hx]
      have h : Commute ((⟨x, hx⟩, 1) : D × D) (1, ⟨y, hy⟩) := by
        change ((⟨x, hx⟩, 1) : D × D) * (1, ⟨y, hy⟩) = (1, ⟨y, hy⟩) * (⟨x, hx⟩, 1)
        ext <;> simp
      exact h.map P.Ψ
    · rw [P.lft_of_not_mem hy, mul_one, mul_inv_cancel]
      exact Commute.one_right _
  · rw [P.lft_of_not_mem hx]
    exact Commute.one_left _

theorem fst_mem_center_of_mem_center {z : D × D} (hz : z ∈ center (D × D)) : z.1 ∈ center D := by
  rw [mem_center_iff] at hz ⊢
  intro g
  exact congrArg Prod.fst (hz (g, 1))

theorem lft_ne_conj_lft {x : G} (hx : x ∈ D) (hxZ : (⟨x, hx⟩ : D) ∉ center D) :
    P.lft x ≠ t * P.lft x * t⁻¹ := by
  rw [P.conj_lft_of_mem hx, P.lft_of_mem hx]
  intro h
  apply hxZ
  have hk : ((⟨x, hx⟩, (⟨x, hx⟩ : D)⁻¹) : D × D) ∈ P.Ψ.ker := by
    rw [MonoidHom.mem_ker]
    have e : ((⟨x, hx⟩, (⟨x, hx⟩ : D)⁻¹) : D × D) = (⟨x, hx⟩, 1) * (1, ⟨x, hx⟩)⁻¹ := by
      ext <;> simp
    rw [e, map_mul, map_inv, h, mul_inv_cancel]
  exact fst_mem_center_of_mem_center (P.ker_le hk)

@[expose] def flip : SwapParam t D where
  Ψ := P.Ψ.comp (MulEquiv.prodComm : D × D ≃* D × D).toMonoidHom
  ker_le z hz := by
    have hc : MulEquiv.prodComm z ∈ center (D × D) := P.ker_le hz
    rw [mem_center_iff] at hc ⊢
    intro g
    have h := congrArg Prod.swap (hc (MulEquiv.prodComm g))
    simpa using h
  diag d := P.diag d
  swap x y := P.swap y x

theorem flip_Ψ (x y : D) : P.flip.Ψ (x, y) = P.Ψ (y, x) := rfl

theorem lft_flip (x : G) : P.flip.lft x = t * P.lft x * t⁻¹ := by
  by_cases hx : x ∈ D
  · rw [P.flip.lft_of_mem hx, P.conj_lft_of_mem hx]
    rfl
  · rw [P.flip.lft_of_not_mem hx, P.lft_of_not_mem hx, mul_one, mul_inv_cancel]

@[expose] def fst (O : Subgroup G) : Subgroup G :=
  (O.subgroupOf D).map (P.Ψ.comp (MonoidHom.inl D D))

theorem lft_mem_fst {O : Subgroup G} (hO : O ≤ D) {x : G} (hx : x ∈ O) : P.lft x ∈ P.fst O := by
  rw [P.lft_of_mem (hO hx)]
  exact ⟨⟨x, hO hx⟩, mem_subgroupOf.2 hx, rfl⟩

theorem exists_lft_eq_of_mem_fst {O : Subgroup G} {y : G} (hy : y ∈ P.fst O) :
    ∃ x ∈ O, P.lft x = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, mem_subgroupOf.1 hx, P.lft_of_mem x.2⟩

theorem fst_eq_of_lft_eq {D' : Subgroup G} {P' : SwapParam t D'} {O : Subgroup G}
    (hO : O ≤ D) (hO' : O ≤ D') (h : ∀ x ∈ O, P'.lft x = P.lft x) : P'.fst O = P.fst O := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := P'.exists_lft_eq_of_mem_fst hy
    rw [h x hx]
    exact P.lft_mem_fst hO hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := P.exists_lft_eq_of_mem_fst hy
    rw [← h x hx]
    exact P'.lft_mem_fst hO' hx

theorem map_conj_fst_le_centralizer (O O' : Subgroup G) :
    (P.fst O').map (MulAut.conj t).toMonoidHom ≤ centralizer (P.fst O : Set G) := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x', -, rfl⟩ := P.exists_lft_eq_of_mem_fst hy
  rw [mem_centralizer_iff]
  intro z hz
  obtain ⟨x, -, rfl⟩ := P.exists_lft_eq_of_mem_fst hz
  exact (P.commute_lft_conj_lft x x').eq

theorem commutator_fst {O : Subgroup G} (hO : O ≤ D) (hperf : ⁅O, O⁆ = O) :
    ⁅P.fst O, P.fst O⁆ = P.fst O :=
  LinearPilot.commutator_map_eq_of_commutator_eq _
    (CFSG.SeitzReduction.commutator_subgroupOf_eq_self hO hperf)

theorem mul_conj_mem_of_mem_fst {O : Subgroup G} {y : G} (hy : y ∈ P.fst O) :
    y * (t * y * t⁻¹) ∈ O := by
  obtain ⟨z, hz, rfl⟩ := hy
  have h : (P.Ψ.comp (MonoidHom.inl D D)) z = P.lft z := (P.lft_of_mem z.2).symm
  rw [h, P.lft_mul_conj_lft z.2]
  exact mem_subgroupOf.1 hz

theorem exists_mem_fst_mul_conj_eq {O : Subgroup G} (hO : O ≤ D) {x : G} (hx : x ∈ O) :
    ∃ y ∈ P.fst O, y * (t * y * t⁻¹) = x :=
  ⟨P.lft x, P.lft_mem_fst hO hx, P.lft_mul_conj_lft (hO hx)⟩

theorem map_prod_eq_fst_sup (O : Subgroup G) :
    ((O.subgroupOf D).prod (O.subgroupOf D)).map P.Ψ =
      P.fst O ⊔ (P.fst O).map (MulAut.conj t).toMonoidHom := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
    obtain ⟨ha, hb⟩ := Subgroup.mem_prod.1 hab
    have e : ((a, b) : D × D) = (a, 1) * (1, b) := by ext <;> simp
    rw [e, map_mul]
    refine mul_mem (mem_sup_left ⟨a, ha, rfl⟩) (mem_sup_right ?_)
    refine ⟨P.Ψ (b, 1), ⟨b, hb, rfl⟩, ?_⟩
    change t * P.Ψ (b, 1) * t⁻¹ = P.Ψ (1, b)
    rw [P.swap]
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨(a, 1), Subgroup.mem_prod.2 ⟨ha, one_mem _⟩, rfl⟩
  · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨(1, a), Subgroup.mem_prod.2 ⟨one_mem _, ha⟩, ?_⟩
    change P.Ψ (1, a) = t * P.Ψ (a, 1) * t⁻¹
    rw [P.swap]

end SwapParam

end Param

section Sign

variable {G : Type*} [Group G] {t : G}

@[expose] noncomputable def signConj (t : G) (s : ℤˣ) (y : G) : G := by
  classical exact if s = 1 then y else t * y * t⁻¹

theorem signConj_one (y : G) : signConj t 1 y = y := by
  rw [signConj, ite_eq_left rfl]

theorem signConj_neg_one (y : G) : signConj t (-1) y = t * y * t⁻¹ := by
  rw [signConj, ite_eq_right (by decide)]

theorem signConj_mul (ht2 : t * t = 1) (s s' : ℤˣ) (y : G) :
    signConj t (s * s') y = signConj t s (signConj t s' y) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · simp only [mul_one, signConj_one]
  · simp only [one_mul, signConj_one]
  · simp only [mul_one, signConj_one]
  · rw [show ((-1 : ℤˣ) * -1) = 1 by decide, signConj_one, signConj_neg_one, signConj_neg_one,
      htinv]
    calc y = (t * t) * y * (t * t) := by rw [ht2, one_mul, mul_one]
      _ = t * (t * y * t) * t := by group

theorem eq_of_signConj_eq {s s' : ℤˣ} {y : G} (hy : y ≠ t * y * t⁻¹)
    (h : signConj t s y = signConj t s' y) : s = s' := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or s' with rfl | rfl
  · rfl
  · rw [signConj_one, signConj_neg_one] at h
    exact absurd h hy
  · rw [signConj_one, signConj_neg_one] at h
    exact absurd h.symm hy
  · rfl

variable {D D' D'' : Subgroup G}

@[expose] def TwistOn (s : ℤˣ) (P : SwapParam t D) (P' : SwapParam t D') (O : Subgroup G) :
    Prop :=
  ∀ x ∈ O, P'.lft x = signConj t s (P.lft x)

@[expose] def AgreeOn (P : SwapParam t D) (P' : SwapParam t D') (O : Subgroup G) : Prop :=
  ∀ x ∈ O, P'.lft x = P.lft x

@[expose] def FlipOn (P : SwapParam t D) (P' : SwapParam t D') (O : Subgroup G) : Prop :=
  ∀ x ∈ O, P'.lft x = t * P.lft x * t⁻¹

theorem agreeOn_flip_iff (ht2 : t * t = 1) {P : SwapParam t D} {P' : SwapParam t D'}
    {O : Subgroup G} : AgreeOn P P'.flip O ↔ FlipOn P P' O := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : ∀ y : G, t * (t * y * t⁻¹) * t⁻¹ = y := fun y => by
    rw [htinv]
    calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
      _ = y := by rw [ht2, one_mul, mul_one]
  refine forall₂_congr fun x _ => ?_
  rw [SwapParam.lft_flip]
  constructor
  · intro h
    rw [← h, hconj]
  · intro h
    rw [h, hconj]

theorem twistOn_one_iff {P : SwapParam t D} {P' : SwapParam t D'} {O : Subgroup G} :
    TwistOn 1 P P' O ↔ AgreeOn P P' O := by
  simp only [TwistOn, AgreeOn, signConj_one]

theorem twistOn_neg_one_iff {P : SwapParam t D} {P' : SwapParam t D'} {O : Subgroup G} :
    TwistOn (-1) P P' O ↔ FlipOn P P' O := by
  simp only [TwistOn, FlipOn, signConj_neg_one]

theorem AgreeOn.refl (P : SwapParam t D) (O : Subgroup G) : AgreeOn P P O := fun _ _ => rfl

theorem AgreeOn.symm {P : SwapParam t D} {P' : SwapParam t D'} {O : Subgroup G}
    (h : AgreeOn P P' O) : AgreeOn P' P O := fun x hx => (h x hx).symm

theorem AgreeOn.mono {P : SwapParam t D} {P' : SwapParam t D'} {O O' : Subgroup G}
    (h : AgreeOn P P' O) (hO : O' ≤ O) : AgreeOn P P' O' := fun x hx => h x (hO hx)

@[expose] noncomputable def SwapParam.twist (s : ℤˣ) (P : SwapParam t D) : SwapParam t D := by
  classical exact if s = 1 then P else P.flip

theorem SwapParam.lft_twist (s : ℤˣ) (P : SwapParam t D) (x : G) :
    (P.twist s).lft x = signConj t s (P.lft x) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [SwapParam.twist, ite_eq_left rfl, signConj_one]
  · rw [SwapParam.twist, ite_eq_right (by decide), SwapParam.lft_flip, signConj_neg_one]

@[expose] noncomputable def agreeSign (P : SwapParam t D) (P' : SwapParam t D') (O : Subgroup G) :
    ℤˣ := by
  classical exact if AgreeOn P P' O then 1 else -1

theorem twistOn_agreeSign {P : SwapParam t D} {P' : SwapParam t D'} {O : Subgroup G}
    (h : AgreeOn P P' O ∨ FlipOn P P' O) : TwistOn (agreeSign P P' O) P P' O := by
  by_cases ha : AgreeOn P P' O
  · rw [agreeSign, ite_eq_left ha]
    exact twistOn_one_iff.2 ha
  · rw [agreeSign, ite_eq_right ha]
    exact twistOn_neg_one_iff.2 (h.resolve_left ha)

theorem agreeSign_comm (P : SwapParam t D) (P' : SwapParam t D') (O : Subgroup G) :
    agreeSign P' P O = agreeSign P P' O := by
  by_cases ha : AgreeOn P P' O
  · rw [agreeSign, agreeSign, ite_eq_left ha, ite_eq_left ha.symm]
  · rw [agreeSign, agreeSign, ite_eq_right ha, ite_eq_right fun h => ha h.symm]

theorem sign_mul_of_triangle (ht2 : t * t = 1) {Pa : SwapParam t D} {Pb : SwapParam t D'}
    {Pc : SwapParam t D''} {Oab Obc Oac : Subgroup G} {s s' s'' : ℤˣ}
    (hab : TwistOn s Pa Pb Oab) (hbc : TwistOn s' Pb Pc Obc) (hac : TwistOn s'' Pa Pc Oac)
    {q : G} (hqab : q ∈ Oab) (hqbc : q ∈ Obc) (hqac : q ∈ Oac)
    (hdet : Pa.lft q ≠ t * Pa.lft q * t⁻¹) : s'' = s * s' := by
  have h1 : signConj t s'' (Pa.lft q) = signConj t (s' * s) (Pa.lft q) := by
    rw [← hac q hqac, hbc q hqbc, hab q hqab, signConj_mul ht2]
  rw [eq_of_signConj_eq hdet h1, mul_comm]

end Sign

section Dichotomy

variable {G : Type*} [Group G] {t : G} {D D' : Subgroup G}

@[expose] def SwapParam.restr (P : SwapParam t D) {O : Subgroup G} (hO : O ≤ D) : O × O →* G :=
  P.Ψ.comp ((Subgroup.inclusion hO).prodMap (Subgroup.inclusion hO))

theorem SwapParam.restr_apply (P : SwapParam t D) {O : Subgroup G} (hO : O ≤ D) (a b : O) :
    P.restr hO (a, b) = P.Ψ (Subgroup.inclusion hO a, Subgroup.inclusion hO b) :=
  rfl

theorem SwapParam.restr_injective (P : SwapParam t D) {O : Subgroup G} (hO : O ≤ D)
    (hZ : center O = ⊥) : Function.Injective (P.restr hO) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ hab
  have hc : ((Subgroup.inclusion hO a, Subgroup.inclusion hO b) : D × D) ∈ center (D × D) :=
    P.ker_le hab
  have hc' : ∀ (z : O), z ∈ center O ↔ ∀ g : O, g * z = z * g := fun z => mem_center_iff
  have key : ∀ (u : O), (∀ g : D, g * Subgroup.inclusion hO u = Subgroup.inclusion hO u * g) →
      u = 1 := by
    intro u hu
    have hu' : u ∈ center O := (hc' u).2 fun g => Subgroup.inclusion_injective hO (by
      rw [map_mul, map_mul]
      exact hu _)
    rw [hZ] at hu'
    exact hu'
  rw [mem_center_iff] at hc
  have ha : a = 1 := key a fun g => congrArg Prod.fst (hc (g, 1))
  have hb : b = 1 := key b fun g => congrArg Prod.snd (hc (1, g))
  rw [ha, hb]
  rfl

theorem SwapParam.range_restr (P : SwapParam t D) {O : Subgroup G} (hO : O ≤ D) :
    (P.restr hO).range = ((O.subgroupOf D).prod (O.subgroupOf D)).map P.Ψ := by
  rw [SwapParam.restr, MonoidHom.range_comp, MonoidHom.range_prodMap, Subgroup.inclusion_range]

theorem agreeOn_or_flipOn_of_map_prod_eq (P : SwapParam t D) (P' : SwapParam t D')
    {O : Subgroup G} (hO : O ≤ D) (hO' : O ≤ D') [IsSimpleGroup O] (hZ : center O = ⊥)
    (hmap : ((O.subgroupOf D').prod (O.subgroupOf D')).map P'.Ψ =
      ((O.subgroupOf D).prod (O.subgroupOf D)).map P.Ψ) :
    AgreeOn P P' O ∨ FlipOn P P' O := by
  have hd : ∀ a : O, P'.restr hO' (a, a) = P.restr hO (a, a) := fun a => by
    rw [SwapParam.restr_apply, SwapParam.restr_apply, P'.diag, P.diag]
    rfl
  rcases eq_or_eq_comp_prodComm_of_range_eq (eq_one_of_forall_mul_comm_of_center_eq_bot hZ)
      (P.restr_injective hO hZ) (P'.restr_injective hO' hZ)
      (by rw [P.range_restr, P'.range_restr, hmap]) hd with h | h
  · left
    intro x hx
    rw [P'.lft_of_mem (hO' hx), P.lft_of_mem (hO hx)]
    exact DFunLike.congr_fun h (⟨x, hx⟩, 1)
  · right
    intro x hx
    rw [P'.lft_of_mem (hO' hx), P.conj_lft_of_mem (hO hx)]
    exact DFunLike.congr_fun h (⟨x, hx⟩, 1)

end Dichotomy

section Coherent

variable {G : Type*} [Group G] {t : G}

theorem exists_coherent_swapParam {ι : Type*} (ht2 : t * t = 1) {D : ι → Subgroup G}
    (P : ∀ a, SwapParam t (D a)) (O : ι → ι → Subgroup G) (hO : ∀ a b, O b a = O a b)
    (p : ι → ι) (d : ι → ℕ) (T : ι → ι → ι → Prop)
    (hdich : ∀ a b, TriangleClosure (TreeEdge p d) T a b →
      AgreeOn (P a) (P b) (O a b) ∨ FlipOn (P a) (P b) (O a b))
    (hT : ∀ a b c, T a b c → ∃ q ∈ O a b, q ∈ O b c ∧ q ∈ O a c ∧
      (P a).lft q ≠ t * (P a).lft q * t⁻¹) :
    ∃ σ : ι → ℤˣ, ∀ a b, TriangleClosure (TreeEdge p d) T a b →
      AgreeOn ((P a).twist (σ a)) ((P b).twist (σ b)) (O a b) := by
  set τ : ι → ι → ℤˣ := fun a b => agreeSign (P a) (P b) (O a b) with hτ
  have htw : ∀ a b, TriangleClosure (TreeEdge p d) T a b → TwistOn (τ a b) (P a) (P b) (O a b) :=
    fun a b h => twistOn_agreeSign (hdich a b h)
  have hsymm : ∀ a b, TriangleClosure (TreeEdge p d) T a b → τ b a = (τ a b)⁻¹ := by
    intro a b _
    rw [Int.units_inv_eq_self, hτ]
    simp only
    rw [hO, agreeSign_comm]
  have hcoc : ∀ a b c, T a b c → TriangleClosure (TreeEdge p d) T a b →
      TriangleClosure (TreeEdge p d) T b c → τ a c = τ a b * τ b c := by
    intro a b c habc hab hbc
    obtain ⟨q, hqab, hqbc, hqac, hdet⟩ := hT a b c habc
    exact sign_mul_of_triangle ht2 (htw a b hab) (htw b c hbc) (htw a c (.tri habc hab hbc))
      hqab hqbc hqac hdet
  refine ⟨treePotential τ p d, fun a b h x hx => ?_⟩
  have hσ := eq_mul_inv_treePotential_of_triangleClosure τ hsymm hcoc h
  rw [SwapParam.lft_twist, SwapParam.lft_twist, htw a b h x hx, ← signConj_mul ht2, hσ]
  congr 1
  rw [mul_comm (treePotential τ p d a), ← mul_assoc, mul_inv_cancel, one_mul]

end Coherent

section Factors

variable {G : Type*} [Group G] {t : G}

theorem isQuasisimple_iSup_fst {κ ι : Type*} {D : ι → Subgroup G} (P : ∀ a, SwapParam t (D a))
    {L : Subgroup G} (hL : IsSimpleGroup L) (O : κ → Subgroup G) (ν : κ → ι)
    (hOν : ∀ k, O k ≤ D (ν k)) (hperf : ∀ k, ⁅O k, O k⁆ = O k)
    (hpair : ∀ k l, ∃ a, O k ≤ D a ∧ O l ≤ D a ∧ AgreeOn (P (ν k)) (P a) (O k) ∧
      AgreeOn (P (ν l)) (P a) (O l))
    (hgen : ⨆ k, O k = L) :
    CFSG.Open.IsQuasisimple (⨆ k, (P (ν k)).fst (O k) : Subgroup G) ∧
      (⨆ k, (P (ν k)).fst (O k)).map (MulAut.conj t).toMonoidHom ≤
        centralizer ((⨆ k, (P (ν k)).fst (O k) : Subgroup G) : Set G) ∧
      (∀ x ∈ ⨆ k, (P (ν k)).fst (O k), x * (t * x * t⁻¹) ∈ L) ∧
      (∀ y ∈ L, ∃ x ∈ ⨆ k, (P (ν k)).fst (O k), x * (t * x * t⁻¹) = y) ∧
      ∀ k, (((O k).subgroupOf (D (ν k))).prod ((O k).subgroupOf (D (ν k)))).map (P (ν k)).Ψ ≤
        (⨆ k, (P (ν k)).fst (O k)) ⊔
          (⨆ k, (P (ν k)).fst (O k)).map (MulAut.conj t).toMonoidHom := by
  set F : κ → Subgroup G := fun k => (P (ν k)).fst (O k) with hF
  have hcomm : ∀ k l, (F l).map (MulAut.conj t).toMonoidHom ≤ centralizer (F k : Set G) := by
    intro k l
    obtain ⟨a, hka, hla, hk, hl⟩ := hpair k l
    have e1 : F k = (P a).fst (O k) := ((P (ν k)).fst_eq_of_lft_eq (hOν k) hka hk).symm
    have e2 : F l = (P a).fst (O l) := ((P (ν l)).fst_eq_of_lft_eq (hOν l) hla hl).symm
    rw [e1, e2]
    exact (P a).map_conj_fst_le_centralizer (O k) (O l)
  obtain ⟨hq, h₁₂, hδ, hsurj⟩ := isQuasisimple_iSup_of_diag hL F O hcomm
    (fun k => (P (ν k)).commutator_fst (hOν k) (hperf k))
    (fun k x hx => (P (ν k)).mul_conj_mem_of_mem_fst hx)
    (fun k y hy => (P (ν k)).exists_mem_fst_mul_conj_eq (hOν k) hy) hgen
  refine ⟨hq, h₁₂, hδ, hsurj, fun k => ?_⟩
  rw [(P (ν k)).map_prod_eq_fst_sup (O k)]
  exact sup_le_sup (le_iSup F k) (Subgroup.map_mono (le_iSup F k))

end Factors

section Overlap

open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

variable {G : Type*} [Group G] {t : G} {D : Subgroup G}

theorem SwapParam.map_prod_inf_centralizer (P : SwapParam t D) (hinj : Function.Injective P.Ψ)
    {O : Subgroup G} (hO : O ≤ D) :
    ((O.subgroupOf D).prod (O.subgroupOf D)).map P.Ψ ⊓ centralizer ({t} : Set G) = O := by
  apply le_antisymm
  · rintro _ ⟨⟨⟨a, b⟩, hab, rfl⟩, ht⟩
    have ht' : P.Ψ (a, b) ∈ centralizer ({t} : Set G) := ht
    have h1 : t * P.Ψ (a, b) * t⁻¹ = P.Ψ (a, b) := by
      rw [mem_centralizer_singleton_iff] at ht'
      rw [← ht', mul_inv_cancel_right]
    rw [P.swap] at h1
    have hba : b = a := congrArg Prod.fst (hinj h1)
    subst hba
    rw [P.diag]
    exact mem_subgroupOf.1 (Subgroup.mem_prod.1 hab).1
  · intro x hx
    refine ⟨⟨(⟨x, hO hx⟩, ⟨x, hO hx⟩), Subgroup.mem_prod.2 ⟨mem_subgroupOf.2 hx,
      mem_subgroupOf.2 hx⟩, P.diag _⟩, ?_⟩
    change x ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have h1 := P.swap ⟨x, hO hx⟩ ⟨x, hO hx⟩
    rw [P.diag] at h1
    calc x * t = t * x * t⁻¹ * t := by rw [h1]
      _ = t * x := by group

variable [Finite G]

theorem SwapParam.centralizerPerfectCore_sup_eq (P : SwapParam t D)
    (hinj : Function.Injective P.Ψ) {X Y : Subgroup G}
    (hrange : P.Ψ.range = centralizerPerfectCore X) (hY : Y ≤ D) :
    centralizerPerfectCore (X ⊔ Y) =
      (((perfectCore (D ⊓ centralizer (Y : Set G))).subgroupOf D).prod
        ((perfectCore (D ⊓ centralizer (Y : Set G))).subgroupOf D)).map P.Ψ := by
  set C : Subgroup D := (centralizer (Y : Set G)).subgroupOf D with hC
  have hcen : centralizerPerfectCore X ⊓ centralizer (Y : Set G) = (C.prod C).map P.Ψ := by
    rw [← hrange]
    apply le_antisymm
    · rintro _ ⟨⟨⟨a, b⟩, rfl⟩, hz⟩
      have hz' : P.Ψ (a, b) ∈ centralizer (Y : Set G) := hz
      have key : ∀ (y : G) (hy : y ∈ Y), ((⟨y, hY hy⟩, ⟨y, hY hy⟩) : D × D) * (a, b) =
          (a, b) * (⟨y, hY hy⟩, ⟨y, hY hy⟩) := by
        intro y hy
        have h1 := mem_centralizer_iff.1 hz' y hy
        have hyy : P.Ψ (⟨y, hY hy⟩, ⟨y, hY hy⟩) = y := P.diag _
        rw [← hyy, ← map_mul, ← map_mul] at h1
        exact hinj h1
      refine ⟨(a, b), Subgroup.mem_prod.2 ⟨mem_subgroupOf.2 ?_, mem_subgroupOf.2 ?_⟩, rfl⟩
      · rw [mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (congrArg Prod.fst (key y hy))
      · rw [mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (congrArg Prod.snd (key y hy))
    · rintro _ ⟨⟨a, b⟩, hab, rfl⟩
      refine ⟨⟨(a, b), rfl⟩, ?_⟩
      change P.Ψ (a, b) ∈ centralizer (Y : Set G)
      refine mem_centralizer_iff.2 fun y hy => ?_
      obtain ⟨ha, hb⟩ := Subgroup.mem_prod.1 hab
      have ha' := mem_centralizer_iff.1 (mem_subgroupOf.1 ha) y hy
      have hb' := mem_centralizer_iff.1 (mem_subgroupOf.1 hb) y hy
      have e : ((⟨y, hY hy⟩, ⟨y, hY hy⟩) : D × D) * (a, b) =
          (a, b) * (⟨y, hY hy⟩, ⟨y, hY hy⟩) := by
        ext
        · exact ha'
        · exact hb'
      have hyy : P.Ψ (⟨y, hY hy⟩, ⟨y, hY hy⟩) = y := P.diag _
      rw [← hyy, ← map_mul, ← map_mul, e]
  have hcore : perfectCore C = (perfectCore (D ⊓ centralizer (Y : Set G))).subgroupOf D := by
    apply Subgroup.map_injective D.subtype_injective
    rw [CFSG.Quasithin.map_perfectCore, hC, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_comm,
      inf_eq_left.2 ((perfectCore_le _).trans inf_le_left)]
  rw [F4Pilot.centralizerPerfectCore_sup, hcen, ← CFSG.Quasithin.map_perfectCore,
    LinearPilot.perfectCore_subgroup_prod, hcore]

theorem SwapParam.perfectCore_inf_centralizer_eq (P : SwapParam t D)
    (hinj : Function.Injective P.Ψ) {X Y : Subgroup G}
    (hrange : P.Ψ.range = centralizerPerfectCore X) (hY : Y ≤ D) :
    perfectCore (D ⊓ centralizer (Y : Set G)) =
      centralizerPerfectCore (X ⊔ Y) ⊓ centralizer ({t} : Set G) := by
  rw [P.centralizerPerfectCore_sup_eq hinj hrange hY,
    P.map_prod_inf_centralizer hinj ((perfectCore_le _).trans inf_le_left)]

theorem agreeOn_or_flipOn_of_neighbours {D' : Subgroup G} (P : SwapParam t D)
    (P' : SwapParam t D') (hinj : Function.Injective P.Ψ) (hinj' : Function.Injective P'.Ψ)
    {X X' : Subgroup G} (hrange : P.Ψ.range = centralizerPerfectCore X)
    (hrange' : P'.Ψ.range = centralizerPerfectCore X') (hX' : X' ≤ D) (hX : X ≤ D')
    [IsSimpleGroup (perfectCore (D ⊓ centralizer (X' : Set G)))]
    (hZ : center (perfectCore (D ⊓ centralizer (X' : Set G))) = ⊥) :
    perfectCore (D' ⊓ centralizer (X : Set G)) = perfectCore (D ⊓ centralizer (X' : Set G)) ∧
      (AgreeOn P P' (perfectCore (D ⊓ centralizer (X' : Set G))) ∨
        FlipOn P P' (perfectCore (D ⊓ centralizer (X' : Set G)))) := by
  have hO : perfectCore (D' ⊓ centralizer (X : Set G)) =
      perfectCore (D ⊓ centralizer (X' : Set G)) := by
    rw [P.perfectCore_inf_centralizer_eq hinj hrange hX',
      P'.perfectCore_inf_centralizer_eq hinj' hrange' hX, sup_comm]
  refine ⟨hO, ?_⟩
  have hOD : perfectCore (D ⊓ centralizer (X' : Set G)) ≤ D := (perfectCore_le _).trans inf_le_left
  have hOD' : perfectCore (D ⊓ centralizer (X' : Set G)) ≤ D' :=
    hO ▸ (perfectCore_le _).trans inf_le_left
  refine agreeOn_or_flipOn_of_map_prod_eq P P' hOD hOD' hZ ?_
  have h1 := P.centralizerPerfectCore_sup_eq hinj hrange hX'
  have h2 := P'.centralizerPerfectCore_sup_eq hinj' hrange' hX
  rw [sup_comm, hO] at h2
  rw [← h1, ← h2]

end Overlap

end CFSG.SeitzReduction.SeitzQ2

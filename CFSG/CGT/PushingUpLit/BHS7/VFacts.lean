module

public import CFSG.CGT.PushingUpLit.BHS6.NatBridge
public import CFSG.CGT.PushingUpLit.BHS7.Basic

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem omegaOneCenterOf_le_omegaOneCenter_pCoreOf (hG : CharTwo G) (hT : IsSylowTwoOf T G) :
    omegaOneCenterOf T ≤ omegaOneCenterOf (pCoreOf 2 G) := by
  refine Subgroup.closure_mono ?_
  rintro x ⟨hxZ, hx2⟩
  have hxZ' : x ∈ T ⊓ Subgroup.centralizer (T : Set Γ) := hxZ
  have hxO : x ∈ pCoreOf 2 G := hG ⟨hT.1 hxZ'.1, Subgroup.centralizer_le hT.pCoreOf_le hxZ'.2⟩
  exact ⟨⟨hxO, Subgroup.centralizer_le hT.pCoreOf_le hxZ'.2⟩, hx2⟩

omit [Finite Γ] in
theorem vSub_le_omegaOneCenter (hG : CharTwo G) (hT : IsSylowTwoOf T G) :
    vSub G T ≤ omegaOneCenterOf (pCoreOf 2 G) := by
  refine iSup_le fun g => ?_
  have h1 : conjSub (g : Γ) (omegaOneCenterOf T) ≤
      conjSub (g : Γ) (omegaOneCenterOf (pCoreOf 2 G)) :=
    conjSub_mono _ (omegaOneCenterOf_le_omegaOneCenter_pCoreOf hG hT)
  rwa [conjSub_eq_of_mem_normalizer (le_normalizer_omegaOneCenter_pCoreOf G g.2)] at h1

omit [Finite Γ] in
theorem isElemAbelian_vSub (hG : CharTwo G) (hT : IsSylowTwoOf T G) :
    IsElemAbelian 2 (vSub G T) :=
  isElemAbelian_mono' (isElemAbelian_omegaOneCenter_pCoreOf G) (vSub_le_omegaOneCenter hG hT)

omit [Finite Γ] in
theorem vSub_le_pCoreOf (hG : CharTwo G) (hT : IsSylowTwoOf T G) : vSub G T ≤ pCoreOf 2 G :=
  (vSub_le_omegaOneCenter hG hT).trans (omegaOneCenter_le_pCoreOf G)

omit [Finite Γ] in
theorem omegaOneCenterOf_le_vSub (G T : Subgroup Γ) : omegaOneCenterOf T ≤ vSub G T := by
  have h : conjSub ((1 : G) : Γ) (omegaOneCenterOf T) ≤ vSub G T :=
    le_iSup (fun g : G => conjSub (g : Γ) (omegaOneCenterOf T)) 1
  rwa [show ((1 : G) : Γ) = 1 from rfl, conjSub_one] at h

omit [Finite Γ] in
theorem le_normalizer_vSub (G T : Subgroup Γ) : G ≤ Subgroup.normalizer (vSub G T : Set Γ) := by
  have key : ∀ g ∈ G, conjSub g (vSub G T) ≤ vSub G T := by
    intro g hg
    unfold vSub
    rw [conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [← conjSub_mul]
    exact le_iSup (fun h : G => conjSub (h : Γ) (omegaOneCenterOf T)) ⟨g * h, G.mul_mem hg h.2⟩
  intro g hg
  exact mem_normalizer_of_conjSub_le (key g hg) (key g⁻¹ (G.inv_mem hg))

omit [Finite Γ] in
theorem centralizer_vSub_le_cStarIn (G T : Subgroup Γ) :
    G ⊓ Subgroup.centralizer (vSub G T : Set Γ) ≤ cStarIn G T :=
  (inf_le_inf_left G (Subgroup.centralizer_le (omegaOneCenterOf_le_vSub G T))).trans
    (centralizer_le_cStarIn G T)

omit [Finite Γ] in
theorem vSub_conjSub {h : Γ} (hh : h ∈ G) (T : Subgroup Γ) : vSub G (conjSub h T) = vSub G T := by
  have key : ∀ (T' : Subgroup Γ) (h' : Γ), h' ∈ G →
      vSub G (conjSub h' T') ≤ vSub G T' := by
    intro T' h' hh'
    refine iSup_le fun g => ?_
    rw [omegaOneCenterOf_conjSub, ← conjSub_mul]
    exact le_iSup (fun g : G => conjSub (g : Γ) (omegaOneCenterOf T')) ⟨g * h', G.mul_mem g.2 hh'⟩
  refine le_antisymm (key T h hh) ?_
  have := key (conjSub h T) h⁻¹ (G.inv_mem hh)
  rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this

theorem le_centralizer_vSub_of_isPGroup_autOn (hT : IsSylowTwoOf T G)
    {R : Subgroup Γ} (hRG : R ≤ G) (hRn : G ≤ Subgroup.normalizer (R : Set Γ))
    (hR2 : IsPGroup 2 ↥(autOn R (vSub G T))) : R ≤ Subgroup.centralizer (vSub G T : Set Γ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup Γ := vSub G T with hVdef
  have hVn : G ≤ Subgroup.normalizer (V : Set Γ) := le_normalizer_vSub G T
  have hRV : R ≤ Subgroup.normalizer (V : Set Γ) := hRG.trans hVn
  set C₀ : Subgroup Γ := R ⊓ Subgroup.centralizer (V : Set Γ) with hC₀
  have hcard : Nat.card (autOn R V) = C₀.relIndex R := card_autOn_eq_relIndex hRV
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hS : IsSylowTwoOf (T ⊓ R) R := B6.isSylowTwoOf_inf_normal hT hRG hRn
  have hCn : G ≤ Subgroup.normalizer (C₀ : Set Γ) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hRn hg, B6.le_normalizer_centralizer hVn hg⟩
  have hTRn : (T ⊓ R) ≤ Subgroup.normalizer (C₀ : Set Γ) := fun t ht => hCn (hT.1 ht.1)
  have hP₀ : R ≤ (T ⊓ R) ⊔ C₀ := by
    have h1 : (T ⊓ R) ≤ (T ⊓ R) ⊔ C₀ := le_sup_left
    have h2 : C₀ ≤ (T ⊓ R) ⊔ C₀ := le_sup_right
    have hd1 : ((T ⊓ R) ⊔ C₀).relIndex R ∣ (T ⊓ R).relIndex R :=
      Subgroup.relIndex_dvd_of_le_left R h1
    have hd2 : ((T ⊓ R) ⊔ C₀).relIndex R ∣ C₀.relIndex R := Subgroup.relIndex_dvd_of_le_left R h2
    rw [← hcard, hk] at hd2
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd2
    have hj0 : j = 0 := by
      by_contra hne
      have h2' : 2 ∣ ((T ⊓ R) ⊔ C₀).relIndex R := by
        rw [hj]
        exact dvd_pow_self 2 hne
      exact hS.2.2 (h2'.trans hd1)
    rw [hj0, pow_zero] at hj
    exact Subgroup.relIndex_eq_one.1 hj
  have hZ : omegaOneCenterOf T ≤ V ⊓ Subgroup.centralizer (R : Set Γ) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨hxZ, hx2⟩
    have hxZ' : x ∈ T ⊓ Subgroup.centralizer (T : Set Γ) := hxZ
    have hxV : x ∈ V := omegaOneCenterOf_le_vSub G T (Subgroup.subset_closure ⟨hxZ, hx2⟩)
    refine ⟨hxV, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
    have hr' : r ∈ ((T ⊓ R : Subgroup Γ) ⊔ C₀ : Subgroup Γ) := hP₀ hr
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ C₀ hTRn] at hr'
    obtain ⟨t, ht, c, hc, rfl⟩ := hr'
    have h1 : t * x = x * t := Subgroup.mem_centralizer_iff.1 hxZ'.2 t ht.1
    have h2 : c * x = x * c := (Subgroup.mem_centralizer_iff.1 hc.2 x hxV).symm
    calc t * c * x = t * (c * x) := by group
      _ = t * (x * c) := by rw [h2]
      _ = (t * x) * c := by group
      _ = (x * t) * c := by rw [h1]
      _ = x * (t * c) := by group
  have hZn : G ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (R : Set Γ) : Subgroup Γ) : Set Γ) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hVn hg, B6.le_normalizer_centralizer hRn hg⟩
  have hVZ : V ≤ V ⊓ Subgroup.centralizer (R : Set Γ) := by
    refine iSup_le fun g => ?_
    have h1 := conjSub_mono (g : Γ) hZ
    rwa [conjSub_eq_of_mem_normalizer (hZn g.2)] at h1
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.1 (hVZ hv).2 r hr).symm

end CFSG.CGT.PushingUpLit.BHS7

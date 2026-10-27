module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.H13.A5S1327d

public section
namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_F_F4 (h331 : Stmt3_3_1_F4)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    ∃ F : ↥H →* Equiv.Perm (Fin 3),
      (∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (S.UH H : Set G)) ∧
      Function.Surjective F ∧
      (∀ (t : G) (ht : t ∈ T), F ⟨t, hH.1.1 ht⟩ ^ 2 = 1) ∧
      (∀ (k : G) (hk : k ∈ oTwoUpper H), F ⟨k, oTwoUpper_le H hk⟩ ^ 3 = 1) := by
  classical
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar_F4 h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hHN : H ≤ Subgroup.normalizer (S.UH H : Set G) := hUred.2.1
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  obtain ⟨p, hp, hp2, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  obtain ⟨eS3⟩ := hS3
  have e3 : ↥(autI hUel H) ≃* Equiv.Perm (Fin 3) := eS3
  set f : ↥H →* MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hUel) :=
    convHom hUel H hHN with hf
  have hfmem : ∀ h : ↥H, f h ∈ autI hUel H := fun h => convI_mem_autI hUel h.2 (hHN h.2)
  set F : ↥H →* Equiv.Perm (Fin 3) :=
    e3.toMonoidHom.comp (f.codRestrict (autI hUel H) hfmem) with hFdef
  have hF1 : ∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (S.UH H : Set G) := by
    intro h
    have e1 : F h = 1 ↔ f h = 1 := by
      have : F h = e3 (f.codRestrict (autI hUel H) hfmem h) := rfl
      rw [this, MulEquiv.map_eq_one_iff]
      constructor
      · intro h1
        exact congrArg Subtype.val h1
      · intro h1
        exact Subtype.ext h1
    rw [e1]
    have : f h = convI hUel ⟨h, hHN h.2⟩ := rfl
    rw [this]
    exact convI_eq_one_iff hUel _
  refine ⟨F, hF1, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨g, hgH, hg⟩ := (mem_autI hUel).1 (e3.symm σ).2
    refine ⟨⟨g, hgH⟩, ?_⟩
    have e : f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩ = e3.symm σ := by
      apply Subtype.ext
      exact hg
    have : F ⟨g, hgH⟩ = e3 (f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩) := rfl
    rw [this, e, MulEquiv.apply_symm_apply]
  · intro t ht
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨t, ht⟩
    have hb' : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ b = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hb)
    refine perm3_sq_of_two_pow (k := b) ?_
    rw [← map_pow, hb', map_one]
  · intro k hk
    obtain ⟨a, ha⟩ := hpow k hk
    refine perm3_cube_of_prime_pow (a := a) hp hp2 ?_
    rw [← map_pow]
    refine (hF1 _).2 ?_
    exact hO2U ha

theorem exists_gen_F4 (h331 : Stmt3_3_1_F4)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) {F : ↥H →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (S.UH H : Set G))
    (hFsurj : Function.Surjective F) (hFT : ∀ (t : G) (ht : t ∈ T), F ⟨t, hH.1.1 ht⟩ ^ 2 = 1)
    (hFL : ∀ (k : G) (hk : k ∈ oTwoUpper H), F ⟨k, oTwoUpper_le H hk⟩ ^ 3 = 1) :
    ∃ (y : G) (hy : y ∈ oTwoUpper H), Odd (orderOf y) ∧ F ⟨y, oTwoUpper_le H hy⟩ ≠ 1 ∧
      oTwoUpper H ≤ Subgroup.zpowers y ⊔ pCoreOf 2 H := by
  classical
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar_F4 h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨-, -, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hZU : quasithinOmegaOneCenter T ≤ S.UH H := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  set LH := oTwoUpper H with hLH
  have hLHH : LH ≤ H := oTwoUpper_le H
  have hHeq : H = LH ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl
  have hTLH : T ≤ Subgroup.normalizer (LH : Set G) := hTH.trans (le_normalizer_oTwoUpper H)
  obtain ⟨l, hl, hFl⟩ : ∃ (l : G) (hl : l ∈ LH), F ⟨l, hLHH hl⟩ ≠ 1 := by
    by_contra hne
    push Not at hne
    obtain ⟨γ, hγ⟩ := perm3_exists_sq_ne_one
    obtain ⟨⟨h, hh⟩, hhγ⟩ := hFsurj γ
    have hh' : h ∈ ((LH ⊔ T : Subgroup G) : Set G) := by rw [← hHeq]; exact hh
    rw [Subgroup.coe_mul_of_right_le_normalizer_left LH T hTLH] at hh'
    obtain ⟨k, hk, t, ht, rfl⟩ := hh'
    have e : (⟨k * t, hh⟩ : ↥H) = ⟨k, hLHH hk⟩ * ⟨t, hTH ht⟩ := rfl
    rw [e, map_mul, hne k hk, one_mul] at hhγ
    exact hγ (hhγ ▸ hFT t ht)
  obtain ⟨e, m, hm, hlm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l).ne'
  set y := l ^ 2 ^ e with hy
  have hyL : y ∈ LH := LH.pow_mem hl _
  have hyo : Odd (orderOf y) := by
    have : orderOf y = m := by
      rw [hy, orderOf_pow' l (pow_ne_zero _ two_ne_zero), hlm, Nat.gcd_mul_right_left]
      exact Nat.mul_div_cancel_left m (pow_pos two_pos e)
    rw [this]
    exact hm
  have hFy : F ⟨y, hLHH hyL⟩ ≠ 1 := by
    intro h1
    have e1 : (⟨y, hLHH hyL⟩ : ↥H) = ⟨l, hLHH hl⟩ ^ 2 ^ e := rfl
    rw [e1, map_pow] at h1
    exact hFl (eq_one_of_pow_coprime (hFL l hl) h1 (Nat.Coprime.pow_right e (by norm_num)))
  refine ⟨y, hyL, hyo, hFy, ?_⟩
  have hcover : LH ≤ Subgroup.zpowers y ⊔ (H ⊓ Subgroup.centralizer (S.UH H : Set G)) := by
    intro k hk
    have hmem : ∀ j : ℕ, F ⟨k, hLHH hk⟩ = F ⟨y, hLHH hyL⟩ ^ j →
        k ∈ Subgroup.zpowers y ⊔ (H ⊓ Subgroup.centralizer (S.UH H : Set G)) := by
      intro j hj
      have hyj : y ^ j ∈ H := H.pow_mem (hLHH hyL) j
      have hmemH : (y ^ j)⁻¹ * k ∈ H := H.mul_mem (H.inv_mem hyj) (hLHH hk)
      have hc : (y ^ j)⁻¹ * k ∈ H ⊓ Subgroup.centralizer (S.UH H : Set G) := by
        refine ⟨hmemH, (hF1 ⟨_, hmemH⟩).1 ?_⟩
        have e1 : (⟨(y ^ j)⁻¹ * k, hmemH⟩ : ↥H) =
            (⟨y, hLHH hyL⟩ ^ j)⁻¹ * ⟨k, hLHH hk⟩ := rfl
        rw [e1, map_mul, map_inv, map_pow, hj, inv_mul_cancel]
      have e2 : k = y ^ j * ((y ^ j)⁻¹ * k) := by group
      rw [e2]
      exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) j) hc
    rcases perm3_cyclic _ _ hFy (hFL y hyL) (hFL k hk) with h1 | h1 | h1
    · exact hmem 0 (by rw [h1, pow_zero])
    · exact hmem 1 (by rw [h1, pow_one])
    · exact hmem 2 h1
  have h2 : twoResidual H ≤ Subgroup.zpowers y ⊔ kerIn (H ⊓ M) H := by
    rw [twoResidual_eq_oTwoUpper']
    exact hcover.trans (sup_le_sup_left (hMP.inf_centralizer_le_kerIn hUred hHU) _)
  have h3 := hMP.twoResidual_le_sup_pCoreOf hsolv
    (Subgroup.zpowers_le.mpr (hLHH hyL)) h2
  rwa [twoResidual_eq_oTwoUpper'] at h3

end Setting

end CFSG.Quasithin.H13.A5

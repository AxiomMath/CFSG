module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327bS331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.H13.A5S1327d

public section
namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem false_of_P_le_R1_F4 (h331 : Stmt3_3_1_F4)
    (h311 : Theorem311Stmt) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hPR' : pCoreOf 2 H ⊓ oTwoUpper H ≤ S.R1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar_F4 h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  set U := S.UH H with hUdef
  set LH := oTwoUpper H with hLH
  set P := pCoreOf 2 H ⊓ LH with hP
  have hLHH : LH ≤ H := oTwoUpper_le H
  have hHLH : H ≤ Subgroup.normalizer (LH : Set G) := le_normalizer_oTwoUpper H
  have hHeq : H = LH ⊔ T := eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl
  have hTLH : T ≤ Subgroup.normalizer (LH : Set G) := hTH.trans hHLH
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hZU : quasithinOmegaOneCenter T ≤ U := le_conjClosure _ _
  have hHU : ¬ H ≤ Subgroup.centralizer (U : Set G) :=
    fun h => hHZ (h.trans (Subgroup.centralizer_le hZU))
  have hUO2 : U ≤ pCoreOf 2 H := hUO.trans inf_le_left
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_pCoreOf 2 H hh, hHLH hh⟩
  have hP2 : IsPGroup 2 P := (pCoreOf_isPGroup 2 H).to_le inf_le_left
  have hLHM : ¬ LH ≤ M := fun h => hH.2.1 (hHeq ▸ sup_le h S.T_le_NL)
  obtain ⟨p, hp, hp2, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  have h2P : ∀ k ∈ LH, (∃ b : ℕ, k ^ 2 ^ b = 1) → k ∈ P := by
    rintro k hk ⟨b, hb⟩
    obtain ⟨a, ha⟩ := hpow k hk
    exact ⟨mem_of_two_pow_of_prime_pow hp hp2 hb ha, hk⟩
  have hPR : P ≤ S.R1 := hPR'
  obtain ⟨eS3⟩ := hS3
  have e3 : ↥(autI hUel H) ≃* Equiv.Perm (Fin 3) := eS3
  set f : ↥H →* MulAut (IntMod (conjClosure (quasithinOmegaOneCenter T) H) hUel) :=
    convHom hUel H hHN with hf
  have hfmem : ∀ h : ↥H, f h ∈ autI hUel H := fun h => convI_mem_autI hUel h.2 (hHN h.2)
  set F : ↥H →* Equiv.Perm (Fin 3) :=
    e3.toMonoidHom.comp (f.codRestrict (autI hUel H) hfmem) with hFdef
  have hF1 : ∀ h : ↥H, F h = 1 ↔ (h : G) ∈ Subgroup.centralizer (U : Set G) := by
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
  have hFsurj : Function.Surjective F := by
    intro σ
    obtain ⟨g, hgH, hg⟩ := (mem_autI hUel).1 (e3.symm σ).2
    refine ⟨⟨g, hgH⟩, ?_⟩
    have e : f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩ = e3.symm σ := by
      apply Subtype.ext
      exact hg
    have : F ⟨g, hgH⟩ = e3 (f.codRestrict (autI hUel H) hfmem ⟨g, hgH⟩) := rfl
    rw [this, e, MulEquiv.apply_symm_apply]
  have hFT : ∀ (t : G) (ht : t ∈ T), F ⟨t, hTH ht⟩ ^ 2 = 1 := by
    intro t ht
    obtain ⟨b, hb⟩ := S.isPGroup_T ⟨t, ht⟩
    have hb' : (⟨t, hTH ht⟩ : ↥H) ^ 2 ^ b = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hb)
    refine perm3_sq_of_two_pow (k := b) ?_
    rw [← map_pow, hb', map_one]
  have hFL : ∀ (k : G) (hk : k ∈ LH), F ⟨k, hLHH hk⟩ ^ 3 = 1 := by
    intro k hk
    obtain ⟨a, ha⟩ := hpow k hk
    refine perm3_cube_of_prime_pow (a := a) hp hp2 ?_
    rw [← map_pow]
    refine (hF1 _).2 ?_
    exact hO2U ha
  have hFne : ∃ (l : G) (hl : l ∈ LH), F ⟨l, hLHH hl⟩ ≠ 1 := by
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
  have hcover : ∀ Y : Subgroup G, Y ≤ LH → ¬ Y ≤ Subgroup.centralizer (U : Set G) →
      LH ≤ Y ⊔ (H ⊓ Subgroup.centralizer (U : Set G)) := by
    intro Y hYL hYU
    obtain ⟨y, hyY, hyU⟩ := IsConcreteLE.not_le_iff_exists.1 hYU
    have hyL : y ∈ LH := hYL hyY
    have hy1 : F ⟨y, hLHH hyL⟩ ≠ 1 := fun h => hyU ((hF1 _).1 h)
    intro k hk
    have hmem : ∀ (c : G) (hc : c ∈ Y), F ⟨c, hLHH (hYL hc)⟩ = F ⟨k, hLHH hk⟩ →
        k ∈ Y ⊔ (H ⊓ Subgroup.centralizer (U : Set G)) := by
      intro c hc hck
      have hcH : c ∈ H := hLHH (hYL hc)
      have hck' : c⁻¹ * k ∈ H ⊓ Subgroup.centralizer (U : Set G) := by
        refine ⟨H.mul_mem (H.inv_mem hcH) (hLHH hk), ?_⟩
        have e : (⟨c⁻¹ * k, H.mul_mem (H.inv_mem hcH) (hLHH hk)⟩ : ↥H) =
            (⟨c, hcH⟩ : ↥H)⁻¹ * ⟨k, hLHH hk⟩ := rfl
        refine (hF1 ⟨c⁻¹ * k, H.mul_mem (H.inv_mem hcH) (hLHH hk)⟩).1 ?_
        rw [e, map_mul, map_inv, ← hck, inv_mul_cancel]
      have e : k = c * (c⁻¹ * k) := by group
      rw [e]
      exact Subgroup.mul_mem_sup hc hck'
    rcases perm3_cyclic _ _ hy1 (hFL y hyL) (hFL k hk) with h1 | h1 | h1
    · exact Subgroup.mem_sup_right ⟨hLHH hk, (hF1 _).1 h1⟩
    · exact hmem y hyY h1.symm
    · refine hmem (y ^ 2) (Y.pow_mem hyY 2) ?_
      rw [h1, ← map_pow]
      rfl
  have hR1T : S.R1 ≤ T := S.R1_le_T
  have hTR1 : T ≤ Subgroup.normalizer (S.R1 : Set G) := by
    have key : ∀ t ∈ T, ∀ x ∈ S.R1, t * x * t⁻¹ ∈ S.R1 := by
      intro t ht x hx
      have hxT : x ∈ T := hR1T hx
      have htxT : t * x * t⁻¹ ∈ T := T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht)
      refine (S.mem_R1 htxT).2 ?_
      have e : (⟨t * x * t⁻¹, S.frame.T_le htxT⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          ⟨t, S.frame.T_le ht⟩ * ⟨x, S.frame.T_le hxT⟩ * (⟨t, S.frame.T_le ht⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact InK4_conj_of_InD _ _ (S.frame.T_D _ ht) ((S.mem_R1 hxT).1 hx)
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t ht x, fun hx => ?_⟩
    have := key t⁻¹ (T.inv_mem ht) _ hx
    simpa [mul_assoc] using this
  have hR12 : IsPGroup 2 S.R1 := S.isPGroup_T.to_le hR1T
  have hR1LH : S.R1 ≤ Subgroup.normalizer (LH : Set G) := hR1T.trans hTLH
  have hR1M : S.R1 ≤ M := hR1T.trans S.T_le_NL
  set X := LH ⊔ S.R1 with hXdef
  have hXH : X ≤ H := sup_le hLHH (hR1T.trans hTH)
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := by
    rw [hHeq]
    refine sup_le ?_ ?_
    · intro k hk
      exact (le_sup_left : LH ≤ X).trans Subgroup.le_normalizer hk
    · intro t ht
      have fwd : ∀ s ∈ T, ∀ x ∈ X, s * x * s⁻¹ ∈ X := by
        intro s hs x hx
        have hle : X ≤ X.comap (MulAut.conj s).toMonoidHom := by
          refine sup_le (fun k hk => ?_) (fun r hr => ?_)
          · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hTLH hs) k).mp hk)
          · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hTR1 hs) r).mp hr)
        have := hle hx
        simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fwd t ht x, fun hx => ?_⟩
      have := fwd t⁻¹ (T.inv_mem ht) _ hx
      simpa [mul_assoc] using this
  have hsylX : IsSylowTwoOf S.R1 X :=
    isSylowTwoOf_sup_of_two_elements hR12 hR1LH fun k hk hk2 => hPR (h2P k hk hk2)
  have hXM : ¬ X ≤ M := fun h => hLHM (le_sup_left.trans h)
  have hmin : ∀ Y : Subgroup G, S.R1 ≤ Y → Y < X → Y ≤ M := by
    intro Y hR1Y hYX
    by_cases hYU : Y ⊓ LH ≤ Subgroup.centralizer (U : Set G)
    · intro y hy
      have hy' : y ∈ ((LH ⊔ S.R1 : Subgroup G) : Set G) := hYX.le hy
      rw [Subgroup.coe_mul_of_right_le_normalizer_left LH S.R1 hR1LH] at hy'
      obtain ⟨k, hk, r, hr, rfl⟩ := hy'
      have hkY : k ∈ Y := by
        have e : k = (k * r) * r⁻¹ := by group
        rw [e]
        exact Y.mul_mem hy (Y.inv_mem (hR1Y hr))
      have hkJ : k ∈ kerIn (H ⊓ M) H :=
        hMP.inf_centralizer_le_kerIn hUred hHU ⟨hLHH hk, hYU ⟨hkY, hk⟩⟩
      exact M.mul_mem (kerIn_le hkJ).2 (hR1M hr)
    · exfalso
      have h1 := hcover (Y ⊓ LH) inf_le_right hYU
      have h2 : twoResidual H ≤ (Y ⊓ LH) ⊔ kerIn (H ⊓ M) H := by
        rw [twoResidual_eq_oTwoUpper']
        exact h1.trans (sup_le_sup_left (hMP.inf_centralizer_le_kerIn hUred hHU) _)
      have h3 := hMP.twoResidual_le_sup_pCoreOf hsolv (inf_le_right.trans hLHH) h2
      rw [twoResidual_eq_oTwoUpper'] at h3
      have hLY : LH ≤ Y := by
        intro k hk
        have hk' : k ∈ (((Y ⊓ LH) ⊔ pCoreOf 2 H : Subgroup G) : Set G) := h3 hk
        rw [Subgroup.coe_mul_of_left_le_normalizer_right (Y ⊓ LH) (pCoreOf 2 H)
          ((inf_le_right.trans hLHH).trans (le_normalizer_pCoreOf 2 H))] at hk'
        obtain ⟨y, hy, q, hq, rfl⟩ := hk'
        have hqL : q ∈ LH := by
          have e : q = y⁻¹ * (y * q) := by group
          rw [e]
          exact LH.mul_mem (LH.inv_mem hy.2) hk
        exact Y.mul_mem hy.1 (hR1Y (hPR ⟨hq, hqL⟩))
      exact hYX.not_ge (sup_le hLY hR1Y)
  have hFX : CharTwo X :=
    CharTwo.of_normal hF hXH ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX)
  have hXZ : ¬ X ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := fun h =>
    hHZ (hHeq ▸ sup_le (le_sup_left.trans h) (T_le_centralizer_omegaOneCenter T))
  have hsolvX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXH)
  have hSQTX : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q X ≤ 2 := fun q hq hq2 =>
    (CFSG.SectionRank.pRank_mono hq.one_lt hXH).trans (hSQT q hq hq2)
  have hLX : LH ≤ oTwoUpper X := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact mem_oTwoUpper_of_odd (Subgroup.mem_sup_left (Subgroup.subset_closure hx)) hx.2
  exact hH.2.1 (S.le_M_of_minParabolic h311 hsylX hXM hmin hFX hXZ hsolvX hSQTX
    (inf_le_right.trans hLX) hPR hH.1 ⟨_, hMP.uniqueMax⟩ h2P)

theorem not_threeTop_F4 (h331 : Stmt3_3_1_F4) (h311 : Theorem311Stmt)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    ¬ ThreeTop (S.H0 H) := fun h3 =>
  S.false_of_P_le_R1_F4 h331 h311 hH hHZ hsolv hS3 (S.le_R1_of_threeTop hH.1.1 h3)

end Setting

theorem lemma13213_of_F4 (h331 : Stmt3_3_1_F4) (h311 : Theorem311Stmt) :
    Lemma13213_F4 := fun _ _ _ _ _ _ S _ hH hHZ hsolv hS3 =>
  S.not_threeTop_F4 h331 h311 hH hHZ hsolv hS3

end CFSG.Quasithin.H13.A5

module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Lift
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Num

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local.P27

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem us_le_preimage (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ S) (htc : IsConj z t)
    (hsw : Swaps z t L₁ L₂) {P₁ : Subgroup G}
    (hP₁ : P₁ = (L₁.comap (rhoS hS)).map S.subtype) {A : Subgroup (CentralizerBar z)}
    (hA : ∀ B : Subgroup (CentralizerBar z), B ≤ CL z t → ⁅B, B⁆ = B → B ≤ A) :
    Psp4.US P₁ t ≤ (A.comap (toBar z)).map (Cen z).subtype := by
  have hSC := S_le_Cen hS
  have htC : t ∈ Cen z := hSC ht
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have ht2 : t * t = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  set tb : CentralizerBar z := toBar z ⟨t, htC⟩ with htb
  have htb2 : tb * tb = 1 := by
    rw [htb, ← map_mul]
    have : (⟨t, htC⟩ : ↥(Cen z)) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have htbinv : tb⁻¹ = tb := inv_eq_of_mul_eq_one_right htb2
  obtain ⟨htC', hc1, hc2⟩ := hsw
  have hconj : ∀ (Y : Subgroup (CentralizerBar z)) (x : CentralizerBar z),
      x ∈ conjugate Y tb ↔ tb * x * tb⁻¹ ∈ Y := fun Y x => by
    unfold conjugate
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hswap : ∀ x ∈ L₁, tb * x * tb⁻¹ ∈ L₂ := fun x hx =>
    (hconj L₂ x).1 (by rw [hc2]; exact hx)
  have hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x := hP.prod.2.1
  have hL₁perf : Group.IsPerfect ↥L₁ := by
    have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
      rw [hP.comps]; exact Set.mem_insert _ _
    exact this.1.1
  let δ : ↥L₁ →* CentralizerBar z :=
    { toFun := fun x => (x : CentralizerBar z) * (tb * (x : CentralizerBar z) * tb⁻¹)
      map_one' := by
        simp only [Subgroup.coe_one]
        group
      map_mul' := fun x y => by
        have h1 := hcomm (y : CentralizerBar z) y.2 _ (hswap _ x.2)
        show ((x * y : ↥L₁) : CentralizerBar z) * (tb * ((x * y : ↥L₁) : CentralizerBar z) * tb⁻¹) =
          ((x : CentralizerBar z) * (tb * (x : CentralizerBar z) * tb⁻¹)) *
            ((y : CentralizerBar z) * (tb * (y : CentralizerBar z) * tb⁻¹))
        simp only [Subgroup.coe_mul]
        calc ((x : CentralizerBar z) * (y : CentralizerBar z)) *
              (tb * ((x : CentralizerBar z) * (y : CentralizerBar z)) * tb⁻¹)
            = (x : CentralizerBar z) * ((y : CentralizerBar z) * (tb * (x : CentralizerBar z) * tb⁻¹))
                * (tb * (y : CentralizerBar z) * tb⁻¹) := by group
          _ = (x : CentralizerBar z) * ((tb * (x : CentralizerBar z) * tb⁻¹) * (y : CentralizerBar z))
                * (tb * (y : CentralizerBar z) * tb⁻¹) := by rw [h1]
          _ = ((x : CentralizerBar z) * (tb * (x : CentralizerBar z) * tb⁻¹)) *
                ((y : CentralizerBar z) * (tb * (y : CentralizerBar z) * tb⁻¹)) := by group }
  have hδ : ∀ x : ↥L₁, δ x = (x : CentralizerBar z) * (tb * (x : CentralizerBar z) * tb⁻¹) :=
    fun x => rfl
  have hδCL : δ.range ≤ CL z t := by
    rw [Stage1.Main.CL_eq_centralizer htC hP.prod.1]
    rintro _ ⟨x, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff, hδ]
      have hxy := hcomm (x : CentralizerBar z) x.2 _ (hswap _ x.2)
      have hy : tb * (tb * (x : CentralizerBar z) * tb⁻¹) * tb⁻¹ = (x : CentralizerBar z) := by
        calc tb * (tb * (x : CentralizerBar z) * tb⁻¹) * tb⁻¹
            = (tb * tb) * (x : CentralizerBar z) * (tb⁻¹ * tb⁻¹) := by group
          _ = (x : CentralizerBar z) := by rw [htb2, htbinv, htb2]; group
      calc (x : CentralizerBar z) * (tb * (x : CentralizerBar z) * tb⁻¹) * tb
          = (tb * (x : CentralizerBar z) * tb⁻¹) * (x : CentralizerBar z) * tb := by rw [hxy]
        _ = (tb * (x : CentralizerBar z) * tb⁻¹) * (tb * (tb * (x : CentralizerBar z) * tb⁻¹) * tb⁻¹) * tb := by rw [hy]
        _ = tb * ((x : CentralizerBar z) * (tb * (x : CentralizerBar z) * tb⁻¹)) := by group
    · rw [hδ]
      exact Subgroup.mul_mem_sup x.2 (hswap _ x.2)
  have hδperf : ⁅δ.range, δ.range⁆ = δ.range :=
    Subgroup.isPerfect_iff.1
      (Group.IsPerfect.ofSurjective (f := δ.rangeRestrict) δ.rangeRestrict_surjective)
  have hδA : δ.range ≤ A := hA _ hδCL hδperf
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [hP₁] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have hxS : (s : G) ∈ S := s.2
  have hgS : (s : G) * (t * (s : G) * t⁻¹) ∈ S :=
    S.mul_mem hxS (S.mul_mem (S.mul_mem ht hxS) (S.inv_mem ht))
  refine ⟨⟨(s : G) * (t * (s : G) * t⁻¹), hSC hgS⟩, ?_, rfl⟩
  show toBar z ⟨(s : G) * (t * (s : G) * t⁻¹), hSC hgS⟩ ∈ A
  have hs' : rhoS hS s ∈ L₁ := hs
  have e : toBar z ⟨(s : G) * (t * (s : G) * t⁻¹), hSC hgS⟩ =
      (rhoS hS s) * (tb * (rhoS hS s) * tb⁻¹) := by
    have : (⟨(s : G) * (t * (s : G) * t⁻¹), hSC hgS⟩ : ↥(Cen z)) =
        ⟨(s : G), hSC hxS⟩ * (⟨t, htC⟩ * ⟨(s : G), hSC hxS⟩ * ⟨t, htC⟩⁻¹) := rfl
    rw [this, map_mul, map_mul, map_mul, map_inv]
    rfl
  rw [e]
  exact hδA ⟨⟨rhoS hS s, hs'⟩, rfl⟩

omit [Finite G] in
theorem us_two_pow (hS : IsSylowOf 2 S (Cen z)) {u : G} (hu : u ∈ S) : ∃ k : ℕ, u ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (S_isPGroup hS)) ⟨u, hu⟩
  refine ⟨k, ?_⟩
  have : (⟨u, hu⟩ : ↥S) ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  simpa using congrArg Subtype.val this

theorem us_le_ixz_and_sylow (hz : IsCentralInvolution z) (hS : IsSylowOf 2 S (Cen z))
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (ht : t ∈ S) (htc : IsConj z t)
    (hsw : Swaps z t L₁ L₂) {P₁ : Subgroup G} {a : ℕ}
    (hP₁ : P₁ = (L₁.comap (rhoS hS)).map S.subtype) (hPc : Nat.card ↥P₁ = 2 ^ a)
    (hS' : IsSylowOf 2 (S ⊓ centralizer ({t} : Set G)) (centralizer ({t * z, z} : Set G)))
    (hUle : Psp4.US P₁ t ≤ S ⊓ centralizer ({t} : Set G))
    (hUc : Nat.card ↥(Psp4.US P₁ t) = 2 ^ (a - 1)) :
    Psp4.US P₁ t ≤ Ixz z (t * z) ∧ IsSylowOf 2 (Psp4.US P₁ t) (Ixz z (t * z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSC := S_le_Cen hS
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have ht2 : t * t = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  obtain ⟨-, A, hbar, hACL, hAcard, hAperf⟩ := ixz_L2_ext hz hS hP ht htc hsw
  have hIY : Ixz z (t * z) ≤ centralizer ({t * z, z} : Set G) := ixz_le_centralizer z t
  have hYC : centralizer ({t * z, z} : Set G) ≤ Cen z := fun y hy =>
    Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact Subgroup.mem_centralizer_iff.1 hy z (by simp))
  have hn : ((Ixz z (t * z)).subgroupOf (centralizer ({t * z, z} : Set G))).Normal := ixz_normal z t
  have hUY : S ⊓ centralizer ({t} : Set G) ≤ centralizer ({t * z, z} : Set G) := hS'.le
  have hpre := us_le_preimage hz hS hP ht htc hsw hP₁ hAperf
  have hUI : Psp4.US P₁ t ≤ Ixz z (t * z) := by
    intro u hu
    obtain ⟨c, hcA, hcu⟩ := hpre hu
    have huY : u ∈ centralizer ({t * z, z} : Set G) := hUY (hUle hu)
    obtain ⟨k, hk⟩ := us_two_pow hS (hUle hu).1
    refine mem_of_toBar_mem hIY hYC hn huY ⟨k, hk⟩ ?_
    rw [hbar]
    have : (⟨u, hYC huY⟩ : ↥(Cen z)) = c := Subtype.ext hcu.symm
    rw [this]
    exact hcA
  refine ⟨hUI, ?_⟩
  have hnorm : centralizer ({t * z, z} : Set G) ≤ normalizer ((Ixz z (t * z) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIY).1 hn
  have hU0 : IsSylowOf 2 ((S ⊓ centralizer ({t} : Set G)) ⊓ Ixz z (t * z)) (Ixz z (t * z)) :=
    hS'.inf_of_le_normalizer hIY hnorm
  have hUUo : Psp4.US P₁ t ≤ (S ⊓ centralizer ({t} : Set G)) ⊓ Ixz z (t * z) := le_inf hUle hUI
  have hfac : (Nat.card ↥(Ixz z (t * z))).factorization 2 + 1 = a := by
    rw [factorization_card_barOf (hIY.trans hYC), hbar]
    exact factorization_card_A hAcard (factorization_card_CL hS hP hsw ht2 hP₁ hPc)
  have hc := hU0.card_eq
  have hle : Nat.card ↥((S ⊓ centralizer ({t} : Set G)) ⊓ Ixz z (t * z)) ≤
      Nat.card ↥(Psp4.US P₁ t) := by
    rw [hc, hUc]
    apply le_of_eq
    congr 1
    omega
  have hEq : Psp4.US P₁ t = (S ⊓ centralizer ({t} : Set G)) ⊓ Ixz z (t * z) :=
    Subgroup.eq_of_le_of_card_ge hUUo hle
  rw [hEq]
  exact hU0

end CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1

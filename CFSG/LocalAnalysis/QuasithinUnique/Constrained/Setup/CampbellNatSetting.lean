module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellFrattiniKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBaumannTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellOffender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellUtil
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedCore
public import CFSG.Quasithin.Background.A1bBasic

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Open CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.BlueprintB2
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
open scoped LinearAlgebra.Projectivization

section Natural

theorem elemThompson_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) (p : ℕ) [Fact p.Prime] :
    (elemThompson X p).map e.toMonoidHom = elemThompson Y p := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_elemThompson (mem_elemThompsonFamily_map e p hA)
  · refine sSup_le fun B hB => ?_
    have hB' : B.map e.symm.toMonoidHom ∈ elemThompsonFamily X p :=
      mem_elemThompsonFamily_map e.symm p hB
    intro y hy
    have : e.symm y ∈ elemThompson X p := le_elemThompson hB' ⟨y, hy, rfl⟩
    exact ⟨e.symm y, this, e.apply_symm_apply y⟩

theorem elemThompsonIn_map_of_injective {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (p : ℕ) [Fact p.Prime] (f : G →* G') (hf : Function.Injective f) (A : Subgroup G) :
    elemThompsonIn p (A.map f) = (elemThompsonIn p A).map f := by
  let e : A ≃* A.map f := A.equivMapOfInjective f hf
  have hcomp : (A.map f).subtype.comp e.toMonoidHom = f.comp A.subtype := by
    ext x; rfl
  unfold elemThompsonIn
  rw [← elemThompson_map_mulEquiv e p, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem pRank_map_of_injective {G G' : Type*} [Group G] [Group G'] (p : ℕ) (f : G →* G')
    (hf : Function.Injective f) (A : Subgroup G) : pRank p (A.map f) = pRank p A :=
  (pRank_eq_of_mulEquiv (A.equivMapOfInjective f hf) p).symm

variable {G : Type*} [Group G] [Finite G]

theorem elemThompsonIn_elemThompsonIn (p : ℕ) [Fact p.Prime] (R : Subgroup G) :
    elemThompsonIn p (elemThompsonIn p R) = elemThompsonIn p R := by
  have h := elemThompsonIn_map_of_injective p R.subtype R.subtype_injective (elemThompson R p)
  show elemThompsonIn p ((elemThompson R p).map R.subtype) = (elemThompson R p).map R.subtype
  rw [h]
  congr 1
  exact elemThompson_map_subtype (Y := elemThompson R p) le_rfl

theorem pRank_elemThompsonIn (p : ℕ) [Fact p.Prime] (R : Subgroup G) :
    pRank p (elemThompsonIn p R) = pRank p R := by
  unfold elemThompsonIn
  rw [pRank_map_of_injective p R.subtype R.subtype_injective]
  exact pRank_eq_of_elemThompson_le (Y := elemThompson R p) le_rfl

theorem elemThompson_map_subtype_self (p : ℕ) [Fact p.Prime] (R : Subgroup G) :
    (elemThompson (elemThompsonIn p R) p).map (elemThompsonIn p R).subtype =
      elemThompsonIn p R :=
  elemThompsonIn_elemThompsonIn p R

omit [Finite G] in
theorem pRank_cj (p : ℕ) (Y : Subgroup G) (g : G) : pRank p (cj Y g) = pRank p Y :=
  pRank_map_of_injective p _ (MulAut.conj g⁻¹).injective Y

theorem elemThompsonIn_cj (p : ℕ) [Fact p.Prime] (Y : Subgroup G) (g : G) :
    elemThompsonIn p (cj Y g) = cj (elemThompsonIn p Y) g :=
  elemThompsonIn_map_of_injective p (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective Y

end Natural

variable {H : Type*} [Group H] {k : Type*} [Field k]

structure IsNatQuotSetting (R M V : Subgroup H) (ρ : H →* Gamma k)
    (φ : V →* Multiplicative (Fin 2 → k)) : Prop where
  sylow : IsSylowTwoOf R (⊤ : Subgroup H)
  nonnormal : ¬ R.Normal
  le_M : R ≤ M
  M_lt : M < ⊤
  M_max : ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M
  reduced : IsTwoReducedIn (⊤ : Subgroup H) V
  sl_le : ∀ A : Matrix.SpecialLinearGroup (Fin 2) k,
    ∃ h : H, ((ρ h : Gamma k) : Equiv.Perm (Fin 2 → k)) = slPerm k A
  two_quot : ∀ h : H, ∃ m : ℕ, ρ h ^ 2 ^ m ∈ slGamma k
  φ_surj : Function.Surjective φ
  φ_equiv : ∀ (h : H) (v v' : V), (v' : H) = h * v * h⁻¹ →
    Multiplicative.toAdd (φ v') = ((ρ h : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd (φ v))
  φ_ker : φ.ker = (Subgroup.centralizer ((oddOrderSubgroup (⊤ : Subgroup H) : Subgroup H) : Set H)).subgroupOf V

namespace IsNatQuotSetting

variable {R M V : Subgroup H} {ρ : H →* Gamma k} {φ : V →* Multiplicative (Fin 2 → k)}

theorem not_le_centralizer (_h : IsNatQuotSetting R M V ρ φ)
    (hJ : ⁅elemThompsonIn 2 R, V⁆ ≠ ⊥) :
    ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H) := fun htop =>
  hJ (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_top.trans htop))

theorem normal_V (h : IsNatQuotSetting R M V ρ φ) : V.Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h.reduced.2.1)

theorem normal_L (_h : IsNatQuotSetting R M V ρ φ) :
    (oddOrderSubgroup (⊤ : Subgroup H)).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  refine top_le_iff.mp fun g _ => normalizer_le_normalizer_oddOrderSubgroup (⊤ : Subgroup H)
    (?_ : g ∈ Subgroup.normalizer ((⊤ : Subgroup H) : Set H))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp

theorem map_L_le (h : IsNatQuotSetting R M V ρ φ) :
    (oddOrderSubgroup (⊤ : Subgroup H)).map ρ ≤ slGamma k := by
  rw [Subgroup.map_le_iff_le_comap]
  refine oddOrderSubgroup_le_of_pow_mem fun x _ => ?_
  obtain ⟨m, hm⟩ := h.two_quot x
  exact ⟨m, by rw [Subgroup.mem_comap, map_pow]; exact hm⟩

theorem centralizer_le_ker (h : IsNatQuotSetting R M V ρ φ) :
    Subgroup.centralizer (V : Set H) ≤ ρ.ker := by
  intro c hc
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply Equiv.ext
  intro w
  obtain ⟨v, rfl⟩ := h.φ_surj (Multiplicative.ofAdd w)
  have hcomm : (v : H) * c = c * (v : H) := Subgroup.mem_centralizer_iff.mp hc (v : H) v.2
  have hv : (v : H) = c * (v : H) * c⁻¹ := by rw [← hcomm]; group
  have := h.φ_equiv c v v hv
  show ((ρ c : Gamma k) : Equiv.Perm (Fin 2 → k)) (Multiplicative.toAdd (φ v)) =
    Multiplicative.toAdd (φ v)
  exact this.symm

variable [Finite H] [Finite k] [CharP k 2]

omit [Finite H] [Finite k] in
theorem ker_le_kerIn (h : IsNatQuotSetting R M V ρ φ) : ρ.ker ≤ kerIn M ⊤ := by
  have hNM : ρ.ker ≤ M := by
    by_contra hNM
    have hsup : ρ.ker ⊔ R = ⊤ := by
      by_contra hne
      have hlt : ρ.ker ⊔ R < ⊤ := lt_top_iff_ne_top.mpr hne
      exact hNM (le_sup_left.trans (h.M_max _ le_sup_right hlt))
    obtain ⟨t, ht⟩ := exists_slPerm_orderOf_three (k := k)
    obtain ⟨x, hx⟩ := h.sl_le t
    obtain ⟨n, hn, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hsup ▸ (Subgroup.mem_top x) : x ∈ ρ.ker ⊔ R)
    have hρn : ρ n = 1 := hn
    obtain ⟨m, hm⟩ := h.sylow.2.1 ⟨r, hr⟩
    have h1 : ρ (n * r) = ρ r := by rw [map_mul, hρn, one_mul]
    have h2 : ((ρ r : Gamma k) : Equiv.Perm (Fin 2 → k)) ^ 2 ^ m = 1 := by
      have : ρ r ^ 2 ^ m = 1 := by
        rw [← map_pow]
        have : r ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
        rw [this, map_one]
      simpa using congrArg Subtype.val this
    have h3 : orderOf (slPerm k t) ∣ 2 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← hx, h1]
      exact h2
    rw [orderOf_injective _ slPerm_injective, ht] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  exact le_kerIn_of_le_normalizer hNM (by
    intro g _
    exact mem_normalizer_of_normal _ g)

omit [Finite k] in
theorem inf_ker_eq (h : IsNatQuotSetting R M V ρ φ)
    (hVH : ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H)) :
    R ⊓ ρ.ker = CFSG.pCore 2 H := by
  obtain ⟨-, hCR, -, -, -, -, -⟩ := minimal_parabolic_reduced_module_Frattini_kernel_production
    h.sylow h.nonnormal h.le_M h.M_lt h.M_max h.reduced hVH
  have hQ : CFSG.pCore 2 H = CFSG.Open.pCore 2 H :=
    CFSG.Quasithin.BlueprintB2.pCore_eq_open_pCore 2 H
  have hodd := (qt_A7_unique_Sylow_overgroup_core_and_simple_section h.sylow h.nonnormal h.le_M
    h.M_lt h.M_max).2.1.2.1
  apply le_antisymm
  · rintro x ⟨hxR, hxN⟩
    have hxJ : x ∈ kerIn M ⊤ := h.ker_le_kerIn hxN
    set φQ := QuotientGroup.mk' (CFSG.Open.pCore 2 H) with hφQ
    have hmem : φQ x ∈ (kerIn M ⊤).map φQ := Subgroup.mem_map_of_mem _ hxJ
    obtain ⟨m, hm⟩ := h.sylow.2.1 ⟨x, hxR⟩
    have hxm : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have h1 : orderOf (⟨φQ x, hmem⟩ : (kerIn M ⊤).map φQ) ∣ Nat.card ((kerIn M ⊤).map φQ) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (φQ x) ∣ 2 ^ m := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow, hxm, map_one]
    rw [Subgroup.orderOf_mk] at h1
    have hcop : Nat.Coprime (Nat.card ((kerIn M ⊤).map φQ)) (2 ^ m) :=
      Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
    have h3 : orderOf (φQ x) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    rw [orderOf_eq_one_iff, hφQ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
    exact h3
  · intro x hxQ
    have hxRC : x ∈ R ⊓ Subgroup.centralizer (V : Set H) := hCR ▸ hxQ
    exact ⟨hxRC.1, h.centralizer_le_ker hxRC.2⟩

omit [Finite k] in
theorem not_two_dvd_relIndex_ker (h : IsNatQuotSetting R M V ρ φ)
    (hVH : ¬ (⊤ : Subgroup H) ≤ Subgroup.centralizer (V : Set H)) :
    ¬ 2 ∣ (Subgroup.centralizer (V : Set H)).relIndex ρ.ker := by
  obtain ⟨-, hCR, -, -, -, -, -⟩ := minimal_parabolic_reduced_module_Frattini_kernel_production
    h.sylow h.nonnormal h.le_M h.M_lt h.M_max h.reduced hVH
  have : V.Normal := h.normal_V
  have hRsyl : IsSylowIn 2 R (⊤ : Subgroup H) := h.sylow
  have h1 : IsSylowIn 2 (R ⊓ ρ.ker) ρ.ker :=
    hRsyl.inf_normal (N := ρ.ker) le_top inferInstance
  have h2 : IsSylowIn 2 (R ⊓ Subgroup.centralizer (V : Set H)) (Subgroup.centralizer (V : Set H)) :=
    hRsyl.inf_normal (N := Subgroup.centralizer (V : Set H)) le_top inferInstance
  rw [h.inf_ker_eq hVH] at h1
  rw [hCR] at h2
  have hc1 := h1.card_eq
  have hc2 := h2.card_eq
  have hv : (Nat.card ρ.ker).factorization 2 = (Nat.card (Subgroup.centralizer (V : Set H))).factorization 2 :=
    Nat.pow_right_injective (le_refl 2) (hc1.symm.trans hc2)
  have hle : Subgroup.centralizer (V : Set H) ≤ ρ.ker := h.centralizer_le_ker
  have hmul := Subgroup.relIndex_mul_card (Subgroup.centralizer (V : Set H)) ρ.ker
  rw [inf_of_le_left hle] at hmul
  intro hdvd
  have hr0 : (Subgroup.centralizer (V : Set H)).relIndex ρ.ker ≠ 0 := relIndex_ne_zero_of_finite _ _
  have hc0 : Nat.card (Subgroup.centralizer (V : Set H)) ≠ 0 := Nat.card_pos.ne'
  have hfac := congrArg (fun n => n.factorization 2) hmul
  simp only [Nat.factorization_mul hr0 hc0, Finsupp.add_apply] at hfac
  have : 1 ≤ ((Subgroup.centralizer (V : Set H)).relIndex ρ.ker).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hr0).mp hdvd
  omega

end IsNatQuotSetting

end CFSG.QuasithinUnique.Setup.Campbell

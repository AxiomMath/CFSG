module

public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance

open CFSG CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ClassicalInvolution.Balance.LocalBalance
open CFSG.LocalAnalysis.ComponentInitial (normalizerConjHom ker_normalizerConjHom
  coe_normalizerConjHom_apply)

universe u

variable {Y : Type u} [Group Y] [Finite Y] {p : ℕ}

omit [Finite Y] in
theorem isPGroup_zpowers_of_pow_eq_one_f {G : Type*} [Group G] (hp : p.Prime) {g : G}
    (hg : g ^ p = 1) : IsPGroup p (Subgroup.zpowers g) := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hg) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

omit [Finite Y] in
theorem centralizer_zpowers_eq_singleton {G : Type*} [Group G] (g : G) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  ext x
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [Set.mem_singleton_iff] at hy
    exact h y (hy ▸ Subgroup.mem_zpowers g)
  · intro h y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : g * x = x * g := h g rfl
    exact (Commute.zpow_left (show Commute g x from h1) n).eq

omit [Finite Y] in
theorem gLAPPrimeCoreOf_le_self' {G : Type*} [Group G] (C : Subgroup G) :
    GLAPPrimeCoreOf p C ≤ C :=
  Subgroup.map_subtype_le _

omit [Finite Y] in
theorem gLAPPrimeCoreOf_conj_mem' {G : Type*} [Group G] {C : Subgroup G} :
    ∀ g ∈ C, ∀ x ∈ GLAPPrimeCoreOf p C, g * x * g⁻¹ ∈ GLAPPrimeCoreOf p C := by
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : ↥C) * y * (⟨g, hg⟩ : ↥C)⁻¹,
    (GLAPPrimeCore.normal p ↥C).conj_mem y hy _, ?_⟩
  simp

omit [Finite Y] in
theorem coprime_card_gLAPPrimeCoreOf' {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    (C : Subgroup G) : Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p C)) := by
  unfold GLAPPrimeCoreOf
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp ↥C

omit [Finite Y] in
theorem le_gLAPPrimeCoreOf_of_normal' {G : Type*} [Group G] {C S : Subgroup G} (hSC : S ≤ C)
    (hS : ∀ g ∈ C, ∀ x ∈ S, g * x * g⁻¹ ∈ S) (hcop : Nat.Coprime p (Nat.card S)) :
    S ≤ GLAPPrimeCoreOf p C := by
  have hnormal : (S.subgroupOf C).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hS (g : G) g.2 (x : G) hx
  have hle : S.subgroupOf C ≤ GLAPPrimeCore p C := by
    refine le_sSup (show S.subgroupOf C ∈ {N : Subgroup C | N.Normal ∧
      Nat.Coprime p (Nat.card N)} from ⟨hnormal, ?_⟩)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv]
    exact hcop
  intro x hx
  refine Subgroup.mem_map.2 ⟨⟨x, hSC hx⟩, hle ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.2 hx

theorem subgroupOf_gLAPPrimeCoreOf_centralizer_le (hp : p.Prime) {M : Subgroup Y} (m : M) :
    (GLAPPrimeCoreOf p (Subgroup.centralizer ({(m : Y)} : Set Y))).subgroupOf M ≤
      GLAPPrimeCoreOf p (Subgroup.centralizer ({m} : Set M)) := by
  set O := GLAPPrimeCoreOf p (Subgroup.centralizer ({(m : Y)} : Set Y)) with hO
  have hOC : O ≤ Subgroup.centralizer ({(m : Y)} : Set Y) := gLAPPrimeCoreOf_le_self' _
  refine le_gLAPPrimeCoreOf_of_normal' (p := p) ?_ ?_ ?_
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have := (Subgroup.mem_centralizer_iff.mp (hOC (Subgroup.mem_subgroupOf.mp hu))) (m : Y) rfl
    exact Subtype.ext this
  · intro g hg x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hgY : (g : Y) ∈ Subgroup.centralizer ({(m : Y)} : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := (Subgroup.mem_centralizer_iff.mp hg) m rfl
      exact congrArg Subtype.val this
    exact gLAPPrimeCoreOf_conj_mem' (g : Y) hgY _ hx
  · have h1 : Nat.card ((O.subgroupOf M)) =
        Nat.card ((O.subgroupOf M).map M.subtype) :=
      (Subgroup.card_map_of_injective M.subtype_injective).symm
    rw [h1, Subgroup.subgroupOf_map_subtype]
    exact (coprime_card_gLAPPrimeCoreOf' hp _).coprime_dvd_right
      (Subgroup.card_dvd_of_le inf_le_left)

theorem commute_of_faithful_p (hH1 : H1Stmt.{u}) (hp : p.Prime) {k : ℕ} {L : Subgroup Y}
    (hL : IsComponent L) {F : Subgroup Y} (hFel : IsElemAbelian p F)
    (hFcard : Nat.card F = p ^ k) (hFL : ∀ f ∈ F, conjSub f L = L)
    (hFfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f)
    (hbal : IsLocallyBalanced p k (fImage F L)) {D : Subgroup Y}
    (hD : ∀ d ∈ D, conjSub d L = L)
    (hDF : ∀ f ∈ F, f ≠ 1 → D ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({f} : Set Y))) :
    ∀ d ∈ D, ∀ x ∈ L, d * x = x * d := by
  classical
  set M : Subgroup Y := Subgroup.normalizer (L : Set Y) with hM
  have hFM : F ≤ M := fun f hf => mem_normalizer_of_conjSub_eq (hFL f hf)
  have hDM : D ≤ M := fun d hd => mem_normalizer_of_conjSub_eq (hD d hd)
  set ρ : M →* MulAut ↥L := normalizerConjHom L with hρ
  have hker : ρ.ker = (Subgroup.centralizer (L : Set Y)).subgroupOf M := ker_normalizerConjHom L
  set H' : Subgroup (MulAut ↥L) := ρ.range with hH'
  set φ : M →* H' := ρ.rangeRestrict with hφdef
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  have hInn : innerAut ↥L ≤ H' := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨x, Subgroup.le_normalizer x.2⟩, ?_⟩
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [hρ, coe_normalizerConjHom_apply]
    simp [MulAut.conj_apply]
  set F' : Subgroup M := F.subgroupOf M with hF'
  have hfI : fImage F L = F'.map ρ := rfl
  have hFinj : ∀ m ∈ F', ρ m = 1 → m = 1 := by
    intro m hm hm1
    have h1 : m ∈ ρ.ker := hm1
    rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    by_contra hne
    refine hFfaith (m : Y) ((Subgroup.mem_subgroupOf).mp hm) (fun h => hne (Subtype.ext h)) ?_
    intro x hx
    exact (h1 x hx).symm
  have hcard : Nat.card (fImage F L) = p ^ k := by
    have hbij : Function.Bijective (ρ.subgroupMap F') := by
      refine ⟨?_, ρ.subgroupMap_surjective F'⟩
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro m hm
      have := hFinj m m.2 (by
        have h2 := (MonoidHom.mem_ker.mp hm)
        have h3 := congrArg Subtype.val h2
        exact h3)
      exact Subtype.ext this
    rw [hfI, ← Nat.card_congr (Equiv.ofBijective _ hbij), ← hFcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv
  have hel : IsElemAbelian p (fImage F L) := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
      have hab : a * b = b * a := by
        have := hFel.1.is_comm.comm (⟨(a : Y), (Subgroup.mem_subgroupOf).mp ha⟩ : F)
          ⟨(b : Y), (Subgroup.mem_subgroupOf).mp hb⟩
        exact Subtype.ext (congrArg (fun z : F => (z : Y)) this)
      apply Subtype.ext
      change ρ a * ρ b = ρ b * ρ a
      rw [← map_mul, ← map_mul, hab]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hFel.2 (a : Y) ((Subgroup.mem_subgroupOf).mp ha))
      rw [this, map_one]
  have hdelta : localDeltaIn p H' (fImage F L) = ⊥ :=
    hbal _ ⟨le_rfl, hel, hcard⟩ H' hInn
      ((Subgroup.map_le_range ρ F').trans Subgroup.le_normalizer)
  have hDle : (D.subgroupOf M).map ρ ≤ localDeltaIn p H' (fImage F L) := by
    refine le_iInf fun d => le_iInf fun hd => le_iInf fun hd1 => ?_
    obtain ⟨m, hm, rfl⟩ := hd
    have hmF : (m : Y) ∈ F := (Subgroup.mem_subgroupOf).mp hm
    have hm1 : (m : Y) ≠ 1 := by
      intro h
      have hm1' : m = 1 := Subtype.ext h
      exact hd1 (by rw [hm1']; exact map_one ρ)
    have hmH : ρ m ∈ H' := ⟨m, rfl⟩
    rw [gLAPPrimeCoreOf_inf_centralizer_eq_map p H' hmH]
    have hDm : D.subgroupOf M ≤ GLAPPrimeCoreOf p (Subgroup.centralizer ({m} : Set M)) :=
      fun u hu => subgroupOf_gLAPPrimeCoreOf_centralizer_le hp m
        ((Subgroup.mem_subgroupOf).mpr
          (hDF (m : Y) hmF hm1 ((Subgroup.mem_subgroupOf).mp hu)))
    have hQ := isPGroup_zpowers_of_pow_eq_one_f hp
      (show m ^ p = 1 from Subtype.ext (hFel.2 (m : Y) hmF))
    have h1 := hH1 φ hφ hp hQ
    rw [MonoidHom.map_zpowers, centralizer_zpowers_eq_singleton,
      centralizer_zpowers_eq_singleton] at h1
    have h2 : (D.subgroupOf M).map φ ≤
        GLAPPrimeCoreOf p (Subgroup.centralizer ({(⟨ρ m, hmH⟩ : H')} : Set H')) :=
      (Subgroup.map_mono hDm).trans h1
    have h3 : (D.subgroupOf M).map ρ = ((D.subgroupOf M).map φ).map H'.subtype := by
      rw [Subgroup.map_map]
      rfl
    rw [h3]
    exact Subgroup.map_mono h2
  rw [hdelta] at hDle
  intro d hd x hx
  have hmem : ρ ⟨d, hDM hd⟩ ∈ (⊥ : Subgroup (MulAut ↥L)) :=
    hDle ⟨⟨d, hDM hd⟩, (Subgroup.mem_subgroupOf).mpr hd, rfl⟩
  have h1 : (⟨d, hDM hd⟩ : M) ∈ ρ.ker := Subgroup.mem_bot.mp hmem
  rw [hker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
  exact (h1 x hx).symm

end CFSG.HardMathSupport.Timmesfeld.Balance

module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTResC2
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTLink
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BTOFCfg
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoDih

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ABGLocalTools

section Fix

variable {A : Type*} [Group A] [Finite A] (J : Subgroup A)

theorem exists_fixed_lift {x : A} (hxN : x ∈ normalizer (J : Set A)) (hx2 : x * x = 1)
    (hZ : Odd (Nat.card (center ↥J))) (j : ↥J)
    (hj : actJ J ⟨x, hxN⟩ (QuotientGroup.mk j) = QuotientGroup.mk j) :
    ∃ c : ↥J, (QuotientGroup.mk c : ↥J ⧸ center ↥J) = QuotientGroup.mk j ∧
      x * (c : A) = (c : A) * x := by
  classical
  set n : ↥(normalizer (J : Set A)) := ⟨x, hxN⟩ with hn
  set f : ↥J → ↥J := fun c => J.normalizerMonoidHom n c with hf
  have hfc : ∀ c : ↥J, ((f c : ↥J) : A) = x * c * x⁻¹ := fun c => rfl
  have hff : ∀ c : ↥J, f (f c) = c := by
    intro c
    apply Subtype.ext
    rw [hfc, hfc]
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    rw [hxi, show x * (x * (c : A) * x) * x = (x * x) * c * (x * x) by group, hx2]
    group
  set S := {c : ↥J // (QuotientGroup.mk c : ↥J ⧸ center ↥J) = QuotientGroup.mk j} with hS
  have hfS : ∀ c : S, (QuotientGroup.mk (f c) : ↥J ⧸ center ↥J) = QuotientGroup.mk j := by
    intro c
    have h1 : (QuotientGroup.mk (f c.1) : ↥J ⧸ center ↥J) = actJ J n (QuotientGroup.mk c.1) :=
      rfl
    rw [h1, c.2, hj]
  set g : S → S := fun c => ⟨f c, hfS c⟩ with hg
  have hgg : Function.Involutive g := fun c => Subtype.ext (hff c)
  set σ : Equiv.Perm S := hgg.toPerm g with hσ
  have hσ2 : σ ^ 2 = 1 := by
    ext c
    simp [hσ, sq, hgg c]
  have hcard : Nat.card S = Nat.card (center ↥J) := by
    refine Nat.card_congr
      { toFun := fun c => ⟨j⁻¹ * c, ?_⟩
        invFun := fun z => ⟨j * z, ?_⟩
        left_inv := fun c => by simp
        right_inv := fun z => by simp }
    · have := c.2
      rw [QuotientGroup.eq] at this
      simpa using (center ↥J).inv_mem this
    · rw [QuotientGroup.eq]
      simp
  have : Fintype S := Fintype.ofFinite S
  have hsupp := Equiv.Perm.two_dvd_card_support hσ2
  have hne : σ.support ≠ Finset.univ := by
    intro hall
    rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at hsupp
    exact (Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hsupp)
  obtain ⟨c, hc⟩ : ∃ c, c ∉ σ.support := by
    by_contra hall
    push Not at hall
    exact hne (Finset.eq_univ_of_forall hall)
  rw [Equiv.Perm.notMem_support] at hc
  refine ⟨c.1, c.2, ?_⟩
  have h1 : ((f c.1 : ↥J) : A) = c.1 := congrArg (fun d : S => ((d.1 : ↥J) : A)) hc
  rw [hfc] at h1
  calc x * (c.1 : A) = x * c.1 * x⁻¹ * x := by group
    _ = c.1 * x := by rw [h1]

theorem fixedSubgroup_le_map {x : A} (hxN : x ∈ normalizer (J : Set A)) (hx2 : x * x = 1)
    (hZ : Odd (Nat.card (center ↥J))) :
    fixedSubgroup (↥J ⧸ center ↥J) (actJ J ⟨x, hxN⟩) ≤
      ((centralizer ({x} : Set A)).subgroupOf J).map (QuotientGroup.mk' (center ↥J)) := by
  intro y hy
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨c, hc, hcx⟩ := exists_fixed_lift J hxN hx2 hZ j hy
  refine ⟨c, ?_, hc⟩
  show (c : A) ∈ centralizer ({x} : Set A)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hcx.symm

theorem not_isSolvable_inf_centralizer {Y : Type*} [Group Y] (e : (↥J ⧸ center ↥J) ≃* Y)
    {x : A} (hxN : x ∈ normalizer (J : Set A)) (hx2 : x * x = 1)
    (hZ : Odd (Nat.card (center ↥J)))
    (hns : ¬ Group.IsSolvable ↥(fixedSubgroup Y (MulAut.congr e (actJ J ⟨x, hxN⟩)))) :
    ¬ Group.IsSolvable ↥(J ⊓ centralizer ({x} : Set A)) := by
  intro hsol
  apply hns
  set C := (centralizer ({x} : Set A)).subgroupOf J with hC
  have hCs : Group.IsSolvable ↥C := by
    let f : ↥C →* ↥(J ⊓ centralizer ({x} : Set A)) :=
      (J.subtype.comp C.subtype).codRestrict _ (fun c => ⟨c.1.2, c.2⟩)
    refine Group.isSolvable_of_isSolvable_injective (f := f) (fun a b hab => ?_)
    have h1 : ((f a : ↥(J ⊓ centralizer ({x} : Set A))) : A) = f b := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  have hmap : Group.IsSolvable ↥(C.map (QuotientGroup.mk' (center ↥J))) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (center ↥J)).subgroupMap_surjective C)
  have hfix : Group.IsSolvable ↥(fixedSubgroup (↥J ⧸ center ↥J) (actJ J ⟨x, hxN⟩)) :=
    Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (fixedSubgroup_le_map J hxN hx2 hZ))
  have heq : fixedSubgroup Y (MulAut.congr e (actJ J ⟨x, hxN⟩)) =
      (fixedSubgroup (↥J ⧸ center ↥J) (actJ J ⟨x, hxN⟩)).map e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map_equiv]
    show MulAut.congr e (actJ J ⟨x, hxN⟩) y = y ↔ actJ J ⟨x, hxN⟩ (e.symm y) = e.symm y
    have h0 : MulAut.congr e (actJ J ⟨x, hxN⟩) y = e (actJ J ⟨x, hxN⟩ (e.symm y)) := rfl
    rw [h0]
    constructor
    · intro h
      have := congrArg e.symm h
      rwa [MulEquiv.symm_apply_apply] at this
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
  rw [heq]
  exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)

end Fix

theorem actYHom_mem_innerPart {Γ : Type} [Group Γ] {K : Subgroup Γ} [K.Normal] {P' : Subgroup Γ}
    {γ : Γ} (hγ : γ ∈ normalizer (P' : Set Γ)) {y : ↥K ⧸ center ↥K}
    (hy : y ∈ innerPart (K := K) P') : actYHom (K := K) γ y ∈ innerPart (K := K) P' := by
  obtain ⟨x, hx, hxy⟩ := mem_innerPart.mp hy
  refine mem_innerPart.mpr ⟨γ * x * γ⁻¹, (mem_normalizer_iff.mp hγ x).mp hx, ?_⟩
  rw [map_mul, map_mul, map_inv, hxy, OFC.mul_conj_inv]

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S T Tstar : Subgroup G} {p : ℕ}
  {H P : Subgroup G} {g : G} {X Y : Subgroup G} {t : G} {q : ℕ} {I Q₁ : Subgroup G}

theorem exists_actUK (hL31 : Lemma31Narrow) (h : Cfg55E G z k S T Tstar p H P g X Y)
    (hd : Data5A2 z k S T Tstar p H P t q I Q₁) {J : Subgroup (HBar H)} (hJ : IsComponent J)
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) {Γ : Type} [Group Γ] {K : Subgroup Γ}
    [K.Normal] {a : Γ} {P' : Subgroup Γ} (hq : IsQuasisimple ↥K) (hL : LinkB H P g K a P' J) :
    ∃ (e : (↥J ⧸ center ↥J) ≃* (↥K ⧸ center ↥K))
      (ψ : ↥(L52Two.U4 z t) →* MulAut (↥K ⧸ center ↥K)), Function.Injective ψ ∧
      (∀ u, ∃ γ ∈ normalizer (P' : Set Γ), ψ u = actYHom (K := K) γ) ∧
      ∀ u : ↥(L52Two.U4 z t), ∃ hN : QuotientGroup.mk' (pPrimeCore 2 ↥H)
        ⟨(u : G), U_le_H h hd.u u.2⟩ ∈ normalizer (J : Set (HBar H)),
        ψ u = MulAut.congr e (actJ J ⟨_, hN⟩) := by
  obtain ⟨φ, hφ, hφa⟩ := exists_actU hL31 h hd hJ hIJ
  obtain ⟨e, he⟩ := LinkB.exists_equiv hq hL
  refine ⟨e, (MulAut.congr e).toMonoidHom.comp φ, (MulAut.congr e).injective.comp hφ,
    fun u => ?_, fun u => ?_⟩
  · obtain ⟨hN, hφu⟩ := hφa u
    obtain ⟨γ, hγP, -, hγ⟩ := he ⟨u, U_le_H h hd.u u.2⟩ hN
    refine ⟨γ, hγP (hd.u.U_le_T.trans (T_norm h) u.2), ?_⟩
    ext y
    show e (φ u (e.symm y)) = _
    rw [hφu, hγ, MulEquiv.apply_symm_apply]
  · obtain ⟨hN, hφu⟩ := hφa u
    exact ⟨hN, by rw [MonoidHom.comp_apply, hφu]; rfl⟩

omit [Finite G] in
theorem exists_zt_ne (hd : Data5A2 z k S T Tstar p H P t q I Q₁) (u₀ : G) :
    ∃ w : G, (w = z ∨ w = t) ∧ w ∈ L52Two.U4 z t ∧ w ≠ u₀ := by
  by_cases hz : u₀ = z
  · refine ⟨t, Or.inr rfl, Subgroup.mem_sup_right (Subgroup.mem_zpowers t), ?_⟩
    rw [hz]
    exact hd.u.udata.zt_ne.symm
  · exact ⟨z, Or.inl rfl, Subgroup.mem_sup_left (Subgroup.mem_zpowers z), fun h => hz h.symm⟩

omit [Finite G] in
theorem inf_centralizer_le {J : Subgroup (HBar H)}
    (hIJ : barIn H I ≤ centralizer (J : Set (HBar H))) {w : G} (hwH : w ∈ H) :
    J ⊓ centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hwH⟩} : Set (HBar H)) ≤
        centralizer (barIn H (zpowers w) : Set (HBar H)) ∧
      J ⊓ centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨w, hwH⟩} : Set (HBar H)) ≤
        centralizer (barIn H I : Set (HBar H)) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · rw [L52Two.barIn_zpowers_eq H hwH, Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, rfl⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.mp hv.2
    exact (Commute.zpow_left (show Commute _ v from hc.symm) n).eq
  · rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact ((Subgroup.mem_centralizer_iff.mp (hIJ hi)) v hv.1).symm

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.BT

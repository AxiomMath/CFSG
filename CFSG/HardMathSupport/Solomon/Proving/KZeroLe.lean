module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

section Elements

variable {G : Type} [Group G]

theorem conj_cent_singleton {x k s : G} (hxs : x * s = s * x) (hks : k * s = s * k) :
    (x * k * x⁻¹) * s = s * (x * k * x⁻¹) := by
  have hxs' : x⁻¹ * s = s * x⁻¹ := (Commute.inv_left (show Commute x s from hxs)).eq
  have e1 : (x * k * x⁻¹) * s = x * (k * s) * x⁻¹ := by
    calc (x * k * x⁻¹) * s = x * k * (x⁻¹ * s) := by rw [mul_assoc]
      _ = x * k * (s * x⁻¹) := by rw [hxs']
      _ = x * (k * s) * x⁻¹ := by simp only [mul_assoc]
  have e2 : s * (x * k * x⁻¹) = x * (s * k) * x⁻¹ := by
    calc s * (x * k * x⁻¹) = (s * x) * k * x⁻¹ := by simp only [mul_assoc]
      _ = (x * s) * k * x⁻¹ := by rw [← hxs]
      _ = x * (s * k) * x⁻¹ := by simp only [mul_assoc]
  rw [e1, e2, hks]

end Elements

section Helpers

variable {G : Type} [Group G]

theorem subsingleton_of_isPerfect_isPGroup {p : ℕ} [Fact p.Prime] {H : Type} [Group H] [Finite H]
    [Group.IsPerfect H] (hH : IsPGroup p H) : Subsingleton H := by
  by_contra hns
  have : Nontrivial H := not_subsingleton_iff_nontrivial.1 hns
  exact Group.IsPerfect.not_isNilpotent H hH.isNilpotent

theorem glaPComponent_le_of_normal_sup_pGroup [Finite G] {p : ℕ} (hp : p.Prime)
    {X Y A : Subgroup G} (hYX : Y ≤ X) (hn : (Y.subgroupOf X).Normal) (hAX : A ≤ X)
    (hA : IsPGroup p ↥A) (hXYA : X ≤ Y ⊔ A) {J : Subgroup G} (hJ : GLAPComponent p X J) :
    J ≤ Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hJX : J ≤ X := hJ.1
  have : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hJ)
  have hPp : IsPGroup p ↥(A.subgroupOf X) := hA.comap_of_injective X.subtype X.subtype_injective
  have hsup : Y.subgroupOf X ⊔ A.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hYX hAX]
    exact Subgroup.subgroupOf_eq_top.2 hXYA
  have hQ : IsPGroup p (↥X ⧸ Y.subgroupOf X) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have hx : x ∈ Y.subgroupOf X ⊔ A.subgroupOf X := hsup ▸ Subgroup.mem_top x
    obtain ⟨t, ht, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hx
    obtain ⟨m, hm⟩ := hPp ⟨k, hk⟩
    refine ⟨m, ?_⟩
    have hkm : k ^ (p ^ m) = 1 := by
      have h := congrArg (fun z : ↥(A.subgroupOf X) => (z : ↥X)) hm
      simpa using h
    have e : (QuotientGroup.mk (t * k) : ↥X ⧸ Y.subgroupOf X) = QuotientGroup.mk k := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff t).2 ht, one_mul]
    rw [e, ← QuotientGroup.mk_pow, hkm]
    rfl
  let f : ↥J →* ↥X ⧸ Y.subgroupOf X :=
    (QuotientGroup.mk' (Y.subgroupOf X)).comp (Subgroup.inclusion hJX)
  have : Group.IsPerfect ↥f.range :=
    Group.IsPerfect.ofSurjective (f := f.rangeRestrict) (MonoidHom.rangeRestrict_surjective f)
  have hR : IsPGroup p ↥f.range := by
    rintro ⟨z, hz⟩
    obtain ⟨j, rfl⟩ := MonoidHom.mem_range.1 hz
    obtain ⟨m, hm⟩ := hQ (f j)
    exact ⟨m, Subtype.ext (by simpa using hm)⟩
  have : Subsingleton ↥f.range := subsingleton_of_isPerfect_isPGroup hR
  intro j hj
  have h1 : f ⟨j, hj⟩ = 1 := by
    have := Subsingleton.elim (⟨f ⟨j, hj⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ↥f.range) 1
    exact congrArg Subtype.val this
  have h2 : ((⟨j, hJX hj⟩ : ↥X) : ↥X ⧸ Y.subgroupOf X) = 1 := h1
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)

theorem glaPLayer_le_of_normal_sup_pGroup [Finite G] {p : ℕ} (hp : p.Prime)
    {X Y A : Subgroup G} (hYX : Y ≤ X) (hn : (Y.subgroupOf X).Normal) (hAX : A ≤ X)
    (hA : IsPGroup p ↥A) (hXYA : X ≤ Y ⊔ A) : GLAPLayer p X ≤ GLAPLayer p Y := by
  unfold GLAPLayer
  refine sSup_le fun J hJ => le_sSup ?_
  exact glaPComponent_of_le hp hJ
    (glaPComponent_le_of_normal_sup_pGroup hp hYX hn hAX hA hXYA hJ) hYX

theorem glaPLayer_le_of_normal_le [Finite G] {p : ℕ} (hp : p.Prime) {Y M : Subgroup G}
    (hYM : Y ≤ M) (hn : (Y.subgroupOf M).Normal) : GLAPLayer p Y ≤ GLAPLayer p M := by
  unfold GLAPLayer
  refine sSup_le fun J hJ => le_sSup ?_
  exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns.glaPComponent_of_normal_sub
    hp hYM hn hJ

end Helpers

theorem kZeroOf_le_layer_inf_centralizer
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    {G : Type} [Group G] [Finite G] {K A : Subgroup G} {a : G}
    (hKA : CFSG.Open.IsKGroup ↥((K ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ A))
    (hA : IsPGroup 3 ↥A) (haA : a ∈ A) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAa : A ≤ Subgroup.centralizer ({a} : Set G)) :
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set G)) ≤
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  set Y : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hYdef
  set X : Subgroup G := Y ⊔ A with hXdef
  have hYK : Y ≤ K := inf_le_left
  have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) := inf_le_right
  have hYX : Y ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hAN' := Subgroup.le_normalizer_iff.1 hAN
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff.2 fun h hh k hk =>
      K.mul_mem (K.mul_mem (hYK hh) hk) (K.inv_mem (hYK hh))
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := sup_le hYN hAN
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    refine Subgroup.le_normalizer_iff.2 fun h hh k hk => ?_
    have hkK : k ∈ K := (Subgroup.mem_inf.1 hk).1
    have hkC : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 (hYa hk)
    have hhC : h * a = a * h := Subgroup.mem_centralizer_singleton_iff.1 (hAa hh)
    exact Subgroup.mem_inf.2 ⟨hAN' h hh k hkK,
      Subgroup.mem_centralizer_singleton_iff.2 (conj_cent_singleton hhC hkC)⟩
  have hYY : Y ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.le_normalizer_iff.2 fun h hh k hk => Y.mul_mem (Y.mul_mem hh hk) (Y.inv_mem hh)
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := sup_le hYY hAY
  have hn : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY
  have step2 : GLAPLayer 3 (X ⊓ Subgroup.centralizer (A : Set G)) ≤ GLAPLayer 3 X :=
    i183_glaPLayer_inf_centralizer_le hS hKA Nat.prime_three hAX hA
  have step3 : GLAPLayer 3 X ≤ GLAPLayer 3 Y :=
    glaPLayer_le_of_normal_sup_pGroup Nat.prime_three hYX hn hAX hA le_rfl
  have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 hk) a haA).symm
  have hKCA_le_X : K ⊓ Subgroup.centralizer (A : Set G) ≤ X := fun k hk =>
    hYX (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hk).1, hCA (Subgroup.mem_inf.1 hk).2⟩)
  have hYM : K ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf hKCA_le_X inf_le_right
  have hX'N : X ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.2 fun x hx k hk => ?_
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer_iff.1 hXN x hxX k hkK, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    have hxs : x * s = s * x := ((Subgroup.mem_centralizer_iff.1 hxC) s hs).symm
    have hks : k * s = s * k := ((Subgroup.mem_centralizer_iff.1 hkC) s hs).symm
    exact (conj_cent_singleton hxs hks).symm
  have hn' : ((K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
      (X ⊓ Subgroup.centralizer (A : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 hX'N
  have step4 : GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set G)) ≤
      GLAPLayer 3 (X ⊓ Subgroup.centralizer (A : Set G)) :=
    glaPLayer_le_of_normal_le Nat.prime_three hYM hn'
  exact step4.trans (step2.trans step3)

end CFSG.HardMathSupport.Solomon.Proving

end

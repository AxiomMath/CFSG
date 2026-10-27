module

public import CFSG.ClassicalInvolution.Q3.TL4C264OmL
public import CFSG.ClassicalInvolution.Q3.TL4E3Fin
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint
open scoped commutatorElement

namespace C264Om

variable {L X F : Type} [Group L] [Group X] [Group F]

theorem exists_surj_range_of_odd_ker [Finite L] (φ : L →* X) (θ : L →* F)
    (hθ : Function.Surjective θ) [IsSimpleGroup F] (h2 : Even (Nat.card F))
    (hodd : Odd (Nat.card φ.ker)) : ∃ ψ : ↥φ.range →* F, Function.Surjective ψ := by
  have hn : (φ.ker.map θ).Normal := (MonoidHom.normal_ker φ).map θ hθ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map θ) with hb | ht
  · have hle : φ.ker ≤ θ.ker := fun l hl => by
      have h1 : θ l ∈ φ.ker.map θ := Subgroup.mem_map_of_mem θ hl
      rw [hb, Subgroup.mem_bot] at h1
      exact h1
    refine ⟨(QuotientGroup.lift φ.ker θ hle).comp
      (QuotientGroup.quotientKerEquivRange φ).symm.toMonoidHom, fun y => ?_⟩
    obtain ⟨l, rfl⟩ := hθ y
    refine ⟨φ.rangeRestrict l, ?_⟩
    have e : (QuotientGroup.quotientKerEquivRange φ).symm (φ.rangeRestrict l) =
        (l : L ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e, QuotientGroup.lift_mk]
  · exfalso
    have hd := Subgroup.card_map_dvd φ.ker θ
    rw [ht, Subgroup.card_top] at hd
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hodd hd)) h2

theorem range_eq_top_of_card_le [Finite X] (φ : L →* X) (ψ : ↥φ.range →* F)
    (hψ : Function.Surjective ψ) (hcard : Nat.card X ≤ Nat.card F) : φ.range = ⊤ := by
  have h1 : Nat.card F ≤ Nat.card ↥φ.range := Nat.card_le_card_of_surjective ψ hψ
  exact Subgroup.eq_top_of_card_eq _
    (le_antisymm (Subgroup.card_le_card_group _) (hcard.trans h1))

theorem false_of_abelian3 [Finite X] {H : Subgroup X} (ψ : ↥H →* F)
    (hψ : Function.Surjective ψ)
    (hab : ∀ P : Subgroup X, IsPGroup 3 ↥P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hnab : ∃ P : Subgroup F, IsPGroup 3 ↥P ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP, a, ha, b, hb, hab'⟩ := hnab
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hψ 3 Q
  have hSQ : (S : Subgroup ↥H).map ψ = (Q : Subgroup F) := by
    rw [← hS, Sylow.coe_mapSurjective]
  have haQ : a ∈ (S : Subgroup ↥H).map ψ := hSQ ▸ hPQ ha
  have hbQ : b ∈ (S : Subgroup ↥H).map ψ := hSQ ▸ hPQ hb
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp haQ
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hbQ
  apply hab'
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hab ((S : Subgroup ↥H).map H.subtype) (S.isPGroup'.map _) _ ⟨u, hu, rfl⟩ _
    ⟨v, hv, rfl⟩)

end C264Om

theorem abelian3_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ P : Subgroup A, IsPGroup 3 ↥P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∀ P : Subgroup B, IsPGroup 3 ↥P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  intro P hP a ha b hb
  have h1 := h (P.map e.symm.toMonoidHom) (hP.map _) (e.symm a) ⟨a, ha, rfl⟩ (e.symm b)
    ⟨b, hb, rfl⟩
  apply e.symm.injective
  rw [map_mul, map_mul]
  exact h1

theorem isSimpleGroup_of_lieModel_psl33 {X : Type} [Group X] (h : LieModel X .PSL 3 3 1) :
    IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

section Cover

variable {G : Type} [Group G]

theorem comm_mem_oddCoreOf_of_cover {X L : Subgroup G} {a : G} (haN : conjSub a X = X)
    (hLa : L ≤ Subgroup.centralizer ({a} : Set G)) (hLX : L ≤ X)
    (hcov : ∀ y ∈ X, ∃ l ∈ L, l⁻¹ * y ∈ oddCoreOf X) : ∀ y ∈ X, ⁅a, y⁆ ∈ oddCoreOf X := by
  intro y hy
  obtain ⟨l, hl, ho⟩ := hcov y hy
  have hal : l * a = a * l := Subgroup.mem_centralizer_singleton_iff.mp (hLa hl)
  have h1 : a * (l⁻¹ * y) * a⁻¹ ∈ oddCoreOf X := by
    have h0 : a * (l⁻¹ * y) * a⁻¹ ∈ conjSub a (oddCoreOf X) := by
      rw [mem_conjSub_iff]
      have e : a⁻¹ * (a * (l⁻¹ * y) * a⁻¹) * a = l⁻¹ * y := by group
      rw [e]
      exact ho
    rwa [← Thompson.oddCoreOf_conjSub_eq, haN] at h0
  have h2 : a * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹ ∈ oddCoreOf X :=
    (oddCoreOf X).mul_mem h1 ((oddCoreOf X).inv_mem ho)
  have h3 : l * (a * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹) * l⁻¹ ∈ oddCoreOf X := by
    have h0 : l * (a * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹) * l⁻¹ ∈
        conjSub l (oddCoreOf X) := by
      rw [mem_conjSub_iff]
      have e : l⁻¹ * (l * (a * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹) * l⁻¹) * l =
          a * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹ := by group
      rw [e]
      exact h2
    rwa [← Thompson.oddCoreOf_conjSub_eq, conjSub_eq_self_of_mem (hLX hl)] at h0
  have e : ⁅a, y⁆ = l * (a * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹) * l⁻¹ := by
    rw [commutatorElement_def]
    calc a * y * a⁻¹ * y⁻¹ = (a * l) * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹ * l⁻¹ := by group
      _ = (l * a) * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹ * l⁻¹ := by rw [hal]
      _ = l * (a * (l⁻¹ * y) * a⁻¹ * (l⁻¹ * y)⁻¹) * l⁻¹ := by group
  rw [e]
  exact h3

theorem cover_of_range_eq_top {X L : Subgroup G} (hLX : L ≤ X)
    (htop : ((QuotientGroup.mk' (classicalInvolutionOddCore ↥X)).comp
      (Subgroup.inclusion hLX)).range = ⊤) :
    ∀ y ∈ X, ∃ l ∈ L, l⁻¹ * y ∈ oddCoreOf X := by
  intro y hy
  have hm : QuotientGroup.mk' (classicalInvolutionOddCore ↥X) ⟨y, hy⟩ ∈
      ((QuotientGroup.mk' (classicalInvolutionOddCore ↥X)).comp
        (Subgroup.inclusion hLX)).range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨l, hl⟩ := hm
  refine ⟨l, l.2, ?_⟩
  have h1 := QuotientGroup.eq.mp hl
  exact mem_oddCoreOf_iff.mpr ⟨X.mul_mem (X.inv_mem (hLX l.2)) hy, by
    convert h1 using 1
    exact Subtype.ext rfl⟩

end Cover

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem exists_c264Two_ii (h : TypeRFam 3 Ω) {K : Subgroup G} (hKx : XMem Ω x K) {z : G}
    (hz : IsUniqueInvolution K z) {t s : G} (hs : s ∈ Subgroup.centralizer ({x} : Set G))
    (hs2 : s * s = 1) {g : G} (hgX : g ∈ omegaNbrGen Ω K) (hgt : g⁻¹ * t * g = s)
    {J₁ : Subgroup G} (hJ₁ : J₁ ∈ CoreAssembly.conjClass K) (hJ₁s : IsUniqueInvolution J₁ s)
    (hout : ¬ ∃ w : SecQuot Ω x, ∀ v, secAct h.hyp.conjInvariant hs v = w * v * w⁻¹)
    (N : Subgroup (SecQuot Ω x)) [N.Normal]
    (hF : LieModel ↥((sigmaFixGen (secImg Ω x K) (secAct h.hyp.conjInvariant hs)).map
      ((QuotientGroup.mk' (Subgroup.center (SecQuot Ω x ⧸ N))).comp
        (QuotientGroup.mk' N))) .PSL 3 3 1)
    (hnab : ∃ P : Subgroup ↥((sigmaFixGen (secImg Ω x K) (secAct h.hyp.conjInvariant hs)).map
      ((QuotientGroup.mk' (Subgroup.center (SecQuot Ω x ⧸ N))).comp (QuotientGroup.mk' N))),
      IsPGroup 3 ↥P ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (h263 : LieModel (XQuot Ω K) .PSL 3 3 1 ∨
      ∀ P : Subgroup (XQuot Ω K), IsPGroup 3 ↥P → ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) :
    ∃ hc : G, (∃ y ∈ omegaNbrGen Ω K, y * t * y⁻¹ = hc * z * hc⁻¹) ∧
      (∀ y ∈ conjSub hc (omegaNbrGen Ω K), ⁅x, y⁆ ∈ oddCoreOf (conjSub hc (omegaNbrGen Ω K))) ∧
      LieModel (↥(conjSub hc (omegaNbrGen Ω K)) ⧸
        classicalInvolutionOddCore ↥(conjSub hc (omegaNbrGen Ω K))) .PSL 3 3 1 := by
  classical
  have hcl : ConjInvariant Ω := h.hyp.conjInvariant
  obtain ⟨hc, hhc'⟩ := hJ₁
  have hhc : conjSub hc K = J₁ := hhc'
  have hJ₁Ω : J₁ ∈ Ω := hhc ▸ hcl hc K hKx.1
  have hzs : hc * z * hc⁻¹ = s := by
    have h1 := hz.conj hc
    rw [hhc] at h1
    exact h1.eq hJ₁s
  have hXh : conjSub hc (omegaNbrGen Ω K) = omegaNbrGen Ω J₁ := by
    rw [← hhc, omegaNbrGen_conjSub_gen hcl]
  have hnX := not_xMem_of_not_inner h hs hJ₁s hout
  obtain ⟨L, hLX1, hLx, hLY, hLmap⟩ :=
    exists_fixGen_lift h hs hs2 hJ₁Ω hJ₁s hnX (secImg_mem hKx)
  have hLXh : L ≤ conjSub hc (omegaNbrGen Ω K) := hXh ▸ hLX1
  have hxN : conjSub x (conjSub hc (omegaNbrGen Ω K)) = conjSub hc (omegaNbrGen Ω K) := by
    have hsx : x ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hs).symm
    have hxJ : conjSub x J₁ = J₁ := mem_normalizer_iff_conjSub_eq.mp (h.tight J₁ hJ₁Ω s hJ₁s hsx)
    rw [hXh]
    exact conjSub_omegaNbrGen_of_conjSub_eq hcl hxJ
  set Xh := conjSub hc (omegaNbrGen Ω K) with hXhdef
  set φ : ↥L →* ↥Xh ⧸ classicalInvolutionOddCore ↥Xh :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥Xh)).comp (Subgroup.inclusion hLXh) with hφ
  set Fb := (sigmaFixGen (secImg Ω x K) (secAct h.hyp.conjInvariant hs)).map
    ((QuotientGroup.mk' (Subgroup.center (SecQuot Ω x ⧸ N))).comp (QuotientGroup.mk' N)) with hFb
  set θ₀ : ↥L →* (SecQuot Ω x ⧸ N) ⧸ Subgroup.center (SecQuot Ω x ⧸ N) :=
    (((QuotientGroup.mk' (Subgroup.center (SecQuot Ω x ⧸ N))).comp (QuotientGroup.mk' N)).comp
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(layerY Ω x)))).comp
      (Subgroup.inclusion hLY) with hθ₀
  have hrange : θ₀.range = Fb := by
    rw [hθ₀, MonoidHom.range_comp, Subgroup.inclusion_range, ← Subgroup.map_map, hLmap]
  set θ : ↥L →* ↥Fb := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp θ₀.rangeRestrict with hθ
  have hθs : Function.Surjective θ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp θ₀.rangeRestrict_surjective
  have : IsSimpleGroup ↥Fb := isSimpleGroup_of_lieModel_psl33 hF
  have hFc : Nat.card ↥Fb = 5616 := card_of_lieModel_psl_three_three_one hF
  have hodd : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map (Subgroup.inclusion hLXh) ≤ classicalInvolutionOddCore ↥Xh := by
      rintro _ ⟨l, hl, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hl)
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hLXh)] at h1
    exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card _) h1
  obtain ⟨ψ, hψ⟩ := C264Om.exists_surj_range_of_odd_ker φ θ hθs (by rw [hFc]; decide) hodd
  let eh : ↥(omegaNbrGen Ω K) ≃* ↥Xh :=
    Subgroup.equivMapOfInjective _ (MulAut.conj hc).toMonoidHom (MulAut.conj hc).injective
  let ehb : XQuot Ω K ≃* (↥Xh ⧸ classicalInvolutionOddCore ↥Xh) :=
    QuotientGroup.congr _ _ eh (CFSG.ComponentClassification.OddCore.equiv_invariant eh)
  have hL33 : LieModel (↥Xh ⧸ classicalInvolutionOddCore ↥Xh) .PSL 3 3 1 := by
    rcases h263 with h3 | hab
    · exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv ehb h3
    · exact (C264Om.false_of_abelian3 ψ hψ (abelian3_of_mulEquiv ehb hab) hnab).elim
  have htop : φ.range = ⊤ := C264Om.range_eq_top_of_card_le φ ψ hψ
    (by rw [card_of_lieModel_psl_three_three_one hL33, hFc])
  refine ⟨hc, ⟨g⁻¹, (omegaNbrGen Ω K).inv_mem hgX, ?_⟩, ?_, hL33⟩
  · rw [hzs, ← hgt, inv_inv]
  · exact comm_mem_oddCoreOf_of_cover hxN hLx hLXh (cover_of_range_eq_top hLXh htop)

end Main

end CFSG.ClassicalInvolution.Q3.TL4

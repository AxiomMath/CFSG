module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUOut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMK4
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RMY
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUG3
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Sporadic.SmallOddCore CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.ComponentClassification.FooteLit

abbrev Kst {G : Type*} [Group G] (β : G) : Subgroup G :=
  normalizer ((zpowers β : Subgroup G) : Set G)

section KEmb


structure KEmb (G : Type) [Group G] (β : G) where
  θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃* ↥U43Ext
  f : G → Equiv.Perm (Fin 820)
  mul : ∀ x ∈ Kst β, ∀ y ∈ Kst β, f (x * y) = f x * f y
  mem : ∀ y ∈ Kst β, f y ∈ U16.U43ExtStar
  ker : ∀ y ∈ Kst β, f y = 1 ↔ y ∈ OG β
  inner : ∀ y ∈ Kst β, y ∈ centralizer ({β} : Set G) ↔ f y ∈ U43Ext
  surj : ∀ b ∈ U43Ext, ∃ y ∈ centralizer ({β} : Set G), f y = b
  inner_val : ∀ (y : G) (hy : y ∈ centralizer ({β} : Set G)),
    f y = ((θ (QuotientGroup.mk (⟨y, hy⟩ : ↥(centralizer ({β} : Set G)))) : ↥U43Ext) :
      Equiv.Perm (Fin 820))

namespace KEmb

variable {G : Type} [Group G] {β : G} (E : KEmb G β)

theorem one : E.f 1 = 1 := by
  have h := E.mul 1 (Kst β).one_mem 1 (Kst β).one_mem
  rw [mul_one] at h
  have h2 : E.f 1 * E.f 1 = E.f 1 * 1 := by rw [mul_one]; exact h.symm
  exact mul_left_cancel h2

theorem inv {x : G} (hx : x ∈ Kst β) : E.f x⁻¹ = (E.f x)⁻¹ := by
  have h := E.mul x hx x⁻¹ ((Kst β).inv_mem hx)
  rw [mul_inv_cancel, E.one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem conj {x k : G} (hx : x ∈ Kst β) (hk : k ∈ Kst β) :
    E.f (k * x * k⁻¹) = E.f k * E.f x * (E.f k)⁻¹ := by
  rw [E.mul _ ((Kst β).mul_mem hk hx) _ ((Kst β).inv_mem hk), E.mul _ hk _ hx, E.inv hk]

end KEmb

section Construction

variable {G : Type} [Group G] [Finite G] {β : G}

theorem mem_OG_iff_aux {a : G} (ha : a ∈ centralizer ({β} : Set G)) :
    a ∈ OG β ↔ (⟨a, ha⟩ : ↥(centralizer ({β} : Set G))) ∈
      fusionOddCore ↥(centralizer ({β} : Set G)) := by
  constructor
  · rintro ⟨o, ho, rfl⟩
    exact ho
  · intro h
    exact ⟨⟨a, ha⟩, h, rfl⟩

theorem cent_le_Kst (β : G) : centralizer ({β} : Set G) ≤ Kst β := fun k hk =>
  mem_normalizer_zpowers_of_conj (Or.inl (by
    have := mem_centralizer_singleton_iff.1 hk
    calc k * β * k⁻¹ = β * k * k⁻¹ := by rw [this]
      _ = β := by group))

theorem Kst_le_normK (hβ3 : orderOf β = 3) :
    Kst β ≤ normalizer ((centralizer ({β} : Set G) : Subgroup G) : Set G) := by
  intro y hy
  by_cases hyK : y ∈ centralizer ({β} : Set G)
  · exact normalizer_cent_of_conj (Or.inl (by
      have := mem_centralizer_singleton_iff.1 hyK
      calc y * β * y⁻¹ = β * y * y⁻¹ := by rw [this]
        _ = β := by group))
  · exact normalizer_cent_of_conj (Or.inr (inv_of_mem_normalizer_zpowers hβ3 hy hyK))

@[expose] noncomputable def cK (hβ3 : orderOf β = 3) :
    ↥(Kst β) →* MulAut ↥(centralizer ({β} : Set G)) :=
  (centralizer ({β} : Set G)).normalizerMonoidHom.comp (Subgroup.inclusion (Kst_le_normK hβ3))

theorem cK_apply (hβ3 : orderOf β = 3) (y : ↥(Kst β)) (k : ↥(centralizer ({β} : Set G))) :
    ((cK hβ3 y k : ↥(centralizer ({β} : Set G))) : G) = (y : G) * k * (y : G)⁻¹ := by
  simp [cK]

theorem cK_conj (hβ3 : orderOf β = 3) {y : G} (hy : y ∈ centralizer ({β} : Set G)) :
    cK hβ3 ⟨y, cent_le_Kst β hy⟩ = MulAut.conj (⟨y, hy⟩ : ↥(centralizer ({β} : Set G))) := by
  ext k
  rw [cK_apply]
  rfl

theorem oddAut_conj {Y : Type*} [Group Y] (c : Y) :
    oddAut Y (MulAut.conj c) = MulAut.conj (QuotientGroup.mk c) := by
  ext s
  induction s using QuotientGroup.induction_on
  simp [MulAut.conj_apply]

theorem hom_conj {q : Equiv.Perm (Fin 820)} (hq : q ∈ U43Ext) :
    U16.autModel_U43Ext.hom (MulAut.conj (⟨q, hq⟩ : ↥U43Ext)) = q :=
  U16.autModel_U43Ext.elt_eq (U16.U43Ext_le_U43ExtStar hq) (fun p => by
    simp [MulAut.conj_apply])

@[expose] noncomputable def psiHom (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) : ↥(Kst β) →* Equiv.Perm (Fin 820) :=
  U16.autModel_U43Ext.hom.comp ((MulAut.congr θ).toMonoidHom.comp
    ((oddAut ↥(centralizer ({β} : Set G))).comp (cK hβ3)))

theorem psiHom_inner (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) {y : G} (hy : y ∈ centralizer ({β} : Set G)) :
    psiHom hβ3 θ ⟨y, cent_le_Kst β hy⟩ =
      ((θ (QuotientGroup.mk (⟨y, hy⟩ : ↥(centralizer ({β} : Set G)))) : ↥U43Ext) :
        Equiv.Perm (Fin 820)) := by
  have h1 : psiHom hβ3 θ ⟨y, cent_le_Kst β hy⟩ = U16.autModel_U43Ext.hom
      (MulAut.congr θ (oddAut ↥(centralizer ({β} : Set G)) (cK hβ3 ⟨y, cent_le_Kst β hy⟩))) := rfl
  rw [h1, cK_conj hβ3 hy, oddAut_conj]
  have h2 : MulAut.congr θ (MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥(centralizer ({β} : Set G))))) =
      MulAut.conj (θ (QuotientGroup.mk (⟨y, hy⟩ : ↥(centralizer ({β} : Set G))))) := by
    ext p
    simp [MulAut.congr_apply, MulAut.conj_apply]
  rw [h2]
  exact hom_conj (θ (QuotientGroup.mk (⟨y, hy⟩ : ↥(centralizer ({β} : Set G))))).2

theorem psiHom_mem (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) (y : ↥(Kst β)) : psiHom hβ3 θ y ∈ U16.U43ExtStar :=
  U16.autModel_U43Ext.elt_mem _

theorem psiHom_ker (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext)
    (hker : ∀ y ∈ Kst β, (∀ k ∈ centralizer ({β} : Set G), y * k * y⁻¹ * k⁻¹ ∈ OG β) →
      y ∈ OG β) (y : G) (hy : y ∈ Kst β) : psiHom hβ3 θ ⟨y, hy⟩ = 1 ↔ y ∈ OG β := by
  constructor
  · intro h1
    apply hker y hy
    intro k hk
    have h2 : U16.autModel_U43Ext.hom (MulAut.congr θ (oddAut ↥(centralizer ({β} : Set G))
        (cK hβ3 ⟨y, hy⟩))) = U16.autModel_U43Ext.hom 1 := by
      rw [map_one]
      exact h1
    have h3 := U16.autModel_U43Ext.hom_injective h2
    have h4 : oddAut ↥(centralizer ({β} : Set G)) (cK hβ3 ⟨y, hy⟩) = 1 :=
      (MulAut.congr θ).injective (by rw [h3, map_one])
    have h5 := congrArg (fun σ : MulAut (↥(centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(centralizer ({β} : Set G))) => σ (QuotientGroup.mk ⟨k, hk⟩)) h4
    simp only [oddAut_mk, MulAut.one_apply] at h5
    have hyk : y * k * y⁻¹ ∈ centralizer ({β} : Set G) := by
      have := ((cK hβ3 ⟨y, hy⟩) ⟨k, hk⟩).2
      simpa [cK_apply] using this
    have e0 : (cK hβ3 ⟨y, hy⟩ ⟨k, hk⟩ : ↥(centralizer ({β} : Set G))) = ⟨y * k * y⁻¹, hyk⟩ :=
      Subtype.ext (cK_apply hβ3 _ _)
    rw [e0] at h5
    have h6 : (QuotientGroup.mk (⟨y * k * y⁻¹ * k⁻¹, mul_mem hyk (inv_mem hk)⟩ :
        ↥(centralizer ({β} : Set G))) : ↥(centralizer ({β} : Set G)) ⧸
          fusionOddCore ↥(centralizer ({β} : Set G))) = 1 := by
      have e : (⟨y * k * y⁻¹ * k⁻¹, mul_mem hyk (inv_mem hk)⟩ : ↥(centralizer ({β} : Set G))) =
          ⟨y * k * y⁻¹, hyk⟩ * (⟨k, hk⟩ : ↥(centralizer ({β} : Set G)))⁻¹ := rfl
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h5]
      group
    exact (mem_OG_iff_aux (mul_mem hyk (inv_mem hk))).2 ((QuotientGroup.eq_one_iff _).1 h6)
  · intro hyO
    have hyK : y ∈ centralizer ({β} : Set G) := OG_le_cent β hyO
    have e : (⟨y, hy⟩ : ↥(Kst β)) = ⟨y, cent_le_Kst β hyK⟩ := rfl
    rw [e, psiHom_inner hβ3 θ hyK]
    have h1 : (QuotientGroup.mk (⟨y, hyK⟩ : ↥(centralizer ({β} : Set G))) :
        ↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ((mem_OG_iff_aux hyK).1 hyO)
    rw [h1, map_one]
    rfl

theorem psiHom_inner_iff (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext)
    (hker : ∀ y ∈ Kst β, (∀ k ∈ centralizer ({β} : Set G), y * k * y⁻¹ * k⁻¹ ∈ OG β) →
      y ∈ OG β) (y : G) (hy : y ∈ Kst β) :
    y ∈ centralizer ({β} : Set G) ↔ psiHom hβ3 θ ⟨y, hy⟩ ∈ U43Ext := by
  constructor
  · intro hyK
    have e : (⟨y, hy⟩ : ↥(Kst β)) = ⟨y, cent_le_Kst β hyK⟩ := rfl
    rw [e, psiHom_inner hβ3 θ hyK]
    exact (θ _).2
  · intro hb
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (θ.symm ⟨psiHom hβ3 θ ⟨y, hy⟩, hb⟩)
    have hkv : psiHom hβ3 θ ⟨(k : G), cent_le_Kst β k.2⟩ = psiHom hβ3 θ ⟨y, hy⟩ := by
      rw [psiHom_inner hβ3 θ k.2]
      have e : (⟨(k : G), k.2⟩ : ↥(centralizer ({β} : Set G))) = k := rfl
      rw [e, hk]
      simp
    have h1 : psiHom hβ3 θ (⟨y, hy⟩ * ⟨(k : G), cent_le_Kst β k.2⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hkv, mul_inv_cancel]
    have h2 := (psiHom_ker hβ3 θ hker (y * (k : G)⁻¹)
      ((Kst β).mul_mem hy ((Kst β).inv_mem (cent_le_Kst β k.2)))).1 h1
    have h3 : y * (k : G)⁻¹ ∈ centralizer ({β} : Set G) := OG_le_cent β h2
    have := mul_mem h3 k.2
    simpa using this

theorem psiHom_surj (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) (b : Equiv.Perm (Fin 820)) (hb : b ∈ U43Ext) :
    ∃ y, ∃ hy : y ∈ centralizer ({β} : Set G),
      psiHom hβ3 θ ⟨y, cent_le_Kst β hy⟩ = b := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (θ.symm ⟨b, hb⟩)
  refine ⟨(k : G), k.2, ?_⟩
  rw [psiHom_inner hβ3 θ k.2]
  have e : (⟨(k : G), k.2⟩ : ↥(centralizer ({β} : Set G))) = k := rfl
  rw [e, hk]
  simp

@[expose] noncomputable def fOf (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) (g : G) : Equiv.Perm (Fin 820) :=
  open Classical in if hg : g ∈ Kst β then psiHom hβ3 θ ⟨g, hg⟩ else 1

theorem fOf_eq (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) {g : G} (hg : g ∈ Kst β) : fOf hβ3 θ g = psiHom hβ3 θ ⟨g, hg⟩ := by
  unfold fOf
  exact dif_pos hg

theorem fOf_mul (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext) {x y : G} (hx : x ∈ Kst β) (hy : y ∈ Kst β) :
    fOf hβ3 θ (x * y) = fOf hβ3 θ x * fOf hβ3 θ y := by
  have e : (⟨x * y, (Kst β).mul_mem hx hy⟩ : ↥(Kst β)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [fOf_eq hβ3 θ ((Kst β).mul_mem hx hy), fOf_eq hβ3 θ hx, fOf_eq hβ3 θ hy, e, map_mul]

theorem exists_kemb (hβ3 : orderOf β = 3)
    (θ : (↥(centralizer ({β} : Set G)) ⧸ fusionOddCore ↥(centralizer ({β} : Set G))) ≃*
      ↥U43Ext)
    (hker : ∀ y ∈ Kst β, (∀ k ∈ centralizer ({β} : Set G), y * k * y⁻¹ * k⁻¹ ∈ OG β) →
      y ∈ OG β) : Nonempty (KEmb G β) :=
  ⟨{ θ := θ
     f := fOf hβ3 θ
     mul := fun x hx y hy => fOf_mul hβ3 θ hx hy
     mem := fun y hy => by rw [fOf_eq hβ3 θ hy]; exact psiHom_mem hβ3 θ ⟨y, hy⟩
     ker := fun y hy => by rw [fOf_eq hβ3 θ hy]; exact psiHom_ker hβ3 θ hker y hy
     inner := fun y hy => by rw [fOf_eq hβ3 θ hy]; exact psiHom_inner_iff hβ3 θ hker y hy
     surj := fun b hb => by
       obtain ⟨y, hy, h⟩ := psiHom_surj hβ3 θ b hb
       exact ⟨y, hy, by rw [fOf_eq hβ3 θ (cent_le_Kst β hy)]; exact h⟩
     inner_val := fun y hy => by
       rw [fOf_eq hβ3 θ (cent_le_Kst β hy)]; exact psiHom_inner hβ3 θ hy }⟩

end Construction

namespace KEmb

variable {G : Type} [Group G] [Finite G] {β : G} (E : KEmb G β)

theorem inj_two {P : Subgroup G} (hP : IsPGroup 2 P) (hPn : P ≤ Kst β) {a b : G} (ha : a ∈ P)
    (hb : b ∈ P) (h : E.f a = E.f b) : a = b := by
  have hy : a⁻¹ * b ∈ P := P.mul_mem (P.inv_mem ha) hb
  have h1 : E.f (a⁻¹ * b) = 1 := by
    rw [E.mul _ ((Kst β).inv_mem (hPn ha)) _ (hPn hb), E.inv (hPn ha), h, inv_mul_cancel]
  have hO : a⁻¹ * b ∈ OG β := (E.ker _ (hPn hy)).1 h1
  obtain ⟨n, hn⟩ := hP ⟨a⁻¹ * b, hy⟩
  have hn' : (a⁻¹ * b) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  exact inv_mul_eq_one.1 (M10Config.eq_one_of_odd_of_pow_two (odd_orderOf_OG hO) n hn')

@[expose] def homOn (P : Subgroup G) (hPn : P ≤ Kst β) : ↥P →* Equiv.Perm (Fin 820) where
  toFun g := E.f g
  map_one' := E.one
  map_mul' a b := E.mul a (hPn a.2) b (hPn b.2)

theorem homOn_injective {P : Subgroup G} (hP : IsPGroup 2 P) (hPn : P ≤ Kst β) :
    Function.Injective (E.homOn P hPn) := fun a b h =>
  Subtype.ext (E.inj_two hP hPn a.2 b.2 h)

theorem exists_image {P : Subgroup G} (hP : IsPGroup 2 P) (hPn : P ≤ Kst β) :
    ∃ R : Subgroup (Equiv.Perm (Fin 820)), R ≤ U16.U43ExtStar ∧ IsPGroup 2 R ∧
      Nonempty (↥P ≃* ↥R) ∧ (∀ g ∈ P, E.f g ∈ R) ∧ (∀ r ∈ R, ∃ g ∈ P, E.f g = r) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(E.homOn P hPn).range = Nat.card ↥P :=
    (Nat.card_congr (MonoidHom.ofInjective (E.homOn_injective hP hPn)).toEquiv).symm
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  refine ⟨(E.homOn P hPn).range, ?_, IsPGroup.of_card (n := n) (by rw [hcard, hn]),
    ⟨MonoidHom.ofInjective (E.homOn_injective hP hPn)⟩, fun g hg => ⟨⟨g, hg⟩, rfl⟩,
    fun r ⟨g, hg⟩ => ⟨g, g.2, hg⟩⟩
  rintro _ ⟨g, rfl⟩
  exact E.mem g (hPn g.2)

theorem orderOf_f {P : Subgroup G} (hP : IsPGroup 2 P) (hPn : P ≤ Kst β) {s : G} (hs : s ∈ P) :
    orderOf (E.f s) = orderOf s := by
  have := orderOf_injective (E.homOn P hPn) (E.homOn_injective hP hPn) ⟨s, hs⟩
  rw [Subgroup.orderOf_mk] at this
  exact this

theorem lift_conj {x y : G} (hx : x ∈ Kst β) (hy : y ∈ Kst β) (hx2 : x * x = 1) (hy2 : y * y = 1)
    {c : Equiv.Perm (Fin 820)} (hc : c ∈ U43Ext) (hcxy : E.f y = c * E.f x * c⁻¹) :
    ∃ g : G, g * x * g⁻¹ = y := by
  obtain ⟨k, hk, hkc⟩ := E.surj c hc
  have hkK : k ∈ Kst β := cent_le_Kst β hk
  have ha'mem : k * x * k⁻¹ ∈ Kst β :=
    (Kst β).mul_mem ((Kst β).mul_mem hkK hx) ((Kst β).inv_mem hkK)
  have hfa' : E.f (k * x * k⁻¹) = E.f y := by rw [E.conj hx hkK, hkc, hcxy]
  have ha'2 : (k * x * k⁻¹) * (k * x * k⁻¹) = 1 := by
    calc (k * x * k⁻¹) * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hker : y⁻¹ * (k * x * k⁻¹) ∈ OG β := by
    have h1 : E.f (y⁻¹ * (k * x * k⁻¹)) = 1 := by
      rw [E.mul _ ((Kst β).inv_mem hy) _ ha'mem, E.inv hy, hfa', inv_mul_cancel]
    exact (E.ker _ ((Kst β).mul_mem ((Kst β).inv_mem hy) ha'mem)).1 h1
  obtain ⟨h, hh⟩ := exists_conj_of_inv_odd (b := y) (a := k * x * k⁻¹) (o := y⁻¹ * (k * x * k⁻¹))
    hy2 ha'2 (by group) (odd_orderOf_OG hker)
  refine ⟨(k⁻¹ * h)⁻¹, ?_⟩
  calc (k⁻¹ * h)⁻¹ * x * ((k⁻¹ * h)⁻¹)⁻¹ = h⁻¹ * (k * x * k⁻¹) * h := by group
    _ = y := by rw [hh]; group

theorem f_pow {P : Subgroup G} (hPn : P ≤ Kst β) {g : G} (hg : g ∈ P) (n : ℕ) :
    E.f (g ^ n) = (E.f g) ^ n := by
  have h := map_pow (E.homOn P hPn) ⟨g, hg⟩ n
  simpa [homOn] using h

theorem f_mem_P_of_A6 {H : Subgroup G} (hH : H ≤ centralizer ({β} : Set G))
    (hA : Nonempty (↥((H.subgroupOf (centralizer ({β} : Set G))).map
      (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G)))))
        ≃* alternatingGroup (Fin 6)))
    {d : G} (hd : d ∈ H) :
    E.f d ∈ P := by
  classical
  obtain ⟨e⟩ := hA
  set Dbar := (H.subgroupOf (centralizer ({β} : Set G))).map
    (QuotientGroup.mk' (fusionOddCore ↥(centralizer ({β} : Set G)))) with hDbar
  set Dp : Subgroup ↥U43Ext := Dbar.map E.θ.toMonoidHom with hDp
  let e₁ : ↥Dbar ≃* ↥Dp := Dbar.equivMapOfInjective E.θ.toMonoidHom E.θ.injective
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have e₂ : ↥Dp ≃* alternatingGroup (Fin 6) := e₁.symm.trans e
  haveI : IsSimpleGroup ↥Dp := MulEquiv.isSimpleGroup e₂
  have hDpcard : Nat.card ↥Dp = 360 := by
    rw [Nat.card_congr e₂.toEquiv]
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  set N : Subgroup ↥U43Ext := P.subgroupOf U43Ext with hN
  have hidx : N.index = 2 := U16.index_P_U43Ext
  haveI hNn : N.Normal := Subgroup.normal_of_index_eq_two hidx
  let φ : ↥Dp →* ↥U43Ext ⧸ N := (QuotientGroup.mk' N).comp Dp.subtype
  have hker : φ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exfalso
      have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
      have h1 : Nat.card ↥Dp ≤ Nat.card (↥U43Ext ⧸ N) := Nat.card_le_card_of_injective _ hinj
      have h2 : Nat.card (↥U43Ext ⧸ N) = 2 := by rw [← Subgroup.index_eq_card]; exact hidx
      omega
    · exact h
  have hdK : d ∈ centralizer ({β} : Set G) := hH hd
  have hmem : (E.θ (QuotientGroup.mk ⟨d, hdK⟩)) ∈ Dp :=
    ⟨QuotientGroup.mk ⟨d, hdK⟩, ⟨⟨d, hdK⟩, hd, rfl⟩, rfl⟩
  have h1 : φ ⟨_, hmem⟩ = 1 := by
    have : (⟨_, hmem⟩ : ↥Dp) ∈ φ.ker := by rw [hker]; trivial
    exact this
  have h2 : (E.θ (QuotientGroup.mk ⟨d, hdK⟩) : ↥U43Ext) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
  rw [E.inner_val d hdK]
  exact Subgroup.mem_subgroupOf.1 h2

end KEmb

end KEmb

end CFSG.EvenSporadicStandard.Fin76b

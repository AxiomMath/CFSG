module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneGMS43Second

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools
open CFSG.CGT.Timmesfeld75 (Goldschmidt1974)

namespace GMS43

variable {G : Type} [Group G]

theorem mk'_eq_mk'_iff {U₁ S : Subgroup G} [(U₁.subgroupOf S).Normal] (a b : S) :
    QuotientGroup.mk' (U₁.subgroupOf S) a = QuotientGroup.mk' (U₁.subgroupOf S) b ↔
      (a : G)⁻¹ * b ∈ U₁ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  rfl

theorem mk'_eq_one_iff {U₁ S : Subgroup G} [(U₁.subgroupOf S).Normal] (a : S) :
    QuotientGroup.mk' (U₁.subgroupOf S) a = 1 ↔ (a : G) ∈ U₁ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem mk'_eq_of_eq_mul {U₁ S : Subgroup G} [(U₁.subgroupOf S).Normal]
    (hSN : S ≤ normalizer (U₁ : Set G)) {a b : S} {e : G} (he : e ∈ U₁)
    (hab : (a : G) = e * b) :
    QuotientGroup.mk' (U₁.subgroupOf S) a = QuotientGroup.mk' (U₁.subgroupOf S) b := by
  rw [mk'_eq_mk'_iff, hab]
  have h1 := (mem_normalizer_iff.mp (inv_mem (hSN b.2)) e⁻¹).mp (inv_mem he)
  rw [inv_inv] at h1
  rwa [show (e * (b : G))⁻¹ * b = (b : G)⁻¹ * e⁻¹ * b by group]

variable [Finite G]

namespace Hyp

variable {L : Subgroup G} {f : ℕ} {t : G} {T V₁ U₁ : Subgroup G} {y d : G}
  (h : Hyp L f t T V₁ U₁ y d)
include h

theorem inv_mul_mul_mem_of_mem_T {p q : G} (hp : p ∈ T) (hq : q ∈ T) :
    (p * q)⁻¹ * (q * p) ∈ T ⊓ L := by
  obtain ⟨htT, htt, -, hTC, -, -, hVn, hcyc, -, -, -, -, -, -, hTU, -⟩ :=
    Endings.psl2_ending_facts h.gold h.setting
  have : ((T ⊓ L).subgroupOf T).Normal := normal_subgroupOf_of_le_normalizer hTU
  have : ((T ⊓ L ⊔ zpowers t).subgroupOf T).Normal := hVn
  have : IsCyclic (T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) := hcyc
  have hle : (T ⊓ L).subgroupOf T ≤
      ((T ⊓ L ⊔ zpowers t).subgroupOf T).comap (MonoidHom.id T) := fun x hx =>
    mem_subgroupOf.mpr (mem_sup_left (mem_subgroupOf.mp hx))
  set φ := QuotientGroup.map ((T ⊓ L).subgroupOf T) ((T ⊓ L ⊔ zpowers t).subgroupOf T)
    (MonoidHom.id T) hle
  have hcent : ∀ v r : T, (v : G) ∈ T ⊓ L ⊔ zpowers t →
      ((r : G) * v)⁻¹ * ((v : G) * r) ∈ T ⊓ L := by
    intro v r hv
    have hrN : (r : G)⁻¹ ∈ normalizer ((T ⊓ L : Subgroup G) : Set G) := inv_mem (hTU r.2)
    have hconj : ∀ u ∈ T ⊓ L, u⁻¹ * ((r : G)⁻¹ * u * r) ∈ T ⊓ L := fun u hu => by
      have h1 := (mem_normalizer_iff.mp hrN u).mp hu
      rw [inv_inv] at h1
      exact mul_mem (inv_mem hu) h1
    obtain ⟨u, hu, hv' | hv'⟩ :=
      Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt (zpowers_le.mpr (hTU htT)) hv
    · rw [← hv', show ((r : G) * u)⁻¹ * (u * r) = u⁻¹ * ((r : G)⁻¹ * u * r) by group]
      exact hconj u hu
    · rw [← hv']
      have hrt : (r : G) * t = t * r := mem_centralizer_singleton_iff.mp (hTC r.2)
      have e : ((r : G) * (u * t))⁻¹ * (u * t * r) =
          t⁻¹ * (u⁻¹ * ((r : G)⁻¹ * u * r)) * t := by
        calc ((r : G) * (u * t))⁻¹ * (u * t * r) = t⁻¹ * u⁻¹ * (r : G)⁻¹ * u * (t * r) := by
              group
          _ = t⁻¹ * u⁻¹ * (r : G)⁻¹ * u * (r * t) := by rw [hrt]
          _ = _ := by group
      rw [e]
      have h1 := (mem_normalizer_iff.mp (inv_mem (hTU htT)) _).mp (hconj u hu)
      rwa [inv_inv] at h1
  have hker : φ.ker ≤ center (T ⧸ (T ⊓ L).subgroupOf T) := by
    intro x hx
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    have hv : (v : G) ∈ T ⊓ L ⊔ zpowers t := by
      rw [MonoidHom.mem_ker] at hx
      change ((v : T) : T ⧸ (T ⊓ L ⊔ zpowers t).subgroupOf T) = 1 at hx
      rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at hx
      exact hx
    rw [mem_center_iff]
    intro g
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
    exact hcent v r hv
  have key := (φ.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm
    ((⟨p, hp⟩ : T) : T ⧸ (T ⊓ L).subgroupOf T) ((⟨q, hq⟩ : T) : T ⧸ (T ⊓ L).subgroupOf T)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at key
  exact key

theorem inv_mul_mul_mem_of_mem_sup {a b : G} (ha : a ∈ U₁ ⊔ T) (hb : b ∈ U₁ ⊔ T) :
    (a * b)⁻¹ * (b * a) ∈ U₁ := by
  obtain ⟨e₁, he₁, p₁, hp₁, rfl⟩ := Endings.exists_mul_eq_of_mem_sup h.T_le_normalizer ha
  obtain ⟨e₂, he₂, p₂, hp₂, rfl⟩ := Endings.exists_mul_eq_of_mem_sup h.T_le_normalizer hb
  have hpe₂ : p₁ * e₂ * p₁⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (h.T_le_normalizer hp₁) e₂).mp he₂
  have hpe₁ : p₂ * e₁ * p₂⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (h.T_le_normalizer hp₂) e₁).mp he₁
  have hcU : (e₁ * (p₁ * e₂ * p₁⁻¹))⁻¹ * (e₂ * (p₂ * e₁ * p₂⁻¹)) ∈ U₁ :=
    mul_mem (inv_mem (mul_mem he₁ hpe₂)) (mul_mem he₂ hpe₁)
  have hcU' : (p₁ * p₂)⁻¹ * ((e₁ * (p₁ * e₂ * p₁⁻¹))⁻¹ * (e₂ * (p₂ * e₁ * p₂⁻¹))) *
      (p₁ * p₂) ∈ U₁ := by
    have h1 := (mem_normalizer_iff.mp (inv_mem (h.T_le_normalizer (mul_mem hp₁ hp₂))) _).mp hcU
    rwa [inv_inv] at h1
  have e : (e₁ * p₁ * (e₂ * p₂))⁻¹ * (e₂ * p₂ * (e₁ * p₁)) =
      ((p₁ * p₂)⁻¹ * ((e₁ * (p₁ * e₂ * p₁⁻¹))⁻¹ * (e₂ * (p₂ * e₁ * p₂⁻¹))) * (p₁ * p₂)) *
        ((p₁ * p₂)⁻¹ * (p₂ * p₁)) := by
    group
  rw [e]
  exact mul_mem hcU' (h.U_le (h.inv_mul_mul_mem_of_mem_T hp₁ hp₂))

theorem mem_sup_zpowers_or_mul_mem {τ : G} (hτ : τ ∈ T) (hττ : τ * τ = 1)
    (hτV : τ ∉ T ⊓ L ⊔ zpowers t) {a : G} (ha : a ∈ U₁ ⊔ T) (haa : a * a ∈ U₁) :
    a ∈ U₁ ⊔ zpowers t ∨ a * τ ∈ U₁ ⊔ zpowers t := by
  by_cases haV : a ∈ U₁ ⊔ zpowers t
  · exact Or.inl haV
  right
  obtain ⟨e, he, p, hp, rfl, hpV⟩ := h.exists_mul_eq_of_not_mem ha haV
  have hpe : p * e * p⁻¹ ∈ U₁ := (mem_normalizer_iff.mp (h.T_le_normalizer hp) e).mp he
  have hp2 : p * p ∈ T ⊓ L := by
    rw [← h.inf_T]
    refine mem_inf.mpr ⟨?_, mul_mem hp hp⟩
    rw [show p * p = (e * (p * e * p⁻¹))⁻¹ * (e * p * (e * p)) by group]
    exact mul_mem (inv_mem (mul_mem he hpe)) haa
  have hpτ := h.mul_mem_of_sq_mem hp hτ hpV hτV (mem_sup_left hp2)
    (by rw [hττ]; exact one_mem _)
  have hVW : T ⊓ L ⊔ zpowers t ≤ U₁ ⊔ zpowers t :=
    sup_le (h.U_le.trans le_sup_left) le_sup_right
  rw [mul_assoc]
  exact mul_mem (mem_sup_left he) (hVW hpτ)

theorem exists_conj_eq_mul_of_mul_self {e : G} (he : e ∈ U₁) (hte : t * e * (t * e) = 1) :
    ∃ g : G, g⁻¹ * t * g = t * e := by
  have het : e * t = t * e := by
    have h1 : t * e * t = e⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hte]; group)
    rw [h.inv_eq e he] at h1
    calc e * t = t * e * t * t := by rw [h1]
      _ = t * e * (t * t) := by group
      _ = t * e := by rw [h.t_mul_t, mul_one]
  have heU : e ∈ T ⊓ L := by
    rw [← h.result.centralizer_eq]
    exact mem_inf.mpr ⟨he, mem_centralizer_singleton_iff.mpr het⟩
  obtain ⟨e₁, -, he₁t⟩ := h.result.exists_comm_eq e heU
  refine ⟨e₁⁻¹, ?_⟩
  rw [inv_inv, ← het, ← he₁t, mul_assoc (e₁ * t * e₁⁻¹) t t, h.t_mul_t, mul_one]

variable {S : Subgroup G} [(U₁.subgroupOf S).Normal]

theorem mk'_mul_comm_iff (hSp : IsPGroup 2 S) (hES : U₁ ⊔ T ≤ S) {s₀ : S} (hs₀ : (s₀ : G) = t)
    (a : S) :
    QuotientGroup.mk' (U₁.subgroupOf S) a * QuotientGroup.mk' (U₁.subgroupOf S) s₀ =
        QuotientGroup.mk' (U₁.subgroupOf S) s₀ * QuotientGroup.mk' (U₁.subgroupOf S) a ↔
      (a : G) ∈ U₁ ⊔ T := by
  have hSN : S ≤ normalizer (U₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hES)).mp ‹_›
  rw [← map_mul, ← map_mul, mk'_eq_mk'_iff, Subgroup.coe_mul, Subgroup.coe_mul, hs₀]
  have e : ((a : G) * t)⁻¹ * (t * a) = ((a : G)⁻¹ * (t * (a * t * (a : G)⁻¹)) * a)⁻¹ := by
    simp only [mul_inv_rev, inv_inv, h.t_inv]
    group
  rw [e, inv_mem_iff]
  have hn := mem_normalizer_iff.mp (inv_mem (hSN a.2)) (t * ((a : G) * t * (a : G)⁻¹))
  rw [inv_inv] at hn
  rw [← hn]
  exact ⟨h.mem_sup_of_mul_conj_mem hSp hES a.2, h.mul_conj_mem_of_mem_sup⟩

theorem mk'_comm_of_comm (hSp : IsPGroup 2 S) (hES : U₁ ⊔ T ≤ S) {s₀ : S} (hs₀ : (s₀ : G) = t)
    (a b : S ⧸ U₁.subgroupOf S)
    (ha : a * QuotientGroup.mk' (U₁.subgroupOf S) s₀ = QuotientGroup.mk' (U₁.subgroupOf S) s₀ * a)
    (hb : b * QuotientGroup.mk' (U₁.subgroupOf S) s₀ = QuotientGroup.mk' (U₁.subgroupOf S) s₀ * b) :
    a * b = b * a := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (U₁.subgroupOf S) a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U₁.subgroupOf S) b
  have ha' := (h.mk'_mul_comm_iff hSp hES hs₀ a).mp ha
  have hb' := (h.mk'_mul_comm_iff hSp hES hs₀ b).mp hb
  rw [← map_mul, ← map_mul, mk'_eq_mk'_iff, Subgroup.coe_mul, Subgroup.coe_mul]
  exact h.inv_mul_mul_mem_of_mem_sup ha' hb'

theorem mk'_eq_of_mul_self_eq_one (hSp : IsPGroup 2 S) (hES : U₁ ⊔ T ≤ S) {s₀ τ₀ : S}
    (hs₀ : (s₀ : G) = t) (hτ : (τ₀ : G) ∈ T) (hττ : (τ₀ : G) * τ₀ = 1)
    (hτV : (τ₀ : G) ∉ T ⊓ L ⊔ zpowers t) (v : S ⧸ U₁.subgroupOf S)
    (hv : v * QuotientGroup.mk' (U₁.subgroupOf S) s₀ = QuotientGroup.mk' (U₁.subgroupOf S) s₀ * v)
    (hvv : v * v = 1) :
    v = 1 ∨ v = QuotientGroup.mk' (U₁.subgroupOf S) s₀ ∨
      v = QuotientGroup.mk' (U₁.subgroupOf S) τ₀ ∨
      v = QuotientGroup.mk' (U₁.subgroupOf S) s₀ * QuotientGroup.mk' (U₁.subgroupOf S) τ₀ := by
  have hSN : S ≤ normalizer (U₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hES)).mp ‹_›
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (U₁.subgroupOf S) v
  have ha := (h.mk'_mul_comm_iff hSp hES hs₀ a).mp hv
  have haa : (a : G) * a ∈ U₁ := by
    rw [← map_mul, mk'_eq_one_iff] at hvv
    exact hvv
  rcases h.mem_sup_zpowers_or_mul_mem hτ hττ hτV ha haa with h1 | h1
  · obtain ⟨e, he, h2 | h2⟩ :=
      Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers h.t_mul_t h.zpowers_le_normalizer h1
    · left
      rw [mk'_eq_one_iff, ← h2]
      exact he
    · right; left
      exact mk'_eq_of_eq_mul hSN he (by rw [hs₀, h2])
  · obtain ⟨e, he, h2 | h2⟩ :=
      Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers h.t_mul_t h.zpowers_le_normalizer h1
    · right; right; left
      exact mk'_eq_of_eq_mul hSN he (by rw [h2, mul_assoc, hττ, mul_one])
    · right; right; right
      rw [← map_mul]
      refine mk'_eq_of_eq_mul hSN he ?_
      rw [Subgroup.coe_mul, hs₀, ← mul_assoc, h2, mul_assoc, hττ, mul_one]

theorem not_isConj_mk' (hES : U₁ ⊔ T ≤ S) {s₀ : S} (hs₀ : (s₀ : G) = t) {x : S}
    (hxx : (x : G) * x = 1) (hxt : ∀ g : G, g⁻¹ * t * g ≠ x) :
    ¬ IsConj (QuotientGroup.mk' (U₁.subgroupOf S) s₀) (QuotientGroup.mk' (U₁.subgroupOf S) x) := by
  have hSN : S ≤ normalizer (U₁ : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_sup_left.trans hES)).mp ‹_›
  intro hc
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (U₁.subgroupOf S) c
  rw [← map_inv, ← map_mul, ← map_mul, mk'_eq_mk'_iff, Subgroup.coe_mul, Subgroup.coe_mul,
    Subgroup.coe_inv, hs₀] at hc
  have he' : (s : G)⁻¹ * (((s : G) * t * (s : G)⁻¹)⁻¹ * x) * s ∈ U₁ := by
    have h1 := (mem_normalizer_iff.mp (inv_mem (hSN s.2)) _).mp hc
    rwa [inv_inv] at h1
  have hte : t * ((s : G)⁻¹ * (((s : G) * t * (s : G)⁻¹)⁻¹ * x) * s) = (s : G)⁻¹ * x * s := by
    group
  have hinv : t * ((s : G)⁻¹ * (((s : G) * t * (s : G)⁻¹)⁻¹ * x) * s) *
      (t * ((s : G)⁻¹ * (((s : G) * t * (s : G)⁻¹)⁻¹ * x) * s)) = 1 := by
    rw [hte, show (s : G)⁻¹ * x * s * ((s : G)⁻¹ * x * s) = (s : G)⁻¹ * (x * x) * s by group, hxx]
    group
  obtain ⟨g, hg⟩ := h.exists_conj_eq_mul_of_mul_self he' hinv
  apply hxt (g * (s : G)⁻¹)
  rw [show (g * (s : G)⁻¹)⁻¹ * t * (g * (s : G)⁻¹) = s * (g⁻¹ * t * g) * (s : G)⁻¹ by group, hg,
    hte]
  group

end Hyp

end GMS43

end CFSG.SeitzReduction.RankOne

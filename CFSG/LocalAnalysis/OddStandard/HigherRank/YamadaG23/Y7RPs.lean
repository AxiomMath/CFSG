module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RRk
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7RWe

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] {t : G} {P U : Subgroup G}

@[expose] def wrStar (t : G) (P : Subgroup G) : Subgroup G := P ⊔ zpowers t

private lemma conj_inv_sq {G : Type*} [Group G] {t x : G} (htt : t * t = 1) :
    t * (t * x * t⁻¹) * t⁻¹ = x := by
  have hii : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, htt, inv_one]
  calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) := by group
    _ = x := by rw [htt, one_mul, hii, mul_one]

private lemma isElemAbelian_mono {p : ℕ} {E F : Subgroup G} (hEF : E ≤ F)
    (hF : IsElemAbelian p F) : IsElemAbelian p E := by
  refine ⟨?_, fun a ha => hF.2 a (hEF ha)⟩
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  simpa using congrArg Subtype.val
    ((isMulCommutative_iff.mp hF.1) (⟨a, hEF a.2⟩ : ↥F) ⟨b, hEF b.2⟩)

private theorem isElemAbelian_map' {H H' : Type*} [Group H] [Group H'] {p : ℕ}
    (f : H →* H') {X : Subgroup H} (hX : IsElemAbelian p X) :
    IsElemAbelian p (X.map f) := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro a b
    obtain ⟨a', ha', ha_eq⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb_eq⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    push_cast
    rw [← ha_eq, ← hb_eq]
    have hval : a' * b' = b' * a' := by
      simpa using congrArg Subtype.val
        ((isMulCommutative_iff.mp hX.1) (⟨a', ha'⟩ : ↥X) ⟨b', hb'⟩)
    simpa only [← map_mul] using congrArg f hval
  · intro a ha
    obtain ⟨a', ha', ha_eq⟩ := Subgroup.mem_map.mp ha
    rw [← ha_eq]
    have ha'p : a' ^ p = 1 := hX.2 a' ha'
    simpa only [map_pow, map_one] using congrArg f ha'p

theorem Wr7.mem_star (h : Wr7 t P U) {x : G} : x ∈ wrStar t P ↔ x ∈ P ∨ x * t⁻¹ ∈ P := by
  have htt : t * t = 1 := by simpa [pow_two] using h.t_sq
  have hii : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, htt, inv_one]
  refine ⟨?_, ?_⟩
  · intro hx
    have hle : wrStar t P ≤ Subgroup.closure ((P : Set G) ∪ {t}) :=
      sup_le (fun y hy => Subgroup.subset_closure (Or.inl hy))
        (zpowers_le.mpr (Subgroup.subset_closure (Or.inr rfl)))
    exact Subgroup.closure_induction
      (p := fun y _ => y ∈ P ∨ y * t⁻¹ ∈ P)
      (fun y hy => by
        rcases hy with hyP | hy
        · exact Or.inl hyP
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          exact Or.inr (by simp))
      (Or.inl (one_mem P))
      (fun a b _ _ ha hb => by
        rcases ha with ha | ha <;> rcases hb with hb | hb
        · exact Or.inl (mul_mem ha hb)
        · exact Or.inr (by
            have : a * b * t⁻¹ = a * (b * t⁻¹) := by group
            rw [this]; exact mul_mem ha hb)
        · exact Or.inr (by
            have : a * b * t⁻¹ = (a * t⁻¹) * (t * b * t⁻¹) := by group
            rw [this]; exact mul_mem ha (h.conj_mem hb))
        · exact Or.inl (by
            have hb' : t * (b * t⁻¹) * t⁻¹ ∈ P := h.conj_mem hb
            have : a * b = (a * t⁻¹) * (t * (b * t⁻¹) * t⁻¹) := by
              calc a * b = a * b * (t⁻¹ * t⁻¹) := by rw [hii, mul_one]
                _ = (a * t⁻¹) * (t * (b * t⁻¹) * t⁻¹) := by group
            rw [this]; exact mul_mem ha hb'))
      (fun a _ ha => by
        rcases ha with ha | ha
        · exact Or.inl (inv_mem ha)
        · exact Or.inr (by
            have ha' : t * (a * t⁻¹)⁻¹ * t⁻¹ ∈ P := h.conj_mem (inv_mem ha)
            have : a⁻¹ * t⁻¹ = t * (a * t⁻¹)⁻¹ * t⁻¹ := by
              calc a⁻¹ * t⁻¹ = (t * t) * (a⁻¹ * t⁻¹) := by rw [htt, one_mul]
                _ = t * (a * t⁻¹)⁻¹ * t⁻¹ := by group
            rw [this]; exact ha'))
      (hle hx)
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have : (x * t⁻¹) * t ∈ P ⊔ zpowers t :=
        Subgroup.mul_mem_sup hx (Subgroup.mem_zpowers t)
      simpa [wrStar] using this

theorem Wr7.le_normalizer_star (h : Wr7 t P U) : wrStar t P ≤ normalizer (P : Set G) := by
  have htt : t * t = 1 := by simpa [pow_two] using h.t_sq
  refine sup_le Subgroup.le_normalizer ?_
  rw [zpowers_le, Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨fun hx => h.conj_mem hx, fun hx => by
    have := h.conj_mem hx
    rwa [conj_inv_sq htt] at this⟩

theorem Wr7.centEl_star (h : Wr7 t P U) :
    wrStar t P ⊓ centralizer ({t} : Set G) = (P ⊓ centralizer ({t} : Set G)) ⊔ zpowers t := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hxC⟩ := hx
    rcases (Wr7.mem_star h).mp hxW with hxP | hxP
    · exact Subgroup.mem_sup_left ⟨hxP, hxC⟩
    · have hpt : x * t⁻¹ ∈ P ⊓ centralizer ({t} : Set G) := by
        refine ⟨hxP, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
        calc (x * t⁻¹) * t = x := by group
          _ = t * (x * t⁻¹) := by rw [← mul_assoc, hxt.symm]; group
      have hx_eq : x = (x * t⁻¹) * t := by group
      rw [hx_eq]
      exact Subgroup.mul_mem_sup hpt (Subgroup.mem_zpowers t)
  · refine sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right ?_)
    rw [zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

private lemma Wr7.cent_comp (h : Wr7 t P U) {x p e : G} (hp : p ∈ P) (hx : x = p * t)
    (he : e ∈ P) (hcomm : e * x = x * e) :
    ((h.proj1 ⟨e, he⟩ : ↥U) : G) * ((h.proj1 ⟨p, hp⟩ : ↥U) : G) =
      ((h.proj1 ⟨p, hp⟩ : ↥U) : G) *
        (t * ((h.proj2 ⟨e, he⟩ : ↥(conjSub t U)) : G) * t⁻¹) := by
  have hep : e * p = p * (t * e * t⁻¹) := by
    have hconj : e = p * (t * e * t⁻¹) * p⁻¹ := by
      calc e = x * e * x⁻¹ := by rw [← hcomm]; group
        _ = (p * t) * e * (p * t)⁻¹ := by rw [hx]
        _ = p * (t * e * t⁻¹) * p⁻¹ := by group
    nth_rewrite 1 [hconj]; group
  set e₁ : G := ((h.proj1 ⟨e, he⟩ : ↥U) : G) with he₁def
  set e₂ : G := ((h.proj2 ⟨e, he⟩ : ↥(conjSub t U)) : G) with he₂def
  set p₁ : G := ((h.proj1 ⟨p, hp⟩ : ↥U) : G) with hp₁def
  set p₂ : G := ((h.proj2 ⟨p, hp⟩ : ↥(conjSub t U)) : G) with hp₂def
  have he₁ : e₁ ∈ U := (h.proj1 ⟨e, he⟩).2
  have he₂ : e₂ ∈ conjSub t U := (h.proj2 ⟨e, he⟩).2
  have hp₁ : p₁ ∈ U := (h.proj1 ⟨p, hp⟩).2
  have hp₂ : p₂ ∈ conjSub t U := (h.proj2 ⟨p, hp⟩).2
  have he_eq : e₁ * e₂ = e := h.proj_mul ⟨e, he⟩
  have hp_eq : p₁ * p₂ = p := h.proj_mul ⟨p, hp⟩
  set X : G := t * e₁ * t⁻¹ with hXdef
  set Y : G := t * e₂ * t⁻¹ with hYdef
  have hX : X ∈ conjSub t U := (mem_conjSub_iff' t U X).mpr ⟨e₁, he₁, rfl⟩
  have hY : Y ∈ U := by
    have : Y ∈ conjSub t (conjSub t U) :=
      (mem_conjSub_iff' t (conjSub t U) Y).mpr ⟨e₂, he₂, rfl⟩
    rwa [conjSub_conjSub_of_sq h.t_sq U] at this
  have hXY : X * Y = t * e * t⁻¹ := by
    rw [hXdef, hYdef, ← he_eq]; group
  have hL : (e₁ * p₁) * (e₂ * p₂) = e * p := by
    have hc : p₁ * e₂ = e₂ * p₁ := h.direct.2.2 p₁ hp₁ e₂ he₂
    calc (e₁ * p₁) * (e₂ * p₂) = e₁ * (p₁ * e₂) * p₂ := by group
      _ = e₁ * (e₂ * p₁) * p₂ := by rw [hc]
      _ = e₁ * e₂ * (p₁ * p₂) := by group
      _ = e * p := by rw [he_eq, hp_eq]
  have hR : (p₁ * Y) * (p₂ * X) = p * (t * e * t⁻¹) := by
    have hYp₂ : Y * p₂ = p₂ * Y := h.direct.2.2 Y hY p₂ hp₂
    have hYX : Y * X = X * Y := h.direct.2.2 Y hY X hX
    calc (p₁ * Y) * (p₂ * X) = p₁ * (Y * p₂) * X := by group
      _ = p₁ * (p₂ * Y) * X := by rw [hYp₂]
      _ = p₁ * p₂ * (Y * X) := by group
      _ = p₁ * p₂ * (X * Y) := by rw [hYX]
      _ = (p₁ * p₂) * (t * e * t⁻¹) := by rw [hXY]
      _ = p * (t * e * t⁻¹) := by rw [hp_eq]
  have heq : (e₁ * p₁) * (e₂ * p₂) = (p₁ * Y) * (p₂ * X) := by
    rw [hL, hR, hep]
  exact (Wr7.unique h (mul_mem he₁ hp₁) (mul_mem hp₁ hY)
    (mul_mem he₂ hp₂) (mul_mem hp₂ hX) heq).1

theorem Wr7.cent_bound (h : Wr7 t P U) (hU : RankFacts U) {x : G} (hx : x ∈ wrStar t P)
    (hxP : x ∉ P) :
    ∀ E : Subgroup G, E ≤ P → IsElemAbelian 2 E → (∀ e ∈ E, e * x = x * e) → Nat.card E ≤ 8 := by
  have hx' : x * t⁻¹ ∈ P := (Wr7.mem_star h).mp hx |>.resolve_left hxP
  have hx_eq : x = (x * t⁻¹) * t := by group
  intro E hEP hEel hEcent
  let φ : ↥E →* ↥U := (h.proj1).comp (Subgroup.inclusion hEP)
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he1
    have heP : (e : G) ∈ P := hEP e.2
    have hcomp := Wr7.cent_comp h hx' hx_eq heP (hEcent (e : G) e.2)
    have hproj1 : ((h.proj1 ⟨(e : G), heP⟩ : ↥U) : G) = 1 := by
      have he1' : h.proj1 ⟨(e : G), heP⟩ = 1 := he1
      simpa using congrArg (fun z : ↥U => (z : G)) he1'
    rw [hproj1, one_mul] at hcomp
    have hY1 : t * ((h.proj2 ⟨(e : G), heP⟩ : ↥(conjSub t U)) : G) * t⁻¹ = 1 := by
      have h1 : ((h.proj1 ⟨x * t⁻¹, hx'⟩ : ↥U) : G) * 1 =
          ((h.proj1 ⟨x * t⁻¹, hx'⟩ : ↥U) : G) *
            (t * ((h.proj2 ⟨(e : G), heP⟩ : ↥(conjSub t U)) : G) * t⁻¹) := by
        rw [mul_one]; exact hcomp
      exact (mul_left_cancel h1).symm
    have he₂1 : ((h.proj2 ⟨(e : G), heP⟩ : ↥(conjSub t U)) : G) = 1 := by
      calc ((h.proj2 ⟨(e : G), heP⟩ : ↥(conjSub t U)) : G)
          = t⁻¹ * (t * ((h.proj2 ⟨(e : G), heP⟩ : ↥(conjSub t U)) : G) * t⁻¹) * t :=
            by group
        _ = 1 := by rw [hY1]; group
    have heG : (e : G) = 1 := by
      rw [← h.proj_mul ⟨(e : G), heP⟩, hproj1, he₂1, one_mul]
    exact Subtype.ext (by simpa using heG)
  let F : Subgroup ↥U := φ.range
  let E' : Subgroup G := F.map U.subtype
  have hE'le : E' ≤ U := by
    rintro g ⟨u, -, rfl⟩
    exact u.2
  have hFel : IsElemAbelian 2 F := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff]
      intro a b
      obtain ⟨ea, haeq⟩ := MonoidHom.mem_range.mp a.2
      obtain ⟨eb, hbeq⟩ := MonoidHom.mem_range.mp b.2
      apply Subtype.ext
      push_cast
      rw [← haeq, ← hbeq]
      simpa only [map_mul] using congrArg φ ((isMulCommutative_iff.mp hEel.1) ea eb)
    · intro a ha
      obtain ⟨e, heq⟩ := MonoidHom.mem_range.mp ha
      rw [← heq]
      have he2 : e ^ 2 = 1 := by
        apply Subtype.ext
        simpa using hEel.2 (e : G) e.2
      simpa only [map_pow, map_one] using congrArg φ he2
  have hE'el : IsElemAbelian 2 E' := isElemAbelian_map' U.subtype hFel
  have hcard1 : Nat.card E' = Nat.card F :=
    Subgroup.card_map_of_injective (K := F) (f := U.subtype) U.subtype_injective
  have hcard2 : Nat.card F = Nat.card ↥E := by
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥E)) (f := φ) hφinj
    rw [Subgroup.card_top, ← MonoidHom.range_eq_map] at h
    exact h
  have hbound : Nat.card E' ≤ 8 := hU.bound E' hE'le hE'el
  rwa [hcard1, hcard2] at hbound

theorem Wr7.abelian_out (h : Wr7 t P U) (hU : RankFacts U) {V : Subgroup G}
    (hV : V ≤ wrStar t P) (hVc : IsMulCommutative V) (hVP : ¬ V ≤ P) :
    ∀ E : Subgroup G, E ≤ V → IsElemAbelian 2 E → Nat.card E ≤ 16 := by
  obtain ⟨x, hxV, hxP⟩ := Set.not_subset.mp hVP
  have hxW : x ∈ wrStar t P := hV hxV
  intro E hEV hEel
  have hHel : IsElemAbelian 2 (E ⊓ P) := isElemAbelian_mono inf_le_left hEel
  have hHcent : ∀ e ∈ E ⊓ P, e * x = x * e := by
    intro e he
    have heV : e ∈ V := hEV he.1
    have hc := (isMulCommutative_iff.mp hVc) (⟨e, heV⟩ : ↥V) (⟨x, hxV⟩ : ↥V)
    simpa using congrArg Subtype.val hc
  have hHbound : Nat.card ↥(E ⊓ P) ≤ 8 :=
    Wr7.cent_bound h hU hxW hxP (E ⊓ P) inf_le_right hHel hHcent
  by_cases hEP : E ≤ P
  · have hinf : E ⊓ P = E := inf_eq_left.mpr hEP
    rw [hinf] at hHbound
    omega
  · obtain ⟨e₀, he₀E, he₀P⟩ := Set.not_subset.mp hEP
    have hdvd : (E ⊓ P).relIndex E ∣ 2 := by
      rw [Subgroup.relIndex_dvd_two_iff]
      refine ⟨e₀, he₀E, fun b hbE => ?_⟩
      by_cases hbP : b ∈ P
      · exact Or.inr (Subgroup.mem_inf.mpr ⟨hbE, hbP⟩)
      · refine Or.inl (Subgroup.mem_inf.mpr ⟨mul_mem hbE he₀E, ?_⟩)
        have hbW : b ∈ wrStar t P := hV (hEV hbE)
        have hbt : b * t⁻¹ ∈ P := (Wr7.mem_star h).mp hbW |>.resolve_left hbP
        have he₀t : e₀ * t⁻¹ ∈ P :=
          (Wr7.mem_star h).mp (hV (hEV he₀E)) |>.resolve_left he₀P
        have hb0 : b * e₀⁻¹ ∈ P := by
          have hm := mul_mem hbt (inv_mem he₀t)
          convert hm using 1
          group
        have he₀2 : e₀ ^ 2 = 1 := by simpa using hEel.2 e₀ he₀E
        have he₀inv : e₀⁻¹ = e₀ :=
          inv_eq_of_mul_eq_one_right (by simpa [pow_two] using he₀2)
        simpa only [he₀inv] using hb0
    have hindex : (E ⊓ P).relIndex E ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hcard : Nat.card E = (E ⊓ P).relIndex E * Nat.card ↥(E ⊓ P) := by
      have hrel := Subgroup.relIndex_mul_card (H := E ⊓ P) (K := E)
      rw [inf_eq_left.mpr inf_le_left] at hrel
      exact hrel.symm
    calc Nat.card E = (E ⊓ P).relIndex E * Nat.card ↥(E ⊓ P) := hcard
      _ ≤ 2 * 8 := Nat.mul_le_mul hindex hHbound
      _ = 16 := by norm_num

end CFSG.OddStandard.HigherRank.YamadaG23

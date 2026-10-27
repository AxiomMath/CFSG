module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3PocketLemmas
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L310Syl
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6FactDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem Sec7Ctx.isOm6P [Finite G] {t : G} {L S : Subgroup G} {z : G} (h : Sec7Ctx G t L S z) :
    IsOm6P L :=
  ⟨h.component.isQuasisimple, h.omega6⟩

theorem Sec7Ctx.le_centralizer [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (h : Sec7Ctx G t L S z) : L ≤ centralizer ({t} : Set G) :=
  h.component.le

theorem Sec7Ctx.t_mem_centralizer [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (h : Sec7Ctx G t L S z) : t ∈ centralizer (L : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
  exact Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hl)

theorem Sec7Ctx.cent_le_normalizer [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G}
    {z : G} (h : Sec7Ctx G t L S z) :
    ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G) := by
  intro c hc
  exact mem_normalizer_of_conjugate_eq (conjugate_eq_self_of_lemma36 h36 h.toSec3SettingLB c hc)

theorem Sec7Ctx.t_mem_S [Finite G] {t : G} {L S : Subgroup G} {z : G} (h : Sec7Ctx G t L S z) :
    t ∈ S := by
  classical
  let H : Subgroup G := centralizer ({t} : Set G)
  have htH : t ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let tH : ↥H := ⟨t, htH⟩
  have htH2 : orderOf tH = 2 := by
    rw [Subgroup.orderOf_mk, h.involution]
  let P : Subgroup ↥H := Subgroup.zpowers tH
  have hPcard : Nat.card P = 2 := by
    change Nat.card (Subgroup.zpowers tH) = 2
    rw [Nat.card_zpowers, htH2]
  have hP : IsPGroup 2 P := IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num)
  have hPcenter : P ≤ Subgroup.center ↥H := by
    rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
    intro a
    apply Subtype.ext
    show (a : G) * t = t * (a : G)
    exact Subgroup.mem_centralizer_singleton_iff.mp a.2
  haveI : P.Normal := Subgroup.normal_of_le_center hPcenter
  obtain ⟨Q, hQ⟩ := h.sylow.exists_sylow
  have htHQ : tH ∈ Q := hP.le_sylow_of_normal Q (Subgroup.mem_zpowers tH)
  have htmap : t ∈ (Q : Subgroup ↥H).map H.subtype := Subgroup.mem_map.mpr ⟨tH, htHQ, rfl⟩
  rwa [hQ] at htmap

theorem Sec7Ctx.isSylow2Of_inf [Finite G] (h36 : Asc82Lemma36) {t : G} {L S : Subgroup G} {z : G}
    (h : Sec7Ctx G t L S z) : IsSylow2Of (S ⊓ L) L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 S (centralizer ({t} : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr h.sylow
  have hinf : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ L) L :=
    hS.inf_of_le_normalizer h.component.le (h.cent_le_normalizer h36)
  exact CFSG.ABGLocalTools.isSylowOf_iff.mp hinf

theorem Sec7Ctx.z_mem_L [Finite G] {t : G} {L S : Subgroup G} {z : G} (h : Sec7Ctx G t L S z) :
    z ∈ L :=
  h.pocket.mem

theorem Sec7Ctx.z_mem_centerIn [Finite G] {t : G} {L S : Subgroup G} {z : G}
    (h : Sec7Ctx G t L S z) : z ∈ centerIn (S ⊓ L) := by
  refine Subgroup.mem_map.mpr ⟨⟨z, h.mem_S, h.z_mem_L⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro a
  apply Subtype.ext
  exact h.central a.1 a.2.1

theorem isSylow2Of_conjugate {S H : Subgroup G} (h : IsSylow2Of S H) (g : G) :
    IsSylow2Of (CFSG.conjugate S g) (CFSG.conjugate H g) := by
  obtain ⟨hle, hp, hndvd⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · unfold CFSG.conjugate
    exact Subgroup.map_mono hle
  · unfold CFSG.conjugate
    exact hp.map (MulAut.conj g⁻¹).toMonoidHom
  · unfold CFSG.conjugate
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hndvd

theorem asc82Notation_conjugate {t : G} {L S : Subgroup G} {z : G} (h : Asc82Notation t L S z)
    (g : G) : Asc82Notation (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g)
      (g⁻¹ * z * g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← conjugate_centralizer_singleton t g]
    exact isSylow2Of_conjugate h.sylow g
  · rw [mem_conjugate_iff S g (g⁻¹ * z * g)]
    convert h.mem_S using 1
    group
  · intro s hs
    have hs' : g * s * g⁻¹ ∈ S := (mem_conjugate_iff S g s).mp hs
    have hc := h.central (g * s * g⁻¹) hs'
    calc s * (g⁻¹ * z * g) = g⁻¹ * ((g * s * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * s * g⁻¹)) * g := by rw [hc]
      _ = (g⁻¹ * z * g) * s := by group
  · exact h.pocket.conjugate g

theorem Sec7Ctx.conjugate [Finite G] {t : G} {L S : Subgroup G} {z : G} (h : Sec7Ctx G t L S z)
    (g : G) : Sec7Ctx G (g⁻¹ * t * g) (CFSG.conjugate L g) (CFSG.conjugate S g) (g⁻¹ * z * g) :=
  { toSec3SettingLB := h.toSec3SettingLB.conjugate g
    toAsc82Notation := asc82Notation_conjugate h.toAsc82Notation g
    omega6 := lieModel_quotient_oddCore_conjugate g h.omega6 }

theorem isOm6P_conjugate {L : Subgroup G} (h : IsOm6P L) (g : G) : IsOm6P (CFSG.conjugate L g) := by
  refine ⟨?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective L (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective) h.1
  · exact lieModel_quotient_oddCore_conjugate g h.2

theorem inducesTypeSome_conjugate {L : Subgroup G} {s : G} {n : ℕ} {ε : ℤˣ} {r : ℕ} {α : ℤˣ}
    (h : InducesTypeSome L s n ε r α) (g : G) :
    InducesTypeSome (CFSG.conjugate L g) (g⁻¹ * s * g) n ε r α := by
  classical
  obtain ⟨V, hAdd, hMod, hFin, Q, hQ, e, x, hfin, hsign, hvia, htype⟩ := h
  let φ : ↥L ≃* ↥(CFSG.conjugate L g) := (MulAut.conj g⁻¹).subgroupMap L
  let ψ : ↥(CFSG.conjugate L g) ≃* ↥L := φ.symm
  let hmap : (Subgroup.center ↥(CFSG.conjugate L g)).map ψ = Subgroup.center ↥L :=
    Subgroup.map_center_eq ψ
  let e' : ↥(CFSG.conjugate L g) ⧸ Subgroup.center ↥(CFSG.conjugate L g) ≃* omegaProj hQ :=
    (QuotientGroup.congr (Subgroup.center ↥(CFSG.conjugate L g)) (Subgroup.center ↥L)
      ψ hmap).trans e
  have he'_apply : ∀ l : ↥(CFSG.conjugate L g),
      e' (QuotientGroup.mk l) = e (QuotientGroup.mk (ψ l)) := by
    intro l
    change e ((QuotientGroup.congr (Subgroup.center ↥(CFSG.conjugate L g))
      (Subgroup.center ↥L) ψ hmap) (QuotientGroup.mk l)) = e (QuotientGroup.mk (ψ l))
    rw [QuotientGroup.congr_mk]
  have hψ : ∀ z : ↥(CFSG.conjugate L g), (ψ z : G) = g * (z : G) * g⁻¹ := by
    intro z
    have hz : g⁻¹ * (ψ z : G) * g = (z : G) := by
      have hval := congrArg Subtype.val (φ.apply_symm_apply z)
      change (MulAut.conj g⁻¹) (ψ z : G) = (z : G) at hval
      rwa [MulAut.conj_apply, inv_inv] at hval
    calc (ψ z : G) = g * (g⁻¹ * (ψ z : G) * g) * g⁻¹ := by group
      _ = g * (z : G) * g⁻¹ := by rw [hz]
  refine ⟨V, hAdd, hMod, hFin, Q, hQ, e', x, hfin, hsign, ?_, htype⟩
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjugate_iff L g y,
      mem_conjugate_iff L g ((g⁻¹ * s * g) * y * (g⁻¹ * s * g)⁻¹)]
    have hconj : g * ((g⁻¹ * s * g) * y * (g⁻¹ * s * g)⁻¹) * g⁻¹ =
        s * (g * y * g⁻¹) * s⁻¹ := by group
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp hvia.1) (g * y * g⁻¹)
  · intro l l' hl'
    have hmm' : (ψ l' : G) = s * (ψ l : G) * s⁻¹ := by
      rw [hψ l, hψ l', hl']
      group
    have hact := hvia.2 (ψ l) (ψ l') hmm'
    rw [he'_apply l', he'_apply l]
    exact hact

theorem inducesTypeSome_mul_centralizer {L : Subgroup G} {s c : G}
    (hc : c ∈ centralizer (L : Set G)) {n : ℕ} {ε : ℤˣ} {r : ℕ} {α : ℤˣ}
    (h : InducesTypeSome L s n ε r α) : InducesTypeSome L (s * c) n ε r α := by
  obtain ⟨V, hAdd, hMod, hFin, Q, hQ, e, x, hfin, hsign, hvia, htype⟩ := h
  refine ⟨V, hAdd, hMod, hFin, Q, hQ, e, x, hfin, hsign, ?_, htype⟩
  refine ⟨?_, ?_⟩
  · exact (Subgroup.normalizer (L : Set G)).mul_mem hvia.1
      ((Subgroup.centralizer_le_normalizer (L : Set G)) hc)
  · intro l l' hl'
    have hl'' : (l' : G) = s * l * s⁻¹ := by
      have hc' : c * (l : G) = (l : G) * c :=
        (Subgroup.mem_centralizer_iff.mp hc l l.2).symm
      rw [hl']
      calc (s * c) * (l : G) * (s * c)⁻¹ = s * (c * (l : G) * c⁻¹) * s⁻¹ := by group
        _ = s * (l : G) * s⁻¹ := by
          have hcl : c * (l : G) * c⁻¹ = (l : G) := by rw [hc']; group
          rw [hcl]
    exact hvia.2 l l' hl''

theorem innerOn_decompose {L : Subgroup G} {s : G} (h : InnerOn L s) :
    ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G), s = l * c := by
  classical
  let C : Subgroup G := centralizer (L : Set G)
  have hmem : s ∈ L ⊔ C := h
  have hmain : ∀ x ∈ (L ⊔ C : Subgroup G), ∃ l ∈ L, ∃ c ∈ C, x = l * c := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ l ∈ L, ∃ c ∈ C, x = l * c)
      ?_ ?_ ?_ ?_ hx
    · rintro y (hy | hy)
      · exact ⟨y, hy, 1, C.one_mem, by simp⟩
      · exact ⟨1, L.one_mem, y, hy, by simp⟩
    · exact ⟨1, L.one_mem, 1, C.one_mem, by simp⟩
    · rintro y z _ _ ⟨l₁, hl₁, c₁, hc₁, rfl⟩ ⟨l₂, hl₂, c₂, hc₂, rfl⟩
      refine ⟨l₁ * l₂, L.mul_mem hl₁ hl₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
      have hcomm : c₁ * l₂ = l₂ * c₁ := (Subgroup.mem_centralizer_iff.mp hc₁ l₂ hl₂).symm
      calc (l₁ * c₁) * (l₂ * c₂) = l₁ * (c₁ * l₂) * c₂ := by group
        _ = l₁ * (l₂ * c₁) * c₂ := by rw [hcomm]
        _ = (l₁ * l₂) * (c₁ * c₂) := by group
    · rintro y _ ⟨l, hl, c, hc, rfl⟩
      refine ⟨l⁻¹, L.inv_mem hl, c⁻¹, C.inv_mem hc, ?_⟩
      have hcomm : c * l = l * c := (Subgroup.mem_centralizer_iff.mp hc l hl).symm
      rw [mul_inv_rev, ← mul_inv_rev c l, hcomm, mul_inv_rev]
  exact hmain s hmem

theorem eq_one_or_eq_of_commute [Finite G] {L : Subgroup G}
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic P)
    {a b : G} (ha : a ∈ centralizer (L : Set G)) (hb : b ∈ centralizer (L : Set G))
    (ha2 : a * a = 1) (hb2 : orderOf b = 2) (hab : a * b = b * a) : a = 1 ∨ a = b := by
  classical
  let C : Subgroup G := centralizer (L : Set G)
  have hcyc' : ∀ P : Sylow 2 ↥C, IsCyclic (P : Subgroup ↥C) := by
    intro P
    haveI : IsCyclic ↥((P : Subgroup ↥C).map C.subtype) := hcyc _ (isSylow2Of_map_sylow P)
    exact isCyclic_of_injective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥C) C.subtype C.subtype_injective).toMonoidHom
      (Subgroup.equivMapOfInjective (P : Subgroup ↥C) C.subtype C.subtype_injective).injective
  by_cases h1 : a = 1
  · exact Or.inl h1
  refine Or.inr ?_
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha2)
  have ha' : orderOf a = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) h1
    · exact h
  have h : (⟨a, ha⟩ : ↥C) = (⟨b, hb⟩ : ↥C) :=
    eq_of_commuting_involutions_of_cyclic_sylow hcyc'
      (by rw [Subgroup.orderOf_mk]; exact ha') (by rw [Subgroup.orderOf_mk]; exact hb2)
      (Subtype.ext hab)
  exact congrArg Subtype.val h

end CFSG.OddStandard.SmallF3.Omega

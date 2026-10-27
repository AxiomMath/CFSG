module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SpecialSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.SylowTransfer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5SylowConj

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.RankThree.Native

structure HSStdQ (T₀ : Subgroup ↥hs100P) (z₀ : ↥hs100P) : Prop where
  pgroup : IsPGroup 2 T₀
  index : ¬ 2 ∣ T₀.index
  mem : z₀ ∈ T₀
  ne_one : z₀ ≠ 1
  sq : z₀ * z₀ = 1
  comm : ∀ x ∈ T₀, z₀ * x = x * z₀
  special : ∃ E : Subgroup ↥hs100P, IsSpecialElem z₀ E
  core : ∀ F₁ F₂ : Subgroup ↥hs100P, F₁ ≤ T₀ → F₂ ≤ T₀ → IsElemAbelian 2 F₁ → IsElemAbelian 2 F₂ →
    Nat.card F₁ = 16 → Nat.card F₂ = 16 → z₀ ∈ F₁ → z₀ ∈ F₂ →
    (∀ e ∈ F₁, e ≠ 1 → ∃ a : ↥hs100P, a * z₀ * a⁻¹ = e) →
    (∀ e ∈ F₂, e ≠ 1 → ∃ a : ↥hs100P, a * z₀ * a⁻¹ = e) →
    ∃ t ∈ T₀, F₁.map (MulAut.conj t).toMonoidHom = F₂

theorem map_conj_subtype (F : Subgroup ↥hs100P) (t : ↥hs100P) :
    (F.map (MulAut.conj t).toMonoidHom).map hs100P.subtype =
      (F.map hs100P.subtype).map (MulAut.conj (t : Equiv.Perm (Fin 100))).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem zas_std_Q_explicit :
    ∃ (T₀ : Subgroup ↥hs100P) (hz : zasZ0 ∈ hs100P), HSStdQ T₀ ⟨zasZ0, hz⟩ := by
  classical
  obtain ⟨hTP, hTcard, hzT, hz2, hz1, hcomm⟩ := zas_sylow_spec
  obtain ⟨E, hE⟩ := zas_special_spec
  have hzP : zasZ0 ∈ hs100P := hTP hzT
  have hcardP := card_hs100P
  refine ⟨zasT0.subgroupOf hs100P, hzP, ?_⟩
  have hcardT : Nat.card (zasT0.subgroupOf hs100P) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv, hTcard]
  have hidx : (zasT0.subgroupOf hs100P).index = 86625 := by
    have h := Subgroup.index_mul_card (zasT0.subgroupOf hs100P)
    rw [hcardT, hcardP] at h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 512) (h.trans (by norm_num))
  refine ⟨IsPGroup.of_card (n := 9) (by rw [hcardT]; norm_num), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hidx]
    norm_num
  · exact hzT
  · intro h
    exact hz1 (congrArg Subtype.val h)
  · exact Subtype.ext hz2
  · intro x hx
    exact Subtype.ext (hcomm x.1 hx)
  · refine ⟨E.subgroupOf hs100P, ?_⟩
    exact (isSpecialIn_iff hzP hE.1).1 hE
  · intro F₁ F₂ hF₁ hF₂ hab₁ hab₂ hc₁ hc₂ hz₁ hz₂ hcj₁ hcj₂
    have key : ∀ F : Subgroup ↥hs100P, F ≤ zasT0.subgroupOf hs100P → IsElemAbelian 2 F →
        Nat.card F = 16 → (⟨zasZ0, hzP⟩ : ↥hs100P) ∈ F →
        (∀ e ∈ F, e ≠ 1 → ∃ a : ↥hs100P, a * ⟨zasZ0, hzP⟩ * a⁻¹ = e) →
        F.map hs100P.subtype ≤ zasT0 ∧ IsElemAbelian 2 (F.map hs100P.subtype) ∧
          Nat.card (F.map hs100P.subtype) = 16 ∧ zasZ0 ∈ F.map hs100P.subtype ∧
          (∀ e ∈ F.map hs100P.subtype, e ≠ 1 →
            ∃ a : Equiv.Perm (Fin 100), a * zasZ0 * a⁻¹ = e) := by
      intro F hF hab hc hz hcj
      refine ⟨?_, isElemAbelian_map _ hs100P.subtype_injective hab, ?_, ⟨⟨zasZ0, hzP⟩, hz, rfl⟩, ?_⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact hF hx
      · rw [Subgroup.card_map_of_injective hs100P.subtype_injective, hc]
      · rintro _ ⟨e, he, rfl⟩ hne
        obtain ⟨a, ha⟩ := hcj e he (fun h => hne (by rw [h]; rfl))
        exact ⟨(a : Equiv.Perm (Fin 100)), congrArg Subtype.val ha⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := key F₁ hF₁ hab₁ hc₁ hz₁ hcj₁
    obtain ⟨h1', h2', h3', h4', h5'⟩ := key F₂ hF₂ hab₂ hc₂ hz₂ hcj₂
    obtain ⟨t, ht, hteq⟩ := zas_uniq_spec _ _ h1 h1' h2 h2' h3 h3' h4 h4' h5 h5'
    have htP : t ∈ hs100P := hTP ht
    refine ⟨⟨t, htP⟩, ht, ?_⟩
    apply Subgroup.map_injective hs100P.subtype_injective
    rw [map_conj_subtype]
    exact hteq

theorem zas_std_Q :
    ∃ (T₀ : Subgroup ↥hs100P) (z₀ : ↥hs100P), HSStdQ T₀ z₀ := by
  obtain ⟨T₀, hz, h⟩ := zas_std_Q_explicit
  exact ⟨T₀, _, h⟩

section Transport

theorem centralizer_map_equiv {M N : Type*} [Group M] [Group N] (σ : M ≃* N) (T : Subgroup M)
    (z : M) (h : centralizer (T : Set M) = zpowers z) :
    centralizer ((T.map σ.toMonoidHom : Subgroup N) : Set N) = zpowers (σ z) := by
  ext x
  obtain ⟨y, rfl⟩ := σ.surjective x
  rw [mem_centralizer_iff]
  have h1 : (∀ h' ∈ (T.map σ.toMonoidHom : Subgroup N), h' * σ y = σ y * h') ↔
      y ∈ centralizer (T : Set M) := by
    rw [mem_centralizer_iff]
    constructor
    · intro hh t ht
      have := hh (σ t) ⟨t, ht, rfl⟩
      exact σ.injective (by simpa using this)
    · rintro hh _ ⟨t, ht, rfl⟩
      simpa using congrArg σ (hh t ht)
  have h2 : σ y ∈ zpowers (σ z) ↔ y ∈ zpowers z := by
    rw [mem_zpowers_iff, mem_zpowers_iff]
    refine exists_congr fun k => ?_
    rw [← map_zpow]
    exact σ.injective.eq_iff
  rw [h2, ← h]
  exact h1

@[expose] def AdmZ {M : Type*} [Group M] (z : M) (F : Subgroup M) : Prop :=
  IsElemAbelian 2 F ∧ Nat.card F = 16 ∧ z ∈ F ∧ ∀ e ∈ F, e ≠ 1 → ∃ a : M, a * z * a⁻¹ = e

theorem AdmZ.map {M N : Type*} [Group M] [Group N] (f : M ≃* N) {z : M} {F : Subgroup M}
    (h : AdmZ z F) : AdmZ (f z) (F.map f.toMonoidHom) := by
  obtain ⟨hab, hc, hz, hcj⟩ := h
  refine ⟨isElemAbelian_map _ f.injective hab, ?_, ⟨z, hz, rfl⟩, ?_⟩
  · rw [Subgroup.card_map_of_injective f.injective, hc]
  · rintro _ ⟨e, he, rfl⟩ hne
    obtain ⟨a, ha⟩ := hcj e he (fun h1 => hne (by rw [h1]; exact map_one f))
    exact ⟨f a, by simpa using congrArg f ha⟩

theorem AdmZ.isPGroup_le {M : Type*} [Group M] {z : M} {F : Subgroup M} (h : AdmZ z F) :
    IsPGroup 2 F ∧ F ≤ centralizer ({z} : Set M) := by
  obtain ⟨hab, hc, hz, -⟩ := h
  refine ⟨IsPGroup.of_card (n := 4) (by rw [hc]; norm_num), fun x hx => ?_⟩
  rw [mem_centralizer_singleton_iff]
  have := hab.1
  rw [isMulCommutative_iff_of_setLike] at this
  exact (this z hz x hx).symm

theorem AdmZ.conj {M : Type*} [Group M] {z : M} {F : Subgroup M} {c : M}
    (hc : c ∈ centralizer ({z} : Set M)) (h : AdmZ z F) :
    AdmZ z (F.map (MulAut.conj c).toMonoidHom) := by
  have hcz : (MulAut.conj c) z = z := by
    rw [mem_centralizer_singleton_iff] at hc
    simp [MulAut.conj_apply, hc]
  have := AdmZ.map (MulAut.conj c) h
  rwa [hcz] at this

theorem map_conj_equiv {M N : Type*} [Group M] [Group N] (f : M ≃* N) (F : Subgroup M) (c : N) :
    (F.map (MulAut.conj (f.symm c)).toMonoidHom).map f.toMonoidHom =
      (F.map f.toMonoidHom).map (MulAut.conj c).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

variable {T₀ : Subgroup ↥hs100P} {z₀ : ↥hs100P}

theorem exists_equiv_std (hstd : HSStdQ T₀ z₀) {M : Type*} [Group M] (σ : M ≃* ↥hs100P)
    {T : Subgroup M} {z : M} (hT : IsPGroup 2 T) (hTi : ¬ 2 ∣ T.index) (hz2 : orderOf z = 2)
    (hcent : centralizer (T : Set M) = zpowers z) :
    ∃ σ' : M ≃* ↥hs100P, T.map σ'.toMonoidHom = T₀ ∧ σ' z = z₀ := by
  have hSw : IsPGroup 2 (T.map σ.toMonoidHom) :=
    IsPGroup.of_injective hT (MulEquiv.subgroupMap σ T).symm.toMonoidHom
      (MulEquiv.subgroupMap σ T).symm.injective
  have hSwi : ¬ 2 ∣ (T.map σ.toMonoidHom).index := by
    have h : (T.map σ.toMonoidHom).index = T.index := Subgroup.index_map_equiv T σ
    rwa [h]
  have hzw2 : orderOf (σ z) = 2 := by
    exact (orderOf_injective σ.toMonoidHom σ.injective z).trans hz2
  have hcentQ : centralizer (((T.map σ.toMonoidHom : Subgroup ↥hs100P) ⊓ ⊤ : Subgroup ↥hs100P) :
      Set ↥hs100P) ⊓ ⊤ = zpowers (σ z) := by
    simp only [inf_top_eq]
    exact centralizer_map_equiv σ T z hcent
  obtain ⟨g, hg1, hg2⟩ := exists_conj_of_one_sylow (⊤ : Subgroup ↥hs100P) T₀ hstd.pgroup
    hstd.index z₀ (mem_top _) hstd.ne_one (fun x hx => hstd.comm x hx.1)
    (T.map σ.toMonoidHom) hSw hSwi (σ z) hzw2 hcentQ
  refine ⟨σ.trans (MulAut.conj g⁻¹), ?_, ?_⟩
  · ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulEquiv.coe_trans, Function.comp_apply,
      MulAut.conj_apply, inv_inv]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hg1 (σ x)).1 ⟨x, hx, rfl⟩
    · intro hy
      have : g * y * g⁻¹ ∈ T.map σ.toMonoidHom := by
        rw [hg1]
        simpa [mul_assoc] using hy
      obtain ⟨x, hx, hxe⟩ := this
      refine ⟨x, hx, ?_⟩
      have hxe' : σ x = g * y * g⁻¹ := hxe
      rw [hxe']
      group
  · show g⁻¹ * σ z * g⁻¹⁻¹ = z₀
    rw [← hg2]
    group

theorem exists_special_internal
    {M : Type*} [Group M] (σ : M ≃* ↥hs100P) {T : Subgroup M} {z : M} (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hz2 : orderOf z = 2) (hcent : centralizer (T : Set M) = zpowers z) :
    ∃ E : Subgroup M, IsSpecialElem z E := by
  obtain ⟨T₀, z₀, hstd⟩ := zas_std_Q
  obtain ⟨σ', -, hz⟩ := exists_equiv_std hstd σ hT hTi hz2 hcent
  obtain ⟨E, hE⟩ := hstd.special
  refine ⟨E.map σ'.symm.toMonoidHom, ?_⟩
  have h := hE.map σ'.symm
  have e : σ'.symm z₀ = z := by rw [← hz]; simp
  rwa [e] at h

theorem uniq_internal_of_std (hstd : HSStdQ T₀ z₀)
    {M : Type*} [Group M] (σ : M ≃* ↥hs100P) {T : Subgroup M} {z : M} (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hz2 : orderOf z = 2) (hcent : centralizer (T : Set M) = zpowers z)
    {F₁ F₂ : Subgroup M} (h₁ : AdmZ z F₁) (h₂ : AdmZ z F₂) :
    ∃ c ∈ centralizer ({z} : Set M), F₁.map (MulAut.conj c).toMonoidHom = F₂ := by
  obtain ⟨σ', -, hz⟩ := exists_equiv_std hstd σ hT hTi hz2 hcent
  have a₁ : AdmZ z₀ (F₁.map σ'.toMonoidHom) := hz ▸ h₁.map σ'
  have a₂ : AdmZ z₀ (F₂.map σ'.toMonoidHom) := hz ▸ h₂.map σ'
  obtain ⟨c, hc, hceq⟩ := exists_conj_of_core hstd.pgroup hstd.index hstd.comm
    (Adm := AdmZ z₀) (fun F h => h.isPGroup_le) (fun F c hc h => h.conj hc)
    (fun F₁ F₂ f₁ f₂ b₁ b₂ => hstd.core F₁ F₂ f₁ f₂ b₁.1 b₂.1 b₁.2.1 b₂.2.1 b₁.2.2.1 b₂.2.2.1
      b₁.2.2.2 b₂.2.2.2) a₁ a₂
  refine ⟨σ'.symm c, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff] at hc ⊢
    have := congrArg σ'.symm hc
    rw [map_mul, map_mul, ← hz] at this
    simpa using this
  · apply Subgroup.map_injective (f := σ'.toMonoidHom) σ'.injective
    rw [map_conj_equiv]
    exact hceq

theorem uniq_internal
    {M : Type*} [Group M] (σ : M ≃* ↥hs100P) {T : Subgroup M} {z : M} (hT : IsPGroup 2 T)
    (hTi : ¬ 2 ∣ T.index) (hz2 : orderOf z = 2) (hcent : centralizer (T : Set M) = zpowers z)
    {F₁ F₂ : Subgroup M} (h₁ : AdmZ z F₁) (h₂ : AdmZ z F₂) :
    ∃ c ∈ centralizer ({z} : Set M), F₁.map (MulAut.conj c).toMonoidHom = F₂ := by
  obtain ⟨T₀, z₀, hstd⟩ := zas_std_Q
  exact uniq_internal_of_std hstd σ hT hTi hz2 hcent h₁ h₂

end Transport

section Ambient

variable {G : Type} [Group G] {L S : Subgroup G} {z : G}

theorem internal_hyps (hS : IsPGroup 2 S) (hSL : ¬ 2 ∣ (S ⊓ L).relIndex L) (hz : z ∈ S ⊓ L)
    (hz2 : orderOf z = 2)
    (hcent : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z) :
    IsPGroup 2 ((S ⊓ L).subgroupOf L) ∧ ¬ 2 ∣ ((S ⊓ L).subgroupOf L).index ∧
      orderOf (⟨z, hz.2⟩ : ↥L) = 2 ∧
      centralizer (((S ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) = zpowers (⟨z, hz.2⟩ : ↥L) := by
  refine ⟨?_, hSL, ?_, ?_⟩
  · exact IsPGroup.of_injective (hS.to_le inf_le_left)
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ L ≤ L)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : S ⊓ L ≤ L)).injective
  · rw [Subgroup.orderOf_mk]
    exact hz2
  · ext x
    rw [mem_centralizer_iff]
    constructor
    · intro hh
      have hx : (x : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L := by
        refine ⟨mem_centralizer_iff.2 fun t ht => ?_, x.2⟩
        have := hh ⟨t, ht.2⟩ (mem_subgroupOf.2 ht)
        exact congrArg Subtype.val this
      rw [hcent] at hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
      exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
      have hx' : (x : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L := by
        rw [hcent]
        exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
      intro h hh
      have := mem_centralizer_iff.1 hx'.1 (h : G) (mem_subgroupOf.1 hh)
      exact Subtype.ext this


theorem exists_special_of_sylow (hL : IsSporadic L .HS) (hS : IsPGroup 2 S)
    (hSL : ¬ 2 ∣ (S ⊓ L).relIndex L) (hz : z ∈ S ⊓ L) (hz2 : orderOf z = 2)
    (hcent : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z) :
    ∃ E : Subgroup G, E ≤ L ∧ z ∈ E ∧ IsElemAbelian 2 E ∧ Nat.card E = 16 ∧
      (∃ φ : ↥(normalizer (E : Set G) ⊓ L) →* Equiv.Perm (Fin 6), Function.Surjective φ ∧
        φ.ker = E.subgroupOf (normalizer (E : Set G) ⊓ L)) ∧
      ∀ e ∈ E, e ≠ 1 → ∃ a ∈ normalizer (E : Set G) ⊓ L, a * z * a⁻¹ = e := by
  obtain ⟨e₀⟩ := hL
  let σ : ↥L ≃* ↥hs100P := (e₀ : ↥L ≃* NativeSporadic.HS).trans hs100Equiv
  obtain ⟨hp, hi, ho, hc⟩ := internal_hyps hS hSL hz hz2 hcent
  obtain ⟨E, hE⟩ := exists_special_internal σ hp hi ho hc
  exact ⟨E.map L.subtype, (hE.isSpecialIn (G := G)).1, (hE.isSpecialIn (G := G)).2.1,
    (hE.isSpecialIn (G := G)).2.2.1, (hE.isSpecialIn (G := G)).2.2.2.1,
    (hE.isSpecialIn (G := G)).2.2.2.2.1, (hE.isSpecialIn (G := G)).2.2.2.2.2⟩

theorem special_unique_of_sylow (hL : IsSporadic L .HS) (hS : IsPGroup 2 S)
    (hSL : ¬ 2 ∣ (S ⊓ L).relIndex L) (hz : z ∈ S ⊓ L) (hz2 : orderOf z = 2)
    (hcent : centralizer ((S ⊓ L : Subgroup G) : Set G) ⊓ L = zpowers z)
    {F₁ F₂ : Subgroup G} (h₁ : F₁ ≤ L) (h₂ : F₂ ≤ L) (hab₁ : IsElemAbelian 2 F₁)
    (hab₂ : IsElemAbelian 2 F₂) (hc₁ : Nat.card F₁ = 16) (hc₂ : Nat.card F₂ = 16)
    (hz₁ : z ∈ F₁) (hz₂ : z ∈ F₂) (hcj₁ : ∀ e ∈ F₁, e ≠ 1 → ∃ a ∈ L, a * z * a⁻¹ = e)
    (hcj₂ : ∀ e ∈ F₂, e ≠ 1 → ∃ a ∈ L, a * z * a⁻¹ = e) :
    ∃ c ∈ L ⊓ centralizer ({z} : Set G), F₁.map (MulAut.conj c : G →* G) = F₂ := by
  obtain ⟨e₀⟩ := hL
  let σ : ↥L ≃* ↥hs100P := (e₀ : ↥L ≃* NativeSporadic.HS).trans hs100Equiv
  obtain ⟨hp, hi, ho, hc⟩ := internal_hyps hS hSL hz hz2 hcent
  exact uniq_ambient_of_internal hz.2
    (fun F₁ F₂ a b c d e f g h => uniq_internal σ hp hi ho hc ⟨a, c, e, g⟩ ⟨b, d, f, h⟩)
    h₁ h₂ hab₁ hab₂ hc₁ hc₂ hz₁ hz₂ hcj₁ hcj₂

end Ambient

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus

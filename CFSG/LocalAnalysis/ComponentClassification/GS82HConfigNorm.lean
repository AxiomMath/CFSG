module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.GSThmB.HConfig

open CFSG Subgroup

variable {G : Type} [Group G]

abbrev cj (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

theorem mem_cj {g x : G} {K : Subgroup G} : x ∈ cj g K ↔ g⁻¹ * x * g ∈ K := by
  rw [cj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_cj {g x : G} {K : Subgroup G} (hx : x ∈ K) : g * x * g⁻¹ ∈ cj g K :=
  ⟨x, hx, rfl⟩

theorem cj_one (K : Subgroup G) : cj 1 K = K := by
  ext x
  rw [mem_cj, inv_one, one_mul, mul_one]

theorem cj_mul (g h : G) (K : Subgroup G) : cj (g * h) K = cj g (cj h K) := by
  ext x
  rw [mem_cj, mem_cj, mem_cj, mul_inv_rev]
  simp only [mul_assoc]

theorem cj_eq_self_iff {g : G} {K : Subgroup G} : cj g K = K ↔ g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  constructor
  · intro h k
    conv_rhs => rw [← h]
    rw [mem_cj]
    have e : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    rw [e]
  · intro h
    ext x
    rw [mem_cj, h (g⁻¹ * x * g)]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]

theorem cj_le_cj_iff {g : G} {K L : Subgroup G} : cj g K ≤ cj g L ↔ K ≤ L := by
  constructor
  · intro h x hx
    have h1 := h (conj_mem_cj (g := g) hx)
    rw [mem_cj] at h1
    convert h1 using 1
    group
  · exact fun h => map_mono h

theorem isComponent_cj [Finite G] {K : Subgroup G} (hK : IsComponent K) (g : G) :
    IsComponent (cj g K) :=
  ⟨LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective _ (MulAut.conj g).injective) hK.1,
    hK.2.map (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective⟩

theorem commute_of_commutator_eq_bot {A A' : Subgroup G} (h : ⁅A, A'⁆ = ⊥) {a a' : G}
    (ha : a ∈ A) (ha' : a' ∈ A') : Commute a a' :=
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h ha) a' ha').symm

theorem commute_of_isComponent [Finite G] {A A' : Subgroup G} (hA : IsComponent A)
    (hA' : IsComponent A') (hne : A ≠ A') {a a' : G} (ha : a ∈ A) (ha' : a' ∈ A') :
    Commute a a' :=
  commute_of_commutator_eq_bot ((LocalCores.distinct_components_commute hA hA').resolve_left hne)
    ha ha'

abbrev stab (B K : Subgroup G) : Subgroup G := B ⊓ normalizer (K : Set G)

abbrev Orb (B K : Subgroup G) : Type := ↥B ⧸ (stab B K).subgroupOf B

abbrev orbOne (B K : Subgroup G) : Orb B K := QuotientGroup.mk (1 : ↥B)

@[expose] noncomputable def rep {B K : Subgroup G} (q : Orb B K) : G := ((Quotient.out q : ↥B) : G)

theorem rep_mem {B K : Subgroup G} (q : Orb B K) : rep q ∈ B := (Quotient.out q : ↥B).2

theorem mk_rep {B K : Subgroup G} (q : Orb B K) :
    (QuotientGroup.mk (⟨rep q, rep_mem q⟩ : ↥B) : Orb B K) = q :=
  QuotientGroup.out_eq' q

theorem mk_eq_mk_iff {B K : Subgroup G} {b b' : ↥B} :
    (QuotientGroup.mk b : Orb B K) = QuotientGroup.mk b' ↔ cj (b : G) K = cj (b' : G) K := by
  rw [QuotientGroup.eq, mem_subgroupOf]
  constructor
  · intro h
    have h1 : cj ((b : G)⁻¹ * b') K = K := cj_eq_self_iff.mpr (mem_inf.mp h).2
    calc cj (b : G) K = cj (b : G) (cj ((b : G)⁻¹ * b') K) := by rw [h1]
      _ = cj (b' : G) K := by rw [← cj_mul, mul_inv_cancel_left]
  · intro h
    refine mem_inf.mpr ⟨(b⁻¹ * b').2, ?_⟩
    rw [coe_mul, coe_inv, ← cj_eq_self_iff, cj_mul, ← h, ← cj_mul, inv_mul_cancel, cj_one]

theorem cj_rep_eq_self_iff {B K : Subgroup G} (q : Orb B K) :
    cj (rep q) K = K ↔ q = orbOne B K := by
  conv_rhs => rw [← mk_rep q]
  rw [orbOne, mk_eq_mk_iff, coe_one, cj_one]

theorem cj_rep_injective {B K : Subgroup G} {q q' : Orb B K} (h : cj (rep q) K = cj (rep q') K) :
    q = q' := by
  rw [← mk_rep q, ← mk_rep q', mk_eq_mk_iff]
  exact h

theorem conj_eq_of_mk_eq {B K : Subgroup G} {b b' : ↥B}
    (h : (QuotientGroup.mk b : Orb B K) = QuotientGroup.mk b') {x : G}
    (hx : x ∈ centralizer (stab B K : Set G)) :
    (b : G) * x * (b : G)⁻¹ = (b' : G) * x * (b' : G)⁻¹ := by
  rw [QuotientGroup.eq, mem_subgroupOf] at h
  have hb' : (b' : G) = (b : G) * ((b⁻¹ * b' : ↥B) : G) := by
    rw [coe_mul, coe_inv, mul_inv_cancel_left]
  have h1 : ((b⁻¹ * b' : ↥B) : G) * x * ((b⁻¹ * b' : ↥B) : G)⁻¹ = x := by
    rw [mem_centralizer_iff.mp hx _ h, mul_inv_cancel_right]
  symm
  calc (b' : G) * x * (b' : G)⁻¹ =
        b * (((b⁻¹ * b' : ↥B) : G) * x * ((b⁻¹ * b' : ↥B) : G)⁻¹) * (b : G)⁻¹ := by
          rw [hb']
          group
    _ = (b : G) * x * (b : G)⁻¹ := by rw [h1]

@[expose] def orbRest (B K : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B) (_ : cj b K ≠ K), cj b K

@[expose] def orbJoin (B K : Subgroup G) : Subgroup G :=
  ⨆ (b : G) (_ : b ∈ B), cj b K

theorem cj_le_orbRest {B K : Subgroup G} {b : G} (hb : b ∈ B) (hne : cj b K ≠ K) :
    cj b K ≤ orbRest B K :=
  le_iSup₂_of_le b hb (le_iSup_of_le hne le_rfl)

theorem cj_le_orbJoin {B K : Subgroup G} {b : G} (hb : b ∈ B) : cj b K ≤ orbJoin B K :=
  le_iSup₂_of_le b hb le_rfl

theorem le_orbJoin (B K : Subgroup G) : K ≤ orbJoin B K := by
  have h := cj_le_orbJoin (B := B) (K := K) (one_mem B)
  rwa [cj_one] at h

theorem orbRest_le_orbJoin (B K : Subgroup G) : orbRest B K ≤ orbJoin B K :=
  iSup₂_le fun _ hb => iSup_le fun _ => cj_le_orbJoin hb

theorem orbJoin_eq_sup (B K : Subgroup G) : orbJoin B K = K ⊔ orbRest B K := by
  refine le_antisymm (iSup₂_le fun b hb => ?_) (sup_le (le_orbJoin B K) (orbRest_le_orbJoin B K))
  by_cases h : cj b K = K
  · rw [h]
    exact le_sup_left
  · exact (cj_le_orbRest hb h).trans le_sup_right

theorem orbRest_le_centralizer [Finite G] {B K : Subgroup G} (hK : IsComponent K) :
    orbRest B K ≤ centralizer (K : Set G) :=
  iSup₂_le fun b _ => iSup_le fun hne => fun x hx => mem_centralizer_iff.mpr fun k hk =>
    (commute_of_isComponent hK (isComponent_cj hK b) (Ne.symm hne) hk hx)

theorem stab_le_normalizer_orbRest [Finite G] {B K : Subgroup G} :
    stab B K ≤ normalizer (orbRest B K : Set G) := by
  have key : ∀ r ∈ stab B K, cj r (orbRest B K) ≤ orbRest B K := by
    intro r hr
    rw [Subgroup.map_le_iff_le_comap]
    unfold orbRest
    refine iSup₂_le fun b hb => iSup_le fun hne => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    change cj r (cj b K) ≤ _
    rw [← cj_mul]
    refine cj_le_orbRest (mul_mem (mem_inf.mp hr).1 hb) fun h => hne ?_
    rw [cj_mul] at h
    have hr' : cj r K = K := cj_eq_self_iff.mpr (mem_inf.mp hr).2
    calc cj b K = cj r⁻¹ (cj r (cj b K)) := by rw [← cj_mul, inv_mul_cancel, cj_one]
      _ = cj r⁻¹ K := by rw [h]
      _ = cj r⁻¹ (cj r K) := by rw [hr']
      _ = K := by rw [← cj_mul, inv_mul_cancel, cj_one]
  intro r hr
  rw [← cj_eq_self_iff]
  refine le_antisymm (key r hr) ?_
  have h := key r⁻¹ (inv_mem hr)
  rw [← cj_le_cj_iff (g := r), ← cj_mul, mul_inv_cancel, cj_one] at h
  exact h

@[expose] noncomputable def normPart (B K : Subgroup G) (q : Orb B K) :
    ↥(K ⊓ centralizer (stab B K : Set G)) →* G :=
  (MulAut.conj (rep q)).toMonoidHom.comp (Subgroup.subtype _)

theorem normPart_apply (B K : Subgroup G) (q : Orb B K)
    (x : ↥(K ⊓ centralizer (stab B K : Set G))) :
    normPart B K q x = rep q * x * (rep q)⁻¹ := rfl

theorem normPart_mem (B K : Subgroup G) (q : Orb B K) (x : ↥(K ⊓ centralizer (stab B K : Set G))) :
    normPart B K q x ∈ cj (rep q) K :=
  conj_mem_cj (mem_inf.mp x.2).1

theorem normPart_commute [Finite G] {B K : Subgroup G} (hK : IsComponent K) :
    Pairwise fun q q' : Orb B K => ∀ x y, Commute (normPart B K q x) (normPart B K q' y) :=
  fun q q' hqq' x y => commute_of_isComponent (isComponent_cj hK _) (isComponent_cj hK _)
    (fun h => hqq' (cj_rep_injective h)) (normPart_mem B K q x) (normPart_mem B K q' y)

@[expose] noncomputable def normMap [Finite G] (B K : Subgroup G) (hK : IsComponent K)
    [Fintype (Orb B K)] :
    ↥(K ⊓ centralizer (stab B K : Set G)) →* G :=
  (MonoidHom.noncommPiCoprod (normPart B K) (normPart_commute hK)).comp
    (MonoidHom.pi fun _ => MonoidHom.id _)

variable [Finite G] {B K : Subgroup G} (hK : IsComponent K) [Fintype (Orb B K)]

include hK in
theorem normPart_pairwise (x : ↥(K ⊓ centralizer (stab B K : Set G))) :
    ((Finset.univ : Finset (Orb B K)) : Set (Orb B K)).Pairwise
      (Function.onFun Commute fun q => normPart B K q x) :=
  fun _ _ _ _ h => normPart_commute hK h x x

theorem normMap_apply (x : ↥(K ⊓ centralizer (stab B K : Set G))) :
    normMap B K hK x = Finset.univ.noncommProd (fun q => normPart B K q x)
      (normPart_pairwise hK x) := by
  rw [normMap, MonoidHom.comp_apply, MonoidHom.noncommPiCoprod_apply]
  rfl

include hK in
theorem rep_one_mem_stab : rep (orbOne B K) ∈ stab B K := by
  have h := (cj_rep_eq_self_iff (orbOne B K)).mpr rfl
  exact mem_inf.mpr ⟨rep_mem _, cj_eq_self_iff.mp h⟩

theorem noncommProd_univ_comp_equiv {ι β : Type*} [Fintype ι] [Monoid β] (e : ι ≃ ι)
    (f : ι → β) (comm : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute f))
    (comm' : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute (f ∘ e))) :
    Finset.univ.noncommProd (f ∘ e) comm' = Finset.univ.noncommProd f comm := by
  unfold Finset.noncommProd
  have h : Multiset.map (f ∘ e) Finset.univ.val = Multiset.map f Finset.univ.val := by
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  have key : ∀ (m₁ m₂ : Multiset β) (h₁ h₂), m₁ = m₂ →
      Multiset.noncommProd m₁ h₁ = Multiset.noncommProd m₂ h₂ := by
    rintro _ _ _ _ rfl
    rfl
  exact key _ _ _ _ h

theorem normMap_mem_centralizer (x : ↥(K ⊓ centralizer (stab B K : Set G))) :
    normMap B K hK x ∈ centralizer (B : Set G) := by
  rw [mem_centralizer_iff]
  intro c hc
  suffices h : c * normMap B K hK x * c⁻¹ = normMap B K hK x by
    calc c * normMap B K hK x = c * normMap B K hK x * c⁻¹ * c := by group
      _ = normMap B K hK x * c := by rw [h]
  have hconj : c * normMap B K hK x * c⁻¹ = MulAut.conj c (normMap B K hK x) := rfl
  rw [hconj, normMap_apply, Finset.map_noncommProd]
  let e : Orb B K ≃ Orb B K := MulAction.toPerm (⟨c, hc⟩ : ↥B)
  have hpt : ∀ q : Orb B K, MulAut.conj c (normPart B K q x) = normPart B K (e q) x := by
    intro q
    rw [MulAut.conj_apply, normPart_apply, normPart_apply]
    have h1 : e q = QuotientGroup.mk ((⟨c, hc⟩ : ↥B) * Quotient.out q) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have h2 := conj_eq_of_mk_eq (B := B) (K := K) (b := (⟨c, hc⟩ : ↥B) * Quotient.out q)
      (b' := Quotient.out (e q)) (by rw [← h1, QuotientGroup.out_eq']) (mem_inf.mp x.2).2
    rw [rep, rep, ← h2, coe_mul, mul_inv_rev]
    simp only [mul_assoc]
  simp_rw [hpt]
  exact noncommProd_univ_comp_equiv e (fun q => normPart B K q x) _ _

theorem inv_mul_normMap_mem (x : ↥(K ⊓ centralizer (stab B K : Set G))) :
    (x : G)⁻¹ * normMap B K hK x ∈ orbRest B K := by
  classical
  rw [normMap_apply, ← Finset.mul_noncommProd_erase _ (Finset.mem_univ (orbOne B K))]
  have h1 : normPart B K (orbOne B K) x = x := by
    rw [normPart_apply]
    have := mem_centralizer_iff.mp (mem_inf.mp x.2).2 _ (rep_one_mem_stab hK)
    rw [this, mul_inv_cancel_right]
  rw [h1, inv_mul_cancel_left]
  refine Subgroup.noncommProd_mem _ _ fun q hq => ?_
  have hq1 : q ≠ orbOne B K := Finset.ne_of_mem_erase hq
  exact cj_le_orbRest (rep_mem q) (fun h => hq1 ((cj_rep_eq_self_iff q).mp h))
    (normPart_mem B K q x)

theorem normMap_mem_orbJoin (x : ↥(K ⊓ centralizer (stab B K : Set G))) :
    normMap B K hK x ∈ orbJoin B K := by
  have h := inv_mul_normMap_mem hK x
  have h2 : normMap B K hK x = (x : G) * ((x : G)⁻¹ * normMap B K hK x) := by group
  rw [h2]
  exact mul_mem (le_orbJoin B K (mem_inf.mp x.2).1) (orbRest_le_orbJoin B K h)

theorem mem_orbRest_of_normMap_eq_one {x : ↥(K ⊓ centralizer (stab B K : Set G))}
    (h : normMap B K hK x = 1) : (x : G) ∈ orbRest B K := by
  have h1 := inv_mem (inv_mul_normMap_mem hK x)
  rwa [h, mul_one, inv_inv] at h1

end CFSG.ComponentClassification.GSThmB.HConfig

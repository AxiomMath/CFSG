module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach

public section

namespace CFSG.ComponentClassification.GSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

theorem map_pPrimeCore_le_of_sup_eq {B L : Subgroup G}
    (hB : B ⊔ (pPrimeCore 2 L).map L.subtype = L) :
    (pPrimeCore 2 B).map B.subtype ≤ (pPrimeCore 2 L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_map_pPrimeCore_of_sup_eq hB (map_subtype_le _) ?_ ?_
  · exact le_normalizer.trans
      (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic B (pPrimeCore 2 B))
  · rw [card_map_of_injective B.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem sup_pPrimeCore_trans {A B L : Subgroup G}
    (hB : B ⊔ (pPrimeCore 2 L).map L.subtype = L)
    (hA : A ⊔ (pPrimeCore 2 B).map B.subtype = B) :
    A ⊔ (pPrimeCore 2 L).map L.subtype = L := by
  apply le_antisymm
  · exact sup_le ((le_sup_left.trans hA.le).trans (le_sup_left.trans hB.le)) (map_subtype_le _)
  · calc L = B ⊔ (pPrimeCore 2 L).map L.subtype := hB.symm
      _ = A ⊔ (pPrimeCore 2 B).map B.subtype ⊔ (pPrimeCore 2 L).map L.subtype := by rw [hA]
      _ ≤ A ⊔ (pPrimeCore 2 L).map L.subtype :=
        sup_le (sup_le le_sup_left ((map_pPrimeCore_le_of_sup_eq hB).trans le_sup_right))
          le_sup_right

theorem map_pPrimeCore_eq_inf_of_sup_eq {B L : Subgroup G}
    (hB : B ⊔ (pPrimeCore 2 L).map L.subtype = L) :
    (pPrimeCore 2 B).map B.subtype = B ⊓ (pPrimeCore 2 L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (le_inf (map_subtype_le _) (map_pPrimeCore_le_of_sup_eq hB)) ?_
  have hle : (B ⊓ (pPrimeCore 2 L).map L.subtype).subgroupOf B ≤ pPrimeCore 2 B := by
    apply le_sSup
    refine ⟨⟨fun x hx g => ?_⟩, ?_⟩
    · rw [mem_subgroupOf] at hx ⊢
      refine mem_inf.mpr ⟨(g * x * g⁻¹ : B).2, ?_⟩
      have hgL : (g : G) ∈ normalizer (((pPrimeCore 2 L).map L.subtype : Subgroup G) : Set G) :=
        UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L)
          (le_normalizer ((le_sup_left.trans hB.le) g.2))
      exact (mem_normalizer_iff.mp hgL _).mp (mem_inf.mp hx).2
    · refine Nat.Coprime.coprime_dvd_right ?_ (pPrimeCore_coprime_card (p := 2) (G := L))
      rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : B ⊓ _ ≤ B)).toEquiv]
      calc Nat.card ↥(B ⊓ (pPrimeCore 2 L).map L.subtype)
          ∣ Nat.card ↥((pPrimeCore 2 L).map L.subtype) := card_dvd_of_le inf_le_right
        _ = Nat.card (pPrimeCore 2 L) := card_map_of_injective L.subtype_injective
  calc B ⊓ (pPrimeCore 2 L).map L.subtype
      = ((B ⊓ (pPrimeCore 2 L).map L.subtype).subgroupOf B).map B.subtype :=
        (map_subgroupOf_eq_of_le inf_le_left).symm
    _ ≤ (pPrimeCore 2 B).map B.subtype := map_mono hle

theorem exists_involution_mem_center {D N : Subgroup G} (hD : IsPGroup 2 D) (hND : N ≤ D)
    (hnorm : D ≤ normalizer (N : Set G)) (hne : N ≠ ⊥) :
    ∃ z ∈ N, orderOf z = 2 ∧ ∀ d ∈ D, d * z = z * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := N.subgroupOf D with hN'
  have hN'norm : N'.Normal := ⟨fun n hn d => by
    rw [mem_subgroupOf] at hn ⊢
    exact (mem_normalizer_iff.mp (hnorm d.2) n).mp hn⟩
  have hN'ne : N' ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hND hx⟩ : D) ∈ N' := hx
    rw [h, mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have : Group.IsNilpotent D := hD.isNilpotent
  have hmeet := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  set W := N' ⊓ center D with hW
  have hW2 : IsPGroup 2 W := hD.to_subgroup W
  have hWnt : Nontrivial W := (nontrivial_iff_ne_bot W).mpr hmeet
  have h2 : 2 ∣ Nat.card W := by
    rcases hW2.card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hWnt).ne'
    · exact h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((x : D) : G), (mem_inf.mp x.2).1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · intro d hd
    exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp x.2).2 ⟨d, hd⟩)

structure B2Setting (a : G) (J S : Subgroup G) : Prop where
  orderOf_eq : orderOf a = 2
  le_centralizer : J ≤ centralizer ({a} : Set G)
  isPComponent : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set G)))
  le_H : S ≤ centralizer ({a} : Set G) ⊓ normalizer (J : Set G)
  isSylow : ∃ P : Sylow 2 ↥(centralizer ({a} : Set G) ⊓ normalizer (J : Set G)),
    (P : Subgroup _) = S.subgroupOf (centralizer ({a} : Set G) ⊓ normalizer (J : Set G))
  iso : ∀ b : G, orderOf b = 2 → b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
    (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
    ∃ K : Subgroup G, GSIsoCorr a J b K
  central : ∀ (b : G) (K : Subgroup G), orderOf b = 2 →
    b ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) →
    (∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype) →
    GSIsoCorr a J b K → b ∈ S → (∀ s ∈ S, s * b = b * s) →
    S ≤ centralizer ({b} : Set G) ⊓ normalizer (K : Set G) ∧
      ∃ P : Sylow 2 ↥(centralizer ({b} : Set G) ⊓ normalizer (K : Set G)),
        (P : Subgroup _) = S.subgroupOf (centralizer ({b} : Set G) ⊓ normalizer (K : Set G))

namespace B2Setting

variable {a : G} {J S : Subgroup G}

theorem isQuasisimple (h : B2Setting a J S) : IsQuasisimple (J ⧸ pPrimeCore 2 J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J _ h.le_centralizer).1
    h.isPComponent).2.2

omit [Finite G] in
theorem isPGroup (h : B2Setting a J S) : IsPGroup 2 S := by
  obtain ⟨P₀, hP₀⟩ := h.isSylow
  have h1 : IsPGroup 2 ((P₀ : Subgroup _).map
      (centralizer ({a} : Set G) ⊓ normalizer (J : Set G)).subtype) := P₀.isPGroup'.map _
  rwa [hP₀, map_subgroupOf_eq_of_le h.le_H] at h1

omit [Finite G] in
theorem comm_a (h : B2Setting a J S) : ∀ s ∈ S, s * a = a * s := fun _s hs =>
  mem_centralizer_singleton_iff.mp (mem_inf.mp (h.le_H hs)).1

omit [Finite G] in
theorem a_mem_coreActionKernel (h : B2Setting a J S) : a ∈ coreActionKernel J :=
  mem_coreActionKernel_of_le_centralizer h.le_centralizer

omit [Finite G] in
theorem a_mem (h : B2Setting a J S) : a ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({a} : Set G) ⊓ normalizer (J : Set G) with hH
  have haH : a ∈ H := mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl,
    (mem_coreActionKernel.mp h.a_mem_coreActionKernel).1⟩
  have ha2 : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_eq, pow_one])
  have hnorm : zpowers a ≤ normalizer (S : Set G) := by
    refine (zpowers_le.mpr ?_).trans (centralizer_le_normalizer _)
    rw [mem_centralizer_iff]
    intro s hs
    exact h.comm_a s hs
  have hQ : IsPGroup 2 ↥(zpowers a ⊔ S) := ha2.to_sup_of_normal_right' h.isPGroup hnorm
  have hQH : zpowers a ⊔ S ≤ H := sup_le (zpowers_le.mpr haH) h.le_H
  obtain ⟨P₀, hP₀⟩ := h.isSylow
  have hle : (P₀ : Subgroup H) ≤ (zpowers a ⊔ S).subgroupOf H := by
    rw [hP₀]
    exact fun x hx => mem_subgroupOf.mpr (mem_sup_right (mem_subgroupOf.mp hx))
  have heq := P₀.is_maximal' (Q := (zpowers a ⊔ S).subgroupOf H) hQ.comap_subtype hle
  have h1 : (⟨a, haH⟩ : H) ∈ (zpowers a ⊔ S).subgroupOf H :=
    mem_subgroupOf.mpr (mem_sup_left (mem_zpowers a))
  rw [heq, hP₀] at h1
  exact mem_subgroupOf.mp h1

omit [Finite G] in
theorem mem_H_of_mem (h : B2Setting a J S) {e : G} (he : e ∈ S ⊓ coreActionKernel J) :
    e ∈ centralizer ({a} : Set G) ⊓ normalizer (J : Set G) ∧
      ∀ j ∈ J, j⁻¹ * e⁻¹ * j * e ∈ (pPrimeCore 2 J).map J.subtype :=
  ⟨h.le_H (mem_inf.mp he).1, (mem_coreActionKernel.mp (mem_inf.mp he).2).2⟩

omit [Finite G] in
theorem exists_isoTarget (h : B2Setting a J S) {e : G} (he : orderOf e = 2)
    (heP : e ∈ S ⊓ coreActionKernel J) : ∃ L : Subgroup G, GSIsoCorr a J e L :=
  h.iso e he (h.mem_H_of_mem heP).1 (h.mem_H_of_mem heP).2

end B2Setting

theorem GSIsoCorr.target_unique {a e : G} {J L L' : Subgroup G} (h : GSIsoCorr a J e L)
    (h' : GSIsoCorr a J e L') : L = L' := by
  obtain ⟨hC, -, hsup⟩ := gsIsoCorr_iff_sup.mp h
  obtain ⟨hC', -, hsup'⟩ := gsIsoCorr_iff_sup.mp h'
  exact eq_of_isPComponent_cover hC.2.2.2.2.2.1 hC.2.2.2.2.2.2.1 hC'.2.2.2.2.2.1
    hC'.2.2.2.2.2.2.1 hsup hsup'

omit [Finite G] in
theorem map_centralizer_subgroup (φ : G ≃* G) (E : Subgroup G) :
    (centralizer (E : Set G)).map φ.toMonoidHom =
      centralizer ((E.map φ.toMonoidHom : Subgroup G) : Set G) := by
  ext z
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro hz _ ⟨e, he, rfl⟩
    have h1 := congrArg φ (hz e he)
    rwa [map_mul, map_mul, φ.apply_symm_apply] at h1
  · intro hz e he
    apply φ.injective
    rw [map_mul, map_mul, φ.apply_symm_apply]
    exact hz (φ e) ⟨e, he, rfl⟩

theorem map_fixedLayer (φ : G ≃* G) (Y E : Subgroup G) :
    (fixedLayer Y E).map φ.toMonoidHom =
      fixedLayer (Y.map φ.toMonoidHom) (E.map φ.toMonoidHom) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY : (Y ⊓ centralizer (E : Set G)).map φ.toMonoidHom =
      Y.map φ.toMonoidHom ⊓ centralizer ((E.map φ.toMonoidHom : Subgroup G) : Set G) := by
    rw [map_inf _ _ _ φ.injective, map_centralizer_subgroup]
  let ψ : ↥(Y ⊓ centralizer (E : Set G)) ≃*
      ↥(Y.map φ.toMonoidHom ⊓ centralizer ((E.map φ.toMonoidHom : Subgroup G) : Set G)) :=
    ((Y ⊓ centralizer (E : Set G)).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr hY)
  have hcomm : φ.toMonoidHom.comp (Y ⊓ centralizer (E : Set G)).subtype =
      (Y.map φ.toMonoidHom ⊓ centralizer ((E.map φ.toMonoidHom : Subgroup G) : Set G)).subtype.comp
        ψ.toMonoidHom := by
    ext y
    rfl
  rw [fixedLayer, fixedLayer, map_map, hcomm, ← map_map,
    FixedLayerPComponent.map_pLayer_mulEquiv 2 ψ]

theorem conjugate_fixedLayer (Y E : Subgroup G) (g : G) :
    conjugate (fixedLayer Y E) g = fixedLayer (conjugate Y g) (conjugate E g) :=
  map_fixedLayer (MulAut.conj g⁻¹) Y E

theorem mem_normalizer_fixedLayer {Y E : Subgroup G} {g : G} (hY : g ∈ normalizer (Y : Set G))
    (hE : g ∈ normalizer (E : Set G)) : g ∈ normalizer (fixedLayer Y E : Set G) := by
  apply mem_normalizer_of_conjugate_eq
  rw [conjugate_fixedLayer, conjugate_eq_of_mem_normalizer hY, conjugate_eq_of_mem_normalizer hE]

omit [Finite G] in
theorem fixedLayer_congr {Y E E' : Subgroup G}
    (h : Y ⊓ centralizer (E : Set G) = Y ⊓ centralizer (E' : Set G)) :
    fixedLayer Y E = fixedLayer Y E' := by
  unfold fixedLayer
  rw [h]

@[expose] def IsCover (J E K : Subgroup G) : Prop :=
  K ≤ centralizer (E : Set G) ∧ IsPComponent 2 (K.subgroupOf (centralizer (E : Set G))) ∧
    fixedLayer J E ⊔ (pPrimeCore 2 K).map K.subtype = K

theorem IsCover.unique {J E K K' : Subgroup G} (h : IsCover J E K) (h' : IsCover J E K') :
    K = K' :=
  eq_of_isPComponent_cover h.1 h.2.1 h'.1 h'.2.1 h.2.2 h'.2.2

theorem IsCover.isQuasisimple {J E K : Subgroup G} (h : IsCover J E K) :
    IsQuasisimple (K ⧸ pPrimeCore 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K _ h.1).1 h.2.1).2.2

omit [Finite G] in
theorem GSIsoCorr.isCover {a e : G} {J L : Subgroup G} (hL : GSIsoCorr a J e L) :
    IsCover J (zpowers e) L := by
  obtain ⟨hC, -, hsup⟩ := gsIsoCorr_iff_sup.mp hL
  rw [IsCover, coe_zpowers, ← coe_zpowers, centralizer_zpowers_eq, fixedLayer_zpowers]
  exact ⟨hC.2.2.2.2.2.1, hC.2.2.2.2.2.2.1, hsup⟩

namespace B2Setting

variable {a : G} {J S : Subgroup G}

theorem isCover_fixedLayer (h : B2Setting a J S) {E : Subgroup G}
    (hE : E ≤ S ⊓ coreActionKernel J) {e : G} (heE : e ∈ E)
    (hEe : E ≤ centralizer ({e} : Set G)) {L : Subgroup G} (hL : GSIsoCorr a J e L) :
    E ≤ coreActionKernel L ∧ IsCover J E (fixedLayer L E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 E := h.isPGroup.to_le (hE.trans inf_le_left)
  have hEJ : E ≤ coreActionKernel J := hE.trans inf_le_right
  have hJq := h.isQuasisimple
  obtain ⟨hNL, -, -, -, -, -, -, hker, -⟩ :=
    isomorphic_correspondence_sylow_growth hL rfl rfl rfl rfl
  have hEL : E ≤ coreActionKernel L := by
    intro g hg
    have h1 : g ∈ {g | g ∈ centralizer ({e} : Set G) ⊓ normalizer (J : Set G) ∧
        ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype} :=
      ⟨mem_inf.mpr ⟨hEe hg, (mem_coreActionKernel.mp (hEJ hg)).1⟩,
        (mem_coreActionKernel.mp (hEJ hg)).2⟩
    rw [hker] at h1
    exact mem_coreActionKernel.mpr ⟨hNL h1.1, h1.2⟩
  obtain ⟨hC, hLa, hsup⟩ := gsIsoCorr_iff_sup.mp hL
  have hLe : L ≤ centralizer ({e} : Set G) := hC.2.2.2.2.2.1
  have hLp := hC.2.2.2.2.2.2.1
  obtain ⟨hLsub, -, hLq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLe).1 hLp
  have hCE : centralizer (E : Set G) ≤ centralizer ({e} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr heE)
  have hpc := fixedLayer_isPComponent hLe hLsub hEe hEL hE2 hLq
  rw [inf_eq_right.mpr hCE] at hpc
  have hzE : zpowers e ≤ E := zpowers_le.mpr heE
  have hJeL : gsFixedLayer J e ≤ L := hC.gsFixedLayer_le hLa
  have hJEK : fixedLayer J E ≤ fixedLayer L E := by
    refine fixedLayer_le_of_twoElements hJq hEJ hE2 fun x hx hk => ?_
    have hxJe : x ∈ fixedLayer J (zpowers e) := by
      rw [fixedLayer_eq_closure hJq (hzE.trans hEJ) (hE2.to_le hzE)]
      refine subset_closure ⟨mem_inf.mpr ⟨(mem_inf.mp hx).1, ?_⟩, hk⟩
      rw [coe_zpowers, ← coe_zpowers, centralizer_zpowers_eq]
      exact hCE (mem_inf.mp hx).2
    rw [fixedLayer_zpowers] at hxJe
    rw [fixedLayer_eq_closure hLq hEL hE2]
    exact subset_closure ⟨mem_inf.mpr ⟨hJeL hxJe, (mem_inf.mp hx).2⟩, hk⟩
  refine ⟨hEL, (fixedLayer_le_inf L E).trans inf_le_right, hpc, ?_⟩
  have hJEJe := (fixedLayer_nested hJq hEJ hE2 hzE).2
  rw [fixedLayer_zpowers] at hJEJe
  have hJEL : fixedLayer J E ⊔ (pPrimeCore 2 L).map L.subtype = L :=
    sup_pPrimeCore_trans hsup hJEJe
  obtain ⟨-, hOK⟩ := fixedLayer_sup_pPrimeCore hLq hEL hE2
  have hKL : fixedLayer L E ≤ L := (fixedLayer_le_inf L E).trans inf_le_left
  apply le_antisymm (sup_le hJEK (map_subtype_le _))
  intro k hk
  have hmul := coe_sup_primeCore_eq_mul (hJEK.trans hKL)
  rw [hJEL] at hmul
  have hk' : k ∈ ((fixedLayer J E : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G)) := by
    rw [← hmul]
    exact hKL hk
  obtain ⟨j, hj, o, ho, rfl⟩ := Set.mem_mul.mp hk'
  have hoK : o ∈ fixedLayer L E := by
    have h1 : o = j⁻¹ * (j * o) := by group
    rw [h1]
    exact mul_mem (inv_mem (hJEK hj)) hk
  have hoOK : o ∈ (pPrimeCore 2 (fixedLayer L E)).map (fixedLayer L E).subtype := by
    rw [hOK]
    exact mem_inf.mpr ⟨hoK, ho⟩
  exact mul_mem (mem_sup_left hj) (mem_sup_right hoOK)

theorem exists_isCover (h : B2Setting a J S) {E : Subgroup G}
    (hE : E ≤ S ⊓ coreActionKernel J) (hne : E ≠ ⊥) : ∃ K : Subgroup G, IsCover J E K := by
  have hE2 : IsPGroup 2 E := h.isPGroup.to_le (hE.trans inf_le_left)
  obtain ⟨e, heE, he, hcomm⟩ := exists_involution_mem_center hE2 le_rfl le_normalizer hne
  have hEe : E ≤ centralizer ({e} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.mpr (hcomm d hd)
  obtain ⟨L, hL⟩ := h.exists_isoTarget he (hE heE)
  exact ⟨_, (h.isCover_fixedLayer hE heE hEe hL).2⟩

end B2Setting

namespace B2Setting

variable {a : G} {J S : Subgroup G}

theorem mem_coreActionKernel_cover_iff (h : B2Setting a J S) {F K : Subgroup G}
    (hF : F ≤ S ⊓ coreActionKernel J) (hne : F ≠ ⊥) (hK : IsCover J F K) {g : G} (hgS : g ∈ S)
    (hgF : g ∈ normalizer (F : Set G)) :
    g ∈ normalizer (K : Set G) ∧ (g ∈ coreActionKernel J ↔ g ∈ coreActionKernel K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : IsPGroup 2 F := h.isPGroup.to_le (hF.trans inf_le_left)
  have hD2 : IsPGroup 2 ↥(F ⊔ zpowers g) :=
    h.isPGroup.to_le (sup_le (hF.trans inf_le_left) (zpowers_le.mpr hgS))
  obtain ⟨e, heF, he, hcomm⟩ := exists_involution_mem_center hD2 le_sup_left
    (sup_le le_normalizer (zpowers_le.mpr hgF)) hne
  have hFe : F ≤ centralizer ({e} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.mpr (hcomm d (mem_sup_left hd))
  have hge : g * e = e * g := hcomm g (mem_sup_right (mem_zpowers g))
  obtain ⟨L, hL⟩ := h.exists_isoTarget he (hF heF)
  obtain ⟨hFL, hcov⟩ := h.isCover_fixedLayer hF heF hFe hL
  have hKeq : K = fixedLayer L F := hK.unique hcov
  subst hKeq
  obtain ⟨hNL, -, -, -, -, -, -, hker, -⟩ :=
    isomorphic_correspondence_sylow_growth hL rfl rfl rfl rfl
  have hgA : g ∈ centralizer ({e} : Set G) ⊓ normalizer (J : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hge, (mem_inf.mp (h.le_H hgS)).2⟩
  have hgL : g ∈ normalizer (L : Set G) := hNL hgA
  have hgK : g ∈ normalizer (fixedLayer L F : Set G) := mem_normalizer_fixedLayer hgL hgF
  refine ⟨hgK, ?_⟩
  have hJL : g ∈ coreActionKernel J ↔ g ∈ coreActionKernel L := by
    constructor
    · intro hgJ
      have h1 : g ∈ {g | g ∈ centralizer ({e} : Set G) ⊓ normalizer (J : Set G) ∧
          ∀ j ∈ J, j⁻¹ * g⁻¹ * j * g ∈ (pPrimeCore 2 J).map J.subtype} :=
        ⟨hgA, (mem_coreActionKernel.mp hgJ).2⟩
      rw [hker] at h1
      exact mem_coreActionKernel.mpr ⟨hgL, h1.2⟩
    · intro hgL'
      have h1 : g ∈ {g | g ∈ centralizer ({e} : Set G) ⊓ normalizer (J : Set G) ∧
          ∀ l ∈ L, l⁻¹ * g⁻¹ * l * g ∈ (pPrimeCore 2 L).map L.subtype} :=
        ⟨hgA, (mem_coreActionKernel.mp hgL').2⟩
      rw [← hker] at h1
      exact mem_coreActionKernel.mpr ⟨(mem_inf.mp hgA).2, h1.2⟩
  rw [hJL]
  obtain ⟨hC, -, -⟩ := gsIsoCorr_iff_sup.mp hL
  have hLe := hC.2.2.2.2.2.1
  obtain ⟨-, -, hLq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hLe).1 hC.2.2.2.2.2.2.1
  obtain ⟨hKL, hOK⟩ := fixedLayer_sup_pPrimeCore hLq hFL hF2
  have hKle : fixedLayer L F ≤ L := (fixedLayer_le_inf L F).trans inf_le_left
  have hgOL : g ∈ normalizer (((pPrimeCore 2 L).map L.subtype : Subgroup G) : Set G) :=
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L) hgL
  constructor
  · intro hgQ
    refine mem_coreActionKernel.mpr ⟨hgK, fun k hk => ?_⟩
    rw [hOK]
    refine mem_inf.mpr ⟨?_, (mem_coreActionKernel.mp hgQ).2 k (hKle hk)⟩
    have h1 := (mem_normalizer_iff.mp (inv_mem hgK) k).mp hk
    rw [inv_inv] at h1
    have h2 : k⁻¹ * g⁻¹ * k * g = k⁻¹ * (g⁻¹ * k * g) := by group
    rw [h2]
    exact mul_mem (inv_mem hk) h1
  · intro hgQ
    refine mem_coreActionKernel.mpr ⟨hgL, fun l hl => ?_⟩
    have hmul := coe_sup_primeCore_eq_mul hKle
    rw [hKL] at hmul
    have hl' : l ∈ ((fixedLayer L F : Set G) * ((pPrimeCore 2 L).map L.subtype : Set G)) := by
      rw [← hmul]
      exact hl
    obtain ⟨k, hk, o, ho, rfl⟩ := Set.mem_mul.mp hl'
    have hkO : k⁻¹ * g⁻¹ * k * g ∈ (pPrimeCore 2 L).map L.subtype := by
      have h1 := (mem_coreActionKernel.mp hgQ).2 k hk
      rw [hOK] at h1
      exact (mem_inf.mp h1).2
    have hoO : g⁻¹ * o * g ∈ (pPrimeCore 2 L).map L.subtype := by
      have h1 := (mem_normalizer_iff.mp (inv_mem hgOL) o).mp ho
      rwa [inv_inv] at h1
    have h2 : (k * o)⁻¹ * g⁻¹ * (k * o) * g = o⁻¹ * (k⁻¹ * g⁻¹ * k * g) * (g⁻¹ * o * g) := by
      group
    rw [h2]
    exact mul_mem (mul_mem (inv_mem ho) hkO) hoO

theorem isCover_nested (h : B2Setting a J S) {F T K : Subgroup G} (hFT : F ≤ T)
    (hT : T ≤ S ⊓ coreActionKernel J) (hTF : T ≤ normalizer (F : Set G)) (hne : F ≠ ⊥)
    (hK : IsCover J F K) :
    T ≤ coreActionKernel K ∧ IsCover J T (fixedLayer K T) ∧
      fixedLayer K T ⊔ (pPrimeCore 2 K).map K.subtype = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := h.isPGroup.to_le (hT.trans inf_le_left)
  have hF : F ≤ S ⊓ coreActionKernel J := hFT.trans hT
  have hF2 : IsPGroup 2 F := hT2.to_le hFT
  have hTK : T ≤ coreActionKernel K := fun g hg =>
    ((h.mem_coreActionKernel_cover_iff hF hne hK (mem_inf.mp (hT hg)).1 (hTF hg)).2).mp
      (mem_inf.mp (hT hg)).2
  obtain ⟨e, heF, he, hcomm⟩ := exists_involution_mem_center hT2 hFT hTF hne
  have hTe : T ≤ centralizer ({e} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.mpr (hcomm d hd)
  obtain ⟨L, hL⟩ := h.exists_isoTarget he (hF heF)
  obtain ⟨hFL, hcovF⟩ := h.isCover_fixedLayer hF heF (hFT.trans hTe) hL
  obtain ⟨hTL, hcovT⟩ := h.isCover_fixedLayer hT (hFT heF) hTe hL
  have hKeq : K = fixedLayer L F := hK.unique hcovF
  have hKq := hK.isQuasisimple
  obtain ⟨hC, -, -⟩ := gsIsoCorr_iff_sup.mp hL
  obtain ⟨-, -, hLq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hC.2.2.2.2.2.1).1 hC.2.2.2.2.2.2.1
  have hCTF : centralizer (T : Set G) ≤ centralizer (F : Set G) := centralizer_le hFT
  have heq : fixedLayer K T = fixedLayer L T := by
    rw [fixedLayer_eq_closure hKq hTK hT2, fixedLayer_eq_closure hLq hTL hT2]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, hk⟩
      refine ⟨mem_inf.mpr ⟨?_, (mem_inf.mp hx).2⟩, hk⟩
      have hxK := (mem_inf.mp hx).1
      rw [hKeq] at hxK
      exact ((fixedLayer_le_inf L F).trans inf_le_left) hxK
    · rintro ⟨hx, hk⟩
      refine ⟨mem_inf.mpr ⟨?_, (mem_inf.mp hx).2⟩, hk⟩
      rw [hKeq, fixedLayer_eq_closure hLq hFL hF2]
      exact subset_closure ⟨mem_inf.mpr ⟨(mem_inf.mp hx).1, hCTF (mem_inf.mp hx).2⟩, hk⟩
  refine ⟨hTK, heq ▸ hcovT, (fixedLayer_sup_pPrimeCore hKq hTK hT2).1⟩

theorem gsIsoCorr_isoTarget (h : B2Setting a J S) {e f : G} (he : orderOf e = 2)
    (hf : orderOf f = 2) (heP : e ∈ S ⊓ coreActionKernel J) (hfP : f ∈ S ⊓ coreActionKernel J)
    (hef : e * f = f * e) {Le Lf : Subgroup G} (hLe : GSIsoCorr a J e Le)
    (hLf : GSIsoCorr a J f Lf) : GSIsoCorr e Le f Lf := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := zpowers e ⊔ zpowers f with hEdef
  have hE : E ≤ S ⊓ coreActionKernel J := sup_le (zpowers_le.mpr heP) (zpowers_le.mpr hfP)
  have hE2 : IsPGroup 2 E := h.isPGroup.to_le (hE.trans inf_le_left)
  have hcen : ∀ c : G, c * e = e * c → c * f = f * c → E ≤ centralizer ({c} : Set G) := by
    intro c hce hcf
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr hce.symm
    · exact mem_centralizer_singleton_iff.mpr hcf.symm
  have hEe : E ≤ centralizer ({e} : Set G) := hcen e rfl hef
  have hEf : E ≤ centralizer ({f} : Set G) := hcen f hef.symm rfl
  obtain ⟨hELe, hcove⟩ := h.isCover_fixedLayer hE (mem_sup_left (mem_zpowers e)) hEe hLe
  obtain ⟨hELf, hcovf⟩ := h.isCover_fixedLayer hE (mem_sup_right (mem_zpowers f)) hEf hLf
  have heq : fixedLayer Le E = fixedLayer Lf E := hcove.unique hcovf
  obtain ⟨hCe, -, -⟩ := gsIsoCorr_iff_sup.mp hLe
  obtain ⟨hCf, -, -⟩ := gsIsoCorr_iff_sup.mp hLf
  have hLee : Le ≤ centralizer ({e} : Set G) := hCe.2.2.2.2.2.1
  have hLff : Lf ≤ centralizer ({f} : Set G) := hCf.2.2.2.2.2.1
  have hCE : centralizer (E : Set G) = centralizer ({e} : Set G) ⊓ centralizer ({f} : Set G) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_left (mem_zpowers e))))
        (centralizer_le (Set.singleton_subset_iff.mpr (mem_sup_right (mem_zpowers f))))
    · intro x hx
      rw [mem_centralizer_iff]
      have hEx : E ≤ centralizer ({x} : Set G) := sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).1).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (mem_inf.mp hx).2).symm))
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hEx hy)
  have h1 : gsFixedLayer Le f = fixedLayer Le E := by
    rw [← fixedLayer_zpowers]
    apply fixedLayer_congr
    rw [hCE, coe_zpowers, ← coe_zpowers, centralizer_zpowers_eq, ← inf_assoc,
      inf_eq_left.mpr hLee]
  have h2 : gsFixedLayer Lf e = fixedLayer Lf E := by
    rw [← fixedLayer_zpowers]
    apply fixedLayer_congr
    rw [hCE, coe_zpowers, ← coe_zpowers, centralizer_zpowers_eq, inf_comm (centralizer _),
      ← inf_assoc, inf_eq_left.mpr hLff]
  have hfLe := hELe (mem_sup_right (mem_zpowers f))
  have heLf := hELf (mem_sup_left (mem_zpowers e))
  have hconj : conjugate Lf e = Lf :=
    conjugate_eq_of_mem_normalizer (mem_coreActionKernel.mp heLf).1
  obtain ⟨-, -, hLfq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Lf _ hLff).1 hCf.2.2.2.2.2.2.1
  rw [gsIsoCorr_iff_sup]
  refine ⟨⟨he, hf, hef, hLee, hCe.2.2.2.2.2.2.1, hLff, hCf.2.2.2.2.2.2.1,
    (mem_coreActionKernel.mp hfLe).1, (mem_coreActionKernel.mp hfLe).2, ?_⟩,
    by rw [hconj, sup_idem], ?_⟩
  · rw [hconj, sup_idem, h1, h2, heq]
  · rw [h1, heq]
    exact (fixedLayer_sup_pPrimeCore hLfq hELf hE2).1

end B2Setting

end CFSG.ComponentClassification.GSLit

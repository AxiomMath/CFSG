module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TLayer
public import CFSG.LocalAnalysis.ComponentClassification.EvenPumpERed
import CFSG.HardMathSupport.Dickson.ElementCaseBp.LayerMap

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def zStarAct (M : Subgroup X) :
    ↥(normalizer (M : Set X)) →* MulAut (↥M ⧸ Open.fusionZStar ↥M) where
  toFun g := QuotientGroup.congr _ _ (M.normalizerMonoidHom g)
    (characteristic_iff_map_eq.mp inferInstance _)
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
    show QuotientGroup.mk' _ (M.normalizerMonoidHom 1 m) = QuotientGroup.mk' _ m
    rw [map_one]
    rfl
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
    show QuotientGroup.mk' _ (M.normalizerMonoidHom (g * h) m) =
      QuotientGroup.mk' _ (M.normalizerMonoidHom g (M.normalizerMonoidHom h m))
    rw [map_mul]
    rfl

abbrev imgZ (M T : Subgroup X) : Subgroup (↥M ⧸ Open.fusionZStar ↥M) :=
  (T.subgroupOf M).map (QuotientGroup.mk' (Open.fusionZStar ↥M))

noncomputable abbrev actZ (M E : Subgroup X) : Subgroup (MulAut (↥M ⧸ Open.fusionZStar ↥M)) :=
  (E.subgroupOf (normalizer (M : Set X))).map (zStarAct M)

theorem zStarAct_mk (M : Subgroup X) (g : ↥(normalizer (M : Set X))) (m : ↥M) :
    zStarAct M g (QuotientGroup.mk' (Open.fusionZStar ↥M) m) =
      QuotientGroup.mk' (Open.fusionZStar ↥M)
        ⟨(g : X) * m * (g : X)⁻¹, (mem_normalizer_iff.mp g.2 m).mp m.2⟩ :=
  rfl

theorem zStarAct_of_mem (M : Subgroup X) (m : ↥M) :
    zStarAct M ⟨m, le_normalizer m.2⟩ =
      MulAut.conj (QuotientGroup.mk' (Open.fusionZStar ↥M) m) := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [zStarAct_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

private theorem map_inv_mul_eq_one_of_mem_center {Y Q : Type*} [Group Y] [Group Q]
    [Group.IsPerfect Y] (ρ : Y →* Q) (α : Y →* Y) (h : ∀ y, ρ (y⁻¹ * α y) ∈ center Q) (y : Y) :
    ρ (y⁻¹ * α y) = 1 := by
  let δ : Y →* center Q := MonoidHom.mk' (fun y => ⟨ρ (y⁻¹ * α y), h y⟩) fun a b => by
    apply Subtype.ext
    change ρ ((a * b)⁻¹ * α (a * b)) = ρ (a⁻¹ * α a) * ρ (b⁻¹ * α b)
    have e1 : (a * b)⁻¹ * α (a * b) = b⁻¹ * (a⁻¹ * α a) * α b := by
      rw [map_mul]
      group
    have hc : ρ b⁻¹ * ρ (a⁻¹ * α a) = ρ (a⁻¹ * α a) * ρ b⁻¹ := mem_center_iff.mp (h a) _
    rw [e1, map_mul ρ (b⁻¹ * (a⁻¹ * α a)) (α b), map_mul ρ b⁻¹ (a⁻¹ * α a), hc, mul_assoc,
      map_mul ρ b⁻¹ (α b)]
  have hker : commutator Y ≤ δ.ker := Abelianization.commutator_subset_ker δ
  rw [Group.IsPerfect.commutator_eq_top] at hker
  exact congrArg Subtype.val (MonoidHom.mem_ker.mp (hker (mem_top y)))

theorem zStarAct_eq_one_iff {H M : Subgroup X} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) (g : ↥(normalizer (M : Set X))) :
    zStarAct M g = 1 ↔ (g : X) ∈ coreActionKernel M := by
  rw [mem_coreActionKernel]
  constructor
  · intro h
    refine ⟨g.2, fun j hj => ?_⟩
    have : Group.IsPerfect ↥M := isPerfect_of_isPComponent hMH hM
    set α := M.normalizerMonoidHom g
    set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
    have hZ : ∀ m : ↥M, ρ (m⁻¹ * α m) ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
      intro m
      have h1 : zStarAct M g (QuotientGroup.mk' _ m) = QuotientGroup.mk' _ m := by
        rw [h]
        rfl
      rw [zStarAct_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
      have h2 := inv_mem h1
      rw [mul_inv_rev, inv_inv, Sol78.fusionZStar_eq_comap, mem_comap] at h2
      exact h2
    have hO : ∀ m : ↥M, ((m : X)⁻¹ * ((g : X) * m * (g : X)⁻¹)) ∈
        (pPrimeCore 2 ↥M).map M.subtype := by
      intro m
      have h1 := map_inv_mul_eq_one_of_mem_center ρ α.toMonoidHom hZ m
      rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact ⟨_, h1, rfl⟩
    have hm : (g : X)⁻¹ * j * g ∈ M := by
      have h1 := (mem_normalizer_iff.mp (inv_mem g.2) j).mp hj
      rwa [inv_inv] at h1
    have h1 := inv_mem (hO ⟨_, hm⟩)
    convert h1 using 1
    simp only
    group
  · rintro ⟨-, hg⟩
    refine MulEquiv.ext fun x => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rw [zStarAct_mk, MulAut.one_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    apply Sol78.pPrimeCore_le_fusionZStar
    obtain ⟨o, ho, hoe⟩ := mem_map.mp (hg _ ((mem_normalizer_iff.mp g.2 m).mp m.2))
    convert ho using 1
    apply Subtype.ext
    rw [show (o : X) = _ from hoe]
    simp only [coe_mul, coe_inv]
    group

private theorem exists_mem_centralizer_mk_eq {M E : Subgroup X} (hE : IsPGroup 2 E)
    (hEN : E ≤ normalizer (M : Set X)) (w : ↥M)
    (hw : ∀ (e : X) (he : e ∈ E), QuotientGroup.mk' (pPrimeCore 2 ↥M)
      (M.normalizerMonoidHom ⟨e, hEN he⟩ w) = QuotientGroup.mk' (pPrimeCore 2 ↥M) w) :
    ∃ c : ↥M, (c : X) ∈ centralizer (E : Set X) ∧
      QuotientGroup.mk' (pPrimeCore 2 ↥M) c = QuotientGroup.mk' (pPrimeCore 2 ↥M) w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  let _ := SignalizerFunctor.Helpers.conjugationAction E M hEN
  have hsmul : ∀ (e : ↥E) (v : ↥M), e • v = M.normalizerMonoidHom ⟨e, hEN e.2⟩ v :=
    fun _ _ => rfl
  have hO : ∀ (e : ↥E) (o : ↥M), o ∈ pPrimeCore 2 ↥M →
      M.normalizerMonoidHom ⟨e, hEN e.2⟩ o ∈ pPrimeCore 2 ↥M := by
    intro e o ho
    rw [← pPrimeCore_map_iso 2 (M.normalizerMonoidHom ⟨e, hEN e.2⟩)]
    exact mem_map_of_mem _ ho
  let fibre : SubMulAction E ↥M := ⟨{v | ρ v = ρ w}, by
    intro e v hv
    change ρ (e • v) = ρ w
    rw [hsmul, ← hw e e.2]
    change ρ v = ρ w at hv
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hv ⊢
    rw [← map_inv, ← map_mul]
    exact hO e _ hv⟩
  have hfibre : Nat.card fibre = Nat.card (pPrimeCore 2 ↥M) := by
    have heq : {v : ↥M | ρ v = ρ w} = ρ ⁻¹' {ρ w} := by
      ext v
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [← QuotientGroup.ker_mk' (pPrimeCore 2 ↥M)]
    exact (Nat.card_congr (Set.equivOfEq heq)).trans (Nat.card_congr (ρ.fiberEquivKer w))
  have hnd : ¬ 2 ∣ Nat.card fibre := by
    rw [hfibre]
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  obtain ⟨c, hc⟩ := hE.nonempty_fixed_point_of_prime_not_dvd_card fibre hnd
  refine ⟨c.val, mem_centralizer_iff.mpr fun e he => ?_, c.2⟩
  have h1 := congrArg (fun v : fibre => ((v.val : ↥M) : X)) (hc ⟨e, he⟩)
  change e * c.val * e⁻¹ = c.val at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem isPComponent_imgZ {H M E T : Subgroup X} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) (hEH : E ≤ H) (hEN : E ≤ normalizer (M : Set X))
    (hE : IsPGroup 2 E) (hTM : T ≤ M) (hTE : T ≤ centralizer (E : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer (E : Set X)))) :
    imgZ M T ≤ EvenPump.autFixed (actZ M E) ∧
      IsPComponent 2 ((imgZ M T).subgroupOf (EvenPump.autFixed (actZ M E))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Open.fusionZStar ↥M) with hπ
  set ρ := QuotientGroup.mk' (pPrimeCore 2 ↥M) with hρ
  set F := EvenPump.autFixed (actZ M E) with hF
  set C : Subgroup ↥M := (M ⊓ centralizer (E : Set X)).subgroupOf M
  set T' : Subgroup ↥M := T.subgroupOf M
  have hT'C : T' ≤ C := fun t ht => mem_subgroupOf.mpr ⟨t.2, hTE ht⟩
  have hFmem : ∀ x, x ∈ F ↔
      ∀ n : ↥(normalizer (M : Set X)), (n : X) ∈ E → zStarAct M n x = x := by
    intro x
    rw [hF, EvenPump.mem_autFixed]
    constructor
    · intro h n hn
      exact h _ ⟨n, hn, rfl⟩
    · rintro h _ ⟨n, hn, rfl⟩
      exact h n hn
  have hCF : C.map π ≤ F := by
    rintro _ ⟨c, hc, rfl⟩
    rw [hFmem]
    intro n hn
    rw [hπ, zStarAct_mk]
    congr 1
    apply Subtype.ext
    change (n : X) * c * (n : X)⁻¹ = c
    rw [mem_centralizer_iff.mp (mem_subgroupOf.mp hc).2 n hn, mul_inv_cancel_right]
  have hCn : ((C.map π).subgroupOf F).Normal := by
    constructor
    rintro ⟨y, hyF⟩ hy ⟨x, hxF⟩
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Open.fusionZStar ↥M) x
    obtain ⟨c', hc', hc'w⟩ := exists_mem_centralizer_mk_eq hE hEN (m * c * m⁻¹) (by
      intro e he
      rw [← hρ]
      set α := M.normalizerMonoidHom ⟨e, hEN he⟩
      have hαc : α c = c := by
        apply Subtype.ext
        change e * c * e⁻¹ = c
        rw [mem_centralizer_iff.mp (mem_subgroupOf.mp hc).2 e he, mul_inv_cancel_right]
      have hz : ρ (m⁻¹ * α m) ∈ center (↥M ⧸ pPrimeCore 2 ↥M) := by
        have h1 := (hFmem _).mp hxF ⟨e, hEN he⟩ he
        rw [zStarAct_mk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq] at h1
        have h2 := inv_mem h1
        rw [mul_inv_rev, inv_inv, Sol78.fusionZStar_eq_comap, mem_comap] at h2
        exact h2
      obtain ⟨z, hz, hαm⟩ : ∃ z, ρ z ∈ center (↥M ⧸ pPrimeCore 2 ↥M) ∧ α m = m * z :=
        ⟨m⁻¹ * α m, hz, by group⟩
      have hαw : α (m * c * m⁻¹) = m * z * c * (m * z)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hαc, hαm]
      have hzc := mem_center_iff.mp hz (ρ c)
      rw [hαw]
      simp only [map_mul, map_inv, mul_inv_rev]
      calc ρ m * ρ z * ρ c * ((ρ z)⁻¹ * (ρ m)⁻¹)
          = ρ m * (ρ c * ρ z) * (ρ z)⁻¹ * (ρ m)⁻¹ := by rw [hzc]; group
        _ = ρ m * ρ c * (ρ m)⁻¹ := by group)
    refine ⟨c', mem_subgroupOf.mpr ⟨c'.2, hc'⟩, ?_⟩
    have h1 : c'⁻¹ * (m * c * m⁻¹) ∈ Open.fusionZStar ↥M := by
      apply Sol78.pPrimeCore_le_fusionZStar
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hc'w
      exact hc'w
    simp only [coe_mul, coe_inv]
    rw [← map_inv, ← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    exact h1
  have hTCH : T ≤ H ⊓ centralizer (E : Set X) := le_inf (hTM.trans hMH) hTE
  have hT'c : IsPComponent 2 (T'.subgroupOf C) :=
    (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two).mpr
      (isPComponent_of_le_of_le (le_inf hTM hTE) (inf_le_inf_right _ hMH) hT)
  have hT'img : IsPComponent 2 ((T'.map π).subgroupOf (C.map π)) := by
    have h := HardMathSupport.Dickson.ElementCaseBp.isPComponent_map_of_surjective
      (π.subgroupMap_surjective C) hT'c ?_
    · rwa [GSThmB.OddQuot.map_subgroupOf_subgroupMap π hT'C] at h
    · intro hle
      apply not_isSolvable_of_isQuasisimple (isQuasisimple_of_isPComponent hTCH hT)
      have hZ : ∀ t : ↥T, inclusion hTM t ∈ Open.fusionZStar ↥M := by
        intro t
        have h1 : (⟨inclusion hTM t, hT'C t.2⟩ : ↥C) ∈ T'.subgroupOf C := t.2
        have h2 := congrArg Subtype.val (MonoidHom.mem_ker.mp (hle h1))
        change π (inclusion hTM t) = 1 at h2
        rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have : Group.IsSolvable ↥(Open.fusionZStar ↥M) := isSolvable_fusionZStar ↥M
      exact Group.isSolvable_of_isSolvable_injective
        (f := (inclusion hTM).codRestrict (Open.fusionZStar ↥M) hZ) fun a b hab =>
          inclusion_injective hTM (congrArg Subtype.val hab)
  have hTC' : T'.map π ≤ C.map π := map_mono hT'C
  exact ⟨hTC'.trans hCF,
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hTC' hCF hCn.isSubnormal).mpr
      hT'img⟩

private theorem fusionZStar_le_comap {A B : Type*} [Group A] [Group B] [Finite A]
    (f : A →* B) (hf : Function.Surjective f) :
    Open.fusionZStar A ≤ (Open.fusionZStar B).comap f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : (pPrimeCore 2 A).map f ≤ pPrimeCore 2 B :=
    Semidihedral.OddCoreQuotient.pPrimeCore_map_le_of_surjective 2 f hf
  intro a ha
  rw [mem_comap, GSThmB.OddQuot.mem_fusionZStar_iff]
  intro b
  obtain ⟨m, rfl⟩ := hf b
  rw [← map_commutatorElement]
  exact hO (mem_map_of_mem f (GSThmB.OddQuot.mem_fusionZStar_iff.mp ha m))

private theorem exists_surjective_imgZ {M T : Subgroup X} (hTM : T ≤ M) :
    ∃ f : ↥T →* ↥(imgZ M T), Function.Surjective f ∧
      ∀ t : ↥T, (f t : ↥M ⧸ Open.fusionZStar ↥M) =
        QuotientGroup.mk' (Open.fusionZStar ↥M) (inclusion hTM t) :=
  ⟨((QuotientGroup.mk' (Open.fusionZStar ↥M)).subgroupMap (T.subgroupOf M)).comp
      (subgroupOfEquivOfLe hTM).symm.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ _).comp (subgroupOfEquivOfLe hTM).symm.surjective,
    fun _ => rfl⟩

theorem card_imgZ_eq {H M E T : Subgroup X} (hMH : M ≤ H)
    (hM : IsPComponent 2 (M.subgroupOf H)) (hEH : E ≤ H) (hEN : E ≤ normalizer (M : Set X))
    (hE : IsPGroup 2 E) (hTM : T ≤ M) (hTE : T ≤ centralizer (E : Set X))
    (hT : IsPComponent 2 (T.subgroupOf (H ⊓ centralizer (E : Set X))))
    (hs : IsSimpleGroup (↥T ⧸ Open.fusionZStar ↥T)) :
    Nat.card (↥(imgZ M T) ⧸ Open.fusionZStar ↥(imgZ M T)) =
      Nat.card (↥T ⧸ Open.fusionZStar ↥T) := by
  obtain ⟨hTF, hTc⟩ := isPComponent_imgZ hMH hM hEH hEN hE hTM hTE hT
  obtain ⟨f, hf, -⟩ := exists_surjective_imgZ (M := M) hTM
  have hle := fusionZStar_le_comap f hf
  set φ := QuotientGroup.map _ _ f hle
  have hφs : Function.Surjective φ :=
    QuotientGroup.map_surjective_of_surjective _ _ f (QuotientGroup.mk_surjective.comp hf) hle
  rcases hs.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · exact (Nat.card_congr
      (MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp h, hφs⟩).toEquiv).symm
  · exfalso
    have hZ : Open.fusionZStar ↥(imgZ M T) = ⊤ := by
      rw [← QuotientGroup.subsingleton_iff]
      refine ⟨fun a b => ?_⟩
      obtain ⟨a, rfl⟩ := hφs a
      obtain ⟨b, rfl⟩ := hφs b
      rw [MonoidHom.mem_ker.mp (h ▸ mem_top a), MonoidHom.mem_ker.mp (h ▸ mem_top b)]
    apply not_isSolvable_of_isQuasisimple (isQuasisimple_of_isPComponent hTF hTc)
    have h1 := isSolvable_fusionZStar ↥(imgZ M T)
    rw [hZ] at h1
    exact Group.isSolvable_of_surjective
      (f := (topEquiv : ↥(⊤ : Subgroup ↥(imgZ M T)) ≃* _).toMonoidHom) topEquiv.surjective

theorem zStarAct_trivial_on_imgZ {M T : Subgroup X} (hTM : T ≤ M)
    (g : ↥(normalizer (M : Set X))) (hgT : (g : X) ∈ coreActionKernel T) :
    ∀ u ∈ imgZ M T, zStarAct M g u ∈ imgZ M T ∧
      zStarAct M g u * u⁻¹ ∈ (pPrimeCore 2 ↥(imgZ M T)).map (imgZ M T).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hgN, hgO⟩ := mem_coreActionKernel.mp hgT
  rintro _ ⟨t, ht, rfl⟩
  replace ht : (t : X) ∈ T := ht
  refine ⟨?_, ?_⟩
  · rw [zStarAct_mk]
    exact mem_map_of_mem _ (mem_subgroupOf.mpr ((mem_normalizer_iff.mp hgN t).mp ht))
  · obtain ⟨f, hf, hfmk⟩ := exists_surjective_imgZ (M := M) hTM
    have hOf := CFSG.map_pPrimeCore_le (p := 2) f hf
    have hj : (g : X) * (t : X)⁻¹ * (g : X)⁻¹ ∈ T :=
      (mem_normalizer_iff.mp hgN _).mp (inv_mem ht)
    obtain ⟨o, ho, hoe⟩ := mem_map.mp (hgO _ hj)
    refine ⟨f o, hOf (mem_map_of_mem f ho), ?_⟩
    rw [subtype_apply, hfmk, zStarAct_mk, ← map_inv, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [coe_inclusion, show (o : X) = _ from hoe]
    simp only [coe_mul, coe_inv]
    group

theorem isSylow_imgZ {M R : Subgroup X} (hR : Seven.IsSylowIn R M) :
    ∃ T : Sylow 2 (↥M ⧸ Open.fusionZStar ↥M), (T : Subgroup _) = imgZ M R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, S, hS⟩ := hR
  exact ⟨S.mapSurjective (QuotientGroup.mk'_surjective _), by rw [Sylow.coe_mapSurjective, hS]⟩

end CFSG.ComponentClassification.GSThmB.A10T

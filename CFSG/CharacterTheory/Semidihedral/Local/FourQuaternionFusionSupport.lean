module

public import CFSG.CharacterTheory.Semidihedral.Local.CentricRadicalSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open

universe u

variable {G : Type u} [Group G]

section Conjugates

theorem map_conj_inv_one (P : Subgroup G) : P.map (MulAut.conj (1 : G)⁻¹).toMonoidHom = P := by
  ext x
  simp

theorem map_conj_inv_mul (P : Subgroup G) (a b : G) :
    P.map (MulAut.conj (a * b)⁻¹).toMonoidHom =
      (P.map (MulAut.conj a⁻¹).toMonoidHom).map (MulAut.conj b⁻¹).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv, mul_inv_rev, mul_assoc]

theorem map_conj_inv_eq_of_pointwise (P : Subgroup G) {a b : G}
    (hab : ∀ x ∈ P, a⁻¹ * x * a = b⁻¹ * x * b) :
    P.map (MulAut.conj a⁻¹).toMonoidHom = P.map (MulAut.conj b⁻¹).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simpa using (hab y hy).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by simpa using hab y hy⟩

theorem support_automorphism_image_eq_map_conj {Q T : Subgroup G} (hQT : Q ≤ T) (α : MulAut T)
    (h : G) (hα : ∀ x : T, (α x : G) = h⁻¹ * (x : G) * h) :
    ((Q.subgroupOf T).map α.toMonoidHom).map T.subtype = Q.map (MulAut.conj h⁻¹).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, by simpa using (hα z).symm⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨α ⟨y, hQT hy⟩, ⟨⟨y, hQT hy⟩, hy, rfl⟩, ?_⟩
    simpa using hα ⟨y, hQT hy⟩

end Conjugates

section Decompositions

@[expose] def SemidihedralFusionStep (S T : Subgroup G) (h : G) : Prop :=
  (T = S ∧ h ∈ S) ∨ (IsKleinFour T ∧ h ∈ Subgroup.normalizer (T : Set G)) ∨
    (Nonempty (T ≃* QuaternionGroup 2) ∧ h ∈ Subgroup.normalizer (T : Set G))

theorem SemidihedralFusionStep.mem_normalizer {S T : Subgroup G} {h : G}
    (hs : SemidihedralFusionStep S T h) : h ∈ Subgroup.normalizer (T : Set G) := by
  rcases hs with ⟨rfl, hh⟩ | ⟨-, hh⟩ | ⟨-, hh⟩
  · exact Subgroup.le_normalizer hh
  · exact hh
  · exact hh

inductive SemidihedralFusionDecomposition (S P : Subgroup G) : G → Prop
  | one : SemidihedralFusionDecomposition S P 1
  | tail {g h : G} {T : Subgroup G} :
      SemidihedralFusionDecomposition S P g → T ≤ S →
      P.map (MulAut.conj g⁻¹).toMonoidHom ≤ T → SemidihedralFusionStep S T h →
      SemidihedralFusionDecomposition S P (g * h)

theorem SemidihedralFusionDecomposition.exists_prefixes {S P : Subgroup G} {z : G} (hPS : P ≤ S)
    (hchain : SemidihedralFusionDecomposition S P z) :
    ∃ k : ℕ, ∃ prefixes : Fin (k + 1) → G,
      ∃ supports : Fin k → Subgroup G, ∃ actors : Fin k → G,
        prefixes 0 = 1 ∧ prefixes (Fin.last k) = z ∧
        (∀ i : Fin k, prefixes i.succ = prefixes i.castSucc * actors i) ∧
        (∀ i : Fin k, supports i ≤ S ∧
          P.map (MulAut.conj (prefixes i.castSucc)⁻¹).toMonoidHom ≤ supports i ∧
          SemidihedralFusionStep S (supports i) (actors i)) ∧
        ∀ i : Fin (k + 1), P.map (MulAut.conj (prefixes i)⁻¹).toMonoidHom ≤ S := by
  induction hchain with
  | one =>
      refine ⟨0, fun _ => 1, Fin.elim0, Fin.elim0, rfl, rfl,
        (by intro i; exact i.elim0), (by intro i; exact i.elim0), ?_⟩
      intro i
      rw [map_conj_inv_one]
      exact hPS
  | @tail z h T hprev hTS hcur hallowed ih =>
      obtain ⟨k, prefixes, supports, actors, hfirst, hlast, hstep, hdata, hinside⟩ := ih
      let stepData (a : G) (T : Subgroup G) (b : G) : Prop :=
        T ≤ S ∧ P.map (MulAut.conj a⁻¹).toMonoidHom ≤ T ∧ SemidihedralFusionStep S T b
      let prefixes' : Fin (k + 2) → G := Fin.snoc prefixes (z * h)
      let supports' : Fin (k + 1) → Subgroup G := Fin.snoc supports T
      let actors' : Fin (k + 1) → G := Fin.snoc actors h
      refine ⟨k + 1, prefixes', supports', actors', ?_, ?_, ?_, ?_, ?_⟩
      · change prefixes' (0 : Fin (k + 1)).castSucc = 1
        simpa only [prefixes', Fin.snoc_castSucc] using hfirst
      · exact Fin.snoc_last _ _
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [prefixes', actors', Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, hlast]
        · simpa only [prefixes', actors', Fin.succ_castSucc, Fin.snoc_castSucc] using hstep j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · change stepData (prefixes' (Fin.last k).castSucc) (supports' (Fin.last k))
            (actors' (Fin.last k))
          dsimp only [supports', actors', prefixes']
          rw [Fin.snoc_last, Fin.snoc_last, Fin.snoc_castSucc, hlast]
          exact ⟨hTS, hcur, hallowed⟩
        · change stepData (prefixes' j.castSucc.castSucc) (supports' j.castSucc)
            (actors' j.castSucc)
          dsimp only [supports', actors', prefixes']
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
          exact hdata j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · dsimp only [prefixes']
          rw [Fin.snoc_last, map_conj_inv_mul]
          have hh := hallowed.mem_normalizer
          rintro _ ⟨y, hy, rfl⟩
          have hyT := hcur hy
          have hhinv := (Subgroup.normalizer (T : Set G)).inv_mem hh
          have himage := (Subgroup.mem_normalizer_iff.mp hhinv y).mp hyT
          apply hTS
          simpa using himage
        · simpa only [prefixes', Fin.snoc_castSucc] using hinside j

end Decompositions

structure SemidihedralFusionChain (S : Subgroup G) (k : ℕ) where
  subgroups : Fin (k + 1) → Subgroup G
  supports : Fin k → Subgroup G
  automorphisms : (i : Fin k) → MulAut (supports i)
  subgroup_le : ∀ i, subgroups i ≤ S
  support_le : ∀ i, supports i ≤ S
  domain_le : ∀ i, subgroups i.castSucc ≤ supports i
  image_eq : ∀ i,
    (((subgroups i.castSucc).subgroupOf (supports i)).map
      (automorphisms i).toMonoidHom).map (supports i).subtype = subgroups i.succ
  realized : ∀ i, ∃ h : G, SemidihedralFusionStep S (supports i) h ∧
    ∀ x : supports i, (automorphisms i x : G) = h⁻¹ * (x : G) * h

namespace SemidihedralFusionChain

variable {S : Subgroup G} {k : ℕ} (c : SemidihedralFusionChain S k)

@[expose] def step (i : Fin k) : c.subgroups i.castSucc →* c.subgroups i.succ where
  toFun x := ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩, by
    rw [← c.image_eq i]
    exact Subgroup.mem_map.mpr
      ⟨c.automorphisms i ⟨x, c.domain_le i x.property⟩,
        Subgroup.mem_map.mpr ⟨⟨x, c.domain_le i x.property⟩, x.property, rfl⟩, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G)) (map_one (c.automorphisms i))
  map_mul' x y := by
    apply Subtype.ext
    exact congrArg (fun t : c.supports i => (t : G))
      (map_mul (c.automorphisms i) ⟨x, c.domain_le i x.property⟩ ⟨y, c.domain_le i y.property⟩)

theorem step_coe (i : Fin k) (x : c.subgroups i.castSucc) :
    (c.step i x : G) = (c.automorphisms i ⟨x, c.domain_le i x.property⟩ : G) := rfl

@[expose] def prefixMap : (i : Fin (k + 1)) → c.subgroups 0 →* c.subgroups i :=
  Fin.induction (MonoidHom.id _) (fun i f => (c.step i).comp f)

theorem prefix_zero (x : c.subgroups 0) : c.prefixMap 0 x = x := by
  simp only [prefixMap, Fin.induction_zero, MonoidHom.id_apply]

theorem prefix_succ (i : Fin k) (x : c.subgroups 0) :
    c.prefixMap i.succ x = c.step i (c.prefixMap i.castSucc x) := by
  simp only [prefixMap, Fin.induction_succ, MonoidHom.comp_apply]

@[expose] def composite : c.subgroups 0 →* c.subgroups (Fin.last k) :=
  c.prefixMap (Fin.last k)

theorem composite_zero (c : SemidihedralFusionChain S 0) (x : c.subgroups 0) :
    (c.composite x : G) = x :=
  congrArg Subtype.val (c.prefix_zero x)

theorem prefix_coe_eq (prefixes : Fin (k + 1) → G) (actors : Fin k → G)
    (hfirst : prefixes 0 = 1)
    (hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i)
    (ha : ∀ i, ∀ x : c.supports i,
      (c.automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i) :
    ∀ i, ∀ x : c.subgroups 0,
      (c.prefixMap i x : G) = (prefixes i)⁻¹ * (x : G) * prefixes i := by
  intro i
  refine Fin.induction ?_ (fun j ih => ?_) i
  · intro x
    rw [hfirst, c.prefix_zero]
    simp only [inv_one, one_mul, mul_one]
  · intro x
    rw [c.prefix_succ, c.step_coe, ha, ih, hstep]
    group

theorem subgroups_eq_map_conj (prefixes : Fin (k + 1) → G) (actors : Fin k → G)
    (hfirst : prefixes 0 = 1)
    (hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i)
    (ha : ∀ i, ∀ x : c.supports i,
      (c.automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i) :
    ∀ i, c.subgroups i = (c.subgroups 0).map (MulAut.conj (prefixes i)⁻¹).toMonoidHom := by
  intro i
  refine Fin.induction ?_ (fun j ih => ?_) i
  · rw [hfirst, map_conj_inv_one]
  · rw [← c.image_eq j, support_automorphism_image_eq_map_conj (c.domain_le j)
      (c.automorphisms j) (actors j) (ha j), ih, hstep, map_conj_inv_mul]

theorem exists_realizing_element :
    ∃ g : G, c.subgroups (Fin.last k) = (c.subgroups 0).map (MulAut.conj g⁻¹).toMonoidHom ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = g⁻¹ * (x : G) * g := by
  classical
  choose actors _hallowed ha using c.realized
  let prefixes : Fin (k + 1) → G := Fin.induction 1 (fun i g => g * actors i)
  have hfirst : prefixes 0 = 1 := Fin.induction_zero _ _
  have hstep : ∀ i, prefixes i.succ = prefixes i.castSucc * actors i :=
    fun i => Fin.induction_succ _ _ i
  exact ⟨prefixes (Fin.last k),
    c.subgroups_eq_map_conj prefixes actors hfirst hstep ha (Fin.last k),
    c.prefix_coe_eq prefixes actors hfirst hstep ha (Fin.last k)⟩

end SemidihedralFusionChain

theorem SemidihedralFusionDecomposition.exists_chain {S P : Subgroup G} {z : G} (hPS : P ≤ S)
    (hchain : SemidihedralFusionDecomposition S P z) :
    ∃ k : ℕ, ∃ c : SemidihedralFusionChain S k,
      c.subgroups 0 = P ∧ c.subgroups (Fin.last k) = P.map (MulAut.conj z⁻¹).toMonoidHom ∧
      ∀ x : c.subgroups 0, (c.composite x : G) = z⁻¹ * (x : G) * z := by
  obtain ⟨k, prefixes, supports, actors, hfirst, hlast, hstep, hdata, hinside⟩ :=
    hchain.exists_prefixes hPS
  have hnormalizer : ∀ i, actors i ∈ Subgroup.normalizer (supports i : Set G) :=
    fun i => (hdata i).2.2.mem_normalizer
  let automorphisms (i : Fin k) : MulAut (supports i) :=
    ((supports i).normalizerMonoidHom ⟨actors i, hnormalizer i⟩).symm
  have ha : ∀ i, ∀ x : supports i,
      (automorphisms i x : G) = (actors i)⁻¹ * (x : G) * actors i :=
    fun i x => Subgroup.normalizerMonoidHom_apply_symm_apply_coe _ _ x
  let c : SemidihedralFusionChain S k :=
    { subgroups := fun i => P.map (MulAut.conj (prefixes i)⁻¹).toMonoidHom
      supports := supports
      automorphisms := automorphisms
      subgroup_le := hinside
      support_le := fun i => (hdata i).1
      domain_le := fun i => (hdata i).2.1
      image_eq := by
        intro i
        rw [support_automorphism_image_eq_map_conj (hdata i).2.1 (automorphisms i) (actors i)
          (ha i), hstep i, map_conj_inv_mul]
      realized := fun i => ⟨actors i, (hdata i).2.2, ha i⟩ }
  refine ⟨k, c, ?_, ?_, ?_⟩
  · change P.map (MulAut.conj (prefixes 0)⁻¹).toMonoidHom = P
    rw [hfirst, map_conj_inv_one]
  · change P.map (MulAut.conj (prefixes (Fin.last k))⁻¹).toMonoidHom = _
    rw [hlast]
  · intro x
    have hx := c.prefix_coe_eq prefixes actors hfirst hstep ha (Fin.last k) x
    simpa only [SemidihedralFusionChain.composite, hlast] using hx

section Alperin

variable [Finite G]

theorem image_on_sylow_of_pGroup {N : Type*} {A : Type*} [Group N] [Finite N] [Group A] {p : ℕ}
    [Fact p.Prime] (hA : IsPGroup p A) (φ : N →* A) (Q : Sylow p N) (m : N) :
    ∃ q : N, q ∈ (Q : Subgroup N) ∧ φ q = φ m := by
  let T : Sylow p φ.range := Q.mapSurjective φ.rangeRestrict_surjective
  have htop : (T : Subgroup φ.range) = ⊤ :=
    (T.is_maximal' ((hA.to_subgroup φ.range).to_subgroup ⊤) le_top).symm
  have hm : (⟨φ m, ⟨m, rfl⟩⟩ : φ.range) ∈ (T : Subgroup φ.range) := by
    rw [htop]
    trivial
  change (⟨φ m, ⟨m, rfl⟩⟩ : φ.range) ∈ (Q : Subgroup N).map φ.rangeRestrict at hm
  obtain ⟨q, hq, heq⟩ := Subgroup.mem_map.mp hm
  exact ⟨q, hq, congrArg Subtype.val heq⟩

theorem sylow_normalizer_step_replacement (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) (m : G)
    (hm : m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G)) :
    ∃ s ∈ (S : Subgroup G), ∀ x ∈ (S : Subgroup G), s⁻¹ * x * s = m⁻¹ * x * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAut : IsPGroup 2 (MulAut (S : Subgroup G)) :=
    (Principal.subgroup_automorphisms_outside_four_and_quaternion_eight hn ⟨f⟩).2
  obtain ⟨q, hq, hqeq⟩ := image_on_sylow_of_pGroup hAut (S : Subgroup G).normalizerMonoidHom
    (S.subtype Subgroup.le_normalizer) ⟨m, hm⟩
  have hqS : (q : G) ∈ (S : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at hq
    exact hq
  refine ⟨q, hqS, fun x hx => ?_⟩
  have heq := DFunLike.congr_fun (congrArg MulEquiv.symm hqeq) (⟨x, hx⟩ : (S : Subgroup G))
  have hval := congrArg Subtype.val heq
  simpa only [Subgroup.normalizerMonoidHom_apply_symm_apply_coe] using hval

theorem semidihedralFusionDecomposition_of_alperin (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (f : SemidihedralGroup n ≃* S) {P : Subgroup G} {c : G}
    (hc : CFSG.RankTwoShapes.AlperinDecomposition 2 (S : Subgroup G) P c) :
    ∃ z : G, SemidihedralFusionDecomposition (S : Subgroup G) P z ∧
      ∀ x ∈ P, z⁻¹ * x * z = c⁻¹ * x * c := by
  induction hc with
  | one => exact ⟨1, .one, fun x _ => rfl⟩
  | @step c m Q hprev hQ hPQ hm ih =>
      obtain ⟨z, hz, hzc⟩ := ih
      obtain ⟨hQS, -, hQC, hQrad⟩ := hQ
      have hPz : P.map (MulAut.conj z⁻¹).toMonoidHom ≤ Q := by
        rw [map_conj_inv_eq_of_pointwise P hzc]
        exact hPQ
      have himage : ∀ x ∈ P, c⁻¹ * x * c ∈ Q := fun x hx => hPQ ⟨x, hx, by simp⟩
      by_cases hQeq : Q = S
      · subst hQeq
        obtain ⟨s, hsS, hsm⟩ := sylow_normalizer_step_replacement n hn S f m hm
        refine ⟨z * s, .tail hz le_rfl hPz (Or.inl ⟨rfl, hsS⟩), fun x hx => ?_⟩
        calc (z * s)⁻¹ * x * (z * s) = s⁻¹ * (z⁻¹ * x * z) * s := by group
          _ = s⁻¹ * (c⁻¹ * x * c) * s := by rw [hzc x hx]
          _ = m⁻¹ * (c⁻¹ * x * c) * m := hsm _ (himage x hx)
          _ = (c * m)⁻¹ * x * (c * m) := by group
      · have hcentric : (S : Subgroup G) ⊓ Subgroup.centralizer (Q : Set G) =
            (Subgroup.center Q).map Q.subtype := by
          rw [center_map_subtype_eq]
          apply le_antisymm
          · rintro x ⟨hxS, hxC⟩
            exact ⟨hQC ⟨hxC, hxS⟩, hxC⟩
          · rintro x ⟨hxQ, hxC⟩
            exact ⟨hQS hxQ, hxC⟩
        have htype := proper_centric_radical_subgroups n hn S f Q (lt_of_le_of_ne hQS hQeq)
          hcentric hQrad
        have hstep : SemidihedralFusionStep (S : Subgroup G) Q m := by
          rcases htype with hK | hQ8
          · exact Or.inr (Or.inl ⟨hK, hm⟩)
          · exact Or.inr (Or.inr ⟨hQ8, hm⟩)
        refine ⟨z * m, .tail hz hQS hPz hstep, fun x hx => ?_⟩
        calc (z * m)⁻¹ * x * (z * m) = m⁻¹ * (z⁻¹ * x * z) * m := by group
          _ = m⁻¹ * (c⁻¹ * x * c) * m := by rw [hzc x hx]
          _ = (c * m)⁻¹ * x * (c * m) := by group

end Alperin

end CFSG.Semidihedral.Local

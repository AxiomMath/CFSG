module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.ComponentClassification.OutcomeLocal

section Group

variable {G : Type*} [Group G]

theorem i285_eq_bot_of_pCoreOf {X K : Subgroup G} (hX : CFSG.Open.pCoreOf 2 X = ⊥) (hKX : K ≤ X)
    (hn : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (h4 : ∀ k ∈ K, k ^ 4 = 1) : K = ⊥ := by
  have hN : (K.subgroupOf X).Normal := by
    constructor
    intro n hn' g
    rw [Subgroup.mem_subgroupOf] at hn' ⊢
    have := hn g g.2 n hn'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have hP : IsPGroup 2 (K.subgroupOf X) := by
    intro g
    refine ⟨2, ?_⟩
    have h1 : ((g : X) : G) ^ 4 = 1 := h4 _ g.2
    apply Subtype.ext
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_pow]
    exact h1
  have hle : K.subgroupOf X ≤ CFSG.Open.pCore 2 X :=
    le_sSup ⟨hN, hP⟩
  have hK : K ≤ CFSG.Open.pCoreOf 2 X := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hKX]
    exact Subgroup.map_mono hle
  rw [hX] at hK
  exact le_bot_iff.1 hK

theorem i285_closure_le_centralizer {S T : Set G} (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.closure T : Set G) := by
  rw [Subgroup.closure_le]
  intro s hs
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro t ht
  have hle : Subgroup.closure T ≤ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.closure_le]
    intro t' ht'
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    rw [hs']
    exact h s hs t' ht'
  have := hle ht
  rw [Subgroup.mem_centralizer_iff] at this
  exact (this s rfl).symm

end Group

section GLBasics

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

theorem i285_mul_apply (g h : 𝔾) (v : M) :
    ((g * h : 𝔾) : M →ₗ[ZMod 2] M) v = (g : M →ₗ[ZMod 2] M) ((h : M →ₗ[ZMod 2] M) v) := rfl

theorem i285_one_apply (v : M) : ((1 : 𝔾) : M →ₗ[ZMod 2] M) v = v := rfl

theorem i285_inv_apply_apply (g : 𝔾) (v : M) :
    ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) ((g : M →ₗ[ZMod 2] M) v) = v := by
  rw [← i285_mul_apply, inv_mul_cancel, i285_one_apply]

theorem i285_apply_inv_apply (g : 𝔾) (v : M) :
    (g : M →ₗ[ZMod 2] M) (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v) = v := by
  rw [← i285_mul_apply, mul_inv_cancel, i285_one_apply]

theorem i285_ext {g h : 𝔾} (hgh : ∀ v, (g : M →ₗ[ZMod 2] M) v = (h : M →ₗ[ZMod 2] M) v) :
    g = h :=
  Units.ext (LinearMap.ext hgh)

@[expose] def i285_stab (S : Submodule (ZMod 2) M) : Subgroup 𝔾 where
  carrier := {g | ∀ v, (g : M →ₗ[ZMod 2] M) v ∈ S ↔ v ∈ S}
  mul_mem' {g h} hg hh v := by
    change ∀ v, _ at hg hh
    change (g : M →ₗ[ZMod 2] M) ((h : M →ₗ[ZMod 2] M) v) ∈ S ↔ v ∈ S
    rw [hg, hh]
  one_mem' v := Iff.rfl
  inv_mem' {g} hg v := by
    have := hg (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v)
    rw [i285_apply_inv_apply] at this
    exact this.symm

theorem i285_le_stab {H : Subgroup 𝔾} {S : Submodule (ZMod 2) M}
    (h : ∀ g ∈ H, ∀ v ∈ S, (g : M →ₗ[ZMod 2] M) v ∈ S) : H ≤ i285_stab S := by
  intro g hg v
  refine ⟨fun hv => ?_, h g hg v⟩
  have := h g⁻¹ (H.inv_mem hg) _ hv
  rwa [i285_inv_apply_apply] at this

@[expose] def i285_fix (S : Submodule (ZMod 2) M) : Subgroup 𝔾 where
  carrier := {g | ∀ v ∈ S, (g : M →ₗ[ZMod 2] M) v = v}
  mul_mem' {g h} hg hh v hv := by rw [i285_mul_apply, hh v hv, hg v hv]
  one_mem' v _ := rfl
  inv_mem' {g} hg v hv := by
    have := i285_inv_apply_apply g v
    rwa [hg v hv] at this

theorem i285_mem_fix {S : Submodule (ZMod 2) M} {g : 𝔾} :
    g ∈ i285_fix S ↔ ∀ v ∈ S, (g : M →ₗ[ZMod 2] M) v = v := Iff.rfl

@[expose] def i285_triv (S : Submodule (ZMod 2) M) : Subgroup 𝔾 where
  carrier := {g | ∀ v, (g : M →ₗ[ZMod 2] M) v - v ∈ S}
  mul_mem' {g h} hg hh v := by
    have := S.add_mem (hg ((h : M →ₗ[ZMod 2] M) v)) (hh v)
    rwa [sub_add_sub_cancel] at this
  one_mem' v := by
    change v - v ∈ S
    rw [sub_self]
    exact S.zero_mem
  inv_mem' {g} hg v := by
    have := S.neg_mem (hg (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v))
    rwa [i285_apply_inv_apply, neg_sub] at this

theorem i285_mem_triv {S : Submodule (ZMod 2) M} {g : 𝔾} :
    g ∈ i285_triv S ↔ ∀ v, (g : M →ₗ[ZMod 2] M) v - v ∈ S := Iff.rfl

theorem i285_triv_le_stab (S : Submodule (ZMod 2) M) : i285_triv S ≤ i285_stab S := by
  intro g hg v
  constructor
  · intro h
    have := S.sub_mem h (hg v)
    rwa [sub_sub_cancel] at this
  · intro h
    have := S.add_mem (hg v) h
    rwa [sub_add_cancel] at this

@[expose] def i285_U3 (P Q : Submodule (ZMod 2) M) : Subgroup 𝔾 where
  carrier := {g | (∀ v, (g : M →ₗ[ZMod 2] M) v - v ∈ P) ∧
    (∀ v ∈ P, (g : M →ₗ[ZMod 2] M) v - v ∈ Q) ∧ ∀ v ∈ Q, (g : M →ₗ[ZMod 2] M) v = v}
  mul_mem' {g h} hg hh := by
    obtain ⟨g1, g2, g3⟩ := hg
    obtain ⟨h1, h2, h3⟩ := hh
    refine ⟨(i285_triv P).mul_mem g1 h1, fun v hv => ?_, (i285_fix Q).mul_mem g3 h3⟩
    have hhv : (h : M →ₗ[ZMod 2] M) v ∈ P := (i285_triv_le_stab P h1 v).2 hv
    have := Q.add_mem (g2 _ hhv) (h2 v hv)
    rwa [sub_add_sub_cancel] at this
  one_mem' := ⟨(i285_triv P).one_mem, fun v _ => by
    change v - v ∈ Q
    rw [sub_self]
    exact Q.zero_mem, (i285_fix Q).one_mem⟩
  inv_mem' {g} hg := by
    obtain ⟨g1, g2, g3⟩ := hg
    refine ⟨(i285_triv P).inv_mem g1, fun v hv => ?_, (i285_fix Q).inv_mem g3⟩
    have hgv : ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v ∈ P :=
      (i285_triv_le_stab P ((i285_triv P).inv_mem g1) v).2 hv
    have := Q.neg_mem (g2 _ hgv)
    rwa [i285_apply_inv_apply, neg_sub] at this

theorem i285_mem_U3 {P Q : Submodule (ZMod 2) M} {g : 𝔾} :
    g ∈ i285_U3 P Q ↔ (∀ v, (g : M →ₗ[ZMod 2] M) v - v ∈ P) ∧
      (∀ v ∈ P, (g : M →ₗ[ZMod 2] M) v - v ∈ Q) ∧ ∀ v ∈ Q, (g : M →ₗ[ZMod 2] M) v = v :=
  Iff.rfl

theorem i285_pow_four {P Q : Submodule (ZMod 2) M} {g : 𝔾} (hg : g ∈ i285_U3 P Q) :
    g ^ 4 = 1 := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hsq : ∀ v, (g : M →ₗ[ZMod 2] M) ((g : M →ₗ[ZMod 2] M) v) - v ∈ Q := by
    intro v
    have hq := h2 _ (h1 v)
    have e : (g : M →ₗ[ZMod 2] M) ((g : M →ₗ[ZMod 2] M) v) - v =
        ((g : M →ₗ[ZMod 2] M) ((g : M →ₗ[ZMod 2] M) v - v) - ((g : M →ₗ[ZMod 2] M) v - v)) +
          (((g : M →ₗ[ZMod 2] M) v - v) + ((g : M →ₗ[ZMod 2] M) v - v)) := by
      rw [map_sub]
      abel
    rw [e, zmod2_add_self, add_zero]
    exact hq
  have e4 : g ^ 4 = (g * g) * (g * g) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e4]
  apply i285_ext
  intro v
  rw [i285_mul_apply, i285_one_apply]
  set k := g * g with hk
  have hkv : ∀ v, (k : M →ₗ[ZMod 2] M) v - v ∈ Q := fun v => by
    rw [hk, i285_mul_apply]
    exact hsq v
  have hkq : ∀ v ∈ Q, (k : M →ₗ[ZMod 2] M) v = v := fun v hv => by
    rw [hk, i285_mul_apply, h3 v hv, h3 v hv]
  have hu := hkv v
  have e2 : (k : M →ₗ[ZMod 2] M) v = v + ((k : M →ₗ[ZMod 2] M) v - v) := by abel
  calc (k : M →ₗ[ZMod 2] M) ((k : M →ₗ[ZMod 2] M) v)
      = (k : M →ₗ[ZMod 2] M) (v + ((k : M →ₗ[ZMod 2] M) v - v)) := by rw [← e2]
    _ = (k : M →ₗ[ZMod 2] M) v + ((k : M →ₗ[ZMod 2] M) v - v) := by rw [map_add, hkq _ hu]
    _ = v + (((k : M →ₗ[ZMod 2] M) v - v) + ((k : M →ₗ[ZMod 2] M) v - v)) := by abel
    _ = v := by rw [zmod2_add_self, add_zero]

theorem i285_mem_map {g : 𝔾} {R : Submodule (ZMod 2) M} {v : M} :
    v ∈ R.map (g : M →ₗ[ZMod 2] M) ↔ ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v ∈ R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [i285_inv_apply_apply]
  · intro h
    exact ⟨_, h, i285_apply_inv_apply g v⟩

theorem i285_map_eq_of_stab {g : 𝔾} {T : Submodule (ZMod 2) M} (hg : g ∈ i285_stab T) :
    T.map (g : M →ₗ[ZMod 2] M) = T := by
  ext v
  rw [i285_mem_map]
  exact (i285_stab T).inv_mem hg v

theorem i285_stab_inf {g : 𝔾} {A B : Submodule (ZMod 2) M} (hA : g ∈ i285_stab A)
    (hB : g ∈ i285_stab B) : g ∈ i285_stab (A ⊓ B) := fun v => by
  rw [Submodule.mem_inf, Submodule.mem_inf, hA v, hB v]

theorem i285_mem_stab_map {g w : 𝔾} {R : Submodule (ZMod 2) M} (hw : g⁻¹ * w * g ∈ i285_stab R) :
    w ∈ i285_stab (R.map (g : M →ₗ[ZMod 2] M)) := fun v => by
  rw [i285_mem_map, i285_mem_map, ← hw (((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) v), i285_mul_apply,
    i285_mul_apply, i285_apply_inv_apply]

theorem i285_map_mul (g h : 𝔾) (R : Submodule (ZMod 2) M) :
    R.map ((g * h : 𝔾) : M →ₗ[ZMod 2] M) =
      (R.map (h : M →ₗ[ZMod 2] M)).map (g : M →ₗ[ZMod 2] M) := by
  rw [← Submodule.map_comp]
  rfl

theorem i285_map_one (R : Submodule (ZMod 2) M) :
    R.map ((1 : 𝔾) : M →ₗ[ZMod 2] M) = R :=
  Submodule.map_id R

theorem i285_map_inv_map (g : 𝔾) (R : Submodule (ZMod 2) M) :
    (R.map (g : M →ₗ[ZMod 2] M)).map ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M) = R := by
  rw [← i285_map_mul, inv_mul_cancel, i285_map_one]

theorem i285_map_map_inv (g : 𝔾) (R : Submodule (ZMod 2) M) :
    (R.map ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M)).map (g : M →ₗ[ZMod 2] M) = R := by
  rw [← i285_map_mul, mul_inv_cancel, i285_map_one]

theorem i285_map_le_map_iff (g : 𝔾) {R T : Submodule (ZMod 2) M} :
    R.map (g : M →ₗ[ZMod 2] M) ≤ T.map (g : M →ₗ[ZMod 2] M) ↔ R ≤ T := by
  refine ⟨fun h => ?_, fun h => Submodule.map_mono h⟩
  have := Submodule.map_mono (f := ((g⁻¹ : 𝔾) : M →ₗ[ZMod 2] M)) h
  rwa [i285_map_inv_map, i285_map_inv_map] at this

theorem i285_map_lt_map_iff (g : 𝔾) {R T : Submodule (ZMod 2) M} :
    R.map (g : M →ₗ[ZMod 2] M) < T.map (g : M →ₗ[ZMod 2] M) ↔ R < T := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, i285_map_le_map_iff, i285_map_le_map_iff]

theorem i285_comm_of_fix {d e : 𝔾} {α β : M} {f f' : M → ZMod 2}
    (hd : ∀ v, (d : M →ₗ[ZMod 2] M) v = v + f v • α)
    (he : ∀ v, (e : M →ₗ[ZMod 2] M) v = v + f' v • β)
    (hdβ : (d : M →ₗ[ZMod 2] M) β = β) (heα : (e : M →ₗ[ZMod 2] M) α = α) : d * e = e * d := by
  apply i285_ext
  intro v
  rw [i285_mul_apply, i285_mul_apply, he v, map_add, map_smul, hdβ, hd v, map_add, map_smul, heα,
    he v]
  abel

@[expose] def i285_fixSub (g : 𝔾) : Submodule (ZMod 2) M :=
  LinearMap.ker ((g : M →ₗ[ZMod 2] M) - LinearMap.id)

theorem i285_mem_fixSub {g : 𝔾} {v : M} : v ∈ i285_fixSub g ↔ (g : M →ₗ[ZMod 2] M) v = v := by
  rw [i285_fixSub, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

@[expose] def i285_relSub (g : 𝔾) (Q : Submodule (ZMod 2) M) : Submodule (ZMod 2) M :=
  Q.comap ((g : M →ₗ[ZMod 2] M) - LinearMap.id)

theorem i285_mem_relSub {g : 𝔾} {Q : Submodule (ZMod 2) M} {v : M} :
    v ∈ i285_relSub g Q ↔ (g : M →ₗ[ZMod 2] M) v - v ∈ Q := by
  rw [i285_relSub, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]

theorem i285_fix_le_stab (S : Submodule (ZMod 2) M) : i285_fix S ≤ i285_stab S :=
  i285_le_stab fun g hg v hv => by rw [hg v hv]; exact hv

end GLBasics

section SectionAction

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

local notation "𝔾" => LinearMap.GeneralLinearGroup (ZMod 2) M

@[expose] def i285_secEnd {R Q : Submodule (ZMod 2) M} {H : Subgroup 𝔾} (hR : H ≤ i285_stab R)
    (hQ : H ≤ i285_stab Q) : ↥H →* Module.End (ZMod 2) (↥R ⧸ Q.comap R.subtype) where
  toFun h := (Q.comap R.subtype).mapQ (Q.comap R.subtype)
    (((h : 𝔾) : M →ₗ[ZMod 2] M).restrict fun v hv => (hR h.2 v).2 hv) fun v hv => by
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply] at hv ⊢
      exact (hQ h.2 _).2 hv
  map_one' := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

@[expose] def i285_secHom {R Q : Submodule (ZMod 2) M} {H : Subgroup 𝔾} (hR : H ≤ i285_stab R)
    (hQ : H ≤ i285_stab Q) :
    ↥H →* LinearMap.GeneralLinearGroup (ZMod 2) (↥R ⧸ Q.comap R.subtype) :=
  (i285_secEnd hR hQ).toHomUnits

theorem i285_secHom_mk {R Q : Submodule (ZMod 2) M} {H : Subgroup 𝔾} (hR : H ≤ i285_stab R)
    (hQ : H ≤ i285_stab Q) (h : ↥H) (v : ↥R) :
    ((i285_secHom hR hQ h : LinearMap.GeneralLinearGroup (ZMod 2) (↥R ⧸ Q.comap R.subtype)) :
        (↥R ⧸ Q.comap R.subtype) →ₗ[ZMod 2] (↥R ⧸ Q.comap R.subtype))
        (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ⟨((h : 𝔾) : M →ₗ[ZMod 2] M) v, (hR h.2 v).2 v.2⟩ := rfl

end SectionAction

theorem i285_isMcLaughlinGroup_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (hB : UniquenessMaximal.IsMcLaughlinGroup B) : UniquenessMaximal.IsMcLaughlinGroup A := by
  rcases hB with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨n, hn, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨e.trans f⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, ⟨e.trans f⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨n, hn, ⟨e.trans f⟩⟩)))

@[expose] def i285_Decomp {G : Type} [Group G] (X : Subgroup G) (τ : G) (r : ℕ)
    (W : Fin (r + 1) → Subgroup G) : Prop :=
  (⨆ i, W i) = Subgroup.closure {τ' | ∃ g ∈ X, τ' = g⁻¹ * τ * g} ∧
    (∀ i, W i ≤ X) ∧
    (∀ i j, i ≠ j → W i ≤ Subgroup.centralizer (W j : Set G)) ∧
    (∀ i, W i ⊓ (⨆ j : {j // j ≠ i}, W j) = ⊥) ∧
    (∀ i, ∃ g ∈ X, CFSG.Open.GLBConj g (W 0) = W i) ∧
    (∀ g ∈ X, ∀ i, ∃ j, CFSG.Open.GLBConj g (W i) = W j) ∧
    τ ∈ W 0 ∧ (∀ i, UniquenessMaximal.IsMcLaughlinGroup ↥(W i))

theorem i285_exists_enum {α : Type*} {s : Set α} (hs : s.Finite) {a : α} (ha : a ∈ s) :
    ∃ (r : ℕ) (f : Fin (r + 1) → α), f 0 = a ∧ Function.Injective f ∧ Set.range f = s := by
  classical
  have : Finite ↥s := hs.to_subtype
  have : Nonempty ↥s := ⟨⟨a, ha⟩⟩
  have hpos : 0 < Nat.card ↥s := Nat.card_pos
  let e : ↥s ≃ Fin (Nat.card ↥s - 1 + 1) :=
    (Finite.equivFin ↥s).trans (finCongr (Nat.succ_pred_eq_of_pos hpos).symm)
  let e' : ↥s ≃ Fin (Nat.card ↥s - 1 + 1) := e.trans (Equiv.swap (e ⟨a, ha⟩) 0)
  have he' : e' ⟨a, ha⟩ = 0 := by
    simp only [e', Equiv.trans_apply, Equiv.swap_apply_left]
  refine ⟨Nat.card ↥s - 1, fun i => (e'.symm i : α), ?_, ?_, ?_⟩
  · simp only
    rw [← he', Equiv.symm_apply_apply]
  · intro i j hij
    exact e'.symm.injective (Subtype.ext hij)
  · ext b
    constructor
    · rintro ⟨i, rfl⟩
      exact (e'.symm i).2
    · intro hb
      exact ⟨e' ⟨b, hb⟩, by simp only [Equiv.symm_apply_apply]⟩

end CFSG.HardMathSupport.Solomon.Coordinator

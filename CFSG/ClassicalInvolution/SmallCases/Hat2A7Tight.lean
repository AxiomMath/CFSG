module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Witness

public section

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open

theorem A7Witness.of_quotientEquiv {A B : Type*} [Group A] [Group B] {JA : Subgroup A}
    {JB : Subgroup B}
    (q : (JA ⧸ classicalInvolutionOddCore JA) ≃* (JB ⧸ classicalInvolutionOddCore JB))
    (h : A7Witness JA) : A7Witness JB := by
  have hZ : (Subgroup.center (JA ⧸ classicalInvolutionOddCore JA)).map q.toMonoidHom =
      Subgroup.center (JB ⧸ classicalInvolutionOddCore JB) := Subgroup.map_center_eq q
  obtain ⟨hqs, hcard, ⟨ψ⟩⟩ := h
  refine ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv q.symm hqs, ?_,
    ⟨(QuotientGroup.congr _ _ q hZ).symm.trans ψ⟩⟩
  rw [← hcard, ← hZ]
  exact Subgroup.card_map_of_injective q.injective

theorem A7Witness.of_mulEquiv {A B : Type*} [Group A] [Group B] {JA : Subgroup A}
    {JB : Subgroup B} (e : JA ≃* JB) (h : A7Witness JA) : A7Witness JB :=
  A7Witness.of_quotientEquiv (QuotientGroup.congr _ _ e
    (CFSG.ComponentClassification.OddCore.equiv_invariant e)) h

theorem A7Witness.of_surjective {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    {JA : Subgroup A} {JB : Subgroup B} (f : JA →* JB) (hf : Function.Surjective f)
    (hker : Odd (Nat.card f.ker)) (h : A7Witness JA) : A7Witness JB :=
  A7Witness.of_quotientEquiv
    (CFSG.ComponentClassification.OddKernel.coreQuotientEquiv f hf hker) h

section Classical

variable {F : Type*} [Group F]

structure IsClassical2A7 (Y L : Subgroup F) (u : F) : Prop where
  orderOf_eq_two : orderOf u = 2
  mem : u ∈ L
  perfect : Group.IsPerfect ↥L
  subnormal : IsSubnormal L (Y ⊓ Subgroup.centralizer ({u} : Set F))
  witness : A7Witness L

namespace IsClassical2A7

variable {Y L : Subgroup F} {u : F}

theorem le_centralizer (h : IsClassical2A7 Y L u) : L ≤ Subgroup.centralizer ({u} : Set F) :=
  (isSubnormal_le h.subnormal).trans inf_le_right

theorem le (h : IsClassical2A7 Y L u) : L ≤ Y :=
  (isSubnormal_le h.subnormal).trans inf_le_left

theorem mul_comm_of_mem (h : IsClassical2A7 Y L u) {k : F} (hk : k ∈ L) : k * u = u * k :=
  (Subgroup.mem_centralizer_iff.mp (h.le_centralizer hk) u rfl).symm

theorem mul_self (h : IsClassical2A7 Y L u) : u * u = 1 := by
  have := pow_orderOf_eq_one u
  rwa [h.orderOf_eq_two, pow_two] at this

theorem eq_of_orderOf_eq_two [Finite F] (h : IsClassical2A7 Y L u) {w : F} (hw : w ∈ L)
    (hw2 : orderOf w = 2) : w = u :=
  unique_involution_of_witness h.witness h.orderOf_eq_two h.mem (fun _ hk => h.mul_comm_of_mem hk)
    w hw hw2

theorem mono (h : IsClassical2A7 Y L u) {Y' : Subgroup F} (hLY' : L ≤ Y') (hY' : Y' ≤ Y) :
    IsClassical2A7 Y' L u := by
  refine ⟨h.orderOf_eq_two, h.mem, h.perfect, ?_, h.witness⟩
  have h1 := isSubnormal_inf h.subnormal Y'
  have e1 : L ⊓ Y' = L := inf_eq_left.mpr hLY'
  have e2 : (Y ⊓ Subgroup.centralizer ({u} : Set F)) ⊓ Y' = Y' ⊓ Subgroup.centralizer ({u} : Set F) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨_, hc⟩, hy⟩
      exact ⟨hy, hc⟩
    · rintro ⟨hy, hc⟩
      exact ⟨⟨hY' hy, hc⟩, hy⟩
  rwa [e1, e2] at h1

theorem conj (h : IsClassical2A7 Y L u) (g : F) :
    IsClassical2A7 (Y.map (MulAut.conj g).toMonoidHom) (L.map (MulAut.conj g).toMonoidHom)
      (g * u * g⁻¹) := by
  have hperf := h.perfect
  refine ⟨?_, ⟨u, h.mem, rfl⟩, ?_, ?_, ?_⟩
  · rw [orderOf_conj_eq, h.orderOf_eq_two]
  · exact Group.IsPerfect.map (MulAut.conj g).toMonoidHom
  · have h1 := isSubnormal_map_conj h.subnormal g
    have e : (Y ⊓ Subgroup.centralizer ({u} : Set F)).map (MulAut.conj g).toMonoidHom =
        Y.map (MulAut.conj g).toMonoidHom ⊓ Subgroup.centralizer ({g * u * g⁻¹} : Set F) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_centralizer_singleton]
    rwa [e] at h1
  · exact A7Witness.of_mulEquiv (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective) h.witness

end IsClassical2A7

@[expose] def ClassicalCommuteBelow (F : Type*) [Group F] : Prop :=
  ∀ x : F, orderOf x = 2 → Subgroup.centralizer ({x} : Set F) ≠ ⊤ → ∀ (L M : Subgroup F) (u v : F),
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) L u →
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) M v → CommOrEq L M

@[expose] def ClassicalQuasisimple (F : Type*) [Group F] : Prop :=
  ∀ (L : Subgroup F) (u : F), IsClassical2A7 ⊤ L u →
    classicalInvolutionOddCore ↥L ≤ Subgroup.center ↥L

end Classical

section Tight

variable {F : Type*} [Group F] {K : Subgroup F} {z : F}

theorem map_map_conj (J : Subgroup F) (a b : F) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

structure IsTight (K : Subgroup F) (z : F) : Prop where
  classical : IsClassical2A7 ⊤ K z
  tight : Subgroup.centralizer ({z} : Set F) ≤ Subgroup.normalizer (K : Set F)

theorem IsTight.conj (h : IsTight K z) (g : F) :
    IsTight (K.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) := by
  refine ⟨?_, ?_⟩
  · have h1 := h.classical.conj g
    rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1
  · intro c hc
    rw [← map_conj_eq_iff_mem_normalizer, map_map_conj, map_conj_eq_map_conj_iff]
    apply h.tight
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    simp only [Set.mem_singleton_iff, forall_eq] at hc ⊢
    calc z * (g⁻¹ * (c * g)) = g⁻¹ * (g * z * g⁻¹ * c) * g := by group
      _ = g⁻¹ * (c * (g * z * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * (c * g) * z := by group

theorem IsTight.map_conj_eq (h : IsTight K z) {g g' : F} (e : g * z * g⁻¹ = g' * z * g'⁻¹) :
    K.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj g').toMonoidHom := by
  rw [map_conj_eq_map_conj_iff]
  apply h.tight
  rw [Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  calc z * (g'⁻¹ * g) = g'⁻¹ * (g' * z * g'⁻¹) * g := by group
    _ = g'⁻¹ * (g * z * g⁻¹) * g := by rw [e]
    _ = g'⁻¹ * g * z := by group

@[expose] def classOf (z : F) : Set F := {u | ∃ g : F, g * z * g⁻¹ = u}

variable (K z) in
@[expose] noncomputable def memb (u : F) : Subgroup F :=
  open Classical in
  if h : ∃ g : F, g * z * g⁻¹ = u then K.map (MulAut.conj h.choose).toMonoidHom else ⊥

theorem memb_eq (h : IsTight K z) {g : F} {u : F} (hg : g * z * g⁻¹ = u) :
    memb K z u = K.map (MulAut.conj g).toMonoidHom := by
  have hex : ∃ g : F, g * z * g⁻¹ = u := ⟨g, hg⟩
  rw [memb]
  simp only [hex, dite_true]
  exact h.map_conj_eq (hex.choose_spec.trans hg.symm)

theorem memb_self (h : IsTight K z) : memb K z z = K := by
  rw [memb_eq h (g := 1) (by simp)]
  ext x
  simp

theorem memb_conj (h : IsTight K z) {u : F} (hu : u ∈ classOf z) (g : F) :
    memb K z (g * u * g⁻¹) = (memb K z u).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨h₀, rfl⟩ := hu
  rw [memb_eq h (g := h₀) rfl, memb_eq h (g := g * h₀) (by group), map_map_conj]

theorem mem_classOf_conj {u : F} (hu : u ∈ classOf z) (g : F) : g * u * g⁻¹ ∈ classOf z := by
  obtain ⟨h₀, rfl⟩ := hu
  exact ⟨g * h₀, by group⟩

theorem IsTight.memb (h : IsTight K z) {u : F} (hu : u ∈ classOf z) :
    IsTight (memb K z u) u := by
  obtain ⟨g, hg⟩ := hu
  rw [memb_eq h hg, ← hg]
  exact h.conj g

end Tight

section Clique

variable {F : Type*} [Group F] [Finite F] {K : Subgroup F} {z : F}

structure TightSetting (F : Type*) [Group F] (K : Subgroup F) (z : F) : Prop where
  tight : IsTight K z
  center_trivial : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1
  IH : ClassicalCommuteBelow F
  P1 : ClassicalQuasisimple F

variable (K z) in
@[expose] def Zset : Set F := {u | u ∈ classOf z ∧ CommOrEq K (memb K z u)}

omit [Finite F] in
theorem TightSetting.centralizer_ne_top (S : TightSetting F K z) {x : F} (hx : x ≠ 1) :
    Subgroup.centralizer ({x} : Set F) ≠ ⊤ := by
  intro h
  apply hx
  apply S.center_trivial
  intro y
  have : y ∈ Subgroup.centralizer ({x} : Set F) := h ▸ Subgroup.mem_top y
  exact Subgroup.mem_centralizer_iff.mp this x rfl

omit [Finite F] in
theorem mem_classOf_self (z : F) : z ∈ classOf z := ⟨1, by simp⟩

omit [Finite F] in
theorem orderOf_eq_two_of_mem_classOf (h : IsTight K z) {u : F} (hu : u ∈ classOf z) :
    orderOf u = 2 := by
  obtain ⟨g, rfl⟩ := hu
  rw [orderOf_conj_eq]
  exact h.classical.orderOf_eq_two

omit [Finite F] in
theorem TightSetting.mem_memb (S : TightSetting F K z) {u : F} (hu : u ∈ classOf z) :
    u ∈ memb K z u :=
  (S.tight.memb hu).classical.mem

omit [Finite F] in
theorem TightSetting.ne_one (S : TightSetting F K z) {u : F} (hu : u ∈ classOf z) : u ≠ 1 := by
  intro h
  have := orderOf_eq_two_of_mem_classOf S.tight hu
  rw [h, orderOf_one] at this
  omega

omit [Finite F] in
theorem TightSetting.commOrEq_of_le_centralizer (S : TightSetting F K z) {x : F}
    (hx : orderOf x = 2) {u v : F} (hu : u ∈ classOf z) (hv : v ∈ classOf z)
    (hux : memb K z u ≤ Subgroup.centralizer ({x} : Set F))
    (hvx : memb K z v ≤ Subgroup.centralizer ({x} : Set F)) :
    CommOrEq (memb K z u) (memb K z v) :=
  S.IH x hx (S.centralizer_ne_top (by rintro rfl; rw [orderOf_one] at hx; omega)) _ _ u v
    ((S.tight.memb hu).classical.mono hux le_top) ((S.tight.memb hv).classical.mono hvx le_top)

omit [Finite F] in
theorem TightSetting.mem_centralizer_of_commOrEq (S : TightSetting F K z) {u v : F}
    (hv : v ∈ classOf z) (h : CommOrEq (memb K z u) (memb K z v)) {k : F} (hk : k ∈ memb K z u) :
    k * v = v * k := by
  rcases h with h | h
  · rw [h] at hk
    exact (S.tight.memb hv).classical.mul_comm_of_mem hk
  · exact h k hk v (S.mem_memb hv)

omit [Finite F] in
theorem TightSetting.commOrEq_trans (S : TightSetting F K z) {u v w : F} (hu : u ∈ classOf z)
    (hv : v ∈ classOf z) (hw : w ∈ classOf z) (h1 : CommOrEq (memb K z u) (memb K z v))
    (h2 : CommOrEq (memb K z v) (memb K z w)) : CommOrEq (memb K z u) (memb K z w) := by
  have hc : ∀ {a : F}, a ∈ classOf z → CommOrEq (memb K z a) (memb K z v) →
      memb K z a ≤ Subgroup.centralizer ({v} : Set F) := fun {a} _ h k hk =>
    Subgroup.mem_centralizer_iff.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact (S.mem_centralizer_of_commOrEq hv h hk).symm)
  exact S.commOrEq_of_le_centralizer (orderOf_eq_two_of_mem_classOf S.tight hv) hu hw (hc hu h1) (hc hw h2.symm)

omit [Finite F] in
theorem TightSetting.self_mem_Zset (S : TightSetting F K z) : z ∈ Zset K z :=
  ⟨mem_classOf_self z, by rw [memb_self S.tight]; exact CommOrEq.refl K⟩

omit [Finite F] in
theorem TightSetting.commOrEq_of_mem_Zset (S : TightSetting F K z) {u v : F} (hu : u ∈ Zset K z)
    (hv : v ∈ Zset K z) : CommOrEq (memb K z u) (memb K z v) := by
  refine S.commOrEq_trans hu.1 (mem_classOf_self z) hv.1 ?_ ?_
  · rw [memb_self S.tight]; exact hu.2.symm
  · rw [memb_self S.tight]; exact hv.2

omit [Finite F] in
theorem TightSetting.mem_centralizer_memb_of_mem_Zset (S : TightSetting F K z) {u v : F}
    (hu : u ∈ Zset K z) (hv : v ∈ Zset K z) : u ∈ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact S.mem_centralizer_of_commOrEq hu.1 (S.commOrEq_of_mem_Zset hv hu) hk

omit [Finite F] in
theorem TightSetting.closure_Zset_le_centralizer (S : TightSetting F K z) {v : F}
    (hv : v ∈ Zset K z) :
    Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) :=
  (Subgroup.closure_le _).mpr fun _ hu => S.mem_centralizer_memb_of_mem_Zset hu hv

omit [Finite F] in
theorem TightSetting.Zset_commute (S : TightSetting F K z) {u v : F} (hu : u ∈ Zset K z)
    (hv : v ∈ Zset K z) : u * v = v * u :=
  (Subgroup.mem_centralizer_iff.mp (S.mem_centralizer_memb_of_mem_Zset hu hv) v
    (S.mem_memb hv.1)).symm

omit [Finite F] in
theorem TightSetting.E_centralizes (S : TightSetting F K z) {x w : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) (hw : w ∈ Zset K z) : x * w = w * x := by
  have : Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ({w} : Set F) := by
    rw [Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (S.Zset_commute hu hw).symm
  exact (Subgroup.mem_centralizer_iff.mp (this hx) w rfl).symm

omit [Finite F] in
theorem TightSetting.E_comm (S : TightSetting F K z) {x y : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) (hy : y ∈ Subgroup.closure (Zset K z)) :
    x * y = y * x := by
  have : Subgroup.closure (Zset K z) ≤ Subgroup.centralizer ({x} : Set F) := by
    rw [Subgroup.closure_le]
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact S.E_centralizes hx hw
  exact Subgroup.mem_centralizer_iff.mp (this hy) x rfl

omit [Finite F] in
theorem TightSetting.E_sq (S : TightSetting F K z) {x : F}
    (hx : x ∈ Subgroup.closure (Zset K z)) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    have := orderOf_eq_two_of_mem_classOf S.tight hx.1
    have h2 := pow_orderOf_eq_one x
    rwa [this, pow_two] at h2
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc := S.E_comm hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy]; group
  | inv x hx ih =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ih]; simp

omit [Finite F] in
theorem le_centralizer_singleton_of_mem_centralizer {H : Subgroup F} {e : F}
    (he : e ∈ Subgroup.centralizer (H : Set F)) : H ≤ Subgroup.centralizer ({e} : Set F) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff] at he ⊢
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  exact (he k hk).symm

omit [Finite F] in
theorem TightSetting.memb_le_centralizer_iff (S : TightSetting F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) {w : F} (hw : w ∈ classOf z) :
    memb K z w ≤ Subgroup.centralizer ({e} : Set F) ↔ w ∈ Zset K z := by
  constructor
  · intro h
    have hK : memb K z z ≤ Subgroup.centralizer ({e} : Set F) :=
      le_centralizer_singleton_of_mem_centralizer (S.closure_Zset_le_centralizer S.self_mem_Zset he)
    have := S.commOrEq_of_le_centralizer (orderOf_eq_prime (by rw [pow_two]; exact S.E_sq he) he1)
      (mem_classOf_self z) hw hK h
    rw [memb_self S.tight] at this
    exact ⟨hw, this⟩
  · intro hwZ
    exact le_centralizer_singleton_of_mem_centralizer (S.closure_Zset_le_centralizer hwZ he)

omit [Finite F] in
theorem TightSetting.conj_mem_Zset (S : TightSetting F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) {c : F}
    (hc : c ∈ Subgroup.centralizer ({e} : Set F)) {w : F} (hw : w ∈ Zset K z) :
    c * w * c⁻¹ ∈ Zset K z := by
  have hcw : c * w * c⁻¹ ∈ classOf z := mem_classOf_conj hw.1 c
  have hwle := (S.memb_le_centralizer_iff he he1 hw.1).mpr hw
  rw [← S.memb_le_centralizer_iff he he1 hcw, memb_conj S.tight hw.1 c]
  rintro _ ⟨y, hy, rfl⟩
  have hy' : e * y = y * e := Subgroup.mem_centralizer_iff.mp (hwle hy) e rfl
  have hc' : e * c = c * e := Subgroup.mem_centralizer_iff.mp hc e rfl
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  show e * (c * y * c⁻¹) = c * y * c⁻¹ * e
  have hc'' : c⁻¹ * e = e * c⁻¹ := by
    calc c⁻¹ * e = c⁻¹ * e * c * c⁻¹ := by group
      _ = c⁻¹ * (e * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * e) * c⁻¹ := by rw [hc']
      _ = e * c⁻¹ := by group
  calc e * (c * y * c⁻¹) = (e * c) * y * c⁻¹ := by group
    _ = c * e * y * c⁻¹ := by rw [hc']
    _ = c * (e * y) * c⁻¹ := by group
    _ = c * (y * e) * c⁻¹ := by rw [hy']
    _ = c * y * (e * c⁻¹) := by group
    _ = c * y * (c⁻¹ * e) := by rw [hc'']
    _ = c * y * c⁻¹ * e := by group

omit [Finite F] in
theorem TightSetting.centralizer_le_setNormalizer (S : TightSetting F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) :
    Subgroup.centralizer ({e} : Set F) ≤ Subgroup.normalizer (Zset K z) := by
  intro c hc
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · exact S.conj_mem_Zset he he1 hc
  · intro hn
    have hc' : c⁻¹ ∈ Subgroup.centralizer ({e} : Set F) := Subgroup.inv_mem _ hc
    have := S.conj_mem_Zset he he1 hc' hn
    simpa [mul_assoc] using this

theorem TightSetting.mem_Zset_of_commute (S : TightSetting F K z) {u : F} (hu : u ∈ classOf z)
    (hcomm : u * z = z * u) : u ∈ Zset K z := by
  have hz := S.tight.classical
  have hTL := S.tight.memb hu
  have hKz : memb K z z = K := memb_self S.tight
  have hunorm : u ∈ Subgroup.normalizer (K : Set F) := S.tight.tight (by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hcomm.symm)
  have hu2 : u * u = 1 := hTL.classical.mul_self
  obtain ⟨R, hRK, hR2, hR8, hRcomm⟩ := exists_two_subgroup_centralizing hz.witness hunorm hu2
  have hRC : R ≤ Subgroup.centralizer ({u} : Set F) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact hRcomm r hr
  have hRN : R ≤ Subgroup.normalizer (memb K z u : Set F) := fun r hr => hTL.tight (hRC hr)
  have huniq : ∀ x ∈ R, orderOf x = 2 → x = z := fun x hx hx2 =>
    hz.eq_of_orderOf_eq_two (hRK hx) hx2
  have hzR : z ∈ R := by
    have hdvd : 2 ∣ Nat.card R := by
      obtain ⟨k, hk⟩ := hR2.exists_card_eq
      rw [hk] at hR8 ⊢
      have : k ≠ 0 := by
        rintro rfl
        simp at hR8
      exact dvd_pow_self 2 this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have : (x : F) = z := huniq x x.2 (by rw [Subgroup.orderOf_coe]; exact hx)
    rw [← this]
    exact x.2
  have htriv := oddQuotAut_conjOn_eq_one_of_card hTL.classical.witness hRN hR2 hzR huniq (by omega)
  have hzN : z ∈ Subgroup.normalizer (memb K z u : Set F) := hRN hzR
  have hL : memb K z u ≤ Subgroup.centralizer ({z} : Set F) := by
    have hzc := centralizes_of_oddQuotAut_eq_one hTL.classical.perfect
      (S.P1 _ u hTL.classical) hzN htriv
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (hzc k hk).symm
  have hK : memb K z z ≤ Subgroup.centralizer ({z} : Set F) := by
    rw [hKz]; exact hz.le_centralizer
  have := S.commOrEq_of_le_centralizer (orderOf_eq_two_of_mem_classOf S.tight (mem_classOf_self z)) (mem_classOf_self z) hu hK hL
  rw [hKz] at this
  exact ⟨hu, this⟩

omit [Finite F] in
theorem classOf_eq_of_mem {x : F} (hx : x ∈ classOf z) : classOf x = classOf z := by
  obtain ⟨h, rfl⟩ := hx
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g * h, by group⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g * h⁻¹, by group⟩

omit [Finite F] in
theorem memb_memb (h : IsTight K z) {x u : F} (hx : x ∈ classOf z) (hu : u ∈ classOf z) :
    memb (memb K z x) x u = memb K z u := by
  obtain ⟨h₀, hh₀⟩ := hx
  obtain ⟨g, hg⟩ := hu
  have hT : IsTight (memb K z x) x := h.memb ⟨h₀, hh₀⟩
  have e1 : (g * h₀⁻¹) * x * (g * h₀⁻¹)⁻¹ = u := by rw [← hh₀, ← hg]; group
  have e2 : g * h₀⁻¹ * h₀ = g := by group
  rw [memb_eq hT e1, memb_eq h hh₀, memb_eq h hg, map_map_conj, e2]

omit [Finite F] in
theorem TightSetting.rebase (S : TightSetting F K z) {x : F} (hx : x ∈ classOf z) :
    TightSetting F (memb K z x) x :=
  ⟨S.tight.memb hx, S.center_trivial, S.IH, S.P1⟩

theorem TightSetting.commOrEq_of_commute (S : TightSetting F K z) {x u : F} (hx : x ∈ classOf z)
    (hu : u ∈ classOf z) (hcomm : u * x = x * u) :
    CommOrEq (memb K z x) (memb K z u) := by
  have hu' : u ∈ classOf x := by rw [classOf_eq_of_mem hx]; exact hu
  have := (S.rebase hx).mem_Zset_of_commute hu' hcomm
  have h2 := this.2
  rwa [memb_memb S.tight hx hu] at h2

variable (K z) in
@[expose] noncomputable def cliqueSub : Subgroup F := ⨆ (w : F) (_ : w ∈ Zset K z), memb K z w

omit [Finite F] in
theorem memb_le_cliqueSub {w : F} (hw : w ∈ Zset K z) : memb K z w ≤ cliqueSub K z :=
  le_iSup₂ (f := fun (w : F) (_ : w ∈ Zset K z) => memb K z w) w hw

omit [Finite F] in
theorem TightSetting.cliqueSub_le_normalizer (S : TightSetting F K z) {v : F} (hv : v ∈ Zset K z) :
    cliqueSub K z ≤ Subgroup.normalizer (memb K z v : Set F) := by
  refine iSup₂_le fun w hw => ?_
  rcases S.commOrEq_of_mem_Zset hw hv with h | h
  · rw [h]
    exact Subgroup.le_normalizer
  · intro g hg
    have hc : g ∈ Subgroup.centralizer ((memb K z v : Subgroup F) : Set F) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (h g hg x hx).symm
    exact Subgroup.centralizer_le_normalizer ((memb K z v : Subgroup F) : Set F) hc

omit [Finite F] in
theorem TightSetting.cliqueSub_le_centralizer (S : TightSetting F K z) {e : F}
    (he : e ∈ Subgroup.closure (Zset K z)) (he1 : e ≠ 1) :
    cliqueSub K z ≤ Subgroup.centralizer ({e} : Set F) :=
  iSup₂_le fun _ hw => (S.memb_le_centralizer_iff he he1 hw.1).mpr hw

omit [Finite F] in
theorem TightSetting.conj_mem_cliqueSub (S : TightSetting F K z) {g : F}
    (hg : g ∈ Subgroup.normalizer (Zset K z)) {x : F} (hx : x ∈ cliqueSub K z) :
    g * x * g⁻¹ ∈ cliqueSub K z := by
  have h : (cliqueSub K z).map (MulAut.conj g).toMonoidHom ≤ cliqueSub K z := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun w hw => ?_
    intro x hx
    have hgw : g * w * g⁻¹ ∈ Zset K z := (Subgroup.mem_set_normalizer_iff.mp hg w).mp hw
    have hxm : g * x * g⁻¹ ∈ memb K z (g * w * g⁻¹) := by
      rw [memb_conj S.tight hw.1 g]
      exact ⟨x, hx, rfl⟩
    exact memb_le_cliqueSub hgw hxm
  exact h ⟨x, hx, rfl⟩

theorem TightSetting.mem_Zset_of_commute_Zset (S : TightSetting F K z) {x u : F}
    (hx : x ∈ Zset K z) (hu : u ∈ classOf z) (hcomm : u * x = x * u) : u ∈ Zset K z := by
  have h2 := S.commOrEq_of_commute hx.1 hu hcomm
  have h1 : CommOrEq (memb K z z) (memb K z x) := by rw [memb_self S.tight]; exact hx.2
  have := S.commOrEq_trans (mem_classOf_self z) hx.1 hu h1 h2
  rw [memb_self S.tight] at this
  exact ⟨hu, this⟩

end Clique

section Diagonal

variable {F : Type*} [Group F] {K : Subgroup F} {u : F}

@[expose] def diagHom (K : Subgroup F) (u : F)
    (hKc : ∀ k ∈ K, ∀ k' ∈ K, k * (u * k' * u⁻¹) = (u * k' * u⁻¹) * k) : ↥K →* F :=
  MonoidHom.mk' (fun k => (k : F) * (u * k * u⁻¹)) (by
    intro k₁ k₂
    have h1 := hKc k₂ k₂.2 k₁ k₁.2
    calc ((k₁ * k₂ : ↥K) : F) * (u * ((k₁ * k₂ : ↥K) : F) * u⁻¹)
        = k₁ * k₂ * ((u * k₁ * u⁻¹) * (u * k₂ * u⁻¹)) := by simp [mul_assoc]
      _ = k₁ * (k₂ * (u * k₁ * u⁻¹)) * (u * k₂ * u⁻¹) := by group
      _ = k₁ * ((u * k₁ * u⁻¹) * k₂) * (u * k₂ * u⁻¹) := by rw [h1]
      _ = ((k₁ : F) * (u * k₁ * u⁻¹)) * ((k₂ : F) * (u * k₂ * u⁻¹)) := by group)

theorem diagHom_apply (hKc : ∀ k ∈ K, ∀ k' ∈ K, k * (u * k' * u⁻¹) = (u * k' * u⁻¹) * k)
    (k : ↥K) : diagHom K u hKc k = (k : F) * (u * k * u⁻¹) := rfl

end Diagonal

section Swap

variable {F : Type*} [Group F] [Finite F] {K : Subgroup F} {z : F}

omit [Finite F] in
theorem TightSetting.swap_data (S : TightSetting F K z) {u : F}
    (hN : u ∈ Subgroup.normalizer (Zset K z)) (hfix : ∀ x ∈ Zset K z, u * x * u⁻¹ ≠ x) :
    u * z * u⁻¹ ∈ Zset K z ∧ u * z * u⁻¹ ≠ z ∧ z * (u * z * u⁻¹) = (u * z * u⁻¹) * z ∧
      z * (u * z * u⁻¹) ∈ Subgroup.closure (Zset K z) ∧ z * (u * z * u⁻¹) ≠ 1 := by
  have hKz := S.tight.classical
  have hz2 : z * z = 1 := hKz.mul_self
  obtain ⟨b, hb⟩ : ∃ b : F, b = u * z * u⁻¹ := ⟨_, rfl⟩
  have hbZ : b ∈ Zset K z := by
    rw [hb]; exact (Subgroup.mem_set_normalizer_iff.mp hN z).mp S.self_mem_Zset
  have hbz : b ≠ z := by
    intro h; exact hfix z S.self_mem_Zset (by rw [← hb]; exact h)
  have hcoZ : CommOrEq (memb K z z) (memb K z b) := S.commOrEq_of_mem_Zset S.self_mem_Zset hbZ
  have hzb : z * b = b * z := S.mem_centralizer_of_commOrEq (u := z) (v := b) hbZ.1 hcoZ
    (S.mem_memb (mem_classOf_self z))
  have hb2 : b * b = 1 := by
    have hb' : b = u * z * u⁻¹ := hb
    have : orderOf b = 2 := orderOf_eq_two_of_mem_classOf S.tight hbZ.1
    have h2 := pow_orderOf_eq_one b
    rwa [this, pow_two] at h2
  have he1 : z * b ≠ 1 := by
    intro h
    apply hbz
    have h1 : b = z⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hz2
  rw [← hb]
  exact ⟨hbZ, hbz, hzb, Subgroup.mul_mem _ (Subgroup.subset_closure S.self_mem_Zset)
    (Subgroup.subset_closure hbZ), he1⟩

theorem TightSetting.swap_lemma (S : TightSetting F K z) {u : F} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hN : u ∈ Subgroup.normalizer (Zset K z)) (hfix : ∀ x ∈ Zset K z, u * x * u⁻¹ ≠ x)
    {L : Subgroup F} {v : F} (hL : IsClassical2A7 ⊤ L v)
    (hLu : L ≤ Subgroup.centralizer ({u} : Set F)) :
    v = z * (u * z * u⁻¹) ∨ L ≤ Subgroup.centralizer ({z * (u * z * u⁻¹)} : Set F) := by
  have hKz := S.tight.classical
  have hz2 : z * z = 1 := hKz.mul_self
  have hzK : z ∈ K := hKz.mem
  obtain ⟨hbZ', hbz', hzb', he_clos', he1'⟩ := S.swap_data hN hfix
  obtain ⟨b, hb⟩ : ∃ b : F, b = u * z * u⁻¹ := ⟨_, rfl⟩
  rw [← hb] at hbZ' hbz' hzb' he_clos' he1' ⊢
  have hbZ := hbZ'
  have hbz := hbz'
  have hzb := hzb'
  have he_clos := he_clos'
  have he1 := he1'
  have hb2 : b * b = 1 := by
    have : orderOf b = 2 := orderOf_eq_two_of_mem_classOf S.tight hbZ.1
    have h2 := pow_orderOf_eq_one b
    rwa [this, pow_two] at h2
  have hbmemb : memb K z b = K.map (MulAut.conj u).toMonoidHom := by
    rw [hb, memb_conj S.tight (mem_classOf_self z) u, memb_self S.tight]
  have hcoZ : CommOrEq (memb K z z) (memb K z b) := S.commOrEq_of_mem_Zset S.self_mem_Zset hbZ
  have hKcomm : ∀ k ∈ K, ∀ k' ∈ K, k * (u * k' * u⁻¹) = (u * k' * u⁻¹) * k := by
    have hco := hcoZ
    rw [memb_self S.tight, hbmemb] at hco
    rcases hco with h | h
    · exfalso
      apply hbz
      have hbK : b ∈ K := by
        rw [hb]
        have : u * z * u⁻¹ ∈ K.map (MulAut.conj u).toMonoidHom := ⟨z, hzK, rfl⟩
        rwa [← h] at this
      exact hKz.eq_of_orderOf_eq_two hbK (orderOf_eq_two_of_mem_classOf S.tight hbZ.1)
    · intro k hk k' hk'
      exact h k hk _ ⟨k', hk', rfl⟩
  have heord : orderOf (z * b) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; calc z * b * (z * b) = z * (b * z) * b := by group
      _ = z * (z * b) * b := by rw [hzb]
      _ = (z * z) * (b * b) := by group
      _ = 1 := by rw [hz2, hb2]; group) he1
  let φ : ↥K →* F := diagHom K u hKcomm
  let Δ : Subgroup F := φ.range
  have hφz : φ ⟨z, hzK⟩ = z * b := by
    show z * (u * z * u⁻¹) = z * b
    rw [← hb]
  have hΔmem : z * b ∈ Δ := ⟨⟨z, hzK⟩, hφz⟩
  have hKle : K ≤ cliqueSub K z := by
    have := memb_le_cliqueSub (K := K) (z := z) S.self_mem_Zset
    rwa [memb_self S.tight] at this
  have hKule : K.map (MulAut.conj u).toMonoidHom ≤ cliqueSub K z := by
    have := memb_le_cliqueSub (K := K) (z := z) hbZ
    rwa [hbmemb] at this
  have hΔle : Δ ≤ cliqueSub K z := by
    rintro _ ⟨k, rfl⟩
    exact Subgroup.mul_mem _ (hKle k.2) (hKule ⟨k, k.2, rfl⟩)
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hΔcu : ∀ x ∈ Δ, u * x = x * u := by
    rintro _ ⟨k, rfl⟩
    have h1 := hKcomm k k.2 k k.2
    show u * ((k : F) * (u * k * u⁻¹)) = ((k : F) * (u * k * u⁻¹)) * u
    calc u * ((k : F) * (u * k * u⁻¹)) = (u * k * u⁻¹) * (u * (u * k * u⁻¹) * u⁻¹) * u := by group
      _ = (u * k * u⁻¹) * k * u := by
        congr 2
        rw [hui]
        calc u * (u * (k : F) * u) * u = (u * u) * k * (u * u) := by group
          _ = k := by rw [hu2]; group
      _ = ((k : F) * (u * k * u⁻¹)) * u := by rw [← h1]
  have hDVK : cliqueSub K z ≤ Subgroup.normalizer (K : Set F) := by
    have := S.cliqueSub_le_normalizer (S.self_mem_Zset)
    rwa [memb_self S.tight] at this
  set M₁ : Subgroup F := cliqueSub K z ⊓ Subgroup.centralizer ({u} : Set F) with hM₁
  have hΔM₁ : Δ ≤ M₁ := fun x hx =>
    ⟨hΔle hx, Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]; exact hΔcu x hx⟩
  have hΔnormal : (Δ.subgroupOf M₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hΔM₁]
    rintro _ d ⟨k, rfl⟩ hd
    have hdK : d ∈ Subgroup.normalizer (K : Set F) := hDVK hd.1
    have hdu : u * d = d * u := Subgroup.mem_centralizer_iff.mp hd.2 u rfl
    have hk2 : d * (k : F) * d⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hdK k).mp k.2
    refine ⟨⟨d * (k : F) * d⁻¹, hk2⟩, ?_⟩
    show (d * (k : F) * d⁻¹) * (u * (d * (k : F) * d⁻¹) * u⁻¹) =
      d * ((k : F) * (u * k * u⁻¹)) * d⁻¹
    calc (d * (k : F) * d⁻¹) * (u * (d * (k : F) * d⁻¹) * u⁻¹)
        = d * (k : F) * d⁻¹ * ((u * d) * k * (u * d)⁻¹) := by group
      _ = d * (k : F) * d⁻¹ * ((d * u) * k * (d * u)⁻¹) := by rw [hdu]
      _ = d * ((k : F) * (u * k * u⁻¹)) * d⁻¹ := by group
  have hM₁le : M₁ ≤ Subgroup.centralizer ({u} : Set F) ⊓ Subgroup.centralizer ({z * b} : Set F) :=
    fun x hx => ⟨hx.2, S.cliqueSub_le_centralizer he_clos he1 hx.1⟩
  have hM₁normal : (M₁.subgroupOf (Subgroup.centralizer ({u} : Set F) ⊓
      Subgroup.centralizer ({z * b} : Set F))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hM₁le]
    rintro m g hm hg
    have hgN := S.centralizer_le_setNormalizer he_clos he1 hg.2
    have hgu : u * g = g * u := Subgroup.mem_centralizer_iff.mp hg.1 u rfl
    have hmu : u * m = m * u := Subgroup.mem_centralizer_iff.mp hm.2 u rfl
    refine ⟨S.conj_mem_cliqueSub hgN hm.1, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    calc u * (g * m * g⁻¹) = (u * g) * m * g⁻¹ := by group
      _ = g * (u * m) * g⁻¹ := by rw [hgu]; group
      _ = g * (m * u) * g⁻¹ := by rw [hmu]
      _ = g * m * (u * g⁻¹) := by group
      _ = g * m * (g⁻¹ * u) := by
        congr 1
        calc u * g⁻¹ = g⁻¹ * (g * u) * g⁻¹ := by group
          _ = g⁻¹ * (u * g) * g⁻¹ := by rw [hgu]
          _ = g⁻¹ * u := by group
      _ = g * m * g⁻¹ * u := by group
  have hsubn : IsSubnormal Δ (Subgroup.centralizer ({u} : Set F) ⊓
      Subgroup.centralizer ({z * b} : Set F)) :=
    IsSubnormal.step hΔM₁ hΔnormal (isSubnormal_of_normal_subgroupOf hM₁le hM₁normal)
  have hΔcl : IsClassical2A7 (Subgroup.centralizer ({u} : Set F)) Δ (z * b) := by
    have := hKz.perfect
    refine ⟨heord, hΔmem, Group.IsPerfect.range φ, hsubn, ?_⟩
    have hsurj : Function.Surjective φ.rangeRestrict := MonoidHom.rangeRestrict_surjective φ
    have hker : Odd (Nat.card φ.rangeRestrict.ker) := by
      rw [MonoidHom.ker_rangeRestrict]
      by_contra hodd
      have hev : 2 ∣ Nat.card φ.ker := by
        rcases Nat.even_or_odd (Nat.card φ.ker) with h | h
        · exact even_iff_two_dvd.mp h
        · exact absurd h hodd
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hev
      have hx' : orderOf (((x : ↥K) : ↥K) : F) = 2 := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hx
      have hxz : (((x : ↥K) : ↥K) : F) = z :=
        hKz.eq_of_orderOf_eq_two (x : ↥K).2 hx'
      have hxker : φ (x : ↥K) = 1 := x.2
      have hxz' : (x : ↥K) = ⟨z, hzK⟩ := Subtype.ext hxz
      rw [hxz', hφz] at hxker
      exact he1 hxker
    exact A7Witness.of_surjective φ.rangeRestrict hsurj hker hKz.witness
  have hMu : IsClassical2A7 (Subgroup.centralizer ({u} : Set F)) L v := hL.mono hLu le_top
  have hYne : Subgroup.centralizer ({u} : Set F) ≠ ⊤ := S.centralizer_ne_top hu1
  rcases S.IH u (orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1) hYne Δ L (z * b) v hΔcl hMu with h | h
  · left
    have hΔu : z * b ∈ L := by rw [← h]; exact hΔmem
    exact (hL.eq_of_orderOf_eq_two hΔu heord).symm
  · right
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro h' hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact h _ hΔmem c hc

theorem TightSetting.mem_Zset_of_mem_normalizer (S : TightSetting F K z) {u : F}
    (hu : u ∈ classOf z) (hN : u ∈ Subgroup.normalizer (Zset K z)) : u ∈ Zset K z := by
  by_contra hnu
  have hTu := S.tight.memb hu
  have hu2 : u * u = 1 := hTu.classical.mul_self
  have hfix : ∀ x ∈ Zset K z, u * x * u⁻¹ ≠ x := by
    intro x hx hxx
    apply hnu
    refine S.mem_Zset_of_commute_Zset hx hu ?_
    have := congrArg (· * u) hxx
    simpa [mul_assoc] using this
  obtain ⟨hbZ, hbz, hzb, he_clos, he1⟩ := S.swap_data hN hfix
  rcases S.swap_lemma hu2 (S.ne_one hu) hN hfix hTu.classical hTu.classical.le_centralizer with
    h | h
  ·
    have hcz : u * z = z * u := by
      rw [h]
      calc z * (u * z * u⁻¹) * z = z * ((u * z * u⁻¹) * z) := by group
        _ = z * (z * (u * z * u⁻¹)) := by rw [← hzb]
        _ = z * (z * (u * z * u⁻¹)) := rfl
    apply hbz
    calc u * z * u⁻¹ = z * u * u⁻¹ := by rw [hcz]
      _ = z := by group
  · exact hnu ((S.memb_le_centralizer_iff he_clos he1 hu).mp h)

end Swap

end CFSG.ClassicalInvolution.Hat2A7

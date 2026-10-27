module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Fusion

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup DihedralGroup
open scoped Pointwise

namespace Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

theorem card_le_of_conjTo {g : X} (hg : ConjTo S.t g) {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hQg : Q ≤ centralizer ({g} : Set X)) : Nat.card Q ≤ 32 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := hg
  have hcard := S.card_T_eq_two_pow_of_conj hc
  have hQ' : IsPGroup 2 (Q.subgroupOf (centralizer ({g} : Set X))) :=
    hQ.comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  rw [← S.card_T, hcard, ← Sylow.card_eq_multiplicity P,
    ← Nat.card_congr (subgroupOfEquivOfLe hQg).toEquiv]
  exact Subgroup.card_le_of_le hP

theorem not_conjTo_of_card {g : X} {Q : Subgroup X} (hQ : IsPGroup 2 Q)
    (hQg : Q ≤ centralizer ({g} : Set X)) (hcard : 32 < Nat.card Q) : ¬ ConjTo S.t g :=
  fun h => absurd (card_le_of_conjTo h hQ hQg) (not_le.mpr hcard)

omit [Finite X] in
theorem isPGroup_of_elemAbelianTwo {A : Subgroup X} (hA : ElemAbelianTwo A) :
    IsPGroup 2 A := fun a => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.sq_eq_one a a.2)⟩

theorem T_not_comm : ¬ ∀ a ∈ S.data.T, ∀ b ∈ S.data.T, a * b = b * a := by
  intro h
  have h1 := S.commutator_x_y
  rw [h S.x S.x_mem.1 S.y S.y_mem.1, mul_inv_cancel_right, mul_inv_cancel] at h1
  exact S.z_ne_one h1.symm

theorem not_conjTo_of_elem {g : X} {A : Subgroup X} (hA : ElemAbelianTwo A)
    (hAg : A ≤ centralizer ({g} : Set X)) (hcard : 32 ≤ Nat.card A) : ¬ ConjTo S.t g := by
  rintro ⟨c, hc⟩
  set A' := A.map (MulAut.conj c⁻¹).toMonoidHom with hA'
  have hA'el : ElemAbelianTwo A' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show c⁻¹ * a * c⁻¹⁻¹ * (c⁻¹ * b * c⁻¹⁻¹) = c⁻¹ * (a * b) * c⁻¹⁻¹ by group,
        hA.comm a ha b hb]
      group
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hA.sq_eq_one a ha]
      group
  have hA't : A' ≤ centralizer ({S.t} : Set X) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hag := mem_centralizer_singleton_iff.mp (hAg ha)
    rw [← hc] at hag
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc c⁻¹ * a * c * S.t = c⁻¹ * (a * (c * S.t * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * S.t * c⁻¹) * a) * c := by rw [hag]
      _ = S.t * (c⁻¹ * a * c) := by group
  obtain ⟨h, -, hhT⟩ := S.data.exists_conj_le_T (isPGroup_of_elemAbelianTwo hA'el) hA't
  set A'' := A'.map (MulAut.conj h).toMonoidHom with hA''
  have hcard'' : Nat.card A'' = Nat.card A := by
    rw [hA'', card_map_of_injective (MulAut.conj h).injective, hA',
      card_map_of_injective (MulAut.conj c⁻¹).injective]
  have heq : A'' = S.data.T :=
    Subgroup.eq_of_le_of_card_ge hhT (by rw [S.card_T, hcard'']; exact hcard)
  apply T_not_comm (S := S)
  rw [← heq]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show h * a * h⁻¹ * (h * b * h⁻¹) = h * (a * b) * h⁻¹ by group, hA'el.comm a ha b hb]
  group

theorem model_central_of_comm (p : DihedralGroup 4 × DihedralGroup 2)
    (h1 : p * (r 1, 1) = (r 1, 1) * p) (h2 : p * (sr 0, 1) = (sr 0, 1) * p)
    (q : DihedralGroup 4 × DihedralGroup 2) : p * q = q * p := by
  revert p q
  decide

theorem model_centralizer_inv (a g : DihedralGroup 4 × DihedralGroup 2) (ha : a * a = 1)
    (hnc : ¬ ∀ q : DihedralGroup 4 × DihedralGroup 2, a * q = q * a) (hg : g * a = a * g) :
    (∀ q : DihedralGroup 4 × DihedralGroup 2, g * q = q * g) ∨
      ∀ q : DihedralGroup 4 × DihedralGroup 2, g * a * q = q * (g * a) := by
  revert a g
  decide

theorem coords_comm {a b : X} (ha : a ∈ S.data.T) (hb : b ∈ S.data.T) (h : a * b = b * a) :
    S.coords ⟨a, ha⟩ * S.coords ⟨b, hb⟩ = S.coords ⟨b, hb⟩ * S.coords ⟨a, ha⟩ := by
  rw [← map_mul, ← map_mul]
  exact congrArg _ (Subtype.ext h)

theorem mem_B_of_coords {g : X} (hg : g ∈ S.data.T)
    (h : ∀ q : DihedralGroup 4 × DihedralGroup 2, S.coords ⟨g, hg⟩ * q = q * S.coords ⟨g, hg⟩) :
    g ∈ S.B := by
  rw [← S.mem_B_iff hg]
  intro b hb
  have := h (S.coords ⟨b, hb⟩)
  rw [← map_mul, ← map_mul] at this
  exact congrArg Subtype.val (S.coords.injective this)

theorem mem_B_of_comm_xy {g : X} (hg : g ∈ S.data.T) (hx : g * S.x = S.x * g)
    (hy : g * S.y = S.y * g) : g ∈ S.B := by
  refine mem_B_of_coords hg (model_central_of_comm _ ?_ ?_)
  · rw [← S.coords_x]; exact coords_comm hg _ hx
  · rw [← S.coords_y]; exact coords_comm hg _ hy

theorem mem_B_or_of_comm {a g : X} (ha : a ∈ S.data.T) (ha2 : a ^ 2 = 1) (haB : a ∉ S.B)
    (hg : g ∈ S.data.T) (hga : g * a = a * g) : g ∈ S.B ∨ g * a ∈ S.B := by
  have ha' : S.coords ⟨a, ha⟩ * S.coords ⟨a, ha⟩ = 1 := by
    rw [← map_mul, ← map_one S.coords]
    congr 1
    exact Subtype.ext (by simpa [pow_two] using ha2)
  have hnc : ¬ ∀ q, S.coords ⟨a, ha⟩ * q = q * S.coords ⟨a, ha⟩ := fun h =>
    haB (mem_B_of_coords ha h)
  rcases model_centralizer_inv _ _ ha' hnc (coords_comm hg ha hga) with h | h
  · exact Or.inl (mem_B_of_coords hg h)
  · right
    refine mem_B_of_coords (mul_mem hg ha) ?_
    have : S.coords ⟨g * a, mul_mem hg ha⟩ = S.coords ⟨g, hg⟩ * S.coords ⟨a, ha⟩ :=
      map_mul S.coords ⟨g, hg⟩ ⟨a, ha⟩
    rw [this]
    exact h

theorem z_mem_B : S.z ∈ S.B := subset_closure (by simp)

theorem t_mem_B : S.t ∈ S.B := subset_closure (by simp)

theorem k_mem_B : S.k ∈ S.B := subset_closure (by simp)

theorem z_sq : S.z ^ 2 = 1 := S.sq_of_mem_B z_mem_B

theorem z_mem_T : S.z ∈ S.data.T := S.B_le_T z_mem_B

theorem commute_of_mem_B {a b : X} (ha : a ∈ S.B) (hb : b ∈ S.B) : a * b = b * a :=
  S.central_of_mem_B ha (S.B_le_T hb)

theorem elemAbelianTwo_B : ElemAbelianTwo S.B :=
  ⟨fun _ ha _ hb => commute_of_mem_B ha hb, fun _ ha => S.sq_of_mem_B ha⟩

section Frame

variable (F : S.Frame)

theorem xF_mem_T : F.xF ∈ S.data.T := F.xF_mem.1

theorem yF_mem_T : F.yF ∈ S.data.T := F.yF_mem.1

theorem kF_mem_B : F.kF ∈ S.B :=
  mem_B_of_comm_xy F.kF_mem (F.kF_comm _ S.x_mem) (F.kF_comm _ S.y_mem)

theorem kF_comm {g : X} (hg : g ∈ S.data.T) : F.kF * g = g * F.kF :=
  S.central_of_mem_B (kF_mem_B F) hg

theorem xF_pow_four : F.xF ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, F.xF_sq, z_sq]

theorem xF_inv : F.xF⁻¹ = S.z * F.xF := by
  rw [inv_eq_iff_mul_eq_one, ← F.xF_sq, ← xF_pow_four F]
  group

theorem yF_inv : F.yF⁻¹ = F.yF := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, F.yF_sq]

theorem xF_ne_inv : F.xF ≠ F.xF⁻¹ := by
  intro h
  have : F.xF ^ 2 = 1 := by rw [pow_two]; nth_rw 2 [h]; exact mul_inv_cancel _
  rw [F.xF_sq] at this
  exact S.z_ne_one this

theorem yF_mul_xF : F.yF * F.xF = F.xF⁻¹ * F.yF := by
  rw [← F.yF_inv]; group

theorem xyF_mem_R : F.xF * F.yF ∈ S.data.R := mul_mem F.xF_mem F.yF_mem

theorem xyF_sq : (F.xF * F.yF) ^ 2 = 1 := by
  rw [pow_two, mul_assoc, ← mul_assoc F.yF, yF_mul_xF, mul_assoc, ← pow_two F.yF, F.yF_sq,
    mul_one, mul_inv_cancel]

theorem xyF_inv : (F.xF * F.yF) * F.xF * (F.xF * F.yF)⁻¹ = F.xF⁻¹ := by
  rw [mul_inv_rev, yF_inv]
  calc F.xF * F.yF * F.xF * (F.yF * F.xF⁻¹) = F.xF * (F.yF * F.xF * F.yF⁻¹) * F.xF⁻¹ := by
        rw [yF_inv]; group
    _ = F.xF⁻¹ := by rw [F.yF_inv]; group

theorem xF_conj_yF : F.xF * F.yF * F.xF⁻¹ = S.z * F.yF := by
  have h : F.yF * F.xF⁻¹ = F.xF * F.yF := by
    have := F.yF_inv
    calc F.yF * F.xF⁻¹ = (F.yF * F.xF * F.yF⁻¹)⁻¹ * F.yF := by group
      _ = F.xF * F.yF := by rw [F.yF_inv]; group
  rw [mul_assoc, h, ← mul_assoc, ← pow_two, F.xF_sq]

end Frame

theorem elemAbelianTwo_sup {V : Subgroup X} (hV : ElemAbelianTwo V) {g : X} (hg2 : g ^ 2 = 1)
    (hgc : ∀ a ∈ V, g * a = a * g) : ElemAbelianTwo (V ⊔ zpowers g) := by
  by_cases hgV : g ∈ V
  · rwa [sup_eq_left.mpr (zpowers_le.mpr hgV)]
  · exact (hV.sup_zpowers hg2 hgV hgc).1

theorem card_sup_of_not_mem {V : Subgroup X} (hV : ElemAbelianTwo V) {g : X} (hg2 : g ^ 2 = 1)
    (hgV : g ∉ V) (hgc : ∀ a ∈ V, g * a = a * g) :
    Nat.card (V ⊔ zpowers g : Subgroup X) = 2 * Nat.card V :=
  (hV.sup_zpowers hg2 hgV hgc).2.2

theorem mem_or_of_mem_sup {V : Subgroup X} (hV : ElemAbelianTwo V) {g : X} (hg2 : g ^ 2 = 1)
    (hgc : ∀ a ∈ V, g * a = a * g) {a : X} (ha : a ∈ V ⊔ zpowers g) : a ∈ V ∨ a * g ∈ V := by
  by_cases hgV : g ∈ V
  · rw [sup_eq_left.mpr (zpowers_le.mpr hgV)] at ha
    exact Or.inl ha
  · exact (hV.sup_zpowers hg2 hgV hgc).2.1 a ha

omit [Finite X] in
theorem closure_pair_eq (a b : X) : closure ({a, b} : Set X) = zpowers a ⊔ zpowers b := by
  rw [Set.insert_eq, Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]

omit [Finite X] in
theorem closure_triple_eq (a b c : X) :
    closure ({a, b, c} : Set X) = zpowers a ⊔ zpowers b ⊔ zpowers c := by
  rw [Set.insert_eq, Subgroup.closure_union, closure_pair_eq, ← zpowers_eq_closure, sup_assoc]

omit [Finite X] in
theorem closure_quad_eq (a b c d : X) :
    closure ({a, b, c, d} : Set X) = zpowers a ⊔ zpowers b ⊔ zpowers c ⊔ zpowers d := by
  rw [Set.insert_eq, Subgroup.closure_union, closure_triple_eq, ← zpowers_eq_closure,
    sup_assoc, sup_assoc, sup_assoc]

theorem B_eq : S.B = zpowers S.z ⊔ zpowers S.t ⊔ zpowers S.k := closure_triple_eq _ _ _

theorem zt_le_B : (zpowers S.z ⊔ zpowers S.t : Subgroup X) ≤ S.B := by
  rw [B_eq]; exact le_sup_left

theorem E_eq (yi : X) : S.E yi = S.B ⊔ zpowers yi := by
  rw [A7Base.E, B_eq, closure_quad_eq]
  ac_rfl

structure IsRefl (F : S.Frame) (yi : X) : Prop where
  mem : yi ∈ S.data.R
  sq : yi ^ 2 = 1
  inv : yi * F.xF * yi⁻¹ = F.xF⁻¹

theorem isRefl_yF (F : S.Frame) : IsRefl F F.yF := ⟨F.yF_mem, F.yF_sq, F.yF_inv⟩

theorem isRefl_xyF (F : S.Frame) : IsRefl F (F.xF * F.yF) :=
  ⟨xyF_mem_R F, xyF_sq F, xyF_inv F⟩

variable {F : S.Frame} {yi : X}

theorem IsRefl.mem_T (h : IsRefl F yi) : yi ∈ S.data.T := h.mem.1

theorem IsRefl.not_mem_B (h : IsRefl F yi) : yi ∉ S.B := by
  intro hB
  have hc := S.central_of_mem_B hB (xF_mem_T F)
  have : yi * F.xF * yi⁻¹ = F.xF := by rw [hc, mul_inv_cancel_right]
  exact xF_ne_inv F (this.symm.trans h.inv)

theorem IsRefl.comm_B (h : IsRefl F yi) {b : X} (hb : b ∈ S.B) : yi * b = b * yi :=
  (S.central_of_mem_B hb h.mem_T).symm

theorem IsRefl.elemAbelianTwo_E (h : IsRefl F yi) : ElemAbelianTwo (S.E yi) := by
  rw [E_eq]
  exact elemAbelianTwo_sup elemAbelianTwo_B h.sq fun _ hb => h.comm_B hb

theorem IsRefl.card_E (h : IsRefl F yi) : Nat.card (S.E yi) = 16 := by
  rw [E_eq, card_sup_of_not_mem elemAbelianTwo_B h.sq h.not_mem_B fun _ hb => h.comm_B hb,
    S.card_B]

theorem B_le_E (yi : X) : S.B ≤ S.E yi := by rw [E_eq]; exact le_sup_left

theorem mem_E_self (yi : X) : yi ∈ S.E yi := by rw [E_eq]; exact mem_sup_right (mem_zpowers _)

theorem t_mem_E (yi : X) : S.t ∈ S.E yi := B_le_E yi t_mem_B

theorem z_mem_E (yi : X) : S.z ∈ S.E yi := B_le_E yi z_mem_B

theorem kF_mem_E (F : S.Frame) (yi : X) : F.kF ∈ S.E yi := B_le_E yi (kF_mem_B F)

theorem IsRefl.E_le_T (h : IsRefl F yi) : S.E yi ≤ S.data.T := by
  rw [E_eq]; exact sup_le S.B_le_T (zpowers_le.mpr h.mem_T)

theorem IsRefl.mem_E_of_comm (h : IsRefl F yi) {g : X} (hg : g ∈ S.data.T)
    (hgy : g * yi = yi * g) : g ∈ S.E yi := by
  rcases mem_B_or_of_comm h.mem_T h.sq h.not_mem_B hg hgy with hB | hB
  · exact B_le_E yi hB
  · have := mul_mem (B_le_E yi hB) (inv_mem (mem_E_self yi))
    rwa [mul_inv_cancel_right] at this

theorem eq_of_elem_le_T {A : Subgroup X} (hA : ElemAbelianTwo A) (hAT : A ≤ S.data.T)
    (hcard : Nat.card A = 16) {g : X} (hg : g ∈ S.data.T) (hgA : ∀ a ∈ A, g * a = a * g) :
    g ∈ A := by
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ S.B := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show A ≤ S.B from hall)
    rw [hcard, S.card_B] at this
    omega
  have ha2 := hA.sq_eq_one a haA
  have hBa : ElemAbelianTwo (S.B ⊔ zpowers a) :=
    elemAbelianTwo_sup elemAbelianTwo_B ha2 fun _ hb => (S.central_of_mem_B hb (hAT haA)).symm
  have hcardBa : Nat.card (S.B ⊔ zpowers a : Subgroup X) = 16 := by
    rw [card_sup_of_not_mem elemAbelianTwo_B ha2 haB
      (fun _ hb => (S.central_of_mem_B hb (hAT haA)).symm), S.card_B]
  have hC : ∀ c ∈ S.data.T, c * a = a * c → c ∈ S.B ⊔ zpowers a := by
    intro c hc hca
    rcases mem_B_or_of_comm (hAT haA) ha2 haB hc hca with hB | hB
    · exact mem_sup_left hB
    · have := mul_mem (show c * a ∈ S.B ⊔ zpowers a from mem_sup_left hB)
        (inv_mem (mem_sup_right (mem_zpowers a)))
      rwa [mul_inv_cancel_right] at this
  have hAle : A ≤ S.B ⊔ zpowers a := fun b hb => hC b (hAT hb) (hA.comm b hb a haA)
  have heq : A = S.B ⊔ zpowers a := Subgroup.eq_of_le_of_card_ge hAle (by rw [hcardBa, hcard])
  rw [heq]
  exact hC g hg (hgA a haA)

theorem le_of_le_centralizer {A : Subgroup X} (hA : ElemAbelianTwo A)
    (hcard : Nat.card A = 16) (htA : S.t ∈ A) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hPA : P ≤ centralizer (A : Set X)) : P ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAC : A ≤ centralizer (A : Set X) := fun a ha =>
    mem_centralizer_iff.mpr fun b hb => hA.comm b hb a ha
  have hQC : P ⊔ A ≤ centralizer (A : Set X) := sup_le hPA hAC
  have hQ : IsPGroup 2 (P ⊔ A : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hP (isPGroup_of_elemAbelianTwo hA)
      (hPA.trans (centralizer_le_normalizer _))
  have hQt : P ⊔ A ≤ centralizer ({S.t} : Set X) := fun q hq =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hQC hq)) S.t htA).symm
  obtain ⟨c, -, hcT⟩ := S.data.exists_conj_le_T hQ hQt
  set φ := (MulAut.conj c).toMonoidHom with hφ
  have hA' : ElemAbelianTwo (A.map φ) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hA.comm a ha b hb]
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hA.sq_eq_one a ha, map_one]
  have hA'T : A.map φ ≤ S.data.T := (map_mono le_sup_right).trans hcT
  have hcard' : Nat.card (A.map φ) = 16 := by
    rw [card_map_of_injective (MulAut.conj c).injective, hcard]
  intro p hp
  have hmem : φ p ∈ A.map φ := by
    refine eq_of_elem_le_T hA' hA'T hcard' (hcT ⟨p, mem_sup_left hp, rfl⟩) ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hPA hp)) a ha]
  obtain ⟨a, ha, hap⟩ := hmem
  rwa [(MulAut.conj c).injective hap] at ha

structure IsK (ki : X) : Prop where
  mem : ki ∈ S.B
  not_mem : ki ∉ (zpowers S.z ⊔ zpowers S.t : Subgroup X)

theorem zt_le_RK : (zpowers S.z ⊔ zpowers S.t : Subgroup X) ≤ S.data.R ⊔ S.data.K :=
  sup_le (zpowers_le.mpr (mem_sup_left S.z_mem)) (zpowers_le.mpr (mem_sup_right S.data.t_mem_K))

theorem isK_kF (F : S.Frame) : IsK (S := S) F.kF :=
  ⟨kF_mem_B F, fun h => F.kF_not_mem (zt_le_RK h)⟩

theorem isK_zkF (F : S.Frame) : IsK (S := S) (S.z * F.kF) := by
  refine ⟨mul_mem z_mem_B (kF_mem_B F), fun h => F.kF_not_mem (zt_le_RK ?_)⟩
  have := mul_mem (inv_mem (show S.z ∈ (zpowers S.z ⊔ zpowers S.t : Subgroup X) from
    mem_sup_left (mem_zpowers _))) h
  rwa [inv_mul_cancel_left] at this

variable {ki : X}

theorem IsK.sq (hk : IsK (S := S) ki) : ki ^ 2 = 1 := S.sq_of_mem_B hk.mem

theorem IsK.ne_one (hk : IsK (S := S) ki) : ki ≠ 1 := fun h => hk.not_mem (h ▸ one_mem _)

theorem E0_eq (yi ki : X) : S.E0 yi ki = zpowers S.z ⊔ zpowers ki ⊔ zpowers yi := by
  rw [A7Base.E0, closure_triple_eq, sup_right_comm]

theorem zk_le_B (hk : IsK (S := S) ki) : (zpowers S.z ⊔ zpowers ki : Subgroup X) ≤ S.B :=
  sup_le (zpowers_le.mpr z_mem_B) (zpowers_le.mpr hk.mem)

theorem elemAbelianTwo_zk (hk : IsK (S := S) ki) :
    ElemAbelianTwo (zpowers S.z ⊔ zpowers ki : Subgroup X) :=
  ⟨fun _ ha _ hb => commute_of_mem_B (zk_le_B hk ha) (zk_le_B hk hb),
    fun _ ha => S.sq_of_mem_B (zk_le_B hk ha)⟩

theorem IsRefl.elemAbelianTwo_E0 (h : IsRefl F yi) (hk : IsK (S := S) ki) :
    ElemAbelianTwo (S.E0 yi ki) := by
  rw [E0_eq]
  exact elemAbelianTwo_sup (elemAbelianTwo_zk hk) h.sq fun _ hb => h.comm_B (zk_le_B hk hb)

theorem card_zk (hk : IsK (S := S) ki) : Nat.card (zpowers S.z ⊔ zpowers ki : Subgroup X) = 4 := by
  have hz : ElemAbelianTwo (zpowers S.z) :=
    ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr z_mem_B ha) (zpowers_le.mpr z_mem_B hb),
      fun a ha => S.sq_of_mem_B (zpowers_le.mpr z_mem_B ha)⟩
  rw [card_sup_of_not_mem hz hk.sq (fun h => hk.not_mem (mem_sup_left h))
    (fun a ha => commute_of_mem_B hk.mem (zpowers_le.mpr z_mem_B ha)),
    Nat.card_zpowers, orderOf_eq_prime z_sq S.z_ne_one]

theorem IsRefl.card_E0 (h : IsRefl F yi) (hk : IsK (S := S) ki) : Nat.card (S.E0 yi ki) = 8 := by
  rw [E0_eq, card_sup_of_not_mem (elemAbelianTwo_zk hk) h.sq
    (fun hy => h.not_mem_B (zk_le_B hk hy)) (fun _ hb => h.comm_B (zk_le_B hk hb)), card_zk hk]

theorem t_not_mem_zt' : S.t ∉ (zpowers S.z : Subgroup X) := by
  intro h
  rcases eq_one_or_eq_of_mem_zpowers z_sq h with h1 | h1
  · exact S.t_ne_one h1
  · exact S.data.t_not_mem_L (h1 ▸ S.z_mem.2)

theorem IsRefl.t_not_mem_E0 (h : IsRefl F yi) (hk : IsK (S := S) ki) : S.t ∉ S.E0 yi ki := by
  intro ht
  rw [E0_eq] at ht
  rcases mem_or_of_mem_sup (elemAbelianTwo_zk hk) h.sq (fun _ hb => h.comm_B (zk_le_B hk hb))
    ht with h1 | h1
  · have hz : ElemAbelianTwo (zpowers S.z) :=
      ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr z_mem_B ha) (zpowers_le.mpr z_mem_B hb),
        fun a ha => S.sq_of_mem_B (zpowers_le.mpr z_mem_B ha)⟩
    rcases mem_or_of_mem_sup hz hk.sq (fun a ha => commute_of_mem_B hk.mem
      (zpowers_le.mpr z_mem_B ha)) h1 with h2 | h2
    · exact t_not_mem_zt' h2
    · apply hk.not_mem
      have : (S.t * ki)⁻¹ * S.t ∈ (zpowers S.z ⊔ zpowers S.t : Subgroup X) :=
        mul_mem (inv_mem (mem_sup_left h2)) (mem_sup_right (mem_zpowers _))
      rwa [show (S.t * ki)⁻¹ * S.t = ki⁻¹ by group, inv_mem_iff] at this
  · apply h.not_mem_B
    have := mul_mem (inv_mem t_mem_B) (zk_le_B hk h1)
    rwa [inv_mul_cancel_left] at this

theorem E0_le_E (hk : IsK (S := S) ki) (yi : X) : S.E0 yi ki ≤ S.E yi := by
  rw [E0_eq]
  exact sup_le (sup_le (zpowers_le.mpr (z_mem_E yi)) (zpowers_le.mpr (B_le_E yi hk.mem)))
    (zpowers_le.mpr (mem_E_self yi))

theorem IsRefl.comm_E0_t (h : IsRefl F yi) (hk : IsK (S := S) ki) {e : X}
    (he : e ∈ S.E0 yi ki) : S.t * e = e * S.t :=
  (S.data.commute_t (h.E_le_T (E0_le_E hk yi he))).symm

theorem IsRefl.E_eq_E0_sup (h : IsRefl F yi) (hk : IsK (S := S) ki) :
    S.E yi = S.E0 yi ki ⊔ zpowers S.t := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (sup_le (E0_le_E hk yi) (zpowers_le.mpr (t_mem_E yi))) ?_
  rw [h.card_E, card_sup_of_not_mem (h.elemAbelianTwo_E0 hk) S.t_sq (h.t_not_mem_E0 hk)
    (fun _ he => h.comm_E0_t hk he), h.card_E0 hk]

theorem IsRefl.mem_E0_or (h : IsRefl F yi) (hk : IsK (S := S) ki) {e : X} (he : e ∈ S.E yi) :
    e ∈ S.E0 yi ki ∨ e * S.t ∈ S.E0 yi ki := by
  rw [h.E_eq_E0_sup hk] at he
  exact mem_or_of_mem_sup (h.elemAbelianTwo_E0 hk) S.t_sq (fun _ he => h.comm_E0_t hk he) he

omit [Finite X] in
theorem conj_mul_eq' (g a b : X) : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by
  group

omit [Finite X] in
theorem conj_eq_of_comm' {e a : X} (h : e * a = a * e) : e * a * e⁻¹ = a := by
  rw [h, mul_inv_cancel_right]

omit [Finite X] in
theorem mem_or_of_mem_sup_zpowers {V : Subgroup X} {g : X} (hg : g ∈ normalizer (V : Set X))
    (hg2 : g ^ 2 ∈ V) {a : X} (ha : a ∈ V ⊔ zpowers g) : a ∈ V ∨ a * g⁻¹ ∈ V := by
  have hN : zpowers g ≤ normalizer (V : Set X) := zpowers_le.mpr hg
  have ha' : a ∈ (V : Set X) * (zpowers g : Set X) := by
    rw [← coe_mul_of_right_le_normalizer_left V _ hN]
    exact ha
  obtain ⟨b, hb, c, hc, rfl⟩ := ha'
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc
  rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
  · left
    refine mul_mem hb ?_
    rw [zpow_mul, show g ^ (2 : ℤ) = g ^ 2 from zpow_natCast g 2]
    exact zpow_mem hg2 m
  · right
    simp only
    rw [zpow_add, zpow_mul, show g ^ (2 : ℤ) = g ^ 2 from zpow_natCast g 2, zpow_one,
      mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_mem hb (zpow_mem hg2 m)

omit [Finite X] in
theorem conj_mem_of_map_eq {H : Subgroup X} {n : X}
    (hn : H.map (MulAut.conj n).toMonoidHom = H) {h : X} (hh : h ∈ H) : n * h * n⁻¹ ∈ H := by
  rw [← hn]
  exact ⟨h, hh, rfl⟩

omit [Finite X] in
theorem mem_normalizer_of_map_eq {H : Subgroup X} {n : X}
    (hn : H.map (MulAut.conj n).toMonoidHom = H) : n ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro h
  refine ⟨conj_mem_of_map_eq hn, fun hh => ?_⟩
  rw [← hn] at hh
  obtain ⟨a, ha, he⟩ := hh
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
  have : a = h := by
    have := congrArg (fun b => n⁻¹ * b * n) he
    simpa [mul_assoc] using this
  rwa [← this]

omit [Finite X] in
theorem conj_mem_of_mem_normalizer {H : Subgroup X} {n : X} (hn : n ∈ normalizer (H : Set X))
    {h : X} (hh : h ∈ H) : n * h * n⁻¹ ∈ H :=
  (mem_normalizer_iff.mp hn h).mp hh

omit [Finite X] in
theorem mul_mem_zpowers_iff {a b : X} (hab : a * b = b * a) (hb2 : b ^ 2 = 1)
    (hb : b ∉ zpowers a) {c d : X} (hc : c ∈ zpowers a ⊔ zpowers b)
    (hd : d ∈ zpowers a ⊔ zpowers b) :
    c * d ∈ zpowers a ↔ (c ∈ zpowers a ↔ d ∈ zpowers a) := by
  have hbN : b ∈ normalizer (zpowers a : Set X) := by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => ?_)
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left hab n).eq
  have hb2' : b ^ 2 ∈ zpowers a := by rw [hb2]; exact one_mem _
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hb2])
  have hbc : ∀ g ∈ zpowers a, b * g = g * b := by
    intro g hg
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left hab n).symm.eq
  rcases mem_or_of_mem_sup_zpowers hbN hb2' hc with hc' | hc' <;>
    rcases mem_or_of_mem_sup_zpowers hbN hb2' hd with hd' | hd'
  · exact iff_of_true (mul_mem hc' hd') (iff_of_true hc' hd')
  · have hd1 : d ∉ zpowers a := fun h => hb (by
      have := mul_mem (inv_mem h) hd'
      rwa [hbinv, inv_mul_cancel_left] at this)
    exact iff_of_false (fun h => hd1 (by simpa using mul_mem (inv_mem hc') h))
      (fun h => hd1 (h.mp hc'))
  · have hc1 : c ∉ zpowers a := fun h => hb (by
      have := mul_mem (inv_mem h) hc'
      rwa [hbinv, inv_mul_cancel_left] at this)
    exact iff_of_false (fun h => hc1 (by simpa using mul_mem h (inv_mem hd')))
      (fun h => hc1 (h.mpr hd'))
  · have hc1 : c ∉ zpowers a := fun h => hb (by
      have := mul_mem (inv_mem h) hc'
      rwa [hbinv, inv_mul_cancel_left] at this)
    have hd1 : d ∉ zpowers a := fun h => hb (by
      have := mul_mem (inv_mem h) hd'
      rwa [hbinv, inv_mul_cancel_left] at this)
    refine iff_of_true ?_ (iff_of_false hc1 hd1)
    have : c * d = (c * b⁻¹) * (d * b⁻¹) * (b * b) := by
      rw [show c * b⁻¹ * (d * b⁻¹) * (b * b) = c * (b⁻¹ * d) * b by group]
      have hdb : b⁻¹ * d = d * b⁻¹ := by
        have h1 := hbc _ hd'
        calc b⁻¹ * d = b⁻¹ * (d * b⁻¹ * b) := by group
          _ = b⁻¹ * (b * (d * b⁻¹)) := by rw [h1]
          _ = d * b⁻¹ := by group
      rw [hdb]; group
    rw [this, show b * b = 1 by rw [← pow_two, hb2], mul_one]
    exact mul_mem hc' hd'

theorem B_eq_kF (F : S.Frame) : S.B = zpowers S.z ⊔ zpowers S.t ⊔ zpowers F.kF := by
  symm
  have hle : zpowers S.z ⊔ zpowers S.t ⊔ zpowers F.kF ≤ S.B :=
    sup_le zt_le_B (zpowers_le.mpr (kF_mem_B F))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hzt : ElemAbelianTwo (zpowers S.z ⊔ zpowers S.t : Subgroup X) :=
    ⟨fun _ ha _ hb => commute_of_mem_B (zt_le_B ha) (zt_le_B hb),
      fun _ ha => S.sq_of_mem_B (zt_le_B ha)⟩
  have hz : ElemAbelianTwo (zpowers S.z) :=
    ⟨fun a ha b hb => commute_of_mem_B (zpowers_le.mpr z_mem_B ha) (zpowers_le.mpr z_mem_B hb),
      fun a ha => S.sq_of_mem_B (zpowers_le.mpr z_mem_B ha)⟩
  have hcard_zt : Nat.card (zpowers S.z ⊔ zpowers S.t : Subgroup X) = 4 := by
    rw [card_sup_of_not_mem hz S.t_sq t_not_mem_zt'
      (fun a ha => commute_of_mem_B t_mem_B (zpowers_le.mpr z_mem_B ha)),
      Nat.card_zpowers, orderOf_eq_prime z_sq S.z_ne_one]
  rw [S.card_B, card_sup_of_not_mem hzt F.kF_sq (isK_kF F).not_mem
    (fun _ ha => commute_of_mem_B (kF_mem_B F) (zt_le_B ha)), hcard_zt]

theorem fix_E_of_fix (F : S.Frame) (yi : X) {g : X} (hz : g * S.z * g⁻¹ = S.z)
    (ht : g * S.t * g⁻¹ = S.t) (hk : g * F.kF * g⁻¹ = F.kF) (hy : g * yi * g⁻¹ = yi)
    {e : X} (he : e ∈ S.E yi) : g * e * g⁻¹ = e := by
  have hfix : ∀ a : X, g * a * g⁻¹ = a → a ∈ centralizer ({g} : Set X) := by
    intro a ha
    rw [mem_centralizer_singleton_iff]
    calc a * g = g * a * g⁻¹ * g := by rw [ha]
      _ = g * a := by group
  have hle : S.E yi ≤ centralizer ({g} : Set X) := by
    rw [E_eq, B_eq_kF F]
    exact sup_le (sup_le (sup_le (zpowers_le.mpr (hfix _ hz)) (zpowers_le.mpr (hfix _ ht)))
      (zpowers_le.mpr (hfix _ hk))) (zpowers_le.mpr (hfix _ hy))
  exact conj_eq_of_comm' (mem_centralizer_singleton_iff.mp (hle he)).symm

end Sec7

end CFSG.ComponentClassification.HSFLit

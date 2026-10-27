module

public import CFSG.ClassicalInvolution.Asc77.AscP1Thompson3T
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonCox

public section

namespace CFSG.ClassicalInvolution.Asc77.Star3T

open CFSG.ClassicalInvolution.Asc77.Cox

variable {Q : Type*} [Group Q] {Δ : Set Q}

theorem isPlane_of_not_conn {d a : Q} (hd : d ∈ Δ) (ha : a ∈ Δ) (hc : ¬ Conn Δ d a) :
    IsPlane Δ d a (d * a * d) := ⟨hd, ha, hc, rfl⟩

theorem noncomm_of_mem_cent {d a e : Q} (hpl : IsPlane Δ d a e) {x : Q} (hx : x ∈ cent Δ d) :
    x * a ≠ a * x := fun e' =>
  hpl.not_conn ((conn_of_mem_cent hpl.mem_left hx).trans (conn_of_commute hx.1 hpl.mem_right e'))

theorem two_le_natCard_centralizer [Finite Q] (h : IsTT Δ) {d : Q} (hd : d ∈ Δ) :
    2 ≤ Nat.card (Subgroup.centralizer ({d} : Set Q)) := by
  have hd1 := h.ne_one d hd
  let f : Fin 2 → Subgroup.centralizer ({d} : Set Q) := ![⟨1, Subgroup.one_mem _⟩,
    ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl |
      (exfalso; simp [f] at hij; first | exact hd1 hij | exact hd1 hij.symm)
  simpa using Nat.card_le_card_of_injective f hf

theorem four_le_natCard_centralizer [Finite Q] (h : IsTT Δ) {d d' : Q} (hd : d ∈ Δ)
    (hd' : d' ∈ cent Δ d) (hne : d ≠ d') :
    4 ≤ Nat.card (Subgroup.centralizer ({d} : Set Q)) := by
  have hd1 := h.ne_one d hd
  have hd'1 := h.ne_one d' hd'.1
  have hcomm : d * d' = d' * d := hd'.2.symm
  have hmem1 : (1 : Q) ∈ Subgroup.centralizer ({d} : Set Q) := Subgroup.one_mem _
  have hmem2 : d ∈ Subgroup.centralizer ({d} : Set Q) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hmem3 : d' ∈ Subgroup.centralizer ({d} : Set Q) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hd'.2
  have hmem4 : d * d' ∈ Subgroup.centralizer ({d} : Set Q) :=
    Subgroup.mul_mem _ hmem2 hmem3
  have h03 : (1 : Q) ≠ d * d' := fun e => hne (by
    have := eq_inv_of_mul_eq_one_right e.symm
    rw [h.inv_eq hd] at this
    exact this.symm)
  let f : Fin 4 → Subgroup.centralizer ({d} : Set Q) :=
    ![⟨1, hmem1⟩, ⟨d, hmem2⟩, ⟨d', hmem3⟩, ⟨d * d', hmem4⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' : (f i : Q) = f j := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exfalso
           simp [f] at hij'
           first
             | exact hd1 hij' | exact hd1 hij'.symm | exact hd'1 hij' | exact hd'1 hij'.symm
             | exact hne hij' | exact hne hij'.symm | exact h03 hij' | exact h03 hij'.symm)
  simpa using Nat.card_le_card_of_injective f hf

theorem isSwap_iff_exists_conj {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (σ : Equiv.Perm α) : σ.IsSwap ↔ ∃ g : Equiv.Perm α, g * Equiv.swap a b * g⁻¹ = σ := by
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hxy)
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g a, g b, g.injective.ne hab, (Equiv.swap_apply_apply g a b).symm⟩

theorem mem_iff_isSwap_of_equiv {α : Type*} [DecidableEq α] {a b : α} (hab : a ≠ b)
    (h : IsTT Δ) {d : Q} (hd : d ∈ Δ) (hcl : ∀ y ∈ Δ, ∃ g : Q, y = g * d * g⁻¹)
    (e : Q ≃* Equiv.Perm α) (hed : e d = Equiv.swap a b) (x : Q) : x ∈ Δ ↔ (e x).IsSwap := by
  rw [isSwap_iff_exists_conj hab]
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := hcl x hx
    exact ⟨e g, by rw [map_mul, map_mul, map_inv, hed]⟩
  · rintro ⟨g, hg⟩
    have : x = e.symm g * d * (e.symm g)⁻¹ := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, hed, MulEquiv.apply_symm_apply, hg]
    rw [this]
    exact h.conj_mem' hd _

theorem exists_mulEquiv_perm_three [Finite Q] (h : IsTT Δ) (hS : IsStar Δ) {d a : Q}
    (hd : d ∈ Δ) (ha : a ∈ Δ) (hc : ¬ Conn Δ d a) (hk : (cent Δ d).ncard = 1) :
    ∃ e : Q ≃* Equiv.Perm (Fin 3), ∀ x, x ∈ Δ ↔ (e x).IsSwap := by
  have hpl := isPlane_of_not_conn hd ha hc
  have hcent : cent Δ d = {d} := by
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hk
    have hdx : d ∈ ({x} : Set Q) := hx ▸ self_mem_cent hd
    rw [hx, Set.mem_singleton_iff.mp hdx]
  let f : Fin 2 → Q := ![d, a]
  have hbr : d * a * d = a * d * a := h.braid hd ha hpl.noncomm
  have hcomm : ∀ i j, MA2 i j = 2 → f i * f j = f j * f i := by
    intro i j hij
    exfalso
    fin_cases i <;> fin_cases j <;> simp [MA2] at hij
  have hbraid : ∀ i j, MA2 i j = 3 → f i * f j * f i = f j * f i * f j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MA2, f] at hij ⊢
    · exact hbr
    · exact hbr.symm
  have hsq : ∀ i, f i * f i = 1 := by
    intro i
    fin_cases i
    · exact h.mul_self d hd
    · exact h.mul_self a ha
  have hR : IsRel (CoxeterMatrix.A 2).M f :=
    (IsRel.of_eq (fun i j => by fin_cases i <;> fin_cases j <;> rfl) ⟨hsq, hcomm, hbraid⟩)
  have hlift : (CoxeterMatrix.A 2).IsLiftable f :=
    hR.isLiftable (fun i j => by fin_cases i <;> fin_cases j <;> decide)
  have hgen : Subgroup.closure (Set.range f) = ⊤ := by
    have hr : Set.range f = insert a (cent Δ d) := by
      rw [hcent]
      ext x
      simp [f, Matrix.range_cons, or_comm]
    rw [hr]
    exact h.closure_insert_cent_eq_top hS hpl
  let cs := (CoxeterMatrix.A 2).toCoxeterSystem
  obtain ⟨hfin, hW⟩ := finite_card_A2 cs
  have : Finite (CoxeterMatrix.A 2).Group := hfin
  have hQ : 6 ≤ Nat.card Q := by
    have h1 := h.natCard_eq_three_mul hS hpl
    have h2 := two_le_natCard_centralizer h hd
    have : (cent Δ d).ncard = 1 := hk
    rw [this] at h1
    omega
  obtain ⟨e₁, he₁⟩ := exists_mulEquiv_of_card_le cs f hlift hgen (by omega)
  obtain ⟨e₂, he₂⟩ := exists_mulEquiv_perm_A2 cs
  refine ⟨e₁.symm.trans e₂, ?_⟩
  have hed : (e₁.symm.trans e₂) d = Equiv.swap 0 1 := by
    have h0 : e₁ (cs.simple 0) = d := he₁ 0
    have : e₁.symm d = cs.simple 0 := by rw [← h0]; exact e₁.symm_apply_apply _
    show e₂ (e₁.symm d) = _
    rw [this, he₂ 0]
    rfl
  exact mem_iff_isSwap_of_equiv (by decide) h hd (h.exists_conj_of_not_conn hd ha hc) _ hed

theorem exists_mulEquiv_perm_four [Finite Q] (h : IsTT Δ) (hS : IsStar Δ) {d a : Q}
    (hd : d ∈ Δ) (ha : a ∈ Δ) (hc : ¬ Conn Δ d a) (hk : (cent Δ d).ncard = 2) :
    ∃ e : Q ≃* Equiv.Perm (Fin 4), ∀ x, x ∈ Δ ↔ (e x).IsSwap := by
  have hpl := isPlane_of_not_conn hd ha hc
  obtain ⟨d', hne, hcent⟩ : ∃ d', d ≠ d' ∧ cent Δ d = {d, d'} := by
    obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp hk
    have hdx : d ∈ ({x, y} : Set Q) := hxy' ▸ self_mem_cent hd
    rcases hdx with rfl | hdy
    · exact ⟨y, hxy, hxy'⟩
    · rw [Set.mem_singleton_iff] at hdy
      subst hdy
      exact ⟨x, fun e => hxy e.symm, by rw [hxy', Set.pair_comm]⟩
  have hd'c : d' ∈ cent Δ d := by rw [hcent]; exact Or.inr rfl
  have hcd : d * d' = d' * d := hd'c.2.symm
  have hbr1 : d * a * d = a * d * a := h.braid hd ha hpl.noncomm
  have hbr2 : a * d' * a = d' * a * d' :=
    h.braid ha hd'c.1 (fun e => noncomm_of_mem_cent hpl hd'c e.symm)
  let f : Fin 3 → Q := ![d, a, d']
  have hcomm : ∀ i j, MA3 i j = 2 → f i * f j = f j * f i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MA3, f] at hij ⊢
    · exact hcd
    · exact hcd.symm
  have hbraid : ∀ i j, MA3 i j = 3 → f i * f j * f i = f j * f i * f j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MA3, f] at hij ⊢
    · exact hbr1
    · exact hbr1.symm
    · exact hbr2
    · exact hbr2.symm
  have hsq : ∀ i, f i * f i = 1 := by
    intro i
    fin_cases i
    · exact h.mul_self d hd
    · exact h.mul_self a ha
    · exact h.mul_self d' hd'c.1
  have hR : IsRel (CoxeterMatrix.A 3).M f :=
    (IsRel.of_eq (fun i j => by fin_cases i <;> fin_cases j <;> rfl) ⟨hsq, hcomm, hbraid⟩)
  have hlift : (CoxeterMatrix.A 3).IsLiftable f :=
    hR.isLiftable (fun i j => by fin_cases i <;> fin_cases j <;> decide)
  have hgen : Subgroup.closure (Set.range f) = ⊤ := by
    have hr : Set.range f = insert a (cent Δ d) := by
      rw [hcent]
      ext x
      simp only [f, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.mem_union,
        Set.mem_singleton_iff, Set.mem_insert_iff]
      tauto
    rw [hr]
    exact h.closure_insert_cent_eq_top hS hpl
  let cs := (CoxeterMatrix.A 3).toCoxeterSystem
  obtain ⟨hfin, hW⟩ := finite_card_A3 cs
  have : Finite (CoxeterMatrix.A 3).Group := hfin
  have hQ : 24 ≤ Nat.card Q := by
    have h1 := h.natCard_eq_three_mul hS hpl
    have h2 := four_le_natCard_centralizer h hd hd'c hne
    have : (cent Δ d).ncard = 2 := hk
    rw [this] at h1
    omega
  obtain ⟨e₁, he₁⟩ := exists_mulEquiv_of_card_le cs f hlift hgen (by omega)
  obtain ⟨e₂, he₂⟩ := exists_mulEquiv_perm_A3 cs
  refine ⟨e₁.symm.trans e₂, ?_⟩
  have hed : (e₁.symm.trans e₂) d = Equiv.swap 0 1 := by
    have h0 : e₁ (cs.simple 0) = d := he₁ 0
    have : e₁.symm d = cs.simple 0 := by rw [← h0]; exact e₁.symm_apply_apply _
    show e₂ (e₁.symm d) = _
    rw [this, he₂ 0]
    rfl
  exact mem_iff_isSwap_of_equiv (by decide) h hd (h.exists_conj_of_not_conn hd ha hc) _ hed

theorem eq_of_conj_eq (h : IsTT Δ) {a u v w : Q} (hu : u ∈ Δ) (hv : v ∈ Δ) (hw : w ∈ Δ)
    (bu : u * a * u = a * u * a) (bv : v * a * v = a * v * a) (bw : w * a * w = a * w * a)
    (hq : a * u * a = (u * v * w) * a * (w * v * u)) : v = w := by
  have huu := h.mul_self u hu
  have hvv := h.mul_self v hv
  have hww := h.mul_self w hw
  have e1 : a = v * w * a * (w * v) := by
    calc a = u * (u * a * u) * u := by
          calc a = (u * u) * a * (u * u) := by rw [huu, one_mul, mul_one]
            _ = u * (u * a * u) * u := by simp only [mul_assoc]
      _ = u * (a * u * a) * u := by rw [bu]
      _ = u * ((u * v * w) * a * (w * v * u)) * u := by rw [hq]
      _ = (u * u) * v * w * a * (w * v) * (u * u) := by simp only [mul_assoc]
      _ = v * w * a * (w * v) := by rw [huu, one_mul, mul_one]
  have e2 : w * a * w = v * a * v := by
    calc w * a * w = (v * v) * w * a * w * (v * v) := by
          rw [hvv, one_mul, mul_one]
      _ = v * (v * w * a * (w * v)) * v := by simp only [mul_assoc]
      _ = v * a * v := by rw [← e1]
  have e3 : a * w * a = a * v * a := by rw [← bw, ← bv, e2]
  have := mul_left_cancel (mul_right_cancel e3)
  exact this.symm

theorem nonempty_mulEquiv_of_card_four [Finite Q] (h : IsTT Δ) (hS : IsStar Δ) {d a : Q}
    (hd : d ∈ Δ) (ha : a ∈ Δ) (hc : ¬ Conn Δ d a) (hk : (cent Δ d).ncard = 4)
    (hcard : 16 ≤ Nat.card (Subgroup.closure (cent Δ d)))
    {M : CoxeterMatrix (Fin 4)} (hM : ∀ i j, M.M i j = MD4 i j) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) : Nonempty (Q ≃* W) := by
  have hpl := isPlane_of_not_conn hd ha hc
  have hcl : ∀ u ∈ cent Δ d, ∀ v ∈ cent Δ d, u * v = v * u := fun u hu v hv =>
    h.isClique_cent hS hd ha hc hu hv
  have hbr : ∀ x ∈ cent Δ d, x * a * x = a * x * a := fun x hx =>
    h.braid hx.1 ha (noncomm_of_mem_cent hpl hx)
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).mp (by omega : 2 < (cent Δ d).ncard)
  have hz : x₁ * (x₂ * (x₃ * a * x₃) * x₂) * x₁ ∈ cent Δ (d * a * d) := by
    have hpl' : IsPlane Δ d (d * a * d) a := h.isPlane_rot hpl
    have u3 : x₃ * a * x₃ ∈ cent Δ (d * a * d) :=
      h.cent_conj_mem hS hpl h₃ (self_mem_cent ha)
    have u2 : x₂ * (x₃ * a * x₃) * x₂ ∈ cent Δ a := h.cent_conj_mem hS hpl' h₂ u3
    exact h.cent_conj_mem hS hpl h₁ u2
  have himg := h.cent_eq_image hS (h.isPlane_swap hpl)
  rw [himg] at hz
  obtain ⟨x₄, h₄, hx₄⟩ := hz
  have hx₄' : a * x₄ * a = (x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁) := by
    have := hx₄
    simp only at this
    rw [this]
    simp only [mul_assoc]
  have c12 : x₁ * x₂ = x₂ * x₁ := hcl _ h₁ _ h₂
  have c13 : x₁ * x₃ = x₃ * x₁ := hcl _ h₁ _ h₃
  have c23 : x₂ * x₃ = x₃ * x₂ := hcl _ h₂ _ h₃
  have n1 : x₄ ≠ x₁ := fun e => by
    rw [e] at hx₄'
    exact h23 (eq_of_conj_eq h h₁.1 h₂.1 h₃.1 (hbr _ h₁) (hbr _ h₂) (hbr _ h₃) hx₄')
  have n2 : x₄ ≠ x₂ := fun e => by
    rw [e] at hx₄'
    have e1 : x₁ * x₂ * x₃ = x₂ * x₁ * x₃ := by rw [c12]
    have e2 : x₃ * x₂ * x₁ = x₃ * x₁ * x₂ := by
      calc x₃ * x₂ * x₁ = x₃ * (x₂ * x₁) := mul_assoc _ _ _
        _ = x₃ * (x₁ * x₂) := by rw [← c12]
        _ = x₃ * x₁ * x₂ := (mul_assoc _ _ _).symm
    rw [e1, e2] at hx₄'
    exact h13 (eq_of_conj_eq h h₂.1 h₁.1 h₃.1 (hbr _ h₂) (hbr _ h₁) (hbr _ h₃) hx₄')
  have n3 : x₄ ≠ x₃ := fun e => by
    rw [e] at hx₄'
    have e1 : x₁ * x₂ * x₃ = x₃ * x₁ * x₂ := by
      calc x₁ * x₂ * x₃ = x₁ * (x₂ * x₃) := mul_assoc _ _ _
        _ = x₁ * (x₃ * x₂) := by rw [c23]
        _ = x₁ * x₃ * x₂ := (mul_assoc _ _ _).symm
        _ = x₃ * x₁ * x₂ := by rw [c13]
    have e2 : x₃ * x₂ * x₁ = x₂ * x₁ * x₃ := by
      calc x₃ * x₂ * x₁ = x₂ * x₃ * x₁ := by rw [← c23]
        _ = x₂ * (x₃ * x₁) := mul_assoc _ _ _
        _ = x₂ * (x₁ * x₃) := by rw [← c13]
        _ = x₂ * x₁ * x₃ := (mul_assoc _ _ _).symm
    rw [e1, e2] at hx₄'
    exact h12 (eq_of_conj_eq h h₃.1 h₁.1 h₂.1 (hbr _ h₃) (hbr _ h₁) (hbr _ h₂) hx₄')
  have hcent : cent Δ d = {x₁, x₂, x₃, x₄} := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl <;> assumption
    · have hn : ({x₁, x₂, x₃, x₄} : Set Q).ncard = 4 := by
        rw [Set.ncard_insert_of_notMem (by simp [h12, h13, n1.symm]),
          Set.ncard_insert_of_notMem (by simp [h23, n2.symm]), Set.ncard_pair n3.symm]
      omega
  let f : Fin 4 → Q := ![x₁, a, x₂, x₃]
  have hsq : ∀ i, f i * f i = 1 := by
    intro i
    fin_cases i
    · exact h.mul_self x₁ h₁.1
    · exact h.mul_self a ha
    · exact h.mul_self x₂ h₂.1
    · exact h.mul_self x₃ h₃.1
  have hcomm : ∀ i j, MD4 i j = 2 → f i * f j = f j * f i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MD4, f] at hij ⊢
    all_goals
      first
        | exact c12 | exact c12.symm | exact c13 | exact c13.symm
        | exact c23 | exact c23.symm
  have hbraid : ∀ i j, MD4 i j = 3 → f i * f j * f i = f j * f i * f j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [MD4, f] at hij ⊢
    all_goals
      first
        | exact hbr _ h₁ | exact (hbr _ h₁).symm | exact hbr _ h₂
        | exact (hbr _ h₂).symm | exact hbr _ h₃ | exact (hbr _ h₃).symm
  have hR : IsRel M.M f := IsRel.of_eq hM ⟨hsq, hcomm, hbraid⟩
  have hlift : M.IsLiftable f :=
    hR.isLiftable (fun i j => by rw [hM]; fin_cases i <;> fin_cases j <;> decide)
  have hgen : Subgroup.closure (Set.range f) = ⊤ := by
    have hmem : ∀ i, f i ∈ Subgroup.closure (Set.range f) := fun i =>
      Subgroup.subset_closure ⟨i, rfl⟩
    have m1 := hmem 0
    have ma := hmem 1
    have m2 := hmem 2
    have m3 := hmem 3
    have hp : (x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁) ∈ Subgroup.closure (Set.range f) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ m1 m2) m3) ma)
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ m3 m2) m1)
    have haa := h.mul_self a ha
    have hx4 : x₄ ∈ Subgroup.closure (Set.range f) := by
      have e : x₄ = a * ((x₁ * x₂ * x₃) * a * (x₃ * x₂ * x₁)) * a := by
        rw [← hx₄']
        calc x₄ = (a * a) * x₄ * (a * a) := by rw [haa, one_mul, mul_one]
          _ = a * (a * x₄ * a) * a := by simp only [mul_assoc]
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ma hp) ma
    rw [eq_top_iff, ← h.closure_insert_cent_eq_top hS hpl, Subgroup.closure_le]
    intro y hy
    rcases hy with rfl | hy
    · exact ma
    · rw [hcent] at hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · exact m1
      · exact m2
      · exact m3
      · exact hx4
  obtain ⟨hfin, hW⟩ := finite_card_D4 hM cs
  have : Finite W := hfin
  have hQ : 192 ≤ Nat.card Q := by
    have h1 := h.natCard_eq_three_mul hS hpl
    have hle : Nat.card (Subgroup.closure (cent Δ d)) ≤
        Nat.card (Subgroup.centralizer ({d} : Set Q)) :=
      Subgroup.card_le_of_le ((Subgroup.closure_le _).mpr (IsTT.cent_subset_centralizer d))
    have : (cent Δ d).ncard = 4 := hk
    rw [this] at h1
    omega
  obtain ⟨e, -⟩ := exists_mulEquiv_of_card_le cs f hlift hgen (by omega)
  exact ⟨e.symm⟩

end CFSG.ClassicalInvolution.Asc77.Star3T

module

public import CFSG.ClassicalInvolution.RouteD.TypeAFrame
public import CFSG.ClassicalInvolution.Models.LinearFrames.Pairs

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic Module Matrix
open scoped MatrixGroups


section Helpers

variable {F : Type} [Field F] {n : ℕ}

theorem spaces_of_commutes (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {L₁ L₂ : Subgroup SL(n, F)} {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hne : i₁ ≠ i₂) (hc : Commutes L₁ L₂) :
    minusSpace i₁ ≤ fixSpace i₂ ∧ minusSpace i₂ ≤ fixSpace i₁ ∧
      minusSpace i₁ ⊓ minusSpace i₂ = ⊥ := by
  have hcomm : Commute i₁ i₂ := hc i₁ h₁.mem i₂ h₂.mem
  rcases lemma_6_5 h2 hn3 h₁ h₂ hcomm hne with ⟨-, h1, h2', h3⟩ | ⟨hnot, -⟩
  · exact ⟨h1, h2', h3⟩
  · exact absurd (Subgroup.mem_centralizer_iff.mpr fun x hx => hc x hx i₂ h₂.mem) hnot

theorem inf_ne_bot_of_not_commutes (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n}
    {L₁ L₂ : Subgroup SL(n, F)} {i₁ i₂ : SL(n, F)} (h₁ : IsLongRootSL2 hn L₁ i₁)
    (h₂ : IsLongRootSL2 hn L₂ i₂) (hc : Commute i₁ i₂) (hnc : ¬ Commutes L₁ L₂) :
    minusSpace i₁ ⊓ minusSpace i₂ ≠ ⊥ := by
  intro h
  apply hnc
  intro x hx y hy
  have hcc : (i₁ : Matrix (Fin n) (Fin n) F) * i₂ = i₂ * i₁ := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hc.eq]
  rw [h₁.eq_longRootGroup h2] at hx
  rw [h₂.eq_longRootGroup h2] at hy
  exact mul_comm_of_inf_eq_bot h2 h₁.coe_mul_self h₂.coe_mul_self hcc h hx hy

end Helpers


section Middle

variable {F : Type} [Field F] {n : ℕ}

theorem inf_eq_bot_of_le_eigSpace {A : Matrix (Fin n) (Fin n) F} (h2 : (2 : F) ≠ 0)
    {U : Submodule F (Fin n → F)} (hU : U ≤ eigSpace A 1) : U ⊓ eigSpace A (-1) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h1 := mem_eigSpace_one.mp (hU hv.1)
  have h3 := mem_eigSpace_neg_one.mp hv.2
  have e : v = -v := h1.symm.trans h3
  have : (2 : F) • v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [e]
    exact neg_add_cancel v
  exact (Submodule.mem_bot F).mpr ((smul_eq_zero.mp this).resolve_left h2)

theorem middle_core (h2 : (2 : F) ≠ 0) {A₁ A₂ A₃ A : Matrix (Fin n) (Fin n) F}
    (s₁ : A₁ * A₁ = 1) (s₂ : A₂ * A₂ = 1) (s₃ : A₃ * A₃ = 1) (s : A * A = 1)
    (c12 : A₁ * A₂ = A₂ * A₁) (c23 : A₂ * A₃ = A₃ * A₂) (c13 : A₁ * A₃ = A₃ * A₁)
    (d₂ : finrank F (eigSpace A₂ (-1)) = 2)
    (h13 : eigSpace A₁ (-1) ⊓ eigSpace A₃ (-1) = ⊥)
    (h12 : eigSpace A₁ (-1) ⊓ eigSpace A₂ (-1) ≠ ⊥)
    (h23 : eigSpace A₂ (-1) ⊓ eigSpace A₃ (-1) ≠ ⊥)
    (a1 : eigSpace A (-1) ≤ eigSpace A₁ 1) (a1' : eigSpace A₁ (-1) ≤ eigSpace A 1)
    (a3 : eigSpace A (-1) ≤ eigSpace A₃ 1) (a3' : eigSpace A₃ (-1) ≤ eigSpace A 1) :
    A * A₂ = A₂ * A ∧ eigSpace A (-1) ⊓ eigSpace A₂ (-1) = ⊥ := by
  have hX : eigSpace A₂ (-1) ⊓ eigSpace A₁ (-1) ≠ ⊥ := by rw [inf_comm]; exact h12
  have hXY : Disjoint (eigSpace A₂ (-1) ⊓ eigSpace A₁ (-1)) (eigSpace A₂ (-1) ⊓ eigSpace A₃ (-1)) := by
    rw [disjoint_iff, eq_bot_iff, ← h13]
    intro v hv
    exact ⟨hv.1.2, hv.2.2⟩
  have hxy : (eigSpace A₂ (-1) ⊓ eigSpace A₁ (-1)) ⊔ (eigSpace A₂ (-1) ⊓ eigSpace A₃ (-1)) =
      eigSpace A₂ (-1) := by
    refine Submodule.eq_of_le_of_finrank_le (sup_le inf_le_left inf_le_left) ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq (eigSpace A₂ (-1) ⊓ eigSpace A₁ (-1))
      (eigSpace A₂ (-1) ⊓ eigSpace A₃ (-1))
    rw [hXY.eq_bot, finrank_bot] at h
    have p1 := Submodule.one_le_finrank_iff.mpr hX
    have p2 := Submodule.one_le_finrank_iff.mpr h23
    omega
  have hV2 : eigSpace A₂ (-1) ≤ eigSpace A₁ (-1) ⊔ eigSpace A₃ (-1) := by
    rw [← hxy]
    exact sup_le_sup inf_le_right inf_le_right
  have hV2W : eigSpace A₂ (-1) ≤ eigSpace A 1 := hV2.trans (sup_le a1' a3')
  have h31 : eigSpace A₃ (-1) ≤ eigSpace A₁ 1 :=
    eigSpace_neg_one_le_one s₁ c13.symm (by rw [inf_comm]; exact h13)
  have h13' : eigSpace A₁ (-1) ≤ eigSpace A₃ 1 := eigSpace_neg_one_le_one s₃ c13 h13
  have hVW2 : eigSpace A (-1) ≤ eigSpace A₂ 1 := by
    intro v hv
    have hv1 : A₁ *ᵥ v = v := mem_eigSpace_one.mp (a1 hv)
    have hv3 : A₃ *ᵥ v = v := mem_eigSpace_one.mp (a3 hv)
    have hff : A₂ *ᵥ (A₂ *ᵥ v) = v := by rw [mulVec_mulVec, s₂, Matrix.one_mulVec]
    set vm : Fin n → F := (2 : F)⁻¹ • (v - A₂ *ᵥ v) with hvm
    have hvm2 : vm ∈ eigSpace A₂ (-1) := by
      rw [mem_eigSpace_neg_one, hvm, Matrix.mulVec_smul, Matrix.mulVec_sub, hff]
      module
    have hA1 : A₁ *ᵥ vm = vm := by
      rw [hvm, Matrix.mulVec_smul, Matrix.mulVec_sub, hv1, mulVec_mulVec, c12, ← mulVec_mulVec, hv1]
    have hA3 : A₃ *ᵥ vm = vm := by
      rw [hvm, Matrix.mulVec_smul, Matrix.mulVec_sub, hv3, mulVec_mulVec, ← c23, ← mulVec_mulVec,
        hv3]
    obtain ⟨x, hx, y, hy, hxy'⟩ := Submodule.mem_sup.mp (hV2 hvm2)
    have hx' := mem_eigSpace_neg_one.mp hx
    have hy' := mem_eigSpace_neg_one.mp hy
    have hy1 := mem_eigSpace_one.mp (h31 hy)
    have hx3 := mem_eigSpace_one.mp (h13' hx)
    have e1 : x = 0 := by
      have := hA1
      rw [← hxy', Matrix.mulVec_add, hx', hy1] at this
      have h4 : (2 : F) • x = 0 := by
        rw [two_smul]
        have : -x + y = x + y := this
        calc x + x = (x + y) - (-x + y) + (x + x) - (x + x) := by abel
          _ = 0 := by rw [← this]; abel
      exact (smul_eq_zero.mp h4).resolve_left h2
    have e2 : y = 0 := by
      have := hA3
      rw [← hxy', Matrix.mulVec_add, hx3, hy'] at this
      have h4 : (2 : F) • y = 0 := by
        rw [two_smul]
        have : x + -y = x + y := this
        calc y + y = (x + y) - (x + -y) := by abel
          _ = 0 := by rw [← this]; abel
      exact (smul_eq_zero.mp h4).resolve_left h2
    have hvm0 : vm = 0 := by rw [← hxy', e1, e2, add_zero]
    have : v - A₂ *ᵥ v = 0 := by
      have h5 : (2 : F) • vm = v - A₂ *ᵥ v := by rw [hvm, smul_smul, mul_inv_cancel₀ h2, one_smul]
      rw [← h5, hvm0, smul_zero]
    rw [mem_eigSpace_one]
    exact (sub_eq_zero.mp this).symm
  have e1 := one_sub_mul_one_sub_eq_zero s₂ hV2W
  have e2 := one_sub_mul_one_sub_eq_zero s hVW2
  refine ⟨?_, ?_⟩
  · have : A * A₂ - A₂ * A = 0 := by
      calc A * A₂ - A₂ * A = (1 - A) * (1 - A₂) - (1 - A₂) * (1 - A) := by noncomm_ring
        _ = 0 := by rw [e1, e2, sub_zero]
    exact sub_eq_zero.mp this
  · exact inf_eq_bot_of_le_eigSpace h2 hVW2


theorem coe_commute_of_commute {i j : SL(n, F)} (h : Commute i j) :
    (i : Matrix (Fin n) (Fin n) F) * j = j * i := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, h.eq]

theorem commutes_middle (h2 : (2 : F) ≠ 0) {hn : 2 ≤ n} (hn3 : 3 ≤ n)
    {R₁ R₂ R₃ R : Subgroup SL(n, F)} {i₁ i₂ i₃ i : SL(n, F)} (h₁ : IsLongRootSL2 hn R₁ i₁)
    (h₂ : IsLongRootSL2 hn R₂ i₂) (h₃ : IsLongRootSL2 hn R₃ i₃) (h : IsLongRootSL2 hn R i)
    (c12 : Commute i₁ i₂) (c23 : Commute i₂ i₃) (c13 : Commute i₁ i₃) (n13 : i₁ ≠ i₃)
    (n1 : i ≠ i₁) (n3 : i ≠ i₃) (hR13 : Commutes R₁ R₃) (hn12 : ¬ Commutes R₁ R₂)
    (hn23 : ¬ Commutes R₂ R₃) (hR1 : Commutes R R₁) (hR3 : Commutes R R₃) : Commutes R R₂ := by
  obtain ⟨-, -, h13⟩ := spaces_of_commutes h2 hn3 h₁ h₃ n13 hR13
  obtain ⟨a1, a1', -⟩ := spaces_of_commutes h2 hn3 h h₁ n1 hR1
  obtain ⟨a3, a3', -⟩ := spaces_of_commutes h2 hn3 h h₃ n3 hR3
  have h12 := inf_ne_bot_of_not_commutes h2 h₁ h₂ c12 hn12
  have h23 := inf_ne_bot_of_not_commutes h2 h₂ h₃ c23 hn23
  obtain ⟨hc, hV⟩ := middle_core h2 h₁.coe_mul_self h₂.coe_mul_self h₃.coe_mul_self
    h.coe_mul_self (coe_commute_of_commute c12) (coe_commute_of_commute c23)
    (coe_commute_of_commute c13) (h₂.finrank_minusSpace h2) h13 h12 h23 a1 a1' a3 a3'
  intro x hx y hy
  rw [h.eq_longRootGroup h2] at hx
  rw [h₂.eq_longRootGroup h2] at hy
  exact mul_comm_of_inf_eq_bot h2 h.coe_mul_self h₂.coe_mul_self hc hV hx hy

end Middle

section Partner

variable {F : Type} [Field F]

theorem commutes_map_iff {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) {A B : Subgroup G} :
    Commutes (A.map φ) (B.map φ) ↔ Commutes A B := by
  constructor
  · intro h x hx y hy
    apply hφ
    rw [map_mul, map_mul]
    exact h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

theorem commute_conj {G : Type*} [Group G] {x y : G} (h : Commute x y) (P : G) :
    Commute (P * x * P⁻¹) (P * y * P⁻¹) := by
  have := h.eq
  show P * x * P⁻¹ * (P * y * P⁻¹) = P * y * P⁻¹ * (P * x * P⁻¹)
  calc P * x * P⁻¹ * (P * y * P⁻¹) = P * (x * y) * P⁻¹ := by group
    _ = P * (y * x) * P⁻¹ := by rw [this]
    _ = _ := by group

@[expose] def natPair (n a b : ℕ) (ha : a < n) (hb : b < n) (hab : a ≠ b) : Pair n :=
  ⟨{⟨a, ha⟩, ⟨b, hb⟩}, Finset.card_pair (by
    intro h
    exact hab (by simpa using congrArg Fin.val h))⟩

theorem Lc_congr {n : ℕ} {T T' : Pair n} (h : T.1 = T'.1) : Lc F T = Lc F T' := by
  have : T = T' := Subtype.ext h
  rw [this]

theorem zElt_ne_of_mem {n : ℕ} (h2 : (2 : F) ≠ 0) {T T' : Pair n} {x : Fin n} (hx : x ∈ T.1)
    (hx' : x ∉ T'.1) : zElt F T ≠ zElt F T' := by
  intro h
  have := congrArg Subtype.val (zElt_injective h2 h)
  rw [this] at hx
  exact hx' hx

theorem negTail_eq_zMat (F : Type) [Field F] (k : ℕ) :
    negTail F (k + 3) k = zMat F (k + 3) {⟨k + 1, by omega⟩, ⟨k + 2, by omega⟩} := by
  rw [negTail, zMat]
  congr 1
  funext j
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  by_cases h : k < j.val
  · have h' : (j : ℕ) = k + 1 ∨ (j : ℕ) = k + 2 := by omega
    simp [h, h']
  · have h' : ¬ ((j : ℕ) = k + 1 ∨ (j : ℕ) = k + 2) := by omega
    simp [h, h']

end Partner

section PartnerMain

variable {F : Type} [Field F]

theorem exists_partner (h2 : (2 : F) ≠ 0) {k : ℕ} (hk : 2 ≤ k) {hn2 : 2 ≤ k + 3}
    {R₀ : Subgroup SL(k + 3, F)} {i₀ : SL(k + 3, F)} (h₀ : IsLongRootSL2 hn2 R₀ i₀)
    {R : ℕ → Subgroup SL(k + 3, F)} {i : ℕ → SL(k + 3, F)}
    (hR : ∀ a < k, IsLongRootSL2 hn2 (R a) (i a))
    (hcomm : ∀ a < k, Commute i₀ (i a)) (hcomm' : ∀ a < k, ∀ b < k, Commute (i a) (i b))
    (hinj : ∀ a < k, ∀ b < k, a ≠ b → i a ≠ i b) (h0ne : ∀ a < k, i₀ ≠ i a)
    (hR0 : ∀ a < k, Commutes R₀ (R a))
    (hfar : ∀ a < k, ∀ b < k, a + 2 ≤ b → Commutes (R a) (R b))
    (hadj : ∀ a, a + 1 < k → ¬ Commutes (R a) (R (a + 1))) :
    ∃ (B : Subgroup SL(k + 3, F)) (iB : SL(k + 3, F)), IsLongRootSL2 hn2 B iB ∧
      Commute iB i₀ ∧ iB ≠ i₀ ∧ ¬ Commutes B R₀ ∧
      Commute iB (i 0) ∧ iB ≠ i 0 ∧ ¬ Commutes B (R 0) ∧
      ∀ a, 1 ≤ a → a < k → Commute iB (i a) ∧ iB ≠ i a ∧ Commutes B (R a) := by
  have hn3 : 3 ≤ k + 3 := by omega
  set I : ℕ → Matrix (Fin (k + 3)) (Fin (k + 3)) F :=
    fun a => if a < k then ((i a : SL(k + 3, F)) : Matrix (Fin (k + 3)) (Fin (k + 3)) F) else 1
    with hI
  have hIa : ∀ a < k, I a = ((i a : SL(k + 3, F)) : Matrix (Fin (k + 3)) (Fin (k + 3)) F) := by
    intro a ha
    simp [hI, ha]
  have hchain : IsInvChain I k :=
    { sq := fun a ha => by rw [hIa a ha]; exact (hR a ha).coe_mul_self
      comm := fun a ha b hb => by
        rw [hIa a ha, hIa b hb]; exact coe_commute_of_commute (hcomm' a ha b hb)
      dim := fun a ha => by rw [hIa a ha]; exact (hR a ha).finrank_minusSpace h2
      far := fun a ha b hb hab => by
        rw [hIa a ha, hIa b hb]
        exact (spaces_of_commutes h2 hn3 (hR a ha) (hR b hb) (hinj a ha b hb (by omega))
          (hfar a ha b hb hab)).2.2
      adj := fun a ha => by
        rw [hIa a (by omega), hIa (a + 1) ha]
        exact inf_ne_bot_of_not_commutes h2 (hR a (by omega)) (hR (a + 1) ha)
          (hcomm' a (by omega) (a + 1) ha) (hadj a ha)
      ne := fun a ha h => by
        rw [hIa a (by omega), hIa (a + 1) ha] at h
        exact hinj a (by omega) (a + 1) ha (by omega) (Subtype.ext h) }
  obtain ⟨hkN, P, hPI, hPJ⟩ := hchain.exists_frame h2 hk
  have hJ : (i₀ : Matrix (Fin (k + 3)) (Fin (k + 3)) F) * P = P * negTail F (k + 3) k := by
    refine hPJ _ h₀.coe_mul_self ?_ ?_ ?_
    · intro a ha
      rw [hIa a ha]
      exact coe_commute_of_commute (hcomm a ha)
    · intro v hv
      rw [chainFix, Submodule.mem_iInf]
      intro a
      rw [hIa a a.2]
      exact (spaces_of_commutes h2 hn3 h₀ (hR a a.2) (h0ne a a.2) (hR0 a a.2)).1 hv
    · have := h₀.finrank_minusSpace h2
      rw [show k + 3 - (k + 1) = 2 by omega]
      exact this
  have hcinj : Function.Injective (MulAut.conj P).toMonoidHom := (MulAut.conj P).injective
  let T : ∀ a, a < k → Pair (k + 3) := fun a ha =>
    natPair (k + 3) a (a + 1) (by omega) (by omega) (by omega)
  let T₀ : Pair (k + 3) := natPair (k + 3) (k + 1) (k + 2) (by omega) (by omega) (by omega)
  let Tb : Pair (k + 3) := natPair (k + 3) 0 (k + 1) (by omega) (by omega) (by omega)
  have hia : ∀ a (ha : a < k), i a = P * zElt F (T a ha) * P⁻¹ := by
    intro a ha
    have h := hPI a ha
    rw [hIa a ha, negBlock_eq_zMat (by omega : a + 2 ≤ k + 3)] at h
    have h' : i a * P = P * zElt F (T a ha) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact h
    rw [eq_mul_inv_iff_mul_eq, h']
  have hRa : ∀ a (ha : a < k), R a = (Lc F (T a ha)).map (MulAut.conj P).toMonoidHom := by
    intro a ha
    have h := hPI a ha
    rw [hIa a ha, negBlock_eq_zMat (by omega : a + 2 ≤ k + 3)] at h
    rw [(hR a ha).eq_longRootGroup h2, longRootGroup_eq_map_conj_of_mul_eq P h]
    rfl
  have hJ' : (i₀ : Matrix (Fin (k + 3)) (Fin (k + 3)) F) * P = P * zMat F (k + 3) T₀.1 := by
    rw [hJ, negTail_eq_zMat]
    rfl
  have hi0 : i₀ = P * zElt F T₀ * P⁻¹ := by
    have h' : i₀ * P = P * zElt F T₀ := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      exact hJ'
    rw [eq_mul_inv_iff_mul_eq, h']
  have hR0' : R₀ = (Lc F T₀).map (MulAut.conj P).toMonoidHom := by
    rw [h₀.eq_longRootGroup h2, longRootGroup_eq_map_conj_of_mul_eq P hJ']
    rfl
  have hconjne : ∀ {x y : SL(k + 3, F)}, x ≠ y → P * x * P⁻¹ ≠ P * y * P⁻¹ := by
    intro x y hxy h
    exact hxy (mul_left_cancel (mul_right_cancel h))
  have hmemb : ∀ {T' : Pair (k + 3)}, ∀ x : Fin (k + 3), x ∈ Tb.1 → x ∉ T'.1 →
      P * zElt F Tb * P⁻¹ ≠ P * zElt F T' * P⁻¹ := fun {T'} x hx hx' =>
    hconjne (zElt_ne_of_mem h2 hx hx')
  have hcz : ∀ T' : Pair (k + 3), Commute (P * zElt F Tb * P⁻¹) (P * zElt F T' * P⁻¹) := fun T' =>
    commute_conj (signGroup_comm (zElt_mem_signGroup Tb) (zElt_mem_signGroup T')) P
  have hk0 : (⟨0, by omega⟩ : Fin (k + 3)) ∈ Tb.1 := by simp [Tb, natPair]
  refine ⟨(Lc F Tb).map (MulAut.conj P).toMonoidHom, P * zElt F Tb * P⁻¹,
    (isLongRootSL2_Lc h2 hn2 Tb).conj P, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hi0]; exact hcz T₀
  · rw [hi0]
    exact hmemb ⟨0, by omega⟩ hk0 (by simp [T₀, natPair, Fin.ext_iff])
  · rw [hR0', commutes_map_iff _ hcinj]
    exact not_commutes_Lc_overlap h2 hn3 (i := ⟨0, by omega⟩) (j := ⟨k + 1, by omega⟩)
      (k := ⟨k + 2, by omega⟩) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
      (by simp [Fin.ext_iff])
  · rw [hia 0 (by omega)]; exact hcz _
  · rw [hia 0 (by omega)]
    exact hmemb ⟨k + 1, by omega⟩ (by simp [Tb, natPair]) (by simp [T, natPair, Fin.ext_iff]; omega)
  · rw [hRa 0 (by omega), commutes_map_iff _ hcinj]
    have hswap : Lc F Tb = Lc F (⟨{⟨k + 1, by omega⟩, ⟨0, by omega⟩},
        Finset.card_pair (by simp)⟩ : Pair (k + 3)) :=
      Lc_congr (Finset.pair_comm _ _)
    rw [hswap]
    exact not_commutes_Lc_overlap h2 hn3 (i := ⟨k + 1, by omega⟩) (j := ⟨0, by omega⟩)
      (k := ⟨1, by omega⟩) (by simp) (by simp)
      (by simp [Fin.ext_iff]; omega)
  · intro a ha1 ha
    refine ⟨?_, ?_, ?_⟩
    · rw [hia a ha]; exact hcz _
    · rw [hia a ha]
      exact hmemb ⟨0, by omega⟩ hk0 (by simp [T, natPair, Fin.ext_iff]; omega)
    · rw [hRa a ha, commutes_map_iff _ hcinj]
      refine commutes_Lc_of_disjoint h2 ?_
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Tb, T, natPair, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff] at hx hx'
      omega

end PartnerMain

end CFSG.ClassicalInvolution.RouteD

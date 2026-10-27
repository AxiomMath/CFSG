module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpPf5Std
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7F0

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Q8

variable {G : Type} [Group G]

private theorem q8_cent : ∀ g p : QuaternionGroup 2, p * p ≠ 1 → g * p = p * g →
    g = 1 ∨ g = p * p ∨ g = p ∨ g = p⁻¹ := by decide +kernel

private theorem q8_four : ∀ p : QuaternionGroup 2, p * p * (p * p) = 1 := by decide

private theorem q8_inv_conj : ∀ p : QuaternionGroup 2, p * p ≠ 1 → ∃ g, g * p * g⁻¹ = p⁻¹ := by
  decide +kernel

theorem eq_of_commute_of_q8 {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2) {x g : G} (hx : x ∈ R)
    (hg : g ∈ R) (hx2 : x * x ≠ 1) (hgx : g * x = x * g) :
    g = 1 ∨ g = x * x ∨ g = x ∨ g = x⁻¹ := by
  have key : ∀ q : R, e ⟨g, hg⟩ = e q → g = q := fun q h => congrArg Subtype.val (e.injective h)
  have hx2' : e ⟨x, hx⟩ * e ⟨x, hx⟩ ≠ 1 := by
    rw [← map_mul, ← map_one e]
    intro h
    exact hx2 (congrArg Subtype.val (e.injective h))
  have hgx' : e ⟨g, hg⟩ * e ⟨x, hx⟩ = e ⟨x, hx⟩ * e ⟨g, hg⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext hgx)
  rcases q8_cent _ _ hx2' hgx' with h | h | h | h
  · exact Or.inl (by simpa using key 1 (by rw [h, map_one]))
  · exact Or.inr (Or.inl (by simpa using key (⟨x, hx⟩ * ⟨x, hx⟩) (by rw [h, map_mul])))
  · exact Or.inr (Or.inr (Or.inl (by simpa using key ⟨x, hx⟩ h)))
  · exact Or.inr (Or.inr (Or.inr (by simpa using key (⟨x, hx⟩)⁻¹ (by rw [h, map_inv]))))

theorem sq_sq_eq_one_of_q8 {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2) {x : G} (hx : x ∈ R) :
    x * x * (x * x) = 1 := by
  have h := q8_four (e ⟨x, hx⟩)
  rw [← map_mul, ← map_mul, ← map_one e] at h
  simpa using congrArg Subtype.val (e.injective h)

theorem exists_conj_inv_of_q8 {R : Subgroup G} (e : ↥R ≃* QuaternionGroup 2) {x : G} (hx : x ∈ R)
    (hx2 : x * x ≠ 1) : ∃ r ∈ R, r * x * r⁻¹ = x⁻¹ := by
  have hx2' : e ⟨x, hx⟩ * e ⟨x, hx⟩ ≠ 1 := by
    rw [← map_mul, ← map_one e]
    intro h
    exact hx2 (congrArg Subtype.val (e.injective h))
  obtain ⟨q, hq⟩ := q8_inv_conj _ hx2'
  refine ⟨(e.symm q : R), (e.symm q).2, ?_⟩
  have h : e (e.symm q * ⟨x, hx⟩ * (e.symm q)⁻¹) = e (⟨x, hx⟩)⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply, hq]
  simpa using congrArg Subtype.val (e.injective h)

theorem eq_mul_or_eq_inv_mul_of_q8 {R₁ R₂ : Subgroup G} (e₁ : ↥R₁ ≃* QuaternionGroup 2)
    (e₂ : ↥R₂ ≃* QuaternionGroup 2) (hc : Commutes R₁ R₂) {x y a : G} (hx : x ∈ R₁) (hy : y ∈ R₂)
    (hx2 : x * x ≠ 1) (hxy : x * x = y * y) (ha : a ∈ R₁ ⊔ R₂) (hax : a * x = x * a)
    (hay : a * y = y * a) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ x * x) :
    a = x * y ∨ a = x⁻¹ * y := by
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc ha
  have ht : x * x * (x * x) = 1 := sq_sq_eq_one_of_q8 e₁ hx
  have hti : (x * x)⁻¹ = x * x := inv_eq_of_mul_eq_one_right ht
  have hy2 : y * y ≠ 1 := hxy ▸ hx2
  have hc₁ : r₁ * x = x * r₁ := by
    have h1 : r₁ * r₂ * x = r₁ * x * r₂ := by rw [mul_assoc, ← hc x hx r₂ hr₂, mul_assoc]
    have h2 : r₁ * x * r₂ = x * r₁ * r₂ := by rw [← h1, hax, mul_assoc]
    exact mul_right_cancel h2
  have hc₂ : r₂ * y = y * r₂ := by
    have h1 : y * (r₁ * r₂) = r₁ * (y * r₂) := by rw [← mul_assoc, ← hc r₁ hr₁ y hy, mul_assoc]
    have h2 : r₁ * (r₂ * y) = r₁ * (y * r₂) := by rw [← h1, ← hay, mul_assoc]
    exact mul_left_cancel h2
  have hsq : r₁ * r₁ * (r₂ * r₂) = 1 := by
    have h12 := hc r₁ hr₁ r₂ hr₂
    calc r₁ * r₁ * (r₂ * r₂) = r₁ * (r₁ * r₂) * r₂ := by group
      _ = r₁ * (r₂ * r₁) * r₂ := by rw [h12]
      _ = r₁ * r₂ * (r₁ * r₂) := by group
      _ = 1 := ha2
  have hr₂sq : r₂ * r₂ = (r₁ * r₁)⁻¹ := eq_inv_of_mul_eq_one_right hsq
  have hinvsq : r₂ = y⁻¹ → r₂ * r₂ = y * y := by
    intro h
    rw [h, ← mul_inv_rev, ← hxy, hti]
  rcases eq_of_commute_of_q8 e₁ hx hr₁ hx2 hc₁ with h₁ | h₁ | h₁
  ·
    exfalso
    have h22 : r₂ * r₂ = 1 := by rw [hr₂sq, h₁]; simp
    rcases eq_of_commute_of_q8 e₂ hy hr₂ hy2 hc₂ with h₂ | h₂ | h₂ | h₂
    · exact ha1 (by rw [h₁, h₂]; simp)
    · exact hat (by rw [h₁, h₂, one_mul, ← hxy])
    · exact hy2 (h₂ ▸ h22)
    · exact hy2 (by rw [← hinvsq h₂]; exact h22)
  ·
    exfalso
    have h22 : r₂ * r₂ = 1 := by rw [hr₂sq, h₁, ht, inv_one]
    rcases eq_of_commute_of_q8 e₂ hy hr₂ hy2 hc₂ with h₂ | h₂ | h₂ | h₂
    · exact hat (by rw [h₁, h₂, mul_one])
    · exact ha1 (by rw [h₁, h₂, ← hxy, ht])
    · exact hy2 (h₂ ▸ h22)
    · exact hy2 (by rw [← hinvsq h₂]; exact h22)
  ·
    have h11 : r₁ * r₁ = x * x := by
      rcases h₁ with h₁ | h₁
      · rw [h₁]
      · rw [h₁, ← mul_inv_rev, hti]
    have h22 : r₂ * r₂ = x * x := by rw [hr₂sq, h11, hti]
    rcases eq_of_commute_of_q8 e₂ hy hr₂ hy2 hc₂ with h₂ | h₂ | h₂ | h₂
    · exfalso; rw [h₂, one_mul] at h22; exact hx2 h22.symm
    · exfalso; rw [h₂, ← hxy, ht] at h22; exact hx2 h22.symm
    · rcases h₁ with h₁ | h₁
      · exact Or.inl (by rw [h₁, h₂])
      · exact Or.inr (by rw [h₁, h₂])
    · rcases h₁ with h₁ | h₁
      · refine Or.inr ?_
        rw [h₁, h₂]
        calc x * y⁻¹ = x⁻¹ * (x * x) * y⁻¹ := by group
          _ = x⁻¹ * (y * y) * y⁻¹ := by rw [hxy]
          _ = x⁻¹ * y := by group
      · refine Or.inl ?_
        rw [h₁, h₂]
        calc x⁻¹ * y⁻¹ = x⁻¹ * (y * y)⁻¹ * y := by group
          _ = x⁻¹ * (x * x)⁻¹ * y := by rw [← hxy]
          _ = x⁻¹ * (x * x) * y := by rw [hti]
          _ = x * y := by group

end Q8

section Twins

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_mul_or_eq_inv_mul_of_twins (hΩ : HypOmegaGen Ω) {L L' : Subgroup G} {t : G}
    (hLΩ : L ∈ Ω) (hL'Ω : L' ∈ Ω) (hne : L' ≠ L) (hzL : IsUniqueInvolution L t)
    (hzL' : IsUniqueInvolution L' t) {R₁ R₂ : Subgroup G} (hR₁ : IsSylow2In R₁ L)
    (hR₂ : IsSylow2In R₂ L') (hc : Commutes R₁ R₂) (e₁ : ↥R₁ ≃* QuaternionGroup 2)
    (e₂ : ↥R₂ ≃* QuaternionGroup 2) {B : Subgroup G} (hB2 : IsPGroup 2 B)
    (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBM : B ≤ L ⊔ L') {x y a : G} (hx : x ∈ R₁)
    (hy : y ∈ R₂) (hxB : x ∈ B) (hyB : y ∈ B) (haB : a ∈ B) (ox : orderOf x = 4)
    (oy : orderOf y = 4) (ha2 : a * a = 1) (ha1 : a ≠ 1) (hat : a ≠ t) :
    a = x * y ∨ a = x⁻¹ * y := by
  have hLN : L ≤ Subgroup.normalizer (L' : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hLΩ hL'Ω hne.symm hzL hzL'
  have hL'N : L' ≤ Subgroup.normalizer (L : Set G) :=
    Sec6Gen.le_normalizer_of_twin hΩ hL'Ω hLΩ hne hzL' hzL
  have hLC : L ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem hw).symm
  have hL'C : L' ≤ Subgroup.centralizer ({t} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hzL'.commute_of_mem hw).symm
  have hMC : L ⊔ L' ≤ Subgroup.centralizer ({t} : Set G) := sup_le hLC hL'C
  have hMNL : L ⊔ L' ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hL'N
  have hMNL' : L ⊔ L' ≤ Subgroup.normalizer (L' : Set G) := sup_le hLN Subgroup.le_normalizer
  have hQ : IsSylow2In (R₁ ⊔ R₂) (L ⊔ L') :=
    Hat2A7S.T7X.isSylow2In_sup_of_twin hΩ hLΩ hL'Ω hne hzL hzL' hR₁ hR₂ hc
  have hQ2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := hQ.2.1
  obtain ⟨V, hV, hBV⟩ := IsSylow2In.exists_ge hB2 hBM
  obtain ⟨m, hmM, hmV⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hV hQ
  have hmQ : ∀ {w : G}, w ∈ B → m * w * m⁻¹ ∈ R₁ ⊔ R₂ := fun hw => by
    rw [← hmV]; exact conj_mem_conjSub (hBV hw)
  have hmt : m * t * m⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hMC hmM)
    calc m * t * m⁻¹ = (t * m) * m⁻¹ := by rw [this]
      _ = t := by group
  have h1 : (R₁ ⊔ R₂) ⊓ L = R₁ :=
    hR₁.2.2 _ inf_le_right (hQ2.to_le inf_le_left) (le_inf le_sup_left hR₁.1)
  have h2 : (R₁ ⊔ R₂) ⊓ L' = R₂ :=
    hR₂.2.2 _ inf_le_right (hQ2.to_le inf_le_left) (le_inf le_sup_right hR₂.1)
  have hx' : m * x * m⁻¹ ∈ R₁ := by
    rw [← h1]
    exact ⟨hmQ hxB, (Subgroup.mem_normalizer_iff.1 (hMNL hmM) x).1 (hR₁.1 hx)⟩
  have hy' : m * y * m⁻¹ ∈ R₂ := by
    rw [← h2]
    exact ⟨hmQ hyB, (Subgroup.mem_normalizer_iff.1 (hMNL' hmM) y).1 (hR₂.1 hy)⟩
  have hxx : x * x = t := TwinPerp.sq_eq_of_orderOf_four hzL (hR₁.1 hx) ox
  have hyy : y * y = t := TwinPerp.sq_eq_of_orderOf_four hzL' (hR₂.1 hy) oy
  have hconj : ∀ p q : G, (m * p * m⁻¹) * (m * q * m⁻¹) = m * (p * q) * m⁻¹ := fun p q => by group
  have hinj : ∀ p q : G, m * p * m⁻¹ = m * q * m⁻¹ → p = q := fun p q h => by simpa using h
  have hx'x' : m * x * m⁻¹ * (m * x * m⁻¹) = t := by rw [hconj, hxx, hmt]
  have hy'y' : m * y * m⁻¹ * (m * y * m⁻¹) = t := by rw [hconj, hyy, hmt]
  have hcomm : ∀ {p q : G}, p ∈ B → q ∈ B → (m * p * m⁻¹) * (m * q * m⁻¹) =
      (m * q * m⁻¹) * (m * p * m⁻¹) := fun hp hq => by rw [hconj, hconj, hBab _ hp _ hq]
  have hcore := eq_mul_or_eq_inv_mul_of_q8 e₁ e₂ hc hx' hy'
    (by rw [hx'x']; exact hzL.ne_one) (by rw [hx'x', hy'y']) (hmQ haB) (hcomm haB hxB)
    (hcomm haB hyB) (by rw [hconj, ha2]; group) (fun h => ha1 (hinj _ _ (by rw [h]; group)))
    (fun h => hat (hinj _ _ (by rw [h, hx'x', hmt])))
  rcases hcore with h | h
  · exact Or.inl (hinj _ _ (by rw [h, hconj]))
  · exact Or.inr (hinj _ _ (by rw [h]; group))

end Twins

section TwoW

variable {n : ℕ}

@[expose] def P23WTrans (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      ∀ W₁ ∈ WSet (Om R), t ∈ W₁ →
        ∃ c ∈ Subgroup.centralizer ({t} : Set Y), conjSub c W = W₁

@[expose] def P23WProd (n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      ∀ W₁ ∈ WSet (Om R), t ∈ W₁ →
        ∀ L ∈ twinSet (Om R) (tightCore R), ∀ L' ∈ twinSet (Om R) (tightCore R), L' ≠ L →
          ∀ R₁ R₂ : Subgroup Y, IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ →
            ∀ x ∈ R₁, ∀ y ∈ R₂, x ∈ W₁ → y ∈ W₁ → orderOf x = 4 → orderOf y = 4 →
              ∃ c ∈ Subgroup.centralizer ({t} : Set Y), c * u * c⁻¹ = x * y

theorem nonempty_q8_of_isSylow2In {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hC : TwinPerp.CoreData n Y R S t) {L P : Subgroup Y} (hL : L ∈ Om R)
    (hP : IsSylow2In P L) : Nonempty (↥P ≃* QuaternionGroup 2) := by
  have hst := CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC
  obtain ⟨k, hk, ⟨e⟩⟩ := Sec6Gen.isQuatSub_of_mem_RSet hst.hyp (mem_RSet_of_isSylow2In hL hP)
  have hc := hst.card8 L hL P hP
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card] at hc
  have hk1 : k = 1 := by
    have h2 : 2 ^ k = 2 ^ 1 := by omega
    exact Nat.pow_right_injective le_rfl h2
  subst hk1
  exact ⟨e⟩

theorem p23WProd_of_wTrans (hT : P23WTrans n) : P23WProd n := by
  intro Y _ _ R S t K' W u e g hc W₁ hW₁ htW₁ L hL L' hL' hne R₁ R₂ hR₁ hR₂ hcm x hx y hy hxW hyW
    ox oy
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hKt := twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne
  have hzL : IsUniqueInvolution L t := isUniqueInvolution_of_mem_twinSet hz hL
  have hzL' : IsUniqueInvolution L' t := isUniqueInvolution_of_mem_twinSet hz hL'
  have hd := hc.data
  obtain ⟨c, hct, hcW⟩ := hT Y R S t K' W u e g hc W₁ hW₁ htW₁
  have hct' : c * t * c⁻¹ = t := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hct
    calc c * t * c⁻¹ = (t * c) * c⁻¹ := by rw [this]
      _ = t := by group
  have hmem2 : ∀ {J : Subgroup Y}, J ∈ twinSet (Om R) (tightCore R) → J = tightCore R ∨ J = K' :=
    fun {J} hJ => by
      have h := hJ
      rw [hKt] at h
      exact h
  have hLL : tightCore R ≤ L ⊔ L' ∧ K' ≤ L ⊔ L' := by
    rcases hmem2 hL with h1 | h1 <;> rcases hmem2 hL' with h2 | h2
    · exact absurd (h2.trans h1.symm) hne
    · exact ⟨by rw [h1]; exact le_sup_left, by rw [h2]; exact le_sup_right⟩
    · exact ⟨by rw [h2]; exact le_sup_right, by rw [h1]; exact le_sup_left⟩
    · exact absurd (h2.trans h1.symm) hne
  have hpair : ∀ J ∈ twinSet (Om R) (tightCore R), J ≤ L ⊔ L' := by
    intro J hJ
    rcases hmem2 hJ with h | h
    · rw [h]; exact hLL.1
    · rw [h]; exact hLL.2
  have haM : c * u * c⁻¹ ∈ L ⊔ L' := by
    have hle : conjSub c (tightCore R ⊔ K') ≤ L ⊔ L' := by
      rw [conjSub, Subgroup.map_sup]
      exact sup_le (hpair _ (conj_mem_twinSet hz (tightCore_mem_twinSet_of_twin
        ⟨K', hc.std.hK', hc.std.hne⟩) hct)) (hpair _ (conj_mem_twinSet hz hc.std.hK' hct))
    exact hle (conj_mem_conjSub hd.hu)
  have haW : c * u * c⁻¹ ∈ W₁ := by rw [← hcW]; exact conj_mem_conjSub hd.huW
  have hinj : ∀ p q : Y, c * p * c⁻¹ = c * q * c⁻¹ → p = q := fun p q h => by simpa using h
  obtain ⟨e₁⟩ := nonempty_q8_of_isSylow2In hC hL.1 hR₁
  obtain ⟨e₂⟩ := nonempty_q8_of_isSylow2In hC hL'.1 hR₂
  have hcore := eq_mul_or_eq_inv_mul_of_twins hΩ hL.1 hL'.1 hne hzL hzL' hR₁ hR₂ hcm e₁ e₂
    ((Asc77.Thompson.isPGroup_of_mem_WSet hW₁).to_le inf_le_left)
    (fun a ha b hb => Q3CL.Thompson.commutes_of_mem_WSet hΩ hW₁ a ha.1 b hb.1) inf_le_right
    (B := W₁ ⊓ (L ⊔ L')) hx hy ⟨hxW, Subgroup.mem_sup_left (hR₁.1 hx)⟩ ⟨hyW, Subgroup.mem_sup_right (hR₂.1 hy)⟩
    ⟨haW, haM⟩ ox oy (by calc c * u * c⁻¹ * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
      _ = 1 := by rw [hd.hu2]; group)
    (fun h => hd.hu1 (hinj _ _ (by rw [h]; group)))
    (fun h => hd.huz (hinj _ _ (by rw [h, hct'])))
  rcases hcore with h | h
  · exact ⟨c, hct, h⟩
  · have hx2 : x * x ≠ 1 := by
      rw [TwinPerp.sq_eq_of_orderOf_four hzL (hR₁.1 hx) ox]; exact hzL.ne_one
    obtain ⟨r, hr, hrx⟩ := exists_conj_inv_of_q8 e₁ hx hx2
    have hrt : r ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (hzL.commute_of_mem (hR₁.1 hr)).symm
    have hry : r * y * r⁻¹ = y := by rw [hcm r hr y hy]; group
    refine ⟨r * c, Subgroup.mul_mem _ hrt hct, ?_⟩
    calc r * c * u * (r * c)⁻¹ = r * (c * u * c⁻¹) * r⁻¹ := by group
      _ = (r * x * r⁻¹)⁻¹ * (r * y * r⁻¹) := by rw [h]; group
      _ = x * y := by rw [hrx, hry, inv_inv]

end TwoW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

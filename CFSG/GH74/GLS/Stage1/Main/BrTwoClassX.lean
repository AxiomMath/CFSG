module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassV

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

section AbstractComm

variable {X : Type} [Group X] {L₁ L₂ : Subgroup X} {z' : X}

theorem mem_pair_mul (hz2 : z' * z' = 1) {a b : X} (ha : a = 1 ∨ a = z') (hb : b = 1 ∨ b = z') :
    a * b = 1 ∨ a * b = z' := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · left
    simp
  · right
    simp
  · right
    simp
  · left
    exact hz2

theorem mem_pair_sq (hz2 : z' * z' = 1) {a : X} (ha : a = 1 ∨ a = z') : a * a = 1 := by
  rcases ha with rfl | rfl
  · simp
  · exact hz2

theorem mem_pair_comm (hzc : ∀ g : X, g * z' = z' * g) {a : X} (ha : a = 1 ∨ a = z') (g : X) :
    g * a = a * g := by
  rcases ha with rfl | rfl
  · simp
  · exact hzc g

theorem split_pair (hinter : ∀ x ∈ L₁, x ∈ L₂ → x = 1 ∨ x = z') (hz2 : z' * z' = 1)
    (hzc : ∀ g : X, g * z' = z' * g) (hz₂ : z' ∈ L₂) {a₁ b₁ a₂ b₂ c : X} (ha₁ : a₁ ∈ L₁)
    (hb₁ : b₁ ∈ L₁) (ha₂ : a₂ ∈ L₂) (hb₂ : b₂ ∈ L₂) (hc : c = 1 ∨ c = z')
    (h : b₁ * b₂ = a₁ * a₂ * c) :
    ∃ c₁ c₂ : X, (c₁ = 1 ∨ c₁ = z') ∧ (c₂ = 1 ∨ c₂ = z') ∧ b₁ = a₁ * c₁ ∧ b₂ = a₂ * c₂ ∧
      c₁ * c₂ = c := by
  have hcL₂ : c ∈ L₂ := by
    rcases hc with rfl | rfl
    · exact L₂.one_mem
    · exact hz₂
  have hmem₁ : a₁⁻¹ * b₁ ∈ L₁ := L₁.mul_mem (L₁.inv_mem ha₁) hb₁
  have hmem₂ : a₁⁻¹ * b₁ ∈ L₂ := by
    have e : a₁⁻¹ * b₁ = a₂ * c * b₂⁻¹ := by
      have : a₁⁻¹ * (b₁ * b₂) = a₂ * c := by rw [h]; group
      calc a₁⁻¹ * b₁ = a₁⁻¹ * (b₁ * b₂) * b₂⁻¹ := by group
        _ = a₂ * c * b₂⁻¹ := by rw [this]
    rw [e]
    exact L₂.mul_mem (L₂.mul_mem ha₂ hcL₂) (L₂.inv_mem hb₂)
  obtain ⟨c₁, hc₁def⟩ : ∃ c₁ : X, c₁ = a₁⁻¹ * b₁ := ⟨_, rfl⟩
  have hc₁ : c₁ = 1 ∨ c₁ = z' := by
    rw [hc₁def]
    exact hinter _ hmem₁ hmem₂
  have hb₁eq : b₁ = a₁ * c₁ := by
    rw [hc₁def]
    group
  have hc₁sq : c₁ * c₁ = 1 := mem_pair_sq hz2 hc₁
  have hb₂eq : b₂ = a₂ * (c₁ * c) := by
    have h1 : a₁ * (c₁ * b₂) = a₁ * (a₂ * c) := by
      calc a₁ * (c₁ * b₂) = a₁ * c₁ * b₂ := by rw [mul_assoc]
        _ = b₁ * b₂ := by rw [← hb₁eq]
        _ = a₁ * a₂ * c := h
        _ = a₁ * (a₂ * c) := by rw [mul_assoc]
    have h2 : c₁ * b₂ = a₂ * c := mul_left_cancel h1
    have h3 : b₂ = c₁ * (a₂ * c) := by
      calc b₂ = (c₁ * c₁) * b₂ := by rw [hc₁sq, one_mul]
        _ = c₁ * (c₁ * b₂) := by rw [mul_assoc]
        _ = c₁ * (a₂ * c) := by rw [h2]
    calc b₂ = c₁ * (a₂ * c) := h3
      _ = (c₁ * a₂) * c := by rw [mul_assoc]
      _ = (a₂ * c₁) * c := by rw [← mem_pair_comm hzc hc₁ a₂]
      _ = a₂ * (c₁ * c) := by rw [mul_assoc]
  exact ⟨c₁, c₁ * c, hc₁, mem_pair_mul hz2 hc₁ hc, hb₁eq, hb₂eq, by rw [← mul_assoc, hc₁sq, one_mul]⟩

theorem conj_fix_of_swap (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hinter : ∀ x ∈ L₁, x ∈ L₂ → x = 1 ∨ x = z') (hz2 : z' * z' = 1)
    (hzc : ∀ g : X, g * z' = z' * g) (hz₂ : z' ∈ L₂) {u' t' w' : X} (hu : u' ∈ L₁ ⊔ L₂)
    (ht₁ : ∀ a ∈ L₁, t' * a * t'⁻¹ ∈ L₂) (ht₂ : ∀ b ∈ L₂, t' * b * t'⁻¹ ∈ L₁) (ht2 : t' * t' = 1)
    (htu : t' * u' * t'⁻¹ = u' ∨ t' * u' * t'⁻¹ = u' * z')
    (hw₁ : ∀ a ∈ L₁, w' * a * w'⁻¹ ∈ L₁) (hw₂ : ∀ b ∈ L₂, w' * b * w'⁻¹ ∈ L₂)
    (hwu : w' * u' * w'⁻¹ = u' ∨ w' * u' * w'⁻¹ = u' * z') (htw : t' * w' = w' * t') :
    w' * u' * w'⁻¹ = u' := by
  obtain ⟨a₁, ha₁, a₂, ha₂, hu'⟩ :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hu
  have hc_of : ∀ s : X, (s * u' * s⁻¹ = u' ∨ s * u' * s⁻¹ = u' * z') →
      ∃ c, (c = 1 ∨ c = z') ∧ s * u' * s⁻¹ = u' * c := by
    intro s h
    rcases h with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨z', Or.inr rfl, h⟩
  obtain ⟨c, hc, hcu⟩ := hc_of t' htu
  have hb₂ : t' * a₁ * t'⁻¹ ∈ L₂ := ht₁ a₁ ha₁
  have hb₁ : t' * a₂ * t'⁻¹ ∈ L₁ := ht₂ a₂ ha₂
  have hprod : (t' * a₂ * t'⁻¹) * (t' * a₁ * t'⁻¹) = a₁ * a₂ * c := by
    calc (t' * a₂ * t'⁻¹) * (t' * a₁ * t'⁻¹) = (t' * a₁ * t'⁻¹) * (t' * a₂ * t'⁻¹) :=
          hcomm _ hb₁ _ hb₂
      _ = t' * (a₁ * a₂) * t'⁻¹ := by group
      _ = a₁ * a₂ * c := by rw [← hu']; exact hcu
  obtain ⟨c₁, c₂, hc₁, hc₂, hb₁eq, hb₂eq, hcc⟩ :=
    split_pair hinter hz2 hzc hz₂ ha₁ hb₁ ha₂ hb₂ hc hprod
  have hct₂ : t' * c₂ * t'⁻¹ = c₂ := by
    have := mem_pair_comm hzc hc₂ t'
    rw [this]
    group
  have hc1 : c = 1 := by
    have h1 : t' * (t' * a₁ * t'⁻¹) * t'⁻¹ = a₁ := by
      calc t' * (t' * a₁ * t'⁻¹) * t'⁻¹ = (t' * t') * a₁ * (t' * t')⁻¹ := by group
        _ = a₁ := by rw [ht2]; group
    have h2 : t' * (t' * a₁ * t'⁻¹) * t'⁻¹ = a₁ * (c₁ * c₂) := by
      rw [hb₂eq]
      calc t' * (a₂ * c₂) * t'⁻¹ = (t' * a₂ * t'⁻¹) * (t' * c₂ * t'⁻¹) := by group
        _ = (a₁ * c₁) * c₂ := by rw [hct₂, hb₁eq]
        _ = a₁ * (c₁ * c₂) := by rw [mul_assoc]
    have h3 : a₁ * (c₁ * c₂) = a₁ * 1 := by rw [← h2, h1, mul_one]
    rw [← hcc]
    exact mul_left_cancel h3
  obtain ⟨c', hc', hcu'⟩ := hc_of w' hwu
  have hd₁ : w' * a₁ * w'⁻¹ ∈ L₁ := hw₁ a₁ ha₁
  have hd₂ : w' * a₂ * w'⁻¹ ∈ L₂ := hw₂ a₂ ha₂
  have hprod' : (w' * a₁ * w'⁻¹) * (w' * a₂ * w'⁻¹) = a₁ * a₂ * c' := by
    calc (w' * a₁ * w'⁻¹) * (w' * a₂ * w'⁻¹) = w' * (a₁ * a₂) * w'⁻¹ := by group
      _ = a₁ * a₂ * c' := by rw [← hu']; exact hcu'
  obtain ⟨e₁, e₂, he₁, he₂, hd₁eq, hd₂eq, hee⟩ :=
    split_pair hinter hz2 hzc hz₂ ha₁ hd₁ ha₂ hd₂ hc' hprod'
  have key : t' * (w' * a₁ * w'⁻¹) * t'⁻¹ = w' * (t' * a₁ * t'⁻¹) * w'⁻¹ := by
    calc t' * (w' * a₁ * w'⁻¹) * t'⁻¹ = (t' * w') * a₁ * (t' * w')⁻¹ := by group
      _ = (w' * t') * a₁ * (w' * t')⁻¹ := by rw [htw]
      _ = w' * (t' * a₁ * t'⁻¹) * w'⁻¹ := by group
  have hct₁ : t' * e₁ * t'⁻¹ = e₁ := by
    have := mem_pair_comm hzc he₁ t'
    rw [this]
    group
  have hcw₂ : w' * c₂ * w'⁻¹ = c₂ := by
    have := mem_pair_comm hzc hc₂ w'
    rw [this]
    group
  have hL : t' * (w' * a₁ * w'⁻¹) * t'⁻¹ = a₂ * c₂ * e₁ := by
    rw [hd₁eq]
    calc t' * (a₁ * e₁) * t'⁻¹ = (t' * a₁ * t'⁻¹) * (t' * e₁ * t'⁻¹) := by group
      _ = a₂ * c₂ * e₁ := by rw [hct₁, hb₂eq]
  have hR : w' * (t' * a₁ * t'⁻¹) * w'⁻¹ = a₂ * e₂ * c₂ := by
    rw [hb₂eq]
    calc w' * (a₂ * c₂) * w'⁻¹ = (w' * a₂ * w'⁻¹) * (w' * c₂ * w'⁻¹) := by group
      _ = a₂ * e₂ * c₂ := by rw [hcw₂, hd₂eq]
  have h4 : a₂ * c₂ * e₁ = a₂ * e₂ * c₂ := by rw [← hL, key, hR]
  have h5 : c₂ * e₁ = c₂ * e₂ := by
    have h6 : a₂ * (c₂ * e₁) = a₂ * (c₂ * e₂) := by
      calc a₂ * (c₂ * e₁) = a₂ * c₂ * e₁ := by rw [mul_assoc]
        _ = a₂ * e₂ * c₂ := h4
        _ = a₂ * (e₂ * c₂) := by rw [mul_assoc]
        _ = a₂ * (c₂ * e₂) := by rw [mem_pair_comm hzc hc₂ e₂]
    exact mul_left_cancel h6
  have h7 : e₁ = e₂ := mul_left_cancel h5
  have hc'1 : c' = 1 := by
    rw [← hee, h7]
    exact mem_pair_sq hz2 he₂
  rw [hcu', hc'1, mul_one]

end AbstractComm

section AbstractPGL

theorem card_statedSL_two_main (F : Type) [Field F] [Finite F] :
    Nat.card (StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

open CFSG.GorensteinWalter

variable {X : Type} [Group X] [Finite X]

theorem pglOver_involution_facts {L : Subgroup X} {y : X} {r : ℕ} (hodd : Odd r) (h3 : 3 < r)
    (hL : HasSL2Model ↥L (fun s => s = r)) (hZ2 : Nat.card ↥(center ↥L) = 2)
    (h : PGLOver L (zpowers y) r) :
    y ∈ normalizer (L : Set X) ∧ y ∉ L ∧
      ∀ c ∈ centralizer (L : Set X), c ∈ L ⊔ zpowers y → c ∈ L := by
  classical
  obtain ⟨hZn, F, iF, fF, hFr, ⟨φ⟩⟩ := h
  set A : Subgroup X := L ⊔ zpowers y with hA
  set Z : Subgroup X := (center ↥L).map L.subtype with hZdef
  have hLA : L ≤ A := le_sup_left
  have hZL : Z ≤ L := Subgroup.map_subtype_le _
  have hZA : Z ≤ A := hZL.trans hLA
  have hq5 : 5 ≤ r := by
    obtain ⟨m, hm⟩ := hodd
    omega
  obtain ⟨F', iF', fF', hF'r, ⟨e⟩⟩ := hL
  have hcardL : Nat.card ↥L = r * (r ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, card_statedSL_two_main, hF'r]
  have hcardPGL : Nat.card (PGL2 F) = r * (r ^ 2 - 1) := by
    rw [pgl2_card_formula, hFr]
  have hcardZ : Nat.card ↥(Z.subgroupOf A) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZA).toEquiv, hZdef,
      Subgroup.card_map_of_injective L.subtype_injective, hZ2]
  have hcardA : Nat.card ↥A = 2 * Nat.card ↥L := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf A)
    rw [hcardZ, Nat.card_congr φ.toEquiv, hcardPGL] at h1
    rw [h1, hcardL]
    ring
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have hidx : (L.subgroupOf A).index = 2 := by
    have h1 := Subgroup.index_mul_card (L.subgroupOf A)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLA).toEquiv, hcardA] at h1
    exact Nat.eq_of_mul_eq_mul_right hLpos h1
  have hnormal : (L.subgroupOf A).Normal := Subgroup.normal_of_index_eq_two hidx
  have hAN : A ≤ normalizer (L : Set X) := (Subgroup.normal_subgroupOf_iff_le_normalizer hLA).1 hnormal
  refine ⟨hAN (Subgroup.mem_sup_right (mem_zpowers y)), ?_, ?_⟩
  · intro hyL
    have : A = L := by
      rw [hA]
      exact sup_eq_left.2 (Subgroup.zpowers_le.2 hyL)
    rw [this] at hcardA
    omega
  · intro c hc hcA
    have hperf : Group.IsPerfect ↥L := (CFSG.GH74.GLS.Stage1.Main.quasi_of_hasSL2 hq5 ⟨F', iF', fF', hF'r, ⟨e⟩⟩).1
    have hFodd : Odd (Nat.card F) := by rw [hFr]; exact hodd
    have hFop := CFSG.ABGLocalTools.isOddPrimePower_card_of_odd hFodd
    have hF3 : 3 < Nat.card F := by rw [hFr]; exact h3
    have hrel : L.relIndex A ≤ 2 := by
      show (L.subgroupOf A).index ≤ 2
      omega
    have := inf_centralizer_le_Z hLA hperf hrel hFop hF3 φ
    exact hZL (this ⟨hcA, hc⟩)

end AbstractPGL

section ConcreteGood

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ} {t u : G}

theorem card_center_imgBar (hII : II4_4_4_center) (hs : Std4 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) {q : ℕ} (hL : HasSL2Model ↥(imgBar z K) (fun r => r = q)) :
    Nat.card ↥(center ↥(imgBar z K)) = 2 := by
  have hZeq := center_imgBar_eq hII hs hK hL
  have hzb1 : piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ ≠ 1 := (zbar_facts4 hII hs).2
  have hzb2 : piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ *
      piC z ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, mem_centralizer_singleton_iff.2 rfl⟩ : ↥(Cz z)) *
        ⟨z, mem_centralizer_singleton_iff.2 rfl⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hs.orderOf_z)
    rw [this, map_one]
  have h1 : Nat.card ↥((center ↥(imgBar z K)).map (imgBar z K).subtype) =
      Nat.card ↥(center ↥(imgBar z K)) :=
    Subgroup.card_map_of_injective (imgBar z K).subtype_injective
  rw [← h1, hZeq, Nat.card_zpowers]
  exact orderOf_eq_prime (by rwa [pow_two]) hzb1

omit [Finite G] in
theorem piC_conj {s x : G} (hs : s ∈ Cz z) (hx : x ∈ Cz z) :
    piC z ⟨s * x * s⁻¹, (Cz z).mul_mem ((Cz z).mul_mem hs hx) ((Cz z).inv_mem hs)⟩ =
      piC z ⟨s, hs⟩ * piC z ⟨x, hx⟩ * (piC z ⟨s, hs⟩)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem w_comm_u (hII : II4_4_4_center) (hcfg : Cfg7 G z S K₁ K₂ t u q)
    (hL₁ : HasSL2Model ↥(imgBar z K₁) (fun r => r = q)) {w : G} (hwS : w ∈ S) (htw : t * w = w * t)
    (hwN₁ : w ∈ normalizer (K₁ : Set G)) : w * u = u * w := by
  have hs : Std4 G z S K₁ K₂ := hcfg.std.std
  have hM := m4_of_std hII hs
  have hSC : S ≤ Cz z := hs.sylow.le
  have hwC : w ∈ Cz z := hSC hwS
  have htS : t ∈ S := hcfg.ch.t_mem
  have htC : t ∈ Cz z := hSC htS
  have ht2 : t * t = 1 := mul_self_of_isConj hs.orderOf_z hcfg.ch.t_conj
  have huS : u ∈ S := hcfg.ch.u_mem.1
  have huC : u ∈ Cz z := hSC huS
  have hzC : z ∈ Cz z := mem_centralizer_singleton_iff.2 rfl
  have hwN₂ : w ∈ normalizer (K₂ : Set G) := mem_normalizer_swap hs hwC hwN₁
  have huK : u ∈ K₁ ⊔ K₂ := by
    have := hcfg.ch.u_mem.2
    rwa [hs.rigidProduct_eq] at this
  obtain ⟨hzfacts, hzb1⟩ := zbar_facts4 hII hs
  have hz2b : piC z ⟨z, hzC⟩ * piC z ⟨z, hzC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨z, hzC⟩ : ↥(Cz z)) * ⟨z, hzC⟩ = 1 :=
      Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hs.orderOf_z)
    rw [this, map_one]
  have hzcb : ∀ g : CentralizerBar z, g * piC z ⟨z, hzC⟩ = piC z ⟨z, hzC⟩ * g := fun g =>
    Subgroup.mem_center_iff.1 (toBar_z_mem_center z) g
  have hcenter := center_imgBar_eq hII hs (Or.inl rfl) hL₁
  have hinter : ∀ x ∈ imgBar z K₁, x ∈ imgBar z K₂ → x = 1 ∨ x = piC z ⟨z, hzC⟩ := by
    intro x hx1 hx2
    have hxc : x ∈ (center ↥(imgBar z K₁)).map (imgBar z K₁).subtype := by
      refine ⟨⟨x, hx1⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (imgBar_comm4 hII hs g.1 g.2 x hx2)
    rw [hcenter] at hxc
    exact eq_one_or_eq_of_mem_zpowers_sq hz2b hxc
  have hu : piC z ⟨u, huC⟩ ∈ imgBar z K₁ ⊔ imgBar z K₂ := by
    rw [← map_K12 hII hs]
    exact ⟨⟨u, huC⟩, huK, rfl⟩
  obtain ⟨_, hsw1, hsw2⟩ := swaps_of_interchanges hM.K₁_le hM.K₂_le htC hcfg.ch.t_swap
  have ht₁ : ∀ a ∈ imgBar z K₁, piC z ⟨t, htC⟩ * a * (piC z ⟨t, htC⟩)⁻¹ ∈ imgBar z K₂ := by
    intro a ha
    have : a ∈ conjugate (imgBar z K₂) (toBar z ⟨t, htC⟩) := by rw [hsw2]; exact ha
    exact mem_conjugate_iff.1 this
  have ht₂ : ∀ b ∈ imgBar z K₂, piC z ⟨t, htC⟩ * b * (piC z ⟨t, htC⟩)⁻¹ ∈ imgBar z K₁ := by
    intro b hb
    have : b ∈ conjugate (imgBar z K₁) (toBar z ⟨t, htC⟩) := by rw [hsw1]; exact hb
    exact mem_conjugate_iff.1 this
  have hnorm_bar : ∀ {s : G} (hsS : s ∈ S),
      piC z ⟨s, hSC hsS⟩ * piC z ⟨u, huC⟩ * (piC z ⟨s, hSC hsS⟩)⁻¹ = piC z ⟨u, huC⟩ ∨
      piC z ⟨s, hSC hsS⟩ * piC z ⟨u, huC⟩ * (piC z ⟨s, hSC hsS⟩)⁻¹ =
        piC z ⟨u, huC⟩ * piC z ⟨z, hzC⟩ := by
    intro s hsS
    rw [← piC_conj (hSC hsS) huC]
    rcases hcfg.ch.u_norm s hsS with h | h
    · left
      congr 1
      exact Subtype.ext h
    · right
      have : (⟨s * u * s⁻¹, (Cz z).mul_mem ((Cz z).mul_mem (hSC hsS) huC) ((Cz z).inv_mem (hSC hsS))⟩ :
          ↥(Cz z)) = ⟨u, huC⟩ * ⟨z, hzC⟩ := Subtype.ext h
      rw [this, map_mul]
  have htw' : piC z ⟨t, htC⟩ * piC z ⟨w, hwC⟩ = piC z ⟨w, hwC⟩ * piC z ⟨t, htC⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext htw
  have ht2' : piC z ⟨t, htC⟩ * piC z ⟨t, htC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨t, htC⟩ : ↥(Cz z)) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
    rw [this, map_one]
  have hwb₁ := bar_mem_normalizer hM.K₁_le hwC hwN₁
  have hwb₂ := bar_mem_normalizer hM.K₂_le hwC hwN₂
  have key := conj_fix_of_swap (imgBar_comm4 hII hs) hinter hz2b hzcb hzfacts.2 hu ht₁ ht₂ ht2'
    (hnorm_bar htS) (fun a ha => (Subgroup.mem_normalizer_iff.1 hwb₁ a).1 ha)
    (fun b hb => (Subgroup.mem_normalizer_iff.1 hwb₂ b).1 hb) (hnorm_bar hwS) htw'
  rcases hcfg.ch.u_norm w hwS with h | h
  · have e : w * u = u * w := by
      calc w * u = (w * u * w⁻¹) * w := by group
        _ = u * w := by rw [h]
    exact e
  · exfalso
    have h2 : piC z ⟨w * u * w⁻¹, (Cz z).mul_mem ((Cz z).mul_mem hwC huC) ((Cz z).inv_mem hwC)⟩ =
        piC z ⟨u, huC⟩ * piC z ⟨z, hzC⟩ := by
      have : (⟨w * u * w⁻¹, (Cz z).mul_mem ((Cz z).mul_mem hwC huC) ((Cz z).inv_mem hwC)⟩ :
          ↥(Cz z)) = ⟨u, huC⟩ * ⟨z, hzC⟩ := Subtype.ext h
      rw [this, map_mul]
    rw [piC_conj hwC huC, key] at h2
    have : piC z ⟨u, huC⟩ * piC z ⟨z, hzC⟩ = piC z ⟨u, huC⟩ * 1 := by rw [← h2, mul_one]
    exact hzb1 (mul_left_cancel this)

theorem sets_transfer {X : Type} {L₁ L₂ M₁ M₂ : X} (h : ({L₁, L₂} : Set X) = {M₁, M₂}) (P : X → Prop)
    (h₁ : P L₁) (h₂ : P L₂) : P M₁ ∧ P M₂ := by
  rcases Set.pair_eq_pair_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · subst e1 e2
    exact ⟨h₁, h₂⟩
  · subst e1 e2
    exact ⟨h₂, h₁⟩

theorem good_conj (hII : II4_4_4_center) (hcfg : Cfg7 G z S K₁ K₂ t u q)
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hpair : Stage1Pair G z S q L₁ L₂)
    (hsets : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {imgBar z K₁, imgBar z K₂})
    {w : G} (hw : Concl72abcf z S K₁ K₂ t q w) (hw1 : w ≠ 1) (hwz : IsConj z w)
    (h31c : IVK_3_1c_lifted) {y : G} (hy : GoodInvolution z S L₁ L₂ q y) : IsConj z y := by
  have hs : Std4 G z S K₁ K₂ := hcfg.std.std
  have hM := m4_of_std hII hs
  have hSC : S ≤ Cz z := hs.sylow.le
  obtain ⟨hyS, hyo, hP₁, hP₂⟩ := hy
  have hyC : y ∈ Cz z := hSC hyS
  have hbar : barOf z (zpowers y) = zpowers (piC z ⟨y, hyC⟩) := barOf_zpowers hyC
  have hA12 : imgBar z K₁ ≠ imgBar z K₂ := by
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact hpair.ne
    · rw [← h1, ← h2]
      exact hpair.ne.symm
  have hSLP : ∀ K, (K = K₁ ∨ K = K₂) → HasSL2Model ↥(imgBar z K) (fun r => r = q) ∧
      PGLOver (imgBar z K) (barOf z (zpowers y)) q := by
    have := sets_transfer hsets (fun L => HasSL2Model ↥L (fun r => r = q) ∧
      PGLOver L (barOf z (zpowers y)) q) ⟨hpair.sl₁, hP₁⟩ ⟨hpair.sl₂, hP₂⟩
    intro K hK
    rcases hK with h | h
    · rw [h]
      exact this.1
    · rw [h]
      exact this.2
  have hfacts : ∀ K, (K = K₁ ∨ K = K₂) →
      piC z ⟨y, hyC⟩ ∈ normalizer ((imgBar z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) ∧
      piC z ⟨y, hyC⟩ ∉ imgBar z K ∧
      ∀ c ∈ centralizer ((imgBar z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)),
        c ∈ imgBar z K ⊔ zpowers (piC z ⟨y, hyC⟩) → c ∈ imgBar z K := by
    intro K hK
    obtain ⟨hL, hP⟩ := hSLP K hK
    rw [hbar] at hP
    exact pglOver_involution_facts hpair.odd hpair.gt3 hL (card_center_imgBar hII hs hK hL) hP
  have hw' := hw
  obtain ⟨hwS, hwo, htw, -, hS1, hint, hf⟩ := hw
  have hwo2 : orderOf w = 2 := hwo.resolve_left hw1
  have hw2 : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hwo2
  have hyN₁ : y ∈ normalizer (K₁ : Set G) :=
    mem_normalizer_of_bar hII hs hA12 hyC (hfacts K₁ (Or.inl rfl)).1
  have hy1 : y ∈ CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ := ⟨hyS, hyN₁⟩
  rw [hS1] at hy1
  have hzw : zpowers w ≤ normalizer ((Pz S z : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.2 hwS).trans (S_le_normalizer_Pz hII hs)
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (Pz S z) (zpowers w) hzw
  have hy' : y ∈ ((Pz S z : Subgroup G) : Set G) * ((zpowers w : Subgroup G) : Set G) := by
    rw [← hmul]
    exact hy1
  obtain ⟨p, hp, a, ha, hpa⟩ := Set.mem_mul.1 hy'
  rcases eq_one_or_eq_of_mem_zpowers_sq hw2 ha with h | h
  ·
    exfalso
    rw [h] at hpa
    have hyP : y ∈ Pz S z := by
      rw [← hpa, mul_one]
      exact hp
    have hyK : y ∈ K₁ ⊔ K₂ := by
      have := hyP.2
      rwa [hs.rigidProduct_eq] at this
    have hybar : piC z ⟨y, hyC⟩ ∈ imgBar z K₁ ⊔ imgBar z K₂ := by
      rw [← map_K12 hII hs]
      exact ⟨⟨y, hyC⟩, hyK, rfl⟩
    obtain ⟨a₁, ha₁, a₂, ha₂, hya⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' (imgBar_comm4 hII hs) hybar
    have ha₂C : a₂ ∈ centralizer ((imgBar z K₁ : Subgroup (CentralizerBar z)) :
        Set (CentralizerBar z)) :=
      Subgroup.mem_centralizer_iff.2 fun l hl => imgBar_comm4 hII hs l hl a₂ ha₂
    have ha₂A : a₂ ∈ imgBar z K₁ ⊔ zpowers (piC z ⟨y, hyC⟩) := by
      have : a₂ = a₁⁻¹ * piC z ⟨y, hyC⟩ := by rw [hya]; group
      rw [this]
      exact (imgBar z K₁ ⊔ zpowers (piC z ⟨y, hyC⟩)).mul_mem
        ((imgBar z K₁ ⊔ zpowers (piC z ⟨y, hyC⟩)).inv_mem (Subgroup.mem_sup_left ha₁))
        (Subgroup.mem_sup_right (mem_zpowers _))
    have ha₂L := (hfacts K₁ (Or.inl rfl)).2.2 a₂ ha₂C ha₂A
    exact (hfacts K₁ (Or.inl rfl)).2.1 (by rw [hya]; exact (imgBar z K₁).mul_mem ha₁ ha₂L)
  ·
    rw [h] at hpa
    have hpw : y * w⁻¹ ∈ Pz S z := by
      rw [← hpa, mul_inv_cancel_right]
      exact hp
    have hw1' : w * w⁻¹ ∈ Pz S z := by
      rw [mul_inv_cancel]
      exact (Pz S z).one_mem
    obtain ⟨c, -, hc⟩ := h31c G z S K₁ K₂ t u q w hcfg hw' hw1 w hwS y hyS hw1' hpw hwo2 hyo
    exact hwz.trans (isConj_iff.2 ⟨c, hc⟩)

theorem l4nfGood_proved (hII : II4_4_4_center) (h41 : Prop4_1) (h72 : Prop7_2)
    (h31c : IVK_3_1c_lifted) : L4NFGood := by
  intro G _ _ z S q w ε hcen hT hw hε L₁ L₂ hpair K₁ K₂ t u hcfg hsets
  have hs : Std4 G z S K₁ K₂ := hcfg.std.std
  have hSC : S ≤ Cz z := hs.sylow.le
  obtain ⟨w₇, hw₇, hde₇⟩ := h72 G z S K₁ K₂ t u q hcfg
  have hLB : LBar z = imgBar z K₁ ⊔ imgBar z K₂ := by
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← hpair.prod.1, h1, h2]
    · rw [← hpair.prod.1, h1, h2, sup_comm]
  have hw₇' := hw₇
  obtain ⟨hwS, hwo, htw, ⟨-, hSPY⟩, hS1, -, hf⟩ := hw₇
  have ht2 : t * t = 1 := mul_self_of_isConj hs.orderOf_z hde₇.1.1
  have hw71 : w₇ ≠ 1 := by
    intro h1
    have hY : Ysub t w₇ = zpowers t := by
      rw [h1]
      simp [Ysub]
    have hSP : S = Pz S z ⊔ zpowers t := by
      have := hSPY
      rwa [hY] at this
    exact w7_ne_one hII h41 hT hw hs hLB hcfg.ch.t_mem ht2 hSP
  have hwo2 : orderOf w₇ = 2 := hwo.resolve_left hw71
  have hw2 : w₇ * w₇ = 1 := mul_self_eq_one_of_orderOf_eq_two hwo2
  have hwC : w₇ ∈ Cz z := hSC hwS
  have hwN₁ : w₇ ∈ normalizer (K₁ : Set G) := by
    have : w₇ ∈ CFSG.GH74.GLS.Stage1.Thm3.Sec5.S1 S K₁ := by
      rw [hS1]
      exact Subgroup.mem_sup_right (mem_zpowers w₇)
    exact this.2
  have hwN₂ : w₇ ∈ normalizer (K₂ : Set G) := mem_normalizer_swap hs hwC hwN₁
  have hwz : IsConj z w₇ := hde₇.2.2 hw71
  have hSL : HasSL2Model ↥(imgBar z K₁) (fun r => r = q) ∧
      HasSL2Model ↥(imgBar z K₂) (fun r => r = q) :=
    sets_transfer hsets (fun L => HasSL2Model ↥L (fun r => r = q)) hpair.sl₁ hpair.sl₂
  have hPGL : ∀ K, (K = K₁ ∨ K = K₂) → HasSL2Model ↥(imgBar z K) (fun r => r = q) →
      PGLOver (imgBar z K) (barOf z (zpowers w₇)) q := by
    intro K hK hL
    have hKmem : K ∈ ({K₁, K₂} : Set (Subgroup G)) := by
      rcases hK with h | h
      · rw [h]
        exact Or.inl rfl
      · rw [h]
        exact Or.inr rfl
    obtain ⟨Fq, iF, fF, hq, hpgl⟩ := hf hw71 K hKmem
    have hwNK : w₇ ∈ normalizer (K : Set G) := by
      rcases hK with h | h
      · rw [h]
        exact hwN₁
      · rw [h]
        exact hwN₂
    exact pglOver_of_pglQuot hII hs hK hL hwC hw2 hwNK hq hpgl
  have hgood : GoodInvolution z S L₁ L₂ q w₇ := by
    have := sets_transfer hsets.symm (fun L => PGLOver L (barOf z (zpowers w₇)) q)
      (hPGL K₁ (Or.inl rfl) hSL.1) (hPGL K₂ (Or.inr rfl) hSL.2)
    exact ⟨hwS, hwo2, this.1, this.2⟩
  have hcomm : w₇ * u = u * w₇ := w_comm_u hII hcfg hSL.1 hwS htw hwN₁
  exact ⟨⟨w₇, hgood, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩,
    fun y hy => good_conj hII hcfg hpair hsets hw₇' hw71 hwz h31c hy⟩

end ConcreteGood

end CFSG.GH74.GLS.Stage1.Main

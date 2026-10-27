module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionShapes
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherShapeExclusionCenter
public import CFSG.LocalAnalysis.RankTwoShapes.SylowShapes

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

open Subgroup

variable {G : Type} [Group G]

structure Setting (A : Subgroup G) (S₀ : Sylow 2 A) (t x ρ : G) (k : ℕ) : Prop where
  quasi : CFSG.Open.IsQuasisimple A
  t_norm : t ∈ normalizer (A : Set G)
  config : Config ((S₀ : Subgroup A).map A.subtype) t x ρ k

theorem false_of_few_involutions {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (T : Sylow 2 X) {V : Subgroup X}
    (hV : Assembly.IsElemAbelian 2 V) (hV4 : Nat.card V = 4)
    (hinv : ∀ g ∈ (T : Subgroup X), g ^ 2 = 1 → g ∈ V) (h8 : 8 ≤ Nat.card (T : Subgroup X))
    (h64 : Nat.card (T : Subgroup X) = 64 → ∃ g ∈ (T : Subgroup X), g ^ 4 ≠ 1) : False := by
  have hrank : Assembly.twoRank X = 2 :=
    twoRank_eq_two T hV hV4 fun E hET hE => card_le_four_of_involutions_mem hV4 hinv E hET hE
  have hshape : IsRankTwoSylowShape (T : Subgroup X) :=
    CFSG.RankTwoShapes.rank_two_sylow_shapes hnonab hrank T
  have hV' : Nat.card (V.subgroupOf (T : Subgroup X)) ≤ 4 := by
    rw [← hV4]
    exact Nat.card_le_card_of_injective (fun g => (⟨(g : X), g.2⟩ : V)) (fun a b hab => by
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa using this)
  refine false_of_shape_few_involutions hshape hV' (fun g hg => ?_) h8 (fun h64' => ?_)
  · exact mem_subgroupOf.2 (hinv g g.2 (by simpa using congrArg Subtype.val hg))
  · obtain ⟨g, hgT, hg⟩ := h64 h64'
    exact ⟨⟨g, hgT⟩, fun h1 => hg (by simpa using congrArg Subtype.val h1)⟩

namespace Setting

variable {A : Subgroup G} {S₀ : Sylow 2 A} {t x ρ : G} {k : ℕ}

theorem S_le_A (_ : Setting A S₀ t x ρ k) : (S₀ : Subgroup A).map A.subtype ≤ A :=
  map_subtype_le _

theorem x_sq_not_central_of_outside [Finite G] (hs : Setting A S₀ t x ρ k) {g : G}
    (hgS : g ∈ (S₀ : Subgroup A).map A.subtype) (hgM : g ∉ zpowers ρ ⊔ zpowers x)
    (hg2 : g ^ 2 ∈ zpowers ρ) (hgi : ∀ i : ℤ, (g * ρ ^ i) ^ 2 ≠ 1) :
    x ^ 2 ∉ centralizer (A : Set G) := by
  intro hz
  have h := hs.config
  have hgN : g ∈ normalizer (zpowers ρ : Set G) := by
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hw
      rw [← _root_.conj_zpow]
      exact zpow_mem (h.conj_rho_mem hgS) i
    · intro hw
      obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hw
      have : w = g⁻¹ * ρ ^ i * g⁻¹⁻¹ := by rw [hi]; group
      rw [this, ← _root_.conj_zpow]
      exact zpow_mem (h.conj_rho_mem (inv_mem hgS)) i
  have hg_not : g ∉ zpowers ρ := fun h' => hgM (mem_sup_left h')
  set K := zpowers ρ ⊔ zpowers g with hK
  have hKS : K ≤ (S₀ : Subgroup A).map A.subtype :=
    sup_le (zpowers_le.2 h.rho_mem) (zpowers_le.2 hgS)
  have hcardK : Nat.card ((S₀ : Subgroup A).map A.subtype) = 2 * Nat.card K := by
    rw [hK, Lemma37.card_sup_zpowers hgN hg2 hg_not, Nat.card_zpowers, h.rho_order, h.card]
    ring
  have heK : h.e ∉ K := by
    intro heK
    rcases (Lemma37.mem_sup_zpowers_iff hgN hg2).1 heK with h1 | h1
    · exact h.e_not_mem h1
    · apply hgM
      have : g = h.e * (g⁻¹ * h.e)⁻¹ := by group
      rw [this]
      exact mul_mem h.e_mem_M (inv_mem (mem_sup_left h1))
  have he_order : orderOf h.e = 2 :=
    orderOf_eq_prime h.e_sq fun h1 => h.e_not_mem (h1 ▸ one_mem _)
  obtain ⟨a, haA, haK⟩ := exists_conj_mem_of_index_two_subgroup
    (commutator_eq_self_of_quasisimple hs.quasi) hs.S_le_A (coprime_relIndex S₀) hKS hcardK
    h.e_mem heK he_order
  have hw2 : (a⁻¹ * h.e * a) ^ 2 = 1 := by
    rw [show a⁻¹ * h.e * a = a⁻¹ * h.e * a⁻¹⁻¹ by rw [inv_inv], conj_pow, h.e_sq]
    group
  have hwz : a⁻¹ * h.e * a = x ^ 2 := by
    rcases (Lemma37.mem_sup_zpowers_iff hgN hg2).1 haK with h1 | h1
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
      rw [← hi] at hw2 ⊢
      rcases h.rho_zpow_sq hw2 with h2 | h2
      · exfalso
        apply h.e_not_mem
        have : h.e = a * ρ ^ i * a⁻¹ := by rw [hi]; group
        rw [this, h2, mul_one, mul_inv_cancel]
        exact one_mem _
      · exact h2
    · obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
      exfalso
      apply hgi i
      rw [hi]
      calc (g * (g⁻¹ * (a⁻¹ * h.e * a))) ^ 2 = (a⁻¹ * h.e * a) ^ 2 := by group
        _ = 1 := hw2
  apply h.e_not_mem
  have : h.e = a * x ^ 2 * a⁻¹ := by rw [← hwz]; group
  rw [this, (mem_centralizer_iff.1 hz a haA), mul_inv_cancel_right]
  exact h.x_sq_mem

theorem mem_zpowers_of_sq_eq_one {X : Type*} [Group X] {a g : X} (ha : a ^ 2 = 1)
    (hg : g ∈ zpowers a) : g = 1 ∨ g = a := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hg
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
  · left
    rw [zpow_mul, zpow_two, ← pow_two, ha, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, ← pow_two, ha, one_zpow, one_mul, zpow_one]

theorem four_group {X : Type*} [Group X] [Finite X] {a b : X} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hba : b ≠ a) (hab : a * b = b * a) :
    Assembly.IsElemAbelian 2 (zpowers a ⊔ zpowers b) ∧
      Nat.card (zpowers a ⊔ zpowers b : Subgroup X) = 4 ∧
      ∀ g ∈ zpowers a ⊔ zpowers b, g = 1 ∨ g = a ∨ g = b ∨ g = b * a := by
  have hbN : b ∈ normalizer (zpowers a : Set X) := by
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun w hw => ?_)
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_left hab n).eq
  have hb2 : b ^ 2 ∈ zpowers a := by rw [hb]; exact one_mem _
  have hbnot : b ∉ zpowers a := fun h' => by
    rcases mem_zpowers_of_sq_eq_one ha h' with h1 | h1
    · exact hb1 h1
    · exact hba h1
  have helem : ∀ g ∈ zpowers a ⊔ zpowers b, g = 1 ∨ g = a ∨ g = b ∨ g = b * a := by
    intro g hg
    rcases (Lemma37.mem_sup_zpowers_iff hbN hb2).1 hg with h1 | h1
    · rcases mem_zpowers_of_sq_eq_one ha h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · rcases mem_zpowers_of_sq_eq_one ha h1 with h2 | h2
      · right; right; left
        calc g = b * (b⁻¹ * g) := by group
          _ = b := by rw [h2, mul_one]
      · right; right; right
        calc g = b * (b⁻¹ * g) := by group
          _ = b * a := by rw [h2]
  have hord : orderOf a = 2 := orderOf_eq_prime ha ha1
  refine ⟨⟨?_, fun g hg => ?_⟩, ?_, helem⟩
  · rw [← le_centralizer_iff_isMulCommutative]
    have hca : a ∈ centralizer ((zpowers a ⊔ zpowers b : Subgroup X) : Set X) := by
      rw [mem_centralizer_iff]
      intro g hg
      rcases helem g hg with rfl | rfl | rfl | rfl
      · group
      · rfl
      · exact hab.symm
      · calc b * a * a = (a * b) * a := by rw [hab]
          _ = a * (b * a) := by group
    have hcb : b ∈ centralizer ((zpowers a ⊔ zpowers b : Subgroup X) : Set X) := by
      rw [mem_centralizer_iff]
      intro g hg
      rcases helem g hg with rfl | rfl | rfl | rfl
      · group
      · exact hab
      · rfl
      · rw [mul_assoc, hab]
    exact sup_le (zpowers_le.2 hca) (zpowers_le.2 hcb)
  · rcases helem g hg with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · exact ha
    · exact hb
    · calc (b * a) ^ 2 = b * (a * b) * a := by rw [pow_two]; group
        _ = b ^ 2 * a ^ 2 := by rw [hab, pow_two, pow_two]; group
        _ = 1 := by rw [ha, hb, one_mul]
  · rw [Lemma37.card_sup_zpowers hbN hb2 hbnot, Nat.card_zpowers, hord]

theorem central_trivial_or [Finite G] (hs : Setting A S₀ t x ρ k) :
    x ^ 2 ∈ centralizer (A : Set G) ∨
      ∀ w ∈ (S₀ : Subgroup A).map A.subtype, w ∈ centralizer (A : Set G) → w = 1 := by
  by_cases hz : x ^ 2 ∈ centralizer (A : Set G)
  · exact Or.inl hz
  · refine Or.inr fun w hwS hwc => ?_
    by_contra hw1
    exact hz (hs.config.x_sq_mem_of_ne_one (S₀.isPGroup'.map _) hs.t_norm hwS hwc hw1)

theorem x_sq_sq (hs : Setting A S₀ t x ρ k) : (x ^ 2) ^ 2 = 1 := by
  rw [← pow_mul]
  exact hs.config.x_pow_four

theorem card_sylowBar_of_central [Finite G] (hs : Setting A S₀ t x ρ k)
    (hz : x ^ 2 ∈ centralizer (A : Set G)) :
    Nat.card (sylowBar S₀ : Subgroup (A ⧸ center A)) = 2 ^ (k + 1) := by
  have h := hs.config
  have hWeq : (S₀ : Subgroup A).map A.subtype ⊓ centralizer (A : Set G) = zpowers (x ^ 2) :=
    le_antisymm (Config.central_le_zpowers_x_sq hs.quasi S₀ h)
      (zpowers_le.2 (mem_inf.2 ⟨pow_mem h.x_mem 2, hz⟩))
  have hcardT := card_sylowBar S₀
  rw [hWeq, Nat.card_zpowers, orderOf_eq_prime hs.x_sq_sq h.x_sq_ne_one, h.card, pow_succ]
    at hcardT
  omega

theorem card_sylowBar_of_trivial [Finite G] (hs : Setting A S₀ t x ρ k)
    (htriv : ∀ w ∈ (S₀ : Subgroup A).map A.subtype, w ∈ centralizer (A : Set G) → w = 1) :
    Nat.card (sylowBar S₀ : Subgroup (A ⧸ center A)) = 2 ^ (k + 2) := by
  have hWeq : (S₀ : Subgroup A).map A.subtype ⊓ centralizer (A : Set G) = ⊥ :=
    eq_bot_iff.2 fun w hw => (mem_bot).2 (htriv w (mem_inf.1 hw).1 (mem_inf.1 hw).2)
  have hcardT := card_sylowBar S₀
  rw [hWeq, card_bot, mul_one, hs.config.card] at hcardT
  exact hcardT

theorem false_of_caseI_central [Finite G] (hs : Setting A S₀ t x ρ k)
    (hI : ∀ g ∈ (S₀ : Subgroup A).map A.subtype, g ∉ zpowers ρ ⊔ zpowers x → g ^ 2 ≠ 1)
    (hz : x ^ 2 ∈ centralizer (A : Set G)) : False := by
  have h := hs.config
  have : IsSimpleGroup (A ⧸ center A) := hs.quasi.2
  have hSA := hs.S_le_A
  by_cases hy : ∃ g ∈ (S₀ : Subgroup A).map A.subtype, g ∉ zpowers ρ ⊔ zpowers x ∧
      g ^ 2 = x ^ 2
  · obtain ⟨g, hgS, hgM, hg2⟩ := hy
    refine hs.x_sq_not_central_of_outside hgS hgM (hg2 ▸ h.x_sq_mem) (fun i hi => ?_) hz
    refine hI _ (mul_mem hgS (zpow_mem h.rho_mem i)) (fun hm => hgM ?_) hi
    have : g = (g * ρ ^ i) * ρ ^ (-i) := by group
    rw [this]
    exact mul_mem hm (mem_sup_left (zpow_mem (mem_zpowers ρ) _))
  push Not at hy
  have hW := Config.central_le_zpowers_x_sq hs.quasi S₀ h
  have hmemW : ∀ g ∈ (S₀ : Subgroup A).map A.subtype, bar A g = 1 → g = 1 ∨ g = x ^ 2 :=
    fun g hg hg1 => mem_zpowers_of_sq_eq_one hs.x_sq_sq
      (hW (mem_inf.2 ⟨hg, (bar_eq_one_iff (hSA hg)).1 hg1⟩))
  have hyS : h.y ∈ (S₀ : Subgroup A).map A.subtype := zpowers_le.2 h.rho_mem h.y_mem
  have heS := h.e_mem
  have hx2S : x ^ 2 ∈ (S₀ : Subgroup A).map A.subtype := pow_mem h.x_mem 2
  have hy2 : bar A h.y ^ 2 = 1 := by
    rw [← bar_pow (hSA hyS), h.y_sq, (bar_eq_one_iff (hSA hx2S)).2 hz]
  have he2 : bar A h.e ^ 2 = 1 := by rw [← bar_pow (hSA heS), h.e_sq, bar_one]
  have hy1 : bar A h.y ≠ 1 := fun h1 => by
    apply h.x_sq_ne_one
    rcases hmemW _ hyS h1 with h2 | h2
    · rw [← h.y_sq, h2, one_pow]
    · rw [← h.y_sq, h2, hs.x_sq_sq]
  have he1 : bar A h.e ≠ 1 := fun h1 => by
    rcases hmemW _ heS h1 with h2 | h2
    · exact h.e_not_mem (h2 ▸ one_mem _)
    · exact h.e_not_mem (h2 ▸ h.x_sq_mem)
  have hey : bar A h.e ≠ bar A h.y := fun h1 => by
    have h1' : bar A (h.y⁻¹ * h.e) = 1 := by
      rw [bar_mul (inv_mem (hSA hyS)) (hSA heS), bar_inv (hSA hyS), h1, inv_mul_cancel]
    apply h.e_not_mem
    have he : h.e = h.y * (h.y⁻¹ * h.e) := by group
    rcases hmemW _ (mul_mem (inv_mem hyS) heS) h1' with h2 | h2 <;> rw [he, h2]
    · rw [mul_one]
      exact h.y_mem
    · exact mul_mem h.y_mem h.x_sq_mem
  have hyecomm : bar A h.y * bar A h.e = bar A h.e * bar A h.y := by
    rw [← bar_mul (hSA hyS) (hSA heS), ← bar_mul (hSA heS) (hSA hyS),
      h.M_comm (mem_sup_left h.y_mem) h.e_mem_M]
  obtain ⟨hV, hV4, -⟩ := four_group hy2 he2 hy1 he1 hey hyecomm
  have hT := hs.card_sylowBar_of_central hz
  refine false_of_few_involutions (nonabelian_bar hs.quasi) (sylowBar S₀) hV hV4 ?_ ?_ ?_
  · intro q hq hq2
    obtain ⟨g, hgS, rfl⟩ := (mem_sylowBar_iff S₀).1 hq
    have hg2W := hmemW _ (pow_mem hgS 2) (by rw [bar_pow (hSA hgS), hq2])
    have hgM : g ∈ zpowers ρ ⊔ zpowers x := by
      by_contra hgM
      rcases hg2W with h2 | h2
      · exact hI g hgS hgM h2
      · exact hy g hgS hgM h2
    have hg4 : g ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
      rcases hg2W with h2 | h2 <;> rw [h2]
      · exact one_pow 2
      · exact hs.x_sq_sq
    obtain ⟨j, hj | hj⟩ := h.M_four hgM hg4 <;> rw [hj]
    · rw [bar_zpow (hSA hyS)]
      exact mem_sup_left (zpow_mem (mem_zpowers _) j)
    · rw [bar_mul (hSA (zpow_mem hyS j)) (hSA heS), bar_zpow (hSA hyS)]
      exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers _) j)) (mem_sup_right (mem_zpowers _))
  · rw [hT]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by have := h.hk; omega)
  · intro h64
    refine ⟨bar A ρ, bar_mem_sylowBar S₀ h.rho_mem, fun h4 => ?_⟩
    rw [hT, show (64 : ℕ) = 2 ^ 6 by norm_num] at h64
    have hk5 : k = 5 := by have := Nat.pow_right_injective (le_refl 2) h64; omega
    rw [← bar_pow (hSA h.rho_mem)] at h4
    have hρ8 : ρ ^ 8 = 1 := by
      rcases hmemW _ (pow_mem h.rho_mem 4) h4 with h5 | h5
      · rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, h5, one_pow]
      · rw [show (8 : ℕ) = 4 * 2 by rfl, pow_mul, h5, hs.x_sq_sq]
    have := orderOf_dvd_of_pow_eq_one hρ8
    rw [h.rho_order, hk5] at this
    norm_num at this

theorem false_of_caseI_trivial [Finite G] (hs : Setting A S₀ t x ρ k)
    (hI : ∀ g ∈ (S₀ : Subgroup A).map A.subtype, g ∉ zpowers ρ ⊔ zpowers x → g ^ 2 ≠ 1)
    (htriv : ∀ w ∈ (S₀ : Subgroup A).map A.subtype, w ∈ centralizer (A : Set G) → w = 1) :
    False := by
  have h := hs.config
  have : IsSimpleGroup (A ⧸ center A) := hs.quasi.2
  have hSA := hs.S_le_A
  have hinj : ∀ {g g' : G}, g ∈ (S₀ : Subgroup A).map A.subtype →
      g' ∈ (S₀ : Subgroup A).map A.subtype → bar A g = bar A g' → g = g' :=
    fun hg hg' hgg' => bar_injective_of_trivial S₀ htriv hg hg' hgg'
  have hx2S : x ^ 2 ∈ (S₀ : Subgroup A).map A.subtype := pow_mem h.x_mem 2
  have heS := h.e_mem
  have hz2 : bar A (x ^ 2) ^ 2 = 1 := by rw [← bar_pow (hSA hx2S), hs.x_sq_sq, bar_one]
  have he2 : bar A h.e ^ 2 = 1 := by rw [← bar_pow (hSA heS), h.e_sq, bar_one]
  have hz1 : bar A (x ^ 2) ≠ 1 := fun h1 =>
    h.x_sq_ne_one (hinj hx2S (one_mem _) (h1.trans bar_one.symm))
  have he1 : bar A h.e ≠ 1 := fun h1 =>
    h.e_not_mem (hinj heS (one_mem _) (h1.trans bar_one.symm) ▸ one_mem _)
  have hez : bar A h.e ≠ bar A (x ^ 2) := fun h1 =>
    h.e_not_mem (hinj heS hx2S h1 ▸ h.x_sq_mem)
  have hzecomm : bar A (x ^ 2) * bar A h.e = bar A h.e * bar A (x ^ 2) := by
    rw [← bar_mul (hSA hx2S) (hSA heS), ← bar_mul (hSA heS) (hSA hx2S),
      h.M_comm (mem_sup_left h.x_sq_mem) h.e_mem_M]
  obtain ⟨hV, hV4, -⟩ := four_group hz2 he2 hz1 he1 hez hzecomm
  have hT := hs.card_sylowBar_of_trivial htriv
  refine false_of_few_involutions (nonabelian_bar hs.quasi) (sylowBar S₀) hV hV4 ?_ ?_ ?_
  · intro q hq hq2
    obtain ⟨g, hgS, rfl⟩ := (mem_sylowBar_iff S₀).1 hq
    have hg2 : g ^ 2 = 1 := hinj (pow_mem hgS 2) (one_mem _) (by rw [bar_pow (hSA hgS), hq2,
      bar_one])
    have hgM : g ∈ zpowers ρ ⊔ zpowers x := by
      by_contra hgM
      exact hI g hgS hgM hg2
    rcases h.M_involution hgM hg2 with rfl | rfl | rfl | rfl
    · rw [bar_one]
      exact one_mem _
    · exact mem_sup_left (mem_zpowers _)
    · exact mem_sup_right (mem_zpowers _)
    · rw [bar_mul (hSA hx2S) (hSA heS)]
      exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
  · rw [hT]
    calc 8 ≤ 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by have := h.hk; omega)
  · intro h64
    refine ⟨bar A ρ, bar_mem_sylowBar S₀ h.rho_mem, fun h4 => ?_⟩
    rw [hT, show (64 : ℕ) = 2 ^ 6 by norm_num] at h64
    have hk4 : k = 4 := by have := Nat.pow_right_injective (le_refl 2) h64; omega
    rw [← bar_pow (hSA h.rho_mem)] at h4
    have hρ4 : ρ ^ 4 = 1 := hinj (pow_mem h.rho_mem 4) (one_mem _) (h4.trans bar_one.symm)
    have := orderOf_dvd_of_pow_eq_one hρ4
    rw [h.rho_order, hk4] at this
    norm_num at this

theorem false_of_caseI [Finite G] (hs : Setting A S₀ t x ρ k)
    (hI : ∀ g ∈ (S₀ : Subgroup A).map A.subtype, g ∉ zpowers ρ ⊔ zpowers x → g ^ 2 ≠ 1) :
    False := by
  rcases hs.central_trivial_or with hz | htriv
  · exact hs.false_of_caseI_central hI hz
  · exact hs.false_of_caseI_trivial hI htriv

end Setting

end CFSG.ComponentClassification.AschbacherKnownGroup.ShapeExclusion

module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Elementary
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Basic

variable {G : Type} [Group G]

theorem isElemAbelian_two_iff {F : Subgroup G} :
    CFSG.Assembly.IsElemAbelian 2 F ↔
      (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1 := by
  constructor
  · rintro ⟨hc, hs⟩
    refine ⟨fun x hx y hy => ?_, fun x hx => by simpa [sq] using hs x hx⟩
    have := hc.is_comm.comm (⟨x, hx⟩ : F) ⟨y, hy⟩
    exact congrArg Subtype.val this
  · rintro ⟨hc, hs⟩
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => by simpa [sq] using hs x hx⟩
    exact Subtype.ext (hc a.1 a.2 b.1 b.2)

theorem exists_pair_of_two_lt [Finite G] {F : Subgroup G}
    (hF : CFSG.Assembly.IsElemAbelian 2 F) (h : 2 < Nat.card F) :
    ∃ a b : G, a ∈ F ∧ b ∈ F ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a := by
  obtain ⟨hcomm, hsq⟩ := isElemAbelian_two_iff.1 hF
  have hne : F ≠ ⊥ := by
    intro hb
    rw [hb] at h
    simp at h
  obtain ⟨⟨a, haF⟩, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have ha1 : a ≠ 1 := fun h => ha (Subtype.ext h)
  have haa := hsq a haF
  have hex : ∃ b ∈ F, b ∉ Subgroup.zpowers a := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ Subgroup.zpowers a := fun x hx => hcon x hx
    have h1 : Nat.card F ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      have : a ^ 2 = 1 := by rw [sq]; exact haa
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one this)
    omega
  obtain ⟨b, hbF, hbz⟩ := hex
  have hb1 : b ≠ 1 := fun h => hbz (h ▸ Subgroup.one_mem _)
  have hba : b ≠ a := fun h => hbz (h ▸ Subgroup.mem_zpowers a)
  exact ⟨a, b, haF, hbF, ha1, hb1, hba.symm, haa, hsq b hbF, hcomm a haF b hbF⟩

theorem exists_pair_of_four [Finite G] {E : Subgroup G} (hE : IsFourSubgroup E) :
    ∃ a b : G, a ∈ E ∧ b ∈ E ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a ∧ E = Subgroup.closure ({a, b} : Set G) := by
  obtain ⟨a, b, haE, hbE, ha1, hb1, hab, haa, hbb, hcomm⟩ :=
    exists_pair_of_two_lt hE.1 (by rw [hE.2]; norm_num)
  refine ⟨a, b, haE, hbE, ha1, hb1, hab, haa, hbb, hcomm, ?_⟩
  have hle : Subgroup.closure ({a, b} : Set G) ≤ E := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact haE
    · rw [Set.mem_singleton_iff.mp hx]
      exact hbE
  have hcard := card_closure_pair haa hbb hcomm ha1 hb1 hab
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hE.2])).symm

theorem exists_triple [Finite G] {F : Subgroup G} (hF : CFSG.Assembly.IsElemAbelian 2 F)
    (h : 4 < Nat.card F) :
    ∃ a b c : G, a ∈ F ∧ b ∈ F ∧ c ∈ F ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ c ≠ 1 ∧ c ≠ a ∧ c ≠ b ∧
      c ≠ a * b ∧ a * a = 1 ∧ b * b = 1 ∧ c * c = 1 ∧ a * b = b * a ∧ a * c = c * a ∧
      b * c = c * b := by
  obtain ⟨hcomm, hsq⟩ := isElemAbelian_two_iff.1 hF
  obtain ⟨a, b, haF, hbF, ha1, hb1, hab, haa, hbb, habc⟩ :=
    exists_pair_of_two_lt hF (by omega)
  have hcard := card_closure_pair haa hbb habc ha1 hb1 hab
  have hex : ∃ c ∈ F, c ∉ Subgroup.closure ({a, b} : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : F ≤ Subgroup.closure ({a, b} : Set G) := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨c, hcF, hcn⟩ := hex
  have hmem : ∀ x : G, x = 1 ∨ x = a ∨ x = b ∨ x = a * b →
      x ∈ Subgroup.closure ({a, b} : Set G) := by
    rintro x (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  exact ⟨a, b, c, haF, hbF, hcF, ha1, hb1, hab, fun h => hcn (hmem c (Or.inl h)),
    fun h => hcn (hmem c (Or.inr (Or.inl h))), fun h => hcn (hmem c (Or.inr (Or.inr (Or.inl h)))),
    fun h => hcn (hmem c (Or.inr (Or.inr (Or.inr h)))), haa, hbb, hsq c hcF, habc,
    hcomm a haF c hcF, hcomm b hbF c hcF⟩

theorem isFourSubgroup_of_pair {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    IsFourSubgroup (Subgroup.closure ({a, b} : Set G)) := by
  refine ⟨⟨?_, fun x hx => ?_⟩, card_closure_pair ha hb hab ha1 hb1 hne⟩
  · exact Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact Commute.refl _
      · rw [Set.mem_singleton_iff.mp hy]
        exact hab
      · rw [Set.mem_singleton_iff.mp hx]
        exact hab.symm
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
  · have hab' : b * a = a * b := hab.symm
    rcases mem_closure_pair_of_involutions ha hb hab hx with h | h | h | h <;> rw [h]
    · simp
    · rw [sq]
      exact ha
    · rw [sq]
      exact hb
    · rw [sq]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab']
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]

theorem mem_conjugate_iff (H : Subgroup G) (g x : G) :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  have hc : ∀ y, (MulAut.conj g⁻¹).toMonoidHom y = g⁻¹ * y * g := fun y => by
    simp
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [hc]
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rw [e]
    exact hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    rw [hc]
    group

end Basic

section Index2

variable {G : Type} [Group G] [Finite G]

structure Idx2 (K A : Subgroup G) : Prop where
  le : K ≤ A
  card : Nat.card A = 2 * Nat.card K

variable {K A : Subgroup G}

theorem Idx2.index (h : Idx2 K A) : (K.subgroupOf A).index = 2 := by
  have h1 := Subgroup.card_mul_index (K.subgroupOf A)
  have h2 : Nat.card (K.subgroupOf A) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  rw [h2, h.card] at h1
  have hpos : 0 < Nat.card K := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])

theorem Idx2.mul_mem_iff (h : Idx2 K A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y ∈ K ↔ (x ∈ K ↔ y ∈ K) :=
  Subgroup.mul_mem_iff_of_index_two h.index (a := (⟨x, hx⟩ : ↥A)) (b := ⟨y, hy⟩)

theorem Idx2.conj_mem (h : Idx2 K A) {a k : G} (ha : a ∈ A) (hk : k ∈ K) : a * k * a⁻¹ ∈ K := by
  have hn : (K.subgroupOf A).Normal := Subgroup.normal_of_index_eq_two h.index
  exact hn.conj_mem ⟨k, h.le hk⟩ hk ⟨a, ha⟩

theorem Idx2.le_normalizer (h : Idx2 K A) : A ≤ Subgroup.normalizer (K : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h.conj_mem ha hx, fun hx => ?_⟩
  have h1 := h.conj_mem (A.inv_mem ha) hx
  have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
  rwa [e] at h1

end Index2

section E8

variable {G : Type} [Group G] [Finite G] {K A E : Subgroup G}

omit [Finite G] in
theorem mem_centIn {x : G} :
    x ∈ A ⊓ Subgroup.centralizer (E : Set G) ↔ x ∈ A ∧ ∀ y ∈ E, x * y = y * x := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => (h y hy).symm⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun y hy => (h y hy).symm⟩

structure CentData (K A E : Subgroup G) (f : G) : Prop where
  idx2 : Idx2 K A
  hEK : E ≤ K
  hE : IsFourSubgroup E
  hCE : ∀ x ∈ K, (∀ y ∈ E, x * y = y * x) → x ∈ E
  hfA : f ∈ A
  hfK : f ∉ K
  hff : f * f = 1
  hfE : ∀ y ∈ E, f * y = y * f

variable {f : G}

omit [Finite G] in
theorem CentData.E_le (h : CentData K A E f) : E ≤ A ⊓ Subgroup.centralizer (E : Set G) := by
  intro x hx
  rw [mem_centIn]
  exact ⟨h.idx2.le (h.hEK hx), fun y hy => (isElemAbelian_two_iff.1 h.hE.1).1 x hx y hy⟩

theorem CentData.decomp (h : CentData K A E f) {x : G}
    (hx : x ∈ A ⊓ Subgroup.centralizer (E : Set G)) : x ∈ E ∨ ∃ e ∈ E, x = f * e := by
  rw [mem_centIn] at hx
  by_cases hxK : x ∈ K
  · exact Or.inl (h.hCE x hxK hx.2)
  · right
    have hfinvA : f⁻¹ ∈ A := A.inv_mem h.hfA
    have hfinvK : f⁻¹ ∉ K := fun hh => h.hfK (by simpa using K.inv_mem hh)
    have hmem : f⁻¹ * x ∈ K :=
      (h.idx2.mul_mem_iff hfinvA hx.1).2 (iff_of_false hfinvK hxK)
    have hcomm : ∀ y ∈ E, (f⁻¹ * x) * y = y * (f⁻¹ * x) := by
      intro y hy
      have h1 : f * y = y * f := h.hfE y hy
      have h2 : f⁻¹ * y = y * f⁻¹ := by
        calc f⁻¹ * y = f⁻¹ * (y * f) * f⁻¹ := by group
          _ = f⁻¹ * (f * y) * f⁻¹ := by rw [h1]
          _ = y * f⁻¹ := by group
      calc f⁻¹ * x * y = f⁻¹ * (x * y) := by group
        _ = f⁻¹ * (y * x) := by rw [hx.2 y hy]
        _ = (f⁻¹ * y) * x := by group
        _ = (y * f⁻¹) * x := by rw [h2]
        _ = y * (f⁻¹ * x) := by group
    exact ⟨f⁻¹ * x, h.hCE _ hmem hcomm, by group⟩

omit [Finite G] in
theorem CentData.inf_K (h : CentData K A E f) :
    (A ⊓ Subgroup.centralizer (E : Set G)) ⊓ K = E := by
  ext x
  constructor
  · rintro ⟨hxF, hxK⟩
    exact h.hCE x hxK (mem_centIn.1 hxF).2
  · intro hx
    exact ⟨h.E_le hx, h.hEK hx⟩

theorem CentData.card (h : CentData K A E f) :
    Nat.card (A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) = 8 := by
  set F := A ⊓ Subgroup.centralizer (E : Set G) with hF
  have hEF : E ≤ F := h.E_le
  have hfF : f ∈ F := mem_centIn.2 ⟨h.hfA, fun y hy => h.hfE y hy⟩
  have hEK' : ∀ x ∈ F, x ∈ K → x ∈ E := fun x hx hxK => by
    have : x ∈ F ⊓ K := ⟨hx, hxK⟩
    rwa [hF, h.inf_K] at this
  have hbf : ∀ b ∈ F, b ∉ E → b * f ∈ E := by
    intro b hb hbE
    have hbK : b ∉ K := fun hh => hbE (hEK' b hb hh)
    have hbA : b ∈ A := (mem_centIn.1 hb).1
    have hbfK : b * f ∈ K := (h.idx2.mul_mem_iff hbA h.hfA).2 (iff_of_false hbK h.hfK)
    exact hEK' _ (F.mul_mem hb hfF) hbfK
  have hidx : (E.subgroupOf F).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨f, hfF⟩, fun b => ?_⟩
    by_cases hb : (b : G) ∈ E
    · right
      refine ⟨hb, fun hbf => ?_⟩
      have hbf' : (b : G) * f ∈ E := hbf
      have : f ∈ E := by
        have h1 := E.mul_mem (E.inv_mem hb) hbf'
        simpa using h1
      exact h.hfK (h.hEK this)
    · left
      exact ⟨hbf b b.2 hb, hb⟩
  have hcardE : Nat.card (E.subgroupOf F) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv]
    exact h.hE.2
  have := Subgroup.card_mul_index (E.subgroupOf F)
  rw [hcardE, hidx] at this
  omega

theorem CentData.elemAbelian (h : CentData K A E f) :
    CFSG.Assembly.IsElemAbelian 2 (A ⊓ Subgroup.centralizer (E : Set G)) := by
  obtain ⟨hcomm, hsq⟩ := isElemAbelian_two_iff.1 h.hE.1
  have hc : ∀ x ∈ E, ∀ y ∈ E, Commute x y := fun x hx y hy => hcomm x hx y hy
  have hfc : ∀ e ∈ E, Commute f e := fun e he => h.hfE e he
  refine isElemAbelian_two_iff.2 ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · rcases h.decomp hx with hxE | ⟨e, he, rfl⟩ <;> rcases h.decomp hy with hyE | ⟨e', he', rfl⟩
    · exact hc x hxE y hyE
    · exact Commute.mul_right (hfc x hxE).symm (hc x hxE e' he')
    · exact Commute.mul_left (hfc y hyE) (hc e he y hyE)
    · exact Commute.mul_left (Commute.mul_right (Commute.refl f) (hfc e' he'))
        (Commute.mul_right (hfc e he).symm (hc e he e' he'))
  · rcases h.decomp hx with hxE | ⟨e, he, rfl⟩
    · exact hsq x hxE
    · rw [(hfc e he).symm.mul_mul_mul_comm f e, h.hff, hsq e he, one_mul]

omit [Finite G] in
theorem inf_normalizer_le :
    A ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) := by
  intro n hn
  obtain ⟨hnA, hnE⟩ := Subgroup.mem_inf.1 hn
  rw [Subgroup.mem_normalizer_iff] at hnE
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_centIn, mem_centIn]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨A.mul_mem (A.mul_mem hnA hx) (A.inv_mem hnA), fun y hy => ?_⟩
    have hy' : n⁻¹ * y * n ∈ E := by
      refine (hnE (n⁻¹ * y * n)).2 ?_
      have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      rw [e]
      exact hy
    have h1 := hc _ hy'
    calc n * x * n⁻¹ * y = n * (x * (n⁻¹ * y * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * y * n) * x) * n⁻¹ := by rw [h1]
      _ = y * (n * x * n⁻¹) := by group
  · rintro ⟨hx, hc⟩
    have hxA : x ∈ A := by
      have e : n⁻¹ * (n * x * n⁻¹) * n = x := by group
      rw [← e]
      exact A.mul_mem (A.mul_mem (A.inv_mem hnA) hx) hnA
    refine ⟨hxA, fun y hy => ?_⟩
    have hy' : n * y * n⁻¹ ∈ E := (hnE y).1 hy
    have h1 := hc _ hy'
    have h2 : n * (x * y) * n⁻¹ = n * (y * x) * n⁻¹ := by
      calc n * (x * y) * n⁻¹ = n * x * n⁻¹ * (n * y * n⁻¹) := by group
        _ = n * y * n⁻¹ * (n * x * n⁻¹) := h1
        _ = n * (y * x) * n⁻¹ := by group
    simpa using h2

omit [Finite G] in
theorem conjugate_centIn {a : G} (ha : a ∈ A) :
    CFSG.conjugate (A ⊓ Subgroup.centralizer (E : Set G)) a =
      A ⊓ Subgroup.centralizer ((CFSG.conjugate E a : Subgroup G) : Set G) := by
  ext x
  rw [mem_conjugate_iff, mem_centIn, mem_centIn]
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨?_, fun y hy => ?_⟩
    · have e : a⁻¹ * (a * x * a⁻¹) * a = x := by group
      rw [← e]
      exact A.mul_mem (A.mul_mem (A.inv_mem ha) hx) ha
    · have hy' : a * y * a⁻¹ ∈ E := (mem_conjugate_iff E a y).1 hy
      have h1 := hc _ hy'
      have e1 : a * x * a⁻¹ * (a * y * a⁻¹) = a * (x * y) * a⁻¹ := by group
      have e2 : a * y * a⁻¹ * (a * x * a⁻¹) = a * (y * x) * a⁻¹ := by group
      rw [e1, e2] at h1
      simpa using h1
  · rintro ⟨hx, hc⟩
    refine ⟨A.mul_mem (A.mul_mem ha hx) (A.inv_mem ha), fun y hy => ?_⟩
    have hy' : a⁻¹ * y * a ∈ (CFSG.conjugate E a : Subgroup G) := by
      rw [mem_conjugate_iff]
      have e : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
      rw [e]
      exact hy
    have h1 := hc _ hy'
    calc a * x * a⁻¹ * y = a * (x * (a⁻¹ * y * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * y * a) * x) * a⁻¹ := by rw [h1]
      _ = y * (a * x * a⁻¹) := by group

theorem four_of_e8 (h : Idx2 K A)
    (hno : ∀ F : Subgroup G, F ≤ K → CFSG.Assembly.IsElemAbelian 2 F → Nat.card F ≤ 4)
    {F : Subgroup G} (hFA : F ≤ A) (hF : CFSG.Assembly.IsElemAbelian 2 F) (hF8 : Nat.card F = 8) :
    IsFourSubgroup (F ⊓ K) ∧ F ≤ A ⊓ Subgroup.centralizer ((F ⊓ K : Subgroup G) : Set G) := by
  obtain ⟨hcomm, hsq⟩ := isElemAbelian_two_iff.1 hF
  have hFK : ¬ F ≤ K := fun hle => by
    have := hno F hle hF
    omega
  obtain ⟨x, hxF, hxK⟩ : ∃ x ∈ F, x ∉ K := by
    by_contra hcon
    push Not at hcon
    exact hFK fun y hy => hcon y hy
  classical
  have hE : CFSG.Assembly.IsElemAbelian 2 (F ⊓ K) :=
    isElemAbelian_two_iff.2 ⟨fun a ha b hb => hcomm a ha.1 b hb.1, fun a ha => hsq a ha.1⟩
  have hle4 : Nat.card (F ⊓ K : Subgroup G) ≤ 4 := hno _ inf_le_right hE
  have hge4 : 4 ≤ Nat.card (F ⊓ K : Subgroup G) := by
    have hinj : Function.Injective (fun y : F =>
        (if hy : (y : G) ∈ K then (⟨⟨y, y.2, hy⟩, false⟩ : (F ⊓ K : Subgroup G) × Bool)
          else (⟨⟨x⁻¹ * y, F.mul_mem (F.inv_mem hxF) y.2, by
            have hxA : x⁻¹ ∈ A := A.inv_mem (hFA hxF)
            have hxK' : x⁻¹ ∉ K := fun hh => hxK (by simpa using K.inv_mem hh)
            exact (h.mul_mem_iff hxA (hFA y.2)).2 (iff_of_false hxK' hy)⟩, true⟩ :
              (F ⊓ K : Subgroup G) × Bool))) := by
      intro y y' hyy
      dsimp only at hyy
      by_cases hy : (y : G) ∈ K <;> by_cases hy' : (y' : G) ∈ K
      · rw [dite_eq_left hy, dite_eq_left hy'] at hyy
        have h1 := congrArg Subtype.val (Prod.mk.inj hyy).1
        exact Subtype.ext h1
      · rw [dite_eq_left hy, dite_eq_right hy'] at hyy
        exact absurd (Prod.mk.inj hyy).2 (by simp)
      · rw [dite_eq_right hy, dite_eq_left hy'] at hyy
        exact absurd (Prod.mk.inj hyy).2 (by simp)
      · rw [dite_eq_right hy, dite_eq_right hy'] at hyy
        have h1 := congrArg Subtype.val (Prod.mk.inj hyy).1
        exact Subtype.ext (mul_left_cancel h1)
    have := Nat.card_le_card_of_injective _ hinj
    have hb : Nat.card Bool = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    rw [Nat.card_prod, hF8, hb] at this
    omega
  have hcard : Nat.card (F ⊓ K : Subgroup G) = 4 := le_antisymm hle4 hge4
  refine ⟨⟨hE, hcard⟩, fun y hy => ?_⟩
  rw [mem_centIn]
  exact ⟨hFA hy, fun z hz => hcomm y hy z hz.1⟩

structure E8Input (K A : Subgroup G) : Prop where
  idx2 : Idx2 K A
  noE8 : ∀ F : Subgroup G, F ≤ K → CFSG.Assembly.IsElemAbelian 2 F → Nat.card F ≤ 4
  klein : ∀ E : Subgroup G, E ≤ K → IsFourSubgroup E →
    (∀ x ∈ K, (∀ y ∈ E, x * y = y * x) → x ∈ E) ∧
      ∃ f : G, f ∈ A ∧ f ∉ K ∧ f * f = 1 ∧ ∀ y ∈ E, f * y = y * f
  trans : ∀ E E' : Subgroup G, E ≤ K → IsFourSubgroup E → E' ≤ K → IsFourSubgroup E' →
    ∃ k ∈ K, E' = CFSG.conjugate E k

omit [Finite G] in
theorem E8Input.centData (h : E8Input K A) {E : Subgroup G} (hEK : E ≤ K) (hE : IsFourSubgroup E) :
    ∃ f : G, CentData K A E f := by
  obtain ⟨hCE, f, hfA, hfK, hff, hfE⟩ := h.klein E hEK hE
  exact ⟨f, h.idx2, hEK, hE, hCE, hfA, hfK, hff, hfE⟩

theorem E8Input.e8_exists (h : E8Input K A) {E : Subgroup G} (hEK : E ≤ K) (hE : IsFourSubgroup E) :
    ∃ F : Subgroup G, F ≤ A ∧ CFSG.Assembly.IsElemAbelian 2 F ∧ Nat.card F = 8 ∧ E ≤ F ∧
      F ⊓ K = E ∧ A ⊓ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (F : Set G) := by
  obtain ⟨f, hf⟩ := h.centData hEK hE
  exact ⟨A ⊓ Subgroup.centralizer (E : Set G), inf_le_left, hf.elemAbelian, hf.card, hf.E_le,
    hf.inf_K, inf_normalizer_le⟩

theorem E8Input.eq_centIn (h : E8Input K A) {F : Subgroup G} (hFA : F ≤ A)
    (hF : CFSG.Assembly.IsElemAbelian 2 F) (hF8 : Nat.card F = 8) :
    IsFourSubgroup (F ⊓ K) ∧ F = A ⊓ Subgroup.centralizer ((F ⊓ K : Subgroup G) : Set G) := by
  obtain ⟨hE4, hFle⟩ := four_of_e8 h.idx2 h.noE8 hFA hF hF8
  obtain ⟨f, hf⟩ := h.centData inf_le_right hE4
  exact ⟨hE4, Subgroup.eq_of_le_of_card_ge hFle (by rw [hf.card, hF8])⟩

theorem E8Input.e8_conj (h : E8Input K A) {F F' : Subgroup G} (hFA : F ≤ A)
    (hF : CFSG.Assembly.IsElemAbelian 2 F) (hF8 : Nat.card F = 8) (hF'A : F' ≤ A)
    (hF' : CFSG.Assembly.IsElemAbelian 2 F') (hF'8 : Nat.card F' = 8) :
    ∃ a ∈ A, CFSG.conjugate F a = F' := by
  obtain ⟨hE4, hFeq⟩ := h.eq_centIn hFA hF hF8
  obtain ⟨hE4', hFeq'⟩ := h.eq_centIn hF'A hF' hF'8
  obtain ⟨k, hk, hkE⟩ := h.trans _ _ inf_le_right hE4 inf_le_right hE4'
  refine ⟨k, h.idx2.le hk, ?_⟩
  have h1 : CFSG.conjugate F k = A ⊓ Subgroup.centralizer ((F' ⊓ K : Subgroup G) : Set G) :=
    calc CFSG.conjugate F k =
          CFSG.conjugate (A ⊓ Subgroup.centralizer ((F ⊓ K : Subgroup G) : Set G)) k :=
        congrArg (fun X => CFSG.conjugate X k) hFeq
      _ = A ⊓ Subgroup.centralizer ((CFSG.conjugate (F ⊓ K) k : Subgroup G) : Set G) :=
        conjugate_centIn (h.idx2.le hk)
      _ = A ⊓ Subgroup.centralizer ((F' ⊓ K : Subgroup G) : Set G) := by rw [← hkE]
  rw [h1]
  exact hFeq'.symm

end E8

end CFSG.QuasithinUnique.Unc25K1

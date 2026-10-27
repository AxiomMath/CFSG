module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.RkBM

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

section Datum

@[expose] def RkBMInvAt {F : Type} [Group F] (g : F) : Prop :=
  (∃ s : F, s ^ 2 = 1 ∧ s * g * s = g⁻¹) ∧
    ∃ t t' : F, t ^ 2 = 1 ∧ t' ^ 2 = 1 ∧ t * g = g * t ∧ t' * g = g * t' ∧
      (t * t') ^ 3 = 1 ∧ t * t' ≠ 1

@[expose] def RkBMInv (F : Type) [Group F] : Prop :=
  ∀ g : F, g ≠ 1 → g ^ 3 = 1 → RkBMInvAt g

theorem RkBMInvAt.of_equiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F') {g : F}
    (h : RkBMInvAt g) : RkBMInvAt (e g) := by
  obtain ⟨⟨s, hs2, hsg⟩, t, t', ht2, ht'2, htg, ht'g, h3, h1⟩ := h
  refine ⟨⟨e s, ?_, ?_⟩, e t, e t', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hs2, map_one]
  · rw [← map_mul, ← map_mul, hsg, map_inv]
  · rw [← map_pow, ht2, map_one]
  · rw [← map_pow, ht'2, map_one]
  · rw [← map_mul, ← map_mul, htg]
  · rw [← map_mul, ← map_mul, ht'g]
  · rw [← map_mul, ← map_pow, h3, map_one]
  · intro h
    apply h1
    apply e.injective
    rw [map_mul, h, map_one]

theorem RkBMInv.of_equiv {F F' : Type} [Group F] [Group F'] (e : F ≃* F') (h : RkBMInv F) :
    RkBMInv F' := by
  intro g hg1 hg3
  have h1 : e.symm g ≠ 1 := fun h' => hg1 (by rw [← e.apply_symm_apply g, h', map_one])
  have h3 : e.symm g ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
  have := (h (e.symm g) h1 h3).of_equiv e
  rwa [MulEquiv.apply_symm_apply] at this

theorem RkBMInvAt.conj {F : Type} [Group F] {g : F} (h : RkBMInvAt g) (c : F) :
    RkBMInvAt (c * g * c⁻¹) := by
  have := h.of_equiv (MulAut.conj c)
  rwa [MulAut.conj_apply] at this

end Datum

section Lift

variable {T : Type} [Group T]

theorem rkBM_eq_one_of_sq (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1) {c : T}
    (hc : c ∈ Subgroup.center T) (h2 : c ^ 2 = 1) : c = 1 := by
  have h3 := hZ3 c hc
  calc c = c ^ 3 * (c ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

theorem rkBM_lift_inv (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1)
    {s : T ⧸ Subgroup.center T} (hs : s ^ 2 = 1) :
    ∃ t : T, t ^ 2 = 1 ∧ (t : T ⧸ Subgroup.center T) = s := by
  obtain ⟨t₀, rfl⟩ := QuotientGroup.mk_surjective s
  have h2 : t₀ ^ 2 ∈ Subgroup.center T := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hs
  refine ⟨t₀ ^ 3, ?_, ?_⟩
  · rw [← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul]
    exact hZ3 _ h2
  · rw [QuotientGroup.mk_pow, pow_three, ← sq, hs, mul_one]

theorem rkBM_comm_of_inv (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1) {s x : T}
    (hs : s ^ 2 = 1)
    (hc : (s : T ⧸ Subgroup.center T) * x = (x : T ⧸ Subgroup.center T) * s) :
    s * x = x * s := by
  have hs' : s * s = 1 := by rw [← sq]; exact hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs'
  have hs'' : (s : T ⧸ Subgroup.center T) * s = 1 := by
    rw [← QuotientGroup.mk_mul, hs', QuotientGroup.mk_one]
  obtain ⟨c, hcdef⟩ : ∃ c : T, c = s * x * s * x⁻¹ := ⟨_, rfl⟩
  have hcZ : c ∈ Subgroup.center T := by
    rw [← QuotientGroup.eq_one_iff, hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc]
    calc (x : T ⧸ Subgroup.center T) * s * s * (x : T ⧸ Subgroup.center T)⁻¹
        = x * ((s : T ⧸ Subgroup.center T) * s) * (x : T ⧸ Subgroup.center T)⁻¹ := by group
      _ = 1 := by rw [hs'']; group
  have hc1 : s * c * s = c := by
    calc s * c * s = c * s * s := by rw [Subgroup.mem_center_iff.1 hcZ s]
      _ = c := by rw [mul_assoc, hs', mul_one]
  have hc2 : s * c * s = c⁻¹ := by
    rw [hcdef]
    calc s * (s * x * s * x⁻¹) * s = (s * s) * x * s * x⁻¹ * s := by group
      _ = x * s * x⁻¹ * s := by rw [hs', one_mul]
      _ = x * s⁻¹ * x⁻¹ * s⁻¹ := by rw [hsinv]
      _ = (s * x * s * x⁻¹)⁻¹ := by group
  have hcc : c = 1 := by
    apply rkBM_eq_one_of_sq hZ3 hcZ
    have h : c = c⁻¹ := hc1.symm.trans hc2
    rw [sq]
    calc c * c = c * c⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel c
  have h1 : s * x * s = x := by
    have := hcc
    rw [hcdef] at this
    exact mul_inv_eq_one.1 this
  calc s * x = s * x * s * s := by rw [mul_assoc (s * x), hs', mul_one]
    _ = x * s := by rw [h1]

theorem rkBM_inv_lift (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1) {s x : T} (hs : s ^ 2 = 1)
    (hi : (s : T ⧸ Subgroup.center T) * x * s = (x : T ⧸ Subgroup.center T)⁻¹) :
    ∃ x' : T, (x' : T ⧸ Subgroup.center T) = x ∧ s * x' * s = x'⁻¹ := by
  obtain ⟨c, hcdef⟩ : ∃ c : T, c = s * x * s * x := ⟨_, rfl⟩
  have hcZ : c ∈ Subgroup.center T := by
    rw [← QuotientGroup.eq_one_iff, hcdef, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, hi, inv_mul_cancel]
  refine ⟨x * c, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff c).2 hcZ, mul_one]
  · have hcs : s * c = c * s := Subgroup.mem_center_iff.1 hcZ s
    have hcx : x⁻¹ * c = c * x⁻¹ := Subgroup.mem_center_iff.1 hcZ x⁻¹
    have hsxs : s * x * s = c * x⁻¹ := by rw [hcdef]; group
    have hc3 := hZ3 c hcZ
    have hcc : c * c = c⁻¹ := by
      calc c * c = c ^ 3 * c⁻¹ := by rw [pow_succ, mul_inv_cancel_right, sq]
        _ = c⁻¹ := by rw [hc3, one_mul]
    calc s * (x * c) * s = s * x * (c * s) := by group
      _ = s * x * (s * c) := by rw [hcs]
      _ = (s * x * s) * c := by group
      _ = c * x⁻¹ * c := by rw [hsxs]
      _ = c * (x⁻¹ * c) := by group
      _ = c * (c * x⁻¹) := by rw [hcx]
      _ = (c * c) * x⁻¹ := by group
      _ = c⁻¹ * x⁻¹ := by rw [hcc]
      _ = (x * c)⁻¹ := by rw [mul_inv_rev]

theorem rkBM_pow_three_of_inv (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1) {s x : T}
    (hs : s ^ 2 = 1) (hi : s * x * s = x⁻¹) (h3 : (x : T ⧸ Subgroup.center T) ^ 3 = 1) :
    x ^ 3 = 1 := by
  have hs' : s * s = 1 := by rw [← sq]; exact hs
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs'
  have hwZ : x ^ 3 ∈ Subgroup.center T := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h3
  have h1 : s * x ^ 3 * s = x ^ 3 := by
    rw [Subgroup.mem_center_iff.1 hwZ s, mul_assoc, hs', mul_one]
  have h2 : s * x ^ 3 * s = (x ^ 3)⁻¹ := by
    have := map_pow (MulAut.conj s) x 3
    simp only [MulAut.conj_apply, hsinv] at this
    rw [this, hi, inv_pow]
  apply rkBM_eq_one_of_sq hZ3 hwZ
  have h : x ^ 3 = (x ^ 3)⁻¹ := h1.symm.trans h2
  rw [sq]
  calc x ^ 3 * x ^ 3 = x ^ 3 * (x ^ 3)⁻¹ := by rw [← h]
    _ = 1 := mul_inv_cancel _

theorem rkBM_cover_plane [Finite T] (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1) {g : T}
    (hg1 : (g : T ⧸ Subgroup.center T) ≠ 1) (hg3 : (g : T ⧸ Subgroup.center T) ^ 3 = 1)
    (hD : RkBMInvAt (g : T ⧸ Subgroup.center T)) :
    ∃ E : Subgroup T, IsElemAbelian 3 E ∧ 3 ^ 2 * Nat.card (Subgroup.center T) ≤ Nat.card E ∧
      ∀ e ∈ E, g * e = e * g := by
  obtain ⟨⟨s₀, hs₀2, hs₀g⟩, t₀, t₀', ht₀2, ht₀'2, ht₀g, ht₀'g, h3, h1⟩ := hD
  obtain ⟨s, hs2, rfl⟩ := rkBM_lift_inv hZ3 hs₀2
  obtain ⟨t, ht2, rfl⟩ := rkBM_lift_inv hZ3 ht₀2
  obtain ⟨t', ht'2, rfl⟩ := rkBM_lift_inv hZ3 ht₀'2
  obtain ⟨g', hg', hsg'⟩ := rkBM_inv_lift hZ3 hs2 hs₀g
  have hg'3 : g' ^ 3 = 1 := rkBM_pow_three_of_inv hZ3 hs2 hsg' (by rw [hg']; exact hg3)
  have hw : g⁻¹ * g' ∈ Subgroup.center T := QuotientGroup.eq.1 hg'.symm
  have hgg' : g * g' = g' * g := by
    have hc : g * (g⁻¹ * g') = (g⁻¹ * g') * g := Subgroup.mem_center_iff.1 hw g
    calc g * g' = g * (g * (g⁻¹ * g')) := by group
      _ = g * ((g⁻¹ * g') * g) := by rw [hc]
      _ = g' * g := by group
  have htg : t * g = g * t := rkBM_comm_of_inv hZ3 ht2 ht₀g
  have ht'g : t' * g = g * t' := rkBM_comm_of_inv hZ3 ht'2 ht₀'g
  have htg' : t * g' = g' * t := rkBM_comm_of_inv hZ3 ht2 (by rw [hg']; exact ht₀g)
  have ht'g' : t' * g' = g' * t' := rkBM_comm_of_inv hZ3 ht'2 (by rw [hg']; exact ht₀'g)
  obtain ⟨a, ha⟩ : ∃ a : T, a = t * t' := ⟨_, rfl⟩
  have htt : t * t = 1 := by rw [← sq]; exact ht2
  have ht't' : t' * t' = 1 := by rw [← sq]; exact ht'2
  have hta : t * a * t = a⁻¹ := by
    rw [ha, mul_inv_rev, inv_eq_of_mul_eq_one_right htt, inv_eq_of_mul_eq_one_right ht't']
    calc t * (t * t') * t = (t * t) * t' * t := by group
      _ = t' * t := by rw [htt, one_mul]
  have ha3 : a ^ 3 = 1 :=
    rkBM_pow_three_of_inv hZ3 ht2 hta (by rw [ha, QuotientGroup.mk_mul]; exact h3)
  have hag : a * g = g * a := by
    calc a * g = t * (t' * g) := by rw [ha, mul_assoc]
      _ = t * (g * t') := by rw [ht'g]
      _ = (t * g) * t' := by rw [mul_assoc]
      _ = (g * t) * t' := by rw [htg]
      _ = g * a := by rw [ha, mul_assoc]
  have hag' : a * g' = g' * a := by
    calc a * g' = t * (t' * g') := by rw [ha, mul_assoc]
      _ = t * (g' * t') := by rw [ht'g']
      _ = (t * g') * t' := by rw [mul_assoc]
      _ = (g' * t) * t' := by rw [htg']
      _ = g' * a := by rw [ha, mul_assoc]
  have hab : ((a : T) : T ⧸ Subgroup.center T) = (t : T ⧸ Subgroup.center T) * t' := by
    rw [ha, QuotientGroup.mk_mul]
  have hnot : (a : T ⧸ Subgroup.center T) ∉ Subgroup.zpowers (g : T ⧸ Subgroup.center T) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcomm : (t : T ⧸ Subgroup.center T) * a = (a : T ⧸ Subgroup.center T) * t := by
      rw [← hk]
      exact (Commute.zpow_right ht₀g k).eq
    have hinv : (t : T ⧸ Subgroup.center T) * a * t = (a : T ⧸ Subgroup.center T)⁻¹ := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hta, QuotientGroup.mk_inv]
    have htt' : (t : T ⧸ Subgroup.center T) * t = 1 := by
      rw [← QuotientGroup.mk_mul, htt, QuotientGroup.mk_one]
    have h2 : (a : T ⧸ Subgroup.center T) ^ 2 = 1 := by
      have h : (a : T ⧸ Subgroup.center T) = (a : T ⧸ Subgroup.center T)⁻¹ := by
        rw [← hinv, hcomm, mul_assoc, htt', mul_one]
      rw [sq]
      calc (a : T ⧸ Subgroup.center T) * a = a * (a : T ⧸ Subgroup.center T)⁻¹ := by
            nth_rewrite 2 [h]; rfl
        _ = 1 := mul_inv_cancel _
    have ha3' : (a : T ⧸ Subgroup.center T) ^ 3 = 1 := by rw [hab]; exact h3
    apply h1
    rw [← hab]
    calc (a : T ⧸ Subgroup.center T) = a ^ 3 * ((a : T ⧸ Subgroup.center T) ^ 2)⁻¹ := by
          rw [pow_succ', mul_inv_cancel_right]
      _ = 1 := by rw [ha3', h2]; group
  have hagb : (a : T ⧸ Subgroup.center T) * g = (g : T ⧸ Subgroup.center T) * a := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hag]
  obtain ⟨-, hcard9⟩ := CFSG.Goldschmidt.G63.sup_zpowers_isElemAbelian Nat.prime_three
    (by rw [hab]; exact h3) hg3 hg1 hnot hagb
  let S : Set T := (Subgroup.center T : Set T) ∪ {g', a}
  have hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro x (hx | hx | hx) y (hy | hy | hy)
    · exact (Subgroup.mem_center_iff.1 hx y).symm
    · exact (Subgroup.mem_center_iff.1 hx y).symm
    · exact (Subgroup.mem_center_iff.1 hx y).symm
    · exact Subgroup.mem_center_iff.1 hy x
    · rw [Set.mem_singleton_iff.1 hx, hy]
    · rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]; exact hag'.symm
    · exact Subgroup.mem_center_iff.1 hy x
    · rw [Set.mem_singleton_iff.1 hx, hy]; exact hag'
    · rw [Set.mem_singleton_iff.1 hx, Set.mem_singleton_iff.1 hy]
  have hcommE : IsMulCommutative (Subgroup.closure S) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hS x hx y hy
  have hexp : ∀ x ∈ Subgroup.closure S, x ^ 3 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx | hx
      · exact hZ3 x hx
      · rw [hx]; exact hg'3
      · rw [Set.mem_singleton_iff.1 hx]; exact ha3
    | one => exact one_pow 3
    | mul x y hx hy ihx ihy =>
      have hc : Commute x y := congrArg Subtype.val (hcommE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      rw [hc.mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  have hle : Subgroup.closure S ≤ Subgroup.centralizer ({g} : Set T) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    rcases hx with hx | hx | hx
    · exact (Subgroup.mem_center_iff.1 hx g)
    · rw [hx]; exact hgg'
    · rw [Set.mem_singleton_iff.1 hx]; exact hag.symm
  have hZE : Subgroup.center T ≤ Subgroup.closure S := fun z hz =>
    Subgroup.subset_closure (Or.inl hz)
  refine ⟨Subgroup.closure S, ⟨hcommE, hexp⟩, ?_, fun e he =>
    Subgroup.mem_centralizer_iff.1 (hle he) g rfl⟩
  let φ : ↥(Subgroup.closure S) →* T ⧸ Subgroup.center T :=
    (QuotientGroup.mk' (Subgroup.center T)).comp (Subgroup.closure S).subtype
  have hker : Nat.card φ.ker = Nat.card (Subgroup.center T) := by
    have hk : φ.ker = (Subgroup.center T).subgroupOf (Subgroup.closure S) := by
      ext x
      simp [φ, Subgroup.mem_subgroupOf, QuotientGroup.eq_one_iff]
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv]
  have hrange : Subgroup.zpowers ((a : T) : T ⧸ Subgroup.center T) ⊔
      Subgroup.zpowers (g : T ⧸ Subgroup.center T) ≤ φ.range := by
    refine sup_le ((Subgroup.zpowers_le).2 ⟨⟨a, Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩,
      rfl⟩) ((Subgroup.zpowers_le).2 ⟨⟨g', Subgroup.subset_closure (Or.inr (Or.inl rfl))⟩, ?_⟩)
    show ((g' : T) : T ⧸ Subgroup.center T) = g
    exact hg'
  have hcardR : 9 ≤ Nat.card φ.range := by
    have := Subgroup.card_le_of_le hrange
    rw [hcard9] at this
    exact this
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker] at h
  rw [← h]
  calc 3 ^ 2 * Nat.card (Subgroup.center T) = Nat.card (Subgroup.center T) * 9 := by ring
    _ ≤ Nat.card (Subgroup.center T) * Nat.card φ.range := Nat.mul_le_mul_left _ hcardR

end Lift

section Inner

variable {T : Type} [Group T] [Finite T]

omit [Finite T] in
theorem rkBM_commutator_mul_center {a b c₁ c₂ : T} (h₁ : c₁ ∈ Subgroup.center T)
    (h₂ : c₂ ∈ Subgroup.center T) : ⁅a * c₁, b * c₂⁆ = ⁅a, b⁆ := by
  have e₁ : ∀ x : T, x * c₁ = c₁ * x := Subgroup.mem_center_iff.1 h₁
  have e₂ : ∀ x : T, x * c₂ = c₂ * x := Subgroup.mem_center_iff.1 h₂
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c₁ * (b * c₂) * (a * c₁)⁻¹ * (b * c₂)⁻¹
      = a * (c₁ * b) * c₂ * c₁⁻¹ * a⁻¹ * c₂⁻¹ * b⁻¹ := by group
    _ = a * (b * c₁) * c₂ * c₁⁻¹ * a⁻¹ * c₂⁻¹ * b⁻¹ := by rw [← e₁ b]
    _ = a * b * (c₁ * c₂ * c₁⁻¹) * a⁻¹ * c₂⁻¹ * b⁻¹ := by group
    _ = a * b * c₂ * a⁻¹ * c₂⁻¹ * b⁻¹ := by
      rw [show c₁ * c₂ * c₁⁻¹ = c₂ by rw [← e₁ c₂]; group]
    _ = a * b * (c₂ * a⁻¹) * c₂⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * c₂) * c₂⁻¹ * b⁻¹ := by rw [← e₂ a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem rkBM_inner (hT : commutator T = ⊤)
    (hO : Nat.Coprime 3 (Nat.card (Outer (T ⧸ Subgroup.center T))))
    (hZF : Subgroup.center (T ⧸ Subgroup.center T) = ⊥) {β : MulAut T} (hβ : β ^ 3 = 1) :
    ∃ g : T, β = MulAut.conj g ∧ (g : T ⧸ Subgroup.center T) ^ 3 = 1 := by
  let β' : MulAut (T ⧸ Subgroup.center T) :=
    QuotientGroup.congr (Subgroup.center T) (Subgroup.center T) β (Subgroup.map_center_eq β)
  have hβ'x : ∀ x : T, β' (x : T ⧸ Subgroup.center T) = ((β x : T) : T ⧸ Subgroup.center T) :=
    fun _ => rfl
  have hβ3x : ∀ x : T, β (β (β x)) = x := fun x => by
    have := congrArg (fun φ : MulAut T => φ x) hβ
    simpa [pow_succ] using this
  have hβ'3 : β' ^ 3 = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hβ'x, hβ3x]
  obtain ⟨gb, hgb⟩ := mem_innerAut_of_pow_eq_one' hO hβ'3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have hmod : ∀ x : T, (g * x * g⁻¹)⁻¹ * β x ∈ Subgroup.center T := fun x => by
    rw [← QuotientGroup.eq, ← hβ'x, ← hgb, MulAut.conj_apply, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  let H : Subgroup T :=
    { carrier := {x | β x = g * x * g⁻¹}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, hx, hy]
        group
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_inv, hx]
        group }
  have hcomm : ∀ x y : T, ⁅x, y⁆ ∈ H := fun x y => by
    show β ⁅x, y⁆ = g * ⁅x, y⁆ * g⁻¹
    have hbx : β x = g * x * g⁻¹ * ((g * x * g⁻¹)⁻¹ * β x) := by group
    have hby : β y = g * y * g⁻¹ * ((g * y * g⁻¹)⁻¹ * β y) := by group
    rw [map_commutatorElement, hbx, hby, rkBM_commutator_mul_center (hmod x) (hmod y)]
    simp only [commutatorElement_def]
    group
  have hH : H = ⊤ := by
    rw [eq_top_iff, ← hT]
    exact Subgroup.commutator_le.2 fun x _ y _ => hcomm x y
  refine ⟨g, ?_, ?_⟩
  · ext x
    have hx : x ∈ H := hH ▸ Subgroup.mem_top x
    rw [MulAut.conj_apply]
    exact hx
  · have h1 : MulAut.conj ((g : T ⧸ Subgroup.center T) ^ 3) = 1 := by
      rw [map_pow, hgb]
      exact hβ'3
    have h2 : (g : T ⧸ Subgroup.center T) ^ 3 ∈ Subgroup.center (T ⧸ Subgroup.center T) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut (T ⧸ Subgroup.center T) => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * (g : T ⧸ Subgroup.center T) ^ 3
          = ((g : T ⧸ Subgroup.center T) ^ 3 * y * ((g : T ⧸ Subgroup.center T) ^ 3)⁻¹) *
            (g : T ⧸ Subgroup.center T) ^ 3 := by rw [this]
        _ = (g : T ⧸ Subgroup.center T) ^ 3 * y := by group
    rw [hZF, Subgroup.mem_bot] at h2
    exact h2

theorem rkAut_three_of_cover (hT : commutator T = ⊤)
    (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1)
    (hO : Nat.Coprime 3 (Nat.card (Outer (T ⧸ Subgroup.center T))))
    (hZF : Subgroup.center (T ⧸ Subgroup.center T) = ⊥) (hD : RkBMInv (T ⧸ Subgroup.center T))
    (h3 : ∃ x : T ⧸ Subgroup.center T, x ≠ 1 ∧ x ^ 3 = 1) : RkAut 3 T := by
  intro β hβ
  obtain ⟨g, rfl, hg3⟩ := rkBM_inner hT hO hZF hβ
  by_cases hg1 : (g : T ⧸ Subgroup.center T) = 1
  · obtain ⟨x, hx1, hx3⟩ := h3
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨E, hE, hc, -⟩ := rkBM_cover_plane hZ3 hx1 hx3 (hD _ hx1 hx3)
    have hgZ : g ∈ Subgroup.center T := (QuotientGroup.eq_one_iff g).1 hg1
    refine ⟨E, hE, hc, fun e _ => ?_⟩
    rw [MulAut.conj_apply, ← Subgroup.mem_center_iff.1 hgZ e, mul_inv_cancel_right]
  · obtain ⟨E, hE, hc, hEg⟩ := rkBM_cover_plane hZ3 hg1 hg3 (hD _ hg1 hg3)
    exact ⟨E, hE, hc, fun e he => by rw [MulAut.conj_apply, hEg e he, mul_inv_cancel_right]⟩

theorem rkAut_three_of_sporadic_cover (hOut : SporadicOuterLeTwo) (hBr : SporadicBridges)
    {X : TauCeti.SporadicName} (hD : RkBMInv (NativeSporadic.Carrier X))
    (hX : ∃ x : NativeSporadic.Carrier X, x ≠ 1 ∧ x ^ 3 = 1) (hq : CFSG.Open.IsQuasisimple T)
    (hZ3 : ∀ z ∈ Subgroup.center T, z ^ 3 = 1)
    (e : T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic X).Group) : RkAut 3 T := by
  haveI hsimple : IsSimpleGroup (T ⧸ Subgroup.center T) := hq.2
  have hnab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian T hq
  have hZF : Subgroup.center (T ⧸ Subgroup.center T) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have ho := hOut (T ⧸ Subgroup.center T) hq.2 hnab X ⟨e⟩
  have hO := rkBM_coprime Nat.prime_three (by norm_num) ho Nat.card_pos
  let e' : T ⧸ Subgroup.center T ≃* NativeSporadic.Carrier X := e.trans (hBr X).some.symm
  refine rkAut_three_of_cover hq.1 hZ3 hO hZF (RkBMInv.of_equiv e'.symm hD) ?_
  obtain ⟨x, hx1, hx3⟩ := hX
  refine ⟨e'.symm x, fun h => hx1 ?_, by rw [← map_pow, hx3, map_one]⟩
  rw [← e'.apply_symm_apply x, h, map_one]

theorem rkBM_pow_three_of_card_dvd (h : Nat.card (Subgroup.center T) ∣ 3) :
    ∀ z ∈ Subgroup.center T, z ^ 3 = 1 := fun z hz =>
  orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard _ hz).trans h)

end Inner

section Fi22


theorem rkAut_Fi22_cover (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) (hD : RkBMInv NativeSporadic.Fi22) {T : Type} [Group T] [Finite T]
    (hq : CFSG.Open.IsQuasisimple T) (hZ : IsPGroup 3 (Subgroup.center T))
    (e : T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) : RkAut 3 T := by
  have hd : Nat.card (Subgroup.center T) ∣ 6 := card_center_dvd_multiplier hSpM hq .Fi22 e
  have h3 : Nat.card (Subgroup.center T) ∣ 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hZ
    rw [hn] at hd ⊢
    have hn1 : n ≤ 1 := by
      by_contra hn1
      push Not at hn1
      have : 3 ^ 2 ∣ 6 := (pow_dvd_pow 3 hn1).trans hd
      norm_num at this
    interval_cases n <;> norm_num
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Fi22_elementary_three_rank_four
  have hX : ∃ x : NativeSporadic.Carrier .Fi22, x ≠ 1 ∧ x ^ 3 = 1 := by
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (1 : E)
    exact ⟨(x : NativeSporadic.Fi22), fun h => hx (Subtype.ext h), hE.2 _ x.2⟩
  exact rkAut_three_of_sporadic_cover (X := .Fi22) hOut hBr hD hX hq
    (rkBM_pow_three_of_card_dvd h3) e

end Fi22

section Fi24


theorem rkAut_Fi24Prime_cover (hOut : SporadicOuterLeTwo) (hSpM : SporadicMultipliers)
    (hBr : SporadicBridges) (hD : RkBMInv NativeSporadic.Fi24prime) {T : Type} [Group T]
    [Finite T] (hq : CFSG.Open.IsQuasisimple T)
    (e : T ⧸ Subgroup.center T ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) : RkAut 3 T := by
  have hd : Nat.card (Subgroup.center T) ∣ 3 := card_center_dvd_multiplier hSpM hq .Fi24Prime e
  obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.Fi24prime_elementary_three_rank_four
  have hX : ∃ x : NativeSporadic.Carrier .Fi24Prime, x ≠ 1 ∧ x ^ 3 = 1 := by
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (1 : E)
    exact ⟨(x : NativeSporadic.Fi24prime), fun h => hx (Subtype.ext h), hE.2 _ x.2⟩
  exact rkAut_three_of_sporadic_cover (X := .Fi24Prime) hOut hBr hD hX hq
    (rkBM_pow_three_of_card_dvd hd) e

end Fi24

end CFSG.HardMathSupport.Dickson.I271

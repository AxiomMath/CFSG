module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Wr
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB45Basic

public section

namespace CFSG.OddStandard.Seitz77.CaseB45

open Subgroup CFSG.Open

structure ModelData (Q : Type) [Group Q] where
  T : Subgroup Q
  Lm : Subgroup Q
  normal : Lm.Normal
  card_T : Nat.card T = 2 ^ 8
  odd_index : ¬ 2 ∣ T.index
  card_U : Nat.card ↥(T ⊓ Lm) = 2 ^ 6
  fb7 : ∀ E : Subgroup Q, E ≤ T → IsElemAbelian 2 E →
    Nat.card E ≤ 16 ∧ (Nat.card E = 16 → E ≤ T ⊓ Lm)
  fb6 : ∀ R : Subgroup (Wr Q), R ≤ Wr.sub T → Wr.ss (T ⊓ Lm) ≤ R → (Wr.swap : Wr Q) ∈ R →
    ∀ x ∈ R, x.e = false → x * x = 1 → x ≠ 1 →
      ¬ Nonempty (↥(R ⊓ centralizer {x}) ≃* ↥(R ⊓ centralizer {(Wr.swap : Wr Q)}))

section Wreath

variable {Q : Type} [Group Q]

theorem ss_normal {Lm : Subgroup Q} (hL : Lm.Normal) : (Wr.ss Lm).Normal := by
  refine ⟨fun w hw g => ?_⟩
  obtain ⟨a, b, e⟩ := w
  obtain ⟨c, d, f⟩ := g
  rw [Wr.mem_ss] at hw ⊢
  obtain ⟨ha, hb, he⟩ := hw
  simp only at ha hb he
  subst he
  cases f
  · simp only [Wr.mk_inv_false, Wr.mk_mul_mk_false, and_true]
    exact ⟨hL.conj_mem a ha c, hL.conj_mem b hb d⟩
  · simp only [Wr.mk_inv_true, Wr.mk_mul_mk_true, Bool.not_false]
    exact ⟨hL.conj_mem b hb c, hL.conj_mem a ha d, rfl⟩

theorem conj_e (g x : Wr Q) : (g * x * g⁻¹).e = x.e := by
  obtain ⟨a, b, e⟩ := g
  obtain ⟨c, d, f⟩ := x
  cases e <;> cases f <;> simp

theorem eq_swap_conj {a : Q} {τ : Wr Q} (h : τ = ⟨a, a⁻¹, true⟩) :
    (⟨a⁻¹, 1, false⟩ : Wr Q) * τ * (⟨a⁻¹, 1, false⟩ : Wr Q)⁻¹ = Wr.swap := by
  subst h
  simp [Wr.swap]

@[expose] def firstCoord (E : Subgroup (Wr Q)) : Subgroup Q where
  carrier := {x | ∃ w ∈ E, w.e = false ∧ w.a = x}
  one_mem' := ⟨1, E.one_mem, rfl, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, e⟩, hw, he, rfl⟩ ⟨⟨c, d, f⟩, hw', hf, rfl⟩
    simp only at he hf
    subst he hf
    exact ⟨_, E.mul_mem hw hw', rfl, rfl⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, e⟩, hw, he, rfl⟩
    simp only at he
    subst he
    exact ⟨_, E.inv_mem hw, rfl, rfl⟩

@[expose] def secondCoord (E : Subgroup (Wr Q)) : Subgroup Q where
  carrier := {x | ∃ w ∈ E, w.e = false ∧ w.b = x}
  one_mem' := ⟨1, E.one_mem, rfl, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a, b, e⟩, hw, he, rfl⟩ ⟨⟨c, d, f⟩, hw', hf, rfl⟩
    simp only at he hf
    subst he hf
    exact ⟨_, E.mul_mem hw hw', rfl, rfl⟩
  inv_mem' := by
    rintro _ ⟨⟨a, b, e⟩, hw, he, rfl⟩
    simp only at he
    subst he
    exact ⟨_, E.inv_mem hw, rfl, rfl⟩

theorem firstCoord_le {E : Subgroup (Wr Q)} {T : Subgroup Q} (h : E ≤ Wr.sub T) :
    firstCoord E ≤ T := by
  rintro _ ⟨w, hw, -, rfl⟩
  exact (h hw).1

theorem secondCoord_le {E : Subgroup (Wr Q)} {T : Subgroup Q} (h : E ≤ Wr.sub T) :
    secondCoord E ≤ T := by
  rintro _ ⟨w, hw, -, rfl⟩
  exact (h hw).2

theorem isElemAbelian_firstCoord {E : Subgroup (Wr Q)} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (firstCoord E) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨⟨a, b, e⟩, hw, he, ha⟩ := x.2
    obtain ⟨⟨c, d, f⟩, hw', hf, hc⟩ := y.2
    simp only at he hf ha hc
    subst he hf
    have := hE.1.is_comm.comm ⟨_, hw⟩ ⟨_, hw'⟩
    have h2 := congrArg (fun z : ↥E => z.1.a) this
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hc]
    simpa using h2
  · obtain ⟨⟨a, b, e⟩, hw, he, rfl⟩ := hx
    simp only at he
    subst he
    have := hE.2 _ hw
    have h2 := congrArg Wr.a this
    simpa [pow_two, Wr.one_def] using h2

theorem isElemAbelian_secondCoord {E : Subgroup (Wr Q)} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (secondCoord E) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨⟨a, b, e⟩, hw, he, ha⟩ := x.2
    obtain ⟨⟨c, d, f⟩, hw', hf, hc⟩ := y.2
    simp only at he hf ha hc
    subst he hf
    have := hE.1.is_comm.comm ⟨_, hw⟩ ⟨_, hw'⟩
    have h2 := congrArg (fun z : ↥E => z.1.b) this
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← ha, ← hc]
    simpa using h2
  · obtain ⟨⟨a, b, e⟩, hw, he, rfl⟩ := hx
    simp only at he
    subst he
    have := hE.2 _ hw
    have h2 := congrArg Wr.b this
    simpa [pow_two, Wr.one_def] using h2

end Wreath

section Base

variable {Q : Type} [Group Q] [Finite Q] (M : ModelData Q)

theorem baseElem {E : Subgroup (Wr Q)} (hET : E ≤ Wr.sub M.T) (hE : IsElemAbelian 2 E)
    (hcard : Nat.card E = 2 ^ 8) : E ≤ Wr.ss (M.T ⊓ M.Lm) := by
  classical
  have hE1 := M.fb7 _ (firstCoord_le hET) (isElemAbelian_firstCoord hE)
  have hE2 := M.fb7 _ (secondCoord_le hET) (isElemAbelian_secondCoord hE)
  by_cases hbase : ∀ w ∈ E, w.e = false
  ·
    let f : ↥E → ↥(firstCoord E) × ↥(secondCoord E) := fun w =>
      (⟨w.1.a, ⟨w.1, w.2, hbase _ w.2, rfl⟩⟩, ⟨w.1.b, ⟨w.1, w.2, hbase _ w.2, rfl⟩⟩)
    have hinj : Function.Injective f := by
      intro w w' h
      have h1 : w.1.a = w'.1.a := congrArg (fun p => p.1.1) h
      have h2 : w.1.b = w'.1.b := congrArg (fun p => p.2.1) h
      apply Subtype.ext
      exact Wr.ext h1 h2 (by rw [hbase _ w.2, hbase _ w'.2])
    have hle := Nat.card_le_card_of_injective f hinj
    rw [Nat.card_prod, hcard] at hle
    have c1 : Nat.card (firstCoord E) = 16 := by nlinarith [hE1.1, hE2.1]
    have c2 : Nat.card (secondCoord E) = 16 := by nlinarith [hE1.1, hE2.1]
    intro w hw
    rw [Wr.mem_ss]
    exact ⟨hE1.2 c1 ⟨w, hw, hbase w hw, rfl⟩, hE2.2 c2 ⟨w, hw, hbase w hw, rfl⟩, hbase w hw⟩
  ·
    exfalso
    push Not at hbase
    obtain ⟨e₀, he₀, he₀e⟩ := hbase
    have he₀e' : e₀.e = true := by simpa using he₀e
    obtain ⟨c, d, f⟩ := e₀
    simp only at he₀e'
    subst he₀e'
    let E₀ : Subgroup (Wr Q) := E ⊓ Wr.base
    let g : ↥E₀ → ↥(secondCoord E) := fun w =>
      ⟨w.1.b, ⟨w.1, w.2.1, Wr.mem_base.1 w.2.2, rfl⟩⟩
    have hginj : Function.Injective g := by
      intro w w' h
      have hb : w.1.b = w'.1.b := congrArg Subtype.val h
      obtain ⟨⟨x, y, e⟩, hw1, hw2⟩ := w
      obtain ⟨⟨x', y', e'⟩, hw1', hw2'⟩ := w'
      have he : e = false := Wr.mem_base.1 hw2
      have he' : e' = false := Wr.mem_base.1 hw2'
      subst he he'
      simp only at hb
      subst hb
      have k1 := congrArg (fun z : ↥E => z.1.a) (hE.1.is_comm.comm ⟨_, hw1⟩ ⟨_, he₀⟩)
      have k2 := congrArg (fun z : ↥E => z.1.a) (hE.1.is_comm.comm ⟨_, hw1'⟩ ⟨_, he₀⟩)
      simp only [Subgroup.coe_mul, Wr.mk_mul_mk_false, Wr.mk_mul_mk_true] at k1 k2
      have : x = x' := by
        have := k1.trans k2.symm
        exact mul_right_cancel this
      subst this
      rfl
    have hle₀ : Nat.card E₀ ≤ 16 := by
      calc Nat.card E₀ ≤ Nat.card (secondCoord E) := Nat.card_le_card_of_injective g hginj
        _ ≤ 16 := hE2.1
    have hsub : (E : Set (Wr Q)) ⊆
        (E₀ : Set (Wr Q)) ∪ (fun z => z * ⟨c, d, true⟩) '' (E₀ : Set (Wr Q)) := by
      intro w hw
      by_cases hwe : w.e = false
      · exact Or.inl ⟨hw, Wr.mem_base.2 hwe⟩
      · right
        refine ⟨w * (⟨c, d, true⟩ : Wr Q)⁻¹, ⟨E.mul_mem hw (E.inv_mem he₀), ?_⟩,
          inv_mul_cancel_right w _⟩
        have hwe' : w.e = true := by simpa using hwe
        exact Wr.mem_base.2 (by simp [Wr.mul_def, Wr.inv_def, hwe'])
    have hcard' : Nat.card E ≤ 2 * Nat.card E₀ := by
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_union_le (E₀ : Set (Wr Q))
        ((fun z => z * (⟨c, d, true⟩ : Wr Q)) '' (E₀ : Set (Wr Q)))
      have h3 := Set.ncard_image_le (s := (E₀ : Set (Wr Q)))
        (f := fun z => z * (⟨c, d, true⟩ : Wr Q))
        (Set.toFinite _)
      have e1 : (E : Set (Wr Q)).ncard = Nat.card E := Nat.card_coe_set_eq _ |>.symm
      have e2 : (E₀ : Set (Wr Q)).ncard = Nat.card E₀ := Nat.card_coe_set_eq _ |>.symm
      omega
    rw [hcard] at hcard'
    omega

end Base

section Main

variable {Q : Type} [Group Q] [Finite Q] (M : ModelData Q)

theorem ModelData.isPGroup_sub : IsPGroup 2 (Wr.sub M.T) :=
  IsPGroup.of_card (n := 17) (by rw [Wr.natCard_sub, M.card_T]; norm_num)

theorem ModelData.not_dvd_index_sub : ¬ 2 ∣ (Wr.sub M.T).index := by
  have h1 := Subgroup.index_mul_card (Wr.sub M.T)
  have h2 := Subgroup.index_mul_card M.T
  rw [Wr.natCard_sub, M.card_T, Wr.natCard] at h1
  rw [M.card_T] at h2
  rw [← h2] at h1
  have : (Wr.sub M.T).index * 2 ^ 17 = M.T.index ^ 2 * 2 ^ 17 := by
    rw [show (2 : ℕ) ^ 17 = (2 ^ 8) ^ 2 * 2 by norm_num]
    calc (Wr.sub M.T).index * ((2 ^ 8) ^ 2 * 2) = (Wr.sub M.T).index * ((2 ^ 8) ^ 2 * 2) := rfl
      _ = M.T.index ^ 2 * ((2 ^ 8) ^ 2 * 2) := by rw [h1]; ring
  have h3 := Nat.eq_of_mul_eq_mul_right (by positivity) this
  rw [h3]
  intro h
  exact M.odd_index (Nat.prime_two.dvd_of_dvd_pow h)

theorem ModelData.exists_conj_le {R : Subgroup (Wr Q)} (hR : IsPGroup 2 R) :
    ∃ g : Wr Q, CaseB45.cs g R ≤ Wr.sub M.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Sy : Sylow 2 (Wr Q) := M.isPGroup_sub.toSylow M.not_dvd_index_sub
  obtain ⟨Q', hRQ⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Wr Q) Sy Q'
  refine ⟨g⁻¹, fun x hx => ?_⟩
  rw [CaseB45.mem_cs] at hx
  have h1 : g⁻¹⁻¹ * x * g⁻¹ ∈ R := hx
  have h2 : g⁻¹⁻¹ * x * g⁻¹ ∈ (Q' : Subgroup (Wr Q)) := hRQ h1
  rw [← hg] at h2
  have key : ∀ y, y ∈ ((g • Sy : Sylow 2 (Wr Q)) : Subgroup (Wr Q)) ↔
      g⁻¹ * y * g ∈ (Sy : Subgroup (Wr Q)) := by
    intro y
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.smul_def]
  rw [key] at h2
  have e : g⁻¹ * (g⁻¹⁻¹ * x * g⁻¹) * g = x := by group
  rw [e] at h2
  exact h2

theorem cs_eq_of_normal {G : Type*} [Group G] (g : G) (N : Subgroup G) [N.Normal] :
    CaseB45.cs g N = N := by
  ext x
  rw [CaseB45.mem_cs]
  constructor
  · intro h
    have := Subgroup.Normal.conj_mem ‹N.Normal› _ h g
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at this
  · intro h
    simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ h g⁻¹

theorem cs_self_of_mem {G : Type*} [Group G] {g : G} {H : Subgroup G} (hg : g ∈ H) :
    CaseB45.cs g H = H := by
  ext x
  rw [CaseB45.mem_cs]
  constructor
  · intro h
    have := H.mul_mem (H.mul_mem hg h) (H.inv_mem hg)
    simpa [mul_assoc] using this
  · intro h
    exact H.mul_mem (H.mul_mem (H.inv_mem hg) h) hg

theorem isElemAbelian_cs {G : Type*} [Group G] {E : Subgroup G} (g : G) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (CaseB45.cs g E) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    rw [CaseB45.mem_cs] at hx hy
    apply Subtype.ext
    have := congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hx⟩ ⟨_, hy⟩)
    simp only [Subgroup.coe_mul] at this ⊢
    have e : x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
    have e' : y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
    rw [e, e', this]
  · rw [CaseB45.mem_cs] at hx
    have := hE.2 _ hx
    have e : (g⁻¹ * x * g) ^ 2 = g⁻¹ * x ^ 2 * g := by
      rw [pow_two, pow_two]
      group
    rw [e] at this
    have h1 : x ^ 2 = 1 := by
      have := congrArg (fun z => g * z * g⁻¹) this
      simpa [mul_assoc] using this
    exact h1

theorem cs_inf_centralizer {G : Type*} [Group G] (h : G) (R : Subgroup G) (x : G) :
    CaseB45.cs h (R ⊓ centralizer {x}) = CaseB45.cs h R ⊓ centralizer {h * x * h⁻¹} := by
  ext y
  rw [CaseB45.mem_cs, Subgroup.mem_inf, Subgroup.mem_inf, CaseB45.mem_cs,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr Iff.rfl ?_
  constructor
  · intro hc
    have e : y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
    have e' : (h * x * h⁻¹) * y = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by group
    rw [e, e', hc]
  · intro hc
    have e : y * (h * x * h⁻¹) = h * ((h⁻¹ * y * h) * x) * h⁻¹ := by group
    have e' : (h * x * h⁻¹) * y = h * (x * (h⁻¹ * y * h)) * h⁻¹ := by group
    rw [e, e'] at hc
    exact mul_left_cancel (mul_right_cancel hc)

noncomputable def equivCs {G : Type*} [Group G] (h : G) (H : Subgroup G) :
    ↥H ≃* ↥(CaseB45.cs h H) :=
  H.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective

theorem ModelData.prep {R S : Subgroup (Wr Q)} (hR : IsPGroup 2 R) (hSR : S ≤ R)
    (hS : S ≤ Wr.ss M.Lm) (hcard : Nat.card S = 2 ^ 12) :
    ∃ g : Wr Q, CaseB45.cs g R ≤ Wr.sub M.T ∧ CaseB45.cs g S = Wr.ss (M.T ⊓ M.Lm) := by
  obtain ⟨g, hg⟩ := M.exists_conj_le hR
  refine ⟨g, hg, ?_⟩
  have : (Wr.ss M.Lm).Normal := ss_normal M.normal
  have h1 : CaseB45.cs g S ≤ Wr.ss (M.T ⊓ M.Lm) := by
    intro x hx
    have hxR : x ∈ CaseB45.cs g R := CaseB45.cs_mono g hSR hx
    have hxT : x ∈ Wr.sub M.T := hg hxR
    have hxL : x ∈ Wr.ss M.Lm := by
      have := CaseB45.cs_mono g hS hx
      rwa [cs_eq_of_normal] at this
    rw [Wr.mem_ss] at hxL ⊢
    exact ⟨⟨hxT.1, hxL.1⟩, ⟨hxT.2, hxL.2.1⟩, hxL.2.2⟩
  apply Subgroup.eq_of_le_of_card_ge h1
  rw [Wr.natCard_ss, M.card_U, CaseB45.nat_card_cs, hcard]
  norm_num

theorem sub_inf_ss {Q' : Type*} [Group Q'] (T L : Subgroup Q') :
    Wr.sub T ⊓ Wr.ss L = Wr.ss (T ⊓ L) := by
  ext x
  rw [Subgroup.mem_inf, Wr.mem_ss, Wr.mem_ss, Wr.mem_sub, Subgroup.mem_inf, Subgroup.mem_inf]
  tauto

theorem ModelData.elem_le {R S : Subgroup (Wr Q)} (hR : IsPGroup 2 R) (hSR : S ≤ R)
    (hS : S ≤ Wr.ss M.Lm) (hcardS : Nat.card S = 2 ^ 12) {E : Subgroup (Wr Q)} (hER : E ≤ R)
    (hE : IsElemAbelian 2 E) (hcardE : Nat.card E = 2 ^ 8) : E ≤ S := by
  obtain ⟨g, hgR, hgS⟩ := M.prep hR hSR hS hcardS
  have h1 : CaseB45.cs g E ≤ Wr.ss (M.T ⊓ M.Lm) :=
    baseElem M ((CaseB45.cs_mono g hER).trans hgR) (isElemAbelian_cs g hE)
      (by rw [CaseB45.nat_card_cs, hcardE])
  rw [← hgS] at h1
  have h2 := CaseB45.cs_mono g⁻¹ h1
  rwa [CaseB45.cs_inv_cs, CaseB45.cs_inv_cs] at h2

theorem ModelData.not_equiv {R S : Subgroup (Wr Q)} (hR : IsPGroup 2 R) (hSR : S ≤ R)
    (hS : S ≤ Wr.ss M.Lm) (hcardS : Nat.card S = 2 ^ 12) {τ x : Wr Q} (hτR : τ ∈ R)
    (hτe : τ.e = true) (hτ2 : τ * τ = 1) (hxR : x ∈ R) (hxe : x.e = false) (hx2 : x * x = 1)
    (hx1 : x ≠ 1) :
    ¬ Nonempty (↥(R ⊓ centralizer {x}) ≃* ↥(R ⊓ centralizer {τ})) := by
  obtain ⟨g, hgR, hgS⟩ := M.prep hR hSR hS hcardS
  rintro ⟨f⟩
  have hτ'R : g * τ * g⁻¹ ∈ CaseB45.cs g R := CaseB45.mem_cs_iff.2 hτR
  have hτ'T : g * τ * g⁻¹ ∈ Wr.sub M.T := hgR hτ'R
  have hτ'e : (g * τ * g⁻¹).e = true := by rw [conj_e]; exact hτe
  have hτ'2 : (g * τ * g⁻¹) * (g * τ * g⁻¹) = 1 := by
    have : (g * τ * g⁻¹) * (g * τ * g⁻¹) = g * (τ * τ) * g⁻¹ := by group
    rw [this, hτ2]
    group
  generalize hτ' : g * τ * g⁻¹ = τ' at hτ'R hτ'T hτ'e hτ'2
  obtain ⟨c, d, e⟩ := τ'
  simp only at hτ'e
  subst hτ'e
  have hd : d = c⁻¹ := Wr.eq_of_mul_self_eq_one_of_e hτ'2
  subst hd
  have hc : c ∈ M.T := hτ'T.1
  let δ : Wr Q := ⟨c⁻¹, 1, false⟩
  have hδT : δ ∈ Wr.sub M.T := ⟨M.T.inv_mem hc, M.T.one_mem⟩
  have hδswap : δ * ⟨c, c⁻¹, true⟩ * δ⁻¹ = Wr.swap := eq_swap_conj rfl
  have hLn : (Wr.ss M.Lm).Normal := ss_normal M.normal
  have hRh : CaseB45.cs (δ * g) R ≤ Wr.sub M.T := by
    rw [CaseB45.cs_mul]
    calc CaseB45.cs δ (CaseB45.cs g R) ≤ CaseB45.cs δ (Wr.sub M.T) := CaseB45.cs_mono δ hgR
      _ = Wr.sub M.T := cs_self_of_mem hδT
  have hssh : Wr.ss (M.T ⊓ M.Lm) ≤ CaseB45.cs (δ * g) R := by
    have h1 : Wr.ss (M.T ⊓ M.Lm) ≤ CaseB45.cs g R := by
      rw [← hgS]
      exact CaseB45.cs_mono g hSR
    have h2 : CaseB45.cs δ (Wr.ss (M.T ⊓ M.Lm)) = Wr.ss (M.T ⊓ M.Lm) := by
      rw [← sub_inf_ss, CaseB45.cs_inf, cs_self_of_mem hδT, cs_eq_of_normal]
    rw [CaseB45.cs_mul]
    calc Wr.ss (M.T ⊓ M.Lm) = CaseB45.cs δ (Wr.ss (M.T ⊓ M.Lm)) := h2.symm
      _ ≤ CaseB45.cs δ (CaseB45.cs g R) := CaseB45.cs_mono δ h1
  have hτh : (δ * g) * τ * (δ * g)⁻¹ = Wr.swap := by
    have : (δ * g) * τ * (δ * g)⁻¹ = δ * (g * τ * g⁻¹) * δ⁻¹ := by group
    rw [this, hτ', hδswap]
  have hswh : (Wr.swap : Wr Q) ∈ CaseB45.cs (δ * g) R := by
    rw [← hτh]
    exact CaseB45.mem_cs_iff.2 hτR
  have hxh : (δ * g) * x * (δ * g)⁻¹ ∈ CaseB45.cs (δ * g) R := CaseB45.mem_cs_iff.2 hxR
  have hxhe : ((δ * g) * x * (δ * g)⁻¹).e = false := by rw [conj_e]; exact hxe
  have hxh2 : ((δ * g) * x * (δ * g)⁻¹) * ((δ * g) * x * (δ * g)⁻¹) = 1 := by
    have : ((δ * g) * x * (δ * g)⁻¹) * ((δ * g) * x * (δ * g)⁻¹) =
        (δ * g) * (x * x) * (δ * g)⁻¹ := by group
    rw [this, hx2]
    group
  have hxh1 : (δ * g) * x * (δ * g)⁻¹ ≠ 1 := by
    intro h1
    apply hx1
    have := congrArg (fun z => (δ * g)⁻¹ * z * (δ * g)) h1
    simpa [mul_assoc] using this
  have hnot := M.fb6 _ hRh hssh hswh _ hxh hxhe hxh2 hxh1
  apply hnot
  have e3 : CaseB45.cs (δ * g) (R ⊓ centralizer {x}) =
      CaseB45.cs (δ * g) R ⊓ centralizer {(δ * g) * x * (δ * g)⁻¹} :=
    cs_inf_centralizer _ _ _
  have e4 : CaseB45.cs (δ * g) (R ⊓ centralizer {τ}) =
      CaseB45.cs (δ * g) R ⊓ centralizer {(Wr.swap : Wr Q)} := by
    rw [cs_inf_centralizer, hτh]
  exact ⟨(MulEquiv.subgroupCongr e3.symm).trans ((equivCs (δ * g) _).symm.trans
    (f.trans ((equivCs (δ * g) _).trans (MulEquiv.subgroupCongr e4))))⟩

end Main

end CFSG.OddStandard.Seitz77.CaseB45

module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3V

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem mat_e₁f₂_ne_zero {g : hypSU h 2 1} (hg : g ∈ patSub h sI₄ isPattern_sI₄) (hg1 : g ≠ 1) :
    mat g ιe₁ ιf₂ ≠ 0 := fun e =>
  hg1 (eq_of_mem_patSub_I₄ hg (one_mem _) (by rw [e, mat_one, Matrix.one_apply_ne (by decide)]))

theorem exists_I₃_conj_patSub_I₄ {g g' : hypSU h 2 1} (hg : g ∈ patSub h sI₄ isPattern_sI₄)
    (hg' : g' ∈ patSub h sI₄ isPattern_sI₄) (hg1 : g ≠ 1) (hg1' : g' ≠ 1) :
    ∃ t ∈ I₃sub h, t * g * t⁻¹ = g' := by
  have hb := mat_e₁f₂_ne_zero hg hg1
  have hb' := mat_e₁f₂_ne_zero hg' hg1'
  set v := h.bar (mat g' ιe₁ ιf₂ / mat g ιe₁ ιf₂) with hv
  have hv0 : v ≠ 0 := (map_ne_zero h.bar).2 (div_ne_zero hb' hb)
  obtain ⟨t, ht, e1, -, -, e4, e5⟩ := exists_torus h one_ne_zero hv0
  refine ⟨t, mem_I₃sub.2 ⟨ht, by rw [e1, e4, map_one, inv_one]⟩, ?_⟩
  refine eq_of_mem_patSub_I₄ (torus_conj_mem_patSub isPattern_sI₄ ht hg) hg' ?_
  rw [torus_conj_apply ht, e1, e5, inv_inv, hv, h.bar_bar]
  field_simp

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
theorem mem_Z₂p_iff (d : Data G h) {p : G} (hp : p ∈ d.P) :
    p ∈ d.Z₂p ↔ ∀ u ∈ d.P, ⁅p, u⁆ ∈ d.Zp := by
  obtain ⟨g, hgU, rfl⟩ := hp
  constructor
  · rintro ⟨g', hg', hgg⟩ _ ⟨y, hyU, rfl⟩
    have hgg' : g' = g := d.η_injOn (Z₂Psub_le_A₂sub.trans A₂sub_le_U hg') hgU hgg
    subst hgg'
    exact ⟨_, (mem_Z₂Psub_iff_commutator.1 hg').2 y hyU, map_commutatorElement _ _ _⟩
  · intro hc
    refine ⟨g, mem_Z₂Psub_iff_commutator.2 ⟨hgU, fun y hyU => ?_⟩, rfl⟩
    obtain ⟨z, hz, hze⟩ := hc _ ⟨y, hyU, rfl⟩
    rw [← map_commutatorElement] at hze
    have hcU : ⁅g, y⁆ ∈ hypUnitriangular h 2 1 := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hgU hyU) (inv_mem hgU)) (inv_mem hyU)
    rw [← d.η_injOn (ZPsub_le_U hz) hcU hze]
    exact hz

theorem Hyp.P_inf_centralizer_I₄ (hd : d.Hyp) :
    d.P ⊓ centralizer (d.I₄ : Set G) = d.pull (patSub h sI₄ isPattern_sI₄) := by
  rw [Data.I₄, ← d.pull_U_inf_centralizer (X := I₄sub h) (torusEq_le _),
    U_inf_centralizer_I₄ hd.two_le]

theorem Hyp.exists_I₃_conj_C₄ (hd : d.Hyp) {a a' : G}
    (ha : a ∈ d.P ⊓ centralizer (d.I₄ : Set G)) (ha' : a' ∈ d.P ⊓ centralizer (d.I₄ : Set G))
    (ha1 : a ≠ 1) (ha1' : a' ≠ 1) : ∃ i ∈ d.I₃, i * a * i⁻¹ = a' := by
  rw [hd.P_inf_centralizer_I₄] at ha ha'
  obtain ⟨g, hg, rfl⟩ := ha
  obtain ⟨g', hg', rfl⟩ := ha'
  obtain ⟨t, ht, e⟩ := exists_I₃_conj_patSub_I₄ hg hg' (fun e => ha1 (by rw [e, map_one]))
    (fun e => ha1' (by rw [e, map_one]))
  exact ⟨d.η t, ⟨t, ht, rfl⟩, by rw [← map_inv, ← map_mul, ← map_mul, e]⟩

theorem Hyp.Z₂p_eq (hd : d.Hyp) :
    d.Z₂p = d.Zp ⊔ (d.P ⊓ centralizer (d.I₄ : Set G)) ∧
      d.Zp ⊓ (d.P ⊓ centralizer (d.I₄ : Set G)) = ⊥ :=
  (d.sec2_1_two hd.two_le).2.1

omit [Finite G] in
theorem C₄_le_normalizer_Zp (d : Data G h) :
    d.P ⊓ centralizer (d.I₄ : Set G) ≤ normalizer (d.Zp : Set G) := fun a ha =>
  Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun z hz =>
    (mem_centralizer_iff.1 ((d.sec2_2_three.2.2.2.2 ▸ hz : z ∈ CFSG.centerIn d.P).2) a
      ha.1).symm)

theorem Hyp.card_C₄ (hd : d.Hyp) : Nat.card (d.P ⊓ centralizer (d.I₄ : Set G) : Subgroup G) =
    (2 ^ f) ^ 2 := by
  obtain ⟨hsup, hinf⟩ := hd.Z₂p_eq
  have h1 := card_sup_mul_card_inf_eq d.C₄_le_normalizer_Zp
  rw [← hsup, hinf, Subgroup.card_bot, mul_one, d.card_Z₂p, d.card_Zp] at h1
  have h2 : (2 ^ f) ^ 3 = 2 ^ f * (2 ^ f) ^ 2 := by ring
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm

theorem Hyp.C₄_inf_ZtP (hd : d.Hyp) :
    (d.P ⊓ centralizer (d.I₄ : Set G)) ⊓ d.ZtP = ⊥ := by
  rw [eq_bot_iff, ← hd.Z₂p_eq.2]
  intro a ha
  refine ⟨?_, ha.1⟩
  rw [← hd.ZtP_inf_P]
  exact ⟨ha.2, ha.1.1⟩

theorem Hyp.commutator_Z₂p_tP_mem (hd : d.Hyp) {w u : G} (hw : w ∈ d.Z₂p) (hu : u ∈ d.tP) :
    ⁅w, u⁆ ∈ d.Zp := by
  have hwP : w ∈ d.P := d.Z₂p_le_A₂.trans d.A₂_le_P hw
  obtain ⟨p, hp, hpu | hpu⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hu <;> rw [hpu]
  · exact (d.mem_Z₂p_iff hwP).1 hw p hp
  · rw [commutatorElement_t_mul_right hd.t_mul_t (hd.comm_t (d.P_le_L hwP))
      (hd.comm_t (d.P_le_L hp))]
    exact (d.mem_Z₂p_iff hwP).1 hw p hp

theorem Hyp.B₄_le_normalizer_tZ₂p (hd : d.Hyp) :
    d.B₄ ≤ normalizer ((zpowers d.t ⊔ d.Z₂p : Subgroup G) : Set G) := by
  intro x hx
  have hxN := hd.B₄_le_normalizer_tP hx
  have hxZ := hd.two_core_B₄.1 hx
  have hW : ∀ w ∈ d.Z₂p, x * w * x⁻¹ ∈ zpowers d.t ⊔ d.Z₂p := by
    intro w hw
    have hwP : w ∈ d.P := d.Z₂p_le_A₂.trans d.A₂_le_P hw
    have hy' : x * w * x⁻¹ ∈ d.tP := (mem_normalizer_iff.1 hxN w).1 (mem_sup_right hwP)
    have hc : ∀ u ∈ d.tP, ⁅x * w * x⁻¹, u⁆ ∈ d.Zp := by
      intro u hu
      have hu' : x⁻¹ * u * x ∈ d.tP := by
        have := (mem_normalizer_iff.1 (inv_mem hxN) u).1 hu
        rwa [inv_inv] at this
      have e : ⁅x * w * x⁻¹, u⁆ = x * ⁅w, x⁻¹ * u * x⁆ * x⁻¹ := by
        rw [commutatorElement_def, commutatorElement_def]
        group
      rw [e, ← mem_centralizer_iff.1 hxZ _ (hd.commutator_Z₂p_tP_mem hw hu'),
        mul_inv_cancel_right]
      exact hd.commutator_Z₂p_tP_mem hw hu'
    obtain ⟨p, hp, hpe | hpe⟩ := hd.exists_of_mem_zpowers_sup d.P_le_L hy'
    · rw [hpe]
      refine mem_sup_right ((d.mem_Z₂p_iff hp).2 fun u hu => ?_)
      have := hc u (mem_sup_right hu)
      rwa [hpe] at this
    · rw [hpe]
      refine mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right ((d.mem_Z₂p_iff hp).2
        fun u hu => ?_))
      have := hc u (mem_sup_right hu)
      rwa [hpe, commutatorElement_t_mul_left hd.t_mul_t (hd.comm_t (d.P_le_L hp))
        (hd.comm_t (d.P_le_L hu))] at this
  refine mem_normalizer_of_conj_le fun y hy => ?_
  obtain ⟨w, hw, hyw | hyw⟩ := hd.exists_of_mem_zpowers_sup (d.Z₂p_le_A₂.trans d.A₂_le_L) hy <;>
    rw [hyw]
  · exact hW w hw
  · have hxt : x * d.t * x⁻¹ ∈ zpowers d.t ⊔ d.Z₂p := by
      have hm := hd.cosetData.inv_mul_conj_mem (d.B₄_le hx)
      have e : x * d.t * x⁻¹ = d.t * (d.t⁻¹ * (x * d.t * x⁻¹)) := by group
      rw [e]
      exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right (d.Zp_le_Z₂p hm))
    have e : x * (d.t * w) * x⁻¹ = (x * d.t * x⁻¹) * (x * w * x⁻¹) := by group
    rw [e]
    exact mul_mem hxt (hW w hw)

omit [Finite G] in
theorem tZ₂p_le_tP (d : Data G h) : zpowers d.t ⊔ d.Z₂p ≤ d.tP :=
  sup_le_sup_left (d.Z₂p_le_A₂.trans d.A₂_le_P) _

theorem Hyp.ZtP_le_tZ₂p (hd : d.Hyp) : d.ZtP ≤ zpowers d.t ⊔ d.Z₂p := by
  rw [hd.ZtP_eq]
  exact sup_le_sup_left d.Zp_le_Z₂p _

omit [Finite G] in
theorem comm_ZtP (d : Data G h) {u z : G} (hu : u ∈ d.tP) (hz : z ∈ d.ZtP) : u * z = z * u :=
  (mem_centralizer_iff.1 hz.2 u hu)

omit [Finite G] in
theorem fix_mul (d : Data G h) {u v : G} (hu : u ∈ zpowers d.t ⊔ d.Z₂p)
    (hv : v ∈ zpowers d.t ⊔ d.Z₂p) (hfu : ∀ b ∈ d.B₄, u⁻¹ * (b * u * b⁻¹) ∈ d.ZtP)
    (hfv : ∀ b ∈ d.B₄, v⁻¹ * (b * v * b⁻¹) ∈ d.ZtP) :
    (∀ b ∈ d.B₄, (u * v)⁻¹ * (b * (u * v) * b⁻¹) ∈ d.ZtP) ∧
      ∀ b ∈ d.B₄, u⁻¹⁻¹ * (b * u⁻¹ * b⁻¹) ∈ d.ZtP := by
  have hvt := d.tZ₂p_le_tP hv
  have hut := d.tZ₂p_le_tP hu
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have e : (u * v)⁻¹ * (b * (u * v) * b⁻¹) =
        v⁻¹ * (u⁻¹ * (b * u * b⁻¹)) * v * (v⁻¹ * (b * v * b⁻¹)) := by group
    have hm : v⁻¹ * (u⁻¹ * (b * u * b⁻¹)) * v = u⁻¹ * (b * u * b⁻¹) := by
      rw [mul_assoc, ← d.comm_ZtP hvt (hfu b hb), inv_mul_cancel_left]
    rw [e, hm]
    exact mul_mem (hfu b hb) (hfv b hb)
  · have e : u⁻¹⁻¹ * (b * u⁻¹ * b⁻¹) = u * (u⁻¹ * (b * u * b⁻¹))⁻¹ * u⁻¹ := by group
    rw [e, d.comm_ZtP hut (inv_mem (hfu b hb)), mul_inv_cancel_right]
    exact inv_mem (hfu b hb)

theorem Hyp.commutator_B₄_Z₂p_mem (hd : d.Hyp) {w : G} (hw : w ∈ zpowers d.t ⊔ d.Z₂p) :
    ∀ b ∈ d.B₄, w⁻¹ * (b * w * b⁻¹) ∈ d.ZtP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := d.P ⊓ centralizer (d.I₄ : Set G) with hA
  obtain ⟨hsup, -⟩ := hd.Z₂p_eq
  have hAZ₂ : A ≤ d.Z₂p := hsup ▸ le_sup_right
  have hAt : A ≤ zpowers d.t ⊔ d.Z₂p := hAZ₂.trans le_sup_right
  have hB₄2 : IsPGroup 2 d.B₄ := by
    rw [B₄_eq_oTwo]
    exact CFSG.EvenSmallLie.UnitarySix.YamadaD.isPGroup_oTwo _
  have htP2 : IsPGroup 2 d.tP := hd.isPGroup_T.to_le hd.tP_le_T
  have hfixZ : ∀ z ∈ d.ZtP, ∀ b ∈ d.B₄, z⁻¹ * (b * z * b⁻¹) ∈ d.ZtP := fun z hz b hb =>
    mul_mem (inv_mem hz) ((mem_normalizer_iff.1 (d.B₄_le hb) z).1 hz)
  have hne : ¬ zpowers d.t ⊔ d.Z₂p ≤ d.ZtP := by
    intro hle
    obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
      have hc := hd.card_C₄
      by_contra hcon
      push Not at hcon
      have hbot : A = ⊥ := (eq_bot_iff_forall _).2 hcon
      rw [← hA, hbot, Subgroup.card_bot] at hc
      have := hd.four_le
      have : 1 < (2 ^ f) ^ 2 := by nlinarith
      omega
    have : a ∈ A ⊓ d.ZtP := ⟨haA, hle (hAt haA)⟩
    rw [hd.C₄_inf_ZtP, mem_bot] at this
    exact ha1 this
  obtain ⟨x₀, hx₀, hx₀Z, hfix₀⟩ := exists_mem_forall_conj_mem_of_isPGroup hB₄2
    (htP2.to_le d.tZ₂p_le_tP) hd.ZtP_le_tZ₂p hne hd.B₄_le_normalizer_tZ₂p
    (fun b hb => d.B₄_le hb) fun u hu => d.normalizer_tP_le_normalizer_ZtP
      (le_normalizer (d.tZ₂p_le_tP hu))
  have hAZp : A ≤ normalizer (d.Zp : Set G) := d.C₄_le_normalizer_Zp
  have hfixt : ∀ z ∈ d.ZtP, ∀ v ∈ zpowers d.t ⊔ d.Z₂p,
      (∀ b ∈ d.B₄, v⁻¹ * (b * v * b⁻¹) ∈ d.ZtP) →
        ∀ b ∈ d.B₄, (z * v)⁻¹ * (b * (z * v) * b⁻¹) ∈ d.ZtP := fun z hz v hv hfv =>
    (d.fix_mul (hd.ZtP_le_tZ₂p hz) hv (hfixZ z hz) hfv).1
  obtain ⟨u, hu, y, hy, rfl⟩ : ∃ u ∈ zpowers d.t, ∃ y ∈ d.Z₂p, x₀ = u * y := by
    obtain ⟨y, hy, hx₀y | hx₀y⟩ :=
      hd.exists_of_mem_zpowers_sup (d.Z₂p_le_A₂.trans d.A₂_le_L) hx₀
    · exact ⟨1, one_mem _, y, hy, by rw [hx₀y, one_mul]⟩
    · exact ⟨d.t, mem_zpowers _, y, hy, hx₀y⟩
  have huZ : u ∈ d.ZtP := hd.ZtP_eq ▸ mem_sup_left hu
  rw [hsup] at hy
  obtain ⟨z, hz, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAZp hy
  have hzZ : z ∈ d.ZtP := hd.ZtP_eq ▸ mem_sup_right hz
  have hfa : ∀ b ∈ d.B₄, a⁻¹ * (b * a * b⁻¹) ∈ d.ZtP := by
    have e : a = (u * z)⁻¹ * (u * (z * a)) := by group
    rw [e]
    exact hfixt _ (inv_mem (mul_mem huZ hzZ)) _ hx₀ hfix₀
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [mul_one] at hx₀Z
    exact hx₀Z (mul_mem huZ hzZ)
  have hfA : ∀ a' ∈ A, ∀ b ∈ d.B₄, a'⁻¹ * (b * a' * b⁻¹) ∈ d.ZtP := by
    intro a' ha' b hb
    by_cases ha'1 : a' = 1
    · rw [ha'1, inv_one, one_mul, mul_one, mul_inv_cancel]
      exact one_mem _
    obtain ⟨i, hi, rfl⟩ := hd.exists_I₃_conj_C₄ ha ha' ha1 ha'1
    have hiH := hd.I_le_H (d.I₃_le_I hi)
    have hb' : i⁻¹ * b * i ∈ d.B₄ := by
      have := (mem_normalizer_iff.1 (d.le_normalizer_B₄ (inv_mem hiH.1)) b).1 hb
      rwa [inv_inv] at this
    have e : (i * a * i⁻¹)⁻¹ * (b * (i * a * i⁻¹) * b⁻¹) =
        i * (a⁻¹ * ((i⁻¹ * b * i) * a * (i⁻¹ * b * i)⁻¹)) * i⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.1 hiH.1 _).1 (hfa _ hb')
  obtain ⟨y, hy, hwy | hwy⟩ := hd.exists_of_mem_zpowers_sup (d.Z₂p_le_A₂.trans d.A₂_le_L) hw
  all_goals
    rw [hsup] at hy
    obtain ⟨z', hz', a', ha', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAZp hy
    have hz'Z : z' ∈ d.ZtP := hd.ZtP_eq ▸ mem_sup_right hz'
    have hfza := hfixt z' hz'Z a' (hAt ha') (hfA a' ha')
  · rw [hwy]
    exact hfza
  · rw [hwy]
    exact hfixt d.t (hd.t_mem_ZtP) _ (mul_mem (hd.ZtP_le_tZ₂p hz'Z) (hAt ha')) hfza

theorem Hyp.I₃_le_centralizer_ZtP (hd : d.Hyp) : d.I₃ ≤ centralizer (d.ZtP : Set G) := by
  intro i hi
  rw [hd.ZtP_eq]
  exact mem_centralizer_sup (mem_centralizer_zpowers (hd.L_le_centralizer (d.pull_le_L _ hi)))
    (hd.I₃_le_centralizer_Zp hi)

theorem Hyp.CB₄I₃_le_centralizer_C₄ (hd : d.Hyp) :
    d.CB₄I₃ ≤ centralizer ((d.P ⊓ centralizer (d.I₄ : Set G) : Subgroup G) : Set G) := by
  set A := d.P ⊓ centralizer (d.I₄ : Set G) with hA
  obtain ⟨hsup, -⟩ := hd.Z₂p_eq
  have hAZ₂ : A ≤ d.Z₂p := hsup ▸ le_sup_right
  have hAt : A ≤ zpowers d.t ⊔ d.Z₂p := hAZ₂.trans le_sup_right
  intro c hc
  have hcB := d.CB₄I₃_le hc
  have hδZ : ∀ u ∈ A, u⁻¹ * (c * u * c⁻¹) ∈ d.ZtP := fun u hu =>
    hd.commutator_B₄_Z₂p_mem (hAt hu) c hcB
  have hδmul : ∀ u ∈ A, ∀ v ∈ A, (u * v)⁻¹ * (c * (u * v) * c⁻¹) =
      (u⁻¹ * (c * u * c⁻¹)) * (v⁻¹ * (c * v * c⁻¹)) := by
    intro u hu v hv
    have hvt := d.tZ₂p_le_tP (hAt hv)
    have e : (u * v)⁻¹ * (c * (u * v) * c⁻¹) =
        v⁻¹ * (u⁻¹ * (c * u * c⁻¹)) * v * (v⁻¹ * (c * v * c⁻¹)) := by group
    have hm : v⁻¹ * (u⁻¹ * (c * u * c⁻¹)) * v = u⁻¹ * (c * u * c⁻¹) := by
      rw [mul_assoc, ← d.comm_ZtP hvt (hδZ u hu), inv_mul_cancel_left]
    rw [e, hm]
  have hδconj : ∀ i ∈ d.I₃, ∀ u ∈ A, (i * u * i⁻¹)⁻¹ * (c * (i * u * i⁻¹) * c⁻¹) =
      u⁻¹ * (c * u * c⁻¹) := by
    intro i hi u hu
    have hci : c * i = i * c := (mem_centralizer_iff.1 hc.2 i hi).symm
    have hc' : i⁻¹ * c * i = c := by rw [mul_assoc, hci, inv_mul_cancel_left]
    have e : (i * u * i⁻¹)⁻¹ * (c * (i * u * i⁻¹) * c⁻¹) =
        i * (u⁻¹ * ((i⁻¹ * c * i) * u * (i⁻¹ * c * i)⁻¹)) * i⁻¹ := by group
    rw [e, hc', ← mem_centralizer_iff.1 (hd.I₃_le_centralizer_ZtP hi) _ (hδZ u hu),
      mul_inv_cancel_right]
  have hA2 : 2 < Nat.card A := by
    rw [hA, hd.card_C₄]
    have := hd.four_le
    nlinarith
  have hsq : ∀ y ∈ A, y * y = 1 := fun y hy => d.A₁_comm_sq.2 y (d.Z₂p_le_A₁ (hAZ₂ hy))
  refine mem_centralizer_iff.2 fun z hz => ?_
  by_cases hz1 : z = 1
  · rw [hz1, one_mul, mul_one]
  obtain ⟨x, hx, hx1, hxz⟩ := exists_mem_ne_ne hA2 1 z
  have hzx1 : z * x ≠ 1 := fun e => hxz (by
    rw [eq_inv_of_mul_eq_one_right e, inv_eq_of_mul_eq_one_right (hsq z hz)])
  obtain ⟨i, hi, hie⟩ := hd.exists_I₃_conj_C₄ hx (mul_mem hz hx) hx1 hzx1
  have hzeq : z = (i * x * i⁻¹) * x⁻¹ := by rw [hie, mul_inv_cancel_right]
  have hixA : i * x * i⁻¹ ∈ A := hie ▸ mul_mem hz hx
  have key : z⁻¹ * (c * z * c⁻¹) = 1 := by
    rw [hzeq, hδmul _ hixA _ (inv_mem hx), hδconj i hi x hx, ← hδmul _ hx _ (inv_mem hx),
      mul_inv_cancel]
    group
  have e : c * z * c⁻¹ = z := (inv_mul_eq_one.1 key).symm
  calc z * c = (c * z * c⁻¹) * c := by rw [e]
    _ = c * z := by group

theorem Hyp.CB₄I₃_le_centralizer_Z₂p (hd : d.Hyp) : d.CB₄I₃ ≤ centralizer (d.Z₂p : Set G) := by
  intro c hc
  rw [hd.Z₂p_eq.1]
  exact mem_centralizer_sup (hd.two_core_B₄.1 (d.CB₄I₃_le hc)) (hd.CB₄I₃_le_centralizer_C₄ hc)

theorem Hyp.CB₄I₃_le_centralizer_Z₂p_s (hd : d.Hyp) :
    d.CB₄I₃ ≤ centralizer ((d.Z₂p.map (MulAut.conj d.s).toMonoidHom : Subgroup G) : Set G) := by
  have hsN : d.s ∈ normalizer (d.CB₄I₃ : Set G) := by
    rw [hd.CB₄I₃_eq]
    exact mem_normalizer_sup hd.s_mem_normalizer_V
      (Subgroup.centralizer_le_normalizer _ (mem_centralizer_zpowers hd.s_mem_K₀.2))
  intro c hc
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨w, hw, rfl⟩
  have hc' : d.s⁻¹ * c * d.s ∈ d.CB₄I₃ := by
    have := (mem_normalizer_iff.1 (inv_mem hsN) c).1 hc
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 (hd.CB₄I₃_le_centralizer_Z₂p hc') w hw
  change d.s * w * d.s⁻¹ * c = c * (d.s * w * d.s⁻¹)
  calc d.s * w * d.s⁻¹ * c = d.s * (w * (d.s⁻¹ * c * d.s)) * d.s⁻¹ := by group
    _ = d.s * ((d.s⁻¹ * c * d.s) * w) * d.s⁻¹ := by rw [e]
    _ = c * (d.s * w * d.s⁻¹) := by group

end Data

end CFSG.LocalAnalysis.EvenBN.U5

module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatSeries
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv

section Comm

variable {V : Type*} [CommGroup V]

@[expose] def altNatComm (a : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v => a v * v⁻¹) (fun x y => by simp only [map_mul, mul_inv_rev]; ac_rfl)

theorem altNatComm_apply (a : MulAut V) (v : V) : altNatComm a v = a v * v⁻¹ := rfl

theorem altNatComm_eq_one {a : MulAut V} {v : V} : altNatComm a v = 1 ↔ a v = v := by
  rw [altNatComm_apply, mul_inv_eq_one]

theorem altNat_comm_of_comm {l a : MulAut V} (h : l * a = a * l) (v : V) :
    l (altNatComm a v) = altNatComm a (l v) := by
  have h1 : a (l v) = l (a v) := (congrArg (fun f : MulAut V => f v) h).symm
  rw [altNatComm_apply, altNatComm_apply, h1]
  simp only [map_mul, map_inv]

end Comm

section Layer

variable {V : Type} [CommGroup V] [Finite V] {L A₀ : Subgroup (MulAut V)} {M : Subgroup V} {n : ℕ}

theorem altNat_layer_step1 (hodd : Odd n) (h5 : 5 ≤ n) (D : AltNatModule L M n)
    (hcomm : ∀ l ∈ L, ∀ a ∈ A₀, l * a = a * l)
    (hII : ∀ B : Subgroup (MulAut V), B ≤ A₀ →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card A₀ * Nat.card (fixV A₀))
    (hMF : ∀ m ∈ M, ∀ a ∈ A₀, a m = m)
    (hFM : ∀ f ∈ fixV A₀, ∀ l ∈ L, l f * f⁻¹ ∈ M) :
    ∀ v ∈ altNatF A₀ 1, ∀ l ∈ L, l v * v⁻¹ ∈ altNatF A₀ 0 := by
  classical
  let Z : Subgroup V := altNatF A₀ 1 ⊓ altNatStep A₀ M
  have hF0Z : altNatF A₀ 0 ≤ Z := fun f hf =>
    ⟨altNatF_mono A₀ 0 hf, fun a ha => by
      rw [(mem_altNatF_zero.1 hf) a ha, mul_inv_cancel]; exact M.one_mem⟩
  have hZL : ∀ l ∈ L, ∀ u ∈ Z, l u ∈ Z := by
    intro l hl u hu
    refine ⟨altNatF_of_comm hcomm 1 l hl u hu.1, fun a ha => ?_⟩
    have := altNat_comm_of_comm (hcomm l hl a ha) u
    rw [altNatComm_apply, altNatComm_apply] at this
    rw [← this]
    exact D.inv l hl _ (hu.2 a ha)
  have hZ : ∀ v ∈ altNatF A₀ 1, ∀ l ∈ L, l v * v⁻¹ ∈ Z := by
    intro v hv l hl
    have hc : ∀ a ∈ A₀, a (l v * v⁻¹) * (l v * v⁻¹)⁻¹ ∈ M := by
      intro a ha
      have hca : a v * v⁻¹ ∈ fixV A₀ := hv a ha
      have h1 := hFM _ hca l hl
      have e : a (l v * v⁻¹) * (l v * v⁻¹)⁻¹ = l (a v * v⁻¹) * (a v * v⁻¹)⁻¹ := by
        have h2 : a (l v) = l (a v) :=
          (congrArg (fun f : MulAut V => f v) (hcomm l hl a ha)).symm
        simp only [map_mul, map_inv, mul_inv_rev, inv_inv, h2]
        ac_rfl
      rw [e]; exact h1
    exact ⟨mem_altNatF_succ.2 fun a ha => mem_altNatF_zero.2 fun b hb => hMF _ (hc a ha) b hb, hc⟩
  suffices hZF : Z ≤ altNatF A₀ 0 from fun v hv l hl => hZF (hZ v hv l hl)
  by_contra hnot
  let 𝒮 : Set (Subgroup V) := {Y | altNatF A₀ 0 < Y ∧ Y ≤ Z ∧ ∀ l ∈ L, ∀ y ∈ Y, l y ∈ Y}
  have hZ𝒮 : Z ∈ 𝒮 :=
    ⟨lt_of_le_of_ne hF0Z fun h => hnot (le_of_eq h.symm), le_rfl, hZL⟩
  obtain ⟨Y, ⟨hF0Y, hYZ, hYL⟩, hYmin⟩ :=
    Set.exists_min_image 𝒮 (fun Y => Nat.card Y) (Set.toFinite 𝒮) ⟨Z, hZ𝒮⟩
  obtain ⟨y₁, hy₁Y, hy₁F⟩ := SetLike.exists_of_lt hF0Y
  obtain ⟨a₁, ha₁, ha₁y⟩ : ∃ a₁ ∈ A₀, a₁ y₁ ≠ y₁ := by
    by_contra hcon
    push Not at hcon
    exact hy₁F (mem_altNatF_zero.2 hcon)
  let K₁ : Subgroup V := Y ⊓ (altNatComm a₁).ker
  have hF0K₁ : altNatF A₀ 0 ≤ K₁ := fun f hf =>
    Subgroup.mem_inf.2 ⟨hF0Y.le hf, MonoidHom.mem_ker.2
      (altNatComm_eq_one.2 ((mem_altNatF_zero.1 hf) a₁ ha₁))⟩
  have hK₁L : ∀ l ∈ L, ∀ k ∈ K₁, l k ∈ K₁ := by
    intro l hl k hk
    have hk' := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨hYL l hl k hk'.1, MonoidHom.mem_ker.2 ?_⟩
    rw [← altNat_comm_of_comm (hcomm l hl a₁ ha₁), MonoidHom.mem_ker.1 hk'.2, map_one]
  have hK₁Y : K₁ < Y := by
    refine lt_of_le_of_ne inf_le_left fun h => ha₁y ?_
    have : y₁ ∈ K₁ := by rw [h]; exact hy₁Y
    exact altNatComm_eq_one.1 (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 this).2)
  have hK₁F : K₁ ≤ altNatF A₀ 0 := by
    by_contra hnle
    have hmem : K₁ ∈ 𝒮 :=
      ⟨lt_of_le_of_ne hF0K₁ fun h => hnle (le_of_eq h.symm), hK₁Y.le.trans hYZ, hK₁L⟩
    exact absurd (Subgroup.card_lt_of_lt hK₁Y) (not_lt.2 (hYmin K₁ hmem))
  have hYM : ∀ a ∈ A₀, ∀ y : ↥Y, altNatComm a (y : V) ∈ M := fun a ha y => (hYZ y.2).2 a ha
  let Ψ : ∀ a ∈ A₀, ↥Y →* ↥M := fun a ha =>
    ((altNatComm a).comp Y.subtype).codRestrict M (hYM a ha)
  have hΨ : ∀ a (ha : a ∈ A₀) (y : ↥Y), ((Ψ a ha y : ↥M) : V) = a (y : V) * (y : V)⁻¹ :=
    fun _ _ _ => rfl
  have hΨ₁ : Function.Surjective (Ψ a₁ ha₁) := by
    let I : Subgroup V := Y.map (altNatComm a₁)
    have hIM : I ≤ M := by rintro _ ⟨y, hy, rfl⟩; exact hYM a₁ ha₁ ⟨y, hy⟩
    have hIL : ∀ l ∈ L, ∀ x ∈ I, l x ∈ I := by
      rintro l hl _ ⟨y, hy, rfl⟩
      exact ⟨l y, hYL l hl y hy, (altNat_comm_of_comm (hcomm l hl a₁ ha₁) y).symm⟩
    have hIbot : I ≠ ⊥ := by
      intro h
      have : altNatComm a₁ y₁ ∈ I := ⟨y₁, hy₁Y, rfl⟩
      rw [h, Subgroup.mem_bot, altNatComm_eq_one] at this
      exact ha₁y this
    have hIM' : I = M := (D.simple hodd (by omega) I hIM hIL).resolve_left hIbot
    intro m
    have : (m : V) ∈ I := by rw [hIM']; exact m.2
    obtain ⟨y, hy, hym⟩ := this
    exact ⟨⟨y, hy⟩, Subtype.ext hym⟩
  have hkerΨ₁ : (Ψ a₁ ha₁).ker = (altNatF A₀ 0).subgroupOf Y := by
    ext y
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : altNatComm a₁ (y : V) = 1 := congrArg Subtype.val h
      exact hK₁F (Subgroup.mem_inf.2 ⟨y.2, MonoidHom.mem_ker.2 h1⟩)
    · intro h
      apply Subtype.ext
      show altNatComm a₁ (y : V) = 1
      rw [altNatComm_eq_one]
      exact (mem_altNatF_zero.1 h) a₁ ha₁
  have hcard : Nat.card Y = Nat.card (altNatF A₀ 0) * Nat.card M := by
    have h1 := Subgroup.card_mul_index (Ψ a₁ ha₁).ker
    rw [Subgroup.index_ker, (MonoidHom.range_eq_top).2 hΨ₁, Subgroup.card_top, hkerΨ₁] at h1
    have h2 : Nat.card ↥((altNatF A₀ 0).subgroupOf Y) = Nat.card (altNatF A₀ 0) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF0Y.le).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hdich : ∀ a (ha : a ∈ A₀), (∀ y ∈ Y, a y = y) ∨ (∀ y ∈ Y, a y = a₁ y) := by
    intro a ha
    have hker : (Ψ a₁ ha₁).ker ≤ (Ψ a ha).ker := by
      intro y hy
      rw [hkerΨ₁, Subgroup.mem_subgroupOf] at hy
      apply MonoidHom.mem_ker.2
      apply Subtype.ext
      show altNatComm a (y : V) = 1
      rw [altNatComm_eq_one]
      exact (mem_altNatF_zero.1 hy) a ha
    let φ : ↥M →* ↥M := (MonoidHom.liftOfSurjective (Ψ a₁ ha₁) hΨ₁) ⟨Ψ a ha, hker⟩
    have hφ : ∀ y : ↥Y, φ (Ψ a₁ ha₁ y) = Ψ a ha y := fun y =>
      MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨Ψ a ha, hker⟩ y
    have hφL : ∀ (l : ↥L) (m : ↥M), φ (D.act l m) = D.act l (φ m) := by
      intro l m
      obtain ⟨y, rfl⟩ := hΨ₁ m
      have e1 : D.act l (Ψ a₁ ha₁ y) = Ψ a₁ ha₁ ⟨(l : MulAut V) y, hYL l l.2 y y.2⟩ := by
        apply Subtype.ext
        exact altNat_comm_of_comm (hcomm l l.2 a₁ ha₁) y
      have e2 : D.act l (Ψ a ha y) = Ψ a ha ⟨(l : MulAut V) y, hYL l l.2 y y.2⟩ := by
        apply Subtype.ext
        exact altNat_comm_of_comm (hcomm l l.2 a ha) y
      rw [e1, hφ, hφ, e2]
    rcases D.end_eq hodd h5 φ hφL with h | h
    · left
      intro y hy
      have h1 := congrArg Subtype.val (hφ ⟨y, hy⟩)
      rw [h] at h1
      have h2 : (1 : V) = a y * y⁻¹ := h1
      exact mul_inv_eq_one.1 h2.symm
    · right
      intro y hy
      have h1 := congrArg Subtype.val (hφ ⟨y, hy⟩)
      rw [h] at h1
      have h2 : a₁ y * y⁻¹ = a y * y⁻¹ := h1
      exact (mul_right_cancel h2).symm
  let H₀ : Subgroup (MulAut V) :=
    { carrier := {a | a ∈ A₀ ∧ ∀ y ∈ Y, a y = y}
      one_mem' := ⟨A₀.one_mem, fun y _ => rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨A₀.mul_mem ha.1 hb.1, fun y hy => by
        show a (b y) = y
        rw [hb.2 y hy, ha.2 y hy]⟩
      inv_mem' := fun {a} ha => ⟨A₀.inv_mem ha.1, fun y hy => by
        show a⁻¹ y = y
        conv_lhs => rw [← ha.2 y hy]
        exact MulAut.inv_apply_self V a y⟩ }
  have hH₀le : H₀ ≤ A₀ := fun a ha => ha.1
  have hidx : Nat.card A₀ ≤ 2 * Nat.card H₀ := by
    let H' : Subgroup ↥A₀ := H₀.subgroupOf A₀
    have h1 : H'.index * Nat.card H' = Nat.card A₀ := Subgroup.index_mul_card H'
    have h2 : Nat.card H' = Nat.card H₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀le).toEquiv
    have h3 : H'.index ≤ 2 := by
      rw [Subgroup.index_eq_card]
      let a₁' : ↥A₀ := ⟨a₁, ha₁⟩
      let f : Bool → ↥A₀ ⧸ H' := fun b => if b then QuotientGroup.mk 1 else QuotientGroup.mk a₁'
      have hf : Function.Surjective f := by
        intro q
        obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
        rcases hdich (g : MulAut V) g.2 with h | h
        · refine ⟨true, ?_⟩
          show (QuotientGroup.mk (1 : ↥A₀) : ↥A₀ ⧸ H') = QuotientGroup.mk g
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          refine ⟨by simp, fun y hy => ?_⟩
          simp [h y hy]
        · refine ⟨false, ?_⟩
          show (QuotientGroup.mk a₁' : ↥A₀ ⧸ H') = QuotientGroup.mk g
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          refine ⟨A₀.mul_mem (A₀.inv_mem ha₁) g.2, fun y hy => ?_⟩
          show a₁⁻¹ ((g : MulAut V) y) = y
          rw [h y hy]
          exact MulAut.inv_apply_self V a₁ y
      have := Nat.card_le_card_of_surjective f hf
      simpa using this
    rw [← h1, h2]
    exact Nat.mul_le_mul_right _ h3
  have hYfix : Y ≤ fixV H₀ := fun y hy b hb => hb.2 y hy
  have hcardY : Nat.card Y ≤ Nat.card (fixV H₀) := Subgroup.card_le_of_le hYfix
  have hII' := hII H₀ hH₀le
  have hpos : 0 < Nat.card H₀ := Nat.card_pos
  have hposF : 0 < Nat.card (altNatF A₀ 0) := Nat.card_pos
  have hM2 := D.two_lt_card hodd (by omega)
  have hF0 : Nat.card (altNatF A₀ 0) = Nat.card (fixV A₀) := rfl
  have h1 : Nat.card H₀ * Nat.card Y ≤ Nat.card H₀ * (2 * Nat.card (altNatF A₀ 0)) := by
    calc Nat.card H₀ * Nat.card Y ≤ Nat.card H₀ * Nat.card (fixV H₀) :=
          Nat.mul_le_mul_left _ hcardY
      _ ≤ Nat.card A₀ * Nat.card (fixV A₀) := hII'
      _ = Nat.card A₀ * Nat.card (altNatF A₀ 0) := by rw [hF0]
      _ ≤ (2 * Nat.card H₀) * Nat.card (altNatF A₀ 0) := Nat.mul_le_mul_right _ hidx
      _ = Nat.card H₀ * (2 * Nat.card (altNatF A₀ 0)) := by ring
  have h2 : Nat.card Y ≤ 2 * Nat.card (altNatF A₀ 0) := Nat.le_of_mul_le_mul_left h1 hpos
  rw [hcard] at h2
  have h3 : Nat.card M ≤ 2 := by
    have : Nat.card (altNatF A₀ 0) * Nat.card M ≤ Nat.card (altNatF A₀ 0) * 2 := by linarith
    exact Nat.le_of_mul_le_mul_left this hposF
  omega

theorem altNat_layer_step (hodd : Odd n) (h5 : 5 ≤ n) (D : AltNatModule L M n)
    (hcomm : ∀ l ∈ L, ∀ a ∈ A₀, l * a = a * l)
    (hII : ∀ B : Subgroup (MulAut V), B ≤ A₀ →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card A₀ * Nat.card (fixV A₀))
    (hMF : ∀ m ∈ M, ∀ a ∈ A₀, a m = m)
    (hFM : ∀ f ∈ fixV A₀, ∀ l ∈ L, l f * f⁻¹ ∈ M) :
    ∀ k : ℕ, ∀ v ∈ altNatF A₀ (k + 1), ∀ l ∈ L, l v * v⁻¹ ∈ altNatF A₀ k := by
  intro k
  induction k with
  | zero => exact altNat_layer_step1 hodd h5 D hcomm hII hMF hFM
  | succ k ih =>
    intro v hv l hl a ha
    have hc : a v * v⁻¹ ∈ altNatF A₀ (k + 1) := hv a ha
    have e : a (l v * v⁻¹) * (l v * v⁻¹)⁻¹ = l (a v * v⁻¹) * (a v * v⁻¹)⁻¹ := by
      have h2 : a (l v) = l (a v) :=
        (congrArg (fun f : MulAut V => f v) (hcomm l hl a ha)).symm
      simp only [map_mul, map_inv, mul_inv_rev, inv_inv, h2]
      ac_rfl
    rw [e]
    exact ih _ hc l hl

theorem altNat_layer_triv (hodd : Odd n) (h5 : 5 ≤ n) (hLperf : Group.IsPerfect ↥L)
    (D : AltNatModule L M n)
    (hcomm : ∀ l ∈ L, ∀ a ∈ A₀, l * a = a * l)
    (hII : ∀ B : Subgroup (MulAut V), B ≤ A₀ →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card A₀ * Nat.card (fixV A₀))
    (hMF : ∀ m ∈ M, ∀ a ∈ A₀, a m = m)
    (hFM : ∀ f ∈ fixV A₀, ∀ l ∈ L, l f * f⁻¹ ∈ M) :
    ∀ k : ℕ, ∀ v ∈ altNatF A₀ k, ∀ l ∈ L, l v * v⁻¹ ∈ altNatF A₀ 0 := by
  intro k
  induction k with
  | zero =>
    intro v hv l hl
    exact (altNatF A₀ 0).mul_mem (altNatF_of_comm hcomm 0 l hl v hv) ((altNatF A₀ 0).inv_mem hv)
  | succ k ih =>
    exact altNat_perf_step hLperf (altNat_layer_step hodd h5 D hcomm hII hMF hFM k) ih

theorem altNat_layer (hV2 : ∀ v : V, v ^ 2 = 1) (hodd : Odd n) (h5 : 5 ≤ n)
    (hLperf : Group.IsPerfect ↥L) (D : AltNatModule L M n)
    (hcomm : ∀ l ∈ L, ∀ a ∈ A₀, l * a = a * l) (hA₀ : IsPGroup 2 ↥A₀)
    (hII : ∀ B : Subgroup (MulAut V), B ≤ A₀ →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card A₀ * Nat.card (fixV A₀))
    (hMF : ∀ m ∈ M, ∀ a ∈ A₀, a m = m)
    (hFM : ∀ f ∈ fixV A₀, ∀ l ∈ L, l f * f⁻¹ ∈ M) :
    ∀ v : V, ∀ l ∈ L, l v * v⁻¹ ∈ fixV A₀ := by
  intro v l hl
  obtain ⟨k, hk⟩ := altNat_exists_mem_F hV2 hA₀ v
  exact altNat_layer_triv hodd h5 hLperf D hcomm hII hMF hFM k v hk l hl

end Layer

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

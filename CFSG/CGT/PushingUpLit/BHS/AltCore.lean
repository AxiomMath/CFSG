module

public import CFSG.CGT.PushingUpLit.BHS.SymNatNormalizer
public import CFSG.CGT.PushingUpLit.BHS.SymNatSplit
public import CFSG.CGT.PushingUpLit.BHS.SymNatOffender

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement

variable {n : ℕ}

theorem fixV_alt_map (hn : Odd n) (h3 : 3 ≤ n) :
    fixV ((alternatingGroup (Fin n)).map (coreAct n)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Subgroup.mem_bot]
  have hfix := mem_fixV_map_iff.mp hv
  have hconst : ∀ i j : Fin n, vcoord v j = vcoord v i := by
    intro i j
    obtain ⟨σ, hσ, hσi⟩ := exists_alt_apply_eq h3 i j
    have := hfix σ hσ i
    rwa [hσi] at this
  have hn0 : 0 < n := by omega
  set c := vcoord v ⟨0, hn0⟩ with hc
  have hsum : ∑ i, vcoord v i = (n : ZMod 2) * c := by
    simp [hconst ⟨0, hn0⟩, hc]
  have h0 := sum_vcoord v
  rw [hsum, hn.natCast_zmod_two, one_mul] at h0
  apply vcoord_ext
  intro i
  rw [hconst ⟨0, hn0⟩ i]
  exact h0.trans (vcoord_one i).symm

theorem eq_one_of_commute_alt (h4 : 4 ≤ n) {π : Equiv.Perm (Fin n)}
    (h : ∀ σ ∈ alternatingGroup (Fin n), π * σ = σ * π) : π = 1 := by
  classical
  refine Equiv.ext fun i => ?_
  rw [Equiv.Perm.one_apply]
  by_contra hne
  set j := π i with hj
  have hji : j ≠ i := hne
  have hcard : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hcard' : ({i, j, k} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
    have h2 : ({i, j, k} : Finset (Fin n)).card ≤ 3 := Finset.card_le_three
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard'
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
  have hjk : j ≠ k := fun h => hk.2 h.symm
  have hkl : k ≠ l := fun h => hl.2.2 h.symm
  have hjl : j ≠ l := fun h => hl.2.1 h.symm
  have hτ : Equiv.swap j k * Equiv.swap k l ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hjk,
      Equiv.Perm.sign_swap hkl]
    decide
  have h1 := congrArg (fun f : Equiv.Perm (Fin n) => f i) (h _ hτ)
  simp only [Equiv.Perm.mul_apply] at h1
  have hτi : Equiv.swap k l i = i := Equiv.swap_apply_of_ne_of_ne (fun h => hk.1 h.symm)
    (fun h => hl.1 h.symm)
  have hτi' : Equiv.swap j k i = i := Equiv.swap_apply_of_ne_of_ne (Ne.symm hji)
    (fun h => hk.1 h.symm)
  rw [hτi, hτi', ← hj] at h1
  have hτj : Equiv.swap j k (Equiv.swap k l j) = k := by
    rw [Equiv.swap_apply_of_ne_of_ne hjk hjl, Equiv.swap_apply_left]
  rw [hτj] at h1
  exact hjk h1

theorem exists_descent_mulEquiv {W D : Type*} [Group W] [Group D] (β : W →* D)
    (hβ : Function.Surjective β) (f : W ≃* W) (hf : ∀ w, β (f w) = 1 ↔ β w = 1) :
    ∃ y : D ≃* D, ∀ w, y (β w) = β (f w) := by
  have hmap : β.ker.map f.toMonoidHom = β.ker := by
    ext d
    simp only [Subgroup.mem_map, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hf w).2 hw
    · intro hd
      refine ⟨f.symm d, ?_, by simp⟩
      exact (hf (f.symm d)).1 (by rw [f.apply_symm_apply]; exact hd)
  let e1 := QuotientGroup.quotientKerEquivOfSurjective β hβ
  let e2 := QuotientGroup.congr β.ker β.ker f hmap
  refine ⟨e1.symm.trans (e2.trans e1), fun w => ?_⟩
  have h1 : e1.symm (β w) = (w : W ⧸ β.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  show e1 (e2 (e1.symm (β w))) = β (f w)
  rw [h1]
  rfl


section Core

variable {W : Type} [CommGroup W] [Finite W]

structure AltNatData (E : Subgroup (MulAut W)) (n : ℕ) where
  θ : E ≃* alternatingGroup (Fin n)
  β : W →* coreMod n
  surj : Function.Surjective β
  ker_fix : ∀ w : W, β w = 1 → w ∈ fixV E
  equivar : ∀ (e : E) (w : W), β ((e : MulAut W) w) =
    coreAct n ((θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) (β w)
  comm_top : commV E = ⊤

variable {E A : Subgroup (MulAut W)} {n : ℕ} (D : AltNatData E n)

omit [Finite W] in
theorem AltNatData.ker_iff (hn : Odd n) (h3 : 3 ≤ n) (w : W) : D.β w = 1 ↔ w ∈ fixV E := by
  refine ⟨D.ker_fix w, fun hw => ?_⟩
  have : D.β w ∈ fixV ((alternatingGroup (Fin n)).map (coreAct n)) := by
    intro g hg
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨e, he⟩ := D.θ.surjective ⟨σ, hσ⟩
    have h1 := D.equivar e w
    rw [he] at h1
    have h2 : (e : MulAut W) w = w := hw e e.2
    rw [h2] at h1
    exact h1.symm
  rw [fixV_alt_map hn h3] at this
  exact this

omit [Finite W] in
theorem mem_fixV_normalizer_iff {x : MulAut W} (hx : x ∈ Subgroup.normalizer (E : Set (MulAut W)))
    (w : W) : x w ∈ fixV E ↔ w ∈ fixV E := by
  have key : ∀ y : MulAut W, y ∈ Subgroup.normalizer (E : Set (MulAut W)) → ∀ w : W,
      w ∈ fixV E → y w ∈ fixV E := by
    intro y hy w hw e he
    have he' : y⁻¹ * e * y ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hy) e).mp he
      simpa using this
    have h1 : (y⁻¹ * e * y) w = w := hw _ he'
    have : e (y w) = y w := by
      have h2 : y ((y⁻¹ * e * y) w) = y w := by rw [h1]
      simpa [MulAut.mul_apply] using h2
    exact this
  refine ⟨fun h => ?_, key x hx w⟩
  have := key x⁻¹ ((Subgroup.normalizer _).inv_mem hx) (x w) h
  simpa using this

omit [Finite W] in
theorem AltNatData.exists_act (hn : Odd n) (h3 : 3 ≤ n) {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (E : Set (MulAut W))) :
    ∃ y : coreMod n ≃* coreMod n, ∀ w, y (D.β w) = D.β (x w) := by
  refine exists_descent_mulEquiv D.β D.surj x fun w => ?_
  rw [D.ker_iff hn h3, D.ker_iff hn h3]
  exact mem_fixV_normalizer_iff hx w


omit [Finite W] in
theorem AltNatData.exists_perm (hn : Odd n) (h5 : 5 ≤ n) {x : MulAut W}
    (hx : x ∈ Subgroup.normalizer (E : Set (MulAut W))) :
    ∃ π : Equiv.Perm (Fin n), ∀ w, D.β (x w) = coreAct n π (D.β w) := by
  have h3 : 3 ≤ n := by omega
  obtain ⟨y, hy⟩ := D.exists_act hn h3 hx
  have hxE : ∀ e : E, x * (e : MulAut W) * x⁻¹ ∈ E := fun e =>
    (Subgroup.mem_normalizer_iff.mp hx e).mp e.2
  have hxE' : ∀ e : E, x⁻¹ * (e : MulAut W) * x ∈ E := fun e => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hx) e).mp e.2
    simpa using this
  have hk : ∀ (e : E) (w : W), y (coreAct n ((D.θ e : alternatingGroup (Fin n)) :
      Equiv.Perm (Fin n)) (D.β w)) = coreAct n ((D.θ ⟨x * (e : MulAut W) * x⁻¹, hxE e⟩ :
      alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) (y (D.β w)) := by
    intro e w
    rw [← D.equivar e w, hy, hy, ← D.equivar ⟨x * (e : MulAut W) * x⁻¹, hxE e⟩ (x w)]
    simp [MulAut.mul_apply]
  obtain ⟨π, hπ⟩ := exists_perm_of_normalizes_alt hn h5 y
    (fun σ hσ => by
      obtain ⟨e, he⟩ := D.θ.surjective ⟨σ, hσ⟩
      refine ⟨_, (D.θ ⟨x * (e : MulAut W) * x⁻¹, hxE e⟩).2, fun d => ?_⟩
      obtain ⟨w, rfl⟩ := D.surj d
      have := hk e w
      rw [he] at this
      exact this)
    (fun σ' hσ' => by
      obtain ⟨e', he'⟩ := D.θ.surjective ⟨σ', hσ'⟩
      refine ⟨((D.θ ⟨x⁻¹ * (e' : MulAut W) * x, hxE' e'⟩ : alternatingGroup (Fin n)) :
        Equiv.Perm (Fin n)), (D.θ ⟨x⁻¹ * (e' : MulAut W) * x, hxE' e'⟩).2, fun d => ?_⟩
      obtain ⟨w, rfl⟩ := D.surj d
      have h1 : x ((x⁻¹ * (e' : MulAut W) * x) w) = (e' : MulAut W) (x w) := by
        simp [MulAut.mul_apply]
      rw [← D.equivar ⟨x⁻¹ * (e' : MulAut W) * x, hxE' e'⟩ w, hy, hy]
      show D.β (x ((x⁻¹ * (e' : MulAut W) * x) w)) = _
      rw [h1, D.equivar e' (x w), he'])
  exact ⟨π, fun w => by rw [← hy, hπ]⟩


omit [Finite W] in
theorem AltNatData.perm_unique (h3 : 3 ≤ n) {π π' : Equiv.Perm (Fin n)}
    (h : ∀ w, coreAct n π (D.β w) = coreAct n π' (D.β w)) : π = π' :=
  coreAct_injective h3 (MulEquiv.ext fun d => by obtain ⟨w, rfl⟩ := D.surj d; exact h w)

@[expose] noncomputable def AltNatData.psiFun (hn : Odd n) (h5 : 5 ≤ n)
    (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) : Equiv.Perm (Fin n) :=
  Classical.choose (D.exists_perm hn h5 x.2)

omit [Finite W] in
theorem AltNatData.psiFun_spec (hn : Odd n) (h5 : 5 ≤ n)
    (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (w : W) :
    D.β ((x : MulAut W) w) = coreAct n (D.psiFun hn h5 x) (D.β w) :=
  Classical.choose_spec (D.exists_perm hn h5 x.2) w

@[expose] noncomputable def AltNatData.psi (hn : Odd n) (h5 : 5 ≤ n) :
    ↥(Subgroup.normalizer (E : Set (MulAut W))) →* Equiv.Perm (Fin n) :=
  MonoidHom.mk' (D.psiFun hn h5) fun a b => by
    apply D.perm_unique (by omega)
    intro w
    have h1 := D.psiFun_spec hn h5 (a * b) w
    have h2 := D.psiFun_spec hn h5 a ((b : MulAut W) w)
    have h3 := D.psiFun_spec hn h5 b w
    rw [← h1, map_mul, MulAut.mul_apply, ← h3, ← h2]
    rfl

omit [Finite W] in
theorem AltNatData.psi_spec (hn : Odd n) (h5 : 5 ≤ n)
    (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (w : W) :
    D.β ((x : MulAut W) w) = coreAct n (D.psi hn h5 x) (D.β w) :=
  D.psiFun_spec hn h5 x w

omit [Finite W] in
theorem AltNatData.psi_of_mem (hn : Odd n) (h5 : 5 ≤ n) (e : E) :
    D.psi hn h5 ⟨(e : MulAut W), Subgroup.le_normalizer e.2⟩ =
      ((D.θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  apply D.perm_unique (by omega)
  intro w
  rw [← D.psi_spec hn h5, D.equivar]


omit [Finite W] in
theorem AltNatData.commute_of_psi_eq_one (hn : Odd n) (h5 : 5 ≤ n)
    {x : ↥(Subgroup.normalizer (E : Set (MulAut W)))} (hx : D.psi hn h5 x = 1) {e : MulAut W}
    (he : e ∈ E) : (x : MulAut W) * e = e * (x : MulAut W) := by
  have hxE : (x : MulAut W) * e * (x : MulAut W)⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp x.2 e).mp he
  have htriv : ∀ w, D.β ((x : MulAut W) w) = D.β w := fun w => by
    rw [D.psi_spec hn h5, hx]
    rfl
  have hinv : ∀ w, D.β ((x : MulAut W)⁻¹ w) = D.β w := fun w => by
    have := htriv ((x : MulAut W)⁻¹ w)
    rw [show (x : MulAut W) ((x : MulAut W)⁻¹ w) = w by simp] at this
    exact this.symm
  have h1 : D.θ ⟨(x : MulAut W) * e * (x : MulAut W)⁻¹, hxE⟩ = D.θ ⟨e, he⟩ := by
    apply Subtype.ext
    apply D.perm_unique (by omega)
    intro w
    rw [← D.equivar ⟨(x : MulAut W) * e * (x : MulAut W)⁻¹, hxE⟩ w]
    rw [← D.equivar ⟨e, he⟩ w]
    show D.β ((x : MulAut W) (e ((x : MulAut W)⁻¹ w))) = D.β (e w)
    rw [htriv, D.equivar ⟨e, he⟩, hinv]
    exact (D.equivar ⟨e, he⟩ w).symm
  have h2 := D.θ.injective h1
  have h3 : (x : MulAut W) * e * (x : MulAut W)⁻¹ = e := congrArg Subtype.val h2
  calc (x : MulAut W) * e = (x : MulAut W) * e * (x : MulAut W)⁻¹ * (x : MulAut W) := by group
    _ = e * (x : MulAut W) := by rw [h3]

omit [Finite W] in
theorem AltNatData.psi_eq_one_of_commute (hn : Odd n) (h5 : 5 ≤ n)
    {x : ↥(Subgroup.normalizer (E : Set (MulAut W)))}
    (hx : ∀ e ∈ E, (x : MulAut W) * e = e * (x : MulAut W)) : D.psi hn h5 x = 1 := by
  apply eq_one_of_commute_alt (by omega)
  intro σ hσ
  obtain ⟨e, he⟩ := D.θ.surjective ⟨σ, hσ⟩
  apply D.perm_unique (by omega)
  intro w
  have h1 : coreAct n σ (D.β w) = D.β ((e : MulAut W) w) := by
    rw [D.equivar, he]
  rw [map_mul, MulAut.mul_apply, map_mul, MulAut.mul_apply, h1, ← D.psi_spec hn h5,
    ← D.psi_spec hn h5 x w]
  have h2 : ((x : MulAut W) * (e : MulAut W)) w = ((e : MulAut W) * (x : MulAut W)) w := by
    rw [hx e e.2]
  rw [MulAut.mul_apply, MulAut.mul_apply] at h2
  rw [h2, D.equivar, he]


omit [Finite W] in
theorem AltNatData.eq_one_of_psi_eq_one (hn : Odd n) (h5 : 5 ≤ n)
    {x : ↥(Subgroup.normalizer (E : Set (MulAut W)))} (hx : D.psi hn h5 x = 1) :
    (x : MulAut W) = 1 := by
  have hcomm := fun e he => D.commute_of_psi_eq_one hn h5 hx (e := e) he
  have htriv : ∀ w, D.β ((x : MulAut W) w) = D.β w := fun w => by
    rw [D.psi_spec hn h5, hx]
    rfl
  let K : Subgroup W :=
    { carrier := {w | (x : MulAut W) w = w}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [map_inv, ha] }
  have hle : commV E ≤ K := by
    unfold commV
    rw [Subgroup.closure_le]
    rintro _ ⟨e, he, w, rfl⟩
    have hφ : (x : MulAut W) w * w⁻¹ ∈ fixV E := by
      rw [← D.ker_iff hn (by omega), map_mul, map_inv, htriv]
      exact mul_inv_cancel _
    have hex : (x : MulAut W) (e w) = e ((x : MulAut W) w) := by
      have := hcomm e he
      exact congrArg (fun f : MulAut W => f w) this
    set φ := (x : MulAut W) w * w⁻¹ with hφdef
    have hxw : (x : MulAut W) w = φ * w := by rw [hφdef]; simp
    show (x : MulAut W) (e w * w⁻¹) = e w * w⁻¹
    have hef : e φ = φ := hφ e he
    calc (x : MulAut W) (e w * w⁻¹) = e ((x : MulAut W) w) * ((x : MulAut W) w)⁻¹ := by
          rw [map_mul, map_inv, hex]
      _ = (φ * e w) * (φ * w)⁻¹ := by rw [hxw, map_mul, hef]
      _ = e w * w⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]
  have htop : ∀ w : W, (x : MulAut W) w = w := fun w => by
    have : w ∈ K := hle (by rw [D.comm_top]; exact Subgroup.mem_top w)
    exact this
  exact MulEquiv.ext fun w => htop w


omit [Finite W] in
theorem AltNatData.psi_injective (hn : Odd n) (h5 : 5 ≤ n) : Function.Injective (D.psi hn h5) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact Subtype.ext (D.eq_one_of_psi_eq_one hn h5 hx)

theorem AltNatData.card_le_offender (hn : Odd n) (h5 : 5 ≤ n)
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut W)))
    (hAw : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) :
    Nat.card (coreMod n) ≤
      Nat.card ((A.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map
        (D.psi hn h5)) *
      Nat.card (fixV (((A.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map
        (D.psi hn h5)).map (coreAct n))) := by
  set N := Subgroup.normalizer (E : Set (MulAut W)) with hN
  set B := (A.subgroupOf N).map (D.psi hn h5) with hB
  set P : Subgroup W := fixV A with hP
  set C := fixV (B.map (coreAct n)) with hC
  have hBA : Nat.card B = Nat.card A := by
    rw [hB, Subgroup.card_map_of_injective (D.psi_injective hn h5)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have hPC : P.map D.β ≤ C := by
    rintro _ ⟨w, hw, rfl⟩ g hg
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hσ
    have hfix : (a : MulAut W) w = w := hw a (Subgroup.mem_subgroupOf.mp ha)
    have h := D.psi_spec hn h5 a w
    rw [hfix] at h
    exact h.symm
  have h1 : (P.map D.β).index ≤ P.index := by
    rw [Subgroup.index_map, MonoidHom.range_eq_top.mpr D.surj, Subgroup.index_top, mul_one]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le le_sup_left)
  have h2 : C.index ≤ (P.map D.β).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hPC)
  have h3 : Nat.card C * C.index = Nat.card (coreMod n) := Subgroup.card_mul_index C
  have h4 : Nat.card P * P.index = Nat.card W := Subgroup.card_mul_index P
  have hPpos : 0 < Nat.card P := Nat.card_pos
  have h5' : P.index ≤ Nat.card A := by
    have : Nat.card P * P.index ≤ Nat.card P * Nat.card A := by
      rw [h4, mul_comm (Nat.card P)]
      exact hAw
    exact Nat.le_of_mul_le_mul_left this hPpos
  rw [hBA, ← h3, mul_comm (Nat.card A)]
  exact Nat.mul_le_mul_left _ (h2.trans (h1.trans h5'))


end Core

theorem sym_offender_generated_weak (n : ℕ) (hn : Odd n) (h3 : 3 ≤ n)
    {A : Subgroup (Equiv.Perm (Fin n))} (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hge : Nat.card (coreMod n) ≤ Nat.card A * Nat.card (fixV (A.map (coreAct n)))) :
    (∃ T : Set (Equiv.Perm (Fin n)), (∀ t ∈ T, t.IsSwap) ∧
        (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧ A = Subgroup.closure T) ∧
      IsQuadratic (A.map (coreAct n)) ∧
      Nat.card (coreMod n) =
        Nat.card (A.map (coreAct n)) * Nat.card (fixV (A.map (coreAct n))) := by
  have hinj := coreAct_injective h3
  have hcardmap : Nat.card (A.map (coreAct n)) = Nat.card A := Subgroup.card_map_of_injective hinj
  obtain ⟨h2, hcard, hweq⟩ := weight_eq_of_ge hn hc hge
  refine ⟨⟨{t | t ∈ A ∧ t.IsSwap}, fun t ht => ht.2, fun t ht t' ht' => hc t ht.1 t' ht'.1,
    eq_closure_swaps fun x y hxy hmem => swap_mem_of_card_eq_prod hc h2 hcard hxy hmem⟩,
    isQuadratic_of_orbSize_le_two h2, ?_⟩
  rw [hcardmap]
  exact hweq.symm


section CoreMain

variable {W : Type} [CommGroup W] [Finite W] {E A : Subgroup (MulAut W)} {n : ℕ}

theorem alt_core (hW : ∀ w : W, w ^ 2 = 1) (hn : Odd n) (h5 : 5 ≤ n) (D : AltNatData E n)
    (hAN : A ≤ Subgroup.normalizer (E : Set (MulAut W))) (hA : IsElemAbelian2 A)
    (hAw : Nat.card W ≤ Nat.card A * Nat.card (fixV A)) (hEA : ⁅E, A⁆ ≠ ⊥) :
    fixV E = ⊥ ∧
      ∃ θX : ↥(E ⊔ A) ≃* Equiv.Perm (Fin n),
        (∀ e : E, θX ⟨e, Subgroup.mem_sup_left e.2⟩ =
          ((D.θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n))) ∧
        (∀ (x : ↥(E ⊔ A)) (w : W), D.β ((x : MulAut W) w) = coreAct n (θX x) (D.β w)) ∧
        (∃ T : Set (Equiv.Perm (Fin n)), T.Nonempty ∧ (∀ t ∈ T, t.IsSwap) ∧
          (∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t) ∧
          (A.subgroupOf (E ⊔ A)).map θX.toMonoidHom = Subgroup.closure T) ∧
        IsQuadratic A ∧ Nat.card W = Nat.card A * Nat.card (fixV A) := by
  have h3 : 3 ≤ n := by omega
  set N := Subgroup.normalizer (E : Set (MulAut W)) with hN
  have hXN : E ⊔ A ≤ N := sup_le Subgroup.le_normalizer hAN
  let ψX : ↥(E ⊔ A) →* Equiv.Perm (Fin n) := (D.psi hn h5).comp (Subgroup.inclusion hXN)
  have hψX_inj : Function.Injective ψX :=
    (D.psi_injective hn h5).comp (Subgroup.inclusion_injective hXN)
  set B := (A.subgroupOf N).map (D.psi hn h5) with hB
  have hcB : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy))
  obtain ⟨⟨T, hTswap, hTcomm, hBT⟩, hquad, hcard⟩ :=
    sym_offender_generated_weak n hn h3 hcB (D.card_le_offender hn h5 hAN hAw)
  have hTne : T.Nonempty := by
    by_contra hT
    rw [Set.not_nonempty_iff_eq_empty] at hT
    apply hEA
    rw [hT, Subgroup.closure_empty] at hBT
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro e he a ha
    have hpsi : D.psi hn h5 ⟨a, hAN ha⟩ = 1 := by
      have : D.psi hn h5 ⟨a, hAN ha⟩ ∈ B := ⟨_, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      rw [hBT] at this
      exact this
    have hcomm := D.commute_of_psi_eq_one hn h5 hpsi he
    rw [Subgroup.mem_bot]
    exact (commutatorElement_eq_one_iff_mul_comm).mpr hcomm.symm
  obtain ⟨t, htT⟩ := hTne
  have htB : t ∈ B := by rw [hBT]; exact Subgroup.subset_closure htT
  obtain ⟨y, hy, hyt⟩ := htB
  have hsign : Equiv.Perm.sign t = -1 := (hTswap t htT).sign_eq
  have hyA : (y : MulAut W) ∈ A := Subgroup.mem_subgroupOf.mp hy
  have hψX_surj : Function.Surjective ψX := by
    intro σ
    by_cases hσ : σ ∈ alternatingGroup (Fin n)
    · obtain ⟨e, he⟩ := D.θ.surjective ⟨σ, hσ⟩
      refine ⟨⟨e, Subgroup.mem_sup_left e.2⟩, ?_⟩
      show D.psi hn h5 ⟨(e : MulAut W), Subgroup.le_normalizer e.2⟩ = σ
      rw [D.psi_of_mem hn h5, he]
    · have hσt : σ * t ∈ alternatingGroup (Fin n) := by
        rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, hsign]
        have : Equiv.Perm.sign σ = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
          · exact absurd ((Equiv.Perm.mem_alternatingGroup).mpr h) hσ
          · exact h
        rw [this]
        decide
      obtain ⟨e, he⟩ := D.θ.surjective ⟨σ * t, hσt⟩
      refine ⟨⟨e, Subgroup.mem_sup_left e.2⟩ * ⟨(y : MulAut W), Subgroup.mem_sup_right hyA⟩⁻¹,
        ?_⟩
      rw [map_mul, map_inv]
      have h1 : ψX ⟨e, Subgroup.mem_sup_left e.2⟩ = σ * t := by
        show D.psi hn h5 ⟨(e : MulAut W), Subgroup.le_normalizer e.2⟩ = σ * t
        rw [D.psi_of_mem hn h5, he]
      have h2 : ψX ⟨(y : MulAut W), Subgroup.mem_sup_right hyA⟩ = t := hyt
      rw [h1, h2]
      group
  let θX : ↥(E ⊔ A) ≃* Equiv.Perm (Fin n) := MulEquiv.ofBijective ψX ⟨hψX_inj, hψX_surj⟩
  have hθX_apply : ∀ x, θX x = D.psi hn h5 ⟨(x : MulAut W), hXN x.2⟩ := fun x => rfl
  have hBeq : (A.subgroupOf (E ⊔ A)).map θX.toMonoidHom = B := by
    ext σ
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : MulAut W), hXN x.2⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx),
        rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨(z : MulAut W), Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hz)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz), rfl⟩
  have hequi : ∀ (x : ↥(E ⊔ A)) (w : W),
      D.β ((x : MulAut W) w) = coreAct n (θX x) (D.β w) := fun x w => by
    rw [hθX_apply]
    exact D.psi_spec hn h5 ⟨(x : MulAut W), hXN x.2⟩ w
  have hθXE : ∀ e : E, θX ⟨e, Subgroup.mem_sup_left e.2⟩ =
      ((D.θ e : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := fun e => by
    rw [hθX_apply]
    exact D.psi_of_mem hn h5 e
  have hcomm_mem : ∀ w : W, w ∈ commV E := fun w => by rw [D.comm_top]; trivial
  have hβinj : Function.Injective D.β := by
    let SD : SymSplitData (E ⊔ A) E n :=
      { θ := θX
        β := D.β.comp (commV E).subtype
        surj := fun d => by
          obtain ⟨w, rfl⟩ := D.surj d
          exact ⟨⟨w, hcomm_mem w⟩, rfl⟩
        ker_fix := fun w hw => D.ker_fix (w : W) hw
        map_apply := fun x p hp => hequi x p
        apply_mem := fun x _ p _ => hcomm_mem _
        three_mem := fun σ hσ => by
          have hσA : σ ∈ alternatingGroup (Fin n) := hσ.mem_alternatingGroup
          obtain ⟨e, he⟩ := D.θ.surjective ⟨σ, hσA⟩
          have : θX.symm σ = ⟨e, Subgroup.mem_sup_left e.2⟩ := by
            apply θX.injective
            rw [MulEquiv.apply_symm_apply, hθXE, he]
          rw [this]
          exact e.2 }
    have hinj := SD.β_injective hW hn h3 (fun H hH e he => by
      have hσ : θX ⟨e, Subgroup.mem_sup_left he⟩ ∈
          Subgroup.closure {σ : Equiv.Perm (Fin n) | σ.IsThreeCycle} := by
        rw [Equiv.Perm.closure_three_cycles_eq_alternating, hθXE ⟨e, he⟩]
        exact (D.θ ⟨e, he⟩).2
      have hle : Subgroup.closure {σ : Equiv.Perm (Fin n) | σ.IsThreeCycle} ≤
          (H.subgroupOf (E ⊔ A)).map θX.toMonoidHom := by
        rw [Subgroup.closure_le]
        intro σ hσ
        exact ⟨θX.symm σ, Subgroup.mem_subgroupOf.2 (hH σ hσ), by simp⟩
      obtain ⟨z, hz, hzx⟩ := hle hσ
      have hz' : z = ⟨e, Subgroup.mem_sup_left he⟩ := θX.injective hzx
      rw [hz'] at hz
      exact Subgroup.mem_subgroupOf.mp hz)
    intro w₁ w₂ h
    have := hinj (a₁ := ⟨w₁, hcomm_mem w₁⟩) (a₂ := ⟨w₂, hcomm_mem w₂⟩) h
    exact congrArg Subtype.val this
  have hfix : fixV E = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    have h1 : D.β z = 1 := (D.ker_iff hn h3 z).mpr hz
    exact Subgroup.mem_bot.2 (hβinj (h1.trans (map_one D.β).symm))
  have hψa : ∀ (a : MulAut W) (ha : a ∈ A) (w : W),
      D.β (a w) = coreAct n (D.psi hn h5 ⟨a, hAN ha⟩) (D.β w) := fun a ha w =>
    D.psi_spec hn h5 ⟨a, hAN ha⟩ w
  refine ⟨hfix, θX, hθXE, hequi, ⟨T, ⟨t, htT⟩, hTswap, hTcomm, ?_⟩, ?_, ?_⟩
  · rw [hBeq, hBT]
  ·
    unfold IsQuadratic commV
    rw [Subgroup.closure_le]
    rintro _ ⟨a, ha, w, rfl⟩ a' ha'
    have hv : D.β (a w * w⁻¹) ∈ commV (B.map (coreAct n)) := by
      refine Subgroup.subset_closure ⟨coreAct n (D.psi hn h5 ⟨a, hAN ha⟩), ?_, D.β w, ?_⟩
      · exact Subgroup.mem_map_of_mem _ ⟨⟨a, hAN ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      · rw [map_mul, map_inv, hψa a ha w]
        rfl
    have hfixv : coreAct n (D.psi hn h5 ⟨a', hAN ha'⟩) (D.β (a w * w⁻¹)) = D.β (a w * w⁻¹) :=
      hquad hv _ (Subgroup.mem_map_of_mem _ ⟨⟨a', hAN ha'⟩, Subgroup.mem_subgroupOf.mpr ha', rfl⟩)
    apply hβinj
    rw [hψa a' ha' (a w * w⁻¹)]
    exact hfixv
  · have hCW : (fixV A).map D.β = fixV (B.map (coreAct n)) := by
      ext d
      constructor
      · rintro ⟨w, hw, rfl⟩ g hg
        obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hg
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hσ
        have hfix' : (a : MulAut W) w = w := hw a (Subgroup.mem_subgroupOf.mp ha)
        have h := D.psi_spec hn h5 a w
        rw [hfix'] at h
        exact h.symm
      · intro hd
        obtain ⟨w, rfl⟩ := D.surj d
        refine ⟨w, fun a ha => hβinj ?_, rfl⟩
        have := hd (coreAct n (D.psi hn h5 ⟨a, hAN ha⟩))
          (Subgroup.mem_map_of_mem _ ⟨⟨a, hAN ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩)
        rw [hψa a ha w]
        exact this
    have hWΔ : Nat.card W = Nat.card (coreMod n) :=
      Nat.card_congr (Equiv.ofBijective D.β ⟨hβinj, D.surj⟩)
    have hBA : Nat.card B = Nat.card A := by
      rw [hB, Subgroup.card_map_of_injective (D.psi_injective hn h5)]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    have h1 : Nat.card (B.map (coreAct n)) = Nat.card A := by
      rw [Subgroup.card_map_of_injective (coreAct_injective h3), hBA]
    have h2 : Nat.card (fixV (B.map (coreAct n))) = Nat.card (fixV A) := by
      rw [← hCW]
      exact Subgroup.card_map_of_injective hβinj
    rw [hWΔ, hcard, h1, h2]

end CoreMain

end CFSG.CGT.PushingUpLit.BHS

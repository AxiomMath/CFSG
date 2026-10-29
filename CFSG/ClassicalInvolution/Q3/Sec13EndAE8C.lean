module

public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8I
public import CFSG.ClassicalInvolution.Q3.Sec13RecogT8

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace AE8End

variable {Ω : Set (Subgroup G)} {u : G}

theorem ae8c_a6_zmod_eq {x y : ZMod 2} (h : x ≠ 0 ↔ y ≠ 0) : x = y := by
  revert x y
  decide

theorem ae8c_a6_perm_of_card {p q : Fin 6 → Prop} [DecidablePred p] [DecidablePred q]
    (h : Fintype.card {i // p i} = Fintype.card {i // q i}) :
    ∃ ρ : Equiv.Perm (Fin 6), (∀ i, p i ↔ q (ρ i)) ∧ Equiv.Perm.sign ρ = 1 := by
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Equiv.Perm (Fin 6), ∀ i, p i ↔ q (σ₀ i) := by
    let e : {i // p i} ≃ {i // q i} := Fintype.equivOfCardEq h
    refine ⟨e.extendSubtype, fun i => ⟨fun hi => e.extendSubtype_mem i hi, fun hi => ?_⟩⟩
    by_contra hpi
    exact e.extendSubtype_not_mem i hpi hi
  by_cases hs : Equiv.Perm.sign σ₀ = 1
  · exact ⟨σ₀, hσ₀, hs⟩
  have hneg : Equiv.Perm.sign σ₀ = -1 := (Int.units_eq_one_or _).resolve_left hs
  obtain ⟨a, b, hab, hpab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i => decide (p i)) (by simp)
  have hiff : p a ↔ p b := by simpa using hpab
  have hsw : ∀ i, p (Equiv.swap a b i) ↔ p i := by
    intro i
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · rw [h1]; exact hiff.symm
    · rw [h2]; exact hiff
    · exact Iff.rfl
  refine ⟨σ₀ * Equiv.swap a b, fun i => ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply]
    exact (hsw i).symm.trans (hσ₀ (Equiv.swap a b i))
  · rw [Equiv.Perm.sign_mul, hneg, Equiv.Perm.sign_swap hab]
    rfl

theorem ae8c_alt_transitive {v w : Fin 6 → ZMod 2} (hvw : wt v = wt w) :
    ∃ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ = 1 ∧ ∀ i, w i = v (σ.symm i) := by
  unfold wt at hvw
  have h : Fintype.card {i // w i ≠ 0} = Fintype.card {i // v i ≠ 0} := by
    simp only [Fintype.card_subtype]
    exact hvw.symm
  obtain ⟨ρ, hρ, hsign⟩ :=
    ae8c_a6_perm_of_card (p := fun i => w i ≠ 0) (q := fun i => v i ≠ 0) h
  have hsgn : Equiv.Perm.sign ρ.symm = 1 := by
    rw [Equiv.Perm.sign_symm]
    exact hsign
  refine ⟨ρ.symm, hsgn, fun i => ?_⟩
  rw [Equiv.symm_symm]
  exact ae8c_a6_zmod_eq (hρ i)

structure Coords (c : Chart Ω u) where
  e : ↥(zGroup Ω) ≃* Multiplicative (Fin 6 → ZMod 2)
  vec : ∀ (d : ↥(zGroup Ω)) (y : ↥(pSpan (Generic.centMembers Ω u))), (d : G) = (y : G) →
    (e d).toAdd = (c.ψ y : AE.Wr 6).vec
  act : ∀ (y : ↥(pSpan (Generic.centMembers Ω u))) (d d' : ↥(zGroup Ω)),
    (d' : G) = y * d * y⁻¹ →
      (e d').toAdd = fun i => (e d).toAdd ((c.ψ y : AE.Wr 6).perm.symm i)
  conj_Y : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
    (y' : G) = d * y * d⁻¹ →
      AE.mkQ 6 (c.ψ y' : AE.Wr 6) =
        AE.mkQ 6 (AE.Wr.ofVec (e d).toAdd) * AE.mkQ 6 (c.ψ y : AE.Wr 6) *
          (AE.mkQ 6 (AE.Wr.ofVec (e d).toAdd))⁻¹

@[expose] def ae8c_e1_act (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => x (σ.symm i)

@[expose] def ae8c_p1 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def ae8c_p2 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def ae8c_p3 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 3

theorem ae8c_e1_zmod2_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem ae8c_e1_zmod2_cancel (p q : ZMod 2) : p + q + p = q := by
  revert p q; decide

theorem ae8c_e1_zmod2_ne (a b : ZMod 2) (ha : a ≠ 0) (hb : b ≠ 0) : a + b = 0 := by
  revert a b; decide

theorem ae8c_e1_vec_self (v : Fin 6 → ZMod 2) : v + v = 0 := by
  funext i
  exact ae8c_e1_zmod2_self (v i)

theorem ae8c_e1_act_add (σ : Equiv.Perm (Fin 6)) (x y : Fin 6 → ZMod 2) :
    ae8c_e1_act σ (x + y) = ae8c_e1_act σ x + ae8c_e1_act σ y := rfl

theorem ae8c_e1_act_act (σ τ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2) :
    ae8c_e1_act σ (ae8c_e1_act τ x) = ae8c_e1_act (σ * τ) x := rfl

theorem ae8c_e1_act_zero_or_one (σ : Equiv.Perm (Fin 6)) {k : Fin 6 → ZMod 2}
    (hk : k = 0 ∨ k = fun _ => 1) : ae8c_e1_act σ k = k := by
  rcases hk with rfl | rfl
  · rfl
  · rfl

theorem ae8c_e1_conj_ofVec (a : AE.Wr 6) (x : Fin 6 → ZMod 2) :
    a * AE.Wr.ofVec x * a⁻¹ = AE.Wr.ofVec (ae8c_e1_act a.perm x) := by
  refine AE.Wr.ext (funext fun i => ?_) ?_
  · simp only [AE.Wr.mul_vec, AE.Wr.inv_vec, AE.Wr.mul_perm, AE.Wr.inv_perm, AE.Wr.ofVec,
      mul_one, Equiv.apply_symm_apply, ae8c_e1_act]
    exact ae8c_e1_zmod2_cancel _ _
  · simp [AE.Wr.mul_perm, AE.Wr.inv_perm, AE.Wr.ofVec]

theorem ae8c_e1_ofVec_mul (x y : Fin 6 → ZMod 2) :
    AE.Wr.ofVec x * AE.Wr.ofVec y = AE.Wr.ofVec (x + y) := by
  refine AE.Wr.ext (funext fun i => ?_) ?_
  · simp [AE.Wr.mul_vec, AE.Wr.ofVec]; rfl
  · simp [AE.Wr.mul_perm, AE.Wr.ofVec]

theorem ae8c_e1_ofVec_inv (x : Fin 6 → ZMod 2) : (AE.Wr.ofVec x)⁻¹ = AE.Wr.ofVec x := by
  refine AE.Wr.ext (funext fun i => ?_) ?_
  · simp [AE.Wr.inv_vec, AE.Wr.ofVec]
  · simp [AE.Wr.inv_perm, AE.Wr.ofVec]

theorem ae8c_e1_ofVec_eq_one_iff (z : Fin 6 → ZMod 2) : AE.Wr.ofVec z = 1 ↔ z = 0 :=
  ⟨fun h => congrArg AE.Wr.vec h, fun h => by subst h; rfl⟩

theorem ae8c_e1_ofVec_eq_allOnes_iff (z : Fin 6 → ZMod 2) :
    AE.Wr.ofVec z = AE.Wr.allOnes 6 ↔ z = fun _ => 1 :=
  ⟨fun h => congrArg AE.Wr.vec h, fun h => by subst h; rfl⟩

theorem ae8c_e1_mkQ_ofVec_eq_iff (x y : Fin 6 → ZMod 2) :
    AE.mkQ 6 (AE.Wr.ofVec x) = AE.mkQ 6 (AE.Wr.ofVec y) ↔
      x + y = 0 ∨ x + y = fun _ => 1 := by
  rw [AE.mkQ_eq_iff, ae8c_e1_ofVec_inv, ae8c_e1_ofVec_mul, ae8c_e1_ofVec_eq_one_iff,
    ae8c_e1_ofVec_eq_allOnes_iff]

theorem ae8c_e1_mkQ_ofVec_mul (x y : Fin 6 → ZMod 2) :
    AE.mkQ 6 (AE.Wr.ofVec x) * AE.mkQ 6 (AE.Wr.ofVec y) =
      AE.mkQ 6 (AE.Wr.ofVec (x + y)) := by
  rw [← map_mul, ae8c_e1_ofVec_mul]

theorem ae8c_e1_mkQ_ofVec_inv (x : Fin 6 → ZMod 2) :
    (AE.mkQ 6 (AE.Wr.ofVec x))⁻¹ = AE.mkQ 6 (AE.Wr.ofVec x) := by
  rw [← map_inv, ae8c_e1_ofVec_inv]

theorem ae8c_e1_mkQ_ofVec_one (x : Fin 6 → ZMod 2) (h : x = 0 ∨ x = fun _ => 1) :
    AE.mkQ 6 (AE.Wr.ofVec x) = 1 := by
  have h0 : AE.mkQ 6 (AE.Wr.ofVec x) = AE.mkQ 6 (AE.Wr.ofVec 0) := by
    rw [ae8c_e1_mkQ_ofVec_eq_iff]
    rcases h with rfl | rfl <;> simp
  have h1 : AE.Wr.ofVec (0 : Fin 6 → ZMod 2) = 1 := rfl
  rw [h0, h1, map_one]

theorem ae8c_e1_mkQ_ofVec_comm (σ : Equiv.Perm (Fin 6)) (x : Fin 6 → ZMod 2)
    (h : AE.mkQ 6 (AE.Wr.ofVec x) * AE.mkQ 6 (AE.Wr.ofPerm σ) =
      AE.mkQ 6 (AE.Wr.ofPerm σ) * AE.mkQ 6 (AE.Wr.ofVec x)) :
    ∃ c : ZMod 2, ∀ i, x (σ i) + x i = c := by
  rw [← map_mul, ← map_mul, AE.mkQ_eq_iff] at h
  have key : ∀ i, ((AE.Wr.ofVec x * AE.Wr.ofPerm σ)⁻¹ * (AE.Wr.ofPerm σ * AE.Wr.ofVec x)).vec i
      = x (σ i) + x i := by
    intro i
    simp [AE.Wr.mul_vec, AE.Wr.inv_vec, AE.Wr.ofVec, AE.Wr.ofPerm, AE.Wr.mul_perm,
      AE.Wr.inv_perm, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]
  rcases h with h | h
  · refine ⟨0, fun i => ?_⟩
    have h2 : ((AE.Wr.ofVec x * AE.Wr.ofPerm σ)⁻¹ * (AE.Wr.ofPerm σ * AE.Wr.ofVec x)).vec i
        = (1 : AE.Wr 6).vec i := by rw [h]
    rw [key] at h2
    exact h2
  · refine ⟨1, fun i => ?_⟩
    have h2 : ((AE.Wr.ofVec x * AE.Wr.ofPerm σ)⁻¹ * (AE.Wr.ofPerm σ * AE.Wr.ofVec x)).vec i
        = (AE.Wr.allOnes 6).vec i := by rw [h]
    rw [key] at h2
    exact h2

theorem ae8c_e1_fin_check : ∀ x : Fin 6 → ZMod 2,
    (∃ c : ZMod 2, ∀ i : Fin 6, x (ae8c_p1 i) + x i = c) →
    (∃ c : ZMod 2, ∀ i : Fin 6, x (ae8c_p2 i) + x i = c) →
    (∃ c : ZMod 2, ∀ i : Fin 6, x (ae8c_p3 i) + x i = c) →
    x = 0 ∨ x = fun _ => 1 := by
  decide +kernel

theorem ae8c_e1_sign_p : Equiv.Perm.sign ae8c_p1 = 1 ∧ Equiv.Perm.sign ae8c_p2 = 1 ∧
    Equiv.Perm.sign ae8c_p3 = 1 := by
  unfold ae8c_p1 ae8c_p2 ae8c_p3
  decide +kernel

theorem ae8c_e1_card_even : Nat.card {x : Fin 6 → ZMod 2 // ∑ i, x i = 0} = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem ae8c_e1_card_mult : Nat.card (Multiplicative (Fin 6 → ZMod 2)) = 64 := by
  rw [Nat.card_eq_fintype_card]
  simp

theorem ae8c_e1_ofVec_mem (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0) :
    AE.Wr.ofVec x ∈ AE.aeSub 6 :=
  AE.mem_aeSub.mpr ⟨hx, by simp [AE.Wr.ofVec]⟩

theorem ae8c_e1_ofPerm_mem (σ : Equiv.Perm (Fin 6)) (hσ : Equiv.Perm.sign σ = 1) :
    AE.Wr.ofPerm σ ∈ AE.aeSub 6 :=
  AE.mem_aeSub.mpr ⟨by simp [AE.Wr.wsum, AE.Wr.ofPerm], by simpa [AE.Wr.ofPerm] using hσ⟩

theorem ae8c_e1_exists_psi_ofPerm (c : Chart Ω u) (σ : Equiv.Perm (Fin 6))
    (hσ : Equiv.Perm.sign σ = 1) :
    ∃ z : ↥(pSpan (Generic.centMembers Ω u)), (c.ψ z : AE.Wr 6) = AE.Wr.ofPerm σ :=
  ⟨c.ψ.symm ⟨AE.Wr.ofPerm σ, ae8c_e1_ofPerm_mem σ hσ⟩, by simp⟩

theorem ae8c_e1_comm_aux {Γ : Type} [Group Γ] {T β m : Γ} (hz : β * m * β⁻¹ = T * m * T⁻¹) :
    T⁻¹ * β * m = m * (T⁻¹ * β) := by
  calc T⁻¹ * β * m = T⁻¹ * (β * m * β⁻¹) * β := by group
    _ = T⁻¹ * (T * m * T⁻¹) * β := by rw [hz]
    _ = m * (T⁻¹ * β) := by group

theorem ae8c_e1_eq_one_of_comm {Y M : Type} [Group Y] [Group M] (hY : commutator Y = ⊤)
    (f : Y →* M) (hf : ∀ a b : Y, Commute (f a) (f b)) (y : Y) : f y = 1 := by
  have hle : commutator Y ≤ f.ker := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hf a b
  have hy : y ∈ commutator Y := by
    rw [hY]
    exact Subgroup.mem_top y
  exact (MonoidHom.mem_ker).mp (hle hy)

theorem ae8c_e1_inv_comm {w d : G} (h : w * d = d * w) : w * d⁻¹ = d⁻¹ * w := by
  calc w * d⁻¹ = d⁻¹ * (d * w) * d⁻¹ := by group
    _ = d⁻¹ * (w * d) * d⁻¹ := by rw [h]
    _ = d⁻¹ * w := by group

theorem ae8c_e1_comm_of_T {T b : G} (hT : T = 1 ∨ T = u) (hb : b * u = u * b) :
    T * b = b * T := by
  rcases hT with rfl | rfl
  · simp
  · exact hb.symm

theorem ae8c_e1_comm_mul_aux {d a b Ta Tb : G} (hda : d * a * d⁻¹ = a * Ta)
    (hdb : d * b * d⁻¹ = b * Tb) (hcomm : Ta * b = b * Ta) :
    (a * b)⁻¹ * (d * (a * b) * d⁻¹) = Ta * Tb := by
  calc (a * b)⁻¹ * (d * (a * b) * d⁻¹) = b⁻¹ * a⁻¹ * ((d * a * d⁻¹) * (d * b * d⁻¹)) := by
        group
    _ = b⁻¹ * a⁻¹ * ((a * Ta) * (b * Tb)) := by rw [hda, hdb]
    _ = b⁻¹ * (Ta * b) * Tb := by group
    _ = b⁻¹ * (b * Ta) * Tb := by rw [hcomm]
    _ = Ta * Tb := by group

theorem ae8c_e1_zGroup_comm (H : End18.Hyp Ω) {a b : G} (ha : a ∈ zGroup Ω)
    (hb : b ∈ zGroup Ω) : a * b = b * a :=
  H.endHyp.zGroup_comm H.perp9 a ha b hb

theorem ae8c_e1_zGroup_sq (H : End18.Hyp Ω) {a : G} (ha : a ∈ zGroup Ω) : a * a = 1 :=
  H.endHyp.zGroup_mul_self H.perp9 a ha

theorem ae8c_e1_zGroup_conj (H : End18.Hyp Ω) (g : G) {x : G} (hx : x ∈ zGroup Ω) :
    g * x * g⁻¹ ∈ zGroup Ω := by
  have hx' : x ∈ Subgroup.closure {v : G | ∃ L ∈ Ω, IsUniqueInvolution L v} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem v hv =>
    obtain ⟨L, hL, hvL⟩ := hv
    refine Subgroup.subset_closure ?_
    exact ⟨conjSub g L, H.endHyp.thmD.hyp.conjInvariant g L hL, hvL.conj g⟩
  | one => simp
  | mul a b _ _ ha hb =>
    have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem ae8c_e1_u_mem (c : Chart Ω u) (H : End18.Hyp Ω) : u ∈ zGroup Ω := by
  have h := (Chart.mem_zGroup_iff c H ⟨u, c.mem⟩).mpr (by rw [c.u_eq]; rfl)
  exact h

theorem ae8c_e1_comm_u (c : Chart Ω u) (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω) :
    d * u = u * d :=
  ae8c_e1_zGroup_comm H hd (ae8c_e1_u_mem c H)

theorem ae8c_e1_Y_comm_u {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u)) :
    y * u = u * y := by
  have hC : pSpan (Generic.centMembers Ω u) ≤ Subgroup.centralizer ({u} : Set G) :=
    pSpan_le fun _ hL => hL.2
  exact Subgroup.mem_centralizer_singleton_iff.mp (hC hy)

theorem ae8c_e1_conjSub_centMembers (H : End18.Hyp Ω) {d : G} (hdu : d * u = u * d)
    {L : Subgroup G} (hL : L ∈ Generic.centMembers Ω u) :
    conjSub d L ∈ Generic.centMembers Ω u := by
  refine ⟨H.endHyp.thmD.hyp.conjInvariant d L hL.1, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 : d⁻¹ * x * d ∈ Subgroup.centralizer ({u} : Set G) := hL.2 hx
  rw [Subgroup.mem_centralizer_singleton_iff] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hdinvu : d⁻¹ * u = u * d⁻¹ := by
    rw [show d⁻¹ * u = d⁻¹ * (u * d) * d⁻¹ by group, ← hdu]
    group
  calc x * u = d * (d⁻¹ * x * d) * (d⁻¹ * u) := by group
    _ = d * (d⁻¹ * x * d) * (u * d⁻¹) := by rw [hdinvu]
    _ = d * ((d⁻¹ * x * d) * u) * d⁻¹ := by group
    _ = d * (u * (d⁻¹ * x * d)) * d⁻¹ := by rw [h1]
    _ = (d * u) * (d⁻¹ * x * d) * d⁻¹ := by group
    _ = (u * d) * (d⁻¹ * x * d) * d⁻¹ := by rw [hdu]
    _ = u * x := by group

theorem ae8c_e1_normalizes (c : Chart Ω u) (H : End18.Hyp Ω) {d : G} (hd : d ∈ zGroup Ω)
    {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u)) :
    d * y * d⁻¹ ∈ pSpan (Generic.centMembers Ω u) := by
  have hdu := ae8c_e1_comm_u c H hd
  have key : pSpan (Generic.centMembers Ω u) ≤
      (pSpan (Generic.centMembers Ω u)).comap (MulAut.conj d).toMonoidHom := by
    refine pSpan_le fun L hL => fun x hx => ?_
    exact le_pSpan (ae8c_e1_conjSub_centMembers H hdu hL) (conj_mem_conjSub hx)
  exact key hy

open scoped Classical in
@[expose] noncomputable def ae8c_e1_nu (c : Chart Ω u) (g : G) : Fin 6 → ZMod 2 :=
  if h : g ∈ pSpan (Generic.centMembers Ω u) then (c.ψ ⟨g, h⟩ : AE.Wr 6).vec else 0

theorem ae8c_e1_nu_Y (c : Chart Ω u) {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u)) :
    ae8c_e1_nu c y = (c.ψ ⟨y, hy⟩ : AE.Wr 6).vec := by
  unfold ae8c_e1_nu
  rw [dif_pos hy]

theorem ae8c_e1_psi_eq (c : Chart Ω u) {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u))
    (hperm : (c.ψ ⟨y, hy⟩ : AE.Wr 6).perm = 1) :
    (c.ψ ⟨y, hy⟩ : AE.Wr 6) = AE.Wr.ofVec (ae8c_e1_nu c y) := by
  rw [ae8c_e1_nu_Y c hy]
  exact AE.Wr.ext rfl hperm

theorem ae8c_e1_nu_sum (c : Chart Ω u) {y : G} (hy : y ∈ pSpan (Generic.centMembers Ω u)) :
    ∑ i, ae8c_e1_nu c y i = 0 := by
  rw [ae8c_e1_nu_Y c hy]
  exact (AE.mem_aeSub.mp (c.ψ ⟨y, hy⟩).2).1

theorem ae8c_e1_perm_of_mem (c : Chart Ω u) (H : End18.Hyp Ω) {y : G}
    (hy : y ∈ pSpan (Generic.centMembers Ω u)) (hyD : y ∈ zGroup Ω) :
    (c.ψ ⟨y, hy⟩ : AE.Wr 6).perm = 1 :=
  (Chart.mem_zGroup_iff c H ⟨y, hy⟩).mp hyD

theorem ae8c_e1_nu_mul (c : Chart Ω u) {a b : G} (ha : a ∈ pSpan (Generic.centMembers Ω u))
    (hb : b ∈ pSpan (Generic.centMembers Ω u)) (hperm : (c.ψ ⟨a, ha⟩ : AE.Wr 6).perm = 1) :
    ae8c_e1_nu c (a * b) = ae8c_e1_nu c a + ae8c_e1_nu c b := by
  have hab : a * b ∈ pSpan (Generic.centMembers Ω u) := mul_mem ha hb
  rw [ae8c_e1_nu_Y c hab, ae8c_e1_nu_Y c ha, ae8c_e1_nu_Y c hb]
  have key : (c.ψ ⟨a * b, hab⟩ : AE.Wr 6) =
      (c.ψ ⟨a, ha⟩ : AE.Wr 6) * (c.ψ ⟨b, hb⟩ : AE.Wr 6) := by
    rw [← Subgroup.coe_mul, ← map_mul]
    rfl
  rw [key]
  funext i
  simp [AE.Wr.mul_vec, hperm] <;> rfl

theorem ae8c_e1_perm_conj (c : Chart Ω u) {y a : G} (hy : y ∈ pSpan (Generic.centMembers Ω u))
    (ha : a ∈ pSpan (Generic.centMembers Ω u)) (hperm : (c.ψ ⟨a, ha⟩ : AE.Wr 6).perm = 1)
    (hyay : y * a * y⁻¹ ∈ pSpan (Generic.centMembers Ω u)) :
    (c.ψ ⟨y * a * y⁻¹, hyay⟩ : AE.Wr 6).perm = 1 := by
  have hYe : (⟨y * a * y⁻¹, hyay⟩ : ↥(pSpan (Generic.centMembers Ω u))) =
      ⟨y, hy⟩ * ⟨a, ha⟩ * ⟨y, hy⟩⁻¹ := rfl
  rw [hYe, map_mul, map_mul, map_inv]
  simp [AE.Wr.mul_perm, AE.Wr.inv_perm, hperm]

theorem ae8c_e1_nu_conj (c : Chart Ω u) {y a : G} (hy : y ∈ pSpan (Generic.centMembers Ω u))
    (ha : a ∈ pSpan (Generic.centMembers Ω u)) (hperm : (c.ψ ⟨a, ha⟩ : AE.Wr 6).perm = 1) :
    ae8c_e1_nu c (y * a * y⁻¹) =
      ae8c_e1_act (c.ψ ⟨y, hy⟩ : AE.Wr 6).perm (ae8c_e1_nu c a) := by
  have hyay : y * a * y⁻¹ ∈ pSpan (Generic.centMembers Ω u) :=
    mul_mem (mul_mem hy ha) (inv_mem hy)
  rw [ae8c_e1_nu_Y c hyay]
  have hYe : (⟨y * a * y⁻¹, hyay⟩ : ↥(pSpan (Generic.centMembers Ω u))) =
      ⟨y, hy⟩ * ⟨a, ha⟩ * ⟨y, hy⟩⁻¹ := rfl
  have h1 : (c.ψ ⟨y * a * y⁻¹, hyay⟩ : AE.Wr 6) =
      (c.ψ ⟨y, hy⟩ : AE.Wr 6) * (c.ψ ⟨a, ha⟩ : AE.Wr 6) * (c.ψ ⟨y, hy⟩ : AE.Wr 6)⁻¹ := by
    rw [hYe, map_mul, map_mul, map_inv]
    rfl
  rw [h1, ae8c_e1_psi_eq c ha hperm, ae8c_e1_conj_ofVec]
  rfl

theorem ae8c_e1_cocycle_alg (σ₁ σ₂ : Equiv.Perm (Fin 6)) (e n₁ n₂ n₁₂ : Fin 6 → ZMod 2)
    (hn : n₁₂ = ae8c_e1_act σ₁ n₂ + n₁)
    (hκ : ae8c_e1_act σ₁ (n₂ + (ae8c_e1_act σ₂ e + e)) = n₂ + (ae8c_e1_act σ₂ e + e)) :
    n₁₂ + (ae8c_e1_act (σ₁ * σ₂) e + e) =
      (n₁ + (ae8c_e1_act σ₁ e + e)) + (n₂ + (ae8c_e1_act σ₂ e + e)) := by
  subst hn
  have hκ2 : ae8c_e1_act σ₁ n₂ + (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e) =
      n₂ + (ae8c_e1_act σ₂ e + e) := by
    have h := hκ
    rw [ae8c_e1_act_add, ae8c_e1_act_add, ae8c_e1_act_act] at h
    exact h
  have hP : ae8c_e1_act σ₁ n₂ =
      (n₂ + (ae8c_e1_act σ₂ e + e)) + (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e) := by
    have hX := ae8c_e1_vec_self (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e)
    calc ae8c_e1_act σ₁ n₂ = ae8c_e1_act σ₁ n₂ +
          ((ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e) +
            (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e)) := by rw [hX, add_zero]
      _ = (ae8c_e1_act σ₁ n₂ + (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e)) +
            (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e) := by abel
      _ = (n₂ + (ae8c_e1_act σ₂ e + e)) + (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e) := by
          rw [hκ2]
  rw [hP]
  have hEE := ae8c_e1_vec_self e
  have hAA := ae8c_e1_vec_self (ae8c_e1_act (σ₁ * σ₂) e)
  calc (n₂ + (ae8c_e1_act σ₂ e + e) + (ae8c_e1_act (σ₁ * σ₂) e + ae8c_e1_act σ₁ e)) + n₁ +
        (ae8c_e1_act (σ₁ * σ₂) e + e)
      = (n₁ + n₂ + ae8c_e1_act σ₂ e + ae8c_e1_act σ₁ e) + (ae8c_e1_act (σ₁ * σ₂) e +
          ae8c_e1_act (σ₁ * σ₂) e) + (e + e) := by abel
    _ = n₁ + n₂ + ae8c_e1_act σ₂ e + ae8c_e1_act σ₁ e := by rw [hAA, hEE, add_zero, add_zero]
    _ = (n₁ + (ae8c_e1_act σ₁ e + e)) + (n₂ + (ae8c_e1_act σ₂ e + e)) := by
          rw [show (n₁ + (ae8c_e1_act σ₁ e + e)) + (n₂ + (ae8c_e1_act σ₂ e + e)) =
            (n₁ + n₂ + ae8c_e1_act σ₂ e + ae8c_e1_act σ₁ e) + (e + e) by abel, hEE, add_zero]

theorem ae8c_e1_s_mem (c : Chart Ω u) (H : End18.Hyp Ω) {d₀ : G} (hd₀ : d₀ ∈ zGroup Ω) {y : G}
    (hy : y ∈ pSpan (Generic.centMembers Ω u)) :
    y * d₀ * y⁻¹ * d₀⁻¹ ∈ pSpan (Generic.centMembers Ω u) ∧ y * d₀ * y⁻¹ * d₀⁻¹ ∈ zGroup Ω := by
  refine ⟨?_, mul_mem (ae8c_e1_zGroup_conj H y hd₀) (inv_mem hd₀)⟩
  have h1 : y * d₀ * y⁻¹ * d₀⁻¹ = y * (d₀ * y⁻¹ * d₀⁻¹) := by group
  rw [h1]
  exact mul_mem hy (ae8c_e1_normalizes c H hd₀ (inv_mem hy))

theorem ae8c_e1_s_class (c : Chart Ω u) (H : End18.Hyp Ω)
    (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθ2 : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
      (y' : G) = d * y * d⁻¹ →
        AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹)
    {d₀ : G} (hd₀ : d₀ ∈ zGroup Ω) (e₁ : Fin 6 → ZMod 2)
    (he₁ : θ ⟨d₀, hd₀⟩ = AE.mkQ 6 (AE.Wr.ofVec e₁))
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8c_e1_nu c ((y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹) + (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁)
        = 0 ∨
      ae8c_e1_nu c ((y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹) + (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁)
        = fun _ => 1 := by
  obtain ⟨hsY, hsD⟩ := ae8c_e1_s_mem c H hd₀ y.2
  have hzY : d₀ * (y : G)⁻¹ * d₀⁻¹ ∈ pSpan (Generic.centMembers Ω u) :=
    ae8c_e1_normalizes c H hd₀ (inv_mem y.2)
  have hconj := hθ2 ⟨d₀, hd₀⟩ y⁻¹ ⟨d₀ * (y : G)⁻¹ * d₀⁻¹, hzY⟩ (by simp)
  rw [he₁] at hconj
  have hperm := ae8c_e1_perm_of_mem c H hsY hsD
  have hψs := ae8c_e1_psi_eq c hsY hperm
  have hsyz : (⟨(y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹, hsY⟩ : ↥(pSpan (Generic.centMembers Ω u))) =
      y * ⟨d₀ * (y : G)⁻¹ * d₀⁻¹, hzY⟩ := Subtype.ext (by simp [mul_assoc])
  have e1 : AE.mkQ 6 (c.ψ ⟨(y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹, hsY⟩ : AE.Wr 6) =
      AE.mkQ 6 (c.ψ y : AE.Wr 6) *
        AE.mkQ 6 (c.ψ ⟨d₀ * (y : G)⁻¹ * d₀⁻¹, hzY⟩ : AE.Wr 6) := by
    rw [hsyz, map_mul, Subgroup.coe_mul, map_mul]
  have hβ_inv : AE.mkQ 6 (c.ψ y⁻¹ : AE.Wr 6) = (AE.mkQ 6 (c.ψ y : AE.Wr 6))⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, map_inv]
  have hmk : AE.mkQ 6 (c.ψ ⟨(y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹, hsY⟩ : AE.Wr 6) =
      AE.mkQ 6 (AE.Wr.ofVec (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁)) := by
    rw [e1, hconj, hβ_inv]
    calc AE.mkQ 6 (c.ψ y : AE.Wr 6) * (AE.mkQ 6 (AE.Wr.ofVec e₁) *
            (AE.mkQ 6 (c.ψ y : AE.Wr 6))⁻¹ * (AE.mkQ 6 (AE.Wr.ofVec e₁))⁻¹)
        = (AE.mkQ 6 (c.ψ y : AE.Wr 6) * AE.mkQ 6 (AE.Wr.ofVec e₁) *
            (AE.mkQ 6 (c.ψ y : AE.Wr 6))⁻¹) * (AE.mkQ 6 (AE.Wr.ofVec e₁))⁻¹ := by group
      _ = AE.mkQ 6 (AE.Wr.ofVec (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁)) *
            (AE.mkQ 6 (AE.Wr.ofVec e₁))⁻¹ := by
          have hβt : AE.mkQ 6 (c.ψ y : AE.Wr 6) * AE.mkQ 6 (AE.Wr.ofVec e₁) *
              (AE.mkQ 6 (c.ψ y : AE.Wr 6))⁻¹ =
              AE.mkQ 6 (AE.Wr.ofVec (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁)) := by
            rw [← map_inv, ← map_mul, ← map_mul, ae8c_e1_conj_ofVec]
          rw [hβt]
      _ = AE.mkQ 6 (AE.Wr.ofVec (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁)) *
            AE.mkQ 6 (AE.Wr.ofVec e₁) := by rw [ae8c_e1_mkQ_ofVec_inv]
      _ = AE.mkQ 6 (AE.Wr.ofVec (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁)) :=
          ae8c_e1_mkQ_ofVec_mul _ _
  rw [hψs] at hmk
  exact (ae8c_e1_mkQ_ofVec_eq_iff _ _).mp hmk

theorem ae8c_e1_s_nu (c : Chart Ω u) (H : End18.Hyp Ω)
    (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθ2 : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
      (y' : G) = d * y * d⁻¹ →
        AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹)
    {d₀ : G} (hd₀ : d₀ ∈ zGroup Ω) (e₁ : Fin 6 → ZMod 2)
    (he₁ : θ ⟨d₀, hd₀⟩ = AE.mkQ 6 (AE.Wr.ofVec e₁))
    (y : ↥(pSpan (Generic.centMembers Ω u))) :
    ae8c_e1_nu c ((y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹) =
      ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁ := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : ↥(pSpan (Generic.centMembers Ω u)) → (Fin 6 → ZMod 2),
      ∀ y, κ y = ae8c_e1_nu c ((y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹) +
        (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁) := ⟨_, fun y => rfl⟩
  have hκmul : ∀ a b : ↥(pSpan (Generic.centMembers Ω u)), κ (a * b) = κ a + κ b := by
    intro a b
    obtain ⟨haS, haSD⟩ := ae8c_e1_s_mem c H hd₀ a.2
    obtain ⟨hbS, hbSD⟩ := ae8c_e1_s_mem c H hd₀ b.2
    have hpSb := ae8c_e1_perm_of_mem c H hbS hbSD
    have hX : (a : G) * ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹) * (a : G)⁻¹ ∈
        pSpan (Generic.centMembers Ω u) := mul_mem (mul_mem a.2 hbS) (inv_mem a.2)
    have hXD : (a : G) * ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹) * (a : G)⁻¹ ∈ zGroup Ω :=
      ae8c_e1_zGroup_conj H (a : G) hbSD
    have hpX := ae8c_e1_perm_conj c a.2 hbS hpSb hX
    have hνX : ae8c_e1_nu c ((a : G) * ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹) * (a : G)⁻¹) =
        ae8c_e1_act (c.ψ a : AE.Wr 6).perm (ae8c_e1_nu c ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹)) :=
      ae8c_e1_nu_conj c a.2 hbS hpSb
    have hSab : ((a * b : ↥(pSpan (Generic.centMembers Ω u))) : G) * d₀ *
        ((a * b : ↥(pSpan (Generic.centMembers Ω u))) : G)⁻¹ * d₀⁻¹ =
        ((a : G) * ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹) * (a : G)⁻¹) *
          ((a : G) * d₀ * (a : G)⁻¹ * d₀⁻¹) := by
      simp only [Subgroup.coe_mul]
      group
    have hnSab : ae8c_e1_nu c (((a * b : ↥(pSpan (Generic.centMembers Ω u))) : G) * d₀ *
        ((a * b : ↥(pSpan (Generic.centMembers Ω u))) : G)⁻¹ * d₀⁻¹) =
        ae8c_e1_act (c.ψ a : AE.Wr 6).perm (ae8c_e1_nu c ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹)) +
          ae8c_e1_nu c ((a : G) * d₀ * (a : G)⁻¹ * d₀⁻¹) := by
      rw [hSab, ae8c_e1_nu_mul c hX haS hpX, hνX]
    have hpab : (c.ψ (a * b) : AE.Wr 6).perm = (c.ψ a : AE.Wr 6).perm * (c.ψ b : AE.Wr 6).perm := by
      rw [map_mul, Subgroup.coe_mul, AE.Wr.mul_perm]
    have hκb : ae8c_e1_act (c.ψ a : AE.Wr 6).perm
        (ae8c_e1_nu c ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹) +
          (ae8c_e1_act (c.ψ b : AE.Wr 6).perm e₁ + e₁)) =
        ae8c_e1_nu c ((b : G) * d₀ * (b : G)⁻¹ * d₀⁻¹) +
          (ae8c_e1_act (c.ψ b : AE.Wr 6).perm e₁ + e₁) :=
      ae8c_e1_act_zero_or_one _ (ae8c_e1_s_class c H θ hθ2 hd₀ e₁ he₁ b)
    rw [hκdef, hκdef, hκdef, hpab]
    exact ae8c_e1_cocycle_alg _ _ e₁ _ _ _ hnSab hκb
  have hκy : κ y = 0 := by
    obtain ⟨K, hK⟩ : ∃ K : ↥(pSpan (Generic.centMembers Ω u)) →* Multiplicative (Fin 6 → ZMod 2),
        ∀ y, K y = Multiplicative.ofAdd (κ y) :=
      ⟨MonoidHom.mk' (fun y => Multiplicative.ofAdd (κ y)) (fun a b => by
        show Multiplicative.ofAdd (κ (a * b)) =
          Multiplicative.ofAdd (κ a) * Multiplicative.ofAdd (κ b)
        rw [hκmul]
        rfl), fun y => rfl⟩
    have h1 := ae8c_e1_eq_one_of_comm (Chart.perfect c) K (fun a b => Commute.all _ _) y
    rw [hK] at h1
    exact ofAdd_eq_one.mp h1
  rw [hκdef] at hκy
  have hζ := ae8c_e1_vec_self (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁)
  calc ae8c_e1_nu c ((y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹)
      = (ae8c_e1_nu c ((y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹) +
          (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁)) +
          (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁) := by
        rw [add_assoc, hζ, add_zero]
    _ = ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁ := by rw [hκy, zero_add]

open scoped Classical in
@[expose] noncomputable def ae8c_e1_E (c : Chart Ω u) (d₀ : G) (e₁ : Fin 6 → ZMod 2) (d : G) :
    Fin 6 → ZMod 2 :=
  if d ∈ pSpan (Generic.centMembers Ω u) then ae8c_e1_nu c d
  else e₁ + ae8c_e1_nu c (d₀⁻¹ * d)

theorem ae8c_e1_E_of_mem (c : Chart Ω u) (d₀ : G) (e₁ : Fin 6 → ZMod 2) {d : G}
    (hd : d ∈ pSpan (Generic.centMembers Ω u)) :
    ae8c_e1_E c d₀ e₁ d = ae8c_e1_nu c d := by
  unfold ae8c_e1_E
  rw [if_pos hd]

theorem ae8c_e1_E_of_not_mem (c : Chart Ω u) (d₀ : G) (e₁ : Fin 6 → ZMod 2) {d : G}
    (hd : d ∉ pSpan (Generic.centMembers Ω u)) :
    ae8c_e1_E c d₀ e₁ d = e₁ + ae8c_e1_nu c (d₀⁻¹ * d) := by
  unfold ae8c_e1_E
  rw [if_neg hd]

theorem ae8c_e1_E_mul (c : Chart Ω u) (H : End18.Hyp Ω) {d₀ : G} (hd₀ : d₀ ∈ zGroup Ω)
    (e₁ : Fin 6 → ZMod 2)
    (hcos : ∀ d ∈ zGroup Ω, d ∉ pSpan (Generic.centMembers Ω u) →
      d₀⁻¹ * d ∈ pSpan (Generic.centMembers Ω u))
    {x y : G} (hx : x ∈ zGroup Ω) (hy : y ∈ zGroup Ω) :
    ae8c_e1_E c d₀ e₁ (x * y) = ae8c_e1_E c d₀ e₁ x + ae8c_e1_E c d₀ e₁ y := by
  have hcomm : ∀ a b : G, a ∈ zGroup Ω → b ∈ zGroup Ω → a * b = b * a :=
    fun a b ha hb => ae8c_e1_zGroup_comm H ha hb
  have hd₀inv : d₀⁻¹ ∈ zGroup Ω := inv_mem hd₀
  have hsq : d₀⁻¹ * d₀⁻¹ = 1 := by
    have h := ae8c_e1_zGroup_sq H hd₀
    rw [inv_eq_of_mul_eq_one_right h]
    exact h
  have hee := ae8c_e1_vec_self e₁
  by_cases hxY : x ∈ pSpan (Generic.centMembers Ω u) <;>
    by_cases hyY : y ∈ pSpan (Generic.centMembers Ω u)
  · rw [ae8c_e1_E_of_mem c d₀ e₁ (mul_mem hxY hyY), ae8c_e1_E_of_mem c d₀ e₁ hxY,
      ae8c_e1_E_of_mem c d₀ e₁ hyY]
    exact ae8c_e1_nu_mul c hxY hyY (ae8c_e1_perm_of_mem c H hxY hx)
  · have hxyY : x * y ∉ pSpan (Generic.centMembers Ω u) := by
      intro h
      apply hyY
      have := mul_mem (inv_mem hxY) h
      simpa using this
    rw [ae8c_e1_E_of_not_mem c d₀ e₁ hxyY, ae8c_e1_E_of_mem c d₀ e₁ hxY,
      ae8c_e1_E_of_not_mem c d₀ e₁ hyY]
    have hcy := hcos y hy hyY
    have e1 : d₀⁻¹ * (x * y) = x * (d₀⁻¹ * y) := by
      calc d₀⁻¹ * (x * y) = (d₀⁻¹ * x) * y := by group
        _ = (x * d₀⁻¹) * y := by rw [hcomm _ _ hd₀inv hx]
        _ = x * (d₀⁻¹ * y) := by group
    rw [e1, ae8c_e1_nu_mul c hxY hcy (ae8c_e1_perm_of_mem c H hxY hx)]
    abel
  · have hxyY : x * y ∉ pSpan (Generic.centMembers Ω u) := by
      intro h
      apply hxY
      have := mul_mem h (inv_mem hyY)
      simpa using this
    have hdx := hcos x hx hxY
    have hdxD : d₀⁻¹ * x ∈ zGroup Ω := mul_mem hd₀inv hx
    rw [ae8c_e1_E_of_not_mem c d₀ e₁ hxyY, ae8c_e1_E_of_not_mem c d₀ e₁ hxY,
      ae8c_e1_E_of_mem c d₀ e₁ hyY]
    have e1 : d₀⁻¹ * (x * y) = (d₀⁻¹ * x) * y := by group
    rw [e1, ae8c_e1_nu_mul c hdx hyY (ae8c_e1_perm_of_mem c H hdx hdxD)]
    abel
  · have hxa := hcos x hx hxY
    have hya := hcos y hy hyY
    have hxaD : d₀⁻¹ * x ∈ zGroup Ω := mul_mem hd₀inv hx
    have hyaD : d₀⁻¹ * y ∈ zGroup Ω := mul_mem hd₀inv hy
    have e2 : x * y = (d₀⁻¹ * x) * (d₀⁻¹ * y) := by
      calc x * y = (d₀⁻¹ * d₀⁻¹) * (x * y) := by rw [hsq, one_mul]
        _ = d₀⁻¹ * (d₀⁻¹ * x) * y := by group
        _ = d₀⁻¹ * (x * d₀⁻¹) * y := by rw [hcomm _ _ hd₀inv hx]
        _ = (d₀⁻¹ * x) * (d₀⁻¹ * y) := by group
    have hxyY : x * y ∈ pSpan (Generic.centMembers Ω u) := by
      rw [e2]
      exact mul_mem hxa hya
    rw [ae8c_e1_E_of_mem c d₀ e₁ hxyY, ae8c_e1_E_of_not_mem c d₀ e₁ hxY,
      ae8c_e1_E_of_not_mem c d₀ e₁ hyY, e2,
      ae8c_e1_nu_mul c hxa hya (ae8c_e1_perm_of_mem c H hxa hxaD)]
    rw [show (e₁ + ae8c_e1_nu c (d₀⁻¹ * x)) + (e₁ + ae8c_e1_nu c (d₀⁻¹ * y)) =
        (e₁ + e₁) + (ae8c_e1_nu c (d₀⁻¹ * x) + ae8c_e1_nu c (d₀⁻¹ * y)) by abel, hee, zero_add]

theorem ae8c_e1_ker_mem (c : Chart Ω u) (H : End18.Hyp Ω)
    (hC : ∀ d ∈ zGroup Ω,
      d ∈ Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) →
        d ∈ Subgroup.zpowers u)
    (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθ2 : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
      (y' : G) = d * y * d⁻¹ →
        AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹)
    (d : ↥(zGroup Ω)) (hd : θ d = 1) : (d : G) ∈ pSpan (Generic.centMembers Ω u) := by
  have hdD : (d : G) ∈ zGroup Ω := d.2
  have step1 : ∀ y : ↥(pSpan (Generic.centMembers Ω u)),
      (y : G)⁻¹ * ((d : G) * y * (d : G)⁻¹) = 1 ∨
        (y : G)⁻¹ * ((d : G) * y * (d : G)⁻¹) = u := by
    intro y
    have hy' : (d : G) * y * (d : G)⁻¹ ∈ pSpan (Generic.centMembers Ω u) :=
      ae8c_e1_normalizes c H hdD y.2
    set y' : ↥(pSpan (Generic.centMembers Ω u)) := ⟨(d : G) * y * (d : G)⁻¹, hy'⟩ with hy'def
    have hy'G : (y' : G) = (d : G) * y * (d : G)⁻¹ := rfl
    have hc : AE.mkQ 6 (c.ψ y' : AE.Wr 6) = AE.mkQ 6 (c.ψ y : AE.Wr 6) := by
      rw [hθ2 d y y' hy'G, hd, one_mul, inv_one, mul_one]
    have hw := (AE.mkQ_eq_iff).mp hc.symm
    have hψw : (c.ψ (y⁻¹ * y') : AE.Wr 6) = (c.ψ y : AE.Wr 6)⁻¹ * (c.ψ y' : AE.Wr 6) := by
      rw [map_mul, map_inv]
      rfl
    have hwG : ((y⁻¹ * y' : ↥(pSpan (Generic.centMembers Ω u))) : G) =
        (y : G)⁻¹ * ((d : G) * y * (d : G)⁻¹) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hy'G]
    rcases hw with h | h
    · left
      have h2 : c.ψ (y⁻¹ * y') = c.ψ 1 := Subtype.ext (by rw [hψw, map_one]; exact h)
      have h3 : y⁻¹ * y' = 1 := c.ψ.injective h2
      have h4 := congrArg Subtype.val h3
      rw [Subgroup.coe_one] at h4
      rw [← hwG, h4]
    · right
      have h2 : c.ψ (y⁻¹ * y') = c.ψ ⟨u, c.mem⟩ :=
        Subtype.ext (by rw [hψw, c.u_eq]; exact h)
      have h3 : y⁻¹ * y' = ⟨u, c.mem⟩ := c.ψ.injective h2
      have h4 := congrArg Subtype.val h3
      rw [← hwG, h4]
  obtain ⟨t, ht⟩ : ∃ t : ↥(pSpan (Generic.centMembers Ω u)) →* G,
      ∀ y, t y = (y : G)⁻¹ * ((d : G) * y * (d : G)⁻¹) :=
    ⟨MonoidHom.mk' (fun y => (y : G)⁻¹ * ((d : G) * y * (d : G)⁻¹)) (fun a b => by
      show ((a * b : ↥(pSpan (Generic.centMembers Ω u))) : G)⁻¹ *
          ((d : G) * ((a * b : ↥(pSpan (Generic.centMembers Ω u))) : G) * (d : G)⁻¹) =
        ((a : G)⁻¹ * ((d : G) * a * (d : G)⁻¹)) * ((b : G)⁻¹ * ((d : G) * b * (d : G)⁻¹))
      rw [Subgroup.coe_mul]
      exact ae8c_e1_comm_mul_aux (by group) (by group)
        (ae8c_e1_comm_of_T (step1 a) (ae8c_e1_Y_comm_u b.2))), fun y => rfl⟩
  have hcommT : ∀ a b : ↥(pSpan (Generic.centMembers Ω u)), Commute (t a) (t b) := by
    intro a b
    rw [ht, ht]
    rcases step1 a with ha | ha <;> rcases step1 b with hb | hb <;> rw [ha, hb] <;>
      simp [Commute, SemiconjBy]
  have hker : ∀ y : ↥(pSpan (Generic.centMembers Ω u)), t y = 1 := fun y =>
    ae8c_e1_eq_one_of_comm (Chart.perfect c) t hcommT y
  have hcent : (d : G) ∈
      Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 := hker ⟨h, hh⟩
    rw [ht] at h1
    have h2 : (d : G) * h * (d : G)⁻¹ = h := (inv_mul_eq_one.mp h1).symm
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  exact (Subgroup.zpowers_le.mpr c.mem) (hC _ hdD hcent)

theorem ae8c_e1_theta_eq (c : Chart Ω u) (H : End18.Hyp Ω) (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθ1 : ∀ d : ↥(zGroup Ω), ∃ v : Fin 6 → ZMod 2, θ d = AE.mkQ 6 (AE.Wr.ofVec v))
    (hθ2 : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
      (y' : G) = d * y * d⁻¹ →
        AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹)
    (d : ↥(zGroup Ω)) (hdY : (d : G) ∈ pSpan (Generic.centMembers Ω u)) :
    θ d = AE.mkQ 6 (c.ψ ⟨(d : G), hdY⟩ : AE.Wr 6) := by
  have hperm : (c.ψ ⟨(d : G), hdY⟩ : AE.Wr 6).perm = 1 :=
    ae8c_e1_perm_of_mem c H hdY d.2
  have hψy := ae8c_e1_psi_eq c hdY hperm
  obtain ⟨w, hw⟩ := hθ1 d
  have hcomm : ∀ z : ↥(pSpan (Generic.centMembers Ω u)),
      (θ d)⁻¹ * AE.mkQ 6 (c.ψ ⟨(d : G), hdY⟩ : AE.Wr 6) * AE.mkQ 6 (c.ψ z : AE.Wr 6) =
        AE.mkQ 6 (c.ψ z : AE.Wr 6) * ((θ d)⁻¹ * AE.mkQ 6 (c.ψ ⟨(d : G), hdY⟩ : AE.Wr 6)) := by
    intro z
    have hz := hθ2 d z (⟨(d : G), hdY⟩ * z * ⟨(d : G), hdY⟩⁻¹) (by simp)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at hz
    exact ae8c_e1_comm_aux hz
  have hc0 : (θ d)⁻¹ * AE.mkQ 6 (c.ψ ⟨(d : G), hdY⟩ : AE.Wr 6) =
      AE.mkQ 6 (AE.Wr.ofVec (w + ae8c_e1_nu c (d : G))) := by
    rw [hw, hψy, ae8c_e1_mkQ_ofVec_inv, ae8c_e1_mkQ_ofVec_mul]
  obtain ⟨z1, hz1⟩ := ae8c_e1_exists_psi_ofPerm c ae8c_p1 ae8c_e1_sign_p.1
  obtain ⟨z2, hz2⟩ := ae8c_e1_exists_psi_ofPerm c ae8c_p2 ae8c_e1_sign_p.2.1
  obtain ⟨z3, hz3⟩ := ae8c_e1_exists_psi_ofPerm c ae8c_p3 ae8c_e1_sign_p.2.2
  have hx1 := ae8c_e1_mkQ_ofVec_comm ae8c_p1 (w + ae8c_e1_nu c (d : G)) (by
    have h := hcomm z1
    rw [hz1, hc0] at h
    exact h)
  have hx2 := ae8c_e1_mkQ_ofVec_comm ae8c_p2 (w + ae8c_e1_nu c (d : G)) (by
    have h := hcomm z2
    rw [hz2, hc0] at h
    exact h)
  have hx3 := ae8c_e1_mkQ_ofVec_comm ae8c_p3 (w + ae8c_e1_nu c (d : G)) (by
    have h := hcomm z3
    rw [hz3, hc0] at h
    exact h)
  have hfin : (θ d)⁻¹ * AE.mkQ 6 (c.ψ ⟨(d : G), hdY⟩ : AE.Wr 6) = 1 := by
    rw [hc0]
    exact ae8c_e1_mkQ_ofVec_one _ (ae8c_e1_fin_check _ hx1 hx2 hx3)
  exact inv_mul_eq_one.mp hfin

theorem ae8c_e1_even_mem (c : Chart Ω u) (H : End18.Hyp Ω)
    (hC : ∀ d ∈ zGroup Ω,
      d ∈ Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) →
        d ∈ Subgroup.zpowers u)
    (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθ1 : ∀ d : ↥(zGroup Ω), ∃ v : Fin 6 → ZMod 2, θ d = AE.mkQ 6 (AE.Wr.ofVec v))
    (hθ2 : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
      (y' : G) = d * y * d⁻¹ →
        AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹)
    (z : G) (hz : z ∈ zGroup Ω) (x : Fin 6 → ZMod 2) (hx : ∑ i, x i = 0)
    (hθz : θ ⟨z, hz⟩ = AE.mkQ 6 (AE.Wr.ofVec x)) :
    z ∈ pSpan (Generic.centMembers Ω u) := by
  obtain ⟨y, hy⟩ : ∃ y : ↥(pSpan (Generic.centMembers Ω u)),
      (c.ψ y : AE.Wr 6) = AE.Wr.ofVec x :=
    ⟨c.ψ.symm ⟨AE.Wr.ofVec x, ae8c_e1_ofVec_mem x hx⟩, by simp⟩
  have hyD : (y : G) ∈ zGroup Ω := (Chart.mem_zGroup_iff c H y).mpr (by rw [hy]; rfl)
  have hθy : θ ⟨(y : G), hyD⟩ = AE.mkQ 6 (AE.Wr.ofVec x) := by
    rw [ae8c_e1_theta_eq c H θ hθ1 hθ2 ⟨(y : G), hyD⟩ y.2]
    exact congrArg (AE.mkQ 6) hy
  have hk : θ (⟨z, hz⟩⁻¹ * ⟨(y : G), hyD⟩) = 1 := by
    rw [map_mul, map_inv, hθz, hθy, inv_mul_cancel]
  have hmem := ae8c_e1_ker_mem c H hC θ hθ2 (⟨z, hz⟩⁻¹ * ⟨(y : G), hyD⟩) hk
  have hmem' : z⁻¹ * (y : G) ∈ pSpan (Generic.centMembers Ω u) := by
    simpa using hmem
  have e3 : z = (y : G) * (z⁻¹ * (y : G))⁻¹ := by group
  rw [e3]
  exact mul_mem y.2 (inv_mem hmem')

theorem ae8c_e1_coset (c : Chart Ω u) (H : End18.Hyp Ω)
    (hC : ∀ d ∈ zGroup Ω,
      d ∈ Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) →
        d ∈ Subgroup.zpowers u)
    (θ : ↥(zGroup Ω) →* AE.AEQ 6)
    (hθ1 : ∀ d : ↥(zGroup Ω), ∃ v : Fin 6 → ZMod 2, θ d = AE.mkQ 6 (AE.Wr.ofVec v))
    (hθ2 : ∀ (d : ↥(zGroup Ω)) (y y' : ↥(pSpan (Generic.centMembers Ω u))),
      (y' : G) = d * y * d⁻¹ →
        AE.mkQ 6 (c.ψ y' : AE.Wr 6) = θ d * AE.mkQ 6 (c.ψ y : AE.Wr 6) * (θ d)⁻¹)
    {d₀ d : G} (hd₀ : d₀ ∈ zGroup Ω) (hd₀Y : d₀ ∉ pSpan (Generic.centMembers Ω u))
    (hd : d ∈ zGroup Ω) (hdY : d ∉ pSpan (Generic.centMembers Ω u))
    (e₁ : Fin 6 → ZMod 2) (he₁ : θ ⟨d₀, hd₀⟩ = AE.mkQ 6 (AE.Wr.ofVec e₁)) :
    d₀⁻¹ * d ∈ pSpan (Generic.centMembers Ω u) := by
  obtain ⟨xd, hxd⟩ := hθ1 ⟨d, hd⟩
  have hsd : ∑ i, xd i ≠ 0 := fun h =>
    hdY (ae8c_e1_even_mem c H hC θ hθ1 hθ2 d hd xd h hxd)
  have hs₀ : ∑ i, e₁ i ≠ 0 := fun h =>
    hd₀Y (ae8c_e1_even_mem c H hC θ hθ1 hθ2 d₀ hd₀ e₁ h he₁)
  have hz : d₀⁻¹ * d ∈ zGroup Ω := mul_mem (inv_mem hd₀) hd
  refine ae8c_e1_even_mem c H hC θ hθ1 hθ2 (d₀⁻¹ * d) hz (e₁ + xd) ?_ ?_
  · simp only [Pi.add_apply, Finset.sum_add_distrib]
    exact ae8c_e1_zmod2_ne _ _ hs₀ hsd
  · have hsplit : (⟨d₀⁻¹ * d, hz⟩ : ↥(zGroup Ω)) = ⟨d₀, hd₀⟩⁻¹ * ⟨d, hd⟩ := rfl
    rw [hsplit, map_mul, map_inv, he₁, hxd, ae8c_e1_mkQ_ofVec_inv, ae8c_e1_mkQ_ofVec_mul]

theorem ae8c_e1_exists_off (c : Chart Ω u) (H : End18.Hyp Ω)
    (hcard : Nat.card ↥(zGroup Ω) = 64) :
    ∃ d ∈ zGroup Ω, d ∉ pSpan (Generic.centMembers Ω u) := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  let g : ↥(zGroup Ω) → {x : Fin 6 → ZMod 2 // ∑ i, x i = 0} :=
    fun d => ⟨ae8c_e1_nu c (d : G), ae8c_e1_nu_sum c (hcon (d : G) d.2)⟩
  have hg : Function.Injective g := by
    intro d d' h
    have h1 : ae8c_e1_nu c (d : G) = ae8c_e1_nu c (d' : G) := congrArg Subtype.val h
    have hdY := hcon (d : G) d.2
    have hd'Y := hcon (d' : G) d'.2
    have e1 : c.ψ ⟨(d : G), hdY⟩ = c.ψ ⟨(d' : G), hd'Y⟩ := Subtype.ext (by
      rw [ae8c_e1_psi_eq c hdY (ae8c_e1_perm_of_mem c H hdY d.2),
        ae8c_e1_psi_eq c hd'Y (ae8c_e1_perm_of_mem c H hd'Y d'.2), h1])
    have e2 := congrArg Subtype.val (c.ψ.injective e1)
    exact Subtype.ext e2
  have hle := Nat.card_le_card_of_injective g hg
  rw [hcard, ae8c_e1_card_even] at hle
  omega

section FrameCert


theorem Chart.exists_coords (H : End18.Hyp Ω)
    (hu : SectFrame Ω u) (c : Chart Ω u) :
    Nonempty (Coords c) := by
  have hC : ∀ d ∈ zGroup Ω,
      d ∈ Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) →
        d ∈ Subgroup.zpowers u := fun d hd hcd => by
    have h1 : d ∈ zGroup Ω ⊓
        Subgroup.centralizer ((pSpan (Generic.centMembers Ω u) : Subgroup G) : Set G) :=
      ⟨hd, hcd⟩
    rw [Chart.zGroup_inf_centralizer_eq H hu] at h1
    exact h1
  classical
  obtain ⟨θ, hθ1, hθ2⟩ := Chart.exists_vecAct c H
  have hcard : Nat.card ↥(zGroup Ω) = 64 := Chart.card_zGroup_eq_64 H
  obtain ⟨d₀, hd₀, hd₀Y⟩ := ae8c_e1_exists_off c H hcard
  obtain ⟨e₁, he₁⟩ := hθ1 ⟨d₀, hd₀⟩
  have he₁sum : ∑ i, e₁ i ≠ 0 := fun h =>
    hd₀Y (ae8c_e1_even_mem c H hC θ hθ1 hθ2 d₀ hd₀ e₁ h he₁)
  have hcos : ∀ d ∈ zGroup Ω, d ∉ pSpan (Generic.centMembers Ω u) →
      d₀⁻¹ * d ∈ pSpan (Generic.centMembers Ω u) := fun d hd hdY =>
    ae8c_e1_coset c H hC θ hθ1 hθ2 hd₀ hd₀Y hd hdY e₁ he₁
  obtain ⟨F, hF⟩ : ∃ F : ↥(zGroup Ω) →* Multiplicative (Fin 6 → ZMod 2),
      ∀ d, F d = Multiplicative.ofAdd (ae8c_e1_E c d₀ e₁ (d : G)) :=
    ⟨MonoidHom.mk' (fun d => Multiplicative.ofAdd (ae8c_e1_E c d₀ e₁ (d : G))) (fun a b => by
      show Multiplicative.ofAdd (ae8c_e1_E c d₀ e₁ ((a * b : ↥(zGroup Ω)) : G)) =
        Multiplicative.ofAdd (ae8c_e1_E c d₀ e₁ (a : G)) *
          Multiplicative.ofAdd (ae8c_e1_E c d₀ e₁ (b : G))
      rw [Subgroup.coe_mul, ae8c_e1_E_mul c H hd₀ e₁ hcos a.2 b.2]
      rfl), fun d => rfl⟩
  have hinj : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    intro d hd
    rw [hF] at hd
    have hE : ae8c_e1_E c d₀ e₁ (d : G) = 0 := ofAdd_eq_one.mp hd
    by_cases hdY : (d : G) ∈ pSpan (Generic.centMembers Ω u)
    · rw [ae8c_e1_E_of_mem c d₀ e₁ hdY] at hE
      have hψ : (c.ψ ⟨(d : G), hdY⟩ : AE.Wr 6) = 1 := by
        rw [ae8c_e1_psi_eq c hdY (ae8c_e1_perm_of_mem c H hdY d.2), hE]
        rfl
      have h1 : c.ψ ⟨(d : G), hdY⟩ = 1 := Subtype.ext hψ
      have h2 : (⟨(d : G), hdY⟩ : ↥(pSpan (Generic.centMembers Ω u))) = 1 :=
        c.ψ.injective (by rw [h1, map_one])
      have h4 := congrArg Subtype.val h2
      rw [Subgroup.coe_one] at h4
      exact Subtype.ext h4
    · rw [ae8c_e1_E_of_not_mem c d₀ e₁ hdY] at hE
      have hsum := congrArg (fun v : Fin 6 → ZMod 2 => ∑ i, v i) hE
      simp only [Pi.add_apply, Finset.sum_add_distrib, Pi.zero_apply,
        Finset.sum_const_zero] at hsum
      rw [ae8c_e1_nu_sum c (hcos (d : G) d.2 hdY), add_zero] at hsum
      exact absurd hsum he₁sum
  have hbij : Function.Bijective F :=
    Function.Injective.bijective_of_nat_card_le hinj
      (le_of_eq (by rw [ae8c_e1_card_mult, hcard]))
  have hval : ∀ d : ↥(zGroup Ω),
      (MulEquiv.ofBijective F hbij d).toAdd = ae8c_e1_E c d₀ e₁ (d : G) := by
    intro d
    rw [MulEquiv.ofBijective_apply, hF]
    rfl
  refine ⟨⟨MulEquiv.ofBijective F hbij, ?_, ?_, ?_⟩⟩
  ·
    intro d y hdy
    have hmem : (d : G) ∈ pSpan (Generic.centMembers Ω u) := by
      rw [hdy]
      exact y.2
    have hy' : (⟨(d : G), hmem⟩ : ↥(pSpan (Generic.centMembers Ω u))) = y :=
      Subtype.ext hdy
    rw [hval, ae8c_e1_E_of_mem c d₀ e₁ hmem, ae8c_e1_nu_Y c hmem, hy']
  ·
    intro y d d' hd'
    try simp only [Subgroup.coe_inv] at hd'
    rw [hval, hval]
    show ae8c_e1_E c d₀ e₁ (d' : G) =
      ae8c_e1_act (c.ψ y : AE.Wr 6).perm (ae8c_e1_E c d₀ e₁ (d : G))
    by_cases hdY : (d : G) ∈ pSpan (Generic.centMembers Ω u)
    · have hd'Y : (d' : G) ∈ pSpan (Generic.centMembers Ω u) := by
        rw [hd']
        exact mul_mem (mul_mem y.2 hdY) (inv_mem y.2)
      rw [ae8c_e1_E_of_mem c d₀ e₁ hd'Y, ae8c_e1_E_of_mem c d₀ e₁ hdY, hd']
      exact ae8c_e1_nu_conj c y.2 hdY (ae8c_e1_perm_of_mem c H hdY d.2)
    · have hd'Y : (d' : G) ∉ pSpan (Generic.centMembers Ω u) := by
        intro h
        apply hdY
        have e1 : (d : G) = (y : G)⁻¹ * (d' : G) * (y : G) := by
          rw [hd']
          group
        rw [e1]
        exact mul_mem (mul_mem (inv_mem y.2) h) y.2
      rw [ae8c_e1_E_of_not_mem c d₀ e₁ hd'Y, ae8c_e1_E_of_not_mem c d₀ e₁ hdY]
      have haY : d₀⁻¹ * (d : G) ∈ pSpan (Generic.centMembers Ω u) := hcos (d : G) d.2 hdY
      have haD : d₀⁻¹ * (d : G) ∈ zGroup Ω := mul_mem (inv_mem hd₀) d.2
      have hpa : (c.ψ ⟨d₀⁻¹ * (d : G), haY⟩ : AE.Wr 6).perm = 1 :=
        ae8c_e1_perm_of_mem c H haY haD
      obtain ⟨hSY, hSD⟩ := ae8c_e1_s_mem c H hd₀ y.2
      have hperm_S := ae8c_e1_perm_of_mem c H hSY hSD
      have hy'Y : d₀⁻¹ * (y : G) * d₀ ∈ pSpan (Generic.centMembers Ω u) := by
        have h := ae8c_e1_normalizes c H (inv_mem hd₀) y.2
        rwa [inv_inv] at h
      have hSy : (y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹ = d₀⁻¹ * (y : G) * d₀ * (y : G)⁻¹ := by
        have hw : (y : G) * d₀ * (y : G)⁻¹ ∈ zGroup Ω := ae8c_e1_zGroup_conj H (y : G) hd₀
        have hcw := ae8c_e1_zGroup_comm H hw hd₀
        calc (y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹ = ((y : G) * d₀ * (y : G)⁻¹) * d₀⁻¹ := by group
          _ = d₀⁻¹ * ((y : G) * d₀ * (y : G)⁻¹) := ae8c_e1_inv_comm hcw
          _ = d₀⁻¹ * (y : G) * d₀ * (y : G)⁻¹ := by group
      have haYa : (d₀⁻¹ * (y : G) * d₀) * (d₀⁻¹ * (d : G)) * (d₀⁻¹ * (y : G) * d₀)⁻¹ ∈
          pSpan (Generic.centMembers Ω u) := mul_mem (mul_mem hy'Y haY) (inv_mem hy'Y)
      have hpYa := ae8c_e1_perm_conj c hy'Y haY hpa haYa
      have hnYa := ae8c_e1_nu_conj c hy'Y haY hpa
      have hpy' : (c.ψ ⟨d₀⁻¹ * (y : G) * d₀, hy'Y⟩ : AE.Wr 6).perm =
          (c.ψ y : AE.Wr 6).perm := by
        have e4 : (⟨d₀⁻¹ * (y : G) * d₀, hy'Y⟩ : ↥(pSpan (Generic.centMembers Ω u))) =
            ⟨(y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹, hSY⟩ * y := Subtype.ext (by
          show d₀⁻¹ * (y : G) * d₀ = (y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹ * (y : G)
          rw [hSy]
          group)
        rw [e4, map_mul, Subgroup.coe_mul, AE.Wr.mul_perm, hperm_S, one_mul]
      have hnS := ae8c_e1_s_nu c H θ hθ2 hd₀ e₁ he₁ y
      have hb : d₀⁻¹ * (d' : G) = ((d₀⁻¹ * (y : G) * d₀) * (d₀⁻¹ * (d : G)) *
          (d₀⁻¹ * (y : G) * d₀)⁻¹) * ((y : G) * d₀ * (y : G)⁻¹ * d₀⁻¹) := by
        rw [hSy, hd']
        group
      have hnb : ae8c_e1_nu c (d₀⁻¹ * (d' : G)) =
          ae8c_e1_act (c.ψ y : AE.Wr 6).perm (ae8c_e1_nu c (d₀⁻¹ * (d : G))) +
            (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁) := by
        rw [hb, ae8c_e1_nu_mul c haYa hSY hpYa, hnYa, hpy', hnS]
      rw [hnb, ae8c_e1_act_add]
      rw [show e₁ + (ae8c_e1_act (c.ψ y : AE.Wr 6).perm (ae8c_e1_nu c (d₀⁻¹ * (d : G))) +
          (ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁ + e₁)) =
          (e₁ + e₁) + (ae8c_e1_act (c.ψ y : AE.Wr 6).perm (ae8c_e1_nu c (d₀⁻¹ * (d : G))) +
            ae8c_e1_act (c.ψ y : AE.Wr 6).perm e₁) by abel, ae8c_e1_vec_self, zero_add,
        add_comm]
  ·
    intro d y y' hy'
    try simp only [Subgroup.coe_inv] at hy'
    rw [hval]
    by_cases hdY : (d : G) ∈ pSpan (Generic.centMembers Ω u)
    · rw [ae8c_e1_E_of_mem c d₀ e₁ hdY,
        ← ae8c_e1_psi_eq c hdY (ae8c_e1_perm_of_mem c H hdY d.2)]
      have hyy : y' = ⟨(d : G), hdY⟩ * y * ⟨(d : G), hdY⟩⁻¹ := Subtype.ext (by
        rw [hy']
        simp)
      simp only [hyy, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    · rw [ae8c_e1_E_of_not_mem c d₀ e₁ hdY]
      have haY : d₀⁻¹ * (d : G) ∈ pSpan (Generic.centMembers Ω u) := hcos (d : G) d.2 hdY
      have haD : d₀⁻¹ * (d : G) ∈ zGroup Ω := mul_mem (inv_mem hd₀) d.2
      have hpa : (c.ψ ⟨d₀⁻¹ * (d : G), haY⟩ : AE.Wr 6).perm = 1 :=
        ae8c_e1_perm_of_mem c H haY haD
      have hzY : (d₀⁻¹ * (d : G)) * (y : G) * (d₀⁻¹ * (d : G))⁻¹ ∈
          pSpan (Generic.centMembers Ω u) :=
        mul_mem (mul_mem haY y.2) (inv_mem haY)
      have hy'' : (y' : G) = d₀ * ((d₀⁻¹ * (d : G)) * (y : G) * (d₀⁻¹ * (d : G))⁻¹) * d₀⁻¹ := by
        rw [hy']
        group
      have hconj := hθ2 ⟨d₀, hd₀⟩ ⟨(d₀⁻¹ * (d : G)) * (y : G) * (d₀⁻¹ * (d : G))⁻¹, hzY⟩ y'
        hy''
      have hzψ : AE.mkQ 6 (c.ψ ⟨(d₀⁻¹ * (d : G)) * (y : G) * (d₀⁻¹ * (d : G))⁻¹, hzY⟩ :
          AE.Wr 6) =
          AE.mkQ 6 (c.ψ ⟨d₀⁻¹ * (d : G), haY⟩ : AE.Wr 6) * AE.mkQ 6 (c.ψ y : AE.Wr 6) *
            (AE.mkQ 6 (c.ψ ⟨d₀⁻¹ * (d : G), haY⟩ : AE.Wr 6))⁻¹ := by
        have e2 : (⟨(d₀⁻¹ * (d : G)) * (y : G) * (d₀⁻¹ * (d : G))⁻¹, hzY⟩ :
            ↥(pSpan (Generic.centMembers Ω u))) =
            ⟨d₀⁻¹ * (d : G), haY⟩ * y * ⟨d₀⁻¹ * (d : G), haY⟩⁻¹ := rfl
        rw [e2]
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      have hνa : AE.mkQ 6 (AE.Wr.ofVec (ae8c_e1_nu c (d₀⁻¹ * (d : G)))) =
          AE.mkQ 6 (c.ψ ⟨d₀⁻¹ * (d : G), haY⟩ : AE.Wr 6) := by
        rw [ae8c_e1_psi_eq c haY hpa]
      rw [← ae8c_e1_mkQ_ofVec_mul, hνa, ← he₁, hconj, hzψ]
      group

end FrameCert

structure Classes {c : Chart Ω u} (co : Coords c) : Prop where
  z_class : ∀ x : G, (∃ L ∈ Ω, IsUniqueInvolution L x) ↔
    ∃ hx : x ∈ zGroup Ω, wt (co.e ⟨x, hx⟩).toAdd = 3 ∨ wt (co.e ⟨x, hx⟩).toAdd = 4
  u_class : ∀ x : G, (∃ g : G, x = g * u * g⁻¹) ↔
    ∃ hx : x ∈ zGroup Ω, wt (co.e ⟨x, hx⟩).toAdd = 1 ∨ wt (co.e ⟨x, hx⟩).toAdd = 2 ∨
      wt (co.e ⟨x, hx⟩).toAdd = 5 ∨ wt (co.e ⟨x, hx⟩).toAdd = 6

namespace Coords

variable {c : Chart Ω u} (co : Coords c)

theorem mem_normalizer_iff (H : End18.Hyp Ω) {L : Subgroup G}
    (hL : L ∈ Generic.centMembers Ω u) {α : Finset (Fin 6)} {h : α.card = 4} {b : Bool}
    (hlab : ((L.subgroupOf (pSpan (Generic.centMembers Ω u))).map c.ψ.toMonoidHom).map
      (AE.aeSub 6).subtype = AE.memAt α h b) (d : ↥(zGroup Ω)) :
    (d : G) ∈ Subgroup.normalizer (L : Set G) ↔
      Even (Finset.univ.filter fun i => i ∈ α ∧ (co.e d).toAdd i ≠ 0).card := by
  have huD : u ∈ zGroup Ω :=
    (Chart.mem_zGroup_iff c H ⟨u, c.mem⟩).mpr (by rw [c.u_eq]; rfl)
  have hdu : (d : G) * u = u * (d : G) := by
    have h1 : co.e d * co.e ⟨u, huD⟩ = co.e ⟨u, huD⟩ * co.e d := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (co.e.injective h1)
  have hL'P : conjSub (d : G) L ∈ Generic.centMembers Ω u := by
    refine ⟨H.endHyp.thmD.hyp.conjInvariant (d : G) L hL.1, ?_⟩
    intro m hm
    rw [mem_conjSub_iff] at hm
    have hc0 : Commute ((d : G)⁻¹ * m * (d : G)) u :=
      Subgroup.mem_centralizer_singleton_iff.mp (hL.2 hm)
    have hdc : Commute (d : G) u := hdu
    have hcm : Commute ((d : G) * ((d : G)⁻¹ * m * (d : G)) * (d : G)⁻¹) u :=
      (hdc.mul_left hc0).mul_left hdc.inv_left
    rw [show (d : G) * ((d : G)⁻¹ * m * (d : G)) * (d : G)⁻¹ = m by group] at hcm
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcm
  have hLY : L ≤ pSpan (Generic.centMembers Ω u) := le_pSpan hL
  obtain ⟨α', h', b', hlab'⟩ := c.label _ hL'P
  have hII : ∀ t ∈ AE.memBar α' h' b', ∃ x ∈ AE.memBar α h b,
      t = AE.mkQ 6 (AE.Wr.ofVec (co.e d).toAdd) * x *
        (AE.mkQ 6 (AE.Wr.ofVec (co.e d).toAdd))⁻¹ := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    rw [← hlab'] at hs
    obtain ⟨w, hw, hws⟩ := Subgroup.mem_map.mp hs
    obtain ⟨y', hy', hyw⟩ := Subgroup.mem_map.mp hw
    have hy'L : (y' : G) ∈ conjSub (d : G) L := Subgroup.mem_subgroupOf.mp hy'
    have hyL : (d : G)⁻¹ * (y' : G) * (d : G) ∈ L := mem_conjSub_iff.mp hy'L
    have hyY : (d : G)⁻¹ * (y' : G) * (d : G) ∈ pSpan (Generic.centMembers Ω u) := hLY hyL
    have hye : (⟨_, hyY⟩ : ↥(pSpan (Generic.centMembers Ω u))) ∈
        L.subgroupOf (pSpan (Generic.centMembers Ω u)) := Subgroup.mem_subgroupOf.mpr hyL
    refine ⟨AE.mkQ 6 (c.ψ ⟨_, hyY⟩ : AE.Wr 6), ?_, ?_⟩
    · have hmem : (c.ψ ⟨_, hyY⟩ : AE.Wr 6) ∈ AE.memAt α h b := by
        rw [← hlab]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hye)
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    · have hyy : (y' : G) = (d : G) * ((d : G)⁻¹ * (y' : G) * (d : G)) * (d : G)⁻¹ := by
        group
      have key := co.conj_Y d ⟨_, hyY⟩ y' hyy
      have hs' : s = (c.ψ y' : AE.Wr 6) := by
        subst hws
        subst hyw
        rfl
      rw [hs', key]
  have hIII : ∀ x ∈ AE.memBar α h b, AE.mkQ 6 (AE.Wr.ofVec (co.e d).toAdd) * x *
      (AE.mkQ 6 (AE.Wr.ofVec (co.e d).toAdd))⁻¹ ∈
        AE.memBar α h
          (if Even (Finset.univ.filter fun i => i ∈ α ∧ (co.e d).toAdd i ≠ 0).card
            then b else !b) := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨_, ae8c_e2_memAt_conj _ ha, by simp only [map_mul, map_inv]⟩
  have hcardB : ∀ (α₁ : Finset (Fin 6)) (h₁ : α₁.card = 4) (b₁ : Bool),
      Nat.card (AE.memBar α₁ h₁ b₁) = 8 :=
    fun α₁ h₁ b₁ => AE.natCard_memBar (by norm_num) α₁ h₁ b₁
  have hne := AE.memBar_true_ne_false (by norm_num : 5 ≤ 6) α h
  constructor
  · intro hnorm
    have hLeq : conjSub (d : G) L = L := (ae8c_e2_normalizer_iff (d : G) L).mp hnorm
    by_contra hodd
    have heqA : AE.memAt α' h' b' = AE.memAt α h b := by
      rw [← hlab', hLeq]
      exact hlab
    have heqB : AE.memBar α' h' b' = AE.memBar α h b := by
      unfold AE.memBar
      rw [heqA]
    have hsub : AE.memBar α h b ≤ AE.memBar α h (!b) := by
      intro t ht
      obtain ⟨x, hx, hxt⟩ := hII t (by rw [heqB]; exact ht)
      have hIIIx := hIII x hx
      rw [if_neg hodd] at hIIIx
      rw [hxt]
      exact hIIIx
    have hEq : AE.memBar α h b = AE.memBar α h (!b) :=
      Subgroup.eq_of_le_of_card_ge hsub (le_of_eq (by rw [hcardB, hcardB]))
    cases b
    · exact hne hEq.symm
    · exact hne hEq
  · intro hev
    have hsub : AE.memBar α' h' b' ≤ AE.memBar α h b := by
      intro t ht
      obtain ⟨x, hx, hxt⟩ := hII t ht
      have hIIIx := hIII x hx
      rw [if_pos hev] at hIIIx
      rw [hxt]
      exact hIIIx
    have hEq : AE.memBar α' h' b' = AE.memBar α h b :=
      Subgroup.eq_of_le_of_card_ge hsub (le_of_eq (by rw [hcardB, hcardB]))
    obtain ⟨rfl, rfl⟩ := ae8c_e2_memBar_inj hEq
    have hLL : conjSub (d : G) L = L := c.label_inj _ hL'P L hL (hlab'.trans hlab.symm)
    exact (ae8c_e2_normalizer_iff (d : G) L).mpr hLL

theorem ae8c_co_u {c : Chart Ω u} (co : Coords c) (hu : u ∈ zGroup Ω) (cu : u ∈ pSpan
    (Generic.centMembers Ω u)) : (co.e ⟨u, hu⟩).toAdd = fun _ => 1 := by
  rw [co.vec ⟨u, hu⟩ ⟨u, cu⟩ rfl, c.u_eq]
  rfl

theorem ae8c_co_of_inv {c : Chart Ω u} (co : Coords c) {α : Finset (Fin 6)} {h : α.card = 4}
    {w : G} (hw : w ∈ zGroup Ω) (hwY : w ∈ pSpan (Generic.centMembers Ω u))
    (hψ : ((c.ψ ⟨w, hwY⟩ : AE.aeSub 6) : AE.Wr 6) = AE.zOf (AE.emb α h)) :
    (co.e ⟨w, hw⟩).toAdd = fun i => if i ∈ α then 1 else 0 := by
  rw [co.vec ⟨w, hw⟩ ⟨w, hwY⟩ rfl, hψ]
  funext i
  by_cases hi : i ∈ α
  · simp [AE.zOf_vec_apply, AE.range_emb, hi]
  · simp [AE.zOf_vec_apply, AE.range_emb, hi]

theorem ae8c_mem_normalizer_of_comm {S : Subgroup G} {g : G}
    (h : ∀ k ∈ S, k * g = g * k) : g ∈ Subgroup.normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have e : g * k * g⁻¹ = k := by rw [← h k hk, mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    exact hk
  · intro hk
    have hc := h _ hk
    have e : k = g * k * g⁻¹ :=
      calc k = g⁻¹ * ((g * k * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * k * g⁻¹)) := by rw [hc]
        _ = g * k * g⁻¹ := by group
    rw [e]
    exact hk

theorem ae8c_u_mem (H : End18.Hyp Ω) (c : Chart Ω u) : u ∈ zGroup Ω :=
  (c.mem_zGroup_iff H ⟨u, c.mem⟩).mpr (by rw [c.u_eq]; rfl)

theorem ae8c_twin_out (H : End18.Hyp Ω) (c : Chart Ω u) {R : Subgroup G}
    (hR : R ∈ Generic.centMembers Ω u) :
    ∃ L ∈ twinSet Ω R, L ∉ Generic.centMembers Ω u := by
  by_contra hcon
  push Not at hcon
  obtain ⟨α, h, b, hlab⟩ := c.label R hR
  obtain ⟨L₁, hL₁P, hlab₁⟩ := c.label_surj α h true
  obtain ⟨L₂, hL₂P, hlab₂⟩ := c.label_surj α h false
  obtain ⟨wR, hwR, hwRY, hψR⟩ := ae8c_exists_inv hR.1 hR c hlab
  have hsub : twinSet Ω R ⊆ {L₁, L₂} := by
    intro M hM
    have hMP := hcon M hM
    obtain ⟨β, h', b', hlab'⟩ := c.label M hMP
    obtain ⟨z, hzR, hzM⟩ := hM.2
    obtain ⟨wM, hwM, hwMY, hψM⟩ := ae8c_exists_inv hM.1 hMP c hlab'
    have hwRM : wR = wM := (hzR.eq hwR).symm.trans (hzM.eq hwM)
    have hYeq : (⟨wR, hwRY⟩ : ↥(pSpan (Generic.centMembers Ω u))) = ⟨wM, hwMY⟩ :=
      Subtype.ext hwRM
    have hzeq : AE.zOf (AE.emb α h) = AE.zOf (AE.emb β h') := by
      rw [← hψR, ← hψM, hYeq]
    have hαβ : α = β := by
      have hv := congrArg (fun a : AE.Wr 6 => a.vec) hzeq
      ext i
      have hi := congrFun hv i
      simp only [AE.zOf_vec_apply, AE.range_emb] at hi
      by_cases hiα : i ∈ α <;> by_cases hiβ : i ∈ β <;> simp_all
    subst hαβ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    cases b' with
    | true => exact Or.inl (c.label_inj M hMP L₁ hL₁P (by rw [hlab', hlab₁]))
    | false => exact Or.inr (c.label_inj M hMP L₂ hL₂P (by rw [hlab', hlab₂]))
  have hle : (twinSet Ω R).ncard ≤ 2 :=
    (Set.ncard_le_ncard hsub).trans
      ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
  have h4 := H.ncard_twinSet hR.1
  omega

theorem ae8c_conj_mul_of_member (H : End18.Hyp Ω) (c : Chart Ω u) {R : Subgroup G}
    (hR : R ∈ Generic.centMembers Ω u) {zR : G} (hzR : IsUniqueInvolution R zR) :
    ∃ g : G, g * u * g⁻¹ = u * zR := by
  obtain ⟨L, hLtw, hLP⟩ := ae8c_twin_out H c hR
  have hLΩ : L ∈ Ω := hLtw.1
  have hLzR : IsUniqueInvolution L zR := by
    obtain ⟨z, hzR', hLz⟩ := hLtw.2
    rw [← hzR'.eq hzR]
    exact hLz
  have huD : u ∈ zGroup Ω := ae8c_u_mem H c
  have huN : u ∈ Subgroup.normalizer (L : Set G) := by
    have huR : u ∈ zGroup Ω ⊓ Subgroup.normalizer (R : Set G) :=
      ⟨huD, ae8c_mem_normalizer_of_comm (Generic.mem_centMembers_iff_commute.mp hR).2⟩
    rw [H.zGroup_inf_normalizer_eq hR.1 hLtw] at huR
    exact huR.2
  obtain ⟨k₀, hk₀L, hk₀⟩ : ∃ k₀ ∈ L, k₀ * u ≠ u * k₀ := by
    by_contra hcon
    push Not at hcon
    exact hLP (Generic.mem_centMembers_iff_commute.mpr ⟨hLΩ, hcon⟩)
  have huP : u ∈ pCore 2 G := H.endHyp.zGroup_le_pCore huD
  have hcm : u * k₀ * u⁻¹ * k₀⁻¹ ∈ L ⊓ pCore 2 G := by
    refine ⟨L.mul_mem ((Subgroup.mem_normalizer_iff.mp huN k₀).mp hk₀L) (L.inv_mem hk₀L), ?_⟩
    have e : u * k₀ * u⁻¹ * k₀⁻¹ = u * (k₀ * u⁻¹ * k₀⁻¹) := by group
    rw [e]
    exact (pCore 2 G).mul_mem huP
      ((inferInstance : (pCore 2 G).Normal).conj_mem u⁻¹ ((pCore 2 G).inv_mem huP) k₀)
  rw [H.inf_pCore hLΩ hLzR] at hcm
  have huu : u * u = 1 := H.endHyp.zGroup_mul_self H.perp9 u huD
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  rcases ae8c_zpowers_invol hLzR.sq hcm with h1 | h1
  · exfalso
    apply hk₀
    have h3 := mul_inv_eq_one.mp h1
    calc k₀ * u = (u * k₀ * u⁻¹) * u := by rw [h3]
      _ = u * k₀ := by group
  · refine ⟨k₀, ?_⟩
    rw [← h1]
    calc k₀ * u * k₀⁻¹ = (u * u) * (k₀ * u⁻¹ * k₀⁻¹) := by rw [huu, huinv, one_mul]
      _ = u * (u * k₀ * u⁻¹ * k₀⁻¹) := by group

theorem ae8c_wt2_conj (H : End18.Hyp Ω) {c : Chart Ω u} (co : Coords c)
    (x : ↥(zGroup Ω)) (hx : wt (co.e x).toAdd = 2) : ∃ g : G, (x : G) = g * u * g⁻¹ := by
  have huD : u ∈ zGroup Ω := ae8c_u_mem H c
  have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  set v : Fin 6 → ZMod 2 := (co.e x).toAdd with hv
  set α : Finset (Fin 6) := Finset.univ.filter (fun i => v i = 0) with hαdef
  have hαcard : α.card = 4 := by
    have h1 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 6))) (fun i => v i ≠ 0)
    simp only [Finset.card_univ, Fintype.card_fin, not_not] at h1
    unfold wt at hx
    rw [hαdef]
    omega
  obtain ⟨L, hLP, hlab⟩ := c.label_surj α hαcard true
  obtain ⟨w, hw, hwY, hψ⟩ := ae8c_exists_inv hLP.1 hLP c hlab
  have hwD : w ∈ zGroup Ω := ae8c_mem_zGroup hLP.1 hw
  obtain ⟨g, hg⟩ := ae8c_conj_mul_of_member H c hLP hw
  refine ⟨g, ?_⟩
  rw [hg]
  have key : co.e x = co.e (⟨u, huD⟩ * ⟨w, hwD⟩) := by
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, ae8c_co_u co huD c.mem, ae8c_co_of_inv co hwD hwY hψ]
    funext i
    show v i = 1 + (if i ∈ α then 1 else 0)
    rcases hcases (v i) with hvi | hvi
    · have hi : i ∈ α := by simp [hαdef, hvi]
      rw [if_pos hi, hvi]
      decide
    · have hi : i ∉ α := by simp [hαdef, hvi]
      rw [if_neg hi, hvi]
      decide
  have hx' : x = ⟨u, huD⟩ * ⟨w, hwD⟩ := co.e.injective key
  rw [hx']
  rfl

theorem ae8c_eq_one_of_wt_zero {c : Chart Ω u} (co : Coords c) {x : ↥(zGroup Ω)}
    (h : wt (co.e x).toAdd = 0) : x = 1 := by
  have hv : (co.e x).toAdd = 0 := by
    unfold wt at h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
    funext i
    simpa using h (Finset.mem_univ i)
  apply co.e.injective
  rw [map_one]
  apply Multiplicative.toAdd.injective
  rw [hv]
  rfl

theorem ae8c_eq_u_of_wt_six {c : Chart Ω u} (co : Coords c) (hu : u ∈ zGroup Ω)
    {x : ↥(zGroup Ω)} (h : wt (co.e x).toAdd = 6) : (x : G) = u := by
  have hv : (co.e x).toAdd = fun _ => 1 := by
    unfold wt at h
    have hall : Finset.univ.filter (fun i => (co.e x).toAdd i ≠ 0) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa using h)
    funext i
    have hi : i ∈ Finset.univ.filter (fun i => (co.e x).toAdd i ≠ 0) := by
      rw [hall]
      exact Finset.mem_univ i
    have hne := (Finset.mem_filter.mp hi).2
    rcases (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hne with h1
    exact h1
  have hxu : x = ⟨u, hu⟩ := by
    apply co.e.injective
    apply Multiplicative.toAdd.injective
    rw [ae8c_co_u co hu c.mem, hv]
  rw [hxu]

theorem z_class_even (H : End18.Hyp Ω) (x : ↥(zGroup Ω)) (hx : Even (wt (co.e x).toAdd)) :
    (∃ L ∈ Ω, IsUniqueInvolution L (x : G)) ↔ wt (co.e x).toAdd = 4 := by
  have hev : wt (co.e x).toAdd = 0 ∨ wt (co.e x).toAdd = 2 ∨ wt (co.e x).toAdd = 4 ∨
      wt (co.e x).toAdd = 6 := by
    have h6 := ae8c_wt_le (co.e x).toAdd
    obtain ⟨k, hk⟩ := hx
    omega
  constructor
  · rintro ⟨L, hL, hz⟩
    rcases hev with h0 | h2 | h4 | h6
    · exfalso
      rw [ae8c_eq_one_of_wt_zero co h0] at hz
      exact hz.ne_one rfl
    · exfalso
      obtain ⟨g, hg⟩ := ae8c_wt2_conj H co x h2
      exact ae8c_conj_u_not_Z H c g ⟨L, hL, hg ▸ hz⟩
    · exact h4
    · exfalso
      rw [ae8c_eq_u_of_wt_six co (ae8c_u_mem H c) h6] at hz
      exact ae8c_not_mem_Z H c ⟨L, hL, hz⟩
  · intro h4
    have hαcard : (Finset.univ.filter fun i => (co.e x).toAdd i ≠ 0).card = 4 := by
      unfold wt at h4
      exact h4
    obtain ⟨L, hLP, hlab⟩ := c.label_surj _ hαcard true
    obtain ⟨w, hw, hwY, hψ⟩ := ae8c_exists_inv hLP.1 hLP c hlab
    have hwD : w ∈ zGroup Ω := ae8c_mem_zGroup hLP.1 hw
    have hcoe : co.e ⟨w, hwD⟩ = co.e x := by
      apply Multiplicative.toAdd.injective
      rw [ae8c_co_of_inv co hwD hwY hψ]
      exact (ae8c_eq_indicator _).symm
    have hxw : (x : G) = w := congrArg Subtype.val (co.e.injective hcoe).symm
    exact ⟨L, hLP.1, by rw [hxw]; exact hw⟩

theorem u_class_even (H : End18.Hyp Ω) (hu : SectData Ω u) (x : ↥(zGroup Ω))
    (hx : Even (wt (co.e x).toAdd)) :
    (∃ g : G, (x : G) = g * u * g⁻¹) ↔ wt (co.e x).toAdd = 2 ∨ wt (co.e x).toAdd = 6 := by
  have hev : wt (co.e x).toAdd = 0 ∨ wt (co.e x).toAdd = 2 ∨ wt (co.e x).toAdd = 4 ∨
      wt (co.e x).toAdd = 6 := by
    have h6 := ae8c_wt_le (co.e x).toAdd
    obtain ⟨k, hk⟩ := hx
    omega
  constructor
  · rintro ⟨g, hg⟩
    rcases hev with h0 | h2 | h4 | h6
    · exfalso
      have hx1 : (x : G) = 1 := by
        rw [ae8c_eq_one_of_wt_zero co h0]
        rfl
      apply hu.ne_one
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = g⁻¹ * (x : G) * g := by rw [hg]
        _ = 1 := by rw [hx1]; group
    · exact Or.inl h2
    · exfalso
      obtain ⟨L, hL, hz⟩ := (z_class_even co H x hx).mpr h4
      exact ae8c_conj_u_not_Z H c g ⟨L, hL, hg ▸ hz⟩
    · exact Or.inr h6
  · rintro (h2 | h6)
    · exact ae8c_wt2_conj H co x h2
    · refine ⟨1, ?_⟩
      rw [inv_one, mul_one, one_mul]
      exact ae8c_eq_u_of_wt_six co (ae8c_u_mem H c) h6

theorem ae8c_double_count {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (D : Set G)
    (r : G → Subgroup G → Prop) (n c : ℕ)
    (hd : ∀ d ∈ D, {J | J ∈ Ω ∧ r d J}.ncard = n)
    (hJ : ∀ J ∈ Ω, {d | d ∈ D ∧ r d J}.ncard = c) :
    n * D.ncard = c * Ω.ncard := by
  classical
  have hΩf : Ω.Finite := Set.toFinite Ω
  have hDf : D.Finite := Set.toFinite D
  have hA : ∀ d ∈ D, (hΩf.toFinset.filter (fun J => r d J)).card = n := by
    intro d hdD
    rw [← hd d hdD, ← Set.ncard_coe_finset]
    congr 1
    ext J
    simp [Set.Finite.mem_toFinset]
  have hB : ∀ J ∈ Ω, (hDf.toFinset.filter (fun d => r d J)).card = c := by
    intro J hJΩ
    rw [← hJ J hJΩ, ← Set.ncard_coe_finset]
    congr 1
    ext d
    simp [Set.Finite.mem_toFinset]
  have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (r := r) (s := hDf.toFinset) (t := hΩf.toFinset)
  simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at key
  rw [Finset.sum_congr rfl (fun d hd' => hA d ((Set.Finite.mem_toFinset hDf).mp hd')),
    Finset.sum_congr rfl (fun J hJ' => hB J ((Set.Finite.mem_toFinset hΩf).mp hJ'))] at key
  simp only [Finset.sum_const, smul_eq_mul] at key
  rw [Set.ncard_eq_toFinset_card D hDf, Set.ncard_eq_toFinset_card Ω hΩf]
  linarith [key]

theorem ae8c_conj_eq_iff (g x y : G) : g * x * g⁻¹ = g * y * g⁻¹ ↔ x = y :=
  ⟨fun h => mul_left_cancel (mul_right_cancel h), fun h => by rw [h]⟩

theorem ae8c_centMembers_conj (hΩ : ConjInvariant Ω) (g a : G) :
    (Generic.centMembers Ω (g * a * g⁻¹)).ncard = (Generic.centMembers Ω a).ncard := by
  have hinj : Function.Injective (fun J : Subgroup G => conjSub g J) := by
    intro J J' h
    have e1 : ∀ K : Subgroup G, conjSub g⁻¹ (conjSub g K) = K := fun K => by
      simpa using conjSub_conjSub_inv g⁻¹ K
    have h' := congrArg (fun K : Subgroup G => conjSub g⁻¹ K) h
    simp only [e1] at h'
    exact h'
  have himg : Generic.centMembers Ω (g * a * g⁻¹) =
      (fun J : Subgroup G => conjSub g J) '' Generic.centMembers Ω a := by
    ext K
    constructor
    · intro hK
      rw [Generic.mem_centMembers_iff_commute] at hK
      refine ⟨conjSub g⁻¹ K, ?_, conjSub_conjSub_inv g K⟩
      rw [Generic.mem_centMembers_iff_commute]
      refine ⟨hΩ g⁻¹ K hK.1, fun j hj => ?_⟩
      have hk : g * j * g⁻¹ ∈ K := by
        have := mem_conjSub_iff.mp hj
        rwa [inv_inv] at this
      have hc := hK.2 _ hk
      exact (ae8c_conj_eq_iff g _ _).mp (by
        rw [show g * (j * a) * g⁻¹ = (g * j * g⁻¹) * (g * a * g⁻¹) by group,
          show g * (a * j) * g⁻¹ = (g * a * g⁻¹) * (g * j * g⁻¹) by group]
        exact hc)
    · rintro ⟨J, hJ, rfl⟩
      rw [Generic.mem_centMembers_iff_commute] at hJ ⊢
      refine ⟨hΩ g J hJ.1, fun k hk => ?_⟩
      obtain ⟨j, rfl⟩ : ∃ j, k = g * j * g⁻¹ := ⟨g⁻¹ * k * g, by group⟩
      have hjJ : j ∈ J := by
        have := mem_conjSub_iff.mp hk
        rwa [show g⁻¹ * (g * j * g⁻¹) * g = j by group] at this
      have hc := hJ.2 j hjJ
      rw [show g * j * g⁻¹ * (g * a * g⁻¹) = g * (j * a) * g⁻¹ by group,
        show (g * a * g⁻¹) * (g * j * g⁻¹) = g * (a * j) * g⁻¹ by group, hc]
  rw [himg, Set.ncard_image_of_injective _ hinj]

def ae8c_Zs (Ω : Set (Subgroup G)) : Set G := {x | ∃ L ∈ Ω, IsUniqueInvolution L x}

def ae8c_Ds (u : G) : Set G := {x | ∃ g : G, x = g * u * g⁻¹}

noncomputable def ae8c_xv {c : Chart Ω u} (co : Coords c) (v : Fin 6 → ZMod 2) : ↥(zGroup Ω) :=
  co.e.symm (Multiplicative.ofAdd v)

theorem ae8c_co_xv {c : Chart Ω u} (co : Coords c) (v : Fin 6 → ZMod 2) :
    (co.e (ae8c_xv co v)).toAdd = v := by
  simp [ae8c_xv]

theorem ae8c_xv_co {c : Chart Ω u} (co : Coords c) (x : ↥(zGroup Ω)) :
    ae8c_xv co (co.e x).toAdd = x := by
  simp [ae8c_xv]

theorem ae8c_xv_inj {c : Chart Ω u} (co : Coords c) {v w : Fin 6 → ZMod 2}
    (h : (ae8c_xv co v : G) = ae8c_xv co w) : v = w := by
  have h' : ae8c_xv co v = ae8c_xv co w := Subtype.ext h
  rw [← ae8c_co_xv co v, ← ae8c_co_xv co w, h']

theorem ae8c_exists_xv {c : Chart Ω u} (co : Coords c) {x : G} (hx : x ∈ zGroup Ω) :
    ∃ v : Fin 6 → ZMod 2, (ae8c_xv co v : G) = x := by
  refine ⟨(co.e ⟨x, hx⟩).toAdd, ?_⟩
  have h1 : ae8c_xv co (co.e ⟨x, hx⟩).toAdd = ⟨x, hx⟩ := by
    simp [ae8c_xv]
  exact congrArg Subtype.val h1

theorem ae8c_exists_y {c : Chart Ω u} {σ : Equiv.Perm (Fin 6)} (hσ : Equiv.Perm.sign σ = 1) :
    ∃ y : ↥(pSpan (Generic.centMembers Ω u)), (c.ψ y : AE.Wr 6).perm = σ := by
  have hmem : AE.Wr.ofPerm σ ∈ AE.aeSub 6 := by
    refine AE.mem_aeSub.mpr ⟨?_, ?_⟩
    · unfold AE.Wr.wsum
      simp [AE.Wr.ofPerm]
    · simpa [AE.Wr.ofPerm] using hσ
  refine ⟨c.ψ.symm ⟨AE.Wr.ofPerm σ, hmem⟩, ?_⟩
  simp [AE.Wr.ofPerm]

theorem ae8c_card_classes (S : Finset (Fin 6 → ZMod 2))
    (hS : ∀ v w : Fin 6 → ZMod 2, wt v = wt w → v ∈ S → w ∈ S) :
    S.card = ∑ k ∈ Finset.range 7,
      (if ∃ v ∈ S, wt v = k then (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = k).card
        else 0) := by
  classical
  have hmaps : ∀ v ∈ S, wt v ∈ Finset.range 7 := fun v _ => by
    rw [Finset.mem_range]
    have := ae8c_wt_le v
    omega
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hex
  · obtain ⟨v₀, hv₀, hwv⟩ := hex
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hk
      exact ⟨hS v₀ v (hwv.trans hk.symm) hv₀, hk⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv hk
    exact hex ⟨v, hv, hk⟩

theorem ae8c_arith (A1 A3 A5 B1 B3 B5 c : ℕ) (hc : c ≤ 7)
    (hA1 : A1 = 0 ∨ A1 = 6) (hA3 : A3 = 0 ∨ A3 = 20) (hA5 : A5 = 0 ∨ A5 = 6)
    (hB1 : B1 = 0 ∨ B1 = 6) (hB3 : B3 = 0 ∨ B3 = 20) (hB5 : B5 = 0 ∨ B5 = 6)
    (d1 : A1 = 0 ∨ B1 = 0) (d3 : A3 = 0 ∨ B3 = 0) (d5 : A5 = 0 ∨ B5 = 0)
    (heq : 15 * (16 + B1 + B3 + B5) = 2 * c * (15 + A1 + A3 + A5)) :
    A3 = 20 ∧ A1 = 0 ∧ A5 = 0 ∧ B1 = 6 ∧ B5 = 6 ∧ B3 = 0 ∧ c = 6 := by
  rcases hA1 with h1 | h1 <;> rcases hA3 with h3 | h3 <;> rcases hA5 with h5 | h5 <;>
    rcases hB1 with k1 | k1 <;> rcases hB3 with k3 | k3 <;> rcases hB5 with k5 | k5 <;>
    subst_vars <;> omega

open scoped Classical in
theorem ae8c_ncard_coords {c : Chart Ω u} (co : Coords c) (S : Set G) (hS : S ⊆ zGroup Ω) :
    S.ncard = (Finset.univ.filter fun v : Fin 6 → ZMod 2 => (ae8c_xv co v : G) ∈ S).card := by
  classical
  have hEq : S = (fun v : Fin 6 → ZMod 2 => (ae8c_xv co v : G)) ''
      {v | (ae8c_xv co v : G) ∈ S} := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv⟩ := ae8c_exists_xv co (hS hx)
      exact ⟨v, by simp [hv, hx], hv⟩
    · rintro ⟨v, hv, rfl⟩
      exact hv
  have hinj : Function.Injective (fun v : Fin 6 → ZMod 2 => (ae8c_xv co v : G)) := by
    intro v w h
    exact ae8c_xv_inj co h
  calc S.ncard = ((fun v : Fin 6 → ZMod 2 => (ae8c_xv co v : G)) ''
        {v | (ae8c_xv co v : G) ∈ S}).ncard := congrArg Set.ncard hEq
    _ = {v | (ae8c_xv co v : G) ∈ S}.ncard := Set.ncard_image_of_injective _ hinj
    _ = (Finset.univ.filter fun v : Fin 6 → ZMod 2 => (ae8c_xv co v : G) ∈ S).card := by
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext v
      simp

theorem ae8c_Ds_conj (g : G) {x : G} (hx : x ∈ ae8c_Ds u) : g * x * g⁻¹ ∈ ae8c_Ds u := by
  obtain ⟨h, rfl⟩ := hx
  exact ⟨g * h, by group⟩

theorem ae8c_Ds_sub (H : End18.Hyp Ω) (hu : u ∈ zGroup Ω) :
    ae8c_Ds u ⊆ zGroup Ω := by
  rintro x ⟨g, rfl⟩
  exact ae8c_conj_zGroup H.endHyp.thmD.hyp.conjInvariant g hu

theorem ae8c_comm_transfer (g j d : G) :
    (g * j * g⁻¹) * d = d * (g * j * g⁻¹) ↔ j * (g⁻¹ * d * g) = (g⁻¹ * d * g) * j := by
  have e1 : (g * j * g⁻¹) * d = g * (j * (g⁻¹ * d * g)) * g⁻¹ := by group
  have e2 : d * (g * j * g⁻¹) = g * ((g⁻¹ * d * g) * j) * g⁻¹ := by group
  rw [e1, e2]
  exact ae8c_conj_eq_iff g _ _

theorem ae8c_Zs_double (H : End18.Hyp Ω) : 4 * (ae8c_Zs Ω).ncard = Ω.ncard := by
  have h := ae8c_double_count Ω (ae8c_Zs Ω) (fun z J => IsUniqueInvolution J z) 4 1
    (fun z hz => by
      obtain ⟨L, hL, hzL⟩ := hz
      have hset : {J | J ∈ Ω ∧ IsUniqueInvolution J z} = twinSet Ω L := by
        ext J
        constructor
        · rintro ⟨hJ, hJz⟩
          exact ⟨hJ, z, hzL, hJz⟩
        · rintro ⟨hJ, z', hz'L, hJz'⟩
          exact ⟨hJ, (hz'L.eq hzL) ▸ hJz'⟩
      rw [hset, H.ncard_twinSet hL])
    (fun J hJ => by
      obtain ⟨z₀, hz₀⟩ := (H.endHyp.thmD.hyp.omega1 J hJ).1
      have hset : {z | z ∈ ae8c_Zs Ω ∧ IsUniqueInvolution J z} = {z₀} := by
        ext z
        constructor
        · rintro ⟨_, hz⟩
          exact hz.eq hz₀
        · rintro rfl
          exact ⟨⟨J, hJ, hz₀⟩, hz₀⟩
      rw [hset, Set.ncard_singleton])
  simpa using h

noncomputable def ae8c_cnt (u : G) (J : Subgroup G) : ℕ :=
  {d | d ∈ ae8c_Ds u ∧ ∀ j ∈ J, j * d = d * j}.ncard

theorem ae8c_cnt_conj (H : End18.Hyp Ω) {J J' : Subgroup G} (hJ : J ∈ Ω) (hJ' : J' ∈ Ω) :
    ae8c_cnt u J = ae8c_cnt u J' := by
  obtain ⟨g, hg⟩ := H.endHyp.thmD.trans J hJ J' hJ'
  unfold ae8c_cnt
  have himg : {d | d ∈ ae8c_Ds u ∧ ∀ j ∈ J', j * d = d * j} =
      (fun d => g * d * g⁻¹) '' {d | d ∈ ae8c_Ds u ∧ ∀ j ∈ J, j * d = d * j} := by
    ext d
    constructor
    · rintro ⟨hdD, hd⟩
      refine ⟨g⁻¹ * d * g⁻¹⁻¹, ⟨ae8c_Ds_conj g⁻¹ hdD, fun j hj => ?_⟩, ?_⟩
      · have hjJ' : g * j * g⁻¹ ∈ J' := by
          rw [← hg]
          exact conj_mem_conjSub hj
        have := hd _ hjJ'
        rw [inv_inv]
        exact (ae8c_comm_transfer g j d).mp this
      · simp only [inv_inv]
        group
    · rintro ⟨d₀, ⟨hd₀D, hd₀⟩, rfl⟩
      refine ⟨ae8c_Ds_conj g hd₀D, fun j' hj' => ?_⟩
      rw [← hg] at hj'
      have hj : g⁻¹ * j' * g ∈ J := mem_conjSub_iff.mp hj'
      have hc := hd₀ _ hj
      have hc' : (g⁻¹ * j' * g) * (g⁻¹ * (g * d₀ * g⁻¹) * g) =
          (g⁻¹ * (g * d₀ * g⁻¹) * g) * (g⁻¹ * j' * g) := by
        rw [show g⁻¹ * (g * d₀ * g⁻¹) * g = d₀ by group]
        exact hc
      have key := (ae8c_comm_transfer g (g⁻¹ * j' * g) (g * d₀ * g⁻¹)).mpr hc'
      rw [show g * (g⁻¹ * j' * g) * g⁻¹ = j' by group] at key
      exact key
  rw [himg, Set.ncard_image_of_injective _ (fun a b h => (ae8c_conj_eq_iff g a b).mp h)]

theorem ae8c_coord_perm {c : Chart Ω u} (co : Coords c) (H : End18.Hyp Ω) (S : Set G)
    (hS : ∀ x ∈ S, ∀ g : G, g * x * g⁻¹ ∈ S)
    {σ : Equiv.Perm (Fin 6)} (hσ : Equiv.Perm.sign σ = 1) {v w : Fin 6 → ZMod 2}
    (hw : ∀ i, w i = v (σ.symm i)) (hv : (ae8c_xv co v : G) ∈ S) :
    (ae8c_xv co w : G) ∈ S := by
  obtain ⟨y, hy⟩ := ae8c_exists_y (c := c) hσ
  have hyD : (y : G) * (ae8c_xv co v : G) * (y : G)⁻¹ ∈ zGroup Ω :=
    ae8c_conj_zGroup H.endHyp.thmD.hyp.conjInvariant (y : G) (ae8c_xv co v).2
  have hact := co.act y (ae8c_xv co v) ⟨_, hyD⟩ rfl
  have hcoe : (co.e ⟨_, hyD⟩).toAdd = w := by
    rw [hact, hy]
    funext i
    rw [ae8c_co_xv co v, hw i]
  have hxw : (⟨_, hyD⟩ : ↥(zGroup Ω)) = ae8c_xv co w := by
    apply co.e.injective
    apply Multiplicative.toAdd.injective
    rw [ae8c_co_xv]
    exact hcoe
  have hmem : (ae8c_xv co w : G) = (y : G) * (ae8c_xv co v : G) * (y : G)⁻¹ := by
    rw [← hxw]
  rw [hmem]
  exact hS _ hv _

theorem ae8c_Zs_class {c : Chart Ω u} (co : Coords c) (H : End18.Hyp Ω) {v w : Fin 6 → ZMod 2}
    (hvw : wt v = wt w) (hv : (ae8c_xv co v : G) ∈ ae8c_Zs Ω) :
    (ae8c_xv co w : G) ∈ ae8c_Zs Ω := by
  obtain ⟨σ, hσ, hw⟩ := ae8c_alt_transitive hvw
  refine ae8c_coord_perm co H (ae8c_Zs Ω) ?_ hσ hw hv
  intro x hx g
  obtain ⟨L, hL, hz⟩ := hx
  exact ae8c_conj_Z H.endHyp.thmD.hyp.conjInvariant (g := g) ⟨L, hL, hz⟩

theorem ae8c_Ds_class {c : Chart Ω u} (co : Coords c) (H : End18.Hyp Ω) {v w : Fin 6 → ZMod 2}
    (hvw : wt v = wt w) (hv : (ae8c_xv co v : G) ∈ ae8c_Ds u) :
    (ae8c_xv co w : G) ∈ ae8c_Ds u := by
  obtain ⟨σ, hσ, hw⟩ := ae8c_alt_transitive hvw
  exact ae8c_coord_perm co H (ae8c_Ds u) (fun x hx g => ae8c_Ds_conj g hx) hσ hw hv

theorem ae8c_cnt_le (H : End18.Hyp Ω) (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) {c : Chart Ω u}
    (co : Coords c) {J : Subgroup G} (hJ : J ∈ Ω) : ae8c_cnt u J ≤ 7 := by
  classical
  have hD : Nat.card ↥(zGroup Ω) = 64 := by
    rw [Nat.card_congr co.e.toEquiv, Nat.card_eq_fintype_card]
    simp
  have h8 := H.card_inf_centralizer_mul_eight hJ
  rw [hD] at h8
  have hcoe : Nat.card ↥(zGroup Ω ⊓ Subgroup.centralizer (J : Set G)) =
      ((zGroup Ω ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G).ncard :=
    Nat.card_coe_set_eq _
  have hC : ((zGroup Ω ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G).ncard = 8 := by
    rw [← hcoe]
    omega
  have hone : (1 : G) ∉ {d | d ∈ ae8c_Ds u ∧ ∀ j ∈ J, j * d = d * j} := by
    rintro ⟨⟨g, hg⟩, -⟩
    apply hu1
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [← hg]; group
  have hsub : {d | d ∈ ae8c_Ds u ∧ ∀ j ∈ J, j * d = d * j} ∪ {1} ⊆
      ((zGroup Ω ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) : Set G) := by
    rintro d (⟨hdD, hdC⟩ | rfl)
    · refine ⟨ae8c_Ds_sub H hu hdD, ?_⟩
      exact Subgroup.mem_centralizer_iff.mpr (fun j hj => hdC j hj)
    · exact ⟨one_mem _, one_mem _⟩
  have hdisj : Disjoint {d | d ∈ ae8c_Ds u ∧ ∀ j ∈ J, j * d = d * j} ({1} : Set G) := by
    rw [Set.disjoint_singleton_right]
    exact hone
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton, hC]
    at hle
  unfold ae8c_cnt
  omega

theorem ae8c_counting (H : End18.Hyp Ω) (hu : SectData Ω u) {c : Chart Ω u} (co : Coords c) :
    ∃ c0 : ℕ, c0 ≤ 7 ∧ 15 * (ae8c_Ds u).ncard = 2 * c0 * (ae8c_Zs Ω).ncard := by
  obtain ⟨J₀, hJ₀, -⟩ := H.endHyp.exists_ne
  have hdbl : 30 * (ae8c_Ds u).ncard = ae8c_cnt u J₀ * Ω.ncard := by
    apply ae8c_double_count Ω (ae8c_Ds u) (fun d J => ∀ j ∈ J, j * d = d * j) 30
      (ae8c_cnt u J₀)
    · intro d hd
      obtain ⟨g, rfl⟩ := hd
      have hset : {J | J ∈ Ω ∧ ∀ j ∈ J, j * (g * u * g⁻¹) = (g * u * g⁻¹) * j} =
          Generic.centMembers Ω (g * u * g⁻¹) := by
        ext J
        rw [Generic.mem_centMembers_iff_commute]
        rfl
      rw [hset, ae8c_centMembers_conj H.endHyp.thmD.hyp.conjInvariant g u,
        c.ncard_centMembers]
    · intro J hJ
      exact ae8c_cnt_conj H hJ hJ₀
  have hZ := ae8c_Zs_double H
  refine ⟨ae8c_cnt u J₀, ae8c_cnt_le H hu.mem hu.ne_one co hJ₀, ?_⟩
  rw [← hZ] at hdbl
  linarith

theorem ae8c_Zs_Ds_disj (H : End18.Hyp Ω) (c : Chart Ω u) {x : G}
    (hZ : x ∈ ae8c_Zs Ω) (hD : x ∈ ae8c_Ds u) : False := by
  obtain ⟨g, rfl⟩ := hD
  obtain ⟨L, hL, hz⟩ := hZ
  exact ae8c_conj_u_not_Z H c g ⟨L, hL, hz⟩

theorem ae8c_Zs_sub (H : End18.Hyp Ω) : ae8c_Zs Ω ⊆ zGroup Ω := by
  rintro x ⟨L, hL, hz⟩
  exact ae8c_mem_zGroup hL hz

theorem ae8c_classes (H : End18.Hyp Ω) (hu : SectData Ω u) {c : Chart Ω u} (co : Coords c) :
    (∀ v : Fin 6 → ZMod 2, (ae8c_xv co v : G) ∈ ae8c_Zs Ω ↔ wt v = 3 ∨ wt v = 4) ∧
    (∀ v : Fin 6 → ZMod 2, (ae8c_xv co v : G) ∈ ae8c_Ds u ↔
      wt v = 1 ∨ wt v = 2 ∨ wt v = 5 ∨ wt v = 6) := by
  classical
  obtain ⟨c0, hc0, hcount⟩ := ae8c_counting H hu co
  set Zc : Finset (Fin 6 → ZMod 2) :=
    Finset.univ.filter fun v => (ae8c_xv co v : G) ∈ ae8c_Zs Ω with hZc
  set Dc : Finset (Fin 6 → ZMod 2) :=
    Finset.univ.filter fun v => (ae8c_xv co v : G) ∈ ae8c_Ds u with hDc
  have hZmem : ∀ v, v ∈ Zc ↔ (ae8c_xv co v : G) ∈ ae8c_Zs Ω := fun v => by
    simp [hZc]
  have hDmem : ∀ v, v ∈ Dc ↔ (ae8c_xv co v : G) ∈ ae8c_Ds u := fun v => by
    simp [hDc]
  have hZn : (ae8c_Zs Ω).ncard = Zc.card := ae8c_ncard_coords co _ (ae8c_Zs_sub H)
  have hDn : (ae8c_Ds u).ncard = Dc.card :=
    ae8c_ncard_coords co _ (ae8c_Ds_sub H hu.mem)
  have hZcard : Zc.card = ∑ k ∈ Finset.range 7,
      (if ∃ v ∈ Zc, wt v = k then (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = k).card
        else 0) :=
    ae8c_card_classes Zc (fun v w h hv => (hZmem w).mpr
      (ae8c_Zs_class co H h ((hZmem v).mp hv)))
  have hDcard : Dc.card = ∑ k ∈ Finset.range 7,
      (if ∃ v ∈ Dc, wt v = k then (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = k).card
        else 0) :=
    ae8c_card_classes Dc (fun v w h hv => (hDmem w).mpr
      (ae8c_Ds_class co H h ((hDmem v).mp hv)))
  have C0 : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = 0).card = 1 := by decide
  have C1 : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = 1).card = 6 := by decide
  have C2 : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = 2).card = 15 := by decide
  have C3 : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = 3).card = 20 := by decide
  have C4 : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = 4).card = 15 := by decide
  have C5 : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = 5).card = 6 := by decide
  have C6 : (Finset.univ.filter fun v : Fin 6 → ZMod 2 => wt v = 6).card = 1 := by decide
  have hpz0 : ¬ ∃ v ∈ Zc, wt v = 0 := by
    rintro ⟨v, hv, hk⟩
    have h1 : (ae8c_xv co v : G) = 1 := by
      have := ae8c_eq_one_of_wt_zero co (x := ae8c_xv co v) (by rw [ae8c_co_xv]; exact hk)
      rw [this]
      rfl
    obtain ⟨L, hL, hz⟩ := (hZmem v).mp hv
    rw [h1] at hz
    exact hz.ne_one rfl
  have hpz2 : ¬ ∃ v ∈ Zc, wt v = 2 := by
    rintro ⟨v, hv, hk⟩
    have hev : Even (wt (co.e (ae8c_xv co v)).toAdd) := by
      rw [ae8c_co_xv, hk]
      decide
    have h4 := (z_class_even co H (ae8c_xv co v) hev).mp ((hZmem v).mp hv)
    rw [ae8c_co_xv, hk] at h4
    omega
  have hpz4 : ∃ v ∈ Zc, wt v = 4 := by
    have hev : Even (wt (co.e (ae8c_xv co ![1, 1, 1, 1, 0, 0])).toAdd) := by
      rw [ae8c_co_xv]
      decide
    have hmem := (z_class_even co H (ae8c_xv co ![1, 1, 1, 1, 0, 0]) hev).mpr (by
      rw [ae8c_co_xv]
      decide)
    exact ⟨![1, 1, 1, 1, 0, 0], (hZmem _).mpr hmem, by decide⟩
  have hpz6 : ¬ ∃ v ∈ Zc, wt v = 6 := by
    rintro ⟨v, hv, hk⟩
    have hx := ae8c_eq_u_of_wt_six co (ae8c_u_mem H c) (x := ae8c_xv co v)
      (by rw [ae8c_co_xv]; exact hk)
    obtain ⟨L, hL, hz⟩ := (hZmem v).mp hv
    rw [hx] at hz
    exact ae8c_not_mem_Z H c ⟨L, hL, hz⟩
  have hqz0 : ¬ ∃ v ∈ Dc, wt v = 0 := by
    rintro ⟨v, hv, hk⟩
    have h1 : (ae8c_xv co v : G) = 1 := by
      have := ae8c_eq_one_of_wt_zero co (x := ae8c_xv co v) (by rw [ae8c_co_xv]; exact hk)
      rw [this]
      rfl
    obtain ⟨g, hg⟩ := (hDmem v).mp hv
    apply hu.ne_one
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [← hg, h1]; group
  have hqz2 : ∃ v ∈ Dc, wt v = 2 := by
    have hev : Even (wt (co.e (ae8c_xv co ![1, 1, 0, 0, 0, 0])).toAdd) := by
      rw [ae8c_co_xv]
      decide
    have hmem := (u_class_even co H hu (ae8c_xv co ![1, 1, 0, 0, 0, 0]) hev).mpr
      (Or.inl (by rw [ae8c_co_xv]; decide))
    exact ⟨![1, 1, 0, 0, 0, 0], (hDmem _).mpr hmem, by decide⟩
  have hqz4 : ¬ ∃ v ∈ Dc, wt v = 4 := by
    rintro ⟨v, hv, hk⟩
    have hev : Even (wt (co.e (ae8c_xv co v)).toAdd) := by
      rw [ae8c_co_xv, hk]
      decide
    have h := (u_class_even co H hu (ae8c_xv co v) hev).mp ((hDmem v).mp hv)
    rw [ae8c_co_xv, hk] at h
    omega
  have hqz6 : ∃ v ∈ Dc, wt v = 6 := by
    have hx := ae8c_eq_u_of_wt_six co (ae8c_u_mem H c)
      (x := ae8c_xv co ![1, 1, 1, 1, 1, 1]) (by rw [ae8c_co_xv]; decide)
    refine ⟨![1, 1, 1, 1, 1, 1], (hDmem _).mpr ⟨1, ?_⟩, by decide⟩
    rw [hx]
    simp
  have hdisj : ∀ k, (∃ v ∈ Zc, wt v = k) → (∃ v ∈ Dc, wt v = k) → False := by
    rintro k ⟨v, hv, hk⟩ ⟨w, hw, hk'⟩
    have hwZ : w ∈ Zc := (hZmem w).mpr
      (ae8c_Zs_class co H (hk.trans hk'.symm) ((hZmem v).mp hv))
    exact ae8c_Zs_Ds_disj H c ((hZmem w).mp hwZ) ((hDmem w).mp hw)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, C0, C1, C2, C3, C4, C5, C6,
    hpz0, hpz2, hpz4, hpz6, hqz0, hqz2, hqz4, hqz6, if_true, if_false, zero_add] at hZcard hDcard
  set P1 := ∃ v ∈ Zc, wt v = 1 with hP1def
  set P3 := ∃ v ∈ Zc, wt v = 3 with hP3def
  set P5 := ∃ v ∈ Zc, wt v = 5 with hP5def
  set Q1 := ∃ v ∈ Dc, wt v = 1 with hQ1def
  set Q3 := ∃ v ∈ Dc, wt v = 3 with hQ3def
  set Q5 := ∃ v ∈ Dc, wt v = 5 with hQ5def
  have hZsum : Zc.card = 15 + (if P1 then 6 else 0) + (if P3 then 20 else 0) +
      (if P5 then 6 else 0) := by
    rw [hZcard]
    split_ifs <;> omega
  have hDsum : Dc.card = 16 + (if Q1 then 6 else 0) + (if Q3 then 20 else 0) +
      (if Q5 then 6 else 0) := by
    rw [hDcard]
    split_ifs <;> omega
  have hdbl : 15 * Dc.card = 2 * c0 * Zc.card := by
    rw [← hDn, ← hZn]
    linarith [hcount]
  have d1 : ¬(P1 ∧ Q1) := fun h => hdisj 1 h.1 h.2
  have d3 : ¬(P3 ∧ Q3) := fun h => hdisj 3 h.1 h.2
  have d5 : ¬(P5 ∧ Q5) := fun h => hdisj 5 h.1 h.2
  have hA1 : (if P1 then 6 else 0) = 0 ∨ (if P1 then 6 else 0) = 6 := by
    by_cases h : P1 <;> simp [h]
  have hA3 : (if P3 then 20 else 0) = 0 ∨ (if P3 then 20 else 0) = 20 := by
    by_cases h : P3 <;> simp [h]
  have hA5 : (if P5 then 6 else 0) = 0 ∨ (if P5 then 6 else 0) = 6 := by
    by_cases h : P5 <;> simp [h]
  have hB1 : (if Q1 then 6 else 0) = 0 ∨ (if Q1 then 6 else 0) = 6 := by
    by_cases h : Q1 <;> simp [h]
  have hB3 : (if Q3 then 20 else 0) = 0 ∨ (if Q3 then 20 else 0) = 20 := by
    by_cases h : Q3 <;> simp [h]
  have hB5 : (if Q5 then 6 else 0) = 0 ∨ (if Q5 then 6 else 0) = 6 := by
    by_cases h : Q5 <;> simp [h]
  have e1 : (if P1 then 6 else 0) = 0 ∨ (if Q1 then 6 else 0) = 0 := by
    rcases not_and_or.mp d1 with h | h
    · left; simp [h]
    · right; simp [h]
  have e3 : (if P3 then 20 else 0) = 0 ∨ (if Q3 then 20 else 0) = 0 := by
    rcases not_and_or.mp d3 with h | h
    · left; simp [h]
    · right; simp [h]
  have e5 : (if P5 then 6 else 0) = 0 ∨ (if Q5 then 6 else 0) = 0 := by
    rcases not_and_or.mp d5 with h | h
    · left; simp [h]
    · right; simp [h]
  rw [hDsum, hZsum] at hdbl
  obtain ⟨hA3e, hA1e, hA5e, hB1e, hB5e, hB3e, hc6⟩ := ae8c_arith _ _ _ _ _ _ c0 hc0 hA1 hA3
    hA5 hB1 hB3 hB5 e1 e3 e5 hdbl
  have hP3 : P3 := by
    by_contra h
    simp [h] at hA3e
  have hP1 : ¬P1 := by
    intro h
    simp [h] at hA1e
  have hP5 : ¬P5 := by
    intro h
    simp [h] at hA5e
  have hQ1 : Q1 := by
    by_contra h
    simp [h] at hB1e
  have hQ5 : Q5 := by
    by_contra h
    simp [h] at hB5e
  have hQ3 : ¬Q3 := by
    intro h
    simp [h] at hB3e
  have hPk : ∀ k, k < 7 → ((∃ w ∈ Zc, wt w = k) ↔ (k = 3 ∨ k = 4)) := by
    intro k hk
    interval_cases k
    · exact ⟨fun h => absurd h hpz0, fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h hP1, fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h hpz2, fun h => absurd h (by omega)⟩
    · exact ⟨fun _ => by simp, fun _ => hP3⟩
    · exact ⟨fun _ => by simp, fun _ => hpz4⟩
    · exact ⟨fun h => absurd h hP5, fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h hpz6, fun h => absurd h (by omega)⟩
  have hQk : ∀ k, k < 7 → ((∃ w ∈ Dc, wt w = k) ↔ (k = 1 ∨ k = 2 ∨ k = 5 ∨ k = 6)) := by
    intro k hk
    interval_cases k
    · exact ⟨fun h => absurd h hqz0, fun h => absurd h (by omega)⟩
    · exact ⟨fun _ => by simp, fun _ => hQ1⟩
    · exact ⟨fun _ => by simp, fun _ => hqz2⟩
    · exact ⟨fun h => absurd h hQ3, fun h => absurd h (by omega)⟩
    · exact ⟨fun h => absurd h hqz4, fun h => absurd h (by omega)⟩
    · exact ⟨fun _ => by simp, fun _ => hQ5⟩
    · exact ⟨fun _ => by simp, fun _ => hqz6⟩
  constructor
  · intro v
    have hlt : wt v < 7 := by
      have := ae8c_wt_le v
      omega
    constructor
    · intro hv
      exact (hPk (wt v) hlt).mp ⟨v, (hZmem v).mpr hv, rfl⟩
    · intro hw
      obtain ⟨w, hw', hwv⟩ := (hPk (wt v) hlt).mpr hw
      exact ae8c_Zs_class co H hwv ((hZmem w).mp hw')
  · intro v
    have hlt : wt v < 7 := by
      have := ae8c_wt_le v
      omega
    constructor
    · intro hv
      exact (hQk (wt v) hlt).mp ⟨v, (hDmem v).mpr hv, rfl⟩
    · intro hw
      obtain ⟨w, hw', hwv⟩ := (hQk (wt v) hlt).mpr hw
      exact ae8c_Ds_class co H hwv ((hDmem w).mp hw')

theorem z_odd_cases (H : End18.Hyp Ω) (hu : SectData Ω u) :
    (∀ x : ↥(zGroup Ω), Odd (wt (co.e x).toAdd) →
      ((∃ L ∈ Ω, IsUniqueInvolution L (x : G)) ↔ wt (co.e x).toAdd = 3)) ∨
    (∀ x : ↥(zGroup Ω), Odd (wt (co.e x).toAdd) →
      ((∃ L ∈ Ω, IsUniqueInvolution L (x : G)) ↔
        wt (co.e x).toAdd = 1 ∨ wt (co.e x).toAdd = 5)) := by
  left
  intro x hx
  have hcl := (ae8c_classes H hu co).1 (co.e x).toAdd
  rw [ae8c_xv_co co x] at hcl
  obtain ⟨k, hk⟩ := hx
  constructor
  · intro h
    have h3 := hcl.mp h
    omega
  · intro h
    exact hcl.mpr (by omega)

end Coords

open Coords in
theorem exists_classes (H : End18.Hyp Ω) (hu : SectData Ω u) {c : Chart Ω u} (co : Coords c) :
    Classes co := by
  obtain ⟨hZ, hD⟩ := ae8c_classes H hu co
  have hzc : ∀ x : G, (∃ L ∈ Ω, IsUniqueInvolution L x) ↔
      ∃ hx : x ∈ zGroup Ω, wt (co.e ⟨x, hx⟩).toAdd = 3 ∨ wt (co.e ⟨x, hx⟩).toAdd = 4 := by
    intro x
    constructor
    · rintro ⟨L, hL, hz⟩
      have hx : x ∈ zGroup Ω := ae8c_mem_zGroup hL hz
      refine ⟨hx, ?_⟩
      have h := hZ (co.e ⟨x, hx⟩).toAdd
      rw [ae8c_xv_co co ⟨x, hx⟩] at h
      exact h.mp ⟨L, hL, hz⟩
    · rintro ⟨hx, hwt⟩
      have h := hZ (co.e ⟨x, hx⟩).toAdd
      rw [ae8c_xv_co co ⟨x, hx⟩] at h
      exact h.mpr hwt
  have hdc : ∀ x : G, (∃ g : G, x = g * u * g⁻¹) ↔
      ∃ hx : x ∈ zGroup Ω, wt (co.e ⟨x, hx⟩).toAdd = 1 ∨ wt (co.e ⟨x, hx⟩).toAdd = 2 ∨
        wt (co.e ⟨x, hx⟩).toAdd = 5 ∨ wt (co.e ⟨x, hx⟩).toAdd = 6 := by
    intro x
    constructor
    · rintro ⟨g, hg⟩
      have hx : x ∈ zGroup Ω := ae8c_Ds_sub H hu.mem ⟨g, hg⟩
      refine ⟨hx, ?_⟩
      have h := hD (co.e ⟨x, hx⟩).toAdd
      rw [ae8c_xv_co co ⟨x, hx⟩] at h
      exact h.mp ⟨g, hg⟩
    · rintro ⟨hx, hwt⟩
      have h := hD (co.e ⟨x, hx⟩).toAdd
      rw [ae8c_xv_co co ⟨x, hx⟩] at h
      exact h.mpr hwt
  exact ⟨hzc, hdc⟩

@[expose] def Delta (u : G) : Set G := {x | ∃ g : G, x = g * u * g⁻¹}

abbrev ae8c_e89_good (v : Fin 6 → ZMod 2) : Prop :=
  wt v = 1 ∨ wt v = 2 ∨ wt v = 5 ∨ wt v = 6

private lemma ae8c_e89_card_good :
    (Finset.univ.filter fun v : Fin 6 → ZMod 2 => ae8c_e89_good v ∧ True).card = 28 := by
  decide

private lemma ae8c_e89_wt_one (v : Fin 6 → ZMod 2) (h : wt v = 1) :
    ∃ c : Fin 6, v = Pi.single c 1 :=
  (by decide : ∀ v : Fin 6 → ZMod 2, wt v = 1 → ∃ c : Fin 6, v = Pi.single c 1) v h

private lemma ae8c_e89_wt_five (v : Fin 6 → ZMod 2) (h : wt v = 5) :
    ∃ d : Fin 6, v = 1 + Pi.single d 1 :=
  (by decide : ∀ v : Fin 6 → ZMod 2, wt v = 5 → ∃ d : Fin 6, v = 1 + Pi.single d 1) v h

private lemma ae8c_e89_not_good_add_self (v : Fin 6 → ZMod 2) : ¬ ae8c_e89_good (v + v) :=
  (by decide : ∀ v : Fin 6 → ZMod 2, ¬ ae8c_e89_good (v + v)) v

private lemma ae8c_e89_good_unit_sum (c d : Fin 6) (h : c ≠ d) :
    ae8c_e89_good (Pi.single c 1 + Pi.single d 1) :=
  (by decide : ∀ c d : Fin 6, c ≠ d → ae8c_e89_good (Pi.single c 1 + Pi.single d 1)) c d h

private lemma ae8c_e89_good_five_sum (c d : Fin 6) (h : c ≠ d) :
    ae8c_e89_good ((1 + Pi.single c 1) + (1 + Pi.single d 1)) :=
  (by decide : ∀ c d : Fin 6, c ≠ d →
    ae8c_e89_good ((1 + Pi.single c 1) + (1 + Pi.single d 1))) c d h

private lemma ae8c_e89_good_unit_five (c d : Fin 6) :
    ae8c_e89_good (Pi.single c 1 + (1 + Pi.single d 1)) ↔ c = d :=
  (by decide : ∀ c d : Fin 6,
    (ae8c_e89_good (Pi.single c 1 + (1 + Pi.single d 1)) ↔ c = d)) c d

private lemma ae8c_e89_good_one_add (v : Fin 6 → ZMod 2) (hv : ae8c_e89_good v) :
    ae8c_e89_good (1 + v) ↔ (wt v = 1 ∨ wt v = 5) :=
  (by decide : ∀ v : Fin 6 → ZMod 2, ae8c_e89_good v →
    (ae8c_e89_good (1 + v) ↔ (wt v = 1 ∨ wt v = 5))) v hv

private lemma ae8c_e89_good_one : ae8c_e89_good (1 : Fin 6 → ZMod 2) := by
  decide

private lemma ae8c_e89_mem_zGroup {c : Chart Ω u} {co : Coords c} (cl : Classes co) {x : G}
    (hx : x ∈ Delta u) : x ∈ zGroup Ω := by
  obtain ⟨h, -⟩ := (cl.u_class x).1 hx
  exact h

private noncomputable def ae8c_e89_coord {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    (y : ↥(Delta u)) : Fin 6 → ZMod 2 :=
  (co.e ⟨y.1, ae8c_e89_mem_zGroup cl y.2⟩).toAdd

private abbrev ae8c_e89_adj (x y : ↥(Delta u)) : Prop := (x : G) * (y : G) ∈ Delta u

private lemma ae8c_e89_adj_iff {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    (y₁ y₂ : ↥(Delta u)) :
    ae8c_e89_adj y₁ y₂ ↔ ae8c_e89_good (ae8c_e89_coord cl y₁ + ae8c_e89_coord cl y₂) := by
  have hm : (y₁ : G) * (y₂ : G) ∈ zGroup Ω :=
    mul_mem (ae8c_e89_mem_zGroup cl y₁.2) (ae8c_e89_mem_zGroup cl y₂.2)
  have key : ∀ hx : (y₁ : G) * (y₂ : G) ∈ zGroup Ω,
      (co.e ⟨(y₁ : G) * (y₂ : G), hx⟩).toAdd =
        ae8c_e89_coord cl y₁ + ae8c_e89_coord cl y₂ := by
    intro hx
    unfold ae8c_e89_coord
    rw [← toAdd_mul, ← map_mul co.e]
    rfl
  constructor
  · intro h
    obtain ⟨hx, hg⟩ := (cl.u_class ((y₁ : G) * (y₂ : G))).1 h
    rw [key hx] at hg
    exact hg
  · intro hg
    refine (cl.u_class ((y₁ : G) * (y₂ : G))).2 ⟨hm, ?_⟩
    rw [key hm]
    exact hg

private lemma ae8c_e89_coord_good {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    (y : ↥(Delta u)) : ae8c_e89_good (ae8c_e89_coord cl y) := by
  obtain ⟨_, hg⟩ := (cl.u_class (y : G)).1 y.2
  exact hg

private lemma ae8c_e89_coord_inj {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    {y₁ y₂ : ↥(Delta u)} (h : ae8c_e89_coord cl y₁ = ae8c_e89_coord cl y₂) : y₁ = y₂ := by
  unfold ae8c_e89_coord at h
  have h1 := co.e.injective (Multiplicative.toAdd.injective h)
  have h2 : (y₁ : G) = (y₂ : G) := congrArg (fun z : ↥(zGroup Ω) => (z : G)) h1
  exact Subtype.ext h2

private lemma ae8c_e89_coord_surj {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    {v : Fin 6 → ZMod 2} (hv : ae8c_e89_good v) :
    ∃ y : ↥(Delta u), ae8c_e89_coord cl y = v := by
  obtain ⟨z, hzv⟩ : ∃ z : ↥(zGroup Ω), (co.e z).toAdd = v :=
    ⟨co.e.symm (Multiplicative.ofAdd v), by simp⟩
  have hmem : (z : G) ∈ Delta u := by
    refine (cl.u_class (z : G)).2 ⟨z.2, ?_⟩
    change ae8c_e89_good (co.e z).toAdd
    rw [hzv]
    exact hv
  exact ⟨⟨(z : G), hmem⟩, hzv⟩

private lemma ae8c_e89_card_filter {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    [Fintype ↥(Delta u)] (P : (Fin 6 → ZMod 2) → Prop) [DecidablePred P] :
    (Finset.univ.filter fun y : ↥(Delta u) => P (ae8c_e89_coord cl y)).card =
      (Finset.univ.filter fun v : Fin 6 → ZMod 2 => ae8c_e89_good v ∧ P v).card := by
  apply Finset.card_nbij (ae8c_e89_coord cl)
  · intro y hy
    have hP := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    exact Finset.mem_coe.2
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, ae8c_e89_coord_good cl y, hP⟩)
  · intro y₁ _ y₂ _ h
    exact ae8c_e89_coord_inj cl h
  · intro v hv
    have hv' := (Finset.mem_filter.1 (Finset.mem_coe.1 hv)).2
    obtain ⟨y, hy⟩ := ae8c_e89_coord_surj cl hv'.1
    refine ⟨y, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩), hy⟩
    show P (ae8c_e89_coord cl y)
    rw [hy]
    exact hv'.2

private lemma ae8c_e89_card_delta {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    [Fintype ↥(Delta u)] : (Finset.univ : Finset ↥(Delta u)).card = 28 := by
  calc (Finset.univ : Finset ↥(Delta u)).card
      = (Finset.univ.filter fun _ : ↥(Delta u) => True).card := by simp
    _ = (Finset.univ.filter fun v : Fin 6 → ZMod 2 => ae8c_e89_good v ∧ True).card :=
        ae8c_e89_card_filter cl (fun _ => True)
    _ = 28 := ae8c_e89_card_good

private def ae8c_e89_Loc {D : Type*} [DecidableEq D] (adj : D → D → Prop) (x : D) : Prop :=
  ∃ A B : Finset D, A.card = 6 ∧ B.card = 6 ∧ Disjoint A B ∧
    (∀ v, adj x v ↔ v ∈ A ∪ B) ∧ (∀ v ∈ A, ∀ w ∈ A, v ≠ w → adj v w) ∧
    (∀ v ∈ B, ∀ w ∈ B, v ≠ w → adj v w) ∧
    (∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, adj a b → adj a' b → a = a') ∧
    (∀ b ∈ B, ∀ b' ∈ B, ∀ a ∈ A, adj a b → adj a b' → b = b')

private lemma ae8c_e89_Loc_map {D : Type*} [DecidableEq D] (adj : D → D → Prop)
    (σ : D ≃ D) (hσ : ∀ a b, adj (σ a) (σ b) ↔ adj a b) {x : D}
    (h : ae8c_e89_Loc adj x) : ae8c_e89_Loc adj (σ x) := by
  obtain ⟨A, B, hA, hB, hdisj, hnbr, hAcl, hBcl, hmA, hmB⟩ := h
  refine ⟨A.map σ.toEmbedding, B.map σ.toEmbedding, by simpa using hA, by simpa using hB,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    intro v hvA hvB
    rw [Finset.mem_map_equiv] at hvA hvB
    exact Finset.disjoint_left.1 hdisj hvA hvB
  · intro v
    have key : adj (σ x) v ↔ adj x (σ.symm v) := by
      have h := hσ x (σ.symm v)
      rwa [σ.apply_symm_apply] at h
    rw [key, hnbr]
    simp [Finset.mem_union, Finset.mem_map_equiv]
  · intro v hv w hw hne
    rw [Finset.mem_map_equiv] at hv hw
    have h1 := hAcl _ hv _ hw (σ.symm.injective.ne hne)
    have h2 := (hσ _ _).2 h1
    simpa using h2
  · intro v hv w hw hne
    rw [Finset.mem_map_equiv] at hv hw
    have h1 := hBcl _ hv _ hw (σ.symm.injective.ne hne)
    have h2 := (hσ _ _).2 h1
    simpa using h2
  · intro a ha a' ha' b hb hab hab'
    rw [Finset.mem_map_equiv] at ha ha' hb
    have h1 := hmA _ ha _ ha' _ hb ((hσ _ _).1 (by simpa using hab))
      ((hσ _ _).1 (by simpa using hab'))
    exact σ.symm.injective h1
  · intro b hb b' hb' a ha hab hab'
    rw [Finset.mem_map_equiv] at hb hb' ha
    have h1 := hmB _ hb _ hb' _ ha ((hσ _ _).1 (by simpa using hab))
      ((hσ _ _).1 (by simpa using hab'))
    exact σ.symm.injective h1

private lemma ae8c_e89_Loc_base {c : Chart Ω u} {co : Coords c} (cl : Classes co)
    [Fintype ↥(Delta u)] [DecidableEq ↥(Delta u)] {x0 : ↥(Delta u)}
    (hx0 : ae8c_e89_coord cl x0 = 1) : ae8c_e89_Loc ae8c_e89_adj x0 := by
  refine ⟨Finset.univ.filter fun y : ↥(Delta u) => wt (ae8c_e89_coord cl y) = 1,
    Finset.univ.filter fun y : ↥(Delta u) => wt (ae8c_e89_coord cl y) = 5,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ae8c_e89_card_filter cl (fun v => wt v = 1)).trans (by decide)
  · exact (ae8c_e89_card_filter cl (fun v => wt v = 5)).trans (by decide)
  · refine Finset.disjoint_left.2 ?_
    intro y hy1 hy5
    have h1 := (Finset.mem_filter.1 hy1).2
    have h5 := (Finset.mem_filter.1 hy5).2
    omega
  · intro v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ae8c_e89_adj_iff cl, hx0]
    exact ae8c_e89_good_one_add _ (ae8c_e89_coord_good cl v)
  · intro v hv w hw hne
    obtain ⟨c1, hc1⟩ := ae8c_e89_wt_one _ (Finset.mem_filter.1 hv).2
    obtain ⟨c2, hc2⟩ := ae8c_e89_wt_one _ (Finset.mem_filter.1 hw).2
    have hc : c1 ≠ c2 := fun h => hne (ae8c_e89_coord_inj cl (by rw [hc1, hc2, h]))
    rw [ae8c_e89_adj_iff cl, hc1, hc2]
    exact ae8c_e89_good_unit_sum c1 c2 hc
  · intro v hv w hw hne
    obtain ⟨c1, hc1⟩ := ae8c_e89_wt_five _ (Finset.mem_filter.1 hv).2
    obtain ⟨c2, hc2⟩ := ae8c_e89_wt_five _ (Finset.mem_filter.1 hw).2
    have hc : c1 ≠ c2 := fun h => hne (ae8c_e89_coord_inj cl (by rw [hc1, hc2, h]))
    rw [ae8c_e89_adj_iff cl, hc1, hc2]
    exact ae8c_e89_good_five_sum c1 c2 hc
  · intro a ha a' ha' b hb hab hab'
    obtain ⟨c, hc⟩ := ae8c_e89_wt_one _ (Finset.mem_filter.1 ha).2
    obtain ⟨c', hc'⟩ := ae8c_e89_wt_one _ (Finset.mem_filter.1 ha').2
    obtain ⟨d, hd⟩ := ae8c_e89_wt_five _ (Finset.mem_filter.1 hb).2
    have h1 : c = d := by
      have h := (ae8c_e89_adj_iff cl a b).1 hab
      rw [hc, hd] at h
      exact (ae8c_e89_good_unit_five c d).1 h
    have h2 : c' = d := by
      have h := (ae8c_e89_adj_iff cl a' b).1 hab'
      rw [hc', hd] at h
      exact (ae8c_e89_good_unit_five c' d).1 h
    apply ae8c_e89_coord_inj cl
    rw [hc, hc', h1, h2]
  · intro b hb b' hb' a ha hab hab'
    obtain ⟨d, hd⟩ := ae8c_e89_wt_five _ (Finset.mem_filter.1 hb).2
    obtain ⟨d', hd'⟩ := ae8c_e89_wt_five _ (Finset.mem_filter.1 hb').2
    obtain ⟨c, hc⟩ := ae8c_e89_wt_one _ (Finset.mem_filter.1 ha).2
    have h1 : c = d := by
      have h := (ae8c_e89_adj_iff cl a b).1 hab
      rw [hc, hd] at h
      exact (ae8c_e89_good_unit_five c d).1 h
    have h2 : c = d' := by
      have h := (ae8c_e89_adj_iff cl a b').1 hab'
      rw [hc, hd'] at h
      exact (ae8c_e89_good_unit_five c d').1 h
    apply ae8c_e89_coord_inj cl
    rw [hd, hd', ← h1, h2]

private lemma ae8c_e89_conj_iff (k x : G) : k * x * k⁻¹ ∈ Delta u ↔ x ∈ Delta u := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨k⁻¹ * g, ?_⟩
    have e : x = k⁻¹ * (k * x * k⁻¹) * k⁻¹⁻¹ := by group
    rw [e, hg]
    group
  · rintro ⟨g, hg⟩
    exact ⟨k * g, by rw [hg]; group⟩

private noncomputable def ae8c_e89_conjEquiv (k : G) : ↥(Delta u) ≃ ↥(Delta u) :=
  Equiv.subtypeEquiv (MulAut.conj k).toEquiv (fun a => (ae8c_e89_conj_iff k a).symm)

private lemma ae8c_e89_conjEquiv_adj (k : G) (a b : ↥(Delta u)) :
    ae8c_e89_adj (ae8c_e89_conjEquiv k a) (ae8c_e89_conjEquiv k b) ↔ ae8c_e89_adj a b := by
  have e1 : ((ae8c_e89_conjEquiv k a : ↥(Delta u)) : G) = k * (a : G) * k⁻¹ := rfl
  have e2 : ((ae8c_e89_conjEquiv k b : ↥(Delta u)) : G) = k * (b : G) * k⁻¹ := rfl
  show ((ae8c_e89_conjEquiv k a : ↥(Delta u)) : G) * ((ae8c_e89_conjEquiv k b : ↥(Delta u)) : G)
    ∈ Delta u ↔ (a : G) * (b : G) ∈ Delta u
  rw [e1, e2, show k * (a : G) * k⁻¹ * (k * (b : G) * k⁻¹) = k * ((a : G) * (b : G)) * k⁻¹ by
    group]
  exact ae8c_e89_conj_iff k _

theorem Delta.ncard_eq (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c} (cl : Classes co) :
    (Delta u).ncard = 28 := by
  classical
  letI : Fintype ↥(Delta u) := Fintype.ofFinite _
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact ae8c_e89_card_delta cl

theorem exists_pairs (H : End18.Hyp Ω) {c : Chart Ω u} {co : Coords c} (cl : Classes co) :
    ∃ E : ↥(Delta u) ≃ {s : Finset (Fin 8) // s.card = 2},
      ∀ x y : ↥(Delta u), (x ≠ y ∧ ((x : G) * y) ∈ Delta u) ↔
        (x ≠ y ∧ ((E x : Finset (Fin 8)) ∩ (E y : Finset (Fin 8))).Nonempty) := by
  classical
  letI : Fintype ↥(Delta u) := Fintype.ofFinite _
  obtain ⟨x0, hx0⟩ := ae8c_e89_coord_surj cl ae8c_e89_good_one
  have hsymm : ∀ a b : ↥(Delta u), ae8c_e89_adj a b → ae8c_e89_adj b a := by
    intro a b h
    rw [ae8c_e89_adj_iff cl a b] at h
    rw [ae8c_e89_adj_iff cl b a, add_comm]
    exact h
  have hirr : ∀ a : ↥(Delta u), ¬ ae8c_e89_adj a a := by
    intro a h
    exact ae8c_e89_not_good_add_self _ ((ae8c_e89_adj_iff cl a a).1 h)
  have hcard : Fintype.card ↥(Delta u) = 28 := by
    rw [← Finset.card_univ]
    exact ae8c_e89_card_delta cl
  have hloc : ∀ x : ↥(Delta u), ae8c_e89_Loc ae8c_e89_adj x := by
    intro x
    have h0 : ae8c_e89_Loc ae8c_e89_adj x0 := ae8c_e89_Loc_base cl hx0
    obtain ⟨g, hg⟩ := x.2
    obtain ⟨h, hh⟩ := x0.2
    have hkx : ae8c_e89_conjEquiv (g * h⁻¹) x0 = x := by
      apply Subtype.ext
      show (g * h⁻¹) * (x0 : G) * (g * h⁻¹)⁻¹ = (x : G)
      rw [hh, hg]
      group
    have hm := ae8c_e89_Loc_map ae8c_e89_adj (ae8c_e89_conjEquiv (g * h⁻¹))
      (ae8c_e89_conjEquiv_adj (g * h⁻¹)) h0
    rwa [hkx] at hm
  obtain ⟨E, hE⟩ := exists_equiv_pairs_of_locally_prism ae8c_e89_adj hsymm hirr hcard hloc
  exact ⟨E, fun x y => and_congr_right fun hne =>
    (hE x y).trans ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩⟩

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13


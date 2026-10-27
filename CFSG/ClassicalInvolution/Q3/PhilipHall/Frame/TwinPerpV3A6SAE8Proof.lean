module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6SAE8

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open Classical in

theorem ae6_graph_iso {G H ι : Type*} [Group G] [Group H] (a : ι → G) (b : ι → H) {A : Subgroup G} {B : Subgroup H}
    (hA : Subgroup.closure (Set.range a) = A) (hB : Subgroup.closure (Set.range b) = B) [Finite A]
    (hcA : Nat.card (Subgroup.closure (Set.range fun i => (a i, b i))) = Nat.card A)
    (hcB : Nat.card (Subgroup.closure (Set.range fun i => (a i, b i))) = Nat.card B) :
    ∃ ρ : A ≃* B, ∀ g ∈ Subgroup.closure (Set.range fun i => (a i, b i)), ∀ hg : g.1 ∈ A, (ρ ⟨g.1, hg⟩ : H) = g.2 := by
  set Γ := Subgroup.closure (Set.range fun i => (a i, b i)) with hΓ
  have hΓA : ∀ g ∈ Γ, g.1 ∈ A := by
    intro g hg
    have : Γ ≤ A.comap (MonoidHom.fst G H) := by
      rw [hΓ, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hA ▸ Subgroup.subset_closure (Set.mem_range_self i)
    exact this hg
  have hΓB : ∀ g ∈ Γ, g.2 ∈ B := by
    intro g hg
    have : Γ ≤ B.comap (MonoidHom.snd G H) := by
      rw [hΓ, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hB ▸ Subgroup.subset_closure (Set.mem_range_self i)
    exact this hg
  have hsA : ∀ x ∈ Subgroup.closure (Set.range a), ∃ g ∈ Γ, g.1 = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨(a i, b i), Subgroup.subset_closure (Set.mem_range_self i), rfl⟩
    | one => exact ⟨1, one_mem _, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨g', hg', rfl⟩ := hy
      exact ⟨g * g', mul_mem hg hg', rfl⟩
    | inv x _ hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact ⟨g⁻¹, inv_mem hg, rfl⟩
  have hsB : ∀ x ∈ Subgroup.closure (Set.range b), ∃ g ∈ Γ, g.2 = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨(a i, b i), Subgroup.subset_closure (Set.mem_range_self i), rfl⟩
    | one => exact ⟨1, one_mem _, rfl⟩
    | mul x y _ _ hx hy =>
      obtain ⟨g, hg, rfl⟩ := hx
      obtain ⟨g', hg', rfl⟩ := hy
      exact ⟨g * g', mul_mem hg hg', rfl⟩
    | inv x _ hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      exact ⟨g⁻¹, inv_mem hg, rfl⟩
  let f₁ : Γ →* A := ((MonoidHom.fst G H).comp Γ.subtype).codRestrict A fun g => hΓA g g.2
  let f₂ : Γ →* B := ((MonoidHom.snd G H).comp Γ.subtype).codRestrict B fun g => hΓB g g.2
  have hf₁ : Function.Surjective f₁ := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := hsA x (hA ▸ hx)
    exact ⟨⟨g, hg⟩, rfl⟩
  have hf₂ : Function.Surjective f₂ := by
    rintro ⟨x, hx⟩
    obtain ⟨g, hg, rfl⟩ := hsB x (hB ▸ hx)
    exact ⟨⟨g, hg⟩, rfl⟩
  have hfin : Finite Γ := Nat.finite_of_card_ne_zero (by rw [hcA]; exact Nat.card_pos.ne')
  have hfinB : Finite B := Nat.finite_of_card_ne_zero (by rw [← hcB, hcA]; exact Nat.card_pos.ne')
  have hb₁ : Function.Bijective f₁ := hf₁.bijective_of_nat_card_le hcA.le
  have hb₂ : Function.Bijective f₂ := hf₂.bijective_of_nat_card_le hcB.le
  let e₁ := MulEquiv.ofBijective f₁ hb₁
  let e₂ := MulEquiv.ofBijective f₂ hb₂
  refine ⟨e₁.symm.trans e₂, fun g hg hg1 => ?_⟩
  have e : (⟨g.1, hg1⟩ : A) = e₁ ⟨g, hg⟩ := rfl
  rw [MulEquiv.trans_apply, e, MulEquiv.symm_apply_apply]
  rfl

abbrev ae6AE8 : Subgroup (AE.AEQ 8) := (AE.aeSub 8).map (AE.mkQ 8)

@[expose] noncomputable def ae6Gamma : Subgroup (AE.AEQ 8 × AE6Om) :=
  Subgroup.closure (Set.range fun i => (AE.mkQ 8 (ae6AEGen i), A6.curtisGen (ae6V0Letter i)))

theorem ae6V0_closure : Subgroup.closure (Set.range fun i => A6.curtisGen (ae6V0Letter i)) = ae6ModelV 0 := by
  have hr : Set.range ae6V0Letter = {i | i ≠ ae6Omit 0} := by
    ext j
    simp only [Set.mem_range, Set.mem_setOf_eq]
    revert j
    decide
  rw [ae6ModelV, ← hr, ← Set.range_comp]
  rfl

theorem AE6AE8Fin.finite (h : AE6AE8Fin) : Finite ae6AE8 :=
  Nat.finite_of_card_ne_zero (by rw [h.2.2.1]; norm_num)

theorem AE6AE8Fin.exists_rho (h : AE6AE8Fin) :
    ∃ ρ : ae6AE8 ≃* ae6ModelV 0, ∀ g ∈ ae6Gamma, ∀ hg : g.1 ∈ ae6AE8, (ρ ⟨g.1, hg⟩ : AE6Om) = g.2 :=
  haveI := h.finite
  ae6_graph_iso _ _ h.2.1 ae6V0_closure (by rw [h.2.2.2.2.1, h.2.2.1]) (by rw [h.2.2.2.2.1, h.2.2.2.1])

@[expose] noncomputable def ae6Rho (h : AE6AE8Fin) : ae6AE8 ≃* ae6ModelV 0 := h.exists_rho.choose

theorem ae6Rho_spec (h : AE6AE8Fin) {g : AE.AEQ 8 × AE6Om} (hg : g ∈ ae6Gamma) (hg1 : g.1 ∈ ae6AE8) :
    (ae6Rho h ⟨g.1, hg1⟩ : AE6Om) = g.2 := h.exists_rho.choose_spec g hg hg1

theorem ae6AEWord_mem (h : AE6AE8Fin) (w : List (Fin 7)) : ae6AEWord w ∈ AE.aeSub 8 := by
  induction w with
  | nil => simp [ae6AEWord]
  | cons a w ih =>
    simp only [ae6AEWord, List.map_cons, List.prod_cons] at ih ⊢
    exact mul_mem (h.1 a) ih

theorem mkQ_ae6AEWord_mem (h : AE6AE8Fin) (w : List (Fin 7)) : AE.mkQ 8 (ae6AEWord w) ∈ ae6AE8 :=
  Subgroup.mem_map_of_mem _ (ae6AEWord_mem h w)

theorem ae6Gamma_word (w : List (Fin 7)) :
    (AE.mkQ 8 (ae6AEWord w), ae6Word (w.map ae6V0Letter)) ∈ ae6Gamma := by
  induction w with
  | nil =>
    have e : (AE.mkQ 8 (ae6AEWord []), ae6Word (([] : List (Fin 7)).map ae6V0Letter)) = 1 := by
      simp [ae6AEWord, ae6Word]
    rw [e]
    exact one_mem _
  | cons a w ih =>
    have e : (AE.mkQ 8 (ae6AEWord (a :: w)), ae6Word ((a :: w).map ae6V0Letter)) =
        (AE.mkQ 8 (ae6AEGen a), A6.curtisGen (ae6V0Letter a)) *
          (AE.mkQ 8 (ae6AEWord w), ae6Word (w.map ae6V0Letter)) := by
      simp [ae6AEWord, ae6Word]
    rw [e]
    exact mul_mem (Subgroup.subset_closure (Set.mem_range_self a)) ih

theorem ae6Rho_word (h : AE6AE8Fin) (w : List (Fin 7)) :
    (ae6Rho h ⟨AE.mkQ 8 (ae6AEWord w), mkQ_ae6AEWord_mem h w⟩ : AE6Om) = ae6Word (w.map ae6V0Letter) :=
  ae6Rho_spec h (ae6Gamma_word w) (mkQ_ae6AEWord_mem h w)

@[expose] def ae6Corr (h : AE6AE8Fin) (S : Subgroup (AE.AEQ 8)) (J : Subgroup AE6Om) : Prop :=
  ∀ x : ae6AE8, (x : AE.AEQ 8) ∈ S ↔ ((ae6Rho h x : ae6ModelV 0) : AE6Om) ∈ J

theorem ae6Corr_conj (h : AE6AE8Fin) {S : Subgroup (AE.AEQ 8)} {J : Subgroup AE6Om} (hSJ : ae6Corr h S J)
    (a : ae6AE8) : ae6Corr h (conjSub (a : AE.AEQ 8) S) (conjSub ((ae6Rho h a : ae6ModelV 0) : AE6Om) J) := by
  intro x
  rw [mem_conjSub_iff, mem_conjSub_iff]
  have := hSJ (a⁻¹ * x * a)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using this

@[expose] noncomputable def ae6KBar (h : AE6AE8Fin) (s : Fin 3) : ae6AE8 :=
  ⟨AE.mkQ 8 (ae6AEWord ((ae6KWord s).map ae6V0Index)), mkQ_ae6AEWord_mem h _⟩

theorem ae6Rho_kBar (h : AE6AE8Fin) (s : Fin 3) :
    ((ae6Rho h (ae6KBar h s) : ae6ModelV 0) : AE6Om) = ae6Word (ae6KWord s) := by
  have hmap : ∀ s : Fin 3, ((ae6KWord s).map ae6V0Index).map ae6V0Letter = ae6KWord s := by decide
  rw [ae6KBar, ae6Rho_word, hmap]

theorem ae6KBar_mem (h : AE6AE8Fin) (s : Fin 3) :
    (ae6KBar h s : AE.AEQ 8) ∈ AE.memBar ae6Alpha0 ae6Alpha0_card true := h.2.2.2.2.2.2.1 s

theorem ae6_K_lift (h : AE6AE8Fin) {v : AE6Om} (hv : v ∈ ae6ModelK) :
    ∃ t : ae6AE8, (t : AE.AEQ 8) ∈ AE.memBar ae6Alpha0 ae6Alpha0_card true ∧
      ((ae6Rho h t : ae6ModelV 0) : AE6Om) = v := by
  rw [ae6ModelK] at hv
  induction hv using Subgroup.closure_induction with
  | mem v hv =>
    rcases hv with rfl | rfl
    · exact ⟨ae6KBar h 0, ae6KBar_mem h 0, ae6Rho_kBar h 0⟩
    · exact ⟨ae6KBar h 1, ae6KBar_mem h 1, ae6Rho_kBar h 1⟩
  | one => exact ⟨1, one_mem _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨t, ht, rfl⟩ := ha
    obtain ⟨t', ht', rfl⟩ := hb
    exact ⟨t * t', mul_mem ht ht', by simp⟩
  | inv a _ ha =>
    obtain ⟨t, ht, rfl⟩ := ha
    exact ⟨t⁻¹, inv_mem ht, by simp⟩

theorem ae6ModelK_le_V0 (h : AE6AE8Fin) : ae6ModelK ≤ ae6ModelV 0 := by
  intro v hv
  obtain ⟨t, -, rfl⟩ := ae6_K_lift h hv
  exact (ae6Rho h t).2

theorem ae6Corr_base (h : AE6AE8Fin) : ae6Corr h (AE.memBar ae6Alpha0 ae6Alpha0_card true) ae6ModelK := by
  have back : ∀ x : ae6AE8, ((ae6Rho h x : ae6ModelV 0) : AE6Om) ∈ ae6ModelK →
      (x : AE.AEQ 8) ∈ AE.memBar ae6Alpha0 ae6Alpha0_card true := by
    intro x hx
    obtain ⟨t, ht, e⟩ := ae6_K_lift h hx
    rwa [(ae6Rho h).injective (Subtype.ext e)] at ht
  intro x
  refine ⟨fun hx => ?_, back x⟩
  set Kp : Subgroup ae6AE8 := (ae6ModelK.subgroupOf (ae6ModelV 0)).comap (ae6Rho h).toMonoidHom
  set Sp : Subgroup ae6AE8 := (AE.memBar ae6Alpha0 ae6Alpha0_card true).subgroupOf ae6AE8
  have hle : Kp ≤ Sp := fun y hy => back y hy
  have hS : Nat.card Sp = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_aeModel _ _ _)).toEquiv).trans
      (AE.natCard_memBar (by norm_num) ae6Alpha0 ae6Alpha0_card true)
  have hK : Nat.card Kp = 8 := by
    have e1 : Kp.map (ae6Rho h).toMonoidHom = ae6ModelK.subgroupOf (ae6ModelV 0) :=
      Subgroup.map_comap_eq_self_of_surjective (ae6Rho h).surjective _
    rw [← Subgroup.card_map_of_injective (f := (ae6Rho h).toMonoidHom) (ae6Rho h).injective, e1]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ae6ModelK_le_V0 h)).toEquiv).trans h.2.2.2.2.2.1
  haveI : Finite Sp := Nat.finite_of_card_ne_zero (by rw [hS]; norm_num)
  have heq : Kp = Sp := Subgroup.eq_of_le_of_card_ge hle (by rw [hS, hK])
  have hx' : x ∈ Sp := hx
  rw [← heq] at hx'
  exact hx'

theorem ae6_memBar_conj (h : AE6AE8Fin) {g : AE.AEQ 8} (hg : g ∈ ae6AE8) (α : Finset (Fin 8)) (hα : α.card = 4)
    (b : Bool) : ∃ (β : Finset (Fin 8)) (hβ : β.card = 4) (c : Bool), conjSub g (AE.memBar α hα b) = AE.memBar β hβ c := by
  let P : AE.AEQ 8 → Prop := fun g => ∀ (α : Finset (Fin 8)) (hα : α.card = 4) (b : Bool),
    ∃ (β : Finset (Fin 8)) (hβ : β.card = 4) (c : Bool), conjSub g (AE.memBar α hα b) = AE.memBar β hβ c
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    intro x y hx hy α hα b
    obtain ⟨β, hβ, c, e⟩ := hy α hα b
    obtain ⟨β', hβ', c', e'⟩ := hx β hβ c
    exact ⟨β', hβ', c', by rw [conjSub_mul, e, e']⟩
  have hone : P 1 := fun α hα b => ⟨α, hα, b, conjSub_one _⟩
  have hpow : ∀ x, P x → ∀ n : ℕ, P (x ^ n) := by
    intro x hx n
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hx
  have hgen : ∀ i, P (AE.mkQ 8 (ae6AEGen i)) := fun i α hα b => h.2.2.2.2.2.2.2.1 α hα b i
  haveI := h.finite
  have hinv : ∀ i, P (AE.mkQ 8 (ae6AEGen i))⁻¹ := by
    intro i
    have hm : AE.mkQ 8 (ae6AEGen i) ∈ ae6AE8 := Subgroup.mem_map_of_mem _ (h.1 i)
    set y : ae6AE8 := ⟨_, hm⟩
    have hpos := (isOfFinOrder_of_finite y).orderOf_pos
    have e : y⁻¹ = y ^ (orderOf y - 1) :=
      (eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one])).symm
    have e' : (AE.mkQ 8 (ae6AEGen i))⁻¹ = AE.mkQ 8 (ae6AEGen i) ^ (orderOf y - 1) :=
      congrArg Subtype.val e
    rw [e']
    exact hpow _ (hgen i) _
  have hg' : g ∈ Subgroup.closure (Set.range fun i => AE.mkQ 8 (ae6AEGen i)) := h.2.1.symm ▸ hg
  clear hg
  revert α hα b
  change P g
  induction hg' using Subgroup.closure_induction'' with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hgen i
  | inv_mem x hx => obtain ⟨i, rfl⟩ := hx; exact hinv i
  | one => exact hone
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem ae6_AE8_V0 (h : AE6AE8Fin) :
    (∀ (α : Finset (Fin 8)) (hα : α.card = 4) (b : Bool), ∃ v ∈ ae6ModelV 0,
      ae6Corr h (AE.memBar α hα b) (conjSub v ae6ModelK)) ∧
    ∀ v ∈ ae6ModelV 0, ∃ (α : Finset (Fin 8)) (hα : α.card = 4) (b : Bool),
      ae6Corr h (AE.memBar α hα b) (conjSub v ae6ModelK) := by
  constructor
  · intro α hα b
    obtain ⟨w, hw⟩ := h.2.2.2.2.2.2.2.2.1 α hα b
    set a : ae6AE8 := ⟨_, mkQ_ae6AEWord_mem h w⟩
    refine ⟨_, (ae6Rho h a).2, ?_⟩
    rw [hw]
    exact ae6Corr_conj h (ae6Corr_base h) a
  · intro v hv
    set a : ae6AE8 := (ae6Rho h).symm ⟨v, hv⟩
    obtain ⟨β, hβ, c, e⟩ := ae6_memBar_conj h a.2 ae6Alpha0 ae6Alpha0_card true
    refine ⟨β, hβ, c, ?_⟩
    have := ae6Corr_conj h (ae6Corr_base h) a
    rwa [e, show ((ae6Rho h a : ae6ModelV 0) : AE6Om) = v by simp [a]] at this

theorem ae6_AE8_transfer (h : AE6AE8Fin) {k : Fin 3} (e : MulAut AE6Om)
    (heV : ∀ y, y ∈ ae6ModelV 0 ↔ e y ∈ ae6ModelV k) {c : AE6Om} (hc : c ∈ ae6ModelV k)
    (hK : ∀ y, y ∈ ae6ModelK ↔ e y ∈ conjSub c ae6ModelK) :
    ∃ ρ : ↥((AE.aeSub 8).map (AE.mkQ 8)) ≃* ↥(ae6ModelV k),
      (∀ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool), ∃ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK,
        ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔
          ((ρ x : ↥(ae6ModelV k)) : AE6Om) ∈ J) ∧
      ∀ J ∈ ae6ConjIn (ae6ModelV k) ae6ModelK, ∃ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool),
        ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔
          ((ρ x : ↥(ae6ModelV k)) : AE6Om) ∈ J := by
  let ψ : ae6ModelV 0 ≃* ae6ModelV k :=
    { toFun := fun y => ⟨e y, (heV y).1 y.2⟩
      invFun := fun z => ⟨e.symm z, (heV _).2 (by rw [MulEquiv.apply_symm_apply]; exact z.2)⟩
      left_inv := fun y => Subtype.ext (e.symm_apply_apply (y : AE6Om))
      right_inv := fun z => Subtype.ext (e.apply_symm_apply (z : AE6Om))
      map_mul' := fun y z => Subtype.ext (map_mul e (y : AE6Om) z) }
  have key : ∀ v ∈ ae6ModelV 0, ∀ S : Subgroup (AE.AEQ 8), ae6Corr h S (conjSub v ae6ModelK) →
      ∀ x : ae6AE8, (x : AE.AEQ 8) ∈ S ↔
        ((((ae6Rho h).trans ψ) x : ae6ModelV k) : AE6Om) ∈ conjSub (e v * c) ae6ModelK := by
    intro v _ S hS x
    rw [hS x]
    change _ ↔ e _ ∈ _
    rw [mem_conjSub_iff, mem_conjSub_iff, hK, mem_conjSub_iff]
    have eq : c⁻¹ * e (v⁻¹ * ((ae6Rho h x : ae6ModelV 0) : AE6Om) * v) * c =
        (e v * c)⁻¹ * e ((ae6Rho h x : ae6ModelV 0) : AE6Om) * (e v * c) := by
      simp only [map_mul, map_inv]
      group
    rw [eq]
    exact Iff.rfl
  refine ⟨(ae6Rho h).trans ψ, fun α hα b => ?_, fun J hJ => ?_⟩
  · obtain ⟨v, hv, hS⟩ := (ae6_AE8_V0 h).1 α hα b
    exact ⟨_, ⟨e v * c, mul_mem ((heV v).1 hv) hc, rfl⟩, key v hv _ hS⟩
  · obtain ⟨v', hv', rfl⟩ := hJ
    have hv : e.symm (v' * c⁻¹) ∈ ae6ModelV 0 :=
      (heV _).2 (by rw [MulEquiv.apply_symm_apply]; exact mul_mem hv' (inv_mem hc))
    obtain ⟨α, hα, b, hS⟩ := (ae6_AE8_V0 h).2 _ hv
    refine ⟨α, hα, b, ?_⟩
    have := key _ hv _ hS
    rwa [MulEquiv.apply_symm_apply, inv_mul_cancel_right] at this

theorem ae6_aut_word {e : MulAut AE6Om} {π : Fin 8 → Fin 8} (he : ∀ i, e (A6.curtisGen i) = A6.curtisGen (π i))
    (w : List (Fin 8)) : e (ae6Word w) = ae6Word (w.map π) := by
  induction w with
  | nil => simp [ae6Word]
  | cons a w ih =>
    simp only [ae6Word] at ih ⊢
    rw [List.map_cons, List.prod_cons, map_mul, ih, he]
    rfl

@[expose] def ae6DiagVertex : Fin 2 → Fin 3 := ![2, 1]

section Diag


theorem ae6Diag_image_V0 (cc : Fin 2) :
    (ae6VertexLetters 0).image (ae6Diag cc) = ae6VertexLetters (ae6DiagVertex cc) := by
  fin_cases cc <;> decide

theorem ae6DiagTwin_mem (cc : Fin 2) : ∀ j ∈ ae6TwinWord (ae6DiagTwin cc), j ∈ ae6VertexLetters (ae6DiagVertex cc) := by
  fin_cases cc <;> decide

theorem ae6Diag_leftInverse (cc : Fin 2) : Function.LeftInverse (ae6Diag cc) (ae6Diag cc) := by
  fin_cases cc <;> decide

theorem ae6ModelK_eq_words :
    ae6ModelK = Subgroup.closure {ae6Word (ae6KWord 0), ae6Word (ae6KWord 1)} := by
  simp only [ae6ModelK, ae6KWord, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem ae6_diag_K_le (h : AE6AE8Fin) (cc : Fin 2) {e : MulAut AE6Om}
    (he : ∀ i, e (A6.curtisGen i) = A6.curtisGen (ae6Diag cc i)) :
    ae6ModelK.map e.toMonoidHom ≤ ae6Twin (ae6DiagTwin cc) := by
  rw [ae6ModelK_eq_words, MonoidHom.map_closure, Subgroup.closure_le, Set.image_insert_eq, Set.image_singleton,
    Set.insert_subset_iff, Set.singleton_subset_iff, MulEquiv.coe_toMonoidHom, ae6_aut_word he, ae6_aut_word he]
  exact ⟨(h.2.2.2.2.2.2.2.2.2 cc).2 0, (h.2.2.2.2.2.2.2.2.2 cc).2 1⟩

theorem ae6_diag_K_eq (h : AE6AE8Fin) (cc : Fin 2) {e : MulAut AE6Om}
    (he : ∀ i, e (A6.curtisGen i) = A6.curtisGen (ae6Diag cc i)) :
    ae6ModelK.map e.toMonoidHom = ae6Twin (ae6DiagTwin cc) := by
  have hcK : Nat.card (ae6Twin (ae6DiagTwin cc)) = 8 := by
    rw [ae6Twin, conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact h.2.2.2.2.2.1
  haveI : Finite (ae6Twin (ae6DiagTwin cc)) := Nat.finite_of_card_ne_zero (by rw [hcK]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge (ae6_diag_K_le h cc he) (by
    rw [hcK, Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h.2.2.2.2.2.1])

theorem ae6_AE8_diag (h : AE6AE8Fin) (cc : Fin 2) :
    ∃ ρ : ↥((AE.aeSub 8).map (AE.mkQ 8)) ≃* ↥(ae6ModelV (ae6DiagVertex cc)),
      (∀ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool), ∃ J ∈ ae6ConjIn (ae6ModelV (ae6DiagVertex cc)) ae6ModelK,
        ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔
          ((ρ x : ↥(ae6ModelV (ae6DiagVertex cc))) : AE6Om) ∈ J) ∧
      ∀ J ∈ ae6ConjIn (ae6ModelV (ae6DiagVertex cc)) ae6ModelK, ∃ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool),
        ∀ x : ↥((AE.aeSub 8).map (AE.mkQ 8)), (x : AE.AEQ 8) ∈ AE.memBar α h b ↔
          ((ρ x : ↥(ae6ModelV (ae6DiagVertex cc))) : AE6Om) ∈ J := by
  obtain ⟨e, he⟩ := ae6_aut_of_perm (ae6Diag cc) (ae6Diag_leftInverse cc).surjective
    (h.2.2.2.2.2.2.2.2.2 cc).1
  have heV : ∀ y, y ∈ ae6ModelV 0 ↔ e y ∈ ae6ModelV (ae6DiagVertex cc) := fun y => by
    rw [ae6ModelV_eq, ae6ModelV_eq, mem_letterSub_aut he, ← Finset.coe_image, ae6Diag_image_V0]
  have hc : ae6Word (ae6TwinWord (ae6DiagTwin cc)) ∈ ae6ModelV (ae6DiagVertex cc) := by
    rw [ae6ModelV_eq]
    exact ae6Word_mem (ae6DiagTwin_mem cc)
  refine ae6_AE8_transfer h e heV hc fun y => ?_
  rw [← ae6Twin, ← ae6_diag_K_eq h cc he]
  exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).symm

theorem ae6ModelAE8_of_fin (h : AE6AE8Fin) : AE6ModelAE8 := by
  intro k
  fin_cases k
  · exact ae6_AE8_transfer h 1 (fun _ => Iff.rfl) (one_mem _) fun y => by rw [conjSub_one]; rfl
  · exact ae6_AE8_diag h 1
  · exact ae6_AE8_diag h 0

end Diag

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

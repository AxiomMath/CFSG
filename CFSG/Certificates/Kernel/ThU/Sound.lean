module

public import Certificates.Data.Kernel.ThU.Defs
public import CFSG.Certificates.Kernel.Th.Spec.SylowAsm
public import CFSG.Certificates.Kernel.Th.Spec.SylowOrbit
public import CFSG.Certificates.Kernel.Th.Spec.FwdSlp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

public section

namespace CFSG.KC.ThU

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Spec CFSG.KC.Th.Spec.FwdRel CFSG.KC.Th.Spec.SylowOrbit

variable {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}

theorem prodR_cons {m : ℕ} (RB : ℕ → ℕ) (c rm ONE GR : ℕ) (l : Fin m × Bool)
    (w : List (Fin m × Bool)) :
    prodR RB c rm ONE GR (l :: w) = mulB c rm (RB (regAt GR l.1.val)) (prodR RB c rm ONE GR w) :=
  rfl

theorem map_lift_of_pos (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {G : Type*} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)) {m : ℕ} {RB : ℕ → ℕ}
    {GR : ℕ} (x : Fin m → G) (hx : ∀ i, φ (x i) = pkMat (RB (regAt GR i.val))) :
    ∀ w : List (Fin m × Bool), (∀ l ∈ w, l.2 = true) →
      φ (FreeGroup.lift x (FreeGroup.mk w)) = pkMat (prodR RB c rm ONE GR w)
  | [], _ => by
    rw [← FreeGroup.one_eq_mk, map_one, map_one]
    exact (pkMat_one hk).symm
  | (i, b) :: w, hw => by
    have hb : b = true := hw (i, b) (List.mem_cons_self ..)
    subst hb
    have e : FreeGroup.mk ((i, true) :: w) = FreeGroup.of i * FreeGroup.mk w := rfl
    rw [e, map_mul, FreeGroup.lift_apply_of, map_mul, hx,
      map_lift_of_pos hk φ x hx w fun l hl => hw l (List.mem_cons_of_mem _ hl), prodR_cons,
      pkMat_mulB hk]

theorem lift_eq_one_of_relOKR
    (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {G : Type*} [Group G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (hφ : Function.Injective φ) {m : ℕ} {RB : ℕ → ℕ} {GR : ℕ} (x : Fin m → G)
    (hx : ∀ i, φ (x i) = pkMat (RB (regAt GR i.val))) {r : List (Fin m × Bool)}
    (h : relOKR RB c rm ONE GR r = true) : FreeGroup.lift x (FreeGroup.mk r) = 1 := by
  obtain ⟨hpos, hone⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 h
  have hpos' : ∀ l ∈ r, l.2 = true := fun l hl => by
    simpa using (List.all_eq_true.1 hpos) l hl
  apply hφ
  rw [map_lift_of_pos hk φ x hx r hpos', Nat.eq_of_beq_eq_true hone, pkMat_one hk, map_one]

theorem marked_iff (m r : ℕ) : marked m r = true ↔ m.testBit r = true := by
  have e : marked m r = Nat.blt 0 (m &&& 2 ^ r) := by
    change Nat.blt 0 (m &&& 1 <<< r) = _
    rw [Nat.one_shiftLeft]
  rw [e, Nat.and_two_pow]
  cases m.testBit r <;> simp [Nat.two_pow_pos]

theorem marked_gmask3 {GR k : ℕ} (h : marked (gmask3 GR) k = true) :
    ∃ i : Fin 3, k = regAt GR i.val := by
  rw [marked_iff] at h
  simp only [gmask3, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩

theorem regIn_of_marked (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {G : Type*} [Group G] (φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)) {RB : ℕ → ℕ}
    {GR : ℕ} (x : Fin 3 → G) (hx : ∀ i, φ (x i) = pkMat (RB (regAt GR i.val))) {Cs : List ℕ}
    {S : ℕ} (hpos : 0 < runSlp RB c rm ONE Cs S) (hlt : runSlp RB c rm ONE Cs S < 2048) {k : ℕ}
    (hm : marked (runMarked Cs (S + 2048 * gmask3 GR) / 2048) k = true) :
    ∃ u ∈ Subgroup.closure (Set.range x), φ u = pkMat (RB k) := by
  let Q : ℕ → Prop := fun k => ∃ u ∈ Subgroup.closure (Set.range x), φ u = pkMat (RB k)
  have hmul : ∀ r a b, Q a → Q b → RB r = mulB c rm (RB a) (RB b) → Q r := by
    rintro r a b ⟨u, hu, eu⟩ ⟨v, hv, ev⟩ e
    exact ⟨u * v, Subgroup.mul_mem _ hu hv, by rw [map_mul, eu, ev, e, pkMat_mulB hk]⟩
  have hpow : ∀ r a e, Q a → 0 < e → e < 16 → RB r = powB c rm ONE (RB a) e 4 → Q r := by
    rintro r a e ⟨u, hu, eu⟩ _ he h
    exact ⟨u ^ e, Subgroup.pow_mem _ hu e,
      by rw [map_pow, eu, h, pkMat_powB hk _ e 4 (by norm_num; omega)]⟩
  have hinv : ∀ r a, Q a → mulB c rm (RB a) (RB r) = ONE → Q r := by
    rintro r a ⟨u, hu, eu⟩ h
    refine ⟨u⁻¹, Subgroup.inv_mem _ hu, ?_⟩
    have h1 : pkMat (RB a) * pkMat (RB r) = 1 := by rw [← pkMat_mulB hk, h, pkMat_one hk]
    have h2 : φ u⁻¹ * pkMat (RB a) = 1 := by rw [← eu, ← map_mul, inv_mul_cancel, map_one]
    calc φ u⁻¹ = φ u⁻¹ * (pkMat (RB a) * pkMat (RB r)) := by rw [h1, Matrix.mul_one]
      _ = (φ u⁻¹ * pkMat (RB a)) * pkMat (RB r) := (Matrix.mul_assoc _ _ _).symm
      _ = pkMat (RB r) := by rw [h2, Matrix.one_mul]
  have hm0 : ∀ k, marked (gmask3 GR) k = true → Q k := by
    intro k hk'
    obtain ⟨i, rfl⟩ := marked_gmask3 hk'
    exact ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩, hx i⟩
  exact (FwdSlp.runMarked_induct Q hmul hpow hinv Cs S (gmask3 GR) hm0 hpos hlt).2 k hm

theorem blockOK_of {RB PT : ℕ → ℕ} {rm PR n fr tb p tc sc BL b : ℕ} (hfr : blkFr BL b = fr)
    (hto : blkTo BL b = tb) (h : blockB RB PT rm PR n fr tb p tc sc = true) :
    BlockOK RB rm PR n p BL b := by
  subst hfr hto
  obtain ⟨hlt, r1⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 h
  obtain ⟨hbase, r2⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 r1
  obtain ⟨htree, hsort⟩ := CFSG.KC.Th.Spec.Dce.andB_iff.1 r2
  unfold BlockOK
  exact ⟨PT, [tc], [sc], _, Nat.le_of_ble_eq_true hlt, hbase, Nat.eq_of_beq_eq_true htree, rfl,
    Nat.eq_of_beq_eq_true hsort⟩

theorem chain_le {J : Subgroup (GL (Fin 248) (ZMod 2))} {RB : ℕ → ℕ} {PR n : ℕ} (f P : ℕ → ℕ)
    (nb : ℕ) (hf0 : f 0 = 0) (hfn : f nb = n)
    (hblk : ∀ b < nb, P b ^ (f (b + 1) - f b) * Nat.card (pcSub J RB PR (f (b + 1)) n) ≤
      Nat.card (pcSub J RB PR (f b) n)) :
    (∏ b ∈ Finset.range nb, P b ^ (f (b + 1) - f b)) ≤ Nat.card (pcSub J RB PR 0 n) := by
  have step : ∀ j ≤ nb, (∏ b ∈ Finset.range j, P b ^ (f (b + 1) - f b)) *
      Nat.card (pcSub J RB PR (f j) n) ≤ Nat.card (pcSub J RB PR 0 n) := by
    intro j
    induction j with
    | zero => intro _; simp [hf0]
    | succ j ih =>
      intro hj
      rw [Finset.prod_range_succ, Nat.mul_assoc]
      exact (Nat.mul_le_mul_left _ (hblk j (by omega))).trans (ih (by omega))
  have h1 : 0 < Nat.card (pcSub J RB PR n n) := Nat.card_pos
  have h := step nb le_rfl
  rw [hfn] at h
  exact (Nat.le_mul_of_pos_right _ h1).trans h

theorem le_card_closure_of_chain
    (hk : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    {G : Type*} [Group G] [Finite G] {φ : G →* Matrix (Fin 248) (Fin 248) (ZMod 2)}
    (hφ : Function.Injective φ) {RB : ℕ → ℕ} {GR PR n N : ℕ} (x : Fin 3 → G)
    (hx : ∀ i, φ (x i) = pkMat (RB (regAt GR i.val))) {Cs : List ℕ} {S : ℕ}
    (hpos : 0 < runSlp RB c rm ONE Cs S) (hlt : runSlp RB c rm ONE Cs S < 2048)
    (hall : allMarked PR n (runMarked Cs (S + 2048 * gmask3 GR) / 2048) = true)
    (hN : ∀ J : Subgroup (GL (Fin 248) (ZMod 2)),
      (∀ k < n, RegIn (⊤ : Subgroup J) RB (regAt PR k)) → N ≤ Nat.card (pcSub J RB PR 0 n)) :
    N ≤ Nat.card (Subgroup.closure (Set.range x)) := by
  let ψ : G →* GL (Fin 248) (ZMod 2) := φ.toHomUnits
  have hψ : Function.Injective ψ := by
    intro a b h
    apply hφ
    have h' := congrArg (fun u : GL (Fin 248) (ZMod 2) =>
      ((u : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))) h
    simpa [ψ, MonoidHom.coe_toHomUnits] using h'
  let U : Subgroup G := Subgroup.closure (Set.range x)
  let J : Subgroup (GL (Fin 248) (ZMod 2)) := U.map ψ
  have hR : ∀ k < n, RegIn (⊤ : Subgroup J) RB (regAt PR k) := by
    intro k hkn
    have hmk : marked (runMarked Cs (S + 2048 * gmask3 GR) / 2048) (regAt PR k) = true :=
      (CFSG.KC.Th.Spec.Dce.allB_iff
        (fun k => marked (runMarked Cs (S + 2048 * gmask3 GR) / 2048) (regAt PR k)) n).1
        hall k hkn
    obtain ⟨u, hu, eu⟩ := regIn_of_marked hk φ x hx hpos hlt hmk
    refine ⟨⟨ψ u, Subgroup.mem_map_of_mem ψ hu⟩, Subgroup.mem_top _, ?_⟩
    simpa [ψ, MonoidHom.coe_toHomUnits] using eu
  have hJ : Nat.card J = Nat.card U := Subgroup.card_map_of_injective hψ
  calc N ≤ Nat.card (pcSub J RB PR 0 n) := hN J hR
    _ ≤ Nat.card (⊤ : Subgroup J) := Subgroup.card_le_of_le le_top
    _ = Nat.card U := by rw [Subgroup.card_top, hJ]

end CFSG.KC.ThU

end

module

public import Certificates.Certificate11000

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover

@[expose] def muIdx (j : ℕ) : ℕ := packEntry muTable 1 j

@[expose] noncomputable def f (s t : S) : ZMod 2 := (fIdx (idx s) (idx t) : ℕ)

@[expose] noncomputable def lam0 (s : S) : ZMod 2 := (lam0Idx (idx s) : ℕ)

@[expose] noncomputable def mu (s : S) : ZMod 2 := (muIdx (idx s) : ℕ)

@[expose] noncomputable def lam (s : S) : ZMod 2 := (lamIdx (idx s) : ℕ)

theorem f_d (i j : Fin 64) : f (d i) (d j) = (fIdx i j : ℕ) := by simp [f]

theorem lam0_d (j : Fin 64) : lam0 (d j) = (lam0Idx j : ℕ) := by simp [lam0]

theorem mu_d (j : Fin 64) : mu (d j) = (muIdx j : ℕ) := by simp [mu]

theorem lam_d (j : Fin 64) : lam (d j) = (lamIdx j : ℕ) := by simp [lam]

theorem zmod2_eq_of_mod {a b : ℕ} (h : a % 2 = b % 2) : (a : ZMod 2) = b := by
  rw [← ZMod.natCast_mod a 2, h, ZMod.natCast_mod]

theorem cocycleCheck_eq : cocycleCheck = true :=
  Certificates.certificate11000.1

theorem idx_one : idx 1 = 0 := by rw [← d_zero, idx_d]

theorem f_cocycle_of_check {y : Fin 64}
    (hy : ∀ j < 64, ∀ k < 64,
      (fIdx y j + fIdx (mIdx y j) k) % 2 = (fIdx j k + fIdx y (mIdx j k)) % 2) (t u : S) :
    f (d y) t + f (d y * t) u = f t u + f (d y) (t * u) := by
  obtain ⟨j, rfl⟩ := d_surjective t
  obtain ⟨k, rfl⟩ := d_surjective u
  rw [← d_mul, ← d_mul, f_d, f_d, f_d, f_d, ← Nat.cast_add, ← Nat.cast_add]
  exact zmod2_eq_of_mod (hy j j.2 k k.2)

theorem cocycle_table {y : ℕ} (hy : y ∈ [8, 61, 54, 59]) (y' : ℕ) (hy' : y' ∈ [y, invIdx y]) :
    ∀ j < 64, ∀ k < 64,
      (fIdx y' j + fIdx (mIdx y' j) k) % 2 = (fIdx j k + fIdx y' (mIdx j k)) % 2 := by
  have h := cocycleCheck_eq
  rw [cocycleCheck, Bool.and_eq_true] at h
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 h.2 y hy) y' hy'
  exact fun j hj k hk => Nat.eq_of_beq_eq_true (all_range (all_range h2 hj) hk)

theorem fIdx_zero {j : ℕ} (hj : j < 64) : fIdx 0 j = 0 ∧ fIdx j 0 = 0 := by
  have h := cocycleCheck_eq
  rw [cocycleCheck, Bool.and_eq_true] at h
  have := all_range h.1 hj
  rw [Bool.and_eq_true] at this
  exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem f_one_left (t : S) : f 1 t = 0 := by
  obtain ⟨j, rfl⟩ := d_surjective t
  rw [f, idx_one, idx_d]
  change ((fIdx 0 j : ℕ) : ZMod 2) = 0
  rw [(fIdx_zero j.2).1, Nat.cast_zero]

theorem f_one_right (s : S) : f s 1 = 0 := by
  obtain ⟨j, rfl⟩ := d_surjective s
  rw [f, idx_one, idx_d]
  change ((fIdx j 0 : ℕ) : ZMod 2) = 0
  rw [(fIdx_zero j.2).2, Nat.cast_zero]

theorem f_cocycle (s t w : S) : f s t + f (s * t) w = f t w + f s (t * w) := by
  have hY : Subgroup.closure (((↑) : S → NativeSporadic.M12) ⁻¹'
      Set.range fun j => g * u j * g⁻¹) = ⊤ := Subgroup.closure_closure_coe_preimage
  have hgen : ∀ y ∈ ((↑) : S → NativeSporadic.M12) ⁻¹' Set.range fun j => g * u j * g⁻¹,
      ∃ k : Fin 4, y = d (genIdx k) := by
    rintro y ⟨k, hk⟩
    exact ⟨k, Subtype.ext ((d_genIdx k).trans hk).symm⟩
  have hgen_mem : ∀ k : Fin 4, ((genIdx k : Fin 64) : ℕ) ∈ [8, 61, 54, 59] := by decide
  refine cocycle_of_closure hY f_one_left (fun y hy a b => ?_) (fun y hy a b => ?_) s t w
  · obtain ⟨k, rfl⟩ := hgen y hy
    exact f_cocycle_of_check (cocycle_table (hgen_mem k) _ (List.mem_cons_self ..)) a b
  · obtain ⟨k, rfl⟩ := hgen y hy
    rw [d_inv]
    exact f_cocycle_of_check (cocycle_table (hgen_mem k) _ (by simp)) a b

@[expose] noncomputable def fN : NormCocycle S := ⟨f, f_one_left, f_one_right, f_cocycle⟩

theorem fN_apply (s t : S) : fN s t = f s t := rfl

theorem diagCheck_eq : diagCheck = true :=
  Certificates.certificate11000.2.1

theorem f_diag (q : S) (hq : orderOf q = 2) :
    ((Finset.univ.filter fun p : Fin 12 =>
        ((q : NativeSporadic.M12) : Equiv.Perm (Fin 12)) p = p).card = 4 ∧ f q q = 0) ∨
      ((Finset.univ.filter fun p : Fin 12 =>
        ((q : NativeSporadic.M12) : Equiv.Perm (Fin 12)) p = p).card = 0 ∧ f q q = 1) := by
  obtain ⟨j, rfl⟩ := d_surjective q
  rw [orderOf_eq_prime_iff, sq, ← d_mul, ← d_zero] at hq
  have hjj : mIdx j j = 0 := congrArg Fin.val (d_injective hq.1)
  have hj0 : (j : ℕ) ≠ 0 := fun h => hq.2 (congrArg d (Fin.ext h))
  have h := all_range diagCheck_eq j.2
  simp only [hjj, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq, hj0,
    false_or, Bool.and_eq_true] at h
  rw [card_fixed_eq (isFCode_d j), f_d]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, by rw [h2]; rfl⟩
  · exact Or.inr ⟨h1, by rw [h2]; rfl⟩

theorem f_diag_four (q : S) (hq : orderOf q = 2)
    (h4 : (Finset.univ.filter fun p : Fin 12 =>
      ((q : NativeSporadic.M12) : Equiv.Perm (Fin 12)) p = p).card = 4) : f q q = 0 := by
  rcases f_diag q hq with h | h
  · exact h.2
  · rw [h.1] at h4
    exact absurd h4 (by norm_num)

theorem f_diag_free (q : S) (hq : orderOf q = 2)
    (h0 : (Finset.univ.filter fun p : Fin 12 =>
      ((q : NativeSporadic.M12) : Equiv.Perm (Fin 12)) p = p).card = 0) : f q q = 1 := by
  rcases f_diag q hq with h | h
  · rw [h.1] at h0
    exact absurd h0 (by norm_num)
  · exact h.2

abbrev R : Type := CocycleExtension fN

theorem autCheck_eq : autCheck = true :=
  Certificates.certificate11000.2.2

theorem autCheck_spec :
    (∀ i < 64, ∀ j < 64,
      (lam0Idx i + lam0Idx j + lam0Idx (mIdx i j)) % 2 = (fIdx (bIdx i) (bIdx j) + fIdx i j) % 2 ∧
      (lamIdx i + lamIdx j + lamIdx (mIdx i j)) % 2 = (fIdx (bIdx i) (bIdx j) + fIdx i j) % 2) ∧
    ∀ j < 64, (lam0Idx j + lam0Idx (bIdx j)) % 2 = 0 ∧ (lamIdx j + lamIdx (bIdx j)) % 2 = 0 := by
  have h := autCheck_eq
  rw [autCheck, Bool.and_eq_true] at h
  refine ⟨fun i hi j hj => ?_, fun j hj => ?_⟩
  · have := all_range (all_range h.1 hi) hj
    rw [Bool.and_eq_true] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  · have := all_range h.2 hj
    rw [Bool.and_eq_true] at this
    exact ⟨Nat.eq_of_beq_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem f_βS (i j : Fin 64) : f (βS (d i)) (βS (d j)) = (fIdx (bIdx i) (bIdx j) : ℕ) := by
  rw [βS_d, βS_d, f_d]
  rfl

theorem lam0_coboundary (s t : S) : lam0 s + lam0 t + lam0 (s * t) = f (βS s) (βS t) + f s t := by
  obtain ⟨i, rfl⟩ := d_surjective s
  obtain ⟨j, rfl⟩ := d_surjective t
  rw [← d_mul, lam0_d, lam0_d, lam0_d, f_βS, f_d, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  exact zmod2_eq_of_mod (autCheck_spec.1 i i.2 j j.2).1

theorem lam_coboundary (s t : S) : lam s + lam t + lam (s * t) = f (βS s) (βS t) + f s t := by
  obtain ⟨i, rfl⟩ := d_surjective s
  obtain ⟨j, rfl⟩ := d_surjective t
  rw [← d_mul, lam_d, lam_d, lam_d, f_βS, f_d, ← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
  exact zmod2_eq_of_mod (autCheck_spec.1 i i.2 j j.2).2

theorem lam0_add_lam0_βS (s : S) : lam0 s + lam0 (βS s) = 0 := by
  obtain ⟨j, rfl⟩ := d_surjective s
  rw [βS_d, lam0_d, lam0_d, ← Nat.cast_add, ← Nat.cast_zero]
  exact zmod2_eq_of_mod ((autCheck_spec.2 j j.2).1.trans (Nat.zero_mod 2).symm)

theorem lam_add_lam_βS (s : S) : lam s + lam (βS s) = 0 := by
  obtain ⟨j, rfl⟩ := d_surjective s
  rw [βS_d, lam_d, lam_d, ← Nat.cast_add, ← Nat.cast_zero]
  exact zmod2_eq_of_mod ((autCheck_spec.2 j j.2).2.trans (Nat.zero_mod 2).symm)

@[expose] noncomputable def tau0 : R ≃* R := cochainAut βS lam0 lam0_coboundary

@[expose] noncomputable def tau : R ≃* R := cochainAut βS lam lam_coboundary

theorem tau0_apply (x : R) : tau0 x = ⟨x.fst + lam0 x.snd, βS x.snd⟩ := rfl

theorem tau_apply (x : R) : tau x = ⟨x.fst + lam x.snd, βS x.snd⟩ := rfl

theorem lam0_one : lam0 1 = 0 := by
  rw [← d_zero, lam0_d]
  decide +kernel

theorem lam_one : lam 1 = 0 := by
  rw [← d_zero, lam_d]
  decide +kernel

theorem βS_one : βS 1 = 1 := map_one βS

theorem tau0_tau0 (x : R) : tau0 (tau0 x) = x := by
  refine CocycleExtension.ext ?_ ?_
  · simp only [tau0_apply, add_assoc, lam0_add_lam0_βS, add_zero]
  · simp only [tau0_apply, βS_βS]

theorem tau_tau (x : R) : tau (tau x) = x := by
  refine CocycleExtension.ext ?_ ?_
  · simp only [tau_apply, add_assoc, lam_add_lam_βS, add_zero]
  · simp only [tau_apply, βS_βS]

theorem tau0_z : tau0 ⟨1, 1⟩ = ⟨1, 1⟩ := by
  refine CocycleExtension.ext ?_ ?_
  · simp [tau0_apply, lam0_one]
  · simp [tau0_apply, βS_one]

theorem tau_z : tau ⟨1, 1⟩ = ⟨1, 1⟩ := by
  refine CocycleExtension.ext ?_ ?_
  · simp [tau_apply, lam_one]
  · simp [tau_apply, βS_one]

theorem proj_tau0 (x : R) : (tau0 x).snd = βS x.snd := rfl

theorem proj_tau (x : R) : (tau x).snd = βS x.snd := rfl

theorem card_R : Nat.card R = 128 := by
  rw [CocycleExtension.card_eq, card_S]

@[expose] def starN (x y : ℕ) : ℕ :=
  64 * ((x / 64 + y / 64 + fIdx (x % 64) (y % 64)) % 2) + mIdx (x % 64) (y % 64)

theorem mIdx_lt (i j : ℕ) : mIdx i j < 64 := packEntry_lt _ 6 _

theorem bIdx_lt (j : ℕ) : bIdx j < 64 := packEntry_lt _ 6 _

theorem starN_lt (x y : ℕ) : starN x y < 128 := by
  have := mIdx_lt (x % 64) (y % 64)
  have := Nat.mod_lt (x / 64 + y / 64 + fIdx (x % 64) (y % 64)) (show 0 < 2 by norm_num)
  unfold starN
  omega

@[expose] def star (x y : Fin 128) : Fin 128 := ⟨starN x y, starN_lt x y⟩

@[expose] def tauN (l : ℕ → ℕ) (x : ℕ) : ℕ := 64 * ((x / 64 + l (x % 64)) % 2) + bIdx (x % 64)

theorem tauN_lt (l : ℕ → ℕ) (x : ℕ) : tauN l x < 128 := by
  have := bIdx_lt (x % 64)
  have := Nat.mod_lt (x / 64 + l (x % 64)) (show 0 < 2 by norm_num)
  unfold tauN
  omega

@[expose] def tau0F (x : Fin 128) : Fin 128 := ⟨tauN lam0Idx x, tauN_lt _ _⟩

@[expose] def tauF (x : Fin 128) : Fin 128 := ⟨tauN lamIdx x, tauN_lt _ _⟩

@[expose] noncomputable def encRFun (x : ℕ) : R :=
  ⟨((x / 64 : ℕ) : ZMod 2), d ⟨x % 64, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] noncomputable def encR : Fin 128 ≃ R where
  toFun x := encRFun x
  invFun r := ⟨64 * r.fst.val + idx r.snd, by
    have := r.fst.val_lt; have := (idx r.snd).2; omega⟩
  left_inv x := by
    apply Fin.ext
    have hx := x.2
    simp only [encRFun, idx_d, ZMod.val_natCast]
    omega
  right_inv r := by
    have he := r.fst.val_lt
    have hs := (idx r.snd).2
    refine CocycleExtension.ext ?_ ?_
    · simp only [encRFun]
      rw [show (64 * r.fst.val + (idx r.snd : ℕ)) / 64 = r.fst.val by omega,
        ZMod.natCast_zmod_val]
    · exact (congrArg d (Fin.ext (by simp only; omega))).trans (d_idx r.snd)

theorem encR_apply (x : Fin 128) : encR x = encRFun x := rfl

theorem encRFun_mk (e : ℕ) (i : ℕ) (hi : i < 64) :
    encRFun (64 * e + i) = ⟨(e : ZMod 2), d ⟨i, hi⟩⟩ := by
  refine CocycleExtension.ext ?_ ?_
  · exact congrArg (fun n : ℕ => (n : ZMod 2)) (by omega)
  · exact congrArg d (Fin.ext (by simp only; omega))

theorem encRFun_eq (x : ℕ) : encRFun x = encRFun (64 * (x / 64) + x % 64) := by
  rw [Nat.div_add_mod]

theorem isTableModel_star : IsTableModel star encR := by
  intro x y
  have hx := x.2
  have hy := y.2
  have hm := mIdx_lt (x % 64) (y % 64)
  have h2 := Nat.mod_lt (x / 64 + y / 64 + fIdx (x % 64) (y % 64)) (show 0 < 2 by norm_num)
  simp only [encR_apply, star, starN]
  rw [encRFun_mk _ _ hm, encRFun_eq x, encRFun_eq y,
    encRFun_mk _ _ (Nat.mod_lt _ (by norm_num)),
    encRFun_mk _ _ (Nat.mod_lt _ (by norm_num))]
  refine CocycleExtension.ext ?_ ?_
  · simp only [CocycleExtension.mul_fst, fN_apply, f_d]
    rw [← Nat.cast_add, ← Nat.cast_add]
    exact zmod2_eq_of_mod (Nat.mod_mod _ _)
  · exact d_mul ⟨(x : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩
      ⟨(y : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩

theorem tauN_encR {l : ℕ → ℕ} {L : S → ZMod 2} (hL : ∀ j : Fin 64, L (d j) = (l j : ℕ))
    (x : Fin 128) :
    encRFun (tauN l x) = ⟨(encR x).fst + L (encR x).snd, βS (encR x).snd⟩ := by
  have hx := x.2
  have hb := bIdx_lt (x % 64)
  have h2 := Nat.mod_lt (x / 64 + l (x % 64)) (show 0 < 2 by norm_num)
  simp only [tauN, encR_apply]
  rw [encRFun_mk _ _ hb, encRFun_eq x, encRFun_mk _ _ (Nat.mod_lt _ (by norm_num))]
  refine CocycleExtension.ext ?_ ?_
  · simp only
    rw [hL, ← Nat.cast_add]
    exact zmod2_eq_of_mod (Nat.mod_mod _ _)
  · exact (βS_d ⟨(x : ℕ) % 64, Nat.mod_lt _ (by norm_num)⟩).symm

theorem encR_tau0F (x : Fin 128) : encR (tau0F x) = tau0 (encR x) := by
  rw [tau0_apply, ← tauN_encR lam0_d]
  rfl

theorem encR_tauF (x : Fin 128) : encR (tauF x) = tau (encR x) := by
  rw [tau_apply, ← tauN_encR lam_d]
  rfl

theorem encR_zero : encR 0 = 1 := by
  rw [encR_apply, show ((0 : Fin 128) : ℕ) = 64 * 0 + 0 from rfl,
    encRFun_mk 0 0 (by norm_num)]
  exact CocycleExtension.ext rfl d_zero

theorem encR_64 : encR 64 = ⟨1, 1⟩ := by
  rw [encR_apply, show ((64 : Fin 128) : ℕ) = 64 * 1 + 0 from rfl,
    encRFun_mk 1 0 (by norm_num)]
  exact CocycleExtension.ext rfl d_zero

theorem encR_27 : encR 27 = ⟨0, d 27⟩ := by
  rw [encR_apply, show ((27 : Fin 128) : ℕ) = 64 * 0 + 27 from rfl,
    encRFun_mk 0 27 (by norm_num)]
  rfl

theorem encR_91 : encR 91 = ⟨1, d 27⟩ := by
  rw [encR_apply, show ((91 : Fin 128) : ℕ) = 64 * 1 + 27 from rfl,
    encRFun_mk 1 27 (by norm_num)]
  rfl

end CFSG.ComponentClassification.M12Cover.InternalSylow

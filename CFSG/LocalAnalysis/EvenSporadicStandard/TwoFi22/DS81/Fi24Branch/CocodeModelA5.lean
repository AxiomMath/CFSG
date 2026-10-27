module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Check
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelStab

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5

open CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.ZTrans
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelPair
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelS6
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelStab
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Lin
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5Check

@[expose] def aPerm (j : ℕ) : Equiv.Perm (Fin 24) := wPerm [lzX, lzY] (wordOf j)

theorem hasArr_aPerm (j : ℕ) : HasArr (aPerm j) (aArr j) :=
  hasArr_wPerm (hasArr_getD₂ hasArr_lzX hasArr_lzY) (wordOf j)

theorem aPerm_mem_Lz (j : ℕ) : aPerm j ∈ Lz := by
  refine wPerm_mem (fun p hp => ?_) (wordOf j)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact lzX_mem_Lz
  · exact lzY_mem_Lz

theorem aPerm_mem_AutPerm (j : ℕ) : aPerm j ∈ AutPerm := Lz_le (aPerm_mem_Lz j)

@[expose] noncomputable def aAut (j : ℕ) : MulAut W11 :=
  rho11 AutPerm le_rfl ⟨aPerm j, aPerm_mem_AutPerm j⟩

@[expose] noncomputable def a1Aut : MulAut W11 := aAut 0

@[expose] noncomputable def a2Aut : MulAut W11 := aAut 1

@[expose] noncomputable def Abar : Subgroup (MulAut W11) := Subgroup.closure {a1Aut, a2Aut}

theorem a1Aut_mem_Abar : a1Aut ∈ Abar := Subgroup.subset_closure (Set.mem_insert _ _)

theorem a2Aut_mem_Abar : a2Aut ∈ Abar := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem aAut_toW (j m : ℕ) : aAut j (toW 11 m) = toW 11 (act11 (aArr j) m) :=
  rho11_toW AutPerm le_rfl ⟨aPerm j, aPerm_mem_AutPerm j⟩ (hasArr_aPerm j) m

theorem aAut_t0 {j : ℕ} (hj : j < 2) : aAut j t0 = t0 := by
  rw [show t0 = toW 11 32 from rfl, aAut_toW, (act11_aArr_fix j hj).1]

theorem aAut_z0 {j : ℕ} (hj : j < 2) : aAut j z0 = z0 := by
  rw [show z0 = toW 11 31 from rfl, aAut_toW, (act11_aArr_fix j hj).2]

theorem aAut_mem_img11_Lz (j : ℕ) : aAut j ∈ img11 Lz :=
  ⟨⟨aPerm j, aPerm_mem_AutPerm j⟩, Subgroup.mem_subgroupOf.2 (aPerm_mem_Lz j), rfl⟩

theorem Abar_le_img11_Lz : Abar ≤ img11 Lz := by
  rw [Abar, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact aAut_mem_img11_Lz 0
  · exact aAut_mem_img11_Lz 1

theorem apply_eq_of_mem_closure {S : Set (MulAut W11)} {v : W11} (h : ∀ a ∈ S, a v = v)
    {a : MulAut W11} (ha : a ∈ Subgroup.closure S) : a v = v := by
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => rfl
  | mul x y _ _ hx hy => rw [MulAut.mul_apply, hy, hx]
  | inv x _ hx =>
    have e : x⁻¹ (x v) = v := MulAut.inv_apply_self _ _ v
    rwa [hx] at e

theorem apply_t0_of_mem_Abar {a : MulAut W11} (ha : a ∈ Abar) : a t0 = t0 := by
  refine apply_eq_of_mem_closure (fun x hx => ?_) ha
  rcases hx with rfl | rfl
  · exact aAut_t0 (by norm_num)
  · exact aAut_t0 (by norm_num)

theorem apply_z0_of_mem_Abar {a : MulAut W11} (ha : a ∈ Abar) : a z0 = z0 := by
  refine apply_eq_of_mem_closure (fun x hx => ?_) ha
  rcases hx with rfl | rfl
  · exact aAut_z0 (by norm_num)
  · exact aAut_z0 (by norm_num)

theorem Abar_le_stabSub_V0 : Abar ≤ stabSub V0 := fun a ha =>
  mem_stabSub_V0_of (by rw [apply_t0_of_mem_Abar ha]; exact mem_V0_iff.2 (Or.inr (Or.inl rfl)))
    (by rw [apply_z0_of_mem_Abar ha]; exact mem_V0_iff.2 (Or.inr (Or.inr (Or.inl rfl))))

theorem Abar_le_Sz : Abar ≤ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0) :=
  Abar_le_img11_Lz.trans img11_Lz_le_stab

theorem Abar_le_stab : Abar ≤ img11 AutPerm ⊓ stabSub V0 :=
  le_inf (Abar_le_Sz.trans inf_le_left) Abar_le_stabSub_V0

@[expose] noncomputable def maskOf (v : W11) : ℕ := Classical.choose (toW_surj 11 v)

theorem maskOf_lt (v : W11) : maskOf v < 2 ^ 11 := (Classical.choose_spec (toW_surj 11 v)).1

theorem toW_maskOf (v : W11) : toW 11 (maskOf v) = v := (Classical.choose_spec (toW_surj 11 v)).2

theorem maskOf_toW {m : ℕ} (hm : m < 2 ^ 11) : maskOf (toW 11 m) = m :=
  toW_inj (maskOf_lt _) hm (toW_maskOf _)

theorem maskOf_mul (u v : W11) : maskOf (u * v) = maskOf u ^^^ maskOf v := by
  refine toW_inj (maskOf_lt _) (Nat.xor_lt_two_pow (maskOf_lt u) (maskOf_lt v)) ?_
  rw [toW_maskOf, toW_xor, toW_maskOf, toW_maskOf]

theorem inv_eq_self_W11 (v : W11) : v⁻¹ = v := by
  conv_lhs => rw [← toW_maskOf v]
  rw [toW_inv, toW_maskOf]

theorem mem_W0_iff_maskOf (v : W11) : v ∈ W0 ↔ maskOf v ∈ combos w0Basis := by
  constructor
  · rintro ⟨m, hm, e⟩
    have : m = maskOf v :=
      toW_inj (combos_lt w0_lt m hm) (maskOf_lt v) (e.trans (toW_maskOf v).symm)
    rwa [← this]
  · intro h
    exact ⟨maskOf v, h, toW_maskOf v⟩

@[expose] noncomputable def qv (v : W11) : ℕ := actM qCols (maskOf v)

theorem qv_lt (v : W11) : qv v < 16 := actM_lt qCols_lt _

theorem qv_mul (u v : W11) : qv (u * v) = qv u ^^^ qv v := by
  rw [qv, qv, qv, maskOf_mul]
  exact actM_xor _ _ _

theorem qv_inv (v : W11) : qv v⁻¹ = qv v := by rw [inv_eq_self_W11]

theorem qv_eq_zero_iff (v : W11) : qv v = 0 ↔ v ∈ W0 := by
  rw [mem_W0_iff_maskOf]
  exact ⟨mem_combos_of_actM_qCols _ (maskOf_lt v), actM_qCols_of_mem _⟩

theorem qv_eq_of_inv_mul_mem {u v : W11} (h : u⁻¹ * v ∈ W0) : qv u = qv v := by
  have h0 := (qv_eq_zero_iff _).2 h
  rw [qv_mul, qv_inv] at h0
  have h1 := congrArg (fun x => x ^^^ qv v) h0
  simpa [Nat.xor_assoc] using h1

theorem qv_aAut {j : ℕ} (hj : j < 2) (v : W11) :
    qv (aAut j v) = actM (mqs.getD j []) (qv v) := by
  have h1 : aAut j v = toW 11 (act11 (aArr j) (maskOf v)) := by
    have h := aAut_toW j (maskOf v)
    rwa [toW_maskOf] at h
  rw [qv, h1, maskOf_toW (act11_lt _ _)]
  exact act11_aArr_q hj (maskOf v) (maskOf_lt v)

@[expose] noncomputable def kb (c : Fin 64) : MulAut W11 :=
  rho11 AutPerm le_rfl ⟨ksP c, ksP_mem_autPerm c⟩

theorem kb_mul (c d : Fin 64) :
    kb c * kb d = kb ⟨c.val ^^^ d.val, Nat.xor_lt_two_pow (n := 6) c.2 d.2⟩ := rho_ksP_mul c d

theorem mem_img11_KSp_iff {k : MulAut W11} : k ∈ img11 KSp ↔ ∃ c, kb c = k := mem_img11_KSp

theorem kb_mem (c : Fin 64) : kb c ∈ img11 KSp := mem_img11_KSp_iff.2 ⟨c, rfl⟩

@[expose] noncomputable def kbN (c : ℕ) : MulAut W11 := kb ⟨c % 64, Nat.mod_lt _ (by norm_num)⟩

theorem kbN_of_lt {c : ℕ} (hc : c < 64) : kbN c = kb ⟨c, hc⟩ := by
  rw [kbN]
  exact congrArg kb (Fin.ext (Nat.mod_eq_of_lt hc))

theorem kbN_mem (c : ℕ) : kbN c ∈ img11 KSp := kb_mem _

theorem kbN_xor (a b : ℕ) : kbN (a ^^^ b) = kbN a * kbN b := by
  rw [kbN, kbN, kbN, kb_mul]
  refine congrArg kb (Fin.ext ?_)
  simpa using Nat.xor_mod_two_pow (a := a) (b := b) (n := 6)

theorem aAut_conj_kb {j : ℕ} (hj : j < 2) (c : Fin 64) :
    aAut j * kb c * (aAut j)⁻¹ = kb ⟨wActM (wordOf j) c, wActM_lt _ c.2⟩ := by
  unfold aAut kb
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg (rho11 AutPerm le_rfl)
    (Subtype.ext (wPerm_conj_ksP (wordOf j) (wordOf_lt j hj) c))

theorem qv_equiv {ψ : MulAut W11 → W11}
    (hequiv : ∀ a ∈ ({a1Aut, a2Aut} : Set (MulAut W11)), ∀ k ∈ img11 KSp,
      (ψ (a * k * a⁻¹))⁻¹ * a (ψ k) ∈ W0) {j : ℕ} (hj : j < 2) {i : ℕ} (hi : i < 6) :
    qv (ψ (kbN (cPs.getD (6 * j + i) 0))) = actM (mqs.getD j []) (qv (ψ (kbN (2 ^ i)))) := by
  have hj' : aAut j ∈ ({a1Aut, a2Aut} : Set (MulAut W11)) := by
    interval_cases j
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h2i : 2 ^ i < 64 := by
    interval_cases i <;> norm_num
  have e := hequiv (aAut j) hj' (kbN (2 ^ i)) (kbN_mem _)
  have e1 : aAut j * kbN (2 ^ i) * (aAut j)⁻¹ = kbN (cPs.getD (6 * j + i) 0) := by
    rw [kbN_of_lt h2i, aAut_conj_kb hj, ← wActM_cPs j hj i hi, kbN_of_lt (wActM_lt _ h2i)]
  rw [e1] at e
  rw [qv_eq_of_inv_mul_mem e, qv_aAut hj]

theorem homVanish_model_gen (ψ : MulAut W11 → W11)
    (hhom : ∀ k₁ ∈ img11 KSp, ∀ k₂ ∈ img11 KSp, (ψ (k₁ * k₂))⁻¹ * (ψ k₁ * ψ k₂) ∈ W0)
    (hequiv : ∀ a ∈ ({a1Aut, a2Aut} : Set (MulAut W11)), ∀ k ∈ img11 KSp,
      (ψ (a * k * a⁻¹))⁻¹ * a (ψ k) ∈ W0) :
    ∀ k ∈ img11 KSp, ψ k ∈ W0 := by
  let g : ℕ → ℕ := fun c => qv (ψ (kbN c))
  have hg : XorLin g := by
    intro a b
    have hmem := hhom (kbN a) (kbN_mem a) (kbN b) (kbN_mem b)
    show qv (ψ (kbN (a ^^^ b))) = qv (ψ (kbN a)) ^^^ qv (ψ (kbN b))
    rw [kbN_xor, qv_eq_of_inv_mul_mem hmem, qv_mul]
  have hlt : ∀ c, g c < 16 := fun c => qv_lt _
  have h : ∀ k < 7, k ≠ 3 →
      g (cPs.getD k 0) = actM (mqs.getD (k / 6) []) (g (2 ^ (k % 6))) := by
    intro k hk _
    have hj : k / 6 < 2 := by omega
    have hi : k % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have e := qv_equiv hequiv (j := k / 6) (i := k % 6) hj hi
    rw [show 6 * (k / 6) + k % 6 = k from Nat.div_add_mod k 6] at e
    exact e
  have hz := lin_vanish g hg hlt h
  intro k hk
  obtain ⟨c, rfl⟩ := mem_img11_KSp_iff.1 hk
  have h0 : g c.val = 0 := hz c.val c.2
  have h1 : qv (ψ (kb c)) = 0 := by
    have e : g c.val = qv (ψ (kb c)) := by
      show qv (ψ (kbN c.val)) = qv (ψ (kb c))
      rw [kbN_of_lt c.2, Fin.eta]
    exact e ▸ h0
  exact (qv_eq_zero_iff _).1 h1

theorem homVanish_model (ψ : MulAut W11 → W11)
    (hhom : ∀ k₁ ∈ img11 KSp, ∀ k₂ ∈ img11 KSp, (ψ (k₁ * k₂))⁻¹ * (ψ k₁ * ψ k₂) ∈ W0)
    (hequiv : ∀ a ∈ Abar, ∀ k ∈ img11 KSp, (ψ (a * k * a⁻¹))⁻¹ * a (ψ k) ∈ W0) :
    ∀ k ∈ img11 KSp, ψ k ∈ W0 :=
  homVanish_model_gen ψ hhom fun a ha k hk => hequiv a (by
    rcases ha with rfl | rfl
    · exact a1Aut_mem_Abar
    · exact a2Aut_mem_Abar) k hk

theorem homVanishX_model :
    ∀ ψ : MulAut W11 → W11,
      (∀ k₁ ∈ img11 KSp, ∀ k₂ ∈ img11 KSp, (ψ (k₁ * k₂))⁻¹ * (ψ k₁ * ψ k₂) ∈ W0) →
      (∀ a ∈ Abar, ∀ k ∈ img11 KSp, (ψ (a * k * a⁻¹))⁻¹ * a (ψ k) ∈ W0) →
      ∀ k ∈ img11 KSp, ψ k ∈ W0 :=
  fun ψ hhom hequiv => homVanish_model ψ hhom hequiv

theorem lzX_mul_r0 : lzX * r0 = ksP 34 * r0 * lzX := by
  have h1 := hasArr_mul hasArr_lzX hasArr_r0
  have h2 : HasArr (ksP 34 * r0 * lzX) (cArr lzXArr r0Arr) := by
    rw [cArr_central_x]
    exact hasArr_mul (hasArr_mul (hasArr_ksP 34) hasArr_r0) hasArr_lzX
  exact perm_eq_of_hasArr h1 h2

theorem lzY_mul_r0 : lzY * r0 = ksP 3 * r0 * lzY := by
  have h1 := hasArr_mul hasArr_lzY hasArr_r0
  have h2 : HasArr (ksP 3 * r0 * lzY) (cArr lzYArr r0Arr) := by
    rw [cArr_central_y]
    exact hasArr_mul (hasArr_mul (hasArr_ksP 3) hasArr_r0) hasArr_lzY
  exact perm_eq_of_hasArr h1 h2

theorem commutator_r0_mem_KSp {g : Equiv.Perm (Fin 24)} (hg : g ∈ Lz) :
    g * r0 * g⁻¹ * r0⁻¹ ∈ KSp := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · have h : lzX * r0 * lzX⁻¹ * r0⁻¹ = ksP 34 := by
        rw [lzX_mul_r0]; group
      rw [h]; exact ksP_mem_KSp 34
    · have h : lzY * r0 * lzY⁻¹ * r0⁻¹ = ksP 3 := by
        rw [lzY_mul_r0]; group
      rw [h]; exact ksP_mem_KSp 3
  | one => simpa using KSp.one_mem
  | mul x y hx hy ihx ihy =>
    have hid : (x * y) * r0 * (x * y)⁻¹ * r0⁻¹ =
        (x * (y * r0 * y⁻¹ * r0⁻¹) * x⁻¹) * (x * r0 * x⁻¹ * r0⁻¹) := by group
    rw [hid]
    exact KSp.mul_mem
      ((Subgroup.mem_normalizer_iff.1 (Lz_le_normalizer_KSp hx)
        (y * r0 * y⁻¹ * r0⁻¹)).1 ihy) ihx
  | inv x hx ih =>
    have hid : x⁻¹ * r0 * (x⁻¹)⁻¹ * r0⁻¹ =
        x⁻¹ * (x * r0 * x⁻¹ * r0⁻¹)⁻¹ * (x⁻¹)⁻¹ := by group
    rw [hid]
    exact (Subgroup.mem_normalizer_iff.1 (Lz_le_normalizer_KSp (Lz.inv_mem hx))
      ((x * r0 * x⁻¹ * r0⁻¹)⁻¹)).1 (KSp.inv_mem ih)

theorem commutator_r0Aut_mem_img11_KSp {g : MulAut W11} (hg : g ∈ img11 Lz) :
    g * r0Aut * g⁻¹ * r0Aut⁻¹ ∈ img11 KSp := by
  obtain ⟨σ, hσ, rfl⟩ := hg
  have hmem : (σ : Equiv.Perm (Fin 24)) * r0 * (σ : Equiv.Perm (Fin 24))⁻¹ * r0⁻¹ ∈ AutPerm :=
    AutPerm.mul_mem (AutPerm.mul_mem (AutPerm.mul_mem σ.2 r0_mem_AutPerm)
      (AutPerm.inv_mem σ.2)) (AutPerm.inv_mem r0_mem_AutPerm)
  refine ⟨⟨_, hmem⟩, Subgroup.mem_subgroupOf.2
    (commutator_r0_mem_KSp (Subgroup.mem_subgroupOf.1 hσ)), ?_⟩
  have e : (⟨(σ : Equiv.Perm (Fin 24)) * r0 * (σ : Equiv.Perm (Fin 24))⁻¹ * r0⁻¹, hmem⟩ :
      ↥AutPerm) = σ * ⟨r0, r0_mem_AutPerm⟩ * σ⁻¹ * ⟨r0, r0_mem_AutPerm⟩⁻¹ := rfl
  unfold r0Aut
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]

theorem conj_mem_img11_KSp_of_mem_img11_Lz {a k : MulAut W11} (ha : a ∈ img11 Lz)
    (hk : k ∈ img11 KSp) : a * k * a⁻¹ ∈ img11 KSp := by
  obtain ⟨σ, hσ, rfl⟩ := ha
  obtain ⟨κ, hκ, rfl⟩ := hk
  refine ⟨σ * κ * σ⁻¹, Subgroup.mem_subgroupOf.2 ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.1 (Lz_le_normalizer_KSp (Subgroup.mem_subgroupOf.1 hσ)) κ).1
    (Subgroup.mem_subgroupOf.1 hκ)

theorem img11_Lz_le_normalizer_img11_KSp :
    img11 Lz ≤ Subgroup.normalizer (img11 KSp : Set (MulAut W11)) := fun a ha =>
  Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => conj_mem_img11_KSp_of_mem_img11_Lz ha hk,
    fun hk => by
      have h := conj_mem_img11_KSp_of_mem_img11_Lz ((img11 Lz).inv_mem ha) hk
      have e : a⁻¹ * (a * k * a⁻¹) * a⁻¹⁻¹ = k := by group
      rwa [e] at h⟩

theorem commutator_mem_img11_KSp_of_mem_sup {a r : MulAut W11} (ha : a ∈ img11 Lz)
    (hr : r ∈ img11 KSp ⊔ Subgroup.zpowers r0Aut) : a * r * a⁻¹ * r⁻¹ ∈ img11 KSp := by
  let K : Subgroup (MulAut W11) := img11 KSp
  let H' : Subgroup (MulAut W11) :=
    { carrier := {r | r ∈ Subgroup.normalizer (K : Set (MulAut W11)) ∧
        a * r * a⁻¹ * r⁻¹ ∈ K}
      mul_mem' := by
        rintro r1 r2 ⟨hr1n, hr1c⟩ ⟨hr2n, hr2c⟩
        refine ⟨mul_mem hr1n hr2n, ?_⟩
        have hid : a * (r1 * r2) * a⁻¹ * (r1 * r2)⁻¹ =
            (a * r1 * a⁻¹ * r1⁻¹) * (r1 * (a * r2 * a⁻¹ * r2⁻¹) * r1⁻¹) := by group
        rw [hid]
        exact K.mul_mem hr1c ((Subgroup.mem_normalizer_iff.1 hr1n _).1 hr2c)
      one_mem' := ⟨Subgroup.one_mem _, by simpa using K.one_mem⟩
      inv_mem' := by
        rintro r ⟨hrn, hrc⟩
        refine ⟨inv_mem hrn, ?_⟩
        have hid : a * r⁻¹ * a⁻¹ * (r⁻¹)⁻¹ =
            r⁻¹ * (a * r * a⁻¹ * r⁻¹)⁻¹ * (r⁻¹)⁻¹ := by group
        rw [hid]
        exact (Subgroup.mem_normalizer_iff.1 (inv_mem hrn) _).1 (K.inv_mem hrc) }
  have hK : K ≤ H' := by
    intro r hr
    refine ⟨Subgroup.le_normalizer hr, ?_⟩
    have hid : a * r * a⁻¹ * r⁻¹ = (a * r * a⁻¹) * r⁻¹ := by group
    rw [hid]
    exact K.mul_mem (conj_mem_img11_KSp_of_mem_img11_Lz ha hr) (K.inv_mem hr)
  have hZ : Subgroup.zpowers r0Aut ≤ H' :=
    Subgroup.zpowers_le.mpr
      ⟨img11_Lz_le_normalizer_img11_KSp r0Aut_mem_img11_Lz,
        commutator_r0Aut_mem_img11_KSp ha⟩
  exact (sup_le hK hZ hr).2

theorem commutator_mem_img11_KSp_of_mem_O23In
    {a r : MulAut W11} (ha : a ∈ img11 Lz)
    (hr : r ∈ O23In (img11 AutPerm ⊓ centSub (Subgroup.zpowers z0))) :
    a * r * a⁻¹ * r⁻¹ ∈ img11 KSp := by
  rw [O23In_Sz_eq] at hr
  exact commutator_mem_img11_KSp_of_mem_sup ha hr

theorem eq_W0_of_apply_mem_of_card_eq {Y : Subgroup W11}
    (hY : ∀ g ∈ img11 Lz, ∀ v ∈ Y, g v ∈ Y) (hc : Nat.card Y = 2 ^ 7) : Y = W0 := by
  rcases eq_of_forall_apply_mem hY with h | h | h | h
  · rw [h, Subgroup.card_bot] at hc
    norm_num at hc
  · rw [h, lat_card_zpowers_z0] at hc
    norm_num at hc
  · exact h
  · rw [h, Subgroup.card_top, natCard_W11] at hc
    norm_num at hc

theorem eq_W0_of_Sz_invariant {Y : Subgroup W11}
    (hY : ∀ g ∈ img11 AutPerm ⊓ centSub (Subgroup.zpowers z0), ∀ v ∈ Y, g v ∈ Y)
    (hc : Nat.card Y = 2 ^ 7) : Y = W0 :=
  eq_W0_of_apply_mem_of_card_eq (fun g hg v hv => hY g (img11_Lz_le_stab hg) v hv) hc

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelA5

module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3ZCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDWedge
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DOrb
public import CFSG.Monster.B.TwoA.Census.PermClasses

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaPar CFSG.EvenSmallLie.UnitarySix.YamadaD
open Matrix (mulVec)
open scoped Matrix

theorem toVec_xor (n a b : ℕ) : toVec n (a ^^^ b) = toVec n a + toVec n b := by
  funext j
  simp only [toVec, Nat.testBit_xor, Pi.add_apply, bz_xor]

theorem eq_zero_of_toVec {n v : ℕ} (hv : v < 2 ^ n) (h : toVec n v = 0) : v = 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit]
  by_cases hj : j < n
  · have := congrFun h ⟨j, hj⟩
    simp only [toVec, Pi.zero_apply] at this
    cases hb : v.testBit j
    · rfl
    · rw [hb] at this
      exact absurd this (by decide)
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num)
      (by omega)))

theorem exists_toVec (n : ℕ) (v : Fin n → ZMod 2) : ∃ m < 2 ^ n, toVec n m = v := by
  set f : ℕ → Bool := fun j => if h : j < n then v ⟨j, h⟩ == 1 else false
  refine ⟨bitsOf n f, Nat.lt_pow_two_of_testBit _ fun i hi => ?_, ?_⟩
  · rw [testBit_bitsOf]
    simp [show ¬ i < n by omega]
  · funext j
    simp only [toVec, testBit_bitsOf, j.isLt, decide_true, Bool.true_and, f]
    exact bz_beq_one _

@[expose] def kNP (g : Equiv.Perm (Fin 693)) : ℕ := pt1Mask[((g 1 : Fin 693) : ℕ)]!

@[expose] def kWP (g : Equiv.Perm (Fin 693)) : ℕ :=
  ((a4KeyTab.find? fun p => p.1 == ((g 3 : Fin 693) : ℕ) && p.2.1 == ((g 1 : Fin 693) : ℕ)).map
    fun p => p.2.2).getD 0

theorem kNA_eq {a : Array ℕ} {g : Equiv.Perm (Fin 693)} (h : Rep 693 a g) : kNA a = kNP g := by
  rw [kNA, kNP, h.apply (by norm_num : 1 < 693)]
  rfl

theorem kWA_eq {a : Array ℕ} {g : Equiv.Perm (Fin 693)} (h : Rep 693 a g) : kWA a = kWP g := by
  rw [kWA, kWP, h.apply (by norm_num : 1 < 693), h.apply (by norm_num : 3 < 693)]
  rfl

theorem pt1Mask_lt : ∀ p ∈ pt1Mask, p < 256 := by decide +kernel

section Spec

theorem coordN_spec : kNP 1 = 0 ∧
    (∀ g ∈ chA1.grp, ∀ w ∈ chA1.gens, kNP (g * wP w) = kNP g ^^^ kNP (wP w)) ∧
    (∀ g ∈ chA1.grp, (kNP g = 0 ↔ g ∈ chZ.grp)) ∧
    (∀ g ∈ chA1.grp, ∀ j < 5, kNP (wP chK1.gens[j]! * g * (wP chK1.gens[j]!)⁻¹) =
      bmulVec 8 8 (wedgeGensN.getD j #[]) (kNP g)) ∧
    ∀ v < 256, ∃ g ∈ chA1.grp, kNP g = v := by
  have h0 := coordNGen_check
  unfold coordNGenCheck at h0
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h0
  obtain ⟨⟨h1, -⟩, h3⟩ := h0
  refine ⟨by rw [← kNA_eq rep_idA]; exact h1, ?_, ?_, ?_, ?_⟩
  · intro g hg w hw
    obtain ⟨a, hX, h⟩ := coordN_check g hg
    unfold coordNAt at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := all_O_spec (p := fun s => kNA (compA 693 a s) == (kNA a ^^^ kNA s)) h.1.1 w hw
    simp only [beq_iff_eq] at this
    rwa [kNA_eq (rep_compA hX (rep_wA_gens gensOK_chA1 hw)), kNA_eq hX,
      kNA_eq (rep_wA_gens gensOK_chA1 hw)] at this
  · intro g hg
    obtain ⟨a, hX, h⟩ := coordN_check g hg
    unfold coordNAt at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have h' := h.1.2
    have hs := mem_chZ_iff hX
    rw [kNA_eq hX] at h'
    constructor
    · intro hk
      rw [hk] at h'
      exact hs.2 (by rw [← h']; rfl)
    · intro hz
      have h5 := hs.1 hz
      rw [h5] at h'
      simpa using h'
  · intro g hg j hj
    obtain ⟨a, hX, h⟩ := coordN_check g hg
    unfold coordNAt at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    have hjj := h.2 j hj
    have hlen : j < chK1.gens.length := by simpa [chK1] using hj
    have hO : chK1.O[j]! = wA chK1.gens[j]! := by
      rw [chK1.O_getElem hlen, getElem!_pos chK1.gens j hlen]
    have hv : validA 693 chK1.O[j]! = true := by
      rw [getElem!_pos chK1.O j (by rw [ChainData.O_size]; exact hlen)]
      exact Array.all_eq_true'.1 valid_spec.2.2.2.2.2.2.2.2.1 _ (Array.getElem_mem _)
    have hr : Rep 693 chK1.O[j]! (wP chK1.gens[j]!) := by
      rw [hO]
      exact rep_wA_gens gensOK_chK1 (by rw [getElem!_pos chK1.gens j hlen]; exact List.getElem_mem _)
    rwa [kNA_eq (rep_conj hv hr hX), kNA_eq hX] at hjj
  · intro v hv
    have hl : ∀ k ∈ coordNWit v, [k] ∈ chA1.gens ∧ k < 18 := by
      intro k hk
      unfold coordNWit at hk
      rw [List.mem_filterMap] at hk
      obtain ⟨i, hi, he⟩ := hk
      have hi' := List.mem_range.1 hi
      split_ifs at he
      rw [Option.some_inj] at he
      rw [← he]
      interval_cases i <;> decide
    refine ⟨wP (coordNWit v), wP_mem_of_letters _ fun k hk => (hl k hk).1, ?_⟩
    rw [← kNA_eq (rep_wA tabs_check _ fun k hk => (hl k hk).2)]
    exact h3 v hv

theorem coordW_spec : (∀ g ∈ chA4.grp, ∀ h ∈ chA4.grp, kWP (g * h) = kWP g ^^^ kWP h) ∧
    (∀ g ∈ chA4.grp, kWP g = 0 → g = 1) ∧
    (∀ g ∈ chA4.grp, ∀ j < 3, kWP (wP chLam.gens[j]! * g * (wP chLam.gens[j]!)⁻¹) =
      bmulVec 4 4 (wedgeGensW.getD j #[]) (kWP g)) ∧
    ∀ v < 16, ∃ g ∈ chA4.grp, kWP g = v := by
  have h3 := coordWGen_check
  unfold coordWGenCheck at h3
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg h hh
    obtain ⟨a, b, hX, hY, hab⟩ := coordWPair_check g hg h hh
    unfold coordWPairAt at hab
    simp only [beq_iff_eq] at hab
    rwa [kWA_eq (rep_compA hX hY), kWA_eq hX, kWA_eq hY] at hab
  · intro g hg h0
    obtain ⟨a, hX, h⟩ := coordW_check g hg
    unfold coordWAt at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
    rcases h.1 with h' | h'
    · rw [kWA_eq hX] at h'; exact absurd h0 h'
    · exact eq_one_of_eqA hX h'
  · intro g hg j hj
    obtain ⟨a, hX, h⟩ := coordW_check g hg
    unfold coordWAt at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    have hjj := h.2 j hj
    have hlen : j < chLam.gens.length := by simpa [chLam] using hj
    have hO : chLam.O[j]! = wA chLam.gens[j]! := by
      rw [chLam.O_getElem hlen, getElem!_pos chLam.gens j hlen]
    have hv : validA 693 chLam.O[j]! = true := by
      rw [getElem!_pos chLam.O j (by rw [ChainData.O_size]; exact hlen)]
      exact uA_valid.2.2.2.1 _ (Array.getElem_mem _)
    have hr : Rep 693 chLam.O[j]! (wP chLam.gens[j]!) := by
      rw [hO]
      exact rep_wA_gens gensOK_chLam (by rw [getElem!_pos chLam.gens j hlen]; exact List.getElem_mem _)
    rwa [kWA_eq (rep_conj hv hr hX), kWA_eq hX] at hjj
  · intro v hv
    have hl : ∀ k ∈ coordWWit v, [k] ∈ chA4.gens ∧ k < 18 := by
      intro k hk
      unfold coordWWit at hk
      rw [List.mem_filterMap] at hk
      obtain ⟨i, hi, he⟩ := hk
      have hi' := List.mem_range.1 hi
      split_ifs at he
      rw [Option.some_inj] at he
      rw [← he]
      interval_cases i <;> decide
    refine ⟨wP (coordWWit v), wP_mem_of_letters _ fun k hk => (hl k hk).1, ?_⟩
    rw [← kWA_eq (rep_wA tabs_check _ fun k hk => (hl k hk).2)]
    exact h3 v hv

theorem kNP_mul : ∀ h ∈ chA1.grp, ∀ g ∈ chA1.grp, kNP (g * h) = kNP g ^^^ kNP h := by
  intro h hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact fun g hg => coordN_spec.2.1 g hg w hw
  | one => exact fun g _ => by rw [mul_one, coordN_spec.1, Nat.xor_zero]
  | mul x y hx hy ihx ihy =>
    intro g hg
    rw [← mul_assoc, ihy _ (mul_mem hg hx), ihx g hg, ihy x hx, Nat.xor_assoc]
  | inv x hx ihx =>
    intro g hg
    have h1 := ihx (g * x⁻¹) (mul_mem hg (inv_mem hx))
    have h2 := ihx x⁻¹ (inv_mem hx)
    rw [inv_mul_cancel_right] at h1
    rw [inv_mul_cancel, coordN_spec.1] at h2
    have h3 : kNP x⁻¹ = kNP x := by
      have := congrArg (· ^^^ kNP x) h2
      simp only [Nat.zero_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
      exact this.symm
    rw [h3, h1, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

end Spec

theorem pt1Mask_size : pt1Mask.size = 693 := by decide +kernel

theorem kNP_lt (g : Equiv.Perm (Fin 693)) : kNP g < 2 ^ 8 := by
  have hs : pt1Mask.size = 693 := pt1Mask_size
  have hi : ((g 1 : Fin 693) : ℕ) < pt1Mask.size := by rw [hs]; exact (g 1).2
  rw [kNP, getElem!_pos pt1Mask _ hi]
  exact pt1Mask_lt _ (Array.getElem_mem hi)

theorem kWP_lt (g : Equiv.Perm (Fin 693)) : kWP g < 2 ^ 4 := by
  have ht : ∀ p ∈ a4KeyTab, p.2.2 < 16 := by decide +kernel
  rw [kWP]
  cases h : a4KeyTab.find? (fun p => p.1 == ((g 3 : Fin 693) : ℕ) && p.2.1 == ((g 1 : Fin 693) : ℕ))
  · simp
  · simp only [Option.map_some, Option.getD_some]
    exact ht _ (List.mem_of_find?_eq_some h)

section GLevel

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

open scoped Classical in
variable (e) in
@[expose] noncomputable def kappaN (x : G) : Fin 8 → ZMod 2 :=
  if h : x ∈ L then toVec 8 (kNP (e ⟨x, h⟩ : Equiv.Perm (Fin 693))) else 0

open scoped Classical in
variable (e) in
@[expose] noncomputable def kappaW (x : G) : Fin 4 → ZMod 2 :=
  if h : x ∈ L then toVec 4 (kWP (e ⟨x, h⟩ : Equiv.Perm (Fin 693))) else 0

theorem eL_iotaG (g : T46) : e ⟨iotaG e g, iotaG_mem g⟩ = g := by
  have : (⟨iotaG e g, iotaG_mem g⟩ : L) = e.symm g := rfl
  rw [this, MulEquiv.apply_symm_apply]

theorem kappaN_iotaG (g : T46) : kappaN e (iotaG e g) = toVec 8 (kNP g) := by
  rw [kappaN, dite_eq_left_of_eq_true (eq_true (iotaG_mem g)), eL_iotaG]

theorem kappaW_iotaG (g : T46) : kappaW e (iotaG e g) = toVec 4 (kWP g) := by
  rw [kappaW, dite_eq_left_of_eq_true (eq_true (iotaG_mem g)), eL_iotaG]

@[expose] noncomputable def gK₁ (j : Fin 5) : G := gw e chK1.gens[j.val]!

theorem gK₁_lt (j : Fin 5) : ∀ k ∈ chK1.gens[j.val]!, k < 18 := by
  have hmem : chK1.gens[j.val]! ∈ chK1.gens := by fin_cases j <;> decide
  exact gensOK_chK1 _ hmem

theorem gK₁_mem (j : Fin 5) : gK₁ (e := e) j ∈ sK₁ e := by
  have hmem : chK1.gens[j.val]! ∈ chK1.gens := by fin_cases j <;> decide
  exact (gw_mem_toG (gK₁_lt j)).2 (wP_mem_grp hmem)

theorem kappaN_mul : ∀ a ∈ sA₁ e, ∀ b ∈ sA₁ e, kappaN e (a * b) = kappaN e a + kappaN e b := by
  intro a ha b hb
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
  obtain ⟨h, hh, rfl⟩ := mem_toG.1 hb
  rw [← map_mul, kappaN_iotaG, kappaN_iotaG, kappaN_iotaG]
  show toVec 8 (kNP ((g : Equiv.Perm (Fin 693)) * h)) = _
  rw [kNP_mul _ hh _ hg, toVec_xor]

theorem kappaN_eq_zero_iff : ∀ a ∈ sA₁ e, kappaN e a = 0 ↔ a ∈ zpowers (sec3DData e t).z := by
  intro a ha
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
  rw [kappaN_iotaG, show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm,
    iotaG_mem_toG, ← coordN_spec.2.2.1 _ hg]
  constructor
  · exact eq_zero_of_toVec (kNP_lt g)
  · intro h
    rw [h]
    funext j
    simp [toVec, bz]

theorem kappaN_surj : ∀ v, ∃ a ∈ sA₁ e, kappaN e a = v := by
  intro v
  obtain ⟨m, hm, rfl⟩ := exists_toVec 8 v
  obtain ⟨g, hg, hgm⟩ := coordN_spec.2.2.2.2 m (by simpa using hm)
  refine ⟨iotaG e ⟨g, grp_le_T46 gensOK_chA1 hg⟩, iotaG_mem_toG.2 hg, ?_⟩
  rw [kappaN_iotaG]
  exact congrArg _ hgm

theorem kappaN_conj : ∀ j : Fin 5, ∀ a ∈ sA₁ e,
    kappaN e (gK₁ (e := e) j * a * (gK₁ (e := e) j)⁻¹) = wedgeMatN j *ᵥ kappaN e a := by
  intro j a ha
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
  rw [gK₁, gw_eq _ (gK₁_lt j), ← map_inv, ← map_mul, ← map_mul, kappaN_iotaG, kappaN_iotaG]
  show toVec 8 (kNP (wP chK1.gens[j.val]! * g * (wP chK1.gens[j.val]!)⁻¹)) = _
  rw [coordN_spec.2.2.2.1 _ hg j j.2, toVec_bmulVec]
  rfl

theorem d_hom_wedge_A₁ : ∀ β : G → G → G,
    (∀ a ∈ (sec3DData e t).A₁, ∀ b ∈ (sec3DData e t).A₁, β a b ∈ (sec3DData e t).A₁) →
    (∀ a ∈ (sec3DData e t).A₁, ∀ a' ∈ (sec3DData e t).A₁, ∀ b ∈ (sec3DData e t).A₁,
      (β a b * β a' b)⁻¹ * β (a * a') b ∈ zpowers (sec3DData e t).z) →
    (∀ a ∈ (sec3DData e t).A₁, ∀ b ∈ (sec3DData e t).A₁, ∀ b' ∈ (sec3DData e t).A₁,
      (β a b * β a b')⁻¹ * β a (b * b') ∈ zpowers (sec3DData e t).z) →
    (∀ a ∈ (sec3DData e t).A₁, β a a ∈ zpowers (sec3DData e t).z) →
    (∀ b ∈ (sec3DData e t).A₁, β (sec3DData e t).z b ∈ zpowers (sec3DData e t).z) →
    (∀ k ∈ (sec3DData e t).K₁, ∀ a ∈ (sec3DData e t).A₁, ∀ b ∈ (sec3DData e t).A₁,
      (k * β a b * k⁻¹)⁻¹ * β (k * a * k⁻¹) (k * b * k⁻¹) ∈ zpowers (sec3DData e t).z) →
    ∀ a ∈ (sec3DData e t).A₁, ∀ b ∈ (sec3DData e t).A₁, β a b ∈ zpowers (sec3DData e t).z := by
  refine hom_wedge_A₁_of_coords (d := sec3DData e t) d_z_sq d_z_mem_A₁ (kappaN e) kappaN_mul
    kappaN_eq_zero_iff kappaN_surj (gK₁ (e := e)) gK₁_mem (fun j a ha => ?_) kappaN_conj
  have hn := toG_le_normalizer (e := e) (grp_le_T46 gensOK_chK1) (grp_le_T46 gensOK_chA1)
    chK1_le_normalizer_A1 (gK₁_mem j)
  exact (mem_normalizer_iff.1 hn a).1 ha

theorem d_hom_wedge_A₄ : ∀ β : G → G → G,
    (∀ a ∈ (sec3DData e t).A₄, ∀ b ∈ (sec3DData e t).A₄, β a b ∈ (sec3DData e t).A₄) →
    (∀ a ∈ (sec3DData e t).A₄, ∀ b ∈ (sec3DData e t).A₄, ∀ c ∈ (sec3DData e t).A₄,
      β (a * b) c = β a c * β b c) →
    (∀ a ∈ (sec3DData e t).A₄, ∀ b ∈ (sec3DData e t).A₄, ∀ c ∈ (sec3DData e t).A₄,
      β a (b * c) = β a b * β a c) →
    (∀ a ∈ (sec3DData e t).A₄, β a a = 1) →
    (∀ l ∈ (sec3DData e t).Λ, ∀ a ∈ (sec3DData e t).A₄, ∀ b ∈ (sec3DData e t).A₄,
      β (l * a * l⁻¹) (l * b * l⁻¹) = l * β a b * l⁻¹) →
    ∀ a ∈ (sec3DData e t).A₄, ∀ b ∈ (sec3DData e t).A₄, β a b = 1 := by
  have hmem : ∀ j : Fin 3, chLam.gens[j.val]! ∈ chLam.gens := by decide
  have hlt : ∀ j : Fin 3, ∀ k ∈ chLam.gens[j.val]!, k < 18 := fun j => gensOK_chLam _ (hmem j)
  refine hom_wedge_A₄_of_coords (d := sec3DData e t) (kappaW e) ?_ ?_ ?_
    (fun j => gw e chLam.gens[j.val]!) ?_ ?_ ?_
  · intro a ha b hb
    obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
    obtain ⟨h, hh, rfl⟩ := mem_toG.1 hb
    rw [← map_mul, kappaW_iotaG, kappaW_iotaG, kappaW_iotaG]
    show toVec 4 (kWP ((g : Equiv.Perm (Fin 693)) * h)) = _
    rw [coordW_spec.1 _ hg _ hh, toVec_xor]
  · intro a ha h0
    obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
    rw [kappaW_iotaG] at h0
    have := coordW_spec.2.1 _ hg (eq_zero_of_toVec (kWP_lt g) h0)
    rw [show g = 1 from Subtype.ext this, map_one]
  · intro v
    obtain ⟨m, hm, rfl⟩ := exists_toVec 4 v
    obtain ⟨g, hg, hgm⟩ := coordW_spec.2.2.2 m (by simpa using hm)
    refine ⟨iotaG e ⟨g, grp_le_T46 gensOK_chA4 hg⟩, iotaG_mem_toG.2 hg, ?_⟩
    rw [kappaW_iotaG]
    exact congrArg _ hgm
  · intro j
    exact (gw_mem_toG (hlt j)).2 (wP_mem_grp (hmem j))
  · intro j a ha
    have hn := toG_le_normalizer (e := e) (grp_le_T46 gensOK_chLam) (grp_le_T46 gensOK_chA4)
      xNorm_spec.1 ((gw_mem_toG (hlt j)).2 (wP_mem_grp (hmem j)))
    exact (mem_normalizer_iff.1 hn a).1 ha
  · intro j a ha
    obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
    rw [gw_eq _ (hlt j), ← map_inv, ← map_mul, ← map_mul, kappaW_iotaG, kappaW_iotaG]
    show toVec 4 (kWP (wP chLam.gens[j.val]! * g * (wP chLam.gens[j.val]!)⁻¹)) = _
    rw [coordW_spec.2.2.1 _ hg j j.2, toVec_bmulVec]
    rfl

end GLevel

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

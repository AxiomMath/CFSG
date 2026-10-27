module

public import CFSG.Certificates.Kernel.G2Three.Sec1T3F11
public import CFSG.Certificates.Kernel.G2Three.Sec1T3F13
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.TabRank
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Certificates.Kernel.G2Three.Sec1T3CSound

public section

namespace CFSG.KC.G2Three.Sec1T3

open Subgroup CFSG.KD.G2Three.Sec1T3 CFSG.KC.Loop CFSG.Open
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {elt : ℕ → Γ} {P C V Q : ℕ}

theorem f15bc_hasB_one (i : ℕ) : hasB 1 i = true ↔ i = 0 := by
  rw [hasB_eq, Nat.testBit_one_eq_true_iff_self_eq_zero]

theorem f15bc_card (hR : RealT elt P C V Q) {m : ℕ} {K : Subgroup Γ}
    (hK : RepM elt m (K : Set Γ)) : Nat.card K = pop m := by
  rw [← pop_sound hR.inj hK]
  exact Nat.card_coe_set_eq (K : Set Γ)

theorem f15bc_comm_of_sq {x y : Γ} (hx : x * x = 1) (hy : y * y = 1) (hxy : x * y * (x * y) = 1) :
    x * y = y * x := by
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_left hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv_eq_of_mul_eq_one_left hy, inv_eq_of_mul_eq_one_left hx]

theorem f15bc_card_closure_le {Y : Type} [Group Y] [Finite Y] (hsq : ∀ y : Y, y * y = 1) :
    ∀ s : Finset Y, Nat.card (closure (s : Set Y)) ≤ 2 ^ s.card := by
  classical
  have hcomm : ∀ x y : Y, x * y = y * x := fun x y => f15bc_comm_of_sq (hsq x) (hsq y) (hsq _)
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ]
    set H := closure (s : Set Y)
    let K : Subgroup Y :=
      { carrier := (H : Set Y) ∪ (fun y => a * y) '' (H : Set Y)
        mul_mem' := by
          rintro x y (hx | ⟨x, hx, rfl⟩) (hy | ⟨y, hy, rfl⟩)
          · exact Or.inl (H.mul_mem hx hy)
          · refine Or.inr ⟨x * y, H.mul_mem hx hy, ?_⟩
            simp only
            rw [← mul_assoc, ← mul_assoc, hcomm a x]
          · refine Or.inr ⟨x * y, H.mul_mem hx hy, ?_⟩
            simp only [mul_assoc]
          · refine Or.inl ?_
            have e : a * x * (a * y) = x * y := by
              rw [hcomm a x, mul_assoc, ← mul_assoc a a, hsq a, one_mul]
            rw [e]
            exact H.mul_mem hx hy
        one_mem' := Or.inl H.one_mem
        inv_mem' := fun {x} hx => by
          rw [inv_eq_of_mul_eq_one_left (hsq x)]
          exact hx }
    have hle : closure ((insert a s : Finset Y) : Set Y) ≤ K := by
      rw [closure_le, Finset.coe_insert]
      rintro y (rfl | hy)
      · exact Or.inr ⟨1, H.one_mem, mul_one _⟩
      · exact Or.inl (subset_closure hy)
    have h1 : Nat.card (closure ((insert a s : Finset Y) : Set Y)) ≤ Nat.card K :=
      Subgroup.card_le_of_le hle
    have h2 : Nat.card K = ((H : Set Y) ∪ (fun y => a * y) '' (H : Set Y)).ncard :=
      Nat.card_coe_set_eq _
    have h3 := Set.ncard_union_le (H : Set Y) ((fun y => a * y) '' (H : Set Y))
    have h4 := Set.ncard_image_le (f := fun y => a * y) (Set.toFinite (H : Set Y))
    have h5 : (H : Set Y).ncard = Nat.card H := (Nat.card_coe_set_eq _).symm
    omega

theorem f15bc_pRank_eq (V : Subgroup Γ) : pRank 2 ↥V = Open.pRank 2 V := by
  have hset : {k : ℕ | ∃ A : Subgroup ↥V, CFSG.IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ k} =
      {k : ℕ | ∃ E : Subgroup Γ, E ≤ V ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k} := by
    ext k
    constructor
    · rintro ⟨A, hA, hAcard⟩
      exact ⟨A.map V.subtype, Subgroup.map_subtype_le A,
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2)).mpr
          (CFSG.IsElementaryAbelian.subgroup_map hA V.subtype),
        by rw [Subgroup.card_map_of_injective (Subtype.coe_injective), hAcard]⟩
    · rintro ⟨E, hEV, hE, hEcard⟩
      have hc : Nat.card (E.subgroupOf V) = Nat.card E :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEV).toEquiv
      exact ⟨E.subgroupOf V,
        (CFSG.Open.isElemAbelian_iff_isElementaryAbelian (p := 2)).mp (hE.subgroupOf V),
        by rw [hc, hEcard]⟩
  unfold pRank Open.pRank
  rw [hset]

section Tables

variable (hR : RealT elt P C V Q)
include hR

theorem f15bc_elt_eq_one {i : ℕ} (hi : i < 128) : elt i = 1 ↔ i = 0 := by
  constructor
  · intro h
    rw [← hR.one] at h
    exact hR.inj i hi 0 (by norm_num) h
  · rintro rfl
    exact hR.one

theorem f15bc_imgR_one {m : ℕ} {E : Subgroup Γ} (hE : RepM elt m (E : Set Γ)) :
    imgR Q m = 1 ↔ ∀ x ∈ E, x * x = 1 := by
  constructor
  · intro h x hx
    obtain ⟨i, hi, rfl⟩ := hE.2 x hx
    have hb : hasB (imgR Q m) (atR Q i) = true := (imgR_bit _ _ _).2 ⟨i, hi, (hE.1 i hi).2 hx, rfl⟩
    rw [h, f15bc_hasB_one] at hb
    rw [← hR.sq hi, hb, hR.one]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.2
    rw [← hasB_eq, imgR_bit, Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro ⟨i, hi, hb, rfl⟩
      have hx := h _ ((hE.1 i hi).1 hb)
      rw [← hR.sq hi] at hx
      exact (f15bc_elt_eq_one hR (atR_lt _ _)).1 hx
    · rintro rfl
      have h0 : elt 0 ∈ E := by rw [hR.one]; exact E.one_mem
      refine ⟨0, by norm_num, (hE.1 0 (by norm_num)).2 h0, ?_⟩
      have hs := hR.sq (i := 0) (by norm_num)
      rw [hR.one, one_mul] at hs
      exact (f15bc_elt_eq_one hR (atR_lt _ _)).1 hs

theorem f15bc_commE_one {x y : ℕ} (hx : x < 128) (hy : y < 128) :
    hasB 1 (commE P C V x y) = true ↔ elt x * elt y = elt y * elt x := by
  rw [f15bc_hasB_one, ← f15bc_elt_eq_one hR (i := commE P C V x y) (atR_lt _ _), commE_elt hR hx hy,
    commutatorElement_eq_one_iff_mul_comm]

end Tables

theorem f15bc_gens_mem {L RG N : ℕ} (hN : N ≤ 448) (hrg : rgK L RG N = true) {k : ℕ}
    (hk : k < N) : Nat.land (rgAt RG k) 7 ≤ 4 ∧
      ∀ t < Nat.land (rgAt RG k) 7, hasB (entL L k) (genAt (rgAt RG k) t) = true := by
  obtain ⟨h4, hg⟩ := rgK_spec hrg hN k hk
  exact ⟨h4, gensIn_spec hg⟩

abbrev f15bc_Lat (elt : ℕ → Γ) (X : Subgroup Γ) (L N : ℕ) : Prop :=
  (∀ k < N, ∃ K : Subgroup Γ, K ≤ X ∧ RepM elt (latM L k) (K : Set Γ)) ∧
    ∀ K ≤ X, ∃ k < N, RepM elt (latM L k) (K : Set Γ)

theorem f15bc_gen (hR : RealT elt P C V Q) {X : Subgroup Γ} {L RG OR N : ℕ}
    (hlat : f15bc_Lat elt X L N) (hN : N ≤ 448) (ho : ordK L OR 0 N = true) (hp : IsPGroup 2 X)
    (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    {k : ℕ} (hk : k < N) {K : Subgroup Γ} (_hKX : K ≤ X) (hK : RepM elt (entL L k) (K : Set Γ)) :
    closure {x | ∃ t < Nat.land (rgAt RG k) 7, elt (genAt (rgAt RG k) t) = x} = K := by
  have hall' : ∀ k < N, ∀ h < N, 2 * ordAt OR h = ordAt OR k →
      subM (entL L h) (entL L k) = true → outB (entL L h) (rgAt RG k) = true := by
    intro k hk h hh
    obtain ⟨lo, w, hlo, hkw, hw, hra⟩ := hall k hk
    have e : lo + (k - lo) = k := by omega
    have := rgAllK_spec hra hN hw (k - lo) (by omega) h hh
    rw [e] at this
    exact this
  exact (rg_closure hR.inj hlat hp hN hrg (ordK_spec ho hN) hall' hk hK).2.symm

section Five

variable {fr : Frame Γ}

theorem f15bc_Fs_le : closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z, fr.σ} ≤ fr.Sσ := by
  have hm : ∀ x ∈ ({fr.a₁, fr.b₁, fr.a₂, fr.b₂, fr.h₀, fr.σ} : Set Γ), x ∈ fr.Sσ :=
    fun x hx => subset_closure hx
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact fr.Sσ.mul_mem (hm _ (by simp)) (hm _ (by simp))
  · exact fr.Sσ.mul_mem (hm _ (by simp)) (hm _ (by simp))
  · exact pow_mem (hm _ (by simp)) 2
  · exact hm _ (by simp)

theorem f15bc_Fs_mset (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s) {R : ℕ}
    (hc : closOK C [mulE P 1 3, mulE P 2 4, atR Q 2, 6] R = true) :
    mset elt (closK C [mulE P 1 3, mulE P 2 4, atR Q 2, 6] R) =
      (closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z, fr.σ} : Set Γ) := by
  obtain ⟨-, -, -, -, -, e6⟩ := f13_gens hg
  obtain ⟨hz, h13, h24, -, -, -, -⟩ := f13_prods hR hg
  have hl : ∀ g ∈ [mulE P 1 3, mulE P 2 4, atR Q 2, 6], g < 128 := by
    intro g hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl | rfl
    exacts [f13_mulE_lt _ _ _, f13_mulE_lt _ _ _, atR_lt _ _, by norm_num]
  rw [closK_closure hR hl hc, f13_setOf_eq_map]
  simp only [List.map_cons, List.map_nil, hz, h13, h24, e6]
  congr 2
  ext x
  simp

theorem f15bc_five_six (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    {L RG OR N kF kFs R : ℕ} (hlat : f15bc_Lat elt fr.Sσ L N) (hN : N ≤ 448)
    (ho : ordK L OR 0 N = true) (hp : IsPGroup 2 fr.Sσ) (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    (hb : f15bK P C V Q L RG N 1 2 3 4 5 6 kF kFs R = true)
    (hc : f15cK P C V Q L RG N 1 2 3 4 5 6 R = true) :
    (∀ U : Subgroup Γ, U ≤ fr.Sσ → IsMulCommutative U → Nat.card U ≤ 16) ∧
    (pRank 2 fr.Sσ = 4 ∧ GH74.sectionalTwoRank ↥fr.Sσ = 4) := by
  classical
  have hinj := hR.inj
  unfold f15cK at hc
  simp only [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hc
  obtain ⟨c6, -, -, hab, hpr, -⟩ := hc
  have hSs := f11_Ss hR hg c6
  unfold f15bK at hb
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at hb
  obtain ⟨-, -, -, -, -, -, cFs, -, -, -, -, -, hFsab, hFs16, -⟩ := hb
  have h5 : ∀ U : Subgroup Γ, U ≤ fr.Sσ → IsMulCommutative U → Nat.card U ≤ 16 := by
    intro U hU hUc
    obtain ⟨k, hk, hrep⟩ := hlat.2 U hU
    have hrep' : RepM elt (entL L k) (U : Set Γ) := hrep
    have h1 := allBelow_spec hab (by omega) k hk
    have habR : abR P C V (rgAt RG k) 1 = true := by
      have hmem := (f15bc_gens_mem hN hrg hk).2
      unfold abR
      refine (recAnd_iff _ _).2 fun t ht => (recAnd_iff _ _).2 fun u hu => ?_
      rw [f15bc_commE_one hR (x := genAt (rgAt RG k) t) (y := genAt (rgAt RG k) u)
        (fld127_lt _ _) (fld127_lt _ _)]
      have ht' := (hrep'.1 _ (fld127_lt _ _)).1 (hmem t ht)
      have hu' := (hrep'.1 _ (fld127_lt _ _)).1 (hmem u hu)
      exact congrArg Subtype.val (hUc.is_comm.comm ⟨_, ht'⟩ ⟨_, hu'⟩)
    rw [habR] at h1
    have h2 : Nat.ble (pop (entL L k)) 16 = true := h1
    rw [f15bc_card hR hrep']
    exact Nat.le_of_ble_eq_true h2
  refine ⟨h5, ?_, ?_⟩
  · unfold pRankK at hpr
    rw [strictN_eq] at hpr
    set F : ℕ → ℕ := fun k => strictN (entL L k) fun K =>
      nIf(bAnd(subM K (closK C [1, 2, 3, 4, 5, 6] R), Nat.beq (imgR Q K) 1), pop K, 0) with hF
    have hval : ∀ k < N, ∀ E : Subgroup Γ, E ≤ fr.Sσ → RepM elt (entL L k) (E : Set Γ) →
        (∀ x ∈ E, x * x = 1) → F k = Nat.card E := by
      intro k hk E hE hrep hsq
      have hs : subM (entL L k) (closK C [1, 2, 3, 4, 5, 6] R) = true := by
        refine (subM_iff_subset hinj (entL_lt L k)).2 ?_
        rw [← RepM.eq_mset hrep, hSs]
        exact hE
      have hi : Nat.beq (imgR Q (entL L k)) 1 = true := by
        rw [Nat.beq_eq]
        exact (f15bc_imgR_one hR hrep).2 hsq
      rw [hF]
      dsimp only
      rw [strictN_eq, hs, hi, f15bc_card hR hrep]
    rw [f15bc_pRank_eq]
    unfold Open.pRank
    have hub : ∀ j ∈ {j | ∃ E : Subgroup Γ, E ≤ fr.Sσ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ j},
        j ≤ 4 := by
      rintro j ⟨E, hE, hEa, hEc⟩
      obtain ⟨k, hk, hrep⟩ := hlat.2 E hE
      have hle := (maxBelow_spec (hi := 7) F (by omega)).1 k hk
      rw [hpr, hval k hk E hE hrep (isElemAbelian_iff_sq.1 hEa), hEc] at hle
      by_contra hj
      have : 2 ^ 5 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h4 : 4 ∈ {j | ∃ E : Subgroup Γ, E ≤ fr.Sσ ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ j} := by
      rcases (maxBelow_spec (hi := 7) F (by omega)).2 with h0 | ⟨k, hk, hk16⟩
      · rw [hpr] at h0
        exact absurd h0 (by norm_num)
      · replace hk16 := hk16.symm
        rw [hpr] at hk16
        obtain ⟨E, hE, hrep⟩ := hlat.1 k hk
        have hrep' : RepM elt (entL L k) (E : Set Γ) := hrep
        rw [hF] at hk16
        dsimp only at hk16
        rw [strictN_eq] at hk16
        cases hcond : bAnd(subM (entL L k) (closK C [1, 2, 3, 4, 5, 6] R),
            Nat.beq (imgR Q (entL L k)) 1)
        · rw [hcond] at hk16
          change 16 = 0 at hk16
          exact absurd hk16 (by norm_num)
        · rw [hcond] at hk16
          rw [bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at hcond
          refine ⟨E, hE, isElemAbelian_iff_sq.2 ((f15bc_imgR_one hR hrep').1 hcond.2), ?_⟩
          rw [f15bc_card hR hrep']
          exact hk16.symm
    exact le_antisymm (csSup_le ⟨4, h4⟩ hub) (le_csSup ⟨4, hub⟩ h4)
  · set Fs := closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z, fr.σ} with hFsdef
    have hFsm := f15bc_Fs_mset hR hg cFs
    have hsqFs : ∀ x ∈ Fs, x * x = 1 := by
      intro x hx
      rw [← SetLike.mem_coe, ← hFsm] at hx
      exact (elemAbK_spec hR hFsab x hx).1
    have hcFs : Nat.card Fs = 16 := by rw [f11_card hR hFsm, hFs16]
    have hup : ∀ P' : Subgroup Γ, P' ≤ fr.Sσ →
        ∃ s : Finset Γ, s.card ≤ 4 ∧ closure (s : Set Γ) = P' := by
      intro P' hP'
      obtain ⟨k, hk, hrep⟩ := hlat.2 P' hP'
      refine ⟨(Finset.range (Nat.land (rgAt RG k) 7)).image
        (fun t => elt (genAt (rgAt RG k) t)), ?_, ?_⟩
      · refine le_trans Finset.card_image_le ?_
        rw [Finset.card_range]
        exact (f15bc_gens_mem hN hrg hk).1
      · rw [← f15bc_gen hR hlat hN ho hp hrg hall hk hP' hrep]
        congr 1
        ext x
        simp
    refine Tab.sectionalTwoRank_eq_of_data hp f15bc_Fs_le (by norm_num) hup
      (MonoidHom.id ↥Fs) Function.surjective_id ?_
    intro s hs htop
    have hle := f15bc_card_closure_le (Y := ↥Fs)
      (fun y => Subtype.ext (hsqFs y.1 y.2)) s
    rw [htop, Subgroup.card_top, hcFs] at hle
    have : 2 ^ s.card ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end Five

theorem f15bc_testBit_sub_pow {G g : ℕ} (h : G.testBit g = true) (j : ℕ) :
    (G - 2 ^ g).testBit j = (G.testBit j && !decide (j = g)) := by
  have hq : (G / 2 ^ g) % 2 = 1 := by
    have := Nat.testBit_div_two_pow (n := g) G 0
    rw [Nat.zero_add, h, Nat.testBit_zero] at this
    simpa using this
  have hr : G % 2 ^ g < 2 ^ g := Nat.mod_lt _ (by positivity)
  have e1 : G = 2 ^ g * (G / 2 ^ g) + G % 2 ^ g := (Nat.div_add_mod G _).symm
  have hx : 1 ≤ G / 2 ^ g := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hq; simp at hq
  have e2 : G - 2 ^ g = 2 ^ g * (G / 2 ^ g - 1) + G % 2 ^ g := by
    rw [Nat.mul_sub_one]
    have : 2 ^ g ≤ 2 ^ g * (G / 2 ^ g) := Nat.le_mul_of_pos_right _ hx
    omega
  rw [e2, Nat.testBit_two_pow_mul_add _ hr]
  conv_rhs => rw [e1, Nat.testBit_two_pow_mul_add _ hr]
  by_cases hj : j < g
  · simp [hj, show j ≠ g by omega]
  · simp only [hj, ite_false]
    by_cases hjg : j = g
    · subst hjg
      simp only [Nat.sub_self, Nat.testBit_zero, decide_true, Bool.not_true, Bool.and_false]
      have : (G / 2 ^ j - 1) % 2 = 0 := by omega
      simp [this]
    · simp only [hjg, decide_false, Bool.not_false, Bool.and_true]
      obtain ⟨k, hk⟩ : ∃ k, j - g = k + 1 := ⟨j - g - 1, by omega⟩
      rw [hk, ← Nat.testBit_div_two, ← Nat.testBit_div_two]
      congr 1
      omega

theorem f15bc_repBot (hR : RealT elt P C V Q) : RepM elt 1 ((⊥ : Subgroup Γ) : Set Γ) := by
  have h := repM_mset hR.inj (elt := elt) 1
  rwa [mset_one hR.one, ← Subgroup.coe_bot] at h

theorem f15bc_rep (hR : RealT elt P C V Q) {m : ℕ} {X : Set Γ} (h : mset elt m = X) :
    RepM elt m X := by
  rw [← h]
  exact repM_mset hR.inj m

theorem f15bc_isMaxSq_iff {X Y : Subgroup Γ} : IsMaxSq ⊥ X Y ↔ Y ∈ maxElemAbelian X := by
  unfold IsMaxSq maxElemAbelian
  simp only [Set.mem_setOf_eq, mem_bot, bot_le, true_and, isElemAbelian_iff_sq]

theorem f15bc_maxEA (hR : RealT elt P C V Q) {G₀ X : Subgroup Γ} {L N Xm : ℕ}
    (hL : LatOK elt L N G₀) (hN : N ≤ 448) (hXG : X ≤ G₀) (hX : RepM elt Xm (X : Set Γ)) {k : ℕ}
    (hk : k < N) {Y : Subgroup Γ} (hY : RepM elt (entL L k) (Y : Set Γ)) :
    hasB (maxIdx L (secC Q L N Xm 1) N) k = true ↔ Y ∈ maxElemAbelian X := by
  rw [maxIdx_secC hR hL hN hXG hX (f15bc_repBot hR) (by norm_num) k]
  constructor
  · rintro ⟨-, K, hK, hmax⟩
    have e : K = Y := SetLike.coe_injective (hK.eq hY)
    subst e
    exact f15bc_isMaxSq_iff.1 hmax
  · intro h
    exact ⟨hk, Y, hY, f15bc_isMaxSq_iff.2 h⟩

theorem f15bc_comm_iff (A : Subgroup Γ) :
    IsMulCommutative A ↔ ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ (⊥ : Subgroup Γ) := by
  simp only [mem_bot, commutatorElement_eq_one_iff_mul_comm]
  constructor
  · intro h a ha b hb
    exact congrArg Subtype.val (h.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · intro h
    exact ⟨⟨fun a b => Subtype.ext (h a.1 a.2 b.1 b.2)⟩⟩

theorem f15bc_card_omega {X A : Subgroup Γ} (hp : IsPGroup 2 X) (hAX : A ≤ X)
    (hc : IsMulCommutative A) :
    {x | x ∈ A ∧ x * x ∈ (⊥ : Subgroup Γ)}.ncard = 2 ^ Open.pRank 2 A := by
  rw [two_pow_pRank_of_comm hc (hp.to_le hAX)]
  simp only [mem_bot]

theorem f15bc_thompson (hR : RealT elt P C V Q) {X : Subgroup Γ} {L RG N Xm R T : ℕ}
    (hL : LatOK elt L N X) (hN : N ≤ 448) (hp : IsPGroup 2 X)
    (hgen : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k))
    (hX : RepM elt Xm (X : Set Γ)) (h : joinK C (jrU P C V Q L RG N Xm 1) R T = true) :
    (thompsonRank X : Set Γ) = mset elt T := by
  have hn : ∀ x ∈ X, ∀ n ∈ (⊥ : Subgroup Γ), x * n * x⁻¹ ∈ (⊥ : Subgroup Γ) := by
    intro x _ n hn
    rw [mem_bot] at hn ⊢
    rw [hn, mul_one, mul_inv_cancel]
  rw [joinK_sound hR h, jrU_sound hR hL hN hgen le_rfl hX (f15bc_repBot hR) (by norm_num) hn]
  refine congrArg (fun H : Subgroup Γ => (H : Set Γ)) ?_
  apply le_antisymm
  · unfold thompsonRank
    refine iSup_le fun U => iSup_le fun hU => iSup_le fun hc => iSup_le fun hmax => ?_
    intro x hx
    refine subset_closure (Set.mem_iUnion₂.2 ⟨U, ⟨⟨bot_le, hU, (f15bc_comm_iff U).1 hc⟩, ?_⟩, hx⟩)
    rintro B ⟨-, hBX, hBc⟩
    rw [f15bc_card_omega hp hBX ((f15bc_comm_iff B).2 hBc), f15bc_card_omega hp hU hc]
    have h1 := hmax B hBX ((f15bc_comm_iff B).2 hBc)
    rw [f15bc_pRank_eq, f15bc_pRank_eq] at h1
    exact Nat.pow_le_pow_right (by norm_num) h1
  · rw [closure_le]
    intro x hx
    obtain ⟨A, ⟨⟨-, hAX, hAc⟩, hAmax⟩, hxA⟩ := Set.mem_iUnion₂.1 hx
    have hc := (f15bc_comm_iff A).2 hAc
    have hmax : ∀ W : Subgroup Γ, W ≤ X → IsMulCommutative W →
        pRank 2 ↥W ≤ pRank 2 ↥A := by
      intro W hWX hWc
      rw [f15bc_pRank_eq, f15bc_pRank_eq]
      have h1 := hAmax W ⟨bot_le, hWX, (f15bc_comm_iff W).1 hWc⟩
      rw [f15bc_card_omega hp hWX hWc, f15bc_card_omega hp hAX hc] at h1
      exact (Nat.pow_le_pow_iff_right (by decide)).1 h1
    have hle : A ≤ thompsonRank X := by
      unfold thompsonRank
      refine le_iSup_of_le A ?_
      refine le_iSup_of_le hAX ?_
      refine le_iSup_of_le hc ?_
      exact le_iSup_of_le hmax le_rfl
    exact hle hxA

section Four

variable {fr : Frame Γ}

theorem f15bc_F_mset (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s) {R : ℕ}
    (hc : closOK C [mulE P 1 3, mulE P 2 4, atR Q 2] R = true) :
    mset elt (closK C [mulE P 1 3, mulE P 2 4, atR Q 2] R) = (fr.F : Set Γ) := by
  obtain ⟨hz, h13, h24, -, -, -, -⟩ := f13_prods hR hg
  have hl : ∀ g ∈ [mulE P 1 3, mulE P 2 4, atR Q 2], g < 128 := by
    intro g hg'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg'
    rcases hg' with rfl | rfl | rfl
    exacts [f13_mulE_lt _ _ _, f13_mulE_lt _ _ _, atR_lt _ _]
  rw [closK_closure hR hl hc, f13_setOf_eq_map]
  simp only [List.map_cons, List.map_nil, hz, h13, h24]
  rw [f13_setOf_three]
  rfl

theorem f15bc_Fs_eq : fr.F ⊔ closure {fr.σ} = closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z, fr.σ} := by
  unfold SFrame.F
  rw [← Subgroup.closure_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc]

theorem f15bc_four (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    {L RG OR N kF kFs R : ℕ} (hlat : f15bc_Lat elt fr.Sσ L N) (hN : N ≤ 448)
    (ho : ordK L OR 0 N = true) (hp : IsPGroup 2 fr.Sσ) (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    (hb : f15bK P C V Q L RG N 1 2 3 4 5 6 kF kFs R = true) :
    thompsonRank fr.Sσ = fr.F ⊔ closure {fr.σ} ∧ IsE 4 ↥(fr.F ⊔ closure {fr.σ}) ∧
      maxElemAbelian fr.Sσ = insert (fr.F ⊔ closure {fr.σ}) (maxElemAbelian fr.S) \ {fr.F} := by
  classical
  have hinj := hR.inj
  have hL : LatOK elt L N fr.Sσ := hlat
  have hgen : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k) := fun k hk K hK =>
    (f15bc_gen hR hlat hN ho hp hrg hall hk (hL.le hk hK) hK).symm
  unfold f15bK at hb
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at hb
  obtain ⟨c5, c6, -, -, cF, -, cFs, -, -, -, -, hjFs, hel, h16, hkF, hkFs, hne, hMxF, hMx⟩ := hb
  have hS := f11_S hR (fun s hs => hg s (by omega)) c5
  have hSs := f11_Ss hR hg c6
  have hFm := f15bc_F_mset hR hg cF
  have hFsm := f15bc_Fs_mset hR hg cFs
  rw [f15bc_Fs_eq]
  set Fs := closure {fr.a₁ * fr.a₂, fr.b₁ * fr.b₂, fr.z, fr.σ} with hFsdef
  have hSle : fr.S ≤ fr.Sσ := by
    unfold SFrame.S Frame.Sσ
    refine closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hrepS := f15bc_rep hR hS
  have hrepSs := f15bc_rep hR hSs
  have hrepF : RepM elt (entL L kF) (fr.F : Set Γ) := by rw [hkF]; exact f15bc_rep hR hFm
  have hrepFs : RepM elt (entL L kFs) (Fs : Set Γ) := by rw [hkFs]; exact f15bc_rep hR hFsm
  have e1 : Nat.shiftLeft 1 kF = 2 ^ kF := Nat.one_shiftLeft kF
  have e2 : Nat.shiftLeft 1 kFs = 2 ^ kFs := Nat.one_shiftLeft kFs
  rw [e1, e2] at hMx
  have hne' : kF ≠ kFs := by
    intro h
    have hself : Nat.beq kFs kFs = true := by rw [Nat.beq_eq]
    rw [h, not'_eq, Bool.not_eq_true', hself] at hne
    exact Bool.noConfusion hne
  have hbit : ∀ k, hasB (maxIdx L (secC Q L N (closK C [1, 2, 3, 4, 5, 6] R) 1) N) k = true ↔
      (hasB (maxIdx L (secC Q L N (closK C [1, 2, 3, 4, 5] R) 1) N) k = true ∧ k ≠ kF) ∨
        k = kFs := by
    intro k
    rw [hMx, hasB_eq, hasB_eq]
    rw [hasB_eq] at hMxF
    change ((maxIdx L (secC Q L N (closK C [1, 2, 3, 4, 5] R) 1) N - 2 ^ kF) ||| 2 ^ kFs).testBit
      k = true ↔ _
    rw [Nat.testBit_or, f15bc_testBit_sub_pow hMxF, Nat.testBit_two_pow]
    simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq, eq_comm (a := kFs)]
  have hkFN : kF < N := by
    by_contra h
    have := (maxIdx_bit hN kF).1 hMxF
    omega
  have hkFsN : kFs < N := by
    have h := (hbit kFs).2 (Or.inr rfl)
    have := (maxIdx_bit hN kFs).1 h
    omega
  have hEA : ∀ {X : Subgroup Γ} {Xm : ℕ}, X ≤ fr.Sσ → RepM elt Xm (X : Set Γ) → ∀ {k : ℕ},
      k < N → ∀ {Y : Subgroup Γ}, RepM elt (entL L k) (Y : Set Γ) →
        (hasB (maxIdx L (secC Q L N Xm 1) N) k = true ↔ Y ∈ maxElemAbelian X) :=
    fun hXG hX _ hk _ hY => f15bc_maxEA hR hL hN hXG hX hk hY
  have hFsMax : Fs ∈ maxElemAbelian fr.Sσ := (hEA le_rfl hrepSs hkFsN hrepFs).1 ((hbit kFs).2 (Or.inr rfl))
  have hFnot : fr.F ∉ maxElemAbelian fr.Sσ := fun h => by
    have := (hbit kF).1 ((hEA le_rfl hrepSs hkFN hrepF).2 h)
    rcases this with ⟨-, h'⟩ | h'
    · exact h' rfl
    · exact hne' h'
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · exact SetLike.coe_injective ((f15bc_thompson hR hL hN hp hgen hrepSs hjFs).trans hFsm)
  · rw [isElemAbelian_iff_sq]
    intro x _
    apply Subtype.ext
    have hx : (x : Γ) ∈ mset elt (closK C [mulE P 1 3, mulE P 2 4, atR Q 2, 6] R) := by
      rw [hFsm]
      exact x.2
    exact (elemAbK_spec hR hel _ hx).1
  · rw [f11_card hR hFsm, h16]
    norm_num
  · ext Y
    simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hY
      have hYne : Y ≠ fr.F := fun h => hFnot (h ▸ hY)
      obtain ⟨k, hk, hrep⟩ := hL.2 Y hY.1
      have hb := (hEA le_rfl hrepSs hk hrep).2 hY
      rcases (hbit k).1 hb with ⟨hbS, -⟩ | rfl
      · exact ⟨Or.inr ((hEA hSle hrepS hk hrep).1 hbS), hYne⟩
      · exact ⟨Or.inl (SetLike.coe_injective (hrep.eq hrepFs)), hYne⟩
    · rintro ⟨rfl | hY, hYne⟩
      · exact hFsMax
      · obtain ⟨k, hk, hrep⟩ := hL.2 Y (le_trans hY.1 hSle)
        have hbS := (hEA hSle hrepS hk hrep).2 hY
        have hkne : k ≠ kF := by
          rintro rfl
          exact hYne (SetLike.coe_injective (hrep.eq hrepF))
        exact (hEA le_rfl hrepSs hk hrep).1 ((hbit k).2 (Or.inl ⟨hbS, hkne⟩))

end Four

theorem f15bc_closK_lt (C : ℕ) (gs : List ℕ) : ∀ R, closK C gs R < 2 ^ 128
  | 0 => by
    change (1 : ℕ) < 2 ^ 128
    norm_num
  | R + 1 => by
    have ih := f15bc_closK_lt C gs R
    rw [closK_succ]
    apply lt128_of_testBit
    intro i hi
    rw [stepK_bit] at hi
    by_contra hge
    rcases hi with h | ⟨g, -, h⟩
    · rw [testBit_lt128 ih (by omega)] at h
      exact Bool.noConfusion h
    · rw [testBit_lt128 (imgR_lt _ _) (by omega)] at h
      exact Bool.noConfusion h

theorem f15bc_conjM_mset (hR : RealT elt P C V Q) {s : ℕ} (hs : s < 128) (X : ℕ) :
    mset elt (conjM P C V s X) = (fun x => elt s * x * (elt s)⁻¹) '' mset elt X := by
  have e : conjM P C V s X = Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR (rowT P s) (rowT C (atR V s)) i)), acc))
        128 := by
    simp only [conjM, strictN_eq]
  rw [e, mset_recMask (hasB X) (fun i => conjR (rowT P s) (rowT C (atR V s)) i)
    (fun i _ => atR_lt _ _)]
  ext x
  constructor
  · rintro ⟨i, hi, hb, rfl⟩
    exact ⟨elt i, ⟨i, hi, hb, rfl⟩, (conjR_elt hR hs hi).symm⟩
  · rintro ⟨_, ⟨i, hi, hb, rfl⟩, rfl⟩
    exact ⟨i, hi, hb, conjR_elt hR hs hi⟩

theorem f15bc_normM (hR : RealT elt P C V Q) {Xm Nm : ℕ} (h : normM P C V Xm Nm = true) :
    ∀ x ∈ mset elt Xm, ∀ n ∈ mset elt Nm, x * n * x⁻¹ ∈ mset elt Nm := by
  rintro _ ⟨i, hi, hb, rfl⟩ n hn
  unfold normM at h
  rw [strictB_eq, strictB_eq] at h
  have h1 := allBelow_spec h (by norm_num) i hi
  rw [hb] at h1
  have h2 : conjM P C V i Nm = Nm := Nat.eq_of_beq_eq_true h1
  rw [← h2, f15bc_conjM_mset hR hi]
  exact ⟨n, hn, rfl⟩

section Quo

variable {X N : Subgroup Γ} [(N.subgroupOf X).Normal]

theorem f15bc_quo_comm {K : Subgroup Γ} (hNK : N ≤ K) (hKX : K ≤ X) :
    IsMulCommutative (quo X N K) ↔ ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N := by
  rw [f15bc_comm_iff]
  constructor
  · intro h a ha b hb
    have := h _ ((mem_quo hNK ⟨a, hKX ha⟩).2 ha) _ ((mem_quo hNK ⟨b, hKX hb⟩).2 hb)
    have e := map_commutatorElement (QuotientGroup.mk' (N.subgroupOf X)) (⟨a, hKX ha⟩ : X)
      ⟨b, hKX hb⟩
    simp only [QuotientGroup.mk'_apply] at e
    rw [mem_bot, ← e, QuotientGroup.eq_one_iff, mem_subgroupOf] at this
    simpa [commutatorElement_def] using this
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      mem_subgroupOf]
    have := h _ (mem_subgroupOf.1 hx) _ (mem_subgroupOf.1 hy)
    simpa [commutatorElement_def] using this

theorem f15bc_quo_card {H : Subgroup Γ} (hNH : N ≤ H) (hHX : H ≤ X) :
    Nat.card (quo X N H) * Nat.card N = Nat.card H := by
  have hcomap : (quo X N H).comap (QuotientGroup.mk' (N.subgroupOf X)) = H.subgroupOf X := by
    ext x
    rw [mem_comap, QuotientGroup.mk'_apply, mem_quo hNH, mem_subgroupOf]
  have h1 := Subgroup.index_mul_card ((quo X N H).comap (QuotientGroup.mk' (N.subgroupOf X)))
  rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hcomap] at h1
  have h2 := Subgroup.index_mul_card (quo X N H)
  have h3 := Subgroup.index_mul_card (N.subgroupOf X)
  rw [Subgroup.index_eq_card] at h3
  have eH : Nat.card (H.subgroupOf X) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHX).toEquiv
  have eN : Nat.card (N.subgroupOf X) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans hNH hHX)).toEquiv
  rw [eH] at h1
  rw [eN] at h3
  have hi : 0 < (quo X N H).index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have key : (quo X N H).index * (Nat.card (quo X N H) * Nat.card N) =
      (quo X N H).index * Nat.card H := by
    rw [h1, ← mul_assoc, h2, h3]
  exact Nat.eq_of_mul_eq_mul_left hi key

theorem f15bc_quo_omega (hp : IsPGroup 2 X) {K : Subgroup Γ} (hNK : N ≤ K) (hKX : K ≤ X)
    (hc : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N) :
    {x | x ∈ K ∧ x * x ∈ N}.ncard = 2 ^ Open.pRank 2 (quo X N K) * Nat.card N := by
  let Ω : Subgroup Γ :=
    { carrier := {x | x ∈ K ∧ x * x ∈ N}
      mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, by
        have hab := hc _ (K.inv_mem ha.1) _ hb.1
        have e : a * b * (a * b) = a * a * ⁅a⁻¹, b⁆ * (b * b) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem (N.mul_mem ha.2 hab) hb.2⟩
      one_mem' := ⟨K.one_mem, by rw [one_mul]; exact N.one_mem⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, by
        rw [← mul_inv_rev]
        exact N.inv_mem ha.2⟩ }
  have hΩK : Ω ≤ K := fun x hx => hx.1
  have hNΩ : N ≤ Ω := fun n hn => ⟨hNK hn, N.mul_mem hn hn⟩
  have hqc : IsMulCommutative (quo X N K) := (f15bc_quo_comm hNK hKX).2 hc
  have hpY : IsPGroup 2 (X ⧸ N.subgroupOf X) := hp.to_quotient _
  rw [two_pow_pRank_of_comm hqc (hpY.to_subgroup _)]
  have hset : {w | w ∈ quo X N K ∧ w * w = 1} = (quo X N Ω : Set (X ⧸ N.subgroupOf X)) := by
    ext w
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hw⟩
      refine ⟨x, mem_subgroupOf.2 ⟨mem_subgroupOf.1 hx, ?_⟩, rfl⟩
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
        mem_subgroupOf] at hw
      exact hw
    · rintro ⟨x, hx, rfl⟩
      refine ⟨⟨x, mem_subgroupOf.2 (mem_subgroupOf.1 hx).1, rfl⟩, ?_⟩
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
        mem_subgroupOf]
      exact (mem_subgroupOf.1 hx).2
  have e : ((quo X N Ω : Set (X ⧸ N.subgroupOf X))).ncard = Nat.card (quo X N Ω) :=
    (Nat.card_coe_set_eq _).symm
  rw [hset, e, f15bc_quo_card hNΩ (le_trans hΩK hKX)]
  rfl

end Quo

theorem f15bc_jr_quo (hR : RealT elt P C V Q) {X N A : Subgroup Γ} [(N.subgroupOf X).Normal]
    {L RG M Xm Nm R T : ℕ} (hL : LatOK elt L M X) (hM : M ≤ 448) (hp : IsPGroup 2 X)
    (hgen : ∀ k < M, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k))
    (hX : RepM elt Xm (X : Set Γ)) (hN : RepM elt Nm (N : Set Γ)) (hNb : Nm < 2 ^ 128)
    (hNX : N ≤ X) (hn : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hT : mset elt T = (A : Set Γ))
    (hNA : N ≤ A) (hAX : A ≤ X) (h : joinK C (jrU P C V Q L RG M Xm Nm) R T = true) :
    thompsonRank (⊤ : Subgroup (X ⧸ N.subgroupOf X)) = quo X N A := by
  have hA : A = closure (⋃ K ∈ {K : Subgroup Γ | (N ≤ K ∧ K ≤ X ∧ ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N) ∧
      ∀ B ∈ {B : Subgroup Γ | N ≤ B ∧ B ≤ X ∧ ∀ a ∈ B, ∀ b ∈ B, ⁅a, b⁆ ∈ N},
        {x | x ∈ B ∧ x * x ∈ N}.ncard ≤ {x | x ∈ K ∧ x * x ∈ N}.ncard}, (K : Set Γ)) := by
    apply SetLike.coe_injective
    rw [← hT, joinK_sound hR h, jrU_sound hR hL hM hgen le_rfl hX hN hNb hn]
  have hNpos : 0 < Nat.card N := Nat.card_pos
  have hrk : ∀ {B K : Subgroup Γ}, N ≤ B → B ≤ X → (∀ a ∈ B, ∀ b ∈ B, ⁅a, b⁆ ∈ N) →
      N ≤ K → K ≤ X → (∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N) →
      ({x | x ∈ B ∧ x * x ∈ N}.ncard ≤ {x | x ∈ K ∧ x * x ∈ N}.ncard ↔
        pRank 2 ↥(quo X N B) ≤ pRank 2 ↥(quo X N K)) := by
    intro B K hNB hBX hBc hNK hKX hKc
    rw [f15bc_quo_omega hp hNB hBX hBc, f15bc_quo_omega hp hNK hKX hKc, f15bc_pRank_eq,
      f15bc_pRank_eq, Nat.mul_le_mul_right_iff hNpos]
    exact Nat.pow_le_pow_iff_right (by decide)
  apply le_antisymm
  · unfold thompsonRank
    refine iSup_le fun W => iSup_le fun _ => iSup_le fun hWc => iSup_le fun hmax => ?_
    obtain ⟨K, hNK, hKX, rfl⟩ := exists_quo hNX W
    have hKc := (f15bc_quo_comm hNK hKX).1 hWc
    have hKA : K ≤ A := by
      rw [hA]
      intro x hx
      refine subset_closure (Set.mem_iUnion₂.2 ⟨K, ⟨⟨hNK, hKX, hKc⟩, ?_⟩, hx⟩)
      rintro B ⟨hNB, hBX, hBc⟩
      exact (hrk hNB hBX hBc hNK hKX hKc).2
        (hmax _ le_top ((f15bc_quo_comm hNB hBX).2 hBc))
    exact (quo_le_quo_iff hNA hKX).2 hKA
  · have hsub : A ≤ ((thompsonRank (⊤ : Subgroup (X ⧸ N.subgroupOf X))).comap
        (QuotientGroup.mk' (N.subgroupOf X))).map X.subtype := by
      rw [hA, closure_le]
      intro x hx
      obtain ⟨K, ⟨⟨hNK, hKX, hKc⟩, hKmax⟩, hxK⟩ := Set.mem_iUnion₂.1 hx
      have hle : quo X N K ≤ thompsonRank (⊤ : Subgroup (X ⧸ N.subgroupOf X)) := by
        unfold thompsonRank
        refine le_iSup_of_le (quo X N K) ?_
        refine le_iSup_of_le le_top ?_
        refine le_iSup_of_le ((f15bc_quo_comm hNK hKX).2 hKc) ?_
        refine le_iSup_of_le ?_ le_rfl
        intro W _ hWc
        obtain ⟨B, hNB, hBX, rfl⟩ := exists_quo hNX W
        have hBc := (f15bc_quo_comm hNB hBX).1 hWc
        exact (hrk hNB hBX hBc hNK hKX hKc).1 (hKmax B ⟨hNB, hBX, hBc⟩)
      exact ⟨⟨x, hKX hxK⟩, hle ⟨⟨x, hKX hxK⟩, mem_subgroupOf.2 hxK, rfl⟩, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', he⟩ := hsub (mem_subgroupOf.1 hy)
    have : y' = y := Subtype.ext he
    subst this
    exact hy'

theorem f15bc_three {fr : Frame Γ} (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    {L RG OR N kF kFs R : ℕ} (hlat : f15bc_Lat elt fr.Sσ L N) (hN : N ≤ 448)
    (ho : ordK L OR 0 N = true) (hp : IsPGroup 2 fr.Sσ) (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    (hb : f15bK P C V Q L RG N 1 2 3 4 5 6 kF kFs R = true) :
    SecProp fr.Sσ fr.Z (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) = (fr.A.subgroupOf fr.Sσ).map π) := by
  have hL : LatOK elt L N fr.Sσ := hlat
  have hgen : ∀ k < N, ∀ K : Subgroup Γ, RepM elt (entL L k) (K : Set Γ) →
      K = closure (rgSet elt RG k) := fun k hk K hK =>
    (f15bc_gen hR hlat hN ho hp hrg hall hk (hL.le hk hK) hK).symm
  unfold f15bK at hb
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true, Nat.beq_eq] at hb
  obtain ⟨-, c6, cz, cA, -, -, -, hnorm, hjA, -⟩ := hb
  obtain ⟨e1, e2, e3, e4, -, -⟩ := f13_gens hg
  obtain ⟨hz, -, -, -, -, -, -⟩ := f13_prods hR hg
  have hSs := f11_Ss hR hg c6
  have hZm : mset elt (closK C [atR Q 2] R) = (fr.Z : Set Γ) := by
    rw [closK_closure hR (fun g hg' => by rw [List.mem_singleton] at hg'; rw [hg']; exact atR_lt _ _)
      cz, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, hz]
    rw [f13_setOf_one]
    unfold SFrame.Z
    rw [Subgroup.zpowers_eq_closure]
  have hAm : mset elt (closK C [1, 2, 3, 4] R) = (fr.A : Set Γ) := by
    rw [closK_closure hR (by decide) cA, f13_setOf_eq_map]
    simp only [List.map_cons, List.map_nil, e1, e2, e3, e4]
    have : {x | x ∈ [fr.a₁, fr.b₁, fr.a₂, fr.b₂]} = ({fr.a₁, fr.b₁, fr.a₂, fr.b₂} : Set Γ) := by
      ext x
      simp
    rw [this]
    rfl
  have hAX : fr.A ≤ fr.Sσ := by
    unfold SFrame.A Frame.Sσ
    refine closure_mono ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  have hZA : fr.Z ≤ fr.A := by
    unfold SFrame.Z SFrame.z
    rw [Subgroup.zpowers_le]
    unfold SFrame.A
    exact pow_mem (subset_closure (by simp)) 2
  have hn : ∀ x ∈ fr.Sσ, ∀ n ∈ fr.Z, x * n * x⁻¹ ∈ fr.Z := by
    intro x hx n hn
    have := f15bc_normM hR hnorm x (by rw [hSs]; exact hx) n (by rw [hZm]; exact hn)
    rwa [hZm] at this
  have hnorm' : (fr.Z.subgroupOf fr.Sσ).Normal :=
    ⟨fun n hn0 g => by
      rw [mem_subgroupOf] at hn0 ⊢
      simpa using hn g.1 g.2 n.1 hn0⟩
  refine ⟨hnorm', ?_⟩
  exact f15bc_jr_quo hR hL hN hp hgen (f15bc_rep hR hSs) (f15bc_rep hR hZm)
    (f15bc_closK_lt _ _ _) (le_trans hZA hAX) hn hAm hZA hAX hjA

theorem fact15_3456_of_twin {fr : Frame Γ} {elt : ℕ → Γ} {P C V Q L RG OR N kF kFs R : ℕ}
    (hR : RealT elt P C V Q) (hg : ∀ s < 6, elt (s + 1) = sGen fr s)
    (hlat : (∀ k < N, ∃ K : Subgroup Γ, K ≤ fr.Sσ ∧ RepM elt (latM L k) (K : Set Γ)) ∧
      ∀ K ≤ fr.Sσ, ∃ k < N, RepM elt (latM L k) (K : Set Γ))
    (hN : N ≤ 448) (ho : ordK L OR 0 N = true) (hp : IsPGroup 2 fr.Sσ)
    (hrg : rgK L RG N = true)
    (hall : ∀ k < N, ∃ lo w, lo ≤ k ∧ k < lo + w ∧ w ≤ 448 ∧ rgAllK L OR RG N lo w = true)
    (hb : f15bK P C V Q L RG N 1 2 3 4 5 6 kF kFs R = true)
    (hc : f15cK P C V Q L RG N 1 2 3 4 5 6 R = true) :
    SecProp fr.Sσ fr.Z (fun Y _ _ π =>
      thompsonRank (⊤ : Subgroup Y) = (fr.A.subgroupOf fr.Sσ).map π) ∧
    (thompsonRank fr.Sσ = fr.F ⊔ closure {fr.σ} ∧ IsE 4 ↥(fr.F ⊔ closure {fr.σ}) ∧
      maxElemAbelian fr.Sσ = insert (fr.F ⊔ closure {fr.σ}) (maxElemAbelian fr.S) \ {fr.F}) ∧
    (∀ U : Subgroup Γ, U ≤ fr.Sσ → IsMulCommutative U → Nat.card U ≤ 16) ∧
    (pRank 2 fr.Sσ = 4 ∧ GH74.sectionalTwoRank ↥fr.Sσ = 4) :=
  ⟨f15bc_three hR hg hlat hN ho hp hrg hall hb, f15bc_four hR hg hlat hN ho hp hrg hall hb,
    f15bc_five_six hR hg hlat hN ho hp hrg hall hb hc⟩

end CFSG.KC.G2Three.Sec1T3

module

public import CFSG.Certificates.Kernel.LocalQTLatGSound
import all CFSG.Certificates.Kernel.LocalQTChainGSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExt
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermEnc
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermExtCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermIso

public section

namespace CFSG.KC.LQT.CM

open Equiv CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
  CFSG.QuasithinUnique.Unc25K1.Six

variable {n : ℕ}

@[expose] noncomputable def duH (n₁ n₂ : ℕ) : Perm (Fin n₁) × Perm (Fin n₂) →* Perm (Fin (n₁ + n₂)) :=
  (finSumFinEquiv.permCongrHom : Perm (Fin n₁ ⊕ Fin n₂) ≃* Perm (Fin (n₁ + n₂))).toMonoidHom.comp
    (Perm.sumCongrHom _ _)

theorem duH_inj (n₁ n₂ : ℕ) : Function.Injective (duH n₁ n₂) := fun _ _ hxy =>
  Perm.sumCongrHom_injective ((finSumFinEquiv.permCongrHom :
    Perm (Fin n₁ ⊕ Fin n₂) ≃* Perm (Fin (n₁ + n₂))).injective hxy)

theorem duH_castAdd {n₁ n₂ : ℕ} (p : Perm (Fin n₁) × Perm (Fin n₂)) (i : Fin n₁) :
    duH n₁ n₂ p (Fin.castAdd n₂ i) = Fin.castAdd n₂ (p.1 i) := by
  change finSumFinEquiv (Perm.sumCongr p.1 p.2 (finSumFinEquiv.symm (Fin.castAdd n₂ i))) = _
  rw [finSumFinEquiv_symm_apply_castAdd, Perm.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

theorem duH_natAdd {n₁ n₂ : ℕ} (p : Perm (Fin n₁) × Perm (Fin n₂)) (j : Fin n₂) :
    duH n₁ n₂ p (Fin.natAdd n₁ j) = Fin.natAdd n₁ (p.2 j) := by
  change finSumFinEquiv (Perm.sumCongr p.1 p.2 (finSumFinEquiv.symm (Fin.natAdd n₁ j))) = _
  rw [finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

theorem duK_code {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) (a : Perm (Fin n₁)) (b : Perm (Fin n₂)) :
    duK n₁ n₂ (P.code a) (P.code b) = P.code (duH n₁ n₂ (a, b)) := by
  have h₂ : n₂ ≤ 32 := by omega
  change P.code a + Nat.rec (motive := fun _ => ℕ) 0 (fun j acc => Nat.add acc
    ((fun j => Nat.shiftLeft (Nat.add n₁ (P.img (P.code b) j)) (Nat.mul 5 (Nat.add n₁ j))) j))
      n₂ = _
  rw [recSumL, Finset.sum_range]
  have e2 : ∑ j : Fin n₂, (fun j => Nat.shiftLeft (Nat.add n₁ (P.img (P.code b) j))
      (Nat.mul 5 (Nat.add n₁ j))) (j : ℕ) =
      ∑ j : Fin n₂, (n₁ + (b j : ℕ)) * 32 ^ (n₁ + (j : ℕ)) :=
    Finset.sum_congr rfl fun j _ => by
      change Nat.shiftLeft (n₁ + P.img (P.code b) j) (Nat.mul 5 (n₁ + j)) = _
      rw [P.shl_eq, img_code_fix h₂ b j.isLt]
  rw [e2, P.code_fin (duH n₁ n₂ (a, b)), Fin.sum_univ_add, P.code_fin a]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [duH_castAdd, Fin.val_castAdd, Fin.val_castAdd]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [duH_natAdd, Fin.val_natAdd, Fin.val_natAdd]

theorem zipDU_code {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) : ∀ (A : List (Perm (Fin n₁)))
    (B : List (Perm (Fin n₂))),
    zipDU n₁ n₂ (A.map P.code) (B.map P.code) = ((A.zip B).map (duH n₁ n₂)).map P.code
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: A, b :: B => by
    change duK n₁ n₂ (P.code a) (P.code b) :: zipDU n₁ n₂ (A.map P.code) (B.map P.code) = _
    rw [zipDU_code h A B, duK_code h, List.zip_cons_cons, List.map_cons, List.map_cons]

theorem img_duH {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) (p : Perm (Fin n₁) × Perm (Fin n₂)) {i : ℕ}
    (hi : i < n₁) : P.img (P.code (duH n₁ n₂ p)) i = P.img (P.code p.1) i := by
  have h₁ : n₁ ≤ 32 := by omega
  rw [img_code_fix h _ (by omega), img_code_fix h₁ _ hi]
  have e : (⟨i, by omega⟩ : Fin (n₁ + n₂)) = Fin.castAdd n₂ ⟨i, hi⟩ := Fin.ext rfl
  rw [e, duH_castAdd, Fin.val_castAdd]

theorem mul_duH {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) (p q : Perm (Fin n₁) × Perm (Fin n₂)) :
    P.mul n₁ (P.code (duH n₁ n₂ p)) (P.code (duH n₁ n₂ q)) = P.code (p.1 * q.1) := by
  have h₁ : n₁ ≤ 32 := by omega
  rw [← P.code_mul h₁]
  change P.ofFn n₁ (fun i => P.img (P.code (duH n₁ n₂ p)) (P.img (P.code (duH n₁ n₂ q)) i)) =
    P.ofFn n₁ (fun i => P.img (P.code p.1) (P.img (P.code q.1) i))
  refine ofFn_congr fun i hi => ?_
  rw [img_duH h q hi, img_duH h p (img_code_lt h₁ q.1 hi)]

theorem fixHi_duH {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) (a : Perm (Fin n₁)) :
    fixHi n₁ n₂ (P.code (duH n₁ n₂ (a, 1))) = true := by
  unfold fixHi
  rw [P.allN_iff]
  intro j hj
  rw [P.beq_iff]
  change P.img (P.code (duH n₁ n₂ (a, 1))) (n₁ + j) = n₁ + j
  rw [img_code_fix h _ (by omega)]
  have e : (⟨n₁ + j, by omega⟩ : Fin (n₁ + n₂)) = Fin.natAdd n₁ ⟨j, hj⟩ := Fin.ext rfl
  rw [e, duH_natAdd, Fin.val_natAdd]
  rfl

theorem letL_eq (y : ℕ) (k : ℕ → List ℕ) : CFSG.KC.LQT.T2.letL y k = k y := by
  cases y <;> rfl

theorem recL_mono {x : ℕ} (g : ℕ → List ℕ → List ℕ) (hg : ∀ j L, x ∈ L → x ∈ g j L) :
    ∀ (m : ℕ) (acc : List ℕ), x ∈ acc →
      x ∈ Nat.rec (motive := fun _ => List ℕ) acc (fun j accJ => g j accJ) m
  | 0, _, h => h
  | m + 1, acc, h => hg m _ (recL_mono g hg m acc h)

theorem recL_hit {x : ℕ} (g : ℕ → List ℕ → List ℕ) (hg : ∀ j L, x ∈ L → x ∈ g j L) {j0 : ℕ}
    (hj0 : ∀ L, x ∈ g j0 L) : ∀ (m : ℕ) (acc : List ℕ), j0 < m →
      x ∈ Nat.rec (motive := fun _ => List ℕ) acc (fun j accJ => g j accJ) m
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, acc, h => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact hg m _ (recL_hit g hg hj0 m acc h)
    · exact hj0 _

theorem colFrom_mono (f : ℕ → ℕ) (s : ℕ → Bool) {x : ℕ} : ∀ (C : List Lvl) (p : ℕ)
    (acc : List ℕ), x ∈ acc → x ∈ CFSG.KC.LQT.PH.colFrom n C f s p acc
  | [], p, acc, h => by
    change x ∈ CFSG.KC.LQT.T2.letL (f p) (fun h => Bool.rec (motive := fun _ => List ℕ) acc
      (h :: acc) (s h))
    rw [letL_eq]
    cases s (f p)
    · exact h
    · exact List.mem_cons_of_mem _ h
  | lv :: C, p, acc, h => by
    change x ∈ Nat.rec (motive := fun _ => List ℕ) acc (fun j accJ =>
      Bool.rec (motive := fun _ => List ℕ)
        (CFSG.KC.LQT.T2.letL (P.mul n p (getK lv.2.1 j)) fun q =>
          CFSG.KC.LQT.PH.colFrom n C f s q accJ) accJ (Nat.beq (getK lv.2.1 j) 0)) n
    refine recL_mono _ (fun j L hL => ?_) n acc h
    cases Nat.beq (getK lv.2.1 j) 0
    · dsimp only
      rw [letL_eq]
      exact colFrom_mono f s C _ L hL
    · exact hL

theorem colFrom_hit (hn : n ≤ 32) (f : ℕ → ℕ) (s : ℕ → Bool) : ∀ {C : List Lvl},
    (∀ lv ∈ C, LvOK n lv) → ∀ (π σ : Perm (Fin n)) (acc : List ℕ), InC n C σ →
      s (f (P.code (π * σ))) = true →
      f (P.code (π * σ)) ∈ CFSG.KC.LQT.PH.colFrom n C f s (P.code π) acc
  | [], _, π, σ, acc, hσ, hs => by
    rw [inC_nil hn] at hσ
    subst hσ
    rw [mul_one] at hs ⊢
    change f (P.code π) ∈ CFSG.KC.LQT.T2.letL (f (P.code π)) (fun h =>
      Bool.rec (motive := fun _ => List ℕ) acc (h :: acc) (s h))
    rw [letL_eq, hs]
    exact List.mem_cons_self
  | lv :: C, hC, π, σ, acc, hσ, hs => by
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hσ
    obtain ⟨j, hj, τ, hτ, e, -, k', h', -⟩ := sift_cons_code hn (hC lv (List.mem_cons_self ..)) σ hk
    have hC' : ∀ l ∈ C, LvOK n l := fun l hl => hC l (List.mem_cons_of_mem _ hl)
    change _ ∈ Nat.rec (motive := fun _ => List ℕ) acc (fun j accJ =>
      Bool.rec (motive := fun _ => List ℕ)
        (CFSG.KC.LQT.T2.letL (P.mul n (P.code π) (getK lv.2.1 j)) fun q =>
          CFSG.KC.LQT.PH.colFrom n C f s q accJ) accJ (Nat.beq (getK lv.2.1 j) 0)) n
    refine recL_hit _ (fun j L hL => ?_) (j0 := j) (fun L => ?_) n acc hj
    · cases Nat.beq (getK lv.2.1 j) 0
      · dsimp only
        rw [letL_eq]
        exact colFrom_mono f s C _ L hL
      · exact hL
    · have hb : Nat.beq (getK lv.2.1 j) 0 = false := by
        cases h0 : Nat.beq (getK lv.2.1 j) 0
        · rfl
        · exact absurd (P.beq_iff.1 h0) e
      rw [hb]
      dsimp only
      rw [letL_eq, ← hτ, P.code_mul hn]
      have := colFrom_hit hn f s hC' (π * τ) (τ⁻¹ * σ) L (by rw [InC, h']; rfl)
        (by rwa [mul_assoc, mul_inv_cancel_left])
      rwa [mul_assoc, mul_inv_cancel_left] at this

theorem closedH_gen {G R : Type} [Group G] [Mul R] [One R] [DecidableEq R] [Hashable R]
    {enc : G → R} (he : IsEnc enc) (gens : List G) (d : ℕ) (Q : G → Prop)
    (hmem : ∀ r, r ∈ bfsSet (gens.map enc) d ↔ ∃ σ, Q σ ∧ enc σ = r) (h1 : Q 1)
    (hmul : ∀ σ, Q σ → ∀ g ∈ gens, Q (σ * g)) :
    closedH (gens.map enc) (bfsSet (gens.map enc) d) = true := by
  unfold closedH
  rw [Bool.and_eq_true, Std.HashSet.contains_iff_mem, toList_all_iff]
  refine ⟨(hmem 1).2 ⟨1, h1, he.map_one⟩, fun x hx => ?_⟩
  obtain ⟨σ, hσ, rfl⟩ := (hmem x).1 hx
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hg
  rw [Std.HashSet.contains_iff_mem, ← he.map_mul]
  exact (hmem _).2 ⟨_, hmul σ hσ γ hγ, rfl⟩

theorem lift_words {n₁ n₂ : ℕ} (Z : List (Perm (Fin n₁) × Perm (Fin n₂))) :
    ∀ l0 : List (Perm (Fin (n₁ + n₂))), (∀ g ∈ l0, g ∈ Z.map (duH n₁ n₂)) →
      ∃ l : List (Perm (Fin n₁) × Perm (Fin n₂)), (∀ g ∈ l, g ∈ Z) ∧ l.length = l0.length ∧
        duH n₁ n₂ l.prod = l0.prod
  | [], _ => ⟨[], by simp, rfl, by simp⟩
  | g :: l0, h => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (h g List.mem_cons_self)
    obtain ⟨l, hl, hlen, e⟩ := lift_words Z l0 fun g hg => h g (List.mem_cons_of_mem _ hg)
    refine ⟨p :: l, fun g hg => ?_, by simp [hlen], by rw [List.prod_cons, map_mul, e,
      List.prod_cons]⟩
    rcases List.mem_cons.1 hg with rfl | hg
    · exact hp
    · exact hl g hg

theorem diagExtC_sound {n₁ n₂ : ℕ} (h : n₁ + n₂ ≤ 32) {d N M : ℕ}
    (A : List (Perm (Fin n₁))) (B : List (Perm (Fin n₂))) (CA : List Lvl)
    (WA : List (List (List ℕ))) (CB : List Lvl) (WB : List (List (List ℕ))) (CD : List Lvl)
    (WD : List (List (List ℕ))) (hIA : chainInj n₁ CA = true) (hIB : chainInj n₂ CB = true)
    (hID : chainInj (n₁ + n₂) CD = true)
    (hc : diagExtC n₁ n₂ d (A.map P.code) (B.map P.code) N M CA WA CB WB CD WD = true) :
    diagExtOK (RN.enc : Perm (Fin n₁) → RN n₁)
      (RN.enc : Perm (Fin n₂) → RN n₂) d A B N M = true := by
  classical
  have h₁ : n₁ ≤ 32 := by omega
  have h₂ : n₂ ≤ 32 := by omega
  unfold diagExtC at hc
  simp only [CFSG.KC.LQT.S.allBs_cons, CFSG.KC.LQT.S.allBs_nil, P.andB_iff, and_true] at hc
  obtain ⟨cA, sA, cB, sB, cD, sD, sL, sK⟩ := hc
  rw [P.beq_iff] at sA sB sD
  rw [P.beq_iff, LK.lenA_eq, LK.lenA_eq, List.length_map, List.length_map] at sL
  obtain ⟨-, -, -, -, hszA, hclA⟩ := memG_spec h₁ (A.map P.code, CA, WA) A rfl hIA cA
  obtain ⟨-, -, -, -, hszB, hclB⟩ := memG_spec h₂ (B.map P.code, CB, WB) B rfl hIB cB
  set Z := A.zip B with hZ
  set Ld := Z.map (duH n₁ n₂) with hLd
  change closedMG (n₁ + n₂) d (zipDU n₁ n₂ (A.map P.code) (B.map P.code), CD, WD) = true at cD
  rw [zipDU_code h] at cD
  unfold closedMG at cD
  rw [P.andB_iff] at cD
  obtain ⟨hokD, hgD⟩ := cD
  have hCD := chainP_lvOK (chainP_of_ok hokD hID)
  obtain ⟨g1, g2⟩ := grpS_sound h hokD hID Ld hgD
  have he := isEnc_prod (rawIsEnc n₁) (rawIsEnc n₂)
  set Dp := Subgroup.closure {p | p ∈ Z} with hDp
  have hmap : ∀ x ∈ Dp, duH n₁ n₂ x ∈ Subgroup.closure {g | g ∈ Ld} := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (List.mem_map_of_mem hx)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y _ _ ihx ihy => rw [map_mul]; exact Subgroup.mul_mem _ ihx ihy
    | inv x _ ihx => rw [map_inv]; exact Subgroup.inv_mem _ ihx
  have hword : ∀ x ∈ Dp, ∃ l : List (Perm (Fin n₁) × Perm (Fin n₂)), (∀ g ∈ l, g ∈ Z) ∧
      l.length ≤ d ∧ l.prod = x := by
    intro x hx
    obtain ⟨l0, hl0, hlen0, e0⟩ := g2 _ ((g1 _).2 (hmap x hx))
    obtain ⟨l, hl, hlen, e⟩ := lift_words Z l0 hl0
    exact ⟨l, hl, by omega, duH_inj n₁ n₂ (e.trans e0)⟩
  have hmemP : ∀ r, r ∈ bfsSet (Z.map fun p => (RN.enc p.1, RN.enc p.2)) d ↔
      ∃ x, x ∈ Dp ∧ (RN.enc x.1, RN.enc x.2) = r := by
    intro r
    constructor
    · intro hr
      obtain ⟨x, hx, e⟩ := bfsSet_sound he Z d r hr
      exact ⟨x, hx, e⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨l, hl, hlen, rfl⟩ := hword x hx
      exact mem_bfsSet_prod (enc := fun p : Perm (Fin n₁) × Perm (Fin n₂) =>
        (RN.enc p.1, RN.enc p.2)) he.map_mul he.map_one Z d l hl hlen
  have hclP : closedH (Z.map fun p => (RN.enc p.1, RN.enc p.2))
      (bfsSet (Z.map fun p => (RN.enc p.1, RN.enc p.2)) d) = true :=
    closedH_gen he Z d (· ∈ Dp) hmemP (Subgroup.one_mem _)
      fun σ hσ g hg => Subgroup.mul_mem _ hσ (Subgroup.subset_closure hg)
  have hszP : (bfsSet (Z.map fun p => (RN.enc p.1, RN.enc p.2)) d).size = chainF CD := by
    rw [← card_closure_of_closedH he Z d hclP, ← Subgroup.card_map_of_injective (duH_inj n₁ n₂),
      MonoidHom.map_closure]
    have e : (duH n₁ n₂) '' {p | p ∈ Z} = {g | g ∈ Ld} := by
      ext g
      simp only [Set.mem_image, Set.mem_ofPred_eq, hLd, List.mem_map]
    rw [e, ← card_inC h hokD hID]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => (g1 σ).symm)
  have hK : ∀ x ∈ Dp, x.2 = 1 → P.code (duH n₁ n₂ x) ∈
      CFSG.KC.LQT.PH.colAll (Nat.add n₁ n₂) CD (fun x => x) (fixHi n₁ n₂) := by
    intro x hx hx2
    have := colFrom_hit h (fun x => x) (fixHi n₁ n₂) hCD 1 (duH n₁ n₂ x) [] ((g1 _).2 (hmap x hx))
      (by
        rw [one_mul]
        obtain ⟨a, b⟩ := x
        dsimp only at hx2
        subst hx2
        exact fixHi_duH h a)
    rw [one_mul, ← P.code_one] at this
    exact this
  unfold kerOK at sK
  rw [P.allL_iff] at sK
  unfold diagExtOK
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_filter]
  refine ⟨⟨⟨⟨⟨⟨⟨hclA, by rw [← sA]; exact hszA.symm⟩, hclB⟩, by rw [← sB]; exact hszB.symm⟩,
    hclP⟩, by rw [← sD]; exact hszP⟩, sL⟩, fun r hr => ?_⟩
  obtain ⟨hr1, hr2⟩ := hr
  rw [Std.HashSet.mem_toList] at hr1
  obtain ⟨x, hx, rfl⟩ := (hmemP r).1 hr1
  have hx2 : x.2 = 1 := RN.enc_inj (hr2.trans RN.enc_one.symm)
  have cx := sK _ (hK x hx hx2)
  rw [P.andB_iff, P.beq_iff, mul_duH h, P.code_one, P.code_eq_iff h₁, P.allL_iff] at cx
  refine ⟨by rw [← RN.enc_mul, cx.1, RN.enc_one], fun s hs => ?_⟩
  obtain ⟨hs1, hs2⟩ := hs
  rw [Std.HashSet.mem_toList] at hs1
  obtain ⟨y, hy, rfl⟩ := (hmemP s).1 hs1
  have hy2 : y.2 = 1 := RN.enc_inj (hs2.trans RN.enc_one.symm)
  have hxy := cx.2 _ (hK y hy hy2)
  rw [P.beq_iff, mul_duH h, mul_duH h, P.code_eq_iff h₁] at hxy
  rw [← RN.enc_mul, ← RN.enc_mul, hxy]

end CFSG.KC.LQT.CM

end

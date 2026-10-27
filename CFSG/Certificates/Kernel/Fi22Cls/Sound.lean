
module

public import Certificates.Data.Kernel.Fi22Cls.Check
public import CFSG.Certificates.Kernel.Fi22S0.Sound
public import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KD.Fi22Cls

open CFSG.KC.Enum CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KD.Fi22S0 CFSG.HardMathSupport.Foote.E27
open CFSG.Sporadic.Fi22 (J)
open CFSG.Sporadic.Fi22.S0 (nS)
open CFSG.HardMathSupport.Foote.E27.Fi22S0 (gJ)
open CFSG.Sporadic.Th (idx idx_one)

theorem strictN_eq (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by
  cases y <;> rfl

theorem ble_iff (i k : ℕ) : Nat.ble i k = true ↔ i ≤ k := by
  rw [Nat.ble_eq]

theorem nS_eq : nS = 19683 := rfl

section Count

variable {G : Type*} [Group G]

theorem natCard_eq_filter [Fintype G] (H : Subgroup G) [DecidablePred (· ∈ H)] :
    Nat.card H = (Finset.univ.filter (· ∈ H)).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp)

theorem card_eq_conj [Fintype G] [DecidableEq G] (T : Subgroup G) (x : G) [DecidablePred (· ∈ T)]
    [DecidablePred (· ∈ T ⊓ Subgroup.centralizer ({x} : Set G))] :
    (Finset.univ.filter (· ∈ T)).card =
      ((Finset.univ.filter (· ∈ T)).image fun t => t * x * t⁻¹).card *
        (Finset.univ.filter (· ∈ T ⊓ Subgroup.centralizer ({x} : Set G))).card := by
  set U := Finset.univ.filter (· ∈ T)
  set V := Finset.univ.filter (· ∈ T ⊓ Subgroup.centralizer ({x} : Set G))
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t * x * t⁻¹)
    (t := U.image fun t => t * x * t⁻¹) (fun t ht => Finset.mem_image_of_mem _ ht)]
  rw [← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun y hy => ?_
  obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.1 hy
  have hT0 : t0 ∈ T := (Finset.mem_filter.1 ht0).2
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (fun t => t0⁻¹ * t) ?_ ?_
    · intro t ht
      have ht' : t ∈ U.filter fun a => a * x * a⁻¹ = t0 * x * t0⁻¹ := by simpa using ht
      obtain ⟨htU, he⟩ := Finset.mem_filter.1 ht'
      have htT : t ∈ T := (Finset.mem_filter.1 htU).2
      have hm : t0⁻¹ * t ∈ T ⊓ Subgroup.centralizer ({x} : Set G) := by
        refine ⟨T.mul_mem (T.inv_mem hT0) htT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        calc t0⁻¹ * t * x = t0⁻¹ * (t * x * t⁻¹) * t := by group
          _ = t0⁻¹ * (t0 * x * t0⁻¹) * t := by rw [he]
          _ = x * (t0⁻¹ * t) := by group
      simpa [V] using hm
    · intro a _ b _ e
      exact mul_left_cancel e
  · refine Finset.card_le_card_of_injOn (fun c => t0 * c) ?_ ?_
    · intro c hc
      have hc' : c ∈ T ⊓ Subgroup.centralizer ({x} : Set G) := by simpa [V] using hc
      have hcT : c ∈ T := hc'.1
      have hcx : c * x = x * c :=
        Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hc').2
      have he : t0 * c * x * (t0 * c)⁻¹ = t0 * x * t0⁻¹ := by
        calc t0 * c * x * (t0 * c)⁻¹ = t0 * (c * x) * c⁻¹ * t0⁻¹ := by group
          _ = t0 * (x * c) * c⁻¹ * t0⁻¹ := by rw [hcx]
          _ = t0 * x * t0⁻¹ := by group
      have hm : t0 * c ∈ U.filter fun a => a * x * a⁻¹ = t0 * x * t0⁻¹ :=
        Finset.mem_filter.2 ⟨by simpa [U] using T.mul_mem hT0 hcT, he⟩
      simpa using hm
    · intro a _ b _ e
      exact mul_left_cancel e

theorem card_le_mul_of_conj [Finite G] (T : Subgroup G) (x : G) (S : Finset G)
    (hS : ∀ t ∈ T, t * x * t⁻¹ ∈ S) :
    Nat.card T ≤ S.card * Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) := by
  classical
  have := Fintype.ofFinite G
  rw [natCard_eq_filter T, natCard_eq_filter (T ⊓ _), card_eq_conj T x]
  refine Nat.mul_le_mul_right _ (Finset.card_le_card fun y hy => ?_)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
  exact hS t (Finset.mem_filter.1 ht).2

theorem mul_card_le_of_conj [Finite G] (T : Subgroup G) (x : G) {k : ℕ} (ts : ℕ → G)
    (hts : ∀ m < k, ts m ∈ T)
    (hd : ∀ a < k, ∀ b < k, ts a * x * (ts a)⁻¹ = ts b * x * (ts b)⁻¹ → a = b) :
    k * Nat.card ↥(T ⊓ Subgroup.centralizer ({x} : Set G)) ≤ Nat.card T := by
  classical
  have := Fintype.ofFinite G
  rw [natCard_eq_filter T, natCard_eq_filter (T ⊓ _), card_eq_conj T x]
  refine Nat.mul_le_mul_right _ ?_
  have hk : ((Finset.range k).image fun m => ts m * x * (ts m)⁻¹).card = k := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    exact hd a (by simpa using ha) b (by simpa using hb) e
  rw [← hk]
  refine Finset.card_le_card fun y hy => ?_
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hy
  exact Finset.mem_image.2 ⟨ts m, by simpa using hts m (by simpa using hm), rfl⟩

@[expose] def setStab (S : Finset G) : Subgroup G where
  carrier := {t | ∀ y, y ∈ S ↔ t * y * t⁻¹ ∈ S}
  one_mem' := fun y => by simp
  mul_mem' := by
    intro a b ha hb y
    have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
    rw [e, hb y, ha]
  inv_mem' := by
    intro a ha y
    have e : a * (a⁻¹ * y * a⁻¹⁻¹) * a⁻¹ = y := by group
    rw [ha (a⁻¹ * y * a⁻¹⁻¹), e]

theorem mem_setStab [DecidableEq G] {S : Finset G} {t : G} (h : ∀ y ∈ S, t * y * t⁻¹ ∈ S) :
    t ∈ setStab S := by
  intro y
  refine ⟨h y, fun hy => ?_⟩
  have hinj : Function.Injective fun z => t * z * t⁻¹ := fun a b e => by
    simpa using e
  have himg : S.image (fun z => t * z * t⁻¹) = S :=
    Finset.eq_of_subset_of_card_le (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz
      exact h w hw) (by rw [Finset.card_image_of_injective _ hinj])
  rw [← himg] at hy
  obtain ⟨w, hw, e⟩ := Finset.mem_image.1 hy
  rw [← hinj e]
  exact hw

end Count

section Table

variable {G : Type*} [Group G] {g : ℕ → G} {P : Array (ℕ × ℕ)} {Lt : Array (Array ℕ)}
  {pp pj : ℕ → ℕ} {lt : ℕ → ℕ → ℕ}

theorem tmF_eq (hT : TabData g P Lt nS 3) (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i)
    (hL : ∀ j < 3, ∀ i < nS, (Lt[j]!)[i]! = lt j i) :
    ∀ f a, a < f → a < nS → ∀ b < nS, tmF pp pj lt f a b = tabMul P Lt a b := by
  intro f
  induction f with
  | zero => intro a ha; omega
  | succ f ih =>
    intro a ha han b hb
    have e : tmF pp pj lt (f + 1) a b =
        strictN (pp a) fun p => nIf(Nat.blt p a, lt (pj a) (tmF pp pj lt f p b), b) := rfl
    rw [e, strictN_eq]
    obtain ⟨e1, e2⟩ := hpar a han
    by_cases hp : pp a < a
    · have hb' : Nat.blt (pp a) a = true := (blt_iff _ _).2 hp
      rw [hb']
      have hp' : (P[a]!).1 < a := by rw [e1]; exact hp
      have hpos : 0 < a := by omega
      have hj : (P[a]!).2 < 3 := (hT.par_lt a hpos han).2
      have hm : tabMul P Lt (pp a) b < nS := (hT.mul (pp a) (by omega) b hb).1
      have hj' : pj a < 3 := by rw [← e2]; exact hj
      change lt (pj a) (tmF pp pj lt f (pp a) b) = _
      rw [ih (pp a) (by omega) (by omega) b hb, tabMul_succ P Lt b hp', e1, e2, hL _ hj' _ hm]
    · have hb' : Nat.blt (pp a) a = false := by
        cases h : Nat.blt (pp a) a
        · rfl
        · exact absurd ((blt_iff _ _).1 h) hp
      rw [hb']
      have hp' : ¬(P[a]!).1 < a := by rw [e1]; exact hp
      rw [tabMul]
      simp [hp']

theorem tm_eq (hT : TabData g P Lt nS 3) (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i)
    (hL : ∀ j < 3, ∀ i < nS, (Lt[j]!)[i]! = lt j i) {a b : ℕ} (ha : a < nS) (hb : b < nS) :
    tm pp pj lt a b = tabMul P Lt a b :=
  tmF_eq hT hpar hL (a + 1) a (by omega) ha b hb

theorem elt_eq_of_tm (hT : TabData g P Lt nS 3)
    (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i)
    (hL : ∀ j < 3, ∀ i < nS, (Lt[j]!)[i]! = lt j i) {a b c d : ℕ} (ha : a < nS) (hb : b < nS)
    (hc : c < nS) (hd : d < nS) (h : tm pp pj lt a b = tm pp pj lt c d) :
    tabElt g P a * tabElt g P b = tabElt g P c * tabElt g P d := by
  rw [(hT.mul a ha b hb).2, (hT.mul c hc d hd).2, ← tm_eq hT hpar hL ha hb,
    ← tm_eq hT hpar hL hc hd, h]

theorem rho_of_rhoC (hT : TabData g P Lt nS 3)
    (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i)
    (hL : ∀ j < 3, ∀ i < nS, (Lt[j]!)[i]! = lt j i) {ρ : ℕ} (hρ : ρ < nS)
    (h : rhoC pp pj lt ρ = true) : ρ ≠ 0 ∧ tabMul P Lt ρ (tabMul P Lt ρ ρ) = 0 := by
  unfold rhoC at h
  simp only [bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h
  obtain ⟨h0, h1⟩ := h
  have hm := (hT.mul ρ hρ ρ hρ).1
  rw [tm_eq hT hpar hL hρ hρ, tm_eq hT hpar hL hρ hm] at h1
  exact ⟨by omega, h1⟩

theorem gen_of_genC (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i) {gi : ℕ → ℕ}
    (h : genC pp pj gi 19683 = true) {j : ℕ} (hj : j < 3) :
    gi j < nS ∧ tabElt g P (gi j) = g j := by
  unfold genC at h
  have h' := CFSG.KS.allN_spec h j hj
  simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h'
  obtain ⟨h0, h1, h2, h3⟩ := h'
  obtain ⟨e1, e2⟩ := hpar (gi j) (by rw [nS_eq]; exact h1)
  have hp : (P[gi j]!).1 < gi j := by rw [e1, h2]; exact h0
  refine ⟨by rw [nS_eq]; exact h1, ?_⟩
  rw [tabElt_succ g P hp, e1, e2, h2, h3, tabElt_zero, mul_one]

theorem comm_ge_of_closC [Finite G] (hT : TabData g P Lt nS 3)
    (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i)
    (hL : ∀ j < 3, ∀ i < nS, (Lt[j]!)[i]! = lt j i) {gi X : ℕ → ℕ} {q : ℕ → ℕ → ℕ} {ρ c p : ℕ}
    (hgen : genC pp pj gi 19683 = true) (hcl : closC pp pj lt gi X q ρ c p 19683 = true) :
    ρ < nS ∧ 2187 ≤ tabComm P Lt nS ρ := by
  classical
  unfold closC at hcl
  simp only [bRec_and, Bool.and_eq_true, ble_iff, blt_iff, beq_iff] at hcl
  obtain ⟨hc9, hpc, hXp, hall⟩ := hcl
  have hu : ∀ u < c, X u < nS ∧ ∀ j < 3, q u j < c ∧
      tm pp pj lt (gi j) (X u) = tm pp pj lt (X (q u j)) (gi j) := by
    intro u hu
    have h1 := CFSG.KS.allBlk_spec hall u hu
    rw [Nat.add_eq, Nat.zero_add, sB_eq] at h1
    simp only [bRec_and, Bool.and_eq_true, blt_iff] at h1
    refine ⟨by rw [nS_eq]; exact h1.1, fun j hj => ?_⟩
    have h2 := CFSG.KS.allBlk_spec h1.2 j hj
    rw [Nat.add_eq, Nat.zero_add, sB_eq, sB_eq] at h2
    simp only [bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h2
    exact h2
  have hρ : ρ < nS := by rw [← hXp]; exact (hu p hpc).1
  obtain ⟨T, hTm, hTc⟩ := hT.exists_subgroup (by rw [nS_eq]; norm_num)
  set S : Finset G := (Finset.range c).image fun u => tabElt g P (X u) with hS
  have hgS : ∀ j < 3, ∀ y ∈ S, g j * y * (g j)⁻¹ ∈ S := by
    intro j hj y hy
    obtain ⟨u, hu', rfl⟩ := Finset.mem_image.1 hy
    have hu'' : u < c := by simpa using hu'
    obtain ⟨hX, hq⟩ := hu u hu''
    obtain ⟨hqc, he⟩ := hq j hj
    obtain ⟨hgi, hge⟩ := gen_of_genC (g := g) hpar hgen hj
    have e := elt_eq_of_tm hT hpar hL hgi hX (hu _ hqc).1 hgi he
    rw [hge] at e
    rw [e, mul_inv_cancel_right]
    exact Finset.mem_image.2 ⟨q u j, by simpa using hqc, rfl⟩
  have hTK : T ≤ setStab S := by
    rw [hTc, Subgroup.closure_le]
    rintro _ ⟨⟨j, hj⟩, rfl⟩
    exact mem_setStab (hgS j hj)
  have hρS : tabElt g P ρ ∈ S := Finset.mem_image.2 ⟨p, by simpa using hpc, by rw [hXp]⟩
  have hle := card_le_mul_of_conj T (tabElt g P ρ) S fun t ht => (hTK ht _).1 hρS
  rw [hT.card_subgroup hTm, hT.card_inf_centralizer hTm hρ] at hle
  have hSc : S.card ≤ 9 := le_trans Finset.card_image_le (by rw [Finset.card_range]; exact hc9)
  have h9 := le_trans hle (Nat.mul_le_mul_right _ hSc)
  have hn := nS_eq
  exact ⟨hρ, by omega⟩

theorem comm_le_of_conjgC [Finite G] (hT : TabData g P Lt nS 3)
    (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i)
    (hL : ∀ j < 3, ∀ i < nS, (Lt[j]!)[i]! = lt j i) {ct cx : ℕ → ℕ} {ρ : ℕ} (hρ : ρ < nS)
    (h : ∀ m < 9, conjgC pp pj lt ct cx ρ 19683 m = true) : tabComm P Lt nS ρ ≤ 2187 := by
  have hm : ∀ m < 9, ct m < nS ∧ cx m < nS ∧ (m = 0 ∨ cx (m - 1) < cx m) ∧
      tm pp pj lt (ct m) ρ = tm pp pj lt (cx m) (ct m) := by
    intro m hm9
    have h1 := h m hm9
    unfold conjgC at h1
    rw [sB_eq, sB_eq] at h1
    rcases m with _ | m
    · simp only [bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h1
      exact ⟨by rw [nS_eq]; exact h1.1, by rw [nS_eq]; exact h1.2.1, Or.inl rfl, h1.2.2.2⟩
    · have hb : Nat.beq (m + 1) 0 = false := rfl
      have hs : Nat.sub (m + 1) 1 = m := Nat.add_sub_cancel m 1
      rw [hb, hs] at h1
      simp only [bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h1
      exact ⟨by rw [nS_eq]; exact h1.1, by rw [nS_eq]; exact h1.2.1, Or.inr h1.2.2.1, h1.2.2.2⟩
  have hmono : ∀ a b, a < b → b < 9 → cx a < cx b := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hs := (hm (b + 1) hb).2.2.1
      rcases hs with hs | hs
      · omega
      · rw [Nat.add_sub_cancel] at hs
        rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | rfl
        · exact lt_trans (ih h' (by omega)) hs
        · exact hs
  obtain ⟨T, hTm, -⟩ := hT.exists_subgroup (by rw [nS_eq]; norm_num)
  have hconj : ∀ m < 9, tabElt g P (ct m) * tabElt g P ρ * (tabElt g P (ct m))⁻¹ =
      tabElt g P (cx m) := by
    intro m hm9
    obtain ⟨h1, h2, -, h4⟩ := hm m hm9
    rw [elt_eq_of_tm hT hpar hL h1 hρ h2 h1 h4, mul_inv_cancel_right]
  have hle := mul_card_le_of_conj T (tabElt g P ρ) (k := 9) (fun m => tabElt g P (ct m))
    (fun m hm9 => (hTm _).2 ⟨ct m, (hm m hm9).1, rfl⟩) (by
      intro a ha b hb e
      rw [hconj a ha, hconj b hb] at e
      have e' := hT.inj _ (hm a ha).2.1 _ (hm b hb).2.1 e
      rcases lt_trichotomy a b with h' | h' | h'
      · exact absurd e' (ne_of_lt (hmono a b h' hb))
      · exact h'
      · exact absurd e' (ne_of_gt (hmono b a h' ha)))
  rw [hT.card_subgroup hTm, hT.card_inf_centralizer hTm hρ] at hle
  have hn := nS_eq
  omega

end Table

theorem ent_letT (P S l x : ℕ) : ent (letT P S l) x = CFSG.KS.Fi22L.LJk P S l x := by
  unfold letT CFSG.KS.Fi22L.LJk
  cases Nat.beq (Nat.land l (nat_lit 1)) (nat_lit 0) <;> rfl

@[expose] noncomputable def wordJ (lJ : ℕ → J) (w : ℕ → ℕ) (s m : ℕ) : J :=
  ((List.range' s m).map fun t => lJ (w t)).prod

theorem wordK_succ (LT w : ℕ → ℕ) (m s K : ℕ) :
    wordK LT w (m + 1) s K = mapK (LT (w s)) (wordK LT w m (s + 1) K) := by
  change strictN (wordK LT w m (Nat.succ s) K) (fun K' => strictN (LT (w s)) fun T => mapK T K') = _
  rw [strictN_eq, strictN_eq]

theorem wordK_keyOf {LT w : ℕ → ℕ} {lJ : ℕ → J} :
    ∀ (m s : ℕ), (∀ t, s ≤ t → t < s + m → RepE (LT (w t)) (lJ (w t))) → ∀ h : J,
      wordK LT w m s (keyOf h) = keyOf (wordJ lJ w s m * h)
  | 0, s, _, h => by
    unfold wordJ
    rw [List.range'_zero, List.map_nil, List.prod_nil, one_mul]
    rfl
  | m + 1, s, hw, h => by
    rw [wordK_succ, wordK_keyOf m (s + 1) (fun t h1 h2 => hw t (by omega) (by omega)) h,
      mapK_keyOf (hw s le_rfl (by omega))]
    unfold wordJ
    rw [List.range'_succ, List.map_cons, List.prod_cons, mul_assoc]

theorem eK_keyOf {gt pp pj : ℕ → ℕ} {P : Array (ℕ × ℕ)} {Lt : Array (Array ℕ)}
    (hg : ∀ j < 3, RepE (gt j) (gJ j)) (hT : TabData gJ P Lt nS 3)
    (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i) :
    ∀ f i, i < f → i < nS → ∀ h : J, eK gt pp pj f i (keyOf h) = keyOf (tabElt gJ P i * h) := by
  intro f
  induction f with
  | zero => intro i hi; omega
  | succ f ih =>
    intro i hi hin h
    have e : eK gt pp pj (f + 1) i (keyOf h) = nIf(Nat.beq i (nat_lit 0), keyOf h,
        strictN (pp i) fun p => strictN (eK gt pp pj f p (keyOf h)) fun K' =>
          strictN (gt (pj i)) fun T => mapK T K') := rfl
    rw [e]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [tabElt_zero, one_mul]
      rfl
    · have hb : Nat.beq i 0 = false := by
        cases i
        · omega
        · rfl
      rw [hb]
      change strictN (pp i) (fun p => strictN (eK gt pp pj f p (keyOf h)) fun K' =>
          strictN (gt (pj i)) fun T => mapK T K') = _
      rw [strictN_eq, strictN_eq, strictN_eq]
      obtain ⟨e1, e2⟩ := hpar i hin
      obtain ⟨hp, hj⟩ := hT.par_lt i hpos hin
      rw [e1] at hp
      rw [e2] at hj
      rw [ih (pp i) (by omega) (by omega) h, mapK_keyOf (hg _ hj),
        tabElt_succ gJ P (i := i) (by rw [e1]; exact hp), e1, e2, mul_assoc]

theorem keyOf_one : keyOf (1 : J) = pk5 bp := by
  unfold keyOf
  congr 1
  funext t
  rw [idx_one]

theorem conj_of_conjC {rep cls wo wd LT glob key gt pp pj : ℕ → ℕ} {k0 l : ℕ}
    {P : Array (ℕ × ℕ)} {Lt : Array (Array ℕ)} {lJ : ℕ → J}
    (hL : ∀ z < 32, RepE (LT z) (lJ z)) (hg : ∀ j < 3, RepE (gt j) (gJ j))
    (hT : TabData gJ P Lt nS 3) (hpar : ∀ i < nS, (P[i]!).1 = pp i ∧ (P[i]!).2 = pj i)
    (hkey : ∀ i < nS, key i = keyOf (tabElt gJ P i)) (hk0 : k0 = pk5 bp)
    (hglob : ∀ k < 4, glob k < nS)
    (h : conjC rep cls wo wd LT glob key gt pp pj k0 19683 l = true) :
    rep l < nS ∧ cls l < 4 ∧ wo l ≤ wo (l + 1) ∧
      (∀ t, wo l ≤ t → t < wo (l + 1) → wd t < 32) ∧
      wordJ lJ wd (wo l) (wo (l + 1) - wo l) * tabElt gJ P (rep l) =
        tabElt gJ P (glob (cls l)) * wordJ lJ wd (wo l) (wo (l + 1) - wo l) := by
  unfold conjC at h
  rw [sB_eq, sB_eq, sB_eq, sB_eq, sB_eq] at h
  simp only [bRec_and, Bool.and_eq_true, blt_iff, ble_iff, beq_iff] at h
  obtain ⟨hr, hk, hse, hwd, he⟩ := h
  have hr' : rep l < nS := by rw [nS_eq]; exact hr
  have hwd' : ∀ t, wo l ≤ t → t < wo (l + 1) → wd t < 32 := by
    intro t h1 h2
    have := CFSG.KS.allBlk_spec hwd (t - wo l) (by change t - wo l < wo (l + 1) - wo l; omega)
    rw [Nat.add_eq, Nat.add_sub_cancel' h1] at this
    exact (blt_iff _ _).1 this
  have hw : ∀ t, wo l ≤ t → t < wo l + (wo (l + 1) - wo l) → RepE (LT (wd t)) (lJ (wd t)) :=
    fun t h1 h2 => hL _ (hwd' t h1 (by omega))
  have hρ := hglob _ hk
  have e1 := wordK_keyOf (wo (l + 1) - wo l) (wo l) hw (tabElt gJ P (rep l))
  have e2 := wordK_keyOf (wo (l + 1) - wo l) (wo l) hw 1
  rw [mul_one, keyOf_one, ← hk0] at e2
  change wordK LT wd (wo (l + 1) - wo l) (wo l) (key (rep l)) =
    eK gt pp pj (glob (cls l) + 1) (glob (cls l))
      (wordK LT wd (wo (l + 1) - wo l) (wo l) k0) at he
  rw [hkey _ hr', e1, e2, eK_keyOf hg hT hpar _ _ (by omega) hρ] at he
  exact ⟨hr', hk, hse, hwd', eq_of_keyOf he⟩

end CFSG.KD.Fi22Cls

end

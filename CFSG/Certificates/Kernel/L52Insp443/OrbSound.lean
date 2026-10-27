module

public import CFSG.Certificates.Kernel.L52Insp443.Stab
import CFSG.Certificates.Kernel.Misc.GL52MatProved
import CFSG.Certificates.Kernel.Misc.GL52Sol
public import CFSG.Certificates.Kernel.L52Insp443.Cent

public section

set_option maxRecDepth 20000

namespace CFSG.KC.L52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.Literature.GL52

theorem letB_l52 (y : ℕ) (k : ℕ → Bool) : letB y k = k y := by
  cases y <;> rfl

theorem nthR_eq : ∀ (L : List Rec) (j : ℕ), nthR L j = L.getD j (0, 0, 0, 0, 0)
  | [], j => by simp [nthR]
  | x :: L, 0 => rfl
  | x :: L, j + 1 => by
    change nthR L j = _
    rw [nthR_eq L j]
    simp

theorem masksR_eq : ∀ L : List Rec, masksR L = L.map Prod.fst
  | [] => rfl
  | r :: L => by
    change r.1 :: masksR L = _
    rw [masksR_eq L, List.map_cons]

theorem genAt_eq (L : List Rec) (P : ℕ → ℕ → Bool) (s s' : ℕ) (r : Rec) (j : ℕ) :
    genAt L P s s' r j = CFSG.KC.Ord.andB (Nat.beq (actK s r.1) (nthR L j).1)
      (P (mmulK (mmulK (nthR L j).2.2.1 s) r.2.1) (mmulK (mmulK r.2.2.1 s') (nthR L j).2.1)) := by
  unfold genAt
  rcases nthR L j with ⟨a, b, c, d, e⟩
  rfl

theorem unitK_mcode (g : G) : unitK (mcode (g : Mat)) = true := by
  rw [unitK_iff, rankK_mcode, ← CFSG.KC.Misc.GLM.Ech.isUnit_iff_rank5]
  exact ⟨CFSG.KC.Misc.GLM.Pf.mcode_lt _, g.isUnit⟩

theorem gD_mcode (g : G) : gD (mcode (g : Mat)) = g :=
  kG_inj (mcode_gD (unitK_mcode g))

theorem gD_idK : gD idK = 1 := by
  rw [← kG_one]
  exact gD_mcode 1

theorem gD_inv {c c' : ℕ} (hc : unitK c = true) (hc' : unitK c' = true) (h : mmulK c' c = idK) :
    gD c' = (gD c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  apply kG_inj
  change mcode ((gD c' * gD c : G) : Mat) = mcode ((1 : G) : Mat)
  rw [kG_mul, mcode_gD hc, mcode_gD hc', h, kG_one]

theorem code3 (A B C : G) : mmulK (mmulK (mcode (A : Mat)) (mcode (B : Mat))) (mcode (C : Mat)) =
    mcode ((A * B * C : G) : Mat) := by
  rw [kG_mul, kG_mul]

theorem orbOK_parts {bs : List ℕ} {L : List Rec} {Pc : ℕ → ℕ → Bool} {sA sA' sB sB' : ℕ}
    (h : orbOK bs L Pc sA sA' sB sB' = true) :
    fixK bs = (nthR L 0).1 ∧ (nthR L 0).2.1 = idK ∧ (L.map Prod.fst).Nodup ∧
      ∀ r ∈ L, recOK (nthR L 0).1 L.length r = true ∧ genAt L Pc sA sA' r r.2.2.2.1 = true ∧
        genAt L Pc sB sB' r r.2.2.2.2 = true := by
  unfold orbOK at h
  rw [letB_l52] at h
  obtain ⟨h1, r2⟩ := and2 h
  obtain ⟨h2, r3⟩ := and2 r2
  obtain ⟨h3, h4⟩ := and2 r3
  refine ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, ?_, fun r hr => ?_⟩
  · rw [← masksR_eq]
    exact (nodupK_iff _).mp h3
  · obtain ⟨r1, r2⟩ := and2 ((allK_iff _ _).mp h4 r hr)
    exact ⟨r1, and2 r2⟩

theorem recOK_facts {F0 m : ℕ} {r : Rec} (hu : unitK r.2.1 = true) (hu' : unitK r.2.2.1 = true)
    (h : recOK F0 m r = true) :
    gD r.2.2.1 = (gD r.2.1)⁻¹ ∧ actG (gD r.2.1) F0 = r.1 ∧ r.2.2.2.1 < m ∧ r.2.2.2.2 < m := by
  unfold recOK at h
  obtain ⟨r1, r2⟩ := and2 h
  obtain ⟨r2, r3⟩ := and2 r2
  obtain ⟨r3, r4⟩ := and2 r3
  refine ⟨gD_inv hu hu' (Nat.eq_of_beq_eq_true r1), ?_, Nat.blt_eq.mp r3, Nat.blt_eq.mp r4⟩
  unfold actG
  rw [mcode_gD hu]
  exact Nat.eq_of_beq_eq_true r2

theorem step_codes {Pc : ℕ → ℕ → Bool} {Q : Subgroup G}
    (hP : ∀ y : G, Pc (mcode (y : Mat)) (mcode ((y⁻¹ : G) : Mat)) = true → y ∈ Q) (x : G)
    {Fr tr tr' Fq tq tq' : ℕ} (hr : unitK tr = true) (hr' : unitK tr' = true)
    (hq : unitK tq = true) (hq' : unitK tq' = true) (hri : gD tr' = (gD tr)⁻¹)
    (hqi : gD tq' = (gD tq)⁻¹) (h1 : Nat.beq (actK (mcode (x : Mat)) Fr) Fq = true)
    (h2 : Pc (mmulK (mmulK tq' (mcode (x : Mat))) tr)
      (mmulK (mmulK tr' (mcode ((x⁻¹ : G) : Mat))) tq) = true) :
    actG x Fr = Fq ∧ (gD tq)⁻¹ * (x * gD tr) ∈ Q := by
  refine ⟨Nat.eq_of_beq_eq_true h1, hP _ ?_⟩
  rw [← mcode_gD hq', ← mcode_gD hr, ← mcode_gD hr', ← mcode_gD hq, code3, code3, hqi,
    hri] at h2
  have e1 : (gD tq)⁻¹ * x * gD tr = (gD tq)⁻¹ * (x * gD tr) := mul_assoc _ _ _
  have e2 : (gD tr)⁻¹ * x⁻¹ * gD tq = ((gD tq)⁻¹ * (x * gD tr))⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  rw [e1, e2] at h2
  exact h2

@[expose] noncomputable def orbT (L : List Rec) (k : Fin L.length) : G := gD (L.get k).2.1

@[expose] noncomputable def orbF (L : List Rec) (k : Fin L.length) : ℕ := (L.get k).1

theorem nthR_get (L : List Rec) {j : ℕ} (hj : j < L.length) : nthR L j = L.get ⟨j, hj⟩ := by
  rw [nthR_eq, List.getD_eq_getElem _ _ hj]
  rfl

theorem rec_at {L : List Rec} {F0 : ℕ}
    (hU : ∀ r ∈ L, unitK r.2.1 = true ∧ unitK r.2.2.1 = true)
    (hrec : ∀ r ∈ L, recOK F0 L.length r = true) (k : Fin L.length) :
    unitK (L.get k).2.1 = true ∧ unitK (L.get k).2.2.1 = true ∧
      gD (L.get k).2.2.1 = (orbT L k)⁻¹ ∧ actG (orbT L k) F0 = orbF L k ∧
        (L.get k).2.2.2.1 < L.length ∧ (L.get k).2.2.2.2 < L.length := by
  have hm := List.get_mem L k
  have hu := hU _ hm
  have hf := recOK_facts (F0 := F0) (m := L.length) (r := L.get k) hu.1 hu.2 (hrec _ hm)
  rw [orbT.eq_1, orbF.eq_1]
  exact ⟨hu.1, hu.2, hf.1, hf.2.1, hf.2.2⟩

theorem gen_cover {L : List Rec} {F0 : ℕ} {Pc : ℕ → ℕ → Bool} {Q : Subgroup G}
    (hP : ∀ y : G, Pc (mcode (y : Mat)) (mcode ((y⁻¹ : G) : Mat)) = true → y ∈ Q)
    (hU : ∀ r ∈ L, unitK r.2.1 = true ∧ unitK r.2.2.1 = true)
    (hrec : ∀ r ∈ L, recOK F0 L.length r = true) (x : G) (sel : Rec → ℕ)
    (hsel : ∀ k : Fin L.length, sel (L.get k) < L.length)
    (hg : ∀ r ∈ L, genAt L Pc (mcode (x : Mat)) (mcode ((x⁻¹ : G) : Mat)) r (sel r) = true)
    (k : Fin L.length) :
    ∃ j, actG x (orbF L k) = orbF L j ∧ (orbT L j)⁻¹ * (x * orbT L k) ∈ Q := by
  have hj := hsel k
  obtain ⟨u1, u2, i1, -⟩ := rec_at hU hrec k
  obtain ⟨q1, q2, qi, -⟩ := rec_at hU hrec ⟨sel (L.get k), hj⟩
  have h := hg _ (List.get_mem L k)
  rw [genAt_eq, nthR_get L hj] at h
  obtain ⟨g1, g2⟩ := and2 h
  rw [orbT.eq_1] at i1 qi
  refine ⟨⟨_, hj⟩, ?_⟩
  simp only [orbT.eq_1, orbF.eq_1]
  exact step_codes (Fr := (L.get k).1) (tr := (L.get k).2.1) (tr' := (L.get k).2.2.1)
    (Fq := (L.get ⟨_, hj⟩).1) (tq := (L.get ⟨_, hj⟩).2.1) (tq' := (L.get ⟨_, hj⟩).2.2.1)
    hP x u1 u2 q1 q2 i1 qi g1 g2

theorem orb_cover {bs : List ℕ} {L : List Rec} {Pc : ℕ → ℕ → Bool} {a b : G} {Q : Subgroup G}
    (hP : ∀ y : G, Pc (mcode (y : Mat)) (mcode ((y⁻¹ : G) : Mat)) = true → y ∈ Q)
    (hU : ∀ r ∈ L, unitK r.2.1 = true ∧ unitK r.2.2.1 = true)
    (hall : ∀ r ∈ L, recOK (fixK bs) L.length r = true ∧
      genAt L Pc (mcode (a : Mat)) (mcode ((a⁻¹ : G) : Mat)) r r.2.2.2.1 = true ∧
        genAt L Pc (mcode (b : Mat)) (mcode ((b⁻¹ : G) : Mat)) r r.2.2.2.2 = true) :
    ∀ x ∈ ({a, b} : Set G), ∀ k, ∃ j, actG x (orbF L k) = orbF L j ∧
      (orbT L j)⁻¹ * (x * orbT L k) ∈ Q := by
  have hrec : ∀ r ∈ L, recOK (fixK bs) L.length r = true := fun r hr => (hall r hr).1
  rintro x (rfl | rfl) k
  · exact gen_cover hP hU hrec x (fun r => r.2.2.2.1)
      (fun k => (rec_at hU hrec k).2.2.2.2.1) (fun r hr => (hall r hr).2.1) k
  · exact gen_cover hP hU hrec x (fun r => r.2.2.2.2)
      (fun k => (rec_at hU hrec k).2.2.2.2.2) (fun r hr => (hall r hr).2.2) k

theorem orb_inj {L : List Rec} (hnd : (L.map Prod.fst).Nodup) : Function.Injective (orbF L) :=
  fun i j e => by
    have e' : (L.map Prod.fst)[i.1]'(by rw [List.length_map]; exact i.2) =
        (L.map Prod.fst)[j.1]'(by rw [List.length_map]; exact j.2) := by
      rw [List.getElem_map, List.getElem_map]
      exact e
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp e')

theorem orb_one {L : List Rec} (hm : 0 < L.length) (h : (nthR L 0).2.1 = idK) :
    orbT L ⟨0, hm⟩ = 1 := by
  rw [orbT.eq_1,← nthR_get L hm, h, gD_idK]

theorem orb_sound {bs : List ℕ} {L : List Rec} {Pc : ℕ → ℕ → Bool} {a b : G}
    (hs : Subgroup.closure ({a, b} : Set G) = ⊤) (hm : 0 < L.length)
    (horb : orbOK bs L Pc (mcode (a : Mat)) (mcode ((a⁻¹ : G) : Mat)) (mcode (b : Mat))
      (mcode ((b⁻¹ : G) : Mat)) = true)
    (hU : ∀ r ∈ L, unitK r.2.1 = true ∧ unitK r.2.2.1 = true) (Q : Subgroup G)
    (hP : ∀ y : G, Pc (mcode (y : Mat)) (mcode ((y⁻¹ : G) : Mat)) = true → y ∈ Q) :
    Nat.card G = L.length * Nat.card (stabK (fixK bs) (fixK_lt bs)) ∧
      stabK (fixK bs) (fixK_lt bs) ≤ Q := by
  obtain ⟨hF0, ht0, hnd, hall⟩ := orbOK_parts horb
  have hall' : ∀ r ∈ L, recOK (fixK bs) L.length r = true ∧
      genAt L Pc (mcode (a : Mat)) (mcode ((a⁻¹ : G) : Mat)) r r.2.2.2.1 = true ∧
        genAt L Pc (mcode (b : Mat)) (mcode ((b⁻¹ : G) : Mat)) r r.2.2.2.2 = true := by
    rw [hF0]
    exact hall
  have hrec : ∀ r ∈ L, recOK (fixK bs) L.length r = true := fun r hr => (hall' r hr).1
  have ht : ∀ k, actG (orbT L k) (fixK bs) = orbF L k := fun k => (rec_at hU hrec k).2.2.2.1
  have hcov := orb_cover hP hU hall'
  have h1 := orb_one hm ht0
  refine ⟨card_stabK (fixK_lt bs) (orbT L) (orbF L) ht hs (orb_inj hnd) (fun x hx k => ?_)
    ⟨⟨0, hm⟩, by rw [h1]; exact Subgroup.one_mem _⟩,
    stabK_le (fixK_lt bs) (orbT L) (orbF L) ht hs (orb_inj hnd) Q hcov h1⟩
  obtain ⟨j, hj, -⟩ := hcov x hx k
  exact ⟨j, hj⟩

end CFSG.KC.L52I

end

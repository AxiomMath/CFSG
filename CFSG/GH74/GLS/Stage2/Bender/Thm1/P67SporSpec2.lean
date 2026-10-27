module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporSpec

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier CFSG.Certificates Certificates.CF67

variable {n : ℕ}

theorem tbl_eq_iff_cf67 (hn : n < 2 ^ 32) (p q : Equiv.Perm (Fin n)) :
    tblEq n (toTable p) (toTable q) = true ↔ p = q :=
  tblEq_eq_iff_cf67 (rep_toTable hn p) (rep_toTable hn q)

theorem tbl_comp_iff_cf67 (hn : n < 2 ^ 32) (p q t : Equiv.Perm (Fin n)) :
    tblEq n (compT n (toTable p) (toTable q)) (toTable t) = true ↔ p * q = t :=
  tblEq_eq_iff_cf67 (Rep.compT (rep_toTable hn p) (rep_toTable hn q)) (rep_toTable hn t)

theorem nodup_of_cf67NodupT (hn : n < 2 ^ 32) :
    ∀ l : List (Equiv.Perm (Fin n)), cf67NodupT n (l.map toTable) = true → l.Nodup
  | [], _ => List.nodup_nil
  | p :: l, h => by
    simp only [List.map_cons, cf67NodupT, Bool.and_eq_true, List.all_eq_true, List.mem_map] at h
    refine List.nodup_cons.2 ⟨fun hp => ?_, nodup_of_cf67NodupT hn l h.2⟩
    have := h.1 (toTable p) ⟨p, hp, rfl⟩
    simp only [Bool.not_eq_true'] at this
    exact absurd ((tbl_eq_iff_cf67 hn p p).2 rfl) (by simp [this])

theorem cf67IsPair_of (hn : n < 2 ^ 32) {r : ℕ} {a b : Equiv.Perm (Fin n)} (ha : a ^ r = 1)
    (hb : b ^ r = 1) (ha1 : a ≠ 1) (hb1 : b ∉ Subgroup.zpowers a) (hab : a * b = b * a) :
    cf67IsPair n r (toTable a) (toTable b) = true := by
  have hpow : ∀ (x : Equiv.Perm (Fin n)), x ^ r = 1 → powFixW n [toTable x] r = true := fun x hx =>
    (powFixW_iff perm_faithful (List.Forall₂.cons (rep_toTable hn x) List.Forall₂.nil) r).2
      (by simpa using hx)
  simp only [cf67IsPair, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  refine ⟨⟨⟨⟨hpow a ha, hpow b hb⟩, ?_⟩, ?_⟩, ?_⟩
  · have h1 : ¬ tblEq n (toTable a) (idT n) = true := fun h =>
      ha1 ((tblEq_eq_iff_cf67 (rep_toTable hn a) (Rep.idT hn)).1 h)
    simpa using h1
  · intro i _
    have hrep := rep_powT hn (rep_toTable hn a) i
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    exact hb1 (Subgroup.mem_zpowers_iff.2 ⟨i, by
      have := (tblEq_eq_iff_cf67 (rep_toTable hn b) hrep).1 hc
      simpa [zpow_natCast] using this.symm⟩)
  · exact (tbl_comp_iff_cf67 hn a b (b * a)).2 hab |> fun h => by
      simpa [commT] using (tblEq_eq_iff_cf67 (Rep.compT (rep_toTable hn a) (rep_toTable hn b))
        (Rep.compT (rep_toTable hn b) (rep_toTable hn a))).2 hab

theorem cf67_gen_data_tss (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG : Q.originalSubgroup = G)
    {gG : List (Equiv.Perm (Fin n))} (hgG : ∀ g ∈ gG, g ∈ G) {r k t : ℕ} (_hr : r.Prime)
    {Pw : List (List ℤ)} {Ew : List (List ℤ × List ℤ)} {Tss : List (List Table)}
    (hTss : levelTables Q = Tss)
    (h : cf67GenOKT n Q.orderCertificate r k t Tss (Pw.map fun w => toTable (evalCodes gG w))
      (Ew.map fun e => (toTable (evalCodes gG e.1), toTable (evalCodes gG e.2))) = true) :
    ∃ (P : Subgroup G) (Es : Set (G × G)), Nat.card P = r ^ k ∧ ¬ r ^ (k + 1) ∣ Nat.card G ∧
      (∀ a b : G, a ∈ P → b ∈ P → a ^ r = 1 → b ^ r = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a →
        a * b = b * a → ∃ e ∈ Es, e.1 ∈ Subgroup.closure ({a, b} : Set G) ∧
          e.2 ∈ Subgroup.closure ({a, b} : Set G)) ∧
      (∀ e ∈ Es, ∀ g : G, g * e.1 = e.1 * g → g * e.2 = e.2 * g →
        g ^ (2 ^ t * r ^ k) = 1) := by
  classical
  have hcardG : Nat.card G = Q.orderCertificate := by
    rw [← hG]; exact (Q.orderCertificate_eq_card hQ).symm
  obtain ⟨Lg, hLg⟩ : ∃ Lg : List (Equiv.Perm (Fin n)), Lg = Pw.map (evalCodes gG) := ⟨_, rfl⟩
  have hLgG : ∀ p ∈ Lg, p ∈ G := by
    intro p hp
    rw [hLg] at hp
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hp
    exact evalCodes_mem G hgG w
  have hPT : (Pw.map fun w => toTable (evalCodes gG w)) = Lg.map toTable := by
    rw [hLg, List.map_map]; rfl
  simp only [cf67GenOKT, hPT, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hlen, hnodup⟩, hclosed⟩, hord⟩, hcover⟩, hcomm⟩ := h
  have hnd : Lg.Nodup := nodup_of_cf67NodupT hn Lg hnodup
  simp only [cf67CoverT, List.all_eq_true] at hcover
  simp only [cf67ClosedT, Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_map] at hclosed
  obtain ⟨⟨hone, hinv⟩, hmul⟩ := hclosed
  have h1 : (1 : Equiv.Perm (Fin n)) ∈ Lg := by
    obtain ⟨t, ⟨q, hq, rfl⟩, ht⟩ := hone
    have := (tblEq_eq_iff_cf67 (Rep.idT hn) (rep_toTable hn q)).1 ht
    rw [this]; exact hq
  have hmulL : ∀ p ∈ Lg, ∀ q ∈ Lg, p * q ∈ Lg := by
    intro p hp q hq
    obtain ⟨t, ⟨u, hu, rfl⟩, ht⟩ := hmul (toTable p) ⟨p, hp, rfl⟩ (toTable q) ⟨q, hq, rfl⟩
    have := (tbl_comp_iff_cf67 hn p q u).1 ht
    rw [this]; exact hu
  have hinvL : ∀ p ∈ Lg, p⁻¹ ∈ Lg := by
    intro p hp
    obtain ⟨t, ⟨u, hu, rfl⟩, ht⟩ := hinv (toTable p) ⟨p, hp, rfl⟩
    have := (tblEq_eq_iff_cf67 (Rep.compT (rep_toTable hn p) (rep_toTable hn u)) (Rep.idT hn)).1 ht
    have hu' : u = p⁻¹ := eq_inv_of_mul_eq_one_right this
    rw [← hu']; exact hu
  let P : Subgroup G :=
    { carrier := {g | (g : Equiv.Perm (Fin n)) ∈ Lg}
      mul_mem' := fun {a b} ha hb => by simpa using hmulL _ ha _ hb
      one_mem' := by simpa using h1
      inv_mem' := fun {a} ha => by simpa using hinvL _ ha }
  have hPmem : ∀ g : G, g ∈ P ↔ (g : Equiv.Perm (Fin n)) ∈ Lg := fun g => Iff.rfl
  have hcardP : Nat.card P = r ^ k := by
    have e : Nat.card P = Nat.card {p : Equiv.Perm (Fin n) // p ∈ Lg} :=
      Nat.card_congr
        { toFun := fun g => ⟨g.1.1, g.2⟩
          invFun := fun p => ⟨⟨p.1, hLgG p.1 p.2⟩, p.2⟩
          left_inv := fun g => rfl
          right_inv := fun p => rfl }
    rw [e, Nat.card_eq_fintype_card, Fintype.card_of_subtype Lg.toFinset
      (fun x => List.mem_toFinset),
      List.toFinset_card_of_nodup hnd]
    simpa using hlen
  refine ⟨P, {e | ∃ w ∈ Ew, (e.1 : Equiv.Perm (Fin n)) = evalCodes gG w.1 ∧
    (e.2 : Equiv.Perm (Fin n)) = evalCodes gG w.2}, hcardP, ?_, ?_, ?_⟩
  · rw [hcardG]
    intro hd
    exact hord (Nat.mod_eq_zero_of_dvd hd)
  · intro a b ha hb har hbr ha1 hb1 hab
    have haL : (a : Equiv.Perm (Fin n)) ∈ Lg := ha
    have hbL : (b : Equiv.Perm (Fin n)) ∈ Lg := hb
    have har' : (a : Equiv.Perm (Fin n)) ^ r = 1 := by simpa using congrArg Subtype.val har
    have hbr' : (b : Equiv.Perm (Fin n)) ^ r = 1 := by simpa using congrArg Subtype.val hbr
    have ha1' : (a : Equiv.Perm (Fin n)) ≠ 1 := fun h => ha1 (Subtype.ext (by simpa using h))
    have hb1' : (b : Equiv.Perm (Fin n)) ∉ Subgroup.zpowers (a : Equiv.Perm (Fin n)) := by
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact hb1 (Subgroup.mem_zpowers_iff.2 ⟨m, Subtype.ext (by simpa using hm)⟩)
    have hab' : (a : Equiv.Perm (Fin n)) * b = b * a := by simpa using congrArg Subtype.val hab
    have hpair := cf67IsPair_of hn har' hbr' ha1' hb1' hab'
    have hc := hcover (toTable (a : Equiv.Perm (Fin n)))
      (List.mem_map.2 ⟨(a : Equiv.Perm (Fin n)), haL, rfl⟩) (toTable (b : Equiv.Perm (Fin n)))
      (List.mem_map.2 ⟨(b : Equiv.Perm (Fin n)), hbL, rfl⟩)
    rw [hpair] at hc
    simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_map, Bool.and_eq_true] at hc
    obtain ⟨_, ⟨w, hw, rfl⟩, h1, h2⟩ := hc
    have hmemgen : ∀ p : Equiv.Perm (Fin n),
        (∃ x ∈ cf67Gen n r (toTable (a : Equiv.Perm (Fin n))) (toTable (b : Equiv.Perm (Fin n))),
          tblEq n (toTable p) x = true) →
        ∃ i j : ℕ, p = (a : Equiv.Perm (Fin n)) ^ i * (b : Equiv.Perm (Fin n)) ^ j := by
      intro p hx
      obtain ⟨t, ht', ht⟩ := hx
      simp only [cf67Gen, List.mem_flatMap, List.mem_map, List.mem_range] at ht'
      obtain ⟨i, -, j, -, rfl⟩ := ht'
      have hrep := Rep.compT (rep_powT hn (rep_toTable hn (a : Equiv.Perm (Fin n))) i)
        (rep_powT hn (rep_toTable hn (b : Equiv.Perm (Fin n))) j)
      exact ⟨i, j, (tblEq_eq_iff_cf67 (rep_toTable hn p) hrep).1 ht⟩
    have hcl : ∀ x : G, ∀ ij : ℕ × ℕ, (x : Equiv.Perm (Fin n)) =
        (a : Equiv.Perm (Fin n)) ^ ij.1 * (b : Equiv.Perm (Fin n)) ^ ij.2 →
        x ∈ Subgroup.closure ({a, b} : Set G) := by
      intro x ij hx
      have : x = a ^ ij.1 * b ^ ij.2 := Subtype.ext (by simpa using hx)
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
        (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
    refine ⟨(⟨evalCodes gG w.1, evalCodes_mem G hgG w.1⟩, ⟨evalCodes gG w.2,
      evalCodes_mem G hgG w.2⟩),
      ⟨w, hw, rfl, rfl⟩, ?_, ?_⟩
    · obtain ⟨i, j, hij⟩ := hmemgen _ h1
      exact hcl _ (i, j) hij
    · obtain ⟨i, j, hij⟩ := hmemgen _ h2
      exact hcl _ (i, j) hij
  · rintro e ⟨w, hw, he1, he2⟩ g hg1 hg2
    have hall := hcomm (toTable (evalCodes gG w.1), toTable (evalCodes gG w.2))
      (List.mem_map.2 ⟨w, hw, rfl⟩)
    have hgmem : g.1 ∈ ((enumeration Q).filter fun h => decide (evalCodes gG w.1 * h =
        h * evalCodes gG w.1 ∧ evalCodes gG w.2 * h = h * evalCodes gG w.2)).reverse := by
      rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff Q hQ, hG]
      refine ⟨g.2, ?_, ?_⟩
      · rw [← he1]; exact (congrArg Subtype.val hg1).symm
      · rw [← he2]; exact (congrArg Subtype.val hg2).symm
    obtain ⟨T, hT, hTg⟩ := exists_of_mem_right_forall₂'
      (forall₂_commAllT hn Q hTss (rep_toTable hn (evalCodes gG w.1))
        (rep_toTable hn (evalCodes gG w.2))) hgmem
    have hpow := (powFixW_iff perm_faithful (List.Forall₂.cons hTg List.Forall₂.nil)
      (2 ^ t * r ^ k)).1
      (hall T hT)
    exact Subtype.ext (by simpa using hpow)

theorem cf67_gen_data (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG : Q.originalSubgroup = G)
    {gG : List (Equiv.Perm (Fin n))} (hgG : ∀ g ∈ gG, g ∈ G) {r k t : ℕ} (_hr : r.Prime)
    {Pw : List (List ℤ)} {Ew : List (List ℤ × List ℤ)}
    (h : cf67GenOK n Q gG r k t Pw Ew = true) :
    ∃ (P : Subgroup G) (Es : Set (G × G)), Nat.card P = r ^ k ∧ ¬ r ^ (k + 1) ∣ Nat.card G ∧
      (∀ a b : G, a ∈ P → b ∈ P → a ^ r = 1 → b ^ r = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a →
        a * b = b * a → ∃ e ∈ Es, e.1 ∈ Subgroup.closure ({a, b} : Set G) ∧
          e.2 ∈ Subgroup.closure ({a, b} : Set G)) ∧
      (∀ e ∈ Es, ∀ g : G, g * e.1 = e.1 * g → g * e.2 = e.2 * g →
        g ^ (2 ^ t * r ^ k) = 1) :=
  cf67_gen_data_tss hn Q hQ hG hgG _hr rfl h

end CFSG.GH74.GLS.Stage2.Bender.Thm1

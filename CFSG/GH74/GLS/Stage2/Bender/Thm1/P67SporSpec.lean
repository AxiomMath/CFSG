module

public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import Certificates.Data.CF67Check

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier CFSG.Certificates Certificates.CF67

variable {n : ℕ}

theorem exists_of_mem_right_forall₂' {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, b, hb => by simp at hb
  | _, _, .cons hab hr, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := exists_of_mem_right_forall₂' hr hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem tblEq_eq_iff_cf67 {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g)
  (hT : Rep n T h) :
    tblEq n S T = true ↔ g = h :=
  ⟨fun e => rep_unique hS (rep_of_tblEq hT e), by
    rintro rfl
    exact tblEq_iff.2 fun i hi => (hS i hi).trans (hT i hi).symm⟩

theorem rep_powT (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)} (hT : Rep n T g) :
    ∀ k : ℕ, Rep n (cf67PowT n T k) (g ^ k)
  | 0 => by simpa [cf67PowT] using Rep.idT hn
  | k + 1 => by simpa [cf67PowT, pow_succ'] using Rep.compT hT (rep_powT hn hT k)

theorem forall₂_commAllT (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) {Tss : List (List Table)}
    (hTss : levelTables Q = Tss) {aT bT : Table} {a b : Equiv.Perm (Fin n)} (ha : Rep n aT a)
    (hb : Rep n bT b) :
    List.Forall₂ (Rep n) (commAllT n Tss aT bT)
      ((enumeration Q).filter fun h => decide (a * h = h * a ∧ b * h = h * b)).reverse := by
  classical
  subst hTss
  have hcomm : ∀ {x : Table} {xg : Equiv.Perm (Fin n)} {c : Table} {cg : Equiv.Perm (Fin n)},
      Rep n x xg → Rep n c cg → (commT n x c = true ↔ xg * cg = cg * xg) := by
    intro x xg c cg hx hc
    exact tblEq_eq_iff_cf67 (Rep.compT hx hc) (Rep.compT hc hx)
  have h := filterProducts_spec
    (P := fun h : Equiv.Perm (Fin n) => a * h = h * a ∧ b * h = h * b)
    (f := fun T => commT n aT T && commT n bT T)
    (fun T g hT => by
      rw [Bool.and_eq_true, hcomm ha hT, hcomm hb hT])
    (forall₂_levelTables hn Q) (Rep.idT hn) (acc := []) (accG := []) List.Forall₂.nil
  simp only [one_mul, List.map_id', List.append_nil] at h
  exact h

theorem cf67_data (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {G : Subgroup (Equiv.Perm (Fin n))} (hG : Q.originalSubgroup = G)
    {gG : List (Equiv.Perm (Fin n))} (hgG : ∀ g ∈ gG, g ∈ G) {r : ℕ} (hr : r.Prime)
    {wa wb : List ℤ} (h : cf67OK n Q gG r wa wb = true) :
    ∃ a0 b0 : G, a0 ^ r = 1 ∧ b0 ^ r = 1 ∧ a0 * b0 = b0 * a0 ∧ a0 ≠ 1 ∧
      b0 ∉ Subgroup.zpowers a0 ∧ ¬ r ^ 3 ∣ Nat.card G ∧
      ∀ g : G, g * a0 = a0 * g → g * b0 = b0 * g → g ^ (r ^ 2) = 1 := by
  classical
  have := Fact.mk hr
  have hcardG : Nat.card G = Q.orderCertificate := by
    rw [← hG]; exact (Q.orderCertificate_eq_card hQ).symm
  have hgG' : ∀ g ∈ gG, g ∈ Q.originalSubgroup := by rw [hG]; exact hgG
  obtain ⟨aG, haG⟩ : ∃ aG, aG = evalCodes gG wa := ⟨_, rfl⟩
  obtain ⟨bG, hbG⟩ : ∃ bG, bG = evalCodes gG wb := ⟨_, rfl⟩
  have haMem : aG ∈ G := by rw [haG]; exact evalCodes_mem G hgG wa
  have hbMem : bG ∈ G := by rw [hbG]; exact evalCodes_mem G hgG wb
  have haRep := rep_toTable hn aG
  have hbRep := rep_toTable hn bG
  simp only [cf67OK, cf67OKT, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at h
  rw [← haG, ← hbG] at h
  obtain ⟨⟨⟨⟨⟨⟨hpa, hpb⟩, hcom⟩, hna⟩, hbn⟩, hcube⟩, hall⟩ := h
  have hna' : ¬ tblEq n (toTable aG) (idT n) = true := by simpa using hna
  have ha : aG ^ r = 1 := by
    have := (powFixW_iff perm_faithful (List.Forall₂.cons haRep List.Forall₂.nil) r).1 hpa
    simpa using this
  have hb : bG ^ r = 1 := by
    have := (powFixW_iff perm_faithful (List.Forall₂.cons hbRep List.Forall₂.nil) r).1 hpb
    simpa using this
  have hab : aG * bG = bG * aG := eq_of_commT haRep hbRep hcom
  have ha1 : aG ≠ 1 := fun h1 => hna' ((tblEq_eq_iff_cf67 haRep (Rep.idT hn)).2 h1)
  have hb1 : bG ∉ Subgroup.zpowers aG := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hr0 : (0 : ℤ) < r := by exact_mod_cast hr.pos
    have hord : orderOf aG = r := orderOf_eq_prime ha ha1
    have h0 : 0 ≤ k % (r : ℤ) := Int.emod_nonneg k hr0.ne'
    have hlt : k % (r : ℤ) < r := Int.emod_lt_of_pos k hr0
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = k % (r : ℤ) := ⟨(k % (r : ℤ)).toNat, Int.toNat_of_nonneg h0⟩
    have hmr : m < r := by omega
    have hkm : aG ^ k = aG ^ m := by
      have e1 := zpow_mod_orderOf aG k
      rw [hord] at e1
      rw [← e1, ← hm, zpow_natCast]
    have heq : tblEq n (toTable bG) (cf67PowT n (toTable aG) m) = true :=
      (tblEq_eq_iff_cf67 hbRep (rep_powT hn haRep m)).2 (hk.symm.trans hkm)
    have hh := hbn m (List.mem_range.2 hmr)
    rw [heq] at hh
    exact absurd hh (by simp)
  refine ⟨⟨aG, haMem⟩, ⟨bG, hbMem⟩, Subtype.ext (by simpa using ha), Subtype.ext
    (by simpa using hb),
    Subtype.ext (by simpa using hab), fun h1 => ha1
    (by simpa using congrArg Subtype.val h1), ?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact hb1 (Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩)
  · rw [hcardG]
    intro hd
    exact hcube (Nat.mod_eq_zero_of_dvd hd)
  · intro g hga hgb
    have hgmem : g.1 ∈ ((enumeration Q).filter
        fun h => decide (aG * h = h * aG ∧ bG * h = h * bG)).reverse := by
      rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff Q hQ, hG]
      refine ⟨g.2, ?_, ?_⟩
      · exact (congrArg Subtype.val hga).symm
      · exact (congrArg Subtype.val hgb).symm
    obtain ⟨T, hT, hTg⟩ := exists_of_mem_right_forall₂'
      (forall₂_commAllT hn Q rfl haRep hbRep) hgmem
    have hpow := (powFixW_iff perm_faithful (List.Forall₂.cons hTg List.Forall₂.nil) (r ^ 2)).1
      (hall T hT)
    exact Subtype.ext (by simpa using hpow)

end CFSG.GH74.GLS.Stage2.Bender.Thm1

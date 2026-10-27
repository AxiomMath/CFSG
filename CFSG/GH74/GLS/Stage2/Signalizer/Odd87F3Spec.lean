module

public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import Certificates.Data.Odd87F3Check
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87F3S
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.Schreier CFSG.Certificates Certificates.Odd87F3

section Lists

theorem exists_of_mem_right_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b : β}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .nil, b, hb => by simp at hb
  | _, _, .cons hab hr, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨a, ha, h⟩ := exists_of_mem_right_forall₂ hr hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

theorem exists_of_mem_left_forall₂ {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, a, ha => by simp at ha
  | _, _, .cons hab hr, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, h⟩ := exists_of_mem_left_forall₂ hr ha
      exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

end Lists

variable {n : ℕ}

theorem tblEq_eq_iff {S T : Table} {g h : Equiv.Perm (Fin n)} (hS : Rep n S g) (hT : Rep n T h) :
    tblEq n S T = true ↔ g = h :=
  ⟨fun e => rep_unique hS (rep_of_tblEq hT e), by
    rintro rfl
    exact tblEq_iff.2 fun i hi => (hS i hi).trans (hT i hi).symm⟩

theorem forall₂_candAllT (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) {Tss : List (List Table)}
    (hTss : levelTables Q = Tss) {uT : Table} {u : Equiv.Perm (Fin n)} (hu : Rep n uT u) :
    List.Forall₂ (Rep n) (candAllT n Tss uT)
      ((enumeration Q).filter fun h => decide ((u * h) * (u * h) = 1)).reverse := by
  subst hTss
  have h := filterProducts_spec
    (P := fun h : Equiv.Perm (Fin n) => (u * h) * (u * h) = 1)
    (f := fun T => let ux := compT n uT T; tblEq n (compT n ux ux) (idT n))
    (fun T g hT => by
      have hux := Rep.compT hu hT
      have hsq := Rep.compT hux hux
      rw [tblEq_eq_iff hsq (Rep.idT hn)])
    (forall₂_levelTables hn Q) (Rep.idT hn) (acc := []) (accG := []) List.Forall₂.nil
  simp only [one_mul, List.map_id', List.append_nil] at h
  exact h

theorem not_mem_pGroup_of_pow_ne_one {M : Type*} [Group M] {G N : Subgroup M} {p k : ℕ} [Fact p.Prime]
    (hk : ¬ p ^ (k + 1) ∣ Nat.card G) (hN : IsPGroup p ↥N) {z : M} (hzN : z ∈ N) (hzG : z ∈ G)
    (hz : z ^ (p ^ k) ≠ 1) : False := by
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hN) ⟨z, hzN⟩
  have hj' : orderOf z = p ^ j := by rwa [Subgroup.orderOf_mk] at hj
  have hdvd : orderOf z ∣ Nat.card G := by
    have := orderOf_dvd_natCard (⟨z, hzG⟩ : ↥G)
    rwa [Subgroup.orderOf_mk] at this
  rw [hj'] at hdvd
  have hjk : j ≤ k := by
    by_contra hlt
    exact hk ((pow_dvd_pow p (by omega : k + 1 ≤ j)).trans hdvd)
  apply hz
  rw [← orderOf_dvd_iff_pow_eq_one, hj']
  exact pow_dvd_pow p hjk

theorem f3S_core' {G : Subgroup (Equiv.Perm (Fin n))} {u : Equiv.Perm (Fin n)} (hu2 : u * u = 1)
    {p N : ℕ} (hp : p.Prime) (hk : ¬ p ^ (N + 1) ∣ Nat.card G) (ogP : List (Equiv.Perm (Fin n)))
    (hogG : ∀ g ∈ ogP, g ∈ G) (hogC : ∀ g ∈ ogP, u * g = g * u)
    (hogO : ∀ g ∈ ogP, Odd (orderOf g)) (WT : List (Table × Table))
    (hWT : List.Forall₂ (fun (w : Table × Table) (g : Equiv.Perm (Fin n)) =>
      Rep n w.1 g ∧ Rep n w.2 g⁻¹) WT ogP) (cands : List Table)
    (hcov : ∀ x ∈ G, orderOf x = p → u * x * u⁻¹ = x⁻¹ → ∃ T ∈ cands, Rep n T x)
    (hcheck : ∀ T ∈ cands, (!ordTest n p T || witnessOK n (p ^ N) WT T) = true) :
    F3S G u p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro x hxG hxo hxu hpg
  obtain ⟨T, hT, hTx⟩ := hcov x hxG hxo hxu
  have hw := hcheck T hT
  have hTo : ordTest n p T = true := (ordTest_iff perm_faithful hTx hp.pos).2 hxo
  rw [hTo] at hw
  simp only [Bool.not_true, Bool.false_or] at hw
  set S : Set (Equiv.Perm (Fin n)) := {y | y ∈ G ∧ u * y = y * u ∧ Odd (orderOf y)} with hS
  have hogS : ∀ g ∈ ogP, g ∈ Subgroup.closure S := fun g hg =>
    Subgroup.subset_closure ⟨hogG g hg, hogC g hg, hogO g hg⟩
  set N' := Subgroup.closure {w : Equiv.Perm (Fin n) | ∃ c ∈ Subgroup.closure S, w = c * x * c⁻¹}
    with hNdef
  have hxN : x ∈ N' := Subgroup.subset_closure ⟨1, Subgroup.one_mem _, by simp⟩
  have hconjN : ∀ g ∈ ogP, g * x * g⁻¹ ∈ N' := fun g hg =>
    Subgroup.subset_closure ⟨g, hogS g hg, rfl⟩
  have hconjG : ∀ g ∈ ogP, g * x * g⁻¹ ∈ G := fun g hg =>
    G.mul_mem (G.mul_mem (hogG g hg) hxG) (G.inv_mem (hogG g hg))
  have key : ∀ z, z ∈ N' → z ∈ G → z ^ (p ^ N) ≠ 1 → False := fun z hzN hzG hz =>
    not_mem_pGroup_of_pow_ne_one hk hpg hzN hzG hz
  simp only [witnessOK, Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at hw
  rcases hw with ⟨a, ha, hfa⟩ | ⟨a, ha, b, hb, hfb⟩
  · obtain ⟨g, hg, hra⟩ := exists_of_mem_left_forall₂ hWT ha
    have hF : List.Forall₂ (Rep n) [T, a.1, T, a.2] [x, g, x, g⁻¹] :=
      .cons hTx (.cons hra.1 (.cons hTx (.cons hra.2 .nil)))
    have h1 := powFixW_iff perm_faithful hF (p ^ N)
    have hne : [x, g, x, g⁻¹].prod ^ (p ^ N) ≠ 1 := fun hc => by
      have := h1.2 hc
      rw [hfa] at this
      exact Bool.false_ne_true this
    have hz : [x, g, x, g⁻¹].prod = x * (g * x * g⁻¹) := by
      simp only [List.prod_cons, List.prod_nil]; group
    rw [hz] at hne
    exact key _ (N'.mul_mem hxN (hconjN g hg)) (G.mul_mem hxG (hconjG g hg)) hne
  · obtain ⟨g₁, hg₁, hr₁⟩ := exists_of_mem_left_forall₂ hWT ha
    obtain ⟨g₂, hg₂, hr₂⟩ := exists_of_mem_left_forall₂ hWT hb
    have hF : List.Forall₂ (Rep n) [T, a.1, T, a.2, b.1, T, b.2] [x, g₁, x, g₁⁻¹, g₂, x, g₂⁻¹] :=
      .cons hTx (.cons hr₁.1 (.cons hTx (.cons hr₁.2 (.cons hr₂.1 (.cons hTx (.cons hr₂.2 .nil))))))
    have h1 := powFixW_iff perm_faithful hF (p ^ N)
    have hne : [x, g₁, x, g₁⁻¹, g₂, x, g₂⁻¹].prod ^ (p ^ N) ≠ 1 := fun hc => by
      have := h1.2 hc
      rw [hfb] at this
      exact Bool.false_ne_true this
    have hz : [x, g₁, x, g₁⁻¹, g₂, x, g₂⁻¹].prod = (x * (g₁ * x * g₁⁻¹)) * (g₂ * x * g₂⁻¹) := by
      simp only [List.prod_cons, List.prod_nil]; group
    rw [hz] at hne
    exact key _ (N'.mul_mem (N'.mul_mem hxN (hconjN g₁ hg₁)) (hconjN g₂ hg₂))
      (G.mul_mem (G.mul_mem hxG (hconjG g₁ hg₁)) (hconjG g₂ hg₂)) hne

theorem f3S_core (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {Tss : List (List Table)} (hTss : levelTables Q = Tss) {uT : Table} {u : Equiv.Perm (Fin n)}
    (hu : Rep n uT u) (hu2 : u * u = 1) {p N : ℕ}
    (hp : p.Prime)
    (hk : ¬ p ^ (N + 1) ∣ Nat.card Q.originalSubgroup) (ogP : List (Equiv.Perm (Fin n)))
    (hogG : ∀ g ∈ ogP, g ∈ Q.originalSubgroup) (hogC : ∀ g ∈ ogP, u * g = g * u)
    (hogO : ∀ g ∈ ogP, Odd (orderOf g)) (WT : List (Table × Table))
    (hWT : List.Forall₂ (fun (w : Table × Table) (g : Equiv.Perm (Fin n)) =>
      Rep n w.1 g ∧ Rep n w.2 g⁻¹) WT ogP)
    (hcheck : ∀ T ∈ candAllT n Tss uT, (!ordTest n p T || witnessOK n (p ^ N) WT T) = true) :
    F3S Q.originalSubgroup u p := by
  classical
  refine f3S_core' hu2 hp hk ogP hogG hogC hogO WT hWT (candAllT n Tss uT) ?_ hcheck
  intro x hxG hxo hxu
  have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  have hxsq : (u * x) * (u * x) = 1 := by
    have h1 : u * x * u = x⁻¹ := by
      have := hxu
      rw [hu1] at this
      exact this
    calc (u * x) * (u * x) = (u * x * u) * x := by group
      _ = 1 := by rw [h1]; group
  have hxmem : x ∈ ((enumeration Q).filter fun h => decide ((u * h) * (u * h) = 1)).reverse := by
    rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_enumeration_iff Q hQ]
    exact ⟨hxG, hxsq⟩
  obtain ⟨T, hT, hTx⟩ := exists_of_mem_right_forall₂ (forall₂_candAllT hn Q hTss hu) hxmem
  exact ⟨T, hT, hTx⟩

theorem f3S_of_rowOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gG : List (Equiv.Perm (Fin n))} (hgG : ∀ g ∈ gG, g ∈ Q.originalSubgroup)
    {u : Equiv.Perm (Fin n)} {r : Row} (hp : r.prime.Prime)
    (h : rowOK n Q gG u (candAll n Q (toTable u)) r = true) : F3S Q.originalSubgroup u r.prime := by
  classical
  set G := Q.originalSubgroup with hG
  set og := r.oddWords.map (evalCodes gG) with hog
  simp only [rowOK, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hu2T, hodd⟩, hord⟩, hogT⟩, hcand⟩ := h
  have hu2 : u * u = 1 := by
    have := Rep.compT (rep_toTable hn u) (rep_toTable hn u)
    exact (tblEq_eq_iff this (Rep.idT hn)).1 hu2T
  have hcardG : Nat.card G = Q.orderCertificate := (Q.orderCertificate_eq_card hQ).symm
  have hk : ¬ r.prime ^ (r.pexp + 1) ∣ Nat.card G := by
    rw [hcardG]
    intro hd
    exact hord (Nat.mod_eq_zero_of_dvd hd)
  have hogG : ∀ g ∈ og, g ∈ G := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact evalCodes_mem G hgG w
  have hogC : ∀ g ∈ og, u * g = g * u := fun g hg =>
    eq_of_commT (rep_toTable hn u) (rep_toTable hn g) (hogT g hg).1
  have hogO : ∀ g ∈ og, Odd (orderOf g) := by
    intro g hg
    have h1 := (powFixW_iff perm_faithful (List.Forall₂.cons (rep_toTable hn g) List.Forall₂.nil)
      r.oddExp).1 (hogT g hg).2
    simp only [List.prod_cons, List.prod_nil, mul_one] at h1
    exact Odd.of_dvd_nat (Nat.odd_iff.2 hodd) (orderOf_dvd_of_pow_eq_one h1)
  refine f3S_core hn Q hQ rfl (rep_toTable hn u) hu2 hp hk og hogG hogC hogO (og.map fun g => (toTable g, toTable g⁻¹)) ?_
    hcand
  rw [List.forall₂_map_left_iff]
  exact List.forall₂_same.2 fun g _ => ⟨rep_toTable hn g, rep_toTable hn g⁻¹⟩


section TableLevel

theorem forall₂_getD {α β : Type*} {R : α → β → Prop} {d₁ : α} {d₂ : β} (hd : R d₁ d₂) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i : ℕ, R (l₁.getD i d₁) (l₂.getD i d₂)
  | _, _, .nil, i => by simpa using hd
  | _, _, .cons hab hr, i => by
    cases i with
    | zero => simpa using hab
    | succ i => simpa using forall₂_getD hd hr i

theorem getD_map_inv (gG : List (Equiv.Perm (Fin n))) (i : ℕ) :
    (gG.map fun g => g⁻¹).getD i (1 : Equiv.Perm (Fin n))⁻¹ = (gG.getD i 1)⁻¹ := by
  induction gG generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i => simpa only [List.map_cons, List.getD_cons_succ] using ih i

theorem rep_evalT (hn : n < 2 ^ 32) {gT gIT : List Table} {gG : List (Equiv.Perm (Fin n))}
    (h1 : List.Forall₂ (Rep n) gT gG) (h2 : List.Forall₂ (Rep n) gIT (gG.map fun g => g⁻¹))
    (w : List ℤ) : Rep n (evalT n gT gIT w) (evalCodes gG w) := by
  induction w with
  | nil => exact Rep.idT hn
  | cons z w ih =>
    simp only [evalT, evalCodes]
    refine Rep.compT ?_ ih
    split_ifs
    · exact forall₂_getD (Rep.idT hn) h1 _
    · have h3 := forall₂_getD (d₁ := idT n) (d₂ := (1 : Equiv.Perm (Fin n))⁻¹)
        (by simpa using Rep.idT hn) h2 ((-z).toNat - 1)
      rwa [getD_map_inv] at h3

theorem commute_evalCodes {gG : List (Equiv.Perm (Fin n))} {u : Equiv.Perm (Fin n)}
    (h : ∀ g ∈ gG, u * g = g * u) (w : List ℤ) : u * evalCodes gG w = evalCodes gG w * u := by
  induction w with
  | nil => simp [evalCodes]
  | cons z w ih =>
    have hget : ∀ k, u * gG.getD k 1 = gG.getD k 1 * u := fun k => by
      rw [List.getD_eq_getElem?_getD]
      cases hk : gG[k]? with
      | none => simp
      | some g => exact h g (List.mem_of_getElem? hk)
    simp only [evalCodes]
    have hl : u * (if 0 < z then gG.getD (z.toNat - 1) 1 else (gG.getD ((-z).toNat - 1) 1)⁻¹) =
        (if 0 < z then gG.getD (z.toNat - 1) 1 else (gG.getD ((-z).toNat - 1) 1)⁻¹) * u := by
      split_ifs
      · exact hget _
      · have := hget ((-z).toNat - 1)
        calc u * (gG.getD ((-z).toNat - 1) 1)⁻¹ = (gG.getD ((-z).toNat - 1) 1)⁻¹ *
            (gG.getD ((-z).toNat - 1) 1 * u) * (gG.getD ((-z).toNat - 1) 1)⁻¹ := by group
          _ = (gG.getD ((-z).toNat - 1) 1)⁻¹ * (u * gG.getD ((-z).toNat - 1) 1) *
            (gG.getD ((-z).toNat - 1) 1)⁻¹ := by rw [this]
          _ = (gG.getD ((-z).toNat - 1) 1)⁻¹ * u := by group
    calc u * ((if 0 < z then gG.getD (z.toNat - 1) 1 else (gG.getD ((-z).toNat - 1) 1)⁻¹) *
          evalCodes gG w)
        = (u * (if 0 < z then gG.getD (z.toNat - 1) 1 else (gG.getD ((-z).toNat - 1) 1)⁻¹)) *
          evalCodes gG w := by rw [mul_assoc]
      _ = (if 0 < z then gG.getD (z.toNat - 1) 1 else (gG.getD ((-z).toNat - 1) 1)⁻¹) *
          (u * evalCodes gG w) := by rw [hl, mul_assoc]
      _ = _ := by rw [ih, mul_assoc]

theorem forall₂_inv_of_invOK {gT : List Table} {gG : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) gT gG) (hinv : ∀ t ∈ gT, invOK n t (invT n t) = true) :
    List.Forall₂ (Rep n) (gT.map (invT n)) (gG.map fun g => g⁻¹) := by
  induction h with
  | nil => exact .nil
  | cons hab hr ih =>
    exact .cons (Rep.inv_of_invOK hab (hinv _ List.mem_cons_self))
      (ih fun t ht => hinv t (List.mem_cons_of_mem _ ht))

theorem forall₂_pair_of_invOK {gT : List Table} {gG : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) gT gG) (hinv : ∀ t ∈ gT, invOK n t (invT n t) = true) :
    List.Forall₂ (fun (w : Table × Table) (g : Equiv.Perm (Fin n)) => Rep n w.1 g ∧ Rep n w.2 g⁻¹)
      (gT.map fun t => (t, invT n t)) gG := by
  induction h with
  | nil => exact .nil
  | cons hab hr ih =>
    exact .cons ⟨hab, Rep.inv_of_invOK hab (hinv _ List.mem_cons_self)⟩
      (ih fun t ht => hinv t (List.mem_cons_of_mem _ ht))

theorem f3S_of_rowOKT (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gT : List Table} {gG : List (Equiv.Perm (Fin n))} (hgT : List.Forall₂ (Rep n) gT gG)
    (hgG : ∀ g ∈ gG, g ∈ Q.originalSubgroup) {uT : Table} {u : Equiv.Perm (Fin n)}
    (hu : Rep n uT u) {r : Row} (hp : r.prime.Prime) {Tss : List (List Table)}
    (hTss : levelTables Q = Tss) {NG : ℕ} (hNG : Q.orderCertificate = NG)
    (h : rowOKT n NG gT uT (candAllT n Tss uT) r = true) : F3S Q.originalSubgroup u r.prime := by
  classical
  set G := Q.originalSubgroup with hG
  simp only [rowOKT, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hu2T, hodd⟩, hord⟩, hgenT⟩, hogT⟩, hcand⟩ := h
  have hu2 : u * u = 1 := (tblEq_eq_iff (Rep.compT hu hu) (Rep.idT hn)).1 hu2T
  have hcardG : Nat.card G = NG := (Q.orderCertificate_eq_card hQ).symm.trans hNG
  have hk : ¬ r.prime ^ (r.pexp + 1) ∣ Nat.card G := by
    rw [hcardG]
    intro hd
    exact hord (Nat.mod_eq_zero_of_dvd hd)
  have hgenC : ∀ g ∈ gG, u * g = g * u := by
    intro g hg
    obtain ⟨t, ht, hrt⟩ := exists_of_mem_left_forall₂ (hgT.flip) hg
    exact eq_of_commT hu hrt (hgenT t ht).2
  have hgI := forall₂_inv_of_invOK hgT (fun t ht => (hgenT t ht).1)
  set ogT := r.oddWords.map (evalT n gT (gT.map (invT n))) with hogT'
  set ogP := r.oddWords.map (evalCodes gG) with hogP
  have hrepog : List.Forall₂ (Rep n) ogT ogP := by
    rw [hogT', hogP, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun w _ => rep_evalT hn hgT hgI w
  have hogG : ∀ g ∈ ogP, g ∈ G := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact evalCodes_mem G hgG w
  have hogC : ∀ g ∈ ogP, u * g = g * u := by
    intro g hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
    exact commute_evalCodes hgenC w
  have hogO : ∀ g ∈ ogP, Odd (orderOf g) := by
    intro g hg
    obtain ⟨T, hT, hTg⟩ := exists_of_mem_right_forall₂ hrepog hg
    have h1 := (powFixW_iff perm_faithful (List.Forall₂.cons hTg List.Forall₂.nil)
      r.oddExp).1 (hogT T hT).2
    simp only [List.prod_cons, List.prod_nil, mul_one] at h1
    exact Odd.of_dvd_nat (Nat.odd_iff.2 hodd) (orderOf_dvd_of_pow_eq_one h1)
  exact f3S_core hn Q hQ hTss hu hu2 hp hk ogP hogG hogC hogO (ogT.map fun T => (T, invT n T))
    (forall₂_pair_of_invOK hrepog fun T hT => (hogT T hT).1) hcand

theorem f3S_of_rowsOKT_primes (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gT : List Table} {gG : List (Equiv.Perm (Fin n))} (hgT : List.Forall₂ (Rep n) gT gG)
    (hgG : ∀ g ∈ gG, g ∈ Q.originalSubgroup) {uT : Table} {u : Equiv.Perm (Fin n)}
    (hu : Rep n uT u) {Tss : List (List Table)} (hTss : levelTables Q = Tss) {NG : ℕ}
    (hNG : Q.orderCertificate = NG) {rs : List Row} (h : rowsOKT n NG Tss gT uT rs = true)
    {ps : List ℕ} (hps : ∀ p ∈ ps, ∃ r ∈ rs, r.prime = p) (hpr : ∀ p ∈ ps, p.Prime) :
    ∀ p ∈ ps, F3S Q.originalSubgroup u p := by
  intro p hp
  obtain ⟨r, hr, rfl⟩ := hps p hp
  refine f3S_of_rowOKT hn Q hQ hgT hgG hu (hpr _ hp) hTss hNG ?_
  simp only [rowsOKT, List.all_eq_true] at h
  exact h r hr

end TableLevel

theorem f3S_of_rowsOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gG : List (Equiv.Perm (Fin n))} (hgG : ∀ g ∈ gG, g ∈ Q.originalSubgroup)
    {u : Equiv.Perm (Fin n)} {rs : List Row} (h : rowsOK n Q gG u rs = true) {r : Row}
    (hr : r ∈ rs) (hp : r.prime.Prime) : F3S Q.originalSubgroup u r.prime :=
  f3S_of_rowOK hn Q hQ hgG hp (by
    simp only [rowsOK, List.all_eq_true] at h
    exact h r hr)

theorem f3S_of_rowsOK_primes (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {gG : List (Equiv.Perm (Fin n))} (hgG : ∀ g ∈ gG, g ∈ Q.originalSubgroup)
    {u : Equiv.Perm (Fin n)} {rs : List Row} (h : rowsOK n Q gG u rs = true) {ps : List ℕ}
    (hps : ∀ p ∈ ps, ∃ r ∈ rs, r.prime = p) (hpr : ∀ p ∈ ps, p.Prime) :
    ∀ p ∈ ps, F3S Q.originalSubgroup u p := by
  intro p hp
  obtain ⟨r, hr, rfl⟩ := hps p hp
  exact f3S_of_rowsOK hn Q hQ hgG h hr (hpr _ hp)

theorem cover_of_coverOK (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {a b g₀ : Equiv.Perm (Fin n)} (ha : a ∈ Q.originalSubgroup) (hb : b ∈ Q.originalSubgroup)
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    {reps : List (Equiv.Perm (Fin n))} (hrepsG : ∀ r ∈ reps, g₀⁻¹ * r ∈ Q.originalSubgroup)
    {cap : ℕ} (h : coverOK n Q a b g₀ reps cap = true) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      ∃ r ∈ reps, ∃ c ∈ Q.originalSubgroup, u = c * r * c⁻¹ := by
  simp only [coverOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  exact (exists_conj_of_repsOK hn Q hQ (pairTables_spec hn ha hb) g₀ hg₀ (by norm_num) reps
    (fun r hr => ⟨hrepsG r hr,
      (ordTest_iff perm_faithful (rep_toTable hn r) (by norm_num)).1 (h2 r hr)⟩) cap h1).1

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

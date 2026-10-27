module

public import CFSG.ClassicalInvolution.Q3.TL3T25
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

section Count

variable {Y : Type} [Group Y] [Finite Y]

theorem card_le_of_conj_pair {C D : Subgroup Y} (a b : Y) (B : Set Y)
    (hBa : ∀ c ∈ C, c * a * c⁻¹ ∈ B) (hBb : ∀ c ∈ C, c * b * c⁻¹ ∈ B)
    (hD : ∀ c ∈ C, c * a = a * c → c * b = b * c → c ∈ D) :
    Nat.card C ≤ Nat.card B ^ 2 * Nat.card D := by
  classical
  let S : Subgroup ↥C := (Subgroup.centralizer ({a, b} : Set Y)).subgroupOf C
  have hS : ∀ c : ↥C, c ∈ S ↔ (c : Y) * a = a * c ∧ (c : Y) * b = b * c := by
    intro c
    simp only [S, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1.symm, h2.symm⟩
  let g : ↥C → B × B := fun c => (⟨c * a * c⁻¹, hBa c c.2⟩, ⟨c * b * c⁻¹, hBb c c.2⟩)
  have hg : ∀ c c' : ↥C, g c = g c' → c⁻¹ * c' ∈ S := by
    intro c c' h
    rw [hS]
    have h1 := congrArg (fun p => (p.1 : Y)) h
    have h2 := congrArg (fun p => (p.2 : Y)) h
    simp only [g, Subgroup.coe_inv] at h1 h2
    constructor
    · show (c⁻¹ * c' : ↥C).1 * a = a * (c⁻¹ * c' : ↥C).1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (c : Y)⁻¹ * c' * a = (c : Y)⁻¹ * ((c' : Y) * a * (c' : Y)⁻¹) * c' := by group
        _ = (c : Y)⁻¹ * ((c : Y) * a * (c : Y)⁻¹) * c' := by rw [← h1]
        _ = a * ((c : Y)⁻¹ * c') := by group
    · show (c⁻¹ * c' : ↥C).1 * b = b * (c⁻¹ * c' : ↥C).1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (c : Y)⁻¹ * c' * b = (c : Y)⁻¹ * ((c' : Y) * b * (c' : Y)⁻¹) * c' := by group
        _ = (c : Y)⁻¹ * ((c : Y) * b * (c : Y)⁻¹) * c' := by rw [← h2]
        _ = b * ((c : Y)⁻¹ * c') := by group
  let f : (↥C ⧸ S) → B × B := Quotient.lift g (fun c c' (h : QuotientGroup.leftRel S c c') => by
    have h' : c⁻¹ * c' ∈ S := QuotientGroup.leftRel_apply.mp h
    rw [hS] at h'
    obtain ⟨h1, h2⟩ := h'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 h2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show (c : Y) * a * (c : Y)⁻¹ = (c' : Y) * a * (c' : Y)⁻¹
      have : (c' : Y) = (c : Y) * ((c : Y)⁻¹ * c') := by group
      rw [this]
      calc (c : Y) * a * (c : Y)⁻¹ = (c : Y) * (a * ((c : Y)⁻¹ * c')) * ((c : Y)⁻¹ * c')⁻¹ * (c : Y)⁻¹ := by
            group
        _ = _ := by rw [← h1]; group
    · show (c : Y) * b * (c : Y)⁻¹ = (c' : Y) * b * (c' : Y)⁻¹
      have : (c' : Y) = (c : Y) * ((c : Y)⁻¹ * c') := by group
      rw [this]
      calc (c : Y) * b * (c : Y)⁻¹ = (c : Y) * (b * ((c : Y)⁻¹ * c')) * ((c : Y)⁻¹ * c')⁻¹ * (c : Y)⁻¹ := by
            group
        _ = _ := by rw [← h2]; group)
  have hf : Function.Injective f := by
    intro x y hxy
    induction x using Quotient.inductionOn' with | _ c => ?_
    induction y using Quotient.inductionOn' with | _ c' => ?_
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    exact hg c c' hxy
  have h1 : Nat.card (↥C ⧸ S) ≤ Nat.card B ^ 2 := by
    calc Nat.card (↥C ⧸ S) ≤ Nat.card (B × B) := Nat.card_le_card_of_injective f hf
      _ = Nat.card B ^ 2 := by rw [Nat.card_prod, sq]
  have h2 : Nat.card S ≤ Nat.card D := by
    refine Nat.card_le_card_of_injective (fun s => (⟨(s : ↥C).1, hD _ (s : ↥C).2
      (((hS s).mp s.2).1) (((hS s).mp s.2).2)⟩ : D)) ?_
    intro s s' h
    have h' : ((s : ↥C) : Y) = ((s' : ↥C) : Y) := congrArg (fun d : D => (d : Y)) h
    exact Subtype.ext (Subtype.ext h')
  calc Nat.card C = Nat.card (↥C ⧸ S) * Nat.card S := Subgroup.card_eq_card_quotient_mul_card_subgroup S
    _ ≤ Nat.card B ^ 2 * Nat.card D := Nat.mul_le_mul h1 h2

end Count

section Three

variable {Y : Type} [Group Y] [Finite Y] {E : Subgroup Y}

theorem e8_top_le_closure (hE : E8Struct (⊤ : Subgroup Y) E) {z : Y} (hzE : z ∈ E) (hz1 : z ≠ 1)
    (hC : Nat.card ↥(Subgroup.centralizer ({z} : Set Y)) = 192) {y : Y} (hyz : y * z = z * y)
    (hy3 : orderOf y = 3) :
    E ≤ Subgroup.closure {w : Y | w * z = z * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1} := by
  classical
  have hcomm : ∀ a b : Y, a ∈ E → b ∈ E → a * b = b * a := fun a b ha hb => comm_of_sq hE.sq ha hb
  have hinv : ∀ e ∈ E, e⁻¹ = e := fun e he => inv_eq_of_mul_eq_one_right (hE.sq e he)
  set S₀ : Set Y := {w : Y | w * z = z * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1} with hS₀
  set T : Subgroup Y := Subgroup.closure S₀ with hT
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hyS : y ∈ S₀ := ⟨hyz, 1, by rw [pow_one]; exact hy3'⟩
  have hstep1 : ∀ y' ∈ S₀, ∀ e ∈ E, e * (y' * e * y'⁻¹) ∈ T := by
    intro y' hy' e he
    obtain ⟨hy'z, a, hya⟩ := hy'
    have hez : e * z = z * e := hcomm e z he hzE
    have h1 : e * y' * e⁻¹ ∈ S₀ := by
      refine ⟨?_, a, ?_⟩
      · rw [hinv e he]
        calc e * y' * e * z = e * y' * (e * z) := by group
          _ = e * y' * (z * e) := by rw [hez]
          _ = e * (y' * z) * e := by group
          _ = e * (z * y') * e := by rw [hy'z]
          _ = (e * z) * y' * e := by group
          _ = z * e * y' * e := by rw [hez]
          _ = z * (e * y' * e) := by group
      · rw [conj_pow, hya]; group
    have h2 : y'⁻¹ ∈ S₀ := by
      refine ⟨?_, a, ?_⟩
      · have : Commute y' z := hy'z
        exact (this.inv_left).eq
      · rw [inv_pow, hya, inv_one]
    have h3 := T.mul_mem (Subgroup.subset_closure h1) (Subgroup.subset_closure h2)
    have e1 : e * y' * e⁻¹ * y'⁻¹ = e * (y' * e * y'⁻¹) := by
      rw [hinv e he]; group
    rwa [e1] at h3
  have hyN : ∀ e ∈ E, y * e * y⁻¹ ∈ E := fun e he => hE.normal y (Subgroup.mem_top y) e he
  have hyyy : y * y * y = 1 := by
    have : y ^ 3 = 1 := hy3'
    simpa [pow_succ, mul_assoc] using this
  have hsig3 : ∀ e : Y, y * (y * (y * e * y⁻¹) * y⁻¹) * y⁻¹ = e := by
    intro e
    calc y * (y * (y * e * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * e * (y * y * y)⁻¹ := by group
      _ = e := by rw [hyyy]; group
  let δ : ↥E →* ↥E := MonoidHom.mk'
    (fun e => ⟨(e : Y) * (y * (e : Y) * y⁻¹), E.mul_mem e.2 (hyN e e.2)⟩) (by
      intro a b
      apply Subtype.ext
      show ((a : Y) * b) * (y * ((a : Y) * b) * y⁻¹) =
        ((a : Y) * (y * (a : Y) * y⁻¹)) * ((b : Y) * (y * (b : Y) * y⁻¹))
      have hc := hcomm (y * (a : Y) * y⁻¹) (b : Y) (hyN a a.2) b.2
      calc ((a : Y) * b) * (y * ((a : Y) * b) * y⁻¹)
          = (a : Y) * (b * (y * (a : Y) * y⁻¹)) * (y * (b : Y) * y⁻¹) := by group
        _ = (a : Y) * ((y * (a : Y) * y⁻¹) * b) * (y * (b : Y) * y⁻¹) := by rw [← hc]
        _ = _ := by group)
  have hδ : ∀ e : ↥E, ((δ e : ↥E) : Y) = (e : Y) * (y * (e : Y) * y⁻¹) := fun e => rfl
  have hnc : ¬ ∀ e ∈ E, y * e = e * y := by
    intro hall
    have hyE : y ∈ E := hE.cent y (Subgroup.mem_top y) fun e he => hall e he
    have hyy : y * y = 1 := hE.sq y hyE
    have : y = 1 := by
      calc y = (y * y) * y := by rw [hyy, one_mul]
        _ = 1 := hyyy
    rw [this, orderOf_one] at hy3
    omega
  set W : Subgroup ↥E := δ.range with hW
  have hB : ∀ e : ↥E, y * ((δ e : ↥E) : Y) * y⁻¹ = ((δ e : ↥E) : Y) → ((δ e : ↥E) : Y) = 1 := by
    intro e hfix
    rw [hδ] at hfix ⊢
    have he₁E : y * (e : Y) * y⁻¹ ∈ E := hyN e e.2
    have h1 : (y * (e : Y) * y⁻¹) * (y * (y * (e : Y) * y⁻¹) * y⁻¹) =
        (e : Y) * (y * (e : Y) * y⁻¹) := by
      have : y * ((e : Y) * (y * (e : Y) * y⁻¹)) * y⁻¹ =
          (y * (e : Y) * y⁻¹) * (y * (y * (e : Y) * y⁻¹) * y⁻¹) := by group
      rw [← this]
      exact hfix
    have h2 : y * (y * (e : Y) * y⁻¹) * y⁻¹ = (e : Y) := by
      have h3 : (y * (e : Y) * y⁻¹) * (y * (y * (e : Y) * y⁻¹) * y⁻¹) =
          (y * (e : Y) * y⁻¹) * (e : Y) := by
        rw [h1, hcomm (e : Y) _ e.2 he₁E]
      exact mul_left_cancel h3
    have h4 : y * (e : Y) * y⁻¹ = (e : Y) := by
      have h5 : y * (y * (y * (e : Y) * y⁻¹) * y⁻¹) * y⁻¹ = (e : Y) := hsig3 e
      rw [h2] at h5
      exact h5
    rw [h4]
    exact hE.sq e e.2
  have hker : ∀ e : ↥E, e ∈ δ.ker ↔ y * (e : Y) * y⁻¹ = e := by
    intro e
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : (e : Y) * (y * (e : Y) * y⁻¹) = 1 := congrArg Subtype.val h
      calc y * (e : Y) * y⁻¹ = (e : Y)⁻¹ * ((e : Y) * (y * (e : Y) * y⁻¹)) := by group
        _ = (e : Y)⁻¹ := by rw [h1, mul_one]
        _ = e := hinv e e.2
    · intro h
      apply Subtype.ext
      show (e : Y) * (y * (e : Y) * y⁻¹) = 1
      rw [h]
      exact hE.sq e e.2
  have hz'ker : (⟨z, hzE⟩ : ↥E) ∈ δ.ker := by
    rw [hker]
    show y * z * y⁻¹ = z
    rw [hyz]
    group
  have hkerlt : 1 < Nat.card δ.ker := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    intro h
    have := hz'ker
    rw [h, Subgroup.mem_bot] at this
    exact hz1 (congrArg Subtype.val this)
  have hkerne : δ.ker ≠ ⊤ := by
    intro h
    apply hnc
    intro e he
    have : (⟨e, he⟩ : ↥E) ∈ δ.ker := by rw [h]; trivial
    have h1 : y * e * y⁻¹ = e := (hker _).mp this
    calc y * e = y * e * y⁻¹ * y := by group
      _ = e * y := by rw [h1]
  have hcardE : Nat.card ↥E = 8 := hE.card
  have hprod : Nat.card δ.ker * Nat.card W = 8 := by
    have := Subgroup.card_ker_mul_card_range δ
    rw [hcardE] at this
    exact this
  have hkdvd : Nat.card δ.ker ∣ 8 := ⟨Nat.card W, hprod.symm⟩
  have hk8 : Nat.card δ.ker ≠ 8 := by
    intro h8
    apply hkerne
    exact Subgroup.eq_top_of_card_eq _ (by rw [h8, hcardE])
  have hk24 : Nat.card δ.ker = 2 ∨ Nat.card δ.ker = 4 := by
    have hmem : Nat.card δ.ker ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hkdvd, by norm_num⟩
    have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  have hWσ : ∀ w ∈ W, (⟨y * (w : Y) * y⁻¹, hyN w w.2⟩ : ↥E) ∈ W := by
    rintro w ⟨e, rfl⟩
    refine ⟨⟨y * (e : Y) * y⁻¹, hyN e e.2⟩, ?_⟩
    apply Subtype.ext
    show ((y * (e : Y) * y⁻¹) * (y * (y * (e : Y) * y⁻¹) * y⁻¹) : Y) =
      y * ((e : Y) * (y * (e : Y) * y⁻¹)) * y⁻¹
    group
  have hW4 : Nat.card W = 4 := by
    rcases hk24 with h2 | h4
    · rw [h2] at hprod
      omega
    · exfalso
      rw [h4] at hprod
      have hW2 : Nat.card W = 2 := by omega
      have hWne : W ≠ ⊥ := by
        intro h
        rw [h, Subgroup.card_bot] at hW2
        omega
      obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hWne
      have hwW : (a : ↥E) ∈ W := a.2
      have hw1 : (a : ↥E) ≠ 1 := fun h => ha1 (Subtype.ext h)
      have hσwW : (⟨y * ((a : ↥E) : Y) * y⁻¹, hyN a a.1.2⟩ : ↥E) ∈ W := hWσ a hwW
      have hσw1 : (⟨y * ((a : ↥E) : Y) * y⁻¹, hyN a a.1.2⟩ : ↥E) ≠ 1 := by
        intro h
        apply hw1
        apply Subtype.ext
        have h' : y * ((a : ↥E) : Y) * y⁻¹ = 1 := congrArg Subtype.val h
        calc ((a : ↥E) : Y) = y⁻¹ * (y * ((a : ↥E) : Y) * y⁻¹) * y := by group
          _ = 1 := by rw [h']; group
      have hσww : (⟨y * ((a : ↥E) : Y) * y⁻¹, hyN a a.1.2⟩ : ↥E) ≠ (a : ↥E) := by
        intro h
        apply hw1
        obtain ⟨e, he⟩ := hwW
        have h' : y * ((δ e : ↥E) : Y) * y⁻¹ = ((δ e : ↥E) : Y) := by
          rw [he]
          exact congrArg Subtype.val h
        have h1 := hB e h'
        rw [he] at h1
        exact Subtype.ext h1
      have h3 : 3 ≤ Nat.card W := by
        have hsub : ({1, (a : ↥E), (⟨y * ((a : ↥E) : Y) * y⁻¹, hyN a a.1.2⟩ : ↥E)} : Set ↥E) ⊆
            (W : Set ↥E) := by
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl | rfl
          · exact W.one_mem
          · exact hwW
          · exact hσwW
        have h3' : ({1, (a : ↥E), (⟨y * ((a : ↥E) : Y) * y⁻¹, hyN a a.1.2⟩ : ↥E)} :
            Set ↥E).ncard = 3 :=
          Set.ncard_eq_three.mpr ⟨1, (a : ↥E), _, hw1.symm, hσw1.symm, hσww.symm, rfl⟩
        have h4' := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [h3', ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h4'
        exact h4'
      omega
  set Wy : Subgroup Y := W.map E.subtype with hWy
  have hWyc : Nat.card Wy = 4 := by
    rw [hWy, Subgroup.card_map_of_injective E.subtype_injective]
    exact hW4
  have hWyE : Wy ≤ E := Subgroup.map_subtype_le _
  have hmemWy : ∀ x : Y, x ∈ Wy ↔ ∃ e : ↥E, (e : Y) * (y * (e : Y) * y⁻¹) = x := by
    intro x
    constructor
    · rintro ⟨w, ⟨e, rfl⟩, rfl⟩
      exact ⟨e, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨δ e, ⟨e, rfl⟩, rfl⟩
  have hWyT : Wy ≤ T := by
    intro x hx
    obtain ⟨e, rfl⟩ := (hmemWy x).mp hx
    exact hstep1 y hyS e e.2
  have hzWy : z ∉ Wy := by
    intro hz
    obtain ⟨e, he⟩ := (hmemWy z).mp hz
    have h1 : y * ((δ e : ↥E) : Y) * y⁻¹ = ((δ e : ↥E) : Y) := by
      rw [hδ, he, hyz]
      group
    have h2 := hB e h1
    rw [hδ, he] at h2
    exact hz1 h2
  obtain ⟨a, haW, ha1⟩ : ∃ a ∈ Wy, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (A := Wy) (a := 1) (b := 1) fun x hx =>
      Or.inl (hcon x hx)
    omega
  obtain ⟨b, hbW, hb1, hba⟩ : ∃ b ∈ Wy, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have := natCard_subgroup_le_two_of_subset (A := Wy) (a := 1) (b := a) fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    omega
  have hgen : Subgroup.closure ({a, b} : Set Y) = Wy := by
    have hle : Subgroup.closure ({a, b} : Set Y) ≤ Wy := by
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact haW
      · exact hbW
    have hdvd : Nat.card (Subgroup.closure ({a, b} : Set Y)) ∣ 4 :=
      hWyc ▸ Subgroup.card_dvd_of_le hle
    have h3 : 3 ≤ Nat.card (Subgroup.closure ({a, b} : Set Y)) := by
      have hsub : ({1, a, b} : Set Y) ⊆ (Subgroup.closure ({a, b} : Set Y) : Set Y) := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have h3' : ({1, a, b} : Set Y).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨1, a, b, ha1.symm, hb1.symm, hba.symm, rfl⟩
      have h4' := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [h3', ← Nat.card_coe_set_eq, SetLike.coe_sort_coe] at h4'
      exact h4'
    have h4 : Nat.card (Subgroup.closure ({a, b} : Set Y)) = 4 := by
      have := Nat.le_of_dvd (by norm_num) hdvd
      have hmem : Nat.card (Subgroup.closure ({a, b} : Set Y)) ∈ Nat.divisors 4 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hWyc])
  have hEcard2 : Nat.card E = 2 * Nat.card Wy := by rw [hE.card, hWyc]
  have hex : ∃ c ∈ Subgroup.centralizer ({z} : Set Y), ∃ w ∈ Wy, c * w * c⁻¹ ∉ Wy := by
    by_contra hno
    push Not at hno
    have hcount := card_le_of_conj_pair (C := Subgroup.centralizer ({z} : Set Y)) (D := E) a b
      (Wy : Set Y) (fun c hc => hno c hc a haW) (fun c hc => hno c hc b hbW) ?_
    · rw [hC, SetLike.coe_sort_coe, hWyc, hE.card] at hcount
      omega
    · intro c hc hca hcb
      have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
      refine hE.cent c (Subgroup.mem_top c) fun e he => ?_
      have hWc : ∀ x ∈ Wy, c * x = x * c := by
        intro x hx
        rw [← hgen] at hx
        have hle : Subgroup.closure ({a, b} : Set Y) ≤ Subgroup.centralizer ({c} : Set Y) := by
          refine (Subgroup.closure_le _).mpr ?_
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact Subgroup.mem_centralizer_singleton_iff.mpr hca.symm
          · exact Subgroup.mem_centralizer_singleton_iff.mpr hcb.symm
        exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hx)).symm
      rcases mem_or_of_card_eq_two_mul hWyE hEcard2 hzE hzWy he with h | h
      · exact hWc e h
      · have h' := hWc _ h
        calc c * e = c * (z * (z⁻¹ * e)) := by group
          _ = (c * z) * (z⁻¹ * e) := by group
          _ = z * (c * (z⁻¹ * e)) := by rw [hcz]; group
          _ = z * ((z⁻¹ * e) * c) := by rw [h']
          _ = e * c := by group
  obtain ⟨c, hc, w, hwWy, hcw⟩ := hex
  have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  set W' : Subgroup Y := conjSub c Wy with hW'
  have hW'c : Nat.card W' = 4 := by
    rw [hW', conjSub, Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hWyc
  have hW'E : W' ≤ E := by
    intro x hx
    rw [hW', mem_conjSub_iff] at hx
    have := hE.normal c (Subgroup.mem_top c) _ (hWyE hx)
    have e1 : c * (c⁻¹ * x * c) * c⁻¹ = x := by group
    rwa [e1] at this
  have hy'S : c * y * c⁻¹ ∈ S₀ := by
    refine ⟨?_, 1, ?_⟩
    · have hcz' : c⁻¹ * z = z * c⁻¹ := by
        calc c⁻¹ * z = c⁻¹ * z * c * c⁻¹ := by group
          _ = c⁻¹ * (z * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * z) * c⁻¹ := by rw [hcz]
          _ = z * c⁻¹ := by group
      calc c * y * c⁻¹ * z = c * y * (c⁻¹ * z) := by group
        _ = c * y * (z * c⁻¹) := by rw [hcz']
        _ = c * (y * z) * c⁻¹ := by group
        _ = c * (z * y) * c⁻¹ := by rw [hyz]
        _ = (c * z) * y * c⁻¹ := by group
        _ = z * c * y * c⁻¹ := by rw [hcz]
        _ = z * (c * y * c⁻¹) := by group
    · rw [pow_one, conj_pow, hy3']
      group
  have hW'T : W' ≤ T := by
    intro x hx
    rw [hW', mem_conjSub_iff] at hx
    obtain ⟨e, he⟩ := (hmemWy _).mp hx
    have he' : c * (e : Y) * c⁻¹ ∈ E := hE.normal c (Subgroup.mem_top c) e e.2
    have h1 := hstep1 (c * y * c⁻¹) hy'S (c * (e : Y) * c⁻¹) he'
    have e1 : x = (c * (e : Y) * c⁻¹) *
        (c * y * c⁻¹ * (c * (e : Y) * c⁻¹) * (c * y * c⁻¹)⁻¹) := by
      have : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
      rw [this, ← he]
      group
    rw [e1]
    exact h1
  have hnotle : ¬ W' ≤ Wy := fun hle => hcw (hle (conj_mem_conjSub hwWy))
  have hsupE : Wy ⊔ W' = E := by
    have hle : Wy ⊔ W' ≤ E := sup_le hWyE hW'E
    have hdvd : Nat.card (Wy ⊔ W' : Subgroup Y) ∣ 8 := hE.card ▸ Subgroup.card_dvd_of_le hle
    have hgt : 4 < Nat.card (Wy ⊔ W' : Subgroup Y) := by
      by_contra hcon
      push Not at hcon
      have heq : Wy = Wy ⊔ W' := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hWyc]; exact hcon)
      exact hnotle (heq ▸ le_sup_right)
    have h8 : Nat.card (Wy ⊔ W' : Subgroup Y) = 8 := by
      have hmem : Nat.card (Wy ⊔ W' : Subgroup Y) ∈ Nat.divisors 8 :=
        Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by decide
      rw [hdiv] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      omega
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8, hE.card])
  rw [← hsupE]
  exact sup_le hWyT hW'T

end Three

end CFSG.ClassicalInvolution.Q3.TC.Thin

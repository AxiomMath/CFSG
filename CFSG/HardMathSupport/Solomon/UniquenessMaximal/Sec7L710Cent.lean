module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710CentA
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Fit
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Tools

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {B T I : Subgroup G}

@[expose] def dOf (B T I : Subgroup G) : Subgroup G :=
  yOf B T I ⊓ Subgroup.centralizer (sOf B T I : Set G)

@[expose] def eOf (B T I : Subgroup G) : Subgroup G := dOf B T I ⊔ pOf B T I

omit [Finite G] in
theorem dOf_le_yOf (B T I : Subgroup G) : dOf B T I ≤ yOf B T I := inf_le_left

omit [Finite G] in
theorem dOf_le_eOf (B T I : Subgroup G) : dOf B T I ≤ eOf B T I := le_sup_left

omit [Finite G] in
theorem pOf_le_eOf (B T I : Subgroup G) : pOf B T I ≤ eOf B T I := le_sup_right

omit [Finite G] in
theorem sOf_le_pOf (B T I : Subgroup G) : sOf B T I ≤ pOf B T I := inf_le_right

omit [Finite G] in
theorem sOf_le_tOf (B T I : Subgroup G) : sOf B T I ≤ T := inf_le_left

omit [Finite G] in
theorem eOf_le_yOf (B T I : Subgroup G) : eOf B T I ≤ yOf B T I :=
  sup_le (dOf_le_yOf B T I) (pOf_le_yOf B T I)

omit [Finite G] in
theorem exists_mul_of_mem_eOf {x : G} (hx : x ∈ eOf B T I) :
    ∃ d ∈ dOf B T I, ∃ p ∈ pOf B T I, x = d * p := by
  have hn : dOf B T I ≤ Subgroup.normalizer (pOf B T I : Set G) :=
    (dOf_le_yOf B T I).trans (y_le_normalizer_pOf B T I)
  have hx0 : x ∈ dOf B T I ⊔ pOf B T I := hx
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hn
  have hx' : (⟨x, hx0⟩ : ↥(dOf B T I ⊔ pOf B T I)) ∈
      (dOf B T I).subgroupOf (dOf B T I ⊔ pOf B T I) ⊔
        (pOf B T I).subgroupOf (dOf B T I ⊔ pOf B T I) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.1 hx'
  exact ⟨y, hy, z, hz, by simpa using (congrArg Subtype.val hyz).symm⟩

theorem y_le_normalizer_eOf (hs : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)) :
    yOf B T I ≤ Subgroup.normalizer (eOf B T I : Set G) := by
  intro y hy
  obtain ⟨q, hq, w, ⟨hwS, hwY⟩, rfl⟩ :=
    exists_mul_normalizer (p := 2) (pOf_le_yOf B T I) (y_le_normalizer_pOf B T I)
      (sOf_le_pOf B T I) hs.1 hs.2 hy
  refine Subgroup.mul_mem _ (Subgroup.le_normalizer (pOf_le_eOf B T I hq)) ?_
  have hD : w ∈ Subgroup.normalizer (dOf B T I : Set G) :=
    Sec7.inf_normalizer_le_normalizer_inf _ _
      ⟨Subgroup.le_normalizer hwY, normalizer_le_normalizer_centralizer _ hwS⟩
  exact Subgroup.inf_normalizer_le_normalizer_sup (dOf B T I) (pOf B T I)
    ⟨hD, y_le_normalizer_pOf B T I hwY⟩

theorem y_le_normalizer_O (h : Setup710 B T I) :
    yOf B T I ≤ Subgroup.normalizer (GLAPPrimeCoreOf 3 I : Set G) := by
  rw [← inf_pOf_eq h]
  exact fun y hy => Sec7.inf_normalizer_le_normalizer_inf _ _
    ⟨y_le_normalizer_I h hy, y_le_normalizer_pOf B T I hy⟩

theorem inf_centralizer_le_O (h : Setup710 B T I)
    (hs : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)) :
    I ⊓ Subgroup.centralizer (sOf B T I : Set G) ≤ GLAPPrimeCoreOf 3 I := by
  set O := GLAPPrimeCoreOf 3 I with hO
  set V : Subgroup G := ⁅I, O⁆ with hV
  have hOI : O ≤ I := Sec7.glaPPrimeCoreOf_le_self' 3 I
  have hIN : I ≤ Subgroup.normalizer (O : Set G) :=
    (I_le_yOf B T I).trans (y_le_normalizer_O h)
  have hVO : V ≤ O := by
    rw [hV, Subgroup.commutator_le]
    intro a ha b hb
    have : a * b * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hIN ha) b).1 hb
    rw [commutatorElement_def]
    exact O.mul_mem this (O.inv_mem hb)
  have hOP : O ≤ pOf B T I := (le_of_eq (inf_pOf_eq h).symm).trans inf_le_right
  have hVP : V ≤ pOf B T I := hVO.trans hOP
  have hYV : yOf B T I ≤ Subgroup.normalizer (V : Set G) := fun y hy =>
    mem_normalizer_commutator (y_le_normalizer_I h hy) (y_le_normalizer_O h hy)
  have hVn : pOf B T I ≤ Subgroup.normalizer (V : Set G) := (pOf_le_yOf B T I).trans hYV
  have hQi := not_dvd_relIndex_inf (p := 2) hVP hVn (sOf_le_pOf B T I) hs.2
  have hQ2 : IsPGroup 2 ↥(sOf B T I ⊓ V) := hs.1.to_le inf_le_left
  have hc := h.c18 (sOf B T I ⊓ V) inf_le_right hQ2 hQi
  refine le_trans ?_ hc
  exact inf_le_inf_left _ (Subgroup.centralizer_le (by exact fun x hx => hx.1))

theorem not_I_le_eOf (h : Setup710 B T I)
    (hs : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)) :
    ¬ I ≤ eOf B T I := by
  intro hIE
  have hIO : I ≤ GLAPPrimeCoreOf 3 I := by
    refine h.gen3.symm.le.trans ((Subgroup.closure_le _).2 ?_)
    rintro x ⟨hxI, n, hxn⟩
    obtain ⟨z, hz, r, hr, -, hxe⟩ := sylow_lift (p := 3) (M := eOf B T I) (Z := pOf B T I)
      (N₀ := dOf B T I) (dOf_le_eOf B T I) (pOf_le_eOf B T I)
      ((eOf_le_yOf B T I).trans (y_le_normalizer_pOf B T I)) (not_three_dvd_card_pOf B T I)
      (by rw [sup_comm]; exact le_rfl) (hIE hxI) hxn
    have hzY : z ∈ yOf B T I := pOf_le_yOf B T I hz
    have hrI : r ∈ I := by
      have h1 := (Subgroup.mem_normalizer_iff.1 (y_le_normalizer_I h (inv_mem hzY)) x).1 hxI
      have h2 : r = z⁻¹ * x * z⁻¹⁻¹ := by rw [hxe]; group
      rw [h2]; exact h1
    have hrO : r ∈ GLAPPrimeCoreOf 3 I := inf_centralizer_le_O h hs ⟨hrI, hr.2⟩
    have := (Subgroup.mem_normalizer_iff.1 (y_le_normalizer_O h hzY) r).1 hrO
    rw [hxe]; exact this
  exact not_le_of_isLThreeFour h.lthree hIO

theorem eOf_inf_I (h : Setup710 B T I)
    (hs : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)) :
    eOf B T I ⊓ I = GLAPPrimeCoreOf 3 I := by
  have hOP : GLAPPrimeCoreOf 3 I ≤ pOf B T I := (le_of_eq (inf_pOf_eq h).symm).trans inf_le_right
  have hOI : GLAPPrimeCoreOf 3 I ≤ I := Sec7.glaPPrimeCoreOf_le_self' 3 I
  rcases eq_or_eq_of_normal_of_isLThreeFour h.lthree
      (N := eOf B T I ⊓ I) (le_inf (hOP.trans (pOf_le_eOf B T I)) hOI) inf_le_right
      (fun i hi => Sec7.inf_normalizer_le_normalizer_inf _ _
        ⟨y_le_normalizer_eOf hs (I_le_yOf B T I hi), Subgroup.le_normalizer hi⟩) with h1 | h1
  · exact h1
  · exact absurd ((le_of_eq h1.symm).trans inf_le_left) (not_I_le_eOf h hs)

theorem comm_mem_O_of_mem_eOf (h : Setup710 B T I)
    (hs : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)) {e i : G}
    (he : e ∈ eOf B T I) (hi : i ∈ I) : e * i * e⁻¹ * i⁻¹ ∈ GLAPPrimeCoreOf 3 I := by
  rw [← eOf_inf_I h hs]
  have heY : e ∈ yOf B T I := eOf_le_yOf B T I he
  have hiY : i ∈ yOf B T I := I_le_yOf B T I hi
  refine ⟨?_, ?_⟩
  · have h1 : e * (i * e⁻¹ * i⁻¹) ∈ eOf B T I := by
      refine (eOf B T I).mul_mem he ?_
      have := (Subgroup.mem_normalizer_iff.1 (y_le_normalizer_eOf hs hiY) e⁻¹).1
        ((eOf B T I).inv_mem he)
      simpa using this
    simpa [mul_assoc] using h1
  · have h1 := (Subgroup.mem_normalizer_iff.1 (y_le_normalizer_I h heY) i).1 hi
    exact I.mul_mem h1 (I.inv_mem hi) |> fun x => by simpa [mul_assoc] using x

theorem exists_conj_mem_B (h : Setup710 B T I) {r : G} (hrY : r ∈ yOf B T I) {k : ℕ}
    (hrk : r ^ (3 ^ k) = 1) : ∃ y ∈ yOf B T I, y * r * y⁻¹ ∈ B := by
  have hB3 : IsPGroup 3 ↥B := fun g => ⟨1, Subtype.ext (by simpa using h.bElem.2 g g.2)⟩
  have hR3 : IsPGroup 3 ↥(Subgroup.zpowers r) := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hrk)
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy, hyr⟩ := exists_conj_le_of_relIndex (p := 3) (H := yOf B T I)
    (R := Subgroup.zpowers r) (S := B) (Subgroup.zpowers_le.2 hrY) hR3 (B_le_yOf B T I) hB3
    (b_sylow_y h)
  exact ⟨y, hy, hyr r (Subgroup.mem_zpowers r)⟩

theorem eq_one_of_mem_B_eOf (h : Setup710 B T I)
    (hs : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)) {b : G}
    (hbB : b ∈ B) (hbE : b ∈ eOf B T I) : b = 1 := by
  have hOP : GLAPPrimeCoreOf 3 I ≤ pOf B T I := (le_of_eq (inf_pOf_eq h).symm).trans inf_le_right
  have hbI : ∀ i ∈ I, b * i * b⁻¹ * i⁻¹ ∈ pOf B T I :=
    fun i hi => hOP (comm_mem_O_of_mem_eOf h hs hbE hi)
  have hT := comm_mem_pOf_of_centralizes h hbB hbI
  have hcS : ∀ t ∈ T, b * t * b⁻¹ * t⁻¹ ∈ sOf B T I := fun t ht =>
    ⟨T.mul_mem ((Subgroup.mem_normalizer_iff.1 (h.bnT hbB) t).1 ht) (T.inv_mem ht), hT t ht⟩
  have hbN : b ∈ Subgroup.normalizer (sOf B T I : Set G) := (b_le_wOf h hbB).1
  obtain ⟨d', hd', p', hp', hbdp⟩ := exists_mul_of_mem_eOf hbE
  have hdc : ∀ c ∈ sOf B T I, c * d' = d' * c := Subgroup.mem_centralizer_iff.1 hd'.2
  have hbS : ∀ s ∈ sOf B T I, b * s * b⁻¹ = p' * s * p'⁻¹ := by
    intro s hs'
    have hc : b * s * b⁻¹ ∈ sOf B T I := (Subgroup.mem_normalizer_iff.1 hbN s).1 hs'
    have hp'eq : p' = d'⁻¹ * b := by rw [hbdp]; group
    rw [hp'eq]
    calc b * s * b⁻¹ = d'⁻¹ * (d' * (b * s * b⁻¹)) := by group
      _ = d'⁻¹ * ((b * s * b⁻¹) * d') := by rw [hdc _ hc]
      _ = d'⁻¹ * b * s * (d'⁻¹ * b)⁻¹ := by group
  have hpS : ∀ s ∈ sOf B T I, p' * s * p'⁻¹ ∈ sOf B T I := fun s hs' => by
    rw [← hbS s hs']; exact (Subgroup.mem_normalizer_iff.1 hbN s).1 hs'
  have hcop : Nat.Coprime 3 (orderOf p') := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => ?_
    exact not_three_dvd_card_pOf B T I (hd.trans (Subgroup.orderOf_dvd_natCard _ hp'))
  have hb3 : b ^ 3 = 1 := h.bElem.2 b hbB
  have hbc := conj_eq_self_of_coprime (orderOf_pos p') hcop hb3 (pow_orderOf_eq_one p') hbS hpS
  have hbT : ∀ t ∈ T, b * t * b⁻¹ = t := by
    intro t ht
    have hcmem := hcS t ht
    set c := b * t * b⁻¹ * t⁻¹ with hc
    have hbcc : b * c * b⁻¹ = c := hbc c hcmem
    have e1 : b * t * b⁻¹ = c * t := by rw [hc]; group
    have e2 : b * (c * t) * b⁻¹ = c * (c * t) := by
      calc b * (c * t) * b⁻¹ = (b * c * b⁻¹) * (b * t * b⁻¹) := by group
        _ = c * (c * t) := by rw [hbcc, e1]
    have e3 : b * (c * (c * t)) * b⁻¹ = c * (c * (c * t)) := by
      calc b * (c * (c * t)) * b⁻¹ = (b * c * b⁻¹) * (b * (c * t) * b⁻¹) := by group
        _ = c * (c * (c * t)) := by rw [hbcc, e2]
    have e4 : b * (b * (b * t * b⁻¹) * b⁻¹) * b⁻¹ = t := by
      have hb3' : b * (b * b) = 1 := by rw [← pow_three]; exact hb3
      calc b * (b * (b * t * b⁻¹) * b⁻¹) * b⁻¹ = (b * (b * b)) * t * (b * (b * b))⁻¹ := by group
        _ = t := by rw [hb3']; simp
    rw [e1, e2, e3] at e4
    have hc3 : c * (c * c) = 1 := by
      have : (c * (c * c)) * t = 1 * t := by
        calc (c * (c * c)) * t = c * (c * (c * t)) := by group
          _ = t := e4
          _ = 1 * t := (one_mul t).symm
      exact mul_right_cancel this
    obtain ⟨m, hm⟩ := hs.1 ⟨c, hcmem⟩
    have hm' : c ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
    have hc1 : c = 1 := by
      have h3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one (by rw [pow_three]; exact hc3)
      have h2 : orderOf c ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm'
      exact orderOf_eq_one_iff.1
        (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)) h3 h2)
    rw [e1, hc1, one_mul]
  refine h.cB b hbB fun t ht => ?_
  calc b * t = (b * t * b⁻¹) * b := by group
    _ = t * b := by rw [hbT t ht]

theorem centralizer_s_le {B T I : Subgroup G} (h : Setup710 B T I)
    (hs : IsPGroup 2 ↥(sOf B T I) ∧ ¬ 2 ∣ (sOf B T I).relIndex (pOf B T I)) :
    yOf B T I ⊓ Subgroup.centralizer (sOf B T I : Set G) ≤ pOf B T I := by
  intro r hr
  by_contra hrP
  have hrD : r ∈ dOf B T I := hr
  have hDP : ¬ dOf B T I ≤ pOf B T I := fun hle => hrP (hle hrD)
  have hE : ¬ eOf B T I ≤ pOf B T I := fun hE => hDP ((dOf_le_eOf B T I).trans hE)
  have h3 : 3 ∣ Nat.card (eOf B T I) := by
    by_contra hn
    exact hE (Lemma85Aux.le_glaPPrimeCoreOf_of_normalizes Nat.prime_three (eOf_le_yOf B T I)
      (y_le_normalizer_eOf hs) hn)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥(eOf B T I) := Fintype.ofFinite _
  obtain ⟨x', hx'⟩ := exists_prime_orderOf_dvd_card (G := ↥(eOf B T I)) 3
    (by rwa [← Nat.card_eq_fintype_card])
  have hx3 : (x' : G) ^ (3 ^ 1) = 1 := by
    have := pow_orderOf_eq_one x'
    rw [hx'] at this
    simpa using congrArg Subtype.val this
  have hxP : (x' : G) ∉ pOf B T I := by
    intro hxP
    have := Subgroup.orderOf_dvd_natCard _ hxP
    rw [Subgroup.orderOf_coe, hx'] at this
    exact not_three_dvd_card_pOf B T I this
  obtain ⟨z, hz, r', hr'D, ⟨k, hrk⟩, hxe⟩ := sylow_lift (p := 3) (M := eOf B T I)
    (Z := pOf B T I) (N₀ := dOf B T I) (dOf_le_eOf B T I) (pOf_le_eOf B T I)
    ((eOf_le_yOf B T I).trans (y_le_normalizer_pOf B T I)) (not_three_dvd_card_pOf B T I)
    (by rw [sup_comm]; exact le_rfl) x'.2 hx3
  have hr'P : r' ∉ pOf B T I := fun hr'P => hxP (by
    rw [hxe]
    exact (pOf B T I).mul_mem ((pOf B T I).mul_mem hz hr'P) ((pOf B T I).inv_mem hz))
  obtain ⟨y, hy, hyB⟩ := exists_conj_mem_B h (dOf_le_yOf B T I hr'D) hrk
  have hbE : y * r' * y⁻¹ ∈ eOf B T I :=
    (Subgroup.mem_normalizer_iff.1 (y_le_normalizer_eOf hs hy) r').1 (dOf_le_eOf B T I hr'D)
  have hb1 := eq_one_of_mem_B_eOf h hs hyB hbE
  have : r' = y⁻¹ * (y * r' * y⁻¹) * y := by group
  rw [hb1] at this
  simp at this
  exact hr'P (this ▸ (pOf B T I).one_mem)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

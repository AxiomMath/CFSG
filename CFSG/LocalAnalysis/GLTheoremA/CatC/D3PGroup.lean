module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace D3P

open CFSG.Open

variable {G : Type*} [Group G]

theorem exists_min_invariant [Finite G] (E T : Subgroup G) (hT : T ≠ ⊥)
    (hnorm : E ≤ Subgroup.normalizer (T : Set G)) :
    ∃ H : Subgroup G, H ≠ ⊥ ∧ H ≤ T ∧ E ≤ Subgroup.normalizer (H : Set G) ∧
      ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H := by
  classical
  let S : Set (Subgroup G) := {H | H ≠ ⊥ ∧ H ≤ T ∧ E ≤ Subgroup.normalizer (H : Set G)}
  have hne : S.Nonempty := ⟨T, hT, le_rfl, hnorm⟩
  obtain ⟨H, hH, hmin⟩ := wellFounded_lt.has_min S hne
  refine ⟨H, hH.1, hH.2.1, hH.2.2, fun H' h1 h2 h3 => ?_⟩
  by_contra hne'
  exact hmin H' ⟨h1, h2.trans hH.2.1, h3⟩ (lt_of_le_of_ne h2 hne')

theorem le_normalizer_of_forward (E C : Subgroup G) (h : ∀ e ∈ E, ∀ c ∈ C, e * c * e⁻¹ ∈ C) :
    E ≤ Subgroup.normalizer (C : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => h e he c hc, fun hc => ?_⟩
  have := h e⁻¹ (E.inv_mem he) _ hc
  simpa [mul_assoc] using this

theorem exists_central_involution {H : Subgroup G} [Finite G] (hH2 : IsPGroup 2 H) (hH : H ≠ ⊥) :
    ∃ z ∈ H, z ≠ 1 ∧ z * z = 1 ∧ ∀ y ∈ H, z * y = y * z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hH
  haveI := hH2.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center H) := by
    obtain ⟨k, hk⟩ := (hH2.to_subgroup (Subgroup.center H)).exists_card_eq
    haveI : Nontrivial (Subgroup.center H) := inferInstance
    have h1 : 1 < Nat.card (Subgroup.center H) := Finite.one_lt_card
    rw [hk] at h1 ⊢
    have hk0 : k ≠ 0 := by rintro rfl; simp at h1
    exact dvd_pow_self 2 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  refine ⟨((z : H) : G), (z : H).2, ?_, ?_, fun y hy => ?_⟩
  · intro h
    have : (z : H) = 1 := Subtype.ext h
    have h2 : z = 1 := Subtype.ext this
    rw [h2, orderOf_one] at hz
    omega
  · have : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have h2 := congrArg (fun w : Subgroup.center H => ((w : H) : G)) this
    simpa [pow_two] using h2
  · have := (Subgroup.mem_center_iff.1 z.2) ⟨y, hy⟩
    simpa using congrArg Subtype.val this.symm

def centralInvol (H : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ H ∧ x * x = 1 ∧ ∀ y ∈ H, x * y = y * x}
  one_mem' := ⟨H.one_mem, by simp, fun y _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haH, ha2, haC⟩ ⟨hbH, hb2, hbC⟩
    refine ⟨H.mul_mem haH hbH, ?_, fun y hy => ?_⟩
    · have hba : b * a = a * b := (haC b hbH).symm
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hba]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    · calc a * b * y = a * (b * y) := mul_assoc _ _ _
        _ = a * (y * b) := by rw [hbC y hy]
        _ = (a * y) * b := (mul_assoc _ _ _).symm
        _ = (y * a) * b := by rw [haC y hy]
        _ = y * (a * b) := mul_assoc _ _ _
  inv_mem' := by
    rintro a ⟨haH, ha2, haC⟩
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    refine ⟨H.inv_mem haH, ?_, fun y hy => ?_⟩
    · rw [hinv, ha2]
    · rw [hinv]; exact haC y hy

theorem conj_mem_of_normalizer {H : Subgroup G} {e : G} (he : e ∈ Subgroup.normalizer (H : Set G))
    {x : G} (hx : x ∈ H) : e * x * e⁻¹ ∈ H :=
  (Subgroup.mem_normalizer_iff.1 he x).1 hx

theorem conj_inv_mem_of_normalizer {H : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H) : e⁻¹ * x * e ∈ H := by
  have h := (Subgroup.mem_normalizer_iff.1 he (e⁻¹ * x * e)).2
  have : e * (e⁻¹ * x * e) * e⁻¹ = x := by group
  rw [this] at h
  exact h hx

theorem min_invariant_elemAbelian [Finite G] {E H : Subgroup G} (hH2 : IsPGroup 2 H) (hH : H ≠ ⊥)
    (hnorm : E ≤ Subgroup.normalizer (H : Set G))
    (hmin : ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H) :
    ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x := by
  obtain ⟨z, hzH, hz1, hz2, hzC⟩ := exists_central_involution hH2 hH
  have hZne : centralInvol H ≠ ⊥ := by
    intro h
    have : z ∈ centralInvol H := ⟨hzH, hz2, hzC⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  have hZle : centralInvol H ≤ H := fun x hx => hx.1
  have hZnorm : E ≤ Subgroup.normalizer (centralInvol H : Set G) := by
    refine le_normalizer_of_forward E _ fun e he c hc => ?_
    obtain ⟨hcH, hc2, hcC⟩ := hc
    refine ⟨conj_mem_of_normalizer (hnorm he) hcH, ?_, fun y hy => ?_⟩
    · calc e * c * e⁻¹ * (e * c * e⁻¹) = e * (c * c) * e⁻¹ := by group
        _ = 1 := by rw [hc2]; group
    · have hy' : e⁻¹ * y * e ∈ H := conj_inv_mem_of_normalizer (hnorm he) hy
      have h1 := hcC _ hy'
      calc e * c * e⁻¹ * y = e * (c * (e⁻¹ * y * e)) * e⁻¹ := by group
        _ = e * ((e⁻¹ * y * e) * c) * e⁻¹ := by rw [h1]
        _ = y * (e * c * e⁻¹) := by group
  have hZH := hmin _ hZne hZle hZnorm
  intro x hx
  have : x ∈ centralInvol H := by rw [hZH]; exact hx
  exact ⟨this.2.1, this.2.2⟩

theorem comm_of_elemAbelian {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  have h := hE.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩
  simpa using congrArg Subtype.val h

theorem min_invariant_fpf [Finite G] {E H : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : E ≤ Subgroup.normalizer (H : Set G))
    (hmin : ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H)
    {e : G} (he : e ∈ E) (hec : e ∉ Subgroup.centralizer (H : Set G)) :
    ∀ x ∈ H, e * x = x * e → x = 1 := by
  set C : Subgroup G := H ⊓ Subgroup.centralizer ({e} : Set G) with hC
  have hCnorm : E ≤ Subgroup.normalizer (C : Set G) := by
    refine le_normalizer_of_forward E C fun e' he' c hc => ?_
    obtain ⟨hcH, hcc⟩ := hc
    have hcc' : e * c = c * e := Subgroup.mem_centralizer_iff.1 hcc e rfl
    have hee' : e * e' = e' * e := comm_of_elemAbelian hE he he'
    refine ⟨conj_mem_of_normalizer (hnorm he') hcH, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc g * (e' * c * e'⁻¹) = e' * (g * c) * e'⁻¹ := by
          calc g * (e' * c * e'⁻¹) = (g * e') * c * e'⁻¹ := by group
            _ = (e' * g) * c * e'⁻¹ := by rw [hee']
            _ = e' * (g * c) * e'⁻¹ := by group
      _ = e' * (c * g) * e'⁻¹ := by rw [hcc']
      _ = (e' * c * e'⁻¹) * g := by
          calc e' * (c * g) * e'⁻¹ = e' * c * (g * e'⁻¹) := by group
            _ = e' * c * (e'⁻¹ * g) := by
                have : g * e'⁻¹ = e'⁻¹ * g := by
                  have h2 := hee'
                  calc g * e'⁻¹ = e'⁻¹ * (e' * g) * e'⁻¹ := by group
                    _ = e'⁻¹ * (g * e') * e'⁻¹ := by rw [← h2]
                    _ = e'⁻¹ * g := by group
                rw [this]
            _ = (e' * c * e'⁻¹) * g := by group
  intro x hx hxe
  by_contra hx1
  have hCne : C ≠ ⊥ := by
    intro h
    have : x ∈ C := ⟨hx, Subgroup.mem_centralizer_iff.2 fun g hg => by
      rw [Set.mem_singleton_iff] at hg; subst hg; exact hxe⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this
  have hCH := hmin C hCne inf_le_left hCnorm
  apply hec
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have : y ∈ C := by rw [hCH]; exact hy
  have h2 := Subgroup.mem_centralizer_iff.1 this.2 e rfl
  exact h2.symm

abbrev commGroupOfComm (H : Subgroup G) (h : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) : CommGroup H :=
  { (inferInstance : Group H) with mul_comm := fun a b => Subtype.ext (h a a.2 b b.2) }

theorem third_of_prod_eq_one_aux {M : Type*} [CommGroup M] (hsq : ∀ w : M, w * w = 1) {x y z : M}
    (h : x * y * z = 1) : z = x * y := by
  have h1 : (x * y) * (x * y) = 1 := by rw [mul_mul_mul_comm, hsq, hsq, one_mul]
  calc z = z * ((x * y) * (x * y)) := by rw [h1, mul_one]
    _ = (x * y * z) * (x * y) := by ac_rfl
    _ = x * y := by rw [h, one_mul]

theorem third_of_prod_eq_one {H : Subgroup G}
    (hex : ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x) {x y z : G} (hx : x ∈ H) (hy : y ∈ H)
    (hz : z ∈ H) (h : x * y * z = 1) : z = x * y := by
  letI := commGroupOfComm H fun a ha b hb => (hex a ha).2 b hb
  have hsq : ∀ w : H, w * w = 1 := fun w => Subtype.ext (hex w w.2).1
  have h' : (⟨x, hx⟩ : H) * ⟨y, hy⟩ * ⟨z, hz⟩ = 1 := Subtype.ext h
  exact congrArg Subtype.val (third_of_prod_eq_one_aux hsq h')

theorem eq_of_mul_eq_one_exp2 {H : Subgroup G}
    (hex : ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x) {p q : G} (hp : p ∈ H) (hq : q ∈ H)
    (h : p * q = 1) : p = q := by
  have h1 := third_of_prod_eq_one hex hp H.one_mem hq (by simpa using h)
  simpa using h1.symm

theorem min_invariant_norm [Finite G] {E H : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : E ≤ Subgroup.normalizer (H : Set G))
    (hmin : ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H)
    (hex : ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x)
    {e : G} (he : e ∈ E) (hec : e ∉ Subgroup.centralizer (H : Set G)) {u : G} (hu : u ∈ H) :
    u * (e * u * e⁻¹) * (e * (e * u * e⁻¹) * e⁻¹) = 1 := by
  have hfpf := min_invariant_fpf hE hnorm hmin he hec
  have h3 : e ^ 3 = 1 := hE.2 e he
  have hu1 : e * u * e⁻¹ ∈ H := conj_mem_of_normalizer (hnorm he) hu
  have hu2 : e * (e * u * e⁻¹) * e⁻¹ ∈ H := conj_mem_of_normalizer (hnorm he) hu1
  set u1 := e * u * e⁻¹ with hu1def
  set u2 := e * u1 * e⁻¹ with hu2def
  set N := u * u1 * u2 with hN
  have hNH : N ∈ H := H.mul_mem (H.mul_mem hu hu1) hu2
  have heu2 : e * u2 * e⁻¹ = u := by
    have h3' : e * e * e = 1 := by rw [← pow_three']; exact h3
    have : e * u2 * e⁻¹ = (e * e * e) * u * (e * e * e)⁻¹ := by simp only [hu2def, hu1def]; group
    rw [this, h3']; group
  have hNe : e * N * e⁻¹ = N := by
    calc e * N * e⁻¹ = (e * u * e⁻¹) * (e * u1 * e⁻¹) * (e * u2 * e⁻¹) := by simp only [hN]; group
      _ = u1 * u2 * u := by rw [heu2]
      _ = u * u1 * u2 := by
          have h := (hex (u1 * u2) (H.mul_mem hu1 hu2)).2 u hu
          exact h.trans (mul_assoc u u1 u2).symm
  have hcom : e * N = N * e := by
    calc e * N = e * N * e⁻¹ * e := by group
      _ = N * e := by rw [hNe]
  exact hfpf N hNH hcom

theorem final_aux {M : Type*} [CommGroup M] (hsq : ∀ w : M, w * w = 1) {u R P Q : M}
    (h : u * R * ((u * P) * (Q * R)) = 1) : P * Q = 1 := by
  calc P * Q = (u * u) * (R * R) * (P * Q) := by rw [hsq u, hsq R, one_mul, one_mul]
    _ = u * R * ((u * P) * (Q * R)) := by ac_rfl
    _ = 1 := h

theorem min_invariant_conj_eq [Finite G] {E H : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : E ≤ Subgroup.normalizer (H : Set G))
    (hmin : ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H)
    (hex : ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x)
    {b : G} (hb : b ∈ E) (hbc : b ∉ Subgroup.centralizer (H : Set G))
    {e : G} (he : e ∈ E) (hec : e ∉ Subgroup.centralizer (H : Set G))
    (hgc : e * b ∉ Subgroup.centralizer (H : Set G)) {u : G} (hu : u ∈ H) :
    e * u * e⁻¹ = b * u * b⁻¹ := by
  have hbe : e * b = b * e := comm_of_elemAbelian hE he hb
  have hgE : e * b ∈ E := E.mul_mem he hb
  have hPH : e * u * e⁻¹ ∈ H := conj_mem_of_normalizer (hnorm he) hu
  have hQH : b * u * b⁻¹ ∈ H := conj_mem_of_normalizer (hnorm hb) hu
  have hRH : e * (b * u * b⁻¹) * e⁻¹ ∈ H := conj_mem_of_normalizer (hnorm he) hQH
  have Ne_u := min_invariant_norm hE hnorm hmin hex he hec hu
  have Ne_Q := min_invariant_norm hE hnorm hmin hex he hec hQH
  have Nb_u := min_invariant_norm hE hnorm hmin hex hb hbc hu
  have Ng_u := min_invariant_norm hE hnorm hmin hex hgE hgc hu
  have hgR : e * b * u * (e * b)⁻¹ = e * (b * u * b⁻¹) * e⁻¹ := by group
  rw [hgR] at Ng_u
  have hQ2H : b * (b * u * b⁻¹) * b⁻¹ ∈ H := conj_mem_of_normalizer (hnorm hb) hQH
  have hQ2 : b * (b * u * b⁻¹) * b⁻¹ = u * (b * u * b⁻¹) :=
    third_of_prod_eq_one hex hu hQH hQ2H Nb_u
  have hP2H : e * (e * u * e⁻¹) * e⁻¹ ∈ H := conj_mem_of_normalizer (hnorm he) hPH
  have hφu : e * (e * u * e⁻¹) * e⁻¹ = u * (e * u * e⁻¹) :=
    third_of_prod_eq_one hex hu hPH hP2H Ne_u
  have hφQ : e * (e * (b * u * b⁻¹) * e⁻¹) * e⁻¹ =
      (b * u * b⁻¹) * (e * (b * u * b⁻¹) * e⁻¹) :=
    third_of_prod_eq_one hex hQH hRH (conj_mem_of_normalizer (hnorm he) hRH) Ne_Q
  have hbe' : b * e = e * b := hbe.symm
  have hS : e * b * (e * (b * u * b⁻¹) * e⁻¹) * (e * b)⁻¹ =
      (u * (e * u * e⁻¹)) * ((b * u * b⁻¹) * (e * (b * u * b⁻¹) * e⁻¹)) := by
    calc e * b * (e * (b * u * b⁻¹) * e⁻¹) * (e * b)⁻¹
        = e * (b * e) * (b * u * b⁻¹) * (b * e)⁻¹ * e⁻¹ := by group
      _ = e * (e * b) * (b * u * b⁻¹) * (e * b)⁻¹ * e⁻¹ := by rw [hbe']
      _ = e * (e * (b * (b * u * b⁻¹) * b⁻¹) * e⁻¹) * e⁻¹ := by group
      _ = e * (e * (u * (b * u * b⁻¹)) * e⁻¹) * e⁻¹ := by rw [hQ2]
      _ = (e * (e * u * e⁻¹) * e⁻¹) * (e * (e * (b * u * b⁻¹) * e⁻¹) * e⁻¹) := by group
      _ = _ := by rw [hφu, hφQ]
  rw [hS] at Ng_u
  letI := commGroupOfComm H fun a ha b hb => (hex a ha).2 b hb
  have hsq : ∀ w : H, w * w = 1 := fun w => Subtype.ext (hex w w.2).1
  have hfin : (⟨u, hu⟩ : H) * ⟨e * (b * u * b⁻¹) * e⁻¹, hRH⟩ *
      ((⟨u, hu⟩ * ⟨e * u * e⁻¹, hPH⟩) * (⟨b * u * b⁻¹, hQH⟩ * ⟨e * (b * u * b⁻¹) * e⁻¹, hRH⟩)) = 1 :=
    Subtype.ext Ng_u
  have h1 := final_aux hsq hfin
  have h2 : (e * u * e⁻¹) * (b * u * b⁻¹) = 1 := congrArg Subtype.val h1
  exact eq_of_mul_eq_one_exp2 hex hPH hQH h2

theorem min_invariant_conj_cases [Finite G] {E H : Subgroup G} (hE : IsElemAbelian 3 E)
    (hnorm : E ≤ Subgroup.normalizer (H : Set G))
    (hmin : ∀ H' : Subgroup G, H' ≠ ⊥ → H' ≤ H → E ≤ Subgroup.normalizer (H' : Set G) → H' = H)
    (hex : ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x)
    {b : G} (hb : b ∈ E) (hbc : b ∉ Subgroup.centralizer (H : Set G)) {e : G} (he : e ∈ E) :
    (∀ u ∈ H, e * u * e⁻¹ = u) ∨ (∀ u ∈ H, e * u * e⁻¹ = b * u * b⁻¹) ∨
      (∀ u ∈ H, e * u * e⁻¹ = b⁻¹ * u * b) := by
  by_cases hec : e ∈ Subgroup.centralizer (H : Set G)
  · left
    intro u hu
    have h := Subgroup.mem_centralizer_iff.1 hec u hu
    calc e * u * e⁻¹ = u * e * e⁻¹ := by rw [← h]
      _ = u := by group
  by_cases hgc : e * b ∈ Subgroup.centralizer (H : Set G)
  · right; right
    intro u hu
    have hw : b⁻¹ * u * b ∈ H := conj_inv_mem_of_normalizer (hnorm hb) hu
    have h := Subgroup.mem_centralizer_iff.1 hgc _ hw
    calc e * u * e⁻¹ = (e * b) * (b⁻¹ * u * b) * (e * b)⁻¹ := by group
      _ = (b⁻¹ * u * b) * (e * b) * (e * b)⁻¹ := by rw [← h]
      _ = b⁻¹ * u * b := by group
  · right; left
    intro u hu
    exact min_invariant_conj_eq hE hnorm hmin hex hb hbc he hec hgc hu

end D3P

end CFSG.LocalAnalysis.GLTheoremA

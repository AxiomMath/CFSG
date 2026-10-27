module

public import Certificates.Data.Kernel.AE6CertE.Keys
public import Certificates.Data.AE6CertE
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.AE6CertE

open Certificates.AE6CertEK Certificates.AE6Model Certificates.AE6CertE CFSG.KC.Enum CFSG.KS
  CFSG.KS.Raw

@[expose] def permN (σ : Equiv.Perm (Fin 360)) (o : ℕ) : ℕ :=
  if h : o < 360 then (σ ⟨o, h⟩).val else o

theorem permN_lt (σ : Equiv.Perm (Fin 360)) {o : ℕ} (h : o < 360) : permN σ o < 360 := by
  rw [permN, dif_pos h]
  exact (σ _).isLt

theorem permN_mul (σ τ : Equiv.Perm (Fin 360)) (o : ℕ) :
    permN (σ * τ) o = permN σ (permN τ o) := by
  by_cases h : o < 360
  · have e1 : permN τ o = (τ ⟨o, h⟩).val := by rw [permN, dif_pos h]
    rw [e1]
    unfold permN
    rw [dif_pos h, dif_pos (τ _).isLt]
    rfl
  · have e1 : permN τ o = o := by rw [permN, dif_neg h]
    rw [e1]
    unfold permN
    rw [dif_neg h, dif_neg h]

theorem permN_one (o : ℕ) : permN 1 o = o := by
  by_cases h : o < 360
  · rw [permN, dif_pos h]
    rfl
  · rw [permN, dif_neg h]

theorem permN_inv_cancel (σ : Equiv.Perm (Fin 360)) (o : ℕ) : permN σ (permN σ⁻¹ o) = o := by
  rw [← permN_mul, mul_inv_cancel, permN_one]

theorem permN_injective (σ : Equiv.Perm (Fin 360)) : Function.Injective (permN σ) := by
  intro a b h
  have e := congrArg (permN σ⁻¹) h
  rwa [← permN_mul, ← permN_mul, inv_mul_cancel, permN_one, permN_one] at e

@[expose] def keyM (O : List ℕ) (g : Equiv.Perm (Fin 360)) : ℕ :=
  (O.map fun o => 2 ^ permN g⁻¹ o).sum

@[expose] def stabO (O : List ℕ) : Subgroup (Equiv.Perm (Fin 360)) where
  carrier := {σ | ∀ a, permN σ a ∈ O ↔ a ∈ O}
  mul_mem' := fun {σ τ} hσ hτ a => by
    rw [permN_mul]
    exact (hσ _).trans (hτ a)
  one_mem' := fun a => by rw [permN_one]
  inv_mem' := fun {σ} hσ a => by
    have e := hσ (permN σ⁻¹ a)
    rw [permN_inv_cancel] at e
    exact e.symm

theorem keyM_mul {O : List ℕ} (hO : O.Nodup) {u : Equiv.Perm (Fin 360)} (hu : u ∈ stabO O)
    (g : Equiv.Perm (Fin 360)) : keyM O (u * g) = keyM O g := by
  have hu' : u⁻¹ ∈ stabO O := (stabO O).inv_mem hu
  have hp : (O.map (permN u⁻¹)).Perm O := by
    rw [List.perm_ext_iff_of_nodup (hO.map (permN_injective _)) hO]
    intro a
    rw [List.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact (hu' b).2 hb
    · intro ha
      refine ⟨permN u a, (hu a).2 ha, ?_⟩
      rw [← permN_mul, inv_mul_cancel, permN_one]
  have e : O.map (fun o => 2 ^ permN (u * g)⁻¹ o) =
      (O.map (permN u⁻¹)).map (fun o => 2 ^ permN g⁻¹ o) := by
    rw [List.map_map]
    refine List.map_congr_left fun o _ => ?_
    rw [Function.comp_apply, mul_inv_rev, permN_mul]
  unfold keyM
  rw [e]
  exact (hp.map _).sum_eq

theorem bool_rec_eq_true {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd (h : false = true) Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem allRec {f : ℕ → Bool} : ∀ {n : ℕ},
    Nat.rec (motive := fun _ => Bool) true (fun x ih => Bool.rec (motive := fun _ => Bool) false ih
      (f x)) n = true → ∀ x < n, f x = true
  | 0, _, x, hx => absurd hx (Nat.not_lt_zero _)
  | n + 1, h, x, hx => by
    obtain ⟨h1, h2⟩ := bool_rec_eq_true h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
    · exact allRec h2 x hx
    · exact h1

theorem memK_iff (x : ℕ) : ∀ L : List ℕ, memK x L = true ↔ x ∈ L
  | [] => by
    constructor
    · intro h
      exact absurd (h : false = true) Bool.false_ne_true
    · intro h
      exact absurd h List.not_mem_nil
  | b :: L => by
    have e : memK x (b :: L) =
        Bool.rec (motive := fun _ => Bool) (memK x L) true (Nat.beq x b) := rfl
    rw [e, List.mem_cons, ← memK_iff x L]
    cases hb : Nat.beq x b
    · have hne : x ≠ b := Nat.ne_of_beq_eq_false hb
      simp only [hne, false_or]
    · have heq : x = b := Nat.eq_of_beq_eq_true hb
      simp only [heq, true_or, iff_true]

theorem notInK_sound (a : ℕ) : ∀ L : List ℕ, notInK a L = true → a ∉ L
  | [], _ => List.not_mem_nil
  | b :: L, h => by
    obtain ⟨h1, h2⟩ := bool_rec_eq_true (b := notInK a L) h
    have hne : a ≠ b := by
      intro e
      rw [e, Nat.beq_refl] at h1
      exact absurd (h1 : false = true) Bool.false_ne_true
    rw [List.mem_cons, not_or]
    exact ⟨hne, notInK_sound a L h2⟩

theorem nodupK_sound : ∀ L : List ℕ, nodupK L = true → L.Nodup
  | [], _ => List.nodup_nil
  | a :: L, h => by
    obtain ⟨h1, h2⟩ := bool_rec_eq_true (b := nodupK L) h
    exact List.nodup_cons.2 ⟨notInK_sound a L h1, nodupK_sound L h2⟩

variable {T : List ℕ} {G : List (Equiv.Perm (Fin 360))}

theorem aeWord_cons (a : ℕ) (v : List ℕ) : aeWord G (a :: v) = G.getD a 1 * aeWord G v := by
  simp [aeWord]

theorem aeWord_append (v v' : List ℕ) : aeWord G (v ++ v') = aeWord G v * aeWord G v' := by
  simp [aeWord]

theorem aeWord_nil : aeWord G [] = 1 := by simp [aeWord]

theorem aeWord_mem {H : Subgroup (Equiv.Perm (Fin 360))} {v : List ℕ}
    (h : ∀ a ∈ v, G.getD a 1 ∈ H) : aeWord G v ∈ H :=
  H.list_prod_mem fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact h a ha

@[expose] def Letters (T : List ℕ) (G : List (Equiv.Perm (Fin 360))) : Prop :=
  ∀ a < 8, Orb.PRep 360 9 (getK T a) (G.getD a 1) ∧ (G.getD a 1)⁻¹ = G.getD a 1

theorem wlk_word (hT : Letters T G) : ∀ v : List ℕ, (∀ a ∈ v, a < 8) →
    ∀ p < 360, wlkK (convK T v) p = permN (aeWord G v)⁻¹ p
  | [], _, p, _ => by
    rw [aeWord_nil, inv_one, permN_one]
    rfl
  | a :: v, hv, p, hp => by
    have ha := hv a List.mem_cons_self
    have e1 : pg 9 (mask 9) (getK T a) p = permN (G.getD a 1)⁻¹ p := by
      rw [(hT a ha).2, permN, dif_pos hp]
      exact (hT a ha).1 ⟨p, hp⟩
    have e2 : wlkK (convK T (a :: v)) p = wlkK (convK T v) (pg 9 (mask 9) (getK T a) p) := rfl
    rw [e2, e1, wlk_word hT v (fun b hb => hv b (List.mem_cons_of_mem _ hb)) _ (permN_lt _ hp),
      aeWord_cons, mul_inv_rev, permN_mul]

theorem keyK_eq (hT : Letters T G) {v : List ℕ} (hv : ∀ a ∈ v, a < 8) :
    ∀ O : List ℕ, (∀ o ∈ O, o < 360) → keyK O (convK T v) = keyM O (aeWord G v)
  | [], _ => rfl
  | o :: O, hO => by
    have e : keyK (o :: O) (convK T v) =
        Nat.add (Nat.shiftLeft 1 (wlkK (convK T v) o)) (keyK O (convK T v)) := rfl
    have e2 : Nat.shiftLeft 1 (wlkK (convK T v) o) = 2 ^ wlkK (convK T v) o :=
      Nat.one_shiftLeft _
    rw [e, e2, keyK_eq hT hv O (fun o' h => hO o' (List.mem_cons_of_mem _ h)),
      wlk_word hT v hv o (hO o List.mem_cons_self)]
    simp [keyM, Nat.add_eq]

theorem invarK_spec {X : ℕ} {O : List ℕ} {n : ℕ} (h : invarK X O n = true) :
    ∀ x < n, Bool.beq (memK (pg 9 (mask 9) X x) O) (memK x O) = true :=
  allRec h

theorem invoK_spec {X : ℕ} {n : ℕ} (h : invoK X n = true) :
    ∀ x < n, Nat.beq (pg 9 (mask 9) X (pg 9 (mask 9) X x)) x = true :=
  allRec h

theorem mem_stabO_of_invarK {X : ℕ} {σ : Equiv.Perm (Fin 360)} (hX : Orb.PRep 360 9 X σ)
    {O : List ℕ} (h : invarK X O 360 = true) : σ ∈ stabO O := by
  intro a
  by_cases ha : a < 360
  · have h1 := invarK_spec h a ha
    have e : memK (pg 9 (mask 9) X a) O = memK a O := by
      revert h1
      cases memK (pg 9 (mask 9) X a) O <;> cases memK a O <;> decide
    rw [hX ⟨a, ha⟩] at e
    rw [permN, dif_pos ha, ← memK_iff, ← memK_iff, e]
  · rw [permN, dif_neg ha]

theorem inv_of_invoK {X : ℕ} {σ : Equiv.Perm (Fin 360)} (hX : Orb.PRep 360 9 X σ)
    (h : invoK X 360 = true) : σ⁻¹ = σ := by
  refine inv_eq_of_mul_eq_one_left (Equiv.ext fun x => ?_)
  have h1 := invoK_spec h x.val x.isLt
  have e : pg 9 (mask 9) X (pg 9 (mask 9) X x.val) = x.val := Nat.eq_of_beq_eq_true h1
  rw [hX x] at e
  rw [hX ⟨_, (σ x).isLt⟩] at e
  exact Fin.ext e

theorem cover_of_inj {Γ : Type*} [Group Γ] [Finite Γ] {U V : Subgroup Γ} (hUV : U ≤ V) {n : ℕ}
    (hc : Nat.card V = n * Nat.card U) (y : ℕ → Γ) (hy : ∀ j < n, y j ∈ V)
    (hinj : ∀ a < n, ∀ b < n, y a * (y b)⁻¹ ∈ U → a = b) :
    ∀ g ∈ V, ∃ j < n, g * (y j)⁻¹ ∈ U := by
  intro g hg
  set U' := U.subgroupOf V
  have hU' : Nat.card U' = Nat.card U := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hidx : U'.index = n := by
    have h1 := U'.card_mul_index
    rw [hU', hc, Nat.mul_comm n] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  let f : Fin n → Quotient (QuotientGroup.rightRel U') := fun j => ⟦⟨y j, hy j j.2⟩⟧
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := QuotientGroup.rightRel_apply.mp (Quotient.exact hab)
    rw [Subgroup.mem_subgroupOf] at h1
    exact Fin.ext (hinj b b.2 a a.2 (by simpa using h1)).symm
  have hQ : Nat.card (Quotient (QuotientGroup.rightRel U')) = n := by
    rw [Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel U'), ← hidx]
    rfl
  have hb := hf.bijective_of_nat_card_le (by rw [hQ, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨j, hj⟩ := hb.2 ⟦⟨g, hg⟩⟧
  have h1 := QuotientGroup.rightRel_apply.mp (Quotient.exact hj)
  rw [Subgroup.mem_subgroupOf] at h1
  exact ⟨j, j.2, by simpa using h1⟩

section Keys

variable {O : List ℕ} {U V : Subgroup (Equiv.Perm (Fin 360))} {W : ℕ → List ℕ} {Lk : List ℕ}

structure KeyData (T : List ℕ) (G : List (Equiv.Perm (Fin 360))) (O : List ℕ)
    (U V : Subgroup (Equiv.Perm (Fin 360))) (W : ℕ → List ℕ) (Lk : List ℕ) : Prop where
  letters : Letters T G
  nodup : O.Nodup
  lt : ∀ o ∈ O, o < 360
  stab : U ≤ stabO O
  le : U ≤ V
  card : Nat.card V = 315 * Nat.card U
  lk : ∀ a ∈ Lk, a < 8 ∧ G.getD a 1 ∈ V
  words : ∀ j < 315, ∀ a ∈ W j, a ∈ Lk
  keys : keysK T O W 315 = true

theorem KeyData.word_lt (hD : KeyData T G O U V W Lk) {j : ℕ} (hj : j < 315) :
    ∀ a ∈ W j, a < 8 := fun a ha => (hD.lk a (hD.words j hj a ha)).1

theorem KeyData.word_mem (hD : KeyData T G O U V W Lk) {j : ℕ} (hj : j < 315) :
    aeWord G (W j) ∈ V :=
  aeWord_mem fun a ha => (hD.lk a (hD.words j hj a ha)).2

theorem KeyData.key_inj (hD : KeyData T G O U V W Lk) {a b : ℕ} (ha : a < 315) (hb : b < 315)
    (h : keyM O (aeWord G (W a)) = keyM O (aeWord G (W b))) : a = b := by
  have hn := nodupK_sound _ hD.keys
  rw [← keyK_eq hD.letters (hD.word_lt ha) O hD.lt,
    ← keyK_eq hD.letters (hD.word_lt hb) O hD.lt] at h
  exact List.inj_on_of_nodup_map hn (List.mem_range.2 ha) (List.mem_range.2 hb) h

theorem keyM_of_mem (hO : O.Nodup) (hU : U ≤ stabO O) {g y : Equiv.Perm (Fin 360)}
    (h : g * y⁻¹ ∈ U) : keyM O g = keyM O y := by
  have e : g = g * y⁻¹ * y := by group
  rw [e, keyM_mul hO (hU h)]

theorem KeyData.cover (hD : KeyData T G O U V W Lk) :
    ∀ g ∈ V, ∃ j < 315, g * (aeWord G (W j))⁻¹ ∈ U :=
  cover_of_inj hD.le hD.card (fun j => aeWord G (W j)) (fun j hj => hD.word_mem hj) fun a ha b hb h =>
    hD.key_inj ha hb (keyM_of_mem hD.nodup hD.stab h)

theorem KeyData.sep (hD : KeyData T G O U V W Lk) {g h : Equiv.Perm (Fin 360)} (hg : g ∈ V)
    (hh : h ∈ V) (hk : keyM O g = keyM O h) : g * h⁻¹ ∈ U := by
  obtain ⟨a, ha, hga⟩ := hD.cover g hg
  obtain ⟨b, hb, hhb⟩ := hD.cover h hh
  have hab : a = b := hD.key_inj ha hb (by
    rw [← keyM_of_mem hD.nodup hD.stab hga, ← keyM_of_mem hD.nodup hD.stab hhb, hk])
  subst hab
  have e : g * h⁻¹ = (g * (aeWord G (W a))⁻¹) * (h * (aeWord G (W a))⁻¹)⁻¹ := by group
  rw [e]
  exact U.mul_mem hga (U.inv_mem hhb)

theorem KeyData.graph (hD : KeyData T G O U V W Lk) {j : ℕ} (hj : j < 315) {x : ℕ}
    (hx : x ∈ Lk) : ∃ j' < 315, aeWord G (W j) * G.getD x 1 * (aeWord G (W j'))⁻¹ ∈ U :=
  hD.cover _ (V.mul_mem (hD.word_mem hj) (hD.lk x hx).2)

theorem expK_spec (hU : ∀ d < 4, G.getD (d + d) 1 ∈ U) (w : List ℕ) (hw : ∀ a ∈ w, a < 8) :
    ∀ (f x : ℕ), (∀ a ∈ expK w f x, a < 8) ∧
      aeWord G (expK w f x) ∈ U ⊔ Subgroup.zpowers (aeWord G w)
  | 0, x => ⟨fun _ h => absurd h List.not_mem_nil, by
      rw [show expK w 0 x = [] from rfl, aeWord_nil]
      exact Subgroup.one_mem _⟩
  | f + 1, x => by
    have e : expK w (f + 1) x = Nat.rec (motive := fun _ => List ℕ) []
        (fun d _ => List.append (mvK w d) (expK w f (Nat.shiftRight x 3))) (Nat.land x 7) := rfl
    obtain ⟨ih1, ih2⟩ := expK_spec hU w hw f (Nat.shiftRight x 3)
    rw [e]
    generalize Nat.land x 7 = d
    cases d with
    | zero => exact ⟨fun _ h => absurd h List.not_mem_nil, by
        rw [show (Nat.rec (motive := fun _ => List ℕ) [] _ 0 : List ℕ) = [] from rfl, aeWord_nil]
        exact Subgroup.one_mem _⟩
    | succ d =>
      have e2 : (Nat.rec (motive := fun _ => List ℕ) []
          (fun d _ => List.append (mvK w d) (expK w f (Nat.shiftRight x 3))) (d + 1) : List ℕ) =
          mvK w d ++ expK w f (Nat.shiftRight x 3) := rfl
      rw [e2, aeWord_append]
      have hm : (∀ a ∈ mvK w d, a < 8) ∧ aeWord G (mvK w d) ∈ U ⊔ Subgroup.zpowers (aeWord G w) := by
        unfold mvK
        cases hlt : Nat.blt d 4
        · cases heq : Nat.beq d 4
          · exact ⟨fun _ h => absurd h List.not_mem_nil, by
              rw [aeWord_nil]
              exact Subgroup.one_mem _⟩
          · exact ⟨hw, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
        · have hd : d < 4 := Nat.le_of_ble_eq_true hlt
          refine ⟨fun a ha => ?_, ?_⟩
          · rw [List.mem_singleton] at ha
            rw [ha, Nat.add_eq]
            omega
          · rw [aeWord_cons, aeWord_nil, mul_one, Nat.add_eq]
            exact Subgroup.mem_sup_left (hU d hd)
      refine ⟨fun a ha => ?_, Subgroup.mul_mem _ hm.2 ih2⟩
      rcases List.mem_append.mp ha with ha | ha
      · exact hm.1 a ha
      · exact ih1 a ha

theorem KeyData.letters_of_paths (hD : KeyData T G O U V W Lk)
    (hU : ∀ d < 4, G.getD (d + d) 1 ∈ U) {F : ℕ → ℕ} {j : ℕ} (hj : j < 315)
    (hp : pathK T O (W j) (F j) = true) :
    ∀ i ∈ W j, G.getD i 1 ∈ U ⊔ Subgroup.zpowers (aeWord G (W j)) := by
  intro i hi
  have hi8 := hD.word_lt hj i hi
  rcases Nat.even_or_odd' i with ⟨t, rfl | rfl⟩
  · have ht : t < 4 := by omega
    have e : 2 * t = t + t := by omega
    rw [e]
    exact Subgroup.mem_sup_left (hU t ht)
  · have ht : t < 4 := by omega
    have h1 := allRec (f := fun t => bIf(memK (Nat.add (Nat.add t t) (nat_lit 1)) (W j),
      Nat.beq (keyK O (convK T (expK (W j) (nat_lit 21) (laneK (F j) t))))
        (keyK O (convK T [Nat.add (Nat.add t t) (nat_lit 1)])), true)) (n := nat_lit 4) hp t ht
    have hm : memK (Nat.add (Nat.add t t) 1) (W j) = true := by
      rw [memK_iff, Nat.add_eq, Nat.add_eq]
      have e : t + t + 1 = 2 * t + 1 := by omega
      rw [e]
      exact hi
    rw [hm] at h1
    have hk := Nat.eq_of_beq_eq_true h1
    have e : Nat.add (Nat.add t t) 1 = 2 * t + 1 := by rw [Nat.add_eq, Nat.add_eq]; omega
    rw [e] at hk
    obtain ⟨hE1, hE2⟩ := expK_spec hU (W j) (hD.word_lt hj) 21 (laneK (F j) t)
    have hL : ∀ a ∈ [2 * t + 1], a < 8 := fun a ha => by
      rw [List.mem_singleton] at ha
      omega
    rw [keyK_eq hD.letters hE1 O hD.lt, keyK_eq hD.letters hL O hD.lt, aeWord_cons, aeWord_nil,
      mul_one] at hk
    set h := aeWord G (expK (W j) 21 (laneK (F j) t))
    have hHV : U ⊔ Subgroup.zpowers (aeWord G (W j)) ≤ V :=
      sup_le hD.le ((Subgroup.zpowers_le).2 (hD.word_mem hj))
    have hs := hD.sep (hD.lk _ (hD.words j hj _ hi)).2 (hHV hE2) hk.symm
    have e2 : G.getD (2 * t + 1) 1 = (G.getD (2 * t + 1) 1 * h⁻¹) * h := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hs) hE2

end Keys

theorem paths_all {O W : _} {F : ℕ → ℕ}
    (h0 : pathsK T O W F 0 63 = true) (h1 : pathsK T O W F 63 63 = true)
    (h2 : pathsK T O W F 126 63 = true) (h3 : pathsK T O W F 189 63 = true)
    (h4 : pathsK T O W F 252 63 = true) : ∀ j < 315, pathK T O (W j) (F j) = true := by
  intro j hj
  have key : ∀ lo, pathsK T O W F lo 63 = true → lo ≤ j → j < lo + 63 →
      pathK T O (W j) (F j) = true := fun lo h hl hu => by
    have := allRec (f := fun s => pathK T O (W (Nat.add lo s)) (F (Nat.add lo s))) (n := 63) h
      (j - lo) (by omega)
    rw [Nat.add_eq, Nat.add_sub_cancel' hl] at this
    exact this
  by_cases a : j < 63
  · exact key 0 h0 (by omega) (by omega)
  by_cases b : j < 126
  · exact key 63 h1 (by omega) (by omega)
  by_cases c : j < 189
  · exact key 126 h2 (by omega) (by omega)
  by_cases d : j < 252
  · exact key 189 h3 (by omega) (by omega)
  · exact key 252 h4 (by omega) (by omega)

end CFSG.KC.AE6CertE

end

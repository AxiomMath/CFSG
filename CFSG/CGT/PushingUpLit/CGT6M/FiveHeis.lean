module

public import CFSG.CGT.PushingUpLit.CGT6M.FiveComm

public section

namespace CFSG.CGT.PushingUpLit.CGT6M

open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mul_pow_pow_comm {c d : MulAut V} (h : c * d = d * c) (m n p q : ℕ) :
    (c ^ m * d ^ n) * (c ^ p * d ^ q) = c ^ (m + p) * d ^ (n + q) := by
  have h1 : d ^ n * c ^ p = c ^ p * d ^ n :=
    ((Commute.pow_pow (show Commute c d from h) p n).eq).symm
  calc (c ^ m * d ^ n) * (c ^ p * d ^ q) = c ^ m * (d ^ n * c ^ p) * d ^ q := by
        simp only [mul_assoc]
    _ = c ^ m * (c ^ p * d ^ n) * d ^ q := by rw [h1]
    _ = c ^ (m + p) * d ^ (n + q) := by
        rw [pow_add, pow_add]
        simp only [mul_assoc]

omit [Finite V] in
theorem commute_pow_mul_pow {c d : MulAut V} (h : c * d = d * c) (a b : ℕ) :
    c * (c ^ a * d ^ b) = (c ^ a * d ^ b) * c :=
  ((Commute.pow_right (Commute.refl c) a).mul_right
    (Commute.pow_right (show Commute c d from h) b)).eq

theorem exists_trivial_elem {c d : MulAut V} (hcd : c * d = d * c) (hc5 : c ^ 5 = 1)
    (hd5 : d ^ 5 = 1) (hV : ∀ v : V, v ^ 2 = 1) (hN : Nat.card (commSub c) = 16) :
    ∃ a b : ℕ, ¬ (5 ∣ a ∧ 5 ∣ b) ∧ commSub c ≤ fixSub (c ^ a * d ^ b) := by
  have hnt : Nontrivial (commSub c) := Finite.one_lt_card_iff_nontrivial.mp (by rw [hN]; norm_num)
  obtain ⟨n₀, hn₀⟩ := exists_ne (1 : commSub c)
  have hmem : ∀ i j : ℕ, ∀ n ∈ commSub c, (c ^ i * d ^ j) n ∈ commSub c := fun i j n hn =>
    apply_mem_commSub (commute_pow_mul_pow hcd i j) hn
  let f : Fin 5 × Fin 5 → commSub c := fun p =>
    ⟨(c ^ (p.1 : ℕ) * d ^ (p.2 : ℕ)) (n₀ : V), hmem _ _ _ n₀.2⟩
  have : Fintype (commSub c) := Fintype.ofFinite _
  have hcard : Fintype.card (commSub c) < Fintype.card (Fin 5 × Fin 5) := by
    rw [← Nat.card_eq_fintype_card, hN]
    simp
  obtain ⟨⟨i, j⟩, ⟨i', j'⟩, hne, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hf' : (c ^ (i : ℕ) * d ^ (j : ℕ)) (n₀ : V) = (c ^ (i' : ℕ) * d ^ (j' : ℕ)) (n₀ : V) :=
    congrArg Subtype.val hf
  have hi := i.isLt
  have hi' := i'.isLt
  have hj := j.isLt
  have hj' := j'.isLt
  refine ⟨(i : ℕ) + (5 - (i' : ℕ)), (j : ℕ) + (5 - (j' : ℕ)), ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    apply hne
    have e1 : (i : ℕ) = i' := by omega
    have e2 : (j : ℕ) = j' := by omega
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · set a : ℕ := (i : ℕ) + (5 - (i' : ℕ)) with ha
    set b : ℕ := (j : ℕ) + (5 - (j' : ℕ)) with hb
    have hfix : (c ^ a * d ^ b) (n₀ : V) = n₀ := by
      have e1 : c ^ a * d ^ b = (c ^ (5 - (i' : ℕ)) * d ^ (5 - (j' : ℕ))) *
          (c ^ (i : ℕ) * d ^ (j : ℕ)) := by
        rw [mul_pow_pow_comm hcd, add_comm (5 - (i' : ℕ)), add_comm (5 - (j' : ℕ))]
      have e2 : (c ^ (5 - (i' : ℕ)) * d ^ (5 - (j' : ℕ))) * (c ^ (i' : ℕ) * d ^ (j' : ℕ)) = 1 := by
        rw [mul_pow_pow_comm hcd, Nat.sub_add_cancel hi'.le, Nat.sub_add_cancel hj'.le, hc5, hd5,
          mul_one]
      calc (c ^ a * d ^ b) (n₀ : V)
          = (c ^ (5 - (i' : ℕ)) * d ^ (5 - (j' : ℕ))) ((c ^ (i : ℕ) * d ^ (j : ℕ)) (n₀ : V)) := by
            rw [e1, MulAut.mul_apply]
        _ = (c ^ (5 - (i' : ℕ)) * d ^ (5 - (j' : ℕ))) ((c ^ (i' : ℕ) * d ^ (j' : ℕ)) (n₀ : V)) := by
            rw [hf']
        _ = ((c ^ (5 - (i' : ℕ)) * d ^ (5 - (j' : ℕ))) * (c ^ (i' : ℕ) * d ^ (j' : ℕ))) (n₀ : V) :=
            rfl
        _ = n₀ := by rw [e2]; rfl
    let M : Subgroup V := commSub c ⊓ fixSub (c ^ a * d ^ b)
    have hMc : ∀ m ∈ M, c m ∈ M := by
      rintro m ⟨hm1, hm2⟩
      refine ⟨apply_mem_commSub rfl hm1, ?_⟩
      have h : c ((c ^ a * d ^ b) m) = (c ^ a * d ^ b) (c m) :=
        congrArg (fun e : MulAut V => e m) (commute_pow_mul_pow hcd a b)
      have hm2' : (c ^ a * d ^ b) m = m := hm2
      show (c ^ a * d ^ b) (c m) = c m
      rw [← h, hm2']
    have hMfix : M ⊓ fixSub c = ⊥ :=
      le_bot_iff.mp (le_trans (inf_le_inf_right _ inf_le_left)
        (le_of_eq (commSub_inf_fixSub_eq_bot (by decide : Odd 5) hc5 hV)))
    have hMle : Nat.card M ≤ 16 := hN ▸ Subgroup.card_le_of_le inf_le_left
    have hn₀M : (n₀ : V) ∈ M := ⟨n₀.2, hfix⟩
    rcases card_eq_one_or_sixteen hc5 hV hMc hMfix hMle with h1 | h16
    · exfalso
      have hbot : M = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      rw [hbot, Subgroup.mem_bot] at hn₀M
      exact hn₀ (Subtype.ext hn₀M)
    · have hMeq : M = commSub c := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, hN])
      intro n hn
      have : n ∈ M := hMeq ▸ hn
      exact this.2

theorem eq_one_of_trivial_on_quotient {u v z : MulAut V} {s : ℕ} (hz5 : z ^ 5 = 1)
    (hs : ¬ 5 ∣ s) (hrel : v * u * v⁻¹ = u * z ^ s) (hV : ∀ v : V, v ^ 2 = 1) (N : Subgroup V)
    (hNu : ∀ n ∈ N, u n ∈ N) (hNv : ∀ n ∈ N, v n ∈ N) (hNz : ∀ n ∈ N, z n = n)
    (hu : ∀ w : V, u w * w⁻¹ ∈ N) : z = 1 := by
  have hNu' : ∀ n ∈ N, u⁻¹ n ∈ N := (stabAut N).inv_mem (show u ∈ stabAut N from hNu)
  have hq : ∀ w : V, (z ^ s) w * w⁻¹ ∈ N := by
    intro w
    have hc : (u * z ^ s) w * w⁻¹ ∈ N := by
      have : (u * z ^ s) w * w⁻¹ = v (u (v⁻¹ w) * (v⁻¹ w)⁻¹) := by
        rw [← hrel]
        simp [MulAut.mul_apply, map_mul, map_inv]
      rw [this]
      exact hNv _ (hu _)
    have h1 : (z ^ s) w * w⁻¹ = u⁻¹ ((u * z ^ s) w * w⁻¹) * (u⁻¹ w * w⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply_self]
      group
    rw [h1]
    refine Subgroup.mul_mem _ (hNu' _ hc) ?_
    have h2 : u⁻¹ w * w⁻¹ = u⁻¹ ((u w * w⁻¹)⁻¹) := by
      simp only [map_mul, map_inv, MulAut.inv_apply_self]
      group
    rw [h2]
    exact hNu' _ (Subgroup.inv_mem _ (hu w))
  have hzs : ∀ w : V, (z ^ s) w = w := by
    intro w
    set n := (z ^ s) w * w⁻¹ with hn
    have hnN : n ∈ N := hq w
    have hfix : (z ^ s) n = n := fixSub_le_pow z s (show n ∈ fixSub z from hNz n hnN)
    have hzw : (z ^ s) w = n * w := by rw [hn]; group
    have hk : ∀ k : ℕ, ((z ^ s) ^ k) w = n ^ k * w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfix, hzw, pow_succ]
        group
    have h5 := hk 5
    rw [← pow_mul, mul_comm, pow_mul, hz5, one_pow] at h5
    have hn5 : n ^ 5 = n := by
      have h2 : n ^ 2 = 1 := hV n
      calc n ^ 5 = (n ^ 2) ^ 2 * n := by group
        _ = n := by rw [h2]; group
    rw [hn5] at h5
    have h6 : n = 1 := by
      have : n * w = 1 * w := by rw [one_mul]; exact h5.symm
      exact mul_right_cancel this
    rw [hzw, h6, one_mul]
  exact eq_one_of_fixSub_pow hz5 hs hzs

omit [Finite V] in
theorem not_le_fixSub_self {x : MulAut V} (hx5 : x ^ 5 = 1) (hV : ∀ v : V, v ^ 2 = 1)
    (hN : Nat.card (commSub x) = 16) : ¬ commSub x ≤ fixSub x := by
  intro h
  have hle : commSub x ≤ commSub x ⊓ fixSub x := le_inf le_rfl h
  rw [commSub_inf_fixSub_eq_bot (by decide : Odd 5) hx5 hV] at hle
  have hbot : commSub x = ⊥ := le_bot_iff.mp hle
  rw [hbot, Subgroup.card_bot] at hN
  omega

omit [Finite V] in
theorem pow_apply_mem_of_inv {z : MulAut V} {N : Subgroup V} (hNz : ∀ n ∈ N, z n ∈ N) (k : ℕ) :
    ∀ n ∈ N, (z ^ k) n ∈ N := by
  induction k with
  | zero => intro n hn; simpa using hn
  | succ k ih =>
    intro n hn
    rw [pow_succ, MulAut.mul_apply]
    exact ih _ (hNz n hn)

theorem false_of_heisenberg_central {p q z : MulAut V} (hp5 : p ^ 5 = 1) (hz5 : z ^ 5 = 1)
    (hz1 : z ≠ 1) (hpz : p * z = z * p) (hqz : q * z = z * q) (hrel : q * p * q⁻¹ = z * p)
    (hV : ∀ v : V, v ^ 2 = 1) (h16 : Nat.card (commSub z) ≤ 16) : False := by
  have hN : Nat.card (commSub z) = 16 := card_commSub_eq_sixteen hz5 hz1 hV h16
  have hNp : ∀ n ∈ commSub z, p n ∈ commSub z := fun n hn => apply_mem_commSub hpz.symm hn
  have hNq : ∀ n ∈ commSub z, q n ∈ commSub z := fun n hn => apply_mem_commSub hqz.symm hn
  have hNz : ∀ n ∈ commSub z, z n ∈ commSub z := fun n hn => apply_mem_commSub rfl hn
  have hNq' : ∀ n ∈ commSub z, q⁻¹ n ∈ commSub z :=
    (stabAut (commSub z)).inv_mem (show q ∈ stabAut (commSub z) from hNq)
  obtain ⟨a, b, hab, hfix⟩ := exists_trivial_elem (c := z) (d := p) hpz.symm hz5 hp5 hV hN
  have hqz' : q * z * q⁻¹ = z := by
    calc q * z * q⁻¹ = z * q * q⁻¹ := by rw [hqz]
      _ = z := by group
  have hzp : Commute z p := hpz.symm
  have hconj : q * (z ^ a * p ^ b) * q⁻¹ = (z ^ a * p ^ b) * z ^ b := by
    calc q * (z ^ a * p ^ b) * q⁻¹ = (q * z * q⁻¹) ^ a * (q * p * q⁻¹) ^ b := by
          rw [conj_pow, conj_pow]; group
      _ = z ^ a * (z * p) ^ b := by rw [hqz', hrel]
      _ = z ^ a * (z ^ b * p ^ b) := by rw [hzp.mul_pow]
      _ = (z ^ a * p ^ b) * z ^ b := by
          rw [mul_assoc, (hzp.pow_pow b b).eq]
  have hzb : ∀ n ∈ commSub z, (z ^ b) n = n := by
    intro n hn
    have h1 : (q * (z ^ a * p ^ b) * q⁻¹) n = n := by
      show q ((z ^ a * p ^ b) (q⁻¹ n)) = n
      have : (z ^ a * p ^ b) (q⁻¹ n) = q⁻¹ n := hfix (hNq' n hn)
      rw [this]
      exact MulAut.apply_inv_self V q n
    rw [hconj] at h1
    have h2 : (z ^ a * p ^ b) ((z ^ b) n) = n := h1
    have h3 : (z ^ a * p ^ b) ((z ^ b) n) = (z ^ b) n :=
      hfix (pow_apply_mem_of_inv hNz b n hn)
    rw [h3] at h2
    exact h2
  have hzfix : commSub z ≤ fixSub z := by
    by_cases hb : 5 ∣ b
    · have ha : ¬ 5 ∣ a := fun ha => hab ⟨ha, hb⟩
      obtain ⟨m, rfl⟩ := hb
      have hpb : p ^ (5 * m) = 1 := by rw [pow_mul, hp5, one_pow]
      rw [hpb, mul_one] at hfix
      rw [← fixSub_pow_eq_of_not_dvd hz5 ha]
      exact hfix
    · rw [← fixSub_pow_eq_of_not_dvd hz5 hb]
      exact fun n hn => hzb n hn
  exact not_le_fixSub_self hz5 hV hN hzfix

theorem false_of_heisenberg_noncentral {u v z : MulAut V} {s : ℕ} (hu5 : u ^ 5 = 1)
    (hv5 : v ^ 5 = 1) (hz5 : z ^ 5 = 1) (hz1 : z ≠ 1) (huz : u * z = z * u)
    (hvz : v * z = z * v) (hrel : v * u * v⁻¹ = u * z ^ s) (hs : ¬ 5 ∣ s)
    (hV : ∀ v : V, v ^ 2 = 1) (h16 : Nat.card (commSub u) ≤ 16) : False := by
  have hu1 : u ≠ 1 := by
    intro h
    rw [h] at hrel
    have hzs : z ^ s = 1 := by simpa using hrel.symm
    exact hz1 (eq_one_of_fixSub_pow hz5 hs (fun w => by rw [hzs]; rfl))
  have hN : Nat.card (commSub u) = 16 := card_commSub_eq_sixteen hu5 hu1 hV h16
  have hcom : Commute u (z ^ s) := Commute.pow_right (show Commute u z from huz) s
  have hvzs : v * z ^ s = z ^ s * v := (Commute.pow_right (show Commute v z from hvz) s).eq
  have claimA : (∀ n ∈ commSub u, v n ∈ commSub u) → False := by
    intro hNv
    have hNz : ∀ n ∈ commSub u, z n ∈ commSub u := fun n hn => apply_mem_commSub huz hn
    have hNu : ∀ n ∈ commSub u, u n ∈ commSub u := fun n hn => apply_mem_commSub rfl hn
    have hNv' : ∀ n ∈ commSub u, v⁻¹ n ∈ commSub u :=
      (stabAut (commSub u)).inv_mem (show v ∈ stabAut (commSub u) from hNv)
    obtain ⟨a, b, hab, hfix⟩ := exists_trivial_elem (c := u) (d := z) huz hu5 hz5 hV hN
    have hvz' : v * z * v⁻¹ = z := by
      calc v * z * v⁻¹ = z * v * v⁻¹ := by rw [hvz]
        _ = z := by group
    have hconj : v * (u ^ a * z ^ b) * v⁻¹ = (u ^ a * z ^ b) * z ^ (s * a) := by
      calc v * (u ^ a * z ^ b) * v⁻¹ = (v * u * v⁻¹) ^ a * (v * z * v⁻¹) ^ b := by
            rw [conj_pow, conj_pow]; group
        _ = (u * z ^ s) ^ a * z ^ b := by rw [hrel, hvz']
        _ = u ^ a * (z ^ s) ^ a * z ^ b := by rw [hcom.mul_pow]
        _ = (u ^ a * z ^ b) * z ^ (s * a) := by
            rw [← pow_mul, mul_assoc, mul_assoc, ← pow_add, ← pow_add, add_comm]
    have hza : ∀ n ∈ commSub u, (z ^ (s * a)) n = n := by
      intro n hn
      have h1 : (v * (u ^ a * z ^ b) * v⁻¹) n = n := by
        show v ((u ^ a * z ^ b) (v⁻¹ n)) = n
        have : (u ^ a * z ^ b) (v⁻¹ n) = v⁻¹ n := hfix (hNv' n hn)
        rw [this]
        exact MulAut.apply_inv_self V v n
      rw [hconj] at h1
      have h2 : (u ^ a * z ^ b) ((z ^ (s * a)) n) = n := h1
      have h3 : (u ^ a * z ^ b) ((z ^ (s * a)) n) = (z ^ (s * a)) n :=
        hfix (pow_apply_mem_of_inv hNz (s * a) n hn)
      rw [h3] at h2
      exact h2
    have hzfix : ∀ n ∈ commSub u, z n = n := by
      by_cases ha : 5 ∣ a
      · have hb : ¬ 5 ∣ b := fun hb => hab ⟨ha, hb⟩
        obtain ⟨m, rfl⟩ := ha
        have hua : u ^ (5 * m) = 1 := by rw [pow_mul, hu5, one_pow]
        rw [hua, one_mul] at hfix
        intro n hn
        have : n ∈ fixSub (z ^ b) := hfix hn
        rw [fixSub_pow_eq_of_not_dvd hz5 hb] at this
        exact this
      · have hsa : ¬ 5 ∣ s * a := by
          intro h
          rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
          · exact hs h
          · exact ha h
        intro n hn
        have : n ∈ fixSub (z ^ (s * a)) := hza n hn
        rw [fixSub_pow_eq_of_not_dvd hz5 hsa] at this
        exact this
    exact hz1 (eq_one_of_trivial_on_quotient hz5 hs hrel hV (commSub u) hNu hNv hzfix
      (fun w => deltaHom_mem_commSub u w))
  have hmap1 : (commSub u).map (v : V ≃* V).toMonoidHom = commSub (v * u * v⁻¹) :=
    map_commSub_conj v u
  have hu1_5 : (v * u * v⁻¹) ^ 5 = 1 := by rw [conj_pow, hu5]; group
  have hN1 : Nat.card (commSub (v * u * v⁻¹)) = 16 := by rw [card_commSub_conj]; exact hN
  have hcomm1 : u * (v * u * v⁻¹) = (v * u * v⁻¹) * u := by
    rw [hrel]
    exact (Commute.mul_right (Commute.refl u) hcom).eq
  rcases commSub_dichotomy hcomm1 hu1_5 hV hN hN1 with h1 | h1
  · have hmap2 : (commSub u).map ((v * v : MulAut V) : V ≃* V).toMonoidHom =
        commSub ((v * v) * u * (v * v)⁻¹) := map_commSub_conj (v * v) u
    have hu2_5 : ((v * v) * u * (v * v)⁻¹) ^ 5 = 1 := by rw [conj_pow, hu5]; group
    have hN2 : Nat.card (commSub ((v * v) * u * (v * v)⁻¹)) = 16 := by
      rw [card_commSub_conj]; exact hN
    have hu2 : (v * v) * u * (v * v)⁻¹ = u * z ^ s * z ^ s := by
      calc (v * v) * u * (v * v)⁻¹ = v * (v * u * v⁻¹) * v⁻¹ := by group
        _ = v * (u * z ^ s) * v⁻¹ := by rw [hrel]
        _ = (v * u * v⁻¹) * (v * z ^ s * v⁻¹) := by group
        _ = u * z ^ s * z ^ s := by
            rw [hrel]
            have : v * z ^ s * v⁻¹ = z ^ s := by rw [hvzs]; group
            rw [this]
    have hcomm2 : u * ((v * v) * u * (v * v)⁻¹) = ((v * v) * u * (v * v)⁻¹) * u := by
      rw [hu2]
      exact (((Commute.refl u).mul_right hcom).mul_right hcom).eq
    rcases commSub_dichotomy hcomm2 hu2_5 hV hN hN2 with h2 | h2
    ·
      have hv1 : ∀ n ∈ commSub u, u (v n) = v n := by
        intro n hn
        have : v n ∈ commSub (v * u * v⁻¹) := by rw [← hmap1]; exact ⟨n, hn, rfl⟩
        exact h1 this
      have hv2 : ∀ n ∈ commSub u, u (v (v n)) = v (v n) := by
        intro n hn
        have : (v * v) n ∈ commSub ((v * v) * u * (v * v)⁻¹) := by
          rw [← hmap2]; exact ⟨n, hn, rfl⟩
        exact h2 this
      have hzs4 : z ^ s * z ^ (4 * s) = 1 := by
        rw [← pow_add, show s + 4 * s = 5 * s by ring, pow_mul, hz5, one_pow]
      have hvz1 : ∀ k : ℕ, v⁻¹ * z ^ k * v = z ^ k := by
        intro k
        have hk : v * z ^ k = z ^ k * v := (Commute.pow_right (show Commute v z from hvz) k).eq
        calc v⁻¹ * z ^ k * v = v⁻¹ * (z ^ k * v) := by group
          _ = v⁻¹ * (v * z ^ k) := by rw [hk]
          _ = z ^ k := by group
      have hw1 : v⁻¹ * u * v = u * z ^ (4 * s) := by
        have hh : u = (v⁻¹ * u * v) * z ^ s := by
          calc u = v⁻¹ * (v * u * v⁻¹) * v := by group
            _ = v⁻¹ * (u * z ^ s) * v := by rw [hrel]
            _ = (v⁻¹ * u * v) * (v⁻¹ * z ^ s * v) := by group
            _ = (v⁻¹ * u * v) * z ^ s := by rw [hvz1]
        calc v⁻¹ * u * v = (v⁻¹ * u * v) * (z ^ s * z ^ (4 * s)) := by rw [hzs4, mul_one]
          _ = ((v⁻¹ * u * v) * z ^ s) * z ^ (4 * s) := by group
          _ = u * z ^ (4 * s) := by rw [← hh]
      have hw2 : v⁻¹ * (v⁻¹ * u * v) * v = u * z ^ (4 * s) * z ^ (4 * s) := by
        calc v⁻¹ * (v⁻¹ * u * v) * v = v⁻¹ * (u * z ^ (4 * s)) * v := by rw [hw1]
          _ = (v⁻¹ * u * v) * (v⁻¹ * z ^ (4 * s) * v) := by group
          _ = u * z ^ (4 * s) * z ^ (4 * s) := by rw [hw1, hvz1]
      have hNz : ∀ n ∈ commSub u, z n ∈ commSub u := fun n hn => apply_mem_commSub huz hn
      have e1 : ∀ n ∈ commSub u, u ((z ^ (4 * s)) n) = n := by
        intro n hn
        have h : (v⁻¹ * u * v) n = n := by
          show v⁻¹ (u (v n)) = n
          rw [hv1 n hn]
          exact MulAut.inv_apply_self V v n
        rw [hw1] at h
        exact h
      have e2 : ∀ n ∈ commSub u, u ((z ^ (4 * s)) ((z ^ (4 * s)) n)) = n := by
        intro n hn
        have h : (v⁻¹ * (v⁻¹ * u * v) * v) n = n := by
          show v⁻¹ (v⁻¹ (u (v (v n)))) = n
          rw [hv2 n hn, MulAut.inv_apply_self, MulAut.inv_apply_self]
        rw [hw2] at h
        exact h
      have hfixu : commSub u ≤ fixSub u := by
        intro n hn
        have hn' : (z ^ (4 * s)) n ∈ commSub u := pow_apply_mem_of_inv hNz (4 * s) n hn
        have h3 : (z ^ (4 * s)) n = n := by
          have := e1 _ hn'
          rw [e2 n hn] at this
          exact this.symm
        have := e1 n hn
        rw [h3] at this
        exact this
      exact not_le_fixSub_self hu5 hV hN hfixu
    ·
      apply claimA
      have hvv : ∀ n ∈ commSub u, (v * v) n ∈ commSub u := by
        intro n hn
        have : (v * v) n ∈ (commSub u).map ((v * v : MulAut V) : V ≃* V).toMonoidHom :=
          ⟨n, hn, rfl⟩
        rwa [hmap2, ← h2] at this
      have hv6 : (v * v) * ((v * v) * (v * v)) = v := by
        calc (v * v) * ((v * v) * (v * v)) = v ^ 5 * v := by
              simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          _ = v := by rw [hv5, one_mul]
      intro n hn
      have : ((v * v) * ((v * v) * (v * v))) n ∈ commSub u :=
        hvv _ (hvv _ (hvv _ hn))
      rwa [hv6] at this
  · apply claimA
    intro n hn
    have : v n ∈ (commSub u).map (v : V ≃* V).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [hmap1, ← h1] at this

theorem false_of_heisenberg {X Y : MulAut V} (hX5 : X ^ 5 = 1) (hY5 : Y ^ 5 = 1)
    (hzx : Commute ⁅Y, X⁆ X) (hzy : Commute ⁅Y, X⁆ Y) (hz1 : ⁅Y, X⁆ ≠ 1)
    (hV : ∀ v : V, v ^ 2 = 1) {i j k : ℕ} (hu5 : (X ^ i * Y ^ j * ⁅Y, X⁆ ^ k) ^ 5 = 1)
    (hu1 : X ^ i * Y ^ j * ⁅Y, X⁆ ^ k ≠ 1)
    (h16 : Nat.card (commSub (X ^ i * Y ^ j * ⁅Y, X⁆ ^ k)) ≤ 16) : False := by
  set Z : MulAut V := ⁅Y, X⁆ with hZ
  have hYX : Y * X * Y⁻¹ = Z * X := by rw [hZ, commutatorElement_def]; group
  have hXY : X * Y * X⁻¹ = Z⁻¹ * Y := by rw [hZ, commutatorElement_def]; group
  have hYn : ∀ n : ℕ, Y ^ n * X * (Y ^ n)⁻¹ = Z ^ n * X := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc Y ^ (n + 1) * X * (Y ^ (n + 1))⁻¹ = Y * (Y ^ n * X * (Y ^ n)⁻¹) * Y⁻¹ := by
            rw [pow_succ', mul_inv_rev]; group
        _ = Y * (Z ^ n * X) * Y⁻¹ := by rw [ih]
        _ = (Y * Z ^ n * Y⁻¹) * (Y * X * Y⁻¹) := by group
        _ = Z ^ (n + 1) * X := by
            have : Y * Z ^ n * Y⁻¹ = Z ^ n := by
              have h := (Commute.pow_right hzy.symm n).eq
              calc Y * Z ^ n * Y⁻¹ = Z ^ n * Y * Y⁻¹ := by rw [h]
                _ = Z ^ n := by group
            rw [hYX, pow_succ, this, mul_assoc]
  have hZ5 : Z ^ 5 = 1 := by
    have h := hYn 5
    rw [hY5] at h
    simp only [inv_one, mul_one, one_mul] at h
    have : Z ^ 5 * X = 1 * X := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this
  have hZX : Z * X = X * Z := hzx.eq
  have hZY : Z * Y = Y * Z := hzy.eq
  have hZu : Z * (X ^ i * Y ^ j * Z ^ k) = (X ^ i * Y ^ j * Z ^ k) * Z :=
    ((((hzx.pow_right i).mul_right (hzy.pow_right j)).mul_right
      (Commute.pow_right (Commute.refl Z) k)).eq)
  have hYZ : Y * Z * Y⁻¹ = Z := by
    calc Y * Z * Y⁻¹ = Z * Y * Y⁻¹ := by rw [← hZY]
      _ = Z := by group
  have hXZ : X * Z * X⁻¹ = Z := by
    calc X * Z * X⁻¹ = Z * X * X⁻¹ := by rw [← hZX]
      _ = Z := by group
  by_cases hij : 5 ∣ i ∧ 5 ∣ j
  ·
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hij
    have hXi : X ^ (5 * a) = 1 := by rw [pow_mul, hX5, one_pow]
    have hYj : Y ^ (5 * b) = 1 := by rw [pow_mul, hY5, one_pow]
    rw [hXi, hYj, one_mul, one_mul] at hu1 h16
    have hk : ¬ 5 ∣ k := by
      rintro ⟨c, rfl⟩
      apply hu1
      rw [pow_mul, hZ5, one_pow]
    rw [commSub_pow_eq_of_not_dvd hZ5 hk] at h16
    exact false_of_heisenberg_central hX5 hZ5 hz1 hzx.eq.symm hzy.eq.symm hYX hV h16
  · by_cases hi : 5 ∣ i
    ·
      have hj : ¬ 5 ∣ j := fun hj => hij ⟨hi, hj⟩
      obtain ⟨a, rfl⟩ := hi
      have hXi : X ^ (5 * a) = 1 := by rw [pow_mul, hX5, one_pow]
      rw [hXi, one_mul] at hu5 hu1 h16
      have hZu' : Commute Z (Y ^ j * Z ^ k) :=
        (hzy.pow_right j).mul_right (Commute.pow_right (Commute.refl Z) k)
      have hZinv : Z⁻¹ = Z ^ 4 := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', hZ5]
      have hrel : X * (Y ^ j * Z ^ k) * X⁻¹ = (Y ^ j * Z ^ k) * Z ^ (4 * j) := by
        calc X * (Y ^ j * Z ^ k) * X⁻¹ = (X * Y * X⁻¹) ^ j * (X * Z * X⁻¹) ^ k := by
              rw [conj_pow, conj_pow]; group
          _ = (Z⁻¹ * Y) ^ j * Z ^ k := by rw [hXY, hXZ]
          _ = Z⁻¹ ^ j * Y ^ j * Z ^ k := by
              rw [hzy.inv_left.mul_pow]
          _ = Z ^ (4 * j) * (Y ^ j * Z ^ k) := by rw [hZinv, ← pow_mul, mul_assoc]
          _ = (Y ^ j * Z ^ k) * Z ^ (4 * j) := (hZu'.pow_left (4 * j)).eq
      have hs : ¬ 5 ∣ 4 * j := by
        intro h
        rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h with h | h
        · omega
        · exact hj h
      exact false_of_heisenberg_noncentral (u := Y ^ j * Z ^ k) (v := X) (z := Z) hu5 hX5 hZ5 hz1
        hZu'.eq.symm hzx.eq.symm hrel hs hV h16
    ·
      have hZu'' : Commute Z (X ^ i * Y ^ j * Z ^ k) :=
        ((hzx.pow_right i).mul_right (hzy.pow_right j)).mul_right
          (Commute.pow_right (Commute.refl Z) k)
      have hrel : Y * (X ^ i * Y ^ j * Z ^ k) * Y⁻¹ = (X ^ i * Y ^ j * Z ^ k) * Z ^ i := by
        calc Y * (X ^ i * Y ^ j * Z ^ k) * Y⁻¹
            = (Y * X * Y⁻¹) ^ i * Y ^ j * (Y * Z * Y⁻¹) ^ k := by
              rw [conj_pow, conj_pow]; group
          _ = (Z * X) ^ i * Y ^ j * Z ^ k := by rw [hYX, hYZ]
          _ = Z ^ i * X ^ i * Y ^ j * Z ^ k := by rw [hzx.mul_pow]
          _ = Z ^ i * (X ^ i * Y ^ j * Z ^ k) := by rw [mul_assoc, mul_assoc, mul_assoc]
          _ = (X ^ i * Y ^ j * Z ^ k) * Z ^ i := (hZu''.pow_left i).eq
      exact false_of_heisenberg_noncentral (u := X ^ i * Y ^ j * Z ^ k) (v := Y) (z := Z) hu5
        hY5 hZ5 hz1 hZu''.eq.symm hzy.eq.symm hrel hi hV h16

end CFSG.CGT.PushingUpLit.CGT6M

module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.KC.OrbRow.CentGrp

open Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem mem_of_orderOf_coprime (N : Subgroup H) [N.Normal] {x : H} {a : ℕ} (hx : orderOf x ∣ a)
    (hc : Nat.Coprime a (Nat.card (H ⧸ N))) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk x : H ⧸ N) ∣ a :=
    (orderOf_map_dvd (QuotientGroup.mk' N) x).trans hx
  have h2 : orderOf (QuotientGroup.mk x : H ⧸ N) ∣ Nat.card (H ⧸ N) := orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk x : H ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes hc h1 h2
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).1 h3

@[expose] def c3 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_card_alternatingGroup (α := Fin 5)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  rw [Nat.card_eq_fintype_card]
  have : Nat.factorial 5 = 120 := by decide
  omega

theorem dvd_card_of_orderOf {G : Type*} [Group G] (S : Subgroup G) {g : G} (hg : g ∈ S) {p : ℕ}
    (hp : orderOf g = p) : p ∣ Nat.card S := by
  rw [← hp]
  exact Subgroup.orderOf_dvd_natCard S hg

theorem closure_c3_rot : closure {c3, finRotate 5} = alternatingGroup (Fin 5) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set G' := closure ({c3, finRotate 5} : Set (Equiv.Perm (Fin 5)))
  have hle : G' ≤ alternatingGroup (Fin 5) := by
    rw [closure_le]
    rintro _ (rfl | rfl) <;> rw [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup] <;> decide
  have m1 : c3 ∈ G' := subset_closure (Or.inl rfl)
  have m2 : finRotate 5 ∈ G' := subset_closure (Or.inr rfl)
  have m3 : c3 * finRotate 5 * c3 * (finRotate 5)⁻¹ ∈ G' :=
    G'.mul_mem (G'.mul_mem (G'.mul_mem m1 m2) m1) (G'.inv_mem m2)
  have h2 : 2 ∣ Nat.card G' := dvd_card_of_orderOf G' m3
    (orderOf_eq_prime (by decide) (by decide))
  have h3 : 3 ∣ Nat.card G' := dvd_card_of_orderOf G' m1
    (orderOf_eq_prime (by decide) (by decide))
  have h5 : 5 ∣ Nat.card G' := dvd_card_of_orderOf G' m2
    (orderOf_eq_prime (by decide) (by decide))
  have h60 : Nat.card G' ∣ 60 := card_alt5 ▸ Subgroup.card_dvd_of_le hle
  have h30 : 30 ∣ Nat.card G' := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 6 5) this h5
  obtain ⟨a, ha⟩ := h30
  have ha2 : a ∣ 2 := by
    rw [ha] at h60
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) (h60 : 30 * a ∣ 30 * 2)
  have hcases : Nat.card G' = 30 ∨ Nat.card G' = 60 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 ha2 with rfl | rfl
    · left
      omega
    · right
      omega
  rcases hcases with h | h
  · exfalso
    set N := G'.subgroupOf (alternatingGroup (Fin 5))
    have hN : Nat.card N = 30 := by
      rw [← h]
      exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
    have hidx : N.index = 2 := by
      have := N.card_mul_index
      rw [hN, card_alt5] at this
      omega
    have hn : N.Normal := normal_of_index_eq_two hidx
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 5)) _
        alternatingGroup.isSimpleGroup_five N hn with hb | ht
    · rw [hb, Subgroup.card_bot] at hN
      omega
    · rw [ht, Subgroup.card_top, card_alt5] at hN
      omega
  · exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_alt5, h])

theorem range_eq_alt {G : Type*} [Group G] (φ : G →* Equiv.Perm (Fin 5))
    (h1 : c3 ∈ φ.range) (h2 : finRotate 5 ∈ φ.range) (h3 : Equiv.swap 0 1 ∉ φ.range) :
    φ.range = alternatingGroup (Fin 5) := by
  have hge : alternatingGroup (Fin 5) ≤ φ.range := by
    rw [← closure_c3_rot, closure_le]
    rintro _ (rfl | rfl)
    · exact h1
    · exact h2
  refine le_antisymm (fun g hg => ?_) hge
  rw [Equiv.Perm.mem_alternatingGroup]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with hs | hs
  · exact hs
  · exfalso
    apply h3
    have hm : g⁻¹ * Equiv.swap 0 1 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, Equiv.Perm.sign_swap (by decide)]
      rfl
    have := φ.range.mul_mem hg (hge hm)
    rwa [mul_inv_cancel_left] at this

theorem eq_top_of_ker_le {G M : Type*} [Group G] [Group M] (φ : G →* M) (S : Subgroup G)
    (hK : φ.ker ≤ S) (hS : φ.range ≤ S.map φ) : S = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨s, hs, he⟩ := hS ⟨g, rfl⟩
  have hk : s⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
  have := S.mul_mem hs (hK hk)
  rwa [mul_inv_cancel_left] at this

@[expose] def conjInto (R : Subgroup H) : Subgroup H where
  carrier := {x | ∀ r ∈ R, x * r * x⁻¹ ∈ R}
  one_mem' r hr := by simpa using hr
  mul_mem' {x y} hx hy r hr := by
    have := hx _ (hy r hr)
    simpa [mul_assoc] using this
  inv_mem' {x} hx r hr := by
    have hpow : ∀ k : ℕ, ∀ r ∈ R, x ^ k * r * (x ^ k)⁻¹ ∈ R := by
      intro k
      induction k with
      | zero => intro r hr; simpa using hr
      | succ k ih =>
        intro r hr
        have := hx _ (ih r hr)
        rw [pow_succ']
        simpa [mul_assoc] using this
    have h1 : x ^ (orderOf x - 1) * x = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact hpow _ r hr

theorem conj_mem_of_closure {R : Subgroup H} {X Y : Set H} (hR : R = closure Y)
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ R) :
    ∀ x ∈ closure X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
  have hX : closure X ≤ conjInto R := by
    rw [closure_le]
    intro x hx r hr
    rw [hR] at hr ⊢
    induction hr using Subgroup.closure_induction with
    | mem y hy => exact hR ▸ h x hx y hy
    | one => simp
    | mul a b _ _ ha hb =>
      have := (closure Y).mul_mem ha hb
      simpa [mul_assoc] using this
    | inv a _ ha =>
      have := (closure Y).inv_mem ha
      simpa [mul_assoc] using this
  exact fun x hx r hr => hX hx r hr

theorem centralizer_normal (R : Subgroup H) [hRn : R.Normal] :
    (centralizer (R : Set H)).Normal := by
  constructor
  intro z hz g
  rw [mem_centralizer_iff] at hz ⊢
  intro r hr
  have hr' : g⁻¹ * r * g ∈ R := by
    have := hRn.conj_mem r hr g⁻¹
    simpa using this
  have hc := hz _ hr'
  calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * r := by group

theorem centralizer_le (K R T : Subgroup H) [K.Normal] [R.Normal] (hRK : R ≤ K)
    (hK : Nat.card K = 2 ^ 5 * 3 ^ 5) (hR : Nat.card R = 3 ^ 5) (hTK : T ≤ K)
    (hT : Nat.card T = 2 ^ 5) (hTc : ∀ t ∈ T, t ∈ centralizer (R : Set H) → t = 1)
    (φ : H →* Equiv.Perm (Fin 5)) (hker : φ.ker = K) (hrange : φ.range = alternatingGroup (Fin 5))
    {c5 : H} (hc5 : orderOf c5 = 5) (hc5R : c5 ∉ centralizer (R : Set H)) :
    centralizer (R : Set H) ≤ R := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Z := centralizer (R : Set H)
  have hZn : Z.Normal := centralizer_normal R
  have hQ : Nat.card (H ⧸ φ.ker) = 60 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hrange, card_alt5]
  have hKc : Nat.card φ.ker = 2 ^ 5 * 3 ^ 5 := by rw [hker]; exact hK
  have hH : Nat.card H = 466560 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, hQ, hKc]
    norm_num
  have hZK : ∀ z ∈ Z, z ∈ K := by
    set A := alternatingGroup (Fin 5)
    set N : Subgroup A := (Z.map φ).subgroupOf A
    have hNn : N.Normal := by
      constructor
      intro n hn a
      rw [mem_subgroupOf] at hn ⊢
      obtain ⟨z, hz, hzn⟩ := hn
      obtain ⟨h, hh⟩ : (a : Equiv.Perm (Fin 5)) ∈ φ.range := by
        rw [hrange]
        exact a.2
      refine ⟨h * z * h⁻¹, hZn.conj_mem z hz h, ?_⟩
      rw [map_mul, map_mul, map_inv, hh, hzn]
      simp
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (alternatingGroup (Fin 5)) _
        alternatingGroup.isSimpleGroup_five N hNn with hb | ht
    · intro z hz
      have hzA : φ z ∈ A := by
        rw [← hrange]
        exact ⟨z, rfl⟩
      have hmem : (⟨φ z, hzA⟩ : A) ∈ N := by
        rw [mem_subgroupOf]
        exact ⟨z, hz, rfl⟩
      rw [hb, Subgroup.mem_bot] at hmem
      have h1 : φ z = 1 := congrArg Subtype.val hmem
      rw [← hker]
      exact h1
    · exfalso
      have hσA : finRotate 5 ∈ A := by
        rw [Equiv.Perm.mem_alternatingGroup]
        decide
      have hmem : (⟨finRotate 5, hσA⟩ : A) ∈ N := by rw [ht]; exact Subgroup.mem_top _
      rw [mem_subgroupOf] at hmem
      obtain ⟨z, hz, hzσ⟩ := hmem
      have hσ5 : orderOf (finRotate 5) = 5 := orderOf_eq_prime (by decide) (by decide)
      have hzσ' : φ z = finRotate 5 := hzσ
      have h5z : 5 ∣ orderOf z := by
        rw [← hσ5, ← hzσ']
        exact orderOf_map_dvd φ z
      have h5Z : 5 ∣ Nat.card Z := h5z.trans (Subgroup.orderOf_dvd_natCard Z hz)
      have hcop : Nat.Coprime 5 (Nat.card (H ⧸ Z)) := by
        rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
        intro hq
        have h25 := Nat.mul_dvd_mul hq h5Z
        rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hH] at h25
        norm_num at h25
      exact hc5R (mem_of_orderOf_coprime Z (by rw [hc5]) hcop)
  intro z hz
  have hzK := hZK z hz
  set W : Subgroup K := Z.subgroupOf K
  have hWn : W.Normal := hZn.subgroupOf K
  set T' : Subgroup K := T.subgroupOf K
  have hT' : Nat.card T' = 2 ^ 5 := by
    rw [← hT]
    exact Nat.card_congr (subgroupOfEquivOfLe hTK).toEquiv
  set f : T' →* K ⧸ W := (QuotientGroup.mk' W).comp T'.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have htW : (t : K) ∈ W := (QuotientGroup.eq_one_iff _).1 ht
    have htT : ((t : K) : H) ∈ T := mem_subgroupOf.1 t.2
    have h1 : ((t : K) : H) = 1 := hTc _ htT (mem_subgroupOf.1 htW)
    exact Subtype.ext (Subtype.ext h1)
  have hdvd : Nat.card T' ∣ Nat.card (K ⧸ W) := Subgroup.card_dvd_of_injective f hinj
  have hKW := Subgroup.card_eq_card_quotient_mul_card_subgroup W
  rw [hK] at hKW
  rw [hT'] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  rw [hq] at hKW
  have hW : Nat.card W ∣ 3 ^ 5 := ⟨q, by
    have : 2 ^ 5 * (q * Nat.card W) = 2 ^ 5 * 3 ^ 5 := by rw [hKW]; ring
    have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
    rw [← this, mul_comm]⟩
  have hzW : (⟨z, hzK⟩ : K) ∈ W := mem_subgroupOf.2 hz
  have hzo : orderOf (⟨z, hzK⟩ : K) ∣ 3 ^ 5 := (Subgroup.orderOf_dvd_natCard W hzW).trans hW
  set R' : Subgroup K := R.subgroupOf K
  have hR'n : R'.Normal := ‹R.Normal›.subgroupOf K
  have hR' : Nat.card R' = 3 ^ 5 := by
    rw [← hR]
    exact Nat.card_congr (subgroupOfEquivOfLe hRK).toEquiv
  have hKR := Subgroup.card_eq_card_quotient_mul_card_subgroup R'
  rw [hK, hR'] at hKR
  have hKR' : Nat.card (K ⧸ R') = 2 ^ 5 := by omega
  have hmem := mem_of_orderOf_coprime R' hzo (by rw [hKR']; norm_num)
  exact mem_subgroupOf.1 hmem

end CFSG.KC.OrbRow.CentGrp

end

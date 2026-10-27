module

public import CFSG.Quasithin.Background.B1Transvection
import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81

open CFSG.Quasithin CFSG.Quasithin.B1

section Commute

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let S : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← h a' ha' b hb]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
          _ = a⁻¹ * b⁻¹ := by
            have := h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
            exact this.symm }
  have hle : A ⊔ B ≤ S :=
    sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem isSolvable_sup_of_commute {A B : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : Group.IsSolvable ↥A)
    (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥(A ⊔ B) := by
  let f : ↥A × ↥B →* ↥(A ⊔ B) :=
    MonoidHom.noncommCoprod (Subgroup.inclusion (le_sup_left : A ≤ A ⊔ B))
      (Subgroup.inclusion (le_sup_right : B ≤ A ⊔ B))
      (fun a b => Subtype.ext (h a.1 a.2 b.1 b.2))
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute h hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext rfl⟩
  exact Group.isSolvable_of_surjective hf

end Commute

section Faithful

variable {V : Type*} [CommGroup V]

theorem isSolvable_of_faithful_on_four (hV : ∀ v : V, v ^ 2 = 1) {M : Subgroup V}
    (h4 : Nat.card M = 4) {S : Subgroup (MulAut V)} (hS : ∀ g ∈ S, ∀ m ∈ M, g m ∈ M)
    (hfaith : ∀ g ∈ S, (∀ m ∈ M, g m = m) → g = 1) : Group.IsSolvable ↥S := by
  have hst : S ≤ stabSub M := le_stabSub_of_invariant hS
  have h6 : Nat.card (MulAut ↥M) = 6 := card_mulAut_of_card_four hV h4
  have hsolv : Group.IsSolvable (MulAut ↥M) := by
    have hfin : Finite (MulAut ↥M) := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
    have := Fintype.ofFinite (MulAut ↥M)
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [← Nat.card_eq_fintype_card, h6]; norm_num)
  let f : ↥S →* MulAut ↥M := (resHom M).comp (Subgroup.inclusion hst)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hfix : ∀ m ∈ M, g.1 m = m := by
      intro m hm
      have := congrArg (fun φ : MulAut ↥M => ((φ ⟨m, hm⟩ : ↥M) : V)) hg
      simpa [f, resHom_apply] using this
    exact Subtype.ext (hfaith g.1 g.2 hfix)
  exact Group.isSolvable_of_isSolvable_injective hinj

end Faithful

section Normal

variable {V : Type*} [CommGroup V]

theorem exists_normal_exponent_three [Finite V] {D Q : Subgroup (MulAut V)} (hQD : Q ≤ D)
    (hQ : IsPGroup 3 Q) (hQn : ∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) (hQ1 : Q ≠ ⊥) :
    ∃ N : Subgroup (MulAut V), N ≤ D ∧ (∀ j ∈ D, ∀ n ∈ N, j * n * j⁻¹ ∈ N) ∧ N ≠ ⊥ ∧
      (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧ ∀ n ∈ N, n ^ 3 = 1 := by
  have hfact : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ1
  have hZnt : Nontrivial ↥(Subgroup.center ↥Q) := hQ.center_nontrivial
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥Q) := hQ.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : Nat.card ↥(Subgroup.center ↥Q) = 1 := by simpa using hk
    have hsub : Subsingleton ↥(Subgroup.center ↥Q) := Nat.card_eq_one_iff_unique.1 this |>.1
    exact (not_subsingleton _) hsub
  have h3dvd : 3 ∣ Nat.card ↥(Subgroup.center ↥Q) := by
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥Q)) 3 h3dvd
  let N : Subgroup (MulAut V) :=
    { carrier := {n | n ∈ Q ∧ (∀ q ∈ Q, n * q = q * n) ∧ n ^ 3 = 1}
      mul_mem' := by
        rintro a b ⟨haQ, hac, ha3⟩ ⟨hbQ, hbc, hb3⟩
        refine ⟨Q.mul_mem haQ hbQ, fun q hq => ?_, ?_⟩
        · rw [mul_assoc, hbc q hq, ← mul_assoc, hac q hq, mul_assoc]
        · have hcomm : Commute a b := hbc a haQ |>.symm
          rw [hcomm.mul_pow, ha3, hb3, mul_one]
      one_mem' := ⟨Q.one_mem, fun q _ => by simp, one_pow 3⟩
      inv_mem' := by
        rintro a ⟨haQ, hac, ha3⟩
        refine ⟨Q.inv_mem haQ, fun q hq => ?_, by rw [inv_pow, ha3, inv_one]⟩
        have := hac q hq
        calc a⁻¹ * q = a⁻¹ * (q * a) * a⁻¹ := by group
          _ = a⁻¹ * (a * q) * a⁻¹ := by rw [← this]
          _ = q * a⁻¹ := by group }
  have hzQ : ((z : ↥Q) : MulAut V) ∈ Q := (z : ↥Q).2
  have hz1 : ((z : ↥Q) : MulAut V) ≠ 1 := by
    intro h
    have hz' : z = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h
    rw [hz', orderOf_one] at hz
    exact Nat.prime_three.one_lt.ne hz
  have hzN : ((z : ↥Q) : MulAut V) ∈ N := by
    refine ⟨hzQ, fun q hq => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.1 (z : ↥(Subgroup.center ↥Q)).2 ⟨q, hq⟩
      exact congrArg Subtype.val this.symm
    · have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg (fun y : ↥Q => (y : MulAut V)) (congrArg Subtype.val this)
  refine ⟨N, fun n hn => hQD hn.1, ?_, ?_, fun a ha b hb => ha.2.1 b hb.1, fun n hn => hn.2.2⟩
  · rintro j hj n ⟨hnQ, hnc, hn3⟩
    refine ⟨hQn j hj n hnQ, fun q hq => ?_, ?_⟩
    · have hq' : j⁻¹ * q * j ∈ Q := by
        have := hQn j⁻¹ (D.inv_mem hj) q hq
        simpa using this
      have := hnc _ hq'
      calc j * n * j⁻¹ * q = j * (n * (j⁻¹ * q * j)) * j⁻¹ := by group
        _ = j * ((j⁻¹ * q * j) * n) * j⁻¹ := by rw [this]
        _ = q * (j * n * j⁻¹) := by group
    · have : (j * n * j⁻¹) ^ 3 = j * n ^ 3 * j⁻¹ := by simp
      rw [this, hn3]
      simp
  · intro h
    exact hz1 (by
      have := hzN
      rw [h, Subgroup.mem_bot] at this
      exact this)

end Normal

section Main

variable {V : Type*} [CommGroup V] [Finite V]

theorem isSolvable_of_transvections_move_aux (hV : ∀ v : V, v ^ 2 = 1) (n : ℕ) :
    ∀ (D Q : Subgroup (MulAut V)), Nat.card D = n →
      Subgroup.closure (transvectionsIn D) = D → Q ≤ D → IsPGroup 3 Q →
      (∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q) →
      (∀ t ∈ transvectionsIn D, ∃ q ∈ Q, t * q ≠ q * t) → Group.IsSolvable ↥D := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D Q hn hD hQD hQ hQn hmove
  by_cases hD0 : D = ⊥
  · have : Subsingleton ↥D := by rw [hD0]; infer_instance
    exact inferInstance
  · have hne : (transvectionsIn D).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hD0
      rw [← hD, hemp, Subgroup.closure_empty]
    obtain ⟨t', ht'⟩ := hne
    obtain ⟨q', hq'Q, hq'⟩ := hmove t' ht'
    have hQ1 : Q ≠ ⊥ := by
      intro hQ0
      rw [hQ0, Subgroup.mem_bot] at hq'Q
      apply hq'
      rw [hq'Q]
      simp
    obtain ⟨N, hND, hNn, hN1, hNc, hN3⟩ := exists_normal_exponent_three hQD hQ hQn hQ1
    obtain ⟨x, t, hxD, hx1, hx3, htT, htx, hnormx⟩ :=
      exists_normal_zpowers hV hD hND hNn hNc (r := 3) (by decide) hN3 hN1
    obtain ⟨ht1, w, htw⟩ := htT.2
    have hsq : t * t = 1 := tv_sq hV htw ht1
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
    obtain ⟨hwM, hCfix, hM4, -⟩ :=
      inverted_by_transvection hV htw ht1 (r := 3) (by decide) hx3 hx1 htx
    obtain ⟨hsup, hinf, hWx, hfpf⟩ := zpowers_decomp hV (r := 3) (by decide) hx3
    have hxY : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    have hDn : ∀ j ∈ D, ∀ y ∈ Subgroup.zpowers x, j * y * j⁻¹ ∈ Subgroup.zpowers x := by
      intro j hj y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      have := map_zpow (MulAut.conj j) x k
      simp only [MulAut.conj_apply] at this
      rw [this]
      exact Subgroup.zpow_mem _ (hnormx j hj) k
    have hDC : ∀ j ∈ D, ∀ c ∈ fixV (Subgroup.zpowers x), j c ∈ fixV (Subgroup.zpowers x) :=
      fun j hj c hc => fixV_smul_mem j
        (fun y hy => by simpa using hDn j⁻¹ (D.inv_mem hj) y hy) hc
    have hDW : ∀ j ∈ D, ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x),
        j m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x) :=
      fun j hj => commSub_smul_mem j (hDn j hj) (fun _ _ => trivial)
    let T1 : Set (MulAut V) :=
      {s | s ∈ transvectionsIn D ∧ ∀ c ∈ fixV (Subgroup.zpowers x), s c = c}
    let T0 : Set (MulAut V) :=
      {s | s ∈ transvectionsIn D ∧ ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), s m = m}
    have hTsplit : ∀ s ∈ transvectionsIn D, s ∈ T1 ∨ s ∈ T0 := by
      intro s hs
      obtain ⟨hs1, w', hsw⟩ := hs.2
      rcases tv_split hsw hs1 hinf hsup (hDC s hs.1) (hDW s hs.1) with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr ⟨hs, h⟩
    let D1 : Subgroup (MulAut V) := Subgroup.closure T1
    let D0 : Subgroup (MulAut V) := Subgroup.closure T0
    have hD1D : D1 ≤ D := (Subgroup.closure_le _).2 fun s hs => hs.1.1
    have hD0D : D0 ≤ D := (Subgroup.closure_le _).2 fun s hs => hs.1.1
    have hDeq : D = D1 ⊔ D0 := by
      refine le_antisymm ?_ (sup_le hD1D hD0D)
      conv_lhs => rw [← hD]
      refine (Subgroup.closure_le _).2 fun s hs => ?_
      rcases hTsplit s hs with h | h
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure h)
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure h)
    have hD1C : ∀ g ∈ D1, ∀ c ∈ fixV (Subgroup.zpowers x), g c = c := fun g hg c hc =>
      ((Subgroup.closure_le (centSub (fixV (Subgroup.zpowers x)))).2
        (fun s hs => (fun c hc => hs.2 c hc : s ∈ centSub (fixV (Subgroup.zpowers x)))) hg) c hc
    have hD0W : ∀ g ∈ D0, ∀ m ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers x), g m = m :=
      fun g hg m hm =>
      ((Subgroup.closure_le (centSub (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)))).2
        (fun s hs => (fun m hm => hs.2 m hm :
          s ∈ centSub (commSub (⊤ : Subgroup V) (Subgroup.zpowers x)))) hg) m hm
    have hcomm : ∀ a ∈ D1, ∀ b ∈ D0, a * b = b * a := by
      intro a ha b hb
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) := by
        rw [hsup]; trivial
      obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
      have hbc := hDC b (hD0D hb) c hc
      have ham := hDW a (hD1D ha) m hm
      show a (b (c * m)) = b (a (c * m))
      simp only [map_mul, hD0W b hb m hm, hD1C a ha c hc, hD1C a ha (b c) hbc,
        hD0W b hb (a m) ham]
    have hcomm10 : ∀ a ∈ D0, ∀ b ∈ D1, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
    have hDeq' : D = D0 ⊔ D1 := by rw [hDeq, sup_comm]
    have hinf01 : ∀ g ∈ D0, g ∈ D1 → g = 1 := by
      intro g hg0 hg1
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) := by
        rw [hsup]; trivial
      obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
      show g (c * m) = c * m
      rw [map_mul, hD1C g hg1 c hc, hD0W g hg0 m hm]
    have hsolv1 : Group.IsSolvable ↥D1 := by
      refine isSolvable_of_faithful_on_four hV hM4 (S := D1)
        (fun g hg m hm => hDW g (hD1D hg) m hm) ?_
      intro g hg hgM
      refine MulEquiv.ext fun v => ?_
      have hv : v ∈ fixV (Subgroup.zpowers x) ⊔ commSub ⊤ (Subgroup.zpowers x) := by
        rw [hsup]; trivial
      obtain ⟨c, hc, m, hm, rfl⟩ := Subgroup.mem_sup.1 hv
      show g (c * m) = c * m
      rw [map_mul, hD1C g hg c hc, hgM m hm]
    have hcl0 : Subgroup.closure (transvectionsIn D0) = D0 := by
      refine le_antisymm ((Subgroup.closure_le _).2 fun s hs => hs.1) ?_
      refine Subgroup.closure_mono ?_
      intro s hs
      exact ⟨Subgroup.subset_closure hs, hs.1.2⟩
    have hxD0 : x ∉ D0 := by
      intro hx0
      have h0 : commSub (⊤ : Subgroup V) (Subgroup.zpowers x) = ⊥ :=
        (Subgroup.eq_bot_iff_forall _).2 fun m hm => hfpf m hm (hD0W x hx0 m hm)
      rw [h0, Subgroup.card_bot] at hM4
      omega
    have hlt : Nat.card D0 < n := by
      rw [← hn]
      refine lt_of_le_of_ne (Subgroup.card_le_of_le hD0D) fun h => hxD0 ?_
      have := Subgroup.eq_of_le_of_card_ge hD0D h.ge
      rw [this]
      exact hxD
    let Q0 : Subgroup (MulAut V) :=
      { carrier := {d | d ∈ D0 ∧ ∃ q ∈ Q, ∃ b ∈ D1, q = d * b}
        mul_mem' := by
          rintro d d' ⟨hd, q, hq, b, hb, rfl⟩ ⟨hd', q', hq', b', hb', rfl⟩
          refine ⟨D0.mul_mem hd hd', _, Q.mul_mem hq hq', b * b', D1.mul_mem hb hb', ?_⟩
          calc d * b * (d' * b') = d * (b * d') * b' := by group
            _ = d * (d' * b) * b' := by rw [← hcomm10 d' hd' b hb]
            _ = d * d' * (b * b') := by group
        one_mem' := ⟨D0.one_mem, 1, Q.one_mem, 1, D1.one_mem, by simp⟩
        inv_mem' := by
          rintro d ⟨hd, q, hq, b, hb, rfl⟩
          refine ⟨D0.inv_mem hd, _, Q.inv_mem hq, b⁻¹, D1.inv_mem hb, ?_⟩
          calc (d * b)⁻¹ = b⁻¹ * d⁻¹ := mul_inv_rev d b
            _ = d⁻¹ * b⁻¹ :=
              (hcomm10 d⁻¹ (D0.inv_mem hd) b⁻¹ (D1.inv_mem hb)).symm }
    have hQ0D0 : Q0 ≤ D0 := fun d hd => hd.1
    have hQ0p : IsPGroup 3 Q0 := by
      rintro ⟨d, hd, q, hq, b, hb, hqdb⟩
      obtain ⟨k, hk⟩ := hQ ⟨q, hq⟩
      have hqk : q ^ (3 ^ k) = 1 := by
        have := congrArg (fun y : ↥Q => (y : MulAut V)) hk
        simpa using this
      have hcm : Commute d b := hcomm10 d hd b hb
      have hdb : d ^ (3 ^ k) * b ^ (3 ^ k) = 1 := by
        rw [← hcm.mul_pow, ← hqdb]
        exact hqk
      have hd1 : d ^ (3 ^ k) ∈ D1 := by
        have : d ^ (3 ^ k) = (b ^ (3 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hdb
        rw [this]
        exact D1.inv_mem (D1.pow_mem hb _)
      refine ⟨k, Subtype.ext ?_⟩
      exact hinf01 _ (D0.pow_mem hd _) hd1
    have hQ0n : ∀ e ∈ D0, ∀ d ∈ Q0, e * d * e⁻¹ ∈ Q0 := by
      rintro e he d ⟨hd, q, hq, b, hb, hqdb⟩
      refine ⟨D0.mul_mem (D0.mul_mem he hd) (D0.inv_mem he), e * q * e⁻¹,
        hQn e (hD0D he) q hq, b, hb, ?_⟩
      rw [hqdb]
      calc e * (d * b) * e⁻¹ = e * d * (b * e⁻¹) := by group
        _ = e * d * (e⁻¹ * b) := by rw [← hcomm10 e⁻¹ (D0.inv_mem he) b hb]
        _ = e * d * e⁻¹ * b := by group
    have hmove0 : ∀ s ∈ transvectionsIn D0, ∃ q0 ∈ Q0, s * q0 ≠ q0 * s := by
      intro s hs
      have hsD : s ∈ transvectionsIn D := ⟨hD0D hs.1, hs.2⟩
      obtain ⟨q, hq, hsq⟩ := hmove s hsD
      have hqD : q ∈ D0 ⊔ D1 := by rw [← hDeq']; exact hQD hq
      obtain ⟨d, hd, b, hb, hqdb⟩ := exists_mul_of_mem_sup_of_commute hcomm10 hqD
      refine ⟨d, ⟨hd, q, hq, b, hb, hqdb⟩, fun hsd => hsq ?_⟩
      rw [hqdb]
      calc s * (d * b) = (s * d) * b := by group
        _ = (d * s) * b := by rw [hsd]
        _ = d * (s * b) := by group
        _ = d * (b * s) := by rw [hcomm10 s hs.1 b hb]
        _ = d * b * s := by group
    have hsolv0 : Group.IsSolvable ↥D0 :=
      ih (Nat.card D0) hlt D0 Q0 rfl hcl0 hQ0D0 hQ0p hQ0n hmove0
    have hsolv := isSolvable_sup_of_commute hcomm hsolv1 hsolv0
    rwa [← hDeq] at hsolv

theorem isSolvable_of_transvections_move (hV : ∀ v : V, v ^ 2 = 1) {D Q : Subgroup (MulAut V)}
    (hD : Subgroup.closure (transvectionsIn D) = D) (hQD : Q ≤ D) (hQ : IsPGroup 3 Q)
    (hQn : ∀ d ∈ D, ∀ q ∈ Q, d * q * d⁻¹ ∈ Q)
    (hmove : ∀ t ∈ transvectionsIn D, ∃ q ∈ Q, t * q ≠ q * t) : Group.IsSolvable ↥D :=
  isSolvable_of_transvections_move_aux hV _ D Q rfl hD hQD hQ hQn hmove

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81

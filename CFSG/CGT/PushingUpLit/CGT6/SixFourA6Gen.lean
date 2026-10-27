module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourLin
public import CFSG.CGT.PushingUpLit.CGT6.SixFourAlt6

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

section Gen

variable {V : Type*} [Group V]

theorem eq_of_le_of_index_eq [Finite V] {H K : Subgroup V} (hle : H ≤ K) (hidx : H.index = K.index) :
    H = K := by
  have hfin : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel := Subgroup.relIndex_mul_index hle
  have h3 : H.relIndex K = 1 := by
    rw [hidx] at hrel
    have hpos : 0 < K.index := Nat.pos_of_ne_zero (hidx ▸ hfin)
    exact (Nat.mul_eq_right hpos.ne').mp hrel
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h3)

theorem fpf_of_nontrivial (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) [Finite V]
    {ζ : MulAut V} (hζ : ζ ^ 3 = 1) {A : Subgroup V} (hA : Nat.card A = 4) (hAζ : ∀ u ∈ A, ζ u ∈ A)
    (hmove : ∃ u ∈ A, ζ u ≠ u) : A ⊓ autFixSub ζ = ⊥ := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hsq : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hV w)
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwA, hwf⟩ := Subgroup.mem_inf.mp hw
  rw [mem_autFixSub] at hwf
  by_contra hw1
  have hw1' : w ≠ 1 := fun h => hw1 (by rw [h]; exact Subgroup.one_mem _)
  obtain ⟨u, huA, hu⟩ := hmove
  have hu1 : u ≠ 1 := fun h => hu (by rw [h, map_one])
  have huw : u ≠ w := fun h => hu (by rw [h, hwf])
  have hwu : w * u ∈ A := A.mul_mem hwA huA
  have hAeq : ∀ x ∈ A, x = 1 ∨ x = w ∨ x = u ∨ x = w * u := by
    refine mem_of_card_eq_four hA A.one_mem hwA huA hwu hw1'.symm hu1.symm ?_ huw.symm ?_ ?_
    · intro h
      apply huw
      have h' : u = w⁻¹ := eq_inv_of_mul_eq_one_right h.symm
      rw [h', hsq]
    · intro h
      apply hu1
      have := congrArg (fun x => w⁻¹ * x) h
      simp at this
      exact this.symm
    · intro h
      apply hw1'
      have := congrArg (fun x => x * u⁻¹) h
      simp at this
      exact this.symm
  have hzu : ζ u ∈ A := hAζ u huA
  have hzu1 : ζ u ≠ 1 := fun h => hu1 (ζ.injective (by rw [h, map_one]))
  have hzuw : ζ u ≠ w := fun h => huw (ζ.injective (by rw [h, hwf]))
  have hzuu : ζ u = w * u := by
    rcases hAeq _ hzu with h | h | h | h
    · exact absurd h hzu1
    · exact absurd h hzuw
    · exact absurd h hu
    · exact h
  have h2 : (ζ ^ 2) u = u := by
    rw [pow_two, MulAut.mul_apply, hzuu, map_mul, hwf, hzuu, ← mul_assoc, hV w, one_mul]
  have h3 : ζ u = u := by
    have h3' : (ζ ^ 3) u = u := by rw [hζ]; rfl
    have : (ζ ^ 3) u = ζ ((ζ ^ 2) u) := by rw [pow_succ', MulAut.mul_apply]
    rw [h2] at this
    rw [← this]; exact h3'.symm ▸ rfl
  exact hu h3

theorem fix_of_pow_prime_ge_five [Finite V] {A : Subgroup V} (hA : Nat.card A = 4) {σ : MulAut V}
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hσ : σ ^ p = 1) (hAσ : ∀ u ∈ A, σ u ∈ A) :
    ∀ u ∈ A, σ u = u := by
  classical
  have : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hfi : Fintype A := Fintype.ofFinite A
  let f : A → A := fun u => ⟨σ u, hAσ u u.2⟩
  have hf : Function.Injective f := fun x y h => Subtype.ext (σ.injective (congrArg Subtype.val h))
  have hfb : Function.Bijective f := Finite.injective_iff_bijective.mp hf
  let τ : Equiv.Perm A := Equiv.ofBijective f hfb
  have hτpow : ∀ n : ℕ, ∀ u : A, (((τ ^ n) u : A) : V) = (σ ^ n) u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Equiv.Perm.mul_apply, pow_succ, MulAut.mul_apply]
      have := ih (τ u)
      rw [this]
      rfl
  have hτ : τ ^ p = 1 := by
    refine Equiv.Perm.ext fun u => Subtype.ext ?_
    rw [hτpow, hσ]
    rfl
  have hord : orderOf τ ∣ p := orderOf_dvd_of_pow_eq_one hτ
  have hdvd : orderOf τ ∣ 24 := by
    have h1 := orderOf_dvd_natCard τ
    have h2 : Nat.card (Equiv.Perm A) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hA]
      rfl
    rwa [h2] at h1
  have hone : orderOf τ = 1 := by
    rcases (Nat.dvd_prime hp).mp hord with h | h
    · exact h
    · exfalso
      rw [h] at hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases p <;> simp_all (config := {decide := true})
  have hτ1 : τ = 1 := orderOf_eq_one_iff.mp hone
  intro u hu
  have := congrArg (fun g : Equiv.Perm A => ((g ⟨u, hu⟩ : A) : V)) hτ1
  simpa [τ, f] using this

theorem card_sup_ge_sixteen [Finite V] (hc : ∀ a b : V, a * b = b * a) {ζ : MulAut V}
    (hζ : ζ ^ 3 = 1) {A B : Subgroup V} (hA : Nat.card A = 4) (hB : Nat.card B = 4)
    (hAζ : ∀ u ∈ A, ζ u ∈ A) (hBζ : ∀ u ∈ B, ζ u ∈ B) (hfix : A ⊓ autFixSub ζ = ⊥) (hne : A ≠ B) :
    16 ≤ Nat.card ↥(A ⊔ B) := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hfA : Finite A := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hfB : Finite B := Nat.finite_of_card_ne_zero (by rw [hB]; norm_num)
  have hAB : A ⊓ B = ⊥ := by
    by_contra hAB
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAB
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hCfix : (A ⊓ B) ⊓ autFixSub ζ = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      have : v ∈ A ⊓ autFixSub ζ := ⟨hv.1.1, hv.2⟩
      rw [hfix] at this
      exact this
    have hC4 := four_le_card_of_fpf hζ (H := A ⊓ B)
      (fun s hs => ⟨hAζ s hs.1, hBζ s hs.2⟩) hCfix hu hu1'
    have hCA : A ⊓ B = A := by
      refine (Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ B ≤ A) ?_)
      rw [hA]; exact hC4
    have hAB' : A ≤ B := hCA ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hAB' (by rw [hA, hB]))
  let m : A × B → ↥(A ⊔ B) := fun p => ⟨(p.1 : V) * (p.2 : V),
    Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hm : Function.Injective m := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h1 : (x : V) * y = x' * y' := congrArg Subtype.val h
    have h2 : ((x' : V)⁻¹ * x) = y' * (y : V)⁻¹ := by
      apply eq_mul_inv_of_mul_eq
      calc (x' : V)⁻¹ * x * y = (x' : V)⁻¹ * (x * y) := by rw [mul_assoc]
        _ = (x' : V)⁻¹ * (x' * y') := by rw [h1]
        _ = y' := by rw [inv_mul_cancel_left]
    have h3 : ((x' : V)⁻¹ * x) ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem x'.2) x.2, by rw [h2]; exact B.mul_mem y'.2 (B.inv_mem y.2)⟩
    rw [hAB] at h3
    have h4 : (x' : V)⁻¹ * x = 1 := Subgroup.mem_bot.mp h3
    have hx : x = x' := Subtype.ext (inv_mul_eq_one.mp h4).symm
    have h5 : y' * (y : V)⁻¹ = 1 := by rw [← h2]; exact h4
    have hy : y = y' := Subtype.ext (mul_inv_eq_one.mp h5).symm
    rw [hx, hy]
  have := Nat.card_le_card_of_injective m hm
  rw [Nat.card_prod, hA, hB] at this
  exact this

theorem commutatorElement_central_mul' {Q : Type*} [Group Q] {z w : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) (x y : Q) :
    ⁅z * x, w * y⁆ = ⁅x, y⁆ := by
  have hz' := Subgroup.mem_center_iff.mp hz
  have hw' := Subgroup.mem_center_iff.mp hw
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * (w * y) * (z * x)⁻¹ * (w * y)⁻¹
      = z * (x * w * y * x⁻¹) * z⁻¹ * y⁻¹ * w⁻¹ := by group
    _ = (x * w * y * x⁻¹) * z * z⁻¹ * y⁻¹ * w⁻¹ := by rw [← hz' (x * w * y * x⁻¹)]
    _ = (w * x * y * x⁻¹ * y⁻¹) * w⁻¹ := by rw [hw' x]; group
    _ = w * (x * y * x⁻¹ * y⁻¹) * w⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * w * w⁻¹ := by rw [← hw' (x * y * x⁻¹ * y⁻¹)]
    _ = x * y * x⁻¹ * y⁻¹ := by group

end Gen

section Perfect

variable {Q : Type*} [Group Q]

theorem eq_top_of_sup_center (hperf : commutator Q = ⊤) {M : Subgroup Q}
    (hM : M ⊔ Subgroup.center Q = ⊤) : M = ⊤ := by
  have hle : commutator Q ≤ M := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hx : x ∈ M ⊔ Subgroup.center Q := hM ▸ Subgroup.mem_top x
    have hy : y ∈ M ⊔ Subgroup.center Q := hM ▸ Subgroup.mem_top y
    obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    obtain ⟨n', hn', z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    have e : ⁅n * z, n' * z'⁆ = ⁅n, n'⁆ := by
      rw [Subgroup.mem_center_iff.mp hz n, Subgroup.mem_center_iff.mp hz' n']
      exact commutatorElement_central_mul' hz hz' n n'
    rw [e, commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hn hn') (M.inv_mem hn)) (M.inv_mem hn')
  rw [hperf] at hle
  exact top_le_iff.mp hle

theorem normalClosure_eq_top (hperf : commutator Q = ⊤)
    (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q)) {J : Subgroup Q}
    (hJ : ¬ J ≤ Subgroup.center Q) : Subgroup.normalClosure (J : Set Q) = ⊤ := by
  set N := Subgroup.normalClosure (J : Set Q) with hNdef
  have hN : N.Normal := Subgroup.normalClosure_normal
  have hJN : J ≤ N := Subgroup.subset_normalClosure
  have h1 : (N.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · exfalso
    apply hJ
    have : N ≤ Subgroup.center Q := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hJN.trans this
  · refine eq_top_of_sup_center hperf (M := N) ?_
    have h2 := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
    rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at h2
    exact h2.symm

theorem mem_of_normalizes_two_group [Finite Q] {Y₀ J : Subgroup Q} (hJY : J ≤ Y₀)
    (hY60 : Nat.card Y₀ = 60) (hJ4 : Nat.card J = 4) {y : Q} (hyY : y ∈ Y₀) (hy2 : y * y = 1)
    (hyN : y ∈ Subgroup.normalizer (J : Set Q)) : y ∈ J := by
  by_contra hyJ
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJp : IsPGroup 2 J := IsPGroup.of_card (n := 2) (by rw [hJ4]; norm_num)
  have hyp : IsPGroup 2 (Subgroup.zpowers y) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨g, k, rfl⟩ := g
    apply Subtype.ext
    show ((y ^ k) ^ 2 : Q) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : y ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hy2
    rw [Nat.cast_ofNat, this, one_zpow]
  have hF : IsPGroup 2 ↥(J ⊔ Subgroup.zpowers y) :=
    hJp.to_sup_of_normal_left' hyp (Subgroup.zpowers_le.mpr hyN)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hF
  have hle : J ≤ J ⊔ Subgroup.zpowers y := le_sup_left
  have hlt : Nat.card J < Nat.card ↥(J ⊔ Subgroup.zpowers y) := by
    by_contra hge
    push Not at hge
    have heq := Subgroup.eq_of_le_of_card_ge hle hge
    apply hyJ
    have : y ∈ J ⊔ Subgroup.zpowers y :=
      (le_sup_right : Subgroup.zpowers y ≤ J ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
    rwa [← heq] at this
  rw [hJ4, hn] at hlt
  have hn3 : 3 ≤ n := by
    by_contra h
    push Not at h
    interval_cases n <;> omega
  have h8 : 8 ∣ Nat.card ↥(J ⊔ Subgroup.zpowers y) := by
    rw [hn]
    exact (pow_dvd_pow 2 hn3)
  have hFY : J ⊔ Subgroup.zpowers y ≤ Y₀ := sup_le hJY (Subgroup.zpowers_le.mpr hyY)
  have h60 : Nat.card ↥(J ⊔ Subgroup.zpowers y) ∣ 60 := hY60 ▸ Subgroup.card_dvd_of_le hFY
  have := dvd_trans h8 h60
  omega

end Perfect


end CFSG.CGT.PushingUpLit.CGT6

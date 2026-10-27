module

public import CFSG.CGT.Timmesfeld75.Sec4OneQuotient

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

structure SylowInner (Q : Type) [Group Q] (S : Subgroup Q) : Prop where
  finite : Finite Q
  exists_conj_eq_sylow : ∀ P : Sylow 2 Q, ∃ g : Q, conjSubgroup g S = (P : Subgroup Q)
  exists_involution_of_unique_fixed : ∀ φ : Q ≃* Q, (∀ x, φ (φ x) = x) → ∀ g : Q,
    (conjSubgroup g S).map φ.toMonoidHom = conjSubgroup g S →
    (∀ g', (conjSubgroup g' S).map φ.toMonoidHom = conjSubgroup g' S →
      conjSubgroup g' S = conjSubgroup g S) →
      ∃ t ∈ conjSubgroup g S, t ≠ 1 ∧ ∀ x, φ x = t * x * t⁻¹

theorem IsL2Pair.sylowInner {Q : Type} [Group Q] {S : Subgroup Q} {q : ℕ} (h : IsL2Pair Q S q) :
    SylowInner Q S :=
  ⟨h.finite, h.exists_conj_eq_sylow, fun φ hφ g hfix huniq =>
    (h.conj g).exists_involution_of_unique_fixed φ hφ hfix fun g' hg' => by
      rw [conjSubgroup_conjSubgroup] at hg' ⊢
      exact huniq _ hg'⟩

namespace SylowInner

variable {G : Type} [Group G]

theorem conj {Q : Type} [Group Q] {S : Subgroup Q} (h : SylowInner Q S) (g : Q) :
    SylowInner Q (conjSubgroup g S) := by
  refine ⟨h.finite, fun P => ?_, fun φ hφ g₀ hfix huniq => ?_⟩
  · obtain ⟨g₁, hg₁⟩ := h.exists_conj_eq_sylow P
    refine ⟨g₁ * g⁻¹, ?_⟩
    rw [conjSubgroup_conjSubgroup, show g₁ * g⁻¹ * g = g₁ by group]
    exact hg₁
  · rw [conjSubgroup_conjSubgroup] at hfix
    rw [conjSubgroup_conjSubgroup]
    refine h.exists_involution_of_unique_fixed φ hφ (g₀ * g) hfix fun g' hg' => ?_
    have := huniq (g' * g⁻¹) (by
      rw [conjSubgroup_conjSubgroup, show g' * g⁻¹ * g = g' by group]
      exact hg')
    rwa [conjSubgroup_conjSubgroup, show g' * g⁻¹ * g = g' by group,
      conjSubgroup_conjSubgroup] at this

theorem exists_fixed_conj_of_involution {X N U : Subgroup G} [(N.subgroupOf X).Normal]
    (hUX : U ≤ X)
    (hpair : SylowInner (↥X ⧸ N.subgroupOf X)
      ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))))
    {a : G} (haa : a * a = 1) (haX : a ∈ Subgroup.normalizer (X : Set G))
    (haN : a ∈ Subgroup.normalizer (N : Set G)) :
    ∃ g ∈ X, ∀ u ∈ conjSubgroup g U, ∃ u' ∈ conjSubgroup g U, ∃ n ∈ N,
      a * u * a⁻¹ = u' * n := by
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := X) (N := N) haX haN
  have hφφ := quotient_conj_equiv_involutive haX haa φ hφ
  have := hpair.finite
  obtain ⟨P, hP⟩ := exists_fixed_sylow_of_involutive φ hφφ
  obtain ⟨gb, hgb⟩ := hpair.exists_conj_eq_sylow P
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  refine ⟨(g : G), g.2, ?_⟩
  have hPimg : (P : Subgroup (↥X ⧸ N.subgroupOf X)) =
      ((conjSubgroup (g : G) U).subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    rw [← hgb]
    exact conjSubgroup_map_subgroupOf X N U g
  refine exists_mul_of_map_le haX φ hφ (conjSubgroup_le_of_le_of_mem hUX g.2) ?_
  rw [← hPimg]
  exact hP

theorem exists_inner_of_unique_fixed {X N U : Subgroup G} [hN : (N.subgroupOf X).Normal]
    (hNX : N ≤ X) (hUX : U ≤ X)
    (hpair : SylowInner (↥X ⧸ N.subgroupOf X)
      ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))))
    {a : G} (haa : a * a = 1) (haX : a ∈ Subgroup.normalizer (X : Set G))
    (haN : a ∈ Subgroup.normalizer (N : Set G)) (haU : a ∈ Subgroup.normalizer (U : Set G))
    (huniq : ∀ g ∈ X, (∀ u ∈ conjSubgroup g U, ∃ u' ∈ conjSubgroup g U, ∃ n ∈ N,
      a * u * a⁻¹ = u' * n) → conjSubgroup g U = U) :
    ∃ t ∈ U, t ∉ N ∧ ∀ x ∈ X, (t⁻¹ * a) * x * (t⁻¹ * a)⁻¹ * x⁻¹ ∈ N := by
  obtain ⟨φ, hφ⟩ := exists_quotient_conj_equiv (X := X) (N := N) haX haN
  have hφφ := quotient_conj_equiv_involutive haX haa φ hφ
  have hφU := map_quotient_conj_equiv haX haU haa φ hφ
  have huniq' : ∀ gb : ↥X ⧸ N.subgroupOf X,
      (conjSubgroup gb ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)))).map
          φ.toMonoidHom =
        conjSubgroup gb ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) →
      conjSubgroup gb ((U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) =
        (U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) := by
    intro gb hgb
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
    rw [conjSubgroup_map_subgroupOf] at hgb ⊢
    have hU' := huniq (g : G) g.2 (exists_mul_of_map_le haX φ hφ
      (conjSubgroup_le_of_le_of_mem hUX g.2) hgb)
    rw [hU']
  obtain ⟨tb, htb, htb1, htb'⟩ := hpair.exists_involution_of_unique_fixed φ hφφ 1
    (by rw [conjSubgroup_one]; exact hφU)
    (fun g' hg' => by rw [conjSubgroup_one]; exact huniq' g' hg')
  rw [conjSubgroup_one] at htb
  obtain ⟨t', ht', rfl⟩ := htb
  have htU : (t' : G) ∈ U := Subgroup.mem_subgroupOf.1 ht'
  refine ⟨(t' : G), htU, fun htN => htb1 ?_, fun x hx => ?_⟩
  · exact (QuotientGroup.eq_one_iff t').2 (Subgroup.mem_subgroupOf.2 htN)
  · have h1 := htb' (QuotientGroup.mk (⟨x, hx⟩ : ↥X))
    rw [hφ] at h1
    have h2 := QuotientGroup.eq.1 (h1.trans (rfl :
      (QuotientGroup.mk' (N.subgroupOf X) t' * QuotientGroup.mk (⟨x, hx⟩ : ↥X) *
          (QuotientGroup.mk' (N.subgroupOf X) t')⁻¹ : ↥X ⧸ N.subgroupOf X) =
        QuotientGroup.mk (t' * ⟨x, hx⟩ * t'⁻¹)))
    have h3 : (a * x * a⁻¹)⁻¹ * ((t' : G) * x * (t' : G)⁻¹) ∈ N := Subgroup.mem_subgroupOf.1 h2
    have hxt : x * (t' : G)⁻¹ ∈ X := X.mul_mem hx (X.inv_mem t'.2)
    have hXN : X ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).1 hN
    have h4 := (Subgroup.mem_normalizer_iff.1 (hXN hxt) _).1 (N.inv_mem h3)
    have e : ((t' : G)⁻¹ * a) * x * ((t' : G)⁻¹ * a)⁻¹ * x⁻¹ =
        (x * (t' : G)⁻¹) * ((a * x * a⁻¹)⁻¹ * ((t' : G) * x * (t' : G)⁻¹))⁻¹ *
          (x * (t' : G)⁻¹)⁻¹ := by
      group
    rw [e]
    exact h4

end SylowInner

open DihedralGroup in
theorem dihedral_inner_of_unique_fixed {n : ℕ} [NeZero n] (hn : Odd n)
    (ψ : DihedralGroup n ≃* DihedralGroup n) (hψ : ∀ x, ψ (ψ x) = x) (j : ZMod n)
    (hj : ψ (sr j) = sr j)
    (huniq : ∀ i : ZMod n, ψ (sr i) = sr i → i = j) (x : DihedralGroup n) :
    ψ x = sr j * x * (sr j)⁻¹ := by
  have hrot : ∀ i : ZMod n, ∃ k : ZMod n, ψ (r i) = r k := by
    intro i
    rcases hψi : ψ (r i) with k | k
    · exact ⟨k, rfl⟩
    · exfalso
      have h1 : orderOf (ψ (r i)) = orderOf (r i) := MulEquiv.orderOf_eq ψ (r i)
      rw [hψi, orderOf_sr] at h1
      have h2 : (r i : DihedralGroup n) ^ n = 1 := by
        rw [r_pow]
        have : (i * (n : ZMod n)) = 0 := by simp
        rw [this]
        rfl
      have h3 : orderOf (r i) ∣ n := orderOf_dvd_of_pow_eq_one h2
      rw [← h1] at h3
      exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h3)
  choose κ hκ using hrot
  have hκadd : ∀ a b, κ (a + b) = κ a + κ b := by
    intro a b
    have h1 : ψ (r (a + b)) = ψ (r a) * ψ (r b) := by rw [← map_mul, r_mul_r]
    rw [hκ, hκ, hκ, r_mul_r] at h1
    exact DihedralGroup.r.inj h1
  have hsr : ∀ k : ZMod n, ψ (sr (j + k)) = sr (j + κ k) := by
    intro k
    have : (sr (j + k) : DihedralGroup n) = sr j * r k := (sr_mul_r j k).symm
    rw [this, map_mul, hj, hκ, sr_mul_r]
  have hκκ : ∀ k, κ (κ k) = k := by
    intro k
    have h1 := hψ (r k)
    rw [hκ, hκ] at h1
    exact DihedralGroup.r.inj h1
  have hfix : ∀ k, κ k = k → k = 0 := by
    intro k hk
    have := huniq (j + k) (by rw [hsr, hk])
    simpa using this
  have hneg : ∀ k, κ k = -k := by
    intro k
    have hw : κ (k + κ k) = k + κ k := by rw [hκadd, hκκ, add_comm]
    have := hfix _ hw
    exact eq_neg_of_add_eq_zero_right this
  cases x with
  | r k =>
    rw [hκ, hneg, inv_sr, sr_mul_r, sr_mul_sr]
    congr 1
    ring
  | sr i =>
    have hi : (sr i : DihedralGroup n) = sr (j + (i - j)) := by congr 1; ring
    rw [hi, hsr, hneg, inv_sr, sr_mul_sr, r_mul_sr]
    congr 1
    ring

theorem two_mul_half_zmod {n : ℕ} (hn : Odd n) :
    (2 : ZMod n) * (((n + 1) / 2 : ℕ) : ZMod n) = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h1]
  have h2 : (2 : ZMod (2 * k + 1)) * ((k + 1 : ℕ) : ZMod (2 * k + 1)) =
      ((2 * k + 1 : ℕ) : ZMod (2 * k + 1)) + 1 := by
    push_cast
    ring
  rw [h2, ZMod.natCast_self, zero_add]

open DihedralGroup in
theorem exists_dihedral_orderOf_two {n : ℕ} [NeZero n] (hn : Odd n) {d : DihedralGroup n}
    (hd : orderOf d = 2) : ∃ j : ZMod n, d = sr j := by
  rcases d with i | j
  · exfalso
    have h2 : (r i : DihedralGroup n) ^ n = 1 := by
      rw [r_pow]
      have : (i * (n : ZMod n)) = 0 := by simp
      rw [this]
      rfl
    have h3 : orderOf (r i) ∣ n := orderOf_dvd_of_pow_eq_one h2
    rw [hd] at h3
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h3)
  · exact ⟨j, rfl⟩

open DihedralGroup in
theorem dihedral_exists_involution_of_unique_fixed {Q : Type} [Group Q] {S : Subgroup Q} {n : ℕ}
    (hn : Odd n) (e : Q ≃* DihedralGroup n) (hS : Nat.card S = 2) (φ : Q ≃* Q)
    (hφ : ∀ x, φ (φ x) = x) (hSφ : S.map φ.toMonoidHom = S)
    (huniq : ∀ g, (conjSubgroup g S).map φ.toMonoidHom = conjSubgroup g S →
      conjSubgroup g S = S) : ∃ t ∈ S, t ≠ 1 ∧ ∀ x, φ x = t * x * t⁻¹ := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  obtain ⟨s, hs⟩ := (Nat.card_eq_two_iff' (1 : S)).1 hS
  have hs1 : s ≠ 1 := hs.1
  have hsS : (s : Q) ∈ S := s.2
  have hsne : (s : Q) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hSeq : ∀ y ∈ S, y = 1 ∨ y = (s : Q) := by
    intro y hy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (congrArg Subtype.val (hs.2 ⟨y, hy⟩ (fun h => hy1 (congrArg Subtype.val h))))
  have hss : (s : Q) * s = 1 := by
    have hdvd : orderOf (s : Q) ∣ 2 := hS ▸ Subgroup.orderOf_dvd_natCard S hsS
    have h2 : orderOf (s : Q) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hsne
      · exact h
    have := pow_orderOf_eq_one (s : Q)
    rwa [h2, pow_two] at this
  have hord : orderOf (e (s : Q)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rw [pow_two]; exact hss) hsne
  obtain ⟨j, hj⟩ := exists_dihedral_orderOf_two hn hord
  have hφs : φ (s : Q) = (s : Q) := by
    have hmem : φ (s : Q) ∈ S.map φ.toMonoidHom := Subgroup.mem_map_of_mem φ.toMonoidHom hsS
    rw [hSφ] at hmem
    rcases hSeq _ hmem with h | h
    · exact absurd (φ.injective (h.trans φ.map_one.symm)) hsne
    · exact h
  set ψ : DihedralGroup n ≃* DihedralGroup n := e.symm.trans (φ.trans e) with hψdef
  have hψ : ∀ d, ψ d = e (φ (e.symm d)) := fun d => rfl
  have hψψ : ∀ d, ψ (ψ d) = d := by
    intro d
    rw [hψ, hψ, MulEquiv.symm_apply_apply, hφ, MulEquiv.apply_symm_apply]
  have hψj : ψ (sr j) = sr j := by
    rw [hψ, ← hj, MulEquiv.symm_apply_apply, hφs]
  have hhalf := two_mul_half_zmod hn
  have hi : ∀ i : ZMod n, ψ (sr i) = sr i → i = j := by
    intro i hi
    set m : ZMod n := (j - i) * (((n + 1) / 2 : ℕ) : ZMod n) with hm
    have hjm : j - 2 * m = i := by
      rw [hm, ← mul_assoc, mul_comm 2, mul_assoc, hhalf]
      ring
    set g : Q := e.symm (r m) with hg
    have hconj : g * (s : Q) * g⁻¹ = e.symm (sr i) := by
      apply e.injective
      rw [map_mul, map_mul, map_inv, hg, MulEquiv.apply_symm_apply, hj,
        MulEquiv.apply_symm_apply, inv_r, r_mul_sr, sr_mul_r]
      congr 1
      rw [← hjm]
      ring
    have hxfix : φ (e.symm (sr i)) = e.symm (sr i) := by
      have h2 : e (φ (e.symm (sr i))) = sr i := (hψ (sr i)).symm.trans hi
      exact e.injective (by rw [h2, MulEquiv.apply_symm_apply])
    have hcmem : ∀ y, y ∈ conjSubgroup g S ↔ y = 1 ∨ y = e.symm (sr i) := by
      intro y
      rw [mem_conjSubgroup]
      constructor
      · intro hy
        rcases hSeq _ hy with h | h
        · left
          have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
          rw [this, h]
          group
        · right
          have : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
          rw [this, h, hconj]
      · rintro (h | h)
        · rw [h]
          simp
        · rw [h, ← hconj]
          have : g⁻¹ * (g * (s : Q) * g⁻¹) * g = s := by group
          rw [this]
          exact hsS
    have hmapfix : (conjSubgroup g S).map φ.toMonoidHom = conjSubgroup g S := by
      have hfixall : ∀ y ∈ conjSubgroup g S, φ y = y := by
        intro y hy
        rcases (hcmem y).1 hy with h | h
        · rw [h]
          exact map_one φ
        · rw [h]
          exact hxfix
      ext y
      constructor
      · rintro ⟨y', hy', rfl⟩
        have := hfixall y' hy'
        change φ y' ∈ conjSubgroup g S
        rw [this]
        exact hy'
      · intro hy
        exact ⟨y, hy, hfixall y hy⟩
    have hEq := huniq g hmapfix
    have hxS : e.symm (sr i) ∈ S := by
      have : e.symm (sr i) ∈ conjSubgroup g S := (hcmem _).2 (Or.inr rfl)
      rw [hEq] at this
      exact this
    have hx1 : e.symm (sr i) ≠ 1 := by
      intro h
      have := congrArg e h
      rw [MulEquiv.apply_symm_apply, map_one] at this
      have h1 : orderOf (sr i : DihedralGroup n) = 1 := by rw [this]; exact orderOf_one
      rw [orderOf_sr] at h1
      omega
    rcases hSeq _ hxS with h | h
    · exact absurd h hx1
    · have : sr i = sr j := by
        have h3 := congrArg e h
        rw [MulEquiv.apply_symm_apply] at h3
        rw [h3, hj]
      exact DihedralGroup.sr.inj this
  refine ⟨(s : Q), hsS, hsne, fun y => ?_⟩
  have h := dihedral_inner_of_unique_fixed hn ψ hψψ j hψj hi (e y)
  rw [hψ, MulEquiv.symm_apply_apply, ← hj] at h
  apply e.injective
  rw [h, map_mul, map_mul, map_inv]

open DihedralGroup in
theorem SylowInner.of_dihedral {Q : Type} [Group Q] {S : Subgroup Q} {n : ℕ} (hn : Odd n)
    (e : Q ≃* DihedralGroup n) (hS : Nat.card S = 2) : SylowInner Q S := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  have hfin : Finite Q := Finite.of_equiv _ e.symm.toEquiv
  have hcard : Nat.card Q = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 1) (by rw [hS, pow_one])
  have hidx : ¬ 2 ∣ S.index := by
    have h1 := S.index_mul_card
    rw [hS, hcard] at h1
    have h2 : S.index = n := by omega
    rw [h2]
    exact fun h => (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h)
  refine ⟨hfin, fun P => ?_, fun φ hφ g hfix huniq => ?_⟩
  · obtain ⟨g, hg⟩ := exists_conjSubgroup_eq_of_sylow (IsPGroup.toSylow hS2 hidx) P
    exact ⟨g, hg⟩
  · have hS' : Nat.card (conjSubgroup g S) = 2 := by rw [card_conjSubgroup]; exact hS
    exact dihedral_exists_involution_of_unique_fixed hn e hS' φ hφ hfix fun g' hg' => by
      rw [conjSubgroup_conjSubgroup] at hg' ⊢
      exact huniq _ hg'

end CFSG.CGT.Timmesfeld75

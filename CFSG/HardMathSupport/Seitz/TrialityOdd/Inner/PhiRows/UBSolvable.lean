module

public import CFSG.GH74.GLS.SP.GlueT3

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open Subgroup CFSG.GH74.GLS.SP

section Dihedral

variable {Q : Type*} [Group Q]

theorem isSolvable_of_two_involutions (x y : Q) (hx : x * x = 1) (hy : y * y = 1)
    (hgen : Subgroup.closure ({x, y} : Set Q) = ⊤) : Group.IsSolvable Q := by
  set a : Q := x * y with ha
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have hai : a⁻¹ = y * x := by rw [ha, mul_inv_rev, hxi, hyi]
  have hxa : x * a * x⁻¹ = a⁻¹ := by
    rw [hai, ha, hxi]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hx, one_mul]
  have hxz : ∀ i : ℤ, x * a ^ i = a ^ (-i) * x := by
    intro i
    have h : x * a ^ i * x⁻¹ = (x * a * x⁻¹) ^ i := (conj_zpow).symm
    rw [hxa, inv_zpow'] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hy' : y = a⁻¹ * x := by
    rw [hai, mul_assoc, hx, mul_one]
  have hP : ∀ g : Q, (∃ i : ℤ, g = a ^ i) ∨ ∃ i : ℤ, g = a ^ i * x := by
    intro g
    have hg : g ∈ Subgroup.closure ({x, y} : Set Q) := by rw [hgen]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with rfl | hg
      · exact Or.inr ⟨0, by simp⟩
      · rw [Set.mem_singleton_iff] at hg
        subst hg
        exact Or.inr ⟨-1, by rw [zpow_neg_one, hy']⟩
    | one => exact Or.inl ⟨0, by simp⟩
    | mul g h _ _ hg hh =>
      rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hh with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact Or.inl ⟨i + j, by rw [zpow_add]⟩
      · exact Or.inr ⟨i + j, by rw [zpow_add, mul_assoc]⟩
      · refine Or.inr ⟨i - j, ?_⟩
        rw [mul_assoc, hxz j, ← mul_assoc, ← zpow_add, sub_eq_add_neg]
      · refine Or.inl ⟨i - j, ?_⟩
        calc a ^ i * x * (a ^ j * x) = a ^ i * (x * a ^ j) * x := by group
          _ = a ^ i * (a ^ (-j) * x) * x := by rw [hxz j]
          _ = a ^ i * a ^ (-j) * (x * x) := by group
          _ = a ^ (i - j) := by rw [hx, mul_one, ← zpow_add, ← sub_eq_add_neg]
    | inv g _ hg =>
      rcases hg with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact Or.inl ⟨-i, by rw [zpow_neg]⟩
      · refine Or.inr ⟨i, ?_⟩
        rw [mul_inv_rev, hxi, ← zpow_neg, hxz, neg_neg]
  let K : Subgroup Q := Subgroup.zpowers a
  have hKc : ∀ i j : ℤ, a ^ i * a ^ j = a ^ j * a ^ i := fun i j => by
    rw [← zpow_add, ← zpow_add, add_comm]
  have hKn : K.Normal := ⟨by
    rintro _ ⟨m, rfl⟩ g
    rcases hP g with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨m, by group⟩
    · refine ⟨-m, ?_⟩
      have h1 : x * a ^ m * x⁻¹ = a ^ (-m) := by
        rw [hxz m, mul_assoc, mul_inv_cancel, mul_one]
      calc a ^ (-m) = a ^ i * a ^ (-m) * (a ^ i)⁻¹ := by rw [hKc i (-m)]; group
        _ = a ^ i * (x * a ^ m * x⁻¹) * (a ^ i)⁻¹ := by rw [h1]
        _ = (a ^ i * x) * a ^ m * (a ^ i * x)⁻¹ := by group⟩
  have hKs : Group.IsSolvable K := Group.isSolvable_of_comm (fun u v => by
    obtain ⟨u, m, rfl⟩ := u
    obtain ⟨v, n, rfl⟩ := v
    exact Subtype.ext (hKc m n))
  have hcl : ∀ g : Q, (QuotientGroup.mk g : Q ⧸ K) = 1 ∨
      (QuotientGroup.mk g : Q ⧸ K) = QuotientGroup.mk x := by
    intro g
    rcases hP g with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact Or.inl ((QuotientGroup.eq_one_iff _).2 ⟨i, rfl⟩)
    · refine Or.inr ?_
      rw [QuotientGroup.eq]
      refine ⟨i, ?_⟩
      show a ^ i = (a ^ i * x)⁻¹ * x
      rw [mul_inv_rev, hxi, ← zpow_neg, hxz, neg_neg, mul_assoc, hx, mul_one]
  have hQs : Group.IsSolvable (Q ⧸ K) := Group.isSolvable_of_comm (fun u v => by
    induction u using QuotientGroup.induction_on with | _ g
    induction v using QuotientGroup.induction_on with | _ h
    rcases hcl g with hg | hg <;> rcases hcl h with hh | hh <;> simp [hg, hh])
  exact Group.isSolvable_of_subgroup_quotient K

end Dihedral

section Hexagon

variable {X : Type*} [Group X] {n : ℕ} {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem RGD2.isSolvable_N (R : RGD2 n H r₁ r₂ U root) : Group.IsSolvable ↥R.N := by
  classical
  have hr₁ : r₁ ∈ R.N := by
    unfold RGD2.N
    exact Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hr₂ : r₂ ∈ R.N := by
    unfold RGD2.N
    exact Subgroup.subset_closure (Or.inr (Or.inr rfl))
  let K : Subgroup ↥R.N := H.subgroupOf R.N
  have hKn : K.Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    simpa using (R.N_normalizes_H g.2 k hk).1⟩
  have hKs : Group.IsSolvable ↥K := Group.isSolvable_of_comm (fun u v =>
    Subtype.ext (Subtype.ext (R.comm_H _ u.2 _ v.2)))
  let f : ↥R.N →* ↥R.N ⧸ K := QuotientGroup.mk' K
  set x : ↥R.N ⧸ K := f ⟨r₁, hr₁⟩ with hxdef
  set y : ↥R.N ⧸ K := f ⟨r₂, hr₂⟩ with hydef
  have hx : x * x = 1 := by
    rw [hxdef, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact R.sq₁
  have hy : y * y = 1 := by
    rw [hydef, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact R.sq₂
  have htop : Subgroup.closure (((↑) : ↥R.N → X) ⁻¹' ((H : Set X) ∪ {r₁, r₂})) = ⊤ := by
    unfold RGD2.N
    exact Subgroup.closure_closure_coe_preimage
  have hgen : Subgroup.closure ({x, y} : Set (↥R.N ⧸ K)) = ⊤ := by
    rw [eq_top_iff]
    rintro q -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ (⊤ : Subgroup ↥R.N) := Subgroup.mem_top g
    rw [← htop] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      rcases hg with hg | hg
      · have : f g = 1 := (QuotientGroup.eq_one_iff _).2 hg
        show f g ∈ _
        rw [this]
        exact Subgroup.one_mem _
      · rcases hg with hg | hg
        · have : g = ⟨r₁, hr₁⟩ := Subtype.ext hg
          show f g ∈ _
          rw [this]
          exact Subgroup.subset_closure (Or.inl rfl)
        · rw [Set.mem_singleton_iff] at hg
          have : g = ⟨r₂, hr₂⟩ := Subtype.ext hg
          show f g ∈ _
          rw [this]
          exact Subgroup.subset_closure (Or.inr rfl)
    | one => exact Subgroup.one_mem _
    | mul g h _ _ hg hh =>
      show f (g * h) ∈ _
      rw [map_mul]
      exact Subgroup.mul_mem _ hg hh
    | inv g _ hg =>
      show f g⁻¹ ∈ _
      rw [map_inv]
      exact Subgroup.inv_mem _ hg
  have hQs : Group.IsSolvable (↥R.N ⧸ K) := isSolvable_of_two_involutions x y hx hy hgen
  exact Group.isSolvable_of_subgroup_quotient K

end Hexagon

section Perfect

variable {X : Type*} [Group X]

theorem le_of_perfect_of_le_sup_normalizing (L N P : Subgroup X) [Group.IsSolvable N]
    (hnorm : ∀ n ∈ N, ∀ l ∈ L, n * l * n⁻¹ ∈ L) (hP : ⁅P, P⁆ = P) (hPle : P ≤ L ⊔ N) :
    P ≤ L := by
  classical
  have hLN : ∀ m ∈ L ⊔ N, ∃ l ∈ L, ∃ n ∈ N, m = l * n := by
    let LN : Subgroup X :=
      { carrier := {m | ∃ l ∈ L, ∃ n ∈ N, m = l * n}
        mul_mem' := by
          rintro _ _ ⟨l, hl, n, hn, rfl⟩ ⟨l', hl', n', hn', rfl⟩
          refine ⟨l * (n * l' * n⁻¹), L.mul_mem hl (hnorm n hn l' hl'), n * n', N.mul_mem hn hn', ?_⟩
          group
        one_mem' := ⟨1, L.one_mem, 1, N.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨l, hl, n, hn, rfl⟩
          refine ⟨n⁻¹ * l⁻¹ * n⁻¹⁻¹, ?_, n⁻¹, N.inv_mem hn, ?_⟩
          · exact hnorm n⁻¹ (N.inv_mem hn) l⁻¹ (L.inv_mem hl)
          · group }
    have : L ⊔ N ≤ LN := sup_le (fun l hl => ⟨l, hl, 1, N.one_mem, by simp⟩)
      (fun n hn => ⟨1, L.one_mem, n, hn, by simp⟩)
    exact fun m hm => this hm
  set M : Subgroup X := L ⊔ N with hM
  have hMn : ∀ g ∈ M, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    obtain ⟨l', hl', n, hn, rfl⟩ := hLN g hg
    have h1 : n * l * n⁻¹ ∈ L := hnorm n hn l hl
    have e : l' * n * l * (l' * n)⁻¹ = l' * (n * l * n⁻¹) * l'⁻¹ := by group
    rw [e]
    exact L.mul_mem (L.mul_mem hl' h1) (L.inv_mem hl')
  let L' : Subgroup ↥M := L.subgroupOf M
  have hL'n : L'.Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    simpa using hMn g g.2 k hk⟩
  let ψ : ↥N →* ↥M ⧸ L' := (QuotientGroup.mk' L').comp (Subgroup.inclusion (le_sup_right : N ≤ M))
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨l, hl, n, hn, rfl⟩ := hLN m hm
    refine ⟨⟨n, hn⟩, ?_⟩
    show (QuotientGroup.mk (⟨n, (le_sup_right : N ≤ M) hn⟩ : ↥M) : ↥M ⧸ L') = QuotientGroup.mk ⟨l * n, hm⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := hnorm n⁻¹ (N.inv_mem hn) l hl
    simpa [mul_assoc] using this
  have hQs : Group.IsSolvable (↥M ⧸ L') := Group.isSolvable_of_surjective hψ
  let P' : Subgroup ↥M := P.subgroupOf M
  have hP' : ⁅P', P'⁆ = P' := by
    apply Subgroup.map_injective M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hPle, hP]
  let R := P'.map (QuotientGroup.mk' L')
  have hR : ⁅R, R⁆ = R := by
    show ⁅P'.map (QuotientGroup.mk' L'), P'.map (QuotientGroup.mk' L')⁆ = _
    rw [← Subgroup.map_commutator, hP']
  have hRbot : R = ⊥ := by
    by_contra h
    exact (Group.IsSolvable.commutator_lt_of_ne_bot h).ne hR
  intro p hp
  have h1 : (⟨p, hPle hp⟩ : ↥M) ∈ P' := hp
  have h2 : QuotientGroup.mk' L' ⟨p, hPle hp⟩ ∈ R := Subgroup.mem_map_of_mem _ h1
  rw [hRbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact h2

end Perfect

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

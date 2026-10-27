module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutKSq
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KSubgroupL1

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F : Subgroup G}

namespace OutOne

omit [Finite G] in
theorem phiv_eq_one_of_mem_F (h : OutOne L z F) {u : G} (hu : u ∈ F) :
    phiv z u = 1 :=
  (phiv_eq_one_iff h (E_le_K h (Subgroup.mem_sup_left hu))).2 (Subgroup.mem_sup_left hu)

omit [Finite G] in
theorem mul_mem_L1set (h : OutOne L z F) (hgood : GoodK z F) {k k' : G}
    (hk : k ∈ L1set z F) (hk' : k' ∈ L1set z F) : k * k' ∈ L1set z F := by
  obtain ⟨hkK, hk2, hkF⟩ := hk
  obtain ⟨hkK', hk2', hkF'⟩ := hk'
  have hmulK : k * k' ∈ Ksub z F := Subgroup.mul_mem _ hkK hkK'
  by_cases hk1 : k ∈ F
  ·
    have hc : k * k' = k' * k := ((mem_Ksub.1 hkK').2 k hk1)
    refine ⟨hmulK, ?_, ?_⟩
    · calc k * k' * (k * k') = k * (k' * k) * k' := by simp only [mul_assoc]
        _ = k * (k * k') * k' := by rw [← hc]
        _ = (k * k) * (k' * k') := by simp only [mul_assoc]
        _ = 1 := by rw [hk2, hk2', mul_one]
    · rcases hkF' with hF' | hphi'
      · left
        exact Subgroup.mul_mem _ hk1 hF'
      · right
        rw [phiv_mul h hkK hkK', phiv_eq_one_of_mem_F h hk1, one_mul]
        exact hphi'
  · have hphi : phiv z k ≠ 1 := hkF.resolve_left hk1
    by_cases hk1' : k' ∈ F
    · have hc : k * k' = k' * k := ((mem_Ksub.1 hkK).2 k' hk1').symm
      refine ⟨hmulK, ?_, Or.inr ?_⟩
      · calc k * k' * (k * k') = k * (k' * k) * k' := by simp only [mul_assoc]
          _ = k * (k * k') * k' := by rw [← hc]
          _ = (k * k) * (k' * k') := by simp only [mul_assoc]
          _ = 1 := by rw [hk2, hk2', mul_one]
      · rw [phiv_mul h hkK hkK', phiv_eq_one_of_mem_F h hk1', mul_one]
        exact hphi
    · have hphi' : phiv z k' ≠ 1 := hkF'.resolve_left hk1'
      by_cases hfeq : phiv z k = phiv z k'
      ·
        obtain ⟨u, hu, hku⟩ := (involutions_eq h hkK hk2 hphi).1 ⟨hkK', hfeq.symm, hk2'⟩
        have : k * k' = u := by
          rw [hku, ← mul_assoc, hk2, one_mul]
        refine ⟨hmulK, ?_, Or.inl (this ▸ hu)⟩
        rw [this]
        exact h.F_sq u hu
      · refine ⟨hmulK, hgood k hkK k' hkK' hk2 hk2' hphi hphi' hfeq, Or.inr ?_⟩
        rw [phiv_mul h hkK hkK']
        intro hprod
        apply hfeq
        have hfF := phiv_mem h hkK
        have hfF' := phiv_mem h hkK'
        calc phiv z k = phiv z k * (phiv z k' * phiv z k') := by rw [h.F_sq _ hfF', mul_one]
          _ = (phiv z k * phiv z k') * phiv z k' := by simp only [mul_assoc]
          _ = phiv z k' := by rw [hprod, one_mul]

@[expose] def L1sub (h : OutOne L z F) (hgood : GoodK z F) : Subgroup G where
  carrier := L1set z F
  mul_mem' := fun hk hk' => mul_mem_L1set h hgood hk hk'
  one_mem' := mem_L1set.2 ⟨Subgroup.one_mem _, mul_one 1, Or.inl (Subgroup.one_mem F)⟩
  inv_mem' := fun {k} hk => by
    obtain ⟨hkK, hk2, hkF⟩ := hk
    have hki : k⁻¹ = k := inv_eq_of_mul_eq_one_right hk2
    rw [hki]
    exact ⟨hkK, hk2, hkF⟩

omit [Finite G] in
theorem mem_L1sub (h : OutOne L z F) (hgood : GoodK z F) {k : G} :
    k ∈ L1sub h hgood ↔ k ∈ Ksub z F ∧ k * k = 1 ∧ (k ∈ F ∨ phiv z k ≠ 1) := Iff.rfl

omit [Finite G] in
theorem L1sub_le_K (h : OutOne L z F) (hgood : GoodK z F) :
    L1sub h hgood ≤ Ksub z F := fun _ hk => hk.1

omit [Finite G] in
theorem F_le_L1sub (h : OutOne L z F) (hgood : GoodK z F) :
    F ≤ L1sub h hgood := fun _ hu =>
  (mem_L1sub h hgood).2 ⟨E_le_K h (Subgroup.mem_sup_left hu), h.F_sq _ hu, Or.inl hu⟩

omit [Finite G] in
theorem L1sub_sq (h : OutOne L z F) (hgood : GoodK z F) {k : G}
    (hk : k ∈ L1sub h hgood) : k * k = 1 := hk.2.1

omit [Finite G] in
theorem L1sub_comm (h : OutOne L z F) (hgood : GoodK z F) {x y : G}
    (hx : x ∈ L1sub h hgood) (hy : y ∈ L1sub h hgood) : x * y = y * x := by
  have h1 : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_right (L1sub_sq h hgood (Subgroup.mul_mem _ hx hy))
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (L1sub_sq h hgood hy),
    inv_eq_of_mul_eq_one_right (L1sub_sq h hgood hx)] at h1
  exact h1.symm

omit [Finite G] in
theorem z_not_mem_L1sub (h : OutOne L z F) (hgood : GoodK z F) :
    z ∉ L1sub h hgood := by
  rintro ⟨-, -, hF | hphi⟩
  · exact h.z_not_mem (h.F_le hF)
  · apply hphi
    unfold phiv
    simp [h.z_mul_self]

omit [Finite G] in
theorem L1sub_inf_E (h : OutOne L z F) (hgood : GoodK z F) {x : G}
    (hx : x ∈ L1sub h hgood) (hxE : x ∈ F ⊔ zpowers z) : x ∈ F := by
  obtain ⟨hxK, -, hF | hphi⟩ := hx
  · exact hF
  · exact absurd ((phiv_eq_one_iff h hxK).2 hxE) hphi

omit [Finite G] in
theorem L1sub_centralizer_z (h : OutOne L z F) (hgood : GoodK z F) {x : G}
    (hx : x ∈ L1sub h hgood) (hxz : z * x = x * z) : x ∈ F := by
  refine L1sub_inf_E h hgood hx ((phiv_eq_one_iff h hx.1).1 ?_)
  unfold phiv
  rw [show x * z * x⁻¹ = z by rw [← hxz]; group, h.z_mul_self]

omit [Finite G] in
theorem phiv_z_self (h : OutOne L z F) : phiv z z = 1 := by
  unfold phiv
  simp [h.z_mul_self]

theorem mem_L1sub_or (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F) {k : G} (hk : k ∈ Ksub z F) :
    k ∈ L1sub h hgood ∨ k * z ∈ L1sub h hgood := by
  have hzK : z ∈ Ksub z F := E_le_K h (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  by_cases hf1 : phiv z k = 1
  · obtain ⟨u, hu, b, hb, hub⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (zpowers_le_cent h h.F_le) ((phiv_eq_one_iff h hk).1 hf1)
    rcases mem_zpowers_involution h.z_mul_self hb with hb1 | hbz
    · left
      rw [hub, hb1, mul_one]
      exact F_le_L1sub h hgood hu
    · right
      rw [hub, hbz, mul_assoc, h.z_mul_self, mul_one]
      exact F_le_L1sub h hgood hu
  · rcases sq_mem_pair h hsq X hk hf1 with h1 | h1
    · exact Or.inl ((mem_L1sub h hgood).2 ⟨hk, h1, Or.inr hf1⟩)
    · right
      refine (mem_L1sub h hgood).2 ⟨Subgroup.mul_mem _ hk hzK, ?_, Or.inr ?_⟩
      · have := sq_mul_zF h hk (Subgroup.one_mem F)
        simp only [one_mul] at this
        rw [this, h1]
        exact h.F_sq _ (phiv_mem h hk)
      · rw [phiv_mul h hk hzK, phiv_z_self h, mul_one]
        exact hf1

theorem conj_mem_Ksub_of_normalizes (h : OutOne L z F) {n k : G}
    (hn : ∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) (hk : k ∈ Ksub z F) :
    n * k * n⁻¹ ∈ Ksub z F := by
  have hnF := normalizes_F h hn
  obtain ⟨hkE, hkF⟩ := mem_Ksub.1 hk
  refine mem_Ksub.2 ⟨fun x => ?_, fun f hf => ?_⟩
  · have e1 := hn (n⁻¹ * x * n)
    rw [show n * (n⁻¹ * x * n) * n⁻¹ = x by group] at e1
    have e2 := hkE (n⁻¹ * x * n)
    have e3 := hn (k * (n⁻¹ * x * n) * k⁻¹)
    rw [show n * (k * (n⁻¹ * x * n) * k⁻¹) * n⁻¹ = n * k * n⁻¹ * x * (n * k * n⁻¹)⁻¹ by group]
      at e3
    exact e1.symm.trans (e2.trans e3)
  · have hf' : n⁻¹ * f * n ∈ F := by
      have e := hnF (n⁻¹ * f * n)
      rw [show n * (n⁻¹ * f * n) * n⁻¹ = f by group] at e
      exact e.2 hf
    have e := hkF (n⁻¹ * f * n) hf'
    calc f * (n * k * n⁻¹) = n * ((n⁻¹ * f * n) * k) * n⁻¹ := by group
      _ = n * (k * (n⁻¹ * f * n)) * n⁻¹ := by rw [e]
      _ = n * k * n⁻¹ * f := by group

theorem L1_normalized (h : OutOne L z F) (hgood : GoodK z F)
    {n : G} (hn : ∀ x, x ∈ F ⊔ zpowers z ↔ n * x * n⁻¹ ∈ F ⊔ zpowers z) :
    ∀ x, x ∈ L1sub h hgood ↔ n * x * n⁻¹ ∈ L1sub h hgood := by
  have hnF := normalizes_F h hn
  apply forall_mem_iff_of_forall_mem
  intro x hx
  obtain ⟨hxK, hx2, hxF⟩ := hx
  refine (mem_L1sub h hgood).2 ⟨conj_mem_Ksub_of_normalizes h hn hxK, ?_, ?_⟩
  · calc n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  · rcases hxF with hF | hphi
    · exact Or.inl ((hnF x).1 hF)
    · right
      intro hcon
      apply hphi
      have hxE : x ∈ F ⊔ zpowers z :=
        (hn x).2 ((phiv_eq_one_iff h (conj_mem_Ksub_of_normalizes h hn hxK)).1 hcon)
      exact (phiv_eq_one_iff h hxK).2 hxE

theorem card_L1sub (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f) : Nat.card (L1sub h hgood) = 256 := by
  let ψ : L1sub h hgood →* F :=
    (phiHomO h).comp (Subgroup.inclusion (L1sub_le_K h hgood))
  have hψ : ∀ x : L1sub h hgood, ((ψ x : F) : G) = phiv z (x : G) := fun x => rfl
  have hsurj : Function.Surjective ψ := by
    rintro ⟨f, hf⟩
    by_cases hf1 : f = 1
    · have h0 : phiv z 1 = 1 := by
        unfold phiv
        simp [h.z_mul_self]
      refine ⟨1, Subtype.ext ?_⟩
      rw [hψ]
      exact h0.trans hf1.symm
    · obtain ⟨x, hxK, hxf, hx2⟩ := exists_involution h hsq X htrans hf hf1
      refine ⟨⟨x, (mem_L1sub h hgood).2 ⟨hxK, hx2, Or.inr (hxf ▸ hf1)⟩⟩, ?_⟩
      exact Subtype.ext (by rw [hψ]; exact hxf)
  have hker : Nat.card ψ.ker = 16 := by
    rw [← h.F_card]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ψ.ker => (⟨(x.1 : G), ?_⟩ : F)) ⟨?_, ?_⟩)
    · have h1 : phiv z (x.1 : G) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 x.2)
        rwa [hψ] at this
      exact L1sub_inf_E h hgood x.1.2 ((phiv_eq_one_iff h (L1sub_le_K h hgood x.1.2)).1 h1)
    · intro x y hxy
      have h1 : ((x.1 : L1sub h hgood) : G) = ((y.1 : L1sub h hgood) : G) :=
        congrArg (fun e : F => (e : G)) hxy
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨u, hu⟩
      refine ⟨⟨⟨u, F_le_L1sub h hgood hu⟩, ?_⟩, rfl⟩
      rw [MonoidHom.mem_ker]
      exact Subtype.ext (by rw [hψ]; exact phiv_eq_one_of_mem_F h hu)
  have := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, h.F_card] at this
  omega

theorem Ksub_eq_L1_sup (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F) : Ksub z F = L1sub h hgood ⊔ zpowers z := by
  apply le_antisymm
  · intro k hk
    rcases mem_L1sub_or h hsq hgood X hk with h1 | h1
    · exact Subgroup.mem_sup_left h1
    · have : k = k * z * z⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers z)))
  · refine sup_le (L1sub_le_K h hgood) ?_
    rw [Subgroup.zpowers_le]
    exact E_le_K h (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))

end OutOne

end CFSG.EvenSporadicStandard.M22Std

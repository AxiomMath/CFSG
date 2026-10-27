module

public import CFSG.LargeExtraspecial.S111ATrans
public import CFSG.LargeExtraspecial.S5Four
public import CFSG.LargeExtraspecial.S111ADisj
public import CFSG.LargeExtraspecial.S5Three

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

theorem exists_form_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {p : Submodule (ZMod 2) V} {x : V} (hx : x ∉ p) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, f x = 1 ∧ ∀ v ∈ p, f v = 0 := by
  obtain ⟨f, hfx, hfp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨f, ?_, fun v hv => ?_⟩
  · rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (f x) with h | h
    · exact absurd h hfx
    · exact h
  · have h1 : f v ∈ p.map f := ⟨v, hv, rfl⟩
    rw [hfp] at h1
    exact h1

theorem exists_mem_not_mem_finset_submodule {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V]
    (U : Submodule (ZMod 2) V) (s : Finset V) (hs : s.card < Nat.card U) :
    ∃ v ∈ U, v ∉ s := by
  by_contra hcon
  push Not at hcon
  have hsub : (U : Set V) ⊆ (s : Set V) := fun v hv => hcon v hv
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq] at h1
  exact absurd (lt_of_lt_of_le hs h1) (lt_irrefl _)

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G} {A : Subgroup G}

theorem IncClosed.exists_mem_Lbar (hA : IncClosed S A) {k : G} (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (f : S.Qt →ₗ[ZMod 2] ZMod 2)
    (hf : f (S.cl (k * S.z * k⁻¹)) = 0) :
    ∃ t ∈ S.Lbar k, ∀ v ∈ S.clSub A,
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + f v • S.cl (k * S.z * k⁻¹) := by
  obtain ⟨y, hy, hyv⟩ := hA.exists_transvection hk hkz f hf
  exact ⟨S.ρ y, ρ_mem_Lbar S hy, hyv⟩

theorem IncClosed.exists_three (hA : IncClosed S A) {k : G} (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) (h8 : 8 ≤ Nat.card (S.clSub A)) :
    ∃ t₁ ∈ S.Lbar k, ∃ t₂ ∈ S.Lbar k,
      (∃ v ∈ S.clSub A, (t₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v) ∧
      (∃ v ∈ S.clSub A, (t₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v) ∧
      (∃ v ∈ S.clSub A, ((t₁ * t₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v) := by
  classical
  set a := S.cl (k * S.z * k⁻¹) with ha
  have hkQ := hA.le_QG hk
  have ha0 : a ≠ 0 := cl_conj_z_ne_zero S hkQ hkz
  have haA : a ∈ S.clSub A := S.cl_mem_clSub hk hkQ
  obtain ⟨v₁, hv₁, hv₁s⟩ := exists_mem_not_mem_finset_submodule (S.clSub A) {0, a}
    (lt_of_lt_of_le (lt_of_le_of_lt (Finset.card_le_two) (by norm_num)) h8)
  obtain ⟨v₂, hv₂, hv₂s⟩ := exists_mem_not_mem_finset_submodule (S.clSub A) {0, a, v₁, a + v₁}
    (lt_of_lt_of_le (lt_of_le_of_lt (Finset.card_le_four) (by norm_num)) h8)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv₁s hv₂s
  obtain ⟨hv₁0, hv₁a⟩ := hv₁s
  obtain ⟨hv₂0, hv₂a, hv₂1, hv₂a1⟩ := hv₂s
  have hv₁p : v₁ ∉ Submodule.span (ZMod 2) {a, v₂} := by
    rw [Submodule.mem_span_pair]
    rintro ⟨r, s, hrs⟩
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases r with rfl | rfl <;>
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases s with rfl | rfl
    · simp at hrs; exact hv₁0 hrs.symm
    · simp at hrs; exact hv₂1 hrs
    · simp at hrs; exact hv₁a hrs.symm
    · simp only [one_smul] at hrs
      apply hv₂a1
      rw [← hrs, ← add_assoc, ZModModule.add_self, zero_add]
  obtain ⟨f₁, hf₁v, hf₁p⟩ := exists_form_eq_one hv₁p
  have hf₁a : f₁ a = 0 := hf₁p a (Submodule.subset_span (by simp))
  have hf₁2 : f₁ v₂ = 0 := hf₁p v₂ (Submodule.subset_span (by simp))
  have hv₂p : v₂ ∉ (ZMod 2) ∙ a := by
    rw [mem_span_cl_iff]
    rintro (h | h)
    · exact hv₂0 h
    · exact hv₂a h
  obtain ⟨f₂, hf₂v, hf₂p⟩ := exists_form_eq_one hv₂p
  have hf₂a : f₂ a = 0 := hf₂p a (Submodule.mem_span_singleton_self a)
  obtain ⟨t₁, ht₁, ht₁v⟩ := hA.exists_mem_Lbar hk hkz f₁ hf₁a
  obtain ⟨t₂, ht₂, ht₂v⟩ := hA.exists_mem_Lbar hk hkz f₂ hf₂a
  have hne : ∀ v : S.Qt, v + a ≠ v := fun v h => ha0 (by
    have := congrArg (fun x => x - v) h
    simpa using this)
  refine ⟨t₁, ht₁, t₂, ht₂, ⟨v₁, hv₁, ?_⟩, ⟨v₂, hv₂, ?_⟩, ⟨v₂, hv₂, ?_⟩⟩
  · rw [ht₁v v₁ hv₁, hf₁v, one_smul]
    exact hne v₁
  · rw [ht₂v v₂ hv₂, hf₂v, one_smul]
    exact hne v₂
  · rw [coe_mul_apply, ht₂v v₂ hv₂, hf₂v, one_smul,
      ht₁v (v₂ + a) (Submodule.add_mem _ hv₂ haA), map_add, hf₁2, hf₁a, add_zero, zero_smul,
      add_zero]
    exact hne v₂

theorem Cfg111.eq_bot_of_odd (C : Cfg111 S g A) (h6 : 6 ≤ S.width) {k : G}
    (hk : k * S.z * k⁻¹ ∈ A) (hkz : k * S.z * k⁻¹ ≠ S.z) (h16 : 16 ≤ Nat.card A)
    {F : Subgroup S.O} (hFM : F ≤ S.Mbar) (hodd : Odd (Nat.card F))
    (hnorm : ∀ s ∈ S.Lbar k, ∀ x ∈ F, s * x * s⁻¹ ∈ F) : F = ⊥ := by
  by_contra hF
  have hkQ := C.inc.le_QG hk
  have hy : Hyp S k := C.hy.of_conj hkQ hkz
  have h3 : Nat.card F = 3 := S5.timmesfeld_5_4 hy.hyp4 hy.noA2' hy.cons
    (by omega) hFM hodd hF hnorm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm := (S5.timmesfeld_5_3 hy.hyp4 hy.noA2' hy.cons hFM (isCyclic_of_prime_card h3)
    hodd hF hnorm).2
  obtain ⟨⟨w, hwF⟩, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
  have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
  have hdich : ∀ s ∈ S.Lbar k, s * w * s⁻¹ = w ∨ s * w * s⁻¹ = w⁻¹ := fun s hs =>
    S5.conj_eq_self_or_inv_of_card_eq_three hy.hyp4 h3 hnorm hwF hs
  have hw3 : w ^ 3 = 1 := by
    have := pow_card_eq_one' (G := F) (x := ⟨w, hwF⟩)
    rw [h3] at this
    exact congrArg Subtype.val this
  have hord : orderOf w = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hw3) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1'
    · exact h
  have hzF : zpowers w = F := Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwF)
    (by rw [Nat.card_zpowers, hord, h3])
  obtain ⟨s₀, hs₀, hs₀w⟩ : ∃ s₀ ∈ S.Lbar k, s₀ * w * s₀⁻¹ = w⁻¹ := by
    by_contra hcon
    push Not at hcon
    apply hcomm
    rw [commutator_eq_bot_iff_le_centralizer, ← hzF, zpowers_le, mem_centralizer_iff]
    intro s hs
    have e := (hdich s hs).resolve_right (hcon s hs)
    calc s * w = s * w * s⁻¹ * s := by group
      _ = w * s := by rw [e]
  have hLw : (S.Lbar k).map (MulAut.conj w).toMonoidHom ≠ S.Lbar k := by
    intro he
    have h1 : w * s₀ * w⁻¹ ∈ S.Lbar k := by rw [← he]; exact ⟨s₀, hs₀, rfl⟩
    have h2 : w * s₀ * w⁻¹ * s₀⁻¹ ∈ S.Lbar k := mul_mem h1 (inv_mem hs₀)
    have e : w * s₀ * w⁻¹ * s₀⁻¹ = w * w := by
      have e1 : s₀ * w⁻¹ * s₀⁻¹ = w := by
        calc s₀ * w⁻¹ * s₀⁻¹ = (s₀ * w * s₀⁻¹)⁻¹ := by group
          _ = w := by rw [hs₀w, inv_inv]
      calc w * s₀ * w⁻¹ * s₀⁻¹ = w * (s₀ * w⁻¹ * s₀⁻¹) := by group
        _ = w * w := by rw [e1]
    rw [e] at h2
    have h4 := mul_self_of_mem_Lbar S hkQ h2
    apply hw1'
    calc w = (w * w * (w * w)) * (w ^ 3)⁻¹ := by group
      _ = 1 := by rw [h4, hw3, one_mul, inv_one]
  have h8 : 8 ≤ Nat.card (S.clSub A) := by
    have := C.inc.card_eq
    omega
  obtain ⟨t₁, ht₁, t₂, ht₂, hv₁, hv₂, hv₁₂⟩ := C.inc.exists_three hk hkz h8
  obtain ⟨t, ht, htw, v, hv, htv⟩ : ∃ t ∈ S.Lbar k, t * w = w * t ∧
      ∃ v ∈ S.clSub A, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v ≠ v := by
    have hcw : ∀ s : S.O, s * w * s⁻¹ = w → s * w = w * s := fun s e => by
      calc s * w = s * w * s⁻¹ * s := by group
        _ = w * s := by rw [e]
    rcases hdich t₁ ht₁ with e₁ | e₁
    · exact ⟨t₁, ht₁, hcw _ e₁, hv₁⟩
    rcases hdich t₂ ht₂ with e₂ | e₂
    · exact ⟨t₂, ht₂, hcw _ e₂, hv₂⟩
    refine ⟨t₁ * t₂, mul_mem ht₁ ht₂, hcw _ ?_, hv₁₂⟩
    calc t₁ * t₂ * w * (t₁ * t₂)⁻¹ = t₁ * (t₂ * w * t₂⁻¹) * t₁⁻¹ := by group
      _ = (t₁ * w * t₁⁻¹)⁻¹ := by rw [e₂]; group
      _ = w := by rw [e₁, inv_inv]
  obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp (hFM hwF)
  have htm : t ∈ S.Lbar ((m : G) * k) := by
    rw [mem_Lbar_mul_iff, hm]
    rwa [show w⁻¹ * t * w = t by rw [mul_assoc, htw, inv_mul_cancel_left]]
  have ht1 : t ≠ 1 := fun h => htv (by rw [h]; rfl)
  have hne : S.Lbar k ⊓ S.Lbar ((m : G) * k) ≠ ⊥ := fun h0 => ht1 (by
    have hmem : t ∈ S.Lbar k ⊓ S.Lbar ((m : G) * k) := ⟨ht, htm⟩
    rw [h0] at hmem
    exact (Subgroup.mem_bot).mp hmem)
  have hmQ := conj_mem_QG' S m.2 hkQ
  have hmA := C.mem_of_Lbar_inf_ne_bot hk hkz hmQ (conj_ne_z' S m.2 hkz) hne
  have hcl : S.cl ((m : G) * k * S.z * ((m : G) * k)⁻¹) ≠ S.cl (k * S.z * k⁻¹) := fun h =>
    hLw (by rw [← hm, ← Lbar_mul S m k]; exact Lbar_eq_of_cl_eq S hkQ hkz hmQ h)
  have h1 := mem_span_cl_iff.mp (C.inc.apply_sub_mem_span hk ht hv)
  have h2 := mem_span_cl_iff.mp (C.inc.apply_sub_mem_span hmA htm hv)
  rcases h1 with h1 | h1
  · exact htv (sub_eq_zero.mp h1)
  rcases h2 with h2 | h2
  · exact htv (sub_eq_zero.mp h2)
  exact hcl (h2.symm.trans h1)

end CFSG.LargeExtraspecial.S11

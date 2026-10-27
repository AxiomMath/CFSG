module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxNine
public import CFSG.GF2Type.Aschbacher1976Full.HSCruxInterfaces

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.CruxNine

open Equiv CFSG.GF2Type.Aschbacher1976Full.HS

theorem pres_of_normal {g : Perm (Fin 6)} (h1 : ∀ e ∈ E9l, g * e * g⁻¹ ∈ E9l)
    (h2 : ∀ e ∈ E9l, g⁻¹ * e * g ∈ E9l) : Pres g := by
  intro x y
  have hA := E9_orbit x y
  have hB := E9_orbit (g x) (g y)
  rw [← hA, ← hB]
  constructor
  · rintro ⟨e, he, hex⟩
    refine ⟨g * e * g⁻¹, h1 e he, ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, hex]
  · rintro ⟨e, he, hex⟩
    refine ⟨g⁻¹ * e * g, h2 e he, ?_⟩
    rw [Perm.mul_apply, Perm.mul_apply, hex, Perm.inv_def, Equiv.symm_apply_apply]

theorem mem_nineL_of_mem_nineSet {s : Perm (Fin 6)} (hs : s ∈ nineSet) : s ∈ nineL := by
  obtain ⟨a, b, d, e, ha, hb, hd, he, hab, hde, rfl⟩ := hs
  exact nineSet_sub_nineL a b d e ha hb hd he hab hde

theorem mem_nineSet_of (a b d e : Fin 6) (ha : (a : ℕ) < 3) (hb : (b : ℕ) < 3) (hd : 3 ≤ (d : ℕ))
    (he : 3 ≤ (e : ℕ)) (hab : a ≠ b) (hde : d ≠ e) : swap a b * swap d e ∈ nineSet :=
  ⟨a, b, d, e, ha, hb, hd, he, hab, hde, rfl⟩

theorem mem_nineSet_of_mem_nineL {s : Perm (Fin 6)} (hs : s ∈ nineL) : s ∈ nineSet := by
  simp only [nineL, List.mem_cons, List.mem_nil_iff, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_nineSet_of 0 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 0 1 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 0 1 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 0 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 0 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 1 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 1 2 3 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
  · exact mem_nineSet_of 1 2 4 5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)

theorem eq_one_of_pow_three {Q : Type} [Group Q] {w : Q} (h3 : w ^ 3 = 1) {k : ℕ}
    (hk : w ^ 2 ^ k = 1) : w = 1 := by
  have h1 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
  have h4 : orderOf w ∣ 1 := by
    have := Nat.dvd_gcd h1 h2
    rwa [hg] at this
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

@[expose] def E9sub : Subgroup (Perm (Fin 6)) where
  carrier := {e | e ∈ E9l}
  mul_mem' := fun {a b} ha hb => E9_mul a ha b hb
  one_mem' := E9_one
  inv_mem' := fun {a} ha => E9_inv a ha

theorem main_of_nine {Q : Type} [Group Q] (ι : Q →* Perm (Fin 6)) (hι : Function.Injective ι)
    (D : Set Q) (hconj : ∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ ∈ D) (hD : ∀ d ∈ D, ι d ∈ nineSet)
    (hS : ∀ s ∈ nineSet, ∃ d ∈ D, ι d = s) : NineFree D ∧ TbarFacts D := by
  have hNs : ∀ q : Q, ∀ s ∈ nineSet, ι q * s * (ι q)⁻¹ ∈ nineSet := by
    intro q s hs
    obtain ⟨d, hd, rfl⟩ := hS s hs
    simpa [map_mul, map_inv] using hD _ (hconj q d hd)
  have hE : ∀ q : Q, ∀ e ∈ E9l, ι q * e * (ι q)⁻¹ ∈ E9l := by
    intro q e he
    obtain ⟨s, hs, t, ht, rfl⟩ := E9_prod e he
    have h1 : ι q * (s * t) * (ι q)⁻¹ = (ι q * s * (ι q)⁻¹) * (ι q * t * (ι q)⁻¹) := by group
    rw [h1]
    exact nineL_prod _ (mem_nineL_of_mem_nineSet (hNs q s (mem_nineSet_of_mem_nineL hs)))
      _ (mem_nineL_of_mem_nineSet (hNs q t (mem_nineSet_of_mem_nineL ht)))
  have hNl : ∀ q : Q, ι q ∈ Nl := by
    intro q
    refine mem_Nl.2 (pres_of_normal (fun e he => hE q e he) (fun e he => ?_))
    have := hE q⁻¹ e he
    rwa [map_inv, inv_inv] at this
  have hmul : ∀ q q' : Q, act (ι (q * q')) = act (ι q) ∘ act (ι q') := by
    intro q q'
    funext x
    rw [map_mul]
    exact act_hom _ (hNl q) _ (hNl q') x
  have hone : act (ι 1) = id := by rw [map_one]; exact act_one
  have hD' : ∀ d ∈ D, act (ι d) = cI := fun d hd => nineL_act _ (mem_nineL_of_mem_nineSet (hD d hd))
  have hker : ∀ w : Q, act (ι w) = id → ι w ∈ E9l := fun w hw => Nl_ker _ (hNl w) hw
  have hTbar : TbarFacts D := by
    intro S hSp a ha haS
    have hinj : ∀ u ∈ S, ∀ v ∈ S, act (ι u) = act (ι v) → u = v := by
      intro u hu v hv huv
      have hw : u * v⁻¹ ∈ S := S.mul_mem hu (S.inv_mem hv)
      have hid : act (ι (u * v⁻¹)) = id := by
        rw [hmul, huv, ← hmul, mul_inv_cancel, hone]
      have h3 : (u * v⁻¹) ^ 3 = 1 := hι (by rw [map_pow, map_one]; exact E9_cube _ (hker _ hid))
      obtain ⟨k, hk⟩ := hSp ⟨u * v⁻¹, hw⟩
      have hk' : (u * v⁻¹) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      exact mul_inv_eq_one.1 (eq_one_of_pow_three h3 hk')
    refine ⟨?_, ?_, ?_⟩
    ·
      intro x hx
      have hxx : x * x ∈ S := S.mul_mem hx hx
      have h := act_sq _ (hNl x)
      rw [← map_mul] at h
      rcases h with h | h
      · exact Or.inl (hinj _ hxx 1 S.one_mem (by rw [hone]; exact h))
      · exact Or.inr (hinj _ hxx a haS (by rw [hD' a ha]; exact h))
    ·
      intro x hx y hy
      have hc : x * y * x⁻¹ * y⁻¹ ∈ S :=
        S.mul_mem (S.mul_mem (S.mul_mem hx hy) (S.inv_mem hx)) (S.inv_mem hy)
      have h : act (ι (x * y * x⁻¹ * y⁻¹)) = id ∨ act (ι (x * y * x⁻¹ * y⁻¹)) = cI := by
        simpa only [map_mul, map_inv] using act_comm _ (hNl x) _ (hNl y)
      rcases h with h | h
      · exact Or.inl (hinj _ hc 1 S.one_mem (by rw [hone]; exact h))
      · exact Or.inr (hinj _ hc a haS (by rw [hD' a ha]; exact h))
    ·
      intro x hx y hy hxy
      have hxy' : act (ι (x * y)) = act (ι (y * x)) := by rw [hxy]
      have hf : ∀ z : Fin 4, act (ι x) (act (ι y) z) = act (ι y) (act (ι x) z) := by
        intro z
        have := congrFun hxy' z
        rw [hmul, hmul] at this
        exact this
      rcases act_cdep _ (hNl x) _ (hNl y) hf with h | h | h | h | h | h
      · exact Or.inl (hinj x hx 1 S.one_mem (by rw [hone]; exact h))
      · exact Or.inr (Or.inl (hinj x hx a haS (by rw [hD' a ha]; exact h)))
      · exact Or.inr (Or.inr (Or.inl (hinj y hy 1 S.one_mem (by rw [hone]; exact h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (hinj y hy a haS (by rw [hD' a ha]; exact h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hinj y hy x hx h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (hinj y hy (x * a) (S.mul_mem hx haS) (by rw [hmul, hD' a ha]; exact h))))))
  have hNF : NineFree D := by
    refine ⟨E9sub.comap ι, ⟨fun {n} hn g => ?_⟩, ?_, ?_⟩
    ·
      have hn' : ι n ∈ E9l := Subgroup.mem_comap.1 hn
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact hE g (ι n) hn'
    ·
      have hinjN : Function.Injective (fun n : ↥(E9sub.comap ι) => ι (n : Q)) := by
        intro n m h
        exact Subtype.ext (hι h)
      have hrange : Set.range (fun n : ↥(E9sub.comap ι) => ι (n : Q)) = ↑E9l.toFinset := by
        ext e
        constructor
        · rintro ⟨n, rfl⟩
          rw [List.coe_toFinset]
          exact Subgroup.mem_comap.1 n.2
        · intro he
          obtain ⟨s, hs, t, ht, rfl⟩ := E9_prod e (List.mem_toFinset.1 he)
          obtain ⟨d, hd, rfl⟩ := hS s (mem_nineSet_of_mem_nineL hs)
          obtain ⟨d', hd', rfl⟩ := hS t (mem_nineSet_of_mem_nineL ht)
          have hmem : d * d' ∈ E9sub.comap ι := by
            rw [Subgroup.mem_comap, map_mul]
            exact nineL_prod _ hs _ ht
          exact ⟨⟨d * d', hmem⟩, map_mul ι d d'⟩
      have hcard : E9l.toFinset.card = 9 := by decide +kernel
      rw [← Nat.card_range_of_injective hinjN, hrange, Nat.card_coe_set_eq, Set.ncard_coe_finset,
        hcard]
    ·
      intro n hn hn1 d hd hdn
      have hn' : ι n ∈ E9l := Subgroup.mem_comap.1 hn
      have hn1' : ι n ≠ 1 := fun h => hn1 (hι (by rw [h, map_one]))
      have hcomm : ι n * ι d = ι d * ι n := by
        have := congrArg ι hdn
        rw [map_mul, map_mul, map_inv] at this
        exact mul_inv_eq_iff_eq_mul.1 this
      exact E9_free _ hn' hn1' _ (mem_nineL_of_mem_nineSet (hD d hd)) hcomm
  exact ⟨hNF, hTbar⟩

end CFSG.GF2Type.Aschbacher1976Full.HS.CruxNine

namespace CFSG.GF2Type.Aschbacher1976Full.HS

theorem cruxNine_holds : CruxNineStmt := by
  intro Q _ _ ι hι D hconj hcn
  obtain ⟨σ, hσ1, hσ2⟩ := hcn
  have hσι : Function.Injective ((MulAut.conj σ).toMonoidHom.comp ι) :=
    (MulAut.conj σ).injective.comp hι
  refine CruxNine.main_of_nine ((MulAut.conj σ).toMonoidHom.comp ι) hσι D hconj ?_ ?_
  · intro d hd
    simpa using hσ1 d hd
  · intro s hs
    obtain ⟨d, hd, hds⟩ := hσ2 s hs
    exact ⟨d, hd, by simpa using hds⟩

end CFSG.GF2Type.Aschbacher1976Full.HS

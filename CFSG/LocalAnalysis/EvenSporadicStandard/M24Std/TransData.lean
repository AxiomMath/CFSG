module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransDataS24

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

variable {G : Type} [Group G] {L A : Subgroup G}

@[expose] def sxtIota (e : L ≃* S24) : S24 →* G := L.subtype.comp e.symm.toMonoidHom

theorem sxtIota_injective (e : L ≃* S24) : Function.Injective (sxtIota e) :=
  Subtype.val_injective.comp e.symm.injective

theorem sxtIota_mem (e : L ≃* S24) (s : S24) : sxtIota e s ∈ L := (e.symm s).2

@[simp] theorem sxtIota_apply (e : L ≃* S24) (x : L) : sxtIota e (e x) = x := by
  simp [sxtIota]

theorem sxtIota_conj (e : L ≃* S24) (g t : S24) :
    sxtIota e g * sxtIota e t * (sxtIota e g)⁻¹ = sxtIota e (g * t * g⁻¹) := by
  simp [map_mul, map_inv]

omit [Group G] in
theorem sxt_ncard_image_list {ι : S24 → G} (hι : Function.Injective ι) {l : List S24}
    (hl : l.Nodup) : (ι '' {s | s ∈ l}).ncard = l.length := by
  rw [Set.ncard_image_of_injective _ hι]
  have : {s | s ∈ l} = (l.toFinset : Set S24) := by
    ext s
    simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hl]

theorem mem_sxtFixClass (a s : S24) :
    s ∈ sxtFixClass a ↔ s ∈ m24E1l ∧ s ≠ 1 ∧ sxtFix s = sxtFix a := by
  simp [sxtFixClass]

theorem nodup_sxtFixClass (hnd : m24E1l.Nodup) (a : S24) : (sxtFixClass a).Nodup := by
  unfold sxtFixClass
  exact hnd.filter _

attribute [local irreducible] sxtFixClass m24E1l sxtReachSteps sxtGens sxtA1 sxtA2 sxtR sxtQ sxtW1
  sxtW2

theorem sxtIota_mem_A (e : L ≃* S24) (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l) (s : S24) :
    sxtIota e s ∈ A ↔ s ∈ m24E1l := by
  simpa [sxtIota] using hA (e.symm s)

section Embedding

variable (e : L ≃* S24) (hAL : A ≤ L) (hA : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l)
include hAL hA

theorem sxt_mem_A_iff (y : G) : y ∈ A ↔ ∃ s ∈ m24E1l, sxtIota e s = y := by
  constructor
  · intro hy
    exact ⟨e ⟨y, hAL hy⟩, (hA ⟨y, hAL hy⟩).1 hy, by simp⟩
  · rintro ⟨s, hs, rfl⟩
    exact (sxtIota_mem_A e hA s).2 hs

theorem sxt_coe_A : (A : Set G) = sxtIota e '' {s | s ∈ m24E1l} := by
  ext y
  exact sxt_mem_A_iff e hAL hA y

theorem sxt_mem_egNL_iff (n : G) : n ∈ egNL L A ↔
    ∃ g : S24, (∀ s, s ∈ m24E1l ↔ g * s * g⁻¹ ∈ m24E1l) ∧ sxtIota e g = n := by
  unfold egNL
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hn, hnL⟩
    have hι : sxtIota e (e ⟨n, hnL⟩) = n := by simp
    refine ⟨e ⟨n, hnL⟩, fun s => ?_, hι⟩
    rw [← sxtIota_mem_A e hA, ← sxtIota_mem_A e hA, ← sxtIota_conj, hι]
    exact Subgroup.mem_normalizer_iff.1 hn _
  · rintro ⟨g, hg, rfl⟩
    refine ⟨Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩,
      sxtIota_mem e g⟩
    · obtain ⟨t, ht, rfl⟩ := (sxt_mem_A_iff e hAL hA h).1 hh
      rw [sxtIota_conj, sxtIota_mem_A e hA]
      exact (hg t).1 ht
    · obtain ⟨u, hu, hu'⟩ := (sxt_mem_A_iff e hAL hA _).1 hh
      have : h = sxtIota e (g⁻¹ * u * g) := by
        rw [map_mul, map_mul, map_inv, hu']
        group
      rw [this, sxtIota_mem_A e hA]
      exact (hg _).2 (by simpa [mul_assoc] using hu)

theorem sxt_egOrb_eq {a : S24} {w : List (ℕ × ℕ)} (ha : a ∈ m24E1l) (ha1 : a ≠ 1)
    (hgens : ∀ g ∈ sxtGens, SxtNormChk m24E1l g)
    (hreach : ∀ s ∈ sxtFixClass a, s ∈ sxtReachSteps sxtGens a w) :
    egOrb L A (sxtIota e a) = sxtIota e '' {s | s ∈ sxtFixClass a} := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (sxt_mem_egNL_iff e hAL hA n).1 hn
    refine ⟨g * a * g⁻¹,
      (mem_sxtFixClass a _).2 ⟨(hg a).1 ha, fun h => ha1 ?_, sxtFix_conj g a⟩, ?_⟩
    · simpa using h
    · simp [map_mul, map_inv]
  · rintro ⟨s, hs, rfl⟩
    refine sxt_mem_reachSteps (P := fun t => sxtIota e t ∈ egOrb L A (sxtIota e a)) ?_ ?_ w s
      (hreach s hs)
    · exact ⟨1, (egNL L A).one_mem, by simp⟩
    · rintro g hg' t ⟨n, hn, hnt⟩
      refine ⟨sxtIota e g * n, (egNL L A).mul_mem ?_ hn, ?_⟩
      · exact (sxt_mem_egNL_iff e hAL hA _).2 ⟨g, (hgens g hg').mem_iff, rfl⟩
      · rw [map_mul, map_mul, map_inv, ← hnt]
        group

theorem sxt_elem_of_emb : EgElemAb A := by
  obtain ⟨-, -, -, -, hsq, hcomm, -⟩ := m24_e1_check
  constructor
  · intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := (sxt_mem_A_iff e hAL hA x).1 hx
    obtain ⟨t, ht, rfl⟩ := (sxt_mem_A_iff e hAL hA y).1 hy
    rw [← map_mul, ← map_mul, hcomm s hs t ht]
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := (sxt_mem_A_iff e hAL hA x).1 hx
    rw [← map_mul, hsq s hs, map_one]

theorem sxt_card_of_emb : Nat.card A = 64 := by
  obtain ⟨hlen, hnd, -⟩ := m24_e1_check
  have h1 : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq _
  rw [h1, sxt_coe_A e hAL hA, sxt_ncard_image_list (sxtIota_injective e) hnd, hlen]

omit hAL in
theorem sxt_cent_of_emb :
    ∀ l ∈ L, (∀ a ∈ A, l * a = a * l) → l ∈ A := by
  intro l hl hcomm
  have hs : ∀ x ∈ m24E1l, e ⟨l, hl⟩ * x = x * e ⟨l, hl⟩ := by
    intro x hx
    have := hcomm _ ((sxtIota_mem_A e hA x).2 hx)
    apply e.symm.injective
    apply Subtype.ext
    simpa [sxtIota] using this
  have hlA := (sxtIota_mem_A e hA _).2 (sxt_cent hs)
  simpa using hlA

theorem sxt_orbits_of_emb :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧
      (∀ x ∈ A, x ≠ 1 → x ∈ egOrb L A a₁ ∨ x ∈ egOrb L A a₂) ∧ a₂ ∉ egOrb L A a₁ ∧
      Nat.card (egOrb L A a₁) = 45 ∧ Nat.card (egOrb L A a₂) = 18 := by
  obtain ⟨-, hgens, ⟨h1m, h11, hr1⟩, ⟨h2m, h21, hr2⟩, hl1, hl2, hne, hcover, -⟩ :=
    Certificates.certificate24841
  obtain ⟨-, hnd, -⟩ := m24_e1_check
  have o1 := sxt_egOrb_eq e hAL hA h1m h11 hgens hr1
  have o2 := sxt_egOrb_eq e hAL hA h2m h21 hgens hr2
  have hι := sxtIota_injective e
  refine ⟨sxtIota e sxtA1, (sxtIota_mem_A e hA _).2 h1m, sxtIota e sxtA2,
    (sxtIota_mem_A e hA _).2 h2m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => h11 (hι (h.trans (map_one _).symm))
  · exact fun h => h21 (hι (h.trans (map_one _).symm))
  · intro x hx hx1
    obtain ⟨s, hs, rfl⟩ := (sxt_mem_A_iff e hAL hA x).1 hx
    have hs1 : s ≠ 1 := fun h => hx1 (by rw [h, map_one])
    rcases hcover s hs hs1 with h | h
    · exact Or.inl (by rw [o1]; exact ⟨s, (mem_sxtFixClass _ _).2 ⟨hs, hs1, h⟩, rfl⟩)
    · exact Or.inr (by rw [o2]; exact ⟨s, (mem_sxtFixClass _ _).2 ⟨hs, hs1, h⟩, rfl⟩)
  · rw [o1]
    rintro ⟨s, hs, hs'⟩
    obtain rfl := hι hs'
    exact hne ((mem_sxtFixClass _ _).1 hs).2.2.symm
  · rw [Nat.card_coe_set_eq, o1, sxt_ncard_image_list hι (nodup_sxtFixClass hnd _), hl1]
  · rw [Nat.card_coe_set_eq, o2, sxt_ncard_image_list hι (nodup_sxtFixClass hnd _), hl2]

theorem sxt_five_of_emb :
    ∃ r ∈ egNL L A, orderOf r = 5 ∧ Nat.card {a : A | r * (a : G) * r⁻¹ = a} = 4 ∧
      ∃ Q : Subgroup G, Q ≤ egNL L A ∧ Q ≤ normalizer (zpowers r : Set G) ∧ Nat.card Q = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, hfive⟩ := Certificates.certificate24841
  obtain ⟨hR, hR1, hR5, hcount, hQlen, hQnd, hQ1, hQmul, hQ⟩ := hfive
  obtain ⟨-, hnd, -⟩ := m24_e1_check
  have hι := sxtIota_injective e
  refine ⟨sxtIota e sxtR, (sxt_mem_egNL_iff e hAL hA _).2 ⟨sxtR, hR.mem_iff, rfl⟩, ?_, ?_, ?_⟩
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, hR5, map_one]
    · exact fun h => hR1 (hι (h.trans (map_one _).symm))
  · have hset : Subtype.val '' {a : A | sxtIota e sxtR * (a : G) * (sxtIota e sxtR)⁻¹ = a} =
        sxtIota e '' {s | s ∈ m24E1l.filter fun x => decide (sxtR * x * sxtR⁻¹ = x)} := by
      ext y
      constructor
      · rintro ⟨a, ha, rfl⟩
        obtain ⟨s, hs, hsa⟩ := (sxt_mem_A_iff e hAL hA a).1 a.2
        refine ⟨s, List.mem_filter.2 ⟨hs, decide_eq_true ?_⟩, hsa⟩
        apply hι
        rw [← sxtIota_conj, hsa]
        exact ha
      · rintro ⟨s, hs, rfl⟩
        obtain ⟨hs1, hs2⟩ := List.mem_filter.1 hs
        refine ⟨⟨sxtIota e s, (sxtIota_mem_A e hA s).2 hs1⟩, ?_, rfl⟩
        show sxtIota e sxtR * sxtIota e s * (sxtIota e sxtR)⁻¹ = sxtIota e s
        rw [sxtIota_conj, of_decide_eq_true hs2]
    rw [Nat.card_coe_set_eq, ← Set.ncard_image_of_injective _ Subtype.val_injective, hset,
      sxt_ncard_image_list hι (hnd.filter _), hcount]
  · have hconj : ∀ q ∈ sxtQ, ∀ m : ℤ,
        sxtIota e q * sxtIota e sxtR ^ m * (sxtIota e q)⁻¹ ∈ zpowers (sxtIota e sxtR) := by
      intro q hq m
      have h4 := (hQ q hq).2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h4
      obtain ⟨k, hk⟩ : ∃ k : ℕ, q * sxtR * q⁻¹ = sxtR ^ k := by
        rcases h4 with h | h | h | h
        exacts [⟨1, by rw [pow_one]; exact h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩]
      have hk' := congrArg (sxtIota e) hk
      simp only [map_mul, map_inv, map_pow] at hk'
      rw [← conj_zpow, hk', ← zpow_natCast, ← zpow_mul]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    obtain ⟨R, hR'⟩ := exists_subgroup_of_list sxtQ hQ1 hQmul
    refine ⟨R.map (sxtIota e), ?_, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact (sxt_mem_egNL_iff e hAL hA _).2 ⟨q, ((hQ q ((hR' q).1 hq)).1).mem_iff, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        exact hconj q ((hR' q).1 hq) m
      · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hh
        have h' := hconj q⁻¹ ((hR' q⁻¹).1 (R.inv_mem hq)) m
        rw [map_inv, hm] at h'
        convert h' using 1
        group
    · rw [Subgroup.card_map_of_injective hι, card_eq_length_of_list_subgroup hR' hQnd, hQlen]

theorem sextetFacts_of_emb :
    SextetFacts L A where
  elem := sxt_elem_of_emb e hAL hA
  card_A := sxt_card_of_emb e hAL hA
  cent := sxt_cent_of_emb e hA
  orbits := sxt_orbits_of_emb e hAL hA
  five := sxt_five_of_emb e hAL hA

end Embedding

theorem sextetFacts_of_type
    {L A : Subgroup G}
    (h : SextetType L A) : SextetFacts L A := by
  obtain ⟨hAL, e, hA⟩ := h
  exact sextetFacts_of_emb e hAL hA

end CFSG.EvenSporadicStandard.M24Std

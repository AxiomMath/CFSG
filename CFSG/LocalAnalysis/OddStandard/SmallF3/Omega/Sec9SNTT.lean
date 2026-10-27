module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private def conjFixRel (N : Subgroup G) (c a b : G) : Prop :=
  ∃ n ∈ N, n * c * n⁻¹ = c ∧ n * a * n⁻¹ = b

private theorem inv_conj_eq_self {g c : G} (h : g * c * g⁻¹ = c) : g⁻¹ * c * g = c := by
  have := congrArg (fun z => g⁻¹ * z * g) h
  simpa [mul_assoc] using this.symm

private theorem conjFixRel_symm {N : Subgroup G} {c a b : G}
    (h : conjFixRel N c a b) : conjFixRel N c b a := by
  obtain ⟨n, hn, hnc, hnab⟩ := h
  refine ⟨n⁻¹, N.inv_mem hn, ?_, ?_⟩
  · simpa using inv_conj_eq_self hnc
  · have := congrArg (fun z => n⁻¹ * z * n) hnab
    simpa [mul_assoc] using this.symm

private theorem conjFixRel_trans {N : Subgroup G} {c a b d : G}
    (h1 : conjFixRel N c a b) (h2 : conjFixRel N c b d) : conjFixRel N c a d := by
  obtain ⟨n, hn, hnc, hnab⟩ := h1
  obtain ⟨m, hm, hmc, hmbd⟩ := h2
  refine ⟨m * n, N.mul_mem hm hn, ?_, ?_⟩
  · rw [mul_inv_rev]
    calc m * n * c * (n⁻¹ * m⁻¹) = m * (n * c * n⁻¹) * m⁻¹ := by group
      _ = m * c * m⁻¹ := by rw [hnc]
      _ = c := hmc
  · rw [mul_inv_rev]
    calc m * n * a * (n⁻¹ * m⁻¹) = m * (n * a * n⁻¹) * m⁻¹ := by group
      _ = m * b * m⁻¹ := by rw [hnab]
      _ = d := hmbd

private theorem conj_conj_fix {g n c : G} (hg : g * c * g⁻¹ = c) (hn : n * c * n⁻¹ = c) :
    (g * n * g⁻¹) * c * (g * n * g⁻¹)⁻¹ = c := by
  have h : (g * n * g⁻¹)⁻¹ = g * n⁻¹ * g⁻¹ := by group
  rw [h]
  calc g * n * g⁻¹ * c * (g * n⁻¹ * g⁻¹)
      = g * (n * (g⁻¹ * c * g) * n⁻¹) * g⁻¹ := by group
    _ = g * (n * c * n⁻¹) * g⁻¹ := by rw [inv_conj_eq_self hg]
    _ = g * c * g⁻¹ := by rw [hn]
    _ = c := hg

private theorem conj_conj_mul (g n a : G) :
    (g * n * g⁻¹) * (g * a * g⁻¹) * (g * n * g⁻¹)⁻¹ = g * (n * a * n⁻¹) * g⁻¹ := by
  have h : (g * n * g⁻¹)⁻¹ = g * n⁻¹ * g⁻¹ := by group
  rw [h]
  group

private theorem conj_injective (g : G) : Function.Injective (fun u : G => g * u * g⁻¹) := by
  intro u v h
  have := congrArg (fun z => g⁻¹ * z * g) h
  simpa [mul_assoc] using this

private theorem conjFixRel_mem_sdiff {N P : Subgroup G} {T : Set G} (hNP : N ≤ P)
    (hT : ∀ n ∈ P, ∀ a ∈ T, n * a * n⁻¹ ∈ T) {c a u : G}
    (haT : a ∈ T) (hac : a ≠ c) (h : conjFixRel N c a u) : u ∈ T \ {c} := by
  obtain ⟨n, hn, hnc, hnu⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hnu]
    exact hT n (hNP hn) a haT
  · intro hu
    apply hac
    have hu' : u = c := by simpa using hu
    have h1 : n * a * n⁻¹ = n * c * n⁻¹ := by rw [hnu, hu', hnc]
    have := congrArg (fun z => n⁻¹ * z * n) h1
    simpa [mul_assoc] using this

theorem sec9n_normal_of_index_two {P N : Subgroup G} (hNP : N ≤ P)
    (hidx : ∀ p ∈ P, ∀ q ∈ P, p ∈ N ∨ q ∈ N ∨ p⁻¹ * q ∈ N) :
    ∀ p ∈ P, ∀ n ∈ N, p * n * p⁻¹ ∈ N := by
  intro p hp n hn
  by_cases hpn : p ∈ N
  · exact N.mul_mem (N.mul_mem hpn hn) (N.inv_mem hpn)
  · have hpinvN : p⁻¹ ∉ N := by
      intro h
      exact hpn (by simpa using N.inv_mem h)
    have hqP : n * p⁻¹ ∈ P := P.mul_mem (hNP hn) (P.inv_mem hp)
    have hqN : n * p⁻¹ ∉ N := by
      intro hq
      apply hpinvN
      have := N.mul_mem (N.inv_mem hn) hq
      rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
    rcases hidx p⁻¹ (P.inv_mem hp) (n * p⁻¹) hqP with h | h | h
    · exact absurd h hpinvN
    · exact absurd h hqN
    · simpa [mul_assoc] using h

theorem sec9n_stab_trans {P N : Subgroup G} {T : Set G} (hNP : N ≤ P)
    (hidx : ∀ p ∈ P, ∀ q ∈ P, p ∈ N ∨ q ∈ N ∨ p⁻¹ * q ∈ N) (hT : T.ncard = 16)
    (hP : ConjTwoTransOn P T) {c x y : G} (hc : c ∈ T) (hx : x ∈ T) (hy : y ∈ T)
    (hxc : x ≠ c) (hyc : y ≠ c) : ∃ n ∈ N, n * c * n⁻¹ = c ∧ n * x * n⁻¹ = y := by
  have hTclosed : ∀ n ∈ P, ∀ a ∈ T, n * a * n⁻¹ ∈ T := hP.1
  by_cases hcaseA : ∀ p ∈ P, p * c * p⁻¹ = c → p ∈ N
  · obtain ⟨p, hpP, hpc, hpxy⟩ := hP.2 c hc x hx c hc y hy hxc.symm hyc.symm
    exact ⟨p, hcaseA p hpP hpc, hpc, hpxy⟩
  · push_neg at hcaseA
    obtain ⟨p₀, hp₀P, hp₀c, hp₀N⟩ := hcaseA
    have hnorm := sec9n_normal_of_index_two hNP hidx
    have hp₀invP : p₀⁻¹ ∈ P := P.inv_mem hp₀P
    have claim1 : ∀ u ∈ T \ {c},
        conjFixRel N c x u ∨ conjFixRel N c (p₀ * x * p₀⁻¹) u := by
      intro u hu
      have huT : u ∈ T := hu.1
      have huc : u ≠ c := by simpa using hu.2
      obtain ⟨p, hpP, hpc, hpxu⟩ := hP.2 c hc x hx c hc u huT hxc.symm huc.symm
      by_cases hpN : p ∈ N
      · exact Or.inl ⟨p, hpN, hpc, hpxu⟩
      · have hn₁N : p₀⁻¹ * p ∈ N := by
          rcases hidx p₀ hp₀P p hpP with h | h | h
          · exact absurd h hp₀N
          · exact absurd h hpN
          · exact h
        have hn₁c : (p₀⁻¹ * p) * c * (p₀⁻¹ * p)⁻¹ = c := by
          have hpc' := inv_conj_eq_self hp₀c
          calc (p₀⁻¹ * p) * c * (p₀⁻¹ * p)⁻¹
              = p₀⁻¹ * (p * c * p⁻¹) * p₀ := by group
            _ = p₀⁻¹ * c * p₀ := by rw [hpc]
            _ = c := hpc'
        refine Or.inr ⟨p₀ * (p₀⁻¹ * p) * p₀⁻¹,
          hnorm p₀ hp₀P (p₀⁻¹ * p) hn₁N, ?_, ?_⟩
        · exact conj_conj_fix hp₀c hn₁c
        · have hp : p₀ * (p₀⁻¹ * p) = p := by group
          calc (p₀ * (p₀⁻¹ * p) * p₀⁻¹) * (p₀ * x * p₀⁻¹)
                * (p₀ * (p₀⁻¹ * p) * p₀⁻¹)⁻¹
              = p₀ * ((p₀⁻¹ * p) * x * (p₀⁻¹ * p)⁻¹) * p₀⁻¹ := conj_conj_mul ..
            _ = (p₀ * (p₀⁻¹ * p)) * x * (p₀ * (p₀⁻¹ * p))⁻¹ := by group
            _ = p * x * p⁻¹ := by rw [hp]
            _ = u := hpxu
    have hTfin : T.Finite := Set.finite_of_ncard_ne_zero (by rw [hT]; norm_num)
    have claim2 : conjFixRel N c x (p₀ * x * p₀⁻¹) := by
      by_contra hnot
      set X : Set G := {u | conjFixRel N c x u} with hX
      set Y : Set G := {u | conjFixRel N c (p₀ * x * p₀⁻¹) u} with hY
      have hXsub : X ⊆ T \ {c} := fun u hu => conjFixRel_mem_sdiff hNP hTclosed hx hxc hu
      have hd'T : p₀ * x * p₀⁻¹ ∈ T := hTclosed p₀ hp₀P x hx
      have hd'c : p₀ * x * p₀⁻¹ ≠ c := by
        intro h
        apply hxc
        have h1 : p₀ * x * p₀⁻¹ = p₀ * c * p₀⁻¹ := by rw [h, hp₀c]
        have := congrArg (fun z => p₀⁻¹ * z * p₀) h1
        simpa [mul_assoc] using this
      have hYsub : Y ⊆ T \ {c} := fun u hu => conjFixRel_mem_sdiff hNP hTclosed hd'T hd'c hu
      have hunion : X ∪ Y = T \ {c} := by
        ext u
        constructor
        · rintro (hu | hu)
          · exact hXsub hu
          · exact hYsub hu
        · intro hu
          rcases claim1 u hu with h | h
          · exact Or.inl h
          · exact Or.inr h
      have hinter : X ∩ Y = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro u hu
        exact hnot (conjFixRel_trans hu.1 (conjFixRel_symm hu.2))
      have himage : Y = (fun u => p₀ * u * p₀⁻¹) '' X := by
        apply Set.Subset.antisymm
        · intro v hv
          obtain ⟨n, hn, hnc, hnv⟩ := hv
          refine ⟨p₀⁻¹ * v * p₀, ?_, ?_⟩
          · refine ⟨p₀⁻¹ * n * p₀, by simpa using hnorm p₀⁻¹ hp₀invP n hn, ?_, ?_⟩
            · simpa using conj_conj_fix (g := p₀⁻¹) (n := n)
                (by simpa using inv_conj_eq_self hp₀c) hnc
            · calc (p₀⁻¹ * n * p₀) * x * (p₀⁻¹ * n * p₀)⁻¹
                  = (p₀⁻¹ * n * p₀) * (p₀⁻¹ * (p₀ * x * p₀⁻¹) * p₀)
                      * (p₀⁻¹ * n * p₀)⁻¹ := by group
                _ = p₀⁻¹ * (n * (p₀ * x * p₀⁻¹) * n⁻¹) * p₀ := by
                    simpa using conj_conj_mul p₀⁻¹ n (p₀ * x * p₀⁻¹)
                _ = p₀⁻¹ * v * p₀ := by rw [hnv]
          · group
        · rintro v ⟨u, hu, rfl⟩
          obtain ⟨n, hn, hnc, hnu⟩ := hu
          refine ⟨p₀ * n * p₀⁻¹, hnorm p₀ hp₀P n hn, ?_, ?_⟩
          · exact conj_conj_fix hp₀c hnc
          · calc (p₀ * n * p₀⁻¹) * (p₀ * x * p₀⁻¹) * (p₀ * n * p₀⁻¹)⁻¹
                = p₀ * (n * x * n⁻¹) * p₀⁻¹ := conj_conj_mul ..
              _ = p₀ * u * p₀⁻¹ := by rw [hnu]
      have hXfin : X.Finite := hTfin.subset (hXsub.trans Set.sdiff_subset)
      have hYfin : Y.Finite := hTfin.subset (hYsub.trans Set.sdiff_subset)
      have hdisj : Disjoint X Y := Set.disjoint_iff_inter_eq_empty.mpr hinter
      have hYcard : Y.ncard = X.ncard := by
        rw [himage, Set.ncard_image_of_injective X (conj_injective p₀)]
      have hcard : (T \ {c}).ncard = 2 * X.ncard := by
        calc (T \ {c}).ncard = (X ∪ Y).ncard := by rw [hunion]
          _ = X.ncard + Y.ncard := Set.ncard_union_eq hdisj hXfin hYfin
          _ = X.ncard + X.ncard := by rw [hYcard]
          _ = 2 * X.ncard := by ring
      have hScard : (T \ {c}).ncard = 15 := by
        simp [Set.ncard_sdiff_singleton_of_mem hc, hT]
      omega
    rcases claim1 y ⟨hy, by simpa using hyc⟩ with h | h
    · exact h
    · exact conjFixRel_trans claim2 h

theorem sec9n_conjTwoTransOn_of_index_two {P N : Subgroup G} {T : Set G} (hNP : N ≤ P)
    (hidx : ∀ p ∈ P, ∀ q ∈ P, p ∈ N ∨ q ∈ N ∨ p⁻¹ * q ∈ N) (hT : T.ncard = 16)
    (hP : ConjTwoTransOn P T) : ConjTwoTransOn N T := by
  have hTclosed : ∀ n ∈ P, ∀ a ∈ T, n * a * n⁻¹ ∈ T := hP.1
  have htrans : ∀ a ∈ T, ∀ c ∈ T, ∃ n ∈ N, n * a * n⁻¹ = c := by
    intro a ha c hc
    by_cases hac : a = c
    · exact ⟨1, N.one_mem, by rw [hac]; simp⟩
    · have hsub : ((T \ {a}) \ {c}).Nonempty := by
        have h1 : (T \ {a}).ncard = 15 := by
          simp [Set.ncard_sdiff_singleton_of_mem ha, hT]
        have hc_in : c ∈ T \ {a} := by
          refine ⟨hc, ?_⟩
          intro h
          have h' : c = a := by simpa using h
          exact hac h'.symm
        have h2 : ((T \ {a}) \ {c}).ncard = (T \ {a}).ncard - 1 :=
          Set.ncard_sdiff_singleton_of_mem hc_in
        exact Set.nonempty_of_ncard_ne_zero (by rw [h2, h1]; norm_num)
      obtain ⟨e, he⟩ := hsub
      have heT : e ∈ T := he.1.1
      have hne_a : e ≠ a := by simpa using he.1.2
      have hne_c : e ≠ c := by simpa using he.2
      obtain ⟨n, hn, _, hnac⟩ :=
        sec9n_stab_trans hNP hidx hT hP heT ha hc hne_a.symm hne_c.symm
      exact ⟨n, hn, hnac⟩
  refine ⟨?_, ?_⟩
  · intro n hn a ha
    exact hTclosed n (hNP hn) a ha
  · intro a ha b hb c hc d hd hab hcd
    obtain ⟨n₁, hn₁, hn₁a⟩ := htrans a ha c hc
    have hb'T : n₁ * b * n₁⁻¹ ∈ T := hTclosed n₁ (hNP hn₁) b hb
    have hb'c : n₁ * b * n₁⁻¹ ≠ c := by
      intro h
      apply hab
      have h1 : n₁ * b * n₁⁻¹ = n₁ * a * n₁⁻¹ := by rw [h, hn₁a]
      have := congrArg (fun z => n₁⁻¹ * z * n₁) h1
      simpa [mul_assoc] using this.symm
    obtain ⟨n₂, hn₂, hn₂c, hn₂b⟩ :=
      sec9n_stab_trans hNP hidx hT hP hc hb'T hd hb'c hcd.symm
    refine ⟨n₂ * n₁, N.mul_mem hn₂ hn₁, ?_, ?_⟩
    · rw [mul_inv_rev]
      calc n₂ * n₁ * a * (n₁⁻¹ * n₂⁻¹) = n₂ * (n₁ * a * n₁⁻¹) * n₂⁻¹ := by group
        _ = n₂ * c * n₂⁻¹ := by rw [hn₁a]
        _ = c := hn₂c
    · rw [mul_inv_rev]
      calc n₂ * n₁ * b * (n₁⁻¹ * n₂⁻¹) = n₂ * (n₁ * b * n₁⁻¹) * n₂⁻¹ := by group
        _ = d := hn₂b

end CFSG.OddStandard.SmallF3.Omega

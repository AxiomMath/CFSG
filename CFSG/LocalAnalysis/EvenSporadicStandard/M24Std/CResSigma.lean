module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideOdd

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem exists_sigma_centralizer (h : Setup L A C z) (σ : egNL L A →* Equiv.Perm (Fin 6))
    (hσ : Function.Surjective σ) (hA : A.subgroupOf (egNL L A) ≤ σ.ker)
    (hk : Nat.card σ.ker = 192) :
    ∃ σ' : ↥(centralizer ({zt h} : Set (egQD C))) →* Equiv.Perm (Fin 6),
      Nat.card σ'.ker = 6 ∧ Nat.card (centralizer ({zt h} : Set (egQD C))) = 4320 ∧
      ∀ (n : egNL L A) (e : ℕ) (y : ↥(centralizer ({zt h} : Set (egQD C)))),
        (y : egQD C) = psi h n * zt h ^ e → σ' y = σ n := by
  set T : Subgroup (egQD C) := zpowers (zt h) with hT
  have hcomm : ∀ (n : egNL L A) (t : T), Commute (psi h n) (T.subtype t) := by
    intro n t
    obtain ⟨k, hk'⟩ := t.2
    have : (T.subtype t) = zt h ^ k := hk'.symm
    rw [this]
    have hc : Commute (psi h n) (zt h) := psi_comm h n
    exact hc.zpow_right k
  let Ψ' : egNL L A × T →* egQD C := (psi h).noncommCoprod T.subtype hcomm
  have hΨ'mem : ∀ x, Ψ' x ∈ centralizer ({zt h} : Set (egQD C)) := by
    intro x
    rw [centralizer_quot_eq h]
    exact mul_mem (mem_sup_left ⟨x.1, rfl⟩) (mem_sup_right x.2.2)
  let Ψ : egNL L A × T →* ↥(centralizer ({zt h} : Set (egQD C))) := Ψ'.codRestrict _ hΨ'mem
  have hΨ_apply : ∀ n t, (Ψ (n, t) : egQD C) = psi h n * (t : egQD C) := fun n t => rfl
  have hΨsurj : Function.Surjective Ψ := by
    intro p
    have hp : (p : egQD C) ∈ (psi h).range ⊔ zpowers (zt h) := by
      rw [← centralizer_quot_eq h]
      exact p.2
    have hle : zpowers (zt h) ≤ centralizer ((psi h).range : Set (egQD C)) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun y hy => by
        obtain ⟨n, rfl⟩ := hy
        exact psi_comm h n
    obtain ⟨a, ⟨n, rfl⟩, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hp
    exact ⟨(n, ⟨b, hb⟩), Subtype.ext (by rw [hΨ_apply]; exact hab.symm)⟩
  have hztzt : zt h * zt h = 1 := by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.1 (orderOf_zt h).dvd
  have hkerΨ : ∀ n t, Ψ (n, t) = 1 → t = 1 ∧ n ∈ A.subgroupOf (egNL L A) := by
    intro n t hnt
    have h1 : psi h n * (t : egQD C) = 1 := congrArg Subtype.val hnt
    have hn : psi h n = (t : egQD C)⁻¹ := eq_inv_of_mul_eq_one_left h1
    rcases mem_zpowers_zt h t.2 with h0 | h0
    · have ht1 : t = 1 := Subtype.ext h0
      refine ⟨ht1, ?_⟩
      rw [← ker_psi h, MonoidHom.mem_ker, hn, h0, inv_one]
    · exfalso
      apply zt_not_mem_range h
      refine ⟨n, ?_⟩
      rw [hn, h0]
      exact inv_eq_of_mul_eq_one_right hztzt
  have hAle : A ≤ egNL L A := fun a ha => mem_inf.2 ⟨le_normalizer ha, h.hAL ha⟩
  have hkerΨcard : Nat.card Ψ.ker = 64 := by
    have e : Ψ.ker ≃ A.subgroupOf (egNL L A) :=
      { toFun := fun x => ⟨x.1.1, (hkerΨ x.1.1 x.1.2 x.2).2⟩
        invFun := fun a => ⟨(a.1, 1), by
          have hψ : psi h a.1 = 1 := by
            rw [← MonoidHom.mem_ker, ker_psi h]
            exact a.2
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (by rw [hΨ_apply]; simp [hψ])⟩
        left_inv := fun x => by
          obtain ⟨⟨n, t⟩, hx⟩ := x
          have := (hkerΨ n t hx).1
          subst this
          rfl
        right_inv := fun a => rfl }
    rw [Nat.card_congr e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv]
    exact h.hF.card_A
  have hTcard : Nat.card T = 2 := by rw [hT, Nat.card_zpowers, orderOf_zt h]
  let φ1 : egNL L A × T →* Equiv.Perm (Fin 6) := σ.comp (MonoidHom.fst _ _)
  have hker : Ψ.ker ≤ φ1.ker := by
    intro x hx
    obtain ⟨n, t⟩ := x
    obtain ⟨-, hn⟩ := hkerΨ n t hx
    rw [MonoidHom.mem_ker]
    simpa [φ1] using hA hn
  let σ' : ↥(centralizer ({zt h} : Set (egQD C))) →* Equiv.Perm (Fin 6) :=
    Ψ.liftOfSurjective hΨsurj ⟨φ1, hker⟩
  have hσ'Ψ : ∀ x, σ' (Ψ x) = φ1 x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ1, hker⟩ x
  have hσ's : Function.Surjective σ' := by
    intro y
    obtain ⟨n, hn⟩ := hσ y
    exact ⟨Ψ (n, 1), by rw [hσ'Ψ]; simpa [φ1] using hn⟩
  have hcards : Nat.card σ'.ker = 6 ∧ Nat.card (centralizer ({zt h} : Set (egQD C))) = 4320 := by
    have c1 := natCard_eq_of_surjective σ hσ
    have c2 := natCard_eq_of_surjective Ψ hΨsurj
    have c3 := natCard_eq_of_surjective σ' hσ's
    rw [Nat.card_prod, hTcard, c1, hk, hkerΨcard] at c2
    have h6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    rw [h6] at c2 c3
    omega
  refine ⟨σ', hcards.1, hcards.2, ?_⟩
  · intro n e y hy
    have : y = Ψ (n, ⟨zt h ^ e, Subgroup.pow_mem _ (mem_zpowers _) e⟩) :=
      Subtype.ext (by rw [hy, hΨ_apply])
    rw [this, hσ'Ψ]
    rfl

end CSide

end CFSG.EvenSporadicStandard.M24Std

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CSideBasic

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open

theorem perm6_normal_odd (N : Subgroup (Equiv.Perm (Fin 6))) (hNn : N.Normal)
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hnorm : (N.subgroupOf (alternatingGroup (Fin 6))).Normal := hNn.subgroupOf _
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 6))) with
    hbot | htop
  · have key : ∀ x ∈ N, x ∈ alternatingGroup (Fin 6) → x = 1 := by
      intro x hxN hxA
      have : (⟨x, hxA⟩ : alternatingGroup (Fin 6)) ∈ N.subgroupOf (alternatingGroup (Fin 6)) :=
        mem_subgroupOf.2 hxN
      rw [hbot] at this
      exact congrArg Subtype.val (Subgroup.mem_bot.1 this)
    have hinj : Function.Injective (Equiv.Perm.sign.comp N.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx' : Equiv.Perm.sign (x : Equiv.Perm (Fin 6)) = 1 := hx
      have hxA : (x : Equiv.Perm (Fin 6)) ∈ alternatingGroup (Fin 6) :=
        MonoidHom.mem_ker.2 hx'
      exact Subgroup.mem_bot.2 (Subtype.ext (key x x.2 hxA))
    have hle : Nat.card N ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ hinj
    have h2 : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_units_int
    have h0 : 0 < Nat.card N := Nat.card_pos
    have hodd : Nat.card N = 1 := by
      obtain ⟨k, hk⟩ := hN
      omega
    exact Subgroup.eq_bot_of_card_eq N hodd
  · exfalso
    have hle : alternatingGroup (Fin 6) ≤ N := by
      intro x hx
      have : (⟨x, hx⟩ : alternatingGroup (Fin 6)) ∈ N.subgroupOf (alternatingGroup (Fin 6)) := by
        rw [htop]
        trivial
      exact this
    have hdvd := Subgroup.card_dvd_of_le hle
    have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [hcard] at hdvd
    have h2 : 2 ∣ Nat.card N := Nat.dvd_trans (by norm_num) hdvd
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h2)

theorem z2s6_normal_odd (N : Subgroup (Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)))
    (hNn : N.Normal) (hN : Odd (Nat.card N)) : N = ⊥ := by
  have hsurj : Function.Surjective (MonoidHom.snd (Multiplicative (ZMod 2))
      (Equiv.Perm (Fin 6))) := fun y => ⟨(1, y), rfl⟩
  have h1 : N.map (MonoidHom.snd _ _) = ⊥ :=
    perm6_normal_odd _ (hNn.map _ hsurj) (Odd.of_dvd_nat hN (Subgroup.card_map_dvd N _))
  rw [eq_bot_iff]
  intro x hx
  have hx2 : x.2 = 1 := by
    have : x.2 ∈ N.map (MonoidHom.snd _ _) := ⟨x, hx, rfl⟩
    rw [h1] at this
    exact Subgroup.mem_bot.1 this
  have hsq : x * x = 1 := by
    refine Prod.ext ?_ (by simp [hx2])
    show x.1 * x.1 = 1
    have : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide
    exact this _
  have hord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq)
  have hord' : orderOf x ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have h2 : orderOf x = 1 ∨ orderOf x = 2 := (Nat.dvd_prime Nat.prime_two).1 hord
  rcases h2 with h2 | h2
  · exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h2)
  · exfalso
    rw [h2] at hord'
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 hord')

theorem fusionOddCore_eq_ker {P Q : Type*} [Group P] [Group Q] (φ : P →* Q)
    (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker))
    (hQ : ∀ N : Subgroup Q, N.Normal → Odd (Nat.card N) → N = ⊥) :
    fusionOddCore P = φ.ker := by
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNn, hNo⟩ := hN
    have h1 : N.map φ = ⊥ :=
      hQ _ (hNn.map φ hφ) (Odd.of_dvd_nat hNo (Subgroup.card_map_dvd N φ))
    intro x hx
    have : φ x ∈ N.map φ := Subgroup.mem_map_of_mem φ hx
    rw [h1, Subgroup.mem_bot] at this
    exact this
  · exact le_sSup ⟨inferInstance, hodd⟩

theorem natCard_eq_of_surjective {M N : Type*} [Group M] [Group N] (f : M →* N)
    (hf : Function.Surjective f) : Nat.card M = Nat.card N * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]

namespace CSide

variable {G : Type} [Group G] [Finite G] {L A C : Subgroup G} {z : G}

theorem mem_zpowers_zt (h : Setup L A C z) {t : egQD C} (ht : t ∈ zpowers (zt h)) :
    t = 1 ∨ t = zt h := by
  obtain ⟨k, rfl⟩ := ht
  have h2 := orderOf_zt h
  have hk := zpow_mod_orderOf (zt h) k
  rw [h2] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    show zt h ^ k = 1
    rw [← hk]
    have : (k % ((2 : ℕ) : ℤ)) = 0 := by exact_mod_cast h0
    rw [this, zpow_zero]
  · right
    show zt h ^ k = zt h
    rw [← hk]
    have : (k % ((2 : ℕ) : ℤ)) = 1 := by exact_mod_cast h1
    rw [this, zpow_one]

theorem exists_hom_centralizer (h : Setup L A C z) (σ : egNL L A →* Equiv.Perm (Fin 6))
    (hσ : Function.Surjective σ) (hA : A.subgroupOf (egNL L A) ≤ σ.ker)
    (hk : Nat.card σ.ker = 192) :
    ∃ φ : ↥(centralizer ({zt h} : Set (egQD C))) →*
        Multiplicative (ZMod 2) × Equiv.Perm (Fin 6),
      Function.Surjective φ ∧ Odd (Nat.card φ.ker) := by
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
  let Ψ : egNL L A × T →* ↥(centralizer ({zt h} : Set (egQD C))) :=
    Ψ'.codRestrict _ hΨ'mem
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
  have hZ2card : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact ZMod.card 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ε : T ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq (p := 2) hTcard hZ2card
  let φ0 : egNL L A × T →* Multiplicative (ZMod 2) × Equiv.Perm (Fin 6) :=
    ((ε : T →* Multiplicative (ZMod 2)).comp (MonoidHom.snd _ _)).prod
      (σ.comp (MonoidHom.fst _ _))
  have hker : Ψ.ker ≤ φ0.ker := by
    intro x hx
    obtain ⟨n, t⟩ := x
    obtain ⟨ht1, hn⟩ := hkerΨ n t hx
    rw [MonoidHom.mem_ker]
    subst ht1
    exact Prod.ext (by simp [φ0]) (by simpa [φ0] using hA hn)
  let φ : ↥(centralizer ({zt h} : Set (egQD C))) →*
      Multiplicative (ZMod 2) × Equiv.Perm (Fin 6) := Ψ.liftOfSurjective hΨsurj ⟨φ0, hker⟩
  have hφΨ : ∀ x, φ (Ψ x) = φ0 x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨φ0, hker⟩ x
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, hn⟩ := hσ y.2
    obtain ⟨t, ht⟩ := ε.surjective y.1
    refine ⟨Ψ (n, t), ?_⟩
    rw [hφΨ]
    exact Prod.ext (by simpa [φ0] using ht) (by simpa [φ0] using hn)
  refine ⟨φ, hφsurj, ?_⟩
  have c1 := natCard_eq_of_surjective σ hσ
  have c2 := natCard_eq_of_surjective Ψ hΨsurj
  have c3 := natCard_eq_of_surjective φ hφsurj
  rw [Nat.card_prod, hTcard, c1, hk, hkerΨcard] at c2
  rw [Nat.card_prod, hZ2card] at c3
  have h6 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [h6] at c2 c3
  have : Nat.card φ.ker = 3 := by omega
  rw [this]
  exact ⟨1, rfl⟩

theorem centralizer_oddCore_equiv (h : Setup L A C z) (σ : egNL L A →* Equiv.Perm (Fin 6))
    (hσ : Function.Surjective σ) (hA : A.subgroupOf (egNL L A) ≤ σ.ker)
    (hk : Nat.card σ.ker = 192) :
    Nonempty (↥(centralizer ({zt h} : Set (egQD C))) ⧸
      fusionOddCore ↥(centralizer ({zt h} : Set (egQD C))) ≃*
        Multiplicative (ZMod 2) × Equiv.Perm (Fin 6)) := by
  obtain ⟨φ, hφ, hodd⟩ := exists_hom_centralizer h σ hσ hA hk
  have hcore := fusionOddCore_eq_ker φ hφ hodd fun N hN hNo => z2s6_normal_odd N hN hNo
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end CSide

end CFSG.EvenSporadicStandard.M24Std

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.CtxCommute
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def oddOrderGrp (K : Subgroup G) : Subgroup G :=
  closure {k : G | k ∈ K ∧ ¬ 2 ∣ orderOf k}

theorem oddOrderGrp_le (K : Subgroup G) : oddOrderGrp K ≤ K :=
  (Subgroup.closure_le K).mpr fun _ hk => hk.1

private def c4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

private def d4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

private def allPerms : List (Equiv.Perm (Fin 4)) := permsOfList [0, 1, 2, 3]

private lemma mem_allPerms (p : Equiv.Perm (Fin 4)) : p ∈ allPerms := by
  rw [allPerms, mem_permsOfList_iff]
  intro x _
  fin_cases x <;> simp

private def ws : Finset (Equiv.Perm (Fin 4)) :=
  {1, c4, d4, c4⁻¹, d4 * c4, c4 * d4, c4⁻¹ * d4, d4 * c4⁻¹,
    c4 * (d4 * c4), c4⁻¹ * (d4 * c4), d4 * (c4 * d4), c4 * (d4 * c4⁻¹)}

private def A4sub : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := ↑ws
  one_mem' := by decide
  mul_mem' := by decide
  inv_mem' := by decide

private lemma A4sub_eq_alternating : A4sub = alternatingGroup (Fin 4) := by
  have hcard_alt : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
  have hcard_A4 : Nat.card A4sub = 12 := by
    rw [show Nat.card A4sub = (ws : Set (Equiv.Perm (Fin 4))).ncard from rfl]
    rw [Set.ncard_eq_toFinset_card', Finset.toFinset_coe]; decide
  apply Subgroup.eq_of_le_of_card_ge
  · intro x hx
    rw [Equiv.Perm.mem_alternatingGroup]
    exact (by decide : ∀ y ∈ ws, Equiv.Perm.sign y = 1) x hx
  · rw [hcard_alt, hcard_A4]

private lemma closure_gen_eq_A4sub :
    closure ({c4, d4} : Set (Equiv.Perm (Fin 4))) = A4sub := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact (by decide : c4 ∈ ws)
      · exact (by decide : d4 ∈ ws))
  · intro x hx
    have hc : c4 ∈ closure ({c4, d4} : Set (Equiv.Perm (Fin 4))) :=
      Subgroup.subset_closure (by simp)
    have hd : d4 ∈ closure ({c4, d4} : Set (Equiv.Perm (Fin 4))) :=
      Subgroup.subset_closure (by simp)
    change x ∈ ws at hx
    simp only [ws, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hc
    · exact hd
    · exact Subgroup.inv_mem _ hc
    · exact Subgroup.mul_mem _ hd hc
    · exact Subgroup.mul_mem _ hc hd
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hd
    · exact Subgroup.mul_mem _ hd (Subgroup.inv_mem _ hc)
    · exact Subgroup.mul_mem _ hc (Subgroup.mul_mem _ hd hc)
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) (Subgroup.mul_mem _ hd hc)
    · exact Subgroup.mul_mem _ hd (Subgroup.mul_mem _ hc hd)
    · exact Subgroup.mul_mem _ hc (Subgroup.mul_mem _ hd (Subgroup.inv_mem _ hc))

private lemma closure_gen_eq_alternating :
    closure ({c4, d4} : Set (Equiv.Perm (Fin 4))) = alternatingGroup (Fin 4) := by
  rw [closure_gen_eq_A4sub, A4sub_eq_alternating]

private lemma simple_transitive :
    ∀ u ∈ allPerms, ∀ v ∈ allPerms, Equiv.Perm.sign u = 1 → Equiv.Perm.sign v = 1 →
      u ^ 3 = 1 → u ≠ 1 → v ^ 2 = 1 → v ≠ 1 →
      ∃ s ∈ allPerms, s * c4 * s⁻¹ = u ∧ s * d4 * s⁻¹ = v := by
  decide

private lemma mem_alternatingGroup_of_odd_orderOf {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Equiv.Perm α} (h : ¬ 2 ∣ orderOf σ) : σ ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h2 : orderOf (Equiv.Perm.sign σ) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact Int.units_sq _
  have hdvd : orderOf (Equiv.Perm.sign σ) ∣ orderOf σ := orderOf_map_dvd _ _
  have hodd : ¬ 2 ∣ orderOf (Equiv.Perm.sign σ) := fun hd => h (hd.trans hdvd)
  have h1 : orderOf (Equiv.Perm.sign σ) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with hh | hh
    · exact hh
    · rw [hh] at hodd
      exact absurd (dvd_refl 2) hodd
  rwa [orderOf_eq_one_iff] at h1

private lemma closure_odd_eq_alternating_fin4 :
    closure {p : Equiv.Perm (Fin 4) | ¬ 2 ∣ orderOf p} = alternatingGroup (Fin 4) := by
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr fun p hp => mem_alternatingGroup_of_odd_orderOf hp
  · rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    apply Subgroup.closure_mono
    intro p hp
    rw [Set.mem_setOf_eq, hp.orderOf]
    decide

private lemma nat_card_alternatingGroup_fin4 : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private def phiHom {Sig : Subgroup G} (φ : ↥Sig ≃* Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin 4) →* G :=
  Sig.subtype.comp φ.symm.toMonoidHom

private lemma phiHom_apply {Sig : Subgroup G} (φ : ↥Sig ≃* Equiv.Perm (Fin 4))
    (p : Equiv.Perm (Fin 4)) : phiHom φ p = ((φ.symm p : ↥Sig) : G) := rfl

private lemma phiHom_injective {Sig : Subgroup G} (φ : ↥Sig ≃* Equiv.Perm (Fin 4)) :
    Function.Injective (phiHom φ) := by
  intro a b h
  exact φ.symm.injective (Subtype.ext h)

private lemma oddOrderGrp_eq_map {Sig : Subgroup G} (φ : ↥Sig ≃* Equiv.Perm (Fin 4)) :
    oddOrderGrp Sig = (alternatingGroup (Fin 4)).map (phiHom φ) := by
  have hgen : {k : G | k ∈ Sig ∧ ¬ 2 ∣ orderOf k}
      = phiHom φ '' {p : Equiv.Perm (Fin 4) | ¬ 2 ∣ orderOf p} := by
    ext k; constructor
    · rintro ⟨hk, hodd⟩
      refine ⟨φ ⟨k, hk⟩, ?_, ?_⟩
      · have : orderOf (φ ⟨k, hk⟩) = orderOf k := by
          rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
        change ¬ 2 ∣ orderOf (φ ⟨k, hk⟩)
        rwa [this]
      · simp [phiHom]
    · rintro ⟨p, hp, rfl⟩
      refine ⟨?_, ?_⟩
      · exact (φ.symm p).2
      · have : orderOf (phiHom φ p) = orderOf p := by
          rw [phiHom_apply, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
        rwa [this]
  rw [oddOrderGrp, hgen, ← MonoidHom.map_closure, closure_odd_eq_alternating_fin4]

theorem card_oddOrderGrp {Sig : Subgroup G} (φ : ↥Sig ≃* Equiv.Perm (Fin 4)) :
    Nat.card (oddOrderGrp Sig) = 12 := by
  rw [oddOrderGrp_eq_map, Subgroup.card_map_of_injective (phiHom_injective φ),
    nat_card_alternatingGroup_fin4]

theorem eq_oddOrderGrp_of_card {Sig A : Subgroup G} (φ : ↥Sig ≃* Equiv.Perm (Fin 4))
    (hAS : A ≤ Sig) (hA : Nat.card A = 12) : A = oddOrderGrp Sig := by
  let A' : Subgroup ↥Sig := A.subgroupOf Sig
  have hcardSig : Nat.card ↥Sig = 24 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hcardA' : Nat.card A' = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAS).toEquiv, hA]
  have hindex : A'.index = 2 := by
    have h := Subgroup.index_mul_card (H := A')
    rw [hcardA', hcardSig] at h
    omega
  apply (Subgroup.eq_of_le_of_card_ge (H := oddOrderGrp Sig) (K := A) ?_ ?_).symm
  · refine (Subgroup.closure_le A).mpr ?_
    rintro k ⟨hk, hodd⟩
    have hk' : (⟨k, hk⟩ : ↥Sig) ∈ A' := by
      have hodd' : ¬ 2 ∣ orderOf (⟨k, hk⟩ : ↥Sig) := by rwa [Subgroup.orderOf_mk]
      have hk2 : (⟨k, hk⟩ : ↥Sig) ^ 2 ∈ A' := Subgroup.sq_mem_of_index_two hindex _
      obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp fun hE => hodd' (even_iff_two_dvd.mp hE)
      have hpow : (⟨k, hk⟩ : ↥Sig) ^ (2 * m + 1) = 1 := by
        rw [← hm]; exact pow_orderOf_eq_one _
      have h2 : (⟨k, hk⟩ : ↥Sig) ^ (2 * m) = (⟨k, hk⟩ : ↥Sig)⁻¹ := by
        have hh := hpow
        rw [pow_succ] at hh
        exact eq_inv_of_mul_eq_one_left hh
      have hkey : ((⟨k, hk⟩ : ↥Sig) ^ 2) ^ (-(m : ℤ)) = (⟨k, hk⟩ : ↥Sig) := by
        rw [zpow_neg, zpow_natCast, ← pow_mul, h2, inv_inv]
      rw [← hkey]
      exact A'.zpow_mem hk2 (-(m : ℤ))
    exact Subgroup.mem_subgroupOf.mp hk'
  · rw [hA, card_oddOrderGrp φ]

theorem exists_mul_centralizes_oddOrderGrp {V Sig : Subgroup G}
    (hcomm : ∀ v ∈ V, ∀ s ∈ Sig, v * s = s * v) (hinf : V ⊓ Sig = ⊥)
    (hV : ∀ v ∈ V, v * v = 1) (φ : ↥Sig ≃* Equiv.Perm (Fin 4)) {g : G}
    (hg : g ∈ normalizer ((V ⊔ Sig : Subgroup G) : Set G)) :
    ∃ σ ∈ Sig, ∀ a ∈ oddOrderGrp Sig, (σ * g) * a * (σ * g)⁻¹ = a := by
  let A : Subgroup G := oddOrderGrp Sig
  let K : Subgroup G := V ⊔ Sig
  have hA_le : A ≤ Sig := show oddOrderGrp Sig ≤ Sig from oddOrderGrp_le Sig
  have hodd_mem_sig : ∀ k ∈ K, ¬ 2 ∣ orderOf k → k ∈ Sig := by
    intro k hk hodd
    change k ∈ V ⊔ Sig at hk
    obtain ⟨v, hv, s, hs, rfl⟩ := (mem_sup_iff_of_commute hcomm).1 hk
    have hcomm' : Commute v s := hcomm v hv s hs
    obtain ⟨m, hm⟩ := Nat.not_even_iff_odd.mp fun hE => hodd (even_iff_two_dvd.mp hE)
    have hvm : v ^ (2 * m + 1) = v := by
      rw [pow_succ, pow_mul, pow_two, hV v hv, one_pow, one_mul]
    have hkpow : (v * s) ^ (2 * m + 1) = 1 := by
      rw [← hm]; exact pow_orderOf_eq_one _
    have hvs : (v * s) ^ (2 * m + 1) = v ^ (2 * m + 1) * s ^ (2 * m + 1) :=
      hcomm'.mul_pow _
    have hvs1 : v * s ^ (2 * m + 1) = 1 := by
      rw [hvs, hvm] at hkpow; exact hkpow
    have hv_sig : v ∈ Sig := by
      rw [eq_inv_of_mul_eq_one_left hvs1]
      exact Sig.inv_mem (Sig.pow_mem hs _)
    have hv1 : v = 1 := by
      have : v ∈ (⊥ : Subgroup G) := by rw [← hinf]; exact ⟨hv, hv_sig⟩
      exact Subgroup.mem_bot.mp this
    rw [hv1, one_mul]
    exact hs
  have hgK : ∀ x ∈ K, g * x * g⁻¹ ∈ K := by
    have hgmap : K.map (MulAut.conj g).toMonoidHom = K :=
      (Subgroup.mem_normalizer_iff_map_conj_eq (H := K)).mp hg
    intro x hx
    have : MulAut.conj g x ∈ K.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rw [hgmap] at this
    simpa [MulAut.conj_apply] using this
  have hconjA : ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    have hgen : ∀ k ∈ {k : G | k ∈ Sig ∧ ¬ 2 ∣ orderOf k}, g * k * g⁻¹ ∈ A := by
      rintro k ⟨hkSig, hkodd⟩
      have hgkK : g * k * g⁻¹ ∈ K := hgK k (Subgroup.mem_sup_right hkSig)
      have hgkodd : ¬ 2 ∣ orderOf (g * k * g⁻¹) := by
        have h := MulEquiv.orderOf_eq (MulAut.conj g) k
        rw [MulAut.conj_apply] at h
        rwa [h]
      exact Subgroup.subset_closure ⟨hodd_mem_sig _ hgkK hgkodd, hgkodd⟩
    have hmap : A.map (MulAut.conj g).toMonoidHom ≤ A := by
      change (oddOrderGrp Sig).map (MulAut.conj g).toMonoidHom ≤ A
      rw [oddOrderGrp, MonoidHom.map_closure]
      exact (Subgroup.closure_le A).mpr (by
        rintro x ⟨k, hk, rfl⟩
        exact hgen k hk)
    intro a ha
    have : MulAut.conj g a ∈ A.map (MulAut.conj g).toMonoidHom := ⟨a, ha, rfl⟩
    have := hmap this
    simpa [MulAut.conj_apply] using this
  let a0 : G := (φ.symm c4 : G)
  let b0 : G := (φ.symm d4 : G)
  have ha0Sig : a0 ∈ Sig := (φ.symm c4).2
  have hb0Sig : b0 ∈ Sig := (φ.symm d4).2
  have hH_eq_A : closure ({a0, b0} : Set G) = A := by
    have h1 : (closure ({c4, d4} : Set (Equiv.Perm (Fin 4)))).map (phiHom φ)
        = closure ({a0, b0} : Set G) := by
      rw [MonoidHom.map_closure]
      congr 1
      ext x; constructor
      · rintro ⟨p, hp, rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp ⊢
        rcases hp with rfl | rfl
        · exact Or.inl (by simp [phiHom, a0])
        · exact Or.inr (by simp [phiHom, b0])
      · intro hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact ⟨c4, by simp, by simp [phiHom, a0]⟩
        · exact ⟨d4, by simp, by simp [phiHom, b0]⟩
    rw [← h1, closure_gen_eq_alternating, ← oddOrderGrp_eq_map]
  have ha0A : a0 ∈ A := by
    rw [← hH_eq_A]
    exact Subgroup.subset_closure (by simp [a0])
  have hb0A : b0 ∈ A := by
    rw [← hH_eq_A]
    exact Subgroup.subset_closure (by simp [b0])
  let u : G := g * a0 * g⁻¹
  let w : G := g * b0 * g⁻¹
  have huA : u ∈ A := by simpa [u] using hconjA a0 ha0A
  have hwA : w ∈ A := by simpa [w] using hconjA b0 hb0A
  have huSig : u ∈ Sig := hA_le huA
  have hwSig : w ∈ Sig := hA_le hwA
  have ha0_order : orderOf a0 = 3 := by
    change orderOf ((φ.symm c4 : ↥Sig) : G) = 3
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  have hb0_order : orderOf b0 = 2 := by
    change orderOf ((φ.symm d4 : ↥Sig) : G) = 2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by decide) (by decide)
  have ha0_3 : a0 ^ 3 = 1 := by rw [← ha0_order]; exact pow_orderOf_eq_one a0
  have hb0_2 : b0 ^ 2 = 1 := by rw [← hb0_order]; exact pow_orderOf_eq_one b0
  have ha0_ne : a0 ≠ 1 := by
    intro h; rw [h, orderOf_one] at ha0_order; omega
  have hb0_ne : b0 ≠ 1 := by
    intro h; rw [h, orderOf_one] at hb0_order; omega
  have hu3 : u ^ 3 = 1 := by
    change (g * a0 * g⁻¹) ^ 3 = 1
    rw [← MulAut.conj_apply g a0, ← map_pow, ha0_3, map_one]
  have hw2 : w ^ 2 = 1 := by
    change (g * b0 * g⁻¹) ^ 2 = 1
    rw [← MulAut.conj_apply g b0, ← map_pow, hb0_2, map_one]
  have hu_ne : u ≠ 1 := by
    intro h
    apply ha0_ne
    have h' : MulAut.conj g a0 = 1 := by simpa [u, MulAut.conj_apply] using h
    exact (MulAut.conj g).injective (by rw [h', map_one])
  have hw_ne : w ≠ 1 := by
    intro h
    apply hb0_ne
    have h' : MulAut.conj g b0 = 1 := by simpa [w, MulAut.conj_apply] using h
    exact (MulAut.conj g).injective (by rw [h', map_one])
  let u' : Equiv.Perm (Fin 4) := φ ⟨u, huSig⟩
  let w' : Equiv.Perm (Fin 4) := φ ⟨w, hwSig⟩
  have hsign_phi : ∀ a (ha : a ∈ A), Equiv.Perm.sign (φ ⟨a, hA_le ha⟩) = 1 := by
    intro a ha
    have ha' : a ∈ (alternatingGroup (Fin 4)).map (phiHom φ) := by
      rw [← oddOrderGrp_eq_map]
      exact ha
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp ha'
    have hx : (⟨a, hA_le ha⟩ : ↥Sig) = φ.symm p := by
      apply Subtype.ext
      change a = (φ.symm p : G)
      rw [← hpa]
      rfl
    rw [hx, φ.apply_symm_apply]
    exact Equiv.Perm.mem_alternatingGroup.mp hp
  have hu'sign : Equiv.Perm.sign u' = 1 := hsign_phi u huA
  have hw'sign : Equiv.Perm.sign w' = 1 := hsign_phi w hwA
  have hu'3 : u' ^ 3 = 1 := by
    change (φ ⟨u, huSig⟩) ^ 3 = 1
    rw [← map_pow]
    have h : (⟨u, huSig⟩ : ↥Sig) ^ 3 = 1 := Subtype.ext (by simpa using hu3)
    rw [h, map_one]
  have hw'2 : w' ^ 2 = 1 := by
    change (φ ⟨w, hwSig⟩) ^ 2 = 1
    rw [← map_pow]
    have h : (⟨w, hwSig⟩ : ↥Sig) ^ 2 = 1 := Subtype.ext (by simpa using hw2)
    rw [h, map_one]
  have hu'ne : u' ≠ 1 := by
    intro h
    apply hu_ne
    have h' : (⟨u, huSig⟩ : ↥Sig) = 1 := φ.injective (by rw [map_one]; exact h)
    simpa using congrArg Subtype.val h'
  have hw'ne : w' ≠ 1 := by
    intro h
    apply hw_ne
    have h' : (⟨w, hwSig⟩ : ↥Sig) = 1 := φ.injective (by rw [map_one]; exact h)
    simpa using congrArg Subtype.val h'
  obtain ⟨s, _hs, hsc, hsd⟩ := simple_transitive u' (mem_allPerms u') w' (mem_allPerms w')
    hu'sign hw'sign hu'3 hu'ne hw'2 hw'ne
  have hσa : ((φ.symm s) * (φ.symm c4) * (φ.symm s)⁻¹ : ↥Sig) = ⟨u, huSig⟩ := by
    apply φ.injective
    simpa only [map_mul, map_inv, φ.apply_symm_apply, u'] using hsc
  have hσaG : ((φ.symm s : G) * a0 * ((φ.symm s : G))⁻¹) = u := by
    have h := congrArg Subtype.val hσa
    simpa [a0] using h
  have hσb : ((φ.symm s) * (φ.symm d4) * (φ.symm s)⁻¹ : ↥Sig) = ⟨w, hwSig⟩ := by
    apply φ.injective
    simpa only [map_mul, map_inv, φ.apply_symm_apply, w'] using hsd
  have hσbG : ((φ.symm s : G) * b0 * ((φ.symm s : G))⁻¹) = w := by
    have h := congrArg Subtype.val hσb
    simpa [b0] using h
  have hca0 : a0 * ((φ.symm s : G)⁻¹ * g) = ((φ.symm s : G)⁻¹ * g) * a0 := by
    have key : ((φ.symm s : G)⁻¹ * g) * a0 * ((φ.symm s : G)⁻¹ * g)⁻¹ = a0 := by
      have hσaG' : g * a0 * g⁻¹ = (φ.symm s : G) * a0 * (φ.symm s : G)⁻¹ := hσaG.symm
      calc ((φ.symm s : G)⁻¹ * g) * a0 * ((φ.symm s : G)⁻¹ * g)⁻¹
          = (φ.symm s : G)⁻¹ * (g * a0 * g⁻¹) * (φ.symm s : G) := by group
        _ = (φ.symm s : G)⁻¹ * ((φ.symm s : G) * a0 * (φ.symm s : G)⁻¹)
              * (φ.symm s : G) := by rw [hσaG']
        _ = a0 := by group
    have h := congrArg (fun t => t * ((φ.symm s : G)⁻¹ * g)) key
    have hx : ((φ.symm s : G)⁻¹ * g) * a0 = a0 * ((φ.symm s : G)⁻¹ * g) := by
      simpa [mul_assoc] using h
    exact hx.symm
  have hcb0 : b0 * ((φ.symm s : G)⁻¹ * g) = ((φ.symm s : G)⁻¹ * g) * b0 := by
    have key : ((φ.symm s : G)⁻¹ * g) * b0 * ((φ.symm s : G)⁻¹ * g)⁻¹ = b0 := by
      have hσbG' : g * b0 * g⁻¹ = (φ.symm s : G) * b0 * (φ.symm s : G)⁻¹ := hσbG.symm
      calc ((φ.symm s : G)⁻¹ * g) * b0 * ((φ.symm s : G)⁻¹ * g)⁻¹
          = (φ.symm s : G)⁻¹ * (g * b0 * g⁻¹) * (φ.symm s : G) := by group
        _ = (φ.symm s : G)⁻¹ * ((φ.symm s : G) * b0 * (φ.symm s : G)⁻¹)
              * (φ.symm s : G) := by rw [hσbG']
        _ = b0 := by group
    have h := congrArg (fun t => t * ((φ.symm s : G)⁻¹ * g)) key
    have hx : ((φ.symm s : G)⁻¹ * g) * b0 = b0 * ((φ.symm s : G)⁻¹ * g) := by
      simpa [mul_assoc] using h
    exact hx.symm
  have hle : A ≤ Subgroup.centralizer ({(φ.symm s : G)⁻¹ * g} : Set G) := by
    rw [← hH_eq_A]
    apply (Subgroup.closure_le _).mpr
    rintro x hx
    change x ∈ Subgroup.centralizer ({(φ.symm s : G)⁻¹ * g} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hca0
    · exact hcb0
  refine ⟨(φ.symm s)⁻¹, Sig.inv_mem (φ.symm s).2, ?_⟩
  intro a ha
  have hmem := hle (ha : a ∈ A)
  have hxa := Subgroup.mem_centralizer_singleton_iff.mp hmem
  rw [← hxa]
  group

end CFSG.OddStandard.SmallF3.HarrisU33.S4A

module

public import CFSG.GH74.GLS.C3.Layer1.St1EndNFam
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4AltEmb
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltTerm

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools Equiv Equiv.Perm CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.GHInv

namespace Lem711Alt

theorem exists_commuting_involution {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}
    (hσ2 : σ * σ = 1) (hsupp4 : σ.support.card = 4) :
    ∃ σ' : Perm Ω, σ' * σ' = 1 ∧ σ' ≠ 1 ∧ σ' ≠ σ ∧ sign σ' = 1 ∧ σ' * σ = σ * σ' ∧
      ∀ z, σ z = z → σ' z = z := by
  obtain ⟨a, ha⟩ : σ.support.Nonempty := by
    rw [← Finset.card_pos]
    omega
  have haσ : σ a ≠ a := Equiv.Perm.mem_support.1 ha
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun p : Perm Ω => p z) hσ2
    simpa using this
  obtain ⟨b, hb⟩ : ∃ b, b = σ a := ⟨_, rfl⟩
  have hσa : σ a = b := hb.symm
  have hσb : σ b = a := by rw [hb]; exact hσσ a
  have hab : a ≠ b := fun h' => haσ (by rw [hσa]; exact h'.symm)
  have hbsupp : b ∈ σ.support := by
    rw [Equiv.Perm.mem_support, hσb]
    exact hab
  obtain ⟨c, hcs, hca, hcb⟩ : ∃ c ∈ σ.support, c ≠ a ∧ c ≠ b := by
    by_contra hcon
    push Not at hcon
    have hsub : σ.support ⊆ {a, b} := by
      intro z hz
      by_cases hza : z = a
      · simp [hza]
      · simp [hcon z hz hza]
    have h1 := Finset.card_le_card hsub
    have h2 : ({a, b} : Finset Ω).card ≤ 2 := Finset.card_le_two
    omega
  have hcσ : σ c ≠ c := Equiv.Perm.mem_support.1 hcs
  obtain ⟨d, hd⟩ : ∃ d, d = σ c := ⟨_, rfl⟩
  have hσc : σ c = d := hd.symm
  have hσd : σ d = c := by rw [hd]; exact hσσ c
  have hcd : c ≠ d := fun h' => hcσ (by rw [hσc]; exact h'.symm)
  have hda : d ≠ a := by
    intro h'
    apply hcb
    have := congrArg σ (hσc.trans h')
    rw [hσσ, hσa] at this
    exact this
  have hdb : d ≠ b := by
    intro h'
    apply hca
    exact σ.injective ((hσc.trans h').trans hσa.symm)
  have hac : a ≠ c := fun h' => hca h'.symm
  have had : a ≠ d := fun h' => hda h'.symm
  have hbc : b ≠ c := fun h' => hcb h'.symm
  have hbd : b ≠ d := fun h' => hdb h'.symm
  have hdsupp : d ∈ σ.support := by
    rw [Equiv.Perm.mem_support, hσd]
    exact hcd
  have hsupp : σ.support = {a, b, c, d} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ (by
      rw [hsupp4, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hcd]
      · simp [hbc, hbd]
      · simp [hab, hac, had])
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ha
    · exact hbsupp
    · exact hcs
    · exact hdsupp
  have hσz : ∀ z, z ≠ a → z ≠ b → z ≠ c → z ≠ d → σ z = z := by
    intro z hza hzb hzc hzd
    have : z ∉ σ.support := by
      rw [hsupp]
      simp [hza, hzb, hzc, hzd]
    exact Equiv.Perm.notMem_support.1 this
  have hcases : ∀ z : Ω, z = a ∨ z = b ∨ z = c ∨ z = d ∨ (z ≠ a ∧ z ≠ b ∧ z ≠ c ∧ z ≠ d) := by
    intro z
    by_cases hza : z = a
    · exact Or.inl hza
    by_cases hzb : z = b
    · exact Or.inr (Or.inl hzb)
    by_cases hzc : z = c
    · exact Or.inr (Or.inr (Or.inl hzc))
    by_cases hzd : z = d
    · exact Or.inr (Or.inr (Or.inr (Or.inl hzd)))
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hza, hzb, hzc, hzd⟩)))
  obtain ⟨σ', hσ'def⟩ : ∃ σ' : Perm Ω, σ' = swap a c * swap b d := ⟨_, rfl⟩
  have hσ'a : σ' a = c := by
    rw [hσ'def, Perm.mul_apply, swap_apply_of_ne_of_ne hab had, swap_apply_left]
  have hσ'c : σ' c = a := by
    rw [hσ'def, Perm.mul_apply, swap_apply_of_ne_of_ne hcb hcd, swap_apply_right]
  have hσ'b : σ' b = d := by
    rw [hσ'def, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hda hcd.symm]
  have hσ'd : σ' d = b := by
    rw [hσ'def, Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hab.symm hbc]
  have hσ'z : ∀ z, z ≠ a → z ≠ b → z ≠ c → z ≠ d → σ' z = z := by
    intro z hza hzb hzc hzd
    rw [hσ'def, Perm.mul_apply, swap_apply_of_ne_of_ne hzb hzd, swap_apply_of_ne_of_ne hza hzc]
  refine ⟨σ', ?_, fun h' => hca (by
      have : σ' a = a := by rw [h']; rfl
      exact hσ'a.symm.trans this), fun h' => hcb (by
      have : σ' a = σ a := by rw [h']
      rw [hσ'a, hσa] at this
      exact this), ?_, ?_, ?_⟩
  · ext z
    rcases hcases z with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩
    · rw [h1, Perm.mul_apply, hσ'a, hσ'c]; rfl
    · rw [h1, Perm.mul_apply, hσ'b, hσ'd]; rfl
    · rw [h1, Perm.mul_apply, hσ'c, hσ'a]; rfl
    · rw [h1, Perm.mul_apply, hσ'd, hσ'b]; rfl
    · rw [Perm.mul_apply, hσ'z z h1 h2 h3 h4, hσ'z z h1 h2 h3 h4]; rfl
  · rw [hσ'def, Perm.sign_mul, sign_swap hac, sign_swap hbd]
    decide
  · ext z
    rcases hcases z with h1 | h1 | h1 | h1 | ⟨h1, h2, h3, h4⟩
    · rw [h1, Perm.mul_apply, Perm.mul_apply, hσa, hσ'b, hσ'a, hσc]
    · rw [h1, Perm.mul_apply, Perm.mul_apply, hσb, hσ'a, hσ'b, hσd]
    · rw [h1, Perm.mul_apply, Perm.mul_apply, hσc, hσ'd, hσ'c, hσa]
    · rw [h1, Perm.mul_apply, Perm.mul_apply, hσd, hσ'c, hσ'd, hσb]
    · rw [Perm.mul_apply, Perm.mul_apply, hσz z h1 h2 h3 h4, hσ'z z h1 h2 h3 h4,
        hσz z h1 h2 h3 h4]
  · intro z hz
    refine hσ'z z ?_ ?_ ?_ ?_
    · intro h'
      rw [h'] at hz
      exact haσ hz
    · intro h'
      rw [h'] at hz
      exact hab (hσb.symm.trans hz)
    · intro h'
      rw [h'] at hz
      exact hcσ hz
    · intro h'
      rw [h'] at hz
      exact hcd (hσd.symm.trans hz)

theorem eq_six_of_factorial_div_two {m : ℕ} (h5 : 5 ≤ m) (h11 : m ≤ 11)
    (h : m.factorial / 2 = 360) : m = 6 := by
  interval_cases m <;> first | rfl | (exfalso; revert h; decide)

theorem card_eq_six {X Ω : Type*} [Group X] [Fintype Ω] [DecidableEq Ω] {K : Subgroup X}
    (ι : X →* Perm Ω) (hι : Function.Injective ι) {F : Finset Ω} (hKF : K.map ι = altOn F)
    (hF5 : 5 ≤ F.card) (hF11 : F.card ≤ 11)
    (h360 : Nat.card (↥K ⧸ pPrimeCore 2 ↥K) = 360) : F.card = 6 := by
  let eK0 : ↥K ≃* altOn F :=
    (Subgroup.equivMapOfInjective K ι hι).trans (MulEquiv.subgroupCongr hKF)
  let eK1 : ↥K ≃* alternatingGroup (Fin F.card) :=
    eK0.trans ((altOnEquiv F).symm.trans (Equiv.altCongrHom F.equivFin))
  have hKsimple : IsSimpleGroup ↥K := eK0.isSimpleGroup_congr.2 (isSimpleGroup_altOn hF5)
  have hbot : pPrimeCore 2 ↥K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥K) with h' | h'
    · exact h'
    · exfalso
      have h360' : (pPrimeCore 2 ↥K).index = 360 := h360
      rw [h', Subgroup.index_top] at h360'
      omega
  let eQ : (↥K ⧸ pPrimeCore 2 ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hcardK : Nat.card ↥K = 360 := by
    rw [← h360]
    exact (Nat.card_congr eQ.toEquiv).symm
  have hcardA : Nat.card (alternatingGroup (Fin F.card)) = F.card.factorial / 2 := by
    have : Nontrivial (Fin F.card) := Fin.nontrivial_iff_two_le.2 (by omega)
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [Nat.card_congr eK1.toEquiv, hcardA] at hcardK
  exact eq_six_of_factorial_div_two hF5 hF11 hcardK

end Lem711Alt

theorem lem711_alt :
    ∀ n : ℕ, 7 ≤ n → n ≤ 11 → Lem711Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  intro n hn7 hn11 X _ _ L K x y h ⟨e⟩
  have := h.normal
  obtain ⟨ι, hι, hιL⟩ := exists_perm_embedding hn7
    (fun z hz => h.soc.centralizer_trivial z (Subgroup.mem_top z) hz) e
  have hNA : alternatingGroup (Fin n) ≤ ι.range := by
    intro g hg
    refine ⟨((e.symm ⟨g, hg⟩ : ↥L) : X), ?_⟩
    rw [hιL]
    simp
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h.hx, pow_two] at this
  have hx1 : x ≠ 1 := by
    intro h1
    have h3 := h.hx
    rw [h1, orderOf_one] at h3
    omega
  obtain ⟨σ, hσdef⟩ : ∃ σ : Perm (Fin n), σ = ι x := ⟨_, rfl⟩
  have hσ2 : σ * σ = 1 := by rw [hσdef, ← map_mul, hxx, map_one]
  have hσ1 : σ ≠ 1 := fun h1 => hx1 (hι (by rw [← hσdef, h1, map_one]))
  have hsign : sign σ = 1 := by
    have hker : x ∈ ((sign : Perm (Fin n) →* ℤˣ).comp ι).ker :=
      Abelianization.commutator_subset_ker _ h.x_mem_commutator
    have := MonoidHom.mem_ker.1 hker
    rwa [MonoidHom.comp_apply, ← hσdef] at this
  obtain ⟨hcard, hsg⟩ := involution_cycle_data hσ2
  rw [hsign] at hsg
  have hceven : Even σ.cycleType.card := (neg_one_pow_eq_one_iff_even (by decide)).1 hsg.symm
  have hcpos : 0 < σ.cycleType.card := by
    by_contra hc0
    have h0 : σ.cycleType.card = 0 := by omega
    rw [h0, mul_zero, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff] at hcard
    exact hσ1 hcard
  have hsuple : σ.support.card ≤ n := by
    have := Finset.card_le_univ σ.support
    rwa [Fintype.card_fin] at this
  obtain ⟨r, hr⟩ := hceven
  have hc4 : σ.cycleType.card ≤ 4 := by omega
  have hKA : K.map ι ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [show ι k = ((e ⟨k, h.K_le hk⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) from
      hιL ⟨k, h.K_le hk⟩]
    exact (e _).2
  have hKp : Group.IsPerfect (K.map ι) := by
    have := h.K_quasi.1
    exact Group.IsPerfect.map ι
  have hK1 : K ≠ ⊥ := by
    intro hK
    obtain ⟨a, b, hab⟩ := h.K_quasi.2.2
    have : Subsingleton ↥K := by rw [hK]; infer_instance
    exact hab (Subsingleton.elim _ _)
  have hK1' : K.map ι ≠ ⊥ := by
    intro hK
    exact hK1 ((Subgroup.map_eq_bot_iff_of_injective K hι).1 hK)
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (mem_centralizer_singleton_iff.1 (h.comp.1 hk)).symm
  have hσK : ∀ k ∈ K.map ι, σ * k = k * σ := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hσdef, ← map_mul, ← map_mul, hxK k hk]
  obtain ⟨F, hFdef⟩ : ∃ F : Finset (Fin n), F = σ.supportᶜ := ⟨_, rfl⟩
  have hF : ∀ z, z ∈ F ↔ σ z = z := by
    intro z
    simp [hFdef, Equiv.Perm.mem_support]
  have hKsym : K.map ι ≤ symOn F := by
    intro k hk z hz
    have hσz : σ z ≠ z := fun h' => hz ((hF z).2 h')
    exact perfect_fixes_support hσ2 hc4 hKp (fun k hk => (hσK k hk).symm) k hk z hσz
  have hF5 : 5 ≤ F.card := by
    by_contra hlt
    exact hK1' (eq_bot_of_perfect_le_symOn (by omega) hKp hKsym)
  have hterm : Terminal ι.range (K.map ι) :=
    terminal_map ι hι hNA K (fun y hy hyk => (h.terminal y hy (fun k hk => (hyk k hk).symm)).2.2)
  have hKeq : K.map ι = altOn F :=
    hterm σ ⟨x, hσdef.symm⟩ hσ2 hσ1 hσK F hF5 (fun z hz => (hF z).1 hz)
      (fun k hk => Subgroup.mem_inf.2 ⟨hKsym hk, hKA hk⟩) hK1'
  have hFle : F.card ≤ 11 := by
    have := Finset.card_le_univ F
    rw [Fintype.card_fin] at this
    omega
  have h6 : F.card = 6 := Lem711Alt.card_eq_six ι hι hKeq hF5 hFle h.card_K_bar
  have hn : σ.support.card + F.card = n := by
    have := Finset.card_add_card_compl σ.support
    rwa [Fintype.card_fin, ← hFdef] at this
  have hsupp4 : σ.support.card = 4 := by omega
  obtain ⟨σ', hσ'2, hσ'1, hσ'ne, hσ'sign, hσ'comm, hσ'fix⟩ :=
    Lem711Alt.exists_commuting_involution hσ2 hsupp4
  obtain ⟨x', hx'⟩ := hNA (Equiv.Perm.mem_alternatingGroup.2 hσ'sign)
  have hx'2 : x' * x' = 1 := hι (by rw [map_mul, hx', hσ'2, map_one])
  have hx'1 : x' ≠ 1 := fun h' => hσ'1 (by rw [← hx', h', map_one])
  have hx'ord : orderOf x' = 2 := orderOf_eq_prime (by rw [sq]; exact hx'2) hx'1
  have hx'K : ∀ k ∈ K, x' * k = k * x' := by
    intro k hk
    apply hι
    rw [map_mul, map_mul, hx']
    exact (commute_of_symOn_of_fixes (hKsym (Subgroup.mem_map_of_mem ι hk))
      fun z hz => hσ'fix z ((hF z).1 hz)).symm
  have hx'x : x' * x = x * x' := by
    apply hι
    rw [map_mul, map_mul, hx', ← hσdef]
    exact hσ'comm
  have hx'eq := h.h1 x' hx'ord hx'K hx'x
  exact hσ'ne (by rw [← hx', hx'eq, hσdef])

end CFSG.GH74.GLS

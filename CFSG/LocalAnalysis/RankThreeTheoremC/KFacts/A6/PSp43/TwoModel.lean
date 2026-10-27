module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.PSp43.AutPerm

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

open CFSG.Open CFSG.GH74.Exceptional CFSG.ComponentClassification.CatFactsSmall.PSp43 Subgroup

@[expose] def powTab (t : Tab) (n : ℕ) : Tab := (tmul t)^[n] tid

@[expose] def normOK (i : ℕ) : Bool :=
  match normW.getD i (0, 0, 0, []) with
  | (0, _, _, _) => [tid, wtab x0W, tmul (wtab x0W) (wtab x0W)].contains (Q0elems.getD i [])
  | (1, a, b, _) => wtab (U1gens.getD 1 []) ==
      tmul (powTab (wtab x0W) a) (powTab (Q0elems.getD i []) b)
  | (2, a, b, _) => wtab (U2gens.getD 1 []) ==
      tmul (powTab (wtab x0W) a) (powTab (Q0elems.getD i []) b)
  | (3, a, b, g) =>
      tmul (powTab (wtab x0W) a) (powTab (Q0elems.getD i []) b) == conjTab g (wtab x0W) &&
      !([tid, wtab x0W, tmul (wtab x0W) (wtab x0W)].contains
        (tmul (powTab (wtab x0W) a) (powTab (Q0elems.getD i []) b)))
  | _ => false

theorem norm_OK : (List.range Q0elems.length).all normOK = true := by decide +kernel

theorem U1gens_eq : U1gens = [x0W, U1gens.getD 1 []] := by decide
theorem U2gens_eq : U2gens = [x0W, U2gens.getD 1 []] := by decide

theorem x0_cube : tmul (wtab x0W) (tmul (wtab x0W) (wtab x0W)) = tid := by decide +kernel

theorem x0_pow_three : wperm x0W ^ 3 = 1 := by
  have h := rep_mul (rep_wperm x0W) (rep_mul (rep_wperm x0W) (rep_wperm x0W))
  rw [x0_cube] at h
  rw [pow_three]
  exact rep_unique h rep_one

theorem x0_ne_one : wperm x0W ≠ 1 := by
  intro h
  have := rep_eq_tab (rep_wperm x0W) (h ▸ rep_one)
  exact absurd this (by decide)

theorem mem_zpowers_x0 {y : Equiv.Perm (Fin 45)} (hy : y ∈ zpowers (wperm x0W)) :
    y = 1 ∨ y = wperm x0W ∨ y = wperm x0W * wperm x0W := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
  have ho : orderOf (wperm x0W) = 3 := orderOf_eq_prime x0_pow_three x0_ne_one
  rw [← zpow_mod_orderOf, ho]
  have h3 : k % (3 : ℕ) < 3 := Int.emod_lt_of_pos k (by norm_num)
  have h0 : 0 ≤ k % (3 : ℕ) := Int.emod_nonneg k (by norm_num)
  interval_cases h : k % (3 : ℕ)
  · left; simp
  · right; left; simp
  · right; right
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two]

abbrev U1 : Subgroup (Equiv.Perm (Fin 45)) := gen (U1gens.map wperm)

abbrev U2 : Subgroup (Equiv.Perm (Fin 45)) := gen (U2gens.map wperm)

theorem card_U1 : Nat.card U1 = 9 := (card_gen_words U1_enumOK).trans (by decide)
theorem card_U2 : Nat.card U2 = 9 := (card_gen_words U2_enumOK).trans (by decide)

theorem eq_of_mem_gens {V : Subgroup (Equiv.Perm (Fin 45))} (hV : Nat.card V = 9)
    {ws : List (List (Fin 45))} (hws : ws = [x0W, ws.getD 1 []])
    (hcard : Nat.card (gen (ws.map wperm)) = 9) (hx : wperm x0W ∈ V)
    (hu : wperm (ws.getD 1 []) ∈ V) : V = gen (ws.map wperm) := by
  have hle : gen (ws.map wperm) ≤ V := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [hws] at hg
    simp only [List.map_cons, List.map_nil, Set.mem_setOf_eq, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hx
    · exact hu
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hV, hcard])).symm

theorem exists_conj_edge {Q' U' : Subgroup (Equiv.Perm (Fin 45))} {x' : Equiv.Perm (Fin 45)}
    (hQP : Q' ≤ P) (hQ : ∀ a ∈ Q', ∀ b ∈ Q', a * b = b * a) (hQc : Nat.card Q' = 27)
    (hUQ : U' ≤ Q') (hUc : Nat.card U' = 9) (hxU : x' ∈ U')
    (hxc : Nat.card ↥(P ⊓ centralizer ({x'} : Set (Equiv.Perm (Fin 45)))) = 108)
    (hwc : ∀ h ∈ P, (zpowers x').map (MulAut.conj h).toMonoidHom ≤ U' →
      (zpowers x').map (MulAut.conj h).toMonoidHom = zpowers x') :
    ∃ g ∈ P, U'.map (MulAut.conj g).toMonoidHom = U1 ∨
      U'.map (MulAut.conj g).toMonoidHom = U2 := by
  have hQp : IsPGroup 3 (Q'.subgroupOf P) :=
    IsPGroup.of_card (n := 3) (by rw [card_subgroupOf_of_le hQP, hQc]; norm_num)
  obtain ⟨S, hS⟩ := hQp.exists_le_sylow
  set SP := (S.toSubgroup).map P.subtype
  have hSPP : SP ≤ P := Subgroup.map_subtype_le _
  have hSPc : Nat.card SP = 3 ^ (Nat.card P).factorization 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, Sylow.card_eq_multiplicity]
  have hQSP : Q' ≤ SP := fun q hq => ⟨⟨q, hQP hq⟩, hS (mem_subgroupOf.2 hq), rfl⟩
  obtain ⟨g₁, hg₁, hg⟩ := exists_conj_eq_of_card P3_le_P hSPP card_P3_eq hSPc
  have hconj : ∀ q ∈ Q', g₁⁻¹ * q * g₁ ∈ P3 := by
    intro q hq
    have := hQSP hq
    rw [hg] at this
    obtain ⟨s, hs, hsq⟩ := this
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hsq
    rw [← hsq]
    simpa [mul_assoc] using hs
  set Q₁ := Q'.map (MulAut.conj g₁⁻¹).toMonoidHom
  have hQ₁c : Nat.card Q₁ = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hQc]
  have hQ₁P3 : ∀ q ∈ Q₁, q ∈ P3 := by
    rintro _ ⟨q, hq, rfl⟩
    simpa using hconj q hq
  have hQ₁comm : ∀ a ∈ Q₁, ∀ b ∈ Q₁, a * b = b * a := comm_of_map hQ
  have hQ₁Q0 : Q₁ ≤ Q0 := by
    intro q hq
    by_contra hqQ
    have h9 := card_centralizer_P3_le (hQ₁P3 q hq) hqQ
    have hle : Q₁ ≤ P3 ⊓ centralizer ({q} : Set (Equiv.Perm (Fin 45))) := fun a ha =>
      ⟨hQ₁P3 a ha, mem_centralizer_singleton_iff.2 (hQ₁comm a ha q hq)⟩
    have := Subgroup.card_le_of_le hle
    omega
  have hQ₁eq : Q₁ = Q0 := Subgroup.eq_of_le_of_card_ge hQ₁Q0 (by rw [hQ₁c, card_Q0])
  have hx₁ : g₁⁻¹ * x' * g₁ ∈ Q0 := by
    rw [← hQ₁eq]
    exact ⟨x', hUQ hxU, by simp [MulAut.conj_apply]⟩
  have hx₁c : Nat.card ↥(P ⊓ centralizer ({g₁⁻¹ * x' * g₁} : Set (Equiv.Perm (Fin 45)))) =
      108 := by
    have := card_centralizer_conj (inv_mem hg₁) x'
    simp only [inv_inv] at this
    rw [this, hxc]
  obtain ⟨n, hnP, hnN, hn⟩ := exists_conj_x0_of_mem_Q0 hx₁ hx₁c
  set g := n * g₁⁻¹
  have hgP : g ∈ P := mul_mem hnP (inv_mem hg₁)
  set U₂ := U'.map (MulAut.conj g).toMonoidHom
  have hU₂c : Nat.card U₂ = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hUc]
  have hx0U₂ : wperm x0W ∈ U₂ := ⟨x', hxU, by rw [hn]; simp [g, MulAut.conj_apply, mul_assoc]⟩
  have hU₂Q0 : ∀ u ∈ U₂, u ∈ Q0 := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : g₁⁻¹ * u * g₁ ∈ Q0 := by
      rw [← hQ₁eq]
      exact ⟨u, hUQ hu, by simp [MulAut.conj_apply]⟩
    have h2 := (mem_normalizer_iff.1 hnN _).1 h1
    simpa [g, MulAut.conj_apply, mul_assoc] using h2
  have hwc₂ : ∀ h ∈ P, h * wperm x0W * h⁻¹ ∈ U₂ → h * wperm x0W * h⁻¹ ∈ zpowers (wperm x0W) := by
    intro h hhP hy
    set h' := g⁻¹ * h * g
    have hh'P : h' ∈ P := mul_mem (mul_mem (inv_mem hgP) hhP) hgP
    have e1 : h' * x' * h'⁻¹ = g⁻¹ * (h * wperm x0W * h⁻¹) * g := by
      rw [hn]; simp only [h', g]; group
    have hmem : h' * x' * h'⁻¹ ∈ U' := by
      rw [e1]
      obtain ⟨u, hu, hu'⟩ := hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hu'
      rw [← hu']
      simpa [mul_assoc] using hu
    have hle : (zpowers x').map (MulAut.conj h').toMonoidHom ≤ U' := by
      rw [MonoidHom.map_zpowers, zpowers_le]
      exact hmem
    have heq := hwc h' hh'P hle
    have h2 : h' * x' * h'⁻¹ ∈ zpowers x' := by
      rw [← heq]
      exact ⟨x', mem_zpowers x', rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h2
    have e2 : h * wperm x0W * h⁻¹ = g * (h' * x' * h'⁻¹) * g⁻¹ := by
      rw [e1]; group
    have hx0g : wperm x0W = g * x' * g⁻¹ := by rw [hn]; simp only [g]; group
    refine mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [e2, ← hk, hx0g]
    rw [← MulAut.conj_apply, ← map_zpow, MulAut.conj_apply]
  obtain ⟨u, huU₂, hux⟩ : ∃ u ∈ U₂, u ∉ zpowers (wperm x0W) := by
    by_contra hno
    push Not at hno
    have hle : U₂ ≤ zpowers (wperm x0W) := hno
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, orderOf_eq_prime x0_pow_three x0_ne_one, hU₂c] at h1
    omega
  obtain ⟨i, hi, hr⟩ := (mem_gen_words Q0_enumOK u).1 (hU₂Q0 u huU₂)
  have hok := List.all_eq_true.1 norm_OK i (List.mem_range.2 hi)
  have hX := rep_wperm x0W
  have hpowmem : ∀ a b : ℕ, wperm x0W ^ a * u ^ b ∈ U₂ := fun a b =>
    mul_mem (pow_mem hx0U₂ a) (pow_mem huU₂ b)
  have hpowrep : ∀ a b : ℕ, Rep (wperm x0W ^ a * u ^ b)
      (tmul (powTab (wtab x0W) a) (powTab (Q0elems.getD i []) b)) := fun a b =>
    rep_mul (rep_pow hX a) (rep_pow hr b)
  unfold normOK at hok
  split at hok
  ·
    exfalso
    simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at hok
    apply hux
    rcases hok with h | h | h
    · rw [rep_unique hr (h ▸ rep_one)]; exact one_mem _
    · rw [rep_unique hr (h ▸ hX)]; exact mem_zpowers _
    · rw [rep_unique hr (h ▸ rep_mul hX hX)]
      exact mul_mem (mem_zpowers _) (mem_zpowers _)
  ·
    rename_i a b _ _
    rw [beq_iff_eq] at hok
    have hu1 : wperm (U1gens.getD 1 []) = wperm x0W ^ a * u ^ b :=
      rep_unique (rep_wperm _) (hok ▸ hpowrep a b)
    exact ⟨g, hgP, Or.inl (eq_of_mem_gens hU₂c U1gens_eq card_U1 hx0U₂ (hu1 ▸ hpowmem a b))⟩
  ·
    rename_i a b _ _
    rw [beq_iff_eq] at hok
    have hu2 : wperm (U2gens.getD 1 []) = wperm x0W ^ a * u ^ b :=
      rep_unique (rep_wperm _) (hok ▸ hpowrep a b)
    exact ⟨g, hgP, Or.inr (eq_of_mem_gens hU₂c U2gens_eq card_U2 hx0U₂ (hu2 ▸ hpowmem a b))⟩
  ·
    exfalso
    rename_i a b gw _
    rw [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      List.contains_iff_mem] at hok
    obtain ⟨hy, hnot⟩ := hok
    have hyeq : wperm x0W ^ a * u ^ b = wperm gw * wperm x0W * (wperm gw)⁻¹ :=
      rep_unique (hpowrep a b) (hy ▸ rep_conj gw hX)
    have hz := hwc₂ (wperm gw) (wperm_mem gw) (hyeq ▸ hpowmem a b)
    rw [← hyeq] at hz
    apply hnot
    rcases mem_zpowers_x0 hz with h | h | h
    · rw [rep_eq_tab (hpowrep a b) (h ▸ rep_one)]; simp
    · rw [rep_eq_tab (hpowrep a b) (h ▸ hX)]; simp
    · rw [rep_eq_tab (hpowrep a b) (h ▸ rep_mul hX hX)]; simp
  · exact absurd hok (by simp)

theorem map_le_normalizer_map {U Y : Subgroup (Equiv.Perm (Fin 45))} (g : Equiv.Perm (Fin 45))
    (hN : U ≤ normalizer (Y : Set (Equiv.Perm (Fin 45)))) :
    U.map (MulAut.conj g).toMonoidHom ≤
      normalizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup (Equiv.Perm (Fin 45))) :
        Set (Equiv.Perm (Fin 45))) := by
  rintro _ ⟨u, hu, rfl⟩
  refine mem_normalizer_of_conj_mem' _ _ fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨u * y * u⁻¹, (mem_normalizer_iff.1 (hN hu) y).1 hy, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem exists_z_of_normalized {U' : Subgroup (Equiv.Perm (Fin 45))} {g : Equiv.Perm (Fin 45)}
    (hg : g ∈ P) (hU : U'.map (MulAut.conj g).toMonoidHom = U1 ∨
      U'.map (MulAut.conj g).toMonoidHom = U2)
    {Y : Subgroup (Equiv.Perm (Fin 45))} (hYP : Y ≤ P) (hY : IsPGroup 2 Y)
    (hN : U' ≤ normalizer (Y : Set (Equiv.Perm (Fin 45)))) :
    ∃ z ∈ P, z ^ 2 = 1 ∧ z ≠ 1 ∧
      Nat.card ↥(P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45)))) = 576 ∧
      Y ≤ pCoreOf 2 (P ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 45)))) := by
  set Y₂ := Y.map (MulAut.conj g).toMonoidHom
  have hY₂P : Y₂ ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hg (hYP hy)) (inv_mem hg)
  have hY₂ : IsPGroup 2 Y₂ := hY.map _
  have hN₂ := map_le_normalizer_map g hN
  have key : ∃ i : Fin 45, Y₂ ≤ pCoreOf 2 (P ⊓ centralizer ({tauPerm i} : Set _)) := by
    rcases hU with h | h
    · rw [h] at hN₂
      obtain ⟨i, -, hi⟩ := le_conj_E_of_normalized U1_enumOK (by decide) U1_fix U1_stab
        U1fix_card hY₂P hY₂ hN₂
      exact ⟨i, (conj_E_eq i) ▸ hi⟩
    · rw [h] at hN₂
      obtain ⟨i, -, hi⟩ := le_conj_E_of_normalized U2_enumOK (by decide) U2_fix U2_stab
        U2fix_card hY₂P hY₂ hN₂
      exact ⟨i, (conj_E_eq i) ▸ hi⟩
  obtain ⟨i, hi⟩ := key
  refine ⟨g⁻¹ * tauPerm i * g⁻¹⁻¹, mul_mem (mul_mem (inv_mem hg) (tauPerm_mem i))
    (inv_mem (inv_mem hg)), ?_, ?_, ?_, ?_⟩
  · rw [pow_two]
    have := tauPerm_mul_self i
    calc g⁻¹ * tauPerm i * g⁻¹⁻¹ * (g⁻¹ * tauPerm i * g⁻¹⁻¹) =
        g⁻¹ * (tauPerm i * tauPerm i) * g := by group
      _ = 1 := by rw [this]; group
  · intro h
    apply tauPerm_ne_one i
    calc tauPerm i = g * (g⁻¹ * tauPerm i * g⁻¹⁻¹) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  · rw [card_centralizer_conj (inv_mem hg), card_centralizer_tau]
  · rw [P_inf_centralizer_conj (inv_mem hg), pCoreOf_map_of_injective' (MulAut.conj _).injective]
    intro y hy
    refine ⟨g * y * g⁻¹, hi ⟨y, hy, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mem_P_of_equivariant_conj {U' : Subgroup (Equiv.Perm (Fin 45))} {g : Equiv.Perm (Fin 45)}
    (hg : g ∈ P) (hU : U'.map (MulAut.conj g).toMonoidHom = U1 ∨
      U'.map (MulAut.conj g).toMonoidHom = U2)
    {π : Equiv.Perm (Fin 45)} (hπ : IsEquivariant π) (hcomm : ∀ u ∈ U', π * u = u * π)
    (h2 : IsPGroup 2 (zpowers π)) : π ∈ P := by
  set π' := g * π * g⁻¹
  have hπ' : IsEquivariant π' :=
    ((isEquivariant_of_mem_P hg).mul hπ).mul (isEquivariant_of_mem_P (inv_mem hg))
  have hcomm' : ∀ u ∈ U'.map (MulAut.conj g).toMonoidHom, π' * u = u * π' := by
    rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, π']
    calc g * π * g⁻¹ * (g * u * g⁻¹) = g * (π * u) * g⁻¹ := by group
      _ = g * (u * π) * g⁻¹ := by rw [hcomm u hu]
      _ = g * u * g⁻¹ * (g * π * g⁻¹) := by group
  have h2' : IsPGroup 2 (zpowers π') := by
    have : zpowers π' = (zpowers π).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]; rfl
    rw [this]
    exact h2.map _
  have hmem : π' ∈ P := by
    rcases hU with h | h
    · rw [h] at hcomm'
      exact mem_P_of_equivariant U1_enumOK U1_fix U1fix_card rig1_OK rig1_cov rig1_card hπ'
        (fun w hw => hcomm' _ (wperm_mem_gen hw)) h2'
    · rw [h] at hcomm'
      exact mem_P_of_equivariant U2_enumOK U2_fix U2fix_card rig2_OK rig2_cov rig2_card hπ'
        (fun w hw => hcomm' _ (wperm_mem_gen hw)) h2'
  have : π = g⁻¹ * π' * g := by simp only [π']; group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hg) hmem) hg

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.PSp43

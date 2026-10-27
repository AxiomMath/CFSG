module

public import CFSG.ClassicalInvolution.SmallCases.NobqL34Check
public import CFSG.ClassicalInvolution.SmallCases.NobqCommutator
public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ClassicalInvolution.Nobq

open CFSG.ComponentClassification.PSL3Four

theorem exists_conj_r₁ {T : Equiv.Perm (Fin 42)} (hT : T ∈ S) (hT1 : T ≠ 1) (hT2 : T * T = 1) :
    ∃ c ∈ R, T = c * r₁ * c⁻¹ := by
  have hTR : T ∈ R := S_le_R hT
  have ho : orderOf (⟨T, hTR⟩ : R) = 2 := by
    refine orderOf_eq_prime (by rw [pow_two]; exact Subtype.ext (by simpa using hT2))
      fun h => hT1 ?_
    exact congrArg Subtype.val h
  rcases (CFSG.ComponentClassification.PSL3Four.orderOf_eq_two_iff _).1 ho with h | h | h | h
  · exact eq_conj_of_isConj h
  · exact absurd hT (not_mem_S_of_isConj h not_mem_S_r₂)
  · exact absurd hT (not_mem_S_of_isConj h not_mem_S_r₃)
  · exact absurd hT (not_mem_S_of_isConj h not_mem_S_r₄)

theorem cq_conj {c₀ : Equiv.Perm (Fin 42)} (hc₀ : c₀ ∈ R) {T x : Equiv.Perm (Fin 42)}
    (hT : T = c₀ * r₁ * c₀⁻¹) (hxS : x ∈ S) (hxT : x * T = T * x) (hx2 : x * x = T) :
    ∃ g ∈ S, g * T = T * g ∧ (x * (g * x * g⁻¹)) * (x * (g * x * g⁻¹)) = 1 ∧
      x * (g * x * g⁻¹) ≠ 1 ∧ x * (g * x * g⁻¹) ≠ T := by
  subst hT
  have hx'S : c₀⁻¹ * x * c₀ ∈ S := by
    simpa using conj_mem_S (R.inv_mem hc₀) hxS
  have hx'r : (c₀⁻¹ * x * c₀) * r₁ = r₁ * (c₀⁻¹ * x * c₀) := by
    calc (c₀⁻¹ * x * c₀) * r₁ = c₀⁻¹ * (x * (c₀ * r₁ * c₀⁻¹)) * c₀ := by group
      _ = c₀⁻¹ * ((c₀ * r₁ * c₀⁻¹) * x) * c₀ := by rw [hxT]
      _ = r₁ * (c₀⁻¹ * x * c₀) := by group
  have hx'2 : (c₀⁻¹ * x * c₀) * (c₀⁻¹ * x * c₀) = r₁ := by
    calc (c₀⁻¹ * x * c₀) * (c₀⁻¹ * x * c₀) = c₀⁻¹ * (x * x) * c₀ := by group
      _ = r₁ := by rw [hx2]; group
  obtain ⟨g', hg'S, hg'r, h1, h2, h3⟩ := cq_C₁ hx'S hx'r hx'2
  have hgS : c₀ * g' * c₀⁻¹ ∈ S := conj_mem_S hc₀ hg'S
  have hW : x * ((c₀ * g' * c₀⁻¹) * x * (c₀ * g' * c₀⁻¹)⁻¹) =
      c₀ * ((c₀⁻¹ * x * c₀) * (g' * (c₀⁻¹ * x * c₀) * g'⁻¹)) * c₀⁻¹ := by group
  refine ⟨c₀ * g' * c₀⁻¹, hgS, ?_, ?_, ?_, ?_⟩
  · calc c₀ * g' * c₀⁻¹ * (c₀ * r₁ * c₀⁻¹) = c₀ * (g' * r₁) * c₀⁻¹ := by group
      _ = c₀ * (r₁ * g') * c₀⁻¹ := by rw [hg'r]
      _ = c₀ * r₁ * c₀⁻¹ * (c₀ * g' * c₀⁻¹) := by group
  · rw [hW]
    calc c₀ * ((c₀⁻¹ * x * c₀) * (g' * (c₀⁻¹ * x * c₀) * g'⁻¹)) * c₀⁻¹ *
          (c₀ * ((c₀⁻¹ * x * c₀) * (g' * (c₀⁻¹ * x * c₀) * g'⁻¹)) * c₀⁻¹)
        = c₀ * (((c₀⁻¹ * x * c₀) * (g' * (c₀⁻¹ * x * c₀) * g'⁻¹)) *
            ((c₀⁻¹ * x * c₀) * (g' * (c₀⁻¹ * x * c₀) * g'⁻¹))) * c₀⁻¹ := by group
      _ = 1 := by rw [h1]; group
  · rw [hW]
    intro h
    apply h2
    have := congrArg (fun z => c₀⁻¹ * z * c₀) h
    simpa [mul_assoc] using this
  · rw [hW]
    intro h
    apply h3
    have := congrArg (fun z => c₀⁻¹ * z * c₀) h
    simpa [mul_assoc] using this

theorem orderOf_dvd_sixtyfour {c₀ : Equiv.Perm (Fin 42)} (hc₀ : c₀ ∈ R)
    {T x : Equiv.Perm (Fin 42)} (hT : T = c₀ * r₁ * c₀⁻¹) (hxS : x ∈ S) (hxT : x * T = T * x) :
    orderOf x ∣ 64 := by
  subst hT
  have hx'S : c₀⁻¹ * x * c₀ ∈ S := by
    simpa using conj_mem_S (R.inv_mem hc₀) hxS
  have hx'r : (c₀⁻¹ * x * c₀) * r₁ = r₁ * (c₀⁻¹ * x * c₀) := by
    calc (c₀⁻¹ * x * c₀) * r₁ = c₀⁻¹ * (x * (c₀ * r₁ * c₀⁻¹)) * c₀ := by group
      _ = c₀⁻¹ * ((c₀ * r₁ * c₀⁻¹) * x) * c₀ := by rw [hxT]
      _ = r₁ * (c₀⁻¹ * x * c₀) := by group
  have hmem : c₀⁻¹ * x * c₀ ∈ C₁ := ⟨Subgroup.mem_centralizer_singleton_iff.2 hx'r, hx'S⟩
  have h1 : orderOf (⟨c₀⁻¹ * x * c₀, hmem⟩ : C₁) ∣ 64 := by
    rw [← card_C₁]
    exact orderOf_dvd_natCard _
  have h2 : orderOf (c₀⁻¹ * x * c₀) = orderOf x := by
    have := MulEquiv.orderOf_eq (MulAut.conj c₀⁻¹) x
    simpa [MulAut.conj_apply] using this
  rw [← h2]
  rw [Subgroup.orderOf_mk] at h1
  exact h1

theorem noDatum_of_stated_psl_three_four (F : Type) [Group F]
    (hF : CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSL 3 2 2) : NoDatum F := by
  obtain ⟨φ0⟩ := nonempty_equiv_of_stated F hF
  intro G _ _ N _ ⟨e⟩ hC R' S0 r hr ⟨eS⟩ t ht hto hRC hRn
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  let φ : ↥N ≃* ↥S := e.trans φ0
  obtain ⟨E, hE, -⟩ := full_automorphism_action
  let ι : G →* ↥R := E.symm.toMonoidHom.comp ((MulAut.congr φ).toMonoidHom.comp MulAut.conjNormal)
  have hEι : ∀ g : G, E (ι g) = MulAut.congr φ (MulAut.conjNormal g) := fun g =>
    E.apply_symm_apply _
  have hP1 : ∀ (g : G) (n : ↥N), ((ι g : ↥R) : Equiv.Perm (Fin 42)) *
      ((φ n : ↥S) : Equiv.Perm (Fin 42)) * ((ι g : ↥R) : Equiv.Perm (Fin 42))⁻¹ =
        ((φ (MulAut.conjNormal g n) : ↥S) : Equiv.Perm (Fin 42)) := by
    intro g n
    have h := hE (ι g) (φ n)
    have h' : ((MulAut.congr φ (MulAut.conjNormal g)) (φ n) : ↥S) =
        φ (MulAut.conjNormal g n) := by
      simp [MulAut.congr_apply]
    rw [hEι g, h', Subgroup.coe_inv] at h
    exact h.symm
  have hP2 : ∀ n : ↥N, ι (n : G) = ⟨((φ n : ↥S) : Equiv.Perm (Fin 42)), S_le_R (φ n).2⟩ := by
    intro n
    apply E.injective
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [hEι, hE, MulAut.congr_apply]
    simp [MulAut.conjNormal_val]
  have hι_inj : ∀ g : G, ι g = 1 → g = 1 := by
    intro g hg
    have hcomm : ∀ n ∈ (N : Set G), n * g = g * n := by
      intro n hn
      have h1 := hP1 g ⟨n, hn⟩
      rw [hg] at h1
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
      have h3 := φ.injective (Subtype.ext h1)
      have h4 := congrArg Subtype.val h3
      simp only [MulAut.conjNormal_apply] at h4
      calc n * g = (g * n * g⁻¹) * g := by rw [← h4]
        _ = g * n := by group
    have : g ∈ Subgroup.centralizer (N : Set G) := Subgroup.mem_centralizer_iff.2 hcomm
    rw [hC, Subgroup.mem_bot] at this
    exact this
  have hι_injective : Function.Injective ι := (injective_iff_map_eq_one ι).2 hι_inj
  have huniq : ∀ u ∈ R', orderOf u = 2 → u = t := fun u hu ho =>
    eq_of_orderOf_eq_two_of_datum S0 eS ht hto hRC hu ho
  by_cases htN : t ∈ N
  swap
  ·
    have : (S.subgroupOf R).Normal := S_normal
    let θ : ↥(S0 : Subgroup ↥R') →* ↥R ⧸ (S.subgroupOf R) :=
      (QuotientGroup.mk' (S.subgroupOf R)).comp
        (ι.comp (R'.subtype.comp (S0 : Subgroup ↥R').subtype))
    have hθ : Function.Injective θ := by
      rw [injective_iff_map_eq_one]
      intro s hs
      have hs' : ((ι (((s : ↥R') : G)) : ↥R) : Equiv.Perm (Fin 42)) ∈ S := by
        have := (QuotientGroup.eq_one_iff _).1 hs
        simpa [Subgroup.mem_subgroupOf] using this
      let n : ↥N := φ.symm ⟨_, hs'⟩
      have hn : ι (n : G) = ι (((s : ↥R') : G)) := by
        rw [hP2 n]
        apply Subtype.ext
        simp [n]
      have hsn : (n : G) = ((s : ↥R') : G) := hι_injective hn
      have hsN : (((s : ↥R') : G)) ∈ N := hsn ▸ n.2
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 S0.isPGroup' s
      by_contra hs1
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, orderOf_eq_one_iff] at hk
        exact hs1 hk
      have hord : orderOf (((s : ↥R') : G)) = 2 ^ k := by
        rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
        exact hk
      have h2 : orderOf ((((s : ↥R') : G)) ^ (2 ^ (k - 1))) = 2 := by
        rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num))
          (by rw [hord]; exact pow_dvd_pow 2 (by omega)), hord,
          Nat.pow_div (by omega) (by norm_num)]
        have : k - (k - 1) = 1 := by omega
        norm_num [this]
      have := huniq _ (R'.pow_mem (s : ↥R').2 _) h2
      exact htN (this ▸ N.pow_mem hsN _)
    have hcard1 : Nat.card ↥(S0 : Subgroup ↥R') ∣ Nat.card (↥R ⧸ S.subgroupOf R) :=
      Subgroup.card_dvd_of_injective θ hθ
    have hcard2 : Nat.card (↥R ⧸ S.subgroupOf R) = 12 := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (S.subgroupOf R)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S_le_R).toEquiv, card_R, card_S] at h
      omega
    have hcard3 : Nat.card ↥(S0 : Subgroup ↥R') = 4 * 2 ^ (r - 2) := by
      rw [Nat.card_congr eS.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    rw [hcard3, hcard2] at hcard1
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 3 := ⟨r - 3, by omega⟩
    have h8 : 8 ∣ 4 * 2 ^ (k + 3 - 2) := by
      rw [show k + 3 - 2 = k + 1 by omega, pow_succ]
      exact ⟨2 ^ k, by ring⟩
    have := h8.trans hcard1
    omega
  ·
    set tN : ↥N := ⟨t, htN⟩ with htNdef
    set T0 : Equiv.Perm (Fin 42) := ((φ tN : ↥S) : Equiv.Perm (Fin 42)) with hT0
    have hT0S : T0 ∈ S := (φ tN).2
    have hφt2 : orderOf (φ tN) = 2 := by
      rw [MulEquiv.orderOf_eq, htNdef, Subgroup.orderOf_mk]
      exact hto
    have hT0sq : T0 * T0 = 1 := by
      have := pow_orderOf_eq_one (φ tN)
      rw [hφt2, pow_two] at this
      simpa [T0] using congrArg Subtype.val this
    have hT01 : T0 ≠ 1 := by
      intro h
      have : φ tN = 1 := Subtype.ext h
      rw [this, orderOf_one] at hφt2
      exact absurd hφt2 (by norm_num)
    obtain ⟨c₀, hc₀, hTc⟩ := exists_conj_r₁ hT0S hT01 hT0sq
    have hcomm' : ∀ a : ↥N, (a : G) * t = t * (a : G) →
        ((φ a : ↥S) : Equiv.Perm (Fin 42)) * T0 = T0 * ((φ a : ↥S) : Equiv.Perm (Fin 42)) := by
      intro a ha
      have h1 : a * tN = tN * a := Subtype.ext ha
      have := congrArg (fun z : ↥N => ((φ z : ↥S) : Equiv.Perm (Fin 42))) h1
      simpa [T0] using this
    have hW : ∀ c ∈ N, c * t = t * c → c * c = t → ∃ g ∈ N, g * t = t * g ∧
        (c * (g * c * g⁻¹)) * (c * (g * c * g⁻¹)) = 1 ∧ c * (g * c * g⁻¹) ≠ 1 ∧
          c * (g * c * g⁻¹) ≠ t := by
      intro c hcN hct hc2
      let cN : ↥N := ⟨c, hcN⟩
      have hx2 : ((φ cN : ↥S) : Equiv.Perm (Fin 42)) * ((φ cN : ↥S) : Equiv.Perm (Fin 42)) =
          T0 := by
        have h1 : cN * cN = tN := Subtype.ext hc2
        have := congrArg (fun z : ↥N => ((φ z : ↥S) : Equiv.Perm (Fin 42))) h1
        simpa [T0] using this
      obtain ⟨g', hg'S, hg'T, h1, h2, h3⟩ := cq_conj hc₀ hTc (φ cN).2 (hcomm' cN hct) hx2
      let gN : ↥N := φ.symm ⟨g', hg'S⟩
      have hφg : φ gN = ⟨g', hg'S⟩ := φ.apply_symm_apply _
      refine ⟨(gN : G), gN.2, ?_, ?_, ?_, ?_⟩
      · have : gN * tN = tN * gN := by
          apply φ.injective
          apply Subtype.ext
          simpa [hφg, T0] using hg'T
        exact congrArg Subtype.val this
      · have : (cN * (gN * cN * gN⁻¹)) * (cN * (gN * cN * gN⁻¹)) = 1 := by
          apply φ.injective
          apply Subtype.ext
          simpa [hφg] using h1
        exact congrArg Subtype.val this
      · intro h
        have h4 : cN * (gN * cN * gN⁻¹) = 1 := Subtype.ext h
        apply h2
        have := congrArg (fun z : ↥N => ((φ z : ↥S) : Equiv.Perm (Fin 42))) h4
        simpa [hφg] using this
      · intro h
        have h4 : cN * (gN * cN * gN⁻¹) = tN := Subtype.ext h
        apply h3
        have := congrArg (fun z : ↥N => ((φ z : ↥S) : Equiv.Perm (Fin 42))) h4
        simpa [hφg, T0] using this
    have hO : ∀ m ∈ N, m * t = t * m → ∃ j : ℕ, orderOf m = 2 ^ j := by
      intro m hmN hmt
      let mN : ↥N := ⟨m, hmN⟩
      have hd : orderOf ((φ mN : ↥S) : Equiv.Perm (Fin 42)) ∣ 64 :=
        orderOf_dvd_sixtyfour hc₀ hTc (φ mN).2 (hcomm' mN hmt)
      have ho : orderOf m = orderOf ((φ mN : ↥S) : Equiv.Perm (Fin 42)) := by
        rw [Subgroup.orderOf_coe (φ mN), MulEquiv.orderOf_eq φ mN, Subgroup.orderOf_mk]
      rw [← ho] at hd
      obtain ⟨j, -, hj⟩ :=
        (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using hd : orderOf m ∣ 2 ^ 6)
      exact ⟨j, hj⟩
    obtain ⟨s, hsR, hs4, hss⟩ := exists_orderOf_eq_four_of_datum S0 eS ht hto hRC
    have hcore := fun (u : G) (huN : u ∈ N) (hut : u * t = t * u) =>
      commutator_mem_of_datum (N := N) hRC hRn huniq hW hO hsR huN hut
    set A : Equiv.Perm (Fin 42) := ((ι s : ↥R) : Equiv.Perm (Fin 42)) with hA
    have hAR : A ∈ R := (ι s).2
    have hAA : A * A = T0 := by
      have h1 : ι s * ι s = ι t := by rw [← map_mul, hss]
      have h2 : ι t = ⟨T0, S_le_R hT0S⟩ := hP2 tN
      rw [h2] at h1
      exact congrArg Subtype.val h1
    set rr : Equiv.Perm (Fin 42) := c₀⁻¹ * A * c₀ with hrr
    have hrrR : rr ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hc₀) hAR) hc₀
    have hrr2 : rr * rr = r₁ := by
      calc rr * rr = c₀⁻¹ * (A * A) * c₀ := by simp only [hrr]; group
        _ = r₁ := by rw [hAA, hTc]; group
    have hAeq : A = c₀ * rr * c₀⁻¹ := by simp only [hrr]; group
    obtain ⟨v, hvS, hvr, h1, h2⟩ := key_R hrrR hrr2
    have huS : c₀ * v * c₀⁻¹ ∈ S := conj_mem_S hc₀ hvS
    let uN : ↥N := φ.symm ⟨c₀ * v * c₀⁻¹, huS⟩
    have hφu : φ uN = ⟨c₀ * v * c₀⁻¹, huS⟩ := φ.apply_symm_apply _
    have hut : (uN : G) * t = t * (uN : G) := by
      have : uN * tN = tN * uN := by
        apply φ.injective
        apply Subtype.ext
        simp only [map_mul, hφu, Subgroup.coe_mul]
        rw [← hT0, hTc]
        calc c₀ * v * c₀⁻¹ * (c₀ * r₁ * c₀⁻¹) = c₀ * (v * r₁) * c₀⁻¹ := by group
          _ = c₀ * (r₁ * v) * c₀⁻¹ := by rw [hvr]
          _ = c₀ * r₁ * c₀⁻¹ * (c₀ * v * c₀⁻¹) := by group
      exact congrArg Subtype.val this
    have hcomm_key : ∀ x : Equiv.Perm (Fin 42),
        A * (c₀ * v * c₀⁻¹) * A⁻¹ * (c₀ * v * c₀⁻¹)⁻¹ = x →
          c₀ * (rr * v * rr⁻¹ * v⁻¹) * c₀⁻¹ = x := by
      intro x hx
      rw [← hx, hAeq]
      group
    have hι_comm : ι (s * (uN : G) * s⁻¹ * (uN : G)⁻¹) =
        ⟨A * (c₀ * v * c₀⁻¹) * A⁻¹ * (c₀ * v * c₀⁻¹)⁻¹, by
          exact R.mul_mem (R.mul_mem (R.mul_mem hAR (S_le_R huS)) (R.inv_mem hAR))
            (R.inv_mem (S_le_R huS))⟩ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hP2 uN, hφu]
      rfl
    rcases hcore (uN : G) uN.2 hut with h | h
    · have h3 : ι (s * (uN : G) * s⁻¹ * (uN : G)⁻¹) = 1 := by rw [h, map_one]
      rw [hι_comm] at h3
      have h3' : A * (c₀ * v * c₀⁻¹) * A⁻¹ * (c₀ * v * c₀⁻¹)⁻¹ = 1 := congrArg Subtype.val h3
      have h4 := hcomm_key 1 h3'
      have h5 : rr * v * rr⁻¹ * v⁻¹ = 1 := by
        have := congrArg (fun z => c₀⁻¹ * z * c₀) h4
        simpa [mul_assoc] using this
      apply h1
      calc rr * v = (rr * v * rr⁻¹ * v⁻¹) * (v * rr) := by group
        _ = v * rr := by rw [h5, one_mul]
    · have h3 : ι (s * (uN : G) * s⁻¹ * (uN : G)⁻¹) = ⟨T0, S_le_R hT0S⟩ := by
        rw [h]
        exact hP2 tN
      rw [hι_comm] at h3
      have h3' : A * (c₀ * v * c₀⁻¹) * A⁻¹ * (c₀ * v * c₀⁻¹)⁻¹ = T0 := congrArg Subtype.val h3
      have h4 := hcomm_key T0 h3'
      have h5 : rr * v * rr⁻¹ * v⁻¹ = r₁ := by
        have := congrArg (fun z => c₀⁻¹ * z * c₀) h4
        rw [hTc] at this
        simpa [mul_assoc] using this
      apply h2
      calc rr * v = (rr * v * rr⁻¹ * v⁻¹) * (v * rr) := by group
        _ = r₁ * v * rr := by rw [h5, mul_assoc]

theorem noDatum_of_lieModel_psl_three_two (F : Type) [Group F]
    (h : CFSG.Blueprint.LieModel F .PSL 3 2 2) : NoDatum F := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact noDatum_of_stated_psl_three_four F h
  all_goals exact absurd h (by norm_num)

end CFSG.ClassicalInvolution.Nobq

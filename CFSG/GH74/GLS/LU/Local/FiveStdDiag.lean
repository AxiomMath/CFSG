module

public import CFSG.GH74.GLS.LU.Local.FiveStdBase

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

namespace FiveStdDiag

theorem diagCheck_spec (h : diagCheck = true) {g : E} (hg : g ∈ Cs) (h5 : ordE g = 5)
    (hmin : ∀ k ∈ [2, 3, 4], codeE g ≤ codeE (powE g k))
    {Cent invols A : List E} (hCent : Cent = Cs.filter fun x => commE x g)
    (hinv : invols = Cent.filter fun τ => ordE τ == 2 && τ != zE)
    (hA : A = Cent.filter fun x => ordE x == 1 || ordE x == 5) :
    invols.isEmpty = true ∨ (A.length = 25 ∧ (∀ a ∈ A, inKK a = true) ∧ (∀ a ∈ A, ∀ b ∈ A, mulE a b ∈ A) ∧
      (∀ a ∈ A, ∀ c ∈ Cent, conjE c a ∈ A) ∧
      (∀ v ∈ Cs, conjE v g = invE g → normK1 v = true → ∀ a ∈ A, conjE v a = invE a) ∧
      ∀ τ ∈ invols, eqL Cent (prod2 A [oneE, zE, τ, mulE zE τ]) = true) := by
  unfold diagCheck at h
  simp only [List.all_eq_true] at h
  have hmem : g ∈ (Cs.filter fun x => ordE x == 5).filter
      fun g => [2, 3, 4].all fun k => codeE g ≤ codeE (powE g k) := by
    simp only [List.mem_filter, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨⟨hg, h5⟩, hmin⟩
  have := h g hmem
  subst hCent hinv hA
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, inL, List.contains_iff_mem,
    bne_iff_ne, ne_eq, Bool.not_eq_true'] at this
  rcases this with h1 | ⟨⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  · exact Or.inl h1
  · refine Or.inr ⟨h2, h3, h4, h5, fun v hv hcv hnv a ha => ?_, h7⟩
    rcases h6 v hv with (h | h) | h
    · exact absurd hcv h
    · rw [hnv] at h
      exact absurd h (by simp)
    · exact h a ha

theorem exists_pp_sub_gen {G : Type} [Group G] {x y : G} {n : ℕ} (hn : 0 < n) (hxy : x * y = y * x)
    (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ P : Subgroup G, ∀ h, h ∈ P ↔ ∃ i j : ℕ, h = x ^ i * y ^ j := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨{ carrier := {h | ∃ i j : ℕ, h = x ^ i * y ^ j}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ },
    fun h => Iff.rfl⟩
  · rintro a b ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact ⟨i + k, j + l, FiveStdBase.pp_mul_formula hxy i j k l⟩
  · exact ⟨0, 0, by simp⟩
  · rintro a ⟨i, j, rfl⟩
    refine ⟨m * i, m * j, ?_⟩
    apply inv_eq_of_mul_eq_one_right
    rw [FiveStdBase.pp_mul_formula hxy, show i + m * i = (m + 1) * i by ring, show j + m * j = (m + 1) * j by ring,
      pow_mul, pow_mul, hx, hy]
    simp

theorem sq_of_mem_sup {G : Type} [Group G] {x y : G} (hxx : x * x = 1) (hyy : y * y = 1) (hxy : x * y = y * x) :
    ∀ t ∈ zpowers x ⊔ zpowers y, t * t = 1 := by
  obtain ⟨P, hP⟩ := exists_pp_sub_gen (n := 2) (by norm_num) hxy (by rw [pow_two]; exact hxx)
    (by rw [pow_two]; exact hyy)
  have hxP : x ∈ P := (hP x).2 ⟨1, 0, by simp⟩
  have hyP : y ∈ P := (hP y).2 ⟨0, 1, by simp⟩
  intro t ht
  have ht' : t ∈ P := (sup_le (Subgroup.zpowers_le.2 hxP) (Subgroup.zpowers_le.2 hyP) : zpowers x ⊔ zpowers y ≤ P) ht
  obtain ⟨i, j, rfl⟩ := (hP t).1 ht'
  rw [FiveStdBase.pp_mul_formula hxy, ← two_mul, ← two_mul, pow_mul, pow_mul, show x ^ 2 = 1 by rw [pow_two]; exact hxx,
    show y ^ 2 = 1 by rw [pow_two]; exact hyy]
  simp

theorem exists_sub_of_mul {G : Type} [Group G] [Finite G] {ι : E → G} (hM : Model ι) {L : List E} (hL : V L)
    (h1 : oneE ∈ L) (hm : ∀ x ∈ L, ∀ y ∈ L, mulE x y ∈ L) : ∃ H : Subgroup G, (H : Set G) = S ι L := by
  have hmul : ∀ a ∈ S ι L, ∀ b ∈ S ι L, a * b ∈ S ι L := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := mem_S.1 ha
    obtain ⟨y, hy, rfl⟩ := mem_S.1 hb
    exact mem_S.2 ⟨mulE x y, hm x hx y hy, hM.map_mul _ _ (hL x hx) (hL y hy)⟩
  have hone : (1 : G) ∈ S ι L := mem_S.2 ⟨oneE, h1, hM.map_one⟩
  have hpow : ∀ g ∈ S ι L, ∀ n : ℕ, g ^ n ∈ S ι L := by
    intro g hg n
    induction n with
    | zero => rw [pow_zero]; exact hone
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hg
  refine ⟨{ carrier := S ι L, mul_mem' := fun ha hb => hmul _ ha _ hb, one_mem' := hone, inv_mem' := ?_ }, rfl⟩
  intro g hg
  have hpos : 0 < orderOf g := orderOf_pos g
  have : g⁻¹ = g ^ (orderOf g - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [this]
  exact hpow g hg _

end FiveStdDiag

namespace FiveStdSetting

open FiveStdBase FiveStdDiag

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

private theorem diag_gen (Z : Subgroup G) (hZC : Z ≤ Cz st.z) (hZ5 : Nat.card ↥Z = 5) :
    ∃ g1 : E, validE g1 = true ∧ st.ι g1 ∈ Z ∧ ordE g1 = 5 ∧ zpowers (st.ι g1) = Z ∧
      ∀ k ∈ [2, 3, 4], codeE g1 ≤ codeE (powE g1 k) := by
  have hnt : Nontrivial ↥Z := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨⟨g0, hg0Z⟩, hg0ne⟩ := exists_ne (1 : ↥Z)
  have hg0ne' : g0 ≠ 1 := fun h => hg0ne (Subtype.ext h)
  obtain ⟨x0, hx0v, rfl⟩ := st.mem_C_iff.1 (hZC hg0Z)
  have hex : ∃ n : ℕ, ∃ x : E, validE x = true ∧ st.ι x ∈ Z ∧ st.ι x ≠ 1 ∧ codeE x = n :=
    ⟨_, x0, hx0v, hg0Z, hg0ne', rfl⟩
  classical
  obtain ⟨g1, hg1v, hg1Z, hg1ne, hg1c⟩ := Nat.find_spec hex
  have hmin : ∀ x : E, validE x = true → st.ι x ∈ Z → st.ι x ≠ 1 → codeE g1 ≤ codeE x := by
    intro x hxv hxZ hxne
    have := Nat.find_min' hex ⟨x, hxv, hxZ, hxne, rfl⟩
    omega
  have hord : orderOf (st.ι g1) = 5 := by
    have hdvd : orderOf (st.ι g1) ∣ 5 := hZ5 ▸ Subgroup.orderOf_dvd_natCard Z hg1Z
    rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hg1ne
    · exact h
  refine ⟨g1, hg1v, hg1Z, st.model.ordE_of_orderOf hg1v hord (by norm_num) (by norm_num), ?_, ?_⟩
  · exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hg1Z) (by rw [hZ5, Nat.card_zpowers, hord])
  · intro k hk
    have hk' : 0 < k ∧ k < 5 := by simp at hk; omega
    refine hmin _ (st.model.valid_powE hg1v k) ?_ ?_
    · rw [st.model.map_powE hg1v]
      exact Subgroup.pow_mem Z hg1Z k
    · rw [st.model.map_powE hg1v]
      exact pow_ne_one_of_lt_orderOf (by omega) (by omega)


theorem diag_sound (hb : baseCheck = true) (hd : diagCheck = true) :
    ∀ τ : G, τ ∈ Cz st.z → τ * τ = 1 → τ ≠ 1 → τ ≠ st.z → ∀ Z : Subgroup G, Z ≤ Cz st.z →
      Nat.card ↥Z = 5 → (∀ s ∈ Z, τ * s = s * τ) →
      ∃ A : Subgroup G, A ≤ st.K₁ ⊔ st.K₂ ∧ IsElemAb 5 A ∧ Nat.card ↥A = 25 ∧
        A ⊓ (zpowers st.z ⊔ zpowers τ) = ⊥ ∧
        centralizer ((Z : Subgroup G) : Set G) ⊓ Cz st.z = A ⊔ (zpowers st.z ⊔ zpowers τ) ∧
        (∀ g ∈ centralizer ((Z : Subgroup G) : Set G) ⊓ Cz st.z, ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
        ∀ v ∈ Cz st.z, v ∈ normalizer (st.K₁ : Set G) → (∀ s ∈ Z, v * s * v⁻¹ = s⁻¹) →
          ∀ a ∈ A, v * a * v⁻¹ = a⁻¹ := by
  intro τ hτC hττ hτ1 hτz Z hZC hZ5 hτZ
  obtain ⟨g1, hg1v, hg1Z, hg1o, hZeq, hg1min⟩ := st.diag_gen Z hZC hZ5
  obtain ⟨τE, hτEv, hτE⟩ := st.mem_C_iff.1 hτC
  subst hτE
  have hM := st.model
  obtain ⟨-, hV1, -, hVS0, -, -, -, -, hzS, -⟩ := baseCheck_spec hb
  have hzv : validE zE = true := hVS0 _ hzS
  obtain ⟨Cent, hCent⟩ : ∃ Cent : List E, Cent = Cs.filter fun x => commE x g1 := ⟨_, rfl⟩
  obtain ⟨invols, hinv⟩ : ∃ invols : List E, invols = Cent.filter fun τ => ordE τ == 2 && τ != zE := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : List E, A = Cent.filter fun x => ordE x == 1 || ordE x == 5 := ⟨_, rfl⟩
  have hmemCent : ∀ x, x ∈ Cent ↔ validE x = true ∧ commE x g1 = true := by
    intro x
    rw [hCent, List.mem_filter, mem_Cs_iff]
  have hmemA : ∀ x, x ∈ A ↔ x ∈ Cent ∧ (ordE x = 1 ∨ ordE x = 5) := by
    intro x
    rw [hA, List.mem_filter]
    simp only [Bool.or_eq_true, beq_iff_eq]
  have hmeminv : ∀ x, x ∈ invols ↔ x ∈ Cent ∧ ordE x = 2 ∧ x ≠ zE := by
    intro x
    rw [hinv, List.mem_filter]
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  have hVA : V A := fun x hx => ((hmemCent x).1 ((hmemA x).1 hx).1).1
  have hVCent : V Cent := fun x hx => ((hmemCent x).1 hx).1
  have hcommZ : ∀ x : E, validE x = true →
      (commE x g1 = true ↔ st.ι x ∈ centralizer ((Z : Subgroup G) : Set G)) := by
    intro x hxv
    rw [hM.commE_iff hxv hg1v, Subgroup.mem_centralizer_iff]
    constructor
    · intro h s hs
      rw [← hZeq] at hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
      exact (Commute.zpow_left (show Commute (st.ι g1) (st.ι x) from h.symm) k).eq
    · intro h
      exact (h _ hg1Z).symm
  have hCentG : ∀ x : E, validE x = true →
      (x ∈ Cent ↔ st.ι x ∈ centralizer ((Z : Subgroup G) : Set G) ⊓ Cz st.z) := by
    intro x hxv
    rw [hmemCent, Subgroup.mem_inf, ← hcommZ x hxv]
    exact ⟨fun h => ⟨h.2, st.ι_mem_C hxv⟩, fun h => ⟨hxv, h.1⟩⟩
  have hτo : ordE τE = 2 := by
    have : orderOf (st.ι τE) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hττ) hτ1
    exact hM.ordE_of_orderOf hτEv this (by norm_num) (by norm_num)
  have hτne : τE ≠ zE := fun h => hτz (by rw [h])
  have hτcomm : commE τE g1 = true := (hM.commE_iff hτEv hg1v).2 (hτZ _ hg1Z)
  have hτinv : τE ∈ invols := (hmeminv _).2 ⟨(hmemCent _).2 ⟨hτEv, hτcomm⟩, hτo, hτne⟩
  rcases diagCheck_spec hd ((mem_Cs_iff g1).2 hg1v) hg1o hg1min hCent hinv hA with hempty |
    ⟨hlen, hKK, hmulA, hconjA, hinvA, heqA⟩
  · exfalso
    rw [List.isEmpty_iff] at hempty
    rw [hempty] at hτinv
    simp at hτinv
  have h1A : oneE ∈ A := by
    refine (hmemA _).2 ⟨(hmemCent _).2 ⟨hM.valid_one, ?_⟩, Or.inl ?_⟩
    · rw [hM.commE_iff hM.valid_one hg1v, hM.map_one]
      simp
    · exact hM.ordE_of_orderOf hM.valid_one (by rw [hM.map_one]; exact orderOf_one) le_rfl (by norm_num)
  obtain ⟨AG, hAG⟩ := exists_sub_of_mul hM hVA h1A hmulA
  have hmemAG : ∀ a, a ∈ AG ↔ ∃ x ∈ A, st.ι x = a := fun a => by
    rw [← SetLike.mem_coe, hAG]
    exact mem_S
  have hAcard : Nat.card ↥AG = 25 := by
    have hnd : A.Nodup := by
      rw [hA, hCent]
      exact ((nodup_Cs hb).filter _).filter _
    rw [natCard_eq_of_coe AG hAG, natCard_S hM hVA hnd, hlen]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcomm : IsMulCommutative ↥AG :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (by rw [hAcard]; norm_num)
  have hpow5 : ∀ a ∈ AG, a ^ 5 = 1 := by
    intro a ha
    obtain ⟨x, hxA, rfl⟩ := (hmemAG a).1 ha
    have hxv := hVA x hxA
    rcases ((hmemA x).1 hxA).2 with h | h
    · rw [orderOf_eq_one_iff.1 (hM.orderOf_of_ordE hxv h (by norm_num))]
      simp
    · have := hM.orderOf_of_ordE hxv h (by norm_num)
      calc st.ι x ^ 5 = st.ι x ^ orderOf (st.ι x) := by rw [this]
        _ = 1 := pow_orderOf_eq_one _
  have hzz : st.z * st.z = 1 := by
    have : mulE zE zE = oneE := by rfl
    rw [← hM.map_mul _ _ hzv hzv, this, hM.map_one]
  have hzτ : st.z * st.ι τE = st.ι τE * st.z := Subgroup.mem_centralizer_singleton_iff.1 hτC |>.symm
  have hVfour : V [oneE, zE, τE, mulE zE τE] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hM.valid_one
    · exact hzv
    · exact hτEv
    · exact hM.valid_mul _ _ hzv hτEv
  refine ⟨AG, ?_, ⟨fun a ha b hb => setLike_mul_comm ha hb, hpow5⟩, hAcard,
    ?_, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hxA, rfl⟩ := (hmemAG a).1 ha
    obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.1 ((st.hKK x (hVA x hxA)).1 (hKK x hxA))
    rw [← huw]
    exact Subgroup.mul_mem_sup hu hw
  · rw [eq_bot_iff]
    intro a ha
    have ha1 := hpow5 a ha.1
    have ha2 := sq_of_mem_sup hzz hττ hzτ a ha.2
    rw [Subgroup.mem_bot]
    have h4 : a ^ 5 = (a * a) * (a * a) * a := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h4, ha2] at ha1
    simpa using ha1
  · apply le_antisymm
    · intro g hg
      obtain ⟨cE, hcEv, rfl⟩ := st.mem_C_iff.1 hg.2
      have hcent : cE ∈ Cent := (hCentG cE hcEv).2 hg
      have hSeq := (hM.eqL_iff hVCent (hM.V_mulLL hVA hVfour)).1 (heqA τE hτinv)
      have hmem : st.ι cE ∈ S st.ι (mulLL A [oneE, zE, τE, mulE zE τE]) := by
        rw [← hSeq]
        exact mem_S.2 ⟨cE, hcent, rfl⟩
      rw [hM.S_mulLL hVA hVfour] at hmem
      obtain ⟨a, ha, t, ht, hat⟩ := Set.mem_mul.1 hmem
      obtain ⟨tE, htE, rfl⟩ := mem_S.1 ht
      rw [← hat]
      refine Subgroup.mul_mem_sup (by rw [← SetLike.mem_coe, hAG]; exact ha) ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htE
      rcases htE with rfl | rfl | rfl | rfl
      · rw [hM.map_one]
        exact Subgroup.one_mem _
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · rw [hM.map_mul _ _ hzv hτEv]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · refine sup_le ?_ (sup_le ?_ ?_)
      · intro a ha
        obtain ⟨x, hxA, rfl⟩ := (hmemAG a).1 ha
        exact (hCentG x (hVA x hxA)).1 ((hmemA x).1 hxA).1
      · rw [Subgroup.zpowers_le, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
        refine ⟨fun s hs => ?_, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.1 (hZC hs)
      · rw [Subgroup.zpowers_le, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
        exact ⟨fun s hs => (hτZ s hs).symm, hτC⟩
  · intro g hg a ha
    obtain ⟨cE, hcEv, rfl⟩ := st.mem_C_iff.1 hg.2
    obtain ⟨x, hxA, rfl⟩ := (hmemAG a).1 ha
    have hcent : cE ∈ Cent := (hCentG cE hcEv).2 hg
    exact (hmemAG _).2 ⟨conjE cE x, hconjA x hxA cE hcent, hM.map_conjE hcEv (hVA x hxA)⟩
  · intro v hvC hvN hvZ a ha
    obtain ⟨vE, hvEv, rfl⟩ := st.mem_C_iff.1 hvC
    obtain ⟨x, hxA, rfl⟩ := (hmemAG a).1 ha
    have hvg : conjE vE g1 = invE g1 := by
      apply hM.inj _ _ (hM.valid_conjE hvEv hg1v) (hM.valid_inv _ hg1v)
      rw [hM.map_conjE hvEv hg1v, hM.map_inv _ hg1v]
      exact hvZ _ hg1Z
    have hnorm : normK1 vE = true := by
      unfold normK1
      rw [List.all_eq_true]
      intro y hy
      have hyv : validE y = true := hV1 y hy
      have hyK : st.ι y ∈ st.K₁ := by
        have : st.ι y ∈ ((st.K₁ : Subgroup G) : Set G) := by
          rw [st.hK₁]
          exact mem_S.2 ⟨y, hy, rfl⟩
        exact this
      have h1 : st.ι vE * st.ι y * (st.ι vE)⁻¹ ∈ st.K₁ := (Subgroup.mem_normalizer_iff.1 hvN (st.ι y)).1 hyK
      rw [← hM.map_conjE hvEv hyv] at h1
      have h2 : st.ι (conjE vE y) ∈ S st.ι K1l := by
        rw [← st.hK₁]
        exact h1
      exact (hM.inL_iff hV1 (hM.valid_conjE hvEv hyv)).2 h2
    have hx := hinvA vE ((mem_Cs_iff vE).2 hvEv) hvg hnorm x hxA
    rw [← hM.map_conjE hvEv (hVA x hxA), hx, hM.map_inv _ (hVA x hxA)]

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five

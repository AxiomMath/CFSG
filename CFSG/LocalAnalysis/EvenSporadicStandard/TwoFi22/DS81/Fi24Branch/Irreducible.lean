module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Core3

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

theorem InvUnder.inf {M A B : Subgroup G} (hA : InvUnder M A) (hB : InvUnder M B) :
    InvUnder M (A ⊓ B) := by
  intro n hn x hx
  exact ⟨hA n hn x hx.1, hB n hn x hx.2⟩

theorem InvUnder.sup {M A B : Subgroup G} (hA : InvUnder M A) (hB : InvUnder M B) :
    InvUnder M (A ⊔ B) := by
  intro n hn x hx
  have hmapA : A.map (MulAut.conj n : G →* G) ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    simpa using hA n hn a ha
  have hmapB : B.map (MulAut.conj n : G →* G) ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    simpa using hB n hn b hb
  have hmap : (A ⊔ B).map (MulAut.conj n : G →* G) ≤ A ⊔ B := by
    rw [Subgroup.map_sup]
    exact sup_le (hmapA.trans le_sup_left) (hmapB.trans le_sup_right)
  have hmem := hmap (Subgroup.mem_map_of_mem (MulAut.conj n : G →* G) hx)
  simpa using hmem

theorem invUnder_CNz_E (c : Core3 E t z) : InvUnder (CNz E z) E := by
  intro n hn e he
  exact (mem_normalizer_iff.mp (mem_CNz.mp hn).1 e).mp he

theorem invUnder_CNz_E7 (c : Core3 E t z) : InvUnder (CNz E z) (Rg t z ⊓ E) :=
  InvUnder.inf c.rnorm (invUnder_CNz_E c)

@[expose] def RIrred (E : Subgroup G) (t z : G) : Prop :=
  ∀ U : Subgroup G, zpowers z ≤ U → U ≤ Rg t z → InvUnder (CNz E z) U → InvUnder (Jg t z) U →
    U = zpowers z ∨ U = Rg t z

theorem rIrred (c : Core3 E t z) : RIrred E t z := by
  intro U hzU hUR hUCN hUJ
  have hc1 : Core1 E t z := c.toCore2.toCore1
  have hzE : z ∈ E := c.isZ.1
  have hzR : z ∈ Rg t z := c.jr.V_le_R z_mem_Vtz
  have hzE7 : z ∈ Rg t z ⊓ E := ⟨hzR, hzE⟩
  have hzU' : z ∈ U := hzU (Subgroup.mem_zpowers z)
  have hcard_E7 : Nat.card ↥(Rg t z ⊓ E) = 2 ^ 7 := c.rp.card_RE
  have hEinv : InvUnder (CNz E z) E := invUnder_CNz_E c
  have hE7inv : InvUnder (CNz E z) (Rg t z ⊓ E) := invUnder_CNz_E7 c
  have hWinv : InvUnder (CNz E z) (U ⊓ (Rg t z ⊓ E)) := InvUnder.inf hUCN hE7inv
  have hW_le_E : U ⊓ (Rg t z ⊓ E) ≤ E := inf_le_right.trans inf_le_right
  have hlat := c.cocode.lattice (U ⊓ (Rg t z ⊓ E)) hW_le_E hWinv
  have hzW : z ∈ U ⊓ (Rg t z ⊓ E) := ⟨hzU', hzE7⟩
  have hW_ne_bot : U ⊓ (Rg t z ⊓ E) ≠ ⊥ := by
    intro h
    rw [h] at hzW
    exact c.klein.z_ne (Subgroup.mem_bot.mp hzW)
  have hW_ne_E : U ⊓ (Rg t z ⊓ E) ≠ E := by
    intro h
    have hle : Nat.card ↥(U ⊓ (Rg t z ⊓ E)) ≤ Nat.card ↥(Rg t z ⊓ E) :=
      Subgroup.card_le_of_le inf_le_right
    rw [h, c.m24.card_E, hcard_E7] at hle
    norm_num at hle
  have hcase_W : U ⊓ (Rg t z ⊓ E) = zpowers z ∨ U ⊓ (Rg t z ⊓ E) = Rg t z ⊓ E := by
    rcases hlat with hbot | hzp | hcard | hE
    · exact absurd hbot hW_ne_bot
    · exact Or.inl hzp
    · right
      exact Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard, hcard_E7])
    · exact absurd hE hW_ne_E
  have hUE_le_P : U ⊔ E ≤ Pg E z := sup_le (hUR.trans c.rp.R_le_P) c.rp.E_le_P
  have hUEinv : InvUnder (CNz E z) (U ⊔ E) := InvUnder.sup hUCN hEinv
  have hcase_UE : U ⊔ E = E ∨ U ⊔ E = Pg E z :=
    c.cocode.P_irred (U ⊔ E) le_sup_right hUE_le_P hUEinv
  have hU_le_Nrm : U ≤ Nrm E :=
    hUR.trans (c.rp.R_le_P.trans ((Pg_le_CNz E z).trans (CNz_le_Nrm E z)))
  rcases hcase_W with hWz | hWE7
  · rcases hcase_UE with hUE | hUE
    ·
      left
      have hU_le_E7 : U ≤ Rg t z ⊓ E := le_inf hUR (hUE ▸ le_sup_left)
      exact (inf_eq_left.mpr hU_le_E7).symm.trans hWz
    ·
      exfalso
      have hE_le_CN : E ≤ CNz E z := by
        intro e he
        rw [mem_CNz]
        exact ⟨Subgroup.le_normalizer he, E_comm hc1 e he z hzE⟩
      have hE_le_J : E ≤ Jg t z := c.rp.E_le_P.trans c.rp.P_le_J
      have hcomm_mem : ∀ u ∈ U, ∀ e ∈ E, ⁅u, e⁆ ∈ zpowers z := by
        intro u hu e he
        have huR : u ∈ Rg t z := hUR hu
        have hmemE : ⁅u, e⁆ ∈ E := by
          rw [commutatorElement_def]
          exact E.mul_mem ((mem_normalizer_iff.mp (hU_le_Nrm hu) e).mp he) (E.inv_mem he)
        have hmemU : ⁅u, e⁆ ∈ U := by
          have hconj : e * u⁻¹ * e⁻¹ ∈ U := hUCN e (hE_le_CN he) u⁻¹ (U.inv_mem hu)
          rw [commutatorElement_def]
          simpa only [mul_assoc] using U.mul_mem hu hconj
        have hmemR : ⁅u, e⁆ ∈ Rg t z := by
          have hconj : e * u⁻¹ * e⁻¹ ∈ Rg t z :=
            c.jr.R_normal e (hE_le_J he) u⁻¹ ((Rg t z).inv_mem huR)
          rw [commutatorElement_def]
          simpa only [mul_assoc] using (Rg t z).mul_mem huR hconj
        have hmemW : ⁅u, e⁆ ∈ U ⊓ (Rg t z ⊓ E) := ⟨hmemU, hmemR, hmemE⟩
        rw [hWz] at hmemW
        exact hmemW
      have hcommEP_le : ⁅E, Pg E z⁆ ≤ zpowers z := by
        rw [Subgroup.commutator_le]
        intro e he p hp
        have hp' : p ∈ U ⊔ E := by rw [hUE]; exact hp
        obtain ⟨u, hu, e', he', hpe⟩ := (mem_sup_of_le_normalizer hU_le_Nrm).mp hp'
        rw [← hpe, commutatorElement_mul_right_eq_mul_conj]
        have h1 : ⁅e, e'⁆ = 1 :=
          commutatorElement_eq_one_iff_mul_comm.mpr (E_comm hc1 e he e' he')
        rw [h1]
        have hsimp : ⁅e, u⁆ * u * 1 * u⁻¹ = ⁅e, u⁆ := by group
        rw [hsimp]
        have h2 : ⁅e, u⁆ = ⁅u, e⁆⁻¹ := (commutatorElement_inv (g₁ := u) (g₂ := e)).symm
        rw [h2]
        exact (zpowers z).inv_mem (hcomm_mem u hu e he)
      have hcard_z : Nat.card ↥(zpowers z) = 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_eq_prime c.klein.z_sq c.klein.z_ne
      have hH_or : ⁅E, Pg E z⁆ = ⊥ ∨ ⁅E, Pg E z⁆ = zpowers z := by
        have hle2 : Nat.card ↥⁅E, Pg E z⁆ ≤ 2 :=
          (Subgroup.card_le_of_le hcommEP_le).trans (le_of_eq hcard_z)
        have hpos : 0 < Nat.card ↥⁅E, Pg E z⁆ := Nat.card_pos (α := ↥⁅E, Pg E z⁆)
        have hcases : Nat.card ↥⁅E, Pg E z⁆ = 1 ∨ Nat.card ↥⁅E, Pg E z⁆ = 2 := by omega
        rcases hcases with h1 | h2
        · left; exact Subgroup.eq_bot_of_card_eq _ h1
        · right
          exact Subgroup.eq_of_le_of_card_ge hcommEP_le (by simp [hcard_z, h2])
      rcases hH_or with hbot | htop
      · have hPE : Pg E z ≤ E := by
          have hcent : E ≤ centralizer (Pg E z : Set G) :=
            Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
          have hcent' : Pg E z ≤ centralizer (E : Set G) :=
            Subgroup.le_centralizer_iff.mp hcent
          rwa [c.m24.centralizer_eq] at hcent'
        have hcardle : Nat.card ↥(Pg E z) ≤ Nat.card ↥E := Subgroup.card_le_of_le hPE
        rw [c.cocode.card_P, c.m24.card_E] at hcardle
        norm_num at hcardle
      · exact c.cocode.comm_ne htop
  · rcases hcase_UE with hUE | hUE
    ·
      exfalso
      have hU_eq : U = Rg t z ⊓ E :=
        le_antisymm (le_inf hUR (hUE ▸ le_sup_left)) (hWE7 ▸ inf_le_left)
      have hE7J : InvUnder (Jg t z) (Rg t z ⊓ E) := hU_eq ▸ hUJ
      obtain ⟨Y, hYK, _hYperf, _hYidx, hlatK⟩ := c.kdata.perfect
      have hYleJ : Y ≤ Jg t z := hYK.trans (Kg_le_Jg t z)
      have hYinv : InvUnder Y (Rg t z ⊓ E) := fun y hy => hE7J y (hYleJ hy)
      have hV_le_E : Vtz t z ≤ E := by
        rw [Vtz]
        exact (Subgroup.closure_le E).2 (by
          rintro x (rfl | rfl)
          · exact c.m24.t_mem
          · exact hzE)
      have hV_le_E7 : Vtz t z ≤ Rg t z ⊓ E := le_inf c.jr.V_le_R hV_le_E
      have hE7_le_OK : Rg t z ⊓ E ≤ OKg t z := by
        rw [← c.jr.R_inf_K]
        exact le_inf inf_le_left (inf_le_right.trans (E_le_K hc1))
      have hcards := hlatK (Rg t z ⊓ E) hV_le_E7 hE7_le_OK hYinv
      rw [hcard_E7] at hcards
      rcases hcards with h | h | h | h <;> exact absurd h (by norm_num)
    ·
      right
      have hUinfE : U ⊓ E = Rg t z ⊓ E := by
        apply le_antisymm
        · exact le_inf (inf_le_left.trans hUR) inf_le_right
        · exact le_inf (hWE7 ▸ inf_le_left) inf_le_right
      have hcardU : Nat.card ↥U = 2 ^ 13 := by
        have h := card_sup_mul_card_inf_of_le_normalizer (A := E) (B := U) hU_le_Nrm
        rw [sup_comm, hUE, inf_comm, hUinfE, c.m24.card_E, c.cocode.card_P, hcard_E7] at h
        have h' : (2 : ℕ) ^ 11 * 2 ^ 13 = 2 ^ 11 * Nat.card ↥U := by
          rw [← h]; norm_num
        exact (Nat.eq_of_mul_eq_mul_left (by norm_num) h').symm
      exact Subgroup.eq_of_le_of_card_ge hUR (by rw [c.jr.card_R, hcardU])

theorem exists_conj_z_mem_R (c : Core3 E t z) :
    ∃ g : G, g * z * g⁻¹ ∈ Rg t z ∧ g * z * g⁻¹ ≠ z := by
  have hE7inv : InvUnder (CNz E z) (Rg t z ⊓ E) := invUnder_CNz_E7 c
  obtain ⟨z', hz', hz'ne, hz'nc⟩ :=
    c.cocode.exists_sextet (Rg t z ⊓ E) inf_le_right hE7inv c.rp.card_RE
  simp only [normClass, Set.mem_setOf_eq] at hz'nc
  obtain ⟨n, _hn, hnz⟩ := hz'nc
  exact ⟨n, by rw [hnz]; exact hz'.1, by rw [hnz]; exact hz'ne⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

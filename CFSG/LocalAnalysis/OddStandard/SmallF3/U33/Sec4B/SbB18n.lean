module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18d
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbS18c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma conj_commutator_mem {A B : Subgroup G} {g : G}
    (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) :
    ∀ n ∈ ⁅A, B⁆, g * n * g⁻¹ ∈ ⁅A, B⁆ := by
  have hA' : A.map (MulAut.conj g : G →* G) ≤ A := by
    rintro x ⟨a, ha, rfl⟩
    simpa using hA a ha
  have hB' : B.map (MulAut.conj g : G →* G) ≤ B := by
    rintro x ⟨b, hb, rfl⟩
    simpa using hB b hb
  intro n hn
  have hmem : (MulAut.conj g : G →* G) n ∈
      (⁅A, B⁆ : Subgroup G).map (MulAut.conj g : G →* G) :=
    Subgroup.mem_map_of_mem _ hn
  rw [Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hA' hB' hmem

private lemma conj_zpowers_mem {g h : G} (hh : g * h * g⁻¹ = h⁻¹) :
    ∀ b ∈ zpowers h, g * b * g⁻¹ ∈ zpowers h := by
  have hle : (zpowers h).map (MulAut.conj g : G →* G) ≤ zpowers h := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (MulAut.conj g h) ≤ Subgroup.zpowers h
    rw [MulAut.conj_apply, hh]
    exact Subgroup.zpowers_le.mpr (Subgroup.inv_mem (Subgroup.zpowers h) (Subgroup.mem_zpowers h))
  intro b hb
  exact hle (Subgroup.mem_map_of_mem _ hb)

private lemma zpowers_t_normalizes_C (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ k ∈ zpowers t, ∀ h ∈ ctxCY t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxCY t tau x₁ x₂ rho := by
  have htK : t ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).1
  have ht_norm : t ∈ Subgroup.normalizer ((ctxCY t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype (fun n hn => (l18_C_normal hc).2 t htK n hn)
  intro k hk h hh
  have hk' : k ∈ Subgroup.normalizer ((ctxCY t tau x₁ x₂ rho : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr ht_norm hk
  exact (Subgroup.mem_normalizer_iff.mp hk' h).mp hh

private lemma zpowers_t_comm_zpowers_rho (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ∀ s ∈ zpowers t, ∀ g ∈ zpowers rho, s * g = g * s := by
  have htcent : t ∈ centralizer ({rho} : Set G) := by
    have hmem : t ∈ ctxK t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := by
      rw [hc.CK_rho]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    exact (Subgroup.mem_inf.mp hmem).2
  have hrho_t : rho * t = t * rho := (Subgroup.mem_centralizer_iff.mp htcent) rho (by simp)
  have hrho_cent_t : rho ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact hrho_t.symm
  have hzp_le : zpowers rho ≤ centralizer ({t} : Set G) := Subgroup.zpowers_le.mpr hrho_cent_t
  have ht_cent_zp : t ∈ centralizer ((zpowers rho : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_centralizer_iff.mp (hzp_le hh)) t rfl).symm
  have hzp_le2 : zpowers t ≤ centralizer ((zpowers rho : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr ht_cent_zp
  intro s hs g hg
  exact ((Subgroup.mem_centralizer_iff.mp (hzp_le2 hs)) g hg).symm

theorem l18_Xi_normal (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    NormalIn (ctxXi t tau x₁ x₂ rho) (ctxK t tau x₁ x₂ rho) := by
  refine ⟨(l18_Xi_le_OK hc).trans (l18_OK_normal.1), ?_⟩
  have hK : ctxK t tau x₁ x₂ rho ≤
      Subgroup.normalizer ((ctxXi t tau x₁ x₂ rho : Subgroup G) : Set G) := by
    rw [hc.K_eq]
    refine sup_le ?_ ?_
    · exact Subgroup.normalizer_commutator_ge_left (ctxOK t tau x₁ x₂ rho) (zpowers rho)
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx
      · rw [hx]
        exact (Subgroup.normalizer_commutator_ge_right
          (ctxOK t tau x₁ x₂ rho) (zpowers rho)) (Subgroup.mem_zpowers rho)
      · rw [hx]
        have hOKn : ∀ a ∈ ctxOK t tau x₁ x₂ rho,
            lam * a * lam⁻¹ ∈ ctxOK t tau x₁ x₂ rho :=
          fun a ha => l18_OK_normal.2 lam (l17_mem_K hc).2.2.2.1 a ha
        have hZn : ∀ b ∈ zpowers rho, lam * b * lam⁻¹ ∈ zpowers rho :=
          conj_zpowers_mem hc.lam_rho
        exact Subgroup.mem_normalizer_fintype
          (fun n hn => conj_commutator_mem hOKn hZn n hn)
  intro g hg m hm
  exact (Subgroup.mem_normalizer_iff.mp (hK hg) m).mp hm

theorem l18_OK_eq (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxOK t tau x₁ x₂ rho = ctxCY t tau x₁ x₂ rho ⊔ zpowers t := by
  have hc13 := hc.toCtx13
  have ht2pow : t ^ 2 = 1 := (ctx13_relations hc13).1
  have ht1 : t ≠ 1 := (ctx13_relations hc13).2.1
  have ht_order : orderOf t = 2 := orderOf_eq_prime (p := 2) ht2pow ht1
  have hle : ctxCY t tau x₁ x₂ rho ⊔ zpowers t ≤ ctxOK t tau x₁ x₂ rho := by
    refine sup_le (l18_C_le_OK hc13) ?_
    exact Subgroup.zpowers_le.mpr (l18_tau_om_mem_OK hc13).1
  have ht_notC : t ∉ ctxCY t tau x₁ x₂ rho := (l18_not_mem_C hc13).1
  have hHK : ctxCY t tau x₁ x₂ rho ⊓ zpowers t = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxC, hxzp⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_zpowers_iff] at hxzp
    obtain ⟨k, rfl⟩ := hxzp
    have hk'' : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by
      simpa using Int.emod_two_eq_zero_or_one k
    rcases hk'' with hk | hk
    · rw [zpow_eq_zpow_emod' (x := t) (n := 2) k ht2pow, hk]
      simp
    · rw [zpow_eq_zpow_emod' (x := t) (n := 2) k ht2pow, hk] at hxC
      simp only [zpow_one] at hxC
      exact absurd hxC ht_notC
  have hcardsup : Nat.card ↥(ctxCY t tau x₁ x₂ rho ⊔ zpowers t) = 2 ^ 11 := by
    rw [card_sup_eq_mul (zpowers_t_normalizes_C hc13) hHK, hc.card_C,
      Nat.card_zpowers t, ht_order]
    norm_num
  have hOKdvd : Nat.card ↥(ctxOK t tau x₁ x₂ rho) ∣ 2 ^ 12 := by
    rw [← l18_card_sylow hc.toCtx18S]
    exact Subgroup.card_dvd_of_le (l18_OK_le_sylow hc.toCtx18S)
  obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hOKdvd
  have hOKne : Nat.card ↥(ctxOK t tau x₁ x₂ rho) ≠ 2 ^ 12 := by
    intro hcard
    have hEq : ctxOK t tau x₁ x₂ rho = 𝒮 :=
      Subgroup.eq_of_le_of_card_ge (l18_OK_le_sylow hc.toCtx18S)
        (by rw [hcard, l18_card_sylow hc.toCtx18S])
    exact l18_lam_not_mem_OK hc13 (hEq ▸ (l18_T_le_sylow hc.toCtx18S).2.2.2)
  have hjne : j ≠ 12 := by
    intro hj12
    exact hOKne (by rw [hj, hj12])
  have hj11 : j ≤ 11 := by omega
  have hOKle : Nat.card ↥(ctxOK t tau x₁ x₂ rho) ≤ 2 ^ 11 := by
    rw [hj]
    exact pow_le_pow_right' (a := 2) (by norm_num) hj11
  refine le_antisymm ?_ hle
  exact le_of_eq (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardsup]; exact hOKle)).symm

theorem l18_Xi_le_comm_C (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ≤ ⁅ctxCY t tau x₁ x₂ rho, zpowers rho⁆ := by
  have hc13 := hc.toCtx13
  refine Subgroup.commutator_le.mpr ?_
  intro x hxOK g hg
  have hx : x ∈ ctxCY t tau x₁ x₂ rho ⊔ zpowers t := by
    rw [← l18_OK_eq hc]
    exact hxOK
  obtain ⟨c, hcC, s, hs, rfl⟩ :=
    (mem_sup_iff_of_normalizes (H := ctxCY t tau x₁ x₂ rho) (K := zpowers t)
      (zpowers_t_normalizes_C hc13)).mp hx
  have hcomm : s * g = g * s := zpowers_t_comm_zpowers_rho hc13 s hs g hg
  have hsg : s * g * s⁻¹ = g := by rw [hcomm]; group
  have hkey : ⁅c * s, g⁆ = ⁅c, g⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    rw [show c * s * g * (c * s)⁻¹ * g⁻¹ = c * (s * g * s⁻¹) * c⁻¹ * g⁻¹ by group, hsg]
  rw [hkey]
  exact Subgroup.commutator_mem_commutator hcC hg

theorem l18_Xi_le_C (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ≤ ctxCY t tau x₁ x₂ rho := by
  have hc13 := hc.toCtx13
  have hrhoK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc13).2.2.2.2
  have hnorm := l18_C_normal hc13
  refine (l18_Xi_le_comm_C hc).trans ?_
  refine Subgroup.commutator_le.mpr ?_
  intro c hcC g hg
  have hgK : g ∈ ctxK t tau x₁ x₂ rho := (Subgroup.zpowers_le.mpr hrhoK) hg
  have hmem : g * c⁻¹ * g⁻¹ ∈ ctxCY t tau x₁ x₂ rho :=
    hnorm.2 g hgK c⁻¹ (Subgroup.inv_mem _ hcC)
  have hkey : ⁅c, g⁆ = c * (g * c⁻¹ * g⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [hkey]
  exact Subgroup.mul_mem _ hcC hmem

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

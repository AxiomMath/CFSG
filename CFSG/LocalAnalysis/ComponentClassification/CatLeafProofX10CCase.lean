module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CPair
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CL34
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CBound
public import CFSG.RankThree.SubgroupLists.CentralizerPerfect
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10CDich

public section

namespace CFSG.ComponentClassification.CatLeafProof.X10CF

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

section Facts

variable {G : Type*} [Group G] [Finite G]

theorem three_dvd_mul_sq_sub_one' {q : ℕ} (hq : 1 ≤ q) : 3 ∣ q * (q ^ 2 - 1) := by
  have h : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    ring_nf
    omega
  rw [h]
  have hr := Nat.mod_lt q (show 3 > 0 by norm_num)
  interval_cases hq3 : q % 3
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hq3) _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _) _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _

theorem sl2_facts {K : Type*} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {M : Subgroup G}
    (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    padicValNat 2 (p ^ (2 * f) - 1) ≤ padicValNat 2 (Nat.card M) ∧
      padicValNat 2 (Nat.card (center M)) ≤ 1 ∧ 3 ∣ Nat.card M ∧ p ^ f ∣ Nat.card M ∧
      f ≤ padicValNat p (Nat.card (↥M ⧸ pPrimeCore 2 ↥M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := Fact.out
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hK
    exact (Finite.one_lt_card (α := K)).ne' hK
  have hq1 : 1 < p ^ f := Nat.one_lt_pow hf0 hp.one_lt
  set q := p ^ f with hq
  have hcard : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv, RankThree.SubgroupLists.card_sl2_field, hK]
  have hdvd : Nat.card (↥M ⧸ pPrimeCore 2 ↥M) ∣ Nat.card M := card_quotient_dvd_card _
  have hqq : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hA0 : q * (q ^ 2 - 1) ≠ 0 := Nat.mul_ne_zero (by omega) hqq
  have hq2 : ¬ 2 ∣ q := fun h2 => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hsq : q ^ 2 = p ^ (2 * f) := by rw [hq, ← pow_mul, mul_comm]
  refine ⟨?_, X10CV.nu_center_le_one e, ?_, ?_, ?_⟩
  · have h1 := X10CV.padicValNat_le_of_dvd' 2 Nat.card_pos.ne' hdvd
    rw [hcard, padicValNat.mul (by omega) hqq, padicValNat.eq_zero_of_not_dvd hq2, zero_add,
      hsq] at h1
    exact h1
  · exact (three_dvd_mul_sq_sub_one' hq1.le).trans (hcard ▸ hdvd)
  · exact (Dvd.intro _ rfl : q ∣ q * (q ^ 2 - 1)).trans (hcard ▸ hdvd)
  · rw [hcard]
    exact (padicValNat_dvd_iff_le hA0).mp (Dvd.intro _ rfl)

noncomputable def quotientSubgroupOfEquiv {M C : Subgroup G} (hMC : M ≤ C) :
    ↥(M.subgroupOf C) ⧸ pPrimeCore 2 ↥(M.subgroupOf C) ≃* ↥M ⧸ pPrimeCore 2 ↥M :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe hMC) (pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hMC))

theorem seven_le_nu (hO : pPrimeCore 2 G = ⊥) {z : G} (hzZ : z ∈ center G) (hz1 : z ≠ 1)
    {L : Subgroup G} (hL : IsComponent L) (hzL : z ∈ L) (hn : padicValNat 2 (Nat.card L) =
      padicValNat 2 (Nat.card (center L)) + 6) :
    7 ≤ padicValNat 2 (Nat.card L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hZ⟩ := X10CC.isPGroup_center_of_isComponent hO hL
  obtain ⟨n, hcard⟩ := hZ.exists_card_eq
  have hzc : (⟨z, hzL⟩ : ↥L) ∈ center ↥L := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hzZ (g : G))
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hcard
    have h1 := eq_bot_of_card_eq _ hcard
    rw [h1, mem_bot] at hzc
    exact hz1 (congrArg Subtype.val hzc)
  rw [hn, hcard, padicValNat.prime_pow]
  omega

end Facts

variable {G : Type} [Group G] [Finite G]

theorem l34_of_le (hO : pPrimeCore 2 G = ⊥) {t z : G} (hzZ : z ∈ center G) (hz1 : z ≠ 1)
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hq : 3 < p ^ f) (hK : Nat.card K = p ^ f) {M L : Subgroup G}
    (hMC : M ≤ centralizer ({t} : Set G))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({t} : Set G))))
    (hzM : z ∈ M) (e : ↥M ⧸ pPrimeCore 2 ↥M ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hL : IsComponent L) (hML : M ≤ L)
    (hL34 : ∀ L₀ : Subgroup G, IsComponent L₀ → z ∈ L₀ → 3 ∣ Nat.card L₀ →
      Blueprint.LieModel (↥L₀ ⧸ center ↥L₀) .PSL 3 2 2) :
    Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 2 ∧ L.map (MulAut.conj t).toMonoidHom = L ∧
      7 ≤ padicValNat 2 (Nat.card L) ∧ ¬ p ^ (2 * f) ∣ 20160 ∧
      padicValNat 2 (p ^ (2 * f) - 1) ≤ 4 ∧ padicValNat 2 f ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, h3, hpf, -⟩ := sl2_facts hp2 hK e
  have hdvd : Nat.card M ∣ Nat.card L := card_dvd_of_le hML
  have h34 := hL34 L hL (hML hzM) (h3.trans hdvd)
  obtain ⟨hn, hodd⟩ := X10CL.l34_component hO hL h34
  have hperf : ⁅M, M⁆ = M :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf hMC hM)
  have hM1 : M ≠ ⊥ := by
    intro hb
    have hnt : Nontrivial M := B5a.nontrivial_of_isPComponent_subgroupOf hMC hM
    rw [hb] at hnt
    exact not_nontrivial _ hnt
  obtain ⟨ha, hb, hc⟩ := X10CL.l34_arith Fact.out hp2 hf hq
    (hodd p f Fact.out hp2 (hpf.trans hdvd))
  exact ⟨h34, X10CD.map_conj_eq_of_le hL hML hMC hperf hM1, seven_le_nu hO hzZ hz1 hL (hML hzM) hn,
    ha, hb, hc⟩

theorem false_of_same_l34 (hO : pPrimeCore 2 G = ⊥) {t : G}
    {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) {M₁ M₂ L : Subgroup G} (hne : M₁ ≠ M₂)
    (h₁C : M₁ ≤ centralizer ({t} : Set G))
    (h₁ : IsPComponent 2 (M₁.subgroupOf (centralizer ({t} : Set G))))
    (e₁ : ↥M₁ ⧸ pPrimeCore 2 ↥M₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (h₂C : M₂ ≤ centralizer ({t} : Set G))
    (h₂ : IsPComponent 2 (M₂.subgroupOf (centralizer ({t} : Set G))))
    (e₂ : ↥M₂ ⧸ pPrimeCore 2 ↥M₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hL : IsComponent L) (hL34 : Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 2)
    (h₁L : M₁ ≤ L) (h₂L : M₂ ≤ L) (hnd : ¬ p ^ (2 * f) ∣ 20160) : False := by
  set C := centralizer ({t} : Set G) with hC
  have hPne : M₁.subgroupOf C ≠ M₂.subgroupOf C := by
    intro h
    rw [subgroupOf_inj, inf_of_le_left h₁C, inf_of_le_left h₂C] at h
    exact hne h
  have h1 := X10CP.add_le_padicValNat_sup p hp2 h₁ h₂ hPne
  rw [Nat.card_congr (quotientSubgroupOfEquiv h₁C).toEquiv,
    Nat.card_congr (quotientSubgroupOfEquiv h₂C).toEquiv,
    ← subgroupOf_sup h₁C h₂C, Nat.card_congr (subgroupOfEquivOfLe (sup_le h₁C h₂C)).toEquiv]
    at h1
  have hf₁ := (sl2_facts hp2 hK e₁).2.2.2.2
  have hf₂ := (sl2_facts hp2 hK e₂).2.2.2.2
  have h2 := X10CV.nu_le_of_le p (sup_le h₁L h₂L)
  have h3 : p ^ (2 * f) ∣ Nat.card L :=
    (padicValNat_dvd_iff_le Nat.card_pos.ne').mpr (by omega)
  exact hnd ((X10CL.l34_component hO hL hL34).2 p (2 * f) Fact.out hp2 h3)

theorem thirteen_le_of_two_l34 (hO : pPrimeCore 2 G = ⊥) {L₁ L₂ : Subgroup G}
    (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂) (hne : L₁ ≠ L₂)
    (h₁34 : Blueprint.LieModel (↥L₁ ⧸ center ↥L₁) .PSL 3 2 2)
    (h₂7 : 7 ≤ padicValNat 2 (Nat.card L₂)) : 13 ≤ padicValNat 2 (Nat.card G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := (LocalCores.distinct_components_commute hL₂ hL₁).resolve_left fun h => hne h.symm
  have h1 := X10CC.nu_add_component 2 (commutator_eq_bot_iff_le_centralizer.mp hc)
  have h2 := (X10CL.l34_component hO hL₁ h₁34).1
  have h3 := X10CC.nu_le_card 2 (L₂ ⊔ L₁)
  omega

theorem le_centralizer_of_ne {A B : Subgroup G} (hA : IsComponent A) (hB : IsComponent B)
    (hne : A ≠ B) : A ≤ centralizer (B : Set G) :=
  commutator_eq_bot_iff_le_centralizer.mp
    ((LocalCores.distinct_components_commute hA hB).resolve_left hne)

theorem le_nu_of_l34_diag {t : G} (ht : t * t = 1) {L W M : Subgroup G} (hL : IsComponent L)
    (hLt : L.map (MulAut.conj t).toMonoidHom = L) (hW : IsComponent W)
    (hWt : W.map (MulAut.conj t).toMonoidHom ≠ W) (hMC : M ≤ centralizer ({t} : Set G))
    (hMW : M ≤ W ⊔ W.map (MulAut.conj t).toMonoidHom) (hMp : ⁅M, M⁆ = M)
    (hZ : padicValNat 2 (Nat.card (center M)) ≤ 1) :
    padicValNat 2 (Nat.card L) + 2 * padicValNat 2 (Nat.card M) ≤
      padicValNat 2 (Nat.card G) + 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (MulAut.conj t).toMonoidHom with hφ
  set W' := W.map φ with hW'def
  have hW' : IsComponent W' := LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hW
  have hW'' : W'.map φ = W := X10CV.map_conj_map_conj ht W
  have hW't : W'.map φ ≠ W' := by
    rw [hW'']
    exact fun h => hWt h.symm
  have hc := X10CD.commute_of_map_conj_ne hW hWt
  have hc' := X10CD.commute_of_map_conj_ne hW' hW't
  have hLW : L ≠ W := fun h => hWt (by rw [hW'def, ← h]; exact hLt)
  have hLW' : L ≠ W' := fun h => hWt (by rw [← hW'', ← h, hLt])
  have hMW' : M ≤ W' ⊔ W'.map φ := by
    rw [hW'', sup_comm]
    exact hMW
  have hW'W : W' ≤ centralizer (W : Set G) := fun y hy =>
    mem_centralizer_iff.mpr fun x hx => hc x hx y hy
  have h1 := X10CC.nu_add_diag ht hc' hMC hMW' hMp hZ (le_centralizer_of_ne hL hW' hLW')
    (by rw [hW'']; exact (le_sSup hW : W ≤ layer G).trans (Pump516.layer_le_normalizer hL))
  have h2 := X10CC.nu_add_diag ht hc hMC hMW hMp hZ
    (sup_le (le_centralizer_of_ne hL hW hLW) hW'W)
    ((le_sSup hW' : W' ≤ layer G).trans (X10CC.layer_le_normalizer_sup
      (Pump516.layer_le_normalizer hL) (Pump516.layer_le_normalizer hW')))
  have h3 := X10CV.nu_le_of_le 2
    (sup_le (sup_le (le_sSup hL) (le_sSup hW')) (le_sSup hW) : L ⊔ W' ⊔ W ≤ layer G)
  have h4 := X10CC.nu_sup_zpowers ht (X10CC.not_mem_layer hW hWt) (X10CC.mem_normalizer_layer t)
  have h5 := X10CC.nu_le_card 2 (layer G ⊔ zpowers t)
  omega

theorem le_nu_of_diag_diag {t : G} (ht : t * t = 1) {W₁ W₂ M₁ M₂ : Subgroup G}
    (hW₁ : IsComponent W₁) (hW₂ : IsComponent W₂)
    (h₁t : W₁.map (MulAut.conj t).toMonoidHom ≠ W₁)
    (h₂t : W₂.map (MulAut.conj t).toMonoidHom ≠ W₂) (h21 : W₂ ≠ W₁)
    (h21' : W₂ ≠ W₁.map (MulAut.conj t).toMonoidHom)
    (h₁C : M₁ ≤ centralizer ({t} : Set G)) (h₁W : M₁ ≤ W₁ ⊔ W₁.map (MulAut.conj t).toMonoidHom)
    (h₁p : ⁅M₁, M₁⁆ = M₁) (h₁Z : padicValNat 2 (Nat.card (center M₁)) ≤ 1)
    (h₂C : M₂ ≤ centralizer ({t} : Set G)) (h₂W : M₂ ≤ W₂ ⊔ W₂.map (MulAut.conj t).toMonoidHom)
    (h₂p : ⁅M₂, M₂⁆ = M₂) (h₂Z : padicValNat 2 (Nat.card (center M₂)) ≤ 1) :
    2 * padicValNat 2 (Nat.card M₁) + 2 * padicValNat 2 (Nat.card M₂) ≤
      padicValNat 2 (Nat.card G) + 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := (MulAut.conj t).toMonoidHom with hφ
  set V₁ := W₁.map φ with hV₁def
  set V₂ := W₂.map φ with hV₂def
  have hV₁ : IsComponent V₁ := LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hW₁
  have hV₂ : IsComponent V₂ := LocalCores.isComponent_map_mulEquiv (MulAut.conj t) hW₂
  have hV₁' : V₁.map φ = W₁ := X10CV.map_conj_map_conj ht W₁
  have hV₁t : V₁.map φ ≠ V₁ := by
    rw [hV₁']
    exact fun h => h₁t h.symm
  have hc₁ := X10CD.commute_of_map_conj_ne hW₁ h₁t
  have hc₁' := X10CD.commute_of_map_conj_ne hV₁ hV₁t
  have hc₂ := X10CD.commute_of_map_conj_ne hW₂ h₂t
  have hV₂V₁ : V₂ ≠ V₁ := fun h => h21 (X10CD.map_conj_injective ht h)
  have hV₂W₁ : V₂ ≠ W₁ := fun h => h21' (by
    rw [hV₁def, ← h, hV₂def, X10CV.map_conj_map_conj ht])
  have hV₁W₁ : V₁ ≠ W₁ := h₁t
  have hM₂D := X10CV.le_range_diagHom ht hc₂ h₂C h₂W h₂p
  have h0 := X10CV.nu_le_of_diag 2 hc₂ hM₂D
  have h0' : padicValNat 2 (Nat.card V₂) = padicValNat 2 (Nat.card W₂) :=
    X10CV.nu_map_conj 2 t W₂
  have hcen : ∀ {A B : Subgroup G}, IsComponent A → IsComponent B → A ≠ B →
      A ≤ centralizer (B : Set G) := fun hA hB hne => le_centralizer_of_ne hA hB hne
  have hnorm : ∀ {A : Subgroup G}, IsComponent A → layer G ≤ normalizer (A : Set G) :=
    fun hA => Pump516.layer_le_normalizer hA
  have h1 := X10CC.nu_add_diag (X := V₂) ht hc₂ h₂C h₂W h₂p h₂Z
    (fun y hy => mem_centralizer_iff.mpr fun x hx => hc₂ x hx y hy) le_normalizer
  have h₁W' : M₁ ≤ V₁ ⊔ V₁.map φ := by
    rw [hV₁', sup_comm]
    exact h₁W
  have h2 := X10CC.nu_add_diag ht hc₁' h₁C h₁W' h₁p h₁Z
    (sup_le (hcen hV₂ hV₁ hV₂V₁) (hcen hW₂ hV₁ (fun h => h21' h)))
    (by
      rw [hV₁']
      exact (le_sSup hW₁ : W₁ ≤ layer G).trans
        (X10CC.layer_le_normalizer_sup (hnorm hV₂) (hnorm hW₂)))
  have h3 := X10CC.nu_add_diag ht hc₁ h₁C h₁W h₁p h₁Z
    (sup_le (sup_le (hcen hV₂ hW₁ hV₂W₁) (hcen hW₂ hW₁ h21)) (hcen hV₁ hW₁ hV₁W₁))
    ((le_sSup hV₁ : V₁ ≤ layer G).trans (X10CC.layer_le_normalizer_sup
      (X10CC.layer_le_normalizer_sup (hnorm hV₂) (hnorm hW₂)) (hnorm hV₁)))
  have h4 := X10CV.nu_le_of_le 2 (sup_le (sup_le (sup_le (le_sSup hV₂) (le_sSup hW₂))
    (le_sSup hV₁)) (le_sSup hW₁) : V₂ ⊔ W₂ ⊔ V₁ ⊔ W₁ ≤ layer G)
  have h5 := X10CC.nu_sup_zpowers ht (X10CC.not_mem_layer hW₁ h₁t)
    (X10CC.mem_normalizer_layer t)
  have h6 := X10CC.nu_le_card 2 (layer G ⊔ zpowers t)
  omega

theorem false_of_config (hO : pPrimeCore 2 G = ⊥) {t z : G} (ht : t * t = 1)
    (hzZ : z ∈ center G) (hz1 : z ≠ 1) {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : 3 < p ^ f) (hK : Nat.card K = p ^ f)
    {M₁ M₂ : Subgroup G} (hne : M₁ ≠ M₂)
    (h₁C : M₁ ≤ centralizer ({t} : Set G))
    (h₁ : IsPComponent 2 (M₁.subgroupOf (centralizer ({t} : Set G)))) (h₁E : M₁ ≤ layer G)
    (hz₁ : z ∈ M₁) (e₁ : ↥M₁ ⧸ pPrimeCore 2 ↥M₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (h₂C : M₂ ≤ centralizer ({t} : Set G))
    (h₂ : IsPComponent 2 (M₂.subgroupOf (centralizer ({t} : Set G)))) (h₂E : M₂ ≤ layer G)
    (hz₂ : z ∈ M₂) (e₂ : ↥M₂ ⧸ pPrimeCore 2 ↥M₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hbound : padicValNat 2 (Nat.card G) ≤
      2 * padicValNat 2 (p ^ (2 * f) - 1) + padicValNat 2 f + 3)
    (hL34 : ∀ L₀ : Subgroup G, IsComponent L₀ → z ∈ L₀ → 3 ∣ Nat.card L₀ →
      Blueprint.LieModel (↥L₀ ⧸ center ↥L₀) .PSL 3 2 2) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hke := (X10CB.lte_facts Fact.out hp2 hf).2.2
  obtain ⟨hk₁, hZ₁, -, -, -⟩ := sl2_facts hp2 hK e₁
  obtain ⟨hk₂, hZ₂, -, -, -⟩ := sl2_facts hp2 hK e₂
  have hp₁ : ⁅M₁, M₁⁆ = M₁ :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf h₁C h₁)
  have hp₂ : ⁅M₂, M₂⁆ = M₂ :=
    Subgroup.isPerfect_iff.mp (B5a.isPerfect_of_isPComponent_subgroupOf h₂C h₂)
  obtain ⟨W₁, hW₁, hMW₁⟩ := X10CD.exists_isComponent_le_sup_conj ht h₁C h₁ h₁E
  obtain ⟨W₂, hW₂, hMW₂⟩ := X10CD.exists_isComponent_le_sup_conj ht h₂C h₂ h₂E
  by_cases hi₁ : W₁.map (MulAut.conj t).toMonoidHom = W₁
  · rw [hi₁, sup_idem] at hMW₁
    obtain ⟨h34₁, hLt₁, h7₁, hnd, hk4, he1⟩ :=
      l34_of_le hO hzZ hz1 hp2 hf hq hK h₁C h₁ hz₁ e₁ hW₁ hMW₁ hL34
    by_cases hi₂ : W₂.map (MulAut.conj t).toMonoidHom = W₂
    · rw [hi₂, sup_idem] at hMW₂
      obtain ⟨-, -, h7₂, -⟩ := l34_of_le hO hzZ hz1 hp2 hf hq hK h₂C h₂ hz₂ e₂ hW₂ hMW₂ hL34
      by_cases hWW : W₁ = W₂
      · subst hWW
        exact false_of_same_l34 hO hp2 hK hne h₁C h₁ e₁ h₂C h₂ e₂ hW₁ h34₁ hMW₁ hMW₂ hnd
      · have := thirteen_le_of_two_l34 hO hW₁ hW₂ hWW h34₁ h7₂
        omega
    · have := le_nu_of_l34_diag ht hW₁ hLt₁ hW₂ hi₂ h₂C hMW₂ hp₂ hZ₂
      omega
  · by_cases hi₂ : W₂.map (MulAut.conj t).toMonoidHom = W₂
    · rw [hi₂, sup_idem] at hMW₂
      obtain ⟨-, hLt₂, h7₂, -, -, he1⟩ :=
        l34_of_le hO hzZ hz1 hp2 hf hq hK h₂C h₂ hz₂ e₂ hW₂ hMW₂ hL34
      have := le_nu_of_l34_diag ht hW₂ hLt₂ hW₁ hi₁ h₁C hMW₁ hp₁ hZ₁
      omega
    · by_cases hsame : W₂ = W₁ ∨ W₂ = W₁.map (MulAut.conj t).toMonoidHom
      ·
        have hc₁ := X10CD.commute_of_map_conj_ne hW₁ hi₁
        have hMW₂' : M₂ ≤ W₁ ⊔ W₁.map (MulAut.conj t).toMonoidHom := by
          rcases hsame with rfl | rfl
          · exact hMW₂
          · rwa [X10CV.map_conj_map_conj ht, sup_comm] at hMW₂
        have e1 := X10CD.eq_range_diagHom ht hW₁ hc₁ h₁C h₁ hMW₁
        have e2 := X10CD.eq_range_diagHom ht hW₁ hc₁ h₂C h₂ hMW₂'
        exact hne (e1.trans e2.symm)
      · push Not at hsame
        have := le_nu_of_diag_diag ht hW₁ hW₂ hi₁ hi₂ hsame.1 hsame.2 h₁C hMW₁ hp₁ hZ₁ h₂C
          hMW₂ hp₂ hZ₂
        omega

end CFSG.ComponentClassification.CatLeafProof.X10CF

module

public import CFSG.Quasithin.Vol2.Ch5Sec3L3ExcNF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3ExcCoords
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec3L3ExcLoc

public section

namespace CFSG.Quasithin.H13.Sec53L3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F1
  CFSG.Quasithin.SL2Semilinear

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D L₂ : Subgroup G} {n f : ℕ}

theorem exists_excNF_F4 (h527 : Stmt5_2_7_F4) (h531 : Stmt5_3_1_F4)
    (hyp : Hyp5_2_4 G T M L V H B D L₂ n) (hty : IsOfLieType52 M L H B D T .PSL 3 f)
    (hf : f = 2) {z : G} (hz : z ∈ sec53ZS T L) (hzT : z ∈ centerOf T) (hz1 : z ≠ 1)
    (hO : pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G)) ≠ sec53S T L) :
    ∃ N : ExcNF T (sec53S T L) (pCoreOf 2 L) (pCoreOf 2 (oTwoUpper H)) (sec53ZS T L),
      N.Φ (1, 0, 0) = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : 2 ≤ f := hf.ge
  have h := hyp.toHyp5_1_8.toHyp5_0_1
  have hST : sec53S T L ≤ T := inf_le_left

  rw [(exc_centralizer_eq_F4 h527 h531 hyp hty hf hz hzT hz1 hO).1] at hO
  obtain ⟨x₀, hx₀T, hx₀S⟩ : ∃ x₀ ∈ T, x₀ ∉ sec53S T L := by
    by_contra hcon
    push Not at hcon
    apply hO
    have hP : pCoreOf 2 T = T := le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 T)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
        h.sylow.1)
    rw [hP]
    exact le_antisymm (fun t ht => hcon t ht) hST

  obtain ⟨F, _, _, _, hFcard, C₁, C₂, h0, hy₁, -⟩ := exists_sCoords_F4 h527 hyp hty hf2
  have hF : Nat.card F = 4 := by rw [hFcard, hf]; norm_num
  have hsup := sup_sec53_F4 h527 hyp hty hf2
  have hinf := (l3facts_two_F4 h527 hyp hty hf2).2.2.2.1
  obtain ⟨Φc, hΦ⟩ := exists_heisCoords_of C₁ C₂ h0 hy₁ hsup hinf

  have hLG : L ≤ sec53G1 M L H B := le_sup_left.trans le_sup_left
  have hKG : oTwoUpper H ≤ sec53G2 M L H D := le_sup_right
  have hV₂L : pCoreOf 2 (oTwoUpper H) ≤ L := (le_sup_right.trans hsup.le).trans inf_le_right
  have hV₁K : pCoreOf 2 L ≤ oTwoUpper H :=
    (le_sup_left.trans hsup.le).trans (sec53S_le_K_F4 h527 hyp)
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  obtain ⟨τ₁, σ₁, hτ₁, hσ₁⟩ := C₁.exists_semilinear hLG hV₂L (hTL hx₀T)
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hTL hx₀T))
  obtain ⟨τ₂, σ₂, hτ₂, hσ₂⟩ := C₂.exists_semilinear hKG hV₁K (hTK hx₀T)
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTK hx₀T))
  have hs₁ := ringHom_eq_sq_of_ne hF
    (exists_sigma_ne_F4 h527 h531 hyp hty hf2 C₁ hz hzT hz1 hx₀T hx₀S hτ₁ hσ₁)
  have hs₂ := ringHom_eq_sq_of_ne hF
    (exists_sigma_ne_F4 h527 h531 hyp hty hf2 C₂ hz hzT hz1 hx₀T hx₀S hτ₂ hσ₂)
  have hTN := le_normalizer_sec53S (L := L) hyp
  have hZ₁ : (τ₁ (0, 1)).1 = 0 := by
    have h1 : C₁.ι (τ₁ (0, 1)) ∈ sec53ZS T L := by
      rw [hτ₁]
      exact conj_mem_centerOf (hTN hx₀T) ((C₁.center _).mpr ⟨1, rfl⟩)
    obtain ⟨c, hc⟩ := (C₁.center _).mp h1
    rw [C₁.inj hc]
  have hZ₂ : (τ₂ (0, 1)).1 = 0 := by
    have h1 : C₂.ι (τ₂ (0, 1)) ∈ sec53ZS T L := by
      rw [hτ₂]
      exact conj_mem_centerOf (hTN hx₀T) ((C₂.center _).mpr ⟨1, rfl⟩)
    obtain ⟨c, hc⟩ := (C₂.center _).mp h1
    rw [C₂.inj hc]
  have hA₁ : (τ₁ (1, 0)).1 ≠ 0 := by
    intro h0'
    have := fst_of_semilinear hσ₁ hZ₁ (τ₁.symm (1, 0))
    rw [τ₁.apply_symm_apply, h0', mul_zero] at this
    exact one_ne_zero this
  have hA₂ : (τ₂ (1, 0)).1 ≠ 0 := by
    intro h0'
    have := fst_of_semilinear hσ₂ hZ₂ (τ₂.symm (1, 0))
    rw [τ₂.apply_symm_apply, h0', mul_zero] at this
    exact one_ne_zero this
  have hact := heis_conj_of_frobenius Φc C₁ C₂ hΦ h0 hτ₁ hσ₁ hτ₂ hσ₂ hZ₁ hs₁ hs₂

  have hTS : ∀ t ∈ T, (∀ g ∈ sec53ZS T L, g * t = t * g) → t ∈ sec53S T L := by
    intro t ht hc
    rw [← l3facts_one_F4 h527 h531 hyp hty hf2]
    exact Subgroup.mem_inf.mpr ⟨ht, Subgroup.mem_centralizer_iff.mpr hc⟩
  obtain ⟨Φ', x, hxT, hxS, hxx, hxact⟩ :=
    Φc.exists_normalized hF hST hTS hx₀T hx₀S hA₁ hA₂ hact

  have := Fintype.ofFinite F
  have hcard : Fintype.card CFSG.Fischer.F4 = Fintype.card F := by
    rw [CFSG.Fischer.F4.card, ← Nat.card_eq_fintype_card, hF]
  obtain ⟨Ψ, hΨ⟩ := Φ'.exists_transport (FiniteField.ringEquivOfCardEq hcard)
  have hΨact : ∀ c a b, x * Ψ.Φ (c, a, b) * x⁻¹ = Ψ.Φ (c ^ 2, a ^ 2, b ^ 2) := by
    intro c a b
    rw [hΨ, hΨ, hxact, map_pow, map_pow, map_pow]

  obtain ⟨cz, hcz⟩ := (Ψ.mem_Z z).mp hz
  have hcz2 : cz ^ 2 = cz := by
    have hxz : x * z * x⁻¹ = z := by
      have hc := Subgroup.mem_centralizer_iff.mp
        ((inf_le_right : centerOf T ≤ Subgroup.centralizer (T : Set G)) hzT) x hxT
      rw [hc]
      group
    rw [← hcz, hΨact] at hxz
    have h' := Ψ.inj hxz
    rw [Prod.mk.injEq] at h'
    exact h'.1
  have hcz0 : cz ≠ 0 := by
    rintro rfl
    exact hz1 (hcz.symm.trans Ψ.zero)
  have hcz1 : cz = 1 := f4_eq_one_of_sq_eq_self cz hcz2 hcz0
  have hcover : ∀ t ∈ T, t ∈ sec53S T L ∨ t * x ∈ sec53S T L := by
    intro t ht
    by_cases htS : t ∈ sec53S T L
    · exact Or.inl htS
    · exact Or.inr (exc_mul_mem_S_F4 h527 h531 hyp hty hf hz hzT hz1 ht htS hxT hxS)
  refine ⟨{ Ψ with
    x := x
    x_mem := hxT
    x_not_mem := hxS
    x_mul_self := hxx
    x_act := hΨact
    cover := hcover }, ?_⟩
  show Ψ.Φ (1, 0, 0) = z
  rw [← hcz1]
  exact hcz

end CFSG.Quasithin.H13.Sec53L3

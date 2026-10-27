module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3Star
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3Frame
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3A

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ABGLocalTools
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

section Arithmetic

theorem padic_card_SU3_of_mod4_three {q : ℕ} (hq4 : q % 4 = 3) (hq2 : 2 ≤ q) :
    padicValNat 2 (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1)) = 1 + 2 * padicValNat 2 (q + 1) := by
  have hodd : Odd q := Nat.odd_iff.2 (by omega)
  rw [u3two_padic_order q hodd (by omega), u3two_padic_sub_one_of_mod4_three q hq4]

theorem two_le_padic_add_one {q : ℕ} (hq4 : q % 4 = 3) : 2 ≤ padicValNat 2 (q + 1) := by
  have h4 : 2 ^ 2 ∣ q + 1 := by omega
  exact (padicValNat_dvd_iff_le (by omega)).1 h4

end Arithmetic

section Units

theorem exists_unit_orderOf_of_dvd (hF : Nat.card F = (p ^ f) ^ 2) {d : ℕ}
    (hd : d ∣ (p ^ f) ^ 2 - 1) : ∃ ι : Fˣ, orderOf ι = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hq2 := two_le_prime_pow_of_card' hF
  have hgo : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  have hpos : 0 < (p ^ f) ^ 2 - 1 := by
    have : 4 ≤ (p ^ f) ^ 2 := by nlinarith
    omega
  obtain ⟨k, hk⟩ := hd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hk
    omega
  refine ⟨g ^ k, ?_⟩
  rw [orderOf_pow_of_dvd hk0 (by rw [hgo]; exact Dvd.intro_left _ hk.symm), hgo]
  conv_lhs => rw [hk]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)

end Units

section Std

variable (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) {c : F}
  (hc : unitaryInvolution F p f c * c = -1)

theorem frameEquiv_zSU :
    ((frameEquiv hF h2 hc (zSU hF) : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) = z0 := by
  have hl : unitaryInvolution F p f (((-1 : Fˣ)) : F) * ((-1 : Fˣ) : F) = 1 := by
    simp
  have h := frameEquiv_tSU hF h2 hc (-1 : Fˣ) hl
  rw [zSU, h, z0]
  simp

@[expose] noncomputable def stdSylG (N : ℕ) : Subgroup (SU (unitaryInvolution F p f) 3) :=
  (stdMon (F := F) N).comap ((SUid (unitaryInvolution F p f) 3).subtype.comp
    (frameEquiv hF h2 hc).toMonoidHom)

theorem mem_stdSylG {N : ℕ} {g : SU (unitaryInvolution F p f) 3} :
    g ∈ stdSylG hF h2 hc N ↔
      ((frameEquiv hF h2 hc g : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) ∈
        stdMon (F := F) N := Iff.rfl

theorem coe_frameEquiv_mul (a b : SU (unitaryInvolution F p f) 3) :
    ((frameEquiv hF h2 hc (a * b) : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) =
      (frameEquiv hF h2 hc a : GL (Fin 3) F) * (frameEquiv hF h2 hc b : GL (Fin 3) F) := by
  rw [map_mul]; rfl

theorem stdSylG_le_centralizer {N : ℕ} :
    stdSylG hF h2 hc N ≤ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  apply (frameEquiv hF h2 hc).injective
  apply Subtype.ext
  rw [coe_frameEquiv_mul, coe_frameEquiv_mul, frameEquiv_zSU hF h2 hc]
  exact (z0_comm hg).symm

theorem card_stdSylG {N : ℕ} (hNe : Even N) (hN : N ∣ p ^ f + 1) :
    Nat.card (stdSylG hF h2 hc N) = Nat.card (stdMon (F := F) N) := by
  set ψ : SU (unitaryInvolution F p f) 3 →* GL (Fin 3) F :=
    (SUid (unitaryInvolution F p f) 3).subtype.comp (frameEquiv hF h2 hc).toMonoidHom with hψ
  have hinj : Function.Injective ψ := by
    intro a b hab
    exact (frameEquiv hF h2 hc).injective (Subtype.ext hab)
  have hle : stdMon (F := F) N ≤ ψ.range := by
    intro x hx
    have hxU : x ∈ SUid (unitaryInvolution F p f) 3 := stdMon_le_SUid hNe hN hx
    exact ⟨(frameEquiv hF h2 hc).symm ⟨x, hxU⟩, by simp [hψ]⟩
  have h1 : (stdSylG hF h2 hc N).map ψ = stdMon (F := F) N := by
    rw [stdSylG, Subgroup.map_comap_eq, inf_of_le_right hle]
  rw [← h1, Subgroup.card_map_of_injective hinj]

end Std

section Standard

variable (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) {c : F}
  (hc : unitaryInvolution F p f c * c = -1)

include hF in
theorem exists_iota (hq4 : (p ^ f) % 4 = 3) :
    ∃ ι : Fˣ, orderOf ι = 2 ^ padicValNat 2 (p ^ f + 1) ∧
      ι ^ (2 ^ padicValNat 2 (p ^ f + 1)) = 1 ∧ ι ^ 2 ≠ 1 := by
  have hq2 := two_le_prime_pow_of_card' hF
  have ha := two_le_padic_add_one hq4
  have hdvd : 2 ^ padicValNat 2 (p ^ f + 1) ∣ (p ^ f) ^ 2 - 1 := by
    have h1 : 2 ^ padicValNat 2 (p ^ f + 1) ∣ p ^ f + 1 := pow_padicValNat_dvd
    refine h1.trans ?_
    refine ⟨p ^ f - 1, ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    have : (k + 1) ^ 2 = (k + 1 + 1) * k + 1 := by ring
    omega
  obtain ⟨ι, hι⟩ := exists_unit_orderOf_of_dvd hF hdvd
  refine ⟨ι, hι, hι ▸ pow_orderOf_eq_one ι, fun h => ?_⟩
  have h1 := orderOf_dvd_of_pow_eq_one h
  rw [hι] at h1
  have h4 : 2 ^ 2 ∣ 2 ^ padicValNat 2 (p ^ f + 1) := pow_dvd_pow 2 ha
  have := (Nat.le_of_dvd (by norm_num) (h4.trans h1))
  omega

theorem isSylowOf_stdSylG (hq4 : (p ^ f) % 4 = 3) :
    IsSylowOf 2 (stdSylG hF h2 hc (2 ^ padicValNat 2 (p ^ f + 1))) ⊤ := by
  have hq2 := two_le_prime_pow_of_card' hF
  have ha := two_le_padic_add_one hq4
  set a := padicValNat 2 (p ^ f + 1) with hadef
  have hNe : Even (2 ^ a) := (even_iff_two_dvd.2 (dvd_pow_self 2 (by omega)))
  have hNd : 2 ^ a ∣ p ^ f + 1 := pow_padicValNat_dvd
  obtain ⟨ι, hιo, -, -⟩ := exists_iota hF hq4
  have hroots : Nat.card (rootsOfUnity (2 ^ a) F) = 2 ^ a := by
    haveI : NeZero (2 ^ a) := ⟨by positivity⟩
    exact (hιo ▸ IsPrimitiveRoot.orderOf ι : IsPrimitiveRoot ι (2 ^ a)).card_rootsOfUnity'
  refine isSylowOf_of_card le_top ?_
  rw [Subgroup.card_top, card_SU3 hF, card_stdSylG hF h2 hc hNe hNd, card_stdMon _ hroots,
    Nat.factorization_def _ Nat.prime_two, padic_card_SU3_of_mod4_three hq4 hq2]
  ring

end Standard

section StarG

variable (hF : Nat.card F = (p ^ f) ^ 2) (h2 : (2 : F) ≠ 0) {c : F}
  (hc : unitaryInvolution F p f c * c = -1)

theorem coe_frameEquiv_conj (n g₀ : SU (unitaryInvolution F p f) 3) :
    ((frameEquiv hF h2 hc (n * g₀ * n⁻¹) : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) =
      (frameEquiv hF h2 hc n : GL (Fin 3) F) * (frameEquiv hF h2 hc g₀ : GL (Fin 3) F) *
        (frameEquiv hF h2 hc n : GL (Fin 3) F)⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  rfl

theorem normalizer_iff_stdMon {N : ℕ} (hNe : Even N) (hN : N ∣ p ^ f + 1)
    {n : SU (unitaryInvolution F p f) 3}
    (hn : n ∈ Subgroup.normalizer (stdSylG hF h2 hc N : Set (SU (unitaryInvolution F p f) 3))) :
    ∀ g : GL (Fin 3) F, g ∈ stdMon (F := F) N ↔
      (frameEquiv hF h2 hc n : GL (Fin 3) F) * g * (frameEquiv hF h2 hc n : GL (Fin 3) F)⁻¹ ∈
        stdMon (F := F) N := by
  intro g
  have hmem := Subgroup.mem_normalizer_iff.1 hn
  have hU : stdMon (F := F) N ≤ SUid (unitaryInvolution F p f) 3 := stdMon_le_SUid hNe hN
  constructor
  · intro hg
    have hgU := hU hg
    set g₀ := (frameEquiv hF h2 hc).symm ⟨g, hgU⟩ with hg₀def
    have hg₀ : ((frameEquiv hF h2 hc g₀ : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) = g := by
      simp [hg₀def]
    have h1 : g₀ ∈ stdSylG hF h2 hc N := by rw [mem_stdSylG, hg₀]; exact hg
    have h3 := (hmem g₀).1 h1
    rw [mem_stdSylG, coe_frameEquiv_conj, hg₀] at h3
    exact h3
  · intro hg
    have hgU' := hU hg
    have hgU : g ∈ SUid (unitaryInvolution F p f) 3 := by
      have : g = (frameEquiv hF h2 hc n : GL (Fin 3) F)⁻¹ *
          ((frameEquiv hF h2 hc n : GL (Fin 3) F) * g * (frameEquiv hF h2 hc n : GL (Fin 3) F)⁻¹) *
            (frameEquiv hF h2 hc n : GL (Fin 3) F) := by group
      rw [this]
      exact (SUid (unitaryInvolution F p f) 3).mul_mem
        ((SUid (unitaryInvolution F p f) 3).mul_mem
          ((SUid (unitaryInvolution F p f) 3).inv_mem (frameEquiv hF h2 hc n).2) hgU')
        (frameEquiv hF h2 hc n).2
    set g₀ := (frameEquiv hF h2 hc).symm ⟨g, hgU⟩ with hg₀def
    have hg₀ : ((frameEquiv hF h2 hc g₀ : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F) = g := by
      simp [hg₀def]
    have h1 : n * g₀ * n⁻¹ ∈ stdSylG hF h2 hc N := by
      rw [mem_stdSylG, coe_frameEquiv_conj, hg₀]; exact hg
    have h3 := (hmem g₀).2 h1
    rw [mem_stdSylG, hg₀] at h3
    exact h3

theorem dGL_comm_of_blockShape {g : GL (Fin 3) F} (l γ : Fˣ)
    (h : (g : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) :
    g * dGL l l γ = dGL l l γ * g := by
  obtain ⟨h02, h12, h20, h21⟩ := h
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_dGL]
  ext i j
  simp only [dMat, Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [h02, h12, h20, h21, mul_comm]

include h2 hc in
theorem tSU_comm_of_mem_centralizer {l : Fˣ} (hl : unitaryInvolution F p f (l : F) * l = 1)
    {k : SU (unitaryInvolution F p f) 3}
    (hk : k ∈ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))) :
    k * tSU hF l = tSU hF l * k := by
  have hkz : k * zSU hF = zSU hF * k := (Subgroup.mem_centralizer_iff.1 hk (zSU hF) rfl).symm
  have hφ : (frameEquiv hF h2 hc k : GL (Fin 3) F) * z0 =
      z0 * (frameEquiv hF h2 hc k : GL (Fin 3) F) := by
    have := congrArg (fun g : SU (unitaryInvolution F p f) 3 =>
      ((frameEquiv hF h2 hc g : SUid (unitaryInvolution F p f) 3) : GL (Fin 3) F)) hkz
    simpa only [coe_frameEquiv_mul, frameEquiv_zSU hF h2 hc] using this
  have hsh := blockShape_of_commute_z0 h2 hφ
  have hcomm := dGL_comm_of_blockShape (g := (frameEquiv hF h2 hc k : GL (Fin 3) F)) l (l * l)⁻¹ hsh
  apply (frameEquiv hF h2 hc).injective
  apply Subtype.ext
  rw [coe_frameEquiv_mul, coe_frameEquiv_mul, frameEquiv_tSU hF h2 hc l hl]
  exact hcomm

theorem star_G_std (hq4 : (p ^ f) % 4 = 3) {n : SU (unitaryInvolution F p f) 3}
    (hn : n ∈ Subgroup.normalizer
      (stdSylG hF h2 hc (2 ^ padicValNat 2 (p ^ f + 1)) : Set (SU (unitaryInvolution F p f) 3))) :
    ∃ s ∈ stdSylG hF h2 hc (2 ^ padicValNat 2 (p ^ f + 1)), ∃ l : Fˣ,
      unitaryInvolution F p f (l : F) * l = 1 ∧ n = s * tSU hF l := by
  have hq2 := two_le_prime_pow_of_card' hF
  have ha := two_le_padic_add_one hq4
  have hNe : Even (2 ^ padicValNat 2 (p ^ f + 1)) :=
    even_iff_two_dvd.2 (dvd_pow_self 2 (by omega))
  have hNd : 2 ^ padicValNat 2 (p ^ f + 1) ∣ p ^ f + 1 := pow_padicValNat_dvd
  obtain ⟨ι, -, hιN, hι2⟩ := exists_iota hF hq4
  obtain ⟨s, hs, l, hl, hnl⟩ := exists_mul_central_of_mem_normalizer h2 hNe hιN hι2
    (frameEquiv hF h2 hc n).2 (normalizer_iff_stdMon hF h2 hc hNe hNd hn)
  refine ⟨(frameEquiv hF h2 hc).symm ⟨s, stdMon_le_SUid hNe hNd hs⟩, ?_, l, hl, ?_⟩
  · rw [mem_stdSylG]
    simpa using hs
  · apply (frameEquiv hF h2 hc).injective
    apply Subtype.ext
    rw [coe_frameEquiv_mul, frameEquiv_tSU hF h2 hc l hl]
    simpa using hnl

include h2 hc in
theorem star_G (hq4 : (p ^ f) % 4 = 3) {S : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hS : IsSylowOf 2 S
      (Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))))
    {n : SU (unitaryInvolution F p f) 3} (hn : n ∈ Subgroup.normalizer (S : Set _)) :
    ∃ s ∈ S, ∃ l : Fˣ, unitaryInvolution F p f (l : F) * l = 1 ∧ n = s * tSU hF l := by
  have hXL := (isSylowOf_stdSylG hF h2 hc hq4).of_le (stdSylG_le_centralizer hF h2 hc) le_top
  obtain ⟨k, hkL, hk⟩ := exists_conj_of_isSylowOf_two hXL hS
  have hn' := mem_normalizer_of_conj hk hn
  obtain ⟨s₀, hs₀, l, hl, hnl⟩ := star_G_std hF h2 hc hq4 hn'
  refine ⟨k * s₀ * k⁻¹, ?_, l, hl, ?_⟩
  · rw [hk]
    have : k⁻¹ * (k * s₀ * k⁻¹) * k = s₀ := by group
    rw [this]
    exact hs₀
  · have hcomm := tSU_comm_of_mem_centralizer hF h2 hc hl hkL
    calc n = k * (k⁻¹ * n * k) * k⁻¹ := by group
      _ = k * (s₀ * tSU hF l) * k⁻¹ := by rw [hnl]
      _ = (k * s₀ * k⁻¹) * (k * tSU hF l * k⁻¹) := by group
      _ = (k * s₀ * k⁻¹) * tSU hF l := by rw [hcomm]; group

end StarG




end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15

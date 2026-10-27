module

public import CFSG.Dihedral.Glauberman.DicksonMaxExist
public import CFSG.Dihedral.Glauberman.DicksonMaxTables
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum

public section

namespace CFSG.Glauberman.Dickson

open BenderSuzuki.MatrixGroups ZMod
open scoped LinearAlgebra.Projectivization

theorem nonempty_psl2_galoisField_four_mulEquiv :
    Nonempty (PSL2MatrixGroup (GaloisField 2 2) ≃* alternatingGroup (Fin 5)) := by
  classical
  let K := GaloisField 2 2
  have hK : Nat.card K = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hcenter :=
    BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one (K := K) (CharTwo.neg_eq 1)
  have hcard := BenderSuzuki.External.huppert614_card_psl_mul_center (K := K)
  rw [hK, hcenter] at hcard
  have hPSL : Nat.card (PSL2MatrixGroup K) = 60 := by
    norm_num at hcard
    exact hcard
  have hP : Nat.card (ℙ K (Fin 2 → K)) = 5 := by
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp), hK]
  let : Fintype (ℙ K (Fin 2 → K)) := Fintype.ofFinite _
  let e : ℙ K (Fin 2 → K) ≃ Fin 5 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, hP])
  let ψ : PSL2MatrixGroup K →* Equiv.Perm (Fin 5) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom (PSL2MatrixGroup K) (ℙ K (Fin 2 → K)))
  have hψ : Function.Injective ψ :=
    e.permCongrHom.injective.comp
      (MulAction.toPerm_injective (α := PSL2MatrixGroup K) (β := ℙ K (Fin 2 → K)))
  have hrange_card : Nat.card ψ.range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hPSL]
  have hindex : ψ.range.index = 2 := by
    have h := ψ.range.card_mul_index
    rw [hrange_card, Nat.card_perm, Nat.card_fin] at h
    simp [Nat.factorial] at h
    omega
  have hrange : ψ.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨(MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hrange)⟩

theorem exists_injective_alternatingFour_alternatingFive :
    ∃ φ : alternatingGroup (Fin 4) →* alternatingGroup (Fin 5), Function.Injective φ := by
  classical
  let ι : Fin 4 ↪ Fin 5 := Fin.castSuccEmb
  let V := Equiv.Perm.viaEmbeddingHom ι
  have hsign : ∀ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign (V σ) = Equiv.Perm.sign σ := by
    intro σ
    simp only [V, Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding]
    convert Equiv.Perm.sign_extendDomain σ (Equiv.ofInjective ι.1 ι.2)
  let φ : alternatingGroup (Fin 4) →* alternatingGroup (Fin 5) :=
    (V.comp (alternatingGroup (Fin 4)).subtype).codRestrict _ (fun σ => by
      rw [Equiv.Perm.mem_alternatingGroup, MonoidHom.comp_apply, hsign]
      exact σ.2)
  refine ⟨φ, fun a b h => Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective ι ?_)⟩
  exact congrArg Subtype.val h

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [hp : Fact p.Prime]

theorem zmod_five_sign_mul (c : ℤ) (hc : c = 1 ∨ c = -1) (r : ℕ) (hr : r = 1 ∨ r = 4) :
    (c : ZMod 5) * (r : ZMod 5) = 1 ∨ (c : ZMod 5) * (r : ZMod 5) = 4 := by
  rcases hc with rfl | rfl <;> rcases hr with rfl | rfl <;> decide

omit [Finite F] in
theorem exists_subgroup_of_injective {G : Type*} [Group G] {φ : G →* PSL2MatrixGroup F}
    (hφ : Function.Injective φ) : ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* G) :=
  ⟨φ.range, ⟨(MonoidHom.ofInjective hφ).symm⟩⟩

theorem isSquare_five (hF : Nat.card F = p ^ f) (hp2 : p ≠ 2)
    (h : p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5]) : IsSquare (5 : F) := by
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  rcases h with rfl | h
  · have h5 : (5 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 5
    rw [h5]
    exact ⟨0, by ring⟩
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F p]
    exact hp2
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have key := FiniteField.isSquare_odd_prime_iff (F := F) hF2 (p := 5) (by norm_num)
  have h5 : ((5 : ℕ) : F) = 5 := by norm_num
  rw [h5] at key
  rw [key]
  have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  set q := Fintype.card F with hqdef
  have hqodd : q % 2 = 1 := by
    rw [hq]
    exact Nat.odd_iff.mp ((hp.out.odd_of_ne_two hp2).pow)
  have hq5 : q % 5 = 1 ∨ q % 5 = 4 := by
    rw [← hq] at h
    have h' : q ^ 2 % 5 = 1 := h
    have : q ^ 2 % 5 = (q % 5) ^ 2 % 5 := Nat.pow_mod q 2 5
    have hlt : q % 5 < 5 := Nat.mod_lt q (by norm_num)
    interval_cases hr : q % 5 <;> simp_all
  have hχ : (χ₄ (q : ZMod 4) : ℤ) = 1 ∨ (χ₄ (q : ZMod 4) : ℤ) = -1 := by
    rw [χ₄_nat_eq_if_mod_four]
    simp only [show q % 2 ≠ 0 by omega, ↓reduceIte]
    split_ifs
    · left; rfl
    · right; rfl
  have harg : ((χ₄ (q : ZMod 4) : ℤ) : ZMod 5) * (q : ZMod 5) = 1 ∨
      ((χ₄ (q : ZMod 4) : ℤ) : ZMod 5) * (q : ZMod 5) = 4 := by
    rw [← ZMod.natCast_mod q 5]
    exact zmod_five_sign_mul _ hχ _ hq5
  rw [Ne, quadraticChar_neg_one_iff_not_isSquare, not_not]
  rcases harg with ha | ha
  · rw [ha]
    exact ⟨1, by norm_num⟩
  · rw [ha]
    exact ⟨2, by norm_num⟩

theorem dickson_psl2_subgroup_existence (hF : Nat.card F = p ^ f) :
    (∀ m ≤ f, ∃ H : Subgroup (PSL2MatrixGroup F),
      Nat.card H = p ^ m ∧ IsElementaryAbelian p H) ∧
    (∀ z, (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nat.card H = z ∧ IsCyclic H) ∧
    (∀ z, 2 ≤ z →
      (z ∣ (p ^ f + 1) / Nat.gcd 2 (p ^ f - 1) ∨ z ∣ (p ^ f - 1) / Nat.gcd 2 (p ^ f - 1)) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* DihedralGroup z)) ∧
    (∀ m, m ∣ f → ∃ H : Subgroup (PSL2MatrixGroup F),
      Nonempty (H ≃* PSL2MatrixGroup (GaloisField p m))) ∧
    (∀ m, 2 * m ∣ f → ∃ H : Subgroup (PSL2MatrixGroup F),
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∧
    ((Odd p ∨ Even f) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* alternatingGroup (Fin 4))) ∧
    ((p ^ f) ^ 2 ≡ 1 [MOD 16] →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* Equiv.Perm (Fin 4))) ∧
    ((p = 5 ∨ (p ^ f) ^ 2 ≡ 1 [MOD 5]) →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* alternatingGroup (Fin 5))) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have : CharP F p := charP_of_card_eq_prime_pow (by simpa using hF)
  have h2iff : (2 : F) ≠ 0 ↔ p ≠ 2 := by
    constructor
    · rintro h rfl
      exact h (by exact_mod_cast CharP.cast_eq_zero F 2)
    · intro hp2 h
      have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
      rw [CharP.cast_eq_zero_iff F p] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have hA5two : p = 2 → Even f →
      ∃ H : Subgroup (PSL2MatrixGroup F), Nonempty (H ≃* alternatingGroup (Fin 5)) := by
    rintro rfl ⟨r, hr⟩
    obtain ⟨φ⟩ := nonempty_galoisField_ringHom hF (show 2 ∣ f from ⟨r, by omega⟩)
    obtain ⟨e⟩ := nonempty_psl2_galoisField_four_mulEquiv
    exact exists_subgroup_of_injective (φ := (psl2Map φ).comp e.symm.toMonoidHom)
      ((psl2Map_injective φ).comp e.symm.injective)
  refine ⟨fun m hm => exists_elementaryAbelian_subgroup hF hm,
    fun z hz => exists_cyclic_subgroup hF hz, fun z _ hz => exists_dihedral_subgroup hF hz,
    fun m hm => exists_psl2_subfield_subgroup hF hm,
    fun m hm => exists_pgl2_subfield_subgroup hF hm, ?_, ?_, ?_⟩
  ·
    rintro (hodd | heven)
    · have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) even_two
      exact QuatTable.exists_alternatingFour_subgroup (h2iff.mpr hp2)
    · by_cases hp2 : p = 2
      · obtain ⟨H, ⟨e⟩⟩ := hA5two hp2 heven
        obtain ⟨φ, hφ⟩ := exists_injective_alternatingFour_alternatingFive
        exact exists_subgroup_of_injective (φ := H.subtype.comp (e.symm.toMonoidHom.comp φ))
          (((Subgroup.subtype_injective H).comp e.symm.injective).comp hφ)
      · exact QuatTable.exists_alternatingFour_subgroup (h2iff.mpr hp2)
  ·
    intro h16
    have hq : Fintype.card F = p ^ f := by rw [← Nat.card_eq_fintype_card, hF]
    have h16' : (p ^ f) ^ 2 % 16 = 1 := h16
    have hmod8 : p ^ f % 8 = 1 ∨ p ^ f % 8 = 7 := by
      have : (p ^ f) ^ 2 % 16 = (p ^ f % 16) ^ 2 % 16 := Nat.pow_mod _ 2 16
      have hlt : p ^ f % 16 < 16 := Nat.mod_lt _ (by norm_num)
      have h8 : p ^ f % 8 = (p ^ f % 16) % 8 := (Nat.mod_mod_of_dvd _ (by norm_num)).symm
      interval_cases hr : p ^ f % 16 <;> simp_all
    have hp2 : p ≠ 2 := by
      rintro rfl
      have hf0 : f ≠ 0 := BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF
      have : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
      omega
    have hsq : IsSquare (2 : F) := by
      rw [FiniteField.isSquare_two_iff, hq]
      omega
    exact QuatTable.exists_permFour_subgroup (h2iff.mpr hp2) hsq
  ·
    intro h5
    by_cases hp2 : p = 2
    · subst hp2
      rcases h5 with h | h
      · exact absurd h (by norm_num)
      · apply hA5two rfl
        by_contra hodd
        rw [Nat.not_even_iff_odd] at hodd
        obtain ⟨r, rfl⟩ := hodd
        have h' : (2 ^ (2 * r + 1)) ^ 2 % 5 = 1 := h
        have h1 : (2 ^ (2 * r + 1)) ^ 2 = 4 * 16 ^ r := by
          rw [← pow_mul, show (2 * r + 1) * 2 = 4 * r + 2 by ring, pow_add, pow_mul]
          norm_num
          ring
        rw [h1, Nat.mul_mod, Nat.pow_mod] at h'
        norm_num at h'
    · obtain ⟨s, hs⟩ := isSquare_five hF hp2 h5
      have h2 : (2 : F) ≠ 0 := h2iff.mpr hp2
      refine QuatTable.exists_alternatingFive_subgroup h2 (θ := (1 + s) / 2) ?_
      field_simp
      linear_combination hs.symm

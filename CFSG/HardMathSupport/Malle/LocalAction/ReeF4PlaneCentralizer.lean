module

public import CFSG.RankThree.PartOne.K128.ReeShape
public import CFSG.RankThree.PartOne.KE8F.FamBruhat
public import CFSG.RankThree.PartOne.KE.F4Regular

public section

namespace CFSG.HardMathSupport.Malle.LocalAction

open CFSG.Open CFSG.RankThree.PartOne.K1214

section Group

abbrev V5 := Fin 2 → Multiplicative (ZMod (5 ^ 2))

theorem card_ker5 : Nat.card (powMonoidHom 5 : V5 →* V5).ker = 25 := by
  rw [Nat.card_eq_fintype_card]
  have : Fintype.card (powMonoidHom 5 : V5 →* V5).ker = Fintype.card {x : V5 // x ^ 5 = 1} := by
    apply Fintype.card_congr
    exact Equiv.subtypeEquivRight (fun x => by simp [MonoidHom.mem_ker])
  rw [this, Fintype.card_subtype]
  decide +kernel

theorem mem_sylow_iff_conj {Γ : Type*} [Group Γ] {P P' : Sylow 5 Γ} {g : Γ} (h : g • P' = P)
    (x : Γ) :
    x ∈ (P : Subgroup Γ) ↔ g⁻¹ * x * g ∈ (P' : Subgroup Γ) := by
  rw [← h]
  have := Sylow.coe_smul (g := g) (P := P')
  show x ∈ ((g • P' : Sylow 5 Γ) : Set Γ) ↔ _
  rw [this, Set.mem_smul_set_iff_inv_smul_mem]
  simp [MulAut.smul_def]
  exact Iff.rfl

theorem plane_unique {Γ : Type*} [Group Γ] {P' : Subgroup Γ} (e : P' ≃* V5)
    {E E' : Subgroup Γ} (hEP : E ≤ P') (hEP' : E' ≤ P')
    (hE : ∀ x ∈ E, x ^ 5 = 1) (hE' : ∀ x ∈ E', x ^ 5 = 1)
    (hc : Nat.card E = 25) (hc' : Nat.card E' = 25) : E = E' := by
  have key : ∀ F : Subgroup Γ, F ≤ P' → (∀ x ∈ F, x ^ 5 = 1) → Nat.card F = 25 →
      (F.subgroupOf P').map e.toMonoidHom = (powMonoidHom 5 : V5 →* V5).ker := by
    intro F hF h5 hcF
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      rw [MonoidHom.mem_ker]
      show (e y) ^ 5 = 1
      rw [← map_pow]
      have : y ^ 5 = 1 := Subtype.ext (h5 _ hy)
      rw [this, map_one]
    · rw [card_ker5, Subgroup.card_map_of_injective e.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv, hcF]
  have h1 := key E hEP hE hc
  have h2 := key E' hEP' hE' hc'
  have h3 : E.subgroupOf P' = E'.subgroupOf P' := by
    have := h1.trans h2.symm
    exact Subgroup.map_injective e.injective this
  ext x
  constructor
  · intro hx
    have : (⟨x, hEP hx⟩ : P') ∈ E.subgroupOf P' := hx
    rw [h3] at this
    exact this
  · intro hx
    have : (⟨x, hEP' hx⟩ : P') ∈ E'.subgroupOf P' := hx
    rw [← h3] at this
    exact this

theorem centralizer_plane_eq_sylow_of_data {Γ : Type*} [Group Γ] [Finite Γ]
    (hshape : SylowShape 5 2 2 Γ) {E₀ : Subgroup Γ} (hE₀ : IsElemAbelian 5 E₀)
    (hE₀c : Nat.card E₀ = 5 ^ 2)
    (hexp : ∀ γ ∈ Subgroup.centralizer (E₀ : Set Γ), γ ^ 625 = 1)
    (P : Sylow 5 Γ) (E : Subgroup Γ) (hEP : E ≤ (P : Subgroup Γ)) (hE : IsElemAbelian 5 E)
    (hEc : Nat.card E = 5 ^ 2) :
    Subgroup.centralizer (E : Set Γ) = (P : Subgroup Γ) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set C := Subgroup.centralizer (E₀ : Set Γ) with hCdef
  have hE₀C : E₀ ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hE₀.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hCp : IsPGroup 5 C := fun g => ⟨4, Subtype.ext (hexp g.1 g.2)⟩
  obtain ⟨P', hP'⟩ := hCp.exists_le_sylow
  obtain ⟨eP⟩ := hshape (P' : Subgroup Γ) P'.isPGroup' P'.not_dvd_index
  have hcomm : ∀ x ∈ (P' : Subgroup Γ), ∀ y ∈ (P' : Subgroup Γ), x * y = y * x := by
    intro x hx y hy
    have := mul_comm (eP ⟨x, hx⟩) (eP ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val (eP.injective this)
  have hPC : (P' : Subgroup Γ) ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y (hP' (hE₀C hy)) x hx
  have hCeq : C = (P' : Subgroup Γ) := le_antisymm hP' hPC
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ P' P
  have hmem := mem_sylow_iff_conj hg
  set E' : Subgroup Γ := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hE'P' : E' ≤ (P' : Subgroup Γ) := by
    rintro _ ⟨y, hy, rfl⟩
    have := (hmem y).1 (hEP hy)
    simpa [MulAut.conj_apply] using this
  have hE'5 : ∀ x ∈ E', x ^ 5 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hE.2 y hy, map_one]
  have hE'c : Nat.card E' = 25 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEc]; norm_num
  have hEE : E' = E₀ :=
    plane_unique eP hE'P' (hCeq ▸ hE₀C) hE'5 hE₀.2 hE'c (by rw [hE₀c]; norm_num)
  ext x
  rw [Subgroup.mem_centralizer_iff, hmem x, ← hCeq, hCdef, Subgroup.mem_centralizer_iff]
  constructor
  · intro h z hz
    have hz' : z ∈ E' := hEE ▸ hz
    obtain ⟨y, hy, rfl⟩ := hz'
    have := h y hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * x * g) = g⁻¹ * (y * x) * g := by group
      _ = g⁻¹ * (x * y) * g := by rw [this]
      _ = g⁻¹ * x * g * (g⁻¹ * y * g⁻¹⁻¹) := by group
  · intro h y hy
    have hz : g⁻¹ * y * g ∈ E₀ := hEE ▸ ⟨y, hy, by simp⟩
    have := h _ hz
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
      _ = x * y := by group

end Group

section Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.RF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KEXC CFSG.RankThree.PartOne.K1214
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.Lattice CFSG.RankThree.PartOne
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.K128

theorem exp625_add {A : Type*} [AddCommGroup A] (x0 x1 x2 x3 : A)
    (e0 : -x0 + -x1 + -((2 : ℕ) • x2) = (8 : ℕ) • x3)
    (e1 : -x1 = (8 : ℕ) • x2)
    (e2 : x1 + x2 = (4 : ℕ) • x1)
    (e3 : x0 + x1 + x2 + x3 = (4 : ℕ) • x0) :
    (625 : ℤ) • x0 = 0 ∧ (625 : ℤ) • x1 = 0 ∧ (625 : ℤ) • x2 = 0 ∧ (625 : ℤ) • x3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := module) (-25 : ℤ) • e0 + (-25 : ℤ) • e1 + (-50 : ℤ) • e2 + (-200 : ℤ) • e3
  · linear_combination (norm := module) (-25 : ℤ) • e1 + (-200 : ℤ) • e2
  · linear_combination (norm := module) (-75 : ℤ) • e1 + (25 : ℤ) • e2
  · linear_combination (norm := module) (-75 : ℤ) • e0 + (25 : ℤ) • e1 + (25 : ℤ) • e2 + (25 : ℤ) • e3

theorem exp625_mul {G : Type*} [CommGroup G] (b0 b1 b2 b3 : G)
    (h0 : b0⁻¹ * b1⁻¹ * (b2 ^ 2)⁻¹ = b3 ^ 8)
    (h1 : b1⁻¹ = b2 ^ 8)
    (h2 : b1 * b2 = b1 ^ 4)
    (h3 : b0 * b1 * b2 * b3 = b0 ^ 4) :
    b0 ^ 625 = 1 ∧ b1 ^ 625 = 1 ∧ b2 ^ 625 = 1 ∧ b3 ^ 625 = 1 := by
  have := exp625_add (Additive.ofMul b0) (Additive.ofMul b1) (Additive.ofMul b2)
    (Additive.ofMul b3)
    (by simpa [ofMul_mul, ofMul_pow] using congrArg Additive.ofMul h0)
    (by simpa [ofMul_mul, ofMul_pow] using congrArg Additive.ofMul h1)
    (by simpa [ofMul_mul, ofMul_pow] using congrArg Additive.ofMul h2)
    (by simpa [ofMul_mul, ofMul_pow] using congrArg Additive.ofMul h3)
  have key : ∀ b : G, (625 : ℤ) • Additive.ofMul b = 0 → b ^ 625 = 1 := fun b h => by
    have h' : Additive.ofMul (b ^ (625 : ℤ)) = Additive.ofMul 1 := by
      rw [ofMul_zpow]; exact h
    simpa using Additive.ofMul.injective h'
  exact ⟨key _ this.1, key _ this.2.1, key _ this.2.2.1, key _ this.2.2.2⟩


section Exp



theorem exponent_625_of_mem_twistedFixed_phi4m {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]
    {F : MulAut (adjointGroup ReeTag.F4.tag L)} (hF : IsReeFrob 2 F)
    {b : Fin ReeTag.F4.tag.rank → Lˣ}
    (hb : rootDiagUnit ReeTag.F4.tag b ∈
      twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4m)) :
    ∀ k, b k ^ 625 = 1 := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  rw [rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF] at hb
  have hprod : ∀ f : Fin ReeTag.F4.tag.rank → Lˣ, ∏ i, f i = f 0 * f 1 * f 2 * f 3 :=
    fun f => Fin.prod_univ_four f
  have hcol : ∀ k : Fin ReeTag.F4.tag.rank,
      rootChar b (wPhi4m • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      b ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) ^
        (![2 ^ 2, 2 ^ 2, 2 ^ (2 + 1), 2 ^ (2 + 1)] : Fin 4 → ℤ)
          ((![3, 2, 1, 0] : Fin 4 → Fin 4) k) := by
    intro k
    rw [hb, CTTorus.rootChar_single]
    show b (ReeTag.F4.perm k) ^ ReeTag.F4.relationExponent 2 (ReeTag.F4.perm k) = _
    rw [← zpow_natCast, relExp_vec, perm_vec]
  have hmat : ∀ k i : Fin ReeTag.F4.tag.rank,
      (wPhi4m • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) i =
        lget [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] i k :=
    fun k i => smul_single_eq_lget _ _ hW k i
  have hc : ∀ k, rootChar b (wPhi4m • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) =
      b 0 ^ lget [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] 0 k *
      b 1 ^ lget [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] 1 k *
      b 2 ^ lget [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] 2 k *
      b 3 ^ lget [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] 3 k := by
    intro k
    simp only [rootChar, hmat]
    exact hprod _
  have c0 := hcol 0
  have c1 := hcol 1
  have c2 := hcol 2
  have c3 := hcol 3
  rw [hc] at c0 c1 c2 c3
  have hrank : ReeTag.F4.tag.rank = 4 := rfl
  simp [lget, hrank] at c0 c1 c2 c3
  have hall := exp625_mul (b 0) (b 1) (b 2) (b 3) c0 c1 c2 c3
  intro k
  fin_cases k
  exacts [hall.1, hall.2.1, hall.2.2.1, hall.2.2.2]

end Exp

section Twisted

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {a : ℕ}
  {F : MulAut (adjointGroup ReeTag.F4.tag L)}

theorem exists_hom_twisted_aux_explicit (hF : IsReeFrob a F) (w : WeylGroup ReeTag.F4.tag) {m : ℕ}
    (hm : Odd m) (Wm : Matrix (Fin ReeTag.F4.tag.rank) (Fin ReeTag.F4.tag.rank) ℤ)
    (U : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ) (i j : Fin ReeTag.F4.tag.rank)
    (hW : ∀ k l : Fin ReeTag.F4.tag.rank,
      (w • (Pi.single k 1 : Fin ReeTag.F4.tag.rank → ℤ)) l = Wm l k)
    (hdet : IsCoprime (U 0 i * U 1 j - U 0 j * U 1 i) (m : ℤ))
    (hfix : ∀ (s : Fin 2) (k : Fin ReeTag.F4.tag.rank),
      (∑ l, U s l * Wm l k) ≡
        U s (ReeTag.F4.perm k) * (ReeTag.F4.relationExponent a (ReeTag.F4.perm k) : ℤ) [ZMOD m]) :
    ∃ Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U) := by
  classical
  have hm2 : ¬ 2 ∣ m := by
    rintro ⟨c, hc⟩
    exact (Nat.not_even_iff_odd.2 hm) ⟨c, by omega⟩
  have hm0 : (m : L) ≠ 0 := fun h => hm2 ((CharP.cast_eq_zero_iff L 2 m).1 h)
  have : NeZero m := ⟨fun h => hm2 (by simp [h])⟩
  have : NeZero (m : L) := ⟨hm0⟩
  let φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* (Fin ReeTag.F4.tag.rank → Lˣ) :=
    { toFun := fun z => expTuple (z.1 : Lˣ) (z.2 : Lˣ) U
      map_one' := by
        funext l
        simp [expTuple]
      map_mul' := fun z z' => by
        simpa using expTuple_mul (z.1 : Lˣ) (z.2 : Lˣ) (z'.1 : Lˣ) (z'.2 : Lˣ) U }
  let Φ : (rootsOfUnity m L) × (rootsOfUnity m L) →* ModGL ReeTag.F4.tag L :=
    (rootDiagUnitHom ReeTag.F4.tag L).comp φ
  have hΦ : ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag (expTuple (z.1 : Lˣ) (z.2 : Lˣ) U) :=
    fun z => rfl
  have hroot : ∀ z : (rootsOfUnity m L) × (rootsOfUnity m L),
      (z.1 : Lˣ) ^ m = 1 ∧ (z.2 : Lˣ) ^ m = 1 :=
    fun z => ⟨(mem_rootsOfUnity m _).1 z.1.2, (mem_rootsOfUnity m _).1 z.2.2⟩
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro z hz
    rw [hΦ, ← rootDiagUnit_one] at hz
    have hb := rootDiagUnit_injective hz
    have hA : (z.1 : Lˣ) ^ U 0 i * (z.2 : Lˣ) ^ U 1 i = 1 := congrFun hb i
    have hB : (z.1 : Lˣ) ^ U 0 j * (z.2 : Lˣ) ^ U 1 j = 1 := congrFun hb j
    obtain ⟨hm1, hm2'⟩ := hroot z
    have h1 := zpow_minor_eq_one hA hB
    have h2 := zpow_minor_eq_one (x := (z.2 : Lˣ)) (y := (z.1 : Lˣ)) (by rwa [mul_comm] at hA)
      (by rwa [mul_comm] at hB)
    have h2' : (z.2 : Lˣ) ^ (U 0 i * U 1 j - U 0 j * U 1 i) = 1 := by
      have : U 1 i * U 0 j - U 1 j * U 0 i = -(U 0 i * U 1 j - U 0 j * U 1 i) := by ring
      rw [this, zpow_neg, inv_eq_one] at h2
      exact h2
    have e1 := zpow_eq_one_of_coprime hm1 h1 hdet
    have e2 := zpow_eq_one_of_coprime hm2' h2' hdet
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  refine ⟨Φ, hinj, ?_, hΦ⟩
  · rintro _ ⟨z, rfl⟩
    rw [hΦ, rootDiagUnit_mem_twistedFixed_canonicalRep_iff hF w]
    apply rootChar_smul_eq_of_forall_single
    intro k
    obtain ⟨hm1, hm2'⟩ := hroot z
    rw [rootChar_expTuple, CTTorus.rootChar_single, reeTuple, expTuple]
    have hpow : ∀ (n : ℕ) (x : Lˣ), x ^ n = x ^ (n : ℤ) := fun n x => (zpow_natCast x n).symm
    rw [hpow, mul_zpow, ← zpow_mul, ← zpow_mul]
    congr 1
    · refine zpow_eq_zpow_of_modEq hm1 ?_
      have h0 := hfix 0 k
      simp only [hW] at *
      exact h0
    · refine zpow_eq_zpow_of_modEq hm2' ?_
      have h1 := hfix 1 k
      simp only [hW] at *
      exact h1

theorem exists_hom_phi4m_five (hF : IsReeFrob 2 F) :
    ∃ Φ : (rootsOfUnity 5 L) × (rootsOfUnity 5 L) →* ModGL ReeTag.F4.tag L,
      Function.Injective Φ ∧
      Φ.range ≤ twistedFixed F (canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4m) ∧
      ∀ z, Φ z = rootDiagUnit ReeTag.F4.tag
        (expTuple (z.1 : Lˣ) (z.2 : Lˣ)
          (![![-1, 0, 0, 1 - 2 ^ 2], ![-1, -1, 1 - 2 ^ 2, 1]] :
            Fin 2 → Fin ReeTag.F4.tag.rank → ℤ)) := by
  have hW : wordMat ReeTag.F4.tag [0, 1, 0, 2, 1, 0] =
      toMat ReeTag.F4.tag.rank [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]] :=
    wordMat_eq_toMat .F4 _ (by decide +kernel)
  refine exists_hom_twisted_aux_explicit hF wPhi4m (m := 5) (by decide)
    (toMat 4 [[-1, 0, 0, 1], [-1, -1, 1, 1], [-2, 0, 1, 1], [0, 0, 0, 1]])
    ![![-1, 0, 0, 1 - 2 ^ 2], ![-1, -1, 1 - 2 ^ 2, 1]] 0 1
    (fun k l => smul_single_eq_lget _ _ hW k l) ?_ ?_
  · exact ⟨1, 0, by norm_num⟩
  · intro s k
    have e : (ReeTag.F4.perm k : Fin 4) = (![3, 2, 1, 0] : Fin 4 → Fin 4) k := perm_vec k
    have h2 : (ReeTag.F4.relationExponent 2 (ReeTag.F4.perm k) : ℤ) =
        (![2 ^ 2, 2 ^ 2, 2 ^ (2 + 1), 2 ^ (2 + 1)] : Fin 4 → ℤ) (ReeTag.F4.perm k) :=
      relExp_vec 2 _
    rw [h2, e]
    fin_cases s <;> fin_cases k <;> simp [toMat, lget] <;> decide

abbrev planeU : Fin 2 → Fin ReeTag.F4.tag.rank → ℤ := ![![-1, 0, 0, 1 - 2 ^ 2], ![-1, -1, 1 - 2 ^ 2, 1]]

theorem regular_roots_phi4m : ∀ β ∈ rootFinset ReeTag.F4.tag,
    ¬ ((∑ i, planeU 0 i * β i) % 5 = 0 ∧ (∑ i, planeU 1 i * β i) % 5 = 0) := by
  decide +kernel

theorem regular_famKernel_phi4m {L : Type} [Field L] {ζ : Lˣ} (hζ : orderOf ζ = 5) :
    famKernel (τ := ReeTag.F4.tag)
      ({expTuple ζ 1 planeU, expTuple 1 ζ planeU} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) = ∅ := by
  have hprim : IsPrimitiveRoot ζ 5 := IsPrimitiveRoot.iff_orderOf.2 hζ
  refine Set.eq_empty_iff_forall_notMem.2 fun α hα => ?_
  obtain ⟨hroot, hall⟩ := hα
  have h1 := hall _ (Set.mem_insert _ _)
  have h2 := hall _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [rootChar_expTuple, one_zpow, mul_one, hprim.zpow_eq_one_iff_dvd] at h1
  rw [rootChar_expTuple, one_zpow, one_mul, hprim.zpow_eq_one_iff_dvd] at h2
  exact regular_roots_phi4m α (mem_rootFinset.2 hroot)
    ⟨Int.emod_eq_zero_of_dvd (by exact_mod_cast h1), Int.emod_eq_zero_of_dvd (by exact_mod_cast h2)⟩

end Twisted

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L 2] [IsAlgClosed L]

omit [CharP L 2] [IsAlgClosed L] in
theorem exists_hom_reeGamma_explicit (D : ReeFrameData K L a) (w : WeylGroup ReeTag.F4.tag)
    {G₀ : Type*} [Group G₀] (φ : G₀ →* ModGL ReeTag.F4.tag L) (hφ : Function.Injective φ)
    (hφF : φ.range ≤ twistedFixed D.F (canonicalRep (coxeterSystem ReeTag.F4.tag) L w)) :
    ∃ g₀ : ModGL ReeTag.F4.tag L, g₀ ∈ adjointGroup ReeTag.F4.tag L ∧
      Fext D.F g₀ = g₀ * canonicalRep (coxeterSystem ReeTag.F4.tag) L w ∧
      ∃ Ψ : G₀ →* ReeTag.F4.reeGamma K a, Function.Injective Ψ ∧
        ∀ z, thetaGamma L a (Ψ z) = g₀ * φ z * g₀⁻¹ := by
  classical
  set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L w with hn
  have hnadj : n ∈ adjointGroup ReeTag.F4.tag L := canonicalRep_mem_adjointGroup _ L w
  obtain ⟨h, hh⟩ := D.lang ⟨n, hnadj⟩
  have hFh : D.F h = h * ⟨n, hnadj⟩ := by
    rw [hh]
    group
  set g₀ : ModGL ReeTag.F4.tag L := (h : ModGL ReeTag.F4.tag L) with hg₀
  have hg₀adj : g₀ ∈ adjointGroup ReeTag.F4.tag L := h.2
  have hFg₀ : Fext D.F g₀ = g₀ * n := by
    rw [Fext_of_mem D.F hg₀adj]
    have : (⟨g₀, hg₀adj⟩ : adjointGroup ReeTag.F4.tag L) = h := rfl
    rw [this, hFh]
    rfl
  have hθ : ∀ z, ∃ γ : ReeTag.F4.reeGamma K a, thetaGamma L a γ = g₀ * φ z * g₀⁻¹ := by
    intro z
    obtain ⟨hadj, hfix⟩ := fixed_of_mem_twistedFixed D.F hg₀adj hFg₀ (hφF ⟨z, rfl⟩)
    exact D.exists_theta_of_fixed hadj hfix
  choose ψ hψ using hθ
  have hinjθ := thetaGamma_injective (K := K) L (a := a)
  let Ψ : G₀ →* ReeTag.F4.reeGamma K a :=
    { toFun := ψ
      map_one' := by
        apply hinjθ
        rw [hψ, map_one, map_one]
        group
      map_mul' := fun z z' => by
        apply hinjθ
        rw [map_mul (thetaGamma L a) (ψ z) (ψ z'), hψ (z * z'), hψ z, hψ z', map_mul φ z z']
        group }
  refine ⟨g₀, hg₀adj, hFg₀, Ψ, fun z z' hzz => ?_, hψ⟩
  have h1 : g₀ * φ z * g₀⁻¹ = g₀ * φ z' * g₀⁻¹ := by
    rw [← hψ z, ← hψ z']
    exact congrArg _ hzz
  have h2 : φ z = φ z' := mul_left_cancel (mul_right_cancel h1)
  exact hφ h2

theorem exists_plane_exponent_625 (D : ReeFrameData K L 2) :
    ∃ E₀ : Subgroup (ReeTag.F4.reeGamma K 2), CFSG.Open.IsElemAbelian 5 E₀ ∧
      Nat.card E₀ = 5 ^ 2 ∧
      ∀ γ ∈ Subgroup.centralizer (E₀ : Set (ReeTag.F4.reeGamma K 2)), γ ^ 625 = 1 := by
  classical
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hpL : (5 : L) ≠ 0 := fun h => by
    have := (CharP.cast_eq_zero_iff L 2 5).1 (by exact_mod_cast h)
    omega
  have : NeZero (5 : ℕ) := ⟨by norm_num⟩
  have : NeZero ((5 : ℕ) : L) := ⟨by exact_mod_cast hpL⟩
  obtain ⟨Φ, hΦinj, hΦF, hΦ⟩ := exists_hom_phi4m_five D.isFrob
  obtain ⟨g₀, hg₀, hFg₀, Ψ, hΨinj, hΨ⟩ :=
    exists_hom_reeGamma_explicit D wPhi4m Φ hΦinj hΦF
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  lift ζ₀ to Lˣ using hζ₀.isUnit (by norm_num)
  rw [IsPrimitiveRoot.coe_units_iff] at hζ₀
  have hζord : orderOf ζ₀ = 5 := hζ₀.eq_orderOf.symm
  have hζ5 : ζ₀ ^ 5 = 1 := hζ₀.pow_eq_one
  let ζr : rootsOfUnity 5 L := ⟨ζ₀, (mem_rootsOfUnity 5 ζ₀).2 hζ5⟩
  refine ⟨Ψ.range, ⟨inferInstance, ?_⟩, ?_, ?_⟩
  · rintro _ ⟨z, rfl⟩
    rw [← map_pow]
    have : z ^ 5 = 1 := by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · exact (mem_rootsOfUnity 5 _).1 z.1.2
      · exact (mem_rootsOfUnity 5 _).1 z.2.2
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΨinj).toEquiv, Nat.card_prod]
    have := card_rootsOfUnity_pow (p := 5) (e := 1) (L := L) hpL
    rw [pow_one] at this
    rw [this]
    norm_num
  · intro γ hγ
    rw [Subgroup.mem_centralizer_iff] at hγ
    set n := canonicalRep (coxeterSystem ReeTag.F4.tag) L wPhi4m with hn
    set u : ModGL ReeTag.F4.tag L := g₀⁻¹ * thetaGamma L 2 γ * g₀ with hu
    have hu_tw : u ∈ twistedFixed D.F n :=
      conj_mem_twistedFixed D.F hg₀ hFg₀ (thetaGamma_mem_adjointGroup L γ) (D.fext_theta γ)
    have hcomm : ∀ z, u * Φ z = Φ z * u := by
      intro z
      have h1 := hγ (Ψ z) ⟨z, rfl⟩
      have h2 := congrArg (thetaGamma L 2) h1
      rw [map_mul, map_mul, hΨ] at h2
      calc u * Φ z = g₀⁻¹ * (thetaGamma L 2 γ * (g₀ * Φ z * g₀⁻¹)) * g₀ := by rw [hu]; group
        _ = g₀⁻¹ * ((g₀ * Φ z * g₀⁻¹) * thetaGamma L 2 γ) * g₀ := by rw [h2]
        _ = Φ z * u := by rw [hu]; group
    set a₁ : Fin ReeTag.F4.tag.rank → Lˣ := expTuple ζ₀ 1 planeU with ha₁
    set a₂ : Fin ReeTag.F4.tag.rank → Lˣ := expTuple 1 ζ₀ planeU with ha₂
    have hΦ₁ : Φ (ζr, 1) = rootDiagUnit ReeTag.F4.tag a₁ := by
      rw [hΦ]; rfl
    have hΦ₂ : Φ (1, ζr) = rootDiagUnit ReeTag.F4.tag a₂ := by
      rw [hΦ]; rfl
    have hFam : ∀ a ∈ ({a₁, a₂} : Set (Fin ReeTag.F4.tag.rank → Lˣ)),
        u * rootDiagUnit ReeTag.F4.tag a = rootDiagUnit ReeTag.F4.tag a * u := by
      intro a ha
      rcases Set.mem_insert_iff.1 ha with h | h
      · rw [h, ← hΦ₁]; exact hcomm _
      · rw [Set.mem_singleton_iff.1 h, ← hΦ₂]; exact hcomm _
    have hord : ¬ 5 ∣ Nat.card (WeylGroup ReeTag.F4.tag) :=
      not_dvd_card_weylGroup_F4 Nat.prime_five (by norm_num)
    have hF5 : ∀ a ∈ ({a₁, a₂} : Set (Fin ReeTag.F4.tag.rank → Lˣ)), ∀ i, a i ^ 5 = 1 := by
      intro a ha i
      have hz : ∀ k : ℤ, (ζ₀ ^ k) ^ 5 = 1 := fun k => by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ5, one_zpow]
      rcases Set.mem_insert_iff.1 ha with h | h
      · rw [h, ha₁, expTuple]
        simpa using hz (planeU 0 i)
      · rw [Set.mem_singleton_iff.1 h, ha₂, expTuple]
        simpa using hz (planeU 1 i)
    have hstab := famStabilizer_subset_closure (τ := ReeTag.F4.tag) (L := L) Nat.prime_five hord
      hζord ({a₁, a₂} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) hF5
    have hker : famKernel (τ := ReeTag.F4.tag)
        ({a₁, a₂} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) ⊆ (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := by
      rw [ha₁, ha₂, regular_famKernel_phi4m hζord]
    obtain ⟨t, ht, q, hq, htq⟩ := mem_torus_mul_rootSpan_of_commute_fam
      ({a₁, a₂} : Set (Fin ReeTag.F4.tag.rank → Lˣ)) hstab (S := ∅) (fun α hα => hα.elim)
      (fun α hα => hα.elim) hker hu_tw.1 hFam
    have hbot : rootSpan ReeTag.F4.tag L (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) = ⊥ := by
      simp [rootSpan]
    have hq1 : q = 1 := by
      have : q ∈ rootSpan ReeTag.F4.tag L (∅ : Set (Fin ReeTag.F4.tag.rank → ℤ)) := hq
      rw [hbot] at this
      exact this
    have htu : t = u := by
      subst hq1
      simpa using htq
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (htu ▸ ht)
    have hb625 := exponent_625_of_mem_twistedFixed_phi4m D.isFrob (b := b) (by rw [← hb]; exact hu_tw)
    have hu625 : u ^ 625 = 1 := by
      have h := (map_pow (rootDiagUnitHom ReeTag.F4.tag L) b 625).symm
      have hb1 : b ^ 625 = 1 := funext fun k => by simpa using hb625 k
      rw [hb1, map_one] at h
      rw [hb]
      exact h
    apply thetaGamma_injective L (K := K) (a := 2)
    rw [map_pow, map_one]
    have hθ : thetaGamma L 2 γ = g₀ * u * g₀⁻¹ := by rw [hu]; group
    have hc := map_pow (MulAut.conj g₀) u 625
    simp only [MulAut.conj_apply] at hc
    rw [hθ, ← hc, hu625]
    group

end Frame

section Main

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem factorization_five_phi4 :
    (((2 ^ (2 * 2 + 1)) ^ 2 + 1 : ℕ)).factorization 5 = 2 := by
  have h : ((2 ^ (2 * 2 + 1)) ^ 2 + 1 : ℕ) = 5 ^ 2 * 41 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
  have h41 : (41 : ℕ).factorization 5 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  rw [Finsupp.add_apply, h41, Nat.Prime.factorization_pow Nat.prime_five]
  simp

theorem centralizer_plane_eq_sylow (hK : Nat.card K = 2 ^ (2 * 2 + 1))
    (P : Sylow 5 (ReeTag.F4.reeGamma K 2)) (E : Subgroup (ReeTag.F4.reeGamma K 2))
    (hEP : E ≤ (P : Subgroup (ReeTag.F4.reeGamma K 2))) (hE : CFSG.Open.IsElemAbelian 5 E)
    (hE25 : Nat.card E = 5 ^ 2) :
    Subgroup.centralizer (E : Set (ReeTag.F4.reeGamma K 2)) =
      (P : Subgroup (ReeTag.F4.reeGamma K 2)) := by
  classical
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K 2) := Subtype.finite
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := AlgebraicClosure K) hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨E₀, hE₀, hE₀c, hexp⟩ := exists_plane_exponent_625 D
  have hsh : SylowShape 5 2 2 (ReeTag.F4.reeGamma K 2) := by
    have := sylowShape_ree_phi4 (K := K) (a := 2) hK Nat.prime_five (by norm_num) (by norm_num)
    rwa [factorization_five_phi4] at this
  exact centralizer_plane_eq_sylow_of_data hsh hE₀ hE₀c hexp P E hEP hE hE25

end Main

end Lie

end CFSG.HardMathSupport.Malle.LocalAction

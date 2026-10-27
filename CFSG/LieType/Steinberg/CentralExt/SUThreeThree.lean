module

public import CFSG.LocalAnalysis.SectionRank.EvenCover.UnitaryThree
public import CFSG.RankThree.CentralLiftU.PerfectSplit

public section

namespace CFSG.LieType.Steinberg.CentralExt.SUThreeThree

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank
  CFSG.SectionRank.OddCover
open CFSG.SectionRank.EvenCover (blockGL blockSUid coe_blockGL blockMat_apply_castAdd
  blockMat_two_one blockGL_diagHom_two swapMat swapGL swapMat_mul_self)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

local notation "σ₀" => unitaryInvolution F p f

local notation "Mq" => CFSG.SectionRank.OddCover.normOne F (p ^ f)

theorem nonempty_sl2_mulEquiv_SUid_two (hF : Nat.card F = (p ^ f) ^ 2) :
    Nonempty (SpecialLinearGroup (Fin 2) (fixedSubfield F p f) ≃* SUid σ₀ 2) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  exact ⟨(hypEquiv hζ0 hζ).trans (conjEquiv P hP)⟩

theorem suidTwo_existsUnique_lift
    (hF : Nat.card F = (p ^ f) ^ 2) {E G : Type*} [Group E] [Group G] [Finite E] {π : E →* G}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : ¬ p ∣ Nat.card π.ker) (α : SUid σ₀ 2 →* G) :
    ∃! α' : SUid σ₀ 2 →* E, π.comp α' = α := by
  obtain ⟨Ψ⟩ := nonempty_sl2_mulEquiv_SUid_two hF
  obtain ⟨β, hβ, huniq⟩ := CFSG.SectionRank.EvenCover.sl2_existsUnique_lift (p := p) hπ hcen hC
    (α.comp Ψ.toMonoidHom)
  refine ⟨β.comp Ψ.symm.toMonoidHom, ?_, fun γ hγ => ?_⟩
  · ext g
    have := congrArg (· (Ψ.symm g)) hβ
    simpa using this
  · have hγ' : π.comp γ = α := hγ
    have h := huniq (γ.comp Ψ.toMonoidHom) (show π.comp (γ.comp Ψ.toMonoidHom) = _ by
      rw [← MonoidHom.comp_assoc, hγ'])
    ext g
    have := congrArg (· (Ψ.symm g)) h
    simpa using this

@[expose] noncomputable def pairEmb (hF : Nat.card F = (p ^ f) ^ 2) :
    SUid σ₀ 2 →* StatedSU 3 (p ^ f) F :=
  (MulEquiv.subgroupCongr (SUid_eq_statedSU hF 3)).toMonoidHom.comp (blockSUid (m := 1) σ₀)

theorem coe_pairEmb (hF : Nat.card F = (p ^ f) ^ 2) (g : SUid σ₀ 2) :
    ((pairEmb hF g : StatedSU 3 (p ^ f) F) : GL (Fin 3) F) = blockGL (m := 1) (g : GL (Fin 2) F) :=
  rfl

theorem pairEmb_injective (hF : Nat.card F = (p ^ f) ^ 2) : Function.Injective (pairEmb hF) := by
  intro g h hgh
  have e := congrArg (fun x : StatedSU 3 (p ^ f) F =>
    ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) hgh
  simp only [coe_pairEmb, coe_blockGL] at e
  apply Subtype.ext
  apply Units.ext
  ext i j
  have := congrFun (congrFun e (Fin.castAdd 1 i)) (Fin.castAdd 1 j)
  rwa [blockMat_apply_castAdd, blockMat_apply_castAdd] at this

theorem exists_pair_lift
    (hF : Nat.card F = (p ^ f) ^ 2) {E : Type*} [Group E] [Finite E]
    {π : E →* StatedSU 3 (p ^ f) F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hC : ¬ p ∣ Nat.card π.ker) :
    ∃ Q : Subgroup E, Q ⊓ π.ker = ⊥ ∧ Nat.card Q = p ^ f * ((p ^ f) ^ 2 - 1) := by
  obtain ⟨ρ, hρ, -⟩ := suidTwo_existsUnique_lift hF hπ hcen hC (pairEmb hF)
  have hρ' : ∀ g, π (ρ g) = pairEmb hF g := fun g => DFunLike.congr_fun hρ g
  have hinj : Function.Injective ρ := fun a b h => pairEmb_injective hF (by
    rw [← hρ', ← hρ', h])
  refine ⟨ρ.range, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro _ ⟨⟨g, rfl⟩, hg⟩
    have h1 : pairEmb hF g = 1 := by rw [← hρ']; exact hg
    have h2 : g = 1 := pairEmb_injective hF (h1.trans (map_one _).symm)
    rw [h2, map_one]
    exact Subgroup.one_mem _
  · obtain ⟨Ψ⟩ := nonempty_sl2_mulEquiv_SUid_two hF
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, ← Nat.card_congr Ψ.toEquiv,
      card_specialLinearGroup_fin_two, card_fixedSubfield hF]

theorem diagHom_two_mem {a : Fˣ} (ha : a ∈ Mq) : diagHom 2 ![a, a⁻¹] ∈ SUid σ₀ 2 := by
  rw [mem_SUid, det_diagHom, Fin.prod_univ_two]
  refine ⟨by simp, ?_⟩
  have ha' : a ^ (p ^ f + 1) = 1 := ha
  rw [coe_diagHom, conjTr, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  have hpow : ∀ c : Fˣ, c ^ (p ^ f + 1) = 1 → σ₀ (c : F) * c = 1 := fun c hc => by
    rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
  fin_cases i
  · exact hpow a ha'
  · exact hpow a⁻¹ (by rw [inv_pow, ha', inv_one])

@[expose] noncomputable def normDiagTwo : Mq →* SUid σ₀ 2 where
  toFun a := ⟨diagHom 2 ![(a : Fˣ), (a : Fˣ)⁻¹], diagHom_two_mem a.2⟩
  map_one' := Subtype.ext (by
    change diagHom 2 ![((1 : Mq) : Fˣ), ((1 : Mq) : Fˣ)⁻¹] = 1
    rw [← map_one (diagHom (K := F) 2)]
    congr 1
    funext i
    fin_cases i <;> simp)
  map_mul' a b := Subtype.ext (by
    change diagHom 2 ![((a * b : Mq) : Fˣ), ((a * b : Mq) : Fˣ)⁻¹] =
      diagHom 2 ![(a : Fˣ), (a : Fˣ)⁻¹] * diagHom 2 ![(b : Fˣ), (b : Fˣ)⁻¹]
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm])

theorem coe_normDiagTwo (a : Mq) :
    ((normDiagTwo a : SUid σ₀ 2) : GL (Fin 2) F) = diagHom 2 ![(a : Fˣ), (a : Fˣ)⁻¹] :=
  rfl

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem conjTr_swapMat_mul (σ : F ≃+* F) : conjTr σ (swapMat (K := F)) * swapMat = 1 := by
  have : conjTr σ (swapMat (K := F)) = swapMat := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjTr, swapMat]
  rw [this, swapMat_mul_self]

@[expose] noncomputable def swapConj (hF : Nat.card F = (p ^ f) ^ 2) : SUid σ₀ 2 →* SUid σ₀ 2 :=
  ((MulAut.conj (swapGL : GL (Fin 2) F)).toMonoidHom.comp (SUid σ₀ 2).subtype).codRestrict
    (SUid σ₀ 2) fun A =>
      conj_mem_SUid (unitaryInvolution_involutive hF) (conjTr_swapMat_mul σ₀) A.2

theorem coe_swapConj (hF : Nat.card F = (p ^ f) ^ 2) (A : SUid σ₀ 2) :
    ((swapConj hF A : SUid σ₀ 2) : GL (Fin 2) F) = swapGL * (A : GL (Fin 2) F) * swapGL⁻¹ :=
  rfl

theorem swapConj_normDiagTwo (hF : Nat.card F = (p ^ f) ^ 2) (a : Mq) :
    swapConj hF (normDiagTwo a) = (normDiagTwo a)⁻¹ := by
  rw [← map_inv]
  apply Subtype.ext
  apply Units.ext
  rw [coe_swapConj, Units.val_mul, Units.val_mul, coe_normDiagTwo, coe_normDiagTwo]
  change swapMat * _ * swapMat = _
  rw [coe_diagHom, coe_diagHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul,
      dotProduct]

omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem s01GL_conj_blockGL (A : GL (Fin 2) F) :
    s01GL * blockGL (m := 1) A * s01GL⁻¹ = blockGL (m := 1) (swapGL * A * swapGL⁻¹) := by
  apply Units.ext
  rw [s01GL_inv, Units.val_mul, Units.val_mul, coe_s01GL, coe_blockGL, coe_blockGL]
  change s01Mat * CFSG.SectionRank.EvenCover.blockMat (m := 1) (A : Matrix (Fin 2) (Fin 2) F) *
      s01Mat = CFSG.SectionRank.EvenCover.blockMat (m := 1) (swapMat * (A : Matrix _ _ F) * swapMat)
  rw [blockMat_two_one, blockMat_two_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s01Mat, swapMat, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct]

theorem exists_monomial_lift_odd
    (hF : Nat.card F = (p ^ f) ^ 2) {E : Type*} [Group E] [Finite E]
    {π : E →* StatedSU 3 (p ^ f) F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker))
    (hC : ¬ p ∣ Nat.card π.ker) :
    ∃ N : Subgroup E, N ⊓ π.ker = ⊥ ∧ Nat.card N = 3 * (p ^ f + 1) ^ 2 := by
  obtain ⟨ρ, hρ, -⟩ := suidTwo_existsUnique_lift hF hπ hcen hC (pairEmb hF)
  have hρ' : ∀ g, π (ρ g) = pairEmb hF g := fun g => DFunLike.congr_fun hρ g
  set φ : E →* GL (Fin 3) F := (StatedSU 3 (p ^ f) F).subtype.comp π with hφdef
  have hφker : φ.ker = π.ker := by
    ext e
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply,
      Subgroup.coe_subtype, OneMemClass.coe_eq_one]
  have hcenφ : φ.ker ≤ Subgroup.center E := hφker ▸ hcen
  have hoddφ : Odd (Nat.card φ.ker) := hφker ▸ hodd
  have hφρ : ∀ g, φ (ρ g) = blockGL (m := 1) (g : GL (Fin 2) F) := fun g => by
    rw [hφdef, MonoidHom.comp_apply, hρ']
    rfl
  obtain ⟨u, ⟨hu2, hu⟩, -⟩ := existsUnique_involution_lift hπ hcen hodd
    (s := ⟨s01GL, monomialData_statedSU.s01_mem⟩) (Subtype.ext s01GL_sq)
  obtain ⟨v, ⟨hv2, hv⟩, -⟩ := existsUnique_involution_lift hπ hcen hodd
    (s := ⟨s12GL, monomialData_statedSU.s12_mem⟩) (Subtype.ext s12GL_sq)
  have hu2' : u * u = 1 := by rw [← sq]; exact hu2
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2'
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hv2)
  set w := u * v with hw
  have hφu : φ u = s01GL := by rw [hφdef, MonoidHom.comp_apply, hu]; rfl
  have hφv : φ v = s12GL := by rw [hφdef, MonoidHom.comp_apply, hv]; rfl
  have hφw : φ w = cycGL := by rw [hw, map_mul, hφu, hφv, s01GL_mul_s12GL]
  have huw : u * w * u⁻¹ = w⁻¹ := by
    rw [hw, huinv, _root_.mul_inv_rev, huinv, hvinv, ← mul_assoc, hu2', one_mul]
  have hw3 : w ^ 3 = 1 := by
    have hk : w ^ 3 ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hφw, cycGL_pow_three]
    have hinv : u * w ^ 3 * u⁻¹ = (w ^ 3)⁻¹ := by
      rw [← conj_pow, huw, inv_pow]
    exact eq_one_of_sq_eq_one_of_odd (sq_eq_one_of_conj_eq_inv (hcenφ hk) hinv)
      (odd_orderOf_of_mem hoddφ hk)
  have hconj : (MulAut.conj u).toMonoidHom.comp ρ = ρ.comp (swapConj hF) := by
    refine (suidTwo_existsUnique_lift hF hπ hcen hC ((pairEmb hF).comp (swapConj hF))).unique
      (MonoidHom.ext fun A => Subtype.ext ?_) (by rw [← MonoidHom.comp_assoc, hρ])
    change φ (u * ρ A * u⁻¹) = blockGL (m := 1) ((swapConj hF A : SUid σ₀ 2) : GL (Fin 2) F)
    rw [map_mul, map_mul, map_inv, hφu, hφρ, coe_swapConj, s01GL_conj_blockGL]
  set x : Mq →* E := ρ.comp normDiagTwo with hx
  have hux : ∀ a, u * x a * u⁻¹ = (x a)⁻¹ := fun a => by
    have h := DFunLike.congr_fun hconj (normDiagTwo a)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, swapConj_normDiagTwo, map_inv] at h
    exact h
  have hφx : ∀ a : Mq, φ (x a) = diagHom 3 ![(a : Fˣ), (a : Fˣ)⁻¹, 1] := fun a => by
    change φ (ρ (normDiagTwo a)) = _
    rw [hφρ, coe_normDiagTwo, blockGL_diagHom_two]
    rfl
  have hφy : ∀ a : Mq, φ (w * x a * w⁻¹) = diagHom 3 ![1, (a : Fˣ), (a : Fˣ)⁻¹] := fun a => by
    rw [map_mul, map_mul, map_inv, hφw, hφx, cycGL_conj_diagHom]
    rfl
  have hφz : ∀ a : Mq, φ (w⁻¹ * x a * w) = diagHom 3 ![(a : Fˣ)⁻¹, 1, (a : Fˣ)] := fun a => by
    rw [map_mul, map_mul, map_inv, hφw, hφx]
    have h := cycGL_conj_diagHom (K := F) ![(a : Fˣ)⁻¹, 1, (a : Fˣ)]
    have e : ![(![(a : Fˣ)⁻¹, 1, (a : Fˣ)] : Fin 3 → Fˣ) 2, ![(a : Fˣ)⁻¹, 1, (a : Fˣ)] 0,
        ![(a : Fˣ)⁻¹, 1, (a : Fˣ)] 1] = ![(a : Fˣ), (a : Fˣ)⁻¹, 1] := by
      funext i
      fin_cases i <;> rfl
    rw [e] at h
    rw [← h]
    group
  have hcomm : ∀ a b : Mq, Commute (φ (w * x a * w⁻¹)) (φ (w⁻¹ * x b * w)) := fun a b => by
    rw [hφy, hφz]
    exact (Commute.all _ _).map (diagHom 3)
  have hprod : ∀ a : Mq, φ (x a * (w * x a * w⁻¹) * (w⁻¹ * x a * w)) = 1 := fun a => by
    rw [map_mul, map_mul, hφx, hφy, hφz, ← map_mul, ← map_mul, ← map_one (diagHom (K := F) 3)]
    congr 1
    funext i
    fin_cases i <;> simp
  obtain ⟨hxy, hxyz⟩ := CFSG.SectionRank.EvenCover.torus_lift_relations φ hcenφ hoddφ x hw3 huw
    hux hcomm hprod
  have hφτ : ∀ a b : Mq, φ (x a * (w * x (a * b) * w⁻¹)) = torusHom Mq (a, b) := fun a b => by
    rw [map_mul, hφx, hφy, torusHom_apply, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]
  have hw1 : ∀ k : ℕ, φ w ^ k ∈ (torusHom Mq).range → φ w ^ k = 1 := fun k hk => by
    rw [hφw] at hk ⊢
    have := zpow_cycGL_mem_torus3 Mq (k := k) (by rw [zpow_natCast]; exact hk)
    rwa [zpow_natCast] at this
  have hw0 : φ w ≠ 1 := by rw [hφw]; exact cycGL_ne_one
  obtain ⟨N, hN, hcard⟩ := CFSG.SectionRank.EvenCover.exists_monomial_lift φ x hw3 hxy hxyz
    (torusHom Mq) (torusHom_injective Mq) hφτ hw1 hw0
  refine ⟨N, hφker ▸ hN, ?_⟩
  rw [hcard, Nat.card_prod, card_normOne hF, sq]

theorem ker_eq_bot_of_perfect_three
    (hF : Nat.card F = (p ^ f) ^ 2) (hp3 : p ≠ 3) {P : Type*} [Group P] [Finite P]
    [Group.IsPerfect P] {π : P →* StatedSU 3 (p ^ f) F} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center P) (h3 : IsPGroup 3 π.ker) : π.ker = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h3
  have hodd : Odd (Nat.card π.ker) := by
    rw [hk]
    exact Odd.pow (by decide)
  have hC : ¬ p ∣ Nat.card π.ker := by
    rw [hk]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).1
      ((Fact.out : p.Prime).dvd_of_dvd_pow h))
  have hq2 : 2 ≤ p ^ f := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF
  have h3q : ¬ 3 ∣ p ^ f := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three
    Fact.out).1 (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have htop : IsPGroup 3 (⊤ : Subgroup π.ker) := h3.to_subgroup ⊤
  set Cp : Sylow 3 π.ker := htop.toSylow (by rw [Subgroup.index_top]; norm_num)
  have hCp : (Cp : Subgroup π.ker) = ⊤ := IsPGroup.toSylow_coe _ _
  have hbot : (Cp : Subgroup π.ker) = ⊥ := by
    by_cases h31 : 3 ∣ p ^ f + 1
    · obtain ⟨N, hN, hcard⟩ := exists_monomial_lift_odd hF hπ hcen hodd hC
      refine CFSG.SectionRank.EvenCover.sylow_kernel_eq_bot_of_inf_ker_eq_bot π hcen N hN ?_ Cp
      rw [hcard, card_statedSU_three hF]
      exact CFSG.SectionRank.EvenCover.factorization_SU_three_le_monomial Nat.prime_three
        (by norm_num) h3q hq2 h31
    · obtain ⟨Q, hQ, hcard⟩ := exists_pair_lift hF hπ hcen hC
      refine CFSG.SectionRank.EvenCover.sylow_kernel_eq_bot_of_inf_ker_eq_bot π hcen Q hQ ?_ Cp
      rw [hcard, card_statedSU_three hF]
      exact CFSG.SectionRank.EvenCover.factorization_SU_three_le_SU_two Nat.prime_three
        (by norm_num) h3q hq2 (by omega)
  rw [eq_bot_iff]
  intro x hx
  have h1 : (⟨x, hx⟩ : π.ker) ∈ (Cp : Subgroup π.ker) := hCp ▸ Subgroup.mem_top _
  rw [hbot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)

theorem su_three_exists_section_of_three
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    {E : Type*} [Group E] [Finite E] {π : E →* SU (unitaryInvolution F p f) 3}
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h3 : IsPGroup 3 π.ker) :
    ∃ s : SU (unitaryInvolution F p f) 3 →* E, ∀ g, π (s g) = g := by
  have : Group.IsPerfect (SU σ₀ 3) := isPerfect_SU_three hF hp2
  obtain ⟨hperf, hsurj, hkcen⟩ := CFSG.RankThree.CentralLiftU.derived_restrict_facts π hπ hcen
  have : Group.IsPerfect (commutator E) := hperf
  have h3' := CFSG.RankThree.CentralLiftU.isPGroup_ker_comp_subtype π h3 (commutator E)
  refine CFSG.RankThree.CentralLiftU.exists_section_of_ker_comp_eq_bot π (commutator E) hsurj ?_
  set e := equivStatedSU hF 3
  have hker : (e.toMonoidHom.comp (π.comp (commutator E).subtype)).ker =
      (π.comp (commutator E).subtype).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ e.injective]
  rw [← hker]
  exact ker_eq_bot_of_perfect_three hF hp3 (e.surjective.comp hsurj) (hker ▸ hkcen) (hker ▸ h3')

end CFSG.LieType.Steinberg.CentralExt.SUThreeThree

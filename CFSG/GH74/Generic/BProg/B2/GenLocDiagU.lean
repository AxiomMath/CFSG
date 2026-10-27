module

public import CFSG.GH74.Generic.BProg.B2.GenLocDiag
public import CFSG.ClassicalInvolution.Phan.Standard
public import CFSG.RankThree.PartOne.KF.UnitaryDiag
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.RankThree.PartOne.CTP.SeitzToral CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel Matrix

namespace GenLocDiagU

variable {K : Type} [Field K]

theorem blockMat_commute_diag {m i : ℕ} {d : Fin m → K}
    (hd : ∀ a b : Fin m, (i ≤ a.val ∧ a.val < i + 2) → (i ≤ b.val ∧ b.val < i + 2) → d a = d b)
    (A : Matrix (Fin 2) (Fin 2) K) :
    diagonal d * Phan.blockMat m i A = Phan.blockMat m i A * diagonal d := by
  ext a b
  rw [diagonal_mul, mul_diagonal, Phan.blockMat_apply]
  by_cases h : (i ≤ a.val ∧ a.val < i + 2) ∧ (i ≤ b.val ∧ b.val < i + 2)
  · rw [dite_eq_left h, hd a b h.1 h.2, mul_comm]
  · rw [dite_eq_right h]
    by_cases hab : a = b
    · subst hab
      simp [mul_comm]
    · simp [hab]

theorem unitaryFieldData_of_card [Finite K] {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) :
    UnitaryFieldData p f K := by
  refine ⟨hp, ?_, by rw [hK, ← pow_mul, mul_comm]⟩
  by_contra h0
  have hf : f = 0 := by omega
  subst hf
  have : Nat.card K = 1 := by simpa using hK
  exact (not_subsingleton K) (Nat.card_eq_one_iff_unique.1 this).1

theorem charP_of_card [Finite K] {p f : ℕ} (hp : p.Prime) (hK : Nat.card K = (p ^ f) ^ 2) :
    CharP K p :=
  (unitaryFieldData_of_card hp hK).charP

theorem pow_ne_two [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (p ^ f) ^ 2) : p ^ f ≠ 2 := by
  intro h
  have hf : f ≠ 0 := by
    have := (unitaryFieldData_of_card hp hK).one_le
    omega
  have : p ∣ 2 := h ▸ dvd_pow_self p hf
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem mem_primeFormUnitary_of_diag_sq {p f : ℕ} (h : UnitaryFieldData p f K) (hp2 : p ≠ 2) {n : ℕ}
    {P : GL (Fin n) K} (hdiag : ((P : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hsq : P * P = 1) : P ∈ primeFormUnitary h (idGram K n) := by
  have hq : Odd (p ^ f) := (h.prime.odd_of_ne_two hp2).pow
  have hbar : ∀ c : K, c * c = 1 → h.bar c = c := by
    intro c hc
    rcases mul_self_eq_one_iff.mp hc with rfl | rfl
    · simp [UnitaryFieldData.bar_apply]
    · simp [UnitaryFieldData.bar_apply, hq.neg_one_pow]
  have hmap : (P : Matrix (Fin n) (Fin n) K).map h.bar = P := by
    ext a b
    simp only [Matrix.map_apply]
    by_cases hab : a = b
    · subst hab
      apply hbar
      have := congrFun (congrFun (congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hsq) a) a
      rw [Units.val_mul, diag_mul_entry (fun i j hij => hdiag hij) a] at this
      simpa using this
    · rw [hdiag hab, map_zero]
  rw [mem_primeFormUnitary, hmap, hdiag.isSymm.eq]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  rw [← Units.val_mul, hsq, Units.val_one]

@[expose] noncomputable def conjSUHom {p f : ℕ} (h : UnitaryFieldData p f K) (n : ℕ) :
    primeFormUnitary h (idGram K n) →* MulAut ↥(StatedSU n (p ^ f) K) where
  toFun P := KFU.conjSU h P
  map_one' := MulEquiv.ext fun g => Subtype.ext (by simp [KFU.coe_conjSU])
  map_mul' P Q := MulEquiv.ext fun g => Subtype.ext (by simp [KFU.coe_conjSU, mul_assoc])

theorem coe_conjSUHom {p f : ℕ} (h : UnitaryFieldData p f K) {n : ℕ} (P : primeFormUnitary h (idGram K n))
    (g : ↥(StatedSU n (p ^ f) K)) :
    ((conjSUHom h n P g : ↥(StatedSU n (p ^ f) K)) : GL (Fin n) K) =
      (P : GL (Fin n) K) * g * (P : GL (Fin n) K)⁻¹ := rfl

theorem exists_involutive_section_of_odd_ker {G Q : Type} [Group G] [Group Q] [Finite G] (π : G →* Q)
    (hπ : Function.Surjective π) (hodd : ¬ 2 ∣ Nat.card π.ker) (D : Subgroup Q)
    (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ σ : ↥D →* G, (∀ d, π (σ d) = d) ∧ ∀ d, σ d * σ d = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hTmap, hTdis⟩ := exists_lift_of_coprime_ker π hπ (p := 2) hodd D
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥D)
  have hTmem : ∀ x ∈ T, π x ∈ D := fun x hx => hTmap ▸ ⟨x, hx, rfl⟩
  let fπ : T →* D := (π.comp T.subtype).codRestrict D (fun x => hTmem x.1 x.2)
  have hsurj : Function.Surjective fπ := by
    intro d
    have : (d : Q) ∈ T.map π := hTmap ▸ d.2
    obtain ⟨x, hx, hxd⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxd⟩
  have hinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 := Subgroup.disjoint_def.mp hTdis (T.mul_mem (T.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  let e : T ≃* D := MulEquiv.ofBijective fπ ⟨hinj, hsurj⟩
  have hπe : ∀ d : D, π (e.symm d : T) = d := fun d => congrArg Subtype.val (e.apply_symm_apply d)
  refine ⟨T.subtype.comp e.symm.toMonoidHom, hπe, fun d => ?_⟩
  have hk : ((e.symm d : T) : G) * (e.symm d : T) ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, hπe]
    exact Subtype.ext_iff.1 (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD d)
  exact Subgroup.disjoint_def.mp hTdis (T.mul_mem (e.symm d).2 (e.symm d).2) hk

end GenLocDiagU

theorem closure_centralizer_hyperplane_diag_unitary_eq_top {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (n : ℕ)
    (D : Subgroup (GL (Fin n) K)) (hD : ∀ x ∈ D, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag ∧ x * x = 1) :
    Subgroup.closure {g : GL (Fin n) K | g ∈ StatedSU n (p ^ f) K ∧ ∃ E : Subgroup (GL (Fin n) K), E ≤ D ∧
      Nat.card ↥D ≤ 2 * Nat.card ↥E ∧ ∀ x ∈ E, g * x = x * g} = StatedSU n (p ^ f) K := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun g hg => hg.1) ?_
  rcases n with _ | m
  · intro g _
    rw [Subsingleton.elim g 1]
    exact one_mem _
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := GenLocDiagU.charP_of_card hp hK
  have hgen := Phan.iSup_range_blockEmb2 (K := K) (p := p) (f := f) hK
    (GenLocDiagU.pow_ne_two hp hp2 hK) m
  have hoff : ∀ x ∈ D, ∀ i j, i ≠ j → (x : Matrix (Fin (m + 1)) (Fin (m + 1)) K) i j = 0 :=
    fun x hx i j hij => (hD x hx).1 hij
  have hsq : ∀ x ∈ D, x * x = 1 := fun x hx => (hD x hx).2
  set H := Subgroup.closure {g : GL (Fin (m + 1)) K | g ∈ StatedSU (m + 1) (p ^ f) K ∧
    ∃ E : Subgroup (GL (Fin (m + 1)) K), E ≤ D ∧ Nat.card ↥D ≤ 2 * Nat.card ↥E ∧
      ∀ x ∈ E, g * x = x * g}
  have hblock : ∀ (i : Fin m) (A : Phan.Su K p f 2),
      ((Phan.blockEmb2 K p f m i A : Phan.Su K p f (m + 1)) : GL (Fin (m + 1)) K) ∈ H := by
    intro i A
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · exact (SetLike.ext_iff.1 (SUid_eq_statedSU hK (m + 1)) _).1 (Phan.blockEmb2 K p f m i A).2
    · let a : Fin (m + 1) := ⟨i, by omega⟩
      let b : Fin (m + 1) := ⟨i + 1, by omega⟩
      let χ : D →* Kˣ := diagRatio D hoff a b
      have hχsq : ∀ x : D, x * x = 1 := fun x => Subtype.ext (hsq x.1 x.2)
      have hrange : Nat.card χ.range ≤ 2 := card_range_le_two_of_sq_eq_one χ hχsq
      refine ⟨χ.ker.map D.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
      · have h1 : Nat.card χ.ker * Nat.card χ.range = Nat.card D := by
          rw [← Subgroup.index_ker, Subgroup.card_mul_index]
        have h2 : Nat.card (χ.ker.map D.subtype) = Nat.card χ.ker :=
          Subgroup.card_map_of_injective D.subtype_injective
        rw [h2, ← h1, mul_comm]
        exact Nat.mul_le_mul_right _ hrange
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        have hy1 : χ y = 1 := hy
        have hii : (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a a =
            (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) b b := by
          have h1 : (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a a *
              ((y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) b b)⁻¹ = 1 := by
            have h := congrArg (fun u : Kˣ => (u : K)) hy1
            simpa [χ, diagRatio] using h
          have hj := diag_entry_ne_zero (hoff y.1 y.2) b
          field_simp at h1
          exact h1
        have hdiag : (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) =
            diagonal (fun k => (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) k k) :=
          (Matrix.IsDiag.diagonal_diag (hD y.1 y.2).1).symm
        apply Units.ext
        rw [Units.val_mul, Units.val_mul]
        change Phan.blockMat (m + 1) i (((A : Phan.Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
          (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = _
        rw [Subgroup.coe_subtype, hdiag]
        refine (GenLocDiagU.blockMat_commute_diag ?_ _).symm
        intro a' b' ha' hb'
        have key : ∀ c : Fin (m + 1), (i ≤ c.val ∧ c.val < i + 2) →
            (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) c c =
              (y.1 : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a a := by
          intro c hc
          rcases (by omega : c.val = i ∨ c.val = i + 1) with h | h
          · rw [show c = a from Fin.ext h]
          · rw [show c = b from Fin.ext h, hii]
        rw [key a' ha', key b' hb']
  have htop : ⨆ i : Fin m, (Phan.blockEmb2 K p f m i).range ≤
      H.comap (SUid (unitaryInvolution K p f) (m + 1)).subtype := by
    refine iSup_le fun i => ?_
    rintro _ ⟨A, rfl⟩
    exact hblock i A
  rw [hgen] at htop
  intro g hg
  have hg' : g ∈ SUid (unitaryInvolution K p f) (m + 1) :=
    (SetLike.ext_iff.1 (SUid_eq_statedSU hK (m + 1)) g).2 hg
  exact htop (Subgroup.mem_top (⟨g, hg'⟩ : SUid (unitaryInvolution K p f) (m + 1)))

section Diag

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_su_of_diag {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ}
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut ↥(StatedSU n (p ^ f) K))
    (ρ : A →* GL (Fin n) K) (hdiag : ∀ a, ((ρ a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hsq : ∀ a, ρ a * ρ a = 1)
    (hρ : ∀ (a : A) (g : ↥(StatedSU n (p ^ f) K)),
      ((α a g : ↥(StatedSU n (p ^ f) K)) : GL (Fin n) K) = ρ a * (g : GL (Fin n) K) * (ρ a)⁻¹) :
    gammaAct α = ⊤ := by
  have key := closure_centralizer_hyperplane_diag_unitary_eq_top hp hp2 hK n ρ.range
    (fun x hx => by obtain ⟨a, rfl⟩ := hx; exact ⟨hdiag a, hsq a⟩)
  have hS : {g : GL (Fin n) K | g ∈ StatedSU n (p ^ f) K ∧ ∃ E : Subgroup (GL (Fin n) K), E ≤ ρ.range ∧
      Nat.card ↥ρ.range ≤ 2 * Nat.card ↥E ∧ ∀ x ∈ E, g * x = x * g} ⊆
      ((gammaAct α).map (StatedSU n (p ^ f) K).subtype : Set (GL (Fin n) K)) := by
    rintro g ⟨hgS, E', hE'D, hcard, hcomm⟩
    have hadm := GenLocDiag.adm_comap_of_card_le hA ρ E' hE'D hcard
    refine ⟨⟨g, hgS⟩, le_gammaAct α hadm ?_, rfl⟩
    rw [GenLocBasic.mem_fixedIn_map]
    intro a ha
    apply Subtype.ext
    rw [hρ, ← hcomm (ρ a) ha, mul_assoc, mul_inv_cancel, mul_one]
  rw [eq_top_iff]
  intro x _
  have hx : (x : GL (Fin n) K) ∈ Subgroup.closure {g : GL (Fin n) K | g ∈ StatedSU n (p ^ f) K ∧
      ∃ E : Subgroup (GL (Fin n) K), E ≤ ρ.range ∧ Nat.card ↥ρ.range ≤ 2 * Nat.card ↥E ∧
        ∀ y ∈ E, g * y = y * g} := by
    rw [key]
    exact x.2
  obtain ⟨y, hy, hyx⟩ := (Subgroup.closure_le _).2 hS hx
  exact (Subtype.ext hyx : y = x) ▸ hy

theorem exists_diag_lift_of_odd_unitary {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : Odd n)
    (D : Subgroup (StatedProj (StatedSU n (p ^ f) K))) (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ (B : GL (Fin n) K) (ρ : ↥D →* GL (Fin n) K),
      ((B : Matrix (Fin n) (Fin n) K).map (· ^ (p ^ f)))ᵀ * (B : Matrix (Fin n) (Fin n) K) = 1 ∧
      (∀ d, ((B⁻¹ * ρ d * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag ∧ ρ d * ρ d = 1) ∧
      ∀ d : ↥D, ∃ hd : ρ d ∈ StatedSU n (p ^ f) K,
        (QuotientGroup.mk (⟨ρ d, hd⟩ : ↥(StatedSU n (p ^ f) K)) :
          StatedProj (StatedSU n (p ^ f) K)) = (d : StatedProj (StatedSU n (p ^ f) K)) := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hn1 : 1 ≤ n := hn.pos
  have hodd : ¬ 2 ∣ Nat.card
      (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))).ker := by
    rw [QuotientGroup.ker_mk', ← unitaryScalars_eq h hn1, card_unitaryScalars h hn1]
    intro h2
    exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (h2.trans (Nat.gcd_dvd_left _ _)))
  obtain ⟨σ, hσπ, hσsq⟩ := GenLocDiagU.exists_involutive_section_of_odd_ker (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) hodd D hD
  have hpq : 2 ∣ p ^ f + 1 := even_iff_two_dvd.1 ((h.prime.odd_of_ne_two hp2).pow).add_one
  have hle : unitarySU p f K n ≤ primeFormUnitary h (idGram K n) :=
    KFU.unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram K n)) := σ.range.map (Subgroup.inclusion hle)
  have hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩ _ ⟨_, ⟨d', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm' d d']
  have hpow : ∀ x ∈ G, x ^ 2 = 1 := by
    rintro _ ⟨_, ⟨d, rfl⟩, rfl⟩
    rw [pow_two, ← map_mul, hσsq, map_one]
  obtain ⟨P, hP⟩ := KFU.exists_unitary_conj_diag h Nat.prime_two hpq G hcomm hpow
  have hρ : ∀ d : ↥D, ((StatedSU n (p ^ f) K).subtype.comp σ) d =
      ((σ d : ↥(StatedSU n (p ^ f) K)) : GL (Fin n) K) := fun d => rfl
  refine ⟨(P : GL (Fin n) K), (StatedSU n (p ^ f) K).subtype.comp σ, ?_, fun d => ?_,
    fun d => ⟨(σ d).2, ?_⟩⟩
  · have hP1 := (mem_primeFormUnitary (h := h)).1 P.2
    simp only [idGram, Units.val_one, Matrix.mul_one] at hP1
    exact hP1
  · rw [hρ d]
    refine ⟨?_, ?_⟩
    · have h1 := hP (Subgroup.inclusion hle (σ d)) ⟨σ d, ⟨d, rfl⟩, rfl⟩
      exact h1
    · have := congrArg Subtype.val (hσsq d)
      simpa using this
  · exact hσπ d

theorem gammaAct_projectiveSU_of_inner_odd {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : Odd n)
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut (StatedProj (StatedSU n (p ^ f) K)))
    (δ : A →* StatedProj (StatedSU n (p ^ f) K)) (hδ : ∀ a, α a = MulAut.conj (δ a)) :
    gammaAct α = ⊤ := by
  have h := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hD : CFSG.IsElementaryAbelian 2 ↥δ.range :=
    GenLocBasic.isEA_of_surjective hA δ.rangeRestrict δ.rangeRestrict_surjective
  obtain ⟨B, ρ, hB, hρ, hlift⟩ := exists_diag_lift_of_odd_unitary hp hp2 hK hn δ.range hD
  let ρ₁ : A →* GL (Fin n) K := ρ.comp δ.rangeRestrict
  have hBU : B ∈ primeFormUnitary h (idGram K n) := by
    rw [mem_primeFormUnitary]
    simp only [idGram, Units.val_one, Matrix.mul_one]
    exact hB
  let BU : primeFormUnitary h (idGram K n) := ⟨B, hBU⟩
  let ρ₂ : A →* GL (Fin n) K := (MulAut.conj B⁻¹).toMonoidHom.comp ρ₁
  have h2 : ∀ a, ρ₂ a = B⁻¹ * ρ₁ a * B := fun a => by simp [ρ₂]
  have hdiag₂ : ∀ a, ((ρ₂ a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag := fun a => by
    rw [h2]
    exact (hρ (δ.rangeRestrict a)).1
  have hsq₂ : ∀ a, ρ₂ a * ρ₂ a = 1 := fun a => by
    have h3 : ρ₁ a * ρ₁ a = 1 := (hρ (δ.rangeRestrict a)).2
    calc ρ₂ a * ρ₂ a = B⁻¹ * (ρ₁ a * ρ₁ a) * B := by rw [h2]; group
      _ = 1 := by rw [h3]; group
  let ρ₂U : A →* primeFormUnitary h (idGram K n) :=
    ρ₂.codRestrict _ fun a => GenLocDiagU.mem_primeFormUnitary_of_diag_sq h hp2 (hdiag₂ a) (hsq₂ a)
  let α₂ : A →* MulAut ↥(StatedSU n (p ^ f) K) := (GenLocDiagU.conjSUHom h n).comp ρ₂U
  have h3 : gammaAct α₂ = ⊤ :=
    gammaAct_su_of_diag hp hp2 hK hA α₂ ρ₂ hdiag₂ hsq₂ fun a g => rfl
  let π : ↥(StatedSU n (p ^ f) K) →* StatedProj (StatedSU n (p ^ f) K) :=
    (QuotientGroup.mk' _).comp (KFU.conjSU h BU).toMonoidHom
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp (KFU.conjSU h BU).surjective
  refine GenLocDiag.gammaAct_eq_top_of_surj α₂ α π hπ (fun a g => ?_) h3
  obtain ⟨hd, hmk⟩ := hlift (δ.rangeRestrict a)
  have hδa : δ a = QuotientGroup.mk (⟨ρ₁ a, hd⟩ : ↥(StatedSU n (p ^ f) K)) := hmk.symm
  show QuotientGroup.mk (KFU.conjSU h BU (α₂ a g)) = α a (QuotientGroup.mk (KFU.conjSU h BU g))
  rw [hδ a, MulAut.conj_apply, hδa, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  show B * (ρ₂ a * (g : GL (Fin n) K) * (ρ₂ a)⁻¹) * B⁻¹ =
    ρ₁ a * (B * (g : GL (Fin n) K) * B⁻¹) * (ρ₁ a)⁻¹
  rw [h2 a]
  group

theorem gammaAct_projectiveSU_of_inner_odd' {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : Odd n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut (StatedProj (StatedSU n (p ^ f) K)))
    (hα : ∀ a, α a ∈ (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range) :
    gammaAct α = ⊤ := by
  let e := MonoidHom.ofInjective hinj
  refine gammaAct_projectiveSU_of_inner_odd hp hp2 hK hn hA α
    (e.symm.toMonoidHom.comp (α.codRestrict _ hα)) fun a => ?_
  have h := congrArg Subtype.val (e.apply_symm_apply ⟨α a, hα a⟩)
  exact h.symm

end Diag

end CFSG.GH74.Generic.BProg.B2

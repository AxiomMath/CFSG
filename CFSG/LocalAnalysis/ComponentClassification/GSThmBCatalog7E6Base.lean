module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerE
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutCard
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81Conf

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Cat7E6

section Transport

variable {K₀ K₁ : Type} [Group K₀] [Group K₁] (e : K₀ ≃* K₁)

theorem congr_conj (k : K₀) : MulAut.congr e (MulAut.conj k) = MulAut.conj (e k) := by
  ext x
  simp [MulAut.congr_apply]

theorem map_inn : (Cat8.Inn K₀).map (MulAut.congr e).toMonoidHom = Cat8.Inn K₁ := by
  ext φ
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    exact ⟨e k, (congr_conj e k).symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨MulAut.conj (e.symm k), ⟨e.symm k, rfl⟩, ?_⟩
    change MulAut.congr e (MulAut.conj (e.symm k)) = _
    rw [congr_conj, MulEquiv.apply_symm_apply]

theorem map_innA (α : MulAut K₀) :
    (Cat8.innA K₀ α).map (MulAut.congr e).toMonoidHom = Cat8.innA K₁ (MulAut.congr e α) := by
  rw [Cat8.innA, Subgroup.map_sup, map_inn, MonoidHom.map_zpowers]
  rfl

theorem map_inf_equiv {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (A B : Subgroup G) :
    (A ⊓ B).map Φ.toMonoidHom = A.map Φ.toMonoidHom ⊓ B.map Φ.toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_inf]

theorem map_centralizer_single {G H : Type*} [Group G] [Group H] (Φ : G ≃* H) (w : G) :
    (centralizer ({w} : Set G)).map Φ.toMonoidHom = centralizer ({Φ w} : Set H) := by
  ext x
  rw [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg Φ h
    simpa using this
  · intro h
    apply Φ.injective
    simpa using h

theorem map_innFix (α : MulAut K₀) :
    (Cat8.innFix K₀ α).map (MulAut.congr e).toMonoidHom =
      Cat8.innFix K₁ (MulAut.congr e α) := by
  rw [Cat8.innFix, map_inf_equiv, map_inn, map_centralizer_single]

theorem map_L0 (α : MulAut K₀) :
    (Cat8.L0 K₀ α).map (MulAut.congr e).toMonoidHom = Cat8.L0 K₁ (MulAut.congr e α) := by
  rw [Cat8.L0, Subgroup.map_commutator, map_innFix]

theorem map_fixSubgroup (α : MulAut K₀) :
    (Eight.fixSubgroup α).map e.toMonoidHom = Eight.fixSubgroup (MulAut.congr e α) := by
  ext y
  rw [Subgroup.mem_map_equiv, Eight.mem_fixSubgroup, Eight.mem_fixSubgroup]
  constructor
  · intro h
    apply e.symm.injective
    rw [← h]
    simp [MulAut.congr_apply]
  · intro h
    have := congrArg e.symm h
    simpa [MulAut.congr_apply] using this

theorem card_fixSubgroup_congr (α : MulAut K₀) :
    Nat.card (Eight.fixSubgroup (MulAut.congr e α)) = Nat.card (Eight.fixSubgroup α) := by
  rw [← map_fixSubgroup, Subgroup.card_map_of_injective e.injective]

theorem mem_inn_congr_iff (α : MulAut K₀) :
    MulAut.congr e α ∈ Cat8.Inn K₁ ↔ α ∈ Cat8.Inn K₀ := by
  rw [← map_inn e, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem isAdmQ_congr {q : ℕ} {α : MulAut K₀} (h : Cat8.IsAdmQ K₀ q α) :
    Cat8.IsAdmQ K₁ q (MulAut.congr e α) where
  sq := by rw [← map_mul, h.sq, map_one]
  out := by rw [mem_inn_congr_iff]; exact h.out
  dvd := by rw [card_fixSubgroup_congr]; exact h.dvd

theorem exists_sylow_map {G H : Type*} [Group G] [Group H] [Finite G] (Φ : G ≃* H) {p : ℕ}
    [Fact p.Prime] {Q M : Subgroup G} {M' : Subgroup H} (hQM : Q ≤ M)
    (h : ∃ T : Sylow p ↥M, (T : Subgroup ↥M) = Q.subgroupOf M)
    (hM : M.map Φ.toMonoidHom = M') :
    ∃ T : Sylow p ↥M', (T : Subgroup _) = (Q.map Φ.toMonoidHom).subgroupOf M' := by
  subst hM
  obtain ⟨T, hT⟩ := h
  have hle : Q.map Φ.toMonoidHom ≤ M.map Φ.toMonoidHom := Subgroup.map_mono hQM
  have hp : IsPGroup p ((Q.map Φ.toMonoidHom).subgroupOf (M.map Φ.toMonoidHom)) := by
    have h1 : IsPGroup p Q := by
      have := T.isPGroup'
      rw [hT] at this
      exact this.of_equiv (subgroupOfEquivOfLe hQM)
    exact (h1.map Φ.toMonoidHom).of_equiv (subgroupOfEquivOfLe hle).symm
  have hidx : ¬ p ∣ ((Q.map Φ.toMonoidHom).subgroupOf (M.map Φ.toMonoidHom)).index := by
    have h1 : ¬ p ∣ (Q.subgroupOf M).index := by
      rw [← hT]
      exact T.not_dvd_index
    change ¬ p ∣ (Q.map Φ.toMonoidHom).relIndex (M.map Φ.toMonoidHom)
    rw [Subgroup.relIndex_map_map_of_injective _ _ Φ.injective]
    exact h1
  exact ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx⟩

variable [Finite K₀] in
@[expose] def qConfCongr {q : ℕ} (c : Cat8.QConf K₀ q) : Cat8.QConf K₁ q where
  a := MulAut.congr e c.a
  Q := c.Q.map (MulAut.congr e).toMonoidHom
  g := MulAut.congr e c.g
  z := MulAut.congr e c.z
  adm := isAdmQ_congr e c.adm
  Q_le := by
    rw [← map_innA, ← map_centralizer_single, ← map_inf_equiv]
    exact Subgroup.map_mono c.Q_le
  Q_sylow := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
      (fun φ ψ h => MulEquiv.ext (congrFun h))
    exact exists_sylow_map (MulAut.congr e) c.Q_le c.Q_sylow
      (by rw [map_inf_equiv, map_innA, map_centralizer_single])
  g_inn := (mem_inn_congr_iff e c.g).mpr c.g_inn
  g_norm := by
    rw [mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply]
    exact mem_normalizer_iff.mp c.g_norm _
  g_not_mem := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact c.g_not_mem
  g_sq := by
    rw [Subgroup.mem_map_equiv, map_mul, MulEquiv.symm_apply_apply]
    exact c.g_sq
  tau_inn := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, mem_inn_congr_iff]
    exact c.tau_inn
  z_mem := by
    rw [← map_L0, ← map_inf_equiv]
    exact Subgroup.mem_map_of_mem _ c.z_mem
  z_comm := by
    intro w hw
    rw [← map_L0, ← map_inf_equiv,
      Subgroup.mem_map_equiv] at hw
    have h2 := congrArg (MulAut.congr e) (c.z_comm _ hw)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  z_sq := by rw [← map_mul, c.z_sq, map_one]
  z_ne := fun h => c.z_ne ((MulAut.congr e).injective (h.trans (map_one _).symm))

section
variable [Finite K₀]

@[simp] theorem qConfCongr_a {q : ℕ} (c : Cat8.QConf K₀ q) :
    (qConfCongr e c).a = MulAut.congr e c.a := rfl

@[simp] theorem qConfCongr_z {q : ℕ} (c : Cat8.QConf K₀ q) :
    (qConfCongr e c).z = MulAut.congr e c.z := rfl

@[simp] theorem qConfCongr_g {q : ℕ} (c : Cat8.QConf K₀ q) :
    (qConfCongr e c).g = MulAut.congr e c.g := rfl

theorem qConfCongr_tau {q : ℕ} (c : Cat8.QConf K₀ q) :
    (qConfCongr e c).tau = MulAut.congr e c.tau := by
  simp only [Cat8.QConf.tau, qConfCongr_a, qConfCongr_g, map_mul, map_inv]

theorem qConfCongr_D {q : ℕ} (c : Cat8.QConf K₀ q) :
    (qConfCongr e c).D = c.D.map (MulAut.congr e).toMonoidHom := by
  rw [Cat8.QConf.D, Cat8.QConf.D, map_inf_equiv, map_L0]
  rfl

end

end Transport

section Model

open CatFactsSp4 Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

theorem conj_proj (g : StatedSp 2 K) :
    MulAut.conj (proj 2 K g) = conjAut 2 K ⟨g, statedSp_le_gsp g.2⟩ := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective x
  rw [MulAut.conj_apply, conjAut_proj, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem conjAut_eq_one_iff [Finite K] (X : gsp 2 K) :
    conjAut 2 K X = 1 ↔
      ∃ c : Kˣ, (X : GL (Fin 2 ⊕ Fin 2) K) = GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c := by
  have h := CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff (r := 2)
    (by norm_num) X 1
  rw [map_one, mul_one] at h
  rw [h]
  simp

theorem eq_one_of_fieldAut_mem [Finite K] {σ : K ≃+* K}
    (h : fieldAut 2 K σ ∈ (conjAut 2 K).range) : σ = 1 := by
  obtain ⟨X, hX⟩ := h
  have h1 : conjAut 2 K X⁻¹ * fieldAut 2 K σ = 1 := by
    rw [map_inv, ← hX, inv_mul_cancel]
  exact ((CatalogueBSymplecticRepresentation.conjAut_mul_fieldAut_eq_one_iff (r := 2)
    (by norm_num) _ σ).mp h1).1

theorem exists_eq_conjAut_mul_fieldAut [Finite K] (hodd : ringChar K ≠ 2)
    (ψ : MulAut (StatedProj (StatedSp 2 K))) :
    ∃ (X : gsp 2 K) (σ : K ≃+* K), ψ = conjAut 2 K X * fieldAut 2 K σ :=
  CatalogueBSymplecticRepresentation.automorphism_standard hodd le_rfl ψ

theorem range_conjAut_normal [Finite K] (hodd : ringChar K ≠ 2) :
    ((conjAut 2 K).range).Normal := by
  constructor
  rintro _ ⟨X, rfl⟩ ψ
  obtain ⟨Y, σ, rfl⟩ := exists_eq_conjAut_mul_fieldAut hodd ψ
  refine ⟨Y * gspFieldMap σ X * Y⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, ← fieldAut_mul_conjAut_mul_inv]
  group

theorem ringChar_ne_two_of_card {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite K]
    (hK : Nat.card K = p ^ f) : ringChar K ≠ 2 := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  intro h
  apply h2
  have := ringChar.Nat.cast_ringChar (R := K)
  rw [h] at this
  exact_mod_cast this

theorem inn_sup_eq_range [Finite K] (B : gsp 2 K)
    (hB : ∀ l : K, l ^ 2 ≠ (multiplierUnit B : K)) :
    Cat8.Inn (StatedProj (StatedSp 2 K)) ⊔ zpowers (conjAut 2 K B) = (conjAut 2 K).range := by
  apply le_antisymm
  · apply sup_le
    · rintro _ ⟨x, rfl⟩
      obtain ⟨g, rfl⟩ := proj_surjective x
      exact ⟨_, (conj_proj g).symm⟩
    · rw [zpowers_le]
      exact ⟨B, rfl⟩
  · rintro _ ⟨X, rfl⟩
    exact conjAut_mem_inn_sup B hB X

theorem admissible_data [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : Cat8.IsAdmQ (StatedProj (StatedSp 2 K)) (p ^ f) α) :
    ∃ A : gsp 2 K, α = conjAut 2 K A ∧ ∃ d : K, d ≠ 0 ∧ (∀ l : K, l ^ 2 ≠ d) ∧
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1 ∧
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
        ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
          d • formJ 2 K := by
  have hfix : Eight.fixSubgroup α = fixOf α := by
    ext x
    rfl
  have hdvd : (p ^ f) ^ 2 * (((p ^ f) ^ 2) ^ 2 - 1) / 2 ∣ Nat.card (fixOf α) := by
    rw [← hfix]
    exact hα.dvd
  exact exists_typeII_of_admissible hp hp2 hf hK α hα.sq hα.out hdvd

theorem innA_eq_range [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα : Cat8.IsAdmQ (StatedProj (StatedSp 2 K)) (p ^ f) α) :
    Cat8.innA (StatedProj (StatedSp 2 K)) α = (conjAut 2 K).range := by
  obtain ⟨A, rfl, d, -, hdsq, -, hμ⟩ := admissible_data hp hp2 hf hK hα
  have hm : (multiplierUnit A : K) = d := by
    have := multiplierUnit_eq A (μ := Units.mk0 d (by
      rintro rfl
      exact hdsq 0 (by ring))) (by rw [Units.val_mk0]; exact hμ)
    rw [this, Units.val_mk0]
  exact inn_sup_eq_range A (fun l => hm ▸ hdsq l)

end Model

theorem exists_zpow_ringEquiv (K : Type) [Field K] [Finite K] :
    ∃ φ₀ : K ≃+* K, ∀ σ : K ≃+* K, ∃ k : ℤ, σ = φ₀ ^ k := by
  obtain ⟨p, hchar⟩ := CharP.exists K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let := ZMod.algebra K p
  let h : (K ≃ₐ[ZMod p] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hsurj : Function.Surjective h := by
    intro σ
    refine ⟨AlgEquiv.ofRingEquiv (f := σ) (fun x => ?_), ?_⟩
    · have := RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) K))
        (algebraMap (ZMod p) K)
      exact congrArg (fun φ : ZMod p →+* K => φ x) this
    · rfl
  have : IsCyclic (K ≃+* K) := isCyclic_of_surjective h hsurj
  obtain ⟨φ₀, hφ₀⟩ := IsCyclic.exists_generator (α := K ≃+* K)
  refine ⟨φ₀, fun σ => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hφ₀ σ)
  exact ⟨k, hk.symm⟩

end Cat7E6

end CFSG.ComponentClassification.GSThmB

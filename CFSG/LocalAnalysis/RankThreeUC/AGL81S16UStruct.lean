module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UNorm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankE
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankF
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16NatU

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G]

section Psi

variable {n : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)

theorem LC_le_normalizer (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) :
    L ⊔ (M ⊓ centralizer (V : Set G)) ≤ normalizer (V : Set G) :=
  (sup_le hLM inf_le_left).trans hMV

theorem le_normalizer_of_le_LC {A : Subgroup G} (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) (hAL : A ≤ L ⊔ (M ⊓ centralizer (V : Set G))) :
    A ≤ normalizer (V : Set G) := hAL.trans (LC_le_normalizer hLM hMV)

theorem U4NatData.exists_su_of_mem_sup {σ : d.F ≃+* d.F}
    (hS : SUid σ 4 = StatedSU 4 (2 ^ n) d.F) (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G))
    {a : G} (ha : a ∈ L ⊔ (M ⊓ centralizer (V : Set G))) :
    ∃ g : SUid σ 4, ∀ v : ↥V,
      g • d.eqv v = d.eqv (conjOn V a (LC_le_normalizer hLM hMV ha) v) := by
  obtain ⟨l, hl, hlb⟩ := exists_mul_of_mem_sup_centralizer hLM hMV ha
  have hlV : l ∈ normalizer (V : Set G) := hMV (hLM hl)
  refine ⟨⟨(d.ε ⟨l, hl⟩ : GL (Fin 4) d.F), hS.symm ▸ (d.ε ⟨l, hl⟩).2⟩, fun v => ?_⟩
  have h1 := d.eps_eqv hl hlV v
  have h2 : conjOn V a (LC_le_normalizer hLM hMV ha) v = conjOn V l hlV v :=
    Subtype.ext (hlb v v.2)
  rw [h2, ← h1]
  rfl

noncomputable def U4NatData.psi {σ : d.F ≃+* d.F} (hS : SUid σ 4 = StatedSU 4 (2 ^ n) d.F)
    (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G)) :
    ↥(L ⊔ (M ⊓ centralizer (V : Set G))) →* SUid σ 4 where
  toFun a := Classical.choose (d.exists_su_of_mem_sup hS hLM hMV a.2)
  map_one' := by
    refine ext_smul σ fun x => ?_
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    rw [Classical.choose_spec (d.exists_su_of_mem_sup hS hLM hMV (1 : ↥(L ⊔ (M ⊓ centralizer (V : Set G)))).2) v, one_smul]
    exact congrArg d.eqv (Subtype.ext (by simp))
  map_mul' a b := by
    refine ext_smul σ fun x => ?_
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    rw [mul_smul, Classical.choose_spec (d.exists_su_of_mem_sup hS hLM hMV b.2) v,
      Classical.choose_spec (d.exists_su_of_mem_sup hS hLM hMV a.2),
      Classical.choose_spec (d.exists_su_of_mem_sup hS hLM hMV (a * b).2) v]
    exact congrArg d.eqv (Subtype.ext (by simp [mul_assoc]))

theorem U4NatData.psi_spec {σ : d.F ≃+* d.F} (hS : SUid σ 4 = StatedSU 4 (2 ^ n) d.F)
    (hLM : L ≤ M) (hMV : M ≤ normalizer (V : Set G))
    (a : ↥(L ⊔ (M ⊓ centralizer (V : Set G)))) (v : ↥V) :
    d.psi hS hLM hMV a • d.eqv v =
      d.eqv (conjOn V a.1 (LC_le_normalizer hLM hMV a.2) v) :=
  Classical.choose_spec (d.exists_su_of_mem_sup hS hLM hMV a.2) v

end Psi

section Elem

variable {n : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)
variable {σ : d.F ≃+* d.F} (hS : SUid σ 4 = StatedSU 4 (2 ^ n) d.F) (hLM : L ≤ M)
  (hMV : M ≤ normalizer (V : Set G)) {A : Subgroup G}
  (hAL : A ≤ L ⊔ (M ⊓ centralizer (V : Set G)))


noncomputable def U4NatData.phiA : ↥A →* SUid σ 4 :=
  (d.psi hS hLM hMV).comp (Subgroup.inclusion hAL)

theorem U4NatData.phiA_spec (a : ↥A) (v : ↥V) :
    d.phiA hS hLM hMV hAL a • d.eqv v =
      d.eqv (conjOn V a.1 (le_normalizer_of_le_LC hLM hMV hAL a.2) v) :=
  d.psi_spec hS hLM hMV (Subgroup.inclusion hAL a) v

theorem U4NatData.phiA_eq_one_iff (a : ↥A) :
    d.phiA hS hLM hMV hAL a = 1 ↔ (a : G) ∈ centralizer (V : Set G) := by
  constructor
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    have h1 := d.phiA_spec hS hLM hMV hAL a ⟨v, hv⟩
    rw [h, one_smul] at h1
    have h2 : conjOn V a.1 (le_normalizer_of_le_LC hLM hMV hAL a.2) ⟨v, hv⟩ = ⟨v, hv⟩ :=
      d.eqv.injective h1.symm
    have h3 : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val h2
    calc v * (a : G) = ((a : G) * v * (a : G)⁻¹) * (a : G) := by rw [h3]
      _ = (a : G) * v := by group
  · intro h
    refine ext_smul σ fun x => ?_
    obtain ⟨v, rfl⟩ := d.eqv.surjective x
    rw [d.phiA_spec hS hLM hMV hAL a v, one_smul]
    refine congrArg d.eqv (Subtype.ext ?_)
    have hc := Subgroup.mem_centralizer_iff.mp h v v.2
    show (a : G) * v * (a : G)⁻¹ = v
    calc (a : G) * v * (a : G)⁻¹ = (v * (a : G)) * (a : G)⁻¹ := by rw [← hc]
      _ = v := by group

theorem U4NatData.eqv_one : d.eqv 1 = 0 := by
  simp [U4NatData.eqv_apply]

theorem U4NatData.eqv_inv (v : ↥V) : d.eqv v⁻¹ = -d.eqv v := by
  simp [U4NatData.eqv_apply]

theorem U4NatData.phiA_sq (hA : IsElemAbelian 2 A) :
    ∀ g ∈ (d.phiA hS hLM hMV hAL).range, g * g = 1 := by
  rintro _ ⟨a, rfl⟩
  rw [← map_mul]
  have : a * a = 1 := Subtype.ext (by simpa [pow_two] using hA.2 a.1 a.2)
  rw [this, map_one]

theorem U4NatData.phiA_comm (hA : IsElemAbelian 2 A) :
    ∀ g ∈ (d.phiA hS hLM hMV hAL).range, ∀ h ∈ (d.phiA hS hLM hMV hAL).range, g * h = h * g := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact hA.1.is_comm.comm a b

theorem U4NatData.card_ker_phiA :
    Nat.card ↥(d.phiA hS hLM hMV hAL).ker =
      Nat.card ↥(A ⊓ (M ⊓ centralizer (V : Set G))) := by
  have hAM : A ≤ M := hAL.trans (sup_le hLM inf_le_left)
  refine Nat.card_congr
    { toFun := fun a => ⟨a.1.1, a.1.2, hAM a.1.2,
        (d.phiA_eq_one_iff hS hLM hMV hAL a.1).mp (MonoidHom.mem_ker.mp a.2)⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩,
        MonoidHom.mem_ker.mpr ((d.phiA_eq_one_iff hS hLM hMV hAL ⟨x.1, x.2.1⟩).mpr x.2.2.2)⟩
      left_inv := fun a => rfl
      right_inv := fun x => rfl }

theorem U4NatData.card_range_phiA [Finite G] :
    Nat.card ↥(d.phiA hS hLM hMV hAL).range =
      (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A := by
  have h1 := Subgroup.card_ker_mul_card_range (d.phiA hS hLM hMV hAL)
  have hker := d.card_ker_phiA hS hLM hMV hAL
  have h2 := Subgroup.relIndex_mul_card (H := A ⊓ (M ⊓ centralizer (V : Set G))) (K := A)
  rw [inf_eq_left.mpr (inf_le_left : A ⊓ (M ⊓ centralizer (V : Set G)) ≤ A)] at h2
  rw [hker] at h1
  have hpos : 0 < Nat.card ↥(A ⊓ (M ⊓ centralizer (V : Set G))) := Nat.card_pos
  have h3 : Nat.card ↥(A ⊓ (M ⊓ centralizer (V : Set G))) * Nat.card ↥(d.phiA hS hLM hMV hAL).range =
      Nat.card ↥(A ⊓ (M ⊓ centralizer (V : Set G))) *
        (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A := by
    rw [h1, mul_comm, h2]
  exact Nat.eq_of_mul_eq_mul_left hpos h3

theorem U4NatData.mem_comm_iff (w : ↥V) :
    (w : G) ∈ ⁅A, V⁆ ↔ d.eqv w ∈ commSp (d.phiA hS hLM hMV hAL).range := by
  have hAV := le_normalizer_of_le_LC hLM hMV hAL
  have hcomm : ∀ (a : ↥A) (v : ↥V), d.eqv (conjOn V a.1 (hAV a.2) v * v⁻¹) =
      d.phiA hS hLM hMV hAL a • d.eqv v - d.eqv v := by
    intro a v
    rw [d.eqv_mul, d.eqv_inv, ← d.phiA_spec hS hLM hMV hAL a v, sub_eq_add_neg]
  have hmemV : ∀ (a : G) (ha : a ∈ A) (v : G) (hv : v ∈ V), ⁅a, v⁆ ∈ V := by
    intro a ha v hv
    have := (conjOn V a (hAV ha) ⟨v, hv⟩ * ⟨v, hv⟩⁻¹).2
    simpa [commutatorElement_def] using this
  have hcommE : ∀ (a : G) (ha : a ∈ A) (v : G) (hv : v ∈ V),
      (⟨⁅a, v⁆, hmemV a ha v hv⟩ : ↥V) = conjOn V a (hAV ha) ⟨v, hv⟩ * ⟨v, hv⟩⁻¹ :=
    fun a ha v hv => Subtype.ext (by simp [commutatorElement_def])
  constructor
  · intro hw
    have key : ∀ g : G, g ∈ ⁅A, V⁆ →
        ∃ hg : g ∈ V, d.eqv ⟨g, hg⟩ ∈ commSp (d.phiA hS hLM hMV hAL).range := by
      intro g hg
      rw [Subgroup.commutator_def] at hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨a, ha, v, hv, rfl⟩ := hg
        refine ⟨hmemV a ha v hv, ?_⟩
        rw [hcommE a ha v hv, hcomm ⟨a, ha⟩ ⟨v, hv⟩]
        exact sub_mem_commSp (E := (d.phiA hS hLM hMV hAL).range)
          (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩) _
      | one =>
        refine ⟨one_mem _, ?_⟩
        have : (⟨1, one_mem V⟩ : ↥V) = 1 := rfl
        rw [this, d.eqv_one]
        exact Submodule.zero_mem _
      | mul g₁ g₂ _ _ ih₁ ih₂ =>
        obtain ⟨h₁, c₁⟩ := ih₁
        obtain ⟨h₂, c₂⟩ := ih₂
        refine ⟨V.mul_mem h₁ h₂, ?_⟩
        have : (⟨g₁ * g₂, V.mul_mem h₁ h₂⟩ : ↥V) = ⟨g₁, h₁⟩ * ⟨g₂, h₂⟩ := rfl
        rw [this, d.eqv_mul]
        exact Submodule.add_mem _ c₁ c₂
      | inv g _ ih =>
        obtain ⟨h, c⟩ := ih
        refine ⟨V.inv_mem h, ?_⟩
        have : (⟨g⁻¹, V.inv_mem h⟩ : ↥V) = ⟨g, h⟩⁻¹ := rfl
        rw [this, d.eqv_inv]
        exact Submodule.neg_mem _ c
    obtain ⟨hg, hc⟩ := key (w : G) hw
    exact hc
  · intro hy
    let K' : Submodule d.F (Fin 4 → d.F) :=
      { carrier := {y | ∃ u : ↥V, (u : G) ∈ ⁅A, V⁆ ∧ d.eqv u = y}
        add_mem' := by
          rintro _ _ ⟨u₁, h₁, rfl⟩ ⟨u₂, h₂, rfl⟩
          exact ⟨u₁ * u₂, ⁅A, V⁆.mul_mem h₁ h₂, d.eqv_mul u₁ u₂⟩
        zero_mem' := ⟨1, one_mem _, d.eqv_one⟩
        smul_mem' := by
          rintro c _ ⟨u, hu, rfl⟩
          have key : ∀ g : G, g ∈ ⁅A, V⁆ → ∃ hg : g ∈ V, ∃ u' : ↥V, (u' : G) ∈ ⁅A, V⁆ ∧
              d.eqv u' = c • d.eqv ⟨g, hg⟩ := by
            intro g hg
            rw [Subgroup.commutator_def] at hg
            induction hg using Subgroup.closure_induction with
            | mem g hg =>
              obtain ⟨a, ha, v, hv, rfl⟩ := hg
              refine ⟨hmemV a ha v hv, ?_⟩
              obtain ⟨v', hv'⟩ := d.eqv.surjective (c • d.eqv ⟨v, hv⟩)
              refine ⟨conjOn V a (hAV ha) v' * v'⁻¹, ?_, ?_⟩
              · have : ((conjOn V a (hAV ha) v' * v'⁻¹ : ↥V) : G) = ⁅a, (v' : G)⁆ := by
                  simp [commutatorElement_def]
                rw [this]
                exact Subgroup.commutator_mem_commutator ha v'.2
              · rw [hcomm ⟨a, ha⟩ v', hcommE a ha v hv, hcomm ⟨a, ha⟩ ⟨v, hv⟩, hv', smul_sub,
                  smul_comm (d.phiA hS hLM hMV hAL ⟨a, ha⟩) c (d.eqv ⟨v, hv⟩)]
            | one =>
              refine ⟨one_mem _, 1, one_mem _, ?_⟩
              have : (⟨1, one_mem V⟩ : ↥V) = 1 := rfl
              rw [this, d.eqv_one, smul_zero]
            | mul g₁ g₂ _ _ ih₁ ih₂ =>
              obtain ⟨h₁, u₁, hu₁, e₁⟩ := ih₁
              obtain ⟨h₂, u₂, hu₂, e₂⟩ := ih₂
              refine ⟨V.mul_mem h₁ h₂, u₁ * u₂, ⁅A, V⁆.mul_mem hu₁ hu₂, ?_⟩
              have : (⟨g₁ * g₂, V.mul_mem h₁ h₂⟩ : ↥V) = ⟨g₁, h₁⟩ * ⟨g₂, h₂⟩ := rfl
              rw [this, d.eqv_mul, d.eqv_mul, e₁, e₂, smul_add]
            | inv g _ ih =>
              obtain ⟨h, u', hu', e⟩ := ih
              refine ⟨V.inv_mem h, u'⁻¹, ⁅A, V⁆.inv_mem hu', ?_⟩
              have : (⟨g⁻¹, V.inv_mem h⟩ : ↥V) = ⟨g, h⟩⁻¹ := rfl
              rw [this, d.eqv_inv, d.eqv_inv, e, smul_neg]
          obtain ⟨hg, u', hu', he⟩ := key (u : G) hu
          exact ⟨u', hu', he⟩ }
    have hle : commSp (d.phiA hS hLM hMV hAL).range ≤ K' := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, hg, x, rfl⟩
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hg
      obtain ⟨v, rfl⟩ := d.eqv.surjective x
      refine ⟨conjOn V a.1 (hAV a.2) v * v⁻¹, ?_, hcomm a v⟩
      have : ((conjOn V a.1 (hAV a.2) v * v⁻¹ : ↥V) : G) = ⁅(a : G), (v : G)⁆ := by
        simp [commutatorElement_def]
      rw [this]
      exact Subgroup.commutator_mem_commutator a.2 v.2
    obtain ⟨u, hu, hue⟩ := hle hy
    have : u = w := d.eqv.injective hue
    rw [← this]
    exact hu

theorem U4NatData.mem_fix_iff (w : ↥V) :
    (w : G) ∈ centralizer (A : Set G) ↔ d.eqv w ∈ fixSp (d.phiA hS hLM hMV hAL).range := by
  have hAV := le_normalizer_of_le_LC hLM hMV hAL
  constructor
  · intro h
    refine mem_fixSp.mpr ?_
    rintro _ ⟨a, rfl⟩
    rw [d.phiA_spec hS hLM hMV hAL a w]
    refine congrArg d.eqv (Subtype.ext ?_)
    have hc := Subgroup.mem_centralizer_iff.mp h a a.2
    show (a : G) * w * (a : G)⁻¹ = w
    calc (a : G) * w * (a : G)⁻¹ = ((a : G) * w) * (a : G)⁻¹ := rfl
      _ = (w * (a : G)) * (a : G)⁻¹ := by rw [← hc]
      _ = w := by group
  · intro h
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    have h1 := mem_fixSp.mp h (d.phiA hS hLM hMV hAL ⟨a, ha⟩)
      (MonoidHom.mem_range.mpr ⟨⟨a, ha⟩, rfl⟩)
    rw [d.phiA_spec hS hLM hMV hAL ⟨a, ha⟩ w] at h1
    have h2 : (⟨a * w * a⁻¹, _⟩ : ↥V) = w := d.eqv.injective h1
    have h3 : a * (w : G) * a⁻¹ = w := congrArg Subtype.val h2
    calc a * (w : G) = (a * (w : G) * a⁻¹) * a := by group
      _ = (w : G) * a := by rw [h3]

end Elem

section Facts

variable {n : ℕ} {M L V : Subgroup G} (d : U4NatData G n L V)

theorem statedSU_data_norm (hF : Nat.card d.F = (2 ^ n) ^ 2) :
    ∃ σ : d.F ≃+* d.F, IsUnitaryInvolution σ ∧ (2 : d.F) = 0 ∧
      SUid σ 4 = StatedSU 4 (2 ^ n) d.F ∧ ∀ c : d.F, σ c * c = c ^ (2 ^ n + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP d.F 2 := charP_of_card_sq (p := 2) (f := n) hF
  refine ⟨CFSG.LieType.BorelTits.unitaryInvolution d.F 2 n,
    isUnitaryInvolution_unitaryInvolution hF, CharP.cast_eq_zero d.F 2,
    CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 4, fun c => ?_⟩
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, pow_succ]

include d in
theorem U4NatData.rank_le [Finite G] (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A → A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
      (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A ≤ 2 ^ (4 * n) := by
  intro A hAM hA hAL
  obtain ⟨σ, hσ, h2, hS, -⟩ := statedSU_data_norm d d.card_F
  rw [← d.card_range_phiA hS hLM hMV hAL]
  exact card_le_two_pow_four hσ (d.phiA_sq hS hLM hMV hAL hA) (d.phiA_comm hS hLM hMV hAL hA)
    hn d.card_F

include d in
theorem U4NatData.generation [Finite G] (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A → A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
      (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A = 2 ^ (4 * n) →
      ∀ X : Subgroup G, (∀ a ∈ A, a ∉ M ⊓ centralizer (V : Set G) →
        V ⊓ centralizer ({a} : Set G) ≤ X) → V ≤ X := by
  intro A hAM hA hAL hrel X hX v hv
  obtain ⟨σ, hσ, h2, hS, -⟩ := statedSU_data_norm d d.card_F
  have hcard : Nat.card ↥(d.phiA hS hLM hMV hAL).range = 2 ^ (4 * n) := by
    rw [d.card_range_phiA hS hLM hMV hAL]; exact hrel
  obtain ⟨g, hgE, hg1, hgx⟩ := generation_model hσ h2 (d.phiA_sq hS hLM hMV hAL hA)
    (d.phiA_comm hS hLM hMV hAL hA) hn d.card_F hcard (d.eqv ⟨v, hv⟩)
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hgE
  have haC : (a : G) ∉ M ⊓ centralizer (V : Set G) := fun h =>
    hg1 ((d.phiA_eq_one_iff hS hLM hMV hAL a).mpr h.2)
  refine hX a a.2 haC ⟨hv, ?_⟩
  rw [d.phiA_spec hS hLM hMV hAL a ⟨v, hv⟩] at hgx
  have h1 : conjOn V a.1 (le_normalizer_of_le_LC hLM hMV hAL a.2) ⟨v, hv⟩ = ⟨v, hv⟩ :=
    d.eqv.injective hgx
  have h3 : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val h1
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  calc (a : G) * v = ((a : G) * v * (a : G)⁻¹) * (a : G) := by group
    _ = v * (a : G) := by rw [h3]

theorem commutator_le_of_le_normalizer' {A V : Subgroup G} (hAV : A ≤ normalizer (V : Set G)) :
    ⁅A, V⁆ ≤ V := by
  rw [Subgroup.commutator_le]
  intro a ha v hv
  have h1 : a * v * a⁻¹ ∈ V := (mem_normalizer_iff.mp (hAV ha) v).mp hv
  have h2 : a * v * a⁻¹ * v⁻¹ ∈ V := V.mul_mem h1 (V.inv_mem hv)
  simpa [commutatorElement_def] using h2

include d in
theorem U4NatData.ts_plane [Finite G] (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A → A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
      2 ^ (2 * n) ≤ (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A →
      (∀ u ∈ ⁅A, V⁆, u ≠ 1 → d.sing u) →
      ⁅A, V⁆ = V ⊓ centralizer (A : Set G) ∧ Nat.card ↥(⁅A, V⁆) = 2 ^ (4 * n) := by
  intro A hAM hA hAL hrel hts
  obtain ⟨σ, hσ, h2, hS, hnorm⟩ := statedSU_data_norm d d.card_F
  have hAV := le_normalizer_of_le_LC hLM hMV hAL
  have hcV := commutator_le_of_le_normalizer' hAV
  have hsing : ∀ y ∈ commSp (d.phiA hS hLM hMV hAL).range, herm σ y y = 0 := by
    intro y hy
    obtain ⟨w, rfl⟩ := d.eqv.surjective y
    have hwc : (w : G) ∈ ⁅A, V⁆ := (d.mem_comm_iff hS hLM hMV hAL w).mpr hy
    by_cases hw1 : (w : G) = 1
    · have : w = 1 := Subtype.ext hw1
      rw [this, d.eqv_one]
      simp
    · obtain ⟨hx, hsum⟩ := hts (w : G) hwc hw1
      simp only [herm_def, hnorm]
      exact hsum
  have hcardE : 2 ^ (2 * n) ≤ Nat.card ↥(d.phiA hS hLM hMV hAL).range := by
    rw [d.card_range_phiA hS hLM hMV hAL]; exact hrel
  obtain ⟨heq, hcard⟩ := ts_plane_model hσ h2 (d.phiA_sq hS hLM hMV hAL hA)
    (d.phiA_comm hS hLM hMV hAL hA) hn d.card_F hcardE hsing
  refine ⟨?_, ?_⟩
  · ext g
    constructor
    · intro hg
      have hgV := hcV hg
      refine ⟨hgV, ?_⟩
      have h1 := (d.mem_comm_iff hS hLM hMV hAL ⟨g, hgV⟩).mp hg
      rw [heq] at h1
      exact (d.mem_fix_iff hS hLM hMV hAL ⟨g, hgV⟩).mpr h1
    · rintro ⟨hgV, hgC⟩
      have h1 := (d.mem_fix_iff hS hLM hMV hAL ⟨g, hgV⟩).mp hgC
      rw [← heq] at h1
      exact (d.mem_comm_iff hS hLM hMV hAL ⟨g, hgV⟩).mpr h1
  · rw [← hcard]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : ↥⁅A, V⁆ => (⟨d.eqv ⟨x.1, hcV x.2⟩,
        (d.mem_comm_iff hS hLM hMV hAL ⟨x.1, hcV x.2⟩).mp x.2⟩ :
          ↥(commSp (d.phiA hS hLM hMV hAL).range))) ⟨?_, ?_⟩)
    · intro x x' h
      have h1 : d.eqv ⟨x.1, hcV x.2⟩ = d.eqv ⟨x'.1, hcV x'.2⟩ := congrArg Subtype.val h
      exact Subtype.ext (congrArg (fun z : ↥V => (z : G)) (d.eqv.injective h1))
    · rintro ⟨y, hy⟩
      obtain ⟨w, rfl⟩ := d.eqv.surjective y
      exact ⟨⟨(w : G), (d.mem_comm_iff hS hLM hMV hAL w).mpr hy⟩, rfl⟩

include d in
theorem U4NatData.transvection [Finite G] (hn : 1 ≤ n) (hLM : L ≤ M)
    (hMV : M ≤ normalizer (V : Set G)) :
    ∀ A : Subgroup G, A ≤ M → IsElemAbelian 2 A → A ≤ L ⊔ (M ⊓ centralizer (V : Set G)) →
      (A ⊓ (M ⊓ centralizer (V : Set G))).relIndex A = 2 ^ (4 * n) →
      (∀ u ∈ ⁅A, V⁆, u ≠ 1 → d.sing u) →
      ∃ B : Subgroup G, B ≤ A ∧ A ⊓ (M ⊓ centralizer (V : Set G)) ≤ B ∧
        Nat.card ↥B = 2 ^ n * Nat.card ↥(A ⊓ (M ⊓ centralizer (V : Set G))) ∧
        B = A ⊓ centralizer ((V ⊓ centralizer (B : Set G) : Subgroup G) : Set G) := by
  intro A hAM hA hAL hrel hts
  obtain ⟨σ, hσ, h2, hS, hnorm⟩ := statedSU_data_norm d d.card_F
  have hAV := le_normalizer_of_le_LC hLM hMV hAL
  set Φ := d.phiA hS hLM hMV hAL with hΦ
  have hcardE : Nat.card ↥Φ.range = 2 ^ (4 * n) := by
    rw [hΦ, d.card_range_phiA hS hLM hMV hAL]; exact hrel
  obtain ⟨Bb, hBbE, hBbcard, hBbiff⟩ := transvection_model hσ h2 (d.phiA_sq hS hLM hMV hAL hA)
    (d.phiA_comm hS hLM hMV hAL hA) hn d.card_F hcardE
  let Bc : Subgroup ↥A := Bb.comap Φ
  refine ⟨Bc.map A.subtype, Subgroup.map_subtype_le Bc, ?_, ?_, ?_⟩
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
    show Φ ⟨x, hx.1⟩ ∈ Bb
    rw [(d.phiA_eq_one_iff hS hLM hMV hAL ⟨x, hx.1⟩).mpr hx.2.2]
    exact Bb.one_mem
  ·
    have hmapcard : Nat.card ↥(Bc.map A.subtype) = Nat.card ↥Bc :=
      Subgroup.card_map_of_injective A.subtype_injective
    let ΦB : ↥Bc →* SUid σ 4 := Φ.comp Bc.subtype
    have hrange : ΦB.range = Bb := by
      ext b
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hb
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (hBbE hb)
        exact ⟨⟨a, by show Φ a ∈ Bb; rw [ha]; exact hb⟩, ha⟩
    have hker : Nat.card ↥ΦB.ker = Nat.card ↥Φ.ker := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩
          invFun := fun y => ⟨⟨y.1, by
              show Φ y.1 ∈ Bb
              rw [MonoidHom.mem_ker.mp y.2]
              exact Bb.one_mem⟩, MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp y.2)⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    have h := Subgroup.card_ker_mul_card_range ΦB
    rw [hker, hrange, hBbcard, hΦ, d.card_ker_phiA hS hLM hMV hAL] at h
    rw [hmapcard, ← h, mul_comm]
  ·
    have hfixV : ∀ v : ↥V, (v : G) ∈ centralizer ((Bc.map A.subtype : Subgroup G) : Set G) ↔
        ∀ b ∈ Bb, b • d.eqv v = d.eqv v := by
      intro v
      constructor
      · intro hv b hb
        obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp (hBbE hb)
        have hmem : (a : G) ∈ Bc.map A.subtype := Subgroup.mem_map.mpr ⟨a, hb, rfl⟩
        have hc := Subgroup.mem_centralizer_iff.mp hv (a : G) hmem
        rw [d.phiA_spec hS hLM hMV hAL a v]
        refine congrArg d.eqv (Subtype.ext ?_)
        show (a : G) * v * (a : G)⁻¹ = v
        calc (a : G) * v * (a : G)⁻¹ = ((v : G) * (a : G)) * (a : G)⁻¹ := by rw [hc]
          _ = v := by group
      · intro hf
        refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
        obtain ⟨a, haBc, rfl⟩ := Subgroup.mem_map.mp hh
        have h1 := hf (Φ a) haBc
        rw [d.phiA_spec hS hLM hMV hAL a v] at h1
        have h2 : conjOn V a.1 (le_normalizer_of_le_LC hLM hMV hAL a.2) v = v :=
          d.eqv.injective h1
        have h3 : (a : G) * v * (a : G)⁻¹ = v := congrArg Subtype.val h2
        show (a : G) * v = v * (a : G)
        calc (a : G) * v = ((a : G) * v * (a : G)⁻¹) * (a : G) := by group
          _ = v * (a : G) := by rw [h3]
    ext a
    constructor
    · intro ha
      obtain ⟨a', ha'B, rfl⟩ := Subgroup.mem_map.mp ha
      refine ⟨a'.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      let v : ↥V := ⟨y, hy.1⟩
      have h1 := (hfixV v).mp hy.2 (Φ a') ha'B
      rw [d.phiA_spec hS hLM hMV hAL a' v] at h1
      have h2 : conjOn V a'.1 (le_normalizer_of_le_LC hLM hMV hAL a'.2) v = v :=
        d.eqv.injective h1
      have h3 : (a' : G) * y * (a' : G)⁻¹ = y := congrArg Subtype.val h2
      show y * (a' : G) = (a' : G) * y
      calc y * (a' : G) = ((a' : G) * y * (a' : G)⁻¹) * (a' : G) := by rw [h3]
        _ = (a' : G) * y := by group
    · rintro ⟨haA, hacen⟩
      let ā : ↥A := ⟨a, haA⟩
      have hmem : Φ ā ∈ Bb := by
        refine (hBbiff (Φ ā)).mpr ⟨MonoidHom.mem_range.mpr ⟨ā, rfl⟩, fun x hx => ?_⟩
        obtain ⟨v, rfl⟩ := d.eqv.surjective x
        have hvC : (v : G) ∈ centralizer ((Bc.map A.subtype : Subgroup G) : Set G) :=
          (hfixV v).mpr hx
        have hc := Subgroup.mem_centralizer_iff.mp hacen (v : G) ⟨v.2, hvC⟩
        rw [d.phiA_spec hS hLM hMV hAL ā v]
        refine congrArg d.eqv (Subtype.ext ?_)
        show a * v * a⁻¹ = v
        calc a * (v : G) * a⁻¹ = ((v : G) * a) * a⁻¹ := by rw [hc]
          _ = v := by group
      exact Subgroup.mem_map.mpr ⟨ā, hmem, rfl⟩

end Facts

end CFSG.LocalAnalysis.RankThreeUC

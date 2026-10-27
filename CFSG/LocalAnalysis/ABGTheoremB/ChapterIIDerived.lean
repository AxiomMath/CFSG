module

public import CFSG.LocalAnalysis.ABGTheoremB.Facts
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.GroupTheory.ABGLocalTools.Criteria

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise commutatorElement

universe u

section General

variable {G : Type u} [Group G]

private theorem mem_normalizer_of_conj_mem [Finite G] {J : Subgroup G} {g : G}
    (h : ∀ y ∈ J, g * y * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem isSolvable_sup_of_le_normalizer {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) [Group.IsSolvable A] [Group.IsSolvable B] :
    Group.IsSolvable (A ⊔ B : Subgroup G) := by
  have hJA : A ⊔ B ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hBA
  have hn : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hJA
  have : Group.IsSolvable (A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ B)).toMonoidHom)
      (MulEquiv.injective _)
  let f : B →* (A ⊔ B : Subgroup G) ⧸ A.subgroupOf (A ⊔ B) :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨j, hj⟩, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf (A ⊔ B)) y
    have hj' : j ∈ ((B ⊔ A : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact hj
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBA] at hj'
    obtain ⟨b, hb, a, ha, rfl⟩ := hj'
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using ha
  have : Group.IsSolvable ((A ⊔ B : Subgroup G) ⧸ A.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient (A.subgroupOf (A ⊔ B))

private theorem oddCore_le_solvableRadical (K : Type*) [Group K] [Finite K] :
    CFSG.oddCore K ≤ CFSG.solvableRadical K :=
  le_sSup ⟨inferInstance, CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ABGTheoremB.odd_card_oddCore K)⟩

private theorem isSolvable_of_le {J K : Subgroup G} (hJK : J ≤ K) [Group.IsSolvable K] :
    Group.IsSolvable J :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJK)
    (Subgroup.inclusion_injective hJK)

private theorem isSolvable_oddCoreIn [Finite G] (K : Subgroup G) :
    Group.IsSolvable (oddCoreIn K) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ (odd_card_oddCoreIn K)

private theorem isSolvable_solvRadIn [Finite G] (K : Subgroup G) :
    Group.IsSolvable (solvRadIn K) := by
  have : Group.IsSolvable (CFSG.solvableRadical K) := solvableRadical_isSolvable
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((CFSG.solvableRadical K).equivMapOfInjective K.subtype
      K.subtype_injective).symm.toMonoidHom) (MulEquiv.injective _)

private theorem le_normalizer_solvRadIn (K : Subgroup G) :
    K ≤ Subgroup.normalizer (solvRadIn K : Set G) := by
  have : (CFSG.solvableRadical K).Normal := solvableRadical_normal
  exact CFSG.ABGTheoremB.le_normalizer_map_subtype K _

private theorem le_solvRadIn {K J : Subgroup G} (hJK : J ≤ K)
    (hnorm : K ≤ Subgroup.normalizer (J : Set G)) [Group.IsSolvable J] : J ≤ solvRadIn K := by
  have hn : (J.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).mpr hnorm
  have hs : Group.IsSolvable (J.subgroupOf K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hJK).toMonoidHom) (MulEquiv.injective _)
  have hle : J.subgroupOf K ≤ CFSG.solvableRadical K := le_sSup ⟨hn, hs⟩
  intro j hj
  exact ⟨⟨j, hJK hj⟩, hle hj, rfl⟩

private theorem normalizer_le_normalizer_solvRadIn [Finite G] (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (solvRadIn K : Set G) := by
  intro n hn
  apply mem_normalizer_of_conj_mem
  have hK : ∀ k ∈ K, n * k * n⁻¹ ∈ K := fun k hk => (Subgroup.mem_normalizer_iff.mp hn k).mp hk
  let φ : K →* K :=
    ((MulAut.conj n).toMonoidHom.comp K.subtype).codRestrict K (fun k => hK k k.2)
  have hφ : Function.Surjective φ := by
    intro k
    have hk : n⁻¹ * k * n ∈ K := by
      refine (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * k * n)).mpr ?_
      rw [show n * (n⁻¹ * k * n) * n⁻¹ = k by group]
      exact k.2
    refine ⟨⟨n⁻¹ * k * n, hk⟩, Subtype.ext ?_⟩
    change n * (n⁻¹ * k * n) * n⁻¹ = k
    group
  have : Group.IsSolvable (CFSG.solvableRadical K) := solvableRadical_isSolvable
  have hnorm : ((CFSG.solvableRadical K).map φ).Normal :=
    (solvableRadical_normal (H := K)).map φ hφ
  have hsolv : Group.IsSolvable ((CFSG.solvableRadical K).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective _)
  have hle : (CFSG.solvableRadical K).map φ ≤ CFSG.solvableRadical K := le_sSup ⟨hnorm, hsolv⟩
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨φ y, hle ⟨y, hy, rfl⟩, rfl⟩

private theorem eq_one_of_mem_of_mem_of_odd {A K : Subgroup G} (hA : IsPGroup 2 A)
    (hK : Odd (Nat.card K)) {g : G} (hgA : g ∈ A) (hgK : g ∈ K) : g = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨g, hgA⟩
  have h1 : orderOf g ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hK)) h1 (Subgroup.orderOf_dvd_natCard K hgK))

private theorem isSylowOf_of_sylow_le [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {K : Subgroup G} (hPK : (P : Subgroup G) ≤ K) : IsSylowOf p (P : Subgroup G) K :=
  isSylowOf_iff.mpr ⟨hPK, P.isPGroup', fun hdvd =>
    P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPK))⟩

private theorem eq_top_of_commutator_mem_of_ker_le {L Q : Type*} [Group L] [Group Q]
    {ψ : L →* Q} (hψ : Function.Surjective ψ) (hQ : commutator Q = ⊤) {X : Subgroup L}
    (hcomm : ∀ a b : L, ⁅a, b⁆ ∈ X) (hker : ψ.ker ≤ X) : X = ⊤ := by
  have hc : commutator L ≤ X := by
    rw [commutator_def]
    exact Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  rw [eq_top_iff]
  intro l _
  have hl : ψ l ∈ (commutator L).map ψ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψ,
      ← commutator_def, hQ]
    exact Subgroup.mem_top _
  obtain ⟨c, hc', hcl⟩ := hl
  have hker' : c⁻¹ * l ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hcl, inv_mul_cancel]
  have h := X.mul_mem (hc hc') (hker hker')
  rwa [mul_inv_cancel_left] at h

private theorem not_isSolvable_SL2 (F : Type*) [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro hsolv
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hF
  let u : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  have hu : u ≠ 1 := by
    intro h
    have h01 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
      (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [u] at h01
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := ⟨⟨u, 1, hu⟩⟩
  have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial
    (Matrix.SpecialLinearGroup (Fin 2) F)
  rw [hperf.commutator_eq_top] at hlt
  exact lt_irrefl _ hlt

private theorem map_map_center_subtype (K : Subgroup G) (Q : Subgroup K) :
    ((Subgroup.center Q).map Q.subtype).map K.subtype = centerOf (Q.map K.subtype) := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨⟨q, q.2, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h := Subgroup.mem_center_iff.mp hq ⟨y, hy⟩
    exact congrArg (fun t : Q => ((t : K) : G)) h
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨⟨y, hy⟩, Subgroup.mem_center_iff.mpr fun q => ?_, rfl⟩, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hc) _ ⟨q, q.2, rfl⟩

private theorem map_centralizer_subgroupOf {K P : Subgroup G} (hPK : P ≤ K) :
    (Subgroup.centralizer ((P.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      K ⊓ Subgroup.centralizer (P : Set G) := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨k.2, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hk) ⟨p, hPK hp⟩ hp)
  · rintro ⟨hxK, hx⟩
    refine ⟨⟨x, hxK⟩, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_, rfl⟩
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) p hp)

private theorem conj_mem_centerOf {P Q : Subgroup G} {k : G}
    (hconj : ∀ y, y ∈ Q ↔ k⁻¹ * y * k ∈ P) {z : G} (hz : z ∈ centerOf P) :
    k * z * k⁻¹ ∈ centerOf Q := by
  refine Subgroup.mem_inf.mpr ⟨(hconj _).mpr ?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
  · rw [show k⁻¹ * (k * z * k⁻¹) * k = z by group]
    exact (Subgroup.mem_inf.mp hz).1
  · intro s hs
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 _ ((hconj s).mp hs)
    calc s * (k * z * k⁻¹) = k * ((k⁻¹ * s * k) * z) * k⁻¹ := by group
      _ = k * (z * (k⁻¹ * s * k)) * k⁻¹ := by rw [hc]
      _ = k * z * k⁻¹ * s := by group

private theorem conj_inv_mem_centerOf {P Q : Subgroup G} {k : G}
    (hconj : ∀ y, y ∈ Q ↔ k⁻¹ * y * k ∈ P) {z : G} (hz : z ∈ centerOf Q) :
    k⁻¹ * z * k ∈ centerOf P := by
  refine Subgroup.mem_inf.mpr ⟨(hconj z).mp (Subgroup.mem_inf.mp hz).1,
    Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
  have hs' : k * s * k⁻¹ ∈ Q := by
    refine (hconj _).mpr ?_
    rw [show k⁻¹ * (k * s * k⁻¹) * k = s by group]
    exact hs
  have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 _ hs'
  calc s * (k⁻¹ * z * k) = k⁻¹ * ((k * s * k⁻¹) * z) * k := by group
    _ = k⁻¹ * (z * (k * s * k⁻¹)) * k := by rw [hc]
    _ = k⁻¹ * z * k * s := by group

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

private theorem L_subset_mul_ON (hσ : σ.IsValid) (hN : σ.NStructure) {H : Subgroup G}
    (hDH : σ.D ≤ H) (hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G)) :
    (σ.L : Set G) ⊆ (H : Set G) * (σ.ON : Set G) := by
  have hnorm : H ⊓ σ.N ≤ Subgroup.normalizer (σ.ON : Set G) :=
    inf_le_right.trans σ.N_le_normalizer_ON
  have h1 : σ.L ≤ H ⊓ σ.N ⊔ σ.ON := by
    rw [hN.L_eq]
    refine sup_le (fun l hl => ?_) ?_
    · have h := σ.L₀_subset_inf_N_mul_ON hσ hcov hl
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at h
      exact h
    · exact inf_le_left.trans ((le_inf hDH (σ.D_le_N hσ)).trans le_sup_left)
  intro l hl
  have h := h1 hl
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm] at h
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact ⟨a, (Subgroup.mem_inf.mp ha).1, b, hb, rfl⟩

private theorem centerOf_sylow_eq_centerOf_D (hσ : σ.IsValid) (hN : σ.NStructure)
    (S₂ : Sylow 2 G) (hDS₂ : σ.D ≤ (S₂ : Subgroup G)) :
    centerOf (S₂ : Subgroup G) = centerOf σ.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxZ := (hN.center_involution_of_sylow S₂ hDS₂).1
  have hS₂N : (S₂ : Subgroup G) ≤ σ.N := by
    intro s hs
    rw [σ.mem_N_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxZ).2 s hs
  obtain ⟨n, hn, hconj⟩ := (isSylowOf_of_sylow_le σ.S (σ.S_le_N hσ)).exists_mem_conj
    (isSylowOf_of_sylow_le S₂ hS₂N)
  rw [← hN.center_S_eq_center_D]
  set Z := centerOf (σ.S : Subgroup G) with hZ
  have hZS₂ : Z ≤ S₂ := by
    rw [hZ, hN.center_S_eq_center_D]
    exact inf_le_left.trans hDS₂
  have ha : ∀ z ∈ Z, n * z * n⁻¹ ∈ centerOf (S₂ : Subgroup G) := fun z hz =>
    conj_mem_centerOf hconj hz
  have hb : centerOf (S₂ : Subgroup G) ≤ Z := by
    intro z hz
    have hzS₂ := (Subgroup.mem_inf.mp hz).1
    have hz' : n⁻¹ * z * n ∈ Z := conj_inv_mem_centerOf hconj hz
    have hzS : z ∈ solvRadIn σ.N := by
      have h1 : n⁻¹ * z * n ∈ solvRadIn σ.N := by
        rw [hN.N_solvRad]
        exact Subgroup.mem_sup_right hz'
      have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_solvRadIn σ.N hn) _).mp h1
      rwa [show n * (n⁻¹ * z * n) * n⁻¹ = z by group] at h2
    have hZON : Z ≤ Subgroup.normalizer (σ.ON : Set G) :=
      (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON
    rw [← SetLike.mem_coe, hN.N_solvRad, sup_comm,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZON] at hzS
    obtain ⟨z', hz'Z, m, hm, rfl⟩ := hzS
    have hmS₂ : m ∈ (S₂ : Subgroup G) := by
      have h := (S₂ : Subgroup G).mul_mem ((S₂ : Subgroup G).inv_mem (hZS₂ hz'Z)) hzS₂
      rwa [inv_mul_cancel_left] at h
    change z' * m ∈ Z
    rw [eq_one_of_mem_of_mem_of_odd S₂.isPGroup' σ.odd_card_ON hmS₂ hm, mul_one]
    exact hz'Z
  have hnZ : n ∈ Subgroup.normalizer (Z : Set G) :=
    mem_normalizer_of_conj_mem fun z hz => hb (ha z hz)
  refine le_antisymm hb fun z hz => ?_
  have h1 : n⁻¹ * z * n ∈ Z := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnZ) z).mp hz
    rwa [inv_inv] at h
  have h2 := ha _ h1
  rwa [show n * (n⁻¹ * z * n) * n⁻¹ = z by group] at h2

private theorem mem_solvRadIn_N_of_commutator_mem (hσ : σ.IsValid) (hN : σ.NStructure) {n : G}
    (hn : n ∈ σ.N) (hcomm : ∀ l ∈ σ.L₀, n * l * n⁻¹ * l⁻¹ ∈ solvRadIn σ.N) :
    n ∈ solvRadIn σ.N := by
  set R := solvRadIn σ.N with hR
  have hNR : σ.N ≤ Subgroup.normalizer (R : Set G) := le_normalizer_solvRadIn σ.N
  have hconjR : ∀ g ∈ σ.N, ∀ y ∈ R, g * y * g⁻¹ ∈ R := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hNR hg) y).mp hy
  have hconjL : ∀ g ∈ σ.N, ∀ l ∈ σ.L₀, g * l * g⁻¹ ∈ σ.L₀ := fun g hg l hl =>
    (Subgroup.mem_normalizer_iff.mp (hσ.N_le_normalizer_L₀ hg) l).mp hl
  let C : Subgroup G :=
    { carrier := {c | c ∈ σ.N ∧ ∀ l ∈ σ.L₀, c * l * c⁻¹ * l⁻¹ ∈ R}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨σ.N.mul_mem ha hb, fun l hl => ?_⟩
        rw [show a * b * l * (a * b)⁻¹ * l⁻¹ =
          a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ * (a * l * a⁻¹ * l⁻¹) by group]
        exact R.mul_mem (hconjR a ha _ (hb' l hl)) (ha' l hl)
      one_mem' := ⟨σ.N.one_mem, fun l _ => by
        rw [show (1 : G) * l * 1⁻¹ * l⁻¹ = 1 by group]
        exact R.one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨σ.N.inv_mem ha, fun l hl => ?_⟩
        have hl' : a⁻¹ * l * a⁻¹⁻¹ ∈ σ.L₀ := hconjL _ (σ.N.inv_mem ha) l hl
        have h := R.inv_mem (ha' _ hl')
        rwa [show (a * (a⁻¹ * l * a⁻¹⁻¹) * a⁻¹ * (a⁻¹ * l * a⁻¹⁻¹)⁻¹)⁻¹ =
          a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ by group] at h }
  have hCN : C ≤ σ.N := fun c hc => hc.1
  have hRC : R ≤ C := by
    intro r hr
    refine ⟨solvRadIn_le σ.N hr, fun l hl => ?_⟩
    have h := hconjR l (hσ.L₀_le_N hl) _ (R.inv_mem hr)
    rw [show r * l * r⁻¹ * l⁻¹ = r * (l * r⁻¹ * l⁻¹) by group]
    exact R.mul_mem hr h
  have hNC : σ.N ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    rintro c ⟨hc, hc'⟩
    refine ⟨σ.N.mul_mem (σ.N.mul_mem hg hc) (σ.N.inv_mem hg), fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ σ.L₀ := hconjL _ (σ.N.inv_mem hg) l hl
    have h := hconjR g hg _ (hc' _ hl')
    rwa [show g * (c * (g⁻¹ * l * g⁻¹⁻¹) * c⁻¹ * (g⁻¹ * l * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * c * g⁻¹ * l * (g * c * g⁻¹)⁻¹ * l⁻¹ by group] at h
  by_contra hnR
  have hCR : ¬ C ≤ R := fun h => hnR (h ⟨hn, hcomm⟩)
  have hL₀C : σ.L₀ ≤ C := by
    have h := hN.N_minimalNormal C hCN hNC hCR
    rwa [sup_eq_left.mpr hRC] at h
  obtain ⟨F, _, _, hF, ψ, hψ, hker⟩ := hσ.L₀_quotient
  have hq : 4 ≤ Nat.card F := by
    have := hσ.five_lt_q
    omega
  have hperf := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F hq
  have htop : R.subgroupOf σ.L₀ = ⊤ := by
    refine eq_top_of_commutator_mem_of_ker_le hψ hperf.commutator_eq_top (fun a b => ?_) ?_
    · rw [Subgroup.mem_subgroupOf, commutatorElement_def]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (hL₀C a.2).2 b b.2
    · rw [hker]
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      rw [hR, hN.N_solvRad]
      exact Subgroup.mem_sup_left hy
  have hL₀R : σ.L₀ ≤ R := by
    intro l hl
    have h : (⟨l, hl⟩ : σ.L₀) ∈ R.subgroupOf σ.L₀ := htop ▸ Subgroup.mem_top _
    exact h
  have : Group.IsSolvable R := isSolvable_solvRadIn σ.N
  have : Group.IsSolvable σ.L₀ := isSolvable_of_le hL₀R
  exact not_isSolvable_SL2 F hq (Group.isSolvable_of_surjective hψ)

private theorem solvRadIn_inf_N_le (hσ : σ.IsValid) (hN : σ.NStructure) {H : Subgroup G}
    (hcov : (σ.L₀ : Set G) ⊆ (H : Set G) * (σ.ON : Set G)) :
    solvRadIn H ⊓ σ.N ≤ solvRadIn σ.N := by
  set Y := solvRadIn H ⊓ σ.N with hY
  have : Group.IsSolvable (solvRadIn H) := isSolvable_solvRadIn H
  have : Group.IsSolvable Y := isSolvable_of_le inf_le_left
  have : Group.IsSolvable σ.ON := isSolvable_oddCoreIn σ.N
  have hYON : Y ≤ Subgroup.normalizer (σ.ON : Set G) := inf_le_right.trans σ.N_le_normalizer_ON
  have : Group.IsSolvable (σ.ON ⊔ Y : Subgroup G) := isSolvable_sup_of_le_normalizer hYON
  have hL₀W : σ.L₀ ≤ Subgroup.normalizer ((σ.ON ⊔ Y : Subgroup G) : Set G) := by
    intro l hl
    obtain ⟨k, hk, o, ho, rfl⟩ := σ.L₀_subset_inf_N_mul_ON hσ hcov hl
    obtain ⟨hkH, hkN⟩ := Subgroup.mem_inf.mp hk
    have hkY : k ∈ Subgroup.normalizer (Y : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨le_normalizer_solvRadIn H hkH,
        Subgroup.le_normalizer hkN⟩
    exact Subgroup.mul_mem _ (normalizer_inf_normalizer_le_normalizer_sup σ.ON Y
      ⟨σ.N_le_normalizer_ON hkN, hkY⟩) (Subgroup.le_normalizer (Subgroup.mem_sup_left ho))
  have hV : (σ.ON ⊔ Y) ⊓ σ.L₀ ≤ solvRadIn σ.L₀ := by
    have : Group.IsSolvable ((σ.ON ⊔ Y) ⊓ σ.L₀ : Subgroup G) := isSolvable_of_le inf_le_left
    exact le_solvRadIn inf_le_right ((le_inf hL₀W Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf)
  have hL₀N : solvRadIn σ.L₀ ≤ solvRadIn σ.N := by
    have : Group.IsSolvable (solvRadIn σ.L₀) := isSolvable_solvRadIn σ.L₀
    exact le_solvRadIn ((solvRadIn_le _).trans hσ.L₀_le_N)
      (hσ.N_le_normalizer_L₀.trans (normalizer_le_normalizer_solvRadIn σ.L₀))
  intro y hy
  refine σ.mem_solvRadIn_N_of_commutator_mem hσ hN (Subgroup.mem_inf.mp hy).2 fun l hl => ?_
  refine hL₀N (hV (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
  · have h1 : l * y⁻¹ * l⁻¹ ∈ σ.ON ⊔ Y :=
      (Subgroup.mem_normalizer_iff.mp (hL₀W hl) y⁻¹).mp (Subgroup.mem_sup_right (Y.inv_mem hy))
    have h2 := (σ.ON ⊔ Y).mul_mem (Subgroup.mem_sup_right hy) h1
    rwa [show y * (l * y⁻¹ * l⁻¹) = y * l * y⁻¹ * l⁻¹ by group] at h2
  · have h1 : y * l * y⁻¹ ∈ σ.L₀ :=
      (Subgroup.mem_normalizer_iff.mp (hσ.N_le_normalizer_L₀ (Subgroup.mem_inf.mp hy).2) l).mp hl
    exact σ.L₀.mul_mem h1 (σ.L₀.inv_mem hl)

theorem qgroup_solvRad_of (hσ : σ.IsValid) (hN : σ.NStructure)
    (hcover : ∀ H : Subgroup G, σ.T ≤ H → oddCoreIn H ≠ ⊥ →
      (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON →
        CFSG.ABGQGroups.HasQCharPower H σ.q ∧ oddCoreIn H ⊔ (H ⊓ σ.N) = H) :
    ∀ H : Subgroup G, σ.D ≤ H → oddCoreIn H ≠ ⊥ →
      (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON → solvRadIn H = oddCoreIn H ⊔ centerOf σ.D := by
  intro H hDH hO hcov
  have hfac := (hcover H ((σ.T_le_D hσ).trans hDH) hO hcov).2
  have hONH := σ.ON_inf_le_oddCoreIn_of_sup_eq hfac
  set Z := centerOf σ.D with hZ
  have hZD : Z ≤ σ.D := inf_le_left
  have hZH : Z ≤ H := hZD.trans hDH
  have hZS : centerOf (σ.S : Subgroup G) = Z := hN.center_S_eq_center_D
  have hZON : Z ≤ Subgroup.normalizer (σ.ON : Set G) :=
    (hZD.trans (σ.D_le_N hσ)).trans σ.N_le_normalizer_ON
  have hZSN : Z ≤ solvRadIn σ.N := by
    rw [hN.N_solvRad, hZS]
    exact le_sup_right
  have hSN : ((solvRadIn σ.N : Subgroup G) : Set G) = (Z : Set G) * (σ.ON : Set G) := by
    rw [hN.N_solvRad, hZS, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZON
  have hOS : oddCoreIn H ≤ solvRadIn H := Subgroup.map_mono (oddCore_le_solvableRadical H)
  have hHO : H ≤ Subgroup.normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  apply le_antisymm
  ·
    intro s hs
    have hsH : s ∈ ((H ⊓ σ.N ⊔ oddCoreIn H : Subgroup G) : Set G) := by
      rw [sup_comm, hfac]
      exact solvRadIn_le H hs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hHO)] at hsH
    obtain ⟨n, hn, o, ho, rfl⟩ := hsH
    have hnS : n ∈ solvRadIn H := by
      have h := (solvRadIn H).mul_mem hs ((solvRadIn H).inv_mem (hOS ho))
      rwa [mul_inv_cancel_right] at h
    have hnSN : n ∈ ((solvRadIn σ.N : Subgroup G) : Set G) :=
      σ.solvRadIn_inf_N_le hσ hN hcov (Subgroup.mem_inf.mpr ⟨hnS, (Subgroup.mem_inf.mp hn).2⟩)
    rw [hSN] at hnSN
    obtain ⟨z, hz, o', ho', hzo⟩ := hnSN
    have hzo : z * o' = n := hzo
    have ho'H : o' ∈ H := by
      have h := H.mul_mem (H.inv_mem (hZH hz)) (Subgroup.mem_inf.mp hn).1
      rwa [← hzo, inv_mul_cancel_left] at h
    have ho'O : o' ∈ oddCoreIn H := hONH (Subgroup.mem_inf.mpr ⟨ho', ho'H⟩)
    change n * o ∈ oddCoreIn H ⊔ Z
    rw [← hzo, mul_assoc]
    exact (oddCoreIn H ⊔ Z).mul_mem (Subgroup.mem_sup_right hz)
      (Subgroup.mem_sup_left ((oddCoreIn H).mul_mem ho'O ho))
  ·
    have : Group.IsSolvable (oddCoreIn H) := isSolvable_oddCoreIn H
    have : Group.IsSolvable Z := Group.isSolvable_of_comm fun a b => Subtype.ext
      ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp b.2).2) a (Subgroup.mem_inf.mp a.2).1)
    have : Group.IsSolvable (oddCoreIn H ⊔ Z : Subgroup G) :=
      isSolvable_sup_of_le_normalizer (hZH.trans hHO)
    refine le_solvRadIn (sup_le (oddCoreIn_le H) hZH)
      (hfac.ge.trans (sup_le (le_sup_left.trans Subgroup.le_normalizer) fun g hg => ?_))
    obtain ⟨hgH, hgN⟩ := Subgroup.mem_inf.mp hg
    apply mem_normalizer_of_conj_mem
    have hle : oddCoreIn H ⊔ Z ≤ (oddCoreIn H ⊔ Z).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun o ho => ?_) (fun z hz => ?_)
      · rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hHO hgH) o).mp ho)
      · rw [Subgroup.mem_comap]
        change g * z * g⁻¹ ∈ oddCoreIn H ⊔ Z
        have h1 : g * z * g⁻¹ ∈ ((solvRadIn σ.N : Subgroup G) : Set G) :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_solvRadIn σ.N hgN) z).mp (hZSN hz)
        rw [hSN] at h1
        obtain ⟨z', hz', o, ho, hzo⟩ := h1
        have hzo : z' * o = g * z * g⁻¹ := hzo
        have hoH : o ∈ H := by
          have h := H.mul_mem (H.inv_mem (hZH hz'))
            (H.mul_mem (H.mul_mem hgH (hZH hz)) (H.inv_mem hgH))
          rwa [← hzo, inv_mul_cancel_left] at h
        rw [← hzo]
        exact (oddCoreIn H ⊔ Z).mul_mem (Subgroup.mem_sup_right hz')
          (Subgroup.mem_sup_left (hONH (Subgroup.mem_inf.mpr ⟨ho, hoH⟩)))
    exact fun y hy => hle hy

theorem qgroup_constraint_criterion_of (hσ : σ.IsValid) (hN : σ.NStructure)
    (hrad : ∀ H : Subgroup G, σ.D ≤ H → oddCoreIn H ≠ ⊥ →
      (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON → solvRadIn H = oddCoreIn H ⊔ centerOf σ.D) :
    ∀ H : Subgroup G, σ.D ≤ H → oddCoreIn H ≠ ⊥ →
      (σ.L₀ : Set G) ⊆ (H : Set G) * σ.ON → ∀ S₁ : Subgroup G, IsSylowOf 2 S₁ H →
        ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ P : Subgroup G,
          IsSylowOf r P (oddCoreIn H) → S₁ ≤ Subgroup.normalizer (P : Set G) →
            (PConstrainedWithin r H (CFSG.solvableRadical H) ↔
                IsSylowOf 2 (centerOf S₁ ⊓ Subgroup.centralizer (P : Set G))
                  (H ⊓ Subgroup.centralizer (P : Set G))) ∧
              (PConstrainedWithin r H (CFSG.oddCore H) ↔
                Odd (Nat.card (H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G))) := by
  intro H hDH hO hcov S₁ hS₁ r hr hr2 P hP hS₁P
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH := hrad H hDH hO hcov
  have hOS : oddCoreIn H ≤ solvRadIn H := Subgroup.map_mono (oddCore_le_solvableRadical H)
  have hHS : H ≤ Subgroup.normalizer (solvRadIn H : Set G) := le_normalizer_solvRadIn H
  have hHO : H ≤ Subgroup.normalizer (oddCoreIn H : Set G) := le_normalizer_oddCoreIn H
  set Z := centerOf σ.D with hZ
  have hZH : Z ≤ H := inf_le_left.trans hDH
  obtain ⟨P₂, hP₂⟩ := σ.exists_sylow_two_le_inf_L hσ (σ.L_subset_mul_ON hσ hN hDH hcov)
  have hP₂H : (P₂ : Subgroup G) ≤ H := hP₂.trans inf_le_left
  have hD2 : IsPGroup 2 (σ.D.subgroupOf H) := (σ.S.isPGroup'.to_le σ.D_le_S).comap_subtype
  obtain ⟨Q₀, hQ₀⟩ := hD2.exists_le_sylow
  set S₀ := (Q₀ : Subgroup H).map H.subtype with hS₀
  have hS₀H : IsSylowOf 2 S₀ H := ⟨Q₀, rfl⟩
  have hDS₀ : σ.D ≤ S₀ := fun d hd => ⟨⟨d, hDH hd⟩, hQ₀ hd, rfl⟩
  have hS₀idx : ¬ 2 ∣ S₀.index := by
    rw [← Subgroup.relIndex_mul_index hS₀H.le]
    exact Nat.prime_two.not_dvd_mul (isSylowOf_iff.mp hS₀H).2.2
      fun h => P₂.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hP₂H))
  have hZS₀ : centerOf S₀ = Z := by
    have h := σ.centerOf_sylow_eq_centerOf_D hσ hN (hS₀H.isPGroup.toSylow hS₀idx)
      (by rw [IsPGroup.toSylow_coe]; exact hDS₀)
    rwa [IsPGroup.toSylow_coe] at h
  obtain ⟨k, hk, hconj⟩ := hS₀H.exists_mem_conj hS₁
  have hradS₁ : solvRadIn H = oddCoreIn H ⊔ centerOf S₁ := by
    apply le_antisymm
    · intro y hy
      have h1 : k⁻¹ * y * k⁻¹⁻¹ ∈ ((Z ⊔ oddCoreIn H : Subgroup G) : Set G) := by
        rw [sup_comm, ← hSH]
        exact (Subgroup.mem_normalizer_iff.mp (hHS (H.inv_mem hk)) y).mp hy
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hZH.trans hHO)] at h1
      obtain ⟨z, hz, o, ho, hzo⟩ := h1
      have hzo : z * o = k⁻¹ * y * k⁻¹⁻¹ := hzo
      have hz₀ : z ∈ centerOf S₀ := by
        rw [hZS₀]
        exact hz
      have hz' : k * z * k⁻¹ ∈ centerOf S₁ := conj_mem_centerOf hconj hz₀
      have ho' : k * o * k⁻¹ ∈ oddCoreIn H := (Subgroup.mem_normalizer_iff.mp (hHO hk) o).mp ho
      have hy' : y = k * z * k⁻¹ * (k * o * k⁻¹) := by
        rw [show k * z * k⁻¹ * (k * o * k⁻¹) = k * (z * o) * k⁻¹ by group, hzo]
        group
      rw [hy']
      exact (oddCoreIn H ⊔ centerOf S₁).mul_mem (Subgroup.mem_sup_right hz')
        (Subgroup.mem_sup_left ho')
    · refine sup_le hOS fun w hw => ?_
      have hw₀ : k⁻¹ * w * k ∈ Z := by
        rw [← hZS₀]
        exact conj_inv_mem_centerOf hconj hw
      have h1 : k⁻¹ * w * k ∈ solvRadIn H := by
        rw [hSH]
        exact Subgroup.mem_sup_right hw₀
      have h2 := (Subgroup.mem_normalizer_iff.mp (hHS hk) _).mp h1
      rwa [show k * (k⁻¹ * w * k) * k⁻¹ = w by group] at h2
  have hPH : P ≤ H := hP.le.trans (oddCoreIn_le H)
  have hZ₁H : centerOf S₁ ≤ H := inf_le_left.trans hS₁.le
  obtain ⟨S', hS'⟩ := hS₁
  have hP' : IsSylowOf r (P.subgroupOf H) (CFSG.oddCore H) := by
    rw [← isSylowOf_map_subtype_iff H, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH]
    exact hP
  have hS'P' : (S' : Subgroup H) ≤
      Subgroup.normalizer ((P.subgroupOf H : Subgroup H) : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPH]
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    apply hS₁P
    rw [← hS']
    exact ⟨s, hs, rfl⟩
  have hrad' : CFSG.solvableRadical H =
      CFSG.oddCore H ⊔ (Subgroup.center S').map (S' : Subgroup H).subtype := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_map_center_subtype, hS']
    exact hradS₁
  obtain ⟨h1, h2⟩ := pConstrainedWithin_criteria_of_solvableRadical_eq hr2 S' hrad' hP' hS'P'
  rw [h1, h2]
  refine ⟨?_, ?_⟩
  · rw [← isSylowOf_map_subtype_iff H, Subgroup.map_inf_eq _ _ _ H.subtype_injective,
      map_map_center_subtype, hS', map_centralizer_subgroupOf hPH, ← inf_assoc,
      inf_eq_left.mpr hZ₁H]
  · rw [← map_centralizer_subgroupOf hPH, Subgroup.card_map_of_injective H.subtype_injective]

end Setting

end CFSG.ABGTheoremB

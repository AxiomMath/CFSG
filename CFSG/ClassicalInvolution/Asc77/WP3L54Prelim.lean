module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Balance.BootstrapAlphaConst
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

namespace Lemma54Proof

section Normalizers

variable {G : Type} [Group G]

theorem mem_normalizer_of_forall_commute {H : Subgroup G} {x : G}
    (hx : ∀ h ∈ H, x * h = h * x) : x ∈ Subgroup.normalizer (H : Set G) := by
  refine Subgroup.centralizer_le_normalizer (H : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (hx h hh).symm

theorem mem_normalizer_sup {x : G} {H K : Subgroup G} (hH : x ∈ Subgroup.normalizer (H : Set G))
    (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have h1 : conjSub x H = H := conjSub_eq_of_mem_normalizer hH
  have h2 : conjSub x K = K := conjSub_eq_of_mem_normalizer hK
  apply mem_normalizer_of_conjSub_eq
  unfold conjSub at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

theorem mem_normalizer_commutator {x : G} {H K : Subgroup G}
    (hH : x ∈ Subgroup.normalizer (H : Set G)) (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((⁅H, K⁆ : Subgroup G) : Set G) := by
  have h1 : conjSub x H = H := conjSub_eq_of_mem_normalizer hH
  have h2 : conjSub x K = K := conjSub_eq_of_mem_normalizer hK
  apply mem_normalizer_of_conjSub_eq
  unfold conjSub at h1 h2 ⊢
  rw [Subgroup.map_commutator, h1, h2]

theorem le_normalizer_of_le {B A : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hAB : A ≤ B) : B ≤ Subgroup.normalizer (A : Set G) := fun x hx =>
  mem_normalizer_of_forall_commute fun a ha => hB x hx a (hAB ha)

end Normalizers

section Coprime

variable {G : Type} [Group G] [Finite G]

theorem commutator_sup_centralizer {P Y : Subgroup G} (hP : IsPGroup 2 P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hY : Odd (Nat.card Y)) :
    ⁅Y, P⁆ ⊔ (Y ⊓ Subgroup.centralizer (P : Set G)) = Y :=
  CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 2 Nat.prime_two P Y hP
    hPY (Nat.coprime_two_left.mpr hY)

theorem exists_mul_of_mem {P Y : Subgroup G} (hP : IsPGroup 2 P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hY : Odd (Nat.card Y)) {y : G} (hy : y ∈ Y) :
    ∃ p ∈ ⁅Y, P⁆, ∃ q ∈ Y ⊓ Subgroup.centralizer (P : Set G), p * q = y := by
  have h := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_product 2 Nat.prime_two P
    Y hP hPY (Nat.coprime_two_left.mpr hY)
  have hy' : y ∈ CFSG.SignalizerFunctor.Helpers.subgroupProduct ⁅Y, P⁆
      (Y ⊓ Subgroup.centralizer (P : Set G)) := by
    rw [h]
    exact hy
  obtain ⟨p, hp, q, hq, hpq⟩ := hy'
  exact ⟨p, hp, q, hq, hpq⟩

theorem commutator_commutator_eq {P Y : Subgroup G} (hP : IsPGroup 2 P)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) (hY : Odd (Nat.card Y)) :
    ⁅⁅Y, P⁆, P⁆ = ⁅Y, P⁆ :=
  commutator_commutator_eq_of_isPGroup hP hY hPY

omit [Finite G] in
theorem commutator_le_self {P Y : Subgroup G} (hPY : P ≤ Subgroup.normalizer (Y : Set G)) :
    ⁅Y, P⁆ ≤ Y :=
  CFSG.SignalizerFunctor.Helpers.commutator_le_of_normalizing Y P hPY

omit [Finite G] in
theorem isPGroup_two {A : Subgroup G} (hA : IsElemAbelian 2 A) : IsPGroup 2 A :=
  CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 A hA

end Coprime

section Completion

variable {G : Type} [Group G] [Finite G] {B A : Subgroup G}

theorem exists_ne_one_mem_inf {D : Subgroup G} (hB8 : Nat.card B = 8) (hA : Nat.card A = 4)
    (hD : Nat.card D = 4) (hAB : A ≤ B) (hDB : D ≤ B) : ∃ z ∈ A ⊓ D, z ≠ 1 := by
  have hcard := CFSG.SignalizerFunctor.Helpers.subgroup_product_cardinality A D
  have hsub : CFSG.SignalizerFunctor.Helpers.subgroupProduct A D ⊆ (B : Set G) := by
    rintro _ ⟨a, ha, d, hd, rfl⟩
    exact B.mul_mem (hAB ha) (hDB hd)
  have hAD : Nat.card (CFSG.SignalizerFunctor.Helpers.subgroupProduct A D) ≤ 8 := by
    rw [← hB8, Nat.card_coe_set_eq]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  by_contra hcon
  push Not at hcon
  have hbot : A ⊓ D = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hcon
  rw [hbot, Subgroup.card_bot, hA, hD] at hcard
  omega

omit [Finite G] in
theorem mem_normalizer_uCore {g : G} (hg : ∀ f ∈ A, g * f = f * g) :
    g ∈ Subgroup.normalizer (uCore A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_uCore hg hy, fun hy => ?_⟩
  have hg' : ∀ f ∈ A, g⁻¹ * f = f * g⁻¹ := fun f hf => by
    have := hg f hf
    calc g⁻¹ * f = g⁻¹ * (f * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * f) * g⁻¹ := by rw [this]
      _ = f * g⁻¹ := by group
  have := conj_mem_uCore hg' hy
  simpa [mul_assoc] using this

theorem deltaStarCompletion_le (hB : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B)
    (hW : WeakBalanced B) (hAB : A ≤ B) (hA4 : 4 ≤ Nat.card A) :
    deltaStarCompletion B ≤ uCore A ⊔ centralOddCore B := by
  obtain ⟨hodd, hnorm, hcent, -⟩ := deltaStar_isCompletion hB h8 hW
  have hAel : IsElemAbelian 2 A :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hB hAB
  have hgen := iSup_inf_centralizer_two hAel hA4 (fun x hx => hnorm (hAB hx)) hodd
  rw [← hgen]
  refine iSup₂_le fun b hb => iSup_le fun hb1 => ?_
  rw [hcent b (hAB hb) hb1]
  exact sup_le_sup_right (involutionOddCore_le_uCore hb hb1) _

theorem commutator_involutionOddCore_le_uCore (hB : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B)
    (hW : WeakBalanced B) (hAB : A ≤ B) (hA4 : 4 ≤ Nat.card A) {d : G} (hd : d ∈ B) (hd1 : d ≠ 1) :
    ⁅involutionOddCore d, A⁆ ≤ uCore A := by
  have hle : involutionOddCore d ≤ uCore A ⊔ centralOddCore B :=
    (le_sup_left.trans (deltaStar_le_deltaStarCompletion hd hd1)).trans
      (deltaStarCompletion_le hB h8 hW hAB hA4)
  refine (Subgroup.commutator_mono hle le_rfl).trans ?_
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hAB hx⟩ : B) ⟨y, hAB hy⟩)
  have hT : centralOddCore B ≤ Subgroup.normalizer (uCore A : Set G) := fun t ht =>
    mem_normalizer_uCore fun f hf =>
      (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer B ht) f (hAB hf)).symm
  rw [Subgroup.commutator_le]
  intro h hh a ha
  obtain ⟨u, hu, t, ht, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing _ _ hT h).mp hh
  have hta : t * a = a * t :=
    (Subgroup.mem_centralizer_iff.mp (centralOddCore_le_centralizer B ht) a (hAB ha)).symm
  have hta' : t * a * t⁻¹ = a := by rw [hta]; group
  have e : ⁅u * t, a⁆ = u * (a * u⁻¹ * a⁻¹) := by
    calc ⁅u * t, a⁆ = u * (t * a * t⁻¹) * u⁻¹ * a⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = u * (a * u⁻¹ * a⁻¹) := by rw [hta']; group
  rw [e]
  exact (uCore A).mul_mem hu (conj_mem_uCore (fun f hf => hcomm a ha f hf) ((uCore A).inv_mem hu))

theorem uCore_inf_centralizer_le (hB : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B)
    (hW : WeakBalanced B) (hAB : A ≤ B) :
    uCore A ⊓ Subgroup.centralizer (A : Set G) ≤ centralOddCore A :=
  inf_centralizer_le_centralOddCore (odd_card_iSup_involutionOddCore hB h8 hW hAB) fun _ hg =>
    mem_normalizer_uCore fun f hf => (Subgroup.mem_centralizer_iff.mp hg f hf).symm

theorem commutator_inf_centralizer_le (hB : IsElemAbelian 2 B) (h8 : 8 ≤ Nat.card B)
    (hW : WeakBalanced B) (hAB : A ≤ B) (hA4 : 4 ≤ Nat.card A) {d : G} (hd : d ∈ B) (hd1 : d ≠ 1) :
    ⁅involutionOddCore d, A⁆ ⊓ Subgroup.centralizer (A : Set G) ≤ centralOddCore A :=
  (inf_le_inf_right _ (commutator_involutionOddCore_le_uCore hB h8 hW hAB hA4 hd hd1)).trans
    (uCore_inf_centralizer_le hB h8 hW hAB)

end Completion

end Lemma54Proof

end CFSG.ClassicalInvolution.Asc77

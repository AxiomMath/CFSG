module

public import CFSG.CGT.Foote82.Lemma62Min
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Faithful

variable {P Q : Type*} [Group P] [Group Q]

private def rimg (X : Subgroup P) (r : ↥X →* Q) (A : Subgroup P) : Subgroup Q :=
  (A.subgroupOf X).map r

private theorem mem_rimg {X : Subgroup P} {r : ↥X →* Q} {A : Subgroup P} {x : Q} :
    x ∈ rimg X r A ↔ ∃ a : ↥X, (a : P) ∈ A ∧ r a = x := by
  unfold rimg
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]

private theorem rimg_mono {X : Subgroup P} (r : ↥X →* Q) {A B : Subgroup P} (h : A ≤ B) :
    rimg X r A ≤ rimg X r B :=
  Subgroup.map_mono (Subgroup.comap_mono h)

private theorem rimg_le_range {X : Subgroup P} (r : ↥X →* Q) (A : Subgroup P) :
    rimg X r A ≤ r.range :=
  Subgroup.map_le_range _ _

private theorem subgroupOf_commutator {X A B : Subgroup P} (hA : A ≤ X) (hB : B ≤ X) :
    ⁅A.subgroupOf X, B.subgroupOf X⁆ = ⁅A, B⁆.subgroupOf X := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le_of_le hA hB)]

private theorem rimg_commutator {X : Subgroup P} (r : ↥X →* Q) {A B : Subgroup P} (hA : A ≤ X)
    (hB : B ≤ X) : ⁅rimg X r A, rimg X r B⁆ = rimg X r ⁅A, B⁆ := by
  unfold rimg
  rw [← Subgroup.map_commutator, subgroupOf_commutator hA hB]

private theorem rimg_le_normalizer {X : Subgroup P} (r : ↥X →* Q) {A B : Subgroup P} (hA : A ≤ X)
    (hB : B ≤ X) (h : B ≤ Subgroup.normalizer (A : Set P)) :
    rimg X r B ≤ Subgroup.normalizer (rimg X r A : Set Q) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right] at h ⊢
  rw [rimg_commutator r hB hA]
  exact rimg_mono r h

private theorem card_rimg {X : Subgroup P} (r : ↥X →* Q) {A : Subgroup P} (hA : A ≤ X)
    (hinj : ∀ a : ↥X, (a : P) ∈ A → r a = 1 → a = 1) :
    Nat.card (rimg X r A) = Nat.card A := by
  have h1 : Nat.card ↥(A.subgroupOf X) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  rw [← h1]
  have hbij : Function.Bijective (r.subgroupMap (A.subgroupOf X)) := by
    refine ⟨?_, r.subgroupMap_surjective _⟩
    rw [injective_iff_map_eq_one]
    intro a ha
    have h2 : r (a : ↥X) = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    exact Subtype.ext (hinj a a.2 h2)
  exact (Nat.card_congr (Equiv.ofBijective _ hbij)).symm

private theorem isPGroup_rimg {X : Subgroup P} (r : ↥X →* Q) {A : Subgroup P} {p : ℕ}
    (h : IsPGroup p A) : IsPGroup p (rimg X r A) :=
  (h.comap_of_injective X.subtype X.subtype_injective).map r

private theorem isQuasisimple_native {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

private theorem isQuasisimple_open {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem isQuasisimple_rimg {X : Subgroup P} (r : ↥X →* Q) {A : Subgroup P} (hA : A ≤ X)
    (hq : CFSG.Open.IsQuasisimple ↥A) (hnt : ∃ a : ↥X, (a : P) ∈ A ∧ r a ≠ 1) :
    CFSG.Open.IsQuasisimple ↥(rimg X r A) := by
  have hq' : CFSG.Open.IsQuasisimple ↥(A.subgroupOf X) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hA) hq
  refine isQuasisimple_open (CFSG.LocalCores.isQuasisimple_map (isQuasisimple_native hq') r ?_)
  intro hle
  obtain ⟨a, haA, har⟩ := hnt
  exact har (MonoidHom.mem_ker.1 (hle (Subgroup.mem_subgroupOf.2 haA)))

private theorem commute_or_eq_of_normalized {A N : Subgroup P} (hA : CFSG.Open.IsQuasisimple ↥A)
    (hNA : N ≤ A) (hnorm : ∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) :
    (∀ n ∈ N, ∀ a ∈ A, n * a = a * n) ∨ N = A := by
  have hN : (N.subgroupOf A).Normal := ⟨fun n hn a => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnorm a a.2 n hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hA
    (N.subgroupOf A) with h | h
  · left
    intro n hn a ha
    have hc := h (show (⟨n, hNA hn⟩ : A) ∈ N.subgroupOf A from hn)
    have := (Subgroup.mem_center_iff.mp hc) ⟨a, ha⟩
    exact (congrArg Subtype.val this).symm
  · right
    exact le_antisymm hNA (Subgroup.subgroupOf_eq_top.mp h)

private theorem commutator_kernel_eq_bot {S L K C : Subgroup P}
    (hLq : CFSG.Open.IsQuasisimple ↥L)
    (hSK : S ≤ Subgroup.normalizer (K : Set P)) (hLK : L ≤ Subgroup.normalizer (K : Set P))
    (hLS : ⁅L, S⁆ = ⊥) (hCH : C ≤ S ⊔ L ⊔ K)
    (hHC : S ⊔ L ⊔ K ≤ Subgroup.normalizer (C : Set P))
    (hCK : C ⊓ K = ⊥) (hKL : ⁅K, L⁆ = K) (hKK : ⁅K, K⁆ ≠ K) : ⁅C, L⁆ = ⊥ := by
  have hLH : L ≤ S ⊔ L ⊔ K := le_sup_right.trans le_sup_left
  have hKH : K ≤ S ⊔ L ⊔ K := le_sup_right
  have hHK : S ⊔ L ⊔ K ≤ Subgroup.normalizer (K : Set P) :=
    sup_le (sup_le hSK hLK) Subgroup.le_normalizer
  have hSL : S ≤ Subgroup.normalizer (L : Set P) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right, Subgroup.commutator_comm, hLS]
    exact bot_le
  have hSY : S ≤ Subgroup.normalizer ((L ⊔ K : Subgroup P) : Set P) :=
    (le_inf hSL hSK).trans (Subgroup.inf_normalizer_le_normalizer_sup L K)
  have hHY : S ⊔ L ⊔ K ≤ Subgroup.normalizer ((L ⊔ K : Subgroup P) : Set P) :=
    sup_le (sup_le hSY (le_sup_left.trans Subgroup.le_normalizer))
      (le_sup_right.trans Subgroup.le_normalizer)
  set N : Subgroup P := C ⊓ (L ⊔ K)
  have hLN : L ≤ Subgroup.normalizer (N : Set P) :=
    (le_inf (hLH.trans hHC) (hLH.trans hHY)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hKN : K ≤ Subgroup.normalizer (N : Set P) :=
    (le_inf (hKH.trans hHC) (hKH.trans hHY)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hLM : L ≤ Subgroup.normalizer ((N ⊔ K : Subgroup P) : Set P) :=
    (le_inf hLN hLK).trans (Subgroup.inf_normalizer_le_normalizer_sup N K)
  have hCKc : ⁅C, K⁆ = ⊥ := by
    have h : ⁅C, K⁆ ≤ C ⊓ K := by
      refine le_inf ?_ ?_
      · rw [Subgroup.commutator_comm]
        exact Subgroup.le_normalizer_iff_commutator_le_right.1 (hKH.trans hHC)
      · exact Subgroup.le_normalizer_iff_commutator_le_right.1 (hCH.trans hHK)
    rw [hCK] at h
    exact le_bot_iff.1 h
  have hNK : ⁅N, K⁆ = ⊥ :=
    le_bot_iff.1 (hCKc ▸ Subgroup.commutator_mono inf_le_left le_rfl)
  have hNc : ∀ n ∈ N, ∀ k ∈ K, k * n = n * k := fun n hn =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hNK hn)
  have hNL : ⁅N, L⁆ = ⊥ := by
    have hnorm : ∀ a ∈ L, ∀ n ∈ L ⊓ (N ⊔ K), a * n * a⁻¹ ∈ L ⊓ (N ⊔ K) := fun a ha n hn =>
      ⟨L.mul_mem (L.mul_mem ha hn.1) (L.inv_mem ha),
        (Subgroup.le_normalizer_iff.1 hLM) a ha n hn.2⟩
    rcases commute_or_eq_of_normalized hLq inf_le_left hnorm with hcomm | heq
    · refine le_bot_iff.1 (Subgroup.commutator_le.2 fun n hn l hl => ?_)
      have hnY : n ∈ ((L ⊔ K : Subgroup P) : Set P) := hn.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right L K hLK] at hnY
      obtain ⟨l₁, hl₁, k₁, hk₁, hnk⟩ := Set.mem_mul.1 hnY
      subst hnk
      have hl₁M : l₁ ∈ N ⊔ K := by
        have : l₁ = (l₁ * k₁) * k₁⁻¹ := by group
        rw [this]
        exact (N ⊔ K).mul_mem (Subgroup.mem_sup_left hn)
          ((N ⊔ K).inv_mem (Subgroup.mem_sup_right hk₁))
      have hcomm1 : l₁ * l = l * l₁ := hcomm l₁ ⟨hl₁, hl₁M⟩ l hl
      have hkl : ⁅k₁, l⁆ ∈ K :=
        (Subgroup.le_normalizer_iff_commutator_le_left.1 hLK)
          (Subgroup.commutator_mem_commutator hk₁ hl)
      have h1 : ⁅l₁ * k₁, l⁆ = l₁ * ⁅k₁, l⁆ * l₁⁻¹ := by
        rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_eq_one_iff_mul_comm.2 hcomm1,
          mul_one]
      have hK1 : ⁅l₁ * k₁, l⁆ ∈ K := by
        rw [h1]
        exact (Subgroup.le_normalizer_iff.1 hLK) l₁ hl₁ _ hkl
      have hN1 : ⁅l₁ * k₁, l⁆ ∈ N := by
        have e : ⁅l₁ * k₁, l⁆ = (l₁ * k₁) * (l * (l₁ * k₁)⁻¹ * l⁻¹) := by
          simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact N.mul_mem hn ((Subgroup.le_normalizer_iff.1 hLN) l hl _ (N.inv_mem hn))
      have h2 : ⁅l₁ * k₁, l⁆ ∈ C ⊓ K := ⟨hN1.1, hK1⟩
      rw [hCK] at h2
      exact h2
    · exfalso
      have hLM' : L ≤ N ⊔ K := inf_eq_left.1 heq
      have hle : ⁅K, L⁆ ≤ ⁅K, K⁆ := by
        refine Subgroup.commutator_le.2 fun k hk l hl => ?_
        have hlM : l ∈ ((N ⊔ K : Subgroup P) : Set P) := hLM' hl
        rw [Subgroup.coe_mul_of_right_le_normalizer_left N K hKN] at hlM
        obtain ⟨n, hn, k₀, hk₀, hnk⟩ := Set.mem_mul.1 hlM
        subst hnk
        have hkk₀ : ⁅k, k₀⁆ ∈ K :=
          (Subgroup.commutator_le_of_le (le_refl K) (le_refl K))
            (Subgroup.commutator_mem_commutator hk hk₀)
        have h1 : ⁅k, n * k₀⁆ = ⁅k, k₀⁆ := by
          rw [commutatorElement_mul_right_eq_mul_conj,
            commutatorElement_eq_one_iff_mul_comm.2 (hNc n hn k hk), one_mul,
            ← hNc n hn _ hkk₀, mul_assoc, mul_inv_cancel, mul_one]
        rw [h1]
        exact Subgroup.commutator_mem_commutator hk hk₀
      rw [hKL] at hle
      exact hKK (le_antisymm (Subgroup.commutator_le_of_le (le_refl K) (le_refl K)) hle)
  have hCLN : ⁅C, L⁆ ≤ N := by
    refine le_inf ?_ ?_
    · rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.1 (hLH.trans hHC)
    · exact (Subgroup.commutator_mono le_rfl (le_sup_left : L ≤ L ⊔ K)).trans
        (Subgroup.le_normalizer_iff_commutator_le_right.1 (hCH.trans hHY))
  have hLCN : ⁅L, C⁆ ≤ N := by
    rw [Subgroup.commutator_comm]
    exact hCLN
  have h1 : ⁅⁅L, C⁆, L⁆ = ⊥ := le_bot_iff.1 (hNL ▸ Subgroup.commutator_mono hLCN le_rfl)
  have h2 : ⁅⁅C, L⁆, L⁆ = ⊥ := le_bot_iff.1 (hNL ▸ Subgroup.commutator_mono hCLN le_rfl)
  have h3 : ⁅⁅L, L⁆, C⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hLq.1)
  rw [hperf] at h3
  rw [Subgroup.commutator_comm]
  exact h3

section Subnormal

variable {X' Q' : Type*} [Group X'] [Group Q']

private theorem isSubnormal_map_centralizer (r : X' →* Q') {S L : Subgroup X'} (hLS : ⁅L, S⁆ = ⊥)
    (hLC : ⁅L, r.ker⁆ = ⊥) (hsub : IsSubnormal L (Subgroup.centralizer (S : Set X'))) :
    IsSubnormal (L.map r) (r.range ⊓ Subgroup.centralizer (S.map r : Set Q')) := by
  set Z : Subgroup X' :=
    Subgroup.centralizer (S : Set X') ⊓ Subgroup.centralizer (r.ker : Set X')
  set Pr : Subgroup X' := (Subgroup.centralizer (S.map r : Set Q')).comap r with hPr
  have hLZ : L ≤ Z := le_inf (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hLS)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hLC)
  have hZPr : Z ≤ Pr := by
    intro z hz
    rw [hPr, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hz.1 s hs]
  have hnormal : (Z.subgroupOf Pr).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZPr]
    intro z p hz hp
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨t, ht⟩ : ∃ t, t = p⁻¹ * s * p := ⟨_, rfl⟩
      have hrs : r s * r p = r p * r s :=
        Subgroup.mem_centralizer_iff.1 hp (r s) ⟨s, hs, rfl⟩
      have hc : s⁻¹ * t ∈ r.ker := by
        rw [MonoidHom.mem_ker, ht]
        have h1 : (r p)⁻¹ * r s * r p = r s := by
          rw [mul_assoc, hrs, inv_mul_cancel_left]
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, inv_mul_cancel]
      have hzc : (s⁻¹ * t) * z = z * (s⁻¹ * t) := Subgroup.mem_centralizer_iff.1 hz.2 _ hc
      have hzs : s * z = z * s := Subgroup.mem_centralizer_iff.1 hz.1 s hs
      have hzt : z * t = t * z := by
        obtain ⟨c, hcdef⟩ : ∃ c, c = s⁻¹ * t := ⟨_, rfl⟩
        have e : t = s * c := by rw [hcdef]; group
        rw [← hcdef] at hzc
        calc z * t = z * (s * c) := by rw [← e]
          _ = (z * s) * c := by rw [mul_assoc]
          _ = (s * z) * c := by rw [hzs]
          _ = s * (z * c) := by rw [mul_assoc]
          _ = s * (c * z) := by rw [hzc]
          _ = (s * c) * z := by rw [mul_assoc]
          _ = t * z := by rw [← e]
      have hs_eq : s = p * t * p⁻¹ := by rw [ht]; group
      calc s * (p * z * p⁻¹) = (p * t * p⁻¹) * (p * z * p⁻¹) := by rw [← hs_eq]
        _ = p * (t * z) * p⁻¹ := by group
        _ = p * (z * t) * p⁻¹ := by rw [hzt]
        _ = (p * z * p⁻¹) * (p * t * p⁻¹) := by group
        _ = (p * z * p⁻¹) * s := by rw [← hs_eq]
    · rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨c', hc'⟩ : ∃ c', c' = p⁻¹ * c * p := ⟨_, rfl⟩
      have hc'k : c' ∈ r.ker := by
        rw [MonoidHom.mem_ker, hc', map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hc]
        simp
      have hzc : c' * z = z * c' := Subgroup.mem_centralizer_iff.1 hz.2 _ hc'k
      have hc_eq : c = p * c' * p⁻¹ := by rw [hc']; group
      calc c * (p * z * p⁻¹) = (p * c' * p⁻¹) * (p * z * p⁻¹) := by rw [← hc_eq]
        _ = p * (c' * z) * p⁻¹ := by group
        _ = p * (z * c') * p⁻¹ := by rw [hzc]
        _ = (p * z * p⁻¹) * (p * c' * p⁻¹) := by group
        _ = (p * z * p⁻¹) * c := by rw [← hc_eq]
  have hLZsub : IsSubnormal L Z := by
    have h := hsub.inf_of_le (inf_le_left : Z ≤ Subgroup.centralizer (S : Set X'))
    rwa [inf_eq_left.2 hLZ] at h
  have h1 : IsSubnormal L Pr := hLZsub.trans (IsSubnormal.step hZPr hnormal (IsSubnormal.refl Pr))
  have h2 := h1.map r
  rwa [hPr, Subgroup.map_comap_eq] at h2

end Subnormal

section Rimg

variable {X : Subgroup P} (r : ↥X →* Q)

private theorem rimg_bot : rimg X r ⊥ = ⊥ := by
  unfold rimg
  rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]

private theorem rimg_isSubnormal_centralizer {S L : Subgroup P}
    (hSX : S ≤ X) (hLX : L ≤ X) (hLS : ⁅L, S⁆ = ⊥)
    (hLC : ⁅L, r.ker.map X.subtype⁆ = ⊥)
    (hsub : IsSubnormal L (Subgroup.centralizer (S : Set P) ⊓ X)) :
    IsSubnormal (rimg X r L) (r.range ⊓ Subgroup.centralizer (rimg X r S : Set Q)) := by
  have hLS' : ⁅L.subgroupOf X, S.subgroupOf X⁆ = ⊥ := by
    rw [subgroupOf_commutator hLX hSX, hLS, Subgroup.bot_subgroupOf]
  have hLC' : ⁅L.subgroupOf X, r.ker⁆ = ⊥ := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLX, hLC, Subgroup.map_bot]
  have hsub' : IsSubnormal (L.subgroupOf X)
      (Subgroup.centralizer (S.subgroupOf X : Set ↥X)) := by
    have h := IsSubnormal.comap X.subtype hsub
    have e : (Subgroup.centralizer (S : Set P) ⊓ X).comap X.subtype =
        Subgroup.centralizer (S.subgroupOf X : Set ↥X) := by
      ext x
      simp only [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
        SetLike.mem_coe, Subgroup.subtype_apply, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨hx, -⟩ y hy
        exact Subtype.ext (hx y hy)
      · intro hx
        refine ⟨fun s hs => ?_, x.2⟩
        exact congrArg Subtype.val (hx ⟨s, hSX hs⟩ hs)
    rwa [e] at h
  exact isSubnormal_map_centralizer r hLS' hLC' hsub'

private theorem rimg_min {S L K : Subgroup P} (hSX : S ≤ X) (hLX : L ≤ X)
    (hSK : S ≤ Subgroup.normalizer (K : Set P)) (hLK : L ≤ Subgroup.normalizer (K : Set P))
    (hmin : ∀ K' : Subgroup P, K' < K → S ≤ Subgroup.normalizer (K' : Set P) →
      L ≤ Subgroup.normalizer (K' : Set P) → ⁅K', L⁆ = ⊥) :
    ∀ K₀ : Subgroup Q, K₀ < rimg X r K → rimg X r S ≤ Subgroup.normalizer (K₀ : Set Q) →
      rimg X r L ≤ Subgroup.normalizer (K₀ : Set Q) → ⁅K₀, rimg X r L⁆ = ⊥ := by
  intro K₀ hlt hS₀ hL₀
  set K' : Subgroup P := (K.subgroupOf X ⊓ K₀.comap r).map X.subtype
  have hK'X : K' ≤ X := Subgroup.map_subtype_le _
  have hK'K : K' ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hmemK' : ∀ x : ↥X, (x : P) ∈ K' ↔ (x : P) ∈ K ∧ r x ∈ K₀ := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact hy
    · rintro hx
      exact ⟨x, hx, rfl⟩
  have hrimgK' : rimg X r K' = K₀ := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, haK', rfl⟩ := mem_rimg.1 hy
      exact ((hmemK' a).1 haK').2
    · intro hy
      obtain ⟨a, haK, rfl⟩ := mem_rimg.1 (hlt.le hy)
      exact mem_rimg.2 ⟨a, (hmemK' a).2 ⟨haK, hy⟩, rfl⟩
  have hK'lt : K' < K := by
    refine lt_of_le_of_ne hK'K fun h => hlt.ne ?_
    rw [← hrimgK', h]
  have hconj : ∀ T : Subgroup P, T ≤ X → T ≤ Subgroup.normalizer (K : Set P) →
      rimg X r T ≤ Subgroup.normalizer (K₀ : Set Q) → T ≤ Subgroup.normalizer (K' : Set P) := by
    intro T hTX hTK hTK₀
    rw [Subgroup.le_normalizer_iff]
    intro t ht k hk
    have hkX : k ∈ X := hK'X hk
    have hk' := (hmemK' ⟨k, hkX⟩).1 hk
    have htX : t ∈ X := hTX ht
    have hcon : (⟨t, htX⟩ * ⟨k, hkX⟩ * ⟨t, htX⟩⁻¹ : ↥X) =
        ⟨t * k * t⁻¹, X.mul_mem (X.mul_mem htX hkX) (X.inv_mem htX)⟩ := rfl
    have hrt : r ⟨t, htX⟩ ∈ rimg X r T := mem_rimg.2 ⟨⟨t, htX⟩, ht, rfl⟩
    have := (hmemK' (⟨t, htX⟩ * ⟨k, hkX⟩ * ⟨t, htX⟩⁻¹)).2 ⟨by
      rw [hcon]
      exact (Subgroup.le_normalizer_iff.1 hTK) t ht k hk'.1, by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.le_normalizer_iff.1 hTK₀) (r ⟨t, htX⟩) hrt _ hk'.2⟩
    rw [hcon] at this
    exact this
  have hSK' := hconj S hSX hSK hS₀
  have hLK' := hconj L hLX hLK hL₀
  have hK'L : ⁅K', L⁆ = ⊥ := hmin K' hK'lt hSK' hLK'
  rw [← hrimgK', rimg_commutator r hK'X hLX, hK'L, rimg_bot]

end Rimg

section Linear

variable {S L K : Subgroup (GLV V)}

private theorem invariant_hgen (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) :
    Invariant (S ⊔ L ⊔ K) (commSpace K ⊤) := by
  have hHK : S ⊔ L ⊔ K ≤ Subgroup.normalizer (K : Set (GLV V)) :=
    sup_le (sup_le hSK hLK) Subgroup.le_normalizer
  exact invariant_commSpace (Subgroup.le_normalizer_iff.1 hHK) (invariant_top _)

private noncomputable def resK (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) :
    ↥(S ⊔ L ⊔ K) →* GLV ↥(commSpace K ⊤) :=
  restrictHom (S ⊔ L ⊔ K) (commSpace K ⊤) (invariant_hgen hSK hLK)

private noncomputable abbrev imgK (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) (A : Subgroup (GLV V)) :
    Subgroup (GLV ↥(commSpace K ⊤)) :=
  rimg (S ⊔ L ⊔ K) (resK hSK hLK) A

private theorem map_ker_resK (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) :
    (resK hSK hLK).ker.map (S ⊔ L ⊔ K).subtype =
      centralizerOn (S ⊔ L ⊔ K) (commSpace K ⊤) := by
  ext x
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.2, fun w hw => restrictHom_eq_one_iff.1 (MonoidHom.mem_ker.1 hh) w hw⟩
  · rintro ⟨hxH, hxW⟩
    exact ⟨⟨x, hxH⟩, MonoidHom.mem_ker.2 (restrictHom_eq_one_iff.2 hxW), rfl⟩

private theorem le_normalizer_centralizerOn {H : Subgroup (GLV V)} {W : Submodule (ZMod 2) V}
    (hW : Invariant H W) : H ≤ Subgroup.normalizer (centralizerOn H W : Set (GLV V)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro h hh c ⟨hcH, hcW⟩
  refine ⟨H.mul_mem (H.mul_mem hh hcH) (H.inv_mem hh), fun w hw => ?_⟩
  have hw' : (h⁻¹ : GLV V) w ∈ W := hW h⁻¹ (H.inv_mem hh) w hw
  show h (c (h⁻¹ w)) = w
  rw [hcW _ hw']
  simp

private theorem inf_centralizerOn_eq_bot {H K : Subgroup (GLV V)}
    (hc : IsCompl (fixedSpace K) (commSpace K ⊤)) :
    centralizerOn H (commSpace K ⊤) ⊓ K = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro k ⟨⟨-, hkW⟩, hkK⟩
  ext v
  have hv : v ∈ fixedSpace K ⊔ commSpace K ⊤ := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, hc', w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  show k (c + w) = c + w
  rw [map_add, hc' k hkK, hkW w hw]

private theorem resK_injOn (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hc : IsCompl (fixedSpace K) (commSpace K ⊤)) :
    ∀ k : ↥(S ⊔ L ⊔ K), (k : GLV V) ∈ K → resK hSK hLK k = 1 → k = 1 := by
  intro k hkK hk1
  have hkC : (k : GLV V) ∈ centralizerOn (S ⊔ L ⊔ K) (commSpace K ⊤) := by
    rw [← map_ker_resK hSK hLK]
    exact ⟨k, MonoidHom.mem_ker.2 hk1, rfl⟩
  have h : (k : GLV V) ∈ centralizerOn (S ⊔ L ⊔ K) (commSpace K ⊤) ⊓ K := ⟨hkC, hkK⟩
  rw [inf_centralizerOn_eq_bot hc] at h
  exact Subtype.ext (Subgroup.mem_bot.1 h)

private theorem fixedSpace_imgK (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) {A : Subgroup (GLV V)}
    (hAH : A ≤ S ⊔ L ⊔ K) :
    fixedSpace (imgK hSK hLK A) = (fixedSpace A).comap (commSpace K ⊤).subtype := by
  ext w
  constructor
  · intro hw a ha
    have := hw (resK hSK hLK ⟨a, hAH ha⟩) (mem_rimg.2 ⟨⟨a, hAH ha⟩, ha, rfl⟩)
    exact congrArg Subtype.val this
  · intro hw x hx
    obtain ⟨a, haA, rfl⟩ := mem_rimg.1 hx
    exact Subtype.ext (hw a haA)

private theorem map_commSpace_imgK (hSK : S ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V))) {A : Subgroup (GLV V)}
    (hAH : A ≤ S ⊔ L ⊔ K) :
    (commSpace (imgK hSK hLK A) ⊤).map (commSpace K ⊤).subtype =
      commSpace A (commSpace K ⊤) := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine commSpace_le_iff.2 fun x hx w _ => ?_
    obtain ⟨a, haA, rfl⟩ := mem_rimg.1 hx
    exact sub_mem_commSpace haA w.2
  · refine commSpace_le_iff.2 fun a ha w hw => ?_
    exact ⟨resK hSK hLK ⟨a, hAH ha⟩ ⟨w, hw⟩ - ⟨w, hw⟩,
      sub_mem_commSpace (mem_rimg.2 ⟨⟨a, hAH ha⟩, ha, rfl⟩) Submodule.mem_top, rfl⟩

private theorem commSpace_top_eq {L K : Subgroup (GLV V)}
    (hfix : ∀ l ∈ L, ∀ v ∈ fixedSpace K, l v = v)
    (hc : IsCompl (fixedSpace K) (commSpace K ⊤)) :
    commSpace L ⊤ = commSpace L (commSpace K ⊤) := by
  refine le_antisymm (commSpace_le_iff.2 fun l hl v _ => ?_) (commSpace_mono le_rfl le_top)
  have hv : v ∈ fixedSpace K ⊔ commSpace K ⊤ := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨c, hc', w, hw, rfl⟩ := Submodule.mem_sup.1 hv
  have h : l (c + w) - (c + w) = l w - w := by
    rw [map_add, hfix l hl c hc']
    abel
  rw [h]
  exact sub_mem_commSpace hl hw

private theorem irrSec_comap_subtype {W : Submodule (ZMod 2) V} {L : Subgroup (GLV V)}
    {L₀ : Subgroup (GLV ↥W)}
    (hcompat : ∀ l ∈ L, ∃ l₀ ∈ L₀, ∀ w : ↥W, (l₀ w : V) = l (w : V))
    {C U : Submodule (ZMod 2) V} (hCW : C ≤ W) (hUW : U ≤ W) (h : IrrSec L C U) :
    IrrSec L₀ (C.comap W.subtype) (U.comap W.subtype) := by
  obtain ⟨hCU, hmin⟩ := h
  refine ⟨?_, fun J₀ hJ₀ hCJ hJU => ?_⟩
  · refine lt_of_le_of_ne (Submodule.comap_mono hCU.le) fun heq => ?_
    obtain ⟨x, hxU, hxC⟩ := SetLike.exists_of_lt hCU
    have hx : (⟨x, hUW hxU⟩ : ↥W) ∈ U.comap W.subtype := hxU
    rw [← heq] at hx
    exact hxC hx
  · have hinv : Invariant L (J₀.map W.subtype) := by
      rintro l hl _ ⟨y, hy, rfl⟩
      obtain ⟨l₀, hl₀, hl₀eq⟩ := hcompat l hl
      exact ⟨l₀ y, hJ₀ l₀ hl₀ y hy, hl₀eq y⟩
    have hCJ' : C ≤ J₀.map W.subtype := fun x hx => ⟨⟨x, hCW hx⟩, hCJ hx, rfl⟩
    have hJU' : J₀.map W.subtype ≤ U := by
      rintro _ ⟨y, hy, rfl⟩
      exact hJU hy
    have hinj : Function.Injective W.subtype := W.injective_subtype
    rcases hmin _ hinv hCJ' hJU' with h | h
    · left
      have h' := congrArg (Submodule.comap W.subtype) h
      rwa [Submodule.comap_map_eq_of_injective hinj] at h'
    · right
      have h' := congrArg (Submodule.comap W.subtype) h
      rwa [Submodule.comap_map_eq_of_injective hinj] at h'

private theorem commSpace_top_le {L K : Subgroup (GLV V)}
    (hLK : L ≤ Subgroup.normalizer (K : Set (GLV V)))
    (hfix : ∀ l ∈ L, ∀ v ∈ fixedSpace K, l v = v)
    (hc : IsCompl (fixedSpace K) (commSpace K ⊤)) : commSpace L ⊤ ≤ commSpace K ⊤ :=
  (commSpace_top_eq hfix hc).le.trans (commSpace_le_of_invariant
    (invariant_commSpace (Subgroup.le_normalizer_iff.1 hLK) (invariant_top L)))

private theorem hasIrrTildeV_imgK {G : Subgroup (GLV V)} (hc : Conf62 G S L K)
    (hne : ⁅K, L⁆ ≠ ⊥) : HasIrrTildeV (imgK hc.S_le hc.L_le L) := by
  have hSK := hc.S_le
  have hLK := hc.L_le
  have hLH : L ≤ S ⊔ L ⊔ K := le_sup_right.trans le_sup_left
  have hcompl := isCompl_fixedSpace_commSpace hc.odd
  have hfix := hc.fixes_fixedSpace hne
  have hcomm := commSpace_top_eq hfix hcompl
  have hUW : commSpace L ⊤ ≤ commSpace K ⊤ := commSpace_top_le hLK hfix hcompl
  have hCW : tildeVBot L ≤ commSpace K ⊤ := inf_le_right.trans hUW
  have e1 := fixedSpace_imgK hSK hLK hLH
  have e2 : commSpace (imgK hSK hLK L) ⊤ = (commSpace L ⊤).comap (commSpace K ⊤).subtype := by
    have h := map_commSpace_imgK hSK hLK hLH
    rw [← hcomm] at h
    rw [← h, Submodule.comap_map_eq_of_injective (commSpace K ⊤).injective_subtype]
  have h : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hc.setup.irrTilde
  show IrrSec (imgK hSK hLK L) (fixedSpace (imgK hSK hLK L) ⊓ commSpace (imgK hSK hLK L) ⊤)
    (commSpace (imgK hSK hLK L) ⊤)
  rw [e1, e2, ← Submodule.comap_inf]
  exact irrSec_comap_subtype
    (fun l hl => ⟨_, mem_rimg.2 ⟨⟨l, hLH hl⟩, hl, rfl⟩, fun w => rfl⟩) hCW hUW h

end Linear

end Faithful

open Faithful in
theorem Conf62.reduce {G S L K : Subgroup (GLV V)} (hc : Conf62 G S L K) (hmin : Min62 S L K)
    (hne : ⁅K, L⁆ ≠ ⊥) :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module (ZMod 2) V₀) (_ : Finite V₀)
      (G₀ S₀ L₀ K₀ : Subgroup (GLV V₀)), Conf62 G₀ S₀ L₀ K₀ ∧ Min62 S₀ L₀ K₀ ∧
        ⁅K₀, L₀⁆ ≠ ⊥ ∧ Nat.card K₀ = Nat.card K ∧ fixedSpace K₀ = ⊥ := by
  obtain ⟨hKL, ⟨p, hp, -, hKp⟩, -, -⟩ := hc.min_structure hmin hne
  have hSK := hc.S_le
  have hLK := hc.L_le
  have hcompl := isCompl_fixedSpace_commSpace hc.odd
  have hLG : L ≤ G ⊓ Subgroup.centralizer (S : Set (GLV V)) := hc.setup.component.1
  have hSH : S ≤ S ⊔ L ⊔ K := le_sup_left.trans le_sup_left
  have hLH : L ≤ S ⊔ L ⊔ K := le_sup_right.trans le_sup_left
  have hKH : K ≤ S ⊔ L ⊔ K := le_sup_right
  have hHG : S ⊔ L ⊔ K ≤ G := sup_le (sup_le hc.setup.S_le (hLG.trans inf_le_left)) hc.K_le
  have hLS : ⁅L, S⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hLG.trans inf_le_right)
  have hKK : ⁅K, K⁆ ≠ K := by
    haveI := Fact.mk hp
    have hKbot : K ≠ ⊥ := fun h => hne (by rw [h, Subgroup.commutator_bot_left])
    exact (lt_of_le_of_lt (commutator_le_frat hKp) (frat_lt hKp hKbot)).ne
  have hCL : ⁅centralizerOn (S ⊔ L ⊔ K) (commSpace K ⊤), L⁆ = ⊥ :=
    commutator_kernel_eq_bot hc.setup.component.2.2 hSK hLK hLS (fun x hx => hx.1)
      (le_normalizer_centralizerOn (invariant_hgen hSK hLK)) (inf_centralizerOn_eq_bot hcompl)
      hKL hKK
  have hLC : ⁅L, (resK hSK hLK).ker.map (S ⊔ L ⊔ K).subtype⁆ = ⊥ := by
    rw [map_ker_resK hSK hLK, Subgroup.commutator_comm]
    exact hCL
  have hcard : Nat.card (imgK hSK hLK K) = Nat.card K :=
    card_rimg _ hKH (resK_injOn hSK hLK hcompl)
  have hsub' : IsSubnormal L (Subgroup.centralizer (S : Set (GLV V)) ⊓ (S ⊔ L ⊔ K)) := by
    have h := hc.setup.component.2.1.inf (S ⊔ L ⊔ K)
    have e : G ⊓ Subgroup.centralizer (S : Set (GLV V)) ⊓ (S ⊔ L ⊔ K) =
        Subgroup.centralizer (S : Set (GLV V)) ⊓ (S ⊔ L ⊔ K) := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hHG h.2, h.1⟩, h.2⟩⟩
    rwa [inf_eq_left.2 hLH, e] at h
  have hnt : ∃ a : ↥(S ⊔ L ⊔ K), (a : GLV V) ∈ L ∧ resK hSK hLK a ≠ 1 := by
    obtain ⟨x, hxU, hxC⟩ := SetLike.exists_of_lt hc.setup.irrTilde.1
    have hxfix : x ∉ fixedSpace L := fun hf => hxC ⟨hf, hxU⟩
    simp only [mem_fixedSpace_iff, not_forall] at hxfix
    obtain ⟨l, hl, hlx⟩ := hxfix
    have hxW : x ∈ commSpace K ⊤ := commSpace_top_le hLK (hc.fixes_fixedSpace hne) hcompl hxU
    refine ⟨⟨l, hLH hl⟩, hl, fun h1 => hlx ?_⟩
    exact restrictHom_eq_one_iff.1 h1 x hxW
  have hcomp : IsComponentOf (imgK hSK hLK L)
      ((resK hSK hLK).range ⊓ Subgroup.centralizer (imgK hSK hLK S : Set (GLV ↥(commSpace K ⊤)))) :=
    ⟨le_inf (rimg_le_range _ _) (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (by rw [rimg_commutator _ hLH hSH, hLS, rimg_bot])),
      rimg_isSubnormal_centralizer _ hSH hLH hLS hLC hsub',
      isQuasisimple_rimg _ hLH hc.setup.component.2.2 hnt⟩
  have hodd : Odd (Nat.card (imgK hSK hLK K)) := by
    rw [hcard]
    exact hc.odd
  have hne' : ⁅imgK hSK hLK K, imgK hSK hLK L⁆ ≠ ⊥ := by
    intro h
    rw [rimg_commutator _ hKH hLH] at h
    refine hne ((Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_)
    have hxK : x ∈ K := (Subgroup.le_normalizer_iff_commutator_le_left.1 hLK) hx
    have hxH : x ∈ S ⊔ L ⊔ K := hKH hxK
    have hmem : resK hSK hLK ⟨x, hxH⟩ ∈ rimg (S ⊔ L ⊔ K) (resK hSK hLK) ⁅K, L⁆ :=
      mem_rimg.2 ⟨⟨x, hxH⟩, hx, rfl⟩
    rw [h] at hmem
    exact congrArg Subtype.val (resK_injOn hSK hLK hcompl ⟨x, hxH⟩ hxK (Subgroup.mem_bot.1 hmem))
  have hfix₀ : fixedSpace (imgK hSK hLK K) = ⊥ := by
    rw [fixedSpace_imgK hSK hLK hKH, eq_bot_iff]
    intro w hw
    have hw1 : (w : V) ∈ fixedSpace K ⊓ commSpace K ⊤ := ⟨hw, w.2⟩
    rw [hcompl.inf_eq_bot] at hw1
    exact (Submodule.mem_bot _).2 (Subtype.ext ((Submodule.mem_bot _).1 hw1))
  exact ⟨↥(commSpace K ⊤), inferInstance, inferInstance, inferInstance, (resK hSK hLK).range,
    imgK hSK hLK S, imgK hSK hLK L, imgK hSK hLK K,
    ⟨⟨rimg_le_range _ _, isPGroup_rimg _ hc.setup.isPGroup, hcomp,
        hasIrrTildeV_imgK hc hne⟩, rimg_le_range _ _, hodd,
      rimg_le_normalizer _ hKH hSH hSK, rimg_le_normalizer _ hKH hLH hLK⟩,
    rimg_min _ hSH hLH hSK hLK hmin, hne', hcard, hfix₀⟩

end CFSG.CGT.Foote82

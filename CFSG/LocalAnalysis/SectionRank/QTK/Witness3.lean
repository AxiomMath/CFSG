module

public import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.LocalAnalysis.SectionRank.OrderThreeCenter
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartTwo.Census (le_localRank_of_le_normalizer)

theorem exists_isElemAbelian_of_witness {G Q : Type*} [Group G] [Group Q] (π : G →* Q)
    (hπ : π.ker ≤ Subgroup.center G) {n : ℕ} (Z A : Fin n → G) (h3 : ∀ i, Z i ^ 3 = 1)
    (h1 : ∀ i, ¬ Commute (Z i) (A i)) (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i))
    (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i)) (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) :
    ∃ E : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ n ∧
      E ≤ (Subgroup.closure (Set.range Z)).map π := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : ∀ i, ∀ g ∈ Subgroup.zpowers (Z i), Commute g (A i) → g = 1 := by
    intro i g hg hc
    rcases CFSG.SectionRank.eq_one_or_of_mem_zpowers_three (h3 i) hg with h | h | h
    · exact h
    · exact absurd (h ▸ hc) (h1 i)
    · exact absurd (h ▸ hc) (h2 i)
  have hcent : ∀ i j, i ≠ j → Subgroup.zpowers (Z j) ≤ Subgroup.centralizer {A i} := by
    intro i j hij
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (hZA i j hij).eq.symm
  have hker : ∀ i, ∀ g : G, π g = 1 → Commute g (A i) := fun i g hg =>
    (Subgroup.mem_center_iff.1 (hπ (MonoidHom.mem_ker.2 hg)) (A i)).symm
  let ϕ : ∀ i, Subgroup.zpowers (Z i) →* Q := fun i => π.comp (Subgroup.zpowers (Z i)).subtype
  have hϕcomm : Pairwise fun i j => ∀ (x : Subgroup.zpowers (Z i)) (y : Subgroup.zpowers (Z j)),
      Commute (ϕ i x) (ϕ j y) := by
    intro i j hij x y
    obtain ⟨a, ha⟩ := x.2
    obtain ⟨b, hb⟩ := y.2
    change Commute (π (x : G)) (π (y : G))
    rw [← ha, ← hb]
    exact ((hZZ i j hij).zpow_zpow a b).map π
  have hϕinj : ∀ i, Function.Injective (ϕ i) := by
    intro i
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    exact (Subgroup.mem_bot).2 (Subtype.ext (key i _ x.2 (hker i _ hx)))
  have hind : iSupIndep fun i => (ϕ i).range := by
    intro i
    rw [disjoint_iff, eq_bot_iff]
    rintro g ⟨⟨x, rfl⟩, hg⟩
    have hle : (⨆ (j : Fin n) (_ : j ≠ i), (ϕ j).range) ≤
        (Subgroup.centralizer {A i}).map π := by
      refine iSup₂_le fun j hj => ?_
      rintro _ ⟨y, rfl⟩
      exact ⟨y, hcent i j (Ne.symm hj) y.2, rfl⟩
    obtain ⟨r, hr, hrx⟩ := hle hg
    change π r = π (x : G) at hrx
    have hc : Commute (x : G) (A i) := by
      have hxr : (x : G) = r * (r⁻¹ * x) := by group
      rw [hxr]
      have hrc : Commute r (A i) := (Subgroup.mem_centralizer_iff.1 hr (A i) rfl).symm
      exact hrc.mul_left (hker i _ (by rw [map_mul, map_inv, hrx, inv_mul_cancel]))
    have hx1 : x = 1 := Subtype.ext (key i _ x.2 hc)
    change ϕ i x ∈ (⊥ : Subgroup Q)
    rw [hx1, map_one]
    exact one_mem _
  have hord : ∀ i, Nat.card (Subgroup.zpowers (Z i)) = 3 := fun i => by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (h3 i) fun h => (h1 i) (h ▸ Commute.one_left _)
  set Φ := MonoidHom.noncommPiCoprod ϕ hϕcomm
  have hΦ : Function.Injective Φ :=
    MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ (hcomm := hϕcomm) hind hϕinj
  have hcomm : ∀ a b : (∀ i, Subgroup.zpowers (Z i)), a * b = b * a := by
    intro a b
    funext i
    obtain ⟨x, hx⟩ := (a i).2
    obtain ⟨y, hy⟩ := (b i).2
    exact Subtype.ext (by
      change (a i : G) * (b i : G) = (b i : G) * (a i : G)
      rw [← hx, ← hy]
      exact (Commute.zpow_zpow_self _ _ _).eq)
  have hpow : ∀ a : (∀ i, Subgroup.zpowers (Z i)), a ^ 3 = 1 := by
    intro a
    funext i
    apply Subtype.ext
    change ((a i : G)) ^ 3 = 1
    obtain ⟨x, hx⟩ := (a i).2
    rw [← hx, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h3 i,
      _root_.one_zpow]
  refine ⟨Φ.range, ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : Q) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_pi,
      Finset.prod_congr rfl fun i _ => hord i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun i => ?_
    rintro _ ⟨x, rfl⟩
    have hZi : Z i ∈ Subgroup.closure (Set.range Z) :=
      Subgroup.subset_closure (Set.mem_range_self i)
    exact ⟨x, Subgroup.zpowers_le.2 hZi x.2, rfl⟩

theorem isElemAbelian_subgroupOf {Q : Type*} [Group Q] {p : ℕ} {E H : Subgroup Q}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem le_localRank_of_le {Q : Type} [Group Q] {H : Subgroup Q} [Finite H] {p k : ℕ}
    (hp : p.Prime) {P E : Subgroup Q} (hPH : P ≤ H) (hEH : E ≤ H) (hP : P ≠ ⊥)
    (hP2 : IsPGroup 2 P) (hE : CFSG.Assembly.IsElemAbelian p E) (hc : Nat.card E = p ^ k)
    (hEP : E ≤ Subgroup.normalizer (P : Set Q)) : k ≤ localRank p H := by
  refine le_localRank_of_le_normalizer hp (P := P.subgroupOf H) (E := E.subgroupOf H) ?_
    (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm) (isElemAbelian_subgroupOf hE) ?_ ?_
  · rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun hd => hP (hd.eq_bot_of_le hPH)
  · rw [← hc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hEP (Subgroup.mem_subgroupOf.1 hx)) h

theorem le_localRank_of_witness {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : π.ker ≤ Subgroup.center G) {H : Subgroup Q} [Finite H] {n : ℕ} (Z A : Fin n → G)
    (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPc : ¬ P ≤ Subgroup.center G) (hZP : ∀ i, Z i ∈ Subgroup.normalizer (P : Set G))
    (hZH : ∀ i, π (Z i) ∈ H) (hPH : P.map π ≤ H) : n ≤ localRank 3 H := by
  obtain ⟨E, hE, hc, hEZ⟩ := exists_isElemAbelian_of_witness π hπ Z A h3 h1 h2 hZA hZZ
  have hZ : Subgroup.closure (Set.range Z) ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 hZP)
  have hZH' : (Subgroup.closure (Set.range Z)).map π ≤ H :=
    Subgroup.map_le_iff_le_comap.2 ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 hZH))
  refine le_localRank_of_le Nat.prime_three hPH (hEZ.trans hZH') ?_ (hP2.map π) hE hc
    (hEZ.trans ((Subgroup.map_mono hZ).trans (Subgroup.le_normalizer_map π)))
  intro h
  exact hPc (((Subgroup.map_eq_bot_iff P).1 h).trans hπ)

theorem isPGroup_zpowers_of_sq {G : Type*} [Group G] {t : G} (ht : t ^ 2 = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  rintro ⟨g, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change (t ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ht,
    _root_.one_zpow]

theorem mem_normalizer_zpowers {G : Type*} [Group G] {g t : G} (h : Commute g t) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
  rintro _ ⟨k, rfl⟩
  exact (Commute.zpow_left h.symm k).eq

theorem le_localRank_of_witness_involution {G Q : Type} [Group G] [Group Q] (π : G →* Q)
    (hπ : π.ker ≤ Subgroup.center G) {H : Subgroup Q} [Finite H] {n : ℕ} (Z A : Fin n → G)
    (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) {t : G} (ht : t ^ 2 = 1)
    (htc : t ∉ Subgroup.center G) (hZt : ∀ i, Commute (Z i) t) (hZH : ∀ i, π (Z i) ∈ H)
    (htH : π t ∈ H) : n ≤ localRank 3 H :=
  le_localRank_of_witness π hπ Z A h3 h1 h2 hZA hZZ (isPGroup_zpowers_of_sq ht)
    (fun h => htc (h (Subgroup.mem_zpowers t))) (fun i => mem_normalizer_zpowers (hZt i)) hZH
    (by rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]; exact htH)

theorem mem_normalizer_sup_of_commute {G : Type*} [Group G] {g a b : G} (ha : Commute g a)
    (hb : Commute g b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer {g} :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 ha.eq.symm))
      (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hb.eq.symm))
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hh))

theorem mem_normalizer_sup_zpowers {G : Type*} [Group G] {g a b : G}
    (ha : g * a * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb : g * b * g⁻¹ ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (ha' : g⁻¹ * a * g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b)
    (hb' : g⁻¹ * b * g ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a ⊔ Subgroup.zpowers b : Subgroup G) : Set G) := by
  set P := Subgroup.zpowers a ⊔ Subgroup.zpowers b
  have h1 : P ≤ P.comap (MulAut.conj g).toMonoidHom :=
    sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb)
  have h2 : P ≤ P.comap (MulAut.conj g⁻¹).toMonoidHom := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · change g⁻¹ * a * g⁻¹⁻¹ ∈ P
      rwa [inv_inv]
    · change g⁻¹ * b * g⁻¹⁻¹ ∈ P
      rwa [inv_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => h1 hh, fun hh => ?_⟩
  have h3 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ ∈ P := h2 hh
  have e : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
  rwa [e] at h3

end CFSG.SectionRank.QTK

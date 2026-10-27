module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.A6.I1435.Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure
import all CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3KFactsA6

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

open Subgroup CFSG.Open

section Common

variable {X : Type} [Group X] [Finite X]

theorem finite_subgroup : Finite (Subgroup X) :=
  Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective

theorem thompson_le_of_three_dvd {K : Subgroup X} (hKn : K.Normal) {P : Sylow 3 X}
    (e : ↥(P : Subgroup X) ≃* W3)
    (hd1 : ∀ D : Subgroup X, D ≤ Open.thompsonSubgroup (P : Subgroup X) →
      (∀ g ∈ normalizer (Open.thompsonSubgroup (P : Subgroup X) : Set X), ∀ d ∈ D,
        g * d * g⁻¹ ∈ D) →
        D = ⊥ ∨ D = Open.thompsonSubgroup (P : Subgroup X))
    (h3 : 3 ∣ Nat.card K) : Open.thompsonSubgroup (P : Subgroup X) ≤ K := by
  set E := Open.thompsonSubgroup (P : Subgroup X) with hE
  have hD : ∀ g ∈ normalizer (E : Set X), ∀ d ∈ E ⊓ K, g * d * g⁻¹ ∈ E ⊓ K := by
    intro g hg d hd
    exact Subgroup.mem_inf.mpr ⟨(mem_normalizer_iff.mp hg d).mp hd.1, hKn.conj_mem d hd.2 g⟩
  rcases hd1 (E ⊓ K) inf_le_left hD with h | h
  · exfalso
    have hPK : (P : Subgroup X) ⊓ K = ⊥ := by
      refine eq_bot_of_normalized e inf_le_left ?_ ?_
      · intro p hp n hn
        exact Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hp hn.1) (inv_mem hp), hKn.conj_mem n hn.2 p⟩
      · rw [← thompsonSubgroup_eq_baseIn e, eq_bot_iff]
        intro y hy
        have hy' : y ∈ E ⊓ K := Subgroup.mem_inf.mpr ⟨hy.2, hy.1.2⟩
        rwa [h] at hy'
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hk' : orderOf (k : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hk
    have hkp : IsPGroup 3 (zpowers (k : X)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk', pow_one])
    obtain ⟨Q, hQ⟩ := hkp.exists_le_sylow
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq X P Q
    have hkQ : (k : X) ∈ ((g • P : Sylow 3 X) : Subgroup X) := hQ (mem_zpowers _)
    rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hkQ
    have hconj : (MulAut.conj g)⁻¹ • (k : X) = g⁻¹ * k * g := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    rw [hconj] at hkQ
    have hkK : g⁻¹ * (k : X) * g ∈ K := by
      have := hKn.conj_mem (k : X) k.2 g⁻¹
      rwa [inv_inv] at this
    have hmem : g⁻¹ * (k : X) * g ∈ (P : Subgroup X) ⊓ K := Subgroup.mem_inf.mpr ⟨hkQ, hkK⟩
    rw [hPK, mem_bot] at hmem
    have hk1 : (k : X) = 1 := by
      have : (k : X) = g * (g⁻¹ * k * g) * g⁻¹ := by group
      rw [this, hmem, mul_one, mul_inv_cancel]
    rw [hk1, orderOf_one] at hk'
    exact absurd hk' (by norm_num)
  · rw [← h]
    exact inf_le_right

theorem card_dvd_of_isPGroup {P : Sylow 3 X} (e : ↥(P : Subgroup X) ≃* W3) {H : Subgroup X}
    (hH : IsPGroup 3 H) : Nat.card H ∣ 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  have hQc : Nat.card (Q : Subgroup X) = 81 :=
    (Nat.card_congr (Sylow.equiv Q P).toEquiv).trans (card_of_equiv e)
  rw [← hQc]
  exact card_dvd_of_le hQ

theorem nonempty_mulEquiv_W3 {P : Sylow 3 X} (e : ↥(P : Subgroup X) ≃* W3) {H : Subgroup X}
    (hH : IsPGroup 3 H) (h81 : Nat.card H = 81) : Nonempty (↥H ≃* W3) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  have hQc : Nat.card (Q : Subgroup X) = 81 :=
    (Nat.card_congr (Sylow.equiv Q P).toEquiv).trans (card_of_equiv e)
  have hHQ : H = (Q : Subgroup X) := eq_of_le_of_card_ge hQ (by rw [hQc, h81])
  exact ⟨(MulEquiv.subgroupCongr hHQ).trans ((Sylow.equiv Q P).trans e)⟩

theorem conjLinesIn_ne_three {L : Type*} [Group L] {K E : Subgroup X} (hEK : E ≤ K)
    (ψ : ↥K →* L) (hψ : Function.Injective ψ) {x : X} (hx : x ∈ K) (k : Fin 4 → ↥K)
    (hle : ∀ i, ψ (k i * ⟨x, hx⟩ * (k i)⁻¹) ∈ (E.subgroupOf K).map ψ)
    (hinj : ∀ i j, zpowers (ψ (k i * ⟨x, hx⟩ * (k i)⁻¹)) =
      zpowers (ψ (k j * ⟨x, hx⟩ * (k j)⁻¹)) → i = j) :
    conjLinesIn E x ≠ 3 := by
  have := finite_subgroup (X := X)
  let c : Fin 4 → Subgroup X := fun i => (zpowers x).map (MulAut.conj (k i : X)).toMonoidHom
  have hci : ∀ i, c i = zpowers ((k i * ⟨x, hx⟩ * (k i)⁻¹ : ↥K) : X) := by
    intro i
    simp only [c]
    rw [MonoidHom.map_zpowers]
    simp
  have hmem : ∀ i, c i ∈ {c : Subgroup X | ∃ g : X,
      c = (zpowers x).map (MulAut.conj g).toMonoidHom ∧ c ≤ E} := by
    intro i
    refine ⟨k i, rfl, ?_⟩
    rw [hci, zpowers_le]
    obtain ⟨y, hy, hyx⟩ := hle i
    rw [hψ hyx] at hy
    exact hy
  have hinjc : Function.Injective c := by
    intro i j hij
    apply hinj i j
    have h1 := hij
    rw [hci, hci] at h1
    have h2 : (zpowers (k i * ⟨x, hx⟩ * (k i)⁻¹)).map K.subtype =
        (zpowers (k j * ⟨x, hx⟩ * (k j)⁻¹)).map K.subtype := by
      rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      exact h1
    have h3 := map_injective K.subtype_injective h2
    rw [← MonoidHom.map_zpowers, ← MonoidHom.map_zpowers, h3]
  have hle4 : 4 ≤ conjLinesIn E x := by
    unfold conjLinesIn
    calc 4 = (Set.range c).ncard := by rw [Set.ncard_range_of_injective hinjc, Nat.card_fin]
      _ ≤ _ := Set.ncard_le_ncard (by rintro _ ⟨i, rfl⟩; exact hmem i) (Set.toFinite _)
  omega

theorem isPSolvable_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hA : CFSG.HallHigman.IsPSolvable 3 A) : CFSG.HallHigman.IsPSolvable 3 B :=
  CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    e hA

theorem not_isPSolvable_centralizer {K : Subgroup X} {x : X} (hx : x ∈ K) (H : Subgroup ↥K)
    (hH : H ≤ centralizer ({⟨x, hx⟩} : Set ↥K)) (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥H) :
    ¬ CFSG.HallHigman.IsPSolvable 3 ↥(centralizer ({x} : Set X)) := by
  intro hs
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : H.map K.subtype ≤ centralizer ({x} : Set X) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.mp (hH hh)
    exact congrArg Subtype.val this
  have h1 := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le hs hle
  exact hns (isPSolvable_of_equiv (equivMapOfInjective H K.subtype K.subtype_injective).symm h1)

theorem card_inf_centralizer_eq {L : Type*} [Group L] {K : Subgroup X} (ψ : ↥K ≃* L) {x : X}
    (hx : x ∈ K) :
    Nat.card ↥(K ⊓ centralizer ({x} : Set X)) = Nat.card ↥(centralizer ({ψ ⟨x, hx⟩} : Set L)) := by
  have e1 : ↥(K ⊓ centralizer ({x} : Set X)) ≃ ↥(centralizer ({(⟨x, hx⟩ : ↥K)} : Set ↥K)) :=
    { toFun := fun y => ⟨⟨y, (Subgroup.mem_inf.mp y.2).1⟩, by
        rw [mem_centralizer_singleton_iff]
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).2)⟩
      invFun := fun y => ⟨y.1, Subgroup.mem_inf.mpr ⟨y.1.2, by
        rw [mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp y.2)⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : ↥(centralizer ({(⟨x, hx⟩ : ↥K)} : Set ↥K)) ≃
      ↥(centralizer ({ψ ⟨x, hx⟩} : Set L)) :=
    ψ.toEquiv.subtypeEquiv fun a => by
      rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
      constructor
      · intro h
        simpa using congrArg ψ h
      · intro h
        apply ψ.injective
        simpa using h
  exact Nat.card_congr (e1.trans e2)

end Common

section Conj

variable {L : Type*} [Group L] [Finite L]

theorem map_trans_conj {K : Type*} [Group K] (ψ : K ≃* L) (E' : Subgroup K) {F₀ : Subgroup L}
    {g : L} (h : E'.map ψ.toMonoidHom = F₀.map (MulAut.conj g).toMonoidHom) :
    E'.map (ψ.trans (MulAut.conj g⁻¹)).toMonoidHom = F₀ := by
  have hc : (ψ.trans (MulAut.conj g⁻¹)).toMonoidHom =
      (MulAut.conj g⁻¹).toMonoidHom.comp ψ.toMonoidHom := rfl
  rw [hc, ← map_map, h, map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id L := by
    ext y
    simp [mul_assoc]
  rw [this, map_id]

theorem exists_conj_eq (hW : ∀ Q : Sylow 3 L, Nonempty (↥(Q : Subgroup L) ≃* W3))
    {F F₀ : Subgroup L} (hF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hF₀ : ∀ a ∈ F₀, ∀ b ∈ F₀, a * b = b * a) (hcF : Nat.card F = 27)
    (hcF₀ : Nat.card F₀ = 27) : ∃ g : L, F = F₀.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 F := IsPGroup.of_card (n := 3) (by rw [hcF]; norm_num)
  have hp₀ : IsPGroup 3 F₀ := IsPGroup.of_card (n := 3) (by rw [hcF₀]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨Q₀, hQ₀⟩ := hp₀.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq L Q₀ Q
  obtain ⟨e⟩ := hW (g • Q₀)
  refine ⟨g, ?_⟩
  have hle : F₀.map (MulAut.conj g).toMonoidHom ≤ ((g • Q₀ : Sylow 3 L) : Subgroup L) := by
    rw [Sylow.coe_subgroup_smul, pointwise_smul_def]
    exact map_mono hQ₀
  have hcomm : ∀ a ∈ F₀.map (MulAut.conj g).toMonoidHom,
      ∀ b ∈ F₀.map (MulAut.conj g).toMonoidHom, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hF₀ a ha b hb]
  have hcard : 27 ≤ Nat.card (F₀.map (MulAut.conj g).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj g).injective, hcF₀]
  rw [eq_baseIn_of_comm e hQ hF hcF.ge, eq_baseIn_of_comm e hle hcomm hcard]

theorem factorization_three {m : ℕ} (hm : ¬ 3 ∣ m) : (81 * m).factorization 3 = 4 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero,
    show (81 : ℕ) = 3 ^ 4 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same]

theorem card_sylow_three {m : ℕ} (hL : Nat.card L = 81 * m) (hm : ¬ 3 ∣ m) (Q : Sylow 3 L) :
    Nat.card (Q : Subgroup L) = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, hL, factorization_three hm]
  norm_num

end Conj

end CFSG.LocalAnalysis.RankThreeTheoremC.A6.I1435

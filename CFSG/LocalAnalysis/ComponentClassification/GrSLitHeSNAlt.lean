module

public import CFSG.Foundations.Basic
public import CFSG.Blueprint.NativeSporadic
import CFSG.LocalAnalysis.OddStandard.AltNoHe
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
import CFSG.Sporadic.He.Simple

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltNoHe

theorem range_eq_bot_of_held {L : Type} [Group L] [Finite L]
    {Y : Type} [Fintype Y] [DecidableEq Y] (hperf : commutator L = ⊤)
    (eL : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) (π : L →* Perm Y)
    (hn : π.range.Normal) : π.range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨h5, hrange⟩ := five_le_card_and_range_eq hperf π hn hne
  have hsA := alternatingGroup.isSimpleGroup h5
  have : Nontrivial Y := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  let φ : L →* alternatingGroup Y :=
    π.codRestrict (alternatingGroup Y) fun l => by rw [← hrange]; exact ⟨l, rfl⟩
  have hφ : Function.Surjective φ := fun y => by
    have hy : (y : Perm Y) ∈ π.range := by rw [hrange]; exact y.2
    obtain ⟨l, hl⟩ := hy
    exact ⟨l, Subtype.ext hl⟩
  have hcardA : 2 * Nat.card (alternatingGroup Y) = (Nat.card Y).factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm]
  have hevA : 2 ∣ Nat.card (alternatingGroup Y) := by
    have h4 : 4 ∣ (Nat.card Y).factorial := Nat.dvd_factorial (by norm_num) (by omega)
    omega
  have hO : pPrimeCore 2 L ≤ φ.ker := by
    have hnm : ((pPrimeCore 2 L).map φ).Normal := Normal.map inferInstance φ hφ
    rcases hsA.eq_bot_or_eq_top_of_normal ((pPrimeCore 2 L).map φ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      have hdvd := card_map_dvd (pPrimeCore 2 L) φ
      rw [ht, card_top] at hdvd
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
        ((pPrimeCore_coprime_card (p := 2) (G := L)).coprime_dvd_right hdvd) hevA
  have hcardQ : Nat.card (L ⧸ pPrimeCore 2 L) = 4030387200 := by
    rw [Nat.card_congr eL.toEquiv, Sporadic.He.card_He]
  have hsQ : IsSimpleGroup (L ⧸ pPrimeCore 2 L) :=
    @MulEquiv.isSimpleGroup _ _ _ _ Sporadic.He.isSimpleGroup_He eL
  let ψ := QuotientGroup.lift (pPrimeCore 2 L) φ hO
  have hψ : Function.Surjective ψ := QuotientGroup.lift_surjective_of_surjective _ φ hφ hO
  rcases hsQ.eq_bot_or_eq_top_of_normal ψ.ker with hb | ht
  · have h1 := Nat.card_eq_of_bijective ψ ⟨(MonoidHom.ker_eq_bot_iff ψ).mp hb, hψ⟩
    exact OddStandard.factorial_div_two_ne_card_he (Nat.card Y) (by omega)
  · obtain ⟨x, y, hxy⟩ := exists_pair_ne (alternatingGroup Y)
    obtain ⟨x', rfl⟩ := hψ x
    obtain ⟨y', rfl⟩ := hψ y
    have hx : x' ∈ ψ.ker := ht ▸ mem_top x'
    have hy : y' ∈ ψ.ker := ht ▸ mem_top y'
    rw [MonoidHom.mem_ker] at hx hy
    exact hxy (hx.trans hy.symm)

theorem false_of_mulEquiv_alternatingGroup {X : Type} [Group X]
    [Finite X] {n : ℕ} (e : X ≃* alternatingGroup (Fin n)) {a : X} (ha : orderOf a = 2)
    {L : Subgroup X} (hLa : L ≤ centralizer ({a} : Set X))
    (hCN : centralizer ({a} : Set X) ≤ normalizer (L : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X))))
    (eL : L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) : False := by
  let ε : X →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hinj : Function.Injective ε := Subtype.val_injective.comp e.injective
  have hsurj : ∀ p ∈ alternatingGroup (Fin n), ∃ x, ε x = p := fun p hp =>
    ⟨e.symm ⟨p, hp⟩, by simp [ε]⟩
  have ha1 : ε a ≠ 1 := by
    intro h1
    have h2 : a = 1 := hinj (by rw [h1, map_one])
    rw [h2, orderOf_one] at ha
    exact absurd ha (by norm_num)
  have ha2 : ε a * ε a = 1 := by
    rw [← map_mul, ← sq, ← ha, pow_orderOf_eq_one, map_one]
  have hperf : commutator L = ⊤ := by
    have := CatalogueBAlternating.pComponent_perfect hLc
    have : Group.IsPerfect L := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe hLa).toMonoidHom) (subgroupOfEquivOfLe hLa).surjective
    exact Group.IsPerfect.commutator_eq_top
  have hLn : (L.subgroupOf (centralizer ({a} : Set X))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLa).mpr hCN
  let π₁ := (quotP ε a).comp (inclusion hLa)
  let π₂ := (quotF ε a).comp (inclusion hLa)
  have hn₁ : π₁.range.Normal := by
    rw [MonoidHom.range_comp, inclusion_range]
    exact hLn.map _ (quotP_surjective hinj hsurj ha1 ha2)
  have hn₂ : π₂.range.Normal := by
    rw [MonoidHom.range_comp, inclusion_range]
    exact hLn.map _ (quotF_surjective hinj hsurj ha1 ha2)
  have h₁ := range_eq_bot_of_held hperf eL π₁ hn₁
  have h₂ := range_eq_bot_of_held hperf eL π₂ hn₂
  have e₁ : ∀ l, π₁ l = 1 := fun l => by
    have : π₁ l ∈ π₁.range := ⟨l, rfl⟩
    rwa [h₁, mem_bot] at this
  have e₂ : ∀ l, π₂ l = 1 := fun l => by
    have : π₂ l ∈ π₂.range := ⟨l, rfl⟩
    rwa [h₂, mem_bot] at this
  have hab : ∀ x y : L, x * y = y * x := fun x y => by
    apply inclusion_injective hLa
    rw [map_mul, map_mul]
    exact quot_comm hinj ha2 _ _ (e₁ x) (e₂ x) (e₁ y) (e₂ y)
  have hker := ker_eq_top_of_forall_comm hperf (MonoidHom.id L) hab
  have hL1 : ∀ l : L, l = 1 := fun l => MonoidHom.mem_ker.mp (hker ▸ mem_top l)
  have hQ1 : ∀ q : L ⧸ pPrimeCore 2 L, q = 1 := fun q => by
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hL1 l, QuotientGroup.mk_one]
  have : Subsingleton (L ⧸ pPrimeCore 2 L) := ⟨fun x y => (hQ1 x).trans (hQ1 y).symm⟩
  have h1 := Nat.card_of_subsingleton (1 : L ⧸ pPrimeCore 2 L)
  rw [Nat.card_congr eL.toEquiv, Sporadic.He.card_He] at h1
  omega

end CFSG.ComponentClassification.GrSLit.HeSN

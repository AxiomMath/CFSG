module

public import CFSG.Goldschmidt.Steps.G73Basic
public import CFSG.Goldschmidt.Steps.G52
public import CFSG.Goldschmidt.Steps.G3aBorel
public import CFSG.Goldschmidt.Steps.G3bPSL2
public import CFSG.Walter.Bender1970.S4.ComponentTools
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.GorensteinWalter
open scoped MatrixGroups

namespace G38

variable {G : Type} [Group G] [Finite G]

theorem qCoreOf_le_centralizer_of_isComponentOf {X L : Subgroup G}
    (hL : GorensteinWalter.IsComponentOf L X)
    {p : ℕ} (hp : p.Prime) : qCoreOf X p ≤ Subgroup.centralizer (L : Set G) := by
  have h1 : L ≤ Subgroup.centralizer (CFSG.fittingSubgroupOf X : Set G) :=
    (CFSG.Walter.le_componentLayerOf_of_isComponentOf hL).trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (layer_centralizes_fitting X))
  exact Subgroup.le_centralizer_iff.mp (h1.trans
    (Subgroup.centralizer_le (qCoreOf_le_fittingSubgroupOf X p hp)))

theorem oddCoreOf_fittingSubgroupOf_eq {X : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : IsPGroup p X) : oddCoreOf (CFSG.fittingSubgroupOf X) = X := by
  have : Fact p.Prime := ⟨hp⟩
  rw [CFSG.Walter.fittingSubgroupOf_eq_self_of_isNilpotent hX.isNilpotent]
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  exact G52.oddCoreOf_eq_self_of_odd (by rw [hk]; exact (hp.odd_of_ne_two hp2).pow)

theorem le_centralizer_of_isComponentOf
    (h37 : S_G37) (h31 : S_G31) {H A A₀ V L : Subgroup G}
    (hS : IsSStarIn H A) (hA : IsElemAbelian 2 A) (hA₀A : A₀ ≤ A) (hA₀ : ¬ IsCyclic A₀)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hV : ∀ a ∈ A₀, a ≠ 1 → V ≤ qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p)
    (hL : GorensteinWalter.IsComponentOf L H) : V ≤ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hVL
  set K := normalClosureIn H A with hK
  have hKH : K ≤ H := G73.normalClosureIn_le H A
  obtain ⟨a₁, ha₁, a₂, ha₂, ha₁1, ha₂1, ha₁₂⟩ :
      ∃ a₁ ∈ A₀, ∃ a₂ ∈ A₀, a₁ ≠ 1 ∧ a₂ ≠ 1 ∧ a₁ ≠ a₂ := by
    by_contra hcon
    push Not at hcon
    apply hA₀
    by_cases hne : ∃ a ∈ A₀, a ≠ 1
    · obtain ⟨a, ha, ha1⟩ := hne
      refine ⟨⟨⟨a, ha⟩, fun x => ?_⟩⟩
      by_cases hx : (x : G) = 1
      · exact ⟨0, Subtype.ext (by simp [hx])⟩
      · exact ⟨1, Subtype.ext (by simp [hcon a ha x x.2 ha1 hx])⟩
    · push Not at hne
      refine ⟨⟨1, fun x => ⟨0, Subtype.ext ?_⟩⟩⟩
      simp [hne x x.2]
  have hQ : ∀ a ∈ A₀, a ≠ 1 →
      ¬ qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p ≤ Subgroup.centralizer (L : Set G) :=
    fun a ha ha1 h => hVL ((hV a ha ha1).trans h)
  have h37' : ∀ a ∈ A₀, a ≠ 1 → L ≤ K ∧ IsGoldL2 L ∧
      qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p ≤
        L ⊔ H ⊓ Subgroup.centralizer (L : Set G) := by
    intro a ha ha1
    set X := qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p with hX
    have hXp : IsPGroup p X := qCoreOf_isPGroup _ p
    have hXodd : Odd (Nat.card X) := by
      obtain ⟨k, hk⟩ := hXp.exists_card_eq
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    have hXH : X ≤ H := (Subgroup.map_subtype_le _).trans inf_le_left
    have hXn : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) :=
      le_normalizer_of_isNormalIn (qCoreOf_normal_in _ p)
    have hXeq := G52.eq_componentLayerOf_sup_of_isPGroup hp hXp hXodd
    obtain ⟨-, -, -, h4⟩ := h37 G H A hS hA a (hA₀A ha) ha1 X hXH hXn hXeq
    have hO := oddCoreOf_fittingSubgroupOf_eq hp hp2 hXp
    obtain ⟨hLK, hL2, hXL, -⟩ := h4 L hL (by rw [hO]; exact hQ a ha ha1)
    exact ⟨hLK, hL2, hO ▸ hXL⟩
  obtain ⟨hLK, hL2, hQ₁⟩ := h37' a₁ ha₁ ha₁1
  have hnc : ∀ a ∈ A₀, a ≠ 1 → a ∉ Subgroup.centralizer (L : Set G) := by
    intro a ha ha1 haL
    have hLC : L ≤ H ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine le_inf hL.1 fun l hl => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp haL l hl
    exact hQ a ha ha1 (qCoreOf_le_centralizer_of_isComponentOf
      (CFSG.Walter.IsComponentOf.of_le hL hLC inf_le_left) hp)
  have hdec := G73.eq_inf_sup_inf_centralizer h31 hS hA
    (CFSG.Walter.IsComponentOf.of_le hL hLK hKH)
  have hsplit : ∀ a ∈ A, ∃ x ∈ A ⊓ L, ∃ y ∈ A ⊓ Subgroup.centralizer (L : Set G), a = x * y := by
    intro a ha
    rw [hdec] at ha
    refine G3a.exists_mul_of_mem_sup (fun d hd => ?_) ha
    exact Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (show ((A ⊓ L : Subgroup G) : Set G) ⊆ L from
        fun t ht => ht.2) hd.2)
  have hZ : ∀ z : L, z ∈ Subgroup.center L ↔ (z : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro z
    rw [Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h l hl
      exact congrArg Subtype.val (h ⟨l, hl⟩)
    · intro h g
      exact Subtype.ext (h g g.2)
  set π := QuotientGroup.mk' (Subgroup.center L) with hπ
  have hπ1 : ∀ z : L, π z = 1 ↔ (z : G) ∈ Subgroup.centralizer (L : Set G) := fun z => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hZ]
  have hcommL : ∀ l₁ l₂ : L, (((l₁ * l₂)⁻¹ * (l₂ * l₁) : L) : G) ∈
      Subgroup.centralizer (L : Set G) → π l₁ * π l₂ = π l₂ * π l₁ := by
    intro l₁ l₂ h
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, hZ]
    exact h
  obtain ⟨x₁, hx₁, y₁, hy₁, he₁⟩ := hsplit a₁ (hA₀A ha₁)
  obtain ⟨x₂, hx₂, y₂, hy₂, he₂⟩ := hsplit a₂ (hA₀A ha₂)
  have hAc : ∀ u ∈ A, ∀ w ∈ A, u * w = w * u := fun u hu w hw =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨w, hw⟩)
  set z₁ : L := ⟨x₁, hx₁.2⟩ with hz₁
  set z₂ : L := ⟨x₂, hx₂.2⟩ with hz₂
  have hz₁1 : π z₁ ≠ 1 := by
    rw [Ne, hπ1]
    intro h
    exact hnc a₁ ha₁ ha₁1 (he₁ ▸ Subgroup.mul_mem _ h hy₁.2)
  have hz₂1 : π z₂ ≠ 1 := by
    rw [Ne, hπ1]
    intro h
    exact hnc a₂ ha₂ ha₂1 (he₂ ▸ Subgroup.mul_mem _ h hy₂.2)
  have hx₁2 : x₁ * x₁ = 1 := by rw [← pow_two]; exact hA.2 x₁ hx₁.1
  have hz₁₂ : π z₁ ≠ π z₂ := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hZ] at h
    have h' : x₁⁻¹ * x₂ ∈ Subgroup.centralizer (L : Set G) := h
    have ha₁₂1 : a₁ * a₂ ≠ 1 := by
      intro h1
      apply ha₁₂
      have : a₂ * a₂ = 1 := by rw [← pow_two]; exact hA.2 a₂ (hA₀A ha₂)
      calc a₁ = a₁ * (a₂ * a₂) := by rw [this, mul_one]
        _ = (a₁ * a₂) * a₂ := by group
        _ = a₂ := by rw [h1, one_mul]
    apply hnc (a₁ * a₂) (A₀.mul_mem ha₁ ha₂) ha₁₂1
    have hy₁x₂ : y₁ * x₂ = x₂ * y₁ := hAc y₁ hy₁.1 x₂ hx₂.1
    have hx₁inv : x₁ = x₁⁻¹ := eq_inv_of_mul_eq_one_left hx₁2
    have : a₁ * a₂ = (x₁⁻¹ * x₂) * (y₁ * y₂) := by
      rw [he₁, he₂]
      calc x₁ * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by group
        _ = x₁ * (x₂ * y₁) * y₂ := by rw [hy₁x₂]
        _ = x₁ * x₂ * (y₁ * y₂) := by group
        _ = x₁⁻¹ * x₂ * (y₁ * y₂) := by rw [← hx₁inv]
    rw [this]
    exact Subgroup.mul_mem _ h' (Subgroup.mul_mem _ hy₁.2 hy₂.2)
  have hz₁₂c : π z₁ * π z₂ = π z₂ * π z₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAc x₁ hx₁.1 x₂ hx₂.1)
  have hord : ∀ z : L, (z : G) ∈ A → π z ≠ 1 → orderOf (π z) = 2 := by
    intro z hz hz1
    refine orderOf_eq_prime ?_ hz1
    rw [← map_pow]
    have : z ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2 z hz)
    rw [this, map_one]
  obtain ⟨p', f, hp', hp'odd, hf, -, -, ⟨e⟩⟩ := hL2
  set W : Subgroup PSL(2, GaloisField p' f) := Subgroup.closure {e (π z₁), e (π z₂)} with hW
  have hWK : IsKleinFour W := by
    refine CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair
      ?_ ?_ ?_ ?_
    · rw [MulEquiv.orderOf_eq]; exact hord z₁ hx₁.1 hz₁1
    · rw [MulEquiv.orderOf_eq]; exact hord z₂ hx₂.1 hz₂1
    · rw [← map_mul e, ← map_mul e, hz₁₂c]
    · exact fun h => hz₁₂ (e.injective h)
  have hcard : IsOddPrimePower (Nat.card (GaloisField p' f)) :=
    ⟨p', f, hp'.out, hp'odd, hf, by rw [GaloisField.card p' f hf.ne']⟩
  have hWC := G3b.psl2_centralizer_kleinFour (GaloisField p' f) hcard W hWK
  apply hVL
  intro v hv
  have hvQ : v ∈ L ⊔ H ⊓ Subgroup.centralizer (L : Set G) := hQ₁ (hV a₁ ha₁ ha₁1 hv)
  rw [sup_comm] at hvQ
  have hLN : L ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hlH : l ∈ H := hL.1 hl
    constructor
    · intro ht
      refine ⟨H.mul_mem (H.mul_mem hlH ht.1) (H.inv_mem hlH),
        Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
      have hk' : l⁻¹ * k * l ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl
      have hc := Subgroup.mem_centralizer_iff.mp ht.2 _ hk'
      calc k * (l * t * l⁻¹) = l * ((l⁻¹ * k * l) * t) * l⁻¹ := by group
        _ = l * (t * (l⁻¹ * k * l)) * l⁻¹ := by rw [hc]
        _ = l * t * l⁻¹ * k := by group
    · intro ht
      have ht' : l⁻¹ * (l * t * l⁻¹) * l = t := by group
      refine ⟨?_, ?_⟩
      · rw [← ht']
        exact H.mul_mem (H.mul_mem (H.inv_mem hlH) ht.1) hlH
      · refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
        have hk' : l * k * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl)
        have hc := Subgroup.mem_centralizer_iff.mp ht.2 _ hk'
        calc k * t = l⁻¹ * ((l * k * l⁻¹) * (l * t * l⁻¹)) * l := by group
          _ = l⁻¹ * ((l * t * l⁻¹) * (l * k * l⁻¹)) * l := by rw [hc]
          _ = t * k := by group
  obtain ⟨c, hc, l, hl, rfl⟩ := G3a.exists_mul_of_mem_sup hLN hvQ
  set w : L := ⟨l, hl⟩ with hw
  have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc.2 l hl
  have hcomm_w : ∀ (a x y : G), a ∈ A₀ → a ≠ 1 → (hx : x ∈ A ⊓ L) →
      y ∈ A ⊓ Subgroup.centralizer (L : Set G) → a = x * y →
      π w * π ⟨x, hx.2⟩ = π ⟨x, hx.2⟩ * π w := by
    intro a x y ha ha1 hx hy hexy
    have hva : c * l * a = a * (c * l) := by
      have hvC := (Subgroup.map_subtype_le _ : qCoreOf (H ⊓ Subgroup.centralizer ({a} : Set G)) p
        ≤ H ⊓ Subgroup.centralizer ({a} : Set G)) (hV a ha ha1 hv)
      exact Subgroup.mem_centralizer_singleton_iff.mp hvC.2
    rw [hexy] at hva
    have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc.2 x hx.2
    have hly : l * y = y * l := Subgroup.mem_centralizer_iff.mp hy.2 l hl
    have h1 : l * x * (c * y) = x * l * (y * c) := by
      calc l * x * (c * y) = l * (x * c) * y := by group
        _ = l * (c * x) * y := by rw [hxc]
        _ = (l * c) * x * y := by group
        _ = (c * l) * x * y := by rw [hlc]
        _ = c * l * (x * y) := by group
        _ = x * y * (c * l) := hva
        _ = x * (y * (l * c)) := by rw [← hlc]; group
        _ = x * ((y * l) * c) := by group
        _ = x * ((l * y) * c) := by rw [← hly]
        _ = x * l * (y * c) := by group
    have key : (l * x)⁻¹ * (x * l) = c * y * c⁻¹ * y⁻¹ := by
      have h2 : x * l = l * x * (c * y) * (y * c)⁻¹ := by rw [h1]; group
      rw [h2]
      group
    refine hcommL w ⟨x, hx.2⟩ ?_
    show (((w * ⟨x, hx.2⟩)⁻¹ * (⟨x, hx.2⟩ * w) : L) : G) ∈ Subgroup.centralizer (L : Set G)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hw]
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hc.2 hy.2)
      (Subgroup.inv_mem _ hc.2)) (Subgroup.inv_mem _ hy.2)
  have hw₁ := hcomm_w a₁ x₁ y₁ ha₁ ha₁1 hx₁ hy₁ he₁
  have hw₂ := hcomm_w a₂ x₂ y₂ ha₂ ha₂1 hx₂ hy₂ he₂
  have hWle : W ≤ Subgroup.centralizer ({e (π w)} : Set PSL(2, GaloisField p' f)) := by
    rw [hW, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← map_mul e, ← map_mul e,
        hw₁]
    · rw [Set.mem_singleton_iff] at hg
      rw [hg, SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← map_mul e,
        ← map_mul e, hw₂]
  have hwC : e (π w) ∈ Subgroup.centralizer (W : Set PSL(2, GaloisField p' f)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hWle hg)
  rw [hWC] at hwC
  have : IsKleinFour W := hWK
  have hw2 : π w ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one, pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨e (π w), hwC⟩ : W))
  have hVp : IsPGroup p V := (qCoreOf_isPGroup _ p).to_le (hV a₁ ha₁ ha₁1)
  obtain ⟨k, hk⟩ := hVp ⟨c * l, hv⟩
  have hwp : π w ^ p ^ k = 1 := by
    rw [← map_pow, hπ1]
    have h1 : (c * l) ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [Commute.mul_pow hlc.symm] at h1
    have h2 : l ^ p ^ k = (c ^ p ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
    have : ((w ^ p ^ k : L) : G) = l ^ p ^ k := by rw [Subgroup.coe_pow]
    rw [this, h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc.2 _)
  have hw1 : π w = 1 := by
    have h1 : orderOf (π w) ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
    have h2 : orderOf (π w) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hwp
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  rw [hπ1] at hw1
  exact Subgroup.mul_mem _ hc.2 hw1

end G38

end CFSG.Goldschmidt

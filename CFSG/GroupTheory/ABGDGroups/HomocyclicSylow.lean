module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.Local
import CFSG.Walter.AStar.Components
import CFSG.LocalAnalysis.RankTwoShapes.Homocyclic.ExponentTwo
import CFSG.LocalAnalysis.RankTwoShapes.CentralMovement
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.ABGDGroups

open CFSG.RankTwoShapes

theorem homocyclic_involution_eq_or_eq_mul {G : Type*} [Group G] {n : ℕ} (hn : 1 ≤ n)
    {S : Subgroup G} (e : S ≃* HomocyclicGroup n) {x w u : G} (hxS : x ∈ S) (hwS : w ∈ S)
    (huS : u ∈ S) (hx : x ^ 2 = 1) (hw : w ^ 2 = 1) (hu : u ^ 2 = 1) (hw1 : w ≠ 1)
    (hu1 : u ≠ 1) (huw : u ≠ w) (hx1 : x ≠ 1) (hxw : x ≠ w) : x = u ∨ x = u * w := by
  obtain ⟨a, rfl⟩ := exists_homocyclicEmbed e x hxS
  obtain ⟨b, rfl⟩ := exists_homocyclicEmbed e w hwS
  obtain ⟨c, rfl⟩ := exists_homocyclicEmbed e u huS
  have h2 : ∀ v, homocyclicEmbed e v ^ 2 = 1 → v + v = 0 := fun v hv => by
    rw [← homocyclicEmbed_eq_one_iff e, homocyclicEmbed_add, ← pow_two, hv]
  have h1 : ∀ v, homocyclicEmbed e v ≠ 1 → v ≠ 0 := fun v hv h =>
    hv (by rw [h, homocyclicEmbed_zero])
  rcases vector_klein hn a b c (h2 a hx) (h2 b hw) (h2 c hu) (h1 b hw1) (h1 c hu1)
    (fun h => huw (by rw [h])) (h1 a hx1) (fun h => hxw (by rw [h])) with h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (by rw [h, homocyclicEmbed_add])

theorem not_isComponent_of_homocyclic_sylow {K : Type} [Group K] [Finite K]
    (hO : oddCore K = ⊥) (U : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (e : (U : Subgroup K) ≃* HomocyclicGroup n) (L : Subgroup K) : ¬ IsComponent L := by
  intro hLc
  replace hO : pPrimeCore 2 K = ⊥ := (pPrimeCore_eq_piCore K 2).trans
    ((oddCore_eq_piCore K).symm.trans hO)
  have hL := (Walter.isComponent_iff_isComponentOf_top L).mp hLc
  have hY : Walter.HasAbelianSylowTwo K :=
    Walter.hasAbelianSylowTwo_of_sylow U (homocyclic_isMulCommutative e)
  have : IsSimpleGroup L := Walter.isSimpleGroup_of_isComponentOf hO hY hL
  have hnonab : ∃ a b : L, a * b ≠ b * a := Walter.nonabelian_of_isComponentOf hL
  have hinner := Walter.exists_inner_of_sylow_le_normalizer hY L hnonab U
    (Walter.sylow_le_normalizer_of_isComponentOf hO hY U hL)
  have hLC : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set K) → x = 1 := by
    intro x hxL hxC
    have hmem : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y y.2)
    rw [Walter.center_eq_bot_of_isSimpleGroup hnonab, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  obtain ⟨P, hP⟩ := Walter.exists_sylow_map_eq_inf_of_isSubnormal U
    (Walter.isSubnormal_of_isComponentOf hL)
  have hPmem : ∀ x : L, x ∈ (P : Subgroup L) ↔ (x : K) ∈ (U : Subgroup K) := by
    intro x
    constructor
    · intro hx
      have hx' : (x : K) ∈ (P : Subgroup L).map L.subtype := ⟨x, hx, rfl⟩
      rw [hP] at hx'
      exact hx'.1
    · intro hx
      have hx' : (x : K) ∈ (U : Subgroup K) ⊓ L := ⟨hx, x.2⟩
      rw [← hP] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rwa [← Subtype.ext hyx]
  have hPab : ∀ a b : (P : Subgroup L), a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (homocyclic_mul_comm e _ _ ((hPmem _).mp a.2) ((hPmem _).mp b.2)))
  have h2L : 2 ∣ Nat.card L := even_iff_two_dvd.mp (Walter.even_card_of_isSimpleGroup hnonab)
  have h2P : 2 ∣ Nat.card (P : Subgroup L) :=
    P.isPGroup'.card_eq_or_dvd.resolve_left fun h =>
      P.ne_bot_of_dvd_card h2L (Subgroup.card_eq_one.mp h)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup L)) 2 h2P
  have hzZ : z ∈ Subgroup.center (P : Subgroup L) :=
    Subgroup.mem_center_iff.mpr fun g => hPab g z
  obtain ⟨g, hgP, hgz⟩ := simple_central_sylow_involution_movement hnonab P z hzZ hz
  set z₁ : K := ((z : L) : K) with hz₁
  set z₂ : K := ((g⁻¹ * (z : L) * g : L) : K) with hz₂
  have hz₁L : z₁ ∈ L := (z : L).2
  have hz₂L : z₂ ∈ L := (g⁻¹ * (z : L) * g).2
  have hz₁U : z₁ ∈ (U : Subgroup K) := (hPmem _).mp z.2
  have hz₂U : z₂ ∈ (U : Subgroup K) := (hPmem _).mp hgP
  have hzo : orderOf z₁ = 2 := by rw [hz₁, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hz₁2 : z₁ ^ 2 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z₁
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzo
    norm_num at hzo
  have hz₂eq : z₂ = (g : K)⁻¹ * z₁ * g := rfl
  have hz₂2 : z₂ ^ 2 = 1 := by
    rw [hz₂eq, pow_two]
    calc (g : K)⁻¹ * z₁ * g * ((g : K)⁻¹ * z₁ * g) = (g : K)⁻¹ * (z₁ * z₁) * g := by group
      _ = 1 := by rw [← pow_two, hz₁2]; group
  have hz₂1 : z₂ ≠ 1 := by
    intro h
    apply hz₁1
    rw [hz₂eq] at h
    calc z₁ = (g : K) * ((g : K)⁻¹ * z₁ * g) * (g : K)⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hz₁₂ : z₁ ≠ z₂ := fun h => hgz (Subtype.ext h.symm)
  have hW : ∀ c ∈ (U : Subgroup K), c ∈ Subgroup.centralizer (L : Set K) → c = 1 := by
    intro c hcU hcC
    by_contra hc1
    set W := (U : Subgroup K) ⊓ Subgroup.centralizer (L : Set K)
    have hWp : IsPGroup 2 W := U.isPGroup'.to_le inf_le_left
    have : Nontrivial W := ⟨⟨⟨c, hcU, hcC⟩, 1, fun h => hc1 (congrArg Subtype.val h)⟩⟩
    have h2W : 2 ∣ Nat.card W := hWp.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2W
    have hwo : orderOf (w : K) = 2 := by rw [Subgroup.orderOf_coe, hw]
    have hw2 : (w : K) ^ 2 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one _
    have hw1 : (w : K) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hwo
      norm_num at hwo
    have hwL : (w : K) ∉ L := fun h => hw1 (hLC _ h w.2.2)
    rcases homocyclic_involution_eq_or_eq_mul (by omega) e w.2.1 hz₂U hz₁U hw2 hz₂2 hz₁2 hz₂1
      hz₁1 hz₁₂ hw1 (fun h => hwL (h ▸ hz₂L)) with h | h
    · exact hwL (h ▸ hz₁L)
    · exact hwL (h ▸ L.mul_mem hz₁L hz₂L)
  have hUL : (U : Subgroup K) ≤ L := by
    intro u hu
    obtain ⟨k, hkL, hk⟩ := hinner u hu
    have hcC : k⁻¹ * u ∈ Subgroup.centralizer (L : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      calc x * (k⁻¹ * u) = k⁻¹ * (k * x * k⁻¹) * u := by group
        _ = k⁻¹ * (u * x * u⁻¹) * u := by rw [hk x hx]
        _ = k⁻¹ * u * x := by group
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp U.isPGroup') ⟨u, hu⟩
    have hupow : u ^ (2 ^ a) = 1 := by
      have h := pow_orderOf_eq_one (⟨u, hu⟩ : (U : Subgroup K))
      rw [ha] at h
      exact congrArg Subtype.val h
    have hkc : Commute k (k⁻¹ * u) := (Subgroup.mem_centralizer_iff.mp hcC k hkL)
    have hkpow : k ^ (2 ^ a) = 1 := by
      have h1 := hkc.mul_pow (2 ^ a)
      rw [mul_inv_cancel_left, hupow] at h1
      have hk' : k ^ (2 ^ a) = ((k⁻¹ * u) ^ (2 ^ a))⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
      apply hLC _ (L.pow_mem hkL _)
      rw [hk']
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcC _)
    have hkN : (⟨k, hkL⟩ : L) ∈ Subgroup.normalizer ((P : Subgroup L) : Set L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hPmem, hPmem]
      have hy : ((⟨k, hkL⟩ * y * (⟨k, hkL⟩ : L)⁻¹ : L) : K) = u * y * u⁻¹ := (hk y y.2).symm
      rw [hy]
      constructor
      · intro hyU
        exact (U : Subgroup K).mul_mem ((U : Subgroup K).mul_mem hu hyU)
          ((U : Subgroup K).inv_mem hu)
      · intro hyU
        have := (U : Subgroup K).mul_mem ((U : Subgroup K).mul_mem
          ((U : Subgroup K).inv_mem hu) hyU) hu
        simpa [mul_assoc] using this
    have hkP := mem_sylow_of_mem_normalizer_of_pow P hkN a (Subtype.ext hkpow)
    have hkU : k ∈ (U : Subgroup K) := (hPmem _).mp hkP
    have hc1 := hW (k⁻¹ * u) ((U : Subgroup K).mul_mem ((U : Subgroup K).inv_mem hkU) hu) hcC
    have hku : u = k := by
      calc u = k * (k⁻¹ * u) := by group
        _ = k := by rw [hc1, mul_one]
    rw [hku]
    exact hkL
  let S : Sylow 2 L := U.subtype hUL
  let eS : (S : Subgroup L) ≃* HomocyclicGroup n :=
    (MulEquiv.subgroupCongr (Sylow.coe_subtype U hUL)).trans
      ((Subgroup.subgroupOfEquivOfLe hUL).trans e)
  have := homocyclic_sylow_simple_exponent_two hnonab S n (by omega) ⟨eS⟩
  omega

theorem layer_eq_bot_of_homocyclic_sylow {K : Type} [Group K] [Finite K]
    (hO : oddCore K = ⊥) (U : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (e : (U : Subgroup K) ≃* HomocyclicGroup n) : layer K = ⊥ := by
  rw [layer, sSup_eq_bot]
  intro L hL
  exact absurd hL (not_isComponent_of_homocyclic_sylow hO U hn e L)

theorem homocyclic_sylow_normal_of_oddCore_eq_bot
    {K : Type} [Group K] [Finite K] (hO : CFSG.oddCore K = ⊥)
    (U : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (e : (U : Subgroup K) ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) :
    (U : Subgroup K).Normal ∧ Subgroup.centralizer (U : Set K) = U ∧
      ((U : Subgroup K).index = 1 ∨ (U : Subgroup K).index = 3) := by
  have hO' : pPrimeCore 2 K = ⊥ := (pPrimeCore_eq_piCore K 2).trans
    ((oddCore_eq_piCore K).symm.trans hO)
  have hchar : Subgroup.centralizer (pCore 2 K : Set K) ≤ pCore 2 K :=
    isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot K 2 hO'
      (layer_eq_bot_of_homocyclic_sylow hO U hn e)
  have hFU : pCore 2 K ≤ (U : Subgroup K) := pCore_isPGroup.le_sylow_of_normal U
  have hUC : ∀ {X : Subgroup K}, X ≤ (U : Subgroup K) →
      (U : Subgroup K) ≤ Subgroup.centralizer (X : Set K) := by
    intro X hX u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact homocyclic_mul_comm e x u (hX hx) hu
  have hUeq : (U : Subgroup K) = pCore 2 K := le_antisymm ((hUC hFU).trans hchar) hFU
  have hnormal : (U : Subgroup K).Normal := hUeq ▸ pCore_normal
  have hcent : Subgroup.centralizer ((U : Subgroup K) : Set K) = U := by
    refine le_antisymm ?_ (hUC le_rfl)
    rw [hUeq]
    exact hchar
  refine ⟨hnormal, hcent, ?_⟩
  by_cases htop : (U : Subgroup K) = ⊤
  · exact Or.inl (by rw [htop, Subgroup.index_top])
  · right
    obtain ⟨g, hg⟩ : ∃ g : K, g ∉ (U : Subgroup K) := by
      by_contra h
      push Not at h
      exact htop (eq_top_iff.mpr fun g _ => h g)
    have hN : Subgroup.normalizer ((U : Subgroup K) : Set K) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hnormal
    have hgN : g ∈ Subgroup.normalizer ((U : Subgroup K) : Set K) := by
      rw [hN]
      exact Subgroup.mem_top g
    have hgC : g ∉ Subgroup.centralizer ((U : Subgroup K) : Set K) := by
      rwa [hcent]
    have h3 := homocyclic_card_normalizer_quotient U e (by omega) hgN hgC
    rw [← Subgroup.index_eq_card] at h3
    change (Subgroup.centralizer ((U : Subgroup K) : Set K)).relIndex
      (Subgroup.normalizer ((U : Subgroup K) : Set K)) = 3 at h3
    rwa [hcent, hN, Subgroup.relIndex_top_right] at h3

theorem homocyclic_sylow_normal_index_three
    {K : Type} [Group K] [Finite K]
    (hO : CFSG.oddCore K = ⊥)
    (hindex : ∀ N : Subgroup K, N.Normal → N.index ≠ 2)
    (U : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (e : (U : Subgroup K) ≃*
      Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) :
    (U : Subgroup K).Normal ∧
      Subgroup.centralizer (U : Set K) = U ∧
      (U : Subgroup K).index = 3 := by
  obtain ⟨hnormal, hcent, h1 | h3⟩ := homocyclic_sylow_normal_of_oddCore_eq_bot hO U hn e
  · exfalso
    have htop : (U : Subgroup K) = ⊤ := Subgroup.index_eq_one.mp h1
    have hmem : ∀ g : K, g ∈ (U : Subgroup K) := fun g => htop ▸ Subgroup.mem_top g
    have hcard : Nat.card K = 2 ^ (2 * n) := by
      rw [← Subgroup.card_top (G := K), ← htop, homocyclic_card e, pow_mul]
      norm_num
    obtain ⟨N, hN⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 2 (n := 2 * n - 1)
      (by rw [hcard]; exact pow_dvd_pow 2 (by omega))
    have hNindex : N.index = 2 := by
      have h := N.card_mul_index
      rw [hN, hcard, show 2 * n = (2 * n - 1) + 1 by omega, pow_succ] at h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h
    have hNnormal : N.Normal := ⟨fun x hx g => by
      rwa [homocyclic_mul_comm e g x (hmem g) (hmem x), mul_inv_cancel_right]⟩
    exact hindex N hNnormal hNindex
  · exact ⟨hnormal, hcent, h3⟩

theorem homocyclic_sylow_oddCore_sup_index
    {K : Type} [Group K] [Finite K]
    (U : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (e : (U : Subgroup K) ≃* Multiplicative (ZMod (2 ^ n)) × Multiplicative (ZMod (2 ^ n))) :
    (CFSG.oddCore K ⊔ (U : Subgroup K)).Normal ∧
      ((CFSG.oddCore K ⊔ (U : Subgroup K)).index = 1 ∨
        (CFSG.oddCore K ⊔ (U : Subgroup K)).index = 3) := by
  have hO : oddCore (K ⧸ oddCore K) = ⊥ := by
    rw [oddCore_eq_piCore (K ⧸ oddCore K)]
    let f := QuotientGroup.quotientMulEquivOfEq (oddCore_eq_piCore K)
    apply (Subgroup.map_eq_bot_iff_of_injective _ (f := f.toMonoidHom) f.injective).mp
    rw [LocalCores.piCore_map_mulEquiv]
    exact LocalCores.prime_set_core_quotient {q : Nat.Primes | q.val ≠ 2}
  set π := QuotientGroup.mk' (oddCore K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hcop : Nat.Coprime (Nat.card (U : Subgroup K)) (Nat.card (oddCore K)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp U.isPGroup'
    have h2 : Nat.Coprime 2 (Nat.card (oddCore K)) := by
      rw [oddCore_eq_piCore K, ← pPrimeCore_eq_piCore K 2]
      exact pPrimeCore_coprime_card
    rw [hk]
    exact h2.pow_left k
  have hUO : (U : Subgroup K) ⊓ oddCore K = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hinj : Function.Injective (π.comp (U : Subgroup K).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπdef, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx' : (x : K) ∈ (U : Subgroup K) ⊓ oddCore K := ⟨x.2, hx⟩
    rw [hUO, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  let Ubar : Sylow 2 (K ⧸ oddCore K) := U.mapSurjective hπ
  have hrange : (π.comp (U : Subgroup K).subtype).range = (Ubar : Subgroup (K ⧸ oddCore K)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Sylow.coe_mapSurjective]
  let ebar : (Ubar : Subgroup (K ⧸ oddCore K)) ≃* HomocyclicGroup n :=
    (MulEquiv.subgroupCongr hrange).symm.trans ((MonoidHom.ofInjective hinj).symm.trans e)
  obtain ⟨hnormal, -, hindex⟩ := homocyclic_sylow_normal_of_oddCore_eq_bot hO Ubar hn ebar
  have hcomap : (Ubar : Subgroup (K ⧸ oddCore K)).comap π = oddCore K ⊔ (U : Subgroup K) := by
    rw [Sylow.coe_mapSurjective, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  rw [← hcomap, Subgroup.index_comap_of_surjective _ hπ]
  exact ⟨hnormal.comap π, hindex⟩

end CFSG.ABGDGroups

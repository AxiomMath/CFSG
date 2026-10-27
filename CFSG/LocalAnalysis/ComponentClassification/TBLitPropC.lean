module

public import CFSG.LocalAnalysis.ComponentClassification.TBLitHatC
public import CFSG.LocalAnalysis.ComponentClassification.TBLitQuotSL

public noncomputable section

namespace CFSG.ComponentClassification.TBLit

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.UnbalancingLocal
open scoped commutatorElement Pointwise MatrixGroups

theorem isSolvable_centralPreimage (L : Type*) [Group L] [Finite L] :
    Group.IsSolvable (centralPreimage (pPrimeCore 2 L)) := by
  have hO : Group.IsSolvable (pPrimeCore 2 L) :=
    Milestones.odd_order_solvable (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hZ : Group.IsSolvable (center (L ⧸ pPrimeCore 2 L)) :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.2 a))
  let g : centralPreimage (pPrimeCore 2 L) →* center (L ⧸ pPrimeCore 2 L) :=
    ((QuotientGroup.mk' (pPrimeCore 2 L)).comp
      (centralPreimage (pPrimeCore 2 L)).subtype).codRestrict _ (fun x => x.2)
  refine Group.isSolvable_of_ker_le_range (inclusion (le_centralPreimage _)) g ?_
  intro x hx
  have hx1 : QuotientGroup.mk' (pPrimeCore 2 L) (x : L) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  exact ⟨⟨x, hx1⟩, rfl⟩

theorem isQuasisimple_psl_of_sl {F : Type*} [Field F]
    (h : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) F)) : IsQuasisimple PSL(2, F) :=
  CatalogueBAlternating.quasisimple_iff_native.mpr
    (Quasisimple.central_quotient (CatalogueBAlternating.quasisimple_iff_native.mp h) _ le_rfl)

theorem propC_false (hC : BurgoynePropC) {G : Type} [Group G] [Finite G] {K : Subgroup G}
    [K.Normal] (hK : IsQuasisimple (K ⧸ pPrimeCore 2 K))
    (hZ : center (K ⧸ centralPreimage (pPrimeCore 2 K)) = ⊥)
    (hM4 : IsM4 (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).range) {a : G}
    (ha : orderOf ((conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict a) = 2)
    {Y : Subgroup G}
    (hY1 : Y.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict ≠ ⊥)
    (hY2 : Y.map (conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict ≤
      oddCentralizerCore ((conjQuotAction K (centralPreimage (pPrimeCore 2 K))).rangeRestrict a))
    {δ₁ δ₂ : G} (hδ₂ : orderOf δ₂ = 2) (hδ₁K : δ₁ ∈ K) (hδ₂K : δ₂ ∈ K)
    (hδ₁ : orderOf δ₁ = 2) (hKδ₁ : K ≤ centralizer ({δ₁} : Set G))
    (hδ₂nt : ¬ ∀ k ∈ K, ⁅k, δ₂⁆ ∈ oddCoreIn K)
    {N₁ N₂ : Subgroup G} (hN₁ : N₁ ≤ K ⊓ centralizer ({δ₂} : Set G))
    (hN₁s : (N₁.subgroupOf (K ⊓ centralizer ({δ₂} : Set G))).IsSubnormal)
    (hN₂ : N₂ ≤ K ⊓ centralizer ({δ₂} : Set G))
    (hN₂s : (N₂.subgroupOf (K ⊓ centralizer ({δ₂} : Set G))).IsSubnormal)
    (hN₁g : CatalogueBPrimeJoin.primeResidual 2 N₁ = ⊤)
    (hN₂g : CatalogueBPrimeJoin.primeResidual 2 N₂ = ⊤)
    (hN₁q : IsQuasisimple (N₁ ⧸ pPrimeCore 2 N₁)) (hN₂q : IsQuasisimple (N₂ ⧸ pPrimeCore 2 N₂))
    (hδN₁ : δ₁ ∈ N₁) (hδN₂ : δ₂ ∈ N₂) {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 0 < n)
    (e₁ : N₁ ⧸ pPrimeCore 2 N₁ ≃* SL(2, GaloisField p n))
    (e₂ : N₂ ⧸ pPrimeCore 2 N₂ ≃* SL(2, GaloisField p n))
    (hprop₁ : ActsProperly a Y N₁ (oddCoreIn N₁)) (hprop₂ : ActsProperly a Y N₂ (oddCoreIn N₂)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := conjQuotAction K (centralPreimage (pPrimeCore 2 K)) with hα
  set ρ := α.rangeRestrict with hρ
  have hA : Group.IsSolvable (zStarIn K) := by
    have := isSolvable_centralPreimage K
    exact Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective _)
  have hkerA : ∀ {M : Subgroup G}, M ≤ K → M ⊓ ρ.ker ≤ zStarIn K := by
    intro M hMK x hx
    have h2 : α x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp (mem_inf.mp hx).2)
    exact ⟨⟨x, hMK (mem_inf.mp hx).1⟩,
      (conjQuotAction_coe_eq_one_iff hZ ⟨x, hMK (mem_inf.mp hx).1⟩).mp h2, rfl⟩
  have hN₁K : N₁ ≤ K := hN₁.trans inf_le_left
  have hN₂K : N₂ ≤ K := hN₂.trans inf_le_left
  have hδ₂sq : δ₂ ^ 2 = 1 := by rw [← hδ₂]; exact pow_orderOf_eq_one δ₂
  have hr1 : ρ δ₂ ≠ 1 := by
    intro h1
    apply hδ₂nt
    have h2 : α δ₂ = 1 := congrArg Subtype.val h1
    rw [conjQuotAction_eq_one_iff] at h2
    exact forall_mem_oddCoreIn_of_forall_mem_zStarIn hK (le_normalizer hδ₂K) h2
  have hr : orderOf (ρ δ₂) = 2 := orderOf_eq_prime (by rw [← map_pow, hδ₂sq, map_one]) hr1
  have hρδ₁ : ρ δ₁ = 1 := by
    apply Subtype.ext
    change α δ₁ = 1
    rw [conjQuotAction_coe_eq_one_iff hZ ⟨δ₁, hδ₁K⟩]
    change QuotientGroup.mk' (pPrimeCore 2 K) ⟨δ₁, hδ₁K⟩ ∈ center (K ⧸ pPrimeCore 2 K)
    refine map_mem_center_of_surjective (QuotientGroup.mk'_surjective _) ?_
    rw [mem_center_iff]
    intro k
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKδ₁ k.2))
  have hF : Odd (Nat.card (GaloisField p n)) := by
    rw [GaloisField.card p n hn.ne']
    exact ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow
  have hiso₁ : Nonempty ((N₁.map ρ) ⧸ pPrimeCore 2 (N₁.map ρ) ≃* PSL(2, GaloisField p n)) := by
    refine (quotient_pPrimeCore_equiv_of_surjective hF e₁ hN₁q (ρ.subgroupMap N₁)
      (ρ.subgroupMap_surjective N₁) (isSolvable_ker_subgroupMap ρ hA (hkerA hN₁K))
      (δ := ⟨δ₁, hδN₁⟩) ?_ (by rw [Subgroup.orderOf_mk]; exact hδ₁)).1 (Subtype.ext hρδ₁)
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKδ₁ (hN₁K x.2)))
  have hiso₂ : Nonempty ((N₂.map ρ) ⧸ pPrimeCore 2 (N₂.map ρ) ≃* SL(2, GaloisField p n)) := by
    refine (quotient_pPrimeCore_equiv_of_surjective hF e₂ hN₂q (ρ.subgroupMap N₂)
      (ρ.subgroupMap_surjective N₂) (isSolvable_ker_subgroupMap ρ hA (hkerA hN₂K))
      (δ := ⟨δ₂, hδN₂⟩) ?_ (by rw [Subgroup.orderOf_mk]; exact hδ₂)).2
      (fun h => hr1 (congrArg Subtype.val h))
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp (hN₂ x.2)).2)
  have hSLq : IsQuasisimple (Matrix.SpecialLinearGroup (Fin 2) (GaloisField p n)) :=
    LocalCores.isQuasisimple_of_mulEquiv e₁ hN₁q
  have hcomp : ∀ {N : Subgroup G}, N ≤ K ⊓ centralizer ({δ₂} : Set G) →
      (N.subgroupOf (K ⊓ centralizer ({δ₂} : Set G))).IsSubnormal →
      CatalogueBPrimeJoin.primeResidual 2 N = ⊤ →
      IsQuasisimple ((N.map ρ) ⧸ pPrimeCore 2 (N.map ρ)) →
      N.map ρ ≤ centralizer ({ρ δ₂} : Set α.range) ∧
        IsPComponent 2 ((N.map ρ).subgroupOf (centralizer ({ρ δ₂} : Set α.range))) := by
    intro N hN hNs hNg hRq
    have hle : N.map ρ ≤ centralizer ({ρ δ₂} : Set α.range) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        mem_centralizer_singleton_iff.mp (mem_inf.mp (hN hx)).2]
    refine ⟨hle, (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 _ _ hle).mpr
      ⟨isSubnormal_map_centralizer hZ hδ₂K hδ₂sq hN hNs, ?_, hRq⟩⟩
    rw [← CatalogueBPrimeJoin.primeResidual_map_surjective 2 (ρ.subgroupMap N)
      (ρ.subgroupMap_surjective N), hNg]
    exact map_top_of_surjective _ (ρ.subgroupMap_surjective N)
  obtain ⟨eR₁⟩ := hiso₁
  obtain ⟨eR₂⟩ := hiso₂
  have hR₁ := hcomp hN₁ hN₁s hN₁g
    (LocalCores.isQuasisimple_of_mulEquiv eR₁.symm (isQuasisimple_psl_of_sl hSLq))
  have hR₂ := hcomp hN₂ hN₂s hN₂g (LocalCores.isQuasisimple_of_mulEquiv eR₂.symm hSLq)
  obtain ⟨-, hno⟩ := hC α.range hM4 (ρ δ₂) hr (N₁.map ρ) (N₂.map ρ) hR₁.1 hR₁.2 hR₂.1 hR₂.2 p n
    hp2 hn ⟨eR₁⟩ ⟨eR₂⟩ (mem_map_of_mem ρ hδN₂)
  exact hno ⟨ρ a, ha, Y.map ρ, hY1, hY2, hprop₁.map ρ hN₁q hA (hkerA hN₁K),
    hprop₂.map ρ hN₂q hA (hkerA hN₂K)⟩

end CFSG.ComponentClassification.TBLit

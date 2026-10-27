module

public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicTorusNormalizerQuotientsSupport
public import CFSG.CharacterTheory.Semidihedral.Principal.LocalParameterFiveSeventeenSupport

public section

open scoped Classical Pointwise

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.Semidihedral.ActualSimpleLayerLocalPackage CFSG.Open

theorem cyclic_four_group_centralizer_torus_has_two_small_normalizer_quotients
    {G : Type}
    [Group G] [Finite G] (n : ℕ) (hn : 4 ≤ n) (S : Sylow 2 G)
    (fS : SemidihedralGroup n ≃* (S : Subgroup G)) (t : G)
    (ht : t = (fS (r n) : G) ^ 2 ^ (n - 2)) (s₀ : G) (hs₀ : s₀ = fS (s n))
    (V : Subgroup G) (hVdef : V = Subgroup.zpowers t ⊔ Subgroup.zpowers s₀)
    (W : Subgroup G) (m : ℕ) (hW1 : W ≠ ⊥) (hWcyc : IsCyclic W) (hWm : Nat.card W = m)
    (hm : Odd m)
    (hsup : V ⊔ W = Subgroup.centralizer (V : Set G)) (hdisj : Disjoint V W)
    (hCW : Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer (W : Set G) =
      Subgroup.centralizer (V : Set G))
    (hsurj : Function.Surjective V.normalizerMonoidHom) (d : G)
    (hd : d ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.normalizer (V : Set G))
    (hd4 : orderOf d = 4) (hd2 : d ^ 2 = t) (hds : d * s₀ * d⁻¹ = t * s₀)
    (hdW : ∀ w ∈ W, d * w * d⁻¹ = w⁻¹) :
    let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
    let D : Subgroup G := Subgroup.centralizer (V : Set G)
    let M : Subgroup G := Subgroup.normalizer (V : Set G)
    let H : Subgroup G := Subgroup.normalizer (W : Set G)
    let K : Subgroup G := Subgroup.centralizer (W : Set G)
    let π : K →* K ⧸ CFSG.pPrimeCore 2 K := QuotientGroup.mk' (CFSG.pPrimeCore 2 K)
    M ≤ H ∧ C ⊓ H = C ⊓ M ∧ Nat.card (C ⊓ H : Subgroup G) = 8 * m ∧
      (Nonempty ((Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) ≃* DihedralGroup 4) ∧
        Nat.card (Subgroup.zpowers d ⊔ Subgroup.zpowers s₀ : Subgroup G) = 8 ∧
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype =
          Subgroup.zpowers d ⊔ Subgroup.zpowers s₀) ∧
      (∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = V) ∧
      (K : Set G) * (M : Set G) = (H : Set G) ∧ K.relIndex H = 2 ∧
      (∀ h ∈ H, h ∉ K → ∀ w ∈ W, h * w * h⁻¹ = w⁻¹) ∧ Nat.card M = 24 * m ∧
      (Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K)).map K.subtype = M ⊓ K ∧
      Nat.card (M ⊓ K : Subgroup G) = 12 * m ∧
      (Subgroup.centralizer ((V.subgroupOf K : Subgroup K) : Set K)).map K.subtype = D ∧
      (CFSG.pPrimeCore 2 K).map K.subtype = W ∧ (CFSG.pPrimeCore 2 H).map H.subtype = W ∧
      W ≤ (Subgroup.center K).map K.subtype ∧
      (((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 12 * m ∧ Nat.card H = 24 * m) ∨
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 60 * m ∧ Nat.card H = 120 * m)) ∧
        ¬ ((Nonempty ((K ⧸ CFSG.pPrimeCore 2 K) ≃* alternatingGroup (Fin 4)) ∧
            Nat.card K = 12 * m ∧ Nat.card H = 24 * m) ∧
          (CFSG.Assembly.LowTwoRank.StatedClassicalModel (K ⧸ CFSG.pPrimeCore 2 K) .PSL 2 5 1 ∧
            Nat.card K = 60 * m ∧ Nat.card H = 120 * m))) ∧
      IsKleinFour (((V ⊔ W).subgroupOf K).map π) ∧
      (∃ P : Sylow 2 (K ⧸ CFSG.pPrimeCore 2 K),
        (P : Subgroup _) = ((V ⊔ W).subgroupOf K).map π) ∧
      ∀ tK : K, (tK : G) = t → ((V ⊔ W).subgroupOf K).map π = Subgroup.centralizer {π tK} := by
  intro C D M H K π
  subst hWm
  obtain ⟨hzt, ht2, -, -, hs2, hst⟩ := supplied_t_s_facts hn fS ht
  rw [← hs₀] at hs2 hst
  have hV : IsKleinFour V := by
    rw [hVdef, hs₀]
    exact supplied_four_group_isKleinFour hn fS ht
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff, ← hzt]
    have h := (Subgroup.mem_center_iff.mp (CFSG.Semidihedral.z_mem_center n hn))
      (fS.symm ⟨x, hx⟩)
    have h' := congrArg (fun w => ((fS w : S) : G)) h
    simpa only [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply] using h'
  have hS4 : ∀ x ∈ (S : Subgroup G), orderOf x = 4 → x ^ 2 = t := by
    intro x hx hx4
    have hy : orderOf (fS.symm ⟨x, hx⟩) = 4 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hx4
    have h := congrArg (fun w => ((fS w : S) : G))
      (semidihedral_order_four_square n hn _ hy)
    simpa only [map_pow, Subgroup.coe_pow, MulEquiv.apply_symm_apply, hzt] using h
  obtain ⟨hdC, hdM⟩ := Subgroup.mem_inf.mp hd
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsCyclic.isMulCommutative (α := W)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨hMH, hCH, hCHcard, hMcard, -, -, -⟩ := cyclic_torus_normalizer_basic V hVdef hV hs2 hst
    W hWcyc hm hW1 hsup hdisj hCW hsurj hdC hdM hd4 hd2 hds hdW
  obtain ⟨hdih, hVsyl, hKMset, hKH, hinv, hKMcard, htrans⟩ := cyclic_torus_normalizer_sylow S V
    hVdef hSC hS4 hV hs2 hst W hWcyc hm hW1 hsup hdisj hCW hsurj hdC hdM hd4 hd2 hds hdW
  obtain ⟨hR, hH2, hWZ, hcases, hVWk, hVWsyl, hCX⟩ := cyclic_torus_centralizer_quotient_of_data
    V W hVdef hV ht2 hm hWcomm hsup hdisj hCW hVsyl hKH hKMcard htrans
  obtain ⟨-, -, hDK, -, -⟩ := klein_centralizer_odd_core V W hV hm hWcomm hsup hdisj
  have hVD : V ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_left
  have hVK : V ≤ K := hVD.trans hDK
  have hNK : (Subgroup.normalizer ((V.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      M ⊓ K := by
    rw [← Subgroup.subgroupOf_normalizer_eq hVK, Subgroup.subgroupOf_map_subtype]
  have hCKV : (Subgroup.centralizer ((V.subgroupOf K : Subgroup K) : Set K)).map K.subtype =
      D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hy
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact congrArg Subtype.val (hy ⟨v, hVK hv⟩ hv)
    · intro hx
      refine ⟨⟨x, hDK hx⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx v hv)
  refine ⟨hMH, hCH, hCHcard, hdih, hVsyl, hKMset, hKH, hinv, hMcard, hNK,
    by rw [inf_comm]; exact hKMcard, hCKV, hR, hH2, hWZ, hcases, hVWk, hVWsyl, hCX⟩

end CFSG.Semidihedral.Principal

module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma21Rel

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isSubnormal_subgroupOf_trans_of_le {B L K : Subgroup G} (hBL : B ≤ L) (hLK : L ≤ K)
    (hB : (B.subgroupOf L).IsSubnormal) (hL : (L.subgroupOf K).IsSubnormal) :
    (B.subgroupOf K).IsSubnormal := by
  have key : ((B.subgroupOf K).subgroupOf (L.subgroupOf K)).IsSubnormal := by
    let e : L.subgroupOf K ≃* L := Subgroup.subgroupOfEquivOfLe hLK
    have h' := hB.comap e.toMonoidHom
    convert h' using 1
    ext z
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom]
    rfl
  exact Subgroup.IsSubnormal.trans (fun _ hz => hBL hz) key hL

omit [Finite G] in
theorem commutator_sup_zpowers_le {N : Subgroup G} {t : G} (htN : t ∈ normalizer (N : Set G)) :
    ⁅N ⊔ zpowers t, N ⊔ zpowers t⁆ ≤ N := by
  have hle : zpowers t ≤ normalizer (N : Set G) := (zpowers_le).mpr htN
  have hconj : ∀ (k : ℤ) (n : G), n ∈ N → t ^ k * n * (t ^ k)⁻¹ ∈ N := fun k n hn =>
    (mem_normalizer_iff.mp (zpow_mem htN k) n).mp hn
  rw [commutator_le]
  intro x hx y hy
  rw [sup_comm, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (zpowers t) N hle]
    at hx hy
  obtain ⟨u, hu, n, hn, rfl⟩ := hx
  obtain ⟨v, hv, m, hm, rfl⟩ := hy
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
  have e : ⁅t ^ i * n, t ^ j * m⁆ = (t ^ i * n * (t ^ i)⁻¹) *
      (t ^ (i + j) * m * (t ^ (i + j))⁻¹) * (t ^ (i + j) * n⁻¹ * (t ^ (i + j))⁻¹) *
      (t ^ j * m⁻¹ * (t ^ j)⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact mul_mem (mul_mem (mul_mem (hconj i n hn) (hconj (i + j) m hm))
    (hconj (i + j) n⁻¹ (inv_mem hn))) (hconj j m⁻¹ (inv_mem hm))

omit [Finite G] in
theorem le_of_le_sup_zpowers_of_perfect {N K : Subgroup G} {t : G}
    (htN : t ∈ normalizer (N : Set G)) (hK : K ≤ N ⊔ zpowers t) (hKp : ⁅K, K⁆ = K) : K ≤ N :=
  calc K = ⁅K, K⁆ := hKp.symm
    _ ≤ ⁅N ⊔ zpowers t, N ⊔ zpowers t⁆ := commutator_mono hK hK
    _ ≤ N := commutator_sup_zpowers_le htN

theorem isSubnormal_inf_centralizer_of_isComponent {G₀ : Subgroup G} (hG₀ : IsComponent G₀)
    (x : G) :
    ((G₀ ⊓ centralizer ({x} : Set G)).subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
  set C := centralizer ({x} : Set G) with hC
  set E := ⨆ g ∈ C, conjugate G₀ g with hE
  have hEN : E ≤ normalizer (G₀ : Set G) := by
    refine iSup₂_le fun g _ => ?_
    rcases LocalCores.distinct_components_commute hG₀ (isComponent_conjugate hG₀ g) with h | h
    · rw [← h]
      exact le_normalizer
    · have h' : ⁅conjugate G₀ g, G₀⁆ = ⊥ := by rw [commutator_comm]; exact h
      exact (commutator_eq_bot_iff_le_centralizer.mp h').trans (centralizer_le_normalizer _)
  have hG₀E : G₀ ≤ E := le_iSup₂_of_le 1 (one_mem C) (by rw [conjugate_one])
  have hCE : C ≤ normalizer (E : Set G) := fun c hc => by
    rw [hE]
    exact mem_normalizer_iSup_conjugate_of_mem hc
  have hle : (G₀ ⊓ C).subgroupOf C ≤ (E ⊓ C).subgroupOf C := fun y hy =>
    mem_subgroupOf.mpr (inf_le_inf_right C hG₀E (mem_subgroupOf.mp hy))
  have hEn : ((E ⊓ C).subgroupOf C).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer inf_le_right]
    exact fun c hc => mem_normalizer_inf' (hCE hc) (le_normalizer hc)
  refine Subgroup.IsSubnormal.step _ _ hle hEn.isSubnormal ?_
  rw [normal_subgroupOf_iff_le_normalizer hle]
  intro y hy
  have hy' : (y : G) ∈ E ⊓ C := mem_subgroupOf.mp hy
  have hN := mem_normalizer_inf' (hEN (mem_inf.mp hy').1) (le_normalizer (mem_inf.mp hy').2)
  rw [mem_normalizer_iff]
  intro z
  rw [mem_subgroupOf, mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.mp hN z

theorem isPComponent_centralizer_of_sup_zpowers {G₀ : Subgroup G} (hG₀ : IsComponent G₀)
    {t : G} (htN : t ∈ normalizer (G₀ : Set G)) {x : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G) ⊓ (G₀ ⊔ zpowers t))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set G) ⊓ (G₀ ⊔ zpowers t)))) :
    K ≤ G₀ ∧ IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({x} : Set G) with hC
  have hKp : ⁅K, K⁆ = K := GSThmB.commutator_eq_self_of_isPComponent hKC hK
  have hKG₀ : K ≤ G₀ := le_of_le_sup_zpowers_of_perfect htN (hKC.trans inf_le_right) hKp
  refine ⟨hKG₀, ?_⟩
  have hKGC : K ≤ G₀ ⊓ C := le_inf hKG₀ (hKC.trans inf_le_left)
  have hK' : IsPComponent 2 (K.subgroupOf (G₀ ⊓ C)) :=
    isPComponent_subgroupOf_of_le hKGC (le_inf inf_le_right (inf_le_left.trans le_sup_left)) hK
  obtain ⟨hsub, hres, hq⟩ :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K (G₀ ⊓ C) hKGC).mp hK'
  refine (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 K C (hKC.trans inf_le_left)).mpr
    ⟨?_, hres, hq⟩
  exact isSubnormal_subgroupOf_trans_of_le hKGC inf_le_right hsub
    (isSubnormal_inf_centralizer_of_isComponent hG₀ x)

theorem conjClosure_eq_sup_conjugate_subgroup {X : Subgroup G} {a : G} (haX : a ∈ X)
    (ha : orderOf a = 2) {T M : Subgroup G} (hTX : T ≤ X ⊓ centralizer ({a} : Set G))
    (hT : IsPComponent 2 (T.subgroupOf (X ⊓ centralizer ({a} : Set G)))) (hMX : M ≤ X)
    (hM : IsPComponent 2 (M.subgroupOf X)) (hTM : T ≤ M ⊔ conjugate M a) :
    conjClosure T (twoLayerIn X) = M ⊔ conjugate M a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a' : X := ⟨a, haX⟩ with ha'
  have ha'2 : orderOf a' = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  have hcena : centralizer ({a'} : Set X) = (X ⊓ centralizer ({a} : Set G)).subgroupOf X := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf]
    exact ⟨fun h => ⟨y.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)⟩,
      fun h => Subtype.ext (mem_centralizer_singleton_iff.mp h.2)⟩
  have hTXX : T ≤ X := hTX.trans inf_le_left
  have hMaX : conjugate M a ≤ X := conjugate_le_of_mem hMX haX
  have hT'C : T.subgroupOf X ≤ centralizer ({a'} : Set X) := by
    rw [hcena]
    intro y hy
    exact mem_subgroupOf.mpr (hTX (mem_subgroupOf.mp hy))
  have hT'pc : IsPComponent 2 ((T.subgroupOf X).subgroupOf (centralizer ({a'} : Set X))) := by
    rw [hcena, isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2 Nat.prime_two]
    exact hT
  have hconj : conjugate (M.subgroupOf X) a' = (conjugate M a).subgroupOf X :=
    conjugate_subgroupOf_eq M X a'
  have hT'M : T.subgroupOf X ≤ M.subgroupOf X ⊔ conjugate (M.subgroupOf X) a' := by
    rw [hconj, ← subgroupOf_sup hMX hMaX]
    intro y hy
    exact mem_subgroupOf.mpr (hTM (mem_subgroupOf.mp hy))
  have h := conjClosure_eq_sup_conjugate ha'2 hT'C hT'pc hM hT'M
  have h' := congrArg (Subgroup.map X.subtype) h
  rw [map_conjClosure, map_subgroupOf_eq_of_le hTXX, Subgroup.map_sup, hconj,
    map_subgroupOf_eq_of_le hMX, map_subgroupOf_eq_of_le hMaX] at h'
  exact h'

theorem gsFixedLayer_le_footeFixed {a b : G} {L : Subgroup G} (hL : IsTwoComponentAt a L)
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbL : b ∈ coreActionKernel L) :
    UnbalancedGS.gsFixedLayer L b ≤ footeFixed L b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hLa, hLpc⟩ := hL
  have hbCa : b ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr hab.symm
  have hLq := isQuasisimple_quotient_of_isPComponent hLa hLpc
  have hLsub : (L.subgroupOf (centralizer ({a} : Set G))).IsSubnormal := by
    obtain ⟨-, -, hs, -, -⟩ := id hLpc
    exact hs
  have hTpc := gsFixedLayer_isPComponent hLa hLsub hbCa hb hbL.1 hLq hbL.2
  have hTLb := UnbalancedGS.gsFixedLayer_le_inf L b
  have hTres : oddResidualIn (UnbalancedGS.gsFixedLayer L b) = UnbalancedGS.gsFixedLayer L b :=
    oddResidualIn_eq_self_of_isPComponent
      (le_inf (hTLb.trans (inf_le_left.trans hLa)) (hTLb.trans inf_le_right)) hTpc
  calc UnbalancedGS.gsFixedLayer L b = oddResidualIn (UnbalancedGS.gsFixedLayer L b) := hTres.symm
    _ ≤ footeFixed L b := oddResidualIn_mono (le_sup_of_le_left hTLb)

end CFSG.ComponentClassification.FooteLit

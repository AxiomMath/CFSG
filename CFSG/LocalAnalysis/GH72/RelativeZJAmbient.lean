module

public import CFSG.LocalAnalysis.GH72.Vocabulary
public import CFSG.LocalAnalysis.GH72.RelativeZJ

public section

namespace CFSG.GH72

open CFSG CFSG.ABGLocalTools Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

section Transport

variable {K₀ P : Subgroup G}

private theorem eq_O_sup_of_eq_top (hPK : P ≤ K₀)
    (h : oddCore K₀ ⊔ normalizer (ambientMaxCardZJ (P.subgroupOf K₀) : Set K₀) = ⊤) :
    K₀ = O K₀ ⊔ (K₀ ⊓ normalizer (ambientMaxCardZJ P : Set G)) := by
  have hZ : (ambientMaxCardZJ (P.subgroupOf K₀)).map K₀.subtype = ambientMaxCardZJ P := by
    rw [map_ambientMaxCardZJ_of_injective K₀.subtype _
      (K₀.subtype_injective.comp Subtype.val_injective), map_subgroupOf_eq_of_le hPK]
  have hN : (normalizer (ambientMaxCardZJ (P.subgroupOf K₀) : Set K₀)).map K₀.subtype ≤
      K₀ ⊓ normalizer (ambientMaxCardZJ P : Set G) := by
    refine le_inf (map_subtype_le _) ?_
    rw [← hZ]
    exact le_normalizer_map _
  have h' := congrArg (map K₀.subtype) h
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h'
  exact le_antisymm (h'.ge.trans (sup_le_sup_left hN _)) (sup_le (map_subtype_le _) inf_le_left)

private theorem isSylowOf_subgroupOf (hPK : P ≤ K₀) (hQ : IsSylowOf p (P ⊓ O K₀) (O K₀)) :
    IsSylowOf p (P.subgroupOf K₀ ⊓ oddCore K₀) (oddCore K₀) := by
  refine (isSylowOf_map_subtype_iff K₀).mp ?_
  rw [Subgroup.map_inf _ _ _ K₀.subtype_injective, map_subgroupOf_eq_of_le hPK]
  exact hQ

private theorem subgroupOf_le_normalizer {X : Subgroup G} (hXP : X ≤ normalizer (P : Set G)) :
    X.subgroupOf K₀ ≤ normalizer (P.subgroupOf K₀ : Set K₀) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  simp only [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact mem_normalizer_iff.mp (hXP hx) h

end Transport

theorem eq_O_sup_inf_normalizer_zj (hp : p ≠ 2) {K₀ P X L : Subgroup G} (hP : IsPGroup p P)
    (hPK : P ≤ K₀) (hQ : IsSylowOf p (P ⊓ O K₀) (O K₀)) (hX : IsPGroup 2 X)
    (hXP : X ≤ normalizer (P : Set G))
    (hXQ : ¬ X ≤ centralizer ((P ⊓ O K₀ : Subgroup G) : Set G))
    (hL : (L.subgroupOf K₀).Normal) (hOL : O K₀ ≤ L) (hXL : X ≤ L) (hLP : L ⊔ P = K₀)
    (hLmin : ∀ N : Subgroup G, (N.subgroupOf K₀).Normal → O K₀ ≤ N → N ≤ L →
      N = O K₀ ∨ N = L)
    (hD : GorensteinWalter.HasDihedralSylowTwo K₀) :
    K₀ = O K₀ ⊔ (K₀ ⊓ normalizer (ambientMaxCardZJ P : Set G)) := by
  have hLK : L ≤ K₀ := hLP ▸ le_sup_left
  have hXK : X ≤ K₀ := hXL.trans hLK
  refine eq_O_sup_of_eq_top hPK ?_
  refine oddCore_sup_normalizer_zj_eq_top hp (P := P.subgroupOf K₀) (X := X.subgroupOf K₀)
    (L := L.subgroupOf K₀) hP.comap_subtype (isSylowOf_subgroupOf hPK hQ)
    hX.comap_subtype (subgroupOf_le_normalizer hXP) ?_ hL ?_ (fun x hx => hXL hx) ?_ ?_ hD
  · intro h
    apply hXQ
    intro x hx
    rw [mem_centralizer_iff]
    rintro y ⟨hyP, ⟨y', hy', rfl⟩⟩
    have hx' : (⟨x, hXK hx⟩ : K₀) ∈ X.subgroupOf K₀ := hx
    exact congrArg Subtype.val ((mem_centralizer_iff.mp (h hx')) y' ⟨hyP, hy'⟩)
  · intro y hy
    exact hOL (mem_map_of_mem _ hy)
  · rw [← subgroupOf_sup hLK hPK, hLP, subgroupOf_self]
  · intro N hN hON hNL
    have hNsub : (N.map K₀.subtype).subgroupOf K₀ = N :=
      comap_map_eq_self_of_injective K₀.subtype_injective N
    have hmin := hLmin (N.map K₀.subtype) (by rw [hNsub]; exact hN) (map_mono hON)
      (by rw [← map_subgroupOf_eq_of_le hLK]; exact map_mono hNL)
    rcases hmin with h | h
    · exact Or.inl (map_injective K₀.subtype_injective h)
    · right
      apply map_injective K₀.subtype_injective
      rw [h, map_subgroupOf_eq_of_le hLK]

theorem eq_O_sup_inf_normalizer_zj_of_le_O {K₀ P : Subgroup G}
    (hQ : IsSylowOf p (P ⊓ O K₀) (O K₀)) (hPO : P ≤ O K₀) :
    K₀ = O K₀ ⊔ (K₀ ⊓ normalizer (ambientMaxCardZJ P : Set G)) := by
  have hPK : P ≤ K₀ := hPO.trans (map_subtype_le _)
  refine eq_O_sup_of_eq_top hPK (oddCore_sup_normalizer_zj_eq_top_of_le_oddCore
    (isSylowOf_subgroupOf hPK hQ) ?_)
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hPO hx
  have hyx' : y = x := Subtype.ext hyx
  exact hyx' ▸ hy

omit [Fact p.Prime] in
theorem hasDihedralSylowTwo_of_isSylowOf {K S : Subgroup G} (hS : IsSylowOf 2 S K)
    (hD : IsDih S) : GorensteinWalter.HasDihedralSylowTwo K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, ⟨e⟩⟩ := hD
  obtain ⟨T, hT⟩ := hS.exists_sylow_eq_subgroupOf
  intro R
  exact ⟨a, ha, ⟨(Sylow.equiv R T).trans
    ((MulEquiv.subgroupCongr hT).trans ((subgroupOfEquivOfLe hS.le).trans e))⟩⟩

end CFSG.GH72

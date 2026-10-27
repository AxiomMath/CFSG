module

public import CFSG.LocalAnalysis.SteinbergBNPerfectFirstTransferExclusion

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

open Subgroup

variable {G : Type*} [Group G]

theorem eq_of_le_of_sylow_map {p : ℕ} {X Q : Subgroup G}
    (hQ : ∃ R : Sylow p X, (R : Subgroup X).map X.subtype = Q) {Q' : Subgroup G}
    (hQ' : IsPGroup p Q') (hle : Q ≤ Q') (hQ'X : Q' ≤ X) : Q' = Q := by
  obtain ⟨R, rfl⟩ := hQ
  have h := R.is_maximal' (hQ'.comap_subtype (K := X)) (fun x hx => hle ⟨x, hx, rfl⟩)
  rw [← h, map_comap_eq, range_subtype, inf_eq_right.mpr hQ'X]

theorem exists_maximal_pGroup {p : ℕ} {T H : Subgroup G} (hT : IsPGroup p T) (hTH : T ≤ H) :
    ∃ W : Subgroup G, IsPGroup p W ∧ T ≤ W ∧ W ≤ H ∧
      ∀ W' : Subgroup G, IsPGroup p W' → W ≤ W' → W' ≤ H → W' = W := by
  obtain ⟨R, hR⟩ := (hT.comap_subtype (K := H)).exists_le_sylow
  exact ⟨_, R.isPGroup'.map _, fun x hx => ⟨⟨x, hTH hx⟩, hR hx, rfl⟩, map_subtype_le _,
    fun _ hW' hle hW'H => eq_of_le_of_sylow_map ⟨R, rfl⟩ hW' hle hW'H⟩

theorem exists_sylow_eq_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {W H : Subgroup G}
    (hW : IsPGroup p W) (hWH : normalizer (W : Set G) ≤ H)
    (hmax : ∀ W' : Subgroup G, IsPGroup p W' → W ≤ W' → W' ≤ H → W' = W) :
    ∃ R : Sylow p G, (R : Subgroup G) = W := by
  obtain ⟨R, hWR⟩ := hW.exists_le_sylow
  refine ⟨R, le_antisymm ?_ hWR⟩
  have hN : (R : Subgroup G) ⊓ normalizer (W : Set G) = W :=
    hmax _ R.isPGroup'.to_inf_left (le_inf hWR le_normalizer) (inf_le_right.trans hWH)
  have : Group.IsNilpotent (R : Subgroup G) := R.isPGroup'.isNilpotent
  have hself : normalizer ((W.subgroupOf R : Subgroup R) : Set R) = W.subgroupOf R := by
    refine le_antisymm (fun x hx => ?_) le_normalizer
    rw [← subgroupOf_normalizer_eq hWR, mem_subgroupOf] at hx
    rw [mem_subgroupOf, ← hN]
    exact ⟨x.2, hx⟩
  exact subgroupOf_eq_top.mp (normalizerCondition_iff_only_full_group_self_normalizing.mp
    Group.normalizerCondition_of_isNilpotent _ hself)

theorem normalizer_le_of_slice {t : G} {X Q T S W : Subgroup G}
    (hX : centralizer ({t} : Set G) ≤ normalizer (X : Set G)) (hQX : Q ≤ X)
    (hQ : ∀ Q' : Subgroup G, IsPGroup 2 Q' → Q ≤ Q' → Q' ≤ X → Q' = Q)
    (hcan : centralizer ({t} : Set G) ⊓ normalizer (Q : Set G) ≤ normalizer (T : Set G))
    (hW : IsPGroup 2 W) (htW : t ∈ W) (hQW : Q ≤ W) (hSW : S ≤ W)
    (hWN : W ≤ normalizer (T : Set G))
    (hslice : ∀ g : G, g⁻¹ * t * g ∈ W → ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s) :
    normalizer (W : Set G) ≤ normalizer (T : Set G) := by
  intro x hx
  obtain ⟨s, hs, hts⟩ := hslice x ((mem_normalizer_iff''.mp hx t).mp htW)
  have hsW : s ∈ W := hSW hs
  have hyC : x * s⁻¹ ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc x * s⁻¹ * t = x * (s⁻¹ * t * s) * s⁻¹ := by group
      _ = x * (x⁻¹ * t * x) * s⁻¹ := by rw [hts]
      _ = t * (x * s⁻¹) := by group
  have hyW : x * s⁻¹ ∈ normalizer (W : Set G) := mul_mem hx (inv_mem (le_normalizer hsW))
  have hWX : W ⊓ X = Q := hQ _ hW.to_inf_left (le_inf hQW hQX) inf_le_right
  have hyQ : x * s⁻¹ ∈ normalizer (Q : Set G) := by
    rw [← hWX]
    exact inf_normalizer_le_normalizer_inf ⟨hyW, hX hyC⟩
  simpa using mul_mem (hcan ⟨hyC, hyQ⟩) (hWN hsW)

theorem sylow_of_slice_of_le_normalizer [Finite G] {t : G} {X Q T S : Subgroup G}
    (hX : centralizer ({t} : Set G) ≤ normalizer (X : Set G))
    (hQ : ∃ R : Sylow 2 X, (R : Subgroup X).map X.subtype = Q)
    (htT : t ∈ T) (hQT : Q ≤ T) (hST : S ≤ T)
    (hcan : centralizer ({t} : Set G) ⊓ normalizer (Q : Set G) ≤ normalizer (T : Set G))
    (hslice : ∀ g : G, g⁻¹ * t * g ∈ normalizer (T : Set G) →
      ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hTW : T ≤ W) (hWN : W ≤ normalizer (T : Set G))
    (hWmax : ∀ W' : Subgroup G, IsPGroup 2 W' → W ≤ W' → W' ≤ normalizer (T : Set G) →
      W' = W) :
    ∃ R : Sylow 2 G, (R : Subgroup G) = W := by
  have hQX : Q ≤ X := by
    obtain ⟨R, rfl⟩ := hQ
    exact map_subtype_le _
  exact exists_sylow_eq_of_normalizer_le hW
    (normalizer_le_of_slice hX hQX (fun _ hQ' hle hle' => eq_of_le_of_sylow_map hQ hQ' hle hle')
      hcan hW (hTW htT) (hQT.trans hTW) (hST.trans hTW) hWN fun g hg => hslice g (hWN hg))
    hWmax

theorem sylow_of_slice_of_centralizer_normalizer_le [Finite G] {t : G} {L P T S : Subgroup G}
    (hLn : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hP : ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype = P)
    (hQT : P ⊔ zpowers t ≤ T) (hST : S ≤ T)
    (hcan : centralizer ({t} : Set G) ⊓ normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (T : Set G))
    (hslice : ∀ g : G, g⁻¹ * t * g ∈ normalizer (T : Set G) →
      ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hTW : T ≤ W) (hWN : W ≤ normalizer (T : Set G))
    (hWmax : ∀ W' : Subgroup G, IsPGroup 2 W' → W ≤ W' → W' ≤ normalizer (T : Set G) →
      W' = W) :
    ∃ R : Sylow 2 G, (R : Subgroup G) = W := by
  have hC : centralizer ({t} : Set G) ≤ normalizer ((zpowers t : Subgroup G) : Set G) := by
    rw [zpowers_eq_closure, ← centralizer_closure]
    exact centralizer_le_normalizer _
  exact sylow_of_slice_of_le_normalizer hLn hP (hQT (mem_sup_right (mem_zpowers t)))
    (le_sup_left.trans hQT) hST
    (fun _ hy => hcan ⟨hy.1, inf_normalizer_le_normalizer_sup _ _ ⟨hy.2, hC hy.1⟩⟩)
    hslice hW hTW hWN hWmax

theorem firstTransferData_of_isSylow {t : G} (ht : orderOf t = 2) {S W : Subgroup G}
    (hWsyl : ∃ R : Sylow 2 G, (R : Subgroup G) = W) (htW : t ∈ W) (hSW : S ≤ W)
    (hSn : (S.subgroupOf W).Normal) (hab : IsMulCommutative (W ⧸ S.subgroupOf W)) (htS : t ∉ S)
    (hslice : ∀ g : G, g⁻¹ * t * g ∈ W → ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s) :
    FirstTransferData W S t := by
  refine ⟨hWsyl, hSW, hSn, hab, htW, htS, ht, fun g hg => ?_⟩
  obtain ⟨s, hs, hgs⟩ := hslice g hg
  have hsW : s ∈ W := hSW hs
  have e : (⟨g⁻¹ * t * g, hg⟩ : W) = (⟨s, hsW⟩ : W)⁻¹ * ⟨t, htW⟩ * ⟨s, hsW⟩ := Subtype.ext hgs
  have h1 : QuotientGroup.mk' (S.subgroupOf W) (⟨s, hsW⟩ : W) = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact mem_subgroupOf.mpr hs
  rw [e, map_mul, map_mul, map_inv, h1, inv_one, one_mul, mul_one]

theorem firstTransferData_of_slice [Finite G] {t : G} (ht : orderOf t = 2)
    {L P T S : Subgroup G} (hLn : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hP : ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype = P)
    (hQT : P ⊔ zpowers t ≤ T) (hST : S ≤ T)
    (hcan : centralizer ({t} : Set G) ⊓ normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (T : Set G))
    (hslice : ∀ g : G, g⁻¹ * t * g ∈ normalizer (T : Set G) →
      ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hTW : T ≤ W) (hWN : W ≤ normalizer (T : Set G))
    (hWmax : ∀ W' : Subgroup G, IsPGroup 2 W' → W ≤ W' → W' ≤ normalizer (T : Set G) →
      W' = W)
    (hSn : (S.subgroupOf W).Normal) (hab : IsMulCommutative (W ⧸ S.subgroupOf W)) (htS : t ∉ S) :
    FirstTransferData W S t :=
  firstTransferData_of_isSylow ht
    (sylow_of_slice_of_centralizer_normalizer_le hLn hP hQT hST hcan hslice hW hTW hWN hWmax)
    (hTW (hQT (mem_sup_right (mem_zpowers t)))) (hST.trans hTW) hSn hab htS
    fun g hg => hslice g (hWN hg)

theorem not_perfect_of_slice [Finite G] [Group.IsPerfect G] {t : G} (ht : orderOf t = 2)
    {L P T S : Subgroup G} (hLn : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hP : ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype = P)
    (hQT : P ⊔ zpowers t ≤ T) (hST : S ≤ T)
    (hcan : centralizer ({t} : Set G) ⊓ normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (T : Set G))
    (hslice : ∀ g : G, g⁻¹ * t * g ∈ normalizer (T : Set G) →
      ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s)
    {W : Subgroup G} (hW : IsPGroup 2 W) (hTW : T ≤ W) (hWN : W ≤ normalizer (T : Set G))
    (hWmax : ∀ W' : Subgroup G, IsPGroup 2 W' → W ≤ W' → W' ≤ normalizer (T : Set G) →
      W' = W)
    (hSn : (S.subgroupOf W).Normal) (hab : IsMulCommutative (W ⧸ S.subgroupOf W)) (htS : t ∉ S) :
    False :=
  perfect_first_transfer_exclusion
    ⟨W, S, t, firstTransferData_of_slice ht hLn hP hQT hST hcan hslice hW hTW hWN hWmax hSn hab
      htS⟩

theorem false_of_slice [Finite G] [Group.IsPerfect G] {t : G} (ht : orderOf t = 2)
    {L P T S : Subgroup G} (hLn : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hP : ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype = P) (hT : IsPGroup 2 T)
    (hQT : P ⊔ zpowers t ≤ T) (hST : S ≤ T)
    (hcan : centralizer ({t} : Set G) ⊓ normalizer ((P ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (T : Set G))
    (hslice : ∀ g : G, g⁻¹ * t * g ∈ normalizer (T : Set G) →
      ∃ s ∈ S, g⁻¹ * t * g = s⁻¹ * t * s)
    (htS : t ∉ S)
    (hquot : ∀ W : Subgroup G, IsPGroup 2 W → T ≤ W → W ≤ normalizer (T : Set G) →
      ∃ _ : (S.subgroupOf W).Normal, IsMulCommutative (W ⧸ S.subgroupOf W)) :
    False := by
  obtain ⟨W, hW, hTW, hWN, hWmax⟩ := exists_maximal_pGroup hT (le_normalizer (H := T))
  obtain ⟨hSn, hab⟩ := hquot W hW hTW hWN
  exact not_perfect_of_slice ht hLn hP hQT hST hcan hslice hW hTW hWN hWmax hSn hab htS

end CFSG.LocalAnalysis.EvenBN.Sp4

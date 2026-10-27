module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35Core
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5CovM12
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternal
public import CFSG.GH74.Generic.S45.LSporM12Data

public section

namespace CFSG.ComponentClassification.SolMax.H35.M12

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.GSThmB
open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.M12Cover.SylowTable
open CFSG.Sporadic.Mathieu

@[expose] def letCode (k : ℕ) : List ℕ :=
  if k = 0 then [3, 1, 9, 0, 10, 11, 6, 7, 8, 2, 4, 5]
  else if k = 1 then [7, 2, 3, 1, 11, 9, 5, 8, 0, 6, 4, 10]
  else [8, 3, 1, 2, 10, 6, 9, 0, 7, 5, 11, 4]

@[expose] def genA : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 3] * List.formPerm [2, 9] * List.formPerm [4, 10] * List.formPerm [5, 11]

@[expose] def genB : Equiv.Perm (Fin 12) :=
  List.formPerm [0, 7, 8] * List.formPerm [1, 2, 3] * List.formPerm [4, 11, 10] *
    List.formPerm [5, 9, 6]

@[expose] def letPerm (k : ℕ) : Equiv.Perm (Fin 12) :=
  if k = 0 then genA else if k = 1 then genB else genB⁻¹

@[expose] def wCode (w : List ℕ) : List ℕ :=
  w.foldr (fun k c => comp (letCode k) c) (List.range 12)

@[expose] def wPerm (w : List ℕ) : Equiv.Perm (Fin 12) := (w.map letPerm).prod

@[expose] def zCode : List ℕ := [9, 7, 3, 2, 11, 10, 8, 1, 6, 0, 5, 4]

@[expose] def pow5 (c : List ℕ) : List ℕ := comp c (comp c (comp c (comp c c)))

@[expose] def gWord : List ℕ := [0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1]

@[expose] def hWord : List ℕ :=
  [2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1]

@[expose] def dCode : List ℕ := comp (wCode gWord) (wCode hWord)

theorem isCode_letter (k : ℕ) : IsCode (letCode k) (letPerm k) := by
  unfold letCode letPerm genA genB
  split_ifs
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩
  · exact ⟨rfl, by decide⟩

theorem isCode_word : ∀ w : List ℕ, IsCode (wCode w) (wPerm w)
  | [] => isCode_one
  | k :: w => by
    change IsCode (comp (letCode k) (wCode w)) (letPerm k * wPerm w)
    exact (isCode_letter k).mul (isCode_word w)

theorem isCode_z : IsCode zCode permZ := ⟨rfl, by decide +kernel⟩

theorem letPerm_mem (k : ℕ) : letPerm k ∈ NativeSporadic.M12 := by
  have hA : genA ∈ NativeSporadic.M12 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hB : genB ∈ NativeSporadic.M12 :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  unfold letPerm
  split_ifs
  · exact hA
  · exact hB
  · exact NativeSporadic.M12.inv_mem hB

theorem wPerm_mem (w : List ℕ) : wPerm w ∈ NativeSporadic.M12 :=
  list_prod_mem fun g hg => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact letPerm_mem k

theorem code_checks :
    comp (wCode gWord) zCode = comp zCode (wCode gWord) ∧
      comp (wCode hWord) zCode = comp zCode (wCode hWord) ∧
      pow5 (wCode gWord) = List.range 12 ∧ pow5 (wCode hWord) = List.range 12 ∧
      comp dCode dCode = List.range 12 ∧ dCode ≠ List.range 12 := by
  decide +kernel

theorem card_fix_dCode :
    (Finset.univ.filter fun i : Fin 12 => nth 0 dCode i = i).card = 4 := by
  decide +kernel

theorem pow5_eq_one {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ)
    (h5 : pow5 c = List.range 12) : σ ^ 5 = 1 := by
  have h1 : IsCode (pow5 c) (σ * (σ * (σ * (σ * σ)))) := h.mul (h.mul (h.mul (h.mul h)))
  rw [h5] at h1
  have h2 := h1.perm_eq isCode_one
  rw [← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem comm_z {c : List ℕ} {σ : Equiv.Perm (Fin 12)} (h : IsCode c σ)
    (hc : comp c zCode = comp zCode c) : σ * permZ = permZ * σ :=
  (h.mul isCode_z).perm_eq (hc ▸ isCode_z.mul h)

theorem gh_facts :
    wPerm gWord * permZ = permZ * wPerm gWord ∧ wPerm hWord * permZ = permZ * wPerm hWord ∧
      wPerm gWord ^ 5 = 1 ∧ wPerm hWord ^ 5 = 1 ∧
      wPerm gWord * wPerm hWord * (wPerm gWord * wPerm hWord) = 1 ∧
      wPerm gWord * wPerm hWord ≠ 1 ∧
      (Finset.univ.filter fun i : Fin 12 => (wPerm gWord * wPerm hWord) i = i).card = 4 := by
  obtain ⟨hg, hh, hg5, hh5, hd2, hd1⟩ := code_checks
  have cg := isCode_word gWord
  have ch := isCode_word hWord
  have cd : IsCode dCode (wPerm gWord * wPerm hWord) := cg.mul ch
  refine ⟨comm_z cg hg, comm_z ch hh, pow5_eq_one cg hg5, pow5_eq_one ch hh5, ?_, ?_, ?_⟩
  · have h1 := cd.mul cd
    rw [hd2] at h1
    exact h1.perm_eq isCode_one
  · intro h1
    rw [h1] at cd
    exact hd1 (cd.code_eq isCode_one)
  · refine Eq.trans (congrArg Finset.card (Finset.filter_congr fun i _ => ?_)) card_fix_dCode
    rw [cd.2 i]
    exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

theorem exists_gh : ∃ g h : Equiv.Perm (Fin 12), g ∈ NativeSporadic.M12 ∧ h ∈ NativeSporadic.M12 ∧
    g * permZ = permZ * g ∧ h * permZ = permZ * h ∧ g ^ 5 = 1 ∧ h ^ 5 = 1 ∧
    g * h * (g * h) = 1 ∧ g * h ≠ 1 ∧
    (Finset.univ.filter fun i : Fin 12 => (g * h) i = i).card = 4 :=
  ⟨wPerm gWord, wPerm hWord, wPerm_mem gWord, wPerm_mem hWord, gh_facts⟩

theorem conj_mem_centralizer {u y : NativeSporadic.M12}
    (hu : (u : Equiv.Perm (Fin 12)) * permZ = permZ * u) (y₀ : NativeSporadic.M12)
    (hy : y = y₀ * elemZ * y₀⁻¹) :
    y₀ * u * y₀⁻¹ ∈ centralizer ({y} : Set NativeSporadic.M12) := by
  rw [mem_centralizer_singleton_iff, hy]
  have h1 : u * elemZ = elemZ * u := Subtype.ext hu
  calc y₀ * u * y₀⁻¹ * (y₀ * elemZ * y₀⁻¹) = y₀ * (u * elemZ) * y₀⁻¹ := by group
    _ = y₀ * (elemZ * u) * y₀⁻¹ := by rw [h1]
    _ = y₀ * elemZ * y₀⁻¹ * (y₀ * u * y₀⁻¹) := by group

theorem false_of_inner
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (X : L) (hX2 : X * X ∈ center L)
    {Lt : Subgroup L} (huniq : ∀ y ∈ Lt, y * y = 1 → y = 1 ∨ y = t)
    (hM : CFSG.Assembly.IsComponentOf (Lt.map π)
      (centralizer ({π X} : Set NativeSporadic.M12)))
    (hMt : Cov.SmallQ (↥(Lt.map π) ⧸ center ↥(Lt.map π))) : False := by
  set x₀ := π X with hx₀def
  have hx2 : x₀ * x₀ = 1 := by
    have h1 : π (X * X) = 1 := by
      rw [← MonoidHom.mem_ker, hker, ← hZ]
      exact hX2
    rwa [map_mul] at h1
  by_cases hx1 : x₀ = 1
  · have hc : centralizer ({x₀} : Set NativeSporadic.M12) = ⊤ := by
      rw [hx1]
      exact eq_top_iff.mpr fun z _ => mem_centralizer_singleton_iff.mpr (by group)
    rw [hc] at hM
    exact Cov.false_of_top' hLq π hπ (hker.trans hZ.symm) hM hMt
      (fun q => by rw [CFSG.Sporadic.Mathieu.card_M12]; exact CovM12.ordA_one_ne_95040 q)
      (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
  have hxo : orderOf x₀ = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  rcases GH74.Generic.S45.LAlt.m12_involution_data x₀ hxo with h192 | ⟨h240, hfix0, -⟩
  · exact Cov.false_of_component_card hM hMt (N := 192) (by rw [h192])
      CovM12.not_ordA_dvd_192 (by decide)
  obtain ⟨y₀, hy₀⟩ := conj_elemZ_of_fixedCount_zero x₀ hxo hfix0
  have hcop := coprime_five_relIndex hM.1 h240 hMt
  obtain ⟨g₀, h₀, hgM, hhM, hgz, hhz, hg5, hh5, hd2, hd1, hdfix⟩ := exists_gh
  set g : NativeSporadic.M12 := ⟨g₀, hgM⟩
  set h : NativeSporadic.M12 := ⟨h₀, hhM⟩
  have hx₀ : x₀ = y₀ * elemZ * y₀⁻¹ := hy₀.symm
  have hG : y₀ * g * y₀⁻¹ ∈ Lt.map π := by
    refine mem_of_isSubnormal_of_coprime hM.2.1 hcop (conj_mem_centralizer hgz y₀ hx₀) ?_
    rw [conj_pow]
    have h1 : g ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg5)
    rw [h1, mul_one, mul_inv_cancel]
  have hH : y₀ * h * y₀⁻¹ ∈ Lt.map π := by
    refine mem_of_isSubnormal_of_coprime hM.2.1 hcop (conj_mem_centralizer hhz y₀ hx₀) ?_
    rw [conj_pow]
    have h1 : h ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hh5)
    rw [h1, mul_one, mul_inv_cancel]
  set D := y₀ * g * y₀⁻¹ * (y₀ * h * y₀⁻¹) with hDdef
  have hD : D = y₀ * (g * h) * y₀⁻¹ := by rw [hDdef]; group
  have hgh2 : g * h * (g * h) = 1 := Subtype.ext hd2
  have hgh1 : g * h ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  have hD2 : D * D = 1 := by
    rw [hD]
    calc y₀ * (g * h) * y₀⁻¹ * (y₀ * (g * h) * y₀⁻¹) = y₀ * (g * h * (g * h)) * y₀⁻¹ := by
          group
      _ = 1 := by rw [hgh2]; group
  have hD1 : D ≠ 1 := by
    intro h1
    rw [hD] at h1
    apply hgh1
    calc g * h = y₀⁻¹ * (y₀ * (g * h) * y₀⁻¹) * y₀ := by group
      _ = 1 := by rw [h1]; group
  have hDo : orderOf D = 2 := orderOf_eq_prime (by rw [sq]; exact hD2) hD1
  have hDfix : M12Cover.fixedCount D = 4 := by
    rw [hD, M12Cover.fixedCount_conj]
    exact hdfix
  obtain ⟨ℓ, hℓ, hℓD₀⟩ := (Lt.map π).mul_mem hG hH
  have hℓD : π ℓ = D := hℓD₀
  obtain ⟨-, h4, -⟩ := m12_double_cover_involution_lift_orders hLq ht hZ π hπ hker
  have hℓo : orderOf ℓ = 2 := h4 ℓ (by rw [hℓD]; exact hDo) (by rw [hℓD]; exact hDfix)
  have hℓ2 : ℓ * ℓ = 1 := by rw [← sq, ← hℓo, pow_orderOf_eq_one]
  have htk : π t = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact mem_zpowers t
  rcases huniq ℓ hℓ hℓ2 with h1 | h1
  · exact hD1 (by rw [← hℓD, h1, map_one])
  · exact hD1 (by rw [← hℓD, h1, htk])

theorem false_of_fixed
    {L : Type} [Group L] [Finite L] (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) (α : MulAut L) (hα : α * α = 1)
    (β : MulAut NativeSporadic.M12) (hβ : ∀ x, π (α x) = β (π x)) {Lt : Subgroup L}
    (hLt : ⁅Lt, Lt⁆ = Lt) (htL : t ∈ Lt) (hfix : ∀ y ∈ Lt, α y = y)
    (huniq : ∀ y ∈ Lt, y * y = 1 → y = 1 ∨ y = t)
    (hM : CFSG.Assembly.IsComponentOf (Lt.map π) (fixSub β))
    (hMt : Cov.SmallQ (↥(Lt.map π) ⧸ center ↥(Lt.map π))) : False := by
  by_cases hinn : ∃ X : L, ∀ y, α y = X * y * X⁻¹
  · obtain ⟨X, hX⟩ := hinn
    rw [Cov.fixSub_eq_of_inner π hπ α β hβ X hX] at hM
    exact false_of_inner hLq ht hZ π hπ hker X (Cov.mul_self_mem_center_of_inner α hα X hX)
      huniq hM hMt
  · push Not at hinn
    exact false_of_outer (s := .M12) hLq ht hZ π hπ hker α hα
      (fun n hn => (hinn n).elim fun y hy => hy (hn y)) (MulEquiv.refl NativeSporadic.M12)
      ctss_m12_central_double_cover_external_data_from_fusion_and_section hLt htL hfix

end CFSG.ComponentClassification.SolMax.H35.M12

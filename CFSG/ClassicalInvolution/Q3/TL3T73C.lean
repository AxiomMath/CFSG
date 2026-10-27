module

public import CFSG.ClassicalInvolution.Q3.TL3T73
public import CFSG.ClassicalInvolution.Q3.TL3T73B
public import CFSG.ClassicalInvolution.Q3.TL4AECover
public import CFSG.ClassicalInvolution.Q3.TL4AECoverG

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

section StarOrTop

open Finset

private theorem smallInterSubsetOrSubsetUnion {α : Type*} [DecidableEq α] {r : ℕ}
    {a b e : Finset α} (he : e.card = r) (hab : (a ∩ b).card + 1 = r)
    (hea : r ≤ (e ∩ a).card + 1) (heb : r ≤ (e ∩ b).card + 1) :
    a ∩ b ⊆ e ∨ e ⊆ a ∪ b := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  obtain ⟨t, ht, hte⟩ := not_subset.mp h
  have h₁ : (e ∩ (a ∩ b)).card < (a ∩ b).card :=
    card_lt_card ⟨inter_subset_right, fun hs => hte (mem_inter.mp (hs ht)).1⟩
  have h₂ := card_union_add_card_inter (e ∩ a) (e ∩ b)
  rw [← inter_union_distrib_left, ← inter_inter_distrib_left] at h₂
  exact inter_eq_left.mp (eq_of_subset_of_card_le inter_subset_left (by omega))

private theorem smallStarOrTop {κ α : Type*} [DecidableEq α] {r : ℕ} (W : Finset κ)
    (hW : 1 < W.card) (A : κ → Finset α) (hA : ∀ x ∈ W, (A x).card = r)
    (hAA : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → (A x ∩ A y).card + 1 = r) :
    (∃ R : Finset α, R.card + 1 = r ∧ ∀ x ∈ W, R ⊆ A x) ∨
      ∃ Z : Finset α, Z.card = r + 1 ∧ ∀ x ∈ W, A x ⊆ Z := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := one_lt_card.mp hW
  have hI := hAA x₀ hx₀ y₀ hy₀ hxy
  have hge : ∀ x ∈ W, ∀ y ∈ W, r ≤ (A x ∩ A y).card + 1 := by
    intro x hx y hy
    by_cases hxy : x = y
    · rw [hxy, inter_self, hA y hy]
      omega
    · exact (hAA x hx y hy hxy).ge
  by_cases hstar : ∀ x ∈ W, A x₀ ∩ A y₀ ⊆ A x
  · exact Or.inl ⟨_, hI, hstar⟩
  right
  obtain ⟨d, hd, hdI⟩ : ∃ d ∈ W, ¬A x₀ ∩ A y₀ ⊆ A d := by
    by_contra hcon
    exact hstar fun d hd => Classical.byContradiction fun hd' => hcon ⟨d, hd, hd'⟩
  have hdich : ∀ e ∈ W, A x₀ ∩ A y₀ ⊆ A e ∨ A e ⊆ A x₀ ∪ A y₀ := fun e he =>
    smallInterSubsetOrSubsetUnion (hA e he) hI (hge e he x₀ hx₀) (hge e he y₀ hy₀)
  have hdZ : A d ⊆ A x₀ ∪ A y₀ := (hdich d hd).resolve_left hdI
  refine ⟨A x₀ ∪ A y₀, ?_, fun e he => ?_⟩
  · have := card_union_add_card_inter (A x₀) (A y₀)
    rw [hA x₀ hx₀, hA y₀ hy₀] at this
    omega
  rcases hdich e he with hIe | hZe
  · by_contra heZ
    have h₁ : A e ∩ (A x₀ ∪ A y₀) = A x₀ ∩ A y₀ := by
      refine (eq_of_subset_of_card_le (subset_inter hIe inter_subset_union) ?_).symm
      have := card_lt_card (⟨inter_subset_left, fun h => heZ fun x hx => (mem_inter.mp (h hx)).2⟩ :
        A e ∩ (A x₀ ∪ A y₀) ⊂ A e)
      rw [hA e he] at this
      omega
    have h₂ : (A e ∩ A d).card < (A x₀ ∩ A y₀).card :=
      calc (A e ∩ A d).card ≤ (A x₀ ∩ A y₀ ∩ A d).card := card_le_card fun x hx => by
            have hx' := mem_inter.mp hx
            have : x ∈ A e ∩ (A x₀ ∪ A y₀) := mem_inter.mpr ⟨hx'.1, hdZ hx'.2⟩
            rw [h₁] at this
            exact mem_inter.mpr ⟨this, hx'.2⟩
        _ < (A x₀ ∩ A y₀).card :=
          card_lt_card ⟨inter_subset_left, fun h => hdI fun x hx => (mem_inter.mp (h hx)).2⟩
    have := hge e he d hd
    omega
  · exact hZe

private theorem smallExistsEqErase {α : Type*} [DecidableEq α] {Z V : Finset α} {n : ℕ}
    (hZ : Z.card = n + 1) (hV : V.card = n) (hVZ : V ⊆ Z) : ∃ p ∈ Z, V = Z.erase p := by
  obtain ⟨p, hp⟩ := card_eq_one.mp (show (Z \ V).card = 1 by
    have := card_sdiff_of_subset hVZ
    omega)
  have hpm : p ∈ Z \ V := by rw [hp]; exact mem_singleton_self p
  refine ⟨p, (mem_sdiff.mp hpm).1, ?_⟩
  ext y
  constructor
  · intro hy
    refine mem_erase.mpr ⟨fun h => (mem_sdiff.mp hpm).2 (h ▸ hy), hVZ hy⟩
  · intro hy
    obtain ⟨hne, hyZ⟩ := mem_erase.mp hy
    by_contra hyV
    have : y ∈ Z \ V := mem_sdiff.mpr ⟨hyZ, hyV⟩
    rw [hp, mem_singleton] at this
    exact hne this

end StarOrTop

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE

private theorem kleinOn_le_alternatingGroup {n : ℕ} (A : Finset (Fin n)) :
    kleinOn A ≤ alternatingGroup (Fin n) := fun _ hσ =>
  Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_kleinOn hσ)

private theorem exists_emb_core {j k : ℕ} (hj5 : 5 ≤ j) (hj7 : j ≤ 7) (hk : k ≤ j + 2)
    (ρ : alternatingGroup (Fin j) →* Equiv.Perm (Fin k)) (hρ : Function.Injective ρ)
    (f : Finset (Fin j) → Finset (Fin k))
    (hf4 : ∀ α : Finset (Fin j), α.card = 4 → (f α).card = 4)
    (hK : ∀ α : Finset (Fin j), α.card = 4 →
      ((kleinOn α).subgroupOf (alternatingGroup (Fin j))).map ρ = kleinOn (f α)) :
    ∃ ι : Fin j ↪ Fin k, ∀ α : Finset (Fin j), α.card = 4 → f α = α.map ι := by
  have hfwd : ∀ α : Finset (Fin j), α.card = 4 → ∀ x : alternatingGroup (Fin j),
      (x : Equiv.Perm (Fin j)) ∈ kleinOn α → ρ x ∈ kleinOn (f α) := by
    intro α hα x hx
    rw [← hK α hα]
    exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr hx)
  have hbwd : ∀ α : Finset (Fin j), α.card = 4 → ∀ y ∈ kleinOn (f α),
      ∃ x : alternatingGroup (Fin j), (x : Equiv.Perm (Fin j)) ∈ kleinOn α ∧ ρ x = y := by
    intro α hα y hy
    rw [← hK α hα] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, rfl⟩
  have hord : ∀ x : alternatingGroup (Fin j), orderOf (ρ x) = orderOf (x : Equiv.Perm (Fin j)) :=
    fun x => by rw [orderOf_injective ρ hρ x, Subgroup.orderOf_coe]
  have hfinj : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 → f α = f β → α = β := by
    intro α β hα hβ h
    have h1 : (kleinOn α).subgroupOf (alternatingGroup (Fin j)) =
        (kleinOn β).subgroupOf (alternatingGroup (Fin j)) :=
      Subgroup.map_injective hρ (by rw [hK α hα, hK β hβ, h])
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (kleinOn_le_alternatingGroup α),
      inf_of_le_left (kleinOn_le_alternatingGroup β)] at h1
    exact eq_of_kleinOn_eq hα hβ h1
  have hD1 : ∀ α β : Finset (Fin j), α.card = 4 → β.card = 4 →
      ((α ∩ β).card = 3 ↔ (f α ∩ f β).card = 3) := by
    intro α β hα hβ
    rw [← exists_five_dvd_orderOf_iff hα hβ,
      ← exists_five_dvd_orderOf_iff (hf4 α hα) (hf4 β hβ)]
    constructor
    · rintro ⟨x, hx, y, hy, h5⟩
      have hxa : x ∈ alternatingGroup (Fin j) :=
        Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_kleinOn hx)
      have hya : y ∈ alternatingGroup (Fin j) :=
        Equiv.Perm.mem_alternatingGroup.mpr (sign_of_mem_kleinOn hy)
      refine ⟨ρ ⟨x, hxa⟩, hfwd α hα ⟨x, hxa⟩ hx, ρ ⟨y, hya⟩, hfwd β hβ ⟨y, hya⟩ hy, ?_⟩
      rw [← map_mul, hord]
      exact h5
    · rintro ⟨x', hx', y', hy', h5⟩
      obtain ⟨x, hx, rfl⟩ := hbwd α hα x' hx'
      obtain ⟨y, hy, rfl⟩ := hbwd β hβ y' hy'
      refine ⟨x, hx, y, hy, ?_⟩
      rw [← map_mul, hord] at h5
      exact h5
  have htop : ∀ S : Finset (Fin j), S.card = 5 →
      ∃ U : Finset (Fin k), U.card = 5 ∧ ∀ α ⊆ S, α.card = 4 → f α ⊆ U := by
    intro S hS
    have hSe : ∀ x ∈ S, (S.erase x).card = 4 := fun x hx => by
      rw [Finset.card_erase_of_mem hx, hS]
    have herase : ∀ x ∈ S, ∀ y ∈ S, S.erase x = S.erase y → x = y := by
      intro x hx y hy h
      by_contra hne
      have h1 : x ∈ S.erase y := Finset.mem_erase.mpr ⟨hne, hx⟩
      rw [← h] at h1
      exact (Finset.mem_erase.mp h1).1 rfl
    have hAA : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        (f (S.erase x) ∩ f (S.erase y)).card + 1 = 4 := by
      intro x hx y hy hxy
      have h3 : (S.erase x ∩ S.erase y).card = 3 := by
        have e : S.erase x ∩ S.erase y = (S.erase x).erase y := by
          ext z
          simp only [Finset.mem_inter, Finset.mem_erase]
          tauto
        have h4 := Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩ : y ∈ S.erase x)
        have h5 := hSe x hx
        rw [e]
        omega
      have := (hD1 _ _ (hSe x hx) (hSe y hy)).mp h3
      omega
    rcases smallStarOrTop S (by omega) (fun x => f (S.erase x))
      (fun x hx => hf4 _ (hSe x hx)) hAA with ⟨R, hR, hRsub⟩ | ⟨Z, hZ, hZsub⟩
    ·
      exfalso
      obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
        Finset.two_lt_card.mp (show 2 < S.card by omega)
      have hR3 : R.card = 3 := by omega
      have hins : ∀ x ∈ S, ∃ y ∉ R, insert y R = f (S.erase x) := fun x hx =>
        Finset.exists_eq_insert_iff.mpr ⟨hRsub x hx, by rw [hf4 _ (hSe x hx)]; exact hR⟩
      obtain ⟨xa, hxa, hea⟩ := hins a ha
      obtain ⟨xb, hxb, heb⟩ := hins b hb
      obtain ⟨xc, hxc, hec⟩ := hins c hc
      have hne : ∀ {x y : Fin j} {u v : Fin k}, x ∈ S → y ∈ S → x ≠ y →
          insert u R = f (S.erase x) → insert v R = f (S.erase y) → u ≠ v := by
        intro x y u v hx hy hxy hu hv huv
        subst huv
        exact hxy (herase x hx y hy (hfinj _ _ (hSe x hx) (hSe y hy) (hu.symm.trans hv)))
      obtain ⟨x, hx, y, hy, w, hw, h4⟩ := exists_orderOf_eq_four_star hR3 hxa hxb hxc
        (hne ha hb hab hea heb) (hne ha hc hac hea hec) (hne hb hc hbc heb hec)
      rw [hea] at hx
      rw [heb] at hy
      rw [hec] at hw
      obtain ⟨x', hx', rfl⟩ := hbwd _ (hSe a ha) x hx
      obtain ⟨y', hy', rfl⟩ := hbwd _ (hSe b hb) y hy
      obtain ⟨w', hw', rfl⟩ := hbwd _ (hSe c hc) w hw
      rw [← map_mul, ← map_mul, hord] at h4
      have hsign : Equiv.Perm.sign ((x' * y' * w' : alternatingGroup (Fin j)) :
          Equiv.Perm (Fin j)) = 1 :=
        Equiv.Perm.mem_alternatingGroup.mp (x' * y' * w').2
      have hfix : ∀ z ∉ S, ((x' * y' * w' : alternatingGroup (Fin j)) :
          Equiv.Perm (Fin j)) z = z := by
        intro z hz
        have hz1 : z ∉ S.erase a := fun h => hz (Finset.mem_of_mem_erase h)
        have hz2 : z ∉ S.erase b := fun h => hz (Finset.mem_of_mem_erase h)
        have hz3 : z ∉ S.erase c := fun h => hz (Finset.mem_of_mem_erase h)
        show (x' : Equiv.Perm (Fin j)) ((y' : Equiv.Perm (Fin j)) ((w' : Equiv.Perm (Fin j)) z)) = z
        rw [fix_of_mem_kleinOn hw' hz3, fix_of_mem_kleinOn hy' hz2, fix_of_mem_kleinOn hx' hz1]
      rcases orderOf_of_support_five hsign hS hfix with h | h | h | h <;> omega
    ·
      refine ⟨Z, hZ, fun α hαS hα4 => ?_⟩
      obtain ⟨x, hx, rfl⟩ := smallExistsEqErase (n := 4) (by omega) hα4 hαS
      exact hZsub x hx
  exact Johnson.exists_emb_of_tops hj5 hj7 hk f hf4 hfinj htop

section Parts

variable {G : Type} [Group G] {P P' : Set (Subgroup G)}

private noncomputable def smallPsiHom (hle : pSpan P ≤ pSpan P') {k : ℕ} (I' : AEIdent P' k) :
    ↥(pSpan P) →* Equiv.Perm (Fin k) :=
  (permQ k).comp (I'.φ.comp (Subgroup.inclusion hle))

private theorem map_inclusion_subgroupOf {H H' : Subgroup G} (hle : H ≤ H') {M : Subgroup G}
    (hM : M ≤ H) : (M.subgroupOf H).map (Subgroup.inclusion hle) = M.subgroupOf H' := by
  ext ⟨y, hy'⟩
  constructor
  · rintro ⟨⟨z, hz⟩, hzM, he⟩
    have hzy : z = y := congrArg Subtype.val he
    subst hzy
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hzM)
  · intro hyM
    have hyM' : y ∈ M := Subgroup.mem_subgroupOf.mp hyM
    exact ⟨⟨y, hM hyM'⟩, Subgroup.mem_subgroupOf.mpr hyM', rfl⟩

private theorem map_smallPsiHom_eq (hle : pSpan P ≤ pSpan P') {k : ℕ} (I' : AEIdent P' k)
    {M : Subgroup G} (hM : M ≤ pSpan P) {β : Finset (Fin k)} {hβ : β.card = 4} {d : Bool}
    (hlab : (M.subgroupOf (pSpan P')).map I'.φ = memBar β hβ d) :
    (M.subgroupOf (pSpan P)).map (smallPsiHom hle I') = kleinOn β := by
  rw [smallPsiHom, ← Subgroup.map_map, ← Subgroup.map_map, map_inclusion_subgroupOf hle hM, hlab,
    map_permQ_memBar]

private theorem map_permHom_eq {k : ℕ} (I : AEIdent P k) {M : Subgroup G} {α : Finset (Fin k)}
    {hα : α.card = 4} {b : Bool} (hlab : (M.subgroupOf (pSpan P)).map I.φ = memBar α hα b) :
    (M.subgroupOf (pSpan P)).map (TL4.AECov.permHom I) =
      (kleinOn α).subgroupOf (alternatingGroup (Fin k)) := by
  have hcomp : (alternatingGroup (Fin k)).subtype.comp (TL4.AECov.permHom I) =
      (permQ k).comp I.φ := MonoidHom.ext fun x => rfl
  refine Subgroup.map_injective (alternatingGroup (Fin k)).subtype_injective ?_
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hlab, map_permQ_memBar,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (kleinOn_le_alternatingGroup α)]

private theorem ker_permHom_le_zSpan' [Finite G] {k : ℕ} (I : AEIdent P k) (hk : 5 ≤ k)
    (hH : TL4.AECoverHyp I) : (TL4.AECov.permHom I).ker ≤ TL4.AECov.zSpan P := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u := fun L hL L' hL' u u' hu hu' =>
    TL4.AECov.comm_of_isUniqueInvolution I hk hH.card hH.conj_mem hH.label_inj hH.twin_z hL hL'
      hu hu'
  exact TL4.AECov.ker_permHom_le_zSpan I (by omega) hH.card hH.conj_mem hH.label_inj hH.ker_two
    (TL4.AECov.zSpan_normal hH.conj_mem) (TL4.AECov.zSpan_elem hcomm)

private theorem zSpan_le_ker_smallPsiHom [Finite G] (hPP : P ⊆ P') (hle : pSpan P ≤ pSpan P')
    {k : ℕ} (hk : 5 ≤ k) (I' : AEIdent P' k) (h8 : ∀ L ∈ P, Nat.card ↥L = 8) :
    TL4.AECov.zSpan P ≤ (smallPsiHom hle I').ker := by
  rw [TL4.AECov.zSpan, Subgroup.closure_le]
  rintro x ⟨L, hL, hxL⟩
  obtain ⟨β, h', b', hlab'⟩ := I'.label L (hPP hL)
  have hz := I'.map_eq_zBar hk (hPP hL) (h8 L hL) hlab' hxL
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  show permQ k (I'.φ ⟨(x : G), hle x.2⟩) = 1
  rw [show (⟨(x : G), hle x.2⟩ : ↥(pSpan P')) = ⟨(x : G), le_pSpan (hPP hL) hxL.mem⟩ from rfl, hz,
    zBar, permQ_mkQ, zOf_perm]

end Parts

variable {G : Type} [Group G]

end CFSG.ClassicalInvolution.Q3.TC.Thin

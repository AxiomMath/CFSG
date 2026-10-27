module

public import CFSG.LocalAnalysis.SectionRank.LargeRee.Weyl

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  ReeTag

section Roots

variable {τ : Tag}

theorem height_inv_smul_pos_of_length_mul
    {z w : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (z * w) =
      (coxeterSystem τ).length z + (coxeterSystem τ).length w)
    {α : Root τ} (hα : 0 < height α.1) (hzα : height (z • α).1 < 0) :
    0 < height (w⁻¹ • α).1 := by
  rcases IsRoot.height_pos_or_neg (w⁻¹ • α).2 with h | h
  · exact h
  ·
    have hβ : 0 < height (-(w⁻¹ • α)).1 := by
      rw [coe_neg_root, height_neg]
      omega
    have hwβ : w • -(w⁻¹ • α) = -α := by rw [smul_neg_root, smul_inv_smul]
    have h1 := height_mul_smul_neg hlen hβ (by rw [hwβ, coe_neg_root, height_neg]; omega)
    rw [mul_smul, hwβ, smul_neg_root, coe_neg_root, height_neg] at h1
    omega

end Roots

section Ambient

variable {τ : Tag} {K : Type} [Field K] [Finite K]

variable (τ K) in
theorem Uplus_le_U
    (w : WeylGroup τ) : Uplus τ K w ≤ (nativeData τ K).U :=
  biSup_mono fun _ hα => hα.1

theorem eq_of_mul_eq_mul_of_mem_Uplus_of_mem_Uminus
    {w : WeylGroup τ}
    {v v' x x' : adjointGroup τ K} (hv : v ∈ Uplus τ K w) (hv' : v' ∈ Uplus τ K w)
    (hx : x ∈ Uminus τ K w) (hx' : x' ∈ Uminus τ K w) (h : v * x = v' * x') :
    v = v' ∧ x = x' := by
  have e : v'⁻¹ * v = x' * x⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h, mul_inv_cancel_right]
  have hm : v'⁻¹ * v ∈ Uplus τ K w ⊓ Uminus τ K w :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hv') hv, by rw [e]; exact mul_mem hx' (inv_mem hx)⟩
  rw [Uplus_inf_Uminus, Subgroup.mem_bot, inv_mul_eq_one] at hm
  subst hm
  exact ⟨rfl, mul_left_cancel h⟩

theorem nrep_conj_mem_Uplus_of_mul_self
    {w : WeylGroup τ} (hw : w * w = 1)
    {v : adjointGroup τ K} (hv : v ∈ Uplus τ K w) :
    nrep τ K w * v * (nrep τ K w)⁻¹ ∈ Uplus τ K w :=
  RootGroupData.conj_mem_iSup_of_smul (D := nativeData τ K)
    ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩
    (S := fun α => 0 < height α.1 ∧ 0 < height (w • α).1)
    (T := fun α => 0 < height α.1 ∧ 0 < height (w • α).1) (fun α hα => by
      change 0 < height (weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ • α).1 ∧
        0 < height (w • weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩ • α).1
      rw [weylHom_nrep, ← mul_smul, hw, one_smul]
      exact ⟨hα.2, hα.1⟩) hv

theorem inv_nrep_conj_mem_Uplus_of_mul_self
    {w : WeylGroup τ} (hw : w * w = 1)
    {v : adjointGroup τ K} (hv : v ∈ Uplus τ K w) :
    (nrep τ K w)⁻¹ * v * nrep τ K w ∈ Uplus τ K w := by
  have h := RootGroupData.conj_mem_iSup_of_smul (D := nativeData τ K)
    (⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ : monomialGroup τ K)
    (S := fun α => 0 < height α.1 ∧ 0 < height (w • α).1)
    (T := fun α => 0 < height α.1 ∧ 0 < height (w • α).1) (fun α hα => by
      change 0 < height (weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ • α).1 ∧
        0 < height (w • weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ • α).1
      rw [map_inv, weylHom_nrep, inv_eq_of_mul_eq_one_right hw, ← mul_smul, hw, one_smul]
      exact ⟨hα.2, hα.1⟩) hv
  rwa [Subgroup.coe_inv, inv_inv] at h

theorem inv_nrep_conj_mem_U_of_mem_Uminus
    {z w : WeylGroup τ}
    (hlen : (coxeterSystem τ).length (z * w) =
      (coxeterSystem τ).length z + (coxeterSystem τ).length w)
    {x : adjointGroup τ K} (hx : x ∈ Uminus τ K z) :
    (nrep τ K w)⁻¹ * x * nrep τ K w ∈ (nativeData τ K).U := by
  have h := RootGroupData.conj_mem_iSup_of_smul (D := nativeData τ K)
    (⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ : monomialGroup τ K)
    (S := fun α => 0 < height α.1 ∧ height (z • α).1 < 0)
    (T := fun α => (rootCombinatorics τ).pos α) (fun α hα => by
      change 0 < height (weylHom τ K ⟨nrep τ K w, nrep_mem_monomialGroup τ K w⟩⁻¹ • α).1
      rw [map_inv, weylHom_nrep]
      exact height_inv_smul_pos_of_length_mul hlen hα.1 hα.2) hx
  rwa [Subgroup.coe_inv, inv_inv] at h

end Ambient

section Ree

variable {t : ReeTag} {K : Type} [Field K] [Finite K] [CharP K t.prime] {a : ℕ}

variable (a) in
theorem reeAut_mem_Uplus
    (w : WeylGroup t.tag) {u : adjointGroup t.tag K}
    (hu : u ∈ Uplus t.tag K w) : t.reeAut K a u ∈ Uplus t.tag K (t.weylPerm w) := by
  have hle : Uplus t.tag K w ≤
      (Uplus t.tag K (t.weylPerm w)).comap (t.reeAut K a).toMonoidHom :=
    iSup₂_le fun α hα _ hx => mem_Uplus_of_mem_X ((height_dualRoot_pos_iff α.2).2 hα.1)
      (by rw [← dualRootOf_smul]; exact (height_dualRoot_pos_iff (w • α).2).2 hα.2)
      (reeAut_mem_X a hx)
  exact hle hu

theorem exists_mem_Uplus_mem_Uminus_of_mem_reeFixed
    {w : WeylGroup t.tag}
    (hw : w ∈ t.relWeylRee) {u : adjointGroup t.tag K} (hu : u ∈ (nativeData t.tag K).U)
    (huF : u ∈ reeFixed t K a) :
    ∃ v ∈ Uplus t.tag K w, v ∈ reeFixed t K a ∧
      ∃ x ∈ Uminus t.tag K w, x ∈ reeFixed t K a ∧ u = v * x := by
  obtain ⟨v, hv, x, hx, rfl⟩ := exists_mem_Uplus_mem_Uminus w hu
  have hδ : t.weylPerm w = w := (mem_relWeylRee t).1 hw
  have hFv := reeAut_mem_Uplus a w hv
  have hFx := reeAut_mem_Uminus a w hx
  rw [hδ] at hFv hFx
  have h : t.reeAut K a v * t.reeAut K a x = v * x := by
    rw [← map_mul]
    exact (mem_reeFixed t K a).1 huF
  obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_of_mem_Uplus_of_mem_Uminus hFv hv hFx hx h
  exact ⟨v, hv, h1, x, hx, h2, rfl⟩

variable (t K a) in
noncomputable abbrev UplusFixed
    (w : WeylGroup t.tag) : Subgroup (reeFixed t K a) :=
  (Uplus t.tag K w).comap (reeFixed t K a).subtype

variable (t K a) in
noncomputable abbrev UminusFixed
    (w : WeylGroup t.tag) : Subgroup (reeFixed t K a) :=
  (Uminus t.tag K w).comap (reeFixed t K a).subtype

theorem UplusFixed_le_reeUnipPart
    (w : WeylGroup t.tag) :
    UplusFixed t K a w ≤ reeUnipPart t K a := fun _ h =>
  Uplus_le_U t.tag K w h

theorem UminusFixed_le_reeUnipPart
    (w : WeylGroup t.tag) :
    UminusFixed t K a w ≤ reeUnipPart t K a := fun _ h =>
  Uminus_le_U t.tag K w h

theorem UplusFixed_le_reeBorelPart
    (w : WeylGroup t.tag) :
    UplusFixed t K a w ≤ reeBorelPart t K a := fun _ h =>
  (nativeData t.tag K).U_le_B (Uplus_le_U t.tag K w h)

theorem UminusFixed_le_reeBorelPart
    (w : WeylGroup t.tag) :
    UminusFixed t K a w ≤ reeBorelPart t K a := fun _ h =>
  (nativeData t.tag K).U_le_B (Uminus_le_U t.tag K w h)

theorem UplusFixed_inf_UminusFixed
    (w : WeylGroup t.tag) :
    UplusFixed t K a w ⊓ UminusFixed t K a w = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hp, hm⟩
  have h : (x : adjointGroup t.tag K) ∈ Uplus t.tag K w ⊓ Uminus t.tag K w := ⟨hp, hm⟩
  rw [Uplus_inf_Uminus, Subgroup.mem_bot] at h
  exact (Subgroup.mem_bot).2 (Subtype.ext h)

theorem exists_mem_UplusFixed_mem_UminusFixed
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    {u : reeFixed t K a} (hu : u ∈ reeUnipPart t K a) :
    ∃ v ∈ UplusFixed t K a w, ∃ x ∈ UminusFixed t K a w, u = v * x := by
  obtain ⟨v, hv, hvF, x, hx, hxF, h⟩ := exists_mem_Uplus_mem_Uminus_of_mem_reeFixed hw hu u.2
  exact ⟨⟨v, hvF⟩, hv, ⟨x, hxF⟩, hx, Subtype.ext h⟩

theorem nrepFixed_conj_mem_UplusFixed
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (hww : w * w = 1) {v : reeFixed t K a} (hv : v ∈ UplusFixed t K a w) :
    nrepFixed t K a hw * v * (nrepFixed t K a hw)⁻¹ ∈ UplusFixed t K a w :=
  nrep_conj_mem_Uplus_of_mul_self hww hv

theorem inv_nrepFixed_conj_mem_UplusFixed
    {w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (hww : w * w = 1) {v : reeFixed t K a} (hv : v ∈ UplusFixed t K a w) :
    (nrepFixed t K a hw)⁻¹ * v * nrepFixed t K a hw ∈ UplusFixed t K a w :=
  inv_nrep_conj_mem_Uplus_of_mul_self hww hv

theorem inv_nrepFixed_conj_mem_reeUnipPart
    {z w : WeylGroup t.tag} (hw : w ∈ t.relWeylRee)
    (hlen : (coxeterSystem t.tag).length (z * w) =
      (coxeterSystem t.tag).length z + (coxeterSystem t.tag).length w)
    {x : reeFixed t K a} (hx : x ∈ UminusFixed t K a z) :
    (nrepFixed t K a hw)⁻¹ * x * nrepFixed t K a hw ∈ reeUnipPart t K a :=
  inv_nrep_conj_mem_U_of_mem_Uminus hlen hx

end Ree

section F4

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

theorem exists_mem_UplusFixed_blockGen_mem_UminusFixed
    (i : Fin 2)
    {u : reeFixed ReeTag.F4 K a} (hu : u ∈ reeUnipPart ReeTag.F4 K a) :
    ∃ v ∈ UplusFixed ReeTag.F4 K a (blockGen i),
      ∃ x ∈ UminusFixed ReeTag.F4 K a (blockGen i), u = v * x :=
  exists_mem_UplusFixed_mem_UminusFixed (blockGen i).2 hu

theorem relNrepHom_blockGen_conj_mem_UplusFixed
    (i : Fin 2) {v : reeFixed ReeTag.F4 K a}
    (hv : v ∈ UplusFixed ReeTag.F4 K a (blockGen i)) :
    relNrepHom K a (blockGen i) * v * (relNrepHom K a (blockGen i))⁻¹ ∈
      UplusFixed ReeTag.F4 K a (blockGen i) :=
  nrepFixed_conj_mem_UplusFixed (blockGen i).2 (ReeTag.F4.blockElt_mul_self (blockIdx i)) hv

theorem inv_relNrepHom_conj_mem_reeUnipPart
    (i : Fin 2) (w : ReeTag.F4.relWeylRee)
    (hlen : (coxeterSystem ReeTag.F4.tag).length ((blockGen i * w : ReeTag.F4.relWeylRee) :
        WeylGroup ReeTag.F4.tag) =
      (coxeterSystem ReeTag.F4.tag).length (blockGen i : WeylGroup ReeTag.F4.tag) +
        (coxeterSystem ReeTag.F4.tag).length (w : WeylGroup ReeTag.F4.tag))
    {x : reeFixed ReeTag.F4 K a} (hx : x ∈ UminusFixed ReeTag.F4 K a (blockGen i)) :
    (relNrepHom K a w)⁻¹ * x * relNrepHom K a w ∈ reeUnipPart ReeTag.F4 K a :=
  inv_nrepFixed_conj_mem_reeUnipPart w.2 hlen hx

end F4

end CFSG.SectionRank.LargeRee

module

public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2SwapUniquePair

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.SeitzQ2 (SwapParam AgreeOn FlipOn TriangleClosure TreeEdge
  SwapPairExclusion)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Twist

variable {G : Type*} [Group G] {t : G} {D : Subgroup G}

theorem injective_flip_Ψ (P : SwapParam t D) (h : Function.Injective P.Ψ) :
    Function.Injective P.flip.Ψ := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ hxy
  rw [P.flip_Ψ, P.flip_Ψ] at hxy
  have h1 := h hxy
  simp only [Prod.mk.injEq] at h1
  rw [h1.1, h1.2]

theorem range_flip_Ψ (P : SwapParam t D) : P.flip.Ψ.range = P.Ψ.range := by
  ext z
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact ⟨(y, x), (P.flip_Ψ x y).symm⟩
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact ⟨(y, x), P.flip_Ψ y x⟩

theorem injective_twist_Ψ (s : ℤˣ) (P : SwapParam t D) (h : Function.Injective P.Ψ) :
    Function.Injective (P.twist s).Ψ := by
  classical
  unfold SwapParam.twist
  split_ifs
  · exact h
  · exact injective_flip_Ψ P h

theorem range_twist_Ψ (s : ℤˣ) (P : SwapParam t D) :
    (P.twist s).Ψ.range = P.Ψ.range := by
  classical
  unfold SwapParam.twist
  split_ifs
  · rfl
  · exact range_flip_Ψ P

end Twist

section Star

variable {G : Type*} [Group G] {t : G}

theorem exists_coherent_star (ht2 : t * t = 1) {ι : Type*} {D : ι → Subgroup G}
    (P : ∀ a, SwapParam t (D a)) (O : ι → ι → Subgroup G) (hO : ∀ a b, O b a = O a b)
    (hdich : ∀ a b, a ≠ b → AgreeOn (P a) (P b) (O a b) ∨ FlipOn (P a) (P b) (O a b)) (o : ι)
    (hdet : ∀ k l, k ≠ o → l ≠ o → k ≠ l → ∃ x ∈ O o k, x ∈ O o l ∧ x ∈ O k l ∧
      ∃ hx : x ∈ D k, (⟨x, hx⟩ : D k) ∉ center (D k)) :
    ∃ σ : ι → ℤˣ, ∀ a b, a ≠ b → AgreeOn ((P a).twist (σ a)) ((P b).twist (σ b)) (O a b) := by
  classical
  set p : ι → ι := fun _ => o with hp
  set d : ι → ℕ := fun a => if a = o then 0 else 1 with hd
  set T : ι → ι → ι → Prop := fun a b c => b = o ∧ a ≠ o ∧ c ≠ o ∧ a ≠ c with hT
  have hedge : ∀ a, a ≠ o → TriangleClosure (TreeEdge p d) T a o := by
    intro a ha
    refine .base ⟨rfl, ?_⟩
    simp [hd, ha]
  have hclos : ∀ a b, a ≠ b → TriangleClosure (TreeEdge p d) T a b := by
    intro a b hab
    by_cases ha : a = o
    · subst ha
      exact .symm (hedge b (Ne.symm hab))
    · by_cases hb : b = o
      · subst hb
        exact hedge a ha
      · exact .tri ⟨rfl, ha, hb, hab⟩ (hedge a ha) (.symm (hedge b hb))
  obtain ⟨σ, hσ⟩ := SeitzQ2.exists_coherent_swapParam ht2 P O hO p d T
    (fun a b _ => by
      by_cases hab : a = b
      · subst hab
        exact .inl (AgreeOn.refl _ _)
      · exact hdich a b hab)
    (fun a b c habc => by
      obtain ⟨rfl, ha, hc, hac⟩ := habc
      obtain ⟨x, hx1, hx2, hx3, hxD, hxZ⟩ := hdet a c ha hc hac
      exact ⟨x, by rw [hO]; exact hx1, hx2, hx3, (P a).lft_ne_conj_lft hxD hxZ⟩)
  exact ⟨σ, fun a b hab => hσ a b (hclos a b hab)⟩

end Star

section Factors

variable {G : Type*} [Group G] {t : G}

theorem fst_sup_of_le {D : Subgroup G} (P : SwapParam t D) {A B : Subgroup G} (hA : A ≤ D)
    (hB : B ≤ D) : P.fst (A ⊔ B) = P.fst A ⊔ P.fst B := by
  rw [SwapParam.fst, SwapParam.fst, SwapParam.fst, Subgroup.subgroupOf_sup hA hB,
    Subgroup.map_sup]

theorem fst_mono_of_le {D : Subgroup G} (P : SwapParam t D) {A B : Subgroup G}
    (h : A ≤ B) : P.fst A ≤ P.fst B :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem le_centralizer_sup_of_le {H A B : Subgroup G} (hA : H ≤ centralizer (A : Set G))
    (hB : H ≤ centralizer (B : Set G)) : H ≤ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← le_centralizer_iff] at hA hB ⊢
  exact sup_le hA hB

theorem map_conj_sup_le_centralizer {A B F : Subgroup G}
    (hA : A.map (MulAut.conj t).toMonoidHom ≤ centralizer (F : Set G))
    (hB : B.map (MulAut.conj t).toMonoidHom ≤ centralizer (F : Set G)) :
    (A ⊔ B).map (MulAut.conj t).toMonoidHom ≤ centralizer (F : Set G) := by
  rw [Subgroup.map_sup]
  exact sup_le hA hB

theorem swapFactors_of_coherent {ι : Type*} {D : ι → Subgroup G} (P : ∀ a, SwapParam t (D a))
    {L : Subgroup G} (hL : IsSimpleGroup L) (O : ι → ι → Subgroup G) (hO : ∀ a b, O b a = O a b)
    (hOD : ∀ a b, a ≠ b → O a b ≤ D a)
    (hagree : ∀ a b, a ≠ b → AgreeOn (P a) (P b) (O a b))
    (h3 : ∀ a b : ι, ∃ c, c ≠ a ∧ c ≠ b)
    (hgen2 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → D a ≤ O a b ⊔ O a c)
    (hperf : ∀ a, ⁅D a, D a⁆ = D a) (hgen : ⨆ a, D a = L) :
    CFSG.Open.IsQuasisimple (⨆ a, (P a).fst (D a) : Subgroup G) ∧
      (⨆ a, (P a).fst (D a)).map (MulAut.conj t).toMonoidHom ≤
        centralizer ((⨆ a, (P a).fst (D a) : Subgroup G) : Set G) ∧
      (∀ x ∈ ⨆ a, (P a).fst (D a), x * (t * x * t⁻¹) ∈ L) ∧
      (∀ y ∈ L, ∃ x ∈ ⨆ a, (P a).fst (D a), x * (t * x * t⁻¹) = y) ∧
      ∀ a, (P a).Ψ.range ≤ (⨆ a, (P a).fst (D a)) ⊔
        (⨆ a, (P a).fst (D a)).map (MulAut.conj t).toMonoidHom := by
  set F : ι → Subgroup G := fun a => (P a).fst (D a) with hF
  have hfst : ∀ a b, a ≠ b → (P b).fst (O a b) = (P a).fst (O a b) := fun a b hab =>
    (P a).fst_eq_of_lft_eq (hOD a b hab) (hO a b ▸ hOD b a (Ne.symm hab)) (hagree a b hab)
  have hsplit : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → F a ≤ (P a).fst (O a b) ⊔ (P a).fst (O a c) :=
    fun a b c hab hac hbc => by
      rw [← fst_sup_of_le (P a) (hOD a b hab) (hOD a c hac)]
      exact fst_mono_of_le (P a) (hgen2 a b c hab hac hbc)
  have hcomm : ∀ a b, (F b).map (MulAut.conj t).toMonoidHom ≤ centralizer (F a : Set G) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact (P a).map_conj_fst_le_centralizer (D a) (D a)
    obtain ⟨c, hca, hcb⟩ := h3 a b
    have hFa := hsplit a b c hab (Ne.symm hca) (Ne.symm hcb)
    have hFb := hsplit b a c (Ne.symm hab) (Ne.symm hcb) (Ne.symm hca)
    have hba : O b a = O a b := hO a b
    refine le_trans (map_mono hFb) (map_conj_sup_le_centralizer ?_ ?_)
    ·
      refine le_trans ?_ (centralizer_le hFa)
      refine le_centralizer_sup_of_le ?_ ?_
      · rw [hba, hfst a b hab]
        exact (P a).map_conj_fst_le_centralizer (O a b) (O a b)
      · rw [hba, hfst a b hab]
        exact (P a).map_conj_fst_le_centralizer (O a c) (O a b)
    ·
      refine le_trans ?_ (centralizer_le hFa)
      refine le_centralizer_sup_of_le ?_ ?_
      · rw [← hfst a b hab]
        exact (P b).map_conj_fst_le_centralizer (O a b) (O b c)
      · rw [← hfst b c (Ne.symm hcb), ← hfst a c (Ne.symm hca)]
        exact (P c).map_conj_fst_le_centralizer (O a c) (O b c)
  obtain ⟨hq, h₁₂, hδ, hsurj⟩ := SeitzQ2.isQuasisimple_iSup_of_diag hL F D hcomm
    (fun a => (P a).commutator_fst le_rfl (hperf a))
    (fun a x hx => (P a).mul_conj_mem_of_mem_fst hx)
    (fun a y hy => (P a).exists_mem_fst_mul_conj_eq le_rfl hy) hgen
  refine ⟨hq, h₁₂, hδ, hsurj, fun a => ?_⟩
  have hr : (P a).Ψ.range = (((D a).subgroupOf (D a)).prod ((D a).subgroupOf (D a))).map
      (P a).Ψ := by
    rw [Subgroup.subgroupOf_self, Subgroup.top_prod_top, MonoidHom.range_eq_map]
  rw [hr, (P a).map_prod_eq_fst_sup (D a)]
  exact sup_le_sup (le_iSup F a) (map_mono (le_iSup F a))

end Factors

section Endgame

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_swapParam_family (hset : SeitzSetting G L) (hOut : Group.IsSolvable (Outer L))
    {P : Type} [Group P] [Finite P] (e : L ≃* P) (hP : SwapPairExclusion P) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {ι : Type*} {X D : ι → Subgroup G} (Ψ : ∀ a, SwapParam t (D a))
    (hinj : ∀ a, Function.Injective (Ψ a).Ψ)
    (hrange : ∀ a, (Ψ a).Ψ.range = centralizerPerfectCore (X a))
    (hXL : ∀ a, X a ≤ L) (hDX : ∀ a, D a ≤ centralizer (X a : Set G))
    (hDperf : ∀ a, ⁅D a, D a⁆ = D a) (hZD : ∀ a, center (D a) = ⊥) (hgen : ⨆ a, D a = L)
    (hXD : ∀ a b, a ≠ b → X b ≤ D a)
    (hsimple : ∀ a b, a ≠ b → IsSimpleGroup (perfectCore (D a ⊓ centralizer (X b : Set G))))
    (hZO : ∀ a b, a ≠ b → center (perfectCore (D a ⊓ centralizer (X b : Set G))) = ⊥)
    (h3 : ∀ a b : ι, ∃ c, c ≠ a ∧ c ≠ b)
    (hgen2 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      D a ≤ perfectCore (D a ⊓ centralizer (X b : Set G)) ⊔
        perfectCore (D a ⊓ centralizer (X c : Set G)))
    (o : ι)
    (hdet : ∀ k l, k ≠ o → l ≠ o → k ≠ l → ∃ x : G, x ≠ 1 ∧
      x ∈ perfectCore (D o ⊓ centralizer (X k : Set G)) ∧
      x ∈ perfectCore (D o ⊓ centralizer (X l : Set G)) ∧
      x ∈ perfectCore (D k ⊓ centralizer (X l : Set G))) : False := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have htC := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  have hL := SeitzQ2.isSimpleGroup_of_seitzSetting hset
  set O : ι → ι → Subgroup G := fun a b => perfectCore (D a ⊓ centralizer (X b : Set G)) with hOdef
  have hOD : ∀ a b, O a b ≤ D a := fun a b => (perfectCore_le _).trans inf_le_left
  have hpair : ∀ a b, a ≠ b → O b a = O a b ∧
      (AgreeOn (Ψ a) (Ψ b) (O a b) ∨ FlipOn (Ψ a) (Ψ b) (O a b)) := by
    intro a b hab
    have := hsimple a b hab
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours (Ψ a) (Ψ b) (hinj a) (hinj b) (hrange a)
      (hrange b) (hXD a b hab) (hXD b a (Ne.symm hab)) (hZO a b hab)
  have hO : ∀ a b, O b a = O a b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · exact (hpair a b hab).1
  obtain ⟨σ, hσ⟩ := exists_coherent_star ht2 Ψ O hO (fun a b hab => (hpair a b hab).2) o
    (fun k l hk hl hkl => by
      obtain ⟨x, hx1, hok, hol, hkl'⟩ := hdet k l hk hl hkl
      refine ⟨x, hok, hol, hkl', hOD k l hkl', fun hxZ => hx1 ?_⟩
      rw [hZD k, mem_bot] at hxZ
      exact congrArg Subtype.val hxZ)
  set Ψ' : ∀ a, SwapParam t (D a) := fun a => (Ψ a).twist (σ a) with hΨ'
  have hrange' : ∀ a, (Ψ' a).Ψ.range = centralizerPerfectCore (X a) := fun a =>
    (range_twist_Ψ (σ a) (Ψ a)).trans (hrange a)
  obtain ⟨hq, h₁₂, hδ, hsurj, hrng⟩ := swapFactors_of_coherent Ψ' hL O hO
    (fun a b _ => hOD a b) hσ h3 hgen2 hDperf hgen
  exact SeitzQ2.false_of_swapFactors_of_neighbours hset hOut htC ht hq h₁₂ hδ hsurj X D hXL hDX
    hDperf hgen (fun a => (hrange' a) ▸ hrng a)
    (SeitzQ2.nonSwap_of_factorNormal hset ht hKt
      (SeitzQ2.factorNormal_of_swapPairExclusion hset hOut e hP ht hKt) hq h₁₂ hδ hsurj)

theorem false_of_swapParam_pieces (hset : SeitzSetting G L) (hOut : Group.IsSolvable (Outer L))
    {P : Type} [Group P] [Finite P] (e : L ≃* P) (hP : SwapPairExclusion P) {t : G}
    (ht : orderOf t = 2) (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    {ι : Type*} [DecidableEq ι] {X D : ι → Subgroup G} (Ψ : ∀ a, SwapParam t (D a))
    (hinj : ∀ a, Function.Injective (Ψ a).Ψ)
    (hrange : ∀ a, (Ψ a).Ψ.range = centralizerPerfectCore (X a))
    (hXL : ∀ a, X a ≤ L) (hDL : ∀ a, D a ≤ L) (hDX : ∀ a, D a ≤ centralizer (X a : Set G))
    (hZD : ∀ a, center (D a) = ⊥)
    (hperfD : ∀ a (H : Subgroup G), ⁅H, H⁆ = H → H ≤ L ⊓ centralizer (X a : Set G) → H ≤ D a)
    (hXD : ∀ a b, a ≠ b → X b ≤ D a)
    (hsimple : ∀ a b, a ≠ b → IsSimpleGroup (perfectCore (D a ⊓ centralizer (X b : Set G))))
    (hZO : ∀ a b, a ≠ b → center (perfectCore (D a ⊓ centralizer (X b : Set G))) = ⊥)
    (o : ι)
    (hdet : ∀ k l, k ≠ o → l ≠ o → k ≠ l → ∃ x : G, x ≠ 1 ∧
      x ∈ perfectCore (D o ⊓ centralizer (X k : Set G)) ∧
      x ∈ perfectCore (D o ⊓ centralizer (X l : Set G)) ∧
      x ∈ perfectCore (D k ⊓ centralizer (X l : Set G)))
    {κ : Type*} (S : κ → Finset ι) (hS : ∀ j j', (S j ∩ S j').Nonempty)
    (hgen : L ≤ ⨆ j, perfectCore (L ⊓ centralizer ((⨆ s ∈ S j, X s : Subgroup G) : Set G))) :
    False := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  set O : ι → ι → Subgroup G := fun a b => perfectCore (D a ⊓ centralizer (X b : Set G)) with hOdef
  have hOD : ∀ a b, O a b ≤ D a := fun a b => (perfectCore_le _).trans inf_le_left
  have hpair : ∀ a b, a ≠ b → O b a = O a b ∧
      (AgreeOn (Ψ a) (Ψ b) (O a b) ∨ FlipOn (Ψ a) (Ψ b) (O a b)) := by
    intro a b hab
    have := hsimple a b hab
    exact SeitzQ2.agreeOn_or_flipOn_of_neighbours (Ψ a) (Ψ b) (hinj a) (hinj b) (hrange a)
      (hrange b) (hXD a b hab) (hXD b a (Ne.symm hab)) (hZO a b hab)
  have hO : ∀ a b, O b a = O a b := by
    intro a b
    by_cases hab : a = b
    · rw [hab]
    · exact (hpair a b hab).1
  obtain ⟨σ, hσ⟩ := exists_coherent_star ht2 Ψ O hO (fun a b hab => (hpair a b hab).2) o
    (fun k l hk hl hkl => by
      obtain ⟨x, hx1, hok, hol, hkl'⟩ := hdet k l hk hl hkl
      refine ⟨x, hok, hol, hkl', hOD k l hkl', fun hxZ => hx1 ?_⟩
      rw [hZD k, mem_bot] at hxZ
      exact congrArg Subtype.val hxZ)
  set Ψ' : ∀ a, SwapParam t (D a) := fun a => (Ψ a).twist (σ a) with hΨ'
  have hinj' : ∀ a, Function.Injective (Ψ' a).Ψ := fun a => injective_twist_Ψ (σ a) (Ψ a) (hinj a)
  have hrange' : ∀ a, (Ψ' a).Ψ.range = centralizerPerfectCore (X a) := fun a =>
    (range_twist_Ψ (σ a) (Ψ a)).trans (hrange a)
  set XS : κ → Subgroup G := fun j => ⨆ s ∈ S j, X s with hXSdef
  set OS : κ → Subgroup G := fun j => perfectCore (L ⊓ centralizer (XS j : Set G)) with hOSdef
  have hXS : ∀ j, ∀ s ∈ S j, X s ≤ XS j := fun j s hs => le_iSup₂ (f := fun s _ => X s) s hs
  have hOSperf : ∀ j, ⁅OS j, OS j⁆ = OS j := fun j => CFSG.Quasithin.perfectCore_perfect _
  have hOSle : ∀ j, OS j ≤ L ⊓ centralizer (XS j : Set G) := fun j => perfectCore_le _
  have hOSD : ∀ j, ∀ a ∈ S j, OS j ≤ D a := fun j a ha =>
    hperfD a (OS j) (hOSperf j) ((hOSle j).trans (inf_le_inf_left _ (centralizer_le (hXS j a ha))))
  have hOSO : ∀ j, ∀ a ∈ S j, ∀ b ∈ S j, OS j ≤ O a b := fun j a ha b hb =>
    CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (hOSD j a ha)
      ((hOSle j).trans (inf_le_right.trans (centralizer_le (hXS j b hb))))) (hOSperf j)
  have hne : ∀ j, (S j).Nonempty := fun j => by simpa using hS j j
  choose ν hν using hne
  have hagree : ∀ j, ∀ a ∈ S j, AgreeOn (Ψ' (ν j)) (Ψ' a) (OS j) := by
    intro j a ha
    by_cases h : ν j = a
    · rw [h]
      exact SeitzQ2.AgreeOn.refl _ _
    · exact (hσ (ν j) a h).mono (hOSO j (ν j) (hν j) a ha)
  have hpair' : ∀ j j', ∃ a, OS j ≤ D a ∧ OS j' ≤ D a ∧ AgreeOn (Ψ' (ν j)) (Ψ' a) (OS j) ∧
      AgreeOn (Ψ' (ν j')) (Ψ' a) (OS j') := by
    intro j j'
    obtain ⟨a, ha⟩ := hS j j'
    rw [Finset.mem_inter] at ha
    exact ⟨a, hOSD j a ha.1, hOSD j' a ha.2, hagree j a ha.1, hagree j' a ha.2⟩
  have hgen' : ⨆ j, OS j = L :=
    le_antisymm (iSup_le fun j => (hOSle j).trans inf_le_left) hgen
  have hM : ∀ j, centralizerPerfectCore (XS j) =
      (((OS j).subgroupOf (D (ν j))).prod ((OS j).subgroupOf (D (ν j)))).map (Ψ' (ν j)).Ψ := by
    intro j
    set a := ν j with ha
    set Y : Subgroup G := ⨆ s ∈ (S j).erase a, X s with hYdef
    have hY : Y ≤ D a := iSup₂_le fun s hs => hXD a s (Finset.ne_of_mem_erase hs).symm
    have hXY : X a ⊔ Y = XS j := by
      refine le_antisymm (sup_le (hXS j a (hν j))
        (iSup₂_le fun s hs => hXS j s (Finset.mem_of_mem_erase hs))) (iSup₂_le fun s hs => ?_)
      by_cases h : s = a
      · rw [h]
        exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂ (f := fun s _ => X s) s (Finset.mem_erase.2 ⟨h, hs⟩))
    have hYX : Y ≤ XS j := by
      rw [← hXY]
      exact le_sup_right
    have hcore : perfectCore (D a ⊓ centralizer (Y : Set G)) = OS j := by
      apply le_antisymm
      · refine CFSG.Quasithin.perfectCore_mono (le_inf (inf_le_left.trans (hDL a)) ?_)
        rw [← hXY]
        exact le_centralizer_sup_of_le (inf_le_left.trans (hDX a)) inf_le_right
      · refine CFSG.Quasithin.le_perfectCore_of_perfect (le_inf (hOSD j a (hν j)) ?_) (hOSperf j)
        exact (hOSle j).trans (inf_le_right.trans (centralizer_le hYX))
    rw [← hXY, (Ψ' a).centralizerPerfectCore_sup_eq (hinj' a) (hrange' a) hY, hcore]
  exact SeitzQ2.false_of_coherent_swapParam_of_swapPairExclusion hset hOut e hP ht hKt Ψ' OS ν
    (fun j => hOSD j (ν j) (hν j)) hOSperf hpair' hgen' XS
    (fun j => iSup₂_le fun s _ => hXL s) (fun j => (hOSle j).trans inf_le_right) hM

end Endgame

end CFSG.SeitzReduction.OmegaPilot

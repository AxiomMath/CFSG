module

public import CFSG.GH74.Uniqueness.Section4Lemma45
public import CFSG.GH74.Uniqueness.Section4Involutory

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Bridge

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def conjEquivOfMemNormalizer (L : Subgroup X) (g : X) (hg : g ∈ normalizer (L : Set X)) :
    ↥L ≃* ↥L where
  toFun l := ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg l).mp l.2⟩
  invFun l := ⟨g⁻¹ * l * g, by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set X)).inv_mem hg) l).mp l.2
    simpa using this⟩
  left_inv l := by apply Subtype.ext; simp [mul_assoc]
  right_inv l := by apply Subtype.ext; simp [mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

omit [Finite X] in
theorem conjEquivOfMemNormalizer_apply (L : Subgroup X) (g : X) (hg : g ∈ normalizer (L : Set X))
    (l : ↥L) : ((conjEquivOfMemNormalizer L g hg l : ↥L) : X) = g * (l : X) * g⁻¹ := rfl

theorem pPrimeCore_map_le (G : Type*) [Group G] [Finite G] (θ : G ≃* G) :
    (pPrimeCore 2 G).map θ.toMonoidHom ≤ pPrimeCore 2 G := by
  refine le_sSup ⟨?_, ?_⟩
  · exact Subgroup.Normal.map inferInstance θ.toMonoidHom θ.surjective
  · rw [Subgroup.card_map_of_injective θ.injective]
    exact pPrimeCore_coprime_card (p := 2) (G := G)

theorem ZDData.toXData {Z : Set X} {M L : Subgroup X}
    {u : ↥L} (hD : ZDData ↥L {l : ↥L | (l : X) ∈ Z} (M.comap L.subtype) u) :
    XData Z M L ((commutator ↥L).map L.subtype) ((pPrimeCore 2 ↥L).map L.subtype) (u : X) := by
  have hinj : Function.Injective L.subtype := L.subtype_injective
  set D := (commutator ↥L).map L.subtype with hDdef
  set O := (pPrimeCore 2 ↥L).map L.subtype with hOdef
  have hOD : O ≤ D := Subgroup.map_mono hD.le_comm
  have hu2 : (u : X) * (u : X) = 1 := by
    have := congrArg Subtype.val hD.sq
    simpa [pow_two] using this
  refine ⟨Subgroup.map_subtype_le _, hOD, u.2, Subgroup.mem_comap.mp hD.mem, hu2, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  ·
    have h := congrArg (Subgroup.map L.subtype) hD.sup
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact h.symm
  ·
    have h := congrArg (Subgroup.map L.subtype) hD.inf
    rw [Subgroup.map_inf _ _ _ hinj, MonoidHom.map_zpowers, Subgroup.map_bot] at h
    exact h
  · intro g hg d hd
    obtain ⟨d', hd', rfl⟩ := hd
    have h1 : (commutator ↥L).map (conjEquivOfMemNormalizer L g hg).toMonoidHom ≤ commutator ↥L := by
      rw [map_commutator_of_surjective _ (conjEquivOfMemNormalizer L g hg).surjective]
    refine ⟨conjEquivOfMemNormalizer L g hg d', h1 (Subgroup.mem_map_of_mem _ hd'), ?_⟩
    rfl
  · intro g hg o ho
    obtain ⟨o', ho', rfl⟩ := ho
    refine ⟨conjEquivOfMemNormalizer L g hg o',
      pPrimeCore_map_le ↥L (conjEquivOfMemNormalizer L g hg) (Subgroup.mem_map_of_mem _ ho'), ?_⟩
    rfl
  · rw [hOdef, Subgroup.card_map_of_injective hinj]
    exact odd_card_pPrimeCore ↥L
  · intro d hd
    obtain ⟨d', hd', rfl⟩ := hd
    have hmem : ⁅u, d'⁆ ∈ ⁅zpowers u, commutator ↥L⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hd'
    have := hD.comm hmem
    refine ⟨⁅u, d'⁆, this, ?_⟩
    simp [commutatorElement_def]
  · intro o ho
    obtain ⟨o', ho', rfl⟩ := ho
    exact Subgroup.mem_comap.mp (hD.le_M ho')
  · obtain ⟨K, _, φ, hφs, hφk, hKB, S, hS⟩ := hD.bar
    let e : ↥D ≃* ↥(commutator ↥L) :=
      (Subgroup.equivMapOfInjective (commutator ↥L) L.subtype hinj).symm
    have he : ∀ x : ↥D, (((e x : ↥(commutator ↥L)) : ↥L) : X) = (x : X) := by
      intro x
      have := (Subgroup.equivMapOfInjective (commutator ↥L) L.subtype hinj).apply_symm_apply x
      exact congrArg Subtype.val this
    refine ⟨K, inferInstance, φ.comp e.toMonoidHom, hφs.comp e.surjective, ?_, hKB, S, ?_⟩
    · ext x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφk,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        exact ⟨(e x : ↥L), h, he x⟩
      · rintro ⟨o', ho', hxo⟩
        have : ((e x : ↥(commutator ↥L)) : ↥L) = o' := by
          apply Subtype.ext
          rw [he x]; exact hxo.symm
        show ((e x : ↥(commutator ↥L)) : ↥L) ∈ pPrimeCore 2 ↥L
        rw [this]; exact ho'
    · rw [← hS, ← Subgroup.map_map]
      congr 1
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_comap,
        Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [he x]; exact hx
      · intro hy
        refine ⟨e.symm y, ?_, by simp⟩
        have := he (e.symm y)
        rw [MulEquiv.apply_symm_apply] at this
        rw [← this]; exact hy
  · intro z hz hzL
    obtain ⟨⟨d', hd', hzd⟩, hno⟩ := hD.zset ⟨z, hzL⟩ hz
    refine ⟨⟨(d' : X), Subgroup.mem_map.mpr ⟨d', hd', rfl⟩, ?_⟩, ?_⟩
    · have := congrArg Subtype.val hzd
      simpa using this
    · rintro o ⟨o', ho', rfl⟩ hzo
      apply hno o' ho'
      apply Subtype.ext
      simpa using hzo

end Bridge


section PartC

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.exists_involution_not_mem (S : ZDSetup X Z M) {H : Subgroup X} (hHM : ¬ H ≤ M)
    (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hbad : ¬ IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H))) :
    ∃ w ∈ zHull Z H, orderOf w = 2 ∧ w ∉ Z := by
  by_contra hall
  push Not at hall
  apply hbad
  obtain ⟨z, hz, hzHM⟩ := hne
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hzHM).1
  have hzM : z ∈ M := (Subgroup.mem_inf.mp hzHM).2
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, hzH⟩
  set L := zHull Z H with hL
  set B := (M ⊓ L).subgroupOf L with hB
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply S.not_zHull_le hHM ⟨z, hz, hzHM⟩
    intro l hl
    have : (⟨l, hl⟩ : ↥L) ∈ B := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_inf.mp this).1
  · have hzB : (⟨z, hzL⟩ : ↥L) ∈ B := Subgroup.mem_inf.mpr ⟨hzM, hzL⟩
    refine Simple.even_card_of_mem_orderOf_eq_two hzB ?_
    rw [Subgroup.orderOf_mk]
    exact S.invariant.1 z hz
  · intro g hg
    by_contra hev
    have hev' : Even (Nat.card ↥(B ⊓ conjugate B g)) := Nat.not_odd_iff_even.mp hev
    obtain ⟨t, ht, ht2⟩ := Simple.exists_mem_orderOf_eq_two_of_even_card hev'
    obtain ⟨htB, htg⟩ := Subgroup.mem_inf.mp ht
    have htM : (t : X) ∈ M := (Subgroup.mem_inf.mp htB).1
    have ht2' : orderOf (t : X) = 2 := by rw [Subgroup.orderOf_coe]; exact ht2
    have htZ : (t : X) ∈ Z := hall (t : X) t.2 ht2'
    have hgt : g * t * g⁻¹ ∈ B := mem_conjugate_iff.mp htg
    have hgtM : (g : X) * (t : X) * (g : X)⁻¹ ∈ M := (Subgroup.mem_inf.mp hgt).1
    have hginv : (g : X)⁻¹ ∈ M := by
      apply S.prodDisc.mem_of_conj_mem htZ htM
      simpa using hgtM
    apply hg
    exact Subgroup.mem_inf.mpr ⟨by simpa using M.inv_mem hginv, g.2⟩

theorem ZDSetup.two_le_twoRank_zHull (S : ZDSetup X Z M) {H : Subgroup X} (hHM : ¬ H ≤ M)
    (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hbad : ¬ IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H))) :
    2 ≤ Open.twoRank ↥(zHull Z H) := by
  by_contra hlt
  obtain ⟨w, hwL, hw2, hwZ⟩ := S.exists_involution_not_mem hHM hne hbad
  obtain ⟨z, hz, hzHM⟩ := hne
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, (Subgroup.mem_inf.mp hzHM).1⟩
  have hconj := isConj_of_involutions_of_twoRank_le_one (by omega : Open.twoRank ↥(zHull Z H) ≤ 1)
    (x := ⟨z, hzL⟩) (y := ⟨w, hwL⟩) (by rw [Subgroup.orderOf_mk]; exact S.invariant.1 z hz)
    (by rw [Subgroup.orderOf_mk]; exact hw2)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  apply hwZ
  have := congrArg Subtype.val hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
  rw [← this]
  have h1 := S.invariant.2 z hz (c : X)⁻¹
  simpa using h1

theorem ZDSetup.exists_xdata (S : ZDSetup X Z M) {H : Subgroup X} (hH : H ≠ ⊤) (hHM : ¬ H ≤ M)
    (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hbad : ¬ IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H))) :
    ∃ u : X, XData Z M (zHull Z H) ((commutator ↥(zHull Z H)).map (zHull Z H).subtype)
      ((pPrimeCore 2 ↥(zHull Z H)).map (zHull Z H).subtype) u := by
  have hIH := S.zdConclusion_zHull hH hHM hne
  rw [zdConclusion_iff] at hIH
  rcases hIH with hrank | ⟨u, hu⟩
  · exact absurd (S.two_le_twoRank_zHull hHM hne hbad) (by omega)
  · exact ⟨(u : X), hu.toXData⟩

end PartC


section ClaimA

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem centralizer_le_of_isStronglyEmbedded {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsStronglyEmbedded B) {t : G} (htB : t ∈ B) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set G) ≤ B := by
  intro g hg
  by_contra hgB
  have hodd := hB.2.2 g hgB
  have htg : t ∈ B ⊓ conjugate B g := by
    refine Subgroup.mem_inf.mpr ⟨htB, mem_conjugate_iff.mpr ?_⟩
    have : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have e : g * t * g⁻¹ = t := by rw [this]; group
    rw [e]; exact htB
  exact (Nat.not_even_iff_odd.mpr hodd) (Simple.even_card_of_mem_orderOf_eq_two htg ht2)

omit [Finite X] in
theorem isStronglyEmbedded_subgroupOf_congr {L D : Subgroup X} (h : L = D) :
    IsStronglyEmbedded (M.subgroupOf D) → IsStronglyEmbedded (M.subgroupOf L) := by
  subst h
  exact id

omit [Finite X] in
theorem inf_subgroupOf_self (M L : Subgroup X) : (M ⊓ L).subgroupOf L = M.subgroupOf L := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

theorem ZDSetup.exists_centralizer_bad (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥)
    {H : Subgroup X} (hH : H ≠ ⊤) (hHM : ¬ H ≤ M)
    (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hbad : ¬ IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H))) :
    ∃ u : X, orderOf u = 2 ∧ u ∈ M ∧ u ∈ zHull Z (centralizer ({u} : Set X)) ∧
      centralizer ({u} : Set X) ≠ ⊤ ∧ ¬ centralizer ({u} : Set X) ≤ M ∧
      (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty ∧
      ¬ IsStronglyEmbedded ((M ⊓ zHull Z (centralizer ({u} : Set X))).subgroupOf
        (zHull Z (centralizer ({u} : Set X)))) := by
  obtain ⟨u, hD⟩ := S.exists_xdata hH hHM hne hbad
  set D := (commutator ↥(zHull Z H)).map (zHull Z H).subtype with hDdef
  set O := (pPrimeCore 2 ↥(zHull Z H)).map (zHull Z H).subtype with hOdef
  obtain ⟨z, hz, hzHM⟩ := hne
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hzHM).1
  have hzM : z ∈ M := (Subgroup.mem_inf.mp hzHM).2
  have hzL : z ∈ zHull Z H := Subgroup.subset_closure ⟨hz, hzH⟩
  have hnotLM : ¬ zHull Z H ≤ M := S.not_zHull_le hHM ⟨z, hz, hzHM⟩
  have hu1 : u ≠ 1 := by
    intro hu1
    have hLD : zHull Z H = (commutator ↥(zHull Z H)).map (zHull Z H).subtype := by
      have := hD.sup
      rw [hu1, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at this
      exact this
    apply hbad
    rw [inf_subgroupOf_self]
    exact isStronglyEmbedded_subgroupOf_congr hLD hD.isStronglyEmbedded
  have hu2 : u * u = 1 := hD.sq
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
  set L := zHull Z H with hLdef
  set H₁ := centralizer ({u} : Set X) with hH₁
  have hNodd := hD.O_odd
  have hOM := hD.O_M
  have hH₁M : ¬ H₁ ≤ M := by
    intro hle
    apply hnotLM
    intro l hl
    obtain ⟨o, ho, c, hcL, huc, rfl⟩ := hD.exists_mul_centralizer_L hl
    exact M.mul_mem (hOM ho) (hle (Subgroup.mem_centralizer_singleton_iff.mpr huc.symm))
  obtain ⟨y, hyZ, hyL, huy, hyz⟩ := hD.exists_mem_Z_centralizer S.invariant hz hzL
  have hyM : y ∈ M := by
    have : y = (y * z⁻¹) * z := by group
    rw [this]
    exact M.mul_mem (hOM hyz) hzM
  have hyH₁ : y ∈ H₁ := Subgroup.mem_centralizer_singleton_iff.mpr huy.symm
  have hne₁ : (Z ∩ ((H₁ ⊓ M : Subgroup X) : Set X)).Nonempty :=
    ⟨y, hyZ, Subgroup.mem_inf.mpr ⟨hyH₁, hyM⟩⟩
  have hH₁top : H₁ ≠ ⊤ := by
    intro htop
    have hucent : u ∈ center X := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ H₁ := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp this
    have hAc : zpowers u ≤ center X := (Subgroup.zpowers_le).mpr hucent
    have : (zpowers u).Normal := normal_of_le_center' hAc
    have hsol : Group.IsSolvable ↥(zpowers u) := inferInstance
    have := h45 _ inferInstance hsol
    exact hu1 (by
      have h1 : u ∈ zpowers u := Subgroup.mem_zpowers u
      rw [this, Subgroup.mem_bot] at h1
      exact h1)
  have huL₁ : u ∈ zHull Z H₁ := by
    obtain ⟨a, haD, b, hbD, ha2, hb2, hab, habc, hua, hub⟩ := hD.exists_commuting_involutions
    have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha2; exact absurd ha2 (by norm_num)
    have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb2; exact absurd hb2 (by norm_num)
    have haa : a * a = 1 := by
      have := pow_orderOf_eq_one a; rwa [ha2, pow_two] at this
    have hbb : b * b = 1 := by
      have := pow_orderOf_eq_one b; rwa [hb2, pow_two] at this
    have hmemZ : ∀ w ∈ D, w * w = 1 → w ≠ 1 → u * w = w * u → u * w ∈ Z := by
      intro w hw hww hw1 huw
      refine hD.mem_of_involution S.invariant ⟨z, hz, hzL⟩ ?_ ⟨w, hw, rfl⟩ ?_
      · calc u * w * (u * w) = u * (w * u) * w := by group
          _ = u * (u * w) * w := by rw [← huw]
          _ = (u * u) * (w * w) := by group
          _ = 1 := by rw [hu2, hww, one_mul]
      · intro o ho hwo
        have : w = o := mul_left_cancel hwo
        subst this
        exact hw1 (eq_one_of_mem_of_sq_eq_one hNodd ho hww)
    have hab2 : a * b ∈ D := D.mul_mem haD hbD
    have habsq : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [habc]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      exact (mul_eq_one_iff_eq_inv.mp h).trans (inv_eq_of_mul_eq_one_right hbb)
    have huab : u * (a * b) = (a * b) * u := by
      calc u * (a * b) = (u * a) * b := by group
        _ = (a * u) * b := by rw [hua]
        _ = a * (u * b) := by group
        _ = a * (b * u) := by rw [hub]
        _ = (a * b) * u := by group
    have hz1 := hmemZ a haD haa ha1 hua
    have hz2 := hmemZ b hbD hbb hb1 hub
    have hz3 := hmemZ (a * b) hab2 habsq hab1 huab
    have hmem : ∀ w, u * w ∈ Z → u * (u * w) = (u * w) * u → u * w ∈ zHull Z H₁ := by
      intro w hwZ hcomm
      exact Subgroup.subset_closure ⟨hwZ, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hc1 : u * (u * a) = (u * a) * u := by
      calc u * (u * a) = u * (a * u) := by rw [hua]
        _ = (u * a) * u := by group
    have hc2 : u * (u * b) = (u * b) * u := by
      calc u * (u * b) = u * (b * u) := by rw [hub]
        _ = (u * b) * u := by group
    have hc3 : u * (u * (a * b)) = (u * (a * b)) * u := by
      calc u * (u * (a * b)) = u * ((a * b) * u) := by rw [huab]
        _ = (u * (a * b)) * u := by group
    have h1 : (u * a) * (u * b) = a * b := by
      calc (u * a) * (u * b) = u * (a * u) * b := by group
        _ = u * (u * a) * b := by rw [hua]
        _ = (u * u) * (a * b) := by group
        _ = a * b := by rw [hu2, one_mul]
    have hprod : u = (u * a) * (u * b) * (u * (a * b)) := by
      rw [h1]
      calc u = u * ((a * b) * (a * b)) := by rw [habsq, mul_one]
        _ = (u * (a * b)) * (a * b) := by group
        _ = ((a * b) * u) * (a * b) := by rw [huab]
        _ = (a * b) * (u * (a * b)) := by group
    rw [hprod]
    exact (zHull Z H₁).mul_mem ((zHull Z H₁).mul_mem (hmem a hz1 hc1) (hmem b hz2 hc2))
      (hmem (a * b) hz3 hc3)
  refine ⟨u, hu2', hD.mem_M, huL₁, hH₁top, hH₁M, hne₁, ?_⟩
  intro hSE
  set L₁ := zHull Z H₁ with hL₁
  have huL₁M : u ∈ M ⊓ L₁ := Subgroup.mem_inf.mpr ⟨hD.mem_M, huL₁⟩
  set B' := (M ⊓ L₁).subgroupOf L₁ with hB'
  have hub : (⟨u, huL₁⟩ : ↥L₁) ∈ B' := huL₁M
  have hcent := centralizer_le_of_isStronglyEmbedded hSE hub
    (by rw [Subgroup.orderOf_mk]; exact hu2')
  have hL₁M : L₁ ≤ M := by
    intro l hl
    have hlH₁ : l ∈ H₁ := ((Subgroup.closure_le _).mpr (fun w hw => hw.2) : L₁ ≤ H₁) hl
    have : (⟨l, hl⟩ : ↥L₁) ∈ centralizer ({(⟨u, huL₁⟩ : ↥L₁)} : Set ↥L₁) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hlH₁
    exact (Subgroup.mem_inf.mp (hcent this)).1
  apply hnotLM
  show zHull Z H ≤ M
  unfold zHull
  rw [Subgroup.closure_le]
  rintro w ⟨hwZ, hwH⟩
  have hwL : w ∈ L := Subgroup.subset_closure ⟨hwZ, hwH⟩
  obtain ⟨y', hy'Z, hy'L, huy', hy'w⟩ := hD.exists_mem_Z_centralizer S.invariant hwZ hwL
  have hy'L₁ : y' ∈ L₁ :=
    Subgroup.subset_closure ⟨hy'Z, Subgroup.mem_centralizer_singleton_iff.mpr huy'.symm⟩
  have hw : w = (y' * w⁻¹)⁻¹ * y' := by group
  show w ∈ M
  rw [hw]
  exact M.mul_mem (M.inv_mem (hOM hy'w)) (hL₁M hy'L₁)

end ClaimA


section Stage2

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem productInvolutions_conj (hZ : IsInvariantInvolutionSet Z) {x : X}
    (hx : x ∈ productInvolutions Z) (g : X) : g⁻¹ * x * g ∈ productInvolutions Z := by
  obtain ⟨hx2, a, ha, b, hb, hab, rfl⟩ := hx
  refine ⟨?_, g⁻¹ * a * g, hZ.2 a ha g, g⁻¹ * b * g, hZ.2 b hb g, ?_, by group⟩
  · have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective (a * b)
    simpa [MulAut.conj_apply, hx2] using this
  · have e : (g⁻¹ * a * g) * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
    have e' : (g⁻¹ * b * g) * (g⁻¹ * a * g) = g⁻¹ * (b * a) * g := by group
    rw [e, e', hab]

theorem exists_conj_centralizer_ne
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥) {u : X} (hu2 : orderOf u = 2)
    (hH : centralizer ({u} : Set X) ≠ ⊤) :
    ∃ x : X, x⁻¹ * u * x ∈ centralizer ({u} : Set X) ∧ x⁻¹ * u * x ≠ u := by
  by_contra hall
  push Not at hall
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  have : Fintype X := Fintype.ofFinite X
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X u hu1 huu (by
    intro g hg
    have := hall g⁻¹ (by
      rw [Subgroup.mem_centralizer_singleton_iff]
      simpa using hg)
    simpa using this)
  have hNbot : N = ⊥ := h45 N hNn (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hNodd)
  apply hH
  rw [eq_top_iff]
  intro g _
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 := hN g
  rw [hNbot, Subgroup.mem_bot] at h1
  calc g * u = (g * u * g⁻¹ * u⁻¹) * u * g := by group
    _ = u * g := by rw [h1]; group


theorem ZDSetup.false_of_centralizer_bad
    (hB : BenderFacts) (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥) {u : X} (hu2 : orderOf u = 2)
    (huM : u ∈ M) (huL : u ∈ zHull Z (centralizer ({u} : Set X)))
    (hH : centralizer ({u} : Set X) ≠ ⊤) (hHM : ¬ centralizer ({u} : Set X) ≤ M)
    (hne : (Z ∩ ((centralizer ({u} : Set X) ⊓ M : Subgroup X) : Set X)).Nonempty)
    (hbad : ¬ IsStronglyEmbedded ((M ⊓ zHull Z (centralizer ({u} : Set X))).subgroupOf
      (zHull Z (centralizer ({u} : Set X))))) : False := by
  have huu : u * u = 1 := by
    have := pow_orderOf_eq_one u
    rwa [hu2, pow_two] at this
  have hu1 : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; exact absurd hu2 (by norm_num)
  obtain ⟨u', hD'⟩ := S.exists_xdata hH hHM hne hbad
  set H := centralizer ({u} : Set X) with hHdef
  set L := zHull Z H with hLdef
  set D := (commutator ↥L).map L.subtype with hDdef
  set O := (pPrimeCore 2 ↥L).map L.subtype with hOdef
  have hLH : L ≤ H := (Subgroup.closure_le _).mpr (fun w hw => hw.2)
  have hcentral : ∀ l ∈ L, u * l = l * u := fun l hl =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hLH hl)).symm
  have hD : XData Z M L D O u := hD'.of_central huL hcentral hu2 huM
  have hDL : D ≤ L := hD.D_le
  have hNodd := hD.O_odd
  obtain ⟨z, hzZ, hzHM⟩ := hne
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hzHM).1
  have hzM : z ∈ M := (Subgroup.mem_inf.mp hzHM).2
  have hzL : z ∈ L := Subgroup.subset_closure ⟨hzZ, hzH⟩
  have hz2 : z * z = 1 := S.invariant.mul_self_eq_one hzZ
  have huz : u * z = z * u := hcentral z hzL
  have huZ : u ∉ Z := fun h => hHM (S.prodDisc.centralizer_le_of_mem h huM)
  have hZH : ∀ y ∈ Z, y ∈ H → y ∈ L := fun y hy hyH => Subgroup.subset_closure ⟨hy, hyH⟩
  have hI : ∀ d ∈ D, orderOf d = 2 → u * d ∈ Z := by
    intro d hd hd2
    have hdd : d * d = 1 := by
      have := pow_orderOf_eq_one d
      rwa [hd2, pow_two] at this
    have hd1 : d ≠ 1 := fun h => by rw [h, orderOf_one] at hd2; exact absurd hd2 (by norm_num)
    have hud : u * d = d * u := hcentral d (hDL hd)
    refine hD.mem_of_involution S.invariant ⟨z, hzZ, hzL⟩ ?_ ⟨d, hd, rfl⟩ ?_
    · calc u * d * (u * d) = u * (d * u) * d := by group
        _ = u * (u * d) * d := by rw [← hud]
        _ = (u * u) * (d * d) := by group
        _ = 1 := by rw [huu, hdd, one_mul]
    · intro o ho hdo
      have : d = o := mul_left_cancel hdo
      subst this
      exact hd1 (eq_one_of_mem_of_sq_eq_one hNodd ho hdd)
  have hZd : ∀ y ∈ Z, y ∈ H → ∃ d ∈ D, y = u * d ∧ orderOf d = 2 := by
    intro y hy hyH
    obtain ⟨⟨d, hd, hyd⟩, -⟩ := hD.zset y hy (hZH y hy hyH)
    have huy : u * y = y * u := hcentral y (hZH y hy hyH)
    have hy2 := S.invariant.mul_self_eq_one hy
    have hdd : d * d = 1 := by
      have hud : u * d = d * u := hcentral d (hDL hd)
      have : (u * d) * (u * d) = 1 := by rw [← hyd]; exact hy2
      calc d * d = (u * u) * (d * d) := by rw [huu, one_mul]
        _ = (u * d) * (u * d) := by
          calc (u * u) * (d * d) = u * (u * d) * d := by group
            _ = u * (d * u) * d := by rw [hud]
            _ = (u * d) * (u * d) := by group
        _ = 1 := this
    have hd1 : d ≠ 1 := by
      intro h
      rw [h, mul_one] at hyd
      exact huZ (hyd ▸ hy)
    exact ⟨d, hd, hyd, orderOf_eq_prime (by rwa [pow_two]) hd1⟩
  have hIP : ∀ d ∈ D, orderOf d = 2 → d ∈ productInvolutions Z := by
    intro d hd hd2
    obtain ⟨a, haD, b, hbD, ha2, hb2, hab, habc, hua, hub⟩ := hD.exists_commuting_involutions
    have haa : a * a = 1 := by
      have := pow_orderOf_eq_one a; rwa [ha2, pow_two] at this
    have hbb : b * b = 1 := by
      have := pow_orderOf_eq_one b; rwa [hb2, pow_two] at this
    have hy₁ : u * a ∈ Z := hI a haD ha2
    have hy₂ : u * b ∈ Z := hI b hbD hb2
    have hP1 : (u * a) * (u * b) = a * b := by
      calc (u * a) * (u * b) = u * (a * u) * b := by group
        _ = u * (u * a) * b := by rw [hua]
        _ = (u * u) * (a * b) := by group
        _ = a * b := by rw [huu, one_mul]
    have hP2 : (u * b) * (u * a) = a * b := by
      calc (u * b) * (u * a) = u * (b * u) * a := by group
        _ = u * (u * b) * a := by rw [hub]
        _ = (u * u) * (b * a) := by group
        _ = a * b := by rw [huu, one_mul, habc]
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      exact (mul_eq_one_iff_eq_inv.mp h).trans (inv_eq_of_mul_eq_one_right hbb)
    have habsq : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [habc]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    have hab2 : orderOf (a * b) = 2 := orderOf_eq_prime (by rwa [pow_two]) hab1
    have hP : a * b ∈ productInvolutions Z :=
      ⟨hab2, u * a, hy₁, u * b, hy₂, by rw [hP1, hP2], hP1.symm⟩
    obtain ⟨g, hgD, hg⟩ := hD.exists_conj_involutions (D.mul_mem haD hbD) hd hab2 hd2
    rw [← hg]
    exact productInvolutions_conj S.invariant hP g
  have h48 : ∀ x' : X, x'⁻¹ * u * x' ∈ H → x'⁻¹ * u * x' ≠ u → ∀ a ∈ D, ∀ b ∈ D, orderOf a = 2 →
      orderOf b = 2 → a ≠ b → a * b = b * a → (x'⁻¹ * u * x') * a = a * (x'⁻¹ * u * x') →
      (x'⁻¹ * u * x') * b = b * (x'⁻¹ * u * x') → False := by
    intro x' hx'v hx'ne a haD b hbD ha2 hb2 hab habc hva hvb
    set v' := x'⁻¹ * u * x' with hv'
    have huv' : v' * u = u * v' := Subgroup.mem_centralizer_singleton_iff.mp hx'v
    have haa : a * a = 1 := by
      have := pow_orderOf_eq_one a; rwa [ha2, pow_two] at this
    have hbb : b * b = 1 := by
      have := pow_orderOf_eq_one b; rwa [hb2, pow_two] at this
    have hua : u * a = a * u := hcentral a (hDL haD)
    have hub : u * b = b * u := hcentral b (hDL hbD)
    have hab1 : a * b ≠ 1 := by
      intro h
      apply hab
      exact (mul_eq_one_iff_eq_inv.mp h).trans (inv_eq_of_mul_eq_one_right hbb)
    have habsq : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [habc]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [haa, hbb, one_mul]
    have hab2 : orderOf (a * b) = 2 := orderOf_eq_prime (by rwa [pow_two]) hab1
    have habD : a * b ∈ D := D.mul_mem haD hbD
    have huab : u * (a * b) = (a * b) * u := hcentral _ (hDL habD)
    have hvab : v' * (a * b) = (a * b) * v' := by
      calc v' * (a * b) = (v' * a) * b := by group
        _ = (a * v') * b := by rw [hva]
        _ = a * (v' * b) := by group
        _ = a * (b * v') := by rw [hvb]
        _ = (a * b) * v' := by group
    have hy₁ : u * a ∈ Z := hI a haD ha2
    have hy₂ : u * b ∈ Z := hI b hbD hb2
    have hy₃ : u * (a * b) ∈ Z := hI (a * b) habD hab2
    have hcv : ∀ w, v' * w = w * v' → v' * (u * w) = (u * w) * v' := by
      intro w hw
      calc v' * (u * w) = (v' * u) * w := by group
        _ = (u * v') * w := by rw [huv']
        _ = u * (v' * w) := by group
        _ = u * (w * v') := by rw [hw]
        _ = (u * w) * v' := by group
    have hxu : x' * v' * x'⁻¹ = u := by rw [hv']; group
    have hconj : ∀ y ∈ Z, v' * y = y * v' →
        ∃ d ∈ D, x' * y * x'⁻¹ = u * d := by
      intro y hy hvy
      have hyZ : x' * y * x'⁻¹ ∈ Z := by
        have := S.invariant.2 y hy x'⁻¹
        simpa using this
      have hyH : x' * y * x'⁻¹ ∈ H := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc x' * y * x'⁻¹ * u = x' * y * (x'⁻¹ * u * x') * x'⁻¹ := by group
          _ = x' * (y * v') * x'⁻¹ := by rw [← hv']; group
          _ = x' * (v' * y) * x'⁻¹ := by rw [hvy]
          _ = (x' * v' * x'⁻¹) * (x' * y * x'⁻¹) := by group
          _ = u * (x' * y * x'⁻¹) := by rw [hxu]
      obtain ⟨⟨d, hd, hyd⟩, -⟩ := hD.zset _ hyZ (hZH _ hyZ hyH)
      exact ⟨d, hd, hyd⟩
    obtain ⟨d₁, hd₁, hw₁⟩ := hconj _ hy₁ (hcv a hva)
    obtain ⟨d₂, hd₂, hw₂⟩ := hconj _ hy₂ (hcv b hvb)
    obtain ⟨d₃, hd₃, hw₃⟩ := hconj _ hy₃ (hcv _ hvab)
    have hprod : u = (u * a) * (u * b) * (u * (a * b)) := by
      have h1 : (u * a) * (u * b) = a * b := by
        calc (u * a) * (u * b) = u * (a * u) * b := by group
          _ = u * (u * a) * b := by rw [hua]
          _ = (u * u) * (a * b) := by group
          _ = a * b := by rw [huu, one_mul]
      rw [h1]
      calc u = u * ((a * b) * (a * b)) := by rw [habsq, mul_one]
        _ = (u * (a * b)) * (a * b) := by group
        _ = ((a * b) * u) * (a * b) := by rw [huab]
        _ = (a * b) * (u * (a * b)) := by group
    have hxuc : x' * u * x'⁻¹ = (u * d₁) * (u * d₂) * (u * d₃) := by
      rw [← hw₁, ← hw₂, ← hw₃]
      calc x' * u * x'⁻¹ = x' * ((u * a) * (u * b) * (u * (a * b))) * x'⁻¹ := by rw [← hprod]
        _ = (x' * (u * a) * x'⁻¹) * (x' * (u * b) * x'⁻¹) * (x' * (u * (a * b)) * x'⁻¹) := by group
    have hd₁u : u * d₁ = d₁ * u := hcentral d₁ (hDL hd₁)
    have hd₂u : u * d₂ = d₂ * u := hcentral d₂ (hDL hd₂)
    have hd₃u : u * d₃ = d₃ * u := hcentral d₃ (hDL hd₃)
    have hee : (u * d₁) * (u * d₂) * (u * d₃) = u * (d₁ * d₂ * d₃) := by
      calc (u * d₁) * (u * d₂) * (u * d₃)
          = u * (d₁ * u) * d₂ * (u * d₃) := by group
        _ = u * (u * d₁) * d₂ * (u * d₃) := by rw [hd₁u]
        _ = (u * u) * (d₁ * d₂) * (u * d₃) := by group
        _ = (d₁ * d₂) * (u * d₃) := by rw [huu, one_mul]
        _ = (d₁ * d₂) * (d₃ * u) := by rw [hd₃u]
        _ = (d₁ * d₂ * d₃) * u := by group
        _ = u * (d₁ * d₂ * d₃) := (hcentral _ (hDL (D.mul_mem (D.mul_mem hd₁ hd₂) hd₃))).symm
    set e := d₁ * d₂ * d₃ with hedef
    have heD : e ∈ D := D.mul_mem (D.mul_mem hd₁ hd₂) hd₃
    have hue : u * e = e * u := hcentral e (hDL heD)
    have hxx : (x' * u * x'⁻¹) * (x' * u * x'⁻¹) = 1 := by
      calc (x' * u * x'⁻¹) * (x' * u * x'⁻¹) = x' * (u * u) * x'⁻¹ := by group
        _ = 1 := by rw [huu]; group
    have hee2 : e * e = 1 := by
      rw [hxuc, hee] at hxx
      calc e * e = (u * u) * (e * e) := by rw [huu, one_mul]
        _ = (u * e) * (u * e) := by
          calc (u * u) * (e * e) = u * (u * e) * e := by group
            _ = u * (e * u) * e := by rw [hue]
            _ = (u * e) * (u * e) := by group
        _ = 1 := hxx
    have he1 : e ≠ 1 := by
      intro h
      rw [h, mul_one] at hee
      have hxc : x' * u * x'⁻¹ = u := by rw [hxuc, hee]
      apply hx'ne
      calc v' = x'⁻¹ * u * x' := hv'
        _ = x'⁻¹ * (x' * u * x'⁻¹) * x' := by rw [hxc]
        _ = u := by group
    have heo : orderOf e = 2 := orderOf_eq_prime (by rwa [pow_two]) he1
    have huez : u * e ∈ Z := hI e heD heo
    apply huZ
    have : u = x'⁻¹ * (u * e) * x' := by
      rw [← hee, ← hxuc]; group
    rw [this]
    have := S.invariant.2 (u * e) huez x'
    exact this
  obtain ⟨x, hxv, hxne⟩ := exists_conj_centralizer_ne h45 hu2 hH
  set v := x⁻¹ * u * x with hvdef
  have hv2 : v * v = 1 := by
    calc v * v = x⁻¹ * (u * u) * x := by rw [hvdef]; group
      _ = 1 := by rw [huu]; group
  have hvH : v ∈ H := hxv
  have hvN : v ∈ normalizer (L : Set X) := le_normalizer_zHull S.invariant H hvH
  obtain ⟨d₁, hd₁D, hd₁2, hvd₁⟩ := hD.exists_involution_commuting hB.outerInvolution hvN hv2
  obtain ⟨dz, hdzD, hzdz, hdz2⟩ := hZd z hzZ hzH
  obtain ⟨e, heD, hed⟩ := hD.exists_conj_involutions hd₁D hdzD hd₁2 hdz2
  set v' := e⁻¹ * v * e with hv'def
  have hv'eq : v' = (x * e)⁻¹ * u * (x * e) := by rw [hv'def, hvdef]; group
  have heH : e ∈ H := hLH (hDL heD)
  have heu : e * u = u * e := Subgroup.mem_centralizer_singleton_iff.mp heH
  have hv'H : v' ∈ H := H.mul_mem (H.mul_mem (H.inv_mem heH) hvH) heH
  have hv'ne : v' ≠ u := by
    intro h
    apply hxne
    calc v = e * (e⁻¹ * v * e) * e⁻¹ := by group
      _ = e * u * e⁻¹ := by rw [← hv'def, h]
      _ = u := by rw [heu]; group
  have hv'2 : v' * v' = 1 := by
    calc v' * v' = e⁻¹ * (v * v) * e := by rw [hv'def]; group
      _ = 1 := by rw [hv2]; group
  have hv'N : v' ∈ normalizer (L : Set X) := le_normalizer_zHull S.invariant H hv'H
  have hv'dz : v' * dz = dz * v' := by
    rw [← hed, hv'def]
    calc e⁻¹ * v * e * (e⁻¹ * d₁ * e) = e⁻¹ * (v * d₁) * e := by group
      _ = e⁻¹ * (d₁ * v) * e := by rw [hvd₁]
      _ = (e⁻¹ * d₁ * e) * (e⁻¹ * v * e) := by group
  have hv'u : v' * u = u * v' := Subgroup.mem_centralizer_singleton_iff.mp hv'H
  have hv'z : v' * z = z * v' := by
    rw [hzdz]
    calc v' * (u * dz) = (v' * u) * dz := by group
      _ = (u * v') * dz := by rw [hv'u]
      _ = u * (v' * dz) := by group
      _ = u * (dz * v') := by rw [hv'dz]
      _ = (u * dz) * v' := by group
  have hzin : ∃ e' ∈ D, ∀ d ∈ D, z * d * z⁻¹ = e' * d * e'⁻¹ := by
    refine ⟨dz, hdzD, fun d hd => ?_⟩
    have hmem : dz * d * dz⁻¹ ∈ D := D.mul_mem (D.mul_mem hdzD hd) (D.inv_mem hdzD)
    have hu1 : u * (dz * d * dz⁻¹) = (dz * d * dz⁻¹) * u := hcentral _ (hDL hmem)
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
    calc z * d * z⁻¹ = (u * dz) * d * (u * dz)⁻¹ := by rw [← hzdz]
      _ = u * (dz * d * dz⁻¹) * u⁻¹ := by group
      _ = (dz * d * dz⁻¹) * u * u⁻¹ := by rw [hu1]
      _ = dz * d * dz⁻¹ := by group
  have hxv'u : (x * e) * v' * (x * e)⁻¹ = u := by rw [hv'eq]; group
  have hv'zP : v' * z ∈ productInvolutions Z := by
    set x' := x * e with hx'
    set y' := x' * z * x'⁻¹ with hy'
    have hy'Z : y' ∈ Z := by
      have := S.invariant.2 z hzZ x'⁻¹
      simpa using this
    have hy'H : y' ∈ H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc y' * u = x' * z * (x'⁻¹ * u * x') * x'⁻¹ := by rw [hy']; group
        _ = x' * z * v' * x'⁻¹ := by rw [← hv'eq]
        _ = x' * (z * v') * x'⁻¹ := by group
        _ = x' * (v' * z) * x'⁻¹ := by rw [hv'z]
        _ = (x' * v' * x'⁻¹) * (x' * z * x'⁻¹) := by group
        _ = u * y' := by rw [hxv'u]
    obtain ⟨d', hd'D, hy'd', hd'2⟩ := hZd y' hy'Z hy'H
    have hd'eq : d' = u * y' := by rw [hy'd', ← mul_assoc, huu, one_mul]
    have hdP := hIP d' hd'D hd'2
    have h1 := productInvolutions_conj S.invariant hdP x'
    have heq : x'⁻¹ * d' * x' = v' * z := by
      rw [hd'eq, hy', hv'eq]; group
    rw [heq] at h1
    exact h1
  have hv'zM : v' * z ∈ M := by
    have hv'M : v' ∈ M := S.prodDisc.centralizer_le_of_mem hzZ hzM
      (Subgroup.mem_centralizer_singleton_iff.mpr hv'z)
    exact M.mul_mem hv'M hzM
  have hfix : ∀ d ∈ D, (v' * z) * d = d * (v' * z) → d ∈ M := fun d _ hc =>
    (S.prodDisc.mem_uniqC hv'zP hv'zM).2.2 (Subgroup.mem_centralizer_singleton_iff.mpr hc.symm)
  have hrank : ∀ a ∈ D, ∀ b ∈ D, orderOf a = 2 → orderOf b = 2 → a ≠ b → a * b = b * a →
      v' * a = a * v' → v' * b = b * v' → False := by
    intro a ha b hb ha2 hb2 hab habc hva hvb
    exact h48 (x * e) (hv'eq ▸ hv'H) (hv'eq ▸ hv'ne) a ha b hb ha2 hb2 hab habc
      (hv'eq ▸ hva) (hv'eq ▸ hvb)
  exact hD.false_of_involutory hB.outerInvolution hv'N hv'2 hzL hz2 hv'z hzin hfix hrank

end Stage2


section Prop44

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.prop44 (hB : BenderFacts) (S : ZDSetup X Z M)
    (h45 : ∀ N : Subgroup X, N.Normal → Group.IsSolvable ↥N → N = ⊥) {H : Subgroup X}
    (hH : H ≠ ⊤) (hHM : ¬ H ≤ M) (hne : (Z ∩ ((H ⊓ M : Subgroup X) : Set X)).Nonempty) :
    IsStronglyEmbedded ((M ⊓ zHull Z H).subgroupOf (zHull Z H)) := by
  by_contra hbad
  obtain ⟨u, hu2, huM, huL, hH', hHM', hne', hbad'⟩ := S.exists_centralizer_bad h45 hH hHM hne hbad
  exact S.false_of_centralizer_bad hB h45 hu2 huM huL hH' hHM' hne' hbad'

end Prop44


end CFSG.GH74.Uniqueness

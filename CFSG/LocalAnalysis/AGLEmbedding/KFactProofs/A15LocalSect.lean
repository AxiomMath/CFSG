module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalPerm
public import CFSG.CharacterTheory.Burnside

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A15Local

open Equiv CFSG.Open

namespace Sect

@[expose] def SectionsOrder60 (U : Type) [Group U] : Prop :=
  ∀ (V X : Type) [Group V] [Group X] (ι : V →* U), Function.Injective ι → IsSimpleGroup X →
    (∃ a b : X, a * b ≠ b * a) → ∀ ψ : V →* X, Function.Surjective ψ → Nat.card X = 60

theorem SectionsOrder60.of_injective {U U' : Type} [Group U] [Group U'] (f : U' →* U)
    (hf : Function.Injective f) (h : SectionsOrder60 U) : SectionsOrder60 U' :=
  fun V X _ _ ι hι hX hna ψ hψ => h V X (f.comp ι) (hf.comp hι) hX hna ψ hψ

theorem false_of_isSolvable {V X : Type} [Group V] [Group X] [Group.IsSolvable V]
    (hX : IsSimpleGroup X) (hna : ∃ a b : X, a * b ≠ b * a) (ψ : V →* X)
    (hψ : Function.Surjective ψ) : False := by
  have hX' : Group.IsSolvable X := Group.isSolvable_of_surjective hψ
  obtain ⟨a, b, hab⟩ := hna
  exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hX' a b)

theorem SectionsOrder60.of_isSolvable {U : Type} [Group U] [Group.IsSolvable U] :
    SectionsOrder60 U := by
  intro V X _ _ ι hι hX hna ψ hψ
  have hV : Group.IsSolvable V := Group.isSolvable_of_isSolvable_injective hι
  exact (false_of_isSolvable hX hna ψ hψ).elim

theorem SectionsOrder60.of_ker {U Q : Type} [Group U] [Group Q] (g : U →* Q)
    (hQ : SectionsOrder60 Q) (hK : SectionsOrder60 g.ker) : SectionsOrder60 U := by
  intro V X _ _ ι hι hX hna ψ hψ
  have hnorm : ((g.comp ι).ker.map ψ).Normal := (MonoidHom.normal_ker (g.comp ι)).map ψ hψ
  rcases hX.eq_bot_or_eq_top_of_normal ((g.comp ι).ker.map ψ) with h | h
  · have hle : (g.comp ι).rangeRestrict.ker ≤ ψ.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro k hk
      have h1 : ψ k ∈ (g.comp ι).ker.map ψ := Subgroup.mem_map_of_mem ψ hk
      rw [h] at h1
      exact Subgroup.mem_bot.1 h1
    let φ : (g.comp ι).range →* X :=
      (MonoidHom.liftOfSurjective (g.comp ι).rangeRestrict
        (g.comp ι).rangeRestrict_surjective) ⟨ψ, hle⟩
    have hφ : ∀ v, φ ((g.comp ι).rangeRestrict v) = ψ v := fun v => by simp [φ]
    refine hQ _ X (g.comp ι).range.subtype (Subgroup.subtype_injective _) hX hna φ ?_
    intro x
    obtain ⟨v, rfl⟩ := hψ x
    exact ⟨(g.comp ι).rangeRestrict v, hφ v⟩
  · let ι₁ : (g.comp ι).ker →* g.ker :=
      (ι.comp (g.comp ι).ker.subtype).codRestrict g.ker (fun k => k.2)
    refine hK _ X ι₁ ?_ hX hna (ψ.comp (g.comp ι).ker.subtype) ?_
    · intro a b hab
      exact Subtype.ext (hι (congrArg Subtype.val hab))
    · intro x
      have hx : x ∈ (g.comp ι).ker.map ψ := by rw [h]; exact Subgroup.mem_top x
      obtain ⟨k, hk, rfl⟩ := hx
      exact ⟨⟨k, hk⟩, rfl⟩

theorem SectionsOrder60.prod {A B : Type} [Group A] [Group B] (hA : SectionsOrder60 A)
    (hB : SectionsOrder60 B) : SectionsOrder60 (A × B) := by
  refine SectionsOrder60.of_ker (MonoidHom.fst A B) hA ?_
  refine hB.of_injective ((MonoidHom.snd A B).comp (MonoidHom.fst A B).ker.subtype) ?_
  intro x y hxy
  refine Subtype.ext (Prod.ext ?_ hxy)
  exact x.2.trans y.2.symm

theorem sectionsOrder60_perm_zmod_three : SectionsOrder60 (Perm (ZMod 3)) :=
  have : Group.IsSolvable (Perm (ZMod 3)) :=
    Equiv.Perm.isSolvable (by rw [Nat.card_zmod]; norm_num)
  SectionsOrder60.of_isSolvable

theorem card_alternatingGroup_fin_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_ne_thirty (H : Subgroup (alternatingGroup (Fin 5))) : Nat.card H ≠ 30 := by
  intro h
  have hindex : H.index = 2 := by
    have := H.card_mul_index
    rw [h, card_alternatingGroup_fin_five] at this
    omega
  have : H.Normal := Subgroup.normal_of_index_eq_two hindex
  rcases Subgroup.Normal.eq_bot_or_eq_top H with h' | h'
  · rw [h', Subgroup.card_bot] at h
    omega
  · rw [h', Subgroup.card_top, card_alternatingGroup_fin_five] at h
    omega

theorem isSolvable_of_ne_top {H : Subgroup (alternatingGroup (Fin 5))} (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  have hdvd : Nat.card H ∣ 60 := card_alternatingGroup_fin_five ▸ H.card_subgroup_dvd_card
  have h60 : Nat.card H ≠ 60 := fun h =>
    hH (Subgroup.eq_top_of_card_eq H (h.trans card_alternatingGroup_fin_five.symm))
  have h30 := card_ne_thirty H
  obtain ⟨p, q, a, b, hp, hq, hpq, hcard⟩ :
      ∃ p q a b : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ Nat.card H = p ^ a * q ^ b := by
    have hmem : Nat.card H ∈ Nat.divisors 60 := Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
    have hdiv : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by decide +kernel
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h
    · exact ⟨2, 3, 0, 0, Nat.prime_two, Nat.prime_three, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 3, 1, 0, Nat.prime_two, Nat.prime_three, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 3, 0, 1, Nat.prime_two, Nat.prime_three, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 3, 2, 0, Nat.prime_two, Nat.prime_three, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 5, 0, 1, Nat.prime_two, Nat.prime_five, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 3, 1, 1, Nat.prime_two, Nat.prime_three, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 5, 1, 1, Nat.prime_two, Nat.prime_five, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 3, 2, 1, Nat.prime_two, Nat.prime_three, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨3, 5, 1, 1, Nat.prime_three, Nat.prime_five, by norm_num, h.trans (by norm_num)⟩
    · exact ⟨2, 5, 2, 1, Nat.prime_two, Nat.prime_five, by norm_num, h.trans (by norm_num)⟩
    · exact absurd h h30
    · exact absurd h h60
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow hp hq hpq
    (by rw [← Nat.card_eq_fintype_card]; exact hcard)

theorem sectionsOrder60_alternatingGroup_fin_five : SectionsOrder60 (alternatingGroup (Fin 5)) := by
  intro V X _ _ ι hι hX hna ψ hψ
  by_cases hsurj : Function.Surjective ι
  · let e : V ≃* alternatingGroup (Fin 5) := MulEquiv.ofBijective ι ⟨hι, hsurj⟩
    have : IsSimpleGroup V := e.isSimpleGroup
    rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with h | h
    · have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 h
      rw [← Nat.card_congr (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩).toEquiv, Nat.card_congr e.toEquiv,
        card_alternatingGroup_fin_five]
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      obtain ⟨a', rfl⟩ := hψ a
      obtain ⟨b', rfl⟩ := hψ b
      have ha : ψ a' = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top a')
      have hb : ψ b' = 1 := MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top b')
      exact hab (by rw [ha, hb])
  · exfalso
    have hrange : ι.range ≠ ⊤ := fun h => hsurj (MonoidHom.range_eq_top.1 h)
    have : Group.IsSolvable ι.range := isSolvable_of_ne_top hrange
    have : Group.IsSolvable V :=
      Group.isSolvable_of_isSolvable_injective (f := (MonoidHom.ofInjective hι).toMonoidHom)
        (MulEquiv.injective _)
    exact false_of_isSolvable hX hna ψ hψ

theorem sectionsOrder60_perm_fin_five : SectionsOrder60 (Perm (Fin 5)) :=
  SectionsOrder60.of_ker Perm.sign SectionsOrder60.of_isSolvable
    sectionsOrder60_alternatingGroup_fin_five

theorem sectionsOrder60_perm_zmod_five : SectionsOrder60 (Perm (ZMod 5)) :=
  sectionsOrder60_perm_fin_five

@[expose] def baseGroup : Subgroup (Perm Pt) where
  carrier := {g | ∀ p : Pt, (g p).1 = p.1}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro g h hg hh p
    exact (hg (h p)).trans (hh p)
  inv_mem' := by
    intro g hg p
    simpa using (hg (g⁻¹ p)).symm

theorem mem_baseGroup_iff {g : Perm Pt} : g ∈ baseGroup ↔ ∀ p : Pt, (g p).1 = p.1 := Iff.rfl

theorem baseGroup_fst_apply {g : Perm Pt} (hg : g ∈ baseGroup) (p : Pt) : (g p).1 = p.1 :=
  mem_baseGroup_iff.1 hg p

theorem baseGroup_apply_eq {g : Perm Pt} (hg : g ∈ baseGroup) (i : ZMod 3) (z : ZMod 5) :
    g (i, z) = (i, (g (i, z)).2) :=
  Prod.ext (baseGroup_fst_apply hg (i, z)) rfl

@[expose] def innerPerm (g : baseGroup) (i : ZMod 3) : Perm (ZMod 5) where
  toFun z := ((g : Perm Pt) (i, z)).2
  invFun z := (((g⁻¹ : baseGroup) : Perm Pt) (i, z)).2
  left_inv z := by
    have h2 : (((g⁻¹ : baseGroup) : Perm Pt)) (((g : Perm Pt)) (i, z)) = (i, z) := by
      simp only [InvMemClass.coe_inv, Perm.coe_inv, Equiv.symm_apply_apply]
    rw [baseGroup_apply_eq g.2 i z] at h2
    exact congrArg Prod.snd h2
  right_inv z := by
    have h2 : ((g : Perm Pt)) ((((g⁻¹ : baseGroup) : Perm Pt)) (i, z)) = (i, z) := by
      simp only [InvMemClass.coe_inv, Perm.coe_inv, Equiv.apply_symm_apply]
    rw [baseGroup_apply_eq (g⁻¹).2 i z] at h2
    exact congrArg Prod.snd h2

@[expose] def innerHom (i : ZMod 3) : baseGroup →* Perm (ZMod 5) where
  toFun g := innerPerm g i
  map_one' := rfl
  map_mul' g h := by
    ext z
    exact congrArg (fun p : Pt => ((g : Perm Pt) p).2) (baseGroup_apply_eq h.2 i z)

theorem eq_one_of_innerHom_eq_one {g : baseGroup} (h0 : innerHom 0 g = 1) (h1 : innerHom 1 g = 1)
    (h2 : innerHom 2 g = 1) : g = 1 := by
  refine Subtype.ext (Equiv.ext fun p => Prod.ext (g.2 p) ?_)
  obtain ⟨i, z⟩ := p
  rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl
  · exact congrArg (fun σ : Perm (ZMod 5) => σ z) h0
  · exact congrArg (fun σ : Perm (ZMod 5) => σ z) h1
  · exact congrArg (fun σ : Perm (ZMod 5) => σ z) h2

@[expose] def innerHom3 : baseGroup →* Perm (ZMod 5) × Perm (ZMod 5) × Perm (ZMod 5) :=
  (innerHom 0).prod ((innerHom 1).prod (innerHom 2))

theorem innerHom3_injective : Function.Injective innerHom3 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have h := Prod.ext_iff.1 hg
  have h' := Prod.ext_iff.1 h.2
  exact eq_one_of_innerHom_eq_one h.1 h'.1 h'.2

theorem sectionsOrder60_baseGroup : SectionsOrder60 baseGroup :=
  (sectionsOrder60_perm_zmod_five.prod
    (sectionsOrder60_perm_zmod_five.prod sectionsOrder60_perm_zmod_five)).of_injective
      innerHom3 innerHom3_injective

@[expose] def blockPerm (g : wr) : Perm (ZMod 3) where
  toFun i := blk (g : Perm Pt) i
  invFun i := blk ((g⁻¹ : wr) : Perm Pt) i
  left_inv i := by
    have h := fst_apply_eq_blk (g⁻¹ : wr).2 ((g : Perm Pt) (i, 0))
    simpa [blk] using h.symm
  right_inv i := by
    have h := fst_apply_eq_blk g.2 (((g⁻¹ : wr) : Perm Pt) (i, 0))
    simpa [blk] using h.symm

theorem fst_apply_eq_blockPerm (g : wr) (p : Pt) : ((g : Perm Pt) p).1 = blockPerm g p.1 :=
  fst_apply_eq_blk g.2 p

theorem blockPerm_mul (g h : wr) : blockPerm (g * h) = blockPerm g * blockPerm h := by
  ext i
  exact fst_apply_eq_blk g.2 ((h : Perm Pt) (i, 0))

theorem blockPerm_one : blockPerm (1 : wr) = 1 := by
  ext i
  rfl

@[expose] def blockHom : wr →* Perm (ZMod 3) where
  toFun := blockPerm
  map_one' := blockPerm_one
  map_mul' := blockPerm_mul

theorem fst_apply_of_mem_ker {h : wr} (hh : h ∈ blockHom.ker) (p : Pt) :
    ((h : Perm Pt) p).1 = p.1 := by
  rw [fst_apply_eq_blockPerm]
  exact congrArg (fun σ : Perm (ZMod 3) => σ p.1) (MonoidHom.mem_ker.1 hh)

@[expose] def kerToBase : blockHom.ker →* baseGroup :=
  ((wr.subtype).comp blockHom.ker.subtype).codRestrict baseGroup
    (fun h => fst_apply_of_mem_ker h.2)

theorem kerToBase_injective : Function.Injective kerToBase := by
  intro a b hab
  have h : ((kerToBase a : baseGroup) : Perm Pt) = ((kerToBase b : baseGroup) : Perm Pt) :=
    congrArg Subtype.val hab
  exact Subtype.ext (Subtype.ext h)

theorem sectionsOrder60_wr : SectionsOrder60 wr :=
  SectionsOrder60.of_ker blockHom sectionsOrder60_perm_zmod_three
    (sectionsOrder60_baseGroup.of_injective kerToBase kerToBase_injective)

end Sect

theorem card_section_of_le_wr {M : Subgroup (Perm Pt)} (hM : M ≤ wr) {U : Subgroup (Perm Pt)}
    (hU : U ≤ M) (V : Subgroup U) [V.Normal] (hs : IsSimpleGroup (U ⧸ V))
    (hna : ∃ a b : U ⧸ V, a * b ≠ b * a) : Nat.card (U ⧸ V) = 60 :=
  Sect.sectionsOrder60_wr U (U ⧸ V) (Subgroup.inclusion (hU.trans hM))
    (Subgroup.inclusion_injective _) hs hna (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)

end CFSG.AGLEmbedding.A15Local

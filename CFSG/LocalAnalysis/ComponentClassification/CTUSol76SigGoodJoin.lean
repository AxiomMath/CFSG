module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigDisc
public import CFSG.LocalAnalysis.ComponentClassification.Sol76SigFourConn
public import CFSG.RankThree.OddKernel.OddLift
public import CFSG.Open.MacWilliamsFourGenerator

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13

@[expose] def InvolutionsFourJoined (Q : Type) [Group Q] : Prop :=
  ∀ E : Subgroup Q, IsKleinFour E → ∀ x : Q, orderOf x = 2 →
    ∃ g : Q, ∃ F : Subgroup Q, IsKleinFour F ∧ g⁻¹ * x * g ∈ F ∧
      Relation.ReflTransGen (CommFourAdj Q) E F

section Conj

variable {X : Type} [Group X]

private theorem isKleinFour_map_inj {X' : Type} [Group X'] {f : X →* X'}
    (hf : Function.Injective f) {V : Subgroup X} (hV : IsKleinFour V) :
    IsKleinFour (V.map f) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun x hx => ?_
  · rw [Subgroup.card_map_of_injective hf, hV.card_four]
  · obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hV hv, map_one]

private theorem isKleinFour_map_conj_join {B : Subgroup X} (hB : IsKleinFour B) (g : X) :
    IsKleinFour (B.map (MulAut.conj g).toMonoidHom) :=
  isKleinFour_map_inj (MulAut.conj g).injective hB

private theorem map_conj_map_conj_join (E : Subgroup X) (g h : X) :
    (E.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      E.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  group

private theorem map_conj_one_join (E : Subgroup X) :
    E.map (MulAut.conj (1 : X)).toMonoidHom = E := by
  ext x
  simp

private theorem exists_map_conj_le_join [Finite X] {E : Subgroup X} (hE : IsPGroup 2 E)
    (S : Sylow 2 X) : ∃ g : X, E.map (MulAut.conj g).toMonoidHom ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P S
  have h : ((g • P : Sylow 2 X) : Subgroup X) =
      (P : Subgroup X).map (MulAut.conj g).toMonoidHom := rfl
  exact ⟨g, by rw [← hg, h]; exact Subgroup.map_mono hP⟩

end Conj

section Joined

variable {Q : Type} [Group Q] [Finite Q]

theorem involutionsFourJoined_of_sylow (hr : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q))
    (S : Sylow 2 Q)
    (hS : ∀ E F : Subgroup Q, IsKleinFour E → E ≤ S → IsKleinFour F → F ≤ S →
      Relation.ReflTransGen (CommFourAdj Q) E F) : InvolutionsFourJoined Q := by
  intro E hE x hx
  obtain ⟨F, -, hF, hxF⟩ := exists_isKleinFour_mem hr (mem_top x) hx
  obtain ⟨a, ha⟩ := exists_map_conj_le_join (isPGroup_of_isKleinFour hE) S
  obtain ⟨b, hb⟩ := exists_map_conj_le_join (isPGroup_of_isKleinFour hF) S
  have h := reflTransGen_commFourAdj_map_conj
    (hS _ _ (isKleinFour_map_conj_join hE a) ha (isKleinFour_map_conj_join hF b) hb) a⁻¹
  rw [map_conj_map_conj_join E a⁻¹ a, inv_mul_cancel, map_conj_one_join E,
    map_conj_map_conj_join F a⁻¹ b] at h
  refine ⟨(a⁻¹ * b)⁻¹, F.map (MulAut.conj (a⁻¹ * b)).toMonoidHom,
    isKleinFour_map_conj_join hF _, ?_, h⟩
  rw [inv_inv]
  exact Subgroup.mem_map.mpr ⟨x, hxF, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩

theorem involutionsFourJoined_of_normal_elemAbelian
    (hr : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q)) (S : Sylow 2 Q) {A : Subgroup Q}
    (hSA : (S : Subgroup Q) ≤ normalizer (A : Set Q)) (hA2 : ∀ a ∈ A, a * a = 1)
    (hA8 : 8 ≤ Nat.card A) : InvolutionsFourJoined Q :=
  involutionsFourJoined_of_sylow hr S fun _ _ hE hES hF hFS =>
    reflTransGen_commFourAdj_of_normal_elemAbelian hSA hA2 hA8 hE hES hF hFS

theorem involutionsFourJoined_of_center (hr : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q))
    {Z : Subgroup Q} (hZ : IsKleinFour Z) (hZc : Z ≤ center Q) : InvolutionsFourJoined Q := by
  intro E hE x hx
  obtain ⟨F, -, hF, hxF⟩ := exists_isKleinFour_mem hr (mem_top x) hx
  refine ⟨1, F, hF, by simpa using hxF, ?_⟩
  have hEZ : CommFourAdj Q E Z := ⟨hE, hZ, fun e _ => mem_centralizer_iff.mpr fun z hz =>
    (mem_center_iff.mp (hZc hz) e).symm⟩
  have hZF : CommFourAdj Q Z F := ⟨hZ, hF, fun z hz => mem_centralizer_iff.mpr fun f _ =>
    mem_center_iff.mp (hZc hz) f⟩
  exact (Relation.ReflTransGen.single hEZ).tail hZF

theorem fourGenerated_of_noNormalEight
    (S : Sylow 2 Q)
    (hS8 : ∀ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) →
      (∀ a ∈ A, a * a = 1) → Nat.card A < 8)
    (P : Subgroup Q) (hP : IsPGroup 2 P) :
    ∃ s : Finset Q, s.card ≤ 4 ∧ Subgroup.closure (s : Set Q) = P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup Q := (S : Subgroup Q) with hT
  have hMW := CFSG.Open.Open.macwilliams_four_generator ↥T S.isPGroup' (fun E hEn hEab hE8 => by
    have hA := hS8 (E.map T.subtype) (fun s hs => ?_) (fun a ha => ?_)
    · rw [Subgroup.card_map_of_injective T.subtype_injective, hE8] at hA
      exact absurd hA (by norm_num)
    · rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨e, he, rfl⟩
        refine ⟨⟨s, hs⟩ * e * ⟨s, hs⟩⁻¹, hEn.conj_mem e he ⟨s, hs⟩, ?_⟩
        simp
      · rintro ⟨e, he, hse⟩
        have hhT : h ∈ T := by
          have e1 : h = s⁻¹ * (e : Q) * s := by
            simp only [Subgroup.coe_subtype] at hse
            rw [hse]
            group
          rw [e1]
          exact mul_mem (mul_mem (inv_mem hs) e.2) hs
        refine ⟨⟨h, hhT⟩, ?_, rfl⟩
        have e2 : (⟨h, hhT⟩ : ↥T) = (⟨s, hs⟩ : ↥T)⁻¹ * e * ((⟨s, hs⟩ : ↥T)⁻¹)⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_subtype] at hse
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
          rw [hse]
          group
        rw [e2]
        exact hEn.conj_mem e he _
    · obtain ⟨e, he, rfl⟩ := ha
      have h2 := hEab.2 e he
      rw [← map_mul, ← sq, h2, map_one])
  obtain ⟨c, hc⟩ := exists_map_conj_le_join hP S
  obtain ⟨X, hXc, hXcl⟩ := hMW ((P.map (MulAut.conj c).toMonoidHom).subgroupOf T)
  refine ⟨(X.image T.subtype).image (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_⟩
  · exact Finset.card_image_le.trans (Finset.card_image_le.trans hXc)
  · rw [Finset.coe_image, Finset.coe_image, ← MonoidHom.map_closure, ← MonoidHom.map_closure,
      hXcl, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hc, map_conj_map_conj_join,
      inv_mul_cancel, map_conj_one_join]

omit [Finite Q] in
theorem reflTransGen_commFourAdj_of_center {Z : Subgroup Q} (hZ : IsKleinFour Z)
    (hZc : Z ≤ center Q) {E F : Subgroup Q} (hE : IsKleinFour E) (hF : IsKleinFour F) :
    Relation.ReflTransGen (CommFourAdj Q) E F := by
  have hEZ : CommFourAdj Q E Z := ⟨hE, hZ, fun e _ => mem_centralizer_iff.mpr fun z hz =>
    (mem_center_iff.mp (hZc hz) e).symm⟩
  have hZF : CommFourAdj Q Z F := ⟨hZ, hF, fun z hz => mem_centralizer_iff.mpr fun f _ =>
    mem_center_iff.mp (hZc hz) f⟩
  exact (Relation.ReflTransGen.single hEZ).tail hZF

@[expose] def QuasisimpleSylowFourJoinedSCN : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
    Blueprint.Catalog (Q ⧸ center Q) → 3 ≤ CFSG.pRank 2 Q →
    (∀ Z : Subgroup Q, Z ≤ center Q → ¬ IsKleinFour Z) →
    ∀ S : Sylow 2 Q, (∀ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) →
      (∀ a ∈ A, a * a = 1) → Nat.card A < 8) →
    (∀ P : Subgroup Q, IsPGroup 2 P →
      ∃ s : Finset Q, s.card ≤ 4 ∧ Subgroup.closure (s : Set Q) = P) →
    ∀ E F : Subgroup Q, IsKleinFour E → E ≤ S → IsKleinFour F → F ≤ S →
      Relation.ReflTransGen (CommFourAdj Q) E F

theorem sylowFourJoined_of_SCN
    (h : QuasisimpleSylowFourJoinedSCN)
    (hQq : IsQuasisimple Q) (hQO : pPrimeCore 2 Q = ⊥) (hQcat : Blueprint.Catalog (Q ⧸ center Q))
    (hQr : 3 ≤ CFSG.pRank 2 Q) (S : Sylow 2 Q) {E F : Subgroup Q} (hE : IsKleinFour E)
    (hES : E ≤ S) (hF : IsKleinFour F) (hFS : F ≤ S) :
    Relation.ReflTransGen (CommFourAdj Q) E F := by
  by_cases h8 : ∃ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) ∧
      (∀ a ∈ A, a * a = 1) ∧ 8 ≤ Nat.card A
  · obtain ⟨A, hSA, hA2, hA8⟩ := h8
    exact reflTransGen_commFourAdj_of_normal_elemAbelian hSA hA2 hA8 hE hES hF hFS
  by_cases hZ : ∃ Z : Subgroup Q, Z ≤ center Q ∧ IsKleinFour Z
  · obtain ⟨Z, hZc, hZ⟩ := hZ
    exact reflTransGen_commFourAdj_of_center hZ hZc hE hF
  have hS8 : ∀ A : Subgroup Q, (S : Subgroup Q) ≤ normalizer (A : Set Q) →
      (∀ a ∈ A, a * a = 1) → Nat.card A < 8 := fun A hSA hA2 => by
    by_contra hlt
    exact h8 ⟨A, hSA, hA2, by omega⟩
  exact h Q hQq hQO hQcat hQr (fun Z hZc hZ' => hZ ⟨Z, hZc, hZ'⟩) S hS8
    (fourGenerated_of_noNormalEight S hS8) E F hE hES hF hFS

theorem involutionsFourJoined_of_SCN
    (h : QuasisimpleSylowFourJoinedSCN)
    (hQq : IsQuasisimple Q) (hQO : pPrimeCore 2 Q = ⊥) (hQcat : Blueprint.Catalog (Q ⧸ center Q))
    (hQr : 3 ≤ CFSG.pRank 2 Q) : InvolutionsFourJoined Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Q) := by
    rw [← SectionRank.pRank_eq_open_pRank_top]
    omega
  obtain ⟨S⟩ : Nonempty (Sylow 2 Q) := inferInstance
  exact involutionsFourJoined_of_sylow hr S fun _ _ hE hES hF hFS =>
    sylowFourJoined_of_SCN h hQq hQO hQcat hQr S hE hES hF hFS

end Joined

section Lift

variable {Y Q : Type} [Group Y] [Finite Y] [Group Q]

theorem exists_pSubgroup_lift_of_surjective {p : ℕ} [Fact p.Prime] (ψ : Y →* Q)
    (hψ : Function.Surjective ψ) {A₀ : Subgroup Y} (hA₀ : IsPGroup p A₀) {E : Subgroup Q}
    (hE : IsPGroup p E) (hAE : A₀.map ψ ≤ E) :
    ∃ P : Subgroup Y, IsPGroup p P ∧ A₀ ≤ P ∧ P.map ψ = E := by
  classical
  set M : Subgroup Y := E.comap ψ with hM
  have hA₀M : A₀ ≤ M := fun a ha => hAE ⟨a, ha, rfl⟩
  let f : ↥M →* Q := ψ.comp M.subtype
  have hfrange : f.range = E := by
    ext e
    constructor
    · rintro ⟨m, rfl⟩
      exact m.2
    · intro he
      obtain ⟨c, rfl⟩ := hψ e
      exact ⟨⟨c, he⟩, rfl⟩
  have hA₀' : IsPGroup p (A₀.subgroupOf M) := hA₀.comap_subtype
  obtain ⟨P₀, hP₀⟩ := hA₀'.exists_le_sylow
  set Q₀ : Subgroup ↥M := (P₀ : Subgroup ↥M) with hQ₀
  refine ⟨Q₀.map M.subtype, P₀.2.map _, ?_, ?_⟩
  · intro a ha
    exact ⟨⟨a, hA₀M ha⟩, hP₀ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  · have hpf : IsPGroup p f.range := by
      intro x
      obtain ⟨k, hk⟩ := hE ⟨x.1, by rw [← hfrange]; exact x.2⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hf' : Function.Surjective f.rangeRestrict := MonoidHom.rangeRestrict_surjective f
    have hT := (P₀.mapSurjective hf').is_maximal' (Q := ⊤) (hpf.to_subgroup ⊤) le_top
    have hmap : Q₀.map f.rangeRestrict = ⊤ := hT.symm
    have hf'' : f = f.range.subtype.comp f.rangeRestrict := by ext; rfl
    have key : Q₀.map f = f.range := by
      calc Q₀.map f = (Q₀.map f.rangeRestrict).map f.range.subtype := by
            rw [Subgroup.map_map, ← hf'']
        _ = (⊤ : Subgroup f.range).map f.range.subtype := by rw [hmap]
        _ = f.range := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    calc (Q₀.map M.subtype).map ψ = Q₀.map f := by rw [Subgroup.map_map]
      _ = f.range := key
      _ = E := hfrange

theorem isKleinFour_map_of_odd_ker (ψ : Y →* Q) (hker : Odd (Nat.card ψ.ker)) {E : Subgroup Y}
    (hE : IsKleinFour E) : IsKleinFour (E.map ψ) := by
  have hinj := CFSG.RankThree.OddKernel.injective_restrict_of_odd ψ hker
    (isPGroup_of_isKleinFour hE)
  have he : E.map ψ = (⊤ : Subgroup E).map (ψ.comp E.subtype) := by
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun y hy => ?_
  · rw [he, Subgroup.card_map_of_injective hinj, Subgroup.card_top, hE.card_four]
  · obtain ⟨e, heE, rfl⟩ := hy
    rw [← map_pow, FooteLit.sq_eq_one_of_isKleinFour hE heE, map_one]

theorem exists_lift_commFourAdj (ψ : Y →* Q) (hψ : Function.Surjective ψ)
    (hker : Odd (Nat.card ψ.ker)) {F : Subgroup Y} (hF : IsKleinFour F) {Cb : Subgroup Q}
    (h : CommFourAdj Q (F.map ψ) Cb) :
    ∃ C : Subgroup Y, IsKleinFour C ∧ C.map ψ = Cb ∧ CommFourAdj Y F C := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hFb, hCb, hFC⟩ := h
  have hD : IsPGroup 2 (F.map ψ ⊔ Cb : Subgroup Q) :=
    (isPGroup_of_isKleinFour hFb).to_sup_of_normal_right' (isPGroup_of_isKleinFour hCb)
      (hFC.trans (Subgroup.centralizer_le_normalizer (Cb : Set Q)))
  obtain ⟨P, hP2, hFP, hPmap⟩ := exists_pSubgroup_lift_of_surjective ψ hψ
    (isPGroup_of_isKleinFour hF) hD le_sup_left
  have hinj := CFSG.RankThree.OddKernel.injective_restrict_of_odd ψ hker hP2
  have hinjP : ∀ a ∈ P, ∀ b ∈ P, ψ a = ψ b → a = b := fun a ha b hb hab =>
    congrArg Subtype.val (hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  set C : Subgroup Y := P ⊓ Cb.comap ψ with hCdef
  have hCmap : C.map ψ = Cb := by
    refine le_antisymm ?_ fun c hc => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · have hcD : c ∈ P.map ψ := by
        rw [hPmap]
        exact mem_sup_right hc
      obtain ⟨y, hyP, rfl⟩ := hcD
      exact ⟨y, ⟨hyP, hc⟩, rfl⟩
  have hC4 : IsKleinFour C := by
    refine FooteLit.isKleinFour_of_card_eq_four ?_ fun y hy => ?_
    · have hinjC : Function.Injective (ψ.comp C.subtype) := fun a b hab =>
        Subtype.ext (hinjP a a.2.1 b b.2.1 hab)
      have he : C.map ψ = (⊤ : Subgroup C).map (ψ.comp C.subtype) := by
        rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [← Subgroup.card_top (G := C), ← Subgroup.card_map_of_injective hinjC, ← he, hCmap,
        hCb.card_four]
    · refine hinjP _ (pow_mem hy.1 2) 1 (one_mem P) ?_
      rw [map_pow, map_one]
      exact FooteLit.sq_eq_one_of_isKleinFour hCb hy.2
  refine ⟨C, hC4, hCmap, hF, hC4, ?_⟩
  · intro f hf
    rw [mem_centralizer_iff]
    intro c hc
    refine hinjP _ (mul_mem hc.1 (hFP hf)) _ (mul_mem (hFP hf) hc.1) ?_
    rw [map_mul, map_mul]
    exact mem_centralizer_iff.mp (hFC ⟨f, hf, rfl⟩) (ψ c) hc.2

theorem exists_lift_reflTransGen_commFourAdj (ψ : Y →* Q) (hψ : Function.Surjective ψ)
    (hker : Odd (Nat.card ψ.ker)) {E : Subgroup Y} (hE : IsKleinFour E) {Fb : Subgroup Q}
    (h : Relation.ReflTransGen (CommFourAdj Q) (E.map ψ) Fb) :
    ∃ F : Subgroup Y, IsKleinFour F ∧ F.map ψ = Fb ∧
      Relation.ReflTransGen (CommFourAdj Y) E F := by
  induction h with
  | refl => exact ⟨E, hE, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hbc ih =>
    obtain ⟨F, hF, hFmap, hEF⟩ := ih
    obtain ⟨C, hC, hCmap, hFC⟩ := exists_lift_commFourAdj ψ hψ hker hF (by rw [hFmap]; exact hbc)
    exact ⟨C, hC, hCmap, hEF.tail hFC⟩

end Lift

variable {G : Type} [Group G] [Finite G] {N K : Subgroup G}

omit [Finite G] in
theorem reflTransGen_commFourIn_of_subtype {X : Subgroup G} {A C : Subgroup ↥X}
    (h : Relation.ReflTransGen (CommFourAdj ↥X) A C) :
    Relation.ReflTransGen (CommFourIn X) (A.map X.subtype) (C.map X.subtype) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
    refine ih.tail ⟨isKleinFour_map_inj X.subtype_injective hbc.1,
      isKleinFour_map_inj X.subtype_injective hbc.2.1, map_subtype_le _, map_subtype_le _, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨c, hc, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hbc.2.2 ha) c hc)

theorem exists_conj_mem_zpowers_of_mk_eq {x v : G} (hxK : x ∈ K) (hx2 : orderOf x = 2)
    (hvK : v ∈ K) {gbar : coreQuot K}
    (h : QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨v, hvK⟩ : ↥K) =
      gbar⁻¹ * QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨x, hxK⟩ : ↥K) * gbar) :
    ∃ g ∈ K, g⁻¹ * x * g ∈ zpowers v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) gbar
  set y : G := (g : G)⁻¹ * x * g with hy
  have hyK : y ∈ K := mul_mem (mul_mem (inv_mem g.2) hxK) g.2
  have hvy : QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨v, hvK⟩ : ↥K) =
      QuotientGroup.mk' (pPrimeCore 2 ↥K) (⟨y, hyK⟩ : ↥K) := by
    rw [h]
    have e : (⟨y, hyK⟩ : ↥K) = g⁻¹ * ⟨x, hxK⟩ * g := rfl
    rw [e, map_mul, map_mul, map_inv]
  have hvy' : v⁻¹ * y ∈ oddCoreIn K := (mk_eq_mk_iff (N := K)).mp hvy
  have hy2 : orderOf y = 2 := by
    have h' := orderOf_injective (MulAut.conj (g : G)⁻¹).toMonoidHom
      (MulAut.conj (g : G)⁻¹).injective x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h'
    rw [hy, h', hx2]
  have hOK : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hvO : zpowers v ≤ normalizer (oddCoreIn K : Set G) :=
    zpowers_le.mpr (le_normalizer_oddCoreIn K hvK)
  have hyM : zpowers y ≤ zpowers v ⊔ oddCoreIn K := zpowers_le.mpr (by
    have e : y = v * (v⁻¹ * y) := by group
    rw [e]
    exact mul_mem (mem_sup_left (mem_zpowers _)) (mem_sup_right hvy'))
  have hy2' : IsPGroup 2 (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  obtain ⟨m, hmM, hm⟩ := exists_conj_le_of_sup_odd le_sup_left hvO hOK rfl hyM hy2'
  have hmK : m ∈ K := sup_le (zpowers_le.mpr hvK) (map_subtype_le _) hmM
  have hmy : m * y * m⁻¹ ∈ zpowers v := by
    have h' := hm ⟨y, mem_zpowers y, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h'
  refine ⟨(g : G) * m⁻¹, mul_mem g.2 (inv_mem hmK), ?_⟩
  have e : ((g : G) * m⁻¹)⁻¹ * x * ((g : G) * m⁻¹) = m * y * m⁻¹ := by
    rw [hy]
    group
  rw [e]
  exact hmy

abbrev coverQuot (K U : Subgroup G) : ↥(K ⊓ centralizer (U : Set G)) →* coreQuot K :=
  (QuotientGroup.mk' (pPrimeCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left)

theorem coverQuot_surjective {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hUQ : U ≤ coreActionKernel K) : Function.Surjective (coverQuot K U) := by
  classical
  set X := K ⊓ centralizer (U : Set G) with hXdef
  have hsup : X ⊔ oddCoreIn K = K := inf_centralizer_sup_oddCoreIn_eq hU2 hUQ
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥K) q
  have hkY : (k : G) ∈ ((X ⊔ oddCoreIn K : Subgroup G) : Set G) := by
    rw [hsup]
    exact k.2
  rw [coe_mul_of_left_le_normalizer_right _ _
    (inf_le_left.trans (le_normalizer_oddCoreIn K))] at hkY
  obtain ⟨c, hcX, o, hoO, hco⟩ := hkY
  refine ⟨⟨c, hcX⟩, ?_⟩
  change QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨c, hcX.1⟩ = QuotientGroup.mk' (pPrimeCore 2 ↥K) k
  refine mk_eq_mk_iff.mpr ?_
  have e : c⁻¹ * (k : G) = o := by
    rw [← hco]
    group
  rw [e]
  exact hoO

theorem coverQuot_ker_odd (U : Subgroup G) : Odd (Nat.card (coverQuot K U).ker) := by
  have hO : Odd (Nat.card (oddCoreIn K)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn K)
  have hle : (coverQuot K U).ker.map (K ⊓ centralizer (U : Set G)).subtype ≤ oddCoreIn K := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨(y : G), y.2.1⟩ = 1 := hy
    exact mk_eq_one_iff.mp h1
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective (K ⊓ centralizer (U : Set G)).subtype_injective] at hdvd
  exact Odd.of_dvd_nat hO hdvd

omit [Finite G] in
theorem isKleinFour_subgroupOf {X E : Subgroup G} (hE : IsKleinFour E) (hEX : E ≤ X) :
    IsKleinFour (E.subgroupOf X) := by
  refine FooteLit.isKleinFour_of_card_eq_four ?_ fun y hy => Subtype.ext ?_
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv, hE.card_four]
  · rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact Sig.sq_eq_one_of_isKleinFour hE hy

theorem false_of_disc_of_joined {K' V B H : Subgroup G} (hP : SigPair N K K' V B)
    (hJ : InvolutionsFourJoined (coreQuot K)) (hKH : K ≤ H) {x : G} (hxK : x ∈ K)
    (hx2 : orderOf x = 2)
    (hdisc : ∀ g ∈ H, ∀ U E F : Subgroup G, IsKleinFour U →
      U ≤ K' ⊓ centralizer (B : Set G) → IsKleinFour E → E ≤ B → E ≤ K → IsKleinFour F →
      F ≤ K ⊓ centralizer (U : Set G) → g⁻¹ * x * g ∈ F →
      ¬ Relation.ReflTransGen (CommFourIn (K ⊓ centralizer (U : Set G))) E F) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK, hK', hne, -, -, hBQ, -, hB, -, -, E, hE, hEB, hEK⟩ := hP
  have hB2 : IsPGroup 2 B := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup 2 B hB
  obtain ⟨U, hU, hUY⟩ := exists_isKleinFour_inf_centralizer hK' hB2 hBQ
  have hUQ : U ≤ coreActionKernel K :=
    (hUY.trans inf_le_left).trans (le_coreActionKernel_of_ne hK hK' hne)
  set X := K ⊓ centralizer (U : Set G) with hXdef
  have hEX : E ≤ X := le_inf hEK fun e he =>
    mem_centralizer_iff.mpr fun u hu => ((mem_centralizer_iff.mp (hUY hu).2) e (hEB he)).symm
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥K) with hπ
  set ψ := coverQuot K U with hψ
  have hψs : Function.Surjective ψ := coverQuot_surjective (isPGroup_of_isKleinFour hU) hUQ
  have hker : Odd (Nat.card ψ.ker) := coverQuot_ker_odd U
  have hEY : IsKleinFour (E.subgroupOf X) := isKleinFour_subgroupOf hE hEX
  have hx2' : orderOf (π ⟨x, hxK⟩) = 2 :=
    Sig.orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hx2)
  obtain ⟨gbar, Fbar, -, hmem, hchain⟩ := hJ _ (isKleinFour_map_of_odd_ker ψ hker hEY) _ hx2'
  obtain ⟨F, hF, hFmap, hEF⟩ := exists_lift_reflTransGen_commFourAdj ψ hψs hker hEY hchain
  set F' := F.map X.subtype with hF'
  have hF'4 : IsKleinFour F' := isKleinFour_map_inj X.subtype_injective hF
  have hF'X : F' ≤ X := map_subtype_le _
  have hEF' : Relation.ReflTransGen (CommFourIn X) E F' := by
    have h := reflTransGen_commFourIn_of_subtype hEF
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hEX] at h
  rw [← hFmap] at hmem
  obtain ⟨v, hvF, hv⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨g, hgK, hg⟩ := exists_conj_mem_zpowers_of_mk_eq hxK hx2 v.2.1 (gbar := gbar) hv
  have hvF' : (v : G) ∈ F' := Subgroup.mem_map.mpr ⟨v, hvF, rfl⟩
  have hgF : g⁻¹ * x * g ∈ F' := (zpowers_le.mpr hvF') hg
  exact hdisc g (hKH hgK) U E F' hU hUY hE hEB hEK hF'4 hF'X hgF hEF'

theorem goodInvolutionsLeftDiscThreeAt_of_joined
    (hJ : ∀ (Q : Type) [Group Q] [Finite Q], IsQuasisimple Q → pPrimeCore 2 Q = ⊥ →
      Blueprint.Catalog (Q ⧸ center Q) → 3 ≤ CFSG.pRank 2 Q → ¬ InvolutionsFourCover Q →
      InvolutionsFourJoined Q) (R : SigOrientation) : GoodInvolutionsLeftDiscThreeAt R := by
  intro G _ _ hG N hN h2 K K' V B hP hR hW h3 hcov hKH x hx hx2 hdisc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := hP.1
  refine (false_of_disc_of_joined hP (hJ _ (isQuasisimple_quotient_of_isPComponent hK.1.1 hK.1.2)
    (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥K) 2)
    (catalog_coreQuotient_of_mem_solomonKStar (kStarKProper_of_simpleAmbient hG) hK.1 hK.2) ?_
    hcov) (hKH K hK) hx hx2 hdisc).elim
  rw [FooteLit.pRank_quotient_pPrimeCore, pRank_coe_eq]
  exact h3

theorem goodInvolutionsLeftDiscThreeAt_of_SCN
    (h : QuasisimpleSylowFourJoinedSCN) (R : SigOrientation) :
    GoodInvolutionsLeftDiscThreeAt R :=
  goodInvolutionsLeftDiscThreeAt_of_joined (fun _ _ _ hq hO hc hr _ =>
    involutionsFourJoined_of_SCN h hq hO hc hr) R

end CFSG.ComponentClassification.Sol76.Sig

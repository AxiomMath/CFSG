module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineCF

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.AGLEmbedding CFSG.Quasithin CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise

theorem exists_sec_of_le_iSup {Γ : Type*} [Group Γ] {S : Type*} [Group S] [hS : IsSimpleGroup S]
    (F : Finset (Subgroup Γ))
    (hcomm : ∀ L ∈ F, ∀ L' ∈ F, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) :
    ∀ Ā : Subgroup Γ, Ā ≤ (⨆ L ∈ F, L : Subgroup Γ) → ∀ f : ↥Ā →* S, Function.Surjective f →
      ∃ L ∈ F, ∃ (A' : Subgroup Γ) (f' : ↥A' →* S), A' ≤ L ∧ Function.Surjective f' := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro Ā hĀ f hf
    exfalso
    have hbot : (⨆ L ∈ (∅ : Finset (Subgroup Γ)), L : Subgroup Γ) = ⊥ := by simp
    rw [hbot, le_bot_iff] at hĀ
    obtain ⟨s, t, hst⟩ := hS.toNontrivial.exists_pair_ne
    obtain ⟨a, rfl⟩ := hf s
    obtain ⟨b, rfl⟩ := hf t
    apply hst
    have : a = b := Subtype.ext (by
      rw [(Subgroup.eq_bot_iff_forall Ā).1 hĀ a a.2, (Subgroup.eq_bot_iff_forall Ā).1 hĀ b b.2])
    rw [this]
  | insert L₀ F hL₀F ih =>
    intro Ā hĀ f hf
    have hcommF : ∀ L ∈ F, ∀ L' ∈ F, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a :=
      fun L hL L' hL' => hcomm L (Finset.mem_insert_of_mem hL) L' (Finset.mem_insert_of_mem hL')
    set E : Subgroup Γ := ⨆ L ∈ F, L with hEdef
    have hLE : ∀ l ∈ L₀, ∀ e ∈ E, l * e = e * l := by
      intro l hl e he
      have hle : E ≤ Subgroup.centralizer ({l} : Set Γ) := by
        refine iSup₂_le fun L hL v hv => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcomm L (Finset.mem_insert_of_mem hL) L₀ (Finset.mem_insert_self _ _)
          (fun h => hL₀F (h ▸ hL)) v hv l hl
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he)).symm
    rw [Finset.iSup_insert] at hĀ
    have hL₀cent : L₀ ≤ Subgroup.centralizer (E : Set Γ) := fun l hl =>
      Subgroup.mem_centralizer_iff.2 fun e he => (hLE l hl e he).symm
    have hmul : ((L₀ ⊔ E : Subgroup Γ) : Set Γ) = (L₀ : Set Γ) * (E : Set Γ) :=
      Subgroup.coe_mul_of_left_le_normalizer_right L₀ E
        (hL₀cent.trans (Subgroup.centralizer_le_normalizer _))
    have hconjE : ∀ e ∈ E, ∀ y ∈ L₀, e * y * e⁻¹ = y := by
      intro e he y hy
      have := hLE y hy e he
      rw [← this]; group
    have heN : ∀ e ∈ E, e ∈ Subgroup.normalizer (L₀ : Set Γ) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun hy => by rw [hconjE e he y hy]; exact hy, fun h => ?_⟩
      have := hconjE e⁻¹ (E.inv_mem he) _ h
      have e1 : e⁻¹ * (e * y * e⁻¹) * e⁻¹⁻¹ = y := by group
      rw [e1] at this
      rw [this]; exact h
    have hĀN : Ā ≤ Subgroup.normalizer (L₀ : Set Γ) := by
      intro x hx
      have hx' : x ∈ ((L₀ ⊔ E : Subgroup Γ) : Set Γ) := hĀ hx
      rw [hmul] at hx'
      obtain ⟨l, hl, e, he, rfl⟩ := hx'
      exact mul_mem (Subgroup.le_normalizer hl) (heN e he)
    have hĀ₀n : ((Ā ⊓ L₀).subgroupOf Ā).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro a ha
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ha, hĀN ha⟩
    have hmapn : (((Ā ⊓ L₀).subgroupOf Ā).map f).Normal := hĀ₀n.map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((Ā ⊓ L₀).subgroupOf Ā).map f) with h | h
    ·
      have hker : (Ā ⊓ L₀).subgroupOf Ā ≤ f.ker := by
        intro x hx
        have : f x ∈ ((Ā ⊓ L₀).subgroupOf Ā).map f := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact this
      set Z : Subgroup Γ := Ā ⊔ L₀ with hZ
      have hZN : Z ≤ Subgroup.normalizer (L₀ : Set Γ) := sup_le hĀN Subgroup.le_normalizer
      have hL₀Z : L₀ ≤ Z := le_sup_right
      have hĀZ : Ā ≤ Z := le_sup_left
      have hZn : (L₀.subgroupOf Z).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hL₀Z).2 hZN
      have hmulZ : (Z : Set Γ) = (Ā : Set Γ) * (L₀ : Set Γ) :=
        Subgroup.coe_mul_of_left_le_normalizer_right Ā L₀ hĀN
      set α : ↥Ā →* ↥Z ⧸ L₀.subgroupOf Z :=
        (QuotientGroup.mk' (L₀.subgroupOf Z)).comp (Subgroup.inclusion hĀZ) with hα
      have hαs : Function.Surjective α := by
        intro q
        obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
        have hz' : (z : Γ) ∈ (Z : Set Γ) := z.2
        rw [hmulZ] at hz'
        obtain ⟨a, ha, l, hl, hal⟩ := hz'
        refine ⟨⟨a, ha⟩, ?_⟩
        show (QuotientGroup.mk (Subgroup.inclusion hĀZ ⟨a, ha⟩) : ↥Z ⧸ L₀.subgroupOf Z) =
          QuotientGroup.mk z
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have : ((Subgroup.inclusion hĀZ ⟨a, ha⟩)⁻¹ * z : ↥Z) = ⟨l, hL₀Z hl⟩ := by
          apply Subtype.ext
          simp [← hal]
        rw [this]
        exact hl
      have hkerα : α.ker ≤ f.ker := by
        intro x hx
        apply hker
        rw [MonoidHom.mem_ker, hα, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hx
        exact ⟨x.2, hx⟩
      obtain ⟨φ, hφ, hφs, -⟩ := exists_surjective_comp_eq α hαs f hf hkerα
      set β : ↥(E ⊓ Z) →* ↥Z ⧸ L₀.subgroupOf Z :=
        (QuotientGroup.mk' (L₀.subgroupOf Z)).comp (Subgroup.inclusion inf_le_right) with hβ
      have hβs : Function.Surjective β := by
        intro q
        obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
        have hz' : (z : Γ) ∈ (Z : Set Γ) := z.2
        rw [hmulZ] at hz'
        obtain ⟨a, ha, l, hl, hal⟩ := hz'
        have ha' : a ∈ ((L₀ ⊔ E : Subgroup Γ) : Set Γ) := hĀ ha
        rw [hmul] at ha'
        obtain ⟨l', hl', e, he, hle⟩ := ha'
        have hze : (z : Γ) = e * (l' * l) := by
          rw [← hal, ← hle]
          have := hLE l' hl' e he
          calc l' * e * l = (l' * e) * l := rfl
            _ = (e * l') * l := by rw [this]
            _ = e * (l' * l) := by group
        have heZ : e ∈ Z := by
          have : e = (z : Γ) * (l' * l)⁻¹ := by rw [hze]; group
          rw [this]
          exact Z.mul_mem z.2 (Z.inv_mem (Z.mul_mem (hL₀Z hl') (hL₀Z hl)))
        refine ⟨⟨e, he, heZ⟩, ?_⟩
        show (QuotientGroup.mk (Subgroup.inclusion inf_le_right ⟨e, he, heZ⟩) :
          ↥Z ⧸ L₀.subgroupOf Z) = QuotientGroup.mk z
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have : ((Subgroup.inclusion (inf_le_right : E ⊓ Z ≤ Z) ⟨e, he, heZ⟩)⁻¹ * z : ↥Z) =
            ⟨l' * l, hL₀Z (L₀.mul_mem hl' hl)⟩ := by
          apply Subtype.ext
          simp [hze]
        rw [this]
        exact L₀.mul_mem hl' hl
      have hgs : Function.Surjective (φ.comp β) := hφs.comp hβs
      obtain ⟨L, hL, A', f', hA'L, hf'⟩ := ih hcommF (E ⊓ Z) inf_le_left (φ.comp β) hgs
      exact ⟨L, Finset.mem_insert_of_mem hL, A', f', hA'L, hf'⟩
    ·
      refine ⟨L₀, Finset.mem_insert_self _ _, Ā ⊓ L₀, f.comp (Subgroup.inclusion inf_le_left),
        inf_le_right, fun s => ?_⟩
      have hs : s ∈ ((Ā ⊓ L₀).subgroupOf Ā).map f := by rw [h]; exact Subgroup.mem_top s
      obtain ⟨a, ha, rfl⟩ := hs
      exact ⟨⟨a, ha⟩, rfl⟩

theorem exists_sec_of_cover {X : Type*} [Group X] {S : Type} [Group S] {A B H₁ : Subgroup X}
    (hB : B.Normal) (hcov : A ≤ B ⊔ (A ⊓ H₁))
    (hS : E1.IsCompositionFactor (↥A ⧸ B.subgroupOf A) S) :
    ∃ (A'' : Subgroup X) (f : ↥A'' →* S), A'' ≤ A ⊓ H₁ ∧ Function.Surjective f ∧
      ∀ a : ↥A'', (a : X) ∈ B → f a = 1 := by
  have : (B.subgroupOf A).Normal := hB.subgroupOf A
  obtain ⟨N, M, hNM, hNMle, -, -, hsimp, ⟨e⟩⟩ := hS
  set g₀ : ↥M →* S := e.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf M)) with hg₀def
  have hg₀ : Function.Surjective g₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  set ρ : ↥(A ⊓ H₁) →* (↥A ⧸ B.subgroupOf A) :=
    (QuotientGroup.mk' (B.subgroupOf A)).comp (Subgroup.inclusion inf_le_left) with hρdef
  have hρ : Function.Surjective ρ := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨b, hb, h, hh, hbh⟩ := Subgroup.mem_sup_of_normal_left.mp (hcov a.2)
    refine ⟨⟨h, hh⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion inf_le_left ⟨h, hh⟩) : ↥A ⧸ B.subgroupOf A) =
      QuotientGroup.mk a
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hab : (a : X) = b * h := hbh.symm
    have e1 : ((Subgroup.inclusion (inf_le_left : A ⊓ H₁ ≤ A) ⟨h, hh⟩)⁻¹ * a : ↥A).1 =
        h⁻¹ * (a : X) := rfl
    rw [e1, hab]
    have : h⁻¹ * (b * h) = h⁻¹ * b * h := by group
    rw [this]
    simpa using hB.conj_mem b hb h⁻¹
  set M'' : Subgroup ↥(A ⊓ H₁) := M.comap ρ with hM''
  set f'' : ↥M'' →* S := g₀.comp (ρ.subgroupComap M) with hf''def
  have hf'' : Function.Surjective f'' := hg₀.comp (MonoidHom.subgroupComap_surjective ρ M hρ)
  let eqv : ↥M'' ≃* ↥(M''.map (A ⊓ H₁).subtype) :=
    Subgroup.equivMapOfInjective M'' (A ⊓ H₁).subtype (A ⊓ H₁).subtype_injective
  refine ⟨M''.map (A ⊓ H₁).subtype, f''.comp eqv.symm.toMonoidHom,
    Subgroup.map_subtype_le M'', ?_, ?_⟩
  · exact hf''.comp eqv.symm.surjective
  · intro a haB
    obtain ⟨m, rfl⟩ := eqv.surjective a
    show f'' (eqv.symm (eqv m)) = 1
    rw [MulEquiv.symm_apply_apply]
    have hmB : ((m : ↥(A ⊓ H₁)) : X) ∈ B := haB
    have h1 : ρ (m : ↥(A ⊓ H₁)) = 1 := by
      show (QuotientGroup.mk (Subgroup.inclusion (inf_le_left : A ⊓ H₁ ≤ A) (m : ↥(A ⊓ H₁))) :
        ↥A ⧸ B.subgroupOf A) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hmB
    have h2 : ρ.subgroupComap M m = 1 := Subtype.ext h1
    show g₀ (ρ.subgroupComap M m) = 1
    rw [h2, map_one]


theorem isSimpleGroup_of_isCompositionFactor {G : Type*} [Group G] {S : Type*} [Group S]
    (h : E1.IsCompositionFactor G S) : IsSimpleGroup S := by
  obtain ⟨N, M, hNM, -, -, -, hs, ⟨e⟩⟩ := h
  have := hNM
  have := hs
  exact e.symm.isSimpleGroup

theorem exists_sec_of_isCompositionFactor_of_le {X : Type*} [Group X] {Y Z : Subgroup X}
    {S : Type} [Group S] (h : E1.IsCompositionFactor ↥Y S) (hYZ : Y ≤ Z) :
    ∃ (A : Subgroup X) (f : ↥A →* S), A ≤ Z ∧ Function.Surjective f := by
  obtain ⟨N, M, hNM, -, -, -, hs, ⟨e⟩⟩ := h
  set g₀ : ↥M →* S := e.toMonoidHom.comp (QuotientGroup.mk' (N.subgroupOf M))
  have hg₀ : Function.Surjective g₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let eqv : ↥M ≃* ↥(M.map Y.subtype) :=
    Subgroup.equivMapOfInjective M Y.subtype Y.subtype_injective
  exact ⟨M.map Y.subtype, g₀.comp eqv.symm.toMonoidHom,
    (Subgroup.map_subtype_le M).trans hYZ, hg₀.comp eqv.symm.surjective⟩

theorem exists_sec_lift_of_le_image {X Y' : Type*} [Group X] [Group Y'] (φ : X →* Y')
    {H₁ : Subgroup X} {A' : Subgroup Y'} {S : Type*} [Group S] (hA' : A' ≤ H₁.map φ)
    (f' : ↥A' →* S) (hf' : Function.Surjective f') :
    ∃ (Ã : Subgroup X) (g : ↥Ã →* S), Ã ≤ H₁ ∧ Function.Surjective g := by
  set Ã : Subgroup X := H₁ ⊓ A'.comap φ with hÃ
  set ρ : ↥Ã →* ↥A' := (φ.comp Ã.subtype).codRestrict A' (fun x => x.2.2) with hρ
  have hρs : Function.Surjective ρ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hA' hy
    exact ⟨⟨x, hx, hy⟩, rfl⟩
  exact ⟨Ã, f'.comp ρ, inf_le_left, hf'.comp hρs⟩

theorem isSolvable_of_isCompositionFactor_of_pow {G : Type} [Group G] [Finite G] {S : Type}
    [Group S] (h : E1.IsCompositionFactor G S) (h3 : ∀ g : G, ∃ k : ℕ, g ^ 3 ^ k = 1) :
    Group.IsSolvable S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 G := h3
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hd : Nat.card S ∣ 3 ^ n := hn ▸ isCompositionFactor_natCard_dvd h
  have : Finite S := isCompositionFactor_finite h
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
  have hpS : IsPGroup 3 S := IsPGroup.of_card hm
  have := hpS.isNilpotent
  infer_instance

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15

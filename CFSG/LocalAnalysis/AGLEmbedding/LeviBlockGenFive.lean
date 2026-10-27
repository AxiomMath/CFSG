module

public import CFSG.Open.Defs
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockFive
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.AGLEmbedding

namespace LeviBlock

@[expose] def SectionsSixty {H : Type} [Group H] (X O : Subgroup H) : Prop :=
  ∀ U : Subgroup H, U ≤ X → ∀ (T : Type) [Group T] [IsSimpleGroup T],
    (∃ a b : T, a * b ≠ b * a) → ∀ φ : ↥U →* T, Function.Surjective φ →
      (∀ u : ↥U, (u : H) ∈ O → φ u = 1) → Nat.card T = 60

variable {A H : Type} [Group A] [Group H]

theorem sectionsSixty_of_quotient {X O : Subgroup H}
    (h : ∀ U : Subgroup H, U ≤ X → ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V →
      IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60) :
    SectionsSixty X O := by
  intro U hU T _ _ hnc φ hφ hO
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hS : IsSimpleGroup (↥U ⧸ φ.ker) := e.isSimpleGroup
  have hle : O.subgroupOf U ≤ φ.ker := fun u hu => hO u (Subgroup.mem_subgroupOf.mp hu)
  have hnc' : ∃ a b : ↥U ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
    simpa using congrArg e h'
  rw [← Nat.card_congr e.toEquiv]
  exact h U hU φ.ker hle hS hnc'

theorem SectionsSixty.quotient {X O : Subgroup H} (h : SectionsSixty X O) :
    ∀ U : Subgroup H, U ≤ X → ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V →
      IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60 := by
  intro U hU V _ hOV hS hnc
  exact h U hU (U ⧸ V) hnc (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)
    fun u hu => (QuotientGroup.eq_one_iff u).mpr (hOV (Subgroup.mem_subgroupOf.mpr hu))

theorem SectionsSixty.mono {X X' O O' : Subgroup H} (h : SectionsSixty X O) (hX : X' ≤ X)
    (hO : O ≤ O') : SectionsSixty X' O' :=
  fun U hU T _ _ hnc φ hφ hk => h U (hU.trans hX) T hnc φ hφ fun u hu => hk u (hO hu)

theorem SectionsSixty.comap (f : A →* H) {X O : Subgroup H} (h : SectionsSixty X O) :
    SectionsSixty (X.comap f) (O.comap f) := by
  intro U hU T _ _ hnc φ hφ hk
  set fU : ↥U →* ↥(U.map f) :=
    (f.comp U.subtype).codRestrict (U.map f) (fun u => ⟨u, u.2, rfl⟩) with hfUd
  have hfU : Function.Surjective fU := by
    rintro ⟨_, u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  have hker : fU.ker ≤ φ.ker := by
    intro u hu
    have h1 : f u = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
    exact hk u (by rw [Subgroup.mem_comap, h1]; exact O.one_mem)
  set φ' := fU.liftOfSurjective hfU ⟨φ, hker⟩ with hφ'd
  have hφ'f : ∀ u, φ' (fU u) = φ u := fun u => by simp [hφ'd]
  refine h (U.map f) (Subgroup.map_le_iff_le_comap.mpr hU) T hnc φ' ?_ ?_
  · intro t
    obtain ⟨u, rfl⟩ := hφ t
    exact ⟨fU u, hφ'f u⟩
  · intro y hy
    obtain ⟨u, rfl⟩ := hfU y
    rw [hφ'f]
    exact hk u hy

theorem SectionsSixty.map (β : A →* H) {O : Subgroup A} (h : SectionsSixty ⊤ O) :
    SectionsSixty β.range (O.map β) := by
  intro U hU T _ _ hnc φ hφ hk
  set βU : ↥(U.comap β) →* ↥U := β.subgroupComap U with hβUd
  have hβU : Function.Surjective βU := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := hU hy
    exact ⟨⟨a, hy⟩, rfl⟩
  refine h (U.comap β) le_top T hnc (φ.comp βU) (hφ.comp hβU) fun u hu => ?_
  exact hk (βU u) ⟨u, hu, rfl⟩

theorem fiveSection_comap (f : A →* H) {O J : Subgroup H} (hJf : J ≤ f.range)
    (hJ : ∃ φ : ↥J →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ ∀ x : ↥J, φ x = 1 ↔ (x : H) ∈ O) :
    ∃ φ : ↥(J.comap f) →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ ∀ x : ↥(J.comap f), φ x = 1 ↔ (x : A) ∈ O.comap f := by
  obtain ⟨φ, hφ, hφO⟩ := hJ
  have hfJ : Function.Surjective (f.subgroupComap J) := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := hJf hy
    exact ⟨⟨a, hy⟩, rfl⟩
  exact ⟨φ.comp (f.subgroupComap J), hφ.comp hfJ, fun x => hφO _⟩

theorem pow_two_pow_mem_of_mem_sup (β : A →* H) (hker : IsPGroup 2 β.ker) {O : Subgroup A}
    [O.Normal] {x : A} (hx : x ∈ O ⊔ β.ker) : ∃ e : ℕ, x ^ 2 ^ e ∈ O := by
  set π := QuotientGroup.mk' O
  have hO : O.map π = ⊥ := (Subgroup.map_eq_bot_iff O).mpr (by rw [QuotientGroup.ker_mk'])
  have hπx : π x ∈ β.ker.map π := by
    have := Subgroup.mem_map_of_mem π hx
    rwa [Subgroup.map_sup, hO, bot_sup_eq] at this
  obtain ⟨e, he⟩ := hker.map π ⟨π x, hπx⟩
  refine ⟨e, (QuotientGroup.eq_one_iff _).mp ?_⟩
  have := congrArg Subtype.val he
  simpa [π] using this

theorem fiveSection_map (β : A →* H) (hker : IsPGroup 2 β.ker) {O J : Subgroup A} [O.Normal]
    (hJ : ∃ φ : ↥J →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ ∀ x : ↥J, φ x = 1 ↔ (x : A) ∈ O) :
    ∃ φ : ↥(J.map β) →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ ∀ y : ↥(J.map β), φ y = 1 ↔ (y : H) ∈ (O ⊔ β.ker).map β := by
  obtain ⟨φ, hφ, hφO⟩ := hJ
  have hA5 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  set M := (O ⊔ β.ker).subgroupOf J with hMd
  have hMn : M.Normal := Subgroup.Normal.subgroupOf inferInstance J
  have : (M.map φ).Normal := hMn.map φ hφ
  have hM2 : IsPGroup 2 (M.map φ) := by
    rintro ⟨_, x, hx, rfl⟩
    obtain ⟨e, he⟩ := pow_two_pow_mem_of_mem_sup β hker (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨e, Subtype.ext ?_⟩
    have h1 : φ (x ^ 2 ^ e) = 1 := (hφO _).mpr (by simpa using he)
    simpa [map_pow] using h1
  have hMle := LeviBlock.le_ker_of_isPGroup_two (by rw [hA5]; norm_num) (MonoidHom.id _)
    Function.surjective_id hM2
  have hkill : ∀ x : ↥J, (x : A) ∈ O ⊔ β.ker → φ x = 1 := fun x hx =>
    hMle ⟨x, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  set βJ : ↥J →* ↥(J.map β) :=
    (β.comp J.subtype).codRestrict (J.map β) (fun x => ⟨x, x.2, rfl⟩) with hβJd
  have hβJ : Function.Surjective βJ := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk : βJ.ker ≤ φ.ker := fun x hx =>
    hkill x (Subgroup.mem_sup_right (MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)))
  set φ' := βJ.liftOfSurjective hβJ ⟨φ, hk⟩ with hφ'd
  have hφ'β : ∀ x, φ' (βJ x) = φ x := fun x => by simp [hφ'd]
  refine ⟨φ', ?_, fun y => ?_⟩
  · intro t
    obtain ⟨x, rfl⟩ := hφ t
    exact ⟨βJ x, hφ'β x⟩
  obtain ⟨x, rfl⟩ := hβJ y
  rw [hφ'β]
  constructor
  · intro h1
    exact ⟨x, Subgroup.mem_sup_left ((hφO x).mp h1), rfl⟩
  · rintro ⟨o, ho, hoβ⟩
    refine hkill x ?_
    have hx : (x : A) = o * (o⁻¹ * x) := by group
    rw [hx]
    refine Subgroup.mul_mem _ ho (Subgroup.mem_sup_right (MonoidHom.mem_ker.mpr ?_))
    rw [map_mul, map_inv, hoβ]
    exact inv_mul_cancel _

end LeviBlock

theorem three_le_card_fiveBlocks {Y Q : Type} [Group Y] [Group Q] {P : Subgroup Y}
    (f : Q →* Y) (hf : f.range = P) {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {S : ∀ j, Subgroup (G j)} (β : Q →* ∀ j, G j)
    (hker : IsPGroup 2 β.ker) (hpi : Subgroup.pi Set.univ S ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    (hcl : ∀ j, CFSG.Open.IsQuasisimple (S j) →
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 → Nat.card (S j) = 60)
    {O : Subgroup Y} {J : Fin 3 → Subgroup Y} (hPO : P ≤ Subgroup.normalizer (O : Set Y))
    (hsec : ∀ U : Subgroup Y, U ≤ P → ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V →
      IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60)
    (hJ : ∀ i, J i ≤ P ∧ ∃ φ : ↥(J i) →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ ∀ x : ↥(J i), φ x = 1 ↔ (x : Y) ∈ O)
    (hJc : ∀ i k, i ≠ k → ⁅J i, J k⁆ ≤ O) :
    3 ≤ Nat.card {j // CFSG.Open.IsQuasisimple (S j) ∧
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60} := by
  classical
  have hPf : P.comap f = ⊤ := eq_top_iff.mpr fun a _ => by
    rw [Subgroup.mem_comap, ← hf]
    exact ⟨a, rfl⟩
  have hOn : (O.comap f).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    have hg : f g ∈ P := hf ▸ ⟨g, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hPO hg) (f n)).mp hn⟩
  set O' := O.comap f ⊔ β.ker with hO'd
  have hsec' : LeviBlock.SectionsSixty β.range (O'.map β) :=
    (((LeviBlock.sectionsSixty_of_quotient hsec).comap f).mono hPf.symm.le le_sup_left).map β
  have hJ' : ∀ i, ((J i).comap f).map β ≤ β.range ∧
      ∃ φ : ↥(((J i).comap f).map β) →* alternatingGroup (Fin 5), Function.Surjective φ ∧
        ∀ y : ↥(((J i).comap f).map β), φ y = 1 ↔ (y : ∀ j, G j) ∈ O'.map β := fun i =>
    ⟨Subgroup.map_le_range β _, LeviBlock.fiveSection_map β hker
      (LeviBlock.fiveSection_comap f (((hJ i).1).trans hf.ge) (hJ i).2)⟩
  have hJc' : ∀ i k, i ≠ k → ⁅((J i).comap f).map β, ((J k).comap f).map β⁆ ≤ O'.map β := by
    intro i k hik
    rw [← Subgroup.map_commutator]
    refine Subgroup.map_mono (le_trans ?_ le_sup_left)
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hJc i k hik (Subgroup.commutator_mem_commutator ha hb)
  have hXO : β.range ≤ Subgroup.normalizer ((O'.map β : Subgroup _) : Set (∀ j, G j)) := by
    have h := Subgroup.le_normalizer_map (H := O') β
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map] at h
  have h3 := fiveBlockSections hpi hcomm hS hcl (O'.map β) (fun i => ((J i).comap f).map β)
    (Subgroup.map_le_range β O') hXO hsec'.quotient hJ' hJc'
  refine h3.trans (Nat.card_le_card_of_injective (fun j => ⟨j.1, j.2.1, j.2.2.1⟩) ?_)
  intro a b hab
  have h := congrArg Subtype.val hab
  exact Subtype.ext h

theorem three_le_card_fiveBlocks_of_cover {Y : Type} [Group Y] {L P : Subgroup Y} (hPL : P ≤ L)
    {K : Type} [Group K] (ρ : K →* ↥L) (hρ : Function.Surjective ρ) {ι : Type} [Fintype ι]
    [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    {S : ∀ j, Subgroup (G j)} (β : ↥((P.subgroupOf L).comap ρ) →* ∀ j, G j)
    (hker : IsPGroup 2 β.ker) (hpi : Subgroup.pi Set.univ S ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hS : ∀ j, CFSG.Open.IsQuasisimple (S j) ∨ Group.IsSolvable (S j))
    (hcl : ∀ j, CFSG.Open.IsQuasisimple (S j) →
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60 → Nat.card (S j) = 60)
    {O : Subgroup Y} {J : Fin 3 → Subgroup Y} (hPO : P ≤ Subgroup.normalizer (O : Set Y))
    (hsec : ∀ U : Subgroup Y, U ≤ P → ∀ (V : Subgroup U) [V.Normal], O.subgroupOf U ≤ V →
      IsSimpleGroup (U ⧸ V) → (∃ a b : U ⧸ V, a * b ≠ b * a) → Nat.card (U ⧸ V) = 60)
    (hJ : ∀ i, J i ≤ P ∧ ∃ φ : ↥(J i) →* alternatingGroup (Fin 5),
      Function.Surjective φ ∧ ∀ x : ↥(J i), φ x = 1 ↔ (x : Y) ∈ O)
    (hJc : ∀ i k, i ≠ k → ⁅J i, J k⁆ ≤ O) :
    3 ≤ Nat.card {j // CFSG.Open.IsQuasisimple (S j) ∧
      Nat.card (↥(S j) ⧸ Subgroup.center ↥(S j)) = 60} := by
  refine three_le_card_fiveBlocks (L.subtype.comp (ρ.comp ((P.subgroupOf L).comap ρ).subtype))
    ?_ β hker hpi hcomm hS hcl hPO hsec hJ hJc
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    exact Subgroup.mem_subgroupOf.mp q.2
  · intro p hp
    obtain ⟨k, hk⟩ := hρ ⟨p, hPL hp⟩
    have hkQ : k ∈ (P.subgroupOf L).comap ρ := by
      change ρ k ∈ P.subgroupOf L
      rw [hk]
      exact Subgroup.mem_subgroupOf.mpr hp
    exact ⟨⟨k, hkQ⟩, by simp [hk]⟩

end CFSG.AGLEmbedding

module

public import CFSG.LocalAnalysis.GLTheoremB.QuasiAut
public import CFSG.LocalAnalysis.GLTheoremB.A7Centralizer
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open
open scoped commutatorElement

section Generic

variable {Q : Type*} [Group Q]

theorem eq_bot_or_eq_of_isSubnormal_of_simple {A B : Subgroup Q} (hB : IsSimpleGroup ↥B)
    (h : IsSubnormal A B) : A = ⊥ ∨ A = B :=
  h.eq_bot_or_eq_of_isSimpleGroup hB

end Generic

section Data

variable {H : Type} [Group H] [Finite H]

structure LData (ℒ : Set (Subgroup H)) : Prop where
  comp : ∀ L ∈ ℒ, IsComponentOf L ⊤
  typ : ∀ L ∈ ℒ, Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* ↥S7.Alt7)

namespace LData

variable {ℒ : Set (Subgroup H)} (hℒ : LData ℒ)

include hℒ

theorem centralizes {L L' : Subgroup H} (hL : L ∈ ℒ) (hL' : L' ∈ ℒ) (hne : L ≠ L') :
    L ≤ Subgroup.centralizer (L' : Set H) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.1
    (CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' (hℒ.comp L hL)
      (hℒ.comp L' hL') hne)

theorem sSup_le_normalizer {L : Subgroup H} (hL : L ∈ ℒ) :
    sSup ℒ ≤ Subgroup.normalizer (L : Set H) := by
  refine sSup_le fun L' hL' => ?_
  by_cases h : L' = L
  · rw [h]
    exact Subgroup.le_normalizer
  · exact (hℒ.centralizes hL' hL h).trans (Subgroup.centralizer_le_normalizer (L : Set H))

theorem FL_mem_Alt7 {L : Subgroup H} (hL : L ∈ ℒ) (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥S7.Alt7)
    {x : H} (hx : x ∈ sSup ℒ) :
    S7.FL L e ⟨x, hℒ.sSup_le_normalizer hL hx⟩ ∈ S7.Alt7 := by
  set N := Subgroup.normalizer (L : Set H) with hN
  set T : Subgroup H := (S7.Alt7.comap (S7.FL L e)).map N.subtype with hT
  have hsup : sSup ℒ ≤ T := by
    refine sSup_le fun L' hL' l' hl' => ?_
    refine ⟨⟨l', hℒ.sSup_le_normalizer hL (le_sSup hL' hl')⟩, ?_, rfl⟩
    by_cases h : L' = L
    · subst h
      have := S7.FL_of_mem L' e ⟨l', hl'⟩
      show S7.FL L' e ⟨l', _⟩ ∈ S7.Alt7
      rw [this]
      exact (e _).2
    · have hc : l' ∈ Subgroup.centralizer (L : Set H) := hℒ.centralizes hL' hL h hl'
      show S7.FL L e ⟨l', _⟩ ∈ S7.Alt7
      rw [S7.FL_of_centralizes L e hc]
      exact S7.Alt7.one_mem
  obtain ⟨y, hy, hyx⟩ := hsup hx
  have : y = ⟨x, hℒ.sSup_le_normalizer hL hx⟩ := Subtype.ext hyx
  rw [← this]
  exact hy

theorem FL_image_eq_Alt7 {b : H} (hb : b ^ 3 = 1)
    (hbℒ : ∀ L ∈ ℒ, L.map (MulAut.conj b).toMonoidHom ∈ ℒ)
    {K : Subgroup H} (hKE : K ≤ sSup ℒ) (hKb : K ≤ Subgroup.centralizer ({b} : Set H))
    (hKperf : ⁅K, K⁆ = K)
    (hsn : IsSubnormal K (sSup ℒ ⊓ Subgroup.centralizer ({b} : Set H)))
    {L : Subgroup H} (hL : L ∈ ℒ) (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥S7.Alt7)
    (hKL : ¬ K ≤ Subgroup.centralizer (L : Set H)) :
    (K.subgroupOf (Subgroup.normalizer (L : Set H))).map (S7.FL L e) = S7.Alt7 := by
  set N : Subgroup H := Subgroup.normalizer (L : Set H) with hN
  set F := S7.FL L e with hF
  set C : Subgroup H := sSup ℒ ⊓ Subgroup.centralizer ({b} : Set H) with hC
  have hEN : sSup ℒ ≤ N := hℒ.sSup_le_normalizer hL
  have hCN : C ≤ N := inf_le_left.trans hEN
  have hKN : K ≤ N := hKE.trans hEN
  have hKC : K ≤ C := le_inf hKE hKb
  have hLperf : commutator ↥L = ⊤ := (hℒ.comp L hL).2.2.1
  set FK : Subgroup S7.S := (K.subgroupOf N).map F with hFK
  have hFKperf : ⁅FK, FK⁆ = FK := by
    have h1 : ⁅K.subgroupOf N, K.subgroupOf N⁆ = K.subgroupOf N := by
      apply Subgroup.map_injective N.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKN]
      exact hKperf
    rw [hFK, ← Subgroup.map_commutator, h1]
  have hFKne : FK ≠ ⊥ := by
    intro h
    apply hKL
    intro k hk
    refine S7.centralizes_of_FL_eq_one L e hLperf (hKN hk) ?_
    have : F ⟨k, hKN hk⟩ ∈ FK := ⟨⟨k, hKN hk⟩, (Subgroup.mem_subgroupOf).2 hk, rfl⟩
    rw [h] at this
    exact (Subgroup.mem_bot).1 this
  have hgen : ∀ l : ↥L, ∃ (x : H) (hx : x ∈ C),
      F ⟨x, hCN hx⟩ = ((e (QuotientGroup.mk l) : ↥S7.Alt7) : S7.S) := by
    intro l
    have hlE : (l : H) ∈ sSup ℒ := le_sSup hL l.2
    by_cases hLb : L.map (MulAut.conj b).toMonoidHom = L
    · have hbN : b ∈ N := by
        refine Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
        · rw [← hLb]
          exact ⟨y, hy, rfl⟩
        · rw [← hLb] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          have : z = y := by
            have h1 : b * z * b⁻¹ = b * y * b⁻¹ := hzy
            simpa using h1
          rw [← this]
          exact hz
      set τ := F ⟨b, hbN⟩ with hτ
      have hτ3 : τ ^ 3 = 1 := by
        rw [hτ, ← map_pow]
        have : (⟨b, hbN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hb)
        rw [this, map_one]
      by_cases hτ1 : τ = 1
      · have hbc : b ∈ Subgroup.centralizer (L : Set H) :=
          S7.centralizes_of_FL_eq_one L e hLperf hbN hτ1
        have hlb : (l : H) ∈ Subgroup.centralizer ({b} : Set H) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.1 hbc) l l.2
        exact ⟨l, ⟨hlE, hlb⟩, S7.FL_of_mem L e l⟩
      · exfalso
        apply hFKne
        refine S7.eq_bot_of_perfect_le_centralizer hτ3 hτ1 ?_ hFKperf
        rintro _ ⟨k, hk, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hkb : (k : H) * b = b * k :=
          Subgroup.mem_centralizer_singleton_iff.1 (hKb ((Subgroup.mem_subgroupOf).1 hk))
        have hkb' : k * (⟨b, hbN⟩ : ↥N) = ⟨b, hbN⟩ * k := Subtype.ext hkb
        show F k * F ⟨b, hbN⟩ = F ⟨b, hbN⟩ * F k
        rw [← map_mul, ← map_mul, hkb']
    ·
      set c : H →* H := (MulAut.conj b).toMonoidHom with hc
      set L₂ : Subgroup H := L.map c with hL₂def
      set L₃ : Subgroup H := L₂.map c with hL₃def
      have hL₂ℒ : L₂ ∈ ℒ := hbℒ L hL
      have hL₃ℒ : L₃ ∈ ℒ := hbℒ L₂ hL₂ℒ
      have hb3 : b * b * b = 1 := by simpa [pow_succ, mul_assoc] using hb
      have hcc : ∀ x : H, c (c (c x)) = x := by
        intro x
        show b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹ = x
        calc b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹ = (b * b * b) * x * (b * b * b)⁻¹ := by group
          _ = x := by rw [hb3]; group
      have act3 : ∀ K' : Subgroup H, ((K'.map c).map c).map c = K' := by
        intro K'
        rw [Subgroup.map_map, Subgroup.map_map]
        have : ((c.comp c).comp c) = MonoidHom.id H := by
          ext x
          exact hcc x
        rw [this, Subgroup.map_id]
      have h12 : L ≠ L₂ := fun h => hLb h.symm
      have h13 : L ≠ L₃ := by
        intro h
        apply h12
        have h1 : L₃.map c = L := by rw [hL₃def, hL₂def, act3]
        rw [← h1, ← h]
      have h23 : L₂ ≠ L₃ := by
        intro h
        apply h12
        have h1 : L₃.map c = L := by rw [hL₃def, hL₂def, act3]
        have h2 : L₂.map c = L₃ := rfl
        rw [← h1, ← h, h2, ← h]
      have c21 : L₂ ≤ Subgroup.centralizer (L : Set H) := hℒ.centralizes hL₂ℒ hL h12.symm
      have c31 : L₃ ≤ Subgroup.centralizer (L : Set H) := hℒ.centralizes hL₃ℒ hL h13.symm
      have c12 : L ≤ Subgroup.centralizer (L₂ : Set H) := hℒ.centralizes hL hL₂ℒ h12
      have c13 : L ≤ Subgroup.centralizer (L₃ : Set H) := hℒ.centralizes hL hL₃ℒ h13
      set l₂ : H := b * (l : H) * b⁻¹ with hl₂def
      set l₃ : H := b * l₂ * b⁻¹ with hl₃def
      have hl₂ : l₂ ∈ L₂ := ⟨l, l.2, rfl⟩
      have hl₃ : l₃ ∈ L₃ := ⟨l₂, hl₂, rfl⟩
      have hl₂N : l₂ ∈ N := Subgroup.centralizer_le_normalizer _ (c21 hl₂)
      have hl₃N : l₃ ∈ N := Subgroup.centralizer_le_normalizer _ (c31 hl₃)
      have hlN : (l : H) ∈ N := Subgroup.le_normalizer l.2
      have hcom2 : l₂ * (l : H) = l * l₂ := (Subgroup.mem_centralizer_iff.1 (c12 l.2)) l₂ hl₂
      have hcom3 : l₃ * (l : H) = l * l₃ := (Subgroup.mem_centralizer_iff.1 (c13 l.2)) l₃ hl₃
      have hl₄ : b * l₃ * b⁻¹ = l := by
        calc b * l₃ * b⁻¹ = b * (b * (b * (l : H) * b⁻¹) * b⁻¹) * b⁻¹ := rfl
          _ = (b * b * b) * (l : H) * (b * b * b)⁻¹ := by group
          _ = l := by rw [hb3]; group
      have hxE : (l : H) * l₂ * l₃ ∈ sSup ℒ :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hlE (le_sSup hL₂ℒ hl₂)) (le_sSup hL₃ℒ hl₃)
      have hxb : (l : H) * l₂ * l₃ ∈ Subgroup.centralizer ({b} : Set H) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : b * ((l : H) * l₂ * l₃) * b⁻¹ = l₂ * l₃ * l := by
          calc b * ((l : H) * l₂ * l₃) * b⁻¹
              = (b * (l : H) * b⁻¹) * (b * l₂ * b⁻¹) * (b * l₃ * b⁻¹) := by group
            _ = l₂ * l₃ * l := by rw [hl₄]
        have h2 : l₂ * l₃ * (l : H) = l * l₂ * l₃ := by
          calc l₂ * l₃ * (l : H) = l₂ * (l₃ * l) := by group
            _ = l₂ * (l * l₃) := by rw [hcom3]
            _ = (l₂ * l) * l₃ := by group
            _ = (l * l₂) * l₃ := by rw [hcom2]
        have h3 : b * ((l : H) * l₂ * l₃) * b⁻¹ = (l : H) * l₂ * l₃ := by rw [h1, h2]
        calc (l : H) * l₂ * l₃ * b = (b * ((l : H) * l₂ * l₃) * b⁻¹) * b := by rw [h3]
          _ = b * ((l : H) * l₂ * l₃) := by group
      refine ⟨(l : H) * l₂ * l₃, ⟨hxE, hxb⟩, ?_⟩
      have hmul : (⟨(l : H) * l₂ * l₃, hCN ⟨hxE, hxb⟩⟩ : ↥N) =
          (⟨(l : H), hlN⟩ : ↥N) * ⟨l₂, hl₂N⟩ * ⟨l₃, hl₃N⟩ := Subtype.ext rfl
      rw [hmul, map_mul, map_mul, S7.FL_of_centralizes L e (c21 hl₂),
        S7.FL_of_centralizes L e (c31 hl₃), mul_one, mul_one]
      exact S7.FL_of_mem L e l
  set g : ↥C →* S7.S := F.comp (Subgroup.inclusion hCN) with hg
  have hrange : g.range = S7.Alt7 := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, rfl⟩
      exact hℒ.FL_mem_Alt7 hL e y.2.1
    · intro a ha
      obtain ⟨z, hz⟩ := e.surjective ⟨a, ha⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
      obtain ⟨x, hx, hFx⟩ := hgen l
      refine ⟨⟨x, hx⟩, ?_⟩
      show F ⟨x, hCN hx⟩ = a
      rw [hFx, hz]
  have hsnK : IsSubnormal ((K.subgroupOf C).map g) g.range := by
    have h1 := isSubnormal_comap' C.subtype hsn
    rw [show C.comap C.subtype = ⊤ from Subgroup.subgroupOf_self C] at h1
    have h2 := isSubnormal_map' g h1
    rwa [← MonoidHom.range_eq_map] at h2
  have himg : (K.subgroupOf C).map g = FK := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : H), hCN y.2⟩, (Subgroup.mem_subgroupOf).2 ((Subgroup.mem_subgroupOf).1 hy), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨(k : H), hKC ((Subgroup.mem_subgroupOf).1 hk)⟩,
        (Subgroup.mem_subgroupOf).2 ((Subgroup.mem_subgroupOf).1 hk), rfl⟩
  rw [himg, hrange] at hsnK
  rcases eq_bot_or_eq_of_isSubnormal_of_simple S7.isSimple_Alt7 hsnK with h | h
  · exact absurd h hFKne
  · exact h

theorem exists_equiv_alt7 {b : H} (hb : b ^ 3 = 1)
    (hbℒ : ∀ L ∈ ℒ, L.map (MulAut.conj b).toMonoidHom ∈ ℒ)
    {J : Type} [Group J] (ι : J →* H) (hιE : ι.range ≤ sSup ℒ)
    (hιb : ι.range ≤ Subgroup.centralizer ({b} : Set H))
    (hsn : IsSubnormal ι.range (sSup ℒ ⊓ Subgroup.centralizer ({b} : Set H)))
    (hperf : commutator J = ⊤) (O : Subgroup J) [O.Normal] (hO2 : IsPGroup 2 ↥O)
    (hker : ι.ker ≤ O) (hq : CFSG.Open.IsQuasisimple (J ⧸ O)) :
    Nonempty (((J ⧸ O) ⧸ Subgroup.center (J ⧸ O)) ≃* ↥S7.Alt7) := by
  have : Group.IsPerfect J := Group.isPerfect_def.2 hperf
  set K : Subgroup H := ι.range with hK
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 (Group.IsPerfect.range ι)
  by_cases hex : ∃ L ∈ ℒ, ¬ K ≤ Subgroup.centralizer (L : Set H)
  · obtain ⟨L, hL, hKL⟩ := hex
    obtain ⟨e⟩ := hℒ.typ L hL
    have hFK := hℒ.FL_image_eq_Alt7 hb hbℒ hιE hιb hKperf hsn hL e hKL
    set N : Subgroup H := Subgroup.normalizer (L : Set H) with hN
    have hKN : K ≤ N := hιE.trans (hℒ.sSup_le_normalizer hL)
    have hmem : ∀ j : J, ι j ∈ N := fun j => hKN ⟨j, rfl⟩
    set f : J →* S7.S := (S7.FL L e).comp (ι.codRestrict N hmem) with hf
    have hfr : f.range = S7.Alt7 := by
      rw [← hFK]
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨ι j, hmem j⟩, (Subgroup.mem_subgroupOf).2 ⟨j, rfl⟩, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        obtain ⟨j, hj⟩ := (Subgroup.mem_subgroupOf).1 hk
        exact ⟨j, by
          show S7.FL L e ⟨ι j, hmem j⟩ = S7.FL L e k
          congr 1
          exact Subtype.ext hj⟩
    have hfA : ∀ j, f j ∈ S7.Alt7 := fun j => by
      have : f j ∈ f.range := ⟨j, rfl⟩
      rw [hfr] at this
      exact this
    set f' : J →* ↥S7.Alt7 := f.codRestrict S7.Alt7 hfA with hf'
    have hsurj : Function.Surjective f' := by
      intro a
      have : (a : S7.S) ∈ f.range := by
        rw [hfr]
        exact a.2
      obtain ⟨j, hj⟩ := this
      exact ⟨j, Subtype.ext hj⟩
    have : IsSimpleGroup ↥S7.Alt7 := S7.isSimple_Alt7
    have hOker : O ≤ f'.ker := by
      have hnorm : (O.map f').Normal := Subgroup.Normal.map inferInstance f' hsurj
      have h2 : IsPGroup 2 ↥(O.map f') := hO2.map f'
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (O.map f') with h | h
      · exact (Subgroup.map_eq_bot_iff O).1 h
      · exfalso
        rw [h] at h2
        exact S7.not_isPGroup_two_Alt7 (h2.of_equiv Subgroup.topEquiv)
    set f'' : J ⧸ O →* ↥S7.Alt7 := QuotientGroup.lift O f' hOker with hf''
    have hsurj' : Function.Surjective f'' := by
      intro a
      obtain ⟨j, hj⟩ := hsurj a
      exact ⟨QuotientGroup.mk j, by rw [hf'', QuotientGroup.lift_mk, hj]⟩
    have hcenter : Subgroup.center (J ⧸ O) = f''.ker := by
      refine le_antisymm (fun z hz => ?_) ?_
      · rw [MonoidHom.mem_ker]
        have h1 : f'' z ∈ Subgroup.center ↥S7.Alt7 := Subgroup.map_center_le_center hsurj'
          ⟨z, hz, rfl⟩
        rw [alternatingGroup.center_eq_bot
          (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num), Subgroup.mem_bot] at h1
        exact h1
      · rcases normal_le_center_or_eq_top' hq f''.ker with h | h
        · exact h
        · exfalso
          have h1 : (1 : ↥S7.Alt7) ≠ (⟨(Equiv.swap 0 1) * Equiv.swap 1 2, by
            rw [Equiv.Perm.mem_alternatingGroup]; decide⟩ : ↥S7.Alt7) := by
            intro h2
            have := congrArg Subtype.val h2
            revert this
            decide
          obtain ⟨z, hz⟩ := hsurj' ⟨(Equiv.swap 0 1) * Equiv.swap 1 2, by
            rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
          have hz1 : f'' z = 1 := by
            have : z ∈ f''.ker := by
              rw [h]
              exact Subgroup.mem_top z
            exact this
          exact h1 (hz1.symm.trans hz)
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective f'' hsurj')⟩
  · exfalso
    push Not at hex
    have hle : sSup ℒ ≤ Subgroup.centralizer (K : Set H) :=
      sSup_le fun L hL => Subgroup.le_centralizer_iff.1 (hex L hL)
    have hcomm : ⁅K, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hιE.trans hle)
    have hbot : K = ⊥ := by rw [← hKperf, hcomm]
    have hker' : ι.ker = ⊤ := by
      rw [eq_top_iff]
      intro j _
      have : ι j ∈ K := ⟨j, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hO : O = ⊤ := eq_top_iff.2 (hker' ▸ hker)
    have hsub : Subsingleton (J ⧸ O) := by
      rw [hO]
      exact QuotientGroup.subsingleton_quotient_top
    have hnt : Nontrivial ((J ⧸ O) ⧸ Subgroup.center (J ⧸ O)) := hq.2.toNontrivial
    have : Subsingleton ((J ⧸ O) ⧸ Subgroup.center (J ⧸ O)) :=
      (QuotientGroup.mk'_surjective _).subsingleton
    exact not_subsingleton _ this

end LData

end Data

end CFSG.LocalAnalysis.GLTheoremB

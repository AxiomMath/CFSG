module

public import CFSG.HardMathSupport.Solomon.Proving.KZeroLe

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Proving

theorem glaPLayer_inf_centralizer_le_of_input18_3_4 (i183 : Input18_3_4) {G : Type} [Group G]
    [Finite G] {X E : Subgroup G} (hK : CFSG.Open.IsKGroup ↥X) {p : ℕ} (hp : p.Prime) (hEX : E ≤ X)
    (hE : IsElemAbelian p E) :
    GLAPLayer p (X ⊓ Subgroup.centralizer (E : Set G)) ≤ GLAPLayer p X := by
  unfold GLAPLayer
  refine sSup_le fun J hJ => ?_
  obtain ⟨𝒞, h𝒞, hgen, -, -⟩ := i183 G X hK p hp E hEX hE J hJ
  have h1 : J ≤ ⨆ g ∈ GLAPLayer p X, GLBConj g J := by
    have hmem : (1 : G) ∈ GLAPLayer p X := (GLAPLayer p X).one_mem
    refine le_trans (le_of_eq (gLBConj_one _).symm) ?_
    exact le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer p X) => GLBConj g J) (1 : G) hmem
  refine h1.trans ?_
  rw [← hgen]
  exact iSup₂_le fun L hL => le_sSup (h𝒞 L hL)

theorem layer_inf_centralizer_le_of_input18_3_4 (i183 : Input18_3_4)
    {G : Type} [Group G] [Finite G] {K A : Subgroup G} {a : G}
    (hKA : CFSG.Open.IsKGroup ↥((K ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ A))
    (hAe : IsElemAbelian 3 A) (haA : a ∈ A) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hAa : A ≤ Subgroup.centralizer ({a} : Set G)) :
    GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set G)) ≤
      GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hA : IsPGroup 3 ↥A := fun z => ⟨1, Subtype.ext (by simpa using hAe.2 z z.2)⟩
  set Y : Subgroup G := K ⊓ Subgroup.centralizer ({a} : Set G) with hYdef
  set X : Subgroup G := Y ⊔ A with hXdef
  have hYK : Y ≤ K := inf_le_left
  have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) := inf_le_right
  have hYX : Y ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hAN' := Subgroup.le_normalizer_iff.1 hAN
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.le_normalizer_iff.2 fun h hh k hk =>
      K.mul_mem (K.mul_mem (hYK hh) hk) (K.inv_mem (hYK hh))
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := sup_le hYN hAN
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := by
    refine Subgroup.le_normalizer_iff.2 fun h hh k hk => ?_
    have hkK : k ∈ K := (Subgroup.mem_inf.1 hk).1
    have hkC : k * a = a * k := Subgroup.mem_centralizer_singleton_iff.1 (hYa hk)
    have hhC : h * a = a * h := Subgroup.mem_centralizer_singleton_iff.1 (hAa hh)
    exact Subgroup.mem_inf.2 ⟨hAN' h hh k hkK,
      Subgroup.mem_centralizer_singleton_iff.2 (conj_cent_singleton hhC hkC)⟩
  have hYY : Y ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.le_normalizer_iff.2 fun h hh k hk => Y.mul_mem (Y.mul_mem hh hk) (Y.inv_mem hh)
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := sup_le hYY hAY
  have hn : (Y.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXY
  have step2 : GLAPLayer 3 (X ⊓ Subgroup.centralizer (A : Set G)) ≤ GLAPLayer 3 X :=
    glaPLayer_inf_centralizer_le_of_input18_3_4 i183 hKA Nat.prime_three hAX hAe
  have step3 : GLAPLayer 3 X ≤ GLAPLayer 3 Y :=
    glaPLayer_le_of_normal_sup_pGroup Nat.prime_three hYX hn hAX hA le_rfl
  have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({a} : Set G) :=
    fun k hk => Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 hk) a haA).symm
  have hKCA_le_X : K ⊓ Subgroup.centralizer (A : Set G) ≤ X := fun k hk =>
    hYX (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hk).1, hCA (Subgroup.mem_inf.1 hk).2⟩)
  have hYM : K ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊓ Subgroup.centralizer (A : Set G) :=
    le_inf hKCA_le_X inf_le_right
  have hX'N : X ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) := by
    refine Subgroup.le_normalizer_iff.2 fun x hx k hk => ?_
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨Subgroup.le_normalizer_iff.1 hXN x hxX k hkK, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    have hxs : x * s = s * x := ((Subgroup.mem_centralizer_iff.1 hxC) s hs).symm
    have hks : k * s = s * k := ((Subgroup.mem_centralizer_iff.1 hkC) s hs).symm
    exact (conj_cent_singleton hxs hks).symm
  have hn' : ((K ⊓ Subgroup.centralizer (A : Set G)).subgroupOf
      (X ⊓ Subgroup.centralizer (A : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2 hX'N
  have step4 : GLAPLayer 3 (K ⊓ Subgroup.centralizer (A : Set G)) ≤
      GLAPLayer 3 (X ⊓ Subgroup.centralizer (A : Set G)) :=
    glaPLayer_le_of_normal_le Nat.prime_three hYM hn'
  exact step4.trans (step2.trans step3)

theorem centralizerQuot_le_normalizer {G : Type} [Group G] [Finite G] {B : Subgroup G}
    (hB : IsElemAbelian 3 B) (K : Subgroup G) :
    centralizerQuot B K ≤ Subgroup.normalizer (K : Set G) := by
  unfold centralizerQuot
  refine (Subgroup.closure_le _).2 fun b hb => ?_
  obtain ⟨hbB, hb⟩ := hb
  have hfwd : ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun k hk => by
    have h1 : b * k * b⁻¹ * k⁻¹ ∈ K := (Subgroup.map_subtype_le _) (hb k hk)
    have := K.mul_mem h1 hk
    simpa [mul_assoc] using this
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hbinv : b⁻¹ = b * b := by
    have : b * (b * b) = 1 := by simpa [pow_succ, mul_assoc] using hb3
    exact inv_eq_of_mul_eq_one_right this
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hfwd h hh, fun hh => ?_⟩
  have e : h = b * (b * (b * h * b⁻¹) * b⁻¹) * b⁻¹ := by
    have h3 : b * b * b = 1 := by simpa [pow_succ, mul_assoc] using hb3
    calc h = (b * b * b) * h * (b * b * b)⁻¹ := by rw [h3]; group
      _ = b * (b * (b * h * b⁻¹) * b⁻¹) * b⁻¹ := by group
  rw [e]
  exact hfwd _ (hfwd _ hh)

theorem hkZero_holds (i183 : Input18_3_4) :
    ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
      ∀ (B : Subgroup G), IsExtremal B →
        ∀ K : Subgroup G, IsHSet B K → ∀ a ∈ centralizerQuot B K, a ≠ 1 →
          kZeroOf B K ≤ bClosureIa K a := by
  intro G _ _ m hS hC B hB K hK a ha ha1
  have hBel : IsElemAbelian 3 B := hB.1.1.1
  have hAB : centralizerQuot B K ≤ B := by
    unfold centralizerQuot
    exact (Subgroup.closure_le B).2 fun b hb => hb.1
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (isMulCommutative_iff.1 hBel.1 ⟨x, hx⟩ ⟨y, hy⟩)
  have hAe : IsElemAbelian 3 (centralizerQuot B K) :=
    ⟨isMulCommutative_iff.2 fun x y => Subtype.ext (hcommB x (hAB x.2) y (hAB y.2)),
      fun x hx => hBel.2 x (hAB hx)⟩
  have haC : centralizerQuot B K ≤ Subgroup.centralizer ({a} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (hcommB x (hAB hx) a (hAB ha))
  have hAN : centralizerQuot B K ≤ Subgroup.normalizer (K : Set G) :=
    centralizerQuot_le_normalizer hBel K
  have hkK : kZeroOf B K ≤ K := by
    unfold kZeroOf GLAPLayer
    exact (sSup_le fun J hJ => hJ.1).trans inf_le_left
  by_cases hK1 : K = ⊥
  · exact le_trans (hkK.trans hK1.le) bot_le
  have := hS.simple
  obtain ⟨⟨x, hxB, hx1, hcomp⟩, -, -⟩ := hK
  have hKt : K ≠ ⊤ := by
    intro htop
    have hx : x ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g =>
      (Subgroup.mem_centralizer_singleton_iff.1 (hcomp.1 (htop ▸ Subgroup.mem_top g)))
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := Subgroup.center G) with h | h
    · exact hx1 (Subgroup.mem_bot.1 (h ▸ hx))
    · obtain ⟨c, d, hcd⟩ := hS.nonabelian
      exact hcd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top c) d).symm
  have hJN : (K ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ centralizerQuot B K ≤
      Subgroup.normalizer (K : Set G) :=
    sup_le (inf_le_left.trans Subgroup.le_normalizer) hAN
  have hNt : Subgroup.normalizer (K : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : K.Normal := by
      refine ⟨fun n hn g => ?_⟩
      have hg : g ∈ Subgroup.normalizer (K : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_normalizer_iff.1 hg n).1 hn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := K) with h | h
    · exact hK1 h
    · exact hKt h
  have hJt : (K ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ centralizerQuot B K ≠ ⊤ :=
    fun h => hNt (top_le_iff.1 (h ▸ hJN))
  have hKA := isKGroup_of_isKProper hS.kProper hJt
  have h1 : kZeroOf B K ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set G)) :=
    layer_inf_centralizer_le_of_input18_3_4 i183 hKA hAe ha hAN haC
  have h2 : GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set G)) ≤ bClosureIa K a := by
    unfold bClosureIa
    have hmem : (1 : G) ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G)) :=
      (GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))).one_mem
    refine le_trans (le_of_eq (gLBConj_one _).symm) ?_
    exact le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Subgroup.centralizer ({a} : Set G))) =>
      GLBConj g (GLAPLayer 3 (K ⊓ Subgroup.centralizer ({a} : Set G)))) (1 : G) hmem
  exact h1.trans h2

end CFSG.HardMathSupport.Solomon.UniquenessMaximal

end

module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPLType
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenAltTenUnique
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroThreePerfectProof
import CFSG.HardMathSupport.Cooperstein.Proving.BarTransport
import CFSG.Quasithin.Vol2.Ch11SecBL2OPSL
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

namespace AltTen

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev imgPL (X N K : Subgroup G) :
    Subgroup (↥(barM X N) ⧸ CFSG.pCore 2 ↥(barM X N)) :=
  ((barM X K).subgroupOf (barM X N)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥(barM X N)))

private theorem imgPL_facts {X H L K : Subgroup G} (hLX : L ≤ X) (hK : K ≤ H ⊓ L)
    (hKs : IsSubnormal K (H ⊓ L)) (hKp : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥) :
    imgPL X (H ⊓ L) K ≠ ⊥ ∧ ⁅imgPL X (H ⊓ L) K, imgPL X (H ⊓ L) K⁆ = imgPL X (H ⊓ L) K ∧
      (imgPL X (H ⊓ L) K).IsSubnormal := by
  obtain ⟨hCP, hCne, hCp, hCsn, -⟩ := CZeroThreePerfect.barM_facts hLX hK hKs hKp hK1
  have hC'ne : (barM X K).subgroupOf (barM X (H ⊓ L)) ≠ ⊥ := by
    intro h
    apply hCne
    rw [← Subgroup.map_subgroupOf_eq_of_le hCP, h, Subgroup.map_bot]
  have hC'p : ⁅(barM X K).subgroupOf (barM X (H ⊓ L)), (barM X K).subgroupOf (barM X (H ⊓ L))⁆ =
      (barM X K).subgroupOf (barM X (H ⊓ L)) := by
    apply Subgroup.map_injective (barM X (H ⊓ L)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hCP]
    exact hCp
  obtain ⟨g1, g2, g3, -⟩ := CZeroThreePerfect.quot_facts hC'ne hC'p hCsn
  exact ⟨g1, g2, g3⟩

private noncomputable abbrev kerPL (X N : Subgroup G) : Subgroup G :=
  N ⊓ ((pCoreOf 2 (barM X N)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥X))).map X.subtype

private theorem isPGroup_kerPL (X N : Subgroup G) : IsPGroup 2 (kerPL X N) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : IsPGroup 2 (pCoreOf 2 (barM X N)) := by
    rw [pCoreOf]
    exact (CFSG.pCore_isPGroup (G := ↥(barM X N)) (p := 2)).map _
  have h2 : IsPGroup 2 (QuotientGroup.mk' (CFSG.pCore 2 ↥X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  exact ((IsPGroup.comap_of_ker_isPGroup h1 _ h2).map X.subtype).to_le inf_le_right

private theorem le_normalizer_kerPL {X N : Subgroup G} (hNX : N ≤ X) :
    N ≤ normalizer (kerPL X N : Set G) := by
  have key : ∀ n ∈ N, ∀ g ∈ kerPL X N, n * g * n⁻¹ ∈ kerPL X N := by
    intro n hn g hg
    obtain ⟨hgN, hgX⟩ := hg
    obtain ⟨g', hg', rfl⟩ := hgX
    refine ⟨N.mul_mem (N.mul_mem hn hgN) (N.inv_mem hn), ?_⟩
    set n' : ↥X := ⟨n, hNX hn⟩
    refine ⟨n' * g' * n'⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hnP : QuotientGroup.mk' (CFSG.pCore 2 ↥X) n' ∈ barM X N :=
      ⟨n', Subgroup.mem_subgroupOf.mpr hn, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap] at hg'
    rw [pCoreOf] at hg' ⊢
    obtain ⟨w, hw, hwe⟩ := hg'
    refine ⟨⟨_, hnP⟩ * w * (⟨_, hnP⟩ : ↥(barM X N))⁻¹,
      (CFSG.pCore_normal (G := ↥(barM X N)) (p := 2)).conj_mem w hw _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hwe ⊢
    rw [hwe]
  intro n hn
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => key n hn g hg, fun hg => ?_⟩
  have := key n⁻¹ (N.inv_mem hn) _ hg
  simpa [mul_assoc] using this

private theorem eq_of_imgPL_eq {X N K₁ K₂ : Subgroup G} (hNX : N ≤ X)
    (h₁ : IsSubnormal K₁ N) (h₂ : IsSubnormal K₂ N) (hp₁ : ⁅K₁, K₁⁆ = K₁) (hp₂ : ⁅K₂, K₂⁆ = K₂)
    (himg : imgPL X N K₁ = imgPL X N K₂) : K₁ = K₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ∀ {A B : Subgroup G}, IsSubnormal A N → IsSubnormal B N →
      imgPL X N A ≤ imgPL X N B → A ≤ B ⊔ kerPL X N := by
    intro A B hA hB hAB x hx
    have hxN : x ∈ N := hA.le hx
    set x' : ↥X := ⟨x, hNX hxN⟩
    have hxP : QuotientGroup.mk' (CFSG.pCore 2 ↥X) x' ∈ barM X N :=
      ⟨x', Subgroup.mem_subgroupOf.mpr hxN, rfl⟩
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥(barM X N)) ⟨_, hxP⟩ ∈ imgPL X N A :=
      ⟨⟨_, hxP⟩, Subgroup.mem_subgroupOf.mpr ⟨x', Subgroup.mem_subgroupOf.mpr hx, rfl⟩, rfl⟩
    obtain ⟨w, hw, hwe⟩ := hAB hmem
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hw
    obtain ⟨y', hy', hy'w⟩ := hw
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy'
    have hyN : (y' : G) ∈ N := hB.le hy'
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hwe
    have hT : (y' : G)⁻¹ * x ∈ kerPL X N := by
      refine ⟨N.mul_mem (N.inv_mem hyN) hxN, y'⁻¹ * x', ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_inv, pCoreOf]
      refine ⟨w⁻¹ * ⟨_, hxP⟩, hwe, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hy'w]
    have : x = (y' : G) * ((y' : G)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hy' hT
  have h12 := hle h₁ h₂ himg.le
  have h21 := hle h₂ h₁ himg.ge
  set R := K₁ ⊔ kerPL X N with hR
  have hRN : R ≤ N := sup_le h₁.le inf_le_left
  have hs₁ : IsSubnormal K₁ R := by
    have := h₁.inf_of_le hRN
    rwa [inf_eq_left.mpr le_sup_left] at this
  have hs₂ : IsSubnormal K₂ R := by
    have := h₂.inf_of_le hRN
    rwa [inf_eq_left.mpr h21] at this
  exact eq_of_perfect_of_isSubnormal (isPGroup_kerPL X N)
    (hRN.trans (le_normalizer_kerPL hNX)) hs₁ hs₂ hp₁ hp₂ le_rfl (sup_le h12 le_sup_right)

private theorem map_conj_self {K : Subgroup G} {t : G} (ht : t ∈ normalizer (K : Set G)) :
    K.map (MulAut.conj t).toMonoidHom = K := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp ht x).mp hx
  · intro hy
    refine ⟨t⁻¹ * y * t, (mem_normalizer_iff.mp ht _).mpr ?_, ?_⟩
    · have : t * (t⁻¹ * y * t) * t⁻¹ = y := by group
      rw [this]
      exact hy
    · show t * (t⁻¹ * y * t) * t⁻¹ = y
      group

private theorem mem_normalizer_of_map_conj_eq {K : Subgroup G} {t : G}
    (h : K.map (MulAut.conj t).toMonoidHom = K) : t ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨y', hy', hyy'⟩ := hy
    have : y' = y := by
      have h1 : t * y' * t⁻¹ = t * y * t⁻¹ := hyy'
      simpa using h1
    exact this ▸ hy'

private theorem eq_of_mulEquiv_perm {Q : Type*} [Group Q] {n : ℕ}
    (e : Q ≃* Equiv.Perm (Fin n)) {C₁ C₂ : Subgroup Q} (h₁ : C₁ ≠ ⊥) (hp₁ : ⁅C₁, C₁⁆ = C₁)
    (hs₁ : C₁.IsSubnormal) (h₂ : C₂ ≠ ⊥) (hp₂ : ⁅C₂, C₂⁆ = C₂) (hs₂ : C₂.IsSubnormal) :
    C₁ = C₂ := by
  have key : ∀ C : Subgroup Q, C ≠ ⊥ → ⁅C, C⁆ = C → C.IsSubnormal →
      C.map e.toMonoidHom = alternatingGroup (Fin n) := by
    intro C h hp hs
    refine (eq_alternatingGroup_of_perfect ?_ (by rw [← Subgroup.map_commutator, hp])
      (hs.map (f := e.toMonoidHom) e.surjective)).2
    intro h0
    exact h ((Subgroup.map_eq_bot_iff_of_injective C (f := e.toMonoidHom) e.injective).mp h0)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [key C₁ h₁ hp₁ hs₁, key C₂ h₂ hp₂ hs₂]

private theorem eq_of_mulEquiv_perm_prod {Q : Type*} [Group Q] {r s : ℕ}
    (e : Q ≃* Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) {C₁ C₂ : Subgroup Q}
    (h₁ : C₁ ≠ ⊥) (hp₁ : ⁅C₁, C₁⁆ = C₁) (hs₁ : C₁.IsSubnormal)
    (hz₁ : (C₁.map e.toMonoidHom).map (MonoidHom.snd _ _) = ⊥)
    (h₂ : C₂ ≠ ⊥) (hp₂ : ⁅C₂, C₂⁆ = C₂) (hs₂ : C₂.IsSubnormal)
    (hz₂ : (C₂.map e.toMonoidHom).map (MonoidHom.snd _ _) = ⊥) : C₁ = C₂ := by
  have key : ∀ C : Subgroup Q, C ≠ ⊥ → ⁅C, C⁆ = C → C.IsSubnormal →
      (C.map e.toMonoidHom).map (MonoidHom.snd _ _) = ⊥ →
      ∀ x : Equiv.Perm (Fin r) × Equiv.Perm (Fin s),
        x ∈ C.map e.toMonoidHom ↔ x.2 = 1 ∧ x.1 ∈ alternatingGroup (Fin r) := by
    intro C h hp hs hz x
    set D := C.map e.toMonoidHom with hD
    have hDp : ⁅D, D⁆ = D := by rw [hD, ← Subgroup.map_commutator, hp]
    have hDs : D.IsSubnormal := hs.map (f := e.toMonoidHom) e.surjective
    have h2 : ∀ y ∈ D, y.2 = 1 := by
      intro y hy
      have : (MonoidHom.snd _ _) y ∈ D.map (MonoidHom.snd _ _) := ⟨y, hy, rfl⟩
      rw [hz, Subgroup.mem_bot] at this
      exact this
    have hne : D.map (MonoidHom.fst _ _) ≠ ⊥ := by
      intro h0
      apply h
      rw [← Subgroup.map_eq_bot_iff_of_injective C (f := e.toMonoidHom) e.injective, ← hD,
        eq_bot_iff]
      intro y hy
      have h1 : (MonoidHom.fst _ _) y ∈ D.map (MonoidHom.fst _ _) := ⟨y, hy, rfl⟩
      rw [h0, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).mpr (Prod.ext h1 (h2 y hy))
    have hA := (eq_alternatingGroup_of_perfect hne (by rw [← Subgroup.map_commutator, hDp])
      (hDs.map Prod.fst_surjective)).2
    constructor
    · intro hx
      refine ⟨h2 x hx, ?_⟩
      rw [← hA]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨hx2, hx1⟩
      rw [← hA] at hx1
      obtain ⟨y, hy, hyx⟩ := hx1
      have : y = x := Prod.ext hyx (by rw [h2 y hy, hx2])
      exact this ▸ hy
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  ext x
  rw [key C₁ h₁ hp₁ hs₁ hz₁, key C₂ h₂ hp₂ hs₂ hz₂]

private theorem false_of_alt_surj {n : ℕ} (hn : 6 ≤ n)
    (g : ↥(alternatingGroup (Fin n)) →* alternatingGroup (Fin 5)) (hg : Function.Surjective g) :
    False := by
  haveI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have h := card_eq_sixty_of_isSimpleGroup g hg
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin] at h
  have h6 : (6 : ℕ).factorial ≤ n.factorial := Nat.factorial_le hn
  have : (720 : ℕ) ≤ n.factorial := by simpa [Nat.factorial] using h6
  omega

private theorem eq_five_of_card_alt {s : ℕ} (hs : 5 ≤ s)
    (h : Nat.card (alternatingGroup (Fin s)) = 60) : s = 5 := by
  haveI : Nontrivial (Fin s) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [nat_card_alternatingGroup, Nat.card_fin] at h
  by_contra hne
  have h6 : (6 : ℕ).factorial ≤ s.factorial := Nat.factorial_le (by omega)
  have : (720 : ℕ) ≤ s.factorial := by simpa [Nat.factorial] using h6
  omega


end AltTen

open AltTen in
theorem kFactBlockAFive_one_of (h93 : Asc81bNineThree) (h85 : Asc81bEightFive)
    (hPLT : CitedBlockTransvectionPLType) (hSp : KFactSpTwoSimple)
    (h7 : CitedBlockAltSevenPL) :
    ∀ (G : Type) [Group G] [Finite G] (X S L I₀ : Subgroup G),
      Open.IsKGroup ↥X → Asc81bHyp X S → IsWeakSBlock X S L → ¬ InClassXBlock L →
      I₀ ∈ cZero (Subgroup.normalizer (S : Set G) ⊓ L) → IsTwoPrimeComponent I₀ I₀ →
      (∃ f : ↥I₀ →* alternatingGroup (Fin 5), Function.Surjective f) →
      NineThreeTwo X S L ∨
        ∀ t ∈ X, t ∈ Subgroup.normalizer (S : Set G) → t ∈ Subgroup.normalizer (L : Set G) →
          t ∈ Subgroup.normalizer (I₀ : Set G) := by
  intro G _ _ X S L I₀ hK hA hL hX hI₀ hI₀c ⟨f, hf⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := hL.le
  have hNX : normalizer (S : Set G) ⊓ L ≤ X := inf_le_right.trans hLX
  have hI₀X : I₀ ≤ X := hI₀.le.trans hNX
  have hSy2 : ¬ IsSylowTwoOf (S ⊓ L) L := fun h =>
    hX (h85 G X S L hK hA hL.toIsTwoPrimeComponent h)
  have hI1 : I₀ ≠ ⊥ := by
    haveI : Nontrivial ↥I₀ := hf.nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot I₀).mp inferInstance
  obtain ⟨hCP, hCne, hCp, hCsn, -⟩ :=
    CZeroThreePerfect.barM_facts hLX hI₀.le hI₀.subnormal hI₀c.perfect hI1
  set Pb := barM X (normalizer (S : Set G) ⊓ L) with hPb
  set C' := (barM X I₀).subgroupOf Pb with hC'
  have hC'ne : C' ≠ ⊥ := by
    intro h
    apply hCne
    rw [← Subgroup.map_subgroupOf_eq_of_le hCP, ← hC', h, Subgroup.map_bot]
  have hC'p : ⁅C', C'⁆ = C' := by
    apply Subgroup.map_injective Pb.subtype_injective
    rw [Subgroup.map_commutator, hC', Subgroup.map_subgroupOf_eq_of_le hCP]
    exact hCp
  have hC'A5 : ∃ g : ↥C' →* alternatingGroup (Fin 5), Function.Surjective g := by
    set β := CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub hI₀X with hβdef
    have hβ := CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective hI₀X
    set γ := (Subgroup.subgroupOfEquivOfLe hCP).symm with hγ
    refine exists_surjective_alt5_of_ker f hf (γ.toMonoidHom.comp β)
      (fun c => by
        obtain ⟨b, rfl⟩ := γ.surjective c
        obtain ⟨a, rfl⟩ := hβ b
        exact ⟨a, rfl⟩) ?_
    rintro ⟨g0, hg0⟩
    have hg1 : β g0 = 1 := γ.injective (by
      rw [map_one]
      exact (MonoidHom.mem_ker).mp hg0)
    have hgk : g0 ∈ β.ker := hg1
    rw [hβdef, CFSG.HardMathSupport.Cooperstein.Proving.ker_barMHomSub,
      Subgroup.mem_subgroupOf] at hgk
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.mp hgk
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥X) ⟨x, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have hthis := congrArg (fun y => ((y : ↥X) : G)) (congrArg Subtype.val hk)
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at hthis ⊢
    rw [← hxg]
    exact hthis
  obtain ⟨hC''ne, hC''p, hC''s, -⟩ := CZeroThreePerfect.quot_facts hC'ne hC'p hCsn
  have hC''A5 : ∃ g : ↥(C'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb))) →* alternatingGroup (Fin 5),
      Function.Surjective g := by
    obtain ⟨g, hg⟩ := hC'A5
    refine exists_surjective_alt5_of_ker g hg
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)).subgroupMap C')
      (MonoidHom.subgroupMap_surjective _ _) ?_
    intro y
    have hy : (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)) ((y : ↥C') : ↥Pb) = 1 :=
      congrArg Subtype.val ((MonoidHom.mem_ker).mp y.2)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Pb) ⟨_, hy⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hconj : ∀ t : G, t ∈ normalizer (S : Set G) → t ∈ normalizer (L : Set G) →
      I₀.map (MulAut.conj t).toMonoidHom ≤ normalizer (S : Set G) ⊓ L ∧
        IsSubnormal (I₀.map (MulAut.conj t).toMonoidHom) (normalizer (S : Set G) ⊓ L) ∧
        ⁅I₀.map (MulAut.conj t).toMonoidHom, I₀.map (MulAut.conj t).toMonoidHom⁆ =
          I₀.map (MulAut.conj t).toMonoidHom ∧ I₀.map (MulAut.conj t).toMonoidHom ≠ ⊥ := by
    intro t htS htL
    have hN : (normalizer (S : Set G) ⊓ L).map (MulAut.conj t).toMonoidHom =
        normalizer (S : Set G) ⊓ L := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective,
        map_conj_self (le_normalizer htS), map_conj_self htL]
    refine ⟨hN ▸ Subgroup.map_mono hI₀.le, hN ▸ hI₀.subnormal.map _,
      by rw [← Subgroup.map_commutator, hI₀c.perfect], ?_⟩
    intro h0
    exact hI1 ((Subgroup.map_eq_bot_iff_of_injective I₀ (MulAut.conj t).injective).mp h0)
  have hfinish : ∀ t : G, t ∈ normalizer (S : Set G) → t ∈ normalizer (L : Set G) →
      imgPL X (normalizer (S : Set G) ⊓ L) I₀ =
        imgPL X (normalizer (S : Set G) ⊓ L) (I₀.map (MulAut.conj t).toMonoidHom) →
      t ∈ normalizer (I₀ : Set G) := by
    intro t htS htL himg
    obtain ⟨-, h1s, h1p, -⟩ := hconj t htS htL
    exact mem_normalizer_of_map_conj_eq
      (eq_of_imgPL_eq hNX hI₀.subnormal h1s hI₀c.perfect h1p himg).symm
  have hfacts₀ := imgPL_facts hLX hI₀.le hI₀.subnormal hI₀c.perfect hI1
  have hfacts₁ : ∀ t : G, t ∈ normalizer (S : Set G) → t ∈ normalizer (L : Set G) → _ :=
    fun t htS htL => by
      obtain ⟨h1le, h1s, h1p, h1ne⟩ := hconj t htS htL
      exact imgPL_facts hLX h1le h1s h1p h1ne
  rcases h93 G X S L hK hA hL with h1 | h2 | h3 | h4 | h5 | h6 | h7' | h8
  · exact absurd h1 hX
  · exact Or.inl h2
  ·
    exfalso
    obtain ⟨hOrth, hU4, hA5, hA6, hA8⟩ := hPLT G X S L hK hA hL hX hSy2 h3
    have hperm : ∀ {n : ℕ}, n ≠ 5 → Nonempty (↥(blockPL X S L) ≃* Equiv.Perm (Fin n)) → False := by
      intro n hn5 ⟨e⟩
      obtain ⟨g, hg⟩ := hC'A5
      have hD := eq_alternatingGroup_of_perfect (D := C'.map e.toMonoidHom)
        (fun h0 => hC'ne ((Subgroup.map_eq_bot_iff_of_injective C' (f := e.toMonoidHom)
          e.injective).mp h0))
        (by rw [← Subgroup.map_commutator, hC'p]) (hCsn.map (f := e.toMonoidHom) e.surjective)
      have eD : ↥(alternatingGroup (Fin n)) ≃* ↥C' :=
        (MulEquiv.subgroupCongr hD.2).symm.trans
          (C'.equivMapOfInjective e.toMonoidHom e.injective).symm
      exact false_of_alt_surj (by omega) (g.comp eD.toMonoidHom) (fun a => by
        obtain ⟨c, rfl⟩ := hg a
        obtain ⟨b, rfl⟩ := eD.surjective c
        exact ⟨b, rfl⟩)
    have hsp : ∀ (k : ℕ) (d : TauCeti.ValidLieTypeIndex),
        (∃ q : TauCeti.PrimePower, q.card = 2 ∧ d.1 = .B k q) →
        Nonempty (↥(blockPL X S L) ⧸ CFSG.pCore 2 ↥(blockPL X S L) ≃*
          (TauCeti.CFSGIndex.lie d).Group) → False := by
      intro k d hd ⟨eP⟩
      have hk3 : 3 ≤ k := by
        obtain ⟨q, hq2, hdB⟩ := hd
        have hv := ((TauCeti.LieTypeIndex.valid_iff _).mp d.2).1
        rw [hdB] at hv
        simp only [TauCeti.LieTypeIndex.inStandardRange_iff] at hv
        omega
      obtain ⟨hsimp, h29⟩ := hSp k d hk3 hd
      set C'' := C'.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)) with hC''
      obtain ⟨g, hg⟩ := hC''A5
      have hDs : (C''.map eP.toMonoidHom).IsSubnormal :=
        hC''s.map (f := eP.toMonoidHom) eP.surjective
      rcases hDs.eq_bot_or_top_of_isSimpleGroup hsimp with h0 | h0
      · exact hC''ne ((Subgroup.map_eq_bot_iff_of_injective C'' (f := eP.toMonoidHom)
          eP.injective).mp h0)
      · have eT : (TauCeti.CFSGIndex.lie d).Group ≃* ↥C'' :=
          (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr h0).symm).trans
            (C''.equivMapOfInjective eP.toMonoidHom eP.injective).symm
        have h60 := card_eq_sixty_of_isSimpleGroup (g.comp eT.toMonoidHom) (fun a => by
          obtain ⟨c, rfl⟩ := hg a
          obtain ⟨b, rfl⟩ := eT.surjective c
          exact ⟨b, rfl⟩)
        rw [h60] at h29
        norm_num at h29
    rcases h3.2.1 with ⟨d, ⟨m, q, hq, hd'⟩, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases hd' with hd' | hd' | ⟨rfl, hd'⟩
      · obtain ⟨d'', hd'', heP⟩ := hOrth m d ⟨q, hq, Or.inl hd'⟩ ⟨e⟩
        exact hsp (m - 1) d'' hd'' heP
      · obtain ⟨d'', hd'', heP⟩ := hOrth m d ⟨q, hq, Or.inr hd'⟩ ⟨e⟩
        exact hsp (m - 1) d'' hd'' heP
      · exact hperm (by norm_num) (hU4 d ⟨q, hq, hd'⟩ ⟨e⟩)
    · rcases hn with rfl | rfl | rfl
      · exact hperm (by norm_num) (hA5 ⟨e⟩)
      · exact hperm (by norm_num) (hA6 ⟨e⟩)
      · exact hperm (by norm_num) (hA8 ⟨e⟩)
  ·
    exfalso
    obtain ⟨-, -, -, -, ⟨eS4⟩⟩ := h4
    have hs := CZeroThreePerfect.isSolvable_of_map_center_perm_four eS4
    have hPL' : Pb ≤ barM X L := Subgroup.map_mono fun y hy => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact hy.2
    set eP := (Subgroup.subgroupOfEquivOfLe hPL').symm
    haveI : Group.IsSolvable ↥Pb :=
      solvable_of_solvable_injective (f := eP.toMonoidHom) eP.injective
    exact hC'ne (CZeroThreePerfect.eq_bot_of_perfect_of_isSolvable hC'p)
  ·
    exfalso
    have h72 := h7 G X S L hK hA hL hX hSy2 h5
    obtain ⟨g, hg⟩ := hC'A5
    have h60 : Nat.card (alternatingGroup (Fin 5)) ∣ Nat.card C' :=
      Subgroup.card_dvd_of_surjective (f := g) hg
    rw [nat_card_alternatingGroup, Nat.card_fin] at h60
    have hC'72 : Nat.card C' ∣ 72 := (Subgroup.card_subgroup_dvd_card C').trans h72
    have := h60.trans hC'72
    norm_num at this
  ·
    right
    intro t _ htS htL
    obtain ⟨-, n, -, ⟨e⟩⟩ := h6
    obtain ⟨g1, g2, g3⟩ := hfacts₀
    obtain ⟨k1, k2, k3⟩ := hfacts₁ t htS htL
    exact hfinish t htS htL (eq_of_mulEquiv_perm e g1 g2 g3 k1 k2 k3)
  ·
    right
    intro t _ htS htL
    obtain ⟨-, n, -, ⟨e⟩⟩ := h7'
    obtain ⟨g1, g2, g3⟩ := hfacts₀
    obtain ⟨k1, k2, k3⟩ := hfacts₁ t htS htL
    exact hfinish t htS htL (eq_of_mulEquiv_perm e g1 g2 g3 k1 k2 k3)
  ·
    right
    intro t _ htS htL
    obtain ⟨-, N, r, hNe, hrN, -, -, -, -, φ, -, -⟩ := h8
    have hse : Even (N - 2 * r) := by
      obtain ⟨a, ha⟩ := hNe
      exact ⟨a - r, by omega⟩
    have hQ : Open.IsQuasisimple (↥I₀ ⧸ CFSG.pCore 2 ↥I₀) := by
      have htop : barM I₀ I₀ = ⊤ := by
        rw [barM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
      exact Open.IsQuasisimple.of_mulEquiv
        ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm hI₀c.component.2.2
    have hsnd : ∀ K : Subgroup G, K ≤ normalizer (S : Set G) ⊓ L →
        (∃ ε : ↥I₀ ≃* ↥K, True) → imgPL X (normalizer (S : Set G) ⊓ L) K ≠ ⊥ →
        ⁅imgPL X (normalizer (S : Set G) ⊓ L) K, imgPL X (normalizer (S : Set G) ⊓ L) K⁆ =
          imgPL X (normalizer (S : Set G) ⊓ L) K →
        (imgPL X (normalizer (S : Set G) ⊓ L) K).IsSubnormal →
        ((imgPL X (normalizer (S : Set G) ⊓ L) K).map φ.toMonoidHom).map
          (MonoidHom.snd _ _) = ⊥ := by
      rintro K hKN ⟨ε, -⟩ hne hp hs
      by_contra hbot
      set D := (imgPL X (normalizer (S : Set G) ⊓ L) K).map φ.toMonoidHom with hD
      have hA := eq_alternatingGroup_of_perfect hbot
        (by rw [← Subgroup.map_commutator, hD, ← Subgroup.map_commutator, hp])
        ((hs.map (f := φ.toMonoidHom) φ.surjective).map Prod.snd_surjective)
      have hKX : K ≤ X := hKN.trans hNX
      have hKP : barM X K ≤ Pb := Subgroup.map_mono fun y hy => by
        rw [Subgroup.mem_subgroupOf] at hy ⊢
        exact hKN hy
      set β := CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub hKX
      have hβ := CFSG.HardMathSupport.Cooperstein.Proving.barMHomSub_surjective hKX
      set γ := (Subgroup.subgroupOfEquivOfLe hKP).symm
      set δ := (QuotientGroup.mk' (CFSG.pCore 2 ↥Pb)).subgroupMap ((barM X K).subgroupOf Pb)
      set ε' := φ.toMonoidHom.subgroupMap (imgPL X (normalizer (S : Set G) ⊓ L) K)
      set σ := (MonoidHom.snd (Equiv.Perm (Fin r)) (Equiv.Perm (Fin (N - 2 * r)))).subgroupMap D
      set ι := (MulEquiv.subgroupCongr hA.2)
      set ψ : ↥I₀ →* alternatingGroup (Fin (N - 2 * r)) :=
        ι.toMonoidHom.comp (σ.comp (ε'.comp (δ.comp (γ.toMonoidHom.comp (β.comp ε.toMonoidHom)))))
      have hψ : Function.Surjective ψ := by
        intro a
        obtain ⟨a1, rfl⟩ := ι.surjective a
        obtain ⟨a2, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ a1
        obtain ⟨a3, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ a2
        obtain ⟨a4, rfl⟩ := MonoidHom.subgroupMap_surjective _ _ a3
        obtain ⟨a5, rfl⟩ := γ.surjective a4
        obtain ⟨a6, rfl⟩ := hβ a5
        obtain ⟨a7, rfl⟩ := ε.surjective a6
        exact ⟨a7, rfl⟩
      haveI : IsSimpleGroup (alternatingGroup (Fin (N - 2 * r))) :=
        alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hA.1)
      have hnc : ∀ (m : ℕ), 5 ≤ m → ∃ a b : alternatingGroup (Fin m), a * b ≠ b * a := by
        intro m hm
        by_contra hc
        push Not at hc
        haveI : Nontrivial (alternatingGroup (Fin m)) :=
          (alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hm)).toNontrivial
        have hz := alternatingGroup.center_eq_bot (α := Fin m) (by rw [Nat.card_fin]; omega)
        obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin m))
        have hac : a ∈ Subgroup.center (alternatingGroup (Fin m)) :=
          Subgroup.mem_center_iff.mpr fun b => hc b a
        rw [hz, Subgroup.mem_bot] at hac
        exact ha hac
      obtain ⟨eA⟩ := CFSG.Quasithin.Vol2.Ch11.SecB.nonempty_mulEquiv_of_two_surjective
        (hnc 5 le_rfl) (hnc _ hA.1) CFSG.pCore_isPGroup hQ f hf ψ hψ
      have hcard := Nat.card_congr eA.toEquiv
      rw [nat_card_alternatingGroup (α := Fin 5), Nat.card_fin] at hcard
      have h5 := eq_five_of_card_alt hA.1 (by rw [← hcard]; rfl)
      rw [h5] at hse
      exact absurd hse (by decide)
    obtain ⟨g1, g2, g3⟩ := hfacts₀
    obtain ⟨k1, k2, k3⟩ := hfacts₁ t htS htL
    obtain ⟨h1le, -, -, -⟩ := hconj t htS htL
    refine hfinish t htS htL (eq_of_mulEquiv_perm_prod φ g1 g2 g3 ?_ k1 k2 k3 ?_)
    · exact hsnd I₀ hI₀.le ⟨MulEquiv.refl _, trivial⟩ g1 g2 g3
    · exact hsnd _ h1le ⟨I₀.equivMapOfInjective _ (MulAut.conj t).injective, trivial⟩ k1 k2 k3

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

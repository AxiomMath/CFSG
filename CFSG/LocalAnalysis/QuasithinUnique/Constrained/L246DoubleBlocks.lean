module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourRank1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin CFSG.SectionRank
open scoped MatrixGroups

namespace L246Double

variable {G : Type} [Group G]

theorem le_conjJoin_self {S L : Subgroup G} : L ≤ conjJoin S L := fun x hx =>
  Subgroup.mem_iSup_of_mem (⟨1, S.one_mem⟩ : S) ⟨x, hx, by simp⟩

theorem conjJoin_mono {S₁ S L : Subgroup G} (h : S₁ ≤ S) : conjJoin S₁ L ≤ conjJoin S L :=
  iSup_le fun s => le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ⟨s, h s.2⟩

theorem le_normalizer_conjJoin {S L : Subgroup G} :
    S ≤ Subgroup.normalizer (conjJoin S L : Set G) := by
  refine CFSG.QuasithinUnique.Setup.le_normalizer_of_map_conj_le fun g hg => ?_
  rw [conjJoin, Subgroup.map_iSup]
  refine iSup_le fun s => ?_
  rw [Subgroup.map_map]
  have h1 : (MulAut.conj g).toMonoidHom.comp (MulAut.conj (s : G)).toMonoidHom =
      (MulAut.conj (((⟨g, hg⟩ : S) * s : S) : G)).toMonoidHom := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [h1]
  exact le_iSup (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom) ((⟨g, hg⟩ : S) * s)

theorem conjJoin_le_of_le {S₁ L K : Subgroup G} (hLK : L ≤ K) (hS : S₁ ≤ K) :
    conjJoin S₁ L ≤ K := by
  refine iSup_le fun s => ?_
  rintro _ ⟨l, hl, rfl⟩
  exact K.mul_mem (K.mul_mem (hS s.2) (hLK hl)) (K.inv_mem (hS s.2))

theorem le_normalizer_of_le_normalizer {L N : Subgroup G} (hLN : L ≤ N)
    (hN : N ≤ Subgroup.normalizer (L : Set G)) : L ≤ Subgroup.normalizer (N : Set G) := by
  refine CFSG.QuasithinUnique.Setup.le_normalizer_of_map_conj_le fun x hx => ?_
  rintro _ ⟨n, hn, rfl⟩
  have h1 : n⁻¹ * x * n ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 (hN (N.inv_mem hn)) x).1 hx
    simpa using this
  have h2 : (MulAut.conj x).toMonoidHom n = n * ((n⁻¹ * x * n) * x⁻¹) := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [h2]
  exact N.mul_mem hn (hLN (L.mul_mem h1 (L.inv_mem hx)))

section NoLarger

variable [Finite G]

theorem eq_of_le_isChi0Block_conj
    {X S L Lh : Subgroup G} (hS : IsSylowTwoOf S X)
    (hLh : IsChi0Block X Lh)
    (hLtype : (∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ IsAltType L 5) (hLLh : L ≤ Lh)
    (hL0 : L ≠ ⊥) (hLperf : ⁅L, L⁆ = L)
    (hnorm : conjJoin S L ≤ Subgroup.normalizer (L : Set G)) : L = Lh := by
  classical
  obtain ⟨x, hxL, hxQ, k, hxk⟩ := L238.exists_twoElement_not_mem_blockQ hLtype
  have hS₁ : IsSylowTwoOf (S ⊓ Lh) Lh :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hS hLh.1.2.1 hLh.1.2.2
  set S₁ := S ⊓ Lh with hS₁def
  have hS₁Lh : S₁ ≤ Lh := inf_le_right
  have hA : L ⊔ S₁ ≤ Lh := sup_le hLLh hS₁Lh
  have hLQ : blockQ Lh ⊓ L ≤ blockQ L := by
    refine le_pCoreOf_of_normalizes inf_le_right ?_ ((C1.blockQ_isPGroup Lh).to_le inf_le_left)
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨C1.le_normalizer_blockQ Lh (hLLh hl), Subgroup.le_normalizer hl⟩
  have hmain : Lh ∈ cComp X →
      (∃ (F : Type) (_ : Field F) (_ : Fintype F) (m : ℕ), Fintype.card F = 2 ^ m ∧
        0 < m ∧ ∃ α : ↥Lh →* SL(2, F), Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥Lh) →
      L = Lh := by
    intro hKC hmod
    rcases L238.dickson_block hS₁ le_sup_right hA hmod with hAeq | hAN
    ·
      have hNLh : conjJoin S₁ L ≤ Lh := conjJoin_le_of_le hLLh hS₁Lh
      have hLN : L ≤ conjJoin S₁ L := le_conjJoin_self
      have hNn : conjJoin S₁ L ≤ Subgroup.normalizer (L : Set G) :=
        (conjJoin_mono (inf_le_left : S₁ ≤ S)).trans hnorm
      have hLnN : L ≤ Subgroup.normalizer (conjJoin S₁ L : Set G) :=
        le_normalizer_of_le_normalizer hLN hNn
      have hS₁nN : S₁ ≤ Subgroup.normalizer (conjJoin S₁ L : Set G) := le_normalizer_conjJoin
      have hpow : ∀ g : ↥Lh, ∃ j : ℕ, (g : G) ^ 2 ^ j ∈ conjJoin S₁ L := by
        intro g
        have hgA : (g : G) ∈ conjJoin S₁ L ⊔ S₁ := by
          have : (g : G) ∈ L ⊔ S₁ := by
            rw [hAeq]
            exact g.2
          exact sup_le_sup_right hLN S₁ this
        exact C1.exists_pow_mem_of_mem_sup hS₁.isPGroup hS₁nN hgA
      have hnormal : ((conjJoin S₁ L).subgroupOf Lh).Normal := by
        refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNLh).mpr ?_
        rw [← hAeq]
        exact sup_le hLnN hS₁nN
      have h2 : IsPGroup 2 (↥Lh ⧸ (conjJoin S₁ L).subgroupOf Lh) := fun q =>
        QuotientGroup.induction_on q fun g => by
          obtain ⟨j, hj⟩ := hpow g
          refine ⟨j, ?_⟩
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
          exact hj
      have htop := hLh.1.1.1 ((conjJoin S₁ L).subgroupOf Lh) h2
      have hLhN : Lh ≤ conjJoin S₁ L := (Subgroup.subgroupOf_eq_top).mp htop
      have hLn : (L.subgroupOf Lh).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLLh).mpr (hLhN.trans hNn)
      by_contra hne
      have hlt : L < Lh := lt_of_le_of_ne hLLh hne
      have hsubL : IsSubnormal L Lh := A3.subnormal_of_normal hLLh hLn
      exact not_subnormal_of_mem_cComp hKC hlt hL0 hLperf
        (A3.subnormal_trans hsubL (subnormal_of_mem_cComp hKC))
    ·
      exfalso
      have hS₁A : IsSylowTwoOf S₁ (L ⊔ S₁) := C1GN.isSylowTwoOf_of_le hS₁ le_sup_right hA
      have hxA : x ∈ L ⊔ S₁ := Subgroup.mem_sup_left hxL
      have hz : IsPGroup 2 (Subgroup.zpowers x) := by
        have hcard : Nat.card (Subgroup.zpowers x) = orderOf x := Nat.card_zpowers x
        have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
        exact IsPGroup.of_card (by rw [hcard, hj])
      obtain ⟨y, hy, hzy⟩ := F7.isSylowTwoOf_exists_conj_le hS₁A
        ((Subgroup.zpowers_le).mpr hxA) hz
      have hyS : conjSub y S₁ = S₁ := B6.conjSub_eq_self (hAN hy)
      have hxS : x ∈ S₁ := by
        have := hzy (Subgroup.mem_zpowers x)
        rwa [hyS] at this
      have hxQ' : x ∈ blockQ L := by
        refine le_pCoreOf_of_normalizes (inf_le_left : L ⊓ S₁ ≤ L) ?_
          (hS₁.isPGroup.to_le (inf_le_right : L ⊓ S₁ ≤ S₁)) ⟨hxL, hxS⟩
        intro l hl
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hl, hAN (Subgroup.mem_sup_left hl)⟩
      exact hxQ hxQ'
  rcases hLh.2 with hlin | h3 | h5
  · exact hmain (L238.mem_cComp_of_isChi0Block_nonsolvable hLh.1 (Or.inl hlin))
      (L238.exists_sl2_model (Or.inl hlin))
  · exfalso
    exact hxQ (hLQ ⟨L238.mem_blockQ_of_twoElement_alt3 h3 (hLLh hxL) ⟨k, hxk⟩, hxL⟩)
  · exact hmain (L238.mem_cComp_of_isChi0Block_nonsolvable hLh.1 (Or.inr h5))
      (L238.exists_sl2_model (Or.inr h5))

end NoLarger

end L246Double

end CFSG.QuasithinUnique

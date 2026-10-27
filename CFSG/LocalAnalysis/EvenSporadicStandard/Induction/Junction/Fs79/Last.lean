module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Fs79.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.GroupLemmas
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H]

theorem map_subtype_map_conj_subgroupOf {Y K : Subgroup H} (hKY : K ≤ Y) (g : ↥Y) :
    ((K.subgroupOf Y).map (MulAut.conj g).toMonoidHom).map Y.subtype =
      K.map (MulAut.conj (g : H)).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨⟨y, hKY hy⟩, hy, rfl⟩, by simp [MulAut.conj_apply]⟩

theorem stdBare_subgroupOf_of_stdBare [Finite H] {Y M : Subgroup H} (hMY : M ≤ Y)
    (h : StdBare M) : StdBare (M.subgroupOf Y) := by
  refine ⟨fun g hbot => ?_, fun g hg => ?_⟩
  · apply h.1 (g : H)
    have h1 := congrArg (Subgroup.map Y.subtype) hbot
    rw [Subgroup.map_commutator, Subgroup.map_bot, map_subtype_map_conj_subgroupOf hMY,
      Subgroup.map_subgroupOf_eq_of_le hMY] at h1
    exact h1
  · have hgH : (g : H) ∉ normalizer (M : Set H) := by
      intro hn
      apply hg
      rw [Subgroup.mem_normalizer_iff] at hn ⊢
      intro n
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hn (n : H)
    refine (h.2 (g : H) hgH).of_dvd_nat ?_
    set C : Subgroup ↥Y := centralizer ((M.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)
    have hCM : ∀ z ∈ C, (z : H) ∈ centralizer (M : Set H) := by
      intro z hz
      refine mem_centralizer_iff.2 fun m hm => ?_
      have := mem_centralizer_iff.1 hz ⟨m, hMY hm⟩ (by simpa [Subgroup.mem_subgroupOf] using hm)
      exact congrArg Subtype.val this
    have hle : (C ⊓ C.map (MulAut.conj g).toMonoidHom).map Y.subtype ≤
        centralizer (M : Set H) ⊓
          (centralizer (M : Set H)).map (MulAut.conj (g : H)).toMonoidHom := by
      rintro _ ⟨z, ⟨hz1, hz2⟩, rfl⟩
      refine ⟨hCM z hz1, ?_⟩
      obtain ⟨w, hw, hwz⟩ := hz2
      refine ⟨(w : H), hCM w hw, ?_⟩
      have := congrArg Subtype.val hwz
      simpa [MulAut.conj_apply] using this
    have h2 := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective Y.subtype_injective] at h2

theorem stdModulo_of_stdBare_subgroupOf {Y Z K : Subgroup H} (hZ : Z = ⊥)
    (h : StdBare (K.subgroupOf Y)) : StdModulo Y Z K := by
  subst hZ
  have hbot : (⊥ : Subgroup H).subgroupOf Y = ⊥ := Subgroup.bot_subgroupOf Y
  have hN : ((⊥ : Subgroup H).subgroupOf Y).Normal := by
    rw [hbot]
    exact Subgroup.normal_bot
  refine ⟨hN, ?_⟩
  let e : (↥Y ⧸ (⊥ : Subgroup H).subgroupOf Y) ≃* ↥Y :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have h1 := stdBare_map_mulEquiv e.symm h
  have hmap : (K.subgroupOf Y).map e.symm.toMonoidHom =
      (K.subgroupOf Y).map (QuotientGroup.mk' ((⊥ : Subgroup H).subgroupOf Y)) := rfl
  rwa [hmap] at h1

variable [Finite H]

theorem last_link {N M : Subgroup H} {t : H} (hN : FStarSimple N)
    (hperf : ∀ P : Subgroup H, ⁅P, P⁆ = P → P ≤ N) (ht : orderOf t = 2)
    (hM : IsCompIn M (centralizer ({t} : Set H))) (hstd : StdBare M) : LConn M N := by
  have htt : t * t = 1 := Solomon78.mul_self_eq_one_of_orderOf_eq_two ht
  have hts : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_orderOf_two ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : IsPGroup 2 ↥(⊥ : Subgroup H) := IsPGroup.of_card (n := 0) (by simp)
  have hMt : IsCompIn M (centralizer ((zpowers t : Subgroup H) : Set H)) := by
    rw [centralizer_zpowers_eq]
    exact hM
  have hMq := hM.isQuasisimple
  have hMN : M ≤ N := hperf M (Subgroup.isPerfect_iff.1 hMq.1)
  have htop : centralizer (((⊥ : Subgroup H)) : Set H) = ⊤ := by
    ext x
    simp only [mem_top, iff_true]
    rw [mem_centralizer_iff]
    intro g hg
    rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hg
    rw [hg, one_mul, mul_one]
  have hNcomp : IsCompIn N (centralizer ((⊥ : Subgroup H) : Set H)) := by
    rw [htop]
    exact isCompIn_of_normal le_top hN.isQuasisimple (hN.normal.subgroupOf _)
  have htN : t ∈ normalizer (N : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hN.normal]
    exact mem_top _
  have hNt : N.map (MulAut.conj t).toMonoidHom = N := Solomon78.mem_normalizer_iff_map_conj_eq.1 htN
  have hlayer : layerIn (centralizer ((⊥ : Subgroup H) : Set H)) = N :=
    le_antisymm (layerIn_le_iff.2 fun E hE => (hN.eq_of_isCompIn_bot hE).le)
      (le_layerIn_of_isCompIn hNcomp)
  have hconj : conjClosure M N = N := by
    refine le_antisymm (conjClosure_le_of_le_normalizer hMN Subgroup.le_normalizer) ?_
    have hCN : conjClosure M N ≤ N := conjClosure_le_of_le_normalizer hMN Subgroup.le_normalizer
    have hn : ((conjClosure M N).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).2 (le_normalizer_conjClosure M N)
    have := hN.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((conjClosure M N).subgroupOf N) with h | h
    · exfalso
      have hNt' := CFSG.LocalCores.isQuasisimple_nontrivial hMq
      obtain ⟨x, hx⟩ := exists_ne (1 : ↥M)
      apply hx
      have hmem : (⟨(x : H), hMN x.2⟩ : ↥N) ∈ (conjClosure M N).subgroupOf N :=
        le_conjClosure M N x.2
      rw [h, Subgroup.mem_bot] at hmem
      have h1 : (x : H) = 1 := congrArg (fun z : ↥N => (z : H)) hmem
      exact Subtype.ext h1
    · exact Subgroup.subgroupOf_eq_top.1 h
  have hstdY : StdModulo (N ⊔ zpowers t) (centralizer (N : Set H)) M :=
    stdModulo_of_stdBare_subgroupOf hN.centralizer_eq_bot
      (stdBare_subgroupOf_of_stdBare (hMN.trans le_sup_left) hstd)
  have hsN : t ∈ normalizer (((⊥ : Subgroup H)) : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  have hsT : t ^ 2 ∈ (⊥ : Subgroup H) := Subgroup.mem_bot.2 (by rw [pow_two]; exact htt)
  have hL0 : IsCompIn M (centralizer ((⊥ ⊔ zpowers t : Subgroup H) : Set H)) := by
    rw [bot_sup_eq]
    exact hMt
  have h1 := Sol78Links.single hts hbot hMt hNcomp hts hsN hsT hL0 (hMN.trans le_sup_left)
    (by rw [hNt, sup_idem, hlayer, hconj]) (Or.inr ⟨hNt.symm, hstdY⟩)
  exact ⟨1, _, _, _, h1, by simp, by simp, fun _ _ _ => trivial⟩

end CFSG.EvenSporadicStandard.Induction.Junction

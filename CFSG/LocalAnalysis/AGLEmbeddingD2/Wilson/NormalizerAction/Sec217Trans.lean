module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217Elements
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217DTrans
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217TransPkg
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.A6Matching
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217CentD

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.SectionRank.Native
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint

theorem mem_normalizer_inf' {X : Type*} [Group X] {A I : Subgroup X} {g : X}
    (hA : g ∈ Subgroup.normalizer (A : Set X)) (hI : g ∈ Subgroup.normalizer (I : Set X)) :
    g ∈ Subgroup.normalizer ((A ⊓ I : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hI ⊢
  intro x
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(hA x).1 h1, (hI x).1 h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(hA x).2 h1, (hI x).2 h2⟩

variable {G : Type} [Group G] [Finite G]

section Main

set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem Cover217.exists_transvection {A E U : Subgroup G} {c : G} {L : Subgroup G}
    (h : Cover217 A E U c L) (hθ : aschbacherSolvableCore 3 L = ⊥) (hAL : A ≤ L) {a : G}
    (hv : Valid217 A c L a) {U₀ K : Subgroup G} (hK : Cover217 A E U₀ a K)
    (hθK : aschbacherSolvableCore 3 K = ⊥) (hAK : A ≤ K) (hvK : Valid217 A a K c)
    (hIK : iCore L a ≤ K) : ∃ t ∈ wStar A, IsTransvectionOn t := by
  have hIK' := h.iCore_K_eq hθ hAL hv hK hθK hAK hvK hIK
  obtain ⟨u, huL, huA, huD, hua, hu8, huc, huI, hu4⟩ := h.exists_u hθ hAL hv
  obtain ⟨v, hvK', hvA, hvD, hvc, hv8, hva, hvI, hv4⟩ := hK.exists_u hθK hAK hvK
  rw [hIK'] at hvI hv4
  obtain ⟨eI⟩ := h.iCore_equiv hθ hAL hv
  have hE9 := h.card_inf_iCore hθ hAL hv
  have hu8' : u ^ 8 = 1 := by rw [← hu8]; exact pow_orderOf_eq_one u
  have hv8' : v ^ 8 = 1 := by rw [← hv8]; exact pow_orderOf_eq_one v
  obtain ⟨x, hxE, k, hk, hxt⟩ := exists_match_pgl (inf_le_right : A ⊓ iCore L a ≤ iCore L a)
    hE9 ⟨eI⟩ huI (mem_normalizer_inf' huA huI) hvI (mem_normalizer_inf' hvA hvI) hu8' hu4 hv8' hv4
  set I := iCore L a with hIdef
  set t : G := u * (x * v ^ k)⁻¹ with ht
  have hab := h.isElemAbelian_A
  have hab' := isElemAbelian_iff.1 hab
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hab'.1 x hx y hy
  have ha3 : a ^ 3 = 1 := hab'.2 a hv.mem
  have hc3 : c ^ 3 = 1 := hab'.2 c h.c_mem_A
  have hca : c * a = a * c := h.c_comm a (hAL hv.mem)
  have ha1 : a ≠ 1 := by
    rintro rfl; exact hv.not_mem (Subgroup.one_mem _)
  have hc1 : c ≠ 1 := by
    intro h1
    have := h.orderOf_c
    rw [h1, orderOf_one] at this
    omega
  have hnot : c ∉ Subgroup.zpowers a := hvK.not_mem
  have hDA : dGroup a c ≤ A :=
    sup_le (Subgroup.zpowers_le.2 hv.mem) (Subgroup.zpowers_le.2 h.c_mem_A)
  have hxA : x ∈ A := (hxE).1
  have hDI : dGroup a c ≤ Subgroup.centralizer (I : Set G) := by
    refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro i hi
      exact Subgroup.mem_centralizer_singleton_iff.1 (iCore_le L a hi).1
    · rw [Subgroup.mem_centralizer_iff]
      intro i hi
      exact (h.c_comm i (iCore_le L a hi).2).symm
  have htI : t ∈ Subgroup.centralizer (I : Set G) := hxt
  have hQc : ∀ n : ℕ, (n = 1 ∨ n = 2) → t ^ n * c * (t ^ n)⁻¹ ∈ zpowers c →
      ∀ δ ∈ zpowers a ⊔ zpowers c, t ^ n * δ = δ * t ^ n := by
    intro n _ hmem δ hδ
    have htI' : t ^ n ∈ Subgroup.centralizer (I : Set G) := Subgroup.pow_mem _ htI n
    have hgL := h.normalizes_L hθ hAL hv htI' (normalizer_zpowers_of_conj_mem hmem)
    exact h.centralizes_D hθ hAL hv hgL htI' δ hδ
  have hQa : ∀ n : ℕ, (n = 1 ∨ n = 2) → t ^ n * a * (t ^ n)⁻¹ ∈ zpowers a →
      ∀ δ ∈ zpowers a ⊔ zpowers c, t ^ n * δ = δ * t ^ n := by
    intro n _ hmem δ hδ
    have htI' : t ^ n ∈ Subgroup.centralizer (iCore K c : Set G) := by
      rw [hIK']; exact Subgroup.pow_mem _ htI n
    have hgK := hK.normalizes_L hθK hAK hvK htI' (normalizer_zpowers_of_conj_mem hmem)
    have hδ' : δ ∈ dGroup c a := by
      unfold dGroup; rw [sup_comm]; exact hδ
    exact hK.centralizes_D hθK hAK hvK hgK htI' δ hδ'
  have hvD' : v ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G) := by
    rw [sup_comm]; exact hvD
  obtain ⟨htD, d, hdD, hd1, htd, ⟨δ0, hδ0, hδ0t⟩, hall⟩ :=
    transvection_on_D hca ha3 hc3 ha1 hc1 hnot (u := u) (v := v) (x := x) (t := t) (k := k) hk
      huD huc hua hu8' hvD' hva hvc hv8' (fun δ hδ => hcommA x hxA δ (hDA hδ)) ht hQc hQa
  have htNA : t ∈ Subgroup.normalizer (A : Set G) := by
    rw [ht]
    exact Subgroup.mul_mem _ huA (Subgroup.inv_mem _
      (Subgroup.mul_mem _ (Subgroup.le_normalizer hxA) (Subgroup.pow_mem _ hvA k)))
  refine ⟨A.normalizerMonoidHom ⟨t, htNA⟩, ⟨⟨t, htNA⟩, rfl⟩, ?_⟩
  have hZI := center_eq_bot_of_equiv_alt6 I eI
  have hdisj : Disjoint (dGroup a c) (A ⊓ I) := by
    rw [Subgroup.disjoint_def]
    intro y hyD hyI
    have : (⟨y, hyI.2⟩ : ↥I) ∈ Subgroup.center ↥I := by
      rw [Subgroup.mem_center_iff]
      intro z
      have := Subgroup.mem_centralizer_iff.1 (hDI hyD) (z : G) z.2
      exact Subtype.ext this
    rw [hZI, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hyz : ∀ y ∈ A, ∀ w ∈ dGroup a c, y * w * y⁻¹ = w := fun y hy w hw => by
    rw [hcommA y hy w (hDA hw)]; group
  have hN : A ⊓ I ≤ Subgroup.normalizer ((dGroup a c : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; rw [hyz y hy.1 z hz]; exact hz
    · intro hz
      have h2 := hyz y⁻¹ (A.inv_mem hy.1) _ hz
      have : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
      rw [this] at h2
      rw [h2]; exact hz
  have hD9 : Nat.card (dGroup a c) = 9 := by
    have e : (ZMod 3 × ZMod 3) ≃ dGroup a c := Equiv.ofBijective
      (fun v => ⟨kap a c v, (mem_D_iff hca ha3 hc3).2 ⟨v, rfl⟩⟩)
      ⟨fun v w hvw => kap_inj hca ha3 hc3 ha1 hc1 hnot (congrArg Subtype.val hvw), fun ⟨y, hy⟩ => by
        obtain ⟨v, rfl⟩ := (mem_D_iff hca ha3 hc3).1 hy
        exact ⟨v, rfl⟩⟩
    rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zmod]
  have hcard : Nat.card A ≤ Nat.card ↥(dGroup a c ⊔ (A ⊓ I)) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj, hE9,
      hD9, h.card]
    norm_num
  have hE : ∀ ε ∈ A ⊓ I, t * ε * t⁻¹ = ε := fun ε hε => by
    have := Subgroup.mem_centralizer_iff.1 htI ε hε.2
    calc t * ε * t⁻¹ = (ε * t) * t⁻¹ := by rw [← this]
      _ = ε := by group
  exact isTransvectionOn_of_action hDA inf_le_left hcard hcommA htNA hdD
    (hab'.2 d (hDA hdD)) hd1 htd hall ⟨δ0, hδ0, hδ0t⟩ hE

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

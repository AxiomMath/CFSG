module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFj
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SuzTau
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58NFb
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7OS1

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

namespace Sub58

variable {G : Type*} [Group G]

theorem normalizer_eq_centralizer_of_card_two {E : Subgroup G} (hE : Nat.card E = 2) {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) : normalizer (E : Set G) = centralizer ({e} : Set G) := by
  have huniq := (Nat.card_eq_two_iff' (1 : ↥E)).mp hE
  have hmem : ∀ x ∈ E, x ≠ 1 → x = e := by
    intro x hx hx1
    have h1 : (⟨x, hx⟩ : ↥E) ≠ 1 := fun h0 => hx1 (congrArg Subtype.val h0)
    have h2 : (⟨e, he⟩ : ↥E) ≠ 1 := fun h0 => he1 (congrArg Subtype.val h0)
    exact congrArg Subtype.val (huniq.unique h1 h2)
  ext g
  rw [mem_normalizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have h1 : g * e * g⁻¹ ∈ E := (hg e).mp he
    have h2 : g * e * g⁻¹ ≠ 1 := by
      intro h0
      apply he1
      rw [show e = g⁻¹ * (g * e * g⁻¹) * g by group, h0]
      group
    have h3 := hmem _ h1 h2
    calc g * e = g * e * g⁻¹ * g := by group
      _ = e * g := by rw [h3]
  · intro hg
    have hz : ∀ w ∈ E, g * w * g⁻¹ = w := by
      intro w hw
      by_cases hw1 : w = 1
      · rw [hw1]
        group
      · rw [hmem w hw hw1, hg]
        group
    intro z
    constructor
    · intro hzE
      rw [hz z hzE]
      exact hzE
    · intro hzE
      have h1 := hz _ hzE
      have h2 : g * z * g⁻¹ = z := by
        have h3 : g⁻¹ * (g * (g * z * g⁻¹) * g⁻¹) * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1]
        rwa [show g⁻¹ * (g * (g * z * g⁻¹) * g⁻¹) * g = g * z * g⁻¹ by group,
          show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h3
      rw [← h2]
      exact hzE

variable [Finite G]

theorem orderOf_eq_two_of_card_two {E : Subgroup G} (hE : Nat.card E = 2) {e : G}
    (he : e ∈ E) (he1 : e ≠ 1) : orderOf e = 2 := by
  have h1 := orderOf_dvd_natCard (⟨e, he⟩ : ↥E)
  rw [Subgroup.orderOf_mk, hE] at h1
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
  · exact absurd (orderOf_eq_one_iff.mp h2) he1
  · exact h2

theorem layerIn_eq_self_of_isPComponent {L Y : Subgroup G} (hLY : L ≤ Y)
    (hL : IsPComponent 2 (L.subgroupOf Y)) : layerIn L = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, h2, h3⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Y hLY).mp hL
  have hLL : IsPComponent 2 (L.subgroupOf L) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L L le_rfl).mpr
      ⟨by rw [subgroupOf_self]; exact (inferInstance : (⊤ : Subgroup ↥L).Normal).isSubnormal,
        h2, h3⟩
  have htop : pLayer ↥L 2 = ⊤ := by
    rw [eq_top_iff, ← subgroupOf_self L]
    exact le_sSup hLL
  show (pLayer ↥L 2).map L.subtype = L
  rw [htop, ← MonoidHom.range_eq_map, range_subtype]

theorem isoCorrSub_fixedLayer_of_mem {a : G} {J E : Subgroup G}
    (hJa : J ≤ centralizer ({a} : Set G))
    (hJsub : (J.subgroupOf (centralizer ({a} : Set G))).IsSubnormal)
    (hJq : IsQuasisimple (↥J ⧸ pPrimeCore 2 ↥J)) (hEa : E ≤ centralizer ({a} : Set G))
    (hEJ : E ≤ coreActionKernel J) (hE2 : IsPGroup 2 E) (haE : a ∈ E) :
    IsoCorrSub a J E (GSLit.fixedLayer J E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := GSLit.fixedLayer J E with hL
  have hCE : centralizer (E : Set G) ≤ centralizer ({a} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr haE)
  have hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set G) ⊓
      centralizer (E : Set G))) :=
    GSLit.fixedLayer_isPComponent hJa hJsub hEa hEJ hE2 hJq
  rw [inf_of_le_right hCE] at hLc
  have hLC : L ≤ centralizer (E : Set G) := (GSLit.fixedLayer_le_inf J E).trans inf_le_right
  have hCN : centralizer (E : Set G) ≤ normalizer (E : Set G) := centralizer_le_normalizer _
  have hLa : L ≤ centralizer ({a} : Set G) := hLC.trans hCE
  have hLNc : IsPComponent 2 (L.subgroupOf (normalizer (E : Set G))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hLC hCN
      (Subgroup.Normal.isSubnormal (Subgroup.normal_subgroupOf_centralizer_normalizer _)) hLc
  have haL : a ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hl
    exact mem_centralizer_singleton_iff.mp (hLa hl)
  refine ⟨hLC.trans hCN, hLNc, conjugate_eq_of_mem_normalizer (centralizer_le_normalizer _ haL),
    sup_eq_left.mpr (map_subtype_le _), ?_⟩
  rw [inf_of_le_left hLa]
  exact (layerIn_eq_self_of_isPComponent hLC hLc).symm

theorem dihedral_step {G : Type} [Group G] [Finite G] {S' P E B' : Subgroup G} {a b : G}
    (hS'2 : IsPGroup 2 S') (hPS : P ≤ S') (hSN : S' ≤ normalizer (P : Set G))
    (haP : a ∈ P) (ha : orderOf a = 2) (haC : ∀ s ∈ S', s * a = a * s)
    (hB' : Nat.card B' = 2) (hbB : b ∈ B') (hb1 : b ≠ 1) (hB'P : B' ≤ P) (haB : a ∉ B')
    (hcb : Nat.card ↥(P ⊓ normalizer (B' : Set G)) = 4) (h8 : 8 ≤ Nat.card P)
    (hEP : E ≤ P) (haE : a ∉ E) :
    Nat.card E ≤ 2 ∧ (Nat.card E = 2 →
      Nat.card ↥(S' ⊓ normalizer (E : Set G)) = Nat.card ↥(S' ⊓ normalizer (B' : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := hS'2.to_le hPS
  have hNB : normalizer (B' : Set G) = centralizer ({b} : Set G) :=
    normalizer_eq_centralizer_of_card_two hB' hbB hb1
  have hb2 : orderOf b = 2 := orderOf_eq_two_of_card_two hB' hbB hb1
  have hcb₀ : Nat.card (centralizer ({(⟨b, hB'P hbB⟩ : ↥P)} : Set ↥P)) = 4 := by
    rw [centralizer_singleton_subgroupOf, Six.card_subgroupOf_eq, inf_comm, ← hNB]
    exact hcb
  obtain ⟨p₀, r₀, hcl₀, hc₀, hr₀, hrel₀⟩ := suzukiTausskyInput ↥P hP2 h8 ⟨b, hB'P hbB⟩
    (by rw [Subgroup.orderOf_mk]; exact hb2) hcb₀
  set p : G := (p₀ : G) with hpdef
  set r : G := (r₀ : G) with hrdef
  have hpP : p ∈ P := p₀.2
  have hrP : r ∈ P := r₀.2
  have hcl : closure {p, r} = P := by
    have h1 := congrArg (Subgroup.map P.subtype) hcl₀
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype, Set.image_insert_eq,
      Set.image_singleton] at h1
    exact h1
  have horder : orderOf p = orderOf p₀ := Subgroup.orderOf_coe p₀
  have hc : 2 * orderOf p = Nat.card P := by
    rw [horder]
    exact hc₀
  have hr2 : r ^ 2 = 1 := by
    rw [hrdef, ← SubgroupClass.coe_pow, hr₀, OneMemClass.coe_one]
  have hrel : r * p * r⁻¹ = p⁻¹ ∨ r * p * r⁻¹ = p ^ (orderOf p / 2 - 1) := by
    rcases hrel₀ with h1 | h1
    · left
      have h2 := congrArg Subtype.val h1
      simpa only [coe_mul, coe_inv] using h2
    · right
      have h2 := congrArg Subtype.val h1
      rw [horder]
      simpa only [coe_mul, coe_inv, SubgroupClass.coe_pow] using h2
  have hpow : ∃ n : ℕ, orderOf p = 2 ^ n := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) p₀
    exact ⟨n, by rw [horder, hn]⟩
  have h4 : 4 ≤ orderOf p := by omega
  have hnab : r * p * r⁻¹ ≠ p := by
    intro hcomm
    have hrp : r * p = p * r := by
      calc r * p = r * p * r⁻¹ * r := by group
        _ = p * r := by rw [hcomm]
    have hPp : P ≤ centralizer ({p} : Set G) := by
      rw [← hcl, closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact mem_centralizer_singleton_iff.mpr rfl
      · exact mem_centralizer_singleton_iff.mpr hrp
    have hPr : P ≤ centralizer ({r} : Set G) := by
      rw [← hcl, closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact mem_centralizer_singleton_iff.mpr hrp.symm
      · exact mem_centralizer_singleton_iff.mpr rfl
    have hPc : P ≤ centralizer ({b} : Set G) := by
      rw [← hcl, closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (hPp (hB'P hbB))).symm
      · exact mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp (hPr (hB'P hbB))).symm
    have h1 : P ⊓ normalizer (B' : Set G) = P := by
      rw [hNB]
      exact inf_eq_left.mpr hPc
    rw [h1] at hcb
    omega
  have haZ : a ∈ zpowers p := by
    rw [← inf_centralizer_eq_zpowers hpP hrP hcl hc hnab]
    exact mem_inf.mpr ⟨haP, mem_centralizer_singleton_iff.mpr (haC p (hPS hpP)).symm⟩
  have hinvZ : ∀ u ∈ zpowers p, orderOf u = 2 → u = a := by
    intro u hu hu2
    have h3 := eq_of_orderOf_eq_two_of_isCyclic (C := ↥(zpowers p)) (w := ⟨u, hu⟩)
      (w' := ⟨a, haZ⟩) (by rw [Subgroup.orderOf_mk]; exact hu2)
      (by rw [Subgroup.orderOf_mk]; exact ha)
    exact congrArg Subtype.val h3
  have hbig : ∀ F : Subgroup G, F ≤ P → 2 < Nat.card F → a ∈ F := by
    intro F hFP hF
    have hZP : zpowers p ≤ P := zpowers_le.mpr hpP
    have hidx : (zpowers p).relIndex P = 2 := by
      have h1 := relIndex_mul_card (H := zpowers p) (K := P)
      rw [inf_eq_left.mpr hZP, Nat.card_zpowers, ← hc] at h1
      have hpos : 0 < orderOf p := by omega
      exact Nat.eq_of_mul_eq_mul_right hpos h1
    have hle : (zpowers p).relIndex F ≤ 2 := by
      rw [← hidx]
      exact relIndex_le_of_le_right hFP (by rw [hidx]; norm_num)
    have h2 := relIndex_mul_card (H := zpowers p) (K := F)
    have hZF : 1 < Nat.card ↥(zpowers p ⊓ F) := by
      by_contra hcon
      push Not at hcon
      have : (zpowers p).relIndex F * Nat.card ↥(zpowers p ⊓ F) ≤ 2 * 1 :=
        Nat.mul_le_mul hle hcon
      omega
    have hZF2 : IsPGroup 2 ↥(zpowers p ⊓ F) := hP2.to_le (inf_le_left.trans hZP)
    have hdvd : 2 ∣ Nat.card ↥(zpowers p ⊓ F) := by
      rcases hZF2.card_eq_or_dvd with h3 | h3
      · omega
      · exact h3
    obtain ⟨⟨u, hu⟩, hu2⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    rw [Subgroup.orderOf_mk] at hu2
    rw [← hinvZ u (mem_inf.mp hu).1 hu2]
    exact (mem_inf.mp hu).2
  refine ⟨?_, fun hE2 => ?_⟩
  · by_contra hcon
    push Not at hcon
    exact haE (hbig E hEP hcon)
  · have : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE2]; norm_num)
    obtain ⟨⟨e, he⟩, he1⟩ := exists_ne (1 : ↥E)
    have he1' : e ≠ 1 := fun h0 => he1 (Subtype.ext h0)
    have he2 : orderOf e = 2 := orderOf_eq_two_of_card_two hE2 he he1'
    have heZ : e ∉ zpowers p := fun heZ => haE (hinvZ e heZ he2 ▸ he)
    have hbZ : b ∉ zpowers p := fun hbZ => haB (hinvZ b hbZ hb2 ▸ hbB)
    have hSP : ∀ s ∈ S', ∀ w ∈ P, s * w * s⁻¹ ∈ P :=
      fun s hs w hw => (mem_normalizer_iff.mp (hSN hs) w).mp hw
    have hSp : ∀ s ∈ S', s * p * s⁻¹ ∈ zpowers p := by
      intro s hs
      refine mem_zpowers_of_orderOf_eq hpP hrP hcl hc hr2 hrel h4 hpow hnab (hSP s hs p hpP) ?_
      have h3 := MulEquiv.orderOf_eq (MulAut.conj s) p
      rwa [MulAut.conj_apply] at h3
    have heq := Seven.card_centralizer_eq_of_maxClass hPS hpP hrP hcl hc hrel hpow h4 hnab hSp
      hSP (hEP he) heZ (hB'P hbB) hbZ
    rw [normalizer_eq_centralizer_of_card_two hE2 he he1', hNB]
    exact heq

end Sub58

namespace Hyp52

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem isPGroup_secPre {E' : Subgroup (h.secBar y)} (hE' : IsPGroup 2 E') :
    IsPGroup 2 (h.secPre y E') := by
  rintro ⟨g, hg⟩
  have hgG := secPre_le_G0 E' hg
  have h1 := secMk_mem_of_mem_secPre hg
  obtain ⟨k, hk⟩ := hE' ⟨_, h1⟩
  have hk' : (h.secMk y ⟨g, hgG⟩) ^ 2 ^ k = 1 := by
    have h2 := congrArg Subtype.val hk
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h2
  have h2 : ((⟨g, hgG⟩ : ↥(h.secG0 y)) ^ 2 ^ k : X) ∈ h.secB0 y := by
    have h3 : (⟨g, hgG⟩ : ↥(h.secG0 y)) ^ 2 ^ k ∈ h.secB0' y := by
      rw [← ker_secMk, MonoidHom.mem_ker, map_pow, hk']
    exact h3
  obtain ⟨m, hm⟩ := (h.isPGroup_secB0 y) ⟨_, h2⟩
  have h3 : g ^ 2 ^ (k + m) = 1 := by
    have h4 := congrArg Subtype.val hm
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h4
    rw [pow_add, pow_mul]
    exact h4
  exact ⟨k + m, Subtype.ext (by simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using h3)⟩

theorem inf_normalizer_B_eq_Q (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    {U : Subgroup X} (hU2 : IsPGroup 2 U) (hUa : U ≤ centralizer ({h.a} : Set X))
    (hQU : h.Q ≤ U) : U ⊓ normalizer (h.B : Set X) = h.Q := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E := zpowers h.a with hE
  have haE : h.a ∈ E := mem_zpowers _
  have hCSE := Six.sylow_centralizer_zpowers hSa
  have hUE : U ≤ centralizer (E : Set X) := by
    intro u hu
    rw [hE, centralizer_zpowers_eq]
    exact hUa hu
  obtain ⟨g, hgE, hgU⟩ := exists_conjugate_le_of_sylow hCSE hUE hU2
  have hga : g ∈ centralizer ({h.a} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hgE h.a haE).symm
  have hca : g⁻¹ ∈ centralizer ({h.a} : Set X) := inv_mem hga
  have hgJ : g ∈ normalizer (h.J : Set X) := hCN hga
  have hcJ : g⁻¹ ∈ normalizer (h.J : Set X) := inv_mem hgJ
  set c := g⁻¹ with hcdef
  set S' := conjugate h.S c with hS'
  have hconjS' : conjugate S' g = h.S := by
    rw [hS', conjugate_conjugate, hcdef, inv_mul_cancel, conjugate_one]
  have hconjInf : ∀ A A' : Subgroup X, conjugate (A ⊓ A') g = conjugate A g ⊓ conjugate A' g :=
    fun A A' => Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective
  have hconjN : ∀ F : Subgroup X,
      conjugate (normalizer (F : Set X)) g = normalizer (conjugate F g : Set X) :=
    fun F => map_equiv_normalizer_eq F (MulAut.conj g⁻¹)
  have hconjC : conjugate (coreActionKernel h.J) g = coreActionKernel h.J :=
    Six.conjugate_coreActionKernel hgJ
  have hUS' : U ≤ S' := by
    intro t ht
    have h1 : g⁻¹ * t * g ∈ h.S := (mem_inf.mp (hgU (by
      rw [mem_conjugate_iff, show g * (g⁻¹ * t * g) * g⁻¹ = t by group]
      exact ht))).1
    rw [hS', mem_conjugate_iff, hcdef, inv_inv]
    exact h1
  have hBU : h.B ≤ U := h.B_le_Q.trans hQU
  have hBC : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hcard : Nat.card ↥(S' ⊓ normalizer (h.B : Set X)) ≤ Nat.card h.Q := by
    by_contra hlt
    push Not at hlt
    set E' := conjugate h.B g with hE'
    have hE'S : E' ≤ h.S := (map_mono hBU).trans (hgU.trans inf_le_left)
    have hE'C : E' ≤ coreActionKernel h.J := by
      rw [← hconjC]
      exact map_mono hBC
    have hE'card : Nat.card E' = Nat.card h.B := GSLit.card_conjugate h.B g
    have hNE' : conjugate (S' ⊓ normalizer (h.B : Set X)) g =
        h.S ⊓ normalizer (E' : Set X) := by
      rw [hconjInf, hconjS', hconjN]
    have hlt' : Nat.card ↥(h.S ⊓ normalizer (h.B : Set X)) <
        Nat.card ↥(h.S ⊓ normalizer (E' : Set X)) := by
      rw [← hNE', GSLit.card_conjugate]
      exact hlt
    obtain ⟨L, hL⟩ := h.isoCorr_of_lt E' (le_inf hE'S hE'C) (Or.inr ⟨hE'card, hlt'⟩)
    have hL' := Six.isoCorrSub_conjugate hca hcJ hL
    rw [hE', conjugate_conjugate, mul_inv_cancel, conjugate_one] at hL'
    exact h.not_isoCorrSub_B _ hL'
  have hQN : h.Q ≤ U ⊓ normalizer (h.B : Set X) := le_inf hQU inf_le_right
  have heq : h.Q = S' ⊓ normalizer (h.B : Set X) :=
    eq_of_le_of_card_ge (hQN.trans (inf_le_inf_right _ hUS')) hcard
  exact le_antisymm ((inf_le_inf_right _ hUS').trans heq.ge) hQN

namespace SecCond

theorem inf_normalizer_subB_eq (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hW : h.NoFusionW) {S' : Subgroup ↥(h.secSubImg y)} (hS'2 : IsPGroup 2 S')
    (hS'a : S' ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y))) (hSS' : h.subS y ≤ S') :
    S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (h.secImage y h.Q).subgroupOf (h.secSubImg y) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) with hN
  set Q' := (h.secImage y h.Q).subgroupOf (h.secSubImg y) with hQ'
  have hQ'eq : h.subS y ⊓ N = Q' := hc.subS_inf_normalizer
  have hQ'le : Q' ≤ S' ⊓ N := hQ'eq ▸ inf_le_inf_right _ hSS'
  have hQH : h.secImage y h.Q ≤ h.secSubImg y :=
    (secImage_mono (inf_le_left : h.Q ≤ h.S)).trans (h.secImage_S_le y)
  have haG := hc.a_mem_G0
  set R := h.secPre y (S'.map (h.secSubImg y).subtype) with hR
  have hR2 : IsPGroup 2 R := isPGroup_secPre (hS'2.map _)
  have hmemR : ∀ (g : ↥(h.secG0 y)) (s : ↥(h.secSubImg y)), s ∈ S' →
      (s : h.secBar y) = h.secMk y g → (g : X) ∈ R := fun g s hs hsg => ⟨g, ⟨s, hs, hsg⟩, rfl⟩
  have hQR : h.Q ≤ R := by
    intro q hq
    have hqG : q ∈ h.secG0 y := hc.Q_le hq
    have h1 : h.secMk y ⟨q, hqG⟩ ∈ h.secImage y h.Q :=
      mem_map_of_mem _ (show (⟨q, hqG⟩ : ↥(h.secG0 y)) ∈ h.Q.subgroupOf (h.secG0 y) from hq)
    exact hmemR ⟨q, hqG⟩ ⟨_, hQH h1⟩
      (mem_inf.mp (hQ'le (show (⟨_, hQH h1⟩ : ↥(h.secSubImg y)) ∈ Q' from h1))).1 rfl
  have haS : hc.subA ∈ h.subS y :=
    mem_map_of_mem _ (show (⟨h.a, haG⟩ : ↥(h.secG0 y)) ∈ h.S.subgroupOf (h.secG0 y) from
      B5a.a_mem_S h)
  have haR : h.a ∈ R := hmemR ⟨h.a, haG⟩ hc.subA (hSS' haS) rfl
  refine le_antisymm ?_ hQ'le
  by_contra hne
  set D := S' ⊓ N with hD
  have hD2 : IsPGroup 2 D := hS'2.to_le inf_le_left
  have hlt : Q'.subgroupOf D < ⊤ := by
    refine lt_of_le_of_ne le_top fun he => hne ?_
    intro w hw
    have : (⟨w, hw⟩ : ↥D) ∈ Q'.subgroupOf D := he ▸ mem_top _
    exact this
  have hnil : Group.IsNilpotent ↥D := hD2.isNilpotent
  obtain ⟨w, hwN, hwQ⟩ := Set.exists_of_ssubset (Group.normalizerCondition_of_isNilpotent _ hlt)
  set w₁ : ↥(h.secSubImg y) := (w : ↥(h.secSubImg y)) with hw₁
  have hw₁S : w₁ ∈ S' := (mem_inf.mp w.2).1
  have hw₁N : w₁ ∈ N := (mem_inf.mp w.2).2
  have hw₁Q : w₁ ∉ Q' := fun h0 => hwQ h0
  have hw₁NQ : w₁ ∈ normalizer (Q' : Set ↥(h.secSubImg y)) :=
    (B5a.mem_normalizer_subgroupOf_iff hQ'le).mp hwN
  obtain ⟨g₀, -, hg₀w⟩ := mem_map.mp w₁.2
  have hgB : (g₀ : X) ∈ normalizer (h.B : Set X) := by
    have h1 : (w₁ : h.secBar y) ∈ normalizer (h.secImage y h.B : Set (h.secBar y)) := by
      have h2 := hw₁N
      rw [hN, normalizer_subB, mem_subgroupOf] at h2
      exact h2
    rw [hc.normalizer_secB, ← hg₀w,
      secMk_mem_secImage_iff ((h.secB0_le_B y).trans le_normalizer)] at h1
    exact h1
  have hgQ : (g₀ : X) ∈ normalizer (h.Q : Set X) := by
    have h1 : (w₁ : h.secBar y) ∈ normalizer (h.secImage y h.Q : Set (h.secBar y)) := by
      have h2 := hw₁NQ
      rw [hQ', ← subgroupOf_normalizer_eq hQH, mem_subgroupOf] at h2
      exact h2
    rw [← hg₀w] at h1
    exact OS1.mem_normalizer_of_secMk ((h.secB0_le_B y).trans h.B_le_Q) hc.Q_le h1
  have hcomm : w₁ * hc.subA = hc.subA * w₁ := mem_centralizer_singleton_iff.mp (hS'a hw₁S)
  have hβ : (g₀ : X) * h.a * (g₀ : X)⁻¹ * h.a⁻¹ ∈ h.secB0 y := by
    have h1 : h.secMk y (g₀ * ⟨h.a, haG⟩ * g₀⁻¹ * (⟨h.a, haG⟩ : ↥(h.secG0 y))⁻¹) = 1 := by
      have h2 : (w₁ : h.secBar y) * hc.secA = hc.secA * (w₁ : h.secBar y) :=
        congrArg Subtype.val hcomm
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg₀w]
      rw [show h.secMk y ⟨h.a, haG⟩ = hc.secA from rfl, h2]
      group
    have h3 : g₀ * ⟨h.a, haG⟩ * g₀⁻¹ * (⟨h.a, haG⟩ : ↥(h.secG0 y))⁻¹ ∈ h.secB0' y := by
      rw [← ker_secMk]
      exact h1
    exact h3
  have hgR : (g₀ : X) ∈ R := hmemR g₀ w₁ hw₁S hg₀w.symm
  have hga : (g₀ : X) * h.a = h.a * g₀ :=
    hW g₀ hgB hgQ R hR2 hgR haR _ ((h.secB0_le_B y) hβ) (by group)
  have hU : (R ⊓ centralizer ({h.a} : Set X)) ⊓ normalizer (h.B : Set X) = h.Q :=
    inf_normalizer_B_eq_Q hCN hSa (hR2.to_le inf_le_left) inf_le_right
      (le_inf hQR (inf_le_left.trans (h.S_le.trans inf_le_left)))
  have hgQ' : (g₀ : X) ∈ h.Q := by
    rw [← hU]
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hgR, mem_centralizer_singleton_iff.mpr hga⟩, hgB⟩
  apply hw₁Q
  show (w₁ : h.secBar y) ∈ h.secImage y h.Q
  rw [← hg₀w]
  exact mem_map_of_mem _ (show g₀ ∈ h.Q.subgroupOf (h.secG0 y) from hgQ')

theorem isoCorr_subStar (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hW : h.NoFusionW) (hT : h.T = h.B ⊔ zpowers h.a) {S' : Subgroup ↥(h.secSubImg y)}
    (hS'le : S' ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
      normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))
    (hS'2 : IsPGroup 2 S') (hSS' : h.subS y ≤ S') (E : Subgroup ↥(h.secSubImg y))
    (hE : E ≤ S' ⊓ coreActionKernel (h.subJ y))
    (hEc : Nat.card (h.subB y) < Nat.card E ∨ (Nat.card E = Nat.card (h.subB y) ∧
      Nat.card ↥(S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
        Set ↥(h.secSubImg y))) < Nat.card ↥(S' ⊓ normalizer (E : Set ↥(h.secSubImg y))))) :
    ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS'a : S' ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) := hS'le.trans inf_le_left
  have hS'J : S' ≤ normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) :
      Set ↥(h.secSubImg y)) := hS'le.trans inf_le_right
  have hEa : E ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) :=
    (hE.trans inf_le_left).trans hS'a
  have hE2 : IsPGroup 2 E := hS'2.to_le (hE.trans inf_le_left)
  by_cases haE : hc.subA ∈ E
  · have hJc := hc.isPComponent_subJ
    obtain ⟨-, -, hJsub, -, -⟩ := id hJc
    have hJq := ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 (h.subJ y) _
      hc.subJ_le).mp hJc).2.2
    exact ⟨_, Sub58.isoCorrSub_fixedLayer_of_mem hc.subJ_le hJsub hJq hEa
      (hE.trans inf_le_right) hE2 haE⟩
  exfalso
  set P' := S' ⊓ coreActionKernel (h.subJ y) with hP'
  set N := normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) with hN
  have hQ' : S' ⊓ N = (h.secImage y h.Q).subgroupOf (h.secSubImg y) :=
    hc.inf_normalizer_subB_eq hCN hSa hW hS'2 hS'a hSS'
  have hB0B := h.secB0_le_B y
  have hB2 : Nat.card h.B = 2 * Nat.card (h.secB0 y) := by
    have h1 := relIndex_mul_card (H := h.secB0 y) (K := h.B)
    rw [inf_eq_left.mpr hB0B, hc.relIndex_secB0 hT] at h1
    exact h1.symm
  have hB0pos : 0 < Nat.card (h.secB0 y) := Nat.card_pos
  have hcardB : Nat.card (h.subB y) = 2 := by
    rw [show Nat.card (h.subB y) = Nat.card (h.secImage y h.B) from
      Nat.card_congr (subgroupOfEquivOfLe (h.secImage_B_le y)).toEquiv]
    apply Nat.eq_of_mul_eq_mul_right hB0pos
    rw [card_secImage hB0B hc.B_le_G0, hB2]
  have hcT : Nat.card (h.secImage y h.T) = 4 := by
    have h1 := card_secImage (hB0B.trans (B5a.B_le_T h)) hc.T_le_G0
    have h2 := h.card_T (nP_of_T_eq hT)
    apply Nat.eq_of_mul_eq_mul_right hB0pos
    rw [h1, h2, hB2]
    ring
  have hTH : h.secImage y h.T ≤ h.secSubImg y :=
    (secImage_mono (inf_le_left.trans inf_le_left : h.T ≤ h.S)).trans (h.secImage_S_le y)
  have hPN : P' ⊓ N = (h.secImage y h.T).subgroupOf (h.secSubImg y) := by
    rw [hP', inf_right_comm, hQ', coreActionKernel_subJ, ← Sub58.inf_subgroupOf, hc.secImage_T_eq]
  have hcardPN : Nat.card ↥(P' ⊓ N) = 4 := by
    rw [hPN, Six.card_subgroupOf_eq, inf_eq_left.mpr hTH, hcT]
  have hPS : ∀ g : ↥(h.secG0 y), (g : X) ∈ h.P →
      h.secMk y g ∈ h.secImage y h.P := fun g hg =>
    mem_map_of_mem _ (show g ∈ h.P.subgroupOf (h.secG0 y) from hg)
  have hxPS : hc.subX ∈ h.subS y ⊓ coreActionKernel (h.subJ y) := by
    rw [hc.subS_inf_coreActionKernel]
    exact hPS ⟨y, hc.y_mem_G0⟩ hc.mem_P
  have hxP : hc.subX ∈ P' := inf_le_inf_right _ hSS' hxPS
  have hxT : hc.subX ∉ P' ⊓ N := by
    rw [hPN, mem_subgroupOf]
    intro hx
    exact hc.not_mem_T ((secMk_mem_secImage_iff (hB0B.trans (B5a.B_le_T h)) _).mp hx)
  have h8 : 8 ≤ Nat.card P' := by
    have hlt : P' ⊓ N < P' := lt_of_le_of_ne inf_le_left (fun he => hxT (by rw [he]; exact hxP))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := Subgroup.card_dvd_of_le (inf_le_left : P' ⊓ N ≤ P')
    rw [hcardPN] at h1 h2
    obtain ⟨k, hk⟩ := h2
    omega
  have haPS : hc.subA ∈ h.subS y ⊓ coreActionKernel (h.subJ y) := by
    rw [hc.subS_inf_coreActionKernel]
    exact hPS ⟨h.a, hc.a_mem_G0⟩ h.a_mem_P
  have haP : hc.subA ∈ P' := inf_le_inf_right _ hSS' haPS
  have hSN : S' ≤ normalizer (P' : Set ↥(h.secSubImg y)) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf (mem_inf.mpr ⟨le_normalizer hs,
      normalizer_le_normalizer_coreActionKernel _ (hS'J hs)⟩)
  have : Nontrivial ↥(h.subB y) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardB]; norm_num)
  obtain ⟨⟨b, hb⟩, hb1⟩ := exists_ne (1 : ↥(h.subB y))
  have hb1' : b ≠ 1 := fun h0 => hb1 (Subtype.ext h0)
  have hBP : h.subB y ≤ P' := subB_le.trans (inf_le_inf_right _ hSS')
  have haB : hc.subA ∉ h.subB y := by
    intro haB
    have h1 : h.secMk y ⟨h.a, hc.a_mem_G0⟩ ∈ h.secImage y h.B := haB
    exact B5a.a_not_mem_B h ((secMk_mem_secImage_iff hB0B _).mp h1)
  obtain ⟨hle2, heq2⟩ := Sub58.dihedral_step hS'2 inf_le_left hSN haP hc.orderOf_subA
    (fun s hs => mem_centralizer_singleton_iff.mp (hS'a hs)) hcardB hb hb1' hBP haB hcardPN h8
    hE haE
  rcases hEc with hlt | ⟨heq, hlt⟩
  · rw [hcardB] at hlt
    omega
  · rw [heq2 (by rw [heq, hcardB])] at hlt
    exact lt_irrefl _ hlt

end SecCond

end Hyp52

end CFSG.ComponentClassification.GSThmB

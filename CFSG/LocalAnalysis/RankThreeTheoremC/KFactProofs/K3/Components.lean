module

public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Struct
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponentsAux
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2 (Bar barMk)
open CFSG.ABGLocalTools (IsSylowOf)

section Cards

variable {H : Type} [Group H] [Finite H]

theorem cp_three_dvd_quotient_center (K : Type) [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hdvd : 3 ∣ Nat.card K) :
    3 ∣ Nat.card (K ⧸ Subgroup.center K) := by
  obtain ⟨x, hxo, hxc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hK Nat.prime_three (by norm_num) hdvd
  have hdvd1 : orderOf (x : K ⧸ Subgroup.center K) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center K)) x
  rw [hxo] at hdvd1
  have hne : (x : K ⧸ Subgroup.center K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hxc
  have hord : orderOf (x : K ⧸ Subgroup.center K) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    exact hne
  have h3 : orderOf (x : K ⧸ Subgroup.center K) = 3 := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd1 with h | h
    · exact absurd h hord
    · exact h
  have hfin := orderOf_dvd_natCard (x : K ⧸ Subgroup.center K)
  rwa [h3] at hfin

theorem three_dvd_card_component (hH : primeComplementCore (G := H) 3 = ⊥) {L : Subgroup H}
    (hL : IsComponentOf L ⊤) : 3 ∣ Nat.card L := by
  by_contra hnd
  have hcop : Nat.Coprime 3 (Nat.card L) := (Nat.prime_three.coprime_iff_not_dvd).2 hnd
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsub : L.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hL.2.1
  have hle : L ≤ CFSG.pPrimeCore 3 H :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ths_le_pPrimeCore_of_isSubnormal hsub hcop
  have hc : CFSG.pPrimeCore 3 H = ⊥ := hH
  rw [hc] at hle
  have hsimp := hL.2.2.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  have hsub1 : ∀ x y : L, x = y := by
    intro x y
    apply Subtype.ext
    have hx : (x : H) = 1 := Subgroup.mem_bot.1 (hle x.2)
    have hy : (y : H) = 1 := Subgroup.mem_bot.1 (hle y.2)
    rw [hx, hy]
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [hsub1 a' b'] at hab
  exact hab rfl

theorem exists_mem_sylow_component (hH : primeComplementCore (G := H) 3 = ⊥) {L : Subgroup H}
    (hL : IsComponentOf L ⊤) {T : Subgroup H} (hT : IsSylowOf 3 T L) :
    ∃ t ∈ T, orderOf t = 3 ∧ ∃ l ∈ L, l * t ≠ t * l := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 3 ↥L, (Q : Subgroup ↥L).map L.subtype = T := hT
  have hdvd : 3 ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    cp_three_dvd_quotient_center ↥L hL.2.2 (three_dvd_card_component hH hL)
  obtain ⟨t, htQ, hto, htc⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_orderOf_eq_not_mem_center (K := ↥L) Nat.prime_three
      (by norm_num) hL.2.2 hdvd Q
  refine ⟨(t : H), ?_, ?_, ?_⟩
  · rw [← hQ]
    exact Subgroup.mem_map_of_mem L.subtype htQ
  · rw [Subgroup.orderOf_coe, hto]
  · obtain ⟨g, hg⟩ : ∃ g : L, g * t ≠ t * g := by
      by_contra hcon
      push Not at hcon
      exact htc (Subgroup.mem_center_iff.2 fun g => hcon g)
    exact ⟨(g : H), g.2, fun h => hg (Subtype.ext h)⟩

theorem exists_order_three_component (hH : primeComplementCore (G := H) 3 = ⊥) {L : Subgroup H}
    (hL : IsComponentOf L ⊤) : ∃ t ∈ L, orderOf t = 3 ∧ ∃ l ∈ L, l * t ≠ t * l := by
  have hdvd := three_dvd_card_component hH hL
  obtain ⟨x, hxo, hxc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hL.2.2 Nat.prime_three (by norm_num) hdvd
  refine ⟨(x : H), x.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hxo]
  · obtain ⟨g, hg⟩ : ∃ g : L, g * x ≠ x * g := by
      by_contra hcon
      push Not at hcon
      exact hxc (Subgroup.mem_center_iff.2 fun g => hcon g)
    exact ⟨(g : H), g.2, fun h => hg (Subtype.ext h)⟩

end Cards

section Components

variable {H : Type} [Group H] [Finite H]

theorem isComponentOf_map_conj {L : Subgroup H} (hL : IsComponentOf L ⊤) (g : H) :
    IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := by
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨le_top, ?_, ?_⟩
  · have h := CFSG.Open.IsSubnormal.map (MulAut.conj g).toMonoidHom hL.2.1
    rwa [Subgroup.map_top_of_surjective _ hsurj] at h
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (L.equivMapOfInjective (MulAut.conj g).toMonoidHom hinj).symm hL.2.2

theorem component_commute {L₁ L₂ : Subgroup H} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (h12 : L₁ ≠ L₂) {a b : H} (ha : a ∈ L₁) (hb : b ∈ L₂) :
    a * b = b * a := by
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ h12
  have hmem := Subgroup.commutator_mem_commutator ha hb
  rw [hcomm, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

theorem component_inf_le_center {L₁ L₂ : Subgroup H} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (h12 : L₁ ≠ L₂) {a : H} (ha₁ : a ∈ L₁) (ha₂ : a ∈ L₂) :
    ∀ l ∈ L₁, l * a = a * l := by
  intro l hl
  exact component_commute h₁ h₂ h12 hl ha₂

end Components

section Components

variable {H : Type} [Group H] [Finite H]

theorem cl_zpowers_le {S : Set H} {x : H} (hx : x ∈ S) : zpowers x ≤ closure S :=
  Subgroup.zpowers_le.mpr (Subgroup.subset_closure hx)

theorem cl_step {E : Subgroup H} (hE : IsElemAbelian 3 E) {d : H}
    (hdc : E ≤ Subgroup.centralizer ({d} : Set H)) (hd3 : d ^ 3 = 1) (hd : d ∉ E) :
    IsElemAbelian 3 (E ⊔ zpowers d) ∧ Nat.card (E ⊔ zpowers d : Subgroup H) = 3 * Nat.card E := by
  have hd1 : d ≠ 1 := by
    intro h
    apply hd
    rw [h]
    exact E.one_mem
  have hdz : IsElemAbelian 3 (zpowers d) := isElemAbelian_zpowers hd3
  have hcomm : ∀ x ∈ E, x * d = d * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hdc hx)
  have hc : ∀ x ∈ E, ∀ y ∈ zpowers d, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x d from hcomm x hx) k).eq
  have hab : IsElemAbelian 3 (E ⊔ zpowers d) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE hdz hc
  have hcardz : Nat.card (zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hdisj : Disjoint E (zpowers d) := by
    rw [Subgroup.disjoint_def]
    intro x hxE hxd
    by_contra hx1
    have hordx : orderOf x = 3 := orderOf_eq_prime (hE.2 x hxE) hx1
    have hcard : Nat.card (zpowers d) = Nat.card (zpowers x) := by
      rw [hcardz, Nat.card_zpowers, hordx]
    have heq : zpowers x = zpowers d :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxd) hcard.le
    apply hd
    have hdx : d ∈ zpowers x := by
      rw [heq]
      exact Subgroup.mem_zpowers d
    exact (Subgroup.zpowers_le.mpr hxE) hdx
  have hnorm : zpowers d ≤ Subgroup.normalizer (E : Set H) := by
    have hcent : d ∈ Subgroup.centralizer (E : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact Subgroup.mem_centralizer_singleton_iff.mp (hdc hh)
    exact Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer (E : Set H) hcent)
  have hcard : Nat.card (E ⊔ zpowers d : Subgroup H) = Nat.card E * Nat.card (zpowers d) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E (zpowers d) hnorm hdisj
  refine ⟨hab, ?_⟩
  rw [hcard, hcardz, mul_comm]

theorem card_closure_four {a b c d : H} (hab : a * b = b * a) (hac : a * c = c * a)
    (had : a * d = d * a) (hbc : b * c = c * b) (hbd : b * d = d * b) (hcd : c * d = d * c)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hc : c ^ 3 = 1) (hd : d ^ 3 = 1) (ha1 : a ≠ 1)
    (hb1 : b ∉ closure {a}) (hc1 : c ∉ closure {a, b}) (hd1 : d ∉ closure {a, b, c}) :
    IsElemAbelian 3 (closure {a, b, c, d} : Subgroup H) ∧
      Nat.card (closure {a, b, c, d} : Subgroup H) = 81 := by
  have hza : IsElemAbelian 3 (zpowers a) := isElemAbelian_zpowers ha
  have hcza : Nat.card (zpowers a) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ha ha1]
  have cab : zpowers a ≤ Subgroup.centralizer ({b} : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hab)
  have cac : zpowers a ≤ Subgroup.centralizer ({c} : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hac)
  have cbc : zpowers b ≤ Subgroup.centralizer ({c} : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbc)
  have cad : zpowers a ≤ Subgroup.centralizer ({d} : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr had)
  have cbd : zpowers b ≤ Subgroup.centralizer ({d} : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbd)
  have ccd : zpowers c ≤ Subgroup.centralizer ({d} : Set H) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcd)
  have hdc3 : zpowers a ⊔ zpowers b ≤ Subgroup.centralizer ({c} : Set H) := sup_le cac cbc
  have hdc4 : zpowers a ⊔ zpowers b ⊔ zpowers c ≤ Subgroup.centralizer ({d} : Set H) :=
    sup_le (sup_le cad cbd) ccd
  have hb' : b ∉ zpowers a := by
    rw [Subgroup.zpowers_eq_closure]
    exact hb1
  have hsub2 : zpowers a ⊔ zpowers b ≤ closure ({a, b} : Set H) :=
    sup_le (cl_zpowers_le (by simp)) (cl_zpowers_le (by simp))
  have hc' : c ∉ zpowers a ⊔ zpowers b := fun h => hc1 (hsub2 h)
  have hsub3 : zpowers a ⊔ zpowers b ⊔ zpowers c ≤ closure ({a, b, c} : Set H) :=
    sup_le (sup_le (cl_zpowers_le (by simp)) (cl_zpowers_le (by simp)))
      (cl_zpowers_le (by simp))
  have hd' : d ∉ zpowers a ⊔ zpowers b ⊔ zpowers c := fun h => hd1 (hsub3 h)
  have hcl : (closure ({a, b, c, d} : Set H) : Subgroup H) =
      zpowers a ⊔ zpowers b ⊔ zpowers c ⊔ zpowers d := by
    apply le_antisymm
    · rw [Subgroup.closure_le, Set.insert_subset_iff, Set.insert_subset_iff,
        Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left
          (Subgroup.mem_zpowers a))),
        Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right
          (Subgroup.mem_zpowers b))),
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)),
        Subgroup.mem_sup_right (Subgroup.mem_zpowers d)⟩
    · exact sup_le (sup_le (sup_le (cl_zpowers_le (by simp)) (cl_zpowers_le (by simp)))
        (cl_zpowers_le (by simp))) (cl_zpowers_le (by simp))
  obtain ⟨h2a, h2b⟩ := cl_step hza cab hb hb'
  obtain ⟨h3a, h3b⟩ := cl_step h2a hdc3 hc hc'
  obtain ⟨h4a, h4b⟩ := cl_step h3a hdc4 hd hd'
  rw [hcl]
  refine ⟨h4a, ?_⟩
  omega

end Components

section Cards

variable {H : Type} [Group H] [Finite H]

theorem nf_notMem_closure {L : Subgroup H} {S : Set H} {t l : H}
    (hS : ∀ s ∈ S, ∀ x ∈ L, s * x = x * s) (hl : l ∈ L) (hlt : l * t ≠ t * l) :
    t ∉ Subgroup.closure S := by
  intro ht
  have hle : Subgroup.closure S ≤ Subgroup.centralizer (L : Set H) := by
    rw [Subgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hS s hs h hh).symm
  exact hlt (Subgroup.mem_centralizer_iff.mp (hle ht) l hl)

theorem no_four_components (hH : primeComplementCore (G := H) 3 = ⊥)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3) {L₁ L₂ L₃ L₄ : Subgroup H}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (h₃ : IsComponentOf L₃ ⊤)
    (h₄ : IsComponentOf L₄ ⊤) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h14 : L₁ ≠ L₄)
    (h23 : L₂ ≠ L₃) (h24 : L₂ ≠ L₄) (h34 : L₃ ≠ L₄) : False := by
  obtain ⟨t₁, ht₁, hord₁, -⟩ := exists_order_three_component hH h₁
  obtain ⟨t₂, ht₂, hord₂, l₂, hl₂, hlt₂⟩ := exists_order_three_component hH h₂
  obtain ⟨t₃, ht₃, hord₃, l₃, hl₃, hlt₃⟩ := exists_order_three_component hH h₃
  obtain ⟨t₄, ht₄, hord₄, l₄, hl₄, hlt₄⟩ := exists_order_three_component hH h₄
  have hS1 : ∀ s ∈ ({t₁} : Set H), ∀ x ∈ L₂, s * x = x * s := by
    intro s hs x hx
    rw [Set.mem_singleton_iff.mp hs]
    exact component_commute h₁ h₂ h12 ht₁ hx
  have hS2 : ∀ s ∈ ({t₁, t₂} : Set H), ∀ x ∈ L₃, s * x = x * s := by
    intro s hs x hx
    rcases Set.mem_insert_iff.mp hs with h | h
    · rw [h]
      exact component_commute h₁ h₃ h13 ht₁ hx
    · rw [Set.mem_singleton_iff.mp h]
      exact component_commute h₂ h₃ h23 ht₂ hx
  have hS3 : ∀ s ∈ ({t₁, t₂, t₃} : Set H), ∀ x ∈ L₄, s * x = x * s := by
    intro s hs x hx
    rcases Set.mem_insert_iff.mp hs with h | hs
    · rw [h]
      exact component_commute h₁ h₄ h14 ht₁ hx
    rcases Set.mem_insert_iff.mp hs with h | h
    · rw [h]
      exact component_commute h₂ h₄ h24 ht₂ hx
    · rw [Set.mem_singleton_iff.mp h]
      exact component_commute h₃ h₄ h34 ht₃ hx
  have hb1 : t₂ ∉ Subgroup.closure ({t₁} : Set H) := nf_notMem_closure hS1 hl₂ hlt₂
  have hc1 : t₃ ∉ Subgroup.closure ({t₁, t₂} : Set H) := nf_notMem_closure hS2 hl₃ hlt₃
  have hd1 : t₄ ∉ Subgroup.closure ({t₁, t₂, t₃} : Set H) := nf_notMem_closure hS3 hl₄ hlt₄
  have hpow : ∀ t : H, orderOf t = 3 → t ^ 3 = 1 := fun t ht => by
    rw [← ht]
    exact pow_orderOf_eq_one t
  have hne : ∀ t : H, orderOf t = 3 → t ≠ 1 := fun t ht h => by
    rw [h, orderOf_one] at ht
    norm_num at ht
  obtain ⟨hE, hcard⟩ := card_closure_four (component_commute h₁ h₂ h12 ht₁ ht₂)
    (component_commute h₁ h₃ h13 ht₁ ht₃) (component_commute h₁ h₄ h14 ht₁ ht₄)
    (component_commute h₂ h₃ h23 ht₂ ht₃) (component_commute h₂ h₄ h24 ht₂ ht₄)
    (component_commute h₃ h₄ h34 ht₃ ht₄) (hpow _ hord₁) (hpow _ hord₂) (hpow _ hord₃)
    (hpow _ hord₄) (hne _ hord₁) hb1 hc1 hd1
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE (hcard.trans (by norm_num))
  omega

end Cards

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

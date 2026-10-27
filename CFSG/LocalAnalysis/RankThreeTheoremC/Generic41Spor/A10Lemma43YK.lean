module

import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6HJNormalA
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.PCompLift
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43YBasic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

theorem a10_K_false (hWC : KFactWeakClosure) (hI : KFactI1434) (hU : KFactU44Data)
    {K : Type} [Group K] [Finite K] (hK : IsSimpleGroup K) (hnab : ∃ a b : K, a * b ≠ b * a)
    (hcat : IsCatalogGroup K)
    (Q : Sylow 5 K) (hQr : CFSG.Open.pRank 5 (Q : Subgroup K) = 3)
    (hQc : IsMulCommutative (Q : Subgroup K))
    {x t₁ t₂ : K} (hx : x ∈ (Q : Subgroup K)) (hx1 : x ≠ 1) (hx5 : x ^ 5 = 1)
    (ht₁ : t₁ ∈ (Q : Subgroup K)) (ht₂ : t₂ ∈ (Q : Subgroup K)) (ht₁1 : t₁ ≠ 1) (ht₂1 : t₂ ≠ 1)
    (ht₁5 : t₁ ^ 5 = 1) (ht₂5 : t₂ ^ 5 = 1)
    {J₁ J₂ : Subgroup K} (hne : J₁ ≠ J₂)
    (hJ₁ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J₁)
    (hJ₂ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J₂)
    (hlay : GLAPLayer 5 (Subgroup.centralizer ({x} : Set K)) = J₁ ⊔ J₂)
    (hA₁ : Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5)))
    (hA₂ : Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5)))
    (ht₁J : t₁ ∈ J₁) (ht₂J : t₂ ∈ J₂)
    (hd₁ : zpowers x ≠ zpowers t₁) (hd₂ : zpowers x ≠ zpowers t₂) (hd₃ : zpowers t₁ ≠ zpowers t₂)
    (hfus : ∀ g : K, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup K) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers t₁ ∨
        (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers t₂)
    (hswap : (∃ g : K, (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers t₁) ↔
      (∃ g : K, (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers t₂)) : False := by
  classical
  have hord : orderOf x = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hx5 hx1
  have hmap1 : (zpowers x).map (MulAut.conj (1 : K)).toMonoidHom = zpowers x := by
    rw [MonoidHom.map_zpowers]
    simp
  by_cases hA : ∃ g : K, (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers t₁
  ·
    obtain ⟨g₁, hg₁⟩ := hA
    obtain ⟨g₂, hg₂⟩ := hswap.mp ⟨g₁, hg₁⟩
    have hD : {A : Subgroup K | ∃ g : K, A = (zpowers x).map (MulAut.conj g).toMonoidHom ∧
        A ≤ (Q : Subgroup K)} = {zpowers x, zpowers t₁, zpowers t₂} := by
      ext B
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨g, rfl, hle⟩
        exact hfus g hle
      · rintro (rfl | rfl | rfl)
        · exact ⟨1, hmap1.symm, zpowers_le.mpr hx⟩
        · exact ⟨g₁, hg₁.symm, zpowers_le.mpr ht₁⟩
        · exact ⟨g₂, hg₂.symm, zpowers_le.mpr ht₂⟩
    have hncard : Set.ncard {A : Subgroup K | ∃ g : K,
        A = (zpowers x).map (MulAut.conj g).toMonoidHom ∧ A ≤ (Q : Subgroup K)} = 3 := by
      rw [hD]
      exact Set.ncard_eq_three.mpr ⟨_, _, _, hd₁, hd₂, hd₃, rfl⟩
    obtain ⟨hiso⟩ := hI K hK hnab hcat Q hQr hQc x hx hx1 hx5 J₁ J₂ hne hJ₁ hJ₂ hlay hA₁ hA₂
      (Or.inr hncard)
    obtain ⟨-, hU2⟩ := hU K ⟨hiso⟩ Q x hx hx1 hx5 J₁ J₂ hne hJ₁ hJ₂ hlay hA₁ hA₂
    refine hU2 J₁ (Or.inl rfl) t₁ (Subgroup.mem_inf.mpr ⟨ht₁, ht₁J⟩) ht₁1 (MulAut.conj g₁) ?_
    rw [← hg₁]
    exact Subgroup.mem_map_of_mem _ (mem_zpowers x)
  ·
    have hB₂ : ¬ ∃ g : K, (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers t₂ :=
      fun h => hA (hswap.mpr h)
    haveI : IsSimpleGroup K := hK
    have hsimple : IsSimpleGroup ↥(⊤ : Subgroup K) := Subgroup.topEquiv.isSimpleGroup_congr.mpr hK
    have hnabT : ∃ a b : ↥(⊤ : Subgroup K), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hnab
      exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
    have hcatT : IsCatalogGroup ↥(⊤ : Subgroup K) :=
      IsCatalogGroup.of_mulEquiv (Subgroup.topEquiv : ↥(⊤ : Subgroup K) ≃* K) hcat
    have hcent : Subgroup.centralizer ((⊤ : Subgroup K) : Set K) = ⊥ := by
      rw [Subgroup.coe_top, Subgroup.centralizer_univ]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        have ha : a ∈ Subgroup.center K := by rw [h]; trivial
        exact hab (Subgroup.mem_center_iff.mp ha b).symm
    have hdvd : 5 ∣ Nat.card ↥(⊤ : Subgroup K) := by
      rw [Subgroup.card_top]
      have := orderOf_dvd_natCard x
      rwa [hord] at this
    have hrkQ : 2 ≤ CFSG.Open.pRank 5 ((Q : Subgroup K) ⊓ (⊤ : Subgroup K)) := by
      rw [inf_top_eq, hQr]
      norm_num
    obtain ⟨g, hgle, hgne⟩ := hWC 5 Nat.prime_five (by norm_num) K (⊤ : Subgroup K) inferInstance
      hsimple hnabT hcatT hcent hdvd Q (top_sup_eq _) hQc hrkQ (zpowers x) (zpowers_le.mpr hx)
      (by rw [Nat.card_zpowers, hord])
    rcases hfus g hgle with h | h | h
    · exact hgne h
    · exact hA ⟨g, h⟩
    · exact hB₂ ⟨g, h⟩

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x t₁ t₂ : Y} {J₁ J₂ F : Subgroup Y}

theorem a10yK_mem_of_map_eq {G : Type*} [Group G] {A : Subgroup G} {Q : Subgroup ↥A} {R : Subgroup G}
    (hQR : Q.map A.subtype = R) {z : ↥A} (hz : (z : G) ∈ R) : z ∈ Q := by
  rw [← hQR] at hz
  obtain ⟨q, hq, hqz⟩ := Subgroup.mem_map.1 hz
  have hqz' : q = z := Subtype.ext hqz
  exact hqz' ▸ hq

theorem a10yK_ne_one_pow {G : Type*} [Group G] {A : Subgroup G} {z : ↥A} {y : G}
    (hz : (z : G) = y) (ho : orderOf y = 5) : z ≠ 1 ∧ z ^ 5 = 1 := by
  refine ⟨?_, ?_⟩
  · intro h1
    have hy : y = 1 := by rw [← hz, h1]; rfl
    rw [hy, orderOf_one] at ho
    omega
  · apply Subtype.ext
    have h5 : y ^ 5 = 1 := ho ▸ pow_orderOf_eq_one y
    simpa [hz] using h5

theorem a10y_sub_basic (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {A : Subgroup Y}
    (Q : Sylow 5 ↥A) (hQP : (Q : Subgroup ↥A).map A.subtype = P)
    (x' t₁' t₂' : ↥A) (hx' : (x' : Y) = x) (ht₁' : (t₁' : Y) = t₁) (ht₂' : (t₂' : Y) = t₂) :
    CFSG.Open.pRank 5 (Q : Subgroup ↥A) = 3 ∧ IsMulCommutative (Q : Subgroup ↥A) ∧
    x' ∈ (Q : Subgroup ↥A) ∧ t₁' ∈ (Q : Subgroup ↥A) ∧ t₂' ∈ (Q : Subgroup ↥A) ∧
    x' ≠ 1 ∧ x' ^ 5 = 1 ∧ t₁' ≠ 1 ∧ t₂' ≠ 1 ∧ t₁' ^ 5 = 1 ∧ t₂' ^ 5 = 1 := by
  have h5 : (1 : ℕ) < 5 := by norm_num
  have hPA : P ≤ A := by
    rw [← hQP]
    exact Subgroup.map_subtype_le _
  have hle : CFSG.Open.pRank 5 (Q : Subgroup ↥A) ≤ 3 := by
    calc CFSG.Open.pRank 5 (Q : Subgroup ↥A)
        ≤ CFSG.Open.pRank 5 ((Q : Subgroup ↥A).map A.subtype) :=
          CFSG.SectionRank.pRank_le_map h5 A.subtype A.subtype_injective _
      _ = CFSG.Open.pRank 5 P := by rw [hQP]
      _ ≤ CFSG.Open.pRank 5 (⊤ : Subgroup Y) := CFSG.SectionRank.pRank_mono h5 le_top
      _ ≤ 3 := h.rank
  obtain ⟨hVe, hVc, hVP, -⟩ := a10y_V h
  have hVA : zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x ≤ A := hVP.trans hPA
  have hEQ : (zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x).subgroupOf A ≤ (Q : Subgroup ↥A) :=
    fun u hu => a10yK_mem_of_map_eq hQP (hVP hu)
  have hEe : IsElemAbelian 5 ((zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x).subgroupOf A) := by
    haveI := hVe.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun u hu => ?_⟩
    · have key := mul_comm' (⟨(a : Y), a.2⟩ : ↥(zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x))
        ⟨(b : Y), b.2⟩
      have key' := congrArg Subtype.val key
      exact Subtype.ext (Subtype.ext key')
    · apply Subtype.ext
      have := hVe.2 (u : Y) hu
      simpa using this
  have hEcard : Nat.card ↥((zpowers t₁ ⊔ zpowers t₂ ⊔ zpowers x).subgroupOf A) = 5 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVA).toEquiv]
    exact hVc
  have hge : 3 ≤ CFSG.Open.pRank 5 (Q : Subgroup ↥A) :=
    CFSG.SectionRank.le_pRank h5 hEQ hEe hEcard
  have hQc : IsMulCommutative (Q : Subgroup ↥A) := by
    haveI := h.P_comm
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : ((a : ↥A) : Y) ∈ P := hQP ▸ Subgroup.mem_map_of_mem A.subtype a.2
    have hb : ((b : ↥A) : Y) ∈ P := hQP ▸ Subgroup.mem_map_of_mem A.subtype b.2
    have key := mul_comm' (⟨((a : ↥A) : Y), ha⟩ : ↥P) ⟨((b : ↥A) : Y), hb⟩
    have key' := congrArg Subtype.val key
    exact Subtype.ext (Subtype.ext key')
  obtain ⟨hx1, hx5⟩ := a10yK_ne_one_pow hx' h.x_ord
  obtain ⟨ht₁1, ht₁5⟩ := a10yK_ne_one_pow ht₁' h.t₁_ord
  obtain ⟨ht₂1, ht₂5⟩ := a10yK_ne_one_pow ht₂' h.t₂_ord
  exact ⟨le_antisymm hle hge, hQc,
    a10yK_mem_of_map_eq hQP (hx' ▸ h.x_mem), a10yK_mem_of_map_eq hQP (ht₁' ▸ h.t₁_mem.1),
    a10yK_mem_of_map_eq hQP (ht₂' ▸ h.t₂_mem.1), hx1, hx5, ht₁1, ht₂1, ht₁5, ht₂5⟩

theorem a10y_comp_sub (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {A : Subgroup Y} (hA : IsComponentOf A ⊤)
    (x' : ↥A) (hx' : (x' : Y) = x) (hJ₁A : J₁ ≤ A) (hJ₂A : J₂ ≤ A) :
    GLAPComponent 5 (Subgroup.centralizer ({x'} : Set ↥A)) (J₁.subgroupOf A) ∧
    GLAPComponent 5 (Subgroup.centralizer ({x'} : Set ↥A)) (J₂.subgroupOf A) ∧
    J₁.subgroupOf A ≠ J₂.subgroupOf A ∧
    GLAPLayer 5 (Subgroup.centralizer ({x'} : Set ↥A)) = J₁.subgroupOf A ⊔ J₂.subgroupOf A := by
  have hp : Nat.Prime 5 := by norm_num
  have hcent : (A ⊓ Subgroup.centralizer ({x} : Set Y)).subgroupOf A =
      Subgroup.centralizer ({x'} : Set ↥A) := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff, ← hx', Subtype.ext_iff]
    simp
  have hJ₁C : J₁ ≤ Subgroup.centralizer ({x} : Set Y) := h.comp₁.1
  have hJ₂C : J₂ ≤ Subgroup.centralizer ({x} : Set Y) := h.comp₂.1
  have hc₁ : GLAPComponent 5 (A ⊓ Subgroup.centralizer ({x} : Set Y)) J₁ :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le hp h.comp₁ (le_inf hJ₁A hJ₁C) inf_le_right
  have hc₂ : GLAPComponent 5 (A ⊓ Subgroup.centralizer ({x} : Set Y)) J₂ :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le hp h.comp₂ (le_inf hJ₂A hJ₂C) inf_le_right
  have hs₁ : GLAPComponent 5 (Subgroup.centralizer ({x'} : Set ↥A)) (J₁.subgroupOf A) := by
    rw [← hcent]
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp inf_le_left hc₁
  have hs₂ : GLAPComponent 5 (Subgroup.centralizer ({x'} : Set ↥A)) (J₂.subgroupOf A) := by
    rw [← hcent]
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_subgroupOf hp inf_le_left hc₂
  have hne : J₁.subgroupOf A ≠ J₂.subgroupOf A := by
    intro heq
    apply h.ne
    have := congrArg (Subgroup.map A.subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hJ₁A, Subgroup.map_subgroupOf_eq_of_le hJ₂A] at this
  refine ⟨hs₁, hs₂, hne, le_antisymm ?_ (sup_le (le_sSup hs₁) (le_sSup hs₂))⟩
  refine sSup_le fun L' hL' => ?_
  have hker : Nat.Coprime 5
      (Nat.card ↥(Subgroup.centralizer ({x'} : Set ↥A) ⊓ A.subtype.ker)) := by
    rw [Subgroup.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 5
  have himg := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp A.subtype hker hL'
  have hmapcent : (Subgroup.centralizer ({x'} : Set ↥A)).map A.subtype =
      A ⊓ Subgroup.centralizer ({x} : Set Y) := by
    rw [← hcent]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
  rw [hmapcent] at himg
  have hsn : IsSubnormal (A ⊓ Subgroup.centralizer ({x} : Set Y))
      (Subgroup.centralizer ({x} : Set Y)) := by
    have := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_inf hA.2.1
      (Subgroup.centralizer ({x} : Set Y))
    rwa [top_inf_eq] at this
  have hC' : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) (L'.map A.subtype) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.glaPComponent_of_subnormal hp hsn himg
  have hle : L'.map A.subtype ≤ J₁ ⊔ J₂ := by
    rw [← h.layer]
    exact le_sSup hC'
  have hle' : L' ≤ (J₁ ⊔ J₂).subgroupOf A := fun g hg =>
    Subgroup.mem_subgroupOf.2 (hle ⟨g, hg, rfl⟩)
  rwa [Subgroup.subgroupOf_sup hJ₁A hJ₂A] at hle'

theorem a10yK_map_conj_zpowers {G : Type*} [Group G] (a g : G) :
    (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers (g * a * g⁻¹) := by
  rw [MonoidHom.map_zpowers]
  rfl

theorem a10yK_zpowers_coe_inj {G : Type*} [Group G] (A : Subgroup G) (u v : ↥A) :
    zpowers u = zpowers v ↔ zpowers (u : G) = zpowers (v : G) := by
  constructor
  · intro huv
    have := congrArg (Subgroup.map A.subtype) huv
    simpa [MonoidHom.map_zpowers] using this
  · intro huv
    apply Subgroup.map_injective A.subtype_injective
    simpa [MonoidHom.map_zpowers] using huv

theorem a10yK_conj_zpowers_iff {G : Type*} [Group G] (A : Subgroup G) (g a u : ↥A) :
    (zpowers a).map (MulAut.conj g).toMonoidHom = zpowers u ↔
      zpowers ((g : G) * (a : G) * (g : G)⁻¹) = zpowers (u : G) := by
  rw [a10yK_map_conj_zpowers, a10yK_zpowers_coe_inj]
  rfl

theorem a10yK_swap_aux {G : Type*} [Group G] {A : Subgroup G} {f : G}
    (hfA : f ∈ Subgroup.normalizer (A : Set G)) {x t t' : G} (hfx : f * x * f⁻¹ = x)
    (hft : zpowers (f * t * f⁻¹) = zpowers t')
    (hg : ∃ g : ↥A, zpowers ((g : G) * x * (g : G)⁻¹) = zpowers t) :
    ∃ g : ↥A, zpowers ((g : G) * x * (g : G)⁻¹) = zpowers t' := by
  obtain ⟨g, hg⟩ := hg
  have hfx' : f⁻¹ * x * f = x := by
    calc f⁻¹ * x * f = f⁻¹ * (f * x * f⁻¹) * f := by rw [hfx]
      _ = x := by group
  have hmem : f * (g : G) * f⁻¹ ∈ A :=
    ((Subgroup.mem_set_normalizer_iff.1 hfA) (g : G)).1 g.2
  refine ⟨⟨f * (g : G) * f⁻¹, hmem⟩, ?_⟩
  have e : (f * (g : G) * f⁻¹) * x * (f * (g : G) * f⁻¹)⁻¹ =
      f * ((g : G) * x * (g : G)⁻¹) * f⁻¹ := by
    calc (f * (g : G) * f⁻¹) * x * (f * (g : G) * f⁻¹)⁻¹
        = f * (g : G) * (f⁻¹ * x * f) * (g : G)⁻¹ * f⁻¹ := by group
      _ = f * (g : G) * x * (g : G)⁻¹ * f⁻¹ := by rw [hfx']
      _ = f * ((g : G) * x * (g : G)⁻¹) * f⁻¹ := by group
  show zpowers ((f * (g : G) * f⁻¹) * x * (f * (g : G) * f⁻¹)⁻¹) = zpowers t'
  rw [e, ← a10yK_map_conj_zpowers, hg, a10yK_map_conj_zpowers, hft]

theorem a10y_fus_sub (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {A : Subgroup Y}
    (hFA : ∀ f ∈ F, f ∈ Subgroup.normalizer (A : Set Y))
    (Q : Sylow 5 ↥A) (hQP : (Q : Subgroup ↥A).map A.subtype = P)
    (x' t₁' t₂' : ↥A) (hx' : (x' : Y) = x) (ht₁' : (t₁' : Y) = t₁) (ht₂' : (t₂' : Y) = t₂) :
    (∀ g : ↥A, (zpowers x').map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup ↥A) →
      (zpowers x').map (MulAut.conj g).toMonoidHom = zpowers x' ∨
        (zpowers x').map (MulAut.conj g).toMonoidHom = zpowers t₁' ∨
        (zpowers x').map (MulAut.conj g).toMonoidHom = zpowers t₂') ∧
    ((∃ g : ↥A, (zpowers x').map (MulAut.conj g).toMonoidHom = zpowers t₁') ↔
      (∃ g : ↥A, (zpowers x').map (MulAut.conj g).toMonoidHom = zpowers t₂')) ∧
    zpowers x' ≠ zpowers t₁' ∧ zpowers x' ≠ zpowers t₂' ∧ zpowers t₁' ≠ zpowers t₂' := by
  subst hx' ht₁' ht₂'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    have hP : (zpowers (x' : Y)).map (MulAut.conj (g : Y)).toMonoidHom ≤ P := by
      rw [a10yK_map_conj_zpowers]
      have hmap := Subgroup.map_mono (f := A.subtype) hg
      rw [hQP, a10yK_map_conj_zpowers, MonoidHom.map_zpowers] at hmap
      exact hmap
    rcases h.fusion (g : Y) hP with e | e | e
    · rw [a10yK_map_conj_zpowers] at e
      exact Or.inl ((a10yK_conj_zpowers_iff A g x' x').2 e)
    · rw [a10yK_map_conj_zpowers] at e
      exact Or.inr (Or.inl ((a10yK_conj_zpowers_iff A g x' t₁').2 e))
    · rw [a10yK_map_conj_zpowers] at e
      exact Or.inr (Or.inr ((a10yK_conj_zpowers_iff A g x' t₂').2 e))
  ·
    obtain ⟨f, hf, -, hft⟩ := h.F_swap
    have hfx : f * (x' : Y) * f⁻¹ = (x' : Y) := by
      have hc := Subgroup.mem_centralizer_iff.1 (h.F_le hf) (x' : Y) (Set.mem_singleton _)
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.symm
    have hfx2 : f⁻¹ * (x' : Y) * f⁻¹⁻¹ = (x' : Y) := by
      have hc := Subgroup.mem_centralizer_iff.1 (h.F_le (inv_mem hf)) (x' : Y) (Set.mem_singleton _)
      rw [mul_inv_eq_iff_eq_mul]
      exact hc.symm
    rw [a10yK_map_conj_zpowers] at hft
    have hft2 : zpowers (f⁻¹ * (t₂' : Y) * f⁻¹⁻¹) = zpowers (t₁' : Y) := by
      calc zpowers (f⁻¹ * (t₂' : Y) * f⁻¹⁻¹)
          = (zpowers (t₂' : Y)).map (MulAut.conj f⁻¹).toMonoidHom :=
            (a10yK_map_conj_zpowers _ _).symm
        _ = (zpowers (f * (t₁' : Y) * f⁻¹)).map (MulAut.conj f⁻¹).toMonoidHom := by rw [hft]
        _ = zpowers (f⁻¹ * (f * (t₁' : Y) * f⁻¹) * f⁻¹⁻¹) := a10yK_map_conj_zpowers _ _
        _ = zpowers (t₁' : Y) := by congr 1; group
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨g', hg'⟩ := a10yK_swap_aux (hFA f hf) hfx hft
        ⟨g, (a10yK_conj_zpowers_iff A g x' t₁').1 hg⟩
      exact ⟨g', (a10yK_conj_zpowers_iff A g' x' t₂').2 hg'⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g', hg'⟩ := a10yK_swap_aux (hFA f⁻¹ (inv_mem hf)) hfx2 hft2
        ⟨g, (a10yK_conj_zpowers_iff A g x' t₂').1 hg⟩
      exact ⟨g', (a10yK_conj_zpowers_iff A g' x' t₁').2 hg'⟩
  ·
    intro heq
    rw [a10yK_zpowers_coe_inj] at heq
    have hx : (x' : Y) ∈ zpowers (t₁' : Y) := by
      rw [← heq]
      exact Subgroup.mem_zpowers _
    exact h.x_not_mem (Subgroup.mem_sup_left hx)
  ·
    intro heq
    rw [a10yK_zpowers_coe_inj] at heq
    have hx : (x' : Y) ∈ zpowers (t₂' : Y) := by
      rw [← heq]
      exact Subgroup.mem_zpowers _
    exact h.x_not_mem (Subgroup.mem_sup_right hx)
  ·
    intro heq
    rw [a10yK_zpowers_coe_inj] at heq
    have ht : (t₁' : Y) ∈ zpowers (t₂' : Y) := by
      rw [← heq]
      exact Subgroup.mem_zpowers _
    exact h.t₁_not_mem ht

theorem a10y_pQuot_equiv_subgroupOf {A J : Subgroup Y} (hJA : J ≤ A) :
    Nonempty (↥(J.subgroupOf A) ⧸ primeComplementCore (G := ↥(J.subgroupOf A)) 5 ≃*
      ↥J ⧸ primeComplementCore (G := ↥J) 5) :=
  ⟨QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJA)
    (CFSG.pPrimeCore_map_iso 5 (Subgroup.subgroupOfEquivOfLe hJA))⟩

theorem a10y_A5_quot_sub (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {A : Subgroup Y} (hJ₁A : J₁ ≤ A)
    (hJ₂A : J₂ ≤ A) :
    Nonempty (↥(J₁.subgroupOf A) ⧸ primeComplementCore (G := ↥(J₁.subgroupOf A)) 5 ≃*
      alternatingGroup (Fin 5)) ∧
    Nonempty (↥(J₂.subgroupOf A) ⧸ primeComplementCore (G := ↥(J₂.subgroupOf A)) 5 ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨e₁⟩ := a10y_pQuot_equiv_subgroupOf hJ₁A
  obtain ⟨e₂⟩ := a10y_pQuot_equiv_subgroupOf hJ₂A
  exact ⟨⟨e₁.trans h.A5₁.some⟩, ⟨e₂.trans h.A5₂.some⟩⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

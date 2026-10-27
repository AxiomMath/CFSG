module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexDefs
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexOrbit
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoHexRank
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVNormalThreeDiag
import CFSG.LocalAnalysis.AGLEmbedding.SurvivorBarM

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}

theorem D1PhaseThree.false_of_threeASix_mem (h : D1PhaseThree 3 P M H R)
    (hThree : KFactBlockThreeASix)
    (hcyc : ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), V ≤ barM M (H ⊓ M) → ⁅V, V⁆ = V →
      ∀ Q : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), Q ≤ V → IsPGroup 3 Q → IsCyclic Q)
    {z : G} (hzM : z ∈ M) (hz3 : z ^ 3 = 1) (hCz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hin : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈
        barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hrk : ∀ E : Subgroup G, E ≤ Subgroup.centralizer ({z} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 3)
    (hP4 : 4 ≤ Open.pRank 3 (P : Subgroup G))
    {L : Subgroup G} (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    (hZ : Nat.card (Subgroup.center ↥(barM M L)) = 3)
    (hA6 : Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 6)))
    (hzL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨z, hzM⟩ ∈ barM M L) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  set S := pCoreOf 2 H with hS
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set zb := mk ⟨z, hzM⟩ with hzb
  have hz : IsPGroup 3 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (k := 1) (by simpa using hz3)
  have hzb3 : zb ^ 3 = 1 := by
    have h1 : (⟨z, hzM⟩ : M) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [hzb, ← map_pow, h1, map_one]
  set A₀ := barM M L with hA₀
  set Cn := Subgroup.centralizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCn
  have hnC : zb ∉ Cn := h.not_mem_centralizer_block hp hp2 hzM hz hCz hL
  obtain ⟨ha, hb, hc⟩ := hThree G M L hL.toIsTwoPrimeComponent hZ hA6
  obtain ⟨ζ, hζA, hζC, hζ1, hζ3⟩ := exists_center_of_card hZ
  have hZ3 : ∀ x ∈ A₀, x ∈ Cn → x ^ 3 = 1 := by
    intro x hxA hxC
    have hxZ : (⟨x, hxA⟩ : A₀) ∈ Subgroup.center A₀ := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    have h1 := pow_card_eq_one' (G := Subgroup.center A₀) (x := ⟨⟨x, hxA⟩, hxZ⟩)
    rw [hZ] at h1
    simpa using congrArg (fun y : Subgroup.center A₀ => ((y : A₀) : ↥M ⧸ CFSG.pCore 2 ↥M)) h1
  have hPN : ∀ g ∈ (P : Subgroup G), ∀ hgM : g ∈ M,
      mk ⟨g, hgM⟩ ∈ Subgroup.normalizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    intro g hgP hgM
    have hg3 : IsPGroup 3 (Subgroup.zpowers g) :=
      P.isPGroup'.to_le ((Subgroup.zpowers_le).mpr hgP)
    exact mem_normalizer_barM hgM (D1PhaseThree.mem_normalizer_of_threeASix h hThree hcyc hzM
      hz3 hCz hin hrk hL hZ hA6 hgM hg3)
  obtain ⟨E, hEP, hEe, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3)
    (P : Subgroup G)
  have hEM : E ≤ M := hEP.trans h.toD1Escape.sylow_le
  have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEe.2 x x.2)⟩
  set Eb := barM M E with hEb
  have hEbc : Nat.card Eb = Nat.card E := card_barM_of_isPGroup hp hp2 hEM hE3
  have hEbe : IsElemAbelian 3 Eb := isElemAbelian_barM hEe
  have h81 : 3 ^ 4 ≤ Nat.card Eb := by
    rw [hEbc, hEc]
    exact Nat.pow_le_pow_right (by norm_num) hP4
  have hEbN : Eb ≤ Subgroup.normalizer (A₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rintro _ ⟨⟨g, hgM⟩, hg, rfl⟩
    exact hPN g (hEP (Subgroup.mem_subgroupOf.mp hg)) hgM
  have hEbin : ∀ x ∈ Eb, x ∈ A₀ ⊔ Cn := fun x hx =>
    ha x (hEbN hx) ⟨1, by rw [pow_one]; exact hEbe.2 x hx⟩
  have hEbNC : Eb ≤ Subgroup.normalizer (Cn : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun x hx =>
    mem_normalizer_centralizer (hEbN hx)
  have hANC : A₀ ≤ Subgroup.normalizer (Cn : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun x hx =>
    mem_normalizer_centralizer (Subgroup.le_normalizer hx)
  set F := Eb ⊓ Cn with hF
  have hFe : IsElemAbelian 3 F := d1_isElemAbelian_of_le hEbe inf_le_left
  have hFz : F ≤ Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hf.2 zb hzL).symm
  obtain ⟨hX₁c, hX₁e⟩ := card_sup_zpowers_elem (inf_le_right : F ≤ Cn) hzb3 hnC hFz hFe
  have hX₁z : F ⊔ Subgroup.zpowers zb ≤
      Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le hFz ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  have hF9 : Nat.card F ≤ 3 ^ 2 := by
    have := card_le_of_le_centralizer_barM hzM hz3 hrk hX₁z hX₁e
    rw [hX₁c] at this
    have h3 : Nat.card F * 3 ≤ 3 ^ 3 := this
    omega
  set I := A₀ ⊓ (Eb ⊔ Cn) with hI
  have hdecE : ∀ x ∈ Eb ⊔ Cn, ∃ e ∈ Eb, ∃ k ∈ Cn, x = e * k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hEbNC] at hx
    obtain ⟨e, he, k, hk, rfl⟩ := hx
    exact ⟨e, he, k, hk, rfl⟩
  have hsup : Cn ⊔ Eb = Cn ⊔ I := by
    refine le_antisymm (sup_le le_sup_left fun e he => ?_) (sup_le le_sup_left
      (inf_le_right.trans (sup_le le_sup_right le_sup_left)))
    have he' := hEbin e he
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hANC] at he'
    obtain ⟨l, hl, k, hk, rfl⟩ := he'
    have hlI : l ∈ I := ⟨hl, by
      have : l = (l * k) * k⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hk))⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hlI) (Subgroup.mem_sup_left hk)
  have hc1 := card_sup_mul_card_inf_eq_of_le_normalizer hEbNC
  have hc2 := card_sup_mul_card_inf_eq_of_le_normalizer (inf_le_left.trans hANC :
    I ≤ Subgroup.normalizer (Cn : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
  have hkey : Nat.card Eb * Nat.card (Cn ⊓ I : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) =
      Nat.card I * Nat.card F := by
    rw [hsup] at hc1
    have hpos : 0 < Nat.card Cn := Nat.card_pos
    have e1 : Nat.card (Cn ⊓ Eb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) = Nat.card F := by
      rw [hF, inf_comm]
    rw [e1] at hc1
    have : Nat.card Cn * (Nat.card Eb * Nat.card (Cn ⊓ I : Subgroup _)) =
        Nat.card Cn * (Nat.card I * Nat.card F) := by
      calc Nat.card Cn * (Nat.card Eb * Nat.card (Cn ⊓ I : Subgroup _))
          = (Nat.card Cn * Nat.card Eb) * Nat.card (Cn ⊓ I : Subgroup _) := by ring
        _ = (Nat.card (Cn ⊔ I : Subgroup _) * Nat.card F) * Nat.card (Cn ⊓ I : Subgroup _) := by
            rw [hc1]
        _ = (Nat.card (Cn ⊔ I : Subgroup _) * Nat.card (Cn ⊓ I : Subgroup _)) * Nat.card F := by
            ring
        _ = Nat.card Cn * (Nat.card I * Nat.card F) := by rw [hc2]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hζI : Subgroup.zpowers ζ ≤ Cn ⊓ I := by
    rw [Subgroup.zpowers_le]
    exact ⟨hζC, hζA, Subgroup.mem_sup_right hζC⟩
  have hζo : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
  have hCI3 : 3 ≤ Nat.card (Cn ⊓ I : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have := Subgroup.card_le_of_le hζI
    rwa [Nat.card_zpowers, hζo] at this
  have hdecI : ∀ l ∈ I, ∃ e ∈ Eb, ∃ c ∈ Cn, e = l * c := by
    intro l hl
    obtain ⟨e, he, k, hk, hek⟩ := hdecE l hl.2
    exact ⟨e, he, k⁻¹, Subgroup.inv_mem _ hk, by rw [hek]; group⟩
  have hI3 : IsPGroup 3 I := by
    intro x
    obtain ⟨e, he, c, hc', hec⟩ := hdecI x x.2
    have hlc : Commute (x : ↥M ⧸ CFSG.pCore 2 ↥M) c :=
      (Subgroup.mem_centralizer_iff.mp hc' x x.2.1)
    have h1 : (x : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 * c ^ 3 = 1 := by
      rw [← hlc.mul_pow, ← hec]
      exact hEbe.2 e he
    have h2 : (x : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have h3 : (x : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 3 ∈ Cn := h2 ▸ Subgroup.inv_mem _ (Cn.pow_mem hc' 3)
    have h4 := hZ3 _ (A₀.pow_mem x.2.1 3) h3
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [show 3 ^ 2 = 3 * 3 by norm_num, pow_mul, h4]
  have hI27 : Nat.card I ≤ 3 ^ 3 := (hc I inf_le_left hI3).1
  have h243 : 3 ^ 5 ≤ Nat.card I * Nat.card F := by
    rw [← hkey]
    calc 3 ^ 5 = 3 ^ 4 * 3 := by norm_num
      _ ≤ Nat.card Eb * Nat.card (Cn ⊓ I : Subgroup _) := Nat.mul_le_mul h81 hCI3
  obtain ⟨kI, hkI⟩ := IsPGroup.iff_card.mp hI3
  have hF3 : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hFe.2 x x.2)⟩
  obtain ⟨kF, hkF⟩ := IsPGroup.iff_card.mp hF3
  have hk : 5 ≤ kI + kF := by
    have h1 : 3 ^ 5 ≤ 3 ^ (kI + kF) := by rw [pow_add, ← hkI, ← hkF]; exact h243
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h1
  have hkI3 : kI ≤ 3 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hkI ▸ hI27)
  have hkF2 : kF ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (hkF ▸ hF9)
  have hIc : Nat.card I = 3 ^ 3 := by rw [hkI]; congr 1; omega
  have hFc : Nat.card F = 3 ^ 2 := by rw [hkF]; congr 1; omega
  obtain ⟨l₁, hl₁, l₂, hl₂, hll⟩ : ∃ l₁ ∈ I, ∃ l₂ ∈ I, l₁ * l₂ ≠ l₂ * l₁ := by
    by_contra hcomm
    push Not at hcomm
    have hab : IsMulCommutative I := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    have := (hc I inf_le_left hI3).2 hab
    rw [hIc] at this
    norm_num at this
  obtain ⟨e₁, he₁, c₁, hc₁, he₁l⟩ := hdecI l₁ hl₁
  obtain ⟨e₂, he₂, c₂, hc₂, he₂l⟩ := hdecI l₂ hl₂
  have hcl : ∀ {c l : ↥M ⧸ CFSG.pCore 2 ↥M}, c ∈ Cn → l ∈ A₀ → l * c = c * l := fun hc hl =>
    Subgroup.mem_centralizer_iff.mp hc _ hl
  have hcc : c₁ * c₂ ≠ c₂ * c₁ := by
    intro hc12
    apply hll
    have hee : e₁ * e₂ = e₂ * e₁ := by
      have := hEbe.1.is_comm.comm ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
      exact congrArg Subtype.val this
    rw [he₁l, he₂l] at hee
    have e1 : l₁ * c₁ * (l₂ * c₂) = l₁ * l₂ * (c₁ * c₂) := by
      rw [mul_assoc, ← mul_assoc c₁, ← hcl hc₁ hl₂.1]; group
    have e2 : l₂ * c₂ * (l₁ * c₁) = l₂ * l₁ * (c₂ * c₁) := by
      rw [mul_assoc, ← mul_assoc c₂, ← hcl hc₂ hl₁.1]; group
    rw [e1, e2, hc12] at hee
    exact mul_right_cancel hee
  have hl3 : ∀ {l : ↥M ⧸ CFSG.pCore 2 ↥M}, l ∈ I → l ^ 3 = 1 := by
    intro l hl
    obtain ⟨k, hk⟩ := hI3 ⟨l, hl⟩
    exact hb l hl.1 ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hc3 : ∀ {e l c : ↥M ⧸ CFSG.pCore 2 ↥M}, e ∈ Eb → l ∈ I → c ∈ Cn → e = l * c →
      c ^ 3 = 1 := by
    intro e l c he hl hc' hel
    have h1 : e ^ 3 = 1 := hEbe.2 e he
    have hcomm : Commute l c := hcl hc' hl.1
    rw [hel, hcomm.mul_pow, hl3 hl, one_mul] at h1
    exact h1
  have hc₁3 : c₁ ^ 3 = 1 := hc3 he₁ hl₁ hc₁ he₁l
  have hcF : ∀ {e l c : ↥M ⧸ CFSG.pCore 2 ↥M}, e ∈ Eb → l ∈ I → c ∈ Cn → e = l * c →
      ∀ f ∈ F, f * c = c * f := by
    intro e l c he hl hc' hel f hf
    have hfe : f * e = e * f := by
      have := hEbe.1.is_comm.comm ⟨f, hf.1⟩ ⟨e, he⟩
      exact congrArg Subtype.val this
    have hfl : Commute l f := hcl hf.2 hl.1
    have hc'' : c = l⁻¹ * e := by rw [hel]; group
    rw [hc'']
    calc f * (l⁻¹ * e) = (f * l⁻¹) * e := by rw [mul_assoc]
      _ = (l⁻¹ * f) * e := by rw [(Commute.inv_left hfl).eq]
      _ = l⁻¹ * (f * e) := by rw [mul_assoc]
      _ = l⁻¹ * (e * f) := by rw [hfe]
      _ = l⁻¹ * e * f := by rw [mul_assoc]
  have hX₁c₂ : F ⊔ Subgroup.zpowers zb ≤
      Subgroup.centralizer ({c₂} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine sup_le (fun f hf => Subgroup.mem_centralizer_singleton_iff.mpr
      (hcF he₂ hl₂ hc₂ he₂l f hf)) ((Subgroup.zpowers_le).mpr ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcl hc₂ hzL)
  have hc₁n : c₁ ∉ Subgroup.centralizer ({c₂} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun h1 =>
    hcc (Subgroup.mem_centralizer_singleton_iff.mp h1)
  have hX₁c₁ : F ⊔ Subgroup.zpowers zb ≤
      Subgroup.centralizer ({c₁} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    refine sup_le (fun f hf => Subgroup.mem_centralizer_singleton_iff.mpr
      (hcF he₁ hl₁ hc₁ he₁l f hf)) ((Subgroup.zpowers_le).mpr ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcl hc₁ hzL)
  obtain ⟨hX₂c, hX₂e⟩ := card_sup_zpowers_elem hX₁c₂ hc₁3 hc₁n hX₁c₁ hX₁e
  have hX₂z : F ⊔ Subgroup.zpowers zb ⊔ Subgroup.zpowers c₁ ≤
      Subgroup.centralizer ({zb} : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le hX₁z ((Subgroup.zpowers_le).mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcl hc₁ hzL).symm))
  have hle := card_le_of_le_centralizer_barM hzM hz3 hrk hX₂z hX₂e
  rw [hX₂c, hX₁c, hFc] at hle
  norm_num at hle

end CFSG.AGLEmbedding

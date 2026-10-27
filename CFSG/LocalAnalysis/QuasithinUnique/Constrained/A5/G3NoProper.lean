module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs25
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3SL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Core
public import CFSG.Quasithin.Background.A3Structure312Embed
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.QuasithinUnique.A5.G3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_pCore_iff_mem_pCoreOf {K : Subgroup G} (x : ↥K) :
    x ∈ CFSG.pCore 2 ↥K ↔ (x : G) ∈ pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff x).symm

omit [Finite G] in
theorem sup_eq_of_range_top {K L : Subgroup G} (hLK : L ≤ K) {A : Type*} [Group A]
    (α : ↥K →* A) (hker : α.ker = CFSG.pCore 2 ↥K)
    (htop : (α.comp (Subgroup.inclusion hLK)).range = ⊤) : K = L ⊔ pCoreOf 2 K := by
  refine le_antisymm (fun k hk => ?_) (sup_le hLK (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
  have hα : α ⟨k, hk⟩ ∈ (α.comp (Subgroup.inclusion hLK)).range := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨l, hl⟩ := hα
  have hq : (⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹ : ↥K) ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have : α (Subgroup.inclusion hLK l) = α ⟨k, hk⟩ := hl
    rw [this, mul_inv_cancel]
  rw [hker] at hq
  have hq' := (mem_pCore_iff_mem_pCoreOf _).mp hq
  have hk' : k = ((⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹ : ↥K) : G) * (l : G) := by
    simp
  rw [sup_comm, hk']
  exact Subgroup.mul_mem_sup hq' l.2

omit [Finite G] in
theorem ker_le_pCore {K L : Subgroup G} (hLK : L ≤ K) {A : Type*} [Group A] (α : ↥K →* A)
    (hker : IsPGroup 2 α.ker) :
    (α.comp (Subgroup.inclusion hLK)).ker ≤ CFSG.pCore 2 ↥L := by
  have h2 : IsPGroup 2 (α.comp (Subgroup.inclusion hLK)).ker := by
    intro x
    obtain ⟨n, hn⟩ := hker ⟨Subgroup.inclusion hLK (x : ↥L), x.2⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subgroup.inclusion_injective hLK
    have := congrArg Subtype.val hn
    simpa using this
  have h3 : (α.comp (Subgroup.inclusion hLK)).ker ≤ CFSG.Open.pCore 2 ↥L :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance h2
  assumption

theorem range_top_of_alt5 {K L : Subgroup G} (hLK : L ≤ K) {A : Type*} [Group A] [Finite A]
    (α : ↥K →* A) (hker : IsPGroup 2 α.ker) (hA : Nat.card A = 60) (hLa : IsAltType L 5) :
    (α.comp (Subgroup.inclusion hLK)).range = ⊤ := by
  set φ := α.comp (Subgroup.inclusion hLK) with hφ
  obtain ⟨ρ, hρ, hρk, -⟩ := hLa
  have hle : φ.ker ≤ CFSG.pCore 2 ↥L := ker_le_pCore hLK α hker
  have h1 : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥L := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have h2 : Nat.card (CFSG.pCore 2 ↥L) * 60 = Nat.card ↥L := by
    rw [← hρk]
    have : Nat.card ρ.range = 60 := by
      rw [MonoidHom.range_eq_top.mpr hρ, Subgroup.card_top, Delta5.a5_card]
    rw [← this, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have h3 : Nat.card φ.ker ≤ Nat.card (CFSG.pCore 2 ↥L) := Subgroup.card_le_of_le hle
  have hpos : 0 < Nat.card φ.ker := Nat.card_pos
  have h4 : 60 ≤ Nat.card φ.range := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range < Nat.card φ.ker * 60 :=
      Nat.mul_lt_mul_of_pos_left hlt hpos
    have : Nat.card φ.ker * 60 ≤ Nat.card (CFSG.pCore 2 ↥L) * 60 := Nat.mul_le_mul_right 60 h3
    omega
  have h5 : Nat.card φ.range ≤ 60 := hA ▸ Subgroup.card_le_card_group _
  exact Subgroup.eq_top_of_card_eq _ (by rw [hA]; omega)

omit [Finite G] in
theorem map_mem_normalizer {K L : Subgroup G} (hLK : L ≤ K) {A : Type*} [Group A] (α : ↥K →* A)
    {x : ↥K} (hx : (x : G) ∈ Subgroup.normalizer (L : Set G)) :
    α x ∈ Subgroup.normalizer ((α.comp (Subgroup.inclusion hLK)).range : Set A) := by
  have one_dir : ∀ x : ↥K, (x : G) ∈ Subgroup.normalizer (L : Set G) →
      ∀ y : A, y ∈ (α.comp (Subgroup.inclusion hLK)).range →
        α x * y * (α x)⁻¹ ∈ (α.comp (Subgroup.inclusion hLK)).range := by
    intro x hx y hy
    obtain ⟨l, rfl⟩ := hy
    have hl : (x : G) * (l : G) * (x : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hx l).mp l.2
    refine ⟨⟨_, hl⟩, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨one_dir x hx y, fun hy => ?_⟩
  have hx' : ((x⁻¹ : ↥K) : G) ∈ Subgroup.normalizer (L : Set G) := inv_mem hx
  have := one_dir x⁻¹ hx' _ hy
  simpa [map_inv, mul_assoc] using this

theorem eq_of_range_top {K L P : Subgroup G} (hperf : ⁅K, K⁆ = K) (hLK : L ≤ K) (hPK : P ≤ K)
    (hQP : pCoreOf 2 K ≤ P) {A : Type*} [Group A] (α : ↥K →* A)
    (hker : α.ker = CFSG.pCore 2 ↥K) (htop : (α.comp (Subgroup.inclusion hLK)).range = ⊤)
    (hidx : (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P ∣ 2) : L = K := by
  have hQK : pCoreOf 2 K ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hQn : ((pCoreOf 2 K).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact eq_of_sup_normal hperf hLK hQK hQn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    (sup_eq_of_range_top hLK α hker htop) hPK hQP hidx

theorem exists_iso_alt5 {K L : Subgroup G} (hLK : L ≤ K) {F : Type} [Field F] [Fintype F]
    {n : ℕ} (hn : 1 ≤ n) (hF : Fintype.card F = 2 ^ n) (α : ↥K →* SL(2, F))
    (hker : α.ker = CFSG.pCore 2 ↥K) (hLa : IsAltType L 5) :
    Nonempty (↥((α.comp (Subgroup.inclusion hLK)).range) ≃* alternatingGroup (Fin 5)) := by
  classical
  have hFfin : Finite F := Finite.of_fintype F
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  have hker2 : IsPGroup 2 α.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  set φ := α.comp (Subgroup.inclusion hLK) with hφ
  obtain ⟨ρ, hρ, hρk, -⟩ := hLa
  have hle : φ.ker ≤ CFSG.pCore 2 ↥L := ker_le_pCore hLK α hker2
  have hφ2 : IsPGroup 2 φ.ker := (CFSG.pCore_isPGroup (G := ↥L) (p := 2)).to_le hle
  have hcore : CFSG.pCore 2 ↥L ≤ φ.ker := by
    by_contra hnot
    have hX2 : IsPGroup 2 ((CFSG.pCore 2 ↥L).map φ) :=
      (CFSG.pCore_isPGroup (G := ↥L) (p := 2)).map φ
    have hX1 : (CFSG.pCore 2 ↥L).map φ ≠ ⊥ := by
      intro hbot
      apply hnot
      rw [Subgroup.map_eq_bot_iff] at hbot
      exact hbot
    have hYX : φ.range ≤ Subgroup.normalizer (((CFSG.pCore 2 ↥L).map φ : Subgroup SL(2, F)) :
        Set SL(2, F)) := by
      rintro _ ⟨l, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨c, hc, rfl⟩
        exact ⟨l * c * l⁻¹, (CFSG.pCore_normal (G := ↥L) (p := 2)).conj_mem c hc l, by simp⟩
      · rintro ⟨c, hc, hcx⟩
        refine ⟨l⁻¹ * c * l, ?_, ?_⟩
        · simpa using (CFSG.pCore_normal (G := ↥L) (p := 2)).conj_mem c hc l⁻¹
        · rw [map_mul, map_mul, map_inv, hcx]
          group
    have hYs : Group.IsSolvable φ.range :=
      solvable_of_le_normalizer hn hFn hX2 hX1 hYX
    have hker_solv : Group.IsSolvable φ.ker := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnil : Group.IsNilpotent φ.ker := hφ2.isNilpotent
      infer_instance
    have hLs : Group.IsSolvable ↥L := by
      refine Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict ?_
      intro y hy
      rw [MonoidHom.ker_rangeRestrict] at hy
      exact ⟨⟨y, hy⟩, rfl⟩
    exact not_solvable_alt5 (Group.isSolvable_of_surjective hρ)
  have hkerEq : φ.ker = ρ.ker := (le_antisymm hle hcore).trans hρk.symm
  exact ⟨((QuotientGroup.quotientKerEquivRange φ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hkerEq)).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρ)⟩

omit [Finite G] in
theorem index_image_normalizer {K L P : Subgroup G} (hLK : L ≤ K) (hPK : P ≤ K) {A : Type*}
    [Group A] (α : ↥K →* A)
    (hidx : (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P ∣ 2) :
    (((P.subgroupOf K).map α) ⊓
      Subgroup.normalizer (((α.comp (Subgroup.inclusion hLK)).range : Subgroup A) : Set A)).relIndex
      ((P.subgroupOf K).map α) ∣ 2 := by
  obtain ⟨a, haP, ha⟩ := Subgroup.relIndex_dvd_two_iff.mp hidx
  have haK : a ∈ K := hPK haP
  have haV : α ⟨a, haK⟩ ∈ (P.subgroupOf K).map α :=
    ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr haP, rfl⟩
  refine Subgroup.relIndex_dvd_two_iff.mpr ⟨α ⟨a, haK⟩, haV, fun b' hb' => ?_⟩
  obtain ⟨b, hb, rfl⟩ := hb'
  have hbP : (b : G) ∈ P := Subgroup.mem_subgroupOf.mp hb
  have hbV : α b ∈ (P.subgroupOf K).map α := ⟨b, hb, rfl⟩
  rcases ha b hbP with h | h
  · left
    refine ⟨Subgroup.mul_mem _ hbV haV, ?_⟩
    rw [← map_mul]
    exact map_mem_normalizer hLK α (x := b * ⟨a, haK⟩) h.2
  · right
    exact ⟨hbV, map_mem_normalizer hLK α h.2⟩

theorem no_lin2_large {K L P : Subgroup G} (hLK : L ≤ K) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hn : 3 ≤ n) (hF : Fintype.card F = 2 ^ n) (α : ↥K →* SL(2, F))
    (hαs : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) (hLa : IsAltType L 5)
    (hP : IsSylowTwoOf P K)
    (hidx : (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P ∣ 2) : False := by
  have hFfin : Finite F := Finite.of_fintype F
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hF
  obtain ⟨θ⟩ := exists_iso_alt5 hLK (by omega) hF α hker hLa
  have hPK : P ≤ K := hP.1
  have hPh2 : IsPGroup 2 (P.subgroupOf K) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  have hV2 : IsPGroup 2 ((P.subgroupOf K).map α) := hPh2.map α
  have hVodd : ¬ 2 ∣ ((P.subgroupOf K).map α).index := fun h =>
    hP.2.2 (h.trans (Subgroup.index_map_dvd (P.subgroupOf K) hαs))
  exact sl2_index_normalizer hn hFn θ hV2 hVodd (index_image_normalizer hLK hPK α hidx)

theorem relIndex_ne_zero' (H K : Subgroup G) : H.relIndex K ≠ 0 := fun h => by
  have := Subgroup.relIndex_dvd_card H K
  rw [h, zero_dvd_iff] at this
  exact Nat.card_pos.ne' this

theorem index_inf_normalizer {S₁ S₀ P L : Subgroup G} (hPS : P ≤ S₁) (hS₀S : S₀.relIndex S₁ = 2)
    (hS₀N : S₀ ≤ Subgroup.normalizer (L : Set G)) :
    (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P ∣ 2 := by
  have h1 : (S₀ ⊓ P).relIndex P ≤ 2 := by
    rw [Subgroup.inf_relIndex_right]
    have := Subgroup.relIndex_le_of_le_right (H := S₀) hPS (by rw [hS₀S]; norm_num)
    omega
  have h0 : (S₀ ⊓ P).relIndex P ≠ 0 := relIndex_ne_zero' _ _
  have h2 : (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P ≤ (S₀ ⊓ P).relIndex P :=
    Subgroup.relIndex_le_of_le_left (fun x hx => ⟨hx.2, hS₀N hx.1⟩) h0
  have h3 : (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P ≠ 0 := relIndex_ne_zero' _ _
  have h4 := h2.trans h1
  obtain h | h : (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P = 1 ∨
      (P ⊓ Subgroup.normalizer (L : Set G)).relIndex P = 2 := by omega
  · rw [h]
    exact one_dvd _
  · rw [h]

theorem noProperA5Block : NoProperA5Block := by
  intro G _ _ X S₁ S₀ K L hX hS₁ hS₀ hidx hK hKb hLs hLa hLK hS₀N hLoc
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hP : IsSylowTwoOf (S₁ ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) hS₁
  have hPK : S₁ ⊓ K ≤ K := inf_le_right
  have hQP : pCoreOf 2 K ≤ S₁ ⊓ K := pCoreOf_two_le_of_sylowIn hP.1 hP.2.1 hP.2.2
  have hPidx := index_inf_normalizer (inf_le_left : S₁ ⊓ K ≤ S₁) hidx hS₀N
  rcases hKb.2 with ⟨n, hn, hlin⟩ | hA3 | hA5
  · obtain ⟨F, _, _, hcard, α, hαs, hαk, -⟩ := hlin
    have hker2 : IsPGroup 2 α.ker := by
      rw [hαk]
      exact CFSG.pCore_isPGroup
    rcases Nat.lt_or_ge n 3 with h | h
    · have h2 : n = 2 := by omega
      subst h2
      have hA : Nat.card SL(2, F) = 60 := by
        rw [card_SL2, hcard]
        norm_num
      exact eq_of_range_top hperf hLK hPK hQP α hαk
        (range_top_of_alt5 hLK α hker2 hA hLa) hPidx
    · exact (no_lin2_large hLK h hcard α hαs hαk hLa hP hPidx).elim
  · exfalso
    obtain ⟨α, hα, hαk, -⟩ := hA3
    have hker2 : IsPGroup 2 α.ker := by
      rw [hαk]
      exact CFSG.pCore_isPGroup
    have hcard3 : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    have : Fact (Nat.Prime (Nat.card (alternatingGroup (Fin 3)))) :=
      ⟨by rw [hcard3]; exact Nat.prime_three⟩
    have hcyc : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card rfl
    have hsolv3 : Group.IsSolvable (alternatingGroup (Fin 3)) :=
      Group.isSolvable_of_comm fun a b =>
        (IsCyclic.commGroup (α := alternatingGroup (Fin 3))).mul_comm a b
    have hker_solv : Group.IsSolvable α.ker := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hnil : Group.IsNilpotent α.ker := hker2.isNilpotent
      infer_instance
    have hKs : Group.IsSolvable ↥K :=
      Group.isSolvable_of_ker_le_range α.ker.subtype α fun y hy => ⟨⟨y, hy⟩, rfl⟩
    exact not_isSolvable_of_mem_cComp hK hKs
  · obtain ⟨α, hα, hαk, -⟩ := hA5
    have hker2 : IsPGroup 2 α.ker := by
      rw [hαk]
      exact CFSG.pCore_isPGroup
    exact eq_of_range_top hperf hLK hPK hQP α hαk
      (range_top_of_alt5 hLK α hker2 Delta5.a5_card hLa) hPidx

end CFSG.QuasithinUnique.A5.G3

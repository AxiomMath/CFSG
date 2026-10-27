module

public import CFSG.LocalAnalysis.GH72.Sec5FourTools
public import CFSG.LocalAnalysis.GH72.PGammaL2Local
public import CFSG.LocalAnalysis.GH72.Sec5Roles
public import CFSG.LocalAnalysis.GH72.Sec5BarType
import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.CGT.Foote81L6.Lemma1
public import CFSG.ClassicalInvolution.NormalQuaternion
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.GH72.G3b
public import CFSG.LocalAnalysis.GH72.G3bEight
public import CFSG.LocalAnalysis.GH72.Sec4Bar
public import CFSG.LocalAnalysis.GH72.Sec4Residual
public import CFSG.LocalAnalysis.GH72.Sec5Eighteen
public import CFSG.LocalAnalysis.GH72.Sec5NineteenTools
public import CFSG.LocalAnalysis.GH72.Sec5Tools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PerfectSubgroupLeTwoResidual

public section

namespace CFSG.GH72

open Subgroup
open scoped Pointwise

namespace G5d

open CFSG.ABGLocalTools (IsSylowOf)

section Bar

variable {G : Type*} [Group G]

theorem nonempty_bar_mulEquiv_of_inf_eq {H H' W : Subgroup G} (hWH : W ≤ H) (hWH' : W ≤ H')
    (h : O H ⊓ W = O H' ⊓ W) : Nonempty (bar H W ≃* bar H' W) := by
  set f : W →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hWH) with hf
  set f' : W →* Bar H' := (QuotientGroup.mk' (CFSG.oddCore H')).comp (inclusion hWH') with hf'
  have hrange : f.range = bar H W := by
    rw [hf, MonoidHom.range_comp, inclusion_range]
    rfl
  have hrange' : f'.range = bar H' W := by
    rw [hf', MonoidHom.range_comp, inclusion_range]
    rfl
  have hker : ∀ {K : Subgroup G} (hWK : W ≤ K) (w : W),
      w ∈ ((QuotientGroup.mk' (CFSG.oddCore K)).comp (inclusion hWK)).ker ↔ (w : G) ∈ O K := by
    intro K hWK w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hw
      exact ⟨_, hw, rfl⟩
    · rintro ⟨y, hy, hyw⟩
      have : y = inclusion hWK w := Subtype.ext hyw
      rwa [← this]
  have hkereq : f.ker = f'.ker := by
    ext w
    rw [hker hWH w, hker hWH' w]
    constructor
    · intro hw
      have : (w : G) ∈ O H ⊓ W := ⟨hw, w.2⟩
      rw [h] at this
      exact this.1
    · intro hw
      have : (w : G) ∈ O H' ⊓ W := ⟨hw, w.2⟩
      rw [← h] at this
      exact this.1
  exact ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
        ((QuotientGroup.quotientKerEquivRange f').trans (MulEquiv.subgroupCongr hrange'))))⟩

variable [Finite G]

theorem inf_O_le_of_isSimpleGroup {K K₁ W V : Subgroup G} (hK₁K : K₁ ≤ K) (hWK₁ : W ≤ K₁)
    (hs : IsSimpleGroup (bar K W)) (hV : IsKleinFour V) (hVW : V ≤ W) : O K₁ ⊓ W ≤ O K := by
  have hWK : W ≤ K := hWK₁.trans hK₁K
  set D : Subgroup G := O K₁ ⊓ W with hD
  have hDW : D ≤ W := inf_le_right
  have hDK : D ≤ K := hDW.trans hWK
  have hWD : W ≤ normalizer (D : Set G) := fun w hw =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer_O K₁ (hWK₁ hw), le_normalizer hw⟩
  have hDodd : Odd (Nat.card (bar K D)) :=
    G4c.odd_card_bar ((card_O_odd K₁).of_dvd_nat (card_dvd_of_le inf_le_left))
  have hDn : ((bar K D).subgroupOf (bar K W)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (G4c.bar_mono hDW)).mpr (G4c.bar_le_normalizer hWD)
  have := hs
  have := hDn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((bar K D).subgroupOf (bar K W)) with h | h
  · have hbot : bar K D = ⊥ := by
      rw [← map_subgroupOf_eq_of_le (G4c.bar_mono hDW), h, Subgroup.map_bot]
    exact (G4c.bar_eq_bot_iff hDK).mp hbot
  ·
    exfalso
    have hWD' : bar K W ≤ bar K D := (subgroupOf_eq_top.mp h)
    have hVb : IsKleinFour (bar K V) := G4c.isKleinFour_bar (hVW.trans hWK) hV
    have h4 : Nat.card (bar K V) ∣ Nat.card (bar K D) :=
      card_dvd_of_le ((G4c.bar_mono hVW).trans hWD')
    rw [IsKleinFour.card_four] at h4
    exact (Nat.not_even_iff_odd.mpr hDodd) (even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4))

omit [Finite G] in
theorem exists_eq_sup_zpowers_of_isCyclic_bar {H U : Subgroup G} (hUH : U ≤ H)
    (hc : IsCyclic (bar H U)) : ∃ u : G, U = (U ⊓ O H) ⊔ zpowers u := by
  obtain ⟨⟨ub, hub⟩, hgen⟩ := hc.exists_generator
  obtain ⟨⟨u, huH⟩, hu, rfl⟩ := hub
  have huU : u ∈ U := hu
  refine ⟨u, le_antisymm (fun v hv => ?_) (sup_le inf_le_left (zpowers_le.mpr huU))⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨_, mem_map_of_mem _
    (show (⟨v, hUH hv⟩ : H) ∈ U.subgroupOf H from hv)⟩)
  have hk' : QuotientGroup.mk' (CFSG.oddCore H) (⟨u, huH⟩ ^ k) =
      QuotientGroup.mk' (CFSG.oddCore H) ⟨v, hUH hv⟩ := by
    rw [map_zpow]
    exact congrArg Subtype.val hk
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hk'
  have hO : (u ^ k)⁻¹ * v ∈ O H := ⟨_, hk', by simp⟩
  have hUm : (u ^ k)⁻¹ * v ∈ U := U.mul_mem (U.inv_mem (U.zpow_mem huU k)) hv
  have : v = u ^ k * ((u ^ k)⁻¹ * v) := by group
  rw [this, sup_comm]
  exact mul_mem_sup (zpow_mem_zpowers u k) ⟨hUm, hO⟩

end Bar

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem not_le_centralizer_of_isSylowOf {p : ℕ} (hp : p.Prime) {A H Z P₁ : Subgroup G}
    (hA2 : IsPGroup 2 A) (hAH : A ≤ H) (hZA : Z ≤ A) (hc : Sec4Setting.PConstrainedWrt p A H Z)
    (hP₁ : IsSylowOf p P₁ (O H)) (hAP₁ : A ≤ normalizer (P₁ : Set G)) :
    ¬ Z ≤ centralizer (P₁ : Set G) := by
  obtain ⟨P₀, hP₀, hAP₀, hZP₀⟩ := hc
  have hAO : A ≤ normalizer (O H : Set G) := hAH.trans (le_normalizer_O H)
  have hO2 : ¬ 2 ∣ Nat.card (O H) := fun h =>
    Nat.not_even_iff_odd.mpr (card_O_odd H) (even_iff_two_dvd.mpr h)
  obtain ⟨c, ⟨-, hcA⟩, hcP⟩ := CFSG.ABGTheoremB.exists_conj_eq_of_isSylowOf_normalized_of_coprime
    Nat.prime_two hp hA2 hAO hO2 hP₀ hP₁ hAP₀ hAP₁
  intro hZP
  apply hZP₀
  intro z hz
  rw [mem_centralizer_iff]
  intro q hq
  have hcq : c * q * c⁻¹ ∈ P₁ := by
    rw [← hcP]
    exact ⟨q, hq, rfl⟩
  have h1 := mem_centralizer_iff.mp (hZP hz) _ hcq
  have hcz : c * z = z * c := (mem_centralizer_iff.mp hcA z (hZA hz)).symm
  have h2 : c * (q * z) * c⁻¹ = c * (z * q) * c⁻¹ := by
    calc c * (q * z) * c⁻¹ = c * q * c⁻¹ * (c * z * c⁻¹) := by group
      _ = c * q * c⁻¹ * z := by rw [hcz]; group
      _ = z * (c * q * c⁻¹) := h1
      _ = c * z * c⁻¹ * (c * q * c⁻¹) := by rw [hcz]; group
      _ = c * (z * q) * c⁻¹ := by group
  have h3 := congrArg (fun g => c⁻¹ * g * c) h2
  simp only [mul_assoc, inv_mul_cancel_left] at h3
  simpa [mul_assoc] using h3

theorem covers_inf_normalizer_of_isSylowOf_O {p : ℕ} (hp : p.Prime) {A Z M M₀ H Q : Subgroup G}
    (hA2 : IsPGroup 2 A) (hZA : Z ≤ A) (hM : M = centralizer (Z : Set G)) (hM₀M : M₀ ≤ M)
    (hOM₀ : O M ≤ M₀)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H M₀ (O M) → ∀ z ∈ Z, z ≠ 1 → z ∈ H →
      O H ⊓ C z ≤ O (C z))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hH : H ≠ ⊤) (hAH : A ≤ H) (hcov : Covers H M₀ (O M))
    (hQ : IsSylowOf p Q (O H)) (hAQ : A ≤ normalizer (Q : Set G)) :
    Covers (H ⊓ normalizer (Q : Set G)) M₀ (O M) := by
  have : Fact p.Prime := ⟨hp⟩
  have hZH : Z ≤ H := hZA.trans hAH
  have hZN : Z ≤ normalizer ((H ⊓ normalizer (Q : Set G) : Subgroup G) : Set G) :=
    fun w hw => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (hZH hw), le_normalizer (hAQ (hZA hw))⟩
  have hMz : M ≤ C z := by
    rw [hM]
    exact centralizer_le (Set.singleton_subset_iff.mpr hzZ)
  have hOHM : O H ⊓ M ≤ O M := by
    have h1 : O H ⊓ M ≤ O (C z) :=
      (le_inf inf_le_left (inf_le_right.trans hMz)).trans (h413 H hH hcov z hzZ hz1 (hZH hzZ))
    exact (le_inf h1 inf_le_right).trans (O_inf_le_O_of_le hMz)
  exact covers_of_eq_O_sup (hA2.to_le hZA) hZH hZN inf_le_left
    (eq_sup_inf_normalizer_of_isSylowOf (map_subtype_le _) (le_normalizer_O _) hQ) hM hM₀M hOM₀
    hOHM hcov

theorem exists_pLocal_covers_of_le_O {q : ℕ} (hq : q.Prime)
    {A Z M₀ D : Subgroup G} {x : G} (hA2 : IsPGroup 2 A)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hZA : Z ≤ A) (hxZ : x ∈ Z)
    (hM₀ : M₀ ≤ centralizer (Z : Set G)) (hOM₀ : O (centralizer (Z : Set G)) ≤ M₀)
    (hD : IsPGroup q D) (hD1 : D ≠ ⊥) (hDO : D ≤ O (C x)) :
    ∃ H : Subgroup G, CFSG.IsPLocal q H ∧ A ≤ H ∧ Covers H M₀ (O (centralizer (Z : Set G))) := by
  have : Fact q.Prime := ⟨hq⟩
  have hAC : A ≤ C x := fun a ha => mem_centralizer_singleton_iff.mpr (hAc a ha x (hZA hxZ))
  obtain ⟨P', hP', -⟩ := exists_isMaxInvIn_ge (p := q) (A := A) (H := C x) bot_le IsPGroup.of_bot
    (fun a _ => by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top a)
  have hT := isSylowOf_inf_O_of_isMaxInvIn hq hA2 (hAC.trans le_normalizer) hP'
  have hAT : A ≤ normalizer ((P' ⊓ O (C x) : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨hP'.2.2.1 ha, le_normalizer_O _ (hAC ha)⟩
  have hT1 : P' ⊓ O (C x) ≠ ⊥ := by
    intro hbot
    obtain ⟨c, -, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hT hDO hD
    rw [hbot, le_bot_iff, map_eq_bot_iff_of_injective _ (MulAut.conj c).injective] at hc
    exact hD1 hc
  refine ⟨normalizer ((P' ⊓ O (C x) : Subgroup G) : Set G),
    ⟨_, hT1, hT.isPGroup, rfl⟩, hAT, ?_⟩
  have hZ2 : IsPGroup 2 Z := hA2.to_le hZA
  have hZK : Z ≤ C x := fun z hz =>
    mem_centralizer_singleton_iff.mpr (hAc z (hZA hz) x (hZA hxZ))
  have hZN : Z ≤ normalizer ((C x ⊓ normalizer ((P' ⊓ O (C x) : Subgroup G) : Set G) :
      Subgroup G) : Set G) :=
    fun z hz => inf_normalizer_le_normalizer_inf
      ⟨le_normalizer (hZK hz), le_normalizer (hAT (hZA hz))⟩
  have hFr := eq_sup_inf_normalizer_of_isSylowOf (map_subtype_le _) (le_normalizer_O (C x)) hT
  have hMK : centralizer (Z : Set G) ≤ C x := centralizer_le (Set.singleton_subset_iff.mpr hxZ)
  have hcov : Covers (C x) M₀ (O (centralizer (Z : Set G))) :=
    fun m hm => mem_sup_left ⟨hMK (hM₀ hm), hm⟩
  have h := covers_of_eq_O_sup hZ2 hZK hZN inf_le_left hFr rfl hM₀ hOM₀ (O_inf_le_O_of_le hMK)
    hcov
  unfold Covers at h ⊢
  exact h.trans (sup_le_sup_right (inf_le_inf_right _ inf_le_right) _)

omit [Finite G] in
theorem mem_O_iff_mk_eq_one {J : Subgroup G} (k : J) :
    (k : G) ∈ O J ↔ QuotientGroup.mk' (CFSG.oddCore J) k = 1 := by
  rw [mem_iff_mk_mem_bar le_rfl k, (G4c.bar_eq_bot_iff (map_subtype_le _)).mpr le_rfl, mem_bot]

theorem isCyclic_bar_of_le_centralizer
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K₁ W P U V : Subgroup G} (hWK₁ : W ≤ K₁) (hPK₁ : P ≤ K₁)
    (hWn : ((W ⊔ O K₁).subgroupOf K₁).Normal) (hWs : IsL2OrA7 (bar K₁ W) 5)
    (hV : IsKleinFour V) (hVW : V ≤ W) (hP : IsPGroup p P)
    (hK₁P : K₁ ≤ normalizer ((P ⊔ (W ⊔ O K₁) : Subgroup G) : Set G)) (hUP : U ≤ P)
    (hUV : U ≤ centralizer (V : Set G)) : IsCyclic (bar K₁ U) := by
  have hOK₁ : O K₁ ≤ K₁ := map_subtype_le _
  have hUK₁ : U ≤ K₁ := hUP.trans hPK₁
  have hK₁N : K₁ ≤ normalizer ((W ⊔ O K₁ : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (sup_le hWK₁ hOK₁)).mp hWn
  have hJn : (bar K₁ W).Normal := by
    rw [← G4c.bar_sup_O hWK₁]
    exact hWn.map _ (QuotientGroup.mk'_surjective _)
  have hUodd : Odd (Nat.card (bar K₁ U)) := by
    obtain ⟨n, hn⟩ := (G4c.isPGroup_bar (H := K₁) (hP.to_le hUP)).exists_card_eq
    rw [hn]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  refine isCyclic_of_odd_of_le_centralizer_kleinFour hWs (G4c.isKleinFour_bar (hVW.trans hWK₁) hV)
    (G4c.bar_mono hVW) (by rw [normalizer_eq_top_iff.mpr hJn]; exact le_top) hUodd
    (bar_le_centralizer hUV) ?_
  rw [eq_bot_iff]
  rintro _ ⟨hg, hgc⟩
  rw [← G4c.bar_sup hWK₁ hUK₁] at hg
  obtain ⟨g, hgWU, rfl⟩ := hg
  have hgWU' : (g : G) ∈ W ⊔ U := hgWU
  rw [mem_bot, ← mem_O_iff_mk_eq_one]
  have hW₁ : ∀ w ∈ W, (g : G) * w * (g : G)⁻¹ * w⁻¹ ∈ O K₁ := by
    intro w hw
    have hc := mem_centralizer_iff.mp hgc (QuotientGroup.mk' (CFSG.oddCore K₁) ⟨w, hWK₁ hw⟩)
      (mem_map_of_mem _ (show (⟨w, hWK₁ hw⟩ : K₁) ∈ W.subgroupOf K₁ from hw))
    have h1 := (mem_O_iff_mk_eq_one (g * ⟨w, hWK₁ hw⟩ * g⁻¹ * ⟨w, hWK₁ hw⟩⁻¹)).mpr (by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
      group)
    simpa using h1
  have hgc' : ∀ n ∈ W ⊔ O K₁, (g : G) * n * (g : G)⁻¹ * n⁻¹ ∈ O K₁ := by
    intro n hn
    obtain ⟨w, hw, o, ho, rfl⟩ := mem_sup_of_le_normalizer' (hWK₁.trans (le_normalizer_O K₁)) hn
    have hgo : (g : G) * o * (g : G)⁻¹ * o⁻¹ ∈ O K₁ :=
      (O K₁).mul_mem ((mem_normalizer_iff.mp (le_normalizer_O K₁ g.2) o).mp ho)
        ((O K₁).inv_mem ho)
    have h1 : (g : G) * (w * o) * (g : G)⁻¹ * (w * o)⁻¹ =
        ((g : G) * w * (g : G)⁻¹ * w⁻¹) * (w * ((g : G) * o * (g : G)⁻¹ * o⁻¹) * w⁻¹) := by group
    rw [h1]
    exact (O K₁).mul_mem (hW₁ w hw)
      ((mem_normalizer_iff.mp (le_normalizer_O K₁ (hWK₁ hw)) _).mp hgo)
  exact mem_O_of_centralizes_mod hp2 hOK₁ (le_normalizer_O K₁) (card_O_odd K₁) hWK₁ hPK₁ hK₁N
    (fun w hw h => mem_O_of_commutator_mem_of_isL2OrA7 hWK₁ hWs hw h) hP hK₁P
    (sup_le (le_sup_left.trans le_sup_right) (hUP.trans le_sup_left) hgWU') hgc'

end Sylow

section Centralizes

variable {G : Type*} [Group G] [Finite G]

theorem exists_subgroup_centralizes_mod {H₀ N Om : Subgroup G}
    (hH₀N : H₀ ≤ normalizer (N : Set G)) (hH₀Om : H₀ ≤ normalizer (Om : Set G)) :
    ∃ C : Subgroup G, (∀ g, g ∈ C ↔ g ∈ H₀ ∧ ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ Om) ∧
      H₀ ≤ normalizer (C : Set G) := by
  let C : Subgroup G :=
    { carrier := {g | g ∈ H₀ ∧ ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ Om}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨H₀.mul_mem ha hb, fun n hn => ?_⟩
        have h1 : a * b * n * (a * b)⁻¹ * n⁻¹ =
            (a * (b * n * b⁻¹ * n⁻¹) * a⁻¹) * (a * n * a⁻¹ * n⁻¹) := by group
        rw [h1]
        exact Om.mul_mem ((mem_normalizer_iff.mp (hH₀Om ha) _).mp (hb' n hn)) (ha' n hn)
      one_mem' := ⟨H₀.one_mem, fun n _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨H₀.inv_mem ha, fun n hn => ?_⟩
        have hn' : a⁻¹ * n * a ∈ N := by
          have := (mem_normalizer_iff.mp (hH₀N (H₀.inv_mem ha)) n).mp hn
          simpa using this
        have h1 : a⁻¹ * n * a⁻¹⁻¹ * n⁻¹ =
            (a * (a⁻¹ * n * a) * a⁻¹ * (a⁻¹ * n * a)⁻¹)⁻¹ := by group
        rw [h1]
        exact Om.inv_mem (ha' _ hn') }
  refine ⟨C, fun g => Iff.rfl, fun h hh => mem_normalizer_of_map_conj_le ?_⟩
  rintro _ ⟨c, ⟨hc, hc'⟩, rfl⟩
  exact ⟨H₀.mul_mem (H₀.mul_mem hh hc) (H₀.inv_mem hh), conj_commutator_mem hH₀N hH₀Om hh hc'⟩

theorem mem_O_of_centralizes_mod_of_eq_sup {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K₁ P A N : Subgroup G} (hPK₁ : P ≤ K₁) (hAK₁ : A ≤ K₁) (hP : IsPGroup p P)
    (hAP : A ≤ normalizer (P : Set G)) (hK₁ : K₁ = P ⊔ A ⊔ O K₁)
    (hK₁N : K₁ ≤ normalizer (N : Set G)) {g : G} (hg : g ∈ P ⊔ O K₁)
    (hgc : ∀ n ∈ N, g * n * g⁻¹ * n⁻¹ ∈ O K₁) : g ∈ O K₁ := by
  have hOK₁ : O K₁ ≤ K₁ := map_subtype_le _
  have hEK₁ : P ⊔ O K₁ ≤ K₁ := sup_le hPK₁ hOK₁
  have hK₁E : K₁ ≤ normalizer ((P ⊔ O K₁ : Subgroup G) : Set G) :=
    hK₁.le.trans (sup_le (sup_le (le_sup_left.trans le_normalizer)
      (fun a ha => mem_normalizer_sup (hAP ha) (le_normalizer_O K₁ (hAK₁ ha))))
      (le_sup_right.trans le_normalizer))
  obtain ⟨C, hC, hK₁C⟩ := exists_subgroup_centralizes_mod hK₁N (le_normalizer_O K₁)
  have hPodd : Odd (Nat.card P) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have hEodd : Odd (Nat.card (P ⊔ O K₁ : Subgroup G)) := by
    rw [sup_comm]
    exact odd_card_sup_of_le_normalizer (hPK₁.trans (le_normalizer_O K₁)) (card_O_odd K₁) hPodd
  have hR : C ⊓ (P ⊔ O K₁) ≤ O K₁ := le_O_of_le_normalizer (inf_le_right.trans hEK₁)
    (fun k hk => inf_normalizer_le_normalizer_inf ⟨hK₁C hk, hK₁E hk⟩)
    (hEodd.of_dvd_nat (card_dvd_of_le inf_le_right))
  exact hR ⟨(hC g).mpr ⟨hEK₁ hg, hgc⟩, hg⟩

theorem commutator_le_O_of_eq_sup_of_le_normalizer {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {K₁ P A N Z : Subgroup G} (hPK₁ : P ≤ K₁) (hAK₁ : A ≤ K₁) (hP : IsPGroup p P)
    (hAP : A ≤ normalizer (P : Set G)) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hK₁ : K₁ = P ⊔ A ⊔ O K₁) (hK₁N : K₁ ≤ normalizer (N : Set G)) (hZA : Z ≤ A)
    (hZc : ∀ z ∈ Z, ∀ n ∈ N, z * n * z⁻¹ * n⁻¹ ∈ O K₁) : ⁅K₁, Z⁆ ≤ O K₁ := by
  have hOK₁ : O K₁ ≤ K₁ := map_subtype_le _
  set E : Subgroup G := P ⊔ O K₁ with hE
  have hEK₁ : E ≤ K₁ := sup_le hPK₁ hOK₁
  have hK₁E : K₁ ≤ normalizer (E : Set G) :=
    hK₁.le.trans (sup_le (sup_le (le_sup_left.trans le_normalizer)
      (fun a ha => mem_normalizer_sup (hAP ha) (le_normalizer_O K₁ (hAK₁ ha))))
      (le_sup_right.trans le_normalizer))
  obtain ⟨C, hC, hK₁C⟩ := exists_subgroup_centralizes_mod hK₁N (le_normalizer_O K₁)
  have hEZ : ∀ g ∈ E, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ E := fun g hg z hz => by
    have h1 : g * z * g⁻¹ * z⁻¹ = g * (z * g⁻¹ * z⁻¹) := by group
    rw [h1]
    exact E.mul_mem hg ((mem_normalizer_iff.mp (hK₁E (hAK₁ (hZA hz))) _).mp (E.inv_mem hg))
  have hAZ : ∀ g ∈ A, ∀ z ∈ Z, g * z * g⁻¹ * z⁻¹ ∈ E := fun g hg z hz => by
    rw [hAc g hg z (hZA hz)]
    simp
  have hK₁eq : K₁ ≤ E ⊔ A := by
    rw [hE]
    calc K₁ = P ⊔ A ⊔ O K₁ := hK₁
      _ ≤ P ⊔ O K₁ ⊔ A :=
        sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
          (le_sup_right.trans le_sup_left)
  rw [commutator_le]
  intro g hg z hz
  rw [commutatorElement_def]
  have hzC : z ∈ C := (hC z).mpr ⟨hAK₁ (hZA hz), hZc z hz⟩
  have hcC : g * z * g⁻¹ * z⁻¹ ∈ C :=
    C.mul_mem ((mem_normalizer_iff.mp (hK₁C hg) z).mp hzC) (C.inv_mem hzC)
  exact mem_O_of_centralizes_mod_of_eq_sup hp2 hPK₁ hAK₁ hP hAP hK₁ hK₁N
    (commutator_sup_le ((sup_le hEK₁ hAK₁).trans hK₁E) hEZ hAZ g (hK₁eq hg) z hz)
    ((hC _).mp hcC).2

theorem inf_O_le_of_isPGroup_two {K K₁ W : Subgroup G} (hK₁K : K₁ ≤ K) (hWK₁ : W ≤ K₁)
    (h2 : IsPGroup 2 (bar K W)) : O K₁ ⊓ W ≤ O K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDK : O K₁ ⊓ W ≤ K := inf_le_right.trans (hWK₁.trans hK₁K)
  have hDodd : Odd (Nat.card (bar K (O K₁ ⊓ W))) :=
    G4c.odd_card_bar ((card_O_odd K₁).of_dvd_nat (card_dvd_of_le inf_le_left))
  obtain ⟨n, hn⟩ := (h2.to_le (G4c.bar_mono inf_le_right)).exists_card_eq
  rw [hn] at hDodd
  have hn0 : n = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hDodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hn0, pow_zero, card_eq_one] at hn
  exact (G4c.bar_eq_bot_iff hDK).mp hn

omit [Finite G] in
theorem bar_eq_of_bar_eq {K K₁ W X : Subgroup G} (hK₁K : K₁ ≤ K) (hWK₁ : W ≤ K₁) (hXW : X ≤ W)
    (hOK : O K ≤ O K₁) (h : bar K W = bar K X) : bar K₁ W = bar K₁ X := by
  have hWK : W ≤ K := hWK₁.trans hK₁K
  have hle : W ≤ X ⊔ O K := by
    rw [le_iff_bar_le_bar hWK le_sup_right, G4c.bar_sup_O (hXW.trans hWK), h]
  refine le_antisymm ?_ (G4c.bar_mono hXW)
  rw [← G4c.bar_sup_O (hXW.trans hWK₁)]
  exact G4c.bar_mono (hle.trans (sup_le_sup_left hOK _))

end Centralizes

end G5d

open G5d

namespace Sec5Roles

open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} (ρ : Sec5Roles G A) {p : ℕ}
  (hp : p.Prime) (hp2 : p ≠ 2)

include hp hp2 in
theorem exists_sec5KConfig_of
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H →
      O H ⊓ C y ≤ O (C y))
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H A : Set (Bar H)))
    (hW : ∀ K, CFSG.IsPLocal p K → A ≤ K → Covers K ρ.N₀ (O ρ.N) →
      ¬ Sec4Setting.PConstrainedWrt p A K ρ.X)
    (hKex : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K ρ.N₀ (O ρ.N))
    {P : Subgroup G} (hP : IsMaxInvIn p A ⊤ P) :
    ∃ 𝔨 : Sec5KConfig ρ p, 𝔨.P = P := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := ρ.isPGroup_A
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => ρ.comm ha hb
  have hXA : ρ.X ≤ A := ρ.X_le_A
  have hYA : ρ.Y ≤ A := ρ.Y_le_A
  have hX4 : IsKleinFour ρ.X := ρ.isKleinFour_X
  have hne : ∀ H : Subgroup G, CFSG.IsPLocal p H → H ≠ ⊤ := fun H hH =>
    ρ.ne_top_of_isPLocal hp hp2 hH
  obtain ⟨K, ⟨hKloc, hAK, hcovK, hPK, hKV, hXV⟩, hKmax, hmax₂⟩ :=
    E4b.exists_K_normalizer hp hp2 hA2 hYA rfl ρ.N₀_le ρ.O_N_le_N₀ ρ.normalizer_le_normalizer_N₀
      ρ.normalizer_le_normalizer_O_N h46 h413 ρ.z₂_mem_Y ρ.z₂_ne_one hne hW hKex hP
  have hKtop := hne K hKloc
  obtain ⟨WK, hWKKN, hXWK, hcovWK, -, hWKn, hOWK, hWKs, -, -⟩ := h1N K hKtop hAK hcovK
  have hWKK : WK ≤ K := hWKKN.trans inf_le_left
  have hWKN₀ : WK ≤ ρ.N₀ := hWKKN.trans inf_le_right
  obtain ⟨K₁, hK₁def⟩ : ∃ K₁ : Subgroup G, K₁ = WK ⊔ (P ⊓ K) ⊔ A ⊔ O K := ⟨_, rfl⟩
  have hK₁K : K₁ ≤ K := by
    rw [hK₁def]
    exact sup_le (sup_le (sup_le hWKK inf_le_right) hAK) (map_subtype_le _)
  have hPAK₁ : P ⊓ K ⊔ A ≤ K₁ := by
    rw [hK₁def]
    exact sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  have hWKK₁ : WK ≤ K₁ := by
    rw [hK₁def]
    exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hOKK₁ : O K ≤ K₁ := by
    rw [hK₁def]
    exact le_sup_right
  have hAK₁ : A ≤ K₁ := le_sup_right.trans hPAK₁
  have hPsK₁ : P ⊓ K ≤ K₁ := le_sup_left.trans hPAK₁
  have hcovK₁ : Covers K₁ ρ.N₀ (O ρ.N) := by
    unfold Covers at hcovWK ⊢
    exact hcovWK.trans (sup_le_sup_right (inf_le_inf_right _ hWKK₁) _)
  have hOKOK₁ : O K ≤ O K₁ :=
    le_O_of_le_normalizer hOKK₁ (hK₁K.trans (le_normalizer_O K)) (card_O_odd K)
  have hVK₁ : P ⊓ K ⊓ O K₁ = P ⊓ K ⊓ O K :=
    E4b.inf_O_eq_of_le hp hp2 hA2 hYA rfl ρ.N₀_le ρ.O_N_le_N₀ h413 ρ.z₂_mem_Y ρ.z₂_ne_one hKtop
      hPK hKV hmax₂ hPAK₁ hK₁K hcovK₁
  have hYWK : ρ.Y ≤ centralizer (WK : Set G) := le_centralizer_iff.mp (hWKN₀.trans ρ.N₀_le)
  have hPsp : IsPGroup p (P ⊓ K : Subgroup G) := hP.2.1.to_le inf_le_left
  have hAPs : A ≤ normalizer ((P ⊓ K : Subgroup G) : Set G) := hPK.2.2.1
  have hK₁N : K₁ ≤ normalizer ((WK ⊔ O K₁ : Subgroup G) : Set G) := by
    intro k hk
    have h1 : k ∈ normalizer ((WK ⊔ O K : Subgroup G) : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (sup_le hWKK (map_subtype_le _))).mp hWKn (hK₁K hk)
    have h2 : WK ⊔ O K₁ = (WK ⊔ O K) ⊔ O K₁ := by
      rw [sup_assoc, sup_eq_right.mpr hOKOK₁]
    rw [h2]
    exact mem_normalizer_sup h1 (le_normalizer_O K₁ hk)
  have hWKOK₁ : ((WK ⊔ O K₁).subgroupOf K₁).Normal :=
    (normal_subgroupOf_iff_le_normalizer (sup_le hWKK₁ (map_subtype_le _))).mpr hK₁N
  have hYc : ∀ y ∈ ρ.Y, ∀ n ∈ WK ⊔ O K₁, y * n * y⁻¹ * n⁻¹ ∈ O K₁ := by
    intro y hy n hn
    obtain ⟨w, hw, o, ho, rfl⟩ :=
      mem_sup_of_le_normalizer' (hWKK₁.trans (le_normalizer_O K₁)) hn
    have hyw : y * w = w * y := (mem_centralizer_iff.mp (hYWK hy) w hw).symm
    have h1 : y * (w * o) * y⁻¹ * (w * o)⁻¹ = w * (y * o * y⁻¹ * o⁻¹) * w⁻¹ := by
      calc y * (w * o) * y⁻¹ * (w * o)⁻¹ = (y * w) * o * y⁻¹ * o⁻¹ * w⁻¹ := by group
        _ = (w * y) * o * y⁻¹ * o⁻¹ * w⁻¹ := by rw [hyw]
        _ = w * (y * o * y⁻¹ * o⁻¹) * w⁻¹ := by group
    rw [h1]
    refine (mem_normalizer_iff.mp (le_normalizer_O K₁ (hWKK₁ hw)) _).mp ?_
    exact (O K₁).mul_mem ((mem_normalizer_iff.mp (le_normalizer_O K₁ (hAK₁ (hYA hy))) o).mp ho)
      ((O K₁).inv_mem ho)
  have key : ⁅K₁, ρ.Y⁆ ≤ O K₁ ∧ O K₁ ⊓ WK = O K ⊓ WK ∧
      (IsL2OrA7 (bar K₁ WK) 5 ∨ (bar K₁ WK = bar K₁ ρ.X ∧ IsKleinFour (bar K₁ WK))) ∧
      ∃ u : G, P ⊓ centralizer (ρ.X : Set G) ⊓ K = (P ⊓ K ⊓ O K) ⊔ zpowers u := by
    rcases hWKs with hWKs' | ⟨hbar, -⟩
    ·
      have hK₁Y : ⁅K₁, ρ.Y⁆ ≤ O K₁ :=
        commutator_le_O_of_eq_sup hp2 hWKK inf_le_right hAK hWKn
          (fun w hw h => mem_O_of_commutator_mem_of_isL2OrA7 hWKK hWKs' hw h) hPsp hAPs hAc hYA
          hYWK hK₁def
      have hOK₁W : O K₁ ⊓ WK = O K ⊓ WK :=
        le_antisymm (le_inf (inf_O_le_of_isSimpleGroup hK₁K hWKK₁
          (isSimpleGroup_of_isL2OrA7 le_rfl hWKs') hX4 hXWK) inf_le_right)
          (inf_le_inf_right _ hOKOK₁)
      have hWKs₁ : IsL2OrA7 (bar K₁ WK) 5 := by
        obtain ⟨e⟩ := nonempty_bar_mulEquiv_of_inf_eq hWKK₁ hWKK hOK₁W
        exact CFSG.GH72.isL2OrA7_of_mulEquiv e hWKs'
      have hK₁P : K₁ ≤ normalizer ((P ⊓ K ⊔ (WK ⊔ O K₁) : Subgroup G) : Set G) := by
        refine hK₁def.le.trans (sup_le (sup_le (sup_le ?_ ?_) ?_) ?_)
        · exact (le_sup_left.trans le_sup_right).trans le_normalizer
        · exact le_sup_left.trans le_normalizer
        · exact fun a ha => mem_normalizer_sup (hAPs ha) (hK₁N (hAK₁ ha))
        · exact (hOKOK₁.trans (le_sup_right.trans le_sup_right)).trans le_normalizer
      have hUc : IsCyclic (bar K₁ (P ⊓ centralizer (ρ.X : Set G) ⊓ K)) :=
        isCyclic_bar_of_le_centralizer hp2 hWKK₁ hPsK₁ hWKOK₁ hWKs₁ hX4 hXWK hPsp hK₁P
          (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_left.trans inf_le_right)
      obtain ⟨u, hu⟩ := exists_eq_sup_zpowers_of_isCyclic_bar
        ((le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans hPsK₁) hUc
      have hUO : P ⊓ centralizer (ρ.X : Set G) ⊓ K ⊓ O K₁ = P ⊓ K ⊓ O K := by
        refine le_antisymm ?_ ?_
        · rw [← hVK₁]
          exact inf_le_inf_right _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        · refine le_inf (le_inf (le_inf (inf_le_left.trans inf_le_left) ?_)
            (inf_le_left.trans inf_le_right)) (inf_le_right.trans hOKOK₁)
          exact le_centralizer_iff.mp hXV
      rw [hUO] at hu
      exact ⟨hK₁Y, hOK₁W, Or.inl hWKs₁, u, hu⟩
    ·
      have hWKX : WK ≤ ρ.X ⊔ O K₁ := by
        have hle : WK ≤ ρ.X ⊔ O K := by
          rw [le_iff_bar_le_bar hWKK le_sup_right, G4c.bar_sup_O (hXA.trans hAK), hbar]
        exact hle.trans (sup_le_sup_left hOKOK₁ _)
      have hK₁' : K₁ = P ⊓ K ⊔ A ⊔ O K₁ := by
        refine le_antisymm ?_ (sup_le hPAK₁ (map_subtype_le _))
        calc K₁ = WK ⊔ (P ⊓ K) ⊔ A ⊔ O K := hK₁def
          _ ≤ P ⊓ K ⊔ A ⊔ O K₁ := by
            refine sup_le (sup_le (sup_le ?_ ?_) ?_) (hOKOK₁.trans le_sup_right)
            · exact hWKX.trans (sup_le ((hXA.trans le_sup_right).trans le_sup_left) le_sup_right)
            · exact le_sup_left.trans le_sup_left
            · exact le_sup_right.trans le_sup_left
      have hK₁Y : ⁅K₁, ρ.Y⁆ ≤ O K₁ :=
        commutator_le_O_of_eq_sup_of_le_normalizer hp2 hPsK₁ hAK₁ hPsp hAPs hAc hK₁' hK₁N hYA hYc
      have hOK₁W : O K₁ ⊓ WK = O K ⊓ WK := by
        refine le_antisymm (le_inf (inf_O_le_of_isPGroup_two hK₁K hWKK₁ ?_) inf_le_right)
          (inf_le_inf_right _ hOKOK₁)
        rw [hbar]
        exact G4c.isPGroup_bar (hA2.to_le hXA)
      have hbar₁ : bar K₁ WK = bar K₁ ρ.X := bar_eq_of_bar_eq hK₁K hWKK₁ hXWK hOKOK₁ hbar
      have hX4₁ : IsKleinFour (bar K₁ WK) := by
        rw [hbar₁]
        exact G4c.isKleinFour_bar (hXA.trans hAK₁) hX4
      have hUO : P ⊓ centralizer (ρ.X : Set G) ⊓ K ≤ O K₁ := by
        intro g hg
        have hgK₁ : g ∈ K₁ := hPsK₁ ⟨hg.1.1, hg.2⟩
        refine mem_O_of_centralizes_mod_of_eq_sup hp2 hPsK₁ hAK₁ hPsp hAPs hK₁' hK₁N
          (mem_sup_left ⟨hg.1.1, hg.2⟩) fun n hn => ?_
        obtain ⟨x, hx, o, ho, rfl⟩ := mem_sup_of_le_normalizer'
          ((hXA.trans hAK₁).trans (le_normalizer_O K₁)) ((sup_le hWKX le_sup_right) hn)
        have hxg : x * g = g * x := mem_centralizer_iff.mp hg.1.2 x hx
        have hgo : g * o * g⁻¹ * o⁻¹ ∈ O K₁ :=
          (O K₁).mul_mem ((mem_normalizer_iff.mp (le_normalizer_O K₁ hgK₁) o).mp ho)
            ((O K₁).inv_mem ho)
        have h1 : g * (x * o) * g⁻¹ * (x * o)⁻¹ = x * (g * o * g⁻¹ * o⁻¹) * x⁻¹ := by
          calc g * (x * o) * g⁻¹ * (x * o)⁻¹ = (g * x) * o * g⁻¹ * o⁻¹ * x⁻¹ := by group
            _ = (x * g) * o * g⁻¹ * o⁻¹ * x⁻¹ := by rw [hxg]
            _ = x * (g * o * g⁻¹ * o⁻¹) * x⁻¹ := by group
        rw [h1]
        exact (mem_normalizer_iff.mp (le_normalizer_O K₁ (hAK₁ (hXA hx))) _).mp hgo
      refine ⟨hK₁Y, hOK₁W, Or.inr ⟨hbar₁, hX4₁⟩, 1, ?_⟩
      rw [zpowers_one_eq_bot, sup_bot_eq]
      refine le_antisymm ?_ (le_inf (le_inf (inf_le_left.trans inf_le_left)
        (le_centralizer_iff.mp hXV)) (inf_le_left.trans inf_le_right))
      rw [← hVK₁]
      exact le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hUO
  obtain ⟨hK₁Y, hOK₁W, hWtype, u, hu⟩ := key
  have hK₁eq : K₁ = WK ⊔ (P ⊓ K) ⊔ ρ.Y ⊔ O K₁ := by
    refine le_antisymm ?_ (sup_le (sup_le (sup_le hWKK₁ hPsK₁) (hYA.trans hAK₁))
      (map_subtype_le _))
    calc K₁ = WK ⊔ (P ⊓ K) ⊔ A ⊔ O K := hK₁def
      _ ≤ WK ⊔ (P ⊓ K) ⊔ ρ.Y ⊔ O K₁ := by
        refine sup_le (sup_le (sup_le ?_ ?_) ?_) (hOKOK₁.trans le_sup_right)
        · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
        · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
        · exact ρ.X_sup_Y.ge.trans (sup_le
            (hXWK.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))
            (le_sup_right.trans le_sup_left))
  exact ⟨{
    hp := hp, hp2 := hp2, P := P, hP := hP, K := K,
    hK := ⟨hKloc, hAK, hcovK, hPK, hKV, hXV⟩, K₁ := K₁, hK₁ := ⟨hPAK₁, hK₁K, hcovK₁, hVK₁⟩,
    hUV := ⟨u, hu⟩, hKmax := hKmax,
    hK₁q := ⟨hK₁Y, WK, le_inf hWKK₁ hWKN₀, hXWK, hcovWK, hK₁eq, hWKOK₁, hOK₁W.trans hOWK,
      hWtype⟩ }, rfl⟩

include hp hp2 in
theorem exists_H₀_of {q : ℕ}
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ → Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H →
      O H ⊓ C x ≤ O (C x))
    (h1 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧ IsL2OrA7 (bar H W) q ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)))
    {P : Subgroup G} (hP : IsMaxInvIn p A ⊤ P)
    (hH : ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
      Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y) :
    ∃ H₀ : Subgroup G, (P ⊔ A ≤ H₀ ∧ H₀ ≤ normalizer (CFSG.ambientMaxCardZJ P : Set G) ∧
        Covers H₀ ρ.M₀ (O ρ.M)) ∧
      (¬ ρ.Y ≤ centralizer ((P ⊓ O H₀ : Subgroup G) : Set G) ∧
        Covers (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) ρ.M₀ (O ρ.M) ∧
        ⁅H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G), ρ.X⁆ ≤
          O (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) ∧
        ∃ W : Subgroup G, W ≤ H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G) ⊓ ρ.M₀ ∧
          ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
          ((W ⊔ O (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G))).subgroupOf
            (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G))).Normal ∧
          O (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) ⊓ W = W ⊓ O ρ.M ∧
          IsL2OrA7 (bar (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) W) q) := by
  have : Fact p.Prime := ⟨hp⟩
  have hA2 : IsPGroup 2 A := ρ.isPGroup_A
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => ρ.comm ha hb
  have hXA : ρ.X ≤ A := ρ.X_le_A
  have hYA : ρ.Y ≤ A := ρ.Y_le_A
  have hne : ∀ H : Subgroup G, CFSG.IsPLocal p H → H ≠ ⊤ := fun H hH =>
    ρ.ne_top_of_isPLocal hp hp2 hH
  obtain ⟨⟨⟨hHloc, hAH, -⟩, hcovH⟩, hpcH⟩ := hH
  have hPH : P ≤ normalizer (CFSG.ambientMaxCardZJ P : Set G) :=
    le_normalizer.trans (CFSG.normalizer_le_normalizer_ambientMaxCardZJ P)
  have hHtop := hne _ hHloc
  obtain ⟨WH, hWHHM, hYWH, hcovWH, -, hWHn, -, hWHs, -, -⟩ := h1 _ hHtop hAH hcovH
  have hWHH : WH ≤ normalizer (CFSG.ambientMaxCardZJ P : Set G) := hWHHM.trans inf_le_left
  have hWHM₀ : WH ≤ ρ.M₀ := hWHHM.trans inf_le_right
  obtain ⟨H₀, hH₀def⟩ : ∃ H₀ : Subgroup G,
      H₀ = WH ⊔ P ⊔ A ⊔ O (normalizer (CFSG.ambientMaxCardZJ P : Set G)) := ⟨_, rfl⟩
  have hH₀H : H₀ ≤ normalizer (CFSG.ambientMaxCardZJ P : Set G) := by
    rw [hH₀def]
    exact sup_le (sup_le (sup_le hWHH hPH) hAH) (map_subtype_le _)
  have hPAH₀ : P ⊔ A ≤ H₀ := by
    rw [hH₀def]
    exact sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  have hAH₀ : A ≤ H₀ := le_sup_right.trans hPAH₀
  have hPH₀ : P ≤ H₀ := le_sup_left.trans hPAH₀
  have hWHH₀ : WH ≤ H₀ := by
    rw [hH₀def]
    exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hcovH₀ : Covers H₀ ρ.M₀ (O ρ.M) := by
    unfold Covers at hcovWH ⊢
    exact hcovWH.trans (sup_le_sup_right (inf_le_inf_right _ hWHH₀) _)
  have hH₀top : H₀ ≠ ⊤ := fun h => hHtop (eq_top_iff.mpr (h ▸ hH₀H))
  have hQsyl : IsSylowOf p (P ⊓ O H₀) (O H₀) :=
    isSylowOf_inf_O_of_isMaxInvIn hp hA2 (hAH₀.trans le_normalizer)
      (IsMaxInvIn.of_le hP hPH₀ le_top)
  have hAQ : A ≤ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf ⟨hP.2.2.1 ha, le_normalizer_O H₀ (hAH₀ ha)⟩
  have hOHH₀ : O (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ≤ O H₀ := by
    refine le_O_of_le_normalizer ?_ (hH₀H.trans (le_normalizer_O _)) (card_O_odd _)
    rw [hH₀def]
    exact le_sup_right
  have hYQ : ¬ ρ.Y ≤ centralizer ((P ⊓ O H₀ : Subgroup G) : Set G) := by
    intro hY
    have hPOH := isSylowOf_inf_O_of_isMaxInvIn hp hA2 (hAH.trans le_normalizer)
      (IsMaxInvIn.of_le hP hPH le_top)
    refine not_le_centralizer_of_isSylowOf hp hA2 hAH hYA hpcH hPOH (fun a ha =>
      inf_normalizer_le_normalizer_inf ⟨hP.2.2.1 ha, le_normalizer_O _ (hAH ha)⟩) ?_
    exact hY.trans (centralizer_le (inf_le_inf_left P hOHH₀))
  have hcovH₁ : Covers (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) ρ.M₀ (O ρ.M) :=
    covers_inf_normalizer_of_isSylowOf_O hp hA2 hXA rfl ρ.M₀_le ρ.O_M_le_M₀ h413 ρ.z₁_mem_X
      ρ.z₁_ne_one hH₀top hAH₀ hcovH₀ hQsyl hAQ
  have hXWH : ρ.X ≤ centralizer (WH : Set G) := le_centralizer_iff.mp (hWHM₀.trans ρ.M₀_le)
  have hH₀X : ⁅H₀, ρ.X⁆ ≤ O H₀ :=
    commutator_le_O_of_eq_sup hp2 hWHH hPH hAH hWHn
      (fun w hw h => mem_O_of_commutator_mem_of_isL2OrA7 hWHH hWHs hw h) hP.2.1 hP.2.2.1 hAc
      hXA hXWH hH₀def
  have hAH₁ : A ≤ H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G) := le_inf hAH₀ hAQ
  have hH₁X : ⁅H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G), ρ.X⁆ ≤
      O (H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G)) := by
    refine (le_inf ((commutator_mono inf_le_left le_rfl).trans hH₀X)
      (G4c.commutator_le_of_le le_rfl (hXA.trans hAH₁))).trans ?_
    exact O_inf_le_O_of_le inf_le_left
  have hH₁top : H₀ ⊓ normalizer ((P ⊓ O H₀ : Subgroup G) : Set G) ≠ ⊤ := fun h =>
    hH₀top (eq_top_iff.mpr (h ▸ inf_le_left))
  obtain ⟨WH₁, hW₁a, hW₁b, hW₁c, -, hW₁e, hW₁f, hW₁g, -, -⟩ := h1 _ hH₁top hAH₁ hcovH₁
  exact ⟨H₀, ⟨hPAH₀, hH₀H, hcovH₀⟩, hYQ, hcovH₁, hH₁X, WH₁, hW₁a, hW₁b, hW₁c, hW₁e, hW₁f, hW₁g⟩

include hp hp2 in
theorem exists_sec5ConfigR_of
    (h46 : ∀ P₁ P₂ : Subgroup G, IsMaxInvIn p A ⊤ P₁ → IsMaxInvIn p A ⊤ P₂ →
      ∃ g ∈ normalizer (A : Set G), P₁.map (MulAut.conj g).toMonoidHom = P₂)
    (h413 : ∀ H : Subgroup G, H ≠ ⊤ →
      (Covers H ρ.M₀ (O ρ.M) → ∀ x ∈ ρ.X, x ≠ 1 → x ∈ H → O H ⊓ C x ≤ O (C x)) ∧
      (Covers H ρ.N₀ (O ρ.N) → ∀ y ∈ ρ.Y, y ≠ 1 → y ∈ H → O H ⊓ C y ≤ O (C y)))
    (hHns : QuotIs ρ.M₀ (O ρ.M) (fun L _ => IsL2OrA7 L 5))
    (h1R : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.Y ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer (bar H A : Set (Bar H)))
    (h1N : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.N₀ (O ρ.N) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.N₀ ∧ ρ.X ≤ W ∧ Covers W ρ.N₀ (O ρ.N) ∧
        H ⊓ ρ.N₀ ≤ W ⊔ (H ⊓ O ρ.N) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.N ∧
        (IsL2OrA7 (bar H W) 5 ∨ (bar H W = bar H ρ.X ∧ IsKleinFour (bar H W))) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H W : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.N) ≤ centralizer (bar H A : Set (Bar H)))
    (h55 : ∀ x ∈ ρ.X, x ≠ 1 → Sec4Setting.PConstrainedWrt p A (C x) ρ.Y →
      ∀ P : Subgroup G, IsMaxInvIn p A ⊤ P →
        ρ.IsCoveringFirst p (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ∧
          Sec4Setting.PConstrainedWrt p A (normalizer (CFSG.ambientMaxCardZJ P : Set G)) ρ.Y)
    (h56 : ∀ x ∈ ρ.X, x ≠ 1 → Sec4Setting.PConstrainedWrt p A (C x) ρ.Y →
      (¬ ∃ H, ρ.IsCovering p H) →
      ∀ K, CFSG.IsPLocal p K → A ≤ K → Covers K ρ.N₀ (O ρ.N) →
        ¬ Sec4Setting.PConstrainedWrt p A K ρ.X)
    {x₀ : G} (hx₀ : x₀ ∈ ρ.X ∧ x₀ ≠ 1 ∧ Sec4Setting.PConstrainedWrt p A (C x₀) ρ.Y)
    (hKex : ∃ K, CFSG.IsPLocal p K ∧ A ≤ K ∧ Covers K ρ.N₀ (O ρ.N))
    (hno : ¬ ∃ H, ρ.IsCovering p H) :
    Nonempty (Sec5ConfigR ρ p) := by
  obtain ⟨P, hP, -⟩ := exists_isMaxInvIn_ge (p := p) (A := A) (H := ⊤) le_top IsPGroup.of_bot
    (fun a _ => by
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top a)
  have h1 : ∀ H : Subgroup G, H ≠ ⊤ → A ≤ H → Covers H ρ.M₀ (O ρ.M) →
      ∃ W : Subgroup G, W ≤ H ⊓ ρ.M₀ ∧ ρ.Y ≤ W ∧ Covers W ρ.M₀ (O ρ.M) ∧
        H ⊓ ρ.M₀ ≤ W ⊔ (H ⊓ O ρ.M) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
        O H ⊓ W = W ⊓ O ρ.M ∧ IsL2OrA7 (bar H W) 5 ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H W : Subgroup (Bar H)) : Set (Bar H)) ∧
        bar H (H ⊓ O ρ.M) ≤ centralizer ((bar H A : Subgroup (Bar H)) : Set (Bar H)) := by
    intro H hH hAH hcov
    obtain ⟨W, h₁, h₂, h₃, h₄, h₅, h₆, -, h₈, h₉⟩ := h1R H hH hAH hcov
    exact ⟨W, h₁, h₂, h₃, h₄, h₅, h₆, isL2OrA7_bar_of_covers (h₁.trans inf_le_left)
      (h₁.trans inf_le_right) ρ.M₀_le_normalizer_O_M h₃ h₆ hHns, h₈, h₉⟩
  obtain ⟨H₀, hH₀, hH₁⟩ := ρ.exists_H₀_of hp hp2 (fun H hH => (h413 H hH).1) h1 hP
    (h55 x₀ hx₀.1 hx₀.2.1 hx₀.2.2 P hP)
  obtain ⟨𝔨, rfl⟩ := ρ.exists_sec5KConfig_of hp hp2 h46 (fun H hH => (h413 H hH).2) h1N
    (h56 x₀ hx₀.1 hx₀.2.1 hx₀.2.2 hno) hKex hP
  exact ⟨{ 𝔨 with x₀ := x₀, hx₀ := hx₀, hno := hno, H₀ := H₀, hH₀ := hH₀, hH₁ := hH₁ }⟩

end Sec5Roles

end CFSG.GH72

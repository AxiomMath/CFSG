module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1Closure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Lemma19

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem mem_or_mem_or_mul_mem_of_index_two {K : Type*} [Group K] {R : Subgroup K}
    (hR : R.index = 2) (a b : K) : a ∈ R ∨ b ∈ R ∨ a * b ∈ R := by
  by_cases ha : a ∈ R
  · exact Or.inl ha
  by_cases hb : b ∈ R
  · exact Or.inr (Or.inl hb)
  exact Or.inr (Or.inr ((Subgroup.mul_mem_iff_of_index_two hR).mpr (iff_of_false ha hb)))

theorem dihedralGroup_two_exists_ne :
    ∀ b : DihedralGroup 2, ∃ a : DihedralGroup 2, a ≠ 1 ∧ a ≠ b := by
  decide

theorem natCast_half_add_half {M : ℕ} (hM : Even M) :
    ((M / 2 : ℕ) : ZMod M) + ((M / 2 : ℕ) : ZMod M) = 0 := by
  obtain ⟨m, hm⟩ := hM
  rw [← Nat.cast_add, show M / 2 + M / 2 = M by omega, ZMod.natCast_self]

theorem dihedralGroup_orderOf_r_half {M : ℕ} (hM : Even M) (hM0 : M ≠ 0) :
    orderOf (DihedralGroup.r ((M / 2 : ℕ) : ZMod M)) = 2 := by
  have : NeZero M := ⟨hM0⟩
  refine orderOf_eq_prime (by
    rw [pow_two, DihedralGroup.r_mul_r, natCast_half_add_half hM, DihedralGroup.r_zero]) ?_
  rw [Ne, ← DihedralGroup.r_zero, DihedralGroup.r.injEq, ZMod.natCast_eq_zero_iff]
  obtain ⟨m, hm⟩ := hM
  intro hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

def dihedralTwoTorsion (M : ℕ) : Subgroup (DihedralGroup M) where
  carrier := {g | ∃ i : ZMod M, i + i = 0 ∧ (g = DihedralGroup.r i ∨ g = DihedralGroup.sr i)}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl | rfl⟩ ⟨j, hj, rfl | rfl⟩
    · exact ⟨i + j, by linear_combination hi + hj, Or.inl (DihedralGroup.r_mul_r i j)⟩
    · exact ⟨j - i, by linear_combination hj - hi, Or.inr (DihedralGroup.r_mul_sr i j)⟩
    · exact ⟨i + j, by linear_combination hi + hj, Or.inr (DihedralGroup.sr_mul_r i j)⟩
    · exact ⟨j - i, by linear_combination hj - hi, Or.inl (DihedralGroup.sr_mul_sr i j)⟩
  one_mem' := ⟨0, add_zero 0, Or.inl DihedralGroup.one_def⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl | rfl⟩
    · exact ⟨-i, by linear_combination -hi, Or.inl (DihedralGroup.inv_r i)⟩
    · exact ⟨i, hi, Or.inr (DihedralGroup.inv_sr i)⟩

theorem dihedralTwoTorsion_commute {M : ℕ} {a b : DihedralGroup M}
    (ha : a ∈ dihedralTwoTorsion M) (hb : b ∈ dihedralTwoTorsion M) : a * b = b * a := by
  obtain ⟨i, hi, rfl | rfl⟩ := ha <;> obtain ⟨j, hj, rfl | rfl⟩ := hb
  · rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  · rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    linear_combination -hi
  · rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
    congr 1
    linear_combination hj
  · rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr]
    congr 1
    linear_combination hj - hi

theorem dihedralTwoTorsion_mul_self {M : ℕ} {a : DihedralGroup M}
    (ha : a ∈ dihedralTwoTorsion M) : a * a = 1 := by
  obtain ⟨i, hi, rfl | rfl⟩ := ha
  · rw [DihedralGroup.r_mul_r, hi, DihedralGroup.r_zero]
  · exact DihedralGroup.sr_mul_self i

theorem r_half_mem_dihedralTwoTorsion {M : ℕ} (hM : Even M) :
    DihedralGroup.r ((M / 2 : ℕ) : ZMod M) ∈ dihedralTwoTorsion M :=
  ⟨_, natCast_half_add_half hM, Or.inl rfl⟩

theorem sr_zero_mem_dihedralTwoTorsion {M : ℕ} :
    DihedralGroup.sr (0 : ZMod M) ∈ dihedralTwoTorsion M :=
  ⟨0, add_zero 0, Or.inr rfl⟩

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem exists_mem_X_ne (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) : ∃ y ∈ b1X T L, y ≠ 1 ∧ y ≠ x := by
  obtain ⟨a, ha1, hax⟩ := dihedralGroup_two_exists_ne (hb.psiX ⟨x, hx⟩)
  refine ⟨hb.psiX.symm a, (hb.psiX.symm a).2, fun h => ha1 ?_, fun h => hax ?_⟩
  · rw [← hb.psiX.apply_symm_apply a, show hb.psiX.symm a = 1 from Subtype.ext h, map_one]
  · rw [← hb.psiX.apply_symm_apply a, show hb.psiX.symm a = ⟨x, hx⟩ from Subtype.ext h]

theorem mem_centralizer_X_of_commute (hb : CaseB1 Q B T L M) {x y c : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hy : y ∈ b1X T L) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hyx : y ≠ x)
    (hcx : Commute c x) (hcy : Commute c y) :
    c ∈ Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, one_mul, mul_one]
  by_cases hzx : z = x
  · rw [hzx]
    exact hcx.eq.symm
  rcases hb.eq_or_eq_mul_of_mem_X hx hy hz hx1 hy1 hyx hz1 hzx with rfl | rfl
  · exact hcy.eq.symm
  · exact (hcx.mul_right hcy).eq.symm

theorem exists_mul_oddCore (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1)
    (g : Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J))) :
    ∃ c ∈ Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)),
      ∃ k ∈ CFSG.oddCore (Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J))),
        (g : J ⧸ Subgroup.center J) = c * k := by
  obtain ⟨y, hy, hy1, hyx⟩ := hb.exists_mem_X_ne hx
  have hS : (hb.sylow : Subgroup (J ⧸ Subgroup.center J)) ≤ Subgroup.centralizer {x} :=
    hb.S_le_centralizer hx
  have hmem : ∀ s : Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J)),
      s ∈ (hb.sylow.subtype hS : Subgroup _) ↔ (s : J ⧸ Subgroup.center J) ∈ b1S T := fun s => by
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    rfl
  let z : (hb.sylow.subtype hS :
      Subgroup (Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J)))) :=
    ⟨⟨y, hS (hb.X_le_S hy)⟩, (hmem _).mpr (hb.X_le_S hy)⟩
  have hzZ : z ∈ Subgroup.center (hb.sylow.subtype hS : Subgroup _) :=
    Subgroup.mem_center_iff.mpr fun s => Subtype.ext (Subtype.ext
      (hb.commute_of_mem_X_of_mem_S hy ((hmem s).mp s.2)).eq.symm)
  have hz : orderOf z = 2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hb.orderOf_of_mem_X hy hy1
  obtain ⟨c, hc, k, hk, hgck⟩ := (CFSG.Adapters.glauberman_zStar (hb.sylow.subtype hS) z hzZ hz
    fun g hg => Subtype.ext (hb.inv_mul_mul_eq_of_mem_centralizer hx hx1 hy g.2
      ((hmem _).mp hg))).1 g
  exact ⟨c, hb.mem_centralizer_X_of_commute hx hy hx1 hy1 hyx
    (Subgroup.mem_centralizer_singleton_iff.mp c.2)
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)), k, hk,
    congrArg Subtype.val hgck⟩

theorem centralizer_le_sup_oddCore (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J)) ≤
      Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)) ⊔
        (CFSG.oddCore (Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J)))).map
          (Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J))).subtype := by
  intro g hg
  obtain ⟨c, hc, k, hk, hgck⟩ := hb.exists_mul_oddCore hx hx1 ⟨g, hg⟩
  rw [show g = c * k from hgck]
  exact Subgroup.mul_mem_sup hc (Subgroup.mem_map_of_mem _ hk)

noncomputable def psiInv (hb : CaseB1 Q B T L M) :
    DihedralGroup 2 × DihedralGroup M →* J ⧸ Subgroup.center J :=
  (b1S T).subtype.comp hb.psi.symm.toMonoidHom

theorem psiInv_apply (hb : CaseB1 Q B T L M) (w : DihedralGroup 2 × DihedralGroup M) :
    hb.psiInv w = ((hb.psi.symm w : b1S T) : J ⧸ Subgroup.center J) := by
  rfl

theorem psiInv_injective (hb : CaseB1 Q B T L M) : Function.Injective hb.psiInv :=
  (b1S T).subtype_injective.comp hb.psi.symm.injective

noncomputable def b1A (hb : CaseB1 Q B T L M) : Subgroup (J ⧸ Subgroup.center J) :=
  ((⊤ : Subgroup (DihedralGroup 2)).prod (dihedralTwoTorsion M)).map hb.psiInv

theorem b1A_le_S (hb : CaseB1 Q B T L M) : hb.b1A ≤ b1S T := by
  rintro _ ⟨w, -, rfl⟩
  exact (hb.psi.symm w).2

theorem psiInv_mem_b1A (hb : CaseB1 Q B T L M) (a : DihedralGroup 2) {b : DihedralGroup M}
    (hbV : b ∈ dihedralTwoTorsion M) : hb.psiInv (a, b) ∈ hb.b1A :=
  Subgroup.mem_map_of_mem _ (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top a, hbV⟩)

theorem isElementaryAbelian_b1A (hb : CaseB1 Q B T L M) : IsElementaryAbelian 2 hb.b1A := by
  have hcomm : ∀ a ∈ hb.b1A, ∀ b ∈ hb.b1A, a * b = b * a := by
    rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg hb.psiInv (Prod.ext (dihedralGroup_two_mul_comm _ _)
      (dihedralTwoTorsion_commute (Subgroup.mem_prod.mp hw).2 (Subgroup.mem_prod.mp hw').2))
  have hsq : ∀ a ∈ hb.b1A, a * a = 1 := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, show w * w = 1 from Prod.ext (dihedralGroup_two_mul_self _)
      (dihedralTwoTorsion_mul_self (Subgroup.mem_prod.mp hw).2), map_one]
  exact { is_comm := ⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩
          exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
            Subtype.ext (by rw [Subgroup.coe_pow, pow_two, hsq _ a.2, Subgroup.coe_one]) }

theorem nontrivial_b1A (hb : CaseB1 Q B T L M) : Nontrivial hb.b1A := by
  refine ⟨⟨⟨_, hb.psiInv_mem_b1A (DihedralGroup.r 1) (one_mem _)⟩, 1, fun h => ?_⟩⟩
  have h1 := (map_eq_one_iff hb.psiInv hb.psiInv_injective).mp (congrArg Subtype.val h)
  exact absurd (Prod.mk_eq_one.mp h1).1 (by decide)

theorem exists_isMixedInv_of_index_two (hb : CaseB1 Q B T L M) {R : Subgroup hb.b1A}
    (hR : R.index = 2) : ∃ t ∈ R, IsMixedInv (t : J ⧸ Subgroup.center J) := by
  have key : ∀ {g g' : J ⧸ Subgroup.center J} (hg : g ∈ hb.b1A) (hg' : g' ∈ hb.b1A),
      g ∈ R.map hb.b1A.subtype ∨ g' ∈ R.map hb.b1A.subtype ∨
        g * g' ∈ R.map hb.b1A.subtype := by
    intro g g' hg hg'
    rcases mem_or_mem_or_mul_mem_of_index_two hR ⟨g, hg⟩ ⟨g', hg'⟩ with h | h | h
    · exact Or.inl (Subgroup.mem_map_of_mem _ h)
    · exact Or.inr (Or.inl (Subgroup.mem_map_of_mem _ h))
    · exact Or.inr (Or.inr (Subgroup.mem_map_of_mem _ h))
  obtain ⟨a, ha1, haR⟩ : ∃ a : DihedralGroup 2, a ≠ 1 ∧
      hb.psiInv (a, 1) ∈ R.map hb.b1A.subtype := by
    rcases key (hb.psiInv_mem_b1A (DihedralGroup.r 1) (one_mem _))
      (hb.psiInv_mem_b1A (DihedralGroup.sr 0) (one_mem _)) with h | h | h
    · exact ⟨_, by decide, h⟩
    · exact ⟨_, by decide, h⟩
    · rw [← map_mul, Prod.mk_mul_mk, mul_one] at h
      exact ⟨_, by decide, h⟩
  obtain ⟨b, hb2, hbR⟩ : ∃ b : DihedralGroup M, orderOf b = 2 ∧
      hb.psiInv (1, b) ∈ R.map hb.b1A.subtype := by
    rcases key (hb.psiInv_mem_b1A 1 (r_half_mem_dihedralTwoTorsion hb.even))
      (hb.psiInv_mem_b1A 1 sr_zero_mem_dihedralTwoTorsion) with h | h | h
    · exact ⟨_, dihedralGroup_orderOf_r_half hb.even hb.ne_zero, h⟩
    · exact ⟨_, DihedralGroup.orderOf_sr 0, h⟩
    · rw [← map_mul, Prod.mk_mul_mk, mul_one, DihedralGroup.r_mul_sr] at h
      exact ⟨_, DihedralGroup.orderOf_sr _, h⟩
  have ht := (R.map hb.b1A.subtype).mul_mem haR hbR
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] at ht
  obtain ⟨t, htR, hteq⟩ := ht
  refine ⟨t, htR, ?_⟩
  rw [show (t : J ⧸ Subgroup.center J) = hb.psiInv (a, b) from hteq, psiInv_apply]
  exact (hb.isMixedInv_psi_symm_iff a b).mpr ⟨ha1, hb2⟩

theorem le_b1Bar_of_odd (hb : CaseB1 Q B T L M) {W : Subgroup (J ⧸ Subgroup.center J)}
    (hSW : b1S T ≤ Subgroup.normalizer (W : Set (J ⧸ Subgroup.center J)))
    (hW : Odd (Nat.card W)) : W ≤ b1Bar B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hb.isElementaryAbelian_b1A
  have := hb.nontrivial_b1A
  let _ : MulDistribMulAction hb.b1A W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer hb.b1A W (hb.b1A_le_S.trans hSW)
  have hp : ¬ 2 ∣ Nat.card W := fun h =>
    (Nat.not_even_iff_odd.mpr hW) (even_iff_two_dvd.mpr h)
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := hb.b1A) (H := W) hp
  have hle : ⨆ (R : Subgroup hb.b1A) (_ : R.index = 2), CFSG.fixedPointSubgroup R W ≤
      (b1Bar B).comap W.subtype := by
    refine iSup₂_le fun R hR => ?_
    obtain ⟨t, htR, htm⟩ := hb.exists_isMixedInv_of_index_two hR
    intro w hw
    have htw := congrArg Subtype.val (hw ⟨t, htR⟩)
    change (t : J ⧸ Subgroup.center J) * w * (t : J ⧸ Subgroup.center J)⁻¹ = w at htw
    refine hb.setting.centralizer_le_of_isMixedInv htm (hb.S_le (hb.b1A_le_S t.2)) ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (w : J ⧸ Subgroup.center J) * t =
        t * w * (t : J ⧸ Subgroup.center J)⁻¹ * t := by rw [htw]
      _ = t * w := by group
  rw [hgen, top_le_iff] at hle
  intro w hw
  have hw' : (⟨w, hw⟩ : W) ∈ (b1Bar B).comap W.subtype := hle ▸ Subgroup.mem_top _
  exact hw'

theorem oddCore_centralizer_le (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) :
    (CFSG.oddCore (Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J)))).map
      (Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J))).subtype ≤ b1Bar B := by
  refine hb.le_b1Bar_of_odd (fun s hs => Subgroup.le_normalizer_map _
    (Subgroup.mem_map_of_mem _ (?_ : (⟨s, hb.S_le_centralizer hx hs⟩ :
      Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J))) ∈ _))) ?_
  · rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top _
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact CFSG.ComponentClassification.OddCore.odd_card _

theorem centralizer_le_of_centralizer_X_le (hb : CaseB1 Q B T L M)
    {x : J ⧸ Subgroup.center J} (hx : x ∈ b1X T L) (hx1 : x ≠ 1)
    (hX : Subgroup.centralizer (b1X T L : Set (J ⧸ Subgroup.center J)) ≤ b1Bar B) :
    Subgroup.centralizer ({x} : Set (J ⧸ Subgroup.center J)) ≤ b1Bar B :=
  (hb.centralizer_le_sup_oddCore hx hx1).trans (sup_le hX (hb.oddCore_centralizer_le hx))

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

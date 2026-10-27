module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIIStruct
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Assembly
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TypeIICommon

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3T U3LineWC TypeAutPCard TypeTorusIrred TypeTorusFpf
  TypeTorusOnCenter TypeBorelMax u3_normal_core_proof_gen)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G} {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
  {Shape : ∀ {X : Type} [Group X], Subgroup X → Subgroup X → Subgroup X → Prop}

private theorem zin_eq_inf_centralizer_aux {K : Type} [Group K] (S : Subgroup K) :
    Zin S = S ⊓ Subgroup.centralizer (S : Set K) := by
  ext y
  constructor
  · rintro ⟨⟨z, hz⟩, hzc, rfl⟩
    refine Subgroup.mem_inf.2 ⟨hz, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro h hh
    have := Subgroup.mem_center_iff.mp hzc ⟨h, hh⟩
    exact congrArg Subtype.val this
  · intro hy
    obtain ⟨hyS, hyc⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_map.2 ⟨⟨y, hyS⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.2 fun g => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hyc g g.2)

private theorem normalizer_le_normalizer_of_conj_mem {K : Type} [Group K] {S A : Subgroup K}
    (h : ∀ n ∈ Subgroup.normalizer (S : Set K), ∀ a ∈ A, n * a * n⁻¹ ∈ A) :
    Subgroup.normalizer (S : Set K) ≤ Subgroup.normalizer (A : Set K) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => h n hn a ha, fun ha => ?_⟩
  have := h n⁻¹ (inv_mem hn) _ ha
  simpa [mul_assoc] using this

private theorem fpf_of_irred_core {K : Type} [Group K] {S : Subgroup K}
    (hirr : ∀ A : Subgroup K, A ≤ S → S ⊓ Subgroup.centralizer (S : Set K) ≤ A →
      (∀ n ∈ Subgroup.normalizer (S : Set K), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
      A = S ⊓ Subgroup.centralizer (S : Set K) ∨ A = S)
    (hnab : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) {t : K} (htS : t ∈ S)
    (hfix : ∀ n ∈ Subgroup.normalizer (S : Set K),
      n * t * n⁻¹ * t⁻¹ ∈ S ⊓ Subgroup.centralizer (S : Set K)) :
    t ∈ S ⊓ Subgroup.centralizer (S : Set K) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup K, Z = S ⊓ Subgroup.centralizer (S : Set K) := ⟨_, rfl⟩
  rw [← hZ] at hirr hfix ⊢
  have hZS : Z ≤ S := by rw [hZ]; exact inf_le_left
  have hZc : ∀ z ∈ Z, ∀ s ∈ S, s * z = z * s := by
    intro z hz s hs
    rw [hZ] at hz
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 s hs
  have hzt : Subgroup.zpowers t ≤ S := Subgroup.zpowers_le.mpr htS
  obtain ⟨A, hA⟩ : ∃ A : Subgroup K, A = Subgroup.zpowers t ⊔ Z := ⟨_, rfl⟩
  have hAS : A ≤ S := by rw [hA]; exact sup_le hzt hZS
  have hZA : Z ≤ A := by rw [hA]; exact le_sup_right
  have htA : t ∈ A := by rw [hA]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hLE : Subgroup.zpowers t ≤ Subgroup.normalizer (Z : Set K) := by
    have h1 : Subgroup.zpowers t ≤ Subgroup.centralizer (Z : Set K) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hZc z hz t htS).symm
    exact h1.trans (Subgroup.centralizer_le_normalizer _)
  have hprod : ∀ a ∈ A, ∃ y ∈ Subgroup.zpowers t, ∃ z ∈ Z, y * z = a := by
    intro a ha
    have h1 : a ∈ ((A : Subgroup K) : Set K) := ha
    rw [hA, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLE] at h1
    exact Set.mem_mul.mp h1
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, hy, z, hz, rfl⟩ := hprod a ha
    obtain ⟨y', hy', z', hz', rfl⟩ := hprod b hb
    have hyy' : Commute y y' := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      exact Commute.zpow_zpow_self t i j
    have hyz' : Commute y z' := hZc z' hz' y (hzt hy)
    have hzy' : Commute z y' := (hZc z hz y' (hzt hy')).symm
    have hzz' : Commute z z' := (hZc z hz z' (hZS hz')).symm
    exact ((hyy'.mul_right hyz').mul_left (hzy'.mul_right hzz')).eq
  have hNZ : ∀ n ∈ Subgroup.normalizer (S : Set K), ∀ z ∈ Z, n * z * n⁻¹ ∈ Z := by
    intro n hn z hz
    rw [hZ]
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn z).mp (hZS hz), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ S := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) s).mp hs
      simpa using h1
    have h1 := hZc z hz _ hs'
    calc s * (n * z * n⁻¹) = n * ((n⁻¹ * s * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * s * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * s := by group
  have hinvA : ∀ n ∈ Subgroup.normalizer (S : Set K), ∀ a ∈ A, n * a * n⁻¹ ∈ A := by
    intro n hn a ha
    have hle : A ≤ A.comap (MulAut.conj n).toMonoidHom := by
      conv_lhs => rw [hA]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        show n * t * n⁻¹ ∈ A
        have hw : n * t * n⁻¹ * t⁻¹ ∈ Z := hfix n hn
        have : n * t * n⁻¹ = (n * t * n⁻¹ * t⁻¹) * t := by group
        rw [this]
        exact A.mul_mem (hZA hw) htA
      · intro z hz
        exact hZA (hNZ n hn z hz)
    exact hle ha
  rcases hirr A hAS hZA hinvA with h | h
  · rw [← h]
    exact htA
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    exact hab (hAcomm a (by rw [h]; exact ha) b (by rw [h]; exact hb))

theorem typeAutPCard_of_extra [Fact p.Prime] (hX : ExtraFacts Typ p Shape) : TypeAutPCard Typ p :=
  fun K _ _ hK hz S hS => typeII_aut_pgroup_card_dvd (hX.sylow K hK) (hX.noOuter K hK) hz S hS

theorem typeTorusIrred_of_extra (hX : ExtraFacts Typ p Shape) : TypeTorusIrred Typ p := by
  intro K _ _ hK T A hAT hZA hinv
  have hZ := zin_eq_inf_centralizer_aux (T : Subgroup K)
  have hNA : Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ Subgroup.normalizer (A : Set K) :=
    normalizer_le_normalizer_of_conj_mem hinv
  rw [← hZ] at hZA ⊢
  exact hX.irreducible K hK T A hZA hAT hNA

theorem typeTorusFpf_of_extra (hX : ExtraFacts Typ p Shape) : TypeTorusFpf Typ p := by
  intro K _ _ hK T t htT hfix
  exact fpf_of_irred_core (fun A h1 h2 h3 => typeTorusIrred_of_extra hX K hK T A h1 h2 h3)
    (hX.sylow K hK T).2.1 htT hfix

theorem typeTorusOnCenter_of_extra [Fact p.Prime] (hX : ExtraFacts Typ p Shape) :
    TypeTorusOnCenter Typ p := by
  intro K _ _ hK T c hcT hcC hc1 k hk
  have hcZ : c ∈ Zin (T : Subgroup K) := by
    rw [zin_eq_inf_centralizer_aux]
    exact Subgroup.mem_inf.mpr ⟨hcT, hcC⟩
  have hord : orderOf c = p := orderOf_eq_prime ((hX.sylow K hK T).2.2 c hcT) hc1
  have hck : c ^ k ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_iff_zpow_eq_one.mpr h
    rw [hord] at h1
    exact hk h1
  exact hX.transCenter K hK T c hcZ hc1 (c ^ k) (Subgroup.zpow_mem _ hcZ k) hck

theorem typeBorelMax_of_extra (hX : ExtraFacts Typ p Shape) : TypeBorelMax Typ p :=
  fun K _ _ hK S H hH => hX.maximal K hK S H hH

theorem typeII_normal_core_proof (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hK : TypeIIKFacts) (hX : ExtraFacts Typ p Shape) (hc : PointConfig Typ G p P M x J)
    (hfus : (P : Subgroup G) ≤ Subgroup.centralizer ({x} : Set G) ∧ U3LineWC x (P : Subgroup G)) :
    M ≤ Subgroup.normalizer ((u3T P x J ⊔ rankThreePrimeCore p M : Subgroup G) : Set G) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  exact u3_normal_core_proof_gen hS hD1 hU0 hK.inner hK.weak hK.heis hc hfus (typeII_T_structure hX hc)
    (typeII_S_decomp hX hc) (typeAutPCard_of_extra hX) (typeTorusIrred_of_extra hX) (typeTorusFpf_of_extra hX)
    (typeTorusOnCenter_of_extra hX) (typeBorelMax_of_extra hX)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

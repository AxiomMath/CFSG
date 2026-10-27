module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SevenFourMainDSetup

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding

namespace CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

open Involution SectionSix AschbacherToolkit CFSG.ABGLocalTools SectionSix.Exclusion

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}
  {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}

omit [Finite G] in
theorem commute_of_inf_trivial {S X L : Subgroup G}
    (htriv : ∀ c ∈ S, c ∈ L → c ∈ X → c = 1) {ρ x : G} (hρS : ρ ∈ S) (hρX : ρ ∈ X)
    (hρL : ρ ∈ Subgroup.normalizer (L : Set G)) (hxS : x ∈ S) (hxL : x ∈ L)
    (hxX : x ∈ Subgroup.normalizer (X : Set G)) : ρ * x = x * ρ := by
  have hcS : ρ * x * ρ⁻¹ * x⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem hρS hxS) (S.inv_mem hρS)) (S.inv_mem hxS)
  have hcL : ρ * x * ρ⁻¹ * x⁻¹ ∈ L :=
    L.mul_mem ((Subgroup.mem_normalizer_iff.mp hρL x).mp hxL) (L.inv_mem hxL)
  have hcX : ρ * x * ρ⁻¹ * x⁻¹ ∈ X := by
    have h1 : ρ * x * ρ⁻¹ * x⁻¹ = ρ * (x * ρ⁻¹ * x⁻¹) := by group
    rw [h1]
    exact X.mul_mem hρX ((Subgroup.mem_normalizer_iff.mp hxX _).mp (X.inv_mem hρX))
  have hc := htriv _ hcS hcL hcX
  calc ρ * x = (ρ * x * ρ⁻¹ * x⁻¹) * (x * ρ) := by group
    _ = x * ρ := by rw [hc, one_mul]

theorem eq_one_of_pRank_le_one {T X : Subgroup G} (hT : IsPGroup 2 T)
    (hTr : CFSG.Open.pRank 2 T ≤ 1) {t : G} (htT : t ∈ T) (ht2 : orderOf t = 2) (htX : t ∉ X) :
    ∀ c ∈ T, c ∈ X → c = 1 := by
  intro c hcT hcX
  by_contra hc1
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.mp hT) ⟨c, hcT⟩
  rw [Subgroup.orderOf_mk] at he
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at he
    exact hc1 he
  have hdvd : 2 ∣ orderOf c := by
    rw [he]
    exact dvd_pow_self 2 he0
  have hs2 : orderOf (c ^ (orderOf c / 2)) = 2 := orderOf_pow_orderOf_div (orderOf_pos c).ne' hdvd
  have hst := eq_of_pRank_le_one hT hTr (T.pow_mem hcT _) htT hs2 ht2
  exact htX (hst ▸ X.pow_mem hcX _)

namespace FieldHyps

variable {t g : G}

theorem commute_sylow (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) {m : Fin 2}
    (htm : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    {r : G} (hrA : r ∈ aschbacherThm5Preimage D (Abar i)) (hr2 : orderOf r = 2)
    (hrt : r * t = t * r)
    (hrnorm : ∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate D g)
        (conjFactors D Abar g k)).map (MulAut.conj r).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k))
    {S : Subgroup G} (hS : IsSylowOf 2 S (Subgroup.centralizer ({r} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)))
    {ρ x : G} (hρS : ρ ∈ S) (hρA : ρ ∈ aschbacherThm5Preimage D (Abar i))
    (hρL : ρ ∈ Subgroup.normalizer ((aschbacherThm5Preimage (rightConjugate D g)
      (conjFactors D Abar g m) : Subgroup G) : Set G))
    (hxS : x ∈ S) (hxL : x ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)) :
    ρ * x = x * ρ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC' := hC.conj g
  have hF' := hF.mirror hC hii' hrA hr2 hrt hrnorm
  have hS' : IsSylowOf 2 S (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({r} : Set G)) := by
    rw [inf_comm]
    exact hS
  have htS := (hF'.isSylowOf_inf_factor hin hC' htm hF.two hrt.symm hS').1
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hr2
    omega
  have hCr : Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    centralizer_le_of_mem_factor hC hrA (two_power_of_orderOf hr2) hr1
  have hTr : CFSG.Open.pRank 2 (S ⊓ aschbacherThm5Preimage (rightConjugate D g)
      (conjFactors D Abar g m)) ≤ 1 := by
    refine (CFSG.SectionRank.pRank_mono one_lt_two ?_).trans
      (hF'.pRank_factor_inf_centralizer_le_one hin hC' m)
    exact fun y hy => ⟨hy.2, (hS.le hy.1).1⟩
  have htriv := eq_one_of_pRank_le_one (hS.isPGroup.to_le inf_le_left) hTr ⟨htS, htm⟩ hF.two
    (hF.not_mem_D hin hC hii' hnd)
  exact commute_of_inf_trivial (fun c hcS hcL hcD => htriv c ⟨hcS, hcL⟩ hcD) hρS
    (preimage_le D _ hρA) hρL hxS hxL (hCr (hS.le hxS).1)

theorem commute_sylow' (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ∀ k : Fin 2, ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar k)) {j m : Fin 2}
    (hjm : j ≠ m)
    (htm : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    {r : G} (hrA : r ∈ aschbacherThm5Preimage D (Abar i)) (hr2 : orderOf r = 2)
    (hrt : r * t = t * r)
    (hrnorm : ∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate D g)
        (conjFactors D Abar g k)).map (MulAut.conj r).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k))
    {S : Subgroup G} (hS : IsSylowOf 2 S (Subgroup.centralizer ({r} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)))
    {τ y : G} (hτS : τ ∈ S)
    (hτL : τ ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    (hτA : τ ∈ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G))
    (hyS : y ∈ S) (hyA : y ∈ aschbacherThm5Preimage D (Abar i)) :
    τ * y = y * τ := by
  have hC' := hC.conj g
  have hF' := hF.mirror hC hii' hrA hr2 hrt hrnorm
  have hS' : IsSylowOf 2 S (Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({r} : Set G)) := by
    rw [inf_comm]
    exact hS
  have htnorm : ∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
      (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ k)).map
        (MulAut.conj t).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
        (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ k) := by
    intro k
    rw [preimage_conjFactors_inv]
    exact hF.norm k
  have hrm : r ∈ aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
      (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ i) := by
    rw [preimage_conjFactors_inv]
    exact hrA
  have hτA' : τ ∈ Subgroup.normalizer ((aschbacherThm5Preimage
      (rightConjugate (rightConjugate D g) g⁻¹)
      (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ i) : Subgroup G) :
        Set G) := by
    rw [preimage_conjFactors_inv]
    exact hτA
  have hyA' : y ∈ aschbacherThm5Preimage (rightConjugate (rightConjugate D g) g⁻¹)
      (conjFactors (rightConjugate D g) (conjFactors D Abar g) g⁻¹ i) := by
    rw [preimage_conjFactors_inv]
    exact hyA
  exact hF'.commute_sylow hin hC' hjm.symm (not_dihedral_conjFactor (hnd m) g) hrm htm hF.two
    hrt.symm htnorm hS' hτS hτL hτA' hyS hyA'

theorem inf_normalizer_le_other (hin : SectionSevenBase) (hC : Counterexample G D 2 Abar)
    (hF : FieldHyps D Abar t g) {i i' : Fin 2} (hii' : i ≠ i')
    (hnd : ¬ AschbacherKnownGroup.HasDihedralSylowTwo (Abar i)) {m : Fin 2}
    (htm : t ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    {r : G} (hrA : r ∈ aschbacherThm5Preimage D (Abar i)) (hr2 : orderOf r = 2)
    (hrt : r * t = t * r)
    (hrnorm : ∀ k : Fin 2, (aschbacherThm5Preimage (rightConjugate D g)
        (conjFactors D Abar g k)).map (MulAut.conj r).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g k))
    {S : Subgroup G} (hS : IsSylowOf 2 S (Subgroup.centralizer ({r} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)))
    {x : G} (hxS : x ∈ S)
    (hxL : x ∈ aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m))
    (hxA : x ∉ Subgroup.normalizer (aschbacherThm5Preimage D (Abar i) : Set G)) :
    S ⊓ aschbacherThm5Preimage D (Abar i) ⊓ Subgroup.normalizer
        ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
          Set G) ≤ aschbacherThm5Preimage D (Abar i') := by
  have hr1 : r ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hr2
    omega
  have hCr : Subgroup.centralizer ({r} : Set G) ≤ Subgroup.normalizer (D : Set G) :=
    centralizer_le_of_mem_factor hC hrA (two_power_of_orderOf hr2) hr1
  have hxH := hCr (hS.le hxS).1
  have hmap := map_eq_other_of_ne hC.hyp hxH hii'
    (fun h => hxA (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))
  rintro ρ ⟨⟨hρS, hρA⟩, hρL⟩
  have hcomm := hF.commute_sylow hin hC hii' hnd htm hrA hr2 hrt hrnorm hS hρS hρA hρL hxS hxL
  rw [← hmap]
  refine ⟨ρ, hρA, ?_⟩
  change x * ρ * x⁻¹ = ρ
  rw [← hcomm, mul_inv_cancel_right]

theorem commute_of_le_other (hC : Counterexample G D 2 Abar) {i i' : Fin 2} (hii' : i ≠ i')
    {j m : Fin 2} (hjm : j ≠ m) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
    (hR₀ : S ⊓ aschbacherThm5Preimage D (Abar i) ⊓ Subgroup.normalizer
        ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
          Set G) ≤ aschbacherThm5Preimage D (Abar i')) :
    ∀ a ∈ S ⊓ aschbacherThm5Preimage D (Abar i), ∀ b ∈ S ⊓ aschbacherThm5Preimage D (Abar i),
      a * b = b * a := by
  have hC' := hC.conj g
  have hcen : ∀ a ∈ S ⊓ aschbacherThm5Preimage D (Abar i), a ∈ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G) → ∀ b ∈ S ⊓ aschbacherThm5Preimage D (Abar i), a * b = b * a := by
    intro a ha haL b hb
    have haA' := hR₀ ⟨ha, haL⟩
    have h1 := cross_factor_centralizes D Abar hC.hyp.hcomm i i' hii' a haA' b hb.2
    have hmem : a⁻¹ * b⁻¹ * a * b ∈ S :=
      S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem ha.1) (S.inv_mem hb.1)) ha.1) hb.1
    have h2 := eq_one_of_mem_core_of_isPGroup hS2 hmem h1
    calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [h2, mul_one]
  intro a ha b hb
  by_cases haL : a ∈ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G)
  · exact hcen a ha haL b hb
  by_cases hbL : b ∈ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G)
  · exact (hcen b hb hbL a ha).symm
  have haK := hSK ha.1
  have hbK := hSK hb.1
  have hamap := map_eq_other_of_ne hC'.hyp haK hjm.symm
    (fun h => haL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))
  have hbmap := map_eq_other_of_ne hC'.hyp hbK hjm.symm
    (fun h => hbL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h))
  have hbinv : (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)).map
      (MulAut.conj b⁻¹).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j) := by
    apply map_eq_other_of_ne hC'.hyp (Subgroup.inv_mem _ hbK) hjm.symm
    intro h
    apply hbL
    have h1 := Subgroup.inv_mem _ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
    rwa [inv_inv] at h1
  have hajm : (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g j)).map
      (MulAut.conj a).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) := by
    apply map_eq_other_of_ne hC'.hyp haK hjm
    intro h
    exact haL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_other_of_map hC'.hyp haK hjm h))
  have hab' : (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)).map
      (MulAut.conj (a * b⁻¹)).toMonoidHom =
      aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) := by
    rw [map_conj_mul, hbinv, hajm]
  have hab : a * b⁻¹ ∈ Subgroup.normalizer
      ((aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Subgroup G) :
        Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hab'
  have habR : a * b⁻¹ ∈ S ⊓ aschbacherThm5Preimage D (Abar i) :=
    ⟨S.mul_mem ha.1 (S.inv_mem hb.1), Subgroup.mul_mem _ ha.2 (Subgroup.inv_mem _ hb.2)⟩
  have h1 := hcen _ habR hab b hb
  calc a * b = (a * b⁻¹) * b * b := by group
    _ = b * (a * b⁻¹) * b := by rw [h1]
    _ = b * a := by group

end FieldHyps

end CFSG.ComponentClassification.AschbacherTheorem5.SevenFour

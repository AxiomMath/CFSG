module

public import CFSG.GH74.GLS.IVK.Lifted.Tshape19
public import CFSG.GH74.GLS.IVK.Lifted.PGLQuot
public import CFSG.GH74.GLS.IVK.Lifted.CentSylow
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.Lifted.TwoGroups2

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm6 CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section HatCard

theorem card_hatImg_of_pgroup {G : Type} [Group G] [Finite G] {K S : Subgroup G} (hSK : S ≤ K)
    (hS : IsPGroup 2 ↥S) : Nat.card ↥(hatImg K S) = Nat.card ↥S := by
  have hS' : IsPGroup 2 ↥(S.subgroupOf K) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hinj := ComponentClassification.OddKernel.image_injective_on_two (hatMk K)
    (odd_card_ker_hatMk K) (S.subgroupOf K) hS'
  rw [hatImg_eq_map]
  have h1 : Nat.card ↥(S.subgroupOf K) = Nat.card ↥((S.subgroupOf K).map (hatMk K)) := by
    have := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.domRestrict_range] at this
    exact this
  rw [← h1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv

end HatCard

section Outer

variable {G : Type} [Group G] [Finite G] {z : G} {S K : Subgroup G}

theorem card_P_eq (h : Std6r1 G z S K) :
    Nat.card ↥(S ⊓ K) = 2 ^ (Nat.card (Hat K)).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg (std6r1_exists_sylow_P h)
  have h1 := Sylow.card_eq_multiplicity Pbar
  rw [hPbar, card_hatImg_of_pgroup inf_le_right ((std6r1_S_pgroup h).to_inf_left)] at h1
  exact h1

omit [Finite G] in
theorem exists_index_two_pair {P T₁ : Subgroup G} {y : G} (hT₁ : T₁ = P ⊔ zpowers y)
    (hyP : y ∉ P) (hyy : y * y = 1) (hyN : y ∈ normalizer (P : Set G)) :
    (P.subgroupOf T₁).index = 2 := by
  have hyT : y ∈ T₁ := hT₁ ▸ mem_sup_right (mem_zpowers y)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨y, hyT⟩, fun b => ?_⟩
  have hb : (b : G) ∈ P ⊔ zpowers y := hT₁ ▸ b.2
  have hcov := mem_or_mul_inv_mem hyN (by rw [hyy]; exact one_mem P) hb
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  rw [hyinv] at hcov
  show Xor ((b : G) * y ∈ P) ((b : G) ∈ P)
  rcases hcov with h1 | h1
  · refine Or.inr ⟨h1, fun h2 => hyP ?_⟩
    have := mul_mem (P.inv_mem h1) h2
    simpa using this
  · refine Or.inl ⟨h1, fun h2 => hyP ?_⟩
    have h3 : y = (b : G)⁻¹ * ((b : G) * y) := by group
    rw [h3]
    exact mul_mem (P.inv_mem h2) h1

theorem semidihedral_of_outer
    {F : Type} [Field F] [Finite F] (h : Std6r1 G z S K) {y : G}
    (hzS : z ∈ S) (hzK : z ∈ K) (hyS : y ∈ S) (hyy : y * y = 1) (hyR : y ∉ Rz S z)
    (hOK : HatOK (Hat K)) (hodd : Odd (Nat.card F))
    (e : Hat K ≃* SpecialLinearGroup (Fin 2) F) (θ : ↥(K ⊔ zpowers y) →* PGL2 F)
    (hker : θ.ker = (pPrimeCoreOf 2 K ⊔ zpowers z).subgroupOf (K ⊔ zpowers y)) :
    ∃ n, IVK.IsSemidihedralTwoGroup ↥(Pz S z ⊔ zpowers y) n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPz : Pz S z = S ⊓ K := std6r1_Pz_eq h
  rw [hPz]
  set P : Subgroup G := S ⊓ K with hPdef
  set T₁ : Subgroup G := P ⊔ zpowers y with hT₁
  have hyN : y ∈ normalizer (K : Set G) := std6r1_S_normalizes h hyS
  have hPR : P ≤ Rz S z := by
    rw [← hPz]
    exact le_sup_left
  have hyP : y ∉ P := fun hy => hyR (hPR hy)
  have hzP : z ∈ P := ⟨hzS, hzK⟩
  have hz2 : orderOf z = 2 := std6r1_orderOf_z h
  have hz1G : z ≠ 1 := ne_one_of_orderOf_eq_two hz2
  have hzzG : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hKC : K ≤ centralizer ({z} : Set G) := (std6r1_comp_isPCompIn h).1
  have hT₁S : T₁ ≤ S := sup_le inf_le_left (zpowers_le.2 hyS)
  have hT₁X : T₁ ≤ K ⊔ zpowers y := sup_le (inf_le_right.trans le_sup_left) le_sup_right
  have hPT₁ : P ≤ T₁ := le_sup_left
  have hT2 : IsPGroup 2 ↥T₁ := (std6r1_S_pgroup h).to_le hT₁S
  have hP2 : IsPGroup 2 ↥P := (std6r1_S_pgroup h).to_inf_left
  have hyPn : y ∈ normalizer (P : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro n hn
    exact std6r1_P_norm h hyS hn
  have hindex := exists_index_two_pair (P := P) (T₁ := T₁) hT₁ hyP hyy hyPn
  have hzT₁ : z ∈ T₁ := hPT₁ hzP
  have hyT₁ : y ∈ T₁ := mem_sup_right (mem_zpowers y)
  let π : ↥T₁ →* PGL2 F := θ.comp (Subgroup.inclusion hT₁X)
  let z' : ↥T₁ := ⟨z, hzT₁⟩
  let y' : ↥T₁ := ⟨y, hyT₁⟩
  have hz1 : z' ≠ 1 := fun h1 => hz1G (congrArg Subtype.val h1)
  have hzz : z' * z' = 1 := Subtype.ext hzzG
  have hSKmem : ∀ t : ↥T₁, ∀ ht : (t : G) ∈ pPrimeCoreOf 2 K ⊔ zpowers z, (t : G) ∈ S ⊓ K := by
    intro t ht
    obtain ⟨hxK, -⟩ := hatMk_of_mem_sup_zpowers hzK hz2 ht
    exact ⟨hT₁S t.2, hxK⟩
  have hker' : ∀ t : ↥T₁, π t = 1 ↔ t = 1 ∨ t = z' := by
    intro t
    have h1 : π t = 1 ↔ (t : G) ∈ pPrimeCoreOf 2 K ⊔ zpowers z := by
      show θ (Subgroup.inclusion hT₁X t) = 1 ↔ _
      rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
      rfl
    rw [h1]
    constructor
    · intro ht
      obtain ⟨hxK, hx⟩ := hatMk_of_mem_sup_zpowers hzK hz2 ht
      have hxSK := hSKmem t ht
      rcases hx with hx | hx
      · left
        apply Subtype.ext
        have := eq_of_hatMk_eq (inf_le_right : S ⊓ K ≤ K) hP2 hxSK (one_mem (S ⊓ K))
          (by rw [hx]; exact (map_one (hatMk K)).symm)
        exact this
      · right
        apply Subtype.ext
        exact eq_of_hatMk_eq (inf_le_right : S ⊓ K ≤ K) hP2 hxSK hzP hx
    · rintro (h2 | h2)
      · rw [h2]
        exact one_mem _
      · rw [h2]
        exact mem_sup_right (mem_zpowers z)
  have hcardHat : Nat.card (Hat K) = Nat.card (PGL2 F) := by
    rw [Nat.card_congr e.toEquiv, sl2_card_formula, pgl2_card_formula]
  have hQ : Nat.card ↥(P.subgroupOf T₁) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPT₁).toEquiv
  have hQcard : Nat.card ↥(P.subgroupOf T₁) * 2 = Nat.card ↥T₁ := by
    have := Subgroup.card_mul_index (P.subgroupOf T₁)
    rw [hindex] at this
    exact this
  have hcP : Nat.card ↥P = 2 ^ (Nat.card (Hat K)).factorization 2 := card_P_eq h
  have hcard : Nat.card ↥T₁ = 2 * 2 ^ (Nat.card (PGL2 F)).factorization 2 := by
    rw [← hQcard, hQ, hcP, hcardHat]
    ring
  have hzQ : z' ∈ P.subgroupOf T₁ := hzP
  have hno := noCommInv_of_pRank hOK.rank
  have hQu : ∀ x ∈ P.subgroupOf T₁, x * x = 1 → x = 1 ∨ x = z' := by
    intro x hxQ hxx
    have hxP : (x : G) ∈ P := hxQ
    have hxx' : (x : G) * (x : G) = 1 := congrArg Subtype.val hxx
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    right
    have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    have hord : orderOf (x : G) = 2 := orderOf_eq_two_of_mul_self_eq_one hxx' hx1'
    have hcomm : (x : G) * z = z * (x : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hKC hxP.2)
    exact Subtype.ext (eq_of_pRank_one (std6r1_comp_pRank h) hxP.2 hzK hord hz2 hcomm)
  have hzc : ∀ g : ↥T₁, g * z' = z' * g := by
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (std6r1_S_le_C h (hT₁S g.2))
  have hnoncomm : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
    obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg (std6r1_exists_sylow_P h)
    obtain ⟨ab, hab, bb, hbb, hne⟩ := sylow_exists_noncomm hOK.quasi hno Pbar
    rw [hPbar] at hab hbb
    obtain ⟨a, haP, rfl⟩ := mem_hatImg.1 hab
    obtain ⟨b, hbP, rfl⟩ := mem_hatImg.1 hbb
    refine ⟨(a : G), haP, (b : G), hbP, fun hc => hne ?_⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hc
  have hQnc : ∀ q₀ : ↥T₁, ¬ P.subgroupOf T₁ ≤ zpowers q₀ ⊔ zpowers z' := by
    intro q₀ hle
    obtain ⟨a, haP, b, hbP, hne⟩ := hnoncomm
    apply hne
    have ha : (⟨a, hPT₁ haP⟩ : ↥T₁) ∈ P.subgroupOf T₁ := haP
    have hb : (⟨b, hPT₁ hbP⟩ : ↥T₁) ∈ P.subgroupOf T₁ := hbP
    have := IVK.mul_comm_of_mem_zpowers_sup hzc (hle ha) (hle hb)
    exact congrArg Subtype.val this
  have hres := tshape_of_pgl_hom hT2 hodd π hz1 hzz hker' hcard (P.subgroupOf T₁) hzQ hQcard hQu
    hQnc
  rcases hres with ⟨n, hn3, ⟨ι⟩⟩ | hsd
  · exfalso
    have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    have hy1 : y' ≠ 1 := fun h1 => hyP (by
      have : y = 1 := congrArg Subtype.val h1
      rw [this]
      exact one_mem P)
    have hy'y : y' * y' = 1 := Subtype.ext hyy
    have h1 := quat_invol (2 ^ (n - 2)) (ι y') (by rw [← map_mul, hy'y, map_one])
      (fun h => hy1 (ι.injective (by rw [h, map_one])))
    have h2 := quat_invol (2 ^ (n - 2)) (ι z') (by rw [← map_mul, hzz, map_one])
      (fun h => hz1 (ι.injective (by rw [h, map_one])))
    have hzy : z' = y' := ι.injective (h2.trans h1.symm)
    have hzy' : z = y := congrArg Subtype.val hzy
    exact hyP (hzy' ▸ hzP)
  · exact hsd

theorem ivk_1_9_outer_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) (hII : II4_4_4_center) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_1_9_outer := by
  intro G _ _ z S K h y hyS hy2 hyR hyF
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK := std6_hatOK h44 h.toStd6 (std6r1_comp_rigid h)
  have hzSK := std6r1_z_mem_S_zStar hII h
  have hzS : z ∈ S := hzSK.1
  have hzK : z ∈ K := hzSK.2.1
  have hKC : K ≤ centralizer ({z} : Set G) := (std6r1_comp_isPCompIn h).1
  have hz2 : orderOf z = 2 := std6r1_orderOf_z h
  have hcen : Nat.card (Subgroup.center (Hat K)) = 2 := hOK.sl2.2
  have hyN : y ∈ normalizer (K : Set G) := std6r1_S_normalizes h hyS
  have hyy : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy2, sq] at this
  have hφ2 : phi K y hyN * phi K y hyN = 1 := phi_mul_self K hyN hyy
  have hZ : ∀ x ∈ Subgroup.center (Hat K), x * x = 1 := sq_eq_one_of_card_center hcen
  have hyin : ¬ InducesInner y K := by
    intro hin
    obtain ⟨k₀, hk₀, hk⟩ := std6r1_lift_inner h hZ hyS hin
    apply hyR
    rw [std6r1_Rz_eq h]
    have e1 : y = (y * k₀⁻¹) * k₀ := by group
    rw [e1]
    exact mul_mem (mem_sup_right hk) (mem_sup_left hk₀)
  have hwin' : ¬ phi K y hyN ∈ innOf (Hat K) := fun hh => hyin ((phi_mem_inn_iff K hyN).1 hh)
  rcases sl_or_a7 hOK.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨e⟩⟩ | h7
  · have hα2 : MulAut.congr e (phi K y hyN) * MulAut.congr e (phi K y hyN) = 1 := by
      rw [← map_mul, hφ2, map_one]
    have hσ : (gammaOf hodd h3 (MulAut.congr e (phi K y hyN))).right = 1 := by
      by_contra hσ
      apply hyF
      refine ⟨hyN, ?_⟩
      exact ⟨hOK.quasi, hOK.kgrp, hOK.rank, exists_pow_two_orderOf hφ2,
        fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 hσ)⟩
    obtain ⟨θ, hsurj, hker⟩ := exists_pgl_hom hodd h3 e hzK hKC hz2 hcen hyN hyy hwin' hσ
    exact ⟨semidihedral_of_outer h hzS hzK hyS hyy hyR hOK hodd e θ hker, F, hFf, hFin, hodd,
      ⟨e.trans (specialLinearGroupEquivStatedSL 2 F)⟩,
      exists_pglQuot hodd h3 e hzK hKC hz2 hcen hyN hyy hwin' hσ⟩
  · exfalso
    exact hyF ⟨hyN, (h2A7 _ h7).2.2.1 _ hφ2 hwin' hOK.kgrp⟩

end Outer

end CFSG.GH74.GLS.IVK.Lifted

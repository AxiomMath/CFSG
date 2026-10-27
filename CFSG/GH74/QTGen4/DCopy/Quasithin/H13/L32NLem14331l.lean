module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14331k
public import CFSG.Quasithin.H13.A5S1327h
public import CFSG.Quasithin.H13.L32NLem14331j

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace L14328

open L14331

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14328.Ctx_F4

variable {g z b l : G} (C : Ctx_F4 G T L V V₂ g z b l) (D : HatModelU (fsuU T V)) {e : G}
include C

theorem caseI_not_caseThree_F4 (h1434 : Lemma1434One_F4) (hL2 : A5.FactL2Three)
    (X : CaseI_F4 T L V g D e) {H₁ H₂ : Subgroup (dQ T L V l e)}
    (h3 : F6.IsF618CaseThree H₁ H₂) : False := by
  obtain ⟨p, K', Zc, hp, hp24, hK'L2, hZc3, hsup, hinf, hcomm, -⟩ := h3
  obtain ⟨hq, h60, h4⟩ := hL2 p ↥K' hp hp24 hK'L2
  have hsimp : IsSimpleGroup ↥K' := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 p 1 hK'L2).2
  set π := piQ T L V l e with hπ
  have hsup' : K' ⊔ Zc = oTwoUpper (⊤ : Subgroup (dQ T L V l e)) := by
    rw [hsup, twoResidual_eq_oTwoUpper']
  have hO2n : (oTwoUpper (⊤ : Subgroup (dQ T L V l e))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr (le_normalizer_oTwoUpper ⊤))
  have hK'N : oTwoUpper (⊤ : Subgroup (dQ T L V l e)) ≤ Subgroup.normalizer (K' : Set _) :=
    hsup' ▸ A5.sup_le_normalizer_of_comm hcomm

  have hK'le : K' ≤ oTwoUpper (⊤ : Subgroup (dQ T L V l e)) := hsup' ▸ le_sup_left
  have hK'c : K' ∈ cComp (⊤ : Subgroup (dQ T L V l e)) :=
    mem_cComp_top_of_isComponent ⟨hq, Subgroup.IsSubnormal.step K' _ hK'le hO2n.isSubnormal
      (Subgroup.normal_subgroupOf_of_le_normalizer hK'N)⟩

  have htriple := C.caseI_triple_F4 D X
  obtain ⟨K₀, hK₀, hK₀K'⟩ :=
    (cComp_quotient_bijOn _ htriple.isSolvable_pPrimeCore).2.2 hK'c

  obtain ⟨y, hyK, hyI, u₁, u₂, hy3, -, -, h21, hne, x, hxU, hxI, hx⟩ := C.caseI_exists_ubar_F4 D X
  have hw := w_mem_oTwoUpper hy3 h21
  obtain ⟨k, hk⟩ := C.caseI_w_two_pow_F4 hxU hxI
  rw [hx] at hk
  have hwK' : u₂ * u₁⁻¹ ∈ K' :=
    A5.mem_of_mem_sup_of_two_pow hcomm hZc3 hinf (hsup' ▸ hw) hk

  have hZ : ⁅quasithinOmegaOneCenter T, K₀.map (iKP T L V l e).subtype⁆ ≠ ⊥ := by
    intro hb
    have hzZ : z ∈ quasithinOmegaOneCenter T := (Subgroup.mem_inf.mp C.z_mem).2

    have hK₀H : ∀ k₀ ∈ K₀, ((k₀ : ↥(iKP T L V l e)) : G) ∈ l32nH T V := by
      intro k₀ hk₀
      refine C.mem_normalizer_V1_F4 ?_
      have h1 := Subgroup.commutator_mem_commutator hzZ
        (Subgroup.mem_map_of_mem (iKP T L V l e).subtype hk₀)
      rw [hb, Subgroup.mem_bot, commutatorElement_def] at h1
      have h1' : z * (k₀ : G) * z⁻¹ * (k₀ : G)⁻¹ = 1 := h1
      calc (k₀ : G) * z * (k₀ : G)⁻¹ = (z * (k₀ : G) * z⁻¹ * (k₀ : G)⁻¹)⁻¹ * z := by group
        _ = z := by rw [h1', inv_one, one_mul]

    set Kb := ((kA T V (l⁻¹ * e * l)).subgroupOf (iKP T L V l e)).map π with hKb
    have hKs : Group.IsSolvable ↥Kb := by
      have h1 := C.caseI_isSolvable_K_F4 D X
      have hKI : kA T V (l⁻¹ * e * l) ≤ iKP T L V l e := le_sup_left.trans le_sup_left
      have h2 : Group.IsSolvable ↥((kA T V (l⁻¹ * e * l)).subgroupOf (iKP T L V l e)) :=
        Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.subgroupOfEquivOfLe hKI).toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hKI).injective
      exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)

    have hbot : ∀ c ∈ Kb, c ∈ K' → c = 1 := by
      have hn : ((Kb ⊓ K').subgroupOf K').Normal := by
        constructor
        intro c hc k'
        rw [Subgroup.mem_subgroupOf] at hc ⊢
        have hk' : (k' : dQ T L V l e) ∈ K₀.map π := hK₀K'.symm ▸ k'.2
        obtain ⟨k₀, hk₀, hk₀'⟩ := hk'
        refine ⟨?_, K'.mul_mem (K'.mul_mem k'.2 hc.2) (K'.inv_mem k'.2)⟩
        obtain ⟨c₀, hc₀, hc₀'⟩ := hc.1
        refine ⟨k₀ * c₀ * k₀⁻¹, ?_, ?_⟩
        · have hc₀G : ((c₀ : ↥(iKP T L V l e)) : G) ∈ kA T V (l⁻¹ * e * l) := hc₀
          show ((k₀ * c₀ * k₀⁻¹ : ↥(iKP T L V l e)) : G) ∈ kA T V (l⁻¹ * e * l)
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_kA _ (hK₀H k₀ hk₀)) _).mp hc₀G
        · rw [map_mul, map_mul, map_inv, hk₀', hc₀']
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rcases hn.eq_bot_or_eq_top with h | h
      · intro c hc hcK'
        have : (⟨c, hcK'⟩ : ↥K') ∈ (Kb ⊓ K').subgroupOf K' :=
          Subgroup.mem_subgroupOf.mpr ⟨hc, hcK'⟩
        rw [h, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      · exfalso
        have hle : K' ≤ Kb := fun k hk => by
          have : (⟨k, hk⟩ : ↥K') ∈ (Kb ⊓ K').subgroupOf K' := by rw [h]; exact Subgroup.mem_top _
          exact (Subgroup.mem_subgroupOf.mp this).1
        have : Group.IsSolvable ↥K' :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
        have hcomm' := IsSimpleGroup.comm_iff_isSolvable.mpr this
        obtain ⟨-, -, a, b', hab⟩ := hq
        obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨b'', rfl⟩ := QuotientGroup.mk_surjective b'
        exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm' a' b''])

    have hyN : π ⟨y, hyI⟩ ∈ Subgroup.normalizer (K' : Set (dQ T L V l e)) :=
      hK'N (mem_oTwoUpper_of_odd (Subgroup.mem_top _)
        (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hy3)))
    have hyK' : ∀ k' ∈ K', π ⟨y, hyI⟩ * k' = k' * π ⟨y, hyI⟩ := by
      intro k' hk'
      rw [← hK₀K'] at hk'
      obtain ⟨k₀, hk₀, rfl⟩ := hk'
      have hcK : y * (k₀ : G) * y⁻¹ * (k₀ : G)⁻¹ ∈ kA T V (l⁻¹ * e * l) := by
        have h1 : (k₀ : G) * y⁻¹ * (k₀ : G)⁻¹ ∈ kA T V (l⁻¹ * e * l) :=
          (Subgroup.mem_normalizer_iff.mp (le_normalizer_kA _ (hK₀H k₀ hk₀)) _).mp
            ((kA T V (l⁻¹ * e * l)).inv_mem hyK)
        rw [show y * (k₀ : G) * y⁻¹ * (k₀ : G)⁻¹ = y * ((k₀ : G) * y⁻¹ * (k₀ : G)⁻¹) by group]
        exact (kA T V (l⁻¹ * e * l)).mul_mem hyK h1
      set c : ↥(iKP T L V l e) := ⟨y, hyI⟩ * k₀ * (⟨y, hyI⟩)⁻¹ * k₀⁻¹ with hc
      have hcKb : π c ∈ Kb := ⟨c, Subgroup.mem_subgroupOf.mpr hcK, rfl⟩
      have hcbar : π c = π ⟨y, hyI⟩ * π k₀ * (π ⟨y, hyI⟩)⁻¹ * (π k₀)⁻¹ := by
        rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hk₀K' : π k₀ ∈ K' := hK₀K' ▸ Subgroup.mem_map_of_mem π hk₀
      have hcK' : π c ∈ K' := by
        rw [hcbar]
        exact K'.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN _).mp hk₀K') (K'.inv_mem hk₀K')
      have h1 := hbot _ hcKb hcK'
      rw [hcbar] at h1
      calc π ⟨y, hyI⟩ * π k₀ =
          (π ⟨y, hyI⟩ * π k₀ * (π ⟨y, hyI⟩)⁻¹ * (π k₀)⁻¹) * (π k₀ * π ⟨y, hyI⟩) := by group
        _ = π k₀ * π ⟨y, hyI⟩ := by rw [h1, one_mul]

    exact hne (eq_one_of_comm_w hy3 h21 (hyK' _ hwK') hk)

  obtain ⟨hs, hcard⟩ := C.caseI_K0_simple_F4 D h1434 X hK₀ hZ
  have h3dvd : 3 ∣ Nat.card (↥K₀ ⧸ CFSG.Open.pCore 2 ↥K₀) := by
    rcases hcard with h | h <;> rw [h] <;> norm_num
  obtain ⟨b, hb⟩ := card_map_of_simple CFSG.pPrimeCore_coprime_card K₀ hs h3dvd
  rw [hK₀K'] at hb
  rcases hcard with h | h
  · exact h60 b (by rw [hb, h])
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥K') 2 (n := 3) (by
      rw [hb, h]
      exact Dvd.intro (21 * 2 ^ b) (by ring))
    have := h4 P (IsPGroup.of_card hP)
    rw [hP] at this
    norm_num at this

end Ctx_F4

end L14328

end CFSG.Quasithin.H13

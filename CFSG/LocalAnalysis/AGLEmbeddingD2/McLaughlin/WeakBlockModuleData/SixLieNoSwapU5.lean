module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieU5Swap
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieHP
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieInvLine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieTransfer

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
  CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.BorelTits
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LocalAnalysis.RankThreeTheoremC
open CFSG.Open (pCoreOf IsElemAbelian)

theorem noSwap_of_psu_five {G : Type} [Group G] [Finite G] {M S L : Subgroup G}
    (hL : IsWeakSBlock M S L)
    (hpar : IsParabolicTwo (barM M L) (barM M (Subgroup.normalizer (S : Set G) ⊓ L)))
    (hsolv : BlockPLThreeSolv M S L)
    (hc : StatedClassicalModel (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) .PSU 5 2 1)
    (hZ3 : Nat.Coprime 3 (Nat.card (Subgroup.center ↥(barM M L))))
    {E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hEel : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hEP : E ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L))
    (h9 : ∀ T : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      T ≤ barM M (Subgroup.normalizer (S : Set G) ⊓ L) → IsPGroup 3 T → Nat.card T ≤ 9) :
    ¬ IrreducibleOn
      (Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer
          (barM M (Subgroup.normalizer (S : Set G) ⊓ L) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) E := by
  classical
  intro hirr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lb := barM M L with hLb
  set P := barM M (Subgroup.normalizer (S : Set G) ⊓ L) with hP
  have hPL : P ≤ Lb := barM_mono inf_le_right
  have hE3 : IsPGroup 3 E := isPGroup_of_isElemAbelian hEel
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb) with hρ
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hEL : E ≤ Lb := hEP.trans hPL
  set E' : Subgroup ↥Lb := E.subgroupOf Lb with hE'
  set P' : Subgroup ↥Lb := P.subgroupOf Lb with hP'
  have hE'3 : IsPGroup 3 E' := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEL).symm
  have hinj : ∀ x ∈ E', ρ x = 1 → x = 1 := by
    intro x hx hx1
    have hxc : x ∈ Subgroup.center ↥Lb := (QuotientGroup.eq_one_iff x).mp hx1
    obtain ⟨k, hk⟩ := hE'3 ⟨x, hx⟩
    have h3 : orderOf x ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card (Subgroup.center ↥Lb) := Subgroup.orderOf_dvd_natCard _ hxc
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hZ3) h3 h2)
  have hcardE : Nat.card (E'.map ρ) = 9 := by
    rw [card_map_eq_of_inj_on ρ hinj, hE', ← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  have hEJ : E'.map ρ ≤ P'.map ρ :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hEP (Subgroup.mem_subgroupOf.mp hx))
  by_cases hsyl : IsSylowTwoOf (pCoreOf 2 P) Lb
  ·
    have hT' : IsSylowTwoOf ((pCoreOf 2 P).subgroupOf Lb) ⊤ := by
      have := L246C127.isSylowTwoOf_top_map_subgroupOf (MulEquiv.refl ↥Lb) hsyl
      simpa using this
    obtain ⟨S2, hS2⟩ := exists_sylow_of_isSylowTwoOf_top hT'
    have hPN : P' ≤ Subgroup.normalizer ((S2 : Subgroup ↥Lb) : Set ↥Lb) := by
      intro x hx
      rw [hS2, Subgroup.mem_normalizer_iff]
      intro z
      have hx' := Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 P
        (Subgroup.mem_subgroupOf.mp hx)) (z : ↥M ⧸ CFSG.pCore 2 ↥M)
      simpa [Subgroup.mem_subgroupOf] using hx'
    set Tb : Sylow 2 (↥Lb ⧸ Subgroup.center ↥Lb) := S2.mapSurjective hρs with hTb
    have hTbc : (Tb : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)) = (S2 : Subgroup ↥Lb).map ρ :=
      Sylow.coe_mapSurjective hρs S2
    have hEN : E'.map ρ ≤ Subgroup.normalizer ((Tb : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)) : Set (↥Lb ⧸ Subgroup.center ↥Lb)) := by
      rw [hTbc]
      exact hEJ.trans ((Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map ρ))
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
      intro x hx y hy
      have := hEel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    have hsq : ∀ n ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (P : Set (↥M ⧸ CFSG.pCore 2 ↥M)) ⊓
        Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)), ∀ x ∈ E,
        n * n * x * (n * n)⁻¹ = x := by
      intro n hn x hx
      have hnE : n ∈ Subgroup.normalizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn).1).1
      have hnP : n ∈ Subgroup.normalizer (P : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn).1).2
      have hnL : n ∈ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        (Subgroup.mem_inf.mp hn).2
      obtain ⟨ψ, hψ⟩ := exists_inducedAut hnL
      obtain ⟨a, ha⟩ := autSqInner_psu_five hc ψ
      have hψρ : ∀ y : ↥Lb, ψ (ρ y) = ρ (conjOnNormalizer Lb n hnL y) := hψ
      have hnR : n ∈ Subgroup.normalizer ((pCoreOf 2 P : Subgroup _) : Set _) :=
        normalizer_le_normalizer_pCoreOf 2 P hnP
      have hψT : ∀ t ∈ (Tb : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)), ψ t ∈ (Tb : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)) := by
        intro t ht
        rw [hTbc] at ht ⊢
        obtain ⟨s, hs, rfl⟩ := ht
        rw [hψρ]
        refine ⟨conjOnNormalizer Lb n hnL s, ?_, rfl⟩
        have hs1 : s ∈ (pCoreOf 2 P).subgroupOf Lb := hS2 ▸ hs
        have hs2 : (s : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ pCoreOf 2 P := Subgroup.mem_subgroupOf.mp hs1
        have hs3 : (conjOnNormalizer Lb n hnL s : ↥Lb) ∈ (pCoreOf 2 P).subgroupOf Lb :=
          Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hnR _).mp hs2)
        show _ ∈ (S2 : Subgroup ↥Lb)
        rw [hS2]; exact hs3
      have hψE : ∀ t ∈ E'.map ρ, ψ t ∈ E'.map ρ := by
        rintro _ ⟨s, hs, rfl⟩
        rw [hψρ]
        refine ⟨conjOnNormalizer Lb n hnL s, ?_, rfl⟩
        have hs2 : (s : ↥M ⧸ CFSG.pCore 2 ↥M) ∈ E := Subgroup.mem_subgroupOf.mp hs
        show _ ∈ E'
        exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp hnE _).mp hs2)
      have haT : a ∈ Subgroup.normalizer ((Tb : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)) : Set (↥Lb ⧸ Subgroup.center ↥Lb)) := by
        refine Subgroup.mem_normalizer_fintype fun t ht => ?_
        rw [← ha]
        exact hψT _ (hψT _ ht)
      have haE : ∀ e ∈ E'.map ρ, a * e * a⁻¹ ∈ E'.map ρ := fun e he => by
        rw [← ha]
        exact hψE _ (hψE _ he)
      have hcent : ∀ e ∈ E'.map ρ, a * e * a⁻¹ = e := by
        intro e he
        have h1 := comm_mem_of_le_normalizer_psu_five hc Tb (y := a⁻¹) (z := e⁻¹)
          (Subgroup.inv_mem _ haT) (Subgroup.inv_mem _ (hEN he))
        have h2 : e * (a * e⁻¹ * a⁻¹) ∈ E'.map ρ :=
          (E'.map ρ).mul_mem he (by
            have e1 : a * e⁻¹ * a⁻¹ = (a * e * a⁻¹)⁻¹ := by group
            rw [e1]
            exact (E'.map ρ).inv_mem (haE e he))
        have h3 : e * a * e⁻¹ * a⁻¹ ∈ (E'.map ρ ⊓ (Tb : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)) : Subgroup _) := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · have e1 : e * a * e⁻¹ * a⁻¹ = e * (a * e⁻¹ * a⁻¹) := by group
            rw [e1]; exact h2
          · have e1 : e * a * e⁻¹ * a⁻¹ = e⁻¹⁻¹ * a⁻¹⁻¹ * e⁻¹ * a⁻¹ := by group
            rw [e1]; exact h1
        have hbot : (E'.map ρ ⊓ (Tb : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)) : Subgroup _) = ⊥ := by
          have hE3' : IsPGroup 3 (E'.map ρ) := hE'3.map ρ
          rw [Subgroup.eq_bot_iff_forall]
          intro v hv
          obtain ⟨k, hk⟩ := hE3' ⟨v, (Subgroup.mem_inf.mp hv).1⟩
          obtain ⟨m, hm⟩ := (Tb.isPGroup' (G := ↥Lb ⧸ Subgroup.center ↥Lb))
            ⟨v, (Subgroup.mem_inf.mp hv).2⟩
          have h3' : orderOf v ∣ 3 ^ k :=
            orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
          have h2' : orderOf v ∣ 2 ^ m :=
            orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hm)
          exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
            (Nat.Coprime.pow k m (by norm_num : Nat.Coprime 3 2)) h3' h2')
        rw [hbot, Subgroup.mem_bot] at h3
        have h5 := mul_inv_eq_one.mp h3
        have h4 : e * a = a * e := mul_inv_eq_iff_eq_mul.mp h5
        calc a * e * a⁻¹ = e * a * a⁻¹ := by rw [← h4]
          _ = e := by group
      set x' : ↥Lb := ⟨x, hEL hx⟩ with hx'
      have hxE' : x' ∈ E' := Subgroup.mem_subgroupOf.mpr hx
      have hnx : conjOnNormalizer Lb n hnL x' = ⟨n * x * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnL x).mp
        (hEL hx)⟩ := rfl
      have hnnx : ((conjOnNormalizer Lb n hnL (conjOnNormalizer Lb n hnL x') : ↥Lb) :
          ↥M ⧸ CFSG.pCore 2 ↥M) = n * n * x * (n * n)⁻¹ := by
        show n * (n * x * n⁻¹) * n⁻¹ = n * n * x * (n * n)⁻¹
        group
      have hy' : conjOnNormalizer Lb n hnL (conjOnNormalizer Lb n hnL x') ∈ E' := by
        rw [Subgroup.mem_subgroupOf, hnnx]
        have h1 := (Subgroup.mem_normalizer_iff.mp hnE x).mp hx
        have h2 := (Subgroup.mem_normalizer_iff.mp hnE _).mp h1
        simpa [mul_assoc] using h2
      have hρeq : ρ (conjOnNormalizer Lb n hnL (conjOnNormalizer Lb n hnL x')) = ρ x' := by
        have h1 : ψ (ψ (ρ x')) = ρ (conjOnNormalizer Lb n hnL (conjOnNormalizer Lb n hnL x')) := by
          rw [hψρ, hψρ]
        rw [← h1, ha, hcent _ ⟨x', hxE', rfl⟩]
      have hz : conjOnNormalizer Lb n hnL (conjOnNormalizer Lb n hnL x') * x'⁻¹ = 1 := by
        refine hinj _ (E'.mul_mem hy' (E'.inv_mem hxE')) ?_
        rw [map_mul, map_inv, hρeq, mul_inv_cancel]
      have := congrArg Subtype.val (mul_inv_eq_one.mp hz)
      rw [hnnx] at this
      simpa [hx'] using this
    obtain ⟨W, hWE, hW3, hWN⟩ := exists_line_of_sq_trivial hE9 hcomm
      (inf_le_left.trans inf_le_left) hsq
    rcases hirr W hWE hWN with h | h
    · rw [h, Subgroup.card_bot] at hW3
      omega
    · rw [h, hE9] at hW3
      omega
  ·
    obtain ⟨T0, hT0, hNJ, hJne, hJperf⟩ := exists_overgroup_quotient_map _ _ hpar hsyl hsolv
    obtain ⟨T', hT'⟩ := exists_sylow_of_isSylowTwoOf_top hT0
    rw [← hT'] at hNJ hJne
    obtain ⟨-, F, hFf, hFfin, hcard, ⟨e⟩⟩ := id hc
    have := Fintype.ofFinite F
    have : CharP F 2 := charP_of_card_eq_prime_pow (f := 1 * 2)
      (by rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
    have h3 := three_le_pRank_su_five hcard e T' _ hNJ hJne hJperf
    rw [pRank_image_eq Lb P hPL hZ3] at h3
    obtain ⟨E27, hE27P, hE27, hE27c⟩ := exists_elemAbelian_of_le_pRank (p := 3) h3 (by norm_num)
    have := h9 E27 hE27P (isPGroup_of_isElemAbelian hE27)
    omega

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

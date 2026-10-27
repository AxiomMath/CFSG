module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K5192P2PB
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A10GenJ2
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.QuasithinUnique KFactsPair
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.GN

private theorem mem_of_odd_of_mem_sup_pGroup {G : Type*} [Group G] [Finite G] {H E : Subgroup G}
    (hE : IsPGroup 2 E) (hEH : E ≤ Subgroup.normalizer (H : Set G)) {x : G} (hx : x ∈ H ⊔ E)
    (hodd : Odd (orderOf x)) : x ∈ H := by
  have hx' : x ∈ ((E ⊔ H : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right E H hEH, Set.mem_mul] at hx'
  obtain ⟨o, ho, c, hc, rfl⟩ := hx'
  exact CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.mem_of_odd_eq_two_mul
    ((Subgroup.normalizer (H : Set G)).mul_mem (hEH ho) (Subgroup.le_normalizer hc)) (hEH ho) hc
    rfl hodd (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_orderOf_two_pow hE ho)

private theorem eq_of_isSubnormal_of_le_sup_pGroup {G : Type*} [Group G] [Finite G]
    {E H K : Subgroup G} (hE : IsPGroup 2 E) (hsub : IsSubnormal H K) (hEK : E ≤ K)
    (hKodd : K ≤ Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)}) (hcov : K ≤ H ⊔ E) :
    H = K := by
  induction hsub with
  | refl => rfl
  | @step H M K hHM hnorm _ ih =>
    have hMK : M = K := ih hEK hKodd (hcov.trans (sup_le_sup_right hHM E))
    subst hMK
    have hMN : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).1 hnorm
    refine le_antisymm hHM (hKodd.trans ((Subgroup.closure_le H).2 fun x hx => ?_))
    exact mem_of_odd_of_mem_sup_pGroup hE (hEK.trans hMN) (hcov hx.1) hx.2

private theorem normalizer_le_normalizer_oddHull {Y : Type} [Group Y] [Finite Y]
    (P : Subgroup Y) :
    Subgroup.normalizer (P : Set Y) ≤ Subgroup.normalizer (oddHull P : Set Y) := by
  refine le_normalizer_of_closure_odd
    (Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩)
    fun g hg x hx hodd => Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hg x).1
      ((Subgroup.closure_le P).2 (fun y hy => hy.1) hx), ?_⟩
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa using this.symm ▸ hodd

theorem eq_oddHull_of_isSubnormal {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y}
    (hP : IsTwoFourSFive P) {H : Subgroup Y} (hsub : IsSubnormal H (oddHull P))
    (hodd : H ≤ Subgroup.closure {x : Y | x ∈ H ∧ Odd (orderOf x)}) (hne : H ≠ ⊥) :
    H = oddHull P := by
  obtain ⟨ψ, hψ, hker⟩ := exists_alt_five_of_isTwoFourSFive hP
  have hE2 : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hHK : H ≤ oddHull P := hsub.le
  have hsn : IsSubnormal ((H.subgroupOf (oddHull P)).map ψ) ⊤ := by
    have h1 : IsSubnormal (H.subgroupOf (oddHull P)) ((oddHull P).subgroupOf (oddHull P)) :=
      hsub.comap (oddHull P).subtype
    rw [Subgroup.subgroupOf_self] at h1
    have h2 := h1.map ψ
    rwa [Subgroup.map_top_of_surjective ψ hψ] at h2
  haveI := alternatingGroup.isSimpleGroup_five
  rcases hsn.eq_bot_or_top with hbot | htop
  · refine absurd (le_bot_iff.1 (hodd.trans ((Subgroup.closure_le _).2 fun x hx => ?_))) hne
    have h1 : ψ ⟨x, hHK hx.1⟩ ∈ (H.subgroupOf (oddHull P)).map ψ := ⟨⟨x, hHK hx.1⟩, hx.1, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    obtain ⟨k, hk⟩ :=
      CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.exists_orderOf_two_pow hE2 ((hker _).1 h1)
    have hk0 : k = 0 := by
      by_contra h0
      have h2 : Even (orderOf x) := hk ▸ Nat.even_pow.2 ⟨even_two, h0⟩
      exact Nat.not_even_iff_odd.2 hx.2 h2
    rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
    exact Subgroup.mem_bot.2 hk
  · refine eq_of_isSubnormal_of_le_sup_pGroup (E := pCoreOf 2 P ⊓ oddHull P)
      (hE2.to_le inf_le_left) hsub inf_le_right
      (Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩) fun k hk => ?_
    obtain ⟨h, hh, hψh⟩ : ψ ⟨k, hk⟩ ∈ (H.subgroupOf (oddHull P)).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    have h1 : ψ (h⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hψh, inv_mul_cancel]
    rw [show k = (h : Y) * ((h⁻¹ * ⟨k, hk⟩ : ↥(oddHull P)) : Y) by simp]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hh) ⟨(hker _).1 h1, (h⁻¹ * ⟨k, hk⟩).2⟩

theorem exists_ne_comm_of_isTwoFourSFive {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y}
    (hP : IsTwoFourSFive P) (ρ : ↥P →* Equiv.Perm (Fin 10)) (hρ : Function.Injective ρ) :
    ∃ x ∈ oddHull P, ∃ y ∈ pCoreOf 2 P, x * y ≠ y * x := by
  obtain ⟨-, h16, ⟨e⟩⟩ := hP
  have hE16 : Nat.card (CFSG.pCore 2 ↥P) = 16 := by
    unfold CFSG.Open.pCoreOf at h16
    rwa [Subgroup.card_map_of_injective Subtype.val_injective] at h16
  have h5 : 5 ∣ Nat.card ↥P := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥P),
      Nat.card_congr e.toEquiv]
    refine Dvd.dvd.mul_right ?_ _
    rw [Nat.card_perm, Nat.card_fin]
    exact Nat.dvd_factorial (by norm_num) le_rfl
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 5 h5
  have hx5 : x ^ 5 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    omega
  have hfree := A10GenJ2.free_of_perm ρ hρ (CFSG.pCore 2 ↥P) hE16 x hx5 hx1
    fun g hg => (inferInstance : (CFSG.pCore 2 ↥P).Normal).conj_mem g hg x
  obtain ⟨g, hg, hg1⟩ : ∃ g ∈ CFSG.pCore 2 ↥P, g ≠ 1 := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_bot_iff_forall _).2 h, Subgroup.card_bot] at hE16
    omega
  refine ⟨x, Subgroup.subset_closure ⟨x.2, ?_⟩, g, ⟨g, hg, rfl⟩, fun hc => hg1 (hfree g hg ?_)⟩
  · rw [Subgroup.orderOf_coe, hx]
    exact ⟨2, by norm_num⟩
  · rw [show x * g = g * x from Subtype.ext hc, mul_inv_cancel_right]

theorem noXBlock_oddHull_sup {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {P S : Subgroup (X ⧸ gnC T)} (hP : IsTwoFourSFive P)
    (hnc : ∃ x ∈ oddHull P, ∃ y ∈ pCoreOf 2 P, x * y ≠ y * x) (hS : IsPGroup 2 S)
    (hSP : S ≤ Subgroup.normalizer (P : Set (X ⧸ gnC T))) :
    ∀ B : Subgroup X, B ≤ (oddHull P ⊔ S).comap (toStar T) →
      IsSubnormal B ((oddHull P ⊔ S).comap (toStar T)) → InClassXBlock B → False := by
  intro B hBM hsub hblock
  have hCM : gnC T ≤ (oddHull P ⊔ S).comap (toStar T) := by
    have h := MonoidHom.ker_le_comap (toStar T) (oddHull P ⊔ S)
    rwa [QuotientGroup.ker_mk'] at h
  by_cases hBC : B ≤ gnC T
  · have h1 := hsub.inf_of_le hCM
    rw [inf_eq_left.2 hBC] at h1
    exact hX.noXBlock B (h1.trans (IsSubnormal.of_mathlib (gnC_normal T).isSubnormal)) hblock
  have hBne : gnImg T B ≠ ⊥ := by
    intro h
    rw [gnImg, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hBC h
  have hSK : S ≤ Subgroup.normalizer (oddHull P : Set (X ⧸ gnC T)) :=
    hSP.trans (normalizer_le_normalizer_oddHull P)
  have hBodd := gnImg_le_closure_odd (T := T)
    (CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.le_closure_odd_of_isShort2 hblock.1)
  have hBS : gnImg T B ≤ oddHull P ⊔ S := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBM hb
  have hBK : gnImg T B ≤ oddHull P := hBodd.trans ((Subgroup.closure_le _).2 fun y hy =>
    mem_of_odd_of_mem_sup_pGroup hS hSK (hBS hy.1) hy.2)
  have hsubK : IsSubnormal (gnImg T B) (oddHull P) := by
    have h1 := hsub.map (toStar T)
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h1
    have h2 := h1.inf_of_le (le_sup_left : oddHull P ≤ oddHull P ⊔ S)
    rwa [show B.map (toStar T) = gnImg T B from rfl, inf_eq_left.2 hBK] at h2
  have hBeq : gnImg T B = oddHull P := eq_oddHull_of_isSubnormal hP hsubK hBodd hBne
  have hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ (oddHull P ⊔ S).comap (toStar T) :=
    (pCoreOf_le_gnC hX).trans hCM
  have hB2 : IsBlock2 ((oddHull P ⊔ S).comap (toStar T)) B :=
    ⟨hblock.1, hBM, (IsSubnormal.iff_subgroupOf hBM).1 hsub⟩
  have hKP : oddHull P ≤ P := (Subgroup.closure_le P).2 fun x hx => hx.1
  have hc : ⁅pCoreOf 2 P, gnImg T B⁆ = ⊥ := by
    refine commutator_gnImg_eq_bot_q hX hQH hB2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P) ?_ ?_
    · rw [hBeq]
      exact hKP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
    · rw [hBeq]
      exact (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans
        (Subgroup.le_normalizer.trans (normalizer_le_normalizer_oddHull P))
  rw [hBeq, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  exact hxy (Subgroup.mem_centralizer_iff.1 (hc hy) x hx)

theorem noXBlock_oddHull_sup_gnImg {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {Ls P₂ : Subgroup (X ⧸ gnC T)}
    (he : Nonempty (↥Ls ≃* alternatingGroup (Fin 10))) (hP₂ : P₂ ≤ Ls)
    (hshape : IsTwoFourSFive P₂)
    (hTP : gnImg T T ≤ Subgroup.normalizer (P₂ : Set (X ⧸ gnC T))) :
    ∀ B : Subgroup X, B ≤ (oddHull P₂ ⊔ gnImg T T).comap (toStar T) →
      IsSubnormal B ((oddHull P₂ ⊔ gnImg T T).comap (toStar T)) → InClassXBlock B → False := by
  obtain ⟨e⟩ := he
  let ρ : ↥P₂ →* Equiv.Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp (e.toMonoidHom.comp (Subgroup.inclusion hP₂))
  have hρ : Function.Injective ρ := fun a b h =>
    Subgroup.inclusion_injective hP₂ (e.injective (Subtype.ext h))
  exact noXBlock_oddHull_sup hX hshape (exists_ne_comm_of_isTwoFourSFive hshape ρ hρ)
    (hX.sylow.2.1.map _) hTP

end CFSG.LocalAnalysis.RankThreeUC.S15

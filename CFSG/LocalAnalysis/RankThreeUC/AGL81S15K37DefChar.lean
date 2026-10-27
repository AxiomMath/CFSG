module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddDefChar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3Cover
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs273
import CFSG.RankThree.PartOne.HNB.InnerAction
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Rest

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K37

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.RankThree.PartTwo.Sec4.Census (IsThreeCenterCover TripleCoverLie)
open CFSG.LocalAnalysis.UniquenessCase.UCK (K36OddDefChar CatGrp)
open CFSG.RankThree.PartTwo.KFacts (congr_mulAutConj mul_mulAutConj_mul_inv)

variable {X : Type} [Group X] [Finite X] {K E S : Subgroup X}

namespace K37Setting

theorem center_eq_bot_of_defChar (hTC : TripleCoverLie) (h : K37Setting X K E S)
    (d : TauCeti.ValidLieTypeIndex) (hd3 : d.1.characteristic = 3)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hO : ¬ K37Open K E) : Subgroup.center ↥K = ⊥ := by
  rcases h.isPGroup_center.card_eq_or_dvd with h1 | hz
  · exact Subgroup.eq_bot_of_card_eq _ h1
  have hcov : IsThreeCenterCover ↥K (TauCeti.CFSGIndex.lie d).Group := ⟨h.quasi, hz, hd⟩
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Chev3.char3_tripleCoverLieIndex hd3
      (hTC d ↥K hcov) with ⟨q, hdq, hq⟩ | ⟨q, hdq, hq⟩ | ⟨q, hdq, hq⟩
  · exact (hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hcov, q, hq, hdq⟩)))))).elim
  · exact (hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, hcov, q, hq, hdq⟩))))))).elim
  · exact (hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨d, hcov, q, hq, hdq⟩)))))))).elim

theorem exists_inner_of_l227 (h : K37Setting X K E S) (hZ : Subgroup.center ↥K = ⊥)
    (eL : ↥K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) :
    ∃ e₀ ∈ E, e₀ ≠ 1 ∧ ∃ u : ↥K, u ^ 3 = 1 ∧
      ∀ y ∈ K, e₀ * y * e₀⁻¹ = (u : X) * y * (u : X)⁻¹ := by
  obtain ⟨hK, hAK⟩ := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs273.card_L227_and_aut eL
  have hconj := CFSG.RankThree.PartOne.HNB.conj_injective_of_center_eq_bot hZ
  haveI : (MulAut.conj : ↥K →* MulAut ↥K).range.Normal := ⟨fun n hn α => by
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hn
    exact MonoidHom.mem_range.mpr ⟨α y, (mul_mulAutConj_mul_inv α y).symm⟩⟩
  have hidx : (MulAut.conj : ↥K →* MulAut ↥K).range.index = 6 := by
    have h0 := Subgroup.card_mul_index (MulAut.conj : ↥K →* MulAut ↥K).range
    rw [← Nat.card_congr (MonoidHom.ofInjective hconj).toEquiv, hK, hAK] at h0
    omega
  have hrel : (MulAut.conj : ↥K →* MulAut ↥K).range.relIndex (autIm E K) ∣ 6 :=
    hidx ▸ Subgroup.relIndex_dvd_index_of_normal (MulAut.conj : ↥K →* MulAut ↥K).range
      (autIm E K)
  have hmul := Subgroup.relIndex_mul_card (H := (MulAut.conj : ↥K →* MulAut ↥K).range)
    (K := autIm E K)
  rw [h.card_autIm] at hmul
  have hne : (MulAut.conj : ↥K →* MulAut ↥K).range ⊓ autIm E K ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, mul_one] at hmul
    rw [hmul] at hrel
    norm_num at hrel
  obtain ⟨⟨α, hαI, hαE⟩, hα1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hαI
  obtain ⟨⟨e₀, he₀N⟩, he₀E, he₀α⟩ := Subgroup.mem_map.mp hαE
  refine ⟨e₀, Subgroup.mem_subgroupOf.mp he₀E, ?_, u, ?_, fun y hy => ?_⟩
  · rintro rfl
    exact hα1 (Subtype.ext (he₀α.symm.trans (map_one _)))
  · apply hconj
    rw [map_pow, hu, map_one]
    exact h.isElemAbelian_autIm.2 α hαE
  · have h1 := congrArg Subtype.val (DFunLike.congr_fun (he₀α.trans hu.symm) ⟨y, hy⟩)
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] at h1
    exact h1

theorem false_of_defChar (hODC : K36OddDefChar) (h : K37Setting X K E S)
    (hZ : Subgroup.center ↥K = ⊥) (d : TauCeti.ValidLieTypeIndex) (hd3 : d.1.characteristic = 3)
    (ψ : ↥K ≃* CatGrp d) (hSC : ¬ S ≤ Subgroup.centralizer (K : Set X)) : False := by
  have hN : ∀ x : X, x ∈ Subgroup.normalizer (K : Set X) := fun x => by
    haveI := h.normal
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨Θ, hΘinj, hΘapp, hΘc⟩ : ∃ Θ : MulAut ↥K →* MulAut (CatGrp d), Function.Injective Θ ∧
      (∀ (α : MulAut ↥K) (y : ↥K), Θ α (ψ y) = ψ (α y)) ∧
      ∀ y : ↥K, Θ (MulAut.conj y) = MulAut.conj (ψ y) :=
    ⟨(MulAut.congr ψ).toMonoidHom, (MulAut.congr ψ).injective,
      fun α y => by simp [MulAut.congr_apply], congr_mulAutConj ψ⟩
  have hker : ∀ x : X, K.normalizerMonoidHom ⟨x, hN x⟩ = 1 →
      x ∈ Subgroup.centralizer (K : Set X) := fun x hx => by
    have hmem : (⟨x, hN x⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈
        K.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr hx
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨e, he, he1, s, hs, hse, hsK⟩ := h.exists_comm_not_mem hSC
  obtain ⟨ε, hε⟩ : ∃ ε : MulAut (CatGrp d), ε = Θ (K.normalizerMonoidHom ⟨e, hN e⟩) :=
    ⟨_, rfl⟩
  have hε3 : ε ^ 3 = 1 := by
    have h1 : (⟨e, hN e⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h.elem.2 e he)
    rw [hε, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hε1 : ε ≠ 1 := by
    intro h1
    have h2 := hker e (hΘinj (by rw [map_one, ← hε, h1]))
    have hmem : e ∈ E ⊓ Subgroup.centralizer (K : Set X) := ⟨he, h2⟩
    rw [h.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact he1 hmem
  have hfix : ∀ k : CatGrp d, ε k = k → ((ψ.symm k : ↥K) : X) ∈ rankThreeGamma 1 3 E := by
    intro k hk
    refine h.centralizer_le he he1 (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    have h1 : K.normalizerMonoidHom ⟨e, hN e⟩ (ψ.symm k) = ψ.symm k :=
      ψ.injective (by rw [← hΘapp, MulEquiv.apply_symm_apply, ← hε]; exact hk)
    have h2 : e * (ψ.symm k : X) * e⁻¹ = ψ.symm k := by
      have h3 := congrArg Subtype.val h1
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
    calc ((ψ.symm k : ↥K) : X) * e = e * (ψ.symm k : X) * e⁻¹ * e := by rw [h2]
      _ = e * (ψ.symm k : X) := by group
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (MulAut (CatGrp d)),
      R = (autIm S K).map Θ ⊓ Subgroup.centralizer ({ε} : Set (MulAut (CatGrp d))) := ⟨_, rfl⟩
  have hR2 : IsPGroup 2 R := by
    rw [hR]
    exact ((isPGroup_autIm (K := K) h.two).map Θ).to_le inf_le_left
  have hRc : ∀ r ∈ R, r * ε = ε * r := fun r hr => by
    rw [hR] at hr
    exact Subgroup.mem_centralizer_singleton_iff.mp hr.2
  have hRne : R ≠ ⊥ := by
    rw [hR]
    intro hbot
    have hcomm : Commute (⟨s, hN s⟩ : ↥(Subgroup.normalizer (K : Set X))) ⟨e, hN e⟩ :=
      Subtype.ext hse
    have hmem : Θ (K.normalizerMonoidHom ⟨s, hN s⟩) ∈
        (autIm S K).map Θ ⊓ Subgroup.centralizer ({ε} : Set (MulAut (CatGrp d))) := by
      refine Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_map_of_mem Θ ⟨⟨s, hN s⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hε]
      exact ((hcomm.map K.normalizerMonoidHom).map Θ).eq
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hsK (hker s (hΘinj (by rw [map_one]; exact hmem)))
  have hRn : ∀ k : CatGrp d, ε k = k → ∀ r ∈ R,
      MulAut.conj k * r * (MulAut.conj k)⁻¹ ∈ R := by
    intro k hk r hr
    rw [hR] at hr ⊢
    have hn : MulAut.conj (ψ.symm k) ∈
        Subgroup.normalizer ((autIm S K : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) :=
      h.conj_mem_normalizer_autIm (ψ.symm k).2 (hfix k hk)
    have hn' := Subgroup.le_normalizer_map Θ (Subgroup.mem_map_of_mem Θ hn)
    rw [hΘc, MulEquiv.apply_symm_apply] at hn'
    have hc : Commute ε (MulAut.conj k) :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.Odd.commute_conj_of_fix hk
    have hr' : Commute ε r := (Subgroup.mem_centralizer_singleton_iff.mp hr.2).symm
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn' r).mp hr.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hc.mul_right hr').mul_right hc.inv_right).symm.eq
  obtain ⟨-, ⟨eL⟩, hout⟩ := hODC.1 d (by rw [hd3]; norm_num) ε (by rw [hd3]; exact hε3) hε1 R
    hRne hR2 hRc hRn
  obtain ⟨e₀, he₀, he₀1, u, hu3, hek⟩ := h.exists_inner_of_l227 hZ (ψ.trans eL)
  have hP : IsPGroup 3 (Subgroup.zpowers u) := by
    have h1 : orderOf u ∣ 3 ^ 1 := by rw [pow_one]; exact orderOf_dvd_of_pow_eq_one hu3
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
    exact IsPGroup.of_card (n := i) (by rw [Nat.card_zpowers, hi])
  obtain ⟨U, hU⟩ := hP.exists_le_sylow
  have huU : u ∈ (U : Subgroup ↥K) := hU (Subgroup.mem_zpowers u)
  have hUc : ∀ x ∈ (U : Subgroup ↥K), ∀ y ∈ (U : Subgroup ↥K), x * y = y * x := by
    intro x hx y hy
    let P : Sylow 3 (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) :=
      U.mapSurjective (f := (ψ.trans eL).toMonoidHom) (ψ.trans eL).surjective
    have hxP : (ψ.trans eL) x ∈ P := Subgroup.mem_map_of_mem (ψ.trans eL).toMonoidHom hx
    have hyP : (ψ.trans eL) y ∈ P := Subgroup.mem_map_of_mem (ψ.trans eL).toMonoidHom hy
    apply (ψ.trans eL).injective
    rw [map_mul, map_mul]
    exact CFSG.Glauberman.Dickson.psl2_mul_comm_of_mem_sylow
      (GaloisField.card 3 3 (by norm_num)) P hxP hyP
  have hUΓ : ∀ x ∈ (U : Subgroup ↥K), (x : X) ∈ rankThreeGamma 1 3 E := fun x hx =>
    h.mem_gamma_of_inner he₀ he₀1 hek x.2 (congrArg Subtype.val (hUc x hx u huU))
  have hgen := hODC.2 d ⟨eL⟩ ε hε3 hout (U.mapSurjective (f := ψ.toMonoidHom) ψ.surjective)
  have hsub : ((U.mapSurjective (f := ψ.toMonoidHom) ψ.surjective : Set (CatGrp d)) ∪
      {k | ε k = k}) ⊆
      (((rankThreeGamma 1 3 E).subgroupOf K).map ψ.toMonoidHom : Set (CatGrp d)) := by
    rintro k (hk | hk)
    · have hk' : k ∈ (U : Subgroup ↥K).map ψ.toMonoidHom := hk
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk'
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hUΓ x hx))
    · exact Subgroup.mem_map.mpr ⟨ψ.symm k, Subgroup.mem_subgroupOf.mpr (hfix k hk),
        ψ.apply_symm_apply k⟩
  have htop : ((rankThreeGamma 1 3 E).subgroupOf K).map ψ.toMonoidHom = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact (Subgroup.closure_le _).mpr hsub
  refine h.not_le fun y hy => ?_
  have hmem : ψ ⟨y, hy⟩ ∈ ((rankThreeGamma 1 3 E).subgroupOf K).map ψ.toMonoidHom := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hmem
  have hyy' : ψ y' = ψ ⟨y, hy⟩ := hyy
  rw [ψ.injective hyy'] at hy'
  exact Subgroup.mem_subgroupOf.mp hy'

theorem le_centralizer_of_defChar (hTC : TripleCoverLie) (hODC : K36OddDefChar)
    (h : K37Setting X K E S) (d : TauCeti.ValidLieTypeIndex) (hd3 : d.1.characteristic = 3)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group))
    (hO : ¬ K37Open K E) : S ≤ Subgroup.centralizer (K : Set X) := by
  by_contra hSC
  have hZ := h.center_eq_bot_of_defChar hTC d hd3 hd hO
  obtain ⟨e₁⟩ := hd
  exact h.false_of_defChar hODC hZ d hd3
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₁) hSC

end K37Setting

end CFSG.LocalAnalysis.RankThreeUC.S15.K37

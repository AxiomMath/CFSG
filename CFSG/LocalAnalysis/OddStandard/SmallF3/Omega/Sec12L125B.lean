module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Fus
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Beta
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Iso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L125Frame
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12Statements

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Lemma125b_of (hp : Asc82Pre11) (h122 : Asc82Lemma122) (h123 : Asc82Lemma123)
    (h124 : Asc82Lemma124) (h125a : Asc82Lemma125a) : Asc82Lemma125b := by
  intro G _ _ t L S z K1 K2 E hctx
  have F : Sec12Frame t L S := sec12Frame_of hp hctx.toSec10Ctx hctx.alt1
  have hE : IsSylow2Of E (secCMB t S L) := hctx.sylowE
  have hcore : Sec125Core t (secV t S L E) E :=
    sec125_core_of hp hctx (h124 G t L S z K1 K2 E hctx)
  have hD : centralizer (secV t S L E : Set G) = secV t S L E ⊔ oddCoreIn (secN (secV t S L E)) :=
    h125a G t L S z K1 K2 E hctx
  obtain ⟨X, hX⟩ := h122 G t L S z K1 K2 E hctx
  obtain ⟨hXA5, hXinf, hXaut, -⟩ := h123 G t L S z K1 K2 E X hctx hX
  have hXC : X ≤ secCMt t S L := sec125_X_le_CMt F hctx.sylow.1 hX.sup
  have htN : t ∈ normalizer (secV t S L E : Set G) := hcore.t_mem_normalizer
  have hKo : ∀ k ∈ oddCoreIn (secN (secV t S L E)), Odd (orderOf k) := fun k hk =>
    odd_orderOf_of_mem_oddCoreIn hk
  have hKt : ∀ k ∈ oddCoreIn (secN (secV t S L E)),
      t * k * t⁻¹ ∈ oddCoreIn (secN (secV t S L E)) := fun k hk =>
    conj_mem_oddCoreIn (Subgroup.le_normalizer (H := secN (secV t S L E)) htN) hk
  refine ⟨?_, ?_⟩
  · ext b
    constructor
    · intro hb
      obtain ⟨hbN, hbC⟩ := Subgroup.mem_inf.mp hb
      obtain ⟨n, hn, rfl⟩ := sec127_mem_secNb_iff.mp hbN
      have hnt : betaOf (secV t S L E) n * betaOf (secV t S L E) t =
          betaOf (secV t S L E) t * betaOf (secV t S L E) n :=
        (Subgroup.mem_centralizer_iff.mp hbC _ (Set.mem_singleton _)).symm
      obtain ⟨c, hcN, hct, hcb⟩ := hcore.exists_comm_of_beta hD hKo hKt hn hnt
      refine sec127_mem_autIn_iff.mpr ⟨c, Subgroup.mem_inf.mpr ⟨hcN, ?_⟩, hcN, hcb.symm⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact hct.symm
    · intro hb
      obtain ⟨c, hcX, hcN, rfl⟩ := sec127_mem_autIn_iff.mp hb
      refine Subgroup.mem_inf.mpr ⟨sec127_mem_secNb_iff.mpr ⟨c, hcN, rfl⟩, ?_⟩
      have hct : t * c = c * t :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcX).2 t (Set.mem_singleton t)
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff.mp hs, ← sec127_betaOf_mul htN hcN,
        ← sec127_betaOf_mul hcN htN, hct]
  · rw [sec125_CNt_eq_CMt F hE hcore]
    obtain ⟨eXA⟩ := hXA5
    obtain ⟨eY⟩ := sec125_autIn_equiv (V := secV t S L E) (X := X)
      (fun x hx => sec125_CMt_le_N F hE (hXC hx))
      (fun x hx hxD => sec125_X_inf_D F hE hcore hXC hXinf hx hxD)
    have htA : t ∈ secA t S L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    have htC : t ∈ secCMt t S L := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer (H := secA t S L) htA, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
    have hg2 : betaOf (secV t S L E) t * betaOf (secV t S L E) t = 1 := by
      rw [← sec127_betaOf_mul htN htN, hcore.tsq, sec127_betaOf_one]
    have hg1 : betaOf (secV t S L E) t ≠ 1 := by
      intro h1
      have htD := (sec127_betaOf_eq_one_iff htN).mp h1
      obtain ⟨v, hv, hne⟩ := hcore.nofix
      exact hne (Subgroup.mem_centralizer_iff.mp htD v hv).symm
    have hcomm : ∀ y ∈ autIn X (secV t S L E),
        betaOf (secV t S L E) t * y = y * betaOf (secV t S L E) t := by
      intro y hy
      obtain ⟨x, hxX, hxN, rfl⟩ := sec127_mem_autIn_iff.mp hy
      rw [← sec127_betaOf_mul htN hxN, ← sec127_betaOf_mul hxN htN, sec125_comm_t (hXC hxX)]
    have hne : ∀ y ∈ autIn X (secV t S L E), y ≠ betaOf (secV t S L E) t := by
      intro y hy
      obtain ⟨x, hxX, hxN, rfl⟩ := sec127_mem_autIn_iff.mp hy
      exact (sec125_betaT_ne F hE hcore hXC hXinf hxX).symm
    have hsplit : ∀ p ∈ autIn (secCMt t S L) (secV t S L E), p ∈ autIn X (secV t S L E) ∨
        ∃ y ∈ autIn X (secV t S L E), p = y * betaOf (secV t S L E) t := by
      intro p hp
      obtain ⟨g, hg, hgN, rfl⟩ := sec127_mem_autIn_iff.mp hp
      obtain ⟨x, hxX, hx⟩ := sec125_beta_decomp F hE hcore hXC hXaut hg
      have hxN : x ∈ normalizer (secV t S L E : Set G) := sec125_CMt_le_N F hE (hXC hxX)
      have hxY : betaOf (secV t S L E) x ∈ autIn X (secV t S L E) :=
        sec127_mem_autIn_iff.mpr ⟨x, hxX, hxN, rfl⟩
      rcases hx with hx | hx
      · left
        rw [hx]
        exact hxY
      · exact Or.inr ⟨_, hxY, hx⟩
    obtain ⟨eP⟩ := sec125_equiv_of_split (g := betaOf (secV t S L E) t)
      (P := autIn (secCMt t S L) (secV t S L E)) (Y := autIn X (secV t S L E)) hg2 hg1
      (sec127_mem_autIn_iff.mpr ⟨t, htC, htN, rfl⟩) (sec127_autIn_mono hXC) hcomm hne hsplit
    exact ⟨eP.trans (MulEquiv.prodCongr (MulEquiv.refl _) (eY.trans eXA))⟩

end CFSG.OddStandard.SmallF3.Omega

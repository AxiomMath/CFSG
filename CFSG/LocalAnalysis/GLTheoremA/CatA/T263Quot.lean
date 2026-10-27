module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Quot

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA

theorem glaPPrimeCore_quot_eq_bot {p : ℕ} (hp : p.Prime) {A : Type} [Group A] [Finite A]
    (K B₀ : Subgroup A) [K.Normal] (hB₀ : IsPGroup p B₀) (hKB : K ⊔ B₀ = ⊤)
    [(GLAPPrimeCoreOf p K).Normal] :
    GLAPPrimeCore p (A ⧸ GLAPPrimeCoreOf p K) = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set N : Subgroup A := GLAPPrimeCoreOf p K with hNdef
  have hNp : ¬ p ∣ Nat.card N := not_dvd_card_glaPPrimeCoreOf hp K
  have hcopN : Nat.Coprime p (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd hp).2 hNp
  have hquot : IsPGroup p (A ⧸ K) := by
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
    have ha : a ∈ K ⊔ B₀ := by rw [hKB]; exact Subgroup.mem_top a
    obtain ⟨y, hy, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_left).1 ha
    obtain ⟨k, hk⟩ := hB₀ ⟨z, hz⟩
    refine ⟨k, ?_⟩
    have hz' : z ^ p ^ k = 1 := congrArg Subtype.val hk
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff y).2 hy, one_mul, ← QuotientGroup.mk_pow, hz',
      QuotientGroup.mk_one]
  unfold GLAPPrimeCore
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro M hM hcopM
  set Mt : Subgroup A := M.comap (QuotientGroup.mk' N) with hMt
  haveI : Mt.Normal := inferInstance
  have hcardMt : Nat.card Mt = Nat.card N * Nat.card M := QuotientGroup.card_preimage_mk N (M : Set (A ⧸ N))
  have hcopMt : Nat.Coprime p (Nat.card Mt) := by
    rw [hcardMt]
    exact Nat.Coprime.mul_right hcopN hcopM
  have hMtK : Mt ≤ K := by
    set Z : Subgroup (A ⧸ K) := Mt.map (QuotientGroup.mk' K) with hZ
    have hZp : IsPGroup p Z := fun z => by
      obtain ⟨k, hk⟩ := hquot z.1
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    obtain ⟨j, hj⟩ := hZp.exists_card_eq
    have hdvd : Nat.card Z ∣ Nat.card Mt := Subgroup.card_map_dvd Mt (QuotientGroup.mk' K)
    have hj0 : j = 0 := by
      by_contra hne
      have hp_dvd : p ∣ Nat.card Mt :=
        (dvd_pow_self p hne).trans (by rw [← hj]; exact hdvd)
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcopMt hp_dvd
    have hZbot : Z = ⊥ := Subgroup.eq_bot_of_card_eq Z (by rw [hj, hj0, pow_zero])
    intro m hm
    have hmZ : (QuotientGroup.mk' K m : A ⧸ K) ∈ Z := Subgroup.mem_map_of_mem _ hm
    rw [hZbot, Subgroup.mem_bot] at hmZ
    exact (QuotientGroup.eq_one_iff m).1 hmZ
  have hMtN : Mt ≤ N := by
    intro m hm
    have hmK : m ∈ K := hMtK hm
    rw [hNdef, CFSG.LocalAnalysis.GLTheoremA.S267.mem_glaPPrimeCoreOf_iff]
    refine ⟨⟨m, hmK⟩, ?_, rfl⟩
    have hcard' : Nat.Coprime p (Nat.card ↥(Mt.subgroupOf K)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMtK).toEquiv]
      exact hcopMt
    have hsub : Mt.subgroupOf K ≤ GLAPPrimeCore p ↥K :=
      le_sSup ⟨inferInstance, hcard'⟩
    exact hsub (Subgroup.mem_subgroupOf.2 hm)
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective y
  have ha : a ∈ Mt := hy
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff a).2 (hMtN ha)

end CFSG.LocalAnalysis.GLTheoremA.T263

end

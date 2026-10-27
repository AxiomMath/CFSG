module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Amb
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12l
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem card_le_of_isCyclic_of_pow_eq_one {p : ℕ} (hp : 0 < p) {M : Type*} [Group M] [Finite M]
    [IsCyclic M] (h : ∀ x : M, x ^ p = 1) : Nat.card M ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := M)
  have hord : orderOf g = Nat.card M := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [← hord]
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (h g))

theorem card_le_sq_aut_L2 {F : Type} [Field F] [Finite F]
    (hF : CFSG.GH74.GLS.IVK.L2Field F) {K : Type} [Group K] [Finite K]
    (e : K ≃* CFSG.GH74.GLS.IVK.L2 F) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : ¬ p ∣ Nat.card F)
    {A : Subgroup (MulAut K)} (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ 2 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut K) := Finite.of_injective (fun f : MulAut K => (f : K → K))
    (fun f g h => MulEquiv.ext (congrFun h))
  set Δ := CFSG.GH74.GLS.IVK.innDiagSub e with hΔ
  set I := CFSG.GH74.GLS.IVK.innAut K with hI
  haveI hΔn : Δ.Normal := CFSG.GH74.GLS.IVK.innDiagSub_normal e
  have hsup : Δ ⊔ CFSG.GH74.GLS.IVK.fieldAutSub e = ⊤ :=
    CFSG.GH74.GLS.IVK.innDiagSub_sup_fieldAutSub e
  haveI hcyc : IsCyclic ↥(CFSG.GH74.GLS.IVK.fieldAutSub e) :=
    CFSG.GH74.GLS.IVK.isCyclic_fieldAutSub e
  have hrel : I.relIndex Δ = 2 := CFSG.GH74.GLS.IVK.innAut_relIndex_two e hF
  set π : MulAut K →* MulAut K ⧸ Δ := QuotientGroup.mk' Δ with hπ
  have hQcyc : IsCyclic (MulAut K ⧸ Δ) := by
    refine isCyclic_of_surjective (π.comp (CFSG.GH74.GLS.IVK.fieldAutSub e).subtype) ?_
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    have hg : g ∈ Δ ⊔ CFSG.GH74.GLS.IVK.fieldAutSub e := hsup ▸ Subgroup.mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hg
    obtain ⟨d, hd, f, hf, rfl⟩ := hg
    refine ⟨⟨f, hf⟩, ?_⟩
    show QuotientGroup.mk f = QuotientGroup.mk (d * f)
    rw [QuotientGroup.eq]
    have := hΔn.conj_mem d hd f⁻¹
    simpa [mul_assoc] using this
  set ρ : ↥A →* MulAut K ⧸ Δ := π.comp A.subtype with hρ
  haveI : IsCyclic ρ.range := inferInstance
  have hApow : ∀ a : ↥A, a ^ p = 1 := fun a => Subtype.ext (by simpa using hA.2 a a.2)
  have hrange : Nat.card ρ.range ≤ p := by
    refine card_le_of_isCyclic_of_pow_eq_one hp.pos ?_
    rintro ⟨_, ⟨a, rfl⟩⟩
    apply Subtype.ext
    show (ρ a) ^ p = 1
    rw [← map_pow, hApow a, map_one]
  have hsplit : Nat.card A = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hAp : IsPGroup p A := isPGroup_of_isElemAbelian hA
  have hker : Nat.card ρ.ker ≤ p := by
    have hYp : IsPGroup p ↥(A ⊓ Δ) := hAp.to_le inf_le_left
    have hrelY : I.relIndex (A ⊓ Δ) ≤ 2 := by
      have := Subgroup.relIndex_le_of_le_right (H := I) (inf_le_right : A ⊓ Δ ≤ Δ)
        (by rw [hrel]; norm_num)
      rwa [hrel] at this
    obtain ⟨k, hk⟩ := hYp.exists_card_eq
    have hdvd : I.relIndex (A ⊓ Δ) ∣ p ^ k := hk ▸ Subgroup.relIndex_dvd_card I (A ⊓ Δ)
    have hodd : Odd (I.relIndex (A ⊓ Δ)) :=
      Odd.of_dvd_nat ((hp.odd_of_ne_two hp2).pow) hdvd
    have hne0 : I.relIndex (A ⊓ Δ) ≠ 0 := ne_zero_of_dvd_ne_zero (pow_ne_zero k hp.ne_zero) hdvd
    have h1 : I.relIndex (A ⊓ Δ) = 1 := by
      obtain ⟨m, hm⟩ := hodd
      omega
    have hYI : A ⊓ Δ ≤ I := Subgroup.relIndex_eq_one.1 h1
    have hkerI : ρ.ker ≤ (I ⊓ A).subgroupOf A := by
      intro x hx
      have hxΔ : (x : MulAut K) ∈ Δ := (QuotientGroup.eq_one_iff _).1 hx
      exact ⟨hYI ⟨x.2, hxΔ⟩, x.2⟩
    have hle : Nat.card ρ.ker ≤ Nat.card ↥(I ⊓ A) :=
      calc Nat.card ρ.ker ≤ Nat.card ↥((I ⊓ A).subgroupOf A) := Subgroup.card_le_of_le hkerI
        _ = Nat.card ↥(I ⊓ A) := Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    refine hle.trans ?_
    have hinj : Function.Injective (MulAut.conj : K →* MulAut K) :=
      CFSG.GH74.GLS.IVK.conj_injective_of_L2 e
    have hXle : I ⊓ A ≤ (MulAut.conj : K →* MulAut K).range := inf_le_left
    have hmapX' : ((I ⊓ A).comap (MulAut.conj : K →* MulAut K)).map (MulAut.conj : K →* MulAut K) =
        I ⊓ A := by
      rw [Subgroup.map_comap_eq, inf_eq_right.2 hXle]
    have hcardX' : Nat.card ↥((I ⊓ A).comap (MulAut.conj : K →* MulAut K)) = Nat.card ↥(I ⊓ A) := by
      have h : Nat.card ↥(((I ⊓ A).comap (MulAut.conj : K →* MulAut K)).map
          (MulAut.conj : K →* MulAut K)) =
          Nat.card ↥((I ⊓ A).comap (MulAut.conj : K →* MulAut K)) :=
        Subgroup.card_map_of_injective hinj
      rw [hmapX'] at h
      exact h.symm
    set X' : Subgroup K := (I ⊓ A).comap (MulAut.conj : K →* MulAut K) with hX'
    have hX'pow : ∀ x : ↥X', x ^ p = 1 := by
      intro x
      apply Subtype.ext
      apply hinj
      have hx : (MulAut.conj (x : K) : MulAut K) ∈ A := x.2.2
      have := hA.2 _ hx
      simpa [map_pow] using this
    have hX'p : IsPGroup p ↥X' := fun x => ⟨1, by simpa using hX'pow x⟩
    haveI : Group.IsNilpotent ↥X' := hX'p.isNilpotent
    obtain ⟨m, hm⟩ := hX'p.exists_card_eq
    have hX'odd : Odd (Nat.card ↥X') := hm ▸ (hp.odd_of_ne_two hp2).pow
    rw [← hcardX']
    rcases CFSG.GH74.GLS.IVK.Proofs2.ivk_1_2l F hF K e X' hX'odd inferInstance with
      ⟨hcycX, -⟩ | ⟨p', -, -, hdvdF⟩
    · haveI := hcycX
      exact card_le_of_isCyclic_of_pow_eq_one hp.pos hX'pow
    · rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [hm, h0, pow_zero]; exact hp.one_lt.le
      · exfalso
        apply hpF
        exact (dvd_pow_self p hpos.ne').trans (hm ▸ hdvdF)
  calc Nat.card A = Nat.card ρ.range * Nat.card ρ.ker := hsplit
    _ ≤ p * p := Nat.mul_le_mul hrange hker
    _ = p ^ 2 := by ring

theorem lieModel_A1 {S : Type} [Group S] (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 1 Q).Valid)
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 Q, hv⟩).Group) :
    CFSG.Blueprint.LieModel S CFSG.Open.StatedLieTag.PSL 2 Q.p Q.exponent :=
  CFSG.Models.LieModel.toBlueprint (by decide) (CFSG.Models.lieModel_A 1 Q hv e)

theorem s2019FactA1_holds : S2019FactA1 := by
  intro p q hp hp2 hq hq2 hqp Ω _ _ S B D J hSn hSq hSp hcat hBel hSB hrank
  intro hC hDB hCD hrel hD hJ hBJ hcm T hTS hT2 hJT
  exfalso
  let eS : PQuot p S ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  let eSS : PSimple p S ≃* (↥S ⧸ Subgroup.center ↥S) :=
    QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  suffices h : ∃ (F : Type) (_ : Field F) (_ : Finite F), CFSG.GH74.GLS.IVK.L2Field F ∧
      ¬ p ∣ Nat.card F ∧ Nonempty ((↥S ⧸ Subgroup.center ↥S) ≃* CFSG.GH74.GLS.IVK.L2 F) by
    obtain ⟨F, _, _, hF, hpF, ⟨e2⟩⟩ := h
    obtain ⟨A, hA, hcard⟩ := exists_elemAbelian_aut_rank_ge_three hp hSn hSq hSp hBel hCD hrel hD
    have h2 := card_le_sq_aut_L2 hF e2 hp hp2 hpF hA
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  cases i with
  | cyclic r hr => simp [onLie] at hi
  | alternating n hn => simp [onLie] at hi
  | sporadic s => simp [onLie] at hi
  | lie d =>
    obtain ⟨d1, hv⟩ := d
    have hi' : d1.characteristic = q ∧ S2019IsA1 d1 := hi
    cases d1 <;> try (simp [S2019IsA1] at hi'; done)
    case A r Q =>
      rcases r with _ | _ | r
      · simp [S2019IsA1] at hi'
      · have hQp : Q.p = q := by
          have := hi'.1
          rwa [TauCeti.LieTypeIndex.characteristic_A] at this
        have e' : (↥S ⧸ Subgroup.center ↥S) ≃*
            (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.A 1 Q, hv⟩).Group := eSS.symm.trans e
        have hL := lieModel_A1 Q hv e'
        obtain ⟨⟨hQprime, hf1, -, -, hn3⟩, F, hFf, hFfin, hcardF, ⟨e2⟩⟩ :=
          hL.statedClassicalModel (by decide)
        rw [hQp] at hcardF hn3
        have hq3 : 3 ≤ q := by have := hq.two_le; omega
        have hge : q ≤ q ^ Q.exponent := Nat.le_self_pow (by omega) q
        refine ⟨F, hFf, hFfin, ⟨?_, ?_⟩, ?_, ⟨e2⟩⟩
        · rw [hcardF]; exact (hq.odd_of_ne_two hq2).pow
        · have hne : q ^ Q.exponent ≠ 3 := fun h => hn3 (by rw [h])
          rw [hcardF]; omega
        · rw [hcardF]
          intro hd
          exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd)).symm
      · simp [S2019IsA1] at hi'

end CFSG.LocalAnalysis.GLTheoremA.S2019

end

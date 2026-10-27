module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SRank
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.CatB

@[expose] def U42E81CentAt : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S IsU42Host →
    ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E = 3 ^ 4 →
      ∀ t : MulAut S, orderOf t = 2 → (∀ e ∈ E, MulAut.conj e * t = t * MulAut.conj e) → False

@[expose] def U42E81InnU6At : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S S9.isU6two → RankFine S 27

theorem rankFine_of_host (hI6 : U42E81InnU6At) (S : Type) [Group S] [Finite S]
    (h : catalogIs S IsU42Host) : RankFine S 27 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hD | hU5 | hU6
  · obtain ⟨e'⟩ := bridge_d4two (⟨i, hD, ⟨e⟩⟩ : catalogIs S S9.isD4two)
    exact RankFine.of_mulEquiv e' rankFine_om8
  · obtain ⟨q, hv, hq2, ⟨e0⟩⟩ := lieIndex_isU5two (⟨i, hU5, ⟨e⟩⟩ : catalogIs S S9.isU5two)
    obtain ⟨e1⟩ := nonempty_equiv_timmesfeldPSU 4 q hv hq2 e0
    exact RankFine.of_mulEquiv (e1.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 5)) rankFine_u5
  · exact hI6 S ⟨i, hU6, ⟨e⟩⟩

theorem scalars_omega_trivial :
    (StatedScalars (Fin 4 ⊕ Fin 4) (ZMod 2)).subgroupOf (StatedOmega (StatedQuadPlus 4 (ZMod 2))) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hc1 : c = 1 := by
    apply Units.ext
    have h : ∀ x : (ZMod 2)ˣ, (x : ZMod 2) = 1 := by decide
    exact h c
  rw [hc1, map_one] at hc
  exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using hc.symm))

theorem isSimple_om8 : IsSimpleGroup CFSG.AGLEmbedding.Om8 := by
  have hsimp : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2)))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (K := ZMod 2) (n := 4)
      (by norm_num)
  have e : StatedProj (StatedOmega (StatedQuadPlus 4 (ZMod 2))) ≃*
      CFSG.AGLEmbedding.Om8 :=
    (QuotientGroup.quotientMulEquivOfEq scalars_omega_trivial).trans QuotientGroup.quotientBot
  exact e.symm.isSimpleGroup

theorem isSimple_of_host (S : Type) [Group S] [Finite S] (h : catalogIs S IsU42Host) :
    IsSimpleGroup S := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  rcases hi with hD | hU5 | hU6
  · obtain ⟨e'⟩ := bridge_d4two (⟨i, hD, ⟨e⟩⟩ : catalogIs S S9.isD4two)
    haveI := isSimple_om8
    exact e'.isSimpleGroup
  · obtain ⟨q, hv, hq2, ⟨e0⟩⟩ := lieIndex_isU5two (⟨i, hU5, ⟨e⟩⟩ : catalogIs S S9.isU5two)
    obtain ⟨e1⟩ := nonempty_equiv_timmesfeldPSU 4 q hv hq2 e0
    have hsimp : IsSimpleGroup (StatedProj (StatedSU 5 2 (GaloisField 2 2))) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField 2 2) 2 1
        (by rw [GaloisField.card 2 2 (by norm_num)]; norm_num) 5 (by norm_num) (by decide)
    exact (e1.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 5)).isSimpleGroup
  · obtain ⟨q, hv, hq2, ⟨e0⟩⟩ := U62RankSound.lieIndex_isU6two (⟨i, hU6, ⟨e⟩⟩ : catalogIs S S9.isU6two)
    have hm := CFSG.LocalAnalysis.GLTheoremA.lieModel_twistedA' 5 q hv e0
    obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two (s := 1)
      (by norm_num) (hq2.trans (by norm_num))
    rw [h1, h2] at hm
    obtain ⟨K, hKF, hKfin, hK4, ⟨f⟩⟩ := U42Cat.classical_u6 hm
    have hsimp : IsSimpleGroup (StatedProj (StatedSU 6 (2 ^ 1) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 (by rw [hK4]; norm_num) 6
        (by norm_num) (by decide)
    exact f.isSimpleGroup

theorem center_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S] (E : Subgroup S)
    (hE : Nat.card E = 3 ^ 4) : Subgroup.center S = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : S, a * b = b * a := fun a b => by
      have hmem : a ∈ Subgroup.center S := by
        rw [h]
        exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.1 hmem) b).symm
    let _ : CommGroup S := { (inferInstance : Group S) with mul_comm := hcomm }
    have hp : (Nat.card S).Prime := (CommGroup.is_simple_iff_prime_card (α := S)).1 inferInstance
    have h81 : 3 ^ 4 ∣ Nat.card S := by
      rw [← hE]
      exact Subgroup.card_subgroup_dvd_card E
    rcases (Nat.dvd_prime hp).1 (dvd_trans (by norm_num : (3 : ℕ) ^ 4 ∣ 3 ^ 4) h81) with h1 | h1
    · norm_num at h1
    · rw [← h1] at hp
      norm_num at hp

theorem conj_injective_of_center {S : Type} [Group S] (hZ : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcx : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h : MulAut.conj x g = g := by
      have := congrArg (fun φ : MulAut S => φ g) hx
      simpa using this
    rw [MulAut.conj_apply] at h
    calc g * x = x * g * x⁻¹ * x := by rw [h]
      _ = x * g := by group
  rw [hZ] at hcx
  exact Subgroup.mem_bot.1 hcx

theorem u42E81At_of_residuals (hC : U42E81CentAt) (hI6 : U42E81InnU6At) : U42E81At := by
  intro S _ _ hS E hE hE81 U hU hnorm
  haveI := isSimple_of_host S hS
  have hZ := center_eq_bot_of_simple E hE81
  have hinj := conj_injective_of_center hZ
  let T : Subgroup S := U.comap (MulAut.conj : S →* MulAut S)
  have hT2 : IsPGroup 2 T := by
    intro x
    obtain ⟨k, hk⟩ := hU ⟨MulAut.conj x.1, x.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    apply hinj
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hk'
    rw [Subgroup.coe_pow, Subgroup.coe_one, map_pow, hk', map_one]
  have hEnorm : E ≤ Subgroup.normalizer (T : Set S) := by
    intro e he
    intro n
    show n ∈ T ↔ e * n * e⁻¹ ∈ T
    have h := hnorm e he (MulAut.conj n)
    have hconj : MulAut.conj (e * n * e⁻¹) =
        MulAut.conj e * MulAut.conj n * (MulAut.conj e)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    simp only [T, Subgroup.mem_comap, SetLike.mem_coe]
    rw [hconj]
    exact h
  have hTbot : T = ⊥ := by
    by_contra hne
    have hr := (rankFine_of_host hI6 S hS) E T hE hT2 hne hEnorm
    rw [hE81] at hr
    norm_num at hr
  have hcomm : ∀ e ∈ E, ∀ u ∈ U, MulAut.conj e * u = u * MulAut.conj e := by
    intro e he u hu
    have h1 : MulAut.conj e * u * (MulAut.conj e)⁻¹ ∈ U := (hnorm e he u).1 hu
    have hz : MulAut.conj e * u * (MulAut.conj e)⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem h1 (U.inv_mem hu)
    have hz_eq : MulAut.conj e * u * (MulAut.conj e)⁻¹ * u⁻¹ = MulAut.conj (e * u e⁻¹) := by
      apply MulEquiv.ext
      intro x
      simp [MulAut.conj_apply, MulAut.mul_apply, mul_assoc]
    have hs : MulAut.conj (e * u e⁻¹) ∈ U := by
      rw [← hz_eq]
      exact hz
    have hs' : e * u e⁻¹ ∈ T := hs
    rw [hTbot] at hs'
    have he1 : e * u e⁻¹ = 1 := Subgroup.mem_bot.1 hs'
    have hz1 : MulAut.conj e * u * (MulAut.conj e)⁻¹ * u⁻¹ = 1 := by
      rw [hz_eq, he1, map_one]
    have h2 : MulAut.conj e * u * (MulAut.conj e)⁻¹ = u := mul_inv_eq_one.1 hz1
    calc MulAut.conj e * u = (MulAut.conj e * u * (MulAut.conj e)⁻¹) * MulAut.conj e := by group
      _ = u * MulAut.conj e := by rw [h2]
  by_contra hne
  have hcard : 2 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU
    have hn1 : Nat.card U ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
    rcases n with _ | n
    · exact absurd (by simpa using hn) hn1
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  exact hC S hS E hE hE81 (t : MulAut S) (by rw [Subgroup.orderOf_coe, ht]) (fun e he => hcomm e he t t.2)

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

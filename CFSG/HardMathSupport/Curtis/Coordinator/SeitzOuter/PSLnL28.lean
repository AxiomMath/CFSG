module

public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnTwo
public import CFSG.Quasithin.Background.F6ResL28
public import CFSG.Walter.W67.Section5.P56R1512

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin.F6 CFSG.Assembly.LowTwoRank

theorem no_cube_of_l28 {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal]
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 8) (e : K ≃* CFSG.GorensteinWalter.PSL2 F) (E : Subgroup Y)
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 27) : False := by
  let e' : K ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 F) :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F)
  obtain ⟨g⟩ := L28Res.nonempty_equiv F hF
  have hK504 : Nat.card K = 504 := by
    rw [Nat.card_congr e'.toEquiv, Nat.card_congr g.toEquiv, L28Res.card_G8]
  have hAut : Nat.card (MulAut K) = 1512 := by
    rw [Nat.card_congr (MulAut.congr e').toEquiv, l28AutFact_holds F hF,
      Nat.card_congr g.toEquiv, L28Res.card_G8]
  have hφ : Function.Injective (MulAut.conjNormal : Y →* MulAut K) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have : y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg (fun f : MulAut K => ((f ⟨k, hk⟩ : K) : Y)) hy
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc k * y = y * k * y⁻¹ * y := by rw [h1]
        _ = y * k := by group
    rw [hC] at this
    exact this
  have hYdvd : Nat.card Y ∣ 1512 := by
    rw [← hAut]
    exact Subgroup.card_dvd_of_injective _ hφ
  have h504 : 504 ∣ Nat.card Y := hK504 ▸ Subgroup.card_subgroup_dvd_card K
  have h27 : 27 ∣ Nat.card Y := hc ▸ Subgroup.card_subgroup_dvd_card E
  have hY : Nat.card Y = 1512 :=
    Nat.dvd_antisymm hYdvd (by
      have h := Nat.lcm_dvd h504 h27
      have h' : Nat.lcm 504 27 = 1512 := by norm_num
      rwa [h'] at h)
  have hT3 : IsPGroup 3 E := fun x => by
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hE.2 x x.2
  have h9 := CFSG.Walter.W67.Sec56.card_inf_derived (L' := K) (T := E) inferInstance hK504 hY hT3 hc
  set P : Subgroup K := (K ⊓ E).subgroupOf K with hP
  have hPc : Nat.card P = 3 ^ 2 := by
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, h9]
    norm_num
  have hPel : IsElemAbelian 3 P := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      apply Subtype.ext
      have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨((a : K) : Y), (Subgroup.mem_inf.mp a.2).2⟩
        ⟨((b : K) : Y), (Subgroup.mem_inf.mp b.2).2⟩)
      simpa using h
    · intro x hx
      apply Subtype.ext
      simpa using hE.2 (x : Y) (Subgroup.mem_inf.mp hx).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact not_exists_plane_psl2 (ℓ := 2) (f := 3) (by rw [hF]; norm_num) (by rw [hF]; norm_num)
    (by norm_num) (by norm_num) (P.map e.toMonoidHom)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hPel _)
    (by rw [Subgroup.card_map_of_injective e.injective, hPc])

theorem kFactSeitzOuterCubeRankTwoAtPrime_A_one_eight {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 1 q).Valid) (h8 : q.card = 8) {p : ℕ} [Fact p.Prime]
    (hp3 : p = 3) : KFactSeitzOuterCubeRankTwoAtPrime ⟨.A 1 q, hv⟩ p := by
  intro hp2 Y _ _ K hKn hC he hpd hl hno E hE hc
  subst hp3
  exfalso
  obtain ⟨e⟩ := he
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hF8 : Nat.card (GaloisField q.p q.exponent) = 8 := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, h8]
  exact no_cube_of_l28 K hC hF8
    (e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)) E hE hc

theorem kFactSeitzOuterCubeRankTwoAtPrime_A'
    (hL4 : L4TwoPlanes) {m : ℕ} (hm : 1 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} [Fact p.Prime]
    (hexc : ¬ (m = 2 ∧ p = 3 ∧ 3 ∣ q.card - 1)) :
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.A m q, hv⟩ p :=
  kFactSeitzOuterCubeRankTwoAtPrime_A hL4 hm hv hexc fun h1 hp3 h8 => by
    subst h1
    exact kFactSeitzOuterCubeRankTwoAtPrime_A_one_eight hv h8 hp3

end CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
